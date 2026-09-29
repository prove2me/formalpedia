-- Prove2me | solution 1 for syracuse_descends_range_754331_758331
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T19:05:18.900473+00:00
-- url     : https://prove2.me/submissions/a480a9e0-8f28-4ed4-a097-814fe5632dbf

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


theorem B1277957 : Blo 754331 1277957 := bbase (se 4 (by rfl) ⟨119808, by rfl⟩ : syracuseStep 1277957 = 239617) (by norm_num)
theorem B851989 : Blo 754331 851989 := bbase (se 6 (by rfl) ⟨19968, by rfl⟩ : syracuseStep 851989 = 39937) (by norm_num)
theorem B852025 : Blo 754331 852025 := bbase (se 2 (by rfl) ⟨319509, by rfl⟩ : syracuseStep 852025 = 639019) (by norm_num)
theorem B1704005 : Blo 754331 1704005 := bbase (se 4 (by rfl) ⟨159750, by rfl⟩ : syracuseStep 1704005 = 319501) (by norm_num)
theorem B852061 : Blo 754331 852061 := bbase (se 3 (by rfl) ⟨159761, by rfl⟩ : syracuseStep 852061 = 319523) (by norm_num)
theorem B1212517 : Blo 754331 1212517 := bbase (se 4 (by rfl) ⟨113673, by rfl⟩ : syracuseStep 1212517 = 227347) (by norm_num)
theorem B852097 : Blo 754331 852097 := bbase (se 2 (by rfl) ⟨319536, by rfl⟩ : syracuseStep 852097 = 639073) (by norm_num)
theorem B1278085 : Blo 754331 1278085 := bbase (se 4 (by rfl) ⟨119820, by rfl⟩ : syracuseStep 1278085 = 239641) (by norm_num)
theorem B1704077 : Blo 754331 1704077 := bbase (se 3 (by rfl) ⟨319514, by rfl⟩ : syracuseStep 1704077 = 639029) (by norm_num)
theorem B852133 : Blo 754331 852133 := bbase (se 4 (by rfl) ⟨79887, by rfl⟩ : syracuseStep 852133 = 159775) (by norm_num)
theorem B6455477 : Blo 754331 6455477 := bbase (se 5 (by rfl) ⟨302600, by rfl⟩ : syracuseStep 6455477 = 605201) (by norm_num)
theorem B3834053 : Blo 754331 3834053 := bbase (se 4 (by rfl) ⟨359442, by rfl⟩ : syracuseStep 3834053 = 718885) (by norm_num)
theorem B852169 : Blo 754331 852169 := bbase (se 2 (by rfl) ⟨319563, by rfl⟩ : syracuseStep 852169 = 639127) (by norm_num)
theorem B1704149 : Blo 754331 1704149 := bbase (se 7 (by rfl) ⟨19970, by rfl⟩ : syracuseStep 1704149 = 39941) (by norm_num)
theorem B1278173 : Blo 754331 1278173 := bbase (se 3 (by rfl) ⟨239657, by rfl⟩ : syracuseStep 1278173 = 479315) (by norm_num)
theorem B852205 : Blo 754331 852205 := bbase (se 3 (by rfl) ⟨159788, by rfl⟩ : syracuseStep 852205 = 319577) (by norm_num)
theorem B852241 : Blo 754331 852241 := bbase (se 2 (by rfl) ⟨319590, by rfl⟩ : syracuseStep 852241 = 639181) (by norm_num)
theorem B2457877 : Blo 754331 2457877 := bbase (se 6 (by rfl) ⟨57606, by rfl⟩ : syracuseStep 2457877 = 115213) (by norm_num)
theorem B1704221 : Blo 754331 1704221 := bbase (se 3 (by rfl) ⟨319541, by rfl⟩ : syracuseStep 1704221 = 639083) (by norm_num)
theorem B2556197 : Blo 754331 2556197 := bbase (se 4 (by rfl) ⟨239643, by rfl⟩ : syracuseStep 2556197 = 479287) (by norm_num)
theorem B852277 : Blo 754331 852277 := bbase (se 5 (by rfl) ⟨39950, by rfl⟩ : syracuseStep 852277 = 79901) (by norm_num)
theorem B852313 : Blo 754331 852313 := bbase (se 2 (by rfl) ⟨319617, by rfl⟩ : syracuseStep 852313 = 639235) (by norm_num)
theorem B1278301 : Blo 754331 1278301 := bbase (se 3 (by rfl) ⟨239681, by rfl⟩ : syracuseStep 1278301 = 479363) (by norm_num)
theorem B1704293 : Blo 754331 1704293 := bbase (se 4 (by rfl) ⟨159777, by rfl⟩ : syracuseStep 1704293 = 319555) (by norm_num)
theorem B852349 : Blo 754331 852349 := bbase (se 3 (by rfl) ⟨159815, by rfl⟩ : syracuseStep 852349 = 319631) (by norm_num)
theorem B852385 : Blo 754331 852385 := bbase (se 2 (by rfl) ⟨319644, by rfl⟩ : syracuseStep 852385 = 639289) (by norm_num)
theorem B1704365 : Blo 754331 1704365 := bbase (se 3 (by rfl) ⟨319568, by rfl⟩ : syracuseStep 1704365 = 639137) (by norm_num)
theorem B1278389 : Blo 754331 1278389 := bbase (se 5 (by rfl) ⟨59924, by rfl⟩ : syracuseStep 1278389 = 119849) (by norm_num)
theorem B852421 : Blo 754331 852421 := bbase (se 4 (by rfl) ⟨79914, by rfl⟩ : syracuseStep 852421 = 159829) (by norm_num)
theorem B819677 : Blo 754331 819677 := bbase (se 3 (by rfl) ⟨153689, by rfl⟩ : syracuseStep 819677 = 307379) (by norm_num)
theorem B852457 : Blo 754331 852457 := bbase (se 2 (by rfl) ⟨319671, by rfl⟩ : syracuseStep 852457 = 639343) (by norm_num)
theorem B1704437 : Blo 754331 1704437 := bbase (se 5 (by rfl) ⟨79895, by rfl⟩ : syracuseStep 1704437 = 159791) (by norm_num)
theorem B852493 : Blo 754331 852493 := bbase (se 3 (by rfl) ⟨159842, by rfl⟩ : syracuseStep 852493 = 319685) (by norm_num)
theorem B1147429 : Blo 754331 1147429 := bbase (se 4 (by rfl) ⟨107571, by rfl⟩ : syracuseStep 1147429 = 215143) (by norm_num)
theorem B852529 : Blo 754331 852529 := bbase (se 2 (by rfl) ⟨319698, by rfl⟩ : syracuseStep 852529 = 639397) (by norm_num)
theorem B1278517 : Blo 754331 1278517 := bbase (se 5 (by rfl) ⟨59930, by rfl⟩ : syracuseStep 1278517 = 119861) (by norm_num)
theorem B1704509 : Blo 754331 1704509 := bbase (se 3 (by rfl) ⟨319595, by rfl⟩ : syracuseStep 1704509 = 639191) (by norm_num)
theorem B1147477 : Blo 754331 1147477 := bbase (se 8 (by rfl) ⟨6723, by rfl⟩ : syracuseStep 1147477 = 13447) (by norm_num)
theorem B852565 : Blo 754331 852565 := bbase (se 8 (by rfl) ⟨4995, by rfl⟩ : syracuseStep 852565 = 9991) (by norm_num)
theorem B852601 : Blo 754331 852601 := bbase (se 2 (by rfl) ⟨319725, by rfl⟩ : syracuseStep 852601 = 639451) (by norm_num)
theorem B1704581 : Blo 754331 1704581 := bbase (se 4 (by rfl) ⟨159804, by rfl⟩ : syracuseStep 1704581 = 319609) (by norm_num)
theorem B1278605 : Blo 754331 1278605 := bbase (se 3 (by rfl) ⟨239738, by rfl⟩ : syracuseStep 1278605 = 479477) (by norm_num)
theorem B852637 : Blo 754331 852637 := bbase (se 3 (by rfl) ⟨159869, by rfl⟩ : syracuseStep 852637 = 319739) (by norm_num)
theorem B852673 : Blo 754331 852673 := bbase (se 2 (by rfl) ⟨319752, by rfl⟩ : syracuseStep 852673 = 639505) (by norm_num)
theorem B1704653 : Blo 754331 1704653 := bbase (se 3 (by rfl) ⟨319622, by rfl⟩ : syracuseStep 1704653 = 639245) (by norm_num)
theorem B3637973 : Blo 754331 3637973 := bbase (se 7 (by rfl) ⟨42632, by rfl⟩ : syracuseStep 3637973 = 85265) (by norm_num)
theorem B2556629 : Blo 754331 2556629 := bbase (se 7 (by rfl) ⟨29960, by rfl⟩ : syracuseStep 2556629 = 59921) (by norm_num)
theorem B852709 : Blo 754331 852709 := bbase (se 4 (by rfl) ⟨79941, by rfl⟩ : syracuseStep 852709 = 159883) (by norm_num)
theorem B852745 : Blo 754331 852745 := bbase (se 2 (by rfl) ⟨319779, by rfl⟩ : syracuseStep 852745 = 639559) (by norm_num)
theorem B1278733 : Blo 754331 1278733 := bbase (se 3 (by rfl) ⟨239762, by rfl⟩ : syracuseStep 1278733 = 479525) (by norm_num)
theorem B1704725 : Blo 754331 1704725 := bbase (se 6 (by rfl) ⟨39954, by rfl⟩ : syracuseStep 1704725 = 79909) (by norm_num)
theorem B852781 : Blo 754331 852781 := bbase (se 3 (by rfl) ⟨159896, by rfl⟩ : syracuseStep 852781 = 319793) (by norm_num)
theorem B852817 : Blo 754331 852817 := bbase (se 2 (by rfl) ⟨319806, by rfl⟩ : syracuseStep 852817 = 639613) (by norm_num)
theorem B1704797 : Blo 754331 1704797 := bbase (se 3 (by rfl) ⟨319649, by rfl⟩ : syracuseStep 1704797 = 639299) (by norm_num)
theorem B1278821 : Blo 754331 1278821 := bbase (se 4 (by rfl) ⟨119889, by rfl⟩ : syracuseStep 1278821 = 239779) (by norm_num)
theorem B5735285 : Blo 754331 5735285 := bbase (se 5 (by rfl) ⟨268841, by rfl⟩ : syracuseStep 5735285 = 537683) (by norm_num)
theorem B852853 : Blo 754331 852853 := bbase (se 5 (by rfl) ⟨39977, by rfl⟩ : syracuseStep 852853 = 79955) (by norm_num)
theorem B852889 : Blo 754331 852889 := bbase (se 2 (by rfl) ⟨319833, by rfl⟩ : syracuseStep 852889 = 639667) (by norm_num)
theorem B1704869 : Blo 754331 1704869 := bbase (se 4 (by rfl) ⟨159831, by rfl⟩ : syracuseStep 1704869 = 319663) (by norm_num)
theorem B852925 : Blo 754331 852925 := bbase (se 3 (by rfl) ⟨159923, by rfl⟩ : syracuseStep 852925 = 319847) (by norm_num)
theorem B852961 : Blo 754331 852961 := bbase (se 2 (by rfl) ⟨319860, by rfl⟩ : syracuseStep 852961 = 639721) (by norm_num)
theorem B1278949 : Blo 754331 1278949 := bbase (se 4 (by rfl) ⟨119901, by rfl⟩ : syracuseStep 1278949 = 239803) (by norm_num)
theorem B1704941 : Blo 754331 1704941 := bbase (se 3 (by rfl) ⟨319676, by rfl⟩ : syracuseStep 1704941 = 639353) (by norm_num)
theorem B852997 : Blo 754331 852997 := bbase (se 4 (by rfl) ⟨79968, by rfl⟩ : syracuseStep 852997 = 159937) (by norm_num)
theorem B6554645 : Blo 754331 6554645 := bbase (se 6 (by rfl) ⟨153624, by rfl⟩ : syracuseStep 6554645 = 307249) (by norm_num)
theorem B853033 : Blo 754331 853033 := bbase (se 2 (by rfl) ⟨319887, by rfl⟩ : syracuseStep 853033 = 639775) (by norm_num)
theorem B1705013 : Blo 754331 1705013 := bbase (se 5 (by rfl) ⟨79922, by rfl⟩ : syracuseStep 1705013 = 159845) (by norm_num)
theorem B1279037 : Blo 754331 1279037 := bbase (se 3 (by rfl) ⟨239819, by rfl⟩ : syracuseStep 1279037 = 479639) (by norm_num)
theorem B853069 : Blo 754331 853069 := bbase (se 3 (by rfl) ⟨159950, by rfl⟩ : syracuseStep 853069 = 319901) (by norm_num)
theorem B853105 : Blo 754331 853105 := bbase (se 2 (by rfl) ⟨319914, by rfl⟩ : syracuseStep 853105 = 639829) (by norm_num)
theorem B1705085 : Blo 754331 1705085 := bbase (se 3 (by rfl) ⟨319703, by rfl⟩ : syracuseStep 1705085 = 639407) (by norm_num)
theorem B2557061 : Blo 754331 2557061 := bbase (se 4 (by rfl) ⟨239724, by rfl⟩ : syracuseStep 2557061 = 479449) (by norm_num)
theorem B2426021 : Blo 754331 2426021 := bbase (se 4 (by rfl) ⟨227439, by rfl⟩ : syracuseStep 2426021 = 454879) (by norm_num)
theorem B1279165 : Blo 754331 1279165 := bbase (se 3 (by rfl) ⟨239843, by rfl⟩ : syracuseStep 1279165 = 479687) (by norm_num)
theorem B1705157 : Blo 754331 1705157 := bbase (se 4 (by rfl) ⟨159858, by rfl⟩ : syracuseStep 1705157 = 319717) (by norm_num)
theorem B1213645 : Blo 754331 1213645 := bbase (se 3 (by rfl) ⟨227558, by rfl⟩ : syracuseStep 1213645 = 455117) (by norm_num)
theorem B1705229 : Blo 754331 1705229 := bbase (se 3 (by rfl) ⟨319730, by rfl⟩ : syracuseStep 1705229 = 639461) (by norm_num)
theorem B1279253 : Blo 754331 1279253 := bbase (se 6 (by rfl) ⟨29982, by rfl⟩ : syracuseStep 1279253 = 59965) (by norm_num)
theorem B918821 : Blo 754331 918821 := bbase (se 4 (by rfl) ⟨86139, by rfl⟩ : syracuseStep 918821 = 172279) (by norm_num)
theorem B1705301 : Blo 754331 1705301 := bbase (se 12 (by rfl) ⟨624, by rfl⟩ : syracuseStep 1705301 = 1249) (by norm_num)
theorem B1279381 : Blo 754331 1279381 := bbase (se 6 (by rfl) ⟨29985, by rfl⟩ : syracuseStep 1279381 = 59971) (by norm_num)
theorem B1705373 : Blo 754331 1705373 := bbase (se 3 (by rfl) ⟨319757, by rfl⟩ : syracuseStep 1705373 = 639515) (by norm_num)
theorem B3835349 : Blo 754331 3835349 := bbase (se 7 (by rfl) ⟨44945, by rfl⟩ : syracuseStep 3835349 = 89891) (by norm_num)
theorem B1705445 : Blo 754331 1705445 := bbase (se 4 (by rfl) ⟨159885, by rfl⟩ : syracuseStep 1705445 = 319771) (by norm_num)
theorem B1279469 : Blo 754331 1279469 := bbase (se 3 (by rfl) ⟨239900, by rfl⟩ : syracuseStep 1279469 = 479801) (by norm_num)
theorem B1705517 : Blo 754331 1705517 := bbase (se 3 (by rfl) ⟨319784, by rfl⟩ : syracuseStep 1705517 = 639569) (by norm_num)
theorem B2557493 : Blo 754331 2557493 := bbase (se 5 (by rfl) ⟨119882, by rfl⟩ : syracuseStep 2557493 = 239765) (by norm_num)
theorem B1279597 : Blo 754331 1279597 := bbase (se 3 (by rfl) ⟨239924, by rfl⟩ : syracuseStep 1279597 = 479849) (by norm_num)
theorem B1705589 : Blo 754331 1705589 := bbase (se 5 (by rfl) ⟨79949, by rfl⟩ : syracuseStep 1705589 = 159899) (by norm_num)
theorem B1214093 : Blo 754331 1214093 := bbase (se 3 (by rfl) ⟨227642, by rfl⟩ : syracuseStep 1214093 = 455285) (by norm_num)
theorem B1705661 : Blo 754331 1705661 := bbase (se 3 (by rfl) ⟨319811, by rfl⟩ : syracuseStep 1705661 = 639623) (by norm_num)
theorem B1279685 : Blo 754331 1279685 := bbase (se 4 (by rfl) ⟨119970, by rfl⟩ : syracuseStep 1279685 = 239941) (by norm_num)
theorem B1148645 : Blo 754331 1148645 := bbase (se 4 (by rfl) ⟨107685, by rfl⟩ : syracuseStep 1148645 = 215371) (by norm_num)
theorem B1705733 : Blo 754331 1705733 := bbase (se 4 (by rfl) ⟨159912, by rfl⟩ : syracuseStep 1705733 = 319825) (by norm_num)
theorem B1705805 : Blo 754331 1705805 := bbase (se 3 (by rfl) ⟨319838, by rfl⟩ : syracuseStep 1705805 = 639677) (by norm_num)
theorem B1705877 : Blo 754331 1705877 := bbase (se 6 (by rfl) ⟨39981, by rfl⟩ : syracuseStep 1705877 = 79963) (by norm_num)
theorem B1705949 : Blo 754331 1705949 := bbase (se 3 (by rfl) ⟨319865, by rfl⟩ : syracuseStep 1705949 = 639731) (by norm_num)
theorem B2557925 : Blo 754331 2557925 := bbase (se 4 (by rfl) ⟨239805, by rfl⟩ : syracuseStep 2557925 = 479611) (by norm_num)
theorem B1640461 : Blo 754331 1640461 := bbase (se 3 (by rfl) ⟨307586, by rfl⟩ : syracuseStep 1640461 = 615173) (by norm_num)
theorem B1706021 : Blo 754331 1706021 := bbase (se 4 (by rfl) ⟨159939, by rfl⟩ : syracuseStep 1706021 = 319879) (by norm_num)
theorem B1640533 : Blo 754331 1640533 := bbase (se 8 (by rfl) ⟨9612, by rfl⟩ : syracuseStep 1640533 = 19225) (by norm_num)
theorem B1706093 : Blo 754331 1706093 := bbase (se 3 (by rfl) ⟨319892, by rfl⟩ : syracuseStep 1706093 = 639785) (by norm_num)
theorem B1706165 : Blo 754331 1706165 := bbase (se 5 (by rfl) ⟨79976, by rfl⟩ : syracuseStep 1706165 = 159953) (by norm_num)
theorem B2459861 : Blo 754331 2459861 := bbase (se 7 (by rfl) ⟨28826, by rfl⟩ : syracuseStep 2459861 = 57653) (by norm_num)
theorem B1706237 : Blo 754331 1706237 := bbase (se 3 (by rfl) ⟨319919, by rfl⟩ : syracuseStep 1706237 = 639839) (by norm_num)
theorem B1149229 : Blo 754331 1149229 := bbase (se 3 (by rfl) ⟨215480, by rfl⟩ : syracuseStep 1149229 = 430961) (by norm_num)
theorem B1968533 : Blo 754331 1968533 := bbase (se 6 (by rfl) ⟨46137, by rfl⟩ : syracuseStep 1968533 = 92275) (by norm_num)
theorem B2558357 : Blo 754331 2558357 := bbase (se 6 (by rfl) ⟨59961, by rfl⟩ : syracuseStep 2558357 = 119923) (by norm_num)
theorem B2427365 : Blo 754331 2427365 := bbase (se 4 (by rfl) ⟨227565, by rfl⟩ : syracuseStep 2427365 = 455131) (by norm_num)
theorem B3836645 : Blo 754331 3836645 := bbase (se 4 (by rfl) ⟨359685, by rfl⟩ : syracuseStep 3836645 = 719371) (by norm_num)
theorem B2558789 : Blo 754331 2558789 := bbase (se 4 (by rfl) ⟨239886, by rfl⟩ : syracuseStep 2558789 = 479773) (by norm_num)
theorem B2591813 : Blo 754331 2591813 := bbase (se 4 (by rfl) ⟨242982, by rfl⟩ : syracuseStep 2591813 = 485965) (by norm_num)
theorem B6458453 : Blo 754331 6458453 := bbase (se 8 (by rfl) ⟨37842, by rfl⟩ : syracuseStep 6458453 = 75685) (by norm_num)
theorem B4852885 : Blo 754331 4852885 := bbase (se 6 (by rfl) ⟨113739, by rfl⟩ : syracuseStep 4852885 = 227479) (by norm_num)
theorem B2559221 : Blo 754331 2559221 := bbase (se 5 (by rfl) ⟨119963, by rfl⟩ : syracuseStep 2559221 = 239927) (by norm_num)
theorem B2592005 : Blo 754331 2592005 := bbase (se 4 (by rfl) ⟨243000, by rfl⟩ : syracuseStep 2592005 = 486001) (by norm_num)
theorem B6917557 : Blo 754331 6917557 := bbase (se 5 (by rfl) ⟨324260, by rfl⟩ : syracuseStep 6917557 = 648521) (by norm_num)
theorem B3837941 : Blo 754331 3837941 := bbase (se 5 (by rfl) ⟨179903, by rfl⟩ : syracuseStep 3837941 = 359807) (by norm_num)
theorem B954757 : Blo 754331 954757 := bbase (se 4 (by rfl) ⟨89508, by rfl⟩ : syracuseStep 954757 = 179017) (by norm_num)
theorem B2429365 : Blo 754331 2429365 := bbase (se 5 (by rfl) ⟨113876, by rfl⟩ : syracuseStep 2429365 = 227753) (by norm_num)
theorem B954929 : Blo 754331 954929 := bbase (se 2 (by rfl) ⟨358098, by rfl⟩ : syracuseStep 954929 = 716197) (by norm_num)
theorem B954985 : Blo 754331 954985 := bbase (se 2 (by rfl) ⟨358119, by rfl⟩ : syracuseStep 954985 = 716239) (by norm_num)
theorem B8163989 : Blo 754331 8163989 := bbase (se 6 (by rfl) ⟨191343, by rfl⟩ : syracuseStep 8163989 = 382687) (by norm_num)
theorem B955081 : Blo 754331 955081 := bbase (se 2 (by rfl) ⟨358155, by rfl⟩ : syracuseStep 955081 = 716311) (by norm_num)
theorem B2298581 : Blo 754331 2298581 := bbase (se 7 (by rfl) ⟨26936, by rfl⟩ : syracuseStep 2298581 = 53873) (by norm_num)
theorem B6558517 : Blo 754331 6558517 := bbase (se 5 (by rfl) ⟨307430, by rfl⟩ : syracuseStep 6558517 = 614861) (by norm_num)
theorem B3674965 : Blo 754331 3674965 := bbase (se 9 (by rfl) ⟨10766, by rfl⟩ : syracuseStep 3674965 = 21533) (by norm_num)
theorem B955253 : Blo 754331 955253 := bbase (se 5 (by rfl) ⟨44777, by rfl⟩ : syracuseStep 955253 = 89555) (by norm_num)
theorem B955309 : Blo 754331 955309 := bbase (se 3 (by rfl) ⟨179120, by rfl⟩ : syracuseStep 955309 = 358241) (by norm_num)
theorem B955405 : Blo 754331 955405 := bbase (se 3 (by rfl) ⟨179138, by rfl⟩ : syracuseStep 955405 = 358277) (by norm_num)
theorem B955577 : Blo 754331 955577 := bbase (se 2 (by rfl) ⟨358341, by rfl⟩ : syracuseStep 955577 = 716683) (by norm_num)
theorem B955633 : Blo 754331 955633 := bbase (se 2 (by rfl) ⟨358362, by rfl⟩ : syracuseStep 955633 = 716725) (by norm_num)
theorem B922897 : Blo 754331 922897 := bbase (se 2 (by rfl) ⟨346086, by rfl⟩ : syracuseStep 922897 = 692173) (by norm_num)
theorem B1611085 : Blo 754331 1611085 := bbase (se 3 (by rfl) ⟨302078, by rfl⟩ : syracuseStep 1611085 = 604157) (by norm_num)
theorem B955729 : Blo 754331 955729 := bbase (se 2 (by rfl) ⟨358398, by rfl⟩ : syracuseStep 955729 = 716797) (by norm_num)
theorem B955901 : Blo 754331 955901 := bbase (se 3 (by rfl) ⟨179231, by rfl⟩ : syracuseStep 955901 = 358463) (by norm_num)
theorem B2725397 : Blo 754331 2725397 := bbase (se 6 (by rfl) ⟨63876, by rfl⟩ : syracuseStep 2725397 = 127753) (by norm_num)
theorem B955957 : Blo 754331 955957 := bbase (se 5 (by rfl) ⟨44810, by rfl⟩ : syracuseStep 955957 = 89621) (by norm_num)
theorem B1611341 : Blo 754331 1611341 := bbase (se 3 (by rfl) ⟨302126, by rfl⟩ : syracuseStep 1611341 = 604253) (by norm_num)
theorem B956053 : Blo 754331 956053 := bbase (se 6 (by rfl) ⟨22407, by rfl⟩ : syracuseStep 956053 = 44815) (by norm_num)
theorem B956225 : Blo 754331 956225 := bbase (se 2 (by rfl) ⟨358584, by rfl⟩ : syracuseStep 956225 = 717169) (by norm_num)
theorem B956281 : Blo 754331 956281 := bbase (se 2 (by rfl) ⟨358605, by rfl⟩ : syracuseStep 956281 = 717211) (by norm_num)
theorem B4855733 : Blo 754331 4855733 := bbase (se 5 (by rfl) ⟨227612, by rfl⟩ : syracuseStep 4855733 = 455225) (by norm_num)
theorem B956377 : Blo 754331 956377 := bbase (se 2 (by rfl) ⟨358641, by rfl⟩ : syracuseStep 956377 = 717283) (by norm_num)
theorem B956549 : Blo 754331 956549 := bbase (se 4 (by rfl) ⟨89676, by rfl⟩ : syracuseStep 956549 = 179353) (by norm_num)
theorem B956605 : Blo 754331 956605 := bbase (se 3 (by rfl) ⟨179363, by rfl⟩ : syracuseStep 956605 = 358727) (by norm_num)
theorem B956701 : Blo 754331 956701 := bbase (se 3 (by rfl) ⟨179381, by rfl⟩ : syracuseStep 956701 = 358763) (by norm_num)
theorem B1612229 : Blo 754331 1612229 := bbase (se 4 (by rfl) ⟨151146, by rfl⟩ : syracuseStep 1612229 = 302293) (by norm_num)
theorem B956873 : Blo 754331 956873 := bbase (se 2 (by rfl) ⟨358827, by rfl⟩ : syracuseStep 956873 = 717655) (by norm_num)
theorem B956929 : Blo 754331 956929 := bbase (se 2 (by rfl) ⟨358848, by rfl⟩ : syracuseStep 956929 = 717697) (by norm_num)
theorem B957025 : Blo 754331 957025 := bbase (se 2 (by rfl) ⟨358884, by rfl⟩ : syracuseStep 957025 = 717769) (by norm_num)
theorem B1612469 : Blo 754331 1612469 := bbase (se 5 (by rfl) ⟨75584, by rfl⟩ : syracuseStep 1612469 = 151169) (by norm_num)
theorem B957197 : Blo 754331 957197 := bbase (se 3 (by rfl) ⟨179474, by rfl⟩ : syracuseStep 957197 = 358949) (by norm_num)
theorem B957253 : Blo 754331 957253 := bbase (se 4 (by rfl) ⟨89742, by rfl⟩ : syracuseStep 957253 = 179485) (by norm_num)
theorem B957349 : Blo 754331 957349 := bbase (se 4 (by rfl) ⟨89751, by rfl⟩ : syracuseStep 957349 = 179503) (by norm_num)
theorem B957521 : Blo 754331 957521 := bbase (se 2 (by rfl) ⟨359070, by rfl⟩ : syracuseStep 957521 = 718141) (by norm_num)
theorem B957577 : Blo 754331 957577 := bbase (se 2 (by rfl) ⟨359091, by rfl⟩ : syracuseStep 957577 = 718183) (by norm_num)
theorem B1612973 : Blo 754331 1612973 := bbase (se 3 (by rfl) ⟨302432, by rfl⟩ : syracuseStep 1612973 = 604865) (by norm_num)
theorem B1612981 : Blo 754331 1612981 := bbase (se 5 (by rfl) ⟨75608, by rfl⟩ : syracuseStep 1612981 = 151217) (by norm_num)
theorem B957673 : Blo 754331 957673 := bbase (se 2 (by rfl) ⟨359127, by rfl⟩ : syracuseStep 957673 = 718255) (by norm_num)
theorem B957845 : Blo 754331 957845 := bbase (se 6 (by rfl) ⟨22449, by rfl⟩ : syracuseStep 957845 = 44899) (by norm_num)
theorem B957901 : Blo 754331 957901 := bbase (se 3 (by rfl) ⟨179606, by rfl⟩ : syracuseStep 957901 = 359213) (by norm_num)
theorem B957997 : Blo 754331 957997 := bbase (se 3 (by rfl) ⟨179624, by rfl⟩ : syracuseStep 957997 = 359249) (by norm_num)
theorem B958169 : Blo 754331 958169 := bbase (se 2 (by rfl) ⟨359313, by rfl⟩ : syracuseStep 958169 = 718627) (by norm_num)
theorem B3448565 : Blo 754331 3448565 := bbase (se 5 (by rfl) ⟨161651, by rfl⟩ : syracuseStep 3448565 = 323303) (by norm_num)
theorem B958225 : Blo 754331 958225 := bbase (se 2 (by rfl) ⟨359334, by rfl⟩ : syracuseStep 958225 = 718669) (by norm_num)
theorem B2629397 : Blo 754331 2629397 := bbase (se 6 (by rfl) ⟨61626, by rfl⟩ : syracuseStep 2629397 = 123253) (by norm_num)
theorem B958321 : Blo 754331 958321 := bbase (se 2 (by rfl) ⟨359370, by rfl⟩ : syracuseStep 958321 = 718741) (by norm_num)
theorem B2039701 : Blo 754331 2039701 := bbase (se 6 (by rfl) ⟨47805, by rfl⟩ : syracuseStep 2039701 = 95611) (by norm_num)
theorem B1310717 : Blo 754331 1310717 := bbase (se 3 (by rfl) ⟨245759, by rfl⟩ : syracuseStep 1310717 = 491519) (by norm_num)
theorem B958493 : Blo 754331 958493 := bbase (se 3 (by rfl) ⟨179717, by rfl⟩ : syracuseStep 958493 = 359435) (by norm_num)
theorem B39297109 : Blo 754331 39297109 := bbase (se 8 (by rfl) ⟨230256, by rfl⟩ : syracuseStep 39297109 = 460513) (by norm_num)
theorem B958549 : Blo 754331 958549 := bbase (se 8 (by rfl) ⟨5616, by rfl⟩ : syracuseStep 958549 = 11233) (by norm_num)
theorem B958645 : Blo 754331 958645 := bbase (se 5 (by rfl) ⟨44936, by rfl⟩ : syracuseStep 958645 = 89873) (by norm_num)
theorem B1614109 : Blo 754331 1614109 := bbase (se 3 (by rfl) ⟨302645, by rfl⟩ : syracuseStep 1614109 = 605291) (by norm_num)
theorem B2302277 : Blo 754331 2302277 := bbase (se 4 (by rfl) ⟨215838, by rfl⟩ : syracuseStep 2302277 = 431677) (by norm_num)
theorem B958817 : Blo 754331 958817 := bbase (se 2 (by rfl) ⟨359556, by rfl⟩ : syracuseStep 958817 = 719113) (by norm_num)
theorem B958873 : Blo 754331 958873 := bbase (se 2 (by rfl) ⟨359577, by rfl⟩ : syracuseStep 958873 = 719155) (by norm_num)
theorem B5743061 : Blo 754331 5743061 := bbase (se 7 (by rfl) ⟨67301, by rfl⟩ : syracuseStep 5743061 = 134603) (by norm_num)
theorem B958969 : Blo 754331 958969 := bbase (se 2 (by rfl) ⟨359613, by rfl⟩ : syracuseStep 958969 = 719227) (by norm_num)
theorem B1614485 : Blo 754331 1614485 := bbase (se 6 (by rfl) ⟨37839, by rfl⟩ : syracuseStep 1614485 = 75679) (by norm_num)
theorem B959141 : Blo 754331 959141 := bbase (se 4 (by rfl) ⟨89919, by rfl⟩ : syracuseStep 959141 = 179839) (by norm_num)
theorem B860873 : Blo 754331 860873 := bbase (se 2 (by rfl) ⟨322827, by rfl⟩ : syracuseStep 860873 = 645655) (by norm_num)
theorem B1909453 : Blo 754331 1909453 := bbase (se 3 (by rfl) ⟨358022, by rfl⟩ : syracuseStep 1909453 = 716045) (by norm_num)
theorem B12264149 : Blo 754331 12264149 := bbase (se 7 (by rfl) ⟨143720, by rfl⟩ : syracuseStep 12264149 = 287441) (by norm_num)
theorem B959197 : Blo 754331 959197 := bbase (se 3 (by rfl) ⟨179849, by rfl⟩ : syracuseStep 959197 = 359699) (by norm_num)
theorem B1909565 : Blo 754331 1909565 := bbase (se 3 (by rfl) ⟨358043, by rfl⟩ : syracuseStep 1909565 = 716087) (by norm_num)
theorem B959293 : Blo 754331 959293 := bbase (se 3 (by rfl) ⟨179867, by rfl⟩ : syracuseStep 959293 = 359735) (by norm_num)
theorem B959465 : Blo 754331 959465 := bbase (se 2 (by rfl) ⟨359799, by rfl⟩ : syracuseStep 959465 = 719599) (by norm_num)
theorem B1909757 : Blo 754331 1909757 := bbase (se 3 (by rfl) ⟨358079, by rfl⟩ : syracuseStep 1909757 = 716159) (by norm_num)
theorem B959521 : Blo 754331 959521 := bbase (se 2 (by rfl) ⟨359820, by rfl⟩ : syracuseStep 959521 = 719641) (by norm_num)
theorem B4138037 : Blo 754331 4138037 := bbase (se 5 (by rfl) ⟨193970, by rfl⟩ : syracuseStep 4138037 = 387941) (by norm_num)
theorem B1090685 : Blo 754331 1090685 := bbase (se 3 (by rfl) ⟨204503, by rfl⟩ : syracuseStep 1090685 = 409007) (by norm_num)
theorem B959617 : Blo 754331 959617 := bbase (se 2 (by rfl) ⟨359856, by rfl⟩ : syracuseStep 959617 = 719713) (by norm_num)
theorem B12297365 : Blo 754331 12297365 := bbase (se 6 (by rfl) ⟨288219, by rfl⟩ : syracuseStep 12297365 = 576439) (by norm_num)
theorem B828613 : Blo 754331 828613 := bbase (se 4 (by rfl) ⟨77682, by rfl⟩ : syracuseStep 828613 = 155365) (by norm_num)
theorem B1910101 : Blo 754331 1910101 := bbase (se 12 (by rfl) ⟨699, by rfl⟩ : syracuseStep 1910101 = 1399) (by norm_num)
theorem B1910213 : Blo 754331 1910213 := bbase (se 4 (by rfl) ⟨179082, by rfl⟩ : syracuseStep 1910213 = 358165) (by norm_num)
theorem B2041301 : Blo 754331 2041301 := bbase (se 7 (by rfl) ⟨23921, by rfl⟩ : syracuseStep 2041301 = 47843) (by norm_num)
theorem B1910405 : Blo 754331 1910405 := bbase (se 4 (by rfl) ⟨179100, by rfl⟩ : syracuseStep 1910405 = 358201) (by norm_num)
theorem B1910749 : Blo 754331 1910749 := bbase (se 3 (by rfl) ⟨358265, by rfl⟩ : syracuseStep 1910749 = 716531) (by norm_num)
theorem B9218069 : Blo 754331 9218069 := bbase (se 6 (by rfl) ⟨216048, by rfl⟩ : syracuseStep 9218069 = 432097) (by norm_num)
theorem B2730037 : Blo 754331 2730037 := bbase (se 5 (by rfl) ⟨127970, by rfl⟩ : syracuseStep 2730037 = 255941) (by norm_num)
theorem B1910861 : Blo 754331 1910861 := bbase (se 3 (by rfl) ⟨358286, by rfl⟩ : syracuseStep 1910861 = 716573) (by norm_num)
theorem B1616125 : Blo 754331 1616125 := bbase (se 3 (by rfl) ⟨303023, by rfl⟩ : syracuseStep 1616125 = 606047) (by norm_num)
theorem B1911053 : Blo 754331 1911053 := bbase (se 3 (by rfl) ⟨358322, by rfl⟩ : syracuseStep 1911053 = 716645) (by norm_num)
theorem B3451189 : Blo 754331 3451189 := bbase (se 5 (by rfl) ⟨161774, by rfl⟩ : syracuseStep 3451189 = 323549) (by norm_num)
theorem B2992565 : Blo 754331 2992565 := bbase (se 5 (by rfl) ⟨140276, by rfl⟩ : syracuseStep 2992565 = 280553) (by norm_num)
theorem B1812989 : Blo 754331 1812989 := bbase (se 3 (by rfl) ⟨339935, by rfl⟩ : syracuseStep 1812989 = 679871) (by norm_num)
theorem B797245 : Blo 754331 797245 := bbase (se 3 (by rfl) ⟨149483, by rfl⟩ : syracuseStep 797245 = 298967) (by norm_num)
theorem B1911397 : Blo 754331 1911397 := bbase (se 4 (by rfl) ⟨179193, by rfl⟩ : syracuseStep 1911397 = 358387) (by norm_num)
theorem B1911509 : Blo 754331 1911509 := bbase (se 7 (by rfl) ⟨22400, by rfl⟩ : syracuseStep 1911509 = 44801) (by norm_num)
theorem B3222341 : Blo 754331 3222341 := bbase (se 4 (by rfl) ⟨302094, by rfl⟩ : syracuseStep 3222341 = 604189) (by norm_num)
theorem B7875413 : Blo 754331 7875413 := bbase (se 9 (by rfl) ⟨23072, by rfl⟩ : syracuseStep 7875413 = 46145) (by norm_num)
theorem B1911701 : Blo 754331 1911701 := bbase (se 6 (by rfl) ⟨44805, by rfl⟩ : syracuseStep 1911701 = 89611) (by norm_num)
theorem B1092509 : Blo 754331 1092509 := bbase (se 3 (by rfl) ⟨204845, by rfl⟩ : syracuseStep 1092509 = 409691) (by norm_num)
theorem B764969 : Blo 754331 764969 := bbase (se 2 (by rfl) ⟨286863, by rfl⟩ : syracuseStep 764969 = 573727) (by norm_num)
theorem B4303925 : Blo 754331 4303925 := bbase (se 5 (by rfl) ⟨201746, by rfl⟩ : syracuseStep 4303925 = 403493) (by norm_num)
theorem B1944661 : Blo 754331 1944661 := bbase (se 8 (by rfl) ⟨11394, by rfl⟩ : syracuseStep 1944661 = 22789) (by norm_num)
theorem B3058805 : Blo 754331 3058805 := bbase (se 5 (by rfl) ⟨143381, by rfl⟩ : syracuseStep 3058805 = 286763) (by norm_num)
theorem B1617013 : Blo 754331 1617013 := bbase (se 5 (by rfl) ⟨75797, by rfl⟩ : syracuseStep 1617013 = 151595) (by norm_num)
theorem B3058901 : Blo 754331 3058901 := bbase (se 7 (by rfl) ⟨35846, by rfl⟩ : syracuseStep 3058901 = 71693) (by norm_num)
theorem B1912045 : Blo 754331 1912045 := bbase (se 3 (by rfl) ⟨358508, by rfl⟩ : syracuseStep 1912045 = 717017) (by norm_num)
theorem B1912157 : Blo 754331 1912157 := bbase (se 3 (by rfl) ⟨358529, by rfl⟩ : syracuseStep 1912157 = 717059) (by norm_num)
theorem B3452357 : Blo 754331 3452357 := bbase (se 4 (by rfl) ⟨323658, by rfl⟩ : syracuseStep 3452357 = 647317) (by norm_num)
theorem B1912349 : Blo 754331 1912349 := bbase (se 3 (by rfl) ⟨358565, by rfl⟩ : syracuseStep 1912349 = 717131) (by norm_num)
theorem B1617509 : Blo 754331 1617509 := bbase (se 4 (by rfl) ⟨151641, by rfl⟩ : syracuseStep 1617509 = 303283) (by norm_num)
theorem B6893333 : Blo 754331 6893333 := bbase (se 6 (by rfl) ⟨161562, by rfl⟩ : syracuseStep 6893333 = 323125) (by norm_num)
theorem B14561045 : Blo 754331 14561045 := bbase (se 6 (by rfl) ⟨341274, by rfl⟩ : syracuseStep 14561045 = 682549) (by norm_num)
theorem B2043701 : Blo 754331 2043701 := bbase (se 5 (by rfl) ⟨95798, by rfl⟩ : syracuseStep 2043701 = 191597) (by norm_num)
theorem B1912693 : Blo 754331 1912693 := bbase (se 5 (by rfl) ⟨89657, by rfl⟩ : syracuseStep 1912693 = 179315) (by norm_num)
theorem B1814413 : Blo 754331 1814413 := bbase (se 3 (by rfl) ⟨340202, by rfl⟩ : syracuseStep 1814413 = 680405) (by norm_num)
theorem B765893 : Blo 754331 765893 := bbase (se 4 (by rfl) ⟨71802, by rfl⟩ : syracuseStep 765893 = 143605) (by norm_num)
theorem B1912805 : Blo 754331 1912805 := bbase (se 4 (by rfl) ⟨179325, by rfl⟩ : syracuseStep 1912805 = 358651) (by norm_num)
theorem B1912997 : Blo 754331 1912997 := bbase (se 4 (by rfl) ⟨179343, by rfl⟩ : syracuseStep 1912997 = 358687) (by norm_num)
theorem B4305109 : Blo 754331 4305109 := bbase (se 7 (by rfl) ⟨50450, by rfl⟩ : syracuseStep 4305109 = 100901) (by norm_num)
theorem B6140117 : Blo 754331 6140117 := bbase (se 7 (by rfl) ⟨71954, by rfl⟩ : syracuseStep 6140117 = 143909) (by norm_num)
theorem B1618373 : Blo 754331 1618373 := bbase (se 4 (by rfl) ⟨151722, by rfl⟩ : syracuseStep 1618373 = 303445) (by norm_num)
theorem B766441 : Blo 754331 766441 := bbase (se 2 (by rfl) ⟨287415, by rfl⟩ : syracuseStep 766441 = 574831) (by norm_num)
theorem B1913341 : Blo 754331 1913341 := bbase (se 3 (by rfl) ⟨358751, by rfl⟩ : syracuseStep 1913341 = 717503) (by norm_num)
theorem B766477 : Blo 754331 766477 := bbase (se 3 (by rfl) ⟨143714, by rfl⟩ : syracuseStep 766477 = 287429) (by norm_num)
theorem B1815085 : Blo 754331 1815085 := bbase (se 3 (by rfl) ⟨340328, by rfl⟩ : syracuseStep 1815085 = 680657) (by norm_num)
theorem B3224117 : Blo 754331 3224117 := bbase (se 5 (by rfl) ⟨151130, by rfl⟩ : syracuseStep 3224117 = 302261) (by norm_num)
theorem B1618517 : Blo 754331 1618517 := bbase (se 8 (by rfl) ⟨9483, by rfl⟩ : syracuseStep 1618517 = 18967) (by norm_num)
theorem B1913453 : Blo 754331 1913453 := bbase (se 3 (by rfl) ⟨358772, by rfl⟩ : syracuseStep 1913453 = 717545) (by norm_num)
theorem B1094357 : Blo 754331 1094357 := bbase (se 7 (by rfl) ⟨12824, by rfl⟩ : syracuseStep 1094357 = 25649) (by norm_num)
theorem B1815317 : Blo 754331 1815317 := bbase (se 6 (by rfl) ⟨42546, by rfl⟩ : syracuseStep 1815317 = 85093) (by norm_num)
theorem B3224357 : Blo 754331 3224357 := bbase (se 4 (by rfl) ⟨302283, by rfl⟩ : syracuseStep 3224357 = 604567) (by norm_num)
theorem B1913645 : Blo 754331 1913645 := bbase (se 3 (by rfl) ⟨358808, by rfl⟩ : syracuseStep 1913645 = 717617) (by norm_num)
theorem B1815365 : Blo 754331 1815365 := bbase (se 4 (by rfl) ⟨170190, by rfl⟩ : syracuseStep 1815365 = 340381) (by norm_num)
theorem B9942101 : Blo 754331 9942101 := bbase (se 8 (by rfl) ⟨58254, by rfl⟩ : syracuseStep 9942101 = 116509) (by norm_num)
theorem B1913989 : Blo 754331 1913989 := bbase (se 4 (by rfl) ⟨179436, by rfl⟩ : syracuseStep 1913989 = 358873) (by norm_num)
theorem B1914101 : Blo 754331 1914101 := bbase (se 5 (by rfl) ⟨89723, by rfl⟩ : syracuseStep 1914101 = 179447) (by norm_num)
theorem B1619261 : Blo 754331 1619261 := bbase (se 3 (by rfl) ⟨303611, by rfl⟩ : syracuseStep 1619261 = 607223) (by norm_num)
theorem B767317 : Blo 754331 767317 := bbase (se 13 (by rfl) ⟨140, by rfl⟩ : syracuseStep 767317 = 281) (by norm_num)
theorem B1914293 : Blo 754331 1914293 := bbase (se 5 (by rfl) ⟨89732, by rfl⟩ : syracuseStep 1914293 = 179465) (by norm_num)
theorem B1226269 : Blo 754331 1226269 := bbase (se 3 (by rfl) ⟨229925, by rfl⟩ : syracuseStep 1226269 = 459851) (by norm_num)
theorem B1914637 : Blo 754331 1914637 := bbase (se 3 (by rfl) ⟨358994, by rfl⟩ : syracuseStep 1914637 = 717989) (by norm_num)
theorem B1914749 : Blo 754331 1914749 := bbase (se 3 (by rfl) ⟨359015, by rfl⟩ : syracuseStep 1914749 = 718031) (by norm_num)
theorem B2865077 : Blo 754331 2865077 := bbase (se 5 (by rfl) ⟨134300, by rfl⟩ : syracuseStep 2865077 = 268601) (by norm_num)
theorem B1914941 : Blo 754331 1914941 := bbase (se 3 (by rfl) ⟨359051, by rfl⟩ : syracuseStep 1914941 = 718103) (by norm_num)
theorem B4307093 : Blo 754331 4307093 := bbase (se 6 (by rfl) ⟨100947, by rfl⟩ : syracuseStep 4307093 = 201895) (by norm_num)
theorem B1816757 : Blo 754331 1816757 := bbase (se 5 (by rfl) ⟨85160, by rfl⟩ : syracuseStep 1816757 = 170321) (by norm_num)
theorem B2865365 : Blo 754331 2865365 := bbase (se 7 (by rfl) ⟨33578, by rfl⟩ : syracuseStep 2865365 = 67157) (by norm_num)
theorem B1227125 : Blo 754331 1227125 := bbase (se 5 (by rfl) ⟨57521, by rfl⟩ : syracuseStep 1227125 = 115043) (by norm_num)
theorem B1816949 : Blo 754331 1816949 := bbase (se 5 (by rfl) ⟨85169, by rfl⟩ : syracuseStep 1816949 = 170339) (by norm_num)
theorem B1915285 : Blo 754331 1915285 := bbase (se 6 (by rfl) ⟨44889, by rfl⟩ : syracuseStep 1915285 = 89779) (by norm_num)
theorem B5257685 : Blo 754331 5257685 := bbase (se 7 (by rfl) ⟨61613, by rfl⟩ : syracuseStep 5257685 = 123227) (by norm_num)
theorem B1915397 : Blo 754331 1915397 := bbase (se 4 (by rfl) ⟨179568, by rfl⟩ : syracuseStep 1915397 = 359137) (by norm_num)
theorem B1915589 : Blo 754331 1915589 := bbase (se 4 (by rfl) ⟨179586, by rfl⟩ : syracuseStep 1915589 = 359173) (by norm_num)
theorem B3062533 : Blo 754331 3062533 := bbase (se 4 (by rfl) ⟨287112, by rfl⟩ : syracuseStep 3062533 = 574225) (by norm_num)
theorem B3226645 : Blo 754331 3226645 := bbase (se 6 (by rfl) ⟨75624, by rfl⟩ : syracuseStep 3226645 = 151249) (by norm_num)
theorem B1915933 : Blo 754331 1915933 := bbase (se 3 (by rfl) ⟨359237, by rfl⟩ : syracuseStep 1915933 = 718475) (by norm_num)
theorem B4602997 : Blo 754331 4602997 := bbase (se 5 (by rfl) ⟨215765, by rfl⟩ : syracuseStep 4602997 = 431531) (by norm_num)
theorem B1916045 : Blo 754331 1916045 := bbase (se 3 (by rfl) ⟨359258, by rfl⟩ : syracuseStep 1916045 = 718517) (by norm_num)
theorem B1916237 : Blo 754331 1916237 := bbase (se 3 (by rfl) ⟨359294, by rfl⟩ : syracuseStep 1916237 = 718589) (by norm_num)
theorem B2866549 : Blo 754331 2866549 := bbase (se 5 (by rfl) ⟨134369, by rfl⟩ : syracuseStep 2866549 = 268739) (by norm_num)
theorem B1457605 : Blo 754331 1457605 := bbase (se 4 (by rfl) ⟨136650, by rfl⟩ : syracuseStep 1457605 = 273301) (by norm_num)
theorem B1293869 : Blo 754331 1293869 := bbase (se 3 (by rfl) ⟨242600, by rfl⟩ : syracuseStep 1293869 = 485201) (by norm_num)
theorem B1228373 : Blo 754331 1228373 := bbase (se 8 (by rfl) ⟨7197, by rfl⟩ : syracuseStep 1228373 = 14395) (by norm_num)
theorem B2866853 : Blo 754331 2866853 := bbase (se 4 (by rfl) ⟨268767, by rfl⟩ : syracuseStep 2866853 = 537535) (by norm_num)
theorem B1916581 : Blo 754331 1916581 := bbase (se 4 (by rfl) ⟨179679, by rfl⟩ : syracuseStep 1916581 = 359359) (by norm_num)
theorem B1916693 : Blo 754331 1916693 := bbase (se 6 (by rfl) ⟨44922, by rfl⟩ : syracuseStep 1916693 = 89845) (by norm_num)
theorem B1916885 : Blo 754331 1916885 := bbase (se 7 (by rfl) ⟨22463, by rfl⟩ : syracuseStep 1916885 = 44927) (by norm_num)
theorem B5750837 : Blo 754331 5750837 := bbase (se 5 (by rfl) ⟨269570, by rfl⟩ : syracuseStep 5750837 = 539141) (by norm_num)
theorem B1917229 : Blo 754331 1917229 := bbase (se 3 (by rfl) ⟨359480, by rfl⟩ : syracuseStep 1917229 = 718961) (by norm_num)
theorem B4309301 : Blo 754331 4309301 := bbase (se 5 (by rfl) ⟨201998, by rfl⟩ : syracuseStep 4309301 = 403997) (by norm_num)
theorem B1818949 : Blo 754331 1818949 := bbase (se 4 (by rfl) ⟨170526, by rfl⟩ : syracuseStep 1818949 = 341053) (by norm_num)
theorem B3457397 : Blo 754331 3457397 := bbase (se 5 (by rfl) ⟨162065, by rfl⟩ : syracuseStep 3457397 = 324131) (by norm_num)
theorem B1360261 : Blo 754331 1360261 := bbase (se 4 (by rfl) ⟨127524, by rfl⟩ : syracuseStep 1360261 = 255049) (by norm_num)
theorem B1917341 : Blo 754331 1917341 := bbase (se 3 (by rfl) ⟨359501, by rfl⟩ : syracuseStep 1917341 = 719003) (by norm_num)
theorem B3228133 : Blo 754331 3228133 := bbase (se 4 (by rfl) ⟨302637, by rfl⟩ : syracuseStep 3228133 = 605275) (by norm_num)
theorem B3228149 : Blo 754331 3228149 := bbase (se 5 (by rfl) ⟨151319, by rfl⟩ : syracuseStep 3228149 = 302639) (by norm_num)
theorem B1917533 : Blo 754331 1917533 := bbase (se 3 (by rfl) ⟨359537, by rfl⟩ : syracuseStep 1917533 = 719075) (by norm_num)
theorem B1360565 : Blo 754331 1360565 := bbase (se 5 (by rfl) ⟨63776, by rfl⟩ : syracuseStep 1360565 = 127553) (by norm_num)
theorem B1458989 : Blo 754331 1458989 := bbase (se 3 (by rfl) ⟨273560, by rfl⟩ : syracuseStep 1458989 = 547121) (by norm_num)
theorem B11027285 : Blo 754331 11027285 := bbase (se 9 (by rfl) ⟨32306, by rfl⟩ : syracuseStep 11027285 = 64613) (by norm_num)
theorem B1819525 : Blo 754331 1819525 := bbase (se 4 (by rfl) ⟨170580, by rfl⟩ : syracuseStep 1819525 = 341161) (by norm_num)
theorem B1917877 : Blo 754331 1917877 := bbase (se 5 (by rfl) ⟨89900, by rfl⟩ : syracuseStep 1917877 = 179801) (by norm_num)
theorem B1131509 : Blo 754331 1131509 := bbase (se 5 (by rfl) ⟨53039, by rfl⟩ : syracuseStep 1131509 = 106079) (by norm_num)
theorem B1131533 : Blo 754331 1131533 := bbase (se 3 (by rfl) ⟨212162, by rfl⟩ : syracuseStep 1131533 = 424325) (by norm_num)
theorem B1131557 : Blo 754331 1131557 := bbase (se 4 (by rfl) ⟨106083, by rfl⟩ : syracuseStep 1131557 = 212167) (by norm_num)
theorem B1917989 : Blo 754331 1917989 := bbase (se 4 (by rfl) ⟨179811, by rfl⟩ : syracuseStep 1917989 = 359623) (by norm_num)
theorem B1131581 : Blo 754331 1131581 := bbase (se 3 (by rfl) ⟨212171, by rfl⟩ : syracuseStep 1131581 = 424343) (by norm_num)
theorem B1131605 : Blo 754331 1131605 := bbase (se 8 (by rfl) ⟨6630, by rfl⟩ : syracuseStep 1131605 = 13261) (by norm_num)
theorem B1131629 : Blo 754331 1131629 := bbase (se 3 (by rfl) ⟨212180, by rfl⟩ : syracuseStep 1131629 = 424361) (by norm_num)
theorem B1131653 : Blo 754331 1131653 := bbase (se 4 (by rfl) ⟨106092, by rfl⟩ : syracuseStep 1131653 = 212185) (by norm_num)
theorem B1131677 : Blo 754331 1131677 := bbase (se 3 (by rfl) ⟨212189, by rfl⟩ : syracuseStep 1131677 = 424379) (by norm_num)
theorem B1131701 : Blo 754331 1131701 := bbase (se 5 (by rfl) ⟨53048, by rfl⟩ : syracuseStep 1131701 = 106097) (by norm_num)
theorem B1131725 : Blo 754331 1131725 := bbase (se 3 (by rfl) ⟨212198, by rfl⟩ : syracuseStep 1131725 = 424397) (by norm_num)
theorem B1819853 : Blo 754331 1819853 := bbase (se 3 (by rfl) ⟨341222, by rfl⟩ : syracuseStep 1819853 = 682445) (by norm_num)
theorem B1131749 : Blo 754331 1131749 := bbase (se 4 (by rfl) ⟨106101, by rfl⟩ : syracuseStep 1131749 = 212203) (by norm_num)
theorem B1918181 : Blo 754331 1918181 := bbase (se 4 (by rfl) ⟨179829, by rfl⟩ : syracuseStep 1918181 = 359659) (by norm_num)
theorem B1131773 : Blo 754331 1131773 := bbase (se 3 (by rfl) ⟨212207, by rfl⟩ : syracuseStep 1131773 = 424415) (by norm_num)
theorem B1819909 : Blo 754331 1819909 := bbase (se 4 (by rfl) ⟨170616, by rfl⟩ : syracuseStep 1819909 = 341233) (by norm_num)
theorem B1131797 : Blo 754331 1131797 := bbase (se 6 (by rfl) ⟨26526, by rfl⟩ : syracuseStep 1131797 = 53053) (by norm_num)
theorem B1131821 : Blo 754331 1131821 := bbase (se 3 (by rfl) ⟨212216, by rfl⟩ : syracuseStep 1131821 = 424433) (by norm_num)
theorem B1131845 : Blo 754331 1131845 := bbase (se 4 (by rfl) ⟨106110, by rfl⟩ : syracuseStep 1131845 = 212221) (by norm_num)
theorem B8635733 : Blo 754331 8635733 := bbase (se 12 (by rfl) ⟨3162, by rfl⟩ : syracuseStep 8635733 = 6325) (by norm_num)
theorem B1131869 : Blo 754331 1131869 := bbase (se 3 (by rfl) ⟨212225, by rfl⟩ : syracuseStep 1131869 = 424451) (by norm_num)
theorem B1131893 : Blo 754331 1131893 := bbase (se 5 (by rfl) ⟨53057, by rfl⟩ : syracuseStep 1131893 = 106115) (by norm_num)
theorem B1131917 : Blo 754331 1131917 := bbase (se 3 (by rfl) ⟨212234, by rfl⟩ : syracuseStep 1131917 = 424469) (by norm_num)
theorem B1131941 : Blo 754331 1131941 := bbase (se 4 (by rfl) ⟨106119, by rfl⟩ : syracuseStep 1131941 = 212239) (by norm_num)
theorem B1131965 : Blo 754331 1131965 := bbase (se 3 (by rfl) ⟨212243, by rfl⟩ : syracuseStep 1131965 = 424487) (by norm_num)
theorem B1131989 : Blo 754331 1131989 := bbase (se 7 (by rfl) ⟨13265, by rfl⟩ : syracuseStep 1131989 = 26531) (by norm_num)
theorem B1132013 : Blo 754331 1132013 := bbase (se 3 (by rfl) ⟨212252, by rfl⟩ : syracuseStep 1132013 = 424505) (by norm_num)
theorem B1820141 : Blo 754331 1820141 := bbase (se 3 (by rfl) ⟨341276, by rfl⟩ : syracuseStep 1820141 = 682553) (by norm_num)
theorem B1132037 : Blo 754331 1132037 := bbase (se 4 (by rfl) ⟨106128, by rfl⟩ : syracuseStep 1132037 = 212257) (by norm_num)
theorem B1132061 : Blo 754331 1132061 := bbase (se 3 (by rfl) ⟨212261, by rfl⟩ : syracuseStep 1132061 = 424523) (by norm_num)
theorem B968225 : Blo 754331 968225 := bbase (se 2 (by rfl) ⟨363084, by rfl⟩ : syracuseStep 968225 = 726169) (by norm_num)
theorem B1132085 : Blo 754331 1132085 := bbase (se 5 (by rfl) ⟨53066, by rfl⟩ : syracuseStep 1132085 = 106133) (by norm_num)
theorem B1918525 : Blo 754331 1918525 := bbase (se 3 (by rfl) ⟨359723, by rfl⟩ : syracuseStep 1918525 = 719447) (by norm_num)
theorem B1132109 : Blo 754331 1132109 := bbase (se 3 (by rfl) ⟨212270, by rfl⟩ : syracuseStep 1132109 = 424541) (by norm_num)
theorem B1132133 : Blo 754331 1132133 := bbase (se 4 (by rfl) ⟨106137, by rfl⟩ : syracuseStep 1132133 = 212275) (by norm_num)
theorem B1132157 : Blo 754331 1132157 := bbase (se 3 (by rfl) ⟨212279, by rfl⟩ : syracuseStep 1132157 = 424559) (by norm_num)
theorem B1132181 : Blo 754331 1132181 := bbase (se 6 (by rfl) ⟨26535, by rfl⟩ : syracuseStep 1132181 = 53071) (by norm_num)
theorem B1132205 : Blo 754331 1132205 := bbase (se 3 (by rfl) ⟨212288, by rfl⟩ : syracuseStep 1132205 = 424577) (by norm_num)
theorem B1820333 : Blo 754331 1820333 := bbase (se 3 (by rfl) ⟨341312, by rfl⟩ : syracuseStep 1820333 = 682625) (by norm_num)
theorem B1918637 : Blo 754331 1918637 := bbase (se 3 (by rfl) ⟨359744, by rfl⟩ : syracuseStep 1918637 = 719489) (by norm_num)
theorem B1132229 : Blo 754331 1132229 := bbase (se 4 (by rfl) ⟨106146, by rfl⟩ : syracuseStep 1132229 = 212293) (by norm_num)
theorem B1132253 : Blo 754331 1132253 := bbase (se 3 (by rfl) ⟨212297, by rfl⟩ : syracuseStep 1132253 = 424595) (by norm_num)
theorem B2868965 : Blo 754331 2868965 := bbase (se 4 (by rfl) ⟨268965, by rfl⟩ : syracuseStep 2868965 = 537931) (by norm_num)
theorem B1132277 : Blo 754331 1132277 := bbase (se 5 (by rfl) ⟨53075, by rfl⟩ : syracuseStep 1132277 = 106151) (by norm_num)
theorem B1132301 : Blo 754331 1132301 := bbase (se 3 (by rfl) ⟨212306, by rfl⟩ : syracuseStep 1132301 = 424613) (by norm_num)
theorem B1132325 : Blo 754331 1132325 := bbase (se 4 (by rfl) ⟨106155, by rfl⟩ : syracuseStep 1132325 = 212311) (by norm_num)
theorem B1132349 : Blo 754331 1132349 := bbase (se 3 (by rfl) ⟨212315, by rfl⟩ : syracuseStep 1132349 = 424631) (by norm_num)
theorem B1132373 : Blo 754331 1132373 := bbase (se 9 (by rfl) ⟨3317, by rfl⟩ : syracuseStep 1132373 = 6635) (by norm_num)
theorem B1132397 : Blo 754331 1132397 := bbase (se 3 (by rfl) ⟨212324, by rfl⟩ : syracuseStep 1132397 = 424649) (by norm_num)
theorem B1918829 : Blo 754331 1918829 := bbase (se 3 (by rfl) ⟨359780, by rfl⟩ : syracuseStep 1918829 = 719561) (by norm_num)
theorem B1132421 : Blo 754331 1132421 := bbase (se 4 (by rfl) ⟨106164, by rfl⟩ : syracuseStep 1132421 = 212329) (by norm_num)
theorem B1132445 : Blo 754331 1132445 := bbase (se 3 (by rfl) ⟨212333, by rfl⟩ : syracuseStep 1132445 = 424667) (by norm_num)
theorem B1132469 : Blo 754331 1132469 := bbase (se 5 (by rfl) ⟨53084, by rfl⟩ : syracuseStep 1132469 = 106169) (by norm_num)
theorem B1132493 : Blo 754331 1132493 := bbase (se 3 (by rfl) ⟨212342, by rfl⟩ : syracuseStep 1132493 = 424685) (by norm_num)
theorem B1132517 : Blo 754331 1132517 := bbase (se 4 (by rfl) ⟨106173, by rfl⟩ : syracuseStep 1132517 = 212347) (by norm_num)
theorem B1132541 : Blo 754331 1132541 := bbase (se 3 (by rfl) ⟨212351, by rfl⟩ : syracuseStep 1132541 = 424703) (by norm_num)
theorem B2869253 : Blo 754331 2869253 := bbase (se 4 (by rfl) ⟨268992, by rfl⟩ : syracuseStep 2869253 = 537985) (by norm_num)
theorem B1132565 : Blo 754331 1132565 := bbase (se 6 (by rfl) ⟨26544, by rfl⟩ : syracuseStep 1132565 = 53089) (by norm_num)
theorem B1034285 : Blo 754331 1034285 := bbase (se 3 (by rfl) ⟨193928, by rfl⟩ : syracuseStep 1034285 = 387857) (by norm_num)
theorem B1132589 : Blo 754331 1132589 := bbase (se 3 (by rfl) ⟨212360, by rfl⟩ : syracuseStep 1132589 = 424721) (by norm_num)
theorem B1132613 : Blo 754331 1132613 := bbase (se 4 (by rfl) ⟨106182, by rfl⟩ : syracuseStep 1132613 = 212365) (by norm_num)
theorem B1132637 : Blo 754331 1132637 := bbase (se 3 (by rfl) ⟨212369, by rfl⟩ : syracuseStep 1132637 = 424739) (by norm_num)
theorem B1132661 : Blo 754331 1132661 := bbase (se 5 (by rfl) ⟨53093, by rfl⟩ : syracuseStep 1132661 = 106187) (by norm_num)
theorem B1132685 : Blo 754331 1132685 := bbase (se 3 (by rfl) ⟨212378, by rfl⟩ : syracuseStep 1132685 = 424757) (by norm_num)
theorem B1132709 : Blo 754331 1132709 := bbase (se 4 (by rfl) ⟨106191, by rfl⟩ : syracuseStep 1132709 = 212383) (by norm_num)
theorem B1132733 : Blo 754331 1132733 := bbase (se 3 (by rfl) ⟨212387, by rfl⟩ : syracuseStep 1132733 = 424775) (by norm_num)
theorem B1919173 : Blo 754331 1919173 := bbase (se 4 (by rfl) ⟨179922, by rfl⟩ : syracuseStep 1919173 = 359845) (by norm_num)
theorem B1132757 : Blo 754331 1132757 := bbase (se 7 (by rfl) ⟨13274, by rfl⟩ : syracuseStep 1132757 = 26549) (by norm_num)
theorem B1132781 : Blo 754331 1132781 := bbase (se 3 (by rfl) ⟨212396, by rfl⟩ : syracuseStep 1132781 = 424793) (by norm_num)
theorem B1132805 : Blo 754331 1132805 := bbase (se 4 (by rfl) ⟨106200, by rfl⟩ : syracuseStep 1132805 = 212401) (by norm_num)
theorem B3819797 : Blo 754331 3819797 := bbase (se 6 (by rfl) ⟨89526, by rfl⟩ : syracuseStep 3819797 = 179053) (by norm_num)
theorem B1132829 : Blo 754331 1132829 := bbase (se 3 (by rfl) ⟨212405, by rfl⟩ : syracuseStep 1132829 = 424811) (by norm_num)
theorem B1132853 : Blo 754331 1132853 := bbase (se 5 (by rfl) ⟨53102, by rfl⟩ : syracuseStep 1132853 = 106205) (by norm_num)
theorem B5458229 : Blo 754331 5458229 := bbase (se 5 (by rfl) ⟨255854, by rfl⟩ : syracuseStep 5458229 = 511709) (by norm_num)
theorem B1919285 : Blo 754331 1919285 := bbase (se 5 (by rfl) ⟨89966, by rfl⟩ : syracuseStep 1919285 = 179933) (by norm_num)
theorem B1132877 : Blo 754331 1132877 := bbase (se 3 (by rfl) ⟨212414, by rfl⟩ : syracuseStep 1132877 = 424829) (by norm_num)
theorem B1132901 : Blo 754331 1132901 := bbase (se 4 (by rfl) ⟨106209, by rfl⟩ : syracuseStep 1132901 = 212419) (by norm_num)
theorem B1132925 : Blo 754331 1132925 := bbase (se 3 (by rfl) ⟨212423, by rfl⟩ : syracuseStep 1132925 = 424847) (by norm_num)
theorem B1132949 : Blo 754331 1132949 := bbase (se 6 (by rfl) ⟨26553, by rfl⟩ : syracuseStep 1132949 = 53107) (by norm_num)
theorem B1132973 : Blo 754331 1132973 := bbase (se 3 (by rfl) ⟨212432, by rfl⟩ : syracuseStep 1132973 = 424865) (by norm_num)
theorem B1132997 : Blo 754331 1132997 := bbase (se 4 (by rfl) ⟨106218, by rfl⟩ : syracuseStep 1132997 = 212437) (by norm_num)
theorem B1133021 : Blo 754331 1133021 := bbase (se 3 (by rfl) ⟨212441, by rfl⟩ : syracuseStep 1133021 = 424883) (by norm_num)
theorem B1133045 : Blo 754331 1133045 := bbase (se 5 (by rfl) ⟨53111, by rfl⟩ : syracuseStep 1133045 = 106223) (by norm_num)
theorem B1919477 : Blo 754331 1919477 := bbase (se 5 (by rfl) ⟨89975, by rfl⟩ : syracuseStep 1919477 = 179951) (by norm_num)
theorem B1133069 : Blo 754331 1133069 := bbase (se 3 (by rfl) ⟨212450, by rfl⟩ : syracuseStep 1133069 = 424901) (by norm_num)
theorem B1133093 : Blo 754331 1133093 := bbase (se 4 (by rfl) ⟨106227, by rfl⟩ : syracuseStep 1133093 = 212455) (by norm_num)
theorem B1133117 : Blo 754331 1133117 := bbase (se 3 (by rfl) ⟨212459, by rfl⟩ : syracuseStep 1133117 = 424919) (by norm_num)
theorem B1133141 : Blo 754331 1133141 := bbase (se 8 (by rfl) ⟨6639, by rfl⟩ : syracuseStep 1133141 = 13279) (by norm_num)
theorem B1133165 : Blo 754331 1133165 := bbase (se 3 (by rfl) ⟨212468, by rfl⟩ : syracuseStep 1133165 = 424937) (by norm_num)
theorem B1821293 : Blo 754331 1821293 := bbase (se 3 (by rfl) ⟨341492, by rfl⟩ : syracuseStep 1821293 = 682985) (by norm_num)
theorem B1133189 : Blo 754331 1133189 := bbase (se 4 (by rfl) ⟨106236, by rfl⟩ : syracuseStep 1133189 = 212473) (by norm_num)
theorem B1133213 : Blo 754331 1133213 := bbase (se 3 (by rfl) ⟨212477, by rfl⟩ : syracuseStep 1133213 = 424955) (by norm_num)
theorem B1133237 : Blo 754331 1133237 := bbase (se 5 (by rfl) ⟨53120, by rfl⟩ : syracuseStep 1133237 = 106241) (by norm_num)
theorem B3230405 : Blo 754331 3230405 := bbase (se 4 (by rfl) ⟨302850, by rfl⟩ : syracuseStep 3230405 = 605701) (by norm_num)
theorem B1297093 : Blo 754331 1297093 := bbase (se 4 (by rfl) ⟨121602, by rfl⟩ : syracuseStep 1297093 = 243205) (by norm_num)
theorem B1133261 : Blo 754331 1133261 := bbase (se 3 (by rfl) ⟨212486, by rfl⟩ : syracuseStep 1133261 = 424973) (by norm_num)
theorem B1133285 : Blo 754331 1133285 := bbase (se 4 (by rfl) ⟨106245, by rfl⟩ : syracuseStep 1133285 = 212491) (by norm_num)
theorem B1133309 : Blo 754331 1133309 := bbase (se 3 (by rfl) ⟨212495, by rfl⟩ : syracuseStep 1133309 = 424991) (by norm_num)
theorem B1133333 : Blo 754331 1133333 := bbase (se 6 (by rfl) ⟨26562, by rfl⟩ : syracuseStep 1133333 = 53125) (by norm_num)
theorem B6146837 : Blo 754331 6146837 := bbase (se 6 (by rfl) ⟨144066, by rfl⟩ : syracuseStep 6146837 = 288133) (by norm_num)
theorem B1133357 : Blo 754331 1133357 := bbase (se 3 (by rfl) ⟨212504, by rfl⟩ : syracuseStep 1133357 = 425009) (by norm_num)
theorem B1723205 : Blo 754331 1723205 := bbase (se 4 (by rfl) ⟨161550, by rfl⟩ : syracuseStep 1723205 = 323101) (by norm_num)
theorem B1133381 : Blo 754331 1133381 := bbase (se 4 (by rfl) ⟨106254, by rfl⟩ : syracuseStep 1133381 = 212509) (by norm_num)
theorem B1133405 : Blo 754331 1133405 := bbase (se 3 (by rfl) ⟨212513, by rfl⟩ : syracuseStep 1133405 = 425027) (by norm_num)
theorem B1133429 : Blo 754331 1133429 := bbase (se 5 (by rfl) ⟨53129, by rfl⟩ : syracuseStep 1133429 = 106259) (by norm_num)
theorem B6474613 : Blo 754331 6474613 := bbase (se 5 (by rfl) ⟨303497, by rfl⟩ : syracuseStep 6474613 = 606995) (by norm_num)
theorem B1133453 : Blo 754331 1133453 := bbase (se 3 (by rfl) ⟨212522, by rfl⟩ : syracuseStep 1133453 = 425045) (by norm_num)
theorem B969617 : Blo 754331 969617 := bbase (se 2 (by rfl) ⟨363606, by rfl⟩ : syracuseStep 969617 = 727213) (by norm_num)
theorem B1133477 : Blo 754331 1133477 := bbase (se 4 (by rfl) ⟨106263, by rfl⟩ : syracuseStep 1133477 = 212527) (by norm_num)
theorem B4836277 : Blo 754331 4836277 := bbase (se 5 (by rfl) ⟨226700, by rfl⟩ : syracuseStep 4836277 = 453401) (by norm_num)
theorem B1133501 : Blo 754331 1133501 := bbase (se 3 (by rfl) ⟨212531, by rfl⟩ : syracuseStep 1133501 = 425063) (by norm_num)
theorem B1133525 : Blo 754331 1133525 := bbase (se 7 (by rfl) ⟨13283, by rfl⟩ : syracuseStep 1133525 = 26567) (by norm_num)
theorem B1133549 : Blo 754331 1133549 := bbase (se 3 (by rfl) ⟨212540, by rfl⟩ : syracuseStep 1133549 = 425081) (by norm_num)
theorem B1133573 : Blo 754331 1133573 := bbase (se 4 (by rfl) ⟨106272, by rfl⟩ : syracuseStep 1133573 = 212545) (by norm_num)
theorem B1133597 : Blo 754331 1133597 := bbase (se 3 (by rfl) ⟨212549, by rfl⟩ : syracuseStep 1133597 = 425099) (by norm_num)
theorem B1133621 : Blo 754331 1133621 := bbase (se 5 (by rfl) ⟨53138, by rfl⟩ : syracuseStep 1133621 = 106277) (by norm_num)
theorem B805961 : Blo 754331 805961 := bbase (se 2 (by rfl) ⟨302235, by rfl⟩ : syracuseStep 805961 = 604471) (by norm_num)
theorem B1133645 : Blo 754331 1133645 := bbase (se 3 (by rfl) ⟨212558, by rfl⟩ : syracuseStep 1133645 = 425117) (by norm_num)
theorem B1133669 : Blo 754331 1133669 := bbase (se 4 (by rfl) ⟨106281, by rfl⟩ : syracuseStep 1133669 = 212563) (by norm_num)
theorem B1133693 : Blo 754331 1133693 := bbase (se 3 (by rfl) ⟨212567, by rfl⟩ : syracuseStep 1133693 = 425135) (by norm_num)
theorem B1133717 : Blo 754331 1133717 := bbase (se 6 (by rfl) ⟨26571, by rfl⟩ : syracuseStep 1133717 = 53143) (by norm_num)
theorem B2870437 : Blo 754331 2870437 := bbase (se 4 (by rfl) ⟨269103, by rfl⟩ : syracuseStep 2870437 = 538207) (by norm_num)
theorem B1133741 : Blo 754331 1133741 := bbase (se 3 (by rfl) ⟨212576, by rfl⟩ : syracuseStep 1133741 = 425153) (by norm_num)
theorem B1133765 : Blo 754331 1133765 := bbase (se 4 (by rfl) ⟨106290, by rfl⟩ : syracuseStep 1133765 = 212581) (by norm_num)
theorem B1133789 : Blo 754331 1133789 := bbase (se 3 (by rfl) ⟨212585, by rfl⟩ : syracuseStep 1133789 = 425171) (by norm_num)
theorem B3067109 : Blo 754331 3067109 := bbase (se 4 (by rfl) ⟨287541, by rfl⟩ : syracuseStep 3067109 = 575083) (by norm_num)
theorem B1133813 : Blo 754331 1133813 := bbase (se 5 (by rfl) ⟨53147, by rfl⟩ : syracuseStep 1133813 = 106295) (by norm_num)
theorem B806149 : Blo 754331 806149 := bbase (se 4 (by rfl) ⟨75576, by rfl⟩ : syracuseStep 806149 = 151153) (by norm_num)
theorem B1133837 : Blo 754331 1133837 := bbase (se 3 (by rfl) ⟨212594, by rfl⟩ : syracuseStep 1133837 = 425189) (by norm_num)
theorem B1133861 : Blo 754331 1133861 := bbase (se 4 (by rfl) ⟨106299, by rfl⟩ : syracuseStep 1133861 = 212599) (by norm_num)
theorem B2149685 : Blo 754331 2149685 := bbase (se 5 (by rfl) ⟨100766, by rfl⟩ : syracuseStep 2149685 = 201533) (by norm_num)
theorem B5918005 : Blo 754331 5918005 := bbase (se 5 (by rfl) ⟨277406, by rfl⟩ : syracuseStep 5918005 = 554813) (by norm_num)
theorem B1133885 : Blo 754331 1133885 := bbase (se 3 (by rfl) ⟨212603, by rfl⟩ : syracuseStep 1133885 = 425207) (by norm_num)
theorem B1133909 : Blo 754331 1133909 := bbase (se 11 (by rfl) ⟨830, by rfl⟩ : syracuseStep 1133909 = 1661) (by norm_num)
theorem B1133933 : Blo 754331 1133933 := bbase (se 3 (by rfl) ⟨212612, by rfl⟩ : syracuseStep 1133933 = 425225) (by norm_num)
theorem B1133957 : Blo 754331 1133957 := bbase (se 4 (by rfl) ⟨106308, by rfl⟩ : syracuseStep 1133957 = 212617) (by norm_num)
theorem B1363333 : Blo 754331 1363333 := bbase (se 4 (by rfl) ⟨127812, by rfl⟩ : syracuseStep 1363333 = 255625) (by norm_num)
theorem B1723789 : Blo 754331 1723789 := bbase (se 3 (by rfl) ⟨323210, by rfl⟩ : syracuseStep 1723789 = 646421) (by norm_num)
theorem B1133981 : Blo 754331 1133981 := bbase (se 3 (by rfl) ⟨212621, by rfl⟩ : syracuseStep 1133981 = 425243) (by norm_num)
theorem B1134005 : Blo 754331 1134005 := bbase (se 5 (by rfl) ⟨53156, by rfl⟩ : syracuseStep 1134005 = 106313) (by norm_num)
theorem B1134029 : Blo 754331 1134029 := bbase (se 3 (by rfl) ⟨212630, by rfl⟩ : syracuseStep 1134029 = 425261) (by norm_num)
theorem B1363405 : Blo 754331 1363405 := bbase (se 3 (by rfl) ⟨255638, by rfl⟩ : syracuseStep 1363405 = 511277) (by norm_num)
theorem B2870741 : Blo 754331 2870741 := bbase (se 7 (by rfl) ⟨33641, by rfl⟩ : syracuseStep 2870741 = 67283) (by norm_num)
theorem B1134053 : Blo 754331 1134053 := bbase (se 4 (by rfl) ⟨106317, by rfl⟩ : syracuseStep 1134053 = 212635) (by norm_num)
theorem B1134077 : Blo 754331 1134077 := bbase (se 3 (by rfl) ⟨212639, by rfl⟩ : syracuseStep 1134077 = 425279) (by norm_num)
theorem B1134101 : Blo 754331 1134101 := bbase (se 6 (by rfl) ⟨26580, by rfl⟩ : syracuseStep 1134101 = 53161) (by norm_num)
theorem B3821093 : Blo 754331 3821093 := bbase (se 4 (by rfl) ⟨358227, by rfl⟩ : syracuseStep 3821093 = 716455) (by norm_num)
theorem B1134125 : Blo 754331 1134125 := bbase (se 3 (by rfl) ⟨212648, by rfl⟩ : syracuseStep 1134125 = 425297) (by norm_num)
theorem B1134149 : Blo 754331 1134149 := bbase (se 4 (by rfl) ⟨106326, by rfl⟩ : syracuseStep 1134149 = 212653) (by norm_num)
theorem B1134173 : Blo 754331 1134173 := bbase (se 3 (by rfl) ⟨212657, by rfl⟩ : syracuseStep 1134173 = 425315) (by norm_num)
theorem B1134197 : Blo 754331 1134197 := bbase (se 5 (by rfl) ⟨53165, by rfl⟩ : syracuseStep 1134197 = 106331) (by norm_num)
theorem B1134221 : Blo 754331 1134221 := bbase (se 3 (by rfl) ⟨212666, by rfl⟩ : syracuseStep 1134221 = 425333) (by norm_num)
theorem B1134245 : Blo 754331 1134245 := bbase (se 4 (by rfl) ⟨106335, by rfl⟩ : syracuseStep 1134245 = 212671) (by norm_num)
theorem B1134269 : Blo 754331 1134269 := bbase (se 3 (by rfl) ⟨212675, by rfl⟩ : syracuseStep 1134269 = 425351) (by norm_num)
theorem B1134293 : Blo 754331 1134293 := bbase (se 7 (by rfl) ⟨13292, by rfl⟩ : syracuseStep 1134293 = 26585) (by norm_num)
theorem B1134317 : Blo 754331 1134317 := bbase (se 3 (by rfl) ⟨212684, by rfl⟩ : syracuseStep 1134317 = 425369) (by norm_num)
theorem B1134341 : Blo 754331 1134341 := bbase (se 4 (by rfl) ⟨106344, by rfl⟩ : syracuseStep 1134341 = 212689) (by norm_num)
theorem B1134365 : Blo 754331 1134365 := bbase (se 3 (by rfl) ⟨212693, by rfl⟩ : syracuseStep 1134365 = 425387) (by norm_num)
theorem B1134389 : Blo 754331 1134389 := bbase (se 5 (by rfl) ⟨53174, by rfl⟩ : syracuseStep 1134389 = 106349) (by norm_num)
theorem B1134413 : Blo 754331 1134413 := bbase (se 3 (by rfl) ⟨212702, by rfl⟩ : syracuseStep 1134413 = 425405) (by norm_num)
theorem B13782869 : Blo 754331 13782869 := bbase (se 9 (by rfl) ⟨40379, by rfl⟩ : syracuseStep 13782869 = 80759) (by norm_num)
theorem B1134437 : Blo 754331 1134437 := bbase (se 4 (by rfl) ⟨106353, by rfl⟩ : syracuseStep 1134437 = 212707) (by norm_num)
theorem B1134461 : Blo 754331 1134461 := bbase (se 3 (by rfl) ⟨212711, by rfl⟩ : syracuseStep 1134461 = 425423) (by norm_num)
theorem B1134485 : Blo 754331 1134485 := bbase (se 6 (by rfl) ⟨26589, by rfl⟩ : syracuseStep 1134485 = 53179) (by norm_num)
theorem B1134509 : Blo 754331 1134509 := bbase (se 3 (by rfl) ⟨212720, by rfl⟩ : syracuseStep 1134509 = 425441) (by norm_num)
theorem B1134533 : Blo 754331 1134533 := bbase (se 4 (by rfl) ⟨106362, by rfl⟩ : syracuseStep 1134533 = 212725) (by norm_num)
theorem B1134557 : Blo 754331 1134557 := bbase (se 3 (by rfl) ⟨212729, by rfl⟩ : syracuseStep 1134557 = 425459) (by norm_num)
theorem B970729 : Blo 754331 970729 := bbase (se 2 (by rfl) ⟨364023, by rfl⟩ : syracuseStep 970729 = 728047) (by norm_num)
theorem B1703933 : Blo 754331 1703933 := bbase (se 3 (by rfl) ⟨319487, by rfl⟩ : syracuseStep 1703933 = 638975) (by norm_num)
theorem B1134581 : Blo 754331 1134581 := bbase (se 5 (by rfl) ⟨53183, by rfl⟩ : syracuseStep 1134581 = 106367) (by norm_num)
theorem B1134605 : Blo 754331 1134605 := bbase (se 3 (by rfl) ⟨212738, by rfl⟩ : syracuseStep 1134605 = 425477) (by norm_num)
theorem B1134629 : Blo 754331 1134629 := bbase (se 4 (by rfl) ⟨106371, by rfl⟩ : syracuseStep 1134629 = 212743) (by norm_num)
theorem B806969 : Blo 754331 806969 := bbase (se 2 (by rfl) ⟨302613, by rfl⟩ : syracuseStep 806969 = 605227) (by norm_num)
theorem B1134653 : Blo 754331 1134653 := bbase (se 3 (by rfl) ⟨212747, by rfl⟩ : syracuseStep 1134653 = 425495) (by norm_num)
theorem B1134677 : Blo 754331 1134677 := bbase (se 8 (by rfl) ⟨6648, by rfl⟩ : syracuseStep 1134677 = 13297) (by norm_num)
theorem B1134701 : Blo 754331 1134701 := bbase (se 3 (by rfl) ⟨212756, by rfl⟩ : syracuseStep 1134701 = 425513) (by norm_num)
theorem B1134725 : Blo 754331 1134725 := bbase (se 4 (by rfl) ⟨106380, by rfl⟩ : syracuseStep 1134725 = 212761) (by norm_num)
theorem B1134749 : Blo 754331 1134749 := bbase (se 3 (by rfl) ⟨212765, by rfl⟩ : syracuseStep 1134749 = 425531) (by norm_num)
theorem B1134773 : Blo 754331 1134773 := bbase (se 5 (by rfl) ⟨53192, by rfl⟩ : syracuseStep 1134773 = 106385) (by norm_num)
theorem B1134797 : Blo 754331 1134797 := bbase (se 3 (by rfl) ⟨212774, by rfl⟩ : syracuseStep 1134797 = 425549) (by norm_num)
theorem B1134821 : Blo 754331 1134821 := bbase (se 4 (by rfl) ⟨106389, by rfl⟩ : syracuseStep 1134821 = 212779) (by norm_num)
theorem B1134845 : Blo 754331 1134845 := bbase (se 3 (by rfl) ⟨212783, by rfl⟩ : syracuseStep 1134845 = 425567) (by norm_num)
theorem B1134869 : Blo 754331 1134869 := bbase (se 6 (by rfl) ⟨26598, by rfl⟩ : syracuseStep 1134869 = 53197) (by norm_num)
theorem B1134893 : Blo 754331 1134893 := bbase (se 3 (by rfl) ⟨212792, by rfl⟩ : syracuseStep 1134893 = 425585) (by norm_num)
theorem B1134917 : Blo 754331 1134917 := bbase (se 4 (by rfl) ⟨106398, by rfl⟩ : syracuseStep 1134917 = 212797) (by norm_num)
theorem B1134941 : Blo 754331 1134941 := bbase (se 3 (by rfl) ⟨212801, by rfl⟩ : syracuseStep 1134941 = 425603) (by norm_num)
theorem B1134965 : Blo 754331 1134965 := bbase (se 5 (by rfl) ⟨53201, by rfl⟩ : syracuseStep 1134965 = 106403) (by norm_num)
theorem B1134989 : Blo 754331 1134989 := bbase (se 3 (by rfl) ⟨212810, by rfl⟩ : syracuseStep 1134989 = 425621) (by norm_num)
theorem B1135013 : Blo 754331 1135013 := bbase (se 4 (by rfl) ⟨106407, by rfl⟩ : syracuseStep 1135013 = 212815) (by norm_num)
theorem B1135037 : Blo 754331 1135037 := bbase (se 3 (by rfl) ⟨212819, by rfl⟩ : syracuseStep 1135037 = 425639) (by norm_num)
theorem B1364413 : Blo 754331 1364413 := bbase (se 3 (by rfl) ⟨255827, by rfl⟩ : syracuseStep 1364413 = 511655) (by norm_num)
theorem B2150869 : Blo 754331 2150869 := bbase (se 7 (by rfl) ⟨25205, by rfl⟩ : syracuseStep 2150869 = 50411) (by norm_num)
theorem B1135061 : Blo 754331 1135061 := bbase (se 7 (by rfl) ⟨13301, by rfl⟩ : syracuseStep 1135061 = 26603) (by norm_num)
theorem B971233 : Blo 754331 971233 := bbase (se 2 (by rfl) ⟨364212, by rfl⟩ : syracuseStep 971233 = 728425) (by norm_num)
theorem B1135085 : Blo 754331 1135085 := bbase (se 3 (by rfl) ⟨212828, by rfl⟩ : syracuseStep 1135085 = 425657) (by norm_num)
theorem B807413 : Blo 754331 807413 := bbase (se 5 (by rfl) ⟨37847, by rfl⟩ : syracuseStep 807413 = 75695) (by norm_num)
theorem B2183669 : Blo 754331 2183669 := bbase (se 5 (by rfl) ⟨102359, by rfl⟩ : syracuseStep 2183669 = 204719) (by norm_num)
theorem B1135109 : Blo 754331 1135109 := bbase (se 4 (by rfl) ⟨106416, by rfl⟩ : syracuseStep 1135109 = 212833) (by norm_num)
theorem B1364501 : Blo 754331 1364501 := bbase (se 6 (by rfl) ⟨31980, by rfl⟩ : syracuseStep 1364501 = 63961) (by norm_num)
theorem B1135133 : Blo 754331 1135133 := bbase (se 3 (by rfl) ⟨212837, by rfl⟩ : syracuseStep 1135133 = 425675) (by norm_num)
theorem B1135157 : Blo 754331 1135157 := bbase (se 5 (by rfl) ⟨53210, by rfl⟩ : syracuseStep 1135157 = 106421) (by norm_num)
theorem B1135181 : Blo 754331 1135181 := bbase (se 3 (by rfl) ⟨212846, by rfl⟩ : syracuseStep 1135181 = 425693) (by norm_num)
theorem B2904661 : Blo 754331 2904661 := bbase (se 8 (by rfl) ⟨17019, by rfl⟩ : syracuseStep 2904661 = 34039) (by norm_num)
theorem B1135205 : Blo 754331 1135205 := bbase (se 4 (by rfl) ⟨106425, by rfl⟩ : syracuseStep 1135205 = 212851) (by norm_num)
theorem B2151029 : Blo 754331 2151029 := bbase (se 5 (by rfl) ⟨100829, by rfl⟩ : syracuseStep 2151029 = 201659) (by norm_num)
theorem B1135229 : Blo 754331 1135229 := bbase (se 3 (by rfl) ⟨212855, by rfl⟩ : syracuseStep 1135229 = 425711) (by norm_num)
theorem B1725077 : Blo 754331 1725077 := bbase (se 6 (by rfl) ⟨40431, by rfl⟩ : syracuseStep 1725077 = 80863) (by norm_num)
theorem B1135253 : Blo 754331 1135253 := bbase (se 6 (by rfl) ⟨26607, by rfl⟩ : syracuseStep 1135253 = 53215) (by norm_num)
theorem B1135277 : Blo 754331 1135277 := bbase (se 3 (by rfl) ⟨212864, by rfl⟩ : syracuseStep 1135277 = 425729) (by norm_num)
theorem B1135301 : Blo 754331 1135301 := bbase (se 4 (by rfl) ⟨106434, by rfl⟩ : syracuseStep 1135301 = 212869) (by norm_num)
theorem B1135325 : Blo 754331 1135325 := bbase (se 3 (by rfl) ⟨212873, by rfl⟩ : syracuseStep 1135325 = 425747) (by norm_num)
theorem B807661 : Blo 754331 807661 := bbase (se 3 (by rfl) ⟨151436, by rfl⟩ : syracuseStep 807661 = 302873) (by norm_num)
theorem B1135349 : Blo 754331 1135349 := bbase (se 5 (by rfl) ⟨53219, by rfl⟩ : syracuseStep 1135349 = 106439) (by norm_num)
theorem B1135373 : Blo 754331 1135373 := bbase (se 3 (by rfl) ⟨212882, by rfl⟩ : syracuseStep 1135373 = 425765) (by norm_num)
theorem B1135397 : Blo 754331 1135397 := bbase (se 4 (by rfl) ⟨106443, by rfl⟩ : syracuseStep 1135397 = 212887) (by norm_num)
theorem B3822389 : Blo 754331 3822389 := bbase (se 5 (by rfl) ⟨179174, by rfl⟩ : syracuseStep 3822389 = 358349) (by norm_num)
theorem B1364789 : Blo 754331 1364789 := bbase (se 5 (by rfl) ⟨63974, by rfl⟩ : syracuseStep 1364789 = 127949) (by norm_num)
theorem B6476597 : Blo 754331 6476597 := bbase (se 5 (by rfl) ⟨303590, by rfl⟩ : syracuseStep 6476597 = 607181) (by norm_num)
theorem B1135421 : Blo 754331 1135421 := bbase (se 3 (by rfl) ⟨212891, by rfl⟩ : syracuseStep 1135421 = 425783) (by norm_num)
theorem B1135445 : Blo 754331 1135445 := bbase (se 9 (by rfl) ⟨3326, by rfl⟩ : syracuseStep 1135445 = 6653) (by norm_num)
theorem B2151269 : Blo 754331 2151269 := bbase (se 4 (by rfl) ⟨201681, by rfl⟩ : syracuseStep 2151269 = 403363) (by norm_num)
theorem B1135469 : Blo 754331 1135469 := bbase (se 3 (by rfl) ⟨212900, by rfl⟩ : syracuseStep 1135469 = 425801) (by norm_num)
theorem B1135493 : Blo 754331 1135493 := bbase (se 4 (by rfl) ⟨106452, by rfl⟩ : syracuseStep 1135493 = 212905) (by norm_num)
theorem B971669 : Blo 754331 971669 := bbase (se 6 (by rfl) ⟨22773, by rfl⟩ : syracuseStep 971669 = 45547) (by norm_num)
theorem B1135517 : Blo 754331 1135517 := bbase (se 3 (by rfl) ⟨212909, by rfl⟩ : syracuseStep 1135517 = 425819) (by norm_num)
theorem B1135541 : Blo 754331 1135541 := bbase (se 5 (by rfl) ⟨53228, by rfl⟩ : syracuseStep 1135541 = 106457) (by norm_num)
theorem B1135565 : Blo 754331 1135565 := bbase (se 3 (by rfl) ⟨212918, by rfl⟩ : syracuseStep 1135565 = 425837) (by norm_num)
theorem B1135589 : Blo 754331 1135589 := bbase (se 4 (by rfl) ⟨106461, by rfl⟩ : syracuseStep 1135589 = 212923) (by norm_num)
theorem B1135613 : Blo 754331 1135613 := bbase (se 3 (by rfl) ⟨212927, by rfl⟩ : syracuseStep 1135613 = 425855) (by norm_num)
theorem B1365005 : Blo 754331 1365005 := bbase (se 3 (by rfl) ⟨255938, by rfl⟩ : syracuseStep 1365005 = 511877) (by norm_num)
theorem B1135637 : Blo 754331 1135637 := bbase (se 6 (by rfl) ⟨26616, by rfl⟩ : syracuseStep 1135637 = 53233) (by norm_num)
theorem B2151461 : Blo 754331 2151461 := bbase (se 4 (by rfl) ⟨201699, by rfl⟩ : syracuseStep 2151461 = 403399) (by norm_num)
theorem B1135661 : Blo 754331 1135661 := bbase (se 3 (by rfl) ⟨212936, by rfl⟩ : syracuseStep 1135661 = 425873) (by norm_num)
theorem B1135685 : Blo 754331 1135685 := bbase (se 4 (by rfl) ⟨106470, by rfl⟩ : syracuseStep 1135685 = 212941) (by norm_num)
theorem B1135709 : Blo 754331 1135709 := bbase (se 3 (by rfl) ⟨212945, by rfl⟩ : syracuseStep 1135709 = 425891) (by norm_num)
theorem B906337 : Blo 754331 906337 := bbase (se 2 (by rfl) ⟨339876, by rfl⟩ : syracuseStep 906337 = 679753) (by norm_num)
theorem B1135733 : Blo 754331 1135733 := bbase (se 5 (by rfl) ⟨53237, by rfl⟩ : syracuseStep 1135733 = 106475) (by norm_num)
theorem B1135757 : Blo 754331 1135757 := bbase (se 3 (by rfl) ⟨212954, by rfl⟩ : syracuseStep 1135757 = 425909) (by norm_num)
theorem B808093 : Blo 754331 808093 := bbase (se 3 (by rfl) ⟨151517, by rfl⟩ : syracuseStep 808093 = 303035) (by norm_num)
theorem B1135781 : Blo 754331 1135781 := bbase (se 4 (by rfl) ⟨106479, by rfl⟩ : syracuseStep 1135781 = 212959) (by norm_num)
theorem B1135805 : Blo 754331 1135805 := bbase (se 3 (by rfl) ⟨212963, by rfl⟩ : syracuseStep 1135805 = 425927) (by norm_num)
theorem B1135829 : Blo 754331 1135829 := bbase (se 7 (by rfl) ⟨13310, by rfl⟩ : syracuseStep 1135829 = 26621) (by norm_num)
theorem B2184421 : Blo 754331 2184421 := bbase (se 4 (by rfl) ⟨204789, by rfl⟩ : syracuseStep 2184421 = 409579) (by norm_num)
theorem B808165 : Blo 754331 808165 := bbase (se 4 (by rfl) ⟨75765, by rfl⟩ : syracuseStep 808165 = 151531) (by norm_num)
theorem B1135853 : Blo 754331 1135853 := bbase (se 3 (by rfl) ⟨212972, by rfl⟩ : syracuseStep 1135853 = 425945) (by norm_num)
theorem B1135877 : Blo 754331 1135877 := bbase (se 4 (by rfl) ⟨106488, by rfl⟩ : syracuseStep 1135877 = 212977) (by norm_num)
theorem B1135901 : Blo 754331 1135901 := bbase (se 3 (by rfl) ⟨212981, by rfl⟩ : syracuseStep 1135901 = 425963) (by norm_num)
theorem B1135925 : Blo 754331 1135925 := bbase (se 5 (by rfl) ⟨53246, by rfl⟩ : syracuseStep 1135925 = 106493) (by norm_num)
theorem B1135949 : Blo 754331 1135949 := bbase (se 3 (by rfl) ⟨212990, by rfl⟩ : syracuseStep 1135949 = 425981) (by norm_num)
theorem B1135973 : Blo 754331 1135973 := bbase (se 4 (by rfl) ⟨106497, by rfl⟩ : syracuseStep 1135973 = 212995) (by norm_num)
theorem B1135997 : Blo 754331 1135997 := bbase (se 3 (by rfl) ⟨212999, by rfl⟩ : syracuseStep 1135997 = 425999) (by norm_num)
theorem B1136021 : Blo 754331 1136021 := bbase (se 6 (by rfl) ⟨26625, by rfl⟩ : syracuseStep 1136021 = 53251) (by norm_num)
theorem B1136045 : Blo 754331 1136045 := bbase (se 3 (by rfl) ⟨213008, by rfl⟩ : syracuseStep 1136045 = 426017) (by norm_num)
theorem B1136069 : Blo 754331 1136069 := bbase (se 4 (by rfl) ⟨106506, by rfl⟩ : syracuseStep 1136069 = 213013) (by norm_num)
theorem B2807237 : Blo 754331 2807237 := bbase (se 4 (by rfl) ⟨263178, by rfl⟩ : syracuseStep 2807237 = 526357) (by norm_num)
theorem B1136093 : Blo 754331 1136093 := bbase (se 3 (by rfl) ⟨213017, by rfl⟩ : syracuseStep 1136093 = 426035) (by norm_num)
theorem B1136117 : Blo 754331 1136117 := bbase (se 5 (by rfl) ⟨53255, by rfl⟩ : syracuseStep 1136117 = 106511) (by norm_num)
theorem B1136141 : Blo 754331 1136141 := bbase (se 3 (by rfl) ⟨213026, by rfl⟩ : syracuseStep 1136141 = 426053) (by norm_num)
theorem B2872853 : Blo 754331 2872853 := bbase (se 6 (by rfl) ⟨67332, by rfl⟩ : syracuseStep 2872853 = 134665) (by norm_num)
theorem B1136165 : Blo 754331 1136165 := bbase (se 4 (by rfl) ⟨106515, by rfl⟩ : syracuseStep 1136165 = 213031) (by norm_num)
theorem B1136189 : Blo 754331 1136189 := bbase (se 3 (by rfl) ⟨213035, by rfl⟩ : syracuseStep 1136189 = 426071) (by norm_num)
theorem B1136213 : Blo 754331 1136213 := bbase (se 8 (by rfl) ⟨6657, by rfl⟩ : syracuseStep 1136213 = 13315) (by norm_num)
theorem B808537 : Blo 754331 808537 := bbase (se 2 (by rfl) ⟨303201, by rfl⟩ : syracuseStep 808537 = 606403) (by norm_num)
theorem B1136237 : Blo 754331 1136237 := bbase (se 3 (by rfl) ⟨213044, by rfl⟩ : syracuseStep 1136237 = 426089) (by norm_num)
theorem B1136261 : Blo 754331 1136261 := bbase (se 4 (by rfl) ⟨106524, by rfl⟩ : syracuseStep 1136261 = 213049) (by norm_num)
theorem B1136285 : Blo 754331 1136285 := bbase (se 3 (by rfl) ⟨213053, by rfl⟩ : syracuseStep 1136285 = 426107) (by norm_num)
theorem B1136309 : Blo 754331 1136309 := bbase (se 5 (by rfl) ⟨53264, by rfl⟩ : syracuseStep 1136309 = 106529) (by norm_num)
theorem B1136333 : Blo 754331 1136333 := bbase (se 3 (by rfl) ⟨213062, by rfl⟩ : syracuseStep 1136333 = 426125) (by norm_num)
theorem B3495653 : Blo 754331 3495653 := bbase (se 4 (by rfl) ⟨327717, by rfl⟩ : syracuseStep 3495653 = 655435) (by norm_num)
theorem B1136357 : Blo 754331 1136357 := bbase (se 4 (by rfl) ⟨106533, by rfl⟩ : syracuseStep 1136357 = 213067) (by norm_num)
theorem B1136381 : Blo 754331 1136381 := bbase (se 3 (by rfl) ⟨213071, by rfl⟩ : syracuseStep 1136381 = 426143) (by norm_num)
theorem B1136405 : Blo 754331 1136405 := bbase (se 6 (by rfl) ⟨26634, by rfl⟩ : syracuseStep 1136405 = 53269) (by norm_num)
theorem B907033 : Blo 754331 907033 := bbase (se 2 (by rfl) ⟨340137, by rfl⟩ : syracuseStep 907033 = 680275) (by norm_num)
theorem B1136429 : Blo 754331 1136429 := bbase (se 3 (by rfl) ⟨213080, by rfl⟩ : syracuseStep 1136429 = 426161) (by norm_num)
theorem B2873141 : Blo 754331 2873141 := bbase (se 5 (by rfl) ⟨134678, by rfl⟩ : syracuseStep 2873141 = 269357) (by norm_num)
theorem B1136453 : Blo 754331 1136453 := bbase (se 4 (by rfl) ⟨106542, by rfl⟩ : syracuseStep 1136453 = 213085) (by norm_num)
theorem B907081 : Blo 754331 907081 := bbase (se 2 (by rfl) ⟨340155, by rfl⟩ : syracuseStep 907081 = 680311) (by norm_num)
theorem B1136477 : Blo 754331 1136477 := bbase (se 3 (by rfl) ⟨213089, by rfl⟩ : syracuseStep 1136477 = 426179) (by norm_num)
theorem B1136501 : Blo 754331 1136501 := bbase (se 5 (by rfl) ⟨53273, by rfl⟩ : syracuseStep 1136501 = 106547) (by norm_num)
theorem B1136525 : Blo 754331 1136525 := bbase (se 3 (by rfl) ⟨213098, by rfl⟩ : syracuseStep 1136525 = 426197) (by norm_num)
theorem B1136549 : Blo 754331 1136549 := bbase (se 4 (by rfl) ⟨106551, by rfl⟩ : syracuseStep 1136549 = 213103) (by norm_num)
theorem B1365941 : Blo 754331 1365941 := bbase (se 5 (by rfl) ⟨64028, by rfl⟩ : syracuseStep 1365941 = 128057) (by norm_num)
theorem B1136573 : Blo 754331 1136573 := bbase (se 3 (by rfl) ⟨213107, by rfl⟩ : syracuseStep 1136573 = 426215) (by norm_num)
theorem B808913 : Blo 754331 808913 := bbase (se 2 (by rfl) ⟨303342, by rfl⟩ : syracuseStep 808913 = 606685) (by norm_num)
theorem B1136597 : Blo 754331 1136597 := bbase (se 7 (by rfl) ⟨13319, by rfl⟩ : syracuseStep 1136597 = 26639) (by norm_num)
theorem B1136621 : Blo 754331 1136621 := bbase (se 3 (by rfl) ⟨213116, by rfl⟩ : syracuseStep 1136621 = 426233) (by norm_num)
theorem B2152453 : Blo 754331 2152453 := bbase (se 4 (by rfl) ⟨201792, by rfl⟩ : syracuseStep 2152453 = 403585) (by norm_num)
theorem B1136645 : Blo 754331 1136645 := bbase (se 4 (by rfl) ⟨106560, by rfl⟩ : syracuseStep 1136645 = 213121) (by norm_num)
theorem B1366021 : Blo 754331 1366021 := bbase (se 4 (by rfl) ⟨128064, by rfl⟩ : syracuseStep 1366021 = 256129) (by norm_num)
theorem B808985 : Blo 754331 808985 := bbase (se 2 (by rfl) ⟨303369, by rfl⟩ : syracuseStep 808985 = 606739) (by norm_num)
theorem B1136669 : Blo 754331 1136669 := bbase (se 3 (by rfl) ⟨213125, by rfl⟩ : syracuseStep 1136669 = 426251) (by norm_num)
theorem B1136693 : Blo 754331 1136693 := bbase (se 5 (by rfl) ⟨53282, by rfl⟩ : syracuseStep 1136693 = 106565) (by norm_num)
theorem B3823685 : Blo 754331 3823685 := bbase (se 4 (by rfl) ⟨358470, by rfl⟩ : syracuseStep 3823685 = 716941) (by norm_num)
theorem B1136717 : Blo 754331 1136717 := bbase (se 3 (by rfl) ⟨213134, by rfl⟩ : syracuseStep 1136717 = 426269) (by norm_num)
theorem B1136741 : Blo 754331 1136741 := bbase (se 4 (by rfl) ⟨106569, by rfl⟩ : syracuseStep 1136741 = 213139) (by norm_num)
theorem B1136765 : Blo 754331 1136765 := bbase (se 3 (by rfl) ⟨213143, by rfl⟩ : syracuseStep 1136765 = 426287) (by norm_num)
theorem B1136789 : Blo 754331 1136789 := bbase (se 6 (by rfl) ⟨26643, by rfl⟩ : syracuseStep 1136789 = 53287) (by norm_num)
theorem B1136813 : Blo 754331 1136813 := bbase (se 3 (by rfl) ⟨213152, by rfl⟩ : syracuseStep 1136813 = 426305) (by norm_num)
theorem B1136837 : Blo 754331 1136837 := bbase (se 4 (by rfl) ⟨106578, by rfl⟩ : syracuseStep 1136837 = 213157) (by norm_num)
theorem B809173 : Blo 754331 809173 := bbase (se 7 (by rfl) ⟨9482, by rfl⟩ : syracuseStep 809173 = 18965) (by norm_num)
theorem B1136861 : Blo 754331 1136861 := bbase (se 3 (by rfl) ⟨213161, by rfl⟩ : syracuseStep 1136861 = 426323) (by norm_num)
theorem B1136885 : Blo 754331 1136885 := bbase (se 5 (by rfl) ⟨53291, by rfl⟩ : syracuseStep 1136885 = 106583) (by norm_num)
theorem B1136909 : Blo 754331 1136909 := bbase (se 3 (by rfl) ⟨213170, by rfl⟩ : syracuseStep 1136909 = 426341) (by norm_num)
theorem B1136933 : Blo 754331 1136933 := bbase (se 4 (by rfl) ⟨106587, by rfl⟩ : syracuseStep 1136933 = 213175) (by norm_num)
theorem B1136957 : Blo 754331 1136957 := bbase (se 3 (by rfl) ⟨213179, by rfl⟩ : syracuseStep 1136957 = 426359) (by norm_num)
theorem B1530181 : Blo 754331 1530181 := bbase (se 4 (by rfl) ⟨143454, by rfl⟩ : syracuseStep 1530181 = 286909) (by norm_num)
theorem B1136981 : Blo 754331 1136981 := bbase (se 10 (by rfl) ⟨1665, by rfl⟩ : syracuseStep 1136981 = 3331) (by norm_num)
theorem B1137005 : Blo 754331 1137005 := bbase (se 3 (by rfl) ⟨213188, by rfl⟩ : syracuseStep 1137005 = 426377) (by norm_num)
theorem B1137029 : Blo 754331 1137029 := bbase (se 4 (by rfl) ⟨106596, by rfl⟩ : syracuseStep 1137029 = 213193) (by norm_num)
theorem B809357 : Blo 754331 809357 := bbase (se 3 (by rfl) ⟨151754, by rfl⟩ : syracuseStep 809357 = 303509) (by norm_num)
theorem B1137053 : Blo 754331 1137053 := bbase (se 3 (by rfl) ⟨213197, by rfl⟩ : syracuseStep 1137053 = 426395) (by norm_num)
theorem B1137077 : Blo 754331 1137077 := bbase (se 5 (by rfl) ⟨53300, by rfl⟩ : syracuseStep 1137077 = 106601) (by norm_num)
theorem B1137101 : Blo 754331 1137101 := bbase (se 3 (by rfl) ⟨213206, by rfl⟩ : syracuseStep 1137101 = 426413) (by norm_num)
theorem B1137125 : Blo 754331 1137125 := bbase (se 4 (by rfl) ⟨106605, by rfl⟩ : syracuseStep 1137125 = 213211) (by norm_num)
theorem B1137149 : Blo 754331 1137149 := bbase (se 3 (by rfl) ⟨213215, by rfl⟩ : syracuseStep 1137149 = 426431) (by norm_num)
theorem B1137173 : Blo 754331 1137173 := bbase (se 6 (by rfl) ⟨26652, by rfl⟩ : syracuseStep 1137173 = 53305) (by norm_num)
theorem B1137197 : Blo 754331 1137197 := bbase (se 3 (by rfl) ⟨213224, by rfl⟩ : syracuseStep 1137197 = 426449) (by norm_num)
theorem B1137221 : Blo 754331 1137221 := bbase (se 4 (by rfl) ⟨106614, by rfl⟩ : syracuseStep 1137221 = 213229) (by norm_num)
theorem B2546261 : Blo 754331 2546261 := bbase (se 8 (by rfl) ⟨14919, by rfl⟩ : syracuseStep 2546261 = 29839) (by norm_num)
theorem B1137245 : Blo 754331 1137245 := bbase (se 3 (by rfl) ⟨213233, by rfl⟩ : syracuseStep 1137245 = 426467) (by norm_num)
theorem B1432181 : Blo 754331 1432181 := bbase (se 5 (by rfl) ⟨67133, by rfl⟩ : syracuseStep 1432181 = 134267) (by norm_num)
theorem B1137269 : Blo 754331 1137269 := bbase (se 5 (by rfl) ⟨53309, by rfl⟩ : syracuseStep 1137269 = 106619) (by norm_num)
theorem B3234437 : Blo 754331 3234437 := bbase (se 4 (by rfl) ⟨303228, by rfl⟩ : syracuseStep 3234437 = 606457) (by norm_num)
theorem B1137293 : Blo 754331 1137293 := bbase (se 3 (by rfl) ⟨213242, by rfl⟩ : syracuseStep 1137293 = 426485) (by norm_num)
theorem B1137317 : Blo 754331 1137317 := bbase (se 4 (by rfl) ⟨106623, by rfl⟩ : syracuseStep 1137317 = 213247) (by norm_num)
theorem B1727165 : Blo 754331 1727165 := bbase (se 3 (by rfl) ⟨323843, by rfl⟩ : syracuseStep 1727165 = 647687) (by norm_num)
theorem B1137341 : Blo 754331 1137341 := bbase (se 3 (by rfl) ⟨213251, by rfl⟩ : syracuseStep 1137341 = 426503) (by norm_num)
theorem B1137365 : Blo 754331 1137365 := bbase (se 7 (by rfl) ⟨13328, by rfl⟩ : syracuseStep 1137365 = 26657) (by norm_num)
theorem B1137389 : Blo 754331 1137389 := bbase (se 3 (by rfl) ⟨213260, by rfl⟩ : syracuseStep 1137389 = 426521) (by norm_num)
theorem B1137413 : Blo 754331 1137413 := bbase (se 4 (by rfl) ⟨106632, by rfl⟩ : syracuseStep 1137413 = 213265) (by norm_num)
theorem B1432333 : Blo 754331 1432333 := bbase (se 3 (by rfl) ⟨268562, by rfl⟩ : syracuseStep 1432333 = 537125) (by norm_num)
theorem B1137437 : Blo 754331 1137437 := bbase (se 3 (by rfl) ⟨213269, by rfl⟩ : syracuseStep 1137437 = 426539) (by norm_num)
theorem B1137461 : Blo 754331 1137461 := bbase (se 5 (by rfl) ⟨53318, by rfl⟩ : syracuseStep 1137461 = 106637) (by norm_num)
theorem B1137485 : Blo 754331 1137485 := bbase (se 3 (by rfl) ⟨213278, by rfl⟩ : syracuseStep 1137485 = 426557) (by norm_num)
theorem B908129 : Blo 754331 908129 := bbase (se 2 (by rfl) ⟨340548, by rfl⟩ : syracuseStep 908129 = 681097) (by norm_num)
theorem B2874325 : Blo 754331 2874325 := bbase (se 7 (by rfl) ⟨33683, by rfl⟩ : syracuseStep 2874325 = 67367) (by norm_num)
theorem B2546693 : Blo 754331 2546693 := bbase (se 4 (by rfl) ⟨238752, by rfl⟩ : syracuseStep 2546693 = 477505) (by norm_num)
theorem B1432637 : Blo 754331 1432637 := bbase (se 3 (by rfl) ⟨268619, by rfl⟩ : syracuseStep 1432637 = 537239) (by norm_num)
theorem B2153557 : Blo 754331 2153557 := bbase (se 8 (by rfl) ⟨12618, by rfl⟩ : syracuseStep 2153557 = 25237) (by norm_num)
theorem B908437 : Blo 754331 908437 := bbase (se 6 (by rfl) ⟨21291, by rfl⟩ : syracuseStep 908437 = 42583) (by norm_num)
theorem B875713 : Blo 754331 875713 := bbase (se 2 (by rfl) ⟨328392, by rfl⟩ : syracuseStep 875713 = 656785) (by norm_num)
theorem B5823701 : Blo 754331 5823701 := bbase (se 7 (by rfl) ⟨68246, by rfl⟩ : syracuseStep 5823701 = 136493) (by norm_num)
theorem B2874629 : Blo 754331 2874629 := bbase (se 4 (by rfl) ⟨269496, by rfl⟩ : syracuseStep 2874629 = 538993) (by norm_num)
theorem B908605 : Blo 754331 908605 := bbase (se 3 (by rfl) ⟨170363, by rfl⟩ : syracuseStep 908605 = 340727) (by norm_num)
theorem B3824981 : Blo 754331 3824981 := bbase (se 11 (by rfl) ⟨2801, by rfl⟩ : syracuseStep 3824981 = 5603) (by norm_num)
theorem B14736725 : Blo 754331 14736725 := bbase (se 11 (by rfl) ⟨10793, by rfl⟩ : syracuseStep 14736725 = 21587) (by norm_num)
theorem B2547125 : Blo 754331 2547125 := bbase (se 5 (by rfl) ⟨119396, by rfl⟩ : syracuseStep 2547125 = 238793) (by norm_num)
theorem B1531325 : Blo 754331 1531325 := bbase (se 3 (by rfl) ⟨287123, by rfl⟩ : syracuseStep 1531325 = 574247) (by norm_num)
theorem B908801 : Blo 754331 908801 := bbase (se 2 (by rfl) ⟨340800, by rfl⟩ : syracuseStep 908801 = 681601) (by norm_num)
theorem B1433389 : Blo 754331 1433389 := bbase (se 3 (by rfl) ⟨268760, by rfl⟩ : syracuseStep 1433389 = 537521) (by norm_num)
theorem B7757621 : Blo 754331 7757621 := bbase (se 5 (by rfl) ⟨363638, by rfl⟩ : syracuseStep 7757621 = 727277) (by norm_num)
theorem B4972373 : Blo 754331 4972373 := bbase (se 9 (by rfl) ⟨14567, by rfl⟩ : syracuseStep 4972373 = 29135) (by norm_num)
theorem B2547557 : Blo 754331 2547557 := bbase (se 4 (by rfl) ⟨238833, by rfl⟩ : syracuseStep 2547557 = 477667) (by norm_num)
theorem B3628901 : Blo 754331 3628901 := bbase (se 4 (by rfl) ⟨340209, by rfl⟩ : syracuseStep 3628901 = 680419) (by norm_num)
theorem B1433533 : Blo 754331 1433533 := bbase (se 3 (by rfl) ⟨268787, by rfl⟩ : syracuseStep 1433533 = 537575) (by norm_num)
theorem B1433693 : Blo 754331 1433693 := bbase (se 3 (by rfl) ⟨268817, by rfl⟩ : syracuseStep 1433693 = 537635) (by norm_num)
theorem B1433837 : Blo 754331 1433837 := bbase (se 3 (by rfl) ⟨268844, by rfl⟩ : syracuseStep 1433837 = 537689) (by norm_num)
theorem B2547989 : Blo 754331 2547989 := bbase (se 6 (by rfl) ⟨59718, by rfl⟩ : syracuseStep 2547989 = 119437) (by norm_num)
theorem B3236213 : Blo 754331 3236213 := bbase (se 5 (by rfl) ⟨151697, by rfl⟩ : syracuseStep 3236213 = 303395) (by norm_num)
theorem B2417141 : Blo 754331 2417141 := bbase (se 5 (by rfl) ⟨113303, by rfl⟩ : syracuseStep 2417141 = 226607) (by norm_num)
theorem B1434125 : Blo 754331 1434125 := bbase (se 3 (by rfl) ⟨268898, by rfl⟩ : syracuseStep 1434125 = 537797) (by norm_num)
theorem B2155061 : Blo 754331 2155061 := bbase (se 5 (by rfl) ⟨101018, by rfl⟩ : syracuseStep 2155061 = 202037) (by norm_num)
theorem B3826277 : Blo 754331 3826277 := bbase (se 4 (by rfl) ⟨358713, by rfl⟩ : syracuseStep 3826277 = 717427) (by norm_num)
theorem B1434277 : Blo 754331 1434277 := bbase (se 4 (by rfl) ⟨134463, by rfl⟩ : syracuseStep 1434277 = 268927) (by norm_num)
theorem B1401517 : Blo 754331 1401517 := bbase (se 3 (by rfl) ⟨262784, by rfl⟩ : syracuseStep 1401517 = 525569) (by norm_num)
theorem B2548421 : Blo 754331 2548421 := bbase (se 4 (by rfl) ⟨238914, by rfl⟩ : syracuseStep 2548421 = 477829) (by norm_num)
theorem B1434581 : Blo 754331 1434581 := bbase (se 7 (by rfl) ⟨16811, by rfl⟩ : syracuseStep 1434581 = 33623) (by norm_num)
theorem B910373 : Blo 754331 910373 := bbase (se 4 (by rfl) ⟨85347, by rfl⟩ : syracuseStep 910373 = 170695) (by norm_num)
theorem B910397 : Blo 754331 910397 := bbase (se 3 (by rfl) ⟨170699, by rfl⟩ : syracuseStep 910397 = 341399) (by norm_num)
theorem B2548853 : Blo 754331 2548853 := bbase (se 5 (by rfl) ⟨119477, by rfl⟩ : syracuseStep 2548853 = 238955) (by norm_num)
theorem B1074341 : Blo 754331 1074341 := bbase (se 4 (by rfl) ⟨100719, by rfl⟩ : syracuseStep 1074341 = 201439) (by norm_num)
theorem B6120629 : Blo 754331 6120629 := bbase (se 5 (by rfl) ⟨286904, by rfl⟩ : syracuseStep 6120629 = 573809) (by norm_num)
theorem B1074421 : Blo 754331 1074421 := bbase (se 5 (by rfl) ⟨50363, by rfl⟩ : syracuseStep 1074421 = 100727) (by norm_num)
theorem B2876741 : Blo 754331 2876741 := bbase (se 4 (by rfl) ⟨269694, by rfl⟩ : syracuseStep 2876741 = 539389) (by norm_num)
theorem B3237205 : Blo 754331 3237205 := bbase (se 12 (by rfl) ⟨1185, by rfl⟩ : syracuseStep 3237205 = 2371) (by norm_num)
theorem B1074541 : Blo 754331 1074541 := bbase (se 3 (by rfl) ⟨201476, by rfl⟩ : syracuseStep 1074541 = 402953) (by norm_num)
theorem B910705 : Blo 754331 910705 := bbase (se 2 (by rfl) ⟨341514, by rfl⟩ : syracuseStep 910705 = 683029) (by norm_num)
theorem B1074637 : Blo 754331 1074637 := bbase (se 3 (by rfl) ⟨201494, by rfl⟩ : syracuseStep 1074637 = 402989) (by norm_num)
theorem B1697309 : Blo 754331 1697309 := bbase (se 3 (by rfl) ⟨318245, by rfl⟩ : syracuseStep 1697309 = 636491) (by norm_num)
theorem B910877 : Blo 754331 910877 := bbase (se 3 (by rfl) ⟨170789, by rfl⟩ : syracuseStep 910877 = 341579) (by norm_num)
theorem B2549285 : Blo 754331 2549285 := bbase (se 4 (by rfl) ⟨238995, by rfl⟩ : syracuseStep 2549285 = 477991) (by norm_num)
theorem B1697381 : Blo 754331 1697381 := bbase (se 4 (by rfl) ⟨159129, by rfl⟩ : syracuseStep 1697381 = 318259) (by norm_num)
theorem B2877029 : Blo 754331 2877029 := bbase (se 4 (by rfl) ⟨269721, by rfl⟩ : syracuseStep 2877029 = 539443) (by norm_num)
theorem B910993 : Blo 754331 910993 := bbase (se 2 (by rfl) ⟨341622, by rfl⟩ : syracuseStep 910993 = 683245) (by norm_num)
theorem B1697453 : Blo 754331 1697453 := bbase (se 3 (by rfl) ⟨318272, by rfl⟩ : syracuseStep 1697453 = 636545) (by norm_num)
theorem B1435333 : Blo 754331 1435333 := bbase (se 4 (by rfl) ⟨134562, by rfl⟩ : syracuseStep 1435333 = 269125) (by norm_num)
theorem B1697525 : Blo 754331 1697525 := bbase (se 5 (by rfl) ⟨79571, by rfl⟩ : syracuseStep 1697525 = 159143) (by norm_num)
theorem B1697597 : Blo 754331 1697597 := bbase (se 3 (by rfl) ⟨318299, by rfl⟩ : syracuseStep 1697597 = 636599) (by norm_num)
theorem B1435477 : Blo 754331 1435477 := bbase (se 9 (by rfl) ⟨4205, by rfl⟩ : syracuseStep 1435477 = 8411) (by norm_num)
theorem B3827573 : Blo 754331 3827573 := bbase (se 5 (by rfl) ⟨179417, by rfl⟩ : syracuseStep 3827573 = 358835) (by norm_num)
theorem B1697669 : Blo 754331 1697669 := bbase (se 4 (by rfl) ⟨159156, by rfl⟩ : syracuseStep 1697669 = 318313) (by norm_num)
theorem B1075133 : Blo 754331 1075133 := bbase (se 3 (by rfl) ⟨201587, by rfl⟩ : syracuseStep 1075133 = 403175) (by norm_num)
theorem B1697741 : Blo 754331 1697741 := bbase (se 3 (by rfl) ⟨318326, by rfl⟩ : syracuseStep 1697741 = 636653) (by norm_num)
theorem B2549717 : Blo 754331 2549717 := bbase (se 7 (by rfl) ⟨29879, by rfl⟩ : syracuseStep 2549717 = 59759) (by norm_num)
theorem B1435637 : Blo 754331 1435637 := bbase (se 5 (by rfl) ⟨67295, by rfl⟩ : syracuseStep 1435637 = 134591) (by norm_num)
theorem B1697813 : Blo 754331 1697813 := bbase (se 6 (by rfl) ⟨39792, by rfl⟩ : syracuseStep 1697813 = 79585) (by norm_num)
theorem B1697885 : Blo 754331 1697885 := bbase (se 3 (by rfl) ⟨318353, by rfl⟩ : syracuseStep 1697885 = 636707) (by norm_num)
theorem B2156645 : Blo 754331 2156645 := bbase (se 4 (by rfl) ⟨202185, by rfl⟩ : syracuseStep 2156645 = 404371) (by norm_num)
theorem B4843637 : Blo 754331 4843637 := bbase (se 5 (by rfl) ⟨227045, by rfl⟩ : syracuseStep 4843637 = 454091) (by norm_num)
theorem B1435781 : Blo 754331 1435781 := bbase (se 4 (by rfl) ⟨134604, by rfl⟩ : syracuseStep 1435781 = 269209) (by norm_num)
theorem B1697957 : Blo 754331 1697957 := bbase (se 4 (by rfl) ⟨159183, by rfl⟩ : syracuseStep 1697957 = 318367) (by norm_num)
theorem B1698029 : Blo 754331 1698029 := bbase (se 3 (by rfl) ⟨318380, by rfl⟩ : syracuseStep 1698029 = 636761) (by norm_num)
theorem B1698101 : Blo 754331 1698101 := bbase (se 5 (by rfl) ⟨79598, by rfl⟩ : syracuseStep 1698101 = 159197) (by norm_num)
theorem B1698173 : Blo 754331 1698173 := bbase (se 3 (by rfl) ⟨318407, by rfl⟩ : syracuseStep 1698173 = 636815) (by norm_num)
theorem B2550149 : Blo 754331 2550149 := bbase (se 4 (by rfl) ⟨239076, by rfl⟩ : syracuseStep 2550149 = 478153) (by norm_num)
theorem B1534349 : Blo 754331 1534349 := bbase (se 3 (by rfl) ⟨287690, by rfl⟩ : syracuseStep 1534349 = 575381) (by norm_num)
theorem B1436069 : Blo 754331 1436069 := bbase (se 4 (by rfl) ⟨134631, by rfl⟩ : syracuseStep 1436069 = 269263) (by norm_num)
theorem B1698245 : Blo 754331 1698245 := bbase (se 4 (by rfl) ⟨159210, by rfl⟩ : syracuseStep 1698245 = 318421) (by norm_num)
theorem B1075685 : Blo 754331 1075685 := bbase (se 4 (by rfl) ⟨100845, by rfl⟩ : syracuseStep 1075685 = 201691) (by norm_num)
theorem B1698317 : Blo 754331 1698317 := bbase (se 3 (by rfl) ⟨318434, by rfl⟩ : syracuseStep 1698317 = 636869) (by norm_num)
theorem B1436221 : Blo 754331 1436221 := bbase (se 3 (by rfl) ⟨269291, by rfl⟩ : syracuseStep 1436221 = 538583) (by norm_num)
theorem B1698389 : Blo 754331 1698389 := bbase (se 8 (by rfl) ⟨9951, by rfl⟩ : syracuseStep 1698389 = 19903) (by norm_num)
theorem B1698461 : Blo 754331 1698461 := bbase (se 3 (by rfl) ⟨318461, by rfl⟩ : syracuseStep 1698461 = 636923) (by norm_num)
theorem B1698533 : Blo 754331 1698533 := bbase (se 4 (by rfl) ⟨159237, by rfl⟩ : syracuseStep 1698533 = 318475) (by norm_num)
theorem B2157317 : Blo 754331 2157317 := bbase (se 4 (by rfl) ⟨202248, by rfl⟩ : syracuseStep 2157317 = 404497) (by norm_num)
theorem B2878213 : Blo 754331 2878213 := bbase (se 4 (by rfl) ⟨269832, by rfl⟩ : syracuseStep 2878213 = 539665) (by norm_num)
theorem B1698605 : Blo 754331 1698605 := bbase (se 3 (by rfl) ⟨318488, by rfl⟩ : syracuseStep 1698605 = 636977) (by norm_num)
theorem B2550581 : Blo 754331 2550581 := bbase (se 5 (by rfl) ⟨119558, by rfl⟩ : syracuseStep 2550581 = 239117) (by norm_num)
theorem B1436525 : Blo 754331 1436525 := bbase (se 3 (by rfl) ⟨269348, by rfl⟩ : syracuseStep 1436525 = 538697) (by norm_num)
theorem B1698677 : Blo 754331 1698677 := bbase (se 5 (by rfl) ⟨79625, by rfl⟩ : syracuseStep 1698677 = 159251) (by norm_num)
theorem B3632053 : Blo 754331 3632053 := bbase (se 5 (by rfl) ⟨170252, by rfl⟩ : syracuseStep 3632053 = 340505) (by norm_num)
theorem B1698749 : Blo 754331 1698749 := bbase (se 3 (by rfl) ⟨318515, by rfl⟩ : syracuseStep 1698749 = 637031) (by norm_num)
theorem B1698821 : Blo 754331 1698821 := bbase (se 4 (by rfl) ⟨159264, by rfl⟩ : syracuseStep 1698821 = 318529) (by norm_num)
theorem B15494165 : Blo 754331 15494165 := bbase (se 6 (by rfl) ⟨363144, by rfl⟩ : syracuseStep 15494165 = 726289) (by norm_num)
theorem B2878517 : Blo 754331 2878517 := bbase (se 5 (by rfl) ⟨134930, by rfl⟩ : syracuseStep 2878517 = 269861) (by norm_num)
theorem B1698893 : Blo 754331 1698893 := bbase (se 3 (by rfl) ⟨318542, by rfl⟩ : syracuseStep 1698893 = 637085) (by norm_num)
theorem B945265 : Blo 754331 945265 := bbase (se 2 (by rfl) ⟨354474, by rfl⟩ : syracuseStep 945265 = 708949) (by norm_num)
theorem B3828869 : Blo 754331 3828869 := bbase (se 4 (by rfl) ⟨358956, by rfl⟩ : syracuseStep 3828869 = 717913) (by norm_num)
theorem B1698965 : Blo 754331 1698965 := bbase (se 6 (by rfl) ⟨39819, by rfl⟩ : syracuseStep 1698965 = 79639) (by norm_num)
theorem B1272989 : Blo 754331 1272989 := bbase (se 3 (by rfl) ⟨238685, by rfl⟩ : syracuseStep 1272989 = 477371) (by norm_num)
theorem B2157749 : Blo 754331 2157749 := bbase (se 5 (by rfl) ⟨101144, by rfl⟩ : syracuseStep 2157749 = 202289) (by norm_num)
theorem B1076437 : Blo 754331 1076437 := bbase (se 7 (by rfl) ⟨12614, by rfl⟩ : syracuseStep 1076437 = 25229) (by norm_num)
theorem B1699037 : Blo 754331 1699037 := bbase (se 3 (by rfl) ⟨318569, by rfl⟩ : syracuseStep 1699037 = 637139) (by norm_num)
theorem B2551013 : Blo 754331 2551013 := bbase (se 4 (by rfl) ⟨239157, by rfl⟩ : syracuseStep 2551013 = 478315) (by norm_num)
theorem B1273117 : Blo 754331 1273117 := bbase (se 3 (by rfl) ⟨238709, by rfl⟩ : syracuseStep 1273117 = 477419) (by norm_num)
theorem B1699109 : Blo 754331 1699109 := bbase (se 4 (by rfl) ⟨159291, by rfl⟩ : syracuseStep 1699109 = 318583) (by norm_num)
theorem B1699181 : Blo 754331 1699181 := bbase (se 3 (by rfl) ⟨318596, by rfl⟩ : syracuseStep 1699181 = 637193) (by norm_num)
theorem B1273205 : Blo 754331 1273205 := bbase (se 5 (by rfl) ⟨59681, by rfl⟩ : syracuseStep 1273205 = 119363) (by norm_num)
theorem B1699253 : Blo 754331 1699253 := bbase (se 5 (by rfl) ⟨79652, by rfl⟩ : syracuseStep 1699253 = 159305) (by norm_num)
theorem B1273333 : Blo 754331 1273333 := bbase (se 5 (by rfl) ⟨59687, by rfl⟩ : syracuseStep 1273333 = 119375) (by norm_num)
theorem B1699325 : Blo 754331 1699325 := bbase (se 3 (by rfl) ⟨318623, by rfl⟩ : syracuseStep 1699325 = 637247) (by norm_num)
theorem B1699397 : Blo 754331 1699397 := bbase (se 4 (by rfl) ⟨159318, by rfl⟩ : syracuseStep 1699397 = 318637) (by norm_num)
theorem B1273421 : Blo 754331 1273421 := bbase (se 3 (by rfl) ⟨238766, by rfl⟩ : syracuseStep 1273421 = 477533) (by norm_num)
theorem B1437277 : Blo 754331 1437277 := bbase (se 3 (by rfl) ⟨269489, by rfl⟩ : syracuseStep 1437277 = 538979) (by norm_num)
theorem B1699469 : Blo 754331 1699469 := bbase (se 3 (by rfl) ⟨318650, by rfl⟩ : syracuseStep 1699469 = 637301) (by norm_num)
theorem B2551445 : Blo 754331 2551445 := bbase (se 6 (by rfl) ⟨59799, by rfl⟩ : syracuseStep 2551445 = 119599) (by norm_num)
theorem B1273549 : Blo 754331 1273549 := bbase (se 3 (by rfl) ⟨238790, by rfl⟩ : syracuseStep 1273549 = 477581) (by norm_num)
theorem B1699541 : Blo 754331 1699541 := bbase (se 7 (by rfl) ⟨19916, by rfl⟩ : syracuseStep 1699541 = 39833) (by norm_num)
theorem B1437421 : Blo 754331 1437421 := bbase (se 3 (by rfl) ⟨269516, by rfl⟩ : syracuseStep 1437421 = 539033) (by norm_num)
theorem B1699613 : Blo 754331 1699613 := bbase (se 3 (by rfl) ⟨318677, by rfl⟩ : syracuseStep 1699613 = 637355) (by norm_num)
theorem B1273637 : Blo 754331 1273637 := bbase (se 4 (by rfl) ⟨119403, by rfl⟩ : syracuseStep 1273637 = 238807) (by norm_num)
theorem B2420549 : Blo 754331 2420549 := bbase (se 4 (by rfl) ⟨226926, by rfl⟩ : syracuseStep 2420549 = 453853) (by norm_num)
theorem B1699685 : Blo 754331 1699685 := bbase (se 4 (by rfl) ⟨159345, by rfl⟩ : syracuseStep 1699685 = 318691) (by norm_num)
theorem B1437581 : Blo 754331 1437581 := bbase (se 3 (by rfl) ⟨269546, by rfl⟩ : syracuseStep 1437581 = 539093) (by norm_num)
theorem B1273765 : Blo 754331 1273765 := bbase (se 4 (by rfl) ⟨119415, by rfl⟩ : syracuseStep 1273765 = 238831) (by norm_num)
theorem B2158501 : Blo 754331 2158501 := bbase (se 4 (by rfl) ⟨202359, by rfl⟩ : syracuseStep 2158501 = 404719) (by norm_num)
theorem B1699757 : Blo 754331 1699757 := bbase (se 3 (by rfl) ⟨318704, by rfl⟩ : syracuseStep 1699757 = 637409) (by norm_num)
theorem B1077229 : Blo 754331 1077229 := bbase (se 3 (by rfl) ⟨201980, by rfl⟩ : syracuseStep 1077229 = 403961) (by norm_num)
theorem B1699829 : Blo 754331 1699829 := bbase (se 5 (by rfl) ⟨79679, by rfl⟩ : syracuseStep 1699829 = 159359) (by norm_num)
theorem B1273853 : Blo 754331 1273853 := bbase (se 3 (by rfl) ⟨238847, by rfl⟩ : syracuseStep 1273853 = 477695) (by norm_num)
theorem B1437725 : Blo 754331 1437725 := bbase (se 3 (by rfl) ⟨269573, by rfl⟩ : syracuseStep 1437725 = 539147) (by norm_num)
theorem B1634365 : Blo 754331 1634365 := bbase (se 3 (by rfl) ⟨306443, by rfl⟩ : syracuseStep 1634365 = 612887) (by norm_num)
theorem B1699901 : Blo 754331 1699901 := bbase (se 3 (by rfl) ⟨318731, by rfl⟩ : syracuseStep 1699901 = 637463) (by norm_num)
theorem B2551877 : Blo 754331 2551877 := bbase (se 4 (by rfl) ⟨239238, by rfl⟩ : syracuseStep 2551877 = 478477) (by norm_num)
theorem B1273981 : Blo 754331 1273981 := bbase (se 3 (by rfl) ⟨238871, by rfl⟩ : syracuseStep 1273981 = 477743) (by norm_num)
theorem B1699973 : Blo 754331 1699973 := bbase (se 4 (by rfl) ⟨159372, by rfl⟩ : syracuseStep 1699973 = 318745) (by norm_num)
theorem B1700045 : Blo 754331 1700045 := bbase (se 3 (by rfl) ⟨318758, by rfl⟩ : syracuseStep 1700045 = 637517) (by norm_num)
theorem B1274069 : Blo 754331 1274069 := bbase (se 7 (by rfl) ⟨14930, by rfl⟩ : syracuseStep 1274069 = 29861) (by norm_num)
theorem B1208557 : Blo 754331 1208557 := bbase (se 3 (by rfl) ⟨226604, by rfl⟩ : syracuseStep 1208557 = 453209) (by norm_num)
theorem B1700117 : Blo 754331 1700117 := bbase (se 6 (by rfl) ⟨39846, by rfl⟩ : syracuseStep 1700117 = 79693) (by norm_num)
theorem B1077565 : Blo 754331 1077565 := bbase (se 3 (by rfl) ⟨202043, by rfl⟩ : syracuseStep 1077565 = 404087) (by norm_num)
theorem B1438013 : Blo 754331 1438013 := bbase (se 3 (by rfl) ⟨269627, by rfl⟩ : syracuseStep 1438013 = 539255) (by norm_num)
theorem B1274197 : Blo 754331 1274197 := bbase (se 10 (by rfl) ⟨1866, by rfl⟩ : syracuseStep 1274197 = 3733) (by norm_num)
theorem B1700189 : Blo 754331 1700189 := bbase (se 3 (by rfl) ⟨318785, by rfl⟩ : syracuseStep 1700189 = 637571) (by norm_num)
theorem B3830165 : Blo 754331 3830165 := bbase (se 6 (by rfl) ⟨89769, by rfl⟩ : syracuseStep 3830165 = 179539) (by norm_num)
theorem B1700261 : Blo 754331 1700261 := bbase (se 4 (by rfl) ⟨159399, by rfl⟩ : syracuseStep 1700261 = 318799) (by norm_num)
theorem B1274285 : Blo 754331 1274285 := bbase (se 3 (by rfl) ⟨238928, by rfl⟩ : syracuseStep 1274285 = 477857) (by norm_num)
theorem B2585029 : Blo 754331 2585029 := bbase (se 4 (by rfl) ⟨242346, by rfl⟩ : syracuseStep 2585029 = 484693) (by norm_num)
theorem B20672981 : Blo 754331 20672981 := bbase (se 7 (by rfl) ⟨242261, by rfl⟩ : syracuseStep 20672981 = 484523) (by norm_num)
theorem B4092373 : Blo 754331 4092373 := bbase (se 7 (by rfl) ⟨47957, by rfl⟩ : syracuseStep 4092373 = 95915) (by norm_num)
theorem B1438165 : Blo 754331 1438165 := bbase (se 7 (by rfl) ⟨16853, by rfl⟩ : syracuseStep 1438165 = 33707) (by norm_num)
theorem B1700333 : Blo 754331 1700333 := bbase (se 3 (by rfl) ⟨318812, by rfl⟩ : syracuseStep 1700333 = 637625) (by norm_num)
theorem B2552309 : Blo 754331 2552309 := bbase (se 5 (by rfl) ⟨119639, by rfl⟩ : syracuseStep 2552309 = 239279) (by norm_num)
theorem B1077781 : Blo 754331 1077781 := bbase (se 6 (by rfl) ⟨25260, by rfl⟩ : syracuseStep 1077781 = 50521) (by norm_num)
theorem B1274413 : Blo 754331 1274413 := bbase (se 3 (by rfl) ⟨238952, by rfl⟩ : syracuseStep 1274413 = 477905) (by norm_num)
theorem B1700405 : Blo 754331 1700405 := bbase (se 5 (by rfl) ⟨79706, by rfl⟩ : syracuseStep 1700405 = 159413) (by norm_num)
theorem B1700477 : Blo 754331 1700477 := bbase (se 3 (by rfl) ⟨318839, by rfl⟩ : syracuseStep 1700477 = 637679) (by norm_num)
theorem B1274501 : Blo 754331 1274501 := bbase (se 4 (by rfl) ⟨119484, by rfl⟩ : syracuseStep 1274501 = 238969) (by norm_num)
theorem B1536653 : Blo 754331 1536653 := bbase (se 3 (by rfl) ⟨288122, by rfl⟩ : syracuseStep 1536653 = 576245) (by norm_num)
theorem B1208981 : Blo 754331 1208981 := bbase (se 6 (by rfl) ⟨28335, by rfl⟩ : syracuseStep 1208981 = 56671) (by norm_num)
theorem B1700549 : Blo 754331 1700549 := bbase (se 4 (by rfl) ⟨159426, by rfl⟩ : syracuseStep 1700549 = 318853) (by norm_num)
theorem B2585317 : Blo 754331 2585317 := bbase (se 4 (by rfl) ⟨242373, by rfl⟩ : syracuseStep 2585317 = 484747) (by norm_num)
theorem B848641 : Blo 754331 848641 := bbase (se 2 (by rfl) ⟨318240, by rfl⟩ : syracuseStep 848641 = 636481) (by norm_num)
theorem B1274629 : Blo 754331 1274629 := bbase (se 4 (by rfl) ⟨119496, by rfl⟩ : syracuseStep 1274629 = 238993) (by norm_num)
theorem B1438469 : Blo 754331 1438469 := bbase (se 4 (by rfl) ⟨134856, by rfl⟩ : syracuseStep 1438469 = 269713) (by norm_num)
theorem B1700621 : Blo 754331 1700621 := bbase (se 3 (by rfl) ⟨318866, by rfl⟩ : syracuseStep 1700621 = 637733) (by norm_num)
theorem B848677 : Blo 754331 848677 := bbase (se 4 (by rfl) ⟨79563, by rfl⟩ : syracuseStep 848677 = 159127) (by norm_num)
theorem B3371813 : Blo 754331 3371813 := bbase (se 4 (by rfl) ⟨316107, by rfl⟩ : syracuseStep 3371813 = 632215) (by norm_num)
theorem B848713 : Blo 754331 848713 := bbase (se 2 (by rfl) ⟨318267, by rfl⟩ : syracuseStep 848713 = 636535) (by norm_num)
theorem B1700693 : Blo 754331 1700693 := bbase (se 9 (by rfl) ⟨4982, by rfl⟩ : syracuseStep 1700693 = 9965) (by norm_num)
theorem B1274717 : Blo 754331 1274717 := bbase (se 3 (by rfl) ⟨239009, by rfl⟩ : syracuseStep 1274717 = 478019) (by norm_num)
theorem B848749 : Blo 754331 848749 := bbase (se 3 (by rfl) ⟨159140, by rfl⟩ : syracuseStep 848749 = 318281) (by norm_num)
theorem B1078157 : Blo 754331 1078157 := bbase (se 3 (by rfl) ⟨202154, by rfl⟩ : syracuseStep 1078157 = 404309) (by norm_num)
theorem B848785 : Blo 754331 848785 := bbase (se 2 (by rfl) ⟨318294, by rfl⟩ : syracuseStep 848785 = 636589) (by norm_num)
theorem B1700765 : Blo 754331 1700765 := bbase (se 3 (by rfl) ⟨318893, by rfl⟩ : syracuseStep 1700765 = 637787) (by norm_num)
theorem B2552741 : Blo 754331 2552741 := bbase (se 4 (by rfl) ⟨239319, by rfl⟩ : syracuseStep 2552741 = 478639) (by norm_num)
theorem B848821 : Blo 754331 848821 := bbase (se 5 (by rfl) ⟨39788, by rfl⟩ : syracuseStep 848821 = 79577) (by norm_num)
theorem B1209269 : Blo 754331 1209269 := bbase (se 5 (by rfl) ⟨56684, by rfl⟩ : syracuseStep 1209269 = 113369) (by norm_num)
theorem B24474581 : Blo 754331 24474581 := bbase (se 7 (by rfl) ⟨286811, by rfl⟩ : syracuseStep 24474581 = 573623) (by norm_num)
theorem B848857 : Blo 754331 848857 := bbase (se 2 (by rfl) ⟨318321, by rfl⟩ : syracuseStep 848857 = 636643) (by norm_num)
theorem B1274845 : Blo 754331 1274845 := bbase (se 3 (by rfl) ⟨239033, by rfl⟩ : syracuseStep 1274845 = 478067) (by norm_num)
theorem B1700837 : Blo 754331 1700837 := bbase (se 4 (by rfl) ⟨159453, by rfl⟩ : syracuseStep 1700837 = 318907) (by norm_num)
theorem B848893 : Blo 754331 848893 := bbase (se 3 (by rfl) ⟨159167, by rfl⟩ : syracuseStep 848893 = 318335) (by norm_num)
theorem B848929 : Blo 754331 848929 := bbase (se 2 (by rfl) ⟨318348, by rfl⟩ : syracuseStep 848929 = 636697) (by norm_num)
theorem B1700909 : Blo 754331 1700909 := bbase (se 3 (by rfl) ⟨318920, by rfl⟩ : syracuseStep 1700909 = 637841) (by norm_num)
theorem B1274933 : Blo 754331 1274933 := bbase (se 5 (by rfl) ⟨59762, by rfl⟩ : syracuseStep 1274933 = 119525) (by norm_num)
theorem B848965 : Blo 754331 848965 := bbase (se 4 (by rfl) ⟨79590, by rfl⟩ : syracuseStep 848965 = 159181) (by norm_num)
theorem B2421829 : Blo 754331 2421829 := bbase (se 4 (by rfl) ⟨227046, by rfl⟩ : syracuseStep 2421829 = 454093) (by norm_num)
theorem B849001 : Blo 754331 849001 := bbase (se 2 (by rfl) ⟨318375, by rfl⟩ : syracuseStep 849001 = 636751) (by norm_num)
theorem B1700981 : Blo 754331 1700981 := bbase (se 5 (by rfl) ⟨79733, by rfl⟩ : syracuseStep 1700981 = 159467) (by norm_num)
theorem B849037 : Blo 754331 849037 := bbase (se 3 (by rfl) ⟨159194, by rfl⟩ : syracuseStep 849037 = 318389) (by norm_num)
theorem B849073 : Blo 754331 849073 := bbase (se 2 (by rfl) ⟨318402, by rfl⟩ : syracuseStep 849073 = 636805) (by norm_num)
theorem B1275061 : Blo 754331 1275061 := bbase (se 5 (by rfl) ⟨59768, by rfl⟩ : syracuseStep 1275061 = 119537) (by norm_num)
theorem B1701053 : Blo 754331 1701053 := bbase (se 3 (by rfl) ⟨318947, by rfl⟩ : syracuseStep 1701053 = 637895) (by norm_num)
theorem B849109 : Blo 754331 849109 := bbase (se 7 (by rfl) ⟨9950, by rfl⟩ : syracuseStep 849109 = 19901) (by norm_num)
theorem B4846837 : Blo 754331 4846837 := bbase (se 5 (by rfl) ⟨227195, by rfl⟩ : syracuseStep 4846837 = 454391) (by norm_num)
theorem B849145 : Blo 754331 849145 := bbase (se 2 (by rfl) ⟨318429, by rfl⟩ : syracuseStep 849145 = 636859) (by norm_num)
theorem B1307909 : Blo 754331 1307909 := bbase (se 4 (by rfl) ⟨122616, by rfl⟩ : syracuseStep 1307909 = 245233) (by norm_num)
theorem B1701125 : Blo 754331 1701125 := bbase (se 4 (by rfl) ⟨159480, by rfl⟩ : syracuseStep 1701125 = 318961) (by norm_num)
theorem B1275149 : Blo 754331 1275149 := bbase (se 3 (by rfl) ⟨239090, by rfl⟩ : syracuseStep 1275149 = 478181) (by norm_num)
theorem B849181 : Blo 754331 849181 := bbase (se 3 (by rfl) ⟨159221, by rfl⟩ : syracuseStep 849181 = 318443) (by norm_num)
theorem B849217 : Blo 754331 849217 := bbase (se 2 (by rfl) ⟨318456, by rfl⟩ : syracuseStep 849217 = 636913) (by norm_num)
theorem B1701197 : Blo 754331 1701197 := bbase (se 3 (by rfl) ⟨318974, by rfl⟩ : syracuseStep 1701197 = 637949) (by norm_num)
theorem B2553173 : Blo 754331 2553173 := bbase (se 13 (by rfl) ⟨467, by rfl⟩ : syracuseStep 2553173 = 935) (by norm_num)
theorem B849253 : Blo 754331 849253 := bbase (se 4 (by rfl) ⟨79617, by rfl⟩ : syracuseStep 849253 = 159235) (by norm_num)
theorem B849289 : Blo 754331 849289 := bbase (se 2 (by rfl) ⟨318483, by rfl⟩ : syracuseStep 849289 = 636967) (by norm_num)
theorem B1275277 : Blo 754331 1275277 := bbase (se 3 (by rfl) ⟨239114, by rfl⟩ : syracuseStep 1275277 = 478229) (by norm_num)
theorem B1701269 : Blo 754331 1701269 := bbase (se 6 (by rfl) ⟨39873, by rfl⟩ : syracuseStep 1701269 = 79747) (by norm_num)
theorem B849325 : Blo 754331 849325 := bbase (se 3 (by rfl) ⟨159248, by rfl⟩ : syracuseStep 849325 = 318497) (by norm_num)
theorem B849361 : Blo 754331 849361 := bbase (se 2 (by rfl) ⟨318510, by rfl⟩ : syracuseStep 849361 = 637021) (by norm_num)
theorem B1701341 : Blo 754331 1701341 := bbase (se 3 (by rfl) ⟨319001, by rfl⟩ : syracuseStep 1701341 = 638003) (by norm_num)
theorem B1275365 : Blo 754331 1275365 := bbase (se 4 (by rfl) ⟨119565, by rfl⟩ : syracuseStep 1275365 = 239131) (by norm_num)
theorem B849397 : Blo 754331 849397 := bbase (se 5 (by rfl) ⟨39815, by rfl⟩ : syracuseStep 849397 = 79631) (by norm_num)
theorem B1439221 : Blo 754331 1439221 := bbase (se 5 (by rfl) ⟨67463, by rfl⟩ : syracuseStep 1439221 = 134927) (by norm_num)
theorem B849433 : Blo 754331 849433 := bbase (se 2 (by rfl) ⟨318537, by rfl⟩ : syracuseStep 849433 = 637075) (by norm_num)
theorem B1701413 : Blo 754331 1701413 := bbase (se 4 (by rfl) ⟨159507, by rfl⟩ : syracuseStep 1701413 = 319015) (by norm_num)
theorem B849469 : Blo 754331 849469 := bbase (se 3 (by rfl) ⟨159275, by rfl⟩ : syracuseStep 849469 = 318551) (by norm_num)
theorem B849505 : Blo 754331 849505 := bbase (se 2 (by rfl) ⟨318564, by rfl⟩ : syracuseStep 849505 = 637129) (by norm_num)
theorem B1275493 : Blo 754331 1275493 := bbase (se 4 (by rfl) ⟨119577, by rfl⟩ : syracuseStep 1275493 = 239155) (by norm_num)
theorem B1701485 : Blo 754331 1701485 := bbase (se 3 (by rfl) ⟨319028, by rfl⟩ : syracuseStep 1701485 = 638057) (by norm_num)
theorem B849541 : Blo 754331 849541 := bbase (se 4 (by rfl) ⟨79644, by rfl⟩ : syracuseStep 849541 = 159289) (by norm_num)
theorem B1439365 : Blo 754331 1439365 := bbase (se 4 (by rfl) ⟨134940, by rfl⟩ : syracuseStep 1439365 = 269881) (by norm_num)
theorem B3831461 : Blo 754331 3831461 := bbase (se 4 (by rfl) ⟨359199, by rfl⟩ : syracuseStep 3831461 = 718399) (by norm_num)
theorem B849577 : Blo 754331 849577 := bbase (se 2 (by rfl) ⟨318591, by rfl⟩ : syracuseStep 849577 = 637183) (by norm_num)
theorem B1701557 : Blo 754331 1701557 := bbase (se 5 (by rfl) ⟨79760, by rfl⟩ : syracuseStep 1701557 = 159521) (by norm_num)
theorem B1275581 : Blo 754331 1275581 := bbase (se 3 (by rfl) ⟨239171, by rfl⟩ : syracuseStep 1275581 = 478343) (by norm_num)
theorem B849613 : Blo 754331 849613 := bbase (se 3 (by rfl) ⟨159302, by rfl⟩ : syracuseStep 849613 = 318605) (by norm_num)
theorem B1210069 : Blo 754331 1210069 := bbase (se 7 (by rfl) ⟨14180, by rfl⟩ : syracuseStep 1210069 = 28361) (by norm_num)
theorem B849649 : Blo 754331 849649 := bbase (se 2 (by rfl) ⟨318618, by rfl⟩ : syracuseStep 849649 = 637237) (by norm_num)
theorem B1701629 : Blo 754331 1701629 := bbase (se 3 (by rfl) ⟨319055, by rfl⟩ : syracuseStep 1701629 = 638111) (by norm_num)
theorem B2553605 : Blo 754331 2553605 := bbase (se 4 (by rfl) ⟨239400, by rfl⟩ : syracuseStep 2553605 = 478801) (by norm_num)
theorem B849685 : Blo 754331 849685 := bbase (se 6 (by rfl) ⟨19914, by rfl⟩ : syracuseStep 849685 = 39829) (by norm_num)
theorem B1439525 : Blo 754331 1439525 := bbase (se 4 (by rfl) ⟨134955, by rfl⟩ : syracuseStep 1439525 = 269911) (by norm_num)
theorem B849721 : Blo 754331 849721 := bbase (se 2 (by rfl) ⟨318645, by rfl⟩ : syracuseStep 849721 = 637291) (by norm_num)
theorem B1275709 : Blo 754331 1275709 := bbase (se 3 (by rfl) ⟨239195, by rfl⟩ : syracuseStep 1275709 = 478391) (by norm_num)
theorem B1701701 : Blo 754331 1701701 := bbase (se 4 (by rfl) ⟨159534, by rfl⟩ : syracuseStep 1701701 = 319069) (by norm_num)
theorem B849757 : Blo 754331 849757 := bbase (se 3 (by rfl) ⟨159329, by rfl⟩ : syracuseStep 849757 = 318659) (by norm_num)
theorem B849793 : Blo 754331 849793 := bbase (se 2 (by rfl) ⟨318672, by rfl⟩ : syracuseStep 849793 = 637345) (by norm_num)
theorem B1701773 : Blo 754331 1701773 := bbase (se 3 (by rfl) ⟨319082, by rfl⟩ : syracuseStep 1701773 = 638165) (by norm_num)
theorem B1275797 : Blo 754331 1275797 := bbase (se 6 (by rfl) ⟨29901, by rfl⟩ : syracuseStep 1275797 = 59803) (by norm_num)
theorem B849829 : Blo 754331 849829 := bbase (se 4 (by rfl) ⟨79671, by rfl⟩ : syracuseStep 849829 = 159343) (by norm_num)
theorem B849865 : Blo 754331 849865 := bbase (se 2 (by rfl) ⟨318699, by rfl⟩ : syracuseStep 849865 = 637399) (by norm_num)
theorem B1701845 : Blo 754331 1701845 := bbase (se 7 (by rfl) ⟨19943, by rfl⟩ : syracuseStep 1701845 = 39887) (by norm_num)
theorem B849901 : Blo 754331 849901 := bbase (se 3 (by rfl) ⟨159356, by rfl⟩ : syracuseStep 849901 = 318713) (by norm_num)
theorem B3635189 : Blo 754331 3635189 := bbase (se 5 (by rfl) ⟨170399, by rfl⟩ : syracuseStep 3635189 = 340799) (by norm_num)
theorem B817165 : Blo 754331 817165 := bbase (se 3 (by rfl) ⟨153218, by rfl⟩ : syracuseStep 817165 = 306437) (by norm_num)
theorem B849937 : Blo 754331 849937 := bbase (se 2 (by rfl) ⟨318726, by rfl⟩ : syracuseStep 849937 = 637453) (by norm_num)
theorem B1275925 : Blo 754331 1275925 := bbase (se 6 (by rfl) ⟨29904, by rfl⟩ : syracuseStep 1275925 = 59809) (by norm_num)
theorem B1701917 : Blo 754331 1701917 := bbase (se 3 (by rfl) ⟨319109, by rfl⟩ : syracuseStep 1701917 = 638219) (by norm_num)
theorem B849973 : Blo 754331 849973 := bbase (se 5 (by rfl) ⟨39842, by rfl⟩ : syracuseStep 849973 = 79685) (by norm_num)
theorem B850009 : Blo 754331 850009 := bbase (se 2 (by rfl) ⟨318753, by rfl⟩ : syracuseStep 850009 = 637507) (by norm_num)
theorem B1701989 : Blo 754331 1701989 := bbase (se 4 (by rfl) ⟨159561, by rfl⟩ : syracuseStep 1701989 = 319123) (by norm_num)
theorem B1276013 : Blo 754331 1276013 := bbase (se 3 (by rfl) ⟨239252, by rfl⟩ : syracuseStep 1276013 = 478505) (by norm_num)
theorem B850045 : Blo 754331 850045 := bbase (se 3 (by rfl) ⟨159383, by rfl⟩ : syracuseStep 850045 = 318767) (by norm_num)
theorem B850081 : Blo 754331 850081 := bbase (se 2 (by rfl) ⟨318780, by rfl⟩ : syracuseStep 850081 = 637561) (by norm_num)
theorem B1702061 : Blo 754331 1702061 := bbase (se 3 (by rfl) ⟨319136, by rfl⟩ : syracuseStep 1702061 = 638273) (by norm_num)
theorem B2554037 : Blo 754331 2554037 := bbase (se 5 (by rfl) ⟨119720, by rfl⟩ : syracuseStep 2554037 = 239441) (by norm_num)
theorem B850117 : Blo 754331 850117 := bbase (se 4 (by rfl) ⟨79698, by rfl⟩ : syracuseStep 850117 = 159397) (by norm_num)
theorem B850153 : Blo 754331 850153 := bbase (se 2 (by rfl) ⟨318807, by rfl⟩ : syracuseStep 850153 = 637615) (by norm_num)
theorem B1276141 : Blo 754331 1276141 := bbase (se 3 (by rfl) ⟨239276, by rfl⟩ : syracuseStep 1276141 = 478553) (by norm_num)
theorem B1702133 : Blo 754331 1702133 := bbase (se 5 (by rfl) ⟨79787, by rfl⟩ : syracuseStep 1702133 = 159575) (by norm_num)
theorem B1210621 : Blo 754331 1210621 := bbase (se 3 (by rfl) ⟨226991, by rfl⟩ : syracuseStep 1210621 = 453983) (by norm_num)
theorem B850189 : Blo 754331 850189 := bbase (se 3 (by rfl) ⟨159410, by rfl⟩ : syracuseStep 850189 = 318821) (by norm_num)
theorem B1079581 : Blo 754331 1079581 := bbase (se 3 (by rfl) ⟨202421, by rfl⟩ : syracuseStep 1079581 = 404843) (by norm_num)
theorem B850225 : Blo 754331 850225 := bbase (se 2 (by rfl) ⟨318834, by rfl⟩ : syracuseStep 850225 = 637669) (by norm_num)
theorem B3733813 : Blo 754331 3733813 := bbase (se 5 (by rfl) ⟨175022, by rfl⟩ : syracuseStep 3733813 = 350045) (by norm_num)
theorem B1702205 : Blo 754331 1702205 := bbase (se 3 (by rfl) ⟨319163, by rfl⟩ : syracuseStep 1702205 = 638327) (by norm_num)
theorem B1276229 : Blo 754331 1276229 := bbase (se 4 (by rfl) ⟨119646, by rfl⟩ : syracuseStep 1276229 = 239293) (by norm_num)
theorem B850261 : Blo 754331 850261 := bbase (se 10 (by rfl) ⟨1245, by rfl⟩ : syracuseStep 850261 = 2491) (by norm_num)
theorem B850297 : Blo 754331 850297 := bbase (se 2 (by rfl) ⟨318861, by rfl⟩ : syracuseStep 850297 = 637723) (by norm_num)
theorem B1702277 : Blo 754331 1702277 := bbase (se 4 (by rfl) ⟨159588, by rfl⟩ : syracuseStep 1702277 = 319177) (by norm_num)
theorem B2423189 : Blo 754331 2423189 := bbase (se 6 (by rfl) ⟨56793, by rfl⟩ : syracuseStep 2423189 = 113587) (by norm_num)
theorem B817561 : Blo 754331 817561 := bbase (se 2 (by rfl) ⟨306585, by rfl⟩ : syracuseStep 817561 = 613171) (by norm_num)
theorem B850333 : Blo 754331 850333 := bbase (se 3 (by rfl) ⟨159437, by rfl⟩ : syracuseStep 850333 = 318875) (by norm_num)
theorem B850369 : Blo 754331 850369 := bbase (se 2 (by rfl) ⟨318888, by rfl⟩ : syracuseStep 850369 = 637777) (by norm_num)
theorem B1276357 : Blo 754331 1276357 := bbase (se 4 (by rfl) ⟨119658, by rfl⟩ : syracuseStep 1276357 = 239317) (by norm_num)
theorem B1702349 : Blo 754331 1702349 := bbase (se 3 (by rfl) ⟨319190, by rfl⟩ : syracuseStep 1702349 = 638381) (by norm_num)
theorem B850405 : Blo 754331 850405 := bbase (se 4 (by rfl) ⟨79725, by rfl⟩ : syracuseStep 850405 = 159451) (by norm_num)
theorem B1210877 : Blo 754331 1210877 := bbase (se 3 (by rfl) ⟨227039, by rfl⟩ : syracuseStep 1210877 = 454079) (by norm_num)
theorem B850441 : Blo 754331 850441 := bbase (se 2 (by rfl) ⟨318915, by rfl⟩ : syracuseStep 850441 = 637831) (by norm_num)
theorem B2423317 : Blo 754331 2423317 := bbase (se 6 (by rfl) ⟨56796, by rfl⟩ : syracuseStep 2423317 = 113593) (by norm_num)
theorem B1702421 : Blo 754331 1702421 := bbase (se 6 (by rfl) ⟨39900, by rfl⟩ : syracuseStep 1702421 = 79801) (by norm_num)
theorem B1276445 : Blo 754331 1276445 := bbase (se 3 (by rfl) ⟨239333, by rfl⟩ : syracuseStep 1276445 = 478667) (by norm_num)
theorem B850477 : Blo 754331 850477 := bbase (se 3 (by rfl) ⟨159464, by rfl⟩ : syracuseStep 850477 = 318929) (by norm_num)
theorem B850513 : Blo 754331 850513 := bbase (se 2 (by rfl) ⟨318942, by rfl⟩ : syracuseStep 850513 = 637885) (by norm_num)
theorem B1702493 : Blo 754331 1702493 := bbase (se 3 (by rfl) ⟨319217, by rfl⟩ : syracuseStep 1702493 = 638435) (by norm_num)
theorem B2554469 : Blo 754331 2554469 := bbase (se 4 (by rfl) ⟨239481, by rfl⟩ : syracuseStep 2554469 = 478963) (by norm_num)
theorem B850549 : Blo 754331 850549 := bbase (se 5 (by rfl) ⟨39869, by rfl⟩ : syracuseStep 850549 = 79739) (by norm_num)
theorem B850585 : Blo 754331 850585 := bbase (se 2 (by rfl) ⟨318969, by rfl⟩ : syracuseStep 850585 = 637939) (by norm_num)
theorem B1276573 : Blo 754331 1276573 := bbase (se 3 (by rfl) ⟨239357, by rfl⟩ : syracuseStep 1276573 = 478715) (by norm_num)
theorem B1702565 : Blo 754331 1702565 := bbase (se 4 (by rfl) ⟨159615, by rfl⟩ : syracuseStep 1702565 = 319231) (by norm_num)
theorem B850621 : Blo 754331 850621 := bbase (se 3 (by rfl) ⟨159491, by rfl⟩ : syracuseStep 850621 = 318983) (by norm_num)
theorem B850657 : Blo 754331 850657 := bbase (se 2 (by rfl) ⟨318996, by rfl⟩ : syracuseStep 850657 = 637993) (by norm_num)
theorem B1702637 : Blo 754331 1702637 := bbase (se 3 (by rfl) ⟨319244, by rfl⟩ : syracuseStep 1702637 = 638489) (by norm_num)
theorem B1276661 : Blo 754331 1276661 := bbase (se 5 (by rfl) ⟨59843, by rfl⟩ : syracuseStep 1276661 = 119687) (by norm_num)
theorem B850693 : Blo 754331 850693 := bbase (se 4 (by rfl) ⟨79752, by rfl⟩ : syracuseStep 850693 = 159505) (by norm_num)
theorem B2423573 : Blo 754331 2423573 := bbase (se 6 (by rfl) ⟨56802, by rfl⟩ : syracuseStep 2423573 = 113605) (by norm_num)
theorem B850729 : Blo 754331 850729 := bbase (se 2 (by rfl) ⟨319023, by rfl⟩ : syracuseStep 850729 = 638047) (by norm_num)
theorem B1702709 : Blo 754331 1702709 := bbase (se 5 (by rfl) ⟨79814, by rfl⟩ : syracuseStep 1702709 = 159629) (by norm_num)
theorem B850765 : Blo 754331 850765 := bbase (se 3 (by rfl) ⟨159518, by rfl⟩ : syracuseStep 850765 = 319037) (by norm_num)
theorem B850801 : Blo 754331 850801 := bbase (se 2 (by rfl) ⟨319050, by rfl⟩ : syracuseStep 850801 = 638101) (by norm_num)
theorem B1276789 : Blo 754331 1276789 := bbase (se 5 (by rfl) ⟨59849, by rfl⟩ : syracuseStep 1276789 = 119699) (by norm_num)
theorem B1702781 : Blo 754331 1702781 := bbase (se 3 (by rfl) ⟨319271, by rfl⟩ : syracuseStep 1702781 = 638543) (by norm_num)
theorem B850837 : Blo 754331 850837 := bbase (se 6 (by rfl) ⟨19941, by rfl⟩ : syracuseStep 850837 = 39883) (by norm_num)
theorem B3832757 : Blo 754331 3832757 := bbase (se 5 (by rfl) ⟨179660, by rfl⟩ : syracuseStep 3832757 = 359321) (by norm_num)
theorem B850873 : Blo 754331 850873 := bbase (se 2 (by rfl) ⟨319077, by rfl⟩ : syracuseStep 850873 = 638155) (by norm_num)
theorem B1702853 : Blo 754331 1702853 := bbase (se 4 (by rfl) ⟨159642, by rfl⟩ : syracuseStep 1702853 = 319285) (by norm_num)
theorem B1276877 : Blo 754331 1276877 := bbase (se 3 (by rfl) ⟨239414, by rfl⟩ : syracuseStep 1276877 = 478829) (by norm_num)
theorem B2718677 : Blo 754331 2718677 := bbase (se 7 (by rfl) ⟨31859, by rfl⟩ : syracuseStep 2718677 = 63719) (by norm_num)
theorem B850909 : Blo 754331 850909 := bbase (se 3 (by rfl) ⟨159545, by rfl⟩ : syracuseStep 850909 = 319091) (by norm_num)
theorem B850945 : Blo 754331 850945 := bbase (se 2 (by rfl) ⟨319104, by rfl⟩ : syracuseStep 850945 = 638209) (by norm_num)
theorem B1702925 : Blo 754331 1702925 := bbase (se 3 (by rfl) ⟨319298, by rfl⟩ : syracuseStep 1702925 = 638597) (by norm_num)
theorem B2554901 : Blo 754331 2554901 := bbase (se 6 (by rfl) ⟨59880, by rfl⟩ : syracuseStep 2554901 = 119761) (by norm_num)
theorem B850981 : Blo 754331 850981 := bbase (se 4 (by rfl) ⟨79779, by rfl⟩ : syracuseStep 850981 = 159559) (by norm_num)
theorem B851017 : Blo 754331 851017 := bbase (se 2 (by rfl) ⟨319131, by rfl⟩ : syracuseStep 851017 = 638263) (by norm_num)
theorem B1277005 : Blo 754331 1277005 := bbase (se 3 (by rfl) ⟨239438, by rfl⟩ : syracuseStep 1277005 = 478877) (by norm_num)
theorem B1702997 : Blo 754331 1702997 := bbase (se 8 (by rfl) ⟨9978, by rfl⟩ : syracuseStep 1702997 = 19957) (by norm_num)
theorem B851053 : Blo 754331 851053 := bbase (se 3 (by rfl) ⟨159572, by rfl⟩ : syracuseStep 851053 = 319145) (by norm_num)
theorem B851089 : Blo 754331 851089 := bbase (se 2 (by rfl) ⟨319158, by rfl⟩ : syracuseStep 851089 = 638317) (by norm_num)
theorem B1703069 : Blo 754331 1703069 := bbase (se 3 (by rfl) ⟨319325, by rfl⟩ : syracuseStep 1703069 = 638651) (by norm_num)
theorem B883877 : Blo 754331 883877 := bbase (se 4 (by rfl) ⟨82863, by rfl⟩ : syracuseStep 883877 = 165727) (by norm_num)
theorem B1277093 : Blo 754331 1277093 := bbase (se 4 (by rfl) ⟨119727, by rfl⟩ : syracuseStep 1277093 = 239455) (by norm_num)
theorem B851125 : Blo 754331 851125 := bbase (se 5 (by rfl) ⟨39896, by rfl⟩ : syracuseStep 851125 = 79793) (by norm_num)
theorem B1211581 : Blo 754331 1211581 := bbase (se 3 (by rfl) ⟨227171, by rfl⟩ : syracuseStep 1211581 = 454343) (by norm_num)
theorem B851161 : Blo 754331 851161 := bbase (se 2 (by rfl) ⟨319185, by rfl⟩ : syracuseStep 851161 = 638371) (by norm_num)
theorem B1703141 : Blo 754331 1703141 := bbase (se 4 (by rfl) ⟨159669, by rfl⟩ : syracuseStep 1703141 = 319339) (by norm_num)
theorem B2718965 : Blo 754331 2718965 := bbase (se 5 (by rfl) ⟨127451, by rfl⟩ : syracuseStep 2718965 = 254903) (by norm_num)
theorem B851197 : Blo 754331 851197 := bbase (se 3 (by rfl) ⟨159599, by rfl⟩ : syracuseStep 851197 = 319199) (by norm_num)
theorem B851233 : Blo 754331 851233 := bbase (se 2 (by rfl) ⟨319212, by rfl⟩ : syracuseStep 851233 = 638425) (by norm_num)
theorem B1277221 : Blo 754331 1277221 := bbase (se 4 (by rfl) ⟨119739, by rfl⟩ : syracuseStep 1277221 = 239479) (by norm_num)
theorem B1703213 : Blo 754331 1703213 := bbase (se 3 (by rfl) ⟨319352, by rfl⟩ : syracuseStep 1703213 = 638705) (by norm_num)
theorem B851269 : Blo 754331 851269 := bbase (se 4 (by rfl) ⟨79806, by rfl⟩ : syracuseStep 851269 = 159613) (by norm_num)
theorem B851305 : Blo 754331 851305 := bbase (se 2 (by rfl) ⟨319239, by rfl⟩ : syracuseStep 851305 = 638479) (by norm_num)
theorem B1703285 : Blo 754331 1703285 := bbase (se 5 (by rfl) ⟨79841, by rfl⟩ : syracuseStep 1703285 = 159683) (by norm_num)
theorem B1277309 : Blo 754331 1277309 := bbase (se 3 (by rfl) ⟨239495, by rfl⟩ : syracuseStep 1277309 = 478991) (by norm_num)
theorem B851341 : Blo 754331 851341 := bbase (se 3 (by rfl) ⟨159626, by rfl⟩ : syracuseStep 851341 = 319253) (by norm_num)
theorem B851377 : Blo 754331 851377 := bbase (se 2 (by rfl) ⟨319266, by rfl⟩ : syracuseStep 851377 = 638533) (by norm_num)
theorem B1703357 : Blo 754331 1703357 := bbase (se 3 (by rfl) ⟨319379, by rfl⟩ : syracuseStep 1703357 = 638759) (by norm_num)
theorem B2555333 : Blo 754331 2555333 := bbase (se 4 (by rfl) ⟨239562, by rfl⟩ : syracuseStep 2555333 = 479125) (by norm_num)
theorem B851413 : Blo 754331 851413 := bbase (se 7 (by rfl) ⟨9977, by rfl⟩ : syracuseStep 851413 = 19955) (by norm_num)
theorem B851449 : Blo 754331 851449 := bbase (se 2 (by rfl) ⟨319293, by rfl⟩ : syracuseStep 851449 = 638587) (by norm_num)
theorem B1277437 : Blo 754331 1277437 := bbase (se 3 (by rfl) ⟨239519, by rfl⟩ : syracuseStep 1277437 = 479039) (by norm_num)
theorem B1703429 : Blo 754331 1703429 := bbase (se 4 (by rfl) ⟨159696, by rfl⟩ : syracuseStep 1703429 = 319393) (by norm_num)
theorem B851485 : Blo 754331 851485 := bbase (se 3 (by rfl) ⟨159653, by rfl⟩ : syracuseStep 851485 = 319307) (by norm_num)
theorem B851521 : Blo 754331 851521 := bbase (se 2 (by rfl) ⟨319320, by rfl⟩ : syracuseStep 851521 = 638641) (by norm_num)
theorem B1703501 : Blo 754331 1703501 := bbase (se 3 (by rfl) ⟨319406, by rfl⟩ : syracuseStep 1703501 = 638813) (by norm_num)
theorem B1277525 : Blo 754331 1277525 := bbase (se 8 (by rfl) ⟨7485, by rfl⟩ : syracuseStep 1277525 = 14971) (by norm_num)
theorem B1212005 : Blo 754331 1212005 := bbase (se 4 (by rfl) ⟨113625, by rfl⟩ : syracuseStep 1212005 = 227251) (by norm_num)
theorem B851557 : Blo 754331 851557 := bbase (se 4 (by rfl) ⟨79833, by rfl⟩ : syracuseStep 851557 = 159667) (by norm_num)
theorem B851593 : Blo 754331 851593 := bbase (se 2 (by rfl) ⟨319347, by rfl⟩ : syracuseStep 851593 = 638695) (by norm_num)
theorem B1703573 : Blo 754331 1703573 := bbase (se 6 (by rfl) ⟨39927, by rfl⟩ : syracuseStep 1703573 = 79855) (by norm_num)
theorem B851629 : Blo 754331 851629 := bbase (se 3 (by rfl) ⟨159680, by rfl⟩ : syracuseStep 851629 = 319361) (by norm_num)
theorem B851665 : Blo 754331 851665 := bbase (se 2 (by rfl) ⟨319374, by rfl⟩ : syracuseStep 851665 = 638749) (by norm_num)
theorem B1277653 : Blo 754331 1277653 := bbase (se 7 (by rfl) ⟨14972, by rfl⟩ : syracuseStep 1277653 = 29945) (by norm_num)
theorem B1703645 : Blo 754331 1703645 := bbase (se 3 (by rfl) ⟨319433, by rfl⟩ : syracuseStep 1703645 = 638867) (by norm_num)
theorem B2457317 : Blo 754331 2457317 := bbase (se 4 (by rfl) ⟨230373, by rfl⟩ : syracuseStep 2457317 = 460747) (by norm_num)
theorem B851701 : Blo 754331 851701 := bbase (se 5 (by rfl) ⟨39923, by rfl⟩ : syracuseStep 851701 = 79847) (by norm_num)
theorem B851737 : Blo 754331 851737 := bbase (se 2 (by rfl) ⟨319401, by rfl⟩ : syracuseStep 851737 = 638803) (by norm_num)
theorem B1703717 : Blo 754331 1703717 := bbase (se 4 (by rfl) ⟨159723, by rfl⟩ : syracuseStep 1703717 = 319447) (by norm_num)
theorem B1277741 : Blo 754331 1277741 := bbase (se 3 (by rfl) ⟨239576, by rfl⟩ : syracuseStep 1277741 = 479153) (by norm_num)
theorem B851773 : Blo 754331 851773 := bbase (se 3 (by rfl) ⟨159707, by rfl⟩ : syracuseStep 851773 = 319415) (by norm_num)
theorem B851809 : Blo 754331 851809 := bbase (se 2 (by rfl) ⟨319428, by rfl⟩ : syracuseStep 851809 = 638857) (by norm_num)
theorem B1638245 : Blo 754331 1638245 := bbase (se 4 (by rfl) ⟨153585, by rfl⟩ : syracuseStep 1638245 = 307171) (by norm_num)
theorem B1703789 : Blo 754331 1703789 := bbase (se 3 (by rfl) ⟨319460, by rfl⟩ : syracuseStep 1703789 = 638921) (by norm_num)
theorem B2555765 : Blo 754331 2555765 := bbase (se 5 (by rfl) ⟨119801, by rfl⟩ : syracuseStep 2555765 = 239603) (by norm_num)
theorem B1212293 : Blo 754331 1212293 := bbase (se 4 (by rfl) ⟨113652, by rfl⟩ : syracuseStep 1212293 = 227305) (by norm_num)
theorem B851845 : Blo 754331 851845 := bbase (se 4 (by rfl) ⟨79860, by rfl⟩ : syracuseStep 851845 = 159721) (by norm_num)
theorem B851881 : Blo 754331 851881 := bbase (se 2 (by rfl) ⟨319455, by rfl⟩ : syracuseStep 851881 = 638911) (by norm_num)
theorem B1277869 : Blo 754331 1277869 := bbase (se 3 (by rfl) ⟨239600, by rfl⟩ : syracuseStep 1277869 = 479201) (by norm_num)
theorem B1703861 : Blo 754331 1703861 := bbase (se 5 (by rfl) ⟨79868, by rfl⟩ : syracuseStep 1703861 = 159737) (by norm_num)
theorem B851917 : Blo 754331 851917 := bbase (se 3 (by rfl) ⟨159734, by rfl⟩ : syracuseStep 851917 = 319469) (by norm_num)
theorem B851953 : Blo 754331 851953 := bbase (se 2 (by rfl) ⟨319482, by rfl⟩ : syracuseStep 851953 = 638965) (by norm_num)
theorem B851971 : Blo 754331 851971 := bstep (se 1 (by rfl) ⟨638978, by rfl⟩ : syracuseStep 851971 = 1277957) B1277957
theorem B3833891 : Blo 754331 3833891 := bstep (se 1 (by rfl) ⟨2875418, by rfl⟩ : syracuseStep 3833891 = 5750837) B5750837
theorem B4358213 : Blo 754331 4358213 := bstep (se 4 (by rfl) ⟨408582, by rfl⟩ : syracuseStep 4358213 = 817165) B817165
theorem B2555981 : Blo 754331 2555981 := bstep (se 3 (by rfl) ⟨479246, by rfl⟩ : syracuseStep 2555981 = 958493) B958493
theorem B52396145 : Blo 754331 52396145 := bstep (se 2 (by rfl) ⟨19648554, by rfl⟩ : syracuseStep 52396145 = 39297109) B39297109
theorem B1278065 : Blo 754331 1278065 := bstep (se 2 (by rfl) ⟨479274, by rfl⟩ : syracuseStep 1278065 = 958549) B958549
theorem B2556035 : Blo 754331 2556035 := bstep (se 1 (by rfl) ⟨1917026, by rfl⟩ : syracuseStep 2556035 = 3834053) B3834053
theorem B852115 : Blo 754331 852115 := bstep (se 1 (by rfl) ⟨639086, by rfl⟩ : syracuseStep 852115 = 1278173) B1278173
theorem B1704113 : Blo 754331 1704113 := bstep (se 2 (by rfl) ⟨639042, by rfl⟩ : syracuseStep 1704113 = 1278085) B1278085
theorem B1704131 : Blo 754331 1704131 := bstep (se 1 (by rfl) ⟨1278098, by rfl⟩ : syracuseStep 1704131 = 2556197) B2556197
theorem B1278193 : Blo 754331 1278193 := bstep (se 2 (by rfl) ⟨479322, by rfl⟩ : syracuseStep 1278193 = 958645) B958645
theorem B1278227 : Blo 754331 1278227 := bstep (se 1 (by rfl) ⟨958670, by rfl⟩ : syracuseStep 1278227 = 1917341) B1917341
theorem B852259 : Blo 754331 852259 := bstep (se 1 (by rfl) ⟨639194, by rfl⟩ : syracuseStep 852259 = 1278389) B1278389
theorem B3277169 : Blo 754331 3277169 := bstep (se 2 (by rfl) ⟨1228938, by rfl⟩ : syracuseStep 3277169 = 2457877) B2457877
theorem B2556305 : Blo 754331 2556305 := bstep (se 2 (by rfl) ⟨958614, by rfl⟩ : syracuseStep 2556305 = 1917229) B1917229
theorem B1278355 : Blo 754331 1278355 := bstep (se 1 (by rfl) ⟨958766, by rfl⟩ : syracuseStep 1278355 = 1917533) B1917533
theorem B2425265 : Blo 754331 2425265 := bstep (se 2 (by rfl) ⟨909474, by rfl⟩ : syracuseStep 2425265 = 1818949) B1818949
theorem B852403 : Blo 754331 852403 := bstep (se 1 (by rfl) ⟨639302, by rfl⟩ : syracuseStep 852403 = 1278605) B1278605
theorem B1704401 : Blo 754331 1704401 := bstep (se 2 (by rfl) ⟨639150, by rfl⟩ : syracuseStep 1704401 = 1278301) B1278301
theorem B2425315 : Blo 754331 2425315 := bstep (se 1 (by rfl) ⟨1818986, by rfl⟩ : syracuseStep 2425315 = 3637973) B3637973
theorem B1704419 : Blo 754331 1704419 := bstep (se 1 (by rfl) ⟨1278314, by rfl⟩ : syracuseStep 1704419 = 2556629) B2556629
theorem B1278497 : Blo 754331 1278497 := bstep (se 2 (by rfl) ⟨479436, by rfl⟩ : syracuseStep 1278497 = 958873) B958873
theorem B852547 : Blo 754331 852547 := bstep (se 1 (by rfl) ⟨639410, by rfl⟩ : syracuseStep 852547 = 1278821) B1278821
theorem B1278625 : Blo 754331 1278625 := bstep (se 2 (by rfl) ⟨479484, by rfl⟩ : syracuseStep 1278625 = 958969) B958969
theorem B754339 : Blo 754331 754339 := bstep (se 1 (by rfl) ⟨565754, by rfl⟩ : syracuseStep 754339 = 1131509) B1131509
theorem B754355 : Blo 754331 754355 := bstep (se 1 (by rfl) ⟨565766, by rfl⟩ : syracuseStep 754355 = 1131533) B1131533
theorem B754371 : Blo 754331 754371 := bstep (se 1 (by rfl) ⟨565778, by rfl⟩ : syracuseStep 754371 = 1131557) B1131557
theorem B1278659 : Blo 754331 1278659 := bstep (se 1 (by rfl) ⟨958994, by rfl⟩ : syracuseStep 1278659 = 1917989) B1917989
theorem B754387 : Blo 754331 754387 := bstep (se 1 (by rfl) ⟨565790, by rfl⟩ : syracuseStep 754387 = 1131581) B1131581
theorem B852691 : Blo 754331 852691 := bstep (se 1 (by rfl) ⟨639518, by rfl⟩ : syracuseStep 852691 = 1279037) B1279037
theorem B754403 : Blo 754331 754403 := bstep (se 1 (by rfl) ⟨565802, by rfl⟩ : syracuseStep 754403 = 1131605) B1131605
theorem B1704689 : Blo 754331 1704689 := bstep (se 2 (by rfl) ⟨639258, by rfl⟩ : syracuseStep 1704689 = 1278517) B1278517
theorem B754419 : Blo 754331 754419 := bstep (se 1 (by rfl) ⟨565814, by rfl⟩ : syracuseStep 754419 = 1131629) B1131629
theorem B754435 : Blo 754331 754435 := bstep (se 1 (by rfl) ⟨565826, by rfl⟩ : syracuseStep 754435 = 1131653) B1131653
theorem B1704707 : Blo 754331 1704707 := bstep (se 1 (by rfl) ⟨1278530, by rfl⟩ : syracuseStep 1704707 = 2557061) B2557061
theorem B754451 : Blo 754331 754451 := bstep (se 1 (by rfl) ⟨565838, by rfl⟩ : syracuseStep 754451 = 1131677) B1131677
theorem B754467 : Blo 754331 754467 := bstep (se 1 (by rfl) ⟨565850, by rfl⟩ : syracuseStep 754467 = 1131701) B1131701
theorem B754483 : Blo 754331 754483 := bstep (se 1 (by rfl) ⟨565862, by rfl⟩ : syracuseStep 754483 = 1131725) B1131725
theorem B1213235 : Blo 754331 1213235 := bstep (se 1 (by rfl) ⟨909926, by rfl⟩ : syracuseStep 1213235 = 1819853) B1819853
theorem B754499 : Blo 754331 754499 := bstep (se 1 (by rfl) ⟨565874, by rfl⟩ : syracuseStep 754499 = 1131749) B1131749
theorem B1278787 : Blo 754331 1278787 := bstep (se 1 (by rfl) ⟨959090, by rfl⟩ : syracuseStep 1278787 = 1918181) B1918181
theorem B3834701 : Blo 754331 3834701 := bstep (se 3 (by rfl) ⟨719006, by rfl⟩ : syracuseStep 3834701 = 1438013) B1438013
theorem B754515 : Blo 754331 754515 := bstep (se 1 (by rfl) ⟨565886, by rfl⟩ : syracuseStep 754515 = 1131773) B1131773
theorem B754531 : Blo 754331 754531 := bstep (se 1 (by rfl) ⟨565898, by rfl⟩ : syracuseStep 754531 = 1131797) B1131797
theorem B852835 : Blo 754331 852835 := bstep (se 1 (by rfl) ⟨639626, by rfl⟩ : syracuseStep 852835 = 1279253) B1279253
theorem B754547 : Blo 754331 754547 := bstep (se 1 (by rfl) ⟨565910, by rfl⟩ : syracuseStep 754547 = 1131821) B1131821
theorem B754563 : Blo 754331 754563 := bstep (se 1 (by rfl) ⟨565922, by rfl⟩ : syracuseStep 754563 = 1131845) B1131845
theorem B1868689 : Blo 754331 1868689 := bstep (se 2 (by rfl) ⟨700758, by rfl⟩ : syracuseStep 1868689 = 1401517) B1401517
theorem B754579 : Blo 754331 754579 := bstep (se 1 (by rfl) ⟨565934, by rfl⟩ : syracuseStep 754579 = 1131869) B1131869
theorem B754595 : Blo 754331 754595 := bstep (se 1 (by rfl) ⟨565946, by rfl⟩ : syracuseStep 754595 = 1131893) B1131893
theorem B2556845 : Blo 754331 2556845 := bstep (se 3 (by rfl) ⟨479408, by rfl⟩ : syracuseStep 2556845 = 958817) B958817
theorem B754611 : Blo 754331 754611 := bstep (se 1 (by rfl) ⟨565958, by rfl⟩ : syracuseStep 754611 = 1131917) B1131917
theorem B754627 : Blo 754331 754627 := bstep (se 1 (by rfl) ⟨565970, by rfl⟩ : syracuseStep 754627 = 1131941) B1131941
theorem B1278929 : Blo 754331 1278929 := bstep (se 2 (by rfl) ⟨479598, by rfl⟩ : syracuseStep 1278929 = 959197) B959197
theorem B754643 : Blo 754331 754643 := bstep (se 1 (by rfl) ⟨565982, by rfl⟩ : syracuseStep 754643 = 1131965) B1131965
theorem B754659 : Blo 754331 754659 := bstep (se 1 (by rfl) ⟨565994, by rfl⟩ : syracuseStep 754659 = 1131989) B1131989
theorem B2556899 : Blo 754331 2556899 := bstep (se 1 (by rfl) ⟨1917674, by rfl⟩ : syracuseStep 2556899 = 3835349) B3835349
theorem B754675 : Blo 754331 754675 := bstep (se 1 (by rfl) ⟨566006, by rfl⟩ : syracuseStep 754675 = 1132013) B1132013
theorem B1213427 : Blo 754331 1213427 := bstep (se 1 (by rfl) ⟨910070, by rfl⟩ : syracuseStep 1213427 = 1820141) B1820141
theorem B852979 : Blo 754331 852979 := bstep (se 1 (by rfl) ⟨639734, by rfl⟩ : syracuseStep 852979 = 1279469) B1279469
theorem B754691 : Blo 754331 754691 := bstep (se 1 (by rfl) ⟨566018, by rfl⟩ : syracuseStep 754691 = 1132037) B1132037
theorem B1704977 : Blo 754331 1704977 := bstep (se 2 (by rfl) ⟨639366, by rfl⟩ : syracuseStep 1704977 = 1278733) B1278733
theorem B754707 : Blo 754331 754707 := bstep (se 1 (by rfl) ⟨566030, by rfl⟩ : syracuseStep 754707 = 1132061) B1132061
theorem B754723 : Blo 754331 754723 := bstep (se 1 (by rfl) ⟨566042, by rfl⟩ : syracuseStep 754723 = 1132085) B1132085
theorem B1704995 : Blo 754331 1704995 := bstep (se 1 (by rfl) ⟨1278746, by rfl⟩ : syracuseStep 1704995 = 2557493) B2557493
theorem B754739 : Blo 754331 754739 := bstep (se 1 (by rfl) ⟨566054, by rfl⟩ : syracuseStep 754739 = 1132109) B1132109
theorem B754755 : Blo 754331 754755 := bstep (se 1 (by rfl) ⟨566066, by rfl⟩ : syracuseStep 754755 = 1132133) B1132133
theorem B1279057 : Blo 754331 1279057 := bstep (se 2 (by rfl) ⟨479646, by rfl⟩ : syracuseStep 1279057 = 959293) B959293
theorem B754771 : Blo 754331 754771 := bstep (se 1 (by rfl) ⟨566078, by rfl⟩ : syracuseStep 754771 = 1132157) B1132157
theorem B754787 : Blo 754331 754787 := bstep (se 1 (by rfl) ⟨566090, by rfl⟩ : syracuseStep 754787 = 1132181) B1132181
theorem B754803 : Blo 754331 754803 := bstep (se 1 (by rfl) ⟨566102, by rfl⟩ : syracuseStep 754803 = 1132205) B1132205
theorem B1213555 : Blo 754331 1213555 := bstep (se 1 (by rfl) ⟨910166, by rfl⟩ : syracuseStep 1213555 = 1820333) B1820333
theorem B1279091 : Blo 754331 1279091 := bstep (se 1 (by rfl) ⟨959318, by rfl⟩ : syracuseStep 1279091 = 1918637) B1918637
theorem B754819 : Blo 754331 754819 := bstep (se 1 (by rfl) ⟨566114, by rfl⟩ : syracuseStep 754819 = 1132229) B1132229
theorem B853123 : Blo 754331 853123 := bstep (se 1 (by rfl) ⟨639842, by rfl⟩ : syracuseStep 853123 = 1279685) B1279685
theorem B754835 : Blo 754331 754835 := bstep (se 1 (by rfl) ⟨566126, by rfl⟩ : syracuseStep 754835 = 1132253) B1132253
theorem B754851 : Blo 754331 754851 := bstep (se 1 (by rfl) ⟨566138, by rfl⟩ : syracuseStep 754851 = 1132277) B1132277
theorem B2426033 : Blo 754331 2426033 := bstep (se 2 (by rfl) ⟨909762, by rfl⟩ : syracuseStep 2426033 = 1819525) B1819525
theorem B754867 : Blo 754331 754867 := bstep (se 1 (by rfl) ⟨566150, by rfl⟩ : syracuseStep 754867 = 1132301) B1132301
theorem B754883 : Blo 754331 754883 := bstep (se 1 (by rfl) ⟨566162, by rfl⟩ : syracuseStep 754883 = 1132325) B1132325
theorem B754899 : Blo 754331 754899 := bstep (se 1 (by rfl) ⟨566174, by rfl⟩ : syracuseStep 754899 = 1132349) B1132349
theorem B754915 : Blo 754331 754915 := bstep (se 1 (by rfl) ⟨566186, by rfl⟩ : syracuseStep 754915 = 1132373) B1132373
theorem B2557169 : Blo 754331 2557169 := bstep (se 2 (by rfl) ⟨958938, by rfl⟩ : syracuseStep 2557169 = 1917877) B1917877
theorem B754931 : Blo 754331 754931 := bstep (se 1 (by rfl) ⟨566198, by rfl⟩ : syracuseStep 754931 = 1132397) B1132397
theorem B1279219 : Blo 754331 1279219 := bstep (se 1 (by rfl) ⟨959414, by rfl⟩ : syracuseStep 1279219 = 1918829) B1918829
theorem B754947 : Blo 754331 754947 := bstep (se 1 (by rfl) ⟨566210, by rfl⟩ : syracuseStep 754947 = 1132421) B1132421
theorem B754963 : Blo 754331 754963 := bstep (se 1 (by rfl) ⟨566222, by rfl⟩ : syracuseStep 754963 = 1132445) B1132445
theorem B754979 : Blo 754331 754979 := bstep (se 1 (by rfl) ⟨566234, by rfl⟩ : syracuseStep 754979 = 1132469) B1132469
theorem B1705265 : Blo 754331 1705265 := bstep (se 2 (by rfl) ⟨639474, by rfl⟩ : syracuseStep 1705265 = 1278949) B1278949
theorem B754995 : Blo 754331 754995 := bstep (se 1 (by rfl) ⟨566246, by rfl⟩ : syracuseStep 754995 = 1132493) B1132493
theorem B755011 : Blo 754331 755011 := bstep (se 1 (by rfl) ⟨566258, by rfl⟩ : syracuseStep 755011 = 1132517) B1132517
theorem B1705283 : Blo 754331 1705283 := bstep (se 1 (by rfl) ⟨1278962, by rfl⟩ : syracuseStep 1705283 = 2557925) B2557925
theorem B755027 : Blo 754331 755027 := bstep (se 1 (by rfl) ⟨566270, by rfl⟩ : syracuseStep 755027 = 1132541) B1132541
theorem B755043 : Blo 754331 755043 := bstep (se 1 (by rfl) ⟨566282, by rfl⟩ : syracuseStep 755043 = 1132565) B1132565
theorem B755059 : Blo 754331 755059 := bstep (se 1 (by rfl) ⟨566294, by rfl⟩ : syracuseStep 755059 = 1132589) B1132589
theorem B1279361 : Blo 754331 1279361 := bstep (se 2 (by rfl) ⟨479760, by rfl⟩ : syracuseStep 1279361 = 959521) B959521
theorem B755075 : Blo 754331 755075 := bstep (se 1 (by rfl) ⟨566306, by rfl⟩ : syracuseStep 755075 = 1132613) B1132613
theorem B755091 : Blo 754331 755091 := bstep (se 1 (by rfl) ⟨566318, by rfl⟩ : syracuseStep 755091 = 1132637) B1132637
theorem B755107 : Blo 754331 755107 := bstep (se 1 (by rfl) ⟨566330, by rfl⟩ : syracuseStep 755107 = 1132661) B1132661
theorem B755123 : Blo 754331 755123 := bstep (se 1 (by rfl) ⟨566342, by rfl⟩ : syracuseStep 755123 = 1132685) B1132685
theorem B755139 : Blo 754331 755139 := bstep (se 1 (by rfl) ⟨566354, by rfl⟩ : syracuseStep 755139 = 1132709) B1132709
theorem B755155 : Blo 754331 755155 := bstep (se 1 (by rfl) ⟨566366, by rfl⟩ : syracuseStep 755155 = 1132733) B1132733
theorem B755171 : Blo 754331 755171 := bstep (se 1 (by rfl) ⟨566378, by rfl⟩ : syracuseStep 755171 = 1132757) B1132757
theorem B1639907 : Blo 754331 1639907 := bstep (se 1 (by rfl) ⟨1229930, by rfl⟩ : syracuseStep 1639907 = 2459861) B2459861
theorem B755187 : Blo 754331 755187 := bstep (se 1 (by rfl) ⟨566390, by rfl⟩ : syracuseStep 755187 = 1132781) B1132781
theorem B1279489 : Blo 754331 1279489 := bstep (se 2 (by rfl) ⟨479808, by rfl⟩ : syracuseStep 1279489 = 959617) B959617
theorem B755203 : Blo 754331 755203 := bstep (se 1 (by rfl) ⟨566402, by rfl⟩ : syracuseStep 755203 = 1132805) B1132805
theorem B755219 : Blo 754331 755219 := bstep (se 1 (by rfl) ⟨566414, by rfl⟩ : syracuseStep 755219 = 1132829) B1132829
theorem B755235 : Blo 754331 755235 := bstep (se 1 (by rfl) ⟨566426, by rfl⟩ : syracuseStep 755235 = 1132853) B1132853
theorem B3638819 : Blo 754331 3638819 := bstep (se 1 (by rfl) ⟨2729114, by rfl⟩ : syracuseStep 3638819 = 5458229) B5458229
theorem B1279523 : Blo 754331 1279523 := bstep (se 1 (by rfl) ⟨959642, by rfl⟩ : syracuseStep 1279523 = 1919285) B1919285
theorem B755251 : Blo 754331 755251 := bstep (se 1 (by rfl) ⟨566438, by rfl⟩ : syracuseStep 755251 = 1132877) B1132877
theorem B755267 : Blo 754331 755267 := bstep (se 1 (by rfl) ⟨566450, by rfl⟩ : syracuseStep 755267 = 1132901) B1132901
theorem B1705553 : Blo 754331 1705553 := bstep (se 2 (by rfl) ⟨639582, by rfl⟩ : syracuseStep 1705553 = 1279165) B1279165
theorem B755283 : Blo 754331 755283 := bstep (se 1 (by rfl) ⟨566462, by rfl⟩ : syracuseStep 755283 = 1132925) B1132925
theorem B755299 : Blo 754331 755299 := bstep (se 1 (by rfl) ⟨566474, by rfl⟩ : syracuseStep 755299 = 1132949) B1132949
theorem B1312355 : Blo 754331 1312355 := bstep (se 1 (by rfl) ⟨984266, by rfl⟩ : syracuseStep 1312355 = 1968533) B1968533
theorem B1705571 : Blo 754331 1705571 := bstep (se 1 (by rfl) ⟨1279178, by rfl⟩ : syracuseStep 1705571 = 2558357) B2558357
theorem B755315 : Blo 754331 755315 := bstep (se 1 (by rfl) ⟨566486, by rfl⟩ : syracuseStep 755315 = 1132973) B1132973
theorem B755331 : Blo 754331 755331 := bstep (se 1 (by rfl) ⟨566498, by rfl⟩ : syracuseStep 755331 = 1132997) B1132997
theorem B755347 : Blo 754331 755347 := bstep (se 1 (by rfl) ⟨566510, by rfl⟩ : syracuseStep 755347 = 1133021) B1133021
theorem B755363 : Blo 754331 755363 := bstep (se 1 (by rfl) ⟨566522, by rfl⟩ : syracuseStep 755363 = 1133045) B1133045
theorem B1279651 : Blo 754331 1279651 := bstep (se 1 (by rfl) ⟨959738, by rfl⟩ : syracuseStep 1279651 = 1919477) B1919477
theorem B2426545 : Blo 754331 2426545 := bstep (se 2 (by rfl) ⟨909954, by rfl⟩ : syracuseStep 2426545 = 1819909) B1819909
theorem B755379 : Blo 754331 755379 := bstep (se 1 (by rfl) ⟨566534, by rfl⟩ : syracuseStep 755379 = 1133069) B1133069
theorem B755395 : Blo 754331 755395 := bstep (se 1 (by rfl) ⟨566546, by rfl⟩ : syracuseStep 755395 = 1133093) B1133093
theorem B755411 : Blo 754331 755411 := bstep (se 1 (by rfl) ⟨566558, by rfl⟩ : syracuseStep 755411 = 1133117) B1133117
theorem B755427 : Blo 754331 755427 := bstep (se 1 (by rfl) ⟨566570, by rfl⟩ : syracuseStep 755427 = 1133141) B1133141
theorem B755443 : Blo 754331 755443 := bstep (se 1 (by rfl) ⟨566582, by rfl⟩ : syracuseStep 755443 = 1133165) B1133165
theorem B1214195 : Blo 754331 1214195 := bstep (se 1 (by rfl) ⟨910646, by rfl⟩ : syracuseStep 1214195 = 1821293) B1821293
theorem B755459 : Blo 754331 755459 := bstep (se 1 (by rfl) ⟨566594, by rfl⟩ : syracuseStep 755459 = 1133189) B1133189
theorem B2557709 : Blo 754331 2557709 := bstep (se 3 (by rfl) ⟨479570, by rfl⟩ : syracuseStep 2557709 = 959141) B959141
theorem B755475 : Blo 754331 755475 := bstep (se 1 (by rfl) ⟨566606, by rfl⟩ : syracuseStep 755475 = 1133213) B1133213
theorem B755491 : Blo 754331 755491 := bstep (se 1 (by rfl) ⟨566618, by rfl⟩ : syracuseStep 755491 = 1133237) B1133237
theorem B755507 : Blo 754331 755507 := bstep (se 1 (by rfl) ⟨566630, by rfl⟩ : syracuseStep 755507 = 1133261) B1133261
theorem B1214273 : Blo 754331 1214273 := bstep (se 2 (by rfl) ⟨455352, by rfl⟩ : syracuseStep 1214273 = 910705) B910705
theorem B755523 : Blo 754331 755523 := bstep (se 1 (by rfl) ⟨566642, by rfl⟩ : syracuseStep 755523 = 1133285) B1133285
theorem B2557763 : Blo 754331 2557763 := bstep (se 1 (by rfl) ⟨1918322, by rfl⟩ : syracuseStep 2557763 = 3836645) B3836645
theorem B755539 : Blo 754331 755539 := bstep (se 1 (by rfl) ⟨566654, by rfl⟩ : syracuseStep 755539 = 1133309) B1133309
theorem B755555 : Blo 754331 755555 := bstep (se 1 (by rfl) ⟨566666, by rfl⟩ : syracuseStep 755555 = 1133333) B1133333
theorem B4097891 : Blo 754331 4097891 := bstep (se 1 (by rfl) ⟨3073418, by rfl⟩ : syracuseStep 4097891 = 6146837) B6146837
theorem B1705841 : Blo 754331 1705841 := bstep (se 2 (by rfl) ⟨639690, by rfl⟩ : syracuseStep 1705841 = 1279381) B1279381
theorem B755571 : Blo 754331 755571 := bstep (se 1 (by rfl) ⟨566678, by rfl⟩ : syracuseStep 755571 = 1133357) B1133357
theorem B1148803 : Blo 754331 1148803 := bstep (se 1 (by rfl) ⟨861602, by rfl⟩ : syracuseStep 1148803 = 1723205) B1723205
theorem B755587 : Blo 754331 755587 := bstep (se 1 (by rfl) ⟨566690, by rfl⟩ : syracuseStep 755587 = 1133381) B1133381
theorem B1705859 : Blo 754331 1705859 := bstep (se 1 (by rfl) ⟨1279394, by rfl⟩ : syracuseStep 1705859 = 2558789) B2558789
theorem B2918285 : Blo 754331 2918285 := bstep (se 3 (by rfl) ⟨547178, by rfl⟩ : syracuseStep 2918285 = 1094357) B1094357
theorem B755603 : Blo 754331 755603 := bstep (se 1 (by rfl) ⟨566702, by rfl⟩ : syracuseStep 755603 = 1133405) B1133405
theorem B755619 : Blo 754331 755619 := bstep (se 1 (by rfl) ⟨566714, by rfl⟩ : syracuseStep 755619 = 1133429) B1133429
theorem B755635 : Blo 754331 755635 := bstep (se 1 (by rfl) ⟨566726, by rfl⟩ : syracuseStep 755635 = 1133453) B1133453
theorem B755651 : Blo 754331 755651 := bstep (se 1 (by rfl) ⟨566738, by rfl⟩ : syracuseStep 755651 = 1133477) B1133477
theorem B755667 : Blo 754331 755667 := bstep (se 1 (by rfl) ⟨566750, by rfl⟩ : syracuseStep 755667 = 1133501) B1133501
theorem B755683 : Blo 754331 755683 := bstep (se 1 (by rfl) ⟨566762, by rfl⟩ : syracuseStep 755683 = 1133525) B1133525
theorem B755699 : Blo 754331 755699 := bstep (se 1 (by rfl) ⟨566774, by rfl⟩ : syracuseStep 755699 = 1133549) B1133549
theorem B755715 : Blo 754331 755715 := bstep (se 1 (by rfl) ⟨566786, by rfl⟩ : syracuseStep 755715 = 1133573) B1133573
theorem B755731 : Blo 754331 755731 := bstep (se 1 (by rfl) ⟨566798, by rfl⟩ : syracuseStep 755731 = 1133597) B1133597
theorem B755747 : Blo 754331 755747 := bstep (se 1 (by rfl) ⟨566810, by rfl⟩ : syracuseStep 755747 = 1133621) B1133621
theorem B755763 : Blo 754331 755763 := bstep (se 1 (by rfl) ⟨566822, by rfl⟩ : syracuseStep 755763 = 1133645) B1133645
theorem B755779 : Blo 754331 755779 := bstep (se 1 (by rfl) ⟨566834, by rfl⟩ : syracuseStep 755779 = 1133669) B1133669
theorem B2558033 : Blo 754331 2558033 := bstep (se 2 (by rfl) ⟨959262, by rfl⟩ : syracuseStep 2558033 = 1918525) B1918525
theorem B755795 : Blo 754331 755795 := bstep (se 1 (by rfl) ⟨566846, by rfl⟩ : syracuseStep 755795 = 1133693) B1133693
theorem B755811 : Blo 754331 755811 := bstep (se 1 (by rfl) ⟨566858, by rfl⟩ : syracuseStep 755811 = 1133717) B1133717
theorem B755827 : Blo 754331 755827 := bstep (se 1 (by rfl) ⟨566870, by rfl⟩ : syracuseStep 755827 = 1133741) B1133741
theorem B755843 : Blo 754331 755843 := bstep (se 1 (by rfl) ⟨566882, by rfl⟩ : syracuseStep 755843 = 1133765) B1133765
theorem B1706129 : Blo 754331 1706129 := bstep (se 2 (by rfl) ⟨639798, by rfl⟩ : syracuseStep 1706129 = 1279597) B1279597
theorem B755859 : Blo 754331 755859 := bstep (se 1 (by rfl) ⟨566894, by rfl⟩ : syracuseStep 755859 = 1133789) B1133789
theorem B755875 : Blo 754331 755875 := bstep (se 1 (by rfl) ⟨566906, by rfl⟩ : syracuseStep 755875 = 1133813) B1133813
theorem B1706147 : Blo 754331 1706147 := bstep (se 1 (by rfl) ⟨1279610, by rfl⟩ : syracuseStep 1706147 = 2559221) B2559221
theorem B755891 : Blo 754331 755891 := bstep (se 1 (by rfl) ⟨566918, by rfl⟩ : syracuseStep 755891 = 1133837) B1133837
theorem B1214657 : Blo 754331 1214657 := bstep (se 2 (by rfl) ⟨455496, by rfl⟩ : syracuseStep 1214657 = 910993) B910993
theorem B755907 : Blo 754331 755907 := bstep (se 1 (by rfl) ⟨566930, by rfl⟩ : syracuseStep 755907 = 1133861) B1133861
theorem B755923 : Blo 754331 755923 := bstep (se 1 (by rfl) ⟨566942, by rfl⟩ : syracuseStep 755923 = 1133885) B1133885
theorem B755939 : Blo 754331 755939 := bstep (se 1 (by rfl) ⟨566954, by rfl⟩ : syracuseStep 755939 = 1133909) B1133909
theorem B755955 : Blo 754331 755955 := bstep (se 1 (by rfl) ⟨566966, by rfl⟩ : syracuseStep 755955 = 1133933) B1133933
theorem B755971 : Blo 754331 755971 := bstep (se 1 (by rfl) ⟨566978, by rfl⟩ : syracuseStep 755971 = 1133957) B1133957
theorem B755987 : Blo 754331 755987 := bstep (se 1 (by rfl) ⟨566990, by rfl⟩ : syracuseStep 755987 = 1133981) B1133981
theorem B756003 : Blo 754331 756003 := bstep (se 1 (by rfl) ⟨567002, by rfl⟩ : syracuseStep 756003 = 1134005) B1134005
theorem B756019 : Blo 754331 756019 := bstep (se 1 (by rfl) ⟨567014, by rfl⟩ : syracuseStep 756019 = 1134029) B1134029
theorem B756035 : Blo 754331 756035 := bstep (se 1 (by rfl) ⟨567026, by rfl⟩ : syracuseStep 756035 = 1134053) B1134053
theorem B756051 : Blo 754331 756051 := bstep (se 1 (by rfl) ⟨567038, by rfl⟩ : syracuseStep 756051 = 1134077) B1134077
theorem B756067 : Blo 754331 756067 := bstep (se 1 (by rfl) ⟨567050, by rfl⟩ : syracuseStep 756067 = 1134101) B1134101
theorem B756083 : Blo 754331 756083 := bstep (se 1 (by rfl) ⟨567062, by rfl⟩ : syracuseStep 756083 = 1134125) B1134125
theorem B756099 : Blo 754331 756099 := bstep (se 1 (by rfl) ⟨567074, by rfl⟩ : syracuseStep 756099 = 1134149) B1134149
theorem B2591117 : Blo 754331 2591117 := bstep (se 3 (by rfl) ⟨485834, by rfl⟩ : syracuseStep 2591117 = 971669) B971669
theorem B756115 : Blo 754331 756115 := bstep (se 1 (by rfl) ⟨567086, by rfl⟩ : syracuseStep 756115 = 1134173) B1134173
theorem B756131 : Blo 754331 756131 := bstep (se 1 (by rfl) ⟨567098, by rfl⟩ : syracuseStep 756131 = 1134197) B1134197
theorem B756147 : Blo 754331 756147 := bstep (se 1 (by rfl) ⟨567110, by rfl⟩ : syracuseStep 756147 = 1134221) B1134221
theorem B756163 : Blo 754331 756163 := bstep (se 1 (by rfl) ⟨567122, by rfl⟩ : syracuseStep 756163 = 1134245) B1134245
theorem B756179 : Blo 754331 756179 := bstep (se 1 (by rfl) ⟨567134, by rfl⟩ : syracuseStep 756179 = 1134269) B1134269
theorem B756195 : Blo 754331 756195 := bstep (se 1 (by rfl) ⟨567146, by rfl⟩ : syracuseStep 756195 = 1134293) B1134293
theorem B756211 : Blo 754331 756211 := bstep (se 1 (by rfl) ⟨567158, by rfl⟩ : syracuseStep 756211 = 1134317) B1134317
theorem B756227 : Blo 754331 756227 := bstep (se 1 (by rfl) ⟨567170, by rfl⟩ : syracuseStep 756227 = 1134341) B1134341
theorem B756243 : Blo 754331 756243 := bstep (se 1 (by rfl) ⟨567182, by rfl⟩ : syracuseStep 756243 = 1134365) B1134365
theorem B756259 : Blo 754331 756259 := bstep (se 1 (by rfl) ⟨567194, by rfl⟩ : syracuseStep 756259 = 1134389) B1134389
theorem B756275 : Blo 754331 756275 := bstep (se 1 (by rfl) ⟨567206, by rfl⟩ : syracuseStep 756275 = 1134413) B1134413
theorem B756291 : Blo 754331 756291 := bstep (se 1 (by rfl) ⟨567218, by rfl⟩ : syracuseStep 756291 = 1134437) B1134437
theorem B756307 : Blo 754331 756307 := bstep (se 1 (by rfl) ⟨567230, by rfl⟩ : syracuseStep 756307 = 1134461) B1134461
theorem B756323 : Blo 754331 756323 := bstep (se 1 (by rfl) ⟨567242, by rfl⟩ : syracuseStep 756323 = 1134485) B1134485
theorem B2558573 : Blo 754331 2558573 := bstep (se 3 (by rfl) ⟨479732, by rfl⟩ : syracuseStep 2558573 = 959465) B959465
theorem B756339 : Blo 754331 756339 := bstep (se 1 (by rfl) ⟨567254, by rfl⟩ : syracuseStep 756339 = 1134509) B1134509
theorem B756355 : Blo 754331 756355 := bstep (se 1 (by rfl) ⟨567266, by rfl⟩ : syracuseStep 756355 = 1134533) B1134533
theorem B756371 : Blo 754331 756371 := bstep (se 1 (by rfl) ⟨567278, by rfl⟩ : syracuseStep 756371 = 1134557) B1134557
theorem B756387 : Blo 754331 756387 := bstep (se 1 (by rfl) ⟨567290, by rfl⟩ : syracuseStep 756387 = 1134581) B1134581
theorem B2558627 : Blo 754331 2558627 := bstep (se 1 (by rfl) ⟨1918970, by rfl⟩ : syracuseStep 2558627 = 3837941) B3837941
theorem B756403 : Blo 754331 756403 := bstep (se 1 (by rfl) ⟨567302, by rfl⟩ : syracuseStep 756403 = 1134605) B1134605
theorem B756419 : Blo 754331 756419 := bstep (se 1 (by rfl) ⟨567314, by rfl⟩ : syracuseStep 756419 = 1134629) B1134629
theorem B756435 : Blo 754331 756435 := bstep (se 1 (by rfl) ⟨567326, by rfl⟩ : syracuseStep 756435 = 1134653) B1134653
theorem B756451 : Blo 754331 756451 := bstep (se 1 (by rfl) ⟨567338, by rfl⟩ : syracuseStep 756451 = 1134677) B1134677
theorem B3640049 : Blo 754331 3640049 := bstep (se 2 (by rfl) ⟨1365018, by rfl⟩ : syracuseStep 3640049 = 2730037) B2730037
theorem B756467 : Blo 754331 756467 := bstep (se 1 (by rfl) ⟨567350, by rfl⟩ : syracuseStep 756467 = 1134701) B1134701
theorem B756483 : Blo 754331 756483 := bstep (se 1 (by rfl) ⟨567362, by rfl⟩ : syracuseStep 756483 = 1134725) B1134725
theorem B5737229 : Blo 754331 5737229 := bstep (se 3 (by rfl) ⟨1075730, by rfl⟩ : syracuseStep 5737229 = 2151461) B2151461
theorem B2427661 : Blo 754331 2427661 := bstep (se 3 (by rfl) ⟨455186, by rfl⟩ : syracuseStep 2427661 = 910373) B910373
theorem B756499 : Blo 754331 756499 := bstep (se 1 (by rfl) ⟨567374, by rfl⟩ : syracuseStep 756499 = 1134749) B1134749
theorem B756515 : Blo 754331 756515 := bstep (se 1 (by rfl) ⟨567386, by rfl⟩ : syracuseStep 756515 = 1134773) B1134773
theorem B756531 : Blo 754331 756531 := bstep (se 1 (by rfl) ⟨567398, by rfl⟩ : syracuseStep 756531 = 1134797) B1134797
theorem B756547 : Blo 754331 756547 := bstep (se 1 (by rfl) ⟨567410, by rfl⟩ : syracuseStep 756547 = 1134821) B1134821
theorem B2427725 : Blo 754331 2427725 := bstep (se 3 (by rfl) ⟨455198, by rfl⟩ : syracuseStep 2427725 = 910397) B910397
theorem B756563 : Blo 754331 756563 := bstep (se 1 (by rfl) ⟨567422, by rfl⟩ : syracuseStep 756563 = 1134845) B1134845
theorem B756579 : Blo 754331 756579 := bstep (se 1 (by rfl) ⟨567434, by rfl⟩ : syracuseStep 756579 = 1134869) B1134869
theorem B756595 : Blo 754331 756595 := bstep (se 1 (by rfl) ⟨567446, by rfl⟩ : syracuseStep 756595 = 1134893) B1134893
theorem B756611 : Blo 754331 756611 := bstep (se 1 (by rfl) ⟨567458, by rfl⟩ : syracuseStep 756611 = 1134917) B1134917
theorem B756627 : Blo 754331 756627 := bstep (se 1 (by rfl) ⟨567470, by rfl⟩ : syracuseStep 756627 = 1134941) B1134941
theorem B756643 : Blo 754331 756643 := bstep (se 1 (by rfl) ⟨567482, by rfl⟩ : syracuseStep 756643 = 1134965) B1134965
theorem B2558897 : Blo 754331 2558897 := bstep (se 2 (by rfl) ⟨959586, by rfl⟩ : syracuseStep 2558897 = 1919173) B1919173
theorem B756659 : Blo 754331 756659 := bstep (se 1 (by rfl) ⟨567494, by rfl⟩ : syracuseStep 756659 = 1134989) B1134989
theorem B756675 : Blo 754331 756675 := bstep (se 1 (by rfl) ⟨567506, by rfl⟩ : syracuseStep 756675 = 1135013) B1135013
theorem B756691 : Blo 754331 756691 := bstep (se 1 (by rfl) ⟨567518, by rfl⟩ : syracuseStep 756691 = 1135037) B1135037
theorem B756707 : Blo 754331 756707 := bstep (se 1 (by rfl) ⟨567530, by rfl⟩ : syracuseStep 756707 = 1135061) B1135061
theorem B756723 : Blo 754331 756723 := bstep (se 1 (by rfl) ⟨567542, by rfl⟩ : syracuseStep 756723 = 1135085) B1135085
theorem B756739 : Blo 754331 756739 := bstep (se 1 (by rfl) ⟨567554, by rfl⟩ : syracuseStep 756739 = 1135109) B1135109
theorem B756755 : Blo 754331 756755 := bstep (se 1 (by rfl) ⟨567566, by rfl⟩ : syracuseStep 756755 = 1135133) B1135133
theorem B756771 : Blo 754331 756771 := bstep (se 1 (by rfl) ⟨567578, by rfl⟩ : syracuseStep 756771 = 1135157) B1135157
theorem B756787 : Blo 754331 756787 := bstep (se 1 (by rfl) ⟨567590, by rfl⟩ : syracuseStep 756787 = 1135181) B1135181
theorem B756803 : Blo 754331 756803 := bstep (se 1 (by rfl) ⟨567602, by rfl⟩ : syracuseStep 756803 = 1135205) B1135205
theorem B756819 : Blo 754331 756819 := bstep (se 1 (by rfl) ⟨567614, by rfl⟩ : syracuseStep 756819 = 1135229) B1135229
theorem B5442659 : Blo 754331 5442659 := bstep (se 1 (by rfl) ⟨4081994, by rfl⟩ : syracuseStep 5442659 = 8163989) B8163989
theorem B1150051 : Blo 754331 1150051 := bstep (se 1 (by rfl) ⟨862538, by rfl⟩ : syracuseStep 1150051 = 1725077) B1725077
theorem B756835 : Blo 754331 756835 := bstep (se 1 (by rfl) ⟨567626, by rfl⟩ : syracuseStep 756835 = 1135253) B1135253
theorem B756851 : Blo 754331 756851 := bstep (se 1 (by rfl) ⟨567638, by rfl⟩ : syracuseStep 756851 = 1135277) B1135277
theorem B756867 : Blo 754331 756867 := bstep (se 1 (by rfl) ⟨567650, by rfl⟩ : syracuseStep 756867 = 1135301) B1135301
theorem B756883 : Blo 754331 756883 := bstep (se 1 (by rfl) ⟨567662, by rfl⟩ : syracuseStep 756883 = 1135325) B1135325
theorem B756899 : Blo 754331 756899 := bstep (se 1 (by rfl) ⟨567674, by rfl⟩ : syracuseStep 756899 = 1135349) B1135349
theorem B756915 : Blo 754331 756915 := bstep (se 1 (by rfl) ⟨567686, by rfl⟩ : syracuseStep 756915 = 1135373) B1135373
theorem B756931 : Blo 754331 756931 := bstep (se 1 (by rfl) ⟨567698, by rfl⟩ : syracuseStep 756931 = 1135397) B1135397
theorem B756947 : Blo 754331 756947 := bstep (se 1 (by rfl) ⟨567710, by rfl⟩ : syracuseStep 756947 = 1135421) B1135421
theorem B756963 : Blo 754331 756963 := bstep (se 1 (by rfl) ⟨567722, by rfl⟩ : syracuseStep 756963 = 1135445) B1135445
theorem B756979 : Blo 754331 756979 := bstep (se 1 (by rfl) ⟨567734, by rfl⟩ : syracuseStep 756979 = 1135469) B1135469
theorem B756995 : Blo 754331 756995 := bstep (se 1 (by rfl) ⟨567746, by rfl⟩ : syracuseStep 756995 = 1135493) B1135493
theorem B757011 : Blo 754331 757011 := bstep (se 1 (by rfl) ⟨567758, by rfl⟩ : syracuseStep 757011 = 1135517) B1135517
theorem B757027 : Blo 754331 757027 := bstep (se 1 (by rfl) ⟨567770, by rfl⟩ : syracuseStep 757027 = 1135541) B1135541
theorem B757043 : Blo 754331 757043 := bstep (se 1 (by rfl) ⟨567782, by rfl⟩ : syracuseStep 757043 = 1135565) B1135565
theorem B757059 : Blo 754331 757059 := bstep (se 1 (by rfl) ⟨567794, by rfl⟩ : syracuseStep 757059 = 1135589) B1135589
theorem B757075 : Blo 754331 757075 := bstep (se 1 (by rfl) ⟨567806, by rfl⟩ : syracuseStep 757075 = 1135613) B1135613
theorem B757091 : Blo 754331 757091 := bstep (se 1 (by rfl) ⟨567818, by rfl⟩ : syracuseStep 757091 = 1135637) B1135637
theorem B757107 : Blo 754331 757107 := bstep (se 1 (by rfl) ⟨567830, by rfl⟩ : syracuseStep 757107 = 1135661) B1135661
theorem B757123 : Blo 754331 757123 := bstep (se 1 (by rfl) ⟨567842, by rfl⟩ : syracuseStep 757123 = 1135685) B1135685
theorem B757139 : Blo 754331 757139 := bstep (se 1 (by rfl) ⟨567854, by rfl⟩ : syracuseStep 757139 = 1135709) B1135709
theorem B757155 : Blo 754331 757155 := bstep (se 1 (by rfl) ⟨567866, by rfl⟩ : syracuseStep 757155 = 1135733) B1135733
theorem B757171 : Blo 754331 757171 := bstep (se 1 (by rfl) ⟨567878, by rfl⟩ : syracuseStep 757171 = 1135757) B1135757
theorem B757187 : Blo 754331 757187 := bstep (se 1 (by rfl) ⟨567890, by rfl⟩ : syracuseStep 757187 = 1135781) B1135781
theorem B757203 : Blo 754331 757203 := bstep (se 1 (by rfl) ⟨567902, by rfl⟩ : syracuseStep 757203 = 1135805) B1135805
theorem B757219 : Blo 754331 757219 := bstep (se 1 (by rfl) ⟨567914, by rfl⟩ : syracuseStep 757219 = 1135829) B1135829
theorem B757235 : Blo 754331 757235 := bstep (se 1 (by rfl) ⟨567926, by rfl⟩ : syracuseStep 757235 = 1135853) B1135853
theorem B757251 : Blo 754331 757251 := bstep (se 1 (by rfl) ⟨567938, by rfl⟩ : syracuseStep 757251 = 1135877) B1135877
theorem B757267 : Blo 754331 757267 := bstep (se 1 (by rfl) ⟨567950, by rfl⟩ : syracuseStep 757267 = 1135901) B1135901
theorem B757283 : Blo 754331 757283 := bstep (se 1 (by rfl) ⟨567962, by rfl⟩ : syracuseStep 757283 = 1135925) B1135925
theorem B757299 : Blo 754331 757299 := bstep (se 1 (by rfl) ⟨567974, by rfl⟩ : syracuseStep 757299 = 1135949) B1135949
theorem B757315 : Blo 754331 757315 := bstep (se 1 (by rfl) ⟨567986, by rfl⟩ : syracuseStep 757315 = 1135973) B1135973
theorem B757331 : Blo 754331 757331 := bstep (se 1 (by rfl) ⟨567998, by rfl⟩ : syracuseStep 757331 = 1135997) B1135997
theorem B757347 : Blo 754331 757347 := bstep (se 1 (by rfl) ⟨568010, by rfl⟩ : syracuseStep 757347 = 1136021) B1136021
theorem B757363 : Blo 754331 757363 := bstep (se 1 (by rfl) ⟨568022, by rfl⟩ : syracuseStep 757363 = 1136045) B1136045
theorem B757379 : Blo 754331 757379 := bstep (se 1 (by rfl) ⟨568034, by rfl⟩ : syracuseStep 757379 = 1136069) B1136069
theorem B757395 : Blo 754331 757395 := bstep (se 1 (by rfl) ⟨568046, by rfl⟩ : syracuseStep 757395 = 1136093) B1136093
theorem B757411 : Blo 754331 757411 := bstep (se 1 (by rfl) ⟨568058, by rfl⟩ : syracuseStep 757411 = 1136117) B1136117
theorem B3837617 : Blo 754331 3837617 := bstep (se 2 (by rfl) ⟨1439106, by rfl⟩ : syracuseStep 3837617 = 2878213) B2878213
theorem B757427 : Blo 754331 757427 := bstep (se 1 (by rfl) ⟨568070, by rfl⟩ : syracuseStep 757427 = 1136141) B1136141
theorem B757443 : Blo 754331 757443 := bstep (se 1 (by rfl) ⟨568082, by rfl⟩ : syracuseStep 757443 = 1136165) B1136165
theorem B757459 : Blo 754331 757459 := bstep (se 1 (by rfl) ⟨568094, by rfl⟩ : syracuseStep 757459 = 1136189) B1136189
theorem B757475 : Blo 754331 757475 := bstep (se 1 (by rfl) ⟨568106, by rfl⟩ : syracuseStep 757475 = 1136213) B1136213
theorem B757491 : Blo 754331 757491 := bstep (se 1 (by rfl) ⟨568118, by rfl⟩ : syracuseStep 757491 = 1136237) B1136237
theorem B757507 : Blo 754331 757507 := bstep (se 1 (by rfl) ⟨568130, by rfl⟩ : syracuseStep 757507 = 1136261) B1136261
theorem B757523 : Blo 754331 757523 := bstep (se 1 (by rfl) ⟨568142, by rfl⟩ : syracuseStep 757523 = 1136285) B1136285
theorem B757539 : Blo 754331 757539 := bstep (se 1 (by rfl) ⟨568154, by rfl⟩ : syracuseStep 757539 = 1136309) B1136309
theorem B757555 : Blo 754331 757555 := bstep (se 1 (by rfl) ⟨568166, by rfl⟩ : syracuseStep 757555 = 1136333) B1136333
theorem B2330435 : Blo 754331 2330435 := bstep (se 1 (by rfl) ⟨1747826, by rfl⟩ : syracuseStep 2330435 = 3495653) B3495653
theorem B757571 : Blo 754331 757571 := bstep (se 1 (by rfl) ⟨568178, by rfl⟩ : syracuseStep 757571 = 1136357) B1136357
theorem B757587 : Blo 754331 757587 := bstep (se 1 (by rfl) ⟨568190, by rfl⟩ : syracuseStep 757587 = 1136381) B1136381
theorem B757603 : Blo 754331 757603 := bstep (se 1 (by rfl) ⟨568202, by rfl⟩ : syracuseStep 757603 = 1136405) B1136405
theorem B757619 : Blo 754331 757619 := bstep (se 1 (by rfl) ⟨568214, by rfl⟩ : syracuseStep 757619 = 1136429) B1136429
theorem B757635 : Blo 754331 757635 := bstep (se 1 (by rfl) ⟨568226, by rfl⟩ : syracuseStep 757635 = 1136453) B1136453
theorem B757651 : Blo 754331 757651 := bstep (se 1 (by rfl) ⟨568238, by rfl⟩ : syracuseStep 757651 = 1136477) B1136477
theorem B757667 : Blo 754331 757667 := bstep (se 1 (by rfl) ⟨568250, by rfl⟩ : syracuseStep 757667 = 1136501) B1136501
theorem B757683 : Blo 754331 757683 := bstep (se 1 (by rfl) ⟨568262, by rfl⟩ : syracuseStep 757683 = 1136525) B1136525
theorem B757699 : Blo 754331 757699 := bstep (se 1 (by rfl) ⟨568274, by rfl⟩ : syracuseStep 757699 = 1136549) B1136549
theorem B757715 : Blo 754331 757715 := bstep (se 1 (by rfl) ⟨568286, by rfl⟩ : syracuseStep 757715 = 1136573) B1136573
theorem B757731 : Blo 754331 757731 := bstep (se 1 (by rfl) ⟨568298, by rfl⟩ : syracuseStep 757731 = 1136597) B1136597
theorem B757747 : Blo 754331 757747 := bstep (se 1 (by rfl) ⟨568310, by rfl⟩ : syracuseStep 757747 = 1136621) B1136621
theorem B757763 : Blo 754331 757763 := bstep (se 1 (by rfl) ⟨568322, by rfl⟩ : syracuseStep 757763 = 1136645) B1136645
theorem B757779 : Blo 754331 757779 := bstep (se 1 (by rfl) ⟨568334, by rfl⟩ : syracuseStep 757779 = 1136669) B1136669
theorem B757795 : Blo 754331 757795 := bstep (se 1 (by rfl) ⟨568346, by rfl⟩ : syracuseStep 757795 = 1136693) B1136693
theorem B757811 : Blo 754331 757811 := bstep (se 1 (by rfl) ⟨568358, by rfl⟩ : syracuseStep 757811 = 1136717) B1136717
theorem B757827 : Blo 754331 757827 := bstep (se 1 (by rfl) ⟨568370, by rfl⟩ : syracuseStep 757827 = 1136741) B1136741
theorem B757843 : Blo 754331 757843 := bstep (se 1 (by rfl) ⟨568382, by rfl⟩ : syracuseStep 757843 = 1136765) B1136765
theorem B757859 : Blo 754331 757859 := bstep (se 1 (by rfl) ⟨568394, by rfl⟩ : syracuseStep 757859 = 1136789) B1136789
theorem B2592881 : Blo 754331 2592881 := bstep (se 2 (by rfl) ⟨972330, by rfl⟩ : syracuseStep 2592881 = 1944661) B1944661
theorem B757875 : Blo 754331 757875 := bstep (se 1 (by rfl) ⟨568406, by rfl⟩ : syracuseStep 757875 = 1136813) B1136813
theorem B757891 : Blo 754331 757891 := bstep (se 1 (by rfl) ⟨568418, by rfl⟩ : syracuseStep 757891 = 1136837) B1136837
theorem B757907 : Blo 754331 757907 := bstep (se 1 (by rfl) ⟨568430, by rfl⟩ : syracuseStep 757907 = 1136861) B1136861
theorem B757923 : Blo 754331 757923 := bstep (se 1 (by rfl) ⟨568442, by rfl⟩ : syracuseStep 757923 = 1136885) B1136885
theorem B757939 : Blo 754331 757939 := bstep (se 1 (by rfl) ⟨568454, by rfl⟩ : syracuseStep 757939 = 1136909) B1136909
theorem B757955 : Blo 754331 757955 := bstep (se 1 (by rfl) ⟨568466, by rfl⟩ : syracuseStep 757955 = 1136933) B1136933
theorem B757971 : Blo 754331 757971 := bstep (se 1 (by rfl) ⟨568478, by rfl⟩ : syracuseStep 757971 = 1136957) B1136957
theorem B757987 : Blo 754331 757987 := bstep (se 1 (by rfl) ⟨568490, by rfl⟩ : syracuseStep 757987 = 1136981) B1136981
theorem B758003 : Blo 754331 758003 := bstep (se 1 (by rfl) ⟨568502, by rfl⟩ : syracuseStep 758003 = 1137005) B1137005
theorem B758019 : Blo 754331 758019 := bstep (se 1 (by rfl) ⟨568514, by rfl⟩ : syracuseStep 758019 = 1137029) B1137029
theorem B758035 : Blo 754331 758035 := bstep (se 1 (by rfl) ⟨568526, by rfl⟩ : syracuseStep 758035 = 1137053) B1137053
theorem B758051 : Blo 754331 758051 := bstep (se 1 (by rfl) ⟨568538, by rfl⟩ : syracuseStep 758051 = 1137077) B1137077
theorem B758067 : Blo 754331 758067 := bstep (se 1 (by rfl) ⟨568550, by rfl⟩ : syracuseStep 758067 = 1137101) B1137101
theorem B758083 : Blo 754331 758083 := bstep (se 1 (by rfl) ⟨568562, by rfl⟩ : syracuseStep 758083 = 1137125) B1137125
theorem B758099 : Blo 754331 758099 := bstep (se 1 (by rfl) ⟨568574, by rfl⟩ : syracuseStep 758099 = 1137149) B1137149
theorem B758115 : Blo 754331 758115 := bstep (se 1 (by rfl) ⟨568586, by rfl⟩ : syracuseStep 758115 = 1137173) B1137173
theorem B758131 : Blo 754331 758131 := bstep (se 1 (by rfl) ⟨568598, by rfl⟩ : syracuseStep 758131 = 1137197) B1137197
theorem B758147 : Blo 754331 758147 := bstep (se 1 (by rfl) ⟨568610, by rfl⟩ : syracuseStep 758147 = 1137221) B1137221
theorem B758163 : Blo 754331 758163 := bstep (se 1 (by rfl) ⟨568622, by rfl⟩ : syracuseStep 758163 = 1137245) B1137245
theorem B758179 : Blo 754331 758179 := bstep (se 1 (by rfl) ⟨568634, by rfl⟩ : syracuseStep 758179 = 1137269) B1137269
theorem B758195 : Blo 754331 758195 := bstep (se 1 (by rfl) ⟨568646, by rfl⟩ : syracuseStep 758195 = 1137293) B1137293
theorem B758211 : Blo 754331 758211 := bstep (se 1 (by rfl) ⟨568658, by rfl⟩ : syracuseStep 758211 = 1137317) B1137317
theorem B1151443 : Blo 754331 1151443 := bstep (se 1 (by rfl) ⟨863582, by rfl⟩ : syracuseStep 1151443 = 1727165) B1727165
theorem B758227 : Blo 754331 758227 := bstep (se 1 (by rfl) ⟨568670, by rfl⟩ : syracuseStep 758227 = 1137341) B1137341
theorem B758243 : Blo 754331 758243 := bstep (se 1 (by rfl) ⟨568682, by rfl⟩ : syracuseStep 758243 = 1137365) B1137365
theorem B758259 : Blo 754331 758259 := bstep (se 1 (by rfl) ⟨568694, by rfl⟩ : syracuseStep 758259 = 1137389) B1137389
theorem B758275 : Blo 754331 758275 := bstep (se 1 (by rfl) ⟨568706, by rfl⟩ : syracuseStep 758275 = 1137413) B1137413
theorem B2298385 : Blo 754331 2298385 := bstep (se 2 (by rfl) ⟨861894, by rfl⟩ : syracuseStep 2298385 = 1723789) B1723789
theorem B758291 : Blo 754331 758291 := bstep (se 1 (by rfl) ⟨568718, by rfl⟩ : syracuseStep 758291 = 1137437) B1137437
theorem B758307 : Blo 754331 758307 := bstep (se 1 (by rfl) ⟨568730, by rfl⟩ : syracuseStep 758307 = 1137461) B1137461
theorem B758323 : Blo 754331 758323 := bstep (se 1 (by rfl) ⟨568742, by rfl⟩ : syracuseStep 758323 = 1137485) B1137485
theorem B955091 : Blo 754331 955091 := bstep (se 1 (by rfl) ⟨716318, by rfl⟩ : syracuseStep 955091 = 1432637) B1432637
theorem B3642509 : Blo 754331 3642509 := bstep (se 3 (by rfl) ⟨682970, by rfl⟩ : syracuseStep 3642509 = 1365941) B1365941
theorem B2299043 : Blo 754331 2299043 := bstep (se 1 (by rfl) ⟨1724282, by rfl⟩ : syracuseStep 2299043 = 3448565) B3448565
theorem B3314915 : Blo 754331 3314915 := bstep (se 1 (by rfl) ⟨2486186, by rfl⟩ : syracuseStep 3314915 = 4972373) B4972373
theorem B955795 : Blo 754331 955795 := bstep (se 1 (by rfl) ⟨716846, by rfl⟩ : syracuseStep 955795 = 1433693) B1433693
theorem B955891 : Blo 754331 955891 := bstep (se 1 (by rfl) ⟨716918, by rfl⟩ : syracuseStep 955891 = 1433837) B1433837
theorem B5740145 : Blo 754331 5740145 := bstep (se 2 (by rfl) ⟨2152554, by rfl⟩ : syracuseStep 5740145 = 4305109) B4305109
theorem B1611409 : Blo 754331 1611409 := bstep (se 2 (by rfl) ⟨604278, by rfl⟩ : syracuseStep 1611409 = 1208557) B1208557
theorem B1611427 : Blo 754331 1611427 := bstep (se 1 (by rfl) ⟨1208570, by rfl⟩ : syracuseStep 1611427 = 2417141) B2417141
theorem B10327733 : Blo 754331 10327733 := bstep (se 5 (by rfl) ⟨484112, by rfl⟩ : syracuseStep 10327733 = 968225) B968225
theorem B12916421 : Blo 754331 12916421 := bstep (se 4 (by rfl) ⟨1210914, by rfl⟩ : syracuseStep 12916421 = 2421829) B2421829
theorem B3446705 : Blo 754331 3446705 := bstep (se 2 (by rfl) ⟨1292514, by rfl⟩ : syracuseStep 3446705 = 2585029) B2585029
theorem B24549317 : Blo 754331 24549317 := bstep (se 4 (by rfl) ⟨2301498, by rfl⟩ : syracuseStep 24549317 = 4602997) B4602997
theorem B8624069 : Blo 754331 8624069 := bstep (se 4 (by rfl) ⟨808506, by rfl⟩ : syracuseStep 8624069 = 1617013) B1617013
theorem B956387 : Blo 754331 956387 := bstep (se 1 (by rfl) ⟨717290, by rfl⟩ : syracuseStep 956387 = 1434581) B1434581
theorem B1021969 : Blo 754331 1021969 := bstep (se 2 (by rfl) ⟨383238, by rfl⟩ : syracuseStep 1021969 = 766477) B766477
theorem B2758691 : Blo 754331 2758691 := bstep (se 1 (by rfl) ⟨2069018, by rfl⟩ : syracuseStep 2758691 = 4138037) B4138037
theorem B8198243 : Blo 754331 8198243 := bstep (se 1 (by rfl) ⟨6148682, by rfl⟩ : syracuseStep 8198243 = 12297365) B12297365
theorem B3872881 : Blo 754331 3872881 := bstep (se 2 (by rfl) ⟨1452330, by rfl⟩ : syracuseStep 3872881 = 2904661) B2904661
theorem B3447089 : Blo 754331 3447089 := bstep (se 2 (by rfl) ⟨1292658, by rfl⟩ : syracuseStep 3447089 = 2585317) B2585317
theorem B6461765 : Blo 754331 6461765 := bstep (se 4 (by rfl) ⟨605790, by rfl⟩ : syracuseStep 6461765 = 1211581) B1211581
theorem B4299277 : Blo 754331 4299277 := bstep (se 3 (by rfl) ⟨806114, by rfl⟩ : syracuseStep 4299277 = 1612229) B1612229
theorem B957091 : Blo 754331 957091 := bstep (se 1 (by rfl) ⟨717818, by rfl⟩ : syracuseStep 957091 = 1435637) B1435637
theorem B957187 : Blo 754331 957187 := bstep (se 1 (by rfl) ⟨717890, by rfl⟩ : syracuseStep 957187 = 1435781) B1435781
theorem B4922117 : Blo 754331 4922117 := bstep (se 4 (by rfl) ⟨461448, by rfl⟩ : syracuseStep 4922117 = 922897) B922897
theorem B31562693 : Blo 754331 31562693 := bstep (se 4 (by rfl) ⟨2959002, by rfl⟩ : syracuseStep 31562693 = 5918005) B5918005
theorem B6462449 : Blo 754331 6462449 := bstep (se 2 (by rfl) ⟨2423418, by rfl⟩ : syracuseStep 6462449 = 4846837) B4846837
theorem B1023089 : Blo 754331 1023089 := bstep (se 2 (by rfl) ⟨383658, by rfl⟩ : syracuseStep 1023089 = 767317) B767317
theorem B5250275 : Blo 754331 5250275 := bstep (se 1 (by rfl) ⟨3937706, by rfl⟩ : syracuseStep 5250275 = 7875413) B7875413
theorem B957683 : Blo 754331 957683 := bstep (se 1 (by rfl) ⟨718262, by rfl⟩ : syracuseStep 957683 = 1436525) B1436525
theorem B10329443 : Blo 754331 10329443 := bstep (se 1 (by rfl) ⟨7747082, by rfl⟩ : syracuseStep 10329443 = 15494165) B15494165
theorem B2039203 : Blo 754331 2039203 := bstep (se 1 (by rfl) ⟨1529402, by rfl⟩ : syracuseStep 2039203 = 3058805) B3058805
theorem B9182645 : Blo 754331 9182645 := bstep (se 5 (by rfl) ⟨430436, by rfl⟩ : syracuseStep 9182645 = 860873) B860873
theorem B2039267 : Blo 754331 2039267 := bstep (se 1 (by rfl) ⟨1529450, by rfl⟩ : syracuseStep 2039267 = 3058901) B3058901
theorem B2301571 : Blo 754331 2301571 := bstep (se 1 (by rfl) ⟨1726178, by rfl⟩ : syracuseStep 2301571 = 3452357) B3452357
theorem B4595555 : Blo 754331 4595555 := bstep (se 1 (by rfl) ⟨3446666, by rfl⟩ : syracuseStep 4595555 = 6893333) B6893333
theorem B9707363 : Blo 754331 9707363 := bstep (se 1 (by rfl) ⟨7280522, by rfl⟩ : syracuseStep 9707363 = 14561045) B14561045
theorem B1613699 : Blo 754331 1613699 := bstep (se 1 (by rfl) ⟨1210274, by rfl⟩ : syracuseStep 1613699 = 2420549) B2420549
theorem B958387 : Blo 754331 958387 := bstep (se 1 (by rfl) ⟨718790, by rfl⟩ : syracuseStep 958387 = 1437581) B1437581
theorem B958483 : Blo 754331 958483 := bstep (se 1 (by rfl) ⟨718862, by rfl⟩ : syracuseStep 958483 = 1437725) B1437725
theorem B2039917 : Blo 754331 2039917 := bstep (se 3 (by rfl) ⟨382484, by rfl⟩ : syracuseStep 2039917 = 764969) B764969
theorem B1614161 : Blo 754331 1614161 := bstep (se 2 (by rfl) ⟨605310, by rfl⟩ : syracuseStep 1614161 = 1210621) B1210621
theorem B2040241 : Blo 754331 2040241 := bstep (se 2 (by rfl) ⟨765090, by rfl⟩ : syracuseStep 2040241 = 1530181) B1530181
theorem B1024435 : Blo 754331 1024435 := bstep (se 1 (by rfl) ⟨768326, by rfl⟩ : syracuseStep 1024435 = 1536653) B1536653
theorem B4301261 : Blo 754331 4301261 := bstep (se 3 (by rfl) ⟨806486, by rfl⟩ : syracuseStep 4301261 = 1612973) B1612973
theorem B958979 : Blo 754331 958979 := bstep (se 1 (by rfl) ⟨719234, by rfl⟩ : syracuseStep 958979 = 1438469) B1438469
theorem B1090081 : Blo 754331 1090081 := bstep (se 2 (by rfl) ⟨408780, by rfl⟩ : syracuseStep 1090081 = 817561) B817561
theorem B7250573 : Blo 754331 7250573 := bstep (se 3 (by rfl) ⟨1359482, by rfl⟩ : syracuseStep 7250573 = 2718965) B2718965
theorem B6628067 : Blo 754331 6628067 := bstep (se 1 (by rfl) ⟨4971050, by rfl⟩ : syracuseStep 6628067 = 9942101) B9942101
theorem B1909777 : Blo 754331 1909777 := bstep (se 2 (by rfl) ⟨716166, by rfl⟩ : syracuseStep 1909777 = 1432333) B1432333
theorem B959683 : Blo 754331 959683 := bstep (se 1 (by rfl) ⟨719762, by rfl⟩ : syracuseStep 959683 = 1439525) B1439525
theorem B1910051 : Blo 754331 1910051 := bstep (se 1 (by rfl) ⟨1432538, by rfl⟩ : syracuseStep 1910051 = 2865077) B2865077
theorem B4302193 : Blo 754331 4302193 := bstep (se 2 (by rfl) ⟨1613322, by rfl⟩ : syracuseStep 4302193 = 3226645) B3226645
theorem B1910243 : Blo 754331 1910243 := bstep (se 1 (by rfl) ⟨1432682, by rfl⟩ : syracuseStep 1910243 = 2865365) B2865365
theorem B1615459 : Blo 754331 1615459 := bstep (se 1 (by rfl) ⟨1211594, by rfl⟩ : syracuseStep 1615459 = 2423189) B2423189
theorem B1615715 : Blo 754331 1615715 := bstep (se 1 (by rfl) ⟨1211786, by rfl⟩ : syracuseStep 1615715 = 2423573) B2423573
theorem B1943473 : Blo 754331 1943473 := bstep (se 2 (by rfl) ⟨728802, by rfl⟩ : syracuseStep 1943473 = 1457605) B1457605
theorem B1812451 : Blo 754331 1812451 := bstep (se 1 (by rfl) ⟨1359338, by rfl⟩ : syracuseStep 1812451 = 2718677) B2718677
theorem B20719637 : Blo 754331 20719637 := bstep (se 6 (by rfl) ⟨485616, by rfl⟩ : syracuseStep 20719637 = 971233) B971233
theorem B4368653 : Blo 754331 4368653 := bstep (se 3 (by rfl) ⟨819122, by rfl⟩ : syracuseStep 4368653 = 1638245) B1638245
theorem B862579 : Blo 754331 862579 := bstep (se 1 (by rfl) ⟨646934, by rfl⟩ : syracuseStep 862579 = 1293869) B1293869
theorem B1911185 : Blo 754331 1911185 := bstep (se 2 (by rfl) ⟨716694, by rfl⟩ : syracuseStep 1911185 = 1433389) B1433389
theorem B1911235 : Blo 754331 1911235 := bstep (se 1 (by rfl) ⟨1433426, by rfl⟩ : syracuseStep 1911235 = 2866853) B2866853
theorem B2042381 : Blo 754331 2042381 := bstep (se 3 (by rfl) ⟨382946, by rfl⟩ : syracuseStep 2042381 = 765893) B765893
theorem B1911377 : Blo 754331 1911377 := bstep (se 2 (by rfl) ⟨716766, by rfl⟩ : syracuseStep 1911377 = 1433533) B1433533
theorem B4303651 : Blo 754331 4303651 := bstep (se 1 (by rfl) ⟨3227738, by rfl⟩ : syracuseStep 4303651 = 6455477) B6455477
theorem B1616689 : Blo 754331 1616689 := bstep (se 2 (by rfl) ⟨606258, by rfl⟩ : syracuseStep 1616689 = 1212517) B1212517
theorem B2304931 : Blo 754331 2304931 := bstep (se 1 (by rfl) ⟨1728698, by rfl⟩ : syracuseStep 2304931 = 3457397) B3457397
theorem B1813681 : Blo 754331 1813681 := bstep (se 2 (by rfl) ⟨680130, by rfl⟩ : syracuseStep 1813681 = 1360261) B1360261
theorem B7351523 : Blo 754331 7351523 := bstep (se 1 (by rfl) ⟨5513642, by rfl⟩ : syracuseStep 7351523 = 11027285) B11027285
theorem B4304177 : Blo 754331 4304177 := bstep (se 2 (by rfl) ⟨1614066, by rfl⟩ : syracuseStep 4304177 = 3228133) B3228133
theorem B4369763 : Blo 754331 4369763 := bstep (se 1 (by rfl) ⟨3277322, by rfl⟩ : syracuseStep 4369763 = 6554645) B6554645
theorem B1617347 : Blo 754331 1617347 := bstep (se 1 (by rfl) ⟨1213010, by rfl⟩ : syracuseStep 1617347 = 2426021) B2426021
theorem B6139405 : Blo 754331 6139405 := bstep (se 3 (by rfl) ⟨1151138, by rfl⟩ : syracuseStep 6139405 = 2302277) B2302277
theorem B1912369 : Blo 754331 1912369 := bstep (se 2 (by rfl) ⟨717138, by rfl⟩ : syracuseStep 1912369 = 1434277) B1434277
theorem B8629901 : Blo 754331 8629901 := bstep (se 3 (by rfl) ⟨1618106, by rfl⟩ : syracuseStep 8629901 = 3236213) B3236213
theorem B765763 : Blo 754331 765763 := bstep (se 1 (by rfl) ⟨574322, by rfl⟩ : syracuseStep 765763 = 1148645) B1148645
theorem B1912643 : Blo 754331 1912643 := bstep (se 1 (by rfl) ⟨1434482, by rfl⟩ : syracuseStep 1912643 = 2868965) B2868965
theorem B1912835 : Blo 754331 1912835 := bstep (se 1 (by rfl) ⟨1434626, by rfl⟩ : syracuseStep 1912835 = 2869253) B2869253
theorem B1618193 : Blo 754331 1618193 := bstep (se 2 (by rfl) ⟨606822, by rfl⟩ : syracuseStep 1618193 = 1213645) B1213645
theorem B4305635 : Blo 754331 4305635 := bstep (se 1 (by rfl) ⟨3229226, by rfl⟩ : syracuseStep 4305635 = 6458453) B6458453
theorem B2044739 : Blo 754331 2044739 := bstep (se 1 (by rfl) ⟨1533554, by rfl⟩ : syracuseStep 2044739 = 3067109) B3067109
theorem B1913777 : Blo 754331 1913777 := bstep (se 2 (by rfl) ⟨717666, by rfl⟩ : syracuseStep 1913777 = 1435333) B1435333
theorem B1913827 : Blo 754331 1913827 := bstep (se 1 (by rfl) ⟨1435370, by rfl⟩ : syracuseStep 1913827 = 2870741) B2870741
theorem B1913969 : Blo 754331 1913969 := bstep (se 2 (by rfl) ⟨717738, by rfl⟩ : syracuseStep 1913969 = 1435477) B1435477
theorem B3224717 : Blo 754331 3224717 := bstep (se 3 (by rfl) ⟨604634, by rfl⟩ : syracuseStep 3224717 = 1209269) B1209269
theorem B9188579 : Blo 754331 9188579 := bstep (se 1 (by rfl) ⟨6891434, by rfl⟩ : syracuseStep 9188579 = 13782869) B13782869
theorem B1455779 : Blo 754331 1455779 := bstep (se 1 (by rfl) ⟨1091834, by rfl⟩ : syracuseStep 1455779 = 2183669) B2183669
theorem B4601585 : Blo 754331 4601585 := bstep (se 2 (by rfl) ⟨1725594, by rfl⟩ : syracuseStep 4601585 = 3451189) B3451189
theorem B2864909 : Blo 754331 2864909 := bstep (se 3 (by rfl) ⟨537170, by rfl⟩ : syracuseStep 2864909 = 1074341) B1074341
theorem B1914961 : Blo 754331 1914961 := bstep (se 2 (by rfl) ⟨718110, by rfl⟩ : syracuseStep 1914961 = 1436221) B1436221
theorem B1816931 : Blo 754331 1816931 := bstep (se 1 (by rfl) ⟨1362698, by rfl⟩ : syracuseStep 1816931 = 2725397) B2725397
theorem B1915235 : Blo 754331 1915235 := bstep (se 1 (by rfl) ⟨1436426, by rfl⟩ : syracuseStep 1915235 = 2872853) B2872853
theorem B8632817 : Blo 754331 8632817 := bstep (se 2 (by rfl) ⟨3237306, by rfl⟩ : syracuseStep 8632817 = 6474613) B6474613
theorem B7485965 : Blo 754331 7485965 := bstep (se 3 (by rfl) ⟨1403618, by rfl⟩ : syracuseStep 7485965 = 2807237) B2807237
theorem B1915427 : Blo 754331 1915427 := bstep (se 1 (by rfl) ⟨1436570, by rfl⟩ : syracuseStep 1915427 = 2873141) B2873141
theorem B4307525 : Blo 754331 4307525 := bstep (se 4 (by rfl) ⟨403830, by rfl⟩ : syracuseStep 4307525 = 807661) B807661
theorem B1260353 : Blo 754331 1260353 := bstep (se 2 (by rfl) ⟨472632, by rfl⟩ : syracuseStep 1260353 = 945265) B945265
theorem B6470513 : Blo 754331 6470513 := bstep (se 2 (by rfl) ⟨2426442, by rfl⟩ : syracuseStep 6470513 = 4852885) B4852885
theorem B1817777 : Blo 754331 1817777 := bstep (se 2 (by rfl) ⟨681666, by rfl⟩ : syracuseStep 1817777 = 1363333) B1363333
theorem B9223409 : Blo 754331 9223409 := bstep (se 2 (by rfl) ⟨3458778, by rfl⟩ : syracuseStep 9223409 = 6917557) B6917557
theorem B1817873 : Blo 754331 1817873 := bstep (se 2 (by rfl) ⟨681702, by rfl⟩ : syracuseStep 1817873 = 1363405) B1363405
theorem B1916369 : Blo 754331 1916369 := bstep (se 2 (by rfl) ⟨718638, by rfl⟩ : syracuseStep 1916369 = 1437277) B1437277
theorem B3882467 : Blo 754331 3882467 := bstep (se 1 (by rfl) ⟨2911850, by rfl⟩ : syracuseStep 3882467 = 5823701) B5823701
theorem B1916419 : Blo 754331 1916419 := bstep (se 1 (by rfl) ⟨1437314, by rfl⟩ : syracuseStep 1916419 = 2874629) B2874629
theorem B1916561 : Blo 754331 1916561 := bstep (se 2 (by rfl) ⟨718710, by rfl⟩ : syracuseStep 1916561 = 1437421) B1437421
theorem B2867021 : Blo 754331 2867021 := bstep (se 3 (by rfl) ⟨537566, by rfl⟩ : syracuseStep 2867021 = 1075133) B1075133
theorem B1752931 : Blo 754331 1752931 := bstep (se 1 (by rfl) ⟨1314698, by rfl⟩ : syracuseStep 1752931 = 2629397) B2629397
theorem B2179153 : Blo 754331 2179153 := bstep (se 2 (by rfl) ⟨817182, by rfl⟩ : syracuseStep 2179153 = 1634365) B1634365
theorem B9716021 : Blo 754331 9716021 := bstep (se 5 (by rfl) ⟨455438, by rfl⟩ : syracuseStep 9716021 = 910877) B910877
theorem B8176099 : Blo 754331 8176099 := bstep (se 1 (by rfl) ⟨6132074, by rfl⟩ : syracuseStep 8176099 = 12264149) B12264149
theorem B1819217 : Blo 754331 1819217 := bstep (se 2 (by rfl) ⟨682206, by rfl⟩ : syracuseStep 1819217 = 1364413) B1364413
theorem B2867825 : Blo 754331 2867825 := bstep (se 2 (by rfl) ⟨1075434, by rfl⟩ : syracuseStep 2867825 = 2150869) B2150869
theorem B5456497 : Blo 754331 5456497 := bstep (se 2 (by rfl) ⟨2046186, by rfl⟩ : syracuseStep 5456497 = 4092373) B4092373
theorem B1917553 : Blo 754331 1917553 := bstep (se 2 (by rfl) ⟨719082, by rfl⟩ : syracuseStep 1917553 = 1438165) B1438165
theorem B4080419 : Blo 754331 4080419 := bstep (se 1 (by rfl) ⟨3060314, by rfl⟩ : syracuseStep 4080419 = 6120629) B6120629
theorem B1917827 : Blo 754331 1917827 := bstep (se 1 (by rfl) ⟨1438370, by rfl⟩ : syracuseStep 1917827 = 2876741) B2876741
theorem B1360867 : Blo 754331 1360867 := bstep (se 1 (by rfl) ⟨1020650, by rfl⟩ : syracuseStep 1360867 = 2041301) B2041301
theorem B1131521 : Blo 754331 1131521 := bstep (se 2 (by rfl) ⟨424320, by rfl⟩ : syracuseStep 1131521 = 848641) B848641
theorem B1131539 : Blo 754331 1131539 := bstep (se 1 (by rfl) ⟨848654, by rfl⟩ : syracuseStep 1131539 = 1697309) B1697309
theorem B1131569 : Blo 754331 1131569 := bstep (se 2 (by rfl) ⟨424338, by rfl⟩ : syracuseStep 1131569 = 848677) B848677
theorem B1131587 : Blo 754331 1131587 := bstep (se 1 (by rfl) ⟨848690, by rfl⟩ : syracuseStep 1131587 = 1697381) B1697381
theorem B1918019 : Blo 754331 1918019 := bstep (se 1 (by rfl) ⟨1438514, by rfl⟩ : syracuseStep 1918019 = 2877029) B2877029
theorem B1131617 : Blo 754331 1131617 := bstep (se 2 (by rfl) ⟨424356, by rfl⟩ : syracuseStep 1131617 = 848713) B848713
theorem B4899953 : Blo 754331 4899953 := bstep (se 2 (by rfl) ⟨1837482, by rfl⟩ : syracuseStep 4899953 = 3674965) B3674965
theorem B1131635 : Blo 754331 1131635 := bstep (se 1 (by rfl) ⟨848726, by rfl⟩ : syracuseStep 1131635 = 1697453) B1697453
theorem B1131665 : Blo 754331 1131665 := bstep (se 2 (by rfl) ⟨424374, by rfl⟩ : syracuseStep 1131665 = 848749) B848749
theorem B1131683 : Blo 754331 1131683 := bstep (se 1 (by rfl) ⟨848762, by rfl⟩ : syracuseStep 1131683 = 1697525) B1697525
theorem B1131713 : Blo 754331 1131713 := bstep (se 2 (by rfl) ⟨424392, by rfl⟩ : syracuseStep 1131713 = 848785) B848785
theorem B1131731 : Blo 754331 1131731 := bstep (se 1 (by rfl) ⟨848798, by rfl⟩ : syracuseStep 1131731 = 1697597) B1697597
theorem B46613717 : Blo 754331 46613717 := bstep (se 7 (by rfl) ⟨546254, by rfl⟩ : syracuseStep 46613717 = 1092509) B1092509
theorem B1131761 : Blo 754331 1131761 := bstep (se 2 (by rfl) ⟨424410, by rfl⟩ : syracuseStep 1131761 = 848821) B848821
theorem B1131779 : Blo 754331 1131779 := bstep (se 1 (by rfl) ⟨848834, by rfl⟩ : syracuseStep 1131779 = 1697669) B1697669
theorem B2868493 : Blo 754331 2868493 := bstep (se 3 (by rfl) ⟨537842, by rfl⟩ : syracuseStep 2868493 = 1075685) B1075685
theorem B6472973 : Blo 754331 6472973 := bstep (se 3 (by rfl) ⟨1213682, by rfl⟩ : syracuseStep 6472973 = 2427365) B2427365
theorem B1131809 : Blo 754331 1131809 := bstep (se 2 (by rfl) ⟨424428, by rfl⟩ : syracuseStep 1131809 = 848857) B848857
theorem B1131827 : Blo 754331 1131827 := bstep (se 1 (by rfl) ⟨848870, by rfl⟩ : syracuseStep 1131827 = 1697741) B1697741
theorem B4834637 : Blo 754331 4834637 := bstep (se 3 (by rfl) ⟨906494, by rfl⟩ : syracuseStep 4834637 = 1812989) B1812989
theorem B1131857 : Blo 754331 1131857 := bstep (se 2 (by rfl) ⟨424446, by rfl⟩ : syracuseStep 1131857 = 848893) B848893
theorem B1131875 : Blo 754331 1131875 := bstep (se 1 (by rfl) ⟨848906, by rfl⟩ : syracuseStep 1131875 = 1697813) B1697813
theorem B6145379 : Blo 754331 6145379 := bstep (se 1 (by rfl) ⟨4609034, by rfl⟩ : syracuseStep 6145379 = 9218069) B9218069
theorem B1131905 : Blo 754331 1131905 := bstep (se 2 (by rfl) ⟨424464, by rfl⟩ : syracuseStep 1131905 = 848929) B848929
theorem B1131923 : Blo 754331 1131923 := bstep (se 1 (by rfl) ⟨848942, by rfl⟩ : syracuseStep 1131923 = 1697885) B1697885
theorem B3229091 : Blo 754331 3229091 := bstep (se 1 (by rfl) ⟨2421818, by rfl⟩ : syracuseStep 3229091 = 4843637) B4843637
theorem B1131953 : Blo 754331 1131953 := bstep (se 2 (by rfl) ⟨424482, by rfl⟩ : syracuseStep 1131953 = 848965) B848965
theorem B1131971 : Blo 754331 1131971 := bstep (se 1 (by rfl) ⟨848978, by rfl⟩ : syracuseStep 1131971 = 1697957) B1697957
theorem B1132001 : Blo 754331 1132001 := bstep (se 2 (by rfl) ⟨424500, by rfl⟩ : syracuseStep 1132001 = 849001) B849001
theorem B1132019 : Blo 754331 1132019 := bstep (se 1 (by rfl) ⟨849014, by rfl⟩ : syracuseStep 1132019 = 1698029) B1698029
theorem B1132049 : Blo 754331 1132049 := bstep (se 2 (by rfl) ⟨424518, by rfl⟩ : syracuseStep 1132049 = 849037) B849037
theorem B1132067 : Blo 754331 1132067 := bstep (se 1 (by rfl) ⟨849050, by rfl⟩ : syracuseStep 1132067 = 1698101) B1698101
theorem B1132097 : Blo 754331 1132097 := bstep (se 2 (by rfl) ⟨424536, by rfl⟩ : syracuseStep 1132097 = 849073) B849073
theorem B1132115 : Blo 754331 1132115 := bstep (se 1 (by rfl) ⟨849086, by rfl⟩ : syracuseStep 1132115 = 1698173) B1698173
theorem B1132145 : Blo 754331 1132145 := bstep (se 2 (by rfl) ⟨424554, by rfl⟩ : syracuseStep 1132145 = 849109) B849109
theorem B1132163 : Blo 754331 1132163 := bstep (se 1 (by rfl) ⟨849122, by rfl⟩ : syracuseStep 1132163 = 1698245) B1698245
theorem B3819149 : Blo 754331 3819149 := bstep (se 3 (by rfl) ⟨716090, by rfl⟩ : syracuseStep 3819149 = 1432181) B1432181
theorem B1132193 : Blo 754331 1132193 := bstep (se 2 (by rfl) ⟨424572, by rfl⟩ : syracuseStep 1132193 = 849145) B849145
theorem B1132211 : Blo 754331 1132211 := bstep (se 1 (by rfl) ⟨849158, by rfl⟩ : syracuseStep 1132211 = 1698317) B1698317
theorem B1132241 : Blo 754331 1132241 := bstep (se 2 (by rfl) ⟨424590, by rfl⟩ : syracuseStep 1132241 = 849181) B849181
theorem B1132259 : Blo 754331 1132259 := bstep (se 1 (by rfl) ⟨849194, by rfl⟩ : syracuseStep 1132259 = 1698389) B1698389
theorem B1132289 : Blo 754331 1132289 := bstep (se 2 (by rfl) ⟨424608, by rfl⟩ : syracuseStep 1132289 = 849217) B849217
theorem B2148113 : Blo 754331 2148113 := bstep (se 2 (by rfl) ⟨805542, by rfl⟩ : syracuseStep 2148113 = 1611085) B1611085
theorem B1132307 : Blo 754331 1132307 := bstep (se 1 (by rfl) ⟨849230, by rfl⟩ : syracuseStep 1132307 = 1698461) B1698461
theorem B1132337 : Blo 754331 1132337 := bstep (se 2 (by rfl) ⟨424626, by rfl⟩ : syracuseStep 1132337 = 849253) B849253
theorem B1132355 : Blo 754331 1132355 := bstep (se 1 (by rfl) ⟨849266, by rfl⟩ : syracuseStep 1132355 = 1698533) B1698533
theorem B1132385 : Blo 754331 1132385 := bstep (se 2 (by rfl) ⟨424644, by rfl⟩ : syracuseStep 1132385 = 849289) B849289
theorem B1132403 : Blo 754331 1132403 := bstep (se 1 (by rfl) ⟨849302, by rfl⟩ : syracuseStep 1132403 = 1698605) B1698605
theorem B2148227 : Blo 754331 2148227 := bstep (se 1 (by rfl) ⟨1611170, by rfl⟩ : syracuseStep 2148227 = 3222341) B3222341
theorem B1132433 : Blo 754331 1132433 := bstep (se 2 (by rfl) ⟨424662, by rfl⟩ : syracuseStep 1132433 = 849325) B849325
theorem B1132451 : Blo 754331 1132451 := bstep (se 1 (by rfl) ⟨849338, by rfl⟩ : syracuseStep 1132451 = 1698677) B1698677
theorem B1132481 : Blo 754331 1132481 := bstep (se 2 (by rfl) ⟨424680, by rfl⟩ : syracuseStep 1132481 = 849361) B849361
theorem B1132499 : Blo 754331 1132499 := bstep (se 1 (by rfl) ⟨849374, by rfl⟩ : syracuseStep 1132499 = 1698749) B1698749
theorem B1132529 : Blo 754331 1132529 := bstep (se 2 (by rfl) ⟨424698, by rfl⟩ : syracuseStep 1132529 = 849397) B849397
theorem B1918961 : Blo 754331 1918961 := bstep (se 2 (by rfl) ⟨719610, by rfl⟩ : syracuseStep 1918961 = 1439221) B1439221
theorem B1132547 : Blo 754331 1132547 := bstep (se 1 (by rfl) ⟨849410, by rfl⟩ : syracuseStep 1132547 = 1698821) B1698821
theorem B1132577 : Blo 754331 1132577 := bstep (se 2 (by rfl) ⟨424716, by rfl⟩ : syracuseStep 1132577 = 849433) B849433
theorem B2869283 : Blo 754331 2869283 := bstep (se 1 (by rfl) ⟨2151962, by rfl⟩ : syracuseStep 2869283 = 4303925) B4303925
theorem B1919011 : Blo 754331 1919011 := bstep (se 1 (by rfl) ⟨1439258, by rfl⟩ : syracuseStep 1919011 = 2878517) B2878517
theorem B1132595 : Blo 754331 1132595 := bstep (se 1 (by rfl) ⟨849446, by rfl⟩ : syracuseStep 1132595 = 1698893) B1698893
theorem B1132625 : Blo 754331 1132625 := bstep (se 2 (by rfl) ⟨424734, by rfl⟩ : syracuseStep 1132625 = 849469) B849469
theorem B1132643 : Blo 754331 1132643 := bstep (se 1 (by rfl) ⟨849482, by rfl⟩ : syracuseStep 1132643 = 1698965) B1698965
theorem B1132673 : Blo 754331 1132673 := bstep (se 2 (by rfl) ⟨424752, by rfl⟩ : syracuseStep 1132673 = 849505) B849505
theorem B1132691 : Blo 754331 1132691 := bstep (se 1 (by rfl) ⟨849518, by rfl⟩ : syracuseStep 1132691 = 1699037) B1699037
theorem B1132721 : Blo 754331 1132721 := bstep (se 2 (by rfl) ⟨424770, by rfl⟩ : syracuseStep 1132721 = 849541) B849541
theorem B1919153 : Blo 754331 1919153 := bstep (se 2 (by rfl) ⟨719682, by rfl⟩ : syracuseStep 1919153 = 1439365) B1439365
theorem B1132739 : Blo 754331 1132739 := bstep (se 1 (by rfl) ⟨849554, by rfl⟩ : syracuseStep 1132739 = 1699109) B1699109
theorem B1132769 : Blo 754331 1132769 := bstep (se 2 (by rfl) ⟨424788, by rfl⟩ : syracuseStep 1132769 = 849577) B849577
theorem B1132787 : Blo 754331 1132787 := bstep (se 1 (by rfl) ⟨849590, by rfl⟩ : syracuseStep 1132787 = 1699181) B1699181
theorem B1132817 : Blo 754331 1132817 := bstep (se 2 (by rfl) ⟨424806, by rfl⟩ : syracuseStep 1132817 = 849613) B849613
theorem B1132835 : Blo 754331 1132835 := bstep (se 1 (by rfl) ⟨849626, by rfl⟩ : syracuseStep 1132835 = 1699253) B1699253
theorem B1132865 : Blo 754331 1132865 := bstep (se 2 (by rfl) ⟨424824, by rfl⟩ : syracuseStep 1132865 = 849649) B849649
theorem B1132883 : Blo 754331 1132883 := bstep (se 1 (by rfl) ⟨849662, by rfl⟩ : syracuseStep 1132883 = 1699325) B1699325
theorem B1132913 : Blo 754331 1132913 := bstep (se 2 (by rfl) ⟨424842, by rfl⟩ : syracuseStep 1132913 = 849685) B849685
theorem B1132931 : Blo 754331 1132931 := bstep (se 1 (by rfl) ⟨849698, by rfl⟩ : syracuseStep 1132931 = 1699397) B1699397
theorem B1132961 : Blo 754331 1132961 := bstep (se 2 (by rfl) ⟨424860, by rfl⟩ : syracuseStep 1132961 = 849721) B849721
theorem B1132979 : Blo 754331 1132979 := bstep (se 1 (by rfl) ⟨849734, by rfl⟩ : syracuseStep 1132979 = 1699469) B1699469
theorem B1133009 : Blo 754331 1133009 := bstep (se 2 (by rfl) ⟨424878, by rfl⟩ : syracuseStep 1133009 = 849757) B849757
theorem B1133027 : Blo 754331 1133027 := bstep (se 1 (by rfl) ⟨849770, by rfl⟩ : syracuseStep 1133027 = 1699541) B1699541
theorem B1133057 : Blo 754331 1133057 := bstep (se 2 (by rfl) ⟨424896, by rfl⟩ : syracuseStep 1133057 = 849793) B849793
theorem B1133075 : Blo 754331 1133075 := bstep (se 1 (by rfl) ⟨849806, by rfl⟩ : syracuseStep 1133075 = 1699613) B1699613
theorem B1362467 : Blo 754331 1362467 := bstep (se 1 (by rfl) ⟨1021850, by rfl⟩ : syracuseStep 1362467 = 2043701) B2043701
theorem B1133105 : Blo 754331 1133105 := bstep (se 2 (by rfl) ⟨424914, by rfl⟩ : syracuseStep 1133105 = 849829) B849829
theorem B1133123 : Blo 754331 1133123 := bstep (se 1 (by rfl) ⟨849842, by rfl⟩ : syracuseStep 1133123 = 1699685) B1699685
theorem B1133153 : Blo 754331 1133153 := bstep (se 2 (by rfl) ⟨424932, by rfl⟩ : syracuseStep 1133153 = 849865) B849865
theorem B1133171 : Blo 754331 1133171 := bstep (se 1 (by rfl) ⟨849878, by rfl⟩ : syracuseStep 1133171 = 1699757) B1699757
theorem B1133201 : Blo 754331 1133201 := bstep (se 2 (by rfl) ⟨424950, by rfl⟩ : syracuseStep 1133201 = 849901) B849901
theorem B1133219 : Blo 754331 1133219 := bstep (se 1 (by rfl) ⟨849914, by rfl⟩ : syracuseStep 1133219 = 1699829) B1699829
theorem B2869937 : Blo 754331 2869937 := bstep (se 2 (by rfl) ⟨1076226, by rfl⟩ : syracuseStep 2869937 = 2152453) B2152453
theorem B1821361 : Blo 754331 1821361 := bstep (se 2 (by rfl) ⟨683010, by rfl⟩ : syracuseStep 1821361 = 1366021) B1366021
theorem B1133249 : Blo 754331 1133249 := bstep (se 2 (by rfl) ⟨424968, by rfl⟩ : syracuseStep 1133249 = 849937) B849937
theorem B1133267 : Blo 754331 1133267 := bstep (se 1 (by rfl) ⟨849950, by rfl⟩ : syracuseStep 1133267 = 1699901) B1699901
theorem B1133297 : Blo 754331 1133297 := bstep (se 2 (by rfl) ⟨424986, by rfl⟩ : syracuseStep 1133297 = 849973) B849973
theorem B1133315 : Blo 754331 1133315 := bstep (se 1 (by rfl) ⟨849986, by rfl⟩ : syracuseStep 1133315 = 1699973) B1699973
theorem B1133345 : Blo 754331 1133345 := bstep (se 2 (by rfl) ⟨425004, by rfl⟩ : syracuseStep 1133345 = 850009) B850009
theorem B1133363 : Blo 754331 1133363 := bstep (se 1 (by rfl) ⟨850022, by rfl⟩ : syracuseStep 1133363 = 1700045) B1700045
theorem B6540101 : Blo 754331 6540101 := bstep (se 4 (by rfl) ⟨613134, by rfl⟩ : syracuseStep 6540101 = 1226269) B1226269
theorem B1133393 : Blo 754331 1133393 := bstep (se 2 (by rfl) ⟨425022, by rfl⟩ : syracuseStep 1133393 = 850045) B850045
theorem B1133411 : Blo 754331 1133411 := bstep (se 1 (by rfl) ⟨850058, by rfl⟩ : syracuseStep 1133411 = 1700117) B1700117
theorem B2149229 : Blo 754331 2149229 := bstep (se 3 (by rfl) ⟨402980, by rfl⟩ : syracuseStep 2149229 = 805961) B805961
theorem B1133441 : Blo 754331 1133441 := bstep (se 2 (by rfl) ⟨425040, by rfl⟩ : syracuseStep 1133441 = 850081) B850081
theorem B1133459 : Blo 754331 1133459 := bstep (se 1 (by rfl) ⟨850094, by rfl⟩ : syracuseStep 1133459 = 1700189) B1700189
theorem B1133489 : Blo 754331 1133489 := bstep (se 2 (by rfl) ⟨425058, by rfl⟩ : syracuseStep 1133489 = 850117) B850117
theorem B1133507 : Blo 754331 1133507 := bstep (se 1 (by rfl) ⟨850130, by rfl⟩ : syracuseStep 1133507 = 1700261) B1700261
theorem B1133537 : Blo 754331 1133537 := bstep (se 2 (by rfl) ⟨425076, by rfl⟩ : syracuseStep 1133537 = 850153) B850153
theorem B13781987 : Blo 754331 13781987 := bstep (se 1 (by rfl) ⟨10336490, by rfl⟩ : syracuseStep 13781987 = 20672981) B20672981
theorem B1133555 : Blo 754331 1133555 := bstep (se 1 (by rfl) ⟨850166, by rfl⟩ : syracuseStep 1133555 = 1700333) B1700333
theorem B1133585 : Blo 754331 1133585 := bstep (se 2 (by rfl) ⟨425094, by rfl⟩ : syracuseStep 1133585 = 850189) B850189
theorem B2149411 : Blo 754331 2149411 := bstep (se 1 (by rfl) ⟨1612058, by rfl⟩ : syracuseStep 2149411 = 3224117) B3224117
theorem B1133603 : Blo 754331 1133603 := bstep (se 1 (by rfl) ⟨850202, by rfl⟩ : syracuseStep 1133603 = 1700405) B1700405
theorem B1133633 : Blo 754331 1133633 := bstep (se 2 (by rfl) ⟨425112, by rfl⟩ : syracuseStep 1133633 = 850225) B850225
theorem B1133651 : Blo 754331 1133651 := bstep (se 1 (by rfl) ⟨850238, by rfl⟩ : syracuseStep 1133651 = 1700477) B1700477
theorem B805987 : Blo 754331 805987 := bstep (se 1 (by rfl) ⟨604490, by rfl⟩ : syracuseStep 805987 = 1208981) B1208981
theorem B1133681 : Blo 754331 1133681 := bstep (se 2 (by rfl) ⟨425130, by rfl⟩ : syracuseStep 1133681 = 850261) B850261
theorem B1133699 : Blo 754331 1133699 := bstep (se 1 (by rfl) ⟨850274, by rfl⟩ : syracuseStep 1133699 = 1700549) B1700549
theorem B1133729 : Blo 754331 1133729 := bstep (se 2 (by rfl) ⟨425148, by rfl⟩ : syracuseStep 1133729 = 850297) B850297
theorem B1133747 : Blo 754331 1133747 := bstep (se 1 (by rfl) ⟨850310, by rfl⟩ : syracuseStep 1133747 = 1700621) B1700621
theorem B2149571 : Blo 754331 2149571 := bstep (se 1 (by rfl) ⟨1612178, by rfl⟩ : syracuseStep 2149571 = 3224357) B3224357
theorem B2247875 : Blo 754331 2247875 := bstep (se 1 (by rfl) ⟨1685906, by rfl⟩ : syracuseStep 2247875 = 3371813) B3371813
theorem B1133777 : Blo 754331 1133777 := bstep (se 2 (by rfl) ⟨425166, by rfl⟩ : syracuseStep 1133777 = 850333) B850333
theorem B1133795 : Blo 754331 1133795 := bstep (se 1 (by rfl) ⟨850346, by rfl⟩ : syracuseStep 1133795 = 1700693) B1700693
theorem B1133825 : Blo 754331 1133825 := bstep (se 2 (by rfl) ⟨425184, by rfl⟩ : syracuseStep 1133825 = 850369) B850369
theorem B1133843 : Blo 754331 1133843 := bstep (se 1 (by rfl) ⟨850382, by rfl⟩ : syracuseStep 1133843 = 1700765) B1700765
theorem B1133873 : Blo 754331 1133873 := bstep (se 2 (by rfl) ⟨425202, by rfl⟩ : syracuseStep 1133873 = 850405) B850405
theorem B1133891 : Blo 754331 1133891 := bstep (se 1 (by rfl) ⟨850418, by rfl⟩ : syracuseStep 1133891 = 1700837) B1700837
theorem B1133921 : Blo 754331 1133921 := bstep (se 2 (by rfl) ⟨425220, by rfl⟩ : syracuseStep 1133921 = 850441) B850441
theorem B3231089 : Blo 754331 3231089 := bstep (se 2 (by rfl) ⟨1211658, by rfl⟩ : syracuseStep 3231089 = 2423317) B2423317
theorem B1133939 : Blo 754331 1133939 := bstep (se 1 (by rfl) ⟨850454, by rfl⟩ : syracuseStep 1133939 = 1700909) B1700909
theorem B1133969 : Blo 754331 1133969 := bstep (se 2 (by rfl) ⟨425238, by rfl⟩ : syracuseStep 1133969 = 850477) B850477
theorem B1133987 : Blo 754331 1133987 := bstep (se 1 (by rfl) ⟨850490, by rfl⟩ : syracuseStep 1133987 = 1700981) B1700981
theorem B1134017 : Blo 754331 1134017 := bstep (se 2 (by rfl) ⟨425256, by rfl⟩ : syracuseStep 1134017 = 850513) B850513
theorem B1134035 : Blo 754331 1134035 := bstep (se 1 (by rfl) ⟨850526, by rfl⟩ : syracuseStep 1134035 = 1701053) B1701053
theorem B1134065 : Blo 754331 1134065 := bstep (se 2 (by rfl) ⟨425274, by rfl⟩ : syracuseStep 1134065 = 850549) B850549
theorem B871939 : Blo 754331 871939 := bstep (se 1 (by rfl) ⟨653954, by rfl⟩ : syracuseStep 871939 = 1307909) B1307909
theorem B1134083 : Blo 754331 1134083 := bstep (se 1 (by rfl) ⟨850562, by rfl⟩ : syracuseStep 1134083 = 1701125) B1701125
theorem B1134113 : Blo 754331 1134113 := bstep (se 2 (by rfl) ⟨425292, by rfl⟩ : syracuseStep 1134113 = 850585) B850585
theorem B1134131 : Blo 754331 1134131 := bstep (se 1 (by rfl) ⟨850598, by rfl⟩ : syracuseStep 1134131 = 1701197) B1701197
theorem B1134161 : Blo 754331 1134161 := bstep (se 2 (by rfl) ⟨425310, by rfl⟩ : syracuseStep 1134161 = 850621) B850621
theorem B1134179 : Blo 754331 1134179 := bstep (se 1 (by rfl) ⟨850634, by rfl⟩ : syracuseStep 1134179 = 1701269) B1701269
theorem B1134209 : Blo 754331 1134209 := bstep (se 2 (by rfl) ⟨425328, by rfl⟩ : syracuseStep 1134209 = 850657) B850657
theorem B1134227 : Blo 754331 1134227 := bstep (se 1 (by rfl) ⟨850670, by rfl⟩ : syracuseStep 1134227 = 1701341) B1701341
theorem B4083377 : Blo 754331 4083377 := bstep (se 2 (by rfl) ⟨1531266, by rfl⟩ : syracuseStep 4083377 = 3062533) B3062533
theorem B1134257 : Blo 754331 1134257 := bstep (se 2 (by rfl) ⟨425346, by rfl⟩ : syracuseStep 1134257 = 850693) B850693
theorem B1134275 : Blo 754331 1134275 := bstep (se 1 (by rfl) ⟨850706, by rfl⟩ : syracuseStep 1134275 = 1701413) B1701413
theorem B1134305 : Blo 754331 1134305 := bstep (se 2 (by rfl) ⟨425364, by rfl⟩ : syracuseStep 1134305 = 850729) B850729
theorem B1134323 : Blo 754331 1134323 := bstep (se 1 (by rfl) ⟨850742, by rfl⟩ : syracuseStep 1134323 = 1701485) B1701485
theorem B1134353 : Blo 754331 1134353 := bstep (se 2 (by rfl) ⟨425382, by rfl⟩ : syracuseStep 1134353 = 850765) B850765
theorem B1134371 : Blo 754331 1134371 := bstep (se 1 (by rfl) ⟨850778, by rfl⟩ : syracuseStep 1134371 = 1701557) B1701557
theorem B1134401 : Blo 754331 1134401 := bstep (se 2 (by rfl) ⟨425400, by rfl⟩ : syracuseStep 1134401 = 850801) B850801
theorem B4083533 : Blo 754331 4083533 := bstep (se 3 (by rfl) ⟨765662, by rfl⟩ : syracuseStep 4083533 = 1531325) B1531325
theorem B1134419 : Blo 754331 1134419 := bstep (se 1 (by rfl) ⟨850814, by rfl⟩ : syracuseStep 1134419 = 1701629) B1701629
theorem B1134449 : Blo 754331 1134449 := bstep (se 2 (by rfl) ⟨425418, by rfl⟩ : syracuseStep 1134449 = 850837) B850837
theorem B1134467 : Blo 754331 1134467 := bstep (se 1 (by rfl) ⟨850850, by rfl⟩ : syracuseStep 1134467 = 1701701) B1701701
theorem B1134497 : Blo 754331 1134497 := bstep (se 2 (by rfl) ⟨425436, by rfl⟩ : syracuseStep 1134497 = 850873) B850873
theorem B1134515 : Blo 754331 1134515 := bstep (se 1 (by rfl) ⟨850886, by rfl⟩ : syracuseStep 1134515 = 1701773) B1701773
theorem B1134545 : Blo 754331 1134545 := bstep (se 2 (by rfl) ⟨425454, by rfl⟩ : syracuseStep 1134545 = 850909) B850909
theorem B1134563 : Blo 754331 1134563 := bstep (se 1 (by rfl) ⟨850922, by rfl⟩ : syracuseStep 1134563 = 1701845) B1701845
theorem B1134593 : Blo 754331 1134593 := bstep (se 2 (by rfl) ⟨425472, by rfl⟩ : syracuseStep 1134593 = 850945) B850945
theorem B1134611 : Blo 754331 1134611 := bstep (se 1 (by rfl) ⟨850958, by rfl⟩ : syracuseStep 1134611 = 1701917) B1701917
theorem B1134641 : Blo 754331 1134641 := bstep (se 2 (by rfl) ⟨425490, by rfl⟩ : syracuseStep 1134641 = 850981) B850981
theorem B1134659 : Blo 754331 1134659 := bstep (se 1 (by rfl) ⟨850994, by rfl⟩ : syracuseStep 1134659 = 1701989) B1701989
theorem B1134689 : Blo 754331 1134689 := bstep (se 2 (by rfl) ⟨425508, by rfl⟩ : syracuseStep 1134689 = 851017) B851017
theorem B2871395 : Blo 754331 2871395 := bstep (se 1 (by rfl) ⟨2153546, by rfl⟩ : syracuseStep 2871395 = 4307093) B4307093
theorem B2871409 : Blo 754331 2871409 := bstep (se 2 (by rfl) ⟨1076778, by rfl⟩ : syracuseStep 2871409 = 2153557) B2153557
theorem B1134707 : Blo 754331 1134707 := bstep (se 1 (by rfl) ⟨851030, by rfl⟩ : syracuseStep 1134707 = 1702061) B1702061
theorem B1134737 : Blo 754331 1134737 := bstep (se 2 (by rfl) ⟨425526, by rfl⟩ : syracuseStep 1134737 = 851053) B851053
theorem B1134755 : Blo 754331 1134755 := bstep (se 1 (by rfl) ⟨851066, by rfl⟩ : syracuseStep 1134755 = 1702133) B1702133
theorem B1134785 : Blo 754331 1134785 := bstep (se 2 (by rfl) ⟨425544, by rfl⟩ : syracuseStep 1134785 = 851089) B851089
theorem B1134803 : Blo 754331 1134803 := bstep (se 1 (by rfl) ⟨851102, by rfl⟩ : syracuseStep 1134803 = 1702205) B1702205
theorem B2150641 : Blo 754331 2150641 := bstep (se 2 (by rfl) ⟨806490, by rfl⟩ : syracuseStep 2150641 = 1612981) B1612981
theorem B1134833 : Blo 754331 1134833 := bstep (se 2 (by rfl) ⟨425562, by rfl⟩ : syracuseStep 1134833 = 851125) B851125
theorem B1167617 : Blo 754331 1167617 := bstep (se 2 (by rfl) ⟨437856, by rfl⟩ : syracuseStep 1167617 = 875713) B875713
theorem B1134851 : Blo 754331 1134851 := bstep (se 1 (by rfl) ⟨851138, by rfl⟩ : syracuseStep 1134851 = 1702277) B1702277
theorem B4313357 : Blo 754331 4313357 := bstep (se 3 (by rfl) ⟨808754, by rfl⟩ : syracuseStep 4313357 = 1617509) B1617509
theorem B1134881 : Blo 754331 1134881 := bstep (se 2 (by rfl) ⟨425580, by rfl⟩ : syracuseStep 1134881 = 851161) B851161
theorem B1134899 : Blo 754331 1134899 := bstep (se 1 (by rfl) ⟨851174, by rfl⟩ : syracuseStep 1134899 = 1702349) B1702349
theorem B1134929 : Blo 754331 1134929 := bstep (se 2 (by rfl) ⟨425598, by rfl⟩ : syracuseStep 1134929 = 851197) B851197
theorem B807251 : Blo 754331 807251 := bstep (se 1 (by rfl) ⟨605438, by rfl⟩ : syracuseStep 807251 = 1210877) B1210877
theorem B1134947 : Blo 754331 1134947 := bstep (se 1 (by rfl) ⟨851210, by rfl⟩ : syracuseStep 1134947 = 1702421) B1702421
theorem B1134977 : Blo 754331 1134977 := bstep (se 2 (by rfl) ⟨425616, by rfl⟩ : syracuseStep 1134977 = 851233) B851233
theorem B4837765 : Blo 754331 4837765 := bstep (se 4 (by rfl) ⟨453540, by rfl⟩ : syracuseStep 4837765 = 907081) B907081
theorem B1134995 : Blo 754331 1134995 := bstep (se 1 (by rfl) ⟨851246, by rfl⟩ : syracuseStep 1134995 = 1702493) B1702493
theorem B1135025 : Blo 754331 1135025 := bstep (se 2 (by rfl) ⟨425634, by rfl⟩ : syracuseStep 1135025 = 851269) B851269
theorem B1135043 : Blo 754331 1135043 := bstep (se 1 (by rfl) ⟨851282, by rfl⟩ : syracuseStep 1135043 = 1702565) B1702565
theorem B1135073 : Blo 754331 1135073 := bstep (se 2 (by rfl) ⟨425652, by rfl⟩ : syracuseStep 1135073 = 851305) B851305
theorem B3822065 : Blo 754331 3822065 := bstep (se 2 (by rfl) ⟨1433274, by rfl⟩ : syracuseStep 3822065 = 2866549) B2866549
theorem B1135091 : Blo 754331 1135091 := bstep (se 1 (by rfl) ⟨851318, by rfl⟩ : syracuseStep 1135091 = 1702637) B1702637
theorem B1135121 : Blo 754331 1135121 := bstep (se 2 (by rfl) ⟨425670, by rfl⟩ : syracuseStep 1135121 = 851341) B851341
theorem B1135139 : Blo 754331 1135139 := bstep (se 1 (by rfl) ⟨851354, by rfl⟩ : syracuseStep 1135139 = 1702709) B1702709
theorem B1135169 : Blo 754331 1135169 := bstep (se 2 (by rfl) ⟨425688, by rfl⟩ : syracuseStep 1135169 = 851377) B851377
theorem B1135187 : Blo 754331 1135187 := bstep (se 1 (by rfl) ⟨851390, by rfl⟩ : syracuseStep 1135187 = 1702781) B1702781
theorem B1135217 : Blo 754331 1135217 := bstep (se 2 (by rfl) ⟨425706, by rfl⟩ : syracuseStep 1135217 = 851413) B851413
theorem B1135235 : Blo 754331 1135235 := bstep (se 1 (by rfl) ⟨851426, by rfl⟩ : syracuseStep 1135235 = 1702853) B1702853
theorem B1135265 : Blo 754331 1135265 := bstep (se 2 (by rfl) ⟨425724, by rfl⟩ : syracuseStep 1135265 = 851449) B851449
theorem B1135283 : Blo 754331 1135283 := bstep (se 1 (by rfl) ⟨851462, by rfl⟩ : syracuseStep 1135283 = 1702925) B1702925
theorem B1135313 : Blo 754331 1135313 := bstep (se 2 (by rfl) ⟨425742, by rfl⟩ : syracuseStep 1135313 = 851485) B851485
theorem B1135331 : Blo 754331 1135331 := bstep (se 1 (by rfl) ⟨851498, by rfl⟩ : syracuseStep 1135331 = 1702997) B1702997
theorem B1135361 : Blo 754331 1135361 := bstep (se 2 (by rfl) ⟨425760, by rfl⟩ : syracuseStep 1135361 = 851521) B851521
theorem B1135379 : Blo 754331 1135379 := bstep (se 1 (by rfl) ⟨851534, by rfl⟩ : syracuseStep 1135379 = 1703069) B1703069
theorem B1135409 : Blo 754331 1135409 := bstep (se 2 (by rfl) ⟨425778, by rfl⟩ : syracuseStep 1135409 = 851557) B851557
theorem B1135427 : Blo 754331 1135427 := bstep (se 1 (by rfl) ⟨851570, by rfl⟩ : syracuseStep 1135427 = 1703141) B1703141
theorem B1135457 : Blo 754331 1135457 := bstep (se 2 (by rfl) ⟨425796, by rfl⟩ : syracuseStep 1135457 = 851593) B851593
theorem B1135475 : Blo 754331 1135475 := bstep (se 1 (by rfl) ⟨851606, by rfl⟩ : syracuseStep 1135475 = 1703213) B1703213
theorem B1135505 : Blo 754331 1135505 := bstep (se 2 (by rfl) ⟨425814, by rfl⟩ : syracuseStep 1135505 = 851629) B851629
theorem B1135523 : Blo 754331 1135523 := bstep (se 1 (by rfl) ⟨851642, by rfl⟩ : syracuseStep 1135523 = 1703285) B1703285
theorem B1135553 : Blo 754331 1135553 := bstep (se 2 (by rfl) ⟨425832, by rfl⟩ : syracuseStep 1135553 = 851665) B851665
theorem B1135571 : Blo 754331 1135571 := bstep (se 1 (by rfl) ⟨851678, by rfl⟩ : syracuseStep 1135571 = 1703357) B1703357
theorem B1135601 : Blo 754331 1135601 := bstep (se 2 (by rfl) ⟨425850, by rfl⟩ : syracuseStep 1135601 = 851701) B851701
theorem B1135619 : Blo 754331 1135619 := bstep (se 1 (by rfl) ⟨851714, by rfl⟩ : syracuseStep 1135619 = 1703429) B1703429
theorem B3232781 : Blo 754331 3232781 := bstep (se 3 (by rfl) ⟨606146, by rfl⟩ : syracuseStep 3232781 = 1212293) B1212293
theorem B1135649 : Blo 754331 1135649 := bstep (se 2 (by rfl) ⟨425868, by rfl⟩ : syracuseStep 1135649 = 851737) B851737
theorem B1135667 : Blo 754331 1135667 := bstep (se 1 (by rfl) ⟨851750, by rfl⟩ : syracuseStep 1135667 = 1703501) B1703501
theorem B808003 : Blo 754331 808003 := bstep (se 1 (by rfl) ⟨606002, by rfl⟩ : syracuseStep 808003 = 1212005) B1212005
theorem B1135697 : Blo 754331 1135697 := bstep (se 2 (by rfl) ⟨425886, by rfl⟩ : syracuseStep 1135697 = 851773) B851773
theorem B1135715 : Blo 754331 1135715 := bstep (se 1 (by rfl) ⟨851786, by rfl⟩ : syracuseStep 1135715 = 1703573) B1703573
theorem B1135745 : Blo 754331 1135745 := bstep (se 2 (by rfl) ⟨425904, by rfl⟩ : syracuseStep 1135745 = 851809) B851809
theorem B1135763 : Blo 754331 1135763 := bstep (se 1 (by rfl) ⟨851822, by rfl⟩ : syracuseStep 1135763 = 1703645) B1703645
theorem B1135793 : Blo 754331 1135793 := bstep (se 2 (by rfl) ⟨425922, by rfl⟩ : syracuseStep 1135793 = 851845) B851845
theorem B1135811 : Blo 754331 1135811 := bstep (se 1 (by rfl) ⟨851858, by rfl⟩ : syracuseStep 1135811 = 1703717) B1703717
theorem B1135841 : Blo 754331 1135841 := bstep (se 2 (by rfl) ⟨425940, by rfl⟩ : syracuseStep 1135841 = 851881) B851881
theorem B1135859 : Blo 754331 1135859 := bstep (se 1 (by rfl) ⟨851894, by rfl⟩ : syracuseStep 1135859 = 1703789) B1703789
theorem B1135889 : Blo 754331 1135889 := bstep (se 2 (by rfl) ⟨425958, by rfl⟩ : syracuseStep 1135889 = 851917) B851917
theorem B1135907 : Blo 754331 1135907 := bstep (se 1 (by rfl) ⟨851930, by rfl⟩ : syracuseStep 1135907 = 1703861) B1703861
theorem B1135937 : Blo 754331 1135937 := bstep (se 2 (by rfl) ⟨425976, by rfl⟩ : syracuseStep 1135937 = 851953) B851953
theorem B873811 : Blo 754331 873811 := bstep (se 1 (by rfl) ⟨655358, by rfl⟩ : syracuseStep 873811 = 1310717) B1310717
theorem B1135955 : Blo 754331 1135955 := bstep (se 1 (by rfl) ⟨851966, by rfl⟩ : syracuseStep 1135955 = 1703933) B1703933
theorem B1135985 : Blo 754331 1135985 := bstep (se 2 (by rfl) ⟨425994, by rfl⟩ : syracuseStep 1135985 = 851989) B851989
theorem B1136003 : Blo 754331 1136003 := bstep (se 1 (by rfl) ⟨852002, by rfl⟩ : syracuseStep 1136003 = 1704005) B1704005
theorem B1136033 : Blo 754331 1136033 := bstep (se 2 (by rfl) ⟨426012, by rfl⟩ : syracuseStep 1136033 = 852025) B852025
theorem B1136051 : Blo 754331 1136051 := bstep (se 1 (by rfl) ⟨852038, by rfl⟩ : syracuseStep 1136051 = 1704077) B1704077
theorem B1136081 : Blo 754331 1136081 := bstep (se 2 (by rfl) ⟨426030, by rfl⟩ : syracuseStep 1136081 = 852061) B852061
theorem B1136099 : Blo 754331 1136099 := bstep (se 1 (by rfl) ⟨852074, by rfl⟩ : syracuseStep 1136099 = 1704149) B1704149
theorem B2151917 : Blo 754331 2151917 := bstep (se 3 (by rfl) ⟨403484, by rfl⟩ : syracuseStep 2151917 = 806969) B806969
theorem B1136129 : Blo 754331 1136129 := bstep (se 2 (by rfl) ⟨426048, by rfl⟩ : syracuseStep 1136129 = 852097) B852097
theorem B1136147 : Blo 754331 1136147 := bstep (se 1 (by rfl) ⟨852110, by rfl⟩ : syracuseStep 1136147 = 1704221) B1704221
theorem B2872867 : Blo 754331 2872867 := bstep (se 1 (by rfl) ⟨2154650, by rfl⟩ : syracuseStep 2872867 = 4309301) B4309301
theorem B1136177 : Blo 754331 1136177 := bstep (se 2 (by rfl) ⟨426066, by rfl⟩ : syracuseStep 1136177 = 852133) B852133
theorem B1136195 : Blo 754331 1136195 := bstep (se 1 (by rfl) ⟨852146, by rfl⟩ : syracuseStep 1136195 = 1704293) B1704293
theorem B1136225 : Blo 754331 1136225 := bstep (se 2 (by rfl) ⟨426084, by rfl⟩ : syracuseStep 1136225 = 852169) B852169
theorem B1136243 : Blo 754331 1136243 := bstep (se 1 (by rfl) ⟨852182, by rfl⟩ : syracuseStep 1136243 = 1704365) B1704365
theorem B1136273 : Blo 754331 1136273 := bstep (se 2 (by rfl) ⟨426102, by rfl⟩ : syracuseStep 1136273 = 852205) B852205
theorem B2152099 : Blo 754331 2152099 := bstep (se 1 (by rfl) ⟨1614074, by rfl⟩ : syracuseStep 2152099 = 3228149) B3228149
theorem B1136291 : Blo 754331 1136291 := bstep (se 1 (by rfl) ⟨852218, by rfl⟩ : syracuseStep 1136291 = 1704437) B1704437
theorem B1136321 : Blo 754331 1136321 := bstep (se 2 (by rfl) ⟨426120, by rfl⟩ : syracuseStep 1136321 = 852241) B852241
theorem B2152145 : Blo 754331 2152145 := bstep (se 2 (by rfl) ⟨807054, by rfl⟩ : syracuseStep 2152145 = 1614109) B1614109
theorem B1136339 : Blo 754331 1136339 := bstep (se 1 (by rfl) ⟨852254, by rfl⟩ : syracuseStep 1136339 = 1704509) B1704509
theorem B1136369 : Blo 754331 1136369 := bstep (se 2 (by rfl) ⟨426138, by rfl⟩ : syracuseStep 1136369 = 852277) B852277
theorem B1136387 : Blo 754331 1136387 := bstep (se 1 (by rfl) ⟨852290, by rfl⟩ : syracuseStep 1136387 = 1704581) B1704581
theorem B1136417 : Blo 754331 1136417 := bstep (se 2 (by rfl) ⟨426156, by rfl⟩ : syracuseStep 1136417 = 852313) B852313
theorem B907043 : Blo 754331 907043 := bstep (se 1 (by rfl) ⟨680282, by rfl⟩ : syracuseStep 907043 = 1360565) B1360565
theorem B1136435 : Blo 754331 1136435 := bstep (se 1 (by rfl) ⟨852326, by rfl⟩ : syracuseStep 1136435 = 1704653) B1704653
theorem B11032373 : Blo 754331 11032373 := bstep (se 5 (by rfl) ⟨517142, by rfl⟩ : syracuseStep 11032373 = 1034285) B1034285
theorem B1136465 : Blo 754331 1136465 := bstep (se 2 (by rfl) ⟨426174, by rfl⟩ : syracuseStep 1136465 = 852349) B852349
theorem B1136483 : Blo 754331 1136483 := bstep (se 1 (by rfl) ⟨852362, by rfl⟩ : syracuseStep 1136483 = 1704725) B1704725
theorem B972659 : Blo 754331 972659 := bstep (se 1 (by rfl) ⟨729494, by rfl⟩ : syracuseStep 972659 = 1458989) B1458989
theorem B1136513 : Blo 754331 1136513 := bstep (se 2 (by rfl) ⟨426192, by rfl⟩ : syracuseStep 1136513 = 852385) B852385
theorem B1136531 : Blo 754331 1136531 := bstep (se 1 (by rfl) ⟨852398, by rfl⟩ : syracuseStep 1136531 = 1704797) B1704797
theorem B3823523 : Blo 754331 3823523 := bstep (se 1 (by rfl) ⟨2867642, by rfl⟩ : syracuseStep 3823523 = 5735285) B5735285
theorem B1136561 : Blo 754331 1136561 := bstep (se 2 (by rfl) ⟨426210, by rfl⟩ : syracuseStep 1136561 = 852421) B852421
theorem B1136579 : Blo 754331 1136579 := bstep (se 1 (by rfl) ⟨852434, by rfl⟩ : syracuseStep 1136579 = 1704869) B1704869
theorem B1136609 : Blo 754331 1136609 := bstep (se 2 (by rfl) ⟨426228, by rfl⟩ : syracuseStep 1136609 = 852457) B852457
theorem B1136627 : Blo 754331 1136627 := bstep (se 1 (by rfl) ⟨852470, by rfl⟩ : syracuseStep 1136627 = 1704941) B1704941
theorem B1136657 : Blo 754331 1136657 := bstep (se 2 (by rfl) ⟨426246, by rfl⟩ : syracuseStep 1136657 = 852493) B852493
theorem B1136675 : Blo 754331 1136675 := bstep (se 1 (by rfl) ⟨852506, by rfl⟩ : syracuseStep 1136675 = 1705013) B1705013
theorem B1136705 : Blo 754331 1136705 := bstep (se 2 (by rfl) ⟨426264, by rfl⟩ : syracuseStep 1136705 = 852529) B852529
theorem B1136723 : Blo 754331 1136723 := bstep (se 1 (by rfl) ⟨852542, by rfl⟩ : syracuseStep 1136723 = 1705085) B1705085
theorem B1529969 : Blo 754331 1529969 := bstep (se 2 (by rfl) ⟨573738, by rfl⟩ : syracuseStep 1529969 = 1147477) B1147477
theorem B1136753 : Blo 754331 1136753 := bstep (se 2 (by rfl) ⟨426282, by rfl⟩ : syracuseStep 1136753 = 852565) B852565
theorem B1136771 : Blo 754331 1136771 := bstep (se 1 (by rfl) ⟨852578, by rfl⟩ : syracuseStep 1136771 = 1705157) B1705157
theorem B1136801 : Blo 754331 1136801 := bstep (se 2 (by rfl) ⟨426300, by rfl⟩ : syracuseStep 1136801 = 852601) B852601
theorem B1136819 : Blo 754331 1136819 := bstep (se 1 (by rfl) ⟨852614, by rfl⟩ : syracuseStep 1136819 = 1705229) B1705229
theorem B1136849 : Blo 754331 1136849 := bstep (se 2 (by rfl) ⟨426318, by rfl⟩ : syracuseStep 1136849 = 852637) B852637
theorem B1136867 : Blo 754331 1136867 := bstep (se 1 (by rfl) ⟨852650, by rfl⟩ : syracuseStep 1136867 = 1705301) B1705301
theorem B5757155 : Blo 754331 5757155 := bstep (se 1 (by rfl) ⟨4317866, by rfl⟩ : syracuseStep 5757155 = 8635733) B8635733
theorem B1136897 : Blo 754331 1136897 := bstep (se 2 (by rfl) ⟨426336, by rfl⟩ : syracuseStep 1136897 = 852673) B852673
theorem B2545937 : Blo 754331 2545937 := bstep (se 2 (by rfl) ⟨954726, by rfl⟩ : syracuseStep 2545937 = 1909453) B1909453
theorem B1136915 : Blo 754331 1136915 := bstep (se 1 (by rfl) ⟨852686, by rfl⟩ : syracuseStep 1136915 = 1705373) B1705373
theorem B1136945 : Blo 754331 1136945 := bstep (se 2 (by rfl) ⟨426354, by rfl⟩ : syracuseStep 1136945 = 852709) B852709
theorem B1136963 : Blo 754331 1136963 := bstep (se 1 (by rfl) ⟨852722, by rfl⟩ : syracuseStep 1136963 = 1705445) B1705445
theorem B1136993 : Blo 754331 1136993 := bstep (se 2 (by rfl) ⟨426372, by rfl⟩ : syracuseStep 1136993 = 852745) B852745
theorem B1137011 : Blo 754331 1137011 := bstep (se 1 (by rfl) ⟨852758, by rfl⟩ : syracuseStep 1137011 = 1705517) B1705517
theorem B1137041 : Blo 754331 1137041 := bstep (se 2 (by rfl) ⟨426390, by rfl⟩ : syracuseStep 1137041 = 852781) B852781
theorem B1137059 : Blo 754331 1137059 := bstep (se 1 (by rfl) ⟨852794, by rfl⟩ : syracuseStep 1137059 = 1705589) B1705589
theorem B809395 : Blo 754331 809395 := bstep (se 1 (by rfl) ⟨607046, by rfl⟩ : syracuseStep 809395 = 1214093) B1214093
theorem B1137089 : Blo 754331 1137089 := bstep (se 2 (by rfl) ⟨426408, by rfl⟩ : syracuseStep 1137089 = 852817) B852817
theorem B4315589 : Blo 754331 4315589 := bstep (se 4 (by rfl) ⟨404586, by rfl⟩ : syracuseStep 4315589 = 809173) B809173
theorem B1137107 : Blo 754331 1137107 := bstep (se 1 (by rfl) ⟨852830, by rfl⟩ : syracuseStep 1137107 = 1705661) B1705661
theorem B1137137 : Blo 754331 1137137 := bstep (se 2 (by rfl) ⟨426426, by rfl⟩ : syracuseStep 1137137 = 852853) B852853
theorem B1137155 : Blo 754331 1137155 := bstep (se 1 (by rfl) ⟨852866, by rfl⟩ : syracuseStep 1137155 = 1705733) B1705733
theorem B1137185 : Blo 754331 1137185 := bstep (se 2 (by rfl) ⟨426444, by rfl⟩ : syracuseStep 1137185 = 852889) B852889
theorem B1137203 : Blo 754331 1137203 := bstep (se 1 (by rfl) ⟨852902, by rfl⟩ : syracuseStep 1137203 = 1705805) B1705805
theorem B2185805 : Blo 754331 2185805 := bstep (se 3 (by rfl) ⟨409838, by rfl⟩ : syracuseStep 2185805 = 819677) B819677
theorem B1137233 : Blo 754331 1137233 := bstep (se 2 (by rfl) ⟨426462, by rfl⟩ : syracuseStep 1137233 = 852925) B852925
theorem B1137251 : Blo 754331 1137251 := bstep (se 1 (by rfl) ⟨852938, by rfl⟩ : syracuseStep 1137251 = 1705877) B1705877
theorem B1137281 : Blo 754331 1137281 := bstep (se 2 (by rfl) ⟨426480, by rfl⟩ : syracuseStep 1137281 = 852961) B852961
theorem B1137299 : Blo 754331 1137299 := bstep (se 1 (by rfl) ⟨852974, by rfl⟩ : syracuseStep 1137299 = 1705949) B1705949
theorem B1137329 : Blo 754331 1137329 := bstep (se 2 (by rfl) ⟨426498, by rfl⟩ : syracuseStep 1137329 = 852997) B852997
theorem B1137347 : Blo 754331 1137347 := bstep (se 1 (by rfl) ⟨853010, by rfl⟩ : syracuseStep 1137347 = 1706021) B1706021
theorem B3824333 : Blo 754331 3824333 := bstep (se 3 (by rfl) ⟨717062, by rfl⟩ : syracuseStep 3824333 = 1434125) B1434125
theorem B1137377 : Blo 754331 1137377 := bstep (se 2 (by rfl) ⟨426516, by rfl⟩ : syracuseStep 1137377 = 853033) B853033
theorem B1137395 : Blo 754331 1137395 := bstep (se 1 (by rfl) ⟨853046, by rfl⟩ : syracuseStep 1137395 = 1706093) B1706093
theorem B1137425 : Blo 754331 1137425 := bstep (se 2 (by rfl) ⟨426534, by rfl⟩ : syracuseStep 1137425 = 853069) B853069
theorem B1137443 : Blo 754331 1137443 := bstep (se 1 (by rfl) ⟨853082, by rfl⟩ : syracuseStep 1137443 = 1706165) B1706165
theorem B2546477 : Blo 754331 2546477 := bstep (se 3 (by rfl) ⟨477464, by rfl⟩ : syracuseStep 2546477 = 954929) B954929
theorem B1137473 : Blo 754331 1137473 := bstep (se 2 (by rfl) ⟨426552, by rfl⟩ : syracuseStep 1137473 = 853105) B853105
theorem B1137491 : Blo 754331 1137491 := bstep (se 1 (by rfl) ⟨853118, by rfl⟩ : syracuseStep 1137491 = 1706237) B1706237
theorem B2546531 : Blo 754331 2546531 := bstep (se 1 (by rfl) ⟨1909898, by rfl⟩ : syracuseStep 2546531 = 3819797) B3819797
theorem B1432561 : Blo 754331 1432561 := bstep (se 2 (by rfl) ⟨537210, by rfl⟩ : syracuseStep 1432561 = 1074421) B1074421
theorem B9428021 : Blo 754331 9428021 := bstep (se 5 (by rfl) ⟨441938, by rfl⟩ : syracuseStep 9428021 = 883877) B883877
theorem B2546801 : Blo 754331 2546801 := bstep (se 2 (by rfl) ⟨955050, by rfl⟩ : syracuseStep 2546801 = 1910101) B1910101
theorem B4316273 : Blo 754331 4316273 := bstep (se 2 (by rfl) ⟨1618602, by rfl⟩ : syracuseStep 4316273 = 3237205) B3237205
theorem B2153603 : Blo 754331 2153603 := bstep (se 1 (by rfl) ⟨1615202, by rfl⟩ : syracuseStep 2153603 = 3230405) B3230405
theorem B1432721 : Blo 754331 1432721 := bstep (se 2 (by rfl) ⟨537270, by rfl⟩ : syracuseStep 1432721 = 1074541) B1074541
theorem B1433123 : Blo 754331 1433123 := bstep (se 1 (by rfl) ⟨1074842, by rfl⟩ : syracuseStep 1433123 = 2149685) B2149685
theorem B2547341 : Blo 754331 2547341 := bstep (se 3 (by rfl) ⟨477626, by rfl⟩ : syracuseStep 2547341 = 955253) B955253
theorem B2547395 : Blo 754331 2547395 := bstep (se 1 (by rfl) ⟨1910546, by rfl⟩ : syracuseStep 2547395 = 3821093) B3821093
theorem B2875085 : Blo 754331 2875085 := bstep (se 3 (by rfl) ⟨539078, by rfl⟩ : syracuseStep 2875085 = 1078157) B1078157
theorem B4087685 : Blo 754331 4087685 := bstep (se 4 (by rfl) ⟨383220, by rfl⟩ : syracuseStep 4087685 = 766441) B766441
theorem B2547665 : Blo 754331 2547665 := bstep (se 2 (by rfl) ⟨955374, by rfl⟩ : syracuseStep 2547665 = 1910749) B1910749
theorem B2187281 : Blo 754331 2187281 := bstep (se 2 (by rfl) ⟨820230, by rfl⟩ : syracuseStep 2187281 = 1640461) B1640461
theorem B27648053 : Blo 754331 27648053 := bstep (se 5 (by rfl) ⟨1296002, by rfl⟩ : syracuseStep 27648053 = 2592005) B2592005
theorem B2187377 : Blo 754331 2187377 := bstep (se 2 (by rfl) ⟨820266, by rfl⟩ : syracuseStep 2187377 = 1640533) B1640533
theorem B6119621 : Blo 754331 6119621 := bstep (se 4 (by rfl) ⟨573714, by rfl⟩ : syracuseStep 6119621 = 1147429) B1147429
theorem B4251973 : Blo 754331 4251973 := bstep (se 4 (by rfl) ⟨398622, by rfl⟩ : syracuseStep 4251973 = 797245) B797245
theorem B2908493 : Blo 754331 2908493 := bstep (se 3 (by rfl) ⟨545342, by rfl⟩ : syracuseStep 2908493 = 1090685) B1090685
theorem B2154833 : Blo 754331 2154833 := bstep (se 2 (by rfl) ⟨808062, by rfl⟩ : syracuseStep 2154833 = 1616125) B1616125
theorem B909667 : Blo 754331 909667 := bstep (se 1 (by rfl) ⟨682250, by rfl⟩ : syracuseStep 909667 = 1364501) B1364501
theorem B1532305 : Blo 754331 1532305 := bstep (se 2 (by rfl) ⟨574614, by rfl⟩ : syracuseStep 1532305 = 1149229) B1149229
theorem B1434019 : Blo 754331 1434019 := bstep (se 1 (by rfl) ⟨1075514, by rfl⟩ : syracuseStep 1434019 = 2151029) B2151029
theorem B1532387 : Blo 754331 1532387 := bstep (se 1 (by rfl) ⟨1149290, by rfl⟩ : syracuseStep 1532387 = 2298581) B2298581
theorem B2548205 : Blo 754331 2548205 := bstep (se 3 (by rfl) ⟨477788, by rfl⟩ : syracuseStep 2548205 = 955577) B955577
theorem B2548259 : Blo 754331 2548259 := bstep (se 1 (by rfl) ⟨1911194, by rfl⟩ : syracuseStep 2548259 = 3822389) B3822389
theorem B909859 : Blo 754331 909859 := bstep (se 1 (by rfl) ⟨682394, by rfl⟩ : syracuseStep 909859 = 1364789) B1364789
theorem B4317731 : Blo 754331 4317731 := bstep (se 1 (by rfl) ⟨3238298, by rfl⟩ : syracuseStep 4317731 = 6476597) B6476597
theorem B1434179 : Blo 754331 1434179 := bstep (se 1 (by rfl) ⟨1075634, by rfl⟩ : syracuseStep 1434179 = 2151269) B2151269
theorem B910003 : Blo 754331 910003 := bstep (se 1 (by rfl) ⟨682502, by rfl⟩ : syracuseStep 910003 = 1365005) B1365005
theorem B2450189 : Blo 754331 2450189 := bstep (se 3 (by rfl) ⟨459410, by rfl⟩ : syracuseStep 2450189 = 918821) B918821
theorem B2548529 : Blo 754331 2548529 := bstep (se 2 (by rfl) ⟨955698, by rfl⟩ : syracuseStep 2548529 = 1911397) B1911397
theorem B1729457 : Blo 754331 1729457 := bstep (se 2 (by rfl) ⟨648546, by rfl⟩ : syracuseStep 1729457 = 1297093) B1297093
theorem B1074227 : Blo 754331 1074227 := bstep (se 1 (by rfl) ⟨805670, by rfl⟩ : syracuseStep 1074227 = 1611341) B1611341
theorem B6448369 : Blo 754331 6448369 := bstep (se 2 (by rfl) ⟨2418138, by rfl⟩ : syracuseStep 6448369 = 4836277) B4836277
theorem B4842737 : Blo 754331 4842737 := bstep (se 2 (by rfl) ⟨1816026, by rfl⟩ : syracuseStep 4842737 = 3632053) B3632053
theorem B3237155 : Blo 754331 3237155 := bstep (se 1 (by rfl) ⟨2427866, by rfl⟩ : syracuseStep 3237155 = 4855733) B4855733
theorem B2549069 : Blo 754331 2549069 := bstep (se 3 (by rfl) ⟨477950, by rfl⟩ : syracuseStep 2549069 = 955901) B955901
theorem B2549123 : Blo 754331 2549123 := bstep (se 1 (by rfl) ⟨1911842, by rfl⟩ : syracuseStep 2549123 = 3823685) B3823685
theorem B3827249 : Blo 754331 3827249 := bstep (se 2 (by rfl) ⟨1435218, by rfl⟩ : syracuseStep 3827249 = 2870437) B2870437
theorem B1435249 : Blo 754331 1435249 := bstep (se 2 (by rfl) ⟨538218, by rfl⟩ : syracuseStep 1435249 = 1076437) B1076437
theorem B2549393 : Blo 754331 2549393 := bstep (se 2 (by rfl) ⟨956022, by rfl⟩ : syracuseStep 2549393 = 1912045) B1912045
theorem B1074865 : Blo 754331 1074865 := bstep (se 2 (by rfl) ⟨403074, by rfl⟩ : syracuseStep 1074865 = 806149) B806149
theorem B1697489 : Blo 754331 1697489 := bstep (se 2 (by rfl) ⟨636558, by rfl⟩ : syracuseStep 1697489 = 1273117) B1273117
theorem B1697507 : Blo 754331 1697507 := bstep (se 1 (by rfl) ⟨1273130, by rfl⟩ : syracuseStep 1697507 = 2546261) B2546261
theorem B2156291 : Blo 754331 2156291 := bstep (se 1 (by rfl) ⟨1617218, by rfl⟩ : syracuseStep 2156291 = 3234437) B3234437
theorem B1074979 : Blo 754331 1074979 := bstep (se 1 (by rfl) ⟨806234, by rfl⟩ : syracuseStep 1074979 = 1612469) B1612469
theorem B1697777 : Blo 754331 1697777 := bstep (se 2 (by rfl) ⟨636666, by rfl⟩ : syracuseStep 1697777 = 1273333) B1273333
theorem B1697795 : Blo 754331 1697795 := bstep (se 1 (by rfl) ⟨1273346, by rfl⟩ : syracuseStep 1697795 = 2546693) B2546693
theorem B2549933 : Blo 754331 2549933 := bstep (se 3 (by rfl) ⟨478112, by rfl⟩ : syracuseStep 2549933 = 956225) B956225
theorem B2549987 : Blo 754331 2549987 := bstep (se 1 (by rfl) ⟨1912490, by rfl⟩ : syracuseStep 2549987 = 3824981) B3824981
theorem B9824483 : Blo 754331 9824483 := bstep (se 1 (by rfl) ⟨7368362, by rfl⟩ : syracuseStep 9824483 = 14736725) B14736725
theorem B1698065 : Blo 754331 1698065 := bstep (se 2 (by rfl) ⟨636774, by rfl⟩ : syracuseStep 1698065 = 1273549) B1273549
theorem B1698083 : Blo 754331 1698083 := bstep (se 1 (by rfl) ⟨1273562, by rfl⟩ : syracuseStep 1698083 = 2547125) B2547125
theorem B2550257 : Blo 754331 2550257 := bstep (se 2 (by rfl) ⟨956346, by rfl⟩ : syracuseStep 2550257 = 1912693) B1912693
theorem B2419217 : Blo 754331 2419217 := bstep (se 2 (by rfl) ⟨907206, by rfl⟩ : syracuseStep 2419217 = 1814413) B1814413
theorem B5171747 : Blo 754331 5171747 := bstep (se 1 (by rfl) ⟨3878810, by rfl⟩ : syracuseStep 5171747 = 7757621) B7757621
theorem B2157101 : Blo 754331 2157101 := bstep (se 3 (by rfl) ⟨404456, by rfl⟩ : syracuseStep 2157101 = 808913) B808913
theorem B1698353 : Blo 754331 1698353 := bstep (se 2 (by rfl) ⟨636882, by rfl⟩ : syracuseStep 1698353 = 1273765) B1273765
theorem B2878001 : Blo 754331 2878001 := bstep (se 2 (by rfl) ⟨1079250, by rfl⟩ : syracuseStep 2878001 = 2158501) B2158501
theorem B8612405 : Blo 754331 8612405 := bstep (se 5 (by rfl) ⟨403706, by rfl⟩ : syracuseStep 8612405 = 807413) B807413
theorem B1698371 : Blo 754331 1698371 := bstep (se 1 (by rfl) ⟨1273778, by rfl⟩ : syracuseStep 1698371 = 2547557) B2547557
theorem B2419267 : Blo 754331 2419267 := bstep (se 1 (by rfl) ⟨1814450, by rfl⟩ : syracuseStep 2419267 = 3628901) B3628901
theorem B1436305 : Blo 754331 1436305 := bstep (se 2 (by rfl) ⟨538614, by rfl⟩ : syracuseStep 1436305 = 1077229) B1077229
theorem B9693877 : Blo 754331 9693877 := bstep (se 5 (by rfl) ⟨454400, by rfl⟩ : syracuseStep 9693877 = 908801) B908801
theorem B2157293 : Blo 754331 2157293 := bstep (se 3 (by rfl) ⟨404492, by rfl⟩ : syracuseStep 2157293 = 808985) B808985
theorem B1698641 : Blo 754331 1698641 := bstep (se 2 (by rfl) ⟨636990, by rfl⟩ : syracuseStep 1698641 = 1273981) B1273981
theorem B1698659 : Blo 754331 1698659 := bstep (se 1 (by rfl) ⟨1273994, by rfl⟩ : syracuseStep 1698659 = 2547989) B2547989
theorem B3828707 : Blo 754331 3828707 := bstep (se 1 (by rfl) ⟨2871530, by rfl⟩ : syracuseStep 3828707 = 5743061) B5743061
theorem B2550797 : Blo 754331 2550797 := bstep (se 3 (by rfl) ⟨478274, by rfl⟩ : syracuseStep 2550797 = 956549) B956549
theorem B1436707 : Blo 754331 1436707 := bstep (se 1 (by rfl) ⟨1077530, by rfl⟩ : syracuseStep 1436707 = 2155061) B2155061
theorem B2550851 : Blo 754331 2550851 := bstep (se 1 (by rfl) ⟨1913138, by rfl⟩ : syracuseStep 2550851 = 3826277) B3826277
theorem B1436753 : Blo 754331 1436753 := bstep (se 2 (by rfl) ⟨538782, by rfl⟩ : syracuseStep 1436753 = 1077565) B1077565
theorem B1076323 : Blo 754331 1076323 := bstep (se 1 (by rfl) ⟨807242, by rfl⟩ : syracuseStep 1076323 = 1614485) B1614485
theorem B1698929 : Blo 754331 1698929 := bstep (se 2 (by rfl) ⟨637098, by rfl⟩ : syracuseStep 1698929 = 1274197) B1274197
theorem B1698947 : Blo 754331 1698947 := bstep (se 1 (by rfl) ⟨1274210, by rfl⟩ : syracuseStep 1698947 = 2548421) B2548421
theorem B1273009 : Blo 754331 1273009 := bstep (se 2 (by rfl) ⟨477378, by rfl⟩ : syracuseStep 1273009 = 954757) B954757
theorem B1273043 : Blo 754331 1273043 := bstep (se 1 (by rfl) ⟨954782, by rfl⟩ : syracuseStep 1273043 = 1909565) B1909565
theorem B3239153 : Blo 754331 3239153 := bstep (se 2 (by rfl) ⟨1214682, by rfl⟩ : syracuseStep 3239153 = 2429365) B2429365
theorem B2551121 : Blo 754331 2551121 := bstep (se 2 (by rfl) ⟨956670, by rfl⟩ : syracuseStep 2551121 = 1913341) B1913341
theorem B1273171 : Blo 754331 1273171 := bstep (se 1 (by rfl) ⟨954878, by rfl⟩ : syracuseStep 1273171 = 1909757) B1909757
theorem B1437041 : Blo 754331 1437041 := bstep (se 2 (by rfl) ⟨538890, by rfl⟩ : syracuseStep 1437041 = 1077781) B1077781
theorem B1699217 : Blo 754331 1699217 := bstep (se 2 (by rfl) ⟨637206, by rfl⟩ : syracuseStep 1699217 = 1274413) B1274413
theorem B2420113 : Blo 754331 2420113 := bstep (se 2 (by rfl) ⟨907542, by rfl⟩ : syracuseStep 2420113 = 1815085) B1815085
theorem B1699235 : Blo 754331 1699235 := bstep (se 1 (by rfl) ⟨1274426, by rfl⟩ : syracuseStep 1699235 = 2548853) B2548853
theorem B1273313 : Blo 754331 1273313 := bstep (se 2 (by rfl) ⟨477492, by rfl⟩ : syracuseStep 1273313 = 954985) B954985
theorem B1273441 : Blo 754331 1273441 := bstep (se 2 (by rfl) ⟨477540, by rfl⟩ : syracuseStep 1273441 = 955081) B955081
theorem B1273475 : Blo 754331 1273475 := bstep (se 1 (by rfl) ⟨955106, by rfl⟩ : syracuseStep 1273475 = 1910213) B1910213
theorem B3272333 : Blo 754331 3272333 := bstep (se 3 (by rfl) ⟨613562, by rfl⟩ : syracuseStep 3272333 = 1227125) B1227125
theorem B4845197 : Blo 754331 4845197 := bstep (se 3 (by rfl) ⟨908474, by rfl⟩ : syracuseStep 4845197 = 1816949) B1816949
theorem B1699505 : Blo 754331 1699505 := bstep (se 2 (by rfl) ⟨637314, by rfl⟩ : syracuseStep 1699505 = 1274629) B1274629
theorem B1699523 : Blo 754331 1699523 := bstep (se 1 (by rfl) ⟨1274642, by rfl⟩ : syracuseStep 1699523 = 2549285) B2549285
theorem B4419269 : Blo 754331 4419269 := bstep (se 4 (by rfl) ⟨414306, by rfl⟩ : syracuseStep 4419269 = 828613) B828613
theorem B4091597 : Blo 754331 4091597 := bstep (se 3 (by rfl) ⟨767174, by rfl⟩ : syracuseStep 4091597 = 1534349) B1534349
theorem B2158285 : Blo 754331 2158285 := bstep (se 3 (by rfl) ⟨404678, by rfl⟩ : syracuseStep 2158285 = 809357) B809357
theorem B8744689 : Blo 754331 8744689 := bstep (se 2 (by rfl) ⟨3279258, by rfl⟩ : syracuseStep 8744689 = 6558517) B6558517
theorem B1273603 : Blo 754331 1273603 := bstep (se 1 (by rfl) ⟨955202, by rfl⟩ : syracuseStep 1273603 = 1910405) B1910405
theorem B3829517 : Blo 754331 3829517 := bstep (se 3 (by rfl) ⟨718034, by rfl⟩ : syracuseStep 3829517 = 1436069) B1436069
theorem B2551661 : Blo 754331 2551661 := bstep (se 3 (by rfl) ⟨478436, by rfl⟩ : syracuseStep 2551661 = 956873) B956873
theorem B1273745 : Blo 754331 1273745 := bstep (se 2 (by rfl) ⟨477654, by rfl⟩ : syracuseStep 1273745 = 955309) B955309
theorem B2551715 : Blo 754331 2551715 := bstep (se 1 (by rfl) ⟨1913786, by rfl⟩ : syracuseStep 2551715 = 3827573) B3827573
theorem B1699793 : Blo 754331 1699793 := bstep (se 2 (by rfl) ⟨637422, by rfl⟩ : syracuseStep 1699793 = 1274845) B1274845
theorem B1699811 : Blo 754331 1699811 := bstep (se 1 (by rfl) ⟨1274858, by rfl⟩ : syracuseStep 1699811 = 2549717) B2549717
theorem B1273873 : Blo 754331 1273873 := bstep (se 2 (by rfl) ⟨477702, by rfl⟩ : syracuseStep 1273873 = 955405) B955405
theorem B1273907 : Blo 754331 1273907 := bstep (se 1 (by rfl) ⟨955430, by rfl⟩ : syracuseStep 1273907 = 1910861) B1910861
theorem B1437763 : Blo 754331 1437763 := bstep (se 1 (by rfl) ⟨1078322, by rfl⟩ : syracuseStep 1437763 = 2156645) B2156645
theorem B1208449 : Blo 754331 1208449 := bstep (se 2 (by rfl) ⟨453168, by rfl⟩ : syracuseStep 1208449 = 906337) B906337
theorem B2551985 : Blo 754331 2551985 := bstep (se 2 (by rfl) ⟨956994, by rfl⟩ : syracuseStep 2551985 = 1913989) B1913989
theorem B1274035 : Blo 754331 1274035 := bstep (se 1 (by rfl) ⟨955526, by rfl⟩ : syracuseStep 1274035 = 1911053) B1911053
theorem B1077457 : Blo 754331 1077457 := bstep (se 2 (by rfl) ⟨404046, by rfl⟩ : syracuseStep 1077457 = 808093) B808093
theorem B1700081 : Blo 754331 1700081 := bstep (se 2 (by rfl) ⟨637530, by rfl⟩ : syracuseStep 1700081 = 1275061) B1275061
theorem B1700099 : Blo 754331 1700099 := bstep (se 1 (by rfl) ⟨1275074, by rfl⟩ : syracuseStep 1700099 = 2550149) B2550149
theorem B1995043 : Blo 754331 1995043 := bstep (se 1 (by rfl) ⟨1496282, by rfl⟩ : syracuseStep 1995043 = 2992565) B2992565
theorem B2912561 : Blo 754331 2912561 := bstep (se 2 (by rfl) ⟨1092210, by rfl⟩ : syracuseStep 2912561 = 2184421) B2184421
theorem B1077553 : Blo 754331 1077553 := bstep (se 2 (by rfl) ⟨404082, by rfl⟩ : syracuseStep 1077553 = 808165) B808165
theorem B1274177 : Blo 754331 1274177 := bstep (se 2 (by rfl) ⟨477816, by rfl⟩ : syracuseStep 1274177 = 955633) B955633
theorem B1274305 : Blo 754331 1274305 := bstep (se 2 (by rfl) ⟨477864, by rfl⟩ : syracuseStep 1274305 = 955729) B955729
theorem B1274339 : Blo 754331 1274339 := bstep (se 1 (by rfl) ⟨955754, by rfl⟩ : syracuseStep 1274339 = 1911509) B1911509
theorem B1438211 : Blo 754331 1438211 := bstep (se 1 (by rfl) ⟨1078658, by rfl⟩ : syracuseStep 1438211 = 2157317) B2157317
theorem B1700369 : Blo 754331 1700369 := bstep (se 2 (by rfl) ⟨637638, by rfl⟩ : syracuseStep 1700369 = 1275277) B1275277
theorem B1700387 : Blo 754331 1700387 := bstep (se 1 (by rfl) ⟨1275290, by rfl⟩ : syracuseStep 1700387 = 2550581) B2550581
theorem B1274467 : Blo 754331 1274467 := bstep (se 1 (by rfl) ⟨955850, by rfl⟩ : syracuseStep 1274467 = 1911701) B1911701
theorem B2552525 : Blo 754331 2552525 := bstep (se 3 (by rfl) ⟨478598, by rfl⟩ : syracuseStep 2552525 = 957197) B957197
theorem B1274609 : Blo 754331 1274609 := bstep (se 2 (by rfl) ⟨477978, by rfl⟩ : syracuseStep 1274609 = 955957) B955957
theorem B2552579 : Blo 754331 2552579 := bstep (se 1 (by rfl) ⟨1914434, by rfl⟩ : syracuseStep 2552579 = 3828869) B3828869
theorem B848659 : Blo 754331 848659 := bstep (se 1 (by rfl) ⟨636494, by rfl⟩ : syracuseStep 848659 = 1272989) B1272989
theorem B1078049 : Blo 754331 1078049 := bstep (se 2 (by rfl) ⟨404268, by rfl⟩ : syracuseStep 1078049 = 808537) B808537
theorem B1438499 : Blo 754331 1438499 := bstep (se 1 (by rfl) ⟨1078874, by rfl⟩ : syracuseStep 1438499 = 2157749) B2157749
theorem B1700657 : Blo 754331 1700657 := bstep (se 2 (by rfl) ⟨637746, by rfl⟩ : syracuseStep 1700657 = 1275493) B1275493
theorem B1700675 : Blo 754331 1700675 := bstep (se 1 (by rfl) ⟨1275506, by rfl⟩ : syracuseStep 1700675 = 2551013) B2551013
theorem B1274737 : Blo 754331 1274737 := bstep (se 2 (by rfl) ⟨478026, by rfl⟩ : syracuseStep 1274737 = 956053) B956053
theorem B1274771 : Blo 754331 1274771 := bstep (se 1 (by rfl) ⟨956078, by rfl⟩ : syracuseStep 1274771 = 1912157) B1912157
theorem B848803 : Blo 754331 848803 := bstep (se 1 (by rfl) ⟨636602, by rfl⟩ : syracuseStep 848803 = 1273205) B1273205
theorem B2421677 : Blo 754331 2421677 := bstep (se 3 (by rfl) ⟨454064, by rfl⟩ : syracuseStep 2421677 = 908129) B908129
theorem B2552849 : Blo 754331 2552849 := bstep (se 2 (by rfl) ⟨957318, by rfl⟩ : syracuseStep 2552849 = 1914637) B1914637
theorem B1274899 : Blo 754331 1274899 := bstep (se 1 (by rfl) ⟨956174, by rfl⟩ : syracuseStep 1274899 = 1912349) B1912349
theorem B1209377 : Blo 754331 1209377 := bstep (se 2 (by rfl) ⟨453516, by rfl⟩ : syracuseStep 1209377 = 907033) B907033
theorem B2585645 : Blo 754331 2585645 := bstep (se 3 (by rfl) ⟨484808, by rfl⟩ : syracuseStep 2585645 = 969617) B969617
theorem B848947 : Blo 754331 848947 := bstep (se 1 (by rfl) ⟨636710, by rfl⟩ : syracuseStep 848947 = 1273421) B1273421
theorem B5731397 : Blo 754331 5731397 := bstep (se 4 (by rfl) ⟨537318, by rfl⟩ : syracuseStep 5731397 = 1074637) B1074637
theorem B1700945 : Blo 754331 1700945 := bstep (se 2 (by rfl) ⟨637854, by rfl⟩ : syracuseStep 1700945 = 1275709) B1275709
theorem B1700963 : Blo 754331 1700963 := bstep (se 1 (by rfl) ⟨1275722, by rfl⟩ : syracuseStep 1700963 = 2551445) B2551445
theorem B1275041 : Blo 754331 1275041 := bstep (se 2 (by rfl) ⟨478140, by rfl⟩ : syracuseStep 1275041 = 956281) B956281
theorem B849091 : Blo 754331 849091 := bstep (se 1 (by rfl) ⟨636818, by rfl⟩ : syracuseStep 849091 = 1273637) B1273637
theorem B1275169 : Blo 754331 1275169 := bstep (se 2 (by rfl) ⟨478188, by rfl⟩ : syracuseStep 1275169 = 956377) B956377
theorem B1275203 : Blo 754331 1275203 := bstep (se 1 (by rfl) ⟨956402, by rfl⟩ : syracuseStep 1275203 = 1912805) B1912805
theorem B849235 : Blo 754331 849235 := bstep (se 1 (by rfl) ⟨636926, by rfl⟩ : syracuseStep 849235 = 1273853) B1273853
theorem B1701233 : Blo 754331 1701233 := bstep (se 2 (by rfl) ⟨637962, by rfl⟩ : syracuseStep 1701233 = 1275925) B1275925
theorem B1701251 : Blo 754331 1701251 := bstep (se 1 (by rfl) ⟨1275938, by rfl⟩ : syracuseStep 1701251 = 2551877) B2551877
theorem B1275331 : Blo 754331 1275331 := bstep (se 1 (by rfl) ⟨956498, by rfl⟩ : syracuseStep 1275331 = 1912997) B1912997
theorem B849379 : Blo 754331 849379 := bstep (se 1 (by rfl) ⟨637034, by rfl⟩ : syracuseStep 849379 = 1274069) B1274069
theorem B4093411 : Blo 754331 4093411 := bstep (se 1 (by rfl) ⟨3070058, by rfl⟩ : syracuseStep 4093411 = 6140117) B6140117
theorem B6911501 : Blo 754331 6911501 := bstep (se 3 (by rfl) ⟨1295906, by rfl⟩ : syracuseStep 6911501 = 2591813) B2591813
theorem B2553389 : Blo 754331 2553389 := bstep (se 3 (by rfl) ⟨478760, by rfl⟩ : syracuseStep 2553389 = 957521) B957521
theorem B1275473 : Blo 754331 1275473 := bstep (se 2 (by rfl) ⟨478302, by rfl⟩ : syracuseStep 1275473 = 956605) B956605
theorem B2553443 : Blo 754331 2553443 := bstep (se 1 (by rfl) ⟨1915082, by rfl⟩ : syracuseStep 2553443 = 3830165) B3830165
theorem B849523 : Blo 754331 849523 := bstep (se 1 (by rfl) ⟨637142, by rfl⟩ : syracuseStep 849523 = 1274285) B1274285
theorem B1078915 : Blo 754331 1078915 := bstep (se 1 (by rfl) ⟨809186, by rfl⟩ : syracuseStep 1078915 = 1618373) B1618373
theorem B1701521 : Blo 754331 1701521 := bstep (se 2 (by rfl) ⟨638070, by rfl⟩ : syracuseStep 1701521 = 1276141) B1276141
theorem B1701539 : Blo 754331 1701539 := bstep (se 1 (by rfl) ⟨1276154, by rfl⟩ : syracuseStep 1701539 = 2552309) B2552309
theorem B1275601 : Blo 754331 1275601 := bstep (se 2 (by rfl) ⟨478350, by rfl⟩ : syracuseStep 1275601 = 956701) B956701
theorem B1439441 : Blo 754331 1439441 := bstep (se 2 (by rfl) ⟨539790, by rfl⟩ : syracuseStep 1439441 = 1079581) B1079581
theorem B1079011 : Blo 754331 1079011 := bstep (se 1 (by rfl) ⟨809258, by rfl⟩ : syracuseStep 1079011 = 1618517) B1618517
theorem B4978417 : Blo 754331 4978417 := bstep (se 2 (by rfl) ⟨1866906, by rfl⟩ : syracuseStep 4978417 = 3733813) B3733813
theorem B1275635 : Blo 754331 1275635 := bstep (se 1 (by rfl) ⟨956726, by rfl⟩ : syracuseStep 1275635 = 1913453) B1913453
theorem B849667 : Blo 754331 849667 := bstep (se 1 (by rfl) ⟨637250, by rfl⟩ : syracuseStep 849667 = 1274501) B1274501
theorem B1210211 : Blo 754331 1210211 := bstep (se 1 (by rfl) ⟨907658, by rfl⟩ : syracuseStep 1210211 = 1815317) B1815317
theorem B2553713 : Blo 754331 2553713 := bstep (se 2 (by rfl) ⟨957642, by rfl⟩ : syracuseStep 2553713 = 1915285) B1915285
theorem B1275763 : Blo 754331 1275763 := bstep (se 1 (by rfl) ⟨956822, by rfl⟩ : syracuseStep 1275763 = 1913645) B1913645
theorem B1210243 : Blo 754331 1210243 := bstep (se 1 (by rfl) ⟨907682, by rfl⟩ : syracuseStep 1210243 = 1815365) B1815365
theorem B849811 : Blo 754331 849811 := bstep (se 1 (by rfl) ⟨637358, by rfl⟩ : syracuseStep 849811 = 1274717) B1274717
theorem B1701809 : Blo 754331 1701809 := bstep (se 2 (by rfl) ⟨638178, by rfl⟩ : syracuseStep 1701809 = 1276357) B1276357
theorem B1701827 : Blo 754331 1701827 := bstep (se 1 (by rfl) ⟨1276370, by rfl⟩ : syracuseStep 1701827 = 2552741) B2552741
theorem B16316387 : Blo 754331 16316387 := bstep (se 1 (by rfl) ⟨12237290, by rfl⟩ : syracuseStep 16316387 = 24474581) B24474581
theorem B1275905 : Blo 754331 1275905 := bstep (se 2 (by rfl) ⟨478464, by rfl⟩ : syracuseStep 1275905 = 956929) B956929
theorem B849955 : Blo 754331 849955 := bstep (se 1 (by rfl) ⟨637466, by rfl⟩ : syracuseStep 849955 = 1274933) B1274933
theorem B1276033 : Blo 754331 1276033 := bstep (se 2 (by rfl) ⟨478512, by rfl⟩ : syracuseStep 1276033 = 957025) B957025
theorem B1276067 : Blo 754331 1276067 := bstep (se 1 (by rfl) ⟨957050, by rfl⟩ : syracuseStep 1276067 = 1914101) B1914101
theorem B850099 : Blo 754331 850099 := bstep (se 1 (by rfl) ⟨637574, by rfl⟩ : syracuseStep 850099 = 1275149) B1275149
theorem B1702097 : Blo 754331 1702097 := bstep (se 2 (by rfl) ⟨638286, by rfl⟩ : syracuseStep 1702097 = 1276573) B1276573
theorem B1079507 : Blo 754331 1079507 := bstep (se 1 (by rfl) ⟨809630, by rfl⟩ : syracuseStep 1079507 = 1619261) B1619261
theorem B1702115 : Blo 754331 1702115 := bstep (se 1 (by rfl) ⟨1276586, by rfl⟩ : syracuseStep 1702115 = 2553173) B2553173
theorem B1276195 : Blo 754331 1276195 := bstep (se 1 (by rfl) ⟨957146, by rfl⟩ : syracuseStep 1276195 = 1914293) B1914293
theorem B850243 : Blo 754331 850243 := bstep (se 1 (by rfl) ⟨637682, by rfl⟩ : syracuseStep 850243 = 1275365) B1275365
theorem B2554253 : Blo 754331 2554253 := bstep (se 3 (by rfl) ⟨478922, by rfl⟩ : syracuseStep 2554253 = 957845) B957845
theorem B1276337 : Blo 754331 1276337 := bstep (se 2 (by rfl) ⟨478626, by rfl⟩ : syracuseStep 1276337 = 957253) B957253
theorem B2554307 : Blo 754331 2554307 := bstep (se 1 (by rfl) ⟨1915730, by rfl⟩ : syracuseStep 2554307 = 3831461) B3831461
theorem B6453701 : Blo 754331 6453701 := bstep (se 4 (by rfl) ⟨605034, by rfl⟩ : syracuseStep 6453701 = 1210069) B1210069
theorem B850387 : Blo 754331 850387 := bstep (se 1 (by rfl) ⟨637790, by rfl⟩ : syracuseStep 850387 = 1275581) B1275581
theorem B1702385 : Blo 754331 1702385 := bstep (se 2 (by rfl) ⟨638394, by rfl⟩ : syracuseStep 1702385 = 1276789) B1276789
theorem B1702403 : Blo 754331 1702403 := bstep (se 1 (by rfl) ⟨1276802, by rfl⟩ : syracuseStep 1702403 = 2553605) B2553605
theorem B1276465 : Blo 754331 1276465 := bstep (se 2 (by rfl) ⟨478674, by rfl⟩ : syracuseStep 1276465 = 957349) B957349
theorem B1276499 : Blo 754331 1276499 := bstep (se 1 (by rfl) ⟨957374, by rfl⟩ : syracuseStep 1276499 = 1914749) B1914749
theorem B850531 : Blo 754331 850531 := bstep (se 1 (by rfl) ⟨637898, by rfl⟩ : syracuseStep 850531 = 1275797) B1275797
theorem B3832433 : Blo 754331 3832433 := bstep (se 2 (by rfl) ⟨1437162, by rfl⟩ : syracuseStep 3832433 = 2874325) B2874325
theorem B2423459 : Blo 754331 2423459 := bstep (se 1 (by rfl) ⟨1817594, by rfl⟩ : syracuseStep 2423459 = 3635189) B3635189
theorem B2554577 : Blo 754331 2554577 := bstep (se 2 (by rfl) ⟨957966, by rfl⟩ : syracuseStep 2554577 = 1915933) B1915933
theorem B1276627 : Blo 754331 1276627 := bstep (se 1 (by rfl) ⟨957470, by rfl⟩ : syracuseStep 1276627 = 1914941) B1914941
theorem B850675 : Blo 754331 850675 := bstep (se 1 (by rfl) ⟨638006, by rfl⟩ : syracuseStep 850675 = 1276013) B1276013
theorem B1702673 : Blo 754331 1702673 := bstep (se 2 (by rfl) ⟨638502, by rfl⟩ : syracuseStep 1702673 = 1277005) B1277005
theorem B1211171 : Blo 754331 1211171 := bstep (se 1 (by rfl) ⟨908378, by rfl⟩ : syracuseStep 1211171 = 1816757) B1816757
theorem B1702691 : Blo 754331 1702691 := bstep (se 1 (by rfl) ⟨1277018, by rfl⟩ : syracuseStep 1702691 = 2554037) B2554037
theorem B1276769 : Blo 754331 1276769 := bstep (se 2 (by rfl) ⟨478788, by rfl⟩ : syracuseStep 1276769 = 957577) B957577
theorem B1211249 : Blo 754331 1211249 := bstep (se 2 (by rfl) ⟨454218, by rfl⟩ : syracuseStep 1211249 = 908437) B908437
theorem B850819 : Blo 754331 850819 := bstep (se 1 (by rfl) ⟨638114, by rfl⟩ : syracuseStep 850819 = 1276229) B1276229
theorem B1276897 : Blo 754331 1276897 := bstep (se 2 (by rfl) ⟨478836, by rfl⟩ : syracuseStep 1276897 = 957673) B957673
theorem B3505123 : Blo 754331 3505123 := bstep (se 1 (by rfl) ⟨2628842, by rfl⟩ : syracuseStep 3505123 = 5257685) B5257685
theorem B1276931 : Blo 754331 1276931 := bstep (se 1 (by rfl) ⟨957698, by rfl⟩ : syracuseStep 1276931 = 1915397) B1915397
theorem B850963 : Blo 754331 850963 := bstep (se 1 (by rfl) ⟨638222, by rfl⟩ : syracuseStep 850963 = 1276445) B1276445
theorem B1702961 : Blo 754331 1702961 := bstep (se 2 (by rfl) ⟨638610, by rfl⟩ : syracuseStep 1702961 = 1277221) B1277221
theorem B1702979 : Blo 754331 1702979 := bstep (se 1 (by rfl) ⟨1277234, by rfl⟩ : syracuseStep 1702979 = 2554469) B2554469
theorem B1211473 : Blo 754331 1211473 := bstep (se 2 (by rfl) ⟨454302, by rfl⟩ : syracuseStep 1211473 = 908605) B908605
theorem B1277059 : Blo 754331 1277059 := bstep (se 1 (by rfl) ⟨957794, by rfl⟩ : syracuseStep 1277059 = 1915589) B1915589
theorem B851107 : Blo 754331 851107 := bstep (se 1 (by rfl) ⟨638330, by rfl⟩ : syracuseStep 851107 = 1276661) B1276661
theorem B2555117 : Blo 754331 2555117 := bstep (se 3 (by rfl) ⟨479084, by rfl⟩ : syracuseStep 2555117 = 958169) B958169
theorem B6552845 : Blo 754331 6552845 := bstep (se 3 (by rfl) ⟨1228658, by rfl⟩ : syracuseStep 6552845 = 2457317) B2457317
theorem B1277201 : Blo 754331 1277201 := bstep (se 2 (by rfl) ⟨478950, by rfl⟩ : syracuseStep 1277201 = 957901) B957901
theorem B2555171 : Blo 754331 2555171 := bstep (se 1 (by rfl) ⟨1916378, by rfl⟩ : syracuseStep 2555171 = 3832757) B3832757
theorem B851251 : Blo 754331 851251 := bstep (se 1 (by rfl) ⟨638438, by rfl⟩ : syracuseStep 851251 = 1276877) B1276877
theorem B1703249 : Blo 754331 1703249 := bstep (se 2 (by rfl) ⟨638718, by rfl⟩ : syracuseStep 1703249 = 1277437) B1277437
theorem B1703267 : Blo 754331 1703267 := bstep (se 1 (by rfl) ⟨1277450, by rfl⟩ : syracuseStep 1703267 = 2554901) B2554901
theorem B1277329 : Blo 754331 1277329 := bstep (se 2 (by rfl) ⟨478998, by rfl⟩ : syracuseStep 1277329 = 957997) B957997
theorem B1277363 : Blo 754331 1277363 := bstep (se 1 (by rfl) ⟨958022, by rfl⟩ : syracuseStep 1277363 = 1916045) B1916045
theorem B851395 : Blo 754331 851395 := bstep (se 1 (by rfl) ⟨638546, by rfl⟩ : syracuseStep 851395 = 1277093) B1277093
theorem B20708885 : Blo 754331 20708885 := bstep (se 6 (by rfl) ⟨485364, by rfl⟩ : syracuseStep 20708885 = 970729) B970729
theorem B2555441 : Blo 754331 2555441 := bstep (se 2 (by rfl) ⟨958290, by rfl⟩ : syracuseStep 2555441 = 1916581) B1916581
theorem B1277491 : Blo 754331 1277491 := bstep (se 1 (by rfl) ⟨958118, by rfl⟩ : syracuseStep 1277491 = 1916237) B1916237
theorem B851539 : Blo 754331 851539 := bstep (se 1 (by rfl) ⟨638654, by rfl⟩ : syracuseStep 851539 = 1277309) B1277309
theorem B1703537 : Blo 754331 1703537 := bstep (se 2 (by rfl) ⟨638826, by rfl⟩ : syracuseStep 1703537 = 1277653) B1277653
theorem B1703555 : Blo 754331 1703555 := bstep (se 1 (by rfl) ⟨1277666, by rfl⟩ : syracuseStep 1703555 = 2555333) B2555333
theorem B1277633 : Blo 754331 1277633 := bstep (se 2 (by rfl) ⟨479112, by rfl⟩ : syracuseStep 1277633 = 958225) B958225
theorem B818915 : Blo 754331 818915 := bstep (se 1 (by rfl) ⟨614186, by rfl⟩ : syracuseStep 818915 = 1228373) B1228373
theorem B851683 : Blo 754331 851683 := bstep (se 1 (by rfl) ⟨638762, by rfl⟩ : syracuseStep 851683 = 1277525) B1277525
theorem B1277761 : Blo 754331 1277761 := bstep (se 2 (by rfl) ⟨479160, by rfl⟩ : syracuseStep 1277761 = 958321) B958321
theorem B1277795 : Blo 754331 1277795 := bstep (se 1 (by rfl) ⟨958346, by rfl⟩ : syracuseStep 1277795 = 1916693) B1916693
theorem B2719601 : Blo 754331 2719601 := bstep (se 2 (by rfl) ⟨1019850, by rfl⟩ : syracuseStep 2719601 = 2039701) B2039701
theorem B851827 : Blo 754331 851827 := bstep (se 1 (by rfl) ⟨638870, by rfl⟩ : syracuseStep 851827 = 1277741) B1277741
theorem B1703825 : Blo 754331 1703825 := bstep (se 2 (by rfl) ⟨638934, by rfl⟩ : syracuseStep 1703825 = 1277869) B1277869
theorem B1703843 : Blo 754331 1703843 := bstep (se 1 (by rfl) ⟨1277882, by rfl⟩ : syracuseStep 1703843 = 2555765) B2555765
theorem B1277923 : Blo 754331 1277923 := bstep (se 1 (by rfl) ⟨958442, by rfl⟩ : syracuseStep 1277923 = 1916885) B1916885
theorem B2555927 : Blo 754331 2555927 := bstep (se 1 (by rfl) ⟨1916945, by rfl⟩ : syracuseStep 2555927 = 3833891) B3833891
theorem B1277977 : Blo 754331 1277977 := bstep (se 2 (by rfl) ⟨479241, by rfl⟩ : syracuseStep 1277977 = 958483) B958483
theorem B5832749 : Blo 754331 5832749 := bstep (se 3 (by rfl) ⟨1093640, by rfl⟩ : syracuseStep 5832749 = 2187281) B2187281
theorem B1703987 : Blo 754331 1703987 := bstep (se 1 (by rfl) ⟨1277990, by rfl⟩ : syracuseStep 1703987 = 2555981) B2555981
theorem B34930763 : Blo 754331 34930763 := bstep (se 1 (by rfl) ⟨26198072, by rfl⟩ : syracuseStep 34930763 = 52396145) B52396145
theorem B852043 : Blo 754331 852043 := bstep (se 1 (by rfl) ⟨639032, by rfl⟩ : syracuseStep 852043 = 1278065) B1278065
theorem B1704023 : Blo 754331 1704023 := bstep (se 1 (by rfl) ⟨1278017, by rfl⟩ : syracuseStep 1704023 = 2556035) B2556035
theorem B2719889 : Blo 754331 2719889 := bstep (se 2 (by rfl) ⟨1019958, by rfl⟩ : syracuseStep 2719889 = 2039917) B2039917
theorem B852151 : Blo 754331 852151 := bstep (se 1 (by rfl) ⟨639113, by rfl⟩ : syracuseStep 852151 = 1278227) B1278227
theorem B1704203 : Blo 754331 1704203 := bstep (se 1 (by rfl) ⟨1278152, by rfl⟩ : syracuseStep 1704203 = 2556305) B2556305
theorem B1704257 : Blo 754331 1704257 := bstep (se 2 (by rfl) ⟨639096, by rfl⟩ : syracuseStep 1704257 = 1278193) B1278193
theorem B852331 : Blo 754331 852331 := bstep (se 1 (by rfl) ⟨639248, by rfl⟩ : syracuseStep 852331 = 1278497) B1278497
theorem B5669297 : Blo 754331 5669297 := bstep (se 2 (by rfl) ⟨2125986, by rfl⟩ : syracuseStep 5669297 = 4251973) B4251973
theorem B852439 : Blo 754331 852439 := bstep (se 1 (by rfl) ⟨639329, by rfl⟩ : syracuseStep 852439 = 1278659) B1278659
theorem B1212889 : Blo 754331 1212889 := bstep (se 2 (by rfl) ⟨454833, by rfl⟩ : syracuseStep 1212889 = 909667) B909667
theorem B2720279 : Blo 754331 2720279 := bstep (se 1 (by rfl) ⟨2040209, by rfl⟩ : syracuseStep 2720279 = 4080419) B4080419
theorem B1704473 : Blo 754331 1704473 := bstep (se 2 (by rfl) ⟨639177, by rfl⟩ : syracuseStep 1704473 = 1278355) B1278355
theorem B2556467 : Blo 754331 2556467 := bstep (se 1 (by rfl) ⟨1917350, by rfl⟩ : syracuseStep 2556467 = 3834701) B3834701
theorem B2720321 : Blo 754331 2720321 := bstep (se 2 (by rfl) ⟨1020120, by rfl⟩ : syracuseStep 2720321 = 2040241) B2040241
theorem B1278551 : Blo 754331 1278551 := bstep (se 1 (by rfl) ⟨958913, by rfl⟩ : syracuseStep 1278551 = 1917827) B1917827
theorem B1704563 : Blo 754331 1704563 := bstep (se 1 (by rfl) ⟨1278422, by rfl⟩ : syracuseStep 1704563 = 2556845) B2556845
theorem B852619 : Blo 754331 852619 := bstep (se 1 (by rfl) ⟨639464, by rfl⟩ : syracuseStep 852619 = 1278929) B1278929
theorem B1704599 : Blo 754331 1704599 := bstep (se 1 (by rfl) ⟨1278449, by rfl⟩ : syracuseStep 1704599 = 2556899) B2556899
theorem B754347 : Blo 754331 754347 := bstep (se 1 (by rfl) ⟨565760, by rfl⟩ : syracuseStep 754347 = 1131521) B1131521
theorem B754359 : Blo 754331 754359 := bstep (se 1 (by rfl) ⟨565769, by rfl⟩ : syracuseStep 754359 = 1131539) B1131539
theorem B754379 : Blo 754331 754379 := bstep (se 1 (by rfl) ⟨565784, by rfl⟩ : syracuseStep 754379 = 1131569) B1131569
theorem B754391 : Blo 754331 754391 := bstep (se 1 (by rfl) ⟨565793, by rfl⟩ : syracuseStep 754391 = 1131587) B1131587
theorem B1278679 : Blo 754331 1278679 := bstep (se 1 (by rfl) ⟨959009, by rfl⟩ : syracuseStep 1278679 = 1918019) B1918019
theorem B1213145 : Blo 754331 1213145 := bstep (se 2 (by rfl) ⟨454929, by rfl⟩ : syracuseStep 1213145 = 909859) B909859
theorem B754411 : Blo 754331 754411 := bstep (se 1 (by rfl) ⟨565808, by rfl⟩ : syracuseStep 754411 = 1131617) B1131617
theorem B754423 : Blo 754331 754423 := bstep (se 1 (by rfl) ⟨565817, by rfl⟩ : syracuseStep 754423 = 1131635) B1131635
theorem B852727 : Blo 754331 852727 := bstep (se 1 (by rfl) ⟨639545, by rfl⟩ : syracuseStep 852727 = 1279091) B1279091
theorem B754443 : Blo 754331 754443 := bstep (se 1 (by rfl) ⟨565832, by rfl⟩ : syracuseStep 754443 = 1131665) B1131665
theorem B754455 : Blo 754331 754455 := bstep (se 1 (by rfl) ⟨565841, by rfl⟩ : syracuseStep 754455 = 1131683) B1131683
theorem B754475 : Blo 754331 754475 := bstep (se 1 (by rfl) ⟨565856, by rfl⟩ : syracuseStep 754475 = 1131713) B1131713
theorem B754487 : Blo 754331 754487 := bstep (se 1 (by rfl) ⟨565865, by rfl⟩ : syracuseStep 754487 = 1131731) B1131731
theorem B7275329 : Blo 754331 7275329 := bstep (se 2 (by rfl) ⟨2728248, by rfl⟩ : syracuseStep 7275329 = 5456497) B5456497
theorem B2556737 : Blo 754331 2556737 := bstep (se 2 (by rfl) ⟨958776, by rfl⟩ : syracuseStep 2556737 = 1917553) B1917553
theorem B754507 : Blo 754331 754507 := bstep (se 1 (by rfl) ⟨565880, by rfl⟩ : syracuseStep 754507 = 1131761) B1131761
theorem B1704779 : Blo 754331 1704779 := bstep (se 1 (by rfl) ⟨1278584, by rfl⟩ : syracuseStep 1704779 = 2557169) B2557169
theorem B754519 : Blo 754331 754519 := bstep (se 1 (by rfl) ⟨565889, by rfl⟩ : syracuseStep 754519 = 1131779) B1131779
theorem B754539 : Blo 754331 754539 := bstep (se 1 (by rfl) ⟨565904, by rfl⟩ : syracuseStep 754539 = 1131809) B1131809
theorem B754551 : Blo 754331 754551 := bstep (se 1 (by rfl) ⟨565913, by rfl⟩ : syracuseStep 754551 = 1131827) B1131827
theorem B1704833 : Blo 754331 1704833 := bstep (se 2 (by rfl) ⟨639312, by rfl⟩ : syracuseStep 1704833 = 1278625) B1278625
theorem B754571 : Blo 754331 754571 := bstep (se 1 (by rfl) ⟨565928, by rfl⟩ : syracuseStep 754571 = 1131857) B1131857
theorem B754583 : Blo 754331 754583 := bstep (se 1 (by rfl) ⟨565937, by rfl⟩ : syracuseStep 754583 = 1131875) B1131875
theorem B1213337 : Blo 754331 1213337 := bstep (se 2 (by rfl) ⟨455001, by rfl⟩ : syracuseStep 1213337 = 910003) B910003
theorem B4096919 : Blo 754331 4096919 := bstep (se 1 (by rfl) ⟨3072689, by rfl⟩ : syracuseStep 4096919 = 6145379) B6145379
theorem B754603 : Blo 754331 754603 := bstep (se 1 (by rfl) ⟨565952, by rfl⟩ : syracuseStep 754603 = 1131905) B1131905
theorem B852907 : Blo 754331 852907 := bstep (se 1 (by rfl) ⟨639680, by rfl⟩ : syracuseStep 852907 = 1279361) B1279361
theorem B754615 : Blo 754331 754615 := bstep (se 1 (by rfl) ⟨565961, by rfl⟩ : syracuseStep 754615 = 1131923) B1131923
theorem B754635 : Blo 754331 754635 := bstep (se 1 (by rfl) ⟨565976, by rfl⟩ : syracuseStep 754635 = 1131953) B1131953
theorem B754647 : Blo 754331 754647 := bstep (se 1 (by rfl) ⟨565985, by rfl⟩ : syracuseStep 754647 = 1131971) B1131971
theorem B754667 : Blo 754331 754667 := bstep (se 1 (by rfl) ⟨566000, by rfl⟩ : syracuseStep 754667 = 1132001) B1132001
theorem B754679 : Blo 754331 754679 := bstep (se 1 (by rfl) ⟨566009, by rfl⟩ : syracuseStep 754679 = 1132019) B1132019
theorem B754699 : Blo 754331 754699 := bstep (se 1 (by rfl) ⟨566024, by rfl⟩ : syracuseStep 754699 = 1132049) B1132049
theorem B754711 : Blo 754331 754711 := bstep (se 1 (by rfl) ⟨566033, by rfl⟩ : syracuseStep 754711 = 1132067) B1132067
theorem B2425879 : Blo 754331 2425879 := bstep (se 1 (by rfl) ⟨1819409, by rfl⟩ : syracuseStep 2425879 = 3638819) B3638819
theorem B853015 : Blo 754331 853015 := bstep (se 1 (by rfl) ⟨639761, by rfl⟩ : syracuseStep 853015 = 1279523) B1279523
theorem B754731 : Blo 754331 754731 := bstep (se 1 (by rfl) ⟨566048, by rfl⟩ : syracuseStep 754731 = 1132097) B1132097
theorem B754743 : Blo 754331 754743 := bstep (se 1 (by rfl) ⟨566057, by rfl⟩ : syracuseStep 754743 = 1132115) B1132115
theorem B754763 : Blo 754331 754763 := bstep (se 1 (by rfl) ⟨566072, by rfl⟩ : syracuseStep 754763 = 1132145) B1132145
theorem B754775 : Blo 754331 754775 := bstep (se 1 (by rfl) ⟨566081, by rfl⟩ : syracuseStep 754775 = 1132163) B1132163
theorem B1705049 : Blo 754331 1705049 := bstep (se 2 (by rfl) ⟨639393, by rfl⟩ : syracuseStep 1705049 = 1278787) B1278787
theorem B754795 : Blo 754331 754795 := bstep (se 1 (by rfl) ⟨566096, by rfl⟩ : syracuseStep 754795 = 1132193) B1132193
theorem B754807 : Blo 754331 754807 := bstep (se 1 (by rfl) ⟨566105, by rfl⟩ : syracuseStep 754807 = 1132211) B1132211
theorem B754827 : Blo 754331 754827 := bstep (se 1 (by rfl) ⟨566120, by rfl⟩ : syracuseStep 754827 = 1132241) B1132241
theorem B754839 : Blo 754331 754839 := bstep (se 1 (by rfl) ⟨566129, by rfl⟩ : syracuseStep 754839 = 1132259) B1132259
theorem B754859 : Blo 754331 754859 := bstep (se 1 (by rfl) ⟨566144, by rfl⟩ : syracuseStep 754859 = 1132289) B1132289
theorem B1705139 : Blo 754331 1705139 := bstep (se 1 (by rfl) ⟨1278854, by rfl⟩ : syracuseStep 1705139 = 2557709) B2557709
theorem B754871 : Blo 754331 754871 := bstep (se 1 (by rfl) ⟨566153, by rfl⟩ : syracuseStep 754871 = 1132307) B1132307
theorem B754891 : Blo 754331 754891 := bstep (se 1 (by rfl) ⟨566168, by rfl⟩ : syracuseStep 754891 = 1132337) B1132337
theorem B754903 : Blo 754331 754903 := bstep (se 1 (by rfl) ⟨566177, by rfl⟩ : syracuseStep 754903 = 1132355) B1132355
theorem B1705175 : Blo 754331 1705175 := bstep (se 1 (by rfl) ⟨1278881, by rfl⟩ : syracuseStep 1705175 = 2557763) B2557763
theorem B754923 : Blo 754331 754923 := bstep (se 1 (by rfl) ⟨566192, by rfl⟩ : syracuseStep 754923 = 1132385) B1132385
theorem B754935 : Blo 754331 754935 := bstep (se 1 (by rfl) ⟨566201, by rfl⟩ : syracuseStep 754935 = 1132403) B1132403
theorem B754955 : Blo 754331 754955 := bstep (se 1 (by rfl) ⟨566216, by rfl⟩ : syracuseStep 754955 = 1132433) B1132433
theorem B754967 : Blo 754331 754967 := bstep (se 1 (by rfl) ⟨566225, by rfl⟩ : syracuseStep 754967 = 1132451) B1132451
theorem B754987 : Blo 754331 754987 := bstep (se 1 (by rfl) ⟨566240, by rfl⟩ : syracuseStep 754987 = 1132481) B1132481
theorem B754999 : Blo 754331 754999 := bstep (se 1 (by rfl) ⟨566249, by rfl⟩ : syracuseStep 754999 = 1132499) B1132499
theorem B755019 : Blo 754331 755019 := bstep (se 1 (by rfl) ⟨566264, by rfl⟩ : syracuseStep 755019 = 1132529) B1132529
theorem B1279307 : Blo 754331 1279307 := bstep (se 1 (by rfl) ⟨959480, by rfl⟩ : syracuseStep 1279307 = 1918961) B1918961
theorem B755031 : Blo 754331 755031 := bstep (se 1 (by rfl) ⟨566273, by rfl⟩ : syracuseStep 755031 = 1132547) B1132547
theorem B2557277 : Blo 754331 2557277 := bstep (se 3 (by rfl) ⟨479489, by rfl⟩ : syracuseStep 2557277 = 958979) B958979
theorem B755051 : Blo 754331 755051 := bstep (se 1 (by rfl) ⟨566288, by rfl⟩ : syracuseStep 755051 = 1132577) B1132577
theorem B755063 : Blo 754331 755063 := bstep (se 1 (by rfl) ⟨566297, by rfl⟩ : syracuseStep 755063 = 1132595) B1132595
theorem B755083 : Blo 754331 755083 := bstep (se 1 (by rfl) ⟨566312, by rfl⟩ : syracuseStep 755083 = 1132625) B1132625
theorem B1705355 : Blo 754331 1705355 := bstep (se 1 (by rfl) ⟨1279016, by rfl⟩ : syracuseStep 1705355 = 2558033) B2558033
theorem B755095 : Blo 754331 755095 := bstep (se 1 (by rfl) ⟨566321, by rfl⟩ : syracuseStep 755095 = 1132643) B1132643
theorem B755115 : Blo 754331 755115 := bstep (se 1 (by rfl) ⟨566336, by rfl⟩ : syracuseStep 755115 = 1132673) B1132673
theorem B755127 : Blo 754331 755127 := bstep (se 1 (by rfl) ⟨566345, by rfl⟩ : syracuseStep 755127 = 1132691) B1132691
theorem B1705409 : Blo 754331 1705409 := bstep (se 2 (by rfl) ⟨639528, by rfl⟩ : syracuseStep 1705409 = 1279057) B1279057
theorem B755147 : Blo 754331 755147 := bstep (se 1 (by rfl) ⟨566360, by rfl⟩ : syracuseStep 755147 = 1132721) B1132721
theorem B1279435 : Blo 754331 1279435 := bstep (se 1 (by rfl) ⟨959576, by rfl⟩ : syracuseStep 1279435 = 1919153) B1919153
theorem B755159 : Blo 754331 755159 := bstep (se 1 (by rfl) ⟨566369, by rfl⟩ : syracuseStep 755159 = 1132739) B1132739
theorem B755179 : Blo 754331 755179 := bstep (se 1 (by rfl) ⟨566384, by rfl⟩ : syracuseStep 755179 = 1132769) B1132769
theorem B755191 : Blo 754331 755191 := bstep (se 1 (by rfl) ⟨566393, by rfl⟩ : syracuseStep 755191 = 1132787) B1132787
theorem B755211 : Blo 754331 755211 := bstep (se 1 (by rfl) ⟨566408, by rfl⟩ : syracuseStep 755211 = 1132817) B1132817
theorem B755223 : Blo 754331 755223 := bstep (se 1 (by rfl) ⟨566417, by rfl⟩ : syracuseStep 755223 = 1132835) B1132835
theorem B755243 : Blo 754331 755243 := bstep (se 1 (by rfl) ⟨566432, by rfl⟩ : syracuseStep 755243 = 1132865) B1132865
theorem B4851245 : Blo 754331 4851245 := bstep (se 3 (by rfl) ⟨909608, by rfl⟩ : syracuseStep 4851245 = 1819217) B1819217
theorem B755255 : Blo 754331 755255 := bstep (se 1 (by rfl) ⟨566441, by rfl⟩ : syracuseStep 755255 = 1132883) B1132883
theorem B755275 : Blo 754331 755275 := bstep (se 1 (by rfl) ⟨566456, by rfl⟩ : syracuseStep 755275 = 1132913) B1132913
theorem B755287 : Blo 754331 755287 := bstep (se 1 (by rfl) ⟨566465, by rfl⟩ : syracuseStep 755287 = 1132931) B1132931
theorem B1279577 : Blo 754331 1279577 := bstep (se 2 (by rfl) ⟨479841, by rfl⟩ : syracuseStep 1279577 = 959683) B959683
theorem B755307 : Blo 754331 755307 := bstep (se 1 (by rfl) ⟨566480, by rfl⟩ : syracuseStep 755307 = 1132961) B1132961
theorem B755319 : Blo 754331 755319 := bstep (se 1 (by rfl) ⟨566489, by rfl⟩ : syracuseStep 755319 = 1132979) B1132979
theorem B755339 : Blo 754331 755339 := bstep (se 1 (by rfl) ⟨566504, by rfl⟩ : syracuseStep 755339 = 1133009) B1133009
theorem B755351 : Blo 754331 755351 := bstep (se 1 (by rfl) ⟨566513, by rfl⟩ : syracuseStep 755351 = 1133027) B1133027
theorem B1705625 : Blo 754331 1705625 := bstep (se 2 (by rfl) ⟨639609, by rfl⟩ : syracuseStep 1705625 = 1279219) B1279219
theorem B755371 : Blo 754331 755371 := bstep (se 1 (by rfl) ⟨566528, by rfl⟩ : syracuseStep 755371 = 1133057) B1133057
theorem B755383 : Blo 754331 755383 := bstep (se 1 (by rfl) ⟨566537, by rfl⟩ : syracuseStep 755383 = 1133075) B1133075
theorem B755403 : Blo 754331 755403 := bstep (se 1 (by rfl) ⟨566552, by rfl⟩ : syracuseStep 755403 = 1133105) B1133105
theorem B755415 : Blo 754331 755415 := bstep (se 1 (by rfl) ⟨566561, by rfl⟩ : syracuseStep 755415 = 1133123) B1133123
theorem B755435 : Blo 754331 755435 := bstep (se 1 (by rfl) ⟨566576, by rfl⟩ : syracuseStep 755435 = 1133153) B1133153
theorem B1705715 : Blo 754331 1705715 := bstep (se 1 (by rfl) ⟨1279286, by rfl⟩ : syracuseStep 1705715 = 2558573) B2558573
theorem B755447 : Blo 754331 755447 := bstep (se 1 (by rfl) ⟨566585, by rfl⟩ : syracuseStep 755447 = 1133171) B1133171
theorem B755467 : Blo 754331 755467 := bstep (se 1 (by rfl) ⟨566600, by rfl⟩ : syracuseStep 755467 = 1133201) B1133201
theorem B755479 : Blo 754331 755479 := bstep (se 1 (by rfl) ⟨566609, by rfl⟩ : syracuseStep 755479 = 1133219) B1133219
theorem B1705751 : Blo 754331 1705751 := bstep (se 1 (by rfl) ⟨1279313, by rfl⟩ : syracuseStep 1705751 = 2558627) B2558627
theorem B755499 : Blo 754331 755499 := bstep (se 1 (by rfl) ⟨566624, by rfl⟩ : syracuseStep 755499 = 1133249) B1133249
theorem B755511 : Blo 754331 755511 := bstep (se 1 (by rfl) ⟨566633, by rfl⟩ : syracuseStep 755511 = 1133267) B1133267
theorem B5736257 : Blo 754331 5736257 := bstep (se 2 (by rfl) ⟨2151096, by rfl⟩ : syracuseStep 5736257 = 4302193) B4302193
theorem B755531 : Blo 754331 755531 := bstep (se 1 (by rfl) ⟨566648, by rfl⟩ : syracuseStep 755531 = 1133297) B1133297
theorem B2426699 : Blo 754331 2426699 := bstep (se 1 (by rfl) ⟨1820024, by rfl⟩ : syracuseStep 2426699 = 3640049) B3640049
theorem B755543 : Blo 754331 755543 := bstep (se 1 (by rfl) ⟨566657, by rfl⟩ : syracuseStep 755543 = 1133315) B1133315
theorem B755563 : Blo 754331 755563 := bstep (se 1 (by rfl) ⟨566672, by rfl⟩ : syracuseStep 755563 = 1133345) B1133345
theorem B755575 : Blo 754331 755575 := bstep (se 1 (by rfl) ⟨566681, by rfl⟩ : syracuseStep 755575 = 1133363) B1133363
theorem B4360067 : Blo 754331 4360067 := bstep (se 1 (by rfl) ⟨3270050, by rfl⟩ : syracuseStep 4360067 = 6540101) B6540101
theorem B755595 : Blo 754331 755595 := bstep (se 1 (by rfl) ⟨566696, by rfl⟩ : syracuseStep 755595 = 1133393) B1133393
theorem B755607 : Blo 754331 755607 := bstep (se 1 (by rfl) ⟨566705, by rfl⟩ : syracuseStep 755607 = 1133411) B1133411
theorem B755627 : Blo 754331 755627 := bstep (se 1 (by rfl) ⟨566720, by rfl⟩ : syracuseStep 755627 = 1133441) B1133441
theorem B755639 : Blo 754331 755639 := bstep (se 1 (by rfl) ⟨566729, by rfl⟩ : syracuseStep 755639 = 1133459) B1133459
theorem B755659 : Blo 754331 755659 := bstep (se 1 (by rfl) ⟨566744, by rfl⟩ : syracuseStep 755659 = 1133489) B1133489
theorem B1705931 : Blo 754331 1705931 := bstep (se 1 (by rfl) ⟨1279448, by rfl⟩ : syracuseStep 1705931 = 2558897) B2558897
theorem B755671 : Blo 754331 755671 := bstep (se 1 (by rfl) ⟨566753, by rfl⟩ : syracuseStep 755671 = 1133507) B1133507
theorem B755691 : Blo 754331 755691 := bstep (se 1 (by rfl) ⟨566768, by rfl⟩ : syracuseStep 755691 = 1133537) B1133537
theorem B755703 : Blo 754331 755703 := bstep (se 1 (by rfl) ⟨566777, by rfl⟩ : syracuseStep 755703 = 1133555) B1133555
theorem B1705985 : Blo 754331 1705985 := bstep (se 2 (by rfl) ⟨639744, by rfl⟩ : syracuseStep 1705985 = 1279489) B1279489
theorem B755723 : Blo 754331 755723 := bstep (se 1 (by rfl) ⟨566792, by rfl⟩ : syracuseStep 755723 = 1133585) B1133585
theorem B755735 : Blo 754331 755735 := bstep (se 1 (by rfl) ⟨566801, by rfl⟩ : syracuseStep 755735 = 1133603) B1133603
theorem B755755 : Blo 754331 755755 := bstep (se 1 (by rfl) ⟨566816, by rfl⟩ : syracuseStep 755755 = 1133633) B1133633
theorem B755767 : Blo 754331 755767 := bstep (se 1 (by rfl) ⟨566825, by rfl⟩ : syracuseStep 755767 = 1133651) B1133651
theorem B755787 : Blo 754331 755787 := bstep (se 1 (by rfl) ⟨566840, by rfl⟩ : syracuseStep 755787 = 1133681) B1133681
theorem B755799 : Blo 754331 755799 := bstep (se 1 (by rfl) ⟨566849, by rfl⟩ : syracuseStep 755799 = 1133699) B1133699
theorem B3835997 : Blo 754331 3835997 := bstep (se 3 (by rfl) ⟨719249, by rfl⟩ : syracuseStep 3835997 = 1438499) B1438499
theorem B755819 : Blo 754331 755819 := bstep (se 1 (by rfl) ⟨566864, by rfl⟩ : syracuseStep 755819 = 1133729) B1133729
theorem B755831 : Blo 754331 755831 := bstep (se 1 (by rfl) ⟨566873, by rfl⟩ : syracuseStep 755831 = 1133747) B1133747
theorem B755851 : Blo 754331 755851 := bstep (se 1 (by rfl) ⟨566888, by rfl⟩ : syracuseStep 755851 = 1133777) B1133777
theorem B755863 : Blo 754331 755863 := bstep (se 1 (by rfl) ⟨566897, by rfl⟩ : syracuseStep 755863 = 1133795) B1133795
theorem B755883 : Blo 754331 755883 := bstep (se 1 (by rfl) ⟨566912, by rfl⟩ : syracuseStep 755883 = 1133825) B1133825
theorem B755895 : Blo 754331 755895 := bstep (se 1 (by rfl) ⟨566921, by rfl⟩ : syracuseStep 755895 = 1133843) B1133843
theorem B755915 : Blo 754331 755915 := bstep (se 1 (by rfl) ⟨566936, by rfl⟩ : syracuseStep 755915 = 1133873) B1133873
theorem B755927 : Blo 754331 755927 := bstep (se 1 (by rfl) ⟨566945, by rfl⟩ : syracuseStep 755927 = 1133891) B1133891
theorem B1706201 : Blo 754331 1706201 := bstep (se 2 (by rfl) ⟨639825, by rfl⟩ : syracuseStep 1706201 = 1279651) B1279651
theorem B755947 : Blo 754331 755947 := bstep (se 1 (by rfl) ⟨566960, by rfl⟩ : syracuseStep 755947 = 1133921) B1133921
theorem B755959 : Blo 754331 755959 := bstep (se 1 (by rfl) ⟨566969, by rfl⟩ : syracuseStep 755959 = 1133939) B1133939
theorem B755979 : Blo 754331 755979 := bstep (se 1 (by rfl) ⟨566984, by rfl⟩ : syracuseStep 755979 = 1133969) B1133969
theorem B755991 : Blo 754331 755991 := bstep (se 1 (by rfl) ⟨566993, by rfl⟩ : syracuseStep 755991 = 1133987) B1133987
theorem B756011 : Blo 754331 756011 := bstep (se 1 (by rfl) ⟨567008, by rfl⟩ : syracuseStep 756011 = 1134017) B1134017
theorem B756023 : Blo 754331 756023 := bstep (se 1 (by rfl) ⟨567017, by rfl⟩ : syracuseStep 756023 = 1134035) B1134035
theorem B756043 : Blo 754331 756043 := bstep (se 1 (by rfl) ⟨567032, by rfl⟩ : syracuseStep 756043 = 1134065) B1134065
theorem B756055 : Blo 754331 756055 := bstep (se 1 (by rfl) ⟨567041, by rfl⟩ : syracuseStep 756055 = 1134083) B1134083
theorem B756075 : Blo 754331 756075 := bstep (se 1 (by rfl) ⟨567056, by rfl⟩ : syracuseStep 756075 = 1134113) B1134113
theorem B756087 : Blo 754331 756087 := bstep (se 1 (by rfl) ⟨567065, by rfl⟩ : syracuseStep 756087 = 1134131) B1134131
theorem B756107 : Blo 754331 756107 := bstep (se 1 (by rfl) ⟨567080, by rfl⟩ : syracuseStep 756107 = 1134161) B1134161
theorem B756119 : Blo 754331 756119 := bstep (se 1 (by rfl) ⟨567089, by rfl⟩ : syracuseStep 756119 = 1134179) B1134179
theorem B756139 : Blo 754331 756139 := bstep (se 1 (by rfl) ⟨567104, by rfl⟩ : syracuseStep 756139 = 1134209) B1134209
theorem B756151 : Blo 754331 756151 := bstep (se 1 (by rfl) ⟨567113, by rfl⟩ : syracuseStep 756151 = 1134227) B1134227
theorem B756171 : Blo 754331 756171 := bstep (se 1 (by rfl) ⟨567128, by rfl⟩ : syracuseStep 756171 = 1134257) B1134257
theorem B2558411 : Blo 754331 2558411 := bstep (se 1 (by rfl) ⟨1918808, by rfl⟩ : syracuseStep 2558411 = 3837617) B3837617
theorem B756183 : Blo 754331 756183 := bstep (se 1 (by rfl) ⟨567137, by rfl⟩ : syracuseStep 756183 = 1134275) B1134275
theorem B756203 : Blo 754331 756203 := bstep (se 1 (by rfl) ⟨567152, by rfl⟩ : syracuseStep 756203 = 1134305) B1134305
theorem B756215 : Blo 754331 756215 := bstep (se 1 (by rfl) ⟨567161, by rfl⟩ : syracuseStep 756215 = 1134323) B1134323
theorem B756235 : Blo 754331 756235 := bstep (se 1 (by rfl) ⟨567176, by rfl⟩ : syracuseStep 756235 = 1134353) B1134353
theorem B756247 : Blo 754331 756247 := bstep (se 1 (by rfl) ⟨567185, by rfl⟩ : syracuseStep 756247 = 1134371) B1134371
theorem B756267 : Blo 754331 756267 := bstep (se 1 (by rfl) ⟨567200, by rfl⟩ : syracuseStep 756267 = 1134401) B1134401
theorem B2722355 : Blo 754331 2722355 := bstep (se 1 (by rfl) ⟨2041766, by rfl⟩ : syracuseStep 2722355 = 4083533) B4083533
theorem B756279 : Blo 754331 756279 := bstep (se 1 (by rfl) ⟨567209, by rfl⟩ : syracuseStep 756279 = 1134419) B1134419
theorem B2591297 : Blo 754331 2591297 := bstep (se 2 (by rfl) ⟨971736, by rfl⟩ : syracuseStep 2591297 = 1943473) B1943473
theorem B756299 : Blo 754331 756299 := bstep (se 1 (by rfl) ⟨567224, by rfl⟩ : syracuseStep 756299 = 1134449) B1134449
theorem B756311 : Blo 754331 756311 := bstep (se 1 (by rfl) ⟨567233, by rfl⟩ : syracuseStep 756311 = 1134467) B1134467
theorem B756331 : Blo 754331 756331 := bstep (se 1 (by rfl) ⟨567248, by rfl⟩ : syracuseStep 756331 = 1134497) B1134497
theorem B756343 : Blo 754331 756343 := bstep (se 1 (by rfl) ⟨567257, by rfl⟩ : syracuseStep 756343 = 1134515) B1134515
theorem B756363 : Blo 754331 756363 := bstep (se 1 (by rfl) ⟨567272, by rfl⟩ : syracuseStep 756363 = 1134545) B1134545
theorem B756375 : Blo 754331 756375 := bstep (se 1 (by rfl) ⟨567281, by rfl⟩ : syracuseStep 756375 = 1134563) B1134563
theorem B756395 : Blo 754331 756395 := bstep (se 1 (by rfl) ⟨567296, by rfl⟩ : syracuseStep 756395 = 1134593) B1134593
theorem B756407 : Blo 754331 756407 := bstep (se 1 (by rfl) ⟨567305, by rfl⟩ : syracuseStep 756407 = 1134611) B1134611
theorem B756427 : Blo 754331 756427 := bstep (se 1 (by rfl) ⟨567320, by rfl⟩ : syracuseStep 756427 = 1134641) B1134641
theorem B756439 : Blo 754331 756439 := bstep (se 1 (by rfl) ⟨567329, by rfl⟩ : syracuseStep 756439 = 1134659) B1134659
theorem B2558681 : Blo 754331 2558681 := bstep (se 2 (by rfl) ⟨959505, by rfl⟩ : syracuseStep 2558681 = 1919011) B1919011
theorem B756459 : Blo 754331 756459 := bstep (se 1 (by rfl) ⟨567344, by rfl⟩ : syracuseStep 756459 = 1134689) B1134689
theorem B756471 : Blo 754331 756471 := bstep (se 1 (by rfl) ⟨567353, by rfl⟩ : syracuseStep 756471 = 1134707) B1134707
theorem B12258053 : Blo 754331 12258053 := bstep (se 4 (by rfl) ⟨1149192, by rfl⟩ : syracuseStep 12258053 = 2298385) B2298385
theorem B756491 : Blo 754331 756491 := bstep (se 1 (by rfl) ⟨567368, by rfl⟩ : syracuseStep 756491 = 1134737) B1134737
theorem B756503 : Blo 754331 756503 := bstep (se 1 (by rfl) ⟨567377, by rfl⟩ : syracuseStep 756503 = 1134755) B1134755
theorem B756523 : Blo 754331 756523 := bstep (se 1 (by rfl) ⟨567392, by rfl⟩ : syracuseStep 756523 = 1134785) B1134785
theorem B756535 : Blo 754331 756535 := bstep (se 1 (by rfl) ⟨567401, by rfl⟩ : syracuseStep 756535 = 1134803) B1134803
theorem B756555 : Blo 754331 756555 := bstep (se 1 (by rfl) ⟨567416, by rfl⟩ : syracuseStep 756555 = 1134833) B1134833
theorem B756567 : Blo 754331 756567 := bstep (se 1 (by rfl) ⟨567425, by rfl⟩ : syracuseStep 756567 = 1134851) B1134851
theorem B756587 : Blo 754331 756587 := bstep (se 1 (by rfl) ⟨567440, by rfl⟩ : syracuseStep 756587 = 1134881) B1134881
theorem B756599 : Blo 754331 756599 := bstep (se 1 (by rfl) ⟨567449, by rfl⟩ : syracuseStep 756599 = 1134899) B1134899
theorem B756619 : Blo 754331 756619 := bstep (se 1 (by rfl) ⟨567464, by rfl⟩ : syracuseStep 756619 = 1134929) B1134929
theorem B756631 : Blo 754331 756631 := bstep (se 1 (by rfl) ⟨567473, by rfl⟩ : syracuseStep 756631 = 1134947) B1134947
theorem B756651 : Blo 754331 756651 := bstep (se 1 (by rfl) ⟨567488, by rfl⟩ : syracuseStep 756651 = 1134977) B1134977
theorem B756663 : Blo 754331 756663 := bstep (se 1 (by rfl) ⟨567497, by rfl⟩ : syracuseStep 756663 = 1134995) B1134995
theorem B756683 : Blo 754331 756683 := bstep (se 1 (by rfl) ⟨567512, by rfl⟩ : syracuseStep 756683 = 1135025) B1135025
theorem B756695 : Blo 754331 756695 := bstep (se 1 (by rfl) ⟨567521, by rfl⟩ : syracuseStep 756695 = 1135043) B1135043
theorem B756715 : Blo 754331 756715 := bstep (se 1 (by rfl) ⟨567536, by rfl⟩ : syracuseStep 756715 = 1135073) B1135073
theorem B756727 : Blo 754331 756727 := bstep (se 1 (by rfl) ⟨567545, by rfl⟩ : syracuseStep 756727 = 1135091) B1135091
theorem B756747 : Blo 754331 756747 := bstep (se 1 (by rfl) ⟨567560, by rfl⟩ : syracuseStep 756747 = 1135121) B1135121
theorem B756759 : Blo 754331 756759 := bstep (se 1 (by rfl) ⟨567569, by rfl⟩ : syracuseStep 756759 = 1135139) B1135139
theorem B756779 : Blo 754331 756779 := bstep (se 1 (by rfl) ⟨567584, by rfl⟩ : syracuseStep 756779 = 1135169) B1135169
theorem B756791 : Blo 754331 756791 := bstep (se 1 (by rfl) ⟨567593, by rfl⟩ : syracuseStep 756791 = 1135187) B1135187
theorem B756811 : Blo 754331 756811 := bstep (se 1 (by rfl) ⟨567608, by rfl⟩ : syracuseStep 756811 = 1135217) B1135217
theorem B756823 : Blo 754331 756823 := bstep (se 1 (by rfl) ⟨567617, by rfl⟩ : syracuseStep 756823 = 1135235) B1135235
theorem B756843 : Blo 754331 756843 := bstep (se 1 (by rfl) ⟨567632, by rfl⟩ : syracuseStep 756843 = 1135265) B1135265
theorem B756855 : Blo 754331 756855 := bstep (se 1 (by rfl) ⟨567641, by rfl⟩ : syracuseStep 756855 = 1135283) B1135283
theorem B756875 : Blo 754331 756875 := bstep (se 1 (by rfl) ⟨567656, by rfl⟩ : syracuseStep 756875 = 1135313) B1135313
theorem B756887 : Blo 754331 756887 := bstep (se 1 (by rfl) ⟨567665, by rfl⟩ : syracuseStep 756887 = 1135331) B1135331
theorem B1150105 : Blo 754331 1150105 := bstep (se 2 (by rfl) ⟨431289, by rfl⟩ : syracuseStep 1150105 = 862579) B862579
theorem B756907 : Blo 754331 756907 := bstep (se 1 (by rfl) ⟨567680, by rfl⟩ : syracuseStep 756907 = 1135361) B1135361
theorem B756919 : Blo 754331 756919 := bstep (se 1 (by rfl) ⟨567689, by rfl⟩ : syracuseStep 756919 = 1135379) B1135379
theorem B756939 : Blo 754331 756939 := bstep (se 1 (by rfl) ⟨567704, by rfl⟩ : syracuseStep 756939 = 1135409) B1135409
theorem B756951 : Blo 754331 756951 := bstep (se 1 (by rfl) ⟨567713, by rfl⟩ : syracuseStep 756951 = 1135427) B1135427
theorem B756971 : Blo 754331 756971 := bstep (se 1 (by rfl) ⟨567728, by rfl⟩ : syracuseStep 756971 = 1135457) B1135457
theorem B756983 : Blo 754331 756983 := bstep (se 1 (by rfl) ⟨567737, by rfl⟩ : syracuseStep 756983 = 1135475) B1135475
theorem B757003 : Blo 754331 757003 := bstep (se 1 (by rfl) ⟨567752, by rfl⟩ : syracuseStep 757003 = 1135505) B1135505
theorem B757015 : Blo 754331 757015 := bstep (se 1 (by rfl) ⟨567761, by rfl⟩ : syracuseStep 757015 = 1135523) B1135523
theorem B757035 : Blo 754331 757035 := bstep (se 1 (by rfl) ⟨567776, by rfl⟩ : syracuseStep 757035 = 1135553) B1135553
theorem B757047 : Blo 754331 757047 := bstep (se 1 (by rfl) ⟨567785, by rfl⟩ : syracuseStep 757047 = 1135571) B1135571
theorem B757067 : Blo 754331 757067 := bstep (se 1 (by rfl) ⟨567800, by rfl⟩ : syracuseStep 757067 = 1135601) B1135601
theorem B757079 : Blo 754331 757079 := bstep (se 1 (by rfl) ⟨567809, by rfl⟩ : syracuseStep 757079 = 1135619) B1135619
theorem B757099 : Blo 754331 757099 := bstep (se 1 (by rfl) ⟨567824, by rfl⟩ : syracuseStep 757099 = 1135649) B1135649
theorem B757111 : Blo 754331 757111 := bstep (se 1 (by rfl) ⟨567833, by rfl⟩ : syracuseStep 757111 = 1135667) B1135667
theorem B757131 : Blo 754331 757131 := bstep (se 1 (by rfl) ⟨567848, by rfl⟩ : syracuseStep 757131 = 1135697) B1135697
theorem B757143 : Blo 754331 757143 := bstep (se 1 (by rfl) ⟨567857, by rfl⟩ : syracuseStep 757143 = 1135715) B1135715
theorem B757163 : Blo 754331 757163 := bstep (se 1 (by rfl) ⟨567872, by rfl⟩ : syracuseStep 757163 = 1135745) B1135745
theorem B757175 : Blo 754331 757175 := bstep (se 1 (by rfl) ⟨567881, by rfl⟩ : syracuseStep 757175 = 1135763) B1135763
theorem B757195 : Blo 754331 757195 := bstep (se 1 (by rfl) ⟨567896, by rfl⟩ : syracuseStep 757195 = 1135793) B1135793
theorem B757207 : Blo 754331 757207 := bstep (se 1 (by rfl) ⟨567905, by rfl⟩ : syracuseStep 757207 = 1135811) B1135811
theorem B757227 : Blo 754331 757227 := bstep (se 1 (by rfl) ⟨567920, by rfl⟩ : syracuseStep 757227 = 1135841) B1135841
theorem B757239 : Blo 754331 757239 := bstep (se 1 (by rfl) ⟨567929, by rfl⟩ : syracuseStep 757239 = 1135859) B1135859
theorem B757259 : Blo 754331 757259 := bstep (se 1 (by rfl) ⟨567944, by rfl⟩ : syracuseStep 757259 = 1135889) B1135889
theorem B757271 : Blo 754331 757271 := bstep (se 1 (by rfl) ⟨567953, by rfl⟩ : syracuseStep 757271 = 1135907) B1135907
theorem B757291 : Blo 754331 757291 := bstep (se 1 (by rfl) ⟨567968, by rfl⟩ : syracuseStep 757291 = 1135937) B1135937
theorem B757303 : Blo 754331 757303 := bstep (se 1 (by rfl) ⟨567977, by rfl⟩ : syracuseStep 757303 = 1135955) B1135955
theorem B2428481 : Blo 754331 2428481 := bstep (se 2 (by rfl) ⟨910680, by rfl⟩ : syracuseStep 2428481 = 1821361) B1821361
theorem B757323 : Blo 754331 757323 := bstep (se 1 (by rfl) ⟨567992, by rfl⟩ : syracuseStep 757323 = 1135985) B1135985
theorem B757335 : Blo 754331 757335 := bstep (se 1 (by rfl) ⟨568001, by rfl⟩ : syracuseStep 757335 = 1136003) B1136003
theorem B757355 : Blo 754331 757355 := bstep (se 1 (by rfl) ⟨568016, by rfl⟩ : syracuseStep 757355 = 1136033) B1136033
theorem B757367 : Blo 754331 757367 := bstep (se 1 (by rfl) ⟨568025, by rfl⟩ : syracuseStep 757367 = 1136051) B1136051
theorem B757387 : Blo 754331 757387 := bstep (se 1 (by rfl) ⟨568040, by rfl⟩ : syracuseStep 757387 = 1136081) B1136081
theorem B757399 : Blo 754331 757399 := bstep (se 1 (by rfl) ⟨568049, by rfl⟩ : syracuseStep 757399 = 1136099) B1136099
theorem B757419 : Blo 754331 757419 := bstep (se 1 (by rfl) ⟨568064, by rfl⟩ : syracuseStep 757419 = 1136129) B1136129
theorem B757431 : Blo 754331 757431 := bstep (se 1 (by rfl) ⟨568073, by rfl⟩ : syracuseStep 757431 = 1136147) B1136147
theorem B757451 : Blo 754331 757451 := bstep (se 1 (by rfl) ⟨568088, by rfl⟩ : syracuseStep 757451 = 1136177) B1136177
theorem B757463 : Blo 754331 757463 := bstep (se 1 (by rfl) ⟨568097, by rfl⟩ : syracuseStep 757463 = 1136195) B1136195
theorem B5738201 : Blo 754331 5738201 := bstep (se 2 (by rfl) ⟨2151825, by rfl⟩ : syracuseStep 5738201 = 4303651) B4303651
theorem B757483 : Blo 754331 757483 := bstep (se 1 (by rfl) ⟨568112, by rfl⟩ : syracuseStep 757483 = 1136225) B1136225
theorem B757495 : Blo 754331 757495 := bstep (se 1 (by rfl) ⟨568121, by rfl⟩ : syracuseStep 757495 = 1136243) B1136243
theorem B757515 : Blo 754331 757515 := bstep (se 1 (by rfl) ⟨568136, by rfl⟩ : syracuseStep 757515 = 1136273) B1136273
theorem B757527 : Blo 754331 757527 := bstep (se 1 (by rfl) ⟨568145, by rfl⟩ : syracuseStep 757527 = 1136291) B1136291
theorem B6885155 : Blo 754331 6885155 := bstep (se 1 (by rfl) ⟨5163866, by rfl⟩ : syracuseStep 6885155 = 10327733) B10327733
theorem B757547 : Blo 754331 757547 := bstep (se 1 (by rfl) ⟨568160, by rfl⟩ : syracuseStep 757547 = 1136321) B1136321
theorem B757559 : Blo 754331 757559 := bstep (se 1 (by rfl) ⟨568169, by rfl⟩ : syracuseStep 757559 = 1136339) B1136339
theorem B757579 : Blo 754331 757579 := bstep (se 1 (by rfl) ⟨568184, by rfl⟩ : syracuseStep 757579 = 1136369) B1136369
theorem B757591 : Blo 754331 757591 := bstep (se 1 (by rfl) ⟨568193, by rfl⟩ : syracuseStep 757591 = 1136387) B1136387
theorem B757611 : Blo 754331 757611 := bstep (se 1 (by rfl) ⟨568208, by rfl⟩ : syracuseStep 757611 = 1136417) B1136417
theorem B757623 : Blo 754331 757623 := bstep (se 1 (by rfl) ⟨568217, by rfl⟩ : syracuseStep 757623 = 1136435) B1136435
theorem B757643 : Blo 754331 757643 := bstep (se 1 (by rfl) ⟨568232, by rfl⟩ : syracuseStep 757643 = 1136465) B1136465
theorem B757655 : Blo 754331 757655 := bstep (se 1 (by rfl) ⟨568241, by rfl⟩ : syracuseStep 757655 = 1136483) B1136483
theorem B757675 : Blo 754331 757675 := bstep (se 1 (by rfl) ⟨568256, by rfl⟩ : syracuseStep 757675 = 1136513) B1136513
theorem B757687 : Blo 754331 757687 := bstep (se 1 (by rfl) ⟨568265, by rfl⟩ : syracuseStep 757687 = 1136531) B1136531
theorem B2297803 : Blo 754331 2297803 := bstep (se 1 (by rfl) ⟨1723352, by rfl⟩ : syracuseStep 2297803 = 3446705) B3446705
theorem B757707 : Blo 754331 757707 := bstep (se 1 (by rfl) ⟨568280, by rfl⟩ : syracuseStep 757707 = 1136561) B1136561
theorem B757719 : Blo 754331 757719 := bstep (se 1 (by rfl) ⟨568289, by rfl⟩ : syracuseStep 757719 = 1136579) B1136579
theorem B757739 : Blo 754331 757739 := bstep (se 1 (by rfl) ⟨568304, by rfl⟩ : syracuseStep 757739 = 1136609) B1136609
theorem B757751 : Blo 754331 757751 := bstep (se 1 (by rfl) ⟨568313, by rfl⟩ : syracuseStep 757751 = 1136627) B1136627
theorem B757771 : Blo 754331 757771 := bstep (se 1 (by rfl) ⟨568328, by rfl⟩ : syracuseStep 757771 = 1136657) B1136657
theorem B757783 : Blo 754331 757783 := bstep (se 1 (by rfl) ⟨568337, by rfl⟩ : syracuseStep 757783 = 1136675) B1136675
theorem B757803 : Blo 754331 757803 := bstep (se 1 (by rfl) ⟨568352, by rfl⟩ : syracuseStep 757803 = 1136705) B1136705
theorem B757815 : Blo 754331 757815 := bstep (se 1 (by rfl) ⟨568361, by rfl⟩ : syracuseStep 757815 = 1136723) B1136723
theorem B757835 : Blo 754331 757835 := bstep (se 1 (by rfl) ⟨568376, by rfl⟩ : syracuseStep 757835 = 1136753) B1136753
theorem B757847 : Blo 754331 757847 := bstep (se 1 (by rfl) ⟨568385, by rfl⟩ : syracuseStep 757847 = 1136771) B1136771
theorem B757867 : Blo 754331 757867 := bstep (se 1 (by rfl) ⟨568400, by rfl⟩ : syracuseStep 757867 = 1136801) B1136801
theorem B757879 : Blo 754331 757879 := bstep (se 1 (by rfl) ⟨568409, by rfl⟩ : syracuseStep 757879 = 1136819) B1136819
theorem B757899 : Blo 754331 757899 := bstep (se 1 (by rfl) ⟨568424, by rfl⟩ : syracuseStep 757899 = 1136849) B1136849
theorem B757911 : Blo 754331 757911 := bstep (se 1 (by rfl) ⟨568433, by rfl⟩ : syracuseStep 757911 = 1136867) B1136867
theorem B3838103 : Blo 754331 3838103 := bstep (se 1 (by rfl) ⟨2878577, by rfl⟩ : syracuseStep 3838103 = 5757155) B5757155
theorem B757931 : Blo 754331 757931 := bstep (se 1 (by rfl) ⟨568448, by rfl⟩ : syracuseStep 757931 = 1136897) B1136897
theorem B757943 : Blo 754331 757943 := bstep (se 1 (by rfl) ⟨568457, by rfl⟩ : syracuseStep 757943 = 1136915) B1136915
theorem B2298059 : Blo 754331 2298059 := bstep (se 1 (by rfl) ⟨1723544, by rfl⟩ : syracuseStep 2298059 = 3447089) B3447089
theorem B757963 : Blo 754331 757963 := bstep (se 1 (by rfl) ⟨568472, by rfl⟩ : syracuseStep 757963 = 1136945) B1136945
theorem B757975 : Blo 754331 757975 := bstep (se 1 (by rfl) ⟨568481, by rfl⟩ : syracuseStep 757975 = 1136963) B1136963
theorem B757995 : Blo 754331 757995 := bstep (se 1 (by rfl) ⟨568496, by rfl⟩ : syracuseStep 757995 = 1136993) B1136993
theorem B758007 : Blo 754331 758007 := bstep (se 1 (by rfl) ⟨568505, by rfl⟩ : syracuseStep 758007 = 1137011) B1137011
theorem B758027 : Blo 754331 758027 := bstep (se 1 (by rfl) ⟨568520, by rfl⟩ : syracuseStep 758027 = 1137041) B1137041
theorem B758039 : Blo 754331 758039 := bstep (se 1 (by rfl) ⟨568529, by rfl⟩ : syracuseStep 758039 = 1137059) B1137059
theorem B758059 : Blo 754331 758059 := bstep (se 1 (by rfl) ⟨568544, by rfl⟩ : syracuseStep 758059 = 1137089) B1137089
theorem B758071 : Blo 754331 758071 := bstep (se 1 (by rfl) ⟨568553, by rfl⟩ : syracuseStep 758071 = 1137107) B1137107
theorem B758091 : Blo 754331 758091 := bstep (se 1 (by rfl) ⟨568568, by rfl⟩ : syracuseStep 758091 = 1137137) B1137137
theorem B758103 : Blo 754331 758103 := bstep (se 1 (by rfl) ⟨568577, by rfl⟩ : syracuseStep 758103 = 1137155) B1137155
theorem B758123 : Blo 754331 758123 := bstep (se 1 (by rfl) ⟨568592, by rfl⟩ : syracuseStep 758123 = 1137185) B1137185
theorem B758135 : Blo 754331 758135 := bstep (se 1 (by rfl) ⟨568601, by rfl⟩ : syracuseStep 758135 = 1137203) B1137203
theorem B758155 : Blo 754331 758155 := bstep (se 1 (by rfl) ⟨568616, by rfl⟩ : syracuseStep 758155 = 1137233) B1137233
theorem B758167 : Blo 754331 758167 := bstep (se 1 (by rfl) ⟨568625, by rfl⟩ : syracuseStep 758167 = 1137251) B1137251
theorem B758187 : Blo 754331 758187 := bstep (se 1 (by rfl) ⟨568640, by rfl⟩ : syracuseStep 758187 = 1137281) B1137281
theorem B758199 : Blo 754331 758199 := bstep (se 1 (by rfl) ⟨568649, by rfl⟩ : syracuseStep 758199 = 1137299) B1137299
theorem B758219 : Blo 754331 758219 := bstep (se 1 (by rfl) ⟨568664, by rfl⟩ : syracuseStep 758219 = 1137329) B1137329
theorem B758231 : Blo 754331 758231 := bstep (se 1 (by rfl) ⟨568673, by rfl⟩ : syracuseStep 758231 = 1137347) B1137347
theorem B758251 : Blo 754331 758251 := bstep (se 1 (by rfl) ⟨568688, by rfl⟩ : syracuseStep 758251 = 1137377) B1137377
theorem B758263 : Blo 754331 758263 := bstep (se 1 (by rfl) ⟨568697, by rfl⟩ : syracuseStep 758263 = 1137395) B1137395
theorem B3281411 : Blo 754331 3281411 := bstep (se 1 (by rfl) ⟨2461058, by rfl⟩ : syracuseStep 3281411 = 4922117) B4922117
theorem B758283 : Blo 754331 758283 := bstep (se 1 (by rfl) ⟨568712, by rfl⟩ : syracuseStep 758283 = 1137425) B1137425
theorem B758295 : Blo 754331 758295 := bstep (se 1 (by rfl) ⟨568721, by rfl⟩ : syracuseStep 758295 = 1137443) B1137443
theorem B758315 : Blo 754331 758315 := bstep (se 1 (by rfl) ⟨568736, by rfl⟩ : syracuseStep 758315 = 1137473) B1137473
theorem B758327 : Blo 754331 758327 := bstep (se 1 (by rfl) ⟨568745, by rfl⟩ : syracuseStep 758327 = 1137491) B1137491
theorem B21041795 : Blo 754331 21041795 := bstep (se 1 (by rfl) ⟨15781346, by rfl⟩ : syracuseStep 21041795 = 31562693) B31562693
theorem B9966341 : Blo 754331 9966341 := bstep (se 4 (by rfl) ⟨934344, by rfl⟩ : syracuseStep 9966341 = 1868689) B1868689
theorem B955147 : Blo 754331 955147 := bstep (se 1 (by rfl) ⟨716360, by rfl⟩ : syracuseStep 955147 = 1432721) B1432721
theorem B6886295 : Blo 754331 6886295 := bstep (se 1 (by rfl) ⟨5164721, by rfl⟩ : syracuseStep 6886295 = 10329443) B10329443
theorem B2593757 : Blo 754331 2593757 := bstep (se 3 (by rfl) ⟨486329, by rfl⟩ : syracuseStep 2593757 = 972659) B972659
theorem B955415 : Blo 754331 955415 := bstep (se 1 (by rfl) ⟨716561, by rfl⟩ : syracuseStep 955415 = 1433123) B1433123
theorem B2725123 : Blo 754331 2725123 := bstep (se 1 (by rfl) ⟨2043842, by rfl⟩ : syracuseStep 2725123 = 4087685) B4087685
theorem B1611265 : Blo 754331 1611265 := bstep (se 2 (by rfl) ⟨604224, by rfl⟩ : syracuseStep 1611265 = 1208449) B1208449
theorem B1938995 : Blo 754331 1938995 := bstep (se 1 (by rfl) ⟨1454246, by rfl⟩ : syracuseStep 1938995 = 2908493) B2908493
theorem B1021591 : Blo 754331 1021591 := bstep (se 1 (by rfl) ⟨766193, by rfl⟩ : syracuseStep 1021591 = 1532387) B1532387
theorem B956119 : Blo 754331 956119 := bstep (se 1 (by rfl) ⟨717089, by rfl⟩ : syracuseStep 956119 = 1434179) B1434179
theorem B2660057 : Blo 754331 2660057 := bstep (se 2 (by rfl) ⟨997521, by rfl⟩ : syracuseStep 2660057 = 1995043) B1995043
theorem B1152971 : Blo 754331 1152971 := bstep (se 1 (by rfl) ⟨864728, by rfl⟩ : syracuseStep 1152971 = 1729457) B1729457
theorem B9672965 : Blo 754331 9672965 := bstep (se 4 (by rfl) ⟨906840, by rfl⟩ : syracuseStep 9672965 = 1813681) B1813681
theorem B5446349 : Blo 754331 5446349 := bstep (se 3 (by rfl) ⟨1021190, by rfl⟩ : syracuseStep 5446349 = 2042381) B2042381
theorem B1612811 : Blo 754331 1612811 := bstep (se 1 (by rfl) ⟨1209608, by rfl⟩ : syracuseStep 1612811 = 2419217) B2419217
theorem B5741603 : Blo 754331 5741603 := bstep (se 1 (by rfl) ⟨4306202, by rfl⟩ : syracuseStep 5741603 = 8612405) B8612405
theorem B4660325 : Blo 754331 4660325 := bstep (se 4 (by rfl) ⟨436905, by rfl⟩ : syracuseStep 4660325 = 873811) B873811
theorem B957835 : Blo 754331 957835 := bstep (se 1 (by rfl) ⟨718376, by rfl⟩ : syracuseStep 957835 = 1436753) B1436753
theorem B2727731 : Blo 754331 2727731 := bstep (se 1 (by rfl) ⟨2045798, by rfl⟩ : syracuseStep 2727731 = 4091597) B4091597
theorem B1613657 : Blo 754331 1613657 := bstep (se 2 (by rfl) ⟨605121, by rfl⟩ : syracuseStep 1613657 = 1210243) B1210243
theorem B12951413 : Blo 754331 12951413 := bstep (se 5 (by rfl) ⟨607097, by rfl⟩ : syracuseStep 12951413 = 1214195) B1214195
theorem B1941707 : Blo 754331 1941707 := bstep (se 1 (by rfl) ⟨1456280, by rfl⟩ : syracuseStep 1941707 = 2912561) B2912561
theorem B2728237 : Blo 754331 2728237 := bstep (se 3 (by rfl) ⟨511544, by rfl⟩ : syracuseStep 2728237 = 1023089) B1023089
theorem B958807 : Blo 754331 958807 := bstep (se 1 (by rfl) ⟨719105, by rfl⟩ : syracuseStep 958807 = 1438211) B1438211
theorem B1614451 : Blo 754331 1614451 := bstep (se 1 (by rfl) ⟨1210838, by rfl⟩ : syracuseStep 1614451 = 2421677) B2421677
theorem B959627 : Blo 754331 959627 := bstep (se 1 (by rfl) ⟨719720, by rfl⟩ : syracuseStep 959627 = 1439441) B1439441
theorem B1909939 : Blo 754331 1909939 := bstep (se 1 (by rfl) ⟨1432454, by rfl⟩ : syracuseStep 1909939 = 2864909) B2864909
theorem B1910081 : Blo 754331 1910081 := bstep (se 2 (by rfl) ⟨716280, by rfl⟩ : syracuseStep 1910081 = 1432561) B1432561
theorem B1615297 : Blo 754331 1615297 := bstep (se 2 (by rfl) ⟨605736, by rfl⟩ : syracuseStep 1615297 = 1211473) B1211473
theorem B4302467 : Blo 754331 4302467 := bstep (se 1 (by rfl) ⟨3226850, by rfl⟩ : syracuseStep 4302467 = 6453701) B6453701
theorem B4990643 : Blo 754331 4990643 := bstep (se 1 (by rfl) ⟨3742982, by rfl⟩ : syracuseStep 4990643 = 7485965) B7485965
theorem B8726221 : Blo 754331 8726221 := bstep (se 3 (by rfl) ⟨1636166, by rfl⟩ : syracuseStep 8726221 = 3272333) B3272333
theorem B1615639 : Blo 754331 1615639 := bstep (se 1 (by rfl) ⟨1211729, by rfl⟩ : syracuseStep 1615639 = 2423459) B2423459
theorem B10889005 : Blo 754331 10889005 := bstep (se 3 (by rfl) ⟨2041688, by rfl⟩ : syracuseStep 10889005 = 4083377) B4083377
theorem B9348965 : Blo 754331 9348965 := bstep (se 4 (by rfl) ⟨876465, by rfl⟩ : syracuseStep 9348965 = 1752931) B1752931
theorem B4368563 : Blo 754331 4368563 := bstep (se 1 (by rfl) ⟨3276422, by rfl⟩ : syracuseStep 4368563 = 6552845) B6552845
theorem B13805923 : Blo 754331 13805923 := bstep (se 1 (by rfl) ⟨10354442, by rfl⟩ : syracuseStep 13805923 = 20708885) B20708885
theorem B1911347 : Blo 754331 1911347 := bstep (se 1 (by rfl) ⟨1433510, by rfl⟩ : syracuseStep 1911347 = 2867021) B2867021
theorem B1813067 : Blo 754331 1813067 := bstep (se 1 (by rfl) ⟨1359800, by rfl⟩ : syracuseStep 1813067 = 2719601) B2719601
theorem B1616843 : Blo 754331 1616843 := bstep (se 1 (by rfl) ⟨1212632, by rfl⟩ : syracuseStep 1616843 = 2425265) B2425265
theorem B1911883 : Blo 754331 1911883 := bstep (se 1 (by rfl) ⟨1433912, by rfl⟩ : syracuseStep 1911883 = 2867825) B2867825
theorem B2043073 : Blo 754331 2043073 := bstep (se 2 (by rfl) ⟨766152, by rfl⟩ : syracuseStep 2043073 = 1532305) B1532305
theorem B1912025 : Blo 754331 1912025 := bstep (se 2 (by rfl) ⟨717009, by rfl⟩ : syracuseStep 1912025 = 1434019) B1434019
theorem B1617355 : Blo 754331 1617355 := bstep (se 1 (by rfl) ⟨1213016, by rfl⟩ : syracuseStep 1617355 = 2426033) B2426033
theorem B31075811 : Blo 754331 31075811 := bstep (se 1 (by rfl) ⟨23306858, by rfl⟩ : syracuseStep 31075811 = 46613717) B46613717
theorem B3223091 : Blo 754331 3223091 := bstep (se 1 (by rfl) ⟨2417318, by rfl⟩ : syracuseStep 3223091 = 4834637) B4834637
theorem B1093271 : Blo 754331 1093271 := bstep (se 1 (by rfl) ⟨819953, by rfl⟩ : syracuseStep 1093271 = 1639907) B1639907
theorem B1945523 : Blo 754331 1945523 := bstep (se 1 (by rfl) ⟨1459142, by rfl⟩ : syracuseStep 1945523 = 2918285) B2918285
theorem B1814489 : Blo 754331 1814489 := bstep (se 2 (by rfl) ⟨680433, by rfl⟩ : syracuseStep 1814489 = 1360867) B1360867
theorem B1912855 : Blo 754331 1912855 := bstep (se 1 (by rfl) ⟨1434641, by rfl⟩ : syracuseStep 1912855 = 2869283) B2869283
theorem B1618073 : Blo 754331 1618073 := bstep (se 2 (by rfl) ⟨606777, by rfl⟩ : syracuseStep 1618073 = 1213555) B1213555
theorem B5746949 : Blo 754331 5746949 := bstep (se 4 (by rfl) ⟨538776, by rfl⟩ : syracuseStep 5746949 = 1077553) B1077553
theorem B8597825 : Blo 754331 8597825 := bstep (se 2 (by rfl) ⟨3224184, by rfl⟩ : syracuseStep 8597825 = 6448369) B6448369
theorem B1913291 : Blo 754331 1913291 := bstep (se 1 (by rfl) ⟨1434968, by rfl⟩ : syracuseStep 1913291 = 2869937) B2869937
theorem B1618483 : Blo 754331 1618483 := bstep (se 1 (by rfl) ⟨1213862, by rfl⟩ : syracuseStep 1618483 = 2427725) B2427725
theorem B9187991 : Blo 754331 9187991 := bstep (se 1 (by rfl) ⟨6890993, by rfl⟩ : syracuseStep 9187991 = 13781987) B13781987
theorem B1913665 : Blo 754331 1913665 := bstep (se 2 (by rfl) ⟨717624, by rfl⟩ : syracuseStep 1913665 = 1435249) B1435249
theorem B1553623 : Blo 754331 1553623 := bstep (se 1 (by rfl) ⟨1165217, by rfl⟩ : syracuseStep 1553623 = 2330435) B2330435
theorem B1914263 : Blo 754331 1914263 := bstep (se 1 (by rfl) ⟨1435697, by rfl⟩ : syracuseStep 1914263 = 2871395) B2871395
theorem B3225005 : Blo 754331 3225005 := bstep (se 3 (by rfl) ⟨604688, by rfl⟩ : syracuseStep 3225005 = 1209377) B1209377
theorem B2864605 : Blo 754331 2864605 := bstep (se 3 (by rfl) ⟨537113, by rfl⟩ : syracuseStep 2864605 = 1074227) B1074227
theorem B5813765 : Blo 754331 5813765 := bstep (se 4 (by rfl) ⟨545040, by rfl⟩ : syracuseStep 5813765 = 1090081) B1090081
theorem B9713357 : Blo 754331 9713357 := bstep (se 3 (by rfl) ⟨1821254, by rfl⟩ : syracuseStep 9713357 = 3642509) B3642509
theorem B3225689 : Blo 754331 3225689 := bstep (se 2 (by rfl) ⟨1209633, by rfl⟩ : syracuseStep 3225689 = 2419267) B2419267
theorem B2209943 : Blo 754331 2209943 := bstep (se 1 (by rfl) ⟨1657457, by rfl⟩ : syracuseStep 2209943 = 3314915) B3314915
theorem B1915073 : Blo 754331 1915073 := bstep (se 2 (by rfl) ⟨718152, by rfl⟩ : syracuseStep 1915073 = 1436305) B1436305
theorem B12925169 : Blo 754331 12925169 := bstep (se 2 (by rfl) ⟨4846938, by rfl⟩ : syracuseStep 12925169 = 9693877) B9693877
theorem B16366211 : Blo 754331 16366211 := bstep (se 1 (by rfl) ⟨12274658, by rfl⟩ : syracuseStep 16366211 = 24549317) B24549317
theorem B5749379 : Blo 754331 5749379 := bstep (se 1 (by rfl) ⟨4312034, by rfl⟩ : syracuseStep 5749379 = 8624069) B8624069
theorem B18430669 : Blo 754331 18430669 := bstep (se 3 (by rfl) ⟨3455750, by rfl⟩ : syracuseStep 18430669 = 6911501) B6911501
theorem B2865881 : Blo 754331 2865881 := bstep (se 2 (by rfl) ⟨1074705, by rfl⟩ : syracuseStep 2865881 = 2149411) B2149411
theorem B1915609 : Blo 754331 1915609 := bstep (se 2 (by rfl) ⟨718353, by rfl⟩ : syracuseStep 1915609 = 1436707) B1436707
theorem B4307843 : Blo 754331 4307843 := bstep (se 1 (by rfl) ⟨3230882, by rfl⟩ : syracuseStep 4307843 = 6461765) B6461765
theorem B1457203 : Blo 754331 1457203 := bstep (se 1 (by rfl) ⟨1092902, by rfl⟩ : syracuseStep 1457203 = 2185805) B2185805
theorem B3882077 : Blo 754331 3882077 := bstep (se 3 (by rfl) ⟨727889, by rfl⟩ : syracuseStep 3882077 = 1455779) B1455779
theorem B3226817 : Blo 754331 3226817 := bstep (se 2 (by rfl) ⟨1210056, by rfl⟩ : syracuseStep 3226817 = 2420113) B2420113
theorem B4308299 : Blo 754331 4308299 := bstep (se 1 (by rfl) ⟨3231224, by rfl⟩ : syracuseStep 4308299 = 6462449) B6462449
theorem B1162585 : Blo 754331 1162585 := bstep (se 2 (by rfl) ⟨435969, by rfl⟩ : syracuseStep 1162585 = 871939) B871939
theorem B10927709 : Blo 754331 10927709 := bstep (se 3 (by rfl) ⟨2048945, by rfl⟩ : syracuseStep 10927709 = 4097891) B4097891
theorem B1359511 : Blo 754331 1359511 := bstep (se 1 (by rfl) ⟨1019633, by rfl⟩ : syracuseStep 1359511 = 2039267) B2039267
theorem B1916723 : Blo 754331 1916723 := bstep (se 1 (by rfl) ⟨1437542, by rfl⟩ : syracuseStep 1916723 = 2875085) B2875085
theorem B18693989 : Blo 754331 18693989 := bstep (se 4 (by rfl) ⟨1752561, by rfl⟩ : syracuseStep 18693989 = 3505123) B3505123
theorem B3063703 : Blo 754331 3063703 := bstep (se 1 (by rfl) ⟨2297777, by rfl⟩ : syracuseStep 3063703 = 4595555) B4595555
theorem B6471575 : Blo 754331 6471575 := bstep (se 1 (by rfl) ⟨4853681, by rfl⟩ : syracuseStep 6471575 = 9707363) B9707363
theorem B18432035 : Blo 754331 18432035 := bstep (se 1 (by rfl) ⟨13824026, by rfl⟩ : syracuseStep 18432035 = 27648053) B27648053
theorem B1458251 : Blo 754331 1458251 := bstep (se 1 (by rfl) ⟨1093688, by rfl⟩ : syracuseStep 1458251 = 2187377) B2187377
theorem B1917017 : Blo 754331 1917017 := bstep (se 2 (by rfl) ⟨718881, by rfl⟩ : syracuseStep 1917017 = 1437763) B1437763
theorem B7356509 : Blo 754331 7356509 := bstep (se 3 (by rfl) ⟨1379345, by rfl⟩ : syracuseStep 7356509 = 2758691) B2758691
theorem B4079747 : Blo 754331 4079747 := bstep (se 1 (by rfl) ⟨3059810, by rfl⟩ : syracuseStep 4079747 = 6119621) B6119621
theorem B4079917 : Blo 754331 4079917 := bstep (se 3 (by rfl) ⟨764984, by rfl⟩ : syracuseStep 4079917 = 1529969) B1529969
theorem B2867507 : Blo 754331 2867507 := bstep (se 1 (by rfl) ⟨2150630, by rfl⟩ : syracuseStep 2867507 = 4301261) B4301261
theorem B2867521 : Blo 754331 2867521 := bstep (se 2 (by rfl) ⟨1075320, by rfl⟩ : syracuseStep 2867521 = 2150641) B2150641
theorem B4833715 : Blo 754331 4833715 := bstep (se 1 (by rfl) ⟨3625286, by rfl⟩ : syracuseStep 4833715 = 7250573) B7250573
theorem B3228491 : Blo 754331 3228491 := bstep (se 1 (by rfl) ⟨2421368, by rfl⟩ : syracuseStep 3228491 = 4842737) B4842737
theorem B1131545 : Blo 754331 1131545 := bstep (se 2 (by rfl) ⟨424329, by rfl⟩ : syracuseStep 1131545 = 848659) B848659
theorem B1131659 : Blo 754331 1131659 := bstep (se 1 (by rfl) ⟨848744, by rfl⟩ : syracuseStep 1131659 = 1697489) B1697489
theorem B1131671 : Blo 754331 1131671 := bstep (se 1 (by rfl) ⟨848753, by rfl⟩ : syracuseStep 1131671 = 1697507) B1697507
theorem B1131737 : Blo 754331 1131737 := bstep (se 2 (by rfl) ⟨424401, by rfl⟩ : syracuseStep 1131737 = 848803) B848803
theorem B1131851 : Blo 754331 1131851 := bstep (se 1 (by rfl) ⟨848888, by rfl⟩ : syracuseStep 1131851 = 1697777) B1697777
theorem B1131863 : Blo 754331 1131863 := bstep (se 1 (by rfl) ⟨848897, by rfl⟩ : syracuseStep 1131863 = 1697795) B1697795
theorem B13813091 : Blo 754331 13813091 := bstep (se 1 (by rfl) ⟨10359818, by rfl⟩ : syracuseStep 13813091 = 20719637) B20719637
theorem B1131929 : Blo 754331 1131929 := bstep (se 2 (by rfl) ⟨424473, by rfl⟩ : syracuseStep 1131929 = 848947) B848947
theorem B1132043 : Blo 754331 1132043 := bstep (se 1 (by rfl) ⟨849032, by rfl⟩ : syracuseStep 1132043 = 1698065) B1698065
theorem B1132055 : Blo 754331 1132055 := bstep (se 1 (by rfl) ⟨849041, by rfl⟩ : syracuseStep 1132055 = 1698083) B1698083
theorem B1132121 : Blo 754331 1132121 := bstep (se 2 (by rfl) ⟨424545, by rfl⟩ : syracuseStep 1132121 = 849091) B849091
theorem B1132235 : Blo 754331 1132235 := bstep (se 1 (by rfl) ⟨849176, by rfl⟩ : syracuseStep 1132235 = 1698353) B1698353
theorem B1918667 : Blo 754331 1918667 := bstep (se 1 (by rfl) ⟨1439000, by rfl⟩ : syracuseStep 1918667 = 2878001) B2878001
theorem B1132247 : Blo 754331 1132247 := bstep (se 1 (by rfl) ⟨849185, by rfl⟩ : syracuseStep 1132247 = 1698371) B1698371
theorem B1132313 : Blo 754331 1132313 := bstep (se 2 (by rfl) ⟨424617, by rfl⟩ : syracuseStep 1132313 = 849235) B849235
theorem B1132427 : Blo 754331 1132427 := bstep (se 1 (by rfl) ⟨849320, by rfl⟩ : syracuseStep 1132427 = 1698641) B1698641
theorem B1132439 : Blo 754331 1132439 := bstep (se 1 (by rfl) ⟨849329, by rfl⟩ : syracuseStep 1132439 = 1698659) B1698659
theorem B5752781 : Blo 754331 5752781 := bstep (se 3 (by rfl) ⟨1078646, by rfl⟩ : syracuseStep 5752781 = 2157293) B2157293
theorem B1132505 : Blo 754331 1132505 := bstep (se 2 (by rfl) ⟨424689, by rfl⟩ : syracuseStep 1132505 = 849379) B849379
theorem B5457881 : Blo 754331 5457881 := bstep (se 2 (by rfl) ⟨2046705, by rfl⟩ : syracuseStep 5457881 = 4093411) B4093411
theorem B1132619 : Blo 754331 1132619 := bstep (se 1 (by rfl) ⟨849464, by rfl⟩ : syracuseStep 1132619 = 1698929) B1698929
theorem B1132631 : Blo 754331 1132631 := bstep (se 1 (by rfl) ⟨849473, by rfl⟩ : syracuseStep 1132631 = 1698947) B1698947
theorem B3229789 : Blo 754331 3229789 := bstep (se 3 (by rfl) ⟨605585, by rfl⟩ : syracuseStep 3229789 = 1211171) B1211171
theorem B4901015 : Blo 754331 4901015 := bstep (se 1 (by rfl) ⟨3675761, by rfl⟩ : syracuseStep 4901015 = 7351523) B7351523
theorem B1132697 : Blo 754331 1132697 := bstep (se 2 (by rfl) ⟨424761, by rfl⟩ : syracuseStep 1132697 = 849523) B849523
theorem B3360941 : Blo 754331 3360941 := bstep (se 3 (by rfl) ⟨630176, by rfl⟩ : syracuseStep 3360941 = 1260353) B1260353
theorem B2148545 : Blo 754331 2148545 := bstep (se 2 (by rfl) ⟨805704, by rfl⟩ : syracuseStep 2148545 = 1611409) B1611409
theorem B2869451 : Blo 754331 2869451 := bstep (se 1 (by rfl) ⟨2152088, by rfl⟩ : syracuseStep 2869451 = 4304177) B4304177
theorem B2148569 : Blo 754331 2148569 := bstep (se 2 (by rfl) ⟨805713, by rfl⟩ : syracuseStep 2148569 = 1611427) B1611427
theorem B2869465 : Blo 754331 2869465 := bstep (se 2 (by rfl) ⟨1076049, by rfl⟩ : syracuseStep 2869465 = 2152099) B2152099
theorem B1132811 : Blo 754331 1132811 := bstep (se 1 (by rfl) ⟨849608, by rfl⟩ : syracuseStep 1132811 = 1699217) B1699217
theorem B1132823 : Blo 754331 1132823 := bstep (se 1 (by rfl) ⟨849617, by rfl⟩ : syracuseStep 1132823 = 1699235) B1699235
theorem B6637889 : Blo 754331 6637889 := bstep (se 2 (by rfl) ⟨2489208, by rfl⟩ : syracuseStep 6637889 = 4978417) B4978417
theorem B1132889 : Blo 754331 1132889 := bstep (se 2 (by rfl) ⟨424833, by rfl⟩ : syracuseStep 1132889 = 849667) B849667
theorem B3230131 : Blo 754331 3230131 := bstep (se 1 (by rfl) ⟨2422598, by rfl⟩ : syracuseStep 3230131 = 4845197) B4845197
theorem B5753267 : Blo 754331 5753267 := bstep (se 1 (by rfl) ⟨4314950, by rfl⟩ : syracuseStep 5753267 = 8629901) B8629901
theorem B1133003 : Blo 754331 1133003 := bstep (se 1 (by rfl) ⟨849752, by rfl⟩ : syracuseStep 1133003 = 1699505) B1699505
theorem B1133015 : Blo 754331 1133015 := bstep (se 1 (by rfl) ⟨849761, by rfl⟩ : syracuseStep 1133015 = 1699523) B1699523
theorem B1133081 : Blo 754331 1133081 := bstep (se 2 (by rfl) ⟨424905, by rfl⟩ : syracuseStep 1133081 = 849811) B849811
theorem B1133195 : Blo 754331 1133195 := bstep (se 1 (by rfl) ⟨849896, by rfl⟩ : syracuseStep 1133195 = 1699793) B1699793
theorem B1133207 : Blo 754331 1133207 := bstep (se 1 (by rfl) ⟨849905, by rfl⟩ : syracuseStep 1133207 = 1699811) B1699811
theorem B1362625 : Blo 754331 1362625 := bstep (se 2 (by rfl) ⟨510984, by rfl⟩ : syracuseStep 1362625 = 1021969) B1021969
theorem B1133273 : Blo 754331 1133273 := bstep (se 2 (by rfl) ⟨424977, by rfl⟩ : syracuseStep 1133273 = 849955) B849955
theorem B5163841 : Blo 754331 5163841 := bstep (se 2 (by rfl) ⟨1936440, by rfl⟩ : syracuseStep 5163841 = 3872881) B3872881
theorem B1133387 : Blo 754331 1133387 := bstep (se 1 (by rfl) ⟨850040, by rfl⟩ : syracuseStep 1133387 = 1700081) B1700081
theorem B1133399 : Blo 754331 1133399 := bstep (se 1 (by rfl) ⟨850049, by rfl⟩ : syracuseStep 1133399 = 1700099) B1700099
theorem B1133465 : Blo 754331 1133465 := bstep (se 2 (by rfl) ⟨425049, by rfl⟩ : syracuseStep 1133465 = 850099) B850099
theorem B1133579 : Blo 754331 1133579 := bstep (se 1 (by rfl) ⟨850184, by rfl⟩ : syracuseStep 1133579 = 1700369) B1700369
theorem B1133591 : Blo 754331 1133591 := bstep (se 1 (by rfl) ⟨850193, by rfl⟩ : syracuseStep 1133591 = 1700387) B1700387
theorem B1133657 : Blo 754331 1133657 := bstep (se 2 (by rfl) ⟨425121, by rfl⟩ : syracuseStep 1133657 = 850243) B850243
theorem B2870423 : Blo 754331 2870423 := bstep (se 1 (by rfl) ⟨2152817, by rfl⟩ : syracuseStep 2870423 = 4305635) B4305635
theorem B1133771 : Blo 754331 1133771 := bstep (se 1 (by rfl) ⟨850328, by rfl⟩ : syracuseStep 1133771 = 1700657) B1700657
theorem B1133783 : Blo 754331 1133783 := bstep (se 1 (by rfl) ⟨850337, by rfl⟩ : syracuseStep 1133783 = 1700675) B1700675
theorem B1363159 : Blo 754331 1363159 := bstep (se 1 (by rfl) ⟨1022369, by rfl⟩ : syracuseStep 1363159 = 2044739) B2044739
theorem B1133849 : Blo 754331 1133849 := bstep (se 2 (by rfl) ⟨425193, by rfl⟩ : syracuseStep 1133849 = 850387) B850387
theorem B1723763 : Blo 754331 1723763 := bstep (se 1 (by rfl) ⟨1292822, by rfl⟩ : syracuseStep 1723763 = 2585645) B2585645
theorem B3820931 : Blo 754331 3820931 := bstep (se 1 (by rfl) ⟨2865698, by rfl⟩ : syracuseStep 3820931 = 5731397) B5731397
theorem B1133963 : Blo 754331 1133963 := bstep (se 1 (by rfl) ⟨850472, by rfl⟩ : syracuseStep 1133963 = 1700945) B1700945
theorem B1133975 : Blo 754331 1133975 := bstep (se 1 (by rfl) ⟨850481, by rfl⟩ : syracuseStep 1133975 = 1700963) B1700963
theorem B2149811 : Blo 754331 2149811 := bstep (se 1 (by rfl) ⟨1612358, by rfl⟩ : syracuseStep 2149811 = 3224717) B3224717
theorem B1134041 : Blo 754331 1134041 := bstep (se 2 (by rfl) ⟨425265, by rfl⟩ : syracuseStep 1134041 = 850531) B850531
theorem B1134155 : Blo 754331 1134155 := bstep (se 1 (by rfl) ⟨850616, by rfl⟩ : syracuseStep 1134155 = 1701233) B1701233
theorem B1134167 : Blo 754331 1134167 := bstep (se 1 (by rfl) ⟨850625, by rfl⟩ : syracuseStep 1134167 = 1701251) B1701251
theorem B1134233 : Blo 754331 1134233 := bstep (se 2 (by rfl) ⟨425337, by rfl⟩ : syracuseStep 1134233 = 850675) B850675
theorem B1134347 : Blo 754331 1134347 := bstep (se 1 (by rfl) ⟨850760, by rfl⟩ : syracuseStep 1134347 = 1701521) B1701521
theorem B1134359 : Blo 754331 1134359 := bstep (se 1 (by rfl) ⟨850769, by rfl⟩ : syracuseStep 1134359 = 1701539) B1701539
theorem B3067723 : Blo 754331 3067723 := bstep (se 1 (by rfl) ⟨2300792, by rfl⟩ : syracuseStep 3067723 = 4601585) B4601585
theorem B1134425 : Blo 754331 1134425 := bstep (se 2 (by rfl) ⟨425409, by rfl⟩ : syracuseStep 1134425 = 850819) B850819
theorem B4312925 : Blo 754331 4312925 := bstep (se 3 (by rfl) ⟨808673, by rfl⟩ : syracuseStep 4312925 = 1617347) B1617347
theorem B5754725 : Blo 754331 5754725 := bstep (se 4 (by rfl) ⟨539505, by rfl⟩ : syracuseStep 5754725 = 1079011) B1079011
theorem B806807 : Blo 754331 806807 := bstep (se 1 (by rfl) ⟨605105, by rfl⟩ : syracuseStep 806807 = 1210211) B1210211
theorem B1134539 : Blo 754331 1134539 := bstep (se 1 (by rfl) ⟨850904, by rfl⟩ : syracuseStep 1134539 = 1701809) B1701809
theorem B1134551 : Blo 754331 1134551 := bstep (se 1 (by rfl) ⟨850913, by rfl⟩ : syracuseStep 1134551 = 1701827) B1701827
theorem B1134617 : Blo 754331 1134617 := bstep (se 2 (by rfl) ⟨425481, by rfl⟩ : syracuseStep 1134617 = 850963) B850963
theorem B1134731 : Blo 754331 1134731 := bstep (se 1 (by rfl) ⟨851048, by rfl⟩ : syracuseStep 1134731 = 1702097) B1702097
theorem B1134743 : Blo 754331 1134743 := bstep (se 1 (by rfl) ⟨851057, by rfl⟩ : syracuseStep 1134743 = 1702115) B1702115
theorem B1134809 : Blo 754331 1134809 := bstep (se 2 (by rfl) ⟨425553, by rfl⟩ : syracuseStep 1134809 = 851107) B851107
theorem B1134923 : Blo 754331 1134923 := bstep (se 1 (by rfl) ⟨851192, by rfl⟩ : syracuseStep 1134923 = 1702385) B1702385
theorem B5755211 : Blo 754331 5755211 := bstep (se 1 (by rfl) ⟨4316408, by rfl⟩ : syracuseStep 5755211 = 8632817) B8632817
theorem B1134935 : Blo 754331 1134935 := bstep (se 1 (by rfl) ⟨851201, by rfl⟩ : syracuseStep 1134935 = 1702403) B1702403
theorem B4084069 : Blo 754331 4084069 := bstep (se 4 (by rfl) ⟨382881, by rfl⟩ : syracuseStep 4084069 = 765763) B765763
theorem B2871683 : Blo 754331 2871683 := bstep (se 1 (by rfl) ⟨2153762, by rfl⟩ : syracuseStep 2871683 = 4307525) B4307525
theorem B1135001 : Blo 754331 1135001 := bstep (se 2 (by rfl) ⟨425625, by rfl⟩ : syracuseStep 1135001 = 851251) B851251
theorem B1135115 : Blo 754331 1135115 := bstep (se 1 (by rfl) ⟨851336, by rfl⟩ : syracuseStep 1135115 = 1702673) B1702673
theorem B1135127 : Blo 754331 1135127 := bstep (se 1 (by rfl) ⟨851345, by rfl⟩ : syracuseStep 1135127 = 1702691) B1702691
theorem B807499 : Blo 754331 807499 := bstep (se 1 (by rfl) ⟨605624, by rfl⟩ : syracuseStep 807499 = 1211249) B1211249
theorem B4313675 : Blo 754331 4313675 := bstep (se 1 (by rfl) ⟨3235256, by rfl⟩ : syracuseStep 4313675 = 6470513) B6470513
theorem B1135193 : Blo 754331 1135193 := bstep (se 2 (by rfl) ⟨425697, by rfl⟩ : syracuseStep 1135193 = 851395) B851395
theorem B2183773 : Blo 754331 2183773 := bstep (se 3 (by rfl) ⟨409457, by rfl⟩ : syracuseStep 2183773 = 818915) B818915
theorem B1135307 : Blo 754331 1135307 := bstep (se 1 (by rfl) ⟨851480, by rfl⟩ : syracuseStep 1135307 = 1702961) B1702961
theorem B1135319 : Blo 754331 1135319 := bstep (se 1 (by rfl) ⟨851489, by rfl⟩ : syracuseStep 1135319 = 1702979) B1702979
theorem B1135385 : Blo 754331 1135385 := bstep (se 2 (by rfl) ⟨425769, by rfl⟩ : syracuseStep 1135385 = 851539) B851539
theorem B6148939 : Blo 754331 6148939 := bstep (se 1 (by rfl) ⟨4611704, by rfl⟩ : syracuseStep 6148939 = 9223409) B9223409
theorem B3068761 : Blo 754331 3068761 := bstep (se 2 (by rfl) ⟨1150785, by rfl⟩ : syracuseStep 3068761 = 2301571) B2301571
theorem B1135499 : Blo 754331 1135499 := bstep (se 1 (by rfl) ⟨851624, by rfl⟩ : syracuseStep 1135499 = 1703249) B1703249
theorem B1135511 : Blo 754331 1135511 := bstep (se 1 (by rfl) ⟨851633, by rfl⟩ : syracuseStep 1135511 = 1703267) B1703267
theorem B1135577 : Blo 754331 1135577 := bstep (se 2 (by rfl) ⟨425841, by rfl⟩ : syracuseStep 1135577 = 851683) B851683
theorem B1135691 : Blo 754331 1135691 := bstep (se 1 (by rfl) ⟨851768, by rfl⟩ : syracuseStep 1135691 = 1703537) B1703537
theorem B1135703 : Blo 754331 1135703 := bstep (se 1 (by rfl) ⟨851777, by rfl⟩ : syracuseStep 1135703 = 1703555) B1703555
theorem B1135769 : Blo 754331 1135769 := bstep (se 2 (by rfl) ⟨425913, by rfl⟩ : syracuseStep 1135769 = 851827) B851827
theorem B1135883 : Blo 754331 1135883 := bstep (se 1 (by rfl) ⟨851912, by rfl⟩ : syracuseStep 1135883 = 1703825) B1703825
theorem B1135895 : Blo 754331 1135895 := bstep (se 1 (by rfl) ⟨851921, by rfl⟩ : syracuseStep 1135895 = 1703843) B1703843
theorem B1135961 : Blo 754331 1135961 := bstep (se 2 (by rfl) ⟨425985, by rfl⟩ : syracuseStep 1135961 = 851971) B851971
theorem B2905475 : Blo 754331 2905475 := bstep (se 1 (by rfl) ⟨2179106, by rfl⟩ : syracuseStep 2905475 = 4358213) B4358213
theorem B2905537 : Blo 754331 2905537 := bstep (se 2 (by rfl) ⟨1089576, by rfl⟩ : syracuseStep 2905537 = 2179153) B2179153
theorem B1136075 : Blo 754331 1136075 := bstep (se 1 (by rfl) ⟨852056, by rfl⟩ : syracuseStep 1136075 = 1704113) B1704113
theorem B1136087 : Blo 754331 1136087 := bstep (se 1 (by rfl) ⟨852065, by rfl⟩ : syracuseStep 1136087 = 1704131) B1704131
theorem B1136153 : Blo 754331 1136153 := bstep (se 2 (by rfl) ⟨426057, by rfl⟩ : syracuseStep 1136153 = 852115) B852115
theorem B6477347 : Blo 754331 6477347 := bstep (se 1 (by rfl) ⟨4858010, by rfl⟩ : syracuseStep 6477347 = 9716021) B9716021
theorem B2184779 : Blo 754331 2184779 := bstep (se 1 (by rfl) ⟨1638584, by rfl⟩ : syracuseStep 2184779 = 3277169) B3277169
theorem B1136267 : Blo 754331 1136267 := bstep (se 1 (by rfl) ⟨852200, by rfl⟩ : syracuseStep 1136267 = 1704401) B1704401
theorem B1136279 : Blo 754331 1136279 := bstep (se 1 (by rfl) ⟨852209, by rfl⟩ : syracuseStep 1136279 = 1704419) B1704419
theorem B1136345 : Blo 754331 1136345 := bstep (se 2 (by rfl) ⟨426129, by rfl⟩ : syracuseStep 1136345 = 852259) B852259
theorem B1136459 : Blo 754331 1136459 := bstep (se 1 (by rfl) ⟨852344, by rfl⟩ : syracuseStep 1136459 = 1704689) B1704689
theorem B1136471 : Blo 754331 1136471 := bstep (se 1 (by rfl) ⟨852353, by rfl⟩ : syracuseStep 1136471 = 1704707) B1704707
theorem B808823 : Blo 754331 808823 := bstep (se 1 (by rfl) ⟨606617, by rfl⟩ : syracuseStep 808823 = 1213235) B1213235
theorem B1136537 : Blo 754331 1136537 := bstep (se 2 (by rfl) ⟨426201, by rfl⟩ : syracuseStep 1136537 = 852403) B852403
theorem B1365913 : Blo 754331 1365913 := bstep (se 2 (by rfl) ⟨512217, by rfl⟩ : syracuseStep 1365913 = 1024435) B1024435
theorem B10901465 : Blo 754331 10901465 := bstep (se 2 (by rfl) ⟨4088049, by rfl⟩ : syracuseStep 10901465 = 8176099) B8176099
theorem B3233753 : Blo 754331 3233753 := bstep (se 2 (by rfl) ⟨1212657, by rfl⟩ : syracuseStep 3233753 = 2425315) B2425315
theorem B808951 : Blo 754331 808951 := bstep (se 1 (by rfl) ⟨606713, by rfl⟩ : syracuseStep 808951 = 1213427) B1213427
theorem B1136651 : Blo 754331 1136651 := bstep (se 1 (by rfl) ⟨852488, by rfl⟩ : syracuseStep 1136651 = 1704977) B1704977
theorem B1136663 : Blo 754331 1136663 := bstep (se 1 (by rfl) ⟨852497, by rfl⟩ : syracuseStep 1136663 = 1704995) B1704995
theorem B1136729 : Blo 754331 1136729 := bstep (se 2 (by rfl) ⟨426273, by rfl⟩ : syracuseStep 1136729 = 852547) B852547
theorem B4315315 : Blo 754331 4315315 := bstep (se 1 (by rfl) ⟨3236486, by rfl⟩ : syracuseStep 4315315 = 6472973) B6472973
theorem B1136843 : Blo 754331 1136843 := bstep (se 1 (by rfl) ⟨852632, by rfl⟩ : syracuseStep 1136843 = 1705265) B1705265
theorem B1136855 : Blo 754331 1136855 := bstep (se 1 (by rfl) ⟨852641, by rfl⟩ : syracuseStep 1136855 = 1705283) B1705283
theorem B2152669 : Blo 754331 2152669 := bstep (se 3 (by rfl) ⟨403625, by rfl⟩ : syracuseStep 2152669 = 807251) B807251
theorem B2152727 : Blo 754331 2152727 := bstep (se 1 (by rfl) ⟨1614545, by rfl⟩ : syracuseStep 2152727 = 3229091) B3229091
theorem B1136921 : Blo 754331 1136921 := bstep (se 2 (by rfl) ⟨426345, by rfl⟩ : syracuseStep 1136921 = 852691) B852691
theorem B1137035 : Blo 754331 1137035 := bstep (se 1 (by rfl) ⟨852776, by rfl⟩ : syracuseStep 1137035 = 1705553) B1705553
theorem B874903 : Blo 754331 874903 := bstep (se 1 (by rfl) ⟨656177, by rfl⟩ : syracuseStep 874903 = 1312355) B1312355
theorem B1137047 : Blo 754331 1137047 := bstep (se 1 (by rfl) ⟨852785, by rfl⟩ : syracuseStep 1137047 = 1705571) B1705571
theorem B2546099 : Blo 754331 2546099 := bstep (se 1 (by rfl) ⟨1909574, by rfl⟩ : syracuseStep 2546099 = 3819149) B3819149
theorem B1137113 : Blo 754331 1137113 := bstep (se 2 (by rfl) ⟨426417, by rfl⟩ : syracuseStep 1137113 = 852835) B852835
theorem B1432075 : Blo 754331 1432075 := bstep (se 1 (by rfl) ⟨1074056, by rfl⟩ : syracuseStep 1432075 = 2148113) B2148113
theorem B809515 : Blo 754331 809515 := bstep (se 1 (by rfl) ⟨607136, by rfl⟩ : syracuseStep 809515 = 1214273) B1214273
theorem B1137227 : Blo 754331 1137227 := bstep (se 1 (by rfl) ⟨852920, by rfl⟩ : syracuseStep 1137227 = 1705841) B1705841
theorem B1432151 : Blo 754331 1432151 := bstep (se 1 (by rfl) ⟨1074113, by rfl⟩ : syracuseStep 1432151 = 2148227) B2148227
theorem B1137239 : Blo 754331 1137239 := bstep (se 1 (by rfl) ⟨852929, by rfl⟩ : syracuseStep 1137239 = 1705859) B1705859
theorem B1137305 : Blo 754331 1137305 := bstep (se 2 (by rfl) ⟨426489, by rfl⟩ : syracuseStep 1137305 = 852979) B852979
theorem B2546369 : Blo 754331 2546369 := bstep (se 2 (by rfl) ⟨954888, by rfl⟩ : syracuseStep 2546369 = 1909777) B1909777
theorem B1137419 : Blo 754331 1137419 := bstep (se 1 (by rfl) ⟨853064, by rfl⟩ : syracuseStep 1137419 = 1706129) B1706129
theorem B1137431 : Blo 754331 1137431 := bstep (se 1 (by rfl) ⟨853073, by rfl⟩ : syracuseStep 1137431 = 1706147) B1706147
theorem B809771 : Blo 754331 809771 := bstep (se 1 (by rfl) ⟨607328, by rfl⟩ : syracuseStep 809771 = 1214657) B1214657
theorem B1137497 : Blo 754331 1137497 := bstep (se 2 (by rfl) ⟨426561, by rfl⟩ : syracuseStep 1137497 = 853123) B853123
theorem B1727411 : Blo 754331 1727411 := bstep (se 1 (by rfl) ⟨1295558, by rfl⟩ : syracuseStep 1727411 = 2591117) B2591117
theorem B3824657 : Blo 754331 3824657 := bstep (se 2 (by rfl) ⟨1434246, by rfl⟩ : syracuseStep 3824657 = 2868493) B2868493
theorem B3824819 : Blo 754331 3824819 := bstep (se 1 (by rfl) ⟨2868614, by rfl⟩ : syracuseStep 3824819 = 5737229) B5737229
theorem B2546909 : Blo 754331 2546909 := bstep (se 3 (by rfl) ⟨477545, by rfl⟩ : syracuseStep 2546909 = 955091) B955091
theorem B1432819 : Blo 754331 1432819 := bstep (se 1 (by rfl) ⟨1074614, by rfl⟩ : syracuseStep 1432819 = 2149229) B2149229
theorem B3628439 : Blo 754331 3628439 := bstep (se 1 (by rfl) ⟨2721329, by rfl⟩ : syracuseStep 3628439 = 5442659) B5442659
theorem B2874797 : Blo 754331 2874797 := bstep (se 3 (by rfl) ⟨539024, by rfl⟩ : syracuseStep 2874797 = 1078049) B1078049
theorem B1433047 : Blo 754331 1433047 := bstep (se 1 (by rfl) ⟨1074785, by rfl⟩ : syracuseStep 1433047 = 2149571) B2149571
theorem B1498583 : Blo 754331 1498583 := bstep (se 1 (by rfl) ⟨1123937, by rfl⟩ : syracuseStep 1498583 = 2247875) B2247875
theorem B2153945 : Blo 754331 2153945 := bstep (se 2 (by rfl) ⟨807729, by rfl⟩ : syracuseStep 2153945 = 1615459) B1615459
theorem B1433153 : Blo 754331 1433153 := bstep (se 2 (by rfl) ⟨537432, by rfl⟩ : syracuseStep 1433153 = 1074865) B1074865
theorem B3235393 : Blo 754331 3235393 := bstep (se 2 (by rfl) ⟨1213272, by rfl⟩ : syracuseStep 3235393 = 2426545) B2426545
theorem B2154059 : Blo 754331 2154059 := bstep (se 1 (by rfl) ⟨1615544, by rfl⟩ : syracuseStep 2154059 = 3231089) B3231089
theorem B4316773 : Blo 754331 4316773 := bstep (se 4 (by rfl) ⟨404697, by rfl⟩ : syracuseStep 4316773 = 809395) B809395
theorem B1433305 : Blo 754331 1433305 := bstep (se 2 (by rfl) ⟨537489, by rfl⟩ : syracuseStep 1433305 = 1074979) B1074979
theorem B2416601 : Blo 754331 2416601 := bstep (se 2 (by rfl) ⟨906225, by rfl⟩ : syracuseStep 2416601 = 1812451) B1812451
theorem B1728587 : Blo 754331 1728587 := bstep (se 1 (by rfl) ⟨1296440, by rfl⟩ : syracuseStep 1728587 = 2592881) B2592881
theorem B778411 : Blo 754331 778411 := bstep (se 1 (by rfl) ⟨583808, by rfl⟩ : syracuseStep 778411 = 1167617) B1167617
theorem B2875571 : Blo 754331 2875571 := bstep (se 1 (by rfl) ⟨2156678, by rfl⟩ : syracuseStep 2875571 = 4313357) B4313357
theorem B13066541 : Blo 754331 13066541 := bstep (se 3 (by rfl) ⟨2449976, by rfl⟩ : syracuseStep 13066541 = 4899953) B4899953
theorem B2548043 : Blo 754331 2548043 := bstep (se 1 (by rfl) ⟨1911032, by rfl⟩ : syracuseStep 2548043 = 3822065) B3822065
theorem B2548313 : Blo 754331 2548313 := bstep (se 2 (by rfl) ⟨955617, by rfl⟩ : syracuseStep 2548313 = 1911235) B1911235
theorem B2155187 : Blo 754331 2155187 := bstep (se 1 (by rfl) ⟨1616390, by rfl⟩ : syracuseStep 2155187 = 3232781) B3232781
theorem B1532695 : Blo 754331 1532695 := bstep (se 1 (by rfl) ⟨1149521, by rfl⟩ : syracuseStep 1532695 = 2299043) B2299043
theorem B1434611 : Blo 754331 1434611 := bstep (se 1 (by rfl) ⟨1075958, by rfl⟩ : syracuseStep 1434611 = 2151917) B2151917
theorem B3236881 : Blo 754331 3236881 := bstep (se 2 (by rfl) ⟨1213830, by rfl⟩ : syracuseStep 3236881 = 2427661) B2427661
theorem B2155585 : Blo 754331 2155585 := bstep (se 2 (by rfl) ⟨808344, by rfl⟩ : syracuseStep 2155585 = 1616689) B1616689
theorem B3826763 : Blo 754331 3826763 := bstep (se 1 (by rfl) ⟨2870072, by rfl⟩ : syracuseStep 3826763 = 5740145) B5740145
theorem B8610947 : Blo 754331 8610947 := bstep (se 1 (by rfl) ⟨6458210, by rfl⟩ : syracuseStep 8610947 = 12916421) B12916421
theorem B1434763 : Blo 754331 1434763 := bstep (se 1 (by rfl) ⟨1076072, by rfl⟩ : syracuseStep 1434763 = 2152145) B2152145
theorem B3073241 : Blo 754331 3073241 := bstep (se 2 (by rfl) ⟨1152465, by rfl⟩ : syracuseStep 3073241 = 2304931) B2304931
theorem B2549015 : Blo 754331 2549015 := bstep (se 1 (by rfl) ⟨1911761, by rfl⟩ : syracuseStep 2549015 = 3823523) B3823523
theorem B5465495 : Blo 754331 5465495 := bstep (se 1 (by rfl) ⟨4099121, by rfl⟩ : syracuseStep 5465495 = 8198243) B8198243
theorem B1074649 : Blo 754331 1074649 := bstep (se 2 (by rfl) ⟨402993, by rfl⟩ : syracuseStep 1074649 = 805987) B805987
theorem B1435097 : Blo 754331 1435097 := bstep (se 2 (by rfl) ⟨538161, by rfl⟩ : syracuseStep 1435097 = 1076323) B1076323
theorem B1533401 : Blo 754331 1533401 := bstep (se 2 (by rfl) ⟨575025, by rfl⟩ : syracuseStep 1533401 = 1150051) B1150051
theorem B1697291 : Blo 754331 1697291 := bstep (se 1 (by rfl) ⟨1272968, by rfl⟩ : syracuseStep 1697291 = 2545937) B2545937
theorem B1697345 : Blo 754331 1697345 := bstep (se 2 (by rfl) ⟨636504, by rfl⟩ : syracuseStep 1697345 = 1273009) B1273009
theorem B2877059 : Blo 754331 2877059 := bstep (se 1 (by rfl) ⟨2157794, by rfl⟩ : syracuseStep 2877059 = 4315589) B4315589
theorem B1697561 : Blo 754331 1697561 := bstep (se 2 (by rfl) ⟨636585, by rfl⟩ : syracuseStep 1697561 = 1273171) B1273171
theorem B2549555 : Blo 754331 2549555 := bstep (se 1 (by rfl) ⟨1912166, by rfl⟩ : syracuseStep 2549555 = 3824333) B3824333
theorem B1697651 : Blo 754331 1697651 := bstep (se 1 (by rfl) ⟨1273238, by rfl⟩ : syracuseStep 1697651 = 2546477) B2546477
theorem B1697687 : Blo 754331 1697687 := bstep (se 1 (by rfl) ⟨1273265, by rfl⟩ : syracuseStep 1697687 = 2546531) B2546531
theorem B8185873 : Blo 754331 8185873 := bstep (se 2 (by rfl) ⟨3069702, by rfl⟩ : syracuseStep 8185873 = 6139405) B6139405
theorem B6285347 : Blo 754331 6285347 := bstep (se 1 (by rfl) ⟨4714010, by rfl⟩ : syracuseStep 6285347 = 9428021) B9428021
theorem B2549825 : Blo 754331 2549825 := bstep (se 2 (by rfl) ⟨956184, by rfl⟩ : syracuseStep 2549825 = 1912369) B1912369
theorem B1697867 : Blo 754331 1697867 := bstep (se 1 (by rfl) ⟨1273400, by rfl⟩ : syracuseStep 1697867 = 2546801) B2546801
theorem B2877515 : Blo 754331 2877515 := bstep (se 1 (by rfl) ⟨2158136, by rfl⟩ : syracuseStep 2877515 = 4316273) B4316273
theorem B1435735 : Blo 754331 1435735 := bstep (se 1 (by rfl) ⟨1076801, by rfl⟩ : syracuseStep 1435735 = 2153603) B2153603
theorem B2418781 : Blo 754331 2418781 := bstep (se 3 (by rfl) ⟨453521, by rfl⟩ : syracuseStep 2418781 = 907043) B907043
theorem B1697921 : Blo 754331 1697921 := bstep (se 2 (by rfl) ⟨636720, by rfl⟩ : syracuseStep 1697921 = 1273441) B1273441
theorem B29419661 : Blo 754331 29419661 := bstep (se 3 (by rfl) ⟨5516186, by rfl⟩ : syracuseStep 29419661 = 11032373) B11032373
theorem B3500183 : Blo 754331 3500183 := bstep (se 1 (by rfl) ⟨2625137, by rfl⟩ : syracuseStep 3500183 = 5250275) B5250275
theorem B2877713 : Blo 754331 2877713 := bstep (se 2 (by rfl) ⟨1079142, by rfl⟩ : syracuseStep 2877713 = 2158285) B2158285
theorem B6121763 : Blo 754331 6121763 := bstep (se 1 (by rfl) ⟨4591322, by rfl⟩ : syracuseStep 6121763 = 9182645) B9182645
theorem B11659585 : Blo 754331 11659585 := bstep (se 2 (by rfl) ⟨4372344, by rfl⟩ : syracuseStep 11659585 = 8744689) B8744689
theorem B1698137 : Blo 754331 1698137 := bstep (se 2 (by rfl) ⟨636801, by rfl⟩ : syracuseStep 1698137 = 1273603) B1273603
theorem B1698227 : Blo 754331 1698227 := bstep (se 1 (by rfl) ⟨1273670, by rfl⟩ : syracuseStep 1698227 = 2547341) B2547341
theorem B1698263 : Blo 754331 1698263 := bstep (se 1 (by rfl) ⟨1273697, by rfl⟩ : syracuseStep 1698263 = 2547395) B2547395
theorem B1075799 : Blo 754331 1075799 := bstep (se 1 (by rfl) ⟨806849, by rfl⟩ : syracuseStep 1075799 = 1613699) B1613699
theorem B2550365 : Blo 754331 2550365 := bstep (se 3 (by rfl) ⟨478193, by rfl⟩ : syracuseStep 2550365 = 956387) B956387
theorem B1698443 : Blo 754331 1698443 := bstep (se 1 (by rfl) ⟨1273832, by rfl⟩ : syracuseStep 1698443 = 2547665) B2547665
theorem B1698497 : Blo 754331 1698497 := bstep (se 2 (by rfl) ⟨636936, by rfl⟩ : syracuseStep 1698497 = 1273873) B1273873
theorem B3828545 : Blo 754331 3828545 := bstep (se 2 (by rfl) ⟨1435704, by rfl⟩ : syracuseStep 3828545 = 2871409) B2871409
theorem B1436555 : Blo 754331 1436555 := bstep (se 1 (by rfl) ⟨1077416, by rfl⟩ : syracuseStep 1436555 = 2154833) B2154833
theorem B1076107 : Blo 754331 1076107 := bstep (se 1 (by rfl) ⟨807080, by rfl⟩ : syracuseStep 1076107 = 1614161) B1614161
theorem B1698713 : Blo 754331 1698713 := bstep (se 2 (by rfl) ⟨637017, by rfl⟩ : syracuseStep 1698713 = 1274035) B1274035
theorem B1436609 : Blo 754331 1436609 := bstep (se 2 (by rfl) ⟨538728, by rfl⟩ : syracuseStep 1436609 = 1077457) B1077457
theorem B1698803 : Blo 754331 1698803 := bstep (se 1 (by rfl) ⟨1274102, by rfl⟩ : syracuseStep 1698803 = 2548205) B2548205
theorem B1698839 : Blo 754331 1698839 := bstep (se 1 (by rfl) ⟨1274129, by rfl⟩ : syracuseStep 1698839 = 2548259) B2548259
theorem B2878487 : Blo 754331 2878487 := bstep (se 1 (by rfl) ⟨2158865, by rfl⟩ : syracuseStep 2878487 = 4317731) B4317731
theorem B4418711 : Blo 754331 4418711 := bstep (se 1 (by rfl) ⟨3314033, by rfl⟩ : syracuseStep 4418711 = 6628067) B6628067
theorem B6450353 : Blo 754331 6450353 := bstep (se 2 (by rfl) ⟨2418882, by rfl⟩ : syracuseStep 6450353 = 4837765) B4837765
theorem B1633459 : Blo 754331 1633459 := bstep (se 1 (by rfl) ⟨1225094, by rfl⟩ : syracuseStep 1633459 = 2450189) B2450189
theorem B1699019 : Blo 754331 1699019 := bstep (se 1 (by rfl) ⟨1274264, by rfl⟩ : syracuseStep 1699019 = 2548529) B2548529
theorem B2878685 : Blo 754331 2878685 := bstep (se 3 (by rfl) ⟨539753, by rfl⟩ : syracuseStep 2878685 = 1079507) B1079507
theorem B1699073 : Blo 754331 1699073 := bstep (se 2 (by rfl) ⟨637152, by rfl⟩ : syracuseStep 1699073 = 1274305) B1274305
theorem B1535257 : Blo 754331 1535257 := bstep (se 2 (by rfl) ⟨575721, by rfl⟩ : syracuseStep 1535257 = 1151443) B1151443
theorem B1699289 : Blo 754331 1699289 := bstep (se 2 (by rfl) ⟨637233, by rfl⟩ : syracuseStep 1699289 = 1274467) B1274467
theorem B1273367 : Blo 754331 1273367 := bstep (se 1 (by rfl) ⟨955025, by rfl⟩ : syracuseStep 1273367 = 1910051) B1910051
theorem B2158103 : Blo 754331 2158103 := bstep (se 1 (by rfl) ⟨1618577, by rfl⟩ : syracuseStep 2158103 = 3237155) B3237155
theorem B1699379 : Blo 754331 1699379 := bstep (se 1 (by rfl) ⟨1274534, by rfl⟩ : syracuseStep 1699379 = 2549069) B2549069
theorem B1699415 : Blo 754331 1699415 := bstep (se 1 (by rfl) ⟨1274561, by rfl⟩ : syracuseStep 1699415 = 2549123) B2549123
theorem B1273495 : Blo 754331 1273495 := bstep (se 1 (by rfl) ⟨955121, by rfl⟩ : syracuseStep 1273495 = 1910243) B1910243
theorem B2551499 : Blo 754331 2551499 := bstep (se 1 (by rfl) ⟨1913624, by rfl⟩ : syracuseStep 2551499 = 3827249) B3827249
theorem B1699595 : Blo 754331 1699595 := bstep (se 1 (by rfl) ⟨1274696, by rfl⟩ : syracuseStep 1699595 = 2549393) B2549393
theorem B1699649 : Blo 754331 1699649 := bstep (se 2 (by rfl) ⟨637368, by rfl⟩ : syracuseStep 1699649 = 1274737) B1274737
theorem B1437527 : Blo 754331 1437527 := bstep (se 1 (by rfl) ⟨1078145, by rfl⟩ : syracuseStep 1437527 = 2156291) B2156291
theorem B1077143 : Blo 754331 1077143 := bstep (se 1 (by rfl) ⟨807857, by rfl⟩ : syracuseStep 1077143 = 1615715) B1615715
theorem B2551769 : Blo 754331 2551769 := bstep (se 2 (by rfl) ⟨956913, by rfl⟩ : syracuseStep 2551769 = 1913827) B1913827
theorem B1699865 : Blo 754331 1699865 := bstep (se 2 (by rfl) ⟨637449, by rfl⟩ : syracuseStep 1699865 = 1274899) B1274899
theorem B1077337 : Blo 754331 1077337 := bstep (se 2 (by rfl) ⟨404001, by rfl⟩ : syracuseStep 1077337 = 808003) B808003
theorem B13791325 : Blo 754331 13791325 := bstep (se 3 (by rfl) ⟨2585873, by rfl⟩ : syracuseStep 13791325 = 5171747) B5171747
theorem B3633245 : Blo 754331 3633245 := bstep (se 3 (by rfl) ⟨681233, by rfl⟩ : syracuseStep 3633245 = 1362467) B1362467
theorem B1699955 : Blo 754331 1699955 := bstep (se 1 (by rfl) ⟨1274966, by rfl⟩ : syracuseStep 1699955 = 2549933) B2549933
theorem B1699991 : Blo 754331 1699991 := bstep (se 1 (by rfl) ⟨1274993, by rfl⟩ : syracuseStep 1699991 = 2549987) B2549987
theorem B6549655 : Blo 754331 6549655 := bstep (se 1 (by rfl) ⟨4912241, by rfl⟩ : syracuseStep 6549655 = 9824483) B9824483
theorem B2912435 : Blo 754331 2912435 := bstep (se 1 (by rfl) ⟨2184326, by rfl⟩ : syracuseStep 2912435 = 4368653) B4368653
theorem B1274123 : Blo 754331 1274123 := bstep (se 1 (by rfl) ⟨955592, by rfl⟩ : syracuseStep 1274123 = 1911185) B1911185
theorem B1700171 : Blo 754331 1700171 := bstep (se 1 (by rfl) ⟨1275128, by rfl⟩ : syracuseStep 1700171 = 2550257) B2550257
theorem B1438067 : Blo 754331 1438067 := bstep (se 1 (by rfl) ⟨1078550, by rfl⟩ : syracuseStep 1438067 = 2157101) B2157101
theorem B1700225 : Blo 754331 1700225 := bstep (se 2 (by rfl) ⟨637584, by rfl⟩ : syracuseStep 1700225 = 1275169) B1275169
theorem B1274251 : Blo 754331 1274251 := bstep (se 1 (by rfl) ⟨955688, by rfl⟩ : syracuseStep 1274251 = 1911377) B1911377
theorem B1274393 : Blo 754331 1274393 := bstep (se 2 (by rfl) ⟨477897, by rfl⟩ : syracuseStep 1274393 = 955795) B955795
theorem B1700441 : Blo 754331 1700441 := bstep (se 2 (by rfl) ⟨637665, by rfl⟩ : syracuseStep 1700441 = 1275331) B1275331
theorem B2552471 : Blo 754331 2552471 := bstep (se 1 (by rfl) ⟨1914353, by rfl⟩ : syracuseStep 2552471 = 3828707) B3828707
theorem B1274521 : Blo 754331 1274521 := bstep (se 2 (by rfl) ⟨477945, by rfl⟩ : syracuseStep 1274521 = 955891) B955891
theorem B1700531 : Blo 754331 1700531 := bstep (se 1 (by rfl) ⟨1275398, by rfl⟩ : syracuseStep 1700531 = 2550797) B2550797
theorem B1700567 : Blo 754331 1700567 := bstep (se 1 (by rfl) ⟨1275425, by rfl⟩ : syracuseStep 1700567 = 2550851) B2550851
theorem B3830489 : Blo 754331 3830489 := bstep (se 2 (by rfl) ⟨1436433, by rfl⟩ : syracuseStep 3830489 = 2872867) B2872867
theorem B848695 : Blo 754331 848695 := bstep (se 1 (by rfl) ⟨636521, by rfl⟩ : syracuseStep 848695 = 1273043) B1273043
theorem B2159435 : Blo 754331 2159435 := bstep (se 1 (by rfl) ⟨1619576, by rfl⟩ : syracuseStep 2159435 = 3239153) B3239153
theorem B1438553 : Blo 754331 1438553 := bstep (se 2 (by rfl) ⟨539457, by rfl⟩ : syracuseStep 1438553 = 1078915) B1078915
theorem B1700747 : Blo 754331 1700747 := bstep (se 1 (by rfl) ⟨1275560, by rfl⟩ : syracuseStep 1700747 = 2551121) B2551121
theorem B2913175 : Blo 754331 2913175 := bstep (se 1 (by rfl) ⟨2184881, by rfl⟩ : syracuseStep 2913175 = 4369763) B4369763
theorem B1700801 : Blo 754331 1700801 := bstep (se 2 (by rfl) ⟨637800, by rfl⟩ : syracuseStep 1700801 = 1275601) B1275601
theorem B848875 : Blo 754331 848875 := bstep (se 1 (by rfl) ⟨636656, by rfl⟩ : syracuseStep 848875 = 1273313) B1273313
theorem B848983 : Blo 754331 848983 := bstep (se 1 (by rfl) ⟨636737, by rfl⟩ : syracuseStep 848983 = 1273475) B1273475
theorem B2946179 : Blo 754331 2946179 := bstep (se 1 (by rfl) ⟨2209634, by rfl⟩ : syracuseStep 2946179 = 4419269) B4419269
theorem B1701017 : Blo 754331 1701017 := bstep (se 2 (by rfl) ⟨637881, by rfl⟩ : syracuseStep 1701017 = 1275763) B1275763
theorem B2553011 : Blo 754331 2553011 := bstep (se 1 (by rfl) ⟨1914758, by rfl⟩ : syracuseStep 2553011 = 3829517) B3829517
theorem B1275095 : Blo 754331 1275095 := bstep (se 1 (by rfl) ⟨956321, by rfl⟩ : syracuseStep 1275095 = 1912643) B1912643
theorem B1701107 : Blo 754331 1701107 := bstep (se 1 (by rfl) ⟨1275830, by rfl⟩ : syracuseStep 1701107 = 2551661) B2551661
theorem B849163 : Blo 754331 849163 := bstep (se 1 (by rfl) ⟨636872, by rfl⟩ : syracuseStep 849163 = 1273745) B1273745
theorem B1701143 : Blo 754331 1701143 := bstep (se 1 (by rfl) ⟨1275857, by rfl⟩ : syracuseStep 1701143 = 2551715) B2551715
theorem B1275223 : Blo 754331 1275223 := bstep (se 1 (by rfl) ⟨956417, by rfl⟩ : syracuseStep 1275223 = 1912835) B1912835
theorem B849271 : Blo 754331 849271 := bstep (se 1 (by rfl) ⟨636953, by rfl⟩ : syracuseStep 849271 = 1273907) B1273907
theorem B2553281 : Blo 754331 2553281 := bstep (se 2 (by rfl) ⟨957480, by rfl⟩ : syracuseStep 2553281 = 1914961) B1914961
theorem B1701323 : Blo 754331 1701323 := bstep (se 1 (by rfl) ⟨1275992, by rfl⟩ : syracuseStep 1701323 = 2551985) B2551985
theorem B1701377 : Blo 754331 1701377 := bstep (se 2 (by rfl) ⟨638016, by rfl⟩ : syracuseStep 1701377 = 1276033) B1276033
theorem B1078795 : Blo 754331 1078795 := bstep (se 1 (by rfl) ⟨809096, by rfl⟩ : syracuseStep 1078795 = 1618193) B1618193
theorem B849451 : Blo 754331 849451 := bstep (se 1 (by rfl) ⟨637088, by rfl⟩ : syracuseStep 849451 = 1274177) B1274177
theorem B849559 : Blo 754331 849559 := bstep (se 1 (by rfl) ⟨637169, by rfl⟩ : syracuseStep 849559 = 1274339) B1274339
theorem B1701593 : Blo 754331 1701593 := bstep (se 2 (by rfl) ⟨638097, by rfl⟩ : syracuseStep 1701593 = 1276195) B1276195
theorem B1701683 : Blo 754331 1701683 := bstep (se 1 (by rfl) ⟨1276262, by rfl⟩ : syracuseStep 1701683 = 2552525) B2552525
theorem B849739 : Blo 754331 849739 := bstep (se 1 (by rfl) ⟨637304, by rfl⟩ : syracuseStep 849739 = 1274609) B1274609
theorem B1701719 : Blo 754331 1701719 := bstep (se 1 (by rfl) ⟨1276289, by rfl⟩ : syracuseStep 1701719 = 2552579) B2552579
theorem B849847 : Blo 754331 849847 := bstep (se 1 (by rfl) ⟨637385, by rfl⟩ : syracuseStep 849847 = 1274771) B1274771
theorem B1275851 : Blo 754331 1275851 := bstep (se 1 (by rfl) ⟨956888, by rfl⟩ : syracuseStep 1275851 = 1913777) B1913777
theorem B2553821 : Blo 754331 2553821 := bstep (se 3 (by rfl) ⟨478841, by rfl⟩ : syracuseStep 2553821 = 957683) B957683
theorem B1701899 : Blo 754331 1701899 := bstep (se 1 (by rfl) ⟨1276424, by rfl⟩ : syracuseStep 1701899 = 2552849) B2552849
theorem B5732369 : Blo 754331 5732369 := bstep (se 2 (by rfl) ⟨2149638, by rfl⟩ : syracuseStep 5732369 = 4299277) B4299277
theorem B1701953 : Blo 754331 1701953 := bstep (se 2 (by rfl) ⟨638232, by rfl⟩ : syracuseStep 1701953 = 1276465) B1276465
theorem B1275979 : Blo 754331 1275979 := bstep (se 1 (by rfl) ⟨956984, by rfl⟩ : syracuseStep 1275979 = 1913969) B1913969
theorem B850027 : Blo 754331 850027 := bstep (se 1 (by rfl) ⟨637520, by rfl⟩ : syracuseStep 850027 = 1275041) B1275041
theorem B6125719 : Blo 754331 6125719 := bstep (se 1 (by rfl) ⟨4594289, by rfl⟩ : syracuseStep 6125719 = 9188579) B9188579
theorem B850135 : Blo 754331 850135 := bstep (se 1 (by rfl) ⟨637601, by rfl⟩ : syracuseStep 850135 = 1275203) B1275203
theorem B1276121 : Blo 754331 1276121 := bstep (se 2 (by rfl) ⟨478545, by rfl⟩ : syracuseStep 1276121 = 957091) B957091
theorem B1702169 : Blo 754331 1702169 := bstep (se 2 (by rfl) ⟨638313, by rfl⟩ : syracuseStep 1702169 = 1276627) B1276627
theorem B3832109 : Blo 754331 3832109 := bstep (se 3 (by rfl) ⟨718520, by rfl⟩ : syracuseStep 3832109 = 1437041) B1437041
theorem B1276249 : Blo 754331 1276249 := bstep (se 2 (by rfl) ⟨478593, by rfl⟩ : syracuseStep 1276249 = 957187) B957187
theorem B1702259 : Blo 754331 1702259 := bstep (se 1 (by rfl) ⟨1276694, by rfl⟩ : syracuseStep 1702259 = 2553389) B2553389
theorem B850315 : Blo 754331 850315 := bstep (se 1 (by rfl) ⟨637736, by rfl⟩ : syracuseStep 850315 = 1275473) B1275473
theorem B1702295 : Blo 754331 1702295 := bstep (se 1 (by rfl) ⟨1276721, by rfl⟩ : syracuseStep 1702295 = 2553443) B2553443
theorem B850423 : Blo 754331 850423 := bstep (se 1 (by rfl) ⟨637817, by rfl⟩ : syracuseStep 850423 = 1275635) B1275635
theorem B1702475 : Blo 754331 1702475 := bstep (se 1 (by rfl) ⟨1276856, by rfl⟩ : syracuseStep 1702475 = 2553713) B2553713
theorem B1702529 : Blo 754331 1702529 := bstep (se 2 (by rfl) ⟨638448, by rfl⟩ : syracuseStep 1702529 = 1276897) B1276897
theorem B10877591 : Blo 754331 10877591 := bstep (se 1 (by rfl) ⟨8158193, by rfl⟩ : syracuseStep 10877591 = 16316387) B16316387
theorem B850603 : Blo 754331 850603 := bstep (se 1 (by rfl) ⟨637952, by rfl⟩ : syracuseStep 850603 = 1275905) B1275905
theorem B850711 : Blo 754331 850711 := bstep (se 1 (by rfl) ⟨638033, by rfl⟩ : syracuseStep 850711 = 1276067) B1276067
theorem B1702745 : Blo 754331 1702745 := bstep (se 2 (by rfl) ⟨638529, by rfl⟩ : syracuseStep 1702745 = 1277059) B1277059
theorem B1211287 : Blo 754331 1211287 := bstep (se 1 (by rfl) ⟨908465, by rfl⟩ : syracuseStep 1211287 = 1816931) B1816931
theorem B1276823 : Blo 754331 1276823 := bstep (se 1 (by rfl) ⟨957617, by rfl⟩ : syracuseStep 1276823 = 1915235) B1915235
theorem B1702835 : Blo 754331 1702835 := bstep (se 1 (by rfl) ⟨1277126, by rfl⟩ : syracuseStep 1702835 = 2554253) B2554253
theorem B850891 : Blo 754331 850891 := bstep (se 1 (by rfl) ⟨638168, by rfl⟩ : syracuseStep 850891 = 1276337) B1276337
theorem B1702871 : Blo 754331 1702871 := bstep (se 1 (by rfl) ⟨1277153, by rfl⟩ : syracuseStep 1702871 = 2554307) B2554307
theorem B1276951 : Blo 754331 1276951 := bstep (se 1 (by rfl) ⟨957713, by rfl⟩ : syracuseStep 1276951 = 1915427) B1915427
theorem B850999 : Blo 754331 850999 := bstep (se 1 (by rfl) ⟨638249, by rfl⟩ : syracuseStep 850999 = 1276499) B1276499
theorem B2554955 : Blo 754331 2554955 := bstep (se 1 (by rfl) ⟨1916216, by rfl⟩ : syracuseStep 2554955 = 3832433) B3832433
theorem B1703051 : Blo 754331 1703051 := bstep (se 1 (by rfl) ⟨1277288, by rfl⟩ : syracuseStep 1703051 = 2554577) B2554577
theorem B1703105 : Blo 754331 1703105 := bstep (se 2 (by rfl) ⟨638664, by rfl⟩ : syracuseStep 1703105 = 1277329) B1277329
theorem B2718937 : Blo 754331 2718937 := bstep (se 2 (by rfl) ⟨1019601, by rfl⟩ : syracuseStep 2718937 = 2039203) B2039203
theorem B851179 : Blo 754331 851179 := bstep (se 1 (by rfl) ⟨638384, by rfl⟩ : syracuseStep 851179 = 1276769) B1276769
theorem B851287 : Blo 754331 851287 := bstep (se 1 (by rfl) ⟨638465, by rfl⟩ : syracuseStep 851287 = 1276931) B1276931
theorem B2555225 : Blo 754331 2555225 := bstep (se 2 (by rfl) ⟨958209, by rfl⟩ : syracuseStep 2555225 = 1916419) B1916419
theorem B6126949 : Blo 754331 6126949 := bstep (se 4 (by rfl) ⟨574401, by rfl⟩ : syracuseStep 6126949 = 1148803) B1148803
theorem B1703321 : Blo 754331 1703321 := bstep (se 2 (by rfl) ⟨638745, by rfl⟩ : syracuseStep 1703321 = 1277491) B1277491
theorem B1211851 : Blo 754331 1211851 := bstep (se 1 (by rfl) ⟨908888, by rfl⟩ : syracuseStep 1211851 = 1817777) B1817777
theorem B1703411 : Blo 754331 1703411 := bstep (se 1 (by rfl) ⟨1277558, by rfl⟩ : syracuseStep 1703411 = 2555117) B2555117
theorem B1211915 : Blo 754331 1211915 := bstep (se 1 (by rfl) ⟨908936, by rfl⟩ : syracuseStep 1211915 = 1817873) B1817873
theorem B851467 : Blo 754331 851467 := bstep (se 1 (by rfl) ⟨638600, by rfl⟩ : syracuseStep 851467 = 1277201) B1277201
theorem B1703447 : Blo 754331 1703447 := bstep (se 1 (by rfl) ⟨1277585, by rfl⟩ : syracuseStep 1703447 = 2555171) B2555171
theorem B851575 : Blo 754331 851575 := bstep (se 1 (by rfl) ⟨638681, by rfl⟩ : syracuseStep 851575 = 1277363) B1277363
theorem B1277579 : Blo 754331 1277579 := bstep (se 1 (by rfl) ⟨958184, by rfl⟩ : syracuseStep 1277579 = 1916369) B1916369
theorem B2588311 : Blo 754331 2588311 := bstep (se 1 (by rfl) ⟨1941233, by rfl⟩ : syracuseStep 2588311 = 3882467) B3882467
theorem B1703627 : Blo 754331 1703627 := bstep (se 1 (by rfl) ⟨1277720, by rfl⟩ : syracuseStep 1703627 = 2555441) B2555441
theorem B1703681 : Blo 754331 1703681 := bstep (se 2 (by rfl) ⟨638880, by rfl⟩ : syracuseStep 1703681 = 1277761) B1277761
theorem B1277707 : Blo 754331 1277707 := bstep (se 1 (by rfl) ⟨958280, by rfl⟩ : syracuseStep 1277707 = 1916561) B1916561
theorem B851755 : Blo 754331 851755 := bstep (se 1 (by rfl) ⟨638816, by rfl⟩ : syracuseStep 851755 = 1277633) B1277633
theorem B851863 : Blo 754331 851863 := bstep (se 1 (by rfl) ⟨638897, by rfl⟩ : syracuseStep 851863 = 1277795) B1277795
theorem B1277849 : Blo 754331 1277849 := bstep (se 2 (by rfl) ⟨479193, by rfl⟩ : syracuseStep 1277849 = 958387) B958387
theorem B1703897 : Blo 754331 1703897 := bstep (se 2 (by rfl) ⟨638961, by rfl⟩ : syracuseStep 1703897 = 1277923) B1277923
theorem B1703951 : Blo 754331 1703951 := bstep (se 1 (by rfl) ⟨1277963, by rfl⟩ : syracuseStep 1703951 = 2555927) B2555927
theorem B12288023 : Blo 754331 12288023 := bstep (se 1 (by rfl) ⟨9216017, by rfl⟩ : syracuseStep 12288023 = 18432035) B18432035
theorem B1703969 : Blo 754331 1703969 := bstep (se 2 (by rfl) ⟨638988, by rfl⟩ : syracuseStep 1703969 = 1277977) B1277977
theorem B1278011 : Blo 754331 1278011 := bstep (se 1 (by rfl) ⟨958508, by rfl⟩ : syracuseStep 1278011 = 1917017) B1917017
theorem B2719831 : Blo 754331 2719831 := bstep (se 1 (by rfl) ⟨2039873, by rfl⟩ : syracuseStep 2719831 = 4079747) B4079747
theorem B1704311 : Blo 754331 1704311 := bstep (se 1 (by rfl) ⟨1278233, by rfl⟩ : syracuseStep 1704311 = 2556467) B2556467
theorem B852367 : Blo 754331 852367 := bstep (se 1 (by rfl) ⟨639275, by rfl⟩ : syracuseStep 852367 = 1278551) B1278551
theorem B5439889 : Blo 754331 5439889 := bstep (se 2 (by rfl) ⟨2039958, by rfl⟩ : syracuseStep 5439889 = 4079917) B4079917
theorem B3637649 : Blo 754331 3637649 := bstep (se 2 (by rfl) ⟨1364118, by rfl⟩ : syracuseStep 3637649 = 2728237) B2728237
theorem B1278409 : Blo 754331 1278409 := bstep (se 2 (by rfl) ⟨479403, by rfl⟩ : syracuseStep 1278409 = 958807) B958807
theorem B4850219 : Blo 754331 4850219 := bstep (se 1 (by rfl) ⟨3637664, by rfl⟩ : syracuseStep 4850219 = 7275329) B7275329
theorem B1704491 : Blo 754331 1704491 := bstep (se 1 (by rfl) ⟨1278368, by rfl⟩ : syracuseStep 1704491 = 2556737) B2556737
theorem B754363 : Blo 754331 754363 := bstep (se 1 (by rfl) ⟨565772, by rfl⟩ : syracuseStep 754363 = 1131545) B1131545
theorem B754439 : Blo 754331 754439 := bstep (se 1 (by rfl) ⟨565829, by rfl⟩ : syracuseStep 754439 = 1131659) B1131659
theorem B754447 : Blo 754331 754447 := bstep (se 1 (by rfl) ⟨565835, by rfl⟩ : syracuseStep 754447 = 1131671) B1131671
theorem B754491 : Blo 754331 754491 := bstep (se 1 (by rfl) ⟨565868, by rfl⟩ : syracuseStep 754491 = 1131737) B1131737
theorem B754567 : Blo 754331 754567 := bstep (se 1 (by rfl) ⟨565925, by rfl⟩ : syracuseStep 754567 = 1131851) B1131851
theorem B852871 : Blo 754331 852871 := bstep (se 1 (by rfl) ⟨639653, by rfl⟩ : syracuseStep 852871 = 1279307) B1279307
theorem B754575 : Blo 754331 754575 := bstep (se 1 (by rfl) ⟨565931, by rfl⟩ : syracuseStep 754575 = 1131863) B1131863
theorem B1704851 : Blo 754331 1704851 := bstep (se 1 (by rfl) ⟨1278638, by rfl⟩ : syracuseStep 1704851 = 2557277) B2557277
theorem B9208727 : Blo 754331 9208727 := bstep (se 1 (by rfl) ⟨6906545, by rfl⟩ : syracuseStep 9208727 = 13813091) B13813091
theorem B754619 : Blo 754331 754619 := bstep (se 1 (by rfl) ⟨565964, by rfl⟩ : syracuseStep 754619 = 1131929) B1131929
theorem B1704905 : Blo 754331 1704905 := bstep (se 2 (by rfl) ⟨639339, by rfl⟩ : syracuseStep 1704905 = 1278679) B1278679
theorem B754695 : Blo 754331 754695 := bstep (se 1 (by rfl) ⟨566021, by rfl⟩ : syracuseStep 754695 = 1132043) B1132043
theorem B754703 : Blo 754331 754703 := bstep (se 1 (by rfl) ⟨566027, by rfl⟩ : syracuseStep 754703 = 1132055) B1132055
theorem B754747 : Blo 754331 754747 := bstep (se 1 (by rfl) ⟨566060, by rfl⟩ : syracuseStep 754747 = 1132121) B1132121
theorem B853051 : Blo 754331 853051 := bstep (se 1 (by rfl) ⟨639788, by rfl⟩ : syracuseStep 853051 = 1279577) B1279577
theorem B754823 : Blo 754331 754823 := bstep (se 1 (by rfl) ⟨566117, by rfl⟩ : syracuseStep 754823 = 1132235) B1132235
theorem B1279111 : Blo 754331 1279111 := bstep (se 1 (by rfl) ⟨959333, by rfl⟩ : syracuseStep 1279111 = 1918667) B1918667
theorem B754831 : Blo 754331 754831 := bstep (se 1 (by rfl) ⟨566123, by rfl⟩ : syracuseStep 754831 = 1132247) B1132247
theorem B754875 : Blo 754331 754875 := bstep (se 1 (by rfl) ⟨566156, by rfl⟩ : syracuseStep 754875 = 1132313) B1132313
theorem B754951 : Blo 754331 754951 := bstep (se 1 (by rfl) ⟨566213, by rfl⟩ : syracuseStep 754951 = 1132427) B1132427
theorem B754959 : Blo 754331 754959 := bstep (se 1 (by rfl) ⟨566219, by rfl⟩ : syracuseStep 754959 = 1132439) B1132439
theorem B3835187 : Blo 754331 3835187 := bstep (se 1 (by rfl) ⟨2876390, by rfl⟩ : syracuseStep 3835187 = 5752781) B5752781
theorem B755003 : Blo 754331 755003 := bstep (se 1 (by rfl) ⟨566252, by rfl⟩ : syracuseStep 755003 = 1132505) B1132505
theorem B8750429 : Blo 754331 8750429 := bstep (se 3 (by rfl) ⟨1640705, by rfl⟩ : syracuseStep 8750429 = 3281411) B3281411
theorem B755079 : Blo 754331 755079 := bstep (se 1 (by rfl) ⟨566309, by rfl⟩ : syracuseStep 755079 = 1132619) B1132619
theorem B755087 : Blo 754331 755087 := bstep (se 1 (by rfl) ⟨566315, by rfl⟩ : syracuseStep 755087 = 1132631) B1132631
theorem B2557331 : Blo 754331 2557331 := bstep (se 1 (by rfl) ⟨1917998, by rfl⟩ : syracuseStep 2557331 = 3835997) B3835997
theorem B755131 : Blo 754331 755131 := bstep (se 1 (by rfl) ⟨566348, by rfl⟩ : syracuseStep 755131 = 1132697) B1132697
theorem B755207 : Blo 754331 755207 := bstep (se 1 (by rfl) ⟨566405, by rfl⟩ : syracuseStep 755207 = 1132811) B1132811
theorem B755215 : Blo 754331 755215 := bstep (se 1 (by rfl) ⟨566411, by rfl⟩ : syracuseStep 755215 = 1132823) B1132823
theorem B755259 : Blo 754331 755259 := bstep (se 1 (by rfl) ⟨566444, by rfl⟩ : syracuseStep 755259 = 1132889) B1132889
theorem B3835511 : Blo 754331 3835511 := bstep (se 1 (by rfl) ⟨2876633, by rfl⟩ : syracuseStep 3835511 = 5753267) B5753267
theorem B755335 : Blo 754331 755335 := bstep (se 1 (by rfl) ⟨566501, by rfl⟩ : syracuseStep 755335 = 1133003) B1133003
theorem B1705607 : Blo 754331 1705607 := bstep (se 1 (by rfl) ⟨1279205, by rfl⟩ : syracuseStep 1705607 = 2558411) B2558411
theorem B755343 : Blo 754331 755343 := bstep (se 1 (by rfl) ⟨566507, by rfl⟩ : syracuseStep 755343 = 1133015) B1133015
theorem B755387 : Blo 754331 755387 := bstep (se 1 (by rfl) ⟨566540, by rfl⟩ : syracuseStep 755387 = 1133081) B1133081
theorem B755463 : Blo 754331 755463 := bstep (se 1 (by rfl) ⟨566597, by rfl⟩ : syracuseStep 755463 = 1133195) B1133195
theorem B755471 : Blo 754331 755471 := bstep (se 1 (by rfl) ⟨566603, by rfl⟩ : syracuseStep 755471 = 1133207) B1133207
theorem B755515 : Blo 754331 755515 := bstep (se 1 (by rfl) ⟨566636, by rfl⟩ : syracuseStep 755515 = 1133273) B1133273
theorem B1705787 : Blo 754331 1705787 := bstep (se 1 (by rfl) ⟨1279340, by rfl⟩ : syracuseStep 1705787 = 2558681) B2558681
theorem B755591 : Blo 754331 755591 := bstep (se 1 (by rfl) ⟨566693, by rfl⟩ : syracuseStep 755591 = 1133387) B1133387
theorem B755599 : Blo 754331 755599 := bstep (se 1 (by rfl) ⟨566699, by rfl⟩ : syracuseStep 755599 = 1133399) B1133399
theorem B1705913 : Blo 754331 1705913 := bstep (se 2 (by rfl) ⟨639717, by rfl⟩ : syracuseStep 1705913 = 1279435) B1279435
theorem B755643 : Blo 754331 755643 := bstep (se 1 (by rfl) ⟨566732, by rfl⟩ : syracuseStep 755643 = 1133465) B1133465
theorem B755719 : Blo 754331 755719 := bstep (se 1 (by rfl) ⟨566789, by rfl⟩ : syracuseStep 755719 = 1133579) B1133579
theorem B755727 : Blo 754331 755727 := bstep (se 1 (by rfl) ⟨566795, by rfl⟩ : syracuseStep 755727 = 1133591) B1133591
theorem B755771 : Blo 754331 755771 := bstep (se 1 (by rfl) ⟨566828, by rfl⟩ : syracuseStep 755771 = 1133657) B1133657
theorem B755847 : Blo 754331 755847 := bstep (se 1 (by rfl) ⟨566885, by rfl⟩ : syracuseStep 755847 = 1133771) B1133771
theorem B755855 : Blo 754331 755855 := bstep (se 1 (by rfl) ⟨566891, by rfl⟩ : syracuseStep 755855 = 1133783) B1133783
theorem B755899 : Blo 754331 755899 := bstep (se 1 (by rfl) ⟨566924, by rfl⟩ : syracuseStep 755899 = 1133849) B1133849
theorem B1149175 : Blo 754331 1149175 := bstep (se 1 (by rfl) ⟨861881, by rfl⟩ : syracuseStep 1149175 = 1723763) B1723763
theorem B755975 : Blo 754331 755975 := bstep (se 1 (by rfl) ⟨566981, by rfl⟩ : syracuseStep 755975 = 1133963) B1133963
theorem B755983 : Blo 754331 755983 := bstep (se 1 (by rfl) ⟨566987, by rfl⟩ : syracuseStep 755983 = 1133975) B1133975
theorem B11634961 : Blo 754331 11634961 := bstep (se 2 (by rfl) ⟨4363110, by rfl⟩ : syracuseStep 11634961 = 8726221) B8726221
theorem B756027 : Blo 754331 756027 := bstep (se 1 (by rfl) ⟨567020, by rfl⟩ : syracuseStep 756027 = 1134041) B1134041
theorem B756103 : Blo 754331 756103 := bstep (se 1 (by rfl) ⟨567077, by rfl⟩ : syracuseStep 756103 = 1134155) B1134155
theorem B756111 : Blo 754331 756111 := bstep (se 1 (by rfl) ⟨567083, by rfl⟩ : syracuseStep 756111 = 1134167) B1134167
theorem B14518673 : Blo 754331 14518673 := bstep (se 2 (by rfl) ⟨5444502, by rfl⟩ : syracuseStep 14518673 = 10889005) B10889005
theorem B756155 : Blo 754331 756155 := bstep (se 1 (by rfl) ⟨567116, by rfl⟩ : syracuseStep 756155 = 1134233) B1134233
theorem B756231 : Blo 754331 756231 := bstep (se 1 (by rfl) ⟨567173, by rfl⟩ : syracuseStep 756231 = 1134347) B1134347
theorem B756239 : Blo 754331 756239 := bstep (se 1 (by rfl) ⟨567179, by rfl⟩ : syracuseStep 756239 = 1134359) B1134359
theorem B4590103 : Blo 754331 4590103 := bstep (se 1 (by rfl) ⟨3442577, by rfl⟩ : syracuseStep 4590103 = 6885155) B6885155
theorem B756283 : Blo 754331 756283 := bstep (se 1 (by rfl) ⟨567212, by rfl⟩ : syracuseStep 756283 = 1134425) B1134425
theorem B3836483 : Blo 754331 3836483 := bstep (se 1 (by rfl) ⟨2877362, by rfl⟩ : syracuseStep 3836483 = 5754725) B5754725
theorem B756359 : Blo 754331 756359 := bstep (se 1 (by rfl) ⟨567269, by rfl⟩ : syracuseStep 756359 = 1134539) B1134539
theorem B756367 : Blo 754331 756367 := bstep (se 1 (by rfl) ⟨567275, by rfl⟩ : syracuseStep 756367 = 1134551) B1134551
theorem B756411 : Blo 754331 756411 := bstep (se 1 (by rfl) ⟨567308, by rfl⟩ : syracuseStep 756411 = 1134617) B1134617
theorem B10914497 : Blo 754331 10914497 := bstep (se 2 (by rfl) ⟨4092936, by rfl⟩ : syracuseStep 10914497 = 8185873) B8185873
theorem B756487 : Blo 754331 756487 := bstep (se 1 (by rfl) ⟨567365, by rfl⟩ : syracuseStep 756487 = 1134731) B1134731
theorem B756495 : Blo 754331 756495 := bstep (se 1 (by rfl) ⟨567371, by rfl⟩ : syracuseStep 756495 = 1134743) B1134743
theorem B2558735 : Blo 754331 2558735 := bstep (se 1 (by rfl) ⟨1919051, by rfl⟩ : syracuseStep 2558735 = 3838103) B3838103
theorem B756539 : Blo 754331 756539 := bstep (se 1 (by rfl) ⟨567404, by rfl⟩ : syracuseStep 756539 = 1134809) B1134809
theorem B756615 : Blo 754331 756615 := bstep (se 1 (by rfl) ⟨567461, by rfl⟩ : syracuseStep 756615 = 1134923) B1134923
theorem B3836807 : Blo 754331 3836807 := bstep (se 1 (by rfl) ⟨2877605, by rfl⟩ : syracuseStep 3836807 = 5755211) B5755211
theorem B756623 : Blo 754331 756623 := bstep (se 1 (by rfl) ⟨567467, by rfl⟩ : syracuseStep 756623 = 1134935) B1134935
theorem B756667 : Blo 754331 756667 := bstep (se 1 (by rfl) ⟨567500, by rfl⟩ : syracuseStep 756667 = 1135001) B1135001
theorem B756743 : Blo 754331 756743 := bstep (se 1 (by rfl) ⟨567557, by rfl⟩ : syracuseStep 756743 = 1135115) B1135115
theorem B756751 : Blo 754331 756751 := bstep (se 1 (by rfl) ⟨567563, by rfl⟩ : syracuseStep 756751 = 1135127) B1135127
theorem B2559005 : Blo 754331 2559005 := bstep (se 3 (by rfl) ⟨479813, by rfl⟩ : syracuseStep 2559005 = 959627) B959627
theorem B756795 : Blo 754331 756795 := bstep (se 1 (by rfl) ⟨567596, by rfl⟩ : syracuseStep 756795 = 1135193) B1135193
theorem B14027863 : Blo 754331 14027863 := bstep (se 1 (by rfl) ⟨10520897, by rfl⟩ : syracuseStep 14027863 = 21041795) B21041795
theorem B756871 : Blo 754331 756871 := bstep (se 1 (by rfl) ⟨567653, by rfl⟩ : syracuseStep 756871 = 1135307) B1135307
theorem B756879 : Blo 754331 756879 := bstep (se 1 (by rfl) ⟨567659, by rfl⟩ : syracuseStep 756879 = 1135319) B1135319
theorem B756923 : Blo 754331 756923 := bstep (se 1 (by rfl) ⟨567692, by rfl⟩ : syracuseStep 756923 = 1135385) B1135385
theorem B756999 : Blo 754331 756999 := bstep (se 1 (by rfl) ⟨567749, by rfl⟩ : syracuseStep 756999 = 1135499) B1135499
theorem B4590863 : Blo 754331 4590863 := bstep (se 1 (by rfl) ⟨3443147, by rfl⟩ : syracuseStep 4590863 = 6886295) B6886295
theorem B757007 : Blo 754331 757007 := bstep (se 1 (by rfl) ⟨567755, by rfl⟩ : syracuseStep 757007 = 1135511) B1135511
theorem B757051 : Blo 754331 757051 := bstep (se 1 (by rfl) ⟨567788, by rfl⟩ : syracuseStep 757051 = 1135577) B1135577
theorem B757127 : Blo 754331 757127 := bstep (se 1 (by rfl) ⟨567845, by rfl⟩ : syracuseStep 757127 = 1135691) B1135691
theorem B757135 : Blo 754331 757135 := bstep (se 1 (by rfl) ⟨567851, by rfl⟩ : syracuseStep 757135 = 1135703) B1135703
theorem B757179 : Blo 754331 757179 := bstep (se 1 (by rfl) ⟨567884, by rfl⟩ : syracuseStep 757179 = 1135769) B1135769
theorem B757255 : Blo 754331 757255 := bstep (se 1 (by rfl) ⟨567941, by rfl⟩ : syracuseStep 757255 = 1135883) B1135883
theorem B757263 : Blo 754331 757263 := bstep (se 1 (by rfl) ⟨567947, by rfl⟩ : syracuseStep 757263 = 1135895) B1135895
theorem B757307 : Blo 754331 757307 := bstep (se 1 (by rfl) ⟨567980, by rfl⟩ : syracuseStep 757307 = 1135961) B1135961
theorem B757383 : Blo 754331 757383 := bstep (se 1 (by rfl) ⟨568037, by rfl⟩ : syracuseStep 757383 = 1136075) B1136075
theorem B757391 : Blo 754331 757391 := bstep (se 1 (by rfl) ⟨568043, by rfl⟩ : syracuseStep 757391 = 1136087) B1136087
theorem B757435 : Blo 754331 757435 := bstep (se 1 (by rfl) ⟨568076, by rfl⟩ : syracuseStep 757435 = 1136153) B1136153
theorem B6885121 : Blo 754331 6885121 := bstep (se 2 (by rfl) ⟨2581920, by rfl⟩ : syracuseStep 6885121 = 5163841) B5163841
theorem B757511 : Blo 754331 757511 := bstep (se 1 (by rfl) ⟨568133, by rfl⟩ : syracuseStep 757511 = 1136267) B1136267
theorem B757519 : Blo 754331 757519 := bstep (se 1 (by rfl) ⟨568139, by rfl⟩ : syracuseStep 757519 = 1136279) B1136279
theorem B1773371 : Blo 754331 1773371 := bstep (se 1 (by rfl) ⟨1330028, by rfl⟩ : syracuseStep 1773371 = 2660057) B2660057
theorem B757563 : Blo 754331 757563 := bstep (se 1 (by rfl) ⟨568172, by rfl⟩ : syracuseStep 757563 = 1136345) B1136345
theorem B757639 : Blo 754331 757639 := bstep (se 1 (by rfl) ⟨568229, by rfl⟩ : syracuseStep 757639 = 1136459) B1136459
theorem B757647 : Blo 754331 757647 := bstep (se 1 (by rfl) ⟨568235, by rfl⟩ : syracuseStep 757647 = 1136471) B1136471
theorem B757691 : Blo 754331 757691 := bstep (se 1 (by rfl) ⟨568268, by rfl⟩ : syracuseStep 757691 = 1136537) B1136537
theorem B757767 : Blo 754331 757767 := bstep (se 1 (by rfl) ⟨568325, by rfl⟩ : syracuseStep 757767 = 1136651) B1136651
theorem B757775 : Blo 754331 757775 := bstep (se 1 (by rfl) ⟨568331, by rfl⟩ : syracuseStep 757775 = 1136663) B1136663
theorem B757819 : Blo 754331 757819 := bstep (se 1 (by rfl) ⟨568364, by rfl⟩ : syracuseStep 757819 = 1136729) B1136729
theorem B757895 : Blo 754331 757895 := bstep (se 1 (by rfl) ⟨568421, by rfl⟩ : syracuseStep 757895 = 1136843) B1136843
theorem B757903 : Blo 754331 757903 := bstep (se 1 (by rfl) ⟨568427, by rfl⟩ : syracuseStep 757903 = 1136855) B1136855
theorem B757947 : Blo 754331 757947 := bstep (se 1 (by rfl) ⟨568460, by rfl⟩ : syracuseStep 757947 = 1136921) B1136921
theorem B2724097 : Blo 754331 2724097 := bstep (se 2 (by rfl) ⟨1021536, by rfl⟩ : syracuseStep 2724097 = 2043073) B2043073
theorem B758023 : Blo 754331 758023 := bstep (se 1 (by rfl) ⟨568517, by rfl⟩ : syracuseStep 758023 = 1137035) B1137035
theorem B758031 : Blo 754331 758031 := bstep (se 1 (by rfl) ⟨568523, by rfl⟩ : syracuseStep 758031 = 1137047) B1137047
theorem B758075 : Blo 754331 758075 := bstep (se 1 (by rfl) ⟨568556, by rfl⟩ : syracuseStep 758075 = 1137113) B1137113
theorem B758151 : Blo 754331 758151 := bstep (se 1 (by rfl) ⟨568613, by rfl⟩ : syracuseStep 758151 = 1137227) B1137227
theorem B954767 : Blo 754331 954767 := bstep (se 1 (by rfl) ⟨716075, by rfl⟩ : syracuseStep 954767 = 1432151) B1432151
theorem B758159 : Blo 754331 758159 := bstep (se 1 (by rfl) ⟨568619, by rfl⟩ : syracuseStep 758159 = 1137239) B1137239
theorem B758203 : Blo 754331 758203 := bstep (se 1 (by rfl) ⟨568652, by rfl⟩ : syracuseStep 758203 = 1137305) B1137305
theorem B758279 : Blo 754331 758279 := bstep (se 1 (by rfl) ⟨568709, by rfl⟩ : syracuseStep 758279 = 1137419) B1137419
theorem B758287 : Blo 754331 758287 := bstep (se 1 (by rfl) ⟨568715, by rfl⟩ : syracuseStep 758287 = 1137431) B1137431
theorem B758331 : Blo 754331 758331 := bstep (se 1 (by rfl) ⟨568748, by rfl⟩ : syracuseStep 758331 = 1137497) B1137497
theorem B14554349 : Blo 754331 14554349 := bstep (se 3 (by rfl) ⟨2728940, by rfl⟩ : syracuseStep 14554349 = 5457881) B5457881
theorem B18388433 : Blo 754331 18388433 := bstep (se 2 (by rfl) ⟨6895662, by rfl⟩ : syracuseStep 18388433 = 13791325) B13791325
theorem B5445425 : Blo 754331 5445425 := bstep (se 2 (by rfl) ⟨2042034, by rfl⟩ : syracuseStep 5445425 = 4084069) B4084069
theorem B5740631 : Blo 754331 5740631 := bstep (se 1 (by rfl) ⟨4305473, by rfl⟩ : syracuseStep 5740631 = 8610947) B8610947
theorem B17701037 : Blo 754331 17701037 := bstep (se 3 (by rfl) ⟨3318944, by rfl⟩ : syracuseStep 17701037 = 6637889) B6637889
theorem B3643663 : Blo 754331 3643663 := bstep (se 1 (by rfl) ⟨2732747, by rfl⟩ : syracuseStep 3643663 = 5465495) B5465495
theorem B1022267 : Blo 754331 1022267 := bstep (se 1 (by rfl) ⟨766700, by rfl⟩ : syracuseStep 1022267 = 1533401) B1533401
theorem B8198585 : Blo 754331 8198585 := bstep (se 2 (by rfl) ⟨3074469, by rfl⟩ : syracuseStep 8198585 = 6148939) B6148939
theorem B6232643 : Blo 754331 6232643 := bstep (se 1 (by rfl) ⟨4674482, by rfl⟩ : syracuseStep 6232643 = 9348965) B9348965
theorem B2333455 : Blo 754331 2333455 := bstep (se 1 (by rfl) ⟨1750091, by rfl⟩ : syracuseStep 2333455 = 3500183) B3500183
theorem B6200453 : Blo 754331 6200453 := bstep (se 4 (by rfl) ⟨581292, by rfl⟩ : syracuseStep 6200453 = 1162585) B1162585
theorem B3874049 : Blo 754331 3874049 := bstep (se 2 (by rfl) ⟨1452768, by rfl⟩ : syracuseStep 3874049 = 2905537) B2905537
theorem B957739 : Blo 754331 957739 := bstep (se 1 (by rfl) ⟨718304, by rfl⟩ : syracuseStep 957739 = 1436609) B1436609
theorem B4300235 : Blo 754331 4300235 := bstep (se 1 (by rfl) ⟨3225176, by rfl⟩ : syracuseStep 4300235 = 6450353) B6450353
theorem B20717207 : Blo 754331 20717207 := bstep (se 1 (by rfl) ⟨15537905, by rfl⟩ : syracuseStep 20717207 = 31075811) B31075811
theorem B1941623 : Blo 754331 1941623 := bstep (se 1 (by rfl) ⟨1456217, by rfl⟩ : syracuseStep 1941623 = 2912435) B2912435
theorem B8167625 : Blo 754331 8167625 := bstep (se 2 (by rfl) ⟨3062859, by rfl⟩ : syracuseStep 8167625 = 6125719) B6125719
theorem B958711 : Blo 754331 958711 := bstep (se 1 (by rfl) ⟨719033, by rfl⟩ : syracuseStep 958711 = 1438067) B1438067
theorem B959035 : Blo 754331 959035 := bstep (se 1 (by rfl) ⟨719276, by rfl⟩ : syracuseStep 959035 = 1438553) B1438553
theorem B1909433 : Blo 754331 1909433 := bstep (se 2 (by rfl) ⟨716037, by rfl⟩ : syracuseStep 1909433 = 1432075) B1432075
theorem B7250725 : Blo 754331 7250725 := bstep (se 4 (by rfl) ⟨679755, by rfl⟩ : syracuseStep 7250725 = 1359511) B1359511
theorem B5448485 : Blo 754331 5448485 := bstep (se 4 (by rfl) ⟨510795, by rfl⟩ : syracuseStep 5448485 = 1021591) B1021591
theorem B3875843 : Blo 754331 3875843 := bstep (se 1 (by rfl) ⟨2906882, by rfl⟩ : syracuseStep 3875843 = 5813765) B5813765
theorem B1615049 : Blo 754331 1615049 := bstep (se 2 (by rfl) ⟨605643, by rfl⟩ : syracuseStep 1615049 = 1211287) B1211287
theorem B1942937 : Blo 754331 1942937 := bstep (se 2 (by rfl) ⟨728601, by rfl⟩ : syracuseStep 1942937 = 1457203) B1457203
theorem B8594909 : Blo 754331 8594909 := bstep (se 3 (by rfl) ⟨1611545, by rfl⟩ : syracuseStep 8594909 = 3223091) B3223091
theorem B1910425 : Blo 754331 1910425 := bstep (se 2 (by rfl) ⟨716409, by rfl⟩ : syracuseStep 1910425 = 1432819) B1432819
theorem B16361189 : Blo 754331 16361189 := bstep (se 4 (by rfl) ⟨1533861, by rfl⟩ : syracuseStep 16361189 = 3067723) B3067723
theorem B7251727 : Blo 754331 7251727 := bstep (se 1 (by rfl) ⟨5438795, by rfl⟩ : syracuseStep 7251727 = 10877591) B10877591
theorem B8169265 : Blo 754331 8169265 := bstep (se 2 (by rfl) ⟨3063474, by rfl⟩ : syracuseStep 8169265 = 6126949) B6126949
theorem B1910587 : Blo 754331 1910587 := bstep (se 1 (by rfl) ⟨1432940, by rfl⟩ : syracuseStep 1910587 = 2865881) B2865881
theorem B18425717 : Blo 754331 18425717 := bstep (se 5 (by rfl) ⟨863705, by rfl⟩ : syracuseStep 18425717 = 1727411) B1727411
theorem B1615801 : Blo 754331 1615801 := bstep (se 2 (by rfl) ⟨605925, by rfl⟩ : syracuseStep 1615801 = 1211851) B1211851
theorem B1910729 : Blo 754331 1910729 := bstep (se 2 (by rfl) ⟨716523, by rfl⟩ : syracuseStep 1910729 = 1433047) B1433047
theorem B3451081 : Blo 754331 3451081 := bstep (se 2 (by rfl) ⟨1294155, by rfl⟩ : syracuseStep 3451081 = 2588311) B2588311
theorem B1911073 : Blo 754331 1911073 := bstep (se 2 (by rfl) ⟨716652, by rfl⟩ : syracuseStep 1911073 = 1433305) B1433305
theorem B7285139 : Blo 754331 7285139 := bstep (se 1 (by rfl) ⟨5463854, by rfl⟩ : syracuseStep 7285139 = 10927709) B10927709
theorem B12462659 : Blo 754331 12462659 := bstep (se 1 (by rfl) ⟨9346994, by rfl⟩ : syracuseStep 12462659 = 18693989) B18693989
theorem B1813259 : Blo 754331 1813259 := bstep (se 1 (by rfl) ⟨1359944, by rfl⟩ : syracuseStep 1813259 = 2719889) B2719889
theorem B1911671 : Blo 754331 1911671 := bstep (se 1 (by rfl) ⟨1433753, by rfl⟩ : syracuseStep 1911671 = 2867507) B2867507
theorem B3779531 : Blo 754331 3779531 := bstep (se 1 (by rfl) ⟨2834648, by rfl⟩ : syracuseStep 3779531 = 5669297) B5669297
theorem B1813519 : Blo 754331 1813519 := bstep (se 1 (by rfl) ⟨1360139, by rfl⟩ : syracuseStep 1813519 = 2720279) B2720279
theorem B1813547 : Blo 754331 1813547 := bstep (se 1 (by rfl) ⟨1360160, by rfl⟩ : syracuseStep 1813547 = 2720321) B2720321
theorem B2731279 : Blo 754331 2731279 := bstep (se 1 (by rfl) ⟨2048459, by rfl⟩ : syracuseStep 2731279 = 4096919) B4096919
theorem B1617185 : Blo 754331 1617185 := bstep (se 2 (by rfl) ⟨606444, by rfl⟩ : syracuseStep 1617185 = 1212889) B1212889
theorem B2043593 : Blo 754331 2043593 := bstep (se 2 (by rfl) ⟨766347, by rfl⟩ : syracuseStep 2043593 = 1532695) B1532695
theorem B2240627 : Blo 754331 2240627 := bstep (se 1 (by rfl) ⟨1680470, by rfl⟩ : syracuseStep 2240627 = 3360941) B3360941
theorem B1912967 : Blo 754331 1912967 := bstep (se 1 (by rfl) ⟨1434725, by rfl⟩ : syracuseStep 1912967 = 2869451) B2869451
theorem B1913017 : Blo 754331 1913017 := bstep (se 2 (by rfl) ⟨717381, by rfl⟩ : syracuseStep 1913017 = 1434763) B1434763
theorem B1814903 : Blo 754331 1814903 := bstep (se 1 (by rfl) ⟨1361177, by rfl⟩ : syracuseStep 1814903 = 2722355) B2722355
theorem B8172035 : Blo 754331 8172035 := bstep (se 1 (by rfl) ⟨6129026, by rfl⟩ : syracuseStep 8172035 = 12258053) B12258053
theorem B1913615 : Blo 754331 1913615 := bstep (se 1 (by rfl) ⟨1435211, by rfl⟩ : syracuseStep 1913615 = 2870423) B2870423
theorem B1914313 : Blo 754331 1914313 := bstep (se 2 (by rfl) ⟨717867, by rfl⟩ : syracuseStep 1914313 = 1435735) B1435735
theorem B3225041 : Blo 754331 3225041 := bstep (se 2 (by rfl) ⟨1209390, by rfl⟩ : syracuseStep 3225041 = 2418781) B2418781
theorem B4306385 : Blo 754331 4306385 := bstep (se 2 (by rfl) ⟨1614894, by rfl⟩ : syracuseStep 4306385 = 3229789) B3229789
theorem B1914455 : Blo 754331 1914455 := bstep (se 1 (by rfl) ⟨1435841, by rfl⟩ : syracuseStep 1914455 = 2871683) B2871683
theorem B15546113 : Blo 754331 15546113 := bstep (se 2 (by rfl) ⟨5829792, by rfl⟩ : syracuseStep 15546113 = 11659585) B11659585
theorem B4306841 : Blo 754331 4306841 := bstep (se 2 (by rfl) ⟨1615065, by rfl⟩ : syracuseStep 4306841 = 3230131) B3230131
theorem B1292663 : Blo 754331 1292663 := bstep (se 1 (by rfl) ⟨969497, by rfl⟩ : syracuseStep 1292663 = 1938995) B1938995
theorem B768647 : Blo 754331 768647 := bstep (se 1 (by rfl) ⟨576485, by rfl⟩ : syracuseStep 768647 = 1152971) B1152971
theorem B2177945 : Blo 754331 2177945 := bstep (se 2 (by rfl) ⟨816729, by rfl⟩ : syracuseStep 2177945 = 1633459) B1633459
theorem B6471197 : Blo 754331 6471197 := bstep (se 3 (by rfl) ⟨1213349, by rfl⟩ : syracuseStep 6471197 = 2426699) B2426699
theorem B1916531 : Blo 754331 1916531 := bstep (se 1 (by rfl) ⟨1437398, by rfl⟩ : syracuseStep 1916531 = 2874797) B2874797
theorem B999055 : Blo 754331 999055 := bstep (se 1 (by rfl) ⟨749291, by rfl⟩ : syracuseStep 999055 = 1498583) B1498583
theorem B1818487 : Blo 754331 1818487 := bstep (se 1 (by rfl) ⟨1363865, by rfl⟩ : syracuseStep 1818487 = 2727731) B2727731
theorem B8634275 : Blo 754331 8634275 := bstep (se 1 (by rfl) ⟨6475706, by rfl⟩ : syracuseStep 8634275 = 12951413) B12951413
theorem B3063737 : Blo 754331 3063737 := bstep (se 2 (by rfl) ⟨1148901, by rfl⟩ : syracuseStep 3063737 = 2297803) B2297803
theorem B1917047 : Blo 754331 1917047 := bstep (se 1 (by rfl) ⟨1437785, by rfl⟩ : syracuseStep 1917047 = 2875571) B2875571
theorem B1294471 : Blo 754331 1294471 := bstep (se 1 (by rfl) ⟨970853, by rfl⟩ : syracuseStep 1294471 = 1941707) B1941707
theorem B8732873 : Blo 754331 8732873 := bstep (se 2 (by rfl) ⟨3274827, by rfl⟩ : syracuseStep 8732873 = 6549655) B6549655
theorem B2048827 : Blo 754331 2048827 := bstep (se 1 (by rfl) ⟨1536620, by rfl⟩ : syracuseStep 2048827 = 3073241) B3073241
theorem B1131527 : Blo 754331 1131527 := bstep (se 1 (by rfl) ⟨848645, by rfl⟩ : syracuseStep 1131527 = 1697291) B1697291
theorem B1131563 : Blo 754331 1131563 := bstep (se 1 (by rfl) ⟨848672, by rfl⟩ : syracuseStep 1131563 = 1697345) B1697345
theorem B1131593 : Blo 754331 1131593 := bstep (se 2 (by rfl) ⟨424347, by rfl⟩ : syracuseStep 1131593 = 848695) B848695
theorem B2868311 : Blo 754331 2868311 := bstep (se 1 (by rfl) ⟨2151233, by rfl⟩ : syracuseStep 2868311 = 4302467) B4302467
theorem B1918039 : Blo 754331 1918039 := bstep (se 1 (by rfl) ⟨1438529, by rfl⟩ : syracuseStep 1918039 = 2877059) B2877059
theorem B3327095 : Blo 754331 3327095 := bstep (se 1 (by rfl) ⟨2495321, by rfl⟩ : syracuseStep 3327095 = 4990643) B4990643
theorem B1131707 : Blo 754331 1131707 := bstep (se 1 (by rfl) ⟨848780, by rfl⟩ : syracuseStep 1131707 = 1697561) B1697561
theorem B3884233 : Blo 754331 3884233 := bstep (se 2 (by rfl) ⟨1456587, by rfl⟩ : syracuseStep 3884233 = 2913175) B2913175
theorem B1131767 : Blo 754331 1131767 := bstep (se 1 (by rfl) ⟨848825, by rfl⟩ : syracuseStep 1131767 = 1697651) B1697651
theorem B1131791 : Blo 754331 1131791 := bstep (se 1 (by rfl) ⟨848843, by rfl⟩ : syracuseStep 1131791 = 1697687) B1697687
theorem B1131833 : Blo 754331 1131833 := bstep (se 2 (by rfl) ⟨424437, by rfl⟩ : syracuseStep 1131833 = 848875) B848875
theorem B1131911 : Blo 754331 1131911 := bstep (se 1 (by rfl) ⟨848933, by rfl⟩ : syracuseStep 1131911 = 1697867) B1697867
theorem B1918343 : Blo 754331 1918343 := bstep (se 1 (by rfl) ⟨1438757, by rfl⟩ : syracuseStep 1918343 = 2877515) B2877515
theorem B1131947 : Blo 754331 1131947 := bstep (se 1 (by rfl) ⟨848960, by rfl⟩ : syracuseStep 1131947 = 1697921) B1697921
theorem B19613107 : Blo 754331 19613107 := bstep (se 1 (by rfl) ⟨14709830, by rfl⟩ : syracuseStep 19613107 = 29419661) B29419661
theorem B1131977 : Blo 754331 1131977 := bstep (se 2 (by rfl) ⟨424491, by rfl⟩ : syracuseStep 1131977 = 848983) B848983
theorem B1918475 : Blo 754331 1918475 := bstep (se 1 (by rfl) ⟨1438856, by rfl⟩ : syracuseStep 1918475 = 2877713) B2877713
theorem B4081175 : Blo 754331 4081175 := bstep (se 1 (by rfl) ⟨3060881, by rfl⟩ : syracuseStep 4081175 = 6121763) B6121763
theorem B1132091 : Blo 754331 1132091 := bstep (se 1 (by rfl) ⟨849068, by rfl⟩ : syracuseStep 1132091 = 1698137) B1698137
theorem B2868797 : Blo 754331 2868797 := bstep (se 3 (by rfl) ⟨537899, by rfl⟩ : syracuseStep 2868797 = 1075799) B1075799
theorem B1132151 : Blo 754331 1132151 := bstep (se 1 (by rfl) ⟨849113, by rfl⟩ : syracuseStep 1132151 = 1698227) B1698227
theorem B1132175 : Blo 754331 1132175 := bstep (se 1 (by rfl) ⟨849131, by rfl⟩ : syracuseStep 1132175 = 1698263) B1698263
theorem B1132217 : Blo 754331 1132217 := bstep (se 2 (by rfl) ⟨424581, by rfl⟩ : syracuseStep 1132217 = 849163) B849163
theorem B1132295 : Blo 754331 1132295 := bstep (se 1 (by rfl) ⟨849221, by rfl⟩ : syracuseStep 1132295 = 1698443) B1698443
theorem B1132331 : Blo 754331 1132331 := bstep (se 1 (by rfl) ⟨849248, by rfl⟩ : syracuseStep 1132331 = 1698497) B1698497
theorem B1132361 : Blo 754331 1132361 := bstep (se 2 (by rfl) ⟨424635, by rfl⟩ : syracuseStep 1132361 = 849271) B849271
theorem B1132475 : Blo 754331 1132475 := bstep (se 1 (by rfl) ⟨849356, by rfl⟩ : syracuseStep 1132475 = 1698713) B1698713
theorem B3819473 : Blo 754331 3819473 := bstep (se 2 (by rfl) ⟨1432302, by rfl⟩ : syracuseStep 3819473 = 2864605) B2864605
theorem B1132535 : Blo 754331 1132535 := bstep (se 1 (by rfl) ⟨849401, by rfl⟩ : syracuseStep 1132535 = 1698803) B1698803
theorem B2148353 : Blo 754331 2148353 := bstep (se 2 (by rfl) ⟨805632, by rfl⟩ : syracuseStep 2148353 = 1611265) B1611265
theorem B1132559 : Blo 754331 1132559 := bstep (se 1 (by rfl) ⟨849419, by rfl⟩ : syracuseStep 1132559 = 1698839) B1698839
theorem B1918991 : Blo 754331 1918991 := bstep (se 1 (by rfl) ⟨1439243, by rfl⟩ : syracuseStep 1918991 = 2878487) B2878487
theorem B1132601 : Blo 754331 1132601 := bstep (se 2 (by rfl) ⟨424725, by rfl⟩ : syracuseStep 1132601 = 849451) B849451
theorem B1132679 : Blo 754331 1132679 := bstep (se 1 (by rfl) ⟨849509, by rfl⟩ : syracuseStep 1132679 = 1699019) B1699019
theorem B1919123 : Blo 754331 1919123 := bstep (se 1 (by rfl) ⟨1439342, by rfl⟩ : syracuseStep 1919123 = 2878685) B2878685
theorem B1132715 : Blo 754331 1132715 := bstep (se 1 (by rfl) ⟨849536, by rfl⟩ : syracuseStep 1132715 = 1699073) B1699073
theorem B1132745 : Blo 754331 1132745 := bstep (se 2 (by rfl) ⟨424779, by rfl⟩ : syracuseStep 1132745 = 849559) B849559
theorem B1132859 : Blo 754331 1132859 := bstep (se 1 (by rfl) ⟨849644, by rfl⟩ : syracuseStep 1132859 = 1699289) B1699289
theorem B1132919 : Blo 754331 1132919 := bstep (se 1 (by rfl) ⟨849689, by rfl⟩ : syracuseStep 1132919 = 1699379) B1699379
theorem B1132943 : Blo 754331 1132943 := bstep (se 1 (by rfl) ⟨849707, by rfl⟩ : syracuseStep 1132943 = 1699415) B1699415
theorem B1132985 : Blo 754331 1132985 := bstep (se 2 (by rfl) ⟨424869, by rfl⟩ : syracuseStep 1132985 = 849739) B849739
theorem B1133063 : Blo 754331 1133063 := bstep (se 1 (by rfl) ⟨849797, by rfl⟩ : syracuseStep 1133063 = 1699595) B1699595
theorem B1821217 : Blo 754331 1821217 := bstep (se 2 (by rfl) ⟨682956, by rfl⟩ : syracuseStep 1821217 = 1365913) B1365913
theorem B1133099 : Blo 754331 1133099 := bstep (se 1 (by rfl) ⟨849824, by rfl⟩ : syracuseStep 1133099 = 1699649) B1699649
theorem B1133129 : Blo 754331 1133129 := bstep (se 2 (by rfl) ⟨424923, by rfl⟩ : syracuseStep 1133129 = 849847) B849847
theorem B1297015 : Blo 754331 1297015 := bstep (se 1 (by rfl) ⟨972761, by rfl⟩ : syracuseStep 1297015 = 1945523) B1945523
theorem B1133243 : Blo 754331 1133243 := bstep (se 1 (by rfl) ⟨849932, by rfl⟩ : syracuseStep 1133243 = 1699865) B1699865
theorem B1133303 : Blo 754331 1133303 := bstep (se 1 (by rfl) ⟨849977, by rfl⟩ : syracuseStep 1133303 = 1699955) B1699955
theorem B1133327 : Blo 754331 1133327 := bstep (se 1 (by rfl) ⟨849995, by rfl⟩ : syracuseStep 1133327 = 1699991) B1699991
theorem B1133369 : Blo 754331 1133369 := bstep (se 2 (by rfl) ⟨425013, by rfl⟩ : syracuseStep 1133369 = 850027) B850027
theorem B1133447 : Blo 754331 1133447 := bstep (se 1 (by rfl) ⟨850085, by rfl⟩ : syracuseStep 1133447 = 1700171) B1700171
theorem B5753753 : Blo 754331 5753753 := bstep (se 2 (by rfl) ⟨2157657, by rfl⟩ : syracuseStep 5753753 = 4315315) B4315315
theorem B1133483 : Blo 754331 1133483 := bstep (se 1 (by rfl) ⟨850112, by rfl⟩ : syracuseStep 1133483 = 1700225) B1700225
theorem B1133513 : Blo 754331 1133513 := bstep (se 2 (by rfl) ⟨425067, by rfl⟩ : syracuseStep 1133513 = 850135) B850135
theorem B2870225 : Blo 754331 2870225 := bstep (se 2 (by rfl) ⟨1076334, by rfl⟩ : syracuseStep 2870225 = 2152669) B2152669
theorem B1133627 : Blo 754331 1133627 := bstep (se 1 (by rfl) ⟨850220, by rfl⟩ : syracuseStep 1133627 = 1700441) B1700441
theorem B1133687 : Blo 754331 1133687 := bstep (se 1 (by rfl) ⟨850265, by rfl⟩ : syracuseStep 1133687 = 1700531) B1700531
theorem B1133711 : Blo 754331 1133711 := bstep (se 1 (by rfl) ⟨850283, by rfl⟩ : syracuseStep 1133711 = 1700567) B1700567
theorem B1133753 : Blo 754331 1133753 := bstep (se 2 (by rfl) ⟨425157, by rfl⟩ : syracuseStep 1133753 = 850315) B850315
theorem B1166537 : Blo 754331 1166537 := bstep (se 2 (by rfl) ⟨437451, by rfl⟩ : syracuseStep 1166537 = 874903) B874903
theorem B1133831 : Blo 754331 1133831 := bstep (se 1 (by rfl) ⟨850373, by rfl⟩ : syracuseStep 1133831 = 1700747) B1700747
theorem B1133867 : Blo 754331 1133867 := bstep (se 1 (by rfl) ⟨850400, by rfl⟩ : syracuseStep 1133867 = 1700801) B1700801
theorem B1133897 : Blo 754331 1133897 := bstep (se 2 (by rfl) ⟨425211, by rfl⟩ : syracuseStep 1133897 = 850423) B850423
theorem B1134011 : Blo 754331 1134011 := bstep (se 1 (by rfl) ⟨850508, by rfl⟩ : syracuseStep 1134011 = 1701017) B1701017
theorem B1134071 : Blo 754331 1134071 := bstep (se 1 (by rfl) ⟨850553, by rfl⟩ : syracuseStep 1134071 = 1701107) B1701107
theorem B1134095 : Blo 754331 1134095 := bstep (se 1 (by rfl) ⟨850571, by rfl⟩ : syracuseStep 1134095 = 1701143) B1701143
theorem B1134137 : Blo 754331 1134137 := bstep (se 2 (by rfl) ⟨425301, by rfl⟩ : syracuseStep 1134137 = 850603) B850603
theorem B2150003 : Blo 754331 2150003 := bstep (se 1 (by rfl) ⟨1612502, by rfl⟩ : syracuseStep 2150003 = 3225005) B3225005
theorem B1134215 : Blo 754331 1134215 := bstep (se 1 (by rfl) ⟨850661, by rfl⟩ : syracuseStep 1134215 = 1701323) B1701323
theorem B1134251 : Blo 754331 1134251 := bstep (se 1 (by rfl) ⟨850688, by rfl⟩ : syracuseStep 1134251 = 1701377) B1701377
theorem B1134281 : Blo 754331 1134281 := bstep (se 2 (by rfl) ⟨425355, by rfl⟩ : syracuseStep 1134281 = 850711) B850711
theorem B6475571 : Blo 754331 6475571 := bstep (se 1 (by rfl) ⟨4856678, by rfl⟩ : syracuseStep 6475571 = 9713357) B9713357
theorem B1134395 : Blo 754331 1134395 := bstep (se 1 (by rfl) ⟨850796, by rfl⟩ : syracuseStep 1134395 = 1701593) B1701593
theorem B1134455 : Blo 754331 1134455 := bstep (se 1 (by rfl) ⟨850841, by rfl⟩ : syracuseStep 1134455 = 1701683) B1701683
theorem B1134479 : Blo 754331 1134479 := bstep (se 1 (by rfl) ⟨850859, by rfl⟩ : syracuseStep 1134479 = 1701719) B1701719
theorem B1134521 : Blo 754331 1134521 := bstep (se 2 (by rfl) ⟨425445, by rfl⟩ : syracuseStep 1134521 = 850891) B850891
theorem B1134599 : Blo 754331 1134599 := bstep (se 1 (by rfl) ⟨850949, by rfl⟩ : syracuseStep 1134599 = 1701899) B1701899
theorem B3821579 : Blo 754331 3821579 := bstep (se 1 (by rfl) ⟨2866184, by rfl⟩ : syracuseStep 3821579 = 5732369) B5732369
theorem B1134635 : Blo 754331 1134635 := bstep (se 1 (by rfl) ⟨850976, by rfl⟩ : syracuseStep 1134635 = 1701953) B1701953
theorem B2150459 : Blo 754331 2150459 := bstep (se 1 (by rfl) ⟨1612844, by rfl⟩ : syracuseStep 2150459 = 3225689) B3225689
theorem B1134665 : Blo 754331 1134665 := bstep (se 2 (by rfl) ⟨425499, by rfl⟩ : syracuseStep 1134665 = 850999) B850999
theorem B3821741 : Blo 754331 3821741 := bstep (se 3 (by rfl) ⟨716576, by rfl⟩ : syracuseStep 3821741 = 1433153) B1433153
theorem B6475949 : Blo 754331 6475949 := bstep (se 3 (by rfl) ⟨1214240, by rfl⟩ : syracuseStep 6475949 = 2428481) B2428481
theorem B1134779 : Blo 754331 1134779 := bstep (se 1 (by rfl) ⟨851084, by rfl⟩ : syracuseStep 1134779 = 1702169) B1702169
theorem B1134839 : Blo 754331 1134839 := bstep (se 1 (by rfl) ⟨851129, by rfl⟩ : syracuseStep 1134839 = 1702259) B1702259
theorem B1134863 : Blo 754331 1134863 := bstep (se 1 (by rfl) ⟨851147, by rfl⟩ : syracuseStep 1134863 = 1702295) B1702295
theorem B3625249 : Blo 754331 3625249 := bstep (se 2 (by rfl) ⟨1359468, by rfl⟩ : syracuseStep 3625249 = 2718937) B2718937
theorem B1134905 : Blo 754331 1134905 := bstep (se 2 (by rfl) ⟨425589, by rfl⟩ : syracuseStep 1134905 = 851179) B851179
theorem B1134983 : Blo 754331 1134983 := bstep (se 1 (by rfl) ⟨851237, by rfl⟩ : syracuseStep 1134983 = 1702475) B1702475
theorem B1135019 : Blo 754331 1135019 := bstep (se 1 (by rfl) ⟨851264, by rfl⟩ : syracuseStep 1135019 = 1702529) B1702529
theorem B1135049 : Blo 754331 1135049 := bstep (se 2 (by rfl) ⟨425643, by rfl⟩ : syracuseStep 1135049 = 851287) B851287
theorem B1135163 : Blo 754331 1135163 := bstep (se 1 (by rfl) ⟨851372, by rfl⟩ : syracuseStep 1135163 = 1702745) B1702745
theorem B2871895 : Blo 754331 2871895 := bstep (se 1 (by rfl) ⟨2153921, by rfl⟩ : syracuseStep 2871895 = 4307843) B4307843
theorem B1135223 : Blo 754331 1135223 := bstep (se 1 (by rfl) ⟨851417, by rfl⟩ : syracuseStep 1135223 = 1702835) B1702835
theorem B1135247 : Blo 754331 1135247 := bstep (se 1 (by rfl) ⟨851435, by rfl⟩ : syracuseStep 1135247 = 1702871) B1702871
theorem B1135289 : Blo 754331 1135289 := bstep (se 2 (by rfl) ⟨425733, by rfl⟩ : syracuseStep 1135289 = 851467) B851467
theorem B4313857 : Blo 754331 4313857 := bstep (se 2 (by rfl) ⟨1617696, by rfl⟩ : syracuseStep 4313857 = 3235393) B3235393
theorem B1135367 : Blo 754331 1135367 := bstep (se 1 (by rfl) ⟨851525, by rfl⟩ : syracuseStep 1135367 = 1703051) B1703051
theorem B2151211 : Blo 754331 2151211 := bstep (se 1 (by rfl) ⟨1613408, by rfl⟩ : syracuseStep 2151211 = 3226817) B3226817
theorem B1135403 : Blo 754331 1135403 := bstep (se 1 (by rfl) ⟨851552, by rfl⟩ : syracuseStep 1135403 = 1703105) B1703105
theorem B5755697 : Blo 754331 5755697 := bstep (se 2 (by rfl) ⟨2158386, by rfl⟩ : syracuseStep 5755697 = 4316773) B4316773
theorem B1135433 : Blo 754331 1135433 := bstep (se 2 (by rfl) ⟨425787, by rfl⟩ : syracuseStep 1135433 = 851575) B851575
theorem B2872199 : Blo 754331 2872199 := bstep (se 1 (by rfl) ⟨2154149, by rfl⟩ : syracuseStep 2872199 = 4308299) B4308299
theorem B1135547 : Blo 754331 1135547 := bstep (se 1 (by rfl) ⟨851660, by rfl⟩ : syracuseStep 1135547 = 1703321) B1703321
theorem B1135607 : Blo 754331 1135607 := bstep (se 1 (by rfl) ⟨851705, by rfl⟩ : syracuseStep 1135607 = 1703411) B1703411
theorem B807943 : Blo 754331 807943 := bstep (se 1 (by rfl) ⟨605957, by rfl⟩ : syracuseStep 807943 = 1211915) B1211915
theorem B1135631 : Blo 754331 1135631 := bstep (se 1 (by rfl) ⟨851723, by rfl⟩ : syracuseStep 1135631 = 1703447) B1703447
theorem B1135673 : Blo 754331 1135673 := bstep (se 2 (by rfl) ⟨425877, by rfl⟩ : syracuseStep 1135673 = 851755) B851755
theorem B2151485 : Blo 754331 2151485 := bstep (se 3 (by rfl) ⟨403403, by rfl⟩ : syracuseStep 2151485 = 806807) B806807
theorem B2872381 : Blo 754331 2872381 := bstep (se 3 (by rfl) ⟨538571, by rfl⟩ : syracuseStep 2872381 = 1077143) B1077143
theorem B1135751 : Blo 754331 1135751 := bstep (se 1 (by rfl) ⟨851813, by rfl⟩ : syracuseStep 1135751 = 1703627) B1703627
theorem B1135787 : Blo 754331 1135787 := bstep (se 1 (by rfl) ⟨851840, by rfl⟩ : syracuseStep 1135787 = 1703681) B1703681
theorem B4084937 : Blo 754331 4084937 := bstep (se 2 (by rfl) ⟨1531851, by rfl⟩ : syracuseStep 4084937 = 3063703) B3063703
theorem B1135817 : Blo 754331 1135817 := bstep (se 2 (by rfl) ⟨425931, by rfl⟩ : syracuseStep 1135817 = 851863) B851863
theorem B6444269 : Blo 754331 6444269 := bstep (se 3 (by rfl) ⟨1208300, by rfl⟩ : syracuseStep 6444269 = 2416601) B2416601
theorem B4314383 : Blo 754331 4314383 := bstep (se 1 (by rfl) ⟨3235787, by rfl⟩ : syracuseStep 4314383 = 6471575) B6471575
theorem B1135931 : Blo 754331 1135931 := bstep (se 1 (by rfl) ⟨851948, by rfl⟩ : syracuseStep 1135931 = 1703897) B1703897
theorem B3888499 : Blo 754331 3888499 := bstep (se 1 (by rfl) ⟨2916374, by rfl⟩ : syracuseStep 3888499 = 5832749) B5832749
theorem B1135991 : Blo 754331 1135991 := bstep (se 1 (by rfl) ⟨851993, by rfl⟩ : syracuseStep 1135991 = 1703987) B1703987
theorem B23287175 : Blo 754331 23287175 := bstep (se 1 (by rfl) ⟨17465381, by rfl⟩ : syracuseStep 23287175 = 34930763) B34930763
theorem B972167 : Blo 754331 972167 := bstep (se 1 (by rfl) ⟨729125, by rfl⟩ : syracuseStep 972167 = 1458251) B1458251
theorem B1136015 : Blo 754331 1136015 := bstep (se 1 (by rfl) ⟨852011, by rfl⟩ : syracuseStep 1136015 = 1704023) B1704023
theorem B4904339 : Blo 754331 4904339 := bstep (se 1 (by rfl) ⟨3678254, by rfl⟩ : syracuseStep 4904339 = 7356509) B7356509
theorem B1136057 : Blo 754331 1136057 := bstep (se 2 (by rfl) ⟨426021, by rfl⟩ : syracuseStep 1136057 = 852043) B852043
theorem B1136135 : Blo 754331 1136135 := bstep (se 1 (by rfl) ⟨852101, by rfl⟩ : syracuseStep 1136135 = 1704203) B1704203
theorem B4609565 : Blo 754331 4609565 := bstep (se 3 (by rfl) ⟨864293, by rfl⟩ : syracuseStep 4609565 = 1728587) B1728587
theorem B1136171 : Blo 754331 1136171 := bstep (se 1 (by rfl) ⟨852128, by rfl⟩ : syracuseStep 1136171 = 1704257) B1704257
theorem B1037881 : Blo 754331 1037881 := bstep (se 2 (by rfl) ⟨389205, by rfl⟩ : syracuseStep 1037881 = 778411) B778411
theorem B1136201 : Blo 754331 1136201 := bstep (se 2 (by rfl) ⟨426075, by rfl⟩ : syracuseStep 1136201 = 852151) B852151
theorem B1136315 : Blo 754331 1136315 := bstep (se 1 (by rfl) ⟨852236, by rfl⟩ : syracuseStep 1136315 = 1704473) B1704473
theorem B1136375 : Blo 754331 1136375 := bstep (se 1 (by rfl) ⟨852281, by rfl⟩ : syracuseStep 1136375 = 1704563) B1704563
theorem B3823361 : Blo 754331 3823361 := bstep (se 2 (by rfl) ⟨1433760, by rfl⟩ : syracuseStep 3823361 = 2867521) B2867521
theorem B1136399 : Blo 754331 1136399 := bstep (se 1 (by rfl) ⟨852299, by rfl⟩ : syracuseStep 1136399 = 1704599) B1704599
theorem B1136441 : Blo 754331 1136441 := bstep (se 2 (by rfl) ⟨426165, by rfl⟩ : syracuseStep 1136441 = 852331) B852331
theorem B808763 : Blo 754331 808763 := bstep (se 1 (by rfl) ⟨606572, by rfl⟩ : syracuseStep 808763 = 1213145) B1213145
theorem B2152327 : Blo 754331 2152327 := bstep (se 1 (by rfl) ⟨1614245, by rfl⟩ : syracuseStep 2152327 = 3228491) B3228491
theorem B1136519 : Blo 754331 1136519 := bstep (se 1 (by rfl) ⟨852389, by rfl⟩ : syracuseStep 1136519 = 1704779) B1704779
theorem B6444953 : Blo 754331 6444953 := bstep (se 2 (by rfl) ⟨2416857, by rfl⟩ : syracuseStep 6444953 = 4833715) B4833715
theorem B1136555 : Blo 754331 1136555 := bstep (se 1 (by rfl) ⟨852416, by rfl⟩ : syracuseStep 1136555 = 1704833) B1704833
theorem B1136585 : Blo 754331 1136585 := bstep (se 2 (by rfl) ⟨426219, by rfl⟩ : syracuseStep 1136585 = 852439) B852439
theorem B1136699 : Blo 754331 1136699 := bstep (se 1 (by rfl) ⟨852524, by rfl⟩ : syracuseStep 1136699 = 1705049) B1705049
theorem B1136759 : Blo 754331 1136759 := bstep (se 1 (by rfl) ⟨852569, by rfl⟩ : syracuseStep 1136759 = 1705139) B1705139
theorem B1136783 : Blo 754331 1136783 := bstep (se 1 (by rfl) ⟨852587, by rfl⟩ : syracuseStep 1136783 = 1705175) B1705175
theorem B2152601 : Blo 754331 2152601 := bstep (se 2 (by rfl) ⟨807225, by rfl⟩ : syracuseStep 2152601 = 1614451) B1614451
theorem B1136825 : Blo 754331 1136825 := bstep (se 2 (by rfl) ⟨426309, by rfl⟩ : syracuseStep 1136825 = 852619) B852619
theorem B1136903 : Blo 754331 1136903 := bstep (se 1 (by rfl) ⟨852677, by rfl⟩ : syracuseStep 1136903 = 1705355) B1705355
theorem B1136939 : Blo 754331 1136939 := bstep (se 1 (by rfl) ⟨852704, by rfl⟩ : syracuseStep 1136939 = 1705409) B1705409
theorem B1136969 : Blo 754331 1136969 := bstep (se 2 (by rfl) ⟨426363, by rfl⟩ : syracuseStep 1136969 = 852727) B852727
theorem B3234163 : Blo 754331 3234163 := bstep (se 1 (by rfl) ⟨2425622, by rfl⟩ : syracuseStep 3234163 = 4851245) B4851245
theorem B1137083 : Blo 754331 1137083 := bstep (se 1 (by rfl) ⟨852812, by rfl⟩ : syracuseStep 1137083 = 1705625) B1705625
theorem B1137143 : Blo 754331 1137143 := bstep (se 1 (by rfl) ⟨852857, by rfl⟩ : syracuseStep 1137143 = 1705715) B1705715
theorem B1137167 : Blo 754331 1137167 := bstep (se 1 (by rfl) ⟨852875, by rfl⟩ : syracuseStep 1137167 = 1705751) B1705751
theorem B3824171 : Blo 754331 3824171 := bstep (se 1 (by rfl) ⟨2868128, by rfl⟩ : syracuseStep 3824171 = 5736257) B5736257
theorem B1137209 : Blo 754331 1137209 := bstep (se 2 (by rfl) ⟨426453, by rfl⟩ : syracuseStep 1137209 = 852907) B852907
theorem B2906711 : Blo 754331 2906711 := bstep (se 1 (by rfl) ⟨2180033, by rfl⟩ : syracuseStep 2906711 = 4360067) B4360067
theorem B1137287 : Blo 754331 1137287 := bstep (se 1 (by rfl) ⟨852965, by rfl⟩ : syracuseStep 1137287 = 1705931) B1705931
theorem B1137323 : Blo 754331 1137323 := bstep (se 1 (by rfl) ⟨852992, by rfl⟩ : syracuseStep 1137323 = 1705985) B1705985
theorem B4315841 : Blo 754331 4315841 := bstep (se 2 (by rfl) ⟨1618440, by rfl⟩ : syracuseStep 4315841 = 3236881) B3236881
theorem B3234505 : Blo 754331 3234505 := bstep (se 2 (by rfl) ⟨1212939, by rfl⟩ : syracuseStep 3234505 = 2425879) B2425879
theorem B1137353 : Blo 754331 1137353 := bstep (se 2 (by rfl) ⟨426507, by rfl⟩ : syracuseStep 1137353 = 853015) B853015
theorem B2874113 : Blo 754331 2874113 := bstep (se 2 (by rfl) ⟨1077792, by rfl⟩ : syracuseStep 2874113 = 2155585) B2155585
theorem B3267343 : Blo 754331 3267343 := bstep (se 1 (by rfl) ⟨2450507, by rfl⟩ : syracuseStep 3267343 = 4901015) B4901015
theorem B1432379 : Blo 754331 1432379 := bstep (se 1 (by rfl) ⟨1074284, by rfl⟩ : syracuseStep 1432379 = 2148569) B2148569
theorem B1137467 : Blo 754331 1137467 := bstep (se 1 (by rfl) ⟨853100, by rfl⟩ : syracuseStep 1137467 = 1706201) B1706201
theorem B2546585 : Blo 754331 2546585 := bstep (se 2 (by rfl) ⟨954969, by rfl⟩ : syracuseStep 2546585 = 1909939) B1909939
theorem B1727531 : Blo 754331 1727531 := bstep (se 1 (by rfl) ⟨1295648, by rfl⟩ : syracuseStep 1727531 = 2591297) B2591297
theorem B2153729 : Blo 754331 2153729 := bstep (se 2 (by rfl) ⟨807648, by rfl⟩ : syracuseStep 2153729 = 1615297) B1615297
theorem B1432865 : Blo 754331 1432865 := bstep (se 2 (by rfl) ⟨537324, by rfl⟩ : syracuseStep 1432865 = 1074649) B1074649
theorem B2547287 : Blo 754331 2547287 := bstep (se 1 (by rfl) ⟨1910465, by rfl⟩ : syracuseStep 2547287 = 3820931) B3820931
theorem B1433207 : Blo 754331 1433207 := bstep (se 1 (by rfl) ⟨1074905, by rfl⟩ : syracuseStep 1433207 = 2149811) B2149811
theorem B2154185 : Blo 754331 2154185 := bstep (se 2 (by rfl) ⟨807819, by rfl⟩ : syracuseStep 2154185 = 1615639) B1615639
theorem B3235565 : Blo 754331 3235565 := bstep (se 3 (by rfl) ⟨606668, by rfl⟩ : syracuseStep 3235565 = 1213337) B1213337
theorem B3825467 : Blo 754331 3825467 := bstep (se 1 (by rfl) ⟨2869100, by rfl⟩ : syracuseStep 3825467 = 5738201) B5738201
theorem B2875283 : Blo 754331 2875283 := bstep (se 1 (by rfl) ⟨2156462, by rfl⟩ : syracuseStep 2875283 = 4312925) B4312925
theorem B3825629 : Blo 754331 3825629 := bstep (se 3 (by rfl) ⟨717305, by rfl⟩ : syracuseStep 3825629 = 1434611) B1434611
theorem B2547773 : Blo 754331 2547773 := bstep (se 3 (by rfl) ⟨477707, by rfl⟩ : syracuseStep 2547773 = 955415) B955415
theorem B1532039 : Blo 754331 1532039 := bstep (se 1 (by rfl) ⟨1149029, by rfl⟩ : syracuseStep 1532039 = 2298059) B2298059
theorem B3825953 : Blo 754331 3825953 := bstep (se 2 (by rfl) ⟨1434732, by rfl⟩ : syracuseStep 3825953 = 2869465) B2869465
theorem B2875783 : Blo 754331 2875783 := bstep (se 1 (by rfl) ⟨2156837, by rfl⟩ : syracuseStep 2875783 = 4313675) B4313675
theorem B18407897 : Blo 754331 18407897 := bstep (se 2 (by rfl) ⟨6902961, by rfl⟩ : syracuseStep 18407897 = 13805923) B13805923
theorem B6644227 : Blo 754331 6644227 := bstep (se 1 (by rfl) ⟨4983170, by rfl⟩ : syracuseStep 6644227 = 9966341) B9966341
theorem B1729171 : Blo 754331 1729171 := bstep (se 1 (by rfl) ⟨1296878, by rfl⟩ : syracuseStep 1729171 = 2593757) B2593757
theorem B7267333 : Blo 754331 7267333 := bstep (se 4 (by rfl) ⟨681312, by rfl⟩ : syracuseStep 7267333 = 1362625) B1362625
theorem B4318231 : Blo 754331 4318231 := bstep (se 1 (by rfl) ⟨3238673, by rfl⟩ : syracuseStep 4318231 = 6477347) B6477347
theorem B1434809 : Blo 754331 1434809 := bstep (se 2 (by rfl) ⟨538053, by rfl⟩ : syracuseStep 1434809 = 1076107) B1076107
theorem B3826925 : Blo 754331 3826925 := bstep (se 3 (by rfl) ⟨717548, by rfl⟩ : syracuseStep 3826925 = 1435097) B1435097
theorem B7267643 : Blo 754331 7267643 := bstep (se 1 (by rfl) ⟨5450732, by rfl⟩ : syracuseStep 7267643 = 10901465) B10901465
theorem B2155835 : Blo 754331 2155835 := bstep (se 1 (by rfl) ⟨1616876, by rfl⟩ : syracuseStep 2155835 = 3233753) B3233753
theorem B30991733 : Blo 754331 30991733 := bstep (se 5 (by rfl) ⟨1452737, by rfl⟩ : syracuseStep 30991733 = 2905475) B2905475
theorem B2549177 : Blo 754331 2549177 := bstep (se 2 (by rfl) ⟨955941, by rfl⟩ : syracuseStep 2549177 = 1911883) B1911883
theorem B6448643 : Blo 754331 6448643 := bstep (se 1 (by rfl) ⟨4836482, by rfl⟩ : syracuseStep 6448643 = 9672965) B9672965
theorem B1435151 : Blo 754331 1435151 := bstep (se 1 (by rfl) ⟨1076363, by rfl⟩ : syracuseStep 1435151 = 2152727) B2152727
theorem B5826077 : Blo 754331 5826077 := bstep (se 3 (by rfl) ⟨1092389, by rfl⟩ : syracuseStep 5826077 = 2184779) B2184779
theorem B1533473 : Blo 754331 1533473 := bstep (se 2 (by rfl) ⟨575052, by rfl⟩ : syracuseStep 1533473 = 1150105) B1150105
theorem B1697399 : Blo 754331 1697399 := bstep (se 1 (by rfl) ⟨1273049, by rfl⟩ : syracuseStep 1697399 = 2546099) B2546099
theorem B1697579 : Blo 754331 1697579 := bstep (se 1 (by rfl) ⟨1273184, by rfl⟩ : syracuseStep 1697579 = 2546369) B2546369
theorem B3630899 : Blo 754331 3630899 := bstep (se 1 (by rfl) ⟨2723174, by rfl⟩ : syracuseStep 3630899 = 5446349) B5446349
theorem B2156473 : Blo 754331 2156473 := bstep (se 2 (by rfl) ⟨808677, by rfl⟩ : syracuseStep 2156473 = 1617355) B1617355
theorem B1075207 : Blo 754331 1075207 := bstep (se 1 (by rfl) ⟨806405, by rfl⟩ : syracuseStep 1075207 = 1612811) B1612811
theorem B2549771 : Blo 754331 2549771 := bstep (se 1 (by rfl) ⟨1912328, by rfl⟩ : syracuseStep 2549771 = 3824657) B3824657
theorem B3827735 : Blo 754331 3827735 := bstep (se 1 (by rfl) ⟨2870801, by rfl⟩ : syracuseStep 3827735 = 5741603) B5741603
theorem B3106883 : Blo 754331 3106883 := bstep (se 1 (by rfl) ⟨2330162, by rfl⟩ : syracuseStep 3106883 = 4660325) B4660325
theorem B2549879 : Blo 754331 2549879 := bstep (se 1 (by rfl) ⟨1912409, by rfl⟩ : syracuseStep 2549879 = 3824819) B3824819
theorem B1697939 : Blo 754331 1697939 := bstep (se 1 (by rfl) ⟨1273454, by rfl⟩ : syracuseStep 1697939 = 2546909) B2546909
theorem B1697993 : Blo 754331 1697993 := bstep (se 2 (by rfl) ⟨636747, by rfl⟩ : syracuseStep 1697993 = 1273495) B1273495
theorem B2418959 : Blo 754331 2418959 := bstep (se 1 (by rfl) ⟨1814219, by rfl⟩ : syracuseStep 2418959 = 3628439) B3628439
theorem B1435963 : Blo 754331 1435963 := bstep (se 1 (by rfl) ⟨1076972, by rfl⟩ : syracuseStep 1435963 = 2153945) B2153945
theorem B2156861 : Blo 754331 2156861 := bstep (se 3 (by rfl) ⟨404411, by rfl⟩ : syracuseStep 2156861 = 808823) B808823
theorem B1436039 : Blo 754331 1436039 := bstep (se 1 (by rfl) ⟨1077029, by rfl⟩ : syracuseStep 1436039 = 2154059) B2154059
theorem B1075771 : Blo 754331 1075771 := bstep (se 1 (by rfl) ⟨806828, by rfl⟩ : syracuseStep 1075771 = 1613657) B1613657
theorem B2550473 : Blo 754331 2550473 := bstep (se 2 (by rfl) ⟨956427, by rfl⟩ : syracuseStep 2550473 = 1912855) B1912855
theorem B1436449 : Blo 754331 1436449 := bstep (se 2 (by rfl) ⟨538668, by rfl⟩ : syracuseStep 1436449 = 1077337) B1077337
theorem B8711027 : Blo 754331 8711027 := bstep (se 1 (by rfl) ⟨6533270, by rfl⟩ : syracuseStep 8711027 = 13066541) B13066541
theorem B1698695 : Blo 754331 1698695 := bstep (se 1 (by rfl) ⟨1274021, by rfl⟩ : syracuseStep 1698695 = 2548043) B2548043
theorem B1698875 : Blo 754331 1698875 := bstep (se 1 (by rfl) ⟨1274156, by rfl⟩ : syracuseStep 1698875 = 2548313) B2548313
theorem B5893181 : Blo 754331 5893181 := bstep (se 3 (by rfl) ⟨1104971, by rfl⟩ : syracuseStep 5893181 = 2209943) B2209943
theorem B1436791 : Blo 754331 1436791 := bstep (se 1 (by rfl) ⟨1077593, by rfl⟩ : syracuseStep 1436791 = 2155187) B2155187
theorem B5729453 : Blo 754331 5729453 := bstep (se 3 (by rfl) ⟨1074272, by rfl⟩ : syracuseStep 5729453 = 2148545) B2148545
theorem B1699001 : Blo 754331 1699001 := bstep (se 2 (by rfl) ⟨637125, by rfl⟩ : syracuseStep 1699001 = 1274251) B1274251
theorem B2551175 : Blo 754331 2551175 := bstep (se 1 (by rfl) ⟨1913381, by rfl⟩ : syracuseStep 2551175 = 3826763) B3826763
theorem B2157977 : Blo 754331 2157977 := bstep (se 2 (by rfl) ⟨809241, by rfl⟩ : syracuseStep 2157977 = 1618483) B1618483
theorem B1076665 : Blo 754331 1076665 := bstep (se 2 (by rfl) ⟨403749, by rfl⟩ : syracuseStep 1076665 = 807499) B807499
theorem B2911697 : Blo 754331 2911697 := bstep (se 2 (by rfl) ⟨1091886, by rfl⟩ : syracuseStep 2911697 = 2183773) B2183773
theorem B1699343 : Blo 754331 1699343 := bstep (se 1 (by rfl) ⟨1274507, by rfl⟩ : syracuseStep 1699343 = 2549015) B2549015
theorem B1699361 : Blo 754331 1699361 := bstep (se 2 (by rfl) ⟨637260, by rfl⟩ : syracuseStep 1699361 = 1274521) B1274521
theorem B1273387 : Blo 754331 1273387 := bstep (se 1 (by rfl) ⟨955040, by rfl⟩ : syracuseStep 1273387 = 1910081) B1910081
theorem B1273529 : Blo 754331 1273529 := bstep (se 2 (by rfl) ⟨477573, by rfl⟩ : syracuseStep 1273529 = 955147) B955147
theorem B2551553 : Blo 754331 2551553 := bstep (se 2 (by rfl) ⟨956832, by rfl⟩ : syracuseStep 2551553 = 1913665) B1913665
theorem B4091681 : Blo 754331 4091681 := bstep (se 2 (by rfl) ⟨1534380, by rfl⟩ : syracuseStep 4091681 = 3068761) B3068761
theorem B8285989 : Blo 754331 8285989 := bstep (se 4 (by rfl) ⟨776811, by rfl⟩ : syracuseStep 8285989 = 1553623) B1553623
theorem B7270181 : Blo 754331 7270181 := bstep (se 4 (by rfl) ⟨681579, by rfl⟩ : syracuseStep 7270181 = 1363159) B1363159
theorem B1699703 : Blo 754331 1699703 := bstep (se 1 (by rfl) ⟨1274777, by rfl⟩ : syracuseStep 1699703 = 2549555) B2549555
theorem B4190231 : Blo 754331 4190231 := bstep (se 1 (by rfl) ⟨3142673, by rfl⟩ : syracuseStep 4190231 = 6285347) B6285347
theorem B1699883 : Blo 754331 1699883 := bstep (se 1 (by rfl) ⟨1274912, by rfl⟩ : syracuseStep 1699883 = 2549825) B2549825
theorem B2912375 : Blo 754331 2912375 := bstep (se 1 (by rfl) ⟨2184281, by rfl⟩ : syracuseStep 2912375 = 4368563) B4368563
theorem B8188037 : Blo 754331 8188037 := bstep (se 4 (by rfl) ⟨767628, by rfl⟩ : syracuseStep 8188037 = 1535257) B1535257
theorem B3633497 : Blo 754331 3633497 := bstep (se 2 (by rfl) ⟨1362561, by rfl⟩ : syracuseStep 3633497 = 2725123) B2725123
theorem B1274231 : Blo 754331 1274231 := bstep (se 1 (by rfl) ⟨955673, by rfl⟩ : syracuseStep 1274231 = 1911347) B1911347
theorem B1208711 : Blo 754331 1208711 := bstep (se 1 (by rfl) ⟨906533, by rfl⟩ : syracuseStep 1208711 = 1813067) B1813067
theorem B1700243 : Blo 754331 1700243 := bstep (se 1 (by rfl) ⟨1275182, by rfl⟩ : syracuseStep 1700243 = 2550365) B2550365
theorem B1700297 : Blo 754331 1700297 := bstep (se 2 (by rfl) ⟨637611, by rfl⟩ : syracuseStep 1700297 = 1275223) B1275223
theorem B2552363 : Blo 754331 2552363 := bstep (se 1 (by rfl) ⟨1914272, by rfl⟩ : syracuseStep 2552363 = 3828545) B3828545
theorem B1077895 : Blo 754331 1077895 := bstep (se 1 (by rfl) ⟨808421, by rfl⟩ : syracuseStep 1077895 = 1616843) B1616843
theorem B1438393 : Blo 754331 1438393 := bstep (se 2 (by rfl) ⟨539397, by rfl⟩ : syracuseStep 1438393 = 1078795) B1078795
theorem B2945807 : Blo 754331 2945807 := bstep (se 1 (by rfl) ⟨2209355, by rfl⟩ : syracuseStep 2945807 = 4418711) B4418711
theorem B2159389 : Blo 754331 2159389 := bstep (se 3 (by rfl) ⟨404885, by rfl⟩ : syracuseStep 2159389 = 809771) B809771
theorem B1274683 : Blo 754331 1274683 := bstep (se 1 (by rfl) ⟨956012, by rfl⟩ : syracuseStep 1274683 = 1912025) B1912025
theorem B1274825 : Blo 754331 1274825 := bstep (se 2 (by rfl) ⟨478059, by rfl⟩ : syracuseStep 1274825 = 956119) B956119
theorem B848911 : Blo 754331 848911 := bstep (se 1 (by rfl) ⟨636683, by rfl⟩ : syracuseStep 848911 = 1273367) B1273367
theorem B1438735 : Blo 754331 1438735 := bstep (se 1 (by rfl) ⟨1079051, by rfl⟩ : syracuseStep 1438735 = 2158103) B2158103
theorem B3830813 : Blo 754331 3830813 := bstep (se 3 (by rfl) ⟨718277, by rfl⟩ : syracuseStep 3830813 = 1436555) B1436555
theorem B1700999 : Blo 754331 1700999 := bstep (se 1 (by rfl) ⟨1275749, by rfl⟩ : syracuseStep 1700999 = 2551499) B2551499
theorem B1209659 : Blo 754331 1209659 := bstep (se 1 (by rfl) ⟨907244, by rfl⟩ : syracuseStep 1209659 = 1814489) B1814489
theorem B1701179 : Blo 754331 1701179 := bstep (se 1 (by rfl) ⟨1275884, by rfl⟩ : syracuseStep 1701179 = 2551769) B2551769
theorem B1078601 : Blo 754331 1078601 := bstep (se 2 (by rfl) ⟨404475, by rfl⟩ : syracuseStep 1078601 = 808951) B808951
theorem B2422163 : Blo 754331 2422163 := bstep (se 1 (by rfl) ⟨1816622, by rfl⟩ : syracuseStep 2422163 = 3633245) B3633245
theorem B1701305 : Blo 754331 1701305 := bstep (se 2 (by rfl) ⟨637989, by rfl⟩ : syracuseStep 1701305 = 1275979) B1275979
theorem B1078715 : Blo 754331 1078715 := bstep (se 1 (by rfl) ⟨809036, by rfl⟩ : syracuseStep 1078715 = 1618073) B1618073
theorem B3831299 : Blo 754331 3831299 := bstep (se 1 (by rfl) ⟨2873474, by rfl⟩ : syracuseStep 3831299 = 5746949) B5746949
theorem B849415 : Blo 754331 849415 := bstep (se 1 (by rfl) ⟨637061, by rfl⟩ : syracuseStep 849415 = 1274123) B1274123
theorem B5731883 : Blo 754331 5731883 := bstep (se 1 (by rfl) ⟨4298912, by rfl⟩ : syracuseStep 5731883 = 8597825) B8597825
theorem B1275527 : Blo 754331 1275527 := bstep (se 1 (by rfl) ⟨956645, by rfl⟩ : syracuseStep 1275527 = 1913291) B1913291
theorem B849595 : Blo 754331 849595 := bstep (se 1 (by rfl) ⟨637196, by rfl⟩ : syracuseStep 849595 = 1274393) B1274393
theorem B6125327 : Blo 754331 6125327 := bstep (se 1 (by rfl) ⟨4593995, by rfl⟩ : syracuseStep 6125327 = 9187991) B9187991
theorem B1701647 : Blo 754331 1701647 := bstep (se 1 (by rfl) ⟨1276235, by rfl⟩ : syracuseStep 1701647 = 2552471) B2552471
theorem B1701665 : Blo 754331 1701665 := bstep (se 2 (by rfl) ⟨638124, by rfl⟩ : syracuseStep 1701665 = 1276249) B1276249
theorem B2553659 : Blo 754331 2553659 := bstep (se 1 (by rfl) ⟨1915244, by rfl⟩ : syracuseStep 2553659 = 3830489) B3830489
theorem B1439623 : Blo 754331 1439623 := bstep (se 1 (by rfl) ⟨1079717, by rfl⟩ : syracuseStep 1439623 = 2159435) B2159435
theorem B1079353 : Blo 754331 1079353 := bstep (se 2 (by rfl) ⟨404757, by rfl⟩ : syracuseStep 1079353 = 809515) B809515
theorem B1964119 : Blo 754331 1964119 := bstep (se 1 (by rfl) ⟨1473089, by rfl⟩ : syracuseStep 1964119 = 2946179) B2946179
theorem B1702007 : Blo 754331 1702007 := bstep (se 1 (by rfl) ⟨1276505, by rfl⟩ : syracuseStep 1702007 = 2553011) B2553011
theorem B850063 : Blo 754331 850063 := bstep (se 1 (by rfl) ⟨637547, by rfl⟩ : syracuseStep 850063 = 1275095) B1275095
theorem B1276175 : Blo 754331 1276175 := bstep (se 1 (by rfl) ⟨957131, by rfl⟩ : syracuseStep 1276175 = 1914263) B1914263
theorem B24574225 : Blo 754331 24574225 := bstep (se 2 (by rfl) ⟨9215334, by rfl⟩ : syracuseStep 24574225 = 18430669) B18430669
theorem B2554145 : Blo 754331 2554145 := bstep (se 2 (by rfl) ⟨957804, by rfl⟩ : syracuseStep 2554145 = 1915609) B1915609
theorem B1702187 : Blo 754331 1702187 := bstep (se 1 (by rfl) ⟨1276640, by rfl⟩ : syracuseStep 1702187 = 2553281) B2553281
theorem B850567 : Blo 754331 850567 := bstep (se 1 (by rfl) ⟨637925, by rfl⟩ : syracuseStep 850567 = 1275851) B1275851
theorem B1702547 : Blo 754331 1702547 := bstep (se 1 (by rfl) ⟨1276910, by rfl⟩ : syracuseStep 1702547 = 2553821) B2553821
theorem B1702601 : Blo 754331 1702601 := bstep (se 2 (by rfl) ⟨638475, by rfl⟩ : syracuseStep 1702601 = 1276951) B1276951
theorem B1276715 : Blo 754331 1276715 := bstep (se 1 (by rfl) ⟨957536, by rfl⟩ : syracuseStep 1276715 = 1915073) B1915073
theorem B850747 : Blo 754331 850747 := bstep (se 1 (by rfl) ⟨638060, by rfl⟩ : syracuseStep 850747 = 1276121) B1276121
theorem B8616779 : Blo 754331 8616779 := bstep (se 1 (by rfl) ⟨6462584, by rfl⟩ : syracuseStep 8616779 = 12925169) B12925169
theorem B2554739 : Blo 754331 2554739 := bstep (se 1 (by rfl) ⟨1916054, by rfl⟩ : syracuseStep 2554739 = 3832109) B3832109
theorem B2915389 : Blo 754331 2915389 := bstep (se 3 (by rfl) ⟨546635, by rfl⟩ : syracuseStep 2915389 = 1093271) B1093271
theorem B10910807 : Blo 754331 10910807 := bstep (se 1 (by rfl) ⟨8183105, by rfl⟩ : syracuseStep 10910807 = 16366211) B16366211
theorem B3832919 : Blo 754331 3832919 := bstep (se 1 (by rfl) ⟨2874689, by rfl⟩ : syracuseStep 3832919 = 5749379) B5749379
theorem B1277113 : Blo 754331 1277113 := bstep (se 2 (by rfl) ⟨478917, by rfl⟩ : syracuseStep 1277113 = 957835) B957835
theorem B851215 : Blo 754331 851215 := bstep (se 1 (by rfl) ⟨638411, by rfl⟩ : syracuseStep 851215 = 1276823) B1276823
theorem B1703303 : Blo 754331 1703303 := bstep (se 1 (by rfl) ⟨1277477, by rfl⟩ : syracuseStep 1703303 = 2554955) B2554955
theorem B2588051 : Blo 754331 2588051 := bstep (se 1 (by rfl) ⟨1941038, by rfl⟩ : syracuseStep 2588051 = 3882077) B3882077
theorem B1703483 : Blo 754331 1703483 := bstep (se 1 (by rfl) ⟨1277612, by rfl⟩ : syracuseStep 1703483 = 2555225) B2555225
theorem B3833405 : Blo 754331 3833405 := bstep (se 3 (by rfl) ⟨718763, by rfl⟩ : syracuseStep 3833405 = 1437527) B1437527
theorem B1703609 : Blo 754331 1703609 := bstep (se 2 (by rfl) ⟨638853, by rfl⟩ : syracuseStep 1703609 = 1277707) B1277707
theorem B851719 : Blo 754331 851719 := bstep (se 1 (by rfl) ⟨638789, by rfl⟩ : syracuseStep 851719 = 1277579) B1277579
theorem B1277815 : Blo 754331 1277815 := bstep (se 1 (by rfl) ⟨958361, by rfl⟩ : syracuseStep 1277815 = 1916723) B1916723
theorem B851899 : Blo 754331 851899 := bstep (se 1 (by rfl) ⟨638924, by rfl⟩ : syracuseStep 851899 = 1277849) B1277849
theorem B8192015 : Blo 754331 8192015 := bstep (se 1 (by rfl) ⟨6144011, by rfl⟩ : syracuseStep 8192015 = 12288023) B12288023
theorem B852007 : Blo 754331 852007 := bstep (se 1 (by rfl) ⟨639005, by rfl⟩ : syracuseStep 852007 = 1278011) B1278011
theorem B1278031 : Blo 754331 1278031 := bstep (se 1 (by rfl) ⟨958523, by rfl⟩ : syracuseStep 1278031 = 1917047) B1917047
theorem B2425099 : Blo 754331 2425099 := bstep (se 1 (by rfl) ⟨1818824, by rfl⟩ : syracuseStep 2425099 = 3637649) B3637649
theorem B1278281 : Blo 754331 1278281 := bstep (se 2 (by rfl) ⟨479355, by rfl⟩ : syracuseStep 1278281 = 958711) B958711
theorem B3834377 : Blo 754331 3834377 := bstep (se 2 (by rfl) ⟨1437891, by rfl⟩ : syracuseStep 3834377 = 2875783) B2875783
theorem B1704545 : Blo 754331 1704545 := bstep (se 2 (by rfl) ⟨639204, by rfl⟩ : syracuseStep 1704545 = 1278409) B1278409
theorem B754351 : Blo 754331 754351 := bstep (se 1 (by rfl) ⟨565763, by rfl⟩ : syracuseStep 754351 = 1131527) B1131527
theorem B754375 : Blo 754331 754375 := bstep (se 1 (by rfl) ⟨565781, by rfl⟩ : syracuseStep 754375 = 1131563) B1131563
theorem B754395 : Blo 754331 754395 := bstep (se 1 (by rfl) ⟨565796, by rfl⟩ : syracuseStep 754395 = 1131593) B1131593
theorem B1278713 : Blo 754331 1278713 := bstep (se 2 (by rfl) ⟨479517, by rfl⟩ : syracuseStep 1278713 = 959035) B959035
theorem B754471 : Blo 754331 754471 := bstep (se 1 (by rfl) ⟨565853, by rfl⟩ : syracuseStep 754471 = 1131707) B1131707
theorem B754511 : Blo 754331 754511 := bstep (se 1 (by rfl) ⟨565883, by rfl⟩ : syracuseStep 754511 = 1131767) B1131767
theorem B754527 : Blo 754331 754527 := bstep (se 1 (by rfl) ⟨565895, by rfl⟩ : syracuseStep 754527 = 1131791) B1131791
theorem B2556791 : Blo 754331 2556791 := bstep (se 1 (by rfl) ⟨1917593, by rfl⟩ : syracuseStep 2556791 = 3835187) B3835187
theorem B754555 : Blo 754331 754555 := bstep (se 1 (by rfl) ⟨565916, by rfl⟩ : syracuseStep 754555 = 1131833) B1131833
theorem B5833619 : Blo 754331 5833619 := bstep (se 1 (by rfl) ⟨4375214, by rfl⟩ : syracuseStep 5833619 = 8750429) B8750429
theorem B754607 : Blo 754331 754607 := bstep (se 1 (by rfl) ⟨565955, by rfl⟩ : syracuseStep 754607 = 1131911) B1131911
theorem B1278895 : Blo 754331 1278895 := bstep (se 1 (by rfl) ⟨959171, by rfl⟩ : syracuseStep 1278895 = 1918343) B1918343
theorem B1704887 : Blo 754331 1704887 := bstep (se 1 (by rfl) ⟨1278665, by rfl⟩ : syracuseStep 1704887 = 2557331) B2557331
theorem B754631 : Blo 754331 754631 := bstep (se 1 (by rfl) ⟨565973, by rfl⟩ : syracuseStep 754631 = 1131947) B1131947
theorem B754651 : Blo 754331 754651 := bstep (se 1 (by rfl) ⟨565988, by rfl⟩ : syracuseStep 754651 = 1131977) B1131977
theorem B1278983 : Blo 754331 1278983 := bstep (se 1 (by rfl) ⟨959237, by rfl⟩ : syracuseStep 1278983 = 1918475) B1918475
theorem B2720783 : Blo 754331 2720783 := bstep (se 1 (by rfl) ⟨2040587, by rfl⟩ : syracuseStep 2720783 = 4081175) B4081175
theorem B754727 : Blo 754331 754727 := bstep (se 1 (by rfl) ⟨566045, by rfl⟩ : syracuseStep 754727 = 1132091) B1132091
theorem B9667633 : Blo 754331 9667633 := bstep (se 2 (by rfl) ⟨3625362, by rfl⟩ : syracuseStep 9667633 = 7250725) B7250725
theorem B754767 : Blo 754331 754767 := bstep (se 1 (by rfl) ⟨566075, by rfl⟩ : syracuseStep 754767 = 1132151) B1132151
theorem B2557007 : Blo 754331 2557007 := bstep (se 1 (by rfl) ⟨1917755, by rfl⟩ : syracuseStep 2557007 = 3835511) B3835511
theorem B754783 : Blo 754331 754783 := bstep (se 1 (by rfl) ⟨566087, by rfl⟩ : syracuseStep 754783 = 1132175) B1132175
theorem B754811 : Blo 754331 754811 := bstep (se 1 (by rfl) ⟨566108, by rfl⟩ : syracuseStep 754811 = 1132217) B1132217
theorem B754863 : Blo 754331 754863 := bstep (se 1 (by rfl) ⟨566147, by rfl⟩ : syracuseStep 754863 = 1132295) B1132295
theorem B754887 : Blo 754331 754887 := bstep (se 1 (by rfl) ⟨566165, by rfl⟩ : syracuseStep 754887 = 1132331) B1132331
theorem B754907 : Blo 754331 754907 := bstep (se 1 (by rfl) ⟨566180, by rfl⟩ : syracuseStep 754907 = 1132361) B1132361
theorem B754983 : Blo 754331 754983 := bstep (se 1 (by rfl) ⟨566237, by rfl⟩ : syracuseStep 754983 = 1132475) B1132475
theorem B755023 : Blo 754331 755023 := bstep (se 1 (by rfl) ⟨566267, by rfl⟩ : syracuseStep 755023 = 1132535) B1132535
theorem B755039 : Blo 754331 755039 := bstep (se 1 (by rfl) ⟨566279, by rfl⟩ : syracuseStep 755039 = 1132559) B1132559
theorem B1279327 : Blo 754331 1279327 := bstep (se 1 (by rfl) ⟨959495, by rfl⟩ : syracuseStep 1279327 = 1918991) B1918991
theorem B755067 : Blo 754331 755067 := bstep (se 1 (by rfl) ⟨566300, by rfl⟩ : syracuseStep 755067 = 1132601) B1132601
theorem B755119 : Blo 754331 755119 := bstep (se 1 (by rfl) ⟨566339, by rfl⟩ : syracuseStep 755119 = 1132679) B1132679
theorem B1279415 : Blo 754331 1279415 := bstep (se 1 (by rfl) ⟨959561, by rfl⟩ : syracuseStep 1279415 = 1919123) B1919123
theorem B755143 : Blo 754331 755143 := bstep (se 1 (by rfl) ⟨566357, by rfl⟩ : syracuseStep 755143 = 1132715) B1132715
theorem B2557385 : Blo 754331 2557385 := bstep (se 2 (by rfl) ⟨959019, by rfl⟩ : syracuseStep 2557385 = 1918039) B1918039
theorem B755163 : Blo 754331 755163 := bstep (se 1 (by rfl) ⟨566372, by rfl⟩ : syracuseStep 755163 = 1132745) B1132745
theorem B1705481 : Blo 754331 1705481 := bstep (se 2 (by rfl) ⟨639555, by rfl⟩ : syracuseStep 1705481 = 1279111) B1279111
theorem B755239 : Blo 754331 755239 := bstep (se 1 (by rfl) ⟨566429, by rfl⟩ : syracuseStep 755239 = 1132859) B1132859
theorem B755279 : Blo 754331 755279 := bstep (se 1 (by rfl) ⟨566459, by rfl⟩ : syracuseStep 755279 = 1132919) B1132919
theorem B755295 : Blo 754331 755295 := bstep (se 1 (by rfl) ⟨566471, by rfl⟩ : syracuseStep 755295 = 1132943) B1132943
theorem B5178977 : Blo 754331 5178977 := bstep (se 2 (by rfl) ⟨1942116, by rfl⟩ : syracuseStep 5178977 = 3884233) B3884233
theorem B755323 : Blo 754331 755323 := bstep (se 1 (by rfl) ⟨566492, by rfl⟩ : syracuseStep 755323 = 1132985) B1132985
theorem B755375 : Blo 754331 755375 := bstep (se 1 (by rfl) ⟨566531, by rfl⟩ : syracuseStep 755375 = 1133063) B1133063
theorem B755399 : Blo 754331 755399 := bstep (se 1 (by rfl) ⟨566549, by rfl⟩ : syracuseStep 755399 = 1133099) B1133099
theorem B2557655 : Blo 754331 2557655 := bstep (se 1 (by rfl) ⟨1918241, by rfl⟩ : syracuseStep 2557655 = 3836483) B3836483
theorem B755419 : Blo 754331 755419 := bstep (se 1 (by rfl) ⟨566564, by rfl⟩ : syracuseStep 755419 = 1133129) B1133129
theorem B755495 : Blo 754331 755495 := bstep (se 1 (by rfl) ⟨566621, by rfl⟩ : syracuseStep 755495 = 1133243) B1133243
theorem B7276331 : Blo 754331 7276331 := bstep (se 1 (by rfl) ⟨5457248, by rfl⟩ : syracuseStep 7276331 = 10914497) B10914497
theorem B755535 : Blo 754331 755535 := bstep (se 1 (by rfl) ⟨566651, by rfl⟩ : syracuseStep 755535 = 1133303) B1133303
theorem B755551 : Blo 754331 755551 := bstep (se 1 (by rfl) ⟨566663, by rfl⟩ : syracuseStep 755551 = 1133327) B1133327
theorem B1705823 : Blo 754331 1705823 := bstep (se 1 (by rfl) ⟨1279367, by rfl⟩ : syracuseStep 1705823 = 2558735) B2558735
theorem B755579 : Blo 754331 755579 := bstep (se 1 (by rfl) ⟨566684, by rfl⟩ : syracuseStep 755579 = 1133369) B1133369
theorem B26150809 : Blo 754331 26150809 := bstep (se 2 (by rfl) ⟨9806553, by rfl⟩ : syracuseStep 26150809 = 19613107) B19613107
theorem B755631 : Blo 754331 755631 := bstep (se 1 (by rfl) ⟨566723, by rfl⟩ : syracuseStep 755631 = 1133447) B1133447
theorem B2557871 : Blo 754331 2557871 := bstep (se 1 (by rfl) ⟨1918403, by rfl⟩ : syracuseStep 2557871 = 3836807) B3836807
theorem B3835835 : Blo 754331 3835835 := bstep (se 1 (by rfl) ⟨2876876, by rfl⟩ : syracuseStep 3835835 = 5753753) B5753753
theorem B755655 : Blo 754331 755655 := bstep (se 1 (by rfl) ⟨566741, by rfl⟩ : syracuseStep 755655 = 1133483) B1133483
theorem B755675 : Blo 754331 755675 := bstep (se 1 (by rfl) ⟨566756, by rfl⟩ : syracuseStep 755675 = 1133513) B1133513
theorem B1706003 : Blo 754331 1706003 := bstep (se 1 (by rfl) ⟨1279502, by rfl⟩ : syracuseStep 1706003 = 2559005) B2559005
theorem B755751 : Blo 754331 755751 := bstep (se 1 (by rfl) ⟨566813, by rfl⟩ : syracuseStep 755751 = 1133627) B1133627
theorem B755791 : Blo 754331 755791 := bstep (se 1 (by rfl) ⟨566843, by rfl⟩ : syracuseStep 755791 = 1133687) B1133687
theorem B755807 : Blo 754331 755807 := bstep (se 1 (by rfl) ⟨566855, by rfl⟩ : syracuseStep 755807 = 1133711) B1133711
theorem B755835 : Blo 754331 755835 := bstep (se 1 (by rfl) ⟨566876, by rfl⟩ : syracuseStep 755835 = 1133753) B1133753
theorem B755887 : Blo 754331 755887 := bstep (se 1 (by rfl) ⟨566915, by rfl⟩ : syracuseStep 755887 = 1133831) B1133831
theorem B755911 : Blo 754331 755911 := bstep (se 1 (by rfl) ⟨566933, by rfl⟩ : syracuseStep 755911 = 1133867) B1133867
theorem B755931 : Blo 754331 755931 := bstep (se 1 (by rfl) ⟨566948, by rfl⟩ : syracuseStep 755931 = 1133897) B1133897
theorem B756007 : Blo 754331 756007 := bstep (se 1 (by rfl) ⟨567005, by rfl⟩ : syracuseStep 756007 = 1134011) B1134011
theorem B756047 : Blo 754331 756047 := bstep (se 1 (by rfl) ⟨567035, by rfl⟩ : syracuseStep 756047 = 1134071) B1134071
theorem B756063 : Blo 754331 756063 := bstep (se 1 (by rfl) ⟨567047, by rfl⟩ : syracuseStep 756063 = 1134095) B1134095
theorem B9668969 : Blo 754331 9668969 := bstep (se 2 (by rfl) ⟨3625863, by rfl⟩ : syracuseStep 9668969 = 7251727) B7251727
theorem B756091 : Blo 754331 756091 := bstep (se 1 (by rfl) ⟨567068, by rfl⟩ : syracuseStep 756091 = 1134137) B1134137
theorem B756143 : Blo 754331 756143 := bstep (se 1 (by rfl) ⟨567107, by rfl⟩ : syracuseStep 756143 = 1134215) B1134215
theorem B756167 : Blo 754331 756167 := bstep (se 1 (by rfl) ⟨567125, by rfl⟩ : syracuseStep 756167 = 1134251) B1134251
theorem B756187 : Blo 754331 756187 := bstep (se 1 (by rfl) ⟨567140, by rfl⟩ : syracuseStep 756187 = 1134281) B1134281
theorem B756263 : Blo 754331 756263 := bstep (se 1 (by rfl) ⟨567197, by rfl⟩ : syracuseStep 756263 = 1134395) B1134395
theorem B756303 : Blo 754331 756303 := bstep (se 1 (by rfl) ⟨567227, by rfl⟩ : syracuseStep 756303 = 1134455) B1134455
theorem B756319 : Blo 754331 756319 := bstep (se 1 (by rfl) ⟨567239, by rfl⟩ : syracuseStep 756319 = 1134479) B1134479
theorem B756347 : Blo 754331 756347 := bstep (se 1 (by rfl) ⟨567260, by rfl⟩ : syracuseStep 756347 = 1134521) B1134521
theorem B756399 : Blo 754331 756399 := bstep (se 1 (by rfl) ⟨567299, by rfl⟩ : syracuseStep 756399 = 1134599) B1134599
theorem B756423 : Blo 754331 756423 := bstep (se 1 (by rfl) ⟨567317, by rfl⟩ : syracuseStep 756423 = 1134635) B1134635
theorem B756443 : Blo 754331 756443 := bstep (se 1 (by rfl) ⟨567332, by rfl⟩ : syracuseStep 756443 = 1134665) B1134665
theorem B756519 : Blo 754331 756519 := bstep (se 1 (by rfl) ⟨567389, by rfl⟩ : syracuseStep 756519 = 1134779) B1134779
theorem B756559 : Blo 754331 756559 := bstep (se 1 (by rfl) ⟨567419, by rfl⟩ : syracuseStep 756559 = 1134839) B1134839
theorem B756575 : Blo 754331 756575 := bstep (se 1 (by rfl) ⟨567431, by rfl⟩ : syracuseStep 756575 = 1134863) B1134863
theorem B756603 : Blo 754331 756603 := bstep (se 1 (by rfl) ⟨567452, by rfl⟩ : syracuseStep 756603 = 1134905) B1134905
theorem B756655 : Blo 754331 756655 := bstep (se 1 (by rfl) ⟨567491, by rfl⟩ : syracuseStep 756655 = 1134983) B1134983
theorem B756679 : Blo 754331 756679 := bstep (se 1 (by rfl) ⟨567509, by rfl⟩ : syracuseStep 756679 = 1135019) B1135019
theorem B756699 : Blo 754331 756699 := bstep (se 1 (by rfl) ⟨567524, by rfl⟩ : syracuseStep 756699 = 1135049) B1135049
theorem B756775 : Blo 754331 756775 := bstep (se 1 (by rfl) ⟨567581, by rfl⟩ : syracuseStep 756775 = 1135163) B1135163
theorem B756815 : Blo 754331 756815 := bstep (se 1 (by rfl) ⟨567611, by rfl⟩ : syracuseStep 756815 = 1135223) B1135223
theorem B756831 : Blo 754331 756831 := bstep (se 1 (by rfl) ⟨567623, by rfl⟩ : syracuseStep 756831 = 1135247) B1135247
theorem B756859 : Blo 754331 756859 := bstep (se 1 (by rfl) ⟨567644, by rfl⟩ : syracuseStep 756859 = 1135289) B1135289
theorem B756911 : Blo 754331 756911 := bstep (se 1 (by rfl) ⟨567683, by rfl⟩ : syracuseStep 756911 = 1135367) B1135367
theorem B756935 : Blo 754331 756935 := bstep (se 1 (by rfl) ⟨567701, by rfl⟩ : syracuseStep 756935 = 1135403) B1135403
theorem B3837131 : Blo 754331 3837131 := bstep (se 1 (by rfl) ⟨2877848, by rfl⟩ : syracuseStep 3837131 = 5755697) B5755697
theorem B756955 : Blo 754331 756955 := bstep (se 1 (by rfl) ⟨567716, by rfl⟩ : syracuseStep 756955 = 1135433) B1135433
theorem B6917413 : Blo 754331 6917413 := bstep (se 4 (by rfl) ⟨648507, by rfl⟩ : syracuseStep 6917413 = 1297015) B1297015
theorem B757031 : Blo 754331 757031 := bstep (se 1 (by rfl) ⟨567773, by rfl⟩ : syracuseStep 757031 = 1135547) B1135547
theorem B757071 : Blo 754331 757071 := bstep (se 1 (by rfl) ⟨567803, by rfl⟩ : syracuseStep 757071 = 1135607) B1135607
theorem B757087 : Blo 754331 757087 := bstep (se 1 (by rfl) ⟨567815, by rfl⟩ : syracuseStep 757087 = 1135631) B1135631
theorem B757115 : Blo 754331 757115 := bstep (se 1 (by rfl) ⟨567836, by rfl⟩ : syracuseStep 757115 = 1135673) B1135673
theorem B2428289 : Blo 754331 2428289 := bstep (se 2 (by rfl) ⟨910608, by rfl⟩ : syracuseStep 2428289 = 1821217) B1821217
theorem B757167 : Blo 754331 757167 := bstep (se 1 (by rfl) ⟨567875, by rfl⟩ : syracuseStep 757167 = 1135751) B1135751
theorem B757191 : Blo 754331 757191 := bstep (se 1 (by rfl) ⟨567893, by rfl⟩ : syracuseStep 757191 = 1135787) B1135787
theorem B2723291 : Blo 754331 2723291 := bstep (se 1 (by rfl) ⟨2042468, by rfl⟩ : syracuseStep 2723291 = 4084937) B4084937
theorem B757211 : Blo 754331 757211 := bstep (se 1 (by rfl) ⟨567908, by rfl⟩ : syracuseStep 757211 = 1135817) B1135817
theorem B4296179 : Blo 754331 4296179 := bstep (se 1 (by rfl) ⟨3222134, by rfl⟩ : syracuseStep 4296179 = 6444269) B6444269
theorem B9702899 : Blo 754331 9702899 := bstep (se 1 (by rfl) ⟨7277174, by rfl⟩ : syracuseStep 9702899 = 14554349) B14554349
theorem B757287 : Blo 754331 757287 := bstep (se 1 (by rfl) ⟨567965, by rfl⟩ : syracuseStep 757287 = 1135931) B1135931
theorem B757327 : Blo 754331 757327 := bstep (se 1 (by rfl) ⟨567995, by rfl⟩ : syracuseStep 757327 = 1135991) B1135991
theorem B757343 : Blo 754331 757343 := bstep (se 1 (by rfl) ⟨568007, by rfl⟩ : syracuseStep 757343 = 1136015) B1136015
theorem B757371 : Blo 754331 757371 := bstep (se 1 (by rfl) ⟨568028, by rfl⟩ : syracuseStep 757371 = 1136057) B1136057
theorem B12258955 : Blo 754331 12258955 := bstep (se 1 (by rfl) ⟨9194216, by rfl⟩ : syracuseStep 12258955 = 18388433) B18388433
theorem B757423 : Blo 754331 757423 := bstep (se 1 (by rfl) ⟨568067, by rfl⟩ : syracuseStep 757423 = 1136135) B1136135
theorem B2592445 : Blo 754331 2592445 := bstep (se 3 (by rfl) ⟨486083, by rfl⟩ : syracuseStep 2592445 = 972167) B972167
theorem B757447 : Blo 754331 757447 := bstep (se 1 (by rfl) ⟨568085, by rfl⟩ : syracuseStep 757447 = 1136171) B1136171
theorem B757467 : Blo 754331 757467 := bstep (se 1 (by rfl) ⟨568100, by rfl⟩ : syracuseStep 757467 = 1136201) B1136201
theorem B6459101 : Blo 754331 6459101 := bstep (se 3 (by rfl) ⟨1211081, by rfl⟩ : syracuseStep 6459101 = 2422163) B2422163
theorem B757543 : Blo 754331 757543 := bstep (se 1 (by rfl) ⟨568157, by rfl⟩ : syracuseStep 757543 = 1136315) B1136315
theorem B757583 : Blo 754331 757583 := bstep (se 1 (by rfl) ⟨568187, by rfl⟩ : syracuseStep 757583 = 1136375) B1136375
theorem B757599 : Blo 754331 757599 := bstep (se 1 (by rfl) ⟨568199, by rfl⟩ : syracuseStep 757599 = 1136399) B1136399
theorem B757627 : Blo 754331 757627 := bstep (se 1 (by rfl) ⟨568220, by rfl⟩ : syracuseStep 757627 = 1136441) B1136441
theorem B757679 : Blo 754331 757679 := bstep (se 1 (by rfl) ⟨568259, by rfl⟩ : syracuseStep 757679 = 1136519) B1136519
theorem B4296635 : Blo 754331 4296635 := bstep (se 1 (by rfl) ⟨3222476, by rfl⟩ : syracuseStep 4296635 = 6444953) B6444953
theorem B757703 : Blo 754331 757703 := bstep (se 1 (by rfl) ⟨568277, by rfl⟩ : syracuseStep 757703 = 1136555) B1136555
theorem B757723 : Blo 754331 757723 := bstep (se 1 (by rfl) ⟨568292, by rfl⟩ : syracuseStep 757723 = 1136585) B1136585
theorem B757799 : Blo 754331 757799 := bstep (se 1 (by rfl) ⟨568349, by rfl⟩ : syracuseStep 757799 = 1136699) B1136699
theorem B757839 : Blo 754331 757839 := bstep (se 1 (by rfl) ⟨568379, by rfl⟩ : syracuseStep 757839 = 1136759) B1136759
theorem B757855 : Blo 754331 757855 := bstep (se 1 (by rfl) ⟨568391, by rfl⟩ : syracuseStep 757855 = 1136783) B1136783
theorem B11800691 : Blo 754331 11800691 := bstep (se 1 (by rfl) ⟨8850518, by rfl⟩ : syracuseStep 11800691 = 17701037) B17701037
theorem B757883 : Blo 754331 757883 := bstep (se 1 (by rfl) ⟨568412, by rfl⟩ : syracuseStep 757883 = 1136825) B1136825
theorem B757935 : Blo 754331 757935 := bstep (se 1 (by rfl) ⟨568451, by rfl⟩ : syracuseStep 757935 = 1136903) B1136903
theorem B757959 : Blo 754331 757959 := bstep (se 1 (by rfl) ⟨568469, by rfl⟩ : syracuseStep 757959 = 1136939) B1136939
theorem B757979 : Blo 754331 757979 := bstep (se 1 (by rfl) ⟨568484, by rfl⟩ : syracuseStep 757979 = 1136969) B1136969
theorem B758055 : Blo 754331 758055 := bstep (se 1 (by rfl) ⟨568541, by rfl⟩ : syracuseStep 758055 = 1137083) B1137083
theorem B758095 : Blo 754331 758095 := bstep (se 1 (by rfl) ⟨568571, by rfl⟩ : syracuseStep 758095 = 1137143) B1137143
theorem B758111 : Blo 754331 758111 := bstep (se 1 (by rfl) ⟨568583, by rfl⟩ : syracuseStep 758111 = 1137167) B1137167
theorem B3641705 : Blo 754331 3641705 := bstep (se 2 (by rfl) ⟨1365639, by rfl⟩ : syracuseStep 3641705 = 2731279) B2731279
theorem B758139 : Blo 754331 758139 := bstep (se 1 (by rfl) ⟨568604, by rfl⟩ : syracuseStep 758139 = 1137209) B1137209
theorem B1937807 : Blo 754331 1937807 := bstep (se 1 (by rfl) ⟨1453355, by rfl⟩ : syracuseStep 1937807 = 2906711) B2906711
theorem B758191 : Blo 754331 758191 := bstep (se 1 (by rfl) ⟨568643, by rfl⟩ : syracuseStep 758191 = 1137287) B1137287
theorem B758215 : Blo 754331 758215 := bstep (se 1 (by rfl) ⟨568661, by rfl⟩ : syracuseStep 758215 = 1137323) B1137323
theorem B758235 : Blo 754331 758235 := bstep (se 1 (by rfl) ⟨568676, by rfl⟩ : syracuseStep 758235 = 1137353) B1137353
theorem B954919 : Blo 754331 954919 := bstep (se 1 (by rfl) ⟨716189, by rfl⟩ : syracuseStep 954919 = 1432379) B1432379
theorem B758311 : Blo 754331 758311 := bstep (se 1 (by rfl) ⟨568733, by rfl⟩ : syracuseStep 758311 = 1137467) B1137467
theorem B1151687 : Blo 754331 1151687 := bstep (se 1 (by rfl) ⟨863765, by rfl⟩ : syracuseStep 1151687 = 1727531) B1727531
theorem B4133635 : Blo 754331 4133635 := bstep (se 1 (by rfl) ⟨3100226, by rfl⟩ : syracuseStep 4133635 = 6200453) B6200453
theorem B14521133 : Blo 754331 14521133 := bstep (se 3 (by rfl) ⟨2722712, by rfl⟩ : syracuseStep 14521133 = 5445425) B5445425
theorem B955243 : Blo 754331 955243 := bstep (se 1 (by rfl) ⟨716432, by rfl⟩ : syracuseStep 955243 = 1432865) B1432865
theorem B9180161 : Blo 754331 9180161 := bstep (se 2 (by rfl) ⟨3442560, by rfl⟩ : syracuseStep 9180161 = 6885121) B6885121
theorem B11047985 : Blo 754331 11047985 := bstep (se 2 (by rfl) ⟨4142994, by rfl⟩ : syracuseStep 11047985 = 8285989) B8285989
theorem B955471 : Blo 754331 955471 := bstep (se 1 (by rfl) ⟨716603, by rfl⟩ : syracuseStep 955471 = 1433207) B1433207
theorem B5445083 : Blo 754331 5445083 := bstep (se 1 (by rfl) ⟨4083812, by rfl⟩ : syracuseStep 5445083 = 8167625) B8167625
theorem B956539 : Blo 754331 956539 := bstep (se 1 (by rfl) ⟨717404, by rfl⟩ : syracuseStep 956539 = 1434809) B1434809
theorem B2726045 : Blo 754331 2726045 := bstep (se 3 (by rfl) ⟨511133, by rfl⟩ : syracuseStep 2726045 = 1022267) B1022267
theorem B3447101 : Blo 754331 3447101 := bstep (se 3 (by rfl) ⟨646331, by rfl⟩ : syracuseStep 3447101 = 1292663) B1292663
theorem B4299095 : Blo 754331 4299095 := bstep (se 1 (by rfl) ⟨3224321, by rfl⟩ : syracuseStep 4299095 = 6448643) B6448643
theorem B956767 : Blo 754331 956767 := bstep (se 1 (by rfl) ⟨717575, by rfl⟩ : syracuseStep 956767 = 1435151) B1435151
theorem B1022315 : Blo 754331 1022315 := bstep (se 1 (by rfl) ⟨766736, by rfl⟩ : syracuseStep 1022315 = 1533473) B1533473
theorem B2071255 : Blo 754331 2071255 := bstep (se 1 (by rfl) ⟨1553441, by rfl⟩ : syracuseStep 2071255 = 3106883) B3106883
theorem B1612639 : Blo 754331 1612639 := bstep (se 1 (by rfl) ⟨1209479, by rfl⟩ : syracuseStep 1612639 = 2418959) B2418959
theorem B957359 : Blo 754331 957359 := bstep (se 1 (by rfl) ⟨718019, by rfl⟩ : syracuseStep 957359 = 1436039) B1436039
theorem B4856759 : Blo 754331 4856759 := bstep (se 1 (by rfl) ⟨3642569, by rfl⟩ : syracuseStep 4856759 = 7285139) B7285139
theorem B5184665 : Blo 754331 5184665 := bstep (se 2 (by rfl) ⟨1944249, by rfl⟩ : syracuseStep 5184665 = 3888499) B3888499
theorem B5807351 : Blo 754331 5807351 := bstep (se 1 (by rfl) ⟨4355513, by rfl⟩ : syracuseStep 5807351 = 8711027) B8711027
theorem B1383841 : Blo 754331 1383841 := bstep (se 2 (by rfl) ⟨518940, by rfl⟩ : syracuseStep 1383841 = 1037881) B1037881
theorem B1941131 : Blo 754331 1941131 := bstep (se 1 (by rfl) ⟨1455848, by rfl⟩ : syracuseStep 1941131 = 2911697) B2911697
theorem B2793487 : Blo 754331 2793487 := bstep (se 1 (by rfl) ⟨2095115, by rfl⟩ : syracuseStep 2793487 = 4190231) B4190231
theorem B1941583 : Blo 754331 1941583 := bstep (se 1 (by rfl) ⟨1456187, by rfl⟩ : syracuseStep 1941583 = 2912375) B2912375
theorem B5448023 : Blo 754331 5448023 := bstep (se 1 (by rfl) ⟨4086017, by rfl⟩ : syracuseStep 5448023 = 8172035) B8172035
theorem B4858217 : Blo 754331 4858217 := bstep (se 2 (by rfl) ⟨1821831, by rfl⟩ : syracuseStep 4858217 = 3643663) B3643663
theorem B10364075 : Blo 754331 10364075 := bstep (se 1 (by rfl) ⟨7773056, by rfl⟩ : syracuseStep 10364075 = 15546113) B15546113
theorem B5744519 : Blo 754331 5744519 := bstep (se 1 (by rfl) ⟨4308389, by rfl⟩ : syracuseStep 5744519 = 8616779) B8616779
theorem B1451963 : Blo 754331 1451963 := bstep (se 1 (by rfl) ⟨1088972, by rfl⟩ : syracuseStep 1451963 = 2177945) B2177945
theorem B4728989 : Blo 754331 4728989 := bstep (se 3 (by rfl) ⟨886685, by rfl⟩ : syracuseStep 4728989 = 1773371) B1773371
theorem B2042491 : Blo 754331 2042491 := bstep (se 1 (by rfl) ⟨1531868, by rfl⟩ : syracuseStep 2042491 = 3063737) B3063737
theorem B5975005 : Blo 754331 5975005 := bstep (se 3 (by rfl) ⟨1120313, by rfl⟩ : syracuseStep 5975005 = 2240627) B2240627
theorem B6139151 : Blo 754331 6139151 := bstep (se 1 (by rfl) ⟨4604363, by rfl⟩ : syracuseStep 6139151 = 9208727) B9208727
theorem B8858969 : Blo 754331 8858969 := bstep (se 2 (by rfl) ⟨3322113, by rfl⟩ : syracuseStep 8858969 = 6644227) B6644227
theorem B1912207 : Blo 754331 1912207 := bstep (se 1 (by rfl) ⟨1434155, by rfl⟩ : syracuseStep 1912207 = 2868311) B2868311
theorem B1912531 : Blo 754331 1912531 := bstep (se 1 (by rfl) ⟨1434398, by rfl⟩ : syracuseStep 1912531 = 2868797) B2868797
theorem B2731769 : Blo 754331 2731769 := bstep (se 2 (by rfl) ⟨1024413, by rfl⟩ : syracuseStep 2731769 = 2048827) B2048827
theorem B9679115 : Blo 754331 9679115 := bstep (se 1 (by rfl) ⟨7259336, by rfl⟩ : syracuseStep 9679115 = 14518673) B14518673
theorem B1913483 : Blo 754331 1913483 := bstep (se 1 (by rfl) ⟨1435112, by rfl⟩ : syracuseStep 1913483 = 2870225) B2870225
theorem B29012741 : Blo 754331 29012741 := bstep (se 4 (by rfl) ⟨2719944, by rfl⟩ : syracuseStep 29012741 = 5439889) B5439889
theorem B3060575 : Blo 754331 3060575 := bstep (se 1 (by rfl) ⟨2295431, by rfl⟩ : syracuseStep 3060575 = 4590863) B4590863
theorem B10892353 : Blo 754331 10892353 := bstep (se 2 (by rfl) ⟨4084632, by rfl⟩ : syracuseStep 10892353 = 8169265) B8169265
theorem B4601441 : Blo 754331 4601441 := bstep (se 2 (by rfl) ⟨1725540, by rfl⟩ : syracuseStep 4601441 = 3451081) B3451081
theorem B15513281 : Blo 754331 15513281 := bstep (se 2 (by rfl) ⟨5817480, by rfl⟩ : syracuseStep 15513281 = 11634961) B11634961
theorem B1914617 : Blo 754331 1914617 := bstep (se 2 (by rfl) ⟨717981, by rfl⟩ : syracuseStep 1914617 = 1435963) B1435963
theorem B1914799 : Blo 754331 1914799 := bstep (se 1 (by rfl) ⟨1436099, by rfl⟩ : syracuseStep 1914799 = 2872199) B2872199
theorem B9222245 : Blo 754331 9222245 := bstep (se 4 (by rfl) ⟨864585, by rfl⟩ : syracuseStep 9222245 = 1729171) B1729171
theorem B3225757 : Blo 754331 3225757 := bstep (se 3 (by rfl) ⟨604829, by rfl⟩ : syracuseStep 3225757 = 1209659) B1209659
theorem B5748893 : Blo 754331 5748893 := bstep (se 3 (by rfl) ⟨1077917, by rfl⟩ : syracuseStep 5748893 = 2155835) B2155835
theorem B1915265 : Blo 754331 1915265 := bstep (se 2 (by rfl) ⟨718224, by rfl⟩ : syracuseStep 1915265 = 1436449) B1436449
theorem B1915721 : Blo 754331 1915721 := bstep (se 2 (by rfl) ⟨718395, by rfl⟩ : syracuseStep 1915721 = 1436791) B1436791
theorem B52312949 : Blo 754331 52312949 := bstep (se 5 (by rfl) ⟨2452169, by rfl⟩ : syracuseStep 52312949 = 4904339) B4904339
theorem B1916075 : Blo 754331 1916075 := bstep (se 1 (by rfl) ⟨1437056, by rfl⟩ : syracuseStep 1916075 = 2874113) B2874113
theorem B2866823 : Blo 754331 2866823 := bstep (se 1 (by rfl) ⟨2150117, by rfl⟩ : syracuseStep 2866823 = 4300235) B4300235
theorem B13811471 : Blo 754331 13811471 := bstep (se 1 (by rfl) ⟨10358603, by rfl⟩ : syracuseStep 13811471 = 20717207) B20717207
theorem B1916855 : Blo 754331 1916855 := bstep (se 1 (by rfl) ⟨1437641, by rfl⟩ : syracuseStep 1916855 = 2875283) B2875283
theorem B1294415 : Blo 754331 1294415 := bstep (se 1 (by rfl) ⟨970811, by rfl⟩ : syracuseStep 1294415 = 1941623) B1941623
theorem B12271931 : Blo 754331 12271931 := bstep (se 1 (by rfl) ⟨9203948, by rfl⟩ : syracuseStep 12271931 = 18407897) B18407897
theorem B4833665 : Blo 754331 4833665 := bstep (se 2 (by rfl) ⟨1812624, by rfl⟩ : syracuseStep 4833665 = 3625249) B3625249
theorem B1917857 : Blo 754331 1917857 := bstep (se 2 (by rfl) ⟨719196, by rfl⟩ : syracuseStep 1917857 = 1438393) B1438393
theorem B20661155 : Blo 754331 20661155 := bstep (se 1 (by rfl) ⟨15495866, by rfl⟩ : syracuseStep 20661155 = 30991733) B30991733
theorem B1295291 : Blo 754331 1295291 := bstep (se 1 (by rfl) ⟨971468, by rfl⟩ : syracuseStep 1295291 = 1942937) B1942937
theorem B5751809 : Blo 754331 5751809 := bstep (se 2 (by rfl) ⟨2156928, by rfl⟩ : syracuseStep 5751809 = 4313857) B4313857
theorem B3884051 : Blo 754331 3884051 := bstep (se 1 (by rfl) ⟨2913038, by rfl⟩ : syracuseStep 3884051 = 5826077) B5826077
theorem B2868281 : Blo 754331 2868281 := bstep (se 2 (by rfl) ⟨1075605, by rfl⟩ : syracuseStep 2868281 = 2151211) B2151211
theorem B1131599 : Blo 754331 1131599 := bstep (se 1 (by rfl) ⟨848699, by rfl⟩ : syracuseStep 1131599 = 1697399) B1697399
theorem B1131719 : Blo 754331 1131719 := bstep (se 1 (by rfl) ⟨848789, by rfl⟩ : syracuseStep 1131719 = 1697579) B1697579
theorem B1131881 : Blo 754331 1131881 := bstep (se 2 (by rfl) ⟨424455, by rfl⟩ : syracuseStep 1131881 = 848911) B848911
theorem B1918313 : Blo 754331 1918313 := bstep (se 2 (by rfl) ⟨719367, by rfl⟩ : syracuseStep 1918313 = 1438735) B1438735
theorem B1131959 : Blo 754331 1131959 := bstep (se 1 (by rfl) ⟨848969, by rfl⟩ : syracuseStep 1131959 = 1697939) B1697939
theorem B1131995 : Blo 754331 1131995 := bstep (se 1 (by rfl) ⟨848996, by rfl⟩ : syracuseStep 1131995 = 1697993) B1697993
theorem B2049725 : Blo 754331 2049725 := bstep (se 3 (by rfl) ⟨384323, by rfl⟩ : syracuseStep 2049725 = 768647) B768647
theorem B8308439 : Blo 754331 8308439 := bstep (se 1 (by rfl) ⟨6231329, by rfl⟩ : syracuseStep 8308439 = 12462659) B12462659
theorem B1132463 : Blo 754331 1132463 := bstep (se 1 (by rfl) ⟨849347, by rfl⟩ : syracuseStep 1132463 = 1698695) B1698695
theorem B1132553 : Blo 754331 1132553 := bstep (se 2 (by rfl) ⟨424707, by rfl⟩ : syracuseStep 1132553 = 849415) B849415
theorem B1132583 : Blo 754331 1132583 := bstep (se 1 (by rfl) ⟨849437, by rfl⟩ : syracuseStep 1132583 = 1698875) B1698875
theorem B3819635 : Blo 754331 3819635 := bstep (se 1 (by rfl) ⟨2864726, by rfl⟩ : syracuseStep 3819635 = 5729453) B5729453
theorem B1132667 : Blo 754331 1132667 := bstep (se 1 (by rfl) ⟨849500, by rfl⟩ : syracuseStep 1132667 = 1699001) B1699001
theorem B1132793 : Blo 754331 1132793 := bstep (se 2 (by rfl) ⟨424797, by rfl⟩ : syracuseStep 1132793 = 849595) B849595
theorem B1132895 : Blo 754331 1132895 := bstep (se 1 (by rfl) ⟨849671, by rfl⟩ : syracuseStep 1132895 = 1699343) B1699343
theorem B1132907 : Blo 754331 1132907 := bstep (se 1 (by rfl) ⟨849680, by rfl⟩ : syracuseStep 1132907 = 1699361) B1699361
theorem B1362395 : Blo 754331 1362395 := bstep (se 1 (by rfl) ⟨1021796, by rfl⟩ : syracuseStep 1362395 = 2043593) B2043593
theorem B2869769 : Blo 754331 2869769 := bstep (se 2 (by rfl) ⟨1076163, by rfl⟩ : syracuseStep 2869769 = 2152327) B2152327
theorem B1919497 : Blo 754331 1919497 := bstep (se 2 (by rfl) ⟨719811, by rfl⟩ : syracuseStep 1919497 = 1439623) B1439623
theorem B1133135 : Blo 754331 1133135 := bstep (se 1 (by rfl) ⟨849851, by rfl⟩ : syracuseStep 1133135 = 1699703) B1699703
theorem B1133255 : Blo 754331 1133255 := bstep (se 1 (by rfl) ⟨849941, by rfl⟩ : syracuseStep 1133255 = 1699883) B1699883
theorem B5458691 : Blo 754331 5458691 := bstep (se 1 (by rfl) ⟨4094018, by rfl⟩ : syracuseStep 5458691 = 8188037) B8188037
theorem B4836125 : Blo 754331 4836125 := bstep (se 3 (by rfl) ⟨906773, by rfl⟩ : syracuseStep 4836125 = 1813547) B1813547
theorem B1133417 : Blo 754331 1133417 := bstep (se 2 (by rfl) ⟨425031, by rfl⟩ : syracuseStep 1133417 = 850063) B850063
theorem B805807 : Blo 754331 805807 := bstep (se 1 (by rfl) ⟨604355, by rfl⟩ : syracuseStep 805807 = 1208711) B1208711
theorem B1133495 : Blo 754331 1133495 := bstep (se 1 (by rfl) ⟨850121, by rfl⟩ : syracuseStep 1133495 = 1700243) B1700243
theorem B1133531 : Blo 754331 1133531 := bstep (se 1 (by rfl) ⟨850148, by rfl⟩ : syracuseStep 1133531 = 1700297) B1700297
theorem B4312217 : Blo 754331 4312217 := bstep (se 2 (by rfl) ⟨1617081, by rfl⟩ : syracuseStep 4312217 = 3234163) B3234163
theorem B5328293 : Blo 754331 5328293 := bstep (se 4 (by rfl) ⟨499527, by rfl⟩ : syracuseStep 5328293 = 999055) B999055
theorem B1133999 : Blo 754331 1133999 := bstep (se 1 (by rfl) ⟨850499, by rfl⟩ : syracuseStep 1133999 = 1700999) B1700999
theorem B1134089 : Blo 754331 1134089 := bstep (se 2 (by rfl) ⟨425283, by rfl⟩ : syracuseStep 1134089 = 850567) B850567
theorem B1134119 : Blo 754331 1134119 := bstep (se 1 (by rfl) ⟨850589, by rfl⟩ : syracuseStep 1134119 = 1701179) B1701179
theorem B4312673 : Blo 754331 4312673 := bstep (se 2 (by rfl) ⟨1617252, by rfl⟩ : syracuseStep 4312673 = 3234505) B3234505
theorem B1134203 : Blo 754331 1134203 := bstep (se 1 (by rfl) ⟨850652, by rfl⟩ : syracuseStep 1134203 = 1701305) B1701305
theorem B2150027 : Blo 754331 2150027 := bstep (se 1 (by rfl) ⟨1612520, by rfl⟩ : syracuseStep 2150027 = 3225041) B3225041
theorem B2870923 : Blo 754331 2870923 := bstep (se 1 (by rfl) ⟨2153192, by rfl⟩ : syracuseStep 2870923 = 4306385) B4306385
theorem B3821255 : Blo 754331 3821255 := bstep (se 1 (by rfl) ⟨2865941, by rfl⟩ : syracuseStep 3821255 = 5731883) B5731883
theorem B6901469 : Blo 754331 6901469 := bstep (se 3 (by rfl) ⟨1294025, by rfl⟩ : syracuseStep 6901469 = 2588051) B2588051
theorem B1134329 : Blo 754331 1134329 := bstep (se 2 (by rfl) ⟨425373, by rfl⟩ : syracuseStep 1134329 = 850747) B850747
theorem B4083551 : Blo 754331 4083551 := bstep (se 1 (by rfl) ⟨3062663, by rfl⟩ : syracuseStep 4083551 = 6125327) B6125327
theorem B1134431 : Blo 754331 1134431 := bstep (se 1 (by rfl) ⟨850823, by rfl⟩ : syracuseStep 1134431 = 1701647) B1701647
theorem B1134443 : Blo 754331 1134443 := bstep (se 1 (by rfl) ⟨850832, by rfl⟩ : syracuseStep 1134443 = 1701665) B1701665
theorem B2871227 : Blo 754331 2871227 := bstep (se 1 (by rfl) ⟨2153420, by rfl⟩ : syracuseStep 2871227 = 4306841) B4306841
theorem B1134671 : Blo 754331 1134671 := bstep (se 1 (by rfl) ⟨851003, by rfl⟩ : syracuseStep 1134671 = 1702007) B1702007
theorem B3887185 : Blo 754331 3887185 := bstep (se 2 (by rfl) ⟨1457694, by rfl⟩ : syracuseStep 3887185 = 2915389) B2915389
theorem B1134791 : Blo 754331 1134791 := bstep (se 1 (by rfl) ⟨851093, by rfl⟩ : syracuseStep 1134791 = 1702187) B1702187
theorem B1134953 : Blo 754331 1134953 := bstep (se 2 (by rfl) ⟨425607, by rfl⟩ : syracuseStep 1134953 = 851215) B851215
theorem B1135031 : Blo 754331 1135031 := bstep (se 1 (by rfl) ⟨851273, by rfl⟩ : syracuseStep 1135031 = 1702547) B1702547
theorem B1135067 : Blo 754331 1135067 := bstep (se 1 (by rfl) ⟨851300, by rfl⟩ : syracuseStep 1135067 = 1702601) B1702601
theorem B1135535 : Blo 754331 1135535 := bstep (se 1 (by rfl) ⟨851651, by rfl⟩ : syracuseStep 1135535 = 1703303) B1703303
theorem B1135625 : Blo 754331 1135625 := bstep (se 2 (by rfl) ⟨425859, by rfl⟩ : syracuseStep 1135625 = 851719) B851719
theorem B4314131 : Blo 754331 4314131 := bstep (se 1 (by rfl) ⟨3235598, by rfl⟩ : syracuseStep 4314131 = 6471197) B6471197
theorem B1135655 : Blo 754331 1135655 := bstep (se 1 (by rfl) ⟨851741, by rfl⟩ : syracuseStep 1135655 = 1703483) B1703483
theorem B1135739 : Blo 754331 1135739 := bstep (se 1 (by rfl) ⟨851804, by rfl⟩ : syracuseStep 1135739 = 1703609) B1703609
theorem B1135865 : Blo 754331 1135865 := bstep (se 2 (by rfl) ⟨425949, by rfl⟩ : syracuseStep 1135865 = 851899) B851899
theorem B5756183 : Blo 754331 5756183 := bstep (se 1 (by rfl) ⟨4317137, by rfl⟩ : syracuseStep 5756183 = 8634275) B8634275
theorem B1135967 : Blo 754331 1135967 := bstep (se 1 (by rfl) ⟨851975, by rfl⟩ : syracuseStep 1135967 = 1703951) B1703951
theorem B1135979 : Blo 754331 1135979 := bstep (se 1 (by rfl) ⟨851984, by rfl⟩ : syracuseStep 1135979 = 1703969) B1703969
theorem B3626441 : Blo 754331 3626441 := bstep (se 2 (by rfl) ⟨1359915, by rfl⟩ : syracuseStep 3626441 = 2719831) B2719831
theorem B5821915 : Blo 754331 5821915 := bstep (se 1 (by rfl) ⟨4366436, by rfl⟩ : syracuseStep 5821915 = 8732873) B8732873
theorem B1725961 : Blo 754331 1725961 := bstep (se 2 (by rfl) ⟨647235, by rfl⟩ : syracuseStep 1725961 = 1294471) B1294471
theorem B1136207 : Blo 754331 1136207 := bstep (se 1 (by rfl) ⟨852155, by rfl⟩ : syracuseStep 1136207 = 1704311) B1704311
theorem B4085437 : Blo 754331 4085437 := bstep (se 3 (by rfl) ⟨766019, by rfl⟩ : syracuseStep 4085437 = 1532039) B1532039
theorem B1136327 : Blo 754331 1136327 := bstep (se 1 (by rfl) ⟨852245, by rfl⟩ : syracuseStep 1136327 = 1704491) B1704491
theorem B1136489 : Blo 754331 1136489 := bstep (se 2 (by rfl) ⟨426183, by rfl⟩ : syracuseStep 1136489 = 852367) B852367
theorem B1136567 : Blo 754331 1136567 := bstep (se 1 (by rfl) ⟨852425, by rfl⟩ : syracuseStep 1136567 = 1704851) B1704851
theorem B1136603 : Blo 754331 1136603 := bstep (se 1 (by rfl) ⟨852452, by rfl⟩ : syracuseStep 1136603 = 1704905) B1704905
theorem B2218063 : Blo 754331 2218063 := bstep (se 1 (by rfl) ⟨1663547, by rfl⟩ : syracuseStep 2218063 = 3327095) B3327095
theorem B2546045 : Blo 754331 2546045 := bstep (se 3 (by rfl) ⟨477383, by rfl⟩ : syracuseStep 2546045 = 954767) B954767
theorem B1137071 : Blo 754331 1137071 := bstep (se 1 (by rfl) ⟨852803, by rfl⟩ : syracuseStep 1137071 = 1705607) B1705607
theorem B1137161 : Blo 754331 1137161 := bstep (se 2 (by rfl) ⟨426435, by rfl⟩ : syracuseStep 1137161 = 852871) B852871
theorem B1137191 : Blo 754331 1137191 := bstep (se 1 (by rfl) ⟨852893, by rfl⟩ : syracuseStep 1137191 = 1705787) B1705787
theorem B1137275 : Blo 754331 1137275 := bstep (se 1 (by rfl) ⟨852956, by rfl⟩ : syracuseStep 1137275 = 1705913) B1705913
theorem B2546315 : Blo 754331 2546315 := bstep (se 1 (by rfl) ⟨1909736, by rfl⟩ : syracuseStep 2546315 = 3819473) B3819473
theorem B1432235 : Blo 754331 1432235 := bstep (se 1 (by rfl) ⟨1074176, by rfl⟩ : syracuseStep 1432235 = 2148353) B2148353
theorem B9689777 : Blo 754331 9689777 := bstep (se 2 (by rfl) ⟨3633666, by rfl⟩ : syracuseStep 9689777 = 7267333) B7267333
theorem B5757641 : Blo 754331 5757641 := bstep (se 2 (by rfl) ⟨2159115, by rfl⟩ : syracuseStep 5757641 = 4318231) B4318231
theorem B1137401 : Blo 754331 1137401 := bstep (se 2 (by rfl) ⟨426525, by rfl⟩ : syracuseStep 1137401 = 853051) B853051
theorem B12933917 : Blo 754331 12933917 := bstep (se 3 (by rfl) ⟨2425109, by rfl⟩ : syracuseStep 12933917 = 4850219) B4850219
theorem B777691 : Blo 754331 777691 := bstep (se 1 (by rfl) ⟨583268, by rfl⟩ : syracuseStep 777691 = 1166537) B1166537
theorem B2547233 : Blo 754331 2547233 := bstep (se 2 (by rfl) ⟨955212, by rfl⟩ : syracuseStep 2547233 = 1910425) B1910425
theorem B2547449 : Blo 754331 2547449 := bstep (se 2 (by rfl) ⟨955293, by rfl⟩ : syracuseStep 2547449 = 1910587) B1910587
theorem B4317047 : Blo 754331 4317047 := bstep (se 1 (by rfl) ⟨3237785, by rfl⟩ : syracuseStep 4317047 = 6475571) B6475571
theorem B2154401 : Blo 754331 2154401 := bstep (se 2 (by rfl) ⟨807900, by rfl⟩ : syracuseStep 2154401 = 1615801) B1615801
theorem B2875297 : Blo 754331 2875297 := bstep (se 2 (by rfl) ⟨1078236, by rfl⟩ : syracuseStep 2875297 = 2156473) B2156473
theorem B2547719 : Blo 754331 2547719 := bstep (se 1 (by rfl) ⟨1910789, by rfl⟩ : syracuseStep 2547719 = 3821579) B3821579
theorem B1433609 : Blo 754331 1433609 := bstep (se 2 (by rfl) ⟨537603, by rfl⟩ : syracuseStep 1433609 = 1075207) B1075207
theorem B1433639 : Blo 754331 1433639 := bstep (se 1 (by rfl) ⟨1075229, by rfl⟩ : syracuseStep 1433639 = 2150459) B2150459
theorem B2547827 : Blo 754331 2547827 := bstep (se 1 (by rfl) ⟨1910870, by rfl⟩ : syracuseStep 2547827 = 3821741) B3821741
theorem B4317299 : Blo 754331 4317299 := bstep (se 1 (by rfl) ⟨3237974, by rfl⟩ : syracuseStep 4317299 = 6475949) B6475949
theorem B1532233 : Blo 754331 1532233 := bstep (se 2 (by rfl) ⟨574587, by rfl⟩ : syracuseStep 1532233 = 1149175) B1149175
theorem B2548097 : Blo 754331 2548097 := bstep (se 2 (by rfl) ⟨955536, by rfl⟩ : syracuseStep 2548097 = 1911073) B1911073
theorem B6120137 : Blo 754331 6120137 := bstep (se 2 (by rfl) ⟨2295051, by rfl⟩ : syracuseStep 6120137 = 4590103) B4590103
theorem B1434323 : Blo 754331 1434323 := bstep (se 1 (by rfl) ⟨1075742, by rfl⟩ : syracuseStep 1434323 = 2151485) B2151485
theorem B1434361 : Blo 754331 1434361 := bstep (se 2 (by rfl) ⟨537885, by rfl⟩ : syracuseStep 1434361 = 1075771) B1075771
theorem B2876255 : Blo 754331 2876255 := bstep (se 1 (by rfl) ⟨2157191, by rfl⟩ : syracuseStep 2876255 = 4314383) B4314383
theorem B2876269 : Blo 754331 2876269 := bstep (se 3 (by rfl) ⟨539300, by rfl⟩ : syracuseStep 2876269 = 1078601) B1078601
theorem B15524783 : Blo 754331 15524783 := bstep (se 1 (by rfl) ⟨11643587, by rfl⟩ : syracuseStep 15524783 = 23287175) B23287175
theorem B3073043 : Blo 754331 3073043 := bstep (se 1 (by rfl) ⟨2304782, by rfl⟩ : syracuseStep 3073043 = 4609565) B4609565
theorem B2876573 : Blo 754331 2876573 := bstep (se 3 (by rfl) ⟨539357, by rfl⟩ : syracuseStep 2876573 = 1078715) B1078715
theorem B2548907 : Blo 754331 2548907 := bstep (se 1 (by rfl) ⟨1911680, by rfl⟩ : syracuseStep 2548907 = 3823361) B3823361
theorem B2418025 : Blo 754331 2418025 := bstep (se 2 (by rfl) ⟨906759, by rfl⟩ : syracuseStep 2418025 = 1813519) B1813519
theorem B3827087 : Blo 754331 3827087 := bstep (se 1 (by rfl) ⟨2870315, by rfl⟩ : syracuseStep 3827087 = 5740631) B5740631
theorem B17425829 : Blo 754331 17425829 := bstep (se 4 (by rfl) ⟨1633671, by rfl⟩ : syracuseStep 17425829 = 3267343) B3267343
theorem B12445093 : Blo 754331 12445093 := bstep (se 4 (by rfl) ⟨1166727, by rfl⟩ : syracuseStep 12445093 = 2333455) B2333455
theorem B1435067 : Blo 754331 1435067 := bstep (se 1 (by rfl) ⟨1076300, by rfl⟩ : syracuseStep 1435067 = 2152601) B2152601
theorem B18703817 : Blo 754331 18703817 := bstep (se 2 (by rfl) ⟨7013931, by rfl⟩ : syracuseStep 18703817 = 14027863) B14027863
theorem B5465723 : Blo 754331 5465723 := bstep (se 1 (by rfl) ⟨4099292, by rfl⟩ : syracuseStep 5465723 = 8198585) B8198585
theorem B2549447 : Blo 754331 2549447 := bstep (se 1 (by rfl) ⟨1912085, by rfl⟩ : syracuseStep 2549447 = 3824171) B3824171
theorem B4155095 : Blo 754331 4155095 := bstep (se 1 (by rfl) ⟨3116321, by rfl⟩ : syracuseStep 4155095 = 6232643) B6232643
theorem B2877227 : Blo 754331 2877227 := bstep (se 1 (by rfl) ⟨2157920, by rfl⟩ : syracuseStep 2877227 = 4315841) B4315841
theorem B1435553 : Blo 754331 1435553 := bstep (se 2 (by rfl) ⟨538332, by rfl⟩ : syracuseStep 1435553 = 1076665) B1076665
theorem B1697723 : Blo 754331 1697723 := bstep (se 1 (by rfl) ⟨1273292, by rfl⟩ : syracuseStep 1697723 = 2546585) B2546585
theorem B1697849 : Blo 754331 1697849 := bstep (se 2 (by rfl) ⟨636693, by rfl⟩ : syracuseStep 1697849 = 1273387) B1273387
theorem B2156701 : Blo 754331 2156701 := bstep (se 3 (by rfl) ⟨404381, by rfl⟩ : syracuseStep 2156701 = 808763) B808763
theorem B2582699 : Blo 754331 2582699 := bstep (se 1 (by rfl) ⟨1937024, by rfl⟩ : syracuseStep 2582699 = 3874049) B3874049
theorem B1435819 : Blo 754331 1435819 := bstep (se 1 (by rfl) ⟨1076864, by rfl⟩ : syracuseStep 1435819 = 2153729) B2153729
theorem B1698191 : Blo 754331 1698191 := bstep (se 1 (by rfl) ⟨1273643, by rfl⟩ : syracuseStep 1698191 = 2547287) B2547287
theorem B1436123 : Blo 754331 1436123 := bstep (se 1 (by rfl) ⟨1077092, by rfl⟩ : syracuseStep 1436123 = 2154185) B2154185
theorem B2157043 : Blo 754331 2157043 := bstep (se 1 (by rfl) ⟨1617782, by rfl⟩ : syracuseStep 2157043 = 3235565) B3235565
theorem B2550311 : Blo 754331 2550311 := bstep (se 1 (by rfl) ⟨1912733, by rfl⟩ : syracuseStep 2550311 = 3825467) B3825467
theorem B2550419 : Blo 754331 2550419 := bstep (se 1 (by rfl) ⟨1912814, by rfl⟩ : syracuseStep 2550419 = 3825629) B3825629
theorem B1698515 : Blo 754331 1698515 := bstep (se 1 (by rfl) ⟨1273886, by rfl⟩ : syracuseStep 1698515 = 2547773) B2547773
theorem B2550635 : Blo 754331 2550635 := bstep (se 1 (by rfl) ⟨1912976, by rfl⟩ : syracuseStep 2550635 = 3825953) B3825953
theorem B2550689 : Blo 754331 2550689 := bstep (se 2 (by rfl) ⟨956508, by rfl⟩ : syracuseStep 2550689 = 1913017) B1913017
theorem B3632129 : Blo 754331 3632129 := bstep (se 2 (by rfl) ⟨1362048, by rfl⟩ : syracuseStep 3632129 = 2724097) B2724097
theorem B1272955 : Blo 754331 1272955 := bstep (se 1 (by rfl) ⟨954716, by rfl⟩ : syracuseStep 1272955 = 1909433) B1909433
theorem B3632323 : Blo 754331 3632323 := bstep (se 1 (by rfl) ⟨2724242, by rfl⟩ : syracuseStep 3632323 = 5448485) B5448485
theorem B2583895 : Blo 754331 2583895 := bstep (se 1 (by rfl) ⟨1937921, by rfl⟩ : syracuseStep 2583895 = 3875843) B3875843
theorem B3829193 : Blo 754331 3829193 := bstep (se 2 (by rfl) ⟨1435947, by rfl⟩ : syracuseStep 3829193 = 2871895) B2871895
theorem B1076699 : Blo 754331 1076699 := bstep (se 1 (by rfl) ⟨807524, by rfl⟩ : syracuseStep 1076699 = 1615049) B1615049
theorem B2551283 : Blo 754331 2551283 := bstep (se 1 (by rfl) ⟨1913462, by rfl⟩ : syracuseStep 2551283 = 3826925) B3826925
theorem B1437193 : Blo 754331 1437193 := bstep (se 2 (by rfl) ⟨538947, by rfl⟩ : syracuseStep 1437193 = 1077895) B1077895
theorem B4845095 : Blo 754331 4845095 := bstep (se 1 (by rfl) ⟨3633821, by rfl⟩ : syracuseStep 4845095 = 7267643) B7267643
theorem B1699451 : Blo 754331 1699451 := bstep (se 1 (by rfl) ⟨1274588, by rfl⟩ : syracuseStep 1699451 = 2549177) B2549177
theorem B5729939 : Blo 754331 5729939 := bstep (se 1 (by rfl) ⟨4297454, by rfl⟩ : syracuseStep 5729939 = 8594909) B8594909
theorem B2879185 : Blo 754331 2879185 := bstep (se 2 (by rfl) ⟨1079694, by rfl⟩ : syracuseStep 2879185 = 2159389) B2159389
theorem B1699577 : Blo 754331 1699577 := bstep (se 2 (by rfl) ⟨637341, by rfl⟩ : syracuseStep 1699577 = 1274683) B1274683
theorem B10907459 : Blo 754331 10907459 := bstep (se 1 (by rfl) ⟨8180594, by rfl⟩ : syracuseStep 10907459 = 16361189) B16361189
theorem B2420599 : Blo 754331 2420599 := bstep (se 1 (by rfl) ⟨1815449, by rfl⟩ : syracuseStep 2420599 = 3630899) B3630899
theorem B12283811 : Blo 754331 12283811 := bstep (se 1 (by rfl) ⟨9212858, by rfl⟩ : syracuseStep 12283811 = 18425717) B18425717
theorem B1273819 : Blo 754331 1273819 := bstep (se 1 (by rfl) ⟨955364, by rfl⟩ : syracuseStep 1273819 = 1910729) B1910729
theorem B1699847 : Blo 754331 1699847 := bstep (se 1 (by rfl) ⟨1274885, by rfl⟩ : syracuseStep 1699847 = 2549771) B2549771
theorem B1077257 : Blo 754331 1077257 := bstep (se 2 (by rfl) ⟨403971, by rfl⟩ : syracuseStep 1077257 = 807943) B807943
theorem B2551823 : Blo 754331 2551823 := bstep (se 1 (by rfl) ⟨1913867, by rfl⟩ : syracuseStep 2551823 = 3827735) B3827735
theorem B1699919 : Blo 754331 1699919 := bstep (se 1 (by rfl) ⟨1274939, by rfl⟩ : syracuseStep 1699919 = 2549879) B2549879
theorem B3829841 : Blo 754331 3829841 := bstep (se 2 (by rfl) ⟨1436190, by rfl⟩ : syracuseStep 3829841 = 2872381) B2872381
theorem B1437907 : Blo 754331 1437907 := bstep (se 1 (by rfl) ⟨1078430, by rfl⟩ : syracuseStep 1437907 = 2156861) B2156861
theorem B1700315 : Blo 754331 1700315 := bstep (se 1 (by rfl) ⟨1275236, by rfl⟩ : syracuseStep 1700315 = 2550473) B2550473
theorem B1208839 : Blo 754331 1208839 := bstep (se 1 (by rfl) ⟨906629, by rfl⟩ : syracuseStep 1208839 = 1813259) B1813259
theorem B1274447 : Blo 754331 1274447 := bstep (se 1 (by rfl) ⟨955835, by rfl⟩ : syracuseStep 1274447 = 1911671) B1911671
theorem B2552417 : Blo 754331 2552417 := bstep (se 2 (by rfl) ⟨957156, by rfl⟩ : syracuseStep 2552417 = 1914313) B1914313
theorem B2519687 : Blo 754331 2519687 := bstep (se 1 (by rfl) ⟨1889765, by rfl⟩ : syracuseStep 2519687 = 3779531) B3779531
theorem B3928787 : Blo 754331 3928787 := bstep (se 1 (by rfl) ⟨2946590, by rfl⟩ : syracuseStep 3928787 = 5893181) B5893181
theorem B1078123 : Blo 754331 1078123 := bstep (se 1 (by rfl) ⟨808592, by rfl⟩ : syracuseStep 1078123 = 1617185) B1617185
theorem B1700783 : Blo 754331 1700783 := bstep (se 1 (by rfl) ⟨1275587, by rfl⟩ : syracuseStep 1700783 = 2551175) B2551175
theorem B1438651 : Blo 754331 1438651 := bstep (se 1 (by rfl) ⟨1078988, by rfl⟩ : syracuseStep 1438651 = 2157977) B2157977
theorem B849019 : Blo 754331 849019 := bstep (se 1 (by rfl) ⟨636764, by rfl⟩ : syracuseStep 849019 = 1273529) B1273529
theorem B1701035 : Blo 754331 1701035 := bstep (se 1 (by rfl) ⟨1275776, by rfl⟩ : syracuseStep 1701035 = 2551553) B2551553
theorem B4846787 : Blo 754331 4846787 := bstep (se 1 (by rfl) ⟨3635090, by rfl⟩ : syracuseStep 4846787 = 7270181) B7270181
theorem B1439137 : Blo 754331 1439137 := bstep (se 2 (by rfl) ⟨539676, by rfl⟩ : syracuseStep 1439137 = 1079353) B1079353
theorem B1275311 : Blo 754331 1275311 := bstep (se 1 (by rfl) ⟨956483, by rfl⟩ : syracuseStep 1275311 = 1912967) B1912967
theorem B2618825 : Blo 754331 2618825 := bstep (se 2 (by rfl) ⟨982059, by rfl⟩ : syracuseStep 2618825 = 1964119) B1964119
theorem B2422331 : Blo 754331 2422331 := bstep (se 1 (by rfl) ⟨1816748, by rfl⟩ : syracuseStep 2422331 = 3633497) B3633497
theorem B849487 : Blo 754331 849487 := bstep (se 1 (by rfl) ⟨637115, by rfl⟩ : syracuseStep 849487 = 1274231) B1274231
theorem B1209935 : Blo 754331 1209935 := bstep (se 1 (by rfl) ⟨907451, by rfl⟩ : syracuseStep 1209935 = 1814903) B1814903
theorem B32765633 : Blo 754331 32765633 := bstep (se 2 (by rfl) ⟨12287112, by rfl⟩ : syracuseStep 32765633 = 24574225) B24574225
theorem B1701575 : Blo 754331 1701575 := bstep (se 1 (by rfl) ⟨1276181, by rfl⟩ : syracuseStep 1701575 = 2552363) B2552363
theorem B1963871 : Blo 754331 1963871 := bstep (se 1 (by rfl) ⟨1472903, by rfl⟩ : syracuseStep 1963871 = 2945807) B2945807
theorem B1275743 : Blo 754331 1275743 := bstep (se 1 (by rfl) ⟨956807, by rfl⟩ : syracuseStep 1275743 = 1913615) B1913615
theorem B849883 : Blo 754331 849883 := bstep (se 1 (by rfl) ⟨637412, by rfl⟩ : syracuseStep 849883 = 1274825) B1274825
theorem B2553875 : Blo 754331 2553875 := bstep (se 1 (by rfl) ⟨1915406, by rfl⟩ : syracuseStep 2553875 = 3830813) B3830813
theorem B2554199 : Blo 754331 2554199 := bstep (se 1 (by rfl) ⟨1915649, by rfl⟩ : syracuseStep 2554199 = 3831299) B3831299
theorem B1276303 : Blo 754331 1276303 := bstep (se 1 (by rfl) ⟨957227, by rfl⟩ : syracuseStep 1276303 = 1914455) B1914455
theorem B850351 : Blo 754331 850351 := bstep (se 1 (by rfl) ⟨637763, by rfl⟩ : syracuseStep 850351 = 1275527) B1275527
theorem B1702439 : Blo 754331 1702439 := bstep (se 1 (by rfl) ⟨1276829, by rfl⟩ : syracuseStep 1702439 = 2553659) B2553659
theorem B850783 : Blo 754331 850783 := bstep (se 1 (by rfl) ⟨638087, by rfl⟩ : syracuseStep 850783 = 1276175) B1276175
theorem B1702763 : Blo 754331 1702763 := bstep (se 1 (by rfl) ⟨1277072, by rfl⟩ : syracuseStep 1702763 = 2554145) B2554145
theorem B1702817 : Blo 754331 1702817 := bstep (se 2 (by rfl) ⟨638556, by rfl⟩ : syracuseStep 1702817 = 1277113) B1277113
theorem B5733341 : Blo 754331 5733341 := bstep (se 3 (by rfl) ⟨1075001, by rfl⟩ : syracuseStep 5733341 = 2150003) B2150003
theorem B1276985 : Blo 754331 1276985 := bstep (se 2 (by rfl) ⟨478869, by rfl⟩ : syracuseStep 1276985 = 957739) B957739
theorem B851143 : Blo 754331 851143 := bstep (se 1 (by rfl) ⟨638357, by rfl⟩ : syracuseStep 851143 = 1276715) B1276715
theorem B1703159 : Blo 754331 1703159 := bstep (se 1 (by rfl) ⟨1277369, by rfl⟩ : syracuseStep 1703159 = 2554739) B2554739
theorem B7273871 : Blo 754331 7273871 := bstep (se 1 (by rfl) ⟨5455403, by rfl⟩ : syracuseStep 7273871 = 10910807) B10910807
theorem B2555279 : Blo 754331 2555279 := bstep (se 1 (by rfl) ⟨1916459, by rfl⟩ : syracuseStep 2555279 = 3832919) B3832919
theorem B10911149 : Blo 754331 10911149 := bstep (se 3 (by rfl) ⟨2045840, by rfl⟩ : syracuseStep 10911149 = 4091681) B4091681
theorem B2555603 : Blo 754331 2555603 := bstep (se 1 (by rfl) ⟨1916702, by rfl⟩ : syracuseStep 2555603 = 3833405) B3833405
theorem B1277687 : Blo 754331 1277687 := bstep (se 1 (by rfl) ⟨958265, by rfl⟩ : syracuseStep 1277687 = 1916531) B1916531
theorem B2424649 : Blo 754331 2424649 := bstep (se 2 (by rfl) ⟨909243, by rfl⟩ : syracuseStep 2424649 = 1818487) B1818487
theorem B1703753 : Blo 754331 1703753 := bstep (se 2 (by rfl) ⟨638907, by rfl⟩ : syracuseStep 1703753 = 1277815) B1277815
theorem B2588777 : Blo 754331 2588777 := bstep (se 2 (by rfl) ⟨970791, by rfl⟩ : syracuseStep 2588777 = 1941583) B1941583
theorem B1704041 : Blo 754331 1704041 := bstep (se 2 (by rfl) ⟨639015, by rfl⟩ : syracuseStep 1704041 = 1278031) B1278031
theorem B852187 : Blo 754331 852187 := bstep (se 1 (by rfl) ⟨639140, by rfl⟩ : syracuseStep 852187 = 1278281) B1278281
theorem B2556251 : Blo 754331 2556251 := bstep (se 1 (by rfl) ⟨1917188, by rfl⟩ : syracuseStep 2556251 = 3834377) B3834377
theorem B852475 : Blo 754331 852475 := bstep (se 1 (by rfl) ⟨639356, by rfl⟩ : syracuseStep 852475 = 1278713) B1278713
theorem B1704527 : Blo 754331 1704527 := bstep (se 1 (by rfl) ⟨1278395, by rfl⟩ : syracuseStep 1704527 = 2556791) B2556791
theorem B1278571 : Blo 754331 1278571 := bstep (se 1 (by rfl) ⟨958928, by rfl⟩ : syracuseStep 1278571 = 1917857) B1917857
theorem B3834539 : Blo 754331 3834539 := bstep (se 1 (by rfl) ⟨2875904, by rfl⟩ : syracuseStep 3834539 = 5751809) B5751809
theorem B852655 : Blo 754331 852655 := bstep (se 1 (by rfl) ⟨639491, by rfl⟩ : syracuseStep 852655 = 1278983) B1278983
theorem B2589367 : Blo 754331 2589367 := bstep (se 1 (by rfl) ⟨1942025, by rfl⟩ : syracuseStep 2589367 = 3884051) B3884051
theorem B754399 : Blo 754331 754399 := bstep (se 1 (by rfl) ⟨565799, by rfl⟩ : syracuseStep 754399 = 1131599) B1131599
theorem B1704671 : Blo 754331 1704671 := bstep (se 1 (by rfl) ⟨1278503, by rfl⟩ : syracuseStep 1704671 = 2557007) B2557007
theorem B754479 : Blo 754331 754479 := bstep (se 1 (by rfl) ⟨565859, by rfl⟩ : syracuseStep 754479 = 1131719) B1131719
theorem B754587 : Blo 754331 754587 := bstep (se 1 (by rfl) ⟨565940, by rfl⟩ : syracuseStep 754587 = 1131881) B1131881
theorem B1278875 : Blo 754331 1278875 := bstep (se 1 (by rfl) ⟨959156, by rfl⟩ : syracuseStep 1278875 = 1918313) B1918313
theorem B754639 : Blo 754331 754639 := bstep (se 1 (by rfl) ⟨565979, by rfl⟩ : syracuseStep 754639 = 1131959) B1131959
theorem B852943 : Blo 754331 852943 := bstep (se 1 (by rfl) ⟨639707, by rfl⟩ : syracuseStep 852943 = 1279415) B1279415
theorem B1704923 : Blo 754331 1704923 := bstep (se 1 (by rfl) ⟨1278692, by rfl⟩ : syracuseStep 1704923 = 2557385) B2557385
theorem B754663 : Blo 754331 754663 := bstep (se 1 (by rfl) ⟨565997, by rfl⟩ : syracuseStep 754663 = 1131995) B1131995
theorem B1705103 : Blo 754331 1705103 := bstep (se 1 (by rfl) ⟨1278827, by rfl⟩ : syracuseStep 1705103 = 2557655) B2557655
theorem B3835025 : Blo 754331 3835025 := bstep (se 2 (by rfl) ⟨1438134, by rfl⟩ : syracuseStep 3835025 = 2876269) B2876269
theorem B5538959 : Blo 754331 5538959 := bstep (se 1 (by rfl) ⟨4154219, by rfl⟩ : syracuseStep 5538959 = 8308439) B8308439
theorem B4850887 : Blo 754331 4850887 := bstep (se 1 (by rfl) ⟨3638165, by rfl⟩ : syracuseStep 4850887 = 7276331) B7276331
theorem B1705193 : Blo 754331 1705193 := bstep (se 2 (by rfl) ⟨639447, by rfl⟩ : syracuseStep 1705193 = 1278895) B1278895
theorem B754975 : Blo 754331 754975 := bstep (se 1 (by rfl) ⟨566231, by rfl⟩ : syracuseStep 754975 = 1132463) B1132463
theorem B1705247 : Blo 754331 1705247 := bstep (se 1 (by rfl) ⟨1278935, by rfl⟩ : syracuseStep 1705247 = 2557871) B2557871
theorem B2557223 : Blo 754331 2557223 := bstep (se 1 (by rfl) ⟨1917917, by rfl⟩ : syracuseStep 2557223 = 3835835) B3835835
theorem B755035 : Blo 754331 755035 := bstep (se 1 (by rfl) ⟨566276, by rfl⟩ : syracuseStep 755035 = 1132553) B1132553
theorem B755055 : Blo 754331 755055 := bstep (se 1 (by rfl) ⟨566291, by rfl⟩ : syracuseStep 755055 = 1132583) B1132583
theorem B755111 : Blo 754331 755111 := bstep (se 1 (by rfl) ⟨566333, by rfl⟩ : syracuseStep 755111 = 1132667) B1132667
theorem B755195 : Blo 754331 755195 := bstep (se 1 (by rfl) ⟨566396, by rfl⟩ : syracuseStep 755195 = 1132793) B1132793
theorem B755263 : Blo 754331 755263 := bstep (se 1 (by rfl) ⟨566447, by rfl⟩ : syracuseStep 755263 = 1132895) B1132895
theorem B755271 : Blo 754331 755271 := bstep (se 1 (by rfl) ⟨566453, by rfl⟩ : syracuseStep 755271 = 1132907) B1132907
theorem B755423 : Blo 754331 755423 := bstep (se 1 (by rfl) ⟨566567, by rfl⟩ : syracuseStep 755423 = 1133135) B1133135
theorem B1705769 : Blo 754331 1705769 := bstep (se 2 (by rfl) ⟨639663, by rfl⟩ : syracuseStep 1705769 = 1279327) B1279327
theorem B755503 : Blo 754331 755503 := bstep (se 1 (by rfl) ⟨566627, by rfl⟩ : syracuseStep 755503 = 1133255) B1133255
theorem B3639127 : Blo 754331 3639127 := bstep (se 1 (by rfl) ⟨2729345, by rfl⟩ : syracuseStep 3639127 = 5458691) B5458691
theorem B16320365 : Blo 754331 16320365 := bstep (se 3 (by rfl) ⟨3060068, by rfl⟩ : syracuseStep 16320365 = 6120137) B6120137
theorem B755611 : Blo 754331 755611 := bstep (se 1 (by rfl) ⟨566708, by rfl⟩ : syracuseStep 755611 = 1133417) B1133417
theorem B755663 : Blo 754331 755663 := bstep (se 1 (by rfl) ⟨566747, by rfl⟩ : syracuseStep 755663 = 1133495) B1133495
theorem B755687 : Blo 754331 755687 := bstep (se 1 (by rfl) ⟨566765, by rfl⟩ : syracuseStep 755687 = 1133531) B1133531
theorem B2558087 : Blo 754331 2558087 := bstep (se 1 (by rfl) ⟨1918565, by rfl⟩ : syracuseStep 2558087 = 3837131) B3837131
theorem B755999 : Blo 754331 755999 := bstep (se 1 (by rfl) ⟨566999, by rfl⟩ : syracuseStep 755999 = 1133999) B1133999
theorem B756059 : Blo 754331 756059 := bstep (se 1 (by rfl) ⟨567044, by rfl⟩ : syracuseStep 756059 = 1134089) B1134089
theorem B756079 : Blo 754331 756079 := bstep (se 1 (by rfl) ⟨567059, by rfl⟩ : syracuseStep 756079 = 1134119) B1134119
theorem B756135 : Blo 754331 756135 := bstep (se 1 (by rfl) ⟨567101, by rfl⟩ : syracuseStep 756135 = 1134203) B1134203
theorem B756219 : Blo 754331 756219 := bstep (se 1 (by rfl) ⟨567164, by rfl⟩ : syracuseStep 756219 = 1134329) B1134329
theorem B34867745 : Blo 754331 34867745 := bstep (se 2 (by rfl) ⟨13075404, by rfl⟩ : syracuseStep 34867745 = 26150809) B26150809
theorem B2722367 : Blo 754331 2722367 := bstep (se 1 (by rfl) ⟨2041775, by rfl⟩ : syracuseStep 2722367 = 4083551) B4083551
theorem B756287 : Blo 754331 756287 := bstep (se 1 (by rfl) ⟨567215, by rfl⟩ : syracuseStep 756287 = 1134431) B1134431
theorem B756295 : Blo 754331 756295 := bstep (se 1 (by rfl) ⟨567221, by rfl⟩ : syracuseStep 756295 = 1134443) B1134443
theorem B756447 : Blo 754331 756447 := bstep (se 1 (by rfl) ⟨567335, by rfl⟩ : syracuseStep 756447 = 1134671) B1134671
theorem B7867127 : Blo 754331 7867127 := bstep (se 1 (by rfl) ⟨5900345, by rfl⟩ : syracuseStep 7867127 = 11800691) B11800691
theorem B756527 : Blo 754331 756527 := bstep (se 1 (by rfl) ⟨567395, by rfl⟩ : syracuseStep 756527 = 1134791) B1134791
theorem B756635 : Blo 754331 756635 := bstep (se 1 (by rfl) ⟨567476, by rfl⟩ : syracuseStep 756635 = 1134953) B1134953
theorem B2427803 : Blo 754331 2427803 := bstep (se 1 (by rfl) ⟨1820852, by rfl⟩ : syracuseStep 2427803 = 3641705) B3641705
theorem B756687 : Blo 754331 756687 := bstep (se 1 (by rfl) ⟨567515, by rfl⟩ : syracuseStep 756687 = 1135031) B1135031
theorem B756711 : Blo 754331 756711 := bstep (se 1 (by rfl) ⟨567533, by rfl⟩ : syracuseStep 756711 = 1135067) B1135067
theorem B757023 : Blo 754331 757023 := bstep (se 1 (by rfl) ⟨567767, by rfl⟩ : syracuseStep 757023 = 1135535) B1135535
theorem B757083 : Blo 754331 757083 := bstep (se 1 (by rfl) ⟨567812, by rfl⟩ : syracuseStep 757083 = 1135625) B1135625
theorem B2559329 : Blo 754331 2559329 := bstep (se 2 (by rfl) ⟨959748, by rfl⟩ : syracuseStep 2559329 = 1919497) B1919497
theorem B757103 : Blo 754331 757103 := bstep (se 1 (by rfl) ⟨567827, by rfl⟩ : syracuseStep 757103 = 1135655) B1135655
theorem B757159 : Blo 754331 757159 := bstep (se 1 (by rfl) ⟨567869, by rfl⟩ : syracuseStep 757159 = 1135739) B1135739
theorem B2723321 : Blo 754331 2723321 := bstep (se 2 (by rfl) ⟨1021245, by rfl⟩ : syracuseStep 2723321 = 2042491) B2042491
theorem B757243 : Blo 754331 757243 := bstep (se 1 (by rfl) ⟨567932, by rfl⟩ : syracuseStep 757243 = 1135865) B1135865
theorem B3837455 : Blo 754331 3837455 := bstep (se 1 (by rfl) ⟨2878091, by rfl⟩ : syracuseStep 3837455 = 5756183) B5756183
theorem B757311 : Blo 754331 757311 := bstep (se 1 (by rfl) ⟨567983, by rfl⟩ : syracuseStep 757311 = 1135967) B1135967
theorem B757319 : Blo 754331 757319 := bstep (se 1 (by rfl) ⟨567989, by rfl⟩ : syracuseStep 757319 = 1135979) B1135979
theorem B757471 : Blo 754331 757471 := bstep (se 1 (by rfl) ⟨568103, by rfl⟩ : syracuseStep 757471 = 1136207) B1136207
theorem B757551 : Blo 754331 757551 := bstep (se 1 (by rfl) ⟨568163, by rfl⟩ : syracuseStep 757551 = 1136327) B1136327
theorem B6983533 : Blo 754331 6983533 := bstep (se 3 (by rfl) ⟨1309412, by rfl⟩ : syracuseStep 6983533 = 2618825) B2618825
theorem B757659 : Blo 754331 757659 := bstep (se 1 (by rfl) ⟨568244, by rfl⟩ : syracuseStep 757659 = 1136489) B1136489
theorem B757711 : Blo 754331 757711 := bstep (se 1 (by rfl) ⟨568283, by rfl⟩ : syracuseStep 757711 = 1136567) B1136567
theorem B7966673 : Blo 754331 7966673 := bstep (se 2 (by rfl) ⟨2987502, by rfl⟩ : syracuseStep 7966673 = 5975005) B5975005
theorem B757735 : Blo 754331 757735 := bstep (se 1 (by rfl) ⟨568301, by rfl⟩ : syracuseStep 757735 = 1136603) B1136603
theorem B758047 : Blo 754331 758047 := bstep (se 1 (by rfl) ⟨568535, by rfl⟩ : syracuseStep 758047 = 1137071) B1137071
theorem B758107 : Blo 754331 758107 := bstep (se 1 (by rfl) ⟨568580, by rfl⟩ : syracuseStep 758107 = 1137161) B1137161
theorem B758127 : Blo 754331 758127 := bstep (se 1 (by rfl) ⟨568595, by rfl⟩ : syracuseStep 758127 = 1137191) B1137191
theorem B758183 : Blo 754331 758183 := bstep (se 1 (by rfl) ⟨568637, by rfl⟩ : syracuseStep 758183 = 1137275) B1137275
theorem B954823 : Blo 754331 954823 := bstep (se 1 (by rfl) ⟨716117, by rfl⟩ : syracuseStep 954823 = 1432235) B1432235
theorem B3445193 : Blo 754331 3445193 := bstep (se 2 (by rfl) ⟨1291947, by rfl⟩ : syracuseStep 3445193 = 2583895) B2583895
theorem B6459851 : Blo 754331 6459851 := bstep (se 1 (by rfl) ⟨4844888, by rfl⟩ : syracuseStep 6459851 = 9689777) B9689777
theorem B3838427 : Blo 754331 3838427 := bstep (se 1 (by rfl) ⟨2878820, by rfl⟩ : syracuseStep 3838427 = 5757641) B5757641
theorem B758267 : Blo 754331 758267 := bstep (se 1 (by rfl) ⟨568700, by rfl⟩ : syracuseStep 758267 = 1137401) B1137401
theorem B8622611 : Blo 754331 8622611 := bstep (se 1 (by rfl) ⟨6466958, by rfl⟩ : syracuseStep 8622611 = 12933917) B12933917
theorem B11080253 : Blo 754331 11080253 := bstep (se 3 (by rfl) ⟨2077547, by rfl⟩ : syracuseStep 11080253 = 4155095) B4155095
theorem B3871567 : Blo 754331 3871567 := bstep (se 1 (by rfl) ⟨2903675, by rfl⟩ : syracuseStep 3871567 = 5807351) B5807351
theorem B4297637 : Blo 754331 4297637 := bstep (se 4 (by rfl) ⟨402903, by rfl⟩ : syracuseStep 4297637 = 805807) B805807
theorem B3838913 : Blo 754331 3838913 := bstep (se 2 (by rfl) ⟨1439592, by rfl⟩ : syracuseStep 3838913 = 2879185) B2879185
theorem B3871901 : Blo 754331 3871901 := bstep (se 3 (by rfl) ⟨725981, by rfl⟩ : syracuseStep 3871901 = 1451963) B1451963
theorem B955739 : Blo 754331 955739 := bstep (se 1 (by rfl) ⟨716804, by rfl⟩ : syracuseStep 955739 = 1433609) B1433609
theorem B5182913 : Blo 754331 5182913 := bstep (se 2 (by rfl) ⟨1943592, by rfl⟩ : syracuseStep 5182913 = 3887185) B3887185
theorem B6887197 : Blo 754331 6887197 := bstep (se 3 (by rfl) ⟨1291349, by rfl⟩ : syracuseStep 6887197 = 2582699) B2582699
theorem B956215 : Blo 754331 956215 := bstep (se 1 (by rfl) ⟨717161, by rfl⟩ : syracuseStep 956215 = 1434323) B1434323
theorem B1611785 : Blo 754331 1611785 := bstep (se 2 (by rfl) ⟨604419, by rfl⟩ : syracuseStep 1611785 = 1208839) B1208839
theorem B2726173 : Blo 754331 2726173 := bstep (se 3 (by rfl) ⟨511157, by rfl⟩ : syracuseStep 2726173 = 1022315) B1022315
theorem B956711 : Blo 754331 956711 := bstep (se 1 (by rfl) ⟨717533, by rfl⟩ : syracuseStep 956711 = 1435067) B1435067
theorem B957035 : Blo 754331 957035 := bstep (se 1 (by rfl) ⟨717776, by rfl⟩ : syracuseStep 957035 = 1435553) B1435553
theorem B14523137 : Blo 754331 14523137 := bstep (se 2 (by rfl) ⟨5446176, by rfl⟩ : syracuseStep 14523137 = 10892353) B10892353
theorem B957415 : Blo 754331 957415 := bstep (se 1 (by rfl) ⟨718061, by rfl⟩ : syracuseStep 957415 = 1436123) B1436123
theorem B2301281 : Blo 754331 2301281 := bstep (se 2 (by rfl) ⟨862980, by rfl⟩ : syracuseStep 2301281 = 1725961) B1725961
theorem B7380485 : Blo 754331 7380485 := bstep (se 4 (by rfl) ⟨691920, by rfl⟩ : syracuseStep 7380485 = 1383841) B1383841
theorem B5905979 : Blo 754331 5905979 := bstep (se 1 (by rfl) ⟨4429484, by rfl⟩ : syracuseStep 5905979 = 8858969) B8858969
theorem B5447249 : Blo 754331 5447249 := bstep (se 2 (by rfl) ⟨2042718, by rfl⟩ : syracuseStep 5447249 = 4085437) B4085437
theorem B2957417 : Blo 754331 2957417 := bstep (se 2 (by rfl) ⟨1109031, by rfl⟩ : syracuseStep 2957417 = 2218063) B2218063
theorem B4301009 : Blo 754331 4301009 := bstep (se 2 (by rfl) ⟨1612878, by rfl⟩ : syracuseStep 4301009 = 3225757) B3225757
theorem B1679791 : Blo 754331 1679791 := bstep (se 1 (by rfl) ⟨1259843, by rfl⟩ : syracuseStep 1679791 = 2519687) B2519687
theorem B19341827 : Blo 754331 19341827 := bstep (se 1 (by rfl) ⟨14506370, by rfl⟩ : syracuseStep 19341827 = 29012741) B29012741
theorem B2040383 : Blo 754331 2040383 := bstep (se 1 (by rfl) ⟨1530287, by rfl⟩ : syracuseStep 2040383 = 3060575) B3060575
theorem B2761673 : Blo 754331 2761673 := bstep (se 2 (by rfl) ⟨1035627, by rfl⟩ : syracuseStep 2761673 = 2071255) B2071255
theorem B1614887 : Blo 754331 1614887 := bstep (se 1 (by rfl) ⟨1211165, by rfl⟩ : syracuseStep 1614887 = 2422331) B2422331
theorem B34875299 : Blo 754331 34875299 := bstep (se 1 (by rfl) ⟨26156474, by rfl⟩ : syracuseStep 34875299 = 52312949) B52312949
theorem B1911215 : Blo 754331 1911215 := bstep (se 1 (by rfl) ⟨1433411, by rfl⟩ : syracuseStep 1911215 = 2866823) B2866823
theorem B862943 : Blo 754331 862943 := bstep (se 1 (by rfl) ⟨647207, by rfl⟩ : syracuseStep 862943 = 1294415) B1294415
theorem B3222443 : Blo 754331 3222443 := bstep (se 1 (by rfl) ⟨2416832, by rfl⟩ : syracuseStep 3222443 = 4833665) B4833665
theorem B2042977 : Blo 754331 2042977 := bstep (se 2 (by rfl) ⟨766116, by rfl⟩ : syracuseStep 2042977 = 1532233) B1532233
theorem B13774103 : Blo 754331 13774103 := bstep (se 1 (by rfl) ⟨10330577, by rfl⟩ : syracuseStep 13774103 = 20661155) B20661155
theorem B1813855 : Blo 754331 1813855 := bstep (se 1 (by rfl) ⟨1360391, by rfl⟩ : syracuseStep 1813855 = 2720783) B2720783
theorem B1912187 : Blo 754331 1912187 := bstep (se 1 (by rfl) ⟨1434140, by rfl⟩ : syracuseStep 1912187 = 2868281) B2868281
theorem B1912481 : Blo 754331 1912481 := bstep (se 2 (by rfl) ⟨717180, by rfl⟩ : syracuseStep 1912481 = 1434361) B1434361
theorem B3452651 : Blo 754331 3452651 := bstep (se 1 (by rfl) ⟨2589488, by rfl⟩ : syracuseStep 3452651 = 5178977) B5178977
theorem B12890177 : Blo 754331 12890177 := bstep (se 2 (by rfl) ⟨4833816, by rfl⟩ : syracuseStep 12890177 = 9667633) B9667633
theorem B1913179 : Blo 754331 1913179 := bstep (se 1 (by rfl) ⟨1434884, by rfl⟩ : syracuseStep 1913179 = 2869769) B2869769
theorem B3224033 : Blo 754331 3224033 := bstep (se 2 (by rfl) ⟨1209012, by rfl⟩ : syracuseStep 3224033 = 2418025) B2418025
theorem B3224083 : Blo 754331 3224083 := bstep (se 1 (by rfl) ⟨2418062, by rfl⟩ : syracuseStep 3224083 = 4836125) B4836125
theorem B16593457 : Blo 754331 16593457 := bstep (se 2 (by rfl) ⟨6222546, by rfl⟩ : syracuseStep 16593457 = 12445093) B12445093
theorem B1618859 : Blo 754331 1618859 := bstep (se 1 (by rfl) ⟨1214144, by rfl⟩ : syracuseStep 1618859 = 2428289) B2428289
theorem B1815527 : Blo 754331 1815527 := bstep (se 1 (by rfl) ⟨1361645, by rfl⟩ : syracuseStep 1815527 = 2723291) B2723291
theorem B2864119 : Blo 754331 2864119 := bstep (se 1 (by rfl) ⟨2148089, by rfl⟩ : syracuseStep 2864119 = 4296179) B4296179
theorem B6468599 : Blo 754331 6468599 := bstep (se 1 (by rfl) ⟨4851449, by rfl⟩ : syracuseStep 6468599 = 9702899) B9702899
theorem B4306067 : Blo 754331 4306067 := bstep (se 1 (by rfl) ⟨3229550, by rfl⟩ : syracuseStep 4306067 = 6459101) B6459101
theorem B4600979 : Blo 754331 4600979 := bstep (se 1 (by rfl) ⟨3450734, by rfl⟩ : syracuseStep 4600979 = 6901469) B6901469
theorem B3454109 : Blo 754331 3454109 := bstep (se 3 (by rfl) ⟨647645, by rfl⟩ : syracuseStep 3454109 = 1295291) B1295291
theorem B2864423 : Blo 754331 2864423 := bstep (se 1 (by rfl) ⟨2148317, by rfl⟩ : syracuseStep 2864423 = 4296635) B4296635
theorem B1914151 : Blo 754331 1914151 := bstep (se 1 (by rfl) ⟨1435613, by rfl⟩ : syracuseStep 1914151 = 2871227) B2871227
theorem B1914425 : Blo 754331 1914425 := bstep (se 2 (by rfl) ⟨717909, by rfl⟩ : syracuseStep 1914425 = 1435819) B1435819
theorem B1291871 : Blo 754331 1291871 := bstep (se 1 (by rfl) ⟨968903, by rfl⟩ : syracuseStep 1291871 = 1937807) B1937807
theorem B767791 : Blo 754331 767791 := bstep (se 1 (by rfl) ⟨575843, by rfl⟩ : syracuseStep 767791 = 1151687) B1151687
theorem B9680755 : Blo 754331 9680755 := bstep (se 1 (by rfl) ⟨7260566, by rfl⟩ : syracuseStep 9680755 = 14521133) B14521133
theorem B1817363 : Blo 754331 1817363 := bstep (se 1 (by rfl) ⟨1363022, by rfl⟩ : syracuseStep 1817363 = 2726045) B2726045
theorem B3226493 : Blo 754331 3226493 := bstep (se 3 (by rfl) ⟨604967, by rfl⟩ : syracuseStep 3226493 = 1209935) B1209935
theorem B2866063 : Blo 754331 2866063 := bstep (se 1 (by rfl) ⟨2149547, by rfl⟩ : syracuseStep 2866063 = 4299095) B4299095
theorem B9223217 : Blo 754331 9223217 := bstep (se 2 (by rfl) ⟨3458706, by rfl⟩ : syracuseStep 9223217 = 6917413) B6917413
theorem B56835125 : Blo 754331 56835125 := bstep (se 5 (by rfl) ⟨2664146, by rfl⟩ : syracuseStep 56835125 = 5328293) B5328293
theorem B8600741 : Blo 754331 8600741 := bstep (se 4 (by rfl) ⟨806319, by rfl⟩ : syracuseStep 8600741 = 1612639) B1612639
theorem B1916257 : Blo 754331 1916257 := bstep (se 2 (by rfl) ⟨718596, by rfl⟩ : syracuseStep 1916257 = 1437193) B1437193
theorem B3456443 : Blo 754331 3456443 := bstep (se 1 (by rfl) ⟨2592332, by rfl⟩ : syracuseStep 3456443 = 5184665) B5184665
theorem B3456593 : Blo 754331 3456593 := bstep (se 2 (by rfl) ⟨1296222, by rfl⟩ : syracuseStep 3456593 = 2592445) B2592445
theorem B3227465 : Blo 754331 3227465 := bstep (se 2 (by rfl) ⟨1210299, by rfl⟩ : syracuseStep 3227465 = 2420599) B2420599
theorem B1917209 : Blo 754331 1917209 := bstep (se 2 (by rfl) ⟨718953, by rfl⟩ : syracuseStep 1917209 = 1437907) B1437907
theorem B1917503 : Blo 754331 1917503 := bstep (se 1 (by rfl) ⟨1438127, by rfl⟩ : syracuseStep 1917503 = 2876255) B2876255
theorem B2048695 : Blo 754331 2048695 := bstep (se 1 (by rfl) ⟨1536521, by rfl⟩ : syracuseStep 2048695 = 3073043) B3073043
theorem B1917715 : Blo 754331 1917715 := bstep (se 1 (by rfl) ⟨1438286, by rfl⟩ : syracuseStep 1917715 = 2876573) B2876573
theorem B9192269 : Blo 754331 9192269 := bstep (se 3 (by rfl) ⟨1723550, by rfl⟩ : syracuseStep 9192269 = 3447101) B3447101
theorem B11617219 : Blo 754331 11617219 := bstep (se 1 (by rfl) ⟨8712914, by rfl⟩ : syracuseStep 11617219 = 17425829) B17425829
theorem B12469211 : Blo 754331 12469211 := bstep (se 1 (by rfl) ⟨9351908, by rfl⟩ : syracuseStep 12469211 = 18703817) B18703817
theorem B1918151 : Blo 754331 1918151 := bstep (se 1 (by rfl) ⟨1438613, by rfl⟩ : syracuseStep 1918151 = 2877227) B2877227
theorem B1918201 : Blo 754331 1918201 := bstep (se 2 (by rfl) ⟨719325, by rfl⟩ : syracuseStep 1918201 = 1438651) B1438651
theorem B1131815 : Blo 754331 1131815 := bstep (se 1 (by rfl) ⟨848861, by rfl⟩ : syracuseStep 1131815 = 1697723) B1697723
theorem B1131899 : Blo 754331 1131899 := bstep (se 1 (by rfl) ⟨848924, by rfl⟩ : syracuseStep 1131899 = 1697849) B1697849
theorem B1132025 : Blo 754331 1132025 := bstep (se 2 (by rfl) ⟨424509, by rfl⟩ : syracuseStep 1132025 = 849019) B849019
theorem B1132127 : Blo 754331 1132127 := bstep (se 1 (by rfl) ⟨849095, by rfl⟩ : syracuseStep 1132127 = 1698191) B1698191
theorem B1132343 : Blo 754331 1132343 := bstep (se 1 (by rfl) ⟨849257, by rfl⟩ : syracuseStep 1132343 = 1698515) B1698515
theorem B1918849 : Blo 754331 1918849 := bstep (se 2 (by rfl) ⟨719568, by rfl⟩ : syracuseStep 1918849 = 1439137) B1439137
theorem B1132649 : Blo 754331 1132649 := bstep (se 2 (by rfl) ⟨424743, by rfl⟩ : syracuseStep 1132649 = 849487) B849487
theorem B3230063 : Blo 754331 3230063 := bstep (se 1 (by rfl) ⟨2422547, by rfl⟩ : syracuseStep 3230063 = 4845095) B4845095
theorem B1132967 : Blo 754331 1132967 := bstep (se 1 (by rfl) ⟨849725, by rfl⟩ : syracuseStep 1132967 = 1699451) B1699451
theorem B3819959 : Blo 754331 3819959 := bstep (se 1 (by rfl) ⟨2864969, by rfl⟩ : syracuseStep 3819959 = 5729939) B5729939
theorem B4147685 : Blo 754331 4147685 := bstep (se 4 (by rfl) ⟨388845, by rfl⟩ : syracuseStep 4147685 = 777691) B777691
theorem B1133051 : Blo 754331 1133051 := bstep (se 1 (by rfl) ⟨849788, by rfl⟩ : syracuseStep 1133051 = 1699577) B1699577
theorem B1821179 : Blo 754331 1821179 := bstep (se 1 (by rfl) ⟨1365884, by rfl⟩ : syracuseStep 1821179 = 2731769) B2731769
theorem B1133177 : Blo 754331 1133177 := bstep (se 2 (by rfl) ⟨424941, by rfl⟩ : syracuseStep 1133177 = 849883) B849883
theorem B1133231 : Blo 754331 1133231 := bstep (se 1 (by rfl) ⟨849923, by rfl⟩ : syracuseStep 1133231 = 1699847) B1699847
theorem B1133279 : Blo 754331 1133279 := bstep (se 1 (by rfl) ⟨849959, by rfl⟩ : syracuseStep 1133279 = 1699919) B1699919
theorem B1133543 : Blo 754331 1133543 := bstep (se 1 (by rfl) ⟨850157, by rfl⟩ : syracuseStep 1133543 = 1700315) B1700315
theorem B1133801 : Blo 754331 1133801 := bstep (se 2 (by rfl) ⟨425175, by rfl⟩ : syracuseStep 1133801 = 850351) B850351
theorem B1133855 : Blo 754331 1133855 := bstep (se 1 (by rfl) ⟨850391, by rfl⟩ : syracuseStep 1133855 = 1700783) B1700783
theorem B1134023 : Blo 754331 1134023 := bstep (se 1 (by rfl) ⟨850517, by rfl⟩ : syracuseStep 1134023 = 1701035) B1701035
theorem B3231191 : Blo 754331 3231191 := bstep (se 1 (by rfl) ⟨2423393, by rfl⟩ : syracuseStep 3231191 = 4846787) B4846787
theorem B3067627 : Blo 754331 3067627 := bstep (se 1 (by rfl) ⟨2300720, by rfl⟩ : syracuseStep 3067627 = 4601441) B4601441
theorem B1134377 : Blo 754331 1134377 := bstep (se 2 (by rfl) ⟨425391, by rfl⟩ : syracuseStep 1134377 = 850783) B850783
theorem B10342187 : Blo 754331 10342187 := bstep (se 1 (by rfl) ⟨7756640, by rfl⟩ : syracuseStep 10342187 = 15513281) B15513281
theorem B21843755 : Blo 754331 21843755 := bstep (se 1 (by rfl) ⟨16382816, by rfl⟩ : syracuseStep 21843755 = 32765633) B32765633
theorem B1134383 : Blo 754331 1134383 := bstep (se 1 (by rfl) ⟨850787, by rfl⟩ : syracuseStep 1134383 = 1701575) B1701575
theorem B2871197 : Blo 754331 2871197 := bstep (se 3 (by rfl) ⟨538349, by rfl⟩ : syracuseStep 2871197 = 1076699) B1076699
theorem B6148163 : Blo 754331 6148163 := bstep (se 1 (by rfl) ⟨4611122, by rfl⟩ : syracuseStep 6148163 = 9222245) B9222245
theorem B1134857 : Blo 754331 1134857 := bstep (se 2 (by rfl) ⟨425571, by rfl⟩ : syracuseStep 1134857 = 851143) B851143
theorem B1134959 : Blo 754331 1134959 := bstep (se 1 (by rfl) ⟨851219, by rfl⟩ : syracuseStep 1134959 = 1702439) B1702439
theorem B1135175 : Blo 754331 1135175 := bstep (se 1 (by rfl) ⟨851381, by rfl⟩ : syracuseStep 1135175 = 1702763) B1702763
theorem B1135211 : Blo 754331 1135211 := bstep (se 1 (by rfl) ⟨851408, by rfl⟩ : syracuseStep 1135211 = 1702817) B1702817
theorem B3822227 : Blo 754331 3822227 := bstep (se 1 (by rfl) ⟨2866670, by rfl⟩ : syracuseStep 3822227 = 5733341) B5733341
theorem B1135439 : Blo 754331 1135439 := bstep (se 1 (by rfl) ⟨851579, by rfl⟩ : syracuseStep 1135439 = 1703159) B1703159
theorem B3232865 : Blo 754331 3232865 := bstep (se 2 (by rfl) ⟨1212324, by rfl⟩ : syracuseStep 3232865 = 2424649) B2424649
theorem B1135835 : Blo 754331 1135835 := bstep (se 1 (by rfl) ⟨851876, by rfl⟩ : syracuseStep 1135835 = 1703753) B1703753
theorem B5461343 : Blo 754331 5461343 := bstep (se 1 (by rfl) ⟨4096007, by rfl⟩ : syracuseStep 5461343 = 8192015) B8192015
theorem B3724649 : Blo 754331 3724649 := bstep (se 2 (by rfl) ⟨1396743, by rfl⟩ : syracuseStep 3724649 = 2793487) B2793487
theorem B2872685 : Blo 754331 2872685 := bstep (se 3 (by rfl) ⟨538628, by rfl⟩ : syracuseStep 2872685 = 1077257) B1077257
theorem B1136009 : Blo 754331 1136009 := bstep (se 2 (by rfl) ⟨426003, by rfl⟩ : syracuseStep 1136009 = 852007) B852007
theorem B3823037 : Blo 754331 3823037 := bstep (se 3 (by rfl) ⟨716819, by rfl⟩ : syracuseStep 3823037 = 1433639) B1433639
theorem B8181287 : Blo 754331 8181287 := bstep (se 1 (by rfl) ⟨6135965, by rfl⟩ : syracuseStep 8181287 = 12271931) B12271931
theorem B3233465 : Blo 754331 3233465 := bstep (se 2 (by rfl) ⟨1212549, by rfl⟩ : syracuseStep 3233465 = 2425099) B2425099
theorem B1136363 : Blo 754331 1136363 := bstep (se 1 (by rfl) ⟨852272, by rfl⟩ : syracuseStep 1136363 = 1704545) B1704545
theorem B3889079 : Blo 754331 3889079 := bstep (se 1 (by rfl) ⟨2916809, by rfl⟩ : syracuseStep 3889079 = 5833619) B5833619
theorem B1136591 : Blo 754331 1136591 := bstep (se 1 (by rfl) ⟨852443, by rfl⟩ : syracuseStep 1136591 = 1704887) B1704887
theorem B1136987 : Blo 754331 1136987 := bstep (se 1 (by rfl) ⟨852740, by rfl⟩ : syracuseStep 1136987 = 1705481) B1705481
theorem B1366483 : Blo 754331 1366483 := bstep (se 1 (by rfl) ⟨1024862, by rfl⟩ : syracuseStep 1366483 = 2049725) B2049725
theorem B1137215 : Blo 754331 1137215 := bstep (se 1 (by rfl) ⟨852911, by rfl⟩ : syracuseStep 1137215 = 1705823) B1705823
theorem B1137335 : Blo 754331 1137335 := bstep (se 1 (by rfl) ⟨853001, by rfl⟩ : syracuseStep 1137335 = 1706003) B1706003
theorem B2546423 : Blo 754331 2546423 := bstep (se 1 (by rfl) ⟨1909817, by rfl⟩ : syracuseStep 2546423 = 3819635) B3819635
theorem B6445979 : Blo 754331 6445979 := bstep (se 1 (by rfl) ⟨4834484, by rfl⟩ : syracuseStep 6445979 = 9668969) B9668969
theorem B908263 : Blo 754331 908263 := bstep (se 1 (by rfl) ⟨681197, by rfl⟩ : syracuseStep 908263 = 1362395) B1362395
theorem B2874811 : Blo 754331 2874811 := bstep (se 1 (by rfl) ⟨2156108, by rfl⟩ : syracuseStep 2874811 = 4312217) B4312217
theorem B2875115 : Blo 754331 2875115 := bstep (se 1 (by rfl) ⟨2156336, by rfl⟩ : syracuseStep 2875115 = 4312673) B4312673
theorem B1433351 : Blo 754331 1433351 := bstep (se 1 (by rfl) ⟨1075013, by rfl⟩ : syracuseStep 1433351 = 2150027) B2150027
theorem B2547503 : Blo 754331 2547503 := bstep (se 1 (by rfl) ⟨1910627, by rfl⟩ : syracuseStep 2547503 = 3821255) B3821255
theorem B2875601 : Blo 754331 2875601 := bstep (se 2 (by rfl) ⟨1078350, by rfl⟩ : syracuseStep 2875601 = 2156701) B2156701
theorem B2876057 : Blo 754331 2876057 := bstep (se 2 (by rfl) ⟨1078521, by rfl⟩ : syracuseStep 2876057 = 2157043) B2157043
theorem B6120107 : Blo 754331 6120107 := bstep (se 1 (by rfl) ⟨4590080, by rfl⟩ : syracuseStep 6120107 = 9180161) B9180161
theorem B2876087 : Blo 754331 2876087 := bstep (se 1 (by rfl) ⟨2157065, by rfl⟩ : syracuseStep 2876087 = 4314131) B4314131
theorem B7365323 : Blo 754331 7365323 := bstep (se 1 (by rfl) ⟨5523992, by rfl⟩ : syracuseStep 7365323 = 11047985) B11047985
theorem B2417627 : Blo 754331 2417627 := bstep (se 1 (by rfl) ⟨1813220, by rfl⟩ : syracuseStep 2417627 = 3626441) B3626441
theorem B3630055 : Blo 754331 3630055 := bstep (se 1 (by rfl) ⟨2722541, by rfl⟩ : syracuseStep 3630055 = 5445083) B5445083
theorem B22046053 : Blo 754331 22046053 := bstep (se 4 (by rfl) ⟨2066817, by rfl⟩ : syracuseStep 22046053 = 4133635) B4133635
theorem B1697273 : Blo 754331 1697273 := bstep (se 2 (by rfl) ⟨636477, by rfl⟩ : syracuseStep 1697273 = 1272955) B1272955
theorem B1697363 : Blo 754331 1697363 := bstep (se 1 (by rfl) ⟨1273022, by rfl⟩ : syracuseStep 1697363 = 2546045) B2546045
theorem B4843097 : Blo 754331 4843097 := bstep (se 2 (by rfl) ⟨1816161, by rfl⟩ : syracuseStep 4843097 = 3632323) B3632323
theorem B14575261 : Blo 754331 14575261 := bstep (se 3 (by rfl) ⟨2732861, by rfl⟩ : syracuseStep 14575261 = 5465723) B5465723
theorem B1697543 : Blo 754331 1697543 := bstep (se 1 (by rfl) ⟨1273157, by rfl⟩ : syracuseStep 1697543 = 2546315) B2546315
theorem B2549609 : Blo 754331 2549609 := bstep (se 2 (by rfl) ⟨956103, by rfl⟩ : syracuseStep 2549609 = 1912207) B1912207
theorem B3237839 : Blo 754331 3237839 := bstep (se 1 (by rfl) ⟨2428379, by rfl⟩ : syracuseStep 3237839 = 4856759) B4856759
theorem B16345273 : Blo 754331 16345273 := bstep (se 2 (by rfl) ⟨6129477, by rfl⟩ : syracuseStep 16345273 = 12258955) B12258955
theorem B3827897 : Blo 754331 3827897 := bstep (se 2 (by rfl) ⟨1435461, by rfl⟩ : syracuseStep 3827897 = 2870923) B2870923
theorem B2550041 : Blo 754331 2550041 := bstep (se 2 (by rfl) ⟨956265, by rfl⟩ : syracuseStep 2550041 = 1912531) B1912531
theorem B1698155 : Blo 754331 1698155 := bstep (se 1 (by rfl) ⟨1273616, by rfl⟩ : syracuseStep 1698155 = 2547233) B2547233
theorem B1698299 : Blo 754331 1698299 := bstep (se 1 (by rfl) ⟨1273724, by rfl⟩ : syracuseStep 1698299 = 2547449) B2547449
theorem B2878031 : Blo 754331 2878031 := bstep (se 1 (by rfl) ⟨2158523, by rfl⟩ : syracuseStep 2878031 = 4317047) B4317047
theorem B1436267 : Blo 754331 1436267 := bstep (se 1 (by rfl) ⟨1077200, by rfl⟩ : syracuseStep 1436267 = 2154401) B2154401
theorem B1698425 : Blo 754331 1698425 := bstep (se 2 (by rfl) ⟨636909, by rfl⟩ : syracuseStep 1698425 = 1273819) B1273819
theorem B1698479 : Blo 754331 1698479 := bstep (se 1 (by rfl) ⟨1273859, by rfl⟩ : syracuseStep 1698479 = 2547719) B2547719
theorem B1698551 : Blo 754331 1698551 := bstep (se 1 (by rfl) ⟨1273913, by rfl⟩ : syracuseStep 1698551 = 2547827) B2547827
theorem B2878199 : Blo 754331 2878199 := bstep (se 1 (by rfl) ⟨2158649, by rfl⟩ : syracuseStep 2878199 = 4317299) B4317299
theorem B3632015 : Blo 754331 3632015 := bstep (se 1 (by rfl) ⟨2724011, by rfl⟩ : syracuseStep 3632015 = 5448023) B5448023
theorem B3238811 : Blo 754331 3238811 := bstep (se 1 (by rfl) ⟨2429108, by rfl⟩ : syracuseStep 3238811 = 4858217) B4858217
theorem B1698731 : Blo 754331 1698731 := bstep (se 1 (by rfl) ⟨1274048, by rfl⟩ : syracuseStep 1698731 = 2548097) B2548097
theorem B12610637 : Blo 754331 12610637 := bstep (se 3 (by rfl) ⟨2364494, by rfl⟩ : syracuseStep 12610637 = 4728989) B4728989
theorem B10349855 : Blo 754331 10349855 := bstep (se 1 (by rfl) ⟨7762391, by rfl⟩ : syracuseStep 10349855 = 15524783) B15524783
theorem B1273225 : Blo 754331 1273225 := bstep (se 2 (by rfl) ⟨477459, by rfl⟩ : syracuseStep 1273225 = 954919) B954919
theorem B1699271 : Blo 754331 1699271 := bstep (se 1 (by rfl) ⟨1274453, by rfl⟩ : syracuseStep 1699271 = 2548907) B2548907
theorem B6909383 : Blo 754331 6909383 := bstep (se 1 (by rfl) ⟨5182037, by rfl⟩ : syracuseStep 6909383 = 10364075) B10364075
theorem B2551391 : Blo 754331 2551391 := bstep (se 1 (by rfl) ⟨1913543, by rfl⟩ : syracuseStep 2551391 = 3827087) B3827087
theorem B1699631 : Blo 754331 1699631 := bstep (se 1 (by rfl) ⟨1274723, by rfl⟩ : syracuseStep 1699631 = 2549447) B2549447
theorem B1273657 : Blo 754331 1273657 := bstep (se 2 (by rfl) ⟨477621, by rfl⟩ : syracuseStep 1273657 = 955243) B955243
theorem B1437497 : Blo 754331 1437497 := bstep (se 2 (by rfl) ⟨539061, by rfl⟩ : syracuseStep 1437497 = 1078123) B1078123
theorem B3829679 : Blo 754331 3829679 := bstep (se 1 (by rfl) ⟨2872259, by rfl⟩ : syracuseStep 3829679 = 5744519) B5744519
theorem B1273961 : Blo 754331 1273961 := bstep (se 2 (by rfl) ⟨477735, by rfl⟩ : syracuseStep 1273961 = 955471) B955471
theorem B1700207 : Blo 754331 1700207 := bstep (se 1 (by rfl) ⟨1275155, by rfl⟩ : syracuseStep 1700207 = 2550311) B2550311
theorem B1700279 : Blo 754331 1700279 := bstep (se 1 (by rfl) ⟨1275209, by rfl⟩ : syracuseStep 1700279 = 2550419) B2550419
theorem B1700423 : Blo 754331 1700423 := bstep (se 1 (by rfl) ⟨1275317, by rfl⟩ : syracuseStep 1700423 = 2550635) B2550635
theorem B1700459 : Blo 754331 1700459 := bstep (se 1 (by rfl) ⟨1275344, by rfl⟩ : syracuseStep 1700459 = 2550689) B2550689
theorem B7762553 : Blo 754331 7762553 := bstep (se 2 (by rfl) ⟨2910957, by rfl⟩ : syracuseStep 7762553 = 5821915) B5821915
theorem B2421419 : Blo 754331 2421419 := bstep (se 1 (by rfl) ⟨1816064, by rfl⟩ : syracuseStep 2421419 = 3632129) B3632129
theorem B4092767 : Blo 754331 4092767 := bstep (se 1 (by rfl) ⟨3069575, by rfl⟩ : syracuseStep 4092767 = 6139151) B6139151
theorem B2552795 : Blo 754331 2552795 := bstep (se 1 (by rfl) ⟨1914596, by rfl⟩ : syracuseStep 2552795 = 3829193) B3829193
theorem B1700855 : Blo 754331 1700855 := bstep (se 1 (by rfl) ⟨1275641, by rfl⟩ : syracuseStep 1700855 = 2551283) B2551283
theorem B2552957 : Blo 754331 2552957 := bstep (se 3 (by rfl) ⟨478679, by rfl⟩ : syracuseStep 2552957 = 957359) B957359
theorem B7271639 : Blo 754331 7271639 := bstep (se 1 (by rfl) ⟨5453729, by rfl⟩ : syracuseStep 7271639 = 10907459) B10907459
theorem B2553065 : Blo 754331 2553065 := bstep (se 2 (by rfl) ⟨957399, by rfl⟩ : syracuseStep 2553065 = 1914799) B1914799
theorem B8189207 : Blo 754331 8189207 := bstep (se 1 (by rfl) ⟨6141905, by rfl⟩ : syracuseStep 8189207 = 12283811) B12283811
theorem B1701215 : Blo 754331 1701215 := bstep (se 1 (by rfl) ⟨1275911, by rfl⟩ : syracuseStep 1701215 = 2551823) B2551823
theorem B2553227 : Blo 754331 2553227 := bstep (se 1 (by rfl) ⟨1914920, by rfl⟩ : syracuseStep 2553227 = 3829841) B3829841
theorem B1275385 : Blo 754331 1275385 := bstep (se 2 (by rfl) ⟨478269, by rfl⟩ : syracuseStep 1275385 = 956539) B956539
theorem B6452743 : Blo 754331 6452743 := bstep (se 1 (by rfl) ⟨4839557, by rfl⟩ : syracuseStep 6452743 = 9679115) B9679115
theorem B849631 : Blo 754331 849631 := bstep (se 1 (by rfl) ⟨637223, by rfl⟩ : syracuseStep 849631 = 1274447) B1274447
theorem B1701611 : Blo 754331 1701611 := bstep (se 1 (by rfl) ⟨1276208, by rfl⟩ : syracuseStep 1701611 = 2552417) B2552417
theorem B1275655 : Blo 754331 1275655 := bstep (se 1 (by rfl) ⟨956741, by rfl⟩ : syracuseStep 1275655 = 1913483) B1913483
theorem B1275689 : Blo 754331 1275689 := bstep (se 2 (by rfl) ⟨478383, by rfl⟩ : syracuseStep 1275689 = 956767) B956767
theorem B2619191 : Blo 754331 2619191 := bstep (se 1 (by rfl) ⟨1964393, by rfl⟩ : syracuseStep 2619191 = 3928787) B3928787
theorem B1701737 : Blo 754331 1701737 := bstep (se 2 (by rfl) ⟨638151, by rfl⟩ : syracuseStep 1701737 = 1276303) B1276303
theorem B850207 : Blo 754331 850207 := bstep (se 1 (by rfl) ⟨637655, by rfl⟩ : syracuseStep 850207 = 1275311) B1275311
theorem B1276411 : Blo 754331 1276411 := bstep (se 1 (by rfl) ⟨957308, by rfl⟩ : syracuseStep 1276411 = 1914617) B1914617
theorem B1309247 : Blo 754331 1309247 := bstep (se 1 (by rfl) ⟨981935, by rfl⟩ : syracuseStep 1309247 = 1963871) B1963871
theorem B850495 : Blo 754331 850495 := bstep (se 1 (by rfl) ⟨637871, by rfl⟩ : syracuseStep 850495 = 1275743) B1275743
theorem B1702583 : Blo 754331 1702583 := bstep (se 1 (by rfl) ⟨1276937, by rfl⟩ : syracuseStep 1702583 = 2553875) B2553875
theorem B3832595 : Blo 754331 3832595 := bstep (se 1 (by rfl) ⟨2874446, by rfl⟩ : syracuseStep 3832595 = 5748893) B5748893
theorem B1702799 : Blo 754331 1702799 := bstep (se 1 (by rfl) ⟨1277099, by rfl⟩ : syracuseStep 1702799 = 2554199) B2554199
theorem B1276843 : Blo 754331 1276843 := bstep (se 1 (by rfl) ⟨957632, by rfl⟩ : syracuseStep 1276843 = 1915265) B1915265
theorem B5176349 : Blo 754331 5176349 := bstep (se 3 (by rfl) ⟨970565, by rfl⟩ : syracuseStep 5176349 = 1941131) B1941131
theorem B1277147 : Blo 754331 1277147 := bstep (se 1 (by rfl) ⟨957860, by rfl⟩ : syracuseStep 1277147 = 1915721) B1915721
theorem B851323 : Blo 754331 851323 := bstep (se 1 (by rfl) ⟨638492, by rfl⟩ : syracuseStep 851323 = 1276985) B1276985
theorem B1277383 : Blo 754331 1277383 := bstep (se 1 (by rfl) ⟨958037, by rfl⟩ : syracuseStep 1277383 = 1916075) B1916075
theorem B4849247 : Blo 754331 4849247 := bstep (se 1 (by rfl) ⟨3636935, by rfl⟩ : syracuseStep 4849247 = 7273871) B7273871
theorem B1703519 : Blo 754331 1703519 := bstep (se 1 (by rfl) ⟨1277639, by rfl⟩ : syracuseStep 1703519 = 2555279) B2555279
theorem B7274099 : Blo 754331 7274099 := bstep (se 1 (by rfl) ⟨5455574, by rfl⟩ : syracuseStep 7274099 = 10911149) B10911149
theorem B1703735 : Blo 754331 1703735 := bstep (se 1 (by rfl) ⟨1277801, by rfl⟩ : syracuseStep 1703735 = 2555603) B2555603
theorem B851791 : Blo 754331 851791 := bstep (se 1 (by rfl) ⟨638843, by rfl⟩ : syracuseStep 851791 = 1277687) B1277687
theorem B9207647 : Blo 754331 9207647 := bstep (se 1 (by rfl) ⟨6905735, by rfl⟩ : syracuseStep 9207647 = 13811471) B13811471
theorem B3833729 : Blo 754331 3833729 := bstep (se 2 (by rfl) ⟨1437648, by rfl⟩ : syracuseStep 3833729 = 2875297) B2875297
theorem B1277903 : Blo 754331 1277903 := bstep (se 1 (by rfl) ⟨958427, by rfl⟩ : syracuseStep 1277903 = 1916855) B1916855
theorem B1278139 : Blo 754331 1278139 := bstep (se 1 (by rfl) ⟨958604, by rfl⟩ : syracuseStep 1278139 = 1917209) B1917209
theorem B1704167 : Blo 754331 1704167 := bstep (se 1 (by rfl) ⟨1278125, by rfl⟩ : syracuseStep 1704167 = 2556251) B2556251
theorem B1278335 : Blo 754331 1278335 := bstep (se 1 (by rfl) ⟨958751, by rfl⟩ : syracuseStep 1278335 = 1917503) B1917503
theorem B2556359 : Blo 754331 2556359 := bstep (se 1 (by rfl) ⟨1917269, by rfl⟩ : syracuseStep 2556359 = 3834539) B3834539
theorem B6128179 : Blo 754331 6128179 := bstep (se 1 (by rfl) ⟨4596134, by rfl⟩ : syracuseStep 6128179 = 9192269) B9192269
theorem B852583 : Blo 754331 852583 := bstep (se 1 (by rfl) ⟨639437, by rfl⟩ : syracuseStep 852583 = 1278875) B1278875
theorem B2556683 : Blo 754331 2556683 := bstep (se 1 (by rfl) ⟨1917512, by rfl⟩ : syracuseStep 2556683 = 3835025) B3835025
theorem B1278767 : Blo 754331 1278767 := bstep (se 1 (by rfl) ⟨959075, by rfl⟩ : syracuseStep 1278767 = 1918151) B1918151
theorem B1704761 : Blo 754331 1704761 := bstep (se 2 (by rfl) ⟨639285, by rfl⟩ : syracuseStep 1704761 = 1278571) B1278571
theorem B754543 : Blo 754331 754543 := bstep (se 1 (by rfl) ⟨565907, by rfl⟩ : syracuseStep 754543 = 1131815) B1131815
theorem B1704815 : Blo 754331 1704815 := bstep (se 1 (by rfl) ⟨1278611, by rfl⟩ : syracuseStep 1704815 = 2557223) B2557223
theorem B754599 : Blo 754331 754599 := bstep (se 1 (by rfl) ⟨565949, by rfl⟩ : syracuseStep 754599 = 1131899) B1131899
theorem B754683 : Blo 754331 754683 := bstep (se 1 (by rfl) ⟨566012, by rfl⟩ : syracuseStep 754683 = 1132025) B1132025
theorem B2556953 : Blo 754331 2556953 := bstep (se 2 (by rfl) ⟨958857, by rfl⟩ : syracuseStep 2556953 = 1917715) B1917715
theorem B754751 : Blo 754331 754751 := bstep (se 1 (by rfl) ⟨566063, by rfl⟩ : syracuseStep 754751 = 1132127) B1132127
theorem B754895 : Blo 754331 754895 := bstep (se 1 (by rfl) ⟨566171, by rfl⟩ : syracuseStep 754895 = 1132343) B1132343
theorem B10880243 : Blo 754331 10880243 := bstep (se 1 (by rfl) ⟨8160182, by rfl⟩ : syracuseStep 10880243 = 16320365) B16320365
theorem B755099 : Blo 754331 755099 := bstep (se 1 (by rfl) ⟨566324, by rfl⟩ : syracuseStep 755099 = 1132649) B1132649
theorem B1705391 : Blo 754331 1705391 := bstep (se 1 (by rfl) ⟨1279043, by rfl⟩ : syracuseStep 1705391 = 2558087) B2558087
theorem B755311 : Blo 754331 755311 := bstep (se 1 (by rfl) ⟨566483, by rfl⟩ : syracuseStep 755311 = 1132967) B1132967
theorem B2557601 : Blo 754331 2557601 := bstep (se 2 (by rfl) ⟨959100, by rfl⟩ : syracuseStep 2557601 = 1918201) B1918201
theorem B755367 : Blo 754331 755367 := bstep (se 1 (by rfl) ⟨566525, by rfl⟩ : syracuseStep 755367 = 1133051) B1133051
theorem B1214119 : Blo 754331 1214119 := bstep (se 1 (by rfl) ⟨910589, by rfl⟩ : syracuseStep 1214119 = 1821179) B1821179
theorem B755451 : Blo 754331 755451 := bstep (se 1 (by rfl) ⟨566588, by rfl⟩ : syracuseStep 755451 = 1133177) B1133177
theorem B6457117 : Blo 754331 6457117 := bstep (se 3 (by rfl) ⟨1210709, by rfl⟩ : syracuseStep 6457117 = 2421419) B2421419
theorem B755487 : Blo 754331 755487 := bstep (se 1 (by rfl) ⟨566615, by rfl⟩ : syracuseStep 755487 = 1133231) B1133231
theorem B29394737 : Blo 754331 29394737 := bstep (se 2 (by rfl) ⟨11023026, by rfl⟩ : syracuseStep 29394737 = 22046053) B22046053
theorem B755519 : Blo 754331 755519 := bstep (se 1 (by rfl) ⟨566639, by rfl⟩ : syracuseStep 755519 = 1133279) B1133279
theorem B5244751 : Blo 754331 5244751 := bstep (se 1 (by rfl) ⟨3933563, by rfl⟩ : syracuseStep 5244751 = 7867127) B7867127
theorem B755695 : Blo 754331 755695 := bstep (se 1 (by rfl) ⟨566771, by rfl⟩ : syracuseStep 755695 = 1133543) B1133543
theorem B755867 : Blo 754331 755867 := bstep (se 1 (by rfl) ⟨566900, by rfl⟩ : syracuseStep 755867 = 1133801) B1133801
theorem B755903 : Blo 754331 755903 := bstep (se 1 (by rfl) ⟨566927, by rfl⟩ : syracuseStep 755903 = 1133855) B1133855
theorem B19433681 : Blo 754331 19433681 := bstep (se 2 (by rfl) ⟨7287630, by rfl⟩ : syracuseStep 19433681 = 14575261) B14575261
theorem B1706219 : Blo 754331 1706219 := bstep (se 1 (by rfl) ⟨1279664, by rfl⟩ : syracuseStep 1706219 = 2559329) B2559329
theorem B756015 : Blo 754331 756015 := bstep (se 1 (by rfl) ⟨567011, by rfl⟩ : syracuseStep 756015 = 1134023) B1134023
theorem B2558303 : Blo 754331 2558303 := bstep (se 1 (by rfl) ⟨1918727, by rfl⟩ : syracuseStep 2558303 = 3837455) B3837455
theorem B4852169 : Blo 754331 4852169 := bstep (se 2 (by rfl) ⟨1819563, by rfl⟩ : syracuseStep 4852169 = 3639127) B3639127
theorem B2558465 : Blo 754331 2558465 := bstep (se 2 (by rfl) ⟨959424, by rfl⟩ : syracuseStep 2558465 = 1918849) B1918849
theorem B756251 : Blo 754331 756251 := bstep (se 1 (by rfl) ⟨567188, by rfl⟩ : syracuseStep 756251 = 1134377) B1134377
theorem B756255 : Blo 754331 756255 := bstep (se 1 (by rfl) ⟨567191, by rfl⟩ : syracuseStep 756255 = 1134383) B1134383
theorem B5311115 : Blo 754331 5311115 := bstep (se 1 (by rfl) ⟨3983336, by rfl⟩ : syracuseStep 5311115 = 7966673) B7966673
theorem B4098775 : Blo 754331 4098775 := bstep (se 1 (by rfl) ⟨3074081, by rfl⟩ : syracuseStep 4098775 = 6148163) B6148163
theorem B756571 : Blo 754331 756571 := bstep (se 1 (by rfl) ⟨567428, by rfl⟩ : syracuseStep 756571 = 1134857) B1134857
theorem B756639 : Blo 754331 756639 := bstep (se 1 (by rfl) ⟨567479, by rfl⟩ : syracuseStep 756639 = 1134959) B1134959
theorem B21793697 : Blo 754331 21793697 := bstep (se 2 (by rfl) ⟨8172636, by rfl⟩ : syracuseStep 21793697 = 16345273) B16345273
theorem B2296795 : Blo 754331 2296795 := bstep (se 1 (by rfl) ⟨1722596, by rfl⟩ : syracuseStep 2296795 = 3445193) B3445193
theorem B2558951 : Blo 754331 2558951 := bstep (se 1 (by rfl) ⟨1919213, by rfl⟩ : syracuseStep 2558951 = 3838427) B3838427
theorem B756783 : Blo 754331 756783 := bstep (se 1 (by rfl) ⟨567587, by rfl⟩ : syracuseStep 756783 = 1135175) B1135175
theorem B756807 : Blo 754331 756807 := bstep (se 1 (by rfl) ⟨567605, by rfl⟩ : syracuseStep 756807 = 1135211) B1135211
theorem B10325069 : Blo 754331 10325069 := bstep (se 3 (by rfl) ⟨1935950, by rfl⟩ : syracuseStep 10325069 = 3871901) B3871901
theorem B756959 : Blo 754331 756959 := bstep (se 1 (by rfl) ⟨567719, by rfl⟩ : syracuseStep 756959 = 1135439) B1135439
theorem B2559275 : Blo 754331 2559275 := bstep (se 1 (by rfl) ⟨1919456, by rfl⟩ : syracuseStep 2559275 = 3838913) B3838913
theorem B757223 : Blo 754331 757223 := bstep (se 1 (by rfl) ⟨567917, by rfl⟩ : syracuseStep 757223 = 1135835) B1135835
theorem B3640895 : Blo 754331 3640895 := bstep (se 1 (by rfl) ⟨2730671, by rfl⟩ : syracuseStep 3640895 = 5461343) B5461343
theorem B757339 : Blo 754331 757339 := bstep (se 1 (by rfl) ⟨568004, by rfl⟩ : syracuseStep 757339 = 1136009) B1136009
theorem B757575 : Blo 754331 757575 := bstep (se 1 (by rfl) ⟨568181, by rfl⟩ : syracuseStep 757575 = 1136363) B1136363
theorem B2592719 : Blo 754331 2592719 := bstep (se 1 (by rfl) ⟨1944539, by rfl⟩ : syracuseStep 2592719 = 3889079) B3889079
theorem B757727 : Blo 754331 757727 := bstep (se 1 (by rfl) ⟨568295, by rfl⟩ : syracuseStep 757727 = 1136591) B1136591
theorem B2723969 : Blo 754331 2723969 := bstep (se 2 (by rfl) ⟨1021488, by rfl⟩ : syracuseStep 2723969 = 2042977) B2042977
theorem B757991 : Blo 754331 757991 := bstep (se 1 (by rfl) ⟨568493, by rfl⟩ : syracuseStep 757991 = 1136987) B1136987
theorem B758143 : Blo 754331 758143 := bstep (se 1 (by rfl) ⟨568607, by rfl⟩ : syracuseStep 758143 = 1137215) B1137215
theorem B20648357 : Blo 754331 20648357 := bstep (se 4 (by rfl) ⟨1935783, by rfl⟩ : syracuseStep 20648357 = 3871567) B3871567
theorem B758223 : Blo 754331 758223 := bstep (se 1 (by rfl) ⟨568667, by rfl⟩ : syracuseStep 758223 = 1137335) B1137335
theorem B4297319 : Blo 754331 4297319 := bstep (se 1 (by rfl) ⟨3222989, by rfl⟩ : syracuseStep 4297319 = 6445979) B6445979
theorem B4920323 : Blo 754331 4920323 := bstep (se 1 (by rfl) ⟨3690242, by rfl⟩ : syracuseStep 4920323 = 7380485) B7380485
theorem B3937319 : Blo 754331 3937319 := bstep (se 1 (by rfl) ⟨2952989, by rfl⟩ : syracuseStep 3937319 = 5905979) B5905979
theorem B9311377 : Blo 754331 9311377 := bstep (se 2 (by rfl) ⟨3491766, by rfl⟩ : syracuseStep 9311377 = 6983533) B6983533
theorem B955567 : Blo 754331 955567 := bstep (se 1 (by rfl) ⟨716675, by rfl⟩ : syracuseStep 955567 = 1433351) B1433351
theorem B4298093 : Blo 754331 4298093 := bstep (se 3 (by rfl) ⟨805892, by rfl⟩ : syracuseStep 4298093 = 1611785) B1611785
theorem B1971611 : Blo 754331 1971611 := bstep (se 1 (by rfl) ⟨1478708, by rfl⟩ : syracuseStep 1971611 = 2957417) B2957417
theorem B1611751 : Blo 754331 1611751 := bstep (se 1 (by rfl) ⟨1208813, by rfl⟩ : syracuseStep 1611751 = 2417627) B2417627
theorem B4298777 : Blo 754331 4298777 := bstep (se 2 (by rfl) ⟨1612041, by rfl⟩ : syracuseStep 4298777 = 3224083) B3224083
theorem B22124609 : Blo 754331 22124609 := bstep (se 2 (by rfl) ⟨8296728, by rfl⟩ : syracuseStep 22124609 = 16593457) B16593457
theorem B957511 : Blo 754331 957511 := bstep (se 1 (by rfl) ⟨718133, by rfl⟩ : syracuseStep 957511 = 1436267) B1436267
theorem B9182735 : Blo 754331 9182735 := bstep (se 1 (by rfl) ⟨6887051, by rfl⟩ : syracuseStep 9182735 = 13774103) B13774103
theorem B9182929 : Blo 754331 9182929 := bstep (se 2 (by rfl) ⟨3443598, by rfl⟩ : syracuseStep 9182929 = 6887197) B6887197
theorem B1023721 : Blo 754331 1023721 := bstep (se 2 (by rfl) ⟨383895, by rfl⟩ : syracuseStep 1023721 = 767791) B767791
theorem B2301767 : Blo 754331 2301767 := bstep (se 1 (by rfl) ⟨1726325, by rfl⟩ : syracuseStep 2301767 = 3452651) B3452651
theorem B958331 : Blo 754331 958331 := bstep (se 1 (by rfl) ⟨718748, by rfl⟩ : syracuseStep 958331 = 1437497) B1437497
theorem B8593451 : Blo 754331 8593451 := bstep (se 1 (by rfl) ⟨6445088, by rfl⟩ : syracuseStep 8593451 = 12890177) B12890177
theorem B2728511 : Blo 754331 2728511 := bstep (se 1 (by rfl) ⟨2046383, by rfl⟩ : syracuseStep 2728511 = 4092767) B4092767
theorem B2302739 : Blo 754331 2302739 := bstep (se 1 (by rfl) ⟨1727054, by rfl⟩ : syracuseStep 2302739 = 3454109) B3454109
theorem B1909615 : Blo 754331 1909615 := bstep (se 1 (by rfl) ⟨1432211, by rfl⟩ : syracuseStep 1909615 = 2864423) B2864423
theorem B861247 : Blo 754331 861247 := bstep (se 1 (by rfl) ⟨645935, by rfl⟩ : syracuseStep 861247 = 1291871) B1291871
theorem B1746127 : Blo 754331 1746127 := bstep (se 1 (by rfl) ⟨1309595, by rfl⟩ : syracuseStep 1746127 = 2619191) B2619191
theorem B3450899 : Blo 754331 3450899 := bstep (se 1 (by rfl) ⟨2588174, by rfl⟩ : syracuseStep 3450899 = 5176349) B5176349
theorem B37890083 : Blo 754331 37890083 := bstep (se 1 (by rfl) ⟨28417562, by rfl⟩ : syracuseStep 37890083 = 56835125) B56835125
theorem B2304295 : Blo 754331 2304295 := bstep (se 1 (by rfl) ⟨1728221, by rfl⟩ : syracuseStep 2304295 = 3456443) B3456443
theorem B2304395 : Blo 754331 2304395 := bstep (se 1 (by rfl) ⟨1728296, by rfl⟩ : syracuseStep 2304395 = 3456593) B3456593
theorem B6138431 : Blo 754331 6138431 := bstep (se 1 (by rfl) ⟨4603823, by rfl⟩ : syracuseStep 6138431 = 9207647) B9207647
theorem B2239721 : Blo 754331 2239721 := bstep (se 2 (by rfl) ⟨839895, by rfl⟩ : syracuseStep 2239721 = 1679791) B1679791
theorem B3452489 : Blo 754331 3452489 := bstep (se 2 (by rfl) ⟨1294683, by rfl⟩ : syracuseStep 3452489 = 2589367) B2589367
theorem B6467849 : Blo 754331 6467849 := bstep (se 2 (by rfl) ⟨2425443, by rfl⟩ : syracuseStep 6467849 = 4850887) B4850887
theorem B2765123 : Blo 754331 2765123 := bstep (se 1 (by rfl) ⟨2073842, by rfl⟩ : syracuseStep 2765123 = 4147685) B4147685
theorem B23245163 : Blo 754331 23245163 := bstep (se 1 (by rfl) ⟨17433872, by rfl⟩ : syracuseStep 23245163 = 34867745) B34867745
theorem B1618535 : Blo 754331 1618535 := bstep (se 1 (by rfl) ⟨1213901, by rfl⟩ : syracuseStep 1618535 = 2427803) B2427803
theorem B1815547 : Blo 754331 1815547 := bstep (se 1 (by rfl) ⟨1361660, by rfl⟩ : syracuseStep 1815547 = 2723321) B2723321
theorem B6894791 : Blo 754331 6894791 := bstep (se 1 (by rfl) ⟨5171093, by rfl⟩ : syracuseStep 6894791 = 10342187) B10342187
theorem B14562503 : Blo 754331 14562503 := bstep (se 1 (by rfl) ⟨10921877, by rfl⟩ : syracuseStep 14562503 = 21843755) B21843755
theorem B1914131 : Blo 754331 1914131 := bstep (se 1 (by rfl) ⟨1435598, by rfl⟩ : syracuseStep 1914131 = 2871197) B2871197
theorem B4306567 : Blo 754331 4306567 := bstep (se 1 (by rfl) ⟨3229925, by rfl⟩ : syracuseStep 4306567 = 6459851) B6459851
theorem B5748407 : Blo 754331 5748407 := bstep (se 1 (by rfl) ⟨4311305, by rfl⟩ : syracuseStep 5748407 = 8622611) B8622611
theorem B2865091 : Blo 754331 2865091 := bstep (se 1 (by rfl) ⟨2148818, by rfl⟩ : syracuseStep 2865091 = 4297637) B4297637
theorem B1915123 : Blo 754331 1915123 := bstep (se 1 (by rfl) ⟨1436342, by rfl⟩ : syracuseStep 1915123 = 2872685) B2872685
theorem B10926373 : Blo 754331 10926373 := bstep (se 4 (by rfl) ⟨1024347, by rfl⟩ : syracuseStep 10926373 = 2048695) B2048695
theorem B5454191 : Blo 754331 5454191 := bstep (se 1 (by rfl) ⟨4090643, by rfl⟩ : syracuseStep 5454191 = 8181287) B8181287
theorem B9682091 : Blo 754331 9682091 := bstep (se 1 (by rfl) ⟨7261568, by rfl⟩ : syracuseStep 9682091 = 14523137) B14523137
theorem B1916743 : Blo 754331 1916743 := bstep (se 1 (by rfl) ⟨1437557, by rfl⟩ : syracuseStep 1916743 = 2875115) B2875115
theorem B2867339 : Blo 754331 2867339 := bstep (se 1 (by rfl) ⟨2150504, by rfl⟩ : syracuseStep 2867339 = 4301009) B4301009
theorem B1917067 : Blo 754331 1917067 := bstep (se 1 (by rfl) ⟨1437800, by rfl⟩ : syracuseStep 1917067 = 2875601) B2875601
theorem B12894551 : Blo 754331 12894551 := bstep (se 1 (by rfl) ⟨9670913, by rfl⟩ : syracuseStep 12894551 = 19341827) B19341827
theorem B1360255 : Blo 754331 1360255 := bstep (se 1 (by rfl) ⟨1020191, by rfl⟩ : syracuseStep 1360255 = 2040383) B2040383
theorem B1917371 : Blo 754331 1917371 := bstep (se 1 (by rfl) ⟨1438028, by rfl⟩ : syracuseStep 1917371 = 2876057) B2876057
theorem B4080071 : Blo 754331 4080071 := bstep (se 1 (by rfl) ⟨3060053, by rfl⟩ : syracuseStep 4080071 = 6120107) B6120107
theorem B1917391 : Blo 754331 1917391 := bstep (se 1 (by rfl) ⟨1438043, by rfl⟩ : syracuseStep 1917391 = 2876087) B2876087
theorem B1131515 : Blo 754331 1131515 := bstep (se 1 (by rfl) ⟨848636, by rfl⟩ : syracuseStep 1131515 = 1697273) B1697273
theorem B1131575 : Blo 754331 1131575 := bstep (se 1 (by rfl) ⟨848681, by rfl⟩ : syracuseStep 1131575 = 1697363) B1697363
theorem B3228731 : Blo 754331 3228731 := bstep (se 1 (by rfl) ⟨2421548, by rfl⟩ : syracuseStep 3228731 = 4843097) B4843097
theorem B1131695 : Blo 754331 1131695 := bstep (se 1 (by rfl) ⟨848771, by rfl⟩ : syracuseStep 1131695 = 1697543) B1697543
theorem B23250199 : Blo 754331 23250199 := bstep (se 1 (by rfl) ⟨17437649, by rfl⟩ : syracuseStep 23250199 = 34875299) B34875299
theorem B3818825 : Blo 754331 3818825 := bstep (se 2 (by rfl) ⟨1432059, by rfl⟩ : syracuseStep 3818825 = 2864119) B2864119
theorem B7259645 : Blo 754331 7259645 := bstep (se 3 (by rfl) ⟨1361183, by rfl⟩ : syracuseStep 7259645 = 2722367) B2722367
theorem B1132103 : Blo 754331 1132103 := bstep (se 1 (by rfl) ⟨849077, by rfl⟩ : syracuseStep 1132103 = 1698155) B1698155
theorem B1132199 : Blo 754331 1132199 := bstep (se 1 (by rfl) ⟨849149, by rfl⟩ : syracuseStep 1132199 = 1698299) B1698299
theorem B1918687 : Blo 754331 1918687 := bstep (se 1 (by rfl) ⟨1439015, by rfl⟩ : syracuseStep 1918687 = 2878031) B2878031
theorem B1132283 : Blo 754331 1132283 := bstep (se 1 (by rfl) ⟨849212, by rfl⟩ : syracuseStep 1132283 = 1698425) B1698425
theorem B1132319 : Blo 754331 1132319 := bstep (se 1 (by rfl) ⟨849239, by rfl⟩ : syracuseStep 1132319 = 1698479) B1698479
theorem B1132367 : Blo 754331 1132367 := bstep (se 1 (by rfl) ⟨849275, by rfl⟩ : syracuseStep 1132367 = 1698551) B1698551
theorem B1918799 : Blo 754331 1918799 := bstep (se 1 (by rfl) ⟨1439099, by rfl⟩ : syracuseStep 1918799 = 2878199) B2878199
theorem B2148295 : Blo 754331 2148295 := bstep (se 1 (by rfl) ⟨1611221, by rfl⟩ : syracuseStep 2148295 = 3222443) B3222443
theorem B1132487 : Blo 754331 1132487 := bstep (se 1 (by rfl) ⟨849365, by rfl⟩ : syracuseStep 1132487 = 1698731) B1698731
theorem B8603657 : Blo 754331 8603657 := bstep (se 2 (by rfl) ⟨3226371, by rfl⟩ : syracuseStep 8603657 = 6452743) B6452743
theorem B8407091 : Blo 754331 8407091 := bstep (se 1 (by rfl) ⟨6305318, by rfl⟩ : syracuseStep 8407091 = 12610637) B12610637
theorem B6899903 : Blo 754331 6899903 := bstep (se 1 (by rfl) ⟨5174927, by rfl⟩ : syracuseStep 6899903 = 10349855) B10349855
theorem B1132841 : Blo 754331 1132841 := bstep (se 2 (by rfl) ⟨424815, by rfl⟩ : syracuseStep 1132841 = 849631) B849631
theorem B1132847 : Blo 754331 1132847 := bstep (se 1 (by rfl) ⟨849635, by rfl⟩ : syracuseStep 1132847 = 1699271) B1699271
theorem B4606255 : Blo 754331 4606255 := bstep (se 1 (by rfl) ⟨3454691, by rfl⟩ : syracuseStep 4606255 = 6909383) B6909383
theorem B1133087 : Blo 754331 1133087 := bstep (se 1 (by rfl) ⟨849815, by rfl⟩ : syracuseStep 1133087 = 1699631) B1699631
theorem B1133471 : Blo 754331 1133471 := bstep (se 1 (by rfl) ⟨850103, by rfl⟩ : syracuseStep 1133471 = 1700207) B1700207
theorem B1133519 : Blo 754331 1133519 := bstep (se 1 (by rfl) ⟨850139, by rfl⟩ : syracuseStep 1133519 = 1700279) B1700279
theorem B2149355 : Blo 754331 2149355 := bstep (se 1 (by rfl) ⟨1612016, by rfl⟩ : syracuseStep 2149355 = 3224033) B3224033
theorem B1133609 : Blo 754331 1133609 := bstep (se 2 (by rfl) ⟨425103, by rfl⟩ : syracuseStep 1133609 = 850207) B850207
theorem B1133615 : Blo 754331 1133615 := bstep (se 1 (by rfl) ⟨850211, by rfl⟩ : syracuseStep 1133615 = 1700423) B1700423
theorem B1133639 : Blo 754331 1133639 := bstep (se 1 (by rfl) ⟨850229, by rfl⟩ : syracuseStep 1133639 = 1700459) B1700459
theorem B1821977 : Blo 754331 1821977 := bstep (se 2 (by rfl) ⟨683241, by rfl⟩ : syracuseStep 1821977 = 1366483) B1366483
theorem B1133903 : Blo 754331 1133903 := bstep (se 1 (by rfl) ⟨850427, by rfl⟩ : syracuseStep 1133903 = 1700855) B1700855
theorem B4312399 : Blo 754331 4312399 := bstep (se 1 (by rfl) ⟨3234299, by rfl⟩ : syracuseStep 4312399 = 6468599) B6468599
theorem B1133993 : Blo 754331 1133993 := bstep (se 2 (by rfl) ⟨425247, by rfl⟩ : syracuseStep 1133993 = 850495) B850495
theorem B2870711 : Blo 754331 2870711 := bstep (se 1 (by rfl) ⟨2153033, by rfl⟩ : syracuseStep 2870711 = 4306067) B4306067
theorem B3067319 : Blo 754331 3067319 := bstep (se 1 (by rfl) ⟨2300489, by rfl⟩ : syracuseStep 3067319 = 4600979) B4600979
theorem B5459471 : Blo 754331 5459471 := bstep (se 1 (by rfl) ⟨4094603, by rfl⟩ : syracuseStep 5459471 = 8189207) B8189207
theorem B1134143 : Blo 754331 1134143 := bstep (se 1 (by rfl) ⟨850607, by rfl⟩ : syracuseStep 1134143 = 1701215) B1701215
theorem B1134407 : Blo 754331 1134407 := bstep (se 1 (by rfl) ⟨850805, by rfl⟩ : syracuseStep 1134407 = 1701611) B1701611
theorem B3821417 : Blo 754331 3821417 := bstep (se 2 (by rfl) ⟨1433031, by rfl⟩ : syracuseStep 3821417 = 2866063) B2866063
theorem B1134491 : Blo 754331 1134491 := bstep (se 1 (by rfl) ⟨850868, by rfl⟩ : syracuseStep 1134491 = 1701737) B1701737
theorem B872831 : Blo 754331 872831 := bstep (se 1 (by rfl) ⟨654623, by rfl⟩ : syracuseStep 872831 = 1309247) B1309247
theorem B1135055 : Blo 754331 1135055 := bstep (se 1 (by rfl) ⟨851291, by rfl⟩ : syracuseStep 1135055 = 1702583) B1702583
theorem B1135097 : Blo 754331 1135097 := bstep (se 2 (by rfl) ⟨425661, by rfl⟩ : syracuseStep 1135097 = 851323) B851323
theorem B2150995 : Blo 754331 2150995 := bstep (se 1 (by rfl) ⟨1613246, by rfl⟩ : syracuseStep 2150995 = 3226493) B3226493
theorem B1135199 : Blo 754331 1135199 := bstep (se 1 (by rfl) ⟨851399, by rfl⟩ : syracuseStep 1135199 = 1702799) B1702799
theorem B6148811 : Blo 754331 6148811 := bstep (se 1 (by rfl) ⟨4611608, by rfl⟩ : syracuseStep 6148811 = 9223217) B9223217
theorem B8606573 : Blo 754331 8606573 := bstep (se 3 (by rfl) ⟨1613732, by rfl⟩ : syracuseStep 8606573 = 3227465) B3227465
theorem B3232831 : Blo 754331 3232831 := bstep (se 1 (by rfl) ⟨2424623, by rfl⟩ : syracuseStep 3232831 = 4849247) B4849247
theorem B1135679 : Blo 754331 1135679 := bstep (se 1 (by rfl) ⟨851759, by rfl⟩ : syracuseStep 1135679 = 1703519) B1703519
theorem B1135721 : Blo 754331 1135721 := bstep (se 2 (by rfl) ⟨425895, by rfl⟩ : syracuseStep 1135721 = 851791) B851791
theorem B1135823 : Blo 754331 1135823 := bstep (se 1 (by rfl) ⟨851867, by rfl⟩ : syracuseStep 1135823 = 1703735) B1703735
theorem B1725851 : Blo 754331 1725851 := bstep (se 1 (by rfl) ⟨1294388, by rfl⟩ : syracuseStep 1725851 = 2588777) B2588777
theorem B1136027 : Blo 754331 1136027 := bstep (se 1 (by rfl) ⟨852020, by rfl⟩ : syracuseStep 1136027 = 1704041) B1704041
theorem B1136249 : Blo 754331 1136249 := bstep (se 2 (by rfl) ⟨426093, by rfl⟩ : syracuseStep 1136249 = 852187) B852187
theorem B1136351 : Blo 754331 1136351 := bstep (se 1 (by rfl) ⟨852263, by rfl⟩ : syracuseStep 1136351 = 1704527) B1704527
theorem B1136447 : Blo 754331 1136447 := bstep (se 1 (by rfl) ⟨852335, by rfl⟩ : syracuseStep 1136447 = 1704671) B1704671
theorem B8312807 : Blo 754331 8312807 := bstep (se 1 (by rfl) ⟨6234605, by rfl⟩ : syracuseStep 8312807 = 12469211) B12469211
theorem B1136615 : Blo 754331 1136615 := bstep (se 1 (by rfl) ⟨852461, by rfl⟩ : syracuseStep 1136615 = 1704923) B1704923
theorem B1136633 : Blo 754331 1136633 := bstep (se 2 (by rfl) ⟨426237, by rfl⟩ : syracuseStep 1136633 = 852475) B852475
theorem B1136735 : Blo 754331 1136735 := bstep (se 1 (by rfl) ⟨852551, by rfl⟩ : syracuseStep 1136735 = 1705103) B1705103
theorem B3692639 : Blo 754331 3692639 := bstep (se 1 (by rfl) ⟨2769479, by rfl⟩ : syracuseStep 3692639 = 5538959) B5538959
theorem B1136795 : Blo 754331 1136795 := bstep (se 1 (by rfl) ⟨852596, by rfl⟩ : syracuseStep 1136795 = 1705193) B1705193
theorem B1136831 : Blo 754331 1136831 := bstep (se 1 (by rfl) ⟨852623, by rfl⟩ : syracuseStep 1136831 = 1705247) B1705247
theorem B1136873 : Blo 754331 1136873 := bstep (se 2 (by rfl) ⟨426327, by rfl⟩ : syracuseStep 1136873 = 852655) B852655
theorem B1137179 : Blo 754331 1137179 := bstep (se 1 (by rfl) ⟨852884, by rfl⟩ : syracuseStep 1137179 = 1705769) B1705769
theorem B15489625 : Blo 754331 15489625 := bstep (se 2 (by rfl) ⟨5808609, by rfl⟩ : syracuseStep 15489625 = 11617219) B11617219
theorem B1137257 : Blo 754331 1137257 := bstep (se 2 (by rfl) ⟨426471, by rfl⟩ : syracuseStep 1137257 = 852943) B852943
theorem B4840073 : Blo 754331 4840073 := bstep (se 2 (by rfl) ⟨1815027, by rfl⟩ : syracuseStep 4840073 = 3630055) B3630055
theorem B29547341 : Blo 754331 29547341 := bstep (se 3 (by rfl) ⟨5540126, by rfl⟩ : syracuseStep 29547341 = 11080253) B11080253
theorem B2153375 : Blo 754331 2153375 := bstep (se 1 (by rfl) ⟨1615031, by rfl⟩ : syracuseStep 2153375 = 3230063) B3230063
theorem B2546639 : Blo 754331 2546639 := bstep (se 1 (by rfl) ⟨1909979, by rfl⟩ : syracuseStep 2546639 = 3819959) B3819959
theorem B2154127 : Blo 754331 2154127 := bstep (se 1 (by rfl) ⟨1615595, by rfl⟩ : syracuseStep 2154127 = 3231191) B3231191
theorem B7364461 : Blo 754331 7364461 := bstep (se 3 (by rfl) ⟨1380836, by rfl⟩ : syracuseStep 7364461 = 2761673) B2761673
theorem B2548151 : Blo 754331 2548151 := bstep (se 1 (by rfl) ⟨1911113, by rfl⟩ : syracuseStep 2548151 = 3822227) B3822227
theorem B2155243 : Blo 754331 2155243 := bstep (se 1 (by rfl) ⟨1616432, by rfl⟩ : syracuseStep 2155243 = 3232865) B3232865
theorem B2483099 : Blo 754331 2483099 := bstep (se 1 (by rfl) ⟨1862324, by rfl⟩ : syracuseStep 2483099 = 3724649) B3724649
theorem B2548637 : Blo 754331 2548637 := bstep (se 3 (by rfl) ⟨477869, by rfl⟩ : syracuseStep 2548637 = 955739) B955739
theorem B2548691 : Blo 754331 2548691 := bstep (se 1 (by rfl) ⟨1911518, by rfl⟩ : syracuseStep 2548691 = 3823037) B3823037
theorem B2155643 : Blo 754331 2155643 := bstep (se 1 (by rfl) ⟨1616732, by rfl⟩ : syracuseStep 2155643 = 3233465) B3233465
theorem B13821101 : Blo 754331 13821101 := bstep (se 3 (by rfl) ⟨2591456, by rfl⟩ : syracuseStep 13821101 = 5182913) B5182913
theorem B2418473 : Blo 754331 2418473 := bstep (se 2 (by rfl) ⟨906927, by rfl⟩ : syracuseStep 2418473 = 1813855) B1813855
theorem B1697615 : Blo 754331 1697615 := bstep (se 1 (by rfl) ⟨1273211, by rfl⟩ : syracuseStep 1697615 = 2546423) B2546423
theorem B1697633 : Blo 754331 1697633 := bstep (se 2 (by rfl) ⟨636612, by rfl⟩ : syracuseStep 1697633 = 1273225) B1273225
theorem B1534187 : Blo 754331 1534187 := bstep (se 1 (by rfl) ⟨1150640, by rfl⟩ : syracuseStep 1534187 = 2301281) B2301281
theorem B4090169 : Blo 754331 4090169 := bstep (se 2 (by rfl) ⟨1533813, by rfl⟩ : syracuseStep 4090169 = 3067627) B3067627
theorem B3631499 : Blo 754331 3631499 := bstep (se 1 (by rfl) ⟨2723624, by rfl⟩ : syracuseStep 3631499 = 5447249) B5447249
theorem B1698209 : Blo 754331 1698209 := bstep (se 2 (by rfl) ⟨636828, by rfl⟩ : syracuseStep 1698209 = 1273657) B1273657
theorem B1698335 : Blo 754331 1698335 := bstep (se 1 (by rfl) ⟨1273751, by rfl⟩ : syracuseStep 1698335 = 2547503) B2547503
theorem B4844069 : Blo 754331 4844069 := bstep (se 4 (by rfl) ⟨454131, by rfl⟩ : syracuseStep 4844069 = 908263) B908263
theorem B2550905 : Blo 754331 2550905 := bstep (se 2 (by rfl) ⟨956589, by rfl⟩ : syracuseStep 2550905 = 1913179) B1913179
theorem B4910215 : Blo 754331 4910215 := bstep (se 1 (by rfl) ⟨3682661, by rfl⟩ : syracuseStep 4910215 = 7365323) B7365323
theorem B1273097 : Blo 754331 1273097 := bstep (se 2 (by rfl) ⟨477411, by rfl⟩ : syracuseStep 1273097 = 954823) B954823
theorem B1076591 : Blo 754331 1076591 := bstep (se 1 (by rfl) ⟨807443, by rfl⟩ : syracuseStep 1076591 = 1614887) B1614887
theorem B2551229 : Blo 754331 2551229 := bstep (se 3 (by rfl) ⟨478355, by rfl⟩ : syracuseStep 2551229 = 956711) B956711
theorem B1699739 : Blo 754331 1699739 := bstep (se 1 (by rfl) ⟨1274804, by rfl⟩ : syracuseStep 1699739 = 2549609) B2549609
theorem B2158559 : Blo 754331 2158559 := bstep (se 1 (by rfl) ⟨1618919, by rfl⟩ : syracuseStep 2158559 = 3237839) B3237839
theorem B2551931 : Blo 754331 2551931 := bstep (se 1 (by rfl) ⟨1913948, by rfl⟩ : syracuseStep 2551931 = 3827897) B3827897
theorem B1700027 : Blo 754331 1700027 := bstep (se 1 (by rfl) ⟨1275020, by rfl⟩ : syracuseStep 1700027 = 2550041) B2550041
theorem B2552093 : Blo 754331 2552093 := bstep (se 3 (by rfl) ⟨478517, by rfl⟩ : syracuseStep 2552093 = 957035) B957035
theorem B1274143 : Blo 754331 1274143 := bstep (se 1 (by rfl) ⟨955607, by rfl⟩ : syracuseStep 1274143 = 1911215) B1911215
theorem B2552201 : Blo 754331 2552201 := bstep (se 2 (by rfl) ⟨957075, by rfl⟩ : syracuseStep 2552201 = 1914151) B1914151
theorem B2421343 : Blo 754331 2421343 := bstep (se 1 (by rfl) ⟨1816007, by rfl⟩ : syracuseStep 2421343 = 3632015) B3632015
theorem B2159207 : Blo 754331 2159207 := bstep (se 1 (by rfl) ⟨1619405, by rfl⟩ : syracuseStep 2159207 = 3238811) B3238811
theorem B1700513 : Blo 754331 1700513 := bstep (se 2 (by rfl) ⟨637692, by rfl⟩ : syracuseStep 1700513 = 1275385) B1275385
theorem B4846301 : Blo 754331 4846301 := bstep (se 3 (by rfl) ⟨908681, by rfl⟩ : syracuseStep 4846301 = 1817363) B1817363
theorem B1274791 : Blo 754331 1274791 := bstep (se 1 (by rfl) ⟨956093, by rfl⟩ : syracuseStep 1274791 = 1912187) B1912187
theorem B9204725 : Blo 754331 9204725 := bstep (se 5 (by rfl) ⟨431471, by rfl⟩ : syracuseStep 9204725 = 862943) B862943
theorem B1700873 : Blo 754331 1700873 := bstep (se 2 (by rfl) ⟨637827, by rfl⟩ : syracuseStep 1700873 = 1275655) B1275655
theorem B1700927 : Blo 754331 1700927 := bstep (se 1 (by rfl) ⟨1275695, by rfl⟩ : syracuseStep 1700927 = 2551391) B2551391
theorem B1274953 : Blo 754331 1274953 := bstep (se 2 (by rfl) ⟨478107, by rfl⟩ : syracuseStep 1274953 = 956215) B956215
theorem B1274987 : Blo 754331 1274987 := bstep (se 1 (by rfl) ⟨956240, by rfl⟩ : syracuseStep 1274987 = 1912481) B1912481
theorem B12907673 : Blo 754331 12907673 := bstep (se 2 (by rfl) ⟨4840377, by rfl⟩ : syracuseStep 12907673 = 9680755) B9680755
theorem B2553119 : Blo 754331 2553119 := bstep (se 1 (by rfl) ⟨1914839, by rfl⟩ : syracuseStep 2553119 = 3829679) B3829679
theorem B849307 : Blo 754331 849307 := bstep (se 1 (by rfl) ⟨636980, by rfl⟩ : syracuseStep 849307 = 1273961) B1273961
theorem B3634897 : Blo 754331 3634897 := bstep (se 2 (by rfl) ⟨1363086, by rfl⟩ : syracuseStep 3634897 = 2726173) B2726173
theorem B5175035 : Blo 754331 5175035 := bstep (se 1 (by rfl) ⟨3881276, by rfl⟩ : syracuseStep 5175035 = 7762553) B7762553
theorem B1079239 : Blo 754331 1079239 := bstep (se 1 (by rfl) ⟨809429, by rfl⟩ : syracuseStep 1079239 = 1618859) B1618859
theorem B1701863 : Blo 754331 1701863 := bstep (se 1 (by rfl) ⟨1276397, by rfl⟩ : syracuseStep 1701863 = 2552795) B2552795
theorem B1210351 : Blo 754331 1210351 := bstep (se 1 (by rfl) ⟨907763, by rfl⟩ : syracuseStep 1210351 = 1815527) B1815527
theorem B1701881 : Blo 754331 1701881 := bstep (se 2 (by rfl) ⟨638205, by rfl⟩ : syracuseStep 1701881 = 1276411) B1276411
theorem B1701971 : Blo 754331 1701971 := bstep (se 1 (by rfl) ⟨1276478, by rfl⟩ : syracuseStep 1701971 = 2552957) B2552957
theorem B4847759 : Blo 754331 4847759 := bstep (se 1 (by rfl) ⟨3635819, by rfl⟩ : syracuseStep 4847759 = 7271639) B7271639
theorem B1702043 : Blo 754331 1702043 := bstep (se 1 (by rfl) ⟨1276532, by rfl⟩ : syracuseStep 1702043 = 2553065) B2553065
theorem B1702151 : Blo 754331 1702151 := bstep (se 1 (by rfl) ⟨1276613, by rfl⟩ : syracuseStep 1702151 = 2553227) B2553227
theorem B1276283 : Blo 754331 1276283 := bstep (se 1 (by rfl) ⟨957212, by rfl⟩ : syracuseStep 1276283 = 1914425) B1914425
theorem B850459 : Blo 754331 850459 := bstep (se 1 (by rfl) ⟨637844, by rfl⟩ : syracuseStep 850459 = 1275689) B1275689
theorem B1702457 : Blo 754331 1702457 := bstep (se 2 (by rfl) ⟨638421, by rfl⟩ : syracuseStep 1702457 = 1276843) B1276843
theorem B1276553 : Blo 754331 1276553 := bstep (se 2 (by rfl) ⟨478707, by rfl⟩ : syracuseStep 1276553 = 957415) B957415
theorem B2555009 : Blo 754331 2555009 := bstep (se 2 (by rfl) ⟨958128, by rfl⟩ : syracuseStep 2555009 = 1916257) B1916257
theorem B2555063 : Blo 754331 2555063 := bstep (se 1 (by rfl) ⟨1916297, by rfl⟩ : syracuseStep 2555063 = 3832595) B3832595
theorem B3833081 : Blo 754331 3833081 := bstep (se 2 (by rfl) ⟨1437405, by rfl⟩ : syracuseStep 3833081 = 2874811) B2874811
theorem B1703177 : Blo 754331 1703177 := bstep (se 2 (by rfl) ⟨638691, by rfl⟩ : syracuseStep 1703177 = 1277383) B1277383
theorem B5733827 : Blo 754331 5733827 := bstep (se 1 (by rfl) ⟨4300370, by rfl⟩ : syracuseStep 5733827 = 8600741) B8600741
theorem B851431 : Blo 754331 851431 := bstep (se 1 (by rfl) ⟨638573, by rfl⟩ : syracuseStep 851431 = 1277147) B1277147
theorem B4849399 : Blo 754331 4849399 := bstep (se 1 (by rfl) ⟨3637049, by rfl⟩ : syracuseStep 4849399 = 7274099) B7274099
theorem B2555819 : Blo 754331 2555819 := bstep (se 1 (by rfl) ⟨1916864, by rfl⟩ : syracuseStep 2555819 = 3833729) B3833729
theorem B851935 : Blo 754331 851935 := bstep (se 1 (by rfl) ⟨638951, by rfl⟩ : syracuseStep 851935 = 1277903) B1277903
theorem B2556089 : Blo 754331 2556089 := bstep (se 2 (by rfl) ⟨958533, by rfl⟩ : syracuseStep 2556089 = 1917067) B1917067
theorem B1704185 : Blo 754331 1704185 := bstep (se 2 (by rfl) ⟨639069, by rfl⟩ : syracuseStep 1704185 = 1278139) B1278139
theorem B852223 : Blo 754331 852223 := bstep (se 1 (by rfl) ⟨639167, by rfl⟩ : syracuseStep 852223 = 1278335) B1278335
theorem B1278247 : Blo 754331 1278247 := bstep (se 1 (by rfl) ⟨958685, by rfl⟩ : syracuseStep 1278247 = 1917371) B1917371
theorem B1704239 : Blo 754331 1704239 := bstep (se 1 (by rfl) ⟨1278179, by rfl⟩ : syracuseStep 1704239 = 2556359) B2556359
theorem B1704455 : Blo 754331 1704455 := bstep (se 1 (by rfl) ⟨1278341, by rfl⟩ : syracuseStep 1704455 = 2556683) B2556683
theorem B852511 : Blo 754331 852511 := bstep (se 1 (by rfl) ⟨639383, by rfl⟩ : syracuseStep 852511 = 1278767) B1278767
theorem B2556521 : Blo 754331 2556521 := bstep (se 2 (by rfl) ⟨958695, by rfl⟩ : syracuseStep 2556521 = 1917391) B1917391
theorem B754343 : Blo 754331 754343 := bstep (se 1 (by rfl) ⟨565757, by rfl⟩ : syracuseStep 754343 = 1131515) B1131515
theorem B1704635 : Blo 754331 1704635 := bstep (se 1 (by rfl) ⟨1278476, by rfl⟩ : syracuseStep 1704635 = 2556953) B2556953
theorem B754383 : Blo 754331 754383 := bstep (se 1 (by rfl) ⟨565787, by rfl⟩ : syracuseStep 754383 = 1131575) B1131575
theorem B754463 : Blo 754331 754463 := bstep (se 1 (by rfl) ⟨565847, by rfl⟩ : syracuseStep 754463 = 1131695) B1131695
theorem B2327549 : Blo 754331 2327549 := bstep (se 3 (by rfl) ⟨436415, by rfl⟩ : syracuseStep 2327549 = 872831) B872831
theorem B754735 : Blo 754331 754735 := bstep (se 1 (by rfl) ⟨566051, by rfl⟩ : syracuseStep 754735 = 1132103) B1132103
theorem B1705067 : Blo 754331 1705067 := bstep (se 1 (by rfl) ⟨1278800, by rfl⟩ : syracuseStep 1705067 = 2557601) B2557601
theorem B754799 : Blo 754331 754799 := bstep (se 1 (by rfl) ⟨566099, by rfl⟩ : syracuseStep 754799 = 1132199) B1132199
theorem B754855 : Blo 754331 754855 := bstep (se 1 (by rfl) ⟨566141, by rfl⟩ : syracuseStep 754855 = 1132283) B1132283
theorem B10880189 : Blo 754331 10880189 := bstep (se 3 (by rfl) ⟨2040035, by rfl⟩ : syracuseStep 10880189 = 4080071) B4080071
theorem B754879 : Blo 754331 754879 := bstep (se 1 (by rfl) ⟨566159, by rfl⟩ : syracuseStep 754879 = 1132319) B1132319
theorem B19596491 : Blo 754331 19596491 := bstep (se 1 (by rfl) ⟨14697368, by rfl⟩ : syracuseStep 19596491 = 29394737) B29394737
theorem B754911 : Blo 754331 754911 := bstep (se 1 (by rfl) ⟨566183, by rfl⟩ : syracuseStep 754911 = 1132367) B1132367
theorem B1279199 : Blo 754331 1279199 := bstep (se 1 (by rfl) ⟨959399, by rfl⟩ : syracuseStep 1279199 = 1918799) B1918799
theorem B754991 : Blo 754331 754991 := bstep (se 1 (by rfl) ⟨566243, by rfl⟩ : syracuseStep 754991 = 1132487) B1132487
theorem B5735771 : Blo 754331 5735771 := bstep (se 1 (by rfl) ⟨4301828, by rfl⟩ : syracuseStep 5735771 = 8603657) B8603657
theorem B5604727 : Blo 754331 5604727 := bstep (se 1 (by rfl) ⟨4203545, by rfl⟩ : syracuseStep 5604727 = 8407091) B8407091
theorem B1148329 : Blo 754331 1148329 := bstep (se 2 (by rfl) ⟨430623, by rfl⟩ : syracuseStep 1148329 = 861247) B861247
theorem B755227 : Blo 754331 755227 := bstep (se 1 (by rfl) ⟨566420, by rfl⟩ : syracuseStep 755227 = 1132841) B1132841
theorem B755231 : Blo 754331 755231 := bstep (se 1 (by rfl) ⟨566423, by rfl⟩ : syracuseStep 755231 = 1132847) B1132847
theorem B12289573 : Blo 754331 12289573 := bstep (se 4 (by rfl) ⟨1152147, by rfl⟩ : syracuseStep 12289573 = 2304295) B2304295
theorem B1705535 : Blo 754331 1705535 := bstep (se 1 (by rfl) ⟨1279151, by rfl⟩ : syracuseStep 1705535 = 2558303) B2558303
theorem B2328169 : Blo 754331 2328169 := bstep (se 2 (by rfl) ⟨873063, by rfl⟩ : syracuseStep 2328169 = 1746127) B1746127
theorem B1705643 : Blo 754331 1705643 := bstep (se 1 (by rfl) ⟨1279232, by rfl⟩ : syracuseStep 1705643 = 2558465) B2558465
theorem B755391 : Blo 754331 755391 := bstep (se 1 (by rfl) ⟨566543, by rfl⟩ : syracuseStep 755391 = 1133087) B1133087
theorem B31000265 : Blo 754331 31000265 := bstep (se 2 (by rfl) ⟨11625099, by rfl⟩ : syracuseStep 31000265 = 23250199) B23250199
theorem B3540743 : Blo 754331 3540743 := bstep (se 1 (by rfl) ⟨2655557, by rfl⟩ : syracuseStep 3540743 = 5311115) B5311115
theorem B755647 : Blo 754331 755647 := bstep (se 1 (by rfl) ⟨566735, by rfl⟩ : syracuseStep 755647 = 1133471) B1133471
theorem B755679 : Blo 754331 755679 := bstep (se 1 (by rfl) ⟨566759, by rfl⟩ : syracuseStep 755679 = 1133519) B1133519
theorem B1705967 : Blo 754331 1705967 := bstep (se 1 (by rfl) ⟨1279475, by rfl⟩ : syracuseStep 1705967 = 2558951) B2558951
theorem B755739 : Blo 754331 755739 := bstep (se 1 (by rfl) ⟨566804, by rfl⟩ : syracuseStep 755739 = 1133609) B1133609
theorem B755743 : Blo 754331 755743 := bstep (se 1 (by rfl) ⟨566807, by rfl⟩ : syracuseStep 755743 = 1133615) B1133615
theorem B755759 : Blo 754331 755759 := bstep (se 1 (by rfl) ⟨566819, by rfl⟩ : syracuseStep 755759 = 1133639) B1133639
theorem B6883379 : Blo 754331 6883379 := bstep (se 1 (by rfl) ⟨5162534, by rfl⟩ : syracuseStep 6883379 = 10325069) B10325069
theorem B1214651 : Blo 754331 1214651 := bstep (se 1 (by rfl) ⟨910988, by rfl⟩ : syracuseStep 1214651 = 1821977) B1821977
theorem B1706183 : Blo 754331 1706183 := bstep (se 1 (by rfl) ⟨1279637, by rfl⟩ : syracuseStep 1706183 = 2559275) B2559275
theorem B755935 : Blo 754331 755935 := bstep (se 1 (by rfl) ⟨566951, by rfl⟩ : syracuseStep 755935 = 1133903) B1133903
theorem B755995 : Blo 754331 755995 := bstep (se 1 (by rfl) ⟨566996, by rfl⟩ : syracuseStep 755995 = 1133993) B1133993
theorem B2558249 : Blo 754331 2558249 := bstep (se 2 (by rfl) ⟨959343, by rfl⟩ : syracuseStep 2558249 = 1918687) B1918687
theorem B3639647 : Blo 754331 3639647 := bstep (se 1 (by rfl) ⟨2729735, by rfl⟩ : syracuseStep 3639647 = 5459471) B5459471
theorem B756095 : Blo 754331 756095 := bstep (se 1 (by rfl) ⟨567071, by rfl⟩ : syracuseStep 756095 = 1134143) B1134143
theorem B2427263 : Blo 754331 2427263 := bstep (se 1 (by rfl) ⟨1820447, by rfl⟩ : syracuseStep 2427263 = 3640895) B3640895
theorem B756271 : Blo 754331 756271 := bstep (se 1 (by rfl) ⟨567203, by rfl⟩ : syracuseStep 756271 = 1134407) B1134407
theorem B756327 : Blo 754331 756327 := bstep (se 1 (by rfl) ⟨567245, by rfl⟩ : syracuseStep 756327 = 1134491) B1134491
theorem B13765571 : Blo 754331 13765571 := bstep (se 1 (by rfl) ⟨10324178, by rfl⟩ : syracuseStep 13765571 = 20648357) B20648357
theorem B756703 : Blo 754331 756703 := bstep (se 1 (by rfl) ⟨567527, by rfl⟩ : syracuseStep 756703 = 1135055) B1135055
theorem B756731 : Blo 754331 756731 := bstep (se 1 (by rfl) ⟨567548, by rfl⟩ : syracuseStep 756731 = 1135097) B1135097
theorem B756799 : Blo 754331 756799 := bstep (se 1 (by rfl) ⟨567599, by rfl⟩ : syracuseStep 756799 = 1135199) B1135199
theorem B5737715 : Blo 754331 5737715 := bstep (se 1 (by rfl) ⟨4303286, by rfl⟩ : syracuseStep 5737715 = 8606573) B8606573
theorem B2624879 : Blo 754331 2624879 := bstep (se 1 (by rfl) ⟨1968659, by rfl⟩ : syracuseStep 2624879 = 3937319) B3937319
theorem B757119 : Blo 754331 757119 := bstep (se 1 (by rfl) ⟨567839, by rfl⟩ : syracuseStep 757119 = 1135679) B1135679
theorem B757147 : Blo 754331 757147 := bstep (se 1 (by rfl) ⟨567860, by rfl⟩ : syracuseStep 757147 = 1135721) B1135721
theorem B757215 : Blo 754331 757215 := bstep (se 1 (by rfl) ⟨567911, by rfl⟩ : syracuseStep 757215 = 1135823) B1135823
theorem B1150567 : Blo 754331 1150567 := bstep (se 1 (by rfl) ⟨862925, by rfl⟩ : syracuseStep 1150567 = 1725851) B1725851
theorem B757351 : Blo 754331 757351 := bstep (se 1 (by rfl) ⟨568013, by rfl⟩ : syracuseStep 757351 = 1136027) B1136027
theorem B1314407 : Blo 754331 1314407 := bstep (se 1 (by rfl) ⟨985805, by rfl⟩ : syracuseStep 1314407 = 1971611) B1971611
theorem B757499 : Blo 754331 757499 := bstep (se 1 (by rfl) ⟨568124, by rfl⟩ : syracuseStep 757499 = 1136249) B1136249
theorem B757567 : Blo 754331 757567 := bstep (se 1 (by rfl) ⟨568175, by rfl⟩ : syracuseStep 757567 = 1136351) B1136351
theorem B757631 : Blo 754331 757631 := bstep (se 1 (by rfl) ⟨568223, by rfl⟩ : syracuseStep 757631 = 1136447) B1136447
theorem B5541871 : Blo 754331 5541871 := bstep (se 1 (by rfl) ⟨4156403, by rfl⟩ : syracuseStep 5541871 = 8312807) B8312807
theorem B757743 : Blo 754331 757743 := bstep (se 1 (by rfl) ⟨568307, by rfl⟩ : syracuseStep 757743 = 1136615) B1136615
theorem B757755 : Blo 754331 757755 := bstep (se 1 (by rfl) ⟨568316, by rfl⟩ : syracuseStep 757755 = 1136633) B1136633
theorem B14749739 : Blo 754331 14749739 := bstep (se 1 (by rfl) ⟨11062304, by rfl⟩ : syracuseStep 14749739 = 22124609) B22124609
theorem B757823 : Blo 754331 757823 := bstep (se 1 (by rfl) ⟨568367, by rfl⟩ : syracuseStep 757823 = 1136735) B1136735
theorem B2461759 : Blo 754331 2461759 := bstep (se 1 (by rfl) ⟨1846319, by rfl⟩ : syracuseStep 2461759 = 3692639) B3692639
theorem B757863 : Blo 754331 757863 := bstep (se 1 (by rfl) ⟨568397, by rfl⟩ : syracuseStep 757863 = 1136795) B1136795
theorem B757887 : Blo 754331 757887 := bstep (se 1 (by rfl) ⟨568415, by rfl⟩ : syracuseStep 757887 = 1136831) B1136831
theorem B757915 : Blo 754331 757915 := bstep (se 1 (by rfl) ⟨568436, by rfl⟩ : syracuseStep 757915 = 1136873) B1136873
theorem B758119 : Blo 754331 758119 := bstep (se 1 (by rfl) ⟨568589, by rfl⟩ : syracuseStep 758119 = 1137179) B1137179
theorem B758171 : Blo 754331 758171 := bstep (se 1 (by rfl) ⟨568628, by rfl⟩ : syracuseStep 758171 = 1137257) B1137257
theorem B19698227 : Blo 754331 19698227 := bstep (se 1 (by rfl) ⟨14773670, by rfl⟩ : syracuseStep 19698227 = 29547341) B29547341
theorem B9214067 : Blo 754331 9214067 := bstep (se 1 (by rfl) ⟨6910550, by rfl⟩ : syracuseStep 9214067 = 13821101) B13821101
theorem B1612315 : Blo 754331 1612315 := bstep (se 1 (by rfl) ⟨1209236, by rfl⟩ : syracuseStep 1612315 = 2418473) B2418473
theorem B2300599 : Blo 754331 2300599 := bstep (se 1 (by rfl) ⟨1725449, by rfl⟩ : syracuseStep 2300599 = 3450899) B3450899
theorem B1022791 : Blo 754331 1022791 := bstep (se 1 (by rfl) ⟨767093, by rfl⟩ : syracuseStep 1022791 = 1534187) B1534187
theorem B2726779 : Blo 754331 2726779 := bstep (se 1 (by rfl) ⟨2045084, by rfl⟩ : syracuseStep 2726779 = 4090169) B4090169
theorem B5742089 : Blo 754331 5742089 := bstep (se 2 (by rfl) ⟨2153283, by rfl⟩ : syracuseStep 5742089 = 4306567) B4306567
theorem B2301659 : Blo 754331 2301659 := bstep (se 1 (by rfl) ⟨1726244, by rfl⟩ : syracuseStep 2301659 = 3452489) B3452489
theorem B1613801 : Blo 754331 1613801 := bstep (se 2 (by rfl) ⟨605175, by rfl⟩ : syracuseStep 1613801 = 1210351) B1210351
theorem B1843415 : Blo 754331 1843415 := bstep (se 1 (by rfl) ⟨1382561, by rfl⟩ : syracuseStep 1843415 = 2765123) B2765123
theorem B6136483 : Blo 754331 6136483 := bstep (se 1 (by rfl) ⟨4602362, by rfl⟩ : syracuseStep 6136483 = 9204725) B9204725
theorem B20652833 : Blo 754331 20652833 := bstep (se 2 (by rfl) ⟨7744812, by rfl⟩ : syracuseStep 20652833 = 15489625) B15489625
theorem B4596527 : Blo 754331 4596527 := bstep (se 1 (by rfl) ⟨3447395, by rfl⟩ : syracuseStep 4596527 = 6894791) B6894791
theorem B9708335 : Blo 754331 9708335 := bstep (se 1 (by rfl) ⟨7281251, by rfl⟩ : syracuseStep 9708335 = 14562503) B14562503
theorem B3450023 : Blo 754331 3450023 := bstep (se 1 (by rfl) ⟨2587517, by rfl⟩ : syracuseStep 3450023 = 5175035) B5175035
theorem B6465865 : Blo 754331 6465865 := bstep (se 2 (by rfl) ⟨2424699, by rfl⟩ : syracuseStep 6465865 = 4849399) B4849399
theorem B1911559 : Blo 754331 1911559 := bstep (se 1 (by rfl) ⟨1433669, by rfl⟩ : syracuseStep 1911559 = 2867339) B2867339
theorem B8596367 : Blo 754331 8596367 := bstep (se 1 (by rfl) ⟨6447275, by rfl⟩ : syracuseStep 8596367 = 12894551) B12894551
theorem B1813673 : Blo 754331 1813673 := bstep (se 2 (by rfl) ⟨680127, by rfl⟩ : syracuseStep 1813673 = 1360255) B1360255
theorem B7253495 : Blo 754331 7253495 := bstep (se 1 (by rfl) ⟨5440121, by rfl⟩ : syracuseStep 7253495 = 10880243) B10880243
theorem B4599935 : Blo 754331 4599935 := bstep (se 1 (by rfl) ⟨3449951, by rfl⟩ : syracuseStep 4599935 = 6899903) B6899903
theorem B12955787 : Blo 754331 12955787 := bstep (se 1 (by rfl) ⟨9716840, by rfl⟩ : syracuseStep 12955787 = 19433681) B19433681
theorem B16396829 : Blo 754331 16396829 := bstep (se 3 (by rfl) ⟨3074405, by rfl⟩ : syracuseStep 16396829 = 6148811) B6148811
theorem B14529131 : Blo 754331 14529131 := bstep (se 1 (by rfl) ⟨10896848, by rfl⟩ : syracuseStep 14529131 = 21793697) B21793697
theorem B1618825 : Blo 754331 1618825 := bstep (se 2 (by rfl) ⟨607059, by rfl⟩ : syracuseStep 1618825 = 1214119) B1214119
theorem B1913807 : Blo 754331 1913807 := bstep (se 1 (by rfl) ⟨1435355, by rfl⟩ : syracuseStep 1913807 = 2870711) B2870711
theorem B6993001 : Blo 754331 6993001 := bstep (se 2 (by rfl) ⟨2622375, by rfl⟩ : syracuseStep 6993001 = 5244751) B5244751
theorem B2864393 : Blo 754331 2864393 := bstep (se 2 (by rfl) ⟨1074147, by rfl⟩ : syracuseStep 2864393 = 2148295) B2148295
theorem B13120861 : Blo 754331 13120861 := bstep (se 3 (by rfl) ⟨2460161, by rfl⟩ : syracuseStep 13120861 = 4920323) B4920323
theorem B32683621 : Blo 754331 32683621 := bstep (se 4 (by rfl) ⟨3064089, by rfl⟩ : syracuseStep 32683621 = 6128179) B6128179
theorem B6141673 : Blo 754331 6141673 := bstep (se 2 (by rfl) ⟨2303127, by rfl⟩ : syracuseStep 6141673 = 4606255) B4606255
theorem B2864879 : Blo 754331 2864879 := bstep (se 1 (by rfl) ⟨2148659, by rfl⟩ : syracuseStep 2864879 = 4297319) B4297319
theorem B2865395 : Blo 754331 2865395 := bstep (se 1 (by rfl) ⟨2149046, by rfl⟩ : syracuseStep 2865395 = 4298093) B4298093
theorem B3062393 : Blo 754331 3062393 := bstep (se 2 (by rfl) ⟨1148397, by rfl⟩ : syracuseStep 3062393 = 2296795) B2296795
theorem B2865851 : Blo 754331 2865851 := bstep (se 1 (by rfl) ⟨2149388, by rfl⟩ : syracuseStep 2865851 = 4298777) B4298777
theorem B3226715 : Blo 754331 3226715 := bstep (se 1 (by rfl) ⟨2420036, by rfl⟩ : syracuseStep 3226715 = 4840073) B4840073
theorem B5749865 : Blo 754331 5749865 := bstep (se 2 (by rfl) ⟨2156199, by rfl⟩ : syracuseStep 5749865 = 4312399) B4312399
theorem B1819007 : Blo 754331 1819007 := bstep (se 1 (by rfl) ⟨1364255, by rfl⟩ : syracuseStep 1819007 = 2728511) B2728511
theorem B1655399 : Blo 754331 1655399 := bstep (se 1 (by rfl) ⟨1241549, by rfl⟩ : syracuseStep 1655399 = 2483099) B2483099
theorem B2867993 : Blo 754331 2867993 := bstep (se 2 (by rfl) ⟨1075497, by rfl⟩ : syracuseStep 2867993 = 2150995) B2150995
theorem B3228457 : Blo 754331 3228457 := bstep (se 2 (by rfl) ⟨1210671, by rfl⟩ : syracuseStep 3228457 = 2421343) B2421343
theorem B1131743 : Blo 754331 1131743 := bstep (se 1 (by rfl) ⟨848807, by rfl⟩ : syracuseStep 1131743 = 1697615) B1697615
theorem B1131755 : Blo 754331 1131755 := bstep (se 1 (by rfl) ⟨848816, by rfl⟩ : syracuseStep 1131755 = 1697633) B1697633
theorem B4310441 : Blo 754331 4310441 := bstep (se 2 (by rfl) ⟨1616415, by rfl⟩ : syracuseStep 4310441 = 3232831) B3232831
theorem B1132139 : Blo 754331 1132139 := bstep (se 1 (by rfl) ⟨849104, by rfl⟩ : syracuseStep 1132139 = 1698209) B1698209
theorem B1132223 : Blo 754331 1132223 := bstep (se 1 (by rfl) ⟨849167, by rfl⟩ : syracuseStep 1132223 = 1698335) B1698335
theorem B3229379 : Blo 754331 3229379 := bstep (se 1 (by rfl) ⟨2422034, by rfl⟩ : syracuseStep 3229379 = 4844069) B4844069
theorem B1132409 : Blo 754331 1132409 := bstep (se 2 (by rfl) ⟨424653, by rfl⟩ : syracuseStep 1132409 = 849307) B849307
theorem B1493147 : Blo 754331 1493147 := bstep (se 1 (by rfl) ⟨1119860, by rfl⟩ : syracuseStep 1493147 = 2239721) B2239721
theorem B3820121 : Blo 754331 3820121 := bstep (se 2 (by rfl) ⟨1432545, by rfl⟩ : syracuseStep 3820121 = 2865091) B2865091
theorem B1133159 : Blo 754331 1133159 := bstep (se 1 (by rfl) ⟨849869, by rfl⟩ : syracuseStep 1133159 = 1699739) B1699739
theorem B2149001 : Blo 754331 2149001 := bstep (se 2 (by rfl) ⟨805875, by rfl⟩ : syracuseStep 2149001 = 1611751) B1611751
theorem B1133351 : Blo 754331 1133351 := bstep (se 1 (by rfl) ⟨850013, by rfl⟩ : syracuseStep 1133351 = 1700027) B1700027
theorem B4311899 : Blo 754331 4311899 := bstep (se 1 (by rfl) ⟨3233924, by rfl⟩ : syracuseStep 4311899 = 6467849) B6467849
theorem B14568497 : Blo 754331 14568497 := bstep (se 2 (by rfl) ⟨5463186, by rfl⟩ : syracuseStep 14568497 = 10926373) B10926373
theorem B1133675 : Blo 754331 1133675 := bstep (se 1 (by rfl) ⟨850256, by rfl⟩ : syracuseStep 1133675 = 1700513) B1700513
theorem B3230867 : Blo 754331 3230867 := bstep (se 1 (by rfl) ⟨2423150, by rfl⟩ : syracuseStep 3230867 = 4846301) B4846301
theorem B1133915 : Blo 754331 1133915 := bstep (se 1 (by rfl) ⟨850436, by rfl⟩ : syracuseStep 1133915 = 1700873) B1700873
theorem B1133945 : Blo 754331 1133945 := bstep (se 2 (by rfl) ⟨425229, by rfl⟩ : syracuseStep 1133945 = 850459) B850459
theorem B1133951 : Blo 754331 1133951 := bstep (se 1 (by rfl) ⟨850463, by rfl⟩ : syracuseStep 1133951 = 1700927) B1700927
theorem B8605115 : Blo 754331 8605115 := bstep (se 1 (by rfl) ⟨6453836, by rfl⟩ : syracuseStep 8605115 = 12907673) B12907673
theorem B2870909 : Blo 754331 2870909 := bstep (se 3 (by rfl) ⟨538295, by rfl⟩ : syracuseStep 2870909 = 1076591) B1076591
theorem B8179517 : Blo 754331 8179517 := bstep (se 3 (by rfl) ⟨1533659, by rfl⟩ : syracuseStep 8179517 = 3067319) B3067319
theorem B5459845 : Blo 754331 5459845 := bstep (se 4 (by rfl) ⟨511860, by rfl⟩ : syracuseStep 5459845 = 1023721) B1023721
theorem B1134575 : Blo 754331 1134575 := bstep (se 1 (by rfl) ⟨850931, by rfl⟩ : syracuseStep 1134575 = 1701863) B1701863
theorem B1134587 : Blo 754331 1134587 := bstep (se 1 (by rfl) ⟨850940, by rfl⟩ : syracuseStep 1134587 = 1701881) B1701881
theorem B1134647 : Blo 754331 1134647 := bstep (se 1 (by rfl) ⟨850985, by rfl⟩ : syracuseStep 1134647 = 1701971) B1701971
theorem B3231839 : Blo 754331 3231839 := bstep (se 1 (by rfl) ⟨2423879, by rfl⟩ : syracuseStep 3231839 = 4847759) B4847759
theorem B1134695 : Blo 754331 1134695 := bstep (se 1 (by rfl) ⟨851021, by rfl⟩ : syracuseStep 1134695 = 1702043) B1702043
theorem B1134767 : Blo 754331 1134767 := bstep (se 1 (by rfl) ⟨851075, by rfl⟩ : syracuseStep 1134767 = 1702151) B1702151
theorem B1134971 : Blo 754331 1134971 := bstep (se 1 (by rfl) ⟨851228, by rfl⟩ : syracuseStep 1134971 = 1702457) B1702457
theorem B1135241 : Blo 754331 1135241 := bstep (se 2 (by rfl) ⟨425715, by rfl⟩ : syracuseStep 1135241 = 851431) B851431
theorem B1135451 : Blo 754331 1135451 := bstep (se 1 (by rfl) ⟨851588, by rfl⟩ : syracuseStep 1135451 = 1703177) B1703177
theorem B2872169 : Blo 754331 2872169 := bstep (se 2 (by rfl) ⟨1077063, by rfl⟩ : syracuseStep 2872169 = 2154127) B2154127
theorem B12243905 : Blo 754331 12243905 := bstep (se 2 (by rfl) ⟨4591464, by rfl⟩ : syracuseStep 12243905 = 9182929) B9182929
theorem B3822551 : Blo 754331 3822551 := bstep (se 1 (by rfl) ⟨2866913, by rfl⟩ : syracuseStep 3822551 = 5733827) B5733827
theorem B9819281 : Blo 754331 9819281 := bstep (se 2 (by rfl) ⟨3682230, by rfl⟩ : syracuseStep 9819281 = 7364461) B7364461
theorem B1135913 : Blo 754331 1135913 := bstep (se 2 (by rfl) ⟨425967, by rfl⟩ : syracuseStep 1135913 = 851935) B851935
theorem B1136111 : Blo 754331 1136111 := bstep (se 1 (by rfl) ⟨852083, by rfl⟩ : syracuseStep 1136111 = 1704167) B1704167
theorem B7263917 : Blo 754331 7263917 := bstep (se 3 (by rfl) ⟨1361984, by rfl⟩ : syracuseStep 7263917 = 2723969) B2723969
theorem B1136507 : Blo 754331 1136507 := bstep (se 1 (by rfl) ⟨852380, by rfl⟩ : syracuseStep 1136507 = 1704761) B1704761
theorem B1136543 : Blo 754331 1136543 := bstep (se 1 (by rfl) ⟨852407, by rfl⟩ : syracuseStep 1136543 = 1704815) B1704815
theorem B2152487 : Blo 754331 2152487 := bstep (se 1 (by rfl) ⟨1614365, by rfl⟩ : syracuseStep 2152487 = 3228731) B3228731
theorem B1136777 : Blo 754331 1136777 := bstep (se 2 (by rfl) ⟨426291, by rfl⟩ : syracuseStep 1136777 = 852583) B852583
theorem B2545883 : Blo 754331 2545883 := bstep (se 1 (by rfl) ⟨1909412, by rfl⟩ : syracuseStep 2545883 = 3818825) B3818825
theorem B1136927 : Blo 754331 1136927 := bstep (se 1 (by rfl) ⟨852695, by rfl⟩ : syracuseStep 1136927 = 1705391) B1705391
theorem B2873657 : Blo 754331 2873657 := bstep (se 2 (by rfl) ⟨1077621, by rfl⟩ : syracuseStep 2873657 = 2155243) B2155243
theorem B4839763 : Blo 754331 4839763 := bstep (se 1 (by rfl) ⟨3629822, by rfl⟩ : syracuseStep 4839763 = 7259645) B7259645
theorem B2546153 : Blo 754331 2546153 := bstep (se 2 (by rfl) ⟨954807, by rfl⟩ : syracuseStep 2546153 = 1909615) B1909615
theorem B1137479 : Blo 754331 1137479 := bstep (se 1 (by rfl) ⟨853109, by rfl⟩ : syracuseStep 1137479 = 1706219) B1706219
theorem B3234779 : Blo 754331 3234779 := bstep (se 1 (by rfl) ⟨2426084, by rfl⟩ : syracuseStep 3234779 = 4852169) B4852169
theorem B1432903 : Blo 754331 1432903 := bstep (se 1 (by rfl) ⟨1074677, by rfl⟩ : syracuseStep 1432903 = 2149355) B2149355
theorem B8609489 : Blo 754331 8609489 := bstep (se 2 (by rfl) ⟨3228558, by rfl⟩ : syracuseStep 8609489 = 6457117) B6457117
theorem B2547611 : Blo 754331 2547611 := bstep (se 1 (by rfl) ⟨1910708, by rfl⟩ : syracuseStep 2547611 = 3821417) B3821417
theorem B1728479 : Blo 754331 1728479 := bstep (se 1 (by rfl) ⟨1296359, by rfl⟩ : syracuseStep 1728479 = 2592719) B2592719
theorem B5465033 : Blo 754331 5465033 := bstep (se 2 (by rfl) ⟨2049387, by rfl⟩ : syracuseStep 5465033 = 4098775) B4098775
theorem B6546953 : Blo 754331 6546953 := bstep (se 2 (by rfl) ⟨2455107, by rfl⟩ : syracuseStep 6546953 = 4910215) B4910215
theorem B1435583 : Blo 754331 1435583 := bstep (se 1 (by rfl) ⟨1076687, by rfl⟩ : syracuseStep 1435583 = 2153375) B2153375
theorem B1697759 : Blo 754331 1697759 := bstep (se 1 (by rfl) ⟨1273319, by rfl⟩ : syracuseStep 1697759 = 2546639) B2546639
theorem B6121823 : Blo 754331 6121823 := bstep (se 1 (by rfl) ⟨4591367, by rfl⟩ : syracuseStep 6121823 = 9182735) B9182735
theorem B1534511 : Blo 754331 1534511 := bstep (se 1 (by rfl) ⟨1150883, by rfl⟩ : syracuseStep 1534511 = 2301767) B2301767
theorem B5728967 : Blo 754331 5728967 := bstep (se 1 (by rfl) ⟨4296725, by rfl⟩ : syracuseStep 5728967 = 8593451) B8593451
theorem B1698767 : Blo 754331 1698767 := bstep (se 1 (by rfl) ⟨1274075, by rfl⟩ : syracuseStep 1698767 = 2548151) B2548151
theorem B1698857 : Blo 754331 1698857 := bstep (se 2 (by rfl) ⟨637071, by rfl⟩ : syracuseStep 1698857 = 1274143) B1274143
theorem B1535159 : Blo 754331 1535159 := bstep (se 1 (by rfl) ⟨1151369, by rfl⟩ : syracuseStep 1535159 = 2302739) B2302739
theorem B1699091 : Blo 754331 1699091 := bstep (se 1 (by rfl) ⟨1274318, by rfl⟩ : syracuseStep 1699091 = 2548637) B2548637
theorem B1699127 : Blo 754331 1699127 := bstep (se 1 (by rfl) ⟨1274345, by rfl⟩ : syracuseStep 1699127 = 2548691) B2548691
theorem B1437095 : Blo 754331 1437095 := bstep (se 1 (by rfl) ⟨1077821, by rfl⟩ : syracuseStep 1437095 = 2155643) B2155643
theorem B1699721 : Blo 754331 1699721 := bstep (se 2 (by rfl) ⟨637395, by rfl⟩ : syracuseStep 1699721 = 1274791) B1274791
theorem B2420729 : Blo 754331 2420729 := bstep (se 2 (by rfl) ⟨907773, by rfl⟩ : syracuseStep 2420729 = 1815547) B1815547
theorem B25260055 : Blo 754331 25260055 := bstep (se 1 (by rfl) ⟨18945041, by rfl⟩ : syracuseStep 25260055 = 37890083) B37890083
theorem B1699937 : Blo 754331 1699937 := bstep (se 2 (by rfl) ⟨637476, by rfl⟩ : syracuseStep 1699937 = 1274953) B1274953
theorem B12415169 : Blo 754331 12415169 := bstep (se 2 (by rfl) ⟨4655688, by rfl⟩ : syracuseStep 12415169 = 9311377) B9311377
theorem B1274089 : Blo 754331 1274089 := bstep (se 2 (by rfl) ⟨477783, by rfl⟩ : syracuseStep 1274089 = 955567) B955567
theorem B2420999 : Blo 754331 2420999 := bstep (se 1 (by rfl) ⟨1815749, by rfl⟩ : syracuseStep 2420999 = 3631499) B3631499
theorem B1536263 : Blo 754331 1536263 := bstep (se 1 (by rfl) ⟨1152197, by rfl⟩ : syracuseStep 1536263 = 2304395) B2304395
theorem B4092287 : Blo 754331 4092287 := bstep (se 1 (by rfl) ⟨3069215, by rfl⟩ : syracuseStep 4092287 = 6138431) B6138431
theorem B1700603 : Blo 754331 1700603 := bstep (se 1 (by rfl) ⟨1275452, by rfl⟩ : syracuseStep 1700603 = 2550905) B2550905
theorem B848731 : Blo 754331 848731 := bstep (se 1 (by rfl) ⟨636548, by rfl⟩ : syracuseStep 848731 = 1273097) B1273097
theorem B4846529 : Blo 754331 4846529 := bstep (se 2 (by rfl) ⟨1817448, by rfl⟩ : syracuseStep 4846529 = 3634897) B3634897
theorem B1700819 : Blo 754331 1700819 := bstep (se 1 (by rfl) ⟨1275614, by rfl⟩ : syracuseStep 1700819 = 2551229) B2551229
theorem B1438985 : Blo 754331 1438985 := bstep (se 2 (by rfl) ⟨539619, by rfl⟩ : syracuseStep 1438985 = 1079239) B1079239
theorem B1439039 : Blo 754331 1439039 := bstep (se 1 (by rfl) ⟨1079279, by rfl⟩ : syracuseStep 1439039 = 2158559) B2158559
theorem B1701287 : Blo 754331 1701287 := bstep (se 1 (by rfl) ⟨1275965, by rfl⟩ : syracuseStep 1701287 = 2551931) B2551931
theorem B1701395 : Blo 754331 1701395 := bstep (se 1 (by rfl) ⟨1276046, by rfl⟩ : syracuseStep 1701395 = 2552093) B2552093
theorem B15496775 : Blo 754331 15496775 := bstep (se 1 (by rfl) ⟨11622581, by rfl⟩ : syracuseStep 15496775 = 23245163) B23245163
theorem B1701467 : Blo 754331 1701467 := bstep (se 1 (by rfl) ⟨1276100, by rfl⟩ : syracuseStep 1701467 = 2552201) B2552201
theorem B2553497 : Blo 754331 2553497 := bstep (se 2 (by rfl) ⟨957561, by rfl⟩ : syracuseStep 2553497 = 1915123) B1915123
theorem B1079023 : Blo 754331 1079023 := bstep (se 1 (by rfl) ⟨809267, by rfl⟩ : syracuseStep 1079023 = 1618535) B1618535
theorem B1439471 : Blo 754331 1439471 := bstep (se 1 (by rfl) ⟨1079603, by rfl⟩ : syracuseStep 1439471 = 2159207) B2159207
theorem B849991 : Blo 754331 849991 := bstep (se 1 (by rfl) ⟨637493, by rfl⟩ : syracuseStep 849991 = 1274987) B1274987
theorem B1276087 : Blo 754331 1276087 := bstep (se 1 (by rfl) ⟨957065, by rfl⟩ : syracuseStep 1276087 = 1914131) B1914131
theorem B1702079 : Blo 754331 1702079 := bstep (se 1 (by rfl) ⟨1276559, by rfl⟩ : syracuseStep 1702079 = 2553119) B2553119
theorem B3832271 : Blo 754331 3832271 := bstep (se 1 (by rfl) ⟨2874203, by rfl⟩ : syracuseStep 3832271 = 5748407) B5748407
theorem B1276681 : Blo 754331 1276681 := bstep (se 2 (by rfl) ⟨478755, by rfl⟩ : syracuseStep 1276681 = 957511) B957511
theorem B3636127 : Blo 754331 3636127 := bstep (se 1 (by rfl) ⟨2727095, by rfl⟩ : syracuseStep 3636127 = 5454191) B5454191
theorem B850855 : Blo 754331 850855 := bstep (se 1 (by rfl) ⟨638141, by rfl⟩ : syracuseStep 850855 = 1276283) B1276283
theorem B851035 : Blo 754331 851035 := bstep (se 1 (by rfl) ⟨638276, by rfl⟩ : syracuseStep 851035 = 1276553) B1276553
theorem B1703339 : Blo 754331 1703339 := bstep (se 1 (by rfl) ⟨1277504, by rfl⟩ : syracuseStep 1703339 = 2555009) B2555009
theorem B6454727 : Blo 754331 6454727 := bstep (se 1 (by rfl) ⟨4841045, by rfl⟩ : syracuseStep 6454727 = 9682091) B9682091
theorem B1703375 : Blo 754331 1703375 := bstep (se 1 (by rfl) ⟨1277531, by rfl⟩ : syracuseStep 1703375 = 2555063) B2555063
theorem B2555387 : Blo 754331 2555387 := bstep (se 1 (by rfl) ⟨1916540, by rfl⟩ : syracuseStep 2555387 = 3833081) B3833081
theorem B2555549 : Blo 754331 2555549 := bstep (se 3 (by rfl) ⟨479165, by rfl⟩ : syracuseStep 2555549 = 958331) B958331
theorem B2555657 : Blo 754331 2555657 := bstep (se 2 (by rfl) ⟨958371, by rfl⟩ : syracuseStep 2555657 = 1916743) B1916743
theorem B1703879 : Blo 754331 1703879 := bstep (se 1 (by rfl) ⟨1277909, by rfl⟩ : syracuseStep 1703879 = 2555819) B2555819
theorem B1704059 : Blo 754331 1704059 := bstep (se 1 (by rfl) ⟨1278044, by rfl⟩ : syracuseStep 1704059 = 2556089) B2556089
theorem B8618237 : Blo 754331 8618237 := bstep (se 3 (by rfl) ⟨1615919, by rfl⟩ : syracuseStep 8618237 = 3231839) B3231839
theorem B1212671 : Blo 754331 1212671 := bstep (se 1 (by rfl) ⟨909503, by rfl⟩ : syracuseStep 1212671 = 1819007) B1819007
theorem B1704329 : Blo 754331 1704329 := bstep (se 2 (by rfl) ⟨639123, by rfl⟩ : syracuseStep 1704329 = 1278247) B1278247
theorem B1704347 : Blo 754331 1704347 := bstep (se 1 (by rfl) ⟨1278260, by rfl⟩ : syracuseStep 1704347 = 2556521) B2556521
theorem B754495 : Blo 754331 754495 := bstep (se 1 (by rfl) ⟨565871, by rfl⟩ : syracuseStep 754495 = 1131743) B1131743
theorem B852799 : Blo 754331 852799 := bstep (se 1 (by rfl) ⟨639599, by rfl⟩ : syracuseStep 852799 = 1279199) B1279199
theorem B754503 : Blo 754331 754503 := bstep (se 1 (by rfl) ⟨565877, by rfl⟩ : syracuseStep 754503 = 1131755) B1131755
theorem B10912765 : Blo 754331 10912765 := bstep (se 3 (by rfl) ⟨2046143, by rfl⟩ : syracuseStep 10912765 = 4092287) B4092287
theorem B754759 : Blo 754331 754759 := bstep (se 1 (by rfl) ⟨566069, by rfl⟩ : syracuseStep 754759 = 1132139) B1132139
theorem B754815 : Blo 754331 754815 := bstep (se 1 (by rfl) ⟨566111, by rfl⟩ : syracuseStep 754815 = 1132223) B1132223
theorem B2360495 : Blo 754331 2360495 := bstep (se 1 (by rfl) ⟨1770371, by rfl⟩ : syracuseStep 2360495 = 3540743) B3540743
theorem B754939 : Blo 754331 754939 := bstep (se 1 (by rfl) ⟨566204, by rfl⟩ : syracuseStep 754939 = 1132409) B1132409
theorem B4588919 : Blo 754331 4588919 := bstep (se 1 (by rfl) ⟨3441689, by rfl⟩ : syracuseStep 4588919 = 6883379) B6883379
theorem B1705499 : Blo 754331 1705499 := bstep (se 1 (by rfl) ⟨1279124, by rfl⟩ : syracuseStep 1705499 = 2558249) B2558249
theorem B2426431 : Blo 754331 2426431 := bstep (se 1 (by rfl) ⟨1819823, by rfl⟩ : syracuseStep 2426431 = 3639647) B3639647
theorem B755439 : Blo 754331 755439 := bstep (se 1 (by rfl) ⟨566579, by rfl⟩ : syracuseStep 755439 = 1133159) B1133159
theorem B7472969 : Blo 754331 7472969 := bstep (se 2 (by rfl) ⟨2802363, by rfl⟩ : syracuseStep 7472969 = 5604727) B5604727
theorem B755567 : Blo 754331 755567 := bstep (se 1 (by rfl) ⟨566675, by rfl⟩ : syracuseStep 755567 = 1133351) B1133351
theorem B9177047 : Blo 754331 9177047 := bstep (se 1 (by rfl) ⟨6882785, by rfl⟩ : syracuseStep 9177047 = 13765571) B13765571
theorem B755783 : Blo 754331 755783 := bstep (se 1 (by rfl) ⟨566837, by rfl⟩ : syracuseStep 755783 = 1133675) B1133675
theorem B12257405 : Blo 754331 12257405 := bstep (se 3 (by rfl) ⟨2298263, by rfl⟩ : syracuseStep 12257405 = 4596527) B4596527
theorem B755943 : Blo 754331 755943 := bstep (se 1 (by rfl) ⟨566957, by rfl⟩ : syracuseStep 755943 = 1133915) B1133915
theorem B755963 : Blo 754331 755963 := bstep (se 1 (by rfl) ⟨566972, by rfl⟩ : syracuseStep 755963 = 1133945) B1133945
theorem B755967 : Blo 754331 755967 := bstep (se 1 (by rfl) ⟨566975, by rfl⟩ : syracuseStep 755967 = 1133951) B1133951
theorem B5736743 : Blo 754331 5736743 := bstep (se 1 (by rfl) ⟨4302557, by rfl⟩ : syracuseStep 5736743 = 8605115) B8605115
theorem B756383 : Blo 754331 756383 := bstep (se 1 (by rfl) ⟨567287, by rfl⟩ : syracuseStep 756383 = 1134575) B1134575
theorem B756391 : Blo 754331 756391 := bstep (se 1 (by rfl) ⟨567293, by rfl⟩ : syracuseStep 756391 = 1134587) B1134587
theorem B9833159 : Blo 754331 9833159 := bstep (se 1 (by rfl) ⟨7374869, by rfl⟩ : syracuseStep 9833159 = 14749739) B14749739
theorem B756431 : Blo 754331 756431 := bstep (se 1 (by rfl) ⟨567323, by rfl⟩ : syracuseStep 756431 = 1134647) B1134647
theorem B756463 : Blo 754331 756463 := bstep (se 1 (by rfl) ⟨567347, by rfl⟩ : syracuseStep 756463 = 1134695) B1134695
theorem B756511 : Blo 754331 756511 := bstep (se 1 (by rfl) ⟨567383, by rfl⟩ : syracuseStep 756511 = 1134767) B1134767
theorem B756647 : Blo 754331 756647 := bstep (se 1 (by rfl) ⟨567485, by rfl⟩ : syracuseStep 756647 = 1134971) B1134971
theorem B756827 : Blo 754331 756827 := bstep (se 1 (by rfl) ⟨567620, by rfl⟩ : syracuseStep 756827 = 1135241) B1135241
theorem B8621153 : Blo 754331 8621153 := bstep (se 2 (by rfl) ⟨3232932, by rfl⟩ : syracuseStep 8621153 = 6465865) B6465865
theorem B756967 : Blo 754331 756967 := bstep (se 1 (by rfl) ⟨567725, by rfl⟩ : syracuseStep 756967 = 1135451) B1135451
theorem B8162603 : Blo 754331 8162603 := bstep (se 1 (by rfl) ⟨6121952, by rfl⟩ : syracuseStep 8162603 = 12243905) B12243905
theorem B3837293 : Blo 754331 3837293 := bstep (se 3 (by rfl) ⟨719492, by rfl⟩ : syracuseStep 3837293 = 1438985) B1438985
theorem B757275 : Blo 754331 757275 := bstep (se 1 (by rfl) ⟨567956, by rfl⟩ : syracuseStep 757275 = 1135913) B1135913
theorem B757407 : Blo 754331 757407 := bstep (se 1 (by rfl) ⟨568055, by rfl⟩ : syracuseStep 757407 = 1136111) B1136111
theorem B757671 : Blo 754331 757671 := bstep (se 1 (by rfl) ⟨568253, by rfl⟩ : syracuseStep 757671 = 1136507) B1136507
theorem B757695 : Blo 754331 757695 := bstep (se 1 (by rfl) ⟨568271, by rfl⟩ : syracuseStep 757695 = 1136543) B1136543
theorem B757851 : Blo 754331 757851 := bstep (se 1 (by rfl) ⟨568388, by rfl⟩ : syracuseStep 757851 = 1136777) B1136777
theorem B757951 : Blo 754331 757951 := bstep (se 1 (by rfl) ⟨568463, by rfl⟩ : syracuseStep 757951 = 1136927) B1136927
theorem B758319 : Blo 754331 758319 := bstep (se 1 (by rfl) ⟨568739, by rfl⟩ : syracuseStep 758319 = 1137479) B1137479
theorem B3838589 : Blo 754331 3838589 := bstep (se 3 (by rfl) ⟨719735, by rfl⟩ : syracuseStep 3838589 = 1439471) B1439471
theorem B5739659 : Blo 754331 5739659 := bstep (se 1 (by rfl) ⟨4304744, by rfl⟩ : syracuseStep 5739659 = 8609489) B8609489
theorem B7279793 : Blo 754331 7279793 := bstep (se 2 (by rfl) ⟨2729922, by rfl⟩ : syracuseStep 7279793 = 5459845) B5459845
theorem B1152319 : Blo 754331 1152319 := bstep (se 1 (by rfl) ⟨864239, by rfl⟩ : syracuseStep 1152319 = 1728479) B1728479
theorem B13768555 : Blo 754331 13768555 := bstep (se 1 (by rfl) ⟨10326416, by rfl⟩ : syracuseStep 13768555 = 20652833) B20652833
theorem B3643355 : Blo 754331 3643355 := bstep (se 1 (by rfl) ⟨2732516, by rfl⟩ : syracuseStep 3643355 = 5465033) B5465033
theorem B2300015 : Blo 754331 2300015 := bstep (se 1 (by rfl) ⟨1725011, by rfl⟩ : syracuseStep 2300015 = 3450023) B3450023
theorem B16324861 : Blo 754331 16324861 := bstep (se 3 (by rfl) ⟨3060911, by rfl⟩ : syracuseStep 16324861 = 6121823) B6121823
theorem B958063 : Blo 754331 958063 := bstep (se 1 (by rfl) ⟨718547, by rfl⟩ : syracuseStep 958063 = 1437095) B1437095
theorem B1613819 : Blo 754331 1613819 := bstep (se 1 (by rfl) ⟨1210364, by rfl⟩ : syracuseStep 1613819 = 2420729) B2420729
theorem B1613999 : Blo 754331 1613999 := bstep (se 1 (by rfl) ⟨1210499, by rfl⟩ : syracuseStep 1613999 = 2420999) B2420999
theorem B1024175 : Blo 754331 1024175 := bstep (se 1 (by rfl) ⟨768131, by rfl⟩ : syracuseStep 1024175 = 1536263) B1536263
theorem B65544389 : Blo 754331 65544389 := bstep (se 4 (by rfl) ⟨6144786, by rfl⟩ : syracuseStep 65544389 = 12289573) B12289573
theorem B6136357 : Blo 754331 6136357 := bstep (se 4 (by rfl) ⟨575283, by rfl⟩ : syracuseStep 6136357 = 1150567) B1150567
theorem B1909595 : Blo 754331 1909595 := bstep (se 1 (by rfl) ⟨1432196, by rfl⟩ : syracuseStep 1909595 = 2864393) B2864393
theorem B959359 : Blo 754331 959359 := bstep (se 1 (by rfl) ⟨719519, by rfl⟩ : syracuseStep 959359 = 1439039) B1439039
theorem B10331183 : Blo 754331 10331183 := bstep (se 1 (by rfl) ⟨7748387, by rfl⟩ : syracuseStep 10331183 = 15496775) B15496775
theorem B1909919 : Blo 754331 1909919 := bstep (se 1 (by rfl) ⟨1432439, by rfl⟩ : syracuseStep 1909919 = 2864879) B2864879
theorem B1910263 : Blo 754331 1910263 := bstep (se 1 (by rfl) ⟨1432697, by rfl⟩ : syracuseStep 1910263 = 2865395) B2865395
theorem B2041595 : Blo 754331 2041595 := bstep (se 1 (by rfl) ⟨1531196, by rfl⟩ : syracuseStep 2041595 = 3062393) B3062393
theorem B1910537 : Blo 754331 1910537 := bstep (se 2 (by rfl) ⟨716451, by rfl⟩ : syracuseStep 1910537 = 1432903) B1432903
theorem B1910567 : Blo 754331 1910567 := bstep (se 1 (by rfl) ⟨1432925, by rfl⟩ : syracuseStep 1910567 = 2865851) B2865851
theorem B4303151 : Blo 754331 4303151 := bstep (se 1 (by rfl) ⟨3227363, by rfl⟩ : syracuseStep 4303151 = 6454727) B6454727
theorem B4303469 : Blo 754331 4303469 := bstep (se 3 (by rfl) ⟨806900, by rfl⟩ : syracuseStep 4303469 = 1613801) B1613801
theorem B134720293 : Blo 754331 134720293 := bstep (se 4 (by rfl) ⟨12630027, by rfl⟩ : syracuseStep 134720293 = 25260055) B25260055
theorem B1911995 : Blo 754331 1911995 := bstep (se 1 (by rfl) ⟨1433996, by rfl⟩ : syracuseStep 1911995 = 2867993) B2867993
theorem B7253459 : Blo 754331 7253459 := bstep (se 1 (by rfl) ⟨5440094, by rfl⟩ : syracuseStep 7253459 = 10880189) B10880189
theorem B4304609 : Blo 754331 4304609 := bstep (se 2 (by rfl) ⟨1614228, by rfl⟩ : syracuseStep 4304609 = 3228457) B3228457
theorem B995431 : Blo 754331 995431 := bstep (se 1 (by rfl) ⟨746573, by rfl⟩ : syracuseStep 995431 = 1493147) B1493147
theorem B1618175 : Blo 754331 1618175 := bstep (se 1 (by rfl) ⟨1213631, by rfl⟩ : syracuseStep 1618175 = 2427263) B2427263
theorem B9712331 : Blo 754331 9712331 := bstep (se 1 (by rfl) ⟨7284248, by rfl⟩ : syracuseStep 9712331 = 14568497) B14568497
theorem B1749919 : Blo 754331 1749919 := bstep (se 1 (by rfl) ⟨1312439, by rfl⟩ : syracuseStep 1749919 = 2624879) B2624879
theorem B1913939 : Blo 754331 1913939 := bstep (se 1 (by rfl) ⟨1435454, by rfl⟩ : syracuseStep 1913939 = 2870909) B2870909
theorem B5453011 : Blo 754331 5453011 := bstep (se 1 (by rfl) ⟨4089758, by rfl⟩ : syracuseStep 5453011 = 8179517) B8179517
theorem B6206797 : Blo 754331 6206797 := bstep (se 3 (by rfl) ⟨1163774, by rfl⟩ : syracuseStep 6206797 = 2327549) B2327549
theorem B1914779 : Blo 754331 1914779 := bstep (se 1 (by rfl) ⟨1436084, by rfl⟩ : syracuseStep 1914779 = 2872169) B2872169
theorem B6142711 : Blo 754331 6142711 := bstep (se 1 (by rfl) ⟨4607033, by rfl⟩ : syracuseStep 6142711 = 9214067) B9214067
theorem B1915771 : Blo 754331 1915771 := bstep (se 1 (by rfl) ⟨1436828, by rfl⟩ : syracuseStep 1915771 = 2873657) B2873657
theorem B7389161 : Blo 754331 7389161 := bstep (se 2 (by rfl) ⟨2770935, by rfl⟩ : syracuseStep 7389161 = 5541871) B5541871
theorem B1228943 : Blo 754331 1228943 := bstep (se 1 (by rfl) ⟨921707, by rfl⟩ : syracuseStep 1228943 = 1843415) B1843415
theorem B6472223 : Blo 754331 6472223 := bstep (se 1 (by rfl) ⟨4854167, by rfl⟩ : syracuseStep 6472223 = 9708335) B9708335
theorem B1131641 : Blo 754331 1131641 := bstep (se 2 (by rfl) ⟨424365, by rfl⟩ : syracuseStep 1131641 = 848731) B848731
theorem B1131839 : Blo 754331 1131839 := bstep (se 1 (by rfl) ⟨848879, by rfl⟩ : syracuseStep 1131839 = 1697759) B1697759
theorem B9324001 : Blo 754331 9324001 := bstep (se 2 (by rfl) ⟨3496500, by rfl⟩ : syracuseStep 9324001 = 6993001) B6993001
theorem B3819311 : Blo 754331 3819311 := bstep (se 1 (by rfl) ⟨2864483, by rfl⟩ : syracuseStep 3819311 = 5728967) B5728967
theorem B1132511 : Blo 754331 1132511 := bstep (se 1 (by rfl) ⟨849383, by rfl⟩ : syracuseStep 1132511 = 1698767) B1698767
theorem B1132571 : Blo 754331 1132571 := bstep (se 1 (by rfl) ⟨849428, by rfl⟩ : syracuseStep 1132571 = 1698857) B1698857
theorem B1132727 : Blo 754331 1132727 := bstep (se 1 (by rfl) ⟨849545, by rfl⟩ : syracuseStep 1132727 = 1699091) B1699091
theorem B1132751 : Blo 754331 1132751 := bstep (se 1 (by rfl) ⟨849563, by rfl⟩ : syracuseStep 1132751 = 1699127) B1699127
theorem B4835663 : Blo 754331 4835663 := bstep (se 1 (by rfl) ⟨3626747, by rfl⟩ : syracuseStep 4835663 = 7253495) B7253495
theorem B1133147 : Blo 754331 1133147 := bstep (se 1 (by rfl) ⟨849860, by rfl⟩ : syracuseStep 1133147 = 1699721) B1699721
theorem B1133291 : Blo 754331 1133291 := bstep (se 1 (by rfl) ⟨849968, by rfl⟩ : syracuseStep 1133291 = 1699937) B1699937
theorem B3066623 : Blo 754331 3066623 := bstep (se 1 (by rfl) ⟨2299967, by rfl⟩ : syracuseStep 3066623 = 4599935) B4599935
theorem B8637191 : Blo 754331 8637191 := bstep (se 1 (by rfl) ⟨6477893, by rfl⟩ : syracuseStep 8637191 = 12955787) B12955787
theorem B1133321 : Blo 754331 1133321 := bstep (se 2 (by rfl) ⟨424995, by rfl⟩ : syracuseStep 1133321 = 849991) B849991
theorem B8276779 : Blo 754331 8276779 := bstep (se 1 (by rfl) ⟨6207584, by rfl⟩ : syracuseStep 8276779 = 12415169) B12415169
theorem B10931219 : Blo 754331 10931219 := bstep (se 1 (by rfl) ⟨8198414, by rfl⟩ : syracuseStep 10931219 = 16396829) B16396829
theorem B9686087 : Blo 754331 9686087 := bstep (se 1 (by rfl) ⟨7264565, by rfl⟩ : syracuseStep 9686087 = 14529131) B14529131
theorem B1133735 : Blo 754331 1133735 := bstep (se 1 (by rfl) ⟨850301, by rfl⟩ : syracuseStep 1133735 = 1700603) B1700603
theorem B3231019 : Blo 754331 3231019 := bstep (se 1 (by rfl) ⟨2423264, by rfl⟩ : syracuseStep 3231019 = 4846529) B4846529
theorem B1133879 : Blo 754331 1133879 := bstep (se 1 (by rfl) ⟨850409, by rfl⟩ : syracuseStep 1133879 = 1700819) B1700819
theorem B2149753 : Blo 754331 2149753 := bstep (se 2 (by rfl) ⟨806157, by rfl⟩ : syracuseStep 2149753 = 1612315) B1612315
theorem B3067465 : Blo 754331 3067465 := bstep (se 2 (by rfl) ⟨1150299, by rfl⟩ : syracuseStep 3067465 = 2300599) B2300599
theorem B1134191 : Blo 754331 1134191 := bstep (se 1 (by rfl) ⟨850643, by rfl⟩ : syracuseStep 1134191 = 1701287) B1701287
theorem B1134263 : Blo 754331 1134263 := bstep (se 1 (by rfl) ⟨850697, by rfl⟩ : syracuseStep 1134263 = 1701395) B1701395
theorem B1134311 : Blo 754331 1134311 := bstep (se 1 (by rfl) ⟨850733, by rfl⟩ : syracuseStep 1134311 = 1701467) B1701467
theorem B1363721 : Blo 754331 1363721 := bstep (se 2 (by rfl) ⟨511395, by rfl⟩ : syracuseStep 1363721 = 1022791) B1022791
theorem B32755589 : Blo 754331 32755589 := bstep (se 4 (by rfl) ⟨3070836, by rfl⟩ : syracuseStep 32755589 = 6141673) B6141673
theorem B1134473 : Blo 754331 1134473 := bstep (se 2 (by rfl) ⟨425427, by rfl⟩ : syracuseStep 1134473 = 850855) B850855
theorem B1134713 : Blo 754331 1134713 := bstep (se 2 (by rfl) ⟨425517, by rfl⟩ : syracuseStep 1134713 = 851035) B851035
theorem B1134719 : Blo 754331 1134719 := bstep (se 1 (by rfl) ⟨851039, by rfl⟩ : syracuseStep 1134719 = 1702079) B1702079
theorem B2151143 : Blo 754331 2151143 := bstep (se 1 (by rfl) ⟨1613357, by rfl⟩ : syracuseStep 2151143 = 3226715) B3226715
theorem B1135559 : Blo 754331 1135559 := bstep (se 1 (by rfl) ⟨851669, by rfl⟩ : syracuseStep 1135559 = 1703339) B1703339
theorem B1135583 : Blo 754331 1135583 := bstep (se 1 (by rfl) ⟨851687, by rfl⟩ : syracuseStep 1135583 = 1703375) B1703375
theorem B1135919 : Blo 754331 1135919 := bstep (se 1 (by rfl) ⟨851939, by rfl⟩ : syracuseStep 1135919 = 1703879) B1703879
theorem B1136123 : Blo 754331 1136123 := bstep (se 1 (by rfl) ⟨852092, by rfl⟩ : syracuseStep 1136123 = 1704185) B1704185
theorem B1136159 : Blo 754331 1136159 := bstep (se 1 (by rfl) ⟨852119, by rfl⟩ : syracuseStep 1136159 = 1704239) B1704239
theorem B13129381 : Blo 754331 13129381 := bstep (se 4 (by rfl) ⟨1230879, by rfl⟩ : syracuseStep 13129381 = 2461759) B2461759
theorem B1136297 : Blo 754331 1136297 := bstep (se 2 (by rfl) ⟨426111, by rfl⟩ : syracuseStep 1136297 = 852223) B852223
theorem B1136303 : Blo 754331 1136303 := bstep (se 1 (by rfl) ⟨852227, by rfl⟩ : syracuseStep 1136303 = 1704455) B1704455
theorem B1136423 : Blo 754331 1136423 := bstep (se 1 (by rfl) ⟨852317, by rfl⟩ : syracuseStep 1136423 = 1704635) B1704635
theorem B1136681 : Blo 754331 1136681 := bstep (se 2 (by rfl) ⟨426255, by rfl⟩ : syracuseStep 1136681 = 852511) B852511
theorem B1136711 : Blo 754331 1136711 := bstep (se 1 (by rfl) ⟨852533, by rfl⟩ : syracuseStep 1136711 = 1705067) B1705067
theorem B13064327 : Blo 754331 13064327 := bstep (se 1 (by rfl) ⟨9798245, by rfl⟩ : syracuseStep 13064327 = 19596491) B19596491
theorem B8181977 : Blo 754331 8181977 := bstep (se 2 (by rfl) ⟨3068241, by rfl⟩ : syracuseStep 8181977 = 6136483) B6136483
theorem B3823847 : Blo 754331 3823847 := bstep (se 1 (by rfl) ⟨2867885, by rfl⟩ : syracuseStep 3823847 = 5735771) B5735771
theorem B2873627 : Blo 754331 2873627 := bstep (se 1 (by rfl) ⟨2155220, by rfl⟩ : syracuseStep 2873627 = 4310441) B4310441
theorem B1137023 : Blo 754331 1137023 := bstep (se 1 (by rfl) ⟨852767, by rfl⟩ : syracuseStep 1137023 = 1705535) B1705535
theorem B1137095 : Blo 754331 1137095 := bstep (se 1 (by rfl) ⟨852821, by rfl⟩ : syracuseStep 1137095 = 1705643) B1705643
theorem B2152919 : Blo 754331 2152919 := bstep (se 1 (by rfl) ⟨1614689, by rfl⟩ : syracuseStep 2152919 = 3229379) B3229379
theorem B20666843 : Blo 754331 20666843 := bstep (se 1 (by rfl) ⟨15500132, by rfl⟩ : syracuseStep 20666843 = 31000265) B31000265
theorem B1137311 : Blo 754331 1137311 := bstep (se 1 (by rfl) ⟨852983, by rfl⟩ : syracuseStep 1137311 = 1705967) B1705967
theorem B809767 : Blo 754331 809767 := bstep (se 1 (by rfl) ⟨607325, by rfl⟩ : syracuseStep 809767 = 1214651) B1214651
theorem B1137455 : Blo 754331 1137455 := bstep (se 1 (by rfl) ⟨853091, by rfl⟩ : syracuseStep 1137455 = 1706183) B1706183
theorem B4414397 : Blo 754331 4414397 := bstep (se 3 (by rfl) ⟨827699, by rfl⟩ : syracuseStep 4414397 = 1655399) B1655399
theorem B2546747 : Blo 754331 2546747 := bstep (se 1 (by rfl) ⟨1910060, by rfl⟩ : syracuseStep 2546747 = 3820121) B3820121
theorem B1432667 : Blo 754331 1432667 := bstep (se 1 (by rfl) ⟨1074500, by rfl⟩ : syracuseStep 1432667 = 2149001) B2149001
theorem B1531105 : Blo 754331 1531105 := bstep (se 2 (by rfl) ⟨574164, by rfl⟩ : syracuseStep 1531105 = 1148329) B1148329
theorem B2874599 : Blo 754331 2874599 := bstep (se 1 (by rfl) ⟨2155949, by rfl⟩ : syracuseStep 2874599 = 4311899) B4311899
theorem B2153911 : Blo 754331 2153911 := bstep (se 1 (by rfl) ⟨1615433, by rfl⟩ : syracuseStep 2153911 = 3230867) B3230867
theorem B3104225 : Blo 754331 3104225 := bstep (se 2 (by rfl) ⟨1164084, by rfl⟩ : syracuseStep 3104225 = 2328169) B2328169
theorem B3825143 : Blo 754331 3825143 := bstep (se 1 (by rfl) ⟨2868857, by rfl⟩ : syracuseStep 3825143 = 5737715) B5737715
theorem B876271 : Blo 754331 876271 := bstep (se 1 (by rfl) ⟨657203, by rfl⟩ : syracuseStep 876271 = 1314407) B1314407
theorem B13132151 : Blo 754331 13132151 := bstep (se 1 (by rfl) ⟨9849113, by rfl⟩ : syracuseStep 13132151 = 19698227) B19698227
theorem B2548367 : Blo 754331 2548367 := bstep (se 1 (by rfl) ⟨1911275, by rfl⟩ : syracuseStep 2548367 = 3822551) B3822551
theorem B6546187 : Blo 754331 6546187 := bstep (se 1 (by rfl) ⟨4909640, by rfl⟩ : syracuseStep 6546187 = 9819281) B9819281
theorem B2548745 : Blo 754331 2548745 := bstep (se 2 (by rfl) ⟨955779, by rfl⟩ : syracuseStep 2548745 = 1911559) B1911559
theorem B4842611 : Blo 754331 4842611 := bstep (se 1 (by rfl) ⟨3631958, by rfl⟩ : syracuseStep 4842611 = 7263917) B7263917
theorem B17458541 : Blo 754331 17458541 := bstep (se 3 (by rfl) ⟨3273476, by rfl⟩ : syracuseStep 17458541 = 6546953) B6546953
theorem B1434991 : Blo 754331 1434991 := bstep (se 1 (by rfl) ⟨1076243, by rfl⟩ : syracuseStep 1434991 = 2152487) B2152487
theorem B1697255 : Blo 754331 1697255 := bstep (se 1 (by rfl) ⟨1272941, by rfl⟩ : syracuseStep 1697255 = 2545883) B2545883
theorem B1697435 : Blo 754331 1697435 := bstep (se 1 (by rfl) ⟨1273076, by rfl⟩ : syracuseStep 1697435 = 2546153) B2546153
theorem B2156519 : Blo 754331 2156519 := bstep (se 1 (by rfl) ⟨1617389, by rfl⟩ : syracuseStep 2156519 = 3234779) B3234779
theorem B3828059 : Blo 754331 3828059 := bstep (se 1 (by rfl) ⟨2871044, by rfl⟩ : syracuseStep 3828059 = 5742089) B5742089
theorem B1534439 : Blo 754331 1534439 := bstep (se 1 (by rfl) ⟨1150829, by rfl⟩ : syracuseStep 1534439 = 2301659) B2301659
theorem B3828221 : Blo 754331 3828221 := bstep (se 3 (by rfl) ⟨717791, by rfl⟩ : syracuseStep 3828221 = 1435583) B1435583
theorem B1698407 : Blo 754331 1698407 := bstep (se 1 (by rfl) ⟨1273805, by rfl⟩ : syracuseStep 1698407 = 2547611) B2547611
theorem B1698785 : Blo 754331 1698785 := bstep (se 2 (by rfl) ⟨637044, by rfl⟩ : syracuseStep 1698785 = 1274089) B1274089
theorem B2158433 : Blo 754331 2158433 := bstep (se 2 (by rfl) ⟨809412, by rfl⟩ : syracuseStep 2158433 = 1618825) B1618825
theorem B4092029 : Blo 754331 4092029 := bstep (se 3 (by rfl) ⟨767255, by rfl⟩ : syracuseStep 4092029 = 1534511) B1534511
theorem B17494481 : Blo 754331 17494481 := bstep (se 2 (by rfl) ⟨6560430, by rfl⟩ : syracuseStep 17494481 = 13120861) B13120861
theorem B5730911 : Blo 754331 5730911 := bstep (se 1 (by rfl) ⟨4298183, by rfl⟩ : syracuseStep 5730911 = 8596367) B8596367
theorem B1209115 : Blo 754331 1209115 := bstep (se 1 (by rfl) ⟨906836, by rfl⟩ : syracuseStep 1209115 = 1813673) B1813673
theorem B43578161 : Blo 754331 43578161 := bstep (se 2 (by rfl) ⟨16341810, by rfl⟩ : syracuseStep 43578161 = 32683621) B32683621
theorem B1438697 : Blo 754331 1438697 := bstep (se 2 (by rfl) ⟨539511, by rfl⟩ : syracuseStep 1438697 = 1079023) B1079023
theorem B1701449 : Blo 754331 1701449 := bstep (se 2 (by rfl) ⟨638043, by rfl⟩ : syracuseStep 1701449 = 1276087) B1276087
theorem B6453017 : Blo 754331 6453017 := bstep (se 2 (by rfl) ⟨2419881, by rfl⟩ : syracuseStep 6453017 = 4839763) B4839763
theorem B4093757 : Blo 754331 4093757 := bstep (se 3 (by rfl) ⟨767579, by rfl⟩ : syracuseStep 4093757 = 1535159) B1535159
theorem B1275871 : Blo 754331 1275871 := bstep (se 1 (by rfl) ⟨956903, by rfl⟩ : syracuseStep 1275871 = 1913807) B1913807
theorem B1702241 : Blo 754331 1702241 := bstep (se 2 (by rfl) ⟨638340, by rfl⟩ : syracuseStep 1702241 = 1276681) B1276681
theorem B1702331 : Blo 754331 1702331 := bstep (se 1 (by rfl) ⟨1276748, by rfl⟩ : syracuseStep 1702331 = 2553497) B2553497
theorem B3635705 : Blo 754331 3635705 := bstep (se 2 (by rfl) ⟨1363389, by rfl⟩ : syracuseStep 3635705 = 2726779) B2726779
theorem B4848169 : Blo 754331 4848169 := bstep (se 2 (by rfl) ⟨1818063, by rfl⟩ : syracuseStep 4848169 = 3636127) B3636127
theorem B2554847 : Blo 754331 2554847 := bstep (se 1 (by rfl) ⟨1916135, by rfl⟩ : syracuseStep 2554847 = 3832271) B3832271
theorem B3833243 : Blo 754331 3833243 := bstep (se 1 (by rfl) ⟨2874932, by rfl⟩ : syracuseStep 3833243 = 5749865) B5749865
theorem B1703591 : Blo 754331 1703591 := bstep (se 1 (by rfl) ⟨1277693, by rfl⟩ : syracuseStep 1703591 = 2555387) B2555387
theorem B1703699 : Blo 754331 1703699 := bstep (se 1 (by rfl) ⟨1277774, by rfl⟩ : syracuseStep 1703699 = 2555549) B2555549
theorem B1703771 : Blo 754331 1703771 := bstep (se 1 (by rfl) ⟨1277828, by rfl⟩ : syracuseStep 1703771 = 2555657) B2555657
theorem B3277181 : Blo 754331 3277181 := bstep (se 3 (by rfl) ⟨614471, by rfl⟩ : syracuseStep 3277181 = 1228943) B1228943
theorem B754427 : Blo 754331 754427 := bstep (se 1 (by rfl) ⟨565820, by rfl⟩ : syracuseStep 754427 = 1131641) B1131641
theorem B1573663 : Blo 754331 1573663 := bstep (se 1 (by rfl) ⟨1180247, by rfl⟩ : syracuseStep 1573663 = 2360495) B2360495
theorem B754559 : Blo 754331 754559 := bstep (se 1 (by rfl) ⟨565919, by rfl⟩ : syracuseStep 754559 = 1131839) B1131839
theorem B1279145 : Blo 754331 1279145 := bstep (se 2 (by rfl) ⟨479679, by rfl⟩ : syracuseStep 1279145 = 959359) B959359
theorem B4981979 : Blo 754331 4981979 := bstep (se 1 (by rfl) ⟨3736484, by rfl⟩ : syracuseStep 4981979 = 7472969) B7472969
theorem B755007 : Blo 754331 755007 := bstep (se 1 (by rfl) ⟨566255, by rfl⟩ : syracuseStep 755007 = 1132511) B1132511
theorem B14550353 : Blo 754331 14550353 := bstep (se 2 (by rfl) ⟨5456382, by rfl⟩ : syracuseStep 14550353 = 10912765) B10912765
theorem B755047 : Blo 754331 755047 := bstep (se 1 (by rfl) ⟨566285, by rfl⟩ : syracuseStep 755047 = 1132571) B1132571
theorem B755151 : Blo 754331 755151 := bstep (se 1 (by rfl) ⟨566363, by rfl⟩ : syracuseStep 755151 = 1132727) B1132727
theorem B755167 : Blo 754331 755167 := bstep (se 1 (by rfl) ⟨566375, by rfl⟩ : syracuseStep 755167 = 1132751) B1132751
theorem B755431 : Blo 754331 755431 := bstep (se 1 (by rfl) ⟨566573, by rfl⟩ : syracuseStep 755431 = 1133147) B1133147
theorem B6555439 : Blo 754331 6555439 := bstep (se 1 (by rfl) ⟨4916579, by rfl⟩ : syracuseStep 6555439 = 9833159) B9833159
theorem B755527 : Blo 754331 755527 := bstep (se 1 (by rfl) ⟨566645, by rfl⟩ : syracuseStep 755527 = 1133291) B1133291
theorem B755547 : Blo 754331 755547 := bstep (se 1 (by rfl) ⟨566660, by rfl⟩ : syracuseStep 755547 = 1133321) B1133321
theorem B6457391 : Blo 754331 6457391 := bstep (se 1 (by rfl) ⟨4843043, by rfl⟩ : syracuseStep 6457391 = 9686087) B9686087
theorem B755823 : Blo 754331 755823 := bstep (se 1 (by rfl) ⟨566867, by rfl⟩ : syracuseStep 755823 = 1133735) B1133735
theorem B5441735 : Blo 754331 5441735 := bstep (se 1 (by rfl) ⟨4081301, by rfl⟩ : syracuseStep 5441735 = 8162603) B8162603
theorem B755919 : Blo 754331 755919 := bstep (se 1 (by rfl) ⟨566939, by rfl⟩ : syracuseStep 755919 = 1133879) B1133879
theorem B2558195 : Blo 754331 2558195 := bstep (se 1 (by rfl) ⟨1918646, by rfl⟩ : syracuseStep 2558195 = 3837293) B3837293
theorem B756127 : Blo 754331 756127 := bstep (se 1 (by rfl) ⟨567095, by rfl⟩ : syracuseStep 756127 = 1134191) B1134191
theorem B756175 : Blo 754331 756175 := bstep (se 1 (by rfl) ⟨567131, by rfl⟩ : syracuseStep 756175 = 1134263) B1134263
theorem B756207 : Blo 754331 756207 := bstep (se 1 (by rfl) ⟨567155, by rfl⟩ : syracuseStep 756207 = 1134311) B1134311
theorem B756315 : Blo 754331 756315 := bstep (se 1 (by rfl) ⟨567236, by rfl⟩ : syracuseStep 756315 = 1134473) B1134473
theorem B756475 : Blo 754331 756475 := bstep (se 1 (by rfl) ⟨567356, by rfl⟩ : syracuseStep 756475 = 1134713) B1134713
theorem B756479 : Blo 754331 756479 := bstep (se 1 (by rfl) ⟨567359, by rfl⟩ : syracuseStep 756479 = 1134719) B1134719
theorem B2559059 : Blo 754331 2559059 := bstep (se 1 (by rfl) ⟨1919294, by rfl⟩ : syracuseStep 2559059 = 3838589) B3838589
theorem B757039 : Blo 754331 757039 := bstep (se 1 (by rfl) ⟨567779, by rfl⟩ : syracuseStep 757039 = 1135559) B1135559
theorem B757055 : Blo 754331 757055 := bstep (se 1 (by rfl) ⟨567791, by rfl⟩ : syracuseStep 757055 = 1135583) B1135583
theorem B4853195 : Blo 754331 4853195 := bstep (se 1 (by rfl) ⟨3639896, by rfl⟩ : syracuseStep 4853195 = 7279793) B7279793
theorem B757279 : Blo 754331 757279 := bstep (se 1 (by rfl) ⟨567959, by rfl⟩ : syracuseStep 757279 = 1135919) B1135919
theorem B757415 : Blo 754331 757415 := bstep (se 1 (by rfl) ⟨568061, by rfl⟩ : syracuseStep 757415 = 1136123) B1136123
theorem B757439 : Blo 754331 757439 := bstep (se 1 (by rfl) ⟨568079, by rfl⟩ : syracuseStep 757439 = 1136159) B1136159
theorem B757531 : Blo 754331 757531 := bstep (se 1 (by rfl) ⟨568148, by rfl⟩ : syracuseStep 757531 = 1136297) B1136297
theorem B757535 : Blo 754331 757535 := bstep (se 1 (by rfl) ⟨568151, by rfl⟩ : syracuseStep 757535 = 1136303) B1136303
theorem B757615 : Blo 754331 757615 := bstep (se 1 (by rfl) ⟨568211, by rfl⟩ : syracuseStep 757615 = 1136423) B1136423
theorem B2428903 : Blo 754331 2428903 := bstep (se 1 (by rfl) ⟨1821677, by rfl⟩ : syracuseStep 2428903 = 3643355) B3643355
theorem B757787 : Blo 754331 757787 := bstep (se 1 (by rfl) ⟨568340, by rfl⟩ : syracuseStep 757787 = 1136681) B1136681
theorem B757807 : Blo 754331 757807 := bstep (se 1 (by rfl) ⟨568355, by rfl⟩ : syracuseStep 757807 = 1136711) B1136711
theorem B758015 : Blo 754331 758015 := bstep (se 1 (by rfl) ⟨568511, by rfl⟩ : syracuseStep 758015 = 1137023) B1137023
theorem B758063 : Blo 754331 758063 := bstep (se 1 (by rfl) ⟨568547, by rfl⟩ : syracuseStep 758063 = 1137095) B1137095
theorem B758207 : Blo 754331 758207 := bstep (se 1 (by rfl) ⟨568655, by rfl⟩ : syracuseStep 758207 = 1137311) B1137311
theorem B758303 : Blo 754331 758303 := bstep (se 1 (by rfl) ⟨568727, by rfl⟩ : syracuseStep 758303 = 1137455) B1137455
theorem B2069483 : Blo 754331 2069483 := bstep (se 1 (by rfl) ⟨1552112, by rfl⟩ : syracuseStep 2069483 = 3104225) B3104225
theorem B8754767 : Blo 754331 8754767 := bstep (se 1 (by rfl) ⟨6566075, by rfl⟩ : syracuseStep 8754767 = 13132151) B13132151
theorem B11639027 : Blo 754331 11639027 := bstep (se 1 (by rfl) ⟨8729270, by rfl⟩ : syracuseStep 11639027 = 17458541) B17458541
theorem B1612153 : Blo 754331 1612153 := bstep (se 2 (by rfl) ⟨604557, by rfl⟩ : syracuseStep 1612153 = 1209115) B1209115
theorem B8165893 : Blo 754331 8165893 := bstep (se 4 (by rfl) ⟨765552, by rfl⟩ : syracuseStep 8165893 = 1531105) B1531105
theorem B2333225 : Blo 754331 2333225 := bstep (se 2 (by rfl) ⟨874959, by rfl⟩ : syracuseStep 2333225 = 1749919) B1749919
theorem B5741117 : Blo 754331 5741117 := bstep (se 3 (by rfl) ⟨1076459, by rfl⟩ : syracuseStep 5741117 = 2152919) B2152919
theorem B1022959 : Blo 754331 1022959 := bstep (se 1 (by rfl) ⟨767219, by rfl⟩ : syracuseStep 1022959 = 1534439) B1534439
theorem B17505841 : Blo 754331 17505841 := bstep (se 2 (by rfl) ⟨6564690, by rfl⟩ : syracuseStep 17505841 = 13129381) B13129381
theorem B18358073 : Blo 754331 18358073 := bstep (se 2 (by rfl) ⟨6884277, by rfl⟩ : syracuseStep 18358073 = 13768555) B13768555
theorem B11771725 : Blo 754331 11771725 := bstep (se 3 (by rfl) ⟨2207198, by rfl⟩ : syracuseStep 11771725 = 4414397) B4414397
theorem B2728019 : Blo 754331 2728019 := bstep (se 1 (by rfl) ⟨2046014, by rfl⟩ : syracuseStep 2728019 = 4092029) B4092029
theorem B21766481 : Blo 754331 21766481 := bstep (se 2 (by rfl) ⟨8162430, by rfl⟩ : syracuseStep 21766481 = 16324861) B16324861
theorem B959131 : Blo 754331 959131 := bstep (se 1 (by rfl) ⟨719348, by rfl⟩ : syracuseStep 959131 = 1438697) B1438697
theorem B6464225 : Blo 754331 6464225 := bstep (se 2 (by rfl) ⟨2424084, by rfl⟩ : syracuseStep 6464225 = 4848169) B4848169
theorem B4302011 : Blo 754331 4302011 := bstep (se 1 (by rfl) ⟨3226508, by rfl⟩ : syracuseStep 4302011 = 6453017) B6453017
theorem B2729171 : Blo 754331 2729171 := bstep (se 1 (by rfl) ⟨2046878, by rfl⟩ : syracuseStep 2729171 = 4093757) B4093757
theorem B4926107 : Blo 754331 4926107 := bstep (se 1 (by rfl) ⟨3694580, by rfl⟩ : syracuseStep 4926107 = 7389161) B7389161
theorem B5745491 : Blo 754331 5745491 := bstep (se 1 (by rfl) ⟨4309118, by rfl⟩ : syracuseStep 5745491 = 8618237) B8618237
theorem B2731133 : Blo 754331 2731133 := bstep (se 3 (by rfl) ⟨512087, by rfl⟩ : syracuseStep 2731133 = 1024175) B1024175
theorem B3059279 : Blo 754331 3059279 := bstep (se 1 (by rfl) ⟨2294459, by rfl⟩ : syracuseStep 3059279 = 4588919) B4588919
theorem B8728249 : Blo 754331 8728249 := bstep (se 2 (by rfl) ⟨3273093, by rfl⟩ : syracuseStep 8728249 = 6546187) B6546187
theorem B8171603 : Blo 754331 8171603 := bstep (se 1 (by rfl) ⟨6128702, by rfl⟩ : syracuseStep 8171603 = 12257405) B12257405
theorem B3223775 : Blo 754331 3223775 := bstep (se 1 (by rfl) ⟨2417831, by rfl⟩ : syracuseStep 3223775 = 4835663) B4835663
theorem B1913321 : Blo 754331 1913321 := bstep (se 2 (by rfl) ⟨717495, by rfl⟩ : syracuseStep 1913321 = 1434991) B1434991
theorem B2044415 : Blo 754331 2044415 := bstep (se 1 (by rfl) ⟨1533311, by rfl⟩ : syracuseStep 2044415 = 3066623) B3066623
theorem B12432001 : Blo 754331 12432001 := bstep (se 2 (by rfl) ⟨4662000, by rfl⟩ : syracuseStep 12432001 = 9324001) B9324001
theorem B7287479 : Blo 754331 7287479 := bstep (se 1 (by rfl) ⟨5465609, by rfl⟩ : syracuseStep 7287479 = 10931219) B10931219
theorem B5747435 : Blo 754331 5747435 := bstep (se 1 (by rfl) ⟨4310576, by rfl⟩ : syracuseStep 5747435 = 8621153) B8621153
theorem B21837059 : Blo 754331 21837059 := bstep (se 1 (by rfl) ⟨16377794, by rfl⟩ : syracuseStep 21837059 = 32755589) B32755589
theorem B1915751 : Blo 754331 1915751 := bstep (se 1 (by rfl) ⟨1436813, by rfl⟩ : syracuseStep 1915751 = 2873627) B2873627
theorem B13777895 : Blo 754331 13777895 := bstep (se 1 (by rfl) ⟨10333421, by rfl⟩ : syracuseStep 13777895 = 20666843) B20666843
theorem B4308025 : Blo 754331 4308025 := bstep (se 2 (by rfl) ⟨1615509, by rfl⟩ : syracuseStep 4308025 = 3231019) B3231019
theorem B2866337 : Blo 754331 2866337 := bstep (se 2 (by rfl) ⟨1074876, by rfl⟩ : syracuseStep 2866337 = 2149753) B2149753
theorem B1916399 : Blo 754331 1916399 := bstep (se 1 (by rfl) ⟨1437299, by rfl⟩ : syracuseStep 1916399 = 2874599) B2874599
theorem B43696259 : Blo 754331 43696259 := bstep (se 1 (by rfl) ⟨32772194, by rfl⟩ : syracuseStep 43696259 = 65544389) B65544389
theorem B1327241 : Blo 754331 1327241 := bstep (se 2 (by rfl) ⟨497715, by rfl⟩ : syracuseStep 1327241 = 995431) B995431
theorem B3228407 : Blo 754331 3228407 := bstep (se 1 (by rfl) ⟨2421305, by rfl⟩ : syracuseStep 3228407 = 4842611) B4842611
theorem B1131503 : Blo 754331 1131503 := bstep (se 1 (by rfl) ⟨848627, by rfl⟩ : syracuseStep 1131503 = 1697255) B1697255
theorem B1131623 : Blo 754331 1131623 := bstep (se 1 (by rfl) ⟨848717, by rfl⟩ : syracuseStep 1131623 = 1697435) B1697435
theorem B1361063 : Blo 754331 1361063 := bstep (se 1 (by rfl) ⟨1020797, by rfl⟩ : syracuseStep 1361063 = 2041595) B2041595
theorem B2868767 : Blo 754331 2868767 := bstep (se 1 (by rfl) ⟨2151575, by rfl⟩ : syracuseStep 2868767 = 4303151) B4303151
theorem B1132271 : Blo 754331 1132271 := bstep (se 1 (by rfl) ⟨849203, by rfl⟩ : syracuseStep 1132271 = 1698407) B1698407
theorem B2868979 : Blo 754331 2868979 := bstep (se 1 (by rfl) ⟨2151734, by rfl⟩ : syracuseStep 2868979 = 4303469) B4303469
theorem B8275729 : Blo 754331 8275729 := bstep (se 2 (by rfl) ⟨3103398, by rfl⟩ : syracuseStep 8275729 = 6206797) B6206797
theorem B1132523 : Blo 754331 1132523 := bstep (se 1 (by rfl) ⟨849392, by rfl⟩ : syracuseStep 1132523 = 1698785) B1698785
theorem B4835639 : Blo 754331 4835639 := bstep (se 1 (by rfl) ⟨3626729, by rfl⟩ : syracuseStep 4835639 = 7253459) B7253459
theorem B2869739 : Blo 754331 2869739 := bstep (se 1 (by rfl) ⟨2152304, by rfl⟩ : syracuseStep 2869739 = 4304609) B4304609
theorem B3820445 : Blo 754331 3820445 := bstep (se 3 (by rfl) ⟨716333, by rfl⟩ : syracuseStep 3820445 = 1432667) B1432667
theorem B3820607 : Blo 754331 3820607 := bstep (se 1 (by rfl) ⟨2865455, by rfl⟩ : syracuseStep 3820607 = 5730911) B5730911
theorem B6474887 : Blo 754331 6474887 := bstep (se 1 (by rfl) ⟨4856165, by rfl⟩ : syracuseStep 6474887 = 9712331) B9712331
theorem B29052107 : Blo 754331 29052107 := bstep (se 1 (by rfl) ⟨21789080, by rfl⟩ : syracuseStep 29052107 = 43578161) B43578161
theorem B1134299 : Blo 754331 1134299 := bstep (se 1 (by rfl) ⟨850724, by rfl⟩ : syracuseStep 1134299 = 1701449) B1701449
theorem B1134827 : Blo 754331 1134827 := bstep (se 1 (by rfl) ⟨851120, by rfl⟩ : syracuseStep 1134827 = 1702241) B1702241
theorem B1134887 : Blo 754331 1134887 := bstep (se 1 (by rfl) ⟨851165, by rfl⟩ : syracuseStep 1134887 = 1702331) B1702331
theorem B2871881 : Blo 754331 2871881 := bstep (se 2 (by rfl) ⟨1076955, by rfl⟩ : syracuseStep 2871881 = 2153911) B2153911
theorem B1168361 : Blo 754331 1168361 := bstep (se 2 (by rfl) ⟨438135, by rfl⟩ : syracuseStep 1168361 = 876271) B876271
theorem B1135727 : Blo 754331 1135727 := bstep (se 1 (by rfl) ⟨851795, by rfl⟩ : syracuseStep 1135727 = 1703591) B1703591
theorem B1135799 : Blo 754331 1135799 := bstep (se 1 (by rfl) ⟨851849, by rfl⟩ : syracuseStep 1135799 = 1703699) B1703699
theorem B1135847 : Blo 754331 1135847 := bstep (se 1 (by rfl) ⟨851885, by rfl⟩ : syracuseStep 1135847 = 1703771) B1703771
theorem B1136039 : Blo 754331 1136039 := bstep (se 1 (by rfl) ⟨852029, by rfl⟩ : syracuseStep 1136039 = 1704059) B1704059
theorem B1136219 : Blo 754331 1136219 := bstep (se 1 (by rfl) ⟨852164, by rfl⟩ : syracuseStep 1136219 = 1704329) B1704329
theorem B1136231 : Blo 754331 1136231 := bstep (se 1 (by rfl) ⟨852173, by rfl⟩ : syracuseStep 1136231 = 1704347) B1704347
theorem B4314815 : Blo 754331 4314815 := bstep (se 1 (by rfl) ⟨3236111, by rfl⟩ : syracuseStep 4314815 = 6472223) B6472223
theorem B3233789 : Blo 754331 3233789 := bstep (se 3 (by rfl) ⟨606335, by rfl⟩ : syracuseStep 3233789 = 1212671) B1212671
theorem B4315133 : Blo 754331 4315133 := bstep (se 3 (by rfl) ⟨809087, by rfl⟩ : syracuseStep 4315133 = 1618175) B1618175
theorem B8181809 : Blo 754331 8181809 := bstep (se 2 (by rfl) ⟨3068178, by rfl⟩ : syracuseStep 8181809 = 6136357) B6136357
theorem B1136999 : Blo 754331 1136999 := bstep (se 1 (by rfl) ⟨852749, by rfl⟩ : syracuseStep 1136999 = 1705499) B1705499
theorem B1137065 : Blo 754331 1137065 := bstep (se 2 (by rfl) ⟨426399, by rfl⟩ : syracuseStep 1137065 = 852799) B852799
theorem B2546207 : Blo 754331 2546207 := bstep (se 1 (by rfl) ⟨1909655, by rfl⟩ : syracuseStep 2546207 = 3819311) B3819311
theorem B6118031 : Blo 754331 6118031 := bstep (se 1 (by rfl) ⟨4588523, by rfl⟩ : syracuseStep 6118031 = 9177047) B9177047
theorem B3824495 : Blo 754331 3824495 := bstep (se 1 (by rfl) ⟨2868371, by rfl⟩ : syracuseStep 3824495 = 5736743) B5736743
theorem B5758127 : Blo 754331 5758127 := bstep (se 1 (by rfl) ⟨4318595, by rfl⟩ : syracuseStep 5758127 = 8637191) B8637191
theorem B2547017 : Blo 754331 2547017 := bstep (se 2 (by rfl) ⟨955131, by rfl⟩ : syracuseStep 2547017 = 1910263) B1910263
theorem B3235241 : Blo 754331 3235241 := bstep (se 2 (by rfl) ⟨1213215, by rfl⟩ : syracuseStep 3235241 = 2426431) B2426431
theorem B27549821 : Blo 754331 27549821 := bstep (se 3 (by rfl) ⟨5165591, by rfl⟩ : syracuseStep 27549821 = 10331183) B10331183
theorem B1434095 : Blo 754331 1434095 := bstep (se 1 (by rfl) ⟨1075571, by rfl⟩ : syracuseStep 1434095 = 2151143) B2151143
theorem B3826439 : Blo 754331 3826439 := bstep (se 1 (by rfl) ⟨2869829, by rfl⟩ : syracuseStep 3826439 = 5739659) B5739659
theorem B179627057 : Blo 754331 179627057 := bstep (se 2 (by rfl) ⟨67360146, by rfl⟩ : syracuseStep 179627057 = 134720293) B134720293
theorem B11035705 : Blo 754331 11035705 := bstep (se 2 (by rfl) ⟨4138389, by rfl⟩ : syracuseStep 11035705 = 8276779) B8276779
theorem B1533343 : Blo 754331 1533343 := bstep (se 1 (by rfl) ⟨1150007, by rfl⟩ : syracuseStep 1533343 = 2300015) B2300015
theorem B8709551 : Blo 754331 8709551 := bstep (se 1 (by rfl) ⟨6532163, by rfl⟩ : syracuseStep 8709551 = 13064327) B13064327
theorem B2549231 : Blo 754331 2549231 := bstep (se 1 (by rfl) ⟨1911923, by rfl⟩ : syracuseStep 2549231 = 3823847) B3823847
theorem B4318757 : Blo 754331 4318757 := bstep (se 4 (by rfl) ⟨404883, by rfl⟩ : syracuseStep 4318757 = 809767) B809767
theorem B1697831 : Blo 754331 1697831 := bstep (se 1 (by rfl) ⟨1273373, by rfl⟩ : syracuseStep 1697831 = 2546747) B2546747
theorem B4089953 : Blo 754331 4089953 := bstep (se 2 (by rfl) ⟨1533732, by rfl⟩ : syracuseStep 4089953 = 3067465) B3067465
theorem B2550095 : Blo 754331 2550095 := bstep (se 1 (by rfl) ⟨1912571, by rfl⟩ : syracuseStep 2550095 = 3825143) B3825143
theorem B1075879 : Blo 754331 1075879 := bstep (se 1 (by rfl) ⟨806909, by rfl⟩ : syracuseStep 1075879 = 1613819) B1613819
theorem B1075999 : Blo 754331 1075999 := bstep (se 1 (by rfl) ⟨806999, by rfl⟩ : syracuseStep 1075999 = 1613999) B1613999
theorem B1698911 : Blo 754331 1698911 := bstep (se 1 (by rfl) ⟨1274183, by rfl⟩ : syracuseStep 1698911 = 2548367) B2548367
theorem B1273063 : Blo 754331 1273063 := bstep (se 1 (by rfl) ⟨954797, by rfl⟩ : syracuseStep 1273063 = 1909595) B1909595
theorem B21818605 : Blo 754331 21818605 := bstep (se 3 (by rfl) ⟨4090988, by rfl⟩ : syracuseStep 21818605 = 8181977) B8181977
theorem B1699163 : Blo 754331 1699163 := bstep (se 1 (by rfl) ⟨1274372, by rfl⟩ : syracuseStep 1699163 = 2548745) B2548745
theorem B1273279 : Blo 754331 1273279 := bstep (se 1 (by rfl) ⟨954959, by rfl⟩ : syracuseStep 1273279 = 1909919) B1909919
theorem B1273691 : Blo 754331 1273691 := bstep (se 1 (by rfl) ⟨955268, by rfl⟩ : syracuseStep 1273691 = 1910537) B1910537
theorem B1273711 : Blo 754331 1273711 := bstep (se 1 (by rfl) ⟨955283, by rfl⟩ : syracuseStep 1273711 = 1910567) B1910567
theorem B9695213 : Blo 754331 9695213 := bstep (se 3 (by rfl) ⟨1817852, by rfl⟩ : syracuseStep 9695213 = 3635705) B3635705
theorem B1437679 : Blo 754331 1437679 := bstep (se 1 (by rfl) ⟨1078259, by rfl⟩ : syracuseStep 1437679 = 2156519) B2156519
theorem B2552039 : Blo 754331 2552039 := bstep (se 1 (by rfl) ⟨1914029, by rfl⟩ : syracuseStep 2552039 = 3828059) B3828059
theorem B7270681 : Blo 754331 7270681 := bstep (se 2 (by rfl) ⟨2726505, by rfl⟩ : syracuseStep 7270681 = 5453011) B5453011
theorem B2552147 : Blo 754331 2552147 := bstep (se 1 (by rfl) ⟨1914110, by rfl⟩ : syracuseStep 2552147 = 3828221) B3828221
theorem B1536425 : Blo 754331 1536425 := bstep (se 2 (by rfl) ⟨576159, by rfl⟩ : syracuseStep 1536425 = 1152319) B1152319
theorem B1274663 : Blo 754331 1274663 := bstep (se 1 (by rfl) ⟨955997, by rfl⟩ : syracuseStep 1274663 = 1911995) B1911995
theorem B1438955 : Blo 754331 1438955 := bstep (se 1 (by rfl) ⟨1079216, by rfl⟩ : syracuseStep 1438955 = 2158433) B2158433
theorem B1701161 : Blo 754331 1701161 := bstep (se 2 (by rfl) ⟨637935, by rfl⟩ : syracuseStep 1701161 = 1275871) B1275871
theorem B11662987 : Blo 754331 11662987 := bstep (se 1 (by rfl) ⟨8747240, by rfl⟩ : syracuseStep 11662987 = 17494481) B17494481
theorem B1275959 : Blo 754331 1275959 := bstep (se 1 (by rfl) ⟨956969, by rfl⟩ : syracuseStep 1275959 = 1913939) B1913939
theorem B8190281 : Blo 754331 8190281 := bstep (se 2 (by rfl) ⟨3071355, by rfl⟩ : syracuseStep 8190281 = 6142711) B6142711
theorem B2554361 : Blo 754331 2554361 := bstep (se 2 (by rfl) ⟨957885, by rfl⟩ : syracuseStep 2554361 = 1915771) B1915771
theorem B1276519 : Blo 754331 1276519 := bstep (se 1 (by rfl) ⟨957389, by rfl⟩ : syracuseStep 1276519 = 1914779) B1914779
theorem B1703231 : Blo 754331 1703231 := bstep (se 1 (by rfl) ⟨1277423, by rfl⟩ : syracuseStep 1703231 = 2554847) B2554847
theorem B3636589 : Blo 754331 3636589 := bstep (se 3 (by rfl) ⟨681860, by rfl⟩ : syracuseStep 3636589 = 1363721) B1363721
theorem B1277417 : Blo 754331 1277417 := bstep (se 2 (by rfl) ⟨479031, by rfl⟩ : syracuseStep 1277417 = 958063) B958063
theorem B2555495 : Blo 754331 2555495 := bstep (se 1 (by rfl) ⟨1916621, by rfl⟩ : syracuseStep 2555495 = 3833243) B3833243
theorem B29130839 : Blo 754331 29130839 := bstep (se 1 (by rfl) ⟨21848129, by rfl⟩ : syracuseStep 29130839 = 43696259) B43696259
theorem B884827 : Blo 754331 884827 := bstep (se 1 (by rfl) ⟨663620, by rfl⟩ : syracuseStep 884827 = 1327241) B1327241
theorem B754335 : Blo 754331 754335 := bstep (se 1 (by rfl) ⟨565751, by rfl⟩ : syracuseStep 754335 = 1131503) B1131503
theorem B754415 : Blo 754331 754415 := bstep (se 1 (by rfl) ⟨565811, by rfl⟩ : syracuseStep 754415 = 1131623) B1131623
theorem B852763 : Blo 754331 852763 := bstep (se 1 (by rfl) ⟨639572, by rfl⟩ : syracuseStep 852763 = 1279145) B1279145
theorem B1278841 : Blo 754331 1278841 := bstep (se 2 (by rfl) ⟨479565, by rfl⟩ : syracuseStep 1278841 = 959131) B959131
theorem B9700235 : Blo 754331 9700235 := bstep (se 1 (by rfl) ⟨7275176, by rfl⟩ : syracuseStep 9700235 = 14550353) B14550353
theorem B2098217 : Blo 754331 2098217 := bstep (se 2 (by rfl) ⟨786831, by rfl⟩ : syracuseStep 2098217 = 1573663) B1573663
theorem B754847 : Blo 754331 754847 := bstep (se 1 (by rfl) ⟨566135, by rfl⟩ : syracuseStep 754847 = 1132271) B1132271
theorem B755015 : Blo 754331 755015 := bstep (se 1 (by rfl) ⟨566261, by rfl⟩ : syracuseStep 755015 = 1132523) B1132523
theorem B14714273 : Blo 754331 14714273 := bstep (se 2 (by rfl) ⟨5517852, by rfl⟩ : syracuseStep 14714273 = 11035705) B11035705
theorem B1705463 : Blo 754331 1705463 := bstep (se 1 (by rfl) ⟨1279097, by rfl⟩ : syracuseStep 1705463 = 2558195) B2558195
theorem B1706039 : Blo 754331 1706039 := bstep (se 1 (by rfl) ⟨1279529, by rfl⟩ : syracuseStep 1706039 = 2559059) B2559059
theorem B19368071 : Blo 754331 19368071 := bstep (se 1 (by rfl) ⟨14526053, by rfl⟩ : syracuseStep 19368071 = 29052107) B29052107
theorem B756199 : Blo 754331 756199 := bstep (se 1 (by rfl) ⟨567149, by rfl⟩ : syracuseStep 756199 = 1134299) B1134299
theorem B756551 : Blo 754331 756551 := bstep (se 1 (by rfl) ⟨567413, by rfl⟩ : syracuseStep 756551 = 1134827) B1134827
theorem B756591 : Blo 754331 756591 := bstep (se 1 (by rfl) ⟨567443, by rfl⟩ : syracuseStep 756591 = 1134887) B1134887
theorem B7277789 : Blo 754331 7277789 := bstep (se 3 (by rfl) ⟨1364585, by rfl⟩ : syracuseStep 7277789 = 2729171) B2729171
theorem B757151 : Blo 754331 757151 := bstep (se 1 (by rfl) ⟨567863, by rfl⟩ : syracuseStep 757151 = 1135727) B1135727
theorem B757199 : Blo 754331 757199 := bstep (se 1 (by rfl) ⟨567899, by rfl⟩ : syracuseStep 757199 = 1135799) B1135799
theorem B757231 : Blo 754331 757231 := bstep (se 1 (by rfl) ⟨567923, by rfl⟩ : syracuseStep 757231 = 1135847) B1135847
theorem B757359 : Blo 754331 757359 := bstep (se 1 (by rfl) ⟨568019, by rfl⟩ : syracuseStep 757359 = 1136039) B1136039
theorem B5836511 : Blo 754331 5836511 := bstep (se 1 (by rfl) ⟨4377383, by rfl⟩ : syracuseStep 5836511 = 8754767) B8754767
theorem B757479 : Blo 754331 757479 := bstep (se 1 (by rfl) ⟨568109, by rfl⟩ : syracuseStep 757479 = 1136219) B1136219
theorem B757487 : Blo 754331 757487 := bstep (se 1 (by rfl) ⟨568115, by rfl⟩ : syracuseStep 757487 = 1136231) B1136231
theorem B757999 : Blo 754331 757999 := bstep (se 1 (by rfl) ⟨568499, by rfl⟩ : syracuseStep 757999 = 1136999) B1136999
theorem B758043 : Blo 754331 758043 := bstep (se 1 (by rfl) ⟨568532, by rfl⟩ : syracuseStep 758043 = 1137065) B1137065
theorem B3838751 : Blo 754331 3838751 := bstep (se 1 (by rfl) ⟨2879063, by rfl⟩ : syracuseStep 3838751 = 5758127) B5758127
theorem B11637665 : Blo 754331 11637665 := bstep (se 2 (by rfl) ⟨4364124, by rfl⟩ : syracuseStep 11637665 = 8728249) B8728249
theorem B956063 : Blo 754331 956063 := bstep (se 1 (by rfl) ⟨717047, by rfl⟩ : syracuseStep 956063 = 1434095) B1434095
theorem B5806367 : Blo 754331 5806367 := bstep (se 1 (by rfl) ⟨4354775, by rfl⟩ : syracuseStep 5806367 = 8709551) B8709551
theorem B2726635 : Blo 754331 2726635 := bstep (se 1 (by rfl) ⟨2044976, by rfl⟩ : syracuseStep 2726635 = 4089953) B4089953
theorem B3284071 : Blo 754331 3284071 := bstep (se 1 (by rfl) ⟨2463053, by rfl⟩ : syracuseStep 3284071 = 4926107) B4926107
theorem B2039519 : Blo 754331 2039519 := bstep (se 1 (by rfl) ⟨1529639, by rfl⟩ : syracuseStep 2039519 = 3059279) B3059279
theorem B36741053 : Blo 754331 36741053 := bstep (se 3 (by rfl) ⟨6888947, by rfl⟩ : syracuseStep 36741053 = 13777895) B13777895
theorem B6463475 : Blo 754331 6463475 := bstep (se 1 (by rfl) ⟨4847606, by rfl⟩ : syracuseStep 6463475 = 9695213) B9695213
theorem B5447735 : Blo 754331 5447735 := bstep (se 1 (by rfl) ⟨4085801, by rfl⟩ : syracuseStep 5447735 = 8171603) B8171603
theorem B1024283 : Blo 754331 1024283 := bstep (se 1 (by rfl) ⟨768212, by rfl⟩ : syracuseStep 1024283 = 1536425) B1536425
theorem B4858319 : Blo 754331 4858319 := bstep (se 1 (by rfl) ⟨3643739, by rfl⟩ : syracuseStep 4858319 = 7287479) B7287479
theorem B10887857 : Blo 754331 10887857 := bstep (se 2 (by rfl) ⟨4082946, by rfl⟩ : syracuseStep 10887857 = 8165893) B8165893
theorem B959303 : Blo 754331 959303 := bstep (se 1 (by rfl) ⟨719477, by rfl⟩ : syracuseStep 959303 = 1438955) B1438955
theorem B14558039 : Blo 754331 14558039 := bstep (se 1 (by rfl) ⟨10918529, by rfl⟩ : syracuseStep 14558039 = 21837059) B21837059
theorem B5744033 : Blo 754331 5744033 := bstep (se 2 (by rfl) ⟨2154012, by rfl⟩ : syracuseStep 5744033 = 4308025) B4308025
theorem B23341121 : Blo 754331 23341121 := bstep (se 2 (by rfl) ⟨8752920, by rfl⟩ : syracuseStep 23341121 = 17505841) B17505841
theorem B1910891 : Blo 754331 1910891 := bstep (se 1 (by rfl) ⟨1433168, by rfl⟩ : syracuseStep 1910891 = 2866337) B2866337
theorem B3321319 : Blo 754331 3321319 := bstep (se 1 (by rfl) ⟨2490989, by rfl⟩ : syracuseStep 3321319 = 4981979) B4981979
theorem B1912511 : Blo 754331 1912511 := bstep (se 1 (by rfl) ⟨1434383, by rfl⟩ : syracuseStep 1912511 = 2868767) B2868767
theorem B4304927 : Blo 754331 4304927 := bstep (se 1 (by rfl) ⟨3228695, by rfl⟩ : syracuseStep 4304927 = 6457391) B6457391
theorem B3223759 : Blo 754331 3223759 := bstep (se 1 (by rfl) ⟨2417819, by rfl⟩ : syracuseStep 3223759 = 4835639) B4835639
theorem B1913159 : Blo 754331 1913159 := bstep (se 1 (by rfl) ⟨1434869, by rfl⟩ : syracuseStep 1913159 = 2869739) B2869739
theorem B2044457 : Blo 754331 2044457 := bstep (se 2 (by rfl) ⟨766671, by rfl⟩ : syracuseStep 2044457 = 1533343) B1533343
theorem B5518621 : Blo 754331 5518621 := bstep (se 3 (by rfl) ⟨1034741, by rfl⟩ : syracuseStep 5518621 = 2069483) B2069483
theorem B1914587 : Blo 754331 1914587 := bstep (se 1 (by rfl) ⟨1435940, by rfl⟩ : syracuseStep 1914587 = 2871881) B2871881
theorem B5454539 : Blo 754331 5454539 := bstep (se 1 (by rfl) ⟨4090904, by rfl⟩ : syracuseStep 5454539 = 8181809) B8181809
theorem B4078687 : Blo 754331 4078687 := bstep (se 1 (by rfl) ⟨3059015, by rfl⟩ : syracuseStep 4078687 = 6118031) B6118031
theorem B12238715 : Blo 754331 12238715 := bstep (se 1 (by rfl) ⟨9179036, by rfl⟩ : syracuseStep 12238715 = 18358073) B18358073
theorem B5455781 : Blo 754331 5455781 := bstep (se 4 (by rfl) ⟨511479, by rfl⟩ : syracuseStep 5455781 = 1022959) B1022959
theorem B1916905 : Blo 754331 1916905 := bstep (se 2 (by rfl) ⟨718839, by rfl⟩ : syracuseStep 1916905 = 1437679) B1437679
theorem B1818679 : Blo 754331 1818679 := bstep (se 1 (by rfl) ⟨1364009, by rfl⟩ : syracuseStep 1818679 = 2728019) B2728019
theorem B18366547 : Blo 754331 18366547 := bstep (se 1 (by rfl) ⟨13774910, by rfl⟩ : syracuseStep 18366547 = 27549821) B27549821
theorem B4309483 : Blo 754331 4309483 := bstep (se 1 (by rfl) ⟨3232112, by rfl⟩ : syracuseStep 4309483 = 6464225) B6464225
theorem B119751371 : Blo 754331 119751371 := bstep (se 1 (by rfl) ⟨89813528, by rfl⟩ : syracuseStep 119751371 = 179627057) B179627057
theorem B2868007 : Blo 754331 2868007 := bstep (se 1 (by rfl) ⟨2151005, by rfl⟩ : syracuseStep 2868007 = 4302011) B4302011
theorem B21840749 : Blo 754331 21840749 := bstep (se 3 (by rfl) ⟨4095140, by rfl⟩ : syracuseStep 21840749 = 8190281) B8190281
theorem B1131887 : Blo 754331 1131887 := bstep (se 1 (by rfl) ⟨848915, by rfl⟩ : syracuseStep 1131887 = 1697831) B1697831
theorem B1132607 : Blo 754331 1132607 := bstep (se 1 (by rfl) ⟨849455, by rfl⟩ : syracuseStep 1132607 = 1698911) B1698911
theorem B1820755 : Blo 754331 1820755 := bstep (se 1 (by rfl) ⟨1365566, by rfl⟩ : syracuseStep 1820755 = 2731133) B2731133
theorem B15550649 : Blo 754331 15550649 := bstep (se 2 (by rfl) ⟨5831493, by rfl⟩ : syracuseStep 15550649 = 11662987) B11662987
theorem B1132775 : Blo 754331 1132775 := bstep (se 1 (by rfl) ⟨849581, by rfl⟩ : syracuseStep 1132775 = 1699163) B1699163
theorem B2149183 : Blo 754331 2149183 := bstep (se 1 (by rfl) ⟨1611887, by rfl⟩ : syracuseStep 2149183 = 3223775) B3223775
theorem B1362943 : Blo 754331 1362943 := bstep (se 1 (by rfl) ⟨1022207, by rfl⟩ : syracuseStep 1362943 = 2044415) B2044415
theorem B2149537 : Blo 754331 2149537 := bstep (se 2 (by rfl) ⟨806076, by rfl⟩ : syracuseStep 2149537 = 1612153) B1612153
theorem B1134107 : Blo 754331 1134107 := bstep (se 1 (by rfl) ⟨850580, by rfl⟩ : syracuseStep 1134107 = 1701161) B1701161
theorem B1135487 : Blo 754331 1135487 := bstep (se 1 (by rfl) ⟨851615, by rfl⟩ : syracuseStep 1135487 = 1703231) B1703231
theorem B2184787 : Blo 754331 2184787 := bstep (se 1 (by rfl) ⟨1638590, by rfl⟩ : syracuseStep 2184787 = 3277181) B3277181
theorem B2152271 : Blo 754331 2152271 := bstep (se 1 (by rfl) ⟨1614203, by rfl⟩ : syracuseStep 2152271 = 3228407) B3228407
theorem B907375 : Blo 754331 907375 := bstep (se 1 (by rfl) ⟨680531, by rfl⟩ : syracuseStep 907375 = 1361063) B1361063
theorem B3627823 : Blo 754331 3627823 := bstep (se 1 (by rfl) ⟨2720867, by rfl⟩ : syracuseStep 3627823 = 5441735) B5441735
theorem B2546963 : Blo 754331 2546963 := bstep (se 1 (by rfl) ⟨1910222, by rfl⟩ : syracuseStep 2546963 = 3820445) B3820445
theorem B2547071 : Blo 754331 2547071 := bstep (se 1 (by rfl) ⟨1910303, by rfl⟩ : syracuseStep 2547071 = 3820607) B3820607
theorem B4316591 : Blo 754331 4316591 := bstep (se 1 (by rfl) ⟨3237443, by rfl⟩ : syracuseStep 4316591 = 6474887) B6474887
theorem B3235463 : Blo 754331 3235463 := bstep (se 1 (by rfl) ⟨2426597, by rfl⟩ : syracuseStep 3235463 = 4853195) B4853195
theorem B3825305 : Blo 754331 3825305 := bstep (se 2 (by rfl) ⟨1434489, by rfl⟩ : syracuseStep 3825305 = 2868979) B2868979
theorem B11034305 : Blo 754331 11034305 := bstep (se 2 (by rfl) ⟨4137864, by rfl⟩ : syracuseStep 11034305 = 8275729) B8275729
theorem B8740585 : Blo 754331 8740585 := bstep (se 2 (by rfl) ⟨3277719, by rfl⟩ : syracuseStep 8740585 = 6555439) B6555439
theorem B778907 : Blo 754331 778907 := bstep (se 1 (by rfl) ⟨584180, by rfl⟩ : syracuseStep 778907 = 1168361) B1168361
theorem B1434505 : Blo 754331 1434505 := bstep (se 2 (by rfl) ⟨537939, by rfl⟩ : syracuseStep 1434505 = 1075879) B1075879
theorem B1434665 : Blo 754331 1434665 := bstep (se 2 (by rfl) ⟨537999, by rfl⟩ : syracuseStep 1434665 = 1075999) B1075999
theorem B2876543 : Blo 754331 2876543 := bstep (se 1 (by rfl) ⟨2157407, by rfl⟩ : syracuseStep 2876543 = 4314815) B4314815
theorem B2155859 : Blo 754331 2155859 := bstep (se 1 (by rfl) ⟨1616894, by rfl⟩ : syracuseStep 2155859 = 3233789) B3233789
theorem B2876755 : Blo 754331 2876755 := bstep (se 1 (by rfl) ⟨2157566, by rfl⟩ : syracuseStep 2876755 = 4315133) B4315133
theorem B7759351 : Blo 754331 7759351 := bstep (se 1 (by rfl) ⟨5819513, by rfl⟩ : syracuseStep 7759351 = 11639027) B11639027
theorem B1697417 : Blo 754331 1697417 := bstep (se 2 (by rfl) ⟨636531, by rfl⟩ : syracuseStep 1697417 = 1273063) B1273063
theorem B29091473 : Blo 754331 29091473 := bstep (se 2 (by rfl) ⟨10909302, by rfl⟩ : syracuseStep 29091473 = 21818605) B21818605
theorem B1697471 : Blo 754331 1697471 := bstep (se 1 (by rfl) ⟨1273103, by rfl⟩ : syracuseStep 1697471 = 2546207) B2546207
theorem B3827411 : Blo 754331 3827411 := bstep (se 1 (by rfl) ⟨2870558, by rfl⟩ : syracuseStep 3827411 = 5741117) B5741117
theorem B2549663 : Blo 754331 2549663 := bstep (se 1 (by rfl) ⟨1912247, by rfl⟩ : syracuseStep 2549663 = 3824495) B3824495
theorem B1697705 : Blo 754331 1697705 := bstep (se 2 (by rfl) ⟨636639, by rfl⟩ : syracuseStep 1697705 = 1273279) B1273279
theorem B1698011 : Blo 754331 1698011 := bstep (se 1 (by rfl) ⟨1273508, by rfl⟩ : syracuseStep 1698011 = 2547017) B2547017
theorem B2156827 : Blo 754331 2156827 := bstep (se 1 (by rfl) ⟨1617620, by rfl⟩ : syracuseStep 2156827 = 3235241) B3235241
theorem B1698281 : Blo 754331 1698281 := bstep (se 2 (by rfl) ⟨636855, by rfl⟩ : syracuseStep 1698281 = 1273711) B1273711
theorem B3238537 : Blo 754331 3238537 := bstep (se 2 (by rfl) ⟨1214451, by rfl⟩ : syracuseStep 3238537 = 2428903) B2428903
theorem B14510987 : Blo 754331 14510987 := bstep (se 1 (by rfl) ⟨10883240, by rfl⟩ : syracuseStep 14510987 = 21766481) B21766481
theorem B9694241 : Blo 754331 9694241 := bstep (se 2 (by rfl) ⟨3635340, by rfl⟩ : syracuseStep 9694241 = 7270681) B7270681
theorem B2550959 : Blo 754331 2550959 := bstep (se 1 (by rfl) ⟨1913219, by rfl⟩ : syracuseStep 2550959 = 3826439) B3826439
theorem B16576001 : Blo 754331 16576001 := bstep (se 2 (by rfl) ⟨6216000, by rfl⟩ : syracuseStep 16576001 = 12432001) B12432001
theorem B1699487 : Blo 754331 1699487 := bstep (se 1 (by rfl) ⟨1274615, by rfl⟩ : syracuseStep 1699487 = 2549231) B2549231
theorem B2879171 : Blo 754331 2879171 := bstep (se 1 (by rfl) ⟨2159378, by rfl⟩ : syracuseStep 2879171 = 4318757) B4318757
theorem B6221933 : Blo 754331 6221933 := bstep (se 3 (by rfl) ⟨1166612, by rfl⟩ : syracuseStep 6221933 = 2333225) B2333225
theorem B1700063 : Blo 754331 1700063 := bstep (se 1 (by rfl) ⟨1275047, by rfl⟩ : syracuseStep 1700063 = 2550095) B2550095
theorem B3830327 : Blo 754331 3830327 := bstep (se 1 (by rfl) ⟨2872745, by rfl⟩ : syracuseStep 3830327 = 5745491) B5745491
theorem B849127 : Blo 754331 849127 := bstep (se 1 (by rfl) ⟨636845, by rfl⟩ : syracuseStep 849127 = 1273691) B1273691
theorem B1701359 : Blo 754331 1701359 := bstep (se 1 (by rfl) ⟨1276019, by rfl⟩ : syracuseStep 1701359 = 2552039) B2552039
theorem B1701431 : Blo 754331 1701431 := bstep (se 1 (by rfl) ⟨1276073, by rfl⟩ : syracuseStep 1701431 = 2552147) B2552147
theorem B1275547 : Blo 754331 1275547 := bstep (se 1 (by rfl) ⟨956660, by rfl⟩ : syracuseStep 1275547 = 1913321) B1913321
theorem B3831623 : Blo 754331 3831623 := bstep (se 1 (by rfl) ⟨2873717, by rfl⟩ : syracuseStep 3831623 = 5747435) B5747435
theorem B849775 : Blo 754331 849775 := bstep (se 1 (by rfl) ⟨637331, by rfl⟩ : syracuseStep 849775 = 1274663) B1274663
theorem B1702025 : Blo 754331 1702025 := bstep (se 2 (by rfl) ⟨638259, by rfl⟩ : syracuseStep 1702025 = 1276519) B1276519
theorem B850639 : Blo 754331 850639 := bstep (se 1 (by rfl) ⟨637979, by rfl⟩ : syracuseStep 850639 = 1275959) B1275959
theorem B1702907 : Blo 754331 1702907 := bstep (se 1 (by rfl) ⟨1277180, by rfl⟩ : syracuseStep 1702907 = 2554361) B2554361
theorem B4848785 : Blo 754331 4848785 := bstep (se 2 (by rfl) ⟨1818294, by rfl⟩ : syracuseStep 4848785 = 3636589) B3636589
theorem B1277167 : Blo 754331 1277167 := bstep (se 1 (by rfl) ⟨957875, by rfl⟩ : syracuseStep 1277167 = 1915751) B1915751
theorem B851611 : Blo 754331 851611 := bstep (se 1 (by rfl) ⟨638708, by rfl⟩ : syracuseStep 851611 = 1277417) B1277417
theorem B1277599 : Blo 754331 1277599 := bstep (se 1 (by rfl) ⟨958199, by rfl⟩ : syracuseStep 1277599 = 1916399) B1916399
theorem B1703663 : Blo 754331 1703663 := bstep (se 1 (by rfl) ⟨1277747, by rfl⟩ : syracuseStep 1703663 = 2555495) B2555495
theorem B15695633 : Blo 754331 15695633 := bstep (se 2 (by rfl) ⟨5885862, by rfl⟩ : syracuseStep 15695633 = 11771725) B11771725
theorem B2424905 : Blo 754331 2424905 := bstep (se 2 (by rfl) ⟨909339, by rfl⟩ : syracuseStep 2424905 = 1818679) B1818679
theorem B4719077 : Blo 754331 4719077 := bstep (se 4 (by rfl) ⟨442413, by rfl⟩ : syracuseStep 4719077 = 884827) B884827
theorem B754591 : Blo 754331 754591 := bstep (se 1 (by rfl) ⟨565943, by rfl⟩ : syracuseStep 754591 = 1131887) B1131887
theorem B1705121 : Blo 754331 1705121 := bstep (se 2 (by rfl) ⟨639420, by rfl⟩ : syracuseStep 1705121 = 1278841) B1278841
theorem B755071 : Blo 754331 755071 := bstep (se 1 (by rfl) ⟨566303, by rfl⟩ : syracuseStep 755071 = 1132607) B1132607
theorem B12912047 : Blo 754331 12912047 := bstep (se 1 (by rfl) ⟨9684035, by rfl⟩ : syracuseStep 12912047 = 19368071) B19368071
theorem B755183 : Blo 754331 755183 := bstep (se 1 (by rfl) ⟨566387, by rfl⟩ : syracuseStep 755183 = 1132775) B1132775
theorem B3835673 : Blo 754331 3835673 := bstep (se 2 (by rfl) ⟨1438377, by rfl⟩ : syracuseStep 3835673 = 2876755) B2876755
theorem B2558141 : Blo 754331 2558141 := bstep (se 3 (by rfl) ⟨479651, by rfl⟩ : syracuseStep 2558141 = 959303) B959303
theorem B756071 : Blo 754331 756071 := bstep (se 1 (by rfl) ⟨567053, by rfl⟩ : syracuseStep 756071 = 1134107) B1134107
theorem B2427673 : Blo 754331 2427673 := bstep (se 2 (by rfl) ⟨910377, by rfl⟩ : syracuseStep 2427673 = 1820755) B1820755
theorem B2559167 : Blo 754331 2559167 := bstep (se 1 (by rfl) ⟨1919375, by rfl⟩ : syracuseStep 2559167 = 3838751) B3838751
theorem B756991 : Blo 754331 756991 := bstep (se 1 (by rfl) ⟨567743, by rfl⟩ : syracuseStep 756991 = 1135487) B1135487
theorem B3870911 : Blo 754331 3870911 := bstep (se 1 (by rfl) ⟨2903183, by rfl⟩ : syracuseStep 3870911 = 5806367) B5806367
theorem B4428425 : Blo 754331 4428425 := bstep (se 2 (by rfl) ⟨1660659, by rfl⟩ : syracuseStep 4428425 = 3321319) B3321319
theorem B4298345 : Blo 754331 4298345 := bstep (se 2 (by rfl) ⟨1611879, by rfl⟩ : syracuseStep 4298345 = 3223759) B3223759
theorem B9705359 : Blo 754331 9705359 := bstep (se 1 (by rfl) ⟨7279019, by rfl⟩ : syracuseStep 9705359 = 14558039) B14558039
theorem B956443 : Blo 754331 956443 := bstep (se 1 (by rfl) ⟨717332, by rfl⟩ : syracuseStep 956443 = 1434665) B1434665
theorem B9673991 : Blo 754331 9673991 := bstep (se 1 (by rfl) ⟨7255493, by rfl⟩ : syracuseStep 9673991 = 14510987) B14510987
theorem B6462827 : Blo 754331 6462827 := bstep (se 1 (by rfl) ⟨4847120, by rfl⟩ : syracuseStep 6462827 = 9694241) B9694241
theorem B11050667 : Blo 754331 11050667 := bstep (se 1 (by rfl) ⟨8288000, by rfl⟩ : syracuseStep 11050667 = 16576001) B16576001
theorem B19407437 : Blo 754331 19407437 := bstep (se 3 (by rfl) ⟨3638894, by rfl⟩ : syracuseStep 19407437 = 7277789) B7277789
theorem B10463755 : Blo 754331 10463755 := bstep (se 1 (by rfl) ⟨7847816, by rfl⟩ : syracuseStep 10463755 = 15695633) B15695633
theorem B24488729 : Blo 754331 24488729 := bstep (se 2 (by rfl) ⟨9183273, by rfl⟩ : syracuseStep 24488729 = 18366547) B18366547
theorem B79834247 : Blo 754331 79834247 := bstep (se 1 (by rfl) ⟨59875685, by rfl⟩ : syracuseStep 79834247 = 119751371) B119751371
theorem B14560499 : Blo 754331 14560499 := bstep (se 1 (by rfl) ⟨10920374, by rfl⟩ : syracuseStep 14560499 = 21840749) B21840749
theorem B6466823 : Blo 754331 6466823 := bstep (se 1 (by rfl) ⟨4850117, by rfl⟩ : syracuseStep 6466823 = 9700235) B9700235
theorem B5745977 : Blo 754331 5745977 := bstep (se 2 (by rfl) ⟨2154741, by rfl⟩ : syracuseStep 5745977 = 4309483) B4309483
theorem B2731421 : Blo 754331 2731421 := bstep (se 3 (by rfl) ⟨512141, by rfl⟩ : syracuseStep 2731421 = 1024283) B1024283
theorem B9809515 : Blo 754331 9809515 := bstep (se 1 (by rfl) ⟨7357136, by rfl⟩ : syracuseStep 9809515 = 14714273) B14714273
theorem B1912673 : Blo 754331 1912673 := bstep (se 2 (by rfl) ⟨717252, by rfl⟩ : syracuseStep 1912673 = 1434505) B1434505
theorem B10367099 : Blo 754331 10367099 := bstep (se 1 (by rfl) ⟨7775324, by rfl⟩ : syracuseStep 10367099 = 15550649) B15550649
theorem B2077085 : Blo 754331 2077085 := bstep (se 3 (by rfl) ⟨389453, by rfl⟩ : syracuseStep 2077085 = 778907) B778907
theorem B2865577 : Blo 754331 2865577 := bstep (se 2 (by rfl) ⟨1074591, by rfl⟩ : syracuseStep 2865577 = 2149183) B2149183
theorem B1817257 : Blo 754331 1817257 := bstep (se 2 (by rfl) ⟨681471, by rfl⟩ : syracuseStep 1817257 = 1362943) B1362943
theorem B2866049 : Blo 754331 2866049 := bstep (se 2 (by rfl) ⟨1074768, by rfl⟩ : syracuseStep 2866049 = 2149537) B2149537
theorem B7356203 : Blo 754331 7356203 := bstep (se 1 (by rfl) ⟨5517152, by rfl⟩ : syracuseStep 7356203 = 11034305) B11034305
theorem B1359679 : Blo 754331 1359679 := bstep (se 1 (by rfl) ⟨1019759, by rfl⟩ : syracuseStep 1359679 = 2039519) B2039519
theorem B24494035 : Blo 754331 24494035 := bstep (se 1 (by rfl) ⟨18370526, by rfl⟩ : syracuseStep 24494035 = 36741053) B36741053
theorem B4308983 : Blo 754331 4308983 := bstep (se 1 (by rfl) ⟨3231737, by rfl⟩ : syracuseStep 4308983 = 6463475) B6463475
theorem B7258571 : Blo 754331 7258571 := bstep (se 1 (by rfl) ⟨5443928, by rfl⟩ : syracuseStep 7258571 = 10887857) B10887857
theorem B17515045 : Blo 754331 17515045 := bstep (se 4 (by rfl) ⟨1642035, by rfl⟩ : syracuseStep 17515045 = 3284071) B3284071
theorem B1917695 : Blo 754331 1917695 := bstep (se 1 (by rfl) ⟨1438271, by rfl⟩ : syracuseStep 1917695 = 2876543) B2876543
theorem B1131611 : Blo 754331 1131611 := bstep (se 1 (by rfl) ⟨848708, by rfl⟩ : syracuseStep 1131611 = 1697417) B1697417
theorem B1131647 : Blo 754331 1131647 := bstep (se 1 (by rfl) ⟨848735, by rfl⟩ : syracuseStep 1131647 = 1697471) B1697471
theorem B1131803 : Blo 754331 1131803 := bstep (se 1 (by rfl) ⟨848852, by rfl⟩ : syracuseStep 1131803 = 1697705) B1697705
theorem B1132007 : Blo 754331 1132007 := bstep (se 1 (by rfl) ⟨849005, by rfl⟩ : syracuseStep 1132007 = 1698011) B1698011
theorem B1132169 : Blo 754331 1132169 := bstep (se 2 (by rfl) ⟨424563, by rfl⟩ : syracuseStep 1132169 = 849127) B849127
theorem B1132187 : Blo 754331 1132187 := bstep (se 1 (by rfl) ⟨849140, by rfl⟩ : syracuseStep 1132187 = 1698281) B1698281
theorem B7358161 : Blo 754331 7358161 := bstep (se 2 (by rfl) ⟨2759310, by rfl⟩ : syracuseStep 7358161 = 5518621) B5518621
theorem B1132991 : Blo 754331 1132991 := bstep (se 1 (by rfl) ⟨849743, by rfl⟩ : syracuseStep 1132991 = 1699487) B1699487
theorem B1919447 : Blo 754331 1919447 := bstep (se 1 (by rfl) ⟨1439585, by rfl⟩ : syracuseStep 1919447 = 2879171) B2879171
theorem B1133033 : Blo 754331 1133033 := bstep (se 2 (by rfl) ⟨424887, by rfl⟩ : syracuseStep 1133033 = 849775) B849775
theorem B2869951 : Blo 754331 2869951 := bstep (se 1 (by rfl) ⟨2152463, by rfl⟩ : syracuseStep 2869951 = 4304927) B4304927
theorem B4147955 : Blo 754331 4147955 := bstep (se 1 (by rfl) ⟨3110966, by rfl⟩ : syracuseStep 4147955 = 6221933) B6221933
theorem B1133375 : Blo 754331 1133375 := bstep (se 1 (by rfl) ⟨850031, by rfl⟩ : syracuseStep 1133375 = 1700063) B1700063
theorem B1362971 : Blo 754331 1362971 := bstep (se 1 (by rfl) ⟨1022228, by rfl⟩ : syracuseStep 1362971 = 2044457) B2044457
theorem B1134185 : Blo 754331 1134185 := bstep (se 2 (by rfl) ⟨425319, by rfl⟩ : syracuseStep 1134185 = 850639) B850639
theorem B1134239 : Blo 754331 1134239 := bstep (se 1 (by rfl) ⟨850679, by rfl⟩ : syracuseStep 1134239 = 1701359) B1701359
theorem B1134287 : Blo 754331 1134287 := bstep (se 1 (by rfl) ⟨850715, by rfl⟩ : syracuseStep 1134287 = 1701431) B1701431
theorem B4837097 : Blo 754331 4837097 := bstep (se 2 (by rfl) ⟨1813911, by rfl⟩ : syracuseStep 4837097 = 3627823) B3627823
theorem B1134683 : Blo 754331 1134683 := bstep (se 1 (by rfl) ⟨851012, by rfl⟩ : syracuseStep 1134683 = 1702025) B1702025
theorem B1135271 : Blo 754331 1135271 := bstep (se 1 (by rfl) ⟨851453, by rfl⟩ : syracuseStep 1135271 = 1702907) B1702907
theorem B3232523 : Blo 754331 3232523 := bstep (se 1 (by rfl) ⟨2424392, by rfl⟩ : syracuseStep 3232523 = 4848785) B4848785
theorem B1135481 : Blo 754331 1135481 := bstep (se 2 (by rfl) ⟨425805, by rfl⟩ : syracuseStep 1135481 = 851611) B851611
theorem B11654113 : Blo 754331 11654113 := bstep (se 2 (by rfl) ⟨4370292, by rfl⟩ : syracuseStep 11654113 = 8740585) B8740585
theorem B1135775 : Blo 754331 1135775 := bstep (se 1 (by rfl) ⟨851831, by rfl⟩ : syracuseStep 1135775 = 1703663) B1703663
theorem B19420559 : Blo 754331 19420559 := bstep (se 1 (by rfl) ⟨14565419, by rfl⟩ : syracuseStep 19420559 = 29130839) B29130839
theorem B1398811 : Blo 754331 1398811 := bstep (se 1 (by rfl) ⟨1049108, by rfl⟩ : syracuseStep 1398811 = 2098217) B2098217
theorem B1136975 : Blo 754331 1136975 := bstep (se 1 (by rfl) ⟨852731, by rfl⟩ : syracuseStep 1136975 = 1705463) B1705463
theorem B1137017 : Blo 754331 1137017 := bstep (se 2 (by rfl) ⟨426381, by rfl⟩ : syracuseStep 1137017 = 852763) B852763
theorem B3824009 : Blo 754331 3824009 := bstep (se 2 (by rfl) ⟨1434003, by rfl⟩ : syracuseStep 3824009 = 2868007) B2868007
theorem B1137359 : Blo 754331 1137359 := bstep (se 1 (by rfl) ⟨853019, by rfl⟩ : syracuseStep 1137359 = 1706039) B1706039
theorem B10345801 : Blo 754331 10345801 := bstep (se 2 (by rfl) ⟨3879675, by rfl⟩ : syracuseStep 10345801 = 7759351) B7759351
theorem B3891007 : Blo 754331 3891007 := bstep (se 1 (by rfl) ⟨2918255, by rfl⟩ : syracuseStep 3891007 = 5836511) B5836511
theorem B2875769 : Blo 754331 2875769 := bstep (se 2 (by rfl) ⟨1078413, by rfl⟩ : syracuseStep 2875769 = 2156827) B2156827
theorem B7758443 : Blo 754331 7758443 := bstep (se 1 (by rfl) ⟨5818832, by rfl⟩ : syracuseStep 7758443 = 11637665) B11637665
theorem B4318049 : Blo 754331 4318049 := bstep (se 2 (by rfl) ⟨1619268, by rfl⟩ : syracuseStep 4318049 = 3238537) B3238537
theorem B1434847 : Blo 754331 1434847 := bstep (se 1 (by rfl) ⟨1076135, by rfl⟩ : syracuseStep 1434847 = 2152271) B2152271
theorem B2549501 : Blo 754331 2549501 := bstep (se 3 (by rfl) ⟨478031, by rfl⟩ : syracuseStep 2549501 = 956063) B956063
theorem B1697975 : Blo 754331 1697975 := bstep (se 1 (by rfl) ⟨1273481, by rfl⟩ : syracuseStep 1697975 = 2546963) B2546963
theorem B1698047 : Blo 754331 1698047 := bstep (se 1 (by rfl) ⟨1273535, by rfl⟩ : syracuseStep 1698047 = 2547071) B2547071
theorem B2877727 : Blo 754331 2877727 := bstep (se 1 (by rfl) ⟨2158295, by rfl⟩ : syracuseStep 2877727 = 4316591) B4316591
theorem B2156975 : Blo 754331 2156975 := bstep (se 1 (by rfl) ⟨1617731, by rfl⟩ : syracuseStep 2156975 = 3235463) B3235463
theorem B2550203 : Blo 754331 2550203 := bstep (se 1 (by rfl) ⟨1912652, by rfl⟩ : syracuseStep 2550203 = 3825305) B3825305
theorem B3631823 : Blo 754331 3631823 := bstep (se 1 (by rfl) ⟨2723867, by rfl⟩ : syracuseStep 3631823 = 5447735) B5447735
theorem B3238879 : Blo 754331 3238879 := bstep (se 1 (by rfl) ⟨2429159, by rfl⟩ : syracuseStep 3238879 = 4858319) B4858319
theorem B1437239 : Blo 754331 1437239 := bstep (se 1 (by rfl) ⟨1077929, by rfl⟩ : syracuseStep 1437239 = 2155859) B2155859
theorem B3829355 : Blo 754331 3829355 := bstep (se 1 (by rfl) ⟨2872016, by rfl⟩ : syracuseStep 3829355 = 5744033) B5744033
theorem B19394315 : Blo 754331 19394315 := bstep (se 1 (by rfl) ⟨14545736, by rfl⟩ : syracuseStep 19394315 = 29091473) B29091473
theorem B2551607 : Blo 754331 2551607 := bstep (se 1 (by rfl) ⟨1913705, by rfl⟩ : syracuseStep 2551607 = 3827411) B3827411
theorem B1699775 : Blo 754331 1699775 := bstep (se 1 (by rfl) ⟨1274831, by rfl⟩ : syracuseStep 1699775 = 2549663) B2549663
theorem B15560747 : Blo 754331 15560747 := bstep (se 1 (by rfl) ⟨11670560, by rfl⟩ : syracuseStep 15560747 = 23341121) B23341121
theorem B1273927 : Blo 754331 1273927 := bstep (se 1 (by rfl) ⟨955445, by rfl⟩ : syracuseStep 1273927 = 1910891) B1910891
theorem B2913049 : Blo 754331 2913049 := bstep (se 2 (by rfl) ⟨1092393, by rfl⟩ : syracuseStep 2913049 = 2184787) B2184787
theorem B1700639 : Blo 754331 1700639 := bstep (se 1 (by rfl) ⟨1275479, by rfl⟩ : syracuseStep 1700639 = 2550959) B2550959
theorem B1700729 : Blo 754331 1700729 := bstep (se 2 (by rfl) ⟨637773, by rfl⟩ : syracuseStep 1700729 = 1275547) B1275547
theorem B1275007 : Blo 754331 1275007 := bstep (se 1 (by rfl) ⟨956255, by rfl⟩ : syracuseStep 1275007 = 1912511) B1912511
theorem B1209833 : Blo 754331 1209833 := bstep (se 2 (by rfl) ⟨453687, by rfl⟩ : syracuseStep 1209833 = 907375) B907375
theorem B1275439 : Blo 754331 1275439 := bstep (se 1 (by rfl) ⟨956579, by rfl⟩ : syracuseStep 1275439 = 1913159) B1913159
theorem B2553551 : Blo 754331 2553551 := bstep (se 1 (by rfl) ⟨1915163, by rfl⟩ : syracuseStep 2553551 = 3830327) B3830327
theorem B3635513 : Blo 754331 3635513 := bstep (se 2 (by rfl) ⟨1363317, by rfl⟩ : syracuseStep 3635513 = 2726635) B2726635
theorem B1276391 : Blo 754331 1276391 := bstep (se 1 (by rfl) ⟨957293, by rfl⟩ : syracuseStep 1276391 = 1914587) B1914587
theorem B2554415 : Blo 754331 2554415 := bstep (se 1 (by rfl) ⟨1915811, by rfl⟩ : syracuseStep 2554415 = 3831623) B3831623
theorem B5438249 : Blo 754331 5438249 := bstep (se 2 (by rfl) ⟨2039343, by rfl⟩ : syracuseStep 5438249 = 4078687) B4078687
theorem B1702889 : Blo 754331 1702889 := bstep (se 2 (by rfl) ⟨638583, by rfl⟩ : syracuseStep 1702889 = 1277167) B1277167
theorem B3636359 : Blo 754331 3636359 := bstep (se 1 (by rfl) ⟨2727269, by rfl⟩ : syracuseStep 3636359 = 5454539) B5454539
theorem B1703465 : Blo 754331 1703465 := bstep (se 2 (by rfl) ⟨638799, by rfl⟩ : syracuseStep 1703465 = 1277599) B1277599
theorem B8159143 : Blo 754331 8159143 := bstep (se 1 (by rfl) ⟨6119357, by rfl⟩ : syracuseStep 8159143 = 12238715) B12238715
theorem B3637187 : Blo 754331 3637187 := bstep (se 1 (by rfl) ⟨2727890, by rfl⟩ : syracuseStep 3637187 = 5455781) B5455781
theorem B2555873 : Blo 754331 2555873 := bstep (se 2 (by rfl) ⟨958452, by rfl⟩ : syracuseStep 2555873 = 1916905) B1916905
theorem B3146051 : Blo 754331 3146051 := bstep (se 1 (by rfl) ⟨2359538, by rfl⟩ : syracuseStep 3146051 = 4719077) B4719077
theorem B1278463 : Blo 754331 1278463 := bstep (se 1 (by rfl) ⟨958847, by rfl⟩ : syracuseStep 1278463 = 1917695) B1917695
theorem B754407 : Blo 754331 754407 := bstep (se 1 (by rfl) ⟨565805, by rfl⟩ : syracuseStep 754407 = 1131611) B1131611
theorem B754431 : Blo 754331 754431 := bstep (se 1 (by rfl) ⟨565823, by rfl⟩ : syracuseStep 754431 = 1131647) B1131647
theorem B754535 : Blo 754331 754535 := bstep (se 1 (by rfl) ⟨565901, by rfl⟩ : syracuseStep 754535 = 1131803) B1131803
theorem B754671 : Blo 754331 754671 := bstep (se 1 (by rfl) ⟨566003, by rfl⟩ : syracuseStep 754671 = 1132007) B1132007
theorem B5538893 : Blo 754331 5538893 := bstep (se 3 (by rfl) ⟨1038542, by rfl⟩ : syracuseStep 5538893 = 2077085) B2077085
theorem B754779 : Blo 754331 754779 := bstep (se 1 (by rfl) ⟨566084, by rfl⟩ : syracuseStep 754779 = 1132169) B1132169
theorem B754791 : Blo 754331 754791 := bstep (se 1 (by rfl) ⟨566093, by rfl⟩ : syracuseStep 754791 = 1132187) B1132187
theorem B2557115 : Blo 754331 2557115 := bstep (se 1 (by rfl) ⟨1917836, by rfl⟩ : syracuseStep 2557115 = 3835673) B3835673
theorem B1705427 : Blo 754331 1705427 := bstep (se 1 (by rfl) ⟨1279070, by rfl⟩ : syracuseStep 1705427 = 2558141) B2558141
theorem B755327 : Blo 754331 755327 := bstep (se 1 (by rfl) ⟨566495, by rfl⟩ : syracuseStep 755327 = 1132991) B1132991
theorem B1279631 : Blo 754331 1279631 := bstep (se 1 (by rfl) ⟨959723, by rfl⟩ : syracuseStep 1279631 = 1919447) B1919447
theorem B755355 : Blo 754331 755355 := bstep (se 1 (by rfl) ⟨566516, by rfl⟩ : syracuseStep 755355 = 1133033) B1133033
theorem B755583 : Blo 754331 755583 := bstep (se 1 (by rfl) ⟨566687, by rfl⟩ : syracuseStep 755583 = 1133375) B1133375
theorem B1706111 : Blo 754331 1706111 := bstep (se 1 (by rfl) ⟨1279583, by rfl⟩ : syracuseStep 1706111 = 2559167) B2559167
theorem B756123 : Blo 754331 756123 := bstep (se 1 (by rfl) ⟨567092, by rfl⟩ : syracuseStep 756123 = 1134185) B1134185
theorem B756159 : Blo 754331 756159 := bstep (se 1 (by rfl) ⟨567119, by rfl⟩ : syracuseStep 756159 = 1134239) B1134239
theorem B756191 : Blo 754331 756191 := bstep (se 1 (by rfl) ⟨567143, by rfl⟩ : syracuseStep 756191 = 1134287) B1134287
theorem B756455 : Blo 754331 756455 := bstep (se 1 (by rfl) ⟨567341, by rfl⟩ : syracuseStep 756455 = 1134683) B1134683
theorem B3836969 : Blo 754331 3836969 := bstep (se 2 (by rfl) ⟨1438863, by rfl⟩ : syracuseStep 3836969 = 2877727) B2877727
theorem B2952283 : Blo 754331 2952283 := bstep (se 1 (by rfl) ⟨2214212, by rfl⟩ : syracuseStep 2952283 = 4428425) B4428425
theorem B756847 : Blo 754331 756847 := bstep (se 1 (by rfl) ⟨567635, by rfl⟩ : syracuseStep 756847 = 1135271) B1135271
theorem B756987 : Blo 754331 756987 := bstep (se 1 (by rfl) ⟨567740, by rfl⟩ : syracuseStep 756987 = 1135481) B1135481
theorem B757183 : Blo 754331 757183 := bstep (se 1 (by rfl) ⟨567887, by rfl⟩ : syracuseStep 757183 = 1135775) B1135775
theorem B12947039 : Blo 754331 12947039 := bstep (se 1 (by rfl) ⟨9710279, by rfl⟩ : syracuseStep 12947039 = 19420559) B19420559
theorem B15536261 : Blo 754331 15536261 := bstep (se 4 (by rfl) ⟨1456524, by rfl⟩ : syracuseStep 15536261 = 2913049) B2913049
theorem B757983 : Blo 754331 757983 := bstep (se 1 (by rfl) ⟨568487, by rfl⟩ : syracuseStep 757983 = 1136975) B1136975
theorem B758011 : Blo 754331 758011 := bstep (se 1 (by rfl) ⟨568508, by rfl⟩ : syracuseStep 758011 = 1137017) B1137017
theorem B758239 : Blo 754331 758239 := bstep (se 1 (by rfl) ⟨568679, by rfl⟩ : syracuseStep 758239 = 1137359) B1137359
theorem B15538817 : Blo 754331 15538817 := bstep (se 2 (by rfl) ⟨5827056, by rfl⟩ : syracuseStep 15538817 = 11654113) B11654113
theorem B16325819 : Blo 754331 16325819 := bstep (se 1 (by rfl) ⟨12244364, by rfl⟩ : syracuseStep 16325819 = 24488729) B24488729
theorem B53222831 : Blo 754331 53222831 := bstep (se 1 (by rfl) ⟨39917123, by rfl⟩ : syracuseStep 53222831 = 79834247) B79834247
theorem B9706999 : Blo 754331 9706999 := bstep (se 1 (by rfl) ⟨7280249, by rfl⟩ : syracuseStep 9706999 = 14560499) B14560499
theorem B958159 : Blo 754331 958159 := bstep (se 1 (by rfl) ⟨718619, by rfl⟩ : syracuseStep 958159 = 1437239) B1437239
theorem B7283789 : Blo 754331 7283789 := bstep (se 3 (by rfl) ⟨1365710, by rfl⟩ : syracuseStep 7283789 = 2731421) B2731421
theorem B1910699 : Blo 754331 1910699 := bstep (se 1 (by rfl) ⟨1433024, by rfl⟩ : syracuseStep 1910699 = 2866049) B2866049
theorem B1812905 : Blo 754331 1812905 := bstep (se 2 (by rfl) ⟨679839, by rfl⟩ : syracuseStep 1812905 = 1359679) B1359679
theorem B5188009 : Blo 754331 5188009 := bstep (se 2 (by rfl) ⟨1945503, by rfl⟩ : syracuseStep 5188009 = 3891007) B3891007
theorem B1616603 : Blo 754331 1616603 := bstep (se 1 (by rfl) ⟨1212452, by rfl⟩ : syracuseStep 1616603 = 2424905) B2424905
theorem B20689181 : Blo 754331 20689181 := bstep (se 3 (by rfl) ⟨3879221, by rfl⟩ : syracuseStep 20689181 = 7758443) B7758443
theorem B1913129 : Blo 754331 1913129 := bstep (se 2 (by rfl) ⟨717423, by rfl⟩ : syracuseStep 1913129 = 1434847) B1434847
theorem B2765303 : Blo 754331 2765303 := bstep (se 1 (by rfl) ⟨2073977, by rfl⟩ : syracuseStep 2765303 = 4147955) B4147955
theorem B9810881 : Blo 754331 9810881 := bstep (se 2 (by rfl) ⟨3679080, by rfl⟩ : syracuseStep 9810881 = 7358161) B7358161
theorem B2865563 : Blo 754331 2865563 := bstep (se 1 (by rfl) ⟨2149172, by rfl⟩ : syracuseStep 2865563 = 4298345) B4298345
theorem B6470239 : Blo 754331 6470239 := bstep (se 1 (by rfl) ⟨4852679, by rfl⟩ : syracuseStep 6470239 = 9705359) B9705359
theorem B4308551 : Blo 754331 4308551 := bstep (se 1 (by rfl) ⟨3231413, by rfl⟩ : syracuseStep 4308551 = 6462827) B6462827
theorem B1917179 : Blo 754331 1917179 := bstep (se 1 (by rfl) ⟨1437884, by rfl⟩ : syracuseStep 1917179 = 2875769) B2875769
theorem B1131983 : Blo 754331 1131983 := bstep (se 1 (by rfl) ⟨848987, by rfl⟩ : syracuseStep 1131983 = 1697975) B1697975
theorem B1132031 : Blo 754331 1132031 := bstep (se 1 (by rfl) ⟨849023, by rfl⟩ : syracuseStep 1132031 = 1698047) B1698047
theorem B4311215 : Blo 754331 4311215 := bstep (se 1 (by rfl) ⟨3233411, by rfl⟩ : syracuseStep 4311215 = 6466823) B6466823
theorem B12929543 : Blo 754331 12929543 := bstep (se 1 (by rfl) ⟨9697157, by rfl⟩ : syracuseStep 12929543 = 19394315) B19394315
theorem B1133183 : Blo 754331 1133183 := bstep (se 1 (by rfl) ⟨849887, by rfl⟩ : syracuseStep 1133183 = 1699775) B1699775
theorem B10373831 : Blo 754331 10373831 := bstep (se 1 (by rfl) ⟨7780373, by rfl⟩ : syracuseStep 10373831 = 15560747) B15560747
theorem B1133759 : Blo 754331 1133759 := bstep (se 1 (by rfl) ⟨850319, by rfl⟩ : syracuseStep 1133759 = 1700639) B1700639
theorem B3820769 : Blo 754331 3820769 := bstep (se 2 (by rfl) ⟨1432788, by rfl⟩ : syracuseStep 3820769 = 2865577) B2865577
theorem B52317413 : Blo 754331 52317413 := bstep (se 4 (by rfl) ⟨4904757, by rfl⟩ : syracuseStep 52317413 = 9809515) B9809515
theorem B1133819 : Blo 754331 1133819 := bstep (se 1 (by rfl) ⟨850364, by rfl⟩ : syracuseStep 1133819 = 1700729) B1700729
theorem B806555 : Blo 754331 806555 := bstep (se 1 (by rfl) ⟨604916, by rfl⟩ : syracuseStep 806555 = 1209833) B1209833
theorem B3625499 : Blo 754331 3625499 := bstep (se 1 (by rfl) ⟨2719124, by rfl⟩ : syracuseStep 3625499 = 5438249) B5438249
theorem B12898925 : Blo 754331 12898925 := bstep (se 3 (by rfl) ⟨2418548, by rfl⟩ : syracuseStep 12898925 = 4837097) B4837097
theorem B1135259 : Blo 754331 1135259 := bstep (se 1 (by rfl) ⟨851444, by rfl⟩ : syracuseStep 1135259 = 1702889) B1702889
theorem B1135643 : Blo 754331 1135643 := bstep (se 1 (by rfl) ⟨851732, by rfl⟩ : syracuseStep 1135643 = 1703465) B1703465
theorem B4904135 : Blo 754331 4904135 := bstep (se 1 (by rfl) ⟨3678101, by rfl⟩ : syracuseStep 4904135 = 7356203) B7356203
theorem B32658713 : Blo 754331 32658713 := bstep (se 2 (by rfl) ⟨12247017, by rfl⟩ : syracuseStep 32658713 = 24494035) B24494035
theorem B2872655 : Blo 754331 2872655 := bstep (se 1 (by rfl) ⟨2154491, by rfl⟩ : syracuseStep 2872655 = 4308983) B4308983
theorem B4839047 : Blo 754331 4839047 := bstep (se 1 (by rfl) ⟨3629285, by rfl⟩ : syracuseStep 4839047 = 7258571) B7258571
theorem B1136747 : Blo 754331 1136747 := bstep (se 1 (by rfl) ⟨852560, by rfl⟩ : syracuseStep 1136747 = 1705121) B1705121
theorem B8608031 : Blo 754331 8608031 := bstep (se 1 (by rfl) ⟨6456023, by rfl⟩ : syracuseStep 8608031 = 12912047) B12912047
theorem B2580607 : Blo 754331 2580607 := bstep (se 1 (by rfl) ⟨1935455, by rfl⟩ : syracuseStep 2580607 = 3870911) B3870911
theorem B93413573 : Blo 754331 93413573 := bstep (se 4 (by rfl) ⟨8757522, by rfl⟩ : syracuseStep 93413573 = 17515045) B17515045
theorem B2155015 : Blo 754331 2155015 := bstep (se 1 (by rfl) ⟨1616261, by rfl⟩ : syracuseStep 2155015 = 3232523) B3232523
theorem B13951673 : Blo 754331 13951673 := bstep (se 2 (by rfl) ⟨5231877, by rfl⟩ : syracuseStep 13951673 = 10463755) B10463755
theorem B3826601 : Blo 754331 3826601 := bstep (se 2 (by rfl) ⟨1434975, by rfl⟩ : syracuseStep 3826601 = 2869951) B2869951
theorem B3236897 : Blo 754331 3236897 := bstep (se 2 (by rfl) ⟨1213836, by rfl⟩ : syracuseStep 3236897 = 2427673) B2427673
theorem B4318505 : Blo 754331 4318505 := bstep (se 2 (by rfl) ⟨1619439, by rfl⟩ : syracuseStep 4318505 = 3238879) B3238879
theorem B2549339 : Blo 754331 2549339 := bstep (se 1 (by rfl) ⟨1912004, by rfl⟩ : syracuseStep 2549339 = 3824009) B3824009
theorem B6449327 : Blo 754331 6449327 := bstep (se 1 (by rfl) ⟨4836995, by rfl⟩ : syracuseStep 6449327 = 9673991) B9673991
theorem B7367111 : Blo 754331 7367111 := bstep (se 1 (by rfl) ⟨5525333, by rfl⟩ : syracuseStep 7367111 = 11050667) B11050667
theorem B1698569 : Blo 754331 1698569 := bstep (se 2 (by rfl) ⟨636963, by rfl⟩ : syracuseStep 1698569 = 1273927) B1273927
theorem B12938291 : Blo 754331 12938291 := bstep (se 1 (by rfl) ⟨9703718, by rfl⟩ : syracuseStep 12938291 = 19407437) B19407437
theorem B2878699 : Blo 754331 2878699 := bstep (se 1 (by rfl) ⟨2159024, by rfl⟩ : syracuseStep 2878699 = 4318049) B4318049
theorem B1699667 : Blo 754331 1699667 := bstep (se 1 (by rfl) ⟨1274750, by rfl⟩ : syracuseStep 1699667 = 2549501) B2549501
theorem B1700009 : Blo 754331 1700009 := bstep (se 2 (by rfl) ⟨637503, by rfl⟩ : syracuseStep 1700009 = 1275007) B1275007
theorem B1437983 : Blo 754331 1437983 := bstep (se 1 (by rfl) ⟨1078487, by rfl⟩ : syracuseStep 1437983 = 2156975) B2156975
theorem B1700135 : Blo 754331 1700135 := bstep (se 1 (by rfl) ⟨1275101, by rfl⟩ : syracuseStep 1700135 = 2550203) B2550203
theorem B2421215 : Blo 754331 2421215 := bstep (se 1 (by rfl) ⟨1815911, by rfl⟩ : syracuseStep 2421215 = 3631823) B3631823
theorem B1700585 : Blo 754331 1700585 := bstep (se 2 (by rfl) ⟨637719, by rfl⟩ : syracuseStep 1700585 = 1275439) B1275439
theorem B3830651 : Blo 754331 3830651 := bstep (se 1 (by rfl) ⟨2872988, by rfl⟩ : syracuseStep 3830651 = 5745977) B5745977
theorem B2552903 : Blo 754331 2552903 := bstep (se 1 (by rfl) ⟨1914677, by rfl⟩ : syracuseStep 2552903 = 3829355) B3829355
theorem B1701071 : Blo 754331 1701071 := bstep (se 1 (by rfl) ⟨1275803, by rfl⟩ : syracuseStep 1701071 = 2551607) B2551607
theorem B1275115 : Blo 754331 1275115 := bstep (se 1 (by rfl) ⟨956336, by rfl⟩ : syracuseStep 1275115 = 1912673) B1912673
theorem B1865081 : Blo 754331 1865081 := bstep (se 2 (by rfl) ⟨699405, by rfl⟩ : syracuseStep 1865081 = 1398811) B1398811
theorem B1275257 : Blo 754331 1275257 := bstep (se 2 (by rfl) ⟨478221, by rfl⟩ : syracuseStep 1275257 = 956443) B956443
theorem B3634589 : Blo 754331 3634589 := bstep (se 3 (by rfl) ⟨681485, by rfl⟩ : syracuseStep 3634589 = 1362971) B1362971
theorem B6911399 : Blo 754331 6911399 := bstep (se 1 (by rfl) ⟨5183549, by rfl⟩ : syracuseStep 6911399 = 10367099) B10367099
theorem B2423009 : Blo 754331 2423009 := bstep (se 2 (by rfl) ⟨908628, by rfl⟩ : syracuseStep 2423009 = 1817257) B1817257
theorem B1702367 : Blo 754331 1702367 := bstep (se 1 (by rfl) ⟨1276775, by rfl⟩ : syracuseStep 1702367 = 2553551) B2553551
theorem B2423675 : Blo 754331 2423675 := bstep (se 1 (by rfl) ⟨1817756, by rfl⟩ : syracuseStep 2423675 = 3635513) B3635513
theorem B850927 : Blo 754331 850927 := bstep (se 1 (by rfl) ⟨638195, by rfl⟩ : syracuseStep 850927 = 1276391) B1276391
theorem B1702943 : Blo 754331 1702943 := bstep (se 1 (by rfl) ⟨1277207, by rfl⟩ : syracuseStep 1702943 = 2554415) B2554415
theorem B13794401 : Blo 754331 13794401 := bstep (se 2 (by rfl) ⟨5172900, by rfl⟩ : syracuseStep 13794401 = 10345801) B10345801
theorem B2424239 : Blo 754331 2424239 := bstep (se 1 (by rfl) ⟨1818179, by rfl⟩ : syracuseStep 2424239 = 3636359) B3636359
theorem B10878857 : Blo 754331 10878857 := bstep (se 2 (by rfl) ⟨4079571, by rfl⟩ : syracuseStep 10878857 = 8159143) B8159143
theorem B2424791 : Blo 754331 2424791 := bstep (se 1 (by rfl) ⟨1818593, by rfl⟩ : syracuseStep 2424791 = 3637187) B3637187
theorem B1703915 : Blo 754331 1703915 := bstep (se 1 (by rfl) ⟨1277936, by rfl⟩ : syracuseStep 1703915 = 2555873) B2555873
theorem B1278119 : Blo 754331 1278119 := bstep (se 1 (by rfl) ⟨958589, by rfl⟩ : syracuseStep 1278119 = 1917179) B1917179
theorem B3440809 : Blo 754331 3440809 := bstep (se 2 (by rfl) ⟨1290303, by rfl⟩ : syracuseStep 3440809 = 2580607) B2580607
theorem B1704617 : Blo 754331 1704617 := bstep (se 2 (by rfl) ⟨639231, by rfl⟩ : syracuseStep 1704617 = 1278463) B1278463
theorem B1704743 : Blo 754331 1704743 := bstep (se 1 (by rfl) ⟨1278557, by rfl⟩ : syracuseStep 1704743 = 2557115) B2557115
theorem B59081525 : Blo 754331 59081525 := bstep (se 5 (by rfl) ⟨2769446, by rfl⟩ : syracuseStep 59081525 = 5538893) B5538893
theorem B8389469 : Blo 754331 8389469 := bstep (se 3 (by rfl) ⟨1573025, by rfl⟩ : syracuseStep 8389469 = 3146051) B3146051
theorem B754655 : Blo 754331 754655 := bstep (se 1 (by rfl) ⟨565991, by rfl⟩ : syracuseStep 754655 = 1131983) B1131983
theorem B754687 : Blo 754331 754687 := bstep (se 1 (by rfl) ⟨566015, by rfl⟩ : syracuseStep 754687 = 1132031) B1132031
theorem B853087 : Blo 754331 853087 := bstep (se 1 (by rfl) ⟨639815, by rfl⟩ : syracuseStep 853087 = 1279631) B1279631
theorem B9667997 : Blo 754331 9667997 := bstep (se 3 (by rfl) ⟨1812749, by rfl⟩ : syracuseStep 9667997 = 3625499) B3625499
theorem B8619695 : Blo 754331 8619695 := bstep (se 1 (by rfl) ⟨6464771, by rfl⟩ : syracuseStep 8619695 = 12929543) B12929543
theorem B755455 : Blo 754331 755455 := bstep (se 1 (by rfl) ⟨566591, by rfl⟩ : syracuseStep 755455 = 1133183) B1133183
theorem B6915887 : Blo 754331 6915887 := bstep (se 1 (by rfl) ⟨5186915, by rfl⟩ : syracuseStep 6915887 = 10373831) B10373831
theorem B2557979 : Blo 754331 2557979 := bstep (se 1 (by rfl) ⟨1918484, by rfl⟩ : syracuseStep 2557979 = 3836969) B3836969
theorem B755839 : Blo 754331 755839 := bstep (se 1 (by rfl) ⟨566879, by rfl⟩ : syracuseStep 755839 = 1133759) B1133759
theorem B755879 : Blo 754331 755879 := bstep (se 1 (by rfl) ⟨566909, by rfl⟩ : syracuseStep 755879 = 1133819) B1133819
theorem B10357507 : Blo 754331 10357507 := bstep (se 1 (by rfl) ⟨7768130, by rfl⟩ : syracuseStep 10357507 = 15536261) B15536261
theorem B756839 : Blo 754331 756839 := bstep (se 1 (by rfl) ⟨567629, by rfl⟩ : syracuseStep 756839 = 1135259) B1135259
theorem B6917345 : Blo 754331 6917345 := bstep (se 2 (by rfl) ⟨2594004, by rfl⟩ : syracuseStep 6917345 = 5188009) B5188009
theorem B757095 : Blo 754331 757095 := bstep (se 1 (by rfl) ⟨567821, by rfl⟩ : syracuseStep 757095 = 1135643) B1135643
theorem B757831 : Blo 754331 757831 := bstep (se 1 (by rfl) ⟨568373, by rfl⟩ : syracuseStep 757831 = 1136747) B1136747
theorem B3936377 : Blo 754331 3936377 := bstep (se 2 (by rfl) ⟨1476141, by rfl⟩ : syracuseStep 3936377 = 2952283) B2952283
theorem B5738687 : Blo 754331 5738687 := bstep (se 1 (by rfl) ⟨4304015, by rfl⟩ : syracuseStep 5738687 = 8608031) B8608031
theorem B3838265 : Blo 754331 3838265 := bstep (se 2 (by rfl) ⟨1439349, by rfl⟩ : syracuseStep 3838265 = 2878699) B2878699
theorem B10359211 : Blo 754331 10359211 := bstep (se 1 (by rfl) ⟨7769408, by rfl⟩ : syracuseStep 10359211 = 15538817) B15538817
theorem B10883879 : Blo 754331 10883879 := bstep (se 1 (by rfl) ⟨8162909, by rfl⟩ : syracuseStep 10883879 = 16325819) B16325819
theorem B4855859 : Blo 754331 4855859 := bstep (se 1 (by rfl) ⟨3641894, by rfl⟩ : syracuseStep 4855859 = 7283789) B7283789
theorem B4299551 : Blo 754331 4299551 := bstep (se 1 (by rfl) ⟨3224663, by rfl⟩ : syracuseStep 4299551 = 6449327) B6449327
theorem B8625527 : Blo 754331 8625527 := bstep (se 1 (by rfl) ⟨6469145, by rfl⟩ : syracuseStep 8625527 = 12938291) B12938291
theorem B958655 : Blo 754331 958655 := bstep (se 1 (by rfl) ⟨718991, by rfl⟩ : syracuseStep 958655 = 1437983) B1437983
theorem B1614143 : Blo 754331 1614143 := bstep (se 1 (by rfl) ⟨1210607, by rfl⟩ : syracuseStep 1614143 = 2421215) B2421215
theorem B1843535 : Blo 754331 1843535 := bstep (se 1 (by rfl) ⟨1382651, by rfl⟩ : syracuseStep 1843535 = 2765303) B2765303
theorem B8626985 : Blo 754331 8626985 := bstep (se 2 (by rfl) ⟨3235119, by rfl⟩ : syracuseStep 8626985 = 6470239) B6470239
theorem B1615339 : Blo 754331 1615339 := bstep (se 1 (by rfl) ⟨1211504, by rfl⟩ : syracuseStep 1615339 = 2423009) B2423009
theorem B1910375 : Blo 754331 1910375 := bstep (se 1 (by rfl) ⟨1432781, by rfl⟩ : syracuseStep 1910375 = 2865563) B2865563
theorem B1615783 : Blo 754331 1615783 := bstep (se 1 (by rfl) ⟨1211837, by rfl⟩ : syracuseStep 1615783 = 2423675) B2423675
theorem B1616159 : Blo 754331 1616159 := bstep (se 1 (by rfl) ⟨1212119, by rfl⟩ : syracuseStep 1616159 = 2424239) B2424239
theorem B7252571 : Blo 754331 7252571 := bstep (se 1 (by rfl) ⟨5439428, by rfl⟩ : syracuseStep 7252571 = 10878857) B10878857
theorem B1616527 : Blo 754331 1616527 := bstep (se 1 (by rfl) ⟨1212395, by rfl⟩ : syracuseStep 1616527 = 2424791) B2424791
theorem B34878275 : Blo 754331 34878275 := bstep (se 1 (by rfl) ⟨26158706, by rfl⟩ : syracuseStep 34878275 = 52317413) B52317413
theorem B8631359 : Blo 754331 8631359 := bstep (se 1 (by rfl) ⟨6473519, by rfl⟩ : syracuseStep 8631359 = 12947039) B12947039
theorem B8599283 : Blo 754331 8599283 := bstep (se 1 (by rfl) ⟨6449462, by rfl⟩ : syracuseStep 8599283 = 12898925) B12898925
theorem B21772475 : Blo 754331 21772475 := bstep (se 1 (by rfl) ⟨16329356, by rfl⟩ : syracuseStep 21772475 = 32658713) B32658713
theorem B1915103 : Blo 754331 1915103 := bstep (se 1 (by rfl) ⟨1436327, by rfl⟩ : syracuseStep 1915103 = 2872655) B2872655
theorem B3226031 : Blo 754331 3226031 := bstep (se 1 (by rfl) ⟨2419523, by rfl⟩ : syracuseStep 3226031 = 4839047) B4839047
theorem B62275715 : Blo 754331 62275715 := bstep (se 1 (by rfl) ⟨46706786, by rfl⟩ : syracuseStep 62275715 = 93413573) B93413573
theorem B1132379 : Blo 754331 1132379 := bstep (se 1 (by rfl) ⟨849284, by rfl⟩ : syracuseStep 1132379 = 1698569) B1698569
theorem B4310941 : Blo 754331 4310941 := bstep (se 3 (by rfl) ⟨808301, by rfl⟩ : syracuseStep 4310941 = 1616603) B1616603
theorem B1133111 : Blo 754331 1133111 := bstep (se 1 (by rfl) ⟨849833, by rfl⟩ : syracuseStep 1133111 = 1699667) B1699667
theorem B1133339 : Blo 754331 1133339 := bstep (se 1 (by rfl) ⟨850004, by rfl⟩ : syracuseStep 1133339 = 1700009) B1700009
theorem B1133423 : Blo 754331 1133423 := bstep (se 1 (by rfl) ⟨850067, by rfl⟩ : syracuseStep 1133423 = 1700135) B1700135
theorem B1133723 : Blo 754331 1133723 := bstep (se 1 (by rfl) ⟨850292, by rfl⟩ : syracuseStep 1133723 = 1700585) B1700585
theorem B6540587 : Blo 754331 6540587 := bstep (se 1 (by rfl) ⟨4905440, by rfl⟩ : syracuseStep 6540587 = 9810881) B9810881
theorem B1134047 : Blo 754331 1134047 := bstep (se 1 (by rfl) ⟨850535, by rfl⟩ : syracuseStep 1134047 = 1701071) B1701071
theorem B4607599 : Blo 754331 4607599 := bstep (se 1 (by rfl) ⟨3455699, by rfl⟩ : syracuseStep 4607599 = 6911399) B6911399
theorem B1134569 : Blo 754331 1134569 := bstep (se 2 (by rfl) ⟨425463, by rfl⟩ : syracuseStep 1134569 = 850927) B850927
theorem B1134911 : Blo 754331 1134911 := bstep (se 1 (by rfl) ⟨851183, by rfl⟩ : syracuseStep 1134911 = 1702367) B1702367
theorem B2150813 : Blo 754331 2150813 := bstep (se 3 (by rfl) ⟨403277, by rfl⟩ : syracuseStep 2150813 = 806555) B806555
theorem B1135295 : Blo 754331 1135295 := bstep (se 1 (by rfl) ⟨851471, by rfl⟩ : syracuseStep 1135295 = 1702943) B1702943
theorem B9196267 : Blo 754331 9196267 := bstep (se 1 (by rfl) ⟨6897200, by rfl⟩ : syracuseStep 9196267 = 13794401) B13794401
theorem B2872367 : Blo 754331 2872367 := bstep (se 1 (by rfl) ⟨2154275, by rfl⟩ : syracuseStep 2872367 = 4308551) B4308551
theorem B1135943 : Blo 754331 1135943 := bstep (se 1 (by rfl) ⟨851957, by rfl⟩ : syracuseStep 1135943 = 1703915) B1703915
theorem B2873353 : Blo 754331 2873353 := bstep (se 2 (by rfl) ⟨1077507, by rfl⟩ : syracuseStep 2873353 = 2155015) B2155015
theorem B1136951 : Blo 754331 1136951 := bstep (se 1 (by rfl) ⟨852713, by rfl⟩ : syracuseStep 1136951 = 1705427) B1705427
theorem B1137407 : Blo 754331 1137407 := bstep (se 1 (by rfl) ⟨853055, by rfl⟩ : syracuseStep 1137407 = 1706111) B1706111
theorem B2874143 : Blo 754331 2874143 := bstep (se 1 (by rfl) ⟨2155607, by rfl⟩ : syracuseStep 2874143 = 4311215) B4311215
theorem B2547179 : Blo 754331 2547179 := bstep (se 1 (by rfl) ⟨1910384, by rfl⟩ : syracuseStep 2547179 = 3820769) B3820769
theorem B3269423 : Blo 754331 3269423 := bstep (se 1 (by rfl) ⟨2452067, by rfl⟩ : syracuseStep 3269423 = 4904135) B4904135
theorem B9692237 : Blo 754331 9692237 := bstep (se 3 (by rfl) ⟨1817294, by rfl⟩ : syracuseStep 9692237 = 3634589) B3634589
theorem B35481887 : Blo 754331 35481887 := bstep (se 1 (by rfl) ⟨26611415, by rfl⟩ : syracuseStep 35481887 = 53222831) B53222831
theorem B9301115 : Blo 754331 9301115 := bstep (se 1 (by rfl) ⟨6975836, by rfl⟩ : syracuseStep 9301115 = 13951673) B13951673
theorem B2551067 : Blo 754331 2551067 := bstep (se 1 (by rfl) ⟨1913300, by rfl⟩ : syracuseStep 2551067 = 3826601) B3826601
theorem B2157931 : Blo 754331 2157931 := bstep (se 1 (by rfl) ⟨1618448, by rfl⟩ : syracuseStep 2157931 = 3236897) B3236897
theorem B2879003 : Blo 754331 2879003 := bstep (se 1 (by rfl) ⟨2159252, by rfl⟩ : syracuseStep 2879003 = 4318505) B4318505
theorem B1699559 : Blo 754331 1699559 := bstep (se 1 (by rfl) ⟨1274669, by rfl⟩ : syracuseStep 1699559 = 2549339) B2549339
theorem B1273799 : Blo 754331 1273799 := bstep (se 1 (by rfl) ⟨955349, by rfl⟩ : syracuseStep 1273799 = 1910699) B1910699
theorem B1208603 : Blo 754331 1208603 := bstep (se 1 (by rfl) ⟨906452, by rfl⟩ : syracuseStep 1208603 = 1812905) B1812905
theorem B4911407 : Blo 754331 4911407 := bstep (se 1 (by rfl) ⟨3683555, by rfl⟩ : syracuseStep 4911407 = 7367111) B7367111
theorem B1700153 : Blo 754331 1700153 := bstep (se 2 (by rfl) ⟨637557, by rfl⟩ : syracuseStep 1700153 = 1275115) B1275115
theorem B13792787 : Blo 754331 13792787 := bstep (se 1 (by rfl) ⟨10344590, by rfl⟩ : syracuseStep 13792787 = 20689181) B20689181
theorem B1275419 : Blo 754331 1275419 := bstep (se 1 (by rfl) ⟨956564, by rfl⟩ : syracuseStep 1275419 = 1913129) B1913129
theorem B2553767 : Blo 754331 2553767 := bstep (se 1 (by rfl) ⟨1915325, by rfl⟩ : syracuseStep 2553767 = 3830651) B3830651
theorem B1701935 : Blo 754331 1701935 := bstep (se 1 (by rfl) ⟨1276451, by rfl⟩ : syracuseStep 1701935 = 2552903) B2552903
theorem B1243387 : Blo 754331 1243387 := bstep (se 1 (by rfl) ⟨932540, by rfl⟩ : syracuseStep 1243387 = 1865081) B1865081
theorem B850171 : Blo 754331 850171 := bstep (se 1 (by rfl) ⟨637628, by rfl⟩ : syracuseStep 850171 = 1275257) B1275257
theorem B12942665 : Blo 754331 12942665 := bstep (se 2 (by rfl) ⟨4853499, by rfl⟩ : syracuseStep 12942665 = 9706999) B9706999
theorem B1277545 : Blo 754331 1277545 := bstep (se 2 (by rfl) ⟨479079, by rfl⟩ : syracuseStep 1277545 = 958159) B958159
theorem B41517143 : Blo 754331 41517143 := bstep (se 1 (by rfl) ⟨31137857, by rfl⟩ : syracuseStep 41517143 = 62275715) B62275715
theorem B852079 : Blo 754331 852079 := bstep (se 1 (by rfl) ⟨639059, by rfl⟩ : syracuseStep 852079 = 1278119) B1278119
theorem B2556413 : Blo 754331 2556413 := bstep (se 3 (by rfl) ⟨479327, by rfl⟩ : syracuseStep 2556413 = 958655) B958655
theorem B39387683 : Blo 754331 39387683 := bstep (se 1 (by rfl) ⟨29540762, by rfl⟩ : syracuseStep 39387683 = 59081525) B59081525
theorem B18350981 : Blo 754331 18350981 := bstep (se 4 (by rfl) ⟨1720404, by rfl⟩ : syracuseStep 18350981 = 3440809) B3440809
theorem B754919 : Blo 754331 754919 := bstep (se 1 (by rfl) ⟨566189, by rfl⟩ : syracuseStep 754919 = 1132379) B1132379
theorem B1705319 : Blo 754331 1705319 := bstep (se 1 (by rfl) ⟨1278989, by rfl⟩ : syracuseStep 1705319 = 2557979) B2557979
theorem B755407 : Blo 754331 755407 := bstep (se 1 (by rfl) ⟨566555, by rfl⟩ : syracuseStep 755407 = 1133111) B1133111
theorem B755559 : Blo 754331 755559 := bstep (se 1 (by rfl) ⟨566669, by rfl⟩ : syracuseStep 755559 = 1133339) B1133339
theorem B755615 : Blo 754331 755615 := bstep (se 1 (by rfl) ⟨566711, by rfl⟩ : syracuseStep 755615 = 1133423) B1133423
theorem B755815 : Blo 754331 755815 := bstep (se 1 (by rfl) ⟨566861, by rfl⟩ : syracuseStep 755815 = 1133723) B1133723
theorem B8718461 : Blo 754331 8718461 := bstep (se 3 (by rfl) ⟨1634711, by rfl⟩ : syracuseStep 8718461 = 3269423) B3269423
theorem B4360391 : Blo 754331 4360391 := bstep (se 1 (by rfl) ⟨3270293, by rfl⟩ : syracuseStep 4360391 = 6540587) B6540587
theorem B756031 : Blo 754331 756031 := bstep (se 1 (by rfl) ⟨567023, by rfl⟩ : syracuseStep 756031 = 1134047) B1134047
theorem B756379 : Blo 754331 756379 := bstep (se 1 (by rfl) ⟨567284, by rfl⟩ : syracuseStep 756379 = 1134569) B1134569
theorem B2624251 : Blo 754331 2624251 := bstep (se 1 (by rfl) ⟨1968188, by rfl⟩ : syracuseStep 2624251 = 3936377) B3936377
theorem B2558843 : Blo 754331 2558843 := bstep (se 1 (by rfl) ⟨1919132, by rfl⟩ : syracuseStep 2558843 = 3838265) B3838265
theorem B756607 : Blo 754331 756607 := bstep (se 1 (by rfl) ⟨567455, by rfl⟩ : syracuseStep 756607 = 1134911) B1134911
theorem B756863 : Blo 754331 756863 := bstep (se 1 (by rfl) ⟨567647, by rfl⟩ : syracuseStep 756863 = 1135295) B1135295
theorem B757295 : Blo 754331 757295 := bstep (se 1 (by rfl) ⟨567971, by rfl⟩ : syracuseStep 757295 = 1135943) B1135943
theorem B757967 : Blo 754331 757967 := bstep (se 1 (by rfl) ⟨568475, by rfl⟩ : syracuseStep 757967 = 1136951) B1136951
theorem B758271 : Blo 754331 758271 := bstep (se 1 (by rfl) ⟨568703, by rfl⟩ : syracuseStep 758271 = 1137407) B1137407
theorem B6461491 : Blo 754331 6461491 := bstep (se 1 (by rfl) ⟨4846118, by rfl⟩ : syracuseStep 6461491 = 9692237) B9692237
theorem B12261689 : Blo 754331 12261689 := bstep (se 2 (by rfl) ⟨4598133, by rfl⟩ : syracuseStep 12261689 = 9196267) B9196267
theorem B8628443 : Blo 754331 8628443 := bstep (se 1 (by rfl) ⟨6471332, by rfl⟩ : syracuseStep 8628443 = 12942665) B12942665
theorem B5746463 : Blo 754331 5746463 := bstep (se 1 (by rfl) ⟨4309847, by rfl⟩ : syracuseStep 5746463 = 8619695) B8619695
theorem B5747921 : Blo 754331 5747921 := bstep (se 2 (by rfl) ⟨2155470, by rfl⟩ : syracuseStep 5747921 = 4310941) B4310941
theorem B7255919 : Blo 754331 7255919 := bstep (se 1 (by rfl) ⟨5441939, by rfl⟩ : syracuseStep 7255919 = 10883879) B10883879
theorem B1914911 : Blo 754331 1914911 := bstep (se 1 (by rfl) ⟨1436183, by rfl⟩ : syracuseStep 1914911 = 2872367) B2872367
theorem B13810009 : Blo 754331 13810009 := bstep (se 2 (by rfl) ⟨5178753, by rfl⟩ : syracuseStep 13810009 = 10357507) B10357507
theorem B2866367 : Blo 754331 2866367 := bstep (se 1 (by rfl) ⟨2149775, by rfl⟩ : syracuseStep 2866367 = 4299551) B4299551
theorem B1916095 : Blo 754331 1916095 := bstep (se 1 (by rfl) ⟨1437071, by rfl⟩ : syracuseStep 1916095 = 2874143) B2874143
theorem B6143465 : Blo 754331 6143465 := bstep (se 2 (by rfl) ⟨2303799, by rfl⟩ : syracuseStep 6143465 = 4607599) B4607599
theorem B5750351 : Blo 754331 5750351 := bstep (se 1 (by rfl) ⟨4312763, by rfl⟩ : syracuseStep 5750351 = 8625527) B8625527
theorem B1229023 : Blo 754331 1229023 := bstep (se 1 (by rfl) ⟨921767, by rfl⟩ : syracuseStep 1229023 = 1843535) B1843535
theorem B5751323 : Blo 754331 5751323 := bstep (se 1 (by rfl) ⟨4313492, by rfl⟩ : syracuseStep 5751323 = 8626985) B8626985
theorem B13812281 : Blo 754331 13812281 := bstep (se 2 (by rfl) ⟨5179605, by rfl⟩ : syracuseStep 13812281 = 10359211) B10359211
theorem B4309757 : Blo 754331 4309757 := bstep (se 3 (by rfl) ⟨808079, by rfl⟩ : syracuseStep 4309757 = 1616159) B1616159
theorem B4835047 : Blo 754331 4835047 := bstep (se 1 (by rfl) ⟨3626285, by rfl⟩ : syracuseStep 4835047 = 7252571) B7252571
theorem B1919335 : Blo 754331 1919335 := bstep (se 1 (by rfl) ⟨1439501, by rfl⟩ : syracuseStep 1919335 = 2879003) B2879003
theorem B1133039 : Blo 754331 1133039 := bstep (se 1 (by rfl) ⟨849779, by rfl⟩ : syracuseStep 1133039 = 1699559) B1699559
theorem B805735 : Blo 754331 805735 := bstep (se 1 (by rfl) ⟨604301, by rfl⟩ : syracuseStep 805735 = 1208603) B1208603
theorem B1133435 : Blo 754331 1133435 := bstep (se 1 (by rfl) ⟨850076, by rfl⟩ : syracuseStep 1133435 = 1700153) B1700153
theorem B1657849 : Blo 754331 1657849 := bstep (se 2 (by rfl) ⟨621693, by rfl⟩ : syracuseStep 1657849 = 1243387) B1243387
theorem B1133561 : Blo 754331 1133561 := bstep (se 2 (by rfl) ⟨425085, by rfl⟩ : syracuseStep 1133561 = 850171) B850171
theorem B23252183 : Blo 754331 23252183 := bstep (se 1 (by rfl) ⟨17439137, by rfl⟩ : syracuseStep 23252183 = 34878275) B34878275
theorem B5754239 : Blo 754331 5754239 := bstep (se 1 (by rfl) ⟨4315679, by rfl⟩ : syracuseStep 5754239 = 8631359) B8631359
theorem B9195191 : Blo 754331 9195191 := bstep (se 1 (by rfl) ⟨6896393, by rfl⟩ : syracuseStep 9195191 = 13792787) B13792787
theorem B1134623 : Blo 754331 1134623 := bstep (se 1 (by rfl) ⟨850967, by rfl⟩ : syracuseStep 1134623 = 1701935) B1701935
theorem B2150687 : Blo 754331 2150687 := bstep (se 1 (by rfl) ⟨1613015, by rfl⟩ : syracuseStep 2150687 = 3226031) B3226031
theorem B1136411 : Blo 754331 1136411 := bstep (se 1 (by rfl) ⟨852308, by rfl⟩ : syracuseStep 1136411 = 1704617) B1704617
theorem B1136495 : Blo 754331 1136495 := bstep (se 1 (by rfl) ⟨852371, by rfl⟩ : syracuseStep 1136495 = 1704743) B1704743
theorem B5592979 : Blo 754331 5592979 := bstep (se 1 (by rfl) ⟨4194734, by rfl⟩ : syracuseStep 5592979 = 8389469) B8389469
theorem B6445331 : Blo 754331 6445331 := bstep (se 1 (by rfl) ⟨4833998, by rfl⟩ : syracuseStep 6445331 = 9667997) B9667997
theorem B4610591 : Blo 754331 4610591 := bstep (se 1 (by rfl) ⟨3457943, by rfl⟩ : syracuseStep 4610591 = 6915887) B6915887
theorem B1137449 : Blo 754331 1137449 := bstep (se 2 (by rfl) ⟨426543, by rfl⟩ : syracuseStep 1137449 = 853087) B853087
theorem B2153785 : Blo 754331 2153785 := bstep (se 2 (by rfl) ⟨807669, by rfl⟩ : syracuseStep 2153785 = 1615339) B1615339
theorem B4611563 : Blo 754331 4611563 := bstep (se 1 (by rfl) ⟨3458672, by rfl⟩ : syracuseStep 4611563 = 6917345) B6917345
theorem B2154377 : Blo 754331 2154377 := bstep (se 2 (by rfl) ⟨807891, by rfl⟩ : syracuseStep 2154377 = 1615783) B1615783
theorem B3825791 : Blo 754331 3825791 := bstep (se 1 (by rfl) ⟨2869343, by rfl⟩ : syracuseStep 3825791 = 5738687) B5738687
theorem B1433875 : Blo 754331 1433875 := bstep (se 1 (by rfl) ⟨1075406, by rfl⟩ : syracuseStep 1433875 = 2150813) B2150813
theorem B2155369 : Blo 754331 2155369 := bstep (se 2 (by rfl) ⟨808263, by rfl⟩ : syracuseStep 2155369 = 1616527) B1616527
theorem B3237239 : Blo 754331 3237239 := bstep (se 1 (by rfl) ⟨2427929, by rfl⟩ : syracuseStep 3237239 = 4855859) B4855859
theorem B2877241 : Blo 754331 2877241 := bstep (se 2 (by rfl) ⟨1078965, by rfl⟩ : syracuseStep 2877241 = 2157931) B2157931
theorem B1698119 : Blo 754331 1698119 := bstep (se 1 (by rfl) ⟨1273589, by rfl⟩ : syracuseStep 1698119 = 2547179) B2547179
theorem B1076095 : Blo 754331 1076095 := bstep (se 1 (by rfl) ⟨807071, by rfl⟩ : syracuseStep 1076095 = 1614143) B1614143
theorem B1273583 : Blo 754331 1273583 := bstep (se 1 (by rfl) ⟨955187, by rfl⟩ : syracuseStep 1273583 = 1910375) B1910375
theorem B23654591 : Blo 754331 23654591 := bstep (se 1 (by rfl) ⟨17740943, by rfl⟩ : syracuseStep 23654591 = 35481887) B35481887
theorem B1700711 : Blo 754331 1700711 := bstep (se 1 (by rfl) ⟨1275533, by rfl⟩ : syracuseStep 1700711 = 2551067) B2551067
theorem B849199 : Blo 754331 849199 := bstep (se 1 (by rfl) ⟨636899, by rfl⟩ : syracuseStep 849199 = 1273799) B1273799
theorem B3831137 : Blo 754331 3831137 := bstep (se 2 (by rfl) ⟨1436676, by rfl⟩ : syracuseStep 3831137 = 2873353) B2873353
theorem B3274271 : Blo 754331 3274271 := bstep (se 1 (by rfl) ⟨2455703, by rfl⟩ : syracuseStep 3274271 = 4911407) B4911407
theorem B24802973 : Blo 754331 24802973 := bstep (se 3 (by rfl) ⟨4650557, by rfl⟩ : syracuseStep 24802973 = 9301115) B9301115
theorem B850279 : Blo 754331 850279 := bstep (se 1 (by rfl) ⟨637709, by rfl⟩ : syracuseStep 850279 = 1275419) B1275419
theorem B5732855 : Blo 754331 5732855 := bstep (se 1 (by rfl) ⟨4299641, by rfl⟩ : syracuseStep 5732855 = 8599283) B8599283
theorem B1702511 : Blo 754331 1702511 := bstep (se 1 (by rfl) ⟨1276883, by rfl⟩ : syracuseStep 1702511 = 2553767) B2553767
theorem B14514983 : Blo 754331 14514983 := bstep (se 1 (by rfl) ⟨10886237, by rfl⟩ : syracuseStep 14514983 = 21772475) B21772475
theorem B1276735 : Blo 754331 1276735 := bstep (se 1 (by rfl) ⟨957551, by rfl⟩ : syracuseStep 1276735 = 1915103) B1915103
theorem B1703393 : Blo 754331 1703393 := bstep (se 2 (by rfl) ⟨638772, by rfl⟩ : syracuseStep 1703393 = 1277545) B1277545
theorem B1704275 : Blo 754331 1704275 := bstep (se 1 (by rfl) ⟨1278206, by rfl⟩ : syracuseStep 1704275 = 2556413) B2556413
theorem B3834215 : Blo 754331 3834215 := bstep (se 1 (by rfl) ⟨2875661, by rfl⟩ : syracuseStep 3834215 = 5751323) B5751323
theorem B9208187 : Blo 754331 9208187 := bstep (se 1 (by rfl) ⟨6906140, by rfl⟩ : syracuseStep 9208187 = 13812281) B13812281
theorem B6554789 : Blo 754331 6554789 := bstep (se 4 (by rfl) ⟨614511, by rfl⟩ : syracuseStep 6554789 = 1229023) B1229023
theorem B755359 : Blo 754331 755359 := bstep (se 1 (by rfl) ⟨566519, by rfl⟩ : syracuseStep 755359 = 1133039) B1133039
theorem B755623 : Blo 754331 755623 := bstep (se 1 (by rfl) ⟨566717, by rfl⟩ : syracuseStep 755623 = 1133435) B1133435
theorem B1705895 : Blo 754331 1705895 := bstep (se 1 (by rfl) ⟨1279421, by rfl⟩ : syracuseStep 1705895 = 2558843) B2558843
theorem B755707 : Blo 754331 755707 := bstep (se 1 (by rfl) ⟨566780, by rfl⟩ : syracuseStep 755707 = 1133561) B1133561
theorem B15501455 : Blo 754331 15501455 := bstep (se 1 (by rfl) ⟨11626091, by rfl⟩ : syracuseStep 15501455 = 23252183) B23252183
theorem B3836159 : Blo 754331 3836159 := bstep (se 1 (by rfl) ⟨2877119, by rfl⟩ : syracuseStep 3836159 = 5754239) B5754239
theorem B3836321 : Blo 754331 3836321 := bstep (se 2 (by rfl) ⟨1438620, by rfl⟩ : syracuseStep 3836321 = 2877241) B2877241
theorem B6130127 : Blo 754331 6130127 := bstep (se 1 (by rfl) ⟨4597595, by rfl⟩ : syracuseStep 6130127 = 9195191) B9195191
theorem B756415 : Blo 754331 756415 := bstep (se 1 (by rfl) ⟨567311, by rfl⟩ : syracuseStep 756415 = 1134623) B1134623
theorem B2559113 : Blo 754331 2559113 := bstep (se 2 (by rfl) ⟨959667, by rfl⟩ : syracuseStep 2559113 = 1919335) B1919335
theorem B757607 : Blo 754331 757607 := bstep (se 1 (by rfl) ⟨568205, by rfl⟩ : syracuseStep 757607 = 1136411) B1136411
theorem B757663 : Blo 754331 757663 := bstep (se 1 (by rfl) ⟨568247, by rfl⟩ : syracuseStep 757663 = 1136495) B1136495
theorem B4296887 : Blo 754331 4296887 := bstep (se 1 (by rfl) ⟨3222665, by rfl⟩ : syracuseStep 4296887 = 6445331) B6445331
theorem B758299 : Blo 754331 758299 := bstep (se 1 (by rfl) ⟨568724, by rfl⟩ : syracuseStep 758299 = 1137449) B1137449
theorem B5739173 : Blo 754331 5739173 := bstep (se 4 (by rfl) ⟨538047, by rfl⟩ : syracuseStep 5739173 = 1076095) B1076095
theorem B15769727 : Blo 754331 15769727 := bstep (se 1 (by rfl) ⟨11827295, by rfl⟩ : syracuseStep 15769727 = 23654591) B23654591
theorem B9676655 : Blo 754331 9676655 := bstep (se 1 (by rfl) ⟨7257491, by rfl⟩ : syracuseStep 9676655 = 14514983) B14514983
theorem B1910911 : Blo 754331 1910911 := bstep (se 1 (by rfl) ⟨1433183, by rfl⟩ : syracuseStep 1910911 = 2866367) B2866367
theorem B5745005 : Blo 754331 5745005 := bstep (se 3 (by rfl) ⟨1077188, by rfl⟩ : syracuseStep 5745005 = 2154377) B2154377
theorem B26258455 : Blo 754331 26258455 := bstep (se 1 (by rfl) ⟨19693841, by rfl⟩ : syracuseStep 26258455 = 39387683) B39387683
theorem B1911833 : Blo 754331 1911833 := bstep (se 2 (by rfl) ⟨716937, by rfl⟩ : syracuseStep 1911833 = 1433875) B1433875
theorem B12233987 : Blo 754331 12233987 := bstep (se 1 (by rfl) ⟨9175490, by rfl⟩ : syracuseStep 12233987 = 18350981) B18350981
theorem B5812307 : Blo 754331 5812307 := bstep (se 1 (by rfl) ⟨4359230, by rfl⟩ : syracuseStep 5812307 = 8718461) B8718461
theorem B2210465 : Blo 754331 2210465 := bstep (se 2 (by rfl) ⟨828924, by rfl⟩ : syracuseStep 2210465 = 1657849) B1657849
theorem B8174459 : Blo 754331 8174459 := bstep (se 1 (by rfl) ⟨6130844, by rfl⟩ : syracuseStep 8174459 = 12261689) B12261689
theorem B5752295 : Blo 754331 5752295 := bstep (se 1 (by rfl) ⟨4314221, by rfl⟩ : syracuseStep 5752295 = 8628443) B8628443
theorem B1132079 : Blo 754331 1132079 := bstep (se 1 (by rfl) ⟨849059, by rfl⟩ : syracuseStep 1132079 = 1698119) B1698119
theorem B1132265 : Blo 754331 1132265 := bstep (se 2 (by rfl) ⟨424599, by rfl⟩ : syracuseStep 1132265 = 849199) B849199
theorem B7457305 : Blo 754331 7457305 := bstep (se 2 (by rfl) ⟨2796489, by rfl⟩ : syracuseStep 7457305 = 5592979) B5592979
theorem B1133705 : Blo 754331 1133705 := bstep (se 2 (by rfl) ⟨425139, by rfl⟩ : syracuseStep 1133705 = 850279) B850279
theorem B1133807 : Blo 754331 1133807 := bstep (se 1 (by rfl) ⟨850355, by rfl⟩ : syracuseStep 1133807 = 1700711) B1700711
theorem B2182847 : Blo 754331 2182847 := bstep (se 1 (by rfl) ⟨1637135, by rfl⟩ : syracuseStep 2182847 = 3274271) B3274271
theorem B16535315 : Blo 754331 16535315 := bstep (se 1 (by rfl) ⟨12401486, by rfl⟩ : syracuseStep 16535315 = 24802973) B24802973
theorem B4837279 : Blo 754331 4837279 := bstep (se 1 (by rfl) ⟨3627959, by rfl⟩ : syracuseStep 4837279 = 7255919) B7255919
theorem B3821903 : Blo 754331 3821903 := bstep (se 1 (by rfl) ⟨2866427, by rfl⟩ : syracuseStep 3821903 = 5732855) B5732855
theorem B1135007 : Blo 754331 1135007 := bstep (se 1 (by rfl) ⟨851255, by rfl⟩ : syracuseStep 1135007 = 1702511) B1702511
theorem B2871713 : Blo 754331 2871713 := bstep (se 2 (by rfl) ⟨1076892, by rfl⟩ : syracuseStep 2871713 = 2153785) B2153785
theorem B1135595 : Blo 754331 1135595 := bstep (se 1 (by rfl) ⟨851696, by rfl⟩ : syracuseStep 1135595 = 1703393) B1703393
theorem B27678095 : Blo 754331 27678095 := bstep (se 1 (by rfl) ⟨20758571, by rfl⟩ : syracuseStep 27678095 = 41517143) B41517143
theorem B1136105 : Blo 754331 1136105 := bstep (se 2 (by rfl) ⟨426039, by rfl⟩ : syracuseStep 1136105 = 852079) B852079
theorem B2873171 : Blo 754331 2873171 := bstep (se 1 (by rfl) ⟨2154878, by rfl⟩ : syracuseStep 2873171 = 4309757) B4309757
theorem B1136879 : Blo 754331 1136879 := bstep (se 1 (by rfl) ⟨852659, by rfl⟩ : syracuseStep 1136879 = 1705319) B1705319
theorem B2873825 : Blo 754331 2873825 := bstep (se 2 (by rfl) ⟨1077684, by rfl⟩ : syracuseStep 2873825 = 2155369) B2155369
theorem B2906927 : Blo 754331 2906927 := bstep (se 1 (by rfl) ⟨2180195, by rfl⟩ : syracuseStep 2906927 = 4360391) B4360391
theorem B6446729 : Blo 754331 6446729 := bstep (se 2 (by rfl) ⟨2417523, by rfl⟩ : syracuseStep 6446729 = 4835047) B4835047
theorem B1433791 : Blo 754331 1433791 := bstep (se 1 (by rfl) ⟨1075343, by rfl⟩ : syracuseStep 1433791 = 2150687) B2150687
theorem B3499001 : Blo 754331 3499001 := bstep (se 2 (by rfl) ⟨1312125, by rfl⟩ : syracuseStep 3499001 = 2624251) B2624251
theorem B1074313 : Blo 754331 1074313 := bstep (se 2 (by rfl) ⟨402867, by rfl⟩ : syracuseStep 1074313 = 805735) B805735
theorem B3073727 : Blo 754331 3073727 := bstep (se 1 (by rfl) ⟨2305295, by rfl⟩ : syracuseStep 3073727 = 4610591) B4610591
theorem B3074375 : Blo 754331 3074375 := bstep (se 1 (by rfl) ⟨2305781, by rfl⟩ : syracuseStep 3074375 = 4611563) B4611563
theorem B2550527 : Blo 754331 2550527 := bstep (se 1 (by rfl) ⟨1912895, by rfl⟩ : syracuseStep 2550527 = 3825791) B3825791
theorem B2158159 : Blo 754331 2158159 := bstep (se 1 (by rfl) ⟨1618619, by rfl⟩ : syracuseStep 2158159 = 3237239) B3237239
theorem B849055 : Blo 754331 849055 := bstep (se 1 (by rfl) ⟨636791, by rfl⟩ : syracuseStep 849055 = 1273583) B1273583
theorem B3830975 : Blo 754331 3830975 := bstep (se 1 (by rfl) ⟨2873231, by rfl⟩ : syracuseStep 3830975 = 5746463) B5746463
theorem B8615321 : Blo 754331 8615321 := bstep (se 2 (by rfl) ⟨3230745, by rfl⟩ : syracuseStep 8615321 = 6461491) B6461491
theorem B18413345 : Blo 754331 18413345 := bstep (se 2 (by rfl) ⟨6905004, by rfl⟩ : syracuseStep 18413345 = 13810009) B13810009
theorem B3831947 : Blo 754331 3831947 := bstep (se 1 (by rfl) ⟨2873960, by rfl⟩ : syracuseStep 3831947 = 5747921) B5747921
theorem B2554091 : Blo 754331 2554091 := bstep (se 1 (by rfl) ⟨1915568, by rfl⟩ : syracuseStep 2554091 = 3831137) B3831137
theorem B1702313 : Blo 754331 1702313 := bstep (se 2 (by rfl) ⟨638367, by rfl⟩ : syracuseStep 1702313 = 1276735) B1276735
theorem B1276607 : Blo 754331 1276607 := bstep (se 1 (by rfl) ⟨957455, by rfl⟩ : syracuseStep 1276607 = 1914911) B1914911
theorem B2554793 : Blo 754331 2554793 := bstep (se 2 (by rfl) ⟨958047, by rfl⟩ : syracuseStep 2554793 = 1916095) B1916095
theorem B4095643 : Blo 754331 4095643 := bstep (se 1 (by rfl) ⟨3071732, by rfl⟩ : syracuseStep 4095643 = 6143465) B6143465
theorem B3833567 : Blo 754331 3833567 := bstep (se 1 (by rfl) ⟨2875175, by rfl⟩ : syracuseStep 3833567 = 5750351) B5750351
theorem B2556143 : Blo 754331 2556143 := bstep (se 1 (by rfl) ⟨1917107, by rfl⟩ : syracuseStep 2556143 = 3834215) B3834215
theorem B3834863 : Blo 754331 3834863 := bstep (se 1 (by rfl) ⟨2876147, by rfl⟩ : syracuseStep 3834863 = 5752295) B5752295
theorem B754719 : Blo 754331 754719 := bstep (se 1 (by rfl) ⟨566039, by rfl⟩ : syracuseStep 754719 = 1132079) B1132079
theorem B754843 : Blo 754331 754843 := bstep (se 1 (by rfl) ⟨566132, by rfl⟩ : syracuseStep 754843 = 1132265) B1132265
theorem B2557439 : Blo 754331 2557439 := bstep (se 1 (by rfl) ⟨1918079, by rfl⟩ : syracuseStep 2557439 = 3836159) B3836159
theorem B2557547 : Blo 754331 2557547 := bstep (se 1 (by rfl) ⟨1918160, by rfl⟩ : syracuseStep 2557547 = 3836321) B3836321
theorem B755803 : Blo 754331 755803 := bstep (se 1 (by rfl) ⟨566852, by rfl⟩ : syracuseStep 755803 = 1133705) B1133705
theorem B1706075 : Blo 754331 1706075 := bstep (se 1 (by rfl) ⟨1279556, by rfl⟩ : syracuseStep 1706075 = 2559113) B2559113
theorem B755871 : Blo 754331 755871 := bstep (se 1 (by rfl) ⟨566903, by rfl⟩ : syracuseStep 755871 = 1133807) B1133807
theorem B756671 : Blo 754331 756671 := bstep (se 1 (by rfl) ⟨567503, by rfl⟩ : syracuseStep 756671 = 1135007) B1135007
theorem B757063 : Blo 754331 757063 := bstep (se 1 (by rfl) ⟨567797, by rfl⟩ : syracuseStep 757063 = 1135595) B1135595
theorem B18452063 : Blo 754331 18452063 := bstep (se 1 (by rfl) ⟨13839047, by rfl⟩ : syracuseStep 18452063 = 27678095) B27678095
theorem B757403 : Blo 754331 757403 := bstep (se 1 (by rfl) ⟨568052, by rfl⟩ : syracuseStep 757403 = 1136105) B1136105
theorem B757919 : Blo 754331 757919 := bstep (se 1 (by rfl) ⟨568439, by rfl⟩ : syracuseStep 757919 = 1136879) B1136879
theorem B1937951 : Blo 754331 1937951 := bstep (se 1 (by rfl) ⟨1453463, by rfl⟩ : syracuseStep 1937951 = 2906927) B2906927
theorem B4297819 : Blo 754331 4297819 := bstep (se 1 (by rfl) ⟨3223364, by rfl⟩ : syracuseStep 4297819 = 6446729) B6446729
theorem B2332667 : Blo 754331 2332667 := bstep (se 1 (by rfl) ⟨1749500, by rfl⟩ : syracuseStep 2332667 = 3499001) B3499001
theorem B8198333 : Blo 754331 8198333 := bstep (se 3 (by rfl) ⟨1537187, by rfl⟩ : syracuseStep 8198333 = 3074375) B3074375
theorem B3874871 : Blo 754331 3874871 := bstep (se 1 (by rfl) ⟨2906153, by rfl⟩ : syracuseStep 3874871 = 5812307) B5812307
theorem B5743547 : Blo 754331 5743547 := bstep (se 1 (by rfl) ⟨4307660, by rfl⟩ : syracuseStep 5743547 = 8615321) B8615321
theorem B5449639 : Blo 754331 5449639 := bstep (se 1 (by rfl) ⟨4087229, by rfl⟩ : syracuseStep 5449639 = 8174459) B8174459
theorem B6138791 : Blo 754331 6138791 := bstep (se 1 (by rfl) ⟨4604093, by rfl⟩ : syracuseStep 6138791 = 9208187) B9208187
theorem B1911721 : Blo 754331 1911721 := bstep (se 2 (by rfl) ⟨716895, by rfl⟩ : syracuseStep 1911721 = 1433791) B1433791
theorem B4369859 : Blo 754331 4369859 := bstep (se 1 (by rfl) ⟨3277394, by rfl⟩ : syracuseStep 4369859 = 6554789) B6554789
theorem B10334303 : Blo 754331 10334303 := bstep (se 1 (by rfl) ⟨7750727, by rfl⟩ : syracuseStep 10334303 = 15501455) B15501455
theorem B11023543 : Blo 754331 11023543 := bstep (se 1 (by rfl) ⟨8267657, by rfl⟩ : syracuseStep 11023543 = 16535315) B16535315
theorem B2864591 : Blo 754331 2864591 := bstep (se 1 (by rfl) ⟨2148443, by rfl⟩ : syracuseStep 2864591 = 4296887) B4296887
theorem B1914475 : Blo 754331 1914475 := bstep (se 1 (by rfl) ⟨1435856, by rfl⟩ : syracuseStep 1914475 = 2871713) B2871713
theorem B9943073 : Blo 754331 9943073 := bstep (se 2 (by rfl) ⟨3728652, by rfl⟩ : syracuseStep 9943073 = 7457305) B7457305
theorem B1915447 : Blo 754331 1915447 := bstep (se 1 (by rfl) ⟨1436585, by rfl⟩ : syracuseStep 1915447 = 2873171) B2873171
theorem B35011273 : Blo 754331 35011273 := bstep (se 2 (by rfl) ⟨13129227, by rfl⟩ : syracuseStep 35011273 = 26258455) B26258455
theorem B1915883 : Blo 754331 1915883 := bstep (se 1 (by rfl) ⟨1436912, by rfl⟩ : syracuseStep 1915883 = 2873825) B2873825
theorem B2049151 : Blo 754331 2049151 := bstep (se 1 (by rfl) ⟨1536863, by rfl⟩ : syracuseStep 2049151 = 3073727) B3073727
theorem B1132073 : Blo 754331 1132073 := bstep (se 2 (by rfl) ⟨424527, by rfl⟩ : syracuseStep 1132073 = 849055) B849055
theorem B12275563 : Blo 754331 12275563 := bstep (se 1 (by rfl) ⟨9206672, by rfl⟩ : syracuseStep 12275563 = 18413345) B18413345
theorem B1134875 : Blo 754331 1134875 := bstep (se 1 (by rfl) ⟨851156, by rfl⟩ : syracuseStep 1134875 = 1702313) B1702313
theorem B5820925 : Blo 754331 5820925 := bstep (se 3 (by rfl) ⟨1091423, by rfl⟩ : syracuseStep 5820925 = 2182847) B2182847
theorem B5460857 : Blo 754331 5460857 := bstep (se 2 (by rfl) ⟨2047821, by rfl⟩ : syracuseStep 5460857 = 4095643) B4095643
theorem B1136183 : Blo 754331 1136183 := bstep (se 1 (by rfl) ⟨852137, by rfl⟩ : syracuseStep 1136183 = 1704275) B1704275
theorem B1137263 : Blo 754331 1137263 := bstep (se 1 (by rfl) ⟨852947, by rfl⟩ : syracuseStep 1137263 = 1705895) B1705895
theorem B1432417 : Blo 754331 1432417 := bstep (se 2 (by rfl) ⟨537156, by rfl⟩ : syracuseStep 1432417 = 1074313) B1074313
theorem B2547881 : Blo 754331 2547881 := bstep (se 2 (by rfl) ⟨955455, by rfl⟩ : syracuseStep 2547881 = 1910911) B1910911
theorem B2547935 : Blo 754331 2547935 := bstep (se 1 (by rfl) ⟨1910951, by rfl⟩ : syracuseStep 2547935 = 3821903) B3821903
theorem B3826115 : Blo 754331 3826115 := bstep (se 1 (by rfl) ⟨2869586, by rfl⟩ : syracuseStep 3826115 = 5739173) B5739173
theorem B2877545 : Blo 754331 2877545 := bstep (se 2 (by rfl) ⟨1079079, by rfl⟩ : syracuseStep 2877545 = 2158159) B2158159
theorem B6449705 : Blo 754331 6449705 := bstep (se 2 (by rfl) ⟨2418639, by rfl⟩ : syracuseStep 6449705 = 4837279) B4837279
theorem B10513151 : Blo 754331 10513151 := bstep (se 1 (by rfl) ⟨7884863, by rfl⟩ : syracuseStep 10513151 = 15769727) B15769727
theorem B16347005 : Blo 754331 16347005 := bstep (se 3 (by rfl) ⟨3065063, by rfl⟩ : syracuseStep 16347005 = 6130127) B6130127
theorem B6451103 : Blo 754331 6451103 := bstep (se 1 (by rfl) ⟨4838327, by rfl⟩ : syracuseStep 6451103 = 9676655) B9676655
theorem B3830003 : Blo 754331 3830003 := bstep (se 1 (by rfl) ⟨2872502, by rfl⟩ : syracuseStep 3830003 = 5745005) B5745005
theorem B1700351 : Blo 754331 1700351 := bstep (se 1 (by rfl) ⟨1275263, by rfl⟩ : syracuseStep 1700351 = 2550527) B2550527
theorem B1274555 : Blo 754331 1274555 := bstep (se 1 (by rfl) ⟨955916, by rfl⟩ : syracuseStep 1274555 = 1911833) B1911833
theorem B8155991 : Blo 754331 8155991 := bstep (se 1 (by rfl) ⟨6116993, by rfl⟩ : syracuseStep 8155991 = 12233987) B12233987
theorem B2553983 : Blo 754331 2553983 := bstep (se 1 (by rfl) ⟨1915487, by rfl⟩ : syracuseStep 2553983 = 3830975) B3830975
theorem B2554631 : Blo 754331 2554631 := bstep (se 1 (by rfl) ⟨1915973, by rfl⟩ : syracuseStep 2554631 = 3831947) B3831947
theorem B1702727 : Blo 754331 1702727 := bstep (se 1 (by rfl) ⟨1277045, by rfl⟩ : syracuseStep 1702727 = 2554091) B2554091
theorem B1473643 : Blo 754331 1473643 := bstep (se 1 (by rfl) ⟨1105232, by rfl⟩ : syracuseStep 1473643 = 2210465) B2210465
theorem B851071 : Blo 754331 851071 := bstep (se 1 (by rfl) ⟨638303, by rfl⟩ : syracuseStep 851071 = 1276607) B1276607
theorem B1703195 : Blo 754331 1703195 := bstep (se 1 (by rfl) ⟨1277396, by rfl⟩ : syracuseStep 1703195 = 2554793) B2554793
theorem B2555711 : Blo 754331 2555711 := bstep (se 1 (by rfl) ⟨1916783, by rfl⟩ : syracuseStep 2555711 = 3833567) B3833567
theorem B1704095 : Blo 754331 1704095 := bstep (se 1 (by rfl) ⟨1278071, by rfl⟩ : syracuseStep 1704095 = 2556143) B2556143
theorem B2556575 : Blo 754331 2556575 := bstep (se 1 (by rfl) ⟨1917431, by rfl⟩ : syracuseStep 2556575 = 3834863) B3834863
theorem B1704959 : Blo 754331 1704959 := bstep (se 1 (by rfl) ⟨1278719, by rfl⟩ : syracuseStep 1704959 = 2557439) B2557439
theorem B754715 : Blo 754331 754715 := bstep (se 1 (by rfl) ⟨566036, by rfl⟩ : syracuseStep 754715 = 1132073) B1132073
theorem B1705031 : Blo 754331 1705031 := bstep (se 1 (by rfl) ⟨1278773, by rfl⟩ : syracuseStep 1705031 = 2557547) B2557547
theorem B756583 : Blo 754331 756583 := bstep (se 1 (by rfl) ⟨567437, by rfl⟩ : syracuseStep 756583 = 1134875) B1134875
theorem B3640571 : Blo 754331 3640571 := bstep (se 1 (by rfl) ⟨2730428, by rfl⟩ : syracuseStep 3640571 = 5460857) B5460857
theorem B757455 : Blo 754331 757455 := bstep (se 1 (by rfl) ⟨568091, by rfl⟩ : syracuseStep 757455 = 1136183) B1136183
theorem B758175 : Blo 754331 758175 := bstep (se 1 (by rfl) ⟨568631, by rfl⟩ : syracuseStep 758175 = 1137263) B1137263
theorem B4299803 : Blo 754331 4299803 := bstep (se 1 (by rfl) ⟨3224852, by rfl⟩ : syracuseStep 4299803 = 6449705) B6449705
theorem B4300735 : Blo 754331 4300735 := bstep (se 1 (by rfl) ⟨3225551, by rfl⟩ : syracuseStep 4300735 = 6451103) B6451103
theorem B6889535 : Blo 754331 6889535 := bstep (se 1 (by rfl) ⟨5167151, by rfl⟩ : syracuseStep 6889535 = 10334303) B10334303
theorem B1909727 : Blo 754331 1909727 := bstep (se 1 (by rfl) ⟨1432295, by rfl⟩ : syracuseStep 1909727 = 2864591) B2864591
theorem B1909889 : Blo 754331 1909889 := bstep (se 2 (by rfl) ⟨716208, by rfl⟩ : syracuseStep 1909889 = 1432417) B1432417
theorem B6628715 : Blo 754331 6628715 := bstep (se 1 (by rfl) ⟨4971536, by rfl⟩ : syracuseStep 6628715 = 9943073) B9943073
theorem B2732201 : Blo 754331 2732201 := bstep (se 2 (by rfl) ⟨1024575, by rfl⟩ : syracuseStep 2732201 = 2049151) B2049151
theorem B12301375 : Blo 754331 12301375 := bstep (se 1 (by rfl) ⟨9226031, by rfl⟩ : syracuseStep 12301375 = 18452063) B18452063
theorem B1291967 : Blo 754331 1291967 := bstep (se 1 (by rfl) ⟨968975, by rfl⟩ : syracuseStep 1291967 = 1937951) B1937951
theorem B1555111 : Blo 754331 1555111 := bstep (se 1 (by rfl) ⟨1166333, by rfl⟩ : syracuseStep 1555111 = 2332667) B2332667
theorem B16367417 : Blo 754331 16367417 := bstep (se 2 (by rfl) ⟨6137781, by rfl⟩ : syracuseStep 16367417 = 12275563) B12275563
theorem B1918363 : Blo 754331 1918363 := bstep (se 1 (by rfl) ⟨1438772, by rfl⟩ : syracuseStep 1918363 = 2877545) B2877545
theorem B14698057 : Blo 754331 14698057 := bstep (se 2 (by rfl) ⟨5511771, by rfl⟩ : syracuseStep 14698057 = 11023543) B11023543
theorem B10898003 : Blo 754331 10898003 := bstep (se 1 (by rfl) ⟨8173502, by rfl⟩ : syracuseStep 10898003 = 16347005) B16347005
theorem B1133567 : Blo 754331 1133567 := bstep (se 1 (by rfl) ⟨850175, by rfl⟩ : syracuseStep 1133567 = 1700351) B1700351
theorem B46681697 : Blo 754331 46681697 := bstep (se 2 (by rfl) ⟨17505636, by rfl⟩ : syracuseStep 46681697 = 35011273) B35011273
theorem B1134761 : Blo 754331 1134761 := bstep (se 2 (by rfl) ⟨425535, by rfl⟩ : syracuseStep 1134761 = 851071) B851071
theorem B1135151 : Blo 754331 1135151 := bstep (se 1 (by rfl) ⟨851363, by rfl⟩ : syracuseStep 1135151 = 1702727) B1702727
theorem B1135463 : Blo 754331 1135463 := bstep (se 1 (by rfl) ⟨851597, by rfl⟩ : syracuseStep 1135463 = 1703195) B1703195
theorem B1137383 : Blo 754331 1137383 := bstep (se 1 (by rfl) ⟨853037, by rfl⟩ : syracuseStep 1137383 = 1706075) B1706075
theorem B7266185 : Blo 754331 7266185 := bstep (se 2 (by rfl) ⟨2724819, by rfl⟩ : syracuseStep 7266185 = 5449639) B5449639
theorem B2548961 : Blo 754331 2548961 := bstep (se 2 (by rfl) ⟨955860, by rfl⟩ : syracuseStep 2548961 = 1911721) B1911721
theorem B5465555 : Blo 754331 5465555 := bstep (se 1 (by rfl) ⟨4099166, by rfl⟩ : syracuseStep 5465555 = 8198333) B8198333
theorem B2583247 : Blo 754331 2583247 := bstep (se 1 (by rfl) ⟨1937435, by rfl⟩ : syracuseStep 2583247 = 3874871) B3874871
theorem B1698587 : Blo 754331 1698587 := bstep (se 1 (by rfl) ⟨1273940, by rfl⟩ : syracuseStep 1698587 = 2547881) B2547881
theorem B1698623 : Blo 754331 1698623 := bstep (se 1 (by rfl) ⟨1273967, by rfl⟩ : syracuseStep 1698623 = 2547935) B2547935
theorem B2550743 : Blo 754331 2550743 := bstep (se 1 (by rfl) ⟨1913057, by rfl⟩ : syracuseStep 2550743 = 3826115) B3826115
theorem B7859429 : Blo 754331 7859429 := bstep (se 4 (by rfl) ⟨736821, by rfl⟩ : syracuseStep 7859429 = 1473643) B1473643
theorem B3829031 : Blo 754331 3829031 := bstep (se 1 (by rfl) ⟨2871773, by rfl⟩ : syracuseStep 3829031 = 5743547) B5743547
theorem B7761233 : Blo 754331 7761233 := bstep (se 2 (by rfl) ⟨2910462, by rfl⟩ : syracuseStep 7761233 = 5820925) B5820925
theorem B5730425 : Blo 754331 5730425 := bstep (se 2 (by rfl) ⟨2148909, by rfl⟩ : syracuseStep 5730425 = 4297819) B4297819
theorem B7008767 : Blo 754331 7008767 := bstep (se 1 (by rfl) ⟨5256575, by rfl⟩ : syracuseStep 7008767 = 10513151) B10513151
theorem B4092527 : Blo 754331 4092527 := bstep (se 1 (by rfl) ⟨3069395, by rfl⟩ : syracuseStep 4092527 = 6138791) B6138791
theorem B2552633 : Blo 754331 2552633 := bstep (se 2 (by rfl) ⟨957237, by rfl⟩ : syracuseStep 2552633 = 1914475) B1914475
theorem B2913239 : Blo 754331 2913239 := bstep (se 1 (by rfl) ⟨2184929, by rfl⟩ : syracuseStep 2913239 = 4369859) B4369859
theorem B2553335 : Blo 754331 2553335 := bstep (se 1 (by rfl) ⟨1915001, by rfl⟩ : syracuseStep 2553335 = 3830003) B3830003
theorem B849703 : Blo 754331 849703 := bstep (se 1 (by rfl) ⟨637277, by rfl⟩ : syracuseStep 849703 = 1274555) B1274555
theorem B5437327 : Blo 754331 5437327 := bstep (se 1 (by rfl) ⟨4077995, by rfl⟩ : syracuseStep 5437327 = 8155991) B8155991
theorem B2553929 : Blo 754331 2553929 := bstep (se 2 (by rfl) ⟨957723, by rfl⟩ : syracuseStep 2553929 = 1915447) B1915447
theorem B1702655 : Blo 754331 1702655 := bstep (se 1 (by rfl) ⟨1276991, by rfl⟩ : syracuseStep 1702655 = 2553983) B2553983
theorem B1703087 : Blo 754331 1703087 := bstep (se 1 (by rfl) ⟨1277315, by rfl⟩ : syracuseStep 1703087 = 2554631) B2554631
theorem B1277255 : Blo 754331 1277255 := bstep (se 1 (by rfl) ⟨957941, by rfl⟩ : syracuseStep 1277255 = 1915883) B1915883
theorem B1703807 : Blo 754331 1703807 := bstep (se 1 (by rfl) ⟨1277855, by rfl⟩ : syracuseStep 1703807 = 2555711) B2555711
theorem B1704383 : Blo 754331 1704383 := bstep (se 1 (by rfl) ⟨1278287, by rfl⟩ : syracuseStep 1704383 = 2556575) B2556575
theorem B2557817 : Blo 754331 2557817 := bstep (se 2 (by rfl) ⟨959181, by rfl⟩ : syracuseStep 2557817 = 1918363) B1918363
theorem B755711 : Blo 754331 755711 := bstep (se 1 (by rfl) ⟨566783, by rfl⟩ : syracuseStep 755711 = 1133567) B1133567
theorem B19597409 : Blo 754331 19597409 := bstep (se 2 (by rfl) ⟨7349028, by rfl⟩ : syracuseStep 19597409 = 14698057) B14698057
theorem B2427047 : Blo 754331 2427047 := bstep (se 1 (by rfl) ⟨1820285, by rfl⟩ : syracuseStep 2427047 = 3640571) B3640571
theorem B756507 : Blo 754331 756507 := bstep (se 1 (by rfl) ⟨567380, by rfl⟩ : syracuseStep 756507 = 1134761) B1134761
theorem B756767 : Blo 754331 756767 := bstep (se 1 (by rfl) ⟨567575, by rfl⟩ : syracuseStep 756767 = 1135151) B1135151
theorem B756975 : Blo 754331 756975 := bstep (se 1 (by rfl) ⟨567731, by rfl⟩ : syracuseStep 756975 = 1135463) B1135463
theorem B3444329 : Blo 754331 3444329 := bstep (se 2 (by rfl) ⟨1291623, by rfl⟩ : syracuseStep 3444329 = 2583247) B2583247
theorem B758255 : Blo 754331 758255 := bstep (se 1 (by rfl) ⟨568691, by rfl⟩ : syracuseStep 758255 = 1137383) B1137383
theorem B4593023 : Blo 754331 4593023 := bstep (se 1 (by rfl) ⟨3444767, by rfl⟩ : syracuseStep 4593023 = 6889535) B6889535
theorem B3643703 : Blo 754331 3643703 := bstep (se 1 (by rfl) ⟨2732777, by rfl⟩ : syracuseStep 3643703 = 5465555) B5465555
theorem B7249769 : Blo 754331 7249769 := bstep (se 2 (by rfl) ⟨2718663, by rfl⟩ : syracuseStep 7249769 = 5437327) B5437327
theorem B2728351 : Blo 754331 2728351 := bstep (se 1 (by rfl) ⟨2046263, by rfl⟩ : syracuseStep 2728351 = 4092527) B4092527
theorem B1942159 : Blo 754331 1942159 := bstep (se 1 (by rfl) ⟨1456619, by rfl⟩ : syracuseStep 1942159 = 2913239) B2913239
theorem B2073481 : Blo 754331 2073481 := bstep (se 2 (by rfl) ⟨777555, by rfl⟩ : syracuseStep 2073481 = 1555111) B1555111
theorem B861311 : Blo 754331 861311 := bstep (se 1 (by rfl) ⟨645983, by rfl⟩ : syracuseStep 861311 = 1291967) B1291967
theorem B2866535 : Blo 754331 2866535 := bstep (se 1 (by rfl) ⟨2149901, by rfl⟩ : syracuseStep 2866535 = 4299803) B4299803
theorem B16401833 : Blo 754331 16401833 := bstep (se 2 (by rfl) ⟨6150687, by rfl⟩ : syracuseStep 16401833 = 12301375) B12301375
theorem B1132391 : Blo 754331 1132391 := bstep (se 1 (by rfl) ⟨849293, by rfl⟩ : syracuseStep 1132391 = 1698587) B1698587
theorem B1132415 : Blo 754331 1132415 := bstep (se 1 (by rfl) ⟨849311, by rfl⟩ : syracuseStep 1132415 = 1698623) B1698623
theorem B1132937 : Blo 754331 1132937 := bstep (se 2 (by rfl) ⟨424851, by rfl⟩ : syracuseStep 1132937 = 849703) B849703
theorem B3820283 : Blo 754331 3820283 := bstep (se 1 (by rfl) ⟨2865212, by rfl⟩ : syracuseStep 3820283 = 5730425) B5730425
theorem B1821467 : Blo 754331 1821467 := bstep (se 1 (by rfl) ⟨1366100, by rfl⟩ : syracuseStep 1821467 = 2732201) B2732201
theorem B4672511 : Blo 754331 4672511 := bstep (se 1 (by rfl) ⟨3504383, by rfl⟩ : syracuseStep 4672511 = 7008767) B7008767
theorem B1135103 : Blo 754331 1135103 := bstep (se 1 (by rfl) ⟨851327, by rfl⟩ : syracuseStep 1135103 = 1702655) B1702655
theorem B1135391 : Blo 754331 1135391 := bstep (se 1 (by rfl) ⟨851543, by rfl⟩ : syracuseStep 1135391 = 1703087) B1703087
theorem B1135871 : Blo 754331 1135871 := bstep (se 1 (by rfl) ⟨851903, by rfl⟩ : syracuseStep 1135871 = 1703807) B1703807
theorem B1136063 : Blo 754331 1136063 := bstep (se 1 (by rfl) ⟨852047, by rfl⟩ : syracuseStep 1136063 = 1704095) B1704095
theorem B1136639 : Blo 754331 1136639 := bstep (se 1 (by rfl) ⟨852479, by rfl⟩ : syracuseStep 1136639 = 1704959) B1704959
theorem B1136687 : Blo 754331 1136687 := bstep (se 1 (by rfl) ⟨852515, by rfl⟩ : syracuseStep 1136687 = 1705031) B1705031
theorem B7265335 : Blo 754331 7265335 := bstep (se 1 (by rfl) ⟨5449001, by rfl⟩ : syracuseStep 7265335 = 10898003) B10898003
theorem B31121131 : Blo 754331 31121131 := bstep (se 1 (by rfl) ⟨23340848, by rfl⟩ : syracuseStep 31121131 = 46681697) B46681697
theorem B4844123 : Blo 754331 4844123 := bstep (se 1 (by rfl) ⟨3633092, by rfl⟩ : syracuseStep 4844123 = 7266185) B7266185
theorem B1273151 : Blo 754331 1273151 := bstep (se 1 (by rfl) ⟨954863, by rfl⟩ : syracuseStep 1273151 = 1909727) B1909727
theorem B1273259 : Blo 754331 1273259 := bstep (se 1 (by rfl) ⟨954944, by rfl⟩ : syracuseStep 1273259 = 1909889) B1909889
theorem B1699307 : Blo 754331 1699307 := bstep (se 1 (by rfl) ⟨1274480, by rfl⟩ : syracuseStep 1699307 = 2548961) B2548961
theorem B4419143 : Blo 754331 4419143 := bstep (se 1 (by rfl) ⟨3314357, by rfl⟩ : syracuseStep 4419143 = 6628715) B6628715
theorem B1700495 : Blo 754331 1700495 := bstep (se 1 (by rfl) ⟨1275371, by rfl⟩ : syracuseStep 1700495 = 2550743) B2550743
theorem B5239619 : Blo 754331 5239619 := bstep (se 1 (by rfl) ⟨3929714, by rfl⟩ : syracuseStep 5239619 = 7859429) B7859429
theorem B2552687 : Blo 754331 2552687 := bstep (se 1 (by rfl) ⟨1914515, by rfl⟩ : syracuseStep 2552687 = 3829031) B3829031
theorem B5174155 : Blo 754331 5174155 := bstep (se 1 (by rfl) ⟨3880616, by rfl⟩ : syracuseStep 5174155 = 7761233) B7761233
theorem B1701755 : Blo 754331 1701755 := bstep (se 1 (by rfl) ⟨1276316, by rfl⟩ : syracuseStep 1701755 = 2552633) B2552633
theorem B1702223 : Blo 754331 1702223 := bstep (se 1 (by rfl) ⟨1276667, by rfl⟩ : syracuseStep 1702223 = 2553335) B2553335
theorem B1702619 : Blo 754331 1702619 := bstep (se 1 (by rfl) ⟨1276964, by rfl⟩ : syracuseStep 1702619 = 2553929) B2553929
theorem B851503 : Blo 754331 851503 := bstep (se 1 (by rfl) ⟨638627, by rfl⟩ : syracuseStep 851503 = 1277255) B1277255
theorem B10911611 : Blo 754331 10911611 := bstep (se 1 (by rfl) ⟨8183708, by rfl⟩ : syracuseStep 10911611 = 16367417) B16367417
theorem B5734313 : Blo 754331 5734313 := bstep (se 2 (by rfl) ⟨2150367, by rfl⟩ : syracuseStep 5734313 = 4300735) B4300735
theorem B3637801 : Blo 754331 3637801 := bstep (se 2 (by rfl) ⟨1364175, by rfl⟩ : syracuseStep 3637801 = 2728351) B2728351
theorem B2589545 : Blo 754331 2589545 := bstep (se 2 (by rfl) ⟨971079, by rfl⟩ : syracuseStep 2589545 = 1942159) B1942159
theorem B754927 : Blo 754331 754927 := bstep (se 1 (by rfl) ⟨566195, by rfl⟩ : syracuseStep 754927 = 1132391) B1132391
theorem B1705211 : Blo 754331 1705211 := bstep (se 1 (by rfl) ⟨1278908, by rfl⟩ : syracuseStep 1705211 = 2557817) B2557817
theorem B754943 : Blo 754331 754943 := bstep (se 1 (by rfl) ⟨566207, by rfl⟩ : syracuseStep 754943 = 1132415) B1132415
theorem B755291 : Blo 754331 755291 := bstep (se 1 (by rfl) ⟨566468, by rfl⟩ : syracuseStep 755291 = 1132937) B1132937
theorem B3115007 : Blo 754331 3115007 := bstep (se 1 (by rfl) ⟨2336255, by rfl⟩ : syracuseStep 3115007 = 4672511) B4672511
theorem B2296829 : Blo 754331 2296829 := bstep (se 3 (by rfl) ⟨430655, by rfl⟩ : syracuseStep 2296829 = 861311) B861311
theorem B756735 : Blo 754331 756735 := bstep (se 1 (by rfl) ⟨567551, by rfl⟩ : syracuseStep 756735 = 1135103) B1135103
theorem B756927 : Blo 754331 756927 := bstep (se 1 (by rfl) ⟨567695, by rfl⟩ : syracuseStep 756927 = 1135391) B1135391
theorem B757247 : Blo 754331 757247 := bstep (se 1 (by rfl) ⟨567935, by rfl⟩ : syracuseStep 757247 = 1135871) B1135871
theorem B757375 : Blo 754331 757375 := bstep (se 1 (by rfl) ⟨568031, by rfl⟩ : syracuseStep 757375 = 1136063) B1136063
theorem B757759 : Blo 754331 757759 := bstep (se 1 (by rfl) ⟨568319, by rfl⟩ : syracuseStep 757759 = 1136639) B1136639
theorem B757791 : Blo 754331 757791 := bstep (se 1 (by rfl) ⟨568343, by rfl⟩ : syracuseStep 757791 = 1136687) B1136687
theorem B2429135 : Blo 754331 2429135 := bstep (se 1 (by rfl) ⟨1821851, by rfl⟩ : syracuseStep 2429135 = 3643703) B3643703
theorem B174952885 : Blo 754331 174952885 := bstep (se 5 (by rfl) ⟨8200916, by rfl⟩ : syracuseStep 174952885 = 16401833) B16401833
theorem B4857245 : Blo 754331 4857245 := bstep (se 3 (by rfl) ⟨910733, by rfl⟩ : syracuseStep 4857245 = 1821467) B1821467
theorem B9184877 : Blo 754331 9184877 := bstep (se 3 (by rfl) ⟨1722164, by rfl⟩ : syracuseStep 9184877 = 3444329) B3444329
theorem B1911023 : Blo 754331 1911023 := bstep (se 1 (by rfl) ⟨1433267, by rfl⟩ : syracuseStep 1911023 = 2866535) B2866535
theorem B41494841 : Blo 754331 41494841 := bstep (se 2 (by rfl) ⟨15560565, by rfl⟩ : syracuseStep 41494841 = 31121131) B31121131
theorem B1618031 : Blo 754331 1618031 := bstep (se 1 (by rfl) ⟨1213523, by rfl⟩ : syracuseStep 1618031 = 2427047) B2427047
theorem B3062015 : Blo 754331 3062015 := bstep (se 1 (by rfl) ⟨2296511, by rfl⟩ : syracuseStep 3062015 = 4593023) B4593023
theorem B4833179 : Blo 754331 4833179 := bstep (se 1 (by rfl) ⟨3624884, by rfl⟩ : syracuseStep 4833179 = 7249769) B7249769
theorem B6898873 : Blo 754331 6898873 := bstep (se 2 (by rfl) ⟨2587077, by rfl⟩ : syracuseStep 6898873 = 5174155) B5174155
theorem B3229415 : Blo 754331 3229415 := bstep (se 1 (by rfl) ⟨2422061, by rfl⟩ : syracuseStep 3229415 = 4844123) B4844123
theorem B1132871 : Blo 754331 1132871 := bstep (se 1 (by rfl) ⟨849653, by rfl⟩ : syracuseStep 1132871 = 1699307) B1699307
theorem B1133663 : Blo 754331 1133663 := bstep (se 1 (by rfl) ⟨850247, by rfl⟩ : syracuseStep 1133663 = 1700495) B1700495
theorem B3493079 : Blo 754331 3493079 := bstep (se 1 (by rfl) ⟨2619809, by rfl⟩ : syracuseStep 3493079 = 5239619) B5239619
theorem B1134503 : Blo 754331 1134503 := bstep (se 1 (by rfl) ⟨850877, by rfl⟩ : syracuseStep 1134503 = 1701755) B1701755
theorem B9687113 : Blo 754331 9687113 := bstep (se 2 (by rfl) ⟨3632667, by rfl⟩ : syracuseStep 9687113 = 7265335) B7265335
theorem B1134815 : Blo 754331 1134815 := bstep (se 1 (by rfl) ⟨851111, by rfl⟩ : syracuseStep 1134815 = 1702223) B1702223
theorem B1135079 : Blo 754331 1135079 := bstep (se 1 (by rfl) ⟨851309, by rfl⟩ : syracuseStep 1135079 = 1702619) B1702619
theorem B1135337 : Blo 754331 1135337 := bstep (se 2 (by rfl) ⟨425751, by rfl⟩ : syracuseStep 1135337 = 851503) B851503
theorem B3822875 : Blo 754331 3822875 := bstep (se 1 (by rfl) ⟨2867156, by rfl⟩ : syracuseStep 3822875 = 5734313) B5734313
theorem B1136255 : Blo 754331 1136255 := bstep (se 1 (by rfl) ⟨852191, by rfl⟩ : syracuseStep 1136255 = 1704383) B1704383
theorem B13064939 : Blo 754331 13064939 := bstep (se 1 (by rfl) ⟨9798704, by rfl⟩ : syracuseStep 13064939 = 19597409) B19597409
theorem B2546855 : Blo 754331 2546855 := bstep (se 1 (by rfl) ⟨1910141, by rfl⟩ : syracuseStep 2546855 = 3820283) B3820283
theorem B848767 : Blo 754331 848767 := bstep (se 1 (by rfl) ⟨636575, by rfl⟩ : syracuseStep 848767 = 1273151) B1273151
theorem B848839 : Blo 754331 848839 := bstep (se 1 (by rfl) ⟨636629, by rfl⟩ : syracuseStep 848839 = 1273259) B1273259
theorem B2946095 : Blo 754331 2946095 := bstep (se 1 (by rfl) ⟨2209571, by rfl⟩ : syracuseStep 2946095 = 4419143) B4419143
theorem B44234261 : Blo 754331 44234261 := bstep (se 6 (by rfl) ⟨1036740, by rfl⟩ : syracuseStep 44234261 = 2073481) B2073481
theorem B1701791 : Blo 754331 1701791 := bstep (se 1 (by rfl) ⟨1276343, by rfl⟩ : syracuseStep 1701791 = 2552687) B2552687
theorem B7274407 : Blo 754331 7274407 := bstep (se 1 (by rfl) ⟨5455805, by rfl⟩ : syracuseStep 7274407 = 10911611) B10911611
theorem B4850401 : Blo 754331 4850401 := bstep (se 2 (by rfl) ⟨1818900, by rfl⟩ : syracuseStep 4850401 = 3637801) B3637801
theorem B755247 : Blo 754331 755247 := bstep (se 1 (by rfl) ⟨566435, by rfl⟩ : syracuseStep 755247 = 1132871) B1132871
theorem B755775 : Blo 754331 755775 := bstep (se 1 (by rfl) ⟨566831, by rfl⟩ : syracuseStep 755775 = 1133663) B1133663
theorem B37259509 : Blo 754331 37259509 := bstep (se 5 (by rfl) ⟨1746539, by rfl⟩ : syracuseStep 37259509 = 3493079) B3493079
theorem B756335 : Blo 754331 756335 := bstep (se 1 (by rfl) ⟨567251, by rfl⟩ : syracuseStep 756335 = 1134503) B1134503
theorem B6458075 : Blo 754331 6458075 := bstep (se 1 (by rfl) ⟨4843556, by rfl⟩ : syracuseStep 6458075 = 9687113) B9687113
theorem B756543 : Blo 754331 756543 := bstep (se 1 (by rfl) ⟨567407, by rfl⟩ : syracuseStep 756543 = 1134815) B1134815
theorem B756719 : Blo 754331 756719 := bstep (se 1 (by rfl) ⟨567539, by rfl⟩ : syracuseStep 756719 = 1135079) B1135079
theorem B756891 : Blo 754331 756891 := bstep (se 1 (by rfl) ⟨567668, by rfl⟩ : syracuseStep 756891 = 1135337) B1135337
theorem B757503 : Blo 754331 757503 := bstep (se 1 (by rfl) ⟨568127, by rfl⟩ : syracuseStep 757503 = 1136255) B1136255
theorem B27663227 : Blo 754331 27663227 := bstep (se 1 (by rfl) ⟨20747420, by rfl⟩ : syracuseStep 27663227 = 41494841) B41494841
theorem B2041343 : Blo 754331 2041343 := bstep (se 1 (by rfl) ⟨1531007, by rfl⟩ : syracuseStep 2041343 = 3062015) B3062015
theorem B3222119 : Blo 754331 3222119 := bstep (se 1 (by rfl) ⟨2416589, by rfl⟩ : syracuseStep 3222119 = 4833179) B4833179
theorem B2076671 : Blo 754331 2076671 := bstep (se 1 (by rfl) ⟨1557503, by rfl⟩ : syracuseStep 2076671 = 3115007) B3115007
theorem B1619423 : Blo 754331 1619423 := bstep (se 1 (by rfl) ⟨1214567, by rfl⟩ : syracuseStep 1619423 = 2429135) B2429135
theorem B1131689 : Blo 754331 1131689 := bstep (se 2 (by rfl) ⟨424383, by rfl⟩ : syracuseStep 1131689 = 848767) B848767
theorem B1131785 : Blo 754331 1131785 := bstep (se 2 (by rfl) ⟨424419, by rfl⟩ : syracuseStep 1131785 = 848839) B848839
theorem B1134527 : Blo 754331 1134527 := bstep (se 1 (by rfl) ⟨850895, by rfl⟩ : syracuseStep 1134527 = 1701791) B1701791
theorem B1726363 : Blo 754331 1726363 := bstep (se 1 (by rfl) ⟨1294772, by rfl⟩ : syracuseStep 1726363 = 2589545) B2589545
theorem B1136807 : Blo 754331 1136807 := bstep (se 1 (by rfl) ⟨852605, by rfl⟩ : syracuseStep 1136807 = 1705211) B1705211
theorem B2152943 : Blo 754331 2152943 := bstep (se 1 (by rfl) ⟨1614707, by rfl⟩ : syracuseStep 2152943 = 3229415) B3229415
theorem B9198497 : Blo 754331 9198497 := bstep (se 2 (by rfl) ⟨3449436, by rfl⟩ : syracuseStep 9198497 = 6898873) B6898873
theorem B1531219 : Blo 754331 1531219 := bstep (se 1 (by rfl) ⟨1148414, by rfl⟩ : syracuseStep 1531219 = 2296829) B2296829
theorem B2548583 : Blo 754331 2548583 := bstep (se 1 (by rfl) ⟨1911437, by rfl⟩ : syracuseStep 2548583 = 3822875) B3822875
theorem B8709959 : Blo 754331 8709959 := bstep (se 1 (by rfl) ⟨6532469, by rfl⟩ : syracuseStep 8709959 = 13064939) B13064939
theorem B1697903 : Blo 754331 1697903 := bstep (se 1 (by rfl) ⟨1273427, by rfl⟩ : syracuseStep 1697903 = 2546855) B2546855
theorem B3238163 : Blo 754331 3238163 := bstep (se 1 (by rfl) ⟨2428622, by rfl⟩ : syracuseStep 3238163 = 4857245) B4857245
theorem B233270513 : Blo 754331 233270513 := bstep (se 2 (by rfl) ⟨87476442, by rfl⟩ : syracuseStep 233270513 = 174952885) B174952885
theorem B6123251 : Blo 754331 6123251 := bstep (se 1 (by rfl) ⟨4592438, by rfl⟩ : syracuseStep 6123251 = 9184877) B9184877
theorem B1274015 : Blo 754331 1274015 := bstep (se 1 (by rfl) ⟨955511, by rfl⟩ : syracuseStep 1274015 = 1911023) B1911023
theorem B1078687 : Blo 754331 1078687 := bstep (se 1 (by rfl) ⟨809015, by rfl⟩ : syracuseStep 1078687 = 1618031) B1618031
theorem B1964063 : Blo 754331 1964063 := bstep (se 1 (by rfl) ⟨1473047, by rfl⟩ : syracuseStep 1964063 = 2946095) B2946095
theorem B29489507 : Blo 754331 29489507 := bstep (se 1 (by rfl) ⟨22117130, by rfl⟩ : syracuseStep 29489507 = 44234261) B44234261
theorem B9699209 : Blo 754331 9699209 := bstep (se 2 (by rfl) ⟨3637203, by rfl⟩ : syracuseStep 9699209 = 7274407) B7274407
theorem B754459 : Blo 754331 754459 := bstep (se 1 (by rfl) ⟨565844, by rfl⟩ : syracuseStep 754459 = 1131689) B1131689
theorem B754523 : Blo 754331 754523 := bstep (se 1 (by rfl) ⟨565892, by rfl⟩ : syracuseStep 754523 = 1131785) B1131785
theorem B756351 : Blo 754331 756351 := bstep (se 1 (by rfl) ⟨567263, by rfl⟩ : syracuseStep 756351 = 1134527) B1134527
theorem B49679345 : Blo 754331 49679345 := bstep (se 2 (by rfl) ⟨18629754, by rfl⟩ : syracuseStep 49679345 = 37259509) B37259509
theorem B757871 : Blo 754331 757871 := bstep (se 1 (by rfl) ⟨568403, by rfl⟩ : syracuseStep 757871 = 1136807) B1136807
theorem B6132331 : Blo 754331 6132331 := bstep (se 1 (by rfl) ⟨4599248, by rfl⟩ : syracuseStep 6132331 = 9198497) B9198497
theorem B5806639 : Blo 754331 5806639 := bstep (se 1 (by rfl) ⟨4354979, by rfl⟩ : syracuseStep 5806639 = 8709959) B8709959
theorem B1384447 : Blo 754331 1384447 := bstep (se 1 (by rfl) ⟨1038335, by rfl⟩ : syracuseStep 1384447 = 2076671) B2076671
theorem B2041625 : Blo 754331 2041625 := bstep (se 2 (by rfl) ⟨765609, by rfl⟩ : syracuseStep 2041625 = 1531219) B1531219
theorem B6466139 : Blo 754331 6466139 := bstep (se 1 (by rfl) ⟨4849604, by rfl⟩ : syracuseStep 6466139 = 9699209) B9699209
theorem B6467201 : Blo 754331 6467201 := bstep (se 2 (by rfl) ⟨2425200, by rfl⟩ : syracuseStep 6467201 = 4850401) B4850401
theorem B4305383 : Blo 754331 4305383 := bstep (se 1 (by rfl) ⟨3229037, by rfl⟩ : syracuseStep 4305383 = 6458075) B6458075
theorem B1360895 : Blo 754331 1360895 := bstep (se 1 (by rfl) ⟨1020671, by rfl⟩ : syracuseStep 1360895 = 2041343) B2041343
theorem B1131935 : Blo 754331 1131935 := bstep (se 1 (by rfl) ⟨848951, by rfl⟩ : syracuseStep 1131935 = 1697903) B1697903
theorem B2148079 : Blo 754331 2148079 := bstep (se 1 (by rfl) ⟨1611059, by rfl⟩ : syracuseStep 2148079 = 3222119) B3222119
theorem B4082167 : Blo 754331 4082167 := bstep (se 1 (by rfl) ⟨3061625, by rfl⟩ : syracuseStep 4082167 = 6123251) B6123251
theorem B1435295 : Blo 754331 1435295 := bstep (se 1 (by rfl) ⟨1076471, by rfl⟩ : syracuseStep 1435295 = 2152943) B2152943
theorem B18442151 : Blo 754331 18442151 := bstep (se 1 (by rfl) ⟨13831613, by rfl⟩ : syracuseStep 18442151 = 27663227) B27663227
theorem B1699055 : Blo 754331 1699055 := bstep (se 1 (by rfl) ⟨1274291, by rfl⟩ : syracuseStep 1699055 = 2548583) B2548583
theorem B2158775 : Blo 754331 2158775 := bstep (se 1 (by rfl) ⟨1619081, by rfl⟩ : syracuseStep 2158775 = 3238163) B3238163
theorem B1438249 : Blo 754331 1438249 := bstep (se 2 (by rfl) ⟨539343, by rfl⟩ : syracuseStep 1438249 = 1078687) B1078687
theorem B155513675 : Blo 754331 155513675 := bstep (se 1 (by rfl) ⟨116635256, by rfl⟩ : syracuseStep 155513675 = 233270513) B233270513
theorem B849343 : Blo 754331 849343 := bstep (se 1 (by rfl) ⟨637007, by rfl⟩ : syracuseStep 849343 = 1274015) B1274015
theorem B1079615 : Blo 754331 1079615 := bstep (se 1 (by rfl) ⟨809711, by rfl⟩ : syracuseStep 1079615 = 1619423) B1619423
theorem B1309375 : Blo 754331 1309375 := bstep (se 1 (by rfl) ⟨982031, by rfl⟩ : syracuseStep 1309375 = 1964063) B1964063
theorem B19659671 : Blo 754331 19659671 := bstep (se 1 (by rfl) ⟨14744753, by rfl⟩ : syracuseStep 19659671 = 29489507) B29489507
theorem B9207269 : Blo 754331 9207269 := bstep (se 4 (by rfl) ⟨863181, by rfl⟩ : syracuseStep 9207269 = 1726363) B1726363
theorem B754623 : Blo 754331 754623 := bstep (se 1 (by rfl) ⟨565967, by rfl⟩ : syracuseStep 754623 = 1131935) B1131935
theorem B32705765 : Blo 754331 32705765 := bstep (se 4 (by rfl) ⟨3066165, by rfl⟩ : syracuseStep 32705765 = 6132331) B6132331
theorem B5442889 : Blo 754331 5442889 := bstep (se 2 (by rfl) ⟨2041083, by rfl⟩ : syracuseStep 5442889 = 4082167) B4082167
theorem B6983333 : Blo 754331 6983333 := bstep (se 4 (by rfl) ⟨654687, by rfl⟩ : syracuseStep 6983333 = 1309375) B1309375
theorem B5444333 : Blo 754331 5444333 := bstep (se 3 (by rfl) ⟨1020812, by rfl⟩ : syracuseStep 5444333 = 2041625) B2041625
theorem B956863 : Blo 754331 956863 := bstep (se 1 (by rfl) ⟨717647, by rfl⟩ : syracuseStep 956863 = 1435295) B1435295
theorem B12294767 : Blo 754331 12294767 := bstep (se 1 (by rfl) ⟨9221075, by rfl⟩ : syracuseStep 12294767 = 18442151) B18442151
theorem B7742185 : Blo 754331 7742185 := bstep (se 2 (by rfl) ⟨2903319, by rfl⟩ : syracuseStep 7742185 = 5806639) B5806639
theorem B6138179 : Blo 754331 6138179 := bstep (se 1 (by rfl) ⟨4603634, by rfl⟩ : syracuseStep 6138179 = 9207269) B9207269
theorem B1845929 : Blo 754331 1845929 := bstep (se 2 (by rfl) ⟨692223, by rfl⟩ : syracuseStep 1845929 = 1384447) B1384447
theorem B2864105 : Blo 754331 2864105 := bstep (se 2 (by rfl) ⟨1074039, by rfl⟩ : syracuseStep 2864105 = 2148079) B2148079
theorem B1917665 : Blo 754331 1917665 := bstep (se 2 (by rfl) ⟨719124, by rfl⟩ : syracuseStep 1917665 = 1438249) B1438249
theorem B4310759 : Blo 754331 4310759 := bstep (se 1 (by rfl) ⟨3233069, by rfl⟩ : syracuseStep 4310759 = 6466139) B6466139
theorem B1132457 : Blo 754331 1132457 := bstep (se 2 (by rfl) ⟨424671, by rfl⟩ : syracuseStep 1132457 = 849343) B849343
theorem B1132703 : Blo 754331 1132703 := bstep (se 1 (by rfl) ⟨849527, by rfl⟩ : syracuseStep 1132703 = 1699055) B1699055
theorem B4311467 : Blo 754331 4311467 := bstep (se 1 (by rfl) ⟨3233600, by rfl⟩ : syracuseStep 4311467 = 6467201) B6467201
theorem B2870255 : Blo 754331 2870255 := bstep (se 1 (by rfl) ⟨2152691, by rfl⟩ : syracuseStep 2870255 = 4305383) B4305383
theorem B33119563 : Blo 754331 33119563 := bstep (se 1 (by rfl) ⟨24839672, by rfl⟩ : syracuseStep 33119563 = 49679345) B49679345
theorem B3629053 : Blo 754331 3629053 := bstep (se 3 (by rfl) ⟨680447, by rfl⟩ : syracuseStep 3629053 = 1360895) B1360895
theorem B2878973 : Blo 754331 2878973 := bstep (se 3 (by rfl) ⟨539807, by rfl⟩ : syracuseStep 2878973 = 1079615) B1079615
theorem B1439183 : Blo 754331 1439183 := bstep (se 1 (by rfl) ⟨1079387, by rfl⟩ : syracuseStep 1439183 = 2158775) B2158775
theorem B103675783 : Blo 754331 103675783 := bstep (se 1 (by rfl) ⟨77756837, by rfl⟩ : syracuseStep 103675783 = 155513675) B155513675
theorem B13106447 : Blo 754331 13106447 := bstep (se 1 (by rfl) ⟨9829835, by rfl⟩ : syracuseStep 13106447 = 19659671) B19659671
theorem B1278443 : Blo 754331 1278443 := bstep (se 1 (by rfl) ⟨958832, by rfl⟩ : syracuseStep 1278443 = 1917665) B1917665
theorem B754971 : Blo 754331 754971 := bstep (se 1 (by rfl) ⟨566228, by rfl⟩ : syracuseStep 754971 = 1132457) B1132457
theorem B755135 : Blo 754331 755135 := bstep (se 1 (by rfl) ⟨566351, by rfl⟩ : syracuseStep 755135 = 1132703) B1132703
theorem B4655555 : Blo 754331 4655555 := bstep (se 1 (by rfl) ⟨3491666, by rfl⟩ : syracuseStep 4655555 = 6983333) B6983333
theorem B41291653 : Blo 754331 41291653 := bstep (se 4 (by rfl) ⟨3871092, by rfl⟩ : syracuseStep 41291653 = 7742185) B7742185
theorem B8196511 : Blo 754331 8196511 := bstep (se 1 (by rfl) ⟨6147383, by rfl⟩ : syracuseStep 8196511 = 12294767) B12294767
theorem B4922477 : Blo 754331 4922477 := bstep (se 3 (by rfl) ⟨922964, by rfl⟩ : syracuseStep 4922477 = 1845929) B1845929
theorem B1909403 : Blo 754331 1909403 := bstep (se 1 (by rfl) ⟨1432052, by rfl⟩ : syracuseStep 1909403 = 2864105) B2864105
theorem B959455 : Blo 754331 959455 := bstep (se 1 (by rfl) ⟨719591, by rfl⟩ : syracuseStep 959455 = 1439183) B1439183
theorem B1913503 : Blo 754331 1913503 := bstep (se 1 (by rfl) ⟨1435127, by rfl⟩ : syracuseStep 1913503 = 2870255) B2870255
theorem B21803843 : Blo 754331 21803843 := bstep (se 1 (by rfl) ⟨16352882, by rfl⟩ : syracuseStep 21803843 = 32705765) B32705765
theorem B7257185 : Blo 754331 7257185 := bstep (se 2 (by rfl) ⟨2721444, by rfl⟩ : syracuseStep 7257185 = 5442889) B5442889
theorem B1919315 : Blo 754331 1919315 := bstep (se 1 (by rfl) ⟨1439486, by rfl⟩ : syracuseStep 1919315 = 2878973) B2878973
theorem B138234377 : Blo 754331 138234377 := bstep (se 2 (by rfl) ⟨51837891, by rfl⟩ : syracuseStep 138234377 = 103675783) B103675783
theorem B44159417 : Blo 754331 44159417 := bstep (se 2 (by rfl) ⟨16559781, by rfl⟩ : syracuseStep 44159417 = 33119563) B33119563
theorem B8737631 : Blo 754331 8737631 := bstep (se 1 (by rfl) ⟨6553223, by rfl⟩ : syracuseStep 8737631 = 13106447) B13106447
theorem B19354949 : Blo 754331 19354949 := bstep (se 4 (by rfl) ⟨1814526, by rfl⟩ : syracuseStep 19354949 = 3629053) B3629053
theorem B2873839 : Blo 754331 2873839 := bstep (se 1 (by rfl) ⟨2155379, by rfl⟩ : syracuseStep 2873839 = 4310759) B4310759
theorem B2874311 : Blo 754331 2874311 := bstep (se 1 (by rfl) ⟨2155733, by rfl⟩ : syracuseStep 2874311 = 4311467) B4311467
theorem B3629555 : Blo 754331 3629555 := bstep (se 1 (by rfl) ⟨2722166, by rfl⟩ : syracuseStep 3629555 = 5444333) B5444333
theorem B4092119 : Blo 754331 4092119 := bstep (se 1 (by rfl) ⟨3069089, by rfl⟩ : syracuseStep 4092119 = 6138179) B6138179
theorem B1275817 : Blo 754331 1275817 := bstep (se 2 (by rfl) ⟨478431, by rfl⟩ : syracuseStep 1275817 = 956863) B956863
theorem B852295 : Blo 754331 852295 := bstep (se 1 (by rfl) ⟨639221, by rfl⟩ : syracuseStep 852295 = 1278443) B1278443
theorem B1279273 : Blo 754331 1279273 := bstep (se 2 (by rfl) ⟨479727, by rfl⟩ : syracuseStep 1279273 = 959455) B959455
theorem B1279543 : Blo 754331 1279543 := bstep (se 1 (by rfl) ⟨959657, by rfl⟩ : syracuseStep 1279543 = 1919315) B1919315
theorem B3281651 : Blo 754331 3281651 := bstep (se 1 (by rfl) ⟨2461238, by rfl⟩ : syracuseStep 3281651 = 4922477) B4922477
theorem B55055537 : Blo 754331 55055537 := bstep (se 2 (by rfl) ⟨20645826, by rfl⟩ : syracuseStep 55055537 = 41291653) B41291653
theorem B2728079 : Blo 754331 2728079 := bstep (se 1 (by rfl) ⟨2046059, by rfl⟩ : syracuseStep 2728079 = 4092119) B4092119
theorem B92156251 : Blo 754331 92156251 := bstep (se 1 (by rfl) ⟨69117188, by rfl⟩ : syracuseStep 92156251 = 138234377) B138234377
theorem B29439611 : Blo 754331 29439611 := bstep (se 1 (by rfl) ⟨22079708, by rfl⟩ : syracuseStep 29439611 = 44159417) B44159417
theorem B1916207 : Blo 754331 1916207 := bstep (se 1 (by rfl) ⟨1437155, by rfl⟩ : syracuseStep 1916207 = 2874311) B2874311
theorem B10928681 : Blo 754331 10928681 := bstep (se 2 (by rfl) ⟨4098255, by rfl⟩ : syracuseStep 10928681 = 8196511) B8196511
theorem B14535895 : Blo 754331 14535895 := bstep (se 1 (by rfl) ⟨10901921, by rfl⟩ : syracuseStep 14535895 = 21803843) B21803843
theorem B4838123 : Blo 754331 4838123 := bstep (se 1 (by rfl) ⟨3628592, by rfl⟩ : syracuseStep 4838123 = 7257185) B7257185
theorem B3103703 : Blo 754331 3103703 := bstep (se 1 (by rfl) ⟨2327777, by rfl⟩ : syracuseStep 3103703 = 4655555) B4655555
theorem B5825087 : Blo 754331 5825087 := bstep (se 1 (by rfl) ⟨4368815, by rfl⟩ : syracuseStep 5825087 = 8737631) B8737631
theorem B12903299 : Blo 754331 12903299 := bstep (se 1 (by rfl) ⟨9677474, by rfl⟩ : syracuseStep 12903299 = 19354949) B19354949
theorem B2419703 : Blo 754331 2419703 := bstep (se 1 (by rfl) ⟨1814777, by rfl⟩ : syracuseStep 2419703 = 3629555) B3629555
theorem B1272935 : Blo 754331 1272935 := bstep (se 1 (by rfl) ⟨954701, by rfl⟩ : syracuseStep 1272935 = 1909403) B1909403
theorem B2551337 : Blo 754331 2551337 := bstep (se 2 (by rfl) ⟨956751, by rfl⟩ : syracuseStep 2551337 = 1913503) B1913503
theorem B1701089 : Blo 754331 1701089 := bstep (se 2 (by rfl) ⟨637908, by rfl⟩ : syracuseStep 1701089 = 1275817) B1275817
theorem B3831785 : Blo 754331 3831785 := bstep (se 2 (by rfl) ⟨1436919, by rfl⟩ : syracuseStep 3831785 = 2873839) B2873839
theorem B1705697 : Blo 754331 1705697 := bstep (se 2 (by rfl) ⟨639636, by rfl⟩ : syracuseStep 1705697 = 1279273) B1279273
theorem B1706057 : Blo 754331 1706057 := bstep (se 2 (by rfl) ⟨639771, by rfl⟩ : syracuseStep 1706057 = 1279543) B1279543
theorem B36703691 : Blo 754331 36703691 := bstep (se 1 (by rfl) ⟨27527768, by rfl⟩ : syracuseStep 36703691 = 55055537) B55055537
theorem B2069135 : Blo 754331 2069135 := bstep (se 1 (by rfl) ⟨1551851, by rfl⟩ : syracuseStep 2069135 = 3103703) B3103703
theorem B1613135 : Blo 754331 1613135 := bstep (se 1 (by rfl) ⟨1209851, by rfl⟩ : syracuseStep 1613135 = 2419703) B2419703
theorem B7285787 : Blo 754331 7285787 := bstep (se 1 (by rfl) ⟨5464340, by rfl⟩ : syracuseStep 7285787 = 10928681) B10928681
theorem B3225415 : Blo 754331 3225415 := bstep (se 1 (by rfl) ⟨2419061, by rfl⟩ : syracuseStep 3225415 = 4838123) B4838123
theorem B19381193 : Blo 754331 19381193 := bstep (se 2 (by rfl) ⟨7267947, by rfl⟩ : syracuseStep 19381193 = 14535895) B14535895
theorem B1818719 : Blo 754331 1818719 := bstep (se 1 (by rfl) ⟨1364039, by rfl⟩ : syracuseStep 1818719 = 2728079) B2728079
theorem B3883391 : Blo 754331 3883391 := bstep (se 1 (by rfl) ⟨2912543, by rfl⟩ : syracuseStep 3883391 = 5825087) B5825087
theorem B8602199 : Blo 754331 8602199 := bstep (se 1 (by rfl) ⟨6451649, by rfl⟩ : syracuseStep 8602199 = 12903299) B12903299
theorem B1134059 : Blo 754331 1134059 := bstep (se 1 (by rfl) ⟨850544, by rfl⟩ : syracuseStep 1134059 = 1701089) B1701089
theorem B1136393 : Blo 754331 1136393 := bstep (se 2 (by rfl) ⟨426147, by rfl⟩ : syracuseStep 1136393 = 852295) B852295
theorem B2187767 : Blo 754331 2187767 := bstep (se 1 (by rfl) ⟨1640825, by rfl⟩ : syracuseStep 2187767 = 3281651) B3281651
theorem B122875001 : Blo 754331 122875001 := bstep (se 2 (by rfl) ⟨46078125, by rfl⟩ : syracuseStep 122875001 = 92156251) B92156251
theorem B848623 : Blo 754331 848623 := bstep (se 1 (by rfl) ⟨636467, by rfl⟩ : syracuseStep 848623 = 1272935) B1272935
theorem B1700891 : Blo 754331 1700891 := bstep (se 1 (by rfl) ⟨1275668, by rfl⟩ : syracuseStep 1700891 = 2551337) B2551337
theorem B19626407 : Blo 754331 19626407 := bstep (se 1 (by rfl) ⟨14719805, by rfl⟩ : syracuseStep 19626407 = 29439611) B29439611
theorem B2554523 : Blo 754331 2554523 := bstep (se 1 (by rfl) ⟨1915892, by rfl⟩ : syracuseStep 2554523 = 3831785) B3831785
theorem B1277471 : Blo 754331 1277471 := bstep (se 1 (by rfl) ⟨958103, by rfl⟩ : syracuseStep 1277471 = 1916207) B1916207
theorem B1212479 : Blo 754331 1212479 := bstep (se 1 (by rfl) ⟨909359, by rfl⟩ : syracuseStep 1212479 = 1818719) B1818719
theorem B2588927 : Blo 754331 2588927 := bstep (se 1 (by rfl) ⟨1941695, by rfl⟩ : syracuseStep 2588927 = 3883391) B3883391
theorem B5734799 : Blo 754331 5734799 := bstep (se 1 (by rfl) ⟨4301099, by rfl⟩ : syracuseStep 5734799 = 8602199) B8602199
theorem B5834045 : Blo 754331 5834045 := bstep (se 3 (by rfl) ⟨1093883, by rfl⟩ : syracuseStep 5834045 = 2187767) B2187767
theorem B756039 : Blo 754331 756039 := bstep (se 1 (by rfl) ⟨567029, by rfl⟩ : syracuseStep 756039 = 1134059) B1134059
theorem B1379423 : Blo 754331 1379423 := bstep (se 1 (by rfl) ⟨1034567, by rfl⟩ : syracuseStep 1379423 = 2069135) B2069135
theorem B757595 : Blo 754331 757595 := bstep (se 1 (by rfl) ⟨568196, by rfl⟩ : syracuseStep 757595 = 1136393) B1136393
theorem B4857191 : Blo 754331 4857191 := bstep (se 1 (by rfl) ⟨3642893, by rfl⟩ : syracuseStep 4857191 = 7285787) B7285787
theorem B4300553 : Blo 754331 4300553 := bstep (se 2 (by rfl) ⟨1612707, by rfl⟩ : syracuseStep 4300553 = 3225415) B3225415
theorem B4301693 : Blo 754331 4301693 := bstep (se 3 (by rfl) ⟨806567, by rfl⟩ : syracuseStep 4301693 = 1613135) B1613135
theorem B13084271 : Blo 754331 13084271 := bstep (se 1 (by rfl) ⟨9813203, by rfl⟩ : syracuseStep 13084271 = 19626407) B19626407
theorem B12920795 : Blo 754331 12920795 := bstep (se 1 (by rfl) ⟨9690596, by rfl⟩ : syracuseStep 12920795 = 19381193) B19381193
theorem B1131497 : Blo 754331 1131497 := bstep (se 2 (by rfl) ⟨424311, by rfl⟩ : syracuseStep 1131497 = 848623) B848623
theorem B1133927 : Blo 754331 1133927 := bstep (se 1 (by rfl) ⟨850445, by rfl⟩ : syracuseStep 1133927 = 1700891) B1700891
theorem B1137131 : Blo 754331 1137131 := bstep (se 1 (by rfl) ⟨852848, by rfl⟩ : syracuseStep 1137131 = 1705697) B1705697
theorem B1137371 : Blo 754331 1137371 := bstep (se 1 (by rfl) ⟨853028, by rfl⟩ : syracuseStep 1137371 = 1706057) B1706057
theorem B24469127 : Blo 754331 24469127 := bstep (se 1 (by rfl) ⟨18351845, by rfl⟩ : syracuseStep 24469127 = 36703691) B36703691
theorem B81916667 : Blo 754331 81916667 := bstep (se 1 (by rfl) ⟨61437500, by rfl⟩ : syracuseStep 81916667 = 122875001) B122875001
theorem B1703015 : Blo 754331 1703015 := bstep (se 1 (by rfl) ⟨1277261, by rfl⟩ : syracuseStep 1703015 = 2554523) B2554523
theorem B851647 : Blo 754331 851647 := bstep (se 1 (by rfl) ⟨638735, by rfl⟩ : syracuseStep 851647 = 1277471) B1277471
theorem B754331 : Blo 754331 754331 := bstep (se 1 (by rfl) ⟨565748, by rfl⟩ : syracuseStep 754331 = 1131497) B1131497
theorem B919615 : Blo 754331 919615 := bstep (se 1 (by rfl) ⟨689711, by rfl⟩ : syracuseStep 919615 = 1379423) B1379423
theorem B755951 : Blo 754331 755951 := bstep (se 1 (by rfl) ⟨566963, by rfl⟩ : syracuseStep 755951 = 1133927) B1133927
theorem B758087 : Blo 754331 758087 := bstep (se 1 (by rfl) ⟨568565, by rfl⟩ : syracuseStep 758087 = 1137131) B1137131
theorem B758247 : Blo 754331 758247 := bstep (se 1 (by rfl) ⟨568685, by rfl⟩ : syracuseStep 758247 = 1137371) B1137371
theorem B8722847 : Blo 754331 8722847 := bstep (se 1 (by rfl) ⟨6542135, by rfl⟩ : syracuseStep 8722847 = 13084271) B13084271
theorem B2867035 : Blo 754331 2867035 := bstep (se 1 (by rfl) ⟨2150276, by rfl⟩ : syracuseStep 2867035 = 4300553) B4300553
theorem B2867795 : Blo 754331 2867795 := bstep (se 1 (by rfl) ⟨2150846, by rfl⟩ : syracuseStep 2867795 = 4301693) B4301693
theorem B54611111 : Blo 754331 54611111 := bstep (se 1 (by rfl) ⟨40958333, by rfl⟩ : syracuseStep 54611111 = 81916667) B81916667
theorem B1135343 : Blo 754331 1135343 := bstep (se 1 (by rfl) ⟨851507, by rfl⟩ : syracuseStep 1135343 = 1703015) B1703015
theorem B1135529 : Blo 754331 1135529 := bstep (se 2 (by rfl) ⟨425823, by rfl⟩ : syracuseStep 1135529 = 851647) B851647
theorem B808319 : Blo 754331 808319 := bstep (se 1 (by rfl) ⟨606239, by rfl⟩ : syracuseStep 808319 = 1212479) B1212479
theorem B3823199 : Blo 754331 3823199 := bstep (se 1 (by rfl) ⟨2867399, by rfl⟩ : syracuseStep 3823199 = 5734799) B5734799
theorem B6903805 : Blo 754331 6903805 := bstep (se 3 (by rfl) ⟨1294463, by rfl⟩ : syracuseStep 6903805 = 2588927) B2588927
theorem B15557453 : Blo 754331 15557453 := bstep (se 3 (by rfl) ⟨2917022, by rfl⟩ : syracuseStep 15557453 = 5834045) B5834045
theorem B3238127 : Blo 754331 3238127 := bstep (se 1 (by rfl) ⟨2428595, by rfl⟩ : syracuseStep 3238127 = 4857191) B4857191
theorem B16312751 : Blo 754331 16312751 := bstep (se 1 (by rfl) ⟨12234563, by rfl⟩ : syracuseStep 16312751 = 24469127) B24469127
theorem B8613863 : Blo 754331 8613863 := bstep (se 1 (by rfl) ⟨6460397, by rfl⟩ : syracuseStep 8613863 = 12920795) B12920795
theorem B36407407 : Blo 754331 36407407 := bstep (se 1 (by rfl) ⟨27305555, by rfl⟩ : syracuseStep 36407407 = 54611111) B54611111
theorem B756895 : Blo 754331 756895 := bstep (se 1 (by rfl) ⟨567671, by rfl⟩ : syracuseStep 756895 = 1135343) B1135343
theorem B757019 : Blo 754331 757019 := bstep (se 1 (by rfl) ⟨567764, by rfl⟩ : syracuseStep 757019 = 1135529) B1135529
theorem B5742575 : Blo 754331 5742575 := bstep (se 1 (by rfl) ⟨4306931, by rfl⟩ : syracuseStep 5742575 = 8613863) B8613863
theorem B1911863 : Blo 754331 1911863 := bstep (se 1 (by rfl) ⟨1433897, by rfl⟩ : syracuseStep 1911863 = 2867795) B2867795
theorem B1226153 : Blo 754331 1226153 := bstep (se 2 (by rfl) ⟨459807, by rfl⟩ : syracuseStep 1226153 = 919615) B919615
theorem B10371635 : Blo 754331 10371635 := bstep (se 1 (by rfl) ⟨7778726, by rfl⟩ : syracuseStep 10371635 = 15557453) B15557453
theorem B3822713 : Blo 754331 3822713 := bstep (se 2 (by rfl) ⟨1433517, by rfl⟩ : syracuseStep 3822713 = 2867035) B2867035
theorem B2155517 : Blo 754331 2155517 := bstep (se 3 (by rfl) ⟨404159, by rfl⟩ : syracuseStep 2155517 = 808319) B808319
theorem B2548799 : Blo 754331 2548799 := bstep (se 1 (by rfl) ⟨1911599, by rfl⟩ : syracuseStep 2548799 = 3823199) B3823199
theorem B23260925 : Blo 754331 23260925 := bstep (se 3 (by rfl) ⟨4361423, by rfl⟩ : syracuseStep 23260925 = 8722847) B8722847
theorem B2158751 : Blo 754331 2158751 := bstep (se 1 (by rfl) ⟨1619063, by rfl⟩ : syracuseStep 2158751 = 3238127) B3238127
theorem B10875167 : Blo 754331 10875167 := bstep (se 1 (by rfl) ⟨8156375, by rfl⟩ : syracuseStep 10875167 = 16312751) B16312751
theorem B9205073 : Blo 754331 9205073 := bstep (se 2 (by rfl) ⟨3451902, by rfl⟩ : syracuseStep 9205073 = 6903805) B6903805
theorem B6914423 : Blo 754331 6914423 := bstep (se 1 (by rfl) ⟨5185817, by rfl⟩ : syracuseStep 6914423 = 10371635) B10371635
theorem B15507283 : Blo 754331 15507283 := bstep (se 1 (by rfl) ⟨11630462, by rfl⟩ : syracuseStep 15507283 = 23260925) B23260925
theorem B7250111 : Blo 754331 7250111 := bstep (se 1 (by rfl) ⟨5437583, by rfl⟩ : syracuseStep 7250111 = 10875167) B10875167
theorem B6136715 : Blo 754331 6136715 := bstep (se 1 (by rfl) ⟨4602536, by rfl⟩ : syracuseStep 6136715 = 9205073) B9205073
theorem B48543209 : Blo 754331 48543209 := bstep (se 2 (by rfl) ⟨18203703, by rfl⟩ : syracuseStep 48543209 = 36407407) B36407407
theorem B5756669 : Blo 754331 5756669 := bstep (se 3 (by rfl) ⟨1079375, by rfl⟩ : syracuseStep 5756669 = 2158751) B2158751
theorem B2548475 : Blo 754331 2548475 := bstep (se 1 (by rfl) ⟨1911356, by rfl⟩ : syracuseStep 2548475 = 3822713) B3822713
theorem B3828383 : Blo 754331 3828383 := bstep (se 1 (by rfl) ⟨2871287, by rfl⟩ : syracuseStep 3828383 = 5742575) B5742575
theorem B1437011 : Blo 754331 1437011 := bstep (se 1 (by rfl) ⟨1077758, by rfl⟩ : syracuseStep 1437011 = 2155517) B2155517
theorem B1699199 : Blo 754331 1699199 := bstep (se 1 (by rfl) ⟨1274399, by rfl⟩ : syracuseStep 1699199 = 2548799) B2548799
theorem B1274575 : Blo 754331 1274575 := bstep (se 1 (by rfl) ⟨955931, by rfl⟩ : syracuseStep 1274575 = 1911863) B1911863
theorem B817435 : Blo 754331 817435 := bstep (se 1 (by rfl) ⟨613076, by rfl⟩ : syracuseStep 817435 = 1226153) B1226153
theorem B4359653 : Blo 754331 4359653 := bstep (se 4 (by rfl) ⟨408717, by rfl⟩ : syracuseStep 4359653 = 817435) B817435
theorem B3837779 : Blo 754331 3837779 := bstep (se 1 (by rfl) ⟨2878334, by rfl⟩ : syracuseStep 3837779 = 5756669) B5756669
theorem B958007 : Blo 754331 958007 := bstep (se 1 (by rfl) ⟨718505, by rfl⟩ : syracuseStep 958007 = 1437011) B1437011
theorem B4833407 : Blo 754331 4833407 := bstep (se 1 (by rfl) ⟨3625055, by rfl⟩ : syracuseStep 4833407 = 7250111) B7250111
theorem B1132799 : Blo 754331 1132799 := bstep (se 1 (by rfl) ⟨849599, by rfl⟩ : syracuseStep 1132799 = 1699199) B1699199
theorem B32362139 : Blo 754331 32362139 := bstep (se 1 (by rfl) ⟨24271604, by rfl⟩ : syracuseStep 32362139 = 48543209) B48543209
theorem B18438461 : Blo 754331 18438461 := bstep (se 3 (by rfl) ⟨3457211, by rfl⟩ : syracuseStep 18438461 = 6914423) B6914423
theorem B1698983 : Blo 754331 1698983 := bstep (se 1 (by rfl) ⟨1274237, by rfl⟩ : syracuseStep 1698983 = 2548475) B2548475
theorem B4091143 : Blo 754331 4091143 := bstep (se 1 (by rfl) ⟨3068357, by rfl⟩ : syracuseStep 4091143 = 6136715) B6136715
theorem B1699433 : Blo 754331 1699433 := bstep (se 2 (by rfl) ⟨637287, by rfl⟩ : syracuseStep 1699433 = 1274575) B1274575
theorem B2552255 : Blo 754331 2552255 := bstep (se 1 (by rfl) ⟨1914191, by rfl⟩ : syracuseStep 2552255 = 3828383) B3828383
theorem B20676377 : Blo 754331 20676377 := bstep (se 2 (by rfl) ⟨7753641, by rfl⟩ : syracuseStep 20676377 = 15507283) B15507283
theorem B755199 : Blo 754331 755199 := bstep (se 1 (by rfl) ⟨566399, by rfl⟩ : syracuseStep 755199 = 1132799) B1132799
theorem B2558519 : Blo 754331 2558519 := bstep (se 1 (by rfl) ⟨1918889, by rfl⟩ : syracuseStep 2558519 = 3837779) B3837779
theorem B12292307 : Blo 754331 12292307 := bstep (se 1 (by rfl) ⟨9219230, by rfl⟩ : syracuseStep 12292307 = 18438461) B18438461
theorem B3222271 : Blo 754331 3222271 := bstep (se 1 (by rfl) ⟨2416703, by rfl⟩ : syracuseStep 3222271 = 4833407) B4833407
theorem B21574759 : Blo 754331 21574759 := bstep (se 1 (by rfl) ⟨16181069, by rfl⟩ : syracuseStep 21574759 = 32362139) B32362139
theorem B5454857 : Blo 754331 5454857 := bstep (se 2 (by rfl) ⟨2045571, by rfl⟩ : syracuseStep 5454857 = 4091143) B4091143
theorem B1132655 : Blo 754331 1132655 := bstep (se 1 (by rfl) ⟨849491, by rfl⟩ : syracuseStep 1132655 = 1698983) B1698983
theorem B1132955 : Blo 754331 1132955 := bstep (se 1 (by rfl) ⟨849716, by rfl⟩ : syracuseStep 1132955 = 1699433) B1699433
theorem B13784251 : Blo 754331 13784251 := bstep (se 1 (by rfl) ⟨10338188, by rfl⟩ : syracuseStep 13784251 = 20676377) B20676377
theorem B2906435 : Blo 754331 2906435 := bstep (se 1 (by rfl) ⟨2179826, by rfl⟩ : syracuseStep 2906435 = 4359653) B4359653
theorem B1701503 : Blo 754331 1701503 := bstep (se 1 (by rfl) ⟨1276127, by rfl⟩ : syracuseStep 1701503 = 2552255) B2552255
theorem B2554685 : Blo 754331 2554685 := bstep (se 3 (by rfl) ⟨479003, by rfl⟩ : syracuseStep 2554685 = 958007) B958007
theorem B755103 : Blo 754331 755103 := bstep (se 1 (by rfl) ⟨566327, by rfl⟩ : syracuseStep 755103 = 1132655) B1132655
theorem B755303 : Blo 754331 755303 := bstep (se 1 (by rfl) ⟨566477, by rfl⟩ : syracuseStep 755303 = 1132955) B1132955
theorem B1705679 : Blo 754331 1705679 := bstep (se 1 (by rfl) ⟨1279259, by rfl⟩ : syracuseStep 1705679 = 2558519) B2558519
theorem B8194871 : Blo 754331 8194871 := bstep (se 1 (by rfl) ⟨6146153, by rfl⟩ : syracuseStep 8194871 = 12292307) B12292307
theorem B4296361 : Blo 754331 4296361 := bstep (se 2 (by rfl) ⟨1611135, by rfl⟩ : syracuseStep 4296361 = 3222271) B3222271
theorem B1937623 : Blo 754331 1937623 := bstep (se 1 (by rfl) ⟨1453217, by rfl⟩ : syracuseStep 1937623 = 2906435) B2906435
theorem B1134335 : Blo 754331 1134335 := bstep (se 1 (by rfl) ⟨850751, by rfl⟩ : syracuseStep 1134335 = 1701503) B1701503
theorem B28766345 : Blo 754331 28766345 := bstep (se 2 (by rfl) ⟨10787379, by rfl⟩ : syracuseStep 28766345 = 21574759) B21574759
theorem B18379001 : Blo 754331 18379001 := bstep (se 2 (by rfl) ⟨6892125, by rfl⟩ : syracuseStep 18379001 = 13784251) B13784251
theorem B1703123 : Blo 754331 1703123 := bstep (se 1 (by rfl) ⟨1277342, by rfl⟩ : syracuseStep 1703123 = 2554685) B2554685
theorem B3636571 : Blo 754331 3636571 := bstep (se 1 (by rfl) ⟨2727428, by rfl⟩ : syracuseStep 3636571 = 5454857) B5454857
theorem B76710253 : Blo 754331 76710253 := bstep (se 3 (by rfl) ⟨14383172, by rfl⟩ : syracuseStep 76710253 = 28766345) B28766345
theorem B756223 : Blo 754331 756223 := bstep (se 1 (by rfl) ⟨567167, by rfl⟩ : syracuseStep 756223 = 1134335) B1134335
theorem B1135415 : Blo 754331 1135415 := bstep (se 1 (by rfl) ⟨851561, by rfl⟩ : syracuseStep 1135415 = 1703123) B1703123
theorem B49010669 : Blo 754331 49010669 := bstep (se 3 (by rfl) ⟨9189500, by rfl⟩ : syracuseStep 49010669 = 18379001) B18379001
theorem B1137119 : Blo 754331 1137119 := bstep (se 1 (by rfl) ⟨852839, by rfl⟩ : syracuseStep 1137119 = 1705679) B1705679
theorem B5463247 : Blo 754331 5463247 := bstep (se 1 (by rfl) ⟨4097435, by rfl⟩ : syracuseStep 5463247 = 8194871) B8194871
theorem B5728481 : Blo 754331 5728481 := bstep (se 2 (by rfl) ⟨2148180, by rfl⟩ : syracuseStep 5728481 = 4296361) B4296361
theorem B2583497 : Blo 754331 2583497 := bstep (se 2 (by rfl) ⟨968811, by rfl⟩ : syracuseStep 2583497 = 1937623) B1937623
theorem B4848761 : Blo 754331 4848761 := bstep (se 2 (by rfl) ⟨1818285, by rfl⟩ : syracuseStep 4848761 = 3636571) B3636571
theorem B756943 : Blo 754331 756943 := bstep (se 1 (by rfl) ⟨567707, by rfl⟩ : syracuseStep 756943 = 1135415) B1135415
theorem B32673779 : Blo 754331 32673779 := bstep (se 1 (by rfl) ⟨24505334, by rfl⟩ : syracuseStep 32673779 = 49010669) B49010669
theorem B758079 : Blo 754331 758079 := bstep (se 1 (by rfl) ⟨568559, by rfl⟩ : syracuseStep 758079 = 1137119) B1137119
theorem B7284329 : Blo 754331 7284329 := bstep (se 2 (by rfl) ⟨2731623, by rfl⟩ : syracuseStep 7284329 = 5463247) B5463247
theorem B102280337 : Blo 754331 102280337 := bstep (se 2 (by rfl) ⟨38355126, by rfl⟩ : syracuseStep 102280337 = 76710253) B76710253
theorem B3818987 : Blo 754331 3818987 := bstep (se 1 (by rfl) ⟨2864240, by rfl⟩ : syracuseStep 3818987 = 5728481) B5728481
theorem B1722331 : Blo 754331 1722331 := bstep (se 1 (by rfl) ⟨1291748, by rfl⟩ : syracuseStep 1722331 = 2583497) B2583497
theorem B3232507 : Blo 754331 3232507 := bstep (se 1 (by rfl) ⟨2424380, by rfl⟩ : syracuseStep 3232507 = 4848761) B4848761
theorem B2296441 : Blo 754331 2296441 := bstep (se 2 (by rfl) ⟨861165, by rfl⟩ : syracuseStep 2296441 = 1722331) B1722331
theorem B4856219 : Blo 754331 4856219 := bstep (se 1 (by rfl) ⟨3642164, by rfl⟩ : syracuseStep 4856219 = 7284329) B7284329
theorem B4310009 : Blo 754331 4310009 := bstep (se 2 (by rfl) ⟨1616253, by rfl⟩ : syracuseStep 4310009 = 3232507) B3232507
theorem B2545991 : Blo 754331 2545991 := bstep (se 1 (by rfl) ⟨1909493, by rfl⟩ : syracuseStep 2545991 = 3818987) B3818987
theorem B21782519 : Blo 754331 21782519 := bstep (se 1 (by rfl) ⟨16336889, by rfl⟩ : syracuseStep 21782519 = 32673779) B32673779
theorem B68186891 : Blo 754331 68186891 := bstep (se 1 (by rfl) ⟨51140168, by rfl⟩ : syracuseStep 68186891 = 102280337) B102280337
theorem B181831709 : Blo 754331 181831709 := bstep (se 3 (by rfl) ⟨34093445, by rfl⟩ : syracuseStep 181831709 = 68186891) B68186891
theorem B14521679 : Blo 754331 14521679 := bstep (se 1 (by rfl) ⟨10891259, by rfl⟩ : syracuseStep 14521679 = 21782519) B21782519
theorem B3061921 : Blo 754331 3061921 := bstep (se 2 (by rfl) ⟨1148220, by rfl⟩ : syracuseStep 3061921 = 2296441) B2296441
theorem B2873339 : Blo 754331 2873339 := bstep (se 1 (by rfl) ⟨2155004, by rfl⟩ : syracuseStep 2873339 = 4310009) B4310009
theorem B1697327 : Blo 754331 1697327 := bstep (se 1 (by rfl) ⟨1272995, by rfl⟩ : syracuseStep 1697327 = 2545991) B2545991
theorem B3237479 : Blo 754331 3237479 := bstep (se 1 (by rfl) ⟨2428109, by rfl⟩ : syracuseStep 3237479 = 4856219) B4856219
theorem B121221139 : Blo 754331 121221139 := bstep (se 1 (by rfl) ⟨90915854, by rfl⟩ : syracuseStep 121221139 = 181831709) B181831709
theorem B9681119 : Blo 754331 9681119 := bstep (se 1 (by rfl) ⟨7260839, by rfl⟩ : syracuseStep 9681119 = 14521679) B14521679
theorem B1915559 : Blo 754331 1915559 := bstep (se 1 (by rfl) ⟨1436669, by rfl⟩ : syracuseStep 1915559 = 2873339) B2873339
theorem B1131551 : Blo 754331 1131551 := bstep (se 1 (by rfl) ⟨848663, by rfl⟩ : syracuseStep 1131551 = 1697327) B1697327
theorem B4082561 : Blo 754331 4082561 := bstep (se 2 (by rfl) ⟨1530960, by rfl⟩ : syracuseStep 4082561 = 3061921) B3061921
theorem B2158319 : Blo 754331 2158319 := bstep (se 1 (by rfl) ⟨1618739, by rfl⟩ : syracuseStep 2158319 = 3237479) B3237479
theorem B754367 : Blo 754331 754367 := bstep (se 1 (by rfl) ⟨565775, by rfl⟩ : syracuseStep 754367 = 1131551) B1131551
theorem B2721707 : Blo 754331 2721707 := bstep (se 1 (by rfl) ⟨2041280, by rfl⟩ : syracuseStep 2721707 = 4082561) B4082561
theorem B161628185 : Blo 754331 161628185 := bstep (se 2 (by rfl) ⟨60610569, by rfl⟩ : syracuseStep 161628185 = 121221139) B121221139
theorem B1438879 : Blo 754331 1438879 := bstep (se 1 (by rfl) ⟨1079159, by rfl⟩ : syracuseStep 1438879 = 2158319) B2158319
theorem B6454079 : Blo 754331 6454079 := bstep (se 1 (by rfl) ⟨4840559, by rfl⟩ : syracuseStep 6454079 = 9681119) B9681119
theorem B1277039 : Blo 754331 1277039 := bstep (se 1 (by rfl) ⟨957779, by rfl⟩ : syracuseStep 1277039 = 1915559) B1915559
theorem B4302719 : Blo 754331 4302719 := bstep (se 1 (by rfl) ⟨3227039, by rfl⟩ : syracuseStep 4302719 = 6454079) B6454079
theorem B107752123 : Blo 754331 107752123 := bstep (se 1 (by rfl) ⟨80814092, by rfl⟩ : syracuseStep 107752123 = 161628185) B161628185
theorem B1814471 : Blo 754331 1814471 := bstep (se 1 (by rfl) ⟨1360853, by rfl⟩ : syracuseStep 1814471 = 2721707) B2721707
theorem B1918505 : Blo 754331 1918505 := bstep (se 2 (by rfl) ⟨719439, by rfl⟩ : syracuseStep 1918505 = 1438879) B1438879
theorem B851359 : Blo 754331 851359 := bstep (se 1 (by rfl) ⟨638519, by rfl⟩ : syracuseStep 851359 = 1277039) B1277039
theorem B1279003 : Blo 754331 1279003 := bstep (se 1 (by rfl) ⟨959252, by rfl⟩ : syracuseStep 1279003 = 1918505) B1918505
theorem B143669497 : Blo 754331 143669497 := bstep (se 2 (by rfl) ⟨53876061, by rfl⟩ : syracuseStep 143669497 = 107752123) B107752123
theorem B2868479 : Blo 754331 2868479 := bstep (se 1 (by rfl) ⟨2151359, by rfl⟩ : syracuseStep 2868479 = 4302719) B4302719
theorem B1135145 : Blo 754331 1135145 := bstep (se 2 (by rfl) ⟨425679, by rfl⟩ : syracuseStep 1135145 = 851359) B851359
theorem B1209647 : Blo 754331 1209647 := bstep (se 1 (by rfl) ⟨907235, by rfl⟩ : syracuseStep 1209647 = 1814471) B1814471
theorem B1705337 : Blo 754331 1705337 := bstep (se 2 (by rfl) ⟨639501, by rfl⟩ : syracuseStep 1705337 = 1279003) B1279003
theorem B756763 : Blo 754331 756763 := bstep (se 1 (by rfl) ⟨567572, by rfl⟩ : syracuseStep 756763 = 1135145) B1135145
theorem B1912319 : Blo 754331 1912319 := bstep (se 1 (by rfl) ⟨1434239, by rfl⟩ : syracuseStep 1912319 = 2868479) B2868479
theorem B806431 : Blo 754331 806431 := bstep (se 1 (by rfl) ⟨604823, by rfl⟩ : syracuseStep 806431 = 1209647) B1209647
theorem B191559329 : Blo 754331 191559329 := bstep (se 2 (by rfl) ⟨71834748, by rfl⟩ : syracuseStep 191559329 = 143669497) B143669497
theorem B127706219 : Blo 754331 127706219 := bstep (se 1 (by rfl) ⟨95779664, by rfl⟩ : syracuseStep 127706219 = 191559329) B191559329
theorem B1136891 : Blo 754331 1136891 := bstep (se 1 (by rfl) ⟨852668, by rfl⟩ : syracuseStep 1136891 = 1705337) B1705337
theorem B1075241 : Blo 754331 1075241 := bstep (se 2 (by rfl) ⟨403215, by rfl⟩ : syracuseStep 1075241 = 806431) B806431
theorem B1274879 : Blo 754331 1274879 := bstep (se 1 (by rfl) ⟨956159, by rfl⟩ : syracuseStep 1274879 = 1912319) B1912319
theorem B757927 : Blo 754331 757927 := bstep (se 1 (by rfl) ⟨568445, by rfl⟩ : syracuseStep 757927 = 1136891) B1136891
theorem B85137479 : Blo 754331 85137479 := bstep (se 1 (by rfl) ⟨63853109, by rfl⟩ : syracuseStep 85137479 = 127706219) B127706219
theorem B2867309 : Blo 754331 2867309 := bstep (se 3 (by rfl) ⟨537620, by rfl⟩ : syracuseStep 2867309 = 1075241) B1075241
theorem B849919 : Blo 754331 849919 := bstep (se 1 (by rfl) ⟨637439, by rfl⟩ : syracuseStep 849919 = 1274879) B1274879
theorem B56758319 : Blo 754331 56758319 := bstep (se 1 (by rfl) ⟨42568739, by rfl⟩ : syracuseStep 56758319 = 85137479) B85137479
theorem B1911539 : Blo 754331 1911539 := bstep (se 1 (by rfl) ⟨1433654, by rfl⟩ : syracuseStep 1911539 = 2867309) B2867309
theorem B1133225 : Blo 754331 1133225 := bstep (se 2 (by rfl) ⟨424959, by rfl⟩ : syracuseStep 1133225 = 849919) B849919
theorem B755483 : Blo 754331 755483 := bstep (se 1 (by rfl) ⟨566612, by rfl⟩ : syracuseStep 755483 = 1133225) B1133225
theorem B37838879 : Blo 754331 37838879 := bstep (se 1 (by rfl) ⟨28379159, by rfl⟩ : syracuseStep 37838879 = 56758319) B56758319
theorem B1274359 : Blo 754331 1274359 := bstep (se 1 (by rfl) ⟨955769, by rfl⟩ : syracuseStep 1274359 = 1911539) B1911539
theorem B25225919 : Blo 754331 25225919 := bstep (se 1 (by rfl) ⟨18919439, by rfl⟩ : syracuseStep 25225919 = 37838879) B37838879
theorem B1699145 : Blo 754331 1699145 := bstep (se 2 (by rfl) ⟨637179, by rfl⟩ : syracuseStep 1699145 = 1274359) B1274359
theorem B16817279 : Blo 754331 16817279 := bstep (se 1 (by rfl) ⟨12612959, by rfl⟩ : syracuseStep 16817279 = 25225919) B25225919
theorem B1132763 : Blo 754331 1132763 := bstep (se 1 (by rfl) ⟨849572, by rfl⟩ : syracuseStep 1132763 = 1699145) B1699145
theorem B755175 : Blo 754331 755175 := bstep (se 1 (by rfl) ⟨566381, by rfl⟩ : syracuseStep 755175 = 1132763) B1132763
theorem B44846077 : Blo 754331 44846077 := bstep (se 3 (by rfl) ⟨8408639, by rfl⟩ : syracuseStep 44846077 = 16817279) B16817279
theorem B59794769 : Blo 754331 59794769 := bstep (se 2 (by rfl) ⟨22423038, by rfl⟩ : syracuseStep 59794769 = 44846077) B44846077
theorem B39863179 : Blo 754331 39863179 := bstep (se 1 (by rfl) ⟨29897384, by rfl⟩ : syracuseStep 39863179 = 59794769) B59794769
theorem B53150905 : Blo 754331 53150905 := bstep (se 2 (by rfl) ⟨19931589, by rfl⟩ : syracuseStep 53150905 = 39863179) B39863179
theorem B70867873 : Blo 754331 70867873 := bstep (se 2 (by rfl) ⟨26575452, by rfl⟩ : syracuseStep 70867873 = 53150905) B53150905
theorem B94490497 : Blo 754331 94490497 := bstep (se 2 (by rfl) ⟨35433936, by rfl⟩ : syracuseStep 94490497 = 70867873) B70867873
theorem B125987329 : Blo 754331 125987329 := bstep (se 2 (by rfl) ⟨47245248, by rfl⟩ : syracuseStep 125987329 = 94490497) B94490497
theorem B167983105 : Blo 754331 167983105 := bstep (se 2 (by rfl) ⟨62993664, by rfl⟩ : syracuseStep 167983105 = 125987329) B125987329
theorem B223977473 : Blo 754331 223977473 := bstep (se 2 (by rfl) ⟨83991552, by rfl⟩ : syracuseStep 223977473 = 167983105) B167983105
theorem B149318315 : Blo 754331 149318315 := bstep (se 1 (by rfl) ⟨111988736, by rfl⟩ : syracuseStep 149318315 = 223977473) B223977473
theorem B99545543 : Blo 754331 99545543 := bstep (se 1 (by rfl) ⟨74659157, by rfl⟩ : syracuseStep 99545543 = 149318315) B149318315
theorem B66363695 : Blo 754331 66363695 := bstep (se 1 (by rfl) ⟨49772771, by rfl⟩ : syracuseStep 66363695 = 99545543) B99545543
theorem B44242463 : Blo 754331 44242463 := bstep (se 1 (by rfl) ⟨33181847, by rfl⟩ : syracuseStep 44242463 = 66363695) B66363695
theorem B117979901 : Blo 754331 117979901 := bstep (se 3 (by rfl) ⟨22121231, by rfl⟩ : syracuseStep 117979901 = 44242463) B44242463
theorem B78653267 : Blo 754331 78653267 := bstep (se 1 (by rfl) ⟨58989950, by rfl⟩ : syracuseStep 78653267 = 117979901) B117979901
theorem B52435511 : Blo 754331 52435511 := bstep (se 1 (by rfl) ⟨39326633, by rfl⟩ : syracuseStep 52435511 = 78653267) B78653267
theorem B34957007 : Blo 754331 34957007 := bstep (se 1 (by rfl) ⟨26217755, by rfl⟩ : syracuseStep 34957007 = 52435511) B52435511
theorem B23304671 : Blo 754331 23304671 := bstep (se 1 (by rfl) ⟨17478503, by rfl⟩ : syracuseStep 23304671 = 34957007) B34957007
theorem B15536447 : Blo 754331 15536447 := bstep (se 1 (by rfl) ⟨11652335, by rfl⟩ : syracuseStep 15536447 = 23304671) B23304671
theorem B10357631 : Blo 754331 10357631 := bstep (se 1 (by rfl) ⟨7768223, by rfl⟩ : syracuseStep 10357631 = 15536447) B15536447
theorem B6905087 : Blo 754331 6905087 := bstep (se 1 (by rfl) ⟨5178815, by rfl⟩ : syracuseStep 6905087 = 10357631) B10357631
theorem B4603391 : Blo 754331 4603391 := bstep (se 1 (by rfl) ⟨3452543, by rfl⟩ : syracuseStep 4603391 = 6905087) B6905087
theorem B3068927 : Blo 754331 3068927 := bstep (se 1 (by rfl) ⟨2301695, by rfl⟩ : syracuseStep 3068927 = 4603391) B4603391
theorem B2045951 : Blo 754331 2045951 := bstep (se 1 (by rfl) ⟨1534463, by rfl⟩ : syracuseStep 2045951 = 3068927) B3068927
theorem B1363967 : Blo 754331 1363967 := bstep (se 1 (by rfl) ⟨1022975, by rfl⟩ : syracuseStep 1363967 = 2045951) B2045951
theorem B909311 : Blo 754331 909311 := bstep (se 1 (by rfl) ⟨681983, by rfl⟩ : syracuseStep 909311 = 1363967) B1363967
theorem B2424829 : Blo 754331 2424829 := bstep (se 3 (by rfl) ⟨454655, by rfl⟩ : syracuseStep 2424829 = 909311) B909311
theorem B3233105 : Blo 754331 3233105 := bstep (se 2 (by rfl) ⟨1212414, by rfl⟩ : syracuseStep 3233105 = 2424829) B2424829
theorem B2155403 : Blo 754331 2155403 := bstep (se 1 (by rfl) ⟨1616552, by rfl⟩ : syracuseStep 2155403 = 3233105) B3233105
theorem B1436935 : Blo 754331 1436935 := bstep (se 1 (by rfl) ⟨1077701, by rfl⟩ : syracuseStep 1436935 = 2155403) B2155403
theorem B1915913 : Blo 754331 1915913 := bstep (se 2 (by rfl) ⟨718467, by rfl⟩ : syracuseStep 1915913 = 1436935) B1436935
theorem B1277275 : Blo 754331 1277275 := bstep (se 1 (by rfl) ⟨957956, by rfl⟩ : syracuseStep 1277275 = 1915913) B1915913
theorem B1703033 : Blo 754331 1703033 := bstep (se 2 (by rfl) ⟨638637, by rfl⟩ : syracuseStep 1703033 = 1277275) B1277275
theorem B1135355 : Blo 754331 1135355 := bstep (se 1 (by rfl) ⟨851516, by rfl⟩ : syracuseStep 1135355 = 1703033) B1703033
theorem B756903 : Blo 754331 756903 := bstep (se 1 (by rfl) ⟨567677, by rfl⟩ : syracuseStep 756903 = 1135355) B1135355

theorem C0 (j : ℕ) (h1 : 188582 ≤ j) (h2 : j ≤ 189281) : Blo 754331 (4 * j + 3) := by
  interval_cases j
  · exact B754331
  · exact B754335
  · exact B754339
  · exact B754343
  · exact B754347
  · exact B754351
  · exact B754355
  · exact B754359
  · exact B754363
  · exact B754367
  · exact B754371
  · exact B754375
  · exact B754379
  · exact B754383
  · exact B754387
  · exact B754391
  · exact B754395
  · exact B754399
  · exact B754403
  · exact B754407
  · exact B754411
  · exact B754415
  · exact B754419
  · exact B754423
  · exact B754427
  · exact B754431
  · exact B754435
  · exact B754439
  · exact B754443
  · exact B754447
  · exact B754451
  · exact B754455
  · exact B754459
  · exact B754463
  · exact B754467
  · exact B754471
  · exact B754475
  · exact B754479
  · exact B754483
  · exact B754487
  · exact B754491
  · exact B754495
  · exact B754499
  · exact B754503
  · exact B754507
  · exact B754511
  · exact B754515
  · exact B754519
  · exact B754523
  · exact B754527
  · exact B754531
  · exact B754535
  · exact B754539
  · exact B754543
  · exact B754547
  · exact B754551
  · exact B754555
  · exact B754559
  · exact B754563
  · exact B754567
  · exact B754571
  · exact B754575
  · exact B754579
  · exact B754583
  · exact B754587
  · exact B754591
  · exact B754595
  · exact B754599
  · exact B754603
  · exact B754607
  · exact B754611
  · exact B754615
  · exact B754619
  · exact B754623
  · exact B754627
  · exact B754631
  · exact B754635
  · exact B754639
  · exact B754643
  · exact B754647
  · exact B754651
  · exact B754655
  · exact B754659
  · exact B754663
  · exact B754667
  · exact B754671
  · exact B754675
  · exact B754679
  · exact B754683
  · exact B754687
  · exact B754691
  · exact B754695
  · exact B754699
  · exact B754703
  · exact B754707
  · exact B754711
  · exact B754715
  · exact B754719
  · exact B754723
  · exact B754727
  · exact B754731
  · exact B754735
  · exact B754739
  · exact B754743
  · exact B754747
  · exact B754751
  · exact B754755
  · exact B754759
  · exact B754763
  · exact B754767
  · exact B754771
  · exact B754775
  · exact B754779
  · exact B754783
  · exact B754787
  · exact B754791
  · exact B754795
  · exact B754799
  · exact B754803
  · exact B754807
  · exact B754811
  · exact B754815
  · exact B754819
  · exact B754823
  · exact B754827
  · exact B754831
  · exact B754835
  · exact B754839
  · exact B754843
  · exact B754847
  · exact B754851
  · exact B754855
  · exact B754859
  · exact B754863
  · exact B754867
  · exact B754871
  · exact B754875
  · exact B754879
  · exact B754883
  · exact B754887
  · exact B754891
  · exact B754895
  · exact B754899
  · exact B754903
  · exact B754907
  · exact B754911
  · exact B754915
  · exact B754919
  · exact B754923
  · exact B754927
  · exact B754931
  · exact B754935
  · exact B754939
  · exact B754943
  · exact B754947
  · exact B754951
  · exact B754955
  · exact B754959
  · exact B754963
  · exact B754967
  · exact B754971
  · exact B754975
  · exact B754979
  · exact B754983
  · exact B754987
  · exact B754991
  · exact B754995
  · exact B754999
  · exact B755003
  · exact B755007
  · exact B755011
  · exact B755015
  · exact B755019
  · exact B755023
  · exact B755027
  · exact B755031
  · exact B755035
  · exact B755039
  · exact B755043
  · exact B755047
  · exact B755051
  · exact B755055
  · exact B755059
  · exact B755063
  · exact B755067
  · exact B755071
  · exact B755075
  · exact B755079
  · exact B755083
  · exact B755087
  · exact B755091
  · exact B755095
  · exact B755099
  · exact B755103
  · exact B755107
  · exact B755111
  · exact B755115
  · exact B755119
  · exact B755123
  · exact B755127
  · exact B755131
  · exact B755135
  · exact B755139
  · exact B755143
  · exact B755147
  · exact B755151
  · exact B755155
  · exact B755159
  · exact B755163
  · exact B755167
  · exact B755171
  · exact B755175
  · exact B755179
  · exact B755183
  · exact B755187
  · exact B755191
  · exact B755195
  · exact B755199
  · exact B755203
  · exact B755207
  · exact B755211
  · exact B755215
  · exact B755219
  · exact B755223
  · exact B755227
  · exact B755231
  · exact B755235
  · exact B755239
  · exact B755243
  · exact B755247
  · exact B755251
  · exact B755255
  · exact B755259
  · exact B755263
  · exact B755267
  · exact B755271
  · exact B755275
  · exact B755279
  · exact B755283
  · exact B755287
  · exact B755291
  · exact B755295
  · exact B755299
  · exact B755303
  · exact B755307
  · exact B755311
  · exact B755315
  · exact B755319
  · exact B755323
  · exact B755327
  · exact B755331
  · exact B755335
  · exact B755339
  · exact B755343
  · exact B755347
  · exact B755351
  · exact B755355
  · exact B755359
  · exact B755363
  · exact B755367
  · exact B755371
  · exact B755375
  · exact B755379
  · exact B755383
  · exact B755387
  · exact B755391
  · exact B755395
  · exact B755399
  · exact B755403
  · exact B755407
  · exact B755411
  · exact B755415
  · exact B755419
  · exact B755423
  · exact B755427
  · exact B755431
  · exact B755435
  · exact B755439
  · exact B755443
  · exact B755447
  · exact B755451
  · exact B755455
  · exact B755459
  · exact B755463
  · exact B755467
  · exact B755471
  · exact B755475
  · exact B755479
  · exact B755483
  · exact B755487
  · exact B755491
  · exact B755495
  · exact B755499
  · exact B755503
  · exact B755507
  · exact B755511
  · exact B755515
  · exact B755519
  · exact B755523
  · exact B755527
  · exact B755531
  · exact B755535
  · exact B755539
  · exact B755543
  · exact B755547
  · exact B755551
  · exact B755555
  · exact B755559
  · exact B755563
  · exact B755567
  · exact B755571
  · exact B755575
  · exact B755579
  · exact B755583
  · exact B755587
  · exact B755591
  · exact B755595
  · exact B755599
  · exact B755603
  · exact B755607
  · exact B755611
  · exact B755615
  · exact B755619
  · exact B755623
  · exact B755627
  · exact B755631
  · exact B755635
  · exact B755639
  · exact B755643
  · exact B755647
  · exact B755651
  · exact B755655
  · exact B755659
  · exact B755663
  · exact B755667
  · exact B755671
  · exact B755675
  · exact B755679
  · exact B755683
  · exact B755687
  · exact B755691
  · exact B755695
  · exact B755699
  · exact B755703
  · exact B755707
  · exact B755711
  · exact B755715
  · exact B755719
  · exact B755723
  · exact B755727
  · exact B755731
  · exact B755735
  · exact B755739
  · exact B755743
  · exact B755747
  · exact B755751
  · exact B755755
  · exact B755759
  · exact B755763
  · exact B755767
  · exact B755771
  · exact B755775
  · exact B755779
  · exact B755783
  · exact B755787
  · exact B755791
  · exact B755795
  · exact B755799
  · exact B755803
  · exact B755807
  · exact B755811
  · exact B755815
  · exact B755819
  · exact B755823
  · exact B755827
  · exact B755831
  · exact B755835
  · exact B755839
  · exact B755843
  · exact B755847
  · exact B755851
  · exact B755855
  · exact B755859
  · exact B755863
  · exact B755867
  · exact B755871
  · exact B755875
  · exact B755879
  · exact B755883
  · exact B755887
  · exact B755891
  · exact B755895
  · exact B755899
  · exact B755903
  · exact B755907
  · exact B755911
  · exact B755915
  · exact B755919
  · exact B755923
  · exact B755927
  · exact B755931
  · exact B755935
  · exact B755939
  · exact B755943
  · exact B755947
  · exact B755951
  · exact B755955
  · exact B755959
  · exact B755963
  · exact B755967
  · exact B755971
  · exact B755975
  · exact B755979
  · exact B755983
  · exact B755987
  · exact B755991
  · exact B755995
  · exact B755999
  · exact B756003
  · exact B756007
  · exact B756011
  · exact B756015
  · exact B756019
  · exact B756023
  · exact B756027
  · exact B756031
  · exact B756035
  · exact B756039
  · exact B756043
  · exact B756047
  · exact B756051
  · exact B756055
  · exact B756059
  · exact B756063
  · exact B756067
  · exact B756071
  · exact B756075
  · exact B756079
  · exact B756083
  · exact B756087
  · exact B756091
  · exact B756095
  · exact B756099
  · exact B756103
  · exact B756107
  · exact B756111
  · exact B756115
  · exact B756119
  · exact B756123
  · exact B756127
  · exact B756131
  · exact B756135
  · exact B756139
  · exact B756143
  · exact B756147
  · exact B756151
  · exact B756155
  · exact B756159
  · exact B756163
  · exact B756167
  · exact B756171
  · exact B756175
  · exact B756179
  · exact B756183
  · exact B756187
  · exact B756191
  · exact B756195
  · exact B756199
  · exact B756203
  · exact B756207
  · exact B756211
  · exact B756215
  · exact B756219
  · exact B756223
  · exact B756227
  · exact B756231
  · exact B756235
  · exact B756239
  · exact B756243
  · exact B756247
  · exact B756251
  · exact B756255
  · exact B756259
  · exact B756263
  · exact B756267
  · exact B756271
  · exact B756275
  · exact B756279
  · exact B756283
  · exact B756287
  · exact B756291
  · exact B756295
  · exact B756299
  · exact B756303
  · exact B756307
  · exact B756311
  · exact B756315
  · exact B756319
  · exact B756323
  · exact B756327
  · exact B756331
  · exact B756335
  · exact B756339
  · exact B756343
  · exact B756347
  · exact B756351
  · exact B756355
  · exact B756359
  · exact B756363
  · exact B756367
  · exact B756371
  · exact B756375
  · exact B756379
  · exact B756383
  · exact B756387
  · exact B756391
  · exact B756395
  · exact B756399
  · exact B756403
  · exact B756407
  · exact B756411
  · exact B756415
  · exact B756419
  · exact B756423
  · exact B756427
  · exact B756431
  · exact B756435
  · exact B756439
  · exact B756443
  · exact B756447
  · exact B756451
  · exact B756455
  · exact B756459
  · exact B756463
  · exact B756467
  · exact B756471
  · exact B756475
  · exact B756479
  · exact B756483
  · exact B756487
  · exact B756491
  · exact B756495
  · exact B756499
  · exact B756503
  · exact B756507
  · exact B756511
  · exact B756515
  · exact B756519
  · exact B756523
  · exact B756527
  · exact B756531
  · exact B756535
  · exact B756539
  · exact B756543
  · exact B756547
  · exact B756551
  · exact B756555
  · exact B756559
  · exact B756563
  · exact B756567
  · exact B756571
  · exact B756575
  · exact B756579
  · exact B756583
  · exact B756587
  · exact B756591
  · exact B756595
  · exact B756599
  · exact B756603
  · exact B756607
  · exact B756611
  · exact B756615
  · exact B756619
  · exact B756623
  · exact B756627
  · exact B756631
  · exact B756635
  · exact B756639
  · exact B756643
  · exact B756647
  · exact B756651
  · exact B756655
  · exact B756659
  · exact B756663
  · exact B756667
  · exact B756671
  · exact B756675
  · exact B756679
  · exact B756683
  · exact B756687
  · exact B756691
  · exact B756695
  · exact B756699
  · exact B756703
  · exact B756707
  · exact B756711
  · exact B756715
  · exact B756719
  · exact B756723
  · exact B756727
  · exact B756731
  · exact B756735
  · exact B756739
  · exact B756743
  · exact B756747
  · exact B756751
  · exact B756755
  · exact B756759
  · exact B756763
  · exact B756767
  · exact B756771
  · exact B756775
  · exact B756779
  · exact B756783
  · exact B756787
  · exact B756791
  · exact B756795
  · exact B756799
  · exact B756803
  · exact B756807
  · exact B756811
  · exact B756815
  · exact B756819
  · exact B756823
  · exact B756827
  · exact B756831
  · exact B756835
  · exact B756839
  · exact B756843
  · exact B756847
  · exact B756851
  · exact B756855
  · exact B756859
  · exact B756863
  · exact B756867
  · exact B756871
  · exact B756875
  · exact B756879
  · exact B756883
  · exact B756887
  · exact B756891
  · exact B756895
  · exact B756899
  · exact B756903
  · exact B756907
  · exact B756911
  · exact B756915
  · exact B756919
  · exact B756923
  · exact B756927
  · exact B756931
  · exact B756935
  · exact B756939
  · exact B756943
  · exact B756947
  · exact B756951
  · exact B756955
  · exact B756959
  · exact B756963
  · exact B756967
  · exact B756971
  · exact B756975
  · exact B756979
  · exact B756983
  · exact B756987
  · exact B756991
  · exact B756995
  · exact B756999
  · exact B757003
  · exact B757007
  · exact B757011
  · exact B757015
  · exact B757019
  · exact B757023
  · exact B757027
  · exact B757031
  · exact B757035
  · exact B757039
  · exact B757043
  · exact B757047
  · exact B757051
  · exact B757055
  · exact B757059
  · exact B757063
  · exact B757067
  · exact B757071
  · exact B757075
  · exact B757079
  · exact B757083
  · exact B757087
  · exact B757091
  · exact B757095
  · exact B757099
  · exact B757103
  · exact B757107
  · exact B757111
  · exact B757115
  · exact B757119
  · exact B757123
  · exact B757127

theorem C1 (j : ℕ) (h1 : 189282 ≤ j) (h2 : j ≤ 189582) : Blo 754331 (4 * j + 3) := by
  interval_cases j
  · exact B757131
  · exact B757135
  · exact B757139
  · exact B757143
  · exact B757147
  · exact B757151
  · exact B757155
  · exact B757159
  · exact B757163
  · exact B757167
  · exact B757171
  · exact B757175
  · exact B757179
  · exact B757183
  · exact B757187
  · exact B757191
  · exact B757195
  · exact B757199
  · exact B757203
  · exact B757207
  · exact B757211
  · exact B757215
  · exact B757219
  · exact B757223
  · exact B757227
  · exact B757231
  · exact B757235
  · exact B757239
  · exact B757243
  · exact B757247
  · exact B757251
  · exact B757255
  · exact B757259
  · exact B757263
  · exact B757267
  · exact B757271
  · exact B757275
  · exact B757279
  · exact B757283
  · exact B757287
  · exact B757291
  · exact B757295
  · exact B757299
  · exact B757303
  · exact B757307
  · exact B757311
  · exact B757315
  · exact B757319
  · exact B757323
  · exact B757327
  · exact B757331
  · exact B757335
  · exact B757339
  · exact B757343
  · exact B757347
  · exact B757351
  · exact B757355
  · exact B757359
  · exact B757363
  · exact B757367
  · exact B757371
  · exact B757375
  · exact B757379
  · exact B757383
  · exact B757387
  · exact B757391
  · exact B757395
  · exact B757399
  · exact B757403
  · exact B757407
  · exact B757411
  · exact B757415
  · exact B757419
  · exact B757423
  · exact B757427
  · exact B757431
  · exact B757435
  · exact B757439
  · exact B757443
  · exact B757447
  · exact B757451
  · exact B757455
  · exact B757459
  · exact B757463
  · exact B757467
  · exact B757471
  · exact B757475
  · exact B757479
  · exact B757483
  · exact B757487
  · exact B757491
  · exact B757495
  · exact B757499
  · exact B757503
  · exact B757507
  · exact B757511
  · exact B757515
  · exact B757519
  · exact B757523
  · exact B757527
  · exact B757531
  · exact B757535
  · exact B757539
  · exact B757543
  · exact B757547
  · exact B757551
  · exact B757555
  · exact B757559
  · exact B757563
  · exact B757567
  · exact B757571
  · exact B757575
  · exact B757579
  · exact B757583
  · exact B757587
  · exact B757591
  · exact B757595
  · exact B757599
  · exact B757603
  · exact B757607
  · exact B757611
  · exact B757615
  · exact B757619
  · exact B757623
  · exact B757627
  · exact B757631
  · exact B757635
  · exact B757639
  · exact B757643
  · exact B757647
  · exact B757651
  · exact B757655
  · exact B757659
  · exact B757663
  · exact B757667
  · exact B757671
  · exact B757675
  · exact B757679
  · exact B757683
  · exact B757687
  · exact B757691
  · exact B757695
  · exact B757699
  · exact B757703
  · exact B757707
  · exact B757711
  · exact B757715
  · exact B757719
  · exact B757723
  · exact B757727
  · exact B757731
  · exact B757735
  · exact B757739
  · exact B757743
  · exact B757747
  · exact B757751
  · exact B757755
  · exact B757759
  · exact B757763
  · exact B757767
  · exact B757771
  · exact B757775
  · exact B757779
  · exact B757783
  · exact B757787
  · exact B757791
  · exact B757795
  · exact B757799
  · exact B757803
  · exact B757807
  · exact B757811
  · exact B757815
  · exact B757819
  · exact B757823
  · exact B757827
  · exact B757831
  · exact B757835
  · exact B757839
  · exact B757843
  · exact B757847
  · exact B757851
  · exact B757855
  · exact B757859
  · exact B757863
  · exact B757867
  · exact B757871
  · exact B757875
  · exact B757879
  · exact B757883
  · exact B757887
  · exact B757891
  · exact B757895
  · exact B757899
  · exact B757903
  · exact B757907
  · exact B757911
  · exact B757915
  · exact B757919
  · exact B757923
  · exact B757927
  · exact B757931
  · exact B757935
  · exact B757939
  · exact B757943
  · exact B757947
  · exact B757951
  · exact B757955
  · exact B757959
  · exact B757963
  · exact B757967
  · exact B757971
  · exact B757975
  · exact B757979
  · exact B757983
  · exact B757987
  · exact B757991
  · exact B757995
  · exact B757999
  · exact B758003
  · exact B758007
  · exact B758011
  · exact B758015
  · exact B758019
  · exact B758023
  · exact B758027
  · exact B758031
  · exact B758035
  · exact B758039
  · exact B758043
  · exact B758047
  · exact B758051
  · exact B758055
  · exact B758059
  · exact B758063
  · exact B758067
  · exact B758071
  · exact B758075
  · exact B758079
  · exact B758083
  · exact B758087
  · exact B758091
  · exact B758095
  · exact B758099
  · exact B758103
  · exact B758107
  · exact B758111
  · exact B758115
  · exact B758119
  · exact B758123
  · exact B758127
  · exact B758131
  · exact B758135
  · exact B758139
  · exact B758143
  · exact B758147
  · exact B758151
  · exact B758155
  · exact B758159
  · exact B758163
  · exact B758167
  · exact B758171
  · exact B758175
  · exact B758179
  · exact B758183
  · exact B758187
  · exact B758191
  · exact B758195
  · exact B758199
  · exact B758203
  · exact B758207
  · exact B758211
  · exact B758215
  · exact B758219
  · exact B758223
  · exact B758227
  · exact B758231
  · exact B758235
  · exact B758239
  · exact B758243
  · exact B758247
  · exact B758251
  · exact B758255
  · exact B758259
  · exact B758263
  · exact B758267
  · exact B758271
  · exact B758275
  · exact B758279
  · exact B758283
  · exact B758287
  · exact B758291
  · exact B758295
  · exact B758299
  · exact B758303
  · exact B758307
  · exact B758311
  · exact B758315
  · exact B758319
  · exact B758323
  · exact B758327
  · exact B758331

theorem solution (m : ℕ) (hlo : 754331 ≤ m) (hhi : m ≤ 758331) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 188582 ≤ j := by omega
    have hj2 : j ≤ 189582 := by omega
    have hb : Blo 754331 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 189282 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
