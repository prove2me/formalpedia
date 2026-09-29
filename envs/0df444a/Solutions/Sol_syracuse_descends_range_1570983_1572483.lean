-- Prove2me | solution 1 for syracuse_descends_range_1570983_1572483
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:07:02.844915+00:00
-- url     : https://prove2.me/submissions/6fcff23e-3ac2-4a9e-a839-deb7455e204b

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


theorem B4145237 : Blo 1570983 4145237 := bbase (se 8 (by rfl) ⟨24288, by rfl⟩ : syracuseStep 4145237 = 48577) (by norm_num)
theorem B3776669 : Blo 1570983 3776669 := bbase (se 3 (by rfl) ⟨708125, by rfl⟩ : syracuseStep 3776669 = 1416251) (by norm_num)
theorem B30613717 : Blo 1570983 30613717 := bbase (se 7 (by rfl) ⟨358754, by rfl⟩ : syracuseStep 30613717 = 717509) (by norm_num)
theorem B3236069 : Blo 1570983 3236069 := bbase (se 4 (by rfl) ⟨303381, by rfl⟩ : syracuseStep 3236069 = 606763) (by norm_num)
theorem B4538693 : Blo 1570983 4538693 := bbase (se 4 (by rfl) ⟨425502, by rfl⟩ : syracuseStep 4538693 = 851005) (by norm_num)
theorem B2687357 : Blo 1570983 2687357 := bbase (se 3 (by rfl) ⟨503879, by rfl⟩ : syracuseStep 2687357 = 1007759) (by norm_num)
theorem B2237005 : Blo 1570983 2237005 := bbase (se 3 (by rfl) ⟨419438, by rfl⟩ : syracuseStep 2237005 = 838877) (by norm_num)
theorem B5374549 : Blo 1570983 5374549 := bbase (se 8 (by rfl) ⟨31491, by rfl⟩ : syracuseStep 5374549 = 62983) (by norm_num)
theorem B3023477 : Blo 1570983 3023477 := bbase (se 5 (by rfl) ⟨141725, by rfl⟩ : syracuseStep 3023477 = 283451) (by norm_num)
theorem B2982757 : Blo 1570983 2982757 := bbase (se 4 (by rfl) ⟨279633, by rfl⟩ : syracuseStep 2982757 = 559267) (by norm_num)
theorem B7955333 : Blo 1570983 7955333 := bbase (se 4 (by rfl) ⟨745812, by rfl⟩ : syracuseStep 7955333 = 1491625) (by norm_num)
theorem B3777445 : Blo 1570983 3777445 := bbase (se 4 (by rfl) ⟨354135, by rfl⟩ : syracuseStep 3777445 = 708271) (by norm_num)
theorem B2982901 : Blo 1570983 2982901 := bbase (se 5 (by rfl) ⟨139823, by rfl⟩ : syracuseStep 2982901 = 279647) (by norm_num)
theorem B2688013 : Blo 1570983 2688013 := bbase (se 3 (by rfl) ⟨504002, by rfl⟩ : syracuseStep 2688013 = 1008005) (by norm_num)
theorem B7169093 : Blo 1570983 7169093 := bbase (se 4 (by rfl) ⟨672102, by rfl⟩ : syracuseStep 7169093 = 1344205) (by norm_num)
theorem B2983061 : Blo 1570983 2983061 := bbase (se 6 (by rfl) ⟨69915, by rfl⟩ : syracuseStep 2983061 = 139831) (by norm_num)
theorem B7570613 : Blo 1570983 7570613 := bbase (se 5 (by rfl) ⟨354872, by rfl⟩ : syracuseStep 7570613 = 709745) (by norm_num)
theorem B11330837 : Blo 1570983 11330837 := bbase (se 6 (by rfl) ⟨265566, by rfl⟩ : syracuseStep 11330837 = 531133) (by norm_num)
theorem B2983205 : Blo 1570983 2983205 := bbase (se 4 (by rfl) ⟨279675, by rfl⟩ : syracuseStep 2983205 = 559351) (by norm_num)
theorem B12739925 : Blo 1570983 12739925 := bbase (se 12 (by rfl) ⟨4665, by rfl⟩ : syracuseStep 12739925 = 9331) (by norm_num)
theorem B2237797 : Blo 1570983 2237797 := bbase (se 4 (by rfl) ⟨209793, by rfl⟩ : syracuseStep 2237797 = 419587) (by norm_num)
theorem B5662133 : Blo 1570983 5662133 := bbase (se 5 (by rfl) ⟨265412, by rfl⟩ : syracuseStep 5662133 = 530825) (by norm_num)
theorem B5965285 : Blo 1570983 5965285 := bbase (se 4 (by rfl) ⟨559245, by rfl⟩ : syracuseStep 5965285 = 1118491) (by norm_num)
theorem B2983493 : Blo 1570983 2983493 := bbase (se 4 (by rfl) ⟨279702, by rfl⟩ : syracuseStep 2983493 = 559405) (by norm_num)
theorem B3778157 : Blo 1570983 3778157 := bbase (se 3 (by rfl) ⟨708404, by rfl⟩ : syracuseStep 3778157 = 1416809) (by norm_num)
theorem B2123381 : Blo 1570983 2123381 := bbase (se 5 (by rfl) ⟨99533, by rfl⟩ : syracuseStep 2123381 = 199067) (by norm_num)
theorem B2123429 : Blo 1570983 2123429 := bbase (se 4 (by rfl) ⟨199071, by rfl⟩ : syracuseStep 2123429 = 398143) (by norm_num)
theorem B8947381 : Blo 1570983 8947381 := bbase (se 5 (by rfl) ⟨419408, by rfl⟩ : syracuseStep 8947381 = 838817) (by norm_num)
theorem B2238133 : Blo 1570983 2238133 := bbase (se 5 (by rfl) ⟨104912, by rfl⟩ : syracuseStep 2238133 = 209825) (by norm_num)
theorem B2983645 : Blo 1570983 2983645 := bbase (se 3 (by rfl) ⟨559433, by rfl⟩ : syracuseStep 2983645 = 1118867) (by norm_num)
theorem B5965589 : Blo 1570983 5965589 := bbase (se 6 (by rfl) ⟨139818, by rfl⟩ : syracuseStep 5965589 = 279637) (by norm_num)
theorem B4474693 : Blo 1570983 4474693 := bbase (se 4 (by rfl) ⟨419502, by rfl⟩ : syracuseStep 4474693 = 839005) (by norm_num)
theorem B11331413 : Blo 1570983 11331413 := bbase (se 9 (by rfl) ⟨33197, by rfl⟩ : syracuseStep 11331413 = 66395) (by norm_num)
theorem B4843397 : Blo 1570983 4843397 := bbase (se 4 (by rfl) ⟨454068, by rfl⟩ : syracuseStep 4843397 = 908137) (by norm_num)
theorem B2238349 : Blo 1570983 2238349 := bbase (se 3 (by rfl) ⟨419690, by rfl⟩ : syracuseStep 2238349 = 839381) (by norm_num)
theorem B5662709 : Blo 1570983 5662709 := bbase (se 5 (by rfl) ⟨265439, by rfl⟩ : syracuseStep 5662709 = 530879) (by norm_num)
theorem B2983949 : Blo 1570983 2983949 := bbase (se 3 (by rfl) ⟨559490, by rfl⟩ : syracuseStep 2983949 = 1118981) (by norm_num)
theorem B38226005 : Blo 1570983 38226005 := bbase (se 8 (by rfl) ⟨223980, by rfl⟩ : syracuseStep 38226005 = 447961) (by norm_num)
theorem B5302421 : Blo 1570983 5302421 := bbase (se 6 (by rfl) ⟨124275, by rfl⟩ : syracuseStep 5302421 = 248551) (by norm_num)
theorem B7956629 : Blo 1570983 7956629 := bbase (se 6 (by rfl) ⟨186483, by rfl⟩ : syracuseStep 7956629 = 372967) (by norm_num)
theorem B6711493 : Blo 1570983 6711493 := bbase (se 4 (by rfl) ⟨629202, by rfl⟩ : syracuseStep 6711493 = 1258405) (by norm_num)
theorem B2124013 : Blo 1570983 2124013 := bbase (se 3 (by rfl) ⟨398252, by rfl⟩ : syracuseStep 2124013 = 796505) (by norm_num)
theorem B2238725 : Blo 1570983 2238725 := bbase (se 4 (by rfl) ⟨209880, by rfl⟩ : syracuseStep 2238725 = 419761) (by norm_num)
theorem B8284565 : Blo 1570983 8284565 := bbase (se 6 (by rfl) ⟨194169, by rfl⟩ : syracuseStep 8284565 = 388339) (by norm_num)
theorem B4032965 : Blo 1570983 4032965 := bbase (se 4 (by rfl) ⟨378090, by rfl⟩ : syracuseStep 4032965 = 756181) (by norm_num)
theorem B5302853 : Blo 1570983 5302853 := bbase (se 4 (by rfl) ⟨497142, by rfl⟩ : syracuseStep 5302853 = 994285) (by norm_num)
theorem B3025493 : Blo 1570983 3025493 := bbase (se 8 (by rfl) ⟨17727, by rfl⟩ : syracuseStep 3025493 = 35455) (by norm_num)
theorem B2517733 : Blo 1570983 2517733 := bbase (se 4 (by rfl) ⟨236037, by rfl⟩ : syracuseStep 2517733 = 472075) (by norm_num)
theorem B2984701 : Blo 1570983 2984701 := bbase (se 3 (by rfl) ⟨559631, by rfl⟩ : syracuseStep 2984701 = 1119263) (by norm_num)
theorem B5376901 : Blo 1570983 5376901 := bbase (se 4 (by rfl) ⟨504084, by rfl⟩ : syracuseStep 5376901 = 1008169) (by norm_num)
theorem B2984845 : Blo 1570983 2984845 := bbase (se 3 (by rfl) ⟨559658, by rfl⟩ : syracuseStep 2984845 = 1119317) (by norm_num)
theorem B8063957 : Blo 1570983 8063957 := bbase (se 7 (by rfl) ⟨94499, by rfl⟩ : syracuseStep 8063957 = 188999) (by norm_num)
theorem B5303285 : Blo 1570983 5303285 := bbase (se 5 (by rfl) ⟨248591, by rfl⟩ : syracuseStep 5303285 = 497183) (by norm_num)
theorem B2985005 : Blo 1570983 2985005 := bbase (se 3 (by rfl) ⟨559688, by rfl⟩ : syracuseStep 2985005 = 1119377) (by norm_num)
theorem B5663861 : Blo 1570983 5663861 := bbase (se 5 (by rfl) ⟨265493, by rfl⟩ : syracuseStep 5663861 = 530987) (by norm_num)
theorem B2985149 : Blo 1570983 2985149 := bbase (se 3 (by rfl) ⟨559715, by rfl⟩ : syracuseStep 2985149 = 1119431) (by norm_num)
theorem B10071317 : Blo 1570983 10071317 := bbase (se 6 (by rfl) ⟨236046, by rfl⟩ : syracuseStep 10071317 = 472093) (by norm_num)
theorem B4476197 : Blo 1570983 4476197 := bbase (se 4 (by rfl) ⟨419643, by rfl⟩ : syracuseStep 4476197 = 839287) (by norm_num)
theorem B3976573 : Blo 1570983 3976573 := bbase (se 3 (by rfl) ⟨745607, by rfl⟩ : syracuseStep 3976573 = 1491215) (by norm_num)
theorem B5303717 : Blo 1570983 5303717 := bbase (se 4 (by rfl) ⟨497223, by rfl⟩ : syracuseStep 5303717 = 994447) (by norm_num)
theorem B7957925 : Blo 1570983 7957925 := bbase (se 4 (by rfl) ⟨746055, by rfl⟩ : syracuseStep 7957925 = 1492111) (by norm_num)
theorem B2518445 : Blo 1570983 2518445 := bbase (se 3 (by rfl) ⟨472208, by rfl⟩ : syracuseStep 2518445 = 944417) (by norm_num)
theorem B3976685 : Blo 1570983 3976685 := bbase (se 3 (by rfl) ⟨745628, by rfl⟩ : syracuseStep 3976685 = 1491257) (by norm_num)
theorem B1887781 : Blo 1570983 1887781 := bbase (se 4 (by rfl) ⟨176979, by rfl⟩ : syracuseStep 1887781 = 353959) (by norm_num)
theorem B8949365 : Blo 1570983 8949365 := bbase (se 5 (by rfl) ⟨419501, by rfl⟩ : syracuseStep 8949365 = 839003) (by norm_num)
theorem B3976877 : Blo 1570983 3976877 := bbase (se 3 (by rfl) ⟨745664, by rfl⟩ : syracuseStep 3976877 = 1491329) (by norm_num)
theorem B4034317 : Blo 1570983 4034317 := bbase (se 3 (by rfl) ⟨756434, by rfl⟩ : syracuseStep 4034317 = 1512869) (by norm_num)
theorem B5304149 : Blo 1570983 5304149 := bbase (se 9 (by rfl) ⟨15539, by rfl⟩ : syracuseStep 5304149 = 31079) (by norm_num)
theorem B5967701 : Blo 1570983 5967701 := bbase (se 9 (by rfl) ⟨17483, by rfl⟩ : syracuseStep 5967701 = 34967) (by norm_num)
theorem B3534749 : Blo 1570983 3534749 := bbase (se 3 (by rfl) ⟨662765, by rfl⟩ : syracuseStep 3534749 = 1325531) (by norm_num)
theorem B3534821 : Blo 1570983 3534821 := bbase (se 4 (by rfl) ⟨331389, by rfl⟩ : syracuseStep 3534821 = 662779) (by norm_num)
theorem B3977221 : Blo 1570983 3977221 := bbase (se 4 (by rfl) ⟨372864, by rfl⟩ : syracuseStep 3977221 = 745729) (by norm_num)
theorem B1888261 : Blo 1570983 1888261 := bbase (se 4 (by rfl) ⟨177024, by rfl⟩ : syracuseStep 1888261 = 354049) (by norm_num)
theorem B15110165 : Blo 1570983 15110165 := bbase (se 6 (by rfl) ⟨354144, by rfl⟩ : syracuseStep 15110165 = 708289) (by norm_num)
theorem B3534893 : Blo 1570983 3534893 := bbase (se 3 (by rfl) ⟨662792, by rfl⟩ : syracuseStep 3534893 = 1325585) (by norm_num)
theorem B2871389 : Blo 1570983 2871389 := bbase (se 3 (by rfl) ⟨538385, by rfl⟩ : syracuseStep 2871389 = 1076771) (by norm_num)
theorem B3534965 : Blo 1570983 3534965 := bbase (se 5 (by rfl) ⟨165701, by rfl⟩ : syracuseStep 3534965 = 331403) (by norm_num)
theorem B3977333 : Blo 1570983 3977333 := bbase (se 5 (by rfl) ⟨186437, by rfl⟩ : syracuseStep 3977333 = 372875) (by norm_num)
theorem B5967989 : Blo 1570983 5967989 := bbase (se 5 (by rfl) ⟨279749, by rfl⟩ : syracuseStep 5967989 = 559499) (by norm_num)
theorem B3535037 : Blo 1570983 3535037 := bbase (se 3 (by rfl) ⟨662819, by rfl⟩ : syracuseStep 3535037 = 1325639) (by norm_num)
theorem B3535109 : Blo 1570983 3535109 := bbase (se 4 (by rfl) ⟨331416, by rfl⟩ : syracuseStep 3535109 = 662833) (by norm_num)
theorem B5304581 : Blo 1570983 5304581 := bbase (se 4 (by rfl) ⟨497304, by rfl⟩ : syracuseStep 5304581 = 994609) (by norm_num)
theorem B3977525 : Blo 1570983 3977525 := bbase (se 5 (by rfl) ⟨186446, by rfl⟩ : syracuseStep 3977525 = 372893) (by norm_num)
theorem B3535181 : Blo 1570983 3535181 := bbase (se 3 (by rfl) ⟨662846, by rfl⟩ : syracuseStep 3535181 = 1325693) (by norm_num)
theorem B3535253 : Blo 1570983 3535253 := bbase (se 6 (by rfl) ⟨82857, by rfl⟩ : syracuseStep 3535253 = 165715) (by norm_num)
theorem B3535325 : Blo 1570983 3535325 := bbase (se 3 (by rfl) ⟨662873, by rfl⟩ : syracuseStep 3535325 = 1325747) (by norm_num)
theorem B3535397 : Blo 1570983 3535397 := bbase (se 4 (by rfl) ⟨331443, by rfl⟩ : syracuseStep 3535397 = 662887) (by norm_num)
theorem B3535469 : Blo 1570983 3535469 := bbase (se 3 (by rfl) ⟨662900, by rfl⟩ : syracuseStep 3535469 = 1325801) (by norm_num)
theorem B3977869 : Blo 1570983 3977869 := bbase (se 3 (by rfl) ⟨745850, by rfl⟩ : syracuseStep 3977869 = 1491701) (by norm_num)
theorem B3535541 : Blo 1570983 3535541 := bbase (se 5 (by rfl) ⟨165728, by rfl⟩ : syracuseStep 3535541 = 331457) (by norm_num)
theorem B5305013 : Blo 1570983 5305013 := bbase (se 5 (by rfl) ⟨248672, by rfl⟩ : syracuseStep 5305013 = 497345) (by norm_num)
theorem B7959221 : Blo 1570983 7959221 := bbase (se 5 (by rfl) ⟨373088, by rfl⟩ : syracuseStep 7959221 = 746177) (by norm_num)
theorem B11940533 : Blo 1570983 11940533 := bbase (se 5 (by rfl) ⟨559712, by rfl⟩ : syracuseStep 11940533 = 1119425) (by norm_num)
theorem B3535613 : Blo 1570983 3535613 := bbase (se 3 (by rfl) ⟨662927, by rfl⟩ : syracuseStep 3535613 = 1325855) (by norm_num)
theorem B3977981 : Blo 1570983 3977981 := bbase (se 3 (by rfl) ⟨745871, by rfl⟩ : syracuseStep 3977981 = 1491743) (by norm_num)
theorem B2831117 : Blo 1570983 2831117 := bbase (se 3 (by rfl) ⟨530834, by rfl⟩ : syracuseStep 2831117 = 1061669) (by norm_num)
theorem B3535685 : Blo 1570983 3535685 := bbase (se 4 (by rfl) ⟨331470, by rfl⟩ : syracuseStep 3535685 = 662941) (by norm_num)
theorem B5665621 : Blo 1570983 5665621 := bbase (se 9 (by rfl) ⟨16598, by rfl⟩ : syracuseStep 5665621 = 33197) (by norm_num)
theorem B4477781 : Blo 1570983 4477781 := bbase (se 9 (by rfl) ⟨13118, by rfl⟩ : syracuseStep 4477781 = 26237) (by norm_num)
theorem B3535757 : Blo 1570983 3535757 := bbase (se 3 (by rfl) ⟨662954, by rfl⟩ : syracuseStep 3535757 = 1325909) (by norm_num)
theorem B2651069 : Blo 1570983 2651069 := bbase (se 3 (by rfl) ⟨497075, by rfl⟩ : syracuseStep 2651069 = 994151) (by norm_num)
theorem B3978173 : Blo 1570983 3978173 := bbase (se 3 (by rfl) ⟨745907, by rfl⟩ : syracuseStep 3978173 = 1491815) (by norm_num)
theorem B3535829 : Blo 1570983 3535829 := bbase (se 7 (by rfl) ⟨41435, by rfl⟩ : syracuseStep 3535829 = 82871) (by norm_num)
theorem B1700869 : Blo 1570983 1700869 := bbase (se 4 (by rfl) ⟨159456, by rfl⟩ : syracuseStep 1700869 = 318913) (by norm_num)
theorem B3535901 : Blo 1570983 3535901 := bbase (se 3 (by rfl) ⟨662981, by rfl⟩ : syracuseStep 3535901 = 1325963) (by norm_num)
theorem B2651197 : Blo 1570983 2651197 := bbase (se 3 (by rfl) ⟨497099, by rfl⟩ : syracuseStep 2651197 = 994199) (by norm_num)
theorem B11932757 : Blo 1570983 11932757 := bbase (se 8 (by rfl) ⟨69918, by rfl⟩ : syracuseStep 11932757 = 139837) (by norm_num)
theorem B3535973 : Blo 1570983 3535973 := bbase (se 4 (by rfl) ⟨331497, by rfl⟩ : syracuseStep 3535973 = 662995) (by norm_num)
theorem B5305445 : Blo 1570983 5305445 := bbase (se 4 (by rfl) ⟨497385, by rfl⟩ : syracuseStep 5305445 = 994771) (by norm_num)
theorem B6714485 : Blo 1570983 6714485 := bbase (se 5 (by rfl) ⟨314741, by rfl⟩ : syracuseStep 6714485 = 629483) (by norm_num)
theorem B5665925 : Blo 1570983 5665925 := bbase (se 4 (by rfl) ⟨531180, by rfl⟩ : syracuseStep 5665925 = 1062361) (by norm_num)
theorem B2651285 : Blo 1570983 2651285 := bbase (se 6 (by rfl) ⟨62139, by rfl⟩ : syracuseStep 2651285 = 124279) (by norm_num)
theorem B3536045 : Blo 1570983 3536045 := bbase (se 3 (by rfl) ⟨663008, by rfl⟩ : syracuseStep 3536045 = 1326017) (by norm_num)
theorem B3536117 : Blo 1570983 3536117 := bbase (se 5 (by rfl) ⟨165755, by rfl⟩ : syracuseStep 3536117 = 331511) (by norm_num)
theorem B3355901 : Blo 1570983 3355901 := bbase (se 3 (by rfl) ⟨629231, by rfl⟩ : syracuseStep 3355901 = 1258463) (by norm_num)
theorem B2356493 : Blo 1570983 2356493 := bbase (se 3 (by rfl) ⟨441842, by rfl⟩ : syracuseStep 2356493 = 883685) (by norm_num)
theorem B2651413 : Blo 1570983 2651413 := bbase (se 6 (by rfl) ⟨62142, by rfl⟩ : syracuseStep 2651413 = 124285) (by norm_num)
theorem B3978517 : Blo 1570983 3978517 := bbase (se 6 (by rfl) ⟨93246, by rfl⟩ : syracuseStep 3978517 = 186493) (by norm_num)
theorem B5969173 : Blo 1570983 5969173 := bbase (se 6 (by rfl) ⟨139902, by rfl⟩ : syracuseStep 5969173 = 279805) (by norm_num)
theorem B2356517 : Blo 1570983 2356517 := bbase (se 4 (by rfl) ⟨220923, by rfl⟩ : syracuseStep 2356517 = 441847) (by norm_num)
theorem B2356541 : Blo 1570983 2356541 := bbase (se 3 (by rfl) ⟨441851, by rfl⟩ : syracuseStep 2356541 = 883703) (by norm_num)
theorem B3536189 : Blo 1570983 3536189 := bbase (se 3 (by rfl) ⟨663035, by rfl⟩ : syracuseStep 3536189 = 1326071) (by norm_num)
theorem B2356565 : Blo 1570983 2356565 := bbase (se 13 (by rfl) ⟨431, by rfl⟩ : syracuseStep 2356565 = 863) (by norm_num)
theorem B2356589 : Blo 1570983 2356589 := bbase (se 3 (by rfl) ⟨441860, by rfl⟩ : syracuseStep 2356589 = 883721) (by norm_num)
theorem B2651501 : Blo 1570983 2651501 := bbase (se 3 (by rfl) ⟨497156, by rfl⟩ : syracuseStep 2651501 = 994313) (by norm_num)
theorem B1914229 : Blo 1570983 1914229 := bbase (se 5 (by rfl) ⟨89729, by rfl⟩ : syracuseStep 1914229 = 179459) (by norm_num)
theorem B2356613 : Blo 1570983 2356613 := bbase (se 4 (by rfl) ⟨220932, by rfl⟩ : syracuseStep 2356613 = 441865) (by norm_num)
theorem B3536261 : Blo 1570983 3536261 := bbase (se 4 (by rfl) ⟨331524, by rfl⟩ : syracuseStep 3536261 = 663049) (by norm_num)
theorem B3978629 : Blo 1570983 3978629 := bbase (se 4 (by rfl) ⟨372996, by rfl⟩ : syracuseStep 3978629 = 745993) (by norm_num)
theorem B2356637 : Blo 1570983 2356637 := bbase (se 3 (by rfl) ⟨441869, by rfl⟩ : syracuseStep 2356637 = 883739) (by norm_num)
theorem B2831773 : Blo 1570983 2831773 := bbase (se 3 (by rfl) ⟨530957, by rfl⟩ : syracuseStep 2831773 = 1061915) (by norm_num)
theorem B2356661 : Blo 1570983 2356661 := bbase (se 5 (by rfl) ⟨110468, by rfl⟩ : syracuseStep 2356661 = 220937) (by norm_num)
theorem B2356685 : Blo 1570983 2356685 := bbase (se 3 (by rfl) ⟨441878, by rfl⟩ : syracuseStep 2356685 = 883757) (by norm_num)
theorem B3536333 : Blo 1570983 3536333 := bbase (se 3 (by rfl) ⟨663062, by rfl⟩ : syracuseStep 3536333 = 1326125) (by norm_num)
theorem B2356709 : Blo 1570983 2356709 := bbase (se 4 (by rfl) ⟨220941, by rfl⟩ : syracuseStep 2356709 = 441883) (by norm_num)
theorem B2651629 : Blo 1570983 2651629 := bbase (se 3 (by rfl) ⟨497180, by rfl⟩ : syracuseStep 2651629 = 994361) (by norm_num)
theorem B3356149 : Blo 1570983 3356149 := bbase (se 5 (by rfl) ⟨157319, by rfl⟩ : syracuseStep 3356149 = 314639) (by norm_num)
theorem B9688565 : Blo 1570983 9688565 := bbase (se 5 (by rfl) ⟨454151, by rfl⟩ : syracuseStep 9688565 = 908303) (by norm_num)
theorem B2356733 : Blo 1570983 2356733 := bbase (se 3 (by rfl) ⟨441887, by rfl⟩ : syracuseStep 2356733 = 883775) (by norm_num)
theorem B3585541 : Blo 1570983 3585541 := bbase (se 4 (by rfl) ⟨336144, by rfl⟩ : syracuseStep 3585541 = 672289) (by norm_num)
theorem B2356757 : Blo 1570983 2356757 := bbase (se 6 (by rfl) ⟨55236, by rfl⟩ : syracuseStep 2356757 = 110473) (by norm_num)
theorem B3536405 : Blo 1570983 3536405 := bbase (se 6 (by rfl) ⟨82884, by rfl⟩ : syracuseStep 3536405 = 165769) (by norm_num)
theorem B5305877 : Blo 1570983 5305877 := bbase (se 6 (by rfl) ⟨124356, by rfl⟩ : syracuseStep 5305877 = 248713) (by norm_num)
theorem B2356781 : Blo 1570983 2356781 := bbase (se 3 (by rfl) ⟨441896, by rfl⟩ : syracuseStep 2356781 = 883793) (by norm_num)
theorem B2356805 : Blo 1570983 2356805 := bbase (se 4 (by rfl) ⟨220950, by rfl⟩ : syracuseStep 2356805 = 441901) (by norm_num)
theorem B2651717 : Blo 1570983 2651717 := bbase (se 4 (by rfl) ⟨248598, by rfl⟩ : syracuseStep 2651717 = 497197) (by norm_num)
theorem B3978821 : Blo 1570983 3978821 := bbase (se 4 (by rfl) ⟨373014, by rfl⟩ : syracuseStep 3978821 = 746029) (by norm_num)
theorem B5969477 : Blo 1570983 5969477 := bbase (se 4 (by rfl) ⟨559638, by rfl⟩ : syracuseStep 5969477 = 1119277) (by norm_num)
theorem B2356829 : Blo 1570983 2356829 := bbase (se 3 (by rfl) ⟨441905, by rfl⟩ : syracuseStep 2356829 = 883811) (by norm_num)
theorem B3536477 : Blo 1570983 3536477 := bbase (se 3 (by rfl) ⟨663089, by rfl⟩ : syracuseStep 3536477 = 1326179) (by norm_num)
theorem B2356853 : Blo 1570983 2356853 := bbase (se 5 (by rfl) ⟨110477, by rfl⟩ : syracuseStep 2356853 = 220955) (by norm_num)
theorem B2389637 : Blo 1570983 2389637 := bbase (se 4 (by rfl) ⟨224028, by rfl⟩ : syracuseStep 2389637 = 448057) (by norm_num)
theorem B2356877 : Blo 1570983 2356877 := bbase (se 3 (by rfl) ⟨441914, by rfl⟩ : syracuseStep 2356877 = 883829) (by norm_num)
theorem B1791653 : Blo 1570983 1791653 := bbase (se 4 (by rfl) ⟨167967, by rfl⟩ : syracuseStep 1791653 = 335935) (by norm_num)
theorem B2356901 : Blo 1570983 2356901 := bbase (se 4 (by rfl) ⟨220959, by rfl⟩ : syracuseStep 2356901 = 441919) (by norm_num)
theorem B3536549 : Blo 1570983 3536549 := bbase (se 4 (by rfl) ⟨331551, by rfl⟩ : syracuseStep 3536549 = 663103) (by norm_num)
theorem B2356925 : Blo 1570983 2356925 := bbase (se 3 (by rfl) ⟨441923, by rfl⟩ : syracuseStep 2356925 = 883847) (by norm_num)
theorem B2651845 : Blo 1570983 2651845 := bbase (se 4 (by rfl) ⟨248610, by rfl⟩ : syracuseStep 2651845 = 497221) (by norm_num)
theorem B2356949 : Blo 1570983 2356949 := bbase (se 7 (by rfl) ⟨27620, by rfl⟩ : syracuseStep 2356949 = 55241) (by norm_num)
theorem B1988317 : Blo 1570983 1988317 := bbase (se 3 (by rfl) ⟨372809, by rfl⟩ : syracuseStep 1988317 = 745619) (by norm_num)
theorem B2356973 : Blo 1570983 2356973 := bbase (se 3 (by rfl) ⟨441932, by rfl⟩ : syracuseStep 2356973 = 883865) (by norm_num)
theorem B3536621 : Blo 1570983 3536621 := bbase (se 3 (by rfl) ⟨663116, by rfl⟩ : syracuseStep 3536621 = 1326233) (by norm_num)
theorem B10065653 : Blo 1570983 10065653 := bbase (se 5 (by rfl) ⟨471827, by rfl⟩ : syracuseStep 10065653 = 943655) (by norm_num)
theorem B2356997 : Blo 1570983 2356997 := bbase (se 4 (by rfl) ⟨220968, by rfl⟩ : syracuseStep 2356997 = 441937) (by norm_num)
theorem B8951573 : Blo 1570983 8951573 := bbase (se 6 (by rfl) ⟨209802, by rfl⟩ : syracuseStep 8951573 = 419605) (by norm_num)
theorem B2357021 : Blo 1570983 2357021 := bbase (se 3 (by rfl) ⟨441941, by rfl⟩ : syracuseStep 2357021 = 883883) (by norm_num)
theorem B2651933 : Blo 1570983 2651933 := bbase (se 3 (by rfl) ⟨497237, by rfl⟩ : syracuseStep 2651933 = 994475) (by norm_num)
theorem B2357045 : Blo 1570983 2357045 := bbase (se 5 (by rfl) ⟨110486, by rfl⟩ : syracuseStep 2357045 = 220973) (by norm_num)
theorem B3536693 : Blo 1570983 3536693 := bbase (se 5 (by rfl) ⟨165782, by rfl⟩ : syracuseStep 3536693 = 331565) (by norm_num)
theorem B2357069 : Blo 1570983 2357069 := bbase (se 3 (by rfl) ⟨441950, by rfl⟩ : syracuseStep 2357069 = 883901) (by norm_num)
theorem B2357093 : Blo 1570983 2357093 := bbase (se 4 (by rfl) ⟨220977, by rfl⟩ : syracuseStep 2357093 = 441955) (by norm_num)
theorem B2357117 : Blo 1570983 2357117 := bbase (se 3 (by rfl) ⟨441959, by rfl⟩ : syracuseStep 2357117 = 883919) (by norm_num)
theorem B3536765 : Blo 1570983 3536765 := bbase (se 3 (by rfl) ⟨663143, by rfl⟩ : syracuseStep 3536765 = 1326287) (by norm_num)
theorem B1988489 : Blo 1570983 1988489 := bbase (se 2 (by rfl) ⟨745683, by rfl⟩ : syracuseStep 1988489 = 1491367) (by norm_num)
theorem B2357141 : Blo 1570983 2357141 := bbase (se 6 (by rfl) ⟨55245, by rfl⟩ : syracuseStep 2357141 = 110491) (by norm_num)
theorem B2652061 : Blo 1570983 2652061 := bbase (se 3 (by rfl) ⟨497261, by rfl⟩ : syracuseStep 2652061 = 994523) (by norm_num)
theorem B3979165 : Blo 1570983 3979165 := bbase (se 3 (by rfl) ⟨746093, by rfl⟩ : syracuseStep 3979165 = 1492187) (by norm_num)
theorem B2357165 : Blo 1570983 2357165 := bbase (se 3 (by rfl) ⟨441968, by rfl⟩ : syracuseStep 2357165 = 883937) (by norm_num)
theorem B1767361 : Blo 1570983 1767361 := bbase (se 2 (by rfl) ⟨662760, by rfl⟩ : syracuseStep 1767361 = 1325521) (by norm_num)
theorem B1988545 : Blo 1570983 1988545 := bbase (se 2 (by rfl) ⟨745704, by rfl⟩ : syracuseStep 1988545 = 1491409) (by norm_num)
theorem B2357189 : Blo 1570983 2357189 := bbase (se 4 (by rfl) ⟨220986, by rfl⟩ : syracuseStep 2357189 = 441973) (by norm_num)
theorem B3536837 : Blo 1570983 3536837 := bbase (se 4 (by rfl) ⟨331578, by rfl⟩ : syracuseStep 3536837 = 663157) (by norm_num)
theorem B5306309 : Blo 1570983 5306309 := bbase (se 4 (by rfl) ⟨497466, by rfl⟩ : syracuseStep 5306309 = 994933) (by norm_num)
theorem B7960517 : Blo 1570983 7960517 := bbase (se 4 (by rfl) ⟨746298, by rfl⟩ : syracuseStep 7960517 = 1492597) (by norm_num)
theorem B2357213 : Blo 1570983 2357213 := bbase (se 3 (by rfl) ⟨441977, by rfl⟩ : syracuseStep 2357213 = 883955) (by norm_num)
theorem B1767397 : Blo 1570983 1767397 := bbase (se 4 (by rfl) ⟨165693, by rfl⟩ : syracuseStep 1767397 = 331387) (by norm_num)
theorem B3356653 : Blo 1570983 3356653 := bbase (se 3 (by rfl) ⟨629372, by rfl⟩ : syracuseStep 3356653 = 1258745) (by norm_num)
theorem B2357237 : Blo 1570983 2357237 := bbase (se 5 (by rfl) ⟨110495, by rfl⟩ : syracuseStep 2357237 = 220991) (by norm_num)
theorem B2652149 : Blo 1570983 2652149 := bbase (se 5 (by rfl) ⟨124319, by rfl⟩ : syracuseStep 2652149 = 248639) (by norm_num)
theorem B1914881 : Blo 1570983 1914881 := bbase (se 2 (by rfl) ⟨718080, by rfl⟩ : syracuseStep 1914881 = 1436161) (by norm_num)
theorem B1767433 : Blo 1570983 1767433 := bbase (se 2 (by rfl) ⟨662787, by rfl⟩ : syracuseStep 1767433 = 1325575) (by norm_num)
theorem B2357261 : Blo 1570983 2357261 := bbase (se 3 (by rfl) ⟨441986, by rfl⟩ : syracuseStep 2357261 = 883973) (by norm_num)
theorem B3536909 : Blo 1570983 3536909 := bbase (se 3 (by rfl) ⟨663170, by rfl⟩ : syracuseStep 3536909 = 1326341) (by norm_num)
theorem B3979277 : Blo 1570983 3979277 := bbase (se 3 (by rfl) ⟨746114, by rfl⟩ : syracuseStep 3979277 = 1492229) (by norm_num)
theorem B1988641 : Blo 1570983 1988641 := bbase (se 2 (by rfl) ⟨745740, by rfl⟩ : syracuseStep 1988641 = 1491481) (by norm_num)
theorem B2357285 : Blo 1570983 2357285 := bbase (se 4 (by rfl) ⟨220995, by rfl⟩ : syracuseStep 2357285 = 441991) (by norm_num)
theorem B5036069 : Blo 1570983 5036069 := bbase (se 4 (by rfl) ⟨472131, by rfl⟩ : syracuseStep 5036069 = 944263) (by norm_num)
theorem B1767469 : Blo 1570983 1767469 := bbase (se 3 (by rfl) ⟨331400, by rfl⟩ : syracuseStep 1767469 = 662801) (by norm_num)
theorem B2357309 : Blo 1570983 2357309 := bbase (se 3 (by rfl) ⟨441995, by rfl⟩ : syracuseStep 2357309 = 883991) (by norm_num)
theorem B1767505 : Blo 1570983 1767505 := bbase (se 2 (by rfl) ⟨662814, by rfl⟩ : syracuseStep 1767505 = 1325629) (by norm_num)
theorem B2357333 : Blo 1570983 2357333 := bbase (se 8 (by rfl) ⟨13812, by rfl⟩ : syracuseStep 2357333 = 27625) (by norm_num)
theorem B3536981 : Blo 1570983 3536981 := bbase (se 8 (by rfl) ⟨20724, by rfl⟩ : syracuseStep 3536981 = 41449) (by norm_num)
theorem B6715493 : Blo 1570983 6715493 := bbase (se 4 (by rfl) ⟨629577, by rfl⟩ : syracuseStep 6715493 = 1259155) (by norm_num)
theorem B2357357 : Blo 1570983 2357357 := bbase (se 3 (by rfl) ⟨442004, by rfl⟩ : syracuseStep 2357357 = 884009) (by norm_num)
theorem B1767541 : Blo 1570983 1767541 := bbase (se 5 (by rfl) ⟨82853, by rfl⟩ : syracuseStep 1767541 = 165707) (by norm_num)
theorem B2652277 : Blo 1570983 2652277 := bbase (se 5 (by rfl) ⟨124325, by rfl⟩ : syracuseStep 2652277 = 248651) (by norm_num)
theorem B2357381 : Blo 1570983 2357381 := bbase (se 4 (by rfl) ⟨221004, by rfl⟩ : syracuseStep 2357381 = 442009) (by norm_num)
theorem B1767577 : Blo 1570983 1767577 := bbase (se 2 (by rfl) ⟨662841, by rfl⟩ : syracuseStep 1767577 = 1325683) (by norm_num)
theorem B2357405 : Blo 1570983 2357405 := bbase (se 3 (by rfl) ⟨442013, by rfl⟩ : syracuseStep 2357405 = 884027) (by norm_num)
theorem B3537053 : Blo 1570983 3537053 := bbase (se 3 (by rfl) ⟨663197, by rfl⟩ : syracuseStep 3537053 = 1326395) (by norm_num)
theorem B2357429 : Blo 1570983 2357429 := bbase (se 5 (by rfl) ⟨110504, by rfl⟩ : syracuseStep 2357429 = 221009) (by norm_num)
theorem B2832565 : Blo 1570983 2832565 := bbase (se 5 (by rfl) ⟨132776, by rfl⟩ : syracuseStep 2832565 = 265553) (by norm_num)
theorem B1767613 : Blo 1570983 1767613 := bbase (se 3 (by rfl) ⟨331427, by rfl⟩ : syracuseStep 1767613 = 662855) (by norm_num)
theorem B1988813 : Blo 1570983 1988813 := bbase (se 3 (by rfl) ⟨372902, by rfl⟩ : syracuseStep 1988813 = 745805) (by norm_num)
theorem B2357453 : Blo 1570983 2357453 := bbase (se 3 (by rfl) ⟨442022, by rfl⟩ : syracuseStep 2357453 = 884045) (by norm_num)
theorem B2652365 : Blo 1570983 2652365 := bbase (se 3 (by rfl) ⟨497318, by rfl⟩ : syracuseStep 2652365 = 994637) (by norm_num)
theorem B3979469 : Blo 1570983 3979469 := bbase (se 3 (by rfl) ⟨746150, by rfl⟩ : syracuseStep 3979469 = 1492301) (by norm_num)
theorem B1767649 : Blo 1570983 1767649 := bbase (se 2 (by rfl) ⟨662868, by rfl⟩ : syracuseStep 1767649 = 1325737) (by norm_num)
theorem B2357477 : Blo 1570983 2357477 := bbase (se 4 (by rfl) ⟨221013, by rfl⟩ : syracuseStep 2357477 = 442027) (by norm_num)
theorem B3537125 : Blo 1570983 3537125 := bbase (se 4 (by rfl) ⟨331605, by rfl⟩ : syracuseStep 3537125 = 663211) (by norm_num)
theorem B2357501 : Blo 1570983 2357501 := bbase (se 3 (by rfl) ⟨442031, by rfl⟩ : syracuseStep 2357501 = 884063) (by norm_num)
theorem B1767685 : Blo 1570983 1767685 := bbase (se 4 (by rfl) ⟨165720, by rfl⟩ : syracuseStep 1767685 = 331441) (by norm_num)
theorem B1988869 : Blo 1570983 1988869 := bbase (se 4 (by rfl) ⟨186456, by rfl⟩ : syracuseStep 1988869 = 372913) (by norm_num)
theorem B2357525 : Blo 1570983 2357525 := bbase (se 6 (by rfl) ⟨55254, by rfl⟩ : syracuseStep 2357525 = 110509) (by norm_num)
theorem B2390293 : Blo 1570983 2390293 := bbase (se 6 (by rfl) ⟨56022, by rfl⟩ : syracuseStep 2390293 = 112045) (by norm_num)
theorem B1767721 : Blo 1570983 1767721 := bbase (se 2 (by rfl) ⟨662895, by rfl⟩ : syracuseStep 1767721 = 1325791) (by norm_num)
theorem B2357549 : Blo 1570983 2357549 := bbase (se 3 (by rfl) ⟨442040, by rfl⟩ : syracuseStep 2357549 = 884081) (by norm_num)
theorem B3537197 : Blo 1570983 3537197 := bbase (se 3 (by rfl) ⟨663224, by rfl⟩ : syracuseStep 3537197 = 1326449) (by norm_num)
theorem B2390317 : Blo 1570983 2390317 := bbase (se 3 (by rfl) ⟨448184, by rfl⟩ : syracuseStep 2390317 = 896369) (by norm_num)
theorem B2357573 : Blo 1570983 2357573 := bbase (se 4 (by rfl) ⟨221022, by rfl⟩ : syracuseStep 2357573 = 442045) (by norm_num)
theorem B1767757 : Blo 1570983 1767757 := bbase (se 3 (by rfl) ⟨331454, by rfl⟩ : syracuseStep 1767757 = 662909) (by norm_num)
theorem B2652493 : Blo 1570983 2652493 := bbase (se 3 (by rfl) ⟨497342, by rfl⟩ : syracuseStep 2652493 = 994685) (by norm_num)
theorem B2357597 : Blo 1570983 2357597 := bbase (se 3 (by rfl) ⟨442049, by rfl⟩ : syracuseStep 2357597 = 884099) (by norm_num)
theorem B1988965 : Blo 1570983 1988965 := bbase (se 4 (by rfl) ⟨186465, by rfl⟩ : syracuseStep 1988965 = 372931) (by norm_num)
theorem B1677677 : Blo 1570983 1677677 := bbase (se 3 (by rfl) ⟨314564, by rfl⟩ : syracuseStep 1677677 = 629129) (by norm_num)
theorem B1767793 : Blo 1570983 1767793 := bbase (se 2 (by rfl) ⟨662922, by rfl⟩ : syracuseStep 1767793 = 1325845) (by norm_num)
theorem B2357621 : Blo 1570983 2357621 := bbase (se 5 (by rfl) ⟨110513, by rfl⟩ : syracuseStep 2357621 = 221027) (by norm_num)
theorem B3537269 : Blo 1570983 3537269 := bbase (se 5 (by rfl) ⟨165809, by rfl⟩ : syracuseStep 3537269 = 331619) (by norm_num)
theorem B5306741 : Blo 1570983 5306741 := bbase (se 5 (by rfl) ⟨248753, by rfl⟩ : syracuseStep 5306741 = 497507) (by norm_num)
theorem B2357645 : Blo 1570983 2357645 := bbase (se 3 (by rfl) ⟨442058, by rfl⟩ : syracuseStep 2357645 = 884117) (by norm_num)
theorem B1767829 : Blo 1570983 1767829 := bbase (se 6 (by rfl) ⟨41433, by rfl⟩ : syracuseStep 1767829 = 82867) (by norm_num)
theorem B2357669 : Blo 1570983 2357669 := bbase (se 4 (by rfl) ⟨221031, by rfl⟩ : syracuseStep 2357669 = 442063) (by norm_num)
theorem B2652581 : Blo 1570983 2652581 := bbase (se 4 (by rfl) ⟨248679, by rfl⟩ : syracuseStep 2652581 = 497359) (by norm_num)
theorem B1767865 : Blo 1570983 1767865 := bbase (se 2 (by rfl) ⟨662949, by rfl⟩ : syracuseStep 1767865 = 1325899) (by norm_num)
theorem B2357693 : Blo 1570983 2357693 := bbase (se 3 (by rfl) ⟨442067, by rfl⟩ : syracuseStep 2357693 = 884135) (by norm_num)
theorem B3537341 : Blo 1570983 3537341 := bbase (se 3 (by rfl) ⟨663251, by rfl⟩ : syracuseStep 3537341 = 1326503) (by norm_num)
theorem B2357717 : Blo 1570983 2357717 := bbase (se 7 (by rfl) ⟨27629, by rfl⟩ : syracuseStep 2357717 = 55259) (by norm_num)
theorem B1767901 : Blo 1570983 1767901 := bbase (se 3 (by rfl) ⟨331481, by rfl⟩ : syracuseStep 1767901 = 662963) (by norm_num)
theorem B2357741 : Blo 1570983 2357741 := bbase (se 3 (by rfl) ⟨442076, by rfl⟩ : syracuseStep 2357741 = 884153) (by norm_num)
theorem B1767937 : Blo 1570983 1767937 := bbase (se 2 (by rfl) ⟨662976, by rfl⟩ : syracuseStep 1767937 = 1325953) (by norm_num)
theorem B2357765 : Blo 1570983 2357765 := bbase (se 4 (by rfl) ⟨221040, by rfl⟩ : syracuseStep 2357765 = 442081) (by norm_num)
theorem B3537413 : Blo 1570983 3537413 := bbase (se 4 (by rfl) ⟨331632, by rfl⟩ : syracuseStep 3537413 = 663265) (by norm_num)
theorem B1989137 : Blo 1570983 1989137 := bbase (se 2 (by rfl) ⟨745926, by rfl⟩ : syracuseStep 1989137 = 1491853) (by norm_num)
theorem B13425173 : Blo 1570983 13425173 := bbase (se 6 (by rfl) ⟨314652, by rfl⟩ : syracuseStep 13425173 = 629305) (by norm_num)
theorem B2357789 : Blo 1570983 2357789 := bbase (se 3 (by rfl) ⟨442085, by rfl⟩ : syracuseStep 2357789 = 884171) (by norm_num)
theorem B1767973 : Blo 1570983 1767973 := bbase (se 4 (by rfl) ⟨165747, by rfl⟩ : syracuseStep 1767973 = 331495) (by norm_num)
theorem B2652709 : Blo 1570983 2652709 := bbase (se 4 (by rfl) ⟨248691, by rfl⟩ : syracuseStep 2652709 = 497383) (by norm_num)
theorem B3979813 : Blo 1570983 3979813 := bbase (se 4 (by rfl) ⟨373107, by rfl⟩ : syracuseStep 3979813 = 746215) (by norm_num)
theorem B2357813 : Blo 1570983 2357813 := bbase (se 5 (by rfl) ⟨110522, by rfl⟩ : syracuseStep 2357813 = 221045) (by norm_num)
theorem B1768009 : Blo 1570983 1768009 := bbase (se 2 (by rfl) ⟨663003, by rfl⟩ : syracuseStep 1768009 = 1326007) (by norm_num)
theorem B1989193 : Blo 1570983 1989193 := bbase (se 2 (by rfl) ⟨745947, by rfl⟩ : syracuseStep 1989193 = 1491895) (by norm_num)
theorem B2357837 : Blo 1570983 2357837 := bbase (se 3 (by rfl) ⟨442094, by rfl⟩ : syracuseStep 2357837 = 884189) (by norm_num)
theorem B3537485 : Blo 1570983 3537485 := bbase (se 3 (by rfl) ⟨663278, by rfl⟩ : syracuseStep 3537485 = 1326557) (by norm_num)
theorem B1677925 : Blo 1570983 1677925 := bbase (se 4 (by rfl) ⟨157305, by rfl⟩ : syracuseStep 1677925 = 314611) (by norm_num)
theorem B2357861 : Blo 1570983 2357861 := bbase (se 4 (by rfl) ⟨221049, by rfl⟩ : syracuseStep 2357861 = 442099) (by norm_num)
theorem B1768045 : Blo 1570983 1768045 := bbase (se 3 (by rfl) ⟨331508, by rfl⟩ : syracuseStep 1768045 = 663017) (by norm_num)
theorem B2357885 : Blo 1570983 2357885 := bbase (se 3 (by rfl) ⟨442103, by rfl⟩ : syracuseStep 2357885 = 884207) (by norm_num)
theorem B2652797 : Blo 1570983 2652797 := bbase (se 3 (by rfl) ⟨497399, by rfl⟩ : syracuseStep 2652797 = 994799) (by norm_num)
theorem B1768081 : Blo 1570983 1768081 := bbase (se 2 (by rfl) ⟨663030, by rfl⟩ : syracuseStep 1768081 = 1326061) (by norm_num)
theorem B2357909 : Blo 1570983 2357909 := bbase (se 6 (by rfl) ⟨55263, by rfl⟩ : syracuseStep 2357909 = 110527) (by norm_num)
theorem B3537557 : Blo 1570983 3537557 := bbase (se 6 (by rfl) ⟨82911, by rfl⟩ : syracuseStep 3537557 = 165823) (by norm_num)
theorem B3979925 : Blo 1570983 3979925 := bbase (se 6 (by rfl) ⟨93279, by rfl⟩ : syracuseStep 3979925 = 186559) (by norm_num)
theorem B1989289 : Blo 1570983 1989289 := bbase (se 2 (by rfl) ⟨745983, by rfl⟩ : syracuseStep 1989289 = 1491967) (by norm_num)
theorem B2357933 : Blo 1570983 2357933 := bbase (se 3 (by rfl) ⟨442112, by rfl⟩ : syracuseStep 2357933 = 884225) (by norm_num)
theorem B1768117 : Blo 1570983 1768117 := bbase (se 5 (by rfl) ⟨82880, by rfl⟩ : syracuseStep 1768117 = 165761) (by norm_num)
theorem B2357957 : Blo 1570983 2357957 := bbase (se 4 (by rfl) ⟨221058, by rfl⟩ : syracuseStep 2357957 = 442117) (by norm_num)
theorem B7551701 : Blo 1570983 7551701 := bbase (se 7 (by rfl) ⟨88496, by rfl⟩ : syracuseStep 7551701 = 176993) (by norm_num)
theorem B1768153 : Blo 1570983 1768153 := bbase (se 2 (by rfl) ⟨663057, by rfl⟩ : syracuseStep 1768153 = 1326115) (by norm_num)
theorem B2357981 : Blo 1570983 2357981 := bbase (se 3 (by rfl) ⟨442121, by rfl⟩ : syracuseStep 2357981 = 884243) (by norm_num)
theorem B3537629 : Blo 1570983 3537629 := bbase (se 3 (by rfl) ⟨663305, by rfl⟩ : syracuseStep 3537629 = 1326611) (by norm_num)
theorem B5741285 : Blo 1570983 5741285 := bbase (se 4 (by rfl) ⟨538245, by rfl⟩ : syracuseStep 5741285 = 1076491) (by norm_num)
theorem B2358005 : Blo 1570983 2358005 := bbase (se 5 (by rfl) ⟨110531, by rfl⟩ : syracuseStep 2358005 = 221063) (by norm_num)
theorem B1768189 : Blo 1570983 1768189 := bbase (se 3 (by rfl) ⟨331535, by rfl⟩ : syracuseStep 1768189 = 663071) (by norm_num)
theorem B2652925 : Blo 1570983 2652925 := bbase (se 3 (by rfl) ⟨497423, by rfl⟩ : syracuseStep 2652925 = 994847) (by norm_num)
theorem B2358029 : Blo 1570983 2358029 := bbase (se 3 (by rfl) ⟨442130, by rfl⟩ : syracuseStep 2358029 = 884261) (by norm_num)
theorem B1768225 : Blo 1570983 1768225 := bbase (se 2 (by rfl) ⟨663084, by rfl⟩ : syracuseStep 1768225 = 1326169) (by norm_num)
theorem B2358053 : Blo 1570983 2358053 := bbase (se 4 (by rfl) ⟨221067, by rfl⟩ : syracuseStep 2358053 = 442135) (by norm_num)
theorem B3537701 : Blo 1570983 3537701 := bbase (se 4 (by rfl) ⟨331659, by rfl⟩ : syracuseStep 3537701 = 663319) (by norm_num)
theorem B2358077 : Blo 1570983 2358077 := bbase (se 3 (by rfl) ⟨442139, by rfl⟩ : syracuseStep 2358077 = 884279) (by norm_num)
theorem B1768261 : Blo 1570983 1768261 := bbase (se 4 (by rfl) ⟨165774, by rfl⟩ : syracuseStep 1768261 = 331549) (by norm_num)
theorem B1989461 : Blo 1570983 1989461 := bbase (se 9 (by rfl) ⟨5828, by rfl⟩ : syracuseStep 1989461 = 11657) (by norm_num)
theorem B2358101 : Blo 1570983 2358101 := bbase (se 9 (by rfl) ⟨6908, by rfl⟩ : syracuseStep 2358101 = 13817) (by norm_num)
theorem B2653013 : Blo 1570983 2653013 := bbase (se 9 (by rfl) ⟨7772, by rfl⟩ : syracuseStep 2653013 = 15545) (by norm_num)
theorem B3980117 : Blo 1570983 3980117 := bbase (se 9 (by rfl) ⟨11660, by rfl⟩ : syracuseStep 3980117 = 23321) (by norm_num)
theorem B3357541 : Blo 1570983 3357541 := bbase (se 4 (by rfl) ⟨314769, by rfl⟩ : syracuseStep 3357541 = 629539) (by norm_num)
theorem B1768297 : Blo 1570983 1768297 := bbase (se 2 (by rfl) ⟨663111, by rfl⟩ : syracuseStep 1768297 = 1326223) (by norm_num)
theorem B2358125 : Blo 1570983 2358125 := bbase (se 3 (by rfl) ⟨442148, by rfl⟩ : syracuseStep 2358125 = 884297) (by norm_num)
theorem B3537773 : Blo 1570983 3537773 := bbase (se 3 (by rfl) ⟨663332, by rfl⟩ : syracuseStep 3537773 = 1326665) (by norm_num)
theorem B6806389 : Blo 1570983 6806389 := bbase (se 5 (by rfl) ⟨319049, by rfl⟩ : syracuseStep 6806389 = 638099) (by norm_num)
theorem B2358149 : Blo 1570983 2358149 := bbase (se 4 (by rfl) ⟨221076, by rfl⟩ : syracuseStep 2358149 = 442153) (by norm_num)
theorem B1768333 : Blo 1570983 1768333 := bbase (se 3 (by rfl) ⟨331562, by rfl⟩ : syracuseStep 1768333 = 663125) (by norm_num)
theorem B1989517 : Blo 1570983 1989517 := bbase (se 3 (by rfl) ⟨373034, by rfl⟩ : syracuseStep 1989517 = 746069) (by norm_num)
theorem B7551893 : Blo 1570983 7551893 := bbase (se 6 (by rfl) ⟨176997, by rfl⟩ : syracuseStep 7551893 = 353995) (by norm_num)
theorem B1792921 : Blo 1570983 1792921 := bbase (se 2 (by rfl) ⟨672345, by rfl⟩ : syracuseStep 1792921 = 1344691) (by norm_num)
theorem B2358173 : Blo 1570983 2358173 := bbase (se 3 (by rfl) ⟨442157, by rfl⟩ : syracuseStep 2358173 = 884315) (by norm_num)
theorem B1768369 : Blo 1570983 1768369 := bbase (se 2 (by rfl) ⟨663138, by rfl⟩ : syracuseStep 1768369 = 1326277) (by norm_num)
theorem B2358197 : Blo 1570983 2358197 := bbase (se 5 (by rfl) ⟨110540, by rfl⟩ : syracuseStep 2358197 = 221081) (by norm_num)
theorem B3537845 : Blo 1570983 3537845 := bbase (se 5 (by rfl) ⟨165836, by rfl⟩ : syracuseStep 3537845 = 331673) (by norm_num)
theorem B1792957 : Blo 1570983 1792957 := bbase (se 3 (by rfl) ⟨336179, by rfl⟩ : syracuseStep 1792957 = 672359) (by norm_num)
theorem B2358221 : Blo 1570983 2358221 := bbase (se 3 (by rfl) ⟨442166, by rfl⟩ : syracuseStep 2358221 = 884333) (by norm_num)
theorem B1768405 : Blo 1570983 1768405 := bbase (se 7 (by rfl) ⟨20723, by rfl⟩ : syracuseStep 1768405 = 41447) (by norm_num)
theorem B2653141 : Blo 1570983 2653141 := bbase (se 7 (by rfl) ⟨31091, by rfl⟩ : syracuseStep 2653141 = 62183) (by norm_num)
theorem B2833373 : Blo 1570983 2833373 := bbase (se 3 (by rfl) ⟨531257, by rfl⟩ : syracuseStep 2833373 = 1062515) (by norm_num)
theorem B2358245 : Blo 1570983 2358245 := bbase (se 4 (by rfl) ⟨221085, by rfl⟩ : syracuseStep 2358245 = 442171) (by norm_num)
theorem B2153453 : Blo 1570983 2153453 := bbase (se 3 (by rfl) ⟨403772, by rfl⟩ : syracuseStep 2153453 = 807545) (by norm_num)
theorem B1989613 : Blo 1570983 1989613 := bbase (se 3 (by rfl) ⟨373052, by rfl⟩ : syracuseStep 1989613 = 746105) (by norm_num)
theorem B1768441 : Blo 1570983 1768441 := bbase (se 2 (by rfl) ⟨663165, by rfl⟩ : syracuseStep 1768441 = 1326331) (by norm_num)
theorem B2358269 : Blo 1570983 2358269 := bbase (se 3 (by rfl) ⟨442175, by rfl⟩ : syracuseStep 2358269 = 884351) (by norm_num)
theorem B3537917 : Blo 1570983 3537917 := bbase (se 3 (by rfl) ⟨663359, by rfl⟩ : syracuseStep 3537917 = 1326719) (by norm_num)
theorem B2358293 : Blo 1570983 2358293 := bbase (se 6 (by rfl) ⟨55272, by rfl⟩ : syracuseStep 2358293 = 110545) (by norm_num)
theorem B1768477 : Blo 1570983 1768477 := bbase (se 3 (by rfl) ⟨331589, by rfl⟩ : syracuseStep 1768477 = 663179) (by norm_num)
theorem B1678369 : Blo 1570983 1678369 := bbase (se 2 (by rfl) ⟨629388, by rfl⟩ : syracuseStep 1678369 = 1258777) (by norm_num)
theorem B2358317 : Blo 1570983 2358317 := bbase (se 3 (by rfl) ⟨442184, by rfl⟩ : syracuseStep 2358317 = 884369) (by norm_num)
theorem B2653229 : Blo 1570983 2653229 := bbase (se 3 (by rfl) ⟨497480, by rfl⟩ : syracuseStep 2653229 = 994961) (by norm_num)
theorem B1866817 : Blo 1570983 1866817 := bbase (se 2 (by rfl) ⟨700056, by rfl⟩ : syracuseStep 1866817 = 1400113) (by norm_num)
theorem B1768513 : Blo 1570983 1768513 := bbase (se 2 (by rfl) ⟨663192, by rfl⟩ : syracuseStep 1768513 = 1326385) (by norm_num)
theorem B2358341 : Blo 1570983 2358341 := bbase (se 4 (by rfl) ⟨221094, by rfl⟩ : syracuseStep 2358341 = 442189) (by norm_num)
theorem B3537989 : Blo 1570983 3537989 := bbase (se 4 (by rfl) ⟨331686, by rfl⟩ : syracuseStep 3537989 = 663373) (by norm_num)
theorem B1678429 : Blo 1570983 1678429 := bbase (se 3 (by rfl) ⟨314705, by rfl⟩ : syracuseStep 1678429 = 629411) (by norm_num)
theorem B2358365 : Blo 1570983 2358365 := bbase (se 3 (by rfl) ⟨442193, by rfl⟩ : syracuseStep 2358365 = 884387) (by norm_num)
theorem B1768549 : Blo 1570983 1768549 := bbase (se 4 (by rfl) ⟨165801, by rfl⟩ : syracuseStep 1768549 = 331603) (by norm_num)
theorem B5037157 : Blo 1570983 5037157 := bbase (se 4 (by rfl) ⟨472233, by rfl⟩ : syracuseStep 5037157 = 944467) (by norm_num)
theorem B2833517 : Blo 1570983 2833517 := bbase (se 3 (by rfl) ⟨531284, by rfl⟩ : syracuseStep 2833517 = 1062569) (by norm_num)
theorem B2358389 : Blo 1570983 2358389 := bbase (se 5 (by rfl) ⟨110549, by rfl⟩ : syracuseStep 2358389 = 221099) (by norm_num)
theorem B1768585 : Blo 1570983 1768585 := bbase (se 2 (by rfl) ⟨663219, by rfl⟩ : syracuseStep 1768585 = 1326439) (by norm_num)
theorem B2358413 : Blo 1570983 2358413 := bbase (se 3 (by rfl) ⟨442202, by rfl⟩ : syracuseStep 2358413 = 884405) (by norm_num)
theorem B3538061 : Blo 1570983 3538061 := bbase (se 3 (by rfl) ⟨663386, by rfl⟩ : syracuseStep 3538061 = 1326773) (by norm_num)
theorem B1989785 : Blo 1570983 1989785 := bbase (se 2 (by rfl) ⟨746169, by rfl⟩ : syracuseStep 1989785 = 1492339) (by norm_num)
theorem B2358437 : Blo 1570983 2358437 := bbase (se 4 (by rfl) ⟨221103, by rfl⟩ : syracuseStep 2358437 = 442207) (by norm_num)
theorem B1768621 : Blo 1570983 1768621 := bbase (se 3 (by rfl) ⟨331616, by rfl⟩ : syracuseStep 1768621 = 663233) (by norm_num)
theorem B2653357 : Blo 1570983 2653357 := bbase (se 3 (by rfl) ⟨497504, by rfl⟩ : syracuseStep 2653357 = 995009) (by norm_num)
theorem B2358461 : Blo 1570983 2358461 := bbase (se 3 (by rfl) ⟨442211, by rfl⟩ : syracuseStep 2358461 = 884423) (by norm_num)
theorem B1768657 : Blo 1570983 1768657 := bbase (se 2 (by rfl) ⟨663246, by rfl⟩ : syracuseStep 1768657 = 1326493) (by norm_num)
theorem B1989841 : Blo 1570983 1989841 := bbase (se 2 (by rfl) ⟨746190, by rfl⟩ : syracuseStep 1989841 = 1492381) (by norm_num)
theorem B2358485 : Blo 1570983 2358485 := bbase (se 7 (by rfl) ⟨27638, by rfl⟩ : syracuseStep 2358485 = 55277) (by norm_num)
theorem B2358509 : Blo 1570983 2358509 := bbase (se 3 (by rfl) ⟨442220, by rfl⟩ : syracuseStep 2358509 = 884441) (by norm_num)
theorem B1768693 : Blo 1570983 1768693 := bbase (se 5 (by rfl) ⟨82907, by rfl⟩ : syracuseStep 1768693 = 165815) (by norm_num)
theorem B2358533 : Blo 1570983 2358533 := bbase (se 4 (by rfl) ⟨221112, by rfl⟩ : syracuseStep 2358533 = 442225) (by norm_num)
theorem B2653445 : Blo 1570983 2653445 := bbase (se 4 (by rfl) ⟨248760, by rfl⟩ : syracuseStep 2653445 = 497521) (by norm_num)
theorem B7552277 : Blo 1570983 7552277 := bbase (se 6 (by rfl) ⟨177006, by rfl⟩ : syracuseStep 7552277 = 354013) (by norm_num)
theorem B1768729 : Blo 1570983 1768729 := bbase (se 2 (by rfl) ⟨663273, by rfl⟩ : syracuseStep 1768729 = 1326547) (by norm_num)
theorem B2358557 : Blo 1570983 2358557 := bbase (se 3 (by rfl) ⟨442229, by rfl⟩ : syracuseStep 2358557 = 884459) (by norm_num)
theorem B1989937 : Blo 1570983 1989937 := bbase (se 2 (by rfl) ⟨746226, by rfl⟩ : syracuseStep 1989937 = 1492453) (by norm_num)
theorem B2358581 : Blo 1570983 2358581 := bbase (se 5 (by rfl) ⟨110558, by rfl⟩ : syracuseStep 2358581 = 221117) (by norm_num)
theorem B1768765 : Blo 1570983 1768765 := bbase (se 3 (by rfl) ⟨331643, by rfl⟩ : syracuseStep 1768765 = 663287) (by norm_num)
theorem B2358605 : Blo 1570983 2358605 := bbase (se 3 (by rfl) ⟨442238, by rfl⟩ : syracuseStep 2358605 = 884477) (by norm_num)
theorem B3358037 : Blo 1570983 3358037 := bbase (se 11 (by rfl) ⟨2459, by rfl⟩ : syracuseStep 3358037 = 4919) (by norm_num)
theorem B1768801 : Blo 1570983 1768801 := bbase (se 2 (by rfl) ⟨663300, by rfl⟩ : syracuseStep 1768801 = 1326601) (by norm_num)
theorem B2358629 : Blo 1570983 2358629 := bbase (se 4 (by rfl) ⟨221121, by rfl⟩ : syracuseStep 2358629 = 442243) (by norm_num)
theorem B2358653 : Blo 1570983 2358653 := bbase (se 3 (by rfl) ⟨442247, by rfl⟩ : syracuseStep 2358653 = 884495) (by norm_num)
theorem B1768837 : Blo 1570983 1768837 := bbase (se 4 (by rfl) ⟨165828, by rfl⟩ : syracuseStep 1768837 = 331657) (by norm_num)
theorem B2358677 : Blo 1570983 2358677 := bbase (se 6 (by rfl) ⟨55281, by rfl⟩ : syracuseStep 2358677 = 110563) (by norm_num)
theorem B1678745 : Blo 1570983 1678745 := bbase (se 2 (by rfl) ⟨629529, by rfl⟩ : syracuseStep 1678745 = 1259059) (by norm_num)
theorem B1768873 : Blo 1570983 1768873 := bbase (se 2 (by rfl) ⟨663327, by rfl⟩ : syracuseStep 1768873 = 1326655) (by norm_num)
theorem B2358701 : Blo 1570983 2358701 := bbase (se 3 (by rfl) ⟨442256, by rfl⟩ : syracuseStep 2358701 = 884513) (by norm_num)
theorem B3186109 : Blo 1570983 3186109 := bbase (se 3 (by rfl) ⟨597395, by rfl⟩ : syracuseStep 3186109 = 1194791) (by norm_num)
theorem B2358725 : Blo 1570983 2358725 := bbase (se 4 (by rfl) ⟨221130, by rfl⟩ : syracuseStep 2358725 = 442261) (by norm_num)
theorem B1768909 : Blo 1570983 1768909 := bbase (se 3 (by rfl) ⟨331670, by rfl⟩ : syracuseStep 1768909 = 663341) (by norm_num)
theorem B1990109 : Blo 1570983 1990109 := bbase (se 3 (by rfl) ⟨373145, by rfl⟩ : syracuseStep 1990109 = 746291) (by norm_num)
theorem B1768945 : Blo 1570983 1768945 := bbase (se 2 (by rfl) ⟨663354, by rfl⟩ : syracuseStep 1768945 = 1326709) (by norm_num)
theorem B1768981 : Blo 1570983 1768981 := bbase (se 6 (by rfl) ⟨41460, by rfl⟩ : syracuseStep 1768981 = 82921) (by norm_num)
theorem B1990165 : Blo 1570983 1990165 := bbase (se 6 (by rfl) ⟨46644, by rfl⟩ : syracuseStep 1990165 = 93289) (by norm_num)
theorem B3776053 : Blo 1570983 3776053 := bbase (se 5 (by rfl) ⟨177002, by rfl⟩ : syracuseStep 3776053 = 354005) (by norm_num)
theorem B1769017 : Blo 1570983 1769017 := bbase (se 2 (by rfl) ⟨663381, by rfl⟩ : syracuseStep 1769017 = 1326763) (by norm_num)
theorem B7954037 : Blo 1570983 7954037 := bbase (se 5 (by rfl) ⟨372845, by rfl⟩ : syracuseStep 7954037 = 745691) (by norm_num)
theorem B1679189 : Blo 1570983 1679189 := bbase (se 9 (by rfl) ⟨4919, by rfl⟩ : syracuseStep 1679189 = 9839) (by norm_num)
theorem B3776753 : Blo 1570983 3776753 := bstep (se 2 (by rfl) ⟨1416282, by rfl⟩ : syracuseStep 3776753 = 2832565) B2832565
theorem B2015651 : Blo 1570983 2015651 := bstep (se 1 (by rfl) ⟨1511738, by rfl⟩ : syracuseStep 2015651 = 3023477) B3023477
theorem B7955171 : Blo 1570983 7955171 := bstep (se 1 (by rfl) ⟨5966378, by rfl⟩ : syracuseStep 7955171 = 11932757) B11932757
theorem B3777283 : Blo 1570983 3777283 := bstep (se 1 (by rfl) ⟨2832962, by rfl⟩ : syracuseStep 3777283 = 5665925) B5665925
theorem B2982673 : Blo 1570983 2982673 := bstep (se 2 (by rfl) ⟨1118502, by rfl⟩ : syracuseStep 2982673 = 2237005) B2237005
theorem B5047075 : Blo 1570983 5047075 := bstep (se 1 (by rfl) ⟨3785306, by rfl⟩ : syracuseStep 5047075 = 7570613) B7570613
theorem B2237233 : Blo 1570983 2237233 := bstep (se 2 (by rfl) ⟨838962, by rfl⟩ : syracuseStep 2237233 = 1677925) B1677925
theorem B2237267 : Blo 1570983 2237267 := bstep (se 1 (by rfl) ⟨1677950, by rfl⟩ : syracuseStep 2237267 = 3355901) B3355901
theorem B7553891 : Blo 1570983 7553891 := bstep (se 1 (by rfl) ⟨5665418, by rfl⟩ : syracuseStep 7553891 = 11330837) B11330837
theorem B4473805 : Blo 1570983 4473805 := bstep (se 3 (by rfl) ⟨838838, by rfl⟩ : syracuseStep 4473805 = 1677677) B1677677
theorem B7554161 : Blo 1570983 7554161 := bstep (se 2 (by rfl) ⟨2832810, by rfl⟩ : syracuseStep 7554161 = 5665621) B5665621
theorem B6710435 : Blo 1570983 6710435 := bstep (se 1 (by rfl) ⟨5032826, by rfl⟩ : syracuseStep 6710435 = 10065653) B10065653
theorem B7169201 : Blo 1570983 7169201 := bstep (se 2 (by rfl) ⟨2688450, by rfl⟩ : syracuseStep 7169201 = 5376901) B5376901
theorem B7554275 : Blo 1570983 7554275 := bstep (se 1 (by rfl) ⟨5665706, by rfl⟩ : syracuseStep 7554275 = 11331413) B11331413
theorem B3228931 : Blo 1570983 3228931 := bstep (se 1 (by rfl) ⟨2421698, by rfl⟩ : syracuseStep 3228931 = 4843397) B4843397
theorem B2237825 : Blo 1570983 2237825 := bstep (se 2 (by rfl) ⟨839184, by rfl⟩ : syracuseStep 2237825 = 1678369) B1678369
theorem B12748229 : Blo 1570983 12748229 := bstep (se 4 (by rfl) ⟨1195146, by rfl⟩ : syracuseStep 12748229 = 2390293) B2390293
theorem B2237905 : Blo 1570983 2237905 := bstep (se 2 (by rfl) ⟨839214, by rfl⟩ : syracuseStep 2237905 = 1678429) B1678429
theorem B7955981 : Blo 1570983 7955981 := bstep (se 3 (by rfl) ⟨1491746, by rfl⟩ : syracuseStep 7955981 = 2983493) B2983493
theorem B12748357 : Blo 1570983 12748357 := bstep (se 4 (by rfl) ⟨1195158, by rfl⟩ : syracuseStep 12748357 = 2390317) B2390317
theorem B2688643 : Blo 1570983 2688643 := bstep (se 1 (by rfl) ⟨2016482, by rfl⟩ : syracuseStep 2688643 = 4032965) B4032965
theorem B5662349 : Blo 1570983 5662349 := bstep (se 3 (by rfl) ⟨1061690, by rfl⟩ : syracuseStep 5662349 = 2123381) B2123381
theorem B2016995 : Blo 1570983 2016995 := bstep (se 1 (by rfl) ⟨1512746, by rfl⟩ : syracuseStep 2016995 = 3025493) B3025493
theorem B4777741 : Blo 1570983 4777741 := bstep (se 3 (by rfl) ⟨895826, by rfl⟩ : syracuseStep 4777741 = 1791653) B1791653
theorem B5662477 : Blo 1570983 5662477 := bstep (se 3 (by rfl) ⟨1061714, by rfl⟩ : syracuseStep 5662477 = 2123429) B2123429
theorem B2983729 : Blo 1570983 2983729 := bstep (se 2 (by rfl) ⟨1118898, by rfl⟩ : syracuseStep 2983729 = 2237797) B2237797
theorem B5302097 : Blo 1570983 5302097 := bstep (se 2 (by rfl) ⟨1988286, by rfl⟩ : syracuseStep 5302097 = 3976573) B3976573
theorem B5375971 : Blo 1570983 5375971 := bstep (se 1 (by rfl) ⟨4031978, by rfl⟩ : syracuseStep 5375971 = 8063957) B8063957
theorem B4474865 : Blo 1570983 4474865 := bstep (se 2 (by rfl) ⟨1678074, by rfl⟩ : syracuseStep 4474865 = 3356149) B3356149
theorem B2517041 : Blo 1570983 2517041 := bstep (se 2 (by rfl) ⟨943890, by rfl⟩ : syracuseStep 2517041 = 1887781) B1887781
theorem B2984131 : Blo 1570983 2984131 := bstep (se 1 (by rfl) ⟨2238098, by rfl⟩ : syracuseStep 2984131 = 4476197) B4476197
theorem B2238691 : Blo 1570983 2238691 := bstep (se 1 (by rfl) ⟨1679018, by rfl⟩ : syracuseStep 2238691 = 3358037) B3358037
theorem B11929841 : Blo 1570983 11929841 := bstep (se 2 (by rfl) ⟨4473690, by rfl⟩ : syracuseStep 11929841 = 8947381) B8947381
theorem B2984177 : Blo 1570983 2984177 := bstep (se 2 (by rfl) ⟨1119066, by rfl⟩ : syracuseStep 2984177 = 2238133) B2238133
theorem B5302637 : Blo 1570983 5302637 := bstep (se 3 (by rfl) ⟨994244, by rfl⟩ : syracuseStep 5302637 = 1988489) B1988489
theorem B5302691 : Blo 1570983 5302691 := bstep (se 1 (by rfl) ⟨3977018, by rfl⟩ : syracuseStep 5302691 = 7954037) B7954037
theorem B5966243 : Blo 1570983 5966243 := bstep (se 1 (by rfl) ⟨4474682, by rfl⟩ : syracuseStep 5966243 = 8949365) B8949365
theorem B5966257 : Blo 1570983 5966257 := bstep (se 2 (by rfl) ⟨2237346, by rfl⟩ : syracuseStep 5966257 = 4474693) B4474693
theorem B2984465 : Blo 1570983 2984465 := bstep (se 2 (by rfl) ⟨1119174, by rfl⟩ : syracuseStep 2984465 = 2238349) B2238349
theorem B4475537 : Blo 1570983 4475537 := bstep (se 2 (by rfl) ⟨1678326, by rfl⟩ : syracuseStep 4475537 = 3356653) B3356653
theorem B5106349 : Blo 1570983 5106349 := bstep (se 3 (by rfl) ⟨957440, by rfl⟩ : syracuseStep 5106349 = 1914881) B1914881
theorem B5302961 : Blo 1570983 5302961 := bstep (se 2 (by rfl) ⟨1988610, by rfl⟩ : syracuseStep 5302961 = 3977221) B3977221
theorem B10070725 : Blo 1570983 10070725 := bstep (se 4 (by rfl) ⟨944130, by rfl⟩ : syracuseStep 10070725 = 1888261) B1888261
theorem B2763491 : Blo 1570983 2763491 := bstep (se 1 (by rfl) ⟨2072618, by rfl⟩ : syracuseStep 2763491 = 4145237) B4145237
theorem B2517779 : Blo 1570983 2517779 := bstep (se 1 (by rfl) ⟨1888334, by rfl⟩ : syracuseStep 2517779 = 3776669) B3776669
theorem B36285205 : Blo 1570983 36285205 := bstep (se 6 (by rfl) ⟨850434, by rfl⟩ : syracuseStep 36285205 = 1700869) B1700869
theorem B3025795 : Blo 1570983 3025795 := bstep (se 1 (by rfl) ⟨2269346, by rfl⟩ : syracuseStep 3025795 = 4538693) B4538693
theorem B8948657 : Blo 1570983 8948657 := bstep (se 2 (by rfl) ⟨3355746, by rfl⟩ : syracuseStep 8948657 = 6711493) B6711493
theorem B9956357 : Blo 1570983 9956357 := bstep (se 4 (by rfl) ⟨933408, by rfl⟩ : syracuseStep 9956357 = 1866817) B1866817
theorem B5303501 : Blo 1570983 5303501 := bstep (se 3 (by rfl) ⟨994406, by rfl⟩ : syracuseStep 5303501 = 1988813) B1988813
theorem B2985187 : Blo 1570983 2985187 := bstep (se 1 (by rfl) ⟨2238890, by rfl⟩ : syracuseStep 2985187 = 4477781) B4477781
theorem B5303555 : Blo 1570983 5303555 := bstep (se 1 (by rfl) ⟨3977666, by rfl⟩ : syracuseStep 5303555 = 7955333) B7955333
theorem B8629517 : Blo 1570983 8629517 := bstep (se 3 (by rfl) ⟨1618034, by rfl⟩ : syracuseStep 8629517 = 3236069) B3236069
theorem B4779395 : Blo 1570983 4779395 := bstep (se 1 (by rfl) ⟨3584546, by rfl⟩ : syracuseStep 4779395 = 7169093) B7169093
theorem B4476323 : Blo 1570983 4476323 := bstep (se 1 (by rfl) ⟨3357242, by rfl⟩ : syracuseStep 4476323 = 6714485) B6714485
theorem B5303825 : Blo 1570983 5303825 := bstep (se 2 (by rfl) ⟨1988934, by rfl⟩ : syracuseStep 5303825 = 3977869) B3977869
theorem B6459043 : Blo 1570983 6459043 := bstep (se 1 (by rfl) ⟨4844282, by rfl⟩ : syracuseStep 6459043 = 9688565) B9688565
theorem B4476653 : Blo 1570983 4476653 := bstep (se 3 (by rfl) ⟨839372, by rfl⟩ : syracuseStep 4476653 = 1678745) B1678745
theorem B2518771 : Blo 1570983 2518771 := bstep (se 1 (by rfl) ⟨1889078, by rfl⟩ : syracuseStep 2518771 = 3778157) B3778157
theorem B1593091 : Blo 1570983 1593091 := bstep (se 1 (by rfl) ⟨1194818, by rfl⟩ : syracuseStep 1593091 = 2389637) B2389637
theorem B3977009 : Blo 1570983 3977009 := bstep (se 2 (by rfl) ⟨1491378, by rfl⟩ : syracuseStep 3977009 = 2982757) B2982757
theorem B4476721 : Blo 1570983 4476721 := bstep (se 2 (by rfl) ⟨1678770, by rfl⟩ : syracuseStep 4476721 = 3357541) B3357541
theorem B3977059 : Blo 1570983 3977059 := bstep (se 1 (by rfl) ⟨2982794, by rfl⟩ : syracuseStep 3977059 = 5965589) B5965589
theorem B5967715 : Blo 1570983 5967715 := bstep (se 1 (by rfl) ⟨4475786, by rfl⟩ : syracuseStep 5967715 = 8951573) B8951573
theorem B3977201 : Blo 1570983 3977201 := bstep (se 2 (by rfl) ⟨1491450, by rfl⟩ : syracuseStep 3977201 = 2982901) B2982901
theorem B3584017 : Blo 1570983 3584017 := bstep (se 2 (by rfl) ⟨1344006, by rfl⟩ : syracuseStep 3584017 = 2688013) B2688013
theorem B5304365 : Blo 1570983 5304365 := bstep (se 3 (by rfl) ⟨994568, by rfl⟩ : syracuseStep 5304365 = 1989137) B1989137
theorem B4476995 : Blo 1570983 4476995 := bstep (se 1 (by rfl) ⟨3357746, by rfl⟩ : syracuseStep 4476995 = 6715493) B6715493
theorem B3534929 : Blo 1570983 3534929 := bstep (se 2 (by rfl) ⟨1325598, by rfl⟩ : syracuseStep 3534929 = 2651197) B2651197
theorem B3534947 : Blo 1570983 3534947 := bstep (se 1 (by rfl) ⟨2651210, by rfl⟩ : syracuseStep 3534947 = 5302421) B5302421
theorem B5304419 : Blo 1570983 5304419 := bstep (se 1 (by rfl) ⟨3978314, by rfl⟩ : syracuseStep 5304419 = 7956629) B7956629
theorem B8950115 : Blo 1570983 8950115 := bstep (se 1 (by rfl) ⟨6712586, by rfl⟩ : syracuseStep 8950115 = 13425173) B13425173
theorem B3535217 : Blo 1570983 3535217 := bstep (se 2 (by rfl) ⟨1325706, by rfl⟩ : syracuseStep 3535217 = 2651413) B2651413
theorem B5304689 : Blo 1570983 5304689 := bstep (se 2 (by rfl) ⟨1989258, by rfl⟩ : syracuseStep 5304689 = 3978517) B3978517
theorem B7958897 : Blo 1570983 7958897 := bstep (se 2 (by rfl) ⟨2984586, by rfl⟩ : syracuseStep 7958897 = 5969173) B5969173
theorem B3535235 : Blo 1570983 3535235 := bstep (se 1 (by rfl) ⟨2651426, by rfl⟩ : syracuseStep 3535235 = 5302853) B5302853
theorem B5034467 : Blo 1570983 5034467 := bstep (se 1 (by rfl) ⟨3775850, by rfl⟩ : syracuseStep 5034467 = 7551701) B7551701
theorem B2552305 : Blo 1570983 2552305 := bstep (se 2 (by rfl) ⟨957114, by rfl⟩ : syracuseStep 2552305 = 1914229) B1914229
theorem B4248145 : Blo 1570983 4248145 := bstep (se 2 (by rfl) ⟨1593054, by rfl⟩ : syracuseStep 4248145 = 3186109) B3186109
theorem B5034595 : Blo 1570983 5034595 := bstep (se 1 (by rfl) ⟨3775946, by rfl⟩ : syracuseStep 5034595 = 7551893) B7551893
theorem B3535505 : Blo 1570983 3535505 := bstep (se 2 (by rfl) ⟨1325814, by rfl⟩ : syracuseStep 3535505 = 2651629) B2651629
theorem B1888915 : Blo 1570983 1888915 := bstep (se 1 (by rfl) ⟨1416686, by rfl⟩ : syracuseStep 1888915 = 2833373) B2833373
theorem B3535523 : Blo 1570983 3535523 := bstep (se 1 (by rfl) ⟨2651642, by rfl⟩ : syracuseStep 3535523 = 5303285) B5303285
theorem B4780721 : Blo 1570983 4780721 := bstep (se 2 (by rfl) ⟨1792770, by rfl⟩ : syracuseStep 4780721 = 3585541) B3585541
theorem B7549645 : Blo 1570983 7549645 := bstep (se 3 (by rfl) ⟨1415558, by rfl⟩ : syracuseStep 7549645 = 2831117) B2831117
theorem B5034737 : Blo 1570983 5034737 := bstep (se 2 (by rfl) ⟨1888026, by rfl⟩ : syracuseStep 5034737 = 3776053) B3776053
theorem B1889011 : Blo 1570983 1889011 := bstep (se 1 (by rfl) ⟨1416758, by rfl⟩ : syracuseStep 1889011 = 2833517) B2833517
theorem B5034851 : Blo 1570983 5034851 := bstep (se 1 (by rfl) ⟨3776138, by rfl⟩ : syracuseStep 5034851 = 7552277) B7552277
theorem B6714211 : Blo 1570983 6714211 := bstep (se 1 (by rfl) ⟨5035658, by rfl⟩ : syracuseStep 6714211 = 10071317) B10071317
theorem B5305229 : Blo 1570983 5305229 := bstep (se 3 (by rfl) ⟨994730, by rfl⟩ : syracuseStep 5305229 = 1989461) B1989461
theorem B4477837 : Blo 1570983 4477837 := bstep (se 3 (by rfl) ⟨839594, by rfl⟩ : syracuseStep 4477837 = 1679189) B1679189
theorem B3535793 : Blo 1570983 3535793 := bstep (se 2 (by rfl) ⟨1325922, by rfl⟩ : syracuseStep 3535793 = 2651845) B2651845
theorem B3535811 : Blo 1570983 3535811 := bstep (se 1 (by rfl) ⟨2651858, by rfl⟩ : syracuseStep 3535811 = 5303717) B5303717
theorem B5305283 : Blo 1570983 5305283 := bstep (se 1 (by rfl) ⟨3978962, by rfl⟩ : syracuseStep 5305283 = 7957925) B7957925
theorem B2651089 : Blo 1570983 2651089 := bstep (se 2 (by rfl) ⟨994158, by rfl⟩ : syracuseStep 2651089 = 1988317) B1988317
theorem B3978193 : Blo 1570983 3978193 := bstep (se 2 (by rfl) ⟨1491822, by rfl⟩ : syracuseStep 3978193 = 2983645) B2983645
theorem B2651123 : Blo 1570983 2651123 := bstep (se 1 (by rfl) ⟨1988342, by rfl⟩ : syracuseStep 2651123 = 3976685) B3976685
theorem B5379089 : Blo 1570983 5379089 := bstep (se 2 (by rfl) ⟨2017158, by rfl⟩ : syracuseStep 5379089 = 4034317) B4034317
theorem B2651251 : Blo 1570983 2651251 := bstep (se 1 (by rfl) ⟨1988438, by rfl⟩ : syracuseStep 2651251 = 3976877) B3976877
theorem B3536081 : Blo 1570983 3536081 := bstep (se 2 (by rfl) ⟨1326030, by rfl⟩ : syracuseStep 3536081 = 2652061) B2652061
theorem B5305553 : Blo 1570983 5305553 := bstep (se 2 (by rfl) ⟨1989582, by rfl⟩ : syracuseStep 5305553 = 3979165) B3979165
theorem B3536099 : Blo 1570983 3536099 := bstep (se 1 (by rfl) ⟨2652074, by rfl⟩ : syracuseStep 3536099 = 5304149) B5304149
theorem B3978467 : Blo 1570983 3978467 := bstep (se 1 (by rfl) ⟨2983850, by rfl⟩ : syracuseStep 3978467 = 5967701) B5967701
theorem B2356481 : Blo 1570983 2356481 := bstep (se 2 (by rfl) ⟨883680, by rfl⟩ : syracuseStep 2356481 = 1767361) B1767361
theorem B2651393 : Blo 1570983 2651393 := bstep (se 2 (by rfl) ⟨994272, by rfl⟩ : syracuseStep 2651393 = 1988545) B1988545
theorem B2356499 : Blo 1570983 2356499 := bstep (se 1 (by rfl) ⟨1767374, by rfl⟩ : syracuseStep 2356499 = 3534749) B3534749
theorem B2356529 : Blo 1570983 2356529 := bstep (se 2 (by rfl) ⟨883698, by rfl⟩ : syracuseStep 2356529 = 1767397) B1767397
theorem B2356547 : Blo 1570983 2356547 := bstep (se 1 (by rfl) ⟨1767410, by rfl⟩ : syracuseStep 2356547 = 3534821) B3534821
theorem B2356577 : Blo 1570983 2356577 := bstep (se 2 (by rfl) ⟨883716, by rfl⟩ : syracuseStep 2356577 = 1767433) B1767433
theorem B10073443 : Blo 1570983 10073443 := bstep (se 1 (by rfl) ⟨7555082, by rfl⟩ : syracuseStep 10073443 = 15110165) B15110165
theorem B2356595 : Blo 1570983 2356595 := bstep (se 1 (by rfl) ⟨1767446, by rfl⟩ : syracuseStep 2356595 = 3534893) B3534893
theorem B2651521 : Blo 1570983 2651521 := bstep (se 2 (by rfl) ⟨994320, by rfl⟩ : syracuseStep 2651521 = 1988641) B1988641
theorem B2356625 : Blo 1570983 2356625 := bstep (se 2 (by rfl) ⟨883734, by rfl⟩ : syracuseStep 2356625 = 1767469) B1767469
theorem B2356643 : Blo 1570983 2356643 := bstep (se 1 (by rfl) ⟨1767482, by rfl⟩ : syracuseStep 2356643 = 3534965) B3534965
theorem B2651555 : Blo 1570983 2651555 := bstep (se 1 (by rfl) ⟨1988666, by rfl⟩ : syracuseStep 2651555 = 3977333) B3977333
theorem B3978659 : Blo 1570983 3978659 := bstep (se 1 (by rfl) ⟨2983994, by rfl⟩ : syracuseStep 3978659 = 5967989) B5967989
theorem B2356673 : Blo 1570983 2356673 := bstep (se 2 (by rfl) ⟨883752, by rfl⟩ : syracuseStep 2356673 = 1767505) B1767505
theorem B2356691 : Blo 1570983 2356691 := bstep (se 1 (by rfl) ⟨1767518, by rfl⟩ : syracuseStep 2356691 = 3535037) B3535037
theorem B2356721 : Blo 1570983 2356721 := bstep (se 2 (by rfl) ⟨883770, by rfl⟩ : syracuseStep 2356721 = 1767541) B1767541
theorem B3536369 : Blo 1570983 3536369 := bstep (se 2 (by rfl) ⟨1326138, by rfl⟩ : syracuseStep 3536369 = 2652277) B2652277
theorem B2356739 : Blo 1570983 2356739 := bstep (se 1 (by rfl) ⟨1767554, by rfl⟩ : syracuseStep 2356739 = 3535109) B3535109
theorem B3536387 : Blo 1570983 3536387 := bstep (se 1 (by rfl) ⟨2652290, by rfl⟩ : syracuseStep 3536387 = 5304581) B5304581
theorem B2356769 : Blo 1570983 2356769 := bstep (se 2 (by rfl) ⟨883788, by rfl⟩ : syracuseStep 2356769 = 1767577) B1767577
theorem B2651683 : Blo 1570983 2651683 := bstep (se 1 (by rfl) ⟨1988762, by rfl⟩ : syracuseStep 2651683 = 3977525) B3977525
theorem B2356787 : Blo 1570983 2356787 := bstep (se 1 (by rfl) ⟨1767590, by rfl⟩ : syracuseStep 2356787 = 3535181) B3535181
theorem B7657037 : Blo 1570983 7657037 := bstep (se 3 (by rfl) ⟨1435694, by rfl⟩ : syracuseStep 7657037 = 2871389) B2871389
theorem B2356817 : Blo 1570983 2356817 := bstep (se 2 (by rfl) ⟨883806, by rfl⟩ : syracuseStep 2356817 = 1767613) B1767613
theorem B1791571 : Blo 1570983 1791571 := bstep (se 1 (by rfl) ⟨1343678, by rfl⟩ : syracuseStep 1791571 = 2687357) B2687357
theorem B2356835 : Blo 1570983 2356835 := bstep (se 1 (by rfl) ⟨1767626, by rfl⟩ : syracuseStep 2356835 = 3535253) B3535253
theorem B40818289 : Blo 1570983 40818289 := bstep (se 2 (by rfl) ⟨15306858, by rfl⟩ : syracuseStep 40818289 = 30613717) B30613717
theorem B2356865 : Blo 1570983 2356865 := bstep (se 2 (by rfl) ⟨883824, by rfl⟩ : syracuseStep 2356865 = 1767649) B1767649
theorem B2832017 : Blo 1570983 2832017 := bstep (se 2 (by rfl) ⟨1062006, by rfl⟩ : syracuseStep 2832017 = 2124013) B2124013
theorem B2356883 : Blo 1570983 2356883 := bstep (se 1 (by rfl) ⟨1767662, by rfl⟩ : syracuseStep 2356883 = 3535325) B3535325
theorem B2356913 : Blo 1570983 2356913 := bstep (se 2 (by rfl) ⟨883842, by rfl⟩ : syracuseStep 2356913 = 1767685) B1767685
theorem B2651825 : Blo 1570983 2651825 := bstep (se 2 (by rfl) ⟨994434, by rfl⟩ : syracuseStep 2651825 = 1988869) B1988869
theorem B2356931 : Blo 1570983 2356931 := bstep (se 1 (by rfl) ⟨1767698, by rfl⟩ : syracuseStep 2356931 = 3535397) B3535397
theorem B2356961 : Blo 1570983 2356961 := bstep (se 2 (by rfl) ⟨883860, by rfl⟩ : syracuseStep 2356961 = 1767721) B1767721
theorem B5306093 : Blo 1570983 5306093 := bstep (se 3 (by rfl) ⟨994892, by rfl⟩ : syracuseStep 5306093 = 1989785) B1989785
theorem B2356979 : Blo 1570983 2356979 := bstep (se 1 (by rfl) ⟨1767734, by rfl⟩ : syracuseStep 2356979 = 3535469) B3535469
theorem B2357009 : Blo 1570983 2357009 := bstep (se 2 (by rfl) ⟨883878, by rfl⟩ : syracuseStep 2357009 = 1767757) B1767757
theorem B3536657 : Blo 1570983 3536657 := bstep (se 2 (by rfl) ⟨1326246, by rfl⟩ : syracuseStep 3536657 = 2652493) B2652493
theorem B2357027 : Blo 1570983 2357027 := bstep (se 1 (by rfl) ⟨1767770, by rfl⟩ : syracuseStep 2357027 = 3535541) B3535541
theorem B3536675 : Blo 1570983 3536675 := bstep (se 1 (by rfl) ⟨2652506, by rfl⟩ : syracuseStep 3536675 = 5305013) B5305013
theorem B5306147 : Blo 1570983 5306147 := bstep (se 1 (by rfl) ⟨3979610, by rfl⟩ : syracuseStep 5306147 = 7959221) B7959221
theorem B7960355 : Blo 1570983 7960355 := bstep (se 1 (by rfl) ⟨5970266, by rfl⟩ : syracuseStep 7960355 = 11940533) B11940533
theorem B2651953 : Blo 1570983 2651953 := bstep (se 2 (by rfl) ⟨994482, by rfl⟩ : syracuseStep 2651953 = 1988965) B1988965
theorem B2357057 : Blo 1570983 2357057 := bstep (se 2 (by rfl) ⟨883896, by rfl⟩ : syracuseStep 2357057 = 1767793) B1767793
theorem B2357075 : Blo 1570983 2357075 := bstep (se 1 (by rfl) ⟨1767806, by rfl⟩ : syracuseStep 2357075 = 3535613) B3535613
theorem B2651987 : Blo 1570983 2651987 := bstep (se 1 (by rfl) ⟨1988990, by rfl⟩ : syracuseStep 2651987 = 3977981) B3977981
theorem B2357105 : Blo 1570983 2357105 := bstep (se 2 (by rfl) ⟨883914, by rfl⟩ : syracuseStep 2357105 = 1767829) B1767829
theorem B2357123 : Blo 1570983 2357123 := bstep (se 1 (by rfl) ⟨1767842, by rfl⟩ : syracuseStep 2357123 = 3535685) B3535685
theorem B2357153 : Blo 1570983 2357153 := bstep (se 2 (by rfl) ⟨883932, by rfl⟩ : syracuseStep 2357153 = 1767865) B1767865
theorem B2357171 : Blo 1570983 2357171 := bstep (se 1 (by rfl) ⟨1767878, by rfl⟩ : syracuseStep 2357171 = 3535757) B3535757
theorem B2357201 : Blo 1570983 2357201 := bstep (se 2 (by rfl) ⟨883950, by rfl⟩ : syracuseStep 2357201 = 1767901) B1767901
theorem B1767379 : Blo 1570983 1767379 := bstep (se 1 (by rfl) ⟨1325534, by rfl⟩ : syracuseStep 1767379 = 2651069) B2651069
theorem B2652115 : Blo 1570983 2652115 := bstep (se 1 (by rfl) ⟨1989086, by rfl⟩ : syracuseStep 2652115 = 3978173) B3978173
theorem B2357219 : Blo 1570983 2357219 := bstep (se 1 (by rfl) ⟨1767914, by rfl⟩ : syracuseStep 2357219 = 3535829) B3535829
theorem B2357249 : Blo 1570983 2357249 := bstep (se 2 (by rfl) ⟨883968, by rfl⟩ : syracuseStep 2357249 = 1767937) B1767937
theorem B5969933 : Blo 1570983 5969933 := bstep (se 3 (by rfl) ⟨1119362, by rfl⟩ : syracuseStep 5969933 = 2238725) B2238725
theorem B2357267 : Blo 1570983 2357267 := bstep (se 1 (by rfl) ⟨1767950, by rfl⟩ : syracuseStep 2357267 = 3535901) B3535901
theorem B2357297 : Blo 1570983 2357297 := bstep (se 2 (by rfl) ⟨883986, by rfl⟩ : syracuseStep 2357297 = 1767973) B1767973
theorem B3536945 : Blo 1570983 3536945 := bstep (se 2 (by rfl) ⟨1326354, by rfl⟩ : syracuseStep 3536945 = 2652709) B2652709
theorem B5306417 : Blo 1570983 5306417 := bstep (se 2 (by rfl) ⟨1989906, by rfl⟩ : syracuseStep 5306417 = 3979813) B3979813
theorem B2357315 : Blo 1570983 2357315 := bstep (se 1 (by rfl) ⟨1767986, by rfl⟩ : syracuseStep 2357315 = 3535973) B3535973
theorem B3536963 : Blo 1570983 3536963 := bstep (se 1 (by rfl) ⟨2652722, by rfl⟩ : syracuseStep 3536963 = 5305445) B5305445
theorem B2357345 : Blo 1570983 2357345 := bstep (se 2 (by rfl) ⟨884004, by rfl⟩ : syracuseStep 2357345 = 1768009) B1768009
theorem B2652257 : Blo 1570983 2652257 := bstep (se 2 (by rfl) ⟨994596, by rfl⟩ : syracuseStep 2652257 = 1989193) B1989193
theorem B1767523 : Blo 1570983 1767523 := bstep (se 1 (by rfl) ⟨1325642, by rfl⟩ : syracuseStep 1767523 = 2651285) B2651285
theorem B1988707 : Blo 1570983 1988707 := bstep (se 1 (by rfl) ⟨1491530, by rfl⟩ : syracuseStep 1988707 = 2983061) B2983061
theorem B7166065 : Blo 1570983 7166065 := bstep (se 2 (by rfl) ⟨2687274, by rfl⟩ : syracuseStep 7166065 = 5374549) B5374549
theorem B2357363 : Blo 1570983 2357363 := bstep (se 1 (by rfl) ⟨1768022, by rfl⟩ : syracuseStep 2357363 = 3536045) B3536045
theorem B2357393 : Blo 1570983 2357393 := bstep (se 2 (by rfl) ⟨884022, by rfl⟩ : syracuseStep 2357393 = 1768045) B1768045
theorem B2357411 : Blo 1570983 2357411 := bstep (se 1 (by rfl) ⟨1768058, by rfl⟩ : syracuseStep 2357411 = 3536117) B3536117
theorem B1570995 : Blo 1570983 1570995 := bstep (se 1 (by rfl) ⟨1178246, by rfl⟩ : syracuseStep 1570995 = 2356493) B2356493
theorem B2357441 : Blo 1570983 2357441 := bstep (se 2 (by rfl) ⟨884040, by rfl⟩ : syracuseStep 2357441 = 1768081) B1768081
theorem B1571011 : Blo 1570983 1571011 := bstep (se 1 (by rfl) ⟨1178258, by rfl⟩ : syracuseStep 1571011 = 2356517) B2356517
theorem B1988803 : Blo 1570983 1988803 := bstep (se 1 (by rfl) ⟨1491602, by rfl⟩ : syracuseStep 1988803 = 2983205) B2983205
theorem B1571027 : Blo 1570983 1571027 := bstep (se 1 (by rfl) ⟨1178270, by rfl⟩ : syracuseStep 1571027 = 2356541) B2356541
theorem B2357459 : Blo 1570983 2357459 := bstep (se 1 (by rfl) ⟨1768094, by rfl⟩ : syracuseStep 2357459 = 3536189) B3536189
theorem B2652385 : Blo 1570983 2652385 := bstep (se 2 (by rfl) ⟨994644, by rfl⟩ : syracuseStep 2652385 = 1989289) B1989289
theorem B1571043 : Blo 1570983 1571043 := bstep (se 1 (by rfl) ⟨1178282, by rfl⟩ : syracuseStep 1571043 = 2356565) B2356565
theorem B8493283 : Blo 1570983 8493283 := bstep (se 1 (by rfl) ⟨6369962, by rfl⟩ : syracuseStep 8493283 = 12739925) B12739925
theorem B2357489 : Blo 1570983 2357489 := bstep (se 2 (by rfl) ⟨884058, by rfl⟩ : syracuseStep 2357489 = 1768117) B1768117
theorem B1571059 : Blo 1570983 1571059 := bstep (se 1 (by rfl) ⟨1178294, by rfl⟩ : syracuseStep 1571059 = 2356589) B2356589
theorem B1767667 : Blo 1570983 1767667 := bstep (se 1 (by rfl) ⟨1325750, by rfl⟩ : syracuseStep 1767667 = 2651501) B2651501
theorem B2652419 : Blo 1570983 2652419 := bstep (se 1 (by rfl) ⟨1989314, by rfl⟩ : syracuseStep 2652419 = 3978629) B3978629
theorem B1571075 : Blo 1570983 1571075 := bstep (se 1 (by rfl) ⟨1178306, by rfl⟩ : syracuseStep 1571075 = 2356613) B2356613
theorem B2357507 : Blo 1570983 2357507 := bstep (se 1 (by rfl) ⟨1768130, by rfl⟩ : syracuseStep 2357507 = 3536261) B3536261
theorem B1571091 : Blo 1570983 1571091 := bstep (se 1 (by rfl) ⟨1178318, by rfl⟩ : syracuseStep 1571091 = 2356637) B2356637
theorem B2357537 : Blo 1570983 2357537 := bstep (se 2 (by rfl) ⟨884076, by rfl⟩ : syracuseStep 2357537 = 1768153) B1768153
theorem B3774755 : Blo 1570983 3774755 := bstep (se 1 (by rfl) ⟨2831066, by rfl⟩ : syracuseStep 3774755 = 5662133) B5662133
theorem B1571107 : Blo 1570983 1571107 := bstep (se 1 (by rfl) ⟨1178330, by rfl⟩ : syracuseStep 1571107 = 2356661) B2356661
theorem B3356977 : Blo 1570983 3356977 := bstep (se 2 (by rfl) ⟨1258866, by rfl⟩ : syracuseStep 3356977 = 2517733) B2517733
theorem B1571123 : Blo 1570983 1571123 := bstep (se 1 (by rfl) ⟨1178342, by rfl⟩ : syracuseStep 1571123 = 2356685) B2356685
theorem B2357555 : Blo 1570983 2357555 := bstep (se 1 (by rfl) ⟨1768166, by rfl⟩ : syracuseStep 2357555 = 3536333) B3536333
theorem B1571139 : Blo 1570983 1571139 := bstep (se 1 (by rfl) ⟨1178354, by rfl⟩ : syracuseStep 1571139 = 2356709) B2356709
theorem B2357585 : Blo 1570983 2357585 := bstep (se 2 (by rfl) ⟨884094, by rfl⟩ : syracuseStep 2357585 = 1768189) B1768189
theorem B3537233 : Blo 1570983 3537233 := bstep (se 2 (by rfl) ⟨1326462, by rfl⟩ : syracuseStep 3537233 = 2652925) B2652925
theorem B1571155 : Blo 1570983 1571155 := bstep (se 1 (by rfl) ⟨1178366, by rfl⟩ : syracuseStep 1571155 = 2356733) B2356733
theorem B3979601 : Blo 1570983 3979601 := bstep (se 2 (by rfl) ⟨1492350, by rfl⟩ : syracuseStep 3979601 = 2984701) B2984701
theorem B1571171 : Blo 1570983 1571171 := bstep (se 1 (by rfl) ⟨1178378, by rfl⟩ : syracuseStep 1571171 = 2356757) B2356757
theorem B2357603 : Blo 1570983 2357603 := bstep (se 1 (by rfl) ⟨1768202, by rfl⟩ : syracuseStep 2357603 = 3536405) B3536405
theorem B3537251 : Blo 1570983 3537251 := bstep (se 1 (by rfl) ⟨2652938, by rfl⟩ : syracuseStep 3537251 = 5305877) B5305877
theorem B1571187 : Blo 1570983 1571187 := bstep (se 1 (by rfl) ⟨1178390, by rfl⟩ : syracuseStep 1571187 = 2356781) B2356781
theorem B2357633 : Blo 1570983 2357633 := bstep (se 2 (by rfl) ⟨884112, by rfl⟩ : syracuseStep 2357633 = 1768225) B1768225
theorem B1571203 : Blo 1570983 1571203 := bstep (se 1 (by rfl) ⟨1178402, by rfl⟩ : syracuseStep 1571203 = 2356805) B2356805
theorem B1767811 : Blo 1570983 1767811 := bstep (se 1 (by rfl) ⟨1325858, by rfl⟩ : syracuseStep 1767811 = 2651717) B2651717
theorem B2652547 : Blo 1570983 2652547 := bstep (se 1 (by rfl) ⟨1989410, by rfl⟩ : syracuseStep 2652547 = 3978821) B3978821
theorem B3979651 : Blo 1570983 3979651 := bstep (se 1 (by rfl) ⟨2984738, by rfl⟩ : syracuseStep 3979651 = 5969477) B5969477
theorem B22092173 : Blo 1570983 22092173 := bstep (se 3 (by rfl) ⟨4142282, by rfl⟩ : syracuseStep 22092173 = 8284565) B8284565
theorem B1571219 : Blo 1570983 1571219 := bstep (se 1 (by rfl) ⟨1178414, by rfl⟩ : syracuseStep 1571219 = 2356829) B2356829
theorem B2357651 : Blo 1570983 2357651 := bstep (se 1 (by rfl) ⟨1768238, by rfl⟩ : syracuseStep 2357651 = 3536477) B3536477
theorem B1571235 : Blo 1570983 1571235 := bstep (se 1 (by rfl) ⟨1178426, by rfl⟩ : syracuseStep 1571235 = 2356853) B2356853
theorem B2357681 : Blo 1570983 2357681 := bstep (se 2 (by rfl) ⟨884130, by rfl⟩ : syracuseStep 2357681 = 1768261) B1768261
theorem B1571251 : Blo 1570983 1571251 := bstep (se 1 (by rfl) ⟨1178438, by rfl⟩ : syracuseStep 1571251 = 2356877) B2356877
theorem B1571267 : Blo 1570983 1571267 := bstep (se 1 (by rfl) ⟨1178450, by rfl⟩ : syracuseStep 1571267 = 2356901) B2356901
theorem B2357699 : Blo 1570983 2357699 := bstep (se 1 (by rfl) ⟨1768274, by rfl⟩ : syracuseStep 2357699 = 3536549) B3536549
theorem B1571283 : Blo 1570983 1571283 := bstep (se 1 (by rfl) ⟨1178462, by rfl⟩ : syracuseStep 1571283 = 2356925) B2356925
theorem B2357729 : Blo 1570983 2357729 := bstep (se 2 (by rfl) ⟨884148, by rfl⟩ : syracuseStep 2357729 = 1768297) B1768297
theorem B1571299 : Blo 1570983 1571299 := bstep (se 1 (by rfl) ⟨1178474, by rfl⟩ : syracuseStep 1571299 = 2356949) B2356949
theorem B9075185 : Blo 1570983 9075185 := bstep (se 2 (by rfl) ⟨3403194, by rfl⟩ : syracuseStep 9075185 = 6806389) B6806389
theorem B1571315 : Blo 1570983 1571315 := bstep (se 1 (by rfl) ⟨1178486, by rfl⟩ : syracuseStep 1571315 = 2356973) B2356973
theorem B2357747 : Blo 1570983 2357747 := bstep (se 1 (by rfl) ⟨1768310, by rfl⟩ : syracuseStep 2357747 = 3536621) B3536621
theorem B1571331 : Blo 1570983 1571331 := bstep (se 1 (by rfl) ⟨1178498, by rfl⟩ : syracuseStep 1571331 = 2356997) B2356997
theorem B2357777 : Blo 1570983 2357777 := bstep (se 2 (by rfl) ⟨884166, by rfl⟩ : syracuseStep 2357777 = 1768333) B1768333
theorem B1571347 : Blo 1570983 1571347 := bstep (se 1 (by rfl) ⟨1178510, by rfl⟩ : syracuseStep 1571347 = 2357021) B2357021
theorem B1767955 : Blo 1570983 1767955 := bstep (se 1 (by rfl) ⟨1325966, by rfl⟩ : syracuseStep 1767955 = 2651933) B2651933
theorem B2652689 : Blo 1570983 2652689 := bstep (se 2 (by rfl) ⟨994758, by rfl⟩ : syracuseStep 2652689 = 1989517) B1989517
theorem B3979793 : Blo 1570983 3979793 := bstep (se 2 (by rfl) ⟨1492422, by rfl⟩ : syracuseStep 3979793 = 2984845) B2984845
theorem B2390561 : Blo 1570983 2390561 := bstep (se 2 (by rfl) ⟨896460, by rfl⟩ : syracuseStep 2390561 = 1792921) B1792921
theorem B1571363 : Blo 1570983 1571363 := bstep (se 1 (by rfl) ⟨1178522, by rfl⟩ : syracuseStep 1571363 = 2357045) B2357045
theorem B2357795 : Blo 1570983 2357795 := bstep (se 1 (by rfl) ⟨1768346, by rfl⟩ : syracuseStep 2357795 = 3536693) B3536693
theorem B5036593 : Blo 1570983 5036593 := bstep (se 2 (by rfl) ⟨1888722, by rfl⟩ : syracuseStep 5036593 = 3777445) B3777445
theorem B1571379 : Blo 1570983 1571379 := bstep (se 1 (by rfl) ⟨1178534, by rfl⟩ : syracuseStep 1571379 = 2357069) B2357069
theorem B2357825 : Blo 1570983 2357825 := bstep (se 2 (by rfl) ⟨884184, by rfl⟩ : syracuseStep 2357825 = 1768369) B1768369
theorem B1571395 : Blo 1570983 1571395 := bstep (se 1 (by rfl) ⟨1178546, by rfl⟩ : syracuseStep 1571395 = 2357093) B2357093
theorem B2390609 : Blo 1570983 2390609 := bstep (se 2 (by rfl) ⟨896478, by rfl⟩ : syracuseStep 2390609 = 1792957) B1792957
theorem B5306957 : Blo 1570983 5306957 := bstep (se 3 (by rfl) ⟨995054, by rfl⟩ : syracuseStep 5306957 = 1990109) B1990109
theorem B1571411 : Blo 1570983 1571411 := bstep (se 1 (by rfl) ⟨1178558, by rfl⟩ : syracuseStep 1571411 = 2357117) B2357117
theorem B2357843 : Blo 1570983 2357843 := bstep (se 1 (by rfl) ⟨1768382, by rfl⟩ : syracuseStep 2357843 = 3536765) B3536765
theorem B1571427 : Blo 1570983 1571427 := bstep (se 1 (by rfl) ⟨1178570, by rfl⟩ : syracuseStep 1571427 = 2357141) B2357141
theorem B2357873 : Blo 1570983 2357873 := bstep (se 2 (by rfl) ⟨884202, by rfl⟩ : syracuseStep 2357873 = 1768405) B1768405
theorem B3537521 : Blo 1570983 3537521 := bstep (se 2 (by rfl) ⟨1326570, by rfl⟩ : syracuseStep 3537521 = 2653141) B2653141
theorem B1571443 : Blo 1570983 1571443 := bstep (se 1 (by rfl) ⟨1178582, by rfl⟩ : syracuseStep 1571443 = 2357165) B2357165
theorem B1571459 : Blo 1570983 1571459 := bstep (se 1 (by rfl) ⟨1178594, by rfl⟩ : syracuseStep 1571459 = 2357189) B2357189
theorem B2357891 : Blo 1570983 2357891 := bstep (se 1 (by rfl) ⟨1768418, by rfl⟩ : syracuseStep 2357891 = 3536837) B3536837
theorem B3537539 : Blo 1570983 3537539 := bstep (se 1 (by rfl) ⟨2653154, by rfl⟩ : syracuseStep 3537539 = 5306309) B5306309
theorem B5307011 : Blo 1570983 5307011 := bstep (se 1 (by rfl) ⟨3980258, by rfl⟩ : syracuseStep 5307011 = 7960517) B7960517
theorem B1571475 : Blo 1570983 1571475 := bstep (se 1 (by rfl) ⟨1178606, by rfl⟩ : syracuseStep 1571475 = 2357213) B2357213
theorem B2652817 : Blo 1570983 2652817 := bstep (se 2 (by rfl) ⟨994806, by rfl⟩ : syracuseStep 2652817 = 1989613) B1989613
theorem B2357921 : Blo 1570983 2357921 := bstep (se 2 (by rfl) ⟨884220, by rfl⟩ : syracuseStep 2357921 = 1768441) B1768441
theorem B3775139 : Blo 1570983 3775139 := bstep (se 1 (by rfl) ⟨2831354, by rfl⟩ : syracuseStep 3775139 = 5662709) B5662709
theorem B1571491 : Blo 1570983 1571491 := bstep (se 1 (by rfl) ⟨1178618, by rfl⟩ : syracuseStep 1571491 = 2357237) B2357237
theorem B1768099 : Blo 1570983 1768099 := bstep (se 1 (by rfl) ⟨1326074, by rfl⟩ : syracuseStep 1768099 = 2652149) B2652149
theorem B1571507 : Blo 1570983 1571507 := bstep (se 1 (by rfl) ⟨1178630, by rfl⟩ : syracuseStep 1571507 = 2357261) B2357261
theorem B1989299 : Blo 1570983 1989299 := bstep (se 1 (by rfl) ⟨1491974, by rfl⟩ : syracuseStep 1989299 = 2983949) B2983949
theorem B2357939 : Blo 1570983 2357939 := bstep (se 1 (by rfl) ⟨1768454, by rfl⟩ : syracuseStep 2357939 = 3536909) B3536909
theorem B2652851 : Blo 1570983 2652851 := bstep (se 1 (by rfl) ⟨1989638, by rfl⟩ : syracuseStep 2652851 = 3979277) B3979277
theorem B1571523 : Blo 1570983 1571523 := bstep (se 1 (by rfl) ⟨1178642, by rfl⟩ : syracuseStep 1571523 = 2357285) B2357285
theorem B3357379 : Blo 1570983 3357379 := bstep (se 1 (by rfl) ⟨2518034, by rfl⟩ : syracuseStep 3357379 = 5036069) B5036069
theorem B2357969 : Blo 1570983 2357969 := bstep (se 2 (by rfl) ⟨884238, by rfl⟩ : syracuseStep 2357969 = 1768477) B1768477
theorem B1571539 : Blo 1570983 1571539 := bstep (se 1 (by rfl) ⟨1178654, by rfl⟩ : syracuseStep 1571539 = 2357309) B2357309
theorem B25484003 : Blo 1570983 25484003 := bstep (se 1 (by rfl) ⟨19113002, by rfl⟩ : syracuseStep 25484003 = 38226005) B38226005
theorem B1571555 : Blo 1570983 1571555 := bstep (se 1 (by rfl) ⟨1178666, by rfl⟩ : syracuseStep 1571555 = 2357333) B2357333
theorem B2357987 : Blo 1570983 2357987 := bstep (se 1 (by rfl) ⟨1768490, by rfl⟩ : syracuseStep 2357987 = 3536981) B3536981
theorem B1571571 : Blo 1570983 1571571 := bstep (se 1 (by rfl) ⟨1178678, by rfl⟩ : syracuseStep 1571571 = 2357357) B2357357
theorem B2358017 : Blo 1570983 2358017 := bstep (se 2 (by rfl) ⟨884256, by rfl⟩ : syracuseStep 2358017 = 1768513) B1768513
theorem B1571587 : Blo 1570983 1571587 := bstep (se 1 (by rfl) ⟨1178690, by rfl⟩ : syracuseStep 1571587 = 2357381) B2357381
theorem B1571603 : Blo 1570983 1571603 := bstep (se 1 (by rfl) ⟨1178702, by rfl⟩ : syracuseStep 1571603 = 2357405) B2357405
theorem B2358035 : Blo 1570983 2358035 := bstep (se 1 (by rfl) ⟨1768526, by rfl⟩ : syracuseStep 2358035 = 3537053) B3537053
theorem B1571619 : Blo 1570983 1571619 := bstep (se 1 (by rfl) ⟨1178714, by rfl⟩ : syracuseStep 1571619 = 2357429) B2357429
theorem B2358065 : Blo 1570983 2358065 := bstep (se 2 (by rfl) ⟨884274, by rfl⟩ : syracuseStep 2358065 = 1768549) B1768549
theorem B6716209 : Blo 1570983 6716209 := bstep (se 2 (by rfl) ⟨2518578, by rfl⟩ : syracuseStep 6716209 = 5037157) B5037157
theorem B1571635 : Blo 1570983 1571635 := bstep (se 1 (by rfl) ⟨1178726, by rfl⟩ : syracuseStep 1571635 = 2357453) B2357453
theorem B1768243 : Blo 1570983 1768243 := bstep (se 1 (by rfl) ⟨1326182, by rfl⟩ : syracuseStep 1768243 = 2652365) B2652365
theorem B2652979 : Blo 1570983 2652979 := bstep (se 1 (by rfl) ⟨1989734, by rfl⟩ : syracuseStep 2652979 = 3979469) B3979469
theorem B1571651 : Blo 1570983 1571651 := bstep (se 1 (by rfl) ⟨1178738, by rfl⟩ : syracuseStep 1571651 = 2357477) B2357477
theorem B2358083 : Blo 1570983 2358083 := bstep (se 1 (by rfl) ⟨1768562, by rfl⟩ : syracuseStep 2358083 = 3537125) B3537125
theorem B1571667 : Blo 1570983 1571667 := bstep (se 1 (by rfl) ⟨1178750, by rfl⟩ : syracuseStep 1571667 = 2357501) B2357501
theorem B2358113 : Blo 1570983 2358113 := bstep (se 2 (by rfl) ⟨884292, by rfl⟩ : syracuseStep 2358113 = 1768585) B1768585
theorem B1571683 : Blo 1570983 1571683 := bstep (se 1 (by rfl) ⟨1178762, by rfl⟩ : syracuseStep 1571683 = 2357525) B2357525
theorem B1571699 : Blo 1570983 1571699 := bstep (se 1 (by rfl) ⟨1178774, by rfl⟩ : syracuseStep 1571699 = 2357549) B2357549
theorem B2358131 : Blo 1570983 2358131 := bstep (se 1 (by rfl) ⟨1768598, by rfl⟩ : syracuseStep 2358131 = 3537197) B3537197
theorem B1571715 : Blo 1570983 1571715 := bstep (se 1 (by rfl) ⟨1178786, by rfl⟩ : syracuseStep 1571715 = 2357573) B2357573
theorem B2358161 : Blo 1570983 2358161 := bstep (se 2 (by rfl) ⟨884310, by rfl⟩ : syracuseStep 2358161 = 1768621) B1768621
theorem B3537809 : Blo 1570983 3537809 := bstep (se 2 (by rfl) ⟨1326678, by rfl⟩ : syracuseStep 3537809 = 2653357) B2653357
theorem B1571731 : Blo 1570983 1571731 := bstep (se 1 (by rfl) ⟨1178798, by rfl⟩ : syracuseStep 1571731 = 2357597) B2357597
theorem B1571747 : Blo 1570983 1571747 := bstep (se 1 (by rfl) ⟨1178810, by rfl⟩ : syracuseStep 1571747 = 2357621) B2357621
theorem B2358179 : Blo 1570983 2358179 := bstep (se 1 (by rfl) ⟨1768634, by rfl⟩ : syracuseStep 2358179 = 3537269) B3537269
theorem B3537827 : Blo 1570983 3537827 := bstep (se 1 (by rfl) ⟨2653370, by rfl⟩ : syracuseStep 3537827 = 5306741) B5306741
theorem B1571763 : Blo 1570983 1571763 := bstep (se 1 (by rfl) ⟨1178822, by rfl⟩ : syracuseStep 1571763 = 2357645) B2357645
theorem B2358209 : Blo 1570983 2358209 := bstep (se 2 (by rfl) ⟨884328, by rfl⟩ : syracuseStep 2358209 = 1768657) B1768657
theorem B2653121 : Blo 1570983 2653121 := bstep (se 2 (by rfl) ⟨994920, by rfl⟩ : syracuseStep 2653121 = 1989841) B1989841
theorem B1571779 : Blo 1570983 1571779 := bstep (se 1 (by rfl) ⟨1178834, by rfl⟩ : syracuseStep 1571779 = 2357669) B2357669
theorem B1768387 : Blo 1570983 1768387 := bstep (se 1 (by rfl) ⟨1326290, by rfl⟩ : syracuseStep 1768387 = 2652581) B2652581
theorem B1571795 : Blo 1570983 1571795 := bstep (se 1 (by rfl) ⟨1178846, by rfl⟩ : syracuseStep 1571795 = 2357693) B2357693
theorem B2358227 : Blo 1570983 2358227 := bstep (se 1 (by rfl) ⟨1768670, by rfl⟩ : syracuseStep 2358227 = 3537341) B3537341
theorem B1571811 : Blo 1570983 1571811 := bstep (se 1 (by rfl) ⟨1178858, by rfl⟩ : syracuseStep 1571811 = 2357717) B2357717
theorem B2358257 : Blo 1570983 2358257 := bstep (se 2 (by rfl) ⟨884346, by rfl⟩ : syracuseStep 2358257 = 1768693) B1768693
theorem B1571827 : Blo 1570983 1571827 := bstep (se 1 (by rfl) ⟨1178870, by rfl⟩ : syracuseStep 1571827 = 2357741) B2357741
theorem B1571843 : Blo 1570983 1571843 := bstep (se 1 (by rfl) ⟨1178882, by rfl⟩ : syracuseStep 1571843 = 2357765) B2357765
theorem B2358275 : Blo 1570983 2358275 := bstep (se 1 (by rfl) ⟨1768706, by rfl⟩ : syracuseStep 2358275 = 3537413) B3537413
theorem B1571859 : Blo 1570983 1571859 := bstep (se 1 (by rfl) ⟨1178894, by rfl⟩ : syracuseStep 1571859 = 2357789) B2357789
theorem B2358305 : Blo 1570983 2358305 := bstep (se 2 (by rfl) ⟨884364, by rfl⟩ : syracuseStep 2358305 = 1768729) B1768729
theorem B1571875 : Blo 1570983 1571875 := bstep (se 1 (by rfl) ⟨1178906, by rfl⟩ : syracuseStep 1571875 = 2357813) B2357813
theorem B1571891 : Blo 1570983 1571891 := bstep (se 1 (by rfl) ⟨1178918, by rfl⟩ : syracuseStep 1571891 = 2357837) B2357837
theorem B2358323 : Blo 1570983 2358323 := bstep (se 1 (by rfl) ⟨1768742, by rfl⟩ : syracuseStep 2358323 = 3537485) B3537485
theorem B1571907 : Blo 1570983 1571907 := bstep (se 1 (by rfl) ⟨1178930, by rfl⟩ : syracuseStep 1571907 = 2357861) B2357861
theorem B2653249 : Blo 1570983 2653249 := bstep (se 2 (by rfl) ⟨994968, by rfl⟩ : syracuseStep 2653249 = 1989937) B1989937
theorem B2358353 : Blo 1570983 2358353 := bstep (se 2 (by rfl) ⟨884382, by rfl⟩ : syracuseStep 2358353 = 1768765) B1768765
theorem B1571923 : Blo 1570983 1571923 := bstep (se 1 (by rfl) ⟨1178942, by rfl⟩ : syracuseStep 1571923 = 2357885) B2357885
theorem B1768531 : Blo 1570983 1768531 := bstep (se 1 (by rfl) ⟨1326398, by rfl⟩ : syracuseStep 1768531 = 2652797) B2652797
theorem B1571939 : Blo 1570983 1571939 := bstep (se 1 (by rfl) ⟨1178954, by rfl⟩ : syracuseStep 1571939 = 2357909) B2357909
theorem B2358371 : Blo 1570983 2358371 := bstep (se 1 (by rfl) ⟨1768778, by rfl⟩ : syracuseStep 2358371 = 3537557) B3537557
theorem B2653283 : Blo 1570983 2653283 := bstep (se 1 (by rfl) ⟨1989962, by rfl⟩ : syracuseStep 2653283 = 3979925) B3979925
theorem B1571955 : Blo 1570983 1571955 := bstep (se 1 (by rfl) ⟨1178966, by rfl⟩ : syracuseStep 1571955 = 2357933) B2357933
theorem B2358401 : Blo 1570983 2358401 := bstep (se 2 (by rfl) ⟨884400, by rfl⟩ : syracuseStep 2358401 = 1768801) B1768801
theorem B1571971 : Blo 1570983 1571971 := bstep (se 1 (by rfl) ⟨1178978, by rfl⟩ : syracuseStep 1571971 = 2357957) B2357957
theorem B1571987 : Blo 1570983 1571987 := bstep (se 1 (by rfl) ⟨1178990, by rfl⟩ : syracuseStep 1571987 = 2357981) B2357981
theorem B2358419 : Blo 1570983 2358419 := bstep (se 1 (by rfl) ⟨1768814, by rfl⟩ : syracuseStep 2358419 = 3537629) B3537629
theorem B1572003 : Blo 1570983 1572003 := bstep (se 1 (by rfl) ⟨1179002, by rfl⟩ : syracuseStep 1572003 = 2358005) B2358005
theorem B2358449 : Blo 1570983 2358449 := bstep (se 2 (by rfl) ⟨884418, by rfl⟩ : syracuseStep 2358449 = 1768837) B1768837
theorem B1572019 : Blo 1570983 1572019 := bstep (se 1 (by rfl) ⟨1179014, by rfl⟩ : syracuseStep 1572019 = 2358029) B2358029
theorem B1572035 : Blo 1570983 1572035 := bstep (se 1 (by rfl) ⟨1179026, by rfl⟩ : syracuseStep 1572035 = 2358053) B2358053
theorem B2358467 : Blo 1570983 2358467 := bstep (se 1 (by rfl) ⟨1768850, by rfl⟩ : syracuseStep 2358467 = 3537701) B3537701
theorem B3775697 : Blo 1570983 3775697 := bstep (se 2 (by rfl) ⟨1415886, by rfl⟩ : syracuseStep 3775697 = 2831773) B2831773
theorem B1572051 : Blo 1570983 1572051 := bstep (se 1 (by rfl) ⟨1179038, by rfl⟩ : syracuseStep 1572051 = 2358077) B2358077
theorem B2358497 : Blo 1570983 2358497 := bstep (se 2 (by rfl) ⟨884436, by rfl⟩ : syracuseStep 2358497 = 1768873) B1768873
theorem B1572067 : Blo 1570983 1572067 := bstep (se 1 (by rfl) ⟨1179050, by rfl⟩ : syracuseStep 1572067 = 2358101) B2358101
theorem B1768675 : Blo 1570983 1768675 := bstep (se 1 (by rfl) ⟨1326506, by rfl⟩ : syracuseStep 1768675 = 2653013) B2653013
theorem B2653411 : Blo 1570983 2653411 := bstep (se 1 (by rfl) ⟨1990058, by rfl⟩ : syracuseStep 2653411 = 3980117) B3980117
theorem B1572083 : Blo 1570983 1572083 := bstep (se 1 (by rfl) ⟨1179062, by rfl⟩ : syracuseStep 1572083 = 2358125) B2358125
theorem B2358515 : Blo 1570983 2358515 := bstep (se 1 (by rfl) ⟨1768886, by rfl⟩ : syracuseStep 2358515 = 3537773) B3537773
theorem B1572099 : Blo 1570983 1572099 := bstep (se 1 (by rfl) ⟨1179074, by rfl⟩ : syracuseStep 1572099 = 2358149) B2358149
theorem B15310093 : Blo 1570983 15310093 := bstep (se 3 (by rfl) ⟨2870642, by rfl⟩ : syracuseStep 15310093 = 5741285) B5741285
theorem B2358545 : Blo 1570983 2358545 := bstep (se 2 (by rfl) ⟨884454, by rfl⟩ : syracuseStep 2358545 = 1768909) B1768909
theorem B1572115 : Blo 1570983 1572115 := bstep (se 1 (by rfl) ⟨1179086, by rfl⟩ : syracuseStep 1572115 = 2358173) B2358173
theorem B1572131 : Blo 1570983 1572131 := bstep (se 1 (by rfl) ⟨1179098, by rfl⟩ : syracuseStep 1572131 = 2358197) B2358197
theorem B2358563 : Blo 1570983 2358563 := bstep (se 1 (by rfl) ⟨1768922, by rfl⟩ : syracuseStep 2358563 = 3537845) B3537845
theorem B7953713 : Blo 1570983 7953713 := bstep (se 2 (by rfl) ⟨2982642, by rfl⟩ : syracuseStep 7953713 = 5965285) B5965285
theorem B1572147 : Blo 1570983 1572147 := bstep (se 1 (by rfl) ⟨1179110, by rfl⟩ : syracuseStep 1572147 = 2358221) B2358221
theorem B2358593 : Blo 1570983 2358593 := bstep (se 2 (by rfl) ⟨884472, by rfl⟩ : syracuseStep 2358593 = 1768945) B1768945
theorem B1572163 : Blo 1570983 1572163 := bstep (se 1 (by rfl) ⟨1179122, by rfl⟩ : syracuseStep 1572163 = 2358245) B2358245
theorem B1572179 : Blo 1570983 1572179 := bstep (se 1 (by rfl) ⟨1179134, by rfl⟩ : syracuseStep 1572179 = 2358269) B2358269
theorem B2358611 : Blo 1570983 2358611 := bstep (se 1 (by rfl) ⟨1768958, by rfl⟩ : syracuseStep 2358611 = 3537917) B3537917
theorem B1572195 : Blo 1570983 1572195 := bstep (se 1 (by rfl) ⟨1179146, by rfl⟩ : syracuseStep 1572195 = 2358293) B2358293
theorem B2358641 : Blo 1570983 2358641 := bstep (se 2 (by rfl) ⟨884490, by rfl⟩ : syracuseStep 2358641 = 1768981) B1768981
theorem B2653553 : Blo 1570983 2653553 := bstep (se 2 (by rfl) ⟨995082, by rfl⟩ : syracuseStep 2653553 = 1990165) B1990165
theorem B1572211 : Blo 1570983 1572211 := bstep (se 1 (by rfl) ⟨1179158, by rfl⟩ : syracuseStep 1572211 = 2358317) B2358317
theorem B1768819 : Blo 1570983 1768819 := bstep (se 1 (by rfl) ⟨1326614, by rfl⟩ : syracuseStep 1768819 = 2653229) B2653229
theorem B1990003 : Blo 1570983 1990003 := bstep (se 1 (by rfl) ⟨1492502, by rfl⟩ : syracuseStep 1990003 = 2985005) B2985005
theorem B1572227 : Blo 1570983 1572227 := bstep (se 1 (by rfl) ⟨1179170, by rfl⟩ : syracuseStep 1572227 = 2358341) B2358341
theorem B2358659 : Blo 1570983 2358659 := bstep (se 1 (by rfl) ⟨1768994, by rfl⟩ : syracuseStep 2358659 = 3537989) B3537989
theorem B1572243 : Blo 1570983 1572243 := bstep (se 1 (by rfl) ⟨1179182, by rfl⟩ : syracuseStep 1572243 = 2358365) B2358365
theorem B2358689 : Blo 1570983 2358689 := bstep (se 2 (by rfl) ⟨884508, by rfl⟩ : syracuseStep 2358689 = 1769017) B1769017
theorem B3775907 : Blo 1570983 3775907 := bstep (se 1 (by rfl) ⟨2831930, by rfl⟩ : syracuseStep 3775907 = 5663861) B5663861
theorem B1572259 : Blo 1570983 1572259 := bstep (se 1 (by rfl) ⟨1179194, by rfl⟩ : syracuseStep 1572259 = 2358389) B2358389
theorem B1572275 : Blo 1570983 1572275 := bstep (se 1 (by rfl) ⟨1179206, by rfl⟩ : syracuseStep 1572275 = 2358413) B2358413
theorem B2358707 : Blo 1570983 2358707 := bstep (se 1 (by rfl) ⟨1769030, by rfl⟩ : syracuseStep 2358707 = 3538061) B3538061
theorem B1572291 : Blo 1570983 1572291 := bstep (se 1 (by rfl) ⟨1179218, by rfl⟩ : syracuseStep 1572291 = 2358437) B2358437
theorem B1572307 : Blo 1570983 1572307 := bstep (se 1 (by rfl) ⟨1179230, by rfl⟩ : syracuseStep 1572307 = 2358461) B2358461
theorem B1990099 : Blo 1570983 1990099 := bstep (se 1 (by rfl) ⟨1492574, by rfl⟩ : syracuseStep 1990099 = 2985149) B2985149
theorem B1572323 : Blo 1570983 1572323 := bstep (se 1 (by rfl) ⟨1179242, by rfl⟩ : syracuseStep 1572323 = 2358485) B2358485
theorem B1572339 : Blo 1570983 1572339 := bstep (se 1 (by rfl) ⟨1179254, by rfl⟩ : syracuseStep 1572339 = 2358509) B2358509
theorem B1572355 : Blo 1570983 1572355 := bstep (se 1 (by rfl) ⟨1179266, by rfl⟩ : syracuseStep 1572355 = 2358533) B2358533
theorem B1768963 : Blo 1570983 1768963 := bstep (se 1 (by rfl) ⟨1326722, by rfl⟩ : syracuseStep 1768963 = 2653445) B2653445
theorem B1572371 : Blo 1570983 1572371 := bstep (se 1 (by rfl) ⟨1179278, by rfl⟩ : syracuseStep 1572371 = 2358557) B2358557
theorem B1572387 : Blo 1570983 1572387 := bstep (se 1 (by rfl) ⟨1179290, by rfl⟩ : syracuseStep 1572387 = 2358581) B2358581
theorem B1572403 : Blo 1570983 1572403 := bstep (se 1 (by rfl) ⟨1179302, by rfl⟩ : syracuseStep 1572403 = 2358605) B2358605
theorem B1572419 : Blo 1570983 1572419 := bstep (se 1 (by rfl) ⟨1179314, by rfl⟩ : syracuseStep 1572419 = 2358629) B2358629
theorem B1572435 : Blo 1570983 1572435 := bstep (se 1 (by rfl) ⟨1179326, by rfl⟩ : syracuseStep 1572435 = 2358653) B2358653
theorem B1572451 : Blo 1570983 1572451 := bstep (se 1 (by rfl) ⟨1179338, by rfl⟩ : syracuseStep 1572451 = 2358677) B2358677
theorem B1678963 : Blo 1570983 1678963 := bstep (se 1 (by rfl) ⟨1259222, by rfl⟩ : syracuseStep 1678963 = 2518445) B2518445
theorem B1572467 : Blo 1570983 1572467 := bstep (se 1 (by rfl) ⟨1179350, by rfl⟩ : syracuseStep 1572467 = 2358701) B2358701
theorem B1572483 : Blo 1570983 1572483 := bstep (se 1 (by rfl) ⟨1179362, by rfl⟩ : syracuseStep 1572483 = 2358725) B2358725
theorem B5742541 : Blo 1570983 5742541 := bstep (se 3 (by rfl) ⟨1076726, by rfl⟩ : syracuseStep 5742541 = 2153453) B2153453
theorem B14344237 : Blo 1570983 14344237 := bstep (se 3 (by rfl) ⟨2689544, by rfl⟩ : syracuseStep 14344237 = 5379089) B5379089
theorem B7955009 : Blo 1570983 7955009 := bstep (se 2 (by rfl) ⟨2983128, by rfl⟩ : syracuseStep 7955009 = 5966257) B5966257
theorem B23012045 : Blo 1570983 23012045 := bstep (se 3 (by rfl) ⟨4314758, by rfl⟩ : syracuseStep 23012045 = 8629517) B8629517
theorem B4473623 : Blo 1570983 4473623 := bstep (se 1 (by rfl) ⟨3355217, by rfl⟩ : syracuseStep 4473623 = 6710435) B6710435
theorem B6808465 : Blo 1570983 6808465 := bstep (se 2 (by rfl) ⟨2553174, by rfl⟩ : syracuseStep 6808465 = 5106349) B5106349
theorem B13427633 : Blo 1570983 13427633 := bstep (se 2 (by rfl) ⟨5035362, by rfl⟩ : syracuseStep 13427633 = 10070725) B10070725
theorem B5104691 : Blo 1570983 5104691 := bstep (se 1 (by rfl) ⟨3828518, by rfl⟩ : syracuseStep 5104691 = 7657037) B7657037
theorem B2982977 : Blo 1570983 2982977 := bstep (se 2 (by rfl) ⟨1118616, by rfl⟩ : syracuseStep 2982977 = 2237233) B2237233
theorem B8954945 : Blo 1570983 8954945 := bstep (se 2 (by rfl) ⟨3358104, by rfl⟩ : syracuseStep 8954945 = 6716209) B6716209
theorem B5375069 : Blo 1570983 5375069 := bstep (se 3 (by rfl) ⟨1007825, by rfl⟩ : syracuseStep 5375069 = 2015651) B2015651
theorem B10069085 : Blo 1570983 10069085 := bstep (se 3 (by rfl) ⟨1887953, by rfl⟩ : syracuseStep 10069085 = 3775907) B3775907
theorem B5965073 : Blo 1570983 5965073 := bstep (se 2 (by rfl) ⟨2236902, by rfl⟩ : syracuseStep 5965073 = 4473805) B4473805
theorem B2983243 : Blo 1570983 2983243 := bstep (se 1 (by rfl) ⟨2237432, by rfl⟩ : syracuseStep 2983243 = 4474865) B4474865
theorem B8496485 : Blo 1570983 8496485 := bstep (se 4 (by rfl) ⟨796545, by rfl⟩ : syracuseStep 8496485 = 1593091) B1593091
theorem B2516503 : Blo 1570983 2516503 := bstep (se 1 (by rfl) ⟨1887377, by rfl⟩ : syracuseStep 2516503 = 3774755) B3774755
theorem B6374957 : Blo 1570983 6374957 := bstep (se 3 (by rfl) ⟨1195304, by rfl⟩ : syracuseStep 6374957 = 2390609) B2390609
theorem B2983691 : Blo 1570983 2983691 := bstep (se 1 (by rfl) ⟨2237768, by rfl⟩ : syracuseStep 2983691 = 4475537) B4475537
theorem B2516759 : Blo 1570983 2516759 := bstep (se 1 (by rfl) ⟨1887569, by rfl⟩ : syracuseStep 2516759 = 3775139) B3775139
theorem B12748589 : Blo 1570983 12748589 := bstep (se 3 (by rfl) ⟨2390360, by rfl⟩ : syracuseStep 12748589 = 4780721) B4780721
theorem B2983873 : Blo 1570983 2983873 := bstep (se 2 (by rfl) ⟨1118952, by rfl⟩ : syracuseStep 2983873 = 2237905) B2237905
theorem B5965771 : Blo 1570983 5965771 := bstep (se 1 (by rfl) ⟨4474328, by rfl⟩ : syracuseStep 5965771 = 8948657) B8948657
theorem B6637571 : Blo 1570983 6637571 := bstep (se 1 (by rfl) ⟨4978178, by rfl⟩ : syracuseStep 6637571 = 9956357) B9956357
theorem B2517131 : Blo 1570983 2517131 := bstep (se 1 (by rfl) ⟨1887848, by rfl⟩ : syracuseStep 2517131 = 3775697) B3775697
theorem B2238617 : Blo 1570983 2238617 := bstep (se 2 (by rfl) ⟨839481, by rfl⟩ : syracuseStep 2238617 = 1678963) B1678963
theorem B5302475 : Blo 1570983 5302475 := bstep (se 1 (by rfl) ⟨3976856, by rfl⟩ : syracuseStep 5302475 = 7953713) B7953713
theorem B8612057 : Blo 1570983 8612057 := bstep (se 2 (by rfl) ⟨3229521, by rfl⟩ : syracuseStep 8612057 = 6459043) B6459043
theorem B5966045 : Blo 1570983 5966045 := bstep (se 3 (by rfl) ⟨1118633, by rfl⟩ : syracuseStep 5966045 = 2237267) B2237267
theorem B2984215 : Blo 1570983 2984215 := bstep (se 1 (by rfl) ⟨2238161, by rfl⟩ : syracuseStep 2984215 = 4476323) B4476323
theorem B5302745 : Blo 1570983 5302745 := bstep (se 2 (by rfl) ⟨1988529, by rfl⟩ : syracuseStep 5302745 = 3977059) B3977059
theorem B7956953 : Blo 1570983 7956953 := bstep (se 2 (by rfl) ⟨2983857, by rfl⟩ : syracuseStep 7956953 = 5967715) B5967715
theorem B2984435 : Blo 1570983 2984435 := bstep (se 1 (by rfl) ⟨2238326, by rfl⟩ : syracuseStep 2984435 = 4476653) B4476653
theorem B4778689 : Blo 1570983 4778689 := bstep (se 2 (by rfl) ⟨1792008, by rfl⟩ : syracuseStep 4778689 = 3584017) B3584017
theorem B2984663 : Blo 1570983 2984663 := bstep (se 1 (by rfl) ⟨2238497, by rfl⟩ : syracuseStep 2984663 = 4476995) B4476995
theorem B6712109 : Blo 1570983 6712109 := bstep (se 3 (by rfl) ⟨1258520, by rfl⟩ : syracuseStep 6712109 = 2517041) B2517041
theorem B9554753 : Blo 1570983 9554753 := bstep (se 2 (by rfl) ⟨3583032, by rfl⟩ : syracuseStep 9554753 = 7166065) B7166065
theorem B5966743 : Blo 1570983 5966743 := bstep (se 1 (by rfl) ⟨4475057, by rfl⟩ : syracuseStep 5966743 = 8950115) B8950115
theorem B11324377 : Blo 1570983 11324377 := bstep (se 2 (by rfl) ⟨4246641, by rfl⟩ : syracuseStep 11324377 = 8493283) B8493283
theorem B2984921 : Blo 1570983 2984921 := bstep (se 2 (by rfl) ⟨1119345, by rfl⟩ : syracuseStep 2984921 = 2238691) B2238691
theorem B4475969 : Blo 1570983 4475969 := bstep (se 2 (by rfl) ⟨1678488, by rfl⟩ : syracuseStep 4475969 = 3356977) B3356977
theorem B5303447 : Blo 1570983 5303447 := bstep (se 1 (by rfl) ⟨3977585, by rfl⟩ : syracuseStep 5303447 = 7955171) B7955171
theorem B10071341 : Blo 1570983 10071341 := bstep (se 3 (by rfl) ⟨1888376, by rfl⟩ : syracuseStep 10071341 = 3776753) B3776753
theorem B3403073 : Blo 1570983 3403073 := bstep (se 2 (by rfl) ⟨1276152, by rfl⟩ : syracuseStep 3403073 = 2552305) B2552305
theorem B14339429 : Blo 1570983 14339429 := bstep (se 4 (by rfl) ⟨1344321, by rfl⟩ : syracuseStep 14339429 = 2688643) B2688643
theorem B4779467 : Blo 1570983 4779467 := bstep (se 1 (by rfl) ⟨3584600, by rfl⟩ : syracuseStep 4779467 = 7169201) B7169201
theorem B6712793 : Blo 1570983 6712793 := bstep (se 2 (by rfl) ⟨2517297, by rfl⟩ : syracuseStep 6712793 = 5034595) B5034595
theorem B2518553 : Blo 1570983 2518553 := bstep (se 2 (by rfl) ⟨944457, by rfl⟩ : syracuseStep 2518553 = 1888915) B1888915
theorem B4476505 : Blo 1570983 4476505 := bstep (se 2 (by rfl) ⟨1678689, by rfl⟩ : syracuseStep 4476505 = 3357379) B3357379
theorem B8498819 : Blo 1570983 8498819 := bstep (se 1 (by rfl) ⟨6374114, by rfl⟩ : syracuseStep 8498819 = 12748229) B12748229
theorem B5967533 : Blo 1570983 5967533 := bstep (se 3 (by rfl) ⟨1118912, by rfl⟩ : syracuseStep 5967533 = 2237825) B2237825
theorem B5303987 : Blo 1570983 5303987 := bstep (se 1 (by rfl) ⟨3977990, by rfl⟩ : syracuseStep 5303987 = 7955981) B7955981
theorem B3976897 : Blo 1570983 3976897 := bstep (se 2 (by rfl) ⟨1491336, by rfl⟩ : syracuseStep 3976897 = 2982673) B2982673
theorem B4034393 : Blo 1570983 4034393 := bstep (se 2 (by rfl) ⟨1512897, by rfl⟩ : syracuseStep 4034393 = 3025795) B3025795
theorem B3534731 : Blo 1570983 3534731 := bstep (se 1 (by rfl) ⟨2651048, by rfl⟩ : syracuseStep 3534731 = 5302097) B5302097
theorem B3534785 : Blo 1570983 3534785 := bstep (se 2 (by rfl) ⟨1325544, by rfl⟩ : syracuseStep 3534785 = 2651089) B2651089
theorem B5304257 : Blo 1570983 5304257 := bstep (se 2 (by rfl) ⟨1989096, by rfl⟩ : syracuseStep 5304257 = 3978193) B3978193
theorem B7958573 : Blo 1570983 7958573 := bstep (se 3 (by rfl) ⟨1492232, by rfl⟩ : syracuseStep 7958573 = 2984465) B2984465
theorem B3535001 : Blo 1570983 3535001 := bstep (se 2 (by rfl) ⟨1325625, by rfl⟩ : syracuseStep 3535001 = 2651251) B2651251
theorem B3535091 : Blo 1570983 3535091 := bstep (se 1 (by rfl) ⟨2651318, by rfl⟩ : syracuseStep 3535091 = 5302637) B5302637
theorem B3535127 : Blo 1570983 3535127 := bstep (se 1 (by rfl) ⟨2651345, by rfl⟩ : syracuseStep 3535127 = 5302691) B5302691
theorem B3977495 : Blo 1570983 3977495 := bstep (se 1 (by rfl) ⟨2983121, by rfl⟩ : syracuseStep 3977495 = 5966243) B5966243
theorem B6050123 : Blo 1570983 6050123 := bstep (se 1 (by rfl) ⟨4537592, by rfl⟩ : syracuseStep 6050123 = 9075185) B9075185
theorem B4305241 : Blo 1570983 4305241 := bstep (se 2 (by rfl) ⟨1614465, by rfl⟩ : syracuseStep 4305241 = 3228931) B3228931
theorem B1593707 : Blo 1570983 1593707 := bstep (se 1 (by rfl) ⟨1195280, by rfl⟩ : syracuseStep 1593707 = 2390561) B2390561
theorem B3535307 : Blo 1570983 3535307 := bstep (se 1 (by rfl) ⟨2651480, by rfl⟩ : syracuseStep 3535307 = 5302961) B5302961
theorem B13431257 : Blo 1570983 13431257 := bstep (se 2 (by rfl) ⟨5036721, by rfl⟩ : syracuseStep 13431257 = 10073443) B10073443
theorem B5304797 : Blo 1570983 5304797 := bstep (se 3 (by rfl) ⟨994649, by rfl⟩ : syracuseStep 5304797 = 1989299) B1989299
theorem B3535361 : Blo 1570983 3535361 := bstep (se 2 (by rfl) ⟨1325760, by rfl⟩ : syracuseStep 3535361 = 2651521) B2651521
theorem B5378653 : Blo 1570983 5378653 := bstep (se 3 (by rfl) ⟨1008497, by rfl⟩ : syracuseStep 5378653 = 2016995) B2016995
theorem B7369309 : Blo 1570983 7369309 := bstep (se 3 (by rfl) ⟨1381745, by rfl⟩ : syracuseStep 7369309 = 2763491) B2763491
theorem B3535577 : Blo 1570983 3535577 := bstep (se 2 (by rfl) ⟨1325841, by rfl⟩ : syracuseStep 3535577 = 2651683) B2651683
theorem B2388761 : Blo 1570983 2388761 := bstep (se 2 (by rfl) ⟨895785, by rfl⟩ : syracuseStep 2388761 = 1791571) B1791571
theorem B3535667 : Blo 1570983 3535667 := bstep (se 1 (by rfl) ⟨2651750, by rfl⟩ : syracuseStep 3535667 = 5303501) B5303501
theorem B54424385 : Blo 1570983 54424385 := bstep (se 2 (by rfl) ⟨20409144, by rfl⟩ : syracuseStep 54424385 = 40818289) B40818289
theorem B3535703 : Blo 1570983 3535703 := bstep (se 1 (by rfl) ⟨2651777, by rfl⟩ : syracuseStep 3535703 = 5303555) B5303555
theorem B3535883 : Blo 1570983 3535883 := bstep (se 1 (by rfl) ⟨2651912, by rfl⟩ : syracuseStep 3535883 = 5303825) B5303825
theorem B7549969 : Blo 1570983 7549969 := bstep (se 2 (by rfl) ⟨2831238, by rfl⟩ : syracuseStep 7549969 = 5662477) B5662477
theorem B6370321 : Blo 1570983 6370321 := bstep (se 2 (by rfl) ⟨2388870, by rfl⟩ : syracuseStep 6370321 = 4777741) B4777741
theorem B3535937 : Blo 1570983 3535937 := bstep (se 2 (by rfl) ⟨1325976, by rfl⟩ : syracuseStep 3535937 = 2651953) B2651953
theorem B3978305 : Blo 1570983 3978305 := bstep (se 2 (by rfl) ⟨1491864, by rfl⟩ : syracuseStep 3978305 = 2983729) B2983729
theorem B5968961 : Blo 1570983 5968961 := bstep (se 2 (by rfl) ⟨2238360, by rfl⟩ : syracuseStep 5968961 = 4476721) B4476721
theorem B30626885 : Blo 1570983 30626885 := bstep (se 4 (by rfl) ⟨2871270, by rfl⟩ : syracuseStep 30626885 = 5742541) B5742541
theorem B2651339 : Blo 1570983 2651339 := bstep (se 1 (by rfl) ⟨1988504, by rfl⟩ : syracuseStep 2651339 = 3977009) B3977009
theorem B2356505 : Blo 1570983 2356505 := bstep (se 2 (by rfl) ⟨883689, by rfl⟩ : syracuseStep 2356505 = 1767379) B1767379
theorem B3536153 : Blo 1570983 3536153 := bstep (se 2 (by rfl) ⟨1326057, by rfl⟩ : syracuseStep 3536153 = 2652115) B2652115
theorem B2651467 : Blo 1570983 2651467 := bstep (se 1 (by rfl) ⟨1988600, by rfl⟩ : syracuseStep 2651467 = 3977201) B3977201
theorem B3536243 : Blo 1570983 3536243 := bstep (se 1 (by rfl) ⟨2652182, by rfl⟩ : syracuseStep 3536243 = 5304365) B5304365
theorem B2356619 : Blo 1570983 2356619 := bstep (se 1 (by rfl) ⟨1767464, by rfl⟩ : syracuseStep 2356619 = 3534929) B3534929
theorem B2356631 : Blo 1570983 2356631 := bstep (se 1 (by rfl) ⟨1767473, by rfl⟩ : syracuseStep 2356631 = 3534947) B3534947
theorem B3536279 : Blo 1570983 3536279 := bstep (se 1 (by rfl) ⟨2652209, by rfl⟩ : syracuseStep 3536279 = 5304419) B5304419
theorem B2356697 : Blo 1570983 2356697 := bstep (se 2 (by rfl) ⟨883761, by rfl⟩ : syracuseStep 2356697 = 1767523) B1767523
theorem B2651609 : Blo 1570983 2651609 := bstep (se 2 (by rfl) ⟨994353, by rfl⟩ : syracuseStep 2651609 = 1988707) B1988707
theorem B2356811 : Blo 1570983 2356811 := bstep (se 1 (by rfl) ⟨1767608, by rfl⟩ : syracuseStep 2356811 = 3535217) B3535217
theorem B3536459 : Blo 1570983 3536459 := bstep (se 1 (by rfl) ⟨2652344, by rfl⟩ : syracuseStep 3536459 = 5304689) B5304689
theorem B5305931 : Blo 1570983 5305931 := bstep (se 1 (by rfl) ⟨3979448, by rfl⟩ : syracuseStep 5305931 = 7958897) B7958897
theorem B2356823 : Blo 1570983 2356823 := bstep (se 1 (by rfl) ⟨1767617, by rfl⟩ : syracuseStep 2356823 = 3535235) B3535235
theorem B2651737 : Blo 1570983 2651737 := bstep (se 2 (by rfl) ⟨994401, by rfl⟩ : syracuseStep 2651737 = 1988803) B1988803
theorem B3978841 : Blo 1570983 3978841 := bstep (se 2 (by rfl) ⟨1492065, by rfl⟩ : syracuseStep 3978841 = 2984131) B2984131
theorem B3536513 : Blo 1570983 3536513 := bstep (se 2 (by rfl) ⟨1326192, by rfl⟩ : syracuseStep 3536513 = 2652385) B2652385
theorem B3356311 : Blo 1570983 3356311 := bstep (se 1 (by rfl) ⟨2517233, by rfl⟩ : syracuseStep 3356311 = 5034467) B5034467
theorem B2356889 : Blo 1570983 2356889 := bstep (se 2 (by rfl) ⟨883833, by rfl⟩ : syracuseStep 2356889 = 1767667) B1767667
theorem B22656773 : Blo 1570983 22656773 := bstep (se 4 (by rfl) ⟨2124072, by rfl⟩ : syracuseStep 22656773 = 4248145) B4248145
theorem B2357003 : Blo 1570983 2357003 := bstep (se 1 (by rfl) ⟨1767752, by rfl⟩ : syracuseStep 2357003 = 3535505) B3535505
theorem B2357015 : Blo 1570983 2357015 := bstep (se 1 (by rfl) ⟨1767761, by rfl⟩ : syracuseStep 2357015 = 3535523) B3535523
theorem B3356491 : Blo 1570983 3356491 := bstep (se 1 (by rfl) ⟨2517368, by rfl⟩ : syracuseStep 3356491 = 5034737) B5034737
theorem B2357081 : Blo 1570983 2357081 := bstep (se 2 (by rfl) ⟨883905, by rfl⟩ : syracuseStep 2357081 = 1767811) B1767811
theorem B3536729 : Blo 1570983 3536729 := bstep (se 2 (by rfl) ⟨1326273, by rfl⟩ : syracuseStep 3536729 = 2652547) B2652547
theorem B5306201 : Blo 1570983 5306201 := bstep (se 2 (by rfl) ⟨1989825, by rfl⟩ : syracuseStep 5306201 = 3979651) B3979651
theorem B3356567 : Blo 1570983 3356567 := bstep (se 1 (by rfl) ⟨2517425, by rfl⟩ : syracuseStep 3356567 = 5034851) B5034851
theorem B5035927 : Blo 1570983 5035927 := bstep (se 1 (by rfl) ⟨3776945, by rfl⟩ : syracuseStep 5035927 = 7553891) B7553891
theorem B3536819 : Blo 1570983 3536819 := bstep (se 1 (by rfl) ⟨2652614, by rfl⟩ : syracuseStep 3536819 = 5305229) B5305229
theorem B2357195 : Blo 1570983 2357195 := bstep (se 1 (by rfl) ⟨1767896, by rfl⟩ : syracuseStep 2357195 = 3535793) B3535793
theorem B2357207 : Blo 1570983 2357207 := bstep (se 1 (by rfl) ⟨1767905, by rfl⟩ : syracuseStep 2357207 = 3535811) B3535811
theorem B3536855 : Blo 1570983 3536855 := bstep (se 1 (by rfl) ⟨2652641, by rfl⟩ : syracuseStep 3536855 = 5305283) B5305283
theorem B1767415 : Blo 1570983 1767415 := bstep (se 1 (by rfl) ⟨1325561, by rfl⟩ : syracuseStep 1767415 = 2651123) B2651123
theorem B2357273 : Blo 1570983 2357273 := bstep (se 2 (by rfl) ⟨883977, by rfl⟩ : syracuseStep 2357273 = 1767955) B1767955
theorem B6715457 : Blo 1570983 6715457 := bstep (se 2 (by rfl) ⟨2518296, by rfl⟩ : syracuseStep 6715457 = 5036593) B5036593
theorem B5036107 : Blo 1570983 5036107 := bstep (se 1 (by rfl) ⟨3777080, by rfl⟩ : syracuseStep 5036107 = 7554161) B7554161
theorem B2357387 : Blo 1570983 2357387 := bstep (se 1 (by rfl) ⟨1768040, by rfl⟩ : syracuseStep 2357387 = 3536081) B3536081
theorem B3537035 : Blo 1570983 3537035 := bstep (se 1 (by rfl) ⟨2652776, by rfl⟩ : syracuseStep 3537035 = 5305553) B5305553
theorem B2357399 : Blo 1570983 2357399 := bstep (se 1 (by rfl) ⟨1768049, by rfl⟩ : syracuseStep 2357399 = 3536099) B3536099
theorem B2652311 : Blo 1570983 2652311 := bstep (se 1 (by rfl) ⟨1989233, by rfl⟩ : syracuseStep 2652311 = 3978467) B3978467
theorem B5036183 : Blo 1570983 5036183 := bstep (se 1 (by rfl) ⟨3777137, by rfl⟩ : syracuseStep 5036183 = 7554275) B7554275
theorem B1570987 : Blo 1570983 1570987 := bstep (se 1 (by rfl) ⟨1178240, by rfl⟩ : syracuseStep 1570987 = 2356481) B2356481
theorem B1767595 : Blo 1570983 1767595 := bstep (se 1 (by rfl) ⟨1325696, by rfl⟩ : syracuseStep 1767595 = 2651393) B2651393
theorem B1570999 : Blo 1570983 1570999 := bstep (se 1 (by rfl) ⟨1178249, by rfl⟩ : syracuseStep 1570999 = 2356499) B2356499
theorem B3537089 : Blo 1570983 3537089 := bstep (se 2 (by rfl) ⟨1326408, by rfl⟩ : syracuseStep 3537089 = 2652817) B2652817
theorem B1571019 : Blo 1570983 1571019 := bstep (se 1 (by rfl) ⟨1178264, by rfl⟩ : syracuseStep 1571019 = 2356529) B2356529
theorem B1571031 : Blo 1570983 1571031 := bstep (se 1 (by rfl) ⟨1178273, by rfl⟩ : syracuseStep 1571031 = 2356547) B2356547
theorem B2357465 : Blo 1570983 2357465 := bstep (se 2 (by rfl) ⟨884049, by rfl⟩ : syracuseStep 2357465 = 1768099) B1768099
theorem B1571051 : Blo 1570983 1571051 := bstep (se 1 (by rfl) ⟨1178288, by rfl⟩ : syracuseStep 1571051 = 2356577) B2356577
theorem B1571063 : Blo 1570983 1571063 := bstep (se 1 (by rfl) ⟨1178297, by rfl⟩ : syracuseStep 1571063 = 2356595) B2356595
theorem B1571083 : Blo 1570983 1571083 := bstep (se 1 (by rfl) ⟨1178312, by rfl⟩ : syracuseStep 1571083 = 2356625) B2356625
theorem B10066193 : Blo 1570983 10066193 := bstep (se 2 (by rfl) ⟨3774822, by rfl⟩ : syracuseStep 10066193 = 7549645) B7549645
theorem B1571095 : Blo 1570983 1571095 := bstep (se 1 (by rfl) ⟨1178321, by rfl⟩ : syracuseStep 1571095 = 2356643) B2356643
theorem B1767703 : Blo 1570983 1767703 := bstep (se 1 (by rfl) ⟨1325777, by rfl⟩ : syracuseStep 1767703 = 2651555) B2651555
theorem B2652439 : Blo 1570983 2652439 := bstep (se 1 (by rfl) ⟨1989329, by rfl⟩ : syracuseStep 2652439 = 3978659) B3978659
theorem B1571115 : Blo 1570983 1571115 := bstep (se 1 (by rfl) ⟨1178336, by rfl⟩ : syracuseStep 1571115 = 2356673) B2356673
theorem B1571127 : Blo 1570983 1571127 := bstep (se 1 (by rfl) ⟨1178345, by rfl⟩ : syracuseStep 1571127 = 2356691) B2356691
theorem B1571147 : Blo 1570983 1571147 := bstep (se 1 (by rfl) ⟨1178360, by rfl⟩ : syracuseStep 1571147 = 2356721) B2356721
theorem B2357579 : Blo 1570983 2357579 := bstep (se 1 (by rfl) ⟨1768184, by rfl⟩ : syracuseStep 2357579 = 3536369) B3536369
theorem B1571159 : Blo 1570983 1571159 := bstep (se 1 (by rfl) ⟨1178369, by rfl⟩ : syracuseStep 1571159 = 2356739) B2356739
theorem B2357591 : Blo 1570983 2357591 := bstep (se 1 (by rfl) ⟨1768193, by rfl⟩ : syracuseStep 2357591 = 3536387) B3536387
theorem B5036377 : Blo 1570983 5036377 := bstep (se 2 (by rfl) ⟨1888641, by rfl⟩ : syracuseStep 5036377 = 3777283) B3777283
theorem B1571179 : Blo 1570983 1571179 := bstep (se 1 (by rfl) ⟨1178384, by rfl⟩ : syracuseStep 1571179 = 2356769) B2356769
theorem B48380273 : Blo 1570983 48380273 := bstep (se 2 (by rfl) ⟨18142602, by rfl⟩ : syracuseStep 48380273 = 36285205) B36285205
theorem B1571191 : Blo 1570983 1571191 := bstep (se 1 (by rfl) ⟨1178393, by rfl⟩ : syracuseStep 1571191 = 2356787) B2356787
theorem B1571211 : Blo 1570983 1571211 := bstep (se 1 (by rfl) ⟨1178408, by rfl⟩ : syracuseStep 1571211 = 2356817) B2356817
theorem B1571223 : Blo 1570983 1571223 := bstep (se 1 (by rfl) ⟨1178417, by rfl⟩ : syracuseStep 1571223 = 2356835) B2356835
theorem B2357657 : Blo 1570983 2357657 := bstep (se 2 (by rfl) ⟨884121, by rfl⟩ : syracuseStep 2357657 = 1768243) B1768243
theorem B3537305 : Blo 1570983 3537305 := bstep (se 2 (by rfl) ⟨1326489, by rfl⟩ : syracuseStep 3537305 = 2652979) B2652979
theorem B1571243 : Blo 1570983 1571243 := bstep (se 1 (by rfl) ⟨1178432, by rfl⟩ : syracuseStep 1571243 = 2356865) B2356865
theorem B3774899 : Blo 1570983 3774899 := bstep (se 1 (by rfl) ⟨2831174, by rfl⟩ : syracuseStep 3774899 = 5662349) B5662349
theorem B1571255 : Blo 1570983 1571255 := bstep (se 1 (by rfl) ⟨1178441, by rfl⟩ : syracuseStep 1571255 = 2356883) B2356883
theorem B1571275 : Blo 1570983 1571275 := bstep (se 1 (by rfl) ⟨1178456, by rfl⟩ : syracuseStep 1571275 = 2356913) B2356913
theorem B1767883 : Blo 1570983 1767883 := bstep (se 1 (by rfl) ⟨1325912, by rfl⟩ : syracuseStep 1767883 = 2651825) B2651825
theorem B1571287 : Blo 1570983 1571287 := bstep (se 1 (by rfl) ⟨1178465, by rfl⟩ : syracuseStep 1571287 = 2356931) B2356931
theorem B8952281 : Blo 1570983 8952281 := bstep (se 2 (by rfl) ⟨3357105, by rfl⟩ : syracuseStep 8952281 = 6714211) B6714211
theorem B1571307 : Blo 1570983 1571307 := bstep (se 1 (by rfl) ⟨1178480, by rfl⟩ : syracuseStep 1571307 = 2356961) B2356961
theorem B3537395 : Blo 1570983 3537395 := bstep (se 1 (by rfl) ⟨2653046, by rfl⟩ : syracuseStep 3537395 = 5306093) B5306093
theorem B1571319 : Blo 1570983 1571319 := bstep (se 1 (by rfl) ⟨1178489, by rfl⟩ : syracuseStep 1571319 = 2356979) B2356979
theorem B1571339 : Blo 1570983 1571339 := bstep (se 1 (by rfl) ⟨1178504, by rfl⟩ : syracuseStep 1571339 = 2357009) B2357009
theorem B2357771 : Blo 1570983 2357771 := bstep (se 1 (by rfl) ⟨1768328, by rfl⟩ : syracuseStep 2357771 = 3536657) B3536657
theorem B1571351 : Blo 1570983 1571351 := bstep (se 1 (by rfl) ⟨1178513, by rfl⟩ : syracuseStep 1571351 = 2357027) B2357027
theorem B2357783 : Blo 1570983 2357783 := bstep (se 1 (by rfl) ⟨1768337, by rfl⟩ : syracuseStep 2357783 = 3536675) B3536675
theorem B3537431 : Blo 1570983 3537431 := bstep (se 1 (by rfl) ⟨2653073, by rfl⟩ : syracuseStep 3537431 = 5306147) B5306147
theorem B5306903 : Blo 1570983 5306903 := bstep (se 1 (by rfl) ⟨3980177, by rfl⟩ : syracuseStep 5306903 = 7960355) B7960355
theorem B1571371 : Blo 1570983 1571371 := bstep (se 1 (by rfl) ⟨1178528, by rfl⟩ : syracuseStep 1571371 = 2357057) B2357057
theorem B1571383 : Blo 1570983 1571383 := bstep (se 1 (by rfl) ⟨1178537, by rfl⟩ : syracuseStep 1571383 = 2357075) B2357075
theorem B1767991 : Blo 1570983 1767991 := bstep (se 1 (by rfl) ⟨1325993, by rfl⟩ : syracuseStep 1767991 = 2651987) B2651987
theorem B1571403 : Blo 1570983 1571403 := bstep (se 1 (by rfl) ⟨1178552, by rfl⟩ : syracuseStep 1571403 = 2357105) B2357105
theorem B1571415 : Blo 1570983 1571415 := bstep (se 1 (by rfl) ⟨1178561, by rfl⟩ : syracuseStep 1571415 = 2357123) B2357123
theorem B2357849 : Blo 1570983 2357849 := bstep (se 2 (by rfl) ⟨884193, by rfl⟩ : syracuseStep 2357849 = 1768387) B1768387
theorem B10074725 : Blo 1570983 10074725 := bstep (se 4 (by rfl) ⟨944505, by rfl⟩ : syracuseStep 10074725 = 1889011) B1889011
theorem B1571435 : Blo 1570983 1571435 := bstep (se 1 (by rfl) ⟨1178576, by rfl⟩ : syracuseStep 1571435 = 2357153) B2357153
theorem B1571447 : Blo 1570983 1571447 := bstep (se 1 (by rfl) ⟨1178585, by rfl⟩ : syracuseStep 1571447 = 2357171) B2357171
theorem B1571467 : Blo 1570983 1571467 := bstep (se 1 (by rfl) ⟨1178600, by rfl⟩ : syracuseStep 1571467 = 2357201) B2357201
theorem B1571479 : Blo 1570983 1571479 := bstep (se 1 (by rfl) ⟨1178609, by rfl⟩ : syracuseStep 1571479 = 2357219) B2357219
theorem B1571499 : Blo 1570983 1571499 := bstep (se 1 (by rfl) ⟨1178624, by rfl⟩ : syracuseStep 1571499 = 2357249) B2357249
theorem B1571511 : Blo 1570983 1571511 := bstep (se 1 (by rfl) ⟨1178633, by rfl⟩ : syracuseStep 1571511 = 2357267) B2357267
theorem B3979955 : Blo 1570983 3979955 := bstep (se 1 (by rfl) ⟨2984966, by rfl⟩ : syracuseStep 3979955 = 5969933) B5969933
theorem B1571531 : Blo 1570983 1571531 := bstep (se 1 (by rfl) ⟨1178648, by rfl⟩ : syracuseStep 1571531 = 2357297) B2357297
theorem B2357963 : Blo 1570983 2357963 := bstep (se 1 (by rfl) ⟨1768472, by rfl⟩ : syracuseStep 2357963 = 3536945) B3536945
theorem B3537611 : Blo 1570983 3537611 := bstep (se 1 (by rfl) ⟨2653208, by rfl⟩ : syracuseStep 3537611 = 5306417) B5306417
theorem B1571543 : Blo 1570983 1571543 := bstep (se 1 (by rfl) ⟨1178657, by rfl⟩ : syracuseStep 1571543 = 2357315) B2357315
theorem B2357975 : Blo 1570983 2357975 := bstep (se 1 (by rfl) ⟨1768481, by rfl⟩ : syracuseStep 2357975 = 3536963) B3536963
theorem B1571563 : Blo 1570983 1571563 := bstep (se 1 (by rfl) ⟨1178672, by rfl⟩ : syracuseStep 1571563 = 2357345) B2357345
theorem B1768171 : Blo 1570983 1768171 := bstep (se 1 (by rfl) ⟨1326128, by rfl⟩ : syracuseStep 1768171 = 2652257) B2652257
theorem B1571575 : Blo 1570983 1571575 := bstep (se 1 (by rfl) ⟨1178681, by rfl⟩ : syracuseStep 1571575 = 2357363) B2357363
theorem B3537665 : Blo 1570983 3537665 := bstep (se 2 (by rfl) ⟨1326624, by rfl⟩ : syracuseStep 3537665 = 2653249) B2653249
theorem B1571595 : Blo 1570983 1571595 := bstep (se 1 (by rfl) ⟨1178696, by rfl⟩ : syracuseStep 1571595 = 2357393) B2357393
theorem B1571607 : Blo 1570983 1571607 := bstep (se 1 (by rfl) ⟨1178705, by rfl⟩ : syracuseStep 1571607 = 2357411) B2357411
theorem B2358041 : Blo 1570983 2358041 := bstep (se 2 (by rfl) ⟨884265, by rfl⟩ : syracuseStep 2358041 = 1768531) B1768531
theorem B5970449 : Blo 1570983 5970449 := bstep (se 2 (by rfl) ⟨2238918, by rfl⟩ : syracuseStep 5970449 = 4477837) B4477837
theorem B1571627 : Blo 1570983 1571627 := bstep (se 1 (by rfl) ⟨1178720, by rfl⟩ : syracuseStep 1571627 = 2357441) B2357441
theorem B1571639 : Blo 1570983 1571639 := bstep (se 1 (by rfl) ⟨1178729, by rfl⟩ : syracuseStep 1571639 = 2357459) B2357459
theorem B7953227 : Blo 1570983 7953227 := bstep (se 1 (by rfl) ⟨5964920, by rfl⟩ : syracuseStep 7953227 = 11929841) B11929841
theorem B1571659 : Blo 1570983 1571659 := bstep (se 1 (by rfl) ⟨1178744, by rfl⟩ : syracuseStep 1571659 = 2357489) B2357489
theorem B1989451 : Blo 1570983 1989451 := bstep (se 1 (by rfl) ⟨1492088, by rfl⟩ : syracuseStep 1989451 = 2984177) B2984177
theorem B1571671 : Blo 1570983 1571671 := bstep (se 1 (by rfl) ⟨1178753, by rfl⟩ : syracuseStep 1571671 = 2357507) B2357507
theorem B1768279 : Blo 1570983 1768279 := bstep (se 1 (by rfl) ⟨1326209, by rfl⟩ : syracuseStep 1768279 = 2652419) B2652419
theorem B26917733 : Blo 1570983 26917733 := bstep (se 4 (by rfl) ⟨2523537, by rfl⟩ : syracuseStep 26917733 = 5047075) B5047075
theorem B1571691 : Blo 1570983 1571691 := bstep (se 1 (by rfl) ⟨1178768, by rfl⟩ : syracuseStep 1571691 = 2357537) B2357537
theorem B1571703 : Blo 1570983 1571703 := bstep (se 1 (by rfl) ⟨1178777, by rfl⟩ : syracuseStep 1571703 = 2357555) B2357555
theorem B1571723 : Blo 1570983 1571723 := bstep (se 1 (by rfl) ⟨1178792, by rfl⟩ : syracuseStep 1571723 = 2357585) B2357585
theorem B2358155 : Blo 1570983 2358155 := bstep (se 1 (by rfl) ⟨1768616, by rfl⟩ : syracuseStep 2358155 = 3537233) B3537233
theorem B2653067 : Blo 1570983 2653067 := bstep (se 1 (by rfl) ⟨1989800, by rfl⟩ : syracuseStep 2653067 = 3979601) B3979601
theorem B1571735 : Blo 1570983 1571735 := bstep (se 1 (by rfl) ⟨1178801, by rfl⟩ : syracuseStep 1571735 = 2357603) B2357603
theorem B2358167 : Blo 1570983 2358167 := bstep (se 1 (by rfl) ⟨1768625, by rfl⟩ : syracuseStep 2358167 = 3537251) B3537251
theorem B1571755 : Blo 1570983 1571755 := bstep (se 1 (by rfl) ⟨1178816, by rfl⟩ : syracuseStep 1571755 = 2357633) B2357633
theorem B14728115 : Blo 1570983 14728115 := bstep (se 1 (by rfl) ⟨11046086, by rfl⟩ : syracuseStep 14728115 = 22092173) B22092173
theorem B1571767 : Blo 1570983 1571767 := bstep (se 1 (by rfl) ⟨1178825, by rfl⟩ : syracuseStep 1571767 = 2357651) B2357651
theorem B1571787 : Blo 1570983 1571787 := bstep (se 1 (by rfl) ⟨1178840, by rfl⟩ : syracuseStep 1571787 = 2357681) B2357681
theorem B1571799 : Blo 1570983 1571799 := bstep (se 1 (by rfl) ⟨1178849, by rfl⟩ : syracuseStep 1571799 = 2357699) B2357699
theorem B2358233 : Blo 1570983 2358233 := bstep (se 2 (by rfl) ⟨884337, by rfl⟩ : syracuseStep 2358233 = 1768675) B1768675
theorem B3537881 : Blo 1570983 3537881 := bstep (se 2 (by rfl) ⟨1326705, by rfl⟩ : syracuseStep 3537881 = 2653411) B2653411
theorem B3980249 : Blo 1570983 3980249 := bstep (se 2 (by rfl) ⟨1492593, by rfl⟩ : syracuseStep 3980249 = 2985187) B2985187
theorem B1571819 : Blo 1570983 1571819 := bstep (se 1 (by rfl) ⟨1178864, by rfl⟩ : syracuseStep 1571819 = 2357729) B2357729
theorem B1571831 : Blo 1570983 1571831 := bstep (se 1 (by rfl) ⟨1178873, by rfl⟩ : syracuseStep 1571831 = 2357747) B2357747
theorem B1571851 : Blo 1570983 1571851 := bstep (se 1 (by rfl) ⟨1178888, by rfl⟩ : syracuseStep 1571851 = 2357777) B2357777
theorem B1768459 : Blo 1570983 1768459 := bstep (se 1 (by rfl) ⟨1326344, by rfl⟩ : syracuseStep 1768459 = 2652689) B2652689
theorem B2653195 : Blo 1570983 2653195 := bstep (se 1 (by rfl) ⟨1989896, by rfl⟩ : syracuseStep 2653195 = 3979793) B3979793
theorem B20413457 : Blo 1570983 20413457 := bstep (se 2 (by rfl) ⟨7655046, by rfl⟩ : syracuseStep 20413457 = 15310093) B15310093
theorem B1571863 : Blo 1570983 1571863 := bstep (se 1 (by rfl) ⟨1178897, by rfl⟩ : syracuseStep 1571863 = 2357795) B2357795
theorem B1571883 : Blo 1570983 1571883 := bstep (se 1 (by rfl) ⟨1178912, by rfl⟩ : syracuseStep 1571883 = 2357825) B2357825
theorem B7552045 : Blo 1570983 7552045 := bstep (se 3 (by rfl) ⟨1416008, by rfl⟩ : syracuseStep 7552045 = 2832017) B2832017
theorem B1571895 : Blo 1570983 1571895 := bstep (se 1 (by rfl) ⟨1178921, by rfl⟩ : syracuseStep 1571895 = 2357843) B2357843
theorem B3537971 : Blo 1570983 3537971 := bstep (se 1 (by rfl) ⟨2653478, by rfl⟩ : syracuseStep 3537971 = 5306957) B5306957
theorem B1571915 : Blo 1570983 1571915 := bstep (se 1 (by rfl) ⟨1178936, by rfl⟩ : syracuseStep 1571915 = 2357873) B2357873
theorem B2358347 : Blo 1570983 2358347 := bstep (se 1 (by rfl) ⟨1768760, by rfl⟩ : syracuseStep 2358347 = 3537521) B3537521
theorem B1571927 : Blo 1570983 1571927 := bstep (se 1 (by rfl) ⟨1178945, by rfl⟩ : syracuseStep 1571927 = 2357891) B2357891
theorem B2358359 : Blo 1570983 2358359 := bstep (se 1 (by rfl) ⟨1768769, by rfl⟩ : syracuseStep 2358359 = 3537539) B3537539
theorem B3538007 : Blo 1570983 3538007 := bstep (se 1 (by rfl) ⟨2653505, by rfl⟩ : syracuseStep 3538007 = 5307011) B5307011
theorem B1571947 : Blo 1570983 1571947 := bstep (se 1 (by rfl) ⟨1178960, by rfl⟩ : syracuseStep 1571947 = 2357921) B2357921
theorem B1571959 : Blo 1570983 1571959 := bstep (se 1 (by rfl) ⟨1178969, by rfl⟩ : syracuseStep 1571959 = 2357939) B2357939
theorem B1768567 : Blo 1570983 1768567 := bstep (se 1 (by rfl) ⟨1326425, by rfl⟩ : syracuseStep 1768567 = 2652851) B2652851
theorem B1571979 : Blo 1570983 1571979 := bstep (se 1 (by rfl) ⟨1178984, by rfl⟩ : syracuseStep 1571979 = 2357969) B2357969
theorem B16989335 : Blo 1570983 16989335 := bstep (se 1 (by rfl) ⟨12742001, by rfl⟩ : syracuseStep 16989335 = 25484003) B25484003
theorem B1571991 : Blo 1570983 1571991 := bstep (se 1 (by rfl) ⟨1178993, by rfl⟩ : syracuseStep 1571991 = 2357987) B2357987
theorem B2358425 : Blo 1570983 2358425 := bstep (se 2 (by rfl) ⟨884409, by rfl⟩ : syracuseStep 2358425 = 1768819) B1768819
theorem B2653337 : Blo 1570983 2653337 := bstep (se 2 (by rfl) ⟨995001, by rfl⟩ : syracuseStep 2653337 = 1990003) B1990003
theorem B1572011 : Blo 1570983 1572011 := bstep (se 1 (by rfl) ⟨1179008, by rfl⟩ : syracuseStep 1572011 = 2358017) B2358017
theorem B1678519 : Blo 1570983 1678519 := bstep (se 1 (by rfl) ⟨1258889, by rfl⟩ : syracuseStep 1678519 = 2517779) B2517779
theorem B1572023 : Blo 1570983 1572023 := bstep (se 1 (by rfl) ⟨1179017, by rfl⟩ : syracuseStep 1572023 = 2358035) B2358035
theorem B1572043 : Blo 1570983 1572043 := bstep (se 1 (by rfl) ⟨1179032, by rfl⟩ : syracuseStep 1572043 = 2358065) B2358065
theorem B1572055 : Blo 1570983 1572055 := bstep (se 1 (by rfl) ⟨1179041, by rfl⟩ : syracuseStep 1572055 = 2358083) B2358083
theorem B1572075 : Blo 1570983 1572075 := bstep (se 1 (by rfl) ⟨1179056, by rfl⟩ : syracuseStep 1572075 = 2358113) B2358113
theorem B1572087 : Blo 1570983 1572087 := bstep (se 1 (by rfl) ⟨1179065, by rfl⟩ : syracuseStep 1572087 = 2358131) B2358131
theorem B1572107 : Blo 1570983 1572107 := bstep (se 1 (by rfl) ⟨1179080, by rfl⟩ : syracuseStep 1572107 = 2358161) B2358161
theorem B2358539 : Blo 1570983 2358539 := bstep (se 1 (by rfl) ⟨1768904, by rfl⟩ : syracuseStep 2358539 = 3537809) B3537809
theorem B1572119 : Blo 1570983 1572119 := bstep (se 1 (by rfl) ⟨1179089, by rfl⟩ : syracuseStep 1572119 = 2358179) B2358179
theorem B2358551 : Blo 1570983 2358551 := bstep (se 1 (by rfl) ⟨1768913, by rfl⟩ : syracuseStep 2358551 = 3537827) B3537827
theorem B2653465 : Blo 1570983 2653465 := bstep (se 2 (by rfl) ⟨995049, by rfl⟩ : syracuseStep 2653465 = 1990099) B1990099
theorem B1572139 : Blo 1570983 1572139 := bstep (se 1 (by rfl) ⟨1179104, by rfl⟩ : syracuseStep 1572139 = 2358209) B2358209
theorem B1768747 : Blo 1570983 1768747 := bstep (se 1 (by rfl) ⟨1326560, by rfl⟩ : syracuseStep 1768747 = 2653121) B2653121
theorem B1572151 : Blo 1570983 1572151 := bstep (se 1 (by rfl) ⟨1179113, by rfl⟩ : syracuseStep 1572151 = 2358227) B2358227
theorem B1572171 : Blo 1570983 1572171 := bstep (se 1 (by rfl) ⟨1179128, by rfl⟩ : syracuseStep 1572171 = 2358257) B2358257
theorem B1572183 : Blo 1570983 1572183 := bstep (se 1 (by rfl) ⟨1179137, by rfl⟩ : syracuseStep 1572183 = 2358275) B2358275
theorem B2358617 : Blo 1570983 2358617 := bstep (se 2 (by rfl) ⟨884481, by rfl⟩ : syracuseStep 2358617 = 1768963) B1768963
theorem B1572203 : Blo 1570983 1572203 := bstep (se 1 (by rfl) ⟨1179152, by rfl⟩ : syracuseStep 1572203 = 2358305) B2358305
theorem B1572215 : Blo 1570983 1572215 := bstep (se 1 (by rfl) ⟨1179161, by rfl⟩ : syracuseStep 1572215 = 2358323) B2358323
theorem B1572235 : Blo 1570983 1572235 := bstep (se 1 (by rfl) ⟨1179176, by rfl⟩ : syracuseStep 1572235 = 2358353) B2358353
theorem B1572247 : Blo 1570983 1572247 := bstep (se 1 (by rfl) ⟨1179185, by rfl⟩ : syracuseStep 1572247 = 2358371) B2358371
theorem B1768855 : Blo 1570983 1768855 := bstep (se 1 (by rfl) ⟨1326641, by rfl⟩ : syracuseStep 1768855 = 2653283) B2653283
theorem B1572267 : Blo 1570983 1572267 := bstep (se 1 (by rfl) ⟨1179200, by rfl⟩ : syracuseStep 1572267 = 2358401) B2358401
theorem B16997809 : Blo 1570983 16997809 := bstep (se 2 (by rfl) ⟨6374178, by rfl⟩ : syracuseStep 16997809 = 12748357) B12748357
theorem B1572279 : Blo 1570983 1572279 := bstep (se 1 (by rfl) ⟨1179209, by rfl⟩ : syracuseStep 1572279 = 2358419) B2358419
theorem B1572299 : Blo 1570983 1572299 := bstep (se 1 (by rfl) ⟨1179224, by rfl⟩ : syracuseStep 1572299 = 2358449) B2358449
theorem B1572311 : Blo 1570983 1572311 := bstep (se 1 (by rfl) ⟨1179233, by rfl⟩ : syracuseStep 1572311 = 2358467) B2358467
theorem B1572331 : Blo 1570983 1572331 := bstep (se 1 (by rfl) ⟨1179248, by rfl⟩ : syracuseStep 1572331 = 2358497) B2358497
theorem B1572343 : Blo 1570983 1572343 := bstep (se 1 (by rfl) ⟨1179257, by rfl⟩ : syracuseStep 1572343 = 2358515) B2358515
theorem B1572363 : Blo 1570983 1572363 := bstep (se 1 (by rfl) ⟨1179272, by rfl⟩ : syracuseStep 1572363 = 2358545) B2358545
theorem B1572375 : Blo 1570983 1572375 := bstep (se 1 (by rfl) ⟨1179281, by rfl⟩ : syracuseStep 1572375 = 2358563) B2358563
theorem B1572395 : Blo 1570983 1572395 := bstep (se 1 (by rfl) ⟨1179296, by rfl⟩ : syracuseStep 1572395 = 2358593) B2358593
theorem B1572407 : Blo 1570983 1572407 := bstep (se 1 (by rfl) ⟨1179305, by rfl⟩ : syracuseStep 1572407 = 2358611) B2358611
theorem B1572427 : Blo 1570983 1572427 := bstep (se 1 (by rfl) ⟨1179320, by rfl⟩ : syracuseStep 1572427 = 2358641) B2358641
theorem B1769035 : Blo 1570983 1769035 := bstep (se 1 (by rfl) ⟨1326776, by rfl⟩ : syracuseStep 1769035 = 2653553) B2653553
theorem B3186263 : Blo 1570983 3186263 := bstep (se 1 (by rfl) ⟨2389697, by rfl⟩ : syracuseStep 3186263 = 4779395) B4779395
theorem B1572439 : Blo 1570983 1572439 := bstep (se 1 (by rfl) ⟨1179329, by rfl⟩ : syracuseStep 1572439 = 2358659) B2358659
theorem B1572459 : Blo 1570983 1572459 := bstep (se 1 (by rfl) ⟨1179344, by rfl⟩ : syracuseStep 1572459 = 2358689) B2358689
theorem B1572471 : Blo 1570983 1572471 := bstep (se 1 (by rfl) ⟨1179353, by rfl⟩ : syracuseStep 1572471 = 2358707) B2358707
theorem B3358361 : Blo 1570983 3358361 := bstep (se 2 (by rfl) ⟨1259385, by rfl⟩ : syracuseStep 3358361 = 2518771) B2518771
theorem B7167961 : Blo 1570983 7167961 := bstep (se 2 (by rfl) ⟨2687985, by rfl⟩ : syracuseStep 7167961 = 5375971) B5375971
theorem B8954171 : Blo 1570983 8954171 := bstep (se 1 (by rfl) ⟨6715628, by rfl⟩ : syracuseStep 8954171 = 13431257) B13431257
theorem B2982415 : Blo 1570983 2982415 := bstep (se 1 (by rfl) ⟨2236811, by rfl⟩ : syracuseStep 2982415 = 4473623) B4473623
theorem B36282923 : Blo 1570983 36282923 := bstep (se 1 (by rfl) ⟨27212192, by rfl⟩ : syracuseStep 36282923 = 54424385) B54424385
theorem B16999541 : Blo 1570983 16999541 := bstep (se 5 (by rfl) ⟨796853, by rfl⟩ : syracuseStep 16999541 = 1593707) B1593707
theorem B9077953 : Blo 1570983 9077953 := bstep (se 2 (by rfl) ⟨3404232, by rfl⟩ : syracuseStep 9077953 = 6808465) B6808465
theorem B7955657 : Blo 1570983 7955657 := bstep (se 2 (by rfl) ⟨2983371, by rfl⟩ : syracuseStep 7955657 = 5966743) B5966743
theorem B2237711 : Blo 1570983 2237711 := bstep (se 1 (by rfl) ⟨1678283, by rfl⟩ : syracuseStep 2237711 = 3356567) B3356567
theorem B15099169 : Blo 1570983 15099169 := bstep (se 2 (by rfl) ⟨5662188, by rfl⟩ : syracuseStep 15099169 = 11324377) B11324377
theorem B4425047 : Blo 1570983 4425047 := bstep (se 1 (by rfl) ⟨3318785, by rfl⟩ : syracuseStep 4425047 = 6637571) B6637571
theorem B10069393 : Blo 1570983 10069393 := bstep (se 2 (by rfl) ⟨3776022, by rfl⟩ : syracuseStep 10069393 = 7552045) B7552045
theorem B16999885 : Blo 1570983 16999885 := bstep (se 3 (by rfl) ⟨3187478, by rfl⟩ : syracuseStep 16999885 = 6374957) B6374957
theorem B6710795 : Blo 1570983 6710795 := bstep (se 1 (by rfl) ⟨5033096, by rfl⟩ : syracuseStep 6710795 = 10066193) B10066193
theorem B8496701 : Blo 1570983 8496701 := bstep (se 3 (by rfl) ⟨1593131, by rfl⟩ : syracuseStep 8496701 = 3186263) B3186263
theorem B2238025 : Blo 1570983 2238025 := bstep (se 2 (by rfl) ⟨839259, by rfl⟩ : syracuseStep 2238025 = 1678519) B1678519
theorem B32253515 : Blo 1570983 32253515 := bstep (se 1 (by rfl) ⟨24190136, by rfl⟩ : syracuseStep 32253515 = 48380273) B48380273
theorem B2516599 : Blo 1570983 2516599 := bstep (se 1 (by rfl) ⟨1887449, by rfl⟩ : syracuseStep 2516599 = 3774899) B3774899
theorem B8955629 : Blo 1570983 8955629 := bstep (se 3 (by rfl) ⟨1679180, by rfl⟩ : syracuseStep 8955629 = 3358361) B3358361
theorem B4474739 : Blo 1570983 4474739 := bstep (se 1 (by rfl) ⟨3356054, by rfl⟩ : syracuseStep 4474739 = 6712109) B6712109
theorem B5302151 : Blo 1570983 5302151 := bstep (se 1 (by rfl) ⟨3976613, by rfl⟩ : syracuseStep 5302151 = 7953227) B7953227
theorem B13608971 : Blo 1570983 13608971 := bstep (se 1 (by rfl) ⟨10206728, by rfl⟩ : syracuseStep 13608971 = 20413457) B20413457
theorem B2983979 : Blo 1570983 2983979 := bstep (se 1 (by rfl) ⟨2237984, by rfl⟩ : syracuseStep 2983979 = 4475969) B4475969
theorem B4475081 : Blo 1570983 4475081 := bstep (se 2 (by rfl) ⟨1678155, by rfl⟩ : syracuseStep 4475081 = 3356311) B3356311
theorem B5302529 : Blo 1570983 5302529 := bstep (se 2 (by rfl) ⟨1988448, by rfl⟩ : syracuseStep 5302529 = 3976897) B3976897
theorem B4475195 : Blo 1570983 4475195 := bstep (se 1 (by rfl) ⟨3356396, by rfl⟩ : syracuseStep 4475195 = 6712793) B6712793
theorem B4475321 : Blo 1570983 4475321 := bstep (se 2 (by rfl) ⟨1678245, by rfl⟩ : syracuseStep 4475321 = 3356491) B3356491
theorem B2689595 : Blo 1570983 2689595 := bstep (se 1 (by rfl) ⟨2017196, by rfl⟩ : syracuseStep 2689595 = 4034393) B4034393
theorem B4033415 : Blo 1570983 4033415 := bstep (se 1 (by rfl) ⟨3025061, by rfl⟩ : syracuseStep 4033415 = 6050123) B6050123
theorem B5303339 : Blo 1570983 5303339 := bstep (se 1 (by rfl) ⟨3977504, by rfl⟩ : syracuseStep 5303339 = 7955009) B7955009
theorem B1592507 : Blo 1570983 1592507 := bstep (se 1 (by rfl) ⟨1194380, by rfl⟩ : syracuseStep 1592507 = 2388761) B2388761
theorem B3403127 : Blo 1570983 3403127 := bstep (se 1 (by rfl) ⟨2552345, by rfl⟩ : syracuseStep 3403127 = 5104691) B5104691
theorem B20417923 : Blo 1570983 20417923 := bstep (se 1 (by rfl) ⟨15313442, by rfl⟩ : syracuseStep 20417923 = 30626885) B30626885
theorem B3583379 : Blo 1570983 3583379 := bstep (se 1 (by rfl) ⟨2687534, by rfl⟩ : syracuseStep 3583379 = 5375069) B5375069
theorem B6712723 : Blo 1570983 6712723 := bstep (se 1 (by rfl) ⟨5034542, by rfl⟩ : syracuseStep 6712723 = 10069085) B10069085
theorem B3976715 : Blo 1570983 3976715 := bstep (se 1 (by rfl) ⟨2982536, by rfl⟩ : syracuseStep 3976715 = 5965073) B5965073
theorem B5664323 : Blo 1570983 5664323 := bstep (se 1 (by rfl) ⟨4248242, by rfl⟩ : syracuseStep 5664323 = 8496485) B8496485
theorem B8499059 : Blo 1570983 8499059 := bstep (se 1 (by rfl) ⟨6374294, by rfl⟩ : syracuseStep 8499059 = 12748589) B12748589
theorem B4476971 : Blo 1570983 4476971 := bstep (se 1 (by rfl) ⟨3357728, by rfl⟩ : syracuseStep 4476971 = 6715457) B6715457
theorem B3534983 : Blo 1570983 3534983 := bstep (se 1 (by rfl) ⟨2651237, by rfl⟩ : syracuseStep 3534983 = 5302475) B5302475
theorem B3977363 : Blo 1570983 3977363 := bstep (se 1 (by rfl) ⟨2983022, by rfl⟩ : syracuseStep 3977363 = 5966045) B5966045
theorem B3535163 : Blo 1570983 3535163 := bstep (se 1 (by rfl) ⟨2651372, by rfl⟩ : syracuseStep 3535163 = 5302745) B5302745
theorem B5304635 : Blo 1570983 5304635 := bstep (se 1 (by rfl) ⟨3978476, by rfl⟩ : syracuseStep 5304635 = 7956953) B7956953
theorem B5968187 : Blo 1570983 5968187 := bstep (se 1 (by rfl) ⟨4476140, by rfl⟩ : syracuseStep 5968187 = 8952281) B8952281
theorem B3535289 : Blo 1570983 3535289 := bstep (se 2 (by rfl) ⟨1325733, by rfl⟩ : syracuseStep 3535289 = 2651467) B2651467
theorem B3977657 : Blo 1570983 3977657 := bstep (se 2 (by rfl) ⟨1491621, by rfl⟩ : syracuseStep 3977657 = 2983243) B2983243
theorem B6369835 : Blo 1570983 6369835 := bstep (se 1 (by rfl) ⟨4777376, by rfl⟩ : syracuseStep 6369835 = 9554753) B9554753
theorem B22663745 : Blo 1570983 22663745 := bstep (se 2 (by rfl) ⟨8498904, by rfl⟩ : syracuseStep 22663745 = 16997809) B16997809
theorem B17945155 : Blo 1570983 17945155 := bstep (se 1 (by rfl) ⟨13458866, by rfl⟩ : syracuseStep 17945155 = 26917733) B26917733
theorem B9818743 : Blo 1570983 9818743 := bstep (se 1 (by rfl) ⟨7364057, by rfl⟩ : syracuseStep 9818743 = 14728115) B14728115
theorem B3355337 : Blo 1570983 3355337 := bstep (se 2 (by rfl) ⟨1258251, by rfl⟩ : syracuseStep 3355337 = 2516503) B2516503
theorem B11326223 : Blo 1570983 11326223 := bstep (se 1 (by rfl) ⟨8494667, by rfl⟩ : syracuseStep 11326223 = 16989335) B16989335
theorem B3535631 : Blo 1570983 3535631 := bstep (se 1 (by rfl) ⟨2651723, by rfl⟩ : syracuseStep 3535631 = 5303447) B5303447
theorem B3535649 : Blo 1570983 3535649 := bstep (se 2 (by rfl) ⟨1325868, by rfl⟩ : syracuseStep 3535649 = 2651737) B2651737
theorem B5305121 : Blo 1570983 5305121 := bstep (se 2 (by rfl) ⟨1989420, by rfl⟩ : syracuseStep 5305121 = 3978841) B3978841
theorem B5968673 : Blo 1570983 5968673 := bstep (se 2 (by rfl) ⟨2238252, by rfl⟩ : syracuseStep 5968673 = 4476505) B4476505
theorem B6714227 : Blo 1570983 6714227 := bstep (se 1 (by rfl) ⟨5035670, by rfl⟩ : syracuseStep 6714227 = 10071341) B10071341
theorem B5665879 : Blo 1570983 5665879 := bstep (se 1 (by rfl) ⟨4249409, by rfl⟩ : syracuseStep 5665879 = 8498819) B8498819
theorem B3978355 : Blo 1570983 3978355 := bstep (se 1 (by rfl) ⟨2983766, by rfl⟩ : syracuseStep 3978355 = 5967533) B5967533
theorem B3535991 : Blo 1570983 3535991 := bstep (se 1 (by rfl) ⟨2651993, by rfl⟩ : syracuseStep 3535991 = 5303987) B5303987
theorem B6714569 : Blo 1570983 6714569 := bstep (se 2 (by rfl) ⟨2517963, by rfl⟩ : syracuseStep 6714569 = 5035927) B5035927
theorem B3978497 : Blo 1570983 3978497 := bstep (se 2 (by rfl) ⟨1491936, by rfl⟩ : syracuseStep 3978497 = 2983873) B2983873
theorem B2356487 : Blo 1570983 2356487 := bstep (se 1 (by rfl) ⟨1767365, by rfl⟩ : syracuseStep 2356487 = 3534731) B3534731
theorem B9557281 : Blo 1570983 9557281 := bstep (se 2 (by rfl) ⟨3583980, by rfl⟩ : syracuseStep 9557281 = 7167961) B7167961
theorem B2356523 : Blo 1570983 2356523 := bstep (se 1 (by rfl) ⟨1767392, by rfl⟩ : syracuseStep 2356523 = 3534785) B3534785
theorem B3536171 : Blo 1570983 3536171 := bstep (se 1 (by rfl) ⟨2652128, by rfl⟩ : syracuseStep 3536171 = 5304257) B5304257
theorem B2356553 : Blo 1570983 2356553 := bstep (se 2 (by rfl) ⟨883707, by rfl⟩ : syracuseStep 2356553 = 1767415) B1767415
theorem B5305715 : Blo 1570983 5305715 := bstep (se 1 (by rfl) ⟨3979286, by rfl⟩ : syracuseStep 5305715 = 7958573) B7958573
theorem B19125649 : Blo 1570983 19125649 := bstep (se 2 (by rfl) ⟨7172118, by rfl⟩ : syracuseStep 19125649 = 14344237) B14344237
theorem B6714809 : Blo 1570983 6714809 := bstep (se 2 (by rfl) ⟨2518053, by rfl⟩ : syracuseStep 6714809 = 5036107) B5036107
theorem B2356667 : Blo 1570983 2356667 := bstep (se 1 (by rfl) ⟨1767500, by rfl⟩ : syracuseStep 2356667 = 3535001) B3535001
theorem B2356727 : Blo 1570983 2356727 := bstep (se 1 (by rfl) ⟨1767545, by rfl⟩ : syracuseStep 2356727 = 3535091) B3535091
theorem B2356751 : Blo 1570983 2356751 := bstep (se 1 (by rfl) ⟨1767563, by rfl⟩ : syracuseStep 2356751 = 3535127) B3535127
theorem B2651663 : Blo 1570983 2651663 := bstep (se 1 (by rfl) ⟨1988747, by rfl⟩ : syracuseStep 2651663 = 3977495) B3977495
theorem B2356793 : Blo 1570983 2356793 := bstep (se 2 (by rfl) ⟨883797, by rfl⟩ : syracuseStep 2356793 = 1767595) B1767595
theorem B2356871 : Blo 1570983 2356871 := bstep (se 1 (by rfl) ⟨1767653, by rfl⟩ : syracuseStep 2356871 = 3535307) B3535307
theorem B3536531 : Blo 1570983 3536531 := bstep (se 1 (by rfl) ⟨2652398, by rfl⟩ : syracuseStep 3536531 = 5304797) B5304797
theorem B2356907 : Blo 1570983 2356907 := bstep (se 1 (by rfl) ⟨1767680, by rfl⟩ : syracuseStep 2356907 = 3535361) B3535361
theorem B2356937 : Blo 1570983 2356937 := bstep (se 2 (by rfl) ⟨883851, by rfl⟩ : syracuseStep 2356937 = 1767703) B1767703
theorem B3536585 : Blo 1570983 3536585 := bstep (se 2 (by rfl) ⟨1326219, by rfl⟩ : syracuseStep 3536585 = 2652439) B2652439
theorem B3978953 : Blo 1570983 3978953 := bstep (se 2 (by rfl) ⟨1492107, by rfl⟩ : syracuseStep 3978953 = 2984215) B2984215
theorem B5969645 : Blo 1570983 5969645 := bstep (se 3 (by rfl) ⟨1119308, by rfl⟩ : syracuseStep 5969645 = 2238617) B2238617
theorem B5740321 : Blo 1570983 5740321 := bstep (se 2 (by rfl) ⟨2152620, by rfl⟩ : syracuseStep 5740321 = 4305241) B4305241
theorem B6715169 : Blo 1570983 6715169 := bstep (se 2 (by rfl) ⟨2518188, by rfl⟩ : syracuseStep 6715169 = 5036377) B5036377
theorem B15341363 : Blo 1570983 15341363 := bstep (se 1 (by rfl) ⟨11506022, by rfl⟩ : syracuseStep 15341363 = 23012045) B23012045
theorem B2357051 : Blo 1570983 2357051 := bstep (se 1 (by rfl) ⟨1767788, by rfl⟩ : syracuseStep 2357051 = 3535577) B3535577
theorem B28686149 : Blo 1570983 28686149 := bstep (se 4 (by rfl) ⟨2689326, by rfl⟩ : syracuseStep 28686149 = 5378653) B5378653
theorem B39302981 : Blo 1570983 39302981 := bstep (se 4 (by rfl) ⟨3684654, by rfl⟩ : syracuseStep 39302981 = 7369309) B7369309
theorem B2357111 : Blo 1570983 2357111 := bstep (se 1 (by rfl) ⟨1767833, by rfl⟩ : syracuseStep 2357111 = 3535667) B3535667
theorem B2357135 : Blo 1570983 2357135 := bstep (se 1 (by rfl) ⟨1767851, by rfl⟩ : syracuseStep 2357135 = 3535703) B3535703
theorem B2357177 : Blo 1570983 2357177 := bstep (se 2 (by rfl) ⟨883941, by rfl⟩ : syracuseStep 2357177 = 1767883) B1767883
theorem B8951755 : Blo 1570983 8951755 := bstep (se 1 (by rfl) ⟨6713816, by rfl⟩ : syracuseStep 8951755 = 13427633) B13427633
theorem B2357255 : Blo 1570983 2357255 := bstep (se 1 (by rfl) ⟨1767941, by rfl⟩ : syracuseStep 2357255 = 3535883) B3535883
theorem B1988651 : Blo 1570983 1988651 := bstep (se 1 (by rfl) ⟨1491488, by rfl⟩ : syracuseStep 1988651 = 2982977) B2982977
theorem B2357291 : Blo 1570983 2357291 := bstep (se 1 (by rfl) ⟨1767968, by rfl⟩ : syracuseStep 2357291 = 3535937) B3535937
theorem B2652203 : Blo 1570983 2652203 := bstep (se 1 (by rfl) ⟨1989152, by rfl⟩ : syracuseStep 2652203 = 3978305) B3978305
theorem B3979307 : Blo 1570983 3979307 := bstep (se 1 (by rfl) ⟨2984480, by rfl⟩ : syracuseStep 3979307 = 5968961) B5968961
theorem B5969963 : Blo 1570983 5969963 := bstep (se 1 (by rfl) ⟨4477472, by rfl⟩ : syracuseStep 5969963 = 8954945) B8954945
theorem B2357321 : Blo 1570983 2357321 := bstep (se 2 (by rfl) ⟨883995, by rfl⟩ : syracuseStep 2357321 = 1767991) B1767991
theorem B1767559 : Blo 1570983 1767559 := bstep (se 1 (by rfl) ⟨1325669, by rfl⟩ : syracuseStep 1767559 = 2651339) B2651339
theorem B9074861 : Blo 1570983 9074861 := bstep (se 3 (by rfl) ⟨1701536, by rfl⟩ : syracuseStep 9074861 = 3403073) B3403073
theorem B1571003 : Blo 1570983 1571003 := bstep (se 1 (by rfl) ⟨1178252, by rfl⟩ : syracuseStep 1571003 = 2356505) B2356505
theorem B2357435 : Blo 1570983 2357435 := bstep (se 1 (by rfl) ⟨1768076, by rfl⟩ : syracuseStep 2357435 = 3536153) B3536153
theorem B2357495 : Blo 1570983 2357495 := bstep (se 1 (by rfl) ⟨1768121, by rfl⟩ : syracuseStep 2357495 = 3536243) B3536243
theorem B6371585 : Blo 1570983 6371585 := bstep (se 2 (by rfl) ⟨2389344, by rfl⟩ : syracuseStep 6371585 = 4778689) B4778689
theorem B1571079 : Blo 1570983 1571079 := bstep (se 1 (by rfl) ⟨1178309, by rfl⟩ : syracuseStep 1571079 = 2356619) B2356619
theorem B1571087 : Blo 1570983 1571087 := bstep (se 1 (by rfl) ⟨1178315, by rfl⟩ : syracuseStep 1571087 = 2356631) B2356631
theorem B2357519 : Blo 1570983 2357519 := bstep (se 1 (by rfl) ⟨1768139, by rfl⟩ : syracuseStep 2357519 = 3536279) B3536279
theorem B2357561 : Blo 1570983 2357561 := bstep (se 2 (by rfl) ⟨884085, by rfl⟩ : syracuseStep 2357561 = 1768171) B1768171
theorem B1571131 : Blo 1570983 1571131 := bstep (se 1 (by rfl) ⟨1178348, by rfl⟩ : syracuseStep 1571131 = 2356697) B2356697
theorem B1767739 : Blo 1570983 1767739 := bstep (se 1 (by rfl) ⟨1325804, by rfl⟩ : syracuseStep 1767739 = 2651609) B2651609
theorem B1571207 : Blo 1570983 1571207 := bstep (se 1 (by rfl) ⟨1178405, by rfl⟩ : syracuseStep 1571207 = 2356811) B2356811
theorem B2357639 : Blo 1570983 2357639 := bstep (se 1 (by rfl) ⟨1768229, by rfl⟩ : syracuseStep 2357639 = 3536459) B3536459
theorem B3537287 : Blo 1570983 3537287 := bstep (se 1 (by rfl) ⟨2652965, by rfl⟩ : syracuseStep 3537287 = 5305931) B5305931
theorem B1571215 : Blo 1570983 1571215 := bstep (se 1 (by rfl) ⟨1178411, by rfl⟩ : syracuseStep 1571215 = 2356823) B2356823
theorem B2357675 : Blo 1570983 2357675 := bstep (se 1 (by rfl) ⟨1768256, by rfl⟩ : syracuseStep 2357675 = 3536513) B3536513
theorem B2652601 : Blo 1570983 2652601 := bstep (se 2 (by rfl) ⟨994725, by rfl⟩ : syracuseStep 2652601 = 1989451) B1989451
theorem B1571259 : Blo 1570983 1571259 := bstep (se 1 (by rfl) ⟨1178444, by rfl⟩ : syracuseStep 1571259 = 2356889) B2356889
theorem B2357705 : Blo 1570983 2357705 := bstep (se 2 (by rfl) ⟨884139, by rfl⟩ : syracuseStep 2357705 = 1768279) B1768279
theorem B15104515 : Blo 1570983 15104515 := bstep (se 1 (by rfl) ⟨11328386, by rfl⟩ : syracuseStep 15104515 = 22656773) B22656773
theorem B1571335 : Blo 1570983 1571335 := bstep (se 1 (by rfl) ⟨1178501, by rfl⟩ : syracuseStep 1571335 = 2357003) B2357003
theorem B1989127 : Blo 1570983 1989127 := bstep (se 1 (by rfl) ⟨1491845, by rfl⟩ : syracuseStep 1989127 = 2983691) B2983691
theorem B1677839 : Blo 1570983 1677839 := bstep (se 1 (by rfl) ⟨1258379, by rfl⟩ : syracuseStep 1677839 = 2516759) B2516759
theorem B1571343 : Blo 1570983 1571343 := bstep (se 1 (by rfl) ⟨1178507, by rfl⟩ : syracuseStep 1571343 = 2357015) B2357015
theorem B1571387 : Blo 1570983 1571387 := bstep (se 1 (by rfl) ⟨1178540, by rfl⟩ : syracuseStep 1571387 = 2357081) B2357081
theorem B2357819 : Blo 1570983 2357819 := bstep (se 1 (by rfl) ⟨1768364, by rfl⟩ : syracuseStep 2357819 = 3536729) B3536729
theorem B3537467 : Blo 1570983 3537467 := bstep (se 1 (by rfl) ⟨2653100, by rfl⟩ : syracuseStep 3537467 = 5306201) B5306201
theorem B2357879 : Blo 1570983 2357879 := bstep (se 1 (by rfl) ⟨1768409, by rfl⟩ : syracuseStep 2357879 = 3536819) B3536819
theorem B1571463 : Blo 1570983 1571463 := bstep (se 1 (by rfl) ⟨1178597, by rfl⟩ : syracuseStep 1571463 = 2357195) B2357195
theorem B1571471 : Blo 1570983 1571471 := bstep (se 1 (by rfl) ⟨1178603, by rfl⟩ : syracuseStep 1571471 = 2357207) B2357207
theorem B2357903 : Blo 1570983 2357903 := bstep (se 1 (by rfl) ⟨1768427, by rfl⟩ : syracuseStep 2357903 = 3536855) B3536855
theorem B2357945 : Blo 1570983 2357945 := bstep (se 2 (by rfl) ⟨884229, by rfl⟩ : syracuseStep 2357945 = 1768459) B1768459
theorem B3537593 : Blo 1570983 3537593 := bstep (se 2 (by rfl) ⟨1326597, by rfl⟩ : syracuseStep 3537593 = 2653195) B2653195
theorem B1571515 : Blo 1570983 1571515 := bstep (se 1 (by rfl) ⟨1178636, by rfl⟩ : syracuseStep 1571515 = 2357273) B2357273
theorem B10066625 : Blo 1570983 10066625 := bstep (se 2 (by rfl) ⟨3774984, by rfl⟩ : syracuseStep 10066625 = 7549969) B7549969
theorem B8493761 : Blo 1570983 8493761 := bstep (se 2 (by rfl) ⟨3185160, by rfl⟩ : syracuseStep 8493761 = 6370321) B6370321
theorem B6716141 : Blo 1570983 6716141 := bstep (se 3 (by rfl) ⟨1259276, by rfl⟩ : syracuseStep 6716141 = 2518553) B2518553
theorem B1678087 : Blo 1570983 1678087 := bstep (se 1 (by rfl) ⟨1258565, by rfl⟩ : syracuseStep 1678087 = 2517131) B2517131
theorem B1571591 : Blo 1570983 1571591 := bstep (se 1 (by rfl) ⟨1178693, by rfl⟩ : syracuseStep 1571591 = 2357387) B2357387
theorem B2358023 : Blo 1570983 2358023 := bstep (se 1 (by rfl) ⟨1768517, by rfl⟩ : syracuseStep 2358023 = 3537035) B3537035
theorem B1571599 : Blo 1570983 1571599 := bstep (se 1 (by rfl) ⟨1178699, by rfl⟩ : syracuseStep 1571599 = 2357399) B2357399
theorem B1768207 : Blo 1570983 1768207 := bstep (se 1 (by rfl) ⟨1326155, by rfl⟩ : syracuseStep 1768207 = 2652311) B2652311
theorem B3357455 : Blo 1570983 3357455 := bstep (se 1 (by rfl) ⟨2518091, by rfl⟩ : syracuseStep 3357455 = 5036183) B5036183
theorem B2358059 : Blo 1570983 2358059 := bstep (se 1 (by rfl) ⟨1768544, by rfl⟩ : syracuseStep 2358059 = 3537089) B3537089
theorem B5741371 : Blo 1570983 5741371 := bstep (se 1 (by rfl) ⟨4306028, by rfl⟩ : syracuseStep 5741371 = 8612057) B8612057
theorem B1571643 : Blo 1570983 1571643 := bstep (se 1 (by rfl) ⟨1178732, by rfl⟩ : syracuseStep 1571643 = 2357465) B2357465
theorem B2358089 : Blo 1570983 2358089 := bstep (se 2 (by rfl) ⟨884283, by rfl⟩ : syracuseStep 2358089 = 1768567) B1768567
theorem B1571719 : Blo 1570983 1571719 := bstep (se 1 (by rfl) ⟨1178789, by rfl⟩ : syracuseStep 1571719 = 2357579) B2357579
theorem B1571727 : Blo 1570983 1571727 := bstep (se 1 (by rfl) ⟨1178795, by rfl⟩ : syracuseStep 1571727 = 2357591) B2357591
theorem B1571771 : Blo 1570983 1571771 := bstep (se 1 (by rfl) ⟨1178828, by rfl⟩ : syracuseStep 1571771 = 2357657) B2357657
theorem B2358203 : Blo 1570983 2358203 := bstep (se 1 (by rfl) ⟨1768652, by rfl⟩ : syracuseStep 2358203 = 3537305) B3537305
theorem B1989623 : Blo 1570983 1989623 := bstep (se 1 (by rfl) ⟨1492217, by rfl⟩ : syracuseStep 1989623 = 2984435) B2984435
theorem B2358263 : Blo 1570983 2358263 := bstep (se 1 (by rfl) ⟨1768697, by rfl⟩ : syracuseStep 2358263 = 3537395) B3537395
theorem B1571847 : Blo 1570983 1571847 := bstep (se 1 (by rfl) ⟨1178885, by rfl⟩ : syracuseStep 1571847 = 2357771) B2357771
theorem B3980299 : Blo 1570983 3980299 := bstep (se 1 (by rfl) ⟨2985224, by rfl⟩ : syracuseStep 3980299 = 5970449) B5970449
theorem B1571855 : Blo 1570983 1571855 := bstep (se 1 (by rfl) ⟨1178891, by rfl⟩ : syracuseStep 1571855 = 2357783) B2357783
theorem B2358287 : Blo 1570983 2358287 := bstep (se 1 (by rfl) ⟨1768715, by rfl⟩ : syracuseStep 2358287 = 3537431) B3537431
theorem B3537935 : Blo 1570983 3537935 := bstep (se 1 (by rfl) ⟨2653451, by rfl⟩ : syracuseStep 3537935 = 5306903) B5306903
theorem B3537953 : Blo 1570983 3537953 := bstep (se 2 (by rfl) ⟨1326732, by rfl⟩ : syracuseStep 3537953 = 2653465) B2653465
theorem B2358329 : Blo 1570983 2358329 := bstep (se 2 (by rfl) ⟨884373, by rfl⟩ : syracuseStep 2358329 = 1768747) B1768747
theorem B1571899 : Blo 1570983 1571899 := bstep (se 1 (by rfl) ⟨1178924, by rfl⟩ : syracuseStep 1571899 = 2357849) B2357849
theorem B6716483 : Blo 1570983 6716483 := bstep (se 1 (by rfl) ⟨5037362, by rfl⟩ : syracuseStep 6716483 = 10074725) B10074725
theorem B2653303 : Blo 1570983 2653303 := bstep (se 1 (by rfl) ⟨1989977, by rfl⟩ : syracuseStep 2653303 = 3979955) B3979955
theorem B1571975 : Blo 1570983 1571975 := bstep (se 1 (by rfl) ⟨1178981, by rfl⟩ : syracuseStep 1571975 = 2357963) B2357963
theorem B2358407 : Blo 1570983 2358407 := bstep (se 1 (by rfl) ⟨1768805, by rfl⟩ : syracuseStep 2358407 = 3537611) B3537611
theorem B1571983 : Blo 1570983 1571983 := bstep (se 1 (by rfl) ⟨1178987, by rfl⟩ : syracuseStep 1571983 = 2357975) B2357975
theorem B1989775 : Blo 1570983 1989775 := bstep (se 1 (by rfl) ⟨1492331, by rfl⟩ : syracuseStep 1989775 = 2984663) B2984663
theorem B2358443 : Blo 1570983 2358443 := bstep (se 1 (by rfl) ⟨1768832, by rfl⟩ : syracuseStep 2358443 = 3537665) B3537665
theorem B1572027 : Blo 1570983 1572027 := bstep (se 1 (by rfl) ⟨1179020, by rfl⟩ : syracuseStep 1572027 = 2358041) B2358041
theorem B2358473 : Blo 1570983 2358473 := bstep (se 2 (by rfl) ⟨884427, by rfl⟩ : syracuseStep 2358473 = 1768855) B1768855
theorem B1572103 : Blo 1570983 1572103 := bstep (se 1 (by rfl) ⟨1179077, by rfl⟩ : syracuseStep 1572103 = 2358155) B2358155
theorem B1768711 : Blo 1570983 1768711 := bstep (se 1 (by rfl) ⟨1326533, by rfl⟩ : syracuseStep 1768711 = 2653067) B2653067
theorem B1572111 : Blo 1570983 1572111 := bstep (se 1 (by rfl) ⟨1179083, by rfl⟩ : syracuseStep 1572111 = 2358167) B2358167
theorem B1572155 : Blo 1570983 1572155 := bstep (se 1 (by rfl) ⟨1179116, by rfl⟩ : syracuseStep 1572155 = 2358233) B2358233
theorem B1989947 : Blo 1570983 1989947 := bstep (se 1 (by rfl) ⟨1492460, by rfl⟩ : syracuseStep 1989947 = 2984921) B2984921
theorem B2358587 : Blo 1570983 2358587 := bstep (se 1 (by rfl) ⟨1768940, by rfl⟩ : syracuseStep 2358587 = 3537881) B3537881
theorem B2653499 : Blo 1570983 2653499 := bstep (se 1 (by rfl) ⟨1990124, by rfl⟩ : syracuseStep 2653499 = 3980249) B3980249
theorem B2358647 : Blo 1570983 2358647 := bstep (se 1 (by rfl) ⟨1768985, by rfl⟩ : syracuseStep 2358647 = 3537971) B3537971
theorem B1572231 : Blo 1570983 1572231 := bstep (se 1 (by rfl) ⟨1179173, by rfl⟩ : syracuseStep 1572231 = 2358347) B2358347
theorem B1572239 : Blo 1570983 1572239 := bstep (se 1 (by rfl) ⟨1179179, by rfl⟩ : syracuseStep 1572239 = 2358359) B2358359
theorem B2358671 : Blo 1570983 2358671 := bstep (se 1 (by rfl) ⟨1769003, by rfl⟩ : syracuseStep 2358671 = 3538007) B3538007
theorem B2358713 : Blo 1570983 2358713 := bstep (se 2 (by rfl) ⟨884517, by rfl⟩ : syracuseStep 2358713 = 1769035) B1769035
theorem B1572283 : Blo 1570983 1572283 := bstep (se 1 (by rfl) ⟨1179212, by rfl⟩ : syracuseStep 1572283 = 2358425) B2358425
theorem B1768891 : Blo 1570983 1768891 := bstep (se 1 (by rfl) ⟨1326668, by rfl⟩ : syracuseStep 1768891 = 2653337) B2653337
theorem B1572359 : Blo 1570983 1572359 := bstep (se 1 (by rfl) ⟨1179269, by rfl⟩ : syracuseStep 1572359 = 2358539) B2358539
theorem B1572367 : Blo 1570983 1572367 := bstep (se 1 (by rfl) ⟨1179275, by rfl⟩ : syracuseStep 1572367 = 2358551) B2358551
theorem B1572411 : Blo 1570983 1572411 := bstep (se 1 (by rfl) ⟨1179308, by rfl⟩ : syracuseStep 1572411 = 2358617) B2358617
theorem B9559619 : Blo 1570983 9559619 := bstep (se 1 (by rfl) ⟨7169714, by rfl⟩ : syracuseStep 9559619 = 14339429) B14339429
theorem B3186311 : Blo 1570983 3186311 := bstep (se 1 (by rfl) ⟨2389733, by rfl⟩ : syracuseStep 3186311 = 4779467) B4779467
theorem B7954361 : Blo 1570983 7954361 := bstep (se 2 (by rfl) ⟨2982885, by rfl⟩ : syracuseStep 7954361 = 5965771) B5965771
theorem B2236891 : Blo 1570983 2236891 := bstep (se 1 (by rfl) ⟨1677668, by rfl⟩ : syracuseStep 2236891 = 3355337) B3355337
theorem B13091657 : Blo 1570983 13091657 := bstep (se 2 (by rfl) ⟨4909371, by rfl⟩ : syracuseStep 13091657 = 9818743) B9818743
theorem B2950031 : Blo 1570983 2950031 := bstep (se 1 (by rfl) ⟨2212523, by rfl⟩ : syracuseStep 2950031 = 4425047) B4425047
theorem B4473863 : Blo 1570983 4473863 := bstep (se 1 (by rfl) ⟨3355397, by rfl⟩ : syracuseStep 4473863 = 6710795) B6710795
theorem B2983159 : Blo 1570983 2983159 := bstep (se 1 (by rfl) ⟨2237369, by rfl⟩ : syracuseStep 2983159 = 4474739) B4474739
theorem B2983387 : Blo 1570983 2983387 := bstep (se 1 (by rfl) ⟨2237540, by rfl⟩ : syracuseStep 2983387 = 4475081) B4475081
theorem B2983463 : Blo 1570983 2983463 := bstep (se 1 (by rfl) ⟨2237597, by rfl⟩ : syracuseStep 2983463 = 4475195) B4475195
theorem B2983547 : Blo 1570983 2983547 := bstep (se 1 (by rfl) ⟨2237660, by rfl⟩ : syracuseStep 2983547 = 4475321) B4475321
theorem B8496829 : Blo 1570983 8496829 := bstep (se 3 (by rfl) ⟨1593155, by rfl⟩ : syracuseStep 8496829 = 3186311) B3186311
theorem B6711083 : Blo 1570983 6711083 := bstep (se 1 (by rfl) ⟨5033312, by rfl⟩ : syracuseStep 6711083 = 10066625) B10066625
theorem B27223897 : Blo 1570983 27223897 := bstep (se 2 (by rfl) ⟨10208961, by rfl⟩ : syracuseStep 27223897 = 20417923) B20417923
theorem B2984033 : Blo 1570983 2984033 := bstep (se 2 (by rfl) ⟨1119012, by rfl⟩ : syracuseStep 2984033 = 2238025) B2238025
theorem B7653761 : Blo 1570983 7653761 := bstep (se 2 (by rfl) ⟨2870160, by rfl⟩ : syracuseStep 7653761 = 5740321) B5740321
theorem B5302907 : Blo 1570983 5302907 := bstep (se 1 (by rfl) ⟨3977180, by rfl⟩ : syracuseStep 5302907 = 7954361) B7954361
theorem B5303069 : Blo 1570983 5303069 := bstep (se 3 (by rfl) ⟨994325, by rfl⟩ : syracuseStep 5303069 = 1988651) B1988651
theorem B7957277 : Blo 1570983 7957277 := bstep (se 3 (by rfl) ⟨1491989, by rfl⟩ : syracuseStep 7957277 = 2983979) B2983979
theorem B11938589 : Blo 1570983 11938589 := bstep (se 3 (by rfl) ⟨2238485, by rfl⟩ : syracuseStep 11938589 = 4476971) B4476971
theorem B15109163 : Blo 1570983 15109163 := bstep (se 1 (by rfl) ⟨11331872, by rfl⟩ : syracuseStep 15109163 = 22663745) B22663745
theorem B4246685 : Blo 1570983 4246685 := bstep (se 3 (by rfl) ⟨796253, by rfl⟩ : syracuseStep 4246685 = 1592507) B1592507
theorem B4476151 : Blo 1570983 4476151 := bstep (se 1 (by rfl) ⟨3357113, by rfl⟩ : syracuseStep 4476151 = 6714227) B6714227
theorem B13421861 : Blo 1570983 13421861 := bstep (se 4 (by rfl) ⟨1258299, by rfl⟩ : syracuseStep 13421861 = 2516599) B2516599
theorem B20139353 : Blo 1570983 20139353 := bstep (se 2 (by rfl) ⟨7552257, by rfl⟩ : syracuseStep 20139353 = 15104515) B15104515
theorem B3976553 : Blo 1570983 3976553 := bstep (se 2 (by rfl) ⟨1491207, by rfl⟩ : syracuseStep 3976553 = 2982415) B2982415
theorem B5967229 : Blo 1570983 5967229 := bstep (se 3 (by rfl) ⟨1118855, by rfl⟩ : syracuseStep 5967229 = 2237711) B2237711
theorem B11333027 : Blo 1570983 11333027 := bstep (se 1 (by rfl) ⟨8499770, by rfl⟩ : syracuseStep 11333027 = 16999541) B16999541
theorem B5303771 : Blo 1570983 5303771 := bstep (se 1 (by rfl) ⟨3977828, by rfl⟩ : syracuseStep 5303771 = 7955657) B7955657
theorem B4476379 : Blo 1570983 4476379 := bstep (se 1 (by rfl) ⟨3357284, by rfl⟩ : syracuseStep 4476379 = 6714569) B6714569
theorem B4476539 : Blo 1570983 4476539 := bstep (se 1 (by rfl) ⟨3357404, by rfl⟩ : syracuseStep 4476539 = 6714809) B6714809
theorem B5664467 : Blo 1570983 5664467 := bstep (se 1 (by rfl) ⟨4248350, by rfl⟩ : syracuseStep 5664467 = 8496701) B8496701
theorem B9555677 : Blo 1570983 9555677 := bstep (se 3 (by rfl) ⟨1791689, by rfl⟩ : syracuseStep 9555677 = 3583379) B3583379
theorem B7655161 : Blo 1570983 7655161 := bstep (se 2 (by rfl) ⟨2870685, by rfl⟩ : syracuseStep 7655161 = 5741371) B5741371
theorem B4476779 : Blo 1570983 4476779 := bstep (se 1 (by rfl) ⟨3357584, by rfl⟩ : syracuseStep 4476779 = 6715169) B6715169
theorem B10227575 : Blo 1570983 10227575 := bstep (se 1 (by rfl) ⟨7670681, by rfl⟩ : syracuseStep 10227575 = 15341363) B15341363
theorem B19124099 : Blo 1570983 19124099 := bstep (se 1 (by rfl) ⟨14343074, by rfl⟩ : syracuseStep 19124099 = 28686149) B28686149
theorem B26201987 : Blo 1570983 26201987 := bstep (se 1 (by rfl) ⟨19651490, by rfl⟩ : syracuseStep 26201987 = 39302981) B39302981
theorem B3534767 : Blo 1570983 3534767 := bstep (se 1 (by rfl) ⟨2651075, by rfl⟩ : syracuseStep 3534767 = 5302151) B5302151
theorem B9072647 : Blo 1570983 9072647 := bstep (se 1 (by rfl) ⟨6804485, by rfl⟩ : syracuseStep 9072647 = 13608971) B13608971
theorem B8949797 : Blo 1570983 8949797 := bstep (se 4 (by rfl) ⟨839043, by rfl⟩ : syracuseStep 8949797 = 1678087) B1678087
theorem B6049907 : Blo 1570983 6049907 := bstep (se 1 (by rfl) ⟨4537430, by rfl⟩ : syracuseStep 6049907 = 9074861) B9074861
theorem B5304473 : Blo 1570983 5304473 := bstep (se 2 (by rfl) ⟨1989177, by rfl⟩ : syracuseStep 5304473 = 3978355) B3978355
theorem B3535019 : Blo 1570983 3535019 := bstep (se 1 (by rfl) ⟨2651264, by rfl⟩ : syracuseStep 3535019 = 5302529) B5302529
theorem B4247723 : Blo 1570983 4247723 := bstep (se 1 (by rfl) ⟨3185792, by rfl⟩ : syracuseStep 4247723 = 6371585) B6371585
theorem B12103937 : Blo 1570983 12103937 := bstep (se 2 (by rfl) ⟨4538976, by rfl⟩ : syracuseStep 12103937 = 9077953) B9077953
theorem B20132225 : Blo 1570983 20132225 := bstep (se 2 (by rfl) ⟨7549584, by rfl⟩ : syracuseStep 20132225 = 15099169) B15099169
theorem B12743041 : Blo 1570983 12743041 := bstep (se 2 (by rfl) ⟨4778640, by rfl⟩ : syracuseStep 12743041 = 9557281) B9557281
theorem B4477427 : Blo 1570983 4477427 := bstep (se 1 (by rfl) ⟨3358070, by rfl⟩ : syracuseStep 4477427 = 6716141) B6716141
theorem B8950297 : Blo 1570983 8950297 := bstep (se 2 (by rfl) ⟨3356361, by rfl⟩ : syracuseStep 8950297 = 6712723) B6712723
theorem B3535559 : Blo 1570983 3535559 := bstep (se 1 (by rfl) ⟨2651669, by rfl⟩ : syracuseStep 3535559 = 5303339) B5303339
theorem B4477655 : Blo 1570983 4477655 := bstep (se 1 (by rfl) ⟨3358241, by rfl⟩ : syracuseStep 4477655 = 6716483) B6716483
theorem B2651143 : Blo 1570983 2651143 := bstep (se 1 (by rfl) ⟨1988357, by rfl⟩ : syracuseStep 2651143 = 3976715) B3976715
theorem B5666039 : Blo 1570983 5666039 := bstep (se 1 (by rfl) ⟨4249529, by rfl⟩ : syracuseStep 5666039 = 8499059) B8499059
theorem B5305661 : Blo 1570983 5305661 := bstep (se 3 (by rfl) ⟨994811, by rfl⟩ : syracuseStep 5305661 = 1989623) B1989623
theorem B2356655 : Blo 1570983 2356655 := bstep (se 1 (by rfl) ⟨1767491, by rfl⟩ : syracuseStep 2356655 = 3534983) B3534983
theorem B2651575 : Blo 1570983 2651575 := bstep (se 1 (by rfl) ⟨1988681, by rfl⟩ : syracuseStep 2651575 = 3977363) B3977363
theorem B17896949 : Blo 1570983 17896949 := bstep (se 5 (by rfl) ⟨838919, by rfl⟩ : syracuseStep 17896949 = 1677839) B1677839
theorem B2356745 : Blo 1570983 2356745 := bstep (se 2 (by rfl) ⟨883779, by rfl⟩ : syracuseStep 2356745 = 1767559) B1767559
theorem B2356775 : Blo 1570983 2356775 := bstep (se 1 (by rfl) ⟨1767581, by rfl⟩ : syracuseStep 2356775 = 3535163) B3535163
theorem B3536423 : Blo 1570983 3536423 := bstep (se 1 (by rfl) ⟨2652317, by rfl⟩ : syracuseStep 3536423 = 5304635) B5304635
theorem B3978791 : Blo 1570983 3978791 := bstep (se 1 (by rfl) ⟨2984093, by rfl⟩ : syracuseStep 3978791 = 5968187) B5968187
theorem B5969447 : Blo 1570983 5969447 := bstep (se 1 (by rfl) ⟨4477085, by rfl⟩ : syracuseStep 5969447 = 8954171) B8954171
theorem B2356859 : Blo 1570983 2356859 := bstep (se 1 (by rfl) ⟨1767644, by rfl⟩ : syracuseStep 2356859 = 3535289) B3535289
theorem B2651771 : Blo 1570983 2651771 := bstep (se 1 (by rfl) ⟨1988828, by rfl⟩ : syracuseStep 2651771 = 3977657) B3977657
theorem B24188615 : Blo 1570983 24188615 := bstep (se 1 (by rfl) ⟨18141461, by rfl⟩ : syracuseStep 24188615 = 36282923) B36282923
theorem B2356985 : Blo 1570983 2356985 := bstep (se 2 (by rfl) ⟨883869, by rfl⟩ : syracuseStep 2356985 = 1767739) B1767739
theorem B30218021 : Blo 1570983 30218021 := bstep (se 4 (by rfl) ⟨2832939, by rfl⟩ : syracuseStep 30218021 = 5665879) B5665879
theorem B7550815 : Blo 1570983 7550815 := bstep (se 1 (by rfl) ⟨5663111, by rfl⟩ : syracuseStep 7550815 = 11326223) B11326223
theorem B2357087 : Blo 1570983 2357087 := bstep (se 1 (by rfl) ⟨1767815, by rfl⟩ : syracuseStep 2357087 = 3535631) B3535631
theorem B2357099 : Blo 1570983 2357099 := bstep (se 1 (by rfl) ⟨1767824, by rfl⟩ : syracuseStep 2357099 = 3535649) B3535649
theorem B3536747 : Blo 1570983 3536747 := bstep (se 1 (by rfl) ⟨2652560, by rfl⟩ : syracuseStep 3536747 = 5305121) B5305121
theorem B3979115 : Blo 1570983 3979115 := bstep (se 1 (by rfl) ⟨2984336, by rfl⟩ : syracuseStep 3979115 = 5968673) B5968673
theorem B3536801 : Blo 1570983 3536801 := bstep (se 2 (by rfl) ⟨1326300, by rfl⟩ : syracuseStep 3536801 = 2652601) B2652601
theorem B2652169 : Blo 1570983 2652169 := bstep (se 2 (by rfl) ⟨994563, by rfl⟩ : syracuseStep 2652169 = 1989127) B1989127
theorem B8493113 : Blo 1570983 8493113 := bstep (se 2 (by rfl) ⟨3184917, by rfl⟩ : syracuseStep 8493113 = 6369835) B6369835
theorem B2357327 : Blo 1570983 2357327 := bstep (se 1 (by rfl) ⟨1767995, by rfl⟩ : syracuseStep 2357327 = 3535991) B3535991
theorem B23926873 : Blo 1570983 23926873 := bstep (se 2 (by rfl) ⟨8972577, by rfl⟩ : syracuseStep 23926873 = 17945155) B17945155
theorem B5306525 : Blo 1570983 5306525 := bstep (se 3 (by rfl) ⟨994973, by rfl⟩ : syracuseStep 5306525 = 1989947) B1989947
theorem B2652331 : Blo 1570983 2652331 := bstep (se 1 (by rfl) ⟨1989248, by rfl⟩ : syracuseStep 2652331 = 3978497) B3978497
theorem B1570991 : Blo 1570983 1570991 := bstep (se 1 (by rfl) ⟨1178243, by rfl⟩ : syracuseStep 1570991 = 2356487) B2356487
theorem B1571015 : Blo 1570983 1571015 := bstep (se 1 (by rfl) ⟨1178261, by rfl⟩ : syracuseStep 1571015 = 2356523) B2356523
theorem B2357447 : Blo 1570983 2357447 := bstep (se 1 (by rfl) ⟨1768085, by rfl⟩ : syracuseStep 2357447 = 3536171) B3536171
theorem B1571035 : Blo 1570983 1571035 := bstep (se 1 (by rfl) ⟨1178276, by rfl⟩ : syracuseStep 1571035 = 2356553) B2356553
theorem B3537143 : Blo 1570983 3537143 := bstep (se 1 (by rfl) ⟨2652857, by rfl⟩ : syracuseStep 3537143 = 5305715) B5305715
theorem B1571111 : Blo 1570983 1571111 := bstep (se 1 (by rfl) ⟨1178333, by rfl⟩ : syracuseStep 1571111 = 2356667) B2356667
theorem B1571151 : Blo 1570983 1571151 := bstep (se 1 (by rfl) ⟨1178363, by rfl⟩ : syracuseStep 1571151 = 2356727) B2356727
theorem B1571167 : Blo 1570983 1571167 := bstep (se 1 (by rfl) ⟨1178375, by rfl⟩ : syracuseStep 1571167 = 2356751) B2356751
theorem B1767775 : Blo 1570983 1767775 := bstep (se 1 (by rfl) ⟨1325831, by rfl⟩ : syracuseStep 1767775 = 2651663) B2651663
theorem B2357609 : Blo 1570983 2357609 := bstep (se 2 (by rfl) ⟨884103, by rfl⟩ : syracuseStep 2357609 = 1768207) B1768207
theorem B1571195 : Blo 1570983 1571195 := bstep (se 1 (by rfl) ⟨1178396, by rfl⟩ : syracuseStep 1571195 = 2356793) B2356793
theorem B21502343 : Blo 1570983 21502343 := bstep (se 1 (by rfl) ⟨16126757, by rfl⟩ : syracuseStep 21502343 = 32253515) B32253515
theorem B1571247 : Blo 1570983 1571247 := bstep (se 1 (by rfl) ⟨1178435, by rfl⟩ : syracuseStep 1571247 = 2356871) B2356871
theorem B2357687 : Blo 1570983 2357687 := bstep (se 1 (by rfl) ⟨1768265, by rfl⟩ : syracuseStep 2357687 = 3536531) B3536531
theorem B1571271 : Blo 1570983 1571271 := bstep (se 1 (by rfl) ⟨1178453, by rfl⟩ : syracuseStep 1571271 = 2356907) B2356907
theorem B1571291 : Blo 1570983 1571291 := bstep (se 1 (by rfl) ⟨1178468, by rfl⟩ : syracuseStep 1571291 = 2356937) B2356937
theorem B2357723 : Blo 1570983 2357723 := bstep (se 1 (by rfl) ⟨1768292, by rfl⟩ : syracuseStep 2357723 = 3536585) B3536585
theorem B2652635 : Blo 1570983 2652635 := bstep (se 1 (by rfl) ⟨1989476, by rfl⟩ : syracuseStep 2652635 = 3978953) B3978953
theorem B3979763 : Blo 1570983 3979763 := bstep (se 1 (by rfl) ⟨2984822, by rfl⟩ : syracuseStep 3979763 = 5969645) B5969645
theorem B5970419 : Blo 1570983 5970419 := bstep (se 1 (by rfl) ⟨4477814, by rfl⟩ : syracuseStep 5970419 = 8955629) B8955629
theorem B1571367 : Blo 1570983 1571367 := bstep (se 1 (by rfl) ⟨1178525, by rfl⟩ : syracuseStep 1571367 = 2357051) B2357051
theorem B1571407 : Blo 1570983 1571407 := bstep (se 1 (by rfl) ⟨1178555, by rfl⟩ : syracuseStep 1571407 = 2357111) B2357111
theorem B1571423 : Blo 1570983 1571423 := bstep (se 1 (by rfl) ⟨1178567, by rfl⟩ : syracuseStep 1571423 = 2357135) B2357135
theorem B1571451 : Blo 1570983 1571451 := bstep (se 1 (by rfl) ⟨1178588, by rfl⟩ : syracuseStep 1571451 = 2357177) B2357177
theorem B1571503 : Blo 1570983 1571503 := bstep (se 1 (by rfl) ⟨1178627, by rfl⟩ : syracuseStep 1571503 = 2357255) B2357255
theorem B5307065 : Blo 1570983 5307065 := bstep (se 2 (by rfl) ⟨1990149, by rfl⟩ : syracuseStep 5307065 = 3980299) B3980299
theorem B1571527 : Blo 1570983 1571527 := bstep (se 1 (by rfl) ⟨1178645, by rfl⟩ : syracuseStep 1571527 = 2357291) B2357291
theorem B1768135 : Blo 1570983 1768135 := bstep (se 1 (by rfl) ⟨1326101, by rfl⟩ : syracuseStep 1768135 = 2652203) B2652203
theorem B2652871 : Blo 1570983 2652871 := bstep (se 1 (by rfl) ⟨1989653, by rfl⟩ : syracuseStep 2652871 = 3979307) B3979307
theorem B3979975 : Blo 1570983 3979975 := bstep (se 1 (by rfl) ⟨2984981, by rfl⟩ : syracuseStep 3979975 = 5969963) B5969963
theorem B1571547 : Blo 1570983 1571547 := bstep (se 1 (by rfl) ⟨1178660, by rfl⟩ : syracuseStep 1571547 = 2357321) B2357321
theorem B1571623 : Blo 1570983 1571623 := bstep (se 1 (by rfl) ⟨1178717, by rfl⟩ : syracuseStep 1571623 = 2357435) B2357435
theorem B3537737 : Blo 1570983 3537737 := bstep (se 2 (by rfl) ⟨1326651, by rfl⟩ : syracuseStep 3537737 = 2653303) B2653303
theorem B1571663 : Blo 1570983 1571663 := bstep (se 1 (by rfl) ⟨1178747, by rfl⟩ : syracuseStep 1571663 = 2357495) B2357495
theorem B1571679 : Blo 1570983 1571679 := bstep (se 1 (by rfl) ⟨1178759, by rfl⟩ : syracuseStep 1571679 = 2357519) B2357519
theorem B2653033 : Blo 1570983 2653033 := bstep (se 2 (by rfl) ⟨994887, by rfl⟩ : syracuseStep 2653033 = 1989775) B1989775
theorem B1571707 : Blo 1570983 1571707 := bstep (se 1 (by rfl) ⟨1178780, by rfl⟩ : syracuseStep 1571707 = 2357561) B2357561
theorem B1571759 : Blo 1570983 1571759 := bstep (se 1 (by rfl) ⟨1178819, by rfl⟩ : syracuseStep 1571759 = 2357639) B2357639
theorem B2358191 : Blo 1570983 2358191 := bstep (se 1 (by rfl) ⟨1768643, by rfl⟩ : syracuseStep 2358191 = 3537287) B3537287
theorem B1571783 : Blo 1570983 1571783 := bstep (se 1 (by rfl) ⟨1178837, by rfl⟩ : syracuseStep 1571783 = 2357675) B2357675
theorem B1571803 : Blo 1570983 1571803 := bstep (se 1 (by rfl) ⟨1178852, by rfl⟩ : syracuseStep 1571803 = 2357705) B2357705
theorem B2358281 : Blo 1570983 2358281 := bstep (se 2 (by rfl) ⟨884355, by rfl⟩ : syracuseStep 2358281 = 1768711) B1768711
theorem B1571879 : Blo 1570983 1571879 := bstep (se 1 (by rfl) ⟨1178909, by rfl⟩ : syracuseStep 1571879 = 2357819) B2357819
theorem B2358311 : Blo 1570983 2358311 := bstep (se 1 (by rfl) ⟨1768733, by rfl⟩ : syracuseStep 2358311 = 3537467) B3537467
theorem B1793063 : Blo 1570983 1793063 := bstep (se 1 (by rfl) ⟨1344797, by rfl⟩ : syracuseStep 1793063 = 2689595) B2689595
theorem B1571919 : Blo 1570983 1571919 := bstep (se 1 (by rfl) ⟨1178939, by rfl⟩ : syracuseStep 1571919 = 2357879) B2357879
theorem B1571935 : Blo 1570983 1571935 := bstep (se 1 (by rfl) ⟨1178951, by rfl⟩ : syracuseStep 1571935 = 2357903) B2357903
theorem B1571963 : Blo 1570983 1571963 := bstep (se 1 (by rfl) ⟨1178972, by rfl⟩ : syracuseStep 1571963 = 2357945) B2357945
theorem B2358395 : Blo 1570983 2358395 := bstep (se 1 (by rfl) ⟨1768796, by rfl⟩ : syracuseStep 2358395 = 3537593) B3537593
theorem B22650029 : Blo 1570983 22650029 := bstep (se 3 (by rfl) ⟨4246880, by rfl⟩ : syracuseStep 22650029 = 8493761) B8493761
theorem B1572015 : Blo 1570983 1572015 := bstep (se 1 (by rfl) ⟨1179011, by rfl⟩ : syracuseStep 1572015 = 2358023) B2358023
theorem B13425857 : Blo 1570983 13425857 := bstep (se 2 (by rfl) ⟨5034696, by rfl⟩ : syracuseStep 13425857 = 10069393) B10069393
theorem B25500865 : Blo 1570983 25500865 := bstep (se 2 (by rfl) ⟨9562824, by rfl⟩ : syracuseStep 25500865 = 19125649) B19125649
theorem B1572039 : Blo 1570983 1572039 := bstep (se 1 (by rfl) ⟨1179029, by rfl⟩ : syracuseStep 1572039 = 2358059) B2358059
theorem B1572059 : Blo 1570983 1572059 := bstep (se 1 (by rfl) ⟨1179044, by rfl⟩ : syracuseStep 1572059 = 2358089) B2358089
theorem B2358521 : Blo 1570983 2358521 := bstep (se 2 (by rfl) ⟨884445, by rfl⟩ : syracuseStep 2358521 = 1768891) B1768891
theorem B22666513 : Blo 1570983 22666513 := bstep (se 2 (by rfl) ⟨8499942, by rfl⟩ : syracuseStep 22666513 = 16999885) B16999885
theorem B1572135 : Blo 1570983 1572135 := bstep (se 1 (by rfl) ⟨1179101, by rfl⟩ : syracuseStep 1572135 = 2358203) B2358203
theorem B1572175 : Blo 1570983 1572175 := bstep (se 1 (by rfl) ⟨1179131, by rfl⟩ : syracuseStep 1572175 = 2358263) B2358263
theorem B1572191 : Blo 1570983 1572191 := bstep (se 1 (by rfl) ⟨1179143, by rfl⟩ : syracuseStep 1572191 = 2358287) B2358287
theorem B2358623 : Blo 1570983 2358623 := bstep (se 1 (by rfl) ⟨1768967, by rfl⟩ : syracuseStep 2358623 = 3537935) B3537935
theorem B2358635 : Blo 1570983 2358635 := bstep (se 1 (by rfl) ⟨1768976, by rfl⟩ : syracuseStep 2358635 = 3537953) B3537953
theorem B1572219 : Blo 1570983 1572219 := bstep (se 1 (by rfl) ⟨1179164, by rfl⟩ : syracuseStep 1572219 = 2358329) B2358329
theorem B8953213 : Blo 1570983 8953213 := bstep (se 3 (by rfl) ⟨1678727, by rfl⟩ : syracuseStep 8953213 = 3357455) B3357455
theorem B1572271 : Blo 1570983 1572271 := bstep (se 1 (by rfl) ⟨1179203, by rfl⟩ : syracuseStep 1572271 = 2358407) B2358407
theorem B1572295 : Blo 1570983 1572295 := bstep (se 1 (by rfl) ⟨1179221, by rfl⟩ : syracuseStep 1572295 = 2358443) B2358443
theorem B1572315 : Blo 1570983 1572315 := bstep (se 1 (by rfl) ⟨1179236, by rfl⟩ : syracuseStep 1572315 = 2358473) B2358473
theorem B1572391 : Blo 1570983 1572391 := bstep (se 1 (by rfl) ⟨1179293, by rfl⟩ : syracuseStep 1572391 = 2358587) B2358587
theorem B1768999 : Blo 1570983 1768999 := bstep (se 1 (by rfl) ⟨1326749, by rfl⟩ : syracuseStep 1768999 = 2653499) B2653499
theorem B2268751 : Blo 1570983 2268751 := bstep (se 1 (by rfl) ⟨1701563, by rfl⟩ : syracuseStep 2268751 = 3403127) B3403127
theorem B1572431 : Blo 1570983 1572431 := bstep (se 1 (by rfl) ⟨1179323, by rfl⟩ : syracuseStep 1572431 = 2358647) B2358647
theorem B1572447 : Blo 1570983 1572447 := bstep (se 1 (by rfl) ⟨1179335, by rfl⟩ : syracuseStep 1572447 = 2358671) B2358671
theorem B1572475 : Blo 1570983 1572475 := bstep (se 1 (by rfl) ⟨1179356, by rfl⟩ : syracuseStep 1572475 = 2358713) B2358713
theorem B10755773 : Blo 1570983 10755773 := bstep (se 3 (by rfl) ⟨2016707, by rfl⟩ : syracuseStep 10755773 = 4033415) B4033415
theorem B3776215 : Blo 1570983 3776215 := bstep (se 1 (by rfl) ⟨2832161, by rfl⟩ : syracuseStep 3776215 = 5664323) B5664323
theorem B6373079 : Blo 1570983 6373079 := bstep (se 1 (by rfl) ⟨4779809, by rfl⟩ : syracuseStep 6373079 = 9559619) B9559619
theorem B11935673 : Blo 1570983 11935673 := bstep (se 2 (by rfl) ⟨4475877, by rfl⟩ : syracuseStep 11935673 = 8951755) B8951755
theorem B8069291 : Blo 1570983 8069291 := bstep (se 1 (by rfl) ⟨6051968, by rfl⟩ : syracuseStep 8069291 = 12103937) B12103937
theorem B16990721 : Blo 1570983 16990721 := bstep (se 2 (by rfl) ⟨6371520, by rfl⟩ : syracuseStep 16990721 = 12743041) B12743041
theorem B1966687 : Blo 1570983 1966687 := bstep (se 1 (by rfl) ⟨1475015, by rfl⟩ : syracuseStep 1966687 = 2950031) B2950031
theorem B2982521 : Blo 1570983 2982521 := bstep (se 2 (by rfl) ⟨1118445, by rfl⟩ : syracuseStep 2982521 = 2236891) B2236891
theorem B2982575 : Blo 1570983 2982575 := bstep (se 1 (by rfl) ⟨2236931, by rfl⟩ : syracuseStep 2982575 = 4473863) B4473863
theorem B3777359 : Blo 1570983 3777359 := bstep (se 1 (by rfl) ⟨2833019, by rfl⟩ : syracuseStep 3777359 = 5666039) B5666039
theorem B20145347 : Blo 1570983 20145347 := bstep (se 1 (by rfl) ⟨15109010, by rfl⟩ : syracuseStep 20145347 = 30218021) B30218021
theorem B4474055 : Blo 1570983 4474055 := bstep (se 1 (by rfl) ⟨3355541, by rfl⟩ : syracuseStep 4474055 = 6711083) B6711083
theorem B3979631 : Blo 1570983 3979631 := bstep (se 1 (by rfl) ⟨2984723, by rfl⟩ : syracuseStep 3979631 = 5969447) B5969447
theorem B5662075 : Blo 1570983 5662075 := bstep (se 1 (by rfl) ⟨4246556, by rfl⟩ : syracuseStep 5662075 = 8493113) B8493113
theorem B30222017 : Blo 1570983 30222017 := bstep (se 2 (by rfl) ⟨11333256, by rfl⟩ : syracuseStep 30222017 = 22666513) B22666513
theorem B7956305 : Blo 1570983 7956305 := bstep (se 2 (by rfl) ⟨2983614, by rfl⟩ : syracuseStep 7956305 = 5967229) B5967229
theorem B11937617 : Blo 1570983 11937617 := bstep (se 2 (by rfl) ⟨4476606, by rfl⟩ : syracuseStep 11937617 = 8953213) B8953213
theorem B3025001 : Blo 1570983 3025001 := bstep (se 2 (by rfl) ⟨1134375, by rfl⟩ : syracuseStep 3025001 = 2268751) B2268751
theorem B15100019 : Blo 1570983 15100019 := bstep (se 1 (by rfl) ⟨11325014, by rfl⟩ : syracuseStep 15100019 = 22650029) B22650029
theorem B8947907 : Blo 1570983 8947907 := bstep (se 1 (by rfl) ⟨6710930, by rfl⟩ : syracuseStep 8947907 = 13421861) B13421861
theorem B7555351 : Blo 1570983 7555351 := bstep (se 1 (by rfl) ⟨5666513, by rfl⟩ : syracuseStep 7555351 = 11333027) B11333027
theorem B2984359 : Blo 1570983 2984359 := bstep (se 1 (by rfl) ⟨2238269, by rfl⟩ : syracuseStep 2984359 = 4476539) B4476539
theorem B7170515 : Blo 1570983 7170515 := bstep (se 1 (by rfl) ⟨5377886, by rfl⟩ : syracuseStep 7170515 = 10755773) B10755773
theorem B2984519 : Blo 1570983 2984519 := bstep (se 1 (by rfl) ⟨2238389, by rfl⟩ : syracuseStep 2984519 = 4476779) B4476779
theorem B6818383 : Blo 1570983 6818383 := bstep (se 1 (by rfl) ⟨5113787, by rfl⟩ : syracuseStep 6818383 = 10227575) B10227575
theorem B12749399 : Blo 1570983 12749399 := bstep (se 1 (by rfl) ⟨9562049, by rfl⟩ : syracuseStep 12749399 = 19124099) B19124099
theorem B17467991 : Blo 1570983 17467991 := bstep (se 1 (by rfl) ⟨13100993, by rfl⟩ : syracuseStep 17467991 = 26201987) B26201987
theorem B7957115 : Blo 1570983 7957115 := bstep (se 1 (by rfl) ⟨5967836, by rfl⟩ : syracuseStep 7957115 = 11935673) B11935673
theorem B6048431 : Blo 1570983 6048431 := bstep (se 1 (by rfl) ⟨4536323, by rfl⟩ : syracuseStep 6048431 = 9072647) B9072647
theorem B5966531 : Blo 1570983 5966531 := bstep (se 1 (by rfl) ⟨4474898, by rfl⟩ : syracuseStep 5966531 = 8949797) B8949797
theorem B4033271 : Blo 1570983 4033271 := bstep (se 1 (by rfl) ⟨3024953, by rfl⟩ : syracuseStep 4033271 = 6049907) B6049907
theorem B31902497 : Blo 1570983 31902497 := bstep (se 2 (by rfl) ⟨11963436, by rfl⟩ : syracuseStep 31902497 = 23926873) B23926873
theorem B13421483 : Blo 1570983 13421483 := bstep (se 1 (by rfl) ⟨10066112, by rfl⟩ : syracuseStep 13421483 = 20132225) B20132225
theorem B2984951 : Blo 1570983 2984951 := bstep (se 1 (by rfl) ⟨2238713, by rfl⟩ : syracuseStep 2984951 = 4477427) B4477427
theorem B2985103 : Blo 1570983 2985103 := bstep (se 1 (by rfl) ⟨2238827, by rfl⟩ : syracuseStep 2985103 = 4477655) B4477655
theorem B139644341 : Blo 1570983 139644341 := bstep (se 5 (by rfl) ⟨6545828, by rfl⟩ : syracuseStep 139644341 = 13091657) B13091657
theorem B11931299 : Blo 1570983 11931299 := bstep (se 1 (by rfl) ⟨8948474, by rfl⟩ : syracuseStep 11931299 = 17896949) B17896949
theorem B16125743 : Blo 1570983 16125743 := bstep (se 1 (by rfl) ⟨12094307, by rfl⟩ : syracuseStep 16125743 = 24188615) B24188615
theorem B3534857 : Blo 1570983 3534857 := bstep (se 2 (by rfl) ⟨1325571, by rfl⟩ : syracuseStep 3534857 = 2651143) B2651143
theorem B34001153 : Blo 1570983 34001153 := bstep (se 2 (by rfl) ⟨12750432, by rfl⟩ : syracuseStep 34001153 = 25500865) B25500865
theorem B3977545 : Blo 1570983 3977545 := bstep (se 2 (by rfl) ⟨1491579, by rfl⟩ : syracuseStep 3977545 = 2983159) B2983159
theorem B5968201 : Blo 1570983 5968201 := bstep (se 2 (by rfl) ⟨2238075, by rfl⟩ : syracuseStep 5968201 = 4476151) B4476151
theorem B3535271 : Blo 1570983 3535271 := bstep (se 1 (by rfl) ⟨2651453, by rfl⟩ : syracuseStep 3535271 = 5302907) B5302907
theorem B3980279 : Blo 1570983 3980279 := bstep (se 1 (by rfl) ⟨2985209, by rfl⟩ : syracuseStep 3980279 = 5970419) B5970419
theorem B3535379 : Blo 1570983 3535379 := bstep (se 1 (by rfl) ⟨2651534, by rfl⟩ : syracuseStep 3535379 = 5303069) B5303069
theorem B5304851 : Blo 1570983 5304851 := bstep (se 1 (by rfl) ⟨3978638, by rfl⟩ : syracuseStep 5304851 = 7957277) B7957277
theorem B7959059 : Blo 1570983 7959059 := bstep (se 1 (by rfl) ⟨5969294, by rfl⟩ : syracuseStep 7959059 = 11938589) B11938589
theorem B3535433 : Blo 1570983 3535433 := bstep (se 2 (by rfl) ⟨1325787, by rfl⟩ : syracuseStep 3535433 = 2651575) B2651575
theorem B3977849 : Blo 1570983 3977849 := bstep (se 2 (by rfl) ⟨1491693, by rfl⟩ : syracuseStep 3977849 = 2983387) B2983387
theorem B5968505 : Blo 1570983 5968505 := bstep (se 2 (by rfl) ⟨2238189, by rfl⟩ : syracuseStep 5968505 = 4476379) B4476379
theorem B10072775 : Blo 1570983 10072775 := bstep (se 1 (by rfl) ⟨7554581, by rfl⟩ : syracuseStep 10072775 = 15109163) B15109163
theorem B2831123 : Blo 1570983 2831123 := bstep (se 1 (by rfl) ⟨2123342, by rfl⟩ : syracuseStep 2831123 = 4246685) B4246685
theorem B8950571 : Blo 1570983 8950571 := bstep (se 1 (by rfl) ⟨6712928, by rfl⟩ : syracuseStep 8950571 = 13425857) B13425857
theorem B2651035 : Blo 1570983 2651035 := bstep (se 1 (by rfl) ⟨1988276, by rfl⟩ : syracuseStep 2651035 = 3976553) B3976553
theorem B5034953 : Blo 1570983 5034953 := bstep (se 2 (by rfl) ⟨1888107, by rfl⟩ : syracuseStep 5034953 = 3776215) B3776215
theorem B3535847 : Blo 1570983 3535847 := bstep (se 1 (by rfl) ⟨2651885, by rfl⟩ : syracuseStep 3535847 = 5303771) B5303771
theorem B4248719 : Blo 1570983 4248719 := bstep (se 1 (by rfl) ⟨3186539, by rfl⟩ : syracuseStep 4248719 = 6373079) B6373079
theorem B6370451 : Blo 1570983 6370451 := bstep (se 1 (by rfl) ⟨4777838, by rfl⟩ : syracuseStep 6370451 = 9555677) B9555677
theorem B2356511 : Blo 1570983 2356511 := bstep (se 1 (by rfl) ⟨1767383, by rfl⟩ : syracuseStep 2356511 = 3534767) B3534767
theorem B3536225 : Blo 1570983 3536225 := bstep (se 2 (by rfl) ⟨1326084, by rfl⟩ : syracuseStep 3536225 = 2652169) B2652169
theorem B3536315 : Blo 1570983 3536315 := bstep (se 1 (by rfl) ⟨2652236, by rfl⟩ : syracuseStep 3536315 = 5304473) B5304473
theorem B4781501 : Blo 1570983 4781501 := bstep (se 3 (by rfl) ⟨896531, by rfl⟩ : syracuseStep 4781501 = 1793063) B1793063
theorem B2356679 : Blo 1570983 2356679 := bstep (se 1 (by rfl) ⟨1767509, by rfl⟩ : syracuseStep 2356679 = 3535019) B3535019
theorem B2831815 : Blo 1570983 2831815 := bstep (se 1 (by rfl) ⟨2123861, by rfl⟩ : syracuseStep 2831815 = 4247723) B4247723
theorem B3536441 : Blo 1570983 3536441 := bstep (se 2 (by rfl) ⟨1326165, by rfl⟩ : syracuseStep 3536441 = 2652331) B2652331
theorem B2357033 : Blo 1570983 2357033 := bstep (se 2 (by rfl) ⟨883887, by rfl⟩ : syracuseStep 2357033 = 1767775) B1767775
theorem B2357039 : Blo 1570983 2357039 := bstep (se 1 (by rfl) ⟨1767779, by rfl⟩ : syracuseStep 2357039 = 3535559) B3535559
theorem B11933729 : Blo 1570983 11933729 := bstep (se 2 (by rfl) ⟨4475148, by rfl⟩ : syracuseStep 11933729 = 8950297) B8950297
theorem B3537107 : Blo 1570983 3537107 := bstep (se 1 (by rfl) ⟨2652830, by rfl⟩ : syracuseStep 3537107 = 5305661) B5305661
theorem B2357513 : Blo 1570983 2357513 := bstep (se 2 (by rfl) ⟨884067, by rfl⟩ : syracuseStep 2357513 = 1768135) B1768135
theorem B3537161 : Blo 1570983 3537161 := bstep (se 2 (by rfl) ⟨1326435, by rfl⟩ : syracuseStep 3537161 = 2652871) B2652871
theorem B5306633 : Blo 1570983 5306633 := bstep (se 2 (by rfl) ⟨1989987, by rfl⟩ : syracuseStep 5306633 = 3979975) B3979975
theorem B1571103 : Blo 1570983 1571103 := bstep (se 1 (by rfl) ⟨1178327, by rfl⟩ : syracuseStep 1571103 = 2356655) B2356655
theorem B1571163 : Blo 1570983 1571163 := bstep (se 1 (by rfl) ⟨1178372, by rfl⟩ : syracuseStep 1571163 = 2356745) B2356745
theorem B1571183 : Blo 1570983 1571183 := bstep (se 1 (by rfl) ⟨1178387, by rfl⟩ : syracuseStep 1571183 = 2356775) B2356775
theorem B1988975 : Blo 1570983 1988975 := bstep (se 1 (by rfl) ⟨1491731, by rfl⟩ : syracuseStep 1988975 = 2983463) B2983463
theorem B2357615 : Blo 1570983 2357615 := bstep (se 1 (by rfl) ⟨1768211, by rfl⟩ : syracuseStep 2357615 = 3536423) B3536423
theorem B2652527 : Blo 1570983 2652527 := bstep (se 1 (by rfl) ⟨1989395, by rfl⟩ : syracuseStep 2652527 = 3978791) B3978791
theorem B1571239 : Blo 1570983 1571239 := bstep (se 1 (by rfl) ⟨1178429, by rfl⟩ : syracuseStep 1571239 = 2356859) B2356859
theorem B1767847 : Blo 1570983 1767847 := bstep (se 1 (by rfl) ⟨1325885, by rfl⟩ : syracuseStep 1767847 = 2651771) B2651771
theorem B1989031 : Blo 1570983 1989031 := bstep (se 1 (by rfl) ⟨1491773, by rfl⟩ : syracuseStep 1989031 = 2983547) B2983547
theorem B3537377 : Blo 1570983 3537377 := bstep (se 2 (by rfl) ⟨1326516, by rfl⟩ : syracuseStep 3537377 = 2653033) B2653033
theorem B1571323 : Blo 1570983 1571323 := bstep (se 1 (by rfl) ⟨1178492, by rfl⟩ : syracuseStep 1571323 = 2356985) B2356985
theorem B1571391 : Blo 1570983 1571391 := bstep (se 1 (by rfl) ⟨1178543, by rfl⟩ : syracuseStep 1571391 = 2357087) B2357087
theorem B1571399 : Blo 1570983 1571399 := bstep (se 1 (by rfl) ⟨1178549, by rfl⟩ : syracuseStep 1571399 = 2357099) B2357099
theorem B2357831 : Blo 1570983 2357831 := bstep (se 1 (by rfl) ⟨1768373, by rfl⟩ : syracuseStep 2357831 = 3536747) B3536747
theorem B2652743 : Blo 1570983 2652743 := bstep (se 1 (by rfl) ⟨1989557, by rfl⟩ : syracuseStep 2652743 = 3979115) B3979115
theorem B2357867 : Blo 1570983 2357867 := bstep (se 1 (by rfl) ⟨1768400, by rfl⟩ : syracuseStep 2357867 = 3536801) B3536801
theorem B1571551 : Blo 1570983 1571551 := bstep (se 1 (by rfl) ⟨1178663, by rfl⟩ : syracuseStep 1571551 = 2357327) B2357327
theorem B1989355 : Blo 1570983 1989355 := bstep (se 1 (by rfl) ⟨1492016, by rfl⟩ : syracuseStep 1989355 = 2984033) B2984033
theorem B3537683 : Blo 1570983 3537683 := bstep (se 1 (by rfl) ⟨2653262, by rfl⟩ : syracuseStep 3537683 = 5306525) B5306525
theorem B1571631 : Blo 1570983 1571631 := bstep (se 1 (by rfl) ⟨1178723, by rfl⟩ : syracuseStep 1571631 = 2357447) B2357447
theorem B2358095 : Blo 1570983 2358095 := bstep (se 1 (by rfl) ⟨1768571, by rfl⟩ : syracuseStep 2358095 = 3537143) B3537143
theorem B1571739 : Blo 1570983 1571739 := bstep (se 1 (by rfl) ⟨1178804, by rfl⟩ : syracuseStep 1571739 = 2357609) B2357609
theorem B5102507 : Blo 1570983 5102507 := bstep (se 1 (by rfl) ⟨3826880, by rfl⟩ : syracuseStep 5102507 = 7653761) B7653761
theorem B14334895 : Blo 1570983 14334895 := bstep (se 1 (by rfl) ⟨10751171, by rfl⟩ : syracuseStep 14334895 = 21502343) B21502343
theorem B1571791 : Blo 1570983 1571791 := bstep (se 1 (by rfl) ⟨1178843, by rfl⟩ : syracuseStep 1571791 = 2357687) B2357687
theorem B1571815 : Blo 1570983 1571815 := bstep (se 1 (by rfl) ⟨1178861, by rfl⟩ : syracuseStep 1571815 = 2357723) B2357723
theorem B1768423 : Blo 1570983 1768423 := bstep (se 1 (by rfl) ⟨1326317, by rfl⟩ : syracuseStep 1768423 = 2652635) B2652635
theorem B2653175 : Blo 1570983 2653175 := bstep (se 1 (by rfl) ⟨1989881, by rfl⟩ : syracuseStep 2653175 = 3979763) B3979763
theorem B3538043 : Blo 1570983 3538043 := bstep (se 1 (by rfl) ⟨2653532, by rfl⟩ : syracuseStep 3538043 = 5307065) B5307065
theorem B2358491 : Blo 1570983 2358491 := bstep (se 1 (by rfl) ⟨1768868, by rfl⟩ : syracuseStep 2358491 = 3537737) B3537737
theorem B1572127 : Blo 1570983 1572127 := bstep (se 1 (by rfl) ⟨1179095, by rfl⟩ : syracuseStep 1572127 = 2358191) B2358191
theorem B1572187 : Blo 1570983 1572187 := bstep (se 1 (by rfl) ⟨1179140, by rfl⟩ : syracuseStep 1572187 = 2358281) B2358281
theorem B1572207 : Blo 1570983 1572207 := bstep (se 1 (by rfl) ⟨1179155, by rfl⟩ : syracuseStep 1572207 = 2358311) B2358311
theorem B2358665 : Blo 1570983 2358665 := bstep (se 2 (by rfl) ⟨884499, by rfl⟩ : syracuseStep 2358665 = 1768999) B1768999
theorem B1572263 : Blo 1570983 1572263 := bstep (se 1 (by rfl) ⟨1179197, by rfl⟩ : syracuseStep 1572263 = 2358395) B2358395
theorem B1572347 : Blo 1570983 1572347 := bstep (se 1 (by rfl) ⟨1179260, by rfl⟩ : syracuseStep 1572347 = 2358521) B2358521
theorem B13426235 : Blo 1570983 13426235 := bstep (se 1 (by rfl) ⟨10069676, by rfl⟩ : syracuseStep 13426235 = 20139353) B20139353
theorem B1572415 : Blo 1570983 1572415 := bstep (se 1 (by rfl) ⟨1179311, by rfl⟩ : syracuseStep 1572415 = 2358623) B2358623
theorem B1572423 : Blo 1570983 1572423 := bstep (se 1 (by rfl) ⟨1179317, by rfl⟩ : syracuseStep 1572423 = 2358635) B2358635
theorem B11329105 : Blo 1570983 11329105 := bstep (se 2 (by rfl) ⟨4248414, by rfl⟩ : syracuseStep 11329105 = 8496829) B8496829
theorem B10206881 : Blo 1570983 10206881 := bstep (se 2 (by rfl) ⟨3827580, by rfl⟩ : syracuseStep 10206881 = 7655161) B7655161
theorem B36298529 : Blo 1570983 36298529 := bstep (se 2 (by rfl) ⟨13611948, by rfl⟩ : syracuseStep 36298529 = 27223897) B27223897
theorem B10067753 : Blo 1570983 10067753 := bstep (se 2 (by rfl) ⟨3775407, by rfl⟩ : syracuseStep 10067753 = 7550815) B7550815
theorem B3776311 : Blo 1570983 3776311 := bstep (se 1 (by rfl) ⟨2832233, by rfl⟩ : syracuseStep 3776311 = 5664467) B5664467
theorem B22667435 : Blo 1570983 22667435 := bstep (se 1 (by rfl) ⟨17000576, by rfl⟩ : syracuseStep 22667435 = 34001153) B34001153
theorem B3187667 : Blo 1570983 3187667 := bstep (se 1 (by rfl) ⟨2390750, by rfl⟩ : syracuseStep 3187667 = 4781501) B4781501
theorem B19113193 : Blo 1570983 19113193 := bstep (se 2 (by rfl) ⟨7167447, by rfl⟩ : syracuseStep 19113193 = 14334895) B14334895
theorem B7955819 : Blo 1570983 7955819 := bstep (se 1 (by rfl) ⟨5966864, by rfl⟩ : syracuseStep 7955819 = 11933729) B11933729
theorem B2016667 : Blo 1570983 2016667 := bstep (se 1 (by rfl) ⟨1512500, by rfl⟩ : syracuseStep 2016667 = 3025001) B3025001
theorem B5965271 : Blo 1570983 5965271 := bstep (se 1 (by rfl) ⟨4473953, by rfl⟩ : syracuseStep 5965271 = 8947907) B8947907
theorem B4032287 : Blo 1570983 4032287 := bstep (se 1 (by rfl) ⟨3024215, by rfl⟩ : syracuseStep 4032287 = 6048431) B6048431
theorem B21268331 : Blo 1570983 21268331 := bstep (se 1 (by rfl) ⟨15951248, by rfl⟩ : syracuseStep 21268331 = 31902497) B31902497
theorem B8947655 : Blo 1570983 8947655 := bstep (se 1 (by rfl) ⟨6710741, by rfl⟩ : syracuseStep 8947655 = 13421483) B13421483
theorem B3401671 : Blo 1570983 3401671 := bstep (se 1 (by rfl) ⟨2551253, by rfl⟩ : syracuseStep 3401671 = 5102507) B5102507
theorem B93096227 : Blo 1570983 93096227 := bstep (se 1 (by rfl) ⟨69822170, by rfl⟩ : syracuseStep 93096227 = 139644341) B139644341
theorem B6711835 : Blo 1570983 6711835 := bstep (se 1 (by rfl) ⟨5033876, by rfl⟩ : syracuseStep 6711835 = 10067753) B10067753
theorem B10750495 : Blo 1570983 10750495 := bstep (se 1 (by rfl) ⟨8062871, by rfl⟩ : syracuseStep 10750495 = 16125743) B16125743
theorem B5303393 : Blo 1570983 5303393 := bstep (se 2 (by rfl) ⟨1988772, by rfl⟩ : syracuseStep 5303393 = 3977545) B3977545
theorem B7957601 : Blo 1570983 7957601 := bstep (se 2 (by rfl) ⟨2984100, by rfl⟩ : syracuseStep 7957601 = 5968201) B5968201
theorem B10488997 : Blo 1570983 10488997 := bstep (se 4 (by rfl) ⟨983343, by rfl⟩ : syracuseStep 10488997 = 1966687) B1966687
theorem B11930813 : Blo 1570983 11930813 := bstep (se 3 (by rfl) ⟨2237027, by rfl⟩ : syracuseStep 11930813 = 4474055) B4474055
theorem B5967047 : Blo 1570983 5967047 := bstep (se 1 (by rfl) ⟨4475285, by rfl⟩ : syracuseStep 5967047 = 8950571) B8950571
theorem B4246967 : Blo 1570983 4246967 := bstep (se 1 (by rfl) ⟨3185225, by rfl⟩ : syracuseStep 4246967 = 6370451) B6370451
theorem B13430231 : Blo 1570983 13430231 := bstep (se 1 (by rfl) ⟨10072673, by rfl⟩ : syracuseStep 13430231 = 20145347) B20145347
theorem B5303933 : Blo 1570983 5303933 := bstep (se 3 (by rfl) ⟨994487, by rfl⟩ : syracuseStep 5303933 = 1988975) B1988975
theorem B20148011 : Blo 1570983 20148011 := bstep (se 1 (by rfl) ⟨15111008, by rfl⟩ : syracuseStep 20148011 = 30222017) B30222017
theorem B3534713 : Blo 1570983 3534713 := bstep (se 2 (by rfl) ⟨1325517, by rfl⟩ : syracuseStep 3534713 = 2651035) B2651035
theorem B5304203 : Blo 1570983 5304203 := bstep (se 1 (by rfl) ⟨3978152, by rfl⟩ : syracuseStep 5304203 = 7956305) B7956305
theorem B7958411 : Blo 1570983 7958411 := bstep (se 1 (by rfl) ⟨5968808, by rfl⟩ : syracuseStep 7958411 = 11937617) B11937617
theorem B20140325 : Blo 1570983 20140325 := bstep (se 4 (by rfl) ⟨1888155, by rfl⟩ : syracuseStep 20140325 = 3776311) B3776311
theorem B4780343 : Blo 1570983 4780343 := bstep (se 1 (by rfl) ⟨3585257, by rfl⟩ : syracuseStep 4780343 = 7170515) B7170515
theorem B8499599 : Blo 1570983 8499599 := bstep (se 1 (by rfl) ⟨6374699, by rfl⟩ : syracuseStep 8499599 = 12749399) B12749399
theorem B11645327 : Blo 1570983 11645327 := bstep (se 1 (by rfl) ⟨8733995, by rfl⟩ : syracuseStep 11645327 = 17467991) B17467991
theorem B5304743 : Blo 1570983 5304743 := bstep (se 1 (by rfl) ⟨3978557, by rfl⟩ : syracuseStep 5304743 = 7957115) B7957115
theorem B3977687 : Blo 1570983 3977687 := bstep (se 1 (by rfl) ⟨2983265, by rfl⟩ : syracuseStep 3977687 = 5966531) B5966531
theorem B7549433 : Blo 1570983 7549433 := bstep (se 2 (by rfl) ⟨2831037, by rfl⟩ : syracuseStep 7549433 = 5662075) B5662075
theorem B7549661 : Blo 1570983 7549661 := bstep (se 3 (by rfl) ⟨1415561, by rfl⟩ : syracuseStep 7549661 = 2831123) B2831123
theorem B10072957 : Blo 1570983 10072957 := bstep (se 3 (by rfl) ⟨1888679, by rfl⟩ : syracuseStep 10072957 = 3777359) B3777359
theorem B8950823 : Blo 1570983 8950823 := bstep (se 1 (by rfl) ⟨6713117, by rfl⟩ : syracuseStep 8950823 = 13426235) B13426235
theorem B6804587 : Blo 1570983 6804587 := bstep (se 1 (by rfl) ⟨5103440, by rfl⟩ : syracuseStep 6804587 = 10206881) B10206881
theorem B7959869 : Blo 1570983 7959869 := bstep (se 3 (by rfl) ⟨1492475, by rfl⟩ : syracuseStep 7959869 = 2984951) B2984951
theorem B2356571 : Blo 1570983 2356571 := bstep (se 1 (by rfl) ⟨1767428, by rfl⟩ : syracuseStep 2356571 = 3534857) B3534857
theorem B5379527 : Blo 1570983 5379527 := bstep (se 1 (by rfl) ⟨4034645, by rfl⟩ : syracuseStep 5379527 = 8069291) B8069291
theorem B2356847 : Blo 1570983 2356847 := bstep (se 1 (by rfl) ⟨1767635, by rfl⟩ : syracuseStep 2356847 = 3535271) B3535271
theorem B11327147 : Blo 1570983 11327147 := bstep (se 1 (by rfl) ⟨8495360, by rfl⟩ : syracuseStep 11327147 = 16990721) B16990721
theorem B2356919 : Blo 1570983 2356919 := bstep (se 1 (by rfl) ⟨1767689, by rfl⟩ : syracuseStep 2356919 = 3535379) B3535379
theorem B3536567 : Blo 1570983 3536567 := bstep (se 1 (by rfl) ⟨2652425, by rfl⟩ : syracuseStep 3536567 = 5304851) B5304851
theorem B5306039 : Blo 1570983 5306039 := bstep (se 1 (by rfl) ⟨3979529, by rfl⟩ : syracuseStep 5306039 = 7959059) B7959059
theorem B10073801 : Blo 1570983 10073801 := bstep (se 2 (by rfl) ⟨3777675, by rfl⟩ : syracuseStep 10073801 = 7555351) B7555351
theorem B2356955 : Blo 1570983 2356955 := bstep (se 1 (by rfl) ⟨1767716, by rfl⟩ : syracuseStep 2356955 = 3535433) B3535433
theorem B2651899 : Blo 1570983 2651899 := bstep (se 1 (by rfl) ⟨1988924, by rfl⟩ : syracuseStep 2651899 = 3977849) B3977849
theorem B3979003 : Blo 1570983 3979003 := bstep (se 1 (by rfl) ⟨2984252, by rfl⟩ : syracuseStep 3979003 = 5968505) B5968505
theorem B1988383 : Blo 1570983 1988383 := bstep (se 1 (by rfl) ⟨1491287, by rfl⟩ : syracuseStep 1988383 = 2982575) B2982575
theorem B2357129 : Blo 1570983 2357129 := bstep (se 2 (by rfl) ⟨883923, by rfl⟩ : syracuseStep 2357129 = 1767847) B1767847
theorem B2652041 : Blo 1570983 2652041 := bstep (se 2 (by rfl) ⟨994515, by rfl⟩ : syracuseStep 2652041 = 1989031) B1989031
theorem B3979145 : Blo 1570983 3979145 := bstep (se 2 (by rfl) ⟨1492179, by rfl⟩ : syracuseStep 3979145 = 2984359) B2984359
theorem B3356635 : Blo 1570983 3356635 := bstep (se 1 (by rfl) ⟨2517476, by rfl⟩ : syracuseStep 3356635 = 5034953) B5034953
theorem B2357231 : Blo 1570983 2357231 := bstep (se 1 (by rfl) ⟨1767923, by rfl⟩ : syracuseStep 2357231 = 3535847) B3535847
theorem B2832479 : Blo 1570983 2832479 := bstep (se 1 (by rfl) ⟨2124359, by rfl⟩ : syracuseStep 2832479 = 4248719) B4248719
theorem B9091177 : Blo 1570983 9091177 := bstep (se 2 (by rfl) ⟨3409191, by rfl⟩ : syracuseStep 9091177 = 6818383) B6818383
theorem B1571007 : Blo 1570983 1571007 := bstep (se 1 (by rfl) ⟨1178255, by rfl⟩ : syracuseStep 1571007 = 2356511) B2356511
theorem B2357483 : Blo 1570983 2357483 := bstep (se 1 (by rfl) ⟨1768112, by rfl⟩ : syracuseStep 2357483 = 3536225) B3536225
theorem B2357543 : Blo 1570983 2357543 := bstep (se 1 (by rfl) ⟨1768157, by rfl⟩ : syracuseStep 2357543 = 3536315) B3536315
theorem B1571119 : Blo 1570983 1571119 := bstep (se 1 (by rfl) ⟨1178339, by rfl⟩ : syracuseStep 1571119 = 2356679) B2356679
theorem B2652473 : Blo 1570983 2652473 := bstep (se 2 (by rfl) ⟨994677, by rfl⟩ : syracuseStep 2652473 = 1989355) B1989355
theorem B2357627 : Blo 1570983 2357627 := bstep (se 1 (by rfl) ⟨1768220, by rfl⟩ : syracuseStep 2357627 = 3536441) B3536441
theorem B1571355 : Blo 1570983 1571355 := bstep (se 1 (by rfl) ⟨1178516, by rfl⟩ : syracuseStep 1571355 = 2357033) B2357033
theorem B1571359 : Blo 1570983 1571359 := bstep (se 1 (by rfl) ⟨1178519, by rfl⟩ : syracuseStep 1571359 = 2357039) B2357039
theorem B2357897 : Blo 1570983 2357897 := bstep (se 2 (by rfl) ⟨884211, by rfl⟩ : syracuseStep 2357897 = 1768423) B1768423
theorem B10066679 : Blo 1570983 10066679 := bstep (se 1 (by rfl) ⟨7550009, by rfl⟩ : syracuseStep 10066679 = 15100019) B15100019
theorem B2358071 : Blo 1570983 2358071 := bstep (se 1 (by rfl) ⟨1768553, by rfl⟩ : syracuseStep 2358071 = 3537107) B3537107
theorem B1571675 : Blo 1570983 1571675 := bstep (se 1 (by rfl) ⟨1178756, by rfl⟩ : syracuseStep 1571675 = 2357513) B2357513
theorem B2358107 : Blo 1570983 2358107 := bstep (se 1 (by rfl) ⟨1768580, by rfl⟩ : syracuseStep 2358107 = 3537161) B3537161
theorem B3537755 : Blo 1570983 3537755 := bstep (se 1 (by rfl) ⟨2653316, by rfl⟩ : syracuseStep 3537755 = 5306633) B5306633
theorem B3980137 : Blo 1570983 3980137 := bstep (se 2 (by rfl) ⟨1492551, by rfl⟩ : syracuseStep 3980137 = 2985103) B2985103
theorem B1571743 : Blo 1570983 1571743 := bstep (se 1 (by rfl) ⟨1178807, by rfl⟩ : syracuseStep 1571743 = 2357615) B2357615
theorem B1768351 : Blo 1570983 1768351 := bstep (se 1 (by rfl) ⟨1326263, by rfl⟩ : syracuseStep 1768351 = 2652527) B2652527
theorem B2653087 : Blo 1570983 2653087 := bstep (se 1 (by rfl) ⟨1989815, by rfl⟩ : syracuseStep 2653087 = 3979631) B3979631
theorem B2358251 : Blo 1570983 2358251 := bstep (se 1 (by rfl) ⟨1768688, by rfl⟩ : syracuseStep 2358251 = 3537377) B3537377
theorem B7953389 : Blo 1570983 7953389 := bstep (se 3 (by rfl) ⟨1491260, by rfl⟩ : syracuseStep 7953389 = 2982521) B2982521
theorem B1571887 : Blo 1570983 1571887 := bstep (se 1 (by rfl) ⟨1178915, by rfl⟩ : syracuseStep 1571887 = 2357831) B2357831
theorem B1768495 : Blo 1570983 1768495 := bstep (se 1 (by rfl) ⟨1326371, by rfl⟩ : syracuseStep 1768495 = 2652743) B2652743
theorem B1989679 : Blo 1570983 1989679 := bstep (se 1 (by rfl) ⟨1492259, by rfl⟩ : syracuseStep 1989679 = 2984519) B2984519
theorem B1571911 : Blo 1570983 1571911 := bstep (se 1 (by rfl) ⟨1178933, by rfl⟩ : syracuseStep 1571911 = 2357867) B2357867
theorem B2358455 : Blo 1570983 2358455 := bstep (se 1 (by rfl) ⟨1768841, by rfl⟩ : syracuseStep 2358455 = 3537683) B3537683
theorem B26860733 : Blo 1570983 26860733 := bstep (se 3 (by rfl) ⟨5036387, by rfl⟩ : syracuseStep 26860733 = 10072775) B10072775
theorem B1572063 : Blo 1570983 1572063 := bstep (se 1 (by rfl) ⟨1179047, by rfl⟩ : syracuseStep 1572063 = 2358095) B2358095
theorem B3775753 : Blo 1570983 3775753 := bstep (se 2 (by rfl) ⟨1415907, by rfl⟩ : syracuseStep 3775753 = 2831815) B2831815
theorem B10755389 : Blo 1570983 10755389 := bstep (se 3 (by rfl) ⟨2016635, by rfl⟩ : syracuseStep 10755389 = 4033271) B4033271
theorem B1768783 : Blo 1570983 1768783 := bstep (se 1 (by rfl) ⟨1326587, by rfl⟩ : syracuseStep 1768783 = 2653175) B2653175
theorem B2653519 : Blo 1570983 2653519 := bstep (se 1 (by rfl) ⟨1990139, by rfl⟩ : syracuseStep 2653519 = 3980279) B3980279
theorem B2358695 : Blo 1570983 2358695 := bstep (se 1 (by rfl) ⟨1769021, by rfl⟩ : syracuseStep 2358695 = 3538043) B3538043
theorem B15105473 : Blo 1570983 15105473 := bstep (se 2 (by rfl) ⟨5664552, by rfl⟩ : syracuseStep 15105473 = 11329105) B11329105
theorem B1572327 : Blo 1570983 1572327 := bstep (se 1 (by rfl) ⟨1179245, by rfl⟩ : syracuseStep 1572327 = 2358491) B2358491
theorem B1572443 : Blo 1570983 1572443 := bstep (se 1 (by rfl) ⟨1179332, by rfl⟩ : syracuseStep 1572443 = 2358665) B2358665
theorem B7954199 : Blo 1570983 7954199 := bstep (se 1 (by rfl) ⟨5965649, by rfl⟩ : syracuseStep 7954199 = 11931299) B11931299
theorem B24199019 : Blo 1570983 24199019 := bstep (se 1 (by rfl) ⟨18149264, by rfl⟩ : syracuseStep 24199019 = 36298529) B36298529
theorem B13426883 : Blo 1570983 13426883 := bstep (se 1 (by rfl) ⟨10070162, by rfl⟩ : syracuseStep 13426883 = 20140325) B20140325
theorem B3186895 : Blo 1570983 3186895 := bstep (se 1 (by rfl) ⟨2390171, by rfl⟩ : syracuseStep 3186895 = 4780343) B4780343
theorem B28681037 : Blo 1570983 28681037 := bstep (se 3 (by rfl) ⟨5377694, by rfl⟩ : syracuseStep 28681037 = 10755389) B10755389
theorem B14345405 : Blo 1570983 14345405 := bstep (se 3 (by rfl) ⟨2689763, by rfl⟩ : syracuseStep 14345405 = 5379527) B5379527
theorem B2688191 : Blo 1570983 2688191 := bstep (se 1 (by rfl) ⟨2016143, by rfl⟩ : syracuseStep 2688191 = 4032287) B4032287
theorem B5965103 : Blo 1570983 5965103 := bstep (se 1 (by rfl) ⟨4473827, by rfl⟩ : syracuseStep 5965103 = 8947655) B8947655
theorem B20137349 : Blo 1570983 20137349 := bstep (se 4 (by rfl) ⟨1887876, by rfl⟩ : syracuseStep 20137349 = 3775753) B3775753
theorem B6711119 : Blo 1570983 6711119 := bstep (se 1 (by rfl) ⟨5033339, by rfl⟩ : syracuseStep 6711119 = 10066679) B10066679
theorem B2688889 : Blo 1570983 2688889 := bstep (se 2 (by rfl) ⟨1008333, by rfl⟩ : syracuseStep 2688889 = 2016667) B2016667
theorem B5302259 : Blo 1570983 5302259 := bstep (se 1 (by rfl) ⟨3976694, by rfl⟩ : syracuseStep 5302259 = 7953389) B7953389
theorem B10070315 : Blo 1570983 10070315 := bstep (se 1 (by rfl) ⟨7552736, by rfl⟩ : syracuseStep 10070315 = 15105473) B15105473
theorem B5302799 : Blo 1570983 5302799 := bstep (se 1 (by rfl) ⟨3977099, by rfl⟩ : syracuseStep 5302799 = 7954199) B7954199
theorem B16132679 : Blo 1570983 16132679 := bstep (se 1 (by rfl) ⟨12099509, by rfl⟩ : syracuseStep 16132679 = 24199019) B24199019
theorem B4475513 : Blo 1570983 4475513 := bstep (se 2 (by rfl) ⟨1678317, by rfl⟩ : syracuseStep 4475513 = 3356635) B3356635
theorem B5032955 : Blo 1570983 5032955 := bstep (se 1 (by rfl) ⟨3774716, by rfl⟩ : syracuseStep 5032955 = 7549433) B7549433
theorem B5033107 : Blo 1570983 5033107 := bstep (se 1 (by rfl) ⟨3774830, by rfl⟩ : syracuseStep 5033107 = 7549661) B7549661
theorem B2125111 : Blo 1570983 2125111 := bstep (se 1 (by rfl) ⟨1593833, by rfl⟩ : syracuseStep 2125111 = 3187667) B3187667
theorem B5967215 : Blo 1570983 5967215 := bstep (se 1 (by rfl) ⟨4475411, by rfl⟩ : syracuseStep 5967215 = 8950823) B8950823
theorem B8949113 : Blo 1570983 8949113 := bstep (se 2 (by rfl) ⟨3355917, by rfl⟩ : syracuseStep 8949113 = 6711835) B6711835
theorem B5303879 : Blo 1570983 5303879 := bstep (se 1 (by rfl) ⟨3977909, by rfl⟩ : syracuseStep 5303879 = 7955819) B7955819
theorem B3976847 : Blo 1570983 3976847 := bstep (se 1 (by rfl) ⟨2982635, by rfl⟩ : syracuseStep 3976847 = 5965271) B5965271
theorem B13430609 : Blo 1570983 13430609 := bstep (se 2 (by rfl) ⟨5036478, by rfl⟩ : syracuseStep 13430609 = 10072957) B10072957
theorem B1888319 : Blo 1570983 1888319 := bstep (se 1 (by rfl) ⟨1416239, by rfl⟩ : syracuseStep 1888319 = 2832479) B2832479
theorem B3535595 : Blo 1570983 3535595 := bstep (se 1 (by rfl) ⟨2651696, by rfl⟩ : syracuseStep 3535595 = 5303393) B5303393
theorem B5305067 : Blo 1570983 5305067 := bstep (se 1 (by rfl) ⟨3978800, by rfl⟩ : syracuseStep 5305067 = 7957601) B7957601
theorem B3978031 : Blo 1570983 3978031 := bstep (se 1 (by rfl) ⟨2983523, by rfl⟩ : syracuseStep 3978031 = 5967047) B5967047
theorem B2831311 : Blo 1570983 2831311 := bstep (se 1 (by rfl) ⟨2123483, by rfl⟩ : syracuseStep 2831311 = 4246967) B4246967
theorem B3535865 : Blo 1570983 3535865 := bstep (se 2 (by rfl) ⟨1325949, by rfl⟩ : syracuseStep 3535865 = 2651899) B2651899
theorem B5305337 : Blo 1570983 5305337 := bstep (se 2 (by rfl) ⟨1989501, by rfl⟩ : syracuseStep 5305337 = 3979003) B3979003
theorem B2651177 : Blo 1570983 2651177 := bstep (se 2 (by rfl) ⟨994191, by rfl⟩ : syracuseStep 2651177 = 1988383) B1988383
theorem B3535955 : Blo 1570983 3535955 := bstep (se 1 (by rfl) ⟨2651966, by rfl⟩ : syracuseStep 3535955 = 5303933) B5303933
theorem B13432007 : Blo 1570983 13432007 := bstep (se 1 (by rfl) ⟨10074005, by rfl⟩ : syracuseStep 13432007 = 20148011) B20148011
theorem B2356475 : Blo 1570983 2356475 := bstep (se 1 (by rfl) ⟨1767356, by rfl⟩ : syracuseStep 2356475 = 3534713) B3534713
theorem B3536135 : Blo 1570983 3536135 := bstep (se 1 (by rfl) ⟨2652101, by rfl⟩ : syracuseStep 3536135 = 5304203) B5304203
theorem B4535561 : Blo 1570983 4535561 := bstep (se 2 (by rfl) ⟨1700835, by rfl⟩ : syracuseStep 4535561 = 3401671) B3401671
theorem B5305607 : Blo 1570983 5305607 := bstep (se 1 (by rfl) ⟨3979205, by rfl⟩ : syracuseStep 5305607 = 7958411) B7958411
theorem B15111623 : Blo 1570983 15111623 := bstep (se 1 (by rfl) ⟨11333717, by rfl⟩ : syracuseStep 15111623 = 22667435) B22667435
theorem B5666399 : Blo 1570983 5666399 := bstep (se 1 (by rfl) ⟨4249799, by rfl⟩ : syracuseStep 5666399 = 8499599) B8499599
theorem B7763551 : Blo 1570983 7763551 := bstep (se 1 (by rfl) ⟨5822663, by rfl⟩ : syracuseStep 7763551 = 11645327) B11645327
theorem B3536495 : Blo 1570983 3536495 := bstep (se 1 (by rfl) ⟨2652371, by rfl⟩ : syracuseStep 3536495 = 5304743) B5304743
theorem B2651791 : Blo 1570983 2651791 := bstep (se 1 (by rfl) ⟨1988843, by rfl⟩ : syracuseStep 2651791 = 3977687) B3977687
theorem B48486277 : Blo 1570983 48486277 := bstep (se 4 (by rfl) ⟨4545588, by rfl⟩ : syracuseStep 48486277 = 9091177) B9091177
theorem B14333993 : Blo 1570983 14333993 := bstep (se 2 (by rfl) ⟨5375247, by rfl⟩ : syracuseStep 14333993 = 10750495) B10750495
theorem B4536391 : Blo 1570983 4536391 := bstep (se 1 (by rfl) ⟨3402293, by rfl⟩ : syracuseStep 4536391 = 6804587) B6804587
theorem B248256605 : Blo 1570983 248256605 := bstep (se 3 (by rfl) ⟨46548113, by rfl⟩ : syracuseStep 248256605 = 93096227) B93096227
theorem B55941317 : Blo 1570983 55941317 := bstep (se 4 (by rfl) ⟨5244498, by rfl⟩ : syracuseStep 55941317 = 10488997) B10488997
theorem B5306579 : Blo 1570983 5306579 := bstep (se 1 (by rfl) ⟨3979934, by rfl⟩ : syracuseStep 5306579 = 7959869) B7959869
theorem B1571047 : Blo 1570983 1571047 := bstep (se 1 (by rfl) ⟨1178285, by rfl⟩ : syracuseStep 1571047 = 2356571) B2356571
theorem B1571231 : Blo 1570983 1571231 := bstep (se 1 (by rfl) ⟨1178423, by rfl⟩ : syracuseStep 1571231 = 2356847) B2356847
theorem B7551431 : Blo 1570983 7551431 := bstep (se 1 (by rfl) ⟨5663573, by rfl⟩ : syracuseStep 7551431 = 11327147) B11327147
theorem B1571279 : Blo 1570983 1571279 := bstep (se 1 (by rfl) ⟨1178459, by rfl⟩ : syracuseStep 1571279 = 2356919) B2356919
theorem B2357711 : Blo 1570983 2357711 := bstep (se 1 (by rfl) ⟨1768283, by rfl⟩ : syracuseStep 2357711 = 3536567) B3536567
theorem B3537359 : Blo 1570983 3537359 := bstep (se 1 (by rfl) ⟨2653019, by rfl⟩ : syracuseStep 3537359 = 5306039) B5306039
theorem B6715867 : Blo 1570983 6715867 := bstep (se 1 (by rfl) ⟨5036900, by rfl⟩ : syracuseStep 6715867 = 10073801) B10073801
theorem B5306849 : Blo 1570983 5306849 := bstep (se 2 (by rfl) ⟨1990068, by rfl⟩ : syracuseStep 5306849 = 3980137) B3980137
theorem B1571303 : Blo 1570983 1571303 := bstep (se 1 (by rfl) ⟨1178477, by rfl⟩ : syracuseStep 1571303 = 2356955) B2356955
theorem B2357801 : Blo 1570983 2357801 := bstep (se 2 (by rfl) ⟨884175, by rfl⟩ : syracuseStep 2357801 = 1768351) B1768351
theorem B3537449 : Blo 1570983 3537449 := bstep (se 2 (by rfl) ⟨1326543, by rfl⟩ : syracuseStep 3537449 = 2653087) B2653087
theorem B14178887 : Blo 1570983 14178887 := bstep (se 1 (by rfl) ⟨10634165, by rfl⟩ : syracuseStep 14178887 = 21268331) B21268331
theorem B1571419 : Blo 1570983 1571419 := bstep (se 1 (by rfl) ⟨1178564, by rfl⟩ : syracuseStep 1571419 = 2357129) B2357129
theorem B1768027 : Blo 1570983 1768027 := bstep (se 1 (by rfl) ⟨1326020, by rfl⟩ : syracuseStep 1768027 = 2652041) B2652041
theorem B2652763 : Blo 1570983 2652763 := bstep (se 1 (by rfl) ⟨1989572, by rfl⟩ : syracuseStep 2652763 = 3979145) B3979145
theorem B1571487 : Blo 1570983 1571487 := bstep (se 1 (by rfl) ⟨1178615, by rfl⟩ : syracuseStep 1571487 = 2357231) B2357231
theorem B2357993 : Blo 1570983 2357993 := bstep (se 2 (by rfl) ⟨884247, by rfl⟩ : syracuseStep 2357993 = 1768495) B1768495
theorem B2652905 : Blo 1570983 2652905 := bstep (se 2 (by rfl) ⟨994839, by rfl⟩ : syracuseStep 2652905 = 1989679) B1989679
theorem B1571655 : Blo 1570983 1571655 := bstep (se 1 (by rfl) ⟨1178741, by rfl⟩ : syracuseStep 1571655 = 2357483) B2357483
theorem B1571695 : Blo 1570983 1571695 := bstep (se 1 (by rfl) ⟨1178771, by rfl⟩ : syracuseStep 1571695 = 2357543) B2357543
theorem B1768315 : Blo 1570983 1768315 := bstep (se 1 (by rfl) ⟨1326236, by rfl⟩ : syracuseStep 1768315 = 2652473) B2652473
theorem B1571751 : Blo 1570983 1571751 := bstep (se 1 (by rfl) ⟨1178813, by rfl⟩ : syracuseStep 1571751 = 2357627) B2357627
theorem B25484257 : Blo 1570983 25484257 := bstep (se 2 (by rfl) ⟨9556596, by rfl⟩ : syracuseStep 25484257 = 19113193) B19113193
theorem B1571931 : Blo 1570983 1571931 := bstep (se 1 (by rfl) ⟨1178948, by rfl⟩ : syracuseStep 1571931 = 2357897) B2357897
theorem B2358377 : Blo 1570983 2358377 := bstep (se 2 (by rfl) ⟨884391, by rfl⟩ : syracuseStep 2358377 = 1768783) B1768783
theorem B3538025 : Blo 1570983 3538025 := bstep (se 2 (by rfl) ⟨1326759, by rfl⟩ : syracuseStep 3538025 = 2653519) B2653519
theorem B1572047 : Blo 1570983 1572047 := bstep (se 1 (by rfl) ⟨1179035, by rfl⟩ : syracuseStep 1572047 = 2358071) B2358071
theorem B1572071 : Blo 1570983 1572071 := bstep (se 1 (by rfl) ⟨1179053, by rfl⟩ : syracuseStep 1572071 = 2358107) B2358107
theorem B2358503 : Blo 1570983 2358503 := bstep (se 1 (by rfl) ⟨1768877, by rfl⟩ : syracuseStep 2358503 = 3537755) B3537755
theorem B1572167 : Blo 1570983 1572167 := bstep (se 1 (by rfl) ⟨1179125, by rfl⟩ : syracuseStep 1572167 = 2358251) B2358251
theorem B1572303 : Blo 1570983 1572303 := bstep (se 1 (by rfl) ⟨1179227, by rfl⟩ : syracuseStep 1572303 = 2358455) B2358455
theorem B7953875 : Blo 1570983 7953875 := bstep (se 1 (by rfl) ⟨5965406, by rfl⟩ : syracuseStep 7953875 = 11930813) B11930813
theorem B17907155 : Blo 1570983 17907155 := bstep (se 1 (by rfl) ⟨13430366, by rfl⟩ : syracuseStep 17907155 = 26860733) B26860733
theorem B1572463 : Blo 1570983 1572463 := bstep (se 1 (by rfl) ⟨1179347, by rfl⟩ : syracuseStep 1572463 = 2358695) B2358695
theorem B8953487 : Blo 1570983 8953487 := bstep (se 1 (by rfl) ⟨6715115, by rfl⟩ : syracuseStep 8953487 = 13430231) B13430231
theorem B19120691 : Blo 1570983 19120691 := bstep (se 1 (by rfl) ⟨14340518, by rfl⟩ : syracuseStep 19120691 = 28681037) B28681037
theorem B8954489 : Blo 1570983 8954489 := bstep (se 2 (by rfl) ⟨3357933, by rfl⟩ : syracuseStep 8954489 = 6715867) B6715867
theorem B8954671 : Blo 1570983 8954671 := bstep (se 1 (by rfl) ⟨6716003, by rfl⟩ : syracuseStep 8954671 = 13432007) B13432007
theorem B3777599 : Blo 1570983 3777599 := bstep (se 1 (by rfl) ⟨2833199, by rfl⟩ : syracuseStep 3777599 = 5666399) B5666399
theorem B40297661 : Blo 1570983 40297661 := bstep (se 3 (by rfl) ⟨7555811, by rfl⟩ : syracuseStep 40297661 = 15111623) B15111623
theorem B4474079 : Blo 1570983 4474079 := bstep (se 1 (by rfl) ⟨3355559, by rfl⟩ : syracuseStep 4474079 = 6711119) B6711119
theorem B165504403 : Blo 1570983 165504403 := bstep (se 1 (by rfl) ⟨124128302, by rfl⟩ : syracuseStep 165504403 = 248256605) B248256605
theorem B5966075 : Blo 1570983 5966075 := bstep (se 1 (by rfl) ⟨4474556, by rfl⟩ : syracuseStep 5966075 = 8949113) B8949113
theorem B5302583 : Blo 1570983 5302583 := bstep (se 1 (by rfl) ⟨3976937, by rfl⟩ : syracuseStep 5302583 = 7953875) B7953875
theorem B11938103 : Blo 1570983 11938103 := bstep (se 1 (by rfl) ⟨8953577, by rfl⟩ : syracuseStep 11938103 = 17907155) B17907155
theorem B6048521 : Blo 1570983 6048521 := bstep (se 2 (by rfl) ⟨2268195, by rfl⟩ : syracuseStep 6048521 = 4536391) B4536391
theorem B12094829 : Blo 1570983 12094829 := bstep (se 3 (by rfl) ⟨2267780, by rfl⟩ : syracuseStep 12094829 = 4535561) B4535561
theorem B9563603 : Blo 1570983 9563603 := bstep (se 1 (by rfl) ⟨7172702, by rfl⟩ : syracuseStep 9563603 = 14345405) B14345405
theorem B3976735 : Blo 1570983 3976735 := bstep (se 1 (by rfl) ⟨2982551, by rfl⟩ : syracuseStep 3976735 = 5965103) B5965103
theorem B5304041 : Blo 1570983 5304041 := bstep (se 2 (by rfl) ⟨1989015, by rfl⟩ : syracuseStep 5304041 = 3978031) B3978031
theorem B3534839 : Blo 1570983 3534839 := bstep (se 1 (by rfl) ⟨2651129, by rfl⟩ : syracuseStep 3534839 = 5302259) B5302259
theorem B9555995 : Blo 1570983 9555995 := bstep (se 1 (by rfl) ⟨7166996, by rfl⟩ : syracuseStep 9555995 = 14333993) B14333993
theorem B37294211 : Blo 1570983 37294211 := bstep (se 1 (by rfl) ⟨27970658, by rfl⟩ : syracuseStep 37294211 = 55941317) B55941317
theorem B6713543 : Blo 1570983 6713543 := bstep (se 1 (by rfl) ⟨5035157, by rfl⟩ : syracuseStep 6713543 = 10070315) B10070315
theorem B5034287 : Blo 1570983 5034287 := bstep (se 1 (by rfl) ⟨3775715, by rfl⟩ : syracuseStep 5034287 = 7551431) B7551431
theorem B3535199 : Blo 1570983 3535199 := bstep (se 1 (by rfl) ⟨2651399, by rfl⟩ : syracuseStep 3535199 = 5302799) B5302799
theorem B165622421 : Blo 1570983 165622421 := bstep (se 6 (by rfl) ⟨3881775, by rfl⟩ : syracuseStep 165622421 = 7763551) B7763551
theorem B3355303 : Blo 1570983 3355303 := bstep (se 1 (by rfl) ⟨2516477, by rfl⟩ : syracuseStep 3355303 = 5032955) B5032955
theorem B258593477 : Blo 1570983 258593477 := bstep (se 4 (by rfl) ⟨24243138, by rfl⟩ : syracuseStep 258593477 = 48486277) B48486277
theorem B3535721 : Blo 1570983 3535721 := bstep (se 2 (by rfl) ⟨1325895, by rfl⟩ : syracuseStep 3535721 = 2651791) B2651791
theorem B3978143 : Blo 1570983 3978143 := bstep (se 1 (by rfl) ⟨2983607, by rfl⟩ : syracuseStep 3978143 = 5967215) B5967215
theorem B3535919 : Blo 1570983 3535919 := bstep (se 1 (by rfl) ⟨2651939, by rfl⟩ : syracuseStep 3535919 = 5303879) B5303879
theorem B2651231 : Blo 1570983 2651231 := bstep (se 1 (by rfl) ⟨1988423, by rfl⟩ : syracuseStep 2651231 = 3976847) B3976847
theorem B5968991 : Blo 1570983 5968991 := bstep (se 1 (by rfl) ⟨4476743, by rfl⟩ : syracuseStep 5968991 = 8953487) B8953487
theorem B3585185 : Blo 1570983 3585185 := bstep (se 2 (by rfl) ⟨1344444, by rfl⟩ : syracuseStep 3585185 = 2688889) B2688889
theorem B8951255 : Blo 1570983 8951255 := bstep (se 1 (by rfl) ⟨6713441, by rfl⟩ : syracuseStep 8951255 = 13426883) B13426883
theorem B5035517 : Blo 1570983 5035517 := bstep (se 3 (by rfl) ⟨944159, by rfl⟩ : syracuseStep 5035517 = 1888319) B1888319
theorem B4249193 : Blo 1570983 4249193 := bstep (se 2 (by rfl) ⟨1593447, by rfl⟩ : syracuseStep 4249193 = 3186895) B3186895
theorem B2357063 : Blo 1570983 2357063 := bstep (se 1 (by rfl) ⟨1767797, by rfl⟩ : syracuseStep 2357063 = 3535595) B3535595
theorem B3536711 : Blo 1570983 3536711 := bstep (se 1 (by rfl) ⟨2652533, by rfl⟩ : syracuseStep 3536711 = 5305067) B5305067
theorem B2357243 : Blo 1570983 2357243 := bstep (se 1 (by rfl) ⟨1767932, by rfl⟩ : syracuseStep 2357243 = 3535865) B3535865
theorem B3536891 : Blo 1570983 3536891 := bstep (se 1 (by rfl) ⟨2652668, by rfl⟩ : syracuseStep 3536891 = 5305337) B5305337
theorem B1767451 : Blo 1570983 1767451 := bstep (se 1 (by rfl) ⟨1325588, by rfl⟩ : syracuseStep 1767451 = 2651177) B2651177
theorem B2357303 : Blo 1570983 2357303 := bstep (se 1 (by rfl) ⟨1767977, by rfl⟩ : syracuseStep 2357303 = 3535955) B3535955
theorem B26843237 : Blo 1570983 26843237 := bstep (se 4 (by rfl) ⟨2516553, by rfl⟩ : syracuseStep 26843237 = 5033107) B5033107
theorem B2357369 : Blo 1570983 2357369 := bstep (se 2 (by rfl) ⟨884013, by rfl⟩ : syracuseStep 2357369 = 1768027) B1768027
theorem B3537017 : Blo 1570983 3537017 := bstep (se 2 (by rfl) ⟨1326381, by rfl⟩ : syracuseStep 3537017 = 2652763) B2652763
theorem B1792127 : Blo 1570983 1792127 := bstep (se 1 (by rfl) ⟨1344095, by rfl⟩ : syracuseStep 1792127 = 2688191) B2688191
theorem B1570983 : Blo 1570983 1570983 := bstep (se 1 (by rfl) ⟨1178237, by rfl⟩ : syracuseStep 1570983 = 2356475) B2356475
theorem B2357423 : Blo 1570983 2357423 := bstep (se 1 (by rfl) ⟨1768067, by rfl⟩ : syracuseStep 2357423 = 3536135) B3536135
theorem B3537071 : Blo 1570983 3537071 := bstep (se 1 (by rfl) ⟨2652803, by rfl⟩ : syracuseStep 3537071 = 5305607) B5305607
theorem B13424899 : Blo 1570983 13424899 := bstep (se 1 (by rfl) ⟨10068674, by rfl⟩ : syracuseStep 13424899 = 20137349) B20137349
theorem B2357663 : Blo 1570983 2357663 := bstep (se 1 (by rfl) ⟨1768247, by rfl⟩ : syracuseStep 2357663 = 3536495) B3536495
theorem B2357753 : Blo 1570983 2357753 := bstep (se 2 (by rfl) ⟨884157, by rfl⟩ : syracuseStep 2357753 = 1768315) B1768315
theorem B3775081 : Blo 1570983 3775081 := bstep (se 2 (by rfl) ⟨1415655, by rfl⟩ : syracuseStep 3775081 = 2831311) B2831311
theorem B33979009 : Blo 1570983 33979009 := bstep (se 2 (by rfl) ⟨12742128, by rfl⟩ : syracuseStep 33979009 = 25484257) B25484257
theorem B3537719 : Blo 1570983 3537719 := bstep (se 1 (by rfl) ⟨2653289, by rfl⟩ : syracuseStep 3537719 = 5306579) B5306579
theorem B1571807 : Blo 1570983 1571807 := bstep (se 1 (by rfl) ⟨1178855, by rfl⟩ : syracuseStep 1571807 = 2357711) B2357711
theorem B2358239 : Blo 1570983 2358239 := bstep (se 1 (by rfl) ⟨1768679, by rfl⟩ : syracuseStep 2358239 = 3537359) B3537359
theorem B11934701 : Blo 1570983 11934701 := bstep (se 3 (by rfl) ⟨2237756, by rfl⟩ : syracuseStep 11934701 = 4475513) B4475513
theorem B3537899 : Blo 1570983 3537899 := bstep (se 1 (by rfl) ⟨2653424, by rfl⟩ : syracuseStep 3537899 = 5306849) B5306849
theorem B1571867 : Blo 1570983 1571867 := bstep (se 1 (by rfl) ⟨1178900, by rfl⟩ : syracuseStep 1571867 = 2357801) B2357801
theorem B2358299 : Blo 1570983 2358299 := bstep (se 1 (by rfl) ⟨1768724, by rfl⟩ : syracuseStep 2358299 = 3537449) B3537449
theorem B10755119 : Blo 1570983 10755119 := bstep (se 1 (by rfl) ⟨8066339, by rfl⟩ : syracuseStep 10755119 = 16132679) B16132679
theorem B9452591 : Blo 1570983 9452591 := bstep (se 1 (by rfl) ⟨7089443, by rfl⟩ : syracuseStep 9452591 = 14178887) B14178887
theorem B2833481 : Blo 1570983 2833481 := bstep (se 2 (by rfl) ⟨1062555, by rfl⟩ : syracuseStep 2833481 = 2125111) B2125111
theorem B1571995 : Blo 1570983 1571995 := bstep (se 1 (by rfl) ⟨1178996, by rfl⟩ : syracuseStep 1571995 = 2357993) B2357993
theorem B1768603 : Blo 1570983 1768603 := bstep (se 1 (by rfl) ⟨1326452, by rfl⟩ : syracuseStep 1768603 = 2652905) B2652905
theorem B1572251 : Blo 1570983 1572251 := bstep (se 1 (by rfl) ⟨1179188, by rfl⟩ : syracuseStep 1572251 = 2358377) B2358377
theorem B2358683 : Blo 1570983 2358683 := bstep (se 1 (by rfl) ⟨1769012, by rfl⟩ : syracuseStep 2358683 = 3538025) B3538025
theorem B1572335 : Blo 1570983 1572335 := bstep (se 1 (by rfl) ⟨1179251, by rfl⟩ : syracuseStep 1572335 = 2358503) B2358503
theorem B8953739 : Blo 1570983 8953739 := bstep (se 1 (by rfl) ⟨6715304, by rfl⟩ : syracuseStep 8953739 = 13430609) B13430609
theorem B24862807 : Blo 1570983 24862807 := bstep (se 1 (by rfl) ⟨18647105, by rfl⟩ : syracuseStep 24862807 = 37294211) B37294211
theorem B28680317 : Blo 1570983 28680317 := bstep (se 3 (by rfl) ⟨5377559, by rfl⟩ : syracuseStep 28680317 = 10755119) B10755119
theorem B17899865 : Blo 1570983 17899865 := bstep (se 2 (by rfl) ⟨6712449, by rfl⟩ : syracuseStep 17899865 = 13424899) B13424899
theorem B12747127 : Blo 1570983 12747127 := bstep (se 1 (by rfl) ⟨9560345, by rfl⟩ : syracuseStep 12747127 = 19120691) B19120691
theorem B2982719 : Blo 1570983 2982719 := bstep (se 1 (by rfl) ⟨2237039, by rfl⟩ : syracuseStep 2982719 = 4474079) B4474079
theorem B4473737 : Blo 1570983 4473737 := bstep (se 2 (by rfl) ⟨1677651, by rfl⟩ : syracuseStep 4473737 = 3355303) B3355303
theorem B25502941 : Blo 1570983 25502941 := bstep (se 3 (by rfl) ⟨4781801, by rfl⟩ : syracuseStep 25502941 = 9563603) B9563603
theorem B11331181 : Blo 1570983 11331181 := bstep (se 3 (by rfl) ⟨2124596, by rfl⟩ : syracuseStep 11331181 = 4249193) B4249193
theorem B4032347 : Blo 1570983 4032347 := bstep (se 1 (by rfl) ⟨3024260, by rfl⟩ : syracuseStep 4032347 = 6048521) B6048521
theorem B7956467 : Blo 1570983 7956467 := bstep (se 1 (by rfl) ⟨5967350, by rfl⟩ : syracuseStep 7956467 = 11934701) B11934701
theorem B6301727 : Blo 1570983 6301727 := bstep (se 1 (by rfl) ⟨4726295, by rfl⟩ : syracuseStep 6301727 = 9452591) B9452591
theorem B5302313 : Blo 1570983 5302313 := bstep (se 2 (by rfl) ⟨1988367, by rfl⟩ : syracuseStep 5302313 = 3976735) B3976735
theorem B882690149 : Blo 1570983 882690149 := bstep (se 4 (by rfl) ⟨82752201, by rfl⟩ : syracuseStep 882690149 = 165504403) B165504403
theorem B8063219 : Blo 1570983 8063219 := bstep (se 1 (by rfl) ⟨6047414, by rfl⟩ : syracuseStep 8063219 = 12094829) B12094829
theorem B7555949 : Blo 1570983 7555949 := bstep (se 3 (by rfl) ⟨1416740, by rfl⟩ : syracuseStep 7555949 = 2833481) B2833481
theorem B4779005 : Blo 1570983 4779005 := bstep (se 3 (by rfl) ⟨896063, by rfl⟩ : syracuseStep 4779005 = 1792127) B1792127
theorem B110414947 : Blo 1570983 110414947 := bstep (se 1 (by rfl) ⟨82811210, by rfl⟩ : syracuseStep 110414947 = 165622421) B165622421
theorem B17902781 : Blo 1570983 17902781 := bstep (se 3 (by rfl) ⟨3356771, by rfl⟩ : syracuseStep 17902781 = 6713543) B6713543
theorem B2518399 : Blo 1570983 2518399 := bstep (se 1 (by rfl) ⟨1888799, by rfl⟩ : syracuseStep 2518399 = 3777599) B3777599
theorem B26865107 : Blo 1570983 26865107 := bstep (se 1 (by rfl) ⟨20148830, by rfl⟩ : syracuseStep 26865107 = 40297661) B40297661
theorem B5033441 : Blo 1570983 5033441 := bstep (se 2 (by rfl) ⟨1887540, by rfl⟩ : syracuseStep 5033441 = 3775081) B3775081
theorem B45305345 : Blo 1570983 45305345 := bstep (se 2 (by rfl) ⟨16989504, by rfl⟩ : syracuseStep 45305345 = 33979009) B33979009
theorem B5967503 : Blo 1570983 5967503 := bstep (se 1 (by rfl) ⟨4475627, by rfl⟩ : syracuseStep 5967503 = 8951255) B8951255
theorem B11939561 : Blo 1570983 11939561 := bstep (se 2 (by rfl) ⟨4477335, by rfl⟩ : syracuseStep 11939561 = 8954671) B8954671
theorem B17895491 : Blo 1570983 17895491 := bstep (se 1 (by rfl) ⟨13421618, by rfl⟩ : syracuseStep 17895491 = 26843237) B26843237
theorem B3977383 : Blo 1570983 3977383 := bstep (se 1 (by rfl) ⟨2983037, by rfl⟩ : syracuseStep 3977383 = 5966075) B5966075
theorem B3535055 : Blo 1570983 3535055 := bstep (se 1 (by rfl) ⟨2651291, by rfl⟩ : syracuseStep 3535055 = 5302583) B5302583
theorem B7958735 : Blo 1570983 7958735 := bstep (se 1 (by rfl) ⟨5969051, by rfl⟩ : syracuseStep 7958735 = 11938103) B11938103
theorem B689582605 : Blo 1570983 689582605 := bstep (se 3 (by rfl) ⟨129296738, by rfl⟩ : syracuseStep 689582605 = 258593477) B258593477
theorem B3536027 : Blo 1570983 3536027 := bstep (se 1 (by rfl) ⟨2652020, by rfl⟩ : syracuseStep 3536027 = 5304041) B5304041
theorem B5969159 : Blo 1570983 5969159 := bstep (se 1 (by rfl) ⟨4476869, by rfl⟩ : syracuseStep 5969159 = 8953739) B8953739
theorem B2356559 : Blo 1570983 2356559 := bstep (se 1 (by rfl) ⟨1767419, by rfl⟩ : syracuseStep 2356559 = 3534839) B3534839
theorem B6370663 : Blo 1570983 6370663 := bstep (se 1 (by rfl) ⟨4777997, by rfl⟩ : syracuseStep 6370663 = 9555995) B9555995
theorem B2356601 : Blo 1570983 2356601 := bstep (se 2 (by rfl) ⟨883725, by rfl⟩ : syracuseStep 2356601 = 1767451) B1767451
theorem B3356191 : Blo 1570983 3356191 := bstep (se 1 (by rfl) ⟨2517143, by rfl⟩ : syracuseStep 3356191 = 5034287) B5034287
theorem B2356799 : Blo 1570983 2356799 := bstep (se 1 (by rfl) ⟨1767599, by rfl⟩ : syracuseStep 2356799 = 3535199) B3535199
theorem B5969659 : Blo 1570983 5969659 := bstep (se 1 (by rfl) ⟨4477244, by rfl⟩ : syracuseStep 5969659 = 8954489) B8954489
theorem B2357147 : Blo 1570983 2357147 := bstep (se 1 (by rfl) ⟨1767860, by rfl⟩ : syracuseStep 2357147 = 3535721) B3535721
theorem B2652095 : Blo 1570983 2652095 := bstep (se 1 (by rfl) ⟨1989071, by rfl⟩ : syracuseStep 2652095 = 3978143) B3978143
theorem B2357279 : Blo 1570983 2357279 := bstep (se 1 (by rfl) ⟨1767959, by rfl⟩ : syracuseStep 2357279 = 3535919) B3535919
theorem B1767487 : Blo 1570983 1767487 := bstep (se 1 (by rfl) ⟨1325615, by rfl⟩ : syracuseStep 1767487 = 2651231) B2651231
theorem B3979327 : Blo 1570983 3979327 := bstep (se 1 (by rfl) ⟨2984495, by rfl⟩ : syracuseStep 3979327 = 5968991) B5968991
theorem B2390123 : Blo 1570983 2390123 := bstep (se 1 (by rfl) ⟨1792592, by rfl⟩ : syracuseStep 2390123 = 3585185) B3585185
theorem B3357011 : Blo 1570983 3357011 := bstep (se 1 (by rfl) ⟨2517758, by rfl⟩ : syracuseStep 3357011 = 5035517) B5035517
theorem B1571375 : Blo 1570983 1571375 := bstep (se 1 (by rfl) ⟨1178531, by rfl⟩ : syracuseStep 1571375 = 2357063) B2357063
theorem B2357807 : Blo 1570983 2357807 := bstep (se 1 (by rfl) ⟨1768355, by rfl⟩ : syracuseStep 2357807 = 3536711) B3536711
theorem B1571495 : Blo 1570983 1571495 := bstep (se 1 (by rfl) ⟨1178621, by rfl⟩ : syracuseStep 1571495 = 2357243) B2357243
theorem B2357927 : Blo 1570983 2357927 := bstep (se 1 (by rfl) ⟨1768445, by rfl⟩ : syracuseStep 2357927 = 3536891) B3536891
theorem B1571535 : Blo 1570983 1571535 := bstep (se 1 (by rfl) ⟨1178651, by rfl⟩ : syracuseStep 1571535 = 2357303) B2357303
theorem B1571579 : Blo 1570983 1571579 := bstep (se 1 (by rfl) ⟨1178684, by rfl⟩ : syracuseStep 1571579 = 2357369) B2357369
theorem B2358011 : Blo 1570983 2358011 := bstep (se 1 (by rfl) ⟨1768508, by rfl⟩ : syracuseStep 2358011 = 3537017) B3537017
theorem B1571615 : Blo 1570983 1571615 := bstep (se 1 (by rfl) ⟨1178711, by rfl⟩ : syracuseStep 1571615 = 2357423) B2357423
theorem B2358047 : Blo 1570983 2358047 := bstep (se 1 (by rfl) ⟨1768535, by rfl⟩ : syracuseStep 2358047 = 3537071) B3537071
theorem B2358137 : Blo 1570983 2358137 := bstep (se 2 (by rfl) ⟨884301, by rfl⟩ : syracuseStep 2358137 = 1768603) B1768603
theorem B1571775 : Blo 1570983 1571775 := bstep (se 1 (by rfl) ⟨1178831, by rfl⟩ : syracuseStep 1571775 = 2357663) B2357663
theorem B1571835 : Blo 1570983 1571835 := bstep (se 1 (by rfl) ⟨1178876, by rfl⟩ : syracuseStep 1571835 = 2357753) B2357753
theorem B2358479 : Blo 1570983 2358479 := bstep (se 1 (by rfl) ⟨1768859, by rfl⟩ : syracuseStep 2358479 = 3537719) B3537719
theorem B1572159 : Blo 1570983 1572159 := bstep (se 1 (by rfl) ⟨1179119, by rfl⟩ : syracuseStep 1572159 = 2358239) B2358239
theorem B2358599 : Blo 1570983 2358599 := bstep (se 1 (by rfl) ⟨1768949, by rfl⟩ : syracuseStep 2358599 = 3537899) B3537899
theorem B1572199 : Blo 1570983 1572199 := bstep (se 1 (by rfl) ⟨1179149, by rfl⟩ : syracuseStep 1572199 = 2358299) B2358299
theorem B1572455 : Blo 1570983 1572455 := bstep (se 1 (by rfl) ⟨1179341, by rfl⟩ : syracuseStep 1572455 = 2358683) B2358683
theorem B19120211 : Blo 1570983 19120211 := bstep (se 1 (by rfl) ⟨14340158, by rfl⟩ : syracuseStep 19120211 = 28680317) B28680317
theorem B2982491 : Blo 1570983 2982491 := bstep (se 1 (by rfl) ⟨2236868, by rfl⟩ : syracuseStep 2982491 = 4473737) B4473737
theorem B147219929 : Blo 1570983 147219929 := bstep (se 2 (by rfl) ⟨55207473, by rfl⟩ : syracuseStep 147219929 = 110414947) B110414947
theorem B5375479 : Blo 1570983 5375479 := bstep (se 1 (by rfl) ⟨4031609, by rfl⟩ : syracuseStep 5375479 = 8063219) B8063219
theorem B4474921 : Blo 1570983 4474921 := bstep (se 2 (by rfl) ⟨1678095, by rfl⟩ : syracuseStep 4474921 = 3356191) B3356191
theorem B15108241 : Blo 1570983 15108241 := bstep (se 2 (by rfl) ⟨5665590, by rfl⟩ : syracuseStep 15108241 = 11331181) B11331181
theorem B17910071 : Blo 1570983 17910071 := bstep (se 1 (by rfl) ⟨13432553, by rfl⟩ : syracuseStep 17910071 = 26865107) B26865107
theorem B11930327 : Blo 1570983 11930327 := bstep (se 1 (by rfl) ⟨8947745, by rfl⟩ : syracuseStep 11930327 = 17895491) B17895491
theorem B5303177 : Blo 1570983 5303177 := bstep (se 2 (by rfl) ⟨1988691, by rfl⟩ : syracuseStep 5303177 = 3977383) B3977383
theorem B13422509 : Blo 1570983 13422509 := bstep (se 3 (by rfl) ⟨2516720, by rfl⟩ : syracuseStep 13422509 = 5033441) B5033441
theorem B5304311 : Blo 1570983 5304311 := bstep (se 1 (by rfl) ⟨3978233, by rfl⟩ : syracuseStep 5304311 = 7956467) B7956467
theorem B3534875 : Blo 1570983 3534875 := bstep (se 1 (by rfl) ⟨2651156, by rfl⟩ : syracuseStep 3534875 = 5302313) B5302313
theorem B588460099 : Blo 1570983 588460099 := bstep (se 1 (by rfl) ⟨441345074, by rfl⟩ : syracuseStep 588460099 = 882690149) B882690149
theorem B1593415 : Blo 1570983 1593415 := bstep (se 1 (by rfl) ⟨1195061, by rfl⟩ : syracuseStep 1593415 = 2390123) B2390123
theorem B10752925 : Blo 1570983 10752925 := bstep (se 3 (by rfl) ⟨2016173, by rfl⟩ : syracuseStep 10752925 = 4032347) B4032347
theorem B7959545 : Blo 1570983 7959545 := bstep (se 2 (by rfl) ⟨2984829, by rfl⟩ : syracuseStep 7959545 = 5969659) B5969659
theorem B3978335 : Blo 1570983 3978335 := bstep (se 1 (by rfl) ⟨2983751, by rfl⟩ : syracuseStep 3978335 = 5967503) B5967503
theorem B7959707 : Blo 1570983 7959707 := bstep (se 1 (by rfl) ⟨5969780, by rfl⟩ : syracuseStep 7959707 = 11939561) B11939561
theorem B50976053 : Blo 1570983 50976053 := bstep (se 5 (by rfl) ⟨2389502, by rfl⟩ : syracuseStep 50976053 = 4779005) B4779005
theorem B2356649 : Blo 1570983 2356649 := bstep (se 2 (by rfl) ⟨883743, by rfl⟩ : syracuseStep 2356649 = 1767487) B1767487
theorem B5305769 : Blo 1570983 5305769 := bstep (se 2 (by rfl) ⟨1989663, by rfl⟩ : syracuseStep 5305769 = 3979327) B3979327
theorem B2356703 : Blo 1570983 2356703 := bstep (se 1 (by rfl) ⟨1767527, by rfl⟩ : syracuseStep 2356703 = 3535055) B3535055
theorem B5305823 : Blo 1570983 5305823 := bstep (se 1 (by rfl) ⟨3979367, by rfl⟩ : syracuseStep 5305823 = 7958735) B7958735
theorem B11933243 : Blo 1570983 11933243 := bstep (se 1 (by rfl) ⟨8949932, by rfl⟩ : syracuseStep 11933243 = 17899865) B17899865
theorem B132601637 : Blo 1570983 132601637 := bstep (se 4 (by rfl) ⟨12431403, by rfl⟩ : syracuseStep 132601637 = 24862807) B24862807
theorem B16996169 : Blo 1570983 16996169 := bstep (se 2 (by rfl) ⟨6373563, by rfl⟩ : syracuseStep 16996169 = 12747127) B12747127
theorem B1988479 : Blo 1570983 1988479 := bstep (se 1 (by rfl) ⟨1491359, by rfl⟩ : syracuseStep 1988479 = 2982719) B2982719
theorem B919443473 : Blo 1570983 919443473 := bstep (se 2 (by rfl) ⟨344791302, by rfl⟩ : syracuseStep 919443473 = 689582605) B689582605
theorem B2357351 : Blo 1570983 2357351 := bstep (se 1 (by rfl) ⟨1768013, by rfl⟩ : syracuseStep 2357351 = 3536027) B3536027
theorem B3979439 : Blo 1570983 3979439 := bstep (se 1 (by rfl) ⟨2984579, by rfl⟩ : syracuseStep 3979439 = 5969159) B5969159
theorem B8952029 : Blo 1570983 8952029 := bstep (se 3 (by rfl) ⟨1678505, by rfl⟩ : syracuseStep 8952029 = 3357011) B3357011
theorem B1571039 : Blo 1570983 1571039 := bstep (se 1 (by rfl) ⟨1178279, by rfl⟩ : syracuseStep 1571039 = 2356559) B2356559
theorem B1571067 : Blo 1570983 1571067 := bstep (se 1 (by rfl) ⟨1178300, by rfl⟩ : syracuseStep 1571067 = 2356601) B2356601
theorem B1571199 : Blo 1570983 1571199 := bstep (se 1 (by rfl) ⟨1178399, by rfl⟩ : syracuseStep 1571199 = 2356799) B2356799
theorem B1571431 : Blo 1570983 1571431 := bstep (se 1 (by rfl) ⟨1178573, by rfl⟩ : syracuseStep 1571431 = 2357147) B2357147
theorem B1768063 : Blo 1570983 1768063 := bstep (se 1 (by rfl) ⟨1326047, by rfl⟩ : syracuseStep 1768063 = 2652095) B2652095
theorem B1571519 : Blo 1570983 1571519 := bstep (se 1 (by rfl) ⟨1178639, by rfl⟩ : syracuseStep 1571519 = 2357279) B2357279
theorem B4201151 : Blo 1570983 4201151 := bstep (se 1 (by rfl) ⟨3150863, by rfl⟩ : syracuseStep 4201151 = 6301727) B6301727
theorem B34003921 : Blo 1570983 34003921 := bstep (se 2 (by rfl) ⟨12751470, by rfl⟩ : syracuseStep 34003921 = 25502941) B25502941
theorem B1571871 : Blo 1570983 1571871 := bstep (se 1 (by rfl) ⟨1178903, by rfl⟩ : syracuseStep 1571871 = 2357807) B2357807
theorem B1571951 : Blo 1570983 1571951 := bstep (se 1 (by rfl) ⟨1178963, by rfl⟩ : syracuseStep 1571951 = 2357927) B2357927
theorem B8494217 : Blo 1570983 8494217 := bstep (se 2 (by rfl) ⟨3185331, by rfl⟩ : syracuseStep 8494217 = 6370663) B6370663
theorem B1572007 : Blo 1570983 1572007 := bstep (se 1 (by rfl) ⟨1179005, by rfl⟩ : syracuseStep 1572007 = 2358011) B2358011
theorem B3357865 : Blo 1570983 3357865 := bstep (se 2 (by rfl) ⟨1259199, by rfl⟩ : syracuseStep 3357865 = 2518399) B2518399
theorem B1572031 : Blo 1570983 1572031 := bstep (se 1 (by rfl) ⟨1179023, by rfl⟩ : syracuseStep 1572031 = 2358047) B2358047
theorem B5037299 : Blo 1570983 5037299 := bstep (se 1 (by rfl) ⟨3777974, by rfl⟩ : syracuseStep 5037299 = 7555949) B7555949
theorem B1572091 : Blo 1570983 1572091 := bstep (se 1 (by rfl) ⟨1179068, by rfl⟩ : syracuseStep 1572091 = 2358137) B2358137
theorem B11935187 : Blo 1570983 11935187 := bstep (se 1 (by rfl) ⟨8951390, by rfl⟩ : syracuseStep 11935187 = 17902781) B17902781
theorem B1572319 : Blo 1570983 1572319 := bstep (se 1 (by rfl) ⟨1179239, by rfl⟩ : syracuseStep 1572319 = 2358479) B2358479
theorem B1572399 : Blo 1570983 1572399 := bstep (se 1 (by rfl) ⟨1179299, by rfl⟩ : syracuseStep 1572399 = 2358599) B2358599
theorem B30203563 : Blo 1570983 30203563 := bstep (se 1 (by rfl) ⟨22652672, by rfl⟩ : syracuseStep 30203563 = 45305345) B45305345
theorem B12746807 : Blo 1570983 12746807 := bstep (se 1 (by rfl) ⟨9560105, by rfl⟩ : syracuseStep 12746807 = 19120211) B19120211
theorem B784613465 : Blo 1570983 784613465 := bstep (se 2 (by rfl) ⟨294230049, by rfl⟩ : syracuseStep 784613465 = 588460099) B588460099
theorem B20144321 : Blo 1570983 20144321 := bstep (se 2 (by rfl) ⟨7554120, by rfl⟩ : syracuseStep 20144321 = 15108241) B15108241
theorem B17908613 : Blo 1570983 17908613 := bstep (se 4 (by rfl) ⟨1678932, by rfl⟩ : syracuseStep 17908613 = 3357865) B3357865
theorem B7955495 : Blo 1570983 7955495 := bstep (se 1 (by rfl) ⟨5966621, by rfl⟩ : syracuseStep 7955495 = 11933243) B11933243
theorem B14337233 : Blo 1570983 14337233 := bstep (se 2 (by rfl) ⟨5376462, by rfl⟩ : syracuseStep 14337233 = 10752925) B10752925
theorem B11330779 : Blo 1570983 11330779 := bstep (se 1 (by rfl) ⟨8498084, by rfl⟩ : syracuseStep 11330779 = 16996169) B16996169
theorem B5662811 : Blo 1570983 5662811 := bstep (se 1 (by rfl) ⟨4247108, by rfl⟩ : syracuseStep 5662811 = 8494217) B8494217
theorem B7956791 : Blo 1570983 7956791 := bstep (se 1 (by rfl) ⟨5967593, by rfl⟩ : syracuseStep 7956791 = 11935187) B11935187
theorem B8948339 : Blo 1570983 8948339 := bstep (se 1 (by rfl) ⟨6711254, by rfl⟩ : syracuseStep 8948339 = 13422509) B13422509
theorem B5966561 : Blo 1570983 5966561 := bstep (se 2 (by rfl) ⟨2237460, by rfl⟩ : syracuseStep 5966561 = 4474921) B4474921
theorem B8498213 : Blo 1570983 8498213 := bstep (se 4 (by rfl) ⟨796707, by rfl⟩ : syracuseStep 8498213 = 1593415) B1593415
theorem B33984035 : Blo 1570983 33984035 := bstep (se 1 (by rfl) ⟨25488026, by rfl⟩ : syracuseStep 33984035 = 50976053) B50976053
theorem B45338561 : Blo 1570983 45338561 := bstep (se 2 (by rfl) ⟨17001960, by rfl⟩ : syracuseStep 45338561 = 34003921) B34003921
theorem B612962315 : Blo 1570983 612962315 := bstep (se 1 (by rfl) ⟨459721736, by rfl⟩ : syracuseStep 612962315 = 919443473) B919443473
theorem B5968019 : Blo 1570983 5968019 := bstep (se 1 (by rfl) ⟨4476014, by rfl⟩ : syracuseStep 5968019 = 8952029) B8952029
theorem B11940047 : Blo 1570983 11940047 := bstep (se 1 (by rfl) ⟨8955035, by rfl⟩ : syracuseStep 11940047 = 17910071) B17910071
theorem B11203069 : Blo 1570983 11203069 := bstep (se 3 (by rfl) ⟨2100575, by rfl⟩ : syracuseStep 11203069 = 4201151) B4201151
theorem B3535451 : Blo 1570983 3535451 := bstep (se 1 (by rfl) ⟨2651588, by rfl⟩ : syracuseStep 3535451 = 5303177) B5303177
theorem B353604365 : Blo 1570983 353604365 := bstep (se 3 (by rfl) ⟨66300818, by rfl⟩ : syracuseStep 353604365 = 132601637) B132601637
theorem B2651305 : Blo 1570983 2651305 := bstep (se 2 (by rfl) ⟨994239, by rfl⟩ : syracuseStep 2651305 = 1988479) B1988479
theorem B3536207 : Blo 1570983 3536207 := bstep (se 1 (by rfl) ⟨2652155, by rfl⟩ : syracuseStep 3536207 = 5304311) B5304311
theorem B2356583 : Blo 1570983 2356583 := bstep (se 1 (by rfl) ⟨1767437, by rfl⟩ : syracuseStep 2356583 = 3534875) B3534875
theorem B1988327 : Blo 1570983 1988327 := bstep (se 1 (by rfl) ⟨1491245, by rfl⟩ : syracuseStep 1988327 = 2982491) B2982491
theorem B5306363 : Blo 1570983 5306363 := bstep (se 1 (by rfl) ⟨3979772, by rfl⟩ : syracuseStep 5306363 = 7959545) B7959545
theorem B2652223 : Blo 1570983 2652223 := bstep (se 1 (by rfl) ⟨1989167, by rfl⟩ : syracuseStep 2652223 = 3978335) B3978335
theorem B5306471 : Blo 1570983 5306471 := bstep (se 1 (by rfl) ⟨3979853, by rfl⟩ : syracuseStep 5306471 = 7959707) B7959707
theorem B2357417 : Blo 1570983 2357417 := bstep (se 2 (by rfl) ⟨884031, by rfl⟩ : syracuseStep 2357417 = 1768063) B1768063
theorem B1571099 : Blo 1570983 1571099 := bstep (se 1 (by rfl) ⟨1178324, by rfl⟩ : syracuseStep 1571099 = 2356649) B2356649
theorem B3537179 : Blo 1570983 3537179 := bstep (se 1 (by rfl) ⟨2652884, by rfl⟩ : syracuseStep 3537179 = 5305769) B5305769
theorem B98146619 : Blo 1570983 98146619 := bstep (se 1 (by rfl) ⟨73609964, by rfl⟩ : syracuseStep 98146619 = 147219929) B147219929
theorem B1571135 : Blo 1570983 1571135 := bstep (se 1 (by rfl) ⟨1178351, by rfl⟩ : syracuseStep 1571135 = 2356703) B2356703
theorem B3537215 : Blo 1570983 3537215 := bstep (se 1 (by rfl) ⟨2652911, by rfl⟩ : syracuseStep 3537215 = 5305823) B5305823
theorem B1571567 : Blo 1570983 1571567 := bstep (se 1 (by rfl) ⟨1178675, by rfl⟩ : syracuseStep 1571567 = 2357351) B2357351
theorem B2652959 : Blo 1570983 2652959 := bstep (se 1 (by rfl) ⟨1989719, by rfl⟩ : syracuseStep 2652959 = 3979439) B3979439
theorem B7953551 : Blo 1570983 7953551 := bstep (se 1 (by rfl) ⟨5965163, by rfl⟩ : syracuseStep 7953551 = 11930327) B11930327
theorem B7167305 : Blo 1570983 7167305 := bstep (se 2 (by rfl) ⟨2687739, by rfl⟩ : syracuseStep 7167305 = 5375479) B5375479
theorem B3358199 : Blo 1570983 3358199 := bstep (se 1 (by rfl) ⟨2518649, by rfl⟩ : syracuseStep 3358199 = 5037299) B5037299
theorem B40271417 : Blo 1570983 40271417 := bstep (se 2 (by rfl) ⟨15101781, by rfl⟩ : syracuseStep 40271417 = 30203563) B30203563
theorem B408641543 : Blo 1570983 408641543 := bstep (se 1 (by rfl) ⟨306481157, by rfl⟩ : syracuseStep 408641543 = 612962315) B612962315
theorem B523075643 : Blo 1570983 523075643 := bstep (se 1 (by rfl) ⟨392306732, by rfl⟩ : syracuseStep 523075643 = 784613465) B784613465
theorem B8955197 : Blo 1570983 8955197 := bstep (se 3 (by rfl) ⟨1679099, by rfl⟩ : syracuseStep 8955197 = 3358199) B3358199
theorem B65431079 : Blo 1570983 65431079 := bstep (se 1 (by rfl) ⟨49073309, by rfl⟩ : syracuseStep 65431079 = 98146619) B98146619
theorem B15107705 : Blo 1570983 15107705 := bstep (se 2 (by rfl) ⟨5665389, by rfl⟩ : syracuseStep 15107705 = 11330779) B11330779
theorem B5965559 : Blo 1570983 5965559 := bstep (se 1 (by rfl) ⟨4474169, by rfl⟩ : syracuseStep 5965559 = 8948339) B8948339
theorem B5302205 : Blo 1570983 5302205 := bstep (se 3 (by rfl) ⟨994163, by rfl⟩ : syracuseStep 5302205 = 1988327) B1988327
theorem B5302367 : Blo 1570983 5302367 := bstep (se 1 (by rfl) ⟨3976775, by rfl⟩ : syracuseStep 5302367 = 7953551) B7953551
theorem B4778203 : Blo 1570983 4778203 := bstep (se 1 (by rfl) ⟨3583652, by rfl⟩ : syracuseStep 4778203 = 7167305) B7167305
theorem B26847611 : Blo 1570983 26847611 := bstep (se 1 (by rfl) ⟨20135708, by rfl⟩ : syracuseStep 26847611 = 40271417) B40271417
theorem B8497871 : Blo 1570983 8497871 := bstep (se 1 (by rfl) ⟨6373403, by rfl⟩ : syracuseStep 8497871 = 12746807) B12746807
theorem B13429547 : Blo 1570983 13429547 := bstep (se 1 (by rfl) ⟨10072160, by rfl⟩ : syracuseStep 13429547 = 20144321) B20144321
theorem B235736243 : Blo 1570983 235736243 := bstep (se 1 (by rfl) ⟨176802182, by rfl⟩ : syracuseStep 235736243 = 353604365) B353604365
theorem B11939075 : Blo 1570983 11939075 := bstep (se 1 (by rfl) ⟨8954306, by rfl⟩ : syracuseStep 11939075 = 17908613) B17908613
theorem B14937425 : Blo 1570983 14937425 := bstep (se 2 (by rfl) ⟨5601534, by rfl⟩ : syracuseStep 14937425 = 11203069) B11203069
theorem B5303663 : Blo 1570983 5303663 := bstep (se 1 (by rfl) ⟨3977747, by rfl⟩ : syracuseStep 5303663 = 7955495) B7955495
theorem B5304527 : Blo 1570983 5304527 := bstep (se 1 (by rfl) ⟨3978395, by rfl⟩ : syracuseStep 5304527 = 7956791) B7956791
theorem B3535073 : Blo 1570983 3535073 := bstep (se 2 (by rfl) ⟨1325652, by rfl⟩ : syracuseStep 3535073 = 2651305) B2651305
theorem B3977707 : Blo 1570983 3977707 := bstep (se 1 (by rfl) ⟨2983280, by rfl⟩ : syracuseStep 3977707 = 5966561) B5966561
theorem B5665475 : Blo 1570983 5665475 := bstep (se 1 (by rfl) ⟨4249106, by rfl⟩ : syracuseStep 5665475 = 8498213) B8498213
theorem B22656023 : Blo 1570983 22656023 := bstep (se 1 (by rfl) ⟨16992017, by rfl⟩ : syracuseStep 22656023 = 33984035) B33984035
theorem B30225707 : Blo 1570983 30225707 := bstep (se 1 (by rfl) ⟨22669280, by rfl⟩ : syracuseStep 30225707 = 45338561) B45338561
theorem B3536297 : Blo 1570983 3536297 := bstep (se 2 (by rfl) ⟨1326111, by rfl⟩ : syracuseStep 3536297 = 2652223) B2652223
theorem B3978679 : Blo 1570983 3978679 := bstep (se 1 (by rfl) ⟨2984009, by rfl⟩ : syracuseStep 3978679 = 5968019) B5968019
theorem B7960031 : Blo 1570983 7960031 := bstep (se 1 (by rfl) ⟨5970023, by rfl⟩ : syracuseStep 7960031 = 11940047) B11940047
theorem B2356967 : Blo 1570983 2356967 := bstep (se 1 (by rfl) ⟨1767725, by rfl⟩ : syracuseStep 2356967 = 3535451) B3535451
theorem B9558155 : Blo 1570983 9558155 := bstep (se 1 (by rfl) ⟨7168616, by rfl⟩ : syracuseStep 9558155 = 14337233) B14337233
theorem B2357471 : Blo 1570983 2357471 := bstep (se 1 (by rfl) ⟨1768103, by rfl⟩ : syracuseStep 2357471 = 3536207) B3536207
theorem B1571055 : Blo 1570983 1571055 := bstep (se 1 (by rfl) ⟨1178291, by rfl⟩ : syracuseStep 1571055 = 2356583) B2356583
theorem B3537575 : Blo 1570983 3537575 := bstep (se 1 (by rfl) ⟨2653181, by rfl⟩ : syracuseStep 3537575 = 5306363) B5306363
theorem B3775207 : Blo 1570983 3775207 := bstep (se 1 (by rfl) ⟨2831405, by rfl⟩ : syracuseStep 3775207 = 5662811) B5662811
theorem B3537647 : Blo 1570983 3537647 := bstep (se 1 (by rfl) ⟨2653235, by rfl⟩ : syracuseStep 3537647 = 5306471) B5306471
theorem B1571611 : Blo 1570983 1571611 := bstep (se 1 (by rfl) ⟨1178708, by rfl⟩ : syracuseStep 1571611 = 2357417) B2357417
theorem B2358119 : Blo 1570983 2358119 := bstep (se 1 (by rfl) ⟨1768589, by rfl⟩ : syracuseStep 2358119 = 3537179) B3537179
theorem B2358143 : Blo 1570983 2358143 := bstep (se 1 (by rfl) ⟨1768607, by rfl⟩ : syracuseStep 2358143 = 3537215) B3537215
theorem B1768639 : Blo 1570983 1768639 := bstep (se 1 (by rfl) ⟨1326479, by rfl⟩ : syracuseStep 1768639 = 2652959) B2652959
theorem B348717095 : Blo 1570983 348717095 := bstep (se 1 (by rfl) ⟨261537821, by rfl⟩ : syracuseStep 348717095 = 523075643) B523075643
theorem B15107933 : Blo 1570983 15107933 := bstep (se 3 (by rfl) ⟨2832737, by rfl⟩ : syracuseStep 15107933 = 5665475) B5665475
theorem B157157495 : Blo 1570983 157157495 := bstep (se 1 (by rfl) ⟨117868121, by rfl⟩ : syracuseStep 157157495 = 235736243) B235736243
theorem B272427695 : Blo 1570983 272427695 := bstep (se 1 (by rfl) ⟨204320771, by rfl⟩ : syracuseStep 272427695 = 408641543) B408641543
theorem B43620719 : Blo 1570983 43620719 := bstep (se 1 (by rfl) ⟨32715539, by rfl⟩ : syracuseStep 43620719 = 65431079) B65431079
theorem B5303609 : Blo 1570983 5303609 := bstep (se 2 (by rfl) ⟨1988853, by rfl⟩ : syracuseStep 5303609 = 3977707) B3977707
theorem B5033609 : Blo 1570983 5033609 := bstep (se 2 (by rfl) ⟨1887603, by rfl⟩ : syracuseStep 5033609 = 3775207) B3775207
theorem B10071803 : Blo 1570983 10071803 := bstep (se 1 (by rfl) ⟨7553852, by rfl⟩ : syracuseStep 10071803 = 15107705) B15107705
theorem B3977039 : Blo 1570983 3977039 := bstep (se 1 (by rfl) ⟨2982779, by rfl⟩ : syracuseStep 3977039 = 5965559) B5965559
theorem B3534803 : Blo 1570983 3534803 := bstep (se 1 (by rfl) ⟨2651102, by rfl⟩ : syracuseStep 3534803 = 5302205) B5302205
theorem B3534911 : Blo 1570983 3534911 := bstep (se 1 (by rfl) ⟨2651183, by rfl⟩ : syracuseStep 3534911 = 5302367) B5302367
theorem B5665247 : Blo 1570983 5665247 := bstep (se 1 (by rfl) ⟨4248935, by rfl⟩ : syracuseStep 5665247 = 8497871) B8497871
theorem B5304905 : Blo 1570983 5304905 := bstep (se 2 (by rfl) ⟨1989339, by rfl⟩ : syracuseStep 5304905 = 3978679) B3978679
theorem B7959383 : Blo 1570983 7959383 := bstep (se 1 (by rfl) ⟨5969537, by rfl⟩ : syracuseStep 7959383 = 11939075) B11939075
theorem B9958283 : Blo 1570983 9958283 := bstep (se 1 (by rfl) ⟨7468712, by rfl⟩ : syracuseStep 9958283 = 14937425) B14937425
theorem B3535775 : Blo 1570983 3535775 := bstep (se 1 (by rfl) ⟨2651831, by rfl⟩ : syracuseStep 3535775 = 5303663) B5303663
theorem B3536351 : Blo 1570983 3536351 := bstep (se 1 (by rfl) ⟨2652263, by rfl⟩ : syracuseStep 3536351 = 5304527) B5304527
theorem B2356715 : Blo 1570983 2356715 := bstep (se 1 (by rfl) ⟨1767536, by rfl⟩ : syracuseStep 2356715 = 3535073) B3535073
theorem B6370937 : Blo 1570983 6370937 := bstep (se 2 (by rfl) ⟨2389101, by rfl⟩ : syracuseStep 6370937 = 4778203) B4778203
theorem B15104015 : Blo 1570983 15104015 := bstep (se 1 (by rfl) ⟨11328011, by rfl⟩ : syracuseStep 15104015 = 22656023) B22656023
theorem B20150471 : Blo 1570983 20150471 := bstep (se 1 (by rfl) ⟨15112853, by rfl⟩ : syracuseStep 20150471 = 30225707) B30225707
theorem B5970131 : Blo 1570983 5970131 := bstep (se 1 (by rfl) ⟨4477598, by rfl⟩ : syracuseStep 5970131 = 8955197) B8955197
theorem B2357531 : Blo 1570983 2357531 := bstep (se 1 (by rfl) ⟨1768148, by rfl⟩ : syracuseStep 2357531 = 3536297) B3536297
theorem B5306687 : Blo 1570983 5306687 := bstep (se 1 (by rfl) ⟨3980015, by rfl⟩ : syracuseStep 5306687 = 7960031) B7960031
theorem B1571311 : Blo 1570983 1571311 := bstep (se 1 (by rfl) ⟨1178483, by rfl⟩ : syracuseStep 1571311 = 2356967) B2356967
theorem B6372103 : Blo 1570983 6372103 := bstep (se 1 (by rfl) ⟨4779077, by rfl⟩ : syracuseStep 6372103 = 9558155) B9558155
theorem B1571647 : Blo 1570983 1571647 := bstep (se 1 (by rfl) ⟨1178735, by rfl⟩ : syracuseStep 1571647 = 2357471) B2357471
theorem B17898407 : Blo 1570983 17898407 := bstep (se 1 (by rfl) ⟨13423805, by rfl⟩ : syracuseStep 17898407 = 26847611) B26847611
theorem B2358185 : Blo 1570983 2358185 := bstep (se 2 (by rfl) ⟨884319, by rfl⟩ : syracuseStep 2358185 = 1768639) B1768639
theorem B2358383 : Blo 1570983 2358383 := bstep (se 1 (by rfl) ⟨1768787, by rfl⟩ : syracuseStep 2358383 = 3537575) B3537575
theorem B2358431 : Blo 1570983 2358431 := bstep (se 1 (by rfl) ⟨1768823, by rfl⟩ : syracuseStep 2358431 = 3537647) B3537647
theorem B8953031 : Blo 1570983 8953031 := bstep (se 1 (by rfl) ⟨6714773, by rfl⟩ : syracuseStep 8953031 = 13429547) B13429547
theorem B1572079 : Blo 1570983 1572079 := bstep (se 1 (by rfl) ⟨1179059, by rfl⟩ : syracuseStep 1572079 = 2358119) B2358119
theorem B1572095 : Blo 1570983 1572095 := bstep (se 1 (by rfl) ⟨1179071, by rfl⟩ : syracuseStep 1572095 = 2358143) B2358143
theorem B3776831 : Blo 1570983 3776831 := bstep (se 1 (by rfl) ⟨2832623, by rfl⟩ : syracuseStep 3776831 = 5665247) B5665247
theorem B8496137 : Blo 1570983 8496137 := bstep (se 2 (by rfl) ⟨3186051, by rfl⟩ : syracuseStep 8496137 = 6372103) B6372103
theorem B10069343 : Blo 1570983 10069343 := bstep (se 1 (by rfl) ⟨7552007, by rfl⟩ : syracuseStep 10069343 = 15104015) B15104015
theorem B181618463 : Blo 1570983 181618463 := bstep (se 1 (by rfl) ⟨136213847, by rfl⟩ : syracuseStep 181618463 = 272427695) B272427695
theorem B6638855 : Blo 1570983 6638855 := bstep (se 1 (by rfl) ⟨4979141, by rfl⟩ : syracuseStep 6638855 = 9958283) B9958283
theorem B116321917 : Blo 1570983 116321917 := bstep (se 3 (by rfl) ⟨21810359, by rfl⟩ : syracuseStep 116321917 = 43620719) B43620719
theorem B4247291 : Blo 1570983 4247291 := bstep (se 1 (by rfl) ⟨3185468, by rfl⟩ : syracuseStep 4247291 = 6370937) B6370937
theorem B10071955 : Blo 1570983 10071955 := bstep (se 1 (by rfl) ⟨7553966, by rfl⟩ : syracuseStep 10071955 = 15107933) B15107933
theorem B104771663 : Blo 1570983 104771663 := bstep (se 1 (by rfl) ⟨78578747, by rfl⟩ : syracuseStep 104771663 = 157157495) B157157495
theorem B11932271 : Blo 1570983 11932271 := bstep (se 1 (by rfl) ⟨8949203, by rfl⟩ : syracuseStep 11932271 = 17898407) B17898407
theorem B5968687 : Blo 1570983 5968687 := bstep (se 1 (by rfl) ⟨4476515, by rfl⟩ : syracuseStep 5968687 = 8953031) B8953031
theorem B3535739 : Blo 1570983 3535739 := bstep (se 1 (by rfl) ⟨2651804, by rfl⟩ : syracuseStep 3535739 = 5303609) B5303609
theorem B3355739 : Blo 1570983 3355739 := bstep (se 1 (by rfl) ⟨2516804, by rfl⟩ : syracuseStep 3355739 = 5033609) B5033609
theorem B6714535 : Blo 1570983 6714535 := bstep (se 1 (by rfl) ⟨5035901, by rfl⟩ : syracuseStep 6714535 = 10071803) B10071803
theorem B2651359 : Blo 1570983 2651359 := bstep (se 1 (by rfl) ⟨1988519, by rfl⟩ : syracuseStep 2651359 = 3977039) B3977039
theorem B2356535 : Blo 1570983 2356535 := bstep (se 1 (by rfl) ⟨1767401, by rfl⟩ : syracuseStep 2356535 = 3534803) B3534803
theorem B232478063 : Blo 1570983 232478063 := bstep (se 1 (by rfl) ⟨174358547, by rfl⟩ : syracuseStep 232478063 = 348717095) B348717095
theorem B2356607 : Blo 1570983 2356607 := bstep (se 1 (by rfl) ⟨1767455, by rfl⟩ : syracuseStep 2356607 = 3534911) B3534911
theorem B3536603 : Blo 1570983 3536603 := bstep (se 1 (by rfl) ⟨2652452, by rfl⟩ : syracuseStep 3536603 = 5304905) B5304905
theorem B5306255 : Blo 1570983 5306255 := bstep (se 1 (by rfl) ⟨3979691, by rfl⟩ : syracuseStep 5306255 = 7959383) B7959383
theorem B2357183 : Blo 1570983 2357183 := bstep (se 1 (by rfl) ⟨1767887, by rfl⟩ : syracuseStep 2357183 = 3535775) B3535775
theorem B2357567 : Blo 1570983 2357567 := bstep (se 1 (by rfl) ⟨1768175, by rfl⟩ : syracuseStep 2357567 = 3536351) B3536351
theorem B1571143 : Blo 1570983 1571143 := bstep (se 1 (by rfl) ⟨1178357, by rfl⟩ : syracuseStep 1571143 = 2356715) B2356715
theorem B13433647 : Blo 1570983 13433647 := bstep (se 1 (by rfl) ⟨10075235, by rfl⟩ : syracuseStep 13433647 = 20150471) B20150471
theorem B3980087 : Blo 1570983 3980087 := bstep (se 1 (by rfl) ⟨2985065, by rfl⟩ : syracuseStep 3980087 = 5970131) B5970131
theorem B1571687 : Blo 1570983 1571687 := bstep (se 1 (by rfl) ⟨1178765, by rfl⟩ : syracuseStep 1571687 = 2357531) B2357531
theorem B3537791 : Blo 1570983 3537791 := bstep (se 1 (by rfl) ⟨2653343, by rfl⟩ : syracuseStep 3537791 = 5306687) B5306687
theorem B1572123 : Blo 1570983 1572123 := bstep (se 1 (by rfl) ⟨1179092, by rfl⟩ : syracuseStep 1572123 = 2358185) B2358185
theorem B1572255 : Blo 1570983 1572255 := bstep (se 1 (by rfl) ⟨1179191, by rfl⟩ : syracuseStep 1572255 = 2358383) B2358383
theorem B1572287 : Blo 1570983 1572287 := bstep (se 1 (by rfl) ⟨1179215, by rfl⟩ : syracuseStep 1572287 = 2358431) B2358431
theorem B7954847 : Blo 1570983 7954847 := bstep (se 1 (by rfl) ⟨5966135, by rfl⟩ : syracuseStep 7954847 = 11932271) B11932271
theorem B17703613 : Blo 1570983 17703613 := bstep (se 3 (by rfl) ⟨3319427, by rfl⟩ : syracuseStep 17703613 = 6638855) B6638855
theorem B2237159 : Blo 1570983 2237159 := bstep (se 1 (by rfl) ⟨1677869, by rfl⟩ : syracuseStep 2237159 = 3355739) B3355739
theorem B154985375 : Blo 1570983 154985375 := bstep (se 1 (by rfl) ⟨116239031, by rfl⟩ : syracuseStep 154985375 = 232478063) B232478063
theorem B13429273 : Blo 1570983 13429273 := bstep (se 2 (by rfl) ⟨5035977, by rfl⟩ : syracuseStep 13429273 = 10071955) B10071955
theorem B69847775 : Blo 1570983 69847775 := bstep (se 1 (by rfl) ⟨52385831, by rfl⟩ : syracuseStep 69847775 = 104771663) B104771663
theorem B2517887 : Blo 1570983 2517887 := bstep (se 1 (by rfl) ⟨1888415, by rfl⟩ : syracuseStep 2517887 = 3776831) B3776831
theorem B5664091 : Blo 1570983 5664091 := bstep (se 1 (by rfl) ⟨4248068, by rfl⟩ : syracuseStep 5664091 = 8496137) B8496137
theorem B6712895 : Blo 1570983 6712895 := bstep (se 1 (by rfl) ⟨5034671, by rfl⟩ : syracuseStep 6712895 = 10069343) B10069343
theorem B7958249 : Blo 1570983 7958249 := bstep (se 2 (by rfl) ⟨2984343, by rfl⟩ : syracuseStep 7958249 = 5968687) B5968687
theorem B17911529 : Blo 1570983 17911529 := bstep (se 2 (by rfl) ⟨6716823, by rfl⟩ : syracuseStep 17911529 = 13433647) B13433647
theorem B3535145 : Blo 1570983 3535145 := bstep (se 2 (by rfl) ⟨1325679, by rfl⟩ : syracuseStep 3535145 = 2651359) B2651359
theorem B484315901 : Blo 1570983 484315901 := bstep (se 3 (by rfl) ⟨90809231, by rfl⟩ : syracuseStep 484315901 = 181618463) B181618463
theorem B155095889 : Blo 1570983 155095889 := bstep (se 2 (by rfl) ⟨58160958, by rfl⟩ : syracuseStep 155095889 = 116321917) B116321917
theorem B2831527 : Blo 1570983 2831527 := bstep (se 1 (by rfl) ⟨2123645, by rfl⟩ : syracuseStep 2831527 = 4247291) B4247291
theorem B2357159 : Blo 1570983 2357159 := bstep (se 1 (by rfl) ⟨1767869, by rfl⟩ : syracuseStep 2357159 = 3535739) B3535739
theorem B1571023 : Blo 1570983 1571023 := bstep (se 1 (by rfl) ⟨1178267, by rfl⟩ : syracuseStep 1571023 = 2356535) B2356535
theorem B1571071 : Blo 1570983 1571071 := bstep (se 1 (by rfl) ⟨1178303, by rfl⟩ : syracuseStep 1571071 = 2356607) B2356607
theorem B2357735 : Blo 1570983 2357735 := bstep (se 1 (by rfl) ⟨1768301, by rfl⟩ : syracuseStep 2357735 = 3536603) B3536603
theorem B3537503 : Blo 1570983 3537503 := bstep (se 1 (by rfl) ⟨2653127, by rfl⟩ : syracuseStep 3537503 = 5306255) B5306255
theorem B1571455 : Blo 1570983 1571455 := bstep (se 1 (by rfl) ⟨1178591, by rfl⟩ : syracuseStep 1571455 = 2357183) B2357183
theorem B1571711 : Blo 1570983 1571711 := bstep (se 1 (by rfl) ⟨1178783, by rfl⟩ : syracuseStep 1571711 = 2357567) B2357567
theorem B8952713 : Blo 1570983 8952713 := bstep (se 2 (by rfl) ⟨3357267, by rfl⟩ : syracuseStep 8952713 = 6714535) B6714535
theorem B2653391 : Blo 1570983 2653391 := bstep (se 1 (by rfl) ⟨1990043, by rfl⟩ : syracuseStep 2653391 = 3980087) B3980087
theorem B2358527 : Blo 1570983 2358527 := bstep (se 1 (by rfl) ⟨1768895, by rfl⟩ : syracuseStep 2358527 = 3537791) B3537791
theorem B46565183 : Blo 1570983 46565183 := bstep (se 1 (by rfl) ⟨34923887, by rfl⟩ : syracuseStep 46565183 = 69847775) B69847775
theorem B5965757 : Blo 1570983 5965757 := bstep (se 3 (by rfl) ⟨1118579, by rfl⟩ : syracuseStep 5965757 = 2237159) B2237159
theorem B4475263 : Blo 1570983 4475263 := bstep (se 1 (by rfl) ⟨3356447, by rfl⟩ : syracuseStep 4475263 = 6712895) B6712895
theorem B5303231 : Blo 1570983 5303231 := bstep (se 1 (by rfl) ⟨3977423, by rfl⟩ : syracuseStep 5303231 = 7954847) B7954847
theorem B15101477 : Blo 1570983 15101477 := bstep (se 4 (by rfl) ⟨1415763, by rfl⟩ : syracuseStep 15101477 = 2831527) B2831527
theorem B5968475 : Blo 1570983 5968475 := bstep (se 1 (by rfl) ⟨4476356, by rfl⟩ : syracuseStep 5968475 = 8952713) B8952713
theorem B5305499 : Blo 1570983 5305499 := bstep (se 1 (by rfl) ⟨3979124, by rfl⟩ : syracuseStep 5305499 = 7958249) B7958249
theorem B11941019 : Blo 1570983 11941019 := bstep (se 1 (by rfl) ⟨8955764, by rfl⟩ : syracuseStep 11941019 = 17911529) B17911529
theorem B2356763 : Blo 1570983 2356763 := bstep (se 1 (by rfl) ⟨1767572, by rfl⟩ : syracuseStep 2356763 = 3535145) B3535145
theorem B322877267 : Blo 1570983 322877267 := bstep (se 1 (by rfl) ⟨242157950, by rfl⟩ : syracuseStep 322877267 = 484315901) B484315901
theorem B103323583 : Blo 1570983 103323583 := bstep (se 1 (by rfl) ⟨77492687, by rfl⟩ : syracuseStep 103323583 = 154985375) B154985375
theorem B17905697 : Blo 1570983 17905697 := bstep (se 2 (by rfl) ⟨6714636, by rfl⟩ : syracuseStep 17905697 = 13429273) B13429273
theorem B94419269 : Blo 1570983 94419269 := bstep (se 4 (by rfl) ⟨8851806, by rfl⟩ : syracuseStep 94419269 = 17703613) B17703613
theorem B1571439 : Blo 1570983 1571439 := bstep (se 1 (by rfl) ⟨1178579, by rfl⟩ : syracuseStep 1571439 = 2357159) B2357159
theorem B1571823 : Blo 1570983 1571823 := bstep (se 1 (by rfl) ⟨1178867, by rfl⟩ : syracuseStep 1571823 = 2357735) B2357735
theorem B2358335 : Blo 1570983 2358335 := bstep (se 1 (by rfl) ⟨1768751, by rfl⟩ : syracuseStep 2358335 = 3537503) B3537503
theorem B7552121 : Blo 1570983 7552121 := bstep (se 2 (by rfl) ⟨2832045, by rfl⟩ : syracuseStep 7552121 = 5664091) B5664091
theorem B1678591 : Blo 1570983 1678591 := bstep (se 1 (by rfl) ⟨1258943, by rfl⟩ : syracuseStep 1678591 = 2517887) B2517887
theorem B1768927 : Blo 1570983 1768927 := bstep (se 1 (by rfl) ⟨1326695, by rfl⟩ : syracuseStep 1768927 = 2653391) B2653391
theorem B1572351 : Blo 1570983 1572351 := bstep (se 1 (by rfl) ⟨1179263, by rfl⟩ : syracuseStep 1572351 = 2358527) B2358527
theorem B413589037 : Blo 1570983 413589037 := bstep (se 3 (by rfl) ⟨77547944, by rfl⟩ : syracuseStep 413589037 = 155095889) B155095889
theorem B11937131 : Blo 1570983 11937131 := bstep (se 1 (by rfl) ⟨8952848, by rfl⟩ : syracuseStep 11937131 = 17905697) B17905697
theorem B2238121 : Blo 1570983 2238121 := bstep (se 2 (by rfl) ⟨839295, by rfl⟩ : syracuseStep 2238121 = 1678591) B1678591
theorem B20138989 : Blo 1570983 20138989 := bstep (se 3 (by rfl) ⟨3776060, by rfl⟩ : syracuseStep 20138989 = 7552121) B7552121
theorem B5967017 : Blo 1570983 5967017 := bstep (se 2 (by rfl) ⟨2237631, by rfl⟩ : syracuseStep 5967017 = 4475263) B4475263
theorem B31043455 : Blo 1570983 31043455 := bstep (se 1 (by rfl) ⟨23282591, by rfl⟩ : syracuseStep 31043455 = 46565183) B46565183
theorem B3977171 : Blo 1570983 3977171 := bstep (se 1 (by rfl) ⟨2982878, by rfl⟩ : syracuseStep 3977171 = 5965757) B5965757
theorem B3535487 : Blo 1570983 3535487 := bstep (se 1 (by rfl) ⟨2651615, by rfl⟩ : syracuseStep 3535487 = 5303231) B5303231
theorem B3978983 : Blo 1570983 3978983 := bstep (se 1 (by rfl) ⟨2984237, by rfl⟩ : syracuseStep 3978983 = 5968475) B5968475
theorem B3536999 : Blo 1570983 3536999 := bstep (se 1 (by rfl) ⟨2652749, by rfl⟩ : syracuseStep 3536999 = 5305499) B5305499
theorem B7960679 : Blo 1570983 7960679 := bstep (se 1 (by rfl) ⟨5970509, by rfl⟩ : syracuseStep 7960679 = 11941019) B11941019
theorem B1571175 : Blo 1570983 1571175 := bstep (se 1 (by rfl) ⟨1178381, by rfl⟩ : syracuseStep 1571175 = 2356763) B2356763
theorem B215251511 : Blo 1570983 215251511 := bstep (se 1 (by rfl) ⟨161438633, by rfl⟩ : syracuseStep 215251511 = 322877267) B322877267
theorem B62946179 : Blo 1570983 62946179 := bstep (se 1 (by rfl) ⟨47209634, by rfl⟩ : syracuseStep 62946179 = 94419269) B94419269
theorem B2358569 : Blo 1570983 2358569 := bstep (se 2 (by rfl) ⟨884463, by rfl⟩ : syracuseStep 2358569 = 1768927) B1768927
theorem B1572223 : Blo 1570983 1572223 := bstep (se 1 (by rfl) ⟨1179167, by rfl⟩ : syracuseStep 1572223 = 2358335) B2358335
theorem B551452049 : Blo 1570983 551452049 := bstep (se 2 (by rfl) ⟨206794518, by rfl⟩ : syracuseStep 551452049 = 413589037) B413589037
theorem B551059109 : Blo 1570983 551059109 := bstep (se 4 (by rfl) ⟨51661791, by rfl⟩ : syracuseStep 551059109 = 103323583) B103323583
theorem B10067651 : Blo 1570983 10067651 := bstep (se 1 (by rfl) ⟨7550738, by rfl⟩ : syracuseStep 10067651 = 15101477) B15101477
theorem B11936645 : Blo 1570983 11936645 := bstep (se 4 (by rfl) ⟨1119060, by rfl⟩ : syracuseStep 11936645 = 2238121) B2238121
theorem B367634699 : Blo 1570983 367634699 := bstep (se 1 (by rfl) ⟨275726024, by rfl⟩ : syracuseStep 367634699 = 551452049) B551452049
theorem B367372739 : Blo 1570983 367372739 := bstep (se 1 (by rfl) ⟨275529554, by rfl⟩ : syracuseStep 367372739 = 551059109) B551059109
theorem B6711767 : Blo 1570983 6711767 := bstep (se 1 (by rfl) ⟨5033825, by rfl⟩ : syracuseStep 6711767 = 10067651) B10067651
theorem B7958087 : Blo 1570983 7958087 := bstep (se 1 (by rfl) ⟨5968565, by rfl⟩ : syracuseStep 7958087 = 11937131) B11937131
theorem B41964119 : Blo 1570983 41964119 := bstep (se 1 (by rfl) ⟨31473089, by rfl⟩ : syracuseStep 41964119 = 62946179) B62946179
theorem B165565093 : Blo 1570983 165565093 := bstep (se 4 (by rfl) ⟨15521727, by rfl⟩ : syracuseStep 165565093 = 31043455) B31043455
theorem B3978011 : Blo 1570983 3978011 := bstep (se 1 (by rfl) ⟨2983508, by rfl⟩ : syracuseStep 3978011 = 5967017) B5967017
theorem B2651447 : Blo 1570983 2651447 := bstep (se 1 (by rfl) ⟨1988585, by rfl⟩ : syracuseStep 2651447 = 3977171) B3977171
theorem B2356991 : Blo 1570983 2356991 := bstep (se 1 (by rfl) ⟨1767743, by rfl⟩ : syracuseStep 2356991 = 3535487) B3535487
theorem B2652655 : Blo 1570983 2652655 := bstep (se 1 (by rfl) ⟨1989491, by rfl⟩ : syracuseStep 2652655 = 3978983) B3978983
theorem B26851985 : Blo 1570983 26851985 := bstep (se 2 (by rfl) ⟨10069494, by rfl⟩ : syracuseStep 26851985 = 20138989) B20138989
theorem B2357999 : Blo 1570983 2357999 := bstep (se 1 (by rfl) ⟨1768499, by rfl⟩ : syracuseStep 2357999 = 3536999) B3536999
theorem B5307119 : Blo 1570983 5307119 := bstep (se 1 (by rfl) ⟨3980339, by rfl⟩ : syracuseStep 5307119 = 7960679) B7960679
theorem B574004029 : Blo 1570983 574004029 := bstep (se 3 (by rfl) ⟨107625755, by rfl⟩ : syracuseStep 574004029 = 215251511) B215251511
theorem B1572379 : Blo 1570983 1572379 := bstep (se 1 (by rfl) ⟨1179284, by rfl⟩ : syracuseStep 1572379 = 2358569) B2358569
theorem B27976079 : Blo 1570983 27976079 := bstep (se 1 (by rfl) ⟨20982059, by rfl⟩ : syracuseStep 27976079 = 41964119) B41964119
theorem B765338705 : Blo 1570983 765338705 := bstep (se 2 (by rfl) ⟨287002014, by rfl⟩ : syracuseStep 765338705 = 574004029) B574004029
theorem B245089799 : Blo 1570983 245089799 := bstep (se 1 (by rfl) ⟨183817349, by rfl⟩ : syracuseStep 245089799 = 367634699) B367634699
theorem B4474511 : Blo 1570983 4474511 := bstep (se 1 (by rfl) ⟨3355883, by rfl⟩ : syracuseStep 4474511 = 6711767) B6711767
theorem B17901323 : Blo 1570983 17901323 := bstep (se 1 (by rfl) ⟨13425992, by rfl⟩ : syracuseStep 17901323 = 26851985) B26851985
theorem B7957763 : Blo 1570983 7957763 := bstep (se 1 (by rfl) ⟨5968322, by rfl⟩ : syracuseStep 7957763 = 11936645) B11936645
theorem B220753457 : Blo 1570983 220753457 := bstep (se 2 (by rfl) ⟨82782546, by rfl⟩ : syracuseStep 220753457 = 165565093) B165565093
theorem B5305391 : Blo 1570983 5305391 := bstep (se 1 (by rfl) ⟨3979043, by rfl⟩ : syracuseStep 5305391 = 7958087) B7958087
theorem B2652007 : Blo 1570983 2652007 := bstep (se 1 (by rfl) ⟨1989005, by rfl⟩ : syracuseStep 2652007 = 3978011) B3978011
theorem B3536873 : Blo 1570983 3536873 := bstep (se 2 (by rfl) ⟨1326327, by rfl⟩ : syracuseStep 3536873 = 2652655) B2652655
theorem B1767631 : Blo 1570983 1767631 := bstep (se 1 (by rfl) ⟨1325723, by rfl⟩ : syracuseStep 1767631 = 2651447) B2651447
theorem B1571327 : Blo 1570983 1571327 := bstep (se 1 (by rfl) ⟨1178495, by rfl⟩ : syracuseStep 1571327 = 2356991) B2356991
theorem B244915159 : Blo 1570983 244915159 := bstep (se 1 (by rfl) ⟨183686369, by rfl⟩ : syracuseStep 244915159 = 367372739) B367372739
theorem B1571999 : Blo 1570983 1571999 := bstep (se 1 (by rfl) ⟨1178999, by rfl⟩ : syracuseStep 1571999 = 2357999) B2357999
theorem B3538079 : Blo 1570983 3538079 := bstep (se 1 (by rfl) ⟨2653559, by rfl⟩ : syracuseStep 3538079 = 5307119) B5307119
theorem B2983007 : Blo 1570983 2983007 := bstep (se 1 (by rfl) ⟨2237255, by rfl⟩ : syracuseStep 2983007 = 4474511) B4474511
theorem B510225803 : Blo 1570983 510225803 := bstep (se 1 (by rfl) ⟨382669352, by rfl⟩ : syracuseStep 510225803 = 765338705) B765338705
theorem B163393199 : Blo 1570983 163393199 := bstep (se 1 (by rfl) ⟨122544899, by rfl⟩ : syracuseStep 163393199 = 245089799) B245089799
theorem B326553545 : Blo 1570983 326553545 := bstep (se 2 (by rfl) ⟨122457579, by rfl⟩ : syracuseStep 326553545 = 244915159) B244915159
theorem B5305175 : Blo 1570983 5305175 := bstep (se 1 (by rfl) ⟨3978881, by rfl⟩ : syracuseStep 5305175 = 7957763) B7957763
theorem B3536009 : Blo 1570983 3536009 := bstep (se 2 (by rfl) ⟨1326003, by rfl⟩ : syracuseStep 3536009 = 2652007) B2652007
theorem B18650719 : Blo 1570983 18650719 := bstep (se 1 (by rfl) ⟨13988039, by rfl⟩ : syracuseStep 18650719 = 27976079) B27976079
theorem B2356841 : Blo 1570983 2356841 := bstep (se 2 (by rfl) ⟨883815, by rfl⟩ : syracuseStep 2356841 = 1767631) B1767631
theorem B3536927 : Blo 1570983 3536927 := bstep (se 1 (by rfl) ⟨2652695, by rfl⟩ : syracuseStep 3536927 = 5305391) B5305391
theorem B11934215 : Blo 1570983 11934215 := bstep (se 1 (by rfl) ⟨8950661, by rfl⟩ : syracuseStep 11934215 = 17901323) B17901323
theorem B2357915 : Blo 1570983 2357915 := bstep (se 1 (by rfl) ⟨1768436, by rfl⟩ : syracuseStep 2357915 = 3536873) B3536873
theorem B2358719 : Blo 1570983 2358719 := bstep (se 1 (by rfl) ⟨1769039, by rfl⟩ : syracuseStep 2358719 = 3538079) B3538079
theorem B147168971 : Blo 1570983 147168971 := bstep (se 1 (by rfl) ⟨110376728, by rfl⟩ : syracuseStep 147168971 = 220753457) B220753457
theorem B7954685 : Blo 1570983 7954685 := bstep (se 3 (by rfl) ⟨1491503, by rfl⟩ : syracuseStep 7954685 = 2983007) B2983007
theorem B7956143 : Blo 1570983 7956143 := bstep (se 1 (by rfl) ⟨5967107, by rfl⟩ : syracuseStep 7956143 = 11934215) B11934215
theorem B340150535 : Blo 1570983 340150535 := bstep (se 1 (by rfl) ⟨255112901, by rfl⟩ : syracuseStep 340150535 = 510225803) B510225803
theorem B99470501 : Blo 1570983 99470501 := bstep (se 4 (by rfl) ⟨9325359, by rfl⟩ : syracuseStep 99470501 = 18650719) B18650719
theorem B98112647 : Blo 1570983 98112647 := bstep (se 1 (by rfl) ⟨73584485, by rfl⟩ : syracuseStep 98112647 = 147168971) B147168971
theorem B3536783 : Blo 1570983 3536783 := bstep (se 1 (by rfl) ⟨2652587, by rfl⟩ : syracuseStep 3536783 = 5305175) B5305175
theorem B2357339 : Blo 1570983 2357339 := bstep (se 1 (by rfl) ⟨1768004, by rfl⟩ : syracuseStep 2357339 = 3536009) B3536009
theorem B1571227 : Blo 1570983 1571227 := bstep (se 1 (by rfl) ⟨1178420, by rfl⟩ : syracuseStep 1571227 = 2356841) B2356841
theorem B2357951 : Blo 1570983 2357951 := bstep (se 1 (by rfl) ⟨1768463, by rfl⟩ : syracuseStep 2357951 = 3536927) B3536927
theorem B1571943 : Blo 1570983 1571943 := bstep (se 1 (by rfl) ⟨1178957, by rfl⟩ : syracuseStep 1571943 = 2357915) B2357915
theorem B1572479 : Blo 1570983 1572479 := bstep (se 1 (by rfl) ⟨1179359, by rfl⟩ : syracuseStep 1572479 = 2358719) B2358719
theorem B108928799 : Blo 1570983 108928799 := bstep (se 1 (by rfl) ⟨81696599, by rfl⟩ : syracuseStep 108928799 = 163393199) B163393199
theorem B217702363 : Blo 1570983 217702363 := bstep (se 1 (by rfl) ⟨163276772, by rfl⟩ : syracuseStep 217702363 = 326553545) B326553545
theorem B290269817 : Blo 1570983 290269817 := bstep (se 2 (by rfl) ⟨108851181, by rfl⟩ : syracuseStep 290269817 = 217702363) B217702363
theorem B5303123 : Blo 1570983 5303123 := bstep (se 1 (by rfl) ⟨3977342, by rfl⟩ : syracuseStep 5303123 = 7954685) B7954685
theorem B65408431 : Blo 1570983 65408431 := bstep (se 1 (by rfl) ⟨49056323, by rfl⟩ : syracuseStep 65408431 = 98112647) B98112647
theorem B5304095 : Blo 1570983 5304095 := bstep (se 1 (by rfl) ⟨3978071, by rfl⟩ : syracuseStep 5304095 = 7956143) B7956143
theorem B226767023 : Blo 1570983 226767023 := bstep (se 1 (by rfl) ⟨170075267, by rfl⟩ : syracuseStep 226767023 = 340150535) B340150535
theorem B72619199 : Blo 1570983 72619199 := bstep (se 1 (by rfl) ⟨54464399, by rfl⟩ : syracuseStep 72619199 = 108928799) B108928799
theorem B2357855 : Blo 1570983 2357855 := bstep (se 1 (by rfl) ⟨1768391, by rfl⟩ : syracuseStep 2357855 = 3536783) B3536783
theorem B1571559 : Blo 1570983 1571559 := bstep (se 1 (by rfl) ⟨1178669, by rfl⟩ : syracuseStep 1571559 = 2357339) B2357339
theorem B1571967 : Blo 1570983 1571967 := bstep (se 1 (by rfl) ⟨1178975, by rfl⟩ : syracuseStep 1571967 = 2357951) B2357951
theorem B66313667 : Blo 1570983 66313667 := bstep (se 1 (by rfl) ⟨49735250, by rfl⟩ : syracuseStep 66313667 = 99470501) B99470501
theorem B193513211 : Blo 1570983 193513211 := bstep (se 1 (by rfl) ⟨145134908, by rfl⟩ : syracuseStep 193513211 = 290269817) B290269817
theorem B151178015 : Blo 1570983 151178015 := bstep (se 1 (by rfl) ⟨113383511, by rfl⟩ : syracuseStep 151178015 = 226767023) B226767023
theorem B3535415 : Blo 1570983 3535415 := bstep (se 1 (by rfl) ⟨2651561, by rfl⟩ : syracuseStep 3535415 = 5303123) B5303123
theorem B44209111 : Blo 1570983 44209111 := bstep (se 1 (by rfl) ⟨33156833, by rfl⟩ : syracuseStep 44209111 = 66313667) B66313667
theorem B3536063 : Blo 1570983 3536063 := bstep (se 1 (by rfl) ⟨2652047, by rfl⟩ : syracuseStep 3536063 = 5304095) B5304095
theorem B48412799 : Blo 1570983 48412799 := bstep (se 1 (by rfl) ⟨36309599, by rfl⟩ : syracuseStep 48412799 = 72619199) B72619199
theorem B1571903 : Blo 1570983 1571903 := bstep (se 1 (by rfl) ⟨1178927, by rfl⟩ : syracuseStep 1571903 = 2357855) B2357855
theorem B87211241 : Blo 1570983 87211241 := bstep (se 2 (by rfl) ⟨32704215, by rfl⟩ : syracuseStep 87211241 = 65408431) B65408431
theorem B129008807 : Blo 1570983 129008807 := bstep (se 1 (by rfl) ⟨96756605, by rfl⟩ : syracuseStep 129008807 = 193513211) B193513211
theorem B58140827 : Blo 1570983 58140827 := bstep (se 1 (by rfl) ⟨43605620, by rfl⟩ : syracuseStep 58140827 = 87211241) B87211241
theorem B58945481 : Blo 1570983 58945481 := bstep (se 2 (by rfl) ⟨22104555, by rfl⟩ : syracuseStep 58945481 = 44209111) B44209111
theorem B2356943 : Blo 1570983 2356943 := bstep (se 1 (by rfl) ⟨1767707, by rfl⟩ : syracuseStep 2356943 = 3535415) B3535415
theorem B2357375 : Blo 1570983 2357375 := bstep (se 1 (by rfl) ⟨1768031, by rfl⟩ : syracuseStep 2357375 = 3536063) B3536063
theorem B32275199 : Blo 1570983 32275199 := bstep (se 1 (by rfl) ⟨24206399, by rfl⟩ : syracuseStep 32275199 = 48412799) B48412799
theorem B100785343 : Blo 1570983 100785343 := bstep (se 1 (by rfl) ⟨75589007, by rfl⟩ : syracuseStep 100785343 = 151178015) B151178015
theorem B86067197 : Blo 1570983 86067197 := bstep (se 3 (by rfl) ⟨16137599, by rfl⟩ : syracuseStep 86067197 = 32275199) B32275199
theorem B38760551 : Blo 1570983 38760551 := bstep (se 1 (by rfl) ⟨29070413, by rfl⟩ : syracuseStep 38760551 = 58140827) B58140827
theorem B86005871 : Blo 1570983 86005871 := bstep (se 1 (by rfl) ⟨64504403, by rfl⟩ : syracuseStep 86005871 = 129008807) B129008807
theorem B1571295 : Blo 1570983 1571295 := bstep (se 1 (by rfl) ⟨1178471, by rfl⟩ : syracuseStep 1571295 = 2356943) B2356943
theorem B1571583 : Blo 1570983 1571583 := bstep (se 1 (by rfl) ⟨1178687, by rfl⟩ : syracuseStep 1571583 = 2357375) B2357375
theorem B134380457 : Blo 1570983 134380457 := bstep (se 2 (by rfl) ⟨50392671, by rfl⟩ : syracuseStep 134380457 = 100785343) B100785343
theorem B39296987 : Blo 1570983 39296987 := bstep (se 1 (by rfl) ⟨29472740, by rfl⟩ : syracuseStep 39296987 = 58945481) B58945481
theorem B57378131 : Blo 1570983 57378131 := bstep (se 1 (by rfl) ⟨43033598, by rfl⟩ : syracuseStep 57378131 = 86067197) B86067197
theorem B57337247 : Blo 1570983 57337247 := bstep (se 1 (by rfl) ⟨43002935, by rfl⟩ : syracuseStep 57337247 = 86005871) B86005871
theorem B25840367 : Blo 1570983 25840367 := bstep (se 1 (by rfl) ⟨19380275, by rfl⟩ : syracuseStep 25840367 = 38760551) B38760551
theorem B89586971 : Blo 1570983 89586971 := bstep (se 1 (by rfl) ⟨67190228, by rfl⟩ : syracuseStep 89586971 = 134380457) B134380457
theorem B26197991 : Blo 1570983 26197991 := bstep (se 1 (by rfl) ⟨19648493, by rfl⟩ : syracuseStep 26197991 = 39296987) B39296987
theorem B38224831 : Blo 1570983 38224831 := bstep (se 1 (by rfl) ⟨28668623, by rfl⟩ : syracuseStep 38224831 = 57337247) B57337247
theorem B38252087 : Blo 1570983 38252087 := bstep (se 1 (by rfl) ⟨28689065, by rfl⟩ : syracuseStep 38252087 = 57378131) B57378131
theorem B59724647 : Blo 1570983 59724647 := bstep (se 1 (by rfl) ⟨44793485, by rfl⟩ : syracuseStep 59724647 = 89586971) B89586971
theorem B17226911 : Blo 1570983 17226911 := bstep (se 1 (by rfl) ⟨12920183, by rfl⟩ : syracuseStep 17226911 = 25840367) B25840367
theorem B17465327 : Blo 1570983 17465327 := bstep (se 1 (by rfl) ⟨13098995, by rfl⟩ : syracuseStep 17465327 = 26197991) B26197991
theorem B11643551 : Blo 1570983 11643551 := bstep (se 1 (by rfl) ⟨8732663, by rfl⟩ : syracuseStep 11643551 = 17465327) B17465327
theorem B39816431 : Blo 1570983 39816431 := bstep (se 1 (by rfl) ⟨29862323, by rfl⟩ : syracuseStep 39816431 = 59724647) B59724647
theorem B50966441 : Blo 1570983 50966441 := bstep (se 2 (by rfl) ⟨19112415, by rfl⟩ : syracuseStep 50966441 = 38224831) B38224831
theorem B11484607 : Blo 1570983 11484607 := bstep (se 1 (by rfl) ⟨8613455, by rfl⟩ : syracuseStep 11484607 = 17226911) B17226911
theorem B25501391 : Blo 1570983 25501391 := bstep (se 1 (by rfl) ⟨19126043, by rfl⟩ : syracuseStep 25501391 = 38252087) B38252087
theorem B15312809 : Blo 1570983 15312809 := bstep (se 2 (by rfl) ⟨5742303, by rfl⟩ : syracuseStep 15312809 = 11484607) B11484607
theorem B26544287 : Blo 1570983 26544287 := bstep (se 1 (by rfl) ⟨19908215, by rfl⟩ : syracuseStep 26544287 = 39816431) B39816431
theorem B17000927 : Blo 1570983 17000927 := bstep (se 1 (by rfl) ⟨12750695, by rfl⟩ : syracuseStep 17000927 = 25501391) B25501391
theorem B33977627 : Blo 1570983 33977627 := bstep (se 1 (by rfl) ⟨25483220, by rfl⟩ : syracuseStep 33977627 = 50966441) B50966441
theorem B124197877 : Blo 1570983 124197877 := bstep (se 5 (by rfl) ⟨5821775, by rfl⟩ : syracuseStep 124197877 = 11643551) B11643551
theorem B22651751 : Blo 1570983 22651751 := bstep (se 1 (by rfl) ⟨16988813, by rfl⟩ : syracuseStep 22651751 = 33977627) B33977627
theorem B10208539 : Blo 1570983 10208539 := bstep (se 1 (by rfl) ⟨7656404, by rfl⟩ : syracuseStep 10208539 = 15312809) B15312809
theorem B17696191 : Blo 1570983 17696191 := bstep (se 1 (by rfl) ⟨13272143, by rfl⟩ : syracuseStep 17696191 = 26544287) B26544287
theorem B165597169 : Blo 1570983 165597169 := bstep (se 2 (by rfl) ⟨62098938, by rfl⟩ : syracuseStep 165597169 = 124197877) B124197877
theorem B11333951 : Blo 1570983 11333951 := bstep (se 1 (by rfl) ⟨8500463, by rfl⟩ : syracuseStep 11333951 = 17000927) B17000927
theorem B23594921 : Blo 1570983 23594921 := bstep (se 2 (by rfl) ⟨8848095, by rfl⟩ : syracuseStep 23594921 = 17696191) B17696191
theorem B7555967 : Blo 1570983 7555967 := bstep (se 1 (by rfl) ⟨5666975, by rfl⟩ : syracuseStep 7555967 = 11333951) B11333951
theorem B15101167 : Blo 1570983 15101167 := bstep (se 1 (by rfl) ⟨11325875, by rfl⟩ : syracuseStep 15101167 = 22651751) B22651751
theorem B13611385 : Blo 1570983 13611385 := bstep (se 2 (by rfl) ⟨5104269, by rfl⟩ : syracuseStep 13611385 = 10208539) B10208539
theorem B220796225 : Blo 1570983 220796225 := bstep (se 2 (by rfl) ⟨82798584, by rfl⟩ : syracuseStep 220796225 = 165597169) B165597169
theorem B15729947 : Blo 1570983 15729947 := bstep (se 1 (by rfl) ⟨11797460, by rfl⟩ : syracuseStep 15729947 = 23594921) B23594921
theorem B147197483 : Blo 1570983 147197483 := bstep (se 1 (by rfl) ⟨110398112, by rfl⟩ : syracuseStep 147197483 = 220796225) B220796225
theorem B72594053 : Blo 1570983 72594053 := bstep (se 4 (by rfl) ⟨6805692, by rfl⟩ : syracuseStep 72594053 = 13611385) B13611385
theorem B20134889 : Blo 1570983 20134889 := bstep (se 2 (by rfl) ⟨7550583, by rfl⟩ : syracuseStep 20134889 = 15101167) B15101167
theorem B5037311 : Blo 1570983 5037311 := bstep (se 1 (by rfl) ⟨3777983, by rfl⟩ : syracuseStep 5037311 = 7555967) B7555967
theorem B10486631 : Blo 1570983 10486631 := bstep (se 1 (by rfl) ⟨7864973, by rfl⟩ : syracuseStep 10486631 = 15729947) B15729947
theorem B13423259 : Blo 1570983 13423259 := bstep (se 1 (by rfl) ⟨10067444, by rfl⟩ : syracuseStep 13423259 = 20134889) B20134889
theorem B48396035 : Blo 1570983 48396035 := bstep (se 1 (by rfl) ⟨36297026, by rfl⟩ : syracuseStep 48396035 = 72594053) B72594053
theorem B3358207 : Blo 1570983 3358207 := bstep (se 1 (by rfl) ⟨2518655, by rfl⟩ : syracuseStep 3358207 = 5037311) B5037311
theorem B98131655 : Blo 1570983 98131655 := bstep (se 1 (by rfl) ⟨73598741, by rfl⟩ : syracuseStep 98131655 = 147197483) B147197483
theorem B8948839 : Blo 1570983 8948839 := bstep (se 1 (by rfl) ⟨6711629, by rfl⟩ : syracuseStep 8948839 = 13423259) B13423259
theorem B32264023 : Blo 1570983 32264023 := bstep (se 1 (by rfl) ⟨24198017, by rfl⟩ : syracuseStep 32264023 = 48396035) B48396035
theorem B4477609 : Blo 1570983 4477609 := bstep (se 2 (by rfl) ⟨1679103, by rfl⟩ : syracuseStep 4477609 = 3358207) B3358207
theorem B27964349 : Blo 1570983 27964349 := bstep (se 3 (by rfl) ⟨5243315, by rfl⟩ : syracuseStep 27964349 = 10486631) B10486631
theorem B65421103 : Blo 1570983 65421103 := bstep (se 1 (by rfl) ⟨49065827, by rfl⟩ : syracuseStep 65421103 = 98131655) B98131655
theorem B43018697 : Blo 1570983 43018697 := bstep (se 2 (by rfl) ⟨16132011, by rfl⟩ : syracuseStep 43018697 = 32264023) B32264023
theorem B11931785 : Blo 1570983 11931785 := bstep (se 2 (by rfl) ⟨4474419, by rfl⟩ : syracuseStep 11931785 = 8948839) B8948839
theorem B18642899 : Blo 1570983 18642899 := bstep (se 1 (by rfl) ⟨13982174, by rfl⟩ : syracuseStep 18642899 = 27964349) B27964349
theorem B5970145 : Blo 1570983 5970145 := bstep (se 2 (by rfl) ⟨2238804, by rfl⟩ : syracuseStep 5970145 = 4477609) B4477609
theorem B87228137 : Blo 1570983 87228137 := bstep (se 2 (by rfl) ⟨32710551, by rfl⟩ : syracuseStep 87228137 = 65421103) B65421103
theorem B7954523 : Blo 1570983 7954523 := bstep (se 1 (by rfl) ⟨5965892, by rfl⟩ : syracuseStep 7954523 = 11931785) B11931785
theorem B12428599 : Blo 1570983 12428599 := bstep (se 1 (by rfl) ⟨9321449, by rfl⟩ : syracuseStep 12428599 = 18642899) B18642899
theorem B58152091 : Blo 1570983 58152091 := bstep (se 1 (by rfl) ⟨43614068, by rfl⟩ : syracuseStep 58152091 = 87228137) B87228137
theorem B7960193 : Blo 1570983 7960193 := bstep (se 2 (by rfl) ⟨2985072, by rfl⟩ : syracuseStep 7960193 = 5970145) B5970145
theorem B28679131 : Blo 1570983 28679131 := bstep (se 1 (by rfl) ⟨21509348, by rfl⟩ : syracuseStep 28679131 = 43018697) B43018697
theorem B5303015 : Blo 1570983 5303015 := bstep (se 1 (by rfl) ⟨3977261, by rfl⟩ : syracuseStep 5303015 = 7954523) B7954523
theorem B5306795 : Blo 1570983 5306795 := bstep (se 1 (by rfl) ⟨3980096, by rfl⟩ : syracuseStep 5306795 = 7960193) B7960193
theorem B38238841 : Blo 1570983 38238841 := bstep (se 2 (by rfl) ⟨14339565, by rfl⟩ : syracuseStep 38238841 = 28679131) B28679131
theorem B77536121 : Blo 1570983 77536121 := bstep (se 2 (by rfl) ⟨29076045, by rfl⟩ : syracuseStep 77536121 = 58152091) B58152091
theorem B16571465 : Blo 1570983 16571465 := bstep (se 2 (by rfl) ⟨6214299, by rfl⟩ : syracuseStep 16571465 = 12428599) B12428599
theorem B3535343 : Blo 1570983 3535343 := bstep (se 1 (by rfl) ⟨2651507, by rfl⟩ : syracuseStep 3535343 = 5303015) B5303015
theorem B11047643 : Blo 1570983 11047643 := bstep (se 1 (by rfl) ⟨8285732, by rfl⟩ : syracuseStep 11047643 = 16571465) B16571465
theorem B206762989 : Blo 1570983 206762989 := bstep (se 3 (by rfl) ⟨38768060, by rfl⟩ : syracuseStep 206762989 = 77536121) B77536121
theorem B50985121 : Blo 1570983 50985121 := bstep (se 2 (by rfl) ⟨19119420, by rfl⟩ : syracuseStep 50985121 = 38238841) B38238841
theorem B3537863 : Blo 1570983 3537863 := bstep (se 1 (by rfl) ⟨2653397, by rfl⟩ : syracuseStep 3537863 = 5306795) B5306795
theorem B7365095 : Blo 1570983 7365095 := bstep (se 1 (by rfl) ⟨5523821, by rfl⟩ : syracuseStep 7365095 = 11047643) B11047643
theorem B67980161 : Blo 1570983 67980161 := bstep (se 2 (by rfl) ⟨25492560, by rfl⟩ : syracuseStep 67980161 = 50985121) B50985121
theorem B2356895 : Blo 1570983 2356895 := bstep (se 1 (by rfl) ⟨1767671, by rfl⟩ : syracuseStep 2356895 = 3535343) B3535343
theorem B275683985 : Blo 1570983 275683985 := bstep (se 2 (by rfl) ⟨103381494, by rfl⟩ : syracuseStep 275683985 = 206762989) B206762989
theorem B2358575 : Blo 1570983 2358575 := bstep (se 1 (by rfl) ⟨1768931, by rfl⟩ : syracuseStep 2358575 = 3537863) B3537863
theorem B183789323 : Blo 1570983 183789323 := bstep (se 1 (by rfl) ⟨137841992, by rfl⟩ : syracuseStep 183789323 = 275683985) B275683985
theorem B45320107 : Blo 1570983 45320107 := bstep (se 1 (by rfl) ⟨33990080, by rfl⟩ : syracuseStep 45320107 = 67980161) B67980161
theorem B4910063 : Blo 1570983 4910063 := bstep (se 1 (by rfl) ⟨3682547, by rfl⟩ : syracuseStep 4910063 = 7365095) B7365095
theorem B1571263 : Blo 1570983 1571263 := bstep (se 1 (by rfl) ⟨1178447, by rfl⟩ : syracuseStep 1571263 = 2356895) B2356895
theorem B1572383 : Blo 1570983 1572383 := bstep (se 1 (by rfl) ⟨1179287, by rfl⟩ : syracuseStep 1572383 = 2358575) B2358575
theorem B60426809 : Blo 1570983 60426809 := bstep (se 2 (by rfl) ⟨22660053, by rfl⟩ : syracuseStep 60426809 = 45320107) B45320107
theorem B13093501 : Blo 1570983 13093501 := bstep (se 3 (by rfl) ⟨2455031, by rfl⟩ : syracuseStep 13093501 = 4910063) B4910063
theorem B122526215 : Blo 1570983 122526215 := bstep (se 1 (by rfl) ⟨91894661, by rfl⟩ : syracuseStep 122526215 = 183789323) B183789323
theorem B17458001 : Blo 1570983 17458001 := bstep (se 2 (by rfl) ⟨6546750, by rfl⟩ : syracuseStep 17458001 = 13093501) B13093501
theorem B81684143 : Blo 1570983 81684143 := bstep (se 1 (by rfl) ⟨61263107, by rfl⟩ : syracuseStep 81684143 = 122526215) B122526215
theorem B40284539 : Blo 1570983 40284539 := bstep (se 1 (by rfl) ⟨30213404, by rfl⟩ : syracuseStep 40284539 = 60426809) B60426809
theorem B26856359 : Blo 1570983 26856359 := bstep (se 1 (by rfl) ⟨20142269, by rfl⟩ : syracuseStep 26856359 = 40284539) B40284539
theorem B54456095 : Blo 1570983 54456095 := bstep (se 1 (by rfl) ⟨40842071, by rfl⟩ : syracuseStep 54456095 = 81684143) B81684143
theorem B11638667 : Blo 1570983 11638667 := bstep (se 1 (by rfl) ⟨8729000, by rfl⟩ : syracuseStep 11638667 = 17458001) B17458001
theorem B7759111 : Blo 1570983 7759111 := bstep (se 1 (by rfl) ⟨5819333, by rfl⟩ : syracuseStep 7759111 = 11638667) B11638667
theorem B17904239 : Blo 1570983 17904239 := bstep (se 1 (by rfl) ⟨13428179, by rfl⟩ : syracuseStep 17904239 = 26856359) B26856359
theorem B145216253 : Blo 1570983 145216253 := bstep (se 3 (by rfl) ⟨27228047, by rfl⟩ : syracuseStep 145216253 = 54456095) B54456095
theorem B11936159 : Blo 1570983 11936159 := bstep (se 1 (by rfl) ⟨8952119, by rfl⟩ : syracuseStep 11936159 = 17904239) B17904239
theorem B96810835 : Blo 1570983 96810835 := bstep (se 1 (by rfl) ⟨72608126, by rfl⟩ : syracuseStep 96810835 = 145216253) B145216253
theorem B10345481 : Blo 1570983 10345481 := bstep (se 2 (by rfl) ⟨3879555, by rfl⟩ : syracuseStep 10345481 = 7759111) B7759111
theorem B7957439 : Blo 1570983 7957439 := bstep (se 1 (by rfl) ⟨5968079, by rfl⟩ : syracuseStep 7957439 = 11936159) B11936159
theorem B6896987 : Blo 1570983 6896987 := bstep (se 1 (by rfl) ⟨5172740, by rfl⟩ : syracuseStep 6896987 = 10345481) B10345481
theorem B129081113 : Blo 1570983 129081113 := bstep (se 2 (by rfl) ⟨48405417, by rfl⟩ : syracuseStep 129081113 = 96810835) B96810835
theorem B4597991 : Blo 1570983 4597991 := bstep (se 1 (by rfl) ⟨3448493, by rfl⟩ : syracuseStep 4597991 = 6896987) B6896987
theorem B5304959 : Blo 1570983 5304959 := bstep (se 1 (by rfl) ⟨3978719, by rfl⟩ : syracuseStep 5304959 = 7957439) B7957439
theorem B86054075 : Blo 1570983 86054075 := bstep (se 1 (by rfl) ⟨64540556, by rfl⟩ : syracuseStep 86054075 = 129081113) B129081113
theorem B57369383 : Blo 1570983 57369383 := bstep (se 1 (by rfl) ⟨43027037, by rfl⟩ : syracuseStep 57369383 = 86054075) B86054075
theorem B3065327 : Blo 1570983 3065327 := bstep (se 1 (by rfl) ⟨2298995, by rfl⟩ : syracuseStep 3065327 = 4597991) B4597991
theorem B3536639 : Blo 1570983 3536639 := bstep (se 1 (by rfl) ⟨2652479, by rfl⟩ : syracuseStep 3536639 = 5304959) B5304959
theorem B32696821 : Blo 1570983 32696821 := bstep (se 5 (by rfl) ⟨1532663, by rfl⟩ : syracuseStep 32696821 = 3065327) B3065327
theorem B38246255 : Blo 1570983 38246255 := bstep (se 1 (by rfl) ⟨28684691, by rfl⟩ : syracuseStep 38246255 = 57369383) B57369383
theorem B2357759 : Blo 1570983 2357759 := bstep (se 1 (by rfl) ⟨1768319, by rfl⟩ : syracuseStep 2357759 = 3536639) B3536639
theorem B25497503 : Blo 1570983 25497503 := bstep (se 1 (by rfl) ⟨19123127, by rfl⟩ : syracuseStep 25497503 = 38246255) B38246255
theorem B43595761 : Blo 1570983 43595761 := bstep (se 2 (by rfl) ⟨16348410, by rfl⟩ : syracuseStep 43595761 = 32696821) B32696821
theorem B1571839 : Blo 1570983 1571839 := bstep (se 1 (by rfl) ⟨1178879, by rfl⟩ : syracuseStep 1571839 = 2357759) B2357759
theorem B58127681 : Blo 1570983 58127681 := bstep (se 2 (by rfl) ⟨21797880, by rfl⟩ : syracuseStep 58127681 = 43595761) B43595761
theorem B16998335 : Blo 1570983 16998335 := bstep (se 1 (by rfl) ⟨12748751, by rfl⟩ : syracuseStep 16998335 = 25497503) B25497503
theorem B11332223 : Blo 1570983 11332223 := bstep (se 1 (by rfl) ⟨8499167, by rfl⟩ : syracuseStep 11332223 = 16998335) B16998335
theorem B38751787 : Blo 1570983 38751787 := bstep (se 1 (by rfl) ⟨29063840, by rfl⟩ : syracuseStep 38751787 = 58127681) B58127681
theorem B7554815 : Blo 1570983 7554815 := bstep (se 1 (by rfl) ⟨5666111, by rfl⟩ : syracuseStep 7554815 = 11332223) B11332223
theorem B51669049 : Blo 1570983 51669049 := bstep (se 2 (by rfl) ⟨19375893, by rfl⟩ : syracuseStep 51669049 = 38751787) B38751787
theorem B68892065 : Blo 1570983 68892065 := bstep (se 2 (by rfl) ⟨25834524, by rfl⟩ : syracuseStep 68892065 = 51669049) B51669049
theorem B5036543 : Blo 1570983 5036543 := bstep (se 1 (by rfl) ⟨3777407, by rfl⟩ : syracuseStep 5036543 = 7554815) B7554815
theorem B45928043 : Blo 1570983 45928043 := bstep (se 1 (by rfl) ⟨34446032, by rfl⟩ : syracuseStep 45928043 = 68892065) B68892065
theorem B3357695 : Blo 1570983 3357695 := bstep (se 1 (by rfl) ⟨2518271, by rfl⟩ : syracuseStep 3357695 = 5036543) B5036543
theorem B2238463 : Blo 1570983 2238463 := bstep (se 1 (by rfl) ⟨1678847, by rfl⟩ : syracuseStep 2238463 = 3357695) B3357695
theorem B30618695 : Blo 1570983 30618695 := bstep (se 1 (by rfl) ⟨22964021, by rfl⟩ : syracuseStep 30618695 = 45928043) B45928043
theorem B81649853 : Blo 1570983 81649853 := bstep (se 3 (by rfl) ⟨15309347, by rfl⟩ : syracuseStep 81649853 = 30618695) B30618695
theorem B2984617 : Blo 1570983 2984617 := bstep (se 2 (by rfl) ⟨1119231, by rfl⟩ : syracuseStep 2984617 = 2238463) B2238463
theorem B54433235 : Blo 1570983 54433235 := bstep (se 1 (by rfl) ⟨40824926, by rfl⟩ : syracuseStep 54433235 = 81649853) B81649853
theorem B3979489 : Blo 1570983 3979489 := bstep (se 2 (by rfl) ⟨1492308, by rfl⟩ : syracuseStep 3979489 = 2984617) B2984617
theorem B5305985 : Blo 1570983 5305985 := bstep (se 2 (by rfl) ⟨1989744, by rfl⟩ : syracuseStep 5305985 = 3979489) B3979489
theorem B36288823 : Blo 1570983 36288823 := bstep (se 1 (by rfl) ⟨27216617, by rfl⟩ : syracuseStep 36288823 = 54433235) B54433235
theorem B48385097 : Blo 1570983 48385097 := bstep (se 2 (by rfl) ⟨18144411, by rfl⟩ : syracuseStep 48385097 = 36288823) B36288823
theorem B3537323 : Blo 1570983 3537323 := bstep (se 1 (by rfl) ⟨2652992, by rfl⟩ : syracuseStep 3537323 = 5305985) B5305985
theorem B32256731 : Blo 1570983 32256731 := bstep (se 1 (by rfl) ⟨24192548, by rfl⟩ : syracuseStep 32256731 = 48385097) B48385097
theorem B2358215 : Blo 1570983 2358215 := bstep (se 1 (by rfl) ⟨1768661, by rfl⟩ : syracuseStep 2358215 = 3537323) B3537323
theorem B21504487 : Blo 1570983 21504487 := bstep (se 1 (by rfl) ⟨16128365, by rfl⟩ : syracuseStep 21504487 = 32256731) B32256731
theorem B1572143 : Blo 1570983 1572143 := bstep (se 1 (by rfl) ⟨1179107, by rfl⟩ : syracuseStep 1572143 = 2358215) B2358215
theorem B28672649 : Blo 1570983 28672649 := bstep (se 2 (by rfl) ⟨10752243, by rfl⟩ : syracuseStep 28672649 = 21504487) B21504487
theorem B19115099 : Blo 1570983 19115099 := bstep (se 1 (by rfl) ⟨14336324, by rfl⟩ : syracuseStep 19115099 = 28672649) B28672649
theorem B12743399 : Blo 1570983 12743399 := bstep (se 1 (by rfl) ⟨9557549, by rfl⟩ : syracuseStep 12743399 = 19115099) B19115099
theorem B8495599 : Blo 1570983 8495599 := bstep (se 1 (by rfl) ⟨6371699, by rfl⟩ : syracuseStep 8495599 = 12743399) B12743399
theorem B11327465 : Blo 1570983 11327465 := bstep (se 2 (by rfl) ⟨4247799, by rfl⟩ : syracuseStep 11327465 = 8495599) B8495599
theorem B7551643 : Blo 1570983 7551643 := bstep (se 1 (by rfl) ⟨5663732, by rfl⟩ : syracuseStep 7551643 = 11327465) B11327465
theorem B10068857 : Blo 1570983 10068857 := bstep (se 2 (by rfl) ⟨3775821, by rfl⟩ : syracuseStep 10068857 = 7551643) B7551643
theorem B6712571 : Blo 1570983 6712571 := bstep (se 1 (by rfl) ⟨5034428, by rfl⟩ : syracuseStep 6712571 = 10068857) B10068857
theorem B4475047 : Blo 1570983 4475047 := bstep (se 1 (by rfl) ⟨3356285, by rfl⟩ : syracuseStep 4475047 = 6712571) B6712571
theorem B5966729 : Blo 1570983 5966729 := bstep (se 2 (by rfl) ⟨2237523, by rfl⟩ : syracuseStep 5966729 = 4475047) B4475047
theorem B3977819 : Blo 1570983 3977819 := bstep (se 1 (by rfl) ⟨2983364, by rfl⟩ : syracuseStep 3977819 = 5966729) B5966729
theorem B2651879 : Blo 1570983 2651879 := bstep (se 1 (by rfl) ⟨1988909, by rfl⟩ : syracuseStep 2651879 = 3977819) B3977819
theorem B1767919 : Blo 1570983 1767919 := bstep (se 1 (by rfl) ⟨1325939, by rfl⟩ : syracuseStep 1767919 = 2651879) B2651879
theorem B2357225 : Blo 1570983 2357225 := bstep (se 2 (by rfl) ⟨883959, by rfl⟩ : syracuseStep 2357225 = 1767919) B1767919
theorem B1571483 : Blo 1570983 1571483 := bstep (se 1 (by rfl) ⟨1178612, by rfl⟩ : syracuseStep 1571483 = 2357225) B2357225

theorem C0 (j : ℕ) (h1 : 392745 ≤ j) (h2 : j ≤ 393120) : Blo 1570983 (4 * j + 3) := by
  interval_cases j
  · exact B1570983
  · exact B1570987
  · exact B1570991
  · exact B1570995
  · exact B1570999
  · exact B1571003
  · exact B1571007
  · exact B1571011
  · exact B1571015
  · exact B1571019
  · exact B1571023
  · exact B1571027
  · exact B1571031
  · exact B1571035
  · exact B1571039
  · exact B1571043
  · exact B1571047
  · exact B1571051
  · exact B1571055
  · exact B1571059
  · exact B1571063
  · exact B1571067
  · exact B1571071
  · exact B1571075
  · exact B1571079
  · exact B1571083
  · exact B1571087
  · exact B1571091
  · exact B1571095
  · exact B1571099
  · exact B1571103
  · exact B1571107
  · exact B1571111
  · exact B1571115
  · exact B1571119
  · exact B1571123
  · exact B1571127
  · exact B1571131
  · exact B1571135
  · exact B1571139
  · exact B1571143
  · exact B1571147
  · exact B1571151
  · exact B1571155
  · exact B1571159
  · exact B1571163
  · exact B1571167
  · exact B1571171
  · exact B1571175
  · exact B1571179
  · exact B1571183
  · exact B1571187
  · exact B1571191
  · exact B1571195
  · exact B1571199
  · exact B1571203
  · exact B1571207
  · exact B1571211
  · exact B1571215
  · exact B1571219
  · exact B1571223
  · exact B1571227
  · exact B1571231
  · exact B1571235
  · exact B1571239
  · exact B1571243
  · exact B1571247
  · exact B1571251
  · exact B1571255
  · exact B1571259
  · exact B1571263
  · exact B1571267
  · exact B1571271
  · exact B1571275
  · exact B1571279
  · exact B1571283
  · exact B1571287
  · exact B1571291
  · exact B1571295
  · exact B1571299
  · exact B1571303
  · exact B1571307
  · exact B1571311
  · exact B1571315
  · exact B1571319
  · exact B1571323
  · exact B1571327
  · exact B1571331
  · exact B1571335
  · exact B1571339
  · exact B1571343
  · exact B1571347
  · exact B1571351
  · exact B1571355
  · exact B1571359
  · exact B1571363
  · exact B1571367
  · exact B1571371
  · exact B1571375
  · exact B1571379
  · exact B1571383
  · exact B1571387
  · exact B1571391
  · exact B1571395
  · exact B1571399
  · exact B1571403
  · exact B1571407
  · exact B1571411
  · exact B1571415
  · exact B1571419
  · exact B1571423
  · exact B1571427
  · exact B1571431
  · exact B1571435
  · exact B1571439
  · exact B1571443
  · exact B1571447
  · exact B1571451
  · exact B1571455
  · exact B1571459
  · exact B1571463
  · exact B1571467
  · exact B1571471
  · exact B1571475
  · exact B1571479
  · exact B1571483
  · exact B1571487
  · exact B1571491
  · exact B1571495
  · exact B1571499
  · exact B1571503
  · exact B1571507
  · exact B1571511
  · exact B1571515
  · exact B1571519
  · exact B1571523
  · exact B1571527
  · exact B1571531
  · exact B1571535
  · exact B1571539
  · exact B1571543
  · exact B1571547
  · exact B1571551
  · exact B1571555
  · exact B1571559
  · exact B1571563
  · exact B1571567
  · exact B1571571
  · exact B1571575
  · exact B1571579
  · exact B1571583
  · exact B1571587
  · exact B1571591
  · exact B1571595
  · exact B1571599
  · exact B1571603
  · exact B1571607
  · exact B1571611
  · exact B1571615
  · exact B1571619
  · exact B1571623
  · exact B1571627
  · exact B1571631
  · exact B1571635
  · exact B1571639
  · exact B1571643
  · exact B1571647
  · exact B1571651
  · exact B1571655
  · exact B1571659
  · exact B1571663
  · exact B1571667
  · exact B1571671
  · exact B1571675
  · exact B1571679
  · exact B1571683
  · exact B1571687
  · exact B1571691
  · exact B1571695
  · exact B1571699
  · exact B1571703
  · exact B1571707
  · exact B1571711
  · exact B1571715
  · exact B1571719
  · exact B1571723
  · exact B1571727
  · exact B1571731
  · exact B1571735
  · exact B1571739
  · exact B1571743
  · exact B1571747
  · exact B1571751
  · exact B1571755
  · exact B1571759
  · exact B1571763
  · exact B1571767
  · exact B1571771
  · exact B1571775
  · exact B1571779
  · exact B1571783
  · exact B1571787
  · exact B1571791
  · exact B1571795
  · exact B1571799
  · exact B1571803
  · exact B1571807
  · exact B1571811
  · exact B1571815
  · exact B1571819
  · exact B1571823
  · exact B1571827
  · exact B1571831
  · exact B1571835
  · exact B1571839
  · exact B1571843
  · exact B1571847
  · exact B1571851
  · exact B1571855
  · exact B1571859
  · exact B1571863
  · exact B1571867
  · exact B1571871
  · exact B1571875
  · exact B1571879
  · exact B1571883
  · exact B1571887
  · exact B1571891
  · exact B1571895
  · exact B1571899
  · exact B1571903
  · exact B1571907
  · exact B1571911
  · exact B1571915
  · exact B1571919
  · exact B1571923
  · exact B1571927
  · exact B1571931
  · exact B1571935
  · exact B1571939
  · exact B1571943
  · exact B1571947
  · exact B1571951
  · exact B1571955
  · exact B1571959
  · exact B1571963
  · exact B1571967
  · exact B1571971
  · exact B1571975
  · exact B1571979
  · exact B1571983
  · exact B1571987
  · exact B1571991
  · exact B1571995
  · exact B1571999
  · exact B1572003
  · exact B1572007
  · exact B1572011
  · exact B1572015
  · exact B1572019
  · exact B1572023
  · exact B1572027
  · exact B1572031
  · exact B1572035
  · exact B1572039
  · exact B1572043
  · exact B1572047
  · exact B1572051
  · exact B1572055
  · exact B1572059
  · exact B1572063
  · exact B1572067
  · exact B1572071
  · exact B1572075
  · exact B1572079
  · exact B1572083
  · exact B1572087
  · exact B1572091
  · exact B1572095
  · exact B1572099
  · exact B1572103
  · exact B1572107
  · exact B1572111
  · exact B1572115
  · exact B1572119
  · exact B1572123
  · exact B1572127
  · exact B1572131
  · exact B1572135
  · exact B1572139
  · exact B1572143
  · exact B1572147
  · exact B1572151
  · exact B1572155
  · exact B1572159
  · exact B1572163
  · exact B1572167
  · exact B1572171
  · exact B1572175
  · exact B1572179
  · exact B1572183
  · exact B1572187
  · exact B1572191
  · exact B1572195
  · exact B1572199
  · exact B1572203
  · exact B1572207
  · exact B1572211
  · exact B1572215
  · exact B1572219
  · exact B1572223
  · exact B1572227
  · exact B1572231
  · exact B1572235
  · exact B1572239
  · exact B1572243
  · exact B1572247
  · exact B1572251
  · exact B1572255
  · exact B1572259
  · exact B1572263
  · exact B1572267
  · exact B1572271
  · exact B1572275
  · exact B1572279
  · exact B1572283
  · exact B1572287
  · exact B1572291
  · exact B1572295
  · exact B1572299
  · exact B1572303
  · exact B1572307
  · exact B1572311
  · exact B1572315
  · exact B1572319
  · exact B1572323
  · exact B1572327
  · exact B1572331
  · exact B1572335
  · exact B1572339
  · exact B1572343
  · exact B1572347
  · exact B1572351
  · exact B1572355
  · exact B1572359
  · exact B1572363
  · exact B1572367
  · exact B1572371
  · exact B1572375
  · exact B1572379
  · exact B1572383
  · exact B1572387
  · exact B1572391
  · exact B1572395
  · exact B1572399
  · exact B1572403
  · exact B1572407
  · exact B1572411
  · exact B1572415
  · exact B1572419
  · exact B1572423
  · exact B1572427
  · exact B1572431
  · exact B1572435
  · exact B1572439
  · exact B1572443
  · exact B1572447
  · exact B1572451
  · exact B1572455
  · exact B1572459
  · exact B1572463
  · exact B1572467
  · exact B1572471
  · exact B1572475
  · exact B1572479
  · exact B1572483

theorem solution (m : ℕ) (hlo : 1570983 ≤ m) (hhi : m ≤ 1572483) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 392745 ≤ j := by omega
    have hj2 : j ≤ 393120 := by omega
    have hb : Blo 1570983 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
