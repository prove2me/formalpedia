-- Prove2me | solution 1 for syracuse_descends_range_1297967_1299967
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:12:26.214653+00:00
-- url     : https://prove2.me/submissions/2a6718cd-cfab-49bf-bf47-4c57e62682fd

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


theorem B2465797 : Blo 1297967 2465797 := bbase (se 4 (by rfl) ⟨231168, by rfl⟩ : syracuseStep 2465797 = 462337) (by norm_num)
theorem B2924549 : Blo 1297967 2924549 := bbase (se 4 (by rfl) ⟨274176, by rfl⟩ : syracuseStep 2924549 = 548353) (by norm_num)
theorem B1949717 : Blo 1297967 1949717 := bbase (se 6 (by rfl) ⟨45696, by rfl⟩ : syracuseStep 1949717 = 91393) (by norm_num)
theorem B1949741 : Blo 1297967 1949741 := bbase (se 3 (by rfl) ⟨365576, by rfl⟩ : syracuseStep 1949741 = 731153) (by norm_num)
theorem B2080837 : Blo 1297967 2080837 := bbase (se 4 (by rfl) ⟨195078, by rfl⟩ : syracuseStep 2080837 = 390157) (by norm_num)
theorem B1949765 : Blo 1297967 1949765 := bbase (se 4 (by rfl) ⟨182790, by rfl⟩ : syracuseStep 1949765 = 365581) (by norm_num)
theorem B2924621 : Blo 1297967 2924621 := bbase (se 3 (by rfl) ⟨548366, by rfl⟩ : syracuseStep 2924621 = 1096733) (by norm_num)
theorem B1949789 : Blo 1297967 1949789 := bbase (se 3 (by rfl) ⟨365585, by rfl⟩ : syracuseStep 1949789 = 731171) (by norm_num)
theorem B1949813 : Blo 1297967 1949813 := bbase (se 5 (by rfl) ⟨91397, by rfl⟩ : syracuseStep 1949813 = 182795) (by norm_num)
theorem B1949837 : Blo 1297967 1949837 := bbase (se 3 (by rfl) ⟨365594, by rfl⟩ : syracuseStep 1949837 = 731189) (by norm_num)
theorem B2924693 : Blo 1297967 2924693 := bbase (se 6 (by rfl) ⟨68547, by rfl⟩ : syracuseStep 2924693 = 137095) (by norm_num)
theorem B1876117 : Blo 1297967 1876117 := bbase (se 6 (by rfl) ⟨43971, by rfl⟩ : syracuseStep 1876117 = 87943) (by norm_num)
theorem B2465957 : Blo 1297967 2465957 := bbase (se 4 (by rfl) ⟨231183, by rfl⟩ : syracuseStep 2465957 = 462367) (by norm_num)
theorem B1949861 : Blo 1297967 1949861 := bbase (se 4 (by rfl) ⟨182799, by rfl⟩ : syracuseStep 1949861 = 365599) (by norm_num)
theorem B1949885 : Blo 1297967 1949885 := bbase (se 3 (by rfl) ⟨365603, by rfl⟩ : syracuseStep 1949885 = 731207) (by norm_num)
theorem B6004949 : Blo 1297967 6004949 := bbase (se 7 (by rfl) ⟨70370, by rfl⟩ : syracuseStep 6004949 = 140741) (by norm_num)
theorem B1949909 : Blo 1297967 1949909 := bbase (se 7 (by rfl) ⟨22850, by rfl⟩ : syracuseStep 1949909 = 45701) (by norm_num)
theorem B2924765 : Blo 1297967 2924765 := bbase (se 3 (by rfl) ⟨548393, by rfl⟩ : syracuseStep 2924765 = 1096787) (by norm_num)
theorem B1949933 : Blo 1297967 1949933 := bbase (se 3 (by rfl) ⟨365612, by rfl⟩ : syracuseStep 1949933 = 731225) (by norm_num)
theorem B2924837 : Blo 1297967 2924837 := bbase (se 4 (by rfl) ⟨274203, by rfl⟩ : syracuseStep 2924837 = 548407) (by norm_num)
theorem B2466101 : Blo 1297967 2466101 := bbase (se 5 (by rfl) ⟨115598, by rfl⟩ : syracuseStep 2466101 = 231197) (by norm_num)
theorem B2924909 : Blo 1297967 2924909 := bbase (se 3 (by rfl) ⟨548420, by rfl⟩ : syracuseStep 2924909 = 1096841) (by norm_num)
theorem B2810261 : Blo 1297967 2810261 := bbase (se 6 (by rfl) ⟨65865, by rfl⟩ : syracuseStep 2810261 = 131731) (by norm_num)
theorem B4383125 : Blo 1297967 4383125 := bbase (se 6 (by rfl) ⟨102729, by rfl⟩ : syracuseStep 4383125 = 205459) (by norm_num)
theorem B6242741 : Blo 1297967 6242741 := bbase (se 5 (by rfl) ⟨292628, by rfl⟩ : syracuseStep 6242741 = 585257) (by norm_num)
theorem B3334621 : Blo 1297967 3334621 := bbase (se 3 (by rfl) ⟨625241, by rfl⟩ : syracuseStep 3334621 = 1250483) (by norm_num)
theorem B4940293 : Blo 1297967 4940293 := bbase (se 4 (by rfl) ⟨463152, by rfl⟩ : syracuseStep 4940293 = 926305) (by norm_num)
theorem B3121669 : Blo 1297967 3121669 := bbase (se 4 (by rfl) ⟨292656, by rfl⟩ : syracuseStep 3121669 = 585313) (by norm_num)
theorem B12485173 : Blo 1297967 12485173 := bbase (se 5 (by rfl) ⟨585242, by rfl⟩ : syracuseStep 12485173 = 1170485) (by norm_num)
theorem B2466389 : Blo 1297967 2466389 := bbase (se 8 (by rfl) ⟨14451, by rfl⟩ : syracuseStep 2466389 = 28903) (by norm_num)
theorem B9355925 : Blo 1297967 9355925 := bbase (se 6 (by rfl) ⟨219279, by rfl⟩ : syracuseStep 9355925 = 438559) (by norm_num)
theorem B5546677 : Blo 1297967 5546677 := bbase (se 5 (by rfl) ⟨260000, by rfl⟩ : syracuseStep 5546677 = 520001) (by norm_num)
theorem B2851549 : Blo 1297967 2851549 := bbase (se 3 (by rfl) ⟨534665, by rfl⟩ : syracuseStep 2851549 = 1069331) (by norm_num)
theorem B2466541 : Blo 1297967 2466541 := bbase (se 3 (by rfl) ⟨462476, by rfl⟩ : syracuseStep 2466541 = 924953) (by norm_num)
theorem B10535669 : Blo 1297967 10535669 := bbase (se 5 (by rfl) ⟨493859, by rfl⟩ : syracuseStep 10535669 = 987719) (by norm_num)
theorem B20284181 : Blo 1297967 20284181 := bbase (se 6 (by rfl) ⟨475410, by rfl⟩ : syracuseStep 20284181 = 950821) (by norm_num)
theorem B6578981 : Blo 1297967 6578981 := bbase (se 4 (by rfl) ⟨616779, by rfl⟩ : syracuseStep 6578981 = 1233559) (by norm_num)
theorem B3285805 : Blo 1297967 3285805 := bbase (se 3 (by rfl) ⟨616088, by rfl⟩ : syracuseStep 3285805 = 1232177) (by norm_num)
theorem B4383557 : Blo 1297967 4383557 := bbase (se 4 (by rfl) ⟨410958, by rfl⟩ : syracuseStep 4383557 = 821917) (by norm_num)
theorem B3285917 : Blo 1297967 3285917 := bbase (se 3 (by rfl) ⟨616109, by rfl⟩ : syracuseStep 3285917 = 1232219) (by norm_num)
theorem B8324117 : Blo 1297967 8324117 := bbase (se 6 (by rfl) ⟨195096, by rfl⟩ : syracuseStep 8324117 = 390193) (by norm_num)
theorem B2466845 : Blo 1297967 2466845 := bbase (se 3 (by rfl) ⟨462533, by rfl⟩ : syracuseStep 2466845 = 925067) (by norm_num)
theorem B2081837 : Blo 1297967 2081837 := bbase (se 3 (by rfl) ⟨390344, by rfl⟩ : syracuseStep 2081837 = 780689) (by norm_num)
theorem B7603253 : Blo 1297967 7603253 := bbase (se 5 (by rfl) ⟨356402, by rfl⟩ : syracuseStep 7603253 = 712805) (by norm_num)
theorem B7398485 : Blo 1297967 7398485 := bbase (se 8 (by rfl) ⟨43350, by rfl⟩ : syracuseStep 7398485 = 86701) (by norm_num)
theorem B37479509 : Blo 1297967 37479509 := bbase (se 8 (by rfl) ⟨219606, by rfl⟩ : syracuseStep 37479509 = 439213) (by norm_num)
theorem B3286109 : Blo 1297967 3286109 := bbase (se 3 (by rfl) ⟨616145, by rfl⟩ : syracuseStep 3286109 = 1232291) (by norm_num)
theorem B6661237 : Blo 1297967 6661237 := bbase (se 5 (by rfl) ⟨312245, by rfl⟩ : syracuseStep 6661237 = 624491) (by norm_num)
theorem B9864341 : Blo 1297967 9864341 := bbase (se 6 (by rfl) ⟨231195, by rfl⟩ : syracuseStep 9864341 = 462391) (by norm_num)
theorem B3122333 : Blo 1297967 3122333 := bbase (se 3 (by rfl) ⟨585437, by rfl⟩ : syracuseStep 3122333 = 1170875) (by norm_num)
theorem B2081965 : Blo 1297967 2081965 := bbase (se 3 (by rfl) ⟨390368, by rfl⟩ : syracuseStep 2081965 = 780737) (by norm_num)
theorem B6571205 : Blo 1297967 6571205 := bbase (se 4 (by rfl) ⟨616050, by rfl⟩ : syracuseStep 6571205 = 1232101) (by norm_num)
theorem B4383989 : Blo 1297967 4383989 := bbase (se 5 (by rfl) ⟨205499, by rfl⟩ : syracuseStep 4383989 = 410999) (by norm_num)
theorem B4162853 : Blo 1297967 4162853 := bbase (se 4 (by rfl) ⟨390267, by rfl⟩ : syracuseStep 4162853 = 780535) (by norm_num)
theorem B2221357 : Blo 1297967 2221357 := bbase (se 3 (by rfl) ⟨416504, by rfl⟩ : syracuseStep 2221357 = 833009) (by norm_num)
theorem B4441477 : Blo 1297967 4441477 := bbase (se 4 (by rfl) ⟨416388, by rfl⟩ : syracuseStep 4441477 = 832777) (by norm_num)
theorem B8881589 : Blo 1297967 8881589 := bbase (se 5 (by rfl) ⟨416324, by rfl⟩ : syracuseStep 8881589 = 832649) (by norm_num)
theorem B3286453 : Blo 1297967 3286453 := bbase (se 5 (by rfl) ⟨154052, by rfl⟩ : syracuseStep 3286453 = 308105) (by norm_num)
theorem B3122621 : Blo 1297967 3122621 := bbase (se 3 (by rfl) ⟨585491, by rfl⟩ : syracuseStep 3122621 = 1170983) (by norm_num)
theorem B1689121 : Blo 1297967 1689121 := bbase (se 2 (by rfl) ⟨633420, by rfl⟩ : syracuseStep 1689121 = 1266841) (by norm_num)
theorem B3286565 : Blo 1297967 3286565 := bbase (se 4 (by rfl) ⟨308115, by rfl⟩ : syracuseStep 3286565 = 616231) (by norm_num)
theorem B1754669 : Blo 1297967 1754669 := bbase (se 3 (by rfl) ⟨329000, by rfl⟩ : syracuseStep 1754669 = 658001) (by norm_num)
theorem B11093557 : Blo 1297967 11093557 := bbase (se 5 (by rfl) ⟨520010, by rfl⟩ : syracuseStep 11093557 = 1040021) (by norm_num)
theorem B9856565 : Blo 1297967 9856565 := bbase (se 5 (by rfl) ⟨462026, by rfl⟩ : syracuseStep 9856565 = 924053) (by norm_num)
theorem B5064245 : Blo 1297967 5064245 := bbase (se 5 (by rfl) ⟨237386, by rfl⟩ : syracuseStep 5064245 = 474773) (by norm_num)
theorem B3696293 : Blo 1297967 3696293 := bbase (se 4 (by rfl) ⟨346527, by rfl⟩ : syracuseStep 3696293 = 693055) (by norm_num)
theorem B4384421 : Blo 1297967 4384421 := bbase (se 4 (by rfl) ⟨411039, by rfl⟩ : syracuseStep 4384421 = 822079) (by norm_num)
theorem B3286757 : Blo 1297967 3286757 := bbase (se 4 (by rfl) ⟨308133, by rfl⟩ : syracuseStep 3286757 = 616267) (by norm_num)
theorem B2467597 : Blo 1297967 2467597 := bbase (se 3 (by rfl) ⟨462674, by rfl⟩ : syracuseStep 2467597 = 925349) (by norm_num)
theorem B1386281 : Blo 1297967 1386281 := bbase (se 2 (by rfl) ⟨519855, by rfl⟩ : syracuseStep 1386281 = 1039711) (by norm_num)
theorem B13330261 : Blo 1297967 13330261 := bbase (se 9 (by rfl) ⟨39053, by rfl⟩ : syracuseStep 13330261 = 78107) (by norm_num)
theorem B1386353 : Blo 1297967 1386353 := bbase (se 2 (by rfl) ⟨519882, by rfl⟩ : syracuseStep 1386353 = 1039765) (by norm_num)
theorem B4933493 : Blo 1297967 4933493 := bbase (se 5 (by rfl) ⟨231257, by rfl⟩ : syracuseStep 4933493 = 462515) (by norm_num)
theorem B2467741 : Blo 1297967 2467741 := bbase (se 3 (by rfl) ⟨462701, by rfl⟩ : syracuseStep 2467741 = 925403) (by norm_num)
theorem B1460245 : Blo 1297967 1460245 := bbase (se 6 (by rfl) ⟨34224, by rfl⟩ : syracuseStep 1460245 = 68449) (by norm_num)
theorem B1386541 : Blo 1297967 1386541 := bbase (se 3 (by rfl) ⟨259976, by rfl⟩ : syracuseStep 1386541 = 519953) (by norm_num)
theorem B6580277 : Blo 1297967 6580277 := bbase (se 5 (by rfl) ⟨308450, by rfl⟩ : syracuseStep 6580277 = 616901) (by norm_num)
theorem B1460281 : Blo 1297967 1460281 := bbase (se 2 (by rfl) ⟨547605, by rfl⟩ : syracuseStep 1460281 = 1095211) (by norm_num)
theorem B3287101 : Blo 1297967 3287101 := bbase (se 3 (by rfl) ⟨616331, by rfl⟩ : syracuseStep 3287101 = 1232663) (by norm_num)
theorem B2467901 : Blo 1297967 2467901 := bbase (se 3 (by rfl) ⟨462731, by rfl⟩ : syracuseStep 2467901 = 925463) (by norm_num)
theorem B4384853 : Blo 1297967 4384853 := bbase (se 8 (by rfl) ⟨25692, by rfl⟩ : syracuseStep 4384853 = 51385) (by norm_num)
theorem B1460317 : Blo 1297967 1460317 := bbase (se 3 (by rfl) ⟨273809, by rfl⟩ : syracuseStep 1460317 = 547619) (by norm_num)
theorem B1460353 : Blo 1297967 1460353 := bbase (se 2 (by rfl) ⟨547632, by rfl⟩ : syracuseStep 1460353 = 1095265) (by norm_num)
theorem B4933781 : Blo 1297967 4933781 := bbase (se 6 (by rfl) ⟨115635, by rfl⟩ : syracuseStep 4933781 = 231271) (by norm_num)
theorem B1927325 : Blo 1297967 1927325 := bbase (se 3 (by rfl) ⟨361373, by rfl⟩ : syracuseStep 1927325 = 722747) (by norm_num)
theorem B1460389 : Blo 1297967 1460389 := bbase (se 4 (by rfl) ⟨136911, by rfl⟩ : syracuseStep 1460389 = 273823) (by norm_num)
theorem B3287213 : Blo 1297967 3287213 := bbase (se 3 (by rfl) ⟨616352, by rfl⟩ : syracuseStep 3287213 = 1232705) (by norm_num)
theorem B1460425 : Blo 1297967 1460425 := bbase (se 2 (by rfl) ⟨547659, by rfl⟩ : syracuseStep 1460425 = 1095319) (by norm_num)
theorem B1386725 : Blo 1297967 1386725 := bbase (se 4 (by rfl) ⟨130005, by rfl⟩ : syracuseStep 1386725 = 260011) (by norm_num)
theorem B1460461 : Blo 1297967 1460461 := bbase (se 3 (by rfl) ⟨273836, by rfl⟩ : syracuseStep 1460461 = 547673) (by norm_num)
theorem B1976557 : Blo 1297967 1976557 := bbase (se 3 (by rfl) ⟨370604, by rfl⟩ : syracuseStep 1976557 = 741209) (by norm_num)
theorem B5335301 : Blo 1297967 5335301 := bbase (se 4 (by rfl) ⟨500184, by rfl⟩ : syracuseStep 5335301 = 1000369) (by norm_num)
theorem B1665293 : Blo 1297967 1665293 := bbase (se 3 (by rfl) ⟨312242, by rfl⟩ : syracuseStep 1665293 = 624485) (by norm_num)
theorem B1460497 : Blo 1297967 1460497 := bbase (se 2 (by rfl) ⟨547686, by rfl⟩ : syracuseStep 1460497 = 1095373) (by norm_num)
theorem B1460533 : Blo 1297967 1460533 := bbase (se 5 (by rfl) ⟨68462, by rfl⟩ : syracuseStep 1460533 = 136925) (by norm_num)
theorem B3696965 : Blo 1297967 3696965 := bbase (se 4 (by rfl) ⟨346590, by rfl⟩ : syracuseStep 3696965 = 693181) (by norm_num)
theorem B1460569 : Blo 1297967 1460569 := bbase (se 2 (by rfl) ⟨547713, by rfl⟩ : syracuseStep 1460569 = 1095427) (by norm_num)
theorem B5925221 : Blo 1297967 5925221 := bbase (se 4 (by rfl) ⟨555489, by rfl⟩ : syracuseStep 5925221 = 1110979) (by norm_num)
theorem B3287405 : Blo 1297967 3287405 := bbase (se 3 (by rfl) ⟨616388, by rfl⟩ : syracuseStep 3287405 = 1232777) (by norm_num)
theorem B1460605 : Blo 1297967 1460605 := bbase (se 3 (by rfl) ⟨273863, by rfl⟩ : syracuseStep 1460605 = 547727) (by norm_num)
theorem B1460641 : Blo 1297967 1460641 := bbase (se 2 (by rfl) ⟨547740, by rfl⟩ : syracuseStep 1460641 = 1095481) (by norm_num)
theorem B1460677 : Blo 1297967 1460677 := bbase (se 4 (by rfl) ⟨136938, by rfl⟩ : syracuseStep 1460677 = 273877) (by norm_num)
theorem B6572501 : Blo 1297967 6572501 := bbase (se 7 (by rfl) ⟨77021, by rfl⟩ : syracuseStep 6572501 = 154043) (by norm_num)
theorem B1460713 : Blo 1297967 1460713 := bbase (se 2 (by rfl) ⟨547767, by rfl⟩ : syracuseStep 1460713 = 1095535) (by norm_num)
theorem B4385285 : Blo 1297967 4385285 := bbase (se 4 (by rfl) ⟨411120, by rfl⟩ : syracuseStep 4385285 = 822241) (by norm_num)
theorem B1460749 : Blo 1297967 1460749 := bbase (se 3 (by rfl) ⟨273890, by rfl⟩ : syracuseStep 1460749 = 547781) (by norm_num)
theorem B2107949 : Blo 1297967 2107949 := bbase (se 3 (by rfl) ⟨395240, by rfl⟩ : syracuseStep 2107949 = 790481) (by norm_num)
theorem B1460785 : Blo 1297967 1460785 := bbase (se 2 (by rfl) ⟨547794, by rfl⟩ : syracuseStep 1460785 = 1095589) (by norm_num)
theorem B1804853 : Blo 1297967 1804853 := bbase (se 5 (by rfl) ⟨84602, by rfl⟩ : syracuseStep 1804853 = 169205) (by norm_num)
theorem B2812477 : Blo 1297967 2812477 := bbase (se 3 (by rfl) ⟨527339, by rfl⟩ : syracuseStep 2812477 = 1054679) (by norm_num)
theorem B6244933 : Blo 1297967 6244933 := bbase (se 4 (by rfl) ⟨585462, by rfl⟩ : syracuseStep 6244933 = 1170925) (by norm_num)
theorem B1460821 : Blo 1297967 1460821 := bbase (se 8 (by rfl) ⟨8559, by rfl⟩ : syracuseStep 1460821 = 17119) (by norm_num)
theorem B1460857 : Blo 1297967 1460857 := bbase (se 2 (by rfl) ⟨547821, by rfl⟩ : syracuseStep 1460857 = 1095643) (by norm_num)
theorem B1460893 : Blo 1297967 1460893 := bbase (se 3 (by rfl) ⟨273917, by rfl⟩ : syracuseStep 1460893 = 547835) (by norm_num)
theorem B1460929 : Blo 1297967 1460929 := bbase (se 2 (by rfl) ⟨547848, by rfl⟩ : syracuseStep 1460929 = 1095697) (by norm_num)
theorem B3287749 : Blo 1297967 3287749 := bbase (se 4 (by rfl) ⟨308226, by rfl⟩ : syracuseStep 3287749 = 616453) (by norm_num)
theorem B1780429 : Blo 1297967 1780429 := bbase (se 3 (by rfl) ⟨333830, by rfl⟩ : syracuseStep 1780429 = 667661) (by norm_num)
theorem B1624801 : Blo 1297967 1624801 := bbase (se 2 (by rfl) ⟨609300, by rfl⟩ : syracuseStep 1624801 = 1218601) (by norm_num)
theorem B1460965 : Blo 1297967 1460965 := bbase (se 4 (by rfl) ⟨136965, by rfl⟩ : syracuseStep 1460965 = 273931) (by norm_num)
theorem B3697397 : Blo 1297967 3697397 := bbase (se 5 (by rfl) ⟨173315, by rfl⟩ : syracuseStep 3697397 = 346631) (by norm_num)
theorem B1461001 : Blo 1297967 1461001 := bbase (se 2 (by rfl) ⟨547875, by rfl⟩ : syracuseStep 1461001 = 1095751) (by norm_num)
theorem B1461037 : Blo 1297967 1461037 := bbase (se 3 (by rfl) ⟨273944, by rfl⟩ : syracuseStep 1461037 = 547889) (by norm_num)
theorem B3287861 : Blo 1297967 3287861 := bbase (se 5 (by rfl) ⟨154118, by rfl⟩ : syracuseStep 3287861 = 308237) (by norm_num)
theorem B1461073 : Blo 1297967 1461073 := bbase (se 2 (by rfl) ⟨547902, by rfl⟩ : syracuseStep 1461073 = 1095805) (by norm_num)
theorem B1461109 : Blo 1297967 1461109 := bbase (se 5 (by rfl) ⟨68489, by rfl⟩ : syracuseStep 1461109 = 136979) (by norm_num)
theorem B1461145 : Blo 1297967 1461145 := bbase (se 2 (by rfl) ⟨547929, by rfl⟩ : syracuseStep 1461145 = 1095859) (by norm_num)
theorem B1665965 : Blo 1297967 1665965 := bbase (se 3 (by rfl) ⟨312368, by rfl⟩ : syracuseStep 1665965 = 624737) (by norm_num)
theorem B4385717 : Blo 1297967 4385717 := bbase (se 5 (by rfl) ⟨205580, by rfl⟩ : syracuseStep 4385717 = 411161) (by norm_num)
theorem B1461181 : Blo 1297967 1461181 := bbase (se 3 (by rfl) ⟨273971, by rfl⟩ : syracuseStep 1461181 = 547943) (by norm_num)
theorem B1387477 : Blo 1297967 1387477 := bbase (se 7 (by rfl) ⟨16259, by rfl⟩ : syracuseStep 1387477 = 32519) (by norm_num)
theorem B1461217 : Blo 1297967 1461217 := bbase (se 2 (by rfl) ⟨547956, by rfl⟩ : syracuseStep 1461217 = 1095913) (by norm_num)
theorem B3288053 : Blo 1297967 3288053 := bbase (se 5 (by rfl) ⟨154127, by rfl⟩ : syracuseStep 3288053 = 308255) (by norm_num)
theorem B2190341 : Blo 1297967 2190341 := bbase (se 4 (by rfl) ⟨205344, by rfl⟩ : syracuseStep 2190341 = 410689) (by norm_num)
theorem B1461253 : Blo 1297967 1461253 := bbase (se 4 (by rfl) ⟨136992, by rfl⟩ : syracuseStep 1461253 = 273985) (by norm_num)
theorem B1666073 : Blo 1297967 1666073 := bbase (se 2 (by rfl) ⟨624777, by rfl⟩ : syracuseStep 1666073 = 1249555) (by norm_num)
theorem B1387549 : Blo 1297967 1387549 := bbase (se 3 (by rfl) ⟨260165, by rfl⟩ : syracuseStep 1387549 = 520331) (by norm_num)
theorem B1461289 : Blo 1297967 1461289 := bbase (se 2 (by rfl) ⟨547983, by rfl⟩ : syracuseStep 1461289 = 1095967) (by norm_num)
theorem B2632781 : Blo 1297967 2632781 := bbase (se 3 (by rfl) ⟨493646, by rfl⟩ : syracuseStep 2632781 = 987293) (by norm_num)
theorem B1461325 : Blo 1297967 1461325 := bbase (se 3 (by rfl) ⟨273998, by rfl⟩ : syracuseStep 1461325 = 547997) (by norm_num)
theorem B1461361 : Blo 1297967 1461361 := bbase (se 2 (by rfl) ⟨548010, by rfl⟩ : syracuseStep 1461361 = 1096021) (by norm_num)
theorem B1756285 : Blo 1297967 1756285 := bbase (se 3 (by rfl) ⟨329303, by rfl⟩ : syracuseStep 1756285 = 658607) (by norm_num)
theorem B2190469 : Blo 1297967 2190469 := bbase (se 4 (by rfl) ⟨205356, by rfl⟩ : syracuseStep 2190469 = 410713) (by norm_num)
theorem B1461397 : Blo 1297967 1461397 := bbase (se 6 (by rfl) ⟨34251, by rfl⟩ : syracuseStep 1461397 = 68503) (by norm_num)
theorem B1461433 : Blo 1297967 1461433 := bbase (se 2 (by rfl) ⟨548037, by rfl⟩ : syracuseStep 1461433 = 1096075) (by norm_num)
theorem B1387729 : Blo 1297967 1387729 := bbase (se 2 (by rfl) ⟨520398, by rfl⟩ : syracuseStep 1387729 = 1040797) (by norm_num)
theorem B2190557 : Blo 1297967 2190557 := bbase (se 3 (by rfl) ⟨410729, by rfl⟩ : syracuseStep 2190557 = 821459) (by norm_num)
theorem B1559773 : Blo 1297967 1559773 := bbase (se 3 (by rfl) ⟨292457, by rfl⟩ : syracuseStep 1559773 = 584915) (by norm_num)
theorem B1461469 : Blo 1297967 1461469 := bbase (se 3 (by rfl) ⟨274025, by rfl⟩ : syracuseStep 1461469 = 548051) (by norm_num)
theorem B1559801 : Blo 1297967 1559801 := bbase (se 2 (by rfl) ⟨584925, by rfl⟩ : syracuseStep 1559801 = 1169851) (by norm_num)
theorem B1461505 : Blo 1297967 1461505 := bbase (se 2 (by rfl) ⟨548064, by rfl⟩ : syracuseStep 1461505 = 1096129) (by norm_num)
theorem B2772245 : Blo 1297967 2772245 := bbase (se 6 (by rfl) ⟨64974, by rfl⟩ : syracuseStep 2772245 = 129949) (by norm_num)
theorem B1461541 : Blo 1297967 1461541 := bbase (se 4 (by rfl) ⟨137019, by rfl⟩ : syracuseStep 1461541 = 274039) (by norm_num)
theorem B4934965 : Blo 1297967 4934965 := bbase (se 5 (by rfl) ⟨231326, by rfl⟩ : syracuseStep 4934965 = 462653) (by norm_num)
theorem B1461577 : Blo 1297967 1461577 := bbase (se 2 (by rfl) ⟨548091, by rfl⟩ : syracuseStep 1461577 = 1096183) (by norm_num)
theorem B3288397 : Blo 1297967 3288397 := bbase (se 3 (by rfl) ⟨616574, by rfl⟩ : syracuseStep 3288397 = 1233149) (by norm_num)
theorem B2190685 : Blo 1297967 2190685 := bbase (se 3 (by rfl) ⟨410753, by rfl⟩ : syracuseStep 2190685 = 821507) (by norm_num)
theorem B4386149 : Blo 1297967 4386149 := bbase (se 4 (by rfl) ⟨411201, by rfl⟩ : syracuseStep 4386149 = 822403) (by norm_num)
theorem B1461613 : Blo 1297967 1461613 := bbase (se 3 (by rfl) ⟨274052, by rfl⟩ : syracuseStep 1461613 = 548105) (by norm_num)
theorem B1461649 : Blo 1297967 1461649 := bbase (se 2 (by rfl) ⟨548118, by rfl⟩ : syracuseStep 1461649 = 1096237) (by norm_num)
theorem B2960813 : Blo 1297967 2960813 := bbase (se 3 (by rfl) ⟨555152, by rfl⟩ : syracuseStep 2960813 = 1110305) (by norm_num)
theorem B2190773 : Blo 1297967 2190773 := bbase (se 5 (by rfl) ⟨102692, by rfl⟩ : syracuseStep 2190773 = 205385) (by norm_num)
theorem B1559989 : Blo 1297967 1559989 := bbase (se 5 (by rfl) ⟨73124, by rfl⟩ : syracuseStep 1559989 = 146249) (by norm_num)
theorem B1461685 : Blo 1297967 1461685 := bbase (se 5 (by rfl) ⟨68516, by rfl⟩ : syracuseStep 1461685 = 137033) (by norm_num)
theorem B3288509 : Blo 1297967 3288509 := bbase (se 3 (by rfl) ⟨616595, by rfl⟩ : syracuseStep 3288509 = 1233191) (by norm_num)
theorem B1461721 : Blo 1297967 1461721 := bbase (se 2 (by rfl) ⟨548145, by rfl⟩ : syracuseStep 1461721 = 1096291) (by norm_num)
theorem B3698149 : Blo 1297967 3698149 := bbase (se 4 (by rfl) ⟨346701, by rfl⟩ : syracuseStep 3698149 = 693403) (by norm_num)
theorem B11095541 : Blo 1297967 11095541 := bbase (se 5 (by rfl) ⟨520103, by rfl⟩ : syracuseStep 11095541 = 1040207) (by norm_num)
theorem B1461757 : Blo 1297967 1461757 := bbase (se 3 (by rfl) ⟨274079, by rfl⟩ : syracuseStep 1461757 = 548159) (by norm_num)
theorem B1461793 : Blo 1297967 1461793 := bbase (se 2 (by rfl) ⟨548172, by rfl⟩ : syracuseStep 1461793 = 1096345) (by norm_num)
theorem B1560109 : Blo 1297967 1560109 := bbase (se 3 (by rfl) ⟨292520, by rfl⟩ : syracuseStep 1560109 = 585041) (by norm_num)
theorem B2190901 : Blo 1297967 2190901 := bbase (se 5 (by rfl) ⟨102698, by rfl⟩ : syracuseStep 2190901 = 205397) (by norm_num)
theorem B3509813 : Blo 1297967 3509813 := bbase (se 5 (by rfl) ⟨164522, by rfl⟩ : syracuseStep 3509813 = 329045) (by norm_num)
theorem B2633285 : Blo 1297967 2633285 := bbase (se 4 (by rfl) ⟨246870, by rfl⟩ : syracuseStep 2633285 = 493741) (by norm_num)
theorem B1461829 : Blo 1297967 1461829 := bbase (se 4 (by rfl) ⟨137046, by rfl⟩ : syracuseStep 1461829 = 274093) (by norm_num)
theorem B4935269 : Blo 1297967 4935269 := bbase (se 4 (by rfl) ⟨462681, by rfl⟩ : syracuseStep 4935269 = 925363) (by norm_num)
theorem B1461865 : Blo 1297967 1461865 := bbase (se 2 (by rfl) ⟨548199, by rfl⟩ : syracuseStep 1461865 = 1096399) (by norm_num)
theorem B3288701 : Blo 1297967 3288701 := bbase (se 3 (by rfl) ⟨616631, by rfl⟩ : syracuseStep 3288701 = 1233263) (by norm_num)
theorem B2190989 : Blo 1297967 2190989 := bbase (se 3 (by rfl) ⟨410810, by rfl⟩ : syracuseStep 2190989 = 821621) (by norm_num)
theorem B1461901 : Blo 1297967 1461901 := bbase (se 3 (by rfl) ⟨274106, by rfl⟩ : syracuseStep 1461901 = 548213) (by norm_num)
theorem B1388173 : Blo 1297967 1388173 := bbase (se 3 (by rfl) ⟨260282, by rfl⟩ : syracuseStep 1388173 = 520565) (by norm_num)
theorem B1461937 : Blo 1297967 1461937 := bbase (se 2 (by rfl) ⟨548226, by rfl⟩ : syracuseStep 1461937 = 1096453) (by norm_num)
theorem B1461973 : Blo 1297967 1461973 := bbase (se 7 (by rfl) ⟨17132, by rfl⟩ : syracuseStep 1461973 = 34265) (by norm_num)
theorem B6573797 : Blo 1297967 6573797 := bbase (se 4 (by rfl) ⟨616293, by rfl⟩ : syracuseStep 6573797 = 1232587) (by norm_num)
theorem B1462009 : Blo 1297967 1462009 := bbase (se 2 (by rfl) ⟨548253, by rfl⟩ : syracuseStep 1462009 = 1096507) (by norm_num)
theorem B2191117 : Blo 1297967 2191117 := bbase (se 3 (by rfl) ⟨410834, by rfl⟩ : syracuseStep 2191117 = 821669) (by norm_num)
theorem B4386581 : Blo 1297967 4386581 := bbase (se 6 (by rfl) ⟨102810, by rfl⟩ : syracuseStep 4386581 = 205621) (by norm_num)
theorem B1462045 : Blo 1297967 1462045 := bbase (se 3 (by rfl) ⟨274133, by rfl⟩ : syracuseStep 1462045 = 548267) (by norm_num)
theorem B3952421 : Blo 1297967 3952421 := bbase (se 4 (by rfl) ⟨370539, by rfl⟩ : syracuseStep 3952421 = 741079) (by norm_num)
theorem B1462081 : Blo 1297967 1462081 := bbase (se 2 (by rfl) ⟨548280, by rfl⟩ : syracuseStep 1462081 = 1096561) (by norm_num)
theorem B2191205 : Blo 1297967 2191205 := bbase (se 4 (by rfl) ⟨205425, by rfl⟩ : syracuseStep 2191205 = 410851) (by norm_num)
theorem B1462117 : Blo 1297967 1462117 := bbase (se 4 (by rfl) ⟨137073, by rfl⟩ : syracuseStep 1462117 = 274147) (by norm_num)
theorem B1462153 : Blo 1297967 1462153 := bbase (se 2 (by rfl) ⟨548307, by rfl⟩ : syracuseStep 1462153 = 1096615) (by norm_num)
theorem B1462189 : Blo 1297967 1462189 := bbase (se 3 (by rfl) ⟨274160, by rfl⟩ : syracuseStep 1462189 = 548321) (by norm_num)
theorem B1462225 : Blo 1297967 1462225 := bbase (se 2 (by rfl) ⟨548334, by rfl⟩ : syracuseStep 1462225 = 1096669) (by norm_num)
theorem B3289045 : Blo 1297967 3289045 := bbase (se 7 (by rfl) ⟨38543, by rfl⟩ : syracuseStep 3289045 = 77087) (by norm_num)
theorem B2002909 : Blo 1297967 2002909 := bbase (se 3 (by rfl) ⟨375545, by rfl⟩ : syracuseStep 2002909 = 751091) (by norm_num)
theorem B2191333 : Blo 1297967 2191333 := bbase (se 4 (by rfl) ⟨205437, by rfl⟩ : syracuseStep 2191333 = 410875) (by norm_num)
theorem B1462261 : Blo 1297967 1462261 := bbase (se 5 (by rfl) ⟨68543, by rfl⟩ : syracuseStep 1462261 = 137087) (by norm_num)
theorem B2920445 : Blo 1297967 2920445 := bbase (se 3 (by rfl) ⟨547583, by rfl⟩ : syracuseStep 2920445 = 1095167) (by norm_num)
theorem B1462297 : Blo 1297967 1462297 := bbase (se 2 (by rfl) ⟨548361, by rfl⟩ : syracuseStep 1462297 = 1096723) (by norm_num)
theorem B2191421 : Blo 1297967 2191421 := bbase (se 3 (by rfl) ⟨410891, by rfl⟩ : syracuseStep 2191421 = 821783) (by norm_num)
theorem B1462333 : Blo 1297967 1462333 := bbase (se 3 (by rfl) ⟨274187, by rfl⟩ : syracuseStep 1462333 = 548375) (by norm_num)
theorem B2920517 : Blo 1297967 2920517 := bbase (se 4 (by rfl) ⟨273798, by rfl⟩ : syracuseStep 2920517 = 547597) (by norm_num)
theorem B3289157 : Blo 1297967 3289157 := bbase (se 4 (by rfl) ⟨308358, by rfl⟩ : syracuseStep 3289157 = 616717) (by norm_num)
theorem B4681813 : Blo 1297967 4681813 := bbase (se 8 (by rfl) ⟨27432, by rfl⟩ : syracuseStep 4681813 = 54865) (by norm_num)
theorem B1462369 : Blo 1297967 1462369 := bbase (se 2 (by rfl) ⟨548388, by rfl⟩ : syracuseStep 1462369 = 1096777) (by norm_num)
theorem B2773109 : Blo 1297967 2773109 := bbase (se 5 (by rfl) ⟨129989, by rfl⟩ : syracuseStep 2773109 = 259979) (by norm_num)
theorem B1462405 : Blo 1297967 1462405 := bbase (se 4 (by rfl) ⟨137100, by rfl⟩ : syracuseStep 1462405 = 274201) (by norm_num)
theorem B2920589 : Blo 1297967 2920589 := bbase (se 3 (by rfl) ⟨547610, by rfl⟩ : syracuseStep 2920589 = 1095221) (by norm_num)
theorem B1462441 : Blo 1297967 1462441 := bbase (se 2 (by rfl) ⟨548415, by rfl⟩ : syracuseStep 1462441 = 1096831) (by norm_num)
theorem B2191549 : Blo 1297967 2191549 := bbase (se 3 (by rfl) ⟨410915, by rfl⟩ : syracuseStep 2191549 = 821831) (by norm_num)
theorem B4387013 : Blo 1297967 4387013 := bbase (se 4 (by rfl) ⟨411282, by rfl⟩ : syracuseStep 4387013 = 822565) (by norm_num)
theorem B2920661 : Blo 1297967 2920661 := bbase (se 7 (by rfl) ⟨34226, by rfl⟩ : syracuseStep 2920661 = 68453) (by norm_num)
theorem B2773253 : Blo 1297967 2773253 := bbase (se 4 (by rfl) ⟨259992, by rfl⟩ : syracuseStep 2773253 = 519985) (by norm_num)
theorem B3289349 : Blo 1297967 3289349 := bbase (se 4 (by rfl) ⟨308376, by rfl⟩ : syracuseStep 3289349 = 616753) (by norm_num)
theorem B2191637 : Blo 1297967 2191637 := bbase (se 6 (by rfl) ⟨51366, by rfl⟩ : syracuseStep 2191637 = 102733) (by norm_num)
theorem B1642781 : Blo 1297967 1642781 := bbase (se 3 (by rfl) ⟨308021, by rfl⟩ : syracuseStep 1642781 = 616043) (by norm_num)
theorem B2920733 : Blo 1297967 2920733 := bbase (se 3 (by rfl) ⟨547637, by rfl⟩ : syracuseStep 2920733 = 1095275) (by norm_num)
theorem B2109773 : Blo 1297967 2109773 := bbase (se 3 (by rfl) ⟨395582, by rfl⟩ : syracuseStep 2109773 = 791165) (by norm_num)
theorem B1642837 : Blo 1297967 1642837 := bbase (se 10 (by rfl) ⟨2406, by rfl⟩ : syracuseStep 1642837 = 4813) (by norm_num)
theorem B2920805 : Blo 1297967 2920805 := bbase (se 4 (by rfl) ⟨273825, by rfl⟩ : syracuseStep 2920805 = 547651) (by norm_num)
theorem B2191765 : Blo 1297967 2191765 := bbase (se 6 (by rfl) ⟨51369, by rfl⟩ : syracuseStep 2191765 = 102739) (by norm_num)
theorem B2920877 : Blo 1297967 2920877 := bbase (se 3 (by rfl) ⟨547664, by rfl⟩ : syracuseStep 2920877 = 1095329) (by norm_num)
theorem B1642933 : Blo 1297967 1642933 := bbase (se 5 (by rfl) ⟨77012, by rfl⟩ : syracuseStep 1642933 = 154025) (by norm_num)
theorem B5624245 : Blo 1297967 5624245 := bbase (se 5 (by rfl) ⟨263636, by rfl⟩ : syracuseStep 5624245 = 527273) (by norm_num)
theorem B1667525 : Blo 1297967 1667525 := bbase (se 4 (by rfl) ⟨156330, by rfl⟩ : syracuseStep 1667525 = 312661) (by norm_num)
theorem B12489173 : Blo 1297967 12489173 := bbase (se 7 (by rfl) ⟨146357, by rfl⟩ : syracuseStep 12489173 = 292715) (by norm_num)
theorem B2191853 : Blo 1297967 2191853 := bbase (se 3 (by rfl) ⟨410972, by rfl⟩ : syracuseStep 2191853 = 821945) (by norm_num)
theorem B2920949 : Blo 1297967 2920949 := bbase (se 5 (by rfl) ⟨136919, by rfl⟩ : syracuseStep 2920949 = 273839) (by norm_num)
theorem B2961917 : Blo 1297967 2961917 := bbase (se 3 (by rfl) ⟨555359, by rfl⟩ : syracuseStep 2961917 = 1110719) (by norm_num)
theorem B2921021 : Blo 1297967 2921021 := bbase (se 3 (by rfl) ⟨547691, by rfl⟩ : syracuseStep 2921021 = 1095383) (by norm_num)
theorem B3289693 : Blo 1297967 3289693 := bbase (se 3 (by rfl) ⟨616817, by rfl⟩ : syracuseStep 3289693 = 1233635) (by norm_num)
theorem B1643105 : Blo 1297967 1643105 := bbase (se 2 (by rfl) ⟨616164, by rfl⟩ : syracuseStep 1643105 = 1232329) (by norm_num)
theorem B2191981 : Blo 1297967 2191981 := bbase (se 3 (by rfl) ⟨410996, by rfl⟩ : syracuseStep 2191981 = 821993) (by norm_num)
theorem B2921093 : Blo 1297967 2921093 := bbase (se 4 (by rfl) ⟨273852, by rfl⟩ : syracuseStep 2921093 = 547705) (by norm_num)
theorem B1643161 : Blo 1297967 1643161 := bbase (se 2 (by rfl) ⟨616185, by rfl⟩ : syracuseStep 1643161 = 1232371) (by norm_num)
theorem B2372261 : Blo 1297967 2372261 := bbase (se 4 (by rfl) ⟨222399, by rfl⟩ : syracuseStep 2372261 = 444799) (by norm_num)
theorem B2192069 : Blo 1297967 2192069 := bbase (se 4 (by rfl) ⟨205506, by rfl⟩ : syracuseStep 2192069 = 411013) (by norm_num)
theorem B2921165 : Blo 1297967 2921165 := bbase (se 3 (by rfl) ⟨547718, by rfl⟩ : syracuseStep 2921165 = 1095437) (by norm_num)
theorem B3289805 : Blo 1297967 3289805 := bbase (se 3 (by rfl) ⟨616838, by rfl⟩ : syracuseStep 3289805 = 1233677) (by norm_num)
theorem B1643257 : Blo 1297967 1643257 := bbase (se 2 (by rfl) ⟨616221, by rfl⟩ : syracuseStep 1643257 = 1232443) (by norm_num)
theorem B2921237 : Blo 1297967 2921237 := bbase (se 6 (by rfl) ⟨68466, by rfl⟩ : syracuseStep 2921237 = 136933) (by norm_num)
theorem B3511109 : Blo 1297967 3511109 := bbase (se 4 (by rfl) ⟨329166, by rfl⟩ : syracuseStep 3511109 = 658333) (by norm_num)
theorem B2192197 : Blo 1297967 2192197 := bbase (se 4 (by rfl) ⟨205518, by rfl⟩ : syracuseStep 2192197 = 411037) (by norm_num)
theorem B2921309 : Blo 1297967 2921309 := bbase (se 3 (by rfl) ⟨547745, by rfl⟩ : syracuseStep 2921309 = 1095491) (by norm_num)
theorem B3289997 : Blo 1297967 3289997 := bbase (se 3 (by rfl) ⟨616874, by rfl⟩ : syracuseStep 3289997 = 1233749) (by norm_num)
theorem B2192285 : Blo 1297967 2192285 := bbase (se 3 (by rfl) ⟨411053, by rfl⟩ : syracuseStep 2192285 = 822107) (by norm_num)
theorem B2921381 : Blo 1297967 2921381 := bbase (se 4 (by rfl) ⟨273879, by rfl⟩ : syracuseStep 2921381 = 547759) (by norm_num)
theorem B1643429 : Blo 1297967 1643429 := bbase (se 4 (by rfl) ⟨154071, by rfl⟩ : syracuseStep 1643429 = 308143) (by norm_num)
theorem B1643485 : Blo 1297967 1643485 := bbase (se 3 (by rfl) ⟨308153, by rfl⟩ : syracuseStep 1643485 = 616307) (by norm_num)
theorem B2888677 : Blo 1297967 2888677 := bbase (se 4 (by rfl) ⟨270813, by rfl⟩ : syracuseStep 2888677 = 541627) (by norm_num)
theorem B2921453 : Blo 1297967 2921453 := bbase (se 3 (by rfl) ⟨547772, by rfl⟩ : syracuseStep 2921453 = 1095545) (by norm_num)
theorem B2773997 : Blo 1297967 2773997 := bbase (se 3 (by rfl) ⟨520124, by rfl⟩ : syracuseStep 2773997 = 1040249) (by norm_num)
theorem B6575093 : Blo 1297967 6575093 := bbase (se 5 (by rfl) ⟨308207, by rfl⟩ : syracuseStep 6575093 = 616415) (by norm_num)
theorem B2192413 : Blo 1297967 2192413 := bbase (se 3 (by rfl) ⟨411077, by rfl⟩ : syracuseStep 2192413 = 822155) (by norm_num)
theorem B2921525 : Blo 1297967 2921525 := bbase (se 5 (by rfl) ⟨136946, by rfl⟩ : syracuseStep 2921525 = 273893) (by norm_num)
theorem B1643581 : Blo 1297967 1643581 := bbase (se 3 (by rfl) ⟨308171, by rfl⟩ : syracuseStep 1643581 = 616343) (by norm_num)
theorem B1315921 : Blo 1297967 1315921 := bbase (se 2 (by rfl) ⟨493470, by rfl⟩ : syracuseStep 1315921 = 986941) (by norm_num)
theorem B21353557 : Blo 1297967 21353557 := bbase (se 8 (by rfl) ⟨125118, by rfl⟩ : syracuseStep 21353557 = 250237) (by norm_num)
theorem B39998549 : Blo 1297967 39998549 := bbase (se 8 (by rfl) ⟨234366, by rfl⟩ : syracuseStep 39998549 = 468733) (by norm_num)
theorem B1561685 : Blo 1297967 1561685 := bbase (se 8 (by rfl) ⟨9150, by rfl⟩ : syracuseStep 1561685 = 18301) (by norm_num)
theorem B2192501 : Blo 1297967 2192501 := bbase (se 5 (by rfl) ⟨102773, by rfl⟩ : syracuseStep 2192501 = 205547) (by norm_num)
theorem B2921597 : Blo 1297967 2921597 := bbase (se 3 (by rfl) ⟨547799, by rfl⟩ : syracuseStep 2921597 = 1095599) (by norm_num)
theorem B2921669 : Blo 1297967 2921669 := bbase (se 4 (by rfl) ⟨273906, by rfl⟩ : syracuseStep 2921669 = 547813) (by norm_num)
theorem B3290341 : Blo 1297967 3290341 := bbase (se 4 (by rfl) ⟨308469, by rfl⟩ : syracuseStep 3290341 = 616939) (by norm_num)
theorem B1643753 : Blo 1297967 1643753 := bbase (se 2 (by rfl) ⟨616407, by rfl⟩ : syracuseStep 1643753 = 1232815) (by norm_num)
theorem B2192629 : Blo 1297967 2192629 := bbase (se 5 (by rfl) ⟨102779, by rfl⟩ : syracuseStep 2192629 = 205559) (by norm_num)
theorem B2921741 : Blo 1297967 2921741 := bbase (se 3 (by rfl) ⟨547826, by rfl⟩ : syracuseStep 2921741 = 1095653) (by norm_num)
theorem B1643809 : Blo 1297967 1643809 := bbase (se 2 (by rfl) ⟨616428, by rfl⟩ : syracuseStep 1643809 = 1232857) (by norm_num)
theorem B1946957 : Blo 1297967 1946957 := bbase (se 3 (by rfl) ⟨365054, by rfl⟩ : syracuseStep 1946957 = 730109) (by norm_num)
theorem B2192717 : Blo 1297967 2192717 := bbase (se 3 (by rfl) ⟨411134, by rfl⟩ : syracuseStep 2192717 = 822269) (by norm_num)
theorem B2921813 : Blo 1297967 2921813 := bbase (se 14 (by rfl) ⟨267, by rfl⟩ : syracuseStep 2921813 = 535) (by norm_num)
theorem B3290453 : Blo 1297967 3290453 := bbase (se 13 (by rfl) ⟨602, by rfl⟩ : syracuseStep 3290453 = 1205) (by norm_num)
theorem B1946981 : Blo 1297967 1946981 := bbase (se 4 (by rfl) ⟨182529, by rfl⟩ : syracuseStep 1946981 = 365059) (by norm_num)
theorem B1947005 : Blo 1297967 1947005 := bbase (se 3 (by rfl) ⟨365063, by rfl⟩ : syracuseStep 1947005 = 730127) (by norm_num)
theorem B1643905 : Blo 1297967 1643905 := bbase (se 2 (by rfl) ⟨616464, by rfl⟩ : syracuseStep 1643905 = 1232929) (by norm_num)
theorem B1947029 : Blo 1297967 1947029 := bbase (se 6 (by rfl) ⟨45633, by rfl⟩ : syracuseStep 1947029 = 91267) (by norm_num)
theorem B2921885 : Blo 1297967 2921885 := bbase (se 3 (by rfl) ⟨547853, by rfl⟩ : syracuseStep 2921885 = 1095707) (by norm_num)
theorem B1316261 : Blo 1297967 1316261 := bbase (se 4 (by rfl) ⟨123399, by rfl⟩ : syracuseStep 1316261 = 246799) (by norm_num)
theorem B1947053 : Blo 1297967 1947053 := bbase (se 3 (by rfl) ⟨365072, by rfl⟩ : syracuseStep 1947053 = 730145) (by norm_num)
theorem B1947077 : Blo 1297967 1947077 := bbase (se 4 (by rfl) ⟨182538, by rfl⟩ : syracuseStep 1947077 = 365077) (by norm_num)
theorem B2192845 : Blo 1297967 2192845 := bbase (se 3 (by rfl) ⟨411158, by rfl⟩ : syracuseStep 2192845 = 822317) (by norm_num)
theorem B39998933 : Blo 1297967 39998933 := bbase (se 7 (by rfl) ⟨468737, by rfl⟩ : syracuseStep 39998933 = 937475) (by norm_num)
theorem B1947101 : Blo 1297967 1947101 := bbase (se 3 (by rfl) ⟨365081, by rfl⟩ : syracuseStep 1947101 = 730163) (by norm_num)
theorem B2921957 : Blo 1297967 2921957 := bbase (se 4 (by rfl) ⟨273933, by rfl⟩ : syracuseStep 2921957 = 547867) (by norm_num)
theorem B1947125 : Blo 1297967 1947125 := bbase (se 5 (by rfl) ⟨91271, by rfl⟩ : syracuseStep 1947125 = 182543) (by norm_num)
theorem B1947149 : Blo 1297967 1947149 := bbase (se 3 (by rfl) ⟨365090, by rfl⟩ : syracuseStep 1947149 = 730181) (by norm_num)
theorem B1947173 : Blo 1297967 1947173 := bbase (se 4 (by rfl) ⟨182547, by rfl⟩ : syracuseStep 1947173 = 365095) (by norm_num)
theorem B2192933 : Blo 1297967 2192933 := bbase (se 4 (by rfl) ⟨205587, by rfl⟩ : syracuseStep 2192933 = 411175) (by norm_num)
theorem B2922029 : Blo 1297967 2922029 := bbase (se 3 (by rfl) ⟨547880, by rfl⟩ : syracuseStep 2922029 = 1095761) (by norm_num)
theorem B1644077 : Blo 1297967 1644077 := bbase (se 3 (by rfl) ⟨308264, by rfl⟩ : syracuseStep 1644077 = 616529) (by norm_num)
theorem B1947197 : Blo 1297967 1947197 := bbase (se 3 (by rfl) ⟨365099, by rfl⟩ : syracuseStep 1947197 = 730199) (by norm_num)
theorem B5551685 : Blo 1297967 5551685 := bbase (se 4 (by rfl) ⟨520470, by rfl⟩ : syracuseStep 5551685 = 1040941) (by norm_num)
theorem B1947221 : Blo 1297967 1947221 := bbase (se 8 (by rfl) ⟨11409, by rfl⟩ : syracuseStep 1947221 = 22819) (by norm_num)
theorem B1644133 : Blo 1297967 1644133 := bbase (se 4 (by rfl) ⟨154137, by rfl⟩ : syracuseStep 1644133 = 308275) (by norm_num)
theorem B1947245 : Blo 1297967 1947245 := bbase (se 3 (by rfl) ⟨365108, by rfl⟩ : syracuseStep 1947245 = 730217) (by norm_num)
theorem B6239861 : Blo 1297967 6239861 := bbase (se 5 (by rfl) ⟨292493, by rfl⟩ : syracuseStep 6239861 = 584987) (by norm_num)
theorem B2922101 : Blo 1297967 2922101 := bbase (se 5 (by rfl) ⟨136973, by rfl⟩ : syracuseStep 2922101 = 273947) (by norm_num)
theorem B1947269 : Blo 1297967 1947269 := bbase (se 4 (by rfl) ⟨182556, by rfl⟩ : syracuseStep 1947269 = 365113) (by norm_num)
theorem B1947293 : Blo 1297967 1947293 := bbase (se 3 (by rfl) ⟨365117, by rfl⟩ : syracuseStep 1947293 = 730235) (by norm_num)
theorem B2193061 : Blo 1297967 2193061 := bbase (se 4 (by rfl) ⟨205599, by rfl⟩ : syracuseStep 2193061 = 411199) (by norm_num)
theorem B1947317 : Blo 1297967 1947317 := bbase (se 5 (by rfl) ⟨91280, by rfl⟩ : syracuseStep 1947317 = 182561) (by norm_num)
theorem B2922173 : Blo 1297967 2922173 := bbase (se 3 (by rfl) ⟨547907, by rfl⟩ : syracuseStep 2922173 = 1095815) (by norm_num)
theorem B1644229 : Blo 1297967 1644229 := bbase (se 4 (by rfl) ⟨154146, by rfl⟩ : syracuseStep 1644229 = 308293) (by norm_num)
theorem B1947341 : Blo 1297967 1947341 := bbase (se 3 (by rfl) ⟨365126, by rfl⟩ : syracuseStep 1947341 = 730253) (by norm_num)
theorem B2774749 : Blo 1297967 2774749 := bbase (se 3 (by rfl) ⟨520265, by rfl⟩ : syracuseStep 2774749 = 1040531) (by norm_num)
theorem B1947365 : Blo 1297967 1947365 := bbase (se 4 (by rfl) ⟨182565, by rfl⟩ : syracuseStep 1947365 = 365131) (by norm_num)
theorem B1947389 : Blo 1297967 1947389 := bbase (se 3 (by rfl) ⟨365135, by rfl⟩ : syracuseStep 1947389 = 730271) (by norm_num)
theorem B2193149 : Blo 1297967 2193149 := bbase (se 3 (by rfl) ⟨411215, by rfl⟩ : syracuseStep 2193149 = 822431) (by norm_num)
theorem B2922245 : Blo 1297967 2922245 := bbase (se 4 (by rfl) ⟨273960, by rfl⟩ : syracuseStep 2922245 = 547921) (by norm_num)
theorem B1947413 : Blo 1297967 1947413 := bbase (se 6 (by rfl) ⟨45642, by rfl⟩ : syracuseStep 1947413 = 91285) (by norm_num)
theorem B1947437 : Blo 1297967 1947437 := bbase (se 3 (by rfl) ⟨365144, by rfl⟩ : syracuseStep 1947437 = 730289) (by norm_num)
theorem B1947461 : Blo 1297967 1947461 := bbase (se 4 (by rfl) ⟨182574, by rfl⟩ : syracuseStep 1947461 = 365149) (by norm_num)
theorem B2922317 : Blo 1297967 2922317 := bbase (se 3 (by rfl) ⟨547934, by rfl⟩ : syracuseStep 2922317 = 1095869) (by norm_num)
theorem B1947485 : Blo 1297967 1947485 := bbase (se 3 (by rfl) ⟨365153, by rfl⟩ : syracuseStep 1947485 = 730307) (by norm_num)
theorem B5551973 : Blo 1297967 5551973 := bbase (se 4 (by rfl) ⟨520497, by rfl⟩ : syracuseStep 5551973 = 1040995) (by norm_num)
theorem B2774893 : Blo 1297967 2774893 := bbase (se 3 (by rfl) ⟨520292, by rfl⟩ : syracuseStep 2774893 = 1040585) (by norm_num)
theorem B1644401 : Blo 1297967 1644401 := bbase (se 2 (by rfl) ⟨616650, by rfl⟩ : syracuseStep 1644401 = 1233301) (by norm_num)
theorem B1947509 : Blo 1297967 1947509 := bbase (se 5 (by rfl) ⟨91289, by rfl⟩ : syracuseStep 1947509 = 182579) (by norm_num)
theorem B2193277 : Blo 1297967 2193277 := bbase (se 3 (by rfl) ⟨411239, by rfl⟩ : syracuseStep 2193277 = 822479) (by norm_num)
theorem B1947533 : Blo 1297967 1947533 := bbase (se 3 (by rfl) ⟨365162, by rfl⟩ : syracuseStep 1947533 = 730325) (by norm_num)
theorem B2922389 : Blo 1297967 2922389 := bbase (se 6 (by rfl) ⟨68493, by rfl⟩ : syracuseStep 2922389 = 136987) (by norm_num)
theorem B1947557 : Blo 1297967 1947557 := bbase (se 4 (by rfl) ⟨182583, by rfl⟩ : syracuseStep 1947557 = 365167) (by norm_num)
theorem B1644457 : Blo 1297967 1644457 := bbase (se 2 (by rfl) ⟨616671, by rfl⟩ : syracuseStep 1644457 = 1233343) (by norm_num)
theorem B1947581 : Blo 1297967 1947581 := bbase (se 3 (by rfl) ⟨365171, by rfl⟩ : syracuseStep 1947581 = 730343) (by norm_num)
theorem B1947605 : Blo 1297967 1947605 := bbase (se 7 (by rfl) ⟨22823, by rfl⟩ : syracuseStep 1947605 = 45647) (by norm_num)
theorem B2193365 : Blo 1297967 2193365 := bbase (se 7 (by rfl) ⟨25703, by rfl⟩ : syracuseStep 2193365 = 51407) (by norm_num)
theorem B2922461 : Blo 1297967 2922461 := bbase (se 3 (by rfl) ⟨547961, by rfl⟩ : syracuseStep 2922461 = 1095923) (by norm_num)
theorem B1947629 : Blo 1297967 1947629 := bbase (se 3 (by rfl) ⟨365180, by rfl⟩ : syracuseStep 1947629 = 730361) (by norm_num)
theorem B1947653 : Blo 1297967 1947653 := bbase (se 4 (by rfl) ⟨182592, by rfl⟩ : syracuseStep 1947653 = 365185) (by norm_num)
theorem B1644553 : Blo 1297967 1644553 := bbase (se 2 (by rfl) ⟨616707, by rfl⟩ : syracuseStep 1644553 = 1233415) (by norm_num)
theorem B1947677 : Blo 1297967 1947677 := bbase (se 3 (by rfl) ⟨365189, by rfl⟩ : syracuseStep 1947677 = 730379) (by norm_num)
theorem B2922533 : Blo 1297967 2922533 := bbase (se 4 (by rfl) ⟨273987, by rfl⟩ : syracuseStep 2922533 = 547975) (by norm_num)
theorem B1947701 : Blo 1297967 1947701 := bbase (se 5 (by rfl) ⟨91298, by rfl⟩ : syracuseStep 1947701 = 182597) (by norm_num)
theorem B1849405 : Blo 1297967 1849405 := bbase (se 3 (by rfl) ⟨346763, by rfl⟩ : syracuseStep 1849405 = 693527) (by norm_num)
theorem B4929605 : Blo 1297967 4929605 := bbase (se 4 (by rfl) ⟨462150, by rfl⟩ : syracuseStep 4929605 = 924301) (by norm_num)
theorem B1947725 : Blo 1297967 1947725 := bbase (se 3 (by rfl) ⟨365198, by rfl⟩ : syracuseStep 1947725 = 730397) (by norm_num)
theorem B2193493 : Blo 1297967 2193493 := bbase (se 8 (by rfl) ⟨12852, by rfl⟩ : syracuseStep 2193493 = 25705) (by norm_num)
theorem B1947749 : Blo 1297967 1947749 := bbase (se 4 (by rfl) ⟨182601, by rfl⟩ : syracuseStep 1947749 = 365203) (by norm_num)
theorem B2922605 : Blo 1297967 2922605 := bbase (se 3 (by rfl) ⟨547988, by rfl⟩ : syracuseStep 2922605 = 1095977) (by norm_num)
theorem B1947773 : Blo 1297967 1947773 := bbase (se 3 (by rfl) ⟨365207, by rfl⟩ : syracuseStep 1947773 = 730415) (by norm_num)
theorem B1947797 : Blo 1297967 1947797 := bbase (se 6 (by rfl) ⟨45651, by rfl⟩ : syracuseStep 1947797 = 91303) (by norm_num)
theorem B1947821 : Blo 1297967 1947821 := bbase (se 3 (by rfl) ⟨365216, by rfl⟩ : syracuseStep 1947821 = 730433) (by norm_num)
theorem B2193581 : Blo 1297967 2193581 := bbase (se 3 (by rfl) ⟨411296, by rfl⟩ : syracuseStep 2193581 = 822593) (by norm_num)
theorem B2922677 : Blo 1297967 2922677 := bbase (se 5 (by rfl) ⟨137000, by rfl⟩ : syracuseStep 2922677 = 274001) (by norm_num)
theorem B1644725 : Blo 1297967 1644725 := bbase (se 5 (by rfl) ⟨77096, by rfl⟩ : syracuseStep 1644725 = 154193) (by norm_num)
theorem B1947845 : Blo 1297967 1947845 := bbase (se 4 (by rfl) ⟨182610, by rfl⟩ : syracuseStep 1947845 = 365221) (by norm_num)
theorem B1947869 : Blo 1297967 1947869 := bbase (se 3 (by rfl) ⟨365225, by rfl⟩ : syracuseStep 1947869 = 730451) (by norm_num)
theorem B2775269 : Blo 1297967 2775269 := bbase (se 4 (by rfl) ⟨260181, by rfl⟩ : syracuseStep 2775269 = 520363) (by norm_num)
theorem B1644781 : Blo 1297967 1644781 := bbase (se 3 (by rfl) ⟨308396, by rfl⟩ : syracuseStep 1644781 = 616793) (by norm_num)
theorem B1947893 : Blo 1297967 1947893 := bbase (se 5 (by rfl) ⟨91307, by rfl⟩ : syracuseStep 1947893 = 182615) (by norm_num)
theorem B2922749 : Blo 1297967 2922749 := bbase (se 3 (by rfl) ⟨548015, by rfl⟩ : syracuseStep 2922749 = 1096031) (by norm_num)
theorem B6576389 : Blo 1297967 6576389 := bbase (se 4 (by rfl) ⟨616536, by rfl⟩ : syracuseStep 6576389 = 1233073) (by norm_num)
theorem B3700997 : Blo 1297967 3700997 := bbase (se 4 (by rfl) ⟨346968, by rfl⟩ : syracuseStep 3700997 = 693937) (by norm_num)
theorem B1947917 : Blo 1297967 1947917 := bbase (se 3 (by rfl) ⟨365234, by rfl⟩ : syracuseStep 1947917 = 730469) (by norm_num)
theorem B4159765 : Blo 1297967 4159765 := bbase (se 6 (by rfl) ⟨97494, by rfl⟩ : syracuseStep 4159765 = 194989) (by norm_num)
theorem B4380965 : Blo 1297967 4380965 := bbase (se 4 (by rfl) ⟨410715, by rfl⟩ : syracuseStep 4380965 = 821431) (by norm_num)
theorem B1947941 : Blo 1297967 1947941 := bbase (se 4 (by rfl) ⟨182619, by rfl⟩ : syracuseStep 1947941 = 365239) (by norm_num)
theorem B1947965 : Blo 1297967 1947965 := bbase (se 3 (by rfl) ⟨365243, by rfl⟩ : syracuseStep 1947965 = 730487) (by norm_num)
theorem B2922821 : Blo 1297967 2922821 := bbase (se 4 (by rfl) ⟨274014, by rfl⟩ : syracuseStep 2922821 = 548029) (by norm_num)
theorem B1644877 : Blo 1297967 1644877 := bbase (se 3 (by rfl) ⟨308414, by rfl⟩ : syracuseStep 1644877 = 616829) (by norm_num)
theorem B1481041 : Blo 1297967 1481041 := bbase (se 2 (by rfl) ⟨555390, by rfl⟩ : syracuseStep 1481041 = 1110781) (by norm_num)
theorem B4159829 : Blo 1297967 4159829 := bbase (se 10 (by rfl) ⟨6093, by rfl⟩ : syracuseStep 4159829 = 12187) (by norm_num)
theorem B1947989 : Blo 1297967 1947989 := bbase (se 10 (by rfl) ⟨2853, by rfl⟩ : syracuseStep 1947989 = 5707) (by norm_num)
theorem B16644437 : Blo 1297967 16644437 := bbase (se 10 (by rfl) ⟨24381, by rfl⟩ : syracuseStep 16644437 = 48763) (by norm_num)
theorem B4929893 : Blo 1297967 4929893 := bbase (se 4 (by rfl) ⟨462177, by rfl⟩ : syracuseStep 4929893 = 924355) (by norm_num)
theorem B1948013 : Blo 1297967 1948013 := bbase (se 3 (by rfl) ⟨365252, by rfl⟩ : syracuseStep 1948013 = 730505) (by norm_num)
theorem B1948037 : Blo 1297967 1948037 := bbase (se 4 (by rfl) ⟨182628, by rfl⟩ : syracuseStep 1948037 = 365257) (by norm_num)
theorem B2922893 : Blo 1297967 2922893 := bbase (se 3 (by rfl) ⟨548042, by rfl⟩ : syracuseStep 2922893 = 1096085) (by norm_num)
theorem B2464157 : Blo 1297967 2464157 := bbase (se 3 (by rfl) ⟨462029, by rfl⟩ : syracuseStep 2464157 = 924059) (by norm_num)
theorem B1948061 : Blo 1297967 1948061 := bbase (se 3 (by rfl) ⟨365261, by rfl⟩ : syracuseStep 1948061 = 730523) (by norm_num)
theorem B7018933 : Blo 1297967 7018933 := bbase (se 5 (by rfl) ⟨329012, by rfl⟩ : syracuseStep 7018933 = 658025) (by norm_num)
theorem B1948085 : Blo 1297967 1948085 := bbase (se 5 (by rfl) ⟨91316, by rfl⟩ : syracuseStep 1948085 = 182633) (by norm_num)
theorem B1948109 : Blo 1297967 1948109 := bbase (se 3 (by rfl) ⟨365270, by rfl⟩ : syracuseStep 1948109 = 730541) (by norm_num)
theorem B2922965 : Blo 1297967 2922965 := bbase (se 7 (by rfl) ⟨34253, by rfl⟩ : syracuseStep 2922965 = 68507) (by norm_num)
theorem B2079197 : Blo 1297967 2079197 := bbase (se 3 (by rfl) ⟨389849, by rfl⟩ : syracuseStep 2079197 = 779699) (by norm_num)
theorem B1948133 : Blo 1297967 1948133 := bbase (se 4 (by rfl) ⟨182637, by rfl⟩ : syracuseStep 1948133 = 365275) (by norm_num)
theorem B1645049 : Blo 1297967 1645049 := bbase (se 2 (by rfl) ⟨616893, by rfl⟩ : syracuseStep 1645049 = 1233787) (by norm_num)
theorem B1948157 : Blo 1297967 1948157 := bbase (se 3 (by rfl) ⟨365279, by rfl⟩ : syracuseStep 1948157 = 730559) (by norm_num)
theorem B1948181 : Blo 1297967 1948181 := bbase (se 6 (by rfl) ⟨45660, by rfl⟩ : syracuseStep 1948181 = 91321) (by norm_num)
theorem B2923037 : Blo 1297967 2923037 := bbase (se 3 (by rfl) ⟨548069, by rfl⟩ : syracuseStep 2923037 = 1096139) (by norm_num)
theorem B1948205 : Blo 1297967 1948205 := bbase (se 3 (by rfl) ⟨365288, by rfl⟩ : syracuseStep 1948205 = 730577) (by norm_num)
theorem B1317421 : Blo 1297967 1317421 := bbase (se 3 (by rfl) ⟨247016, by rfl⟩ : syracuseStep 1317421 = 494033) (by norm_num)
theorem B1645105 : Blo 1297967 1645105 := bbase (se 2 (by rfl) ⟨616914, by rfl⟩ : syracuseStep 1645105 = 1233829) (by norm_num)
theorem B1948229 : Blo 1297967 1948229 := bbase (se 4 (by rfl) ⟨182646, by rfl⟩ : syracuseStep 1948229 = 365293) (by norm_num)
theorem B2775637 : Blo 1297967 2775637 := bbase (se 8 (by rfl) ⟨16263, by rfl⟩ : syracuseStep 2775637 = 32527) (by norm_num)
theorem B5552725 : Blo 1297967 5552725 := bbase (se 8 (by rfl) ⟨32535, by rfl⟩ : syracuseStep 5552725 = 65071) (by norm_num)
theorem B1948253 : Blo 1297967 1948253 := bbase (se 3 (by rfl) ⟨365297, by rfl⟩ : syracuseStep 1948253 = 730595) (by norm_num)
theorem B2923109 : Blo 1297967 2923109 := bbase (se 4 (by rfl) ⟨274041, by rfl⟩ : syracuseStep 2923109 = 548083) (by norm_num)
theorem B1948277 : Blo 1297967 1948277 := bbase (se 5 (by rfl) ⟨91325, by rfl⟩ : syracuseStep 1948277 = 182651) (by norm_num)
theorem B1948301 : Blo 1297967 1948301 := bbase (se 3 (by rfl) ⟨365306, by rfl⟩ : syracuseStep 1948301 = 730613) (by norm_num)
theorem B1849997 : Blo 1297967 1849997 := bbase (se 3 (by rfl) ⟨346874, by rfl⟩ : syracuseStep 1849997 = 693749) (by norm_num)
theorem B1645201 : Blo 1297967 1645201 := bbase (se 2 (by rfl) ⟨616950, by rfl⟩ : syracuseStep 1645201 = 1233901) (by norm_num)
theorem B2079389 : Blo 1297967 2079389 := bbase (se 3 (by rfl) ⟨389885, by rfl⟩ : syracuseStep 2079389 = 779771) (by norm_num)
theorem B1948325 : Blo 1297967 1948325 := bbase (se 4 (by rfl) ⟨182655, by rfl⟩ : syracuseStep 1948325 = 365311) (by norm_num)
theorem B2923181 : Blo 1297967 2923181 := bbase (se 3 (by rfl) ⟨548096, by rfl⟩ : syracuseStep 2923181 = 1096193) (by norm_num)
theorem B2464445 : Blo 1297967 2464445 := bbase (se 3 (by rfl) ⟨462083, by rfl⟩ : syracuseStep 2464445 = 924167) (by norm_num)
theorem B1948349 : Blo 1297967 1948349 := bbase (se 3 (by rfl) ⟨365315, by rfl⟩ : syracuseStep 1948349 = 730631) (by norm_num)
theorem B4381397 : Blo 1297967 4381397 := bbase (se 7 (by rfl) ⟨51344, by rfl⟩ : syracuseStep 4381397 = 102689) (by norm_num)
theorem B1948373 : Blo 1297967 1948373 := bbase (se 7 (by rfl) ⟨22832, by rfl⟩ : syracuseStep 1948373 = 45665) (by norm_num)
theorem B1850077 : Blo 1297967 1850077 := bbase (se 3 (by rfl) ⟨346889, by rfl⟩ : syracuseStep 1850077 = 693779) (by norm_num)
theorem B1948397 : Blo 1297967 1948397 := bbase (se 3 (by rfl) ⟨365324, by rfl⟩ : syracuseStep 1948397 = 730649) (by norm_num)
theorem B2923253 : Blo 1297967 2923253 := bbase (se 5 (by rfl) ⟨137027, by rfl⟩ : syracuseStep 2923253 = 274055) (by norm_num)
theorem B1948421 : Blo 1297967 1948421 := bbase (se 4 (by rfl) ⟨182664, by rfl⟩ : syracuseStep 1948421 = 365329) (by norm_num)
theorem B1948445 : Blo 1297967 1948445 := bbase (se 3 (by rfl) ⟨365333, by rfl⟩ : syracuseStep 1948445 = 730667) (by norm_num)
theorem B1948469 : Blo 1297967 1948469 := bbase (se 5 (by rfl) ⟨91334, by rfl⟩ : syracuseStep 1948469 = 182669) (by norm_num)
theorem B2923325 : Blo 1297967 2923325 := bbase (se 3 (by rfl) ⟨548123, by rfl⟩ : syracuseStep 2923325 = 1096247) (by norm_num)
theorem B1948493 : Blo 1297967 1948493 := bbase (se 3 (by rfl) ⟨365342, by rfl⟩ : syracuseStep 1948493 = 730685) (by norm_num)
theorem B2464597 : Blo 1297967 2464597 := bbase (se 9 (by rfl) ⟨7220, by rfl⟩ : syracuseStep 2464597 = 14441) (by norm_num)
theorem B1850197 : Blo 1297967 1850197 := bbase (se 9 (by rfl) ⟨5420, by rfl⟩ : syracuseStep 1850197 = 10841) (by norm_num)
theorem B1948517 : Blo 1297967 1948517 := bbase (se 4 (by rfl) ⟨182673, by rfl⟩ : syracuseStep 1948517 = 365347) (by norm_num)
theorem B1948541 : Blo 1297967 1948541 := bbase (se 3 (by rfl) ⟨365351, by rfl⟩ : syracuseStep 1948541 = 730703) (by norm_num)
theorem B2923397 : Blo 1297967 2923397 := bbase (se 4 (by rfl) ⟨274068, by rfl⟩ : syracuseStep 2923397 = 548137) (by norm_num)
theorem B1948565 : Blo 1297967 1948565 := bbase (se 6 (by rfl) ⟨45669, by rfl⟩ : syracuseStep 1948565 = 91339) (by norm_num)
theorem B4684709 : Blo 1297967 4684709 := bbase (se 4 (by rfl) ⟨439191, by rfl⟩ : syracuseStep 4684709 = 878383) (by norm_num)
theorem B1948589 : Blo 1297967 1948589 := bbase (se 3 (by rfl) ⟨365360, by rfl⟩ : syracuseStep 1948589 = 730721) (by norm_num)
theorem B1850293 : Blo 1297967 1850293 := bbase (se 5 (by rfl) ⟨86732, by rfl⟩ : syracuseStep 1850293 = 173465) (by norm_num)
theorem B1948613 : Blo 1297967 1948613 := bbase (se 4 (by rfl) ⟨182682, by rfl⟩ : syracuseStep 1948613 = 365365) (by norm_num)
theorem B2341829 : Blo 1297967 2341829 := bbase (se 4 (by rfl) ⟨219546, by rfl⟩ : syracuseStep 2341829 = 439093) (by norm_num)
theorem B2923469 : Blo 1297967 2923469 := bbase (se 3 (by rfl) ⟨548150, by rfl⟩ : syracuseStep 2923469 = 1096301) (by norm_num)
theorem B1948637 : Blo 1297967 1948637 := bbase (se 3 (by rfl) ⟨365369, by rfl⟩ : syracuseStep 1948637 = 730739) (by norm_num)
theorem B1948661 : Blo 1297967 1948661 := bbase (se 5 (by rfl) ⟨91343, by rfl⟩ : syracuseStep 1948661 = 182687) (by norm_num)
theorem B1948685 : Blo 1297967 1948685 := bbase (se 3 (by rfl) ⟨365378, by rfl⟩ : syracuseStep 1948685 = 730757) (by norm_num)
theorem B2923541 : Blo 1297967 2923541 := bbase (se 6 (by rfl) ⟨68520, by rfl⟩ : syracuseStep 2923541 = 137041) (by norm_num)
theorem B1948709 : Blo 1297967 1948709 := bbase (se 4 (by rfl) ⟨182691, by rfl⟩ : syracuseStep 1948709 = 365383) (by norm_num)
theorem B1948733 : Blo 1297967 1948733 := bbase (se 3 (by rfl) ⟨365387, by rfl⟩ : syracuseStep 1948733 = 730775) (by norm_num)
theorem B1948757 : Blo 1297967 1948757 := bbase (se 8 (by rfl) ⟨11418, by rfl⟩ : syracuseStep 1948757 = 22837) (by norm_num)
theorem B2923613 : Blo 1297967 2923613 := bbase (se 3 (by rfl) ⟨548177, by rfl⟩ : syracuseStep 2923613 = 1096355) (by norm_num)
theorem B1875053 : Blo 1297967 1875053 := bbase (se 3 (by rfl) ⟨351572, by rfl⟩ : syracuseStep 1875053 = 703145) (by norm_num)
theorem B1948781 : Blo 1297967 1948781 := bbase (se 3 (by rfl) ⟨365396, by rfl⟩ : syracuseStep 1948781 = 730793) (by norm_num)
theorem B4381829 : Blo 1297967 4381829 := bbase (se 4 (by rfl) ⟨410796, by rfl⟩ : syracuseStep 4381829 = 821593) (by norm_num)
theorem B2464901 : Blo 1297967 2464901 := bbase (se 4 (by rfl) ⟨231084, by rfl⟩ : syracuseStep 2464901 = 462169) (by norm_num)
theorem B1948805 : Blo 1297967 1948805 := bbase (se 4 (by rfl) ⟨182700, by rfl⟩ : syracuseStep 1948805 = 365401) (by norm_num)
theorem B1948829 : Blo 1297967 1948829 := bbase (se 3 (by rfl) ⟨365405, by rfl⟩ : syracuseStep 1948829 = 730811) (by norm_num)
theorem B2923685 : Blo 1297967 2923685 := bbase (se 4 (by rfl) ⟨274095, by rfl⟩ : syracuseStep 2923685 = 548191) (by norm_num)
theorem B1948853 : Blo 1297967 1948853 := bbase (se 5 (by rfl) ⟨91352, by rfl⟩ : syracuseStep 1948853 = 182705) (by norm_num)
theorem B1948877 : Blo 1297967 1948877 := bbase (se 3 (by rfl) ⟨365414, by rfl⟩ : syracuseStep 1948877 = 730829) (by norm_num)
theorem B1948901 : Blo 1297967 1948901 := bbase (se 4 (by rfl) ⟨182709, by rfl⟩ : syracuseStep 1948901 = 365419) (by norm_num)
theorem B1875181 : Blo 1297967 1875181 := bbase (se 3 (by rfl) ⟨351596, by rfl⟩ : syracuseStep 1875181 = 703193) (by norm_num)
theorem B2923757 : Blo 1297967 2923757 := bbase (se 3 (by rfl) ⟨548204, by rfl⟩ : syracuseStep 2923757 = 1096409) (by norm_num)
theorem B1948925 : Blo 1297967 1948925 := bbase (se 3 (by rfl) ⟨365423, by rfl⟩ : syracuseStep 1948925 = 730847) (by norm_num)
theorem B1948949 : Blo 1297967 1948949 := bbase (se 6 (by rfl) ⟨45678, by rfl⟩ : syracuseStep 1948949 = 91357) (by norm_num)
theorem B1948973 : Blo 1297967 1948973 := bbase (se 3 (by rfl) ⟨365432, by rfl⟩ : syracuseStep 1948973 = 730865) (by norm_num)
theorem B2923829 : Blo 1297967 2923829 := bbase (se 5 (by rfl) ⟨137054, by rfl⟩ : syracuseStep 2923829 = 274109) (by norm_num)
theorem B1948997 : Blo 1297967 1948997 := bbase (se 4 (by rfl) ⟨182718, by rfl⟩ : syracuseStep 1948997 = 365437) (by norm_num)
theorem B3333469 : Blo 1297967 3333469 := bbase (se 3 (by rfl) ⟨625025, by rfl⟩ : syracuseStep 3333469 = 1250051) (by norm_num)
theorem B1949021 : Blo 1297967 1949021 := bbase (se 3 (by rfl) ⟨365441, by rfl⟩ : syracuseStep 1949021 = 730883) (by norm_num)
theorem B1949045 : Blo 1297967 1949045 := bbase (se 5 (by rfl) ⟨91361, by rfl⟩ : syracuseStep 1949045 = 182723) (by norm_num)
theorem B2923901 : Blo 1297967 2923901 := bbase (se 3 (by rfl) ⟨548231, by rfl⟩ : syracuseStep 2923901 = 1096463) (by norm_num)
theorem B1949069 : Blo 1297967 1949069 := bbase (se 3 (by rfl) ⟨365450, by rfl⟩ : syracuseStep 1949069 = 730901) (by norm_num)
theorem B4742549 : Blo 1297967 4742549 := bbase (se 6 (by rfl) ⟨111153, by rfl⟩ : syracuseStep 4742549 = 222307) (by norm_num)
theorem B1949093 : Blo 1297967 1949093 := bbase (se 4 (by rfl) ⟨182727, by rfl⟩ : syracuseStep 1949093 = 365455) (by norm_num)
theorem B1850789 : Blo 1297967 1850789 := bbase (se 4 (by rfl) ⟨173511, by rfl⟩ : syracuseStep 1850789 = 347023) (by norm_num)
theorem B1949117 : Blo 1297967 1949117 := bbase (se 3 (by rfl) ⟨365459, by rfl⟩ : syracuseStep 1949117 = 730919) (by norm_num)
theorem B2923973 : Blo 1297967 2923973 := bbase (se 4 (by rfl) ⟨274122, by rfl⟩ : syracuseStep 2923973 = 548245) (by norm_num)
theorem B1949141 : Blo 1297967 1949141 := bbase (se 7 (by rfl) ⟨22841, by rfl⟩ : syracuseStep 1949141 = 45683) (by norm_num)
theorem B1949165 : Blo 1297967 1949165 := bbase (se 3 (by rfl) ⟨365468, by rfl⟩ : syracuseStep 1949165 = 730937) (by norm_num)
theorem B4931077 : Blo 1297967 4931077 := bbase (se 4 (by rfl) ⟨462288, by rfl⟩ : syracuseStep 4931077 = 924577) (by norm_num)
theorem B1949189 : Blo 1297967 1949189 := bbase (se 4 (by rfl) ⟨182736, by rfl⟩ : syracuseStep 1949189 = 365473) (by norm_num)
theorem B2924045 : Blo 1297967 2924045 := bbase (se 3 (by rfl) ⟨548258, by rfl⟩ : syracuseStep 2924045 = 1096517) (by norm_num)
theorem B6577685 : Blo 1297967 6577685 := bbase (se 6 (by rfl) ⟨154164, by rfl⟩ : syracuseStep 6577685 = 308329) (by norm_num)
theorem B1949213 : Blo 1297967 1949213 := bbase (se 3 (by rfl) ⟨365477, by rfl⟩ : syracuseStep 1949213 = 730955) (by norm_num)
theorem B4382261 : Blo 1297967 4382261 := bbase (se 5 (by rfl) ⟨205418, by rfl⟩ : syracuseStep 4382261 = 410837) (by norm_num)
theorem B1949237 : Blo 1297967 1949237 := bbase (se 5 (by rfl) ⟨91370, by rfl⟩ : syracuseStep 1949237 = 182741) (by norm_num)
theorem B1334845 : Blo 1297967 1334845 := bbase (se 3 (by rfl) ⟨250283, by rfl⟩ : syracuseStep 1334845 = 500567) (by norm_num)
theorem B2080325 : Blo 1297967 2080325 := bbase (se 4 (by rfl) ⟨195030, by rfl⟩ : syracuseStep 2080325 = 390061) (by norm_num)
theorem B1949261 : Blo 1297967 1949261 := bbase (se 3 (by rfl) ⟨365486, by rfl⟩ : syracuseStep 1949261 = 730973) (by norm_num)
theorem B14794325 : Blo 1297967 14794325 := bbase (se 8 (by rfl) ⟨86685, by rfl⟩ : syracuseStep 14794325 = 173371) (by norm_num)
theorem B2924117 : Blo 1297967 2924117 := bbase (se 8 (by rfl) ⟨17133, by rfl⟩ : syracuseStep 2924117 = 34267) (by norm_num)
theorem B1949285 : Blo 1297967 1949285 := bbase (se 4 (by rfl) ⟨182745, by rfl⟩ : syracuseStep 1949285 = 365491) (by norm_num)
theorem B1949309 : Blo 1297967 1949309 := bbase (se 3 (by rfl) ⟨365495, by rfl⟩ : syracuseStep 1949309 = 730991) (by norm_num)
theorem B1580693 : Blo 1297967 1580693 := bbase (se 6 (by rfl) ⟨37047, by rfl⟩ : syracuseStep 1580693 = 74095) (by norm_num)
theorem B1949333 : Blo 1297967 1949333 := bbase (se 6 (by rfl) ⟨45687, by rfl⟩ : syracuseStep 1949333 = 91375) (by norm_num)
theorem B2924189 : Blo 1297967 2924189 := bbase (se 3 (by rfl) ⟨548285, by rfl⟩ : syracuseStep 2924189 = 1096571) (by norm_num)
theorem B1949357 : Blo 1297967 1949357 := bbase (se 3 (by rfl) ⟨365504, by rfl⟩ : syracuseStep 1949357 = 731009) (by norm_num)
theorem B1949381 : Blo 1297967 1949381 := bbase (se 4 (by rfl) ⟨182754, by rfl⟩ : syracuseStep 1949381 = 365509) (by norm_num)
theorem B5545685 : Blo 1297967 5545685 := bbase (se 7 (by rfl) ⟨64988, by rfl⟩ : syracuseStep 5545685 = 129977) (by norm_num)
theorem B1949405 : Blo 1297967 1949405 := bbase (se 3 (by rfl) ⟨365513, by rfl⟩ : syracuseStep 1949405 = 731027) (by norm_num)
theorem B2924261 : Blo 1297967 2924261 := bbase (se 4 (by rfl) ⟨274149, by rfl⟩ : syracuseStep 2924261 = 548299) (by norm_num)
theorem B1335025 : Blo 1297967 1335025 := bbase (se 2 (by rfl) ⟨500634, by rfl⟩ : syracuseStep 1335025 = 1001269) (by norm_num)
theorem B1949429 : Blo 1297967 1949429 := bbase (se 5 (by rfl) ⟨91379, by rfl⟩ : syracuseStep 1949429 = 182759) (by norm_num)
theorem B1949453 : Blo 1297967 1949453 := bbase (se 3 (by rfl) ⟨365522, by rfl⟩ : syracuseStep 1949453 = 731045) (by norm_num)
theorem B1949477 : Blo 1297967 1949477 := bbase (se 4 (by rfl) ⟨182763, by rfl⟩ : syracuseStep 1949477 = 365527) (by norm_num)
theorem B2924333 : Blo 1297967 2924333 := bbase (se 3 (by rfl) ⟨548312, by rfl⟩ : syracuseStep 2924333 = 1096625) (by norm_num)
theorem B4931381 : Blo 1297967 4931381 := bbase (se 5 (by rfl) ⟨231158, by rfl⟩ : syracuseStep 4931381 = 462317) (by norm_num)
theorem B1949501 : Blo 1297967 1949501 := bbase (se 3 (by rfl) ⟨365531, by rfl⟩ : syracuseStep 1949501 = 731063) (by norm_num)
theorem B1949525 : Blo 1297967 1949525 := bbase (se 9 (by rfl) ⟨5711, by rfl⟩ : syracuseStep 1949525 = 11423) (by norm_num)
theorem B7905109 : Blo 1297967 7905109 := bbase (se 9 (by rfl) ⟨23159, by rfl⟩ : syracuseStep 7905109 = 46319) (by norm_num)
theorem B1949549 : Blo 1297967 1949549 := bbase (se 3 (by rfl) ⟨365540, by rfl⟩ : syracuseStep 1949549 = 731081) (by norm_num)
theorem B2465653 : Blo 1297967 2465653 := bbase (se 5 (by rfl) ⟨115577, by rfl⟩ : syracuseStep 2465653 = 231155) (by norm_num)
theorem B2924405 : Blo 1297967 2924405 := bbase (se 5 (by rfl) ⟨137081, by rfl⟩ : syracuseStep 2924405 = 274163) (by norm_num)
theorem B1949573 : Blo 1297967 1949573 := bbase (se 4 (by rfl) ⟨182772, by rfl⟩ : syracuseStep 1949573 = 365545) (by norm_num)
theorem B1949597 : Blo 1297967 1949597 := bbase (se 3 (by rfl) ⟨365549, by rfl⟩ : syracuseStep 1949597 = 731099) (by norm_num)
theorem B1949621 : Blo 1297967 1949621 := bbase (se 5 (by rfl) ⟨91388, by rfl⟩ : syracuseStep 1949621 = 182777) (by norm_num)
theorem B2924477 : Blo 1297967 2924477 := bbase (se 3 (by rfl) ⟨548339, by rfl⟩ : syracuseStep 2924477 = 1096679) (by norm_num)
theorem B2080709 : Blo 1297967 2080709 := bbase (se 4 (by rfl) ⟨195066, by rfl⟩ : syracuseStep 2080709 = 390133) (by norm_num)
theorem B1949645 : Blo 1297967 1949645 := bbase (se 3 (by rfl) ⟨365558, by rfl⟩ : syracuseStep 1949645 = 731117) (by norm_num)
theorem B4382693 : Blo 1297967 4382693 := bbase (se 4 (by rfl) ⟨410877, by rfl⟩ : syracuseStep 4382693 = 821755) (by norm_num)
theorem B1949669 : Blo 1297967 1949669 := bbase (se 4 (by rfl) ⟨182781, by rfl⟩ : syracuseStep 1949669 = 365563) (by norm_num)
theorem B1335289 : Blo 1297967 1335289 := bbase (se 2 (by rfl) ⟨500733, by rfl⟩ : syracuseStep 1335289 = 1001467) (by norm_num)
theorem B1949693 : Blo 1297967 1949693 := bbase (se 3 (by rfl) ⟨365567, by rfl⟩ : syracuseStep 1949693 = 731135) (by norm_num)
theorem B1949699 : Blo 1297967 1949699 := bstep (se 1 (by rfl) ⟨1462274, by rfl⟩ : syracuseStep 1949699 = 2924549) B2924549
theorem B1949729 : Blo 1297967 1949729 := bstep (se 2 (by rfl) ⟨731148, by rfl⟩ : syracuseStep 1949729 = 1462297) B1462297
theorem B1949747 : Blo 1297967 1949747 := bstep (se 1 (by rfl) ⟨1462310, by rfl⟩ : syracuseStep 1949747 = 2924621) B2924621
theorem B4382801 : Blo 1297967 4382801 := bstep (se 2 (by rfl) ⟨1643550, by rfl⟩ : syracuseStep 4382801 = 3287101) B3287101
theorem B2465873 : Blo 1297967 2465873 := bstep (se 2 (by rfl) ⟨924702, by rfl⟩ : syracuseStep 2465873 = 1849405) B1849405
theorem B1949777 : Blo 1297967 1949777 := bstep (se 2 (by rfl) ⟨731166, by rfl⟩ : syracuseStep 1949777 = 1462333) B1462333
theorem B1949795 : Blo 1297967 1949795 := bstep (se 1 (by rfl) ⟨1462346, by rfl⟩ : syracuseStep 1949795 = 2924693) B2924693
theorem B6242417 : Blo 1297967 6242417 := bstep (se 2 (by rfl) ⟨2340906, by rfl⟩ : syracuseStep 6242417 = 4681813) B4681813
theorem B2924657 : Blo 1297967 2924657 := bstep (se 2 (by rfl) ⟨1096746, by rfl⟩ : syracuseStep 2924657 = 2193493) B2193493
theorem B1949825 : Blo 1297967 1949825 := bstep (se 2 (by rfl) ⟨731184, by rfl⟩ : syracuseStep 1949825 = 1462369) B1462369
theorem B2924675 : Blo 1297967 2924675 := bstep (se 1 (by rfl) ⟨2193506, by rfl⟩ : syracuseStep 2924675 = 4387013) B4387013
theorem B1949843 : Blo 1297967 1949843 := bstep (se 1 (by rfl) ⟨1462382, by rfl⟩ : syracuseStep 1949843 = 2924765) B2924765
theorem B1949873 : Blo 1297967 1949873 := bstep (se 2 (by rfl) ⟨731202, by rfl⟩ : syracuseStep 1949873 = 1462405) B1462405
theorem B1949891 : Blo 1297967 1949891 := bstep (se 1 (by rfl) ⟨1462418, by rfl⟩ : syracuseStep 1949891 = 2924837) B2924837
theorem B7020749 : Blo 1297967 7020749 := bstep (se 3 (by rfl) ⟨1316390, by rfl⟩ : syracuseStep 7020749 = 2632781) B2632781
theorem B1949921 : Blo 1297967 1949921 := bstep (se 2 (by rfl) ⟨731220, by rfl⟩ : syracuseStep 1949921 = 1462441) B1462441
theorem B1949939 : Blo 1297967 1949939 := bstep (se 1 (by rfl) ⟨1462454, by rfl⟩ : syracuseStep 1949939 = 2924909) B2924909
theorem B4161827 : Blo 1297967 4161827 := bstep (se 1 (by rfl) ⟨3121370, by rfl⟩ : syracuseStep 4161827 = 6242741) B6242741
theorem B7119173 : Blo 1297967 7119173 := bstep (se 4 (by rfl) ⟨667422, by rfl⟩ : syracuseStep 7119173 = 1334845) B1334845
theorem B1974611 : Blo 1297967 1974611 := bstep (se 1 (by rfl) ⟨1480958, by rfl⟩ : syracuseStep 1974611 = 2961917) B2961917
theorem B5546353 : Blo 1297967 5546353 := bstep (se 2 (by rfl) ⟨2079882, by rfl⟩ : syracuseStep 5546353 = 4159765) B4159765
theorem B1974721 : Blo 1297967 1974721 := bstep (se 2 (by rfl) ⟨740520, by rfl⟩ : syracuseStep 1974721 = 1481041) B1481041
theorem B4383341 : Blo 1297967 4383341 := bstep (se 3 (by rfl) ⟨821876, by rfl⟩ : syracuseStep 4383341 = 1643753) B1643753
theorem B4383395 : Blo 1297967 4383395 := bstep (se 1 (by rfl) ⟨3287546, by rfl⟩ : syracuseStep 4383395 = 6575093) B6575093
theorem B6587057 : Blo 1297967 6587057 := bstep (se 2 (by rfl) ⟨2470146, by rfl⟩ : syracuseStep 6587057 = 4940293) B4940293
theorem B4440781 : Blo 1297967 4440781 := bstep (se 3 (by rfl) ⟨832646, by rfl⟩ : syracuseStep 4440781 = 1665293) B1665293
theorem B4932323 : Blo 1297967 4932323 := bstep (se 1 (by rfl) ⟨3699242, by rfl⟩ : syracuseStep 4932323 = 7398485) B7398485
theorem B26665699 : Blo 1297967 26665699 := bstep (se 1 (by rfl) ⟨19999274, by rfl⟩ : syracuseStep 26665699 = 39998549) B39998549
theorem B24986339 : Blo 1297967 24986339 := bstep (se 1 (by rfl) ⟨18739754, by rfl⟩ : syracuseStep 24986339 = 37479509) B37479509
theorem B16646897 : Blo 1297967 16646897 := bstep (se 2 (by rfl) ⟨6242586, by rfl⟩ : syracuseStep 16646897 = 12485173) B12485173
theorem B2081555 : Blo 1297967 2081555 := bstep (se 1 (by rfl) ⟨1561166, by rfl⟩ : syracuseStep 2081555 = 3122333) B3122333
theorem B4383665 : Blo 1297967 4383665 := bstep (se 2 (by rfl) ⟨1643874, by rfl⟩ : syracuseStep 4383665 = 3287749) B3287749
theorem B2466769 : Blo 1297967 2466769 := bstep (se 2 (by rfl) ⟨925038, by rfl⟩ : syracuseStep 2466769 = 1850077) B1850077
theorem B2081747 : Blo 1297967 2081747 := bstep (se 1 (by rfl) ⟨1561310, by rfl⟩ : syracuseStep 2081747 = 3122621) B3122621
theorem B26665955 : Blo 1297967 26665955 := bstep (se 1 (by rfl) ⟨19999466, by rfl⟩ : syracuseStep 26665955 = 39998933) B39998933
theorem B6571043 : Blo 1297967 6571043 := bstep (se 1 (by rfl) ⟨4928282, by rfl⟩ : syracuseStep 6571043 = 9856565) B9856565
theorem B3376163 : Blo 1297967 3376163 := bstep (se 1 (by rfl) ⟨2532122, by rfl⟩ : syracuseStep 3376163 = 5064245) B5064245
theorem B3286129 : Blo 1297967 3286129 := bstep (se 2 (by rfl) ⟨1232298, by rfl⟩ : syracuseStep 3286129 = 2464597) B2464597
theorem B2466929 : Blo 1297967 2466929 := bstep (se 2 (by rfl) ⟨925098, by rfl⟩ : syracuseStep 2466929 = 1850197) B1850197
theorem B7120133 : Blo 1297967 7120133 := bstep (se 4 (by rfl) ⟨667512, by rfl⟩ : syracuseStep 7120133 = 1335025) B1335025
theorem B3851569 : Blo 1297967 3851569 := bstep (se 2 (by rfl) ⟨1444338, by rfl⟩ : syracuseStep 3851569 = 2888677) B2888677
theorem B3286403 : Blo 1297967 3286403 := bstep (se 1 (by rfl) ⟨2464802, by rfl⟩ : syracuseStep 3286403 = 4929605) B4929605
theorem B1754561 : Blo 1297967 1754561 := bstep (se 2 (by rfl) ⟨657960, by rfl⟩ : syracuseStep 1754561 = 1315921) B1315921
theorem B4679117 : Blo 1297967 4679117 := bstep (se 3 (by rfl) ⟨877334, by rfl⟩ : syracuseStep 4679117 = 1754669) B1754669
theorem B4384205 : Blo 1297967 4384205 := bstep (se 3 (by rfl) ⟨822038, by rfl⟩ : syracuseStep 4384205 = 1644077) B1644077
theorem B8881649 : Blo 1297967 8881649 := bstep (se 2 (by rfl) ⟨3330618, by rfl⟩ : syracuseStep 8881649 = 6661237) B6661237
theorem B3556867 : Blo 1297967 3556867 := bstep (se 1 (by rfl) ⟨2667650, by rfl⟩ : syracuseStep 3556867 = 5335301) B5335301
theorem B4384259 : Blo 1297967 4384259 := bstep (se 1 (by rfl) ⟨3288194, by rfl⟩ : syracuseStep 4384259 = 6576389) B6576389
theorem B2467331 : Blo 1297967 2467331 := bstep (se 1 (by rfl) ⟨1850498, by rfl⟩ : syracuseStep 2467331 = 3700997) B3700997
theorem B3286595 : Blo 1297967 3286595 := bstep (se 1 (by rfl) ⟨2464946, by rfl⟩ : syracuseStep 3286595 = 4929893) B4929893
theorem B3950147 : Blo 1297967 3950147 := bstep (se 1 (by rfl) ⟨2962610, by rfl⟩ : syracuseStep 3950147 = 5925221) B5925221
theorem B2500241 : Blo 1297967 2500241 := bstep (se 2 (by rfl) ⟨937590, by rfl⟩ : syracuseStep 2500241 = 1875181) B1875181
theorem B1386131 : Blo 1297967 1386131 := bstep (se 1 (by rfl) ⟨1039598, by rfl⟩ : syracuseStep 1386131 = 2079197) B2079197
theorem B4933325 : Blo 1297967 4933325 := bstep (se 3 (by rfl) ⟨924998, by rfl⟩ : syracuseStep 4933325 = 1849997) B1849997
theorem B6579953 : Blo 1297967 6579953 := bstep (se 2 (by rfl) ⟨2467482, by rfl⟩ : syracuseStep 6579953 = 4934965) B4934965
theorem B6326029 : Blo 1297967 6326029 := bstep (se 3 (by rfl) ⟨1186130, by rfl⟩ : syracuseStep 6326029 = 2372261) B2372261
theorem B4384529 : Blo 1297967 4384529 := bstep (se 2 (by rfl) ⟨1644198, by rfl⟩ : syracuseStep 4384529 = 3288397) B3288397
theorem B6571853 : Blo 1297967 6571853 := bstep (se 3 (by rfl) ⟨1232222, by rfl⟩ : syracuseStep 6571853 = 2464445) B2464445
theorem B14788493 : Blo 1297967 14788493 := bstep (se 3 (by rfl) ⟨2772842, by rfl⟩ : syracuseStep 14788493 = 5545685) B5545685
theorem B3123139 : Blo 1297967 3123139 := bstep (se 1 (by rfl) ⟨2342354, by rfl⟩ : syracuseStep 3123139 = 4684709) B4684709
theorem B1460227 : Blo 1297967 1460227 := bstep (se 1 (by rfl) ⟨1095170, by rfl⟩ : syracuseStep 1460227 = 2190341) B2190341
theorem B3696749 : Blo 1297967 3696749 := bstep (se 3 (by rfl) ⟨693140, by rfl⟩ : syracuseStep 3696749 = 1386281) B1386281
theorem B1460371 : Blo 1297967 1460371 := bstep (se 1 (by rfl) ⟨1095278, by rfl⟩ : syracuseStep 1460371 = 2190557) B2190557
theorem B1460515 : Blo 1297967 1460515 := bstep (se 1 (by rfl) ⟨1095386, by rfl⟩ : syracuseStep 1460515 = 2190773) B2190773
theorem B3696941 : Blo 1297967 3696941 := bstep (se 3 (by rfl) ⟨693176, by rfl⟩ : syracuseStep 3696941 = 1386353) B1386353
theorem B4385069 : Blo 1297967 4385069 := bstep (se 3 (by rfl) ⟨822200, by rfl⟩ : syracuseStep 4385069 = 1644401) B1644401
theorem B4385123 : Blo 1297967 4385123 := bstep (se 1 (by rfl) ⟨3288842, by rfl⟩ : syracuseStep 4385123 = 6577685) B6577685
theorem B1386883 : Blo 1297967 1386883 := bstep (se 1 (by rfl) ⟨1040162, by rfl⟩ : syracuseStep 1386883 = 2080325) B2080325
theorem B1755523 : Blo 1297967 1755523 := bstep (se 1 (by rfl) ⟨1316642, by rfl⟩ : syracuseStep 1755523 = 2633285) B2633285
theorem B1460659 : Blo 1297967 1460659 := bstep (se 1 (by rfl) ⟨1095494, by rfl⟩ : syracuseStep 1460659 = 2190989) B2190989
theorem B4442573 : Blo 1297967 4442573 := bstep (se 3 (by rfl) ⟨832982, by rfl⟩ : syracuseStep 4442573 = 1665965) B1665965
theorem B3287537 : Blo 1297967 3287537 := bstep (se 2 (by rfl) ⟨1232826, by rfl⟩ : syracuseStep 3287537 = 2465653) B2465653
theorem B6244877 : Blo 1297967 6244877 := bstep (se 3 (by rfl) ⟨1170914, by rfl⟩ : syracuseStep 6244877 = 2341829) B2341829
theorem B3287587 : Blo 1297967 3287587 := bstep (se 1 (by rfl) ⟨2465690, by rfl⟩ : syracuseStep 3287587 = 4931381) B4931381
theorem B1460803 : Blo 1297967 1460803 := bstep (se 1 (by rfl) ⟨1095602, by rfl⟩ : syracuseStep 1460803 = 2191205) B2191205
theorem B4385393 : Blo 1297967 4385393 := bstep (se 2 (by rfl) ⟨1644522, by rfl⟩ : syracuseStep 4385393 = 3289045) B3289045
theorem B1387139 : Blo 1297967 1387139 := bstep (se 1 (by rfl) ⟨1040354, by rfl⟩ : syracuseStep 1387139 = 2080709) B2080709
theorem B1780385 : Blo 1297967 1780385 := bstep (se 2 (by rfl) ⟨667644, by rfl⟩ : syracuseStep 1780385 = 1335289) B1335289
theorem B3287729 : Blo 1297967 3287729 := bstep (se 2 (by rfl) ⟨1232898, by rfl⟩ : syracuseStep 3287729 = 2465797) B2465797
theorem B16648901 : Blo 1297967 16648901 := bstep (se 4 (by rfl) ⟨1560834, by rfl⟩ : syracuseStep 16648901 = 3121669) B3121669
theorem B1460947 : Blo 1297967 1460947 := bstep (se 1 (by rfl) ⟨1095710, by rfl⟩ : syracuseStep 1460947 = 2191421) B2191421
theorem B4442861 : Blo 1297967 4442861 := bstep (se 3 (by rfl) ⟨833036, by rfl⟩ : syracuseStep 4442861 = 1666073) B1666073
theorem B7400261 : Blo 1297967 7400261 := bstep (se 4 (by rfl) ⟨693774, by rfl⟩ : syracuseStep 7400261 = 1387549) B1387549
theorem B1461091 : Blo 1297967 1461091 := bstep (se 1 (by rfl) ⟨1095818, by rfl⟩ : syracuseStep 1461091 = 2191637) B2191637
theorem B2501489 : Blo 1297967 2501489 := bstep (se 2 (by rfl) ⟨938058, by rfl⟩ : syracuseStep 2501489 = 1876117) B1876117
theorem B4164493 : Blo 1297967 4164493 := bstep (se 3 (by rfl) ⟨780842, by rfl⟩ : syracuseStep 4164493 = 1561685) B1561685
theorem B5000141 : Blo 1297967 5000141 := bstep (se 3 (by rfl) ⟨937526, by rfl⟩ : syracuseStep 5000141 = 1875053) B1875053
theorem B8326115 : Blo 1297967 8326115 := bstep (se 1 (by rfl) ⟨6244586, by rfl⟩ : syracuseStep 8326115 = 12489173) B12489173
theorem B1461235 : Blo 1297967 1461235 := bstep (se 1 (by rfl) ⟨1095926, by rfl⟩ : syracuseStep 1461235 = 2191853) B2191853
theorem B5139533 : Blo 1297967 5139533 := bstep (se 3 (by rfl) ⟨963662, by rfl⟩ : syracuseStep 5139533 = 1927325) B1927325
theorem B6237283 : Blo 1297967 6237283 := bstep (se 1 (by rfl) ⟨4677962, by rfl⟩ : syracuseStep 6237283 = 9355925) B9355925
theorem B2190449 : Blo 1297967 2190449 := bstep (se 2 (by rfl) ⟨821418, by rfl⟩ : syracuseStep 2190449 = 1642837) B1642837
theorem B1461379 : Blo 1297967 1461379 := bstep (se 1 (by rfl) ⟨1096034, by rfl⟩ : syracuseStep 1461379 = 2192069) B2192069
theorem B4385933 : Blo 1297967 4385933 := bstep (se 3 (by rfl) ⟨822362, by rfl⟩ : syracuseStep 4385933 = 1644725) B1644725
theorem B7023779 : Blo 1297967 7023779 := bstep (se 1 (by rfl) ⟨5267834, by rfl⟩ : syracuseStep 7023779 = 10535669) B10535669
theorem B4385987 : Blo 1297967 4385987 := bstep (se 1 (by rfl) ⟨3289490, by rfl⟩ : syracuseStep 4385987 = 6578981) B6578981
theorem B2190577 : Blo 1297967 2190577 := bstep (se 2 (by rfl) ⟨821466, by rfl⟩ : syracuseStep 2190577 = 1642933) B1642933
theorem B9358577 : Blo 1297967 9358577 := bstep (se 2 (by rfl) ⟨3509466, by rfl⟩ : syracuseStep 9358577 = 7018933) B7018933
theorem B7498993 : Blo 1297967 7498993 := bstep (se 2 (by rfl) ⟨2812122, by rfl⟩ : syracuseStep 7498993 = 5624245) B5624245
theorem B3697933 : Blo 1297967 3697933 := bstep (se 3 (by rfl) ⟨693362, by rfl⟩ : syracuseStep 3697933 = 1386725) B1386725
theorem B7400717 : Blo 1297967 7400717 := bstep (se 3 (by rfl) ⟨1387634, by rfl⟩ : syracuseStep 7400717 = 2775269) B2775269
theorem B2190611 : Blo 1297967 2190611 := bstep (se 1 (by rfl) ⟨1642958, by rfl⟩ : syracuseStep 2190611 = 3285917) B3285917
theorem B1461523 : Blo 1297967 1461523 := bstep (se 1 (by rfl) ⟨1096142, by rfl⟩ : syracuseStep 1461523 = 2192285) B2192285
theorem B9366853 : Blo 1297967 9366853 := bstep (se 4 (by rfl) ⟨878142, by rfl⟩ : syracuseStep 9366853 = 1756285) B1756285
theorem B5549411 : Blo 1297967 5549411 := bstep (se 1 (by rfl) ⟨4162058, by rfl⟩ : syracuseStep 5549411 = 8324117) B8324117
theorem B1387891 : Blo 1297967 1387891 := bstep (se 1 (by rfl) ⟨1040918, by rfl⟩ : syracuseStep 1387891 = 2081837) B2081837
theorem B7392653 : Blo 1297967 7392653 := bstep (se 3 (by rfl) ⟨1386122, by rfl⟩ : syracuseStep 7392653 = 2772245) B2772245
theorem B1756561 : Blo 1297967 1756561 := bstep (se 2 (by rfl) ⟨658710, by rfl⟩ : syracuseStep 1756561 = 1317421) B1317421
theorem B2190739 : Blo 1297967 2190739 := bstep (se 1 (by rfl) ⟨1643054, by rfl⟩ : syracuseStep 2190739 = 3286109) B3286109
theorem B1461667 : Blo 1297967 1461667 := bstep (se 1 (by rfl) ⟨1096250, by rfl⟩ : syracuseStep 1461667 = 2192501) B2192501
theorem B8326577 : Blo 1297967 8326577 := bstep (se 2 (by rfl) ⟨3122466, by rfl⟩ : syracuseStep 8326577 = 6244933) B6244933
theorem B4386257 : Blo 1297967 4386257 := bstep (se 2 (by rfl) ⟨1644846, by rfl⟩ : syracuseStep 4386257 = 3289693) B3289693
theorem B2190881 : Blo 1297967 2190881 := bstep (se 2 (by rfl) ⟨821580, by rfl⟩ : syracuseStep 2190881 = 1643161) B1643161
theorem B1297971 : Blo 1297967 1297971 := bstep (se 1 (by rfl) ⟨973478, by rfl⟩ : syracuseStep 1297971 = 1946957) B1946957
theorem B1461811 : Blo 1297967 1461811 := bstep (se 1 (by rfl) ⟨1096358, by rfl⟩ : syracuseStep 1461811 = 2192717) B2192717
theorem B1297987 : Blo 1297967 1297987 := bstep (se 1 (by rfl) ⟨973490, by rfl⟩ : syracuseStep 1297987 = 1946981) B1946981
theorem B1298003 : Blo 1297967 1298003 := bstep (se 1 (by rfl) ⟨973502, by rfl⟩ : syracuseStep 1298003 = 1947005) B1947005
theorem B1298019 : Blo 1297967 1298019 := bstep (se 1 (by rfl) ⟨973514, by rfl⟩ : syracuseStep 1298019 = 1947029) B1947029
theorem B1298035 : Blo 1297967 1298035 := bstep (se 1 (by rfl) ⟨973526, by rfl⟩ : syracuseStep 1298035 = 1947053) B1947053
theorem B2166401 : Blo 1297967 2166401 := bstep (se 2 (by rfl) ⟨812400, by rfl⟩ : syracuseStep 2166401 = 1624801) B1624801
theorem B1298051 : Blo 1297967 1298051 := bstep (se 1 (by rfl) ⟨973538, by rfl⟩ : syracuseStep 1298051 = 1947077) B1947077
theorem B3288721 : Blo 1297967 3288721 := bstep (se 2 (by rfl) ⟨1233270, by rfl⟩ : syracuseStep 3288721 = 2466541) B2466541
theorem B1298067 : Blo 1297967 1298067 := bstep (se 1 (by rfl) ⟨973550, by rfl⟩ : syracuseStep 1298067 = 1947101) B1947101
theorem B2191009 : Blo 1297967 2191009 := bstep (se 2 (by rfl) ⟨821628, by rfl⟩ : syracuseStep 2191009 = 1643257) B1643257
theorem B1298083 : Blo 1297967 1298083 := bstep (se 1 (by rfl) ⟨973562, by rfl⟩ : syracuseStep 1298083 = 1947125) B1947125
theorem B1298099 : Blo 1297967 1298099 := bstep (se 1 (by rfl) ⟨973574, by rfl⟩ : syracuseStep 1298099 = 1947149) B1947149
theorem B1298115 : Blo 1297967 1298115 := bstep (se 1 (by rfl) ⟨973586, by rfl⟩ : syracuseStep 1298115 = 1947173) B1947173
theorem B2191043 : Blo 1297967 2191043 := bstep (se 1 (by rfl) ⟨1643282, by rfl⟩ : syracuseStep 2191043 = 3286565) B3286565
theorem B1461955 : Blo 1297967 1461955 := bstep (se 1 (by rfl) ⟨1096466, by rfl⟩ : syracuseStep 1461955 = 2192933) B2192933
theorem B1298131 : Blo 1297967 1298131 := bstep (se 1 (by rfl) ⟨973598, by rfl⟩ : syracuseStep 1298131 = 1947197) B1947197
theorem B1298147 : Blo 1297967 1298147 := bstep (se 1 (by rfl) ⟨973610, by rfl⟩ : syracuseStep 1298147 = 1947221) B1947221
theorem B1298163 : Blo 1297967 1298163 := bstep (se 1 (by rfl) ⟨973622, by rfl⟩ : syracuseStep 1298163 = 1947245) B1947245
theorem B1298179 : Blo 1297967 1298179 := bstep (se 1 (by rfl) ⟨973634, by rfl⟩ : syracuseStep 1298179 = 1947269) B1947269
theorem B3510029 : Blo 1297967 3510029 := bstep (se 3 (by rfl) ⟨658130, by rfl⟩ : syracuseStep 3510029 = 1316261) B1316261
theorem B4935437 : Blo 1297967 4935437 := bstep (se 3 (by rfl) ⟨925394, by rfl⟩ : syracuseStep 4935437 = 1850789) B1850789
theorem B1298195 : Blo 1297967 1298195 := bstep (se 1 (by rfl) ⟨973646, by rfl⟩ : syracuseStep 1298195 = 1947293) B1947293
theorem B1298211 : Blo 1297967 1298211 := bstep (se 1 (by rfl) ⟨973658, by rfl⟩ : syracuseStep 1298211 = 1947317) B1947317
theorem B1298227 : Blo 1297967 1298227 := bstep (se 1 (by rfl) ⟨973670, by rfl⟩ : syracuseStep 1298227 = 1947341) B1947341
theorem B1298243 : Blo 1297967 1298243 := bstep (se 1 (by rfl) ⟨973682, by rfl⟩ : syracuseStep 1298243 = 1947365) B1947365
theorem B2191171 : Blo 1297967 2191171 := bstep (se 1 (by rfl) ⟨1643378, by rfl⟩ : syracuseStep 2191171 = 3286757) B3286757
theorem B1298259 : Blo 1297967 1298259 := bstep (se 1 (by rfl) ⟨973694, by rfl⟩ : syracuseStep 1298259 = 1947389) B1947389
theorem B1462099 : Blo 1297967 1462099 := bstep (se 1 (by rfl) ⟨1096574, by rfl⟩ : syracuseStep 1462099 = 2193149) B2193149
theorem B1298275 : Blo 1297967 1298275 := bstep (se 1 (by rfl) ⟨973706, by rfl⟩ : syracuseStep 1298275 = 1947413) B1947413
theorem B1298291 : Blo 1297967 1298291 := bstep (se 1 (by rfl) ⟨973718, by rfl⟩ : syracuseStep 1298291 = 1947437) B1947437
theorem B1298307 : Blo 1297967 1298307 := bstep (se 1 (by rfl) ⟨973730, by rfl⟩ : syracuseStep 1298307 = 1947461) B1947461
theorem B1298323 : Blo 1297967 1298323 := bstep (se 1 (by rfl) ⟨973742, by rfl⟩ : syracuseStep 1298323 = 1947485) B1947485
theorem B1298339 : Blo 1297967 1298339 := bstep (se 1 (by rfl) ⟨973754, by rfl⟩ : syracuseStep 1298339 = 1947509) B1947509
theorem B3288995 : Blo 1297967 3288995 := bstep (se 1 (by rfl) ⟨2466746, by rfl⟩ : syracuseStep 3288995 = 4933493) B4933493
theorem B1298355 : Blo 1297967 1298355 := bstep (se 1 (by rfl) ⟨973766, by rfl⟩ : syracuseStep 1298355 = 1947533) B1947533
theorem B1298371 : Blo 1297967 1298371 := bstep (se 1 (by rfl) ⟨973778, by rfl⟩ : syracuseStep 1298371 = 1947557) B1947557
theorem B2191313 : Blo 1297967 2191313 := bstep (se 2 (by rfl) ⟨821742, by rfl⟩ : syracuseStep 2191313 = 1643485) B1643485
theorem B1298387 : Blo 1297967 1298387 := bstep (se 1 (by rfl) ⟨973790, by rfl⟩ : syracuseStep 1298387 = 1947581) B1947581
theorem B1298403 : Blo 1297967 1298403 := bstep (se 1 (by rfl) ⟨973802, by rfl⟩ : syracuseStep 1298403 = 1947605) B1947605
theorem B1462243 : Blo 1297967 1462243 := bstep (se 1 (by rfl) ⟨1096682, by rfl⟩ : syracuseStep 1462243 = 2193365) B2193365
theorem B4386797 : Blo 1297967 4386797 := bstep (se 3 (by rfl) ⟨822524, by rfl⟩ : syracuseStep 4386797 = 1645049) B1645049
theorem B1298419 : Blo 1297967 1298419 := bstep (se 1 (by rfl) ⟨973814, by rfl⟩ : syracuseStep 1298419 = 1947629) B1947629
theorem B1298435 : Blo 1297967 1298435 := bstep (se 1 (by rfl) ⟨973826, by rfl⟩ : syracuseStep 1298435 = 1947653) B1947653
theorem B1298451 : Blo 1297967 1298451 := bstep (se 1 (by rfl) ⟨973838, by rfl⟩ : syracuseStep 1298451 = 1947677) B1947677
theorem B1298467 : Blo 1297967 1298467 := bstep (se 1 (by rfl) ⟨973850, by rfl⟩ : syracuseStep 1298467 = 1947701) B1947701
theorem B4386851 : Blo 1297967 4386851 := bstep (se 1 (by rfl) ⟨3290138, by rfl⟩ : syracuseStep 4386851 = 6580277) B6580277
theorem B1298483 : Blo 1297967 1298483 := bstep (se 1 (by rfl) ⟨973862, by rfl⟩ : syracuseStep 1298483 = 1947725) B1947725
theorem B1298499 : Blo 1297967 1298499 := bstep (se 1 (by rfl) ⟨973874, by rfl⟩ : syracuseStep 1298499 = 1947749) B1947749
theorem B2191441 : Blo 1297967 2191441 := bstep (se 2 (by rfl) ⟨821790, by rfl⟩ : syracuseStep 2191441 = 1643581) B1643581
theorem B1298515 : Blo 1297967 1298515 := bstep (se 1 (by rfl) ⟨973886, by rfl⟩ : syracuseStep 1298515 = 1947773) B1947773
theorem B1298531 : Blo 1297967 1298531 := bstep (se 1 (by rfl) ⟨973898, by rfl⟩ : syracuseStep 1298531 = 1947797) B1947797
theorem B3289187 : Blo 1297967 3289187 := bstep (se 1 (by rfl) ⟨2466890, by rfl⟩ : syracuseStep 3289187 = 4933781) B4933781
theorem B28471409 : Blo 1297967 28471409 := bstep (se 2 (by rfl) ⟨10676778, by rfl⟩ : syracuseStep 28471409 = 21353557) B21353557
theorem B1298547 : Blo 1297967 1298547 := bstep (se 1 (by rfl) ⟨973910, by rfl⟩ : syracuseStep 1298547 = 1947821) B1947821
theorem B2191475 : Blo 1297967 2191475 := bstep (se 1 (by rfl) ⟨1643606, by rfl⟩ : syracuseStep 2191475 = 3287213) B3287213
theorem B1462387 : Blo 1297967 1462387 := bstep (se 1 (by rfl) ⟨1096790, by rfl⟩ : syracuseStep 1462387 = 2193581) B2193581
theorem B1298563 : Blo 1297967 1298563 := bstep (se 1 (by rfl) ⟨973922, by rfl⟩ : syracuseStep 1298563 = 1947845) B1947845
theorem B4812941 : Blo 1297967 4812941 := bstep (se 3 (by rfl) ⟨902426, by rfl⟩ : syracuseStep 4812941 = 1804853) B1804853
theorem B1298579 : Blo 1297967 1298579 := bstep (se 1 (by rfl) ⟨973934, by rfl⟩ : syracuseStep 1298579 = 1947869) B1947869
theorem B1298595 : Blo 1297967 1298595 := bstep (se 1 (by rfl) ⟨973946, by rfl⟩ : syracuseStep 1298595 = 1947893) B1947893
theorem B2920625 : Blo 1297967 2920625 := bstep (se 2 (by rfl) ⟨1095234, by rfl⟩ : syracuseStep 2920625 = 2190469) B2190469
theorem B1298611 : Blo 1297967 1298611 := bstep (se 1 (by rfl) ⟨973958, by rfl⟩ : syracuseStep 1298611 = 1947917) B1947917
theorem B2920643 : Blo 1297967 2920643 := bstep (se 1 (by rfl) ⟨2190482, by rfl⟩ : syracuseStep 2920643 = 4380965) B4380965
theorem B1298627 : Blo 1297967 1298627 := bstep (se 1 (by rfl) ⟨973970, by rfl⟩ : syracuseStep 1298627 = 1947941) B1947941
theorem B1298643 : Blo 1297967 1298643 := bstep (se 1 (by rfl) ⟨973982, by rfl⟩ : syracuseStep 1298643 = 1947965) B1947965
theorem B2773219 : Blo 1297967 2773219 := bstep (se 1 (by rfl) ⟨2079914, by rfl⟩ : syracuseStep 2773219 = 4159829) B4159829
theorem B1298659 : Blo 1297967 1298659 := bstep (se 1 (by rfl) ⟨973994, by rfl⟩ : syracuseStep 1298659 = 1947989) B1947989
theorem B11096291 : Blo 1297967 11096291 := bstep (se 1 (by rfl) ⟨8322218, by rfl⟩ : syracuseStep 11096291 = 16644437) B16644437
theorem B1298675 : Blo 1297967 1298675 := bstep (se 1 (by rfl) ⟨974006, by rfl⟩ : syracuseStep 1298675 = 1948013) B1948013
theorem B2191603 : Blo 1297967 2191603 := bstep (se 1 (by rfl) ⟨1643702, by rfl⟩ : syracuseStep 2191603 = 3287405) B3287405
theorem B1298691 : Blo 1297967 1298691 := bstep (se 1 (by rfl) ⟨974018, by rfl⟩ : syracuseStep 1298691 = 1948037) B1948037
theorem B1642771 : Blo 1297967 1642771 := bstep (se 1 (by rfl) ⟨1232078, by rfl⟩ : syracuseStep 1642771 = 2464157) B2464157
theorem B1298707 : Blo 1297967 1298707 := bstep (se 1 (by rfl) ⟨974030, by rfl⟩ : syracuseStep 1298707 = 1948061) B1948061
theorem B1298723 : Blo 1297967 1298723 := bstep (se 1 (by rfl) ⟨974042, by rfl⟩ : syracuseStep 1298723 = 1948085) B1948085
theorem B4387121 : Blo 1297967 4387121 := bstep (se 2 (by rfl) ⟨1645170, by rfl⟩ : syracuseStep 4387121 = 3290341) B3290341
theorem B1298739 : Blo 1297967 1298739 := bstep (se 1 (by rfl) ⟨974054, by rfl⟩ : syracuseStep 1298739 = 1948109) B1948109
theorem B1298755 : Blo 1297967 1298755 := bstep (se 1 (by rfl) ⟨974066, by rfl⟩ : syracuseStep 1298755 = 1948133) B1948133
theorem B1298771 : Blo 1297967 1298771 := bstep (se 1 (by rfl) ⟨974078, by rfl⟩ : syracuseStep 1298771 = 1948157) B1948157
theorem B1298787 : Blo 1297967 1298787 := bstep (se 1 (by rfl) ⟨974090, by rfl⟩ : syracuseStep 1298787 = 1948181) B1948181
theorem B1298803 : Blo 1297967 1298803 := bstep (se 1 (by rfl) ⟨974102, by rfl⟩ : syracuseStep 1298803 = 1948205) B1948205
theorem B2191745 : Blo 1297967 2191745 := bstep (se 2 (by rfl) ⟨821904, by rfl⟩ : syracuseStep 2191745 = 1643809) B1643809
theorem B1298819 : Blo 1297967 1298819 := bstep (se 1 (by rfl) ⟨974114, by rfl⟩ : syracuseStep 1298819 = 1948229) B1948229
theorem B4215181 : Blo 1297967 4215181 := bstep (se 3 (by rfl) ⟨790346, by rfl⟩ : syracuseStep 4215181 = 1580693) B1580693
theorem B2961809 : Blo 1297967 2961809 := bstep (se 2 (by rfl) ⟨1110678, by rfl⟩ : syracuseStep 2961809 = 2221357) B2221357
theorem B1298835 : Blo 1297967 1298835 := bstep (se 1 (by rfl) ⟨974126, by rfl⟩ : syracuseStep 1298835 = 1948253) B1948253
theorem B1298851 : Blo 1297967 1298851 := bstep (se 1 (by rfl) ⟨974138, by rfl⟩ : syracuseStep 1298851 = 1948277) B1948277
theorem B1298867 : Blo 1297967 1298867 := bstep (se 1 (by rfl) ⟨974150, by rfl⟩ : syracuseStep 1298867 = 1948301) B1948301
theorem B1298883 : Blo 1297967 1298883 := bstep (se 1 (by rfl) ⟨974162, by rfl⟩ : syracuseStep 1298883 = 1948325) B1948325
theorem B2920913 : Blo 1297967 2920913 := bstep (se 2 (by rfl) ⟨1095342, by rfl⟩ : syracuseStep 2920913 = 2190685) B2190685
theorem B4444625 : Blo 1297967 4444625 := bstep (se 2 (by rfl) ⟨1666734, by rfl⟩ : syracuseStep 4444625 = 3333469) B3333469
theorem B1298899 : Blo 1297967 1298899 := bstep (se 1 (by rfl) ⟨974174, by rfl⟩ : syracuseStep 1298899 = 1948349) B1948349
theorem B2920931 : Blo 1297967 2920931 := bstep (se 1 (by rfl) ⟨2190698, by rfl⟩ : syracuseStep 2920931 = 4381397) B4381397
theorem B1298915 : Blo 1297967 1298915 := bstep (se 1 (by rfl) ⟨974186, by rfl⟩ : syracuseStep 1298915 = 1948373) B1948373
theorem B1298931 : Blo 1297967 1298931 := bstep (se 1 (by rfl) ⟨974198, by rfl⟩ : syracuseStep 1298931 = 1948397) B1948397
theorem B2191873 : Blo 1297967 2191873 := bstep (se 2 (by rfl) ⟨821952, by rfl⟩ : syracuseStep 2191873 = 1643905) B1643905
theorem B1298947 : Blo 1297967 1298947 := bstep (se 1 (by rfl) ⟨974210, by rfl⟩ : syracuseStep 1298947 = 1948421) B1948421
theorem B1298963 : Blo 1297967 1298963 := bstep (se 1 (by rfl) ⟨974222, by rfl⟩ : syracuseStep 1298963 = 1948445) B1948445
theorem B2191907 : Blo 1297967 2191907 := bstep (se 1 (by rfl) ⟨1643930, by rfl⟩ : syracuseStep 2191907 = 3287861) B3287861
theorem B1298979 : Blo 1297967 1298979 := bstep (se 1 (by rfl) ⟨974234, by rfl⟩ : syracuseStep 1298979 = 1948469) B1948469
theorem B1298995 : Blo 1297967 1298995 := bstep (se 1 (by rfl) ⟨974246, by rfl⟩ : syracuseStep 1298995 = 1948493) B1948493
theorem B1299011 : Blo 1297967 1299011 := bstep (se 1 (by rfl) ⟨974258, by rfl⟩ : syracuseStep 1299011 = 1948517) B1948517
theorem B1299027 : Blo 1297967 1299027 := bstep (se 1 (by rfl) ⟨974270, by rfl⟩ : syracuseStep 1299027 = 1948541) B1948541
theorem B1299043 : Blo 1297967 1299043 := bstep (se 1 (by rfl) ⟨974282, by rfl⟩ : syracuseStep 1299043 = 1948565) B1948565
theorem B1299059 : Blo 1297967 1299059 := bstep (se 1 (by rfl) ⟨974294, by rfl⟩ : syracuseStep 1299059 = 1948589) B1948589
theorem B1299075 : Blo 1297967 1299075 := bstep (se 1 (by rfl) ⟨974306, by rfl⟩ : syracuseStep 1299075 = 1948613) B1948613
theorem B1299091 : Blo 1297967 1299091 := bstep (se 1 (by rfl) ⟨974318, by rfl⟩ : syracuseStep 1299091 = 1948637) B1948637
theorem B2192035 : Blo 1297967 2192035 := bstep (se 1 (by rfl) ⟨1644026, by rfl⟩ : syracuseStep 2192035 = 3288053) B3288053
theorem B1299107 : Blo 1297967 1299107 := bstep (se 1 (by rfl) ⟨974330, by rfl⟩ : syracuseStep 1299107 = 1948661) B1948661
theorem B6574769 : Blo 1297967 6574769 := bstep (se 2 (by rfl) ⟨2465538, by rfl⟩ : syracuseStep 6574769 = 4931077) B4931077
theorem B1299123 : Blo 1297967 1299123 := bstep (se 1 (by rfl) ⟨974342, by rfl⟩ : syracuseStep 1299123 = 1948685) B1948685
theorem B1299139 : Blo 1297967 1299139 := bstep (se 1 (by rfl) ⟨974354, by rfl⟩ : syracuseStep 1299139 = 1948709) B1948709
theorem B1299155 : Blo 1297967 1299155 := bstep (se 1 (by rfl) ⟨974366, by rfl⟩ : syracuseStep 1299155 = 1948733) B1948733
theorem B1299171 : Blo 1297967 1299171 := bstep (se 1 (by rfl) ⟨974378, by rfl⟩ : syracuseStep 1299171 = 1948757) B1948757
theorem B2921201 : Blo 1297967 2921201 := bstep (se 2 (by rfl) ⟨1095450, by rfl⟩ : syracuseStep 2921201 = 2190901) B2190901
theorem B14791409 : Blo 1297967 14791409 := bstep (se 2 (by rfl) ⟨5546778, by rfl⟩ : syracuseStep 14791409 = 11093557) B11093557
theorem B1299187 : Blo 1297967 1299187 := bstep (se 1 (by rfl) ⟨974390, by rfl⟩ : syracuseStep 1299187 = 1948781) B1948781
theorem B2921219 : Blo 1297967 2921219 := bstep (se 1 (by rfl) ⟨2190914, by rfl⟩ : syracuseStep 2921219 = 4381829) B4381829
theorem B1643267 : Blo 1297967 1643267 := bstep (se 1 (by rfl) ⟨1232450, by rfl⟩ : syracuseStep 1643267 = 2464901) B2464901
theorem B1299203 : Blo 1297967 1299203 := bstep (se 1 (by rfl) ⟨974402, by rfl⟩ : syracuseStep 1299203 = 1948805) B1948805
theorem B1299219 : Blo 1297967 1299219 := bstep (se 1 (by rfl) ⟨974414, by rfl⟩ : syracuseStep 1299219 = 1948829) B1948829
theorem B1299235 : Blo 1297967 1299235 := bstep (se 1 (by rfl) ⟨974426, by rfl⟩ : syracuseStep 1299235 = 1948853) B1948853
theorem B2192177 : Blo 1297967 2192177 := bstep (se 2 (by rfl) ⟨822066, by rfl⟩ : syracuseStep 2192177 = 1644133) B1644133
theorem B1299251 : Blo 1297967 1299251 := bstep (se 1 (by rfl) ⟨974438, by rfl⟩ : syracuseStep 1299251 = 1948877) B1948877
theorem B1299267 : Blo 1297967 1299267 := bstep (se 1 (by rfl) ⟨974450, by rfl⟩ : syracuseStep 1299267 = 1948901) B1948901
theorem B1299283 : Blo 1297967 1299283 := bstep (se 1 (by rfl) ⟨974462, by rfl⟩ : syracuseStep 1299283 = 1948925) B1948925
theorem B1299299 : Blo 1297967 1299299 := bstep (se 1 (by rfl) ⟨974474, by rfl⟩ : syracuseStep 1299299 = 1948949) B1948949
theorem B1299315 : Blo 1297967 1299315 := bstep (se 1 (by rfl) ⟨974486, by rfl⟩ : syracuseStep 1299315 = 1948973) B1948973
theorem B1299331 : Blo 1297967 1299331 := bstep (se 1 (by rfl) ⟨974498, by rfl⟩ : syracuseStep 1299331 = 1948997) B1948997
theorem B1299347 : Blo 1297967 1299347 := bstep (se 1 (by rfl) ⟨974510, by rfl⟩ : syracuseStep 1299347 = 1949021) B1949021
theorem B1299363 : Blo 1297967 1299363 := bstep (se 1 (by rfl) ⟨974522, by rfl⟩ : syracuseStep 1299363 = 1949045) B1949045
theorem B2192305 : Blo 1297967 2192305 := bstep (se 2 (by rfl) ⟨822114, by rfl⟩ : syracuseStep 2192305 = 1644229) B1644229
theorem B1299379 : Blo 1297967 1299379 := bstep (se 1 (by rfl) ⟨974534, by rfl⟩ : syracuseStep 1299379 = 1949069) B1949069
theorem B1299395 : Blo 1297967 1299395 := bstep (se 1 (by rfl) ⟨974546, by rfl⟩ : syracuseStep 1299395 = 1949093) B1949093
theorem B8319941 : Blo 1297967 8319941 := bstep (se 4 (by rfl) ⟨779994, by rfl⟩ : syracuseStep 8319941 = 1559989) B1559989
theorem B9868229 : Blo 1297967 9868229 := bstep (se 4 (by rfl) ⟨925146, by rfl⟩ : syracuseStep 9868229 = 1850293) B1850293
theorem B3699665 : Blo 1297967 3699665 := bstep (se 2 (by rfl) ⟨1387374, by rfl⟩ : syracuseStep 3699665 = 2774749) B2774749
theorem B2192339 : Blo 1297967 2192339 := bstep (se 1 (by rfl) ⟨1644254, by rfl⟩ : syracuseStep 2192339 = 3288509) B3288509
theorem B1299411 : Blo 1297967 1299411 := bstep (se 1 (by rfl) ⟨974558, by rfl⟩ : syracuseStep 1299411 = 1949117) B1949117
theorem B1299427 : Blo 1297967 1299427 := bstep (se 1 (by rfl) ⟨974570, by rfl⟩ : syracuseStep 1299427 = 1949141) B1949141
theorem B1299443 : Blo 1297967 1299443 := bstep (se 1 (by rfl) ⟨974582, by rfl⟩ : syracuseStep 1299443 = 1949165) B1949165
theorem B1299459 : Blo 1297967 1299459 := bstep (se 1 (by rfl) ⟨974594, by rfl⟩ : syracuseStep 1299459 = 1949189) B1949189
theorem B2921489 : Blo 1297967 2921489 := bstep (se 2 (by rfl) ⟨1095558, by rfl⟩ : syracuseStep 2921489 = 2191117) B2191117
theorem B1299475 : Blo 1297967 1299475 := bstep (se 1 (by rfl) ⟨974606, by rfl⟩ : syracuseStep 1299475 = 1949213) B1949213
theorem B3290129 : Blo 1297967 3290129 := bstep (se 2 (by rfl) ⟨1233798, by rfl⟩ : syracuseStep 3290129 = 2467597) B2467597
theorem B2921507 : Blo 1297967 2921507 := bstep (se 1 (by rfl) ⟨2191130, by rfl⟩ : syracuseStep 2921507 = 4382261) B4382261
theorem B2339875 : Blo 1297967 2339875 := bstep (se 1 (by rfl) ⟨1754906, by rfl⟩ : syracuseStep 2339875 = 3509813) B3509813
theorem B1299491 : Blo 1297967 1299491 := bstep (se 1 (by rfl) ⟨974618, by rfl⟩ : syracuseStep 1299491 = 1949237) B1949237
theorem B1299507 : Blo 1297967 1299507 := bstep (se 1 (by rfl) ⟨974630, by rfl⟩ : syracuseStep 1299507 = 1949261) B1949261
theorem B1299523 : Blo 1297967 1299523 := bstep (se 1 (by rfl) ⟨974642, by rfl⟩ : syracuseStep 1299523 = 1949285) B1949285
theorem B3290179 : Blo 1297967 3290179 := bstep (se 1 (by rfl) ⟨2467634, by rfl⟩ : syracuseStep 3290179 = 4935269) B4935269
theorem B2192467 : Blo 1297967 2192467 := bstep (se 1 (by rfl) ⟨1644350, by rfl⟩ : syracuseStep 2192467 = 3288701) B3288701
theorem B1299539 : Blo 1297967 1299539 := bstep (se 1 (by rfl) ⟨974654, by rfl⟩ : syracuseStep 1299539 = 1949309) B1949309
theorem B1299555 : Blo 1297967 1299555 := bstep (se 1 (by rfl) ⟨974666, by rfl⟩ : syracuseStep 1299555 = 1949333) B1949333
theorem B17773681 : Blo 1297967 17773681 := bstep (se 2 (by rfl) ⟨6665130, by rfl⟩ : syracuseStep 17773681 = 13330261) B13330261
theorem B10540145 : Blo 1297967 10540145 := bstep (se 2 (by rfl) ⟨3952554, by rfl⟩ : syracuseStep 10540145 = 7905109) B7905109
theorem B1299571 : Blo 1297967 1299571 := bstep (se 1 (by rfl) ⟨974678, by rfl⟩ : syracuseStep 1299571 = 1949357) B1949357
theorem B1299587 : Blo 1297967 1299587 := bstep (se 1 (by rfl) ⟨974690, by rfl⟩ : syracuseStep 1299587 = 1949381) B1949381
theorem B3699857 : Blo 1297967 3699857 := bstep (se 2 (by rfl) ⟨1387446, by rfl⟩ : syracuseStep 3699857 = 2774893) B2774893
theorem B1299603 : Blo 1297967 1299603 := bstep (se 1 (by rfl) ⟨974702, by rfl⟩ : syracuseStep 1299603 = 1949405) B1949405
theorem B1299619 : Blo 1297967 1299619 := bstep (se 1 (by rfl) ⟨974714, by rfl⟩ : syracuseStep 1299619 = 1949429) B1949429
theorem B1299635 : Blo 1297967 1299635 := bstep (se 1 (by rfl) ⟨974726, by rfl⟩ : syracuseStep 1299635 = 1949453) B1949453
theorem B1299651 : Blo 1297967 1299651 := bstep (se 1 (by rfl) ⟨974738, by rfl⟩ : syracuseStep 1299651 = 1949477) B1949477
theorem B2634947 : Blo 1297967 2634947 := bstep (se 1 (by rfl) ⟨1976210, by rfl⟩ : syracuseStep 2634947 = 3952421) B3952421
theorem B3290321 : Blo 1297967 3290321 := bstep (se 2 (by rfl) ⟨1233870, by rfl⟩ : syracuseStep 3290321 = 2467741) B2467741
theorem B1299667 : Blo 1297967 1299667 := bstep (se 1 (by rfl) ⟨974750, by rfl⟩ : syracuseStep 1299667 = 1949501) B1949501
theorem B2192609 : Blo 1297967 2192609 := bstep (se 2 (by rfl) ⟨822228, by rfl⟩ : syracuseStep 2192609 = 1644457) B1644457
theorem B1299683 : Blo 1297967 1299683 := bstep (se 1 (by rfl) ⟨974762, by rfl⟩ : syracuseStep 1299683 = 1949525) B1949525
theorem B1299699 : Blo 1297967 1299699 := bstep (se 1 (by rfl) ⟨974774, by rfl⟩ : syracuseStep 1299699 = 1949549) B1949549
theorem B1299715 : Blo 1297967 1299715 := bstep (se 1 (by rfl) ⟨974786, by rfl⟩ : syracuseStep 1299715 = 1949573) B1949573
theorem B1299731 : Blo 1297967 1299731 := bstep (se 1 (by rfl) ⟨974798, by rfl⟩ : syracuseStep 1299731 = 1949597) B1949597
theorem B1299747 : Blo 1297967 1299747 := bstep (se 1 (by rfl) ⟨974810, by rfl⟩ : syracuseStep 1299747 = 1949621) B1949621
theorem B2921777 : Blo 1297967 2921777 := bstep (se 2 (by rfl) ⟨1095666, by rfl⟩ : syracuseStep 2921777 = 2191333) B2191333
theorem B1299763 : Blo 1297967 1299763 := bstep (se 1 (by rfl) ⟨974822, by rfl⟩ : syracuseStep 1299763 = 1949645) B1949645
theorem B2921795 : Blo 1297967 2921795 := bstep (se 1 (by rfl) ⟨2191346, by rfl⟩ : syracuseStep 2921795 = 4382693) B4382693
theorem B1299779 : Blo 1297967 1299779 := bstep (se 1 (by rfl) ⟨974834, by rfl⟩ : syracuseStep 1299779 = 1949669) B1949669
theorem B1946963 : Blo 1297967 1946963 := bstep (se 1 (by rfl) ⟨1460222, by rfl⟩ : syracuseStep 1946963 = 2920445) B2920445
theorem B1299795 : Blo 1297967 1299795 := bstep (se 1 (by rfl) ⟨974846, by rfl⟩ : syracuseStep 1299795 = 1949693) B1949693
theorem B2192737 : Blo 1297967 2192737 := bstep (se 2 (by rfl) ⟨822276, by rfl⟩ : syracuseStep 2192737 = 1644553) B1644553
theorem B1299811 : Blo 1297967 1299811 := bstep (se 1 (by rfl) ⟨974858, by rfl⟩ : syracuseStep 1299811 = 1949717) B1949717
theorem B1946993 : Blo 1297967 1946993 := bstep (se 2 (by rfl) ⟨730122, by rfl⟩ : syracuseStep 1946993 = 1460245) B1460245
theorem B1299827 : Blo 1297967 1299827 := bstep (se 1 (by rfl) ⟨974870, by rfl⟩ : syracuseStep 1299827 = 1949741) B1949741
theorem B1947011 : Blo 1297967 1947011 := bstep (se 1 (by rfl) ⟨1460258, by rfl⟩ : syracuseStep 1947011 = 2920517) B2920517
theorem B2192771 : Blo 1297967 2192771 := bstep (se 1 (by rfl) ⟨1644578, by rfl⟩ : syracuseStep 2192771 = 3289157) B3289157
theorem B1299843 : Blo 1297967 1299843 := bstep (se 1 (by rfl) ⟨974882, by rfl⟩ : syracuseStep 1299843 = 1949765) B1949765
theorem B1299859 : Blo 1297967 1299859 := bstep (se 1 (by rfl) ⟨974894, by rfl⟩ : syracuseStep 1299859 = 1949789) B1949789
theorem B1947041 : Blo 1297967 1947041 := bstep (se 2 (by rfl) ⟨730140, by rfl⟩ : syracuseStep 1947041 = 1460281) B1460281
theorem B1848739 : Blo 1297967 1848739 := bstep (se 1 (by rfl) ⟨1386554, by rfl⟩ : syracuseStep 1848739 = 2773109) B2773109
theorem B1299875 : Blo 1297967 1299875 := bstep (se 1 (by rfl) ⟨974906, by rfl⟩ : syracuseStep 1299875 = 1949813) B1949813
theorem B2774449 : Blo 1297967 2774449 := bstep (se 2 (by rfl) ⟨1040418, by rfl⟩ : syracuseStep 2774449 = 2080837) B2080837
theorem B1947059 : Blo 1297967 1947059 := bstep (se 1 (by rfl) ⟨1460294, by rfl⟩ : syracuseStep 1947059 = 2920589) B2920589
theorem B1299891 : Blo 1297967 1299891 := bstep (se 1 (by rfl) ⟨974918, by rfl⟩ : syracuseStep 1299891 = 1949837) B1949837
theorem B1643971 : Blo 1297967 1643971 := bstep (se 1 (by rfl) ⟨1232978, by rfl⟩ : syracuseStep 1643971 = 2465957) B2465957
theorem B1299907 : Blo 1297967 1299907 := bstep (se 1 (by rfl) ⟨974930, by rfl⟩ : syracuseStep 1299907 = 1949861) B1949861
theorem B1947089 : Blo 1297967 1947089 := bstep (se 2 (by rfl) ⟨730158, by rfl⟩ : syracuseStep 1947089 = 1460317) B1460317
theorem B1299923 : Blo 1297967 1299923 := bstep (se 1 (by rfl) ⟨974942, by rfl⟩ : syracuseStep 1299923 = 1949885) B1949885
theorem B1947107 : Blo 1297967 1947107 := bstep (se 1 (by rfl) ⟨1460330, by rfl⟩ : syracuseStep 1947107 = 2920661) B2920661
theorem B1299939 : Blo 1297967 1299939 := bstep (se 1 (by rfl) ⟨974954, by rfl⟩ : syracuseStep 1299939 = 1949909) B1949909
theorem B1299955 : Blo 1297967 1299955 := bstep (se 1 (by rfl) ⟨974966, by rfl⟩ : syracuseStep 1299955 = 1949933) B1949933
theorem B1947137 : Blo 1297967 1947137 := bstep (se 2 (by rfl) ⟨730176, by rfl⟩ : syracuseStep 1947137 = 1460353) B1460353
theorem B1848835 : Blo 1297967 1848835 := bstep (se 1 (by rfl) ⟨1386626, by rfl⟩ : syracuseStep 1848835 = 2773253) B2773253
theorem B2192899 : Blo 1297967 2192899 := bstep (se 1 (by rfl) ⟨1644674, by rfl⟩ : syracuseStep 2192899 = 3289349) B3289349
theorem B1947155 : Blo 1297967 1947155 := bstep (se 1 (by rfl) ⟨1460366, by rfl⟩ : syracuseStep 1947155 = 2920733) B2920733
theorem B1644067 : Blo 1297967 1644067 := bstep (se 1 (by rfl) ⟨1233050, by rfl⟩ : syracuseStep 1644067 = 2466101) B2466101
theorem B1947185 : Blo 1297967 1947185 := bstep (se 2 (by rfl) ⟨730194, by rfl⟩ : syracuseStep 1947185 = 1460389) B1460389
theorem B1947203 : Blo 1297967 1947203 := bstep (se 1 (by rfl) ⟨1460402, by rfl⟩ : syracuseStep 1947203 = 2920805) B2920805
theorem B7394885 : Blo 1297967 7394885 := bstep (se 4 (by rfl) ⟨693270, by rfl⟩ : syracuseStep 7394885 = 1386541) B1386541
theorem B2922065 : Blo 1297967 2922065 := bstep (se 2 (by rfl) ⟨1095774, by rfl⟩ : syracuseStep 2922065 = 2191549) B2191549
theorem B1947233 : Blo 1297967 1947233 := bstep (se 2 (by rfl) ⟨730212, by rfl⟩ : syracuseStep 1947233 = 1460425) B1460425
theorem B2922083 : Blo 1297967 2922083 := bstep (se 1 (by rfl) ⟨2191562, by rfl⟩ : syracuseStep 2922083 = 4383125) B4383125
theorem B1947251 : Blo 1297967 1947251 := bstep (se 1 (by rfl) ⟨1460438, by rfl⟩ : syracuseStep 1947251 = 2920877) B2920877
theorem B1947281 : Blo 1297967 1947281 := bstep (se 2 (by rfl) ⟨730230, by rfl⟩ : syracuseStep 1947281 = 1460461) B1460461
theorem B2193041 : Blo 1297967 2193041 := bstep (se 2 (by rfl) ⟨822390, by rfl⟩ : syracuseStep 2193041 = 1644781) B1644781
theorem B2635409 : Blo 1297967 2635409 := bstep (se 2 (by rfl) ⟨988278, by rfl⟩ : syracuseStep 2635409 = 1976557) B1976557
theorem B1947299 : Blo 1297967 1947299 := bstep (se 1 (by rfl) ⟨1460474, by rfl⟩ : syracuseStep 1947299 = 2920949) B2920949
theorem B1947329 : Blo 1297967 1947329 := bstep (se 2 (by rfl) ⟨730248, by rfl⟩ : syracuseStep 1947329 = 1460497) B1460497
theorem B1947347 : Blo 1297967 1947347 := bstep (se 1 (by rfl) ⟨1460510, by rfl⟩ : syracuseStep 1947347 = 2921021) B2921021
theorem B1947377 : Blo 1297967 1947377 := bstep (se 2 (by rfl) ⟨730266, by rfl⟩ : syracuseStep 1947377 = 1460533) B1460533
theorem B1947395 : Blo 1297967 1947395 := bstep (se 1 (by rfl) ⟨1460546, by rfl⟩ : syracuseStep 1947395 = 2921093) B2921093
theorem B2193169 : Blo 1297967 2193169 := bstep (se 2 (by rfl) ⟨822438, by rfl⟩ : syracuseStep 2193169 = 1644877) B1644877
theorem B1947425 : Blo 1297967 1947425 := bstep (se 2 (by rfl) ⟨730284, by rfl⟩ : syracuseStep 1947425 = 1460569) B1460569
theorem B1947443 : Blo 1297967 1947443 := bstep (se 1 (by rfl) ⟨1460582, by rfl⟩ : syracuseStep 1947443 = 2921165) B2921165
theorem B2193203 : Blo 1297967 2193203 := bstep (se 1 (by rfl) ⟨1644902, by rfl⟩ : syracuseStep 2193203 = 3289805) B3289805
theorem B22484789 : Blo 1297967 22484789 := bstep (se 5 (by rfl) ⟨1053974, by rfl⟩ : syracuseStep 22484789 = 2107949) B2107949
theorem B1947473 : Blo 1297967 1947473 := bstep (se 2 (by rfl) ⟨730302, by rfl⟩ : syracuseStep 1947473 = 1460605) B1460605
theorem B1947491 : Blo 1297967 1947491 := bstep (se 1 (by rfl) ⟨1460618, by rfl⟩ : syracuseStep 1947491 = 2921237) B2921237
theorem B13522787 : Blo 1297967 13522787 := bstep (se 1 (by rfl) ⟨10142090, by rfl⟩ : syracuseStep 13522787 = 20284181) B20284181
theorem B2922353 : Blo 1297967 2922353 := bstep (se 2 (by rfl) ⟨1095882, by rfl⟩ : syracuseStep 2922353 = 2191765) B2191765
theorem B1947521 : Blo 1297967 1947521 := bstep (se 2 (by rfl) ⟨730320, by rfl⟩ : syracuseStep 1947521 = 1460641) B1460641
theorem B2922371 : Blo 1297967 2922371 := bstep (se 1 (by rfl) ⟨2191778, by rfl⟩ : syracuseStep 2922371 = 4383557) B4383557
theorem B16013197 : Blo 1297967 16013197 := bstep (se 3 (by rfl) ⟨3002474, by rfl⟩ : syracuseStep 16013197 = 6004949) B6004949
theorem B1947539 : Blo 1297967 1947539 := bstep (se 1 (by rfl) ⟨1460654, by rfl⟩ : syracuseStep 1947539 = 2921309) B2921309
theorem B1947569 : Blo 1297967 1947569 := bstep (se 2 (by rfl) ⟨730338, by rfl⟩ : syracuseStep 1947569 = 1460677) B1460677
theorem B2193331 : Blo 1297967 2193331 := bstep (se 1 (by rfl) ⟨1644998, by rfl⟩ : syracuseStep 2193331 = 3289997) B3289997
theorem B1947587 : Blo 1297967 1947587 := bstep (se 1 (by rfl) ⟨1460690, by rfl⟩ : syracuseStep 1947587 = 2921381) B2921381
theorem B4446161 : Blo 1297967 4446161 := bstep (se 2 (by rfl) ⟨1667310, by rfl⟩ : syracuseStep 4446161 = 3334621) B3334621
theorem B1947617 : Blo 1297967 1947617 := bstep (se 2 (by rfl) ⟨730356, by rfl⟩ : syracuseStep 1947617 = 1460713) B1460713
theorem B4159469 : Blo 1297967 4159469 := bstep (se 3 (by rfl) ⟨779900, by rfl⟩ : syracuseStep 4159469 = 1559801) B1559801
theorem B1947635 : Blo 1297967 1947635 := bstep (se 1 (by rfl) ⟨1460726, by rfl⟩ : syracuseStep 1947635 = 2921453) B2921453
theorem B1849331 : Blo 1297967 1849331 := bstep (se 1 (by rfl) ⟨1386998, by rfl⟩ : syracuseStep 1849331 = 2773997) B2773997
theorem B1947665 : Blo 1297967 1947665 := bstep (se 2 (by rfl) ⟨730374, by rfl⟩ : syracuseStep 1947665 = 1460749) B1460749
theorem B1644563 : Blo 1297967 1644563 := bstep (se 1 (by rfl) ⟨1233422, by rfl⟩ : syracuseStep 1644563 = 2466845) B2466845
theorem B1947683 : Blo 1297967 1947683 := bstep (se 1 (by rfl) ⟨1460762, by rfl⟩ : syracuseStep 1947683 = 2921525) B2921525
theorem B5068835 : Blo 1297967 5068835 := bstep (se 1 (by rfl) ⟨3801626, by rfl⟩ : syracuseStep 5068835 = 7603253) B7603253
theorem B1947713 : Blo 1297967 1947713 := bstep (se 2 (by rfl) ⟨730392, by rfl⟩ : syracuseStep 1947713 = 1460785) B1460785
theorem B2193473 : Blo 1297967 2193473 := bstep (se 2 (by rfl) ⟨822552, by rfl⟩ : syracuseStep 2193473 = 1645105) B1645105
theorem B4380749 : Blo 1297967 4380749 := bstep (se 3 (by rfl) ⟨821390, by rfl⟩ : syracuseStep 4380749 = 1642781) B1642781
theorem B3749969 : Blo 1297967 3749969 := bstep (se 2 (by rfl) ⟨1406238, by rfl⟩ : syracuseStep 3749969 = 2812477) B2812477
theorem B1947731 : Blo 1297967 1947731 := bstep (se 1 (by rfl) ⟨1460798, by rfl⟩ : syracuseStep 1947731 = 2921597) B2921597
theorem B6576227 : Blo 1297967 6576227 := bstep (se 1 (by rfl) ⟨4932170, by rfl⟩ : syracuseStep 6576227 = 9864341) B9864341
theorem B1947761 : Blo 1297967 1947761 := bstep (se 2 (by rfl) ⟨730410, by rfl⟩ : syracuseStep 1947761 = 1460821) B1460821
theorem B3700849 : Blo 1297967 3700849 := bstep (se 2 (by rfl) ⟨1387818, by rfl⟩ : syracuseStep 3700849 = 2775637) B2775637
theorem B7403633 : Blo 1297967 7403633 := bstep (se 2 (by rfl) ⟨2776362, by rfl⟩ : syracuseStep 7403633 = 5552725) B5552725
theorem B4380803 : Blo 1297967 4380803 := bstep (se 1 (by rfl) ⟨3285602, by rfl⟩ : syracuseStep 4380803 = 6571205) B6571205
theorem B1947779 : Blo 1297967 1947779 := bstep (se 1 (by rfl) ⟨1460834, by rfl⟩ : syracuseStep 1947779 = 2921669) B2921669
theorem B2922641 : Blo 1297967 2922641 := bstep (se 2 (by rfl) ⟨1095990, by rfl⟩ : syracuseStep 2922641 = 2191981) B2191981
theorem B1947809 : Blo 1297967 1947809 := bstep (se 2 (by rfl) ⟨730428, by rfl⟩ : syracuseStep 1947809 = 1460857) B1460857
theorem B2922659 : Blo 1297967 2922659 := bstep (se 1 (by rfl) ⟨2191994, by rfl⟩ : syracuseStep 2922659 = 4383989) B4383989
theorem B1947827 : Blo 1297967 1947827 := bstep (se 1 (by rfl) ⟨1460870, by rfl⟩ : syracuseStep 1947827 = 2921741) B2921741
theorem B2193601 : Blo 1297967 2193601 := bstep (se 2 (by rfl) ⟨822600, by rfl⟩ : syracuseStep 2193601 = 1645201) B1645201
theorem B2775235 : Blo 1297967 2775235 := bstep (se 1 (by rfl) ⟨2081426, by rfl⟩ : syracuseStep 2775235 = 4162853) B4162853
theorem B5626061 : Blo 1297967 5626061 := bstep (se 3 (by rfl) ⟨1054886, by rfl⟩ : syracuseStep 5626061 = 2109773) B2109773
theorem B1947857 : Blo 1297967 1947857 := bstep (se 2 (by rfl) ⟨730446, by rfl⟩ : syracuseStep 1947857 = 1460893) B1460893
theorem B1947875 : Blo 1297967 1947875 := bstep (se 1 (by rfl) ⟨1460906, by rfl⟩ : syracuseStep 1947875 = 2921813) B2921813
theorem B2193635 : Blo 1297967 2193635 := bstep (se 1 (by rfl) ⟨1645226, by rfl⟩ : syracuseStep 2193635 = 3290453) B3290453
theorem B7395569 : Blo 1297967 7395569 := bstep (se 2 (by rfl) ⟨2773338, by rfl⟩ : syracuseStep 7395569 = 5546677) B5546677
theorem B1947905 : Blo 1297967 1947905 := bstep (se 2 (by rfl) ⟨730464, by rfl⟩ : syracuseStep 1947905 = 1460929) B1460929
theorem B1947923 : Blo 1297967 1947923 := bstep (se 1 (by rfl) ⟨1460942, by rfl⟩ : syracuseStep 1947923 = 2921885) B2921885
theorem B2373905 : Blo 1297967 2373905 := bstep (se 2 (by rfl) ⟨890214, by rfl⟩ : syracuseStep 2373905 = 1780429) B1780429
theorem B5921059 : Blo 1297967 5921059 := bstep (se 1 (by rfl) ⟨4440794, by rfl⟩ : syracuseStep 5921059 = 8881589) B8881589
theorem B1947953 : Blo 1297967 1947953 := bstep (se 2 (by rfl) ⟨730482, by rfl⟩ : syracuseStep 1947953 = 1460965) B1460965
theorem B1947971 : Blo 1297967 1947971 := bstep (se 1 (by rfl) ⟨1460978, by rfl⟩ : syracuseStep 1947971 = 2921957) B2921957
theorem B1948001 : Blo 1297967 1948001 := bstep (se 2 (by rfl) ⟨730500, by rfl⟩ : syracuseStep 1948001 = 1461001) B1461001
theorem B1948019 : Blo 1297967 1948019 := bstep (se 1 (by rfl) ⟨1461014, by rfl⟩ : syracuseStep 1948019 = 2922029) B2922029
theorem B3701123 : Blo 1297967 3701123 := bstep (se 1 (by rfl) ⟨2775842, by rfl⟩ : syracuseStep 3701123 = 5551685) B5551685
theorem B7494029 : Blo 1297967 7494029 := bstep (se 3 (by rfl) ⟨1405130, by rfl⟩ : syracuseStep 7494029 = 2810261) B2810261
theorem B4381073 : Blo 1297967 4381073 := bstep (se 2 (by rfl) ⟨1642902, by rfl⟩ : syracuseStep 4381073 = 3285805) B3285805
theorem B1948049 : Blo 1297967 1948049 := bstep (se 2 (by rfl) ⟨730518, by rfl⟩ : syracuseStep 1948049 = 1461037) B1461037
theorem B4159907 : Blo 1297967 4159907 := bstep (se 1 (by rfl) ⟨3119930, by rfl⟩ : syracuseStep 4159907 = 6239861) B6239861
theorem B1948067 : Blo 1297967 1948067 := bstep (se 1 (by rfl) ⟨1461050, by rfl⟩ : syracuseStep 1948067 = 2922101) B2922101
theorem B2922929 : Blo 1297967 2922929 := bstep (se 2 (by rfl) ⟨1096098, by rfl⟩ : syracuseStep 2922929 = 2192197) B2192197
theorem B1948097 : Blo 1297967 1948097 := bstep (se 2 (by rfl) ⟨730536, by rfl⟩ : syracuseStep 1948097 = 1461073) B1461073
theorem B2464195 : Blo 1297967 2464195 := bstep (se 1 (by rfl) ⟨1848146, by rfl⟩ : syracuseStep 2464195 = 3696293) B3696293
theorem B2922947 : Blo 1297967 2922947 := bstep (se 1 (by rfl) ⟨2192210, by rfl⟩ : syracuseStep 2922947 = 4384421) B4384421
theorem B1948115 : Blo 1297967 1948115 := bstep (se 1 (by rfl) ⟨1461086, by rfl⟩ : syracuseStep 1948115 = 2922173) B2922173
theorem B1948145 : Blo 1297967 1948145 := bstep (se 2 (by rfl) ⟨730554, by rfl⟩ : syracuseStep 1948145 = 1461109) B1461109
theorem B1948163 : Blo 1297967 1948163 := bstep (se 1 (by rfl) ⟨1461122, by rfl⟩ : syracuseStep 1948163 = 2922245) B2922245
theorem B4446733 : Blo 1297967 4446733 := bstep (se 3 (by rfl) ⟨833762, by rfl⟩ : syracuseStep 4446733 = 1667525) B1667525
theorem B1948193 : Blo 1297967 1948193 := bstep (se 2 (by rfl) ⟨730572, by rfl⟩ : syracuseStep 1948193 = 1461145) B1461145
theorem B1948211 : Blo 1297967 1948211 := bstep (se 1 (by rfl) ⟨1461158, by rfl⟩ : syracuseStep 1948211 = 2922317) B2922317
theorem B3701315 : Blo 1297967 3701315 := bstep (se 1 (by rfl) ⟨2775986, by rfl⟩ : syracuseStep 3701315 = 5551973) B5551973
theorem B1948241 : Blo 1297967 1948241 := bstep (se 2 (by rfl) ⟨730590, by rfl⟩ : syracuseStep 1948241 = 1461181) B1461181
theorem B1948259 : Blo 1297967 1948259 := bstep (se 1 (by rfl) ⟨1461194, by rfl⟩ : syracuseStep 1948259 = 2922389) B2922389
theorem B1849969 : Blo 1297967 1849969 := bstep (se 2 (by rfl) ⟨693738, by rfl⟩ : syracuseStep 1849969 = 1387477) B1387477
theorem B1948289 : Blo 1297967 1948289 := bstep (se 2 (by rfl) ⟨730608, by rfl⟩ : syracuseStep 1948289 = 1461217) B1461217
theorem B1948307 : Blo 1297967 1948307 := bstep (se 1 (by rfl) ⟨1461230, by rfl⟩ : syracuseStep 1948307 = 2922461) B2922461
theorem B1948337 : Blo 1297967 1948337 := bstep (se 2 (by rfl) ⟨730626, by rfl⟩ : syracuseStep 1948337 = 1461253) B1461253
theorem B1948355 : Blo 1297967 1948355 := bstep (se 1 (by rfl) ⟨1461266, by rfl⟩ : syracuseStep 1948355 = 2922533) B2922533
theorem B2923217 : Blo 1297967 2923217 := bstep (se 2 (by rfl) ⟨1096206, by rfl⟩ : syracuseStep 2923217 = 2192413) B2192413
theorem B1645267 : Blo 1297967 1645267 := bstep (se 1 (by rfl) ⟨1233950, by rfl⟩ : syracuseStep 1645267 = 2467901) B2467901
theorem B1948385 : Blo 1297967 1948385 := bstep (se 2 (by rfl) ⟨730644, by rfl⟩ : syracuseStep 1948385 = 1461289) B1461289
theorem B2923235 : Blo 1297967 2923235 := bstep (se 1 (by rfl) ⟨2192426, by rfl⟩ : syracuseStep 2923235 = 4384853) B4384853
theorem B1948403 : Blo 1297967 1948403 := bstep (se 1 (by rfl) ⟨1461302, by rfl⟩ : syracuseStep 1948403 = 2922605) B2922605
theorem B1948433 : Blo 1297967 1948433 := bstep (se 2 (by rfl) ⟨730662, by rfl⟩ : syracuseStep 1948433 = 1461325) B1461325
theorem B1948451 : Blo 1297967 1948451 := bstep (se 1 (by rfl) ⟨1461338, by rfl⟩ : syracuseStep 1948451 = 2922677) B2922677
theorem B1948481 : Blo 1297967 1948481 := bstep (se 2 (by rfl) ⟨730680, by rfl⟩ : syracuseStep 1948481 = 1461361) B1461361
theorem B1948499 : Blo 1297967 1948499 := bstep (se 1 (by rfl) ⟨1461374, by rfl⟩ : syracuseStep 1948499 = 2922749) B2922749
theorem B1948529 : Blo 1297967 1948529 := bstep (se 2 (by rfl) ⟨730698, by rfl⟩ : syracuseStep 1948529 = 1461397) B1461397
theorem B2464643 : Blo 1297967 2464643 := bstep (se 1 (by rfl) ⟨1848482, by rfl⟩ : syracuseStep 2464643 = 3696965) B3696965
theorem B1948547 : Blo 1297967 1948547 := bstep (se 1 (by rfl) ⟨1461410, by rfl⟩ : syracuseStep 1948547 = 2922821) B2922821
theorem B6577037 : Blo 1297967 6577037 := bstep (se 3 (by rfl) ⟨1233194, by rfl⟩ : syracuseStep 6577037 = 2466389) B2466389
theorem B2775953 : Blo 1297967 2775953 := bstep (se 2 (by rfl) ⟨1040982, by rfl⟩ : syracuseStep 2775953 = 2081965) B2081965
theorem B1948577 : Blo 1297967 1948577 := bstep (se 2 (by rfl) ⟨730716, by rfl⟩ : syracuseStep 1948577 = 1461433) B1461433
theorem B4381613 : Blo 1297967 4381613 := bstep (se 3 (by rfl) ⟨821552, by rfl⟩ : syracuseStep 4381613 = 1643105) B1643105
theorem B1948595 : Blo 1297967 1948595 := bstep (se 1 (by rfl) ⟨1461446, by rfl⟩ : syracuseStep 1948595 = 2922893) B2922893
theorem B1850305 : Blo 1297967 1850305 := bstep (se 2 (by rfl) ⟨693864, by rfl⟩ : syracuseStep 1850305 = 1387729) B1387729
theorem B2079697 : Blo 1297967 2079697 := bstep (se 2 (by rfl) ⟨779886, by rfl⟩ : syracuseStep 2079697 = 1559773) B1559773
theorem B1948625 : Blo 1297967 1948625 := bstep (se 2 (by rfl) ⟨730734, by rfl⟩ : syracuseStep 1948625 = 1461469) B1461469
theorem B4381667 : Blo 1297967 4381667 := bstep (se 1 (by rfl) ⟨3286250, by rfl⟩ : syracuseStep 4381667 = 6572501) B6572501
theorem B1948643 : Blo 1297967 1948643 := bstep (se 1 (by rfl) ⟨1461482, by rfl⟩ : syracuseStep 1948643 = 2922965) B2922965
theorem B2923505 : Blo 1297967 2923505 := bstep (se 2 (by rfl) ⟨1096314, by rfl⟩ : syracuseStep 2923505 = 2192629) B2192629
theorem B1948673 : Blo 1297967 1948673 := bstep (se 2 (by rfl) ⟨730752, by rfl⟩ : syracuseStep 1948673 = 1461505) B1461505
theorem B2923523 : Blo 1297967 2923523 := bstep (se 1 (by rfl) ⟨2192642, by rfl⟩ : syracuseStep 2923523 = 4385285) B4385285
theorem B1948691 : Blo 1297967 1948691 := bstep (se 1 (by rfl) ⟨1461518, by rfl⟩ : syracuseStep 1948691 = 2923037) B2923037
theorem B1948721 : Blo 1297967 1948721 := bstep (se 2 (by rfl) ⟨730770, by rfl⟩ : syracuseStep 1948721 = 1461541) B1461541
theorem B1948739 : Blo 1297967 1948739 := bstep (se 1 (by rfl) ⟨1461554, by rfl⟩ : syracuseStep 1948739 = 2923109) B2923109
theorem B5545037 : Blo 1297967 5545037 := bstep (se 3 (by rfl) ⟨1039694, by rfl⟩ : syracuseStep 5545037 = 2079389) B2079389
theorem B1948769 : Blo 1297967 1948769 := bstep (se 2 (by rfl) ⟨730788, by rfl⟩ : syracuseStep 1948769 = 1461577) B1461577
theorem B1948787 : Blo 1297967 1948787 := bstep (se 1 (by rfl) ⟨1461590, by rfl⟩ : syracuseStep 1948787 = 2923181) B2923181
theorem B1948817 : Blo 1297967 1948817 := bstep (se 2 (by rfl) ⟨730806, by rfl⟩ : syracuseStep 1948817 = 1461613) B1461613
theorem B2464931 : Blo 1297967 2464931 := bstep (se 1 (by rfl) ⟨1848698, by rfl⟩ : syracuseStep 2464931 = 3697397) B3697397
theorem B1948835 : Blo 1297967 1948835 := bstep (se 1 (by rfl) ⟨1461626, by rfl⟩ : syracuseStep 1948835 = 2923253) B2923253
theorem B5921969 : Blo 1297967 5921969 := bstep (se 2 (by rfl) ⟨2220738, by rfl⟩ : syracuseStep 5921969 = 4441477) B4441477
theorem B1948865 : Blo 1297967 1948865 := bstep (se 2 (by rfl) ⟨730824, by rfl⟩ : syracuseStep 1948865 = 1461649) B1461649
theorem B1948883 : Blo 1297967 1948883 := bstep (se 1 (by rfl) ⟨1461662, by rfl⟩ : syracuseStep 1948883 = 2923325) B2923325
theorem B4381937 : Blo 1297967 4381937 := bstep (se 2 (by rfl) ⟨1643226, by rfl⟩ : syracuseStep 4381937 = 3286453) B3286453
theorem B1948913 : Blo 1297967 1948913 := bstep (se 2 (by rfl) ⟨730842, by rfl⟩ : syracuseStep 1948913 = 1461685) B1461685
theorem B1948931 : Blo 1297967 1948931 := bstep (se 1 (by rfl) ⟨1461698, by rfl⟩ : syracuseStep 1948931 = 2923397) B2923397
theorem B2923793 : Blo 1297967 2923793 := bstep (se 2 (by rfl) ⟨1096422, by rfl⟩ : syracuseStep 2923793 = 2192845) B2192845
theorem B60833045 : Blo 1297967 60833045 := bstep (se 6 (by rfl) ⟨1425774, by rfl⟩ : syracuseStep 60833045 = 2851549) B2851549
theorem B1948961 : Blo 1297967 1948961 := bstep (se 2 (by rfl) ⟨730860, by rfl⟩ : syracuseStep 1948961 = 1461721) B1461721
theorem B2923811 : Blo 1297967 2923811 := bstep (se 1 (by rfl) ⟨2192858, by rfl⟩ : syracuseStep 2923811 = 4385717) B4385717
theorem B4930865 : Blo 1297967 4930865 := bstep (se 2 (by rfl) ⟨1849074, by rfl⟩ : syracuseStep 4930865 = 3698149) B3698149
theorem B1948979 : Blo 1297967 1948979 := bstep (se 1 (by rfl) ⟨1461734, by rfl⟩ : syracuseStep 1948979 = 2923469) B2923469
theorem B1949009 : Blo 1297967 1949009 := bstep (se 2 (by rfl) ⟨730878, by rfl⟩ : syracuseStep 1949009 = 1461757) B1461757
theorem B1949027 : Blo 1297967 1949027 := bstep (se 1 (by rfl) ⟨1461770, by rfl⟩ : syracuseStep 1949027 = 2923541) B2923541
theorem B2252161 : Blo 1297967 2252161 := bstep (se 2 (by rfl) ⟨844560, by rfl⟩ : syracuseStep 2252161 = 1689121) B1689121
theorem B1949057 : Blo 1297967 1949057 := bstep (se 2 (by rfl) ⟨730896, by rfl⟩ : syracuseStep 1949057 = 1461793) B1461793
theorem B2080145 : Blo 1297967 2080145 := bstep (se 2 (by rfl) ⟨780054, by rfl⟩ : syracuseStep 2080145 = 1560109) B1560109
theorem B1949075 : Blo 1297967 1949075 := bstep (se 1 (by rfl) ⟨1461806, by rfl⟩ : syracuseStep 1949075 = 2923613) B2923613
theorem B1949105 : Blo 1297967 1949105 := bstep (se 2 (by rfl) ⟨730914, by rfl⟩ : syracuseStep 1949105 = 1461829) B1461829
theorem B1949123 : Blo 1297967 1949123 := bstep (se 1 (by rfl) ⟨1461842, by rfl⟩ : syracuseStep 1949123 = 2923685) B2923685
theorem B1949153 : Blo 1297967 1949153 := bstep (se 2 (by rfl) ⟨730932, by rfl⟩ : syracuseStep 1949153 = 1461865) B1461865
theorem B1949171 : Blo 1297967 1949171 := bstep (se 1 (by rfl) ⟨1461878, by rfl⟩ : syracuseStep 1949171 = 2923757) B2923757
theorem B9362957 : Blo 1297967 9362957 := bstep (se 3 (by rfl) ⟨1755554, by rfl⟩ : syracuseStep 9362957 = 3511109) B3511109
theorem B1949201 : Blo 1297967 1949201 := bstep (se 2 (by rfl) ⟨730950, by rfl⟩ : syracuseStep 1949201 = 1461901) B1461901
theorem B1850897 : Blo 1297967 1850897 := bstep (se 2 (by rfl) ⟨694086, by rfl⟩ : syracuseStep 1850897 = 1388173) B1388173
theorem B1949219 : Blo 1297967 1949219 := bstep (se 1 (by rfl) ⟨1461914, by rfl⟩ : syracuseStep 1949219 = 2923829) B2923829
theorem B2924081 : Blo 1297967 2924081 := bstep (se 2 (by rfl) ⟨1096530, by rfl⟩ : syracuseStep 2924081 = 2193061) B2193061
theorem B1949249 : Blo 1297967 1949249 := bstep (se 2 (by rfl) ⟨730968, by rfl⟩ : syracuseStep 1949249 = 1461937) B1461937
theorem B2924099 : Blo 1297967 2924099 := bstep (se 1 (by rfl) ⟨2193074, by rfl⟩ : syracuseStep 2924099 = 4386149) B4386149
theorem B1949267 : Blo 1297967 1949267 := bstep (se 1 (by rfl) ⟨1461950, by rfl⟩ : syracuseStep 1949267 = 2923901) B2923901
theorem B3161699 : Blo 1297967 3161699 := bstep (se 1 (by rfl) ⟨2371274, by rfl⟩ : syracuseStep 3161699 = 4742549) B4742549
theorem B1949297 : Blo 1297967 1949297 := bstep (se 2 (by rfl) ⟨730986, by rfl⟩ : syracuseStep 1949297 = 1461973) B1461973
theorem B1973875 : Blo 1297967 1973875 := bstep (se 1 (by rfl) ⟨1480406, by rfl⟩ : syracuseStep 1973875 = 2960813) B2960813
theorem B1949315 : Blo 1297967 1949315 := bstep (se 1 (by rfl) ⟨1461986, by rfl⟩ : syracuseStep 1949315 = 2923973) B2923973
theorem B7397027 : Blo 1297967 7397027 := bstep (se 1 (by rfl) ⟨5547770, by rfl⟩ : syracuseStep 7397027 = 11095541) B11095541
theorem B1949345 : Blo 1297967 1949345 := bstep (se 2 (by rfl) ⟨731004, by rfl⟩ : syracuseStep 1949345 = 1462009) B1462009
theorem B1949363 : Blo 1297967 1949363 := bstep (se 1 (by rfl) ⟨1462022, by rfl⟩ : syracuseStep 1949363 = 2924045) B2924045
theorem B1949393 : Blo 1297967 1949393 := bstep (se 2 (by rfl) ⟨731022, by rfl⟩ : syracuseStep 1949393 = 1462045) B1462045
theorem B9862883 : Blo 1297967 9862883 := bstep (se 1 (by rfl) ⟨7397162, by rfl⟩ : syracuseStep 9862883 = 14794325) B14794325
theorem B1949411 : Blo 1297967 1949411 := bstep (se 1 (by rfl) ⟨1462058, by rfl⟩ : syracuseStep 1949411 = 2924117) B2924117
theorem B1949441 : Blo 1297967 1949441 := bstep (se 2 (by rfl) ⟨731040, by rfl⟩ : syracuseStep 1949441 = 1462081) B1462081
theorem B4382477 : Blo 1297967 4382477 := bstep (se 3 (by rfl) ⟨821714, by rfl⟩ : syracuseStep 4382477 = 1643429) B1643429
theorem B1949459 : Blo 1297967 1949459 := bstep (se 1 (by rfl) ⟨1462094, by rfl⟩ : syracuseStep 1949459 = 2924189) B2924189
theorem B1949489 : Blo 1297967 1949489 := bstep (se 2 (by rfl) ⟨731058, by rfl⟩ : syracuseStep 1949489 = 1462117) B1462117
theorem B4382531 : Blo 1297967 4382531 := bstep (se 1 (by rfl) ⟨3286898, by rfl⟩ : syracuseStep 4382531 = 6573797) B6573797
theorem B1949507 : Blo 1297967 1949507 := bstep (se 1 (by rfl) ⟨1462130, by rfl⟩ : syracuseStep 1949507 = 2924261) B2924261
theorem B2924369 : Blo 1297967 2924369 := bstep (se 2 (by rfl) ⟨1096638, by rfl⟩ : syracuseStep 2924369 = 2193277) B2193277
theorem B1949537 : Blo 1297967 1949537 := bstep (se 2 (by rfl) ⟨731076, by rfl⟩ : syracuseStep 1949537 = 1462153) B1462153
theorem B2924387 : Blo 1297967 2924387 := bstep (se 1 (by rfl) ⟨2193290, by rfl⟩ : syracuseStep 2924387 = 4386581) B4386581
theorem B1949555 : Blo 1297967 1949555 := bstep (se 1 (by rfl) ⟨1462166, by rfl⟩ : syracuseStep 1949555 = 2924333) B2924333
theorem B1949585 : Blo 1297967 1949585 := bstep (se 2 (by rfl) ⟨731094, by rfl⟩ : syracuseStep 1949585 = 1462189) B1462189
theorem B1949603 : Blo 1297967 1949603 := bstep (se 1 (by rfl) ⟨1462202, by rfl⟩ : syracuseStep 1949603 = 2924405) B2924405
theorem B1949633 : Blo 1297967 1949633 := bstep (se 2 (by rfl) ⟨731112, by rfl⟩ : syracuseStep 1949633 = 1462225) B1462225
theorem B2670545 : Blo 1297967 2670545 := bstep (se 2 (by rfl) ⟨1001454, by rfl⟩ : syracuseStep 2670545 = 2002909) B2002909
theorem B1949651 : Blo 1297967 1949651 := bstep (se 1 (by rfl) ⟨1462238, by rfl⟩ : syracuseStep 1949651 = 2924477) B2924477
theorem B1949681 : Blo 1297967 1949681 := bstep (se 2 (by rfl) ⟨731130, by rfl⟩ : syracuseStep 1949681 = 1462261) B1462261
theorem B2924567 : Blo 1297967 2924567 := bstep (se 1 (by rfl) ⟨2193425, by rfl⟩ : syracuseStep 2924567 = 4386851) B4386851
theorem B18980939 : Blo 1297967 18980939 := bstep (se 1 (by rfl) ⟨14235704, by rfl⟩ : syracuseStep 18980939 = 28471409) B28471409
theorem B4161611 : Blo 1297967 4161611 := bstep (se 1 (by rfl) ⟨3121208, by rfl⟩ : syracuseStep 4161611 = 6242417) B6242417
theorem B1949771 : Blo 1297967 1949771 := bstep (se 1 (by rfl) ⟨1462328, by rfl⟩ : syracuseStep 1949771 = 2924657) B2924657
theorem B1949783 : Blo 1297967 1949783 := bstep (se 1 (by rfl) ⟨1462337, by rfl⟩ : syracuseStep 1949783 = 2924675) B2924675
theorem B7397527 : Blo 1297967 7397527 := bstep (se 1 (by rfl) ⟨5548145, by rfl⟩ : syracuseStep 7397527 = 11096291) B11096291
theorem B1949849 : Blo 1297967 1949849 := bstep (se 2 (by rfl) ⟨731193, by rfl⟩ : syracuseStep 1949849 = 1462387) B1462387
theorem B2924747 : Blo 1297967 2924747 := bstep (se 1 (by rfl) ⟨2193560, by rfl⟩ : syracuseStep 2924747 = 4387121) B4387121
theorem B13705421 : Blo 1297967 13705421 := bstep (se 3 (by rfl) ⟨2569766, by rfl⟩ : syracuseStep 13705421 = 5139533) B5139533
theorem B2924801 : Blo 1297967 2924801 := bstep (se 2 (by rfl) ⟨1096800, by rfl⟩ : syracuseStep 2924801 = 2193601) B2193601
theorem B1974539 : Blo 1297967 1974539 := bstep (se 1 (by rfl) ⟨1480904, by rfl⟩ : syracuseStep 1974539 = 2961809) B2961809
theorem B4391371 : Blo 1297967 4391371 := bstep (se 1 (by rfl) ⟨3293528, by rfl⟩ : syracuseStep 4391371 = 6587057) B6587057
theorem B4383179 : Blo 1297967 4383179 := bstep (se 1 (by rfl) ⟨3287384, by rfl⟩ : syracuseStep 4383179 = 6574769) B6574769
theorem B5620241 : Blo 1297967 5620241 := bstep (se 2 (by rfl) ⟨2107590, by rfl⟩ : syracuseStep 5620241 = 4215181) B4215181
theorem B3285593 : Blo 1297967 3285593 := bstep (se 2 (by rfl) ⟨1232097, by rfl⟩ : syracuseStep 3285593 = 2464195) B2464195
theorem B5546627 : Blo 1297967 5546627 := bstep (se 1 (by rfl) ⟨4159970, by rfl⟩ : syracuseStep 5546627 = 8319941) B8319941
theorem B6578819 : Blo 1297967 6578819 := bstep (se 1 (by rfl) ⟨4934114, by rfl⟩ : syracuseStep 6578819 = 9868229) B9868229
theorem B2466443 : Blo 1297967 2466443 := bstep (se 1 (by rfl) ⟨1849832, by rfl⟩ : syracuseStep 2466443 = 3699665) B3699665
theorem B17777303 : Blo 1297967 17777303 := bstep (se 1 (by rfl) ⟨13332977, by rfl⟩ : syracuseStep 17777303 = 26665955) B26665955
theorem B4383449 : Blo 1297967 4383449 := bstep (se 2 (by rfl) ⟨1643793, by rfl⟩ : syracuseStep 4383449 = 3287587) B3287587
theorem B2466625 : Blo 1297967 2466625 := bstep (se 2 (by rfl) ⟨924984, by rfl⟩ : syracuseStep 2466625 = 1849969) B1849969
theorem B35554265 : Blo 1297967 35554265 := bstep (se 2 (by rfl) ⟨13332849, by rfl⟩ : syracuseStep 35554265 = 26665699) B26665699
theorem B4678829 : Blo 1297967 4678829 := bstep (se 3 (by rfl) ⟨877280, by rfl⟩ : syracuseStep 4678829 = 1754561) B1754561
theorem B11846861 : Blo 1297967 11846861 := bstep (se 3 (by rfl) ⟨2221286, by rfl⟩ : syracuseStep 11846861 = 4442573) B4442573
theorem B2467073 : Blo 1297967 2467073 := bstep (se 2 (by rfl) ⟨925152, by rfl⟩ : syracuseStep 2467073 = 1850305) B1850305
theorem B2499979 : Blo 1297967 2499979 := bstep (se 1 (by rfl) ⟨1874984, by rfl⟩ : syracuseStep 2499979 = 3749969) B3749969
theorem B4384151 : Blo 1297967 4384151 := bstep (se 1 (by rfl) ⟨3288113, by rfl⟩ : syracuseStep 4384151 = 6576227) B6576227
theorem B8316377 : Blo 1297967 8316377 := bstep (se 2 (by rfl) ⟨3118641, by rfl⟩ : syracuseStep 8316377 = 6237283) B6237283
theorem B2467415 : Blo 1297967 2467415 := bstep (se 1 (by rfl) ⟨1850561, by rfl⟩ : syracuseStep 2467415 = 3701123) B3701123
theorem B4163251 : Blo 1297967 4163251 := bstep (se 1 (by rfl) ⟨3122438, by rfl⟩ : syracuseStep 4163251 = 6244877) B6244877
theorem B3696349 : Blo 1297967 3696349 := bstep (se 3 (by rfl) ⟨693065, by rfl⟩ : syracuseStep 3696349 = 1386131) B1386131
theorem B4933507 : Blo 1297967 4933507 := bstep (se 1 (by rfl) ⟨3700130, by rfl⟩ : syracuseStep 4933507 = 7400261) B7400261
theorem B4384691 : Blo 1297967 4384691 := bstep (se 1 (by rfl) ⟨3288518, by rfl⟩ : syracuseStep 4384691 = 6577037) B6577037
theorem B11847629 : Blo 1297967 11847629 := bstep (se 3 (by rfl) ⟨2221430, by rfl⟩ : syracuseStep 11847629 = 4442861) B4442861
theorem B3696691 : Blo 1297967 3696691 := bstep (se 1 (by rfl) ⟨2772518, by rfl⟩ : syracuseStep 3696691 = 5545037) B5545037
theorem B85403717 : Blo 1297967 85403717 := bstep (se 4 (by rfl) ⟨8006598, by rfl⟩ : syracuseStep 85403717 = 16013197) B16013197
theorem B1460299 : Blo 1297967 1460299 := bstep (se 1 (by rfl) ⟨1095224, by rfl⟩ : syracuseStep 1460299 = 2190449) B2190449
theorem B2631833 : Blo 1297967 2631833 := bstep (se 2 (by rfl) ⟨986937, by rfl⟩ : syracuseStep 2631833 = 1973875) B1973875
theorem B4933811 : Blo 1297967 4933811 := bstep (se 1 (by rfl) ⟨3700358, by rfl⟩ : syracuseStep 4933811 = 7400717) B7400717
theorem B1460407 : Blo 1297967 1460407 := bstep (se 1 (by rfl) ⟨1095305, by rfl⟩ : syracuseStep 1460407 = 2190611) B2190611
theorem B4384961 : Blo 1297967 4384961 := bstep (se 2 (by rfl) ⟨1644360, by rfl⟩ : syracuseStep 4384961 = 3288721) B3288721
theorem B3287243 : Blo 1297967 3287243 := bstep (se 1 (by rfl) ⟨2465432, by rfl⟩ : syracuseStep 3287243 = 4930865) B4930865
theorem B1386763 : Blo 1297967 1386763 := bstep (se 1 (by rfl) ⟨1040072, by rfl⟩ : syracuseStep 1386763 = 2080145) B2080145
theorem B1460587 : Blo 1297967 1460587 := bstep (se 1 (by rfl) ⟨1095440, by rfl⟩ : syracuseStep 1460587 = 2190881) B2190881
theorem B2107799 : Blo 1297967 2107799 := bstep (se 1 (by rfl) ⟨1580849, by rfl⟩ : syracuseStep 2107799 = 3161699) B3161699
theorem B1444267 : Blo 1297967 1444267 := bstep (se 1 (by rfl) ⟨1083200, by rfl⟩ : syracuseStep 1444267 = 2166401) B2166401
theorem B1460695 : Blo 1297967 1460695 := bstep (se 1 (by rfl) ⟨1095521, by rfl⟩ : syracuseStep 1460695 = 2191043) B2191043
theorem B7121453 : Blo 1297967 7121453 := bstep (se 3 (by rfl) ⟨1335272, by rfl⟩ : syracuseStep 7121453 = 2670545) B2670545
theorem B4164185 : Blo 1297967 4164185 := bstep (se 2 (by rfl) ⟨1561569, by rfl⟩ : syracuseStep 4164185 = 3123139) B3123139
theorem B1460875 : Blo 1297967 1460875 := bstep (se 1 (by rfl) ⟨1095656, by rfl⟩ : syracuseStep 1460875 = 2191313) B2191313
theorem B4385501 : Blo 1297967 4385501 := bstep (se 3 (by rfl) ⟨822281, by rfl⟩ : syracuseStep 4385501 = 1644563) B1644563
theorem B1460983 : Blo 1297967 1460983 := bstep (se 1 (by rfl) ⟨1095737, by rfl⟩ : syracuseStep 1460983 = 2191475) B2191475
theorem B4680499 : Blo 1297967 4680499 := bstep (se 1 (by rfl) ⟨3510374, by rfl⟩ : syracuseStep 4680499 = 7020749) B7020749
theorem B4934465 : Blo 1297967 4934465 := bstep (se 2 (by rfl) ⟨1850424, by rfl⟩ : syracuseStep 4934465 = 3700849) B3700849
theorem B4746115 : Blo 1297967 4746115 := bstep (se 1 (by rfl) ⟨3559586, by rfl⟩ : syracuseStep 4746115 = 7119173) B7119173
theorem B1461163 : Blo 1297967 1461163 := bstep (se 1 (by rfl) ⟨1095872, by rfl⟩ : syracuseStep 1461163 = 2191745) B2191745
theorem B3697625 : Blo 1297967 3697625 := bstep (se 2 (by rfl) ⟨1386609, by rfl⟩ : syracuseStep 3697625 = 2773219) B2773219
theorem B1461271 : Blo 1297967 1461271 := bstep (se 1 (by rfl) ⟨1095953, by rfl⟩ : syracuseStep 1461271 = 2191907) B2191907
theorem B2190361 : Blo 1297967 2190361 := bstep (se 2 (by rfl) ⟨821385, by rfl⟩ : syracuseStep 2190361 = 1642771) B1642771
theorem B9866285 : Blo 1297967 9866285 := bstep (se 3 (by rfl) ⟨1849928, by rfl⟩ : syracuseStep 9866285 = 3699857) B3699857
theorem B6573149 : Blo 1297967 6573149 := bstep (se 3 (by rfl) ⟨1232465, by rfl⟩ : syracuseStep 6573149 = 2464931) B2464931
theorem B3288215 : Blo 1297967 3288215 := bstep (se 1 (by rfl) ⟨2466161, by rfl⟩ : syracuseStep 3288215 = 4932323) B4932323
theorem B16657559 : Blo 1297967 16657559 := bstep (se 1 (by rfl) ⟨12493169, by rfl⟩ : syracuseStep 16657559 = 24986339) B24986339
theorem B1387703 : Blo 1297967 1387703 := bstep (se 1 (by rfl) ⟨1040777, by rfl⟩ : syracuseStep 1387703 = 2081555) B2081555
theorem B1461451 : Blo 1297967 1461451 := bstep (se 1 (by rfl) ⟨1096088, by rfl⟩ : syracuseStep 1461451 = 2192177) B2192177
theorem B2632961 : Blo 1297967 2632961 := bstep (se 2 (by rfl) ⟨987360, by rfl⟩ : syracuseStep 2632961 = 1974721) B1974721
theorem B1461559 : Blo 1297967 1461559 := bstep (se 1 (by rfl) ⟨1096169, by rfl⟩ : syracuseStep 1461559 = 2192339) B2192339
theorem B9858509 : Blo 1297967 9858509 := bstep (se 3 (by rfl) ⟨1848470, by rfl⟩ : syracuseStep 9858509 = 3696941) B3696941
theorem B1756631 : Blo 1297967 1756631 := bstep (se 1 (by rfl) ⟨1317473, by rfl⟩ : syracuseStep 1756631 = 2634947) B2634947
theorem B1461739 : Blo 1297967 1461739 := bstep (se 1 (by rfl) ⟨1096304, by rfl⟩ : syracuseStep 1461739 = 2192609) B2192609
theorem B4746755 : Blo 1297967 4746755 := bstep (se 1 (by rfl) ⟨3560066, by rfl⟩ : syracuseStep 4746755 = 7120133) B7120133
theorem B1297975 : Blo 1297967 1297975 := bstep (se 1 (by rfl) ⟨973481, by rfl⟩ : syracuseStep 1297975 = 1946963) B1946963
theorem B1297995 : Blo 1297967 1297995 := bstep (se 1 (by rfl) ⟨973496, by rfl⟩ : syracuseStep 1297995 = 1946993) B1946993
theorem B1298007 : Blo 1297967 1298007 := bstep (se 1 (by rfl) ⟨973505, by rfl⟩ : syracuseStep 1298007 = 1947011) B1947011
theorem B2190935 : Blo 1297967 2190935 := bstep (se 1 (by rfl) ⟨1643201, by rfl⟩ : syracuseStep 2190935 = 3286403) B3286403
theorem B1461847 : Blo 1297967 1461847 := bstep (se 1 (by rfl) ⟨1096385, by rfl⟩ : syracuseStep 1461847 = 2192771) B2192771
theorem B1298027 : Blo 1297967 1298027 := bstep (se 1 (by rfl) ⟨973520, by rfl⟩ : syracuseStep 1298027 = 1947041) B1947041
theorem B1298039 : Blo 1297967 1298039 := bstep (se 1 (by rfl) ⟨973529, by rfl⟩ : syracuseStep 1298039 = 1947059) B1947059
theorem B1298059 : Blo 1297967 1298059 := bstep (se 1 (by rfl) ⟨973544, by rfl⟩ : syracuseStep 1298059 = 1947089) B1947089
theorem B1298071 : Blo 1297967 1298071 := bstep (se 1 (by rfl) ⟨973553, by rfl⟩ : syracuseStep 1298071 = 1947107) B1947107
theorem B1298091 : Blo 1297967 1298091 := bstep (se 1 (by rfl) ⟨973568, by rfl⟩ : syracuseStep 1298091 = 1947137) B1947137
theorem B1298103 : Blo 1297967 1298103 := bstep (se 1 (by rfl) ⟨973577, by rfl⟩ : syracuseStep 1298103 = 1947155) B1947155
theorem B1298123 : Blo 1297967 1298123 := bstep (se 1 (by rfl) ⟨973592, by rfl⟩ : syracuseStep 1298123 = 1947185) B1947185
theorem B1298135 : Blo 1297967 1298135 := bstep (se 1 (by rfl) ⟨973601, by rfl⟩ : syracuseStep 1298135 = 1947203) B1947203
theorem B2191063 : Blo 1297967 2191063 := bstep (se 1 (by rfl) ⟨1643297, by rfl⟩ : syracuseStep 2191063 = 3286595) B3286595
theorem B2633431 : Blo 1297967 2633431 := bstep (se 1 (by rfl) ⟨1975073, by rfl⟩ : syracuseStep 2633431 = 3950147) B3950147
theorem B1298155 : Blo 1297967 1298155 := bstep (se 1 (by rfl) ⟨973616, by rfl⟩ : syracuseStep 1298155 = 1947233) B1947233
theorem B1298167 : Blo 1297967 1298167 := bstep (se 1 (by rfl) ⟨973625, by rfl⟩ : syracuseStep 1298167 = 1947251) B1947251
theorem B1298187 : Blo 1297967 1298187 := bstep (se 1 (by rfl) ⟨973640, by rfl⟩ : syracuseStep 1298187 = 1947281) B1947281
theorem B1462027 : Blo 1297967 1462027 := bstep (se 1 (by rfl) ⟨1096520, by rfl⟩ : syracuseStep 1462027 = 2193041) B2193041
theorem B1756939 : Blo 1297967 1756939 := bstep (se 1 (by rfl) ⟨1317704, by rfl⟩ : syracuseStep 1756939 = 2635409) B2635409
theorem B1298199 : Blo 1297967 1298199 := bstep (se 1 (by rfl) ⟨973649, by rfl⟩ : syracuseStep 1298199 = 1947299) B1947299
theorem B1298219 : Blo 1297967 1298219 := bstep (se 1 (by rfl) ⟨973664, by rfl⟩ : syracuseStep 1298219 = 1947329) B1947329
theorem B3288883 : Blo 1297967 3288883 := bstep (se 1 (by rfl) ⟨2466662, by rfl⟩ : syracuseStep 3288883 = 4933325) B4933325
theorem B1298231 : Blo 1297967 1298231 := bstep (se 1 (by rfl) ⟨973673, by rfl⟩ : syracuseStep 1298231 = 1947347) B1947347
theorem B1298251 : Blo 1297967 1298251 := bstep (se 1 (by rfl) ⟨973688, by rfl⟩ : syracuseStep 1298251 = 1947377) B1947377
theorem B4386635 : Blo 1297967 4386635 := bstep (se 1 (by rfl) ⟨3289976, by rfl⟩ : syracuseStep 4386635 = 6579953) B6579953
theorem B1298263 : Blo 1297967 1298263 := bstep (se 1 (by rfl) ⟨973697, by rfl⟩ : syracuseStep 1298263 = 1947395) B1947395
theorem B1298283 : Blo 1297967 1298283 := bstep (se 1 (by rfl) ⟨973712, by rfl⟩ : syracuseStep 1298283 = 1947425) B1947425
theorem B1298295 : Blo 1297967 1298295 := bstep (se 1 (by rfl) ⟨973721, by rfl⟩ : syracuseStep 1298295 = 1947443) B1947443
theorem B1462135 : Blo 1297967 1462135 := bstep (se 1 (by rfl) ⟨1096601, by rfl⟩ : syracuseStep 1462135 = 2193203) B2193203
theorem B1298315 : Blo 1297967 1298315 := bstep (se 1 (by rfl) ⟨973736, by rfl⟩ : syracuseStep 1298315 = 1947473) B1947473
theorem B1298327 : Blo 1297967 1298327 := bstep (se 1 (by rfl) ⟨973745, by rfl⟩ : syracuseStep 1298327 = 1947491) B1947491
theorem B9015191 : Blo 1297967 9015191 := bstep (se 1 (by rfl) ⟨6761393, by rfl⟩ : syracuseStep 9015191 = 13522787) B13522787
theorem B1298347 : Blo 1297967 1298347 := bstep (se 1 (by rfl) ⟨973760, by rfl⟩ : syracuseStep 1298347 = 1947521) B1947521
theorem B9858995 : Blo 1297967 9858995 := bstep (se 1 (by rfl) ⟨7394246, by rfl⟩ : syracuseStep 9858995 = 14788493) B14788493
theorem B1298359 : Blo 1297967 1298359 := bstep (se 1 (by rfl) ⟨973769, by rfl⟩ : syracuseStep 1298359 = 1947539) B1947539
theorem B2772929 : Blo 1297967 2772929 := bstep (se 2 (by rfl) ⟨1039848, by rfl⟩ : syracuseStep 2772929 = 2079697) B2079697
theorem B3289025 : Blo 1297967 3289025 := bstep (se 2 (by rfl) ⟨1233384, by rfl⟩ : syracuseStep 3289025 = 2466769) B2466769
theorem B1298379 : Blo 1297967 1298379 := bstep (se 1 (by rfl) ⟨973784, by rfl⟩ : syracuseStep 1298379 = 1947569) B1947569
theorem B1298391 : Blo 1297967 1298391 := bstep (se 1 (by rfl) ⟨973793, by rfl⟩ : syracuseStep 1298391 = 1947587) B1947587
theorem B1298411 : Blo 1297967 1298411 := bstep (se 1 (by rfl) ⟨973808, by rfl⟩ : syracuseStep 1298411 = 1947617) B1947617
theorem B1298423 : Blo 1297967 1298423 := bstep (se 1 (by rfl) ⟨973817, by rfl⟩ : syracuseStep 1298423 = 1947635) B1947635
theorem B1298443 : Blo 1297967 1298443 := bstep (se 1 (by rfl) ⟨973832, by rfl⟩ : syracuseStep 1298443 = 1947665) B1947665
theorem B1298455 : Blo 1297967 1298455 := bstep (se 1 (by rfl) ⟨973841, by rfl⟩ : syracuseStep 1298455 = 1947683) B1947683
theorem B3379223 : Blo 1297967 3379223 := bstep (se 1 (by rfl) ⟨2534417, by rfl⟩ : syracuseStep 3379223 = 5068835) B5068835
theorem B1298475 : Blo 1297967 1298475 := bstep (se 1 (by rfl) ⟨973856, by rfl⟩ : syracuseStep 1298475 = 1947713) B1947713
theorem B1462315 : Blo 1297967 1462315 := bstep (se 1 (by rfl) ⟨1096736, by rfl⟩ : syracuseStep 1462315 = 2193473) B2193473
theorem B4935725 : Blo 1297967 4935725 := bstep (se 3 (by rfl) ⟨925448, by rfl⟩ : syracuseStep 4935725 = 1850897) B1850897
theorem B2920499 : Blo 1297967 2920499 := bstep (se 1 (by rfl) ⟨2190374, by rfl⟩ : syracuseStep 2920499 = 4380749) B4380749
theorem B1298487 : Blo 1297967 1298487 := bstep (se 1 (by rfl) ⟨973865, by rfl⟩ : syracuseStep 1298487 = 1947731) B1947731
theorem B1298507 : Blo 1297967 1298507 := bstep (se 1 (by rfl) ⟨973880, by rfl⟩ : syracuseStep 1298507 = 1947761) B1947761
theorem B4935755 : Blo 1297967 4935755 := bstep (se 1 (by rfl) ⟨3701816, by rfl⟩ : syracuseStep 4935755 = 7403633) B7403633
theorem B2920535 : Blo 1297967 2920535 := bstep (se 1 (by rfl) ⟨2190401, by rfl⟩ : syracuseStep 2920535 = 4380803) B4380803
theorem B1298519 : Blo 1297967 1298519 := bstep (se 1 (by rfl) ⟨973889, by rfl⟩ : syracuseStep 1298519 = 1947779) B1947779
theorem B4386905 : Blo 1297967 4386905 := bstep (se 2 (by rfl) ⟨1645089, by rfl⟩ : syracuseStep 4386905 = 3290179) B3290179
theorem B1298539 : Blo 1297967 1298539 := bstep (se 1 (by rfl) ⟨973904, by rfl⟩ : syracuseStep 1298539 = 1947809) B1947809
theorem B1298551 : Blo 1297967 1298551 := bstep (se 1 (by rfl) ⟨973913, by rfl⟩ : syracuseStep 1298551 = 1947827) B1947827
theorem B1298571 : Blo 1297967 1298571 := bstep (se 1 (by rfl) ⟨973928, by rfl⟩ : syracuseStep 1298571 = 1947857) B1947857
theorem B1298583 : Blo 1297967 1298583 := bstep (se 1 (by rfl) ⟨973937, by rfl⟩ : syracuseStep 1298583 = 1947875) B1947875
theorem B1462423 : Blo 1297967 1462423 := bstep (se 1 (by rfl) ⟨1096817, by rfl⟩ : syracuseStep 1462423 = 2193635) B2193635
theorem B1298603 : Blo 1297967 1298603 := bstep (se 1 (by rfl) ⟨973952, by rfl⟩ : syracuseStep 1298603 = 1947905) B1947905
theorem B1298615 : Blo 1297967 1298615 := bstep (se 1 (by rfl) ⟨973961, by rfl⟩ : syracuseStep 1298615 = 1947923) B1947923
theorem B1298635 : Blo 1297967 1298635 := bstep (se 1 (by rfl) ⟨973976, by rfl⟩ : syracuseStep 1298635 = 1947953) B1947953
theorem B1298647 : Blo 1297967 1298647 := bstep (se 1 (by rfl) ⟨973985, by rfl⟩ : syracuseStep 1298647 = 1947971) B1947971
theorem B1298667 : Blo 1297967 1298667 := bstep (se 1 (by rfl) ⟨974000, by rfl⟩ : syracuseStep 1298667 = 1948001) B1948001
theorem B1298679 : Blo 1297967 1298679 := bstep (se 1 (by rfl) ⟨974009, by rfl⟩ : syracuseStep 1298679 = 1948019) B1948019
theorem B2920715 : Blo 1297967 2920715 := bstep (se 1 (by rfl) ⟨2190536, by rfl⟩ : syracuseStep 2920715 = 4381073) B4381073
theorem B1298699 : Blo 1297967 1298699 := bstep (se 1 (by rfl) ⟨974024, by rfl⟩ : syracuseStep 1298699 = 1948049) B1948049
theorem B2773271 : Blo 1297967 2773271 := bstep (se 1 (by rfl) ⟨2079953, by rfl⟩ : syracuseStep 2773271 = 4159907) B4159907
theorem B1298711 : Blo 1297967 1298711 := bstep (se 1 (by rfl) ⟨974033, by rfl⟩ : syracuseStep 1298711 = 1948067) B1948067
theorem B1298731 : Blo 1297967 1298731 := bstep (se 1 (by rfl) ⟨974048, by rfl⟩ : syracuseStep 1298731 = 1948097) B1948097
theorem B1298743 : Blo 1297967 1298743 := bstep (se 1 (by rfl) ⟨974057, by rfl⟩ : syracuseStep 1298743 = 1948115) B1948115
theorem B2920769 : Blo 1297967 2920769 := bstep (se 2 (by rfl) ⟨1095288, by rfl⟩ : syracuseStep 2920769 = 2190577) B2190577
theorem B9998657 : Blo 1297967 9998657 := bstep (se 2 (by rfl) ⟨3749496, by rfl⟩ : syracuseStep 9998657 = 7498993) B7498993
theorem B1298763 : Blo 1297967 1298763 := bstep (se 1 (by rfl) ⟨974072, by rfl⟩ : syracuseStep 1298763 = 1948145) B1948145
theorem B2191691 : Blo 1297967 2191691 := bstep (se 1 (by rfl) ⟨1643768, by rfl⟩ : syracuseStep 2191691 = 3287537) B3287537
theorem B1298775 : Blo 1297967 1298775 := bstep (se 1 (by rfl) ⟨974081, by rfl⟩ : syracuseStep 1298775 = 1948163) B1948163
theorem B3699037 : Blo 1297967 3699037 := bstep (se 3 (by rfl) ⟨693569, by rfl⟩ : syracuseStep 3699037 = 1387139) B1387139
theorem B1298795 : Blo 1297967 1298795 := bstep (se 1 (by rfl) ⟨974096, by rfl⟩ : syracuseStep 1298795 = 1948193) B1948193
theorem B1298807 : Blo 1297967 1298807 := bstep (se 1 (by rfl) ⟨974105, by rfl⟩ : syracuseStep 1298807 = 1948211) B1948211
theorem B1298827 : Blo 1297967 1298827 := bstep (se 1 (by rfl) ⟨974120, by rfl⟩ : syracuseStep 1298827 = 1948241) B1948241
theorem B1298839 : Blo 1297967 1298839 := bstep (se 1 (by rfl) ⟨974129, by rfl⟩ : syracuseStep 1298839 = 1948259) B1948259
theorem B1298859 : Blo 1297967 1298859 := bstep (se 1 (by rfl) ⟨974144, by rfl⟩ : syracuseStep 1298859 = 1948289) B1948289
theorem B4747693 : Blo 1297967 4747693 := bstep (se 3 (by rfl) ⟨890192, by rfl⟩ : syracuseStep 4747693 = 1780385) B1780385
theorem B12489137 : Blo 1297967 12489137 := bstep (se 2 (by rfl) ⟨4683426, by rfl⟩ : syracuseStep 12489137 = 9366853) B9366853
theorem B1298871 : Blo 1297967 1298871 := bstep (se 1 (by rfl) ⟨974153, by rfl⟩ : syracuseStep 1298871 = 1948307) B1948307
theorem B2191819 : Blo 1297967 2191819 := bstep (se 1 (by rfl) ⟨1643864, by rfl⟩ : syracuseStep 2191819 = 3287729) B3287729
theorem B1298891 : Blo 1297967 1298891 := bstep (se 1 (by rfl) ⟨974168, by rfl⟩ : syracuseStep 1298891 = 1948337) B1948337
theorem B1298903 : Blo 1297967 1298903 := bstep (se 1 (by rfl) ⟨974177, by rfl⟩ : syracuseStep 1298903 = 1948355) B1948355
theorem B1298923 : Blo 1297967 1298923 := bstep (se 1 (by rfl) ⟨974192, by rfl⟩ : syracuseStep 1298923 = 1948385) B1948385
theorem B1298935 : Blo 1297967 1298935 := bstep (se 1 (by rfl) ⟨974201, by rfl⟩ : syracuseStep 1298935 = 1948403) B1948403
theorem B3002881 : Blo 1297967 3002881 := bstep (se 2 (by rfl) ⟨1126080, by rfl⟩ : syracuseStep 3002881 = 2252161) B2252161
theorem B1298955 : Blo 1297967 1298955 := bstep (se 1 (by rfl) ⟨974216, by rfl⟩ : syracuseStep 1298955 = 1948433) B1948433
theorem B1298967 : Blo 1297967 1298967 := bstep (se 1 (by rfl) ⟨974225, by rfl⟩ : syracuseStep 1298967 = 1948451) B1948451
theorem B2920985 : Blo 1297967 2920985 := bstep (se 2 (by rfl) ⟨1095369, by rfl⟩ : syracuseStep 2920985 = 2190739) B2190739
theorem B1298987 : Blo 1297967 1298987 := bstep (se 1 (by rfl) ⟨974240, by rfl⟩ : syracuseStep 1298987 = 1948481) B1948481
theorem B1298999 : Blo 1297967 1298999 := bstep (se 1 (by rfl) ⟨974249, by rfl⟩ : syracuseStep 1298999 = 1948499) B1948499
theorem B3699265 : Blo 1297967 3699265 := bstep (se 2 (by rfl) ⟨1387224, by rfl⟩ : syracuseStep 3699265 = 2774449) B2774449
theorem B1299019 : Blo 1297967 1299019 := bstep (se 1 (by rfl) ⟨974264, by rfl⟩ : syracuseStep 1299019 = 1948529) B1948529
theorem B1667659 : Blo 1297967 1667659 := bstep (se 1 (by rfl) ⟨1250744, by rfl⟩ : syracuseStep 1667659 = 2501489) B2501489
theorem B1643095 : Blo 1297967 1643095 := bstep (se 1 (by rfl) ⟨1232321, by rfl⟩ : syracuseStep 1643095 = 2464643) B2464643
theorem B1299031 : Blo 1297967 1299031 := bstep (se 1 (by rfl) ⟨974273, by rfl⟩ : syracuseStep 1299031 = 1948547) B1948547
theorem B2191961 : Blo 1297967 2191961 := bstep (se 2 (by rfl) ⟨821985, by rfl⟩ : syracuseStep 2191961 = 1643971) B1643971
theorem B1299051 : Blo 1297967 1299051 := bstep (se 1 (by rfl) ⟨974288, by rfl⟩ : syracuseStep 1299051 = 1948577) B1948577
theorem B2921075 : Blo 1297967 2921075 := bstep (se 1 (by rfl) ⟨2190806, by rfl⟩ : syracuseStep 2921075 = 4381613) B4381613
theorem B1299063 : Blo 1297967 1299063 := bstep (se 1 (by rfl) ⟨974297, by rfl⟩ : syracuseStep 1299063 = 1948595) B1948595
theorem B1299083 : Blo 1297967 1299083 := bstep (se 1 (by rfl) ⟨974312, by rfl⟩ : syracuseStep 1299083 = 1948625) B1948625
theorem B2921111 : Blo 1297967 2921111 := bstep (se 1 (by rfl) ⟨2190833, by rfl⟩ : syracuseStep 2921111 = 4381667) B4381667
theorem B1299095 : Blo 1297967 1299095 := bstep (se 1 (by rfl) ⟨974321, by rfl⟩ : syracuseStep 1299095 = 1948643) B1948643
theorem B5550743 : Blo 1297967 5550743 := bstep (se 1 (by rfl) ⟨4163057, by rfl⟩ : syracuseStep 5550743 = 8326115) B8326115
theorem B1299115 : Blo 1297967 1299115 := bstep (se 1 (by rfl) ⟨974336, by rfl⟩ : syracuseStep 1299115 = 1948673) B1948673
theorem B1299127 : Blo 1297967 1299127 := bstep (se 1 (by rfl) ⟨974345, by rfl⟩ : syracuseStep 1299127 = 1948691) B1948691
theorem B1299147 : Blo 1297967 1299147 := bstep (se 1 (by rfl) ⟨974360, by rfl⟩ : syracuseStep 1299147 = 1948721) B1948721
theorem B1299159 : Blo 1297967 1299159 := bstep (se 1 (by rfl) ⟨974369, by rfl⟩ : syracuseStep 1299159 = 1948739) B1948739
theorem B2192089 : Blo 1297967 2192089 := bstep (se 2 (by rfl) ⟨822033, by rfl⟩ : syracuseStep 2192089 = 1644067) B1644067
theorem B1299179 : Blo 1297967 1299179 := bstep (se 1 (by rfl) ⟨974384, by rfl⟩ : syracuseStep 1299179 = 1948769) B1948769
theorem B1299191 : Blo 1297967 1299191 := bstep (se 1 (by rfl) ⟨974393, by rfl⟩ : syracuseStep 1299191 = 1948787) B1948787
theorem B1299211 : Blo 1297967 1299211 := bstep (se 1 (by rfl) ⟨974408, by rfl⟩ : syracuseStep 1299211 = 1948817) B1948817
theorem B1299223 : Blo 1297967 1299223 := bstep (se 1 (by rfl) ⟨974417, by rfl⟩ : syracuseStep 1299223 = 1948835) B1948835
theorem B4682519 : Blo 1297967 4682519 := bstep (se 1 (by rfl) ⟨3511889, by rfl⟩ : syracuseStep 4682519 = 7023779) B7023779
theorem B1299243 : Blo 1297967 1299243 := bstep (se 1 (by rfl) ⟨974432, by rfl⟩ : syracuseStep 1299243 = 1948865) B1948865
theorem B1299255 : Blo 1297967 1299255 := bstep (se 1 (by rfl) ⟨974441, by rfl⟩ : syracuseStep 1299255 = 1948883) B1948883
theorem B6239051 : Blo 1297967 6239051 := bstep (se 1 (by rfl) ⟨4679288, by rfl⟩ : syracuseStep 6239051 = 9358577) B9358577
theorem B2921291 : Blo 1297967 2921291 := bstep (se 1 (by rfl) ⟨2190968, by rfl⟩ : syracuseStep 2921291 = 4381937) B4381937
theorem B1299275 : Blo 1297967 1299275 := bstep (se 1 (by rfl) ⟨974456, by rfl⟩ : syracuseStep 1299275 = 1948913) B1948913
theorem B1299287 : Blo 1297967 1299287 := bstep (se 1 (by rfl) ⟨974465, by rfl⟩ : syracuseStep 1299287 = 1948931) B1948931
theorem B40555363 : Blo 1297967 40555363 := bstep (se 1 (by rfl) ⟨30416522, by rfl⟩ : syracuseStep 40555363 = 60833045) B60833045
theorem B1299307 : Blo 1297967 1299307 := bstep (se 1 (by rfl) ⟨974480, by rfl⟩ : syracuseStep 1299307 = 1948961) B1948961
theorem B1299319 : Blo 1297967 1299319 := bstep (se 1 (by rfl) ⟨974489, by rfl⟩ : syracuseStep 1299319 = 1948979) B1948979
theorem B2921345 : Blo 1297967 2921345 := bstep (se 2 (by rfl) ⟨1095504, by rfl⟩ : syracuseStep 2921345 = 2191009) B2191009
theorem B1299339 : Blo 1297967 1299339 := bstep (se 1 (by rfl) ⟨974504, by rfl⟩ : syracuseStep 1299339 = 1949009) B1949009
theorem B3699607 : Blo 1297967 3699607 := bstep (se 1 (by rfl) ⟨2774705, by rfl⟩ : syracuseStep 3699607 = 5549411) B5549411
theorem B1299351 : Blo 1297967 1299351 := bstep (se 1 (by rfl) ⟨974513, by rfl⟩ : syracuseStep 1299351 = 1949027) B1949027
theorem B1299371 : Blo 1297967 1299371 := bstep (se 1 (by rfl) ⟨974528, by rfl⟩ : syracuseStep 1299371 = 1949057) B1949057
theorem B4928435 : Blo 1297967 4928435 := bstep (se 1 (by rfl) ⟨3696326, by rfl⟩ : syracuseStep 4928435 = 7392653) B7392653
theorem B1299383 : Blo 1297967 1299383 := bstep (se 1 (by rfl) ⟨974537, by rfl⟩ : syracuseStep 1299383 = 1949075) B1949075
theorem B1299403 : Blo 1297967 1299403 := bstep (se 1 (by rfl) ⟨974552, by rfl⟩ : syracuseStep 1299403 = 1949105) B1949105
theorem B5551051 : Blo 1297967 5551051 := bstep (se 1 (by rfl) ⟨4163288, by rfl⟩ : syracuseStep 5551051 = 8326577) B8326577
theorem B1299415 : Blo 1297967 1299415 := bstep (se 1 (by rfl) ⟨974561, by rfl⟩ : syracuseStep 1299415 = 1949123) B1949123
theorem B1299435 : Blo 1297967 1299435 := bstep (se 1 (by rfl) ⟨974576, by rfl⟩ : syracuseStep 1299435 = 1949153) B1949153
theorem B1299447 : Blo 1297967 1299447 := bstep (se 1 (by rfl) ⟨974585, by rfl⟩ : syracuseStep 1299447 = 1949171) B1949171
theorem B1299467 : Blo 1297967 1299467 := bstep (se 1 (by rfl) ⟨974600, by rfl⟩ : syracuseStep 1299467 = 1949201) B1949201
theorem B8434705 : Blo 1297967 8434705 := bstep (se 2 (by rfl) ⟨3163014, by rfl⟩ : syracuseStep 8434705 = 6326029) B6326029
theorem B1299479 : Blo 1297967 1299479 := bstep (se 1 (by rfl) ⟨974609, by rfl⟩ : syracuseStep 1299479 = 1949219) B1949219
theorem B1299499 : Blo 1297967 1299499 := bstep (se 1 (by rfl) ⟨974624, by rfl⟩ : syracuseStep 1299499 = 1949249) B1949249
theorem B1299511 : Blo 1297967 1299511 := bstep (se 1 (by rfl) ⟨974633, by rfl⟩ : syracuseStep 1299511 = 1949267) B1949267
theorem B1299531 : Blo 1297967 1299531 := bstep (se 1 (by rfl) ⟨974648, by rfl⟩ : syracuseStep 1299531 = 1949297) B1949297
theorem B1299543 : Blo 1297967 1299543 := bstep (se 1 (by rfl) ⟨974657, by rfl⟩ : syracuseStep 1299543 = 1949315) B1949315
theorem B2921561 : Blo 1297967 2921561 := bstep (se 2 (by rfl) ⟨1095585, by rfl⟩ : syracuseStep 2921561 = 2191171) B2191171
theorem B1299563 : Blo 1297967 1299563 := bstep (se 1 (by rfl) ⟨974672, by rfl⟩ : syracuseStep 1299563 = 1949345) B1949345
theorem B1299575 : Blo 1297967 1299575 := bstep (se 1 (by rfl) ⟨974681, by rfl⟩ : syracuseStep 1299575 = 1949363) B1949363
theorem B1299595 : Blo 1297967 1299595 := bstep (se 1 (by rfl) ⟨974696, by rfl⟩ : syracuseStep 1299595 = 1949393) B1949393
theorem B6575255 : Blo 1297967 6575255 := bstep (se 1 (by rfl) ⟨4931441, by rfl⟩ : syracuseStep 6575255 = 9862883) B9862883
theorem B1299607 : Blo 1297967 1299607 := bstep (se 1 (by rfl) ⟨974705, by rfl⟩ : syracuseStep 1299607 = 1949411) B1949411
theorem B1299627 : Blo 1297967 1299627 := bstep (se 1 (by rfl) ⟨974720, by rfl⟩ : syracuseStep 1299627 = 1949441) B1949441
theorem B2921651 : Blo 1297967 2921651 := bstep (se 1 (by rfl) ⟨2191238, by rfl⟩ : syracuseStep 2921651 = 4382477) B4382477
theorem B2340019 : Blo 1297967 2340019 := bstep (se 1 (by rfl) ⟨1755014, by rfl⟩ : syracuseStep 2340019 = 3510029) B3510029
theorem B3290291 : Blo 1297967 3290291 := bstep (se 1 (by rfl) ⟨2467718, by rfl⟩ : syracuseStep 3290291 = 4935437) B4935437
theorem B1299639 : Blo 1297967 1299639 := bstep (se 1 (by rfl) ⟨974729, by rfl⟩ : syracuseStep 1299639 = 1949459) B1949459
theorem B1299659 : Blo 1297967 1299659 := bstep (se 1 (by rfl) ⟨974744, by rfl⟩ : syracuseStep 1299659 = 1949489) B1949489
theorem B13333709 : Blo 1297967 13333709 := bstep (se 3 (by rfl) ⟨2500070, by rfl⟩ : syracuseStep 13333709 = 5000141) B5000141
theorem B2921687 : Blo 1297967 2921687 := bstep (se 1 (by rfl) ⟨2191265, by rfl⟩ : syracuseStep 2921687 = 4382531) B4382531
theorem B1299671 : Blo 1297967 1299671 := bstep (se 1 (by rfl) ⟨974753, by rfl⟩ : syracuseStep 1299671 = 1949507) B1949507
theorem B5551325 : Blo 1297967 5551325 := bstep (se 3 (by rfl) ⟨1040873, by rfl⟩ : syracuseStep 5551325 = 2081747) B2081747
theorem B1299691 : Blo 1297967 1299691 := bstep (se 1 (by rfl) ⟨974768, by rfl⟩ : syracuseStep 1299691 = 1949537) B1949537
theorem B1299703 : Blo 1297967 1299703 := bstep (se 1 (by rfl) ⟨974777, by rfl⟩ : syracuseStep 1299703 = 1949555) B1949555
theorem B1299723 : Blo 1297967 1299723 := bstep (se 1 (by rfl) ⟨974792, by rfl⟩ : syracuseStep 1299723 = 1949585) B1949585
theorem B2192663 : Blo 1297967 2192663 := bstep (se 1 (by rfl) ⟨1644497, by rfl⟩ : syracuseStep 2192663 = 3288995) B3288995
theorem B1299735 : Blo 1297967 1299735 := bstep (se 1 (by rfl) ⟨974801, by rfl⟩ : syracuseStep 1299735 = 1949603) B1949603
theorem B1299755 : Blo 1297967 1299755 := bstep (se 1 (by rfl) ⟨974816, by rfl⟩ : syracuseStep 1299755 = 1949633) B1949633
theorem B1299767 : Blo 1297967 1299767 := bstep (se 1 (by rfl) ⟨974825, by rfl⟩ : syracuseStep 1299767 = 1949651) B1949651
theorem B1299787 : Blo 1297967 1299787 := bstep (se 1 (by rfl) ⟨974840, by rfl⟩ : syracuseStep 1299787 = 1949681) B1949681
theorem B1299799 : Blo 1297967 1299799 := bstep (se 1 (by rfl) ⟨974849, by rfl⟩ : syracuseStep 1299799 = 1949699) B1949699
theorem B1946969 : Blo 1297967 1946969 := bstep (se 2 (by rfl) ⟨730113, by rfl⟩ : syracuseStep 1946969 = 1460227) B1460227
theorem B9860453 : Blo 1297967 9860453 := bstep (se 4 (by rfl) ⟨924417, by rfl⟩ : syracuseStep 9860453 = 1848835) B1848835
theorem B1299819 : Blo 1297967 1299819 := bstep (se 1 (by rfl) ⟨974864, by rfl⟩ : syracuseStep 1299819 = 1949729) B1949729
theorem B1299831 : Blo 1297967 1299831 := bstep (se 1 (by rfl) ⟨974873, by rfl⟩ : syracuseStep 1299831 = 1949747) B1949747
theorem B2921867 : Blo 1297967 2921867 := bstep (se 1 (by rfl) ⟨2191400, by rfl⟩ : syracuseStep 2921867 = 4382801) B4382801
theorem B1643915 : Blo 1297967 1643915 := bstep (se 1 (by rfl) ⟨1232936, by rfl⟩ : syracuseStep 1643915 = 2465873) B2465873
theorem B1299851 : Blo 1297967 1299851 := bstep (se 1 (by rfl) ⟨974888, by rfl⟩ : syracuseStep 1299851 = 1949777) B1949777
theorem B2192791 : Blo 1297967 2192791 := bstep (se 1 (by rfl) ⟨1644593, by rfl⟩ : syracuseStep 2192791 = 3289187) B3289187
theorem B1299863 : Blo 1297967 1299863 := bstep (se 1 (by rfl) ⟨974897, by rfl⟩ : syracuseStep 1299863 = 1949795) B1949795
theorem B1299883 : Blo 1297967 1299883 := bstep (se 1 (by rfl) ⟨974912, by rfl⟩ : syracuseStep 1299883 = 1949825) B1949825
theorem B3208627 : Blo 1297967 3208627 := bstep (se 1 (by rfl) ⟨2406470, by rfl⟩ : syracuseStep 3208627 = 4812941) B4812941
theorem B1299895 : Blo 1297967 1299895 := bstep (se 1 (by rfl) ⟨974921, by rfl⟩ : syracuseStep 1299895 = 1949843) B1949843
theorem B2921921 : Blo 1297967 2921921 := bstep (se 2 (by rfl) ⟨1095720, by rfl⟩ : syracuseStep 2921921 = 2191441) B2191441
theorem B1947083 : Blo 1297967 1947083 := bstep (se 1 (by rfl) ⟨1460312, by rfl⟩ : syracuseStep 1947083 = 2920625) B2920625
theorem B1299915 : Blo 1297967 1299915 := bstep (se 1 (by rfl) ⟨974936, by rfl⟩ : syracuseStep 1299915 = 1949873) B1949873
theorem B1947095 : Blo 1297967 1947095 := bstep (se 1 (by rfl) ⟨1460321, by rfl⟩ : syracuseStep 1947095 = 2920643) B2920643
theorem B1299927 : Blo 1297967 1299927 := bstep (se 1 (by rfl) ⟨974945, by rfl⟩ : syracuseStep 1299927 = 1949891) B1949891
theorem B1299947 : Blo 1297967 1299947 := bstep (se 1 (by rfl) ⟨974960, by rfl⟩ : syracuseStep 1299947 = 1949921) B1949921
theorem B1299959 : Blo 1297967 1299959 := bstep (se 1 (by rfl) ⟨974969, by rfl⟩ : syracuseStep 1299959 = 1949939) B1949939
theorem B1947161 : Blo 1297967 1947161 := bstep (se 2 (by rfl) ⟨730185, by rfl⟩ : syracuseStep 1947161 = 1460371) B1460371
theorem B1316407 : Blo 1297967 1316407 := bstep (se 1 (by rfl) ⟨987305, by rfl⟩ : syracuseStep 1316407 = 1974611) B1974611
theorem B3700313 : Blo 1297967 3700313 := bstep (se 2 (by rfl) ⟨1387617, by rfl⟩ : syracuseStep 3700313 = 2775235) B2775235
theorem B1947275 : Blo 1297967 1947275 := bstep (se 1 (by rfl) ⟨1460456, by rfl⟩ : syracuseStep 1947275 = 2920913) B2920913
theorem B2963083 : Blo 1297967 2963083 := bstep (se 1 (by rfl) ⟨2222312, by rfl⟩ : syracuseStep 2963083 = 4444625) B4444625
theorem B1947287 : Blo 1297967 1947287 := bstep (se 1 (by rfl) ⟨1460465, by rfl⟩ : syracuseStep 1947287 = 2920931) B2920931
theorem B2922137 : Blo 1297967 2922137 := bstep (se 2 (by rfl) ⟨1095801, by rfl⟩ : syracuseStep 2922137 = 2191603) B2191603
theorem B7894745 : Blo 1297967 7894745 := bstep (se 2 (by rfl) ⟨2960529, by rfl⟩ : syracuseStep 7894745 = 5921059) B5921059
theorem B1947353 : Blo 1297967 1947353 := bstep (se 2 (by rfl) ⟨730257, by rfl⟩ : syracuseStep 1947353 = 1460515) B1460515
theorem B2922227 : Blo 1297967 2922227 := bstep (se 1 (by rfl) ⟨2191670, by rfl⟩ : syracuseStep 2922227 = 4383341) B4383341
theorem B2922263 : Blo 1297967 2922263 := bstep (se 1 (by rfl) ⟨2191697, by rfl⟩ : syracuseStep 2922263 = 4383395) B4383395
theorem B15791917 : Blo 1297967 15791917 := bstep (se 3 (by rfl) ⟨2960984, by rfl⟩ : syracuseStep 15791917 = 5921969) B5921969
theorem B7395137 : Blo 1297967 7395137 := bstep (se 2 (by rfl) ⟨2773176, by rfl⟩ : syracuseStep 7395137 = 5546353) B5546353
theorem B1947467 : Blo 1297967 1947467 := bstep (se 1 (by rfl) ⟨1460600, by rfl⟩ : syracuseStep 1947467 = 2921201) B2921201
theorem B9860939 : Blo 1297967 9860939 := bstep (se 1 (by rfl) ⟨7395704, by rfl⟩ : syracuseStep 9860939 = 14791409) B14791409
theorem B11097931 : Blo 1297967 11097931 := bstep (se 1 (by rfl) ⟨8323448, by rfl⟩ : syracuseStep 11097931 = 16646897) B16646897
theorem B1947479 : Blo 1297967 1947479 := bstep (se 1 (by rfl) ⟨1460609, by rfl⟩ : syracuseStep 1947479 = 2921219) B2921219
theorem B1849177 : Blo 1297967 1849177 := bstep (se 2 (by rfl) ⟨693441, by rfl⟩ : syracuseStep 1849177 = 1386883) B1386883
theorem B1947545 : Blo 1297967 1947545 := bstep (se 2 (by rfl) ⟨730329, by rfl⟩ : syracuseStep 1947545 = 1460659) B1460659
theorem B2922443 : Blo 1297967 2922443 := bstep (se 1 (by rfl) ⟨2191832, by rfl⟩ : syracuseStep 2922443 = 4383665) B4383665
theorem B2922497 : Blo 1297967 2922497 := bstep (se 2 (by rfl) ⟨1095936, by rfl⟩ : syracuseStep 2922497 = 2191873) B2191873
theorem B1947659 : Blo 1297967 1947659 := bstep (se 1 (by rfl) ⟨1460744, by rfl⟩ : syracuseStep 1947659 = 2921489) B2921489
theorem B2193419 : Blo 1297967 2193419 := bstep (se 1 (by rfl) ⟨1645064, by rfl⟩ : syracuseStep 2193419 = 3290129) B3290129
theorem B5928977 : Blo 1297967 5928977 := bstep (se 2 (by rfl) ⟨2223366, by rfl⟩ : syracuseStep 5928977 = 4446733) B4446733
theorem B4380695 : Blo 1297967 4380695 := bstep (se 1 (by rfl) ⟨3285521, by rfl⟩ : syracuseStep 4380695 = 6571043) B6571043
theorem B2250775 : Blo 1297967 2250775 := bstep (se 1 (by rfl) ⟨1688081, by rfl⟩ : syracuseStep 2250775 = 3376163) B3376163
theorem B1947671 : Blo 1297967 1947671 := bstep (se 1 (by rfl) ⟨1460753, by rfl⟩ : syracuseStep 1947671 = 2921507) B2921507
theorem B6330413 : Blo 1297967 6330413 := bstep (se 3 (by rfl) ⟨1186952, by rfl⟩ : syracuseStep 6330413 = 2373905) B2373905
theorem B1644619 : Blo 1297967 1644619 := bstep (se 1 (by rfl) ⟨1233464, by rfl⟩ : syracuseStep 1644619 = 2466929) B2466929
theorem B7026763 : Blo 1297967 7026763 := bstep (se 1 (by rfl) ⟨5270072, by rfl⟩ : syracuseStep 7026763 = 10540145) B10540145
theorem B1947737 : Blo 1297967 1947737 := bstep (se 2 (by rfl) ⟨730401, by rfl⟩ : syracuseStep 1947737 = 1460803) B1460803
theorem B11098205 : Blo 1297967 11098205 := bstep (se 3 (by rfl) ⟨2080913, by rfl⟩ : syracuseStep 11098205 = 4161827) B4161827
theorem B2193547 : Blo 1297967 2193547 := bstep (se 1 (by rfl) ⟨1645160, by rfl⟩ : syracuseStep 2193547 = 3290321) B3290321
theorem B1947851 : Blo 1297967 1947851 := bstep (se 1 (by rfl) ⟨1460888, by rfl⟩ : syracuseStep 1947851 = 2921777) B2921777
theorem B1947863 : Blo 1297967 1947863 := bstep (se 1 (by rfl) ⟨1460897, by rfl⟩ : syracuseStep 1947863 = 2921795) B2921795
theorem B2922713 : Blo 1297967 2922713 := bstep (se 2 (by rfl) ⟨1096017, by rfl⟩ : syracuseStep 2922713 = 2192035) B2192035
theorem B5921041 : Blo 1297967 5921041 := bstep (se 2 (by rfl) ⟨2220390, by rfl⟩ : syracuseStep 5921041 = 4440781) B4440781
theorem B1947929 : Blo 1297967 1947929 := bstep (se 2 (by rfl) ⟨730473, by rfl⟩ : syracuseStep 1947929 = 1460947) B1460947
theorem B2193689 : Blo 1297967 2193689 := bstep (se 2 (by rfl) ⟨822633, by rfl⟩ : syracuseStep 2193689 = 1645267) B1645267
theorem B3119411 : Blo 1297967 3119411 := bstep (se 1 (by rfl) ⟨2339558, by rfl⟩ : syracuseStep 3119411 = 4679117) B4679117
theorem B2922803 : Blo 1297967 2922803 := bstep (se 1 (by rfl) ⟨2192102, by rfl⟩ : syracuseStep 2922803 = 4384205) B4384205
theorem B5921099 : Blo 1297967 5921099 := bstep (se 1 (by rfl) ⟨4440824, by rfl⟩ : syracuseStep 5921099 = 8881649) B8881649
theorem B2922839 : Blo 1297967 2922839 := bstep (se 1 (by rfl) ⟨2192129, by rfl⟩ : syracuseStep 2922839 = 4384259) B4384259
theorem B1644887 : Blo 1297967 1644887 := bstep (se 1 (by rfl) ⟨1233665, by rfl⟩ : syracuseStep 1644887 = 2467331) B2467331
theorem B4929923 : Blo 1297967 4929923 := bstep (se 1 (by rfl) ⟨3697442, by rfl⟩ : syracuseStep 4929923 = 7394885) B7394885
theorem B1948043 : Blo 1297967 1948043 := bstep (se 1 (by rfl) ⟨1461032, by rfl⟩ : syracuseStep 1948043 = 2922065) B2922065
theorem B1948055 : Blo 1297967 1948055 := bstep (se 1 (by rfl) ⟨1461041, by rfl⟩ : syracuseStep 1948055 = 2922083) B2922083
theorem B1948121 : Blo 1297967 1948121 := bstep (se 2 (by rfl) ⟨730545, by rfl⟩ : syracuseStep 1948121 = 1461091) B1461091
theorem B2923019 : Blo 1297967 2923019 := bstep (se 1 (by rfl) ⟨2192264, by rfl⟩ : syracuseStep 2923019 = 4384529) B4384529
theorem B5552657 : Blo 1297967 5552657 := bstep (se 2 (by rfl) ⟨2082246, by rfl⟩ : syracuseStep 5552657 = 4164493) B4164493
theorem B14989859 : Blo 1297967 14989859 := bstep (se 1 (by rfl) ⟨11242394, by rfl⟩ : syracuseStep 14989859 = 22484789) B22484789
theorem B4381235 : Blo 1297967 4381235 := bstep (se 1 (by rfl) ⟨3285926, by rfl⟩ : syracuseStep 4381235 = 6571853) B6571853
theorem B2923073 : Blo 1297967 2923073 := bstep (se 2 (by rfl) ⟨1096152, by rfl⟩ : syracuseStep 2923073 = 2192305) B2192305
theorem B1948235 : Blo 1297967 1948235 := bstep (se 1 (by rfl) ⟨1461176, by rfl⟩ : syracuseStep 1948235 = 2922353) B2922353
theorem B1948247 : Blo 1297967 1948247 := bstep (se 1 (by rfl) ⟨1461185, by rfl⟩ : syracuseStep 1948247 = 2922371) B2922371
theorem B2964107 : Blo 1297967 2964107 := bstep (se 1 (by rfl) ⟨2223080, by rfl⟩ : syracuseStep 2964107 = 4446161) B4446161
theorem B1948313 : Blo 1297967 1948313 := bstep (se 2 (by rfl) ⟨730617, by rfl⟩ : syracuseStep 1948313 = 1461235) B1461235
theorem B24967885 : Blo 1297967 24967885 := bstep (se 3 (by rfl) ⟨4681478, by rfl⟩ : syracuseStep 24967885 = 9362957) B9362957
theorem B3119833 : Blo 1297967 3119833 := bstep (se 2 (by rfl) ⟨1169937, by rfl⟩ : syracuseStep 3119833 = 2339875) B2339875
theorem B2464499 : Blo 1297967 2464499 := bstep (se 1 (by rfl) ⟨1848374, by rfl⟩ : syracuseStep 2464499 = 3696749) B3696749
theorem B1948427 : Blo 1297967 1948427 := bstep (se 1 (by rfl) ⟨1461320, by rfl⟩ : syracuseStep 1948427 = 2922641) B2922641
theorem B1948439 : Blo 1297967 1948439 := bstep (se 1 (by rfl) ⟨1461329, by rfl⟩ : syracuseStep 1948439 = 2922659) B2922659
theorem B2923289 : Blo 1297967 2923289 := bstep (se 2 (by rfl) ⟨1096233, by rfl⟩ : syracuseStep 2923289 = 2192467) B2192467
theorem B3750707 : Blo 1297967 3750707 := bstep (se 1 (by rfl) ⟨2813030, by rfl⟩ : syracuseStep 3750707 = 5626061) B5626061
theorem B4381505 : Blo 1297967 4381505 := bstep (se 2 (by rfl) ⟨1643064, by rfl⟩ : syracuseStep 4381505 = 3286129) B3286129
theorem B23698241 : Blo 1297967 23698241 := bstep (se 2 (by rfl) ⟨8886840, by rfl⟩ : syracuseStep 23698241 = 17773681) B17773681
theorem B4930379 : Blo 1297967 4930379 := bstep (se 1 (by rfl) ⟨3697784, by rfl⟩ : syracuseStep 4930379 = 7395569) B7395569
theorem B1948505 : Blo 1297967 1948505 := bstep (se 2 (by rfl) ⟨730689, by rfl⟩ : syracuseStep 1948505 = 1461379) B1461379
theorem B9870173 : Blo 1297967 9870173 := bstep (se 3 (by rfl) ⟨1850657, by rfl⟩ : syracuseStep 9870173 = 3701315) B3701315
theorem B2923379 : Blo 1297967 2923379 := bstep (se 1 (by rfl) ⟨2192534, by rfl⟩ : syracuseStep 2923379 = 4385069) B4385069
theorem B2923415 : Blo 1297967 2923415 := bstep (se 1 (by rfl) ⟨2192561, by rfl⟩ : syracuseStep 2923415 = 4385123) B4385123
theorem B4996019 : Blo 1297967 4996019 := bstep (se 1 (by rfl) ⟨3747014, by rfl⟩ : syracuseStep 4996019 = 7494029) B7494029
theorem B1948619 : Blo 1297967 1948619 := bstep (se 1 (by rfl) ⟨1461464, by rfl⟩ : syracuseStep 1948619 = 2922929) B2922929
theorem B1948631 : Blo 1297967 1948631 := bstep (se 1 (by rfl) ⟨1461473, by rfl⟩ : syracuseStep 1948631 = 2922947) B2922947
theorem B4930577 : Blo 1297967 4930577 := bstep (se 2 (by rfl) ⟨1848966, by rfl⟩ : syracuseStep 4930577 = 3697933) B3697933
theorem B1948697 : Blo 1297967 1948697 := bstep (se 2 (by rfl) ⟨730761, by rfl⟩ : syracuseStep 1948697 = 1461523) B1461523
theorem B6667309 : Blo 1297967 6667309 := bstep (se 3 (by rfl) ⟨1250120, by rfl⟩ : syracuseStep 6667309 = 2500241) B2500241
theorem B5135425 : Blo 1297967 5135425 := bstep (se 2 (by rfl) ⟨1925784, by rfl⟩ : syracuseStep 5135425 = 3851569) B3851569
theorem B2923595 : Blo 1297967 2923595 := bstep (se 1 (by rfl) ⟨2192696, by rfl⟩ : syracuseStep 2923595 = 4385393) B4385393
theorem B11099267 : Blo 1297967 11099267 := bstep (se 1 (by rfl) ⟨8324450, by rfl⟩ : syracuseStep 11099267 = 16648901) B16648901
theorem B2923649 : Blo 1297967 2923649 := bstep (se 2 (by rfl) ⟨1096368, by rfl⟩ : syracuseStep 2923649 = 2192737) B2192737
theorem B1948811 : Blo 1297967 1948811 := bstep (se 1 (by rfl) ⟨1461608, by rfl⟩ : syracuseStep 1948811 = 2923217) B2923217
theorem B1948823 : Blo 1297967 1948823 := bstep (se 1 (by rfl) ⟨1461617, by rfl⟩ : syracuseStep 1948823 = 2923235) B2923235
theorem B1850521 : Blo 1297967 1850521 := bstep (se 2 (by rfl) ⟨693945, by rfl⟩ : syracuseStep 1850521 = 1387891) B1387891
theorem B2342081 : Blo 1297967 2342081 := bstep (se 2 (by rfl) ⟨878280, by rfl⟩ : syracuseStep 2342081 = 1756561) B1756561
theorem B2464985 : Blo 1297967 2464985 := bstep (se 2 (by rfl) ⟨924369, by rfl⟩ : syracuseStep 2464985 = 1848739) B1848739
theorem B1948889 : Blo 1297967 1948889 := bstep (se 2 (by rfl) ⟨730833, by rfl⟩ : syracuseStep 1948889 = 1461667) B1461667
theorem B1850635 : Blo 1297967 1850635 := bstep (se 1 (by rfl) ⟨1387976, by rfl⟩ : syracuseStep 1850635 = 2775953) B2775953
theorem B1949003 : Blo 1297967 1949003 := bstep (se 1 (by rfl) ⟨1461752, by rfl⟩ : syracuseStep 1949003 = 2923505) B2923505
theorem B1949015 : Blo 1297967 1949015 := bstep (se 1 (by rfl) ⟨1461761, by rfl⟩ : syracuseStep 1949015 = 2923523) B2923523
theorem B4742489 : Blo 1297967 4742489 := bstep (se 2 (by rfl) ⟨1778433, by rfl⟩ : syracuseStep 4742489 = 3556867) B3556867
theorem B2923865 : Blo 1297967 2923865 := bstep (se 2 (by rfl) ⟨1096449, by rfl⟩ : syracuseStep 2923865 = 2192899) B2192899
theorem B4382045 : Blo 1297967 4382045 := bstep (se 3 (by rfl) ⟨821633, by rfl⟩ : syracuseStep 4382045 = 1643267) B1643267
theorem B9362789 : Blo 1297967 9362789 := bstep (se 4 (by rfl) ⟨877761, by rfl⟩ : syracuseStep 9362789 = 1755523) B1755523
theorem B1949081 : Blo 1297967 1949081 := bstep (se 2 (by rfl) ⟨730905, by rfl⟩ : syracuseStep 1949081 = 1461811) B1461811
theorem B2923955 : Blo 1297967 2923955 := bstep (se 1 (by rfl) ⟨2192966, by rfl⟩ : syracuseStep 2923955 = 4385933) B4385933
theorem B2923991 : Blo 1297967 2923991 := bstep (se 1 (by rfl) ⟨2192993, by rfl⟩ : syracuseStep 2923991 = 4385987) B4385987
theorem B1949195 : Blo 1297967 1949195 := bstep (se 1 (by rfl) ⟨1461896, by rfl⟩ : syracuseStep 1949195 = 2923793) B2923793
theorem B1949207 : Blo 1297967 1949207 := bstep (se 1 (by rfl) ⟨1461905, by rfl⟩ : syracuseStep 1949207 = 2923811) B2923811
theorem B1949273 : Blo 1297967 1949273 := bstep (se 2 (by rfl) ⟨730977, by rfl⟩ : syracuseStep 1949273 = 1461955) B1461955
theorem B2924171 : Blo 1297967 2924171 := bstep (se 1 (by rfl) ⟨2193128, by rfl⟩ : syracuseStep 2924171 = 4386257) B4386257
theorem B2924225 : Blo 1297967 2924225 := bstep (se 2 (by rfl) ⟨1096584, by rfl⟩ : syracuseStep 2924225 = 2193169) B2193169
theorem B1949387 : Blo 1297967 1949387 := bstep (se 1 (by rfl) ⟨1462040, by rfl⟩ : syracuseStep 1949387 = 2924081) B2924081
theorem B1949399 : Blo 1297967 1949399 := bstep (se 1 (by rfl) ⟨1462049, by rfl⟩ : syracuseStep 1949399 = 2924099) B2924099
theorem B4931351 : Blo 1297967 4931351 := bstep (se 1 (by rfl) ⟨3698513, by rfl⟩ : syracuseStep 4931351 = 7397027) B7397027
theorem B1949465 : Blo 1297967 1949465 := bstep (se 2 (by rfl) ⟨731049, by rfl⟩ : syracuseStep 1949465 = 1462099) B1462099
theorem B1949579 : Blo 1297967 1949579 := bstep (se 1 (by rfl) ⟨1462184, by rfl⟩ : syracuseStep 1949579 = 2924369) B2924369
theorem B1949591 : Blo 1297967 1949591 := bstep (se 1 (by rfl) ⟨1462193, by rfl⟩ : syracuseStep 1949591 = 2924387) B2924387
theorem B2924441 : Blo 1297967 2924441 := bstep (se 2 (by rfl) ⟨1096665, by rfl⟩ : syracuseStep 2924441 = 2193331) B2193331
theorem B11091917 : Blo 1297967 11091917 := bstep (se 3 (by rfl) ⟨2079734, by rfl⟩ : syracuseStep 11091917 = 4159469) B4159469
theorem B1949657 : Blo 1297967 1949657 := bstep (se 2 (by rfl) ⟨731121, by rfl⟩ : syracuseStep 1949657 = 1462243) B1462243
theorem B4931549 : Blo 1297967 4931549 := bstep (se 3 (by rfl) ⟨924665, by rfl⟩ : syracuseStep 4931549 = 1849331) B1849331
theorem B2924531 : Blo 1297967 2924531 := bstep (se 1 (by rfl) ⟨2193398, by rfl⟩ : syracuseStep 2924531 = 4386797) B4386797
theorem B2252815 : Blo 1297967 2252815 := bstep (se 1 (by rfl) ⟨1689611, by rfl⟩ : syracuseStep 2252815 = 3379223) B3379223
theorem B1949711 : Blo 1297967 1949711 := bstep (se 1 (by rfl) ⟨1462283, by rfl⟩ : syracuseStep 1949711 = 2924567) B2924567
theorem B1949753 : Blo 1297967 1949753 := bstep (se 2 (by rfl) ⟨731157, by rfl⟩ : syracuseStep 1949753 = 1462315) B1462315
theorem B2924603 : Blo 1297967 2924603 := bstep (se 1 (by rfl) ⟨2193452, by rfl⟩ : syracuseStep 2924603 = 4386905) B4386905
theorem B1949831 : Blo 1297967 1949831 := bstep (se 1 (by rfl) ⟨1462373, by rfl⟩ : syracuseStep 1949831 = 2924747) B2924747
theorem B1949867 : Blo 1297967 1949867 := bstep (se 1 (by rfl) ⟨1462400, by rfl⟩ : syracuseStep 1949867 = 2924801) B2924801
theorem B2924729 : Blo 1297967 2924729 := bstep (se 2 (by rfl) ⟨1096773, by rfl⟩ : syracuseStep 2924729 = 2193547) B2193547
theorem B9863369 : Blo 1297967 9863369 := bstep (se 2 (by rfl) ⟨3698763, by rfl⟩ : syracuseStep 9863369 = 7397527) B7397527
theorem B1949897 : Blo 1297967 1949897 := bstep (se 2 (by rfl) ⟨731211, by rfl⟩ : syracuseStep 1949897 = 1462423) B1462423
theorem B4932049 : Blo 1297967 4932049 := bstep (se 2 (by rfl) ⟨1849518, by rfl⟩ : syracuseStep 4932049 = 3699037) B3699037
theorem B3121679 : Blo 1297967 3121679 := bstep (se 1 (by rfl) ⟨2341259, by rfl⟩ : syracuseStep 3121679 = 4682519) B4682519
theorem B1925689 : Blo 1297967 1925689 := bstep (se 2 (by rfl) ⟨722133, by rfl⟩ : syracuseStep 1925689 = 1444267) B1444267
theorem B3285623 : Blo 1297967 3285623 := bstep (se 1 (by rfl) ⟨2464217, by rfl⟩ : syracuseStep 3285623 = 4928435) B4928435
theorem B4932353 : Blo 1297967 4932353 := bstep (se 2 (by rfl) ⟨1849632, by rfl⟩ : syracuseStep 4932353 = 3699265) B3699265
theorem B4383503 : Blo 1297967 4383503 := bstep (se 1 (by rfl) ⟨3287627, by rfl⟩ : syracuseStep 4383503 = 6575255) B6575255
theorem B7897907 : Blo 1297967 7897907 := bstep (se 1 (by rfl) ⟨5923430, by rfl⟩ : syracuseStep 7897907 = 11846861) B11846861
theorem B8889139 : Blo 1297967 8889139 := bstep (se 1 (by rfl) ⟨6666854, by rfl⟩ : syracuseStep 8889139 = 13333709) B13333709
theorem B4383773 : Blo 1297967 4383773 := bstep (se 3 (by rfl) ⟨821957, by rfl⟩ : syracuseStep 4383773 = 1643915) B1643915
theorem B2466875 : Blo 1297967 2466875 := bstep (se 1 (by rfl) ⟨1850156, by rfl⟩ : syracuseStep 2466875 = 3700313) B3700313
theorem B4932809 : Blo 1297967 4932809 := bstep (se 2 (by rfl) ⟨1849803, by rfl⟩ : syracuseStep 4932809 = 3699607) B3699607
theorem B7898419 : Blo 1297967 7898419 := bstep (se 1 (by rfl) ⟨5923814, by rfl⟩ : syracuseStep 7898419 = 11847629) B11847629
theorem B4220275 : Blo 1297967 4220275 := bstep (se 1 (by rfl) ⟨3165206, by rfl⟩ : syracuseStep 4220275 = 6330413) B6330413
theorem B56935811 : Blo 1297967 56935811 := bstep (se 1 (by rfl) ⟨42701858, by rfl⟩ : syracuseStep 56935811 = 85403717) B85403717
theorem B8889745 : Blo 1297967 8889745 := bstep (se 2 (by rfl) ⟨3333654, by rfl⟩ : syracuseStep 8889745 = 6667309) B6667309
theorem B7398803 : Blo 1297967 7398803 := bstep (se 1 (by rfl) ⟨5549102, by rfl⟩ : syracuseStep 7398803 = 11098205) B11098205
theorem B1754555 : Blo 1297967 1754555 := bstep (se 1 (by rfl) ⟨1315916, by rfl⟩ : syracuseStep 1754555 = 2631833) B2631833
theorem B18990541 : Blo 1297967 18990541 := bstep (se 3 (by rfl) ⟨3560726, by rfl⟩ : syracuseStep 18990541 = 7121453) B7121453
theorem B2467361 : Blo 1297967 2467361 := bstep (se 2 (by rfl) ⟨925260, by rfl⟩ : syracuseStep 2467361 = 1850521) B1850521
theorem B3286615 : Blo 1297967 3286615 := bstep (se 1 (by rfl) ⟨2464961, by rfl⟩ : syracuseStep 3286615 = 4929923) B4929923
theorem B2467513 : Blo 1297967 2467513 := bstep (se 2 (by rfl) ⟨925317, by rfl⟩ : syracuseStep 2467513 = 1850635) B1850635
theorem B1976071 : Blo 1297967 1976071 := bstep (se 1 (by rfl) ⟨1482053, by rfl⟩ : syracuseStep 1976071 = 2964107) B2964107
theorem B2500471 : Blo 1297967 2500471 := bstep (se 1 (by rfl) ⟨1875353, by rfl⟩ : syracuseStep 2500471 = 3750707) B3750707
theorem B3286919 : Blo 1297967 3286919 := bstep (se 1 (by rfl) ⟨2465189, by rfl⟩ : syracuseStep 3286919 = 4930379) B4930379
theorem B6580115 : Blo 1297967 6580115 := bstep (se 1 (by rfl) ⟨4935086, by rfl⟩ : syracuseStep 6580115 = 9870173) B9870173
theorem B4278169 : Blo 1297967 4278169 := bstep (se 2 (by rfl) ⟨1604313, by rfl⟩ : syracuseStep 4278169 = 3208627) B3208627
theorem B3287051 : Blo 1297967 3287051 := bstep (se 1 (by rfl) ⟨2465288, by rfl⟩ : syracuseStep 3287051 = 4930577) B4930577
theorem B1755209 : Blo 1297967 1755209 := bstep (se 2 (by rfl) ⟨658203, by rfl⟩ : syracuseStep 1755209 = 1316407) B1316407
theorem B7399511 : Blo 1297967 7399511 := bstep (se 1 (by rfl) ⟨5549633, by rfl⟩ : syracuseStep 7399511 = 11099267) B11099267
theorem B1755307 : Blo 1297967 1755307 := bstep (se 1 (by rfl) ⟨1316480, by rfl⟩ : syracuseStep 1755307 = 2632961) B2632961
theorem B3950777 : Blo 1297967 3950777 := bstep (se 2 (by rfl) ⟨1481541, by rfl⟩ : syracuseStep 3950777 = 2963083) B2963083
theorem B6572339 : Blo 1297967 6572339 := bstep (se 1 (by rfl) ⟨4929254, by rfl⟩ : syracuseStep 6572339 = 9858509) B9858509
theorem B3164503 : Blo 1297967 3164503 := bstep (se 1 (by rfl) ⟨2373377, by rfl⟩ : syracuseStep 3164503 = 4746755) B4746755
theorem B1460623 : Blo 1297967 1460623 := bstep (se 1 (by rfl) ⟨1095467, by rfl⟩ : syracuseStep 1460623 = 2190935) B2190935
theorem B21055889 : Blo 1297967 21055889 := bstep (se 2 (by rfl) ⟨7895958, by rfl⟩ : syracuseStep 21055889 = 15791917) B15791917
theorem B4385177 : Blo 1297967 4385177 := bstep (se 2 (by rfl) ⟨1644441, by rfl⟩ : syracuseStep 4385177 = 3288883) B3288883
theorem B14797241 : Blo 1297967 14797241 := bstep (se 2 (by rfl) ⟨5548965, by rfl⟩ : syracuseStep 14797241 = 11097931) B11097931
theorem B3287567 : Blo 1297967 3287567 := bstep (se 1 (by rfl) ⟨2465675, by rfl⟩ : syracuseStep 3287567 = 4931351) B4931351
theorem B6572663 : Blo 1297967 6572663 := bstep (se 1 (by rfl) ⟨4929497, by rfl⟩ : syracuseStep 6572663 = 9858995) B9858995
theorem B3287699 : Blo 1297967 3287699 := bstep (se 1 (by rfl) ⟨2465774, by rfl⟩ : syracuseStep 3287699 = 4931549) B4931549
theorem B3001033 : Blo 1297967 3001033 := bstep (se 2 (by rfl) ⟨1125387, by rfl⟩ : syracuseStep 3001033 = 2250775) B2250775
theorem B1461127 : Blo 1297967 1461127 := bstep (se 1 (by rfl) ⟨1095845, by rfl⟩ : syracuseStep 1461127 = 2191691) B2191691
theorem B8326091 : Blo 1297967 8326091 := bstep (se 1 (by rfl) ⟨6244568, by rfl⟩ : syracuseStep 8326091 = 12489137) B12489137
theorem B3746827 : Blo 1297967 3746827 := bstep (se 1 (by rfl) ⟨2810120, by rfl⟩ : syracuseStep 3746827 = 5620241) B5620241
theorem B2190395 : Blo 1297967 2190395 := bstep (se 1 (by rfl) ⟨1642796, by rfl⟩ : syracuseStep 2190395 = 3285593) B3285593
theorem B1461307 : Blo 1297967 1461307 := bstep (se 1 (by rfl) ⟨1095980, by rfl⟩ : syracuseStep 1461307 = 2191961) B2191961
theorem B3697751 : Blo 1297967 3697751 := bstep (se 1 (by rfl) ⟨2773313, by rfl⟩ : syracuseStep 3697751 = 5546627) B5546627
theorem B4385879 : Blo 1297967 4385879 := bstep (se 1 (by rfl) ⟨3289409, by rfl⟩ : syracuseStep 4385879 = 6578819) B6578819
theorem B6245549 : Blo 1297967 6245549 := bstep (se 3 (by rfl) ⟨1171040, by rfl⟩ : syracuseStep 6245549 = 2342081) B2342081
theorem B36547789 : Blo 1297967 36547789 := bstep (se 3 (by rfl) ⟨6852710, by rfl⟩ : syracuseStep 36547789 = 13705421) B13705421
theorem B23702843 : Blo 1297967 23702843 := bstep (se 1 (by rfl) ⟨17777132, by rfl⟩ : syracuseStep 23702843 = 35554265) B35554265
theorem B2223545 : Blo 1297967 2223545 := bstep (se 2 (by rfl) ⟨833829, by rfl⟩ : syracuseStep 2223545 = 1667659) B1667659
theorem B2190793 : Blo 1297967 2190793 := bstep (se 2 (by rfl) ⟨821547, by rfl⟩ : syracuseStep 2190793 = 1643095) B1643095
theorem B1461775 : Blo 1297967 1461775 := bstep (se 1 (by rfl) ⟨1096331, by rfl⟩ : syracuseStep 1461775 = 2192663) B2192663
theorem B1297979 : Blo 1297967 1297979 := bstep (se 1 (by rfl) ⟨973484, by rfl⟩ : syracuseStep 1297979 = 1946969) B1946969
theorem B4386365 : Blo 1297967 4386365 := bstep (se 3 (by rfl) ⟨822443, by rfl⟩ : syracuseStep 4386365 = 1644887) B1644887
theorem B6573635 : Blo 1297967 6573635 := bstep (se 1 (by rfl) ⟨4930226, by rfl⟩ : syracuseStep 6573635 = 9860453) B9860453
theorem B12480101 : Blo 1297967 12480101 := bstep (se 4 (by rfl) ⟨1170009, by rfl⟩ : syracuseStep 12480101 = 2340019) B2340019
theorem B1298055 : Blo 1297967 1298055 := bstep (se 1 (by rfl) ⟨973541, by rfl⟩ : syracuseStep 1298055 = 1947083) B1947083
theorem B1298063 : Blo 1297967 1298063 := bstep (se 1 (by rfl) ⟨973547, by rfl⟩ : syracuseStep 1298063 = 1947095) B1947095
theorem B1298107 : Blo 1297967 1298107 := bstep (se 1 (by rfl) ⟨973580, by rfl⟩ : syracuseStep 1298107 = 1947161) B1947161
theorem B3288833 : Blo 1297967 3288833 := bstep (se 2 (by rfl) ⟨1233312, by rfl⟩ : syracuseStep 3288833 = 2466625) B2466625
theorem B1298183 : Blo 1297967 1298183 := bstep (se 1 (by rfl) ⟨973637, by rfl⟩ : syracuseStep 1298183 = 1947275) B1947275
theorem B1298191 : Blo 1297967 1298191 := bstep (se 1 (by rfl) ⟨973643, by rfl⟩ : syracuseStep 1298191 = 1947287) B1947287
theorem B5263163 : Blo 1297967 5263163 := bstep (se 1 (by rfl) ⟨3947372, by rfl⟩ : syracuseStep 5263163 = 7894745) B7894745
theorem B1298235 : Blo 1297967 1298235 := bstep (se 1 (by rfl) ⟨973676, by rfl⟩ : syracuseStep 1298235 = 1947353) B1947353
theorem B6328153 : Blo 1297967 6328153 := bstep (se 2 (by rfl) ⟨2373057, by rfl⟩ : syracuseStep 6328153 = 4746115) B4746115
theorem B6573959 : Blo 1297967 6573959 := bstep (se 1 (by rfl) ⟨4930469, by rfl⟩ : syracuseStep 6573959 = 9860939) B9860939
theorem B1298311 : Blo 1297967 1298311 := bstep (se 1 (by rfl) ⟨973733, by rfl⟩ : syracuseStep 1298311 = 1947467) B1947467
theorem B1298319 : Blo 1297967 1298319 := bstep (se 1 (by rfl) ⟨973739, by rfl⟩ : syracuseStep 1298319 = 1947479) B1947479
theorem B7401401 : Blo 1297967 7401401 := bstep (se 2 (by rfl) ⟨2775525, by rfl⟩ : syracuseStep 7401401 = 5551051) B5551051
theorem B1298363 : Blo 1297967 1298363 := bstep (se 1 (by rfl) ⟨973772, by rfl⟩ : syracuseStep 1298363 = 1947545) B1947545
theorem B1298439 : Blo 1297967 1298439 := bstep (se 1 (by rfl) ⟨973829, by rfl⟩ : syracuseStep 1298439 = 1947659) B1947659
theorem B1462279 : Blo 1297967 1462279 := bstep (se 1 (by rfl) ⟨1096709, by rfl⟩ : syracuseStep 1462279 = 2193419) B2193419
theorem B3952651 : Blo 1297967 3952651 := bstep (se 1 (by rfl) ⟨2964488, by rfl⟩ : syracuseStep 3952651 = 5928977) B5928977
theorem B2920463 : Blo 1297967 2920463 := bstep (se 1 (by rfl) ⟨2190347, by rfl⟩ : syracuseStep 2920463 = 4380695) B4380695
theorem B1298447 : Blo 1297967 1298447 := bstep (se 1 (by rfl) ⟨973835, by rfl⟩ : syracuseStep 1298447 = 1947671) B1947671
theorem B109555733 : Blo 1297967 109555733 := bstep (se 6 (by rfl) ⟨2567712, by rfl⟩ : syracuseStep 109555733 = 5135425) B5135425
theorem B2920481 : Blo 1297967 2920481 := bstep (se 2 (by rfl) ⟨1095180, by rfl⟩ : syracuseStep 2920481 = 2190361) B2190361
theorem B1298491 : Blo 1297967 1298491 := bstep (se 1 (by rfl) ⟨973868, by rfl⟩ : syracuseStep 1298491 = 1947737) B1947737
theorem B3289207 : Blo 1297967 3289207 := bstep (se 1 (by rfl) ⟨2466905, by rfl⟩ : syracuseStep 3289207 = 4933811) B4933811
theorem B1298567 : Blo 1297967 1298567 := bstep (se 1 (by rfl) ⟨973925, by rfl⟩ : syracuseStep 1298567 = 1947851) B1947851
theorem B2191495 : Blo 1297967 2191495 := bstep (se 1 (by rfl) ⟨1643621, by rfl⟩ : syracuseStep 2191495 = 3287243) B3287243
theorem B1298575 : Blo 1297967 1298575 := bstep (se 1 (by rfl) ⟨973931, by rfl⟩ : syracuseStep 1298575 = 1947863) B1947863
theorem B1298619 : Blo 1297967 1298619 := bstep (se 1 (by rfl) ⟨973964, by rfl⟩ : syracuseStep 1298619 = 1947929) B1947929
theorem B1462459 : Blo 1297967 1462459 := bstep (se 1 (by rfl) ⟨1096844, by rfl⟩ : syracuseStep 1462459 = 2193689) B2193689
theorem B1298695 : Blo 1297967 1298695 := bstep (se 1 (by rfl) ⟨974021, by rfl⟩ : syracuseStep 1298695 = 1948043) B1948043
theorem B1405199 : Blo 1297967 1405199 := bstep (se 1 (by rfl) ⟨1053899, by rfl⟩ : syracuseStep 1405199 = 2107799) B2107799
theorem B1298703 : Blo 1297967 1298703 := bstep (se 1 (by rfl) ⟨974027, by rfl⟩ : syracuseStep 1298703 = 1948055) B1948055
theorem B1298747 : Blo 1297967 1298747 := bstep (se 1 (by rfl) ⟨974060, by rfl⟩ : syracuseStep 1298747 = 1948121) B1948121
theorem B2920823 : Blo 1297967 2920823 := bstep (se 1 (by rfl) ⟨2190617, by rfl⟩ : syracuseStep 2920823 = 4381235) B4381235
theorem B1298823 : Blo 1297967 1298823 := bstep (se 1 (by rfl) ⟨974117, by rfl⟩ : syracuseStep 1298823 = 1948235) B1948235
theorem B1298831 : Blo 1297967 1298831 := bstep (se 1 (by rfl) ⟨974123, by rfl⟩ : syracuseStep 1298831 = 1948247) B1948247
theorem B1298875 : Blo 1297967 1298875 := bstep (se 1 (by rfl) ⟨974156, by rfl⟩ : syracuseStep 1298875 = 1948313) B1948313
theorem B1642999 : Blo 1297967 1642999 := bstep (se 1 (by rfl) ⟨1232249, by rfl⟩ : syracuseStep 1642999 = 2464499) B2464499
theorem B1298951 : Blo 1297967 1298951 := bstep (se 1 (by rfl) ⟨974213, by rfl⟩ : syracuseStep 1298951 = 1948427) B1948427
theorem B1298959 : Blo 1297967 1298959 := bstep (se 1 (by rfl) ⟨974219, by rfl⟩ : syracuseStep 1298959 = 1948439) B1948439
theorem B2921003 : Blo 1297967 2921003 := bstep (se 1 (by rfl) ⟨2190752, by rfl⟩ : syracuseStep 2921003 = 4381505) B4381505
theorem B15798827 : Blo 1297967 15798827 := bstep (se 1 (by rfl) ⟨11849120, by rfl⟩ : syracuseStep 15798827 = 23698241) B23698241
theorem B3289643 : Blo 1297967 3289643 := bstep (se 1 (by rfl) ⟨2467232, by rfl⟩ : syracuseStep 3289643 = 4934465) B4934465
theorem B1299003 : Blo 1297967 1299003 := bstep (se 1 (by rfl) ⟨974252, by rfl⟩ : syracuseStep 1299003 = 1948505) B1948505
theorem B3330679 : Blo 1297967 3330679 := bstep (se 1 (by rfl) ⟨2498009, by rfl⟩ : syracuseStep 3330679 = 4996019) B4996019
theorem B1299079 : Blo 1297967 1299079 := bstep (se 1 (by rfl) ⟨974309, by rfl⟩ : syracuseStep 1299079 = 1948619) B1948619
theorem B1299087 : Blo 1297967 1299087 := bstep (se 1 (by rfl) ⟨974315, by rfl⟩ : syracuseStep 1299087 = 1948631) B1948631
theorem B1299131 : Blo 1297967 1299131 := bstep (se 1 (by rfl) ⟨974348, by rfl⟩ : syracuseStep 1299131 = 1948697) B1948697
theorem B1299207 : Blo 1297967 1299207 := bstep (se 1 (by rfl) ⟨974405, by rfl⟩ : syracuseStep 1299207 = 1948811) B1948811
theorem B2192143 : Blo 1297967 2192143 := bstep (se 1 (by rfl) ⟨1644107, by rfl⟩ : syracuseStep 2192143 = 3288215) B3288215
theorem B1299215 : Blo 1297967 1299215 := bstep (se 1 (by rfl) ⟨974411, by rfl⟩ : syracuseStep 1299215 = 1948823) B1948823
theorem B11105039 : Blo 1297967 11105039 := bstep (se 1 (by rfl) ⟨8328779, by rfl⟩ : syracuseStep 11105039 = 16657559) B16657559
theorem B1643323 : Blo 1297967 1643323 := bstep (se 1 (by rfl) ⟨1232492, by rfl⟩ : syracuseStep 1643323 = 2464985) B2464985
theorem B1299259 : Blo 1297967 1299259 := bstep (se 1 (by rfl) ⟨974444, by rfl⟩ : syracuseStep 1299259 = 1948889) B1948889
theorem B1299335 : Blo 1297967 1299335 := bstep (se 1 (by rfl) ⟨974501, by rfl⟩ : syracuseStep 1299335 = 1949003) B1949003
theorem B1299343 : Blo 1297967 1299343 := bstep (se 1 (by rfl) ⟨974507, by rfl⟩ : syracuseStep 1299343 = 1949015) B1949015
theorem B2921363 : Blo 1297967 2921363 := bstep (se 1 (by rfl) ⟨2191022, by rfl⟩ : syracuseStep 2921363 = 4382045) B4382045
theorem B5551001 : Blo 1297967 5551001 := bstep (se 2 (by rfl) ⟨2081625, by rfl⟩ : syracuseStep 5551001 = 4163251) B4163251
theorem B1299387 : Blo 1297967 1299387 := bstep (se 1 (by rfl) ⟨974540, by rfl⟩ : syracuseStep 1299387 = 1949081) B1949081
theorem B2921417 : Blo 1297967 2921417 := bstep (se 2 (by rfl) ⟨1095531, by rfl⟩ : syracuseStep 2921417 = 2191063) B2191063
theorem B3511241 : Blo 1297967 3511241 := bstep (se 2 (by rfl) ⟨1316715, by rfl⟩ : syracuseStep 3511241 = 2633431) B2633431
theorem B4928465 : Blo 1297967 4928465 := bstep (se 2 (by rfl) ⟨1848174, by rfl⟩ : syracuseStep 4928465 = 3696349) B3696349
theorem B1299463 : Blo 1297967 1299463 := bstep (se 1 (by rfl) ⟨974597, by rfl⟩ : syracuseStep 1299463 = 1949195) B1949195
theorem B1299471 : Blo 1297967 1299471 := bstep (se 1 (by rfl) ⟨974603, by rfl⟩ : syracuseStep 1299471 = 1949207) B1949207
theorem B1299515 : Blo 1297967 1299515 := bstep (se 1 (by rfl) ⟨974636, by rfl⟩ : syracuseStep 1299515 = 1949273) B1949273
theorem B1299591 : Blo 1297967 1299591 := bstep (se 1 (by rfl) ⟨974693, by rfl⟩ : syracuseStep 1299591 = 1949387) B1949387
theorem B1299599 : Blo 1297967 1299599 := bstep (se 1 (by rfl) ⟨974699, by rfl⟩ : syracuseStep 1299599 = 1949399) B1949399
theorem B1299643 : Blo 1297967 1299643 := bstep (se 1 (by rfl) ⟨974732, by rfl⟩ : syracuseStep 1299643 = 1949465) B1949465
theorem B1299719 : Blo 1297967 1299719 := bstep (se 1 (by rfl) ⟨974789, by rfl⟩ : syracuseStep 1299719 = 1949579) B1949579
theorem B1299727 : Blo 1297967 1299727 := bstep (se 1 (by rfl) ⟨974795, by rfl⟩ : syracuseStep 1299727 = 1949591) B1949591
theorem B6010127 : Blo 1297967 6010127 := bstep (se 1 (by rfl) ⟨4507595, by rfl⟩ : syracuseStep 6010127 = 9015191) B9015191
theorem B1848619 : Blo 1297967 1848619 := bstep (se 1 (by rfl) ⟨1386464, by rfl⟩ : syracuseStep 1848619 = 2772929) B2772929
theorem B2192683 : Blo 1297967 2192683 := bstep (se 1 (by rfl) ⟨1644512, by rfl⟩ : syracuseStep 2192683 = 3289025) B3289025
theorem B7394611 : Blo 1297967 7394611 := bstep (se 1 (by rfl) ⟨5545958, by rfl⟩ : syracuseStep 7394611 = 11091917) B11091917
theorem B1299771 : Blo 1297967 1299771 := bstep (se 1 (by rfl) ⟨974828, by rfl⟩ : syracuseStep 1299771 = 1949657) B1949657
theorem B3290483 : Blo 1297967 3290483 := bstep (se 1 (by rfl) ⟨2467862, by rfl⟩ : syracuseStep 3290483 = 4935725) B4935725
theorem B1946999 : Blo 1297967 1946999 := bstep (se 1 (by rfl) ⟨1460249, by rfl⟩ : syracuseStep 1946999 = 2920499) B2920499
theorem B2774407 : Blo 1297967 2774407 := bstep (se 1 (by rfl) ⟨2080805, by rfl⟩ : syracuseStep 2774407 = 4161611) B4161611
theorem B1299847 : Blo 1297967 1299847 := bstep (se 1 (by rfl) ⟨974885, by rfl⟩ : syracuseStep 1299847 = 1949771) B1949771
theorem B3290503 : Blo 1297967 3290503 := bstep (se 1 (by rfl) ⟨2467877, by rfl⟩ : syracuseStep 3290503 = 4935755) B4935755
theorem B1947023 : Blo 1297967 1947023 := bstep (se 1 (by rfl) ⟨1460267, by rfl⟩ : syracuseStep 1947023 = 2920535) B2920535
theorem B1299855 : Blo 1297967 1299855 := bstep (se 1 (by rfl) ⟨974891, by rfl⟩ : syracuseStep 1299855 = 1949783) B1949783
theorem B4928921 : Blo 1297967 4928921 := bstep (se 2 (by rfl) ⟨1848345, by rfl⟩ : syracuseStep 4928921 = 3696691) B3696691
theorem B1947065 : Blo 1297967 1947065 := bstep (se 2 (by rfl) ⟨730149, by rfl⟩ : syracuseStep 1947065 = 1460299) B1460299
theorem B2192825 : Blo 1297967 2192825 := bstep (se 2 (by rfl) ⟨822309, by rfl⟩ : syracuseStep 2192825 = 1644619) B1644619
theorem B9369017 : Blo 1297967 9369017 := bstep (se 2 (by rfl) ⟨3513381, by rfl⟩ : syracuseStep 9369017 = 7026763) B7026763
theorem B1299899 : Blo 1297967 1299899 := bstep (se 1 (by rfl) ⟨974924, by rfl⟩ : syracuseStep 1299899 = 1949849) B1949849
theorem B1947143 : Blo 1297967 1947143 := bstep (se 1 (by rfl) ⟨1460357, by rfl⟩ : syracuseStep 1947143 = 2920715) B2920715
theorem B1316359 : Blo 1297967 1316359 := bstep (se 1 (by rfl) ⟨987269, by rfl⟩ : syracuseStep 1316359 = 1974539) B1974539
theorem B1848847 : Blo 1297967 1848847 := bstep (se 1 (by rfl) ⟨1386635, by rfl⟩ : syracuseStep 1848847 = 2773271) B2773271
theorem B50615837 : Blo 1297967 50615837 := bstep (se 3 (by rfl) ⟨9490469, by rfl⟩ : syracuseStep 50615837 = 18980939) B18980939
theorem B1947179 : Blo 1297967 1947179 := bstep (se 1 (by rfl) ⟨1460384, by rfl⟩ : syracuseStep 1947179 = 2920769) B2920769
theorem B6665771 : Blo 1297967 6665771 := bstep (se 1 (by rfl) ⟨4999328, by rfl⟩ : syracuseStep 6665771 = 9998657) B9998657
theorem B1947209 : Blo 1297967 1947209 := bstep (se 2 (by rfl) ⟨730203, by rfl⟩ : syracuseStep 1947209 = 1460407) B1460407
theorem B2922119 : Blo 1297967 2922119 := bstep (se 1 (by rfl) ⟨2191589, by rfl⟩ : syracuseStep 2922119 = 4383179) B4383179
theorem B1947323 : Blo 1297967 1947323 := bstep (se 1 (by rfl) ⟨1460492, by rfl⟩ : syracuseStep 1947323 = 2920985) B2920985
theorem B7894721 : Blo 1297967 7894721 := bstep (se 2 (by rfl) ⟨2960520, by rfl⟩ : syracuseStep 7894721 = 5921041) B5921041
theorem B1947383 : Blo 1297967 1947383 := bstep (se 1 (by rfl) ⟨1460537, by rfl⟩ : syracuseStep 1947383 = 2921075) B2921075
theorem B1644295 : Blo 1297967 1644295 := bstep (se 1 (by rfl) ⟨1233221, by rfl⟩ : syracuseStep 1644295 = 2466443) B2466443
theorem B1947407 : Blo 1297967 1947407 := bstep (se 1 (by rfl) ⟨1460555, by rfl⟩ : syracuseStep 1947407 = 2921111) B2921111
theorem B11851535 : Blo 1297967 11851535 := bstep (se 1 (by rfl) ⟨8888651, by rfl⟩ : syracuseStep 11851535 = 17777303) B17777303
theorem B3700495 : Blo 1297967 3700495 := bstep (se 1 (by rfl) ⟨2775371, by rfl⟩ : syracuseStep 3700495 = 5550743) B5550743
theorem B1947449 : Blo 1297967 1947449 := bstep (se 2 (by rfl) ⟨730293, by rfl⟩ : syracuseStep 1947449 = 1460587) B1460587
theorem B2922299 : Blo 1297967 2922299 := bstep (se 1 (by rfl) ⟨2191724, by rfl⟩ : syracuseStep 2922299 = 4383449) B4383449
theorem B3700541 : Blo 1297967 3700541 := bstep (se 3 (by rfl) ⟨693851, by rfl⟩ : syracuseStep 3700541 = 1387703) B1387703
theorem B4159367 : Blo 1297967 4159367 := bstep (se 1 (by rfl) ⟨3119525, by rfl⟩ : syracuseStep 4159367 = 6239051) B6239051
theorem B1947527 : Blo 1297967 1947527 := bstep (se 1 (by rfl) ⟨1460645, by rfl⟩ : syracuseStep 1947527 = 2921291) B2921291
theorem B6330257 : Blo 1297967 6330257 := bstep (se 2 (by rfl) ⟨2373846, by rfl⟩ : syracuseStep 6330257 = 4747693) B4747693
theorem B1947563 : Blo 1297967 1947563 := bstep (se 1 (by rfl) ⟨1460672, by rfl⟩ : syracuseStep 1947563 = 2921345) B2921345
theorem B5855161 : Blo 1297967 5855161 := bstep (se 2 (by rfl) ⟨2195685, by rfl⟩ : syracuseStep 5855161 = 4391371) B4391371
theorem B2922425 : Blo 1297967 2922425 := bstep (se 2 (by rfl) ⟨1095909, by rfl⟩ : syracuseStep 2922425 = 2191819) B2191819
theorem B1947593 : Blo 1297967 1947593 := bstep (se 2 (by rfl) ⟨730347, by rfl⟩ : syracuseStep 1947593 = 1460695) B1460695
theorem B4003841 : Blo 1297967 4003841 := bstep (se 2 (by rfl) ⟨1501440, by rfl⟩ : syracuseStep 4003841 = 3002881) B3002881
theorem B1947707 : Blo 1297967 1947707 := bstep (se 1 (by rfl) ⟨1460780, by rfl⟩ : syracuseStep 1947707 = 2921561) B2921561
theorem B3119219 : Blo 1297967 3119219 := bstep (se 1 (by rfl) ⟨2339414, by rfl⟩ : syracuseStep 3119219 = 4678829) B4678829
theorem B1947767 : Blo 1297967 1947767 := bstep (se 1 (by rfl) ⟨1460825, by rfl⟩ : syracuseStep 1947767 = 2921651) B2921651
theorem B2193527 : Blo 1297967 2193527 := bstep (se 1 (by rfl) ⟨1645145, by rfl⟩ : syracuseStep 2193527 = 3290291) B3290291
theorem B1947791 : Blo 1297967 1947791 := bstep (se 1 (by rfl) ⟨1460843, by rfl⟩ : syracuseStep 1947791 = 2921687) B2921687
theorem B3700883 : Blo 1297967 3700883 := bstep (se 1 (by rfl) ⟨2775662, by rfl⟩ : syracuseStep 3700883 = 5551325) B5551325
theorem B1644715 : Blo 1297967 1644715 := bstep (se 1 (by rfl) ⟨1233536, by rfl⟩ : syracuseStep 1644715 = 2467073) B2467073
theorem B1947833 : Blo 1297967 1947833 := bstep (se 2 (by rfl) ⟨730437, by rfl⟩ : syracuseStep 1947833 = 1460875) B1460875
theorem B1947911 : Blo 1297967 1947911 := bstep (se 1 (by rfl) ⟨1460933, by rfl⟩ : syracuseStep 1947911 = 2921867) B2921867
theorem B2922767 : Blo 1297967 2922767 := bstep (se 1 (by rfl) ⟨2192075, by rfl⟩ : syracuseStep 2922767 = 4384151) B4384151
theorem B33290513 : Blo 1297967 33290513 := bstep (se 2 (by rfl) ⟨12483942, by rfl⟩ : syracuseStep 33290513 = 24967885) B24967885
theorem B4159777 : Blo 1297967 4159777 := bstep (se 2 (by rfl) ⟨1559916, by rfl⟩ : syracuseStep 4159777 = 3119833) B3119833
theorem B2922785 : Blo 1297967 2922785 := bstep (se 2 (by rfl) ⟨1096044, by rfl⟩ : syracuseStep 2922785 = 2192089) B2192089
theorem B1947947 : Blo 1297967 1947947 := bstep (se 1 (by rfl) ⟨1460960, by rfl⟩ : syracuseStep 1947947 = 2921921) B2921921
theorem B5544251 : Blo 1297967 5544251 := bstep (se 1 (by rfl) ⟨4158188, by rfl⟩ : syracuseStep 5544251 = 8316377) B8316377
theorem B1947977 : Blo 1297967 1947977 := bstep (se 2 (by rfl) ⟨730491, by rfl⟩ : syracuseStep 1947977 = 1460983) B1460983
theorem B1644943 : Blo 1297967 1644943 := bstep (se 1 (by rfl) ⟨1233707, by rfl⟩ : syracuseStep 1644943 = 2467415) B2467415
theorem B6240665 : Blo 1297967 6240665 := bstep (se 2 (by rfl) ⟨2340249, by rfl⟩ : syracuseStep 6240665 = 4680499) B4680499
theorem B1948091 : Blo 1297967 1948091 := bstep (se 1 (by rfl) ⟨1461068, by rfl⟩ : syracuseStep 1948091 = 2922137) B2922137
theorem B54073817 : Blo 1297967 54073817 := bstep (se 2 (by rfl) ⟨20277681, by rfl⟩ : syracuseStep 54073817 = 40555363) B40555363
theorem B1948151 : Blo 1297967 1948151 := bstep (se 1 (by rfl) ⟨1461113, by rfl⟩ : syracuseStep 1948151 = 2922227) B2922227
theorem B1948175 : Blo 1297967 1948175 := bstep (se 1 (by rfl) ⟨1461131, by rfl⟩ : syracuseStep 1948175 = 2922263) B2922263
theorem B4930091 : Blo 1297967 4930091 := bstep (se 1 (by rfl) ⟨3697568, by rfl⟩ : syracuseStep 4930091 = 7395137) B7395137
theorem B1948217 : Blo 1297967 1948217 := bstep (se 2 (by rfl) ⟨730581, by rfl⟩ : syracuseStep 1948217 = 1461163) B1461163
theorem B4684349 : Blo 1297967 4684349 := bstep (se 3 (by rfl) ⟨878315, by rfl⟩ : syracuseStep 4684349 = 1756631) B1756631
theorem B2923127 : Blo 1297967 2923127 := bstep (se 1 (by rfl) ⟨2192345, by rfl⟩ : syracuseStep 2923127 = 4384691) B4384691
theorem B1948295 : Blo 1297967 1948295 := bstep (se 1 (by rfl) ⟨1461221, by rfl⟩ : syracuseStep 1948295 = 2922443) B2922443
theorem B1948331 : Blo 1297967 1948331 := bstep (se 1 (by rfl) ⟨1461248, by rfl⟩ : syracuseStep 1948331 = 2922497) B2922497
theorem B11246273 : Blo 1297967 11246273 := bstep (se 2 (by rfl) ⟨4217352, by rfl⟩ : syracuseStep 11246273 = 8434705) B8434705
theorem B1948361 : Blo 1297967 1948361 := bstep (se 2 (by rfl) ⟨730635, by rfl⟩ : syracuseStep 1948361 = 1461271) B1461271
theorem B7396069 : Blo 1297967 7396069 := bstep (se 4 (by rfl) ⟨693381, by rfl⟩ : syracuseStep 7396069 = 1386763) B1386763
theorem B2923307 : Blo 1297967 2923307 := bstep (se 1 (by rfl) ⟨2192480, by rfl⟩ : syracuseStep 2923307 = 4384961) B4384961
theorem B1948475 : Blo 1297967 1948475 := bstep (se 1 (by rfl) ⟨1461356, by rfl⟩ : syracuseStep 1948475 = 2922713) B2922713
theorem B2079607 : Blo 1297967 2079607 := bstep (se 1 (by rfl) ⟨1559705, by rfl⟩ : syracuseStep 2079607 = 3119411) B3119411
theorem B1948535 : Blo 1297967 1948535 := bstep (se 1 (by rfl) ⟨1461401, by rfl⟩ : syracuseStep 1948535 = 2922803) B2922803
theorem B3947399 : Blo 1297967 3947399 := bstep (se 1 (by rfl) ⟨2960549, by rfl⟩ : syracuseStep 3947399 = 5921099) B5921099
theorem B1948559 : Blo 1297967 1948559 := bstep (se 1 (by rfl) ⟨1461419, by rfl⟩ : syracuseStep 1948559 = 2922839) B2922839
theorem B1948601 : Blo 1297967 1948601 := bstep (se 2 (by rfl) ⟨730725, by rfl⟩ : syracuseStep 1948601 = 1461451) B1461451
theorem B1948679 : Blo 1297967 1948679 := bstep (se 1 (by rfl) ⟨1461509, by rfl⟩ : syracuseStep 1948679 = 2923019) B2923019
theorem B3701771 : Blo 1297967 3701771 := bstep (se 1 (by rfl) ⟨2776328, by rfl⟩ : syracuseStep 3701771 = 5552657) B5552657
theorem B9993239 : Blo 1297967 9993239 := bstep (se 1 (by rfl) ⟨7494929, by rfl⟩ : syracuseStep 9993239 = 14989859) B14989859
theorem B1948715 : Blo 1297967 1948715 := bstep (se 1 (by rfl) ⟨1461536, by rfl⟩ : syracuseStep 1948715 = 2923073) B2923073
theorem B2776123 : Blo 1297967 2776123 := bstep (se 1 (by rfl) ⟨2082092, by rfl⟩ : syracuseStep 2776123 = 4164185) B4164185
theorem B1948745 : Blo 1297967 1948745 := bstep (se 2 (by rfl) ⟨730779, by rfl⟩ : syracuseStep 1948745 = 1461559) B1461559
theorem B2923667 : Blo 1297967 2923667 := bstep (se 1 (by rfl) ⟨2192750, by rfl⟩ : syracuseStep 2923667 = 4385501) B4385501
theorem B3333305 : Blo 1297967 3333305 := bstep (se 2 (by rfl) ⟨1249989, by rfl⟩ : syracuseStep 3333305 = 2499979) B2499979
theorem B1948859 : Blo 1297967 1948859 := bstep (se 1 (by rfl) ⟨1461644, by rfl⟩ : syracuseStep 1948859 = 2923289) B2923289
theorem B2923721 : Blo 1297967 2923721 := bstep (se 2 (by rfl) ⟨1096395, by rfl⟩ : syracuseStep 2923721 = 2192791) B2192791
theorem B1948919 : Blo 1297967 1948919 := bstep (se 1 (by rfl) ⟨1461689, by rfl⟩ : syracuseStep 1948919 = 2923379) B2923379
theorem B1948943 : Blo 1297967 1948943 := bstep (se 1 (by rfl) ⟨1461707, by rfl⟩ : syracuseStep 1948943 = 2923415) B2923415
theorem B1948985 : Blo 1297967 1948985 := bstep (se 2 (by rfl) ⟨730869, by rfl⟩ : syracuseStep 1948985 = 1461739) B1461739
theorem B2465083 : Blo 1297967 2465083 := bstep (se 1 (by rfl) ⟨1848812, by rfl⟩ : syracuseStep 2465083 = 3697625) B3697625
theorem B6577523 : Blo 1297967 6577523 := bstep (se 1 (by rfl) ⟨4933142, by rfl⟩ : syracuseStep 6577523 = 9866285) B9866285
theorem B1949063 : Blo 1297967 1949063 := bstep (se 1 (by rfl) ⟨1461797, by rfl⟩ : syracuseStep 1949063 = 2923595) B2923595
theorem B4382099 : Blo 1297967 4382099 := bstep (se 1 (by rfl) ⟨3286574, by rfl⟩ : syracuseStep 4382099 = 6573149) B6573149
theorem B1949099 : Blo 1297967 1949099 := bstep (se 1 (by rfl) ⟨1461824, by rfl⟩ : syracuseStep 1949099 = 2923649) B2923649
theorem B1949129 : Blo 1297967 1949129 := bstep (se 2 (by rfl) ⟨730923, by rfl⟩ : syracuseStep 1949129 = 1461847) B1461847
theorem B3161659 : Blo 1297967 3161659 := bstep (se 1 (by rfl) ⟨2371244, by rfl⟩ : syracuseStep 3161659 = 4742489) B4742489
theorem B1949243 : Blo 1297967 1949243 := bstep (se 1 (by rfl) ⟨1461932, by rfl⟩ : syracuseStep 1949243 = 2923865) B2923865
theorem B6241859 : Blo 1297967 6241859 := bstep (se 1 (by rfl) ⟨4681394, by rfl⟩ : syracuseStep 6241859 = 9362789) B9362789
theorem B1949303 : Blo 1297967 1949303 := bstep (se 1 (by rfl) ⟨1461977, by rfl⟩ : syracuseStep 1949303 = 2923955) B2923955
theorem B1949327 : Blo 1297967 1949327 := bstep (se 1 (by rfl) ⟨1461995, by rfl⟩ : syracuseStep 1949327 = 2923991) B2923991
theorem B1949369 : Blo 1297967 1949369 := bstep (se 2 (by rfl) ⟨731013, by rfl⟩ : syracuseStep 1949369 = 1462027) B1462027
theorem B2342585 : Blo 1297967 2342585 := bstep (se 2 (by rfl) ⟨878469, by rfl⟩ : syracuseStep 2342585 = 1756939) B1756939
theorem B1949447 : Blo 1297967 1949447 := bstep (se 1 (by rfl) ⟨1462085, by rfl⟩ : syracuseStep 1949447 = 2924171) B2924171
theorem B2465569 : Blo 1297967 2465569 := bstep (se 2 (by rfl) ⟨924588, by rfl⟩ : syracuseStep 2465569 = 1849177) B1849177
theorem B1949483 : Blo 1297967 1949483 := bstep (se 1 (by rfl) ⟨1462112, by rfl⟩ : syracuseStep 1949483 = 2924225) B2924225
theorem B1949513 : Blo 1297967 1949513 := bstep (se 2 (by rfl) ⟨731067, by rfl⟩ : syracuseStep 1949513 = 1462135) B1462135
theorem B6578009 : Blo 1297967 6578009 := bstep (se 2 (by rfl) ⟨2466753, by rfl⟩ : syracuseStep 6578009 = 4933507) B4933507
theorem B2924423 : Blo 1297967 2924423 := bstep (se 1 (by rfl) ⟨2193317, by rfl⟩ : syracuseStep 2924423 = 4386635) B4386635
theorem B1949627 : Blo 1297967 1949627 := bstep (se 1 (by rfl) ⟨1462220, by rfl⟩ : syracuseStep 1949627 = 2924441) B2924441
theorem B1949687 : Blo 1297967 1949687 := bstep (se 1 (by rfl) ⟨1462265, by rfl⟩ : syracuseStep 1949687 = 2924531) B2924531
theorem B1949705 : Blo 1297967 1949705 := bstep (se 2 (by rfl) ⟨731139, by rfl⟩ : syracuseStep 1949705 = 1462279) B1462279
theorem B1949735 : Blo 1297967 1949735 := bstep (se 1 (by rfl) ⟨1462301, by rfl⟩ : syracuseStep 1949735 = 2924603) B2924603
theorem B1949819 : Blo 1297967 1949819 := bstep (se 1 (by rfl) ⟨1462364, by rfl⟩ : syracuseStep 1949819 = 2924729) B2924729
theorem B6578333 : Blo 1297967 6578333 := bstep (se 3 (by rfl) ⟨1233437, by rfl⟩ : syracuseStep 6578333 = 2466875) B2466875
theorem B1949945 : Blo 1297967 1949945 := bstep (se 2 (by rfl) ⟨731229, by rfl⟩ : syracuseStep 1949945 = 1462459) B1462459
theorem B2081119 : Blo 1297967 2081119 := bstep (se 1 (by rfl) ⟨1560839, by rfl⟩ : syracuseStep 2081119 = 3121679) B3121679
theorem B5546369 : Blo 1297967 5546369 := bstep (se 2 (by rfl) ⟨2079888, by rfl⟩ : syracuseStep 5546369 = 4159777) B4159777
theorem B4219337 : Blo 1297967 4219337 := bstep (se 2 (by rfl) ⟨1582251, by rfl⟩ : syracuseStep 4219337 = 3164503) B3164503
theorem B3285643 : Blo 1297967 3285643 := bstep (se 1 (by rfl) ⟨2464232, by rfl⟩ : syracuseStep 3285643 = 4928465) B4928465
theorem B4440905 : Blo 1297967 4440905 := bstep (se 2 (by rfl) ⟨1665339, by rfl⟩ : syracuseStep 4440905 = 3330679) B3330679
theorem B4006751 : Blo 1297967 4006751 := bstep (se 1 (by rfl) ⟨3005063, by rfl⟩ : syracuseStep 4006751 = 6010127) B6010127
theorem B4932535 : Blo 1297967 4932535 := bstep (se 1 (by rfl) ⟨3699401, by rfl⟩ : syracuseStep 4932535 = 7398803) B7398803
theorem B3285947 : Blo 1297967 3285947 := bstep (se 1 (by rfl) ⟨2464460, by rfl⟩ : syracuseStep 3285947 = 4928921) B4928921
theorem B33743891 : Blo 1297967 33743891 := bstep (se 1 (by rfl) ⟨25307918, by rfl⟩ : syracuseStep 33743891 = 50615837) B50615837
theorem B56149037 : Blo 1297967 56149037 := bstep (se 3 (by rfl) ⟨10527944, by rfl⟩ : syracuseStep 56149037 = 21055889) B21055889
theorem B4678813 : Blo 1297967 4678813 := bstep (se 3 (by rfl) ⟨877277, by rfl⟩ : syracuseStep 4678813 = 1754555) B1754555
theorem B2467027 : Blo 1297967 2467027 := bstep (se 1 (by rfl) ⟨1850270, by rfl⟩ : syracuseStep 2467027 = 3700541) B3700541
theorem B4220171 : Blo 1297967 4220171 := bstep (se 1 (by rfl) ⟨3165128, by rfl⟩ : syracuseStep 4220171 = 6330257) B6330257
theorem B4933007 : Blo 1297967 4933007 := bstep (se 1 (by rfl) ⟨3699755, by rfl⟩ : syracuseStep 4933007 = 7399511) B7399511
theorem B6579629 : Blo 1297967 6579629 := bstep (se 3 (by rfl) ⟨1233680, by rfl⟩ : syracuseStep 6579629 = 2467361) B2467361
theorem B2467255 : Blo 1297967 2467255 := bstep (se 1 (by rfl) ⟨1850441, by rfl⟩ : syracuseStep 2467255 = 3700883) B3700883
theorem B22193675 : Blo 1297967 22193675 := bstep (se 1 (by rfl) ⟨16645256, by rfl⟩ : syracuseStep 22193675 = 33290513) B33290513
theorem B3696167 : Blo 1297967 3696167 := bstep (se 1 (by rfl) ⟨2772125, by rfl⟩ : syracuseStep 3696167 = 5544251) B5544251
theorem B9864827 : Blo 1297967 9864827 := bstep (se 1 (by rfl) ⟨7398620, by rfl⟩ : syracuseStep 9864827 = 14797241) B14797241
theorem B3286727 : Blo 1297967 3286727 := bstep (se 1 (by rfl) ⟨2465045, by rfl⟩ : syracuseStep 3286727 = 4930091) B4930091
theorem B3286777 : Blo 1297967 3286777 := bstep (se 2 (by rfl) ⟨1232541, by rfl⟩ : syracuseStep 3286777 = 2465083) B2465083
theorem B7497515 : Blo 1297967 7497515 := bstep (se 1 (by rfl) ⟨5623136, by rfl⟩ : syracuseStep 7497515 = 11246273) B11246273
theorem B2631599 : Blo 1297967 2631599 := bstep (se 1 (by rfl) ⟨1973699, by rfl⟩ : syracuseStep 2631599 = 3947399) B3947399
theorem B2467847 : Blo 1297967 2467847 := bstep (se 1 (by rfl) ⟨1850885, by rfl⟩ : syracuseStep 2467847 = 3701771) B3701771
theorem B1755145 : Blo 1297967 1755145 := bstep (se 2 (by rfl) ⟨658179, by rfl⟩ : syracuseStep 1755145 = 1316359) B1316359
theorem B6662159 : Blo 1297967 6662159 := bstep (se 1 (by rfl) ⟨4996619, by rfl⟩ : syracuseStep 6662159 = 9993239) B9993239
theorem B1460263 : Blo 1297967 1460263 := bstep (se 1 (by rfl) ⟨1095197, by rfl⟩ : syracuseStep 1460263 = 2190395) B2190395
theorem B4163699 : Blo 1297967 4163699 := bstep (se 1 (by rfl) ⟨3122774, by rfl⟩ : syracuseStep 4163699 = 6245549) B6245549
theorem B2222203 : Blo 1297967 2222203 := bstep (se 1 (by rfl) ⟨1666652, by rfl⟩ : syracuseStep 2222203 = 3333305) B3333305
theorem B4385015 : Blo 1297967 4385015 := bstep (se 1 (by rfl) ⟨3288761, by rfl⟩ : syracuseStep 4385015 = 6577523) B6577523
theorem B4933993 : Blo 1297967 4933993 := bstep (se 2 (by rfl) ⟨1850247, by rfl⟩ : syracuseStep 4933993 = 3700495) B3700495
theorem B3287425 : Blo 1297967 3287425 := bstep (se 2 (by rfl) ⟨1232784, by rfl⟩ : syracuseStep 3287425 = 2465569) B2465569
theorem B5704225 : Blo 1297967 5704225 := bstep (se 2 (by rfl) ⟨2139084, by rfl⟩ : syracuseStep 5704225 = 4278169) B4278169
theorem B3508775 : Blo 1297967 3508775 := bstep (se 1 (by rfl) ⟨2631581, by rfl⟩ : syracuseStep 3508775 = 5263163) B5263163
theorem B4385339 : Blo 1297967 4385339 := bstep (se 1 (by rfl) ⟨3289004, by rfl⟩ : syracuseStep 4385339 = 6578009) B6578009
theorem B4934267 : Blo 1297967 4934267 := bstep (se 1 (by rfl) ⟨3700700, by rfl⟩ : syracuseStep 4934267 = 7401401) B7401401
theorem B10676909 : Blo 1297967 10676909 := bstep (se 3 (by rfl) ⟨2001920, by rfl⟩ : syracuseStep 10676909 = 4003841) B4003841
theorem B5270201 : Blo 1297967 5270201 := bstep (se 2 (by rfl) ⟨1976325, by rfl⟩ : syracuseStep 5270201 = 3952651) B3952651
theorem B4385609 : Blo 1297967 4385609 := bstep (se 2 (by rfl) ⟨1644603, by rfl⟩ : syracuseStep 4385609 = 3289207) B3289207
theorem B4680557 : Blo 1297967 4680557 := bstep (se 3 (by rfl) ⟨877604, by rfl⟩ : syracuseStep 4680557 = 1755209) B1755209
theorem B14805989 : Blo 1297967 14805989 := bstep (se 4 (by rfl) ⟨1388061, by rfl⟩ : syracuseStep 14805989 = 2776123) B2776123
theorem B2190415 : Blo 1297967 2190415 := bstep (se 1 (by rfl) ⟨1642811, by rfl⟩ : syracuseStep 2190415 = 3285623) B3285623
theorem B3288235 : Blo 1297967 3288235 := bstep (se 1 (by rfl) ⟨2466176, by rfl⟩ : syracuseStep 3288235 = 4932353) B4932353
theorem B2190665 : Blo 1297967 2190665 := bstep (se 2 (by rfl) ⟨821499, by rfl⟩ : syracuseStep 2190665 = 1642999) B1642999
theorem B3747197 : Blo 1297967 3747197 := bstep (se 3 (by rfl) ⟨702599, by rfl⟩ : syracuseStep 3747197 = 1405199) B1405199
theorem B2567585 : Blo 1297967 2567585 := bstep (se 2 (by rfl) ⟨962844, by rfl⟩ : syracuseStep 2567585 = 1925689) B1925689
theorem B3288539 : Blo 1297967 3288539 := bstep (se 1 (by rfl) ⟨2466404, by rfl⟩ : syracuseStep 3288539 = 4932809) B4932809
theorem B1297999 : Blo 1297967 1297999 := bstep (se 1 (by rfl) ⟨973499, by rfl⟩ : syracuseStep 1297999 = 1946999) B1946999
theorem B37957207 : Blo 1297967 37957207 := bstep (se 1 (by rfl) ⟨28467905, by rfl⟩ : syracuseStep 37957207 = 56935811) B56935811
theorem B1298015 : Blo 1297967 1298015 := bstep (se 1 (by rfl) ⟨973511, by rfl⟩ : syracuseStep 1298015 = 1947023) B1947023
theorem B1298043 : Blo 1297967 1298043 := bstep (se 1 (by rfl) ⟨973532, by rfl⟩ : syracuseStep 1298043 = 1947065) B1947065
theorem B1461883 : Blo 1297967 1461883 := bstep (se 1 (by rfl) ⟨1096412, by rfl⟩ : syracuseStep 1461883 = 2192825) B2192825
theorem B6246011 : Blo 1297967 6246011 := bstep (se 1 (by rfl) ⟨4684508, by rfl⟩ : syracuseStep 6246011 = 9369017) B9369017
theorem B1298095 : Blo 1297967 1298095 := bstep (se 1 (by rfl) ⟨973571, by rfl⟩ : syracuseStep 1298095 = 1947143) B1947143
theorem B1298119 : Blo 1297967 1298119 := bstep (se 1 (by rfl) ⟨973589, by rfl⟩ : syracuseStep 1298119 = 1947179) B1947179
theorem B1298139 : Blo 1297967 1298139 := bstep (se 1 (by rfl) ⟨973604, by rfl⟩ : syracuseStep 1298139 = 1947209) B1947209
theorem B16641773 : Blo 1297967 16641773 := bstep (se 3 (by rfl) ⟨3120332, by rfl⟩ : syracuseStep 16641773 = 6240665) B6240665
theorem B2191097 : Blo 1297967 2191097 := bstep (se 2 (by rfl) ⟨821661, by rfl⟩ : syracuseStep 2191097 = 1643323) B1643323
theorem B1298215 : Blo 1297967 1298215 := bstep (se 1 (by rfl) ⟨973661, by rfl⟩ : syracuseStep 1298215 = 1947323) B1947323
theorem B5263147 : Blo 1297967 5263147 := bstep (se 1 (by rfl) ⟨3947360, by rfl⟩ : syracuseStep 5263147 = 7894721) B7894721
theorem B2772809 : Blo 1297967 2772809 := bstep (se 2 (by rfl) ⟨1039803, by rfl⟩ : syracuseStep 2772809 = 2079607) B2079607
theorem B1298255 : Blo 1297967 1298255 := bstep (se 1 (by rfl) ⟨973691, by rfl⟩ : syracuseStep 1298255 = 1947383) B1947383
theorem B1298271 : Blo 1297967 1298271 := bstep (se 1 (by rfl) ⟨973703, by rfl⟩ : syracuseStep 1298271 = 1947407) B1947407
theorem B7901023 : Blo 1297967 7901023 := bstep (se 1 (by rfl) ⟨5925767, by rfl⟩ : syracuseStep 7901023 = 11851535) B11851535
theorem B1298299 : Blo 1297967 1298299 := bstep (se 1 (by rfl) ⟨973724, by rfl⟩ : syracuseStep 1298299 = 1947449) B1947449
theorem B2191279 : Blo 1297967 2191279 := bstep (se 1 (by rfl) ⟨1643459, by rfl⟩ : syracuseStep 2191279 = 3286919) B3286919
theorem B2772911 : Blo 1297967 2772911 := bstep (se 1 (by rfl) ⟨2079683, by rfl⟩ : syracuseStep 2772911 = 4159367) B4159367
theorem B1298351 : Blo 1297967 1298351 := bstep (se 1 (by rfl) ⟨973763, by rfl⟩ : syracuseStep 1298351 = 1947527) B1947527
theorem B4386743 : Blo 1297967 4386743 := bstep (se 1 (by rfl) ⟨3290057, by rfl⟩ : syracuseStep 4386743 = 6580115) B6580115
theorem B1298375 : Blo 1297967 1298375 := bstep (se 1 (by rfl) ⟨973781, by rfl⟩ : syracuseStep 1298375 = 1947563) B1947563
theorem B1298395 : Blo 1297967 1298395 := bstep (se 1 (by rfl) ⟨973796, by rfl⟩ : syracuseStep 1298395 = 1947593) B1947593
theorem B2191367 : Blo 1297967 2191367 := bstep (se 1 (by rfl) ⟨1643525, by rfl⟩ : syracuseStep 2191367 = 3287051) B3287051
theorem B1298471 : Blo 1297967 1298471 := bstep (se 1 (by rfl) ⟨973853, by rfl⟩ : syracuseStep 1298471 = 1947707) B1947707
theorem B1298511 : Blo 1297967 1298511 := bstep (se 1 (by rfl) ⟨973883, by rfl⟩ : syracuseStep 1298511 = 1947767) B1947767
theorem B1462351 : Blo 1297967 1462351 := bstep (se 1 (by rfl) ⟨1096763, by rfl⟩ : syracuseStep 1462351 = 2193527) B2193527
theorem B1298527 : Blo 1297967 1298527 := bstep (se 1 (by rfl) ⟨973895, by rfl⟩ : syracuseStep 1298527 = 1947791) B1947791
theorem B1298555 : Blo 1297967 1298555 := bstep (se 1 (by rfl) ⟨973916, by rfl⟩ : syracuseStep 1298555 = 1947833) B1947833
theorem B2633851 : Blo 1297967 2633851 := bstep (se 1 (by rfl) ⟨1975388, by rfl⟩ : syracuseStep 2633851 = 3950777) B3950777
theorem B1298607 : Blo 1297967 1298607 := bstep (se 1 (by rfl) ⟨973955, by rfl⟩ : syracuseStep 1298607 = 1947911) B1947911
theorem B1298631 : Blo 1297967 1298631 := bstep (se 1 (by rfl) ⟨973973, by rfl⟩ : syracuseStep 1298631 = 1947947) B1947947
theorem B1298651 : Blo 1297967 1298651 := bstep (se 1 (by rfl) ⟨973988, by rfl⟩ : syracuseStep 1298651 = 1947977) B1947977
theorem B48730385 : Blo 1297967 48730385 := bstep (se 2 (by rfl) ⟨18273894, by rfl⟩ : syracuseStep 48730385 = 36547789) B36547789
theorem B1298727 : Blo 1297967 1298727 := bstep (se 1 (by rfl) ⟨974045, by rfl⟩ : syracuseStep 1298727 = 1948091) B1948091
theorem B36049211 : Blo 1297967 36049211 := bstep (se 1 (by rfl) ⟨27036908, by rfl⟩ : syracuseStep 36049211 = 54073817) B54073817
theorem B1298767 : Blo 1297967 1298767 := bstep (se 1 (by rfl) ⟨974075, by rfl⟩ : syracuseStep 1298767 = 1948151) B1948151
theorem B1298783 : Blo 1297967 1298783 := bstep (se 1 (by rfl) ⟨974087, by rfl⟩ : syracuseStep 1298783 = 1948175) B1948175
theorem B2191711 : Blo 1297967 2191711 := bstep (se 1 (by rfl) ⟨1643783, by rfl⟩ : syracuseStep 2191711 = 3287567) B3287567
theorem B1298811 : Blo 1297967 1298811 := bstep (se 1 (by rfl) ⟨974108, by rfl⟩ : syracuseStep 1298811 = 1948217) B1948217
theorem B9859481 : Blo 1297967 9859481 := bstep (se 2 (by rfl) ⟨3697305, by rfl⟩ : syracuseStep 9859481 = 7394611) B7394611
theorem B10531225 : Blo 1297967 10531225 := bstep (se 2 (by rfl) ⟨3949209, by rfl⟩ : syracuseStep 10531225 = 7898419) B7898419
theorem B1298863 : Blo 1297967 1298863 := bstep (se 1 (by rfl) ⟨974147, by rfl⟩ : syracuseStep 1298863 = 1948295) B1948295
theorem B2191799 : Blo 1297967 2191799 := bstep (se 1 (by rfl) ⟨1643849, by rfl⟩ : syracuseStep 2191799 = 3287699) B3287699
theorem B1298887 : Blo 1297967 1298887 := bstep (se 1 (by rfl) ⟨974165, by rfl⟩ : syracuseStep 1298887 = 1948331) B1948331
theorem B1298907 : Blo 1297967 1298907 := bstep (se 1 (by rfl) ⟨974180, by rfl⟩ : syracuseStep 1298907 = 1948361) B1948361
theorem B3699209 : Blo 1297967 3699209 := bstep (se 2 (by rfl) ⟨1387203, by rfl⟩ : syracuseStep 3699209 = 2774407) B2774407
theorem B4387337 : Blo 1297967 4387337 := bstep (se 2 (by rfl) ⟨1645251, by rfl⟩ : syracuseStep 4387337 = 3290503) B3290503
theorem B1298983 : Blo 1297967 1298983 := bstep (se 1 (by rfl) ⟨974237, by rfl⟩ : syracuseStep 1298983 = 1948475) B1948475
theorem B1299023 : Blo 1297967 1299023 := bstep (se 1 (by rfl) ⟨974267, by rfl⟩ : syracuseStep 1299023 = 1948535) B1948535
theorem B1299039 : Blo 1297967 1299039 := bstep (se 1 (by rfl) ⟨974279, by rfl⟩ : syracuseStep 1299039 = 1948559) B1948559
theorem B2921057 : Blo 1297967 2921057 := bstep (se 2 (by rfl) ⟨1095396, by rfl⟩ : syracuseStep 2921057 = 2190793) B2190793
theorem B1299067 : Blo 1297967 1299067 := bstep (se 1 (by rfl) ⟨974300, by rfl⟩ : syracuseStep 1299067 = 1948601) B1948601
theorem B5550727 : Blo 1297967 5550727 := bstep (se 1 (by rfl) ⟨4163045, by rfl⟩ : syracuseStep 5550727 = 8326091) B8326091
theorem B1299119 : Blo 1297967 1299119 := bstep (se 1 (by rfl) ⟨974339, by rfl⟩ : syracuseStep 1299119 = 1948679) B1948679
theorem B1299143 : Blo 1297967 1299143 := bstep (se 1 (by rfl) ⟨974357, by rfl⟩ : syracuseStep 1299143 = 1948715) B1948715
theorem B1299163 : Blo 1297967 1299163 := bstep (se 1 (by rfl) ⟨974372, by rfl⟩ : syracuseStep 1299163 = 1948745) B1948745
theorem B4215545 : Blo 1297967 4215545 := bstep (se 2 (by rfl) ⟨1580829, by rfl⟩ : syracuseStep 4215545 = 3161659) B3161659
theorem B1299239 : Blo 1297967 1299239 := bstep (se 1 (by rfl) ⟨974429, by rfl⟩ : syracuseStep 1299239 = 1948859) B1948859
theorem B1299279 : Blo 1297967 1299279 := bstep (se 1 (by rfl) ⟨974459, by rfl⟩ : syracuseStep 1299279 = 1948919) B1948919
theorem B1299295 : Blo 1297967 1299295 := bstep (se 1 (by rfl) ⟨974471, by rfl⟩ : syracuseStep 1299295 = 1948943) B1948943
theorem B1299323 : Blo 1297967 1299323 := bstep (se 1 (by rfl) ⟨974492, by rfl⟩ : syracuseStep 1299323 = 1948985) B1948985
theorem B3290017 : Blo 1297967 3290017 := bstep (se 2 (by rfl) ⟨1233756, by rfl⟩ : syracuseStep 3290017 = 2467513) B2467513
theorem B1299375 : Blo 1297967 1299375 := bstep (se 1 (by rfl) ⟨974531, by rfl⟩ : syracuseStep 1299375 = 1949063) B1949063
theorem B2921399 : Blo 1297967 2921399 := bstep (se 1 (by rfl) ⟨2191049, by rfl⟩ : syracuseStep 2921399 = 4382099) B4382099
theorem B1299399 : Blo 1297967 1299399 := bstep (se 1 (by rfl) ⟨974549, by rfl⟩ : syracuseStep 1299399 = 1949099) B1949099
theorem B1299419 : Blo 1297967 1299419 := bstep (se 1 (by rfl) ⟨974564, by rfl⟩ : syracuseStep 1299419 = 1949129) B1949129
theorem B2192393 : Blo 1297967 2192393 := bstep (se 2 (by rfl) ⟨822147, by rfl⟩ : syracuseStep 2192393 = 1644295) B1644295
theorem B2634761 : Blo 1297967 2634761 := bstep (se 2 (by rfl) ⟨988035, by rfl⟩ : syracuseStep 2634761 = 1976071) B1976071
theorem B1299495 : Blo 1297967 1299495 := bstep (se 1 (by rfl) ⟨974621, by rfl⟩ : syracuseStep 1299495 = 1949243) B1949243
theorem B8320067 : Blo 1297967 8320067 := bstep (se 1 (by rfl) ⟨6240050, by rfl⟩ : syracuseStep 8320067 = 12480101) B12480101
theorem B1299535 : Blo 1297967 1299535 := bstep (se 1 (by rfl) ⟨974651, by rfl⟩ : syracuseStep 1299535 = 1949303) B1949303
theorem B1299551 : Blo 1297967 1299551 := bstep (se 1 (by rfl) ⟨974663, by rfl⟩ : syracuseStep 1299551 = 1949327) B1949327
theorem B1299579 : Blo 1297967 1299579 := bstep (se 1 (by rfl) ⟨974684, by rfl⟩ : syracuseStep 1299579 = 1949369) B1949369
theorem B1561723 : Blo 1297967 1561723 := bstep (se 1 (by rfl) ⟨1171292, by rfl⟩ : syracuseStep 1561723 = 2342585) B2342585
theorem B2192555 : Blo 1297967 2192555 := bstep (se 1 (by rfl) ⟨1644416, by rfl⟩ : syracuseStep 2192555 = 3288833) B3288833
theorem B1299631 : Blo 1297967 1299631 := bstep (se 1 (by rfl) ⟨974723, by rfl⟩ : syracuseStep 1299631 = 1949447) B1949447
theorem B1299655 : Blo 1297967 1299655 := bstep (se 1 (by rfl) ⟨974741, by rfl⟩ : syracuseStep 1299655 = 1949483) B1949483
theorem B1299675 : Blo 1297967 1299675 := bstep (se 1 (by rfl) ⟨974756, by rfl⟩ : syracuseStep 1299675 = 1949513) B1949513
theorem B1299751 : Blo 1297967 1299751 := bstep (se 1 (by rfl) ⟨974813, by rfl⟩ : syracuseStep 1299751 = 1949627) B1949627
theorem B1299791 : Blo 1297967 1299791 := bstep (se 1 (by rfl) ⟨974843, by rfl⟩ : syracuseStep 1299791 = 1949687) B1949687
theorem B1946975 : Blo 1297967 1946975 := bstep (se 1 (by rfl) ⟨1460231, by rfl⟩ : syracuseStep 1946975 = 2920463) B2920463
theorem B1299807 : Blo 1297967 1299807 := bstep (se 1 (by rfl) ⟨974855, by rfl⟩ : syracuseStep 1299807 = 1949711) B1949711
theorem B73037155 : Blo 1297967 73037155 := bstep (se 1 (by rfl) ⟨54777866, by rfl⟩ : syracuseStep 73037155 = 109555733) B109555733
theorem B1946987 : Blo 1297967 1946987 := bstep (se 1 (by rfl) ⟨1460240, by rfl⟩ : syracuseStep 1946987 = 2920481) B2920481
theorem B1299835 : Blo 1297967 1299835 := bstep (se 1 (by rfl) ⟨974876, by rfl⟩ : syracuseStep 1299835 = 1949753) B1949753
theorem B12015013 : Blo 1297967 12015013 := bstep (se 4 (by rfl) ⟨1126407, by rfl⟩ : syracuseStep 12015013 = 2252815) B2252815
theorem B1299887 : Blo 1297967 1299887 := bstep (se 1 (by rfl) ⟨974915, by rfl⟩ : syracuseStep 1299887 = 1949831) B1949831
theorem B1299911 : Blo 1297967 1299911 := bstep (se 1 (by rfl) ⟨974933, by rfl⟩ : syracuseStep 1299911 = 1949867) B1949867
theorem B6575579 : Blo 1297967 6575579 := bstep (se 1 (by rfl) ⟨4931684, by rfl⟩ : syracuseStep 6575579 = 9863369) B9863369
theorem B1299931 : Blo 1297967 1299931 := bstep (se 1 (by rfl) ⟨974948, by rfl⟩ : syracuseStep 1299931 = 1949897) B1949897
theorem B2921993 : Blo 1297967 2921993 := bstep (se 2 (by rfl) ⟨1095747, by rfl⟩ : syracuseStep 2921993 = 2191495) B2191495
theorem B2340409 : Blo 1297967 2340409 := bstep (se 2 (by rfl) ⟨877653, by rfl⟩ : syracuseStep 2340409 = 1755307) B1755307
theorem B2192953 : Blo 1297967 2192953 := bstep (se 2 (by rfl) ⟨822357, by rfl⟩ : syracuseStep 2192953 = 1644715) B1644715
theorem B1947215 : Blo 1297967 1947215 := bstep (se 1 (by rfl) ⟨1460411, by rfl⟩ : syracuseStep 1947215 = 2920823) B2920823
theorem B1947335 : Blo 1297967 1947335 := bstep (se 1 (by rfl) ⟨1460501, by rfl⟩ : syracuseStep 1947335 = 2921003) B2921003
theorem B10532551 : Blo 1297967 10532551 := bstep (se 1 (by rfl) ⟨7899413, by rfl⟩ : syracuseStep 10532551 = 15798827) B15798827
theorem B2193095 : Blo 1297967 2193095 := bstep (se 1 (by rfl) ⟨1644821, by rfl⟩ : syracuseStep 2193095 = 3289643) B3289643
theorem B2922335 : Blo 1297967 2922335 := bstep (se 1 (by rfl) ⟨2191751, by rfl⟩ : syracuseStep 2922335 = 4383503) B4383503
theorem B7403359 : Blo 1297967 7403359 := bstep (se 1 (by rfl) ⟨5552519, by rfl⟩ : syracuseStep 7403359 = 11105039) B11105039
theorem B1947497 : Blo 1297967 1947497 := bstep (se 2 (by rfl) ⟨730311, by rfl⟩ : syracuseStep 1947497 = 1460623) B1460623
theorem B2193257 : Blo 1297967 2193257 := bstep (se 2 (by rfl) ⟨822471, by rfl⟩ : syracuseStep 2193257 = 1644943) B1644943
theorem B5265271 : Blo 1297967 5265271 := bstep (se 1 (by rfl) ⟨3948953, by rfl⟩ : syracuseStep 5265271 = 7897907) B7897907
theorem B1947575 : Blo 1297967 1947575 := bstep (se 1 (by rfl) ⟨1460681, by rfl⟩ : syracuseStep 1947575 = 2921363) B2921363
theorem B3700667 : Blo 1297967 3700667 := bstep (se 1 (by rfl) ⟨2775500, by rfl⟩ : syracuseStep 3700667 = 5551001) B5551001
theorem B6576065 : Blo 1297967 6576065 := bstep (se 2 (by rfl) ⟨2466024, by rfl⟩ : syracuseStep 6576065 = 4932049) B4932049
theorem B1947611 : Blo 1297967 1947611 := bstep (se 1 (by rfl) ⟨1460708, by rfl⟩ : syracuseStep 1947611 = 2921417) B2921417
theorem B2340827 : Blo 1297967 2340827 := bstep (se 1 (by rfl) ⟨1755620, by rfl⟩ : syracuseStep 2340827 = 3511241) B3511241
theorem B2922515 : Blo 1297967 2922515 := bstep (se 1 (by rfl) ⟨2191886, by rfl⟩ : syracuseStep 2922515 = 4383773) B4383773
theorem B2193655 : Blo 1297967 2193655 := bstep (se 1 (by rfl) ⟨1645241, by rfl⟩ : syracuseStep 2193655 = 3290483) B3290483
theorem B9861425 : Blo 1297967 9861425 := bstep (se 2 (by rfl) ⟨3698034, by rfl⟩ : syracuseStep 9861425 = 7396069) B7396069
theorem B2922857 : Blo 1297967 2922857 := bstep (se 2 (by rfl) ⟨1096071, by rfl⟩ : syracuseStep 2922857 = 2192143) B2192143
theorem B16005509 : Blo 1297967 16005509 := bstep (se 4 (by rfl) ⟨1500516, by rfl⟩ : syracuseStep 16005509 = 3001033) B3001033
theorem B11852185 : Blo 1297967 11852185 := bstep (se 2 (by rfl) ⟨4444569, by rfl⟩ : syracuseStep 11852185 = 8889139) B8889139
theorem B1948079 : Blo 1297967 1948079 := bstep (se 1 (by rfl) ⟨1461059, by rfl⟩ : syracuseStep 1948079 = 2922119) B2922119
theorem B5929453 : Blo 1297967 5929453 := bstep (se 3 (by rfl) ⟨1111772, by rfl⟩ : syracuseStep 5929453 = 2223545) B2223545
theorem B1948169 : Blo 1297967 1948169 := bstep (se 2 (by rfl) ⟨730563, by rfl⟩ : syracuseStep 1948169 = 1461127) B1461127
theorem B1948199 : Blo 1297967 1948199 := bstep (se 1 (by rfl) ⟨1461149, by rfl⟩ : syracuseStep 1948199 = 2922299) B2922299
theorem B1948283 : Blo 1297967 1948283 := bstep (se 1 (by rfl) ⟨1461212, by rfl⟩ : syracuseStep 1948283 = 2922425) B2922425
theorem B4995769 : Blo 1297967 4995769 := bstep (se 2 (by rfl) ⟨1873413, by rfl⟩ : syracuseStep 4995769 = 3746827) B3746827
theorem B2079479 : Blo 1297967 2079479 := bstep (se 1 (by rfl) ⟨1559609, by rfl⟩ : syracuseStep 2079479 = 3119219) B3119219
theorem B1948409 : Blo 1297967 1948409 := bstep (se 2 (by rfl) ⟨730653, by rfl⟩ : syracuseStep 1948409 = 1461307) B1461307
theorem B17775389 : Blo 1297967 17775389 := bstep (se 3 (by rfl) ⟨3332885, by rfl⟩ : syracuseStep 17775389 = 6665771) B6665771
theorem B12491597 : Blo 1297967 12491597 := bstep (se 3 (by rfl) ⟨2342174, by rfl⟩ : syracuseStep 12491597 = 4684349) B4684349
theorem B1948511 : Blo 1297967 1948511 := bstep (se 1 (by rfl) ⟨1461383, by rfl⟩ : syracuseStep 1948511 = 2922767) B2922767
theorem B1948523 : Blo 1297967 1948523 := bstep (se 1 (by rfl) ⟨1461392, by rfl⟩ : syracuseStep 1948523 = 2922785) B2922785
theorem B4381559 : Blo 1297967 4381559 := bstep (se 1 (by rfl) ⟨3286169, by rfl⟩ : syracuseStep 4381559 = 6572339) B6572339
theorem B2923451 : Blo 1297967 2923451 := bstep (se 1 (by rfl) ⟨2192588, by rfl⟩ : syracuseStep 2923451 = 4385177) B4385177
theorem B2464825 : Blo 1297967 2464825 := bstep (se 2 (by rfl) ⟨924309, by rfl⟩ : syracuseStep 2464825 = 1848619) B1848619
theorem B2923577 : Blo 1297967 2923577 := bstep (se 2 (by rfl) ⟨1096341, by rfl⟩ : syracuseStep 2923577 = 2192683) B2192683
theorem B4381775 : Blo 1297967 4381775 := bstep (se 1 (by rfl) ⟨3286331, by rfl⟩ : syracuseStep 4381775 = 6572663) B6572663
theorem B1948751 : Blo 1297967 1948751 := bstep (se 1 (by rfl) ⟨1461563, by rfl⟩ : syracuseStep 1948751 = 2923127) B2923127
theorem B5627033 : Blo 1297967 5627033 := bstep (se 2 (by rfl) ⟨2110137, by rfl⟩ : syracuseStep 5627033 = 4220275) B4220275
theorem B11852993 : Blo 1297967 11852993 := bstep (se 2 (by rfl) ⟨4444872, by rfl⟩ : syracuseStep 11852993 = 8889745) B8889745
theorem B1948871 : Blo 1297967 1948871 := bstep (se 1 (by rfl) ⟨1461653, by rfl⟩ : syracuseStep 1948871 = 2923307) B2923307
theorem B25320721 : Blo 1297967 25320721 := bstep (se 2 (by rfl) ⟨9495270, by rfl⟩ : syracuseStep 25320721 = 18990541) B18990541
theorem B2465129 : Blo 1297967 2465129 := bstep (se 2 (by rfl) ⟨924423, by rfl⟩ : syracuseStep 2465129 = 1848847) B1848847
theorem B1949033 : Blo 1297967 1949033 := bstep (se 2 (by rfl) ⟨730887, by rfl⟩ : syracuseStep 1949033 = 1461775) B1461775
theorem B2465167 : Blo 1297967 2465167 := bstep (se 1 (by rfl) ⟨1848875, by rfl⟩ : syracuseStep 2465167 = 3697751) B3697751
theorem B2923919 : Blo 1297967 2923919 := bstep (se 1 (by rfl) ⟨2192939, by rfl⟩ : syracuseStep 2923919 = 4385879) B4385879
theorem B1949111 : Blo 1297967 1949111 := bstep (se 1 (by rfl) ⟨1461833, by rfl⟩ : syracuseStep 1949111 = 2923667) B2923667
theorem B4382153 : Blo 1297967 4382153 := bstep (se 2 (by rfl) ⟨1643307, by rfl⟩ : syracuseStep 4382153 = 3286615) B3286615
theorem B1949147 : Blo 1297967 1949147 := bstep (se 1 (by rfl) ⟨1461860, by rfl⟩ : syracuseStep 1949147 = 2923721) B2923721
theorem B15801895 : Blo 1297967 15801895 := bstep (se 1 (by rfl) ⟨11851421, by rfl⟩ : syracuseStep 15801895 = 23702843) B23702843
theorem B2924243 : Blo 1297967 2924243 := bstep (se 1 (by rfl) ⟨2193182, by rfl⟩ : syracuseStep 2924243 = 4386365) B4386365
theorem B4382423 : Blo 1297967 4382423 := bstep (se 1 (by rfl) ⟨3286817, by rfl⟩ : syracuseStep 4382423 = 6573635) B6573635
theorem B4161239 : Blo 1297967 4161239 := bstep (se 1 (by rfl) ⟨3120929, by rfl⟩ : syracuseStep 4161239 = 6241859) B6241859
theorem B8437537 : Blo 1297967 8437537 := bstep (se 2 (by rfl) ⟨3164076, by rfl⟩ : syracuseStep 8437537 = 6328153) B6328153
theorem B3333961 : Blo 1297967 3333961 := bstep (se 2 (by rfl) ⟨1250235, by rfl⟩ : syracuseStep 3333961 = 2500471) B2500471
theorem B7806881 : Blo 1297967 7806881 := bstep (se 2 (by rfl) ⟨2927580, by rfl⟩ : syracuseStep 7806881 = 5855161) B5855161
theorem B4382639 : Blo 1297967 4382639 := bstep (se 1 (by rfl) ⟨3286979, by rfl⟩ : syracuseStep 4382639 = 6573959) B6573959
theorem B1949615 : Blo 1297967 1949615 := bstep (se 1 (by rfl) ⟨1462211, by rfl⟩ : syracuseStep 1949615 = 2924423) B2924423
theorem B1949801 : Blo 1297967 1949801 := bstep (se 2 (by rfl) ⟨731175, by rfl⟩ : syracuseStep 1949801 = 1462351) B1462351
theorem B2924873 : Blo 1297967 2924873 := bstep (se 2 (by rfl) ⟨1096827, by rfl⟩ : syracuseStep 2924873 = 2193655) B2193655
theorem B2466139 : Blo 1297967 2466139 := bstep (se 1 (by rfl) ⟨1849604, by rfl⟩ : syracuseStep 2466139 = 3699209) B3699209
theorem B2924891 : Blo 1297967 2924891 := bstep (se 1 (by rfl) ⟨2193668, by rfl⟩ : syracuseStep 2924891 = 4387337) B4387337
theorem B6578657 : Blo 1297967 6578657 := bstep (se 2 (by rfl) ⟨2466996, by rfl⟩ : syracuseStep 6578657 = 4933993) B4933993
theorem B4383233 : Blo 1297967 4383233 := bstep (se 2 (by rfl) ⟨1643712, by rfl⟩ : syracuseStep 4383233 = 3287425) B3287425
theorem B14041633 : Blo 1297967 14041633 := bstep (se 2 (by rfl) ⟨5265612, by rfl⟩ : syracuseStep 14041633 = 10531225) B10531225
theorem B15802913 : Blo 1297967 15802913 := bstep (se 2 (by rfl) ⟨5926092, by rfl⟩ : syracuseStep 15802913 = 11852185) B11852185
theorem B7905937 : Blo 1297967 7905937 := bstep (se 2 (by rfl) ⟨2964726, by rfl⟩ : syracuseStep 7905937 = 5929453) B5929453
theorem B22495927 : Blo 1297967 22495927 := bstep (se 1 (by rfl) ⟨16871945, by rfl⟩ : syracuseStep 22495927 = 33743891) B33743891
theorem B5546711 : Blo 1297967 5546711 := bstep (se 1 (by rfl) ⟨4160033, by rfl⟩ : syracuseStep 5546711 = 8320067) B8320067
theorem B24953669 : Blo 1297967 24953669 := bstep (se 4 (by rfl) ⟨2339406, by rfl⟩ : syracuseStep 24953669 = 4678813) B4678813
theorem B6661025 : Blo 1297967 6661025 := bstep (se 2 (by rfl) ⟨2497884, by rfl⟩ : syracuseStep 6661025 = 4995769) B4995769
theorem B4383719 : Blo 1297967 4383719 := bstep (se 1 (by rfl) ⟨3287789, by rfl⟩ : syracuseStep 4383719 = 6575579) B6575579
theorem B14795783 : Blo 1297967 14795783 := bstep (se 1 (by rfl) ⟨11096837, by rfl⟩ : syracuseStep 14795783 = 22193675) B22193675
theorem B4998343 : Blo 1297967 4998343 := bstep (se 1 (by rfl) ⟨3748757, by rfl⟩ : syracuseStep 4998343 = 7497515) B7497515
theorem B1754399 : Blo 1297967 1754399 := bstep (se 1 (by rfl) ⟨1315799, by rfl⟩ : syracuseStep 1754399 = 2631599) B2631599
theorem B2467111 : Blo 1297967 2467111 := bstep (se 1 (by rfl) ⟨1850333, by rfl⟩ : syracuseStep 2467111 = 3700667) B3700667
theorem B4384043 : Blo 1297967 4384043 := bstep (se 1 (by rfl) ⟨3288032, by rfl⟩ : syracuseStep 4384043 = 6576065) B6576065
theorem B4441439 : Blo 1297967 4441439 := bstep (se 1 (by rfl) ⟨3331079, by rfl⟩ : syracuseStep 4441439 = 6662159) B6662159
theorem B3286433 : Blo 1297967 3286433 := bstep (se 2 (by rfl) ⟨1232412, by rfl⟩ : syracuseStep 3286433 = 2464825) B2464825
theorem B4384313 : Blo 1297967 4384313 := bstep (se 2 (by rfl) ⟨1644117, by rfl⟩ : syracuseStep 4384313 = 3288235) B3288235
theorem B33760961 : Blo 1297967 33760961 := bstep (se 2 (by rfl) ⟨12660360, by rfl⟩ : syracuseStep 33760961 = 25320721) B25320721
theorem B1386319 : Blo 1297967 1386319 := bstep (se 1 (by rfl) ⟨1039739, by rfl⟩ : syracuseStep 1386319 = 2079479) B2079479
theorem B3286889 : Blo 1297967 3286889 := bstep (se 2 (by rfl) ⟨1232583, by rfl⟩ : syracuseStep 3286889 = 2465167) B2465167
theorem B1460443 : Blo 1297967 1460443 := bstep (se 1 (by rfl) ⟨1095332, by rfl⟩ : syracuseStep 1460443 = 2190665) B2190665
theorem B10684669 : Blo 1297967 10684669 := bstep (se 3 (by rfl) ⟨2003375, by rfl⟩ : syracuseStep 10684669 = 4006751) B4006751
theorem B14043401 : Blo 1297967 14043401 := bstep (se 2 (by rfl) ⟨5266275, by rfl⟩ : syracuseStep 14043401 = 10532551) B10532551
theorem B11250049 : Blo 1297967 11250049 := bstep (se 2 (by rfl) ⟨4218768, by rfl⟩ : syracuseStep 11250049 = 8437537) B8437537
theorem B4164007 : Blo 1297967 4164007 := bstep (se 1 (by rfl) ⟨3123005, by rfl⟩ : syracuseStep 4164007 = 6246011) B6246011
theorem B11094515 : Blo 1297967 11094515 := bstep (se 1 (by rfl) ⟨8320886, by rfl⟩ : syracuseStep 11094515 = 16641773) B16641773
theorem B1460731 : Blo 1297967 1460731 := bstep (se 1 (by rfl) ⟨1095548, by rfl⟩ : syracuseStep 1460731 = 2191097) B2191097
theorem B5204587 : Blo 1297967 5204587 := bstep (se 1 (by rfl) ⟨3903440, by rfl⟩ : syracuseStep 5204587 = 7806881) B7806881
theorem B1460911 : Blo 1297967 1460911 := bstep (se 1 (by rfl) ⟨1095683, by rfl⟩ : syracuseStep 1460911 = 2191367) B2191367
theorem B6580925 : Blo 1297967 6580925 := bstep (se 3 (by rfl) ⟨1233923, by rfl⟩ : syracuseStep 6580925 = 2467847) B2467847
theorem B4385555 : Blo 1297967 4385555 := bstep (se 1 (by rfl) ⟨3289166, by rfl⟩ : syracuseStep 4385555 = 6578333) B6578333
theorem B3697579 : Blo 1297967 3697579 := bstep (se 1 (by rfl) ⟨2773184, by rfl⟩ : syracuseStep 3697579 = 5546369) B5546369
theorem B6572987 : Blo 1297967 6572987 := bstep (se 1 (by rfl) ⟨4929740, by rfl⟩ : syracuseStep 6572987 = 9859481) B9859481
theorem B1461199 : Blo 1297967 1461199 := bstep (se 1 (by rfl) ⟨1095899, by rfl⟩ : syracuseStep 1461199 = 2191799) B2191799
theorem B31607981 : Blo 1297967 31607981 := bstep (se 3 (by rfl) ⟨5926496, by rfl⟩ : syracuseStep 31607981 = 11852993) B11852993
theorem B2960603 : Blo 1297967 2960603 := bstep (se 1 (by rfl) ⟨2220452, by rfl⟩ : syracuseStep 2960603 = 4440905) B4440905
theorem B2190631 : Blo 1297967 2190631 := bstep (se 1 (by rfl) ⟨1642973, by rfl⟩ : syracuseStep 2190631 = 3285947) B3285947
theorem B1461595 : Blo 1297967 1461595 := bstep (se 1 (by rfl) ⟨1096196, by rfl⟩ : syracuseStep 1461595 = 2192393) B2192393
theorem B1756507 : Blo 1297967 1756507 := bstep (se 1 (by rfl) ⟨1317380, by rfl⟩ : syracuseStep 1756507 = 2634761) B2634761
theorem B37432691 : Blo 1297967 37432691 := bstep (se 1 (by rfl) ⟨28074518, by rfl⟩ : syracuseStep 37432691 = 56149037) B56149037
theorem B1461703 : Blo 1297967 1461703 := bstep (se 1 (by rfl) ⟨1096277, by rfl⟩ : syracuseStep 1461703 = 2192555) B2192555
theorem B2813447 : Blo 1297967 2813447 := bstep (se 1 (by rfl) ⟨2110085, by rfl⟩ : syracuseStep 2813447 = 4220171) B4220171
theorem B7400969 : Blo 1297967 7400969 := bstep (se 2 (by rfl) ⟨2775363, by rfl⟩ : syracuseStep 7400969 = 5550727) B5550727
theorem B1297983 : Blo 1297967 1297983 := bstep (se 1 (by rfl) ⟨973487, by rfl⟩ : syracuseStep 1297983 = 1946975) B1946975
theorem B1297991 : Blo 1297967 1297991 := bstep (se 1 (by rfl) ⟨973493, by rfl⟩ : syracuseStep 1297991 = 1946987) B1946987
theorem B3288671 : Blo 1297967 3288671 := bstep (se 1 (by rfl) ⟨2466503, by rfl⟩ : syracuseStep 3288671 = 4933007) B4933007
theorem B4386419 : Blo 1297967 4386419 := bstep (se 1 (by rfl) ⟨3289814, by rfl⟩ : syracuseStep 4386419 = 6579629) B6579629
theorem B1298143 : Blo 1297967 1298143 := bstep (se 1 (by rfl) ⟨973607, by rfl⟩ : syracuseStep 1298143 = 1947215) B1947215
theorem B1298223 : Blo 1297967 1298223 := bstep (se 1 (by rfl) ⟨973667, by rfl⟩ : syracuseStep 1298223 = 1947335) B1947335
theorem B2191151 : Blo 1297967 2191151 := bstep (se 1 (by rfl) ⟨1643363, by rfl⟩ : syracuseStep 2191151 = 3286727) B3286727
theorem B1462063 : Blo 1297967 1462063 := bstep (se 1 (by rfl) ⟨1096547, by rfl⟩ : syracuseStep 1462063 = 2193095) B2193095
theorem B11251565 : Blo 1297967 11251565 := bstep (se 3 (by rfl) ⟨2109668, by rfl⟩ : syracuseStep 11251565 = 4219337) B4219337
theorem B4386689 : Blo 1297967 4386689 := bstep (se 2 (by rfl) ⟨1645008, by rfl⟩ : syracuseStep 4386689 = 3290017) B3290017
theorem B1298331 : Blo 1297967 1298331 := bstep (se 1 (by rfl) ⟨973748, by rfl⟩ : syracuseStep 1298331 = 1947497) B1947497
theorem B1462171 : Blo 1297967 1462171 := bstep (se 1 (by rfl) ⟨1096628, by rfl⟩ : syracuseStep 1462171 = 2193257) B2193257
theorem B1298383 : Blo 1297967 1298383 := bstep (se 1 (by rfl) ⟨973787, by rfl⟩ : syracuseStep 1298383 = 1947575) B1947575
theorem B1298407 : Blo 1297967 1298407 := bstep (se 1 (by rfl) ⟨973805, by rfl⟩ : syracuseStep 1298407 = 1947611) B1947611
theorem B1560551 : Blo 1297967 1560551 := bstep (se 1 (by rfl) ⟨1170413, by rfl⟩ : syracuseStep 1560551 = 2340827) B2340827
theorem B2920553 : Blo 1297967 2920553 := bstep (se 2 (by rfl) ⟨1095207, by rfl⟩ : syracuseStep 2920553 = 2190415) B2190415
theorem B6574283 : Blo 1297967 6574283 := bstep (se 1 (by rfl) ⟨4930712, by rfl⟩ : syracuseStep 6574283 = 9861425) B9861425
theorem B10670339 : Blo 1297967 10670339 := bstep (se 1 (by rfl) ⟨8002754, by rfl⟩ : syracuseStep 10670339 = 16005509) B16005509
theorem B3289369 : Blo 1297967 3289369 := bstep (se 2 (by rfl) ⟨1233513, by rfl⟩ : syracuseStep 3289369 = 2467027) B2467027
theorem B1298719 : Blo 1297967 1298719 := bstep (se 1 (by rfl) ⟨974039, by rfl⟩ : syracuseStep 1298719 = 1948079) B1948079
theorem B1298779 : Blo 1297967 1298779 := bstep (se 1 (by rfl) ⟨974084, by rfl⟩ : syracuseStep 1298779 = 1948169) B1948169
theorem B2339183 : Blo 1297967 2339183 := bstep (se 1 (by rfl) ⟨1754387, by rfl⟩ : syracuseStep 2339183 = 3508775) B3508775
theorem B1298799 : Blo 1297967 1298799 := bstep (se 1 (by rfl) ⟨974099, by rfl⟩ : syracuseStep 1298799 = 1948199) B1948199
theorem B1298855 : Blo 1297967 1298855 := bstep (se 1 (by rfl) ⟨974141, by rfl⟩ : syracuseStep 1298855 = 1948283) B1948283
theorem B3289511 : Blo 1297967 3289511 := bstep (se 1 (by rfl) ⟨2467133, by rfl⟩ : syracuseStep 3289511 = 4934267) B4934267
theorem B97382873 : Blo 1297967 97382873 := bstep (se 2 (by rfl) ⟨36518577, by rfl⟩ : syracuseStep 97382873 = 73037155) B73037155
theorem B1298939 : Blo 1297967 1298939 := bstep (se 1 (by rfl) ⟨974204, by rfl⟩ : syracuseStep 1298939 = 1948409) B1948409
theorem B11850259 : Blo 1297967 11850259 := bstep (se 1 (by rfl) ⟨8887694, by rfl⟩ : syracuseStep 11850259 = 17775389) B17775389
theorem B16020017 : Blo 1297967 16020017 := bstep (se 2 (by rfl) ⟨6007506, by rfl⟩ : syracuseStep 16020017 = 12015013) B12015013
theorem B8327731 : Blo 1297967 8327731 := bstep (se 1 (by rfl) ⟨6245798, by rfl⟩ : syracuseStep 8327731 = 12491597) B12491597
theorem B1299007 : Blo 1297967 1299007 := bstep (se 1 (by rfl) ⟨974255, by rfl⟩ : syracuseStep 1299007 = 1948511) B1948511
theorem B1299015 : Blo 1297967 1299015 := bstep (se 1 (by rfl) ⟨974261, by rfl⟩ : syracuseStep 1299015 = 1948523) B1948523
theorem B3289673 : Blo 1297967 3289673 := bstep (se 2 (by rfl) ⟨1233627, by rfl⟩ : syracuseStep 3289673 = 2467255) B2467255
theorem B2921039 : Blo 1297967 2921039 := bstep (se 1 (by rfl) ⟨2190779, by rfl⟩ : syracuseStep 2921039 = 4381559) B4381559
theorem B2921183 : Blo 1297967 2921183 := bstep (se 1 (by rfl) ⟨2190887, by rfl⟩ : syracuseStep 2921183 = 4381775) B4381775
theorem B1299167 : Blo 1297967 1299167 := bstep (se 1 (by rfl) ⟨974375, by rfl⟩ : syracuseStep 1299167 = 1948751) B1948751
theorem B1299247 : Blo 1297967 1299247 := bstep (se 1 (by rfl) ⟨974435, by rfl⟩ : syracuseStep 1299247 = 1948871) B1948871
theorem B1643419 : Blo 1297967 1643419 := bstep (se 1 (by rfl) ⟨1232564, by rfl⟩ : syracuseStep 1643419 = 2465129) B2465129
theorem B1299355 : Blo 1297967 1299355 := bstep (se 1 (by rfl) ⟨974516, by rfl⟩ : syracuseStep 1299355 = 1949033) B1949033
theorem B1299407 : Blo 1297967 1299407 := bstep (se 1 (by rfl) ⟨974555, by rfl⟩ : syracuseStep 1299407 = 1949111) B1949111
theorem B2921435 : Blo 1297967 2921435 := bstep (se 1 (by rfl) ⟨2191076, by rfl⟩ : syracuseStep 2921435 = 4382153) B4382153
theorem B2192359 : Blo 1297967 2192359 := bstep (se 1 (by rfl) ⟨1644269, by rfl⟩ : syracuseStep 2192359 = 3288539) B3288539
theorem B1299431 : Blo 1297967 1299431 := bstep (se 1 (by rfl) ⟨974573, by rfl⟩ : syracuseStep 1299431 = 1949147) B1949147
theorem B7017529 : Blo 1297967 7017529 := bstep (se 2 (by rfl) ⟨2631573, by rfl⟩ : syracuseStep 7017529 = 5263147) B5263147
theorem B4445281 : Blo 1297967 4445281 := bstep (se 2 (by rfl) ⟨1666980, by rfl⟩ : syracuseStep 4445281 = 3333961) B3333961
theorem B7394429 : Blo 1297967 7394429 := bstep (se 3 (by rfl) ⟨1386455, by rfl⟩ : syracuseStep 7394429 = 2772911) B2772911
theorem B2921615 : Blo 1297967 2921615 := bstep (se 1 (by rfl) ⟨2191211, by rfl⟩ : syracuseStep 2921615 = 4382423) B4382423
theorem B2774159 : Blo 1297967 2774159 := bstep (se 1 (by rfl) ⟨2080619, by rfl⟩ : syracuseStep 2774159 = 4161239) B4161239
theorem B1848539 : Blo 1297967 1848539 := bstep (se 1 (by rfl) ⟨1386404, by rfl⟩ : syracuseStep 1848539 = 2772809) B2772809
theorem B2921705 : Blo 1297967 2921705 := bstep (se 2 (by rfl) ⟨1095639, by rfl⟩ : syracuseStep 2921705 = 2191279) B2191279
theorem B2921759 : Blo 1297967 2921759 := bstep (se 1 (by rfl) ⟨2191319, by rfl⟩ : syracuseStep 2921759 = 4382639) B4382639
theorem B1299743 : Blo 1297967 1299743 := bstep (se 1 (by rfl) ⟨974807, by rfl⟩ : syracuseStep 1299743 = 1949615) B1949615
theorem B1299803 : Blo 1297967 1299803 := bstep (se 1 (by rfl) ⟨974852, by rfl⟩ : syracuseStep 1299803 = 1949705) B1949705
theorem B2340193 : Blo 1297967 2340193 := bstep (se 2 (by rfl) ⟨877572, by rfl⟩ : syracuseStep 2340193 = 1755145) B1755145
theorem B1299823 : Blo 1297967 1299823 := bstep (se 1 (by rfl) ⟨974867, by rfl⟩ : syracuseStep 1299823 = 1949735) B1949735
theorem B1947017 : Blo 1297967 1947017 := bstep (se 2 (by rfl) ⟨730131, by rfl⟩ : syracuseStep 1947017 = 1460263) B1460263
theorem B1299879 : Blo 1297967 1299879 := bstep (se 1 (by rfl) ⟨974909, by rfl⟩ : syracuseStep 1299879 = 1949819) B1949819
theorem B2962937 : Blo 1297967 2962937 := bstep (se 2 (by rfl) ⟨1111101, by rfl⟩ : syracuseStep 2962937 = 2222203) B2222203
theorem B3511801 : Blo 1297967 3511801 := bstep (se 2 (by rfl) ⟨1316925, by rfl⟩ : syracuseStep 3511801 = 2633851) B2633851
theorem B1299963 : Blo 1297967 1299963 := bstep (se 1 (by rfl) ⟨974972, by rfl⟩ : syracuseStep 1299963 = 1949945) B1949945
theorem B32486923 : Blo 1297967 32486923 := bstep (se 1 (by rfl) ⟨24365192, by rfl⟩ : syracuseStep 32486923 = 48730385) B48730385
theorem B24032807 : Blo 1297967 24032807 := bstep (se 1 (by rfl) ⟨18024605, by rfl⟩ : syracuseStep 24032807 = 36049211) B36049211
theorem B1947371 : Blo 1297967 1947371 := bstep (se 1 (by rfl) ⟨1460528, by rfl⟩ : syracuseStep 1947371 = 2921057) B2921057
theorem B2922281 : Blo 1297967 2922281 := bstep (se 2 (by rfl) ⟨1095855, by rfl⟩ : syracuseStep 2922281 = 2191711) B2191711
theorem B2774825 : Blo 1297967 2774825 := bstep (se 2 (by rfl) ⟨1040559, by rfl⟩ : syracuseStep 2774825 = 2081119) B2081119
theorem B1947599 : Blo 1297967 1947599 := bstep (se 1 (by rfl) ⟨1460699, by rfl⟩ : syracuseStep 1947599 = 2921399) B2921399
theorem B121690133 : Blo 1297967 121690133 := bstep (se 6 (by rfl) ⟨2852112, by rfl⟩ : syracuseStep 121690133 = 5704225) B5704225
theorem B4380857 : Blo 1297967 4380857 := bstep (se 2 (by rfl) ⟨1642821, by rfl⟩ : syracuseStep 4380857 = 3285643) B3285643
theorem B1947995 : Blo 1297967 1947995 := bstep (se 1 (by rfl) ⟨1460996, by rfl⟩ : syracuseStep 1947995 = 2921993) B2921993
theorem B2464111 : Blo 1297967 2464111 := bstep (se 1 (by rfl) ⟨1848083, by rfl⟩ : syracuseStep 2464111 = 3696167) B3696167
theorem B6576551 : Blo 1297967 6576551 := bstep (se 1 (by rfl) ⟨4932413, by rfl⟩ : syracuseStep 6576551 = 9864827) B9864827
theorem B6846893 : Blo 1297967 6846893 := bstep (se 3 (by rfl) ⟨1283792, by rfl⟩ : syracuseStep 6846893 = 2567585) B2567585
theorem B1948223 : Blo 1297967 1948223 := bstep (se 1 (by rfl) ⟨1461167, by rfl⟩ : syracuseStep 1948223 = 2922335) B2922335
theorem B6576713 : Blo 1297967 6576713 := bstep (se 2 (by rfl) ⟨2466267, by rfl⟩ : syracuseStep 6576713 = 4932535) B4932535
theorem B1948343 : Blo 1297967 1948343 := bstep (se 1 (by rfl) ⟨1461257, by rfl⟩ : syracuseStep 1948343 = 2922515) B2922515
theorem B2775799 : Blo 1297967 2775799 := bstep (se 1 (by rfl) ⟨2081849, by rfl⟩ : syracuseStep 2775799 = 4163699) B4163699
theorem B2923343 : Blo 1297967 2923343 := bstep (se 1 (by rfl) ⟨2192507, by rfl⟩ : syracuseStep 2923343 = 4385015) B4385015
theorem B1948571 : Blo 1297967 1948571 := bstep (se 1 (by rfl) ⟨1461428, by rfl⟩ : syracuseStep 1948571 = 2922857) B2922857
theorem B2923559 : Blo 1297967 2923559 := bstep (se 1 (by rfl) ⟨2192669, by rfl⟩ : syracuseStep 2923559 = 4385339) B4385339
theorem B7117939 : Blo 1297967 7117939 := bstep (se 1 (by rfl) ⟨5338454, by rfl⟩ : syracuseStep 7117939 = 10676909) B10676909
theorem B3513467 : Blo 1297967 3513467 := bstep (se 1 (by rfl) ⟨2635100, by rfl⟩ : syracuseStep 3513467 = 5270201) B5270201
theorem B2923739 : Blo 1297967 2923739 := bstep (se 1 (by rfl) ⟨2192804, by rfl⟩ : syracuseStep 2923739 = 4385609) B4385609
theorem B3120371 : Blo 1297967 3120371 := bstep (se 1 (by rfl) ⟨2340278, by rfl⟩ : syracuseStep 3120371 = 4680557) B4680557
theorem B1948967 : Blo 1297967 1948967 := bstep (se 1 (by rfl) ⟨1461725, by rfl⟩ : syracuseStep 1948967 = 2923451) B2923451
theorem B9870659 : Blo 1297967 9870659 := bstep (se 1 (by rfl) ⟨7402994, by rfl⟩ : syracuseStep 9870659 = 14805989) B14805989
theorem B1949051 : Blo 1297967 1949051 := bstep (se 1 (by rfl) ⟨1461788, by rfl⟩ : syracuseStep 1949051 = 2923577) B2923577
theorem B21069193 : Blo 1297967 21069193 := bstep (se 2 (by rfl) ⟨7900947, by rfl⟩ : syracuseStep 21069193 = 15801895) B15801895
theorem B3120545 : Blo 1297967 3120545 := bstep (se 2 (by rfl) ⟨1170204, by rfl⟩ : syracuseStep 3120545 = 2340409) B2340409
theorem B2923937 : Blo 1297967 2923937 := bstep (se 2 (by rfl) ⟨1096476, by rfl⟩ : syracuseStep 2923937 = 2192953) B2192953
theorem B3751355 : Blo 1297967 3751355 := bstep (se 1 (by rfl) ⟨2813516, by rfl⟩ : syracuseStep 3751355 = 5627033) B5627033
theorem B50609609 : Blo 1297967 50609609 := bstep (se 2 (by rfl) ⟨18978603, by rfl⟩ : syracuseStep 50609609 = 37957207) B37957207
theorem B1949177 : Blo 1297967 1949177 := bstep (se 2 (by rfl) ⟨730941, by rfl⟩ : syracuseStep 1949177 = 1461883) B1461883
theorem B2498131 : Blo 1297967 2498131 := bstep (se 1 (by rfl) ⟨1873598, by rfl⟩ : syracuseStep 2498131 = 3747197) B3747197
theorem B1949279 : Blo 1297967 1949279 := bstep (se 1 (by rfl) ⟨1461959, by rfl⟩ : syracuseStep 1949279 = 2923919) B2923919
theorem B4382369 : Blo 1297967 4382369 := bstep (se 2 (by rfl) ⟨1643388, by rfl⟩ : syracuseStep 4382369 = 3286777) B3286777
theorem B10534697 : Blo 1297967 10534697 := bstep (se 2 (by rfl) ⟨3950511, by rfl⟩ : syracuseStep 10534697 = 7901023) B7901023
theorem B9871145 : Blo 1297967 9871145 := bstep (se 2 (by rfl) ⟨3701679, by rfl⟩ : syracuseStep 9871145 = 7403359) B7403359
theorem B1949495 : Blo 1297967 1949495 := bstep (se 1 (by rfl) ⟨1462121, by rfl⟩ : syracuseStep 1949495 = 2924243) B2924243
theorem B7020361 : Blo 1297967 7020361 := bstep (se 2 (by rfl) ⟨2632635, by rfl⟩ : syracuseStep 7020361 = 5265271) B5265271
theorem B33316757 : Blo 1297967 33316757 := bstep (se 6 (by rfl) ⟨780861, by rfl⟩ : syracuseStep 33316757 = 1561723) B1561723
theorem B44965813 : Blo 1297967 44965813 := bstep (se 5 (by rfl) ⟨2107772, by rfl⟩ : syracuseStep 44965813 = 4215545) B4215545
theorem B2924495 : Blo 1297967 2924495 := bstep (se 1 (by rfl) ⟨2193371, by rfl⟩ : syracuseStep 2924495 = 4386743) B4386743
theorem B4382855 : Blo 1297967 4382855 := bstep (se 1 (by rfl) ⟨3287141, by rfl⟩ : syracuseStep 4382855 = 6574283) B6574283
theorem B1949915 : Blo 1297967 1949915 := bstep (se 1 (by rfl) ⟨1462436, by rfl⟩ : syracuseStep 1949915 = 2924873) B2924873
theorem B1949927 : Blo 1297967 1949927 := bstep (se 1 (by rfl) ⟨1462445, by rfl⟩ : syracuseStep 1949927 = 2924891) B2924891
theorem B64921915 : Blo 1297967 64921915 := bstep (se 1 (by rfl) ⟨48691436, by rfl⟩ : syracuseStep 64921915 = 97382873) B97382873
theorem B14246225 : Blo 1297967 14246225 := bstep (se 2 (by rfl) ⟨5342334, by rfl⟩ : syracuseStep 14246225 = 10684669) B10684669
theorem B10535275 : Blo 1297967 10535275 := bstep (se 1 (by rfl) ⟨7901456, by rfl⟩ : syracuseStep 10535275 = 15802913) B15802913
theorem B3285481 : Blo 1297967 3285481 := bstep (se 2 (by rfl) ⟨1232055, by rfl⟩ : syracuseStep 3285481 = 2464111) B2464111
theorem B15000065 : Blo 1297967 15000065 := bstep (se 2 (by rfl) ⟨5625024, by rfl⟩ : syracuseStep 15000065 = 11250049) B11250049
theorem B37962341 : Blo 1297967 37962341 := bstep (se 4 (by rfl) ⟨3558969, by rfl⟩ : syracuseStep 37962341 = 7117939) B7117939
theorem B4440683 : Blo 1297967 4440683 := bstep (se 1 (by rfl) ⟨3330512, by rfl⟩ : syracuseStep 4440683 = 6661025) B6661025
theorem B9863855 : Blo 1297967 9863855 := bstep (se 1 (by rfl) ⟨7397891, by rfl⟩ : syracuseStep 9863855 = 14795783) B14795783
theorem B4678397 : Blo 1297967 4678397 := bstep (se 3 (by rfl) ⟨877199, by rfl⟩ : syracuseStep 4678397 = 1754399) B1754399
theorem B6939449 : Blo 1297967 6939449 := bstep (se 2 (by rfl) ⟨2602293, by rfl⟩ : syracuseStep 6939449 = 5204587) B5204587
theorem B81126755 : Blo 1297967 81126755 := bstep (se 1 (by rfl) ⟨60845066, by rfl⟩ : syracuseStep 81126755 = 121690133) B121690133
theorem B9356705 : Blo 1297967 9356705 := bstep (se 2 (by rfl) ⟨3508764, by rfl⟩ : syracuseStep 9356705 = 7017529) B7017529
theorem B4384367 : Blo 1297967 4384367 := bstep (se 1 (by rfl) ⟨3288275, by rfl⟩ : syracuseStep 4384367 = 6576551) B6576551
theorem B4564595 : Blo 1297967 4564595 := bstep (se 1 (by rfl) ⟨3423446, by rfl⟩ : syracuseStep 4564595 = 6846893) B6846893
theorem B4384475 : Blo 1297967 4384475 := bstep (se 1 (by rfl) ⟨3288356, by rfl⟩ : syracuseStep 4384475 = 6576713) B6576713
theorem B28092257 : Blo 1297967 28092257 := bstep (se 2 (by rfl) ⟨10534596, by rfl⟩ : syracuseStep 28092257 = 21069193) B21069193
theorem B21071987 : Blo 1297967 21071987 := bstep (se 1 (by rfl) ⟨15803990, by rfl⟩ : syracuseStep 21071987 = 31607981) B31607981
theorem B6580439 : Blo 1297967 6580439 := bstep (se 1 (by rfl) ⟨4935329, by rfl⟩ : syracuseStep 6580439 = 9870659) B9870659
theorem B24955127 : Blo 1297967 24955127 := bstep (se 1 (by rfl) ⟨18716345, by rfl⟩ : syracuseStep 24955127 = 37432691) B37432691
theorem B2500903 : Blo 1297967 2500903 := bstep (se 1 (by rfl) ⟨1875677, by rfl⟩ : syracuseStep 2500903 = 3751355) B3751355
theorem B4933979 : Blo 1297967 4933979 := bstep (se 1 (by rfl) ⟨3700484, by rfl⟩ : syracuseStep 4933979 = 7400969) B7400969
theorem B7023131 : Blo 1297967 7023131 := bstep (se 1 (by rfl) ⟨5267348, by rfl⟩ : syracuseStep 7023131 = 10534697) B10534697
theorem B6580763 : Blo 1297967 6580763 := bstep (se 1 (by rfl) ⟨4935572, by rfl⟩ : syracuseStep 6580763 = 9871145) B9871145
theorem B1460767 : Blo 1297967 1460767 := bstep (se 1 (by rfl) ⟨1095575, by rfl⟩ : syracuseStep 1460767 = 2191151) B2191151
theorem B22211171 : Blo 1297967 22211171 := bstep (se 1 (by rfl) ⟨16658378, by rfl⟩ : syracuseStep 22211171 = 33316757) B33316757
theorem B18729605 : Blo 1297967 18729605 := bstep (se 4 (by rfl) ⟨1755900, by rfl⟩ : syracuseStep 18729605 = 3511801) B3511801
theorem B1559455 : Blo 1297967 1559455 := bstep (se 1 (by rfl) ⟨1169591, by rfl⟩ : syracuseStep 1559455 = 2339183) B2339183
theorem B4385771 : Blo 1297967 4385771 := bstep (se 1 (by rfl) ⟨3289328, by rfl⟩ : syracuseStep 4385771 = 6578657) B6578657
theorem B4385825 : Blo 1297967 4385825 := bstep (se 2 (by rfl) ⟨1644684, by rfl⟩ : syracuseStep 4385825 = 3289369) B3289369
theorem B13323365 : Blo 1297967 13323365 := bstep (se 4 (by rfl) ⟨1249065, by rfl⟩ : syracuseStep 13323365 = 2498131) B2498131
theorem B3288185 : Blo 1297967 3288185 := bstep (se 2 (by rfl) ⟨1233069, by rfl⟩ : syracuseStep 3288185 = 2466139) B2466139
theorem B3697807 : Blo 1297967 3697807 := bstep (se 1 (by rfl) ⟨2773355, by rfl⟩ : syracuseStep 3697807 = 5546711) B5546711
theorem B28454237 : Blo 1297967 28454237 := bstep (se 3 (by rfl) ⟨5335169, by rfl⟩ : syracuseStep 28454237 = 10670339) B10670339
theorem B18722177 : Blo 1297967 18722177 := bstep (se 2 (by rfl) ⟨7020816, by rfl⟩ : syracuseStep 18722177 = 14041633) B14041633
theorem B11103641 : Blo 1297967 11103641 := bstep (se 2 (by rfl) ⟨4163865, by rfl⟩ : syracuseStep 11103641 = 8327731) B8327731
theorem B2960959 : Blo 1297967 2960959 := bstep (se 1 (by rfl) ⟨2220719, by rfl⟩ : syracuseStep 2960959 = 4441439) B4441439
theorem B29994569 : Blo 1297967 29994569 := bstep (se 2 (by rfl) ⟨11247963, by rfl⟩ : syracuseStep 29994569 = 22495927) B22495927
theorem B1298011 : Blo 1297967 1298011 := bstep (se 1 (by rfl) ⟨973508, by rfl⟩ : syracuseStep 1298011 = 1947017) B1947017
theorem B2190955 : Blo 1297967 2190955 := bstep (se 1 (by rfl) ⟨1643216, by rfl⟩ : syracuseStep 2190955 = 3286433) B3286433
theorem B22507307 : Blo 1297967 22507307 := bstep (se 1 (by rfl) ⟨16880480, by rfl⟩ : syracuseStep 22507307 = 33760961) B33760961
theorem B1298247 : Blo 1297967 1298247 := bstep (se 1 (by rfl) ⟨973685, by rfl⟩ : syracuseStep 1298247 = 1947371) B1947371
theorem B2191225 : Blo 1297967 2191225 := bstep (se 2 (by rfl) ⟨821709, by rfl⟩ : syracuseStep 2191225 = 1643419) B1643419
theorem B2191259 : Blo 1297967 2191259 := bstep (se 1 (by rfl) ⟨1643444, by rfl⟩ : syracuseStep 2191259 = 3286889) B3286889
theorem B1298399 : Blo 1297967 1298399 := bstep (se 1 (by rfl) ⟨973799, by rfl⟩ : syracuseStep 1298399 = 1947599) B1947599
theorem B7901165 : Blo 1297967 7901165 := bstep (se 3 (by rfl) ⟨1481468, by rfl⟩ : syracuseStep 7901165 = 2962937) B2962937
theorem B2920571 : Blo 1297967 2920571 := bstep (se 1 (by rfl) ⟨2190428, by rfl⟩ : syracuseStep 2920571 = 4380857) B4380857
theorem B5927041 : Blo 1297967 5927041 := bstep (se 2 (by rfl) ⟨2222640, by rfl⟩ : syracuseStep 5927041 = 4445281) B4445281
theorem B1298663 : Blo 1297967 1298663 := bstep (se 1 (by rfl) ⟨973997, by rfl⟩ : syracuseStep 1298663 = 1947995) B1947995
theorem B6664457 : Blo 1297967 6664457 := bstep (se 2 (by rfl) ⟨2499171, by rfl⟩ : syracuseStep 6664457 = 4998343) B4998343
theorem B1298815 : Blo 1297967 1298815 := bstep (se 1 (by rfl) ⟨974111, by rfl⟩ : syracuseStep 1298815 = 1948223) B1948223
theorem B2920841 : Blo 1297967 2920841 := bstep (se 2 (by rfl) ⟨1095315, by rfl⟩ : syracuseStep 2920841 = 2190631) B2190631
theorem B3289481 : Blo 1297967 3289481 := bstep (se 2 (by rfl) ⟨1233555, by rfl⟩ : syracuseStep 3289481 = 2467111) B2467111
theorem B1298895 : Blo 1297967 1298895 := bstep (se 1 (by rfl) ⟨974171, by rfl⟩ : syracuseStep 1298895 = 1948343) B1948343
theorem B4387283 : Blo 1297967 4387283 := bstep (se 1 (by rfl) ⟨3290462, by rfl⟩ : syracuseStep 4387283 = 6580925) B6580925
theorem B1299047 : Blo 1297967 1299047 := bstep (se 1 (by rfl) ⟨974285, by rfl⟩ : syracuseStep 1299047 = 1948571) B1948571
theorem B43315897 : Blo 1297967 43315897 := bstep (se 2 (by rfl) ⟨16243461, by rfl⟩ : syracuseStep 43315897 = 32486923) B32486923
theorem B1299311 : Blo 1297967 1299311 := bstep (se 1 (by rfl) ⟨974483, by rfl⟩ : syracuseStep 1299311 = 1948967) B1948967
theorem B1299367 : Blo 1297967 1299367 := bstep (se 1 (by rfl) ⟨974525, by rfl⟩ : syracuseStep 1299367 = 1949051) B1949051
theorem B33739739 : Blo 1297967 33739739 := bstep (se 1 (by rfl) ⟨25304804, by rfl⟩ : syracuseStep 33739739 = 50609609) B50609609
theorem B1299451 : Blo 1297967 1299451 := bstep (se 1 (by rfl) ⟨974588, by rfl⟩ : syracuseStep 1299451 = 1949177) B1949177
theorem B2192447 : Blo 1297967 2192447 := bstep (se 1 (by rfl) ⟨1644335, by rfl⟩ : syracuseStep 2192447 = 3288671) B3288671
theorem B1299519 : Blo 1297967 1299519 := bstep (se 1 (by rfl) ⟨974639, by rfl⟩ : syracuseStep 1299519 = 1949279) B1949279
theorem B9360481 : Blo 1297967 9360481 := bstep (se 2 (by rfl) ⟨3510180, by rfl⟩ : syracuseStep 9360481 = 7020361) B7020361
theorem B1848425 : Blo 1297967 1848425 := bstep (se 2 (by rfl) ⟨693159, by rfl⟩ : syracuseStep 1848425 = 1386319) B1386319
theorem B2921579 : Blo 1297967 2921579 := bstep (se 1 (by rfl) ⟨2191184, by rfl⟩ : syracuseStep 2921579 = 4382369) B4382369
theorem B1299663 : Blo 1297967 1299663 := bstep (se 1 (by rfl) ⟨974747, by rfl⟩ : syracuseStep 1299663 = 1949495) B1949495
theorem B59954417 : Blo 1297967 59954417 := bstep (se 2 (by rfl) ⟨22482906, by rfl⟩ : syracuseStep 59954417 = 44965813) B44965813
theorem B7501043 : Blo 1297967 7501043 := bstep (se 1 (by rfl) ⟨5625782, by rfl⟩ : syracuseStep 7501043 = 11251565) B11251565
theorem B1947035 : Blo 1297967 1947035 := bstep (se 1 (by rfl) ⟨1460276, by rfl⟩ : syracuseStep 1947035 = 2920553) B2920553
theorem B1299867 : Blo 1297967 1299867 := bstep (se 1 (by rfl) ⟨974900, by rfl⟩ : syracuseStep 1299867 = 1949801) B1949801
theorem B2193007 : Blo 1297967 2193007 := bstep (se 1 (by rfl) ⟨1644755, by rfl⟩ : syracuseStep 2193007 = 3289511) B3289511
theorem B1947257 : Blo 1297967 1947257 := bstep (se 2 (by rfl) ⟨730221, by rfl⟩ : syracuseStep 1947257 = 1460443) B1460443
theorem B9369245 : Blo 1297967 9369245 := bstep (se 3 (by rfl) ⟨1756733, by rfl⟩ : syracuseStep 9369245 = 3513467) B3513467
theorem B2922155 : Blo 1297967 2922155 := bstep (se 1 (by rfl) ⟨2191616, by rfl⟩ : syracuseStep 2922155 = 4383233) B4383233
theorem B10680011 : Blo 1297967 10680011 := bstep (se 1 (by rfl) ⟨8010008, by rfl⟩ : syracuseStep 10680011 = 16020017) B16020017
theorem B2193115 : Blo 1297967 2193115 := bstep (se 1 (by rfl) ⟨1644836, by rfl⟩ : syracuseStep 2193115 = 3289673) B3289673
theorem B1947359 : Blo 1297967 1947359 := bstep (se 1 (by rfl) ⟨1460519, by rfl⟩ : syracuseStep 1947359 = 2921039) B2921039
theorem B1947455 : Blo 1297967 1947455 := bstep (se 1 (by rfl) ⟨1460591, by rfl⟩ : syracuseStep 1947455 = 2921183) B2921183
theorem B16635779 : Blo 1297967 16635779 := bstep (se 1 (by rfl) ⟨12476834, by rfl⟩ : syracuseStep 16635779 = 24953669) B24953669
theorem B5552009 : Blo 1297967 5552009 := bstep (se 2 (by rfl) ⟨2082003, by rfl⟩ : syracuseStep 5552009 = 4164007) B4164007
theorem B4929437 : Blo 1297967 4929437 := bstep (se 3 (by rfl) ⟨924269, by rfl⟩ : syracuseStep 4929437 = 1848539) B1848539
theorem B1947623 : Blo 1297967 1947623 := bstep (se 1 (by rfl) ⟨1460717, by rfl⟩ : syracuseStep 1947623 = 2921435) B2921435
theorem B2922479 : Blo 1297967 2922479 := bstep (se 1 (by rfl) ⟨2191859, by rfl⟩ : syracuseStep 2922479 = 4383719) B4383719
theorem B1947641 : Blo 1297967 1947641 := bstep (se 2 (by rfl) ⟨730365, by rfl⟩ : syracuseStep 1947641 = 1460731) B1460731
theorem B15800345 : Blo 1297967 15800345 := bstep (se 2 (by rfl) ⟨5925129, by rfl⟩ : syracuseStep 15800345 = 11850259) B11850259
theorem B4929619 : Blo 1297967 4929619 := bstep (se 1 (by rfl) ⟨3697214, by rfl⟩ : syracuseStep 4929619 = 7394429) B7394429
theorem B1947743 : Blo 1297967 1947743 := bstep (se 1 (by rfl) ⟨1460807, by rfl⟩ : syracuseStep 1947743 = 2921615) B2921615
theorem B1849439 : Blo 1297967 1849439 := bstep (se 1 (by rfl) ⟨1387079, by rfl⟩ : syracuseStep 1849439 = 2774159) B2774159
theorem B1947803 : Blo 1297967 1947803 := bstep (se 1 (by rfl) ⟨1460852, by rfl⟩ : syracuseStep 1947803 = 2921705) B2921705
theorem B1947839 : Blo 1297967 1947839 := bstep (se 1 (by rfl) ⟨1460879, by rfl⟩ : syracuseStep 1947839 = 2921759) B2921759
theorem B10541249 : Blo 1297967 10541249 := bstep (se 2 (by rfl) ⟨3952968, by rfl⟩ : syracuseStep 10541249 = 7905937) B7905937
theorem B2922695 : Blo 1297967 2922695 := bstep (se 1 (by rfl) ⟨2192021, by rfl⟩ : syracuseStep 2922695 = 4384043) B4384043
theorem B1947881 : Blo 1297967 1947881 := bstep (se 2 (by rfl) ⟨730455, by rfl⟩ : syracuseStep 1947881 = 1460911) B1460911
theorem B3701065 : Blo 1297967 3701065 := bstep (se 2 (by rfl) ⟨1387899, by rfl⟩ : syracuseStep 3701065 = 2775799) B2775799
theorem B16021871 : Blo 1297967 16021871 := bstep (se 1 (by rfl) ⟨12016403, by rfl⟩ : syracuseStep 16021871 = 24032807) B24032807
theorem B2922875 : Blo 1297967 2922875 := bstep (se 1 (by rfl) ⟨2192156, by rfl⟩ : syracuseStep 2922875 = 4384313) B4384313
theorem B8321453 : Blo 1297967 8321453 := bstep (se 3 (by rfl) ⟨1560272, by rfl⟩ : syracuseStep 8321453 = 3120545) B3120545
theorem B1948187 : Blo 1297967 1948187 := bstep (se 1 (by rfl) ⟨1461140, by rfl⟩ : syracuseStep 1948187 = 2922281) B2922281
theorem B1849883 : Blo 1297967 1849883 := bstep (se 1 (by rfl) ⟨1387412, by rfl⟩ : syracuseStep 1849883 = 2774825) B2774825
theorem B4930105 : Blo 1297967 4930105 := bstep (se 2 (by rfl) ⟨1848789, by rfl⟩ : syracuseStep 4930105 = 3697579) B3697579
theorem B1948265 : Blo 1297967 1948265 := bstep (se 2 (by rfl) ⟨730599, by rfl⟩ : syracuseStep 1948265 = 1461199) B1461199
theorem B2923145 : Blo 1297967 2923145 := bstep (se 2 (by rfl) ⟨1096179, by rfl⟩ : syracuseStep 2923145 = 2192359) B2192359
theorem B9362267 : Blo 1297967 9362267 := bstep (se 1 (by rfl) ⟨7021700, by rfl⟩ : syracuseStep 9362267 = 14043401) B14043401
theorem B7396343 : Blo 1297967 7396343 := bstep (se 1 (by rfl) ⟨5547257, by rfl⟩ : syracuseStep 7396343 = 11094515) B11094515
theorem B1948793 : Blo 1297967 1948793 := bstep (se 2 (by rfl) ⟨730797, by rfl⟩ : syracuseStep 1948793 = 1461595) B1461595
theorem B2342009 : Blo 1297967 2342009 := bstep (se 2 (by rfl) ⟨878253, by rfl⟩ : syracuseStep 2342009 = 1756507) B1756507
theorem B3120257 : Blo 1297967 3120257 := bstep (se 2 (by rfl) ⟨1170096, by rfl⟩ : syracuseStep 3120257 = 2340193) B2340193
theorem B2923703 : Blo 1297967 2923703 := bstep (se 1 (by rfl) ⟨2192777, by rfl⟩ : syracuseStep 2923703 = 4385555) B4385555
theorem B1948895 : Blo 1297967 1948895 := bstep (se 1 (by rfl) ⟨1461671, by rfl⟩ : syracuseStep 1948895 = 2923343) B2923343
theorem B1948937 : Blo 1297967 1948937 := bstep (se 2 (by rfl) ⟨730851, by rfl⟩ : syracuseStep 1948937 = 1461703) B1461703
theorem B4381991 : Blo 1297967 4381991 := bstep (se 1 (by rfl) ⟨3286493, by rfl⟩ : syracuseStep 4381991 = 6572987) B6572987
theorem B1949039 : Blo 1297967 1949039 := bstep (se 1 (by rfl) ⟨1461779, by rfl⟩ : syracuseStep 1949039 = 2923559) B2923559
theorem B1973735 : Blo 1297967 1973735 := bstep (se 1 (by rfl) ⟨1480301, by rfl⟩ : syracuseStep 1973735 = 2960603) B2960603
theorem B1949159 : Blo 1297967 1949159 := bstep (se 1 (by rfl) ⟨1461869, by rfl⟩ : syracuseStep 1949159 = 2923739) B2923739
theorem B2080247 : Blo 1297967 2080247 := bstep (se 1 (by rfl) ⟨1560185, by rfl⟩ : syracuseStep 2080247 = 3120371) B3120371
theorem B1949291 : Blo 1297967 1949291 := bstep (se 1 (by rfl) ⟨1461968, by rfl⟩ : syracuseStep 1949291 = 2923937) B2923937
theorem B1875631 : Blo 1297967 1875631 := bstep (se 1 (by rfl) ⟨1406723, by rfl⟩ : syracuseStep 1875631 = 2813447) B2813447
theorem B1949417 : Blo 1297967 1949417 := bstep (se 2 (by rfl) ⟨731031, by rfl⟩ : syracuseStep 1949417 = 1462063) B1462063
theorem B2924279 : Blo 1297967 2924279 := bstep (se 1 (by rfl) ⟨2193209, by rfl⟩ : syracuseStep 2924279 = 4386419) B4386419
theorem B1949561 : Blo 1297967 1949561 := bstep (se 2 (by rfl) ⟨731085, by rfl⟩ : syracuseStep 1949561 = 1462171) B1462171
theorem B2924459 : Blo 1297967 2924459 := bstep (se 1 (by rfl) ⟨2193344, by rfl⟩ : syracuseStep 2924459 = 4386689) B4386689
theorem B4161469 : Blo 1297967 4161469 := bstep (se 3 (by rfl) ⟨780275, by rfl⟩ : syracuseStep 4161469 = 1560551) B1560551
theorem B1949663 : Blo 1297967 1949663 := bstep (se 1 (by rfl) ⟨1462247, by rfl⟩ : syracuseStep 1949663 = 2924495) B2924495
theorem B4931837 : Blo 1297967 4931837 := bstep (se 3 (by rfl) ⟨924719, by rfl⟩ : syracuseStep 4931837 = 1849439) B1849439
theorem B2924855 : Blo 1297967 2924855 := bstep (se 1 (by rfl) ⟨2193641, by rfl⟩ : syracuseStep 2924855 = 4387283) B4387283
theorem B3334537 : Blo 1297967 3334537 := bstep (se 2 (by rfl) ⟨1250451, by rfl⟩ : syracuseStep 3334537 = 2500903) B2500903
theorem B39969611 : Blo 1297967 39969611 := bstep (se 1 (by rfl) ⟨29977208, by rfl⟩ : syracuseStep 39969611 = 59954417) B59954417
theorem B54084503 : Blo 1297967 54084503 := bstep (se 1 (by rfl) ⟨40563377, by rfl⟩ : syracuseStep 54084503 = 81126755) B81126755
theorem B57754529 : Blo 1297967 57754529 := bstep (se 2 (by rfl) ⟨21657948, by rfl⟩ : syracuseStep 57754529 = 43315897) B43315897
theorem B7120007 : Blo 1297967 7120007 := bstep (se 1 (by rfl) ⟨5340005, by rfl⟩ : syracuseStep 7120007 = 10680011) B10680011
theorem B18728171 : Blo 1297967 18728171 := bstep (se 1 (by rfl) ⟨14046128, by rfl⟩ : syracuseStep 18728171 = 28092257) B28092257
theorem B3286291 : Blo 1297967 3286291 := bstep (se 1 (by rfl) ⟨2464718, by rfl⟩ : syracuseStep 3286291 = 4929437) B4929437
theorem B4933021 : Blo 1297967 4933021 := bstep (se 3 (by rfl) ⟨924941, by rfl⟩ : syracuseStep 4933021 = 1849883) B1849883
theorem B5547635 : Blo 1297967 5547635 := bstep (se 1 (by rfl) ⟨4160726, by rfl⟩ : syracuseStep 5547635 = 8321453) B8321453
theorem B12486403 : Blo 1297967 12486403 := bstep (se 1 (by rfl) ⟨9364802, by rfl⟩ : syracuseStep 12486403 = 18729605) B18729605
theorem B8882243 : Blo 1297967 8882243 := bstep (se 1 (by rfl) ⟨6661682, by rfl⟩ : syracuseStep 8882243 = 13323365) B13323365
theorem B8317093 : Blo 1297967 8317093 := bstep (se 4 (by rfl) ⟨779727, by rfl⟩ : syracuseStep 8317093 = 1559455) B1559455
theorem B2500841 : Blo 1297967 2500841 := bstep (se 2 (by rfl) ⟨937815, by rfl⟩ : syracuseStep 2500841 = 1875631) B1875631
theorem B5548625 : Blo 1297967 5548625 := bstep (se 2 (by rfl) ⟨2080734, by rfl⟩ : syracuseStep 5548625 = 4161469) B4161469
theorem B1460839 : Blo 1297967 1460839 := bstep (se 1 (by rfl) ⟨1095629, by rfl⟩ : syracuseStep 1460839 = 2191259) B2191259
theorem B6572825 : Blo 1297967 6572825 := bstep (se 2 (by rfl) ⟨2464809, by rfl⟩ : syracuseStep 6572825 = 4929619) B4929619
theorem B4442971 : Blo 1297967 4442971 := bstep (se 1 (by rfl) ⟨3332228, by rfl⟩ : syracuseStep 4442971 = 6664457) B6664457
theorem B9497483 : Blo 1297967 9497483 := bstep (se 1 (by rfl) ⟨7123112, by rfl⟩ : syracuseStep 9497483 = 14246225) B14246225
theorem B25308227 : Blo 1297967 25308227 := bstep (se 1 (by rfl) ⟨18981170, by rfl⟩ : syracuseStep 25308227 = 37962341) B37962341
theorem B2960455 : Blo 1297967 2960455 := bstep (se 1 (by rfl) ⟨2220341, by rfl⟩ : syracuseStep 2960455 = 4440683) B4440683
theorem B4934753 : Blo 1297967 4934753 := bstep (se 2 (by rfl) ⟨1850532, by rfl⟩ : syracuseStep 4934753 = 3701065) B3701065
theorem B1461631 : Blo 1297967 1461631 := bstep (se 1 (by rfl) ⟨1096223, by rfl⟩ : syracuseStep 1461631 = 2192447) B2192447
theorem B6573473 : Blo 1297967 6573473 := bstep (se 2 (by rfl) ⟨2465052, by rfl⟩ : syracuseStep 6573473 = 4930105) B4930105
theorem B1298023 : Blo 1297967 1298023 := bstep (se 1 (by rfl) ⟨973517, by rfl⟩ : syracuseStep 1298023 = 1947035) B1947035
theorem B6237803 : Blo 1297967 6237803 := bstep (se 1 (by rfl) ⟨4678352, by rfl⟩ : syracuseStep 6237803 = 9356705) B9356705
theorem B3043063 : Blo 1297967 3043063 := bstep (se 1 (by rfl) ⟨2282297, by rfl⟩ : syracuseStep 3043063 = 4564595) B4564595
theorem B1298171 : Blo 1297967 1298171 := bstep (se 1 (by rfl) ⟨973628, by rfl⟩ : syracuseStep 1298171 = 1947257) B1947257
theorem B6246163 : Blo 1297967 6246163 := bstep (se 1 (by rfl) ⟨4684622, by rfl⟩ : syracuseStep 6246163 = 9369245) B9369245
theorem B1298239 : Blo 1297967 1298239 := bstep (se 1 (by rfl) ⟨973679, by rfl⟩ : syracuseStep 1298239 = 1947359) B1947359
theorem B1298303 : Blo 1297967 1298303 := bstep (se 1 (by rfl) ⟨973727, by rfl⟩ : syracuseStep 1298303 = 1947455) B1947455
theorem B1298415 : Blo 1297967 1298415 := bstep (se 1 (by rfl) ⟨973811, by rfl⟩ : syracuseStep 1298415 = 1947623) B1947623
theorem B1298427 : Blo 1297967 1298427 := bstep (se 1 (by rfl) ⟨973820, by rfl⟩ : syracuseStep 1298427 = 1947641) B1947641
theorem B1298495 : Blo 1297967 1298495 := bstep (se 1 (by rfl) ⟨973871, by rfl⟩ : syracuseStep 1298495 = 1947743) B1947743
theorem B1298535 : Blo 1297967 1298535 := bstep (se 1 (by rfl) ⟨973901, by rfl⟩ : syracuseStep 1298535 = 1947803) B1947803
theorem B1298559 : Blo 1297967 1298559 := bstep (se 1 (by rfl) ⟨973919, by rfl⟩ : syracuseStep 1298559 = 1947839) B1947839
theorem B12480641 : Blo 1297967 12480641 := bstep (se 2 (by rfl) ⟨4680240, by rfl⟩ : syracuseStep 12480641 = 9360481) B9360481
theorem B4386959 : Blo 1297967 4386959 := bstep (se 1 (by rfl) ⟨3290219, by rfl⟩ : syracuseStep 4386959 = 6580439) B6580439
theorem B1298587 : Blo 1297967 1298587 := bstep (se 1 (by rfl) ⟨973940, by rfl⟩ : syracuseStep 1298587 = 1947881) B1947881
theorem B3289319 : Blo 1297967 3289319 := bstep (se 1 (by rfl) ⟨2466989, by rfl⟩ : syracuseStep 3289319 = 4933979) B4933979
theorem B1298791 : Blo 1297967 1298791 := bstep (se 1 (by rfl) ⟨974093, by rfl⟩ : syracuseStep 1298791 = 1948187) B1948187
theorem B4682087 : Blo 1297967 4682087 := bstep (se 1 (by rfl) ⟨3511565, by rfl⟩ : syracuseStep 4682087 = 7023131) B7023131
theorem B4387175 : Blo 1297967 4387175 := bstep (se 1 (by rfl) ⟨3290381, by rfl⟩ : syracuseStep 4387175 = 6580763) B6580763
theorem B14807447 : Blo 1297967 14807447 := bstep (se 1 (by rfl) ⟨11105585, by rfl⟩ : syracuseStep 14807447 = 22211171) B22211171
theorem B1298843 : Blo 1297967 1298843 := bstep (se 1 (by rfl) ⟨974132, by rfl⟩ : syracuseStep 1298843 = 1948265) B1948265
theorem B2192123 : Blo 1297967 2192123 := bstep (se 1 (by rfl) ⟨1644092, by rfl⟩ : syracuseStep 2192123 = 3288185) B3288185
theorem B1299195 : Blo 1297967 1299195 := bstep (se 1 (by rfl) ⟨974396, by rfl⟩ : syracuseStep 1299195 = 1948793) B1948793
theorem B1561339 : Blo 1297967 1561339 := bstep (se 1 (by rfl) ⟨1171004, by rfl⟩ : syracuseStep 1561339 = 2342009) B2342009
theorem B2921273 : Blo 1297967 2921273 := bstep (se 2 (by rfl) ⟨1095477, by rfl⟩ : syracuseStep 2921273 = 2190955) B2190955
theorem B1299263 : Blo 1297967 1299263 := bstep (se 1 (by rfl) ⟨974447, by rfl⟩ : syracuseStep 1299263 = 1948895) B1948895
theorem B1299291 : Blo 1297967 1299291 := bstep (se 1 (by rfl) ⟨974468, by rfl⟩ : syracuseStep 1299291 = 1948937) B1948937
theorem B2921327 : Blo 1297967 2921327 := bstep (se 1 (by rfl) ⟨2190995, by rfl⟩ : syracuseStep 2921327 = 4381991) B4381991
theorem B18969491 : Blo 1297967 18969491 := bstep (se 1 (by rfl) ⟨14227118, by rfl⟩ : syracuseStep 18969491 = 28454237) B28454237
theorem B1299359 : Blo 1297967 1299359 := bstep (se 1 (by rfl) ⟨974519, by rfl⟩ : syracuseStep 1299359 = 1949039) B1949039
theorem B12481451 : Blo 1297967 12481451 := bstep (se 1 (by rfl) ⟨9361088, by rfl⟩ : syracuseStep 12481451 = 18722177) B18722177
theorem B7402427 : Blo 1297967 7402427 := bstep (se 1 (by rfl) ⟨5551820, by rfl⟩ : syracuseStep 7402427 = 11103641) B11103641
theorem B1315823 : Blo 1297967 1315823 := bstep (se 1 (by rfl) ⟨986867, by rfl⟩ : syracuseStep 1315823 = 1973735) B1973735
theorem B1299439 : Blo 1297967 1299439 := bstep (se 1 (by rfl) ⟨974579, by rfl⟩ : syracuseStep 1299439 = 1949159) B1949159
theorem B1299527 : Blo 1297967 1299527 := bstep (se 1 (by rfl) ⟨974645, by rfl⟩ : syracuseStep 1299527 = 1949291) B1949291
theorem B1299611 : Blo 1297967 1299611 := bstep (se 1 (by rfl) ⟨974708, by rfl⟩ : syracuseStep 1299611 = 1949417) B1949417
theorem B2921633 : Blo 1297967 2921633 := bstep (se 2 (by rfl) ⟨1095612, by rfl⟩ : syracuseStep 2921633 = 2191225) B2191225
theorem B15004871 : Blo 1297967 15004871 := bstep (se 1 (by rfl) ⟨11253653, by rfl⟩ : syracuseStep 15004871 = 22507307) B22507307
theorem B22189301 : Blo 1297967 22189301 := bstep (se 5 (by rfl) ⟨1040123, by rfl⟩ : syracuseStep 22189301 = 2080247) B2080247
theorem B1299707 : Blo 1297967 1299707 := bstep (se 1 (by rfl) ⟨974780, by rfl⟩ : syracuseStep 1299707 = 1949561) B1949561
theorem B1299775 : Blo 1297967 1299775 := bstep (se 1 (by rfl) ⟨974831, by rfl⟩ : syracuseStep 1299775 = 1949663) B1949663
theorem B1947047 : Blo 1297967 1947047 := bstep (se 1 (by rfl) ⟨1460285, by rfl⟩ : syracuseStep 1947047 = 2920571) B2920571
theorem B2921903 : Blo 1297967 2921903 := bstep (se 1 (by rfl) ⟨2191427, by rfl⟩ : syracuseStep 2921903 = 4382855) B4382855
theorem B1299943 : Blo 1297967 1299943 := bstep (se 1 (by rfl) ⟨974957, by rfl⟩ : syracuseStep 1299943 = 1949915) B1949915
theorem B1299951 : Blo 1297967 1299951 := bstep (se 1 (by rfl) ⟨974963, by rfl⟩ : syracuseStep 1299951 = 1949927) B1949927
theorem B7902721 : Blo 1297967 7902721 := bstep (se 2 (by rfl) ⟨2963520, by rfl⟩ : syracuseStep 7902721 = 5927041) B5927041
theorem B1947227 : Blo 1297967 1947227 := bstep (se 1 (by rfl) ⟨1460420, by rfl⟩ : syracuseStep 1947227 = 2920841) B2920841
theorem B2192987 : Blo 1297967 2192987 := bstep (se 1 (by rfl) ⟨1644740, by rfl⟩ : syracuseStep 2192987 = 3289481) B3289481
theorem B4929133 : Blo 1297967 4929133 := bstep (se 3 (by rfl) ⟨924212, by rfl⟩ : syracuseStep 4929133 = 1848425) B1848425
theorem B10000043 : Blo 1297967 10000043 := bstep (se 1 (by rfl) ⟨7500032, by rfl⟩ : syracuseStep 10000043 = 15000065) B15000065
theorem B86562553 : Blo 1297967 86562553 := bstep (se 2 (by rfl) ⟨32460957, by rfl⟩ : syracuseStep 86562553 = 64921915) B64921915
theorem B6575903 : Blo 1297967 6575903 := bstep (se 1 (by rfl) ⟨4931927, by rfl⟩ : syracuseStep 6575903 = 9863855) B9863855
theorem B14047033 : Blo 1297967 14047033 := bstep (se 2 (by rfl) ⟨5267637, by rfl⟩ : syracuseStep 14047033 = 10535275) B10535275
theorem B3118931 : Blo 1297967 3118931 := bstep (se 1 (by rfl) ⟨2339198, by rfl⟩ : syracuseStep 3118931 = 4678397) B4678397
theorem B4626299 : Blo 1297967 4626299 := bstep (se 1 (by rfl) ⟨3469724, by rfl⟩ : syracuseStep 4626299 = 6939449) B6939449
theorem B20002781 : Blo 1297967 20002781 := bstep (se 3 (by rfl) ⟨3750521, by rfl⟩ : syracuseStep 20002781 = 7501043) B7501043
theorem B4380641 : Blo 1297967 4380641 := bstep (se 2 (by rfl) ⟨1642740, by rfl⟩ : syracuseStep 4380641 = 3285481) B3285481
theorem B22493159 : Blo 1297967 22493159 := bstep (se 1 (by rfl) ⟨16869869, by rfl⟩ : syracuseStep 22493159 = 33739739) B33739739
theorem B1947689 : Blo 1297967 1947689 := bstep (se 2 (by rfl) ⟨730383, by rfl⟩ : syracuseStep 1947689 = 1460767) B1460767
theorem B1947719 : Blo 1297967 1947719 := bstep (se 1 (by rfl) ⟨1460789, by rfl⟩ : syracuseStep 1947719 = 2921579) B2921579
theorem B2922911 : Blo 1297967 2922911 := bstep (se 1 (by rfl) ⟨2192183, by rfl⟩ : syracuseStep 2922911 = 4384367) B4384367
theorem B1948103 : Blo 1297967 1948103 := bstep (se 1 (by rfl) ⟨1461077, by rfl⟩ : syracuseStep 1948103 = 2922155) B2922155
theorem B2922983 : Blo 1297967 2922983 := bstep (se 1 (by rfl) ⟨2192237, by rfl⟩ : syracuseStep 2922983 = 4384475) B4384475
theorem B11090519 : Blo 1297967 11090519 := bstep (se 1 (by rfl) ⟨8317889, by rfl⟩ : syracuseStep 11090519 = 16635779) B16635779
theorem B3701339 : Blo 1297967 3701339 := bstep (se 1 (by rfl) ⟨2776004, by rfl⟩ : syracuseStep 3701339 = 5552009) B5552009
theorem B1948319 : Blo 1297967 1948319 := bstep (se 1 (by rfl) ⟨1461239, by rfl⟩ : syracuseStep 1948319 = 2922479) B2922479
theorem B10533563 : Blo 1297967 10533563 := bstep (se 1 (by rfl) ⟨7900172, by rfl⟩ : syracuseStep 10533563 = 15800345) B15800345
theorem B14047991 : Blo 1297967 14047991 := bstep (se 1 (by rfl) ⟨10535993, by rfl⟩ : syracuseStep 14047991 = 21071987) B21071987
theorem B7027499 : Blo 1297967 7027499 := bstep (se 1 (by rfl) ⟨5270624, by rfl⟩ : syracuseStep 7027499 = 10541249) B10541249
theorem B1948463 : Blo 1297967 1948463 := bstep (se 1 (by rfl) ⟨1461347, by rfl⟩ : syracuseStep 1948463 = 2922695) B2922695
theorem B16636751 : Blo 1297967 16636751 := bstep (se 1 (by rfl) ⟨12477563, by rfl⟩ : syracuseStep 16636751 = 24955127) B24955127
theorem B4930409 : Blo 1297967 4930409 := bstep (se 2 (by rfl) ⟨1848903, by rfl⟩ : syracuseStep 4930409 = 3697807) B3697807
theorem B10681247 : Blo 1297967 10681247 := bstep (se 1 (by rfl) ⟨8010935, by rfl⟩ : syracuseStep 10681247 = 16021871) B16021871
theorem B1948583 : Blo 1297967 1948583 := bstep (se 1 (by rfl) ⟨1461437, by rfl⟩ : syracuseStep 1948583 = 2922875) B2922875
theorem B1948763 : Blo 1297967 1948763 := bstep (se 1 (by rfl) ⟨1461572, by rfl⟩ : syracuseStep 1948763 = 2923145) B2923145
theorem B6241511 : Blo 1297967 6241511 := bstep (se 1 (by rfl) ⟨4681133, by rfl⟩ : syracuseStep 6241511 = 9362267) B9362267
theorem B2923847 : Blo 1297967 2923847 := bstep (se 1 (by rfl) ⟨2192885, by rfl⟩ : syracuseStep 2923847 = 4385771) B4385771
theorem B4930895 : Blo 1297967 4930895 := bstep (se 1 (by rfl) ⟨3698171, by rfl⟩ : syracuseStep 4930895 = 7396343) B7396343
theorem B2923883 : Blo 1297967 2923883 := bstep (se 1 (by rfl) ⟨2192912, by rfl⟩ : syracuseStep 2923883 = 4385825) B4385825
theorem B3947945 : Blo 1297967 3947945 := bstep (se 2 (by rfl) ⟨1480479, by rfl⟩ : syracuseStep 3947945 = 2960959) B2960959
theorem B2080171 : Blo 1297967 2080171 := bstep (se 1 (by rfl) ⟨1560128, by rfl⟩ : syracuseStep 2080171 = 3120257) B3120257
theorem B1949135 : Blo 1297967 1949135 := bstep (se 1 (by rfl) ⟨1461851, by rfl⟩ : syracuseStep 1949135 = 2923703) B2923703
theorem B2924009 : Blo 1297967 2924009 := bstep (se 2 (by rfl) ⟨1096503, by rfl⟩ : syracuseStep 2924009 = 2193007) B2193007
theorem B2924153 : Blo 1297967 2924153 := bstep (se 2 (by rfl) ⟨1096557, by rfl⟩ : syracuseStep 2924153 = 2193115) B2193115
theorem B19996379 : Blo 1297967 19996379 := bstep (se 1 (by rfl) ⟨14997284, by rfl⟩ : syracuseStep 19996379 = 29994569) B29994569
theorem B1949519 : Blo 1297967 1949519 := bstep (se 1 (by rfl) ⟨1462139, by rfl⟩ : syracuseStep 1949519 = 2924279) B2924279
theorem B1949639 : Blo 1297967 1949639 := bstep (se 1 (by rfl) ⟨1462229, by rfl⟩ : syracuseStep 1949639 = 2924459) B2924459
theorem B5267443 : Blo 1297967 5267443 := bstep (se 1 (by rfl) ⟨3950582, by rfl⟩ : syracuseStep 5267443 = 7901165) B7901165
theorem B2924639 : Blo 1297967 2924639 := bstep (se 1 (by rfl) ⟨2193479, by rfl⟩ : syracuseStep 2924639 = 4386959) B4386959
theorem B1949903 : Blo 1297967 1949903 := bstep (se 1 (by rfl) ⟨1462427, by rfl⟩ : syracuseStep 1949903 = 2924855) B2924855
theorem B3121391 : Blo 1297967 3121391 := bstep (se 1 (by rfl) ⟨2341043, by rfl⟩ : syracuseStep 3121391 = 4682087) B4682087
theorem B2924783 : Blo 1297967 2924783 := bstep (se 1 (by rfl) ⟨2193587, by rfl⟩ : syracuseStep 2924783 = 4387175) B4387175
theorem B9871631 : Blo 1297967 9871631 := bstep (se 1 (by rfl) ⟨7403723, by rfl⟩ : syracuseStep 9871631 = 14807447) B14807447
theorem B38503019 : Blo 1297967 38503019 := bstep (se 1 (by rfl) ⟨28877264, by rfl⟩ : syracuseStep 38503019 = 57754529) B57754529
theorem B10003247 : Blo 1297967 10003247 := bstep (se 1 (by rfl) ⟨7502435, by rfl⟩ : syracuseStep 10003247 = 15004871) B15004871
theorem B12485447 : Blo 1297967 12485447 := bstep (se 1 (by rfl) ⟨9364085, by rfl⟩ : syracuseStep 12485447 = 18728171) B18728171
theorem B2081785 : Blo 1297967 2081785 := bstep (se 2 (by rfl) ⟨780669, by rfl⟩ : syracuseStep 2081785 = 1561339) B1561339
theorem B10527853 : Blo 1297967 10527853 := bstep (se 3 (by rfl) ⟨1973972, by rfl⟩ : syracuseStep 10527853 = 3947945) B3947945
theorem B5923961 : Blo 1297967 5923961 := bstep (se 2 (by rfl) ⟨2221485, by rfl⟩ : syracuseStep 5923961 = 4442971) B4442971
theorem B4383935 : Blo 1297967 4383935 := bstep (se 1 (by rfl) ⟨3287951, by rfl⟩ : syracuseStep 4383935 = 6575903) B6575903
theorem B2467559 : Blo 1297967 2467559 := bstep (se 1 (by rfl) ⟨1850669, by rfl⟩ : syracuseStep 2467559 = 3701339) B3701339
theorem B7022375 : Blo 1297967 7022375 := bstep (se 1 (by rfl) ⟨5266781, by rfl⟩ : syracuseStep 7022375 = 10533563) B10533563
theorem B9365327 : Blo 1297967 9365327 := bstep (se 1 (by rfl) ⟨7023995, by rfl⟩ : syracuseStep 9365327 = 14047991) B14047991
theorem B3286939 : Blo 1297967 3286939 := bstep (se 1 (by rfl) ⟨2465204, by rfl⟩ : syracuseStep 3286939 = 4930409) B4930409
theorem B7120831 : Blo 1297967 7120831 := bstep (se 1 (by rfl) ⟨5340623, by rfl⟩ : syracuseStep 7120831 = 10681247) B10681247
theorem B10536961 : Blo 1297967 10536961 := bstep (se 2 (by rfl) ⟨3951360, by rfl⟩ : syracuseStep 10536961 = 7902721) B7902721
theorem B6572177 : Blo 1297967 6572177 := bstep (se 2 (by rfl) ⟨2464566, by rfl⟩ : syracuseStep 6572177 = 4929133) B4929133
theorem B3287263 : Blo 1297967 3287263 := bstep (se 1 (by rfl) ⟨2465447, by rfl⟩ : syracuseStep 3287263 = 4930895) B4930895
theorem B4057417 : Blo 1297967 4057417 := bstep (se 2 (by rfl) ⟨1521531, by rfl⟩ : syracuseStep 4057417 = 3043063) B3043063
theorem B16648537 : Blo 1297967 16648537 := bstep (se 2 (by rfl) ⟨6243201, by rfl⟩ : syracuseStep 16648537 = 12486403) B12486403
theorem B18729377 : Blo 1297967 18729377 := bstep (se 2 (by rfl) ⟨7023516, by rfl⟩ : syracuseStep 18729377 = 14047033) B14047033
theorem B13330919 : Blo 1297967 13330919 := bstep (se 1 (by rfl) ⟨9998189, by rfl⟩ : syracuseStep 13330919 = 19996379) B19996379
theorem B3508861 : Blo 1297967 3508861 := bstep (se 3 (by rfl) ⟨657911, by rfl⟩ : syracuseStep 3508861 = 1315823) B1315823
theorem B7023257 : Blo 1297967 7023257 := bstep (se 2 (by rfl) ⟨2633721, by rfl⟩ : syracuseStep 7023257 = 5267443) B5267443
theorem B3287891 : Blo 1297967 3287891 := bstep (se 1 (by rfl) ⟨2465918, by rfl⟩ : syracuseStep 3287891 = 4931837) B4931837
theorem B1461415 : Blo 1297967 1461415 := bstep (se 1 (by rfl) ⟨1096061, by rfl⟩ : syracuseStep 1461415 = 2192123) B2192123
theorem B36056335 : Blo 1297967 36056335 := bstep (se 1 (by rfl) ⟨27042251, by rfl⟩ : syracuseStep 36056335 = 54084503) B54084503
theorem B4934951 : Blo 1297967 4934951 := bstep (se 1 (by rfl) ⟨3701213, by rfl⟩ : syracuseStep 4934951 = 7402427) B7402427
theorem B4746671 : Blo 1297967 4746671 := bstep (se 1 (by rfl) ⟨3560003, by rfl⟩ : syracuseStep 4746671 = 7120007) B7120007
theorem B1298031 : Blo 1297967 1298031 := bstep (se 1 (by rfl) ⟨973523, by rfl⟩ : syracuseStep 1298031 = 1947047) B1947047
theorem B1298151 : Blo 1297967 1298151 := bstep (se 1 (by rfl) ⟨973613, by rfl⟩ : syracuseStep 1298151 = 1947227) B1947227
theorem B1461991 : Blo 1297967 1461991 := bstep (se 1 (by rfl) ⟨1096493, by rfl⟩ : syracuseStep 1461991 = 2192987) B2192987
theorem B3698423 : Blo 1297967 3698423 := bstep (se 1 (by rfl) ⟨2773817, by rfl⟩ : syracuseStep 3698423 = 5547635) B5547635
theorem B3084199 : Blo 1297967 3084199 := bstep (se 1 (by rfl) ⟨2313149, by rfl⟩ : syracuseStep 3084199 = 4626299) B4626299
theorem B2920427 : Blo 1297967 2920427 := bstep (se 1 (by rfl) ⟨2190320, by rfl⟩ : syracuseStep 2920427 = 4380641) B4380641
theorem B14995439 : Blo 1297967 14995439 := bstep (se 1 (by rfl) ⟨11246579, by rfl⟩ : syracuseStep 14995439 = 22493159) B22493159
theorem B1298459 : Blo 1297967 1298459 := bstep (se 1 (by rfl) ⟨973844, by rfl⟩ : syracuseStep 1298459 = 1947689) B1947689
theorem B1298479 : Blo 1297967 1298479 := bstep (se 1 (by rfl) ⟨973859, by rfl⟩ : syracuseStep 1298479 = 1947719) B1947719
theorem B1667227 : Blo 1297967 1667227 := bstep (se 1 (by rfl) ⟨1250420, by rfl⟩ : syracuseStep 1667227 = 2500841) B2500841
theorem B1298735 : Blo 1297967 1298735 := bstep (se 1 (by rfl) ⟨974051, by rfl⟩ : syracuseStep 1298735 = 1948103) B1948103
theorem B3699083 : Blo 1297967 3699083 := bstep (se 1 (by rfl) ⟨2774312, by rfl⟩ : syracuseStep 3699083 = 5548625) B5548625
theorem B7393679 : Blo 1297967 7393679 := bstep (se 1 (by rfl) ⟨5545259, by rfl⟩ : syracuseStep 7393679 = 11090519) B11090519
theorem B1298879 : Blo 1297967 1298879 := bstep (se 1 (by rfl) ⟨974159, by rfl⟩ : syracuseStep 1298879 = 1948319) B1948319
theorem B1298975 : Blo 1297967 1298975 := bstep (se 1 (by rfl) ⟨974231, by rfl⟩ : syracuseStep 1298975 = 1948463) B1948463
theorem B2773561 : Blo 1297967 2773561 := bstep (se 2 (by rfl) ⟨1040085, by rfl⟩ : syracuseStep 2773561 = 2080171) B2080171
theorem B1299055 : Blo 1297967 1299055 := bstep (se 1 (by rfl) ⟨974291, by rfl⟩ : syracuseStep 1299055 = 1948583) B1948583
theorem B16872151 : Blo 1297967 16872151 := bstep (se 1 (by rfl) ⟨12654113, by rfl⟩ : syracuseStep 16872151 = 25308227) B25308227
theorem B1299175 : Blo 1297967 1299175 := bstep (se 1 (by rfl) ⟨974381, by rfl⟩ : syracuseStep 1299175 = 1948763) B1948763
theorem B3289835 : Blo 1297967 3289835 := bstep (se 1 (by rfl) ⟨2467376, by rfl⟩ : syracuseStep 3289835 = 4934753) B4934753
theorem B1299423 : Blo 1297967 1299423 := bstep (se 1 (by rfl) ⟨974567, by rfl⟩ : syracuseStep 1299423 = 1949135) B1949135
theorem B8328217 : Blo 1297967 8328217 := bstep (se 2 (by rfl) ⟨3123081, by rfl⟩ : syracuseStep 8328217 = 6246163) B6246163
theorem B4158535 : Blo 1297967 4158535 := bstep (se 1 (by rfl) ⟨3118901, by rfl⟩ : syracuseStep 4158535 = 6237803) B6237803
theorem B1299679 : Blo 1297967 1299679 := bstep (se 1 (by rfl) ⟨974759, by rfl⟩ : syracuseStep 1299679 = 1949519) B1949519
theorem B1299759 : Blo 1297967 1299759 := bstep (se 1 (by rfl) ⟨974819, by rfl⟩ : syracuseStep 1299759 = 1949639) B1949639
theorem B8320427 : Blo 1297967 8320427 := bstep (se 1 (by rfl) ⟨6240320, by rfl⟩ : syracuseStep 8320427 = 12480641) B12480641
theorem B2192879 : Blo 1297967 2192879 := bstep (se 1 (by rfl) ⟨1644659, by rfl⟩ : syracuseStep 2192879 = 3289319) B3289319
theorem B11089457 : Blo 1297967 11089457 := bstep (se 2 (by rfl) ⟨4158546, by rfl⟩ : syracuseStep 11089457 = 8317093) B8317093
theorem B4446049 : Blo 1297967 4446049 := bstep (se 2 (by rfl) ⟨1667268, by rfl⟩ : syracuseStep 4446049 = 3334537) B3334537
theorem B1947515 : Blo 1297967 1947515 := bstep (se 1 (by rfl) ⟨1460636, by rfl⟩ : syracuseStep 1947515 = 2921273) B2921273
theorem B26646407 : Blo 1297967 26646407 := bstep (se 1 (by rfl) ⟨19984805, by rfl⟩ : syracuseStep 26646407 = 39969611) B39969611
theorem B1947551 : Blo 1297967 1947551 := bstep (se 1 (by rfl) ⟨1460663, by rfl⟩ : syracuseStep 1947551 = 2921327) B2921327
theorem B8320967 : Blo 1297967 8320967 := bstep (se 1 (by rfl) ⟨6240725, by rfl⟩ : syracuseStep 8320967 = 12481451) B12481451
theorem B1947755 : Blo 1297967 1947755 := bstep (se 1 (by rfl) ⟨1460816, by rfl⟩ : syracuseStep 1947755 = 2921633) B2921633
theorem B1947785 : Blo 1297967 1947785 := bstep (se 2 (by rfl) ⟨730419, by rfl⟩ : syracuseStep 1947785 = 1460839) B1460839
theorem B14792867 : Blo 1297967 14792867 := bstep (se 1 (by rfl) ⟨11094650, by rfl⟩ : syracuseStep 14792867 = 22189301) B22189301
theorem B1947935 : Blo 1297967 1947935 := bstep (se 1 (by rfl) ⟨1460951, by rfl⟩ : syracuseStep 1947935 = 2921903) B2921903
theorem B6666695 : Blo 1297967 6666695 := bstep (se 1 (by rfl) ⟨5000021, by rfl⟩ : syracuseStep 6666695 = 10000043) B10000043
theorem B2079287 : Blo 1297967 2079287 := bstep (se 1 (by rfl) ⟨1559465, by rfl⟩ : syracuseStep 2079287 = 3118931) B3118931
theorem B13335187 : Blo 1297967 13335187 := bstep (se 1 (by rfl) ⟨10001390, by rfl⟩ : syracuseStep 13335187 = 20002781) B20002781
theorem B5921495 : Blo 1297967 5921495 := bstep (se 1 (by rfl) ⟨4441121, by rfl⟩ : syracuseStep 5921495 = 8882243) B8882243
theorem B3947273 : Blo 1297967 3947273 := bstep (se 2 (by rfl) ⟨1480227, by rfl⟩ : syracuseStep 3947273 = 2960455) B2960455
theorem B1948607 : Blo 1297967 1948607 := bstep (se 1 (by rfl) ⟨1461455, by rfl⟩ : syracuseStep 1948607 = 2922911) B2922911
theorem B1948655 : Blo 1297967 1948655 := bstep (se 1 (by rfl) ⟨1461491, by rfl⟩ : syracuseStep 1948655 = 2922983) B2922983
theorem B4381721 : Blo 1297967 4381721 := bstep (se 2 (by rfl) ⟨1643145, by rfl⟩ : syracuseStep 4381721 = 3286291) B3286291
theorem B1948841 : Blo 1297967 1948841 := bstep (se 2 (by rfl) ⟨730815, by rfl⟩ : syracuseStep 1948841 = 1461631) B1461631
theorem B4381883 : Blo 1297967 4381883 := bstep (se 1 (by rfl) ⟨3286412, by rfl⟩ : syracuseStep 4381883 = 6572825) B6572825
theorem B4684999 : Blo 1297967 4684999 := bstep (se 1 (by rfl) ⟨3513749, by rfl⟩ : syracuseStep 4684999 = 7027499) B7027499
theorem B6577361 : Blo 1297967 6577361 := bstep (se 2 (by rfl) ⟨2466510, by rfl⟩ : syracuseStep 6577361 = 4933021) B4933021
theorem B11091167 : Blo 1297967 11091167 := bstep (se 1 (by rfl) ⟨8318375, by rfl⟩ : syracuseStep 11091167 = 16636751) B16636751
theorem B6331655 : Blo 1297967 6331655 := bstep (se 1 (by rfl) ⟨4748741, by rfl⟩ : syracuseStep 6331655 = 9497483) B9497483
theorem B4161007 : Blo 1297967 4161007 := bstep (se 1 (by rfl) ⟨3120755, by rfl⟩ : syracuseStep 4161007 = 6241511) B6241511
theorem B1949231 : Blo 1297967 1949231 := bstep (se 1 (by rfl) ⟨1461923, by rfl⟩ : syracuseStep 1949231 = 2923847) B2923847
theorem B1949255 : Blo 1297967 1949255 := bstep (se 1 (by rfl) ⟨1461941, by rfl⟩ : syracuseStep 1949255 = 2923883) B2923883
theorem B4382315 : Blo 1297967 4382315 := bstep (se 1 (by rfl) ⟨3286736, by rfl⟩ : syracuseStep 4382315 = 6573473) B6573473
theorem B1949339 : Blo 1297967 1949339 := bstep (se 1 (by rfl) ⟨1462004, by rfl⟩ : syracuseStep 1949339 = 2924009) B2924009
theorem B115416737 : Blo 1297967 115416737 := bstep (se 2 (by rfl) ⟨43281276, by rfl⟩ : syracuseStep 115416737 = 86562553) B86562553
theorem B50585309 : Blo 1297967 50585309 := bstep (se 3 (by rfl) ⟨9484745, by rfl⟩ : syracuseStep 50585309 = 18969491) B18969491
theorem B1949435 : Blo 1297967 1949435 := bstep (se 1 (by rfl) ⟨1462076, by rfl⟩ : syracuseStep 1949435 = 2924153) B2924153
theorem B14049281 : Blo 1297967 14049281 := bstep (se 2 (by rfl) ⟨5268480, by rfl⟩ : syracuseStep 14049281 = 10536961) B10536961
theorem B1949759 : Blo 1297967 1949759 := bstep (se 1 (by rfl) ⟨1462319, by rfl⟩ : syracuseStep 1949759 = 2924639) B2924639
theorem B2080927 : Blo 1297967 2080927 := bstep (se 1 (by rfl) ⟨1560695, by rfl⟩ : syracuseStep 2080927 = 3121391) B3121391
theorem B1949855 : Blo 1297967 1949855 := bstep (se 1 (by rfl) ⟨1462391, by rfl⟩ : syracuseStep 1949855 = 2924783) B2924783
theorem B2466055 : Blo 1297967 2466055 := bstep (se 1 (by rfl) ⟨1849541, by rfl⟩ : syracuseStep 2466055 = 3699083) B3699083
theorem B4383017 : Blo 1297967 4383017 := bstep (se 2 (by rfl) ⟨1643631, by rfl⟩ : syracuseStep 4383017 = 3287263) B3287263
theorem B6668831 : Blo 1297967 6668831 := bstep (se 1 (by rfl) ⟨5001623, by rfl⟩ : syracuseStep 6668831 = 10003247) B10003247
theorem B8323631 : Blo 1297967 8323631 := bstep (se 1 (by rfl) ⟨6242723, by rfl⟩ : syracuseStep 8323631 = 12485447) B12485447
theorem B3949307 : Blo 1297967 3949307 := bstep (se 1 (by rfl) ⟨2961980, by rfl⟩ : syracuseStep 3949307 = 5923961) B5923961
theorem B4678481 : Blo 1297967 4678481 := bstep (se 2 (by rfl) ⟨1754430, by rfl⟩ : syracuseStep 4678481 = 3508861) B3508861
theorem B5546951 : Blo 1297967 5546951 := bstep (se 1 (by rfl) ⟨4160213, by rfl⟩ : syracuseStep 5546951 = 8320427) B8320427
theorem B22496201 : Blo 1297967 22496201 := bstep (se 2 (by rfl) ⟨8436075, by rfl⟩ : syracuseStep 22496201 = 16872151) B16872151
theorem B6243551 : Blo 1297967 6243551 := bstep (se 1 (by rfl) ⟨4682663, by rfl⟩ : syracuseStep 6243551 = 9365327) B9365327
theorem B5547311 : Blo 1297967 5547311 := bstep (se 1 (by rfl) ⟨4160483, by rfl⟩ : syracuseStep 5547311 = 8320967) B8320967
theorem B12486251 : Blo 1297967 12486251 := bstep (se 1 (by rfl) ⟨9364688, by rfl⟩ : syracuseStep 12486251 = 18729377) B18729377
theorem B1386191 : Blo 1297967 1386191 := bstep (se 1 (by rfl) ⟨1039643, by rfl⟩ : syracuseStep 1386191 = 2079287) B2079287
theorem B5548009 : Blo 1297967 5548009 := bstep (se 2 (by rfl) ⟨2080503, by rfl⟩ : syracuseStep 5548009 = 4161007) B4161007
theorem B4384907 : Blo 1297967 4384907 := bstep (se 1 (by rfl) ⟨3288680, by rfl⟩ : syracuseStep 4384907 = 6577361) B6577361
theorem B4221103 : Blo 1297967 4221103 := bstep (se 1 (by rfl) ⟨3165827, by rfl⟩ : syracuseStep 4221103 = 6331655) B6331655
theorem B3164447 : Blo 1297967 3164447 := bstep (se 1 (by rfl) ⟨2373335, by rfl⟩ : syracuseStep 3164447 = 4746671) B4746671
theorem B9996959 : Blo 1297967 9996959 := bstep (se 1 (by rfl) ⟨7497719, by rfl⟩ : syracuseStep 9996959 = 14995439) B14995439
theorem B6581087 : Blo 1297967 6581087 := bstep (se 1 (by rfl) ⟨4935815, by rfl⟩ : syracuseStep 6581087 = 9871631) B9871631
theorem B2222969 : Blo 1297967 2222969 := bstep (se 2 (by rfl) ⟨833613, by rfl⟩ : syracuseStep 2222969 = 1667227) B1667227
theorem B25668679 : Blo 1297967 25668679 := bstep (se 1 (by rfl) ⟨19251509, by rfl⟩ : syracuseStep 25668679 = 38503019) B38503019
theorem B3698081 : Blo 1297967 3698081 := bstep (se 2 (by rfl) ⟨1386780, by rfl⟩ : syracuseStep 3698081 = 2773561) B2773561
theorem B17780249 : Blo 1297967 17780249 := bstep (se 2 (by rfl) ⟨6667593, by rfl⟩ : syracuseStep 17780249 = 13335187) B13335187
theorem B1461919 : Blo 1297967 1461919 := bstep (se 1 (by rfl) ⟨1096439, by rfl⟩ : syracuseStep 1461919 = 2192879) B2192879
theorem B7392971 : Blo 1297967 7392971 := bstep (se 1 (by rfl) ⟨5544728, by rfl⟩ : syracuseStep 7392971 = 11089457) B11089457
theorem B4681583 : Blo 1297967 4681583 := bstep (se 1 (by rfl) ⟨3511187, by rfl⟩ : syracuseStep 4681583 = 7022375) B7022375
theorem B1298343 : Blo 1297967 1298343 := bstep (se 1 (by rfl) ⟨973757, by rfl⟩ : syracuseStep 1298343 = 1947515) B1947515
theorem B17764271 : Blo 1297967 17764271 := bstep (se 1 (by rfl) ⟨13323203, by rfl⟩ : syracuseStep 17764271 = 26646407) B26646407
theorem B35549117 : Blo 1297967 35549117 := bstep (se 3 (by rfl) ⟨6665459, by rfl⟩ : syracuseStep 35549117 = 13330919) B13330919
theorem B1298367 : Blo 1297967 1298367 := bstep (se 1 (by rfl) ⟨973775, by rfl⟩ : syracuseStep 1298367 = 1947551) B1947551
theorem B11104289 : Blo 1297967 11104289 := bstep (se 2 (by rfl) ⟨4164108, by rfl⟩ : syracuseStep 11104289 = 8328217) B8328217
theorem B1298503 : Blo 1297967 1298503 := bstep (se 1 (by rfl) ⟨973877, by rfl⟩ : syracuseStep 1298503 = 1947755) B1947755
theorem B1298523 : Blo 1297967 1298523 := bstep (se 1 (by rfl) ⟨973892, by rfl⟩ : syracuseStep 1298523 = 1947785) B1947785
theorem B14037137 : Blo 1297967 14037137 := bstep (se 2 (by rfl) ⟨5263926, by rfl⟩ : syracuseStep 14037137 = 10527853) B10527853
theorem B1298623 : Blo 1297967 1298623 := bstep (se 1 (by rfl) ⟨973967, by rfl⟩ : syracuseStep 1298623 = 1947935) B1947935
theorem B6246665 : Blo 1297967 6246665 := bstep (se 2 (by rfl) ⟨2342499, by rfl⟩ : syracuseStep 6246665 = 4684999) B4684999
theorem B4444463 : Blo 1297967 4444463 := bstep (se 1 (by rfl) ⟨3333347, by rfl⟩ : syracuseStep 4444463 = 6666695) B6666695
theorem B48075113 : Blo 1297967 48075113 := bstep (se 2 (by rfl) ⟨18028167, by rfl⟩ : syracuseStep 48075113 = 36056335) B36056335
theorem B21639557 : Blo 1297967 21639557 := bstep (se 4 (by rfl) ⟨2028708, by rfl⟩ : syracuseStep 21639557 = 4057417) B4057417
theorem B4682171 : Blo 1297967 4682171 := bstep (se 1 (by rfl) ⟨3511628, by rfl⟩ : syracuseStep 4682171 = 7023257) B7023257
theorem B2191927 : Blo 1297967 2191927 := bstep (se 1 (by rfl) ⟨1643945, by rfl⟩ : syracuseStep 2191927 = 3287891) B3287891
theorem B1299071 : Blo 1297967 1299071 := bstep (se 1 (by rfl) ⟨974303, by rfl⟩ : syracuseStep 1299071 = 1948607) B1948607
theorem B1299103 : Blo 1297967 1299103 := bstep (se 1 (by rfl) ⟨974327, by rfl⟩ : syracuseStep 1299103 = 1948655) B1948655
theorem B2921147 : Blo 1297967 2921147 := bstep (se 1 (by rfl) ⟨2190860, by rfl⟩ : syracuseStep 2921147 = 4381721) B4381721
theorem B1299227 : Blo 1297967 1299227 := bstep (se 1 (by rfl) ⟨974420, by rfl⟩ : syracuseStep 1299227 = 1948841) B1948841
theorem B2921255 : Blo 1297967 2921255 := bstep (se 1 (by rfl) ⟨2190941, by rfl⟩ : syracuseStep 2921255 = 4381883) B4381883
theorem B7394111 : Blo 1297967 7394111 := bstep (se 1 (by rfl) ⟨5545583, by rfl⟩ : syracuseStep 7394111 = 11091167) B11091167
theorem B3289967 : Blo 1297967 3289967 := bstep (se 1 (by rfl) ⟨2467475, by rfl⟩ : syracuseStep 3289967 = 4934951) B4934951
theorem B1299487 : Blo 1297967 1299487 := bstep (se 1 (by rfl) ⟨974615, by rfl⟩ : syracuseStep 1299487 = 1949231) B1949231
theorem B1299503 : Blo 1297967 1299503 := bstep (se 1 (by rfl) ⟨974627, by rfl⟩ : syracuseStep 1299503 = 1949255) B1949255
theorem B2921543 : Blo 1297967 2921543 := bstep (se 1 (by rfl) ⟨2191157, by rfl⟩ : syracuseStep 2921543 = 4382315) B4382315
theorem B1299559 : Blo 1297967 1299559 := bstep (se 1 (by rfl) ⟨974669, by rfl⟩ : syracuseStep 1299559 = 1949339) B1949339
theorem B76944491 : Blo 1297967 76944491 := bstep (se 1 (by rfl) ⟨57708368, by rfl⟩ : syracuseStep 76944491 = 115416737) B115416737
theorem B5928065 : Blo 1297967 5928065 := bstep (se 2 (by rfl) ⟨2223024, by rfl⟩ : syracuseStep 5928065 = 4446049) B4446049
theorem B33723539 : Blo 1297967 33723539 := bstep (se 1 (by rfl) ⟨25292654, by rfl⟩ : syracuseStep 33723539 = 50585309) B50585309
theorem B1299623 : Blo 1297967 1299623 := bstep (se 1 (by rfl) ⟨974717, by rfl⟩ : syracuseStep 1299623 = 1949435) B1949435
theorem B1946951 : Blo 1297967 1946951 := bstep (se 1 (by rfl) ⟨1460213, by rfl⟩ : syracuseStep 1946951 = 2920427) B2920427
theorem B42104245 : Blo 1297967 42104245 := bstep (se 5 (by rfl) ⟨1973636, by rfl⟩ : syracuseStep 42104245 = 3947273) B3947273
theorem B1299935 : Blo 1297967 1299935 := bstep (se 1 (by rfl) ⟨974951, by rfl⟩ : syracuseStep 1299935 = 1949903) B1949903
theorem B4929119 : Blo 1297967 4929119 := bstep (se 1 (by rfl) ⟨3696839, by rfl⟩ : syracuseStep 4929119 = 7393679) B7393679
theorem B22198049 : Blo 1297967 22198049 := bstep (se 2 (by rfl) ⟨8324268, by rfl⟩ : syracuseStep 22198049 = 16648537) B16648537
theorem B2193223 : Blo 1297967 2193223 := bstep (se 1 (by rfl) ⟨1644917, by rfl⟩ : syracuseStep 2193223 = 3289835) B3289835
theorem B2922623 : Blo 1297967 2922623 := bstep (se 1 (by rfl) ⟨2191967, by rfl⟩ : syracuseStep 2922623 = 4383935) B4383935
theorem B65796245 : Blo 1297967 65796245 := bstep (se 6 (by rfl) ⟨1542099, by rfl⟩ : syracuseStep 65796245 = 3084199) B3084199
theorem B1645039 : Blo 1297967 1645039 := bstep (se 1 (by rfl) ⟨1233779, by rfl⟩ : syracuseStep 1645039 = 2467559) B2467559
theorem B2775713 : Blo 1297967 2775713 := bstep (se 2 (by rfl) ⟨1040892, by rfl⟩ : syracuseStep 2775713 = 2081785) B2081785
theorem B5544713 : Blo 1297967 5544713 := bstep (se 2 (by rfl) ⟨2079267, by rfl⟩ : syracuseStep 5544713 = 4158535) B4158535
theorem B4381451 : Blo 1297967 4381451 := bstep (se 1 (by rfl) ⟨3286088, by rfl⟩ : syracuseStep 4381451 = 6572177) B6572177
theorem B9861911 : Blo 1297967 9861911 := bstep (se 1 (by rfl) ⟨7396433, by rfl⟩ : syracuseStep 9861911 = 14792867) B14792867
theorem B1948553 : Blo 1297967 1948553 := bstep (se 2 (by rfl) ⟨730707, by rfl⟩ : syracuseStep 1948553 = 1461415) B1461415
theorem B3947663 : Blo 1297967 3947663 := bstep (se 1 (by rfl) ⟨2960747, by rfl⟩ : syracuseStep 3947663 = 5921495) B5921495
theorem B1949321 : Blo 1297967 1949321 := bstep (se 2 (by rfl) ⟨730995, by rfl⟩ : syracuseStep 1949321 = 1461991) B1461991
theorem B2465615 : Blo 1297967 2465615 := bstep (se 1 (by rfl) ⟨1849211, by rfl⟩ : syracuseStep 2465615 = 3698423) B3698423
theorem B4382585 : Blo 1297967 4382585 := bstep (se 2 (by rfl) ⟨1643469, by rfl⟩ : syracuseStep 4382585 = 3286939) B3286939
theorem B9494441 : Blo 1297967 9494441 := bstep (se 2 (by rfl) ⟨3560415, by rfl⟩ : syracuseStep 9494441 = 7120831) B7120831
theorem B5628137 : Blo 1297967 5628137 := bstep (se 2 (by rfl) ⟨2110551, by rfl⟩ : syracuseStep 5628137 = 4221103) B4221103
theorem B14426371 : Blo 1297967 14426371 := bstep (se 1 (by rfl) ⟨10819778, by rfl⟩ : syracuseStep 14426371 = 21639557) B21639557
theorem B8438525 : Blo 1297967 8438525 := bstep (se 3 (by rfl) ⟨1582223, by rfl⟩ : syracuseStep 8438525 = 3164447) B3164447
theorem B4162367 : Blo 1297967 4162367 := bstep (se 1 (by rfl) ⟨3121775, by rfl⟩ : syracuseStep 4162367 = 6243551) B6243551
theorem B3286079 : Blo 1297967 3286079 := bstep (se 1 (by rfl) ⟨2464559, by rfl⟩ : syracuseStep 3286079 = 4929119) B4929119
theorem B8324167 : Blo 1297967 8324167 := bstep (se 1 (by rfl) ⟨6243125, by rfl⟩ : syracuseStep 8324167 = 12486251) B12486251
theorem B12485789 : Blo 1297967 12485789 := bstep (se 3 (by rfl) ⟨2341085, by rfl⟩ : syracuseStep 12485789 = 4682171) B4682171
theorem B3696475 : Blo 1297967 3696475 := bstep (se 1 (by rfl) ⟨2772356, by rfl⟩ : syracuseStep 3696475 = 5544713) B5544713
theorem B3696509 : Blo 1297967 3696509 := bstep (se 3 (by rfl) ⟨693095, by rfl⟩ : syracuseStep 3696509 = 1386191) B1386191
theorem B2631775 : Blo 1297967 2631775 := bstep (se 1 (by rfl) ⟨1973831, by rfl⟩ : syracuseStep 2631775 = 3947663) B3947663
theorem B9366187 : Blo 1297967 9366187 := bstep (se 1 (by rfl) ⟨7024640, by rfl⟩ : syracuseStep 9366187 = 14049281) B14049281
theorem B9358091 : Blo 1297967 9358091 := bstep (se 1 (by rfl) ⟨7018568, by rfl⟩ : syracuseStep 9358091 = 14037137) B14037137
theorem B4164443 : Blo 1297967 4164443 := bstep (se 1 (by rfl) ⟨3123332, by rfl⟩ : syracuseStep 4164443 = 6246665) B6246665
theorem B32050075 : Blo 1297967 32050075 := bstep (se 1 (by rfl) ⟨24037556, by rfl⟩ : syracuseStep 32050075 = 48075113) B48075113
theorem B3288073 : Blo 1297967 3288073 := bstep (se 2 (by rfl) ⟨1233027, by rfl⟩ : syracuseStep 3288073 = 2466055) B2466055
theorem B5549087 : Blo 1297967 5549087 := bstep (se 1 (by rfl) ⟨4161815, by rfl⟩ : syracuseStep 5549087 = 8323631) B8323631
theorem B2632871 : Blo 1297967 2632871 := bstep (se 1 (by rfl) ⟨1974653, by rfl⟩ : syracuseStep 2632871 = 3949307) B3949307
theorem B3697967 : Blo 1297967 3697967 := bstep (se 1 (by rfl) ⟨2773475, by rfl⟩ : syracuseStep 3697967 = 5546951) B5546951
theorem B3952043 : Blo 1297967 3952043 := bstep (se 1 (by rfl) ⟨2964032, by rfl⟩ : syracuseStep 3952043 = 5928065) B5928065
theorem B22482359 : Blo 1297967 22482359 := bstep (se 1 (by rfl) ⟨16861769, by rfl⟩ : syracuseStep 22482359 = 33723539) B33723539
theorem B3698207 : Blo 1297967 3698207 := bstep (se 1 (by rfl) ⟨2773655, by rfl⟩ : syracuseStep 3698207 = 5547311) B5547311
theorem B1297967 : Blo 1297967 1297967 := bstep (se 1 (by rfl) ⟨973475, by rfl⟩ : syracuseStep 1297967 = 1946951) B1946951
theorem B14798699 : Blo 1297967 14798699 := bstep (se 1 (by rfl) ⟨11099024, by rfl⟩ : syracuseStep 14798699 = 22198049) B22198049
theorem B43864163 : Blo 1297967 43864163 := bstep (se 1 (by rfl) ⟨32898122, by rfl⟩ : syracuseStep 43864163 = 65796245) B65796245
theorem B7401901 : Blo 1297967 7401901 := bstep (se 3 (by rfl) ⟨1387856, by rfl⟩ : syracuseStep 7401901 = 2775713) B2775713
theorem B6664639 : Blo 1297967 6664639 := bstep (se 1 (by rfl) ⟨4998479, by rfl⟩ : syracuseStep 6664639 = 9996959) B9996959
theorem B2920967 : Blo 1297967 2920967 := bstep (se 1 (by rfl) ⟨2190725, by rfl⟩ : syracuseStep 2920967 = 4381451) B4381451
theorem B6574607 : Blo 1297967 6574607 := bstep (se 1 (by rfl) ⟨4930955, by rfl⟩ : syracuseStep 6574607 = 9861911) B9861911
theorem B4387391 : Blo 1297967 4387391 := bstep (se 1 (by rfl) ⟨3290543, by rfl⟩ : syracuseStep 4387391 = 6581087) B6581087
theorem B1299035 : Blo 1297967 1299035 := bstep (se 1 (by rfl) ⟨974276, by rfl⟩ : syracuseStep 1299035 = 1948553) B1948553
theorem B5927917 : Blo 1297967 5927917 := bstep (se 3 (by rfl) ⟨1111484, by rfl⟩ : syracuseStep 5927917 = 2222969) B2222969
theorem B1299547 : Blo 1297967 1299547 := bstep (se 1 (by rfl) ⟨974660, by rfl⟩ : syracuseStep 1299547 = 1949321) B1949321
theorem B4928647 : Blo 1297967 4928647 := bstep (se 1 (by rfl) ⟨3696485, by rfl⟩ : syracuseStep 4928647 = 7392971) B7392971
theorem B1643743 : Blo 1297967 1643743 := bstep (se 1 (by rfl) ⟨1232807, by rfl⟩ : syracuseStep 1643743 = 2465615) B2465615
theorem B2921723 : Blo 1297967 2921723 := bstep (se 1 (by rfl) ⟨2191292, by rfl⟩ : syracuseStep 2921723 = 4382585) B4382585
theorem B6329627 : Blo 1297967 6329627 := bstep (se 1 (by rfl) ⟨4747220, by rfl⟩ : syracuseStep 6329627 = 9494441) B9494441
theorem B11842847 : Blo 1297967 11842847 := bstep (se 1 (by rfl) ⟨8882135, by rfl⟩ : syracuseStep 11842847 = 17764271) B17764271
theorem B7402859 : Blo 1297967 7402859 := bstep (se 1 (by rfl) ⟨5552144, by rfl⟩ : syracuseStep 7402859 = 11104289) B11104289
theorem B1299839 : Blo 1297967 1299839 := bstep (se 1 (by rfl) ⟨974879, by rfl⟩ : syracuseStep 1299839 = 1949759) B1949759
theorem B1299903 : Blo 1297967 1299903 := bstep (se 1 (by rfl) ⟨974927, by rfl⟩ : syracuseStep 1299903 = 1949855) B1949855
theorem B2922011 : Blo 1297967 2922011 := bstep (se 1 (by rfl) ⟨2191508, by rfl⟩ : syracuseStep 2922011 = 4383017) B4383017
theorem B2962975 : Blo 1297967 2962975 := bstep (se 1 (by rfl) ⟨2222231, by rfl⟩ : syracuseStep 2962975 = 4444463) B4444463
theorem B2774569 : Blo 1297967 2774569 := bstep (se 2 (by rfl) ⟨1040463, by rfl⟩ : syracuseStep 2774569 = 2080927) B2080927
theorem B4445887 : Blo 1297967 4445887 := bstep (se 1 (by rfl) ⟨3334415, by rfl⟩ : syracuseStep 4445887 = 6668831) B6668831
theorem B1947431 : Blo 1297967 1947431 := bstep (se 1 (by rfl) ⟨1460573, by rfl⟩ : syracuseStep 1947431 = 2921147) B2921147
theorem B1947503 : Blo 1297967 1947503 := bstep (se 1 (by rfl) ⟨1460627, by rfl⟩ : syracuseStep 1947503 = 2921255) B2921255
theorem B4929407 : Blo 1297967 4929407 := bstep (se 1 (by rfl) ⟨3697055, by rfl⟩ : syracuseStep 4929407 = 7394111) B7394111
theorem B3118987 : Blo 1297967 3118987 := bstep (se 1 (by rfl) ⟨2339240, by rfl⟩ : syracuseStep 3118987 = 4678481) B4678481
theorem B2193311 : Blo 1297967 2193311 := bstep (se 1 (by rfl) ⟨1644983, by rfl⟩ : syracuseStep 2193311 = 3289967) B3289967
theorem B14997467 : Blo 1297967 14997467 := bstep (se 1 (by rfl) ⟨11248100, by rfl⟩ : syracuseStep 14997467 = 22496201) B22496201
theorem B2193385 : Blo 1297967 2193385 := bstep (se 2 (by rfl) ⟨822519, by rfl⟩ : syracuseStep 2193385 = 1645039) B1645039
theorem B1947695 : Blo 1297967 1947695 := bstep (se 1 (by rfl) ⟨1460771, by rfl⟩ : syracuseStep 1947695 = 2921543) B2921543
theorem B51296327 : Blo 1297967 51296327 := bstep (se 1 (by rfl) ⟨38472245, by rfl⟩ : syracuseStep 51296327 = 76944491) B76944491
theorem B2922569 : Blo 1297967 2922569 := bstep (se 2 (by rfl) ⟨1095963, by rfl⟩ : syracuseStep 2922569 = 2191927) B2191927
theorem B1948415 : Blo 1297967 1948415 := bstep (se 1 (by rfl) ⟨1461311, by rfl⟩ : syracuseStep 1948415 = 2922623) B2922623
theorem B2923271 : Blo 1297967 2923271 := bstep (se 1 (by rfl) ⟨2192453, by rfl⟩ : syracuseStep 2923271 = 4384907) B4384907
theorem B34224905 : Blo 1297967 34224905 := bstep (se 2 (by rfl) ⟨12834339, by rfl⟩ : syracuseStep 34224905 = 25668679) B25668679
theorem B56138993 : Blo 1297967 56138993 := bstep (se 2 (by rfl) ⟨21052122, by rfl⟩ : syracuseStep 56138993 = 42104245) B42104245
theorem B1949225 : Blo 1297967 1949225 := bstep (se 2 (by rfl) ⟨730959, by rfl⟩ : syracuseStep 1949225 = 1461919) B1461919
theorem B2465387 : Blo 1297967 2465387 := bstep (se 1 (by rfl) ⟨1849040, by rfl⟩ : syracuseStep 2465387 = 3698081) B3698081
theorem B11853499 : Blo 1297967 11853499 := bstep (se 1 (by rfl) ⟨8890124, by rfl⟩ : syracuseStep 11853499 = 17780249) B17780249
theorem B2924297 : Blo 1297967 2924297 := bstep (se 2 (by rfl) ⟨1096611, by rfl⟩ : syracuseStep 2924297 = 2193223) B2193223
theorem B3121055 : Blo 1297967 3121055 := bstep (se 1 (by rfl) ⟨2340791, by rfl⟩ : syracuseStep 3121055 = 4681583) B4681583
theorem B23699411 : Blo 1297967 23699411 := bstep (se 1 (by rfl) ⟨17774558, by rfl⟩ : syracuseStep 23699411 = 35549117) B35549117
theorem B7397345 : Blo 1297967 7397345 := bstep (se 2 (by rfl) ⟨2774004, by rfl⟩ : syracuseStep 7397345 = 5548009) B5548009
theorem B19235161 : Blo 1297967 19235161 := bstep (se 2 (by rfl) ⟨7213185, by rfl⟩ : syracuseStep 19235161 = 14426371) B14426371
theorem B4383071 : Blo 1297967 4383071 := bstep (se 1 (by rfl) ⟨3287303, by rfl⟩ : syracuseStep 4383071 = 6574607) B6574607
theorem B2924927 : Blo 1297967 2924927 := bstep (se 1 (by rfl) ⟨2193695, by rfl⟩ : syracuseStep 2924927 = 4387391) B4387391
theorem B7020989 : Blo 1297967 7020989 := bstep (se 3 (by rfl) ⟨1316435, by rfl⟩ : syracuseStep 7020989 = 2632871) B2632871
theorem B15008365 : Blo 1297967 15008365 := bstep (se 3 (by rfl) ⟨2814068, by rfl⟩ : syracuseStep 15008365 = 5628137) B5628137
theorem B8323859 : Blo 1297967 8323859 := bstep (se 1 (by rfl) ⟨6242894, by rfl⟩ : syracuseStep 8323859 = 12485789) B12485789
theorem B4219751 : Blo 1297967 4219751 := bstep (se 1 (by rfl) ⟨3164813, by rfl⟩ : syracuseStep 4219751 = 6329627) B6329627
theorem B3286271 : Blo 1297967 3286271 := bstep (se 1 (by rfl) ⟨2464703, by rfl⟩ : syracuseStep 3286271 = 4929407) B4929407
theorem B4384097 : Blo 1297967 4384097 := bstep (se 2 (by rfl) ⟨1644036, by rfl⟩ : syracuseStep 4384097 = 3288073) B3288073
theorem B6571529 : Blo 1297967 6571529 := bstep (se 2 (by rfl) ⟨2464323, by rfl⟩ : syracuseStep 6571529 = 4928647) B4928647
theorem B22816603 : Blo 1297967 22816603 := bstep (se 1 (by rfl) ⟨17112452, by rfl⟩ : syracuseStep 22816603 = 34224905) B34224905
theorem B3950633 : Blo 1297967 3950633 := bstep (se 2 (by rfl) ⟨1481487, by rfl⟩ : syracuseStep 3950633 = 2962975) B2962975
theorem B15804665 : Blo 1297967 15804665 := bstep (se 2 (by rfl) ⟨5926749, by rfl⟩ : syracuseStep 15804665 = 11853499) B11853499
theorem B9865799 : Blo 1297967 9865799 := bstep (se 1 (by rfl) ⟨7399349, by rfl⟩ : syracuseStep 9865799 = 14798699) B14798699
theorem B3509033 : Blo 1297967 3509033 := bstep (se 2 (by rfl) ⟨1315887, by rfl⟩ : syracuseStep 3509033 = 2631775) B2631775
theorem B2190719 : Blo 1297967 2190719 := bstep (se 1 (by rfl) ⟨1643039, by rfl⟩ : syracuseStep 2190719 = 3286079) B3286079
theorem B12488249 : Blo 1297967 12488249 := bstep (se 2 (by rfl) ⟨4683093, by rfl⟩ : syracuseStep 12488249 = 9366187) B9366187
theorem B4935239 : Blo 1297967 4935239 := bstep (se 1 (by rfl) ⟨3701429, by rfl⟩ : syracuseStep 4935239 = 7402859) B7402859
theorem B1298287 : Blo 1297967 1298287 := bstep (se 1 (by rfl) ⟨973715, by rfl⟩ : syracuseStep 1298287 = 1947431) B1947431
theorem B42733433 : Blo 1297967 42733433 := bstep (se 2 (by rfl) ⟨16025037, by rfl⟩ : syracuseStep 42733433 = 32050075) B32050075
theorem B1298335 : Blo 1297967 1298335 := bstep (se 1 (by rfl) ⟨973751, by rfl⟩ : syracuseStep 1298335 = 1947503) B1947503
theorem B1462207 : Blo 1297967 1462207 := bstep (se 1 (by rfl) ⟨1096655, by rfl⟩ : syracuseStep 1462207 = 2193311) B2193311
theorem B9998311 : Blo 1297967 9998311 := bstep (se 1 (by rfl) ⟨7498733, by rfl⟩ : syracuseStep 9998311 = 14997467) B14997467
theorem B1298463 : Blo 1297967 1298463 := bstep (se 1 (by rfl) ⟨973847, by rfl⟩ : syracuseStep 1298463 = 1947695) B1947695
theorem B34197551 : Blo 1297967 34197551 := bstep (se 1 (by rfl) ⟨25648163, by rfl⟩ : syracuseStep 34197551 = 51296327) B51296327
theorem B2191657 : Blo 1297967 2191657 := bstep (se 2 (by rfl) ⟨821871, by rfl⟩ : syracuseStep 2191657 = 1643743) B1643743
theorem B1298943 : Blo 1297967 1298943 := bstep (se 1 (by rfl) ⟨974207, by rfl⟩ : syracuseStep 1298943 = 1948415) B1948415
theorem B6238727 : Blo 1297967 6238727 := bstep (se 1 (by rfl) ⟨4679045, by rfl⟩ : syracuseStep 6238727 = 9358091) B9358091
theorem B3699391 : Blo 1297967 3699391 := bstep (se 1 (by rfl) ⟨2774543, by rfl⟩ : syracuseStep 3699391 = 5549087) B5549087
theorem B3699425 : Blo 1297967 3699425 := bstep (se 2 (by rfl) ⟨1387284, by rfl⟩ : syracuseStep 3699425 = 2774569) B2774569
theorem B37425995 : Blo 1297967 37425995 := bstep (se 1 (by rfl) ⟨28069496, by rfl⟩ : syracuseStep 37425995 = 56138993) B56138993
theorem B5927849 : Blo 1297967 5927849 := bstep (se 2 (by rfl) ⟨2222943, by rfl⟩ : syracuseStep 5927849 = 4445887) B4445887
theorem B2634695 : Blo 1297967 2634695 := bstep (se 1 (by rfl) ⟨1976021, by rfl⟩ : syracuseStep 2634695 = 3952043) B3952043
theorem B14988239 : Blo 1297967 14988239 := bstep (se 1 (by rfl) ⟨11241179, by rfl⟩ : syracuseStep 14988239 = 22482359) B22482359
theorem B1299483 : Blo 1297967 1299483 := bstep (se 1 (by rfl) ⟨974612, by rfl⟩ : syracuseStep 1299483 = 1949225) B1949225
theorem B1643591 : Blo 1297967 1643591 := bstep (se 1 (by rfl) ⟨1232693, by rfl⟩ : syracuseStep 1643591 = 2465387) B2465387
theorem B4928633 : Blo 1297967 4928633 := bstep (se 2 (by rfl) ⟨1848237, by rfl⟩ : syracuseStep 4928633 = 3696475) B3696475
theorem B4158649 : Blo 1297967 4158649 := bstep (se 2 (by rfl) ⟨1559493, by rfl⟩ : syracuseStep 4158649 = 3118987) B3118987
theorem B15799607 : Blo 1297967 15799607 := bstep (se 1 (by rfl) ⟨11849705, by rfl⟩ : syracuseStep 15799607 = 23699411) B23699411
theorem B29242775 : Blo 1297967 29242775 := bstep (se 1 (by rfl) ⟨21932081, by rfl⟩ : syracuseStep 29242775 = 43864163) B43864163
theorem B1947311 : Blo 1297967 1947311 := bstep (se 1 (by rfl) ⟨1460483, by rfl⟩ : syracuseStep 1947311 = 2920967) B2920967
theorem B5625683 : Blo 1297967 5625683 := bstep (se 1 (by rfl) ⟨4219262, by rfl⟩ : syracuseStep 5625683 = 8438525) B8438525
theorem B2774911 : Blo 1297967 2774911 := bstep (se 1 (by rfl) ⟨2081183, by rfl⟩ : syracuseStep 2774911 = 4162367) B4162367
theorem B9869201 : Blo 1297967 9869201 := bstep (se 2 (by rfl) ⟨3700950, by rfl⟩ : syracuseStep 9869201 = 7401901) B7401901
theorem B8886185 : Blo 1297967 8886185 := bstep (se 2 (by rfl) ⟨3332319, by rfl⟩ : syracuseStep 8886185 = 6664639) B6664639
theorem B1947815 : Blo 1297967 1947815 := bstep (se 1 (by rfl) ⟨1460861, by rfl⟩ : syracuseStep 1947815 = 2921723) B2921723
theorem B7895231 : Blo 1297967 7895231 := bstep (se 1 (by rfl) ⟨5921423, by rfl⟩ : syracuseStep 7895231 = 11842847) B11842847
theorem B1948007 : Blo 1297967 1948007 := bstep (se 1 (by rfl) ⟨1461005, by rfl⟩ : syracuseStep 1948007 = 2922011) B2922011
theorem B2464339 : Blo 1297967 2464339 := bstep (se 1 (by rfl) ⟨1848254, by rfl⟩ : syracuseStep 2464339 = 3696509) B3696509
theorem B7903889 : Blo 1297967 7903889 := bstep (se 2 (by rfl) ⟨2963958, by rfl⟩ : syracuseStep 7903889 = 5927917) B5927917
theorem B1948379 : Blo 1297967 1948379 := bstep (se 1 (by rfl) ⟨1461284, by rfl⟩ : syracuseStep 1948379 = 2922569) B2922569
theorem B11098889 : Blo 1297967 11098889 := bstep (se 2 (by rfl) ⟨4162083, by rfl⟩ : syracuseStep 11098889 = 8324167) B8324167
theorem B1948847 : Blo 1297967 1948847 := bstep (se 1 (by rfl) ⟨1461635, by rfl⟩ : syracuseStep 1948847 = 2923271) B2923271
theorem B2776295 : Blo 1297967 2776295 := bstep (se 1 (by rfl) ⟨2082221, by rfl⟩ : syracuseStep 2776295 = 4164443) B4164443
theorem B2465311 : Blo 1297967 2465311 := bstep (se 1 (by rfl) ⟨1848983, by rfl⟩ : syracuseStep 2465311 = 3697967) B3697967
theorem B2465471 : Blo 1297967 2465471 := bstep (se 1 (by rfl) ⟨1849103, by rfl⟩ : syracuseStep 2465471 = 3698207) B3698207
theorem B1949531 : Blo 1297967 1949531 := bstep (se 1 (by rfl) ⟨1462148, by rfl⟩ : syracuseStep 1949531 = 2924297) B2924297
theorem B2080703 : Blo 1297967 2080703 := bstep (se 1 (by rfl) ⟨1560527, by rfl⟩ : syracuseStep 2080703 = 3121055) B3121055
theorem B2924513 : Blo 1297967 2924513 := bstep (se 2 (by rfl) ⟨1096692, by rfl⟩ : syracuseStep 2924513 = 2193385) B2193385
theorem B4931563 : Blo 1297967 4931563 := bstep (se 1 (by rfl) ⟨3698672, by rfl⟩ : syracuseStep 4931563 = 7397345) B7397345
theorem B22798367 : Blo 1297967 22798367 := bstep (se 1 (by rfl) ⟨17098775, by rfl⟩ : syracuseStep 22798367 = 34197551) B34197551
theorem B10535021 : Blo 1297967 10535021 := bstep (se 3 (by rfl) ⟨1975316, by rfl⟩ : syracuseStep 10535021 = 3950633) B3950633
theorem B4382909 : Blo 1297967 4382909 := bstep (se 3 (by rfl) ⟨821795, by rfl⟩ : syracuseStep 4382909 = 1643591) B1643591
theorem B1949951 : Blo 1297967 1949951 := bstep (se 1 (by rfl) ⟨1462463, by rfl⟩ : syracuseStep 1949951 = 2924927) B2924927
theorem B37429685 : Blo 1297967 37429685 := bstep (se 5 (by rfl) ⟨1754516, by rfl⟩ : syracuseStep 37429685 = 3509033) B3509033
theorem B2466283 : Blo 1297967 2466283 := bstep (se 1 (by rfl) ⟨1849712, by rfl⟩ : syracuseStep 2466283 = 3699425) B3699425
theorem B3285755 : Blo 1297967 3285755 := bstep (se 1 (by rfl) ⟨2464316, by rfl⟩ : syracuseStep 3285755 = 4928633) B4928633
theorem B3285785 : Blo 1297967 3285785 := bstep (se 2 (by rfl) ⟨1232169, by rfl⟩ : syracuseStep 3285785 = 2464339) B2464339
theorem B4932521 : Blo 1297967 4932521 := bstep (se 2 (by rfl) ⟨1849695, by rfl⟩ : syracuseStep 4932521 = 3699391) B3699391
theorem B6579467 : Blo 1297967 6579467 := bstep (se 1 (by rfl) ⟨4934600, by rfl⟩ : syracuseStep 6579467 = 9869201) B9869201
theorem B5924123 : Blo 1297967 5924123 := bstep (se 1 (by rfl) ⟨4443092, by rfl⟩ : syracuseStep 5924123 = 8886185) B8886185
theorem B10536443 : Blo 1297967 10536443 := bstep (se 1 (by rfl) ⟨7902332, by rfl⟩ : syracuseStep 10536443 = 15804665) B15804665
theorem B5269259 : Blo 1297967 5269259 := bstep (se 1 (by rfl) ⟨3951944, by rfl⟩ : syracuseStep 5269259 = 7903889) B7903889
theorem B7399259 : Blo 1297967 7399259 := bstep (se 1 (by rfl) ⟨5549444, by rfl⟩ : syracuseStep 7399259 = 11098889) B11098889
theorem B3287081 : Blo 1297967 3287081 := bstep (se 2 (by rfl) ⟨1232655, by rfl⟩ : syracuseStep 3287081 = 2465311) B2465311
theorem B1460479 : Blo 1297967 1460479 := bstep (se 1 (by rfl) ⟨1095359, by rfl⟩ : syracuseStep 1460479 = 2190719) B2190719
theorem B8325499 : Blo 1297967 8325499 := bstep (se 1 (by rfl) ⟨6244124, by rfl⟩ : syracuseStep 8325499 = 12488249) B12488249
theorem B1387135 : Blo 1297967 1387135 := bstep (se 1 (by rfl) ⟨1040351, by rfl⟩ : syracuseStep 1387135 = 2080703) B2080703
theorem B13331081 : Blo 1297967 13331081 := bstep (se 2 (by rfl) ⟨4999155, by rfl⟩ : syracuseStep 13331081 = 9998311) B9998311
theorem B4680659 : Blo 1297967 4680659 := bstep (se 1 (by rfl) ⟨3510494, by rfl⟩ : syracuseStep 4680659 = 7020989) B7020989
theorem B5549239 : Blo 1297967 5549239 := bstep (se 1 (by rfl) ⟨4161929, by rfl⟩ : syracuseStep 5549239 = 8323859) B8323859
theorem B3951899 : Blo 1297967 3951899 := bstep (se 1 (by rfl) ⟨2963924, by rfl⟩ : syracuseStep 3951899 = 5927849) B5927849
theorem B1756463 : Blo 1297967 1756463 := bstep (se 1 (by rfl) ⟨1317347, by rfl⟩ : syracuseStep 1756463 = 2634695) B2634695
theorem B2190847 : Blo 1297967 2190847 := bstep (se 1 (by rfl) ⟨1643135, by rfl⟩ : syracuseStep 2190847 = 3286271) B3286271
theorem B1298207 : Blo 1297967 1298207 := bstep (se 1 (by rfl) ⟨973655, by rfl⟩ : syracuseStep 1298207 = 1947311) B1947311
theorem B1298543 : Blo 1297967 1298543 := bstep (se 1 (by rfl) ⟨973907, by rfl⟩ : syracuseStep 1298543 = 1947815) B1947815
theorem B5263487 : Blo 1297967 5263487 := bstep (se 1 (by rfl) ⟨3947615, by rfl⟩ : syracuseStep 5263487 = 7895231) B7895231
theorem B1298671 : Blo 1297967 1298671 := bstep (se 1 (by rfl) ⟨974003, by rfl⟩ : syracuseStep 1298671 = 1948007) B1948007
theorem B1298919 : Blo 1297967 1298919 := bstep (se 1 (by rfl) ⟨974189, by rfl⟩ : syracuseStep 1298919 = 1948379) B1948379
theorem B1299231 : Blo 1297967 1299231 := bstep (se 1 (by rfl) ⟨974423, by rfl⟩ : syracuseStep 1299231 = 1948847) B1948847
theorem B3290159 : Blo 1297967 3290159 := bstep (se 1 (by rfl) ⟨2467619, by rfl⟩ : syracuseStep 3290159 = 4935239) B4935239
theorem B30422137 : Blo 1297967 30422137 := bstep (se 2 (by rfl) ⟨11408301, by rfl⟩ : syracuseStep 30422137 = 22816603) B22816603
theorem B1643647 : Blo 1297967 1643647 := bstep (se 1 (by rfl) ⟨1232735, by rfl⟩ : syracuseStep 1643647 = 2465471) B2465471
theorem B3699881 : Blo 1297967 3699881 := bstep (se 2 (by rfl) ⟨1387455, by rfl⟩ : syracuseStep 3699881 = 2774911) B2774911
theorem B1299687 : Blo 1297967 1299687 := bstep (se 1 (by rfl) ⟨974765, by rfl⟩ : syracuseStep 1299687 = 1949531) B1949531
theorem B28488955 : Blo 1297967 28488955 := bstep (se 1 (by rfl) ⟨21366716, by rfl⟩ : syracuseStep 28488955 = 42733433) B42733433
theorem B6575417 : Blo 1297967 6575417 := bstep (se 2 (by rfl) ⟨2465781, by rfl⟩ : syracuseStep 6575417 = 4931563) B4931563
theorem B2922047 : Blo 1297967 2922047 := bstep (se 1 (by rfl) ⟨2191535, by rfl⟩ : syracuseStep 2922047 = 4383071) B4383071
theorem B4159151 : Blo 1297967 4159151 := bstep (se 1 (by rfl) ⟨3119363, by rfl⟩ : syracuseStep 4159151 = 6238727) B6238727
theorem B2922209 : Blo 1297967 2922209 := bstep (se 2 (by rfl) ⟨1095828, by rfl⟩ : syracuseStep 2922209 = 2191657) B2191657
theorem B25646881 : Blo 1297967 25646881 := bstep (se 2 (by rfl) ⟨9617580, by rfl⟩ : syracuseStep 25646881 = 19235161) B19235161
theorem B24950663 : Blo 1297967 24950663 := bstep (se 1 (by rfl) ⟨18712997, by rfl⟩ : syracuseStep 24950663 = 37425995) B37425995
theorem B9992159 : Blo 1297967 9992159 := bstep (se 1 (by rfl) ⟨7494119, by rfl⟩ : syracuseStep 9992159 = 14988239) B14988239
theorem B20011153 : Blo 1297967 20011153 := bstep (se 2 (by rfl) ⟨7504182, by rfl⟩ : syracuseStep 20011153 = 15008365) B15008365
theorem B10533071 : Blo 1297967 10533071 := bstep (se 1 (by rfl) ⟨7899803, by rfl⟩ : syracuseStep 10533071 = 15799607) B15799607
theorem B2922731 : Blo 1297967 2922731 := bstep (se 1 (by rfl) ⟨2192048, by rfl⟩ : syracuseStep 2922731 = 4384097) B4384097
theorem B19495183 : Blo 1297967 19495183 := bstep (se 1 (by rfl) ⟨14621387, by rfl⟩ : syracuseStep 19495183 = 29242775) B29242775
theorem B4381019 : Blo 1297967 4381019 := bstep (se 1 (by rfl) ⟨3285764, by rfl⟩ : syracuseStep 4381019 = 6571529) B6571529
theorem B3750455 : Blo 1297967 3750455 := bstep (se 1 (by rfl) ⟨2812841, by rfl⟩ : syracuseStep 3750455 = 5625683) B5625683
theorem B5544865 : Blo 1297967 5544865 := bstep (se 2 (by rfl) ⟨2079324, by rfl⟩ : syracuseStep 5544865 = 4158649) B4158649
theorem B180042709 : Blo 1297967 180042709 := bstep (se 7 (by rfl) ⟨2109875, by rfl⟩ : syracuseStep 180042709 = 4219751) B4219751
theorem B6577199 : Blo 1297967 6577199 := bstep (se 1 (by rfl) ⟨4932899, by rfl⟩ : syracuseStep 6577199 = 9865799) B9865799
theorem B1850863 : Blo 1297967 1850863 := bstep (se 1 (by rfl) ⟨1388147, by rfl⟩ : syracuseStep 1850863 = 2776295) B2776295
theorem B1949609 : Blo 1297967 1949609 := bstep (se 2 (by rfl) ⟨731103, by rfl⟩ : syracuseStep 1949609 = 1462207) B1462207
theorem B1949675 : Blo 1297967 1949675 := bstep (se 1 (by rfl) ⟨1462256, by rfl⟩ : syracuseStep 1949675 = 2924513) B2924513
theorem B26681537 : Blo 1297967 26681537 := bstep (se 2 (by rfl) ⟨10005576, by rfl⟩ : syracuseStep 26681537 = 20011153) B20011153
theorem B24953123 : Blo 1297967 24953123 := bstep (se 1 (by rfl) ⟨18714842, by rfl⟩ : syracuseStep 24953123 = 37429685) B37429685
theorem B25993577 : Blo 1297967 25993577 := bstep (se 2 (by rfl) ⟨9747591, by rfl⟩ : syracuseStep 25993577 = 19495183) B19495183
theorem B11100665 : Blo 1297967 11100665 := bstep (se 2 (by rfl) ⟨4162749, by rfl⟩ : syracuseStep 11100665 = 8325499) B8325499
theorem B7398053 : Blo 1297967 7398053 := bstep (se 4 (by rfl) ⟨693567, by rfl⟩ : syracuseStep 7398053 = 1387135) B1387135
theorem B2466587 : Blo 1297967 2466587 := bstep (se 1 (by rfl) ⟨1849940, by rfl⟩ : syracuseStep 2466587 = 3699881) B3699881
theorem B3949415 : Blo 1297967 3949415 := bstep (se 1 (by rfl) ⟨2962061, by rfl⟩ : syracuseStep 3949415 = 5924123) B5924123
theorem B4383611 : Blo 1297967 4383611 := bstep (se 1 (by rfl) ⟨3287708, by rfl⟩ : syracuseStep 4383611 = 6575417) B6575417
theorem B4932839 : Blo 1297967 4932839 := bstep (se 1 (by rfl) ⟨3699629, by rfl⟩ : syracuseStep 4932839 = 7399259) B7399259
theorem B6661439 : Blo 1297967 6661439 := bstep (se 1 (by rfl) ⟨4996079, by rfl⟩ : syracuseStep 6661439 = 9992159) B9992159
theorem B7022047 : Blo 1297967 7022047 := bstep (se 1 (by rfl) ⟨5266535, by rfl⟩ : syracuseStep 7022047 = 10533071) B10533071
theorem B7398985 : Blo 1297967 7398985 := bstep (se 2 (by rfl) ⟨2774619, by rfl⟩ : syracuseStep 7398985 = 5549239) B5549239
theorem B2500303 : Blo 1297967 2500303 := bstep (se 1 (by rfl) ⟨1875227, by rfl⟩ : syracuseStep 2500303 = 3750455) B3750455
theorem B2467817 : Blo 1297967 2467817 := bstep (se 2 (by rfl) ⟨925431, by rfl⟩ : syracuseStep 2467817 = 1850863) B1850863
theorem B14051357 : Blo 1297967 14051357 := bstep (se 3 (by rfl) ⟨2634629, by rfl⟩ : syracuseStep 14051357 = 5269259) B5269259
theorem B4384799 : Blo 1297967 4384799 := bstep (se 1 (by rfl) ⟨3288599, by rfl⟩ : syracuseStep 4384799 = 6577199) B6577199
theorem B34195841 : Blo 1297967 34195841 := bstep (se 2 (by rfl) ⟨12823440, by rfl⟩ : syracuseStep 34195841 = 25646881) B25646881
theorem B15198911 : Blo 1297967 15198911 := bstep (se 1 (by rfl) ⟨11399183, by rfl⟩ : syracuseStep 15198911 = 22798367) B22798367
theorem B7023347 : Blo 1297967 7023347 := bstep (se 1 (by rfl) ⟨5267510, by rfl⟩ : syracuseStep 7023347 = 10535021) B10535021
theorem B3508991 : Blo 1297967 3508991 := bstep (se 1 (by rfl) ⟨2631743, by rfl⟩ : syracuseStep 3508991 = 5263487) B5263487
theorem B2190503 : Blo 1297967 2190503 := bstep (se 1 (by rfl) ⟨1642877, by rfl⟩ : syracuseStep 2190503 = 3285755) B3285755
theorem B2190523 : Blo 1297967 2190523 := bstep (se 1 (by rfl) ⟨1642892, by rfl⟩ : syracuseStep 2190523 = 3285785) B3285785
theorem B3288347 : Blo 1297967 3288347 := bstep (se 1 (by rfl) ⟨2466260, by rfl⟩ : syracuseStep 3288347 = 4932521) B4932521
theorem B3288377 : Blo 1297967 3288377 := bstep (se 2 (by rfl) ⟨1233141, by rfl⟩ : syracuseStep 3288377 = 2466283) B2466283
theorem B4386311 : Blo 1297967 4386311 := bstep (se 1 (by rfl) ⟨3289733, by rfl⟩ : syracuseStep 4386311 = 6579467) B6579467
theorem B7024295 : Blo 1297967 7024295 := bstep (se 1 (by rfl) ⟨5268221, by rfl⟩ : syracuseStep 7024295 = 10536443) B10536443
theorem B2772767 : Blo 1297967 2772767 := bstep (se 1 (by rfl) ⟨2079575, by rfl⟩ : syracuseStep 2772767 = 4159151) B4159151
theorem B7393153 : Blo 1297967 7393153 := bstep (se 2 (by rfl) ⟨2772432, by rfl⟩ : syracuseStep 7393153 = 5544865) B5544865
theorem B16633775 : Blo 1297967 16633775 := bstep (se 1 (by rfl) ⟨12475331, by rfl⟩ : syracuseStep 16633775 = 24950663) B24950663
theorem B2191387 : Blo 1297967 2191387 := bstep (se 1 (by rfl) ⟨1643540, by rfl⟩ : syracuseStep 2191387 = 3287081) B3287081
theorem B40562849 : Blo 1297967 40562849 := bstep (se 2 (by rfl) ⟨15211068, by rfl⟩ : syracuseStep 40562849 = 30422137) B30422137
theorem B2191529 : Blo 1297967 2191529 := bstep (se 2 (by rfl) ⟨821823, by rfl⟩ : syracuseStep 2191529 = 1643647) B1643647
theorem B2920679 : Blo 1297967 2920679 := bstep (se 1 (by rfl) ⟨2190509, by rfl⟩ : syracuseStep 2920679 = 4381019) B4381019
theorem B35549549 : Blo 1297967 35549549 := bstep (se 3 (by rfl) ⟨6665540, by rfl⟩ : syracuseStep 35549549 = 13331081) B13331081
theorem B2921129 : Blo 1297967 2921129 := bstep (se 2 (by rfl) ⟨1095423, by rfl⟩ : syracuseStep 2921129 = 2190847) B2190847
theorem B2634599 : Blo 1297967 2634599 := bstep (se 1 (by rfl) ⟨1975949, by rfl⟩ : syracuseStep 2634599 = 3951899) B3951899
theorem B1299739 : Blo 1297967 1299739 := bstep (se 1 (by rfl) ⟨974804, by rfl⟩ : syracuseStep 1299739 = 1949609) B1949609
theorem B1299783 : Blo 1297967 1299783 := bstep (se 1 (by rfl) ⟨974837, by rfl⟩ : syracuseStep 1299783 = 1949675) B1949675
theorem B2921939 : Blo 1297967 2921939 := bstep (se 1 (by rfl) ⟨2191454, by rfl⟩ : syracuseStep 2921939 = 4382909) B4382909
theorem B1299967 : Blo 1297967 1299967 := bstep (se 1 (by rfl) ⟨974975, by rfl⟩ : syracuseStep 1299967 = 1949951) B1949951
theorem B1947305 : Blo 1297967 1947305 := bstep (se 2 (by rfl) ⟨730239, by rfl⟩ : syracuseStep 1947305 = 1460479) B1460479
theorem B2193439 : Blo 1297967 2193439 := bstep (se 1 (by rfl) ⟨1645079, by rfl⟩ : syracuseStep 2193439 = 3290159) B3290159
theorem B4683901 : Blo 1297967 4683901 := bstep (se 3 (by rfl) ⟨878231, by rfl⟩ : syracuseStep 4683901 = 1756463) B1756463
theorem B1948031 : Blo 1297967 1948031 := bstep (se 1 (by rfl) ⟨1461023, by rfl⟩ : syracuseStep 1948031 = 2922047) B2922047
theorem B1948139 : Blo 1297967 1948139 := bstep (se 1 (by rfl) ⟨1461104, by rfl⟩ : syracuseStep 1948139 = 2922209) B2922209
theorem B240056945 : Blo 1297967 240056945 := bstep (se 2 (by rfl) ⟨90021354, by rfl⟩ : syracuseStep 240056945 = 180042709) B180042709
theorem B1948487 : Blo 1297967 1948487 := bstep (se 1 (by rfl) ⟨1461365, by rfl⟩ : syracuseStep 1948487 = 2922731) B2922731
theorem B37985273 : Blo 1297967 37985273 := bstep (se 2 (by rfl) ⟨14244477, by rfl⟩ : syracuseStep 37985273 = 28488955) B28488955
theorem B3120439 : Blo 1297967 3120439 := bstep (se 1 (by rfl) ⟨2340329, by rfl⟩ : syracuseStep 3120439 = 4680659) B4680659
theorem B2924585 : Blo 1297967 2924585 := bstep (se 2 (by rfl) ⟨1096719, by rfl⟩ : syracuseStep 2924585 = 2193439) B2193439
theorem B27041899 : Blo 1297967 27041899 := bstep (se 1 (by rfl) ⟨20281424, by rfl⟩ : syracuseStep 27041899 = 40562849) B40562849
theorem B23699699 : Blo 1297967 23699699 := bstep (se 1 (by rfl) ⟨17774774, by rfl⟩ : syracuseStep 23699699 = 35549549) B35549549
theorem B4932035 : Blo 1297967 4932035 := bstep (se 1 (by rfl) ⟨3699026, by rfl⟩ : syracuseStep 4932035 = 7398053) B7398053
theorem B4440959 : Blo 1297967 4440959 := bstep (se 1 (by rfl) ⟨3330719, by rfl⟩ : syracuseStep 4440959 = 6661439) B6661439
theorem B25323515 : Blo 1297967 25323515 := bstep (se 1 (by rfl) ⟨18992636, by rfl⟩ : syracuseStep 25323515 = 37985273) B37985273
theorem B9865313 : Blo 1297967 9865313 := bstep (se 2 (by rfl) ⟨3699492, by rfl⟩ : syracuseStep 9865313 = 7398985) B7398985
theorem B1460335 : Blo 1297967 1460335 := bstep (se 1 (by rfl) ⟨1095251, by rfl⟩ : syracuseStep 1460335 = 2190503) B2190503
theorem B9857537 : Blo 1297967 9857537 := bstep (se 2 (by rfl) ⟨3696576, by rfl⟩ : syracuseStep 9857537 = 7393153) B7393153
theorem B1461019 : Blo 1297967 1461019 := bstep (se 1 (by rfl) ⟨1095764, by rfl⟩ : syracuseStep 1461019 = 2191529) B2191529
theorem B17787691 : Blo 1297967 17787691 := bstep (se 1 (by rfl) ⟨13340768, by rfl⟩ : syracuseStep 17787691 = 26681537) B26681537
theorem B6245201 : Blo 1297967 6245201 := bstep (se 2 (by rfl) ⟨2341950, by rfl⟩ : syracuseStep 6245201 = 4683901) B4683901
theorem B17329051 : Blo 1297967 17329051 := bstep (se 1 (by rfl) ⟨12996788, by rfl⟩ : syracuseStep 17329051 = 25993577) B25993577
theorem B7400443 : Blo 1297967 7400443 := bstep (se 1 (by rfl) ⟨5550332, by rfl⟩ : syracuseStep 7400443 = 11100665) B11100665
theorem B2632943 : Blo 1297967 2632943 := bstep (se 1 (by rfl) ⟨1974707, by rfl⟩ : syracuseStep 2632943 = 3949415) B3949415
theorem B1756399 : Blo 1297967 1756399 := bstep (se 1 (by rfl) ⟨1317299, by rfl⟩ : syracuseStep 1756399 = 2634599) B2634599
theorem B3288559 : Blo 1297967 3288559 := bstep (se 1 (by rfl) ⟨2466419, by rfl⟩ : syracuseStep 3288559 = 4932839) B4932839
theorem B1298203 : Blo 1297967 1298203 := bstep (se 1 (by rfl) ⟨973652, by rfl⟩ : syracuseStep 1298203 = 1947305) B1947305
theorem B9367571 : Blo 1297967 9367571 := bstep (se 1 (by rfl) ⟨7025678, by rfl⟩ : syracuseStep 9367571 = 14051357) B14051357
theorem B2920697 : Blo 1297967 2920697 := bstep (se 2 (by rfl) ⟨1095261, by rfl⟩ : syracuseStep 2920697 = 2190523) B2190523
theorem B1298687 : Blo 1297967 1298687 := bstep (se 1 (by rfl) ⟨974015, by rfl⟩ : syracuseStep 1298687 = 1948031) B1948031
theorem B1298759 : Blo 1297967 1298759 := bstep (se 1 (by rfl) ⟨974069, by rfl⟩ : syracuseStep 1298759 = 1948139) B1948139
theorem B4682231 : Blo 1297967 4682231 := bstep (se 1 (by rfl) ⟨3511673, by rfl⟩ : syracuseStep 4682231 = 7023347) B7023347
theorem B2339327 : Blo 1297967 2339327 := bstep (se 1 (by rfl) ⟨1754495, by rfl⟩ : syracuseStep 2339327 = 3508991) B3508991
theorem B1298991 : Blo 1297967 1298991 := bstep (se 1 (by rfl) ⟨974243, by rfl⟩ : syracuseStep 1298991 = 1948487) B1948487
theorem B2192231 : Blo 1297967 2192231 := bstep (se 1 (by rfl) ⟨1644173, by rfl⟩ : syracuseStep 2192231 = 3288347) B3288347
theorem B2192251 : Blo 1297967 2192251 := bstep (se 1 (by rfl) ⟨1644188, by rfl⟩ : syracuseStep 2192251 = 3288377) B3288377
theorem B4682863 : Blo 1297967 4682863 := bstep (se 1 (by rfl) ⟨3512147, by rfl⟩ : syracuseStep 4682863 = 7024295) B7024295
theorem B1848511 : Blo 1297967 1848511 := bstep (se 1 (by rfl) ⟨1386383, by rfl⟩ : syracuseStep 1848511 = 2772767) B2772767
theorem B11089183 : Blo 1297967 11089183 := bstep (se 1 (by rfl) ⟨8316887, by rfl⟩ : syracuseStep 11089183 = 16633775) B16633775
theorem B2921849 : Blo 1297967 2921849 := bstep (se 2 (by rfl) ⟨1095693, by rfl⟩ : syracuseStep 2921849 = 2191387) B2191387
theorem B1947119 : Blo 1297967 1947119 := bstep (se 1 (by rfl) ⟨1460339, by rfl⟩ : syracuseStep 1947119 = 2920679) B2920679
theorem B16635415 : Blo 1297967 16635415 := bstep (se 1 (by rfl) ⟨12476561, by rfl⟩ : syracuseStep 16635415 = 24953123) B24953123
theorem B1947419 : Blo 1297967 1947419 := bstep (se 1 (by rfl) ⟨1460564, by rfl⟩ : syracuseStep 1947419 = 2921129) B2921129
theorem B1644391 : Blo 1297967 1644391 := bstep (se 1 (by rfl) ⟨1233293, by rfl⟩ : syracuseStep 1644391 = 2466587) B2466587
theorem B2922407 : Blo 1297967 2922407 := bstep (se 1 (by rfl) ⟨2191805, by rfl⟩ : syracuseStep 2922407 = 4383611) B4383611
theorem B1947959 : Blo 1297967 1947959 := bstep (se 1 (by rfl) ⟨1460969, by rfl⟩ : syracuseStep 1947959 = 2921939) B2921939
theorem B1645211 : Blo 1297967 1645211 := bstep (se 1 (by rfl) ⟨1233908, by rfl⟩ : syracuseStep 1645211 = 2467817) B2467817
theorem B2923199 : Blo 1297967 2923199 := bstep (se 1 (by rfl) ⟨2192399, by rfl⟩ : syracuseStep 2923199 = 4384799) B4384799
theorem B22797227 : Blo 1297967 22797227 := bstep (se 1 (by rfl) ⟨17097920, by rfl⟩ : syracuseStep 22797227 = 34195841) B34195841
theorem B4160585 : Blo 1297967 4160585 := bstep (se 2 (by rfl) ⟨1560219, by rfl⟩ : syracuseStep 4160585 = 3120439) B3120439
theorem B160037963 : Blo 1297967 160037963 := bstep (se 1 (by rfl) ⟨120028472, by rfl⟩ : syracuseStep 160037963 = 240056945) B240056945
theorem B10132607 : Blo 1297967 10132607 := bstep (se 1 (by rfl) ⟨7599455, by rfl⟩ : syracuseStep 10132607 = 15198911) B15198911
theorem B9362729 : Blo 1297967 9362729 := bstep (se 2 (by rfl) ⟨3511023, by rfl⟩ : syracuseStep 9362729 = 7022047) B7022047
theorem B3333737 : Blo 1297967 3333737 := bstep (se 2 (by rfl) ⟨1250151, by rfl⟩ : syracuseStep 3333737 = 2500303) B2500303
theorem B2924207 : Blo 1297967 2924207 := bstep (se 1 (by rfl) ⟨2193155, by rfl⟩ : syracuseStep 2924207 = 4386311) B4386311
theorem B1949723 : Blo 1297967 1949723 := bstep (se 1 (by rfl) ⟨1462292, by rfl⟩ : syracuseStep 1949723 = 2924585) B2924585
theorem B3121487 : Blo 1297967 3121487 := bstep (se 1 (by rfl) ⟨2341115, by rfl⟩ : syracuseStep 3121487 = 4682231) B4682231
theorem B7021181 : Blo 1297967 7021181 := bstep (se 3 (by rfl) ⟨1316471, by rfl⟩ : syracuseStep 7021181 = 2632943) B2632943
theorem B6243817 : Blo 1297967 6243817 := bstep (se 2 (by rfl) ⟨2341431, by rfl⟩ : syracuseStep 6243817 = 4682863) B4682863
theorem B6571691 : Blo 1297967 6571691 := bstep (se 1 (by rfl) ⟨4928768, by rfl⟩ : syracuseStep 6571691 = 9857537) B9857537
theorem B15198151 : Blo 1297967 15198151 := bstep (se 1 (by rfl) ⟨11398613, by rfl⟩ : syracuseStep 15198151 = 22797227) B22797227
theorem B4384745 : Blo 1297967 4384745 := bstep (se 2 (by rfl) ⟨1644279, by rfl⟩ : syracuseStep 4384745 = 3288559) B3288559
theorem B2222491 : Blo 1297967 2222491 := bstep (se 1 (by rfl) ⟨1666868, by rfl⟩ : syracuseStep 2222491 = 3333737) B3333737
theorem B6245047 : Blo 1297967 6245047 := bstep (se 1 (by rfl) ⟨4683785, by rfl⟩ : syracuseStep 6245047 = 9367571) B9367571
theorem B36055865 : Blo 1297967 36055865 := bstep (se 2 (by rfl) ⟨13520949, by rfl⟩ : syracuseStep 36055865 = 27041899) B27041899
theorem B11094893 : Blo 1297967 11094893 := bstep (se 3 (by rfl) ⟨2080292, by rfl⟩ : syracuseStep 11094893 = 4160585) B4160585
theorem B3288023 : Blo 1297967 3288023 := bstep (se 1 (by rfl) ⟨2466017, by rfl⟩ : syracuseStep 3288023 = 4932035) B4932035
theorem B1461487 : Blo 1297967 1461487 := bstep (se 1 (by rfl) ⟨1096115, by rfl⟩ : syracuseStep 1461487 = 2192231) B2192231
theorem B2960639 : Blo 1297967 2960639 := bstep (se 1 (by rfl) ⟨2220479, by rfl⟩ : syracuseStep 2960639 = 4440959) B4440959
theorem B1298079 : Blo 1297967 1298079 := bstep (se 1 (by rfl) ⟨973559, by rfl⟩ : syracuseStep 1298079 = 1947119) B1947119
theorem B1298279 : Blo 1297967 1298279 := bstep (se 1 (by rfl) ⟨973709, by rfl⟩ : syracuseStep 1298279 = 1947419) B1947419
theorem B23105401 : Blo 1297967 23105401 := bstep (se 2 (by rfl) ⟨8664525, by rfl⟩ : syracuseStep 23105401 = 17329051) B17329051
theorem B9867257 : Blo 1297967 9867257 := bstep (se 2 (by rfl) ⟨3700221, by rfl⟩ : syracuseStep 9867257 = 7400443) B7400443
theorem B6238205 : Blo 1297967 6238205 := bstep (se 3 (by rfl) ⟨1169663, by rfl⟩ : syracuseStep 6238205 = 2339327) B2339327
theorem B1298639 : Blo 1297967 1298639 := bstep (se 1 (by rfl) ⟨973979, by rfl⟩ : syracuseStep 1298639 = 1947959) B1947959
theorem B94867685 : Blo 1297967 94867685 := bstep (se 4 (by rfl) ⟨8893845, by rfl⟩ : syracuseStep 94867685 = 17787691) B17787691
theorem B4387229 : Blo 1297967 4387229 := bstep (se 3 (by rfl) ⟨822605, by rfl⟩ : syracuseStep 4387229 = 1645211) B1645211
theorem B22180553 : Blo 1297967 22180553 := bstep (se 2 (by rfl) ⟨8317707, by rfl⟩ : syracuseStep 22180553 = 16635415) B16635415
theorem B6755071 : Blo 1297967 6755071 := bstep (se 1 (by rfl) ⟨5066303, by rfl⟩ : syracuseStep 6755071 = 10132607) B10132607
theorem B2192521 : Blo 1297967 2192521 := bstep (se 2 (by rfl) ⟨822195, by rfl⟩ : syracuseStep 2192521 = 1644391) B1644391
theorem B1947113 : Blo 1297967 1947113 := bstep (se 2 (by rfl) ⟨730167, by rfl⟩ : syracuseStep 1947113 = 1460335) B1460335
theorem B15799799 : Blo 1297967 15799799 := bstep (se 1 (by rfl) ⟨11849849, by rfl⟩ : syracuseStep 15799799 = 23699699) B23699699
theorem B1947131 : Blo 1297967 1947131 := bstep (se 1 (by rfl) ⟨1460348, by rfl⟩ : syracuseStep 1947131 = 2920697) B2920697
theorem B1947899 : Blo 1297967 1947899 := bstep (se 1 (by rfl) ⟨1460924, by rfl⟩ : syracuseStep 1947899 = 2921849) B2921849
theorem B1948025 : Blo 1297967 1948025 := bstep (se 2 (by rfl) ⟨730509, by rfl⟩ : syracuseStep 1948025 = 1461019) B1461019
theorem B2923001 : Blo 1297967 2923001 := bstep (se 2 (by rfl) ⟨1096125, by rfl⟩ : syracuseStep 2923001 = 2192251) B2192251
theorem B1948271 : Blo 1297967 1948271 := bstep (se 1 (by rfl) ⟨1461203, by rfl⟩ : syracuseStep 1948271 = 2922407) B2922407
theorem B16882343 : Blo 1297967 16882343 := bstep (se 1 (by rfl) ⟨12661757, by rfl⟩ : syracuseStep 16882343 = 25323515) B25323515
theorem B6576875 : Blo 1297967 6576875 := bstep (se 1 (by rfl) ⟨4932656, by rfl⟩ : syracuseStep 6576875 = 9865313) B9865313
theorem B2464681 : Blo 1297967 2464681 := bstep (se 2 (by rfl) ⟨924255, by rfl⟩ : syracuseStep 2464681 = 1848511) B1848511
theorem B2341865 : Blo 1297967 2341865 := bstep (se 2 (by rfl) ⟨878199, by rfl⟩ : syracuseStep 2341865 = 1756399) B1756399
theorem B14785577 : Blo 1297967 14785577 := bstep (se 2 (by rfl) ⟨5544591, by rfl⟩ : syracuseStep 14785577 = 11089183) B11089183
theorem B1948799 : Blo 1297967 1948799 := bstep (se 1 (by rfl) ⟨1461599, by rfl⟩ : syracuseStep 1948799 = 2923199) B2923199
theorem B106691975 : Blo 1297967 106691975 := bstep (se 1 (by rfl) ⟨80018981, by rfl⟩ : syracuseStep 106691975 = 160037963) B160037963
theorem B6241819 : Blo 1297967 6241819 := bstep (se 1 (by rfl) ⟨4681364, by rfl⟩ : syracuseStep 6241819 = 9362729) B9362729
theorem B16653869 : Blo 1297967 16653869 := bstep (se 3 (by rfl) ⟨3122600, by rfl⟩ : syracuseStep 16653869 = 6245201) B6245201
theorem B1949471 : Blo 1297967 1949471 := bstep (se 1 (by rfl) ⟨1462103, by rfl⟩ : syracuseStep 1949471 = 2924207) B2924207
theorem B2080991 : Blo 1297967 2080991 := bstep (se 1 (by rfl) ⟨1560743, by rfl⟩ : syracuseStep 2080991 = 3121487) B3121487
theorem B2924819 : Blo 1297967 2924819 := bstep (se 1 (by rfl) ⟨2193614, by rfl⟩ : syracuseStep 2924819 = 4387229) B4387229
theorem B14787035 : Blo 1297967 14787035 := bstep (se 1 (by rfl) ⟨11090276, by rfl⟩ : syracuseStep 14787035 = 22180553) B22180553
theorem B3286241 : Blo 1297967 3286241 := bstep (se 2 (by rfl) ⟨1232340, by rfl⟩ : syracuseStep 3286241 = 2464681) B2464681
theorem B42132797 : Blo 1297967 42132797 := bstep (se 3 (by rfl) ⟨7899899, by rfl⟩ : syracuseStep 42132797 = 15799799) B15799799
theorem B4384583 : Blo 1297967 4384583 := bstep (se 1 (by rfl) ⟨3288437, by rfl⟩ : syracuseStep 4384583 = 6576875) B6576875
theorem B24037243 : Blo 1297967 24037243 := bstep (se 1 (by rfl) ⟨18027932, by rfl⟩ : syracuseStep 24037243 = 36055865) B36055865
theorem B8325089 : Blo 1297967 8325089 := bstep (se 2 (by rfl) ⟨3121908, by rfl⟩ : syracuseStep 8325089 = 6243817) B6243817
theorem B9857051 : Blo 1297967 9857051 := bstep (se 1 (by rfl) ⟨7392788, by rfl⟩ : syracuseStep 9857051 = 14785577) B14785577
theorem B11102579 : Blo 1297967 11102579 := bstep (se 1 (by rfl) ⟨8326934, by rfl⟩ : syracuseStep 11102579 = 16653869) B16653869
theorem B63245123 : Blo 1297967 63245123 := bstep (se 1 (by rfl) ⟨47433842, by rfl⟩ : syracuseStep 63245123 = 94867685) B94867685
theorem B8326729 : Blo 1297967 8326729 := bstep (se 2 (by rfl) ⟨3122523, by rfl⟩ : syracuseStep 8326729 = 6245047) B6245047
theorem B1298075 : Blo 1297967 1298075 := bstep (se 1 (by rfl) ⟨973556, by rfl⟩ : syracuseStep 1298075 = 1947113) B1947113
theorem B1298087 : Blo 1297967 1298087 := bstep (se 1 (by rfl) ⟨973565, by rfl⟩ : syracuseStep 1298087 = 1947131) B1947131
theorem B9006761 : Blo 1297967 9006761 := bstep (se 2 (by rfl) ⟨3377535, by rfl⟩ : syracuseStep 9006761 = 6755071) B6755071
theorem B1298599 : Blo 1297967 1298599 := bstep (se 1 (by rfl) ⟨973949, by rfl⟩ : syracuseStep 1298599 = 1947899) B1947899
theorem B1298683 : Blo 1297967 1298683 := bstep (se 1 (by rfl) ⟨974012, by rfl⟩ : syracuseStep 1298683 = 1948025) B1948025
theorem B18723149 : Blo 1297967 18723149 := bstep (se 3 (by rfl) ⟨3510590, by rfl⟩ : syracuseStep 18723149 = 7021181) B7021181
theorem B1298847 : Blo 1297967 1298847 := bstep (se 1 (by rfl) ⟨974135, by rfl⟩ : syracuseStep 1298847 = 1948271) B1948271
theorem B123228805 : Blo 1297967 123228805 := bstep (se 4 (by rfl) ⟨11552700, by rfl⟩ : syracuseStep 123228805 = 23105401) B23105401
theorem B2192015 : Blo 1297967 2192015 := bstep (se 1 (by rfl) ⟨1644011, by rfl⟩ : syracuseStep 2192015 = 3288023) B3288023
theorem B1561243 : Blo 1297967 1561243 := bstep (se 1 (by rfl) ⟨1170932, by rfl⟩ : syracuseStep 1561243 = 2341865) B2341865
theorem B1299199 : Blo 1297967 1299199 := bstep (se 1 (by rfl) ⟨974399, by rfl⟩ : syracuseStep 1299199 = 1948799) B1948799
theorem B71127983 : Blo 1297967 71127983 := bstep (se 1 (by rfl) ⟨53345987, by rfl⟩ : syracuseStep 71127983 = 106691975) B106691975
theorem B1299647 : Blo 1297967 1299647 := bstep (se 1 (by rfl) ⟨974735, by rfl⟩ : syracuseStep 1299647 = 1949471) B1949471
theorem B20264201 : Blo 1297967 20264201 := bstep (se 2 (by rfl) ⟨7599075, by rfl⟩ : syracuseStep 20264201 = 15198151) B15198151
theorem B4158803 : Blo 1297967 4158803 := bstep (se 1 (by rfl) ⟨3119102, by rfl⟩ : syracuseStep 4158803 = 6238205) B6238205
theorem B1299815 : Blo 1297967 1299815 := bstep (se 1 (by rfl) ⟨974861, by rfl⟩ : syracuseStep 1299815 = 1949723) B1949723
theorem B2963321 : Blo 1297967 2963321 := bstep (se 2 (by rfl) ⟨1111245, by rfl⟩ : syracuseStep 2963321 = 2222491) B2222491
theorem B4381127 : Blo 1297967 4381127 := bstep (se 1 (by rfl) ⟨3285845, by rfl⟩ : syracuseStep 4381127 = 6571691) B6571691
theorem B2923163 : Blo 1297967 2923163 := bstep (se 1 (by rfl) ⟨2192372, by rfl⟩ : syracuseStep 2923163 = 4384745) B4384745
theorem B2923361 : Blo 1297967 2923361 := bstep (se 2 (by rfl) ⟨1096260, by rfl⟩ : syracuseStep 2923361 = 2192521) B2192521
theorem B1948649 : Blo 1297967 1948649 := bstep (se 2 (by rfl) ⟨730743, by rfl⟩ : syracuseStep 1948649 = 1461487) B1461487
theorem B1948667 : Blo 1297967 1948667 := bstep (se 1 (by rfl) ⟨1461500, by rfl⟩ : syracuseStep 1948667 = 2923001) B2923001
theorem B11254895 : Blo 1297967 11254895 := bstep (se 1 (by rfl) ⟨8441171, by rfl⟩ : syracuseStep 11254895 = 16882343) B16882343
theorem B7396595 : Blo 1297967 7396595 := bstep (se 1 (by rfl) ⟨5547446, by rfl⟩ : syracuseStep 7396595 = 11094893) B11094893
theorem B8322425 : Blo 1297967 8322425 := bstep (se 2 (by rfl) ⟨3120909, by rfl⟩ : syracuseStep 8322425 = 6241819) B6241819
theorem B1973759 : Blo 1297967 1973759 := bstep (se 1 (by rfl) ⟨1480319, by rfl⟩ : syracuseStep 1973759 = 2960639) B2960639
theorem B6578171 : Blo 1297967 6578171 := bstep (se 1 (by rfl) ⟨4933628, by rfl⟩ : syracuseStep 6578171 = 9867257) B9867257
theorem B1949879 : Blo 1297967 1949879 := bstep (se 1 (by rfl) ⟨1462409, by rfl⟩ : syracuseStep 1949879 = 2924819) B2924819
theorem B13509467 : Blo 1297967 13509467 := bstep (se 1 (by rfl) ⟨10132100, by rfl⟩ : syracuseStep 13509467 = 20264201) B20264201
theorem B2081657 : Blo 1297967 2081657 := bstep (se 2 (by rfl) ⟨780621, by rfl⟩ : syracuseStep 2081657 = 1561243) B1561243
theorem B1975547 : Blo 1297967 1975547 := bstep (se 1 (by rfl) ⟨1481660, by rfl⟩ : syracuseStep 1975547 = 2963321) B2963321
theorem B6571367 : Blo 1297967 6571367 := bstep (se 1 (by rfl) ⟨4928525, by rfl⟩ : syracuseStep 6571367 = 9857051) B9857051
theorem B128198629 : Blo 1297967 128198629 := bstep (se 4 (by rfl) ⟨12018621, by rfl⟩ : syracuseStep 128198629 = 24037243) B24037243
theorem B11102305 : Blo 1297967 11102305 := bstep (se 2 (by rfl) ⟨4163364, by rfl⟩ : syracuseStep 11102305 = 8326729) B8326729
theorem B5548283 : Blo 1297967 5548283 := bstep (se 1 (by rfl) ⟨4161212, by rfl⟩ : syracuseStep 5548283 = 8322425) B8322425
theorem B4385447 : Blo 1297967 4385447 := bstep (se 1 (by rfl) ⟨3289085, by rfl⟩ : syracuseStep 4385447 = 6578171) B6578171
theorem B9858023 : Blo 1297967 9858023 := bstep (se 1 (by rfl) ⟨7393517, by rfl⟩ : syracuseStep 9858023 = 14787035) B14787035
theorem B1461343 : Blo 1297967 1461343 := bstep (se 1 (by rfl) ⟨1096007, by rfl⟩ : syracuseStep 1461343 = 2192015) B2192015
theorem B5549309 : Blo 1297967 5549309 := bstep (se 3 (by rfl) ⟨1040495, by rfl⟩ : syracuseStep 5549309 = 2080991) B2080991
theorem B47418655 : Blo 1297967 47418655 := bstep (se 1 (by rfl) ⟨35563991, by rfl⟩ : syracuseStep 47418655 = 71127983) B71127983
theorem B2190827 : Blo 1297967 2190827 := bstep (se 1 (by rfl) ⟨1643120, by rfl⟩ : syracuseStep 2190827 = 3286241) B3286241
theorem B5550059 : Blo 1297967 5550059 := bstep (se 1 (by rfl) ⟨4162544, by rfl⟩ : syracuseStep 5550059 = 8325089) B8325089
theorem B7401719 : Blo 1297967 7401719 := bstep (se 1 (by rfl) ⟨5551289, by rfl⟩ : syracuseStep 7401719 = 11102579) B11102579
theorem B2920751 : Blo 1297967 2920751 := bstep (se 1 (by rfl) ⟨2190563, by rfl⟩ : syracuseStep 2920751 = 4381127) B4381127
theorem B1299099 : Blo 1297967 1299099 := bstep (se 1 (by rfl) ⟨974324, by rfl⟩ : syracuseStep 1299099 = 1948649) B1948649
theorem B1299111 : Blo 1297967 1299111 := bstep (se 1 (by rfl) ⟨974333, by rfl⟩ : syracuseStep 1299111 = 1948667) B1948667
theorem B12482099 : Blo 1297967 12482099 := bstep (se 1 (by rfl) ⟨9361574, by rfl⟩ : syracuseStep 12482099 = 18723149) B18723149
theorem B164305073 : Blo 1297967 164305073 := bstep (se 2 (by rfl) ⟨61614402, by rfl⟩ : syracuseStep 164305073 = 123228805) B123228805
theorem B28088531 : Blo 1297967 28088531 := bstep (se 1 (by rfl) ⟨21066398, by rfl⟩ : syracuseStep 28088531 = 42132797) B42132797
theorem B11090141 : Blo 1297967 11090141 := bstep (se 3 (by rfl) ⟨2079401, by rfl⟩ : syracuseStep 11090141 = 4158803) B4158803
theorem B2923055 : Blo 1297967 2923055 := bstep (se 1 (by rfl) ⟨2192291, by rfl⟩ : syracuseStep 2923055 = 4384583) B4384583
theorem B1948775 : Blo 1297967 1948775 := bstep (se 1 (by rfl) ⟨1461581, by rfl⟩ : syracuseStep 1948775 = 2923163) B2923163
theorem B42163415 : Blo 1297967 42163415 := bstep (se 1 (by rfl) ⟨31622561, by rfl⟩ : syracuseStep 42163415 = 63245123) B63245123
theorem B1948907 : Blo 1297967 1948907 := bstep (se 1 (by rfl) ⟨1461680, by rfl⟩ : syracuseStep 1948907 = 2923361) B2923361
theorem B7503263 : Blo 1297967 7503263 := bstep (se 1 (by rfl) ⟨5627447, by rfl⟩ : syracuseStep 7503263 = 11254895) B11254895
theorem B4931063 : Blo 1297967 4931063 := bstep (se 1 (by rfl) ⟨3698297, by rfl⟩ : syracuseStep 4931063 = 7396595) B7396595
theorem B6004507 : Blo 1297967 6004507 := bstep (se 1 (by rfl) ⟨4503380, by rfl⟩ : syracuseStep 6004507 = 9006761) B9006761
theorem B21053429 : Blo 1297967 21053429 := bstep (se 5 (by rfl) ⟨986879, by rfl⟩ : syracuseStep 21053429 = 1973759) B1973759
theorem B14803073 : Blo 1297967 14803073 := bstep (se 2 (by rfl) ⟨5551152, by rfl⟩ : syracuseStep 14803073 = 11102305) B11102305
theorem B5268125 : Blo 1297967 5268125 := bstep (se 3 (by rfl) ⟨987773, by rfl⟩ : syracuseStep 5268125 = 1975547) B1975547
theorem B109536715 : Blo 1297967 109536715 := bstep (se 1 (by rfl) ⟨82152536, by rfl⟩ : syracuseStep 109536715 = 164305073) B164305073
theorem B6572015 : Blo 1297967 6572015 := bstep (se 1 (by rfl) ⟨4929011, by rfl⟩ : syracuseStep 6572015 = 9858023) B9858023
theorem B28108943 : Blo 1297967 28108943 := bstep (se 1 (by rfl) ⟨21081707, by rfl⟩ : syracuseStep 28108943 = 42163415) B42163415
theorem B1460551 : Blo 1297967 1460551 := bstep (se 1 (by rfl) ⟨1095413, by rfl⟩ : syracuseStep 1460551 = 2190827) B2190827
theorem B3287375 : Blo 1297967 3287375 := bstep (se 1 (by rfl) ⟨2465531, by rfl⟩ : syracuseStep 3287375 = 4931063) B4931063
theorem B8006009 : Blo 1297967 8006009 := bstep (se 2 (by rfl) ⟨3002253, by rfl⟩ : syracuseStep 8006009 = 6004507) B6004507
theorem B14035619 : Blo 1297967 14035619 := bstep (se 1 (by rfl) ⟨10526714, by rfl⟩ : syracuseStep 14035619 = 21053429) B21053429
theorem B4934479 : Blo 1297967 4934479 := bstep (se 1 (by rfl) ⟨3700859, by rfl⟩ : syracuseStep 4934479 = 7401719) B7401719
theorem B9006311 : Blo 1297967 9006311 := bstep (se 1 (by rfl) ⟨6754733, by rfl⟩ : syracuseStep 9006311 = 13509467) B13509467
theorem B7393427 : Blo 1297967 7393427 := bstep (se 1 (by rfl) ⟨5545070, by rfl⟩ : syracuseStep 7393427 = 11090141) B11090141
theorem B3698855 : Blo 1297967 3698855 := bstep (se 1 (by rfl) ⟨2774141, by rfl⟩ : syracuseStep 3698855 = 5548283) B5548283
theorem B1299183 : Blo 1297967 1299183 := bstep (se 1 (by rfl) ⟨974387, by rfl⟩ : syracuseStep 1299183 = 1948775) B1948775
theorem B1299271 : Blo 1297967 1299271 := bstep (se 1 (by rfl) ⟨974453, by rfl⟩ : syracuseStep 1299271 = 1948907) B1948907
theorem B3699539 : Blo 1297967 3699539 := bstep (se 1 (by rfl) ⟨2774654, by rfl⟩ : syracuseStep 3699539 = 5549309) B5549309
theorem B5002175 : Blo 1297967 5002175 := bstep (se 1 (by rfl) ⟨3751631, by rfl⟩ : syracuseStep 5002175 = 7503263) B7503263
theorem B5551085 : Blo 1297967 5551085 := bstep (se 3 (by rfl) ⟨1040828, by rfl⟩ : syracuseStep 5551085 = 2081657) B2081657
theorem B14800157 : Blo 1297967 14800157 := bstep (se 3 (by rfl) ⟨2775029, by rfl⟩ : syracuseStep 14800157 = 5550059) B5550059
theorem B170931505 : Blo 1297967 170931505 := bstep (se 2 (by rfl) ⟨64099314, by rfl⟩ : syracuseStep 170931505 = 128198629) B128198629
theorem B1299919 : Blo 1297967 1299919 := bstep (se 1 (by rfl) ⟨974939, by rfl⟩ : syracuseStep 1299919 = 1949879) B1949879
theorem B1947167 : Blo 1297967 1947167 := bstep (se 1 (by rfl) ⟨1460375, by rfl⟩ : syracuseStep 1947167 = 2920751) B2920751
theorem B4380911 : Blo 1297967 4380911 := bstep (se 1 (by rfl) ⟨3285683, by rfl⟩ : syracuseStep 4380911 = 6571367) B6571367
theorem B8321399 : Blo 1297967 8321399 := bstep (se 1 (by rfl) ⟨6241049, by rfl⟩ : syracuseStep 8321399 = 12482099) B12482099
theorem B1948457 : Blo 1297967 1948457 := bstep (se 2 (by rfl) ⟨730671, by rfl⟩ : syracuseStep 1948457 = 1461343) B1461343
theorem B18725687 : Blo 1297967 18725687 := bstep (se 1 (by rfl) ⟨14044265, by rfl⟩ : syracuseStep 18725687 = 28088531) B28088531
theorem B1948703 : Blo 1297967 1948703 := bstep (se 1 (by rfl) ⟨1461527, by rfl⟩ : syracuseStep 1948703 = 2923055) B2923055
theorem B63224873 : Blo 1297967 63224873 := bstep (se 2 (by rfl) ⟨23709327, by rfl⟩ : syracuseStep 63224873 = 47418655) B47418655
theorem B2923631 : Blo 1297967 2923631 := bstep (se 1 (by rfl) ⟨2192723, by rfl⟩ : syracuseStep 2923631 = 4385447) B4385447
theorem B2465903 : Blo 1297967 2465903 := bstep (se 1 (by rfl) ⟨1849427, by rfl⟩ : syracuseStep 2465903 = 3698855) B3698855
theorem B2466359 : Blo 1297967 2466359 := bstep (se 1 (by rfl) ⟨1849769, by rfl⟩ : syracuseStep 2466359 = 3699539) B3699539
theorem B3334783 : Blo 1297967 3334783 := bstep (se 1 (by rfl) ⟨2501087, by rfl⟩ : syracuseStep 3334783 = 5002175) B5002175
theorem B6579305 : Blo 1297967 6579305 := bstep (se 2 (by rfl) ⟨2467239, by rfl⟩ : syracuseStep 6579305 = 4934479) B4934479
theorem B5547599 : Blo 1297967 5547599 := bstep (se 1 (by rfl) ⟨4160699, by rfl⟩ : syracuseStep 5547599 = 8321399) B8321399
theorem B9357079 : Blo 1297967 9357079 := bstep (se 1 (by rfl) ⟨7017809, by rfl⟩ : syracuseStep 9357079 = 14035619) B14035619
theorem B146048953 : Blo 1297967 146048953 := bstep (se 2 (by rfl) ⟨54768357, by rfl⟩ : syracuseStep 146048953 = 109536715) B109536715
theorem B42149915 : Blo 1297967 42149915 := bstep (se 1 (by rfl) ⟨31612436, by rfl⟩ : syracuseStep 42149915 = 63224873) B63224873
theorem B9866771 : Blo 1297967 9866771 := bstep (se 1 (by rfl) ⟨7400078, by rfl⟩ : syracuseStep 9866771 = 14800157) B14800157
theorem B1298111 : Blo 1297967 1298111 := bstep (se 1 (by rfl) ⟨973583, by rfl⟩ : syracuseStep 1298111 = 1947167) B1947167
theorem B85397429 : Blo 1297967 85397429 := bstep (se 5 (by rfl) ⟨4003004, by rfl⟩ : syracuseStep 85397429 = 8006009) B8006009
theorem B18739295 : Blo 1297967 18739295 := bstep (se 1 (by rfl) ⟨14054471, by rfl⟩ : syracuseStep 18739295 = 28108943) B28108943
theorem B2920607 : Blo 1297967 2920607 := bstep (se 1 (by rfl) ⟨2190455, by rfl⟩ : syracuseStep 2920607 = 4380911) B4380911
theorem B2191583 : Blo 1297967 2191583 := bstep (se 1 (by rfl) ⟨1643687, by rfl⟩ : syracuseStep 2191583 = 3287375) B3287375
theorem B1298971 : Blo 1297967 1298971 := bstep (se 1 (by rfl) ⟨974228, by rfl⟩ : syracuseStep 1298971 = 1948457) B1948457
theorem B1299135 : Blo 1297967 1299135 := bstep (se 1 (by rfl) ⟨974351, by rfl⟩ : syracuseStep 1299135 = 1948703) B1948703
theorem B9868715 : Blo 1297967 9868715 := bstep (se 1 (by rfl) ⟨7401536, by rfl⟩ : syracuseStep 9868715 = 14803073) B14803073
theorem B4928951 : Blo 1297967 4928951 := bstep (se 1 (by rfl) ⟨3696713, by rfl⟩ : syracuseStep 4928951 = 7393427) B7393427
theorem B1947401 : Blo 1297967 1947401 := bstep (se 2 (by rfl) ⟨730275, by rfl⟩ : syracuseStep 1947401 = 1460551) B1460551
theorem B3512083 : Blo 1297967 3512083 := bstep (se 1 (by rfl) ⟨2634062, by rfl⟩ : syracuseStep 3512083 = 5268125) B5268125
theorem B3700723 : Blo 1297967 3700723 := bstep (se 1 (by rfl) ⟨2775542, by rfl⟩ : syracuseStep 3700723 = 5551085) B5551085
theorem B4381343 : Blo 1297967 4381343 := bstep (se 1 (by rfl) ⟨3286007, by rfl⟩ : syracuseStep 4381343 = 6572015) B6572015
theorem B227908673 : Blo 1297967 227908673 := bstep (se 2 (by rfl) ⟨85465752, by rfl⟩ : syracuseStep 227908673 = 170931505) B170931505
theorem B12483791 : Blo 1297967 12483791 := bstep (se 1 (by rfl) ⟨9362843, by rfl⟩ : syracuseStep 12483791 = 18725687) B18725687
theorem B1949087 : Blo 1297967 1949087 := bstep (se 1 (by rfl) ⟨1461815, by rfl⟩ : syracuseStep 1949087 = 2923631) B2923631
theorem B6004207 : Blo 1297967 6004207 := bstep (se 1 (by rfl) ⟨4503155, by rfl⟩ : syracuseStep 6004207 = 9006311) B9006311
theorem B12492863 : Blo 1297967 12492863 := bstep (se 1 (by rfl) ⟨9369647, by rfl⟩ : syracuseStep 12492863 = 18739295) B18739295
theorem B6579143 : Blo 1297967 6579143 := bstep (se 1 (by rfl) ⟨4934357, by rfl⟩ : syracuseStep 6579143 = 9868715) B9868715
theorem B3285967 : Blo 1297967 3285967 := bstep (se 1 (by rfl) ⟨2464475, by rfl⟩ : syracuseStep 3285967 = 4928951) B4928951
theorem B28099943 : Blo 1297967 28099943 := bstep (se 1 (by rfl) ⟨21074957, by rfl⟩ : syracuseStep 28099943 = 42149915) B42149915
theorem B8005609 : Blo 1297967 8005609 := bstep (se 2 (by rfl) ⟨3002103, by rfl⟩ : syracuseStep 8005609 = 6004207) B6004207
theorem B151939115 : Blo 1297967 151939115 := bstep (se 1 (by rfl) ⟨113954336, by rfl⟩ : syracuseStep 151939115 = 227908673) B227908673
theorem B4934297 : Blo 1297967 4934297 := bstep (se 2 (by rfl) ⟨1850361, by rfl⟩ : syracuseStep 4934297 = 3700723) B3700723
theorem B1461055 : Blo 1297967 1461055 := bstep (se 1 (by rfl) ⟨1095791, by rfl⟩ : syracuseStep 1461055 = 2191583) B2191583
theorem B4386203 : Blo 1297967 4386203 := bstep (se 1 (by rfl) ⟨3289652, by rfl⟩ : syracuseStep 4386203 = 6579305) B6579305
theorem B3698399 : Blo 1297967 3698399 := bstep (se 1 (by rfl) ⟨2773799, by rfl⟩ : syracuseStep 3698399 = 5547599) B5547599
theorem B1298267 : Blo 1297967 1298267 := bstep (se 1 (by rfl) ⟨973700, by rfl⟩ : syracuseStep 1298267 = 1947401) B1947401
theorem B2920895 : Blo 1297967 2920895 := bstep (se 1 (by rfl) ⟨2190671, by rfl⟩ : syracuseStep 2920895 = 4381343) B4381343
theorem B1299391 : Blo 1297967 1299391 := bstep (se 1 (by rfl) ⟨974543, by rfl⟩ : syracuseStep 1299391 = 1949087) B1949087
theorem B4682777 : Blo 1297967 4682777 := bstep (se 2 (by rfl) ⟨1756041, by rfl⟩ : syracuseStep 4682777 = 3512083) B3512083
theorem B56931619 : Blo 1297967 56931619 := bstep (se 1 (by rfl) ⟨42698714, by rfl⟩ : syracuseStep 56931619 = 85397429) B85397429
theorem B1947071 : Blo 1297967 1947071 := bstep (se 1 (by rfl) ⟨1460303, by rfl⟩ : syracuseStep 1947071 = 2920607) B2920607
theorem B6575741 : Blo 1297967 6575741 := bstep (se 3 (by rfl) ⟨1232951, by rfl⟩ : syracuseStep 6575741 = 2465903) B2465903
theorem B1644239 : Blo 1297967 1644239 := bstep (se 1 (by rfl) ⟨1233179, by rfl⟩ : syracuseStep 1644239 = 2466359) B2466359
theorem B4446377 : Blo 1297967 4446377 := bstep (se 2 (by rfl) ⟨1667391, by rfl⟩ : syracuseStep 4446377 = 3334783) B3334783
theorem B8322527 : Blo 1297967 8322527 := bstep (se 1 (by rfl) ⟨6241895, by rfl⟩ : syracuseStep 8322527 = 12483791) B12483791
theorem B6577847 : Blo 1297967 6577847 := bstep (se 1 (by rfl) ⟨4933385, by rfl⟩ : syracuseStep 6577847 = 9866771) B9866771
theorem B12476105 : Blo 1297967 12476105 := bstep (se 2 (by rfl) ⟨4678539, by rfl⟩ : syracuseStep 12476105 = 9357079) B9357079
theorem B194731937 : Blo 1297967 194731937 := bstep (se 2 (by rfl) ⟨73024476, by rfl⟩ : syracuseStep 194731937 = 146048953) B146048953
theorem B4383827 : Blo 1297967 4383827 := bstep (se 1 (by rfl) ⟨3287870, by rfl⟩ : syracuseStep 4383827 = 6575741) B6575741
theorem B75908825 : Blo 1297967 75908825 := bstep (se 2 (by rfl) ⟨28465809, by rfl⟩ : syracuseStep 75908825 = 56931619) B56931619
theorem B4384637 : Blo 1297967 4384637 := bstep (se 3 (by rfl) ⟨822119, by rfl⟩ : syracuseStep 4384637 = 1644239) B1644239
theorem B5548351 : Blo 1297967 5548351 := bstep (se 1 (by rfl) ⟨4161263, by rfl⟩ : syracuseStep 5548351 = 8322527) B8322527
theorem B4385231 : Blo 1297967 4385231 := bstep (se 1 (by rfl) ⟨3288923, by rfl⟩ : syracuseStep 4385231 = 6577847) B6577847
theorem B8317403 : Blo 1297967 8317403 := bstep (se 1 (by rfl) ⟨6238052, by rfl⟩ : syracuseStep 8317403 = 12476105) B12476105
theorem B129821291 : Blo 1297967 129821291 := bstep (se 1 (by rfl) ⟨97365968, by rfl⟩ : syracuseStep 129821291 = 194731937) B194731937
theorem B12487405 : Blo 1297967 12487405 := bstep (se 3 (by rfl) ⟨2341388, by rfl⟩ : syracuseStep 12487405 = 4682777) B4682777
theorem B4386095 : Blo 1297967 4386095 := bstep (se 1 (by rfl) ⟨3289571, by rfl⟩ : syracuseStep 4386095 = 6579143) B6579143
theorem B1298047 : Blo 1297967 1298047 := bstep (se 1 (by rfl) ⟨973535, by rfl⟩ : syracuseStep 1298047 = 1947071) B1947071
theorem B3289531 : Blo 1297967 3289531 := bstep (se 1 (by rfl) ⟨2467148, by rfl⟩ : syracuseStep 3289531 = 4934297) B4934297
theorem B8328575 : Blo 1297967 8328575 := bstep (se 1 (by rfl) ⟨6246431, by rfl⟩ : syracuseStep 8328575 = 12492863) B12492863
theorem B1947263 : Blo 1297967 1947263 := bstep (se 1 (by rfl) ⟨1460447, by rfl⟩ : syracuseStep 1947263 = 2920895) B2920895
theorem B18733295 : Blo 1297967 18733295 := bstep (se 1 (by rfl) ⟨14049971, by rfl⟩ : syracuseStep 18733295 = 28099943) B28099943
theorem B1948073 : Blo 1297967 1948073 := bstep (se 2 (by rfl) ⟨730527, by rfl⟩ : syracuseStep 1948073 = 1461055) B1461055
theorem B4381289 : Blo 1297967 4381289 := bstep (se 2 (by rfl) ⟨1642983, by rfl⟩ : syracuseStep 4381289 = 3285967) B3285967
theorem B101292743 : Blo 1297967 101292743 := bstep (se 1 (by rfl) ⟨75969557, by rfl⟩ : syracuseStep 101292743 = 151939115) B151939115
theorem B2964251 : Blo 1297967 2964251 := bstep (se 1 (by rfl) ⟨2223188, by rfl⟩ : syracuseStep 2964251 = 4446377) B4446377
theorem B9862397 : Blo 1297967 9862397 := bstep (se 3 (by rfl) ⟨1849199, by rfl⟩ : syracuseStep 9862397 = 3698399) B3698399
theorem B2924135 : Blo 1297967 2924135 := bstep (se 1 (by rfl) ⟨2193101, by rfl⟩ : syracuseStep 2924135 = 4386203) B4386203
theorem B10674145 : Blo 1297967 10674145 := bstep (se 2 (by rfl) ⟨4002804, by rfl⟩ : syracuseStep 10674145 = 8005609) B8005609
theorem B7397801 : Blo 1297967 7397801 := bstep (se 2 (by rfl) ⟨2774175, by rfl⟩ : syracuseStep 7397801 = 5548351) B5548351
theorem B49955453 : Blo 1297967 49955453 := bstep (se 3 (by rfl) ⟨9366647, by rfl⟩ : syracuseStep 49955453 = 18733295) B18733295
theorem B67528495 : Blo 1297967 67528495 := bstep (se 1 (by rfl) ⟨50646371, by rfl⟩ : syracuseStep 67528495 = 101292743) B101292743
theorem B1976167 : Blo 1297967 1976167 := bstep (se 1 (by rfl) ⟨1482125, by rfl⟩ : syracuseStep 1976167 = 2964251) B2964251
theorem B14232193 : Blo 1297967 14232193 := bstep (se 2 (by rfl) ⟨5337072, by rfl⟩ : syracuseStep 14232193 = 10674145) B10674145
theorem B4386041 : Blo 1297967 4386041 := bstep (se 2 (by rfl) ⟨1644765, by rfl⟩ : syracuseStep 4386041 = 3289531) B3289531
theorem B16649873 : Blo 1297967 16649873 := bstep (se 2 (by rfl) ⟨6243702, by rfl⟩ : syracuseStep 16649873 = 12487405) B12487405
theorem B1298175 : Blo 1297967 1298175 := bstep (se 1 (by rfl) ⟨973631, by rfl⟩ : syracuseStep 1298175 = 1947263) B1947263
theorem B50605883 : Blo 1297967 50605883 := bstep (se 1 (by rfl) ⟨37954412, by rfl⟩ : syracuseStep 50605883 = 75908825) B75908825
theorem B1298715 : Blo 1297967 1298715 := bstep (se 1 (by rfl) ⟨974036, by rfl⟩ : syracuseStep 1298715 = 1948073) B1948073
theorem B2920859 : Blo 1297967 2920859 := bstep (se 1 (by rfl) ⟨2190644, by rfl⟩ : syracuseStep 2920859 = 4381289) B4381289
theorem B6574931 : Blo 1297967 6574931 := bstep (se 1 (by rfl) ⟨4931198, by rfl⟩ : syracuseStep 6574931 = 9862397) B9862397
theorem B2922551 : Blo 1297967 2922551 := bstep (se 1 (by rfl) ⟨2191913, by rfl⟩ : syracuseStep 2922551 = 4383827) B4383827
theorem B5552383 : Blo 1297967 5552383 := bstep (se 1 (by rfl) ⟨4164287, by rfl⟩ : syracuseStep 5552383 = 8328575) B8328575
theorem B2923091 : Blo 1297967 2923091 := bstep (se 1 (by rfl) ⟨2192318, by rfl⟩ : syracuseStep 2923091 = 4384637) B4384637
theorem B2923487 : Blo 1297967 2923487 := bstep (se 1 (by rfl) ⟨2192615, by rfl⟩ : syracuseStep 2923487 = 4385231) B4385231
theorem B5544935 : Blo 1297967 5544935 := bstep (se 1 (by rfl) ⟨4158701, by rfl⟩ : syracuseStep 5544935 = 8317403) B8317403
theorem B86547527 : Blo 1297967 86547527 := bstep (se 1 (by rfl) ⟨64910645, by rfl⟩ : syracuseStep 86547527 = 129821291) B129821291
theorem B2924063 : Blo 1297967 2924063 := bstep (se 1 (by rfl) ⟨2193047, by rfl⟩ : syracuseStep 2924063 = 4386095) B4386095
theorem B1949423 : Blo 1297967 1949423 := bstep (se 1 (by rfl) ⟨1462067, by rfl⟩ : syracuseStep 1949423 = 2924135) B2924135
theorem B4931867 : Blo 1297967 4931867 := bstep (se 1 (by rfl) ⟨3698900, by rfl⟩ : syracuseStep 4931867 = 7397801) B7397801
theorem B4383287 : Blo 1297967 4383287 := bstep (se 1 (by rfl) ⟨3287465, by rfl⟩ : syracuseStep 4383287 = 6574931) B6574931
theorem B3696623 : Blo 1297967 3696623 := bstep (se 1 (by rfl) ⟨2772467, by rfl⟩ : syracuseStep 3696623 = 5544935) B5544935
theorem B57698351 : Blo 1297967 57698351 := bstep (se 1 (by rfl) ⟨43273763, by rfl⟩ : syracuseStep 57698351 = 86547527) B86547527
theorem B33737255 : Blo 1297967 33737255 := bstep (se 1 (by rfl) ⟨25302941, by rfl⟩ : syracuseStep 33737255 = 50605883) B50605883
theorem B33303635 : Blo 1297967 33303635 := bstep (se 1 (by rfl) ⟨24977726, by rfl⟩ : syracuseStep 33303635 = 49955453) B49955453
theorem B10539557 : Blo 1297967 10539557 := bstep (se 4 (by rfl) ⟨988083, by rfl⟩ : syracuseStep 10539557 = 1976167) B1976167
theorem B1299615 : Blo 1297967 1299615 := bstep (se 1 (by rfl) ⟨974711, by rfl⟩ : syracuseStep 1299615 = 1949423) B1949423
theorem B1947239 : Blo 1297967 1947239 := bstep (se 1 (by rfl) ⟨1460429, by rfl⟩ : syracuseStep 1947239 = 2920859) B2920859
theorem B7403177 : Blo 1297967 7403177 := bstep (se 2 (by rfl) ⟨2776191, by rfl⟩ : syracuseStep 7403177 = 5552383) B5552383
theorem B75905029 : Blo 1297967 75905029 := bstep (se 4 (by rfl) ⟨7116096, by rfl⟩ : syracuseStep 75905029 = 14232193) B14232193
theorem B1948367 : Blo 1297967 1948367 := bstep (se 1 (by rfl) ⟨1461275, by rfl⟩ : syracuseStep 1948367 = 2922551) B2922551
theorem B1948727 : Blo 1297967 1948727 := bstep (se 1 (by rfl) ⟨1461545, by rfl⟩ : syracuseStep 1948727 = 2923091) B2923091
theorem B1948991 : Blo 1297967 1948991 := bstep (se 1 (by rfl) ⟨1461743, by rfl⟩ : syracuseStep 1948991 = 2923487) B2923487
theorem B2924027 : Blo 1297967 2924027 := bstep (se 1 (by rfl) ⟨2193020, by rfl⟩ : syracuseStep 2924027 = 4386041) B4386041
theorem B1949375 : Blo 1297967 1949375 := bstep (se 1 (by rfl) ⟨1462031, by rfl⟩ : syracuseStep 1949375 = 2924063) B2924063
theorem B90037993 : Blo 1297967 90037993 := bstep (se 2 (by rfl) ⟨33764247, by rfl⟩ : syracuseStep 90037993 = 67528495) B67528495
theorem B11099915 : Blo 1297967 11099915 := bstep (se 1 (by rfl) ⟨8324936, by rfl⟩ : syracuseStep 11099915 = 16649873) B16649873
theorem B22202423 : Blo 1297967 22202423 := bstep (se 1 (by rfl) ⟨16651817, by rfl⟩ : syracuseStep 22202423 = 33303635) B33303635
theorem B7399943 : Blo 1297967 7399943 := bstep (se 1 (by rfl) ⟨5549957, by rfl⟩ : syracuseStep 7399943 = 11099915) B11099915
theorem B101206705 : Blo 1297967 101206705 := bstep (se 2 (by rfl) ⟨37952514, by rfl⟩ : syracuseStep 101206705 = 75905029) B75905029
theorem B3287911 : Blo 1297967 3287911 := bstep (se 1 (by rfl) ⟨2465933, by rfl⟩ : syracuseStep 3287911 = 4931867) B4931867
theorem B1298159 : Blo 1297967 1298159 := bstep (se 1 (by rfl) ⟨973619, by rfl⟩ : syracuseStep 1298159 = 1947239) B1947239
theorem B4935451 : Blo 1297967 4935451 := bstep (se 1 (by rfl) ⟨3701588, by rfl⟩ : syracuseStep 4935451 = 7403177) B7403177
theorem B38465567 : Blo 1297967 38465567 := bstep (se 1 (by rfl) ⟨28849175, by rfl⟩ : syracuseStep 38465567 = 57698351) B57698351
theorem B22491503 : Blo 1297967 22491503 := bstep (se 1 (by rfl) ⟨16868627, by rfl⟩ : syracuseStep 22491503 = 33737255) B33737255
theorem B1298911 : Blo 1297967 1298911 := bstep (se 1 (by rfl) ⟨974183, by rfl⟩ : syracuseStep 1298911 = 1948367) B1948367
theorem B1299151 : Blo 1297967 1299151 := bstep (se 1 (by rfl) ⟨974363, by rfl⟩ : syracuseStep 1299151 = 1948727) B1948727
theorem B1299327 : Blo 1297967 1299327 := bstep (se 1 (by rfl) ⟨974495, by rfl⟩ : syracuseStep 1299327 = 1948991) B1948991
theorem B120050657 : Blo 1297967 120050657 := bstep (se 2 (by rfl) ⟨45018996, by rfl⟩ : syracuseStep 120050657 = 90037993) B90037993
theorem B1299583 : Blo 1297967 1299583 := bstep (se 1 (by rfl) ⟨974687, by rfl⟩ : syracuseStep 1299583 = 1949375) B1949375
theorem B7026371 : Blo 1297967 7026371 := bstep (se 1 (by rfl) ⟨5269778, by rfl⟩ : syracuseStep 7026371 = 10539557) B10539557
theorem B2922191 : Blo 1297967 2922191 := bstep (se 1 (by rfl) ⟨2191643, by rfl⟩ : syracuseStep 2922191 = 4383287) B4383287
theorem B2464415 : Blo 1297967 2464415 := bstep (se 1 (by rfl) ⟨1848311, by rfl⟩ : syracuseStep 2464415 = 3696623) B3696623
theorem B1949351 : Blo 1297967 1949351 := bstep (se 1 (by rfl) ⟨1462013, by rfl⟩ : syracuseStep 1949351 = 2924027) B2924027
theorem B4383881 : Blo 1297967 4383881 := bstep (se 2 (by rfl) ⟨1643955, by rfl⟩ : syracuseStep 4383881 = 3287911) B3287911
theorem B4933295 : Blo 1297967 4933295 := bstep (se 1 (by rfl) ⟨3699971, by rfl⟩ : syracuseStep 4933295 = 7399943) B7399943
theorem B6580601 : Blo 1297967 6580601 := bstep (se 2 (by rfl) ⟨2467725, by rfl⟩ : syracuseStep 6580601 = 4935451) B4935451
theorem B25643711 : Blo 1297967 25643711 := bstep (se 1 (by rfl) ⟨19232783, by rfl⟩ : syracuseStep 25643711 = 38465567) B38465567
theorem B14994335 : Blo 1297967 14994335 := bstep (se 1 (by rfl) ⟨11245751, by rfl⟩ : syracuseStep 14994335 = 22491503) B22491503
theorem B134942273 : Blo 1297967 134942273 := bstep (se 2 (by rfl) ⟨50603352, by rfl⟩ : syracuseStep 134942273 = 101206705) B101206705
theorem B1642943 : Blo 1297967 1642943 := bstep (se 1 (by rfl) ⟨1232207, by rfl⟩ : syracuseStep 1642943 = 2464415) B2464415
theorem B1299567 : Blo 1297967 1299567 := bstep (se 1 (by rfl) ⟨974675, by rfl⟩ : syracuseStep 1299567 = 1949351) B1949351
theorem B80033771 : Blo 1297967 80033771 := bstep (se 1 (by rfl) ⟨60025328, by rfl⟩ : syracuseStep 80033771 = 120050657) B120050657
theorem B4684247 : Blo 1297967 4684247 := bstep (se 1 (by rfl) ⟨3513185, by rfl⟩ : syracuseStep 4684247 = 7026371) B7026371
theorem B1948127 : Blo 1297967 1948127 := bstep (se 1 (by rfl) ⟨1461095, by rfl⟩ : syracuseStep 1948127 = 2922191) B2922191
theorem B14801615 : Blo 1297967 14801615 := bstep (se 1 (by rfl) ⟨11101211, by rfl⟩ : syracuseStep 14801615 = 22202423) B22202423
theorem B53355847 : Blo 1297967 53355847 := bstep (se 1 (by rfl) ⟨40016885, by rfl⟩ : syracuseStep 53355847 = 80033771) B80033771
theorem B3122831 : Blo 1297967 3122831 := bstep (se 1 (by rfl) ⟨2342123, by rfl⟩ : syracuseStep 3122831 = 4684247) B4684247
theorem B9996223 : Blo 1297967 9996223 := bstep (se 1 (by rfl) ⟨7497167, by rfl⟩ : syracuseStep 9996223 = 14994335) B14994335
theorem B3288863 : Blo 1297967 3288863 := bstep (se 1 (by rfl) ⟨2466647, by rfl⟩ : syracuseStep 3288863 = 4933295) B4933295
theorem B4387067 : Blo 1297967 4387067 := bstep (se 1 (by rfl) ⟨3290300, by rfl⟩ : syracuseStep 4387067 = 6580601) B6580601
theorem B1298751 : Blo 1297967 1298751 := bstep (se 1 (by rfl) ⟨974063, by rfl⟩ : syracuseStep 1298751 = 1948127) B1948127
theorem B9867743 : Blo 1297967 9867743 := bstep (se 1 (by rfl) ⟨7400807, by rfl⟩ : syracuseStep 9867743 = 14801615) B14801615
theorem B89961515 : Blo 1297967 89961515 := bstep (se 1 (by rfl) ⟨67471136, by rfl⟩ : syracuseStep 89961515 = 134942273) B134942273
theorem B2922587 : Blo 1297967 2922587 := bstep (se 1 (by rfl) ⟨2191940, by rfl⟩ : syracuseStep 2922587 = 4383881) B4383881
theorem B4381181 : Blo 1297967 4381181 := bstep (se 3 (by rfl) ⟨821471, by rfl⟩ : syracuseStep 4381181 = 1642943) B1642943
theorem B17095807 : Blo 1297967 17095807 := bstep (se 1 (by rfl) ⟨12821855, by rfl⟩ : syracuseStep 17095807 = 25643711) B25643711
theorem B2924711 : Blo 1297967 2924711 := bstep (se 1 (by rfl) ⟨2193533, by rfl⟩ : syracuseStep 2924711 = 4387067) B4387067
theorem B6578495 : Blo 1297967 6578495 := bstep (se 1 (by rfl) ⟨4933871, by rfl⟩ : syracuseStep 6578495 = 9867743) B9867743
theorem B59974343 : Blo 1297967 59974343 := bstep (se 1 (by rfl) ⟨44980757, by rfl⟩ : syracuseStep 59974343 = 89961515) B89961515
theorem B71141129 : Blo 1297967 71141129 := bstep (se 2 (by rfl) ⟨26677923, by rfl⟩ : syracuseStep 71141129 = 53355847) B53355847
theorem B22794409 : Blo 1297967 22794409 := bstep (se 2 (by rfl) ⟨8547903, by rfl⟩ : syracuseStep 22794409 = 17095807) B17095807
theorem B2920787 : Blo 1297967 2920787 := bstep (se 1 (by rfl) ⟨2190590, by rfl⟩ : syracuseStep 2920787 = 4381181) B4381181
theorem B8327549 : Blo 1297967 8327549 := bstep (se 3 (by rfl) ⟨1561415, by rfl⟩ : syracuseStep 8327549 = 3122831) B3122831
theorem B2192575 : Blo 1297967 2192575 := bstep (se 1 (by rfl) ⟨1644431, by rfl⟩ : syracuseStep 2192575 = 3288863) B3288863
theorem B1948391 : Blo 1297967 1948391 := bstep (se 1 (by rfl) ⟨1461293, by rfl⟩ : syracuseStep 1948391 = 2922587) B2922587
theorem B13328297 : Blo 1297967 13328297 := bstep (se 2 (by rfl) ⟨4998111, by rfl⟩ : syracuseStep 13328297 = 9996223) B9996223
theorem B1949807 : Blo 1297967 1949807 := bstep (se 1 (by rfl) ⟨1462355, by rfl⟩ : syracuseStep 1949807 = 2924711) B2924711
theorem B30392545 : Blo 1297967 30392545 := bstep (se 2 (by rfl) ⟨11397204, by rfl⟩ : syracuseStep 30392545 = 22794409) B22794409
theorem B4385663 : Blo 1297967 4385663 := bstep (se 1 (by rfl) ⟨3289247, by rfl⟩ : syracuseStep 4385663 = 6578495) B6578495
theorem B47427419 : Blo 1297967 47427419 := bstep (se 1 (by rfl) ⟨35570564, by rfl⟩ : syracuseStep 47427419 = 71141129) B71141129
theorem B1298927 : Blo 1297967 1298927 := bstep (se 1 (by rfl) ⟨974195, by rfl⟩ : syracuseStep 1298927 = 1948391) B1948391
theorem B8885531 : Blo 1297967 8885531 := bstep (se 1 (by rfl) ⟨6664148, by rfl⟩ : syracuseStep 8885531 = 13328297) B13328297
theorem B1947191 : Blo 1297967 1947191 := bstep (se 1 (by rfl) ⟨1460393, by rfl⟩ : syracuseStep 1947191 = 2920787) B2920787
theorem B39982895 : Blo 1297967 39982895 := bstep (se 1 (by rfl) ⟨29987171, by rfl⟩ : syracuseStep 39982895 = 59974343) B59974343
theorem B22206797 : Blo 1297967 22206797 := bstep (se 3 (by rfl) ⟨4163774, by rfl⟩ : syracuseStep 22206797 = 8327549) B8327549
theorem B2923433 : Blo 1297967 2923433 := bstep (se 2 (by rfl) ⟨1096287, by rfl⟩ : syracuseStep 2923433 = 2192575) B2192575
theorem B5923687 : Blo 1297967 5923687 := bstep (se 1 (by rfl) ⟨4442765, by rfl⟩ : syracuseStep 5923687 = 8885531) B8885531
theorem B14804531 : Blo 1297967 14804531 := bstep (se 1 (by rfl) ⟨11103398, by rfl⟩ : syracuseStep 14804531 = 22206797) B22206797
theorem B1298127 : Blo 1297967 1298127 := bstep (se 1 (by rfl) ⟨973595, by rfl⟩ : syracuseStep 1298127 = 1947191) B1947191
theorem B31618279 : Blo 1297967 31618279 := bstep (se 1 (by rfl) ⟨23713709, by rfl⟩ : syracuseStep 31618279 = 47427419) B47427419
theorem B1299871 : Blo 1297967 1299871 := bstep (se 1 (by rfl) ⟨974903, by rfl⟩ : syracuseStep 1299871 = 1949807) B1949807
theorem B40523393 : Blo 1297967 40523393 := bstep (se 2 (by rfl) ⟨15196272, by rfl⟩ : syracuseStep 40523393 = 30392545) B30392545
theorem B26655263 : Blo 1297967 26655263 := bstep (se 1 (by rfl) ⟨19991447, by rfl⟩ : syracuseStep 26655263 = 39982895) B39982895
theorem B2923775 : Blo 1297967 2923775 := bstep (se 1 (by rfl) ⟨2192831, by rfl⟩ : syracuseStep 2923775 = 4385663) B4385663
theorem B1948955 : Blo 1297967 1948955 := bstep (se 1 (by rfl) ⟨1461716, by rfl⟩ : syracuseStep 1948955 = 2923433) B2923433
theorem B7898249 : Blo 1297967 7898249 := bstep (se 2 (by rfl) ⟨2961843, by rfl⟩ : syracuseStep 7898249 = 5923687) B5923687
theorem B42157705 : Blo 1297967 42157705 := bstep (se 2 (by rfl) ⟨15809139, by rfl⟩ : syracuseStep 42157705 = 31618279) B31618279
theorem B108062381 : Blo 1297967 108062381 := bstep (se 3 (by rfl) ⟨20261696, by rfl⟩ : syracuseStep 108062381 = 40523393) B40523393
theorem B17770175 : Blo 1297967 17770175 := bstep (se 1 (by rfl) ⟨13327631, by rfl⟩ : syracuseStep 17770175 = 26655263) B26655263
theorem B1299303 : Blo 1297967 1299303 := bstep (se 1 (by rfl) ⟨974477, by rfl⟩ : syracuseStep 1299303 = 1948955) B1948955
theorem B9869687 : Blo 1297967 9869687 := bstep (se 1 (by rfl) ⟨7402265, by rfl⟩ : syracuseStep 9869687 = 14804531) B14804531
theorem B1949183 : Blo 1297967 1949183 := bstep (se 1 (by rfl) ⟨1461887, by rfl⟩ : syracuseStep 1949183 = 2923775) B2923775
theorem B11846783 : Blo 1297967 11846783 := bstep (se 1 (by rfl) ⟨8885087, by rfl⟩ : syracuseStep 11846783 = 17770175) B17770175
theorem B6579791 : Blo 1297967 6579791 := bstep (se 1 (by rfl) ⟨4934843, by rfl⟩ : syracuseStep 6579791 = 9869687) B9869687
theorem B288166349 : Blo 1297967 288166349 := bstep (se 3 (by rfl) ⟨54031190, by rfl⟩ : syracuseStep 288166349 = 108062381) B108062381
theorem B56210273 : Blo 1297967 56210273 := bstep (se 2 (by rfl) ⟨21078852, by rfl⟩ : syracuseStep 56210273 = 42157705) B42157705
theorem B1299455 : Blo 1297967 1299455 := bstep (se 1 (by rfl) ⟨974591, by rfl⟩ : syracuseStep 1299455 = 1949183) B1949183
theorem B5265499 : Blo 1297967 5265499 := bstep (se 1 (by rfl) ⟨3949124, by rfl⟩ : syracuseStep 5265499 = 7898249) B7898249
theorem B7020665 : Blo 1297967 7020665 := bstep (se 2 (by rfl) ⟨2632749, by rfl⟩ : syracuseStep 7020665 = 5265499) B5265499
theorem B192110899 : Blo 1297967 192110899 := bstep (se 1 (by rfl) ⟨144083174, by rfl⟩ : syracuseStep 192110899 = 288166349) B288166349
theorem B31591421 : Blo 1297967 31591421 := bstep (se 3 (by rfl) ⟨5923391, by rfl⟩ : syracuseStep 31591421 = 11846783) B11846783
theorem B37473515 : Blo 1297967 37473515 := bstep (se 1 (by rfl) ⟨28105136, by rfl⟩ : syracuseStep 37473515 = 56210273) B56210273
theorem B4386527 : Blo 1297967 4386527 := bstep (se 1 (by rfl) ⟨3289895, by rfl⟩ : syracuseStep 4386527 = 6579791) B6579791
theorem B256147865 : Blo 1297967 256147865 := bstep (se 2 (by rfl) ⟨96055449, by rfl⟩ : syracuseStep 256147865 = 192110899) B192110899
theorem B4680443 : Blo 1297967 4680443 := bstep (se 1 (by rfl) ⟨3510332, by rfl⟩ : syracuseStep 4680443 = 7020665) B7020665
theorem B24982343 : Blo 1297967 24982343 := bstep (se 1 (by rfl) ⟨18736757, by rfl⟩ : syracuseStep 24982343 = 37473515) B37473515
theorem B21060947 : Blo 1297967 21060947 := bstep (se 1 (by rfl) ⟨15795710, by rfl⟩ : syracuseStep 21060947 = 31591421) B31591421
theorem B2924351 : Blo 1297967 2924351 := bstep (se 1 (by rfl) ⟨2193263, by rfl⟩ : syracuseStep 2924351 = 4386527) B4386527
theorem B16654895 : Blo 1297967 16654895 := bstep (se 1 (by rfl) ⟨12491171, by rfl⟩ : syracuseStep 16654895 = 24982343) B24982343
theorem B170765243 : Blo 1297967 170765243 := bstep (se 1 (by rfl) ⟨128073932, by rfl⟩ : syracuseStep 170765243 = 256147865) B256147865
theorem B3120295 : Blo 1297967 3120295 := bstep (se 1 (by rfl) ⟨2340221, by rfl⟩ : syracuseStep 3120295 = 4680443) B4680443
theorem B14040631 : Blo 1297967 14040631 := bstep (se 1 (by rfl) ⟨10530473, by rfl⟩ : syracuseStep 14040631 = 21060947) B21060947
theorem B1949567 : Blo 1297967 1949567 := bstep (se 1 (by rfl) ⟨1462175, by rfl⟩ : syracuseStep 1949567 = 2924351) B2924351
theorem B18720841 : Blo 1297967 18720841 := bstep (se 2 (by rfl) ⟨7020315, by rfl⟩ : syracuseStep 18720841 = 14040631) B14040631
theorem B11103263 : Blo 1297967 11103263 := bstep (se 1 (by rfl) ⟨8327447, by rfl⟩ : syracuseStep 11103263 = 16654895) B16654895
theorem B1299711 : Blo 1297967 1299711 := bstep (se 1 (by rfl) ⟨974783, by rfl⟩ : syracuseStep 1299711 = 1949567) B1949567
theorem B4160393 : Blo 1297967 4160393 := bstep (se 2 (by rfl) ⟨1560147, by rfl⟩ : syracuseStep 4160393 = 3120295) B3120295
theorem B113843495 : Blo 1297967 113843495 := bstep (se 1 (by rfl) ⟨85382621, by rfl⟩ : syracuseStep 113843495 = 170765243) B170765243
theorem B24961121 : Blo 1297967 24961121 := bstep (se 2 (by rfl) ⟨9360420, by rfl⟩ : syracuseStep 24961121 = 18720841) B18720841
theorem B2773595 : Blo 1297967 2773595 := bstep (se 1 (by rfl) ⟨2080196, by rfl⟩ : syracuseStep 2773595 = 4160393) B4160393
theorem B7402175 : Blo 1297967 7402175 := bstep (se 1 (by rfl) ⟨5551631, by rfl⟩ : syracuseStep 7402175 = 11103263) B11103263
theorem B75895663 : Blo 1297967 75895663 := bstep (se 1 (by rfl) ⟨56921747, by rfl⟩ : syracuseStep 75895663 = 113843495) B113843495
theorem B16640747 : Blo 1297967 16640747 := bstep (se 1 (by rfl) ⟨12480560, by rfl⟩ : syracuseStep 16640747 = 24961121) B24961121
theorem B4934783 : Blo 1297967 4934783 := bstep (se 1 (by rfl) ⟨3701087, by rfl⟩ : syracuseStep 4934783 = 7402175) B7402175
theorem B1849063 : Blo 1297967 1849063 := bstep (se 1 (by rfl) ⟨1386797, by rfl⟩ : syracuseStep 1849063 = 2773595) B2773595
theorem B101194217 : Blo 1297967 101194217 := bstep (se 2 (by rfl) ⟨37947831, by rfl⟩ : syracuseStep 101194217 = 75895663) B75895663
theorem B67462811 : Blo 1297967 67462811 := bstep (se 1 (by rfl) ⟨50597108, by rfl⟩ : syracuseStep 67462811 = 101194217) B101194217
theorem B11093831 : Blo 1297967 11093831 := bstep (se 1 (by rfl) ⟨8320373, by rfl⟩ : syracuseStep 11093831 = 16640747) B16640747
theorem B3289855 : Blo 1297967 3289855 := bstep (se 1 (by rfl) ⟨2467391, by rfl⟩ : syracuseStep 3289855 = 4934783) B4934783
theorem B2465417 : Blo 1297967 2465417 := bstep (se 2 (by rfl) ⟨924531, by rfl⟩ : syracuseStep 2465417 = 1849063) B1849063
theorem B44975207 : Blo 1297967 44975207 := bstep (se 1 (by rfl) ⟨33731405, by rfl⟩ : syracuseStep 44975207 = 67462811) B67462811
theorem B4386473 : Blo 1297967 4386473 := bstep (se 2 (by rfl) ⟨1644927, by rfl⟩ : syracuseStep 4386473 = 3289855) B3289855
theorem B6574445 : Blo 1297967 6574445 := bstep (se 3 (by rfl) ⟨1232708, by rfl⟩ : syracuseStep 6574445 = 2465417) B2465417
theorem B7395887 : Blo 1297967 7395887 := bstep (se 1 (by rfl) ⟨5546915, by rfl⟩ : syracuseStep 7395887 = 11093831) B11093831
theorem B4382963 : Blo 1297967 4382963 := bstep (se 1 (by rfl) ⟨3287222, by rfl⟩ : syracuseStep 4382963 = 6574445) B6574445
theorem B119933885 : Blo 1297967 119933885 := bstep (se 3 (by rfl) ⟨22487603, by rfl⟩ : syracuseStep 119933885 = 44975207) B44975207
theorem B4930591 : Blo 1297967 4930591 := bstep (se 1 (by rfl) ⟨3697943, by rfl⟩ : syracuseStep 4930591 = 7395887) B7395887
theorem B2924315 : Blo 1297967 2924315 := bstep (se 1 (by rfl) ⟨2193236, by rfl⟩ : syracuseStep 2924315 = 4386473) B4386473
theorem B79955923 : Blo 1297967 79955923 := bstep (se 1 (by rfl) ⟨59966942, by rfl⟩ : syracuseStep 79955923 = 119933885) B119933885
theorem B6574121 : Blo 1297967 6574121 := bstep (se 2 (by rfl) ⟨2465295, by rfl⟩ : syracuseStep 6574121 = 4930591) B4930591
theorem B2921975 : Blo 1297967 2921975 := bstep (se 1 (by rfl) ⟨2191481, by rfl⟩ : syracuseStep 2921975 = 4382963) B4382963
theorem B1949543 : Blo 1297967 1949543 := bstep (se 1 (by rfl) ⟨1462157, by rfl⟩ : syracuseStep 1949543 = 2924315) B2924315
theorem B4382747 : Blo 1297967 4382747 := bstep (se 1 (by rfl) ⟨3287060, by rfl⟩ : syracuseStep 4382747 = 6574121) B6574121
theorem B1299695 : Blo 1297967 1299695 := bstep (se 1 (by rfl) ⟨974771, by rfl⟩ : syracuseStep 1299695 = 1949543) B1949543
theorem B106607897 : Blo 1297967 106607897 := bstep (se 2 (by rfl) ⟨39977961, by rfl⟩ : syracuseStep 106607897 = 79955923) B79955923
theorem B1947983 : Blo 1297967 1947983 := bstep (se 1 (by rfl) ⟨1460987, by rfl⟩ : syracuseStep 1947983 = 2921975) B2921975
theorem B1298655 : Blo 1297967 1298655 := bstep (se 1 (by rfl) ⟨973991, by rfl⟩ : syracuseStep 1298655 = 1947983) B1947983
theorem B2921831 : Blo 1297967 2921831 := bstep (se 1 (by rfl) ⟨2191373, by rfl⟩ : syracuseStep 2921831 = 4382747) B4382747
theorem B71071931 : Blo 1297967 71071931 := bstep (se 1 (by rfl) ⟨53303948, by rfl⟩ : syracuseStep 71071931 = 106607897) B106607897
theorem B1947887 : Blo 1297967 1947887 := bstep (se 1 (by rfl) ⟨1460915, by rfl⟩ : syracuseStep 1947887 = 2921831) B2921831
theorem B47381287 : Blo 1297967 47381287 := bstep (se 1 (by rfl) ⟨35535965, by rfl⟩ : syracuseStep 47381287 = 71071931) B71071931
theorem B1298591 : Blo 1297967 1298591 := bstep (se 1 (by rfl) ⟨973943, by rfl⟩ : syracuseStep 1298591 = 1947887) B1947887
theorem B63175049 : Blo 1297967 63175049 := bstep (se 2 (by rfl) ⟨23690643, by rfl⟩ : syracuseStep 63175049 = 47381287) B47381287
theorem B42116699 : Blo 1297967 42116699 := bstep (se 1 (by rfl) ⟨31587524, by rfl⟩ : syracuseStep 42116699 = 63175049) B63175049
theorem B112311197 : Blo 1297967 112311197 := bstep (se 3 (by rfl) ⟨21058349, by rfl⟩ : syracuseStep 112311197 = 42116699) B42116699
theorem B74874131 : Blo 1297967 74874131 := bstep (se 1 (by rfl) ⟨56155598, by rfl⟩ : syracuseStep 74874131 = 112311197) B112311197
theorem B49916087 : Blo 1297967 49916087 := bstep (se 1 (by rfl) ⟨37437065, by rfl⟩ : syracuseStep 49916087 = 74874131) B74874131
theorem B33277391 : Blo 1297967 33277391 := bstep (se 1 (by rfl) ⟨24958043, by rfl⟩ : syracuseStep 33277391 = 49916087) B49916087
theorem B22184927 : Blo 1297967 22184927 := bstep (se 1 (by rfl) ⟨16638695, by rfl⟩ : syracuseStep 22184927 = 33277391) B33277391
theorem B14789951 : Blo 1297967 14789951 := bstep (se 1 (by rfl) ⟨11092463, by rfl⟩ : syracuseStep 14789951 = 22184927) B22184927
theorem B9859967 : Blo 1297967 9859967 := bstep (se 1 (by rfl) ⟨7394975, by rfl⟩ : syracuseStep 9859967 = 14789951) B14789951
theorem B6573311 : Blo 1297967 6573311 := bstep (se 1 (by rfl) ⟨4929983, by rfl⟩ : syracuseStep 6573311 = 9859967) B9859967
theorem B4382207 : Blo 1297967 4382207 := bstep (se 1 (by rfl) ⟨3286655, by rfl⟩ : syracuseStep 4382207 = 6573311) B6573311
theorem B2921471 : Blo 1297967 2921471 := bstep (se 1 (by rfl) ⟨2191103, by rfl⟩ : syracuseStep 2921471 = 4382207) B4382207
theorem B1947647 : Blo 1297967 1947647 := bstep (se 1 (by rfl) ⟨1460735, by rfl⟩ : syracuseStep 1947647 = 2921471) B2921471
theorem B1298431 : Blo 1297967 1298431 := bstep (se 1 (by rfl) ⟨973823, by rfl⟩ : syracuseStep 1298431 = 1947647) B1947647

theorem C0 (j : ℕ) (h1 : 324491 ≤ j) (h2 : j ≤ 324991) : Blo 1297967 (4 * j + 3) := by
  interval_cases j
  · exact B1297967
  · exact B1297971
  · exact B1297975
  · exact B1297979
  · exact B1297983
  · exact B1297987
  · exact B1297991
  · exact B1297995
  · exact B1297999
  · exact B1298003
  · exact B1298007
  · exact B1298011
  · exact B1298015
  · exact B1298019
  · exact B1298023
  · exact B1298027
  · exact B1298031
  · exact B1298035
  · exact B1298039
  · exact B1298043
  · exact B1298047
  · exact B1298051
  · exact B1298055
  · exact B1298059
  · exact B1298063
  · exact B1298067
  · exact B1298071
  · exact B1298075
  · exact B1298079
  · exact B1298083
  · exact B1298087
  · exact B1298091
  · exact B1298095
  · exact B1298099
  · exact B1298103
  · exact B1298107
  · exact B1298111
  · exact B1298115
  · exact B1298119
  · exact B1298123
  · exact B1298127
  · exact B1298131
  · exact B1298135
  · exact B1298139
  · exact B1298143
  · exact B1298147
  · exact B1298151
  · exact B1298155
  · exact B1298159
  · exact B1298163
  · exact B1298167
  · exact B1298171
  · exact B1298175
  · exact B1298179
  · exact B1298183
  · exact B1298187
  · exact B1298191
  · exact B1298195
  · exact B1298199
  · exact B1298203
  · exact B1298207
  · exact B1298211
  · exact B1298215
  · exact B1298219
  · exact B1298223
  · exact B1298227
  · exact B1298231
  · exact B1298235
  · exact B1298239
  · exact B1298243
  · exact B1298247
  · exact B1298251
  · exact B1298255
  · exact B1298259
  · exact B1298263
  · exact B1298267
  · exact B1298271
  · exact B1298275
  · exact B1298279
  · exact B1298283
  · exact B1298287
  · exact B1298291
  · exact B1298295
  · exact B1298299
  · exact B1298303
  · exact B1298307
  · exact B1298311
  · exact B1298315
  · exact B1298319
  · exact B1298323
  · exact B1298327
  · exact B1298331
  · exact B1298335
  · exact B1298339
  · exact B1298343
  · exact B1298347
  · exact B1298351
  · exact B1298355
  · exact B1298359
  · exact B1298363
  · exact B1298367
  · exact B1298371
  · exact B1298375
  · exact B1298379
  · exact B1298383
  · exact B1298387
  · exact B1298391
  · exact B1298395
  · exact B1298399
  · exact B1298403
  · exact B1298407
  · exact B1298411
  · exact B1298415
  · exact B1298419
  · exact B1298423
  · exact B1298427
  · exact B1298431
  · exact B1298435
  · exact B1298439
  · exact B1298443
  · exact B1298447
  · exact B1298451
  · exact B1298455
  · exact B1298459
  · exact B1298463
  · exact B1298467
  · exact B1298471
  · exact B1298475
  · exact B1298479
  · exact B1298483
  · exact B1298487
  · exact B1298491
  · exact B1298495
  · exact B1298499
  · exact B1298503
  · exact B1298507
  · exact B1298511
  · exact B1298515
  · exact B1298519
  · exact B1298523
  · exact B1298527
  · exact B1298531
  · exact B1298535
  · exact B1298539
  · exact B1298543
  · exact B1298547
  · exact B1298551
  · exact B1298555
  · exact B1298559
  · exact B1298563
  · exact B1298567
  · exact B1298571
  · exact B1298575
  · exact B1298579
  · exact B1298583
  · exact B1298587
  · exact B1298591
  · exact B1298595
  · exact B1298599
  · exact B1298603
  · exact B1298607
  · exact B1298611
  · exact B1298615
  · exact B1298619
  · exact B1298623
  · exact B1298627
  · exact B1298631
  · exact B1298635
  · exact B1298639
  · exact B1298643
  · exact B1298647
  · exact B1298651
  · exact B1298655
  · exact B1298659
  · exact B1298663
  · exact B1298667
  · exact B1298671
  · exact B1298675
  · exact B1298679
  · exact B1298683
  · exact B1298687
  · exact B1298691
  · exact B1298695
  · exact B1298699
  · exact B1298703
  · exact B1298707
  · exact B1298711
  · exact B1298715
  · exact B1298719
  · exact B1298723
  · exact B1298727
  · exact B1298731
  · exact B1298735
  · exact B1298739
  · exact B1298743
  · exact B1298747
  · exact B1298751
  · exact B1298755
  · exact B1298759
  · exact B1298763
  · exact B1298767
  · exact B1298771
  · exact B1298775
  · exact B1298779
  · exact B1298783
  · exact B1298787
  · exact B1298791
  · exact B1298795
  · exact B1298799
  · exact B1298803
  · exact B1298807
  · exact B1298811
  · exact B1298815
  · exact B1298819
  · exact B1298823
  · exact B1298827
  · exact B1298831
  · exact B1298835
  · exact B1298839
  · exact B1298843
  · exact B1298847
  · exact B1298851
  · exact B1298855
  · exact B1298859
  · exact B1298863
  · exact B1298867
  · exact B1298871
  · exact B1298875
  · exact B1298879
  · exact B1298883
  · exact B1298887
  · exact B1298891
  · exact B1298895
  · exact B1298899
  · exact B1298903
  · exact B1298907
  · exact B1298911
  · exact B1298915
  · exact B1298919
  · exact B1298923
  · exact B1298927
  · exact B1298931
  · exact B1298935
  · exact B1298939
  · exact B1298943
  · exact B1298947
  · exact B1298951
  · exact B1298955
  · exact B1298959
  · exact B1298963
  · exact B1298967
  · exact B1298971
  · exact B1298975
  · exact B1298979
  · exact B1298983
  · exact B1298987
  · exact B1298991
  · exact B1298995
  · exact B1298999
  · exact B1299003
  · exact B1299007
  · exact B1299011
  · exact B1299015
  · exact B1299019
  · exact B1299023
  · exact B1299027
  · exact B1299031
  · exact B1299035
  · exact B1299039
  · exact B1299043
  · exact B1299047
  · exact B1299051
  · exact B1299055
  · exact B1299059
  · exact B1299063
  · exact B1299067
  · exact B1299071
  · exact B1299075
  · exact B1299079
  · exact B1299083
  · exact B1299087
  · exact B1299091
  · exact B1299095
  · exact B1299099
  · exact B1299103
  · exact B1299107
  · exact B1299111
  · exact B1299115
  · exact B1299119
  · exact B1299123
  · exact B1299127
  · exact B1299131
  · exact B1299135
  · exact B1299139
  · exact B1299143
  · exact B1299147
  · exact B1299151
  · exact B1299155
  · exact B1299159
  · exact B1299163
  · exact B1299167
  · exact B1299171
  · exact B1299175
  · exact B1299179
  · exact B1299183
  · exact B1299187
  · exact B1299191
  · exact B1299195
  · exact B1299199
  · exact B1299203
  · exact B1299207
  · exact B1299211
  · exact B1299215
  · exact B1299219
  · exact B1299223
  · exact B1299227
  · exact B1299231
  · exact B1299235
  · exact B1299239
  · exact B1299243
  · exact B1299247
  · exact B1299251
  · exact B1299255
  · exact B1299259
  · exact B1299263
  · exact B1299267
  · exact B1299271
  · exact B1299275
  · exact B1299279
  · exact B1299283
  · exact B1299287
  · exact B1299291
  · exact B1299295
  · exact B1299299
  · exact B1299303
  · exact B1299307
  · exact B1299311
  · exact B1299315
  · exact B1299319
  · exact B1299323
  · exact B1299327
  · exact B1299331
  · exact B1299335
  · exact B1299339
  · exact B1299343
  · exact B1299347
  · exact B1299351
  · exact B1299355
  · exact B1299359
  · exact B1299363
  · exact B1299367
  · exact B1299371
  · exact B1299375
  · exact B1299379
  · exact B1299383
  · exact B1299387
  · exact B1299391
  · exact B1299395
  · exact B1299399
  · exact B1299403
  · exact B1299407
  · exact B1299411
  · exact B1299415
  · exact B1299419
  · exact B1299423
  · exact B1299427
  · exact B1299431
  · exact B1299435
  · exact B1299439
  · exact B1299443
  · exact B1299447
  · exact B1299451
  · exact B1299455
  · exact B1299459
  · exact B1299463
  · exact B1299467
  · exact B1299471
  · exact B1299475
  · exact B1299479
  · exact B1299483
  · exact B1299487
  · exact B1299491
  · exact B1299495
  · exact B1299499
  · exact B1299503
  · exact B1299507
  · exact B1299511
  · exact B1299515
  · exact B1299519
  · exact B1299523
  · exact B1299527
  · exact B1299531
  · exact B1299535
  · exact B1299539
  · exact B1299543
  · exact B1299547
  · exact B1299551
  · exact B1299555
  · exact B1299559
  · exact B1299563
  · exact B1299567
  · exact B1299571
  · exact B1299575
  · exact B1299579
  · exact B1299583
  · exact B1299587
  · exact B1299591
  · exact B1299595
  · exact B1299599
  · exact B1299603
  · exact B1299607
  · exact B1299611
  · exact B1299615
  · exact B1299619
  · exact B1299623
  · exact B1299627
  · exact B1299631
  · exact B1299635
  · exact B1299639
  · exact B1299643
  · exact B1299647
  · exact B1299651
  · exact B1299655
  · exact B1299659
  · exact B1299663
  · exact B1299667
  · exact B1299671
  · exact B1299675
  · exact B1299679
  · exact B1299683
  · exact B1299687
  · exact B1299691
  · exact B1299695
  · exact B1299699
  · exact B1299703
  · exact B1299707
  · exact B1299711
  · exact B1299715
  · exact B1299719
  · exact B1299723
  · exact B1299727
  · exact B1299731
  · exact B1299735
  · exact B1299739
  · exact B1299743
  · exact B1299747
  · exact B1299751
  · exact B1299755
  · exact B1299759
  · exact B1299763
  · exact B1299767
  · exact B1299771
  · exact B1299775
  · exact B1299779
  · exact B1299783
  · exact B1299787
  · exact B1299791
  · exact B1299795
  · exact B1299799
  · exact B1299803
  · exact B1299807
  · exact B1299811
  · exact B1299815
  · exact B1299819
  · exact B1299823
  · exact B1299827
  · exact B1299831
  · exact B1299835
  · exact B1299839
  · exact B1299843
  · exact B1299847
  · exact B1299851
  · exact B1299855
  · exact B1299859
  · exact B1299863
  · exact B1299867
  · exact B1299871
  · exact B1299875
  · exact B1299879
  · exact B1299883
  · exact B1299887
  · exact B1299891
  · exact B1299895
  · exact B1299899
  · exact B1299903
  · exact B1299907
  · exact B1299911
  · exact B1299915
  · exact B1299919
  · exact B1299923
  · exact B1299927
  · exact B1299931
  · exact B1299935
  · exact B1299939
  · exact B1299943
  · exact B1299947
  · exact B1299951
  · exact B1299955
  · exact B1299959
  · exact B1299963
  · exact B1299967

theorem solution (m : ℕ) (hlo : 1297967 ≤ m) (hhi : m ≤ 1299967) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 324491 ≤ j := by omega
    have hj2 : j ≤ 324991 := by omega
    have hb : Blo 1297967 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
