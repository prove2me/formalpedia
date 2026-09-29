-- Prove2me | solution 1 for syracuse_descends_range_1262449_1264449
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:11:24.239232+00:00
-- url     : https://prove2.me/submissions/8e653f25-a0e5-481d-818d-da511fd7d435

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


theorem B2400293 : Blo 1262449 2400293 := bbase (se 4 (by rfl) ⟨225027, by rfl⟩ : syracuseStep 2400293 = 450055) (by norm_num)
theorem B2842685 : Blo 1262449 2842685 := bbase (se 3 (by rfl) ⟨533003, by rfl⟩ : syracuseStep 2842685 = 1066007) (by norm_num)
theorem B7684213 : Blo 1262449 7684213 := bbase (se 5 (by rfl) ⟨360197, by rfl⟩ : syracuseStep 7684213 = 720395) (by norm_num)
theorem B2842757 : Blo 1262449 2842757 := bbase (se 4 (by rfl) ⟨266508, by rfl⟩ : syracuseStep 2842757 = 533017) (by norm_num)
theorem B23052437 : Blo 1262449 23052437 := bbase (se 6 (by rfl) ⟨540291, by rfl⟩ : syracuseStep 23052437 = 1080583) (by norm_num)
theorem B2277533 : Blo 1262449 2277533 := bbase (se 3 (by rfl) ⟨427037, by rfl⟩ : syracuseStep 2277533 = 854075) (by norm_num)
theorem B2400445 : Blo 1262449 2400445 := bbase (se 3 (by rfl) ⟨450083, by rfl⟩ : syracuseStep 2400445 = 900167) (by norm_num)
theorem B2842829 : Blo 1262449 2842829 := bbase (se 3 (by rfl) ⟨533030, by rfl⟩ : syracuseStep 2842829 = 1066061) (by norm_num)
theorem B3416309 : Blo 1262449 3416309 := bbase (se 5 (by rfl) ⟨160139, by rfl⟩ : syracuseStep 3416309 = 320279) (by norm_num)
theorem B1753349 : Blo 1262449 1753349 := bbase (se 4 (by rfl) ⟨164376, by rfl⟩ : syracuseStep 1753349 = 328753) (by norm_num)
theorem B2842901 : Blo 1262449 2842901 := bbase (se 6 (by rfl) ⟨66630, by rfl⟩ : syracuseStep 2842901 = 133261) (by norm_num)
theorem B2842973 : Blo 1262449 2842973 := bbase (se 3 (by rfl) ⟨533057, by rfl⟩ : syracuseStep 2842973 = 1066115) (by norm_num)
theorem B1597801 : Blo 1262449 1597801 := bbase (se 2 (by rfl) ⟨599175, by rfl⟩ : syracuseStep 1597801 = 1198351) (by norm_num)
theorem B10797461 : Blo 1262449 10797461 := bbase (se 6 (by rfl) ⟨253065, by rfl⟩ : syracuseStep 10797461 = 506131) (by norm_num)
theorem B2843045 : Blo 1262449 2843045 := bbase (se 4 (by rfl) ⟨266535, by rfl⟩ : syracuseStep 2843045 = 533071) (by norm_num)
theorem B2277821 : Blo 1262449 2277821 := bbase (se 3 (by rfl) ⟨427091, by rfl⟩ : syracuseStep 2277821 = 854183) (by norm_num)
theorem B1597897 : Blo 1262449 1597897 := bbase (se 2 (by rfl) ⟨599211, by rfl⟩ : syracuseStep 1597897 = 1198423) (by norm_num)
theorem B2843117 : Blo 1262449 2843117 := bbase (se 3 (by rfl) ⟨533084, by rfl⟩ : syracuseStep 2843117 = 1066169) (by norm_num)
theorem B2130421 : Blo 1262449 2130421 := bbase (se 5 (by rfl) ⟨99863, by rfl⟩ : syracuseStep 2130421 = 199727) (by norm_num)
theorem B2843189 : Blo 1262449 2843189 := bbase (se 5 (by rfl) ⟨133274, by rfl⟩ : syracuseStep 2843189 = 266549) (by norm_num)
theorem B2130509 : Blo 1262449 2130509 := bbase (se 3 (by rfl) ⟨399470, by rfl⟩ : syracuseStep 2130509 = 798941) (by norm_num)
theorem B1598069 : Blo 1262449 1598069 := bbase (se 5 (by rfl) ⟨74909, by rfl⟩ : syracuseStep 1598069 = 149819) (by norm_num)
theorem B2843261 : Blo 1262449 2843261 := bbase (se 3 (by rfl) ⟨533111, by rfl⟩ : syracuseStep 2843261 = 1066223) (by norm_num)
theorem B21897877 : Blo 1262449 21897877 := bbase (se 6 (by rfl) ⟨513231, by rfl⟩ : syracuseStep 21897877 = 1026463) (by norm_num)
theorem B1598125 : Blo 1262449 1598125 := bbase (se 3 (by rfl) ⟨299648, by rfl⟩ : syracuseStep 1598125 = 599297) (by norm_num)
theorem B2843333 : Blo 1262449 2843333 := bbase (se 4 (by rfl) ⟨266562, by rfl⟩ : syracuseStep 2843333 = 533125) (by norm_num)
theorem B2130637 : Blo 1262449 2130637 := bbase (se 3 (by rfl) ⟨399494, by rfl⟩ : syracuseStep 2130637 = 798989) (by norm_num)
theorem B1598221 : Blo 1262449 1598221 := bbase (se 3 (by rfl) ⟨299666, by rfl⟩ : syracuseStep 1598221 = 599333) (by norm_num)
theorem B2843405 : Blo 1262449 2843405 := bbase (se 3 (by rfl) ⟨533138, by rfl⟩ : syracuseStep 2843405 = 1066277) (by norm_num)
theorem B2130725 : Blo 1262449 2130725 := bbase (se 4 (by rfl) ⟨199755, by rfl⟩ : syracuseStep 2130725 = 399511) (by norm_num)
theorem B11682613 : Blo 1262449 11682613 := bbase (se 5 (by rfl) ⟨547622, by rfl⟩ : syracuseStep 11682613 = 1095245) (by norm_num)
theorem B3195733 : Blo 1262449 3195733 := bbase (se 9 (by rfl) ⟨9362, by rfl⟩ : syracuseStep 3195733 = 18725) (by norm_num)
theorem B2843477 : Blo 1262449 2843477 := bbase (se 9 (by rfl) ⟨8330, by rfl⟩ : syracuseStep 2843477 = 16661) (by norm_num)
theorem B6398837 : Blo 1262449 6398837 := bbase (se 5 (by rfl) ⟨299945, by rfl⟩ : syracuseStep 6398837 = 599891) (by norm_num)
theorem B3597205 : Blo 1262449 3597205 := bbase (se 6 (by rfl) ⟨84309, by rfl⟩ : syracuseStep 3597205 = 168619) (by norm_num)
theorem B2843549 : Blo 1262449 2843549 := bbase (se 3 (by rfl) ⟨533165, by rfl⟩ : syracuseStep 2843549 = 1066331) (by norm_num)
theorem B2130853 : Blo 1262449 2130853 := bbase (se 4 (by rfl) ⟨199767, by rfl⟩ : syracuseStep 2130853 = 399535) (by norm_num)
theorem B1598393 : Blo 1262449 1598393 := bbase (se 2 (by rfl) ⟨599397, by rfl⟩ : syracuseStep 1598393 = 1198795) (by norm_num)
theorem B3195845 : Blo 1262449 3195845 := bbase (se 4 (by rfl) ⟨299610, by rfl⟩ : syracuseStep 3195845 = 599221) (by norm_num)
theorem B2843621 : Blo 1262449 2843621 := bbase (se 4 (by rfl) ⟨266589, by rfl⟩ : syracuseStep 2843621 = 533179) (by norm_num)
theorem B1598449 : Blo 1262449 1598449 := bbase (se 2 (by rfl) ⟨599418, by rfl⟩ : syracuseStep 1598449 = 1198837) (by norm_num)
theorem B2130941 : Blo 1262449 2130941 := bbase (se 3 (by rfl) ⟨399551, by rfl⟩ : syracuseStep 2130941 = 799103) (by norm_num)
theorem B4260869 : Blo 1262449 4260869 := bbase (se 4 (by rfl) ⟨399456, by rfl⟩ : syracuseStep 4260869 = 798913) (by norm_num)
theorem B2843693 : Blo 1262449 2843693 := bbase (se 3 (by rfl) ⟨533192, by rfl⟩ : syracuseStep 2843693 = 1066385) (by norm_num)
theorem B3597365 : Blo 1262449 3597365 := bbase (se 5 (by rfl) ⟨168626, by rfl⟩ : syracuseStep 3597365 = 337253) (by norm_num)
theorem B1598545 : Blo 1262449 1598545 := bbase (se 2 (by rfl) ⟨599454, by rfl⟩ : syracuseStep 1598545 = 1198909) (by norm_num)
theorem B2843765 : Blo 1262449 2843765 := bbase (se 5 (by rfl) ⟨133301, by rfl⟩ : syracuseStep 2843765 = 266603) (by norm_num)
theorem B2131069 : Blo 1262449 2131069 := bbase (se 3 (by rfl) ⟨399575, by rfl⟩ : syracuseStep 2131069 = 799151) (by norm_num)
theorem B3196037 : Blo 1262449 3196037 := bbase (se 4 (by rfl) ⟨299628, by rfl⟩ : syracuseStep 3196037 = 599257) (by norm_num)
theorem B5121157 : Blo 1262449 5121157 := bbase (se 4 (by rfl) ⟨480108, by rfl⟩ : syracuseStep 5121157 = 960217) (by norm_num)
theorem B9110677 : Blo 1262449 9110677 := bbase (se 6 (by rfl) ⟨213531, by rfl⟩ : syracuseStep 9110677 = 427063) (by norm_num)
theorem B4793525 : Blo 1262449 4793525 := bbase (se 5 (by rfl) ⟨224696, by rfl⟩ : syracuseStep 4793525 = 449393) (by norm_num)
theorem B2843837 : Blo 1262449 2843837 := bbase (se 3 (by rfl) ⟨533219, by rfl⟩ : syracuseStep 2843837 = 1066439) (by norm_num)
theorem B2131157 : Blo 1262449 2131157 := bbase (se 7 (by rfl) ⟨24974, by rfl⟩ : syracuseStep 2131157 = 49949) (by norm_num)
theorem B1598717 : Blo 1262449 1598717 := bbase (se 3 (by rfl) ⟨299759, by rfl⟩ : syracuseStep 1598717 = 599519) (by norm_num)
theorem B2843909 : Blo 1262449 2843909 := bbase (se 4 (by rfl) ⟨266616, by rfl⟩ : syracuseStep 2843909 = 533233) (by norm_num)
theorem B3597605 : Blo 1262449 3597605 := bbase (se 4 (by rfl) ⟨337275, by rfl⟩ : syracuseStep 3597605 = 674551) (by norm_num)
theorem B1893677 : Blo 1262449 1893677 := bbase (se 3 (by rfl) ⟨355064, by rfl⟩ : syracuseStep 1893677 = 710129) (by norm_num)
theorem B1598773 : Blo 1262449 1598773 := bbase (se 5 (by rfl) ⟨74942, by rfl⟩ : syracuseStep 1598773 = 149885) (by norm_num)
theorem B1893701 : Blo 1262449 1893701 := bbase (se 4 (by rfl) ⟨177534, by rfl⟩ : syracuseStep 1893701 = 355069) (by norm_num)
theorem B2843981 : Blo 1262449 2843981 := bbase (se 3 (by rfl) ⟨533246, by rfl⟩ : syracuseStep 2843981 = 1066493) (by norm_num)
theorem B2131285 : Blo 1262449 2131285 := bbase (se 12 (by rfl) ⟨780, by rfl⟩ : syracuseStep 2131285 = 1561) (by norm_num)
theorem B1893725 : Blo 1262449 1893725 := bbase (se 3 (by rfl) ⟨355073, by rfl⟩ : syracuseStep 1893725 = 710147) (by norm_num)
theorem B5399909 : Blo 1262449 5399909 := bbase (se 4 (by rfl) ⟨506241, by rfl⟩ : syracuseStep 5399909 = 1012483) (by norm_num)
theorem B1516909 : Blo 1262449 1516909 := bbase (se 3 (by rfl) ⟨284420, by rfl⟩ : syracuseStep 1516909 = 568841) (by norm_num)
theorem B2024813 : Blo 1262449 2024813 := bbase (se 3 (by rfl) ⟨379652, by rfl⟩ : syracuseStep 2024813 = 759305) (by norm_num)
theorem B1893749 : Blo 1262449 1893749 := bbase (se 5 (by rfl) ⟨88769, by rfl⟩ : syracuseStep 1893749 = 177539) (by norm_num)
theorem B1893773 : Blo 1262449 1893773 := bbase (se 3 (by rfl) ⟨355082, by rfl⟩ : syracuseStep 1893773 = 710165) (by norm_num)
theorem B1598869 : Blo 1262449 1598869 := bbase (se 6 (by rfl) ⟨37473, by rfl⟩ : syracuseStep 1598869 = 74947) (by norm_num)
theorem B2844053 : Blo 1262449 2844053 := bbase (se 6 (by rfl) ⟨66657, by rfl⟩ : syracuseStep 2844053 = 133315) (by norm_num)
theorem B1893797 : Blo 1262449 1893797 := bbase (se 4 (by rfl) ⟨177543, by rfl⟩ : syracuseStep 1893797 = 355087) (by norm_num)
theorem B2131373 : Blo 1262449 2131373 := bbase (se 3 (by rfl) ⟨399632, by rfl⟩ : syracuseStep 2131373 = 799265) (by norm_num)
theorem B4261301 : Blo 1262449 4261301 := bbase (se 5 (by rfl) ⟨199748, by rfl⟩ : syracuseStep 4261301 = 399497) (by norm_num)
theorem B9102773 : Blo 1262449 9102773 := bbase (se 5 (by rfl) ⟨426692, by rfl⟩ : syracuseStep 9102773 = 853385) (by norm_num)
theorem B1893821 : Blo 1262449 1893821 := bbase (se 3 (by rfl) ⟨355091, by rfl⟩ : syracuseStep 1893821 = 710183) (by norm_num)
theorem B1893845 : Blo 1262449 1893845 := bbase (se 7 (by rfl) ⟨22193, by rfl⟩ : syracuseStep 1893845 = 44387) (by norm_num)
theorem B4793813 : Blo 1262449 4793813 := bbase (se 7 (by rfl) ⟨56177, by rfl⟩ : syracuseStep 4793813 = 112355) (by norm_num)
theorem B3196381 : Blo 1262449 3196381 := bbase (se 3 (by rfl) ⟨599321, by rfl⟩ : syracuseStep 3196381 = 1198643) (by norm_num)
theorem B2844125 : Blo 1262449 2844125 := bbase (se 3 (by rfl) ⟨533273, by rfl⟩ : syracuseStep 2844125 = 1066547) (by norm_num)
theorem B3597797 : Blo 1262449 3597797 := bbase (se 4 (by rfl) ⟨337293, by rfl⟩ : syracuseStep 3597797 = 674587) (by norm_num)
theorem B1893869 : Blo 1262449 1893869 := bbase (se 3 (by rfl) ⟨355100, by rfl⟩ : syracuseStep 1893869 = 710201) (by norm_num)
theorem B1893893 : Blo 1262449 1893893 := bbase (se 4 (by rfl) ⟨177552, by rfl⟩ : syracuseStep 1893893 = 355105) (by norm_num)
theorem B1893917 : Blo 1262449 1893917 := bbase (se 3 (by rfl) ⟨355109, by rfl⟩ : syracuseStep 1893917 = 710219) (by norm_num)
theorem B2844197 : Blo 1262449 2844197 := bbase (se 4 (by rfl) ⟨266643, by rfl⟩ : syracuseStep 2844197 = 533287) (by norm_num)
theorem B2131501 : Blo 1262449 2131501 := bbase (se 3 (by rfl) ⟨399656, by rfl⟩ : syracuseStep 2131501 = 799313) (by norm_num)
theorem B1893941 : Blo 1262449 1893941 := bbase (se 5 (by rfl) ⟨88778, by rfl⟩ : syracuseStep 1893941 = 177557) (by norm_num)
theorem B1599041 : Blo 1262449 1599041 := bbase (se 2 (by rfl) ⟨599640, by rfl⟩ : syracuseStep 1599041 = 1199281) (by norm_num)
theorem B1517125 : Blo 1262449 1517125 := bbase (se 4 (by rfl) ⟨142230, by rfl⟩ : syracuseStep 1517125 = 284461) (by norm_num)
theorem B1893965 : Blo 1262449 1893965 := bbase (se 3 (by rfl) ⟨355118, by rfl⟩ : syracuseStep 1893965 = 710237) (by norm_num)
theorem B3196493 : Blo 1262449 3196493 := bbase (se 3 (by rfl) ⟨599342, by rfl⟩ : syracuseStep 3196493 = 1198685) (by norm_num)
theorem B2025037 : Blo 1262449 2025037 := bbase (se 3 (by rfl) ⟨379694, by rfl⟩ : syracuseStep 2025037 = 759389) (by norm_num)
theorem B1893989 : Blo 1262449 1893989 := bbase (se 4 (by rfl) ⟨177561, by rfl⟩ : syracuseStep 1893989 = 355123) (by norm_num)
theorem B2844269 : Blo 1262449 2844269 := bbase (se 3 (by rfl) ⟨533300, by rfl⟩ : syracuseStep 2844269 = 1066601) (by norm_num)
theorem B4556405 : Blo 1262449 4556405 := bbase (se 5 (by rfl) ⟨213581, by rfl⟩ : syracuseStep 4556405 = 427163) (by norm_num)
theorem B1599097 : Blo 1262449 1599097 := bbase (se 2 (by rfl) ⟨599661, by rfl⟩ : syracuseStep 1599097 = 1199323) (by norm_num)
theorem B1894013 : Blo 1262449 1894013 := bbase (se 3 (by rfl) ⟨355127, by rfl⟩ : syracuseStep 1894013 = 710255) (by norm_num)
theorem B2131589 : Blo 1262449 2131589 := bbase (se 4 (by rfl) ⟨199836, by rfl⟩ : syracuseStep 2131589 = 399673) (by norm_num)
theorem B1894037 : Blo 1262449 1894037 := bbase (se 6 (by rfl) ⟨44391, by rfl⟩ : syracuseStep 1894037 = 88783) (by norm_num)
theorem B2107037 : Blo 1262449 2107037 := bbase (se 3 (by rfl) ⟨395069, by rfl⟩ : syracuseStep 2107037 = 790139) (by norm_num)
theorem B1894061 : Blo 1262449 1894061 := bbase (se 3 (by rfl) ⟨355136, by rfl⟩ : syracuseStep 1894061 = 710273) (by norm_num)
theorem B2844341 : Blo 1262449 2844341 := bbase (se 5 (by rfl) ⟨133328, by rfl⟩ : syracuseStep 2844341 = 266657) (by norm_num)
theorem B1894085 : Blo 1262449 1894085 := bbase (se 4 (by rfl) ⟨177570, by rfl⟩ : syracuseStep 1894085 = 355141) (by norm_num)
theorem B37422805 : Blo 1262449 37422805 := bbase (se 7 (by rfl) ⟨438548, by rfl⟩ : syracuseStep 37422805 = 877097) (by norm_num)
theorem B1599193 : Blo 1262449 1599193 := bbase (se 2 (by rfl) ⟨599697, by rfl⟩ : syracuseStep 1599193 = 1199395) (by norm_num)
theorem B1894109 : Blo 1262449 1894109 := bbase (se 3 (by rfl) ⟨355145, by rfl⟩ : syracuseStep 1894109 = 710291) (by norm_num)
theorem B1894133 : Blo 1262449 1894133 := bbase (se 5 (by rfl) ⟨88787, by rfl⟩ : syracuseStep 1894133 = 177575) (by norm_num)
theorem B2844413 : Blo 1262449 2844413 := bbase (se 3 (by rfl) ⟨533327, by rfl⟩ : syracuseStep 2844413 = 1066655) (by norm_num)
theorem B2131717 : Blo 1262449 2131717 := bbase (se 4 (by rfl) ⟨199848, by rfl⟩ : syracuseStep 2131717 = 399697) (by norm_num)
theorem B1894157 : Blo 1262449 1894157 := bbase (se 3 (by rfl) ⟨355154, by rfl⟩ : syracuseStep 1894157 = 710309) (by norm_num)
theorem B3196685 : Blo 1262449 3196685 := bbase (se 3 (by rfl) ⟨599378, by rfl⟩ : syracuseStep 3196685 = 1198757) (by norm_num)
theorem B4859669 : Blo 1262449 4859669 := bbase (se 6 (by rfl) ⟨113898, by rfl⟩ : syracuseStep 4859669 = 227797) (by norm_num)
theorem B2696981 : Blo 1262449 2696981 := bbase (se 6 (by rfl) ⟨63210, by rfl⟩ : syracuseStep 2696981 = 126421) (by norm_num)
theorem B1894181 : Blo 1262449 1894181 := bbase (se 4 (by rfl) ⟨177579, by rfl⟩ : syracuseStep 1894181 = 355159) (by norm_num)
theorem B1894205 : Blo 1262449 1894205 := bbase (se 3 (by rfl) ⟨355163, by rfl⟩ : syracuseStep 1894205 = 710327) (by norm_num)
theorem B2844485 : Blo 1262449 2844485 := bbase (se 4 (by rfl) ⟨266670, by rfl⟩ : syracuseStep 2844485 = 533341) (by norm_num)
theorem B1894229 : Blo 1262449 1894229 := bbase (se 9 (by rfl) ⟨5549, by rfl⟩ : syracuseStep 1894229 = 11099) (by norm_num)
theorem B2131805 : Blo 1262449 2131805 := bbase (se 3 (by rfl) ⟨399713, by rfl⟩ : syracuseStep 2131805 = 799427) (by norm_num)
theorem B4261733 : Blo 1262449 4261733 := bbase (se 4 (by rfl) ⟨399537, by rfl⟩ : syracuseStep 4261733 = 799075) (by norm_num)
theorem B1894253 : Blo 1262449 1894253 := bbase (se 3 (by rfl) ⟨355172, by rfl⟩ : syracuseStep 1894253 = 710345) (by norm_num)
theorem B1894277 : Blo 1262449 1894277 := bbase (se 4 (by rfl) ⟨177588, by rfl⟩ : syracuseStep 1894277 = 355177) (by norm_num)
theorem B1599365 : Blo 1262449 1599365 := bbase (se 4 (by rfl) ⟨149940, by rfl⟩ : syracuseStep 1599365 = 299881) (by norm_num)
theorem B2844557 : Blo 1262449 2844557 := bbase (se 3 (by rfl) ⟨533354, by rfl⟩ : syracuseStep 2844557 = 1066709) (by norm_num)
theorem B1894301 : Blo 1262449 1894301 := bbase (se 3 (by rfl) ⟨355181, by rfl⟩ : syracuseStep 1894301 = 710363) (by norm_num)
theorem B4048805 : Blo 1262449 4048805 := bbase (se 4 (by rfl) ⟨379575, by rfl⟩ : syracuseStep 4048805 = 759151) (by norm_num)
theorem B1894325 : Blo 1262449 1894325 := bbase (se 5 (by rfl) ⟨88796, by rfl⟩ : syracuseStep 1894325 = 177593) (by norm_num)
theorem B1460153 : Blo 1262449 1460153 := bbase (se 2 (by rfl) ⟨547557, by rfl⟩ : syracuseStep 1460153 = 1095115) (by norm_num)
theorem B1599421 : Blo 1262449 1599421 := bbase (se 3 (by rfl) ⟨299891, by rfl⟩ : syracuseStep 1599421 = 599783) (by norm_num)
theorem B1894349 : Blo 1262449 1894349 := bbase (se 3 (by rfl) ⟨355190, by rfl⟩ : syracuseStep 1894349 = 710381) (by norm_num)
theorem B2844629 : Blo 1262449 2844629 := bbase (se 7 (by rfl) ⟨33335, by rfl⟩ : syracuseStep 2844629 = 66671) (by norm_num)
theorem B2131933 : Blo 1262449 2131933 := bbase (se 3 (by rfl) ⟨399737, by rfl⟩ : syracuseStep 2131933 = 799475) (by norm_num)
theorem B1894373 : Blo 1262449 1894373 := bbase (se 4 (by rfl) ⟨177597, by rfl⟩ : syracuseStep 1894373 = 355195) (by norm_num)
theorem B1894397 : Blo 1262449 1894397 := bbase (se 3 (by rfl) ⟨355199, by rfl⟩ : syracuseStep 1894397 = 710399) (by norm_num)
theorem B2697221 : Blo 1262449 2697221 := bbase (se 4 (by rfl) ⟨252864, by rfl⟩ : syracuseStep 2697221 = 505729) (by norm_num)
theorem B1894421 : Blo 1262449 1894421 := bbase (se 6 (by rfl) ⟨44400, by rfl⟩ : syracuseStep 1894421 = 88801) (by norm_num)
theorem B1599517 : Blo 1262449 1599517 := bbase (se 3 (by rfl) ⟨299909, by rfl⟩ : syracuseStep 1599517 = 599819) (by norm_num)
theorem B2844701 : Blo 1262449 2844701 := bbase (se 3 (by rfl) ⟨533381, by rfl⟩ : syracuseStep 2844701 = 1066763) (by norm_num)
theorem B4556837 : Blo 1262449 4556837 := bbase (se 4 (by rfl) ⟨427203, by rfl⟩ : syracuseStep 4556837 = 854407) (by norm_num)
theorem B1894445 : Blo 1262449 1894445 := bbase (se 3 (by rfl) ⟨355208, by rfl⟩ : syracuseStep 1894445 = 710417) (by norm_num)
theorem B2132021 : Blo 1262449 2132021 := bbase (se 5 (by rfl) ⟨99938, by rfl⟩ : syracuseStep 2132021 = 199877) (by norm_num)
theorem B1894469 : Blo 1262449 1894469 := bbase (se 4 (by rfl) ⟨177606, by rfl⟩ : syracuseStep 1894469 = 355213) (by norm_num)
theorem B1894493 : Blo 1262449 1894493 := bbase (se 3 (by rfl) ⟨355217, by rfl⟩ : syracuseStep 1894493 = 710435) (by norm_num)
theorem B3197029 : Blo 1262449 3197029 := bbase (se 4 (by rfl) ⟨299721, by rfl⟩ : syracuseStep 3197029 = 599443) (by norm_num)
theorem B2844773 : Blo 1262449 2844773 := bbase (se 4 (by rfl) ⟨266697, by rfl⟩ : syracuseStep 2844773 = 533395) (by norm_num)
theorem B1894517 : Blo 1262449 1894517 := bbase (se 5 (by rfl) ⟨88805, by rfl⟩ : syracuseStep 1894517 = 177611) (by norm_num)
theorem B6400133 : Blo 1262449 6400133 := bbase (se 4 (by rfl) ⟨600012, by rfl⟩ : syracuseStep 6400133 = 1200025) (by norm_num)
theorem B1894541 : Blo 1262449 1894541 := bbase (se 3 (by rfl) ⟨355226, by rfl⟩ : syracuseStep 1894541 = 710453) (by norm_num)
theorem B1517725 : Blo 1262449 1517725 := bbase (se 3 (by rfl) ⟨284573, by rfl⟩ : syracuseStep 1517725 = 569147) (by norm_num)
theorem B1894565 : Blo 1262449 1894565 := bbase (se 4 (by rfl) ⟨177615, by rfl⟩ : syracuseStep 1894565 = 355231) (by norm_num)
theorem B2844845 : Blo 1262449 2844845 := bbase (se 3 (by rfl) ⟨533408, by rfl⟩ : syracuseStep 2844845 = 1066817) (by norm_num)
theorem B2132149 : Blo 1262449 2132149 := bbase (se 5 (by rfl) ⟨99944, by rfl⟩ : syracuseStep 2132149 = 199889) (by norm_num)
theorem B1894589 : Blo 1262449 1894589 := bbase (se 3 (by rfl) ⟨355235, by rfl⟩ : syracuseStep 1894589 = 710471) (by norm_num)
theorem B1599689 : Blo 1262449 1599689 := bbase (se 2 (by rfl) ⟨599883, by rfl⟩ : syracuseStep 1599689 = 1199767) (by norm_num)
theorem B3197141 : Blo 1262449 3197141 := bbase (se 7 (by rfl) ⟨37466, by rfl⟩ : syracuseStep 3197141 = 74933) (by norm_num)
theorem B1894613 : Blo 1262449 1894613 := bbase (se 7 (by rfl) ⟨22202, by rfl⟩ : syracuseStep 1894613 = 44405) (by norm_num)
theorem B1894637 : Blo 1262449 1894637 := bbase (se 3 (by rfl) ⟨355244, by rfl⟩ : syracuseStep 1894637 = 710489) (by norm_num)
theorem B1730797 : Blo 1262449 1730797 := bbase (se 3 (by rfl) ⟨324524, by rfl⟩ : syracuseStep 1730797 = 649049) (by norm_num)
theorem B2844917 : Blo 1262449 2844917 := bbase (se 5 (by rfl) ⟨133355, by rfl⟩ : syracuseStep 2844917 = 266711) (by norm_num)
theorem B1599745 : Blo 1262449 1599745 := bbase (se 2 (by rfl) ⟨599904, by rfl⟩ : syracuseStep 1599745 = 1199809) (by norm_num)
theorem B1894661 : Blo 1262449 1894661 := bbase (se 4 (by rfl) ⟨177624, by rfl⟩ : syracuseStep 1894661 = 355249) (by norm_num)
theorem B2132237 : Blo 1262449 2132237 := bbase (se 3 (by rfl) ⟨399794, by rfl⟩ : syracuseStep 2132237 = 799589) (by norm_num)
theorem B4262165 : Blo 1262449 4262165 := bbase (se 6 (by rfl) ⟨99894, by rfl⟩ : syracuseStep 4262165 = 199789) (by norm_num)
theorem B1894685 : Blo 1262449 1894685 := bbase (se 3 (by rfl) ⟨355253, by rfl⟩ : syracuseStep 1894685 = 710507) (by norm_num)
theorem B1280305 : Blo 1262449 1280305 := bbase (se 2 (by rfl) ⟨480114, by rfl⟩ : syracuseStep 1280305 = 960229) (by norm_num)
theorem B1894709 : Blo 1262449 1894709 := bbase (se 5 (by rfl) ⟨88814, by rfl⟩ : syracuseStep 1894709 = 177629) (by norm_num)
theorem B2844989 : Blo 1262449 2844989 := bbase (se 3 (by rfl) ⟨533435, by rfl⟩ : syracuseStep 2844989 = 1066871) (by norm_num)
theorem B3033413 : Blo 1262449 3033413 := bbase (se 4 (by rfl) ⟨284382, by rfl⟩ : syracuseStep 3033413 = 568765) (by norm_num)
theorem B1894733 : Blo 1262449 1894733 := bbase (se 3 (by rfl) ⟨355262, by rfl⟩ : syracuseStep 1894733 = 710525) (by norm_num)
theorem B1599841 : Blo 1262449 1599841 := bbase (se 2 (by rfl) ⟨599940, by rfl⟩ : syracuseStep 1599841 = 1199881) (by norm_num)
theorem B1894757 : Blo 1262449 1894757 := bbase (se 4 (by rfl) ⟨177633, by rfl⟩ : syracuseStep 1894757 = 355267) (by norm_num)
theorem B1894781 : Blo 1262449 1894781 := bbase (se 3 (by rfl) ⟨355271, by rfl⟩ : syracuseStep 1894781 = 710543) (by norm_num)
theorem B2132365 : Blo 1262449 2132365 := bbase (se 3 (by rfl) ⟨399818, by rfl⟩ : syracuseStep 2132365 = 799637) (by norm_num)
theorem B3197333 : Blo 1262449 3197333 := bbase (se 6 (by rfl) ⟨74937, by rfl⟩ : syracuseStep 3197333 = 149875) (by norm_num)
theorem B1894805 : Blo 1262449 1894805 := bbase (se 6 (by rfl) ⟨44409, by rfl⟩ : syracuseStep 1894805 = 88819) (by norm_num)
theorem B1894829 : Blo 1262449 1894829 := bbase (se 3 (by rfl) ⟨355280, by rfl⟩ : syracuseStep 1894829 = 710561) (by norm_num)
theorem B1894853 : Blo 1262449 1894853 := bbase (se 4 (by rfl) ⟨177642, by rfl⟩ : syracuseStep 1894853 = 355285) (by norm_num)
theorem B3598789 : Blo 1262449 3598789 := bbase (se 4 (by rfl) ⟨337386, by rfl⟩ : syracuseStep 3598789 = 674773) (by norm_num)
theorem B1894877 : Blo 1262449 1894877 := bbase (se 3 (by rfl) ⟨355289, by rfl⟩ : syracuseStep 1894877 = 710579) (by norm_num)
theorem B2132453 : Blo 1262449 2132453 := bbase (se 4 (by rfl) ⟨199917, by rfl⟩ : syracuseStep 2132453 = 399835) (by norm_num)
theorem B1894901 : Blo 1262449 1894901 := bbase (se 5 (by rfl) ⟨88823, by rfl⟩ : syracuseStep 1894901 = 177647) (by norm_num)
theorem B6072821 : Blo 1262449 6072821 := bbase (se 5 (by rfl) ⟨284663, by rfl⟩ : syracuseStep 6072821 = 569327) (by norm_num)
theorem B2697725 : Blo 1262449 2697725 := bbase (se 3 (by rfl) ⟨505823, by rfl⟩ : syracuseStep 2697725 = 1011647) (by norm_num)
theorem B3033605 : Blo 1262449 3033605 := bbase (se 4 (by rfl) ⟨284400, by rfl⟩ : syracuseStep 3033605 = 568801) (by norm_num)
theorem B2697733 : Blo 1262449 2697733 := bbase (se 4 (by rfl) ⟨252912, by rfl⟩ : syracuseStep 2697733 = 505825) (by norm_num)
theorem B1894925 : Blo 1262449 1894925 := bbase (se 3 (by rfl) ⟨355298, by rfl⟩ : syracuseStep 1894925 = 710597) (by norm_num)
theorem B1600013 : Blo 1262449 1600013 := bbase (se 3 (by rfl) ⟨300002, by rfl⟩ : syracuseStep 1600013 = 600005) (by norm_num)
theorem B6392357 : Blo 1262449 6392357 := bbase (se 4 (by rfl) ⟨599283, by rfl⟩ : syracuseStep 6392357 = 1198567) (by norm_num)
theorem B1894949 : Blo 1262449 1894949 := bbase (se 4 (by rfl) ⟨177651, by rfl⟩ : syracuseStep 1894949 = 355303) (by norm_num)
theorem B1919533 : Blo 1262449 1919533 := bbase (se 3 (by rfl) ⟨359912, by rfl⟩ : syracuseStep 1919533 = 719825) (by norm_num)
theorem B1894973 : Blo 1262449 1894973 := bbase (se 3 (by rfl) ⟨355307, by rfl⟩ : syracuseStep 1894973 = 710615) (by norm_num)
theorem B1600069 : Blo 1262449 1600069 := bbase (se 4 (by rfl) ⟨150006, by rfl⟩ : syracuseStep 1600069 = 300013) (by norm_num)
theorem B1894997 : Blo 1262449 1894997 := bbase (se 8 (by rfl) ⟨11103, by rfl⟩ : syracuseStep 1894997 = 22207) (by norm_num)
theorem B2132581 : Blo 1262449 2132581 := bbase (se 4 (by rfl) ⟨199929, by rfl⟩ : syracuseStep 2132581 = 399859) (by norm_num)
theorem B1895021 : Blo 1262449 1895021 := bbase (se 3 (by rfl) ⟨355316, by rfl⟩ : syracuseStep 1895021 = 710633) (by norm_num)
theorem B4794997 : Blo 1262449 4794997 := bbase (se 5 (by rfl) ⟨224765, by rfl⟩ : syracuseStep 4794997 = 449531) (by norm_num)
theorem B1895045 : Blo 1262449 1895045 := bbase (se 4 (by rfl) ⟨177660, by rfl⟩ : syracuseStep 1895045 = 355321) (by norm_num)
theorem B1895069 : Blo 1262449 1895069 := bbase (se 3 (by rfl) ⟨355325, by rfl⟩ : syracuseStep 1895069 = 710651) (by norm_num)
theorem B1600165 : Blo 1262449 1600165 := bbase (se 4 (by rfl) ⟨150015, by rfl⟩ : syracuseStep 1600165 = 300031) (by norm_num)
theorem B1895093 : Blo 1262449 1895093 := bbase (se 5 (by rfl) ⟨88832, by rfl⟩ : syracuseStep 1895093 = 177665) (by norm_num)
theorem B2132669 : Blo 1262449 2132669 := bbase (se 3 (by rfl) ⟨399875, by rfl⟩ : syracuseStep 2132669 = 799751) (by norm_num)
theorem B4262597 : Blo 1262449 4262597 := bbase (se 4 (by rfl) ⟨399618, by rfl⟩ : syracuseStep 4262597 = 799237) (by norm_num)
theorem B1895117 : Blo 1262449 1895117 := bbase (se 3 (by rfl) ⟨355334, by rfl⟩ : syracuseStep 1895117 = 710669) (by norm_num)
theorem B1895141 : Blo 1262449 1895141 := bbase (se 4 (by rfl) ⟨177669, by rfl⟩ : syracuseStep 1895141 = 355339) (by norm_num)
theorem B3197677 : Blo 1262449 3197677 := bbase (se 3 (by rfl) ⟨599564, by rfl⟩ : syracuseStep 3197677 = 1199129) (by norm_num)
theorem B1895165 : Blo 1262449 1895165 := bbase (se 3 (by rfl) ⟨355343, by rfl⟩ : syracuseStep 1895165 = 710687) (by norm_num)
theorem B1895189 : Blo 1262449 1895189 := bbase (se 6 (by rfl) ⟨44418, by rfl⟩ : syracuseStep 1895189 = 88837) (by norm_num)
theorem B3033893 : Blo 1262449 3033893 := bbase (se 4 (by rfl) ⟨284427, by rfl⟩ : syracuseStep 3033893 = 568855) (by norm_num)
theorem B1895213 : Blo 1262449 1895213 := bbase (se 3 (by rfl) ⟨355352, by rfl⟩ : syracuseStep 1895213 = 710705) (by norm_num)
theorem B2132797 : Blo 1262449 2132797 := bbase (se 3 (by rfl) ⟨399899, by rfl⟩ : syracuseStep 2132797 = 799799) (by norm_num)
theorem B1895237 : Blo 1262449 1895237 := bbase (se 4 (by rfl) ⟨177678, by rfl⟩ : syracuseStep 1895237 = 355357) (by norm_num)
theorem B3197789 : Blo 1262449 3197789 := bbase (se 3 (by rfl) ⟨599585, by rfl⟩ : syracuseStep 3197789 = 1199171) (by norm_num)
theorem B1895261 : Blo 1262449 1895261 := bbase (se 3 (by rfl) ⟨355361, by rfl⟩ : syracuseStep 1895261 = 710723) (by norm_num)
theorem B1895285 : Blo 1262449 1895285 := bbase (se 5 (by rfl) ⟨88841, by rfl⟩ : syracuseStep 1895285 = 177683) (by norm_num)
theorem B1895309 : Blo 1262449 1895309 := bbase (se 3 (by rfl) ⟨355370, by rfl⟩ : syracuseStep 1895309 = 710741) (by norm_num)
theorem B2132885 : Blo 1262449 2132885 := bbase (se 6 (by rfl) ⟨49989, by rfl⟩ : syracuseStep 2132885 = 99979) (by norm_num)
theorem B4795301 : Blo 1262449 4795301 := bbase (se 4 (by rfl) ⟨449559, by rfl⟩ : syracuseStep 4795301 = 899119) (by norm_num)
theorem B1895333 : Blo 1262449 1895333 := bbase (se 4 (by rfl) ⟨177687, by rfl⟩ : syracuseStep 1895333 = 355375) (by norm_num)
theorem B1895357 : Blo 1262449 1895357 := bbase (se 3 (by rfl) ⟨355379, by rfl⟩ : syracuseStep 1895357 = 710759) (by norm_num)
theorem B1895381 : Blo 1262449 1895381 := bbase (se 7 (by rfl) ⟨22211, by rfl⟩ : syracuseStep 1895381 = 44423) (by norm_num)
theorem B1895405 : Blo 1262449 1895405 := bbase (se 3 (by rfl) ⟨355388, by rfl⟩ : syracuseStep 1895405 = 710777) (by norm_num)
theorem B1420285 : Blo 1262449 1420285 := bbase (se 3 (by rfl) ⟨266303, by rfl⟩ : syracuseStep 1420285 = 532607) (by norm_num)
theorem B1895429 : Blo 1262449 1895429 := bbase (se 4 (by rfl) ⟨177696, by rfl⟩ : syracuseStep 1895429 = 355393) (by norm_num)
theorem B2133013 : Blo 1262449 2133013 := bbase (se 6 (by rfl) ⟨49992, by rfl⟩ : syracuseStep 2133013 = 99985) (by norm_num)
theorem B3197981 : Blo 1262449 3197981 := bbase (se 3 (by rfl) ⟨599621, by rfl⟩ : syracuseStep 3197981 = 1199243) (by norm_num)
theorem B1895453 : Blo 1262449 1895453 := bbase (se 3 (by rfl) ⟨355397, by rfl⟩ : syracuseStep 1895453 = 710795) (by norm_num)
theorem B1420321 : Blo 1262449 1420321 := bbase (se 2 (by rfl) ⟨532620, by rfl⟩ : syracuseStep 1420321 = 1065241) (by norm_num)
theorem B1895477 : Blo 1262449 1895477 := bbase (se 5 (by rfl) ⟨88850, by rfl⟩ : syracuseStep 1895477 = 177701) (by norm_num)
theorem B1420357 : Blo 1262449 1420357 := bbase (se 4 (by rfl) ⟨133158, by rfl⟩ : syracuseStep 1420357 = 266317) (by norm_num)
theorem B1707085 : Blo 1262449 1707085 := bbase (se 3 (by rfl) ⟨320078, by rfl⟩ : syracuseStep 1707085 = 640157) (by norm_num)
theorem B1895501 : Blo 1262449 1895501 := bbase (se 3 (by rfl) ⟨355406, by rfl⟩ : syracuseStep 1895501 = 710813) (by norm_num)
theorem B1895525 : Blo 1262449 1895525 := bbase (se 4 (by rfl) ⟨177705, by rfl⟩ : syracuseStep 1895525 = 355411) (by norm_num)
theorem B1420393 : Blo 1262449 1420393 := bbase (se 2 (by rfl) ⟨532647, by rfl⟩ : syracuseStep 1420393 = 1065295) (by norm_num)
theorem B2133101 : Blo 1262449 2133101 := bbase (se 3 (by rfl) ⟨399956, by rfl⟩ : syracuseStep 2133101 = 799913) (by norm_num)
theorem B4263029 : Blo 1262449 4263029 := bbase (se 5 (by rfl) ⟨199829, by rfl⟩ : syracuseStep 4263029 = 399659) (by norm_num)
theorem B1895549 : Blo 1262449 1895549 := bbase (se 3 (by rfl) ⟨355415, by rfl⟩ : syracuseStep 1895549 = 710831) (by norm_num)
theorem B1420429 : Blo 1262449 1420429 := bbase (se 3 (by rfl) ⟨266330, by rfl⟩ : syracuseStep 1420429 = 532661) (by norm_num)
theorem B1895573 : Blo 1262449 1895573 := bbase (se 6 (by rfl) ⟨44427, by rfl⟩ : syracuseStep 1895573 = 88855) (by norm_num)
theorem B1895597 : Blo 1262449 1895597 := bbase (se 3 (by rfl) ⟨355424, by rfl⟩ : syracuseStep 1895597 = 710849) (by norm_num)
theorem B1420465 : Blo 1262449 1420465 := bbase (se 2 (by rfl) ⟨532674, by rfl⟩ : syracuseStep 1420465 = 1065349) (by norm_num)
theorem B1895621 : Blo 1262449 1895621 := bbase (se 4 (by rfl) ⟨177714, by rfl⟩ : syracuseStep 1895621 = 355429) (by norm_num)
theorem B1420501 : Blo 1262449 1420501 := bbase (se 7 (by rfl) ⟨16646, by rfl⟩ : syracuseStep 1420501 = 33293) (by norm_num)
theorem B5393621 : Blo 1262449 5393621 := bbase (se 7 (by rfl) ⟨63206, by rfl⟩ : syracuseStep 5393621 = 126413) (by norm_num)
theorem B1895645 : Blo 1262449 1895645 := bbase (se 3 (by rfl) ⟨355433, by rfl⟩ : syracuseStep 1895645 = 710867) (by norm_num)
theorem B2133229 : Blo 1262449 2133229 := bbase (se 3 (by rfl) ⟨399980, by rfl⟩ : syracuseStep 2133229 = 799961) (by norm_num)
theorem B1895669 : Blo 1262449 1895669 := bbase (se 5 (by rfl) ⟨88859, by rfl⟩ : syracuseStep 1895669 = 177719) (by norm_num)
theorem B1420537 : Blo 1262449 1420537 := bbase (se 2 (by rfl) ⟨532701, by rfl⟩ : syracuseStep 1420537 = 1065403) (by norm_num)
theorem B1895693 : Blo 1262449 1895693 := bbase (se 3 (by rfl) ⟨355442, by rfl⟩ : syracuseStep 1895693 = 710885) (by norm_num)
theorem B1518869 : Blo 1262449 1518869 := bbase (se 6 (by rfl) ⟨35598, by rfl⟩ : syracuseStep 1518869 = 71197) (by norm_num)
theorem B1420573 : Blo 1262449 1420573 := bbase (se 3 (by rfl) ⟨266357, by rfl⟩ : syracuseStep 1420573 = 532715) (by norm_num)
theorem B1895717 : Blo 1262449 1895717 := bbase (se 4 (by rfl) ⟨177723, by rfl⟩ : syracuseStep 1895717 = 355447) (by norm_num)
theorem B1895741 : Blo 1262449 1895741 := bbase (se 3 (by rfl) ⟨355451, by rfl⟩ : syracuseStep 1895741 = 710903) (by norm_num)
theorem B1420609 : Blo 1262449 1420609 := bbase (se 2 (by rfl) ⟨532728, by rfl⟩ : syracuseStep 1420609 = 1065457) (by norm_num)
theorem B2133317 : Blo 1262449 2133317 := bbase (se 4 (by rfl) ⟨199998, by rfl⟩ : syracuseStep 2133317 = 399997) (by norm_num)
theorem B1518917 : Blo 1262449 1518917 := bbase (se 4 (by rfl) ⟨142398, by rfl⟩ : syracuseStep 1518917 = 284797) (by norm_num)
theorem B1895765 : Blo 1262449 1895765 := bbase (se 11 (by rfl) ⟨1388, by rfl⟩ : syracuseStep 1895765 = 2777) (by norm_num)
theorem B1420645 : Blo 1262449 1420645 := bbase (se 4 (by rfl) ⟨133185, by rfl⟩ : syracuseStep 1420645 = 266371) (by norm_num)
theorem B1895789 : Blo 1262449 1895789 := bbase (se 3 (by rfl) ⟨355460, by rfl⟩ : syracuseStep 1895789 = 710921) (by norm_num)
theorem B3198325 : Blo 1262449 3198325 := bbase (se 5 (by rfl) ⟨149921, by rfl⟩ : syracuseStep 3198325 = 299843) (by norm_num)
theorem B1895813 : Blo 1262449 1895813 := bbase (se 4 (by rfl) ⟨177732, by rfl⟩ : syracuseStep 1895813 = 355465) (by norm_num)
theorem B1420681 : Blo 1262449 1420681 := bbase (se 2 (by rfl) ⟨532755, by rfl⟩ : syracuseStep 1420681 = 1065511) (by norm_num)
theorem B1895837 : Blo 1262449 1895837 := bbase (se 3 (by rfl) ⟨355469, by rfl⟩ : syracuseStep 1895837 = 710939) (by norm_num)
theorem B1519013 : Blo 1262449 1519013 := bbase (se 4 (by rfl) ⟨142407, by rfl⟩ : syracuseStep 1519013 = 284815) (by norm_num)
theorem B1420717 : Blo 1262449 1420717 := bbase (se 3 (by rfl) ⟨266384, by rfl⟩ : syracuseStep 1420717 = 532769) (by norm_num)
theorem B1895861 : Blo 1262449 1895861 := bbase (se 5 (by rfl) ⟨88868, by rfl⟩ : syracuseStep 1895861 = 177737) (by norm_num)
theorem B5393861 : Blo 1262449 5393861 := bbase (se 4 (by rfl) ⟨505674, by rfl⟩ : syracuseStep 5393861 = 1011349) (by norm_num)
theorem B2133445 : Blo 1262449 2133445 := bbase (se 4 (by rfl) ⟨200010, by rfl⟩ : syracuseStep 2133445 = 400021) (by norm_num)
theorem B1895885 : Blo 1262449 1895885 := bbase (se 3 (by rfl) ⟨355478, by rfl⟩ : syracuseStep 1895885 = 710957) (by norm_num)
theorem B1420753 : Blo 1262449 1420753 := bbase (se 2 (by rfl) ⟨532782, by rfl⟩ : syracuseStep 1420753 = 1065565) (by norm_num)
theorem B1797589 : Blo 1262449 1797589 := bbase (se 7 (by rfl) ⟨21065, by rfl⟩ : syracuseStep 1797589 = 42131) (by norm_num)
theorem B44330453 : Blo 1262449 44330453 := bbase (se 7 (by rfl) ⟨519497, by rfl⟩ : syracuseStep 44330453 = 1038995) (by norm_num)
theorem B6237653 : Blo 1262449 6237653 := bbase (se 7 (by rfl) ⟨73097, by rfl⟩ : syracuseStep 6237653 = 146195) (by norm_num)
theorem B1281505 : Blo 1262449 1281505 := bbase (se 2 (by rfl) ⟨480564, by rfl⟩ : syracuseStep 1281505 = 961129) (by norm_num)
theorem B3198437 : Blo 1262449 3198437 := bbase (se 4 (by rfl) ⟨299853, by rfl⟩ : syracuseStep 3198437 = 599707) (by norm_num)
theorem B1895909 : Blo 1262449 1895909 := bbase (se 4 (by rfl) ⟨177741, by rfl⟩ : syracuseStep 1895909 = 355483) (by norm_num)
theorem B1420789 : Blo 1262449 1420789 := bbase (se 5 (by rfl) ⟨66599, by rfl⟩ : syracuseStep 1420789 = 133199) (by norm_num)
theorem B7687669 : Blo 1262449 7687669 := bbase (se 5 (by rfl) ⟨360359, by rfl⟩ : syracuseStep 7687669 = 720719) (by norm_num)
theorem B1895933 : Blo 1262449 1895933 := bbase (se 3 (by rfl) ⟨355487, by rfl⟩ : syracuseStep 1895933 = 710975) (by norm_num)
theorem B1895957 : Blo 1262449 1895957 := bbase (se 6 (by rfl) ⟨44436, by rfl⟩ : syracuseStep 1895957 = 88873) (by norm_num)
theorem B3599893 : Blo 1262449 3599893 := bbase (se 6 (by rfl) ⟨84372, by rfl⟩ : syracuseStep 3599893 = 168745) (by norm_num)
theorem B1420825 : Blo 1262449 1420825 := bbase (se 2 (by rfl) ⟨532809, by rfl⟩ : syracuseStep 1420825 = 1065619) (by norm_num)
theorem B2133533 : Blo 1262449 2133533 := bbase (se 3 (by rfl) ⟨400037, by rfl⟩ : syracuseStep 2133533 = 800075) (by norm_num)
theorem B4263461 : Blo 1262449 4263461 := bbase (se 4 (by rfl) ⟨399699, by rfl⟩ : syracuseStep 4263461 = 799399) (by norm_num)
theorem B1895981 : Blo 1262449 1895981 := bbase (se 3 (by rfl) ⟨355496, by rfl⟩ : syracuseStep 1895981 = 710993) (by norm_num)
theorem B1420861 : Blo 1262449 1420861 := bbase (se 3 (by rfl) ⟨266411, by rfl⟩ : syracuseStep 1420861 = 532823) (by norm_num)
theorem B1896005 : Blo 1262449 1896005 := bbase (se 4 (by rfl) ⟨177750, by rfl⟩ : syracuseStep 1896005 = 355501) (by norm_num)
theorem B1797709 : Blo 1262449 1797709 := bbase (se 3 (by rfl) ⟨337070, by rfl⟩ : syracuseStep 1797709 = 674141) (by norm_num)
theorem B1896029 : Blo 1262449 1896029 := bbase (se 3 (by rfl) ⟨355505, by rfl⟩ : syracuseStep 1896029 = 711011) (by norm_num)
theorem B1420897 : Blo 1262449 1420897 := bbase (se 2 (by rfl) ⟨532836, by rfl⟩ : syracuseStep 1420897 = 1065673) (by norm_num)
theorem B2698861 : Blo 1262449 2698861 := bbase (se 3 (by rfl) ⟨506036, by rfl⟩ : syracuseStep 2698861 = 1012073) (by norm_num)
theorem B1896053 : Blo 1262449 1896053 := bbase (se 5 (by rfl) ⟨88877, by rfl⟩ : syracuseStep 1896053 = 177755) (by norm_num)
theorem B1420933 : Blo 1262449 1420933 := bbase (se 4 (by rfl) ⟨133212, by rfl⟩ : syracuseStep 1420933 = 266425) (by norm_num)
theorem B1896077 : Blo 1262449 1896077 := bbase (se 3 (by rfl) ⟨355514, by rfl⟩ : syracuseStep 1896077 = 711029) (by norm_num)
theorem B2133661 : Blo 1262449 2133661 := bbase (se 3 (by rfl) ⟨400061, by rfl⟩ : syracuseStep 2133661 = 800123) (by norm_num)
theorem B3198629 : Blo 1262449 3198629 := bbase (se 4 (by rfl) ⟨299871, by rfl⟩ : syracuseStep 3198629 = 599743) (by norm_num)
theorem B1896101 : Blo 1262449 1896101 := bbase (se 4 (by rfl) ⟨177759, by rfl⟩ : syracuseStep 1896101 = 355519) (by norm_num)
theorem B1420969 : Blo 1262449 1420969 := bbase (se 2 (by rfl) ⟨532863, by rfl⟩ : syracuseStep 1420969 = 1065727) (by norm_num)
theorem B1797805 : Blo 1262449 1797805 := bbase (se 3 (by rfl) ⟨337088, by rfl⟩ : syracuseStep 1797805 = 674177) (by norm_num)
theorem B1896125 : Blo 1262449 1896125 := bbase (se 3 (by rfl) ⟨355523, by rfl⟩ : syracuseStep 1896125 = 711047) (by norm_num)
theorem B1421005 : Blo 1262449 1421005 := bbase (se 3 (by rfl) ⟨266438, by rfl⟩ : syracuseStep 1421005 = 532877) (by norm_num)
theorem B18706133 : Blo 1262449 18706133 := bbase (se 7 (by rfl) ⟨219212, by rfl⟩ : syracuseStep 18706133 = 438425) (by norm_num)
theorem B1896149 : Blo 1262449 1896149 := bbase (se 7 (by rfl) ⟨22220, by rfl⟩ : syracuseStep 1896149 = 44441) (by norm_num)
theorem B1896173 : Blo 1262449 1896173 := bbase (se 3 (by rfl) ⟨355532, by rfl⟩ : syracuseStep 1896173 = 711065) (by norm_num)
theorem B1421041 : Blo 1262449 1421041 := bbase (se 2 (by rfl) ⟨532890, by rfl⟩ : syracuseStep 1421041 = 1065781) (by norm_num)
theorem B2133749 : Blo 1262449 2133749 := bbase (se 5 (by rfl) ⟨100019, by rfl⟩ : syracuseStep 2133749 = 200039) (by norm_num)
theorem B1896197 : Blo 1262449 1896197 := bbase (se 4 (by rfl) ⟨177768, by rfl⟩ : syracuseStep 1896197 = 355537) (by norm_num)
theorem B1421077 : Blo 1262449 1421077 := bbase (se 6 (by rfl) ⟨33306, by rfl⟩ : syracuseStep 1421077 = 66613) (by norm_num)
theorem B1896221 : Blo 1262449 1896221 := bbase (se 3 (by rfl) ⟨355541, by rfl⟩ : syracuseStep 1896221 = 711083) (by norm_num)
theorem B6393653 : Blo 1262449 6393653 := bbase (se 5 (by rfl) ⟨299702, by rfl⟩ : syracuseStep 6393653 = 599405) (by norm_num)
theorem B1896245 : Blo 1262449 1896245 := bbase (se 5 (by rfl) ⟨88886, by rfl⟩ : syracuseStep 1896245 = 177773) (by norm_num)
theorem B1421113 : Blo 1262449 1421113 := bbase (se 2 (by rfl) ⟨532917, by rfl⟩ : syracuseStep 1421113 = 1065835) (by norm_num)
theorem B1896269 : Blo 1262449 1896269 := bbase (se 3 (by rfl) ⟨355550, by rfl⟩ : syracuseStep 1896269 = 711101) (by norm_num)
theorem B1421149 : Blo 1262449 1421149 := bbase (se 3 (by rfl) ⟨266465, by rfl⟩ : syracuseStep 1421149 = 532931) (by norm_num)
theorem B1896293 : Blo 1262449 1896293 := bbase (se 4 (by rfl) ⟨177777, by rfl⟩ : syracuseStep 1896293 = 355555) (by norm_num)
theorem B1896317 : Blo 1262449 1896317 := bbase (se 3 (by rfl) ⟨355559, by rfl⟩ : syracuseStep 1896317 = 711119) (by norm_num)
theorem B1421185 : Blo 1262449 1421185 := bbase (se 2 (by rfl) ⟨532944, by rfl⟩ : syracuseStep 1421185 = 1065889) (by norm_num)
theorem B1896341 : Blo 1262449 1896341 := bbase (se 6 (by rfl) ⟨44445, by rfl⟩ : syracuseStep 1896341 = 88891) (by norm_num)
theorem B1421221 : Blo 1262449 1421221 := bbase (se 4 (by rfl) ⟨133239, by rfl⟩ : syracuseStep 1421221 = 266479) (by norm_num)
theorem B1707949 : Blo 1262449 1707949 := bbase (se 3 (by rfl) ⟨320240, by rfl⟩ : syracuseStep 1707949 = 640481) (by norm_num)
theorem B1896365 : Blo 1262449 1896365 := bbase (se 3 (by rfl) ⟨355568, by rfl⟩ : syracuseStep 1896365 = 711137) (by norm_num)
theorem B7196597 : Blo 1262449 7196597 := bbase (se 5 (by rfl) ⟨337340, by rfl⟩ : syracuseStep 7196597 = 674681) (by norm_num)
theorem B1896389 : Blo 1262449 1896389 := bbase (se 4 (by rfl) ⟨177786, by rfl⟩ : syracuseStep 1896389 = 355573) (by norm_num)
theorem B1421257 : Blo 1262449 1421257 := bbase (se 2 (by rfl) ⟨532971, by rfl⟩ : syracuseStep 1421257 = 1065943) (by norm_num)
theorem B4263893 : Blo 1262449 4263893 := bbase (se 7 (by rfl) ⟨49967, by rfl⟩ : syracuseStep 4263893 = 99935) (by norm_num)
theorem B1896413 : Blo 1262449 1896413 := bbase (se 3 (by rfl) ⟨355577, by rfl⟩ : syracuseStep 1896413 = 711155) (by norm_num)
theorem B2699237 : Blo 1262449 2699237 := bbase (se 4 (by rfl) ⟨253053, by rfl⟩ : syracuseStep 2699237 = 506107) (by norm_num)
theorem B1421293 : Blo 1262449 1421293 := bbase (se 3 (by rfl) ⟨266492, by rfl⟩ : syracuseStep 1421293 = 532985) (by norm_num)
theorem B1896437 : Blo 1262449 1896437 := bbase (se 5 (by rfl) ⟨88895, by rfl⟩ : syracuseStep 1896437 = 177791) (by norm_num)
theorem B3198973 : Blo 1262449 3198973 := bbase (se 3 (by rfl) ⟨599807, by rfl⟩ : syracuseStep 3198973 = 1199615) (by norm_num)
theorem B1896461 : Blo 1262449 1896461 := bbase (se 3 (by rfl) ⟨355586, by rfl⟩ : syracuseStep 1896461 = 711173) (by norm_num)
theorem B1421329 : Blo 1262449 1421329 := bbase (se 2 (by rfl) ⟨532998, by rfl⟩ : syracuseStep 1421329 = 1065997) (by norm_num)
theorem B1896485 : Blo 1262449 1896485 := bbase (se 4 (by rfl) ⟨177795, by rfl⟩ : syracuseStep 1896485 = 355591) (by norm_num)
theorem B1421365 : Blo 1262449 1421365 := bbase (se 5 (by rfl) ⟨66626, by rfl⟩ : syracuseStep 1421365 = 133253) (by norm_num)
theorem B1896509 : Blo 1262449 1896509 := bbase (se 3 (by rfl) ⟨355595, by rfl⟩ : syracuseStep 1896509 = 711191) (by norm_num)
theorem B1896533 : Blo 1262449 1896533 := bbase (se 8 (by rfl) ⟨11112, by rfl⟩ : syracuseStep 1896533 = 22225) (by norm_num)
theorem B1421401 : Blo 1262449 1421401 := bbase (se 2 (by rfl) ⟨533025, by rfl⟩ : syracuseStep 1421401 = 1066051) (by norm_num)
theorem B3199085 : Blo 1262449 3199085 := bbase (se 3 (by rfl) ⟨599828, by rfl⟩ : syracuseStep 3199085 = 1199657) (by norm_num)
theorem B1896557 : Blo 1262449 1896557 := bbase (se 3 (by rfl) ⟨355604, by rfl⟩ : syracuseStep 1896557 = 711209) (by norm_num)
theorem B1421437 : Blo 1262449 1421437 := bbase (se 3 (by rfl) ⟨266519, by rfl⟩ : syracuseStep 1421437 = 533039) (by norm_num)
theorem B1896581 : Blo 1262449 1896581 := bbase (se 4 (by rfl) ⟨177804, by rfl⟩ : syracuseStep 1896581 = 355609) (by norm_num)
theorem B1798301 : Blo 1262449 1798301 := bbase (se 3 (by rfl) ⟨337181, by rfl⟩ : syracuseStep 1798301 = 674363) (by norm_num)
theorem B1896605 : Blo 1262449 1896605 := bbase (se 3 (by rfl) ⟨355613, by rfl⟩ : syracuseStep 1896605 = 711227) (by norm_num)
theorem B1421473 : Blo 1262449 1421473 := bbase (se 2 (by rfl) ⟨533052, by rfl⟩ : syracuseStep 1421473 = 1066105) (by norm_num)
theorem B1896629 : Blo 1262449 1896629 := bbase (se 5 (by rfl) ⟨88904, by rfl⟩ : syracuseStep 1896629 = 177809) (by norm_num)
theorem B5763269 : Blo 1262449 5763269 := bbase (se 4 (by rfl) ⟨540306, by rfl⟩ : syracuseStep 5763269 = 1080613) (by norm_num)
theorem B1421509 : Blo 1262449 1421509 := bbase (se 4 (by rfl) ⟨133266, by rfl⟩ : syracuseStep 1421509 = 266533) (by norm_num)
theorem B1896653 : Blo 1262449 1896653 := bbase (se 3 (by rfl) ⟨355622, by rfl⟩ : syracuseStep 1896653 = 711245) (by norm_num)
theorem B7794901 : Blo 1262449 7794901 := bbase (se 7 (by rfl) ⟨91346, by rfl⟩ : syracuseStep 7794901 = 182693) (by norm_num)
theorem B1421545 : Blo 1262449 1421545 := bbase (se 2 (by rfl) ⟨533079, by rfl⟩ : syracuseStep 1421545 = 1066159) (by norm_num)
theorem B2887949 : Blo 1262449 2887949 := bbase (se 3 (by rfl) ⟨541490, by rfl⟩ : syracuseStep 2887949 = 1082981) (by norm_num)
theorem B1421581 : Blo 1262449 1421581 := bbase (se 3 (by rfl) ⟨266546, by rfl⟩ : syracuseStep 1421581 = 533093) (by norm_num)
theorem B3199277 : Blo 1262449 3199277 := bbase (se 3 (by rfl) ⟨599864, by rfl⟩ : syracuseStep 3199277 = 1199729) (by norm_num)
theorem B1421617 : Blo 1262449 1421617 := bbase (se 2 (by rfl) ⟨533106, by rfl⟩ : syracuseStep 1421617 = 1066213) (by norm_num)
theorem B1421653 : Blo 1262449 1421653 := bbase (se 10 (by rfl) ⟨2082, by rfl⟩ : syracuseStep 1421653 = 4165) (by norm_num)
theorem B4551029 : Blo 1262449 4551029 := bbase (se 5 (by rfl) ⟨213329, by rfl⟩ : syracuseStep 4551029 = 426659) (by norm_num)
theorem B1421689 : Blo 1262449 1421689 := bbase (se 2 (by rfl) ⟨533133, by rfl⟩ : syracuseStep 1421689 = 1066267) (by norm_num)
theorem B4264325 : Blo 1262449 4264325 := bbase (se 4 (by rfl) ⟨399780, by rfl⟩ : syracuseStep 4264325 = 799561) (by norm_num)
theorem B1421725 : Blo 1262449 1421725 := bbase (se 3 (by rfl) ⟨266573, by rfl⟩ : syracuseStep 1421725 = 533147) (by norm_num)
theorem B1421761 : Blo 1262449 1421761 := bbase (se 2 (by rfl) ⟨533160, by rfl⟩ : syracuseStep 1421761 = 1066321) (by norm_num)
theorem B2879957 : Blo 1262449 2879957 := bbase (se 7 (by rfl) ⟨33749, by rfl⟩ : syracuseStep 2879957 = 67499) (by norm_num)
theorem B1421797 : Blo 1262449 1421797 := bbase (se 4 (by rfl) ⟨133293, by rfl⟩ : syracuseStep 1421797 = 266587) (by norm_num)
theorem B1421833 : Blo 1262449 1421833 := bbase (se 2 (by rfl) ⟨533187, by rfl⟩ : syracuseStep 1421833 = 1066375) (by norm_num)
theorem B3117581 : Blo 1262449 3117581 := bbase (se 3 (by rfl) ⟨584546, by rfl⟩ : syracuseStep 3117581 = 1169093) (by norm_num)
theorem B8098325 : Blo 1262449 8098325 := bbase (se 6 (by rfl) ⟨189804, by rfl⟩ : syracuseStep 8098325 = 379609) (by norm_num)
theorem B1421869 : Blo 1262449 1421869 := bbase (se 3 (by rfl) ⟨266600, by rfl⟩ : syracuseStep 1421869 = 533201) (by norm_num)
theorem B1421905 : Blo 1262449 1421905 := bbase (se 2 (by rfl) ⟨533214, by rfl⟩ : syracuseStep 1421905 = 1066429) (by norm_num)
theorem B1421941 : Blo 1262449 1421941 := bbase (se 5 (by rfl) ⟨66653, by rfl⟩ : syracuseStep 1421941 = 133307) (by norm_num)
theorem B3199621 : Blo 1262449 3199621 := bbase (se 4 (by rfl) ⟨299964, by rfl⟩ : syracuseStep 3199621 = 599929) (by norm_num)
theorem B12145301 : Blo 1262449 12145301 := bbase (se 6 (by rfl) ⟨284655, by rfl⟩ : syracuseStep 12145301 = 569311) (by norm_num)
theorem B1421977 : Blo 1262449 1421977 := bbase (se 2 (by rfl) ⟨533241, by rfl⟩ : syracuseStep 1421977 = 1066483) (by norm_num)
theorem B1708717 : Blo 1262449 1708717 := bbase (se 3 (by rfl) ⟨320384, by rfl⟩ : syracuseStep 1708717 = 640769) (by norm_num)
theorem B6828725 : Blo 1262449 6828725 := bbase (se 5 (by rfl) ⟨320096, by rfl⟩ : syracuseStep 6828725 = 640193) (by norm_num)
theorem B2396861 : Blo 1262449 2396861 := bbase (se 3 (by rfl) ⟨449411, by rfl⟩ : syracuseStep 2396861 = 898823) (by norm_num)
theorem B1422013 : Blo 1262449 1422013 := bbase (se 3 (by rfl) ⟨266627, by rfl⟩ : syracuseStep 1422013 = 533255) (by norm_num)
theorem B1798853 : Blo 1262449 1798853 := bbase (se 4 (by rfl) ⟨168642, by rfl⟩ : syracuseStep 1798853 = 337285) (by norm_num)
theorem B1422049 : Blo 1262449 1422049 := bbase (se 2 (by rfl) ⟨533268, by rfl⟩ : syracuseStep 1422049 = 1066537) (by norm_num)
theorem B1348337 : Blo 1262449 1348337 := bbase (se 2 (by rfl) ⟨505626, by rfl⟩ : syracuseStep 1348337 = 1011253) (by norm_num)
theorem B3035893 : Blo 1262449 3035893 := bbase (se 5 (by rfl) ⟨142307, by rfl⟩ : syracuseStep 3035893 = 284615) (by norm_num)
theorem B3199733 : Blo 1262449 3199733 := bbase (se 5 (by rfl) ⟨149987, by rfl⟩ : syracuseStep 3199733 = 299975) (by norm_num)
theorem B1422085 : Blo 1262449 1422085 := bbase (se 4 (by rfl) ⟨133320, by rfl⟩ : syracuseStep 1422085 = 266641) (by norm_num)
theorem B1422121 : Blo 1262449 1422121 := bbase (se 2 (by rfl) ⟨533295, by rfl⟩ : syracuseStep 1422121 = 1066591) (by norm_num)
theorem B4264757 : Blo 1262449 4264757 := bbase (se 5 (by rfl) ⟨199910, by rfl⟩ : syracuseStep 4264757 = 399821) (by norm_num)
theorem B1422157 : Blo 1262449 1422157 := bbase (se 3 (by rfl) ⟨266654, by rfl⟩ : syracuseStep 1422157 = 533309) (by norm_num)
theorem B1422193 : Blo 1262449 1422193 := bbase (se 2 (by rfl) ⟨533322, by rfl⟩ : syracuseStep 1422193 = 1066645) (by norm_num)
theorem B1708933 : Blo 1262449 1708933 := bbase (se 4 (by rfl) ⟨160212, by rfl⟩ : syracuseStep 1708933 = 320425) (by norm_num)
theorem B1422229 : Blo 1262449 1422229 := bbase (se 6 (by rfl) ⟨33333, by rfl⟩ : syracuseStep 1422229 = 66667) (by norm_num)
theorem B1348525 : Blo 1262449 1348525 := bbase (se 3 (by rfl) ⟨252848, by rfl⟩ : syracuseStep 1348525 = 505697) (by norm_num)
theorem B6157237 : Blo 1262449 6157237 := bbase (se 5 (by rfl) ⟨288620, by rfl⟩ : syracuseStep 6157237 = 577241) (by norm_num)
theorem B3199925 : Blo 1262449 3199925 := bbase (se 5 (by rfl) ⟨149996, by rfl⟩ : syracuseStep 3199925 = 299993) (by norm_num)
theorem B1422265 : Blo 1262449 1422265 := bbase (se 2 (by rfl) ⟨533349, by rfl⟩ : syracuseStep 1422265 = 1066699) (by norm_num)
theorem B1422301 : Blo 1262449 1422301 := bbase (se 3 (by rfl) ⟨266681, by rfl⟩ : syracuseStep 1422301 = 533363) (by norm_num)
theorem B4797413 : Blo 1262449 4797413 := bbase (se 4 (by rfl) ⟨449757, by rfl⟩ : syracuseStep 4797413 = 899515) (by norm_num)
theorem B1422337 : Blo 1262449 1422337 := bbase (se 2 (by rfl) ⟨533376, by rfl⟩ : syracuseStep 1422337 = 1066753) (by norm_num)
theorem B1422373 : Blo 1262449 1422373 := bbase (se 4 (by rfl) ⟨133347, by rfl⟩ : syracuseStep 1422373 = 266695) (by norm_num)
theorem B10941493 : Blo 1262449 10941493 := bbase (se 5 (by rfl) ⟨512882, by rfl⟩ : syracuseStep 10941493 = 1025765) (by norm_num)
theorem B6394949 : Blo 1262449 6394949 := bbase (se 4 (by rfl) ⟨599526, by rfl⟩ : syracuseStep 6394949 = 1199053) (by norm_num)
theorem B1422409 : Blo 1262449 1422409 := bbase (se 2 (by rfl) ⟨533403, by rfl⟩ : syracuseStep 1422409 = 1066807) (by norm_num)
theorem B7197781 : Blo 1262449 7197781 := bbase (se 8 (by rfl) ⟨42174, by rfl⟩ : syracuseStep 7197781 = 84349) (by norm_num)
theorem B6157397 : Blo 1262449 6157397 := bbase (se 8 (by rfl) ⟨36078, by rfl⟩ : syracuseStep 6157397 = 72157) (by norm_num)
theorem B1422445 : Blo 1262449 1422445 := bbase (se 3 (by rfl) ⟨266708, by rfl⟩ : syracuseStep 1422445 = 533417) (by norm_num)
theorem B2462861 : Blo 1262449 2462861 := bbase (se 3 (by rfl) ⟨461786, by rfl⟩ : syracuseStep 2462861 = 923573) (by norm_num)
theorem B1422481 : Blo 1262449 1422481 := bbase (se 2 (by rfl) ⟨533430, by rfl⟩ : syracuseStep 1422481 = 1066861) (by norm_num)
theorem B6075589 : Blo 1262449 6075589 := bbase (se 4 (by rfl) ⟨569586, by rfl⟩ : syracuseStep 6075589 = 1139173) (by norm_num)
theorem B1316045 : Blo 1262449 1316045 := bbase (se 3 (by rfl) ⟨246758, by rfl⟩ : syracuseStep 1316045 = 493517) (by norm_num)
theorem B4265189 : Blo 1262449 4265189 := bbase (se 4 (by rfl) ⟨399861, by rfl⟩ : syracuseStep 4265189 = 799723) (by norm_num)
theorem B10245365 : Blo 1262449 10245365 := bbase (se 5 (by rfl) ⟨480251, by rfl⟩ : syracuseStep 10245365 = 960503) (by norm_num)
theorem B4797701 : Blo 1262449 4797701 := bbase (se 4 (by rfl) ⟨449784, by rfl⟩ : syracuseStep 4797701 = 899569) (by norm_num)
theorem B3200269 : Blo 1262449 3200269 := bbase (se 3 (by rfl) ⟨600050, by rfl⟩ : syracuseStep 3200269 = 1200101) (by norm_num)
theorem B3200381 : Blo 1262449 3200381 := bbase (se 3 (by rfl) ⟨600071, by rfl⟩ : syracuseStep 3200381 = 1200143) (by norm_num)
theorem B1922429 : Blo 1262449 1922429 := bbase (se 3 (by rfl) ⟨360455, by rfl⟩ : syracuseStep 1922429 = 720911) (by norm_num)
theorem B2397613 : Blo 1262449 2397613 := bbase (se 3 (by rfl) ⟨449552, by rfl⟩ : syracuseStep 2397613 = 899105) (by norm_num)
theorem B1799605 : Blo 1262449 1799605 := bbase (se 5 (by rfl) ⟨84356, by rfl⟩ : syracuseStep 1799605 = 168713) (by norm_num)
theorem B1316297 : Blo 1262449 1316297 := bbase (se 2 (by rfl) ⟨493611, by rfl⟩ : syracuseStep 1316297 = 987223) (by norm_num)
theorem B3413477 : Blo 1262449 3413477 := bbase (se 4 (by rfl) ⟨320013, by rfl⟩ : syracuseStep 3413477 = 640027) (by norm_num)
theorem B10794485 : Blo 1262449 10794485 := bbase (se 5 (by rfl) ⟨505991, by rfl⟩ : syracuseStep 10794485 = 1011983) (by norm_num)
theorem B2430517 : Blo 1262449 2430517 := bbase (se 5 (by rfl) ⟨113930, by rfl⟩ : syracuseStep 2430517 = 227861) (by norm_num)
theorem B2397757 : Blo 1262449 2397757 := bbase (se 3 (by rfl) ⟨449579, by rfl⟩ : syracuseStep 2397757 = 899159) (by norm_num)
theorem B3200573 : Blo 1262449 3200573 := bbase (se 3 (by rfl) ⟨600107, by rfl⟩ : syracuseStep 3200573 = 1200215) (by norm_num)
theorem B4552309 : Blo 1262449 4552309 := bbase (se 5 (by rfl) ⟨213389, by rfl⟩ : syracuseStep 4552309 = 426779) (by norm_num)
theorem B4265621 : Blo 1262449 4265621 := bbase (se 6 (by rfl) ⟨99975, by rfl⟩ : syracuseStep 4265621 = 199951) (by norm_num)
theorem B5396149 : Blo 1262449 5396149 := bbase (se 5 (by rfl) ⟨252944, by rfl⟩ : syracuseStep 5396149 = 505889) (by norm_num)
theorem B2397917 : Blo 1262449 2397917 := bbase (se 3 (by rfl) ⟨449609, by rfl⟩ : syracuseStep 2397917 = 899219) (by norm_num)
theorem B1349345 : Blo 1262449 1349345 := bbase (se 2 (by rfl) ⟨506004, by rfl⟩ : syracuseStep 1349345 = 1012009) (by norm_num)
theorem B2561861 : Blo 1262449 2561861 := bbase (se 4 (by rfl) ⟨240174, by rfl⟩ : syracuseStep 2561861 = 480349) (by norm_num)
theorem B3839845 : Blo 1262449 3839845 := bbase (se 4 (by rfl) ⟨359985, by rfl⟩ : syracuseStep 3839845 = 719971) (by norm_num)
theorem B2398061 : Blo 1262449 2398061 := bbase (se 3 (by rfl) ⟨449636, by rfl⟩ : syracuseStep 2398061 = 899273) (by norm_num)
theorem B2840525 : Blo 1262449 2840525 := bbase (se 3 (by rfl) ⟨532598, by rfl⟩ : syracuseStep 2840525 = 1065197) (by norm_num)
theorem B2840597 : Blo 1262449 2840597 := bbase (se 6 (by rfl) ⟨66576, by rfl⟩ : syracuseStep 2840597 = 133153) (by norm_num)
theorem B4266053 : Blo 1262449 4266053 := bbase (se 4 (by rfl) ⟨399942, by rfl⟩ : syracuseStep 4266053 = 799885) (by norm_num)
theorem B2840669 : Blo 1262449 2840669 := bbase (se 3 (by rfl) ⟨532625, by rfl⟩ : syracuseStep 2840669 = 1065251) (by norm_num)
theorem B3037277 : Blo 1262449 3037277 := bbase (se 3 (by rfl) ⟨569489, by rfl⟩ : syracuseStep 3037277 = 1138979) (by norm_num)
theorem B2398349 : Blo 1262449 2398349 := bbase (se 3 (by rfl) ⟨449690, by rfl⟩ : syracuseStep 2398349 = 899381) (by norm_num)
theorem B1349789 : Blo 1262449 1349789 := bbase (se 3 (by rfl) ⟨253085, by rfl⟩ : syracuseStep 1349789 = 506171) (by norm_num)
theorem B2840741 : Blo 1262449 2840741 := bbase (se 4 (by rfl) ⟨266319, by rfl⟩ : syracuseStep 2840741 = 532639) (by norm_num)
theorem B2840813 : Blo 1262449 2840813 := bbase (se 3 (by rfl) ⟨532652, by rfl⟩ : syracuseStep 2840813 = 1065305) (by norm_num)
theorem B2398501 : Blo 1262449 2398501 := bbase (se 4 (by rfl) ⟨224859, by rfl⟩ : syracuseStep 2398501 = 449719) (by norm_num)
theorem B2840885 : Blo 1262449 2840885 := bbase (se 5 (by rfl) ⟨133166, by rfl⟩ : syracuseStep 2840885 = 266333) (by norm_num)
theorem B6396245 : Blo 1262449 6396245 := bbase (se 10 (by rfl) ⟨9369, by rfl⟩ : syracuseStep 6396245 = 18739) (by norm_num)
theorem B8092021 : Blo 1262449 8092021 := bbase (se 5 (by rfl) ⟨379313, by rfl⟩ : syracuseStep 8092021 = 758627) (by norm_num)
theorem B2840957 : Blo 1262449 2840957 := bbase (se 3 (by rfl) ⟨532679, by rfl⟩ : syracuseStep 2840957 = 1065359) (by norm_num)
theorem B1350037 : Blo 1262449 1350037 := bbase (se 6 (by rfl) ⟨31641, by rfl⟩ : syracuseStep 1350037 = 63283) (by norm_num)
theorem B4798885 : Blo 1262449 4798885 := bbase (se 4 (by rfl) ⟨449895, by rfl⟩ : syracuseStep 4798885 = 899791) (by norm_num)
theorem B2841029 : Blo 1262449 2841029 := bbase (se 4 (by rfl) ⟨266346, by rfl⟩ : syracuseStep 2841029 = 532693) (by norm_num)
theorem B3332549 : Blo 1262449 3332549 := bbase (se 4 (by rfl) ⟨312426, by rfl⟩ : syracuseStep 3332549 = 624853) (by norm_num)
theorem B4266485 : Blo 1262449 4266485 := bbase (se 5 (by rfl) ⟨199991, by rfl⟩ : syracuseStep 4266485 = 399983) (by norm_num)
theorem B2841101 : Blo 1262449 2841101 := bbase (se 3 (by rfl) ⟨532706, by rfl⟩ : syracuseStep 2841101 = 1065413) (by norm_num)
theorem B3037709 : Blo 1262449 3037709 := bbase (se 3 (by rfl) ⟨569570, by rfl⟩ : syracuseStep 3037709 = 1139141) (by norm_num)
theorem B2595349 : Blo 1262449 2595349 := bbase (se 6 (by rfl) ⟨60828, by rfl⟩ : syracuseStep 2595349 = 121657) (by norm_num)
theorem B2808389 : Blo 1262449 2808389 := bbase (se 4 (by rfl) ⟨263286, by rfl⟩ : syracuseStep 2808389 = 526573) (by norm_num)
theorem B2841173 : Blo 1262449 2841173 := bbase (se 8 (by rfl) ⟨16647, by rfl⟩ : syracuseStep 2841173 = 33295) (by norm_num)
theorem B2398805 : Blo 1262449 2398805 := bbase (se 8 (by rfl) ⟨14055, by rfl⟩ : syracuseStep 2398805 = 28111) (by norm_num)
theorem B3078773 : Blo 1262449 3078773 := bbase (se 5 (by rfl) ⟨144317, by rfl⟩ : syracuseStep 3078773 = 288635) (by norm_num)
theorem B16202389 : Blo 1262449 16202389 := bbase (se 6 (by rfl) ⟨379743, by rfl⟩ : syracuseStep 16202389 = 759487) (by norm_num)
theorem B2841245 : Blo 1262449 2841245 := bbase (se 3 (by rfl) ⟨532733, by rfl⟩ : syracuseStep 2841245 = 1065467) (by norm_num)
theorem B4799189 : Blo 1262449 4799189 := bbase (se 7 (by rfl) ⟨56240, by rfl⟩ : syracuseStep 4799189 = 112481) (by norm_num)
theorem B2841317 : Blo 1262449 2841317 := bbase (se 4 (by rfl) ⟨266373, by rfl⟩ : syracuseStep 2841317 = 532747) (by norm_num)
theorem B2841389 : Blo 1262449 2841389 := bbase (se 3 (by rfl) ⟨532760, by rfl⟩ : syracuseStep 2841389 = 1065521) (by norm_num)
theorem B1440617 : Blo 1262449 1440617 := bbase (se 2 (by rfl) ⟨540231, by rfl⟩ : syracuseStep 1440617 = 1080463) (by norm_num)
theorem B2841461 : Blo 1262449 2841461 := bbase (se 5 (by rfl) ⟨133193, by rfl⟩ : syracuseStep 2841461 = 266387) (by norm_num)
theorem B1620901 : Blo 1262449 1620901 := bbase (se 4 (by rfl) ⟨151959, by rfl⟩ : syracuseStep 1620901 = 303919) (by norm_num)
theorem B4266917 : Blo 1262449 4266917 := bbase (se 4 (by rfl) ⟨400023, by rfl⟩ : syracuseStep 4266917 = 800047) (by norm_num)
theorem B2841533 : Blo 1262449 2841533 := bbase (se 3 (by rfl) ⟨532787, by rfl⟩ : syracuseStep 2841533 = 1065575) (by norm_num)
theorem B3840965 : Blo 1262449 3840965 := bbase (se 4 (by rfl) ⟨360090, by rfl⟩ : syracuseStep 3840965 = 720181) (by norm_num)
theorem B9599957 : Blo 1262449 9599957 := bbase (se 7 (by rfl) ⟨112499, by rfl⟩ : syracuseStep 9599957 = 224999) (by norm_num)
theorem B2841605 : Blo 1262449 2841605 := bbase (se 4 (by rfl) ⟨266400, by rfl⟩ : syracuseStep 2841605 = 532801) (by norm_num)
theorem B7199765 : Blo 1262449 7199765 := bbase (se 6 (by rfl) ⟨168744, by rfl⟩ : syracuseStep 7199765 = 337489) (by norm_num)
theorem B5119013 : Blo 1262449 5119013 := bbase (se 4 (by rfl) ⟨479907, by rfl⟩ : syracuseStep 5119013 = 959815) (by norm_num)
theorem B2161733 : Blo 1262449 2161733 := bbase (se 4 (by rfl) ⟨202662, by rfl⟩ : syracuseStep 2161733 = 405325) (by norm_num)
theorem B2841677 : Blo 1262449 2841677 := bbase (se 3 (by rfl) ⟨532814, by rfl⟩ : syracuseStep 2841677 = 1065629) (by norm_num)
theorem B4045909 : Blo 1262449 4045909 := bbase (se 8 (by rfl) ⟨23706, by rfl⟩ : syracuseStep 4045909 = 47413) (by norm_num)
theorem B2276437 : Blo 1262449 2276437 := bbase (se 8 (by rfl) ⟨13338, by rfl⟩ : syracuseStep 2276437 = 26677) (by norm_num)
theorem B5397637 : Blo 1262449 5397637 := bbase (se 4 (by rfl) ⟨506028, by rfl⟩ : syracuseStep 5397637 = 1012057) (by norm_num)
theorem B2841749 : Blo 1262449 2841749 := bbase (se 6 (by rfl) ⟨66603, by rfl⟩ : syracuseStep 2841749 = 133207) (by norm_num)
theorem B5397653 : Blo 1262449 5397653 := bbase (se 6 (by rfl) ⟨126507, by rfl⟩ : syracuseStep 5397653 = 253015) (by norm_num)
theorem B2882749 : Blo 1262449 2882749 := bbase (se 3 (by rfl) ⟨540515, by rfl⟩ : syracuseStep 2882749 = 1081031) (by norm_num)
theorem B2841821 : Blo 1262449 2841821 := bbase (se 3 (by rfl) ⟨532841, by rfl⟩ : syracuseStep 2841821 = 1065683) (by norm_num)
theorem B1441037 : Blo 1262449 1441037 := bbase (se 3 (by rfl) ⟨270194, by rfl⟩ : syracuseStep 1441037 = 540389) (by norm_num)
theorem B2841893 : Blo 1262449 2841893 := bbase (se 4 (by rfl) ⟨266427, by rfl⟩ : syracuseStep 2841893 = 532855) (by norm_num)
theorem B1621289 : Blo 1262449 1621289 := bbase (se 2 (by rfl) ⟨607983, by rfl⟩ : syracuseStep 1621289 = 1215967) (by norm_num)
theorem B2399557 : Blo 1262449 2399557 := bbase (se 4 (by rfl) ⟨224958, by rfl⟩ : syracuseStep 2399557 = 449917) (by norm_num)
theorem B4267349 : Blo 1262449 4267349 := bbase (se 11 (by rfl) ⟨3125, by rfl⟩ : syracuseStep 4267349 = 6251) (by norm_num)
theorem B2841965 : Blo 1262449 2841965 := bbase (se 3 (by rfl) ⟨532868, by rfl⟩ : syracuseStep 2841965 = 1065737) (by norm_num)
theorem B9592181 : Blo 1262449 9592181 := bbase (se 5 (by rfl) ⟨449633, by rfl⟩ : syracuseStep 9592181 = 899267) (by norm_num)
theorem B2842037 : Blo 1262449 2842037 := bbase (se 5 (by rfl) ⟨133220, by rfl⟩ : syracuseStep 2842037 = 266441) (by norm_num)
theorem B2399701 : Blo 1262449 2399701 := bbase (se 7 (by rfl) ⟨28121, by rfl⟩ : syracuseStep 2399701 = 56243) (by norm_num)
theorem B2842109 : Blo 1262449 2842109 := bbase (se 3 (by rfl) ⟨532895, by rfl⟩ : syracuseStep 2842109 = 1065791) (by norm_num)
theorem B2022941 : Blo 1262449 2022941 := bbase (se 3 (by rfl) ⟨379301, by rfl⟩ : syracuseStep 2022941 = 758603) (by norm_num)
theorem B2842181 : Blo 1262449 2842181 := bbase (se 4 (by rfl) ⟨266454, by rfl⟩ : syracuseStep 2842181 = 532909) (by norm_num)
theorem B6397541 : Blo 1262449 6397541 := bbase (se 4 (by rfl) ⟨599769, by rfl⟩ : syracuseStep 6397541 = 1199539) (by norm_num)
theorem B2399861 : Blo 1262449 2399861 := bbase (se 5 (by rfl) ⟨112493, by rfl⟩ : syracuseStep 2399861 = 224987) (by norm_num)
theorem B2842253 : Blo 1262449 2842253 := bbase (se 3 (by rfl) ⟨532922, by rfl⟩ : syracuseStep 2842253 = 1065845) (by norm_num)
theorem B2842325 : Blo 1262449 2842325 := bbase (se 7 (by rfl) ⟨33308, by rfl⟩ : syracuseStep 2842325 = 66617) (by norm_num)
theorem B3596021 : Blo 1262449 3596021 := bbase (se 5 (by rfl) ⟨168563, by rfl⟩ : syracuseStep 3596021 = 337127) (by norm_num)
theorem B2400005 : Blo 1262449 2400005 := bbase (se 4 (by rfl) ⟨225000, by rfl⟩ : syracuseStep 2400005 = 450001) (by norm_num)
theorem B2842397 : Blo 1262449 2842397 := bbase (se 3 (by rfl) ⟨532949, by rfl⟩ : syracuseStep 2842397 = 1065899) (by norm_num)
theorem B10944341 : Blo 1262449 10944341 := bbase (se 9 (by rfl) ⟨32063, by rfl⟩ : syracuseStep 10944341 = 64127) (by norm_num)
theorem B2842469 : Blo 1262449 2842469 := bbase (se 4 (by rfl) ⟨266481, by rfl⟩ : syracuseStep 2842469 = 532963) (by norm_num)
theorem B9723797 : Blo 1262449 9723797 := bbase (se 6 (by rfl) ⟨227901, by rfl⟩ : syracuseStep 9723797 = 455803) (by norm_num)
theorem B2842541 : Blo 1262449 2842541 := bbase (se 3 (by rfl) ⟨532976, by rfl⟩ : syracuseStep 2842541 = 1065953) (by norm_num)
theorem B2023397 : Blo 1262449 2023397 := bbase (se 4 (by rfl) ⟨189693, by rfl⟩ : syracuseStep 2023397 = 379387) (by norm_num)
theorem B1974245 : Blo 1262449 1974245 := bbase (se 4 (by rfl) ⟨185085, by rfl⟩ : syracuseStep 1974245 = 370171) (by norm_num)
theorem B2842613 : Blo 1262449 2842613 := bbase (se 5 (by rfl) ⟨133247, by rfl⟩ : syracuseStep 2842613 = 266495) (by norm_num)
theorem B18702389 : Blo 1262449 18702389 := bstep (se 5 (by rfl) ⟨876674, by rfl⟩ : syracuseStep 18702389 = 1753349) B1753349
theorem B15368291 : Blo 1262449 15368291 := bstep (se 1 (by rfl) ⟨11526218, by rfl⟩ : syracuseStep 15368291 = 23052437) B23052437
theorem B2277539 : Blo 1262449 2277539 := bstep (se 1 (by rfl) ⟨1708154, by rfl⟩ : syracuseStep 2277539 = 3416309) B3416309
theorem B1925299 : Blo 1262449 1925299 := bstep (se 1 (by rfl) ⟨1443974, by rfl⟩ : syracuseStep 1925299 = 2887949) B2887949
theorem B2023633 : Blo 1262449 2023633 := bstep (se 2 (by rfl) ⟨758862, by rfl⟩ : syracuseStep 2023633 = 1517725) B1517725
theorem B2842865 : Blo 1262449 2842865 := bstep (se 2 (by rfl) ⟨1066074, by rfl⟩ : syracuseStep 2842865 = 2132149) B2132149
theorem B2842883 : Blo 1262449 2842883 := bstep (se 1 (by rfl) ⟨2132162, by rfl⟩ : syracuseStep 2842883 = 4264325) B4264325
theorem B5398883 : Blo 1262449 5398883 := bstep (se 1 (by rfl) ⟨4049162, by rfl⟩ : syracuseStep 5398883 = 8098325) B8098325
theorem B1597907 : Blo 1262449 1597907 := bstep (se 1 (by rfl) ⟨1198430, by rfl⟩ : syracuseStep 1597907 = 2396861) B2396861
theorem B2130401 : Blo 1262449 2130401 := bstep (se 2 (by rfl) ⟨798900, by rfl⟩ : syracuseStep 2130401 = 1597801) B1597801
theorem B10789361 : Blo 1262449 10789361 := bstep (se 2 (by rfl) ⟨4046010, by rfl⟩ : syracuseStep 10789361 = 8092021) B8092021
theorem B15368717 : Blo 1262449 15368717 := bstep (se 3 (by rfl) ⟨2881634, by rfl⟩ : syracuseStep 15368717 = 5763269) B5763269
theorem B2843153 : Blo 1262449 2843153 := bstep (se 2 (by rfl) ⟨1066182, by rfl⟩ : syracuseStep 2843153 = 2132365) B2132365
theorem B2843171 : Blo 1262449 2843171 := bstep (se 1 (by rfl) ⟨2132378, by rfl⟩ : syracuseStep 2843171 = 4264757) B4264757
theorem B6398513 : Blo 1262449 6398513 := bstep (se 2 (by rfl) ⟨2399442, by rfl⟩ : syracuseStep 6398513 = 4798885) B4798885
theorem B2130529 : Blo 1262449 2130529 := bstep (se 2 (by rfl) ⟨798948, by rfl⟩ : syracuseStep 2130529 = 1597897) B1597897
theorem B2130563 : Blo 1262449 2130563 := bstep (se 1 (by rfl) ⟨1597922, by rfl⟩ : syracuseStep 2130563 = 3195845) B3195845
theorem B3596977 : Blo 1262449 3596977 := bstep (se 2 (by rfl) ⟨1348866, by rfl⟩ : syracuseStep 3596977 = 2697733) B2697733
theorem B3842765 : Blo 1262449 3842765 := bstep (se 3 (by rfl) ⟨720518, by rfl⟩ : syracuseStep 3842765 = 1441037) B1441037
theorem B4104931 : Blo 1262449 4104931 := bstep (se 1 (by rfl) ⟨3078698, by rfl⟩ : syracuseStep 4104931 = 6157397) B6157397
theorem B2130691 : Blo 1262449 2130691 := bstep (se 1 (by rfl) ⟨1598018, by rfl⟩ : syracuseStep 2130691 = 3196037) B3196037
theorem B3195683 : Blo 1262449 3195683 := bstep (se 1 (by rfl) ⟨2396762, by rfl⟩ : syracuseStep 3195683 = 4793525) B4793525
theorem B2843441 : Blo 1262449 2843441 := bstep (se 2 (by rfl) ⟨1066290, by rfl⟩ : syracuseStep 2843441 = 2132581) B2132581
theorem B2843459 : Blo 1262449 2843459 := bstep (se 1 (by rfl) ⟨2132594, by rfl⟩ : syracuseStep 2843459 = 4265189) B4265189
theorem B29197169 : Blo 1262449 29197169 := bstep (se 2 (by rfl) ⟨10948938, by rfl⟩ : syracuseStep 29197169 = 21897877) B21897877
theorem B21603185 : Blo 1262449 21603185 := bstep (se 2 (by rfl) ⟨8101194, by rfl⟩ : syracuseStep 21603185 = 16202389) B16202389
theorem B1262451 : Blo 1262449 1262451 := bstep (se 1 (by rfl) ⟨946838, by rfl⟩ : syracuseStep 1262451 = 1893677) B1893677
theorem B1262467 : Blo 1262449 1262467 := bstep (se 1 (by rfl) ⟨946850, by rfl⟩ : syracuseStep 1262467 = 1893701) B1893701
theorem B2130833 : Blo 1262449 2130833 := bstep (se 2 (by rfl) ⟨799062, by rfl⟩ : syracuseStep 2130833 = 1598125) B1598125
theorem B2278289 : Blo 1262449 2278289 := bstep (se 2 (by rfl) ⟨854358, by rfl⟩ : syracuseStep 2278289 = 1708717) B1708717
theorem B1262483 : Blo 1262449 1262483 := bstep (se 1 (by rfl) ⟨946862, by rfl⟩ : syracuseStep 1262483 = 1893725) B1893725
theorem B1262499 : Blo 1262449 1262499 := bstep (se 1 (by rfl) ⟨946874, by rfl⟩ : syracuseStep 1262499 = 1893749) B1893749
theorem B1262515 : Blo 1262449 1262515 := bstep (se 1 (by rfl) ⟨946886, by rfl⟩ : syracuseStep 1262515 = 1893773) B1893773
theorem B1262531 : Blo 1262449 1262531 := bstep (se 1 (by rfl) ⟨946898, by rfl⟩ : syracuseStep 1262531 = 1893797) B1893797
theorem B1262547 : Blo 1262449 1262547 := bstep (se 1 (by rfl) ⟨946910, by rfl⟩ : syracuseStep 1262547 = 1893821) B1893821
theorem B1262563 : Blo 1262449 1262563 := bstep (se 1 (by rfl) ⟨946922, by rfl⟩ : syracuseStep 1262563 = 1893845) B1893845
theorem B3195875 : Blo 1262449 3195875 := bstep (se 1 (by rfl) ⟨2396906, by rfl⟩ : syracuseStep 3195875 = 4793813) B4793813
theorem B4047857 : Blo 1262449 4047857 := bstep (se 2 (by rfl) ⟨1517946, by rfl⟩ : syracuseStep 4047857 = 3035893) B3035893
theorem B1262579 : Blo 1262449 1262579 := bstep (se 1 (by rfl) ⟨946934, by rfl⟩ : syracuseStep 1262579 = 1893869) B1893869
theorem B1262595 : Blo 1262449 1262595 := bstep (se 1 (by rfl) ⟨946946, by rfl⟩ : syracuseStep 1262595 = 1893893) B1893893
theorem B2130961 : Blo 1262449 2130961 := bstep (se 2 (by rfl) ⟨799110, by rfl⟩ : syracuseStep 2130961 = 1598221) B1598221
theorem B1262611 : Blo 1262449 1262611 := bstep (se 1 (by rfl) ⟨946958, by rfl⟩ : syracuseStep 1262611 = 1893917) B1893917
theorem B1262627 : Blo 1262449 1262627 := bstep (se 1 (by rfl) ⟨946970, by rfl⟩ : syracuseStep 1262627 = 1893941) B1893941
theorem B1262643 : Blo 1262449 1262643 := bstep (se 1 (by rfl) ⟨946982, by rfl⟩ : syracuseStep 1262643 = 1893965) B1893965
theorem B2130995 : Blo 1262449 2130995 := bstep (se 1 (by rfl) ⟨1598246, by rfl⟩ : syracuseStep 2130995 = 3196493) B3196493
theorem B1262659 : Blo 1262449 1262659 := bstep (se 1 (by rfl) ⟨946994, by rfl⟩ : syracuseStep 1262659 = 1893989) B1893989
theorem B1262675 : Blo 1262449 1262675 := bstep (se 1 (by rfl) ⟨947006, by rfl⟩ : syracuseStep 1262675 = 1894013) B1894013
theorem B2843729 : Blo 1262449 2843729 := bstep (se 2 (by rfl) ⟨1066398, by rfl⟩ : syracuseStep 2843729 = 2132797) B2132797
theorem B1262691 : Blo 1262449 1262691 := bstep (se 1 (by rfl) ⟨947018, by rfl⟩ : syracuseStep 1262691 = 1894037) B1894037
theorem B2843747 : Blo 1262449 2843747 := bstep (se 1 (by rfl) ⟨2132810, by rfl⟩ : syracuseStep 2843747 = 4265621) B4265621
theorem B4260977 : Blo 1262449 4260977 := bstep (se 2 (by rfl) ⟨1597866, by rfl⟩ : syracuseStep 4260977 = 3195733) B3195733
theorem B1262707 : Blo 1262449 1262707 := bstep (se 1 (by rfl) ⟨947030, by rfl⟩ : syracuseStep 1262707 = 1894061) B1894061
theorem B1262723 : Blo 1262449 1262723 := bstep (se 1 (by rfl) ⟨947042, by rfl⟩ : syracuseStep 1262723 = 1894085) B1894085
theorem B1262739 : Blo 1262449 1262739 := bstep (se 1 (by rfl) ⟨947054, by rfl⟩ : syracuseStep 1262739 = 1894109) B1894109
theorem B1598611 : Blo 1262449 1598611 := bstep (se 1 (by rfl) ⟨1198958, by rfl⟩ : syracuseStep 1598611 = 2397917) B2397917
theorem B1262755 : Blo 1262449 1262755 := bstep (se 1 (by rfl) ⟨947066, by rfl⟩ : syracuseStep 1262755 = 1894133) B1894133
theorem B2278577 : Blo 1262449 2278577 := bstep (se 2 (by rfl) ⟨854466, by rfl⟩ : syracuseStep 2278577 = 1708933) B1708933
theorem B1262771 : Blo 1262449 1262771 := bstep (se 1 (by rfl) ⟨947078, by rfl⟩ : syracuseStep 1262771 = 1894157) B1894157
theorem B2131123 : Blo 1262449 2131123 := bstep (se 1 (by rfl) ⟨1598342, by rfl⟩ : syracuseStep 2131123 = 3196685) B3196685
theorem B1262787 : Blo 1262449 1262787 := bstep (se 1 (by rfl) ⟨947090, by rfl⟩ : syracuseStep 1262787 = 1894181) B1894181
theorem B1262803 : Blo 1262449 1262803 := bstep (se 1 (by rfl) ⟨947102, by rfl⟩ : syracuseStep 1262803 = 1894205) B1894205
theorem B1262819 : Blo 1262449 1262819 := bstep (se 1 (by rfl) ⟨947114, by rfl⟩ : syracuseStep 1262819 = 1894229) B1894229
theorem B8209649 : Blo 1262449 8209649 := bstep (se 2 (by rfl) ⟨3078618, by rfl⟩ : syracuseStep 8209649 = 6157237) B6157237
theorem B1262835 : Blo 1262449 1262835 := bstep (se 1 (by rfl) ⟨947126, by rfl⟩ : syracuseStep 1262835 = 1894253) B1894253
theorem B1598707 : Blo 1262449 1598707 := bstep (se 1 (by rfl) ⟨1199030, by rfl⟩ : syracuseStep 1598707 = 2398061) B2398061
theorem B1262851 : Blo 1262449 1262851 := bstep (se 1 (by rfl) ⟨947138, by rfl⟩ : syracuseStep 1262851 = 1894277) B1894277
theorem B9594125 : Blo 1262449 9594125 := bstep (se 3 (by rfl) ⟨1798898, by rfl⟩ : syracuseStep 9594125 = 3597797) B3597797
theorem B1262867 : Blo 1262449 1262867 := bstep (se 1 (by rfl) ⟨947150, by rfl⟩ : syracuseStep 1262867 = 1894301) B1894301
theorem B1262883 : Blo 1262449 1262883 := bstep (se 1 (by rfl) ⟨947162, by rfl⟩ : syracuseStep 1262883 = 1894325) B1894325
theorem B1893683 : Blo 1262449 1893683 := bstep (se 1 (by rfl) ⟨1420262, by rfl⟩ : syracuseStep 1893683 = 2840525) B2840525
theorem B1262899 : Blo 1262449 1262899 := bstep (se 1 (by rfl) ⟨947174, by rfl⟩ : syracuseStep 1262899 = 1894349) B1894349
theorem B2131265 : Blo 1262449 2131265 := bstep (se 2 (by rfl) ⟨799224, by rfl⟩ : syracuseStep 2131265 = 1598449) B1598449
theorem B1262915 : Blo 1262449 1262915 := bstep (se 1 (by rfl) ⟨947186, by rfl⟩ : syracuseStep 1262915 = 1894373) B1894373
theorem B7193933 : Blo 1262449 7193933 := bstep (se 3 (by rfl) ⟨1348862, by rfl⟩ : syracuseStep 7193933 = 2697725) B2697725
theorem B1893713 : Blo 1262449 1893713 := bstep (se 2 (by rfl) ⟨710142, by rfl⟩ : syracuseStep 1893713 = 1420285) B1420285
theorem B1262931 : Blo 1262449 1262931 := bstep (se 1 (by rfl) ⟨947198, by rfl⟩ : syracuseStep 1262931 = 1894397) B1894397
theorem B1893731 : Blo 1262449 1893731 := bstep (se 1 (by rfl) ⟨1420298, by rfl⟩ : syracuseStep 1893731 = 2840597) B2840597
theorem B1262947 : Blo 1262449 1262947 := bstep (se 1 (by rfl) ⟨947210, by rfl⟩ : syracuseStep 1262947 = 1894421) B1894421
theorem B2844017 : Blo 1262449 2844017 := bstep (se 2 (by rfl) ⟨1066506, by rfl⟩ : syracuseStep 2844017 = 2133013) B2133013
theorem B1262963 : Blo 1262449 1262963 := bstep (se 1 (by rfl) ⟨947222, by rfl⟩ : syracuseStep 1262963 = 1894445) B1894445
theorem B1893761 : Blo 1262449 1893761 := bstep (se 2 (by rfl) ⟨710160, by rfl⟩ : syracuseStep 1893761 = 1420321) B1420321
theorem B1262979 : Blo 1262449 1262979 := bstep (se 1 (by rfl) ⟨947234, by rfl⟩ : syracuseStep 1262979 = 1894469) B1894469
theorem B2844035 : Blo 1262449 2844035 := bstep (se 1 (by rfl) ⟨2133026, by rfl⟩ : syracuseStep 2844035 = 4266053) B4266053
theorem B1893779 : Blo 1262449 1893779 := bstep (se 1 (by rfl) ⟨1420334, by rfl⟩ : syracuseStep 1893779 = 2840669) B2840669
theorem B1262995 : Blo 1262449 1262995 := bstep (se 1 (by rfl) ⟨947246, by rfl⟩ : syracuseStep 1262995 = 1894493) B1894493
theorem B2024851 : Blo 1262449 2024851 := bstep (se 1 (by rfl) ⟨1518638, by rfl⟩ : syracuseStep 2024851 = 3037277) B3037277
theorem B1263011 : Blo 1262449 1263011 := bstep (se 1 (by rfl) ⟨947258, by rfl⟩ : syracuseStep 1263011 = 1894517) B1894517
theorem B1893809 : Blo 1262449 1893809 := bstep (se 2 (by rfl) ⟨710178, by rfl⟩ : syracuseStep 1893809 = 1420357) B1420357
theorem B1263027 : Blo 1262449 1263027 := bstep (se 1 (by rfl) ⟨947270, by rfl⟩ : syracuseStep 1263027 = 1894541) B1894541
theorem B2131393 : Blo 1262449 2131393 := bstep (se 2 (by rfl) ⟨799272, by rfl⟩ : syracuseStep 2131393 = 1598545) B1598545
theorem B1893827 : Blo 1262449 1893827 := bstep (se 1 (by rfl) ⟨1420370, by rfl⟩ : syracuseStep 1893827 = 2840741) B2840741
theorem B1263043 : Blo 1262449 1263043 := bstep (se 1 (by rfl) ⟨947282, by rfl⟩ : syracuseStep 1263043 = 1894565) B1894565
theorem B1263059 : Blo 1262449 1263059 := bstep (se 1 (by rfl) ⟨947294, by rfl⟩ : syracuseStep 1263059 = 1894589) B1894589
theorem B1893857 : Blo 1262449 1893857 := bstep (se 2 (by rfl) ⟨710196, by rfl⟩ : syracuseStep 1893857 = 1420393) B1420393
theorem B2131427 : Blo 1262449 2131427 := bstep (se 1 (by rfl) ⟨1598570, by rfl⟩ : syracuseStep 2131427 = 3197141) B3197141
theorem B1263075 : Blo 1262449 1263075 := bstep (se 1 (by rfl) ⟨947306, by rfl⟩ : syracuseStep 1263075 = 1894613) B1894613
theorem B1893875 : Blo 1262449 1893875 := bstep (se 1 (by rfl) ⟨1420406, by rfl⟩ : syracuseStep 1893875 = 2840813) B2840813
theorem B1263091 : Blo 1262449 1263091 := bstep (se 1 (by rfl) ⟨947318, by rfl⟩ : syracuseStep 1263091 = 1894637) B1894637
theorem B1263107 : Blo 1262449 1263107 := bstep (se 1 (by rfl) ⟨947330, by rfl⟩ : syracuseStep 1263107 = 1894661) B1894661
theorem B7489037 : Blo 1262449 7489037 := bstep (se 3 (by rfl) ⟨1404194, by rfl⟩ : syracuseStep 7489037 = 2808389) B2808389
theorem B1893905 : Blo 1262449 1893905 := bstep (se 2 (by rfl) ⟨710214, by rfl⟩ : syracuseStep 1893905 = 1420429) B1420429
theorem B1263123 : Blo 1262449 1263123 := bstep (se 1 (by rfl) ⟨947342, by rfl⟩ : syracuseStep 1263123 = 1894685) B1894685
theorem B1893923 : Blo 1262449 1893923 := bstep (se 1 (by rfl) ⟨1420442, by rfl⟩ : syracuseStep 1893923 = 2840885) B2840885
theorem B1263139 : Blo 1262449 1263139 := bstep (se 1 (by rfl) ⟨947354, by rfl⟩ : syracuseStep 1263139 = 1894709) B1894709
theorem B1263155 : Blo 1262449 1263155 := bstep (se 1 (by rfl) ⟨947366, by rfl⟩ : syracuseStep 1263155 = 1894733) B1894733
theorem B1893953 : Blo 1262449 1893953 := bstep (se 2 (by rfl) ⟨710232, by rfl⟩ : syracuseStep 1893953 = 1420465) B1420465
theorem B1263171 : Blo 1262449 1263171 := bstep (se 1 (by rfl) ⟨947378, by rfl⟩ : syracuseStep 1263171 = 1894757) B1894757
theorem B3843665 : Blo 1262449 3843665 := bstep (se 2 (by rfl) ⟨1441374, by rfl⟩ : syracuseStep 3843665 = 2882749) B2882749
theorem B1893971 : Blo 1262449 1893971 := bstep (se 1 (by rfl) ⟨1420478, by rfl⟩ : syracuseStep 1893971 = 2840957) B2840957
theorem B1263187 : Blo 1262449 1263187 := bstep (se 1 (by rfl) ⟨947390, by rfl⟩ : syracuseStep 1263187 = 1894781) B1894781
theorem B2131555 : Blo 1262449 2131555 := bstep (se 1 (by rfl) ⟨1598666, by rfl⟩ : syracuseStep 2131555 = 3197333) B3197333
theorem B1263203 : Blo 1262449 1263203 := bstep (se 1 (by rfl) ⟨947402, by rfl⟩ : syracuseStep 1263203 = 1894805) B1894805
theorem B1894001 : Blo 1262449 1894001 := bstep (se 2 (by rfl) ⟨710250, by rfl⟩ : syracuseStep 1894001 = 1420501) B1420501
theorem B1263219 : Blo 1262449 1263219 := bstep (se 1 (by rfl) ⟨947414, by rfl⟩ : syracuseStep 1263219 = 1894829) B1894829
theorem B1894019 : Blo 1262449 1894019 := bstep (se 1 (by rfl) ⟨1420514, by rfl⟩ : syracuseStep 1894019 = 2841029) B2841029
theorem B1263235 : Blo 1262449 1263235 := bstep (se 1 (by rfl) ⟨947426, by rfl⟩ : syracuseStep 1263235 = 1894853) B1894853
theorem B4261517 : Blo 1262449 4261517 := bstep (se 3 (by rfl) ⟨799034, by rfl⟩ : syracuseStep 4261517 = 1598069) B1598069
theorem B2844305 : Blo 1262449 2844305 := bstep (se 2 (by rfl) ⟨1066614, by rfl⟩ : syracuseStep 2844305 = 2133229) B2133229
theorem B1263251 : Blo 1262449 1263251 := bstep (se 1 (by rfl) ⟨947438, by rfl⟩ : syracuseStep 1263251 = 1894877) B1894877
theorem B1894049 : Blo 1262449 1894049 := bstep (se 2 (by rfl) ⟨710268, by rfl⟩ : syracuseStep 1894049 = 1420537) B1420537
theorem B1263267 : Blo 1262449 1263267 := bstep (se 1 (by rfl) ⟨947450, by rfl⟩ : syracuseStep 1263267 = 1894901) B1894901
theorem B4048547 : Blo 1262449 4048547 := bstep (se 1 (by rfl) ⟨3036410, by rfl⟩ : syracuseStep 4048547 = 6072821) B6072821
theorem B2844323 : Blo 1262449 2844323 := bstep (se 1 (by rfl) ⟨2133242, by rfl⟩ : syracuseStep 2844323 = 4266485) B4266485
theorem B1894067 : Blo 1262449 1894067 := bstep (se 1 (by rfl) ⟨1420550, by rfl⟩ : syracuseStep 1894067 = 2841101) B2841101
theorem B1263283 : Blo 1262449 1263283 := bstep (se 1 (by rfl) ⟨947462, by rfl⟩ : syracuseStep 1263283 = 1894925) B1894925
theorem B4261571 : Blo 1262449 4261571 := bstep (se 1 (by rfl) ⟨3196178, by rfl⟩ : syracuseStep 4261571 = 6392357) B6392357
theorem B1263299 : Blo 1262449 1263299 := bstep (se 1 (by rfl) ⟨947474, by rfl⟩ : syracuseStep 1263299 = 1894949) B1894949
theorem B1894097 : Blo 1262449 1894097 := bstep (se 2 (by rfl) ⟨710286, by rfl⟩ : syracuseStep 1894097 = 1420573) B1420573
theorem B1263315 : Blo 1262449 1263315 := bstep (se 1 (by rfl) ⟨947486, by rfl⟩ : syracuseStep 1263315 = 1894973) B1894973
theorem B1894115 : Blo 1262449 1894115 := bstep (se 1 (by rfl) ⟨1420586, by rfl⟩ : syracuseStep 1894115 = 2841173) B2841173
theorem B1263331 : Blo 1262449 1263331 := bstep (se 1 (by rfl) ⟨947498, by rfl⟩ : syracuseStep 1263331 = 1894997) B1894997
theorem B1599203 : Blo 1262449 1599203 := bstep (se 1 (by rfl) ⟨1199402, by rfl⟩ : syracuseStep 1599203 = 2398805) B2398805
theorem B2131697 : Blo 1262449 2131697 := bstep (se 2 (by rfl) ⟨799386, by rfl⟩ : syracuseStep 2131697 = 1598773) B1598773
theorem B1263347 : Blo 1262449 1263347 := bstep (se 1 (by rfl) ⟨947510, by rfl⟩ : syracuseStep 1263347 = 1895021) B1895021
theorem B1894145 : Blo 1262449 1894145 := bstep (se 2 (by rfl) ⟨710304, by rfl⟩ : syracuseStep 1894145 = 1420609) B1420609
theorem B1263363 : Blo 1262449 1263363 := bstep (se 1 (by rfl) ⟨947522, by rfl⟩ : syracuseStep 1263363 = 1895045) B1895045
theorem B1894163 : Blo 1262449 1894163 := bstep (se 1 (by rfl) ⟨1420622, by rfl⟩ : syracuseStep 1894163 = 2841245) B2841245
theorem B1263379 : Blo 1262449 1263379 := bstep (se 1 (by rfl) ⟨947534, by rfl⟩ : syracuseStep 1263379 = 1895069) B1895069
theorem B1263395 : Blo 1262449 1263395 := bstep (se 1 (by rfl) ⟨947546, by rfl⟩ : syracuseStep 1263395 = 1895093) B1895093
theorem B1894193 : Blo 1262449 1894193 := bstep (se 2 (by rfl) ⟨710322, by rfl⟩ : syracuseStep 1894193 = 1420645) B1420645
theorem B1263411 : Blo 1262449 1263411 := bstep (se 1 (by rfl) ⟨947558, by rfl⟩ : syracuseStep 1263411 = 1895117) B1895117
theorem B1894211 : Blo 1262449 1894211 := bstep (se 1 (by rfl) ⟨1420658, by rfl⟩ : syracuseStep 1894211 = 2841317) B2841317
theorem B1263427 : Blo 1262449 1263427 := bstep (se 1 (by rfl) ⟨947570, by rfl⟩ : syracuseStep 1263427 = 1895141) B1895141
theorem B1263443 : Blo 1262449 1263443 := bstep (se 1 (by rfl) ⟨947582, by rfl⟩ : syracuseStep 1263443 = 1895165) B1895165
theorem B1894241 : Blo 1262449 1894241 := bstep (se 2 (by rfl) ⟨710340, by rfl⟩ : syracuseStep 1894241 = 1420681) B1420681
theorem B1263459 : Blo 1262449 1263459 := bstep (se 1 (by rfl) ⟨947594, by rfl⟩ : syracuseStep 1263459 = 1895189) B1895189
theorem B2131825 : Blo 1262449 2131825 := bstep (se 2 (by rfl) ⟨799434, by rfl⟩ : syracuseStep 2131825 = 1598869) B1598869
theorem B1894259 : Blo 1262449 1894259 := bstep (se 1 (by rfl) ⟨1420694, by rfl⟩ : syracuseStep 1894259 = 2841389) B2841389
theorem B1263475 : Blo 1262449 1263475 := bstep (se 1 (by rfl) ⟨947606, by rfl⟩ : syracuseStep 1263475 = 1895213) B1895213
theorem B1263491 : Blo 1262449 1263491 := bstep (se 1 (by rfl) ⟨947618, by rfl⟩ : syracuseStep 1263491 = 1895237) B1895237
theorem B1894289 : Blo 1262449 1894289 := bstep (se 2 (by rfl) ⟨710358, by rfl⟩ : syracuseStep 1894289 = 1420717) B1420717
theorem B3196817 : Blo 1262449 3196817 := bstep (se 2 (by rfl) ⟨1198806, by rfl⟩ : syracuseStep 3196817 = 2397613) B2397613
theorem B2131859 : Blo 1262449 2131859 := bstep (se 1 (by rfl) ⟨1598894, by rfl⟩ : syracuseStep 2131859 = 3197789) B3197789
theorem B1263507 : Blo 1262449 1263507 := bstep (se 1 (by rfl) ⟨947630, by rfl⟩ : syracuseStep 1263507 = 1895261) B1895261
theorem B1894307 : Blo 1262449 1894307 := bstep (se 1 (by rfl) ⟨1420730, by rfl⟩ : syracuseStep 1894307 = 2841461) B2841461
theorem B1263523 : Blo 1262449 1263523 := bstep (se 1 (by rfl) ⟨947642, by rfl⟩ : syracuseStep 1263523 = 1895285) B1895285
theorem B3598253 : Blo 1262449 3598253 := bstep (se 3 (by rfl) ⟨674672, by rfl⟩ : syracuseStep 3598253 = 1349345) B1349345
theorem B2844593 : Blo 1262449 2844593 := bstep (se 2 (by rfl) ⟨1066722, by rfl⟩ : syracuseStep 2844593 = 2133445) B2133445
theorem B1263539 : Blo 1262449 1263539 := bstep (se 1 (by rfl) ⟨947654, by rfl⟩ : syracuseStep 1263539 = 1895309) B1895309
theorem B1894337 : Blo 1262449 1894337 := bstep (se 2 (by rfl) ⟨710376, by rfl⟩ : syracuseStep 1894337 = 1420753) B1420753
theorem B3196867 : Blo 1262449 3196867 := bstep (se 1 (by rfl) ⟨2397650, by rfl⟩ : syracuseStep 3196867 = 4795301) B4795301
theorem B1263555 : Blo 1262449 1263555 := bstep (se 1 (by rfl) ⟨947666, by rfl⟩ : syracuseStep 1263555 = 1895333) B1895333
theorem B2844611 : Blo 1262449 2844611 := bstep (se 1 (by rfl) ⟨2133458, by rfl⟩ : syracuseStep 2844611 = 4266917) B4266917
theorem B4261841 : Blo 1262449 4261841 := bstep (se 2 (by rfl) ⟨1598190, by rfl⟩ : syracuseStep 4261841 = 3196381) B3196381
theorem B1894355 : Blo 1262449 1894355 := bstep (se 1 (by rfl) ⟨1420766, by rfl⟩ : syracuseStep 1894355 = 2841533) B2841533
theorem B1263571 : Blo 1262449 1263571 := bstep (se 1 (by rfl) ⟨947678, by rfl⟩ : syracuseStep 1263571 = 1895357) B1895357
theorem B1263587 : Blo 1262449 1263587 := bstep (se 1 (by rfl) ⟨947690, by rfl⟩ : syracuseStep 1263587 = 1895381) B1895381
theorem B6399971 : Blo 1262449 6399971 := bstep (se 1 (by rfl) ⟨4799978, by rfl⟩ : syracuseStep 6399971 = 9599957) B9599957
theorem B1894385 : Blo 1262449 1894385 := bstep (se 2 (by rfl) ⟨710394, by rfl⟩ : syracuseStep 1894385 = 1420789) B1420789
theorem B10250225 : Blo 1262449 10250225 := bstep (se 2 (by rfl) ⟨3843834, by rfl⟩ : syracuseStep 10250225 = 7687669) B7687669
theorem B1263603 : Blo 1262449 1263603 := bstep (se 1 (by rfl) ⟨947702, by rfl⟩ : syracuseStep 1263603 = 1895405) B1895405
theorem B1894403 : Blo 1262449 1894403 := bstep (se 1 (by rfl) ⟨1420802, by rfl⟩ : syracuseStep 1894403 = 2841605) B2841605
theorem B1263619 : Blo 1262449 1263619 := bstep (se 1 (by rfl) ⟨947714, by rfl⟩ : syracuseStep 1263619 = 1895429) B1895429
theorem B2131987 : Blo 1262449 2131987 := bstep (se 1 (by rfl) ⟨1598990, by rfl⟩ : syracuseStep 2131987 = 3197981) B3197981
theorem B1263635 : Blo 1262449 1263635 := bstep (se 1 (by rfl) ⟨947726, by rfl⟩ : syracuseStep 1263635 = 1895453) B1895453
theorem B1894433 : Blo 1262449 1894433 := bstep (se 2 (by rfl) ⟨710412, by rfl⟩ : syracuseStep 1894433 = 1420825) B1420825
theorem B1263651 : Blo 1262449 1263651 := bstep (se 1 (by rfl) ⟨947738, by rfl⟩ : syracuseStep 1263651 = 1895477) B1895477
theorem B1894451 : Blo 1262449 1894451 := bstep (se 1 (by rfl) ⟨1420838, by rfl⟩ : syracuseStep 1894451 = 2841677) B2841677
theorem B1263667 : Blo 1262449 1263667 := bstep (se 1 (by rfl) ⟨947750, by rfl⟩ : syracuseStep 1263667 = 1895501) B1895501
theorem B1263683 : Blo 1262449 1263683 := bstep (se 1 (by rfl) ⟨947762, by rfl⟩ : syracuseStep 1263683 = 1895525) B1895525
theorem B1894481 : Blo 1262449 1894481 := bstep (se 2 (by rfl) ⟨710430, by rfl⟩ : syracuseStep 1894481 = 1420861) B1420861
theorem B3197009 : Blo 1262449 3197009 := bstep (se 2 (by rfl) ⟨1198878, by rfl⟩ : syracuseStep 3197009 = 2397757) B2397757
theorem B1263699 : Blo 1262449 1263699 := bstep (se 1 (by rfl) ⟨947774, by rfl⟩ : syracuseStep 1263699 = 1895549) B1895549
theorem B1894499 : Blo 1262449 1894499 := bstep (se 1 (by rfl) ⟨1420874, by rfl⟩ : syracuseStep 1894499 = 2841749) B2841749
theorem B3598435 : Blo 1262449 3598435 := bstep (se 1 (by rfl) ⟨2698826, by rfl⟩ : syracuseStep 3598435 = 5397653) B5397653
theorem B1263715 : Blo 1262449 1263715 := bstep (se 1 (by rfl) ⟨947786, by rfl⟩ : syracuseStep 1263715 = 1895573) B1895573
theorem B1263731 : Blo 1262449 1263731 := bstep (se 1 (by rfl) ⟨947798, by rfl⟩ : syracuseStep 1263731 = 1895597) B1895597
theorem B1894529 : Blo 1262449 1894529 := bstep (se 2 (by rfl) ⟨710448, by rfl⟩ : syracuseStep 1894529 = 1420897) B1420897
theorem B1263747 : Blo 1262449 1263747 := bstep (se 1 (by rfl) ⟨947810, by rfl⟩ : syracuseStep 1263747 = 1895621) B1895621
theorem B3598481 : Blo 1262449 3598481 := bstep (se 2 (by rfl) ⟨1349430, by rfl⟩ : syracuseStep 3598481 = 2698861) B2698861
theorem B1894547 : Blo 1262449 1894547 := bstep (se 1 (by rfl) ⟨1420910, by rfl⟩ : syracuseStep 1894547 = 2841821) B2841821
theorem B1263763 : Blo 1262449 1263763 := bstep (se 1 (by rfl) ⟨947822, by rfl⟩ : syracuseStep 1263763 = 1895645) B1895645
theorem B2132129 : Blo 1262449 2132129 := bstep (se 2 (by rfl) ⟨799548, by rfl⟩ : syracuseStep 2132129 = 1599097) B1599097
theorem B1263779 : Blo 1262449 1263779 := bstep (se 1 (by rfl) ⟨947834, by rfl⟩ : syracuseStep 1263779 = 1895669) B1895669
theorem B1894577 : Blo 1262449 1894577 := bstep (se 2 (by rfl) ⟨710466, by rfl⟩ : syracuseStep 1894577 = 1420933) B1420933
theorem B1263795 : Blo 1262449 1263795 := bstep (se 1 (by rfl) ⟨947846, by rfl⟩ : syracuseStep 1263795 = 1895693) B1895693
theorem B1894595 : Blo 1262449 1894595 := bstep (se 1 (by rfl) ⟨1420946, by rfl⟩ : syracuseStep 1894595 = 2841893) B2841893
theorem B1263811 : Blo 1262449 1263811 := bstep (se 1 (by rfl) ⟨947858, by rfl⟩ : syracuseStep 1263811 = 1895717) B1895717
theorem B2844881 : Blo 1262449 2844881 := bstep (se 2 (by rfl) ⟨1066830, by rfl⟩ : syracuseStep 2844881 = 2133661) B2133661
theorem B1263827 : Blo 1262449 1263827 := bstep (se 1 (by rfl) ⟨947870, by rfl⟩ : syracuseStep 1263827 = 1895741) B1895741
theorem B1894625 : Blo 1262449 1894625 := bstep (se 2 (by rfl) ⟨710484, by rfl⟩ : syracuseStep 1894625 = 1420969) B1420969
theorem B1263843 : Blo 1262449 1263843 := bstep (se 1 (by rfl) ⟨947882, by rfl⟩ : syracuseStep 1263843 = 1895765) B1895765
theorem B2844899 : Blo 1262449 2844899 := bstep (se 1 (by rfl) ⟨2133674, by rfl⟩ : syracuseStep 2844899 = 4267349) B4267349
theorem B7194865 : Blo 1262449 7194865 := bstep (se 2 (by rfl) ⟨2698074, by rfl⟩ : syracuseStep 7194865 = 5396149) B5396149
theorem B1894643 : Blo 1262449 1894643 := bstep (se 1 (by rfl) ⟨1420982, by rfl⟩ : syracuseStep 1894643 = 2841965) B2841965
theorem B1263859 : Blo 1262449 1263859 := bstep (se 1 (by rfl) ⟨947894, by rfl⟩ : syracuseStep 1263859 = 1895789) B1895789
theorem B1263875 : Blo 1262449 1263875 := bstep (se 1 (by rfl) ⟨947906, by rfl⟩ : syracuseStep 1263875 = 1895813) B1895813
theorem B1894673 : Blo 1262449 1894673 := bstep (se 2 (by rfl) ⟨710502, by rfl⟩ : syracuseStep 1894673 = 1421005) B1421005
theorem B1263891 : Blo 1262449 1263891 := bstep (se 1 (by rfl) ⟨947918, by rfl⟩ : syracuseStep 1263891 = 1895837) B1895837
theorem B2132257 : Blo 1262449 2132257 := bstep (se 2 (by rfl) ⟨799596, by rfl⟩ : syracuseStep 2132257 = 1599193) B1599193
theorem B1894691 : Blo 1262449 1894691 := bstep (se 1 (by rfl) ⟨1421018, by rfl⟩ : syracuseStep 1894691 = 2842037) B2842037
theorem B1263907 : Blo 1262449 1263907 := bstep (se 1 (by rfl) ⟨947930, by rfl⟩ : syracuseStep 1263907 = 1895861) B1895861
theorem B1263923 : Blo 1262449 1263923 := bstep (se 1 (by rfl) ⟨947942, by rfl⟩ : syracuseStep 1263923 = 1895885) B1895885
theorem B1894721 : Blo 1262449 1894721 := bstep (se 2 (by rfl) ⟨710520, by rfl⟩ : syracuseStep 1894721 = 1421041) B1421041
theorem B2132291 : Blo 1262449 2132291 := bstep (se 1 (by rfl) ⟨1599218, by rfl⟩ : syracuseStep 2132291 = 3198437) B3198437
theorem B1263939 : Blo 1262449 1263939 := bstep (se 1 (by rfl) ⟨947954, by rfl⟩ : syracuseStep 1263939 = 1895909) B1895909
theorem B1894739 : Blo 1262449 1894739 := bstep (se 1 (by rfl) ⟨1421054, by rfl⟩ : syracuseStep 1894739 = 2842109) B2842109
theorem B1263955 : Blo 1262449 1263955 := bstep (se 1 (by rfl) ⟨947966, by rfl⟩ : syracuseStep 1263955 = 1895933) B1895933
theorem B1263971 : Blo 1262449 1263971 := bstep (se 1 (by rfl) ⟨947978, by rfl⟩ : syracuseStep 1263971 = 1895957) B1895957
theorem B1894769 : Blo 1262449 1894769 := bstep (se 2 (by rfl) ⟨710538, by rfl⟩ : syracuseStep 1894769 = 1421077) B1421077
theorem B1263987 : Blo 1262449 1263987 := bstep (se 1 (by rfl) ⟨947990, by rfl⟩ : syracuseStep 1263987 = 1895981) B1895981
theorem B1894787 : Blo 1262449 1894787 := bstep (se 1 (by rfl) ⟨1421090, by rfl⟩ : syracuseStep 1894787 = 2842181) B2842181
theorem B1264003 : Blo 1262449 1264003 := bstep (se 1 (by rfl) ⟨948002, by rfl⟩ : syracuseStep 1264003 = 1896005) B1896005
theorem B1264019 : Blo 1262449 1264019 := bstep (se 1 (by rfl) ⟨948014, by rfl⟩ : syracuseStep 1264019 = 1896029) B1896029
theorem B1894817 : Blo 1262449 1894817 := bstep (se 2 (by rfl) ⟨710556, by rfl⟩ : syracuseStep 1894817 = 1421113) B1421113
theorem B1264035 : Blo 1262449 1264035 := bstep (se 1 (by rfl) ⟨948026, by rfl⟩ : syracuseStep 1264035 = 1896053) B1896053
theorem B1599907 : Blo 1262449 1599907 := bstep (se 1 (by rfl) ⟨1199930, by rfl⟩ : syracuseStep 1599907 = 2399861) B2399861
theorem B1894835 : Blo 1262449 1894835 := bstep (se 1 (by rfl) ⟨1421126, by rfl⟩ : syracuseStep 1894835 = 2842253) B2842253
theorem B1264051 : Blo 1262449 1264051 := bstep (se 1 (by rfl) ⟨948038, by rfl⟩ : syracuseStep 1264051 = 1896077) B1896077
theorem B2132419 : Blo 1262449 2132419 := bstep (se 1 (by rfl) ⟨1599314, by rfl⟩ : syracuseStep 2132419 = 3198629) B3198629
theorem B1264067 : Blo 1262449 1264067 := bstep (se 1 (by rfl) ⟨948050, by rfl⟩ : syracuseStep 1264067 = 1896101) B1896101
theorem B1894865 : Blo 1262449 1894865 := bstep (se 2 (by rfl) ⟨710574, by rfl⟩ : syracuseStep 1894865 = 1421149) B1421149
theorem B1264083 : Blo 1262449 1264083 := bstep (se 1 (by rfl) ⟨948062, by rfl⟩ : syracuseStep 1264083 = 1896125) B1896125
theorem B12470755 : Blo 1262449 12470755 := bstep (se 1 (by rfl) ⟨9353066, by rfl⟩ : syracuseStep 12470755 = 18706133) B18706133
theorem B1894883 : Blo 1262449 1894883 := bstep (se 1 (by rfl) ⟨1421162, by rfl⟩ : syracuseStep 1894883 = 2842325) B2842325
theorem B1264099 : Blo 1262449 1264099 := bstep (se 1 (by rfl) ⟨948074, by rfl⟩ : syracuseStep 1264099 = 1896149) B1896149
theorem B4262381 : Blo 1262449 4262381 := bstep (se 3 (by rfl) ⟨799196, by rfl⟩ : syracuseStep 4262381 = 1598393) B1598393
theorem B3893741 : Blo 1262449 3893741 := bstep (se 3 (by rfl) ⟨730076, by rfl⟩ : syracuseStep 3893741 = 1460153) B1460153
theorem B1264115 : Blo 1262449 1264115 := bstep (se 1 (by rfl) ⟨948086, by rfl⟩ : syracuseStep 1264115 = 1896173) B1896173
theorem B1894913 : Blo 1262449 1894913 := bstep (se 2 (by rfl) ⟨710592, by rfl⟩ : syracuseStep 1894913 = 1421185) B1421185
theorem B1264131 : Blo 1262449 1264131 := bstep (se 1 (by rfl) ⟨948098, by rfl⟩ : syracuseStep 1264131 = 1896197) B1896197
theorem B1600003 : Blo 1262449 1600003 := bstep (se 1 (by rfl) ⟨1200002, by rfl⟩ : syracuseStep 1600003 = 2400005) B2400005
theorem B1894931 : Blo 1262449 1894931 := bstep (se 1 (by rfl) ⟨1421198, by rfl⟩ : syracuseStep 1894931 = 2842397) B2842397
theorem B1264147 : Blo 1262449 1264147 := bstep (se 1 (by rfl) ⟨948110, by rfl⟩ : syracuseStep 1264147 = 1896221) B1896221
theorem B4262435 : Blo 1262449 4262435 := bstep (se 1 (by rfl) ⟨3196826, by rfl⟩ : syracuseStep 4262435 = 6393653) B6393653
theorem B1264163 : Blo 1262449 1264163 := bstep (se 1 (by rfl) ⟨948122, by rfl⟩ : syracuseStep 1264163 = 1896245) B1896245
theorem B1894961 : Blo 1262449 1894961 := bstep (se 2 (by rfl) ⟨710610, by rfl⟩ : syracuseStep 1894961 = 1421221) B1421221
theorem B1264179 : Blo 1262449 1264179 := bstep (se 1 (by rfl) ⟨948134, by rfl⟩ : syracuseStep 1264179 = 1896269) B1896269
theorem B1894979 : Blo 1262449 1894979 := bstep (se 1 (by rfl) ⟨1421234, by rfl⟩ : syracuseStep 1894979 = 2842469) B2842469
theorem B1264195 : Blo 1262449 1264195 := bstep (se 1 (by rfl) ⟨948146, by rfl⟩ : syracuseStep 1264195 = 1896293) B1896293
theorem B2132561 : Blo 1262449 2132561 := bstep (se 2 (by rfl) ⟨799710, by rfl⟩ : syracuseStep 2132561 = 1599421) B1599421
theorem B1264211 : Blo 1262449 1264211 := bstep (se 1 (by rfl) ⟨948158, by rfl⟩ : syracuseStep 1264211 = 1896317) B1896317
theorem B1895009 : Blo 1262449 1895009 := bstep (se 2 (by rfl) ⟨710628, by rfl⟩ : syracuseStep 1895009 = 1421257) B1421257
theorem B6482531 : Blo 1262449 6482531 := bstep (se 1 (by rfl) ⟨4861898, by rfl⟩ : syracuseStep 6482531 = 9723797) B9723797
theorem B1264227 : Blo 1262449 1264227 := bstep (se 1 (by rfl) ⟨948170, by rfl⟩ : syracuseStep 1264227 = 1896341) B1896341
theorem B1895027 : Blo 1262449 1895027 := bstep (se 1 (by rfl) ⟨1421270, by rfl⟩ : syracuseStep 1895027 = 2842541) B2842541
theorem B1264243 : Blo 1262449 1264243 := bstep (se 1 (by rfl) ⟨948182, by rfl⟩ : syracuseStep 1264243 = 1896365) B1896365
theorem B1264259 : Blo 1262449 1264259 := bstep (se 1 (by rfl) ⟨948194, by rfl⟩ : syracuseStep 1264259 = 1896389) B1896389
theorem B1895057 : Blo 1262449 1895057 := bstep (se 2 (by rfl) ⟨710646, by rfl⟩ : syracuseStep 1895057 = 1421293) B1421293
theorem B1264275 : Blo 1262449 1264275 := bstep (se 1 (by rfl) ⟨948206, by rfl⟩ : syracuseStep 1264275 = 1896413) B1896413
theorem B1895075 : Blo 1262449 1895075 := bstep (se 1 (by rfl) ⟨1421306, by rfl⟩ : syracuseStep 1895075 = 2842613) B2842613
theorem B1264291 : Blo 1262449 1264291 := bstep (se 1 (by rfl) ⟨948218, by rfl⟩ : syracuseStep 1264291 = 1896437) B1896437
theorem B1264307 : Blo 1262449 1264307 := bstep (se 1 (by rfl) ⟨948230, by rfl⟩ : syracuseStep 1264307 = 1896461) B1896461
theorem B1895105 : Blo 1262449 1895105 := bstep (se 2 (by rfl) ⟨710664, by rfl⟩ : syracuseStep 1895105 = 1421329) B1421329
theorem B1264323 : Blo 1262449 1264323 := bstep (se 1 (by rfl) ⟨948242, by rfl⟩ : syracuseStep 1264323 = 1896485) B1896485
theorem B2132689 : Blo 1262449 2132689 := bstep (se 2 (by rfl) ⟨799758, by rfl⟩ : syracuseStep 2132689 = 1599517) B1599517
theorem B1895123 : Blo 1262449 1895123 := bstep (se 1 (by rfl) ⟨1421342, by rfl⟩ : syracuseStep 1895123 = 2842685) B2842685
theorem B1264339 : Blo 1262449 1264339 := bstep (se 1 (by rfl) ⟨948254, by rfl⟩ : syracuseStep 1264339 = 1896509) B1896509
theorem B1264355 : Blo 1262449 1264355 := bstep (se 1 (by rfl) ⟨948266, by rfl⟩ : syracuseStep 1264355 = 1896533) B1896533
theorem B1895153 : Blo 1262449 1895153 := bstep (se 2 (by rfl) ⟨710682, by rfl⟩ : syracuseStep 1895153 = 1421365) B1421365
theorem B2132723 : Blo 1262449 2132723 := bstep (se 1 (by rfl) ⟨1599542, by rfl⟩ : syracuseStep 2132723 = 3199085) B3199085
theorem B1264371 : Blo 1262449 1264371 := bstep (se 1 (by rfl) ⟨948278, by rfl⟩ : syracuseStep 1264371 = 1896557) B1896557
theorem B1895171 : Blo 1262449 1895171 := bstep (se 1 (by rfl) ⟨1421378, by rfl⟩ : syracuseStep 1895171 = 2842757) B2842757
theorem B1264387 : Blo 1262449 1264387 := bstep (se 1 (by rfl) ⟨948290, by rfl⟩ : syracuseStep 1264387 = 1896581) B1896581
theorem B6400781 : Blo 1262449 6400781 := bstep (se 3 (by rfl) ⟨1200146, by rfl⟩ : syracuseStep 6400781 = 2400293) B2400293
theorem B12151565 : Blo 1262449 12151565 := bstep (se 3 (by rfl) ⟨2278418, by rfl⟩ : syracuseStep 12151565 = 4556837) B4556837
theorem B1518355 : Blo 1262449 1518355 := bstep (se 1 (by rfl) ⟨1138766, by rfl⟩ : syracuseStep 1518355 = 2277533) B2277533
theorem B1264403 : Blo 1262449 1264403 := bstep (se 1 (by rfl) ⟨948302, by rfl⟩ : syracuseStep 1264403 = 1896605) B1896605
theorem B1895201 : Blo 1262449 1895201 := bstep (se 2 (by rfl) ⟨710700, by rfl⟩ : syracuseStep 1895201 = 1421401) B1421401
theorem B1264419 : Blo 1262449 1264419 := bstep (se 1 (by rfl) ⟨948314, by rfl⟩ : syracuseStep 1264419 = 1896629) B1896629
theorem B4262705 : Blo 1262449 4262705 := bstep (se 2 (by rfl) ⟨1598514, by rfl⟩ : syracuseStep 4262705 = 3197029) B3197029
theorem B1895219 : Blo 1262449 1895219 := bstep (se 1 (by rfl) ⟨1421414, by rfl⟩ : syracuseStep 1895219 = 2842829) B2842829
theorem B1264435 : Blo 1262449 1264435 := bstep (se 1 (by rfl) ⟨948326, by rfl⟩ : syracuseStep 1264435 = 1896653) B1896653
theorem B1895249 : Blo 1262449 1895249 := bstep (se 2 (by rfl) ⟨710718, by rfl⟩ : syracuseStep 1895249 = 1421437) B1421437
theorem B1895267 : Blo 1262449 1895267 := bstep (se 1 (by rfl) ⟨1421450, by rfl⟩ : syracuseStep 1895267 = 2842901) B2842901
theorem B2132851 : Blo 1262449 2132851 := bstep (se 1 (by rfl) ⟨1599638, by rfl⟩ : syracuseStep 2132851 = 3199277) B3199277
theorem B1895297 : Blo 1262449 1895297 := bstep (se 2 (by rfl) ⟨710736, by rfl⟩ : syracuseStep 1895297 = 1421473) B1421473
theorem B1895315 : Blo 1262449 1895315 := bstep (se 1 (by rfl) ⟨1421486, by rfl⟩ : syracuseStep 1895315 = 2842973) B2842973
theorem B3034019 : Blo 1262449 3034019 := bstep (se 1 (by rfl) ⟨2275514, by rfl⟩ : syracuseStep 3034019 = 4551029) B4551029
theorem B1895345 : Blo 1262449 1895345 := bstep (se 2 (by rfl) ⟨710754, by rfl⟩ : syracuseStep 1895345 = 1421509) B1421509
theorem B1895363 : Blo 1262449 1895363 := bstep (se 1 (by rfl) ⟨1421522, by rfl⟩ : syracuseStep 1895363 = 2843045) B2843045
theorem B1895393 : Blo 1262449 1895393 := bstep (se 2 (by rfl) ⟨710772, by rfl⟩ : syracuseStep 1895393 = 1421545) B1421545
theorem B1919971 : Blo 1262449 1919971 := bstep (se 1 (by rfl) ⟨1439978, by rfl⟩ : syracuseStep 1919971 = 2879957) B2879957
theorem B1895411 : Blo 1262449 1895411 := bstep (se 1 (by rfl) ⟨1421558, by rfl⟩ : syracuseStep 1895411 = 2843117) B2843117
theorem B2132993 : Blo 1262449 2132993 := bstep (se 2 (by rfl) ⟨799872, by rfl⟩ : syracuseStep 2132993 = 1599745) B1599745
theorem B1895441 : Blo 1262449 1895441 := bstep (se 2 (by rfl) ⟨710790, by rfl⟩ : syracuseStep 1895441 = 1421581) B1421581
theorem B1895459 : Blo 1262449 1895459 := bstep (se 1 (by rfl) ⟨1421594, by rfl⟩ : syracuseStep 1895459 = 2843189) B2843189
theorem B3198001 : Blo 1262449 3198001 := bstep (se 2 (by rfl) ⟨1199250, by rfl⟩ : syracuseStep 3198001 = 2398501) B2398501
theorem B1420339 : Blo 1262449 1420339 := bstep (se 1 (by rfl) ⟨1065254, by rfl⟩ : syracuseStep 1420339 = 2130509) B2130509
theorem B1895489 : Blo 1262449 1895489 := bstep (se 2 (by rfl) ⟨710808, by rfl⟩ : syracuseStep 1895489 = 1421617) B1421617
theorem B4795469 : Blo 1262449 4795469 := bstep (se 3 (by rfl) ⟨899150, by rfl⟩ : syracuseStep 4795469 = 1798301) B1798301
theorem B1895507 : Blo 1262449 1895507 := bstep (se 1 (by rfl) ⟨1421630, by rfl⟩ : syracuseStep 1895507 = 2843261) B2843261
theorem B8096867 : Blo 1262449 8096867 := bstep (se 1 (by rfl) ⟨6072650, by rfl⟩ : syracuseStep 8096867 = 12145301) B12145301
theorem B1895537 : Blo 1262449 1895537 := bstep (se 2 (by rfl) ⟨710826, by rfl⟩ : syracuseStep 1895537 = 1421653) B1421653
theorem B2133121 : Blo 1262449 2133121 := bstep (se 2 (by rfl) ⟨799920, by rfl⟩ : syracuseStep 2133121 = 1599841) B1599841
theorem B1895555 : Blo 1262449 1895555 := bstep (se 1 (by rfl) ⟨1421666, by rfl⟩ : syracuseStep 1895555 = 2843333) B2843333
theorem B1895585 : Blo 1262449 1895585 := bstep (se 2 (by rfl) ⟨710844, by rfl⟩ : syracuseStep 1895585 = 1421689) B1421689
theorem B2133155 : Blo 1262449 2133155 := bstep (se 1 (by rfl) ⟨1599866, by rfl⟩ : syracuseStep 2133155 = 3199733) B3199733
theorem B1895603 : Blo 1262449 1895603 := bstep (se 1 (by rfl) ⟨1421702, by rfl⟩ : syracuseStep 1895603 = 2843405) B2843405
theorem B1420483 : Blo 1262449 1420483 := bstep (se 1 (by rfl) ⟨1065362, by rfl⟩ : syracuseStep 1420483 = 2130725) B2130725
theorem B3509453 : Blo 1262449 3509453 := bstep (se 3 (by rfl) ⟨658022, by rfl⟩ : syracuseStep 3509453 = 1316045) B1316045
theorem B1895633 : Blo 1262449 1895633 := bstep (se 2 (by rfl) ⟨710862, by rfl⟩ : syracuseStep 1895633 = 1421725) B1421725
theorem B1895651 : Blo 1262449 1895651 := bstep (se 1 (by rfl) ⟨1421738, by rfl⟩ : syracuseStep 1895651 = 2843477) B2843477
theorem B1895681 : Blo 1262449 1895681 := bstep (se 2 (by rfl) ⟨710880, by rfl⟩ : syracuseStep 1895681 = 1421761) B1421761
theorem B1895699 : Blo 1262449 1895699 := bstep (se 1 (by rfl) ⟨1421774, by rfl⟩ : syracuseStep 1895699 = 2843549) B2843549
theorem B2133283 : Blo 1262449 2133283 := bstep (se 1 (by rfl) ⟨1599962, by rfl⟩ : syracuseStep 2133283 = 3199925) B3199925
theorem B1895729 : Blo 1262449 1895729 := bstep (se 2 (by rfl) ⟨710898, by rfl⟩ : syracuseStep 1895729 = 1421797) B1421797
theorem B3198275 : Blo 1262449 3198275 := bstep (se 1 (by rfl) ⟨2398706, by rfl⟩ : syracuseStep 3198275 = 4797413) B4797413
theorem B1895747 : Blo 1262449 1895747 := bstep (se 1 (by rfl) ⟨1421810, by rfl⟩ : syracuseStep 1895747 = 2843621) B2843621
theorem B4263245 : Blo 1262449 4263245 := bstep (se 3 (by rfl) ⟨799358, by rfl⟩ : syracuseStep 4263245 = 1598717) B1598717
theorem B1420627 : Blo 1262449 1420627 := bstep (se 1 (by rfl) ⟨1065470, by rfl⟩ : syracuseStep 1420627 = 2130941) B2130941
theorem B1895777 : Blo 1262449 1895777 := bstep (se 2 (by rfl) ⟨710916, by rfl⟩ : syracuseStep 1895777 = 1421833) B1421833
theorem B3460465 : Blo 1262449 3460465 := bstep (se 2 (by rfl) ⟨1297674, by rfl⟩ : syracuseStep 3460465 = 2595349) B2595349
theorem B1895795 : Blo 1262449 1895795 := bstep (se 1 (by rfl) ⟨1421846, by rfl⟩ : syracuseStep 1895795 = 2843693) B2843693
theorem B4263299 : Blo 1262449 4263299 := bstep (se 1 (by rfl) ⟨3197474, by rfl⟩ : syracuseStep 4263299 = 6394949) B6394949
theorem B4050317 : Blo 1262449 4050317 := bstep (se 3 (by rfl) ⟨759434, by rfl⟩ : syracuseStep 4050317 = 1518869) B1518869
theorem B2559377 : Blo 1262449 2559377 := bstep (se 2 (by rfl) ⟨959766, by rfl⟩ : syracuseStep 2559377 = 1919533) B1919533
theorem B1895825 : Blo 1262449 1895825 := bstep (se 2 (by rfl) ⟨710934, by rfl⟩ : syracuseStep 1895825 = 1421869) B1421869
theorem B1895843 : Blo 1262449 1895843 := bstep (se 1 (by rfl) ⟨1421882, by rfl⟩ : syracuseStep 1895843 = 2843765) B2843765
theorem B2133425 : Blo 1262449 2133425 := bstep (se 2 (by rfl) ⟨800034, by rfl⟩ : syracuseStep 2133425 = 1600069) B1600069
theorem B1641907 : Blo 1262449 1641907 := bstep (se 1 (by rfl) ⟨1231430, by rfl⟩ : syracuseStep 1641907 = 2462861) B2462861
theorem B1895873 : Blo 1262449 1895873 := bstep (se 2 (by rfl) ⟨710952, by rfl⟩ : syracuseStep 1895873 = 1421905) B1421905
theorem B1895891 : Blo 1262449 1895891 := bstep (se 1 (by rfl) ⟨1421918, by rfl⟩ : syracuseStep 1895891 = 2843837) B2843837
theorem B1420771 : Blo 1262449 1420771 := bstep (se 1 (by rfl) ⟨1065578, by rfl⟩ : syracuseStep 1420771 = 2131157) B2131157
theorem B6393329 : Blo 1262449 6393329 := bstep (se 2 (by rfl) ⟨2397498, by rfl⟩ : syracuseStep 6393329 = 4794997) B4794997
theorem B1895921 : Blo 1262449 1895921 := bstep (se 2 (by rfl) ⟨710970, by rfl⟩ : syracuseStep 1895921 = 1421941) B1421941
theorem B3198467 : Blo 1262449 3198467 := bstep (se 1 (by rfl) ⟨2398850, by rfl⟩ : syracuseStep 3198467 = 4797701) B4797701
theorem B1895939 : Blo 1262449 1895939 := bstep (se 1 (by rfl) ⟨1421954, by rfl⟩ : syracuseStep 1895939 = 2843909) B2843909
theorem B4050445 : Blo 1262449 4050445 := bstep (se 3 (by rfl) ⟨759458, by rfl⟩ : syracuseStep 4050445 = 1518917) B1518917
theorem B1895969 : Blo 1262449 1895969 := bstep (se 2 (by rfl) ⟨710988, by rfl⟩ : syracuseStep 1895969 = 1421977) B1421977
theorem B2133553 : Blo 1262449 2133553 := bstep (se 2 (by rfl) ⟨800082, by rfl⟩ : syracuseStep 2133553 = 1600165) B1600165
theorem B1895987 : Blo 1262449 1895987 := bstep (se 1 (by rfl) ⟨1421990, by rfl⟩ : syracuseStep 1895987 = 2843981) B2843981
theorem B3599939 : Blo 1262449 3599939 := bstep (se 1 (by rfl) ⟨2699954, by rfl⟩ : syracuseStep 3599939 = 5399909) B5399909
theorem B9588293 : Blo 1262449 9588293 := bstep (se 4 (by rfl) ⟨898902, by rfl⟩ : syracuseStep 9588293 = 1797805) B1797805
theorem B1896017 : Blo 1262449 1896017 := bstep (se 2 (by rfl) ⟨711006, by rfl⟩ : syracuseStep 1896017 = 1422013) B1422013
theorem B2133587 : Blo 1262449 2133587 := bstep (se 1 (by rfl) ⟨1600190, by rfl⟩ : syracuseStep 2133587 = 3200381) B3200381
theorem B1281619 : Blo 1262449 1281619 := bstep (se 1 (by rfl) ⟨961214, by rfl⟩ : syracuseStep 1281619 = 1922429) B1922429
theorem B1896035 : Blo 1262449 1896035 := bstep (se 1 (by rfl) ⟨1422026, by rfl⟩ : syracuseStep 1896035 = 2844053) B2844053
theorem B1420915 : Blo 1262449 1420915 := bstep (se 1 (by rfl) ⟨1065686, by rfl⟩ : syracuseStep 1420915 = 2131373) B2131373
theorem B1896065 : Blo 1262449 1896065 := bstep (se 2 (by rfl) ⟨711024, by rfl⟩ : syracuseStep 1896065 = 1422049) B1422049
theorem B4263569 : Blo 1262449 4263569 := bstep (se 2 (by rfl) ⟨1598838, by rfl⟩ : syracuseStep 4263569 = 3197677) B3197677
theorem B1896083 : Blo 1262449 1896083 := bstep (se 1 (by rfl) ⟨1422062, by rfl⟩ : syracuseStep 1896083 = 2844125) B2844125
theorem B7196323 : Blo 1262449 7196323 := bstep (se 1 (by rfl) ⟨5397242, by rfl⟩ : syracuseStep 7196323 = 10794485) B10794485
theorem B1896113 : Blo 1262449 1896113 := bstep (se 2 (by rfl) ⟨711042, by rfl⟩ : syracuseStep 1896113 = 1422085) B1422085
theorem B1896131 : Blo 1262449 1896131 := bstep (se 1 (by rfl) ⟨1422098, by rfl⟩ : syracuseStep 1896131 = 2844197) B2844197
theorem B2133715 : Blo 1262449 2133715 := bstep (se 1 (by rfl) ⟨1600286, by rfl⟩ : syracuseStep 2133715 = 3200573) B3200573
theorem B1896161 : Blo 1262449 1896161 := bstep (se 2 (by rfl) ⟨711060, by rfl⟩ : syracuseStep 1896161 = 1422121) B1422121
theorem B1896179 : Blo 1262449 1896179 := bstep (se 1 (by rfl) ⟨1422134, by rfl⟩ : syracuseStep 1896179 = 2844269) B2844269
theorem B1421059 : Blo 1262449 1421059 := bstep (se 1 (by rfl) ⟨1065794, by rfl⟩ : syracuseStep 1421059 = 2131589) B2131589
theorem B4050701 : Blo 1262449 4050701 := bstep (se 3 (by rfl) ⟨759506, by rfl⟩ : syracuseStep 4050701 = 1519013) B1519013
theorem B1896209 : Blo 1262449 1896209 := bstep (se 2 (by rfl) ⟨711078, by rfl⟩ : syracuseStep 1896209 = 1422157) B1422157
theorem B1404691 : Blo 1262449 1404691 := bstep (se 1 (by rfl) ⟨1053518, by rfl⟩ : syracuseStep 1404691 = 2107037) B2107037
theorem B1896227 : Blo 1262449 1896227 := bstep (se 1 (by rfl) ⟨1422170, by rfl⟩ : syracuseStep 1896227 = 2844341) B2844341
theorem B1896257 : Blo 1262449 1896257 := bstep (se 2 (by rfl) ⟨711096, by rfl⟩ : syracuseStep 1896257 = 1422193) B1422193
theorem B6074189 : Blo 1262449 6074189 := bstep (se 3 (by rfl) ⟨1138910, by rfl⟩ : syracuseStep 6074189 = 2277821) B2277821
theorem B1896275 : Blo 1262449 1896275 := bstep (se 1 (by rfl) ⟨1422206, by rfl⟩ : syracuseStep 1896275 = 2844413) B2844413
theorem B3239779 : Blo 1262449 3239779 := bstep (se 1 (by rfl) ⟨2429834, by rfl⟩ : syracuseStep 3239779 = 4859669) B4859669
theorem B3510125 : Blo 1262449 3510125 := bstep (se 3 (by rfl) ⟨658148, by rfl⟩ : syracuseStep 3510125 = 1316297) B1316297
theorem B4796273 : Blo 1262449 4796273 := bstep (se 2 (by rfl) ⟨1798602, by rfl⟩ : syracuseStep 4796273 = 3597205) B3597205
theorem B1896305 : Blo 1262449 1896305 := bstep (se 2 (by rfl) ⟨711114, by rfl⟩ : syracuseStep 1896305 = 1422229) B1422229
theorem B1707907 : Blo 1262449 1707907 := bstep (se 1 (by rfl) ⟨1280930, by rfl⟩ : syracuseStep 1707907 = 2561861) B2561861
theorem B1896323 : Blo 1262449 1896323 := bstep (se 1 (by rfl) ⟨1422242, by rfl⟩ : syracuseStep 1896323 = 2844485) B2844485
theorem B1798033 : Blo 1262449 1798033 := bstep (se 2 (by rfl) ⟨674262, by rfl⟩ : syracuseStep 1798033 = 1348525) B1348525
theorem B1421203 : Blo 1262449 1421203 := bstep (se 1 (by rfl) ⟨1065902, by rfl⟩ : syracuseStep 1421203 = 2131805) B2131805
theorem B1896353 : Blo 1262449 1896353 := bstep (se 2 (by rfl) ⟨711132, by rfl⟩ : syracuseStep 1896353 = 1422265) B1422265
theorem B1896371 : Blo 1262449 1896371 := bstep (se 1 (by rfl) ⟨1422278, by rfl⟩ : syracuseStep 1896371 = 2844557) B2844557
theorem B2699203 : Blo 1262449 2699203 := bstep (se 1 (by rfl) ⟨2024402, by rfl⟩ : syracuseStep 2699203 = 4048805) B4048805
theorem B1896401 : Blo 1262449 1896401 := bstep (se 2 (by rfl) ⟨711150, by rfl⟩ : syracuseStep 1896401 = 1422301) B1422301
theorem B1896419 : Blo 1262449 1896419 := bstep (se 1 (by rfl) ⟨1422314, by rfl⟩ : syracuseStep 1896419 = 2844629) B2844629
theorem B1896449 : Blo 1262449 1896449 := bstep (se 2 (by rfl) ⟨711168, by rfl⟩ : syracuseStep 1896449 = 1422337) B1422337
theorem B1798147 : Blo 1262449 1798147 := bstep (se 1 (by rfl) ⟨1348610, by rfl⟩ : syracuseStep 1798147 = 2697221) B2697221
theorem B1896467 : Blo 1262449 1896467 := bstep (se 1 (by rfl) ⟨1422350, by rfl⟩ : syracuseStep 1896467 = 2844701) B2844701
theorem B1421347 : Blo 1262449 1421347 := bstep (se 1 (by rfl) ⟨1066010, by rfl⟩ : syracuseStep 1421347 = 2132021) B2132021
theorem B1896497 : Blo 1262449 1896497 := bstep (se 2 (by rfl) ⟨711186, by rfl⟩ : syracuseStep 1896497 = 1422373) B1422373
theorem B1896515 : Blo 1262449 1896515 := bstep (se 1 (by rfl) ⟨1422386, by rfl⟩ : syracuseStep 1896515 = 2844773) B2844773
theorem B5394509 : Blo 1262449 5394509 := bstep (se 3 (by rfl) ⟨1011470, by rfl⟩ : syracuseStep 5394509 = 2022941) B2022941
theorem B1896545 : Blo 1262449 1896545 := bstep (se 2 (by rfl) ⟨711204, by rfl⟩ : syracuseStep 1896545 = 1422409) B1422409
theorem B5394545 : Blo 1262449 5394545 := bstep (se 2 (by rfl) ⟨2022954, by rfl⟩ : syracuseStep 5394545 = 4045909) B4045909
theorem B3035249 : Blo 1262449 3035249 := bstep (se 2 (by rfl) ⟨1138218, by rfl⟩ : syracuseStep 3035249 = 2276437) B2276437
theorem B9597041 : Blo 1262449 9597041 := bstep (se 2 (by rfl) ⟨3598890, by rfl⟩ : syracuseStep 9597041 = 7197781) B7197781
theorem B1896563 : Blo 1262449 1896563 := bstep (se 1 (by rfl) ⟨1422422, by rfl⟩ : syracuseStep 1896563 = 2844845) B2844845
theorem B1896593 : Blo 1262449 1896593 := bstep (se 2 (by rfl) ⟨711222, by rfl⟩ : syracuseStep 1896593 = 1422445) B1422445
theorem B1896611 : Blo 1262449 1896611 := bstep (se 1 (by rfl) ⟨1422458, by rfl⟩ : syracuseStep 1896611 = 2844917) B2844917
theorem B4264109 : Blo 1262449 4264109 := bstep (se 3 (by rfl) ⟨799520, by rfl⟩ : syracuseStep 4264109 = 1599041) B1599041
theorem B6828209 : Blo 1262449 6828209 := bstep (se 2 (by rfl) ⟨2560578, by rfl⟩ : syracuseStep 6828209 = 5121157) B5121157
theorem B7196849 : Blo 1262449 7196849 := bstep (se 2 (by rfl) ⟨2698818, by rfl⟩ : syracuseStep 7196849 = 5397637) B5397637
theorem B1421491 : Blo 1262449 1421491 := bstep (se 1 (by rfl) ⟨1066118, by rfl⟩ : syracuseStep 1421491 = 2132237) B2132237
theorem B1896641 : Blo 1262449 1896641 := bstep (se 2 (by rfl) ⟨711240, by rfl⟩ : syracuseStep 1896641 = 1422481) B1422481
theorem B1896659 : Blo 1262449 1896659 := bstep (se 1 (by rfl) ⟨1422494, by rfl⟩ : syracuseStep 1896659 = 2844989) B2844989
theorem B4264163 : Blo 1262449 4264163 := bstep (se 1 (by rfl) ⟨3198122, by rfl⟩ : syracuseStep 4264163 = 6396245) B6396245
theorem B6828293 : Blo 1262449 6828293 := bstep (se 4 (by rfl) ⟨640152, by rfl⟩ : syracuseStep 6828293 = 1280305) B1280305
theorem B14397749 : Blo 1262449 14397749 := bstep (se 5 (by rfl) ⟨674894, by rfl⟩ : syracuseStep 14397749 = 1349789) B1349789
theorem B1421635 : Blo 1262449 1421635 := bstep (se 1 (by rfl) ⟨1066226, by rfl⟩ : syracuseStep 1421635 = 2132453) B2132453
theorem B2052515 : Blo 1262449 2052515 := bstep (se 1 (by rfl) ⟨1539386, by rfl⟩ : syracuseStep 2052515 = 3078773) B3078773
theorem B3199409 : Blo 1262449 3199409 := bstep (se 2 (by rfl) ⟨1199778, by rfl⟩ : syracuseStep 3199409 = 2399557) B2399557
theorem B1421779 : Blo 1262449 1421779 := bstep (se 1 (by rfl) ⟨1066334, by rfl⟩ : syracuseStep 1421779 = 2132669) B2132669
theorem B3199459 : Blo 1262449 3199459 := bstep (se 1 (by rfl) ⟨2399594, by rfl⟩ : syracuseStep 3199459 = 4799189) B4799189
theorem B4264433 : Blo 1262449 4264433 := bstep (se 2 (by rfl) ⟨1599162, by rfl⟩ : syracuseStep 4264433 = 3198325) B3198325
theorem B4796941 : Blo 1262449 4796941 := bstep (se 3 (by rfl) ⟨899426, by rfl⟩ : syracuseStep 4796941 = 1798853) B1798853
theorem B1421923 : Blo 1262449 1421923 := bstep (se 1 (by rfl) ⟨1066442, by rfl⟩ : syracuseStep 1421923 = 2132885) B2132885
theorem B2396785 : Blo 1262449 2396785 := bstep (se 2 (by rfl) ⟨898794, by rfl⟩ : syracuseStep 2396785 = 1797589) B1797589
theorem B3199601 : Blo 1262449 3199601 := bstep (se 2 (by rfl) ⟨1199850, by rfl⟩ : syracuseStep 3199601 = 2399701) B2399701
theorem B1708673 : Blo 1262449 1708673 := bstep (se 2 (by rfl) ⟨640752, by rfl⟩ : syracuseStep 1708673 = 1281505) B1281505
theorem B2560643 : Blo 1262449 2560643 := bstep (se 1 (by rfl) ⟨1920482, by rfl⟩ : syracuseStep 2560643 = 3840965) B3840965
theorem B3412675 : Blo 1262449 3412675 := bstep (se 1 (by rfl) ⟨2559506, by rfl⟩ : syracuseStep 3412675 = 5119013) B5119013
theorem B3240689 : Blo 1262449 3240689 := bstep (se 2 (by rfl) ⟨1215258, by rfl⟩ : syracuseStep 3240689 = 2430517) B2430517
theorem B1422067 : Blo 1262449 1422067 := bstep (se 1 (by rfl) ⟨1066550, by rfl⟩ : syracuseStep 1422067 = 2133101) B2133101
theorem B8090381 : Blo 1262449 8090381 := bstep (se 3 (by rfl) ⟨1516946, by rfl⟩ : syracuseStep 8090381 = 3033893) B3033893
theorem B2396945 : Blo 1262449 2396945 := bstep (se 2 (by rfl) ⟨898854, by rfl⟩ : syracuseStep 2396945 = 1797709) B1797709
theorem B2700049 : Blo 1262449 2700049 := bstep (se 2 (by rfl) ⟨1012518, by rfl⟩ : syracuseStep 2700049 = 2025037) B2025037
theorem B1422211 : Blo 1262449 1422211 := bstep (se 1 (by rfl) ⟨1066658, by rfl⟩ : syracuseStep 1422211 = 2133317) B2133317
theorem B6394787 : Blo 1262449 6394787 := bstep (se 1 (by rfl) ⟨4796090, by rfl⟩ : syracuseStep 6394787 = 9592181) B9592181
theorem B4264973 : Blo 1262449 4264973 := bstep (se 3 (by rfl) ⟨799682, by rfl⟩ : syracuseStep 4264973 = 1599365) B1599365
theorem B1422355 : Blo 1262449 1422355 := bstep (se 1 (by rfl) ⟨1066766, by rfl⟩ : syracuseStep 1422355 = 2133533) B2133533
theorem B21058613 : Blo 1262449 21058613 := bstep (se 5 (by rfl) ⟨987122, by rfl⟩ : syracuseStep 21058613 = 1974245) B1974245
theorem B4265027 : Blo 1262449 4265027 := bstep (se 1 (by rfl) ⟨3198770, by rfl⟩ : syracuseStep 4265027 = 6397541) B6397541
theorem B2397347 : Blo 1262449 2397347 := bstep (se 1 (by rfl) ⟨1798010, by rfl⟩ : syracuseStep 2397347 = 3596021) B3596021
theorem B1422499 : Blo 1262449 1422499 := bstep (se 1 (by rfl) ⟨1066874, by rfl⟩ : syracuseStep 1422499 = 2133749) B2133749
theorem B7296227 : Blo 1262449 7296227 := bstep (se 1 (by rfl) ⟨5472170, by rfl⟩ : syracuseStep 7296227 = 10944341) B10944341
theorem B4797731 : Blo 1262449 4797731 := bstep (se 1 (by rfl) ⟨3598298, by rfl⟩ : syracuseStep 4797731 = 7196597) B7196597
theorem B1348931 : Blo 1262449 1348931 := bstep (se 1 (by rfl) ⟨1011698, by rfl⟩ : syracuseStep 1348931 = 2023397) B2023397
theorem B1799491 : Blo 1262449 1799491 := bstep (se 1 (by rfl) ⟨1349618, by rfl⟩ : syracuseStep 1799491 = 2699237) B2699237
theorem B4265297 : Blo 1262449 4265297 := bstep (se 2 (by rfl) ⟨1599486, by rfl⟩ : syracuseStep 4265297 = 3198973) B3198973
theorem B10245617 : Blo 1262449 10245617 := bstep (se 2 (by rfl) ⟨3842106, by rfl⟩ : syracuseStep 10245617 = 7684213) B7684213
theorem B5764621 : Blo 1262449 5764621 := bstep (se 3 (by rfl) ⟨1080866, by rfl⟩ : syracuseStep 5764621 = 2161733) B2161733
theorem B3200593 : Blo 1262449 3200593 := bstep (se 2 (by rfl) ⟨1200222, by rfl⟩ : syracuseStep 3200593 = 2400445) B2400445
theorem B7198307 : Blo 1262449 7198307 := bstep (se 1 (by rfl) ⟨5398730, by rfl⟩ : syracuseStep 7198307 = 10797461) B10797461
theorem B10393201 : Blo 1262449 10393201 := bstep (se 2 (by rfl) ⟨3897450, by rfl⟩ : syracuseStep 10393201 = 7794901) B7794901
theorem B2078387 : Blo 1262449 2078387 := bstep (se 1 (by rfl) ⟨1558790, by rfl⟩ : syracuseStep 2078387 = 3117581) B3117581
theorem B6395597 : Blo 1262449 6395597 := bstep (se 3 (by rfl) ⟨1199174, by rfl⟩ : syracuseStep 6395597 = 2398349) B2398349
theorem B4265837 : Blo 1262449 4265837 := bstep (se 3 (by rfl) ⟨799844, by rfl⟩ : syracuseStep 4265837 = 1599689) B1599689
theorem B4265891 : Blo 1262449 4265891 := bstep (se 1 (by rfl) ⟨3199418, by rfl⟩ : syracuseStep 4265891 = 6398837) B6398837
theorem B4798385 : Blo 1262449 4798385 := bstep (se 2 (by rfl) ⟨1799394, by rfl⟩ : syracuseStep 4798385 = 3598789) B3598789
theorem B2840561 : Blo 1262449 2840561 := bstep (se 2 (by rfl) ⟨1065210, by rfl⟩ : syracuseStep 2840561 = 2130421) B2130421
theorem B2840579 : Blo 1262449 2840579 := bstep (se 1 (by rfl) ⟨2130434, by rfl⟩ : syracuseStep 2840579 = 4260869) B4260869
theorem B2398243 : Blo 1262449 2398243 := bstep (se 1 (by rfl) ⟨1798682, by rfl⟩ : syracuseStep 2398243 = 3597365) B3597365
theorem B4323437 : Blo 1262449 4323437 := bstep (se 3 (by rfl) ⟨810644, by rfl⟩ : syracuseStep 4323437 = 1621289) B1621289
theorem B6830243 : Blo 1262449 6830243 := bstep (se 1 (by rfl) ⟨5122682, by rfl⟩ : syracuseStep 6830243 = 10245365) B10245365
theorem B4266161 : Blo 1262449 4266161 := bstep (se 2 (by rfl) ⟨1599810, by rfl⟩ : syracuseStep 4266161 = 3199621) B3199621
theorem B2398403 : Blo 1262449 2398403 := bstep (se 1 (by rfl) ⟨1798802, by rfl⟩ : syracuseStep 2398403 = 3597605) B3597605
theorem B1349875 : Blo 1262449 1349875 := bstep (se 1 (by rfl) ⟨1012406, by rfl⟩ : syracuseStep 1349875 = 2024813) B2024813
theorem B2840849 : Blo 1262449 2840849 := bstep (se 2 (by rfl) ⟨1065318, by rfl⟩ : syracuseStep 2840849 = 2130637) B2130637
theorem B2840867 : Blo 1262449 2840867 := bstep (se 1 (by rfl) ⟨2130650, by rfl⟩ : syracuseStep 2840867 = 4261301) B4261301
theorem B6068515 : Blo 1262449 6068515 := bstep (se 1 (by rfl) ⟨4551386, by rfl⟩ : syracuseStep 6068515 = 9102773) B9102773
theorem B2275651 : Blo 1262449 2275651 := bstep (se 1 (by rfl) ⟨1706738, by rfl⟩ : syracuseStep 2275651 = 3413477) B3413477
theorem B3037603 : Blo 1262449 3037603 := bstep (se 1 (by rfl) ⟨2278202, by rfl⟩ : syracuseStep 3037603 = 4556405) B4556405
theorem B15366581 : Blo 1262449 15366581 := bstep (se 5 (by rfl) ⟨720308, by rfl⟩ : syracuseStep 15366581 = 1440617) B1440617
theorem B8886797 : Blo 1262449 8886797 := bstep (se 3 (by rfl) ⟨1666274, by rfl⟩ : syracuseStep 8886797 = 3332549) B3332549
theorem B2841137 : Blo 1262449 2841137 := bstep (se 2 (by rfl) ⟨1065426, by rfl⟩ : syracuseStep 2841137 = 2130853) B2130853
theorem B2161201 : Blo 1262449 2161201 := bstep (se 2 (by rfl) ⟨810450, by rfl⟩ : syracuseStep 2161201 = 1620901) B1620901
theorem B2841155 : Blo 1262449 2841155 := bstep (se 1 (by rfl) ⟨2130866, by rfl⟩ : syracuseStep 2841155 = 4261733) B4261733
theorem B9230917 : Blo 1262449 9230917 := bstep (se 4 (by rfl) ⟨865398, by rfl⟩ : syracuseStep 9230917 = 1730797) B1730797
theorem B4266701 : Blo 1262449 4266701 := bstep (se 3 (by rfl) ⟨800006, by rfl⟩ : syracuseStep 4266701 = 1600013) B1600013
theorem B8100557 : Blo 1262449 8100557 := bstep (se 3 (by rfl) ⟨1518854, by rfl⟩ : syracuseStep 8100557 = 3037709) B3037709
theorem B14588657 : Blo 1262449 14588657 := bstep (se 2 (by rfl) ⟨5470746, by rfl⟩ : syracuseStep 14588657 = 10941493) B10941493
theorem B4266755 : Blo 1262449 4266755 := bstep (se 1 (by rfl) ⟨3200066, by rfl⟩ : syracuseStep 4266755 = 6400133) B6400133
theorem B2276113 : Blo 1262449 2276113 := bstep (se 2 (by rfl) ⟨853542, by rfl⟩ : syracuseStep 2276113 = 1707085) B1707085
theorem B2841425 : Blo 1262449 2841425 := bstep (se 2 (by rfl) ⟨1065534, by rfl⟩ : syracuseStep 2841425 = 2131069) B2131069
theorem B2841443 : Blo 1262449 2841443 := bstep (se 1 (by rfl) ⟨2131082, by rfl⟩ : syracuseStep 2841443 = 4262165) B4262165
theorem B12147569 : Blo 1262449 12147569 := bstep (se 2 (by rfl) ⟨4555338, by rfl⟩ : syracuseStep 12147569 = 9110677) B9110677
theorem B2022275 : Blo 1262449 2022275 := bstep (se 1 (by rfl) ⟨1516706, by rfl⟩ : syracuseStep 2022275 = 3033413) B3033413
theorem B8100785 : Blo 1262449 8100785 := bstep (se 2 (by rfl) ⟨3037794, by rfl⟩ : syracuseStep 8100785 = 6075589) B6075589
theorem B62307269 : Blo 1262449 62307269 := bstep (se 4 (by rfl) ⟨5841306, by rfl⟩ : syracuseStep 62307269 = 11682613) B11682613
theorem B2022403 : Blo 1262449 2022403 := bstep (se 1 (by rfl) ⟨1516802, by rfl⟩ : syracuseStep 2022403 = 3033605) B3033605
theorem B4267025 : Blo 1262449 4267025 := bstep (se 2 (by rfl) ⟨1600134, by rfl⟩ : syracuseStep 4267025 = 3200269) B3200269
theorem B2841713 : Blo 1262449 2841713 := bstep (se 2 (by rfl) ⟨1065642, by rfl⟩ : syracuseStep 2841713 = 2131285) B2131285
theorem B2841731 : Blo 1262449 2841731 := bstep (se 1 (by rfl) ⟨2131298, by rfl⟩ : syracuseStep 2841731 = 4262597) B4262597
theorem B18209933 : Blo 1262449 18209933 := bstep (se 3 (by rfl) ⟨3414362, by rfl⟩ : syracuseStep 18209933 = 6828725) B6828725
theorem B2022545 : Blo 1262449 2022545 := bstep (se 2 (by rfl) ⟨758454, by rfl⟩ : syracuseStep 2022545 = 1516909) B1516909
theorem B2399473 : Blo 1262449 2399473 := bstep (se 2 (by rfl) ⟨899802, by rfl⟩ : syracuseStep 2399473 = 1799605) B1799605
theorem B3595565 : Blo 1262449 3595565 := bstep (se 3 (by rfl) ⟨674168, by rfl⟩ : syracuseStep 3595565 = 1348337) B1348337
theorem B4799843 : Blo 1262449 4799843 := bstep (se 1 (by rfl) ⟨3599882, by rfl⟩ : syracuseStep 4799843 = 7199765) B7199765
theorem B4799857 : Blo 1262449 4799857 := bstep (se 2 (by rfl) ⟨1799946, by rfl⟩ : syracuseStep 4799857 = 3599893) B3599893
theorem B7191949 : Blo 1262449 7191949 := bstep (se 3 (by rfl) ⟨1348490, by rfl⟩ : syracuseStep 7191949 = 2696981) B2696981
theorem B2842001 : Blo 1262449 2842001 := bstep (se 2 (by rfl) ⟨1065750, by rfl⟩ : syracuseStep 2842001 = 2131501) B2131501
theorem B2842019 : Blo 1262449 2842019 := bstep (se 1 (by rfl) ⟨2131514, by rfl⟩ : syracuseStep 2842019 = 4263029) B4263029
theorem B2022833 : Blo 1262449 2022833 := bstep (se 2 (by rfl) ⟨758562, by rfl⟩ : syracuseStep 2022833 = 1517125) B1517125
theorem B7200197 : Blo 1262449 7200197 := bstep (se 4 (by rfl) ⟨675018, by rfl⟩ : syracuseStep 7200197 = 1350037) B1350037
theorem B3595747 : Blo 1262449 3595747 := bstep (se 1 (by rfl) ⟨2696810, by rfl⟩ : syracuseStep 3595747 = 5393621) B5393621
theorem B6069745 : Blo 1262449 6069745 := bstep (se 2 (by rfl) ⟨2276154, by rfl⟩ : syracuseStep 6069745 = 4552309) B4552309
theorem B472858165 : Blo 1262449 472858165 := bstep (se 5 (by rfl) ⟨22165226, by rfl⟩ : syracuseStep 472858165 = 44330453) B44330453
theorem B66534965 : Blo 1262449 66534965 := bstep (se 5 (by rfl) ⟨3118826, by rfl⟩ : syracuseStep 66534965 = 6237653) B6237653
theorem B9109061 : Blo 1262449 9109061 := bstep (se 4 (by rfl) ⟨853974, by rfl⟩ : syracuseStep 9109061 = 1707949) B1707949
theorem B49897073 : Blo 1262449 49897073 := bstep (se 2 (by rfl) ⟨18711402, by rfl⟩ : syracuseStep 49897073 = 37422805) B37422805
theorem B3595907 : Blo 1262449 3595907 := bstep (se 1 (by rfl) ⟨2696930, by rfl⟩ : syracuseStep 3595907 = 5393861) B5393861
theorem B2842289 : Blo 1262449 2842289 := bstep (se 2 (by rfl) ⟨1065858, by rfl⟩ : syracuseStep 2842289 = 2131717) B2131717
theorem B2842307 : Blo 1262449 2842307 := bstep (se 1 (by rfl) ⟨2131730, by rfl⟩ : syracuseStep 2842307 = 4263461) B4263461
theorem B5119793 : Blo 1262449 5119793 := bstep (se 2 (by rfl) ⟨1919922, by rfl⟩ : syracuseStep 5119793 = 3839845) B3839845
theorem B2842577 : Blo 1262449 2842577 := bstep (se 2 (by rfl) ⟨1065966, by rfl⟩ : syracuseStep 2842577 = 2131933) B2131933
theorem B2842595 : Blo 1262449 2842595 := bstep (se 1 (by rfl) ⟨2131946, by rfl⟩ : syracuseStep 2842595 = 4263893) B4263893
theorem B2842649 : Blo 1262449 2842649 := bstep (se 2 (by rfl) ⟨1065993, by rfl⟩ : syracuseStep 2842649 = 2131987) B2131987
theorem B12468259 : Blo 1262449 12468259 := bstep (se 1 (by rfl) ⟨9351194, by rfl⟩ : syracuseStep 12468259 = 18702389) B18702389
theorem B3596339 : Blo 1262449 3596339 := bstep (se 1 (by rfl) ⟨2697254, by rfl⟩ : syracuseStep 3596339 = 5394509) B5394509
theorem B3596363 : Blo 1262449 3596363 := bstep (se 1 (by rfl) ⟨2697272, by rfl⟩ : syracuseStep 3596363 = 5394545) B5394545
theorem B2023499 : Blo 1262449 2023499 := bstep (se 1 (by rfl) ⟨1517624, by rfl⟩ : syracuseStep 2023499 = 3035249) B3035249
theorem B6398027 : Blo 1262449 6398027 := bstep (se 1 (by rfl) ⟨4798520, by rfl⟩ : syracuseStep 6398027 = 9597041) B9597041
theorem B2842739 : Blo 1262449 2842739 := bstep (se 1 (by rfl) ⟨2132054, by rfl⟩ : syracuseStep 2842739 = 4264109) B4264109
theorem B2842775 : Blo 1262449 2842775 := bstep (se 1 (by rfl) ⟨2132081, by rfl⟩ : syracuseStep 2842775 = 4264163) B4264163
theorem B9593153 : Blo 1262449 9593153 := bstep (se 2 (by rfl) ⟨3597432, by rfl⟩ : syracuseStep 9593153 = 7194865) B7194865
theorem B7192907 : Blo 1262449 7192907 := bstep (se 1 (by rfl) ⟨5394680, by rfl⟩ : syracuseStep 7192907 = 10789361) B10789361
theorem B2842955 : Blo 1262449 2842955 := bstep (se 1 (by rfl) ⟨2132216, by rfl⟩ : syracuseStep 2842955 = 4264433) B4264433
theorem B2843009 : Blo 1262449 2843009 := bstep (se 2 (by rfl) ⟨1066128, by rfl⟩ : syracuseStep 2843009 = 2132257) B2132257
theorem B1597963 : Blo 1262449 1597963 := bstep (se 1 (by rfl) ⟨1198472, by rfl⟩ : syracuseStep 1597963 = 2396945) B2396945
theorem B2130455 : Blo 1262449 2130455 := bstep (se 1 (by rfl) ⟨1597841, by rfl⟩ : syracuseStep 2130455 = 3195683) B3195683
theorem B19464779 : Blo 1262449 19464779 := bstep (se 1 (by rfl) ⟨14598584, by rfl⟩ : syracuseStep 19464779 = 29197169) B29197169
theorem B14402123 : Blo 1262449 14402123 := bstep (se 1 (by rfl) ⟨10801592, by rfl⟩ : syracuseStep 14402123 = 21603185) B21603185
theorem B2843225 : Blo 1262449 2843225 := bstep (se 2 (by rfl) ⟨1066209, by rfl⟩ : syracuseStep 2843225 = 2132419) B2132419
theorem B2130583 : Blo 1262449 2130583 := bstep (se 1 (by rfl) ⟨1597937, by rfl⟩ : syracuseStep 2130583 = 3195875) B3195875
theorem B2843315 : Blo 1262449 2843315 := bstep (se 1 (by rfl) ⟨2132486, by rfl⟩ : syracuseStep 2843315 = 4264973) B4264973
theorem B2843351 : Blo 1262449 2843351 := bstep (se 1 (by rfl) ⟨2132513, by rfl⟩ : syracuseStep 2843351 = 4265027) B4265027
theorem B1598231 : Blo 1262449 1598231 := bstep (se 1 (by rfl) ⟨1198673, by rfl⟩ : syracuseStep 1598231 = 2397347) B2397347
theorem B3195713 : Blo 1262449 3195713 := bstep (se 2 (by rfl) ⟨1198392, by rfl⟩ : syracuseStep 3195713 = 2396785) B2396785
theorem B5473099 : Blo 1262449 5473099 := bstep (se 1 (by rfl) ⟨4104824, by rfl⟩ : syracuseStep 5473099 = 8209649) B8209649
theorem B3597149 : Blo 1262449 3597149 := bstep (se 3 (by rfl) ⟨674465, by rfl⟩ : syracuseStep 3597149 = 1348931) B1348931
theorem B1262455 : Blo 1262449 1262455 := bstep (se 1 (by rfl) ⟨946841, by rfl⟩ : syracuseStep 1262455 = 1893683) B1893683
theorem B1262475 : Blo 1262449 1262475 := bstep (se 1 (by rfl) ⟨946856, by rfl⟩ : syracuseStep 1262475 = 1893713) B1893713
theorem B2843531 : Blo 1262449 2843531 := bstep (se 1 (by rfl) ⟨2132648, by rfl⟩ : syracuseStep 2843531 = 4265297) B4265297
theorem B1262487 : Blo 1262449 1262487 := bstep (se 1 (by rfl) ⟨946865, by rfl⟩ : syracuseStep 1262487 = 1893731) B1893731
theorem B1262507 : Blo 1262449 1262507 := bstep (se 1 (by rfl) ⟨946880, by rfl⟩ : syracuseStep 1262507 = 1893761) B1893761
theorem B1262519 : Blo 1262449 1262519 := bstep (se 1 (by rfl) ⟨946889, by rfl⟩ : syracuseStep 1262519 = 1893779) B1893779
theorem B2843585 : Blo 1262449 2843585 := bstep (se 2 (by rfl) ⟨1066344, by rfl⟩ : syracuseStep 2843585 = 2132689) B2132689
theorem B1262539 : Blo 1262449 1262539 := bstep (se 1 (by rfl) ⟨946904, by rfl⟩ : syracuseStep 1262539 = 1893809) B1893809
theorem B1262551 : Blo 1262449 1262551 := bstep (se 1 (by rfl) ⟨946913, by rfl⟩ : syracuseStep 1262551 = 1893827) B1893827
theorem B5473241 : Blo 1262449 5473241 := bstep (se 2 (by rfl) ⟨2052465, by rfl⟩ : syracuseStep 5473241 = 4104931) B4104931
theorem B1262571 : Blo 1262449 1262571 := bstep (se 1 (by rfl) ⟨946928, by rfl⟩ : syracuseStep 1262571 = 1893857) B1893857
theorem B1262583 : Blo 1262449 1262583 := bstep (se 1 (by rfl) ⟨946937, by rfl⟩ : syracuseStep 1262583 = 1893875) B1893875
theorem B1262603 : Blo 1262449 1262603 := bstep (se 1 (by rfl) ⟨946952, by rfl⟩ : syracuseStep 1262603 = 1893905) B1893905
theorem B1262615 : Blo 1262449 1262615 := bstep (se 1 (by rfl) ⟨946961, by rfl⟩ : syracuseStep 1262615 = 1893923) B1893923
theorem B1262635 : Blo 1262449 1262635 := bstep (se 1 (by rfl) ⟨946976, by rfl⟩ : syracuseStep 1262635 = 1893953) B1893953
theorem B6825005 : Blo 1262449 6825005 := bstep (se 3 (by rfl) ⟨1279688, by rfl⟩ : syracuseStep 6825005 = 2559377) B2559377
theorem B1262647 : Blo 1262449 1262647 := bstep (se 1 (by rfl) ⟨946985, by rfl⟩ : syracuseStep 1262647 = 1893971) B1893971
theorem B1262667 : Blo 1262449 1262667 := bstep (se 1 (by rfl) ⟨947000, by rfl⟩ : syracuseStep 1262667 = 1894001) B1894001
theorem B1262679 : Blo 1262449 1262679 := bstep (se 1 (by rfl) ⟨947009, by rfl⟩ : syracuseStep 1262679 = 1894019) B1894019
theorem B5473373 : Blo 1262449 5473373 := bstep (se 3 (by rfl) ⟨1026257, by rfl⟩ : syracuseStep 5473373 = 2052515) B2052515
theorem B1262699 : Blo 1262449 1262699 := bstep (se 1 (by rfl) ⟨947024, by rfl⟩ : syracuseStep 1262699 = 1894049) B1894049
theorem B1262711 : Blo 1262449 1262711 := bstep (se 1 (by rfl) ⟨947033, by rfl⟩ : syracuseStep 1262711 = 1894067) B1894067
theorem B1385591 : Blo 1262449 1385591 := bstep (se 1 (by rfl) ⟨1039193, by rfl⟩ : syracuseStep 1385591 = 2078387) B2078387
theorem B1262731 : Blo 1262449 1262731 := bstep (se 1 (by rfl) ⟨947048, by rfl⟩ : syracuseStep 1262731 = 1894097) B1894097
theorem B1262743 : Blo 1262449 1262743 := bstep (se 1 (by rfl) ⟨947057, by rfl⟩ : syracuseStep 1262743 = 1894115) B1894115
theorem B2843801 : Blo 1262449 2843801 := bstep (se 2 (by rfl) ⟨1066425, by rfl⟩ : syracuseStep 2843801 = 2132851) B2132851
theorem B1262763 : Blo 1262449 1262763 := bstep (se 1 (by rfl) ⟨947072, by rfl⟩ : syracuseStep 1262763 = 1894145) B1894145
theorem B1262775 : Blo 1262449 1262775 := bstep (se 1 (by rfl) ⟨947081, by rfl⟩ : syracuseStep 1262775 = 1894163) B1894163
theorem B1262795 : Blo 1262449 1262795 := bstep (se 1 (by rfl) ⟨947096, by rfl⟩ : syracuseStep 1262795 = 1894193) B1894193
theorem B1262807 : Blo 1262449 1262807 := bstep (se 1 (by rfl) ⟨947105, by rfl⟩ : syracuseStep 1262807 = 1894211) B1894211
theorem B4261085 : Blo 1262449 4261085 := bstep (se 3 (by rfl) ⟨798953, by rfl⟩ : syracuseStep 4261085 = 1597907) B1597907
theorem B1262827 : Blo 1262449 1262827 := bstep (se 1 (by rfl) ⟨947120, by rfl⟩ : syracuseStep 1262827 = 1894241) B1894241
theorem B2843891 : Blo 1262449 2843891 := bstep (se 1 (by rfl) ⟨2132918, by rfl⟩ : syracuseStep 2843891 = 4265837) B4265837
theorem B1262839 : Blo 1262449 1262839 := bstep (se 1 (by rfl) ⟨947129, by rfl⟩ : syracuseStep 1262839 = 1894259) B1894259
theorem B1262859 : Blo 1262449 1262859 := bstep (se 1 (by rfl) ⟨947144, by rfl⟩ : syracuseStep 1262859 = 1894289) B1894289
theorem B2131211 : Blo 1262449 2131211 := bstep (se 1 (by rfl) ⟨1598408, by rfl⟩ : syracuseStep 2131211 = 3196817) B3196817
theorem B1262871 : Blo 1262449 1262871 := bstep (se 1 (by rfl) ⟨947153, by rfl⟩ : syracuseStep 1262871 = 1894307) B1894307
theorem B2843927 : Blo 1262449 2843927 := bstep (se 1 (by rfl) ⟨2132945, by rfl⟩ : syracuseStep 2843927 = 4265891) B4265891
theorem B1262891 : Blo 1262449 1262891 := bstep (se 1 (by rfl) ⟨947168, by rfl⟩ : syracuseStep 1262891 = 1894337) B1894337
theorem B1262903 : Blo 1262449 1262903 := bstep (se 1 (by rfl) ⟨947177, by rfl⟩ : syracuseStep 1262903 = 1894355) B1894355
theorem B1893707 : Blo 1262449 1893707 := bstep (se 1 (by rfl) ⟨1420280, by rfl⟩ : syracuseStep 1893707 = 2840561) B2840561
theorem B1262923 : Blo 1262449 1262923 := bstep (se 1 (by rfl) ⟨947192, by rfl⟩ : syracuseStep 1262923 = 1894385) B1894385
theorem B6833483 : Blo 1262449 6833483 := bstep (se 1 (by rfl) ⟨5125112, by rfl⟩ : syracuseStep 6833483 = 10250225) B10250225
theorem B1893719 : Blo 1262449 1893719 := bstep (se 1 (by rfl) ⟨1420289, by rfl⟩ : syracuseStep 1893719 = 2840579) B2840579
theorem B1262935 : Blo 1262449 1262935 := bstep (se 1 (by rfl) ⟨947201, by rfl⟩ : syracuseStep 1262935 = 1894403) B1894403
theorem B2696537 : Blo 1262449 2696537 := bstep (se 2 (by rfl) ⟨1011201, by rfl⟩ : syracuseStep 2696537 = 2022403) B2022403
theorem B1262955 : Blo 1262449 1262955 := bstep (se 1 (by rfl) ⟨947216, by rfl⟩ : syracuseStep 1262955 = 1894433) B1894433
theorem B1262967 : Blo 1262449 1262967 := bstep (se 1 (by rfl) ⟨947225, by rfl⟩ : syracuseStep 1262967 = 1894451) B1894451
theorem B1262987 : Blo 1262449 1262987 := bstep (se 1 (by rfl) ⟨947240, by rfl⟩ : syracuseStep 1262987 = 1894481) B1894481
theorem B2131339 : Blo 1262449 2131339 := bstep (se 1 (by rfl) ⟨1598504, by rfl⟩ : syracuseStep 2131339 = 3197009) B3197009
theorem B1262999 : Blo 1262449 1262999 := bstep (se 1 (by rfl) ⟨947249, by rfl⟩ : syracuseStep 1262999 = 1894499) B1894499
theorem B1893785 : Blo 1262449 1893785 := bstep (se 2 (by rfl) ⟨710169, by rfl⟩ : syracuseStep 1893785 = 1420339) B1420339
theorem B1263019 : Blo 1262449 1263019 := bstep (se 1 (by rfl) ⟨947264, by rfl⟩ : syracuseStep 1263019 = 1894529) B1894529
theorem B1263031 : Blo 1262449 1263031 := bstep (se 1 (by rfl) ⟨947273, by rfl⟩ : syracuseStep 1263031 = 1894547) B1894547
theorem B1263051 : Blo 1262449 1263051 := bstep (se 1 (by rfl) ⟨947288, by rfl⟩ : syracuseStep 1263051 = 1894577) B1894577
theorem B2844107 : Blo 1262449 2844107 := bstep (se 1 (by rfl) ⟨2133080, by rfl⟩ : syracuseStep 2844107 = 4266161) B4266161
theorem B1263063 : Blo 1262449 1263063 := bstep (se 1 (by rfl) ⟨947297, by rfl⟩ : syracuseStep 1263063 = 1894595) B1894595
theorem B1598935 : Blo 1262449 1598935 := bstep (se 1 (by rfl) ⟨1199201, by rfl⟩ : syracuseStep 1598935 = 2398403) B2398403
theorem B1263083 : Blo 1262449 1263083 := bstep (se 1 (by rfl) ⟨947312, by rfl⟩ : syracuseStep 1263083 = 1894625) B1894625
theorem B1263095 : Blo 1262449 1263095 := bstep (se 1 (by rfl) ⟨947321, by rfl⟩ : syracuseStep 1263095 = 1894643) B1894643
theorem B2844161 : Blo 1262449 2844161 := bstep (se 2 (by rfl) ⟨1066560, by rfl⟩ : syracuseStep 2844161 = 2133121) B2133121
theorem B1893899 : Blo 1262449 1893899 := bstep (se 1 (by rfl) ⟨1420424, by rfl⟩ : syracuseStep 1893899 = 2840849) B2840849
theorem B1263115 : Blo 1262449 1263115 := bstep (se 1 (by rfl) ⟨947336, by rfl⟩ : syracuseStep 1263115 = 1894673) B1894673
theorem B1893911 : Blo 1262449 1893911 := bstep (se 1 (by rfl) ⟨1420433, by rfl⟩ : syracuseStep 1893911 = 2840867) B2840867
theorem B1263127 : Blo 1262449 1263127 := bstep (se 1 (by rfl) ⟨947345, by rfl⟩ : syracuseStep 1263127 = 1894691) B1894691
theorem B2131481 : Blo 1262449 2131481 := bstep (se 2 (by rfl) ⟨799305, by rfl⟩ : syracuseStep 2131481 = 1598611) B1598611
theorem B1263147 : Blo 1262449 1263147 := bstep (se 1 (by rfl) ⟨947360, by rfl⟩ : syracuseStep 1263147 = 1894721) B1894721
theorem B1263159 : Blo 1262449 1263159 := bstep (se 1 (by rfl) ⟨947369, by rfl⟩ : syracuseStep 1263159 = 1894739) B1894739
theorem B1263179 : Blo 1262449 1263179 := bstep (se 1 (by rfl) ⟨947384, by rfl⟩ : syracuseStep 1263179 = 1894769) B1894769
theorem B1263191 : Blo 1262449 1263191 := bstep (se 1 (by rfl) ⟨947393, by rfl⟩ : syracuseStep 1263191 = 1894787) B1894787
theorem B1893977 : Blo 1262449 1893977 := bstep (se 2 (by rfl) ⟨710241, by rfl⟩ : syracuseStep 1893977 = 1420483) B1420483
theorem B1263211 : Blo 1262449 1263211 := bstep (se 1 (by rfl) ⟨947408, by rfl⟩ : syracuseStep 1263211 = 1894817) B1894817
theorem B1263223 : Blo 1262449 1263223 := bstep (se 1 (by rfl) ⟨947417, by rfl⟩ : syracuseStep 1263223 = 1894835) B1894835
theorem B1263243 : Blo 1262449 1263243 := bstep (se 1 (by rfl) ⟨947432, by rfl⟩ : syracuseStep 1263243 = 1894865) B1894865
theorem B1263255 : Blo 1262449 1263255 := bstep (se 1 (by rfl) ⟨947441, by rfl⟩ : syracuseStep 1263255 = 1894883) B1894883
theorem B2131609 : Blo 1262449 2131609 := bstep (se 2 (by rfl) ⟨799353, by rfl⟩ : syracuseStep 2131609 = 1598707) B1598707
theorem B1263275 : Blo 1262449 1263275 := bstep (se 1 (by rfl) ⟨947456, by rfl⟩ : syracuseStep 1263275 = 1894913) B1894913
theorem B4556461 : Blo 1262449 4556461 := bstep (se 3 (by rfl) ⟨854336, by rfl⟩ : syracuseStep 4556461 = 1708673) B1708673
theorem B5924531 : Blo 1262449 5924531 := bstep (se 1 (by rfl) ⟨4443398, by rfl⟩ : syracuseStep 5924531 = 8886797) B8886797
theorem B1263287 : Blo 1262449 1263287 := bstep (se 1 (by rfl) ⟨947465, by rfl⟩ : syracuseStep 1263287 = 1894931) B1894931
theorem B1894091 : Blo 1262449 1894091 := bstep (se 1 (by rfl) ⟨1420568, by rfl⟩ : syracuseStep 1894091 = 2841137) B2841137
theorem B1263307 : Blo 1262449 1263307 := bstep (se 1 (by rfl) ⟨947480, by rfl⟩ : syracuseStep 1263307 = 1894961) B1894961
theorem B1894103 : Blo 1262449 1894103 := bstep (se 1 (by rfl) ⟨1420577, by rfl⟩ : syracuseStep 1894103 = 2841155) B2841155
theorem B1263319 : Blo 1262449 1263319 := bstep (se 1 (by rfl) ⟨947489, by rfl⟩ : syracuseStep 1263319 = 1894979) B1894979
theorem B2844377 : Blo 1262449 2844377 := bstep (se 2 (by rfl) ⟨1066641, by rfl⟩ : syracuseStep 2844377 = 2133283) B2133283
theorem B1263339 : Blo 1262449 1263339 := bstep (se 1 (by rfl) ⟨947504, by rfl⟩ : syracuseStep 1263339 = 1895009) B1895009
theorem B1263351 : Blo 1262449 1263351 := bstep (se 1 (by rfl) ⟨947513, by rfl⟩ : syracuseStep 1263351 = 1895027) B1895027
theorem B1263371 : Blo 1262449 1263371 := bstep (se 1 (by rfl) ⟨947528, by rfl⟩ : syracuseStep 1263371 = 1895057) B1895057
theorem B1263383 : Blo 1262449 1263383 := bstep (se 1 (by rfl) ⟨947537, by rfl⟩ : syracuseStep 1263383 = 1895075) B1895075
theorem B1894169 : Blo 1262449 1894169 := bstep (se 2 (by rfl) ⟨710313, by rfl⟩ : syracuseStep 1894169 = 1420627) B1420627
theorem B1263403 : Blo 1262449 1263403 := bstep (se 1 (by rfl) ⟨947552, by rfl⟩ : syracuseStep 1263403 = 1895105) B1895105
theorem B2844467 : Blo 1262449 2844467 := bstep (se 1 (by rfl) ⟨2133350, by rfl⟩ : syracuseStep 2844467 = 4266701) B4266701
theorem B5400371 : Blo 1262449 5400371 := bstep (se 1 (by rfl) ⟨4050278, by rfl⟩ : syracuseStep 5400371 = 8100557) B8100557
theorem B1263415 : Blo 1262449 1263415 := bstep (se 1 (by rfl) ⟨947561, by rfl⟩ : syracuseStep 1263415 = 1895123) B1895123
theorem B6399809 : Blo 1262449 6399809 := bstep (se 2 (by rfl) ⟨2399928, by rfl⟩ : syracuseStep 6399809 = 4799857) B4799857
theorem B1263435 : Blo 1262449 1263435 := bstep (se 1 (by rfl) ⟨947576, by rfl⟩ : syracuseStep 1263435 = 1895153) B1895153
theorem B9725771 : Blo 1262449 9725771 := bstep (se 1 (by rfl) ⟨7294328, by rfl⟩ : syracuseStep 9725771 = 14588657) B14588657
theorem B1263447 : Blo 1262449 1263447 := bstep (se 1 (by rfl) ⟨947585, by rfl⟩ : syracuseStep 1263447 = 1895171) B1895171
theorem B2844503 : Blo 1262449 2844503 := bstep (se 1 (by rfl) ⟨2133377, by rfl⟩ : syracuseStep 2844503 = 4266755) B4266755
theorem B1263467 : Blo 1262449 1263467 := bstep (se 1 (by rfl) ⟨947600, by rfl⟩ : syracuseStep 1263467 = 1895201) B1895201
theorem B1263479 : Blo 1262449 1263479 := bstep (se 1 (by rfl) ⟨947609, by rfl⟩ : syracuseStep 1263479 = 1895219) B1895219
theorem B1894283 : Blo 1262449 1894283 := bstep (se 1 (by rfl) ⟨1420712, by rfl⟩ : syracuseStep 1894283 = 2841425) B2841425
theorem B1263499 : Blo 1262449 1263499 := bstep (se 1 (by rfl) ⟨947624, by rfl⟩ : syracuseStep 1263499 = 1895249) B1895249
theorem B1894295 : Blo 1262449 1894295 := bstep (se 1 (by rfl) ⟨1420721, by rfl⟩ : syracuseStep 1894295 = 2841443) B2841443
theorem B1263511 : Blo 1262449 1263511 := bstep (se 1 (by rfl) ⟨947633, by rfl⟩ : syracuseStep 1263511 = 1895267) B1895267
theorem B2189209 : Blo 1262449 2189209 := bstep (se 2 (by rfl) ⟨820953, by rfl⟩ : syracuseStep 2189209 = 1641907) B1641907
theorem B1263531 : Blo 1262449 1263531 := bstep (se 1 (by rfl) ⟨947648, by rfl⟩ : syracuseStep 1263531 = 1895297) B1895297
theorem B1263543 : Blo 1262449 1263543 := bstep (se 1 (by rfl) ⟨947657, by rfl⟩ : syracuseStep 1263543 = 1895315) B1895315
theorem B1263563 : Blo 1262449 1263563 := bstep (se 1 (by rfl) ⟨947672, by rfl⟩ : syracuseStep 1263563 = 1895345) B1895345
theorem B5400523 : Blo 1262449 5400523 := bstep (se 1 (by rfl) ⟨4050392, by rfl⟩ : syracuseStep 5400523 = 8100785) B8100785
theorem B1263575 : Blo 1262449 1263575 := bstep (se 1 (by rfl) ⟨947681, by rfl⟩ : syracuseStep 1263575 = 1895363) B1895363
theorem B4794329 : Blo 1262449 4794329 := bstep (se 2 (by rfl) ⟨1797873, by rfl⟩ : syracuseStep 4794329 = 3595747) B3595747
theorem B1894361 : Blo 1262449 1894361 := bstep (se 2 (by rfl) ⟨710385, by rfl⟩ : syracuseStep 1894361 = 1420771) B1420771
theorem B1263595 : Blo 1262449 1263595 := bstep (se 1 (by rfl) ⟨947696, by rfl⟩ : syracuseStep 1263595 = 1895393) B1895393
theorem B1263607 : Blo 1262449 1263607 := bstep (se 1 (by rfl) ⟨947705, by rfl⟩ : syracuseStep 1263607 = 1895411) B1895411
theorem B1263627 : Blo 1262449 1263627 := bstep (se 1 (by rfl) ⟨947720, by rfl⟩ : syracuseStep 1263627 = 1895441) B1895441
theorem B2844683 : Blo 1262449 2844683 := bstep (se 1 (by rfl) ⟨2133512, by rfl⟩ : syracuseStep 2844683 = 4267025) B4267025
theorem B7686161 : Blo 1262449 7686161 := bstep (se 2 (by rfl) ⟨2882310, by rfl⟩ : syracuseStep 7686161 = 5764621) B5764621
theorem B5400593 : Blo 1262449 5400593 := bstep (se 2 (by rfl) ⟨2025222, by rfl⟩ : syracuseStep 5400593 = 4050445) B4050445
theorem B1263639 : Blo 1262449 1263639 := bstep (se 1 (by rfl) ⟨947729, by rfl⟩ : syracuseStep 1263639 = 1895459) B1895459
theorem B1263659 : Blo 1262449 1263659 := bstep (se 1 (by rfl) ⟨947744, by rfl⟩ : syracuseStep 1263659 = 1895489) B1895489
theorem B3196979 : Blo 1262449 3196979 := bstep (se 1 (by rfl) ⟨2397734, by rfl⟩ : syracuseStep 3196979 = 4795469) B4795469
theorem B1263671 : Blo 1262449 1263671 := bstep (se 1 (by rfl) ⟨947753, by rfl⟩ : syracuseStep 1263671 = 1895507) B1895507
theorem B2844737 : Blo 1262449 2844737 := bstep (se 2 (by rfl) ⟨1066776, by rfl⟩ : syracuseStep 2844737 = 2133553) B2133553
theorem B1894475 : Blo 1262449 1894475 := bstep (se 1 (by rfl) ⟨1420856, by rfl⟩ : syracuseStep 1894475 = 2841713) B2841713
theorem B1263691 : Blo 1262449 1263691 := bstep (se 1 (by rfl) ⟨947768, by rfl⟩ : syracuseStep 1263691 = 1895537) B1895537
theorem B1894487 : Blo 1262449 1894487 := bstep (se 1 (by rfl) ⟨1420865, by rfl⟩ : syracuseStep 1894487 = 2841731) B2841731
theorem B1263703 : Blo 1262449 1263703 := bstep (se 1 (by rfl) ⟨947777, by rfl⟩ : syracuseStep 1263703 = 1895555) B1895555
theorem B1263723 : Blo 1262449 1263723 := bstep (se 1 (by rfl) ⟨947792, by rfl⟩ : syracuseStep 1263723 = 1895585) B1895585
theorem B1263735 : Blo 1262449 1263735 := bstep (se 1 (by rfl) ⟨947801, by rfl⟩ : syracuseStep 1263735 = 1895603) B1895603
theorem B1263755 : Blo 1262449 1263755 := bstep (se 1 (by rfl) ⟨947816, by rfl⟩ : syracuseStep 1263755 = 1895633) B1895633
theorem B1263767 : Blo 1262449 1263767 := bstep (se 1 (by rfl) ⟨947825, by rfl⟩ : syracuseStep 1263767 = 1895651) B1895651
theorem B1894553 : Blo 1262449 1894553 := bstep (se 2 (by rfl) ⟨710457, by rfl⟩ : syracuseStep 1894553 = 1420915) B1420915
theorem B1263787 : Blo 1262449 1263787 := bstep (se 1 (by rfl) ⟨947840, by rfl⟩ : syracuseStep 1263787 = 1895681) B1895681
theorem B1263799 : Blo 1262449 1263799 := bstep (se 1 (by rfl) ⟨947849, by rfl⟩ : syracuseStep 1263799 = 1895699) B1895699
theorem B1263819 : Blo 1262449 1263819 := bstep (se 1 (by rfl) ⟨947864, by rfl⟩ : syracuseStep 1263819 = 1895729) B1895729
theorem B2132183 : Blo 1262449 2132183 := bstep (se 1 (by rfl) ⟨1599137, by rfl⟩ : syracuseStep 2132183 = 3198275) B3198275
theorem B1263831 : Blo 1262449 1263831 := bstep (se 1 (by rfl) ⟨947873, by rfl⟩ : syracuseStep 1263831 = 1895747) B1895747
theorem B9595097 : Blo 1262449 9595097 := bstep (se 2 (by rfl) ⟨3598161, by rfl⟩ : syracuseStep 9595097 = 7196323) B7196323
theorem B1263851 : Blo 1262449 1263851 := bstep (se 1 (by rfl) ⟨947888, by rfl⟩ : syracuseStep 1263851 = 1895777) B1895777
theorem B1263863 : Blo 1262449 1263863 := bstep (se 1 (by rfl) ⟨947897, by rfl⟩ : syracuseStep 1263863 = 1895795) B1895795
theorem B1894667 : Blo 1262449 1894667 := bstep (se 1 (by rfl) ⟨1421000, by rfl⟩ : syracuseStep 1894667 = 2842001) B2842001
theorem B1263883 : Blo 1262449 1263883 := bstep (se 1 (by rfl) ⟨947912, by rfl⟩ : syracuseStep 1263883 = 1895825) B1895825
theorem B1894679 : Blo 1262449 1894679 := bstep (se 1 (by rfl) ⟨1421009, by rfl⟩ : syracuseStep 1894679 = 2842019) B2842019
theorem B1263895 : Blo 1262449 1263895 := bstep (se 1 (by rfl) ⟨947921, by rfl⟩ : syracuseStep 1263895 = 1895843) B1895843
theorem B2844953 : Blo 1262449 2844953 := bstep (se 2 (by rfl) ⟨1066857, by rfl⟩ : syracuseStep 2844953 = 2133715) B2133715
theorem B1263915 : Blo 1262449 1263915 := bstep (se 1 (by rfl) ⟨947936, by rfl⟩ : syracuseStep 1263915 = 1895873) B1895873
theorem B1263927 : Blo 1262449 1263927 := bstep (se 1 (by rfl) ⟨947945, by rfl⟩ : syracuseStep 1263927 = 1895891) B1895891
theorem B4262219 : Blo 1262449 4262219 := bstep (se 1 (by rfl) ⟨3196664, by rfl⟩ : syracuseStep 4262219 = 6393329) B6393329
theorem B1263947 : Blo 1262449 1263947 := bstep (se 1 (by rfl) ⟨947960, by rfl⟩ : syracuseStep 1263947 = 1895921) B1895921
theorem B1894745 : Blo 1262449 1894745 := bstep (se 2 (by rfl) ⟨710529, by rfl⟩ : syracuseStep 1894745 = 1421059) B1421059
theorem B2132311 : Blo 1262449 2132311 := bstep (se 1 (by rfl) ⟨1599233, by rfl⟩ : syracuseStep 2132311 = 3198467) B3198467
theorem B1263959 : Blo 1262449 1263959 := bstep (se 1 (by rfl) ⟨947969, by rfl⟩ : syracuseStep 1263959 = 1895939) B1895939
theorem B1263979 : Blo 1262449 1263979 := bstep (se 1 (by rfl) ⟨947984, by rfl⟩ : syracuseStep 1263979 = 1895969) B1895969
theorem B1263991 : Blo 1262449 1263991 := bstep (se 1 (by rfl) ⟨947993, by rfl⟩ : syracuseStep 1263991 = 1895987) B1895987
theorem B6392195 : Blo 1262449 6392195 := bstep (se 1 (by rfl) ⟨4794146, by rfl⟩ : syracuseStep 6392195 = 9588293) B9588293
theorem B6072707 : Blo 1262449 6072707 := bstep (se 1 (by rfl) ⟨4554530, by rfl⟩ : syracuseStep 6072707 = 9109061) B9109061
theorem B1264011 : Blo 1262449 1264011 := bstep (se 1 (by rfl) ⟨948008, by rfl⟩ : syracuseStep 1264011 = 1896017) B1896017
theorem B1264023 : Blo 1262449 1264023 := bstep (se 1 (by rfl) ⟨948017, by rfl⟩ : syracuseStep 1264023 = 1896035) B1896035
theorem B1264043 : Blo 1262449 1264043 := bstep (se 1 (by rfl) ⟨948032, by rfl⟩ : syracuseStep 1264043 = 1896065) B1896065
theorem B1264055 : Blo 1262449 1264055 := bstep (se 1 (by rfl) ⟨948041, by rfl⟩ : syracuseStep 1264055 = 1896083) B1896083
theorem B1894859 : Blo 1262449 1894859 := bstep (se 1 (by rfl) ⟨1421144, by rfl⟩ : syracuseStep 1894859 = 2842289) B2842289
theorem B1264075 : Blo 1262449 1264075 := bstep (se 1 (by rfl) ⟨948056, by rfl⟩ : syracuseStep 1264075 = 1896113) B1896113
theorem B1894871 : Blo 1262449 1894871 := bstep (se 1 (by rfl) ⟨1421153, by rfl⟩ : syracuseStep 1894871 = 2842307) B2842307
theorem B1264087 : Blo 1262449 1264087 := bstep (se 1 (by rfl) ⟨948065, by rfl⟩ : syracuseStep 1264087 = 1896131) B1896131
theorem B4319705 : Blo 1262449 4319705 := bstep (se 2 (by rfl) ⟨1619889, by rfl⟩ : syracuseStep 4319705 = 3239779) B3239779
theorem B1264107 : Blo 1262449 1264107 := bstep (se 1 (by rfl) ⟨948080, by rfl⟩ : syracuseStep 1264107 = 1896161) B1896161
theorem B1264119 : Blo 1262449 1264119 := bstep (se 1 (by rfl) ⟨948089, by rfl⟩ : syracuseStep 1264119 = 1896179) B1896179
theorem B1264139 : Blo 1262449 1264139 := bstep (se 1 (by rfl) ⟨948104, by rfl⟩ : syracuseStep 1264139 = 1896209) B1896209
theorem B1264151 : Blo 1262449 1264151 := bstep (se 1 (by rfl) ⟨948113, by rfl⟩ : syracuseStep 1264151 = 1896227) B1896227
theorem B1894937 : Blo 1262449 1894937 := bstep (se 2 (by rfl) ⟨710601, by rfl⟩ : syracuseStep 1894937 = 1421203) B1421203
theorem B1264171 : Blo 1262449 1264171 := bstep (se 1 (by rfl) ⟨948128, by rfl⟩ : syracuseStep 1264171 = 1896257) B1896257
theorem B4049459 : Blo 1262449 4049459 := bstep (se 1 (by rfl) ⟨3037094, by rfl⟩ : syracuseStep 4049459 = 6074189) B6074189
theorem B1264183 : Blo 1262449 1264183 := bstep (se 1 (by rfl) ⟨948137, by rfl⟩ : syracuseStep 1264183 = 1896275) B1896275
theorem B3197515 : Blo 1262449 3197515 := bstep (se 1 (by rfl) ⟨2398136, by rfl⟩ : syracuseStep 3197515 = 4796273) B4796273
theorem B1264203 : Blo 1262449 1264203 := bstep (se 1 (by rfl) ⟨948152, by rfl⟩ : syracuseStep 1264203 = 1896305) B1896305
theorem B1264215 : Blo 1262449 1264215 := bstep (se 1 (by rfl) ⟨948161, by rfl⟩ : syracuseStep 1264215 = 1896323) B1896323
theorem B4262489 : Blo 1262449 4262489 := bstep (se 2 (by rfl) ⟨1598433, by rfl⟩ : syracuseStep 4262489 = 3196867) B3196867
theorem B3598937 : Blo 1262449 3598937 := bstep (se 2 (by rfl) ⟨1349601, by rfl⟩ : syracuseStep 3598937 = 2699203) B2699203
theorem B1264235 : Blo 1262449 1264235 := bstep (se 1 (by rfl) ⟨948176, by rfl⟩ : syracuseStep 1264235 = 1896353) B1896353
theorem B1264247 : Blo 1262449 1264247 := bstep (se 1 (by rfl) ⟨948185, by rfl⟩ : syracuseStep 1264247 = 1896371) B1896371
theorem B1895051 : Blo 1262449 1895051 := bstep (se 1 (by rfl) ⟨1421288, by rfl⟩ : syracuseStep 1895051 = 2842577) B2842577
theorem B1264267 : Blo 1262449 1264267 := bstep (se 1 (by rfl) ⟨948200, by rfl⟩ : syracuseStep 1264267 = 1896401) B1896401
theorem B1895063 : Blo 1262449 1895063 := bstep (se 1 (by rfl) ⟨1421297, by rfl⟩ : syracuseStep 1895063 = 2842595) B2842595
theorem B1264279 : Blo 1262449 1264279 := bstep (se 1 (by rfl) ⟨948209, by rfl⟩ : syracuseStep 1264279 = 1896419) B1896419
theorem B1264299 : Blo 1262449 1264299 := bstep (se 1 (by rfl) ⟨948224, by rfl⟩ : syracuseStep 1264299 = 1896449) B1896449
theorem B1264311 : Blo 1262449 1264311 := bstep (se 1 (by rfl) ⟨948233, by rfl⟩ : syracuseStep 1264311 = 1896467) B1896467
theorem B1264331 : Blo 1262449 1264331 := bstep (se 1 (by rfl) ⟨948248, by rfl⟩ : syracuseStep 1264331 = 1896497) B1896497
theorem B1264343 : Blo 1262449 1264343 := bstep (se 1 (by rfl) ⟨948257, by rfl⟩ : syracuseStep 1264343 = 1896515) B1896515
theorem B3197657 : Blo 1262449 3197657 := bstep (se 2 (by rfl) ⟨1199121, by rfl⟩ : syracuseStep 3197657 = 2398243) B2398243
theorem B1895129 : Blo 1262449 1895129 := bstep (se 2 (by rfl) ⟨710673, by rfl⟩ : syracuseStep 1895129 = 1421347) B1421347
theorem B1264363 : Blo 1262449 1264363 := bstep (se 1 (by rfl) ⟨948272, by rfl⟩ : syracuseStep 1264363 = 1896545) B1896545
theorem B1264375 : Blo 1262449 1264375 := bstep (se 1 (by rfl) ⟨948281, by rfl⟩ : syracuseStep 1264375 = 1896563) B1896563
theorem B1264395 : Blo 1262449 1264395 := bstep (se 1 (by rfl) ⟨948296, by rfl⟩ : syracuseStep 1264395 = 1896593) B1896593
theorem B1518359 : Blo 1262449 1518359 := bstep (se 1 (by rfl) ⟨1138769, by rfl⟩ : syracuseStep 1518359 = 2277539) B2277539
theorem B1264407 : Blo 1262449 1264407 := bstep (se 1 (by rfl) ⟨948305, by rfl⟩ : syracuseStep 1264407 = 1896611) B1896611
theorem B1264427 : Blo 1262449 1264427 := bstep (se 1 (by rfl) ⟨948320, by rfl⟩ : syracuseStep 1264427 = 1896641) B1896641
theorem B1264439 : Blo 1262449 1264439 := bstep (se 1 (by rfl) ⟨948329, by rfl⟩ : syracuseStep 1264439 = 1896659) B1896659
theorem B1895243 : Blo 1262449 1895243 := bstep (se 1 (by rfl) ⟨1421432, by rfl⟩ : syracuseStep 1895243 = 2842865) B2842865
theorem B1895255 : Blo 1262449 1895255 := bstep (se 1 (by rfl) ⟨1421441, by rfl⟩ : syracuseStep 1895255 = 2842883) B2842883
theorem B3599255 : Blo 1262449 3599255 := bstep (se 1 (by rfl) ⟨2699441, by rfl⟩ : syracuseStep 3599255 = 5398883) B5398883
theorem B1895321 : Blo 1262449 1895321 := bstep (se 2 (by rfl) ⟨710745, by rfl⟩ : syracuseStep 1895321 = 1421491) B1421491
theorem B2567065 : Blo 1262449 2567065 := bstep (se 2 (by rfl) ⟨962649, by rfl⟩ : syracuseStep 2567065 = 1925299) B1925299
theorem B2132939 : Blo 1262449 2132939 := bstep (se 1 (by rfl) ⟨1599704, by rfl⟩ : syracuseStep 2132939 = 3199409) B3199409
theorem B1420267 : Blo 1262449 1420267 := bstep (se 1 (by rfl) ⟨1065200, by rfl⟩ : syracuseStep 1420267 = 2130401) B2130401
theorem B1895435 : Blo 1262449 1895435 := bstep (se 1 (by rfl) ⟨1421576, by rfl⟩ : syracuseStep 1895435 = 2843153) B2843153
theorem B1895447 : Blo 1262449 1895447 := bstep (se 1 (by rfl) ⟨1421585, by rfl⟩ : syracuseStep 1895447 = 2843171) B2843171
theorem B2133067 : Blo 1262449 2133067 := bstep (se 1 (by rfl) ⟨1599800, by rfl⟩ : syracuseStep 2133067 = 3199601) B3199601
theorem B1420375 : Blo 1262449 1420375 := bstep (se 1 (by rfl) ⟨1065281, by rfl⟩ : syracuseStep 1420375 = 2130563) B2130563
theorem B1707095 : Blo 1262449 1707095 := bstep (se 1 (by rfl) ⟨1280321, by rfl⟩ : syracuseStep 1707095 = 2560643) B2560643
theorem B3034201 : Blo 1262449 3034201 := bstep (se 2 (by rfl) ⟨1137825, by rfl⟩ : syracuseStep 3034201 = 2275651) B2275651
theorem B1895513 : Blo 1262449 1895513 := bstep (se 2 (by rfl) ⟨710817, by rfl⟩ : syracuseStep 1895513 = 1421635) B1421635
theorem B5393587 : Blo 1262449 5393587 := bstep (se 1 (by rfl) ⟨4045190, by rfl⟩ : syracuseStep 5393587 = 8090381) B8090381
theorem B1895627 : Blo 1262449 1895627 := bstep (se 1 (by rfl) ⟨1421720, by rfl⟩ : syracuseStep 1895627 = 2843441) B2843441
theorem B1895639 : Blo 1262449 1895639 := bstep (se 1 (by rfl) ⟨1421729, by rfl⟩ : syracuseStep 1895639 = 2843459) B2843459
theorem B2133209 : Blo 1262449 2133209 := bstep (se 2 (by rfl) ⟨799953, by rfl⟩ : syracuseStep 2133209 = 1599907) B1599907
theorem B4050137 : Blo 1262449 4050137 := bstep (se 2 (by rfl) ⟨1518801, by rfl⟩ : syracuseStep 4050137 = 3037603) B3037603
theorem B55430405 : Blo 1262449 55430405 := bstep (se 4 (by rfl) ⟨5196600, by rfl⟩ : syracuseStep 55430405 = 10393201) B10393201
theorem B1420555 : Blo 1262449 1420555 := bstep (se 1 (by rfl) ⟨1065416, by rfl⟩ : syracuseStep 1420555 = 2130833) B2130833
theorem B1518859 : Blo 1262449 1518859 := bstep (se 1 (by rfl) ⟨1139144, by rfl⟩ : syracuseStep 1518859 = 2278289) B2278289
theorem B4263191 : Blo 1262449 4263191 := bstep (se 1 (by rfl) ⟨3197393, by rfl⟩ : syracuseStep 4263191 = 6394787) B6394787
theorem B1895705 : Blo 1262449 1895705 := bstep (se 2 (by rfl) ⟨710889, by rfl⟩ : syracuseStep 1895705 = 1421779) B1421779
theorem B2698571 : Blo 1262449 2698571 := bstep (se 1 (by rfl) ⟨2023928, by rfl⟩ : syracuseStep 2698571 = 4047857) B4047857
theorem B2133337 : Blo 1262449 2133337 := bstep (se 2 (by rfl) ⟨800001, by rfl⟩ : syracuseStep 2133337 = 1600003) B1600003
theorem B1420663 : Blo 1262449 1420663 := bstep (se 1 (by rfl) ⟨1065497, by rfl⟩ : syracuseStep 1420663 = 2130995) B2130995
theorem B1895819 : Blo 1262449 1895819 := bstep (se 1 (by rfl) ⟨1421864, by rfl⟩ : syracuseStep 1895819 = 2843729) B2843729
theorem B1895831 : Blo 1262449 1895831 := bstep (se 1 (by rfl) ⟨1421873, by rfl⟩ : syracuseStep 1895831 = 2843747) B2843747
theorem B12307889 : Blo 1262449 12307889 := bstep (se 2 (by rfl) ⟨4615458, by rfl⟩ : syracuseStep 12307889 = 9230917) B9230917
theorem B1895897 : Blo 1262449 1895897 := bstep (se 2 (by rfl) ⟨710961, by rfl⟩ : syracuseStep 1895897 = 1421923) B1421923
theorem B3198487 : Blo 1262449 3198487 := bstep (se 1 (by rfl) ⟨2398865, by rfl⟩ : syracuseStep 3198487 = 4797731) B4797731
theorem B1420843 : Blo 1262449 1420843 := bstep (se 1 (by rfl) ⟨1065632, by rfl⟩ : syracuseStep 1420843 = 2131265) B2131265
theorem B4795955 : Blo 1262449 4795955 := bstep (se 1 (by rfl) ⟨3596966, by rfl⟩ : syracuseStep 4795955 = 7193933) B7193933
theorem B4795969 : Blo 1262449 4795969 := bstep (se 2 (by rfl) ⟨1798488, by rfl⟩ : syracuseStep 4795969 = 3596977) B3596977
theorem B1896011 : Blo 1262449 1896011 := bstep (se 1 (by rfl) ⟨1422008, by rfl⟩ : syracuseStep 1896011 = 2844017) B2844017
theorem B1896023 : Blo 1262449 1896023 := bstep (se 1 (by rfl) ⟨1422017, by rfl⟩ : syracuseStep 1896023 = 2844035) B2844035
theorem B1420951 : Blo 1262449 1420951 := bstep (se 1 (by rfl) ⟨1065713, by rfl⟩ : syracuseStep 1420951 = 2131427) B2131427
theorem B1896089 : Blo 1262449 1896089 := bstep (se 2 (by rfl) ⟨711033, by rfl⟩ : syracuseStep 1896089 = 1422067) B1422067
theorem B4992691 : Blo 1262449 4992691 := bstep (se 1 (by rfl) ⟨3744518, by rfl⟩ : syracuseStep 4992691 = 7489037) B7489037
theorem B3034817 : Blo 1262449 3034817 := bstep (se 2 (by rfl) ⟨1138056, by rfl⟩ : syracuseStep 3034817 = 2276113) B2276113
theorem B3600065 : Blo 1262449 3600065 := bstep (se 2 (by rfl) ⟨1350024, by rfl⟩ : syracuseStep 3600065 = 2700049) B2700049
theorem B10792709 : Blo 1262449 10792709 := bstep (se 4 (by rfl) ⟨1011816, by rfl⟩ : syracuseStep 10792709 = 2023633) B2023633
theorem B1896203 : Blo 1262449 1896203 := bstep (se 1 (by rfl) ⟨1422152, by rfl⟩ : syracuseStep 1896203 = 2844305) B2844305
theorem B1896215 : Blo 1262449 1896215 := bstep (se 1 (by rfl) ⟨1422161, by rfl⟩ : syracuseStep 1896215 = 2844323) B2844323
theorem B5394221 : Blo 1262449 5394221 := bstep (se 3 (by rfl) ⟨1011416, by rfl⟩ : syracuseStep 5394221 = 2022833) B2022833
theorem B4263731 : Blo 1262449 4263731 := bstep (se 1 (by rfl) ⟨3197798, by rfl⟩ : syracuseStep 4263731 = 6395597) B6395597
theorem B1421131 : Blo 1262449 1421131 := bstep (se 1 (by rfl) ⟨1065848, by rfl⟩ : syracuseStep 1421131 = 2131697) B2131697
theorem B1896281 : Blo 1262449 1896281 := bstep (se 2 (by rfl) ⟨711105, by rfl⟩ : syracuseStep 1896281 = 1422211) B1422211
theorem B1421239 : Blo 1262449 1421239 := bstep (se 1 (by rfl) ⟨1065929, by rfl⟩ : syracuseStep 1421239 = 2131859) B2131859
theorem B3198923 : Blo 1262449 3198923 := bstep (se 1 (by rfl) ⟨2399192, by rfl⟩ : syracuseStep 3198923 = 4798385) B4798385
theorem B1896395 : Blo 1262449 1896395 := bstep (se 1 (by rfl) ⟨1422296, by rfl⟩ : syracuseStep 1896395 = 2844593) B2844593
theorem B1896407 : Blo 1262449 1896407 := bstep (se 1 (by rfl) ⟨1422305, by rfl⟩ : syracuseStep 1896407 = 2844611) B2844611
theorem B2559961 : Blo 1262449 2559961 := bstep (se 2 (by rfl) ⟨959985, by rfl⟩ : syracuseStep 2559961 = 1919971) B1919971
theorem B1896473 : Blo 1262449 1896473 := bstep (se 2 (by rfl) ⟨711177, by rfl⟩ : syracuseStep 1896473 = 1422355) B1422355
theorem B4264001 : Blo 1262449 4264001 := bstep (se 2 (by rfl) ⟨1599000, by rfl⟩ : syracuseStep 4264001 = 3198001) B3198001
theorem B7491685 : Blo 1262449 7491685 := bstep (se 4 (by rfl) ⟨702345, by rfl⟩ : syracuseStep 7491685 = 1404691) B1404691
theorem B8097893 : Blo 1262449 8097893 := bstep (se 4 (by rfl) ⟨759177, by rfl⟩ : syracuseStep 8097893 = 1518355) B1518355
theorem B1421419 : Blo 1262449 1421419 := bstep (se 1 (by rfl) ⟨1066064, by rfl⟩ : syracuseStep 1421419 = 2132129) B2132129
theorem B1896587 : Blo 1262449 1896587 := bstep (se 1 (by rfl) ⟨1422440, by rfl⟩ : syracuseStep 1896587 = 2844881) B2844881
theorem B1896599 : Blo 1262449 1896599 := bstep (se 1 (by rfl) ⟨1422449, by rfl⟩ : syracuseStep 1896599 = 2844899) B2844899
theorem B1421527 : Blo 1262449 1421527 := bstep (se 1 (by rfl) ⟨1066145, by rfl⟩ : syracuseStep 1421527 = 2132291) B2132291
theorem B1896665 : Blo 1262449 1896665 := bstep (se 2 (by rfl) ⟨711249, by rfl⟩ : syracuseStep 1896665 = 1422499) B1422499
theorem B10244387 : Blo 1262449 10244387 := bstep (se 1 (by rfl) ⟨7683290, by rfl⟩ : syracuseStep 10244387 = 15366581) B15366581
theorem B3199297 : Blo 1262449 3199297 := bstep (se 2 (by rfl) ⟨1199736, by rfl⟩ : syracuseStep 3199297 = 2399473) B2399473
theorem B1421707 : Blo 1262449 1421707 := bstep (se 1 (by rfl) ⟨1066280, by rfl⟩ : syracuseStep 1421707 = 2132561) B2132561
theorem B4321687 : Blo 1262449 4321687 := bstep (se 1 (by rfl) ⟨3241265, by rfl⟩ : syracuseStep 4321687 = 6482531) B6482531
theorem B1421815 : Blo 1262449 1421815 := bstep (se 1 (by rfl) ⟨1066361, by rfl⟩ : syracuseStep 1421815 = 2132723) B2132723
theorem B9589265 : Blo 1262449 9589265 := bstep (se 2 (by rfl) ⟨3595974, by rfl⟩ : syracuseStep 9589265 = 7191949) B7191949
theorem B2699801 : Blo 1262449 2699801 := bstep (se 2 (by rfl) ⟨1012425, by rfl⟩ : syracuseStep 2699801 = 2024851) B2024851
theorem B8098379 : Blo 1262449 8098379 := bstep (se 1 (by rfl) ⟨6073784, by rfl⟩ : syracuseStep 8098379 = 12147569) B12147569
theorem B1348183 : Blo 1262449 1348183 := bstep (se 1 (by rfl) ⟨1011137, by rfl⟩ : syracuseStep 1348183 = 2022275) B2022275
theorem B4264541 : Blo 1262449 4264541 := bstep (se 3 (by rfl) ⟨799601, by rfl⟩ : syracuseStep 4264541 = 1599203) B1599203
theorem B41538179 : Blo 1262449 41538179 := bstep (se 1 (by rfl) ⟨31153634, by rfl⟩ : syracuseStep 41538179 = 62307269) B62307269
theorem B1421995 : Blo 1262449 1421995 := bstep (se 1 (by rfl) ⟨1066496, by rfl⟩ : syracuseStep 1421995 = 2132993) B2132993
theorem B630477553 : Blo 1262449 630477553 := bstep (se 2 (by rfl) ⟨236429082, by rfl⟩ : syracuseStep 630477553 = 472858165) B472858165
theorem B1348363 : Blo 1262449 1348363 := bstep (se 1 (by rfl) ⟨1011272, by rfl⟩ : syracuseStep 1348363 = 2022545) B2022545
theorem B1422103 : Blo 1262449 1422103 := bstep (se 1 (by rfl) ⟨1066577, by rfl⟩ : syracuseStep 1422103 = 2133155) B2133155
theorem B1708825 : Blo 1262449 1708825 := bstep (se 2 (by rfl) ⟨640809, by rfl⟩ : syracuseStep 1708825 = 1281619) B1281619
theorem B2339635 : Blo 1262449 2339635 := bstep (se 1 (by rfl) ⟨1754726, by rfl⟩ : syracuseStep 2339635 = 3509453) B3509453
theorem B2397043 : Blo 1262449 2397043 := bstep (se 1 (by rfl) ⟨1797782, by rfl⟩ : syracuseStep 2397043 = 3595565) B3595565
theorem B3199895 : Blo 1262449 3199895 := bstep (se 1 (by rfl) ⟨2399921, by rfl⟩ : syracuseStep 3199895 = 4799843) B4799843
theorem B2700211 : Blo 1262449 2700211 := bstep (se 1 (by rfl) ⟨2025158, by rfl⟩ : syracuseStep 2700211 = 4050317) B4050317
theorem B1422283 : Blo 1262449 1422283 := bstep (se 1 (by rfl) ⟨1066712, by rfl⟩ : syracuseStep 1422283 = 2133425) B2133425
theorem B44356643 : Blo 1262449 44356643 := bstep (se 1 (by rfl) ⟨33267482, by rfl⟩ : syracuseStep 44356643 = 66534965) B66534965
theorem B1422391 : Blo 1262449 1422391 := bstep (se 1 (by rfl) ⟨1066793, by rfl⟩ : syracuseStep 1422391 = 2133587) B2133587
theorem B33264715 : Blo 1262449 33264715 := bstep (se 1 (by rfl) ⟨24948536, by rfl⟩ : syracuseStep 33264715 = 49897073) B49897073
theorem B2397271 : Blo 1262449 2397271 := bstep (se 1 (by rfl) ⟨1797953, by rfl⟩ : syracuseStep 2397271 = 3595907) B3595907
theorem B2700467 : Blo 1262449 2700467 := bstep (se 1 (by rfl) ⟨2025350, by rfl⟩ : syracuseStep 2700467 = 4050701) B4050701
theorem B2397377 : Blo 1262449 2397377 := bstep (se 2 (by rfl) ⟨899016, by rfl⟩ : syracuseStep 2397377 = 1798033) B1798033
theorem B3413195 : Blo 1262449 3413195 := bstep (se 1 (by rfl) ⟨2559896, by rfl⟩ : syracuseStep 3413195 = 5119793) B5119793
theorem B2340083 : Blo 1262449 2340083 := bstep (se 1 (by rfl) ⟨1755062, by rfl⟩ : syracuseStep 2340083 = 3510125) B3510125
theorem B32371973 : Blo 1262449 32371973 := bstep (se 4 (by rfl) ⟨3034872, by rfl⟩ : syracuseStep 32371973 = 6069745) B6069745
theorem B2397529 : Blo 1262449 2397529 := bstep (se 2 (by rfl) ⟨899073, by rfl⟩ : syracuseStep 2397529 = 1798147) B1798147
theorem B10245527 : Blo 1262449 10245527 := bstep (se 1 (by rfl) ⟨7684145, by rfl⟩ : syracuseStep 10245527 = 15368291) B15368291
theorem B4552139 : Blo 1262449 4552139 := bstep (se 1 (by rfl) ⟨3414104, by rfl⟩ : syracuseStep 4552139 = 6828209) B6828209
theorem B4797899 : Blo 1262449 4797899 := bstep (se 1 (by rfl) ⟨3598424, by rfl⟩ : syracuseStep 4797899 = 7196849) B7196849
theorem B4797913 : Blo 1262449 4797913 := bstep (se 2 (by rfl) ⟨1799217, by rfl⟩ : syracuseStep 4797913 = 3598435) B3598435
theorem B4552195 : Blo 1262449 4552195 := bstep (se 1 (by rfl) ⟨3414146, by rfl⟩ : syracuseStep 4552195 = 6828293) B6828293
theorem B9598499 : Blo 1262449 9598499 := bstep (se 1 (by rfl) ⟨7198874, by rfl⟩ : syracuseStep 9598499 = 14397749) B14397749
theorem B1799833 : Blo 1262449 1799833 := bstep (se 2 (by rfl) ⟨674937, by rfl⟩ : syracuseStep 1799833 = 1349875) B1349875
theorem B10245811 : Blo 1262449 10245811 := bstep (se 1 (by rfl) ⟨7684358, by rfl⟩ : syracuseStep 10245811 = 15368717) B15368717
theorem B4265675 : Blo 1262449 4265675 := bstep (se 1 (by rfl) ⟨3199256, by rfl⟩ : syracuseStep 4265675 = 6398513) B6398513
theorem B8091353 : Blo 1262449 8091353 := bstep (se 2 (by rfl) ⟨3034257, by rfl⟩ : syracuseStep 8091353 = 6068515) B6068515
theorem B6076205 : Blo 1262449 6076205 := bstep (se 3 (by rfl) ⟨1139288, by rfl⟩ : syracuseStep 6076205 = 2278577) B2278577
theorem B2561843 : Blo 1262449 2561843 := bstep (se 1 (by rfl) ⟨1921382, by rfl⟩ : syracuseStep 2561843 = 3842765) B3842765
theorem B16627673 : Blo 1262449 16627673 := bstep (se 2 (by rfl) ⟨6235377, by rfl⟩ : syracuseStep 16627673 = 12470755) B12470755
theorem B4265945 : Blo 1262449 4265945 := bstep (se 2 (by rfl) ⟨1599729, by rfl⟩ : syracuseStep 4265945 = 3199459) B3199459
theorem B6395921 : Blo 1262449 6395921 := bstep (se 2 (by rfl) ⟨2398470, by rfl⟩ : syracuseStep 6395921 = 4796941) B4796941
theorem B14039075 : Blo 1262449 14039075 := bstep (se 1 (by rfl) ⟨10529306, by rfl⟩ : syracuseStep 14039075 = 21058613) B21058613
theorem B2881601 : Blo 1262449 2881601 := bstep (se 2 (by rfl) ⟨1080600, by rfl⟩ : syracuseStep 2881601 = 2161201) B2161201
theorem B2840651 : Blo 1262449 2840651 := bstep (se 1 (by rfl) ⟨2130488, by rfl⟩ : syracuseStep 2840651 = 4260977) B4260977
theorem B2840705 : Blo 1262449 2840705 := bstep (se 2 (by rfl) ⟨1065264, by rfl⟩ : syracuseStep 2840705 = 2130529) B2130529
theorem B4864151 : Blo 1262449 4864151 := bstep (se 1 (by rfl) ⟨3648113, by rfl⟩ : syracuseStep 4864151 = 7296227) B7296227
theorem B6396083 : Blo 1262449 6396083 := bstep (se 1 (by rfl) ⟨4797062, by rfl⟩ : syracuseStep 6396083 = 9594125) B9594125
theorem B6830411 : Blo 1262449 6830411 := bstep (se 1 (by rfl) ⟨5122808, by rfl⟩ : syracuseStep 6830411 = 10245617) B10245617
theorem B2840921 : Blo 1262449 2840921 := bstep (se 2 (by rfl) ⟨1065345, by rfl⟩ : syracuseStep 2840921 = 2130691) B2130691
theorem B18200933 : Blo 1262449 18200933 := bstep (se 4 (by rfl) ⟨1706337, by rfl⟩ : syracuseStep 18200933 = 3412675) B3412675
theorem B2562443 : Blo 1262449 2562443 := bstep (se 1 (by rfl) ⟨1921832, by rfl⟩ : syracuseStep 2562443 = 3843665) B3843665
theorem B4798871 : Blo 1262449 4798871 := bstep (se 1 (by rfl) ⟨3599153, by rfl⟩ : syracuseStep 4798871 = 7198307) B7198307
theorem B2841011 : Blo 1262449 2841011 := bstep (se 1 (by rfl) ⟨2130758, by rfl⟩ : syracuseStep 2841011 = 4261517) B4261517
theorem B2841047 : Blo 1262449 2841047 := bstep (se 1 (by rfl) ⟨2130785, by rfl⟩ : syracuseStep 2841047 = 4261571) B4261571
theorem B2398835 : Blo 1262449 2398835 := bstep (se 1 (by rfl) ⟨1799126, by rfl⟩ : syracuseStep 2398835 = 3598253) B3598253
theorem B2841227 : Blo 1262449 2841227 := bstep (se 1 (by rfl) ⟨2130920, by rfl⟩ : syracuseStep 2841227 = 4261841) B4261841
theorem B4266647 : Blo 1262449 4266647 := bstep (se 1 (by rfl) ⟨3199985, by rfl⟩ : syracuseStep 4266647 = 6399971) B6399971
theorem B2841281 : Blo 1262449 2841281 := bstep (se 2 (by rfl) ⟨1065480, by rfl⟩ : syracuseStep 2841281 = 2130961) B2130961
theorem B2882291 : Blo 1262449 2882291 := bstep (se 1 (by rfl) ⟨2161718, by rfl⟩ : syracuseStep 2882291 = 4323437) B4323437
theorem B2398987 : Blo 1262449 2398987 := bstep (se 1 (by rfl) ⟨1799240, by rfl⟩ : syracuseStep 2398987 = 3598481) B3598481
theorem B4553495 : Blo 1262449 4553495 := bstep (se 1 (by rfl) ⟨3415121, by rfl⟩ : syracuseStep 4553495 = 6830243) B6830243
theorem B2841497 : Blo 1262449 2841497 := bstep (se 2 (by rfl) ⟨1065561, by rfl⟩ : syracuseStep 2841497 = 2131123) B2131123
theorem B2841587 : Blo 1262449 2841587 := bstep (se 1 (by rfl) ⟨2131190, by rfl⟩ : syracuseStep 2841587 = 4262381) B4262381
theorem B2595827 : Blo 1262449 2595827 := bstep (se 1 (by rfl) ⟨1946870, by rfl⟩ : syracuseStep 2595827 = 3893741) B3893741
theorem B2841623 : Blo 1262449 2841623 := bstep (se 1 (by rfl) ⟨2131217, by rfl⟩ : syracuseStep 2841623 = 4262435) B4262435
theorem B2399321 : Blo 1262449 2399321 := bstep (se 2 (by rfl) ⟨899745, by rfl⟩ : syracuseStep 2399321 = 1799491) B1799491
theorem B10796125 : Blo 1262449 10796125 := bstep (se 3 (by rfl) ⟨2024273, by rfl⟩ : syracuseStep 10796125 = 4048547) B4048547
theorem B4267187 : Blo 1262449 4267187 := bstep (se 1 (by rfl) ⟨3200390, by rfl⟩ : syracuseStep 4267187 = 6400781) B6400781
theorem B8101043 : Blo 1262449 8101043 := bstep (se 1 (by rfl) ⟨6075782, by rfl⟩ : syracuseStep 8101043 = 12151565) B12151565
theorem B2841803 : Blo 1262449 2841803 := bstep (se 1 (by rfl) ⟨2131352, by rfl⟩ : syracuseStep 2841803 = 4262705) B4262705
theorem B2841857 : Blo 1262449 2841857 := bstep (se 2 (by rfl) ⟨1065696, by rfl⟩ : syracuseStep 2841857 = 2131393) B2131393
theorem B18455813 : Blo 1262449 18455813 := bstep (se 4 (by rfl) ⟨1730232, by rfl⟩ : syracuseStep 18455813 = 3460465) B3460465
theorem B2022679 : Blo 1262449 2022679 := bstep (se 1 (by rfl) ⟨1517009, by rfl⟩ : syracuseStep 2022679 = 3034019) B3034019
theorem B8641837 : Blo 1262449 8641837 := bstep (se 3 (by rfl) ⟨1620344, by rfl⟩ : syracuseStep 8641837 = 3240689) B3240689
theorem B5397911 : Blo 1262449 5397911 := bstep (se 1 (by rfl) ⟨4048433, by rfl⟩ : syracuseStep 5397911 = 8096867) B8096867
theorem B12139955 : Blo 1262449 12139955 := bstep (se 1 (by rfl) ⟨9104966, by rfl⟩ : syracuseStep 12139955 = 18209933) B18209933
theorem B4267457 : Blo 1262449 4267457 := bstep (se 2 (by rfl) ⟨1600296, by rfl⟩ : syracuseStep 4267457 = 3200593) B3200593
theorem B2842073 : Blo 1262449 2842073 := bstep (se 2 (by rfl) ⟨1065777, by rfl⟩ : syracuseStep 2842073 = 2131555) B2131555
theorem B2842163 : Blo 1262449 2842163 := bstep (se 1 (by rfl) ⟨2131622, by rfl⟩ : syracuseStep 2842163 = 4263245) B4263245
theorem B2842199 : Blo 1262449 2842199 := bstep (se 1 (by rfl) ⟨2131649, by rfl⟩ : syracuseStep 2842199 = 4263299) B4263299
theorem B4800131 : Blo 1262449 4800131 := bstep (se 1 (by rfl) ⟨3600098, by rfl⟩ : syracuseStep 4800131 = 7200197) B7200197
theorem B2399959 : Blo 1262449 2399959 := bstep (se 1 (by rfl) ⟨1799969, by rfl⟩ : syracuseStep 2399959 = 3599939) B3599939
theorem B2842379 : Blo 1262449 2842379 := bstep (se 1 (by rfl) ⟨2131784, by rfl⟩ : syracuseStep 2842379 = 4263569) B4263569
theorem B2842433 : Blo 1262449 2842433 := bstep (se 2 (by rfl) ⟨1065912, by rfl⟩ : syracuseStep 2842433 = 2131825) B2131825
theorem B2277209 : Blo 1262449 2277209 := bstep (se 2 (by rfl) ⟨853953, by rfl⟩ : syracuseStep 2277209 = 1707907) B1707907
theorem B2842667 : Blo 1262449 2842667 := bstep (se 1 (by rfl) ⟨2132000, by rfl⟩ : syracuseStep 2842667 = 4264001) B4264001
theorem B5398595 : Blo 1262449 5398595 := bstep (se 1 (by rfl) ⟨4048946, by rfl⟩ : syracuseStep 5398595 = 8097893) B8097893
theorem B6398189 : Blo 1262449 6398189 := bstep (se 3 (by rfl) ⟨1199660, by rfl⟩ : syracuseStep 6398189 = 2399321) B2399321
theorem B3694909 : Blo 1262449 3694909 := bstep (se 3 (by rfl) ⟨692795, by rfl⟩ : syracuseStep 3694909 = 1385591) B1385591
theorem B5398919 : Blo 1262449 5398919 := bstep (se 1 (by rfl) ⟨4049189, by rfl⟩ : syracuseStep 5398919 = 8098379) B8098379
theorem B12976519 : Blo 1262449 12976519 := bstep (se 1 (by rfl) ⟨9732389, by rfl⟩ : syracuseStep 12976519 = 19464779) B19464779
theorem B9601415 : Blo 1262449 9601415 := bstep (se 1 (by rfl) ⟨7201061, by rfl⟩ : syracuseStep 9601415 = 14402123) B14402123
theorem B2843027 : Blo 1262449 2843027 := bstep (se 1 (by rfl) ⟨2132270, by rfl⟩ : syracuseStep 2843027 = 4264541) B4264541
theorem B2843081 : Blo 1262449 2843081 := bstep (se 2 (by rfl) ⟨1066155, by rfl⟩ : syracuseStep 2843081 = 2132311) B2132311
theorem B2130475 : Blo 1262449 2130475 := bstep (se 1 (by rfl) ⟨1597856, by rfl⟩ : syracuseStep 2130475 = 3195713) B3195713
theorem B2130617 : Blo 1262449 2130617 := bstep (se 2 (by rfl) ⟨798981, by rfl⟩ : syracuseStep 2130617 = 1597963) B1597963
theorem B1262471 : Blo 1262449 1262471 := bstep (se 1 (by rfl) ⟨946853, by rfl⟩ : syracuseStep 1262471 = 1893707) B1893707
theorem B4555655 : Blo 1262449 4555655 := bstep (se 1 (by rfl) ⟨3416741, by rfl⟩ : syracuseStep 4555655 = 6833483) B6833483
theorem B1262479 : Blo 1262449 1262479 := bstep (se 1 (by rfl) ⟨946859, by rfl⟩ : syracuseStep 1262479 = 1893719) B1893719
theorem B1262523 : Blo 1262449 1262523 := bstep (se 1 (by rfl) ⟨946892, by rfl⟩ : syracuseStep 1262523 = 1893785) B1893785
theorem B1262599 : Blo 1262449 1262599 := bstep (se 1 (by rfl) ⟨946949, by rfl⟩ : syracuseStep 1262599 = 1893899) B1893899
theorem B1262607 : Blo 1262449 1262607 := bstep (se 1 (by rfl) ⟨946955, by rfl⟩ : syracuseStep 1262607 = 1893911) B1893911
theorem B6398999 : Blo 1262449 6398999 := bstep (se 1 (by rfl) ⟨4799249, by rfl⟩ : syracuseStep 6398999 = 9598499) B9598499
theorem B2278433 : Blo 1262449 2278433 := bstep (se 2 (by rfl) ⟨854412, by rfl⟩ : syracuseStep 2278433 = 1708825) B1708825
theorem B1262651 : Blo 1262449 1262651 := bstep (se 1 (by rfl) ⟨946988, by rfl⟩ : syracuseStep 1262651 = 1893977) B1893977
theorem B3949687 : Blo 1262449 3949687 := bstep (se 1 (by rfl) ⟨2962265, by rfl⟩ : syracuseStep 3949687 = 5924531) B5924531
theorem B1262727 : Blo 1262449 1262727 := bstep (se 1 (by rfl) ⟨947045, by rfl⟩ : syracuseStep 1262727 = 1894091) B1894091
theorem B2843783 : Blo 1262449 2843783 := bstep (se 1 (by rfl) ⟨2132837, by rfl⟩ : syracuseStep 2843783 = 4265675) B4265675
theorem B1262735 : Blo 1262449 1262735 := bstep (se 1 (by rfl) ⟨947051, by rfl⟩ : syracuseStep 1262735 = 1894103) B1894103
theorem B3196057 : Blo 1262449 3196057 := bstep (se 2 (by rfl) ⟨1198521, by rfl⟩ : syracuseStep 3196057 = 2397043) B2397043
theorem B1262779 : Blo 1262449 1262779 := bstep (se 1 (by rfl) ⟨947084, by rfl⟩ : syracuseStep 1262779 = 1894169) B1894169
theorem B1262855 : Blo 1262449 1262855 := bstep (se 1 (by rfl) ⟨947141, by rfl⟩ : syracuseStep 1262855 = 1894283) B1894283
theorem B1262863 : Blo 1262449 1262863 := bstep (se 1 (by rfl) ⟨947147, by rfl⟩ : syracuseStep 1262863 = 1894295) B1894295
theorem B1893689 : Blo 1262449 1893689 := bstep (se 2 (by rfl) ⟨710133, by rfl⟩ : syracuseStep 1893689 = 1420267) B1420267
theorem B3196219 : Blo 1262449 3196219 := bstep (se 1 (by rfl) ⟨2397164, by rfl⟩ : syracuseStep 3196219 = 4794329) B4794329
theorem B11085115 : Blo 1262449 11085115 := bstep (se 1 (by rfl) ⟨8313836, by rfl⟩ : syracuseStep 11085115 = 16627673) B16627673
theorem B1262907 : Blo 1262449 1262907 := bstep (se 1 (by rfl) ⟨947180, by rfl⟩ : syracuseStep 1262907 = 1894361) B1894361
theorem B2843963 : Blo 1262449 2843963 := bstep (se 1 (by rfl) ⟨2132972, by rfl⟩ : syracuseStep 2843963 = 4265945) B4265945
theorem B2131319 : Blo 1262449 2131319 := bstep (se 1 (by rfl) ⟨1598489, by rfl⟩ : syracuseStep 2131319 = 3196979) B3196979
theorem B1893767 : Blo 1262449 1893767 := bstep (se 1 (by rfl) ⟨1420325, by rfl⟩ : syracuseStep 1893767 = 2840651) B2840651
theorem B1262983 : Blo 1262449 1262983 := bstep (se 1 (by rfl) ⟨947237, by rfl⟩ : syracuseStep 1262983 = 1894475) B1894475
theorem B1262991 : Blo 1262449 1262991 := bstep (se 1 (by rfl) ⟨947243, by rfl⟩ : syracuseStep 1262991 = 1894487) B1894487
theorem B1893803 : Blo 1262449 1893803 := bstep (se 1 (by rfl) ⟨1420352, by rfl⟩ : syracuseStep 1893803 = 2840705) B2840705
theorem B44352953 : Blo 1262449 44352953 := bstep (se 2 (by rfl) ⟨16632357, by rfl⟩ : syracuseStep 44352953 = 33264715) B33264715
theorem B1263035 : Blo 1262449 1263035 := bstep (se 1 (by rfl) ⟨947276, by rfl⟩ : syracuseStep 1263035 = 1894553) B1894553
theorem B2844089 : Blo 1262449 2844089 := bstep (se 2 (by rfl) ⟨1066533, by rfl⟩ : syracuseStep 2844089 = 2133067) B2133067
theorem B1893833 : Blo 1262449 1893833 := bstep (se 2 (by rfl) ⟨710187, by rfl⟩ : syracuseStep 1893833 = 1420375) B1420375
theorem B3196361 : Blo 1262449 3196361 := bstep (se 2 (by rfl) ⟨1198635, by rfl⟩ : syracuseStep 3196361 = 2397271) B2397271
theorem B14394833 : Blo 1262449 14394833 := bstep (se 2 (by rfl) ⟨5398062, by rfl⟩ : syracuseStep 14394833 = 10796125) B10796125
theorem B1263111 : Blo 1262449 1263111 := bstep (se 1 (by rfl) ⟨947333, by rfl⟩ : syracuseStep 1263111 = 1894667) B1894667
theorem B1263119 : Blo 1262449 1263119 := bstep (se 1 (by rfl) ⟨947339, by rfl⟩ : syracuseStep 1263119 = 1894679) B1894679
theorem B1893947 : Blo 1262449 1893947 := bstep (se 1 (by rfl) ⟨1420460, by rfl⟩ : syracuseStep 1893947 = 2840921) B2840921
theorem B1263163 : Blo 1262449 1263163 := bstep (se 1 (by rfl) ⟨947372, by rfl⟩ : syracuseStep 1263163 = 1894745) B1894745
theorem B12133955 : Blo 1262449 12133955 := bstep (se 1 (by rfl) ⟨9100466, by rfl⟩ : syracuseStep 12133955 = 18200933) B18200933
theorem B4261463 : Blo 1262449 4261463 := bstep (se 1 (by rfl) ⟨3196097, by rfl⟩ : syracuseStep 4261463 = 6392195) B6392195
theorem B4048471 : Blo 1262449 4048471 := bstep (se 1 (by rfl) ⟨3036353, by rfl⟩ : syracuseStep 4048471 = 6072707) B6072707
theorem B1894007 : Blo 1262449 1894007 := bstep (se 1 (by rfl) ⟨1420505, by rfl⟩ : syracuseStep 1894007 = 2841011) B2841011
theorem B1263239 : Blo 1262449 1263239 := bstep (se 1 (by rfl) ⟨947429, by rfl⟩ : syracuseStep 1263239 = 1894859) B1894859
theorem B1894031 : Blo 1262449 1894031 := bstep (se 1 (by rfl) ⟨1420523, by rfl⟩ : syracuseStep 1894031 = 2841047) B2841047
theorem B1263247 : Blo 1262449 1263247 := bstep (se 1 (by rfl) ⟨947435, by rfl⟩ : syracuseStep 1263247 = 1894871) B1894871
theorem B1894073 : Blo 1262449 1894073 := bstep (se 2 (by rfl) ⟨710277, by rfl⟩ : syracuseStep 1894073 = 1420555) B1420555
theorem B2025145 : Blo 1262449 2025145 := bstep (se 2 (by rfl) ⟨759429, by rfl⟩ : syracuseStep 2025145 = 1518859) B1518859
theorem B1263291 : Blo 1262449 1263291 := bstep (se 1 (by rfl) ⟨947468, by rfl⟩ : syracuseStep 1263291 = 1894937) B1894937
theorem B2696905 : Blo 1262449 2696905 := bstep (se 2 (by rfl) ⟨1011339, by rfl⟩ : syracuseStep 2696905 = 2022679) B2022679
theorem B1894151 : Blo 1262449 1894151 := bstep (se 1 (by rfl) ⟨1420613, by rfl⟩ : syracuseStep 1894151 = 2841227) B2841227
theorem B1263367 : Blo 1262449 1263367 := bstep (se 1 (by rfl) ⟨947525, by rfl⟩ : syracuseStep 1263367 = 1895051) B1895051
theorem B1263375 : Blo 1262449 1263375 := bstep (se 1 (by rfl) ⟨947531, by rfl⟩ : syracuseStep 1263375 = 1895063) B1895063
theorem B2844431 : Blo 1262449 2844431 := bstep (se 1 (by rfl) ⟨2133323, by rfl⟩ : syracuseStep 2844431 = 4266647) B4266647
theorem B3196705 : Blo 1262449 3196705 := bstep (se 2 (by rfl) ⟨1198764, by rfl⟩ : syracuseStep 3196705 = 2397529) B2397529
theorem B2844449 : Blo 1262449 2844449 := bstep (se 2 (by rfl) ⟨1066668, by rfl⟩ : syracuseStep 2844449 = 2133337) B2133337
theorem B1894187 : Blo 1262449 1894187 := bstep (se 1 (by rfl) ⟨1420640, by rfl⟩ : syracuseStep 1894187 = 2841281) B2841281
theorem B2131771 : Blo 1262449 2131771 := bstep (se 1 (by rfl) ⟨1598828, by rfl⟩ : syracuseStep 2131771 = 3197657) B3197657
theorem B1263419 : Blo 1262449 1263419 := bstep (se 1 (by rfl) ⟨947564, by rfl⟩ : syracuseStep 1263419 = 1895129) B1895129
theorem B1894217 : Blo 1262449 1894217 := bstep (se 2 (by rfl) ⟨710331, by rfl⟩ : syracuseStep 1894217 = 1420663) B1420663
theorem B1263495 : Blo 1262449 1263495 := bstep (se 1 (by rfl) ⟨947621, by rfl⟩ : syracuseStep 1263495 = 1895243) B1895243
theorem B1263503 : Blo 1262449 1263503 := bstep (se 1 (by rfl) ⟨947627, by rfl⟩ : syracuseStep 1263503 = 1895255) B1895255
theorem B1894331 : Blo 1262449 1894331 := bstep (se 1 (by rfl) ⟨1420748, by rfl⟩ : syracuseStep 1894331 = 2841497) B2841497
theorem B1263547 : Blo 1262449 1263547 := bstep (se 1 (by rfl) ⟨947660, by rfl⟩ : syracuseStep 1263547 = 1895321) B1895321
theorem B2131913 : Blo 1262449 2131913 := bstep (se 2 (by rfl) ⟨799467, by rfl⟩ : syracuseStep 2131913 = 1598935) B1598935
theorem B7686109 : Blo 1262449 7686109 := bstep (se 3 (by rfl) ⟨1441145, by rfl⟩ : syracuseStep 7686109 = 2882291) B2882291
theorem B1894391 : Blo 1262449 1894391 := bstep (se 1 (by rfl) ⟨1420793, by rfl⟩ : syracuseStep 1894391 = 2841587) B2841587
theorem B1263623 : Blo 1262449 1263623 := bstep (se 1 (by rfl) ⟨947717, by rfl⟩ : syracuseStep 1263623 = 1895435) B1895435
theorem B1894415 : Blo 1262449 1894415 := bstep (se 1 (by rfl) ⟨1420811, by rfl⟩ : syracuseStep 1894415 = 2841623) B2841623
theorem B1263631 : Blo 1262449 1263631 := bstep (se 1 (by rfl) ⟨947723, by rfl⟩ : syracuseStep 1263631 = 1895447) B1895447
theorem B1894457 : Blo 1262449 1894457 := bstep (se 2 (by rfl) ⟨710421, by rfl⟩ : syracuseStep 1894457 = 1420843) B1420843
theorem B1263675 : Blo 1262449 1263675 := bstep (se 1 (by rfl) ⟨947756, by rfl⟩ : syracuseStep 1263675 = 1895513) B1895513
theorem B4261949 : Blo 1262449 4261949 := bstep (se 3 (by rfl) ⟨799115, by rfl⟩ : syracuseStep 4261949 = 1598231) B1598231
theorem B4048957 : Blo 1262449 4048957 := bstep (se 3 (by rfl) ⟨759179, by rfl⟩ : syracuseStep 4048957 = 1518359) B1518359
theorem B2844791 : Blo 1262449 2844791 := bstep (se 1 (by rfl) ⟨2133593, by rfl⟩ : syracuseStep 2844791 = 4267187) B4267187
theorem B5400695 : Blo 1262449 5400695 := bstep (se 1 (by rfl) ⟨4050521, by rfl⟩ : syracuseStep 5400695 = 8101043) B8101043
theorem B1894535 : Blo 1262449 1894535 := bstep (se 1 (by rfl) ⟨1420901, by rfl⟩ : syracuseStep 1894535 = 2841803) B2841803
theorem B1263751 : Blo 1262449 1263751 := bstep (se 1 (by rfl) ⟨947813, by rfl⟩ : syracuseStep 1263751 = 1895627) B1895627
theorem B1263759 : Blo 1262449 1263759 := bstep (se 1 (by rfl) ⟨947819, by rfl⟩ : syracuseStep 1263759 = 1895639) B1895639
theorem B1894571 : Blo 1262449 1894571 := bstep (se 1 (by rfl) ⟨1420928, by rfl⟩ : syracuseStep 1894571 = 2841857) B2841857
theorem B1263803 : Blo 1262449 1263803 := bstep (se 1 (by rfl) ⟨947852, by rfl⟩ : syracuseStep 1263803 = 1895705) B1895705
theorem B1894601 : Blo 1262449 1894601 := bstep (se 2 (by rfl) ⟨710475, by rfl⟩ : syracuseStep 1894601 = 1420951) B1420951
theorem B1263879 : Blo 1262449 1263879 := bstep (se 1 (by rfl) ⟨947909, by rfl⟩ : syracuseStep 1263879 = 1895819) B1895819
theorem B3598607 : Blo 1262449 3598607 := bstep (se 1 (by rfl) ⟨2698955, by rfl⟩ : syracuseStep 3598607 = 5397911) B5397911
theorem B1263887 : Blo 1262449 1263887 := bstep (se 1 (by rfl) ⟨947915, by rfl⟩ : syracuseStep 1263887 = 1895831) B1895831
theorem B2844971 : Blo 1262449 2844971 := bstep (se 1 (by rfl) ⟨2133728, by rfl⟩ : syracuseStep 2844971 = 4267457) B4267457
theorem B1894715 : Blo 1262449 1894715 := bstep (se 1 (by rfl) ⟨1421036, by rfl⟩ : syracuseStep 1894715 = 2842073) B2842073
theorem B1263931 : Blo 1262449 1263931 := bstep (se 1 (by rfl) ⟨947948, by rfl⟩ : syracuseStep 1263931 = 1895897) B1895897
theorem B3197303 : Blo 1262449 3197303 := bstep (se 1 (by rfl) ⟨2397977, by rfl⟩ : syracuseStep 3197303 = 4795955) B4795955
theorem B1894775 : Blo 1262449 1894775 := bstep (se 1 (by rfl) ⟨1421081, by rfl⟩ : syracuseStep 1894775 = 2842163) B2842163
theorem B1264007 : Blo 1262449 1264007 := bstep (se 1 (by rfl) ⟨948005, by rfl⟩ : syracuseStep 1264007 = 1896011) B1896011
theorem B1894799 : Blo 1262449 1894799 := bstep (se 1 (by rfl) ⟨1421099, by rfl⟩ : syracuseStep 1894799 = 2842199) B2842199
theorem B1264015 : Blo 1262449 1264015 := bstep (se 1 (by rfl) ⟨948011, by rfl⟩ : syracuseStep 1264015 = 1896023) B1896023
theorem B1894841 : Blo 1262449 1894841 := bstep (se 2 (by rfl) ⟨710565, by rfl⟩ : syracuseStep 1894841 = 1421131) B1421131
theorem B1264059 : Blo 1262449 1264059 := bstep (se 1 (by rfl) ⟨948044, by rfl⟩ : syracuseStep 1264059 = 1896089) B1896089
theorem B7195139 : Blo 1262449 7195139 := bstep (se 1 (by rfl) ⟨5396354, by rfl⟩ : syracuseStep 7195139 = 10792709) B10792709
theorem B1894919 : Blo 1262449 1894919 := bstep (se 1 (by rfl) ⟨1421189, by rfl⟩ : syracuseStep 1894919 = 2842379) B2842379
theorem B1264135 : Blo 1262449 1264135 := bstep (se 1 (by rfl) ⟨948101, by rfl⟩ : syracuseStep 1264135 = 1896203) B1896203
theorem B1264143 : Blo 1262449 1264143 := bstep (se 1 (by rfl) ⟨948107, by rfl⟩ : syracuseStep 1264143 = 1896215) B1896215
theorem B2918945 : Blo 1262449 2918945 := bstep (se 2 (by rfl) ⟨1094604, by rfl⟩ : syracuseStep 2918945 = 2189209) B2189209
theorem B1894955 : Blo 1262449 1894955 := bstep (se 1 (by rfl) ⟨1421216, by rfl⟩ : syracuseStep 1894955 = 2842433) B2842433
theorem B1518139 : Blo 1262449 1518139 := bstep (se 1 (by rfl) ⟨1138604, by rfl⟩ : syracuseStep 1518139 = 2277209) B2277209
theorem B1264187 : Blo 1262449 1264187 := bstep (se 1 (by rfl) ⟨948140, by rfl⟩ : syracuseStep 1264187 = 1896281) B1896281
theorem B1894985 : Blo 1262449 1894985 := bstep (se 2 (by rfl) ⟨710619, by rfl⟩ : syracuseStep 1894985 = 1421239) B1421239
theorem B2132615 : Blo 1262449 2132615 := bstep (se 1 (by rfl) ⟨1599461, by rfl⟩ : syracuseStep 2132615 = 3198923) B3198923
theorem B1264263 : Blo 1262449 1264263 := bstep (se 1 (by rfl) ⟨948197, by rfl⟩ : syracuseStep 1264263 = 1896395) B1896395
theorem B1264271 : Blo 1262449 1264271 := bstep (se 1 (by rfl) ⟨948203, by rfl⟩ : syracuseStep 1264271 = 1896407) B1896407
theorem B1895099 : Blo 1262449 1895099 := bstep (se 1 (by rfl) ⟨1421324, by rfl⟩ : syracuseStep 1895099 = 2842649) B2842649
theorem B1264315 : Blo 1262449 1264315 := bstep (se 1 (by rfl) ⟨948236, by rfl⟩ : syracuseStep 1264315 = 1896473) B1896473
theorem B1895159 : Blo 1262449 1895159 := bstep (se 1 (by rfl) ⟨1421369, by rfl⟩ : syracuseStep 1895159 = 2842739) B2842739
theorem B1264391 : Blo 1262449 1264391 := bstep (se 1 (by rfl) ⟨948293, by rfl⟩ : syracuseStep 1264391 = 1896587) B1896587
theorem B1895183 : Blo 1262449 1895183 := bstep (se 1 (by rfl) ⟨1421387, by rfl⟩ : syracuseStep 1895183 = 2842775) B2842775
theorem B1264399 : Blo 1262449 1264399 := bstep (se 1 (by rfl) ⟨948299, by rfl⟩ : syracuseStep 1264399 = 1896599) B1896599
theorem B9988913 : Blo 1262449 9988913 := bstep (se 2 (by rfl) ⟨3745842, by rfl⟩ : syracuseStep 9988913 = 7491685) B7491685
theorem B1895225 : Blo 1262449 1895225 := bstep (se 2 (by rfl) ⟨710709, by rfl⟩ : syracuseStep 1895225 = 1421419) B1421419
theorem B1264443 : Blo 1262449 1264443 := bstep (se 1 (by rfl) ⟨948332, by rfl⟩ : syracuseStep 1264443 = 1896665) B1896665
theorem B66497381 : Blo 1262449 66497381 := bstep (se 4 (by rfl) ⟨6234129, by rfl⟩ : syracuseStep 66497381 = 12468259) B12468259
theorem B4795271 : Blo 1262449 4795271 := bstep (se 1 (by rfl) ⟨3596453, by rfl⟩ : syracuseStep 4795271 = 7192907) B7192907
theorem B1895303 : Blo 1262449 1895303 := bstep (se 1 (by rfl) ⟨1421477, by rfl⟩ : syracuseStep 1895303 = 2842955) B2842955
theorem B1895339 : Blo 1262449 1895339 := bstep (se 1 (by rfl) ⟨1421504, by rfl⟩ : syracuseStep 1895339 = 2843009) B2843009
theorem B1895369 : Blo 1262449 1895369 := bstep (se 2 (by rfl) ⟨710763, by rfl⟩ : syracuseStep 1895369 = 1421527) B1421527
theorem B6392843 : Blo 1262449 6392843 := bstep (se 1 (by rfl) ⟨4794632, by rfl⟩ : syracuseStep 6392843 = 9589265) B9589265
theorem B1420303 : Blo 1262449 1420303 := bstep (se 1 (by rfl) ⟨1065227, by rfl⟩ : syracuseStep 1420303 = 2130455) B2130455
theorem B1895483 : Blo 1262449 1895483 := bstep (se 1 (by rfl) ⟨1421612, by rfl⟩ : syracuseStep 1895483 = 2843225) B2843225
theorem B27692119 : Blo 1262449 27692119 := bstep (se 1 (by rfl) ⟨20769089, by rfl⟩ : syracuseStep 27692119 = 41538179) B41538179
theorem B1895543 : Blo 1262449 1895543 := bstep (se 1 (by rfl) ⟨1421657, by rfl⟩ : syracuseStep 1895543 = 2843315) B2843315
theorem B1895567 : Blo 1262449 1895567 := bstep (se 1 (by rfl) ⟨1421675, by rfl⟩ : syracuseStep 1895567 = 2843351) B2843351
theorem B6393005 : Blo 1262449 6393005 := bstep (se 3 (by rfl) ⟨1198688, by rfl⟩ : syracuseStep 6393005 = 2397377) B2397377
theorem B1895609 : Blo 1262449 1895609 := bstep (se 2 (by rfl) ⟨710853, by rfl⟩ : syracuseStep 1895609 = 1421707) B1421707
theorem B5762249 : Blo 1262449 5762249 := bstep (se 2 (by rfl) ⟨2160843, by rfl⟩ : syracuseStep 5762249 = 4321687) B4321687
theorem B1895687 : Blo 1262449 1895687 := bstep (se 1 (by rfl) ⟨1421765, by rfl⟩ : syracuseStep 1895687 = 2843531) B2843531
theorem B2133263 : Blo 1262449 2133263 := bstep (se 1 (by rfl) ⟨1599947, by rfl⟩ : syracuseStep 2133263 = 3199895) B3199895
theorem B1895723 : Blo 1262449 1895723 := bstep (se 1 (by rfl) ⟨1421792, by rfl⟩ : syracuseStep 1895723 = 2843585) B2843585
theorem B3648827 : Blo 1262449 3648827 := bstep (se 1 (by rfl) ⟨2736620, by rfl⟩ : syracuseStep 3648827 = 5473241) B5473241
theorem B1895753 : Blo 1262449 1895753 := bstep (se 2 (by rfl) ⟨710907, by rfl⟩ : syracuseStep 1895753 = 1421815) B1421815
theorem B4550003 : Blo 1262449 4550003 := bstep (se 1 (by rfl) ⟨3412502, by rfl⟩ : syracuseStep 4550003 = 6825005) B6825005
theorem B4263353 : Blo 1262449 4263353 := bstep (se 2 (by rfl) ⟨1598757, by rfl⟩ : syracuseStep 4263353 = 3197515) B3197515
theorem B1895867 : Blo 1262449 1895867 := bstep (se 1 (by rfl) ⟨1421900, by rfl⟩ : syracuseStep 1895867 = 2843801) B2843801
theorem B1560055 : Blo 1262449 1560055 := bstep (se 1 (by rfl) ⟨1170041, by rfl⟩ : syracuseStep 1560055 = 2340083) B2340083
theorem B1895927 : Blo 1262449 1895927 := bstep (se 1 (by rfl) ⟨1421945, by rfl⟩ : syracuseStep 1895927 = 2843891) B2843891
theorem B21581315 : Blo 1262449 21581315 := bstep (se 1 (by rfl) ⟨16185986, by rfl⟩ : syracuseStep 21581315 = 32371973) B32371973
theorem B1420807 : Blo 1262449 1420807 := bstep (se 1 (by rfl) ⟨1065605, by rfl⟩ : syracuseStep 1420807 = 2131211) B2131211
theorem B1895951 : Blo 1262449 1895951 := bstep (se 1 (by rfl) ⟨1421963, by rfl⟩ : syracuseStep 1895951 = 2843927) B2843927
theorem B18214429 : Blo 1262449 18214429 := bstep (se 3 (by rfl) ⟨3415205, by rfl⟩ : syracuseStep 18214429 = 6830411) B6830411
theorem B1895993 : Blo 1262449 1895993 := bstep (se 2 (by rfl) ⟨710997, by rfl⟩ : syracuseStep 1895993 = 1421995) B1421995
theorem B3034759 : Blo 1262449 3034759 := bstep (se 1 (by rfl) ⟨2276069, by rfl⟩ : syracuseStep 3034759 = 4552139) B4552139
theorem B3198599 : Blo 1262449 3198599 := bstep (se 1 (by rfl) ⟨2398949, by rfl⟩ : syracuseStep 3198599 = 4797899) B4797899
theorem B1896071 : Blo 1262449 1896071 := bstep (se 1 (by rfl) ⟨1422053, by rfl⟩ : syracuseStep 1896071 = 2844107) B2844107
theorem B1896107 : Blo 1262449 1896107 := bstep (se 1 (by rfl) ⟨1422080, by rfl⟩ : syracuseStep 1896107 = 2844161) B2844161
theorem B1797817 : Blo 1262449 1797817 := bstep (se 2 (by rfl) ⟨674181, by rfl⟩ : syracuseStep 1797817 = 1348363) B1348363
theorem B3198649 : Blo 1262449 3198649 := bstep (se 2 (by rfl) ⟨1199493, by rfl⟩ : syracuseStep 3198649 = 2398987) B2398987
theorem B1420987 : Blo 1262449 1420987 := bstep (se 1 (by rfl) ⟨1065740, by rfl⟩ : syracuseStep 1420987 = 2131481) B2131481
theorem B1896137 : Blo 1262449 1896137 := bstep (se 2 (by rfl) ⟨711051, by rfl⟩ : syracuseStep 1896137 = 1422103) B1422103
theorem B1896251 : Blo 1262449 1896251 := bstep (se 1 (by rfl) ⟨1422188, by rfl⟩ : syracuseStep 1896251 = 2844377) B2844377
theorem B4050803 : Blo 1262449 4050803 := bstep (se 1 (by rfl) ⟨3038102, by rfl⟩ : syracuseStep 4050803 = 6076205) B6076205
theorem B1707895 : Blo 1262449 1707895 := bstep (se 1 (by rfl) ⟨1280921, by rfl⟩ : syracuseStep 1707895 = 2561843) B2561843
theorem B1896311 : Blo 1262449 1896311 := bstep (se 1 (by rfl) ⟨1422233, by rfl⟩ : syracuseStep 1896311 = 2844467) B2844467
theorem B3600247 : Blo 1262449 3600247 := bstep (se 1 (by rfl) ⟨2700185, by rfl⟩ : syracuseStep 3600247 = 5400371) B5400371
theorem B6483847 : Blo 1262449 6483847 := bstep (se 1 (by rfl) ⟨4862885, by rfl⟩ : syracuseStep 6483847 = 9725771) B9725771
theorem B1896335 : Blo 1262449 1896335 := bstep (se 1 (by rfl) ⟨1422251, by rfl⟩ : syracuseStep 1896335 = 2844503) B2844503
theorem B3600281 : Blo 1262449 3600281 := bstep (se 2 (by rfl) ⟨1350105, by rfl⟩ : syracuseStep 3600281 = 2700211) B2700211
theorem B1896377 : Blo 1262449 1896377 := bstep (se 2 (by rfl) ⟨711141, by rfl⟩ : syracuseStep 1896377 = 1422283) B1422283
theorem B1896455 : Blo 1262449 1896455 := bstep (se 1 (by rfl) ⟨1422341, by rfl⟩ : syracuseStep 1896455 = 2844683) B2844683
theorem B4263947 : Blo 1262449 4263947 := bstep (se 1 (by rfl) ⟨3197960, by rfl⟩ : syracuseStep 4263947 = 6395921) B6395921
theorem B5124107 : Blo 1262449 5124107 := bstep (se 1 (by rfl) ⟨3843080, by rfl⟩ : syracuseStep 5124107 = 7686161) B7686161
theorem B3600395 : Blo 1262449 3600395 := bstep (se 1 (by rfl) ⟨2700296, by rfl⟩ : syracuseStep 3600395 = 5400593) B5400593
theorem B9359383 : Blo 1262449 9359383 := bstep (se 1 (by rfl) ⟨7019537, by rfl⟩ : syracuseStep 9359383 = 14039075) B14039075
theorem B1921067 : Blo 1262449 1921067 := bstep (se 1 (by rfl) ⟨1440800, by rfl⟩ : syracuseStep 1921067 = 2881601) B2881601
theorem B1896491 : Blo 1262449 1896491 := bstep (se 1 (by rfl) ⟨1422368, by rfl⟩ : syracuseStep 1896491 = 2844737) B2844737
theorem B1896521 : Blo 1262449 1896521 := bstep (se 2 (by rfl) ⟨711195, by rfl⟩ : syracuseStep 1896521 = 1422391) B1422391
theorem B4264055 : Blo 1262449 4264055 := bstep (se 1 (by rfl) ⟨3198041, by rfl⟩ : syracuseStep 4264055 = 6396083) B6396083
theorem B1421455 : Blo 1262449 1421455 := bstep (se 1 (by rfl) ⟨1066091, by rfl⟩ : syracuseStep 1421455 = 2132183) B2132183
theorem B1896635 : Blo 1262449 1896635 := bstep (se 1 (by rfl) ⟨1422476, by rfl⟩ : syracuseStep 1896635 = 2844953) B2844953
theorem B1708295 : Blo 1262449 1708295 := bstep (se 1 (by rfl) ⟨1281221, by rfl⟩ : syracuseStep 1708295 = 2562443) B2562443
theorem B3199247 : Blo 1262449 3199247 := bstep (se 1 (by rfl) ⟨2399435, by rfl⟩ : syracuseStep 3199247 = 4798871) B4798871
theorem B2879803 : Blo 1262449 2879803 := bstep (se 1 (by rfl) ⟨2159852, by rfl⟩ : syracuseStep 2879803 = 4319705) B4319705
theorem B2699639 : Blo 1262449 2699639 := bstep (se 1 (by rfl) ⟨2024729, by rfl⟩ : syracuseStep 2699639 = 4049459) B4049459
theorem B11522449 : Blo 1262449 11522449 := bstep (se 2 (by rfl) ⟨4320918, by rfl⟩ : syracuseStep 11522449 = 8641837) B8641837
theorem B3035663 : Blo 1262449 3035663 := bstep (se 1 (by rfl) ⟨2276747, by rfl⟩ : syracuseStep 3035663 = 4553495) B4553495
theorem B1421959 : Blo 1262449 1421959 := bstep (se 1 (by rfl) ⟨1066469, by rfl⟩ : syracuseStep 1421959 = 2132939) B2132939
theorem B4264649 : Blo 1262449 4264649 := bstep (se 2 (by rfl) ⟨1599243, by rfl⟩ : syracuseStep 4264649 = 3198487) B3198487
theorem B6394625 : Blo 1262449 6394625 := bstep (se 2 (by rfl) ⟨2397984, by rfl⟩ : syracuseStep 6394625 = 4795969) B4795969
theorem B1422139 : Blo 1262449 1422139 := bstep (se 1 (by rfl) ⟨1066604, by rfl⟩ : syracuseStep 1422139 = 2133209) B2133209
theorem B2700091 : Blo 1262449 2700091 := bstep (se 1 (by rfl) ⟨2025068, by rfl⟩ : syracuseStep 2700091 = 4050137) B4050137
theorem B1799047 : Blo 1262449 1799047 := bstep (se 1 (by rfl) ⟨1349285, by rfl⟩ : syracuseStep 1799047 = 2698571) B2698571
theorem B6075281 : Blo 1262449 6075281 := bstep (se 2 (by rfl) ⟨2278230, by rfl⟩ : syracuseStep 6075281 = 4556461) B4556461
theorem B6656921 : Blo 1262449 6656921 := bstep (se 2 (by rfl) ⟨2496345, by rfl⟩ : syracuseStep 6656921 = 4992691) B4992691
theorem B13661081 : Blo 1262449 13661081 := bstep (se 2 (by rfl) ⟨5122905, by rfl⟩ : syracuseStep 13661081 = 10245811) B10245811
theorem B3199945 : Blo 1262449 3199945 := bstep (se 2 (by rfl) ⟨1199979, by rfl⟩ : syracuseStep 3199945 = 2399959) B2399959
theorem B8205259 : Blo 1262449 8205259 := bstep (se 1 (by rfl) ⟨6153944, by rfl⟩ : syracuseStep 8205259 = 12307889) B12307889
theorem B9598013 : Blo 1262449 9598013 := bstep (se 3 (by rfl) ⟨1799627, by rfl⟩ : syracuseStep 9598013 = 3599255) B3599255
theorem B3200087 : Blo 1262449 3200087 := bstep (se 1 (by rfl) ⟨2400065, by rfl⟩ : syracuseStep 3200087 = 4800131) B4800131
theorem B3413281 : Blo 1262449 3413281 := bstep (se 2 (by rfl) ⟨1279980, by rfl⟩ : syracuseStep 3413281 = 2559961) B2559961
theorem B2397575 : Blo 1262449 2397575 := bstep (se 1 (by rfl) ⟨1798181, by rfl⟩ : syracuseStep 2397575 = 3596363) B3596363
theorem B4265351 : Blo 1262449 4265351 := bstep (se 1 (by rfl) ⟨3199013, by rfl⟩ : syracuseStep 4265351 = 6398027) B6398027
theorem B9590237 : Blo 1262449 9590237 := bstep (se 3 (by rfl) ⟨1798169, by rfl⟩ : syracuseStep 9590237 = 3596339) B3596339
theorem B6829591 : Blo 1262449 6829591 := bstep (se 1 (by rfl) ⟨5122193, by rfl⟩ : syracuseStep 6829591 = 10244387) B10244387
theorem B5395997 : Blo 1262449 5395997 := bstep (se 3 (by rfl) ⟨1011749, by rfl⟩ : syracuseStep 5395997 = 2023499) B2023499
theorem B6395435 : Blo 1262449 6395435 := bstep (se 1 (by rfl) ⟨4796576, by rfl⟩ : syracuseStep 6395435 = 9593153) B9593153
theorem B4552253 : Blo 1262449 4552253 := bstep (se 3 (by rfl) ⟨853547, by rfl⟩ : syracuseStep 4552253 = 1707095) B1707095
theorem B14595661 : Blo 1262449 14595661 := bstep (se 3 (by rfl) ⟨2736686, by rfl⟩ : syracuseStep 14595661 = 5473373) B5473373
theorem B1799867 : Blo 1262449 1799867 := bstep (se 1 (by rfl) ⟨1349900, by rfl⟩ : syracuseStep 1799867 = 2699801) B2699801
theorem B4265729 : Blo 1262449 4265729 := bstep (se 2 (by rfl) ⟨1599648, by rfl⟩ : syracuseStep 4265729 = 3199297) B3199297
theorem B7190309 : Blo 1262449 7190309 := bstep (se 4 (by rfl) ⟨674091, by rfl⟩ : syracuseStep 7190309 = 1348183) B1348183
theorem B2398099 : Blo 1262449 2398099 := bstep (se 1 (by rfl) ⟨1798574, by rfl⟩ : syracuseStep 2398099 = 3597149) B3597149
theorem B29571095 : Blo 1262449 29571095 := bstep (se 1 (by rfl) ⟨22178321, by rfl⟩ : syracuseStep 29571095 = 44356643) B44356643
theorem B1800311 : Blo 1262449 1800311 := bstep (se 1 (by rfl) ⟨1350233, by rfl⟩ : syracuseStep 1800311 = 2700467) B2700467
theorem B2275463 : Blo 1262449 2275463 := bstep (se 1 (by rfl) ⟨1706597, by rfl⟩ : syracuseStep 2275463 = 3413195) B3413195
theorem B2840723 : Blo 1262449 2840723 := bstep (se 1 (by rfl) ⟨2130542, by rfl⟩ : syracuseStep 2840723 = 4261085) B4261085
theorem B2840777 : Blo 1262449 2840777 := bstep (se 2 (by rfl) ⟨1065291, by rfl⟩ : syracuseStep 2840777 = 2130583) B2130583
theorem B7190765 : Blo 1262449 7190765 := bstep (se 3 (by rfl) ⟨1348268, by rfl⟩ : syracuseStep 7190765 = 2696537) B2696537
theorem B6830351 : Blo 1262449 6830351 := bstep (se 1 (by rfl) ⟨5122763, by rfl⟩ : syracuseStep 6830351 = 10245527) B10245527
theorem B840636737 : Blo 1262449 840636737 := bstep (se 2 (by rfl) ⟨315238776, by rfl⟩ : syracuseStep 840636737 = 630477553) B630477553
theorem B3119513 : Blo 1262449 3119513 := bstep (se 2 (by rfl) ⟨1169817, by rfl⟩ : syracuseStep 3119513 = 2339635) B2339635
theorem B7297465 : Blo 1262449 7297465 := bstep (se 2 (by rfl) ⟨2736549, by rfl⟩ : syracuseStep 7297465 = 5473099) B5473099
theorem B3422753 : Blo 1262449 3422753 := bstep (se 2 (by rfl) ⟨1283532, by rfl⟩ : syracuseStep 3422753 = 2567065) B2567065
theorem B4266539 : Blo 1262449 4266539 := bstep (se 1 (by rfl) ⟨3199904, by rfl⟩ : syracuseStep 4266539 = 6399809) B6399809
theorem B3242767 : Blo 1262449 3242767 := bstep (se 1 (by rfl) ⟨2432075, by rfl⟩ : syracuseStep 3242767 = 4864151) B4864151
theorem B4045601 : Blo 1262449 4045601 := bstep (se 2 (by rfl) ⟨1517100, by rfl⟩ : syracuseStep 4045601 = 3034201) B3034201
theorem B6396731 : Blo 1262449 6396731 := bstep (se 1 (by rfl) ⟨4797548, by rfl⟩ : syracuseStep 6396731 = 9595097) B9595097
theorem B2841479 : Blo 1262449 2841479 := bstep (se 1 (by rfl) ⟨2131109, by rfl⟩ : syracuseStep 2841479 = 4262219) B4262219
theorem B7191449 : Blo 1262449 7191449 := bstep (se 2 (by rfl) ⟨2696793, by rfl⟩ : syracuseStep 7191449 = 5393587) B5393587
theorem B6396893 : Blo 1262449 6396893 := bstep (se 3 (by rfl) ⟨1199417, by rfl⟩ : syracuseStep 6396893 = 2398835) B2398835
theorem B2841659 : Blo 1262449 2841659 := bstep (se 1 (by rfl) ⟨2131244, by rfl⟩ : syracuseStep 2841659 = 4262489) B4262489
theorem B2399291 : Blo 1262449 2399291 := bstep (se 1 (by rfl) ⟨1799468, by rfl⟩ : syracuseStep 2399291 = 3598937) B3598937
theorem B2841785 : Blo 1262449 2841785 := bstep (se 2 (by rfl) ⟨1065669, by rfl⟩ : syracuseStep 2841785 = 2131339) B2131339
theorem B21576941 : Blo 1262449 21576941 := bstep (se 3 (by rfl) ⟨4045676, by rfl⟩ : syracuseStep 21576941 = 8091353) B8091353
theorem B6397217 : Blo 1262449 6397217 := bstep (se 2 (by rfl) ⟨2398956, by rfl⟩ : syracuseStep 6397217 = 4797913) B4797913
theorem B6069593 : Blo 1262449 6069593 := bstep (se 2 (by rfl) ⟨2276097, by rfl⟩ : syracuseStep 6069593 = 4552195) B4552195
theorem B12303875 : Blo 1262449 12303875 := bstep (se 1 (by rfl) ⟨9227906, by rfl⟩ : syracuseStep 12303875 = 18455813) B18455813
theorem B36953603 : Blo 1262449 36953603 := bstep (se 1 (by rfl) ⟨27715202, by rfl⟩ : syracuseStep 36953603 = 55430405) B55430405
theorem B2842127 : Blo 1262449 2842127 := bstep (se 1 (by rfl) ⟨2131595, by rfl⟩ : syracuseStep 2842127 = 4263191) B4263191
theorem B2842145 : Blo 1262449 2842145 := bstep (se 2 (by rfl) ⟨1065804, by rfl⟩ : syracuseStep 2842145 = 2131609) B2131609
theorem B2399777 : Blo 1262449 2399777 := bstep (se 2 (by rfl) ⟨899916, by rfl⟩ : syracuseStep 2399777 = 1799833) B1799833
theorem B8093303 : Blo 1262449 8093303 := bstep (se 1 (by rfl) ⟨6069977, by rfl⟩ : syracuseStep 8093303 = 12139955) B12139955
theorem B2023211 : Blo 1262449 2023211 := bstep (se 1 (by rfl) ⟨1517408, by rfl⟩ : syracuseStep 2023211 = 3034817) B3034817
theorem B2400043 : Blo 1262449 2400043 := bstep (se 1 (by rfl) ⟨1800032, by rfl⟩ : syracuseStep 2400043 = 3600065) B3600065
theorem B3596147 : Blo 1262449 3596147 := bstep (se 1 (by rfl) ⟨2697110, by rfl⟩ : syracuseStep 3596147 = 5394221) B5394221
theorem B2842487 : Blo 1262449 2842487 := bstep (se 1 (by rfl) ⟨2131865, by rfl⟩ : syracuseStep 2842487 = 4263731) B4263731
theorem B7200697 : Blo 1262449 7200697 := bstep (se 2 (by rfl) ⟨2700261, by rfl⟩ : syracuseStep 7200697 = 5400523) B5400523
theorem B6922205 : Blo 1262449 6922205 := bstep (se 3 (by rfl) ⟨1297913, by rfl⟩ : syracuseStep 6922205 = 2595827) B2595827
theorem B2842631 : Blo 1262449 2842631 := bstep (se 1 (by rfl) ⟨2131973, by rfl⟩ : syracuseStep 2842631 = 4263947) B4263947
theorem B2400263 : Blo 1262449 2400263 := bstep (se 1 (by rfl) ⟨1800197, by rfl⟩ : syracuseStep 2400263 = 3600395) B3600395
theorem B13664285 : Blo 1262449 13664285 := bstep (se 3 (by rfl) ⟨2562053, by rfl⟩ : syracuseStep 13664285 = 5124107) B5124107
theorem B2842703 : Blo 1262449 2842703 := bstep (se 1 (by rfl) ⟨2132027, by rfl⟩ : syracuseStep 2842703 = 4264055) B4264055
theorem B4800829 : Blo 1262449 4800829 := bstep (se 3 (by rfl) ⟨900155, by rfl⟩ : syracuseStep 4800829 = 1800311) B1800311
theorem B21594437 : Blo 1262449 21594437 := bstep (se 4 (by rfl) ⟨2024478, by rfl⟩ : syracuseStep 21594437 = 4048957) B4048957
theorem B2023775 : Blo 1262449 2023775 := bstep (se 1 (by rfl) ⟨1517831, by rfl⟩ : syracuseStep 2023775 = 3035663) B3035663
theorem B2843099 : Blo 1262449 2843099 := bstep (se 1 (by rfl) ⟨2132324, by rfl⟩ : syracuseStep 2843099 = 4264649) B4264649
theorem B17302025 : Blo 1262449 17302025 := bstep (se 2 (by rfl) ⟨6488259, by rfl⟩ : syracuseStep 17302025 = 12976519) B12976519
theorem B4555453 : Blo 1262449 4555453 := bstep (se 3 (by rfl) ⟨854147, by rfl⟩ : syracuseStep 4555453 = 1708295) B1708295
theorem B6398675 : Blo 1262449 6398675 := bstep (se 1 (by rfl) ⟨4799006, by rfl⟩ : syracuseStep 6398675 = 9598013) B9598013
theorem B2024185 : Blo 1262449 2024185 := bstep (se 2 (by rfl) ⟨759069, by rfl⟩ : syracuseStep 2024185 = 1518139) B1518139
theorem B1262459 : Blo 1262449 1262459 := bstep (se 1 (by rfl) ⟨946844, by rfl⟩ : syracuseStep 1262459 = 1893689) B1893689
theorem B1262511 : Blo 1262449 1262511 := bstep (se 1 (by rfl) ⟨946883, by rfl⟩ : syracuseStep 1262511 = 1893767) B1893767
theorem B1598383 : Blo 1262449 1598383 := bstep (se 1 (by rfl) ⟨1198787, by rfl⟩ : syracuseStep 1598383 = 2397575) B2397575
theorem B2843567 : Blo 1262449 2843567 := bstep (se 1 (by rfl) ⟨2132675, by rfl⟩ : syracuseStep 2843567 = 4265351) B4265351
theorem B1262535 : Blo 1262449 1262535 := bstep (se 1 (by rfl) ⟨946901, by rfl⟩ : syracuseStep 1262535 = 1893803) B1893803
theorem B1262555 : Blo 1262449 1262555 := bstep (se 1 (by rfl) ⟨946916, by rfl⟩ : syracuseStep 1262555 = 1893833) B1893833
theorem B2130907 : Blo 1262449 2130907 := bstep (se 1 (by rfl) ⟨1598180, by rfl⟩ : syracuseStep 2130907 = 3196361) B3196361
theorem B3597331 : Blo 1262449 3597331 := bstep (se 1 (by rfl) ⟨2697998, by rfl⟩ : syracuseStep 3597331 = 5395997) B5395997
theorem B1262631 : Blo 1262449 1262631 := bstep (se 1 (by rfl) ⟨946973, by rfl⟩ : syracuseStep 1262631 = 1893947) B1893947
theorem B1262671 : Blo 1262449 1262671 := bstep (se 1 (by rfl) ⟨947003, by rfl⟩ : syracuseStep 1262671 = 1894007) B1894007
theorem B1262687 : Blo 1262449 1262687 := bstep (se 1 (by rfl) ⟨947015, by rfl⟩ : syracuseStep 1262687 = 1894031) B1894031
theorem B1262715 : Blo 1262449 1262715 := bstep (se 1 (by rfl) ⟨947036, by rfl⟩ : syracuseStep 1262715 = 1894073) B1894073
theorem B2843819 : Blo 1262449 2843819 := bstep (se 1 (by rfl) ⟨2132864, by rfl⟩ : syracuseStep 2843819 = 4265729) B4265729
theorem B1262767 : Blo 1262449 1262767 := bstep (se 1 (by rfl) ⟨947075, by rfl⟩ : syracuseStep 1262767 = 1894151) B1894151
theorem B4793539 : Blo 1262449 4793539 := bstep (se 1 (by rfl) ⟨3595154, by rfl⟩ : syracuseStep 4793539 = 7190309) B7190309
theorem B1262791 : Blo 1262449 1262791 := bstep (se 1 (by rfl) ⟨947093, by rfl⟩ : syracuseStep 1262791 = 1894187) B1894187
theorem B1262811 : Blo 1262449 1262811 := bstep (se 1 (by rfl) ⟨947108, by rfl⟩ : syracuseStep 1262811 = 1894217) B1894217
theorem B1262887 : Blo 1262449 1262887 := bstep (se 1 (by rfl) ⟨947165, by rfl⟩ : syracuseStep 1262887 = 1894331) B1894331
theorem B1262927 : Blo 1262449 1262927 := bstep (se 1 (by rfl) ⟨947195, by rfl⟩ : syracuseStep 1262927 = 1894391) B1894391
theorem B1262943 : Blo 1262449 1262943 := bstep (se 1 (by rfl) ⟨947207, by rfl⟩ : syracuseStep 1262943 = 1894415) B1894415
theorem B1893737 : Blo 1262449 1893737 := bstep (se 2 (by rfl) ⟨710151, by rfl⟩ : syracuseStep 1893737 = 1420303) B1420303
theorem B1262971 : Blo 1262449 1262971 := bstep (se 1 (by rfl) ⟨947228, by rfl⟩ : syracuseStep 1262971 = 1894457) B1894457
theorem B1516975 : Blo 1262449 1516975 := bstep (se 1 (by rfl) ⟨1137731, by rfl⟩ : syracuseStep 1516975 = 2275463) B2275463
theorem B1263023 : Blo 1262449 1263023 := bstep (se 1 (by rfl) ⟨947267, by rfl⟩ : syracuseStep 1263023 = 1894535) B1894535
theorem B1893815 : Blo 1262449 1893815 := bstep (se 1 (by rfl) ⟨1420361, by rfl⟩ : syracuseStep 1893815 = 2840723) B2840723
theorem B1263047 : Blo 1262449 1263047 := bstep (se 1 (by rfl) ⟨947285, by rfl⟩ : syracuseStep 1263047 = 1894571) B1894571
theorem B36922825 : Blo 1262449 36922825 := bstep (se 2 (by rfl) ⟨13846059, by rfl⟩ : syracuseStep 36922825 = 27692119) B27692119
theorem B1893851 : Blo 1262449 1893851 := bstep (se 1 (by rfl) ⟨1420388, by rfl⟩ : syracuseStep 1893851 = 2840777) B2840777
theorem B1263067 : Blo 1262449 1263067 := bstep (se 1 (by rfl) ⟨947300, by rfl⟩ : syracuseStep 1263067 = 1894601) B1894601
theorem B4793843 : Blo 1262449 4793843 := bstep (se 1 (by rfl) ⟨3595382, by rfl⟩ : syracuseStep 4793843 = 7190765) B7190765
theorem B4261409 : Blo 1262449 4261409 := bstep (se 2 (by rfl) ⟨1598028, by rfl⟩ : syracuseStep 4261409 = 3196057) B3196057
theorem B1263143 : Blo 1262449 1263143 := bstep (se 1 (by rfl) ⟨947357, by rfl⟩ : syracuseStep 1263143 = 1894715) B1894715
theorem B560424491 : Blo 1262449 560424491 := bstep (se 1 (by rfl) ⟨420318368, by rfl⟩ : syracuseStep 560424491 = 840636737) B840636737
theorem B2131535 : Blo 1262449 2131535 := bstep (se 1 (by rfl) ⟨1598651, by rfl⟩ : syracuseStep 2131535 = 3197303) B3197303
theorem B1263183 : Blo 1262449 1263183 := bstep (se 1 (by rfl) ⟨947387, by rfl⟩ : syracuseStep 1263183 = 1894775) B1894775
theorem B1263199 : Blo 1262449 1263199 := bstep (se 1 (by rfl) ⟨947399, by rfl⟩ : syracuseStep 1263199 = 1894799) B1894799
theorem B1263227 : Blo 1262449 1263227 := bstep (se 1 (by rfl) ⟨947420, by rfl⟩ : syracuseStep 1263227 = 1894841) B1894841
theorem B1263279 : Blo 1262449 1263279 := bstep (se 1 (by rfl) ⟨947459, by rfl⟩ : syracuseStep 1263279 = 1894919) B1894919
theorem B1263303 : Blo 1262449 1263303 := bstep (se 1 (by rfl) ⟨947477, by rfl⟩ : syracuseStep 1263303 = 1894955) B1894955
theorem B2844359 : Blo 1262449 2844359 := bstep (se 1 (by rfl) ⟨2133269, by rfl⟩ : syracuseStep 2844359 = 4266539) B4266539
theorem B1263323 : Blo 1262449 1263323 := bstep (se 1 (by rfl) ⟨947492, by rfl⟩ : syracuseStep 1263323 = 1894985) B1894985
theorem B4261625 : Blo 1262449 4261625 := bstep (se 2 (by rfl) ⟨1598109, by rfl⟩ : syracuseStep 4261625 = 3196219) B3196219
theorem B14780153 : Blo 1262449 14780153 := bstep (se 2 (by rfl) ⟨5542557, by rfl⟩ : syracuseStep 14780153 = 11085115) B11085115
theorem B1263399 : Blo 1262449 1263399 := bstep (se 1 (by rfl) ⟨947549, by rfl⟩ : syracuseStep 1263399 = 1895099) B1895099
theorem B1263439 : Blo 1262449 1263439 := bstep (se 1 (by rfl) ⟨947579, by rfl⟩ : syracuseStep 1263439 = 1895159) B1895159
theorem B1263455 : Blo 1262449 1263455 := bstep (se 1 (by rfl) ⟨947591, by rfl⟩ : syracuseStep 1263455 = 1895183) B1895183
theorem B2697067 : Blo 1262449 2697067 := bstep (se 1 (by rfl) ⟨2022800, by rfl⟩ : syracuseStep 2697067 = 4045601) B4045601
theorem B1263483 : Blo 1262449 1263483 := bstep (se 1 (by rfl) ⟨947612, by rfl⟩ : syracuseStep 1263483 = 1895225) B1895225
theorem B1894319 : Blo 1262449 1894319 := bstep (se 1 (by rfl) ⟨1420739, by rfl⟩ : syracuseStep 1894319 = 2841479) B2841479
theorem B3196847 : Blo 1262449 3196847 := bstep (se 1 (by rfl) ⟨2397635, by rfl⟩ : syracuseStep 3196847 = 4795271) B4795271
theorem B1263535 : Blo 1262449 1263535 := bstep (se 1 (by rfl) ⟨947651, by rfl⟩ : syracuseStep 1263535 = 1895303) B1895303
theorem B4794299 : Blo 1262449 4794299 := bstep (se 1 (by rfl) ⟨3595724, by rfl⟩ : syracuseStep 4794299 = 7191449) B7191449
theorem B1263559 : Blo 1262449 1263559 := bstep (se 1 (by rfl) ⟨947669, by rfl⟩ : syracuseStep 1263559 = 1895339) B1895339
theorem B1263579 : Blo 1262449 1263579 := bstep (se 1 (by rfl) ⟨947684, by rfl⟩ : syracuseStep 1263579 = 1895369) B1895369
theorem B4261895 : Blo 1262449 4261895 := bstep (se 1 (by rfl) ⟨3196421, by rfl⟩ : syracuseStep 4261895 = 6392843) B6392843
theorem B1894409 : Blo 1262449 1894409 := bstep (se 2 (by rfl) ⟨710403, by rfl⟩ : syracuseStep 1894409 = 1420807) B1420807
theorem B1894439 : Blo 1262449 1894439 := bstep (se 1 (by rfl) ⟨1420829, by rfl⟩ : syracuseStep 1894439 = 2841659) B2841659
theorem B1263655 : Blo 1262449 1263655 := bstep (se 1 (by rfl) ⟨947741, by rfl⟩ : syracuseStep 1263655 = 1895483) B1895483
theorem B1599527 : Blo 1262449 1599527 := bstep (se 1 (by rfl) ⟨1199645, by rfl⟩ : syracuseStep 1599527 = 2399291) B2399291
theorem B1263695 : Blo 1262449 1263695 := bstep (se 1 (by rfl) ⟨947771, by rfl⟩ : syracuseStep 1263695 = 1895543) B1895543
theorem B1263711 : Blo 1262449 1263711 := bstep (se 1 (by rfl) ⟨947783, by rfl⟩ : syracuseStep 1263711 = 1895567) B1895567
theorem B4262003 : Blo 1262449 4262003 := bstep (se 1 (by rfl) ⟨3196502, by rfl⟩ : syracuseStep 4262003 = 6393005) B6393005
theorem B1894523 : Blo 1262449 1894523 := bstep (se 1 (by rfl) ⟨1420892, by rfl⟩ : syracuseStep 1894523 = 2841785) B2841785
theorem B1263739 : Blo 1262449 1263739 := bstep (se 1 (by rfl) ⟨947804, by rfl⟩ : syracuseStep 1263739 = 1895609) B1895609
theorem B1263791 : Blo 1262449 1263791 := bstep (se 1 (by rfl) ⟨947843, by rfl⟩ : syracuseStep 1263791 = 1895687) B1895687
theorem B1263815 : Blo 1262449 1263815 := bstep (se 1 (by rfl) ⟨947861, by rfl⟩ : syracuseStep 1263815 = 1895723) B1895723
theorem B1263835 : Blo 1262449 1263835 := bstep (se 1 (by rfl) ⟨947876, by rfl⟩ : syracuseStep 1263835 = 1895753) B1895753
theorem B3033335 : Blo 1262449 3033335 := bstep (se 1 (by rfl) ⟨2275001, by rfl⟩ : syracuseStep 3033335 = 4550003) B4550003
theorem B1894649 : Blo 1262449 1894649 := bstep (se 2 (by rfl) ⟨710493, by rfl⟩ : syracuseStep 1894649 = 1420987) B1420987
theorem B1263911 : Blo 1262449 1263911 := bstep (se 1 (by rfl) ⟨947933, by rfl⟩ : syracuseStep 1263911 = 1895867) B1895867
theorem B1263951 : Blo 1262449 1263951 := bstep (se 1 (by rfl) ⟨947963, by rfl⟩ : syracuseStep 1263951 = 1895927) B1895927
theorem B8202583 : Blo 1262449 8202583 := bstep (se 1 (by rfl) ⟨6151937, by rfl⟩ : syracuseStep 8202583 = 12303875) B12303875
theorem B14387543 : Blo 1262449 14387543 := bstep (se 1 (by rfl) ⟨10790657, by rfl⟩ : syracuseStep 14387543 = 21581315) B21581315
theorem B24635735 : Blo 1262449 24635735 := bstep (se 1 (by rfl) ⟨18476801, by rfl⟩ : syracuseStep 24635735 = 36953603) B36953603
theorem B1894751 : Blo 1262449 1894751 := bstep (se 1 (by rfl) ⟨1421063, by rfl⟩ : syracuseStep 1894751 = 2842127) B2842127
theorem B1263967 : Blo 1262449 1263967 := bstep (se 1 (by rfl) ⟨947975, by rfl⟩ : syracuseStep 1263967 = 1895951) B1895951
theorem B1894763 : Blo 1262449 1894763 := bstep (se 1 (by rfl) ⟨1421072, by rfl⟩ : syracuseStep 1894763 = 2842145) B2842145
theorem B1599851 : Blo 1262449 1599851 := bstep (se 1 (by rfl) ⟨1199888, by rfl⟩ : syracuseStep 1599851 = 2399777) B2399777
theorem B1263995 : Blo 1262449 1263995 := bstep (se 1 (by rfl) ⟨947996, by rfl⟩ : syracuseStep 1263995 = 1895993) B1895993
theorem B4262273 : Blo 1262449 4262273 := bstep (se 2 (by rfl) ⟨1598352, by rfl⟩ : syracuseStep 4262273 = 3196705) B3196705
theorem B2132399 : Blo 1262449 2132399 := bstep (se 1 (by rfl) ⟨1599299, by rfl⟩ : syracuseStep 2132399 = 3198599) B3198599
theorem B1264047 : Blo 1262449 1264047 := bstep (se 1 (by rfl) ⟨948035, by rfl⟩ : syracuseStep 1264047 = 1896071) B1896071
theorem B1264071 : Blo 1262449 1264071 := bstep (se 1 (by rfl) ⟨948053, by rfl⟩ : syracuseStep 1264071 = 1896107) B1896107
theorem B1264091 : Blo 1262449 1264091 := bstep (se 1 (by rfl) ⟨948068, by rfl⟩ : syracuseStep 1264091 = 1896137) B1896137
theorem B8645129 : Blo 1262449 8645129 := bstep (se 2 (by rfl) ⟨3241923, by rfl⟩ : syracuseStep 8645129 = 6483847) B6483847
theorem B3197465 : Blo 1262449 3197465 := bstep (se 2 (by rfl) ⟨1199049, by rfl⟩ : syracuseStep 3197465 = 2398099) B2398099
theorem B1264167 : Blo 1262449 1264167 := bstep (se 1 (by rfl) ⟨948125, by rfl⟩ : syracuseStep 1264167 = 1896251) B1896251
theorem B1894991 : Blo 1262449 1894991 := bstep (se 1 (by rfl) ⟨1421243, by rfl⟩ : syracuseStep 1894991 = 2842487) B2842487
theorem B1264207 : Blo 1262449 1264207 := bstep (se 1 (by rfl) ⟨948155, by rfl⟩ : syracuseStep 1264207 = 1896311) B1896311
theorem B1264223 : Blo 1262449 1264223 := bstep (se 1 (by rfl) ⟨948167, by rfl⟩ : syracuseStep 1264223 = 1896335) B1896335
theorem B1264251 : Blo 1262449 1264251 := bstep (se 1 (by rfl) ⟨948188, by rfl⟩ : syracuseStep 1264251 = 1896377) B1896377
theorem B4614803 : Blo 1262449 4614803 := bstep (se 1 (by rfl) ⟨3461102, by rfl⟩ : syracuseStep 4614803 = 6922205) B6922205
theorem B1264303 : Blo 1262449 1264303 := bstep (se 1 (by rfl) ⟨948227, by rfl⟩ : syracuseStep 1264303 = 1896455) B1896455
theorem B1895111 : Blo 1262449 1895111 := bstep (se 1 (by rfl) ⟨1421333, by rfl⟩ : syracuseStep 1895111 = 2842667) B2842667
theorem B1280711 : Blo 1262449 1280711 := bstep (se 1 (by rfl) ⟨960533, by rfl⟩ : syracuseStep 1280711 = 1921067) B1921067
theorem B12479177 : Blo 1262449 12479177 := bstep (se 2 (by rfl) ⟨4679691, by rfl⟩ : syracuseStep 12479177 = 9359383) B9359383
theorem B1264327 : Blo 1262449 1264327 := bstep (se 1 (by rfl) ⟨948245, by rfl⟩ : syracuseStep 1264327 = 1896491) B1896491
theorem B3599063 : Blo 1262449 3599063 := bstep (se 1 (by rfl) ⟨2699297, by rfl⟩ : syracuseStep 3599063 = 5398595) B5398595
theorem B1264347 : Blo 1262449 1264347 := bstep (se 1 (by rfl) ⟨948260, by rfl⟩ : syracuseStep 1264347 = 1896521) B1896521
theorem B1264423 : Blo 1262449 1264423 := bstep (se 1 (by rfl) ⟨948317, by rfl⟩ : syracuseStep 1264423 = 1896635) B1896635
theorem B2132831 : Blo 1262449 2132831 := bstep (se 1 (by rfl) ⟨1599623, by rfl⟩ : syracuseStep 2132831 = 3199247) B3199247
theorem B1895273 : Blo 1262449 1895273 := bstep (se 2 (by rfl) ⟨710727, by rfl⟩ : syracuseStep 1895273 = 1421455) B1421455
theorem B3599279 : Blo 1262449 3599279 := bstep (se 1 (by rfl) ⟨2699459, by rfl⟩ : syracuseStep 3599279 = 5398919) B5398919
theorem B6400943 : Blo 1262449 6400943 := bstep (se 1 (by rfl) ⟨4800707, by rfl⟩ : syracuseStep 6400943 = 9601415) B9601415
theorem B1895351 : Blo 1262449 1895351 := bstep (se 1 (by rfl) ⟨1421513, by rfl⟩ : syracuseStep 1895351 = 2843027) B2843027
theorem B1895387 : Blo 1262449 1895387 := bstep (se 1 (by rfl) ⟨1421540, by rfl⟩ : syracuseStep 1895387 = 2843081) B2843081
theorem B4926545 : Blo 1262449 4926545 := bstep (se 2 (by rfl) ⟨1847454, by rfl⟩ : syracuseStep 4926545 = 3694909) B3694909
theorem B1420411 : Blo 1262449 1420411 := bstep (se 1 (by rfl) ⟨1065308, by rfl⟩ : syracuseStep 1420411 = 2130617) B2130617
theorem B4263083 : Blo 1262449 4263083 := bstep (se 1 (by rfl) ⟨3197312, by rfl⟩ : syracuseStep 4263083 = 6394625) B6394625
theorem B15363265 : Blo 1262449 15363265 := bstep (se 2 (by rfl) ⟨5761224, by rfl⟩ : syracuseStep 15363265 = 11522449) B11522449
theorem B21064997 : Blo 1262449 21064997 := bstep (se 4 (by rfl) ⟨1974843, by rfl⟩ : syracuseStep 21064997 = 3949687) B3949687
theorem B1518955 : Blo 1262449 1518955 := bstep (se 1 (by rfl) ⟨1139216, by rfl⟩ : syracuseStep 1518955 = 2278433) B2278433
theorem B2133391 : Blo 1262449 2133391 := bstep (se 1 (by rfl) ⟨1600043, by rfl⟩ : syracuseStep 2133391 = 3200087) B3200087
theorem B1895855 : Blo 1262449 1895855 := bstep (se 1 (by rfl) ⟨1421891, by rfl⟩ : syracuseStep 1895855 = 2843783) B2843783
theorem B1895945 : Blo 1262449 1895945 := bstep (se 2 (by rfl) ⟨710979, by rfl⟩ : syracuseStep 1895945 = 1421959) B1421959
theorem B1895975 : Blo 1262449 1895975 := bstep (se 1 (by rfl) ⟨1421981, by rfl⟩ : syracuseStep 1895975 = 2843963) B2843963
theorem B1420879 : Blo 1262449 1420879 := bstep (se 1 (by rfl) ⟨1065659, by rfl⟩ : syracuseStep 1420879 = 2131319) B2131319
theorem B29568635 : Blo 1262449 29568635 := bstep (se 1 (by rfl) ⟨22176476, by rfl⟩ : syracuseStep 29568635 = 44352953) B44352953
theorem B1896059 : Blo 1262449 1896059 := bstep (se 1 (by rfl) ⟨1422044, by rfl⟩ : syracuseStep 1896059 = 2844089) B2844089
theorem B10800773 : Blo 1262449 10800773 := bstep (se 4 (by rfl) ⟨1012572, by rfl⟩ : syracuseStep 10800773 = 2025145) B2025145
theorem B9596555 : Blo 1262449 9596555 := bstep (se 1 (by rfl) ⟨7197416, by rfl⟩ : syracuseStep 9596555 = 14394833) B14394833
theorem B6393491 : Blo 1262449 6393491 := bstep (se 1 (by rfl) ⟨4795118, by rfl⟩ : syracuseStep 6393491 = 9590237) B9590237
theorem B4263623 : Blo 1262449 4263623 := bstep (se 1 (by rfl) ⟨3197717, by rfl⟩ : syracuseStep 4263623 = 6395435) B6395435
theorem B3034835 : Blo 1262449 3034835 := bstep (se 1 (by rfl) ⟨2276126, by rfl⟩ : syracuseStep 3034835 = 4552253) B4552253
theorem B8089303 : Blo 1262449 8089303 := bstep (se 1 (by rfl) ⟨6066977, by rfl⟩ : syracuseStep 8089303 = 12133955) B12133955
theorem B8318701 : Blo 1262449 8318701 := bstep (se 3 (by rfl) ⟨1559756, by rfl⟩ : syracuseStep 8318701 = 3119513) B3119513
theorem B1896185 : Blo 1262449 1896185 := bstep (se 2 (by rfl) ⟨711069, by rfl⟩ : syracuseStep 1896185 = 1422139) B1422139
theorem B3600121 : Blo 1262449 3600121 := bstep (se 2 (by rfl) ⟨1350045, by rfl⟩ : syracuseStep 3600121 = 2700091) B2700091
theorem B1896287 : Blo 1262449 1896287 := bstep (se 1 (by rfl) ⟨1422215, by rfl⟩ : syracuseStep 1896287 = 2844431) B2844431
theorem B1896299 : Blo 1262449 1896299 := bstep (se 1 (by rfl) ⟨1422224, by rfl⟩ : syracuseStep 1896299 = 2844449) B2844449
theorem B10940345 : Blo 1262449 10940345 := bstep (se 2 (by rfl) ⟨4102629, by rfl⟩ : syracuseStep 10940345 = 8205259) B8205259
theorem B1421275 : Blo 1262449 1421275 := bstep (se 1 (by rfl) ⟨1065956, by rfl⟩ : syracuseStep 1421275 = 2131913) B2131913
theorem B19714063 : Blo 1262449 19714063 := bstep (se 1 (by rfl) ⟨14785547, by rfl⟩ : syracuseStep 19714063 = 29571095) B29571095
theorem B1896527 : Blo 1262449 1896527 := bstep (se 1 (by rfl) ⟨1422395, by rfl⟩ : syracuseStep 1896527 = 2844791) B2844791
theorem B3600463 : Blo 1262449 3600463 := bstep (se 1 (by rfl) ⟨2700347, by rfl⟩ : syracuseStep 3600463 = 5400695) B5400695
theorem B1896647 : Blo 1262449 1896647 := bstep (se 1 (by rfl) ⟨1422485, by rfl⟩ : syracuseStep 1896647 = 2844971) B2844971
theorem B4796759 : Blo 1262449 4796759 := bstep (se 1 (by rfl) ⟨3597569, by rfl⟩ : syracuseStep 4796759 = 7195139) B7195139
theorem B1945963 : Blo 1262449 1945963 := bstep (se 1 (by rfl) ⟨1459472, by rfl⟩ : syracuseStep 1945963 = 2918945) B2918945
theorem B2281835 : Blo 1262449 2281835 := bstep (se 1 (by rfl) ⟨1711376, by rfl⟩ : syracuseStep 2281835 = 3422753) B3422753
theorem B4551041 : Blo 1262449 4551041 := bstep (se 2 (by rfl) ⟨1706640, by rfl⟩ : syracuseStep 4551041 = 3413281) B3413281
theorem B1421743 : Blo 1262449 1421743 := bstep (se 1 (by rfl) ⟨1066307, by rfl⟩ : syracuseStep 1421743 = 2132615) B2132615
theorem B4264487 : Blo 1262449 4264487 := bstep (se 1 (by rfl) ⟨3198365, by rfl⟩ : syracuseStep 4264487 = 6396731) B6396731
theorem B44331587 : Blo 1262449 44331587 := bstep (se 1 (by rfl) ⟨33248690, by rfl⟩ : syracuseStep 44331587 = 66497381) B66497381
theorem B4264595 : Blo 1262449 4264595 := bstep (se 1 (by rfl) ⟨3198446, by rfl⟩ : syracuseStep 4264595 = 6396893) B6396893
theorem B9106121 : Blo 1262449 9106121 := bstep (se 2 (by rfl) ⟨3414795, by rfl⟩ : syracuseStep 9106121 = 6829591) B6829591
theorem B24285905 : Blo 1262449 24285905 := bstep (se 2 (by rfl) ⟨9107214, by rfl⟩ : syracuseStep 24285905 = 18214429) B18214429
theorem B19460881 : Blo 1262449 19460881 := bstep (se 2 (by rfl) ⟨7297830, by rfl⟩ : syracuseStep 19460881 = 14595661) B14595661
theorem B1422175 : Blo 1262449 1422175 := bstep (se 1 (by rfl) ⟨1066631, by rfl⟩ : syracuseStep 1422175 = 2133263) B2133263
theorem B4264811 : Blo 1262449 4264811 := bstep (se 1 (by rfl) ⟨3198608, by rfl⟩ : syracuseStep 4264811 = 6397217) B6397217
theorem B2397089 : Blo 1262449 2397089 := bstep (se 2 (by rfl) ⟨898908, by rfl⟩ : syracuseStep 2397089 = 1797817) B1797817
theorem B4264865 : Blo 1262449 4264865 := bstep (se 2 (by rfl) ⟨1599324, by rfl⟩ : syracuseStep 4264865 = 3198649) B3198649
theorem B16200749 : Blo 1262449 16200749 := bstep (se 3 (by rfl) ⟨3037640, by rfl⟩ : syracuseStep 16200749 = 6075281) B6075281
theorem B3200057 : Blo 1262449 3200057 := bstep (se 2 (by rfl) ⟨1200021, by rfl⟩ : syracuseStep 3200057 = 2400043) B2400043
theorem B5395535 : Blo 1262449 5395535 := bstep (se 1 (by rfl) ⟨4046651, by rfl⟩ : syracuseStep 5395535 = 8093303) B8093303
theorem B1348807 : Blo 1262449 1348807 := bstep (se 1 (by rfl) ⟨1011605, by rfl⟩ : syracuseStep 1348807 = 2023211) B2023211
theorem B2397431 : Blo 1262449 2397431 := bstep (se 1 (by rfl) ⟨1798073, by rfl⟩ : syracuseStep 2397431 = 3596147) B3596147
theorem B2700535 : Blo 1262449 2700535 := bstep (se 1 (by rfl) ⟨2025401, by rfl⟩ : syracuseStep 2700535 = 4050803) B4050803
theorem B4265459 : Blo 1262449 4265459 := bstep (se 1 (by rfl) ⟨3199094, by rfl⟩ : syracuseStep 4265459 = 6398189) B6398189
theorem B1799759 : Blo 1262449 1799759 := bstep (se 1 (by rfl) ⟨1349819, by rfl⟩ : syracuseStep 1799759 = 2699639) B2699639
theorem B3839737 : Blo 1262449 3839737 := bstep (se 2 (by rfl) ⟨1439901, by rfl⟩ : syracuseStep 3839737 = 2879803) B2879803
theorem B9729953 : Blo 1262449 9729953 := bstep (se 2 (by rfl) ⟨3648732, by rfl⟩ : syracuseStep 9729953 = 7297465) B7297465
theorem B3037103 : Blo 1262449 3037103 := bstep (se 1 (by rfl) ⟨2277827, by rfl⟩ : syracuseStep 3037103 = 4555655) B4555655
theorem B4437947 : Blo 1262449 4437947 := bstep (se 1 (by rfl) ⟨3328460, by rfl⟩ : syracuseStep 4437947 = 6656921) B6656921
theorem B9107387 : Blo 1262449 9107387 := bstep (se 1 (by rfl) ⟨6830540, by rfl⟩ : syracuseStep 9107387 = 13661081) B13661081
theorem B4265999 : Blo 1262449 4265999 := bstep (se 1 (by rfl) ⟨3199499, by rfl⟩ : syracuseStep 4265999 = 6398999) B6398999
theorem B2840633 : Blo 1262449 2840633 := bstep (se 2 (by rfl) ⟨1065237, by rfl⟩ : syracuseStep 2840633 = 2130475) B2130475
theorem B9730205 : Blo 1262449 9730205 := bstep (se 3 (by rfl) ⟨1824413, by rfl⟩ : syracuseStep 9730205 = 3648827) B3648827
theorem B4323689 : Blo 1262449 4323689 := bstep (se 2 (by rfl) ⟨1621383, by rfl⟩ : syracuseStep 4323689 = 3242767) B3242767
theorem B2840975 : Blo 1262449 2840975 := bstep (se 1 (by rfl) ⟨2130731, by rfl⟩ : syracuseStep 2840975 = 4261463) B4261463
theorem B2398729 : Blo 1262449 2398729 := bstep (se 2 (by rfl) ⟨899523, by rfl⟩ : syracuseStep 2398729 = 1799047) B1799047
theorem B4266593 : Blo 1262449 4266593 := bstep (se 2 (by rfl) ⟨1599972, by rfl⟩ : syracuseStep 4266593 = 3199945) B3199945
theorem B2841299 : Blo 1262449 2841299 := bstep (se 1 (by rfl) ⟨2130974, by rfl⟩ : syracuseStep 2841299 = 4261949) B4261949
theorem B4553567 : Blo 1262449 4553567 := bstep (se 1 (by rfl) ⟨3415175, by rfl⟩ : syracuseStep 4553567 = 6830351) B6830351
theorem B2399071 : Blo 1262449 2399071 := bstep (se 1 (by rfl) ⟨1799303, by rfl⟩ : syracuseStep 2399071 = 3598607) B3598607
theorem B4799645 : Blo 1262449 4799645 := bstep (se 3 (by rfl) ⟨899933, by rfl⟩ : syracuseStep 4799645 = 1799867) B1799867
theorem B6659275 : Blo 1262449 6659275 := bstep (se 1 (by rfl) ⟨4994456, by rfl⟩ : syracuseStep 6659275 = 9988913) B9988913
theorem B9108773 : Blo 1262449 9108773 := bstep (se 4 (by rfl) ⟨853947, by rfl⟩ : syracuseStep 9108773 = 1707895) B1707895
theorem B2080073 : Blo 1262449 2080073 := bstep (se 2 (by rfl) ⟨780027, by rfl⟩ : syracuseStep 2080073 = 1560055) B1560055
theorem B5397961 : Blo 1262449 5397961 := bstep (se 2 (by rfl) ⟨2024235, by rfl⟩ : syracuseStep 5397961 = 4048471) B4048471
theorem B3841499 : Blo 1262449 3841499 := bstep (se 1 (by rfl) ⟨2881124, by rfl⟩ : syracuseStep 3841499 = 5762249) B5762249
theorem B14384627 : Blo 1262449 14384627 := bstep (se 1 (by rfl) ⟨10788470, by rfl⟩ : syracuseStep 14384627 = 21576941) B21576941
theorem B4046345 : Blo 1262449 4046345 := bstep (se 2 (by rfl) ⟨1517379, by rfl⟩ : syracuseStep 4046345 = 3034759) B3034759
theorem B4046395 : Blo 1262449 4046395 := bstep (se 1 (by rfl) ⟨3034796, by rfl⟩ : syracuseStep 4046395 = 6069593) B6069593
theorem B3595873 : Blo 1262449 3595873 := bstep (se 2 (by rfl) ⟨1348452, by rfl⟩ : syracuseStep 3595873 = 2696905) B2696905
theorem B2842235 : Blo 1262449 2842235 := bstep (se 1 (by rfl) ⟨2131676, by rfl⟩ : syracuseStep 2842235 = 4263353) B4263353
theorem B2842361 : Blo 1262449 2842361 := bstep (se 2 (by rfl) ⟨1065885, by rfl⟩ : syracuseStep 2842361 = 2131771) B2131771
theorem B40992581 : Blo 1262449 40992581 := bstep (se 4 (by rfl) ⟨3843054, by rfl⟩ : syracuseStep 40992581 = 7686109) B7686109
theorem B4800329 : Blo 1262449 4800329 := bstep (se 2 (by rfl) ⟨1800123, by rfl⟩ : syracuseStep 4800329 = 3600247) B3600247
theorem B9600929 : Blo 1262449 9600929 := bstep (se 2 (by rfl) ⟨3600348, by rfl⟩ : syracuseStep 9600929 = 7200697) B7200697
theorem B2400187 : Blo 1262449 2400187 := bstep (se 1 (by rfl) ⟨1800140, by rfl⟩ : syracuseStep 2400187 = 3600281) B3600281
theorem B9109523 : Blo 1262449 9109523 := bstep (se 1 (by rfl) ⟨6832142, by rfl⟩ : syracuseStep 9109523 = 13664285) B13664285
theorem B4800617 : Blo 1262449 4800617 := bstep (se 2 (by rfl) ⟨1800231, by rfl⟩ : syracuseStep 4800617 = 3600463) B3600463
theorem B11534683 : Blo 1262449 11534683 := bstep (se 1 (by rfl) ⟨8651012, by rfl⟩ : syracuseStep 11534683 = 17302025) B17302025
theorem B2842991 : Blo 1262449 2842991 := bstep (se 1 (by rfl) ⟨2132243, by rfl⟩ : syracuseStep 2842991 = 4264487) B4264487
theorem B2843063 : Blo 1262449 2843063 := bstep (se 1 (by rfl) ⟨2132297, by rfl⟩ : syracuseStep 2843063 = 4264595) B4264595
theorem B10936777 : Blo 1262449 10936777 := bstep (se 2 (by rfl) ⟨4101291, by rfl⟩ : syracuseStep 10936777 = 8202583) B8202583
theorem B6070747 : Blo 1262449 6070747 := bstep (se 1 (by rfl) ⟨4553060, by rfl⟩ : syracuseStep 6070747 = 9106121) B9106121
theorem B2843207 : Blo 1262449 2843207 := bstep (se 1 (by rfl) ⟨2132405, by rfl⟩ : syracuseStep 2843207 = 4264811) B4264811
theorem B1598059 : Blo 1262449 1598059 := bstep (se 1 (by rfl) ⟨1198544, by rfl⟩ : syracuseStep 1598059 = 2397089) B2397089
theorem B2843243 : Blo 1262449 2843243 := bstep (se 1 (by rfl) ⟨2132432, by rfl⟩ : syracuseStep 2843243 = 4264865) B4264865
theorem B3597023 : Blo 1262449 3597023 := bstep (se 1 (by rfl) ⟨2697767, by rfl⟩ : syracuseStep 3597023 = 5395535) B5395535
theorem B1598287 : Blo 1262449 1598287 := bstep (se 1 (by rfl) ⟨1198715, by rfl⟩ : syracuseStep 1598287 = 2397431) B2397431
theorem B1262491 : Blo 1262449 1262491 := bstep (se 1 (by rfl) ⟨946868, by rfl⟩ : syracuseStep 1262491 = 1893737) B1893737
theorem B1262543 : Blo 1262449 1262543 := bstep (se 1 (by rfl) ⟨946907, by rfl⟩ : syracuseStep 1262543 = 1893815) B1893815
theorem B1262567 : Blo 1262449 1262567 := bstep (se 1 (by rfl) ⟨946925, by rfl⟩ : syracuseStep 1262567 = 1893851) B1893851
theorem B3195895 : Blo 1262449 3195895 := bstep (se 1 (by rfl) ⟨2396921, by rfl⟩ : syracuseStep 3195895 = 4793843) B4793843
theorem B2843639 : Blo 1262449 2843639 := bstep (se 1 (by rfl) ⟨2132729, by rfl⟩ : syracuseStep 2843639 = 4265459) B4265459
theorem B2131177 : Blo 1262449 2131177 := bstep (se 2 (by rfl) ⟨799191, by rfl⟩ : syracuseStep 2131177 = 1598383) B1598383
theorem B1262879 : Blo 1262449 1262879 := bstep (se 1 (by rfl) ⟨947159, by rfl⟩ : syracuseStep 1262879 = 1894319) B1894319
theorem B2131231 : Blo 1262449 2131231 := bstep (se 1 (by rfl) ⟨1598423, by rfl⟩ : syracuseStep 2131231 = 3196847) B3196847
theorem B2024735 : Blo 1262449 2024735 := bstep (se 1 (by rfl) ⟨1518551, by rfl⟩ : syracuseStep 2024735 = 3037103) B3037103
theorem B3196199 : Blo 1262449 3196199 := bstep (se 1 (by rfl) ⟨2397149, by rfl⟩ : syracuseStep 3196199 = 4794299) B4794299
theorem B6071591 : Blo 1262449 6071591 := bstep (se 1 (by rfl) ⟨4553693, by rfl⟩ : syracuseStep 6071591 = 9107387) B9107387
theorem B1262939 : Blo 1262449 1262939 := bstep (se 1 (by rfl) ⟨947204, by rfl⟩ : syracuseStep 1262939 = 1894409) B1894409
theorem B2843999 : Blo 1262449 2843999 := bstep (se 1 (by rfl) ⟨2132999, by rfl⟩ : syracuseStep 2843999 = 4265999) B4265999
theorem B1262959 : Blo 1262449 1262959 := bstep (se 1 (by rfl) ⟨947219, by rfl⟩ : syracuseStep 1262959 = 1894439) B1894439
theorem B1893755 : Blo 1262449 1893755 := bstep (se 1 (by rfl) ⟨1420316, by rfl⟩ : syracuseStep 1893755 = 2840633) B2840633
theorem B1263015 : Blo 1262449 1263015 := bstep (se 1 (by rfl) ⟨947261, by rfl⟩ : syracuseStep 1263015 = 1894523) B1894523
theorem B1893881 : Blo 1262449 1893881 := bstep (se 2 (by rfl) ⟨710205, by rfl⟩ : syracuseStep 1893881 = 1420411) B1420411
theorem B1263099 : Blo 1262449 1263099 := bstep (se 1 (by rfl) ⟨947324, by rfl⟩ : syracuseStep 1263099 = 1894649) B1894649
theorem B1263167 : Blo 1262449 1263167 := bstep (se 1 (by rfl) ⟨947375, by rfl⟩ : syracuseStep 1263167 = 1894751) B1894751
theorem B1263175 : Blo 1262449 1263175 := bstep (se 1 (by rfl) ⟨947381, by rfl⟩ : syracuseStep 1263175 = 1894763) B1894763
theorem B6391385 : Blo 1262449 6391385 := bstep (se 2 (by rfl) ⟨2396769, by rfl⟩ : syracuseStep 6391385 = 4793539) B4793539
theorem B1893983 : Blo 1262449 1893983 := bstep (se 1 (by rfl) ⟨1420487, by rfl⟩ : syracuseStep 1893983 = 2840975) B2840975
theorem B2131643 : Blo 1262449 2131643 := bstep (se 1 (by rfl) ⟨1598732, by rfl⟩ : syracuseStep 2131643 = 3197465) B3197465
theorem B1263327 : Blo 1262449 1263327 := bstep (se 1 (by rfl) ⟨947495, by rfl⟩ : syracuseStep 1263327 = 1894991) B1894991
theorem B2844395 : Blo 1262449 2844395 := bstep (se 1 (by rfl) ⟨2133296, by rfl⟩ : syracuseStep 2844395 = 4266593) B4266593
theorem B1263407 : Blo 1262449 1263407 := bstep (se 1 (by rfl) ⟨947555, by rfl⟩ : syracuseStep 1263407 = 1895111) B1895111
theorem B1894199 : Blo 1262449 1894199 := bstep (se 1 (by rfl) ⟨1420649, by rfl⟩ : syracuseStep 1894199 = 2841299) B2841299
theorem B2844521 : Blo 1262449 2844521 := bstep (se 2 (by rfl) ⟨1066695, by rfl⟩ : syracuseStep 2844521 = 2133391) B2133391
theorem B1263515 : Blo 1262449 1263515 := bstep (se 1 (by rfl) ⟨947636, by rfl⟩ : syracuseStep 1263515 = 1895273) B1895273
theorem B1263567 : Blo 1262449 1263567 := bstep (se 1 (by rfl) ⟨947675, by rfl⟩ : syracuseStep 1263567 = 1895351) B1895351
theorem B1263591 : Blo 1262449 1263591 := bstep (se 1 (by rfl) ⟨947693, by rfl⟩ : syracuseStep 1263591 = 1895387) B1895387
theorem B1894505 : Blo 1262449 1894505 := bstep (se 2 (by rfl) ⟨710439, by rfl⟩ : syracuseStep 1894505 = 1420879) B1420879
theorem B4794497 : Blo 1262449 4794497 := bstep (se 2 (by rfl) ⟨1797936, by rfl⟩ : syracuseStep 4794497 = 3595873) B3595873
theorem B6072515 : Blo 1262449 6072515 := bstep (se 1 (by rfl) ⟨4554386, by rfl⟩ : syracuseStep 6072515 = 9108773) B9108773
theorem B14043331 : Blo 1262449 14043331 := bstep (se 1 (by rfl) ⟨10532498, by rfl⟩ : syracuseStep 14043331 = 21064997) B21064997
theorem B1386715 : Blo 1262449 1386715 := bstep (se 1 (by rfl) ⟨1040036, by rfl⟩ : syracuseStep 1386715 = 2080073) B2080073
theorem B1263903 : Blo 1262449 1263903 := bstep (se 1 (by rfl) ⟨947927, by rfl⟩ : syracuseStep 1263903 = 1895855) B1895855
theorem B2697563 : Blo 1262449 2697563 := bstep (se 1 (by rfl) ⟨2023172, by rfl⟩ : syracuseStep 2697563 = 4046345) B4046345
theorem B1263963 : Blo 1262449 1263963 := bstep (se 1 (by rfl) ⟨947972, by rfl⟩ : syracuseStep 1263963 = 1895945) B1895945
theorem B1263983 : Blo 1262449 1263983 := bstep (se 1 (by rfl) ⟨947987, by rfl⟩ : syracuseStep 1263983 = 1895975) B1895975
theorem B1894823 : Blo 1262449 1894823 := bstep (se 1 (by rfl) ⟨1421117, by rfl⟩ : syracuseStep 1894823 = 2842235) B2842235
theorem B19712423 : Blo 1262449 19712423 := bstep (se 1 (by rfl) ⟨14784317, by rfl⟩ : syracuseStep 19712423 = 29568635) B29568635
theorem B1264039 : Blo 1262449 1264039 := bstep (se 1 (by rfl) ⟨948029, by rfl⟩ : syracuseStep 1264039 = 1896059) B1896059
theorem B4262327 : Blo 1262449 4262327 := bstep (se 1 (by rfl) ⟨3196745, by rfl⟩ : syracuseStep 4262327 = 6393491) B6393491
theorem B1894907 : Blo 1262449 1894907 := bstep (se 1 (by rfl) ⟨1421180, by rfl⟩ : syracuseStep 1894907 = 2842361) B2842361
theorem B1264123 : Blo 1262449 1264123 := bstep (se 1 (by rfl) ⟨948092, by rfl⟩ : syracuseStep 1264123 = 1896185) B1896185
theorem B1264191 : Blo 1262449 1264191 := bstep (se 1 (by rfl) ⟨948143, by rfl⟩ : syracuseStep 1264191 = 1896287) B1896287
theorem B1264199 : Blo 1262449 1264199 := bstep (se 1 (by rfl) ⟨948149, by rfl⟩ : syracuseStep 1264199 = 1896299) B1896299
theorem B6400619 : Blo 1262449 6400619 := bstep (se 1 (by rfl) ⟨4800464, by rfl⟩ : syracuseStep 6400619 = 9600929) B9600929
theorem B1895033 : Blo 1262449 1895033 := bstep (se 2 (by rfl) ⟨710637, by rfl⟩ : syracuseStep 1895033 = 1421275) B1421275
theorem B7293563 : Blo 1262449 7293563 := bstep (se 1 (by rfl) ⟨5470172, by rfl⟩ : syracuseStep 7293563 = 10940345) B10940345
theorem B1895087 : Blo 1262449 1895087 := bstep (se 1 (by rfl) ⟨1421315, by rfl⟩ : syracuseStep 1895087 = 2842631) B2842631
theorem B1600175 : Blo 1262449 1600175 := bstep (se 1 (by rfl) ⟨1200131, by rfl⟩ : syracuseStep 1600175 = 2400263) B2400263
theorem B1895135 : Blo 1262449 1895135 := bstep (se 1 (by rfl) ⟨1421351, by rfl⟩ : syracuseStep 1895135 = 2842703) B2842703
theorem B1264351 : Blo 1262449 1264351 := bstep (se 1 (by rfl) ⟨948263, by rfl⟩ : syracuseStep 1264351 = 1896527) B1896527
theorem B1264431 : Blo 1262449 1264431 := bstep (se 1 (by rfl) ⟨948323, by rfl⟩ : syracuseStep 1264431 = 1896647) B1896647
theorem B14396291 : Blo 1262449 14396291 := bstep (se 1 (by rfl) ⟨10797218, by rfl⟩ : syracuseStep 14396291 = 21594437) B21594437
theorem B3197839 : Blo 1262449 3197839 := bstep (se 1 (by rfl) ⟨2398379, by rfl⟩ : syracuseStep 3197839 = 4796759) B4796759
theorem B3034027 : Blo 1262449 3034027 := bstep (se 1 (by rfl) ⟨2275520, by rfl⟩ : syracuseStep 3034027 = 4551041) B4551041
theorem B1895399 : Blo 1262449 1895399 := bstep (se 1 (by rfl) ⟨1421549, by rfl⟩ : syracuseStep 1895399 = 2843099) B2843099
theorem B6401105 : Blo 1262449 6401105 := bstep (se 2 (by rfl) ⟨2400414, by rfl⟩ : syracuseStep 6401105 = 4800829) B4800829
theorem B16190603 : Blo 1262449 16190603 := bstep (se 1 (by rfl) ⟨12142952, by rfl⟩ : syracuseStep 16190603 = 24285905) B24285905
theorem B1895657 : Blo 1262449 1895657 := bstep (se 2 (by rfl) ⟨710871, by rfl⟩ : syracuseStep 1895657 = 1421743) B1421743
theorem B1895711 : Blo 1262449 1895711 := bstep (se 1 (by rfl) ⟨1421783, by rfl⟩ : syracuseStep 1895711 = 2843567) B2843567
theorem B8088893 : Blo 1262449 8088893 := bstep (se 3 (by rfl) ⟨1516667, by rfl⟩ : syracuseStep 8088893 = 3033335) B3033335
theorem B3198305 : Blo 1262449 3198305 := bstep (se 2 (by rfl) ⟨1199364, by rfl⟩ : syracuseStep 3198305 = 2398729) B2398729
theorem B10800499 : Blo 1262449 10800499 := bstep (se 1 (by rfl) ⟨8100374, by rfl⟩ : syracuseStep 10800499 = 16200749) B16200749
theorem B2133371 : Blo 1262449 2133371 := bstep (se 1 (by rfl) ⟨1600028, by rfl⟩ : syracuseStep 2133371 = 3200057) B3200057
theorem B1895879 : Blo 1262449 1895879 := bstep (se 1 (by rfl) ⟨1421909, by rfl⟩ : syracuseStep 1895879 = 2843819) B2843819
theorem B6073937 : Blo 1262449 6073937 := bstep (se 2 (by rfl) ⟨2277726, by rfl⟩ : syracuseStep 6073937 = 4555453) B4555453
theorem B2698913 : Blo 1262449 2698913 := bstep (se 2 (by rfl) ⟨1012092, by rfl⟩ : syracuseStep 2698913 = 2024185) B2024185
theorem B373616327 : Blo 1262449 373616327 := bstep (se 1 (by rfl) ⟨280212245, by rfl⟩ : syracuseStep 373616327 = 560424491) B560424491
theorem B1421023 : Blo 1262449 1421023 := bstep (se 1 (by rfl) ⟨1065767, by rfl⟩ : syracuseStep 1421023 = 2131535) B2131535
theorem B3198761 : Blo 1262449 3198761 := bstep (se 2 (by rfl) ⟨1199535, by rfl⟩ : syracuseStep 3198761 = 2399071) B2399071
theorem B1896233 : Blo 1262449 1896233 := bstep (se 2 (by rfl) ⟨711087, by rfl⟩ : syracuseStep 1896233 = 1422175) B1422175
theorem B1896239 : Blo 1262449 1896239 := bstep (se 1 (by rfl) ⟨1422179, by rfl⟩ : syracuseStep 1896239 = 2844359) B2844359
theorem B4796441 : Blo 1262449 4796441 := bstep (se 2 (by rfl) ⟨1798665, by rfl⟩ : syracuseStep 4796441 = 3597331) B3597331
theorem B20484353 : Blo 1262449 20484353 := bstep (se 2 (by rfl) ⟨7681632, by rfl⟩ : syracuseStep 20484353 = 15363265) B15363265
theorem B1798409 : Blo 1262449 1798409 := bstep (se 2 (by rfl) ⟨674403, by rfl⟩ : syracuseStep 1798409 = 1348807) B1348807
theorem B1421599 : Blo 1262449 1421599 := bstep (se 1 (by rfl) ⟨1066199, by rfl⟩ : syracuseStep 1421599 = 2132399) B2132399
theorem B3600713 : Blo 1262449 3600713 := bstep (se 2 (by rfl) ⟨1350267, by rfl⟩ : syracuseStep 3600713 = 2700535) B2700535
theorem B5763419 : Blo 1262449 5763419 := bstep (se 1 (by rfl) ⟨4322564, by rfl⟩ : syracuseStep 5763419 = 8645129) B8645129
theorem B3076535 : Blo 1262449 3076535 := bstep (se 1 (by rfl) ⟨2307401, by rfl⟩ : syracuseStep 3076535 = 4614803) B4614803
theorem B8319451 : Blo 1262449 8319451 := bstep (se 1 (by rfl) ⟨6239588, by rfl⟩ : syracuseStep 8319451 = 12479177) B12479177
theorem B3035711 : Blo 1262449 3035711 := bstep (se 1 (by rfl) ⟨2276783, by rfl⟩ : syracuseStep 3035711 = 4553567) B4553567
theorem B1421887 : Blo 1262449 1421887 := bstep (se 1 (by rfl) ⟨1066415, by rfl⟩ : syracuseStep 1421887 = 2132831) B2132831
theorem B49230433 : Blo 1262449 49230433 := bstep (se 2 (by rfl) ⟨18461412, by rfl⟩ : syracuseStep 49230433 = 36922825) B36922825
theorem B7197281 : Blo 1262449 7197281 := bstep (se 2 (by rfl) ⟨2698980, by rfl⟩ : syracuseStep 7197281 = 5397961) B5397961
theorem B5395193 : Blo 1262449 5395193 := bstep (se 2 (by rfl) ⟨2023197, by rfl⟩ : syracuseStep 5395193 = 4046395) B4046395
theorem B3199763 : Blo 1262449 3199763 := bstep (se 1 (by rfl) ⟨2399822, by rfl⟩ : syracuseStep 3199763 = 4799645) B4799645
theorem B8090533 : Blo 1262449 8090533 := bstep (se 4 (by rfl) ⟨758487, by rfl⟩ : syracuseStep 8090533 = 1516975) B1516975
theorem B10785737 : Blo 1262449 10785737 := bstep (se 2 (by rfl) ⟨4044651, by rfl⟩ : syracuseStep 10785737 = 8089303) B8089303
theorem B2560999 : Blo 1262449 2560999 := bstep (se 1 (by rfl) ⟨1920749, by rfl⟩ : syracuseStep 2560999 = 3841499) B3841499
theorem B9589751 : Blo 1262449 9589751 := bstep (se 1 (by rfl) ⟨7192313, by rfl⟩ : syracuseStep 9589751 = 14384627) B14384627
theorem B11834525 : Blo 1262449 11834525 := bstep (se 3 (by rfl) ⟨2218973, by rfl⟩ : syracuseStep 11834525 = 4437947) B4437947
theorem B3200219 : Blo 1262449 3200219 := bstep (se 1 (by rfl) ⟨2400164, by rfl⟩ : syracuseStep 3200219 = 4800329) B4800329
theorem B3200249 : Blo 1262449 3200249 := bstep (se 2 (by rfl) ⟨1200093, by rfl⟩ : syracuseStep 3200249 = 2400187) B2400187
theorem B26285417 : Blo 1262449 26285417 := bstep (se 2 (by rfl) ⟨9857031, by rfl⟩ : syracuseStep 26285417 = 19714063) B19714063
theorem B4265405 : Blo 1262449 4265405 := bstep (se 3 (by rfl) ⟨799763, by rfl⟩ : syracuseStep 4265405 = 1599527) B1599527
theorem B1349183 : Blo 1262449 1349183 := bstep (se 1 (by rfl) ⟨1011887, by rfl⟩ : syracuseStep 1349183 = 2023775) B2023775
theorem B1521223 : Blo 1262449 1521223 := bstep (se 1 (by rfl) ⟨1140917, by rfl⟩ : syracuseStep 1521223 = 2281835) B2281835
theorem B29554391 : Blo 1262449 29554391 := bstep (se 1 (by rfl) ⟨22165793, by rfl⟩ : syracuseStep 29554391 = 44331587) B44331587
theorem B4265783 : Blo 1262449 4265783 := bstep (se 1 (by rfl) ⟨3199337, by rfl⟩ : syracuseStep 4265783 = 6398675) B6398675
theorem B4266269 : Blo 1262449 4266269 := bstep (se 3 (by rfl) ⟨799925, by rfl⟩ : syracuseStep 4266269 = 1599851) B1599851
theorem B2840939 : Blo 1262449 2840939 := bstep (se 1 (by rfl) ⟨2130704, by rfl⟩ : syracuseStep 2840939 = 4261409) B4261409
theorem B2841083 : Blo 1262449 2841083 := bstep (se 1 (by rfl) ⟨2130812, by rfl⟩ : syracuseStep 2841083 = 4261625) B4261625
theorem B9853435 : Blo 1262449 9853435 := bstep (se 1 (by rfl) ⟨7390076, by rfl⟩ : syracuseStep 9853435 = 14780153) B14780153
theorem B6486635 : Blo 1262449 6486635 := bstep (se 1 (by rfl) ⟨4864976, by rfl⟩ : syracuseStep 6486635 = 9729953) B9729953
theorem B2841209 : Blo 1262449 2841209 := bstep (se 2 (by rfl) ⟨1065453, by rfl⟩ : syracuseStep 2841209 = 2130907) B2130907
theorem B2841263 : Blo 1262449 2841263 := bstep (se 1 (by rfl) ⟨2130947, by rfl⟩ : syracuseStep 2841263 = 4261895) B4261895
theorem B2841335 : Blo 1262449 2841335 := bstep (se 1 (by rfl) ⟨2131001, by rfl⟩ : syracuseStep 2841335 = 4262003) B4262003
theorem B103791365 : Blo 1262449 103791365 := bstep (se 4 (by rfl) ⟨9730440, by rfl⟩ : syracuseStep 103791365 = 19460881) B19460881
theorem B6486803 : Blo 1262449 6486803 := bstep (se 1 (by rfl) ⟨4865102, by rfl⟩ : syracuseStep 6486803 = 9730205) B9730205
theorem B4799357 : Blo 1262449 4799357 := bstep (se 3 (by rfl) ⟨899879, by rfl⟩ : syracuseStep 4799357 = 1799759) B1799759
theorem B9591695 : Blo 1262449 9591695 := bstep (se 1 (by rfl) ⟨7193771, by rfl⟩ : syracuseStep 9591695 = 14387543) B14387543
theorem B16423823 : Blo 1262449 16423823 := bstep (se 1 (by rfl) ⟨12317867, by rfl⟩ : syracuseStep 16423823 = 24635735) B24635735
theorem B2882459 : Blo 1262449 2882459 := bstep (se 1 (by rfl) ⟨2161844, by rfl⟩ : syracuseStep 2882459 = 4323689) B4323689
theorem B2841515 : Blo 1262449 2841515 := bstep (se 1 (by rfl) ⟨2131136, by rfl⟩ : syracuseStep 2841515 = 4262273) B4262273
theorem B8879033 : Blo 1262449 8879033 := bstep (se 2 (by rfl) ⟨3329637, by rfl⟩ : syracuseStep 8879033 = 6659275) B6659275
theorem B2399375 : Blo 1262449 2399375 := bstep (se 1 (by rfl) ⟨1799531, by rfl⟩ : syracuseStep 2399375 = 3599063) B3599063
theorem B3415229 : Blo 1262449 3415229 := bstep (se 3 (by rfl) ⟨640355, by rfl⟩ : syracuseStep 3415229 = 1280711) B1280711
theorem B10378469 : Blo 1262449 10378469 := bstep (se 4 (by rfl) ⟨972981, by rfl⟩ : syracuseStep 10378469 = 1945963) B1945963
theorem B8101093 : Blo 1262449 8101093 := bstep (se 4 (by rfl) ⟨759477, by rfl⟩ : syracuseStep 8101093 = 1518955) B1518955
theorem B2399519 : Blo 1262449 2399519 := bstep (se 1 (by rfl) ⟨1799639, by rfl⟩ : syracuseStep 2399519 = 3599279) B3599279
theorem B4267295 : Blo 1262449 4267295 := bstep (se 1 (by rfl) ⟨3200471, by rfl⟩ : syracuseStep 4267295 = 6400943) B6400943
theorem B3284363 : Blo 1262449 3284363 := bstep (se 1 (by rfl) ⟨2463272, by rfl⟩ : syracuseStep 3284363 = 4926545) B4926545
theorem B2842055 : Blo 1262449 2842055 := bstep (se 1 (by rfl) ⟨2131541, by rfl⟩ : syracuseStep 2842055 = 4263083) B4263083
theorem B11091601 : Blo 1262449 11091601 := bstep (se 2 (by rfl) ⟨4159350, by rfl⟩ : syracuseStep 11091601 = 8318701) B8318701
theorem B5119649 : Blo 1262449 5119649 := bstep (se 2 (by rfl) ⟨1919868, by rfl⟩ : syracuseStep 5119649 = 3839737) B3839737
theorem B4800161 : Blo 1262449 4800161 := bstep (se 2 (by rfl) ⟨1800060, by rfl⟩ : syracuseStep 4800161 = 3600121) B3600121
theorem B7200515 : Blo 1262449 7200515 := bstep (se 1 (by rfl) ⟨5400386, by rfl⟩ : syracuseStep 7200515 = 10800773) B10800773
theorem B6397703 : Blo 1262449 6397703 := bstep (se 1 (by rfl) ⟨4798277, by rfl⟩ : syracuseStep 6397703 = 9596555) B9596555
theorem B2842415 : Blo 1262449 2842415 := bstep (se 1 (by rfl) ⟨2131811, by rfl⟩ : syracuseStep 2842415 = 4263623) B4263623
theorem B2023223 : Blo 1262449 2023223 := bstep (se 1 (by rfl) ⟨1517417, by rfl⟩ : syracuseStep 2023223 = 3034835) B3034835
theorem B3596089 : Blo 1262449 3596089 := bstep (se 2 (by rfl) ⟨1348533, by rfl⟩ : syracuseStep 3596089 = 2697067) B2697067
theorem B27328387 : Blo 1262449 27328387 := bstep (se 1 (by rfl) ⟨20496290, by rfl⟩ : syracuseStep 27328387 = 40992581) B40992581
theorem B3842279 : Blo 1262449 3842279 := bstep (se 1 (by rfl) ⟨2881709, by rfl⟩ : syracuseStep 3842279 = 5763419) B5763419
theorem B2023807 : Blo 1262449 2023807 := bstep (se 1 (by rfl) ⟨1517855, by rfl⟩ : syracuseStep 2023807 = 3035711) B3035711
theorem B3596795 : Blo 1262449 3596795 := bstep (se 1 (by rfl) ⟨2697596, by rfl⟩ : syracuseStep 3596795 = 5395193) B5395193
theorem B14582369 : Blo 1262449 14582369 := bstep (se 2 (by rfl) ⟨5468388, by rfl⟩ : syracuseStep 14582369 = 10936777) B10936777
theorem B8094329 : Blo 1262449 8094329 := bstep (se 2 (by rfl) ⟨3035373, by rfl⟩ : syracuseStep 8094329 = 6070747) B6070747
theorem B11092601 : Blo 1262449 11092601 := bstep (se 2 (by rfl) ⟨4159725, by rfl⟩ : syracuseStep 11092601 = 8319451) B8319451
theorem B54624941 : Blo 1262449 54624941 := bstep (se 3 (by rfl) ⟨10242176, by rfl⟩ : syracuseStep 54624941 = 20484353) B20484353
theorem B5399293 : Blo 1262449 5399293 := bstep (se 3 (by rfl) ⟨1012367, by rfl⟩ : syracuseStep 5399293 = 2024735) B2024735
theorem B59155205 : Blo 1262449 59155205 := bstep (se 4 (by rfl) ⟨5545800, by rfl⟩ : syracuseStep 59155205 = 11091601) B11091601
theorem B7889683 : Blo 1262449 7889683 := bstep (se 1 (by rfl) ⟨5917262, by rfl⟩ : syracuseStep 7889683 = 11834525) B11834525
theorem B2130745 : Blo 1262449 2130745 := bstep (se 2 (by rfl) ⟨799029, by rfl⟩ : syracuseStep 2130745 = 1598059) B1598059
theorem B9601901 : Blo 1262449 9601901 := bstep (se 3 (by rfl) ⟨1800356, by rfl⟩ : syracuseStep 9601901 = 3600713) B3600713
theorem B2130799 : Blo 1262449 2130799 := bstep (se 1 (by rfl) ⟨1598099, by rfl⟩ : syracuseStep 2130799 = 3196199) B3196199
theorem B4047727 : Blo 1262449 4047727 := bstep (se 1 (by rfl) ⟨3035795, by rfl⟩ : syracuseStep 4047727 = 6071591) B6071591
theorem B17523611 : Blo 1262449 17523611 := bstep (se 1 (by rfl) ⟨13142708, by rfl⟩ : syracuseStep 17523611 = 26285417) B26285417
theorem B1262503 : Blo 1262449 1262503 := bstep (se 1 (by rfl) ⟨946877, by rfl⟩ : syracuseStep 1262503 = 1893755) B1893755
theorem B2843603 : Blo 1262449 2843603 := bstep (se 1 (by rfl) ⟨2132702, by rfl⟩ : syracuseStep 2843603 = 4265405) B4265405
theorem B1262587 : Blo 1262449 1262587 := bstep (se 1 (by rfl) ⟨946940, by rfl⟩ : syracuseStep 1262587 = 1893881) B1893881
theorem B4260923 : Blo 1262449 4260923 := bstep (se 1 (by rfl) ⟨3195692, by rfl⟩ : syracuseStep 4260923 = 6391385) B6391385
theorem B1262655 : Blo 1262449 1262655 := bstep (se 1 (by rfl) ⟨946991, by rfl⟩ : syracuseStep 1262655 = 1893983) B1893983
theorem B2131049 : Blo 1262449 2131049 := bstep (se 2 (by rfl) ⟨799143, by rfl⟩ : syracuseStep 2131049 = 1598287) B1598287
theorem B19702927 : Blo 1262449 19702927 := bstep (se 1 (by rfl) ⟨14777195, by rfl⟩ : syracuseStep 19702927 = 29554391) B29554391
theorem B1262799 : Blo 1262449 1262799 := bstep (se 1 (by rfl) ⟨947099, by rfl⟩ : syracuseStep 1262799 = 1894199) B1894199
theorem B2843855 : Blo 1262449 2843855 := bstep (se 1 (by rfl) ⟨2132891, by rfl⟩ : syracuseStep 2843855 = 4265783) B4265783
theorem B4261193 : Blo 1262449 4261193 := bstep (se 2 (by rfl) ⟨1597947, by rfl⟩ : syracuseStep 4261193 = 3195895) B3195895
theorem B1263003 : Blo 1262449 1263003 := bstep (se 1 (by rfl) ⟨947252, by rfl⟩ : syracuseStep 1263003 = 1894505) B1894505
theorem B3196331 : Blo 1262449 3196331 := bstep (se 1 (by rfl) ⟨2397248, by rfl⟩ : syracuseStep 3196331 = 4794497) B4794497
theorem B4048343 : Blo 1262449 4048343 := bstep (se 1 (by rfl) ⟨3036257, by rfl⟩ : syracuseStep 4048343 = 6072515) B6072515
theorem B3597821 : Blo 1262449 3597821 := bstep (se 3 (by rfl) ⟨674591, by rfl⟩ : syracuseStep 3597821 = 1349183) B1349183
theorem B2844179 : Blo 1262449 2844179 := bstep (se 1 (by rfl) ⟨2133134, by rfl⟩ : syracuseStep 2844179 = 4266269) B4266269
theorem B1893959 : Blo 1262449 1893959 := bstep (se 1 (by rfl) ⟨1420469, by rfl⟩ : syracuseStep 1893959 = 2840939) B2840939
theorem B13141615 : Blo 1262449 13141615 := bstep (se 1 (by rfl) ⟨9856211, by rfl⟩ : syracuseStep 13141615 = 19712423) B19712423
theorem B1263215 : Blo 1262449 1263215 := bstep (se 1 (by rfl) ⟨947411, by rfl⟩ : syracuseStep 1263215 = 1894823) B1894823
theorem B1894055 : Blo 1262449 1894055 := bstep (se 1 (by rfl) ⟨1420541, by rfl⟩ : syracuseStep 1894055 = 2841083) B2841083
theorem B1263271 : Blo 1262449 1263271 := bstep (se 1 (by rfl) ⟨947453, by rfl⟩ : syracuseStep 1263271 = 1894907) B1894907
theorem B1894139 : Blo 1262449 1894139 := bstep (se 1 (by rfl) ⟨1420604, by rfl⟩ : syracuseStep 1894139 = 2841209) B2841209
theorem B1263355 : Blo 1262449 1263355 := bstep (se 1 (by rfl) ⟨947516, by rfl⟩ : syracuseStep 1263355 = 1895033) B1895033
theorem B1894175 : Blo 1262449 1894175 := bstep (se 1 (by rfl) ⟨1420631, by rfl⟩ : syracuseStep 1894175 = 2841263) B2841263
theorem B1263391 : Blo 1262449 1263391 := bstep (se 1 (by rfl) ⟨947543, by rfl⟩ : syracuseStep 1263391 = 1895087) B1895087
theorem B1263423 : Blo 1262449 1263423 := bstep (se 1 (by rfl) ⟨947567, by rfl⟩ : syracuseStep 1263423 = 1895135) B1895135
theorem B1894223 : Blo 1262449 1894223 := bstep (se 1 (by rfl) ⟨1420667, by rfl⟩ : syracuseStep 1894223 = 2841335) B2841335
theorem B1894343 : Blo 1262449 1894343 := bstep (se 1 (by rfl) ⟨1420757, by rfl⟩ : syracuseStep 1894343 = 2841515) B2841515
theorem B1263599 : Blo 1262449 1263599 := bstep (se 1 (by rfl) ⟨947699, by rfl⟩ : syracuseStep 1263599 = 1895399) B1895399
theorem B1599583 : Blo 1262449 1599583 := bstep (se 1 (by rfl) ⟨1199687, by rfl⟩ : syracuseStep 1599583 = 2399375) B2399375
theorem B1263771 : Blo 1262449 1263771 := bstep (se 1 (by rfl) ⟨947828, by rfl⟩ : syracuseStep 1263771 = 1895657) B1895657
theorem B1263807 : Blo 1262449 1263807 := bstep (se 1 (by rfl) ⟨947855, by rfl⟩ : syracuseStep 1263807 = 1895711) B1895711
theorem B1599679 : Blo 1262449 1599679 := bstep (se 1 (by rfl) ⟨1199759, by rfl⟩ : syracuseStep 1599679 = 2399519) B2399519
theorem B2844863 : Blo 1262449 2844863 := bstep (se 1 (by rfl) ⟨2133647, by rfl⟩ : syracuseStep 2844863 = 4267295) B4267295
theorem B5392595 : Blo 1262449 5392595 := bstep (se 1 (by rfl) ⟨4044446, by rfl⟩ : syracuseStep 5392595 = 8088893) B8088893
theorem B16181477 : Blo 1262449 16181477 := bstep (se 4 (by rfl) ⟨1517013, by rfl⟩ : syracuseStep 16181477 = 3034027) B3034027
theorem B2132203 : Blo 1262449 2132203 := bstep (se 1 (by rfl) ⟨1599152, by rfl⟩ : syracuseStep 2132203 = 3198305) B3198305
theorem B2189575 : Blo 1262449 2189575 := bstep (se 1 (by rfl) ⟨1642181, by rfl⟩ : syracuseStep 2189575 = 3284363) B3284363
theorem B1894697 : Blo 1262449 1894697 := bstep (se 2 (by rfl) ⟨710511, by rfl⟩ : syracuseStep 1894697 = 1421023) B1421023
theorem B1894703 : Blo 1262449 1894703 := bstep (se 1 (by rfl) ⟨1421027, by rfl⟩ : syracuseStep 1894703 = 2842055) B2842055
theorem B1263919 : Blo 1262449 1263919 := bstep (se 1 (by rfl) ⟨947939, by rfl⟩ : syracuseStep 1263919 = 1895879) B1895879
theorem B4049291 : Blo 1262449 4049291 := bstep (se 1 (by rfl) ⟨3036968, by rfl⟩ : syracuseStep 4049291 = 6073937) B6073937
theorem B4794785 : Blo 1262449 4794785 := bstep (se 2 (by rfl) ⟨1798044, by rfl⟩ : syracuseStep 4794785 = 3596089) B3596089
theorem B2132507 : Blo 1262449 2132507 := bstep (se 1 (by rfl) ⟨1599380, by rfl⟩ : syracuseStep 2132507 = 3198761) B3198761
theorem B1264155 : Blo 1262449 1264155 := bstep (se 1 (by rfl) ⟨948116, by rfl⟩ : syracuseStep 1264155 = 1896233) B1896233
theorem B1894943 : Blo 1262449 1894943 := bstep (se 1 (by rfl) ⟨1421207, by rfl⟩ : syracuseStep 1894943 = 2842415) B2842415
theorem B1264159 : Blo 1262449 1264159 := bstep (se 1 (by rfl) ⟨948119, by rfl⟩ : syracuseStep 1264159 = 1896239) B1896239
theorem B6073015 : Blo 1262449 6073015 := bstep (se 1 (by rfl) ⟨4554761, by rfl⟩ : syracuseStep 6073015 = 9109523) B9109523
theorem B3197627 : Blo 1262449 3197627 := bstep (se 1 (by rfl) ⟨2398220, by rfl⟩ : syracuseStep 3197627 = 4796441) B4796441
theorem B1895327 : Blo 1262449 1895327 := bstep (se 1 (by rfl) ⟨1421495, by rfl⟩ : syracuseStep 1895327 = 2842991) B2842991
theorem B2051023 : Blo 1262449 2051023 := bstep (se 1 (by rfl) ⟨1538267, by rfl⟩ : syracuseStep 2051023 = 3076535) B3076535
theorem B1895375 : Blo 1262449 1895375 := bstep (se 1 (by rfl) ⟨1421531, by rfl⟩ : syracuseStep 1895375 = 2843063) B2843063
theorem B1895465 : Blo 1262449 1895465 := bstep (se 2 (by rfl) ⟨710799, by rfl⟩ : syracuseStep 1895465 = 1421599) B1421599
theorem B1895471 : Blo 1262449 1895471 := bstep (se 1 (by rfl) ⟨1421603, by rfl⟩ : syracuseStep 1895471 = 2843207) B2843207
theorem B1895495 : Blo 1262449 1895495 := bstep (se 1 (by rfl) ⟨1421621, by rfl⟩ : syracuseStep 1895495 = 2843243) B2843243
theorem B15379577 : Blo 1262449 15379577 := bstep (se 2 (by rfl) ⟨5767341, by rfl⟩ : syracuseStep 15379577 = 11534683) B11534683
theorem B2133175 : Blo 1262449 2133175 := bstep (se 1 (by rfl) ⟨1599881, by rfl⟩ : syracuseStep 2133175 = 3199763) B3199763
theorem B27675917 : Blo 1262449 27675917 := bstep (se 3 (by rfl) ⟨5189234, by rfl⟩ : syracuseStep 27675917 = 10378469) B10378469
theorem B6393167 : Blo 1262449 6393167 := bstep (se 1 (by rfl) ⟨4794875, by rfl⟩ : syracuseStep 6393167 = 9589751) B9589751
theorem B1895759 : Blo 1262449 1895759 := bstep (se 1 (by rfl) ⟨1421819, by rfl⟩ : syracuseStep 1895759 = 2843639) B2843639
theorem B4795757 : Blo 1262449 4795757 := bstep (se 3 (by rfl) ⟨899204, by rfl⟩ : syracuseStep 4795757 = 1798409) B1798409
theorem B1895849 : Blo 1262449 1895849 := bstep (se 2 (by rfl) ⟨710943, by rfl⟩ : syracuseStep 1895849 = 1421887) B1421887
theorem B2133479 : Blo 1262449 2133479 := bstep (se 1 (by rfl) ⟨1600109, by rfl⟩ : syracuseStep 2133479 = 3200219) B3200219
theorem B2133499 : Blo 1262449 2133499 := bstep (se 1 (by rfl) ⟨1600124, by rfl⟩ : syracuseStep 2133499 = 3200249) B3200249
theorem B1895999 : Blo 1262449 1895999 := bstep (se 1 (by rfl) ⟨1421999, by rfl⟩ : syracuseStep 1895999 = 2843999) B2843999
theorem B1421095 : Blo 1262449 1421095 := bstep (se 1 (by rfl) ⟨1065821, by rfl⟩ : syracuseStep 1421095 = 2131643) B2131643
theorem B1896263 : Blo 1262449 1896263 := bstep (se 1 (by rfl) ⟨1422197, by rfl⟩ : syracuseStep 1896263 = 2844395) B2844395
theorem B4263785 : Blo 1262449 4263785 := bstep (se 2 (by rfl) ⟨1598919, by rfl⟩ : syracuseStep 4263785 = 3197839) B3197839
theorem B1896347 : Blo 1262449 1896347 := bstep (se 1 (by rfl) ⟨1422260, by rfl⟩ : syracuseStep 1896347 = 2844521) B2844521
theorem B32452757 : Blo 1262449 32452757 := bstep (se 6 (by rfl) ⟨760611, by rfl⟩ : syracuseStep 32452757 = 1521223) B1521223
theorem B1798375 : Blo 1262449 1798375 := bstep (se 1 (by rfl) ⟨1348781, by rfl⟩ : syracuseStep 1798375 = 2697563) B2697563
theorem B10801457 : Blo 1262449 10801457 := bstep (se 2 (by rfl) ⟨4050546, by rfl⟩ : syracuseStep 10801457 = 8101093) B8101093
theorem B4862375 : Blo 1262449 4862375 := bstep (se 1 (by rfl) ⟨3646781, by rfl⟩ : syracuseStep 4862375 = 7293563) B7293563
theorem B69194243 : Blo 1262449 69194243 := bstep (se 1 (by rfl) ⟨51895682, by rfl⟩ : syracuseStep 69194243 = 103791365) B103791365
theorem B3199571 : Blo 1262449 3199571 := bstep (se 1 (by rfl) ⟨2399678, by rfl⟩ : syracuseStep 3199571 = 4799357) B4799357
theorem B9597527 : Blo 1262449 9597527 := bstep (se 1 (by rfl) ⟨7198145, by rfl⟩ : syracuseStep 9597527 = 14396291) B14396291
theorem B6394463 : Blo 1262449 6394463 := bstep (se 1 (by rfl) ⟨4795847, by rfl⟩ : syracuseStep 6394463 = 9591695) B9591695
theorem B10949215 : Blo 1262449 10949215 := bstep (se 1 (by rfl) ⟨8211911, by rfl⟩ : syracuseStep 10949215 = 16423823) B16423823
theorem B1921639 : Blo 1262449 1921639 := bstep (se 1 (by rfl) ⟨1441229, by rfl⟩ : syracuseStep 1921639 = 2882459) B2882459
theorem B5919355 : Blo 1262449 5919355 := bstep (se 1 (by rfl) ⟨4439516, by rfl⟩ : syracuseStep 5919355 = 8879033) B8879033
theorem B10793735 : Blo 1262449 10793735 := bstep (se 1 (by rfl) ⟨8095301, by rfl⟩ : syracuseStep 10793735 = 16190603) B16190603
theorem B5395261 : Blo 1262449 5395261 := bstep (se 3 (by rfl) ⟨1011611, by rfl⟩ : syracuseStep 5395261 = 2023223) B2023223
theorem B1422247 : Blo 1262449 1422247 := bstep (se 1 (by rfl) ⟨1066685, by rfl⟩ : syracuseStep 1422247 = 2133371) B2133371
theorem B3413099 : Blo 1262449 3413099 := bstep (se 1 (by rfl) ⟨2559824, by rfl⟩ : syracuseStep 3413099 = 5119649) B5119649
theorem B1799275 : Blo 1262449 1799275 := bstep (se 1 (by rfl) ⟨1349456, by rfl⟩ : syracuseStep 1799275 = 2698913) B2698913
theorem B3200107 : Blo 1262449 3200107 := bstep (se 1 (by rfl) ⟨2400080, by rfl⟩ : syracuseStep 3200107 = 4800161) B4800161
theorem B4265135 : Blo 1262449 4265135 := bstep (se 1 (by rfl) ⟨3198851, by rfl⟩ : syracuseStep 4265135 = 6397703) B6397703
theorem B3200411 : Blo 1262449 3200411 := bstep (se 1 (by rfl) ⟨2400308, by rfl⟩ : syracuseStep 3200411 = 4800617) B4800617
theorem B18724441 : Blo 1262449 18724441 := bstep (se 2 (by rfl) ⟨7021665, by rfl⟩ : syracuseStep 18724441 = 14043331) B14043331
theorem B1848953 : Blo 1262449 1848953 := bstep (se 2 (by rfl) ⟨693357, by rfl⟩ : syracuseStep 1848953 = 1386715) B1386715
theorem B4798187 : Blo 1262449 4798187 := bstep (se 1 (by rfl) ⟨3598640, by rfl⟩ : syracuseStep 4798187 = 7197281) B7197281
theorem B2398015 : Blo 1262449 2398015 := bstep (se 1 (by rfl) ⟨1798511, by rfl⟩ : syracuseStep 2398015 = 3597023) B3597023
theorem B7190491 : Blo 1262449 7190491 := bstep (se 1 (by rfl) ⟨5392868, by rfl⟩ : syracuseStep 7190491 = 10785737) B10785737
theorem B13137913 : Blo 1262449 13137913 := bstep (se 2 (by rfl) ⟨4926717, by rfl⟩ : syracuseStep 13137913 = 9853435) B9853435
theorem B65640577 : Blo 1262449 65640577 := bstep (se 2 (by rfl) ⟨24615216, by rfl⟩ : syracuseStep 65640577 = 49230433) B49230433
theorem B10787377 : Blo 1262449 10787377 := bstep (se 2 (by rfl) ⟨4045266, by rfl⟩ : syracuseStep 10787377 = 8090533) B8090533
theorem B3414665 : Blo 1262449 3414665 := bstep (se 2 (by rfl) ⟨1280499, by rfl⟩ : syracuseStep 3414665 = 2560999) B2560999
theorem B2841551 : Blo 1262449 2841551 := bstep (se 1 (by rfl) ⟨2131163, by rfl⟩ : syracuseStep 2841551 = 4262327) B4262327
theorem B2841569 : Blo 1262449 2841569 := bstep (se 2 (by rfl) ⟨1065588, by rfl⟩ : syracuseStep 2841569 = 2131177) B2131177
theorem B2841641 : Blo 1262449 2841641 := bstep (se 2 (by rfl) ⟨1065615, by rfl⟩ : syracuseStep 2841641 = 2131231) B2131231
theorem B4324423 : Blo 1262449 4324423 := bstep (se 1 (by rfl) ⟨3243317, by rfl⟩ : syracuseStep 4324423 = 6486635) B6486635
theorem B4267079 : Blo 1262449 4267079 := bstep (se 1 (by rfl) ⟨3200309, by rfl⟩ : syracuseStep 4267079 = 6400619) B6400619
theorem B4267133 : Blo 1262449 4267133 := bstep (se 3 (by rfl) ⟨800087, by rfl⟩ : syracuseStep 4267133 = 1600175) B1600175
theorem B14400665 : Blo 1262449 14400665 := bstep (se 2 (by rfl) ⟨5400249, by rfl⟩ : syracuseStep 14400665 = 10800499) B10800499
theorem B4324535 : Blo 1262449 4324535 := bstep (se 1 (by rfl) ⟨3243401, by rfl⟩ : syracuseStep 4324535 = 6486803) B6486803
theorem B4267403 : Blo 1262449 4267403 := bstep (se 1 (by rfl) ⟨3200552, by rfl⟩ : syracuseStep 4267403 = 6401105) B6401105
theorem B2276819 : Blo 1262449 2276819 := bstep (se 1 (by rfl) ⟨1707614, by rfl⟩ : syracuseStep 2276819 = 3415229) B3415229
theorem B249077551 : Blo 1262449 249077551 := bstep (se 1 (by rfl) ⟨186808163, by rfl⟩ : syracuseStep 249077551 = 373616327) B373616327
theorem B4800343 : Blo 1262449 4800343 := bstep (se 1 (by rfl) ⟨3600257, by rfl⟩ : syracuseStep 4800343 = 7200515) B7200515
theorem B36437849 : Blo 1262449 36437849 := bstep (se 2 (by rfl) ⟨13664193, by rfl⟩ : syracuseStep 36437849 = 27328387) B27328387
theorem B21635171 : Blo 1262449 21635171 := bstep (se 1 (by rfl) ⟨16226378, by rfl⟩ : syracuseStep 21635171 = 32452757) B32452757
theorem B7200971 : Blo 1262449 7200971 := bstep (se 1 (by rfl) ⟨5400728, by rfl⟩ : syracuseStep 7200971 = 10801457) B10801457
theorem B2842937 : Blo 1262449 2842937 := bstep (se 2 (by rfl) ⟨1066101, by rfl⟩ : syracuseStep 2842937 = 2132203) B2132203
theorem B46129495 : Blo 1262449 46129495 := bstep (se 1 (by rfl) ⟨34597121, by rfl⟩ : syracuseStep 46129495 = 69194243) B69194243
theorem B6398351 : Blo 1262449 6398351 := bstep (se 1 (by rfl) ⟨4798763, by rfl⟩ : syracuseStep 6398351 = 9597527) B9597527
theorem B11682407 : Blo 1262449 11682407 := bstep (se 1 (by rfl) ⟨8761805, by rfl⟩ : syracuseStep 11682407 = 17523611) B17523611
theorem B2843423 : Blo 1262449 2843423 := bstep (se 1 (by rfl) ⟨2132567, by rfl⟩ : syracuseStep 2843423 = 4265135) B4265135
theorem B14598953 : Blo 1262449 14598953 := bstep (se 2 (by rfl) ⟨5474607, by rfl⟩ : syracuseStep 14598953 = 10949215) B10949215
theorem B2130887 : Blo 1262449 2130887 := bstep (se 1 (by rfl) ⟨1598165, by rfl⟩ : syracuseStep 2130887 = 3196331) B3196331
theorem B10519577 : Blo 1262449 10519577 := bstep (se 2 (by rfl) ⟨3944841, by rfl⟩ : syracuseStep 10519577 = 7889683) B7889683
theorem B10798109 : Blo 1262449 10798109 := bstep (se 3 (by rfl) ⟨2024645, by rfl⟩ : syracuseStep 10798109 = 4049291) B4049291
theorem B1262639 : Blo 1262449 1262639 := bstep (se 1 (by rfl) ⟨946979, by rfl⟩ : syracuseStep 1262639 = 1893959) B1893959
theorem B7193681 : Blo 1262449 7193681 := bstep (se 2 (by rfl) ⟨2697630, by rfl⟩ : syracuseStep 7193681 = 5395261) B5395261
theorem B1262703 : Blo 1262449 1262703 := bstep (se 1 (by rfl) ⟨947027, by rfl⟩ : syracuseStep 1262703 = 1894055) B1894055
theorem B1262759 : Blo 1262449 1262759 := bstep (se 1 (by rfl) ⟨947069, by rfl⟩ : syracuseStep 1262759 = 1894139) B1894139
theorem B1262783 : Blo 1262449 1262783 := bstep (se 1 (by rfl) ⟨947087, by rfl⟩ : syracuseStep 1262783 = 1894175) B1894175
theorem B1262815 : Blo 1262449 1262815 := bstep (se 1 (by rfl) ⟨947111, by rfl⟩ : syracuseStep 1262815 = 1894223) B1894223
theorem B1262895 : Blo 1262449 1262895 := bstep (se 1 (by rfl) ⟨947171, by rfl⟩ : syracuseStep 1262895 = 1894343) B1894343
theorem B1263131 : Blo 1262449 1263131 := bstep (se 1 (by rfl) ⟨947348, by rfl⟩ : syracuseStep 1263131 = 1894697) B1894697
theorem B1263135 : Blo 1262449 1263135 := bstep (se 1 (by rfl) ⟨947351, by rfl⟩ : syracuseStep 1263135 = 1894703) B1894703
theorem B2844233 : Blo 1262449 2844233 := bstep (se 2 (by rfl) ⟨1066587, by rfl⟩ : syracuseStep 2844233 = 2133175) B2133175
theorem B3196523 : Blo 1262449 3196523 := bstep (se 1 (by rfl) ⟨2397392, by rfl⟩ : syracuseStep 3196523 = 4794785) B4794785
theorem B1263295 : Blo 1262449 1263295 := bstep (se 1 (by rfl) ⟨947471, by rfl⟩ : syracuseStep 1263295 = 1894943) B1894943
theorem B2131751 : Blo 1262449 2131751 := bstep (se 1 (by rfl) ⟨1598813, by rfl⟩ : syracuseStep 2131751 = 3197627) B3197627
theorem B1263551 : Blo 1262449 1263551 := bstep (se 1 (by rfl) ⟨947663, by rfl⟩ : syracuseStep 1263551 = 1895327) B1895327
theorem B1894367 : Blo 1262449 1894367 := bstep (se 1 (by rfl) ⟨1420775, by rfl⟩ : syracuseStep 1894367 = 2841551) B2841551
theorem B1263583 : Blo 1262449 1263583 := bstep (se 1 (by rfl) ⟨947687, by rfl⟩ : syracuseStep 1263583 = 1895375) B1895375
theorem B1894379 : Blo 1262449 1894379 := bstep (se 1 (by rfl) ⟨1420784, by rfl⟩ : syracuseStep 1894379 = 2841569) B2841569
theorem B2844665 : Blo 1262449 2844665 := bstep (se 2 (by rfl) ⟨1066749, by rfl⟩ : syracuseStep 2844665 = 2133499) B2133499
theorem B157747213 : Blo 1262449 157747213 := bstep (se 3 (by rfl) ⟨29577602, by rfl⟩ : syracuseStep 157747213 = 59155205) B59155205
theorem B1894427 : Blo 1262449 1894427 := bstep (se 1 (by rfl) ⟨1420820, by rfl⟩ : syracuseStep 1894427 = 2841641) B2841641
theorem B1263643 : Blo 1262449 1263643 := bstep (se 1 (by rfl) ⟨947732, by rfl⟩ : syracuseStep 1263643 = 1895465) B1895465
theorem B1263647 : Blo 1262449 1263647 := bstep (se 1 (by rfl) ⟨947735, by rfl⟩ : syracuseStep 1263647 = 1895471) B1895471
theorem B1263663 : Blo 1262449 1263663 := bstep (se 1 (by rfl) ⟨947747, by rfl⟩ : syracuseStep 1263663 = 1895495) B1895495
theorem B2844719 : Blo 1262449 2844719 := bstep (se 1 (by rfl) ⟨2133539, by rfl⟩ : syracuseStep 2844719 = 4267079) B4267079
theorem B2844755 : Blo 1262449 2844755 := bstep (se 1 (by rfl) ⟨2133566, by rfl⟩ : syracuseStep 2844755 = 4267133) B4267133
theorem B18450611 : Blo 1262449 18450611 := bstep (se 1 (by rfl) ⟨13837958, by rfl⟩ : syracuseStep 18450611 = 27675917) B27675917
theorem B4262111 : Blo 1262449 4262111 := bstep (se 1 (by rfl) ⟨3196583, by rfl⟩ : syracuseStep 4262111 = 6393167) B6393167
theorem B1263839 : Blo 1262449 1263839 := bstep (se 1 (by rfl) ⟨947879, by rfl⟩ : syracuseStep 1263839 = 1895759) B1895759
theorem B3197171 : Blo 1262449 3197171 := bstep (se 1 (by rfl) ⟨2397878, by rfl⟩ : syracuseStep 3197171 = 4795757) B4795757
theorem B2844935 : Blo 1262449 2844935 := bstep (se 1 (by rfl) ⟨2133701, by rfl⟩ : syracuseStep 2844935 = 4267403) B4267403
theorem B1263899 : Blo 1262449 1263899 := bstep (se 1 (by rfl) ⟨947924, by rfl⟩ : syracuseStep 1263899 = 1895849) B1895849
theorem B1517879 : Blo 1262449 1517879 := bstep (se 1 (by rfl) ⟨1138409, by rfl⟩ : syracuseStep 1517879 = 2276819) B2276819
theorem B1263999 : Blo 1262449 1263999 := bstep (se 1 (by rfl) ⟨947999, by rfl⟩ : syracuseStep 1263999 = 1895999) B1895999
theorem B1894793 : Blo 1262449 1894793 := bstep (se 2 (by rfl) ⟨710547, by rfl⟩ : syracuseStep 1894793 = 1421095) B1421095
theorem B3197353 : Blo 1262449 3197353 := bstep (se 2 (by rfl) ⟨1199007, by rfl⟩ : syracuseStep 3197353 = 2398015) B2398015
theorem B6400457 : Blo 1262449 6400457 := bstep (se 2 (by rfl) ⟨2400171, by rfl⟩ : syracuseStep 6400457 = 4800343) B4800343
theorem B1264175 : Blo 1262449 1264175 := bstep (se 1 (by rfl) ⟨948131, by rfl⟩ : syracuseStep 1264175 = 1896263) B1896263
theorem B24291899 : Blo 1262449 24291899 := bstep (se 1 (by rfl) ⟨18218924, by rfl⟩ : syracuseStep 24291899 = 36437849) B36437849
theorem B1264231 : Blo 1262449 1264231 := bstep (se 1 (by rfl) ⟨948173, by rfl⟩ : syracuseStep 1264231 = 1896347) B1896347
theorem B9587321 : Blo 1262449 9587321 := bstep (se 2 (by rfl) ⟨3595245, by rfl⟩ : syracuseStep 9587321 = 7190491) B7190491
theorem B17517217 : Blo 1262449 17517217 := bstep (se 2 (by rfl) ⟨6568956, by rfl⟩ : syracuseStep 17517217 = 13137913) B13137913
theorem B2132777 : Blo 1262449 2132777 := bstep (se 2 (by rfl) ⟨799791, by rfl⟩ : syracuseStep 2132777 = 1599583) B1599583
theorem B2132905 : Blo 1262449 2132905 := bstep (se 2 (by rfl) ⟨799839, by rfl⟩ : syracuseStep 2132905 = 1599679) B1599679
theorem B2133047 : Blo 1262449 2133047 := bstep (se 1 (by rfl) ⟨1599785, by rfl⟩ : syracuseStep 2133047 = 3199571) B3199571
theorem B4262975 : Blo 1262449 4262975 := bstep (se 1 (by rfl) ⟨3197231, by rfl⟩ : syracuseStep 4262975 = 6394463) B6394463
theorem B36416627 : Blo 1262449 36416627 := bstep (se 1 (by rfl) ⟨27312470, by rfl⟩ : syracuseStep 36416627 = 54624941) B54624941
theorem B2698409 : Blo 1262449 2698409 := bstep (se 2 (by rfl) ⟨1011903, by rfl⟩ : syracuseStep 2698409 = 2023807) B2023807
theorem B7195823 : Blo 1262449 7195823 := bstep (se 1 (by rfl) ⟨5396867, by rfl⟩ : syracuseStep 7195823 = 10793735) B10793735
theorem B14380253 : Blo 1262449 14380253 := bstep (se 3 (by rfl) ⟨2696297, by rfl⟩ : syracuseStep 14380253 = 5392595) B5392595
theorem B6401267 : Blo 1262449 6401267 := bstep (se 1 (by rfl) ⟨4800950, by rfl⟩ : syracuseStep 6401267 = 9601901) B9601901
theorem B1895735 : Blo 1262449 1895735 := bstep (se 1 (by rfl) ⟨1421801, by rfl⟩ : syracuseStep 1895735 = 2843603) B2843603
theorem B1420699 : Blo 1262449 1420699 := bstep (se 1 (by rfl) ⟨1065524, by rfl⟩ : syracuseStep 1420699 = 2131049) B2131049
theorem B1895903 : Blo 1262449 1895903 := bstep (se 1 (by rfl) ⟨1421927, by rfl⟩ : syracuseStep 1895903 = 2843855) B2843855
theorem B7892473 : Blo 1262449 7892473 := bstep (se 2 (by rfl) ⟨2959677, by rfl⟩ : syracuseStep 7892473 = 5919355) B5919355
theorem B8097353 : Blo 1262449 8097353 := bstep (se 2 (by rfl) ⟨3036507, by rfl⟩ : syracuseStep 8097353 = 6073015) B6073015
theorem B2133607 : Blo 1262449 2133607 := bstep (se 1 (by rfl) ⟨1600205, by rfl⟩ : syracuseStep 2133607 = 3200411) B3200411
theorem B2698895 : Blo 1262449 2698895 := bstep (se 1 (by rfl) ⟨2024171, by rfl⟩ : syracuseStep 2698895 = 4048343) B4048343
theorem B1896119 : Blo 1262449 1896119 := bstep (se 1 (by rfl) ⟨1422089, by rfl⟩ : syracuseStep 1896119 = 2844179) B2844179
theorem B3198791 : Blo 1262449 3198791 := bstep (se 1 (by rfl) ⟨2399093, by rfl⟩ : syracuseStep 3198791 = 4798187) B4798187
theorem B1896329 : Blo 1262449 1896329 := bstep (se 2 (by rfl) ⟨711123, by rfl⟩ : syracuseStep 1896329 = 1422247) B1422247
theorem B11677733 : Blo 1262449 11677733 := bstep (se 4 (by rfl) ⟨1094787, by rfl⟩ : syracuseStep 11677733 = 2189575) B2189575
theorem B1896575 : Blo 1262449 1896575 := bstep (se 1 (by rfl) ⟨1422431, by rfl⟩ : syracuseStep 1896575 = 2844863) B2844863
theorem B1421671 : Blo 1262449 1421671 := bstep (se 1 (by rfl) ⟨1066253, by rfl⟩ : syracuseStep 1421671 = 2132507) B2132507
theorem B10253051 : Blo 1262449 10253051 := bstep (se 1 (by rfl) ⟨7689788, by rfl⟩ : syracuseStep 10253051 = 15379577) B15379577
theorem B24965921 : Blo 1262449 24965921 := bstep (se 2 (by rfl) ⟨9362220, by rfl⟩ : syracuseStep 24965921 = 18724441) B18724441
theorem B1422319 : Blo 1262449 1422319 := bstep (se 1 (by rfl) ⟨1066739, by rfl⟩ : syracuseStep 1422319 = 2133479) B2133479
theorem B2561519 : Blo 1262449 2561519 := bstep (se 1 (by rfl) ⟨1921139, by rfl⟩ : syracuseStep 2561519 = 3842279) B3842279
theorem B87520769 : Blo 1262449 87520769 := bstep (se 2 (by rfl) ⟨32820288, by rfl⟩ : syracuseStep 87520769 = 65640577) B65640577
theorem B3241583 : Blo 1262449 3241583 := bstep (se 1 (by rfl) ⟨2431187, by rfl⟩ : syracuseStep 3241583 = 4862375) B4862375
theorem B2397833 : Blo 1262449 2397833 := bstep (se 2 (by rfl) ⟨899187, by rfl⟩ : syracuseStep 2397833 = 1798375) B1798375
theorem B2397863 : Blo 1262449 2397863 := bstep (se 1 (by rfl) ⟨1798397, by rfl⟩ : syracuseStep 2397863 = 3596795) B3596795
theorem B9721579 : Blo 1262449 9721579 := bstep (se 1 (by rfl) ⟨7291184, by rfl⟩ : syracuseStep 9721579 = 14582369) B14582369
theorem B5396219 : Blo 1262449 5396219 := bstep (se 1 (by rfl) ⟨4047164, by rfl⟩ : syracuseStep 5396219 = 8094329) B8094329
theorem B7395067 : Blo 1262449 7395067 := bstep (se 1 (by rfl) ⟨5546300, by rfl⟩ : syracuseStep 7395067 = 11092601) B11092601
theorem B2840615 : Blo 1262449 2840615 := bstep (se 1 (by rfl) ⟨2130461, by rfl⟩ : syracuseStep 2840615 = 4260923) B4260923
theorem B14383169 : Blo 1262449 14383169 := bstep (se 2 (by rfl) ⟨5393688, by rfl⟩ : syracuseStep 14383169 = 10787377) B10787377
theorem B2275399 : Blo 1262449 2275399 := bstep (se 1 (by rfl) ⟨1706549, by rfl⟩ : syracuseStep 2275399 = 3413099) B3413099
theorem B2562185 : Blo 1262449 2562185 := bstep (se 2 (by rfl) ⟨960819, by rfl⟩ : syracuseStep 2562185 = 1921639) B1921639
theorem B2840795 : Blo 1262449 2840795 := bstep (se 1 (by rfl) ⟨2130596, by rfl⟩ : syracuseStep 2840795 = 4261193) B4261193
theorem B7199057 : Blo 1262449 7199057 := bstep (se 2 (by rfl) ⟨2699646, by rfl⟩ : syracuseStep 7199057 = 5399293) B5399293
theorem B2398547 : Blo 1262449 2398547 := bstep (se 1 (by rfl) ⟨1798910, by rfl⟩ : syracuseStep 2398547 = 3597821) B3597821
theorem B2840993 : Blo 1262449 2840993 := bstep (se 2 (by rfl) ⟨1065372, by rfl⟩ : syracuseStep 2840993 = 2130745) B2130745
theorem B2841065 : Blo 1262449 2841065 := bstep (se 2 (by rfl) ⟨1065399, by rfl⟩ : syracuseStep 2841065 = 2130799) B2130799
theorem B5396969 : Blo 1262449 5396969 := bstep (se 2 (by rfl) ⟨2023863, by rfl⟩ : syracuseStep 5396969 = 4047727) B4047727
theorem B2734697 : Blo 1262449 2734697 := bstep (se 2 (by rfl) ⟨1025511, by rfl⟩ : syracuseStep 2734697 = 2051023) B2051023
theorem B5765897 : Blo 1262449 5765897 := bstep (se 2 (by rfl) ⟨2162211, by rfl⟩ : syracuseStep 5765897 = 4324423) B4324423
theorem B2399033 : Blo 1262449 2399033 := bstep (se 2 (by rfl) ⟨899637, by rfl⟩ : syracuseStep 2399033 = 1799275) B1799275
theorem B4266809 : Blo 1262449 4266809 := bstep (se 2 (by rfl) ⟨1600053, by rfl⟩ : syracuseStep 4266809 = 3200107) B3200107
theorem B10787651 : Blo 1262449 10787651 := bstep (se 1 (by rfl) ⟨8090738, by rfl⟩ : syracuseStep 10787651 = 16181477) B16181477
theorem B26270569 : Blo 1262449 26270569 := bstep (se 2 (by rfl) ⟨9851463, by rfl⟩ : syracuseStep 26270569 = 19702927) B19702927
theorem B4930541 : Blo 1262449 4930541 := bstep (se 3 (by rfl) ⟨924476, by rfl⟩ : syracuseStep 4930541 = 1848953) B1848953
theorem B2276443 : Blo 1262449 2276443 := bstep (se 1 (by rfl) ⟨1707332, by rfl⟩ : syracuseStep 2276443 = 3414665) B3414665
theorem B9600443 : Blo 1262449 9600443 := bstep (se 1 (by rfl) ⟨7200332, by rfl⟩ : syracuseStep 9600443 = 14400665) B14400665
theorem B2883023 : Blo 1262449 2883023 := bstep (se 1 (by rfl) ⟨2162267, by rfl⟩ : syracuseStep 2883023 = 4324535) B4324535
theorem B17522153 : Blo 1262449 17522153 := bstep (se 2 (by rfl) ⟨6570807, by rfl⟩ : syracuseStep 17522153 = 13141615) B13141615
theorem B332103401 : Blo 1262449 332103401 := bstep (se 2 (by rfl) ⟨124538775, by rfl⟩ : syracuseStep 332103401 = 249077551) B249077551
theorem B2842523 : Blo 1262449 2842523 := bstep (se 1 (by rfl) ⟨2131892, by rfl⟩ : syracuseStep 2842523 = 4263785) B4263785
theorem B210329617 : Blo 1262449 210329617 := bstep (se 2 (by rfl) ⟨78873606, by rfl⟩ : syracuseStep 210329617 = 157747213) B157747213
theorem B4800647 : Blo 1262449 4800647 := bstep (se 1 (by rfl) ⟨3600485, by rfl⟩ : syracuseStep 4800647 = 7200971) B7200971
theorem B61505993 : Blo 1262449 61505993 := bstep (se 2 (by rfl) ⟨23064747, by rfl⟩ : syracuseStep 61505993 = 46129495) B46129495
theorem B12141029 : Blo 1262449 12141029 := bstep (se 4 (by rfl) ⟨1138221, by rfl⟩ : syracuseStep 12141029 = 2276443) B2276443
theorem B9732635 : Blo 1262449 9732635 := bstep (se 1 (by rfl) ⟨7299476, by rfl⟩ : syracuseStep 9732635 = 14598953) B14598953
theorem B7013051 : Blo 1262449 7013051 := bstep (se 1 (by rfl) ⟨5259788, by rfl⟩ : syracuseStep 7013051 = 10519577) B10519577
theorem B4047677 : Blo 1262449 4047677 := bstep (se 3 (by rfl) ⟨758939, by rfl⟩ : syracuseStep 4047677 = 1517879) B1517879
theorem B23356289 : Blo 1262449 23356289 := bstep (se 2 (by rfl) ⟨8758608, by rfl⟩ : syracuseStep 23356289 = 17517217) B17517217
theorem B2131015 : Blo 1262449 2131015 := bstep (se 1 (by rfl) ⟨1598261, by rfl⟩ : syracuseStep 2131015 = 3196523) B3196523
theorem B1598555 : Blo 1262449 1598555 := bstep (se 1 (by rfl) ⟨1198916, by rfl⟩ : syracuseStep 1598555 = 2397833) B2397833
theorem B3597479 : Blo 1262449 3597479 := bstep (se 1 (by rfl) ⟨2698109, by rfl⟩ : syracuseStep 3597479 = 5396219) B5396219
theorem B2843873 : Blo 1262449 2843873 := bstep (se 2 (by rfl) ⟨1066452, by rfl⟩ : syracuseStep 2843873 = 2132905) B2132905
theorem B1262911 : Blo 1262449 1262911 := bstep (se 1 (by rfl) ⟨947183, by rfl⟩ : syracuseStep 1262911 = 1894367) B1894367
theorem B1262919 : Blo 1262449 1262919 := bstep (se 1 (by rfl) ⟨947189, by rfl⟩ : syracuseStep 1262919 = 1894379) B1894379
theorem B1262951 : Blo 1262449 1262951 := bstep (se 1 (by rfl) ⟨947213, by rfl⟩ : syracuseStep 1262951 = 1894427) B1894427
theorem B1893743 : Blo 1262449 1893743 := bstep (se 1 (by rfl) ⟨1420307, by rfl⟩ : syracuseStep 1893743 = 2840615) B2840615
theorem B1893863 : Blo 1262449 1893863 := bstep (se 1 (by rfl) ⟨1420397, by rfl⟩ : syracuseStep 1893863 = 2840795) B2840795
theorem B2131447 : Blo 1262449 2131447 := bstep (se 1 (by rfl) ⟨1598585, by rfl⟩ : syracuseStep 2131447 = 3197171) B3197171
theorem B1599031 : Blo 1262449 1599031 := bstep (se 1 (by rfl) ⟨1199273, by rfl⟩ : syracuseStep 1599031 = 2398547) B2398547
theorem B1263195 : Blo 1262449 1263195 := bstep (se 1 (by rfl) ⟨947396, by rfl⟩ : syracuseStep 1263195 = 1894793) B1894793
theorem B1893995 : Blo 1262449 1893995 := bstep (se 1 (by rfl) ⟨1420496, by rfl⟩ : syracuseStep 1893995 = 2840993) B2840993
theorem B1894043 : Blo 1262449 1894043 := bstep (se 1 (by rfl) ⟨1420532, by rfl⟩ : syracuseStep 1894043 = 2841065) B2841065
theorem B6391547 : Blo 1262449 6391547 := bstep (se 1 (by rfl) ⟨4793660, by rfl⟩ : syracuseStep 6391547 = 9587321) B9587321
theorem B3843931 : Blo 1262449 3843931 := bstep (se 1 (by rfl) ⟨2882948, by rfl⟩ : syracuseStep 3843931 = 5765897) B5765897
theorem B1894265 : Blo 1262449 1894265 := bstep (se 2 (by rfl) ⟨710349, by rfl⟩ : syracuseStep 1894265 = 1420699) B1420699
theorem B1599355 : Blo 1262449 1599355 := bstep (se 1 (by rfl) ⟨1199516, by rfl⟩ : syracuseStep 1599355 = 2399033) B2399033
theorem B2844539 : Blo 1262449 2844539 := bstep (se 1 (by rfl) ⟨2133404, by rfl⟩ : syracuseStep 2844539 = 4266809) B4266809
theorem B3287027 : Blo 1262449 3287027 := bstep (se 1 (by rfl) ⟨2465270, by rfl⟩ : syracuseStep 3287027 = 4930541) B4930541
theorem B2844809 : Blo 1262449 2844809 := bstep (se 2 (by rfl) ⟨1066803, by rfl⟩ : syracuseStep 2844809 = 2133607) B2133607
theorem B9586835 : Blo 1262449 9586835 := bstep (se 1 (by rfl) ⟨7190126, by rfl⟩ : syracuseStep 9586835 = 14380253) B14380253
theorem B1263823 : Blo 1262449 1263823 := bstep (se 1 (by rfl) ⟨947867, by rfl⟩ : syracuseStep 1263823 = 1895735) B1895735
theorem B6400295 : Blo 1262449 6400295 := bstep (se 1 (by rfl) ⟨4800221, by rfl⟩ : syracuseStep 6400295 = 9600443) B9600443
theorem B12962105 : Blo 1262449 12962105 := bstep (se 2 (by rfl) ⟨4860789, by rfl⟩ : syracuseStep 12962105 = 9721579) B9721579
theorem B1263935 : Blo 1262449 1263935 := bstep (se 1 (by rfl) ⟨947951, by rfl⟩ : syracuseStep 1263935 = 1895903) B1895903
theorem B1264079 : Blo 1262449 1264079 := bstep (se 1 (by rfl) ⟨948059, by rfl⟩ : syracuseStep 1264079 = 1896119) B1896119
theorem B2132527 : Blo 1262449 2132527 := bstep (se 1 (by rfl) ⟨1599395, by rfl⟩ : syracuseStep 2132527 = 3198791) B3198791
theorem B1264219 : Blo 1262449 1264219 := bstep (se 1 (by rfl) ⟨948164, by rfl⟩ : syracuseStep 1264219 = 1896329) B1896329
theorem B1895015 : Blo 1262449 1895015 := bstep (se 1 (by rfl) ⟨1421261, by rfl⟩ : syracuseStep 1895015 = 2842523) B2842523
theorem B7785155 : Blo 1262449 7785155 := bstep (se 1 (by rfl) ⟨5838866, by rfl⟩ : syracuseStep 7785155 = 11677733) B11677733
theorem B1264383 : Blo 1262449 1264383 := bstep (se 1 (by rfl) ⟨948287, by rfl⟩ : syracuseStep 1264383 = 1896575) B1896575
theorem B3033865 : Blo 1262449 3033865 := bstep (se 2 (by rfl) ⟨1137699, by rfl⟩ : syracuseStep 3033865 = 2275399) B2275399
theorem B1895291 : Blo 1262449 1895291 := bstep (se 1 (by rfl) ⟨1421468, by rfl⟩ : syracuseStep 1895291 = 2842937) B2842937
theorem B1895561 : Blo 1262449 1895561 := bstep (se 2 (by rfl) ⟨710835, by rfl⟩ : syracuseStep 1895561 = 1421671) B1421671
theorem B6835367 : Blo 1262449 6835367 := bstep (se 1 (by rfl) ⟨5126525, by rfl⟩ : syracuseStep 6835367 = 10253051) B10253051
theorem B1895615 : Blo 1262449 1895615 := bstep (se 1 (by rfl) ⟨1421711, by rfl⟩ : syracuseStep 1895615 = 2843423) B2843423
theorem B4263137 : Blo 1262449 4263137 := bstep (se 2 (by rfl) ⟨1598676, by rfl⟩ : syracuseStep 4263137 = 3197353) B3197353
theorem B1420591 : Blo 1262449 1420591 := bstep (se 1 (by rfl) ⟨1065443, by rfl⟩ : syracuseStep 1420591 = 2130887) B2130887
theorem B4795787 : Blo 1262449 4795787 := bstep (se 1 (by rfl) ⟨3596840, by rfl⟩ : syracuseStep 4795787 = 7193681) B7193681
theorem B1707679 : Blo 1262449 1707679 := bstep (se 1 (by rfl) ⟨1280759, by rfl⟩ : syracuseStep 1707679 = 2561519) B2561519
theorem B58347179 : Blo 1262449 58347179 := bstep (se 1 (by rfl) ⟨43760384, by rfl⟩ : syracuseStep 58347179 = 87520769) B87520769
theorem B1896155 : Blo 1262449 1896155 := bstep (se 1 (by rfl) ⟨1422116, by rfl⟩ : syracuseStep 1896155 = 2844233) B2844233
theorem B1421167 : Blo 1262449 1421167 := bstep (se 1 (by rfl) ⟨1065875, by rfl⟩ : syracuseStep 1421167 = 2131751) B2131751
theorem B39440357 : Blo 1262449 39440357 := bstep (se 4 (by rfl) ⟨3697533, by rfl⟩ : syracuseStep 39440357 = 7395067) B7395067
theorem B1896425 : Blo 1262449 1896425 := bstep (se 2 (by rfl) ⟨711159, by rfl⟩ : syracuseStep 1896425 = 1422319) B1422319
theorem B1896443 : Blo 1262449 1896443 := bstep (se 1 (by rfl) ⟨1422332, by rfl⟩ : syracuseStep 1896443 = 2844665) B2844665
theorem B1896479 : Blo 1262449 1896479 := bstep (se 1 (by rfl) ⟨1422359, by rfl⟩ : syracuseStep 1896479 = 2844719) B2844719
theorem B9588779 : Blo 1262449 9588779 := bstep (se 1 (by rfl) ⟨7191584, by rfl⟩ : syracuseStep 9588779 = 14383169) B14383169
theorem B1896503 : Blo 1262449 1896503 := bstep (se 1 (by rfl) ⟨1422377, by rfl⟩ : syracuseStep 1896503 = 2844755) B2844755
theorem B1708123 : Blo 1262449 1708123 := bstep (se 1 (by rfl) ⟨1281092, by rfl⟩ : syracuseStep 1708123 = 2562185) B2562185
theorem B12300407 : Blo 1262449 12300407 := bstep (se 1 (by rfl) ⟨9225305, by rfl⟩ : syracuseStep 12300407 = 18450611) B18450611
theorem B1896623 : Blo 1262449 1896623 := bstep (se 1 (by rfl) ⟨1422467, by rfl⟩ : syracuseStep 1896623 = 2844935) B2844935
theorem B1823131 : Blo 1262449 1823131 := bstep (se 1 (by rfl) ⟨1367348, by rfl⟩ : syracuseStep 1823131 = 2734697) B2734697
theorem B6394301 : Blo 1262449 6394301 := bstep (se 3 (by rfl) ⟨1198931, by rfl⟩ : syracuseStep 6394301 = 2397863) B2397863
theorem B1421851 : Blo 1262449 1421851 := bstep (se 1 (by rfl) ⟨1066388, by rfl⟩ : syracuseStep 1421851 = 2132777) B2132777
theorem B10523297 : Blo 1262449 10523297 := bstep (se 2 (by rfl) ⟨3946236, by rfl⟩ : syracuseStep 10523297 = 7892473) B7892473
theorem B1422031 : Blo 1262449 1422031 := bstep (se 1 (by rfl) ⟨1066523, by rfl⟩ : syracuseStep 1422031 = 2133047) B2133047
theorem B24277751 : Blo 1262449 24277751 := bstep (se 1 (by rfl) ⟨18208313, by rfl⟩ : syracuseStep 24277751 = 36416627) B36416627
theorem B1798939 : Blo 1262449 1798939 := bstep (se 1 (by rfl) ⟨1349204, by rfl⟩ : syracuseStep 1798939 = 2698409) B2698409
theorem B4797215 : Blo 1262449 4797215 := bstep (se 1 (by rfl) ⟨3597911, by rfl⟩ : syracuseStep 4797215 = 7195823) B7195823
theorem B1922015 : Blo 1262449 1922015 := bstep (se 1 (by rfl) ⟨1441511, by rfl⟩ : syracuseStep 1922015 = 2883023) B2883023
theorem B1799263 : Blo 1262449 1799263 := bstep (se 1 (by rfl) ⟨1349447, by rfl⟩ : syracuseStep 1799263 = 2698895) B2698895
theorem B221402267 : Blo 1262449 221402267 := bstep (se 1 (by rfl) ⟨166051700, by rfl⟩ : syracuseStep 221402267 = 332103401) B332103401
theorem B14423447 : Blo 1262449 14423447 := bstep (se 1 (by rfl) ⟨10817585, by rfl⟩ : syracuseStep 14423447 = 21635171) B21635171
theorem B4265567 : Blo 1262449 4265567 := bstep (se 1 (by rfl) ⟨3199175, by rfl⟩ : syracuseStep 4265567 = 6398351) B6398351
theorem B7198739 : Blo 1262449 7198739 := bstep (se 1 (by rfl) ⟨5399054, by rfl⟩ : syracuseStep 7198739 = 10798109) B10798109
theorem B2161055 : Blo 1262449 2161055 := bstep (se 1 (by rfl) ⟨1620791, by rfl⟩ : syracuseStep 2161055 = 3241583) B3241583
theorem B35027425 : Blo 1262449 35027425 := bstep (se 2 (by rfl) ⟨13135284, by rfl⟩ : syracuseStep 35027425 = 26270569) B26270569
theorem B14391917 : Blo 1262449 14391917 := bstep (se 3 (by rfl) ⟨2698484, by rfl⟩ : syracuseStep 14391917 = 5396969) B5396969
theorem B2841407 : Blo 1262449 2841407 := bstep (se 1 (by rfl) ⟨2131055, by rfl⟩ : syracuseStep 2841407 = 4262111) B4262111
theorem B4799371 : Blo 1262449 4799371 := bstep (se 1 (by rfl) ⟨3599528, by rfl⟩ : syracuseStep 4799371 = 7199057) B7199057
theorem B31153085 : Blo 1262449 31153085 := bstep (se 3 (by rfl) ⟨5841203, by rfl⟩ : syracuseStep 31153085 = 11682407) B11682407
theorem B4266971 : Blo 1262449 4266971 := bstep (se 1 (by rfl) ⟨3200228, by rfl⟩ : syracuseStep 4266971 = 6400457) B6400457
theorem B16194599 : Blo 1262449 16194599 := bstep (se 1 (by rfl) ⟨12145949, by rfl⟩ : syracuseStep 16194599 = 24291899) B24291899
theorem B7191767 : Blo 1262449 7191767 := bstep (se 1 (by rfl) ⟨5393825, by rfl⟩ : syracuseStep 7191767 = 10787651) B10787651
theorem B2841983 : Blo 1262449 2841983 := bstep (se 1 (by rfl) ⟨2131487, by rfl⟩ : syracuseStep 2841983 = 4262975) B4262975
theorem B66575789 : Blo 1262449 66575789 := bstep (se 3 (by rfl) ⟨12482960, by rfl⟩ : syracuseStep 66575789 = 24965921) B24965921
theorem B4267511 : Blo 1262449 4267511 := bstep (se 1 (by rfl) ⟨3200633, by rfl⟩ : syracuseStep 4267511 = 6401267) B6401267
theorem B11681435 : Blo 1262449 11681435 := bstep (se 1 (by rfl) ⟨8761076, by rfl⟩ : syracuseStep 11681435 = 17522153) B17522153
theorem B5398235 : Blo 1262449 5398235 := bstep (se 1 (by rfl) ⟨4048676, by rfl⟩ : syracuseStep 5398235 = 8097353) B8097353
theorem B8200271 : Blo 1262449 8200271 := bstep (se 1 (by rfl) ⟨6150203, by rfl⟩ : syracuseStep 8200271 = 12300407) B12300407
theorem B2277497 : Blo 1262449 2277497 := bstep (se 2 (by rfl) ⟨854061, by rfl⟩ : syracuseStep 2277497 = 1708123) B1708123
theorem B8094019 : Blo 1262449 8094019 := bstep (se 1 (by rfl) ⟨6070514, by rfl⟩ : syracuseStep 8094019 = 12141029) B12141029
theorem B6488423 : Blo 1262449 6488423 := bstep (se 1 (by rfl) ⟨4866317, by rfl⟩ : syracuseStep 6488423 = 9732635) B9732635
theorem B46703233 : Blo 1262449 46703233 := bstep (se 2 (by rfl) ⟨17513712, by rfl⟩ : syracuseStep 46703233 = 35027425) B35027425
theorem B2843369 : Blo 1262449 2843369 := bstep (se 2 (by rfl) ⟨1066263, by rfl⟩ : syracuseStep 2843369 = 2132527) B2132527
theorem B1262495 : Blo 1262449 1262495 := bstep (se 1 (by rfl) ⟨946871, by rfl⟩ : syracuseStep 1262495 = 1893743) B1893743
theorem B1262575 : Blo 1262449 1262575 := bstep (se 1 (by rfl) ⟨946931, by rfl⟩ : syracuseStep 1262575 = 1893863) B1893863
theorem B2843711 : Blo 1262449 2843711 := bstep (se 1 (by rfl) ⟨2132783, by rfl⟩ : syracuseStep 2843711 = 4265567) B4265567
theorem B1262663 : Blo 1262449 1262663 := bstep (se 1 (by rfl) ⟨946997, by rfl⟩ : syracuseStep 1262663 = 1893995) B1893995
theorem B1262695 : Blo 1262449 1262695 := bstep (se 1 (by rfl) ⟨947021, by rfl⟩ : syracuseStep 1262695 = 1894043) B1894043
theorem B4261031 : Blo 1262449 4261031 := bstep (se 1 (by rfl) ⟨3195773, by rfl⟩ : syracuseStep 4261031 = 6391547) B6391547
theorem B6399161 : Blo 1262449 6399161 := bstep (se 2 (by rfl) ⟨2399685, by rfl⟩ : syracuseStep 6399161 = 4799371) B4799371
theorem B1262843 : Blo 1262449 1262843 := bstep (se 1 (by rfl) ⟨947132, by rfl⟩ : syracuseStep 1262843 = 1894265) B1894265
theorem B6391223 : Blo 1262449 6391223 := bstep (se 1 (by rfl) ⟨4793417, by rfl⟩ : syracuseStep 6391223 = 9586835) B9586835
theorem B1894121 : Blo 1262449 1894121 := bstep (se 2 (by rfl) ⟨710295, by rfl⟩ : syracuseStep 1894121 = 1420591) B1420591
theorem B1263343 : Blo 1262449 1263343 := bstep (se 1 (by rfl) ⟨947507, by rfl⟩ : syracuseStep 1263343 = 1895015) B1895015
theorem B9594611 : Blo 1262449 9594611 := bstep (se 1 (by rfl) ⟨7195958, by rfl⟩ : syracuseStep 9594611 = 14391917) B14391917
theorem B1894271 : Blo 1262449 1894271 := bstep (se 1 (by rfl) ⟨1420703, by rfl⟩ : syracuseStep 1894271 = 2841407) B2841407
theorem B1263527 : Blo 1262449 1263527 := bstep (se 1 (by rfl) ⟨947645, by rfl⟩ : syracuseStep 1263527 = 1895291) B1895291
theorem B20768723 : Blo 1262449 20768723 := bstep (se 1 (by rfl) ⟨15576542, by rfl⟩ : syracuseStep 20768723 = 31153085) B31153085
theorem B2844647 : Blo 1262449 2844647 := bstep (se 1 (by rfl) ⟨2133485, by rfl⟩ : syracuseStep 2844647 = 4266971) B4266971
theorem B2132041 : Blo 1262449 2132041 := bstep (se 2 (by rfl) ⟨799515, by rfl⟩ : syracuseStep 2132041 = 1599031) B1599031
theorem B1263707 : Blo 1262449 1263707 := bstep (se 1 (by rfl) ⟨947780, by rfl⟩ : syracuseStep 1263707 = 1895561) B1895561
theorem B4556911 : Blo 1262449 4556911 := bstep (se 1 (by rfl) ⟨3417683, by rfl⟩ : syracuseStep 4556911 = 6835367) B6835367
theorem B1263743 : Blo 1262449 1263743 := bstep (se 1 (by rfl) ⟨947807, by rfl⟩ : syracuseStep 1263743 = 1895615) B1895615
theorem B4794511 : Blo 1262449 4794511 := bstep (se 1 (by rfl) ⟨3595883, by rfl⟩ : syracuseStep 4794511 = 7191767) B7191767
theorem B1894655 : Blo 1262449 1894655 := bstep (se 1 (by rfl) ⟨1420991, by rfl⟩ : syracuseStep 1894655 = 2841983) B2841983
theorem B3197191 : Blo 1262449 3197191 := bstep (se 1 (by rfl) ⟨2397893, by rfl⟩ : syracuseStep 3197191 = 4795787) B4795787
theorem B2845007 : Blo 1262449 2845007 := bstep (se 1 (by rfl) ⟨2133755, by rfl⟩ : syracuseStep 2845007 = 4267511) B4267511
theorem B38898119 : Blo 1262449 38898119 := bstep (se 1 (by rfl) ⟨29173589, by rfl⟩ : syracuseStep 38898119 = 58347179) B58347179
theorem B3598823 : Blo 1262449 3598823 := bstep (se 1 (by rfl) ⟨2699117, by rfl⟩ : syracuseStep 3598823 = 5398235) B5398235
theorem B1264103 : Blo 1262449 1264103 := bstep (se 1 (by rfl) ⟨948077, by rfl⟩ : syracuseStep 1264103 = 1896155) B1896155
theorem B1894889 : Blo 1262449 1894889 := bstep (se 2 (by rfl) ⟨710583, by rfl⟩ : syracuseStep 1894889 = 1421167) B1421167
theorem B2132473 : Blo 1262449 2132473 := bstep (se 2 (by rfl) ⟨799677, by rfl⟩ : syracuseStep 2132473 = 1599355) B1599355
theorem B1264283 : Blo 1262449 1264283 := bstep (se 1 (by rfl) ⟨948212, by rfl⟩ : syracuseStep 1264283 = 1896425) B1896425
theorem B1264295 : Blo 1262449 1264295 := bstep (se 1 (by rfl) ⟨948221, by rfl⟩ : syracuseStep 1264295 = 1896443) B1896443
theorem B1264319 : Blo 1262449 1264319 := bstep (se 1 (by rfl) ⟨948239, by rfl⟩ : syracuseStep 1264319 = 1896479) B1896479
theorem B280439489 : Blo 1262449 280439489 := bstep (se 2 (by rfl) ⟨105164808, by rfl⟩ : syracuseStep 280439489 = 210329617) B210329617
theorem B6392519 : Blo 1262449 6392519 := bstep (se 1 (by rfl) ⟨4794389, by rfl⟩ : syracuseStep 6392519 = 9588779) B9588779
theorem B1264335 : Blo 1262449 1264335 := bstep (se 1 (by rfl) ⟨948251, by rfl⟩ : syracuseStep 1264335 = 1896503) B1896503
theorem B1264415 : Blo 1262449 1264415 := bstep (se 1 (by rfl) ⟨948311, by rfl⟩ : syracuseStep 1264415 = 1896623) B1896623
theorem B4262813 : Blo 1262449 4262813 := bstep (se 3 (by rfl) ⟨799277, by rfl⟩ : syracuseStep 4262813 = 1598555) B1598555
theorem B4262867 : Blo 1262449 4262867 := bstep (se 1 (by rfl) ⟨3197150, by rfl⟩ : syracuseStep 4262867 = 6394301) B6394301
theorem B41003995 : Blo 1262449 41003995 := bstep (se 1 (by rfl) ⟨30752996, by rfl⟩ : syracuseStep 41003995 = 61505993) B61505993
theorem B9596069 : Blo 1262449 9596069 := bstep (se 4 (by rfl) ⟨899631, by rfl⟩ : syracuseStep 9596069 = 1799263) B1799263
theorem B3198143 : Blo 1262449 3198143 := bstep (se 1 (by rfl) ⟨2398607, by rfl⟩ : syracuseStep 3198143 = 4797215) B4797215
theorem B2698451 : Blo 1262449 2698451 := bstep (se 1 (by rfl) ⟨2023838, by rfl⟩ : syracuseStep 2698451 = 4047677) B4047677
theorem B1281343 : Blo 1262449 1281343 := bstep (se 1 (by rfl) ⟨961007, by rfl⟩ : syracuseStep 1281343 = 1922015) B1922015
theorem B1895801 : Blo 1262449 1895801 := bstep (se 2 (by rfl) ⟨710925, by rfl⟩ : syracuseStep 1895801 = 1421851) B1421851
theorem B1895915 : Blo 1262449 1895915 := bstep (se 1 (by rfl) ⟨1421936, by rfl⟩ : syracuseStep 1895915 = 2843873) B2843873
theorem B1896041 : Blo 1262449 1896041 := bstep (se 2 (by rfl) ⟨711015, by rfl⟩ : syracuseStep 1896041 = 1422031) B1422031
theorem B1896359 : Blo 1262449 1896359 := bstep (se 1 (by rfl) ⟨1422269, by rfl⟩ : syracuseStep 1896359 = 2844539) B2844539
theorem B92205013 : Blo 1262449 92205013 := bstep (se 7 (by rfl) ⟨1080527, by rfl⟩ : syracuseStep 92205013 = 2161055) B2161055
theorem B1896539 : Blo 1262449 1896539 := bstep (se 1 (by rfl) ⟨1422404, by rfl⟩ : syracuseStep 1896539 = 2844809) B2844809
theorem B28062125 : Blo 1262449 28062125 := bstep (se 3 (by rfl) ⟨5261648, by rfl⟩ : syracuseStep 28062125 = 10523297) B10523297
theorem B5190103 : Blo 1262449 5190103 := bstep (se 1 (by rfl) ⟨3892577, by rfl⟩ : syracuseStep 5190103 = 7785155) B7785155
theorem B7787623 : Blo 1262449 7787623 := bstep (se 1 (by rfl) ⟨5840717, by rfl⟩ : syracuseStep 7787623 = 11681435) B11681435
theorem B5125241 : Blo 1262449 5125241 := bstep (se 2 (by rfl) ⟨1921965, by rfl⟩ : syracuseStep 5125241 = 3843931) B3843931
theorem B26293571 : Blo 1262449 26293571 := bstep (se 1 (by rfl) ⟨19720178, by rfl⟩ : syracuseStep 26293571 = 39440357) B39440357
theorem B3200431 : Blo 1262449 3200431 := bstep (se 1 (by rfl) ⟨2400323, by rfl⟩ : syracuseStep 3200431 = 4800647) B4800647
theorem B4675367 : Blo 1262449 4675367 := bstep (se 1 (by rfl) ⟨3506525, by rfl⟩ : syracuseStep 4675367 = 7013051) B7013051
theorem B16185167 : Blo 1262449 16185167 := bstep (se 1 (by rfl) ⟨12138875, by rfl⟩ : syracuseStep 16185167 = 24277751) B24277751
theorem B147601511 : Blo 1262449 147601511 := bstep (se 1 (by rfl) ⟨110701133, by rfl⟩ : syracuseStep 147601511 = 221402267) B221402267
theorem B2398319 : Blo 1262449 2398319 := bstep (se 1 (by rfl) ⟨1798739, by rfl⟩ : syracuseStep 2398319 = 3597479) B3597479
theorem B9615631 : Blo 1262449 9615631 := bstep (se 1 (by rfl) ⟨7211723, by rfl⟩ : syracuseStep 9615631 = 14423447) B14423447
theorem B4045153 : Blo 1262449 4045153 := bstep (se 2 (by rfl) ⟨1516932, by rfl⟩ : syracuseStep 4045153 = 3033865) B3033865
theorem B2398585 : Blo 1262449 2398585 := bstep (se 2 (by rfl) ⟨899469, by rfl⟩ : syracuseStep 2398585 = 1798939) B1798939
theorem B4799159 : Blo 1262449 4799159 := bstep (se 1 (by rfl) ⟨3599369, by rfl⟩ : syracuseStep 4799159 = 7198739) B7198739
theorem B2841353 : Blo 1262449 2841353 := bstep (se 2 (by rfl) ⟨1065507, by rfl⟩ : syracuseStep 2841353 = 2131015) B2131015
theorem B4266863 : Blo 1262449 4266863 := bstep (se 1 (by rfl) ⟨3200147, by rfl⟩ : syracuseStep 4266863 = 6400295) B6400295
theorem B8641403 : Blo 1262449 8641403 := bstep (se 1 (by rfl) ⟨6481052, by rfl⟩ : syracuseStep 8641403 = 12962105) B12962105
theorem B2841929 : Blo 1262449 2841929 := bstep (se 2 (by rfl) ⟨1065723, by rfl⟩ : syracuseStep 2841929 = 2131447) B2131447
theorem B10796399 : Blo 1262449 10796399 := bstep (se 1 (by rfl) ⟨8097299, by rfl⟩ : syracuseStep 10796399 = 16194599) B16194599
theorem B9723365 : Blo 1262449 9723365 := bstep (se 4 (by rfl) ⟨911565, by rfl⟩ : syracuseStep 9723365 = 1823131) B1823131
theorem B2842091 : Blo 1262449 2842091 := bstep (se 1 (by rfl) ⟨2131568, by rfl⟩ : syracuseStep 2842091 = 4263137) B4263137
theorem B2276905 : Blo 1262449 2276905 := bstep (se 2 (by rfl) ⟨853839, by rfl⟩ : syracuseStep 2276905 = 1707679) B1707679
theorem B44383859 : Blo 1262449 44383859 := bstep (se 1 (by rfl) ⟨33287894, by rfl⟩ : syracuseStep 44383859 = 66575789) B66575789
theorem B62283437 : Blo 1262449 62283437 := bstep (se 3 (by rfl) ⟨11678144, by rfl⟩ : syracuseStep 62283437 = 23356289) B23356289
theorem B8765405 : Blo 1262449 8765405 := bstep (se 3 (by rfl) ⟨1643513, by rfl⟩ : syracuseStep 8765405 = 3287027) B3287027
theorem B2842721 : Blo 1262449 2842721 := bstep (se 2 (by rfl) ⟨1066020, by rfl⟩ : syracuseStep 2842721 = 2132041) B2132041
theorem B4325615 : Blo 1262449 4325615 := bstep (se 1 (by rfl) ⟨3244211, by rfl⟩ : syracuseStep 4325615 = 6488423) B6488423
theorem B12820841 : Blo 1262449 12820841 := bstep (se 2 (by rfl) ⟨4807815, by rfl⟩ : syracuseStep 12820841 = 9615631) B9615631
theorem B2843297 : Blo 1262449 2843297 := bstep (se 2 (by rfl) ⟨1066236, by rfl⟩ : syracuseStep 2843297 = 2132473) B2132473
theorem B3416827 : Blo 1262449 3416827 := bstep (se 1 (by rfl) ⟨2562620, by rfl⟩ : syracuseStep 3416827 = 5125241) B5125241
theorem B4260815 : Blo 1262449 4260815 := bstep (se 1 (by rfl) ⟨3195611, by rfl⟩ : syracuseStep 4260815 = 6391223) B6391223
theorem B1262747 : Blo 1262449 1262747 := bstep (se 1 (by rfl) ⟨947060, by rfl⟩ : syracuseStep 1262747 = 1894121) B1894121
theorem B10790111 : Blo 1262449 10790111 := bstep (se 1 (by rfl) ⟨8092583, by rfl⟩ : syracuseStep 10790111 = 16185167) B16185167
theorem B1262847 : Blo 1262449 1262847 := bstep (se 1 (by rfl) ⟨947135, by rfl⟩ : syracuseStep 1262847 = 1894271) B1894271
theorem B13845815 : Blo 1262449 13845815 := bstep (se 1 (by rfl) ⟨10384361, by rfl⟩ : syracuseStep 13845815 = 20768723) B20768723
theorem B1598879 : Blo 1262449 1598879 := bstep (se 1 (by rfl) ⟨1199159, by rfl⟩ : syracuseStep 1598879 = 2398319) B2398319
theorem B1263103 : Blo 1262449 1263103 := bstep (se 1 (by rfl) ⟨947327, by rfl⟩ : syracuseStep 1263103 = 1894655) B1894655
theorem B1263259 : Blo 1262449 1263259 := bstep (se 1 (by rfl) ⟨947444, by rfl⟩ : syracuseStep 1263259 = 1894889) B1894889
theorem B186959659 : Blo 1262449 186959659 := bstep (se 1 (by rfl) ⟨140219744, by rfl⟩ : syracuseStep 186959659 = 280439489) B280439489
theorem B4261679 : Blo 1262449 4261679 := bstep (se 1 (by rfl) ⟨3196259, by rfl⟩ : syracuseStep 4261679 = 6392519) B6392519
theorem B1894235 : Blo 1262449 1894235 := bstep (se 1 (by rfl) ⟨1420676, by rfl⟩ : syracuseStep 1894235 = 2841353) B2841353
theorem B2844575 : Blo 1262449 2844575 := bstep (se 1 (by rfl) ⟨2133431, by rfl⟩ : syracuseStep 2844575 = 4266863) B4266863
theorem B5760935 : Blo 1262449 5760935 := bstep (se 1 (by rfl) ⟨4320701, by rfl⟩ : syracuseStep 5760935 = 8641403) B8641403
theorem B2132095 : Blo 1262449 2132095 := bstep (se 1 (by rfl) ⟨1599071, by rfl⟩ : syracuseStep 2132095 = 3198143) B3198143
theorem B1894619 : Blo 1262449 1894619 := bstep (se 1 (by rfl) ⟨1420964, by rfl⟩ : syracuseStep 1894619 = 2841929) B2841929
theorem B1263867 : Blo 1262449 1263867 := bstep (se 1 (by rfl) ⟨947900, by rfl⟩ : syracuseStep 1263867 = 1895801) B1895801
theorem B6482243 : Blo 1262449 6482243 := bstep (se 1 (by rfl) ⟨4861682, by rfl⟩ : syracuseStep 6482243 = 9723365) B9723365
theorem B1894727 : Blo 1262449 1894727 := bstep (se 1 (by rfl) ⟨1421045, by rfl⟩ : syracuseStep 1894727 = 2842091) B2842091
theorem B1263943 : Blo 1262449 1263943 := bstep (se 1 (by rfl) ⟨947957, by rfl⟩ : syracuseStep 1263943 = 1895915) B1895915
theorem B1264027 : Blo 1262449 1264027 := bstep (se 1 (by rfl) ⟨948020, by rfl⟩ : syracuseStep 1264027 = 1896041) B1896041
theorem B1264239 : Blo 1262449 1264239 := bstep (se 1 (by rfl) ⟨948179, by rfl⟩ : syracuseStep 1264239 = 1896359) B1896359
theorem B122940017 : Blo 1262449 122940017 := bstep (se 2 (by rfl) ⟨46102506, by rfl⟩ : syracuseStep 122940017 = 92205013) B92205013
theorem B5843603 : Blo 1262449 5843603 := bstep (se 1 (by rfl) ⟨4382702, by rfl⟩ : syracuseStep 5843603 = 8765405) B8765405
theorem B5466847 : Blo 1262449 5466847 := bstep (se 1 (by rfl) ⟨4100135, by rfl⟩ : syracuseStep 5466847 = 8200271) B8200271
theorem B1264359 : Blo 1262449 1264359 := bstep (se 1 (by rfl) ⟨948269, by rfl⟩ : syracuseStep 1264359 = 1896539) B1896539
theorem B1518331 : Blo 1262449 1518331 := bstep (se 1 (by rfl) ⟨1138748, by rfl⟩ : syracuseStep 1518331 = 2277497) B2277497
theorem B6392681 : Blo 1262449 6392681 := bstep (se 2 (by rfl) ⟨2397255, by rfl⟩ : syracuseStep 6392681 = 4794511) B4794511
theorem B4262921 : Blo 1262449 4262921 := bstep (se 2 (by rfl) ⟨1598595, by rfl⟩ : syracuseStep 4262921 = 3197191) B3197191
theorem B10792025 : Blo 1262449 10792025 := bstep (se 2 (by rfl) ⟨4047009, by rfl⟩ : syracuseStep 10792025 = 8094019) B8094019
theorem B5393537 : Blo 1262449 5393537 := bstep (se 2 (by rfl) ⟨2022576, by rfl⟩ : syracuseStep 5393537 = 4045153) B4045153
theorem B1895579 : Blo 1262449 1895579 := bstep (se 1 (by rfl) ⟨1421684, by rfl⟩ : syracuseStep 1895579 = 2843369) B2843369
theorem B3198113 : Blo 1262449 3198113 := bstep (se 2 (by rfl) ⟨1199292, by rfl⟩ : syracuseStep 3198113 = 2398585) B2398585
theorem B1895807 : Blo 1262449 1895807 := bstep (se 1 (by rfl) ⟨1421855, by rfl⟩ : syracuseStep 1895807 = 2843711) B2843711
theorem B3116911 : Blo 1262449 3116911 := bstep (se 1 (by rfl) ⟨2337683, by rfl⟩ : syracuseStep 3116911 = 4675367) B4675367
theorem B1896431 : Blo 1262449 1896431 := bstep (se 1 (by rfl) ⟨1422323, by rfl⟩ : syracuseStep 1896431 = 2844647) B2844647
theorem B10383497 : Blo 1262449 10383497 := bstep (se 2 (by rfl) ⟨3893811, by rfl⟩ : syracuseStep 10383497 = 7787623) B7787623
theorem B1896671 : Blo 1262449 1896671 := bstep (se 1 (by rfl) ⟨1422503, by rfl⟩ : syracuseStep 1896671 = 2845007) B2845007
theorem B25932079 : Blo 1262449 25932079 := bstep (se 1 (by rfl) ⟨19449059, by rfl⟩ : syracuseStep 25932079 = 38898119) B38898119
theorem B1708457 : Blo 1262449 1708457 := bstep (se 2 (by rfl) ⟨640671, by rfl⟩ : syracuseStep 1708457 = 1281343) B1281343
theorem B3199439 : Blo 1262449 3199439 := bstep (se 1 (by rfl) ⟨2399579, by rfl⟩ : syracuseStep 3199439 = 4799159) B4799159
theorem B3035873 : Blo 1262449 3035873 := bstep (se 2 (by rfl) ⟨1138452, by rfl⟩ : syracuseStep 3035873 = 2276905) B2276905
theorem B1798967 : Blo 1262449 1798967 := bstep (se 1 (by rfl) ⟨1349225, by rfl⟩ : syracuseStep 1798967 = 2698451) B2698451
theorem B7197599 : Blo 1262449 7197599 := bstep (se 1 (by rfl) ⟨5398199, by rfl⟩ : syracuseStep 7197599 = 10796399) B10796399
theorem B41522291 : Blo 1262449 41522291 := bstep (se 1 (by rfl) ⟨31141718, by rfl⟩ : syracuseStep 41522291 = 62283437) B62283437
theorem B6075881 : Blo 1262449 6075881 := bstep (se 2 (by rfl) ⟨2278455, by rfl⟩ : syracuseStep 6075881 = 4556911) B4556911
theorem B18708083 : Blo 1262449 18708083 := bstep (se 1 (by rfl) ⟨14031062, by rfl⟩ : syracuseStep 18708083 = 28062125) B28062125
theorem B6920137 : Blo 1262449 6920137 := bstep (se 2 (by rfl) ⟨2595051, by rfl⟩ : syracuseStep 6920137 = 5190103) B5190103
theorem B249083909 : Blo 1262449 249083909 := bstep (se 4 (by rfl) ⟨23351616, by rfl⟩ : syracuseStep 249083909 = 46703233) B46703233
theorem B2840687 : Blo 1262449 2840687 := bstep (se 1 (by rfl) ⟨2130515, by rfl⟩ : syracuseStep 2840687 = 4261031) B4261031
theorem B4266107 : Blo 1262449 4266107 := bstep (se 1 (by rfl) ⟨3199580, by rfl⟩ : syracuseStep 4266107 = 6399161) B6399161
theorem B17529047 : Blo 1262449 17529047 := bstep (se 1 (by rfl) ⟨13146785, by rfl⟩ : syracuseStep 17529047 = 26293571) B26293571
theorem B6396407 : Blo 1262449 6396407 := bstep (se 1 (by rfl) ⟨4797305, by rfl⟩ : syracuseStep 6396407 = 9594611) B9594611
theorem B54671993 : Blo 1262449 54671993 := bstep (se 2 (by rfl) ⟨20501997, by rfl⟩ : syracuseStep 54671993 = 41003995) B41003995
theorem B98401007 : Blo 1262449 98401007 := bstep (se 1 (by rfl) ⟨73800755, by rfl⟩ : syracuseStep 98401007 = 147601511) B147601511
theorem B2399215 : Blo 1262449 2399215 := bstep (se 1 (by rfl) ⟨1799411, by rfl⟩ : syracuseStep 2399215 = 3598823) B3598823
theorem B4267241 : Blo 1262449 4267241 := bstep (se 2 (by rfl) ⟨1600215, by rfl⟩ : syracuseStep 4267241 = 3200431) B3200431
theorem B2841875 : Blo 1262449 2841875 := bstep (se 1 (by rfl) ⟨2131406, by rfl⟩ : syracuseStep 2841875 = 4262813) B4262813
theorem B2841911 : Blo 1262449 2841911 := bstep (se 1 (by rfl) ⟨2131433, by rfl⟩ : syracuseStep 2841911 = 4262867) B4262867
theorem B6397379 : Blo 1262449 6397379 := bstep (se 1 (by rfl) ⟨4798034, by rfl⟩ : syracuseStep 6397379 = 9596069) B9596069
theorem B29589239 : Blo 1262449 29589239 := bstep (se 1 (by rfl) ⟨22191929, by rfl⟩ : syracuseStep 29589239 = 44383859) B44383859
theorem B6922331 : Blo 1262449 6922331 := bstep (se 1 (by rfl) ⟨5191748, by rfl⟩ : syracuseStep 6922331 = 10383497) B10383497
theorem B2883743 : Blo 1262449 2883743 := bstep (se 1 (by rfl) ⟨2162807, by rfl⟩ : syracuseStep 2883743 = 4325615) B4325615
theorem B2842793 : Blo 1262449 2842793 := bstep (se 2 (by rfl) ⟨1066047, by rfl⟩ : syracuseStep 2842793 = 2132095) B2132095
theorem B2023915 : Blo 1262449 2023915 := bstep (se 1 (by rfl) ⟨1517936, by rfl⟩ : syracuseStep 2023915 = 3035873) B3035873
theorem B27681527 : Blo 1262449 27681527 := bstep (se 1 (by rfl) ⟨20761145, by rfl⟩ : syracuseStep 27681527 = 41522291) B41522291
theorem B7193407 : Blo 1262449 7193407 := bstep (se 1 (by rfl) ⟨5395055, by rfl⟩ : syracuseStep 7193407 = 10790111) B10790111
theorem B2024441 : Blo 1262449 2024441 := bstep (se 2 (by rfl) ⟨759165, by rfl⟩ : syracuseStep 2024441 = 1518331) B1518331
theorem B4555769 : Blo 1262449 4555769 := bstep (se 2 (by rfl) ⟨1708413, by rfl⟩ : syracuseStep 4555769 = 3416827) B3416827
theorem B1262823 : Blo 1262449 1262823 := bstep (se 1 (by rfl) ⟨947117, by rfl⟩ : syracuseStep 1262823 = 1894235) B1894235
theorem B1893791 : Blo 1262449 1893791 := bstep (se 1 (by rfl) ⟨1420343, by rfl⟩ : syracuseStep 1893791 = 2840687) B2840687
theorem B2844071 : Blo 1262449 2844071 := bstep (se 1 (by rfl) ⟨2133053, by rfl⟩ : syracuseStep 2844071 = 4266107) B4266107
theorem B1263079 : Blo 1262449 1263079 := bstep (se 1 (by rfl) ⟨947309, by rfl⟩ : syracuseStep 1263079 = 1894619) B1894619
theorem B1263151 : Blo 1262449 1263151 := bstep (se 1 (by rfl) ⟨947363, by rfl⟩ : syracuseStep 1263151 = 1894727) B1894727
theorem B36447995 : Blo 1262449 36447995 := bstep (se 1 (by rfl) ⟨27335996, by rfl⟩ : syracuseStep 36447995 = 54671993) B54671993
theorem B4261787 : Blo 1262449 4261787 := bstep (se 1 (by rfl) ⟨3196340, by rfl⟩ : syracuseStep 4261787 = 6392681) B6392681
theorem B7194683 : Blo 1262449 7194683 := bstep (se 1 (by rfl) ⟨5396012, by rfl⟩ : syracuseStep 7194683 = 10792025) B10792025
theorem B1263719 : Blo 1262449 1263719 := bstep (se 1 (by rfl) ⟨947789, by rfl⟩ : syracuseStep 1263719 = 1895579) B1895579
theorem B2132075 : Blo 1262449 2132075 := bstep (se 1 (by rfl) ⟨1599056, by rfl⟩ : syracuseStep 2132075 = 3198113) B3198113
theorem B2844827 : Blo 1262449 2844827 := bstep (se 1 (by rfl) ⟨2133620, by rfl⟩ : syracuseStep 2844827 = 4267241) B4267241
theorem B1894583 : Blo 1262449 1894583 := bstep (se 1 (by rfl) ⟨1420937, by rfl⟩ : syracuseStep 1894583 = 2841875) B2841875
theorem B1894607 : Blo 1262449 1894607 := bstep (se 1 (by rfl) ⟨1420955, by rfl⟩ : syracuseStep 1894607 = 2841911) B2841911
theorem B1263871 : Blo 1262449 1263871 := bstep (se 1 (by rfl) ⟨947903, by rfl⟩ : syracuseStep 1263871 = 1895807) B1895807
theorem B36907397 : Blo 1262449 36907397 := bstep (se 4 (by rfl) ⟨3460068, by rfl⟩ : syracuseStep 36907397 = 6920137) B6920137
theorem B4155881 : Blo 1262449 4155881 := bstep (se 2 (by rfl) ⟨1558455, by rfl⟩ : syracuseStep 4155881 = 3116911) B3116911
theorem B1264287 : Blo 1262449 1264287 := bstep (se 1 (by rfl) ⟨948215, by rfl⟩ : syracuseStep 1264287 = 1896431) B1896431
theorem B1895147 : Blo 1262449 1895147 := bstep (se 1 (by rfl) ⟨1421360, by rfl⟩ : syracuseStep 1895147 = 2842721) B2842721
theorem B1264447 : Blo 1262449 1264447 := bstep (se 1 (by rfl) ⟨948335, by rfl⟩ : syracuseStep 1264447 = 1896671) B1896671
theorem B8547227 : Blo 1262449 8547227 := bstep (se 1 (by rfl) ⟨6410420, by rfl⟩ : syracuseStep 8547227 = 12820841) B12820841
theorem B2132959 : Blo 1262449 2132959 := bstep (se 1 (by rfl) ⟨1599719, by rfl⟩ : syracuseStep 2132959 = 3199439) B3199439
theorem B1895531 : Blo 1262449 1895531 := bstep (se 1 (by rfl) ⟨1421648, by rfl⟩ : syracuseStep 1895531 = 2843297) B2843297
theorem B4050587 : Blo 1262449 4050587 := bstep (se 1 (by rfl) ⟨3037940, by rfl⟩ : syracuseStep 4050587 = 6075881) B6075881
theorem B12472055 : Blo 1262449 12472055 := bstep (se 1 (by rfl) ⟨9354041, by rfl⟩ : syracuseStep 12472055 = 18708083) B18708083
theorem B4263677 : Blo 1262449 4263677 := bstep (se 3 (by rfl) ⟨799439, by rfl⟩ : syracuseStep 4263677 = 1598879) B1598879
theorem B1896383 : Blo 1262449 1896383 := bstep (se 1 (by rfl) ⟨1422287, by rfl⟩ : syracuseStep 1896383 = 2844575) B2844575
theorem B3198953 : Blo 1262449 3198953 := bstep (se 2 (by rfl) ⟨1199607, by rfl⟩ : syracuseStep 3198953 = 2399215) B2399215
theorem B166055939 : Blo 1262449 166055939 := bstep (se 1 (by rfl) ⟨124541954, by rfl⟩ : syracuseStep 166055939 = 249083909) B249083909
theorem B11686031 : Blo 1262449 11686031 := bstep (se 1 (by rfl) ⟨8764523, by rfl⟩ : syracuseStep 11686031 = 17529047) B17529047
theorem B4321495 : Blo 1262449 4321495 := bstep (se 1 (by rfl) ⟨3241121, by rfl⟩ : syracuseStep 4321495 = 6482243) B6482243
theorem B4264271 : Blo 1262449 4264271 := bstep (se 1 (by rfl) ⟨3198203, by rfl⟩ : syracuseStep 4264271 = 6396407) B6396407
theorem B18223541 : Blo 1262449 18223541 := bstep (se 5 (by rfl) ⟨854228, by rfl⟩ : syracuseStep 18223541 = 1708457) B1708457
theorem B3895735 : Blo 1262449 3895735 := bstep (se 1 (by rfl) ⟨2921801, by rfl⟩ : syracuseStep 3895735 = 5843603) B5843603
theorem B262402685 : Blo 1262449 262402685 := bstep (se 3 (by rfl) ⟨49200503, by rfl⟩ : syracuseStep 262402685 = 98401007) B98401007
theorem B4797245 : Blo 1262449 4797245 := bstep (se 3 (by rfl) ⟨899483, by rfl⟩ : syracuseStep 4797245 = 1798967) B1798967
theorem B4264919 : Blo 1262449 4264919 := bstep (se 1 (by rfl) ⟨3198689, by rfl⟩ : syracuseStep 4264919 = 6397379) B6397379
theorem B249279545 : Blo 1262449 249279545 := bstep (se 2 (by rfl) ⟨93479829, by rfl⟩ : syracuseStep 249279545 = 186959659) B186959659
theorem B34576105 : Blo 1262449 34576105 := bstep (se 2 (by rfl) ⟨12966039, by rfl⟩ : syracuseStep 34576105 = 25932079) B25932079
theorem B4798399 : Blo 1262449 4798399 := bstep (se 1 (by rfl) ⟨3598799, by rfl⟩ : syracuseStep 4798399 = 7197599) B7197599
theorem B2840543 : Blo 1262449 2840543 := bstep (se 1 (by rfl) ⟨2130407, by rfl⟩ : syracuseStep 2840543 = 4260815) B4260815
theorem B9230543 : Blo 1262449 9230543 := bstep (se 1 (by rfl) ⟨6922907, by rfl⟩ : syracuseStep 9230543 = 13845815) B13845815
theorem B7289129 : Blo 1262449 7289129 := bstep (se 2 (by rfl) ⟨2733423, by rfl⟩ : syracuseStep 7289129 = 5466847) B5466847
theorem B2841119 : Blo 1262449 2841119 := bstep (se 1 (by rfl) ⟨2130839, by rfl⟩ : syracuseStep 2841119 = 4261679) B4261679
theorem B3840623 : Blo 1262449 3840623 := bstep (se 1 (by rfl) ⟨2880467, by rfl⟩ : syracuseStep 3840623 = 5760935) B5760935
theorem B81960011 : Blo 1262449 81960011 := bstep (se 1 (by rfl) ⟨61470008, by rfl⟩ : syracuseStep 81960011 = 122940017) B122940017
theorem B78904637 : Blo 1262449 78904637 := bstep (se 3 (by rfl) ⟨14794619, by rfl⟩ : syracuseStep 78904637 = 29589239) B29589239
theorem B2841947 : Blo 1262449 2841947 := bstep (se 1 (by rfl) ⟨2131460, by rfl⟩ : syracuseStep 2841947 = 4262921) B4262921
theorem B3595691 : Blo 1262449 3595691 := bstep (se 1 (by rfl) ⟨2696768, by rfl⟩ : syracuseStep 3595691 = 5393537) B5393537
theorem B7790687 : Blo 1262449 7790687 := bstep (se 1 (by rfl) ⟨5843015, by rfl⟩ : syracuseStep 7790687 = 11686031) B11686031
theorem B2842847 : Blo 1262449 2842847 := bstep (se 1 (by rfl) ⟨2132135, by rfl⟩ : syracuseStep 2842847 = 4264271) B4264271
theorem B12149027 : Blo 1262449 12149027 := bstep (se 1 (by rfl) ⟨9111770, by rfl⟩ : syracuseStep 12149027 = 18223541) B18223541
theorem B5194313 : Blo 1262449 5194313 := bstep (se 2 (by rfl) ⟨1947867, by rfl⟩ : syracuseStep 5194313 = 3895735) B3895735
theorem B2843279 : Blo 1262449 2843279 := bstep (se 1 (by rfl) ⟨2132459, by rfl⟩ : syracuseStep 2843279 = 4264919) B4264919
theorem B1262527 : Blo 1262449 1262527 := bstep (se 1 (by rfl) ⟨946895, by rfl⟩ : syracuseStep 1262527 = 1893791) B1893791
theorem B24298663 : Blo 1262449 24298663 := bstep (se 1 (by rfl) ⟨18223997, by rfl⟩ : syracuseStep 24298663 = 36447995) B36447995
theorem B2843945 : Blo 1262449 2843945 := bstep (se 2 (by rfl) ⟨1066479, by rfl⟩ : syracuseStep 2843945 = 2132959) B2132959
theorem B1893695 : Blo 1262449 1893695 := bstep (se 1 (by rfl) ⟨1420271, by rfl⟩ : syracuseStep 1893695 = 2840543) B2840543
theorem B1263055 : Blo 1262449 1263055 := bstep (se 1 (by rfl) ⟨947291, by rfl⟩ : syracuseStep 1263055 = 1894583) B1894583
theorem B1263071 : Blo 1262449 1263071 := bstep (se 1 (by rfl) ⟨947303, by rfl⟩ : syracuseStep 1263071 = 1894607) B1894607
theorem B6153695 : Blo 1262449 6153695 := bstep (se 1 (by rfl) ⟨4615271, by rfl⟩ : syracuseStep 6153695 = 9230543) B9230543
theorem B1894079 : Blo 1262449 1894079 := bstep (se 1 (by rfl) ⟨1420559, by rfl⟩ : syracuseStep 1894079 = 2841119) B2841119
theorem B1263431 : Blo 1262449 1263431 := bstep (se 1 (by rfl) ⟨947573, by rfl⟩ : syracuseStep 1263431 = 1895147) B1895147
theorem B1263687 : Blo 1262449 1263687 := bstep (se 1 (by rfl) ⟨947765, by rfl⟩ : syracuseStep 1263687 = 1895531) B1895531
theorem B52603091 : Blo 1262449 52603091 := bstep (se 1 (by rfl) ⟨39452318, by rfl⟩ : syracuseStep 52603091 = 78904637) B78904637
theorem B1894631 : Blo 1262449 1894631 := bstep (se 1 (by rfl) ⟨1420973, by rfl⟩ : syracuseStep 1894631 = 2841947) B2841947
theorem B1264255 : Blo 1262449 1264255 := bstep (se 1 (by rfl) ⟨948191, by rfl⟩ : syracuseStep 1264255 = 1896383) B1896383
theorem B2132635 : Blo 1262449 2132635 := bstep (se 1 (by rfl) ⟨1599476, by rfl⟩ : syracuseStep 2132635 = 3198953) B3198953
theorem B4614887 : Blo 1262449 4614887 := bstep (se 1 (by rfl) ⟨3461165, by rfl⟩ : syracuseStep 4614887 = 6922331) B6922331
theorem B1895195 : Blo 1262449 1895195 := bstep (se 1 (by rfl) ⟨1421396, by rfl⟩ : syracuseStep 1895195 = 2842793) B2842793
theorem B174935123 : Blo 1262449 174935123 := bstep (se 1 (by rfl) ⟨131201342, by rfl⟩ : syracuseStep 174935123 = 262402685) B262402685
theorem B3198163 : Blo 1262449 3198163 := bstep (se 1 (by rfl) ⟨2398622, by rfl⟩ : syracuseStep 3198163 = 4797245) B4797245
theorem B2698553 : Blo 1262449 2698553 := bstep (se 2 (by rfl) ⟨1011957, by rfl⟩ : syracuseStep 2698553 = 2023915) B2023915
theorem B1896047 : Blo 1262449 1896047 := bstep (se 1 (by rfl) ⟨1422035, by rfl⟩ : syracuseStep 1896047 = 2844071) B2844071
theorem B23047973 : Blo 1262449 23047973 := bstep (se 4 (by rfl) ⟨2160747, by rfl⟩ : syracuseStep 23047973 = 4321495) B4321495
theorem B4796455 : Blo 1262449 4796455 := bstep (se 1 (by rfl) ⟨3597341, by rfl⟩ : syracuseStep 4796455 = 7194683) B7194683
theorem B1421383 : Blo 1262449 1421383 := bstep (se 1 (by rfl) ⟨1066037, by rfl⟩ : syracuseStep 1421383 = 2132075) B2132075
theorem B1896551 : Blo 1262449 1896551 := bstep (se 1 (by rfl) ⟨1422413, by rfl⟩ : syracuseStep 1896551 = 2844827) B2844827
theorem B24604931 : Blo 1262449 24604931 := bstep (se 1 (by rfl) ⟨18453698, by rfl⟩ : syracuseStep 24604931 = 36907397) B36907397
theorem B2560415 : Blo 1262449 2560415 := bstep (se 1 (by rfl) ⟨1920311, by rfl⟩ : syracuseStep 2560415 = 3840623) B3840623
theorem B5698151 : Blo 1262449 5698151 := bstep (se 1 (by rfl) ⟨4273613, by rfl⟩ : syracuseStep 5698151 = 8547227) B8547227
theorem B2397127 : Blo 1262449 2397127 := bstep (se 1 (by rfl) ⟨1797845, by rfl⟩ : syracuseStep 2397127 = 3595691) B3595691
theorem B46101473 : Blo 1262449 46101473 := bstep (se 2 (by rfl) ⟨17288052, by rfl⟩ : syracuseStep 46101473 = 34576105) B34576105
theorem B2700391 : Blo 1262449 2700391 := bstep (se 1 (by rfl) ⟨2025293, by rfl⟩ : syracuseStep 2700391 = 4050587) B4050587
theorem B110703959 : Blo 1262449 110703959 := bstep (se 1 (by rfl) ⟨83027969, by rfl⟩ : syracuseStep 110703959 = 166055939) B166055939
theorem B1922495 : Blo 1262449 1922495 := bstep (se 1 (by rfl) ⟨1441871, by rfl⟩ : syracuseStep 1922495 = 2883743) B2883743
theorem B664745453 : Blo 1262449 664745453 := bstep (se 3 (by rfl) ⟨124639772, by rfl⟩ : syracuseStep 664745453 = 249279545) B249279545
theorem B18454351 : Blo 1262449 18454351 := bstep (se 1 (by rfl) ⟨13840763, by rfl⟩ : syracuseStep 18454351 = 27681527) B27681527
theorem B1349627 : Blo 1262449 1349627 := bstep (se 1 (by rfl) ⟨1012220, by rfl⟩ : syracuseStep 1349627 = 2024441) B2024441
theorem B19437677 : Blo 1262449 19437677 := bstep (se 3 (by rfl) ⟨3644564, by rfl⟩ : syracuseStep 19437677 = 7289129) B7289129
theorem B9591209 : Blo 1262449 9591209 := bstep (se 2 (by rfl) ⟨3596703, by rfl⟩ : syracuseStep 9591209 = 7193407) B7193407
theorem B2841191 : Blo 1262449 2841191 := bstep (se 1 (by rfl) ⟨2130893, by rfl⟩ : syracuseStep 2841191 = 4261787) B4261787
theorem B11082349 : Blo 1262449 11082349 := bstep (se 3 (by rfl) ⟨2077940, by rfl⟩ : syracuseStep 11082349 = 4155881) B4155881
theorem B54640007 : Blo 1262449 54640007 := bstep (se 1 (by rfl) ⟨40980005, by rfl⟩ : syracuseStep 54640007 = 81960011) B81960011
theorem B8314703 : Blo 1262449 8314703 := bstep (se 1 (by rfl) ⟨6236027, by rfl⟩ : syracuseStep 8314703 = 12472055) B12472055
theorem B2842451 : Blo 1262449 2842451 := bstep (se 1 (by rfl) ⟨2131838, by rfl⟩ : syracuseStep 2842451 = 4263677) B4263677
theorem B6397865 : Blo 1262449 6397865 := bstep (se 2 (by rfl) ⟨2399199, by rfl⟩ : syracuseStep 6397865 = 4798399) B4798399
theorem B12148717 : Blo 1262449 12148717 := bstep (se 3 (by rfl) ⟨2277884, by rfl⟩ : syracuseStep 12148717 = 4555769) B4555769
theorem B5193791 : Blo 1262449 5193791 := bstep (se 1 (by rfl) ⟨3895343, by rfl⟩ : syracuseStep 5193791 = 7790687) B7790687
theorem B2843513 : Blo 1262449 2843513 := bstep (se 2 (by rfl) ⟨1066317, by rfl⟩ : syracuseStep 2843513 = 2132635) B2132635
theorem B1262463 : Blo 1262449 1262463 := bstep (se 1 (by rfl) ⟨946847, by rfl⟩ : syracuseStep 1262463 = 1893695) B1893695
theorem B73802639 : Blo 1262449 73802639 := bstep (se 1 (by rfl) ⟨55351979, by rfl⟩ : syracuseStep 73802639 = 110703959) B110703959
theorem B443163635 : Blo 1262449 443163635 := bstep (se 1 (by rfl) ⟨332372726, by rfl⟩ : syracuseStep 443163635 = 664745453) B664745453
theorem B1262719 : Blo 1262449 1262719 := bstep (se 1 (by rfl) ⟨947039, by rfl⟩ : syracuseStep 1262719 = 1894079) B1894079
theorem B3196169 : Blo 1262449 3196169 := bstep (se 2 (by rfl) ⟨1198563, by rfl⟩ : syracuseStep 3196169 = 2397127) B2397127
theorem B1263087 : Blo 1262449 1263087 := bstep (se 1 (by rfl) ⟨947315, by rfl⟩ : syracuseStep 1263087 = 1894631) B1894631
theorem B1894127 : Blo 1262449 1894127 := bstep (se 1 (by rfl) ⟨1420595, by rfl⟩ : syracuseStep 1894127 = 2841191) B2841191
theorem B1263463 : Blo 1262449 1263463 := bstep (se 1 (by rfl) ⟨947597, by rfl⟩ : syracuseStep 1263463 = 1895195) B1895195
theorem B116623415 : Blo 1262449 116623415 := bstep (se 1 (by rfl) ⟨87467561, by rfl⟩ : syracuseStep 116623415 = 174935123) B174935123
theorem B1264031 : Blo 1262449 1264031 := bstep (se 1 (by rfl) ⟨948023, by rfl⟩ : syracuseStep 1264031 = 1896047) B1896047
theorem B1894967 : Blo 1262449 1894967 := bstep (se 1 (by rfl) ⟨1421225, by rfl⟩ : syracuseStep 1894967 = 2842451) B2842451
theorem B16198289 : Blo 1262449 16198289 := bstep (se 2 (by rfl) ⟨6074358, by rfl⟩ : syracuseStep 16198289 = 12148717) B12148717
theorem B3599005 : Blo 1262449 3599005 := bstep (se 3 (by rfl) ⟨674813, by rfl⟩ : syracuseStep 3599005 = 1349627) B1349627
theorem B1264367 : Blo 1262449 1264367 := bstep (se 1 (by rfl) ⟨948275, by rfl⟩ : syracuseStep 1264367 = 1896551) B1896551
theorem B1895177 : Blo 1262449 1895177 := bstep (se 2 (by rfl) ⟨710691, by rfl⟩ : syracuseStep 1895177 = 1421383) B1421383
theorem B1895231 : Blo 1262449 1895231 := bstep (se 1 (by rfl) ⟨1421423, by rfl⟩ : syracuseStep 1895231 = 2842847) B2842847
theorem B1895519 : Blo 1262449 1895519 := bstep (se 1 (by rfl) ⟨1421639, by rfl⟩ : syracuseStep 1895519 = 2843279) B2843279
theorem B65613149 : Blo 1262449 65613149 := bstep (se 3 (by rfl) ⟨12302465, by rfl⟩ : syracuseStep 65613149 = 24604931) B24604931
theorem B7196141 : Blo 1262449 7196141 := bstep (se 3 (by rfl) ⟨1349276, by rfl⟩ : syracuseStep 7196141 = 2698553) B2698553
theorem B1895963 : Blo 1262449 1895963 := bstep (se 1 (by rfl) ⟨1421972, by rfl⟩ : syracuseStep 1895963 = 2843945) B2843945
theorem B6827773 : Blo 1262449 6827773 := bstep (se 3 (by rfl) ⟨1280207, by rfl⟩ : syracuseStep 6827773 = 2560415) B2560415
theorem B3600521 : Blo 1262449 3600521 := bstep (se 2 (by rfl) ⟨1350195, by rfl⟩ : syracuseStep 3600521 = 2700391) B2700391
theorem B4264217 : Blo 1262449 4264217 := bstep (se 2 (by rfl) ⟨1599081, by rfl⟩ : syracuseStep 4264217 = 3198163) B3198163
theorem B6394139 : Blo 1262449 6394139 := bstep (se 1 (by rfl) ⟨4795604, by rfl⟩ : syracuseStep 6394139 = 9591209) B9591209
theorem B3076591 : Blo 1262449 3076591 := bstep (se 1 (by rfl) ⟨2307443, by rfl⟩ : syracuseStep 3076591 = 4614887) B4614887
theorem B36426671 : Blo 1262449 36426671 := bstep (se 1 (by rfl) ⟨27320003, by rfl⟩ : syracuseStep 36426671 = 54640007) B54640007
theorem B24605801 : Blo 1262449 24605801 := bstep (se 2 (by rfl) ⟨9227175, by rfl⟩ : syracuseStep 24605801 = 18454351) B18454351
theorem B15365315 : Blo 1262449 15365315 := bstep (se 1 (by rfl) ⟨11523986, by rfl⟩ : syracuseStep 15365315 = 23047973) B23047973
theorem B5543135 : Blo 1262449 5543135 := bstep (se 1 (by rfl) ⟨4157351, by rfl⟩ : syracuseStep 5543135 = 8314703) B8314703
theorem B4265243 : Blo 1262449 4265243 := bstep (se 1 (by rfl) ⟨3198932, by rfl⟩ : syracuseStep 4265243 = 6397865) B6397865
theorem B6395273 : Blo 1262449 6395273 := bstep (se 2 (by rfl) ⟨2398227, by rfl⟩ : syracuseStep 6395273 = 4796455) B4796455
theorem B8099351 : Blo 1262449 8099351 := bstep (se 1 (by rfl) ⟨6074513, by rfl⟩ : syracuseStep 8099351 = 12149027) B12149027
theorem B3462875 : Blo 1262449 3462875 := bstep (se 1 (by rfl) ⟨2597156, by rfl⟩ : syracuseStep 3462875 = 5194313) B5194313
theorem B3798767 : Blo 1262449 3798767 := bstep (se 1 (by rfl) ⟨2849075, by rfl⟩ : syracuseStep 3798767 = 5698151) B5698151
theorem B30734315 : Blo 1262449 30734315 := bstep (se 1 (by rfl) ⟨23050736, by rfl⟩ : syracuseStep 30734315 = 46101473) B46101473
theorem B14776465 : Blo 1262449 14776465 := bstep (se 2 (by rfl) ⟨5541174, by rfl⟩ : syracuseStep 14776465 = 11082349) B11082349
theorem B4102463 : Blo 1262449 4102463 := bstep (se 1 (by rfl) ⟨3076847, by rfl⟩ : syracuseStep 4102463 = 6153695) B6153695
theorem B5126653 : Blo 1262449 5126653 := bstep (se 3 (by rfl) ⟨961247, by rfl⟩ : syracuseStep 5126653 = 1922495) B1922495
theorem B12958451 : Blo 1262449 12958451 := bstep (se 1 (by rfl) ⟨9718838, by rfl⟩ : syracuseStep 12958451 = 19437677) B19437677
theorem B35068727 : Blo 1262449 35068727 := bstep (se 1 (by rfl) ⟨26301545, by rfl⟩ : syracuseStep 35068727 = 52603091) B52603091
theorem B32398217 : Blo 1262449 32398217 := bstep (se 2 (by rfl) ⟨12149331, by rfl⟩ : syracuseStep 32398217 = 24298663) B24298663
theorem B2400347 : Blo 1262449 2400347 := bstep (se 1 (by rfl) ⟨1800260, by rfl⟩ : syracuseStep 2400347 = 3600521) B3600521
theorem B2842811 : Blo 1262449 2842811 := bstep (se 1 (by rfl) ⟨2132108, by rfl⟩ : syracuseStep 2842811 = 4264217) B4264217
theorem B19701953 : Blo 1262449 19701953 := bstep (se 2 (by rfl) ⟨7388232, by rfl⟩ : syracuseStep 19701953 = 14776465) B14776465
theorem B49201759 : Blo 1262449 49201759 := bstep (se 1 (by rfl) ⟨36901319, by rfl⟩ : syracuseStep 49201759 = 73802639) B73802639
theorem B3695423 : Blo 1262449 3695423 := bstep (se 1 (by rfl) ⟨2771567, by rfl⟩ : syracuseStep 3695423 = 5543135) B5543135
theorem B2130779 : Blo 1262449 2130779 := bstep (se 1 (by rfl) ⟨1598084, by rfl⟩ : syracuseStep 2130779 = 3196169) B3196169
theorem B2843495 : Blo 1262449 2843495 := bstep (se 1 (by rfl) ⟨2132621, by rfl⟩ : syracuseStep 2843495 = 4265243) B4265243
theorem B5399567 : Blo 1262449 5399567 := bstep (se 1 (by rfl) ⟨4049675, by rfl⟩ : syracuseStep 5399567 = 8099351) B8099351
theorem B1262751 : Blo 1262449 1262751 := bstep (se 1 (by rfl) ⟨947063, by rfl⟩ : syracuseStep 1262751 = 1894127) B1894127
theorem B2532511 : Blo 1262449 2532511 := bstep (se 1 (by rfl) ⟨1899383, by rfl⟩ : syracuseStep 2532511 = 3798767) B3798767
theorem B20489543 : Blo 1262449 20489543 := bstep (se 1 (by rfl) ⟨15367157, by rfl⟩ : syracuseStep 20489543 = 30734315) B30734315
theorem B1263311 : Blo 1262449 1263311 := bstep (se 1 (by rfl) ⟨947483, by rfl⟩ : syracuseStep 1263311 = 1894967) B1894967
theorem B10798859 : Blo 1262449 10798859 := bstep (se 1 (by rfl) ⟨8099144, by rfl⟩ : syracuseStep 10798859 = 16198289) B16198289
theorem B1263451 : Blo 1262449 1263451 := bstep (se 1 (by rfl) ⟨947588, by rfl⟩ : syracuseStep 1263451 = 1895177) B1895177
theorem B1263487 : Blo 1262449 1263487 := bstep (se 1 (by rfl) ⟨947615, by rfl⟩ : syracuseStep 1263487 = 1895231) B1895231
theorem B1263679 : Blo 1262449 1263679 := bstep (se 1 (by rfl) ⟨947759, by rfl⟩ : syracuseStep 1263679 = 1895519) B1895519
theorem B9103697 : Blo 1262449 9103697 := bstep (se 2 (by rfl) ⟨3413886, by rfl⟩ : syracuseStep 9103697 = 6827773) B6827773
theorem B1263975 : Blo 1262449 1263975 := bstep (se 1 (by rfl) ⟨947981, by rfl⟩ : syracuseStep 1263975 = 1895963) B1895963
theorem B4262759 : Blo 1262449 4262759 := bstep (se 1 (by rfl) ⟨3197069, by rfl⟩ : syracuseStep 4262759 = 6394139) B6394139
theorem B1895675 : Blo 1262449 1895675 := bstep (se 1 (by rfl) ⟨1421756, by rfl⟩ : syracuseStep 1895675 = 2843513) B2843513
theorem B24284447 : Blo 1262449 24284447 := bstep (se 1 (by rfl) ⟨18213335, by rfl⟩ : syracuseStep 24284447 = 36426671) B36426671
theorem B6835537 : Blo 1262449 6835537 := bstep (se 2 (by rfl) ⟨2563326, by rfl⟩ : syracuseStep 6835537 = 5126653) B5126653
theorem B16403867 : Blo 1262449 16403867 := bstep (se 1 (by rfl) ⟨12302900, by rfl⟩ : syracuseStep 16403867 = 24605801) B24605801
theorem B10243543 : Blo 1262449 10243543 := bstep (se 1 (by rfl) ⟨7682657, by rfl⟩ : syracuseStep 10243543 = 15365315) B15365315
theorem B4263515 : Blo 1262449 4263515 := bstep (se 1 (by rfl) ⟨3197636, by rfl⟩ : syracuseStep 4263515 = 6395273) B6395273
theorem B8638967 : Blo 1262449 8638967 := bstep (se 1 (by rfl) ⟨6479225, by rfl⟩ : syracuseStep 8638967 = 12958451) B12958451
theorem B21598811 : Blo 1262449 21598811 := bstep (se 1 (by rfl) ⟨16199108, by rfl⟩ : syracuseStep 21598811 = 32398217) B32398217
theorem B43742099 : Blo 1262449 43742099 := bstep (se 1 (by rfl) ⟨32806574, by rfl⟩ : syracuseStep 43742099 = 65613149) B65613149
theorem B4797427 : Blo 1262449 4797427 := bstep (se 1 (by rfl) ⟨3598070, by rfl⟩ : syracuseStep 4797427 = 7196141) B7196141
theorem B3462527 : Blo 1262449 3462527 := bstep (se 1 (by rfl) ⟨2596895, by rfl⟩ : syracuseStep 3462527 = 5193791) B5193791
theorem B4102121 : Blo 1262449 4102121 := bstep (se 2 (by rfl) ⟨1538295, by rfl⟩ : syracuseStep 4102121 = 3076591) B3076591
theorem B295442423 : Blo 1262449 295442423 := bstep (se 1 (by rfl) ⟨221581817, by rfl⟩ : syracuseStep 295442423 = 443163635) B443163635
theorem B4798673 : Blo 1262449 4798673 := bstep (se 2 (by rfl) ⟨1799502, by rfl⟩ : syracuseStep 4798673 = 3599005) B3599005
theorem B2308583 : Blo 1262449 2308583 := bstep (se 1 (by rfl) ⟨1731437, by rfl⟩ : syracuseStep 2308583 = 3462875) B3462875
theorem B77748943 : Blo 1262449 77748943 := bstep (se 1 (by rfl) ⟨58311707, by rfl⟩ : syracuseStep 77748943 = 116623415) B116623415
theorem B2734975 : Blo 1262449 2734975 := bstep (se 1 (by rfl) ⟨2051231, by rfl⟩ : syracuseStep 2734975 = 4102463) B4102463
theorem B23379151 : Blo 1262449 23379151 := bstep (se 1 (by rfl) ⟨17534363, by rfl⟩ : syracuseStep 23379151 = 35068727) B35068727
theorem B5759311 : Blo 1262449 5759311 := bstep (se 1 (by rfl) ⟨4319483, by rfl⟩ : syracuseStep 5759311 = 8638967) B8638967
theorem B3646633 : Blo 1262449 3646633 := bstep (se 2 (by rfl) ⟨1367487, by rfl⟩ : syracuseStep 3646633 = 2734975) B2734975
theorem B196961615 : Blo 1262449 196961615 := bstep (se 1 (by rfl) ⟨147721211, by rfl⟩ : syracuseStep 196961615 = 295442423) B295442423
theorem B31172201 : Blo 1262449 31172201 := bstep (se 2 (by rfl) ⟨11689575, by rfl⟩ : syracuseStep 31172201 = 23379151) B23379151
theorem B13658057 : Blo 1262449 13658057 := bstep (se 2 (by rfl) ⟨5121771, by rfl⟩ : syracuseStep 13658057 = 10243543) B10243543
theorem B1263783 : Blo 1262449 1263783 := bstep (se 1 (by rfl) ⟨947837, by rfl⟩ : syracuseStep 1263783 = 1895675) B1895675
theorem B16189631 : Blo 1262449 16189631 := bstep (se 1 (by rfl) ⟨12142223, by rfl⟩ : syracuseStep 16189631 = 24284447) B24284447
theorem B10938989 : Blo 1262449 10938989 := bstep (se 3 (by rfl) ⟨2051060, by rfl⟩ : syracuseStep 10938989 = 4102121) B4102121
theorem B1600231 : Blo 1262449 1600231 := bstep (se 1 (by rfl) ⟨1200173, by rfl⟩ : syracuseStep 1600231 = 2400347) B2400347
theorem B1895207 : Blo 1262449 1895207 := bstep (se 1 (by rfl) ⟨1421405, by rfl⟩ : syracuseStep 1895207 = 2842811) B2842811
theorem B13134635 : Blo 1262449 13134635 := bstep (se 1 (by rfl) ⟨9850976, by rfl⟩ : syracuseStep 13134635 = 19701953) B19701953
theorem B262409381 : Blo 1262449 262409381 := bstep (se 4 (by rfl) ⟨24600879, by rfl⟩ : syracuseStep 262409381 = 49201759) B49201759
theorem B1420519 : Blo 1262449 1420519 := bstep (se 1 (by rfl) ⟨1065389, by rfl⟩ : syracuseStep 1420519 = 2130779) B2130779
theorem B1895663 : Blo 1262449 1895663 := bstep (se 1 (by rfl) ⟨1421747, by rfl⟩ : syracuseStep 1895663 = 2843495) B2843495
theorem B3599711 : Blo 1262449 3599711 := bstep (se 1 (by rfl) ⟨2699783, by rfl⟩ : syracuseStep 3599711 = 5399567) B5399567
theorem B13659695 : Blo 1262449 13659695 := bstep (se 1 (by rfl) ⟨10244771, by rfl⟩ : syracuseStep 13659695 = 20489543) B20489543
theorem B103665257 : Blo 1262449 103665257 := bstep (se 2 (by rfl) ⟨38874471, by rfl⟩ : syracuseStep 103665257 = 77748943) B77748943
theorem B6156221 : Blo 1262449 6156221 := bstep (se 3 (by rfl) ⟨1154291, by rfl⟩ : syracuseStep 6156221 = 2308583) B2308583
theorem B3199115 : Blo 1262449 3199115 := bstep (se 1 (by rfl) ⟨2399336, by rfl⟩ : syracuseStep 3199115 = 4798673) B4798673
theorem B9114049 : Blo 1262449 9114049 := bstep (se 2 (by rfl) ⟨3417768, by rfl⟩ : syracuseStep 9114049 = 6835537) B6835537
theorem B14399207 : Blo 1262449 14399207 := bstep (se 1 (by rfl) ⟨10799405, by rfl⟩ : syracuseStep 14399207 = 21598811) B21598811
theorem B29161399 : Blo 1262449 29161399 := bstep (se 1 (by rfl) ⟨21871049, by rfl⟩ : syracuseStep 29161399 = 43742099) B43742099
theorem B13506725 : Blo 1262449 13506725 := bstep (se 4 (by rfl) ⟨1266255, by rfl⟩ : syracuseStep 13506725 = 2532511) B2532511
theorem B2308351 : Blo 1262449 2308351 := bstep (se 1 (by rfl) ⟨1731263, by rfl⟩ : syracuseStep 2308351 = 3462527) B3462527
theorem B7199239 : Blo 1262449 7199239 := bstep (se 1 (by rfl) ⟨5399429, by rfl⟩ : syracuseStep 7199239 = 10798859) B10798859
theorem B6396569 : Blo 1262449 6396569 := bstep (se 2 (by rfl) ⟨2398713, by rfl⟩ : syracuseStep 6396569 = 4797427) B4797427
theorem B6069131 : Blo 1262449 6069131 := bstep (se 1 (by rfl) ⟨4551848, by rfl⟩ : syracuseStep 6069131 = 9103697) B9103697
theorem B2841839 : Blo 1262449 2841839 := bstep (se 1 (by rfl) ⟨2131379, by rfl⟩ : syracuseStep 2841839 = 4262759) B4262759
theorem B9854461 : Blo 1262449 9854461 := bstep (se 3 (by rfl) ⟨1847711, by rfl⟩ : syracuseStep 9854461 = 3695423) B3695423
theorem B10935911 : Blo 1262449 10935911 := bstep (se 1 (by rfl) ⟨8201933, by rfl⟩ : syracuseStep 10935911 = 16403867) B16403867
theorem B2842343 : Blo 1262449 2842343 := bstep (se 1 (by rfl) ⟨2131757, by rfl⟩ : syracuseStep 2842343 = 4263515) B4263515
theorem B9004483 : Blo 1262449 9004483 := bstep (se 1 (by rfl) ⟨6753362, by rfl⟩ : syracuseStep 9004483 = 13506725) B13506725
theorem B1894025 : Blo 1262449 1894025 := bstep (se 2 (by rfl) ⟨710259, by rfl⟩ : syracuseStep 1894025 = 1420519) B1420519
theorem B7292659 : Blo 1262449 7292659 := bstep (se 1 (by rfl) ⟨5469494, by rfl⟩ : syracuseStep 7292659 = 10938989) B10938989
theorem B1263471 : Blo 1262449 1263471 := bstep (se 1 (by rfl) ⟨947603, by rfl⟩ : syracuseStep 1263471 = 1895207) B1895207
theorem B1894559 : Blo 1262449 1894559 := bstep (se 1 (by rfl) ⟨1420919, by rfl⟩ : syracuseStep 1894559 = 2841839) B2841839
theorem B1263775 : Blo 1262449 1263775 := bstep (se 1 (by rfl) ⟨947831, by rfl⟩ : syracuseStep 1263775 = 1895663) B1895663
theorem B69110171 : Blo 1262449 69110171 := bstep (se 1 (by rfl) ⟨51832628, by rfl⟩ : syracuseStep 69110171 = 103665257) B103665257
theorem B1894895 : Blo 1262449 1894895 := bstep (se 1 (by rfl) ⟨1421171, by rfl⟩ : syracuseStep 1894895 = 2842343) B2842343
theorem B38881865 : Blo 1262449 38881865 := bstep (se 2 (by rfl) ⟨14580699, by rfl⟩ : syracuseStep 38881865 = 29161399) B29161399
theorem B2132743 : Blo 1262449 2132743 := bstep (se 1 (by rfl) ⟨1599557, by rfl⟩ : syracuseStep 2132743 = 3199115) B3199115
theorem B7679081 : Blo 1262449 7679081 := bstep (se 2 (by rfl) ⟨2879655, by rfl⟩ : syracuseStep 7679081 = 5759311) B5759311
theorem B12152065 : Blo 1262449 12152065 := bstep (se 2 (by rfl) ⟨4557024, by rfl⟩ : syracuseStep 12152065 = 9114049) B9114049
theorem B2133641 : Blo 1262449 2133641 := bstep (se 2 (by rfl) ⟨800115, by rfl⟩ : syracuseStep 2133641 = 1600231) B1600231
theorem B9105371 : Blo 1262449 9105371 := bstep (se 1 (by rfl) ⟨6829028, by rfl⟩ : syracuseStep 9105371 = 13658057) B13658057
theorem B10793087 : Blo 1262449 10793087 := bstep (se 1 (by rfl) ⟨8094815, by rfl⟩ : syracuseStep 10793087 = 16189631) B16189631
theorem B4862177 : Blo 1262449 4862177 := bstep (se 2 (by rfl) ⟨1823316, by rfl⟩ : syracuseStep 4862177 = 3646633) B3646633
theorem B4264379 : Blo 1262449 4264379 := bstep (se 1 (by rfl) ⟨3198284, by rfl⟩ : syracuseStep 4264379 = 6396569) B6396569
theorem B9106463 : Blo 1262449 9106463 := bstep (se 1 (by rfl) ⟨6829847, by rfl⟩ : syracuseStep 9106463 = 13659695) B13659695
theorem B3077801 : Blo 1262449 3077801 := bstep (se 2 (by rfl) ⟨1154175, by rfl⟩ : syracuseStep 3077801 = 2308351) B2308351
theorem B9598985 : Blo 1262449 9598985 := bstep (se 2 (by rfl) ⟨3599619, by rfl⟩ : syracuseStep 9598985 = 7199239) B7199239
theorem B131307743 : Blo 1262449 131307743 := bstep (se 1 (by rfl) ⟨98480807, by rfl⟩ : syracuseStep 131307743 = 196961615) B196961615
theorem B20781467 : Blo 1262449 20781467 := bstep (se 1 (by rfl) ⟨15586100, by rfl⟩ : syracuseStep 20781467 = 31172201) B31172201
theorem B9599471 : Blo 1262449 9599471 := bstep (se 1 (by rfl) ⟨7199603, by rfl⟩ : syracuseStep 9599471 = 14399207) B14399207
theorem B29162429 : Blo 1262449 29162429 := bstep (se 3 (by rfl) ⟨5467955, by rfl⟩ : syracuseStep 29162429 = 10935911) B10935911
theorem B8756423 : Blo 1262449 8756423 := bstep (se 1 (by rfl) ⟨6567317, by rfl⟩ : syracuseStep 8756423 = 13134635) B13134635
theorem B4046087 : Blo 1262449 4046087 := bstep (se 1 (by rfl) ⟨3034565, by rfl⟩ : syracuseStep 4046087 = 6069131) B6069131
theorem B13139281 : Blo 1262449 13139281 := bstep (se 2 (by rfl) ⟨4927230, by rfl⟩ : syracuseStep 13139281 = 9854461) B9854461
theorem B174939587 : Blo 1262449 174939587 := bstep (se 1 (by rfl) ⟨131204690, by rfl⟩ : syracuseStep 174939587 = 262409381) B262409381
theorem B2399807 : Blo 1262449 2399807 := bstep (se 1 (by rfl) ⟨1799855, by rfl⟩ : syracuseStep 2399807 = 3599711) B3599711
theorem B16416589 : Blo 1262449 16416589 := bstep (se 3 (by rfl) ⟨3078110, by rfl⟩ : syracuseStep 16416589 = 6156221) B6156221
theorem B2842919 : Blo 1262449 2842919 := bstep (se 1 (by rfl) ⟨2132189, by rfl⟩ : syracuseStep 2842919 = 4264379) B4264379
theorem B2843657 : Blo 1262449 2843657 := bstep (se 2 (by rfl) ⟨1066371, by rfl⟩ : syracuseStep 2843657 = 2132743) B2132743
theorem B1262683 : Blo 1262449 1262683 := bstep (se 1 (by rfl) ⟨947012, by rfl⟩ : syracuseStep 1262683 = 1894025) B1894025
theorem B6399323 : Blo 1262449 6399323 := bstep (se 1 (by rfl) ⟨4799492, by rfl⟩ : syracuseStep 6399323 = 9598985) B9598985
theorem B1263039 : Blo 1262449 1263039 := bstep (se 1 (by rfl) ⟨947279, by rfl⟩ : syracuseStep 1263039 = 1894559) B1894559
theorem B6399485 : Blo 1262449 6399485 := bstep (se 3 (by rfl) ⟨1199903, by rfl⟩ : syracuseStep 6399485 = 2399807) B2399807
theorem B46073447 : Blo 1262449 46073447 := bstep (se 1 (by rfl) ⟨34555085, by rfl⟩ : syracuseStep 46073447 = 69110171) B69110171
theorem B13854311 : Blo 1262449 13854311 := bstep (se 1 (by rfl) ⟨10390733, by rfl⟩ : syracuseStep 13854311 = 20781467) B20781467
theorem B1263263 : Blo 1262449 1263263 := bstep (se 1 (by rfl) ⟨947447, by rfl⟩ : syracuseStep 1263263 = 1894895) B1894895
theorem B6399647 : Blo 1262449 6399647 := bstep (se 1 (by rfl) ⟨4799735, by rfl⟩ : syracuseStep 6399647 = 9599471) B9599471
theorem B25921243 : Blo 1262449 25921243 := bstep (se 1 (by rfl) ⟨19440932, by rfl⟩ : syracuseStep 25921243 = 38881865) B38881865
theorem B19441619 : Blo 1262449 19441619 := bstep (se 1 (by rfl) ⟨14581214, by rfl⟩ : syracuseStep 19441619 = 29162429) B29162429
theorem B2697391 : Blo 1262449 2697391 := bstep (se 1 (by rfl) ⟨2023043, by rfl⟩ : syracuseStep 2697391 = 4046087) B4046087
theorem B24283901 : Blo 1262449 24283901 := bstep (se 3 (by rfl) ⟨4553231, by rfl⟩ : syracuseStep 24283901 = 9106463) B9106463
theorem B7195391 : Blo 1262449 7195391 := bstep (se 1 (by rfl) ⟨5396543, by rfl⟩ : syracuseStep 7195391 = 10793087) B10793087
theorem B2051867 : Blo 1262449 2051867 := bstep (se 1 (by rfl) ⟨1538900, by rfl⟩ : syracuseStep 2051867 = 3077801) B3077801
theorem B17519041 : Blo 1262449 17519041 := bstep (se 2 (by rfl) ⟨6569640, by rfl⟩ : syracuseStep 17519041 = 13139281) B13139281
theorem B12005977 : Blo 1262449 12005977 := bstep (se 2 (by rfl) ⟨4502241, by rfl⟩ : syracuseStep 12005977 = 9004483) B9004483
theorem B5837615 : Blo 1262449 5837615 := bstep (se 1 (by rfl) ⟨4378211, by rfl⟩ : syracuseStep 5837615 = 8756423) B8756423
theorem B116626391 : Blo 1262449 116626391 := bstep (se 1 (by rfl) ⟨87469793, by rfl⟩ : syracuseStep 116626391 = 174939587) B174939587
theorem B1422427 : Blo 1262449 1422427 := bstep (se 1 (by rfl) ⟨1066820, by rfl⟩ : syracuseStep 1422427 = 2133641) B2133641
theorem B3241451 : Blo 1262449 3241451 := bstep (se 1 (by rfl) ⟨2431088, by rfl⟩ : syracuseStep 3241451 = 4862177) B4862177
theorem B20477549 : Blo 1262449 20477549 := bstep (se 3 (by rfl) ⟨3839540, by rfl⟩ : syracuseStep 20477549 = 7679081) B7679081
theorem B87538495 : Blo 1262449 87538495 := bstep (se 1 (by rfl) ⟨65653871, by rfl⟩ : syracuseStep 87538495 = 131307743) B131307743
theorem B16202753 : Blo 1262449 16202753 := bstep (se 2 (by rfl) ⟨6076032, by rfl⟩ : syracuseStep 16202753 = 12152065) B12152065
theorem B9723545 : Blo 1262449 9723545 := bstep (se 2 (by rfl) ⟨3646329, by rfl⟩ : syracuseStep 9723545 = 7292659) B7292659
theorem B21888785 : Blo 1262449 21888785 := bstep (se 2 (by rfl) ⟨8208294, by rfl⟩ : syracuseStep 21888785 = 16416589) B16416589
theorem B6070247 : Blo 1262449 6070247 := bstep (se 1 (by rfl) ⟨4552685, by rfl⟩ : syracuseStep 6070247 = 9105371) B9105371
theorem B3891743 : Blo 1262449 3891743 := bstep (se 1 (by rfl) ⟨2918807, by rfl⟩ : syracuseStep 3891743 = 5837615) B5837615
theorem B77750927 : Blo 1262449 77750927 := bstep (se 1 (by rfl) ⟨58313195, by rfl⟩ : syracuseStep 77750927 = 116626391) B116626391
theorem B16007969 : Blo 1262449 16007969 := bstep (se 2 (by rfl) ⟨6002988, by rfl⟩ : syracuseStep 16007969 = 12005977) B12005977
theorem B14386085 : Blo 1262449 14386085 := bstep (se 4 (by rfl) ⟨1348695, by rfl⟩ : syracuseStep 14386085 = 2697391) B2697391
theorem B12961079 : Blo 1262449 12961079 := bstep (se 1 (by rfl) ⟨9720809, by rfl⟩ : syracuseStep 12961079 = 19441619) B19441619
theorem B16189267 : Blo 1262449 16189267 := bstep (se 1 (by rfl) ⟨12141950, by rfl⟩ : syracuseStep 16189267 = 24283901) B24283901
theorem B6482363 : Blo 1262449 6482363 := bstep (se 1 (by rfl) ⟨4861772, by rfl⟩ : syracuseStep 6482363 = 9723545) B9723545
theorem B14592523 : Blo 1262449 14592523 := bstep (se 1 (by rfl) ⟨10944392, by rfl⟩ : syracuseStep 14592523 = 21888785) B21888785
theorem B1895279 : Blo 1262449 1895279 := bstep (se 1 (by rfl) ⟨1421459, by rfl⟩ : syracuseStep 1895279 = 2842919) B2842919
theorem B23358721 : Blo 1262449 23358721 := bstep (se 2 (by rfl) ⟨8759520, by rfl⟩ : syracuseStep 23358721 = 17519041) B17519041
theorem B1895771 : Blo 1262449 1895771 := bstep (se 1 (by rfl) ⟨1421828, by rfl⟩ : syracuseStep 1895771 = 2843657) B2843657
theorem B30715631 : Blo 1262449 30715631 := bstep (se 1 (by rfl) ⟨23036723, by rfl⟩ : syracuseStep 30715631 = 46073447) B46073447
theorem B9236207 : Blo 1262449 9236207 := bstep (se 1 (by rfl) ⟨6927155, by rfl⟩ : syracuseStep 9236207 = 13854311) B13854311
theorem B13651699 : Blo 1262449 13651699 := bstep (se 1 (by rfl) ⟨10238774, by rfl⟩ : syracuseStep 13651699 = 20477549) B20477549
theorem B1896569 : Blo 1262449 1896569 := bstep (se 2 (by rfl) ⟨711213, by rfl⟩ : syracuseStep 1896569 = 1422427) B1422427
theorem B4796927 : Blo 1262449 4796927 := bstep (se 1 (by rfl) ⟨3597695, by rfl⟩ : syracuseStep 4796927 = 7195391) B7195391
theorem B10801835 : Blo 1262449 10801835 := bstep (se 1 (by rfl) ⟨8101376, by rfl⟩ : syracuseStep 10801835 = 16202753) B16202753
theorem B4266215 : Blo 1262449 4266215 := bstep (se 1 (by rfl) ⟨3199661, by rfl⟩ : syracuseStep 4266215 = 6399323) B6399323
theorem B2160967 : Blo 1262449 2160967 := bstep (se 1 (by rfl) ⟨1620725, by rfl⟩ : syracuseStep 2160967 = 3241451) B3241451
theorem B4266323 : Blo 1262449 4266323 := bstep (se 1 (by rfl) ⟨3199742, by rfl⟩ : syracuseStep 4266323 = 6399485) B6399485
theorem B116717993 : Blo 1262449 116717993 := bstep (se 2 (by rfl) ⟨43769247, by rfl⟩ : syracuseStep 116717993 = 87538495) B87538495
theorem B4266431 : Blo 1262449 4266431 := bstep (se 1 (by rfl) ⟨3199823, by rfl⟩ : syracuseStep 4266431 = 6399647) B6399647
theorem B34561657 : Blo 1262449 34561657 := bstep (se 2 (by rfl) ⟨12960621, by rfl⟩ : syracuseStep 34561657 = 25921243) B25921243
theorem B1367911 : Blo 1262449 1367911 := bstep (se 1 (by rfl) ⟨1025933, by rfl⟩ : syracuseStep 1367911 = 2051867) B2051867
theorem B4046831 : Blo 1262449 4046831 := bstep (se 1 (by rfl) ⟨3035123, by rfl⟩ : syracuseStep 4046831 = 6070247) B6070247
theorem B7201223 : Blo 1262449 7201223 := bstep (se 1 (by rfl) ⟨5400917, by rfl⟩ : syracuseStep 7201223 = 10801835) B10801835
theorem B19456697 : Blo 1262449 19456697 := bstep (se 2 (by rfl) ⟨7296261, by rfl⟩ : syracuseStep 19456697 = 14592523) B14592523
theorem B17286301 : Blo 1262449 17286301 := bstep (se 3 (by rfl) ⟨3241181, by rfl⟩ : syracuseStep 17286301 = 6482363) B6482363
theorem B2844143 : Blo 1262449 2844143 := bstep (se 1 (by rfl) ⟨2133107, by rfl⟩ : syracuseStep 2844143 = 4266215) B4266215
theorem B2844215 : Blo 1262449 2844215 := bstep (se 1 (by rfl) ⟨2133161, by rfl⟩ : syracuseStep 2844215 = 4266323) B4266323
theorem B2844287 : Blo 1262449 2844287 := bstep (se 1 (by rfl) ⟨2133215, by rfl⟩ : syracuseStep 2844287 = 4266431) B4266431
theorem B1263519 : Blo 1262449 1263519 := bstep (se 1 (by rfl) ⟨947639, by rfl⟩ : syracuseStep 1263519 = 1895279) B1895279
theorem B46082209 : Blo 1262449 46082209 := bstep (se 2 (by rfl) ⟨17280828, by rfl⟩ : syracuseStep 46082209 = 34561657) B34561657
theorem B1263847 : Blo 1262449 1263847 := bstep (se 1 (by rfl) ⟨947885, by rfl⟩ : syracuseStep 1263847 = 1895771) B1895771
theorem B2697887 : Blo 1262449 2697887 := bstep (se 1 (by rfl) ⟨2023415, by rfl⟩ : syracuseStep 2697887 = 4046831) B4046831
theorem B1264379 : Blo 1262449 1264379 := bstep (se 1 (by rfl) ⟨948284, by rfl⟩ : syracuseStep 1264379 = 1896569) B1896569
theorem B3197951 : Blo 1262449 3197951 := bstep (se 1 (by rfl) ⟨2398463, by rfl⟩ : syracuseStep 3197951 = 4796927) B4796927
theorem B51833951 : Blo 1262449 51833951 := bstep (se 1 (by rfl) ⟨38875463, by rfl⟩ : syracuseStep 51833951 = 77750927) B77750927
theorem B77811995 : Blo 1262449 77811995 := bstep (se 1 (by rfl) ⟨58358996, by rfl⟩ : syracuseStep 77811995 = 116717993) B116717993
theorem B7295525 : Blo 1262449 7295525 := bstep (se 4 (by rfl) ⟨683955, by rfl⟩ : syracuseStep 7295525 = 1367911) B1367911
theorem B20477087 : Blo 1262449 20477087 := bstep (se 1 (by rfl) ⟨15357815, by rfl⟩ : syracuseStep 20477087 = 30715631) B30715631
theorem B6157471 : Blo 1262449 6157471 := bstep (se 1 (by rfl) ⟨4618103, by rfl⟩ : syracuseStep 6157471 = 9236207) B9236207
theorem B2594495 : Blo 1262449 2594495 := bstep (se 1 (by rfl) ⟨1945871, by rfl⟩ : syracuseStep 2594495 = 3891743) B3891743
theorem B2881289 : Blo 1262449 2881289 := bstep (se 2 (by rfl) ⟨1080483, by rfl⟩ : syracuseStep 2881289 = 2160967) B2160967
theorem B9590723 : Blo 1262449 9590723 := bstep (se 1 (by rfl) ⟨7193042, by rfl⟩ : syracuseStep 9590723 = 14386085) B14386085
theorem B8640719 : Blo 1262449 8640719 := bstep (se 1 (by rfl) ⟨6480539, by rfl⟩ : syracuseStep 8640719 = 12961079) B12961079
theorem B31144961 : Blo 1262449 31144961 := bstep (se 2 (by rfl) ⟨11679360, by rfl⟩ : syracuseStep 31144961 = 23358721) B23358721
theorem B42687917 : Blo 1262449 42687917 := bstep (se 3 (by rfl) ⟨8003984, by rfl⟩ : syracuseStep 42687917 = 16007969) B16007969
theorem B18202265 : Blo 1262449 18202265 := bstep (se 2 (by rfl) ⟨6825849, by rfl⟩ : syracuseStep 18202265 = 13651699) B13651699
theorem B21585689 : Blo 1262449 21585689 := bstep (se 2 (by rfl) ⟨8094633, by rfl⟩ : syracuseStep 21585689 = 16189267) B16189267
theorem B4800815 : Blo 1262449 4800815 := bstep (se 1 (by rfl) ⟨3600611, by rfl⟩ : syracuseStep 4800815 = 7201223) B7201223
theorem B1729663 : Blo 1262449 1729663 := bstep (se 1 (by rfl) ⟨1297247, by rfl⟩ : syracuseStep 1729663 = 2594495) B2594495
theorem B5760479 : Blo 1262449 5760479 := bstep (se 1 (by rfl) ⟨4320359, by rfl⟩ : syracuseStep 5760479 = 8640719) B8640719
theorem B8209961 : Blo 1262449 8209961 := bstep (se 2 (by rfl) ⟨3078735, by rfl⟩ : syracuseStep 8209961 = 6157471) B6157471
theorem B7194365 : Blo 1262449 7194365 := bstep (se 3 (by rfl) ⟨1348943, by rfl⟩ : syracuseStep 7194365 = 2697887) B2697887
theorem B2131967 : Blo 1262449 2131967 := bstep (se 1 (by rfl) ⟨1598975, by rfl⟩ : syracuseStep 2131967 = 3197951) B3197951
theorem B34555967 : Blo 1262449 34555967 := bstep (se 1 (by rfl) ⟨25916975, by rfl⟩ : syracuseStep 34555967 = 51833951) B51833951
theorem B12134843 : Blo 1262449 12134843 := bstep (se 1 (by rfl) ⟨9101132, by rfl⟩ : syracuseStep 12134843 = 18202265) B18202265
theorem B51874663 : Blo 1262449 51874663 := bstep (se 1 (by rfl) ⟨38905997, by rfl⟩ : syracuseStep 51874663 = 77811995) B77811995
theorem B61442945 : Blo 1262449 61442945 := bstep (se 2 (by rfl) ⟨23041104, by rfl⟩ : syracuseStep 61442945 = 46082209) B46082209
theorem B13651391 : Blo 1262449 13651391 := bstep (se 1 (by rfl) ⟨10238543, by rfl⟩ : syracuseStep 13651391 = 20477087) B20477087
theorem B1896095 : Blo 1262449 1896095 := bstep (se 1 (by rfl) ⟨1422071, by rfl⟩ : syracuseStep 1896095 = 2844143) B2844143
theorem B1896143 : Blo 1262449 1896143 := bstep (se 1 (by rfl) ⟨1422107, by rfl⟩ : syracuseStep 1896143 = 2844215) B2844215
theorem B1896191 : Blo 1262449 1896191 := bstep (se 1 (by rfl) ⟨1422143, by rfl⟩ : syracuseStep 1896191 = 2844287) B2844287
theorem B6393815 : Blo 1262449 6393815 := bstep (se 1 (by rfl) ⟨4795361, by rfl⟩ : syracuseStep 6393815 = 9590723) B9590723
theorem B23048401 : Blo 1262449 23048401 := bstep (se 2 (by rfl) ⟨8643150, by rfl⟩ : syracuseStep 23048401 = 17286301) B17286301
theorem B51884525 : Blo 1262449 51884525 := bstep (se 3 (by rfl) ⟨9728348, by rfl⟩ : syracuseStep 51884525 = 19456697) B19456697
theorem B20763307 : Blo 1262449 20763307 := bstep (se 1 (by rfl) ⟨15572480, by rfl⟩ : syracuseStep 20763307 = 31144961) B31144961
theorem B14390459 : Blo 1262449 14390459 := bstep (se 1 (by rfl) ⟨10792844, by rfl⟩ : syracuseStep 14390459 = 21585689) B21585689
theorem B4863683 : Blo 1262449 4863683 := bstep (se 1 (by rfl) ⟨3647762, by rfl⟩ : syracuseStep 4863683 = 7295525) B7295525
theorem B7683437 : Blo 1262449 7683437 := bstep (se 3 (by rfl) ⟨1440644, by rfl⟩ : syracuseStep 7683437 = 2881289) B2881289
theorem B28458611 : Blo 1262449 28458611 := bstep (se 1 (by rfl) ⟨21343958, by rfl⟩ : syracuseStep 28458611 = 42687917) B42687917
theorem B9224869 : Blo 1262449 9224869 := bstep (se 4 (by rfl) ⟨864831, by rfl⟩ : syracuseStep 9224869 = 1729663) B1729663
theorem B9593639 : Blo 1262449 9593639 := bstep (se 1 (by rfl) ⟨7195229, by rfl⟩ : syracuseStep 9593639 = 14390459) B14390459
theorem B5473307 : Blo 1262449 5473307 := bstep (se 1 (by rfl) ⟨4104980, by rfl⟩ : syracuseStep 5473307 = 8209961) B8209961
theorem B69166217 : Blo 1262449 69166217 := bstep (se 2 (by rfl) ⟨25937331, by rfl⟩ : syracuseStep 69166217 = 51874663) B51874663
theorem B23037311 : Blo 1262449 23037311 := bstep (se 1 (by rfl) ⟨17277983, by rfl⟩ : syracuseStep 23037311 = 34555967) B34555967
theorem B12969821 : Blo 1262449 12969821 := bstep (se 3 (by rfl) ⟨2431841, by rfl⟩ : syracuseStep 12969821 = 4863683) B4863683
theorem B40961963 : Blo 1262449 40961963 := bstep (se 1 (by rfl) ⟨30721472, by rfl⟩ : syracuseStep 40961963 = 61442945) B61442945
theorem B5122291 : Blo 1262449 5122291 := bstep (se 1 (by rfl) ⟨3841718, by rfl⟩ : syracuseStep 5122291 = 7683437) B7683437
theorem B1264063 : Blo 1262449 1264063 := bstep (se 1 (by rfl) ⟨948047, by rfl⟩ : syracuseStep 1264063 = 1896095) B1896095
theorem B1264095 : Blo 1262449 1264095 := bstep (se 1 (by rfl) ⟨948071, by rfl⟩ : syracuseStep 1264095 = 1896143) B1896143
theorem B1264127 : Blo 1262449 1264127 := bstep (se 1 (by rfl) ⟨948095, by rfl⟩ : syracuseStep 1264127 = 1896191) B1896191
theorem B4262543 : Blo 1262449 4262543 := bstep (se 1 (by rfl) ⟨3196907, by rfl⟩ : syracuseStep 4262543 = 6393815) B6393815
theorem B30731201 : Blo 1262449 30731201 := bstep (se 2 (by rfl) ⟨11524200, by rfl⟩ : syracuseStep 30731201 = 23048401) B23048401
theorem B34589683 : Blo 1262449 34589683 := bstep (se 1 (by rfl) ⟨25942262, by rfl⟩ : syracuseStep 34589683 = 51884525) B51884525
theorem B4796243 : Blo 1262449 4796243 := bstep (se 1 (by rfl) ⟨3597182, by rfl⟩ : syracuseStep 4796243 = 7194365) B7194365
theorem B1421311 : Blo 1262449 1421311 := bstep (se 1 (by rfl) ⟨1065983, by rfl⟩ : syracuseStep 1421311 = 2131967) B2131967
theorem B8089895 : Blo 1262449 8089895 := bstep (se 1 (by rfl) ⟨6067421, by rfl⟩ : syracuseStep 8089895 = 12134843) B12134843
theorem B3200543 : Blo 1262449 3200543 := bstep (se 1 (by rfl) ⟨2400407, by rfl⟩ : syracuseStep 3200543 = 4800815) B4800815
theorem B110737637 : Blo 1262449 110737637 := bstep (se 4 (by rfl) ⟨10381653, by rfl⟩ : syracuseStep 110737637 = 20763307) B20763307
theorem B3840319 : Blo 1262449 3840319 := bstep (se 1 (by rfl) ⟨2880239, by rfl⟩ : syracuseStep 3840319 = 5760479) B5760479
theorem B9100927 : Blo 1262449 9100927 := bstep (se 1 (by rfl) ⟨6825695, by rfl⟩ : syracuseStep 9100927 = 13651391) B13651391
theorem B18972407 : Blo 1262449 18972407 := bstep (se 1 (by rfl) ⟨14229305, by rfl⟩ : syracuseStep 18972407 = 28458611) B28458611
theorem B5120425 : Blo 1262449 5120425 := bstep (se 2 (by rfl) ⟨1920159, by rfl⟩ : syracuseStep 5120425 = 3840319) B3840319
theorem B48538277 : Blo 1262449 48538277 := bstep (se 4 (by rfl) ⟨4550463, by rfl⟩ : syracuseStep 48538277 = 9100927) B9100927
theorem B61432829 : Blo 1262449 61432829 := bstep (se 3 (by rfl) ⟨11518655, by rfl⟩ : syracuseStep 61432829 = 23037311) B23037311
theorem B3197495 : Blo 1262449 3197495 := bstep (se 1 (by rfl) ⟨2398121, by rfl⟩ : syracuseStep 3197495 = 4796243) B4796243
theorem B1895081 : Blo 1262449 1895081 := bstep (se 2 (by rfl) ⟨710655, by rfl⟩ : syracuseStep 1895081 = 1421311) B1421311
theorem B5393263 : Blo 1262449 5393263 := bstep (se 1 (by rfl) ⟨4044947, by rfl⟩ : syracuseStep 5393263 = 8089895) B8089895
theorem B3648871 : Blo 1262449 3648871 := bstep (se 1 (by rfl) ⟨2736653, by rfl⟩ : syracuseStep 3648871 = 5473307) B5473307
theorem B12299825 : Blo 1262449 12299825 := bstep (se 2 (by rfl) ⟨4612434, by rfl⟩ : syracuseStep 12299825 = 9224869) B9224869
theorem B2133695 : Blo 1262449 2133695 := bstep (se 1 (by rfl) ⟨1600271, by rfl⟩ : syracuseStep 2133695 = 3200543) B3200543
theorem B27307975 : Blo 1262449 27307975 := bstep (se 1 (by rfl) ⟨20480981, by rfl⟩ : syracuseStep 27307975 = 40961963) B40961963
theorem B6829721 : Blo 1262449 6829721 := bstep (se 2 (by rfl) ⟨2561145, by rfl⟩ : syracuseStep 6829721 = 5122291) B5122291
theorem B6395759 : Blo 1262449 6395759 := bstep (se 1 (by rfl) ⟨4796819, by rfl⟩ : syracuseStep 6395759 = 9593639) B9593639
theorem B46110811 : Blo 1262449 46110811 := bstep (se 1 (by rfl) ⟨34583108, by rfl⟩ : syracuseStep 46110811 = 69166217) B69166217
theorem B46119577 : Blo 1262449 46119577 := bstep (se 2 (by rfl) ⟨17294841, by rfl⟩ : syracuseStep 46119577 = 34589683) B34589683
theorem B73825091 : Blo 1262449 73825091 := bstep (se 1 (by rfl) ⟨55368818, by rfl⟩ : syracuseStep 73825091 = 110737637) B110737637
theorem B2841695 : Blo 1262449 2841695 := bstep (se 1 (by rfl) ⟨2131271, by rfl⟩ : syracuseStep 2841695 = 4262543) B4262543
theorem B20487467 : Blo 1262449 20487467 := bstep (se 1 (by rfl) ⟨15365600, by rfl⟩ : syracuseStep 20487467 = 30731201) B30731201
theorem B34586189 : Blo 1262449 34586189 := bstep (se 3 (by rfl) ⟨6484910, by rfl⟩ : syracuseStep 34586189 = 12969821) B12969821
theorem B12648271 : Blo 1262449 12648271 := bstep (se 1 (by rfl) ⟨9486203, by rfl⟩ : syracuseStep 12648271 = 18972407) B18972407
theorem B61481081 : Blo 1262449 61481081 := bstep (se 2 (by rfl) ⟨23055405, by rfl⟩ : syracuseStep 61481081 = 46110811) B46110811
theorem B32358851 : Blo 1262449 32358851 := bstep (se 1 (by rfl) ⟨24269138, by rfl⟩ : syracuseStep 32358851 = 48538277) B48538277
theorem B2131663 : Blo 1262449 2131663 := bstep (se 1 (by rfl) ⟨1598747, by rfl⟩ : syracuseStep 2131663 = 3197495) B3197495
theorem B1263387 : Blo 1262449 1263387 := bstep (se 1 (by rfl) ⟨947540, by rfl⟩ : syracuseStep 1263387 = 1895081) B1895081
theorem B1894463 : Blo 1262449 1894463 := bstep (se 1 (by rfl) ⟨1420847, by rfl⟩ : syracuseStep 1894463 = 2841695) B2841695
theorem B13658311 : Blo 1262449 13658311 := bstep (se 1 (by rfl) ⟨10243733, by rfl⟩ : syracuseStep 13658311 = 20487467) B20487467
theorem B40955219 : Blo 1262449 40955219 := bstep (se 1 (by rfl) ⟨30716414, by rfl⟩ : syracuseStep 40955219 = 61432829) B61432829
theorem B61492769 : Blo 1262449 61492769 := bstep (se 2 (by rfl) ⟨23059788, by rfl⟩ : syracuseStep 61492769 = 46119577) B46119577
theorem B4263839 : Blo 1262449 4263839 := bstep (se 1 (by rfl) ⟨3197879, by rfl⟩ : syracuseStep 4263839 = 6395759) B6395759
theorem B19460645 : Blo 1262449 19460645 := bstep (se 4 (by rfl) ⟨1824435, by rfl⟩ : syracuseStep 19460645 = 3648871) B3648871
theorem B27308933 : Blo 1262449 27308933 := bstep (se 4 (by rfl) ⟨2560212, by rfl⟩ : syracuseStep 27308933 = 5120425) B5120425
theorem B23057459 : Blo 1262449 23057459 := bstep (se 1 (by rfl) ⟨17293094, by rfl⟩ : syracuseStep 23057459 = 34586189) B34586189
theorem B16864361 : Blo 1262449 16864361 := bstep (se 2 (by rfl) ⟨6324135, by rfl⟩ : syracuseStep 16864361 = 12648271) B12648271
theorem B1422463 : Blo 1262449 1422463 := bstep (se 1 (by rfl) ⟨1066847, by rfl⟩ : syracuseStep 1422463 = 2133695) B2133695
theorem B36410633 : Blo 1262449 36410633 := bstep (se 2 (by rfl) ⟨13653987, by rfl⟩ : syracuseStep 36410633 = 27307975) B27307975
theorem B4553147 : Blo 1262449 4553147 := bstep (se 1 (by rfl) ⟨3414860, by rfl⟩ : syracuseStep 4553147 = 6829721) B6829721
theorem B7191017 : Blo 1262449 7191017 := bstep (se 2 (by rfl) ⟨2696631, by rfl⟩ : syracuseStep 7191017 = 5393263) B5393263
theorem B49216727 : Blo 1262449 49216727 := bstep (se 1 (by rfl) ⟨36912545, by rfl⟩ : syracuseStep 49216727 = 73825091) B73825091
theorem B8199883 : Blo 1262449 8199883 := bstep (se 1 (by rfl) ⟨6149912, by rfl⟩ : syracuseStep 8199883 = 12299825) B12299825
theorem B18211081 : Blo 1262449 18211081 := bstep (se 2 (by rfl) ⟨6829155, by rfl⟩ : syracuseStep 18211081 = 13658311) B13658311
theorem B24273755 : Blo 1262449 24273755 := bstep (se 1 (by rfl) ⟨18205316, by rfl⟩ : syracuseStep 24273755 = 36410633) B36410633
theorem B1262975 : Blo 1262449 1262975 := bstep (se 1 (by rfl) ⟨947231, by rfl⟩ : syracuseStep 1262975 = 1894463) B1894463
theorem B4794011 : Blo 1262449 4794011 := bstep (se 1 (by rfl) ⟨3595508, by rfl⟩ : syracuseStep 4794011 = 7191017) B7191017
theorem B32811151 : Blo 1262449 32811151 := bstep (se 1 (by rfl) ⟨24608363, by rfl⟩ : syracuseStep 32811151 = 49216727) B49216727
theorem B40995179 : Blo 1262449 40995179 := bstep (se 1 (by rfl) ⟨30746384, by rfl⟩ : syracuseStep 40995179 = 61492769) B61492769
theorem B40987387 : Blo 1262449 40987387 := bstep (se 1 (by rfl) ⟨30740540, by rfl⟩ : syracuseStep 40987387 = 61481081) B61481081
theorem B21572567 : Blo 1262449 21572567 := bstep (se 1 (by rfl) ⟨16179425, by rfl⟩ : syracuseStep 21572567 = 32358851) B32358851
theorem B18205955 : Blo 1262449 18205955 := bstep (se 1 (by rfl) ⟨13654466, by rfl⟩ : syracuseStep 18205955 = 27308933) B27308933
theorem B15371639 : Blo 1262449 15371639 := bstep (se 1 (by rfl) ⟨11528729, by rfl⟩ : syracuseStep 15371639 = 23057459) B23057459
theorem B11242907 : Blo 1262449 11242907 := bstep (se 1 (by rfl) ⟨8432180, by rfl⟩ : syracuseStep 11242907 = 16864361) B16864361
theorem B43732709 : Blo 1262449 43732709 := bstep (se 4 (by rfl) ⟨4099941, by rfl⟩ : syracuseStep 43732709 = 8199883) B8199883
theorem B1896617 : Blo 1262449 1896617 := bstep (se 2 (by rfl) ⟨711231, by rfl⟩ : syracuseStep 1896617 = 1422463) B1422463
theorem B3035431 : Blo 1262449 3035431 := bstep (se 1 (by rfl) ⟨2276573, by rfl⟩ : syracuseStep 3035431 = 4553147) B4553147
theorem B12973763 : Blo 1262449 12973763 := bstep (se 1 (by rfl) ⟨9730322, by rfl⟩ : syracuseStep 12973763 = 19460645) B19460645
theorem B27303479 : Blo 1262449 27303479 := bstep (se 1 (by rfl) ⟨20477609, by rfl⟩ : syracuseStep 27303479 = 40955219) B40955219
theorem B2842217 : Blo 1262449 2842217 := bstep (se 2 (by rfl) ⟨1065831, by rfl⟩ : syracuseStep 2842217 = 2131663) B2131663
theorem B2842559 : Blo 1262449 2842559 := bstep (se 1 (by rfl) ⟨2131919, by rfl⟩ : syracuseStep 2842559 = 4263839) B4263839
theorem B24281441 : Blo 1262449 24281441 := bstep (se 2 (by rfl) ⟨9105540, by rfl⟩ : syracuseStep 24281441 = 18211081) B18211081
theorem B4047241 : Blo 1262449 4047241 := bstep (se 2 (by rfl) ⟨1517715, by rfl⟩ : syracuseStep 4047241 = 3035431) B3035431
theorem B54649849 : Blo 1262449 54649849 := bstep (se 2 (by rfl) ⟨20493693, by rfl⟩ : syracuseStep 54649849 = 40987387) B40987387
theorem B3196007 : Blo 1262449 3196007 := bstep (se 1 (by rfl) ⟨2397005, by rfl⟩ : syracuseStep 3196007 = 4794011) B4794011
theorem B27330119 : Blo 1262449 27330119 := bstep (se 1 (by rfl) ⟨20497589, by rfl⟩ : syracuseStep 27330119 = 40995179) B40995179
theorem B1894811 : Blo 1262449 1894811 := bstep (se 1 (by rfl) ⟨1421108, by rfl⟩ : syracuseStep 1894811 = 2842217) B2842217
theorem B1895039 : Blo 1262449 1895039 := bstep (se 1 (by rfl) ⟨1421279, by rfl⟩ : syracuseStep 1895039 = 2842559) B2842559
theorem B1264411 : Blo 1262449 1264411 := bstep (se 1 (by rfl) ⟨948308, by rfl⟩ : syracuseStep 1264411 = 1896617) B1896617
theorem B43748201 : Blo 1262449 43748201 := bstep (se 2 (by rfl) ⟨16405575, by rfl⟩ : syracuseStep 43748201 = 32811151) B32811151
theorem B16182503 : Blo 1262449 16182503 := bstep (se 1 (by rfl) ⟨12136877, by rfl⟩ : syracuseStep 16182503 = 24273755) B24273755
theorem B14381711 : Blo 1262449 14381711 := bstep (se 1 (by rfl) ⟨10786283, by rfl⟩ : syracuseStep 14381711 = 21572567) B21572567
theorem B12137303 : Blo 1262449 12137303 := bstep (se 1 (by rfl) ⟨9102977, by rfl⟩ : syracuseStep 12137303 = 18205955) B18205955
theorem B8649175 : Blo 1262449 8649175 := bstep (se 1 (by rfl) ⟨6486881, by rfl⟩ : syracuseStep 8649175 = 12973763) B12973763
theorem B10247759 : Blo 1262449 10247759 := bstep (se 1 (by rfl) ⟨7685819, by rfl⟩ : syracuseStep 10247759 = 15371639) B15371639
theorem B7495271 : Blo 1262449 7495271 := bstep (se 1 (by rfl) ⟨5621453, by rfl⟩ : syracuseStep 7495271 = 11242907) B11242907
theorem B18202319 : Blo 1262449 18202319 := bstep (se 1 (by rfl) ⟨13651739, by rfl⟩ : syracuseStep 18202319 = 27303479) B27303479
theorem B29155139 : Blo 1262449 29155139 := bstep (se 1 (by rfl) ⟨21866354, by rfl⟩ : syracuseStep 29155139 = 43732709) B43732709
theorem B16187627 : Blo 1262449 16187627 := bstep (se 1 (by rfl) ⟨12140720, by rfl⟩ : syracuseStep 16187627 = 24281441) B24281441
theorem B2130671 : Blo 1262449 2130671 := bstep (se 1 (by rfl) ⟨1598003, by rfl⟩ : syracuseStep 2130671 = 3196007) B3196007
theorem B18220079 : Blo 1262449 18220079 := bstep (se 1 (by rfl) ⟨13665059, by rfl⟩ : syracuseStep 18220079 = 27330119) B27330119
theorem B1263207 : Blo 1262449 1263207 := bstep (se 1 (by rfl) ⟨947405, by rfl⟩ : syracuseStep 1263207 = 1894811) B1894811
theorem B1263359 : Blo 1262449 1263359 := bstep (se 1 (by rfl) ⟨947519, by rfl⟩ : syracuseStep 1263359 = 1895039) B1895039
theorem B29165467 : Blo 1262449 29165467 := bstep (se 1 (by rfl) ⟨21874100, by rfl⟩ : syracuseStep 29165467 = 43748201) B43748201
theorem B12134879 : Blo 1262449 12134879 := bstep (se 1 (by rfl) ⟨9101159, by rfl⟩ : syracuseStep 12134879 = 18202319) B18202319
theorem B9587807 : Blo 1262449 9587807 := bstep (se 1 (by rfl) ⟨7190855, by rfl⟩ : syracuseStep 9587807 = 14381711) B14381711
theorem B19436759 : Blo 1262449 19436759 := bstep (se 1 (by rfl) ⟨14577569, by rfl⟩ : syracuseStep 19436759 = 29155139) B29155139
theorem B5396321 : Blo 1262449 5396321 := bstep (se 2 (by rfl) ⟨2023620, by rfl⟩ : syracuseStep 5396321 = 4047241) B4047241
theorem B8091535 : Blo 1262449 8091535 := bstep (se 1 (by rfl) ⟨6068651, by rfl⟩ : syracuseStep 8091535 = 12137303) B12137303
theorem B11532233 : Blo 1262449 11532233 := bstep (se 2 (by rfl) ⟨4324587, by rfl⟩ : syracuseStep 11532233 = 8649175) B8649175
theorem B72866465 : Blo 1262449 72866465 := bstep (se 2 (by rfl) ⟨27324924, by rfl⟩ : syracuseStep 72866465 = 54649849) B54649849
theorem B10788335 : Blo 1262449 10788335 := bstep (se 1 (by rfl) ⟨8091251, by rfl⟩ : syracuseStep 10788335 = 16182503) B16182503
theorem B6831839 : Blo 1262449 6831839 := bstep (se 1 (by rfl) ⟨5123879, by rfl⟩ : syracuseStep 6831839 = 10247759) B10247759
theorem B4996847 : Blo 1262449 4996847 := bstep (se 1 (by rfl) ⟨3747635, by rfl⟩ : syracuseStep 4996847 = 7495271) B7495271
theorem B3597547 : Blo 1262449 3597547 := bstep (se 1 (by rfl) ⟨2698160, by rfl⟩ : syracuseStep 3597547 = 5396321) B5396321
theorem B6391871 : Blo 1262449 6391871 := bstep (se 1 (by rfl) ⟨4793903, by rfl⟩ : syracuseStep 6391871 = 9587807) B9587807
theorem B10791751 : Blo 1262449 10791751 := bstep (se 1 (by rfl) ⟨8093813, by rfl⟩ : syracuseStep 10791751 = 16187627) B16187627
theorem B1420447 : Blo 1262449 1420447 := bstep (se 1 (by rfl) ⟨1065335, by rfl⟩ : syracuseStep 1420447 = 2130671) B2130671
theorem B7688155 : Blo 1262449 7688155 := bstep (se 1 (by rfl) ⟨5766116, by rfl⟩ : syracuseStep 7688155 = 11532233) B11532233
theorem B8089919 : Blo 1262449 8089919 := bstep (se 1 (by rfl) ⟨6067439, by rfl⟩ : syracuseStep 8089919 = 12134879) B12134879
theorem B13324925 : Blo 1262449 13324925 := bstep (se 3 (by rfl) ⟨2498423, by rfl⟩ : syracuseStep 13324925 = 4996847) B4996847
theorem B12146719 : Blo 1262449 12146719 := bstep (se 1 (by rfl) ⟨9110039, by rfl⟩ : syracuseStep 12146719 = 18220079) B18220079
theorem B12957839 : Blo 1262449 12957839 := bstep (se 1 (by rfl) ⟨9718379, by rfl⟩ : syracuseStep 12957839 = 19436759) B19436759
theorem B48577643 : Blo 1262449 48577643 := bstep (se 1 (by rfl) ⟨36433232, by rfl⟩ : syracuseStep 48577643 = 72866465) B72866465
theorem B7192223 : Blo 1262449 7192223 := bstep (se 1 (by rfl) ⟨5394167, by rfl⟩ : syracuseStep 7192223 = 10788335) B10788335
theorem B4554559 : Blo 1262449 4554559 := bstep (se 1 (by rfl) ⟨3415919, by rfl⟩ : syracuseStep 4554559 = 6831839) B6831839
theorem B10788713 : Blo 1262449 10788713 := bstep (se 2 (by rfl) ⟨4045767, by rfl⟩ : syracuseStep 10788713 = 8091535) B8091535
theorem B38887289 : Blo 1262449 38887289 := bstep (se 2 (by rfl) ⟨14582733, by rfl⟩ : syracuseStep 38887289 = 29165467) B29165467
theorem B16195625 : Blo 1262449 16195625 := bstep (se 2 (by rfl) ⟨6073359, by rfl⟩ : syracuseStep 16195625 = 12146719) B12146719
theorem B4261247 : Blo 1262449 4261247 := bstep (se 1 (by rfl) ⟨3195935, by rfl⟩ : syracuseStep 4261247 = 6391871) B6391871
theorem B1893929 : Blo 1262449 1893929 := bstep (se 2 (by rfl) ⟨710223, by rfl⟩ : syracuseStep 1893929 = 1420447) B1420447
theorem B32385095 : Blo 1262449 32385095 := bstep (se 1 (by rfl) ⟨24288821, by rfl⟩ : syracuseStep 32385095 = 48577643) B48577643
theorem B6072745 : Blo 1262449 6072745 := bstep (se 2 (by rfl) ⟨2277279, by rfl⟩ : syracuseStep 6072745 = 4554559) B4554559
theorem B4794815 : Blo 1262449 4794815 := bstep (se 1 (by rfl) ⟨3596111, by rfl⟩ : syracuseStep 4794815 = 7192223) B7192223
theorem B10250873 : Blo 1262449 10250873 := bstep (se 2 (by rfl) ⟨3844077, by rfl⟩ : syracuseStep 10250873 = 7688155) B7688155
theorem B5393279 : Blo 1262449 5393279 := bstep (se 1 (by rfl) ⟨4044959, by rfl⟩ : syracuseStep 5393279 = 8089919) B8089919
theorem B8883283 : Blo 1262449 8883283 := bstep (se 1 (by rfl) ⟨6662462, by rfl⟩ : syracuseStep 8883283 = 13324925) B13324925
theorem B14389001 : Blo 1262449 14389001 := bstep (se 2 (by rfl) ⟨5395875, by rfl⟩ : syracuseStep 14389001 = 10791751) B10791751
theorem B8638559 : Blo 1262449 8638559 := bstep (se 1 (by rfl) ⟨6478919, by rfl⟩ : syracuseStep 8638559 = 12957839) B12957839
theorem B4796729 : Blo 1262449 4796729 := bstep (se 2 (by rfl) ⟨1798773, by rfl⟩ : syracuseStep 4796729 = 3597547) B3597547
theorem B25924859 : Blo 1262449 25924859 := bstep (se 1 (by rfl) ⟨19443644, by rfl⟩ : syracuseStep 25924859 = 38887289) B38887289
theorem B7192475 : Blo 1262449 7192475 := bstep (se 1 (by rfl) ⟨5394356, by rfl⟩ : syracuseStep 7192475 = 10788713) B10788713
theorem B10797083 : Blo 1262449 10797083 := bstep (se 1 (by rfl) ⟨8097812, by rfl⟩ : syracuseStep 10797083 = 16195625) B16195625
theorem B5759039 : Blo 1262449 5759039 := bstep (se 1 (by rfl) ⟨4319279, by rfl⟩ : syracuseStep 5759039 = 8638559) B8638559
theorem B1262619 : Blo 1262449 1262619 := bstep (se 1 (by rfl) ⟨946964, by rfl⟩ : syracuseStep 1262619 = 1893929) B1893929
theorem B3196543 : Blo 1262449 3196543 := bstep (se 1 (by rfl) ⟨2397407, by rfl⟩ : syracuseStep 3196543 = 4794815) B4794815
theorem B6833915 : Blo 1262449 6833915 := bstep (se 1 (by rfl) ⟨5125436, by rfl⟩ : syracuseStep 6833915 = 10250873) B10250873
theorem B4794983 : Blo 1262449 4794983 := bstep (se 1 (by rfl) ⟨3596237, by rfl⟩ : syracuseStep 4794983 = 7192475) B7192475
theorem B3197819 : Blo 1262449 3197819 := bstep (se 1 (by rfl) ⟨2398364, by rfl⟩ : syracuseStep 3197819 = 4796729) B4796729
theorem B8096993 : Blo 1262449 8096993 := bstep (se 2 (by rfl) ⟨3036372, by rfl⟩ : syracuseStep 8096993 = 6072745) B6072745
theorem B21590063 : Blo 1262449 21590063 := bstep (se 1 (by rfl) ⟨16192547, by rfl⟩ : syracuseStep 21590063 = 32385095) B32385095
theorem B17283239 : Blo 1262449 17283239 := bstep (se 1 (by rfl) ⟨12962429, by rfl⟩ : syracuseStep 17283239 = 25924859) B25924859
theorem B2840831 : Blo 1262449 2840831 := bstep (se 1 (by rfl) ⟨2130623, by rfl⟩ : syracuseStep 2840831 = 4261247) B4261247
theorem B11844377 : Blo 1262449 11844377 := bstep (se 2 (by rfl) ⟨4441641, by rfl⟩ : syracuseStep 11844377 = 8883283) B8883283
theorem B3595519 : Blo 1262449 3595519 := bstep (se 1 (by rfl) ⟨2696639, by rfl⟩ : syracuseStep 3595519 = 5393279) B5393279
theorem B9592667 : Blo 1262449 9592667 := bstep (se 1 (by rfl) ⟨7194500, by rfl⟩ : syracuseStep 9592667 = 14389001) B14389001
theorem B14393375 : Blo 1262449 14393375 := bstep (se 1 (by rfl) ⟨10795031, by rfl⟩ : syracuseStep 14393375 = 21590063) B21590063
theorem B4555943 : Blo 1262449 4555943 := bstep (se 1 (by rfl) ⟨3416957, by rfl⟩ : syracuseStep 4555943 = 6833915) B6833915
theorem B1893887 : Blo 1262449 1893887 := bstep (se 1 (by rfl) ⟨1420415, by rfl⟩ : syracuseStep 1893887 = 2840831) B2840831
theorem B4794025 : Blo 1262449 4794025 := bstep (se 2 (by rfl) ⟨1797759, by rfl⟩ : syracuseStep 4794025 = 3595519) B3595519
theorem B3196655 : Blo 1262449 3196655 := bstep (se 1 (by rfl) ⟨2397491, by rfl⟩ : syracuseStep 3196655 = 4794983) B4794983
theorem B2131879 : Blo 1262449 2131879 := bstep (se 1 (by rfl) ⟨1598909, by rfl⟩ : syracuseStep 2131879 = 3197819) B3197819
theorem B4262057 : Blo 1262449 4262057 := bstep (se 2 (by rfl) ⟨1598271, by rfl⟩ : syracuseStep 4262057 = 3196543) B3196543
theorem B11522159 : Blo 1262449 11522159 := bstep (se 1 (by rfl) ⟨8641619, by rfl⟩ : syracuseStep 11522159 = 17283239) B17283239
theorem B6395111 : Blo 1262449 6395111 := bstep (se 1 (by rfl) ⟨4796333, by rfl⟩ : syracuseStep 6395111 = 9592667) B9592667
theorem B7198055 : Blo 1262449 7198055 := bstep (se 1 (by rfl) ⟨5398541, by rfl⟩ : syracuseStep 7198055 = 10797083) B10797083
theorem B3839359 : Blo 1262449 3839359 := bstep (se 1 (by rfl) ⟨2879519, by rfl⟩ : syracuseStep 3839359 = 5759039) B5759039
theorem B7896251 : Blo 1262449 7896251 := bstep (se 1 (by rfl) ⟨5922188, by rfl⟩ : syracuseStep 7896251 = 11844377) B11844377
theorem B5397995 : Blo 1262449 5397995 := bstep (se 1 (by rfl) ⟨4048496, by rfl⟩ : syracuseStep 5397995 = 8096993) B8096993
theorem B1262591 : Blo 1262449 1262591 := bstep (se 1 (by rfl) ⟨946943, by rfl⟩ : syracuseStep 1262591 = 1893887) B1893887
theorem B2131103 : Blo 1262449 2131103 := bstep (se 1 (by rfl) ⟨1598327, by rfl⟩ : syracuseStep 2131103 = 3196655) B3196655
theorem B6392033 : Blo 1262449 6392033 := bstep (se 2 (by rfl) ⟨2397012, by rfl⟩ : syracuseStep 6392033 = 4794025) B4794025
theorem B3598663 : Blo 1262449 3598663 := bstep (se 1 (by rfl) ⟨2698997, by rfl⟩ : syracuseStep 3598663 = 5397995) B5397995
theorem B9595583 : Blo 1262449 9595583 := bstep (se 1 (by rfl) ⟨7196687, by rfl⟩ : syracuseStep 9595583 = 14393375) B14393375
theorem B21056669 : Blo 1262449 21056669 := bstep (se 3 (by rfl) ⟨3948125, by rfl⟩ : syracuseStep 21056669 = 7896251) B7896251
theorem B4263407 : Blo 1262449 4263407 := bstep (se 1 (by rfl) ⟨3197555, by rfl⟩ : syracuseStep 4263407 = 6395111) B6395111
theorem B7681439 : Blo 1262449 7681439 := bstep (se 1 (by rfl) ⟨5761079, by rfl⟩ : syracuseStep 7681439 = 11522159) B11522159
theorem B3037295 : Blo 1262449 3037295 := bstep (se 1 (by rfl) ⟨2277971, by rfl⟩ : syracuseStep 3037295 = 4555943) B4555943
theorem B4798703 : Blo 1262449 4798703 := bstep (se 1 (by rfl) ⟨3599027, by rfl⟩ : syracuseStep 4798703 = 7198055) B7198055
theorem B2841371 : Blo 1262449 2841371 := bstep (se 1 (by rfl) ⟨2131028, by rfl⟩ : syracuseStep 2841371 = 4262057) B4262057
theorem B5119145 : Blo 1262449 5119145 := bstep (se 2 (by rfl) ⟨1919679, by rfl⟩ : syracuseStep 5119145 = 3839359) B3839359
theorem B2842505 : Blo 1262449 2842505 := bstep (se 2 (by rfl) ⟨1065939, by rfl⟩ : syracuseStep 2842505 = 2131879) B2131879
theorem B4261355 : Blo 1262449 4261355 := bstep (se 1 (by rfl) ⟨3196016, by rfl⟩ : syracuseStep 4261355 = 6392033) B6392033
theorem B1894247 : Blo 1262449 1894247 := bstep (se 1 (by rfl) ⟨1420685, by rfl⟩ : syracuseStep 1894247 = 2841371) B2841371
theorem B1895003 : Blo 1262449 1895003 := bstep (se 1 (by rfl) ⟨1421252, by rfl⟩ : syracuseStep 1895003 = 2842505) B2842505
theorem B1420735 : Blo 1262449 1420735 := bstep (se 1 (by rfl) ⟨1065551, by rfl⟩ : syracuseStep 1420735 = 2131103) B2131103
theorem B20483837 : Blo 1262449 20483837 := bstep (se 3 (by rfl) ⟨3840719, by rfl⟩ : syracuseStep 20483837 = 7681439) B7681439
theorem B3199135 : Blo 1262449 3199135 := bstep (se 1 (by rfl) ⟨2399351, by rfl⟩ : syracuseStep 3199135 = 4798703) B4798703
theorem B14037779 : Blo 1262449 14037779 := bstep (se 1 (by rfl) ⟨10528334, by rfl⟩ : syracuseStep 14037779 = 21056669) B21056669
theorem B3412763 : Blo 1262449 3412763 := bstep (se 1 (by rfl) ⟨2559572, by rfl⟩ : syracuseStep 3412763 = 5119145) B5119145
theorem B8099453 : Blo 1262449 8099453 := bstep (se 3 (by rfl) ⟨1518647, by rfl⟩ : syracuseStep 8099453 = 3037295) B3037295
theorem B4798217 : Blo 1262449 4798217 := bstep (se 2 (by rfl) ⟨1799331, by rfl⟩ : syracuseStep 4798217 = 3598663) B3598663
theorem B6397055 : Blo 1262449 6397055 := bstep (se 1 (by rfl) ⟨4797791, by rfl⟩ : syracuseStep 6397055 = 9595583) B9595583
theorem B2842271 : Blo 1262449 2842271 := bstep (se 1 (by rfl) ⟨2131703, by rfl⟩ : syracuseStep 2842271 = 4263407) B4263407
theorem B5399635 : Blo 1262449 5399635 := bstep (se 1 (by rfl) ⟨4049726, by rfl⟩ : syracuseStep 5399635 = 8099453) B8099453
theorem B1262831 : Blo 1262449 1262831 := bstep (se 1 (by rfl) ⟨947123, by rfl⟩ : syracuseStep 1262831 = 1894247) B1894247
theorem B1263335 : Blo 1262449 1263335 := bstep (se 1 (by rfl) ⟨947501, by rfl⟩ : syracuseStep 1263335 = 1895003) B1895003
theorem B1894313 : Blo 1262449 1894313 := bstep (se 2 (by rfl) ⟨710367, by rfl⟩ : syracuseStep 1894313 = 1420735) B1420735
theorem B1894847 : Blo 1262449 1894847 := bstep (se 1 (by rfl) ⟨1421135, by rfl⟩ : syracuseStep 1894847 = 2842271) B2842271
theorem B9358519 : Blo 1262449 9358519 := bstep (se 1 (by rfl) ⟨7018889, by rfl⟩ : syracuseStep 9358519 = 14037779) B14037779
theorem B3198811 : Blo 1262449 3198811 := bstep (se 1 (by rfl) ⟨2399108, by rfl⟩ : syracuseStep 3198811 = 4798217) B4798217
theorem B4264703 : Blo 1262449 4264703 := bstep (se 1 (by rfl) ⟨3198527, by rfl⟩ : syracuseStep 4264703 = 6397055) B6397055
theorem B4265513 : Blo 1262449 4265513 := bstep (se 2 (by rfl) ⟨1599567, by rfl⟩ : syracuseStep 4265513 = 3199135) B3199135
theorem B2275175 : Blo 1262449 2275175 := bstep (se 1 (by rfl) ⟨1706381, by rfl⟩ : syracuseStep 2275175 = 3412763) B3412763
theorem B2840903 : Blo 1262449 2840903 := bstep (se 1 (by rfl) ⟨2130677, by rfl⟩ : syracuseStep 2840903 = 4261355) B4261355
theorem B13655891 : Blo 1262449 13655891 := bstep (se 1 (by rfl) ⟨10241918, by rfl⟩ : syracuseStep 13655891 = 20483837) B20483837
theorem B2843135 : Blo 1262449 2843135 := bstep (se 1 (by rfl) ⟨2132351, by rfl⟩ : syracuseStep 2843135 = 4264703) B4264703
theorem B2843675 : Blo 1262449 2843675 := bstep (se 1 (by rfl) ⟨2132756, by rfl⟩ : syracuseStep 2843675 = 4265513) B4265513
theorem B1262875 : Blo 1262449 1262875 := bstep (se 1 (by rfl) ⟨947156, by rfl⟩ : syracuseStep 1262875 = 1894313) B1894313
theorem B1893935 : Blo 1262449 1893935 := bstep (se 1 (by rfl) ⟨1420451, by rfl⟩ : syracuseStep 1893935 = 2840903) B2840903
theorem B12478025 : Blo 1262449 12478025 := bstep (se 2 (by rfl) ⟨4679259, by rfl⟩ : syracuseStep 12478025 = 9358519) B9358519
theorem B1263231 : Blo 1262449 1263231 := bstep (se 1 (by rfl) ⟨947423, by rfl⟩ : syracuseStep 1263231 = 1894847) B1894847
theorem B9103927 : Blo 1262449 9103927 := bstep (se 1 (by rfl) ⟨6827945, by rfl⟩ : syracuseStep 9103927 = 13655891) B13655891
theorem B6067133 : Blo 1262449 6067133 := bstep (se 3 (by rfl) ⟨1137587, by rfl⟩ : syracuseStep 6067133 = 2275175) B2275175
theorem B4265081 : Blo 1262449 4265081 := bstep (se 2 (by rfl) ⟨1599405, by rfl⟩ : syracuseStep 4265081 = 3198811) B3198811
theorem B7199513 : Blo 1262449 7199513 := bstep (se 2 (by rfl) ⟨2699817, by rfl⟩ : syracuseStep 7199513 = 5399635) B5399635
theorem B2843387 : Blo 1262449 2843387 := bstep (se 1 (by rfl) ⟨2132540, by rfl⟩ : syracuseStep 2843387 = 4265081) B4265081
theorem B1262623 : Blo 1262449 1262623 := bstep (se 1 (by rfl) ⟨946967, by rfl⟩ : syracuseStep 1262623 = 1893935) B1893935
theorem B1895423 : Blo 1262449 1895423 := bstep (se 1 (by rfl) ⟨1421567, by rfl⟩ : syracuseStep 1895423 = 2843135) B2843135
theorem B1895783 : Blo 1262449 1895783 := bstep (se 1 (by rfl) ⟨1421837, by rfl⟩ : syracuseStep 1895783 = 2843675) B2843675
theorem B8318683 : Blo 1262449 8318683 := bstep (se 1 (by rfl) ⟨6239012, by rfl⟩ : syracuseStep 8318683 = 12478025) B12478025
theorem B4044755 : Blo 1262449 4044755 := bstep (se 1 (by rfl) ⟨3033566, by rfl⟩ : syracuseStep 4044755 = 6067133) B6067133
theorem B12138569 : Blo 1262449 12138569 := bstep (se 2 (by rfl) ⟨4551963, by rfl⟩ : syracuseStep 12138569 = 9103927) B9103927
theorem B4799675 : Blo 1262449 4799675 := bstep (se 1 (by rfl) ⟨3599756, by rfl⟩ : syracuseStep 4799675 = 7199513) B7199513
theorem B2696503 : Blo 1262449 2696503 := bstep (se 1 (by rfl) ⟨2022377, by rfl⟩ : syracuseStep 2696503 = 4044755) B4044755
theorem B1263615 : Blo 1262449 1263615 := bstep (se 1 (by rfl) ⟨947711, by rfl⟩ : syracuseStep 1263615 = 1895423) B1895423
theorem B1263855 : Blo 1262449 1263855 := bstep (se 1 (by rfl) ⟨947891, by rfl⟩ : syracuseStep 1263855 = 1895783) B1895783
theorem B1895591 : Blo 1262449 1895591 := bstep (se 1 (by rfl) ⟨1421693, by rfl⟩ : syracuseStep 1895591 = 2843387) B2843387
theorem B3199783 : Blo 1262449 3199783 := bstep (se 1 (by rfl) ⟨2399837, by rfl⟩ : syracuseStep 3199783 = 4799675) B4799675
theorem B8092379 : Blo 1262449 8092379 := bstep (se 1 (by rfl) ⟨6069284, by rfl⟩ : syracuseStep 8092379 = 12138569) B12138569
theorem B11091577 : Blo 1262449 11091577 := bstep (se 2 (by rfl) ⟨4159341, by rfl⟩ : syracuseStep 11091577 = 8318683) B8318683
theorem B1263727 : Blo 1262449 1263727 := bstep (se 1 (by rfl) ⟨947795, by rfl⟩ : syracuseStep 1263727 = 1895591) B1895591
theorem B14788769 : Blo 1262449 14788769 := bstep (se 2 (by rfl) ⟨5545788, by rfl⟩ : syracuseStep 14788769 = 11091577) B11091577
theorem B5394919 : Blo 1262449 5394919 := bstep (se 1 (by rfl) ⟨4046189, by rfl⟩ : syracuseStep 5394919 = 8092379) B8092379
theorem B4266377 : Blo 1262449 4266377 := bstep (se 2 (by rfl) ⟨1599891, by rfl⟩ : syracuseStep 4266377 = 3199783) B3199783
theorem B3595337 : Blo 1262449 3595337 := bstep (se 2 (by rfl) ⟨1348251, by rfl⟩ : syracuseStep 3595337 = 2696503) B2696503
theorem B39436717 : Blo 1262449 39436717 := bstep (se 3 (by rfl) ⟨7394384, by rfl⟩ : syracuseStep 39436717 = 14788769) B14788769
theorem B7193225 : Blo 1262449 7193225 := bstep (se 2 (by rfl) ⟨2697459, by rfl⟩ : syracuseStep 7193225 = 5394919) B5394919
theorem B2844251 : Blo 1262449 2844251 := bstep (se 1 (by rfl) ⟨2133188, by rfl⟩ : syracuseStep 2844251 = 4266377) B4266377
theorem B2396891 : Blo 1262449 2396891 := bstep (se 1 (by rfl) ⟨1797668, by rfl⟩ : syracuseStep 2396891 = 3595337) B3595337
theorem B6391709 : Blo 1262449 6391709 := bstep (se 3 (by rfl) ⟨1198445, by rfl⟩ : syracuseStep 6391709 = 2396891) B2396891
theorem B4795483 : Blo 1262449 4795483 := bstep (se 1 (by rfl) ⟨3596612, by rfl⟩ : syracuseStep 4795483 = 7193225) B7193225
theorem B1896167 : Blo 1262449 1896167 := bstep (se 1 (by rfl) ⟨1422125, by rfl⟩ : syracuseStep 1896167 = 2844251) B2844251
theorem B52582289 : Blo 1262449 52582289 := bstep (se 2 (by rfl) ⟨19718358, by rfl⟩ : syracuseStep 52582289 = 39436717) B39436717
theorem B4261139 : Blo 1262449 4261139 := bstep (se 1 (by rfl) ⟨3195854, by rfl⟩ : syracuseStep 4261139 = 6391709) B6391709
theorem B1264111 : Blo 1262449 1264111 := bstep (se 1 (by rfl) ⟨948083, by rfl⟩ : syracuseStep 1264111 = 1896167) B1896167
theorem B6393977 : Blo 1262449 6393977 := bstep (se 2 (by rfl) ⟨2397741, by rfl⟩ : syracuseStep 6393977 = 4795483) B4795483
theorem B140219437 : Blo 1262449 140219437 := bstep (se 3 (by rfl) ⟨26291144, by rfl⟩ : syracuseStep 140219437 = 52582289) B52582289
theorem B186959249 : Blo 1262449 186959249 := bstep (se 2 (by rfl) ⟨70109718, by rfl⟩ : syracuseStep 186959249 = 140219437) B140219437
theorem B4262651 : Blo 1262449 4262651 := bstep (se 1 (by rfl) ⟨3196988, by rfl⟩ : syracuseStep 4262651 = 6393977) B6393977
theorem B2840759 : Blo 1262449 2840759 := bstep (se 1 (by rfl) ⟨2130569, by rfl⟩ : syracuseStep 2840759 = 4261139) B4261139
theorem B1893839 : Blo 1262449 1893839 := bstep (se 1 (by rfl) ⟨1420379, by rfl⟩ : syracuseStep 1893839 = 2840759) B2840759
theorem B124639499 : Blo 1262449 124639499 := bstep (se 1 (by rfl) ⟨93479624, by rfl⟩ : syracuseStep 124639499 = 186959249) B186959249
theorem B2841767 : Blo 1262449 2841767 := bstep (se 1 (by rfl) ⟨2131325, by rfl⟩ : syracuseStep 2841767 = 4262651) B4262651
theorem B1262559 : Blo 1262449 1262559 := bstep (se 1 (by rfl) ⟨946919, by rfl⟩ : syracuseStep 1262559 = 1893839) B1893839
theorem B83092999 : Blo 1262449 83092999 := bstep (se 1 (by rfl) ⟨62319749, by rfl⟩ : syracuseStep 83092999 = 124639499) B124639499
theorem B1894511 : Blo 1262449 1894511 := bstep (se 1 (by rfl) ⟨1420883, by rfl⟩ : syracuseStep 1894511 = 2841767) B2841767
theorem B1263007 : Blo 1262449 1263007 := bstep (se 1 (by rfl) ⟨947255, by rfl⟩ : syracuseStep 1263007 = 1894511) B1894511
theorem B110790665 : Blo 1262449 110790665 := bstep (se 2 (by rfl) ⟨41546499, by rfl⟩ : syracuseStep 110790665 = 83092999) B83092999
theorem B73860443 : Blo 1262449 73860443 := bstep (se 1 (by rfl) ⟨55395332, by rfl⟩ : syracuseStep 73860443 = 110790665) B110790665
theorem B49240295 : Blo 1262449 49240295 := bstep (se 1 (by rfl) ⟨36930221, by rfl⟩ : syracuseStep 49240295 = 73860443) B73860443
theorem B32826863 : Blo 1262449 32826863 := bstep (se 1 (by rfl) ⟨24620147, by rfl⟩ : syracuseStep 32826863 = 49240295) B49240295
theorem B21884575 : Blo 1262449 21884575 := bstep (se 1 (by rfl) ⟨16413431, by rfl⟩ : syracuseStep 21884575 = 32826863) B32826863
theorem B29179433 : Blo 1262449 29179433 := bstep (se 2 (by rfl) ⟨10942287, by rfl⟩ : syracuseStep 29179433 = 21884575) B21884575
theorem B19452955 : Blo 1262449 19452955 := bstep (se 1 (by rfl) ⟨14589716, by rfl⟩ : syracuseStep 19452955 = 29179433) B29179433
theorem B25937273 : Blo 1262449 25937273 := bstep (se 2 (by rfl) ⟨9726477, by rfl⟩ : syracuseStep 25937273 = 19452955) B19452955
theorem B69166061 : Blo 1262449 69166061 := bstep (se 3 (by rfl) ⟨12968636, by rfl⟩ : syracuseStep 69166061 = 25937273) B25937273
theorem B46110707 : Blo 1262449 46110707 := bstep (se 1 (by rfl) ⟨34583030, by rfl⟩ : syracuseStep 46110707 = 69166061) B69166061
theorem B30740471 : Blo 1262449 30740471 := bstep (se 1 (by rfl) ⟨23055353, by rfl⟩ : syracuseStep 30740471 = 46110707) B46110707
theorem B20493647 : Blo 1262449 20493647 := bstep (se 1 (by rfl) ⟨15370235, by rfl⟩ : syracuseStep 20493647 = 30740471) B30740471
theorem B13662431 : Blo 1262449 13662431 := bstep (se 1 (by rfl) ⟨10246823, by rfl⟩ : syracuseStep 13662431 = 20493647) B20493647
theorem B9108287 : Blo 1262449 9108287 := bstep (se 1 (by rfl) ⟨6831215, by rfl⟩ : syracuseStep 9108287 = 13662431) B13662431
theorem B6072191 : Blo 1262449 6072191 := bstep (se 1 (by rfl) ⟨4554143, by rfl⟩ : syracuseStep 6072191 = 9108287) B9108287
theorem B4048127 : Blo 1262449 4048127 := bstep (se 1 (by rfl) ⟨3036095, by rfl⟩ : syracuseStep 4048127 = 6072191) B6072191
theorem B2698751 : Blo 1262449 2698751 := bstep (se 1 (by rfl) ⟨2024063, by rfl⟩ : syracuseStep 2698751 = 4048127) B4048127
theorem B1799167 : Blo 1262449 1799167 := bstep (se 1 (by rfl) ⟨1349375, by rfl⟩ : syracuseStep 1799167 = 2698751) B2698751
theorem B2398889 : Blo 1262449 2398889 := bstep (se 2 (by rfl) ⟨899583, by rfl⟩ : syracuseStep 2398889 = 1799167) B1799167
theorem B1599259 : Blo 1262449 1599259 := bstep (se 1 (by rfl) ⟨1199444, by rfl⟩ : syracuseStep 1599259 = 2398889) B2398889
theorem B2132345 : Blo 1262449 2132345 := bstep (se 2 (by rfl) ⟨799629, by rfl⟩ : syracuseStep 2132345 = 1599259) B1599259
theorem B1421563 : Blo 1262449 1421563 := bstep (se 1 (by rfl) ⟨1066172, by rfl⟩ : syracuseStep 1421563 = 2132345) B2132345
theorem B1895417 : Blo 1262449 1895417 := bstep (se 2 (by rfl) ⟨710781, by rfl⟩ : syracuseStep 1895417 = 1421563) B1421563
theorem B1263611 : Blo 1262449 1263611 := bstep (se 1 (by rfl) ⟨947708, by rfl⟩ : syracuseStep 1263611 = 1895417) B1895417

theorem C0 (j : ℕ) (h1 : 315612 ≤ j) (h2 : j ≤ 316111) : Blo 1262449 (4 * j + 3) := by
  interval_cases j
  · exact B1262451
  · exact B1262455
  · exact B1262459
  · exact B1262463
  · exact B1262467
  · exact B1262471
  · exact B1262475
  · exact B1262479
  · exact B1262483
  · exact B1262487
  · exact B1262491
  · exact B1262495
  · exact B1262499
  · exact B1262503
  · exact B1262507
  · exact B1262511
  · exact B1262515
  · exact B1262519
  · exact B1262523
  · exact B1262527
  · exact B1262531
  · exact B1262535
  · exact B1262539
  · exact B1262543
  · exact B1262547
  · exact B1262551
  · exact B1262555
  · exact B1262559
  · exact B1262563
  · exact B1262567
  · exact B1262571
  · exact B1262575
  · exact B1262579
  · exact B1262583
  · exact B1262587
  · exact B1262591
  · exact B1262595
  · exact B1262599
  · exact B1262603
  · exact B1262607
  · exact B1262611
  · exact B1262615
  · exact B1262619
  · exact B1262623
  · exact B1262627
  · exact B1262631
  · exact B1262635
  · exact B1262639
  · exact B1262643
  · exact B1262647
  · exact B1262651
  · exact B1262655
  · exact B1262659
  · exact B1262663
  · exact B1262667
  · exact B1262671
  · exact B1262675
  · exact B1262679
  · exact B1262683
  · exact B1262687
  · exact B1262691
  · exact B1262695
  · exact B1262699
  · exact B1262703
  · exact B1262707
  · exact B1262711
  · exact B1262715
  · exact B1262719
  · exact B1262723
  · exact B1262727
  · exact B1262731
  · exact B1262735
  · exact B1262739
  · exact B1262743
  · exact B1262747
  · exact B1262751
  · exact B1262755
  · exact B1262759
  · exact B1262763
  · exact B1262767
  · exact B1262771
  · exact B1262775
  · exact B1262779
  · exact B1262783
  · exact B1262787
  · exact B1262791
  · exact B1262795
  · exact B1262799
  · exact B1262803
  · exact B1262807
  · exact B1262811
  · exact B1262815
  · exact B1262819
  · exact B1262823
  · exact B1262827
  · exact B1262831
  · exact B1262835
  · exact B1262839
  · exact B1262843
  · exact B1262847
  · exact B1262851
  · exact B1262855
  · exact B1262859
  · exact B1262863
  · exact B1262867
  · exact B1262871
  · exact B1262875
  · exact B1262879
  · exact B1262883
  · exact B1262887
  · exact B1262891
  · exact B1262895
  · exact B1262899
  · exact B1262903
  · exact B1262907
  · exact B1262911
  · exact B1262915
  · exact B1262919
  · exact B1262923
  · exact B1262927
  · exact B1262931
  · exact B1262935
  · exact B1262939
  · exact B1262943
  · exact B1262947
  · exact B1262951
  · exact B1262955
  · exact B1262959
  · exact B1262963
  · exact B1262967
  · exact B1262971
  · exact B1262975
  · exact B1262979
  · exact B1262983
  · exact B1262987
  · exact B1262991
  · exact B1262995
  · exact B1262999
  · exact B1263003
  · exact B1263007
  · exact B1263011
  · exact B1263015
  · exact B1263019
  · exact B1263023
  · exact B1263027
  · exact B1263031
  · exact B1263035
  · exact B1263039
  · exact B1263043
  · exact B1263047
  · exact B1263051
  · exact B1263055
  · exact B1263059
  · exact B1263063
  · exact B1263067
  · exact B1263071
  · exact B1263075
  · exact B1263079
  · exact B1263083
  · exact B1263087
  · exact B1263091
  · exact B1263095
  · exact B1263099
  · exact B1263103
  · exact B1263107
  · exact B1263111
  · exact B1263115
  · exact B1263119
  · exact B1263123
  · exact B1263127
  · exact B1263131
  · exact B1263135
  · exact B1263139
  · exact B1263143
  · exact B1263147
  · exact B1263151
  · exact B1263155
  · exact B1263159
  · exact B1263163
  · exact B1263167
  · exact B1263171
  · exact B1263175
  · exact B1263179
  · exact B1263183
  · exact B1263187
  · exact B1263191
  · exact B1263195
  · exact B1263199
  · exact B1263203
  · exact B1263207
  · exact B1263211
  · exact B1263215
  · exact B1263219
  · exact B1263223
  · exact B1263227
  · exact B1263231
  · exact B1263235
  · exact B1263239
  · exact B1263243
  · exact B1263247
  · exact B1263251
  · exact B1263255
  · exact B1263259
  · exact B1263263
  · exact B1263267
  · exact B1263271
  · exact B1263275
  · exact B1263279
  · exact B1263283
  · exact B1263287
  · exact B1263291
  · exact B1263295
  · exact B1263299
  · exact B1263303
  · exact B1263307
  · exact B1263311
  · exact B1263315
  · exact B1263319
  · exact B1263323
  · exact B1263327
  · exact B1263331
  · exact B1263335
  · exact B1263339
  · exact B1263343
  · exact B1263347
  · exact B1263351
  · exact B1263355
  · exact B1263359
  · exact B1263363
  · exact B1263367
  · exact B1263371
  · exact B1263375
  · exact B1263379
  · exact B1263383
  · exact B1263387
  · exact B1263391
  · exact B1263395
  · exact B1263399
  · exact B1263403
  · exact B1263407
  · exact B1263411
  · exact B1263415
  · exact B1263419
  · exact B1263423
  · exact B1263427
  · exact B1263431
  · exact B1263435
  · exact B1263439
  · exact B1263443
  · exact B1263447
  · exact B1263451
  · exact B1263455
  · exact B1263459
  · exact B1263463
  · exact B1263467
  · exact B1263471
  · exact B1263475
  · exact B1263479
  · exact B1263483
  · exact B1263487
  · exact B1263491
  · exact B1263495
  · exact B1263499
  · exact B1263503
  · exact B1263507
  · exact B1263511
  · exact B1263515
  · exact B1263519
  · exact B1263523
  · exact B1263527
  · exact B1263531
  · exact B1263535
  · exact B1263539
  · exact B1263543
  · exact B1263547
  · exact B1263551
  · exact B1263555
  · exact B1263559
  · exact B1263563
  · exact B1263567
  · exact B1263571
  · exact B1263575
  · exact B1263579
  · exact B1263583
  · exact B1263587
  · exact B1263591
  · exact B1263595
  · exact B1263599
  · exact B1263603
  · exact B1263607
  · exact B1263611
  · exact B1263615
  · exact B1263619
  · exact B1263623
  · exact B1263627
  · exact B1263631
  · exact B1263635
  · exact B1263639
  · exact B1263643
  · exact B1263647
  · exact B1263651
  · exact B1263655
  · exact B1263659
  · exact B1263663
  · exact B1263667
  · exact B1263671
  · exact B1263675
  · exact B1263679
  · exact B1263683
  · exact B1263687
  · exact B1263691
  · exact B1263695
  · exact B1263699
  · exact B1263703
  · exact B1263707
  · exact B1263711
  · exact B1263715
  · exact B1263719
  · exact B1263723
  · exact B1263727
  · exact B1263731
  · exact B1263735
  · exact B1263739
  · exact B1263743
  · exact B1263747
  · exact B1263751
  · exact B1263755
  · exact B1263759
  · exact B1263763
  · exact B1263767
  · exact B1263771
  · exact B1263775
  · exact B1263779
  · exact B1263783
  · exact B1263787
  · exact B1263791
  · exact B1263795
  · exact B1263799
  · exact B1263803
  · exact B1263807
  · exact B1263811
  · exact B1263815
  · exact B1263819
  · exact B1263823
  · exact B1263827
  · exact B1263831
  · exact B1263835
  · exact B1263839
  · exact B1263843
  · exact B1263847
  · exact B1263851
  · exact B1263855
  · exact B1263859
  · exact B1263863
  · exact B1263867
  · exact B1263871
  · exact B1263875
  · exact B1263879
  · exact B1263883
  · exact B1263887
  · exact B1263891
  · exact B1263895
  · exact B1263899
  · exact B1263903
  · exact B1263907
  · exact B1263911
  · exact B1263915
  · exact B1263919
  · exact B1263923
  · exact B1263927
  · exact B1263931
  · exact B1263935
  · exact B1263939
  · exact B1263943
  · exact B1263947
  · exact B1263951
  · exact B1263955
  · exact B1263959
  · exact B1263963
  · exact B1263967
  · exact B1263971
  · exact B1263975
  · exact B1263979
  · exact B1263983
  · exact B1263987
  · exact B1263991
  · exact B1263995
  · exact B1263999
  · exact B1264003
  · exact B1264007
  · exact B1264011
  · exact B1264015
  · exact B1264019
  · exact B1264023
  · exact B1264027
  · exact B1264031
  · exact B1264035
  · exact B1264039
  · exact B1264043
  · exact B1264047
  · exact B1264051
  · exact B1264055
  · exact B1264059
  · exact B1264063
  · exact B1264067
  · exact B1264071
  · exact B1264075
  · exact B1264079
  · exact B1264083
  · exact B1264087
  · exact B1264091
  · exact B1264095
  · exact B1264099
  · exact B1264103
  · exact B1264107
  · exact B1264111
  · exact B1264115
  · exact B1264119
  · exact B1264123
  · exact B1264127
  · exact B1264131
  · exact B1264135
  · exact B1264139
  · exact B1264143
  · exact B1264147
  · exact B1264151
  · exact B1264155
  · exact B1264159
  · exact B1264163
  · exact B1264167
  · exact B1264171
  · exact B1264175
  · exact B1264179
  · exact B1264183
  · exact B1264187
  · exact B1264191
  · exact B1264195
  · exact B1264199
  · exact B1264203
  · exact B1264207
  · exact B1264211
  · exact B1264215
  · exact B1264219
  · exact B1264223
  · exact B1264227
  · exact B1264231
  · exact B1264235
  · exact B1264239
  · exact B1264243
  · exact B1264247
  · exact B1264251
  · exact B1264255
  · exact B1264259
  · exact B1264263
  · exact B1264267
  · exact B1264271
  · exact B1264275
  · exact B1264279
  · exact B1264283
  · exact B1264287
  · exact B1264291
  · exact B1264295
  · exact B1264299
  · exact B1264303
  · exact B1264307
  · exact B1264311
  · exact B1264315
  · exact B1264319
  · exact B1264323
  · exact B1264327
  · exact B1264331
  · exact B1264335
  · exact B1264339
  · exact B1264343
  · exact B1264347
  · exact B1264351
  · exact B1264355
  · exact B1264359
  · exact B1264363
  · exact B1264367
  · exact B1264371
  · exact B1264375
  · exact B1264379
  · exact B1264383
  · exact B1264387
  · exact B1264391
  · exact B1264395
  · exact B1264399
  · exact B1264403
  · exact B1264407
  · exact B1264411
  · exact B1264415
  · exact B1264419
  · exact B1264423
  · exact B1264427
  · exact B1264431
  · exact B1264435
  · exact B1264439
  · exact B1264443
  · exact B1264447

theorem solution (m : ℕ) (hlo : 1262449 ≤ m) (hhi : m ≤ 1264449) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 315612 ≤ j := by omega
    have hj2 : j ≤ 316111 := by omega
    have hb : Blo 1262449 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
