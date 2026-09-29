-- Prove2me | solution 1 for syracuse_descends_range_603293_607293
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T19:04:29.437102+00:00
-- url     : https://prove2.me/submissions/097ae2a4-877f-42b4-af9a-8aa72f49bc8d

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


theorem B2293829 : Blo 603293 2293829 := bbase (se 4 (by rfl) ⟨215046, by rfl⟩ : syracuseStep 2293829 = 430093) (by norm_num)
theorem B1310813 : Blo 603293 1310813 := bbase (se 3 (by rfl) ⟨245777, by rfl⟩ : syracuseStep 1310813 = 491555) (by norm_num)
theorem B1933445 : Blo 603293 1933445 := bbase (se 4 (by rfl) ⟨181260, by rfl⟩ : syracuseStep 1933445 = 362521) (by norm_num)
theorem B622733 : Blo 603293 622733 := bbase (se 3 (by rfl) ⟨116762, by rfl⟩ : syracuseStep 622733 = 233525) (by norm_num)
theorem B3440789 : Blo 603293 3440789 := bbase (se 6 (by rfl) ⟨80643, by rfl⟩ : syracuseStep 3440789 = 161287) (by norm_num)
theorem B2916661 : Blo 603293 2916661 := bbase (se 5 (by rfl) ⟨136718, by rfl⟩ : syracuseStep 2916661 = 273437) (by norm_num)
theorem B3277205 : Blo 603293 3277205 := bbase (se 6 (by rfl) ⟨76809, by rfl⟩ : syracuseStep 3277205 = 153619) (by norm_num)
theorem B5833397 : Blo 603293 5833397 := bbase (se 5 (by rfl) ⟨273440, by rfl⟩ : syracuseStep 5833397 = 546881) (by norm_num)
theorem B1147621 : Blo 603293 1147621 := bbase (se 4 (by rfl) ⟨107589, by rfl⟩ : syracuseStep 1147621 = 215179) (by norm_num)
theorem B1147765 : Blo 603293 1147765 := bbase (se 5 (by rfl) ⟨53801, by rfl⟩ : syracuseStep 1147765 = 107603) (by norm_num)
theorem B2458565 : Blo 603293 2458565 := bbase (se 4 (by rfl) ⟨230490, by rfl⟩ : syracuseStep 2458565 = 460981) (by norm_num)
theorem B1147925 : Blo 603293 1147925 := bbase (se 6 (by rfl) ⟨26904, by rfl⟩ : syracuseStep 1147925 = 53809) (by norm_num)
theorem B1148069 : Blo 603293 1148069 := bbase (se 4 (by rfl) ⟨107631, by rfl⟩ : syracuseStep 1148069 = 215263) (by norm_num)
theorem B2295013 : Blo 603293 2295013 := bbase (se 4 (by rfl) ⟨215157, by rfl⟩ : syracuseStep 2295013 = 430315) (by norm_num)
theorem B3278069 : Blo 603293 3278069 := bbase (se 5 (by rfl) ⟨153659, by rfl⟩ : syracuseStep 3278069 = 307319) (by norm_num)
theorem B820469 : Blo 603293 820469 := bbase (se 5 (by rfl) ⟨38459, by rfl⟩ : syracuseStep 820469 = 76919) (by norm_num)
theorem B3441973 : Blo 603293 3441973 := bbase (se 5 (by rfl) ⟨161342, by rfl⟩ : syracuseStep 3441973 = 322685) (by norm_num)
theorem B1148357 : Blo 603293 1148357 := bbase (se 4 (by rfl) ⟨107658, by rfl⟩ : syracuseStep 1148357 = 215317) (by norm_num)
theorem B2295317 : Blo 603293 2295317 := bbase (se 6 (by rfl) ⟨53796, by rfl⟩ : syracuseStep 2295317 = 107593) (by norm_num)
theorem B1148509 : Blo 603293 1148509 := bbase (se 3 (by rfl) ⟨215345, by rfl⟩ : syracuseStep 1148509 = 430691) (by norm_num)
theorem B1377901 : Blo 603293 1377901 := bbase (se 3 (by rfl) ⟨258356, by rfl⟩ : syracuseStep 1377901 = 516713) (by norm_num)
theorem B886477 : Blo 603293 886477 := bbase (se 3 (by rfl) ⟨166214, by rfl⟩ : syracuseStep 886477 = 332429) (by norm_num)
theorem B1836773 : Blo 603293 1836773 := bbase (se 4 (by rfl) ⟨172197, by rfl⟩ : syracuseStep 1836773 = 344395) (by norm_num)
theorem B1640245 : Blo 603293 1640245 := bbase (se 5 (by rfl) ⟨76886, by rfl⟩ : syracuseStep 1640245 = 153773) (by norm_num)
theorem B1148813 : Blo 603293 1148813 := bbase (se 3 (by rfl) ⟨215402, by rfl⟩ : syracuseStep 1148813 = 430805) (by norm_num)
theorem B657293 : Blo 603293 657293 := bbase (se 3 (by rfl) ⟨123242, by rfl⟩ : syracuseStep 657293 = 246485) (by norm_num)
theorem B919621 : Blo 603293 919621 := bbase (se 4 (by rfl) ⟨86214, by rfl⟩ : syracuseStep 919621 = 172429) (by norm_num)
theorem B1378421 : Blo 603293 1378421 := bbase (se 5 (by rfl) ⟨64613, by rfl⟩ : syracuseStep 1378421 = 129227) (by norm_num)
theorem B1018109 : Blo 603293 1018109 := bbase (se 3 (by rfl) ⟨190895, by rfl⟩ : syracuseStep 1018109 = 381791) (by norm_num)
theorem B985421 : Blo 603293 985421 := bbase (se 3 (by rfl) ⟨184766, by rfl⟩ : syracuseStep 985421 = 369533) (by norm_num)
theorem B1935701 : Blo 603293 1935701 := bbase (se 10 (by rfl) ⟨2835, by rfl⟩ : syracuseStep 1935701 = 5671) (by norm_num)
theorem B3869045 : Blo 603293 3869045 := bbase (se 5 (by rfl) ⟨181361, by rfl⟩ : syracuseStep 3869045 = 362723) (by norm_num)
theorem B1018237 : Blo 603293 1018237 := bbase (se 3 (by rfl) ⟨190919, by rfl⟩ : syracuseStep 1018237 = 381839) (by norm_num)
theorem B1018325 : Blo 603293 1018325 := bbase (se 7 (by rfl) ⟨11933, by rfl⟩ : syracuseStep 1018325 = 23867) (by norm_num)
theorem B1935829 : Blo 603293 1935829 := bbase (se 7 (by rfl) ⟨22685, by rfl⟩ : syracuseStep 1935829 = 45371) (by norm_num)
theorem B788977 : Blo 603293 788977 := bbase (se 2 (by rfl) ⟨295866, by rfl⟩ : syracuseStep 788977 = 591733) (by norm_num)
theorem B1018453 : Blo 603293 1018453 := bbase (se 8 (by rfl) ⟨5967, by rfl⟩ : syracuseStep 1018453 = 11935) (by norm_num)
theorem B1149565 : Blo 603293 1149565 := bbase (se 3 (by rfl) ⟨215543, by rfl⟩ : syracuseStep 1149565 = 431087) (by norm_num)
theorem B1018541 : Blo 603293 1018541 := bbase (se 3 (by rfl) ⟨190976, by rfl⟩ : syracuseStep 1018541 = 381953) (by norm_num)
theorem B1641205 : Blo 603293 1641205 := bbase (se 5 (by rfl) ⟨76931, by rfl⟩ : syracuseStep 1641205 = 153863) (by norm_num)
theorem B1149709 : Blo 603293 1149709 := bbase (se 3 (by rfl) ⟨215570, by rfl⟩ : syracuseStep 1149709 = 431141) (by norm_num)
theorem B1018669 : Blo 603293 1018669 := bbase (se 3 (by rfl) ⟨191000, by rfl⟩ : syracuseStep 1018669 = 382001) (by norm_num)
theorem B1018757 : Blo 603293 1018757 := bbase (se 4 (by rfl) ⟨95508, by rfl⟩ : syracuseStep 1018757 = 191017) (by norm_num)
theorem B1149869 : Blo 603293 1149869 := bbase (se 3 (by rfl) ⟨215600, by rfl⟩ : syracuseStep 1149869 = 431201) (by norm_num)
theorem B1018885 : Blo 603293 1018885 := bbase (se 4 (by rfl) ⟨95520, by rfl⟩ : syracuseStep 1018885 = 191041) (by norm_num)
theorem B1150013 : Blo 603293 1150013 := bbase (se 3 (by rfl) ⟨215627, by rfl⟩ : syracuseStep 1150013 = 431255) (by norm_num)
theorem B1018973 : Blo 603293 1018973 := bbase (se 3 (by rfl) ⟨191057, by rfl⟩ : syracuseStep 1018973 = 382115) (by norm_num)
theorem B1019101 : Blo 603293 1019101 := bbase (se 3 (by rfl) ⟨191081, by rfl⟩ : syracuseStep 1019101 = 382163) (by norm_num)
theorem B3443957 : Blo 603293 3443957 := bbase (se 5 (by rfl) ⟨161435, by rfl⟩ : syracuseStep 3443957 = 322871) (by norm_num)
theorem B691481 : Blo 603293 691481 := bbase (se 2 (by rfl) ⟨259305, by rfl⟩ : syracuseStep 691481 = 518611) (by norm_num)
theorem B1019189 : Blo 603293 1019189 := bbase (se 5 (by rfl) ⟨47774, by rfl⟩ : syracuseStep 1019189 = 95549) (by norm_num)
theorem B1150301 : Blo 603293 1150301 := bbase (se 3 (by rfl) ⟨215681, by rfl⟩ : syracuseStep 1150301 = 431363) (by norm_num)
theorem B920989 : Blo 603293 920989 := bbase (se 3 (by rfl) ⟨172685, by rfl⟩ : syracuseStep 920989 = 345371) (by norm_num)
theorem B1478045 : Blo 603293 1478045 := bbase (se 3 (by rfl) ⟨277133, by rfl⟩ : syracuseStep 1478045 = 554267) (by norm_num)
theorem B1019317 : Blo 603293 1019317 := bbase (se 5 (by rfl) ⟨47780, by rfl⟩ : syracuseStep 1019317 = 95561) (by norm_num)
theorem B4656565 : Blo 603293 4656565 := bbase (se 5 (by rfl) ⟨218276, by rfl⟩ : syracuseStep 4656565 = 436553) (by norm_num)
theorem B2985461 : Blo 603293 2985461 := bbase (se 5 (by rfl) ⟨139943, by rfl⟩ : syracuseStep 2985461 = 279887) (by norm_num)
theorem B1150453 : Blo 603293 1150453 := bbase (se 5 (by rfl) ⟨53927, by rfl⟩ : syracuseStep 1150453 = 107855) (by norm_num)
theorem B1019405 : Blo 603293 1019405 := bbase (se 3 (by rfl) ⟨191138, by rfl⟩ : syracuseStep 1019405 = 382277) (by norm_num)
theorem B2297429 : Blo 603293 2297429 := bbase (se 8 (by rfl) ⟨13461, by rfl⟩ : syracuseStep 2297429 = 26923) (by norm_num)
theorem B1019533 : Blo 603293 1019533 := bbase (se 3 (by rfl) ⟨191162, by rfl⟩ : syracuseStep 1019533 = 382325) (by norm_num)
theorem B1019621 : Blo 603293 1019621 := bbase (se 4 (by rfl) ⟨95589, by rfl⟩ : syracuseStep 1019621 = 191179) (by norm_num)
theorem B2592485 : Blo 603293 2592485 := bbase (se 4 (by rfl) ⟨243045, by rfl⟩ : syracuseStep 2592485 = 486091) (by norm_num)
theorem B1150757 : Blo 603293 1150757 := bbase (se 4 (by rfl) ⟨107883, by rfl⟩ : syracuseStep 1150757 = 215767) (by norm_num)
theorem B1019749 : Blo 603293 1019749 := bbase (se 4 (by rfl) ⟨95601, by rfl⟩ : syracuseStep 1019749 = 191203) (by norm_num)
theorem B2297717 : Blo 603293 2297717 := bbase (se 5 (by rfl) ⟨107705, by rfl⟩ : syracuseStep 2297717 = 215411) (by norm_num)
theorem B1019837 : Blo 603293 1019837 := bbase (se 3 (by rfl) ⟨191219, by rfl⟩ : syracuseStep 1019837 = 382439) (by norm_num)
theorem B692165 : Blo 603293 692165 := bbase (se 4 (by rfl) ⟨64890, by rfl⟩ : syracuseStep 692165 = 129781) (by norm_num)
theorem B1019965 : Blo 603293 1019965 := bbase (se 3 (by rfl) ⟨191243, by rfl⟩ : syracuseStep 1019965 = 382487) (by norm_num)
theorem B1020053 : Blo 603293 1020053 := bbase (se 6 (by rfl) ⟨23907, by rfl⟩ : syracuseStep 1020053 = 47815) (by norm_num)
theorem B4657333 : Blo 603293 4657333 := bbase (se 5 (by rfl) ⟨218312, by rfl⟩ : syracuseStep 4657333 = 436625) (by norm_num)
theorem B1020181 : Blo 603293 1020181 := bbase (se 6 (by rfl) ⟨23910, by rfl⟩ : syracuseStep 1020181 = 47821) (by norm_num)
theorem B725321 : Blo 603293 725321 := bbase (se 2 (by rfl) ⟨271995, by rfl⟩ : syracuseStep 725321 = 543991) (by norm_num)
theorem B1020269 : Blo 603293 1020269 := bbase (se 3 (by rfl) ⟨191300, by rfl⟩ : syracuseStep 1020269 = 382601) (by norm_num)
theorem B1020397 : Blo 603293 1020397 := bbase (se 3 (by rfl) ⟨191324, by rfl⟩ : syracuseStep 1020397 = 382649) (by norm_num)
theorem B11637269 : Blo 603293 11637269 := bbase (se 6 (by rfl) ⟨272748, by rfl⟩ : syracuseStep 11637269 = 545497) (by norm_num)
theorem B1151509 : Blo 603293 1151509 := bbase (se 6 (by rfl) ⟨26988, by rfl⟩ : syracuseStep 1151509 = 53977) (by norm_num)
theorem B1020485 : Blo 603293 1020485 := bbase (se 4 (by rfl) ⟨95670, by rfl⟩ : syracuseStep 1020485 = 191341) (by norm_num)
theorem B4592213 : Blo 603293 4592213 := bbase (se 8 (by rfl) ⟨26907, by rfl⟩ : syracuseStep 4592213 = 53815) (by norm_num)
theorem B725657 : Blo 603293 725657 := bbase (se 2 (by rfl) ⟨272121, by rfl⟩ : syracuseStep 725657 = 544243) (by norm_num)
theorem B1151653 : Blo 603293 1151653 := bbase (se 4 (by rfl) ⟨107967, by rfl⟩ : syracuseStep 1151653 = 215935) (by norm_num)
theorem B1020613 : Blo 603293 1020613 := bbase (se 4 (by rfl) ⟨95682, by rfl⟩ : syracuseStep 1020613 = 191365) (by norm_num)
theorem B4362997 : Blo 603293 4362997 := bbase (se 5 (by rfl) ⟨204515, by rfl⟩ : syracuseStep 4362997 = 409031) (by norm_num)
theorem B725773 : Blo 603293 725773 := bbase (se 3 (by rfl) ⟨136082, by rfl⟩ : syracuseStep 725773 = 272165) (by norm_num)
theorem B2036501 : Blo 603293 2036501 := bbase (se 6 (by rfl) ⟨47730, by rfl⟩ : syracuseStep 2036501 = 95461) (by norm_num)
theorem B1020701 : Blo 603293 1020701 := bbase (se 3 (by rfl) ⟨191381, by rfl⟩ : syracuseStep 1020701 = 382763) (by norm_num)
theorem B1151813 : Blo 603293 1151813 := bbase (se 4 (by rfl) ⟨107982, by rfl⟩ : syracuseStep 1151813 = 215965) (by norm_num)
theorem B725845 : Blo 603293 725845 := bbase (se 9 (by rfl) ⟨2126, by rfl⟩ : syracuseStep 725845 = 4253) (by norm_num)
theorem B725869 : Blo 603293 725869 := bbase (se 3 (by rfl) ⟨136100, by rfl⟩ : syracuseStep 725869 = 272201) (by norm_num)
theorem B1020829 : Blo 603293 1020829 := bbase (se 3 (by rfl) ⟨191405, by rfl⟩ : syracuseStep 1020829 = 382811) (by norm_num)
theorem B1151957 : Blo 603293 1151957 := bbase (se 7 (by rfl) ⟨13499, by rfl⟩ : syracuseStep 1151957 = 26999) (by norm_num)
theorem B1020917 : Blo 603293 1020917 := bbase (se 5 (by rfl) ⟨47855, by rfl⟩ : syracuseStep 1020917 = 95711) (by norm_num)
theorem B726013 : Blo 603293 726013 := bbase (se 3 (by rfl) ⟨136127, by rfl⟩ : syracuseStep 726013 = 272255) (by norm_num)
theorem B2298901 : Blo 603293 2298901 := bbase (se 6 (by rfl) ⟨53880, by rfl⟩ : syracuseStep 2298901 = 107761) (by norm_num)
theorem B1840229 : Blo 603293 1840229 := bbase (se 4 (by rfl) ⟨172521, by rfl⟩ : syracuseStep 1840229 = 345043) (by norm_num)
theorem B1021045 : Blo 603293 1021045 := bbase (se 5 (by rfl) ⟨47861, by rfl⟩ : syracuseStep 1021045 = 95723) (by norm_num)
theorem B2036933 : Blo 603293 2036933 := bbase (se 4 (by rfl) ⟨190962, by rfl⟩ : syracuseStep 2036933 = 381925) (by norm_num)
theorem B1021133 : Blo 603293 1021133 := bbase (se 3 (by rfl) ⟨191462, by rfl⟩ : syracuseStep 1021133 = 382925) (by norm_num)
theorem B1152245 : Blo 603293 1152245 := bbase (se 5 (by rfl) ⟨54011, by rfl⟩ : syracuseStep 1152245 = 108023) (by norm_num)
theorem B1938725 : Blo 603293 1938725 := bbase (se 4 (by rfl) ⟨181755, by rfl⟩ : syracuseStep 1938725 = 363511) (by norm_num)
theorem B1840421 : Blo 603293 1840421 := bbase (se 4 (by rfl) ⟨172539, by rfl⟩ : syracuseStep 1840421 = 345079) (by norm_num)
theorem B2299205 : Blo 603293 2299205 := bbase (se 4 (by rfl) ⟨215550, by rfl⟩ : syracuseStep 2299205 = 431101) (by norm_num)
theorem B1021261 : Blo 603293 1021261 := bbase (se 3 (by rfl) ⟨191486, by rfl⟩ : syracuseStep 1021261 = 382973) (by norm_num)
theorem B1152397 : Blo 603293 1152397 := bbase (se 3 (by rfl) ⟨216074, by rfl⟩ : syracuseStep 1152397 = 432149) (by norm_num)
theorem B3446165 : Blo 603293 3446165 := bbase (se 6 (by rfl) ⟨80769, by rfl⟩ : syracuseStep 3446165 = 161539) (by norm_num)
theorem B1021349 : Blo 603293 1021349 := bbase (se 4 (by rfl) ⟨95751, by rfl⟩ : syracuseStep 1021349 = 191503) (by norm_num)
theorem B1021477 : Blo 603293 1021477 := bbase (se 4 (by rfl) ⟨95763, by rfl⟩ : syracuseStep 1021477 = 191527) (by norm_num)
theorem B11605589 : Blo 603293 11605589 := bbase (se 8 (by rfl) ⟨68001, by rfl⟩ : syracuseStep 11605589 = 136003) (by norm_num)
theorem B2037365 : Blo 603293 2037365 := bbase (se 5 (by rfl) ⟨95501, by rfl⟩ : syracuseStep 2037365 = 191003) (by norm_num)
theorem B1021565 : Blo 603293 1021565 := bbase (se 3 (by rfl) ⟨191543, by rfl⟩ : syracuseStep 1021565 = 383087) (by norm_num)
theorem B1152701 : Blo 603293 1152701 := bbase (se 3 (by rfl) ⟨216131, by rfl⟩ : syracuseStep 1152701 = 432263) (by norm_num)
theorem B1021693 : Blo 603293 1021693 := bbase (se 3 (by rfl) ⟨191567, by rfl⟩ : syracuseStep 1021693 = 383135) (by norm_num)
theorem B1021781 : Blo 603293 1021781 := bbase (se 9 (by rfl) ⟨2993, by rfl⟩ : syracuseStep 1021781 = 5987) (by norm_num)
theorem B1841093 : Blo 603293 1841093 := bbase (se 4 (by rfl) ⟨172602, by rfl⟩ : syracuseStep 1841093 = 345205) (by norm_num)
theorem B1021909 : Blo 603293 1021909 := bbase (se 7 (by rfl) ⟨11975, by rfl⟩ : syracuseStep 1021909 = 23951) (by norm_num)
theorem B13277141 : Blo 603293 13277141 := bbase (se 7 (by rfl) ⟨155591, by rfl⟩ : syracuseStep 13277141 = 311183) (by norm_num)
theorem B2037797 : Blo 603293 2037797 := bbase (se 4 (by rfl) ⟨191043, by rfl⟩ : syracuseStep 2037797 = 382087) (by norm_num)
theorem B1021997 : Blo 603293 1021997 := bbase (se 3 (by rfl) ⟨191624, by rfl⟩ : syracuseStep 1021997 = 383249) (by norm_num)
theorem B1022125 : Blo 603293 1022125 := bbase (se 3 (by rfl) ⟨191648, by rfl⟩ : syracuseStep 1022125 = 383297) (by norm_num)
theorem B727229 : Blo 603293 727229 := bbase (se 3 (by rfl) ⟨136355, by rfl⟩ : syracuseStep 727229 = 272711) (by norm_num)
theorem B1022213 : Blo 603293 1022213 := bbase (se 4 (by rfl) ⟨95832, by rfl⟩ : syracuseStep 1022213 = 191665) (by norm_num)
theorem B1022341 : Blo 603293 1022341 := bbase (se 4 (by rfl) ⟨95844, by rfl⟩ : syracuseStep 1022341 = 191689) (by norm_num)
theorem B1382789 : Blo 603293 1382789 := bbase (se 4 (by rfl) ⟨129636, by rfl⟩ : syracuseStep 1382789 = 259273) (by norm_num)
theorem B2038229 : Blo 603293 2038229 := bbase (se 7 (by rfl) ⟨23885, by rfl⟩ : syracuseStep 2038229 = 47771) (by norm_num)
theorem B1022429 : Blo 603293 1022429 := bbase (se 3 (by rfl) ⟨191705, by rfl⟩ : syracuseStep 1022429 = 383411) (by norm_num)
theorem B727537 : Blo 603293 727537 := bbase (se 2 (by rfl) ⟨272826, by rfl⟩ : syracuseStep 727537 = 545653) (by norm_num)
theorem B4659797 : Blo 603293 4659797 := bbase (se 8 (by rfl) ⟨27303, by rfl⟩ : syracuseStep 4659797 = 54607) (by norm_num)
theorem B727637 : Blo 603293 727637 := bbase (se 8 (by rfl) ⟨4263, by rfl⟩ : syracuseStep 727637 = 8527) (by norm_num)
theorem B1022557 : Blo 603293 1022557 := bbase (se 3 (by rfl) ⟨191729, by rfl⟩ : syracuseStep 1022557 = 383459) (by norm_num)
theorem B1022645 : Blo 603293 1022645 := bbase (se 5 (by rfl) ⟨47936, by rfl⟩ : syracuseStep 1022645 = 95873) (by norm_num)
theorem B1022773 : Blo 603293 1022773 := bbase (se 5 (by rfl) ⟨47942, by rfl⟩ : syracuseStep 1022773 = 95885) (by norm_num)
theorem B2038661 : Blo 603293 2038661 := bbase (se 4 (by rfl) ⟨191124, by rfl⟩ : syracuseStep 2038661 = 382249) (by norm_num)
theorem B1022861 : Blo 603293 1022861 := bbase (se 3 (by rfl) ⟨191786, by rfl⟩ : syracuseStep 1022861 = 383573) (by norm_num)
theorem B728041 : Blo 603293 728041 := bbase (se 2 (by rfl) ⟨273015, by rfl⟩ : syracuseStep 728041 = 546031) (by norm_num)
theorem B1022989 : Blo 603293 1022989 := bbase (se 3 (by rfl) ⟨191810, by rfl⟩ : syracuseStep 1022989 = 383621) (by norm_num)
theorem B1023077 : Blo 603293 1023077 := bbase (se 4 (by rfl) ⟨95913, by rfl⟩ : syracuseStep 1023077 = 191827) (by norm_num)
theorem B10362005 : Blo 603293 10362005 := bbase (se 6 (by rfl) ⟨242859, by rfl⟩ : syracuseStep 10362005 = 485719) (by norm_num)
theorem B859349 : Blo 603293 859349 := bbase (se 7 (by rfl) ⟨10070, by rfl⟩ : syracuseStep 859349 = 20141) (by norm_num)
theorem B1023205 : Blo 603293 1023205 := bbase (se 4 (by rfl) ⟨95925, by rfl⟩ : syracuseStep 1023205 = 191851) (by norm_num)
theorem B2039093 : Blo 603293 2039093 := bbase (se 5 (by rfl) ⟨95582, by rfl⟩ : syracuseStep 2039093 = 191165) (by norm_num)
theorem B1023293 : Blo 603293 1023293 := bbase (se 3 (by rfl) ⟨191867, by rfl⟩ : syracuseStep 1023293 = 383735) (by norm_num)
theorem B728425 : Blo 603293 728425 := bbase (se 2 (by rfl) ⟨273159, by rfl⟩ : syracuseStep 728425 = 546319) (by norm_num)
theorem B2301317 : Blo 603293 2301317 := bbase (se 4 (by rfl) ⟨215748, by rfl⟩ : syracuseStep 2301317 = 431497) (by norm_num)
theorem B2956709 : Blo 603293 2956709 := bbase (se 4 (by rfl) ⟨277191, by rfl⟩ : syracuseStep 2956709 = 554383) (by norm_num)
theorem B1940917 : Blo 603293 1940917 := bbase (se 5 (by rfl) ⟨90980, by rfl⟩ : syracuseStep 1940917 = 181961) (by norm_num)
theorem B1023421 : Blo 603293 1023421 := bbase (se 3 (by rfl) ⟨191891, by rfl⟩ : syracuseStep 1023421 = 383783) (by norm_num)
theorem B2334197 : Blo 603293 2334197 := bbase (se 5 (by rfl) ⟨109415, by rfl⟩ : syracuseStep 2334197 = 218831) (by norm_num)
theorem B1023509 : Blo 603293 1023509 := bbase (se 6 (by rfl) ⟨23988, by rfl⟩ : syracuseStep 1023509 = 47977) (by norm_num)
theorem B3055157 : Blo 603293 3055157 := bbase (se 5 (by rfl) ⟨143210, by rfl⟩ : syracuseStep 3055157 = 286421) (by norm_num)
theorem B1023637 : Blo 603293 1023637 := bbase (se 6 (by rfl) ⟨23991, by rfl⟩ : syracuseStep 1023637 = 47983) (by norm_num)
theorem B2301605 : Blo 603293 2301605 := bbase (se 4 (by rfl) ⟨215775, by rfl⟩ : syracuseStep 2301605 = 431551) (by norm_num)
theorem B1089229 : Blo 603293 1089229 := bbase (se 3 (by rfl) ⟨204230, by rfl⟩ : syracuseStep 1089229 = 408461) (by norm_num)
theorem B1449701 : Blo 603293 1449701 := bbase (se 4 (by rfl) ⟨135909, by rfl⟩ : syracuseStep 1449701 = 271819) (by norm_num)
theorem B2039525 : Blo 603293 2039525 := bbase (se 4 (by rfl) ⟨191205, by rfl⟩ : syracuseStep 2039525 = 382411) (by norm_num)
theorem B1023725 : Blo 603293 1023725 := bbase (se 3 (by rfl) ⟨191948, by rfl⟩ : syracuseStep 1023725 = 383897) (by norm_num)
theorem B859901 : Blo 603293 859901 := bbase (se 3 (by rfl) ⟨161231, by rfl⟩ : syracuseStep 859901 = 322463) (by norm_num)
theorem B1089293 : Blo 603293 1089293 := bbase (se 3 (by rfl) ⟨204242, by rfl⟩ : syracuseStep 1089293 = 408485) (by norm_num)
theorem B1023853 : Blo 603293 1023853 := bbase (se 3 (by rfl) ⟨191972, by rfl⟩ : syracuseStep 1023853 = 383945) (by norm_num)
theorem B1449893 : Blo 603293 1449893 := bbase (se 4 (by rfl) ⟨135927, by rfl⟩ : syracuseStep 1449893 = 271855) (by norm_num)
theorem B1023941 : Blo 603293 1023941 := bbase (se 4 (by rfl) ⟨95994, by rfl⟩ : syracuseStep 1023941 = 191989) (by norm_num)
theorem B1024069 : Blo 603293 1024069 := bbase (se 4 (by rfl) ⟨96006, by rfl⟩ : syracuseStep 1024069 = 192013) (by norm_num)
theorem B2039957 : Blo 603293 2039957 := bbase (se 6 (by rfl) ⟨47811, by rfl⟩ : syracuseStep 2039957 = 95623) (by norm_num)
theorem B1024157 : Blo 603293 1024157 := bbase (se 3 (by rfl) ⟨192029, by rfl⟩ : syracuseStep 1024157 = 384059) (by norm_num)
theorem B729281 : Blo 603293 729281 := bbase (se 2 (by rfl) ⟨273480, by rfl⟩ : syracuseStep 729281 = 546961) (by norm_num)
theorem B1941749 : Blo 603293 1941749 := bbase (se 5 (by rfl) ⟨91019, by rfl⟩ : syracuseStep 1941749 = 182039) (by norm_num)
theorem B1024285 : Blo 603293 1024285 := bbase (se 3 (by rfl) ⟨192053, by rfl⟩ : syracuseStep 1024285 = 384107) (by norm_num)
theorem B1024373 : Blo 603293 1024373 := bbase (se 5 (by rfl) ⟨48017, by rfl⟩ : syracuseStep 1024373 = 96035) (by norm_num)
theorem B1450469 : Blo 603293 1450469 := bbase (se 4 (by rfl) ⟨135981, by rfl⟩ : syracuseStep 1450469 = 271963) (by norm_num)
theorem B860653 : Blo 603293 860653 := bbase (se 3 (by rfl) ⟨161372, by rfl⟩ : syracuseStep 860653 = 322745) (by norm_num)
theorem B1024501 : Blo 603293 1024501 := bbase (se 5 (by rfl) ⟨48023, by rfl⟩ : syracuseStep 1024501 = 96047) (by norm_num)
theorem B2040389 : Blo 603293 2040389 := bbase (se 4 (by rfl) ⟨191286, by rfl⟩ : syracuseStep 2040389 = 382573) (by norm_num)
theorem B1024589 : Blo 603293 1024589 := bbase (se 3 (by rfl) ⟨192110, by rfl⟩ : syracuseStep 1024589 = 384221) (by norm_num)
theorem B1024717 : Blo 603293 1024717 := bbase (se 3 (by rfl) ⟨192134, by rfl⟩ : syracuseStep 1024717 = 384269) (by norm_num)
theorem B1024805 : Blo 603293 1024805 := bbase (se 4 (by rfl) ⟨96075, by rfl⟩ : syracuseStep 1024805 = 192151) (by norm_num)
theorem B3056453 : Blo 603293 3056453 := bbase (se 4 (by rfl) ⟨286542, by rfl⟩ : syracuseStep 3056453 = 573085) (by norm_num)
theorem B2302789 : Blo 603293 2302789 := bbase (se 4 (by rfl) ⟨215886, by rfl⟩ : syracuseStep 2302789 = 431773) (by norm_num)
theorem B1450853 : Blo 603293 1450853 := bbase (se 4 (by rfl) ⟨136017, by rfl⟩ : syracuseStep 1450853 = 272035) (by norm_num)
theorem B4137941 : Blo 603293 4137941 := bbase (se 7 (by rfl) ⟨48491, by rfl⟩ : syracuseStep 4137941 = 96983) (by norm_num)
theorem B2040821 : Blo 603293 2040821 := bbase (se 5 (by rfl) ⟨95663, by rfl⟩ : syracuseStep 2040821 = 191327) (by norm_num)
theorem B1090613 : Blo 603293 1090613 := bbase (se 5 (by rfl) ⟨51122, by rfl⟩ : syracuseStep 1090613 = 102245) (by norm_num)
theorem B2303093 : Blo 603293 2303093 := bbase (se 5 (by rfl) ⟨107957, by rfl⟩ : syracuseStep 2303093 = 215915) (by norm_num)
theorem B1746085 : Blo 603293 1746085 := bbase (se 4 (by rfl) ⟨163695, by rfl⟩ : syracuseStep 1746085 = 327391) (by norm_num)
theorem B861445 : Blo 603293 861445 := bbase (se 4 (by rfl) ⟨80760, by rfl⟩ : syracuseStep 861445 = 161521) (by norm_num)
theorem B2041253 : Blo 603293 2041253 := bbase (se 4 (by rfl) ⟨191367, by rfl⟩ : syracuseStep 2041253 = 382735) (by norm_num)
theorem B959941 : Blo 603293 959941 := bbase (se 4 (by rfl) ⟨89994, by rfl⟩ : syracuseStep 959941 = 179989) (by norm_num)
theorem B2336309 : Blo 603293 2336309 := bbase (se 5 (by rfl) ⟨109514, by rfl⟩ : syracuseStep 2336309 = 219029) (by norm_num)
theorem B861781 : Blo 603293 861781 := bbase (se 8 (by rfl) ⟨5049, by rfl⟩ : syracuseStep 861781 = 10099) (by norm_num)
theorem B763597 : Blo 603293 763597 := bbase (se 3 (by rfl) ⟨143174, by rfl⟩ : syracuseStep 763597 = 286349) (by norm_num)
theorem B861997 : Blo 603293 861997 := bbase (se 3 (by rfl) ⟨161624, by rfl⟩ : syracuseStep 861997 = 323249) (by norm_num)
theorem B2041685 : Blo 603293 2041685 := bbase (se 9 (by rfl) ⟨5981, by rfl⟩ : syracuseStep 2041685 = 11963) (by norm_num)
theorem B763769 : Blo 603293 763769 := bbase (se 2 (by rfl) ⟨286413, by rfl⟩ : syracuseStep 763769 = 572827) (by norm_num)
theorem B763825 : Blo 603293 763825 := bbase (se 2 (by rfl) ⟨286434, by rfl⟩ : syracuseStep 763825 = 572869) (by norm_num)
theorem B763921 : Blo 603293 763921 := bbase (se 2 (by rfl) ⟨286470, by rfl⟩ : syracuseStep 763921 = 572941) (by norm_num)
theorem B1943621 : Blo 603293 1943621 := bbase (se 4 (by rfl) ⟨182214, by rfl⟩ : syracuseStep 1943621 = 364429) (by norm_num)
theorem B3057749 : Blo 603293 3057749 := bbase (se 8 (by rfl) ⟨17916, by rfl⟩ : syracuseStep 3057749 = 35833) (by norm_num)
theorem B862373 : Blo 603293 862373 := bbase (se 4 (by rfl) ⟨80847, by rfl⟩ : syracuseStep 862373 = 161695) (by norm_num)
theorem B764093 : Blo 603293 764093 := bbase (se 3 (by rfl) ⟨143267, by rfl⟩ : syracuseStep 764093 = 286535) (by norm_num)
theorem B764149 : Blo 603293 764149 := bbase (se 5 (by rfl) ⟨35819, by rfl⟩ : syracuseStep 764149 = 71639) (by norm_num)
theorem B2042117 : Blo 603293 2042117 := bbase (se 4 (by rfl) ⟨191448, by rfl⟩ : syracuseStep 2042117 = 382897) (by norm_num)
theorem B3877141 : Blo 603293 3877141 := bbase (se 6 (by rfl) ⟨90870, by rfl⟩ : syracuseStep 3877141 = 181741) (by norm_num)
theorem B1091917 : Blo 603293 1091917 := bbase (se 3 (by rfl) ⟨204734, by rfl⟩ : syracuseStep 1091917 = 409469) (by norm_num)
theorem B764245 : Blo 603293 764245 := bbase (se 10 (by rfl) ⟨1119, by rfl⟩ : syracuseStep 764245 = 2239) (by norm_num)
theorem B764417 : Blo 603293 764417 := bbase (se 2 (by rfl) ⟨286656, by rfl⟩ : syracuseStep 764417 = 573313) (by norm_num)
theorem B829957 : Blo 603293 829957 := bbase (se 4 (by rfl) ⟨77808, by rfl⟩ : syracuseStep 829957 = 155617) (by norm_num)
theorem B764473 : Blo 603293 764473 := bbase (se 2 (by rfl) ⟨286677, by rfl⟩ : syracuseStep 764473 = 573355) (by norm_num)
theorem B1452613 : Blo 603293 1452613 := bbase (se 4 (by rfl) ⟨136182, by rfl⟩ : syracuseStep 1452613 = 272365) (by norm_num)
theorem B764569 : Blo 603293 764569 := bbase (se 2 (by rfl) ⟨286713, by rfl⟩ : syracuseStep 764569 = 573427) (by norm_num)
theorem B2042549 : Blo 603293 2042549 := bbase (se 5 (by rfl) ⟨95744, by rfl⟩ : syracuseStep 2042549 = 191489) (by norm_num)
theorem B764741 : Blo 603293 764741 := bbase (se 4 (by rfl) ⟨71694, by rfl⟩ : syracuseStep 764741 = 143389) (by norm_num)
theorem B2796373 : Blo 603293 2796373 := bbase (se 9 (by rfl) ⟨8192, by rfl⟩ : syracuseStep 2796373 = 16385) (by norm_num)
theorem B764797 : Blo 603293 764797 := bbase (se 3 (by rfl) ⟨143399, by rfl⟩ : syracuseStep 764797 = 286799) (by norm_num)
theorem B764893 : Blo 603293 764893 := bbase (se 3 (by rfl) ⟨143417, by rfl⟩ : syracuseStep 764893 = 286835) (by norm_num)
theorem B2042981 : Blo 603293 2042981 := bbase (se 4 (by rfl) ⟨191529, by rfl⟩ : syracuseStep 2042981 = 383059) (by norm_num)
theorem B765065 : Blo 603293 765065 := bbase (se 2 (by rfl) ⟨286899, by rfl⟩ : syracuseStep 765065 = 573799) (by norm_num)
theorem B2305205 : Blo 603293 2305205 := bbase (se 5 (by rfl) ⟨108056, by rfl⟩ : syracuseStep 2305205 = 216113) (by norm_num)
theorem B765121 : Blo 603293 765121 := bbase (se 2 (by rfl) ⟨286920, by rfl⟩ : syracuseStep 765121 = 573841) (by norm_num)
theorem B765217 : Blo 603293 765217 := bbase (se 2 (by rfl) ⟨286956, by rfl⟩ : syracuseStep 765217 = 573913) (by norm_num)
theorem B3059045 : Blo 603293 3059045 := bbase (se 4 (by rfl) ⟨286785, by rfl⟩ : syracuseStep 3059045 = 573571) (by norm_num)
theorem B765389 : Blo 603293 765389 := bbase (se 3 (by rfl) ⟨143510, by rfl⟩ : syracuseStep 765389 = 287021) (by norm_num)
theorem B2305493 : Blo 603293 2305493 := bbase (se 7 (by rfl) ⟨27017, by rfl⟩ : syracuseStep 2305493 = 54035) (by norm_num)
theorem B765445 : Blo 603293 765445 := bbase (se 4 (by rfl) ⟨71760, by rfl⟩ : syracuseStep 765445 = 143521) (by norm_num)
theorem B2043413 : Blo 603293 2043413 := bbase (se 6 (by rfl) ⟨47892, by rfl⟩ : syracuseStep 2043413 = 95785) (by norm_num)
theorem B1093157 : Blo 603293 1093157 := bbase (se 4 (by rfl) ⟨102483, by rfl⟩ : syracuseStep 1093157 = 204967) (by norm_num)
theorem B1453621 : Blo 603293 1453621 := bbase (se 5 (by rfl) ⟨68138, by rfl⟩ : syracuseStep 1453621 = 136277) (by norm_num)
theorem B863797 : Blo 603293 863797 := bbase (se 5 (by rfl) ⟨40490, by rfl⟩ : syracuseStep 863797 = 80981) (by norm_num)
theorem B765541 : Blo 603293 765541 := bbase (se 4 (by rfl) ⟨71769, by rfl⟩ : syracuseStep 765541 = 143539) (by norm_num)
theorem B1453717 : Blo 603293 1453717 := bbase (se 6 (by rfl) ⟨34071, by rfl⟩ : syracuseStep 1453717 = 68143) (by norm_num)
theorem B4140725 : Blo 603293 4140725 := bbase (se 5 (by rfl) ⟨194096, by rfl⟩ : syracuseStep 4140725 = 388193) (by norm_num)
theorem B1289981 : Blo 603293 1289981 := bbase (se 3 (by rfl) ⟨241871, by rfl⟩ : syracuseStep 1289981 = 483743) (by norm_num)
theorem B765713 : Blo 603293 765713 := bbase (se 2 (by rfl) ⟨287142, by rfl⟩ : syracuseStep 765713 = 574285) (by norm_num)
theorem B765769 : Blo 603293 765769 := bbase (se 2 (by rfl) ⟨287163, by rfl⟩ : syracuseStep 765769 = 574327) (by norm_num)
theorem B1290125 : Blo 603293 1290125 := bbase (se 3 (by rfl) ⟨241898, by rfl⟩ : syracuseStep 1290125 = 483797) (by norm_num)
theorem B765865 : Blo 603293 765865 := bbase (se 2 (by rfl) ⟨287199, by rfl⟩ : syracuseStep 765865 = 574399) (by norm_num)
theorem B2043845 : Blo 603293 2043845 := bbase (se 4 (by rfl) ⟨191610, by rfl⟩ : syracuseStep 2043845 = 383221) (by norm_num)
theorem B766037 : Blo 603293 766037 := bbase (se 8 (by rfl) ⟨4488, by rfl⟩ : syracuseStep 766037 = 8977) (by norm_num)
theorem B864389 : Blo 603293 864389 := bbase (se 4 (by rfl) ⟨81036, by rfl⟩ : syracuseStep 864389 = 162073) (by norm_num)
theorem B766093 : Blo 603293 766093 := bbase (se 3 (by rfl) ⟨143642, by rfl⟩ : syracuseStep 766093 = 287285) (by norm_num)
theorem B1454237 : Blo 603293 1454237 := bbase (se 3 (by rfl) ⟨272669, by rfl⟩ : syracuseStep 1454237 = 545339) (by norm_num)
theorem B4599989 : Blo 603293 4599989 := bbase (se 5 (by rfl) ⟨215624, by rfl⟩ : syracuseStep 4599989 = 431249) (by norm_num)
theorem B864469 : Blo 603293 864469 := bbase (se 7 (by rfl) ⟨10130, by rfl⟩ : syracuseStep 864469 = 20261) (by norm_num)
theorem B766189 : Blo 603293 766189 := bbase (se 3 (by rfl) ⟨143660, by rfl⟩ : syracuseStep 766189 = 287321) (by norm_num)
theorem B1290485 : Blo 603293 1290485 := bbase (se 5 (by rfl) ⟨60491, by rfl⟩ : syracuseStep 1290485 = 120983) (by norm_num)
theorem B864589 : Blo 603293 864589 := bbase (se 3 (by rfl) ⟨162110, by rfl⟩ : syracuseStep 864589 = 324221) (by norm_num)
theorem B2044277 : Blo 603293 2044277 := bbase (se 5 (by rfl) ⟨95825, by rfl⟩ : syracuseStep 2044277 = 191651) (by norm_num)
theorem B766361 : Blo 603293 766361 := bbase (se 2 (by rfl) ⟨287385, by rfl⟩ : syracuseStep 766361 = 574771) (by norm_num)
theorem B766417 : Blo 603293 766417 := bbase (se 2 (by rfl) ⟨287406, by rfl⟩ : syracuseStep 766417 = 574813) (by norm_num)
theorem B766513 : Blo 603293 766513 := bbase (se 2 (by rfl) ⟨287442, by rfl⟩ : syracuseStep 766513 = 574885) (by norm_num)
theorem B9810517 : Blo 603293 9810517 := bbase (se 8 (by rfl) ⟨57483, by rfl⟩ : syracuseStep 9810517 = 114967) (by norm_num)
theorem B1225325 : Blo 603293 1225325 := bbase (se 3 (by rfl) ⟨229748, by rfl⟩ : syracuseStep 1225325 = 459497) (by norm_num)
theorem B3060341 : Blo 603293 3060341 := bbase (se 5 (by rfl) ⟨143453, by rfl⟩ : syracuseStep 3060341 = 286907) (by norm_num)
theorem B1454765 : Blo 603293 1454765 := bbase (se 3 (by rfl) ⟨272768, by rfl⟩ : syracuseStep 1454765 = 545537) (by norm_num)
theorem B766657 : Blo 603293 766657 := bbase (se 2 (by rfl) ⟨287496, by rfl⟩ : syracuseStep 766657 = 574993) (by norm_num)
theorem B766685 : Blo 603293 766685 := bbase (se 3 (by rfl) ⟨143753, by rfl⟩ : syracuseStep 766685 = 287507) (by norm_num)
theorem B766741 : Blo 603293 766741 := bbase (se 6 (by rfl) ⟨17970, by rfl⟩ : syracuseStep 766741 = 35941) (by norm_num)
theorem B2044709 : Blo 603293 2044709 := bbase (se 4 (by rfl) ⟨191691, by rfl⟩ : syracuseStep 2044709 = 383383) (by norm_num)
theorem B2274149 : Blo 603293 2274149 := bbase (se 4 (by rfl) ⟨213201, by rfl⟩ : syracuseStep 2274149 = 426403) (by norm_num)
theorem B766837 : Blo 603293 766837 := bbase (se 5 (by rfl) ⟨35945, by rfl⟩ : syracuseStep 766837 = 71891) (by norm_num)
theorem B1455005 : Blo 603293 1455005 := bbase (se 3 (by rfl) ⟨272813, by rfl⟩ : syracuseStep 1455005 = 545627) (by norm_num)
theorem B767009 : Blo 603293 767009 := bbase (se 2 (by rfl) ⟨287628, by rfl⟩ : syracuseStep 767009 = 575257) (by norm_num)
theorem B767065 : Blo 603293 767065 := bbase (se 2 (by rfl) ⟨287649, by rfl⟩ : syracuseStep 767065 = 575299) (by norm_num)
theorem B1291373 : Blo 603293 1291373 := bbase (se 3 (by rfl) ⟨242132, by rfl⟩ : syracuseStep 1291373 = 484265) (by norm_num)
theorem B767161 : Blo 603293 767161 := bbase (se 2 (by rfl) ⟨287685, by rfl⟩ : syracuseStep 767161 = 575371) (by norm_num)
theorem B2045141 : Blo 603293 2045141 := bbase (se 7 (by rfl) ⟨23966, by rfl⟩ : syracuseStep 2045141 = 47933) (by norm_num)
theorem B1291621 : Blo 603293 1291621 := bbase (se 4 (by rfl) ⟨121089, by rfl⟩ : syracuseStep 1291621 = 242179) (by norm_num)
theorem B767333 : Blo 603293 767333 := bbase (se 4 (by rfl) ⟨71937, by rfl⟩ : syracuseStep 767333 = 143875) (by norm_num)
theorem B767389 : Blo 603293 767389 := bbase (se 3 (by rfl) ⟨143885, by rfl⟩ : syracuseStep 767389 = 287771) (by norm_num)
theorem B767485 : Blo 603293 767485 := bbase (se 3 (by rfl) ⟨143903, by rfl⟩ : syracuseStep 767485 = 287807) (by norm_num)
theorem B1226357 : Blo 603293 1226357 := bbase (se 5 (by rfl) ⟨57485, by rfl⟩ : syracuseStep 1226357 = 114971) (by norm_num)
theorem B2045573 : Blo 603293 2045573 := bbase (se 4 (by rfl) ⟨191772, by rfl⟩ : syracuseStep 2045573 = 383545) (by norm_num)
theorem B1357469 : Blo 603293 1357469 := bbase (se 3 (by rfl) ⟨254525, by rfl⟩ : syracuseStep 1357469 = 509051) (by norm_num)
theorem B767657 : Blo 603293 767657 := bbase (se 2 (by rfl) ⟨287871, by rfl⟩ : syracuseStep 767657 = 575743) (by norm_num)
theorem B1226429 : Blo 603293 1226429 := bbase (se 3 (by rfl) ⟨229955, by rfl⟩ : syracuseStep 1226429 = 459911) (by norm_num)
theorem B767713 : Blo 603293 767713 := bbase (se 2 (by rfl) ⟨287892, by rfl⟩ : syracuseStep 767713 = 575785) (by norm_num)
theorem B1357541 : Blo 603293 1357541 := bbase (se 4 (by rfl) ⟨127269, by rfl⟩ : syracuseStep 1357541 = 254539) (by norm_num)
theorem B1357613 : Blo 603293 1357613 := bbase (se 3 (by rfl) ⟨254552, by rfl⟩ : syracuseStep 1357613 = 509105) (by norm_num)
theorem B767809 : Blo 603293 767809 := bbase (se 2 (by rfl) ⟨287928, by rfl⟩ : syracuseStep 767809 = 575857) (by norm_num)
theorem B1292125 : Blo 603293 1292125 := bbase (se 3 (by rfl) ⟨242273, by rfl⟩ : syracuseStep 1292125 = 484547) (by norm_num)
theorem B1718117 : Blo 603293 1718117 := bbase (se 4 (by rfl) ⟨161073, by rfl⟩ : syracuseStep 1718117 = 322147) (by norm_num)
theorem B1357685 : Blo 603293 1357685 := bbase (se 5 (by rfl) ⟨63641, by rfl⟩ : syracuseStep 1357685 = 127283) (by norm_num)
theorem B2176885 : Blo 603293 2176885 := bbase (se 5 (by rfl) ⟨102041, by rfl⟩ : syracuseStep 2176885 = 204083) (by norm_num)
theorem B3061637 : Blo 603293 3061637 := bbase (se 4 (by rfl) ⟨287028, by rfl⟩ : syracuseStep 3061637 = 574057) (by norm_num)
theorem B1161101 : Blo 603293 1161101 := bbase (se 3 (by rfl) ⟨217706, by rfl⟩ : syracuseStep 1161101 = 435413) (by norm_num)
theorem B1357757 : Blo 603293 1357757 := bbase (se 3 (by rfl) ⟨254579, by rfl⟩ : syracuseStep 1357757 = 509159) (by norm_num)
theorem B767981 : Blo 603293 767981 := bbase (se 3 (by rfl) ⟨143996, by rfl⟩ : syracuseStep 767981 = 287993) (by norm_num)
theorem B1357829 : Blo 603293 1357829 := bbase (se 4 (by rfl) ⟨127296, by rfl⟩ : syracuseStep 1357829 = 254593) (by norm_num)
theorem B768037 : Blo 603293 768037 := bbase (se 4 (by rfl) ⟨72003, by rfl⟩ : syracuseStep 768037 = 144007) (by norm_num)
theorem B2046005 : Blo 603293 2046005 := bbase (se 5 (by rfl) ⟨95906, by rfl⟩ : syracuseStep 2046005 = 191813) (by norm_num)
theorem B1357901 : Blo 603293 1357901 := bbase (se 3 (by rfl) ⟨254606, by rfl⟩ : syracuseStep 1357901 = 509213) (by norm_num)
theorem B5158997 : Blo 603293 5158997 := bbase (se 8 (by rfl) ⟨30228, by rfl⟩ : syracuseStep 5158997 = 60457) (by norm_num)
theorem B768133 : Blo 603293 768133 := bbase (se 4 (by rfl) ⟨72012, by rfl⟩ : syracuseStep 768133 = 144025) (by norm_num)
theorem B1357973 : Blo 603293 1357973 := bbase (se 6 (by rfl) ⟨31827, by rfl⟩ : syracuseStep 1357973 = 63655) (by norm_num)
theorem B3881141 : Blo 603293 3881141 := bbase (se 5 (by rfl) ⟨181928, by rfl⟩ : syracuseStep 3881141 = 363857) (by norm_num)
theorem B735437 : Blo 603293 735437 := bbase (se 3 (by rfl) ⟨137894, by rfl⟩ : syracuseStep 735437 = 275789) (by norm_num)
theorem B1358045 : Blo 603293 1358045 := bbase (se 3 (by rfl) ⟨254633, by rfl⟩ : syracuseStep 1358045 = 509267) (by norm_num)
theorem B1358117 : Blo 603293 1358117 := bbase (se 4 (by rfl) ⟨127323, by rfl⟩ : syracuseStep 1358117 = 254647) (by norm_num)
theorem B768305 : Blo 603293 768305 := bbase (se 2 (by rfl) ⟨288114, by rfl⟩ : syracuseStep 768305 = 576229) (by norm_num)
theorem B768361 : Blo 603293 768361 := bbase (se 2 (by rfl) ⟨288135, by rfl⟩ : syracuseStep 768361 = 576271) (by norm_num)
theorem B1358189 : Blo 603293 1358189 := bbase (se 3 (by rfl) ⟨254660, by rfl⟩ : syracuseStep 1358189 = 509321) (by norm_num)
theorem B1358261 : Blo 603293 1358261 := bbase (se 5 (by rfl) ⟨63668, by rfl⟩ : syracuseStep 1358261 = 127337) (by norm_num)
theorem B768457 : Blo 603293 768457 := bbase (se 2 (by rfl) ⟨288171, by rfl⟩ : syracuseStep 768457 = 576343) (by norm_num)
theorem B2046437 : Blo 603293 2046437 := bbase (se 4 (by rfl) ⟨191853, by rfl⟩ : syracuseStep 2046437 = 383707) (by norm_num)
theorem B1358333 : Blo 603293 1358333 := bbase (se 3 (by rfl) ⟨254687, by rfl⟩ : syracuseStep 1358333 = 509375) (by norm_num)
theorem B1358405 : Blo 603293 1358405 := bbase (se 4 (by rfl) ⟨127350, by rfl⟩ : syracuseStep 1358405 = 254701) (by norm_num)
theorem B1456717 : Blo 603293 1456717 := bbase (se 3 (by rfl) ⟨273134, by rfl⟩ : syracuseStep 1456717 = 546269) (by norm_num)
theorem B1358477 : Blo 603293 1358477 := bbase (se 3 (by rfl) ⟨254714, by rfl⟩ : syracuseStep 1358477 = 509429) (by norm_num)
theorem B1358549 : Blo 603293 1358549 := bbase (se 7 (by rfl) ⟨15920, by rfl⟩ : syracuseStep 1358549 = 31841) (by norm_num)
theorem B1293013 : Blo 603293 1293013 := bbase (se 7 (by rfl) ⟨15152, by rfl⟩ : syracuseStep 1293013 = 30305) (by norm_num)
theorem B1358621 : Blo 603293 1358621 := bbase (se 3 (by rfl) ⟨254741, by rfl⟩ : syracuseStep 1358621 = 509483) (by norm_num)
theorem B1358693 : Blo 603293 1358693 := bbase (se 4 (by rfl) ⟨127377, by rfl⟩ : syracuseStep 1358693 = 254755) (by norm_num)
theorem B1162117 : Blo 603293 1162117 := bbase (se 4 (by rfl) ⟨108948, by rfl⟩ : syracuseStep 1162117 = 217897) (by norm_num)
theorem B2046869 : Blo 603293 2046869 := bbase (se 6 (by rfl) ⟨47973, by rfl⟩ : syracuseStep 2046869 = 95947) (by norm_num)
theorem B1358765 : Blo 603293 1358765 := bbase (se 3 (by rfl) ⟨254768, by rfl⟩ : syracuseStep 1358765 = 509537) (by norm_num)
theorem B1358837 : Blo 603293 1358837 := bbase (se 5 (by rfl) ⟨63695, by rfl⟩ : syracuseStep 1358837 = 127391) (by norm_num)
theorem B1719301 : Blo 603293 1719301 := bbase (se 4 (by rfl) ⟨161184, by rfl⟩ : syracuseStep 1719301 = 322369) (by norm_num)
theorem B3456053 : Blo 603293 3456053 := bbase (se 5 (by rfl) ⟨162002, by rfl⟩ : syracuseStep 3456053 = 324005) (by norm_num)
theorem B1358909 : Blo 603293 1358909 := bbase (se 3 (by rfl) ⟨254795, by rfl⟩ : syracuseStep 1358909 = 509591) (by norm_num)
theorem B736337 : Blo 603293 736337 := bbase (se 2 (by rfl) ⟨276126, by rfl⟩ : syracuseStep 736337 = 552253) (by norm_num)
theorem B1358981 : Blo 603293 1358981 := bbase (se 4 (by rfl) ⟨127404, by rfl⟩ : syracuseStep 1358981 = 254809) (by norm_num)
theorem B3062933 : Blo 603293 3062933 := bbase (se 6 (by rfl) ⟨71787, by rfl⟩ : syracuseStep 3062933 = 143575) (by norm_num)
theorem B1719461 : Blo 603293 1719461 := bbase (se 4 (by rfl) ⟨161199, by rfl⟩ : syracuseStep 1719461 = 322399) (by norm_num)
theorem B1293509 : Blo 603293 1293509 := bbase (se 4 (by rfl) ⟨121266, by rfl⟩ : syracuseStep 1293509 = 242533) (by norm_num)
theorem B1359053 : Blo 603293 1359053 := bbase (se 3 (by rfl) ⟨254822, by rfl⟩ : syracuseStep 1359053 = 509645) (by norm_num)
theorem B1359125 : Blo 603293 1359125 := bbase (se 6 (by rfl) ⟨31854, by rfl⟩ : syracuseStep 1359125 = 63709) (by norm_num)
theorem B2047301 : Blo 603293 2047301 := bbase (se 4 (by rfl) ⟨191934, by rfl⟩ : syracuseStep 2047301 = 383869) (by norm_num)
theorem B1359197 : Blo 603293 1359197 := bbase (se 3 (by rfl) ⟨254849, by rfl⟩ : syracuseStep 1359197 = 509699) (by norm_num)
theorem B1719701 : Blo 603293 1719701 := bbase (se 6 (by rfl) ⟨40305, by rfl⟩ : syracuseStep 1719701 = 80611) (by norm_num)
theorem B1359269 : Blo 603293 1359269 := bbase (se 4 (by rfl) ⟨127431, by rfl⟩ : syracuseStep 1359269 = 254863) (by norm_num)
theorem B1359341 : Blo 603293 1359341 := bbase (se 3 (by rfl) ⟨254876, by rfl⟩ : syracuseStep 1359341 = 509753) (by norm_num)
theorem B1359413 : Blo 603293 1359413 := bbase (se 5 (by rfl) ⟨63722, by rfl⟩ : syracuseStep 1359413 = 127445) (by norm_num)
theorem B1719893 : Blo 603293 1719893 := bbase (se 8 (by rfl) ⟨10077, by rfl⟩ : syracuseStep 1719893 = 20155) (by norm_num)
theorem B1359485 : Blo 603293 1359485 := bbase (se 3 (by rfl) ⟨254903, by rfl⟩ : syracuseStep 1359485 = 509807) (by norm_num)
theorem B1359557 : Blo 603293 1359557 := bbase (se 4 (by rfl) ⟨127458, by rfl⟩ : syracuseStep 1359557 = 254917) (by norm_num)
theorem B2047733 : Blo 603293 2047733 := bbase (se 5 (by rfl) ⟨95987, by rfl⟩ : syracuseStep 2047733 = 191975) (by norm_num)
theorem B1359629 : Blo 603293 1359629 := bbase (se 3 (by rfl) ⟨254930, by rfl⟩ : syracuseStep 1359629 = 509861) (by norm_num)
theorem B1359701 : Blo 603293 1359701 := bbase (se 9 (by rfl) ⟨3983, by rfl⟩ : syracuseStep 1359701 = 7967) (by norm_num)
theorem B3358549 : Blo 603293 3358549 := bbase (se 9 (by rfl) ⟨9839, by rfl⟩ : syracuseStep 3358549 = 19679) (by norm_num)
theorem B1359773 : Blo 603293 1359773 := bbase (se 3 (by rfl) ⟨254957, by rfl⟩ : syracuseStep 1359773 = 509915) (by norm_num)
theorem B1359845 : Blo 603293 1359845 := bbase (se 4 (by rfl) ⟨127485, by rfl⟩ : syracuseStep 1359845 = 254971) (by norm_num)
theorem B1458157 : Blo 603293 1458157 := bbase (se 3 (by rfl) ⟨273404, by rfl⟩ : syracuseStep 1458157 = 546809) (by norm_num)
theorem B1359917 : Blo 603293 1359917 := bbase (se 3 (by rfl) ⟨254984, by rfl⟩ : syracuseStep 1359917 = 509969) (by norm_num)
theorem B1294397 : Blo 603293 1294397 := bbase (se 3 (by rfl) ⟨242699, by rfl⟩ : syracuseStep 1294397 = 485399) (by norm_num)
theorem B2900053 : Blo 603293 2900053 := bbase (se 8 (by rfl) ⟨16992, by rfl⟩ : syracuseStep 2900053 = 33985) (by norm_num)
theorem B3686485 : Blo 603293 3686485 := bbase (se 8 (by rfl) ⟨21600, by rfl⟩ : syracuseStep 3686485 = 43201) (by norm_num)
theorem B1359989 : Blo 603293 1359989 := bbase (se 5 (by rfl) ⟨63749, by rfl⟩ : syracuseStep 1359989 = 127499) (by norm_num)
theorem B2048165 : Blo 603293 2048165 := bbase (se 4 (by rfl) ⟨192015, by rfl⟩ : syracuseStep 2048165 = 384031) (by norm_num)
theorem B1294517 : Blo 603293 1294517 := bbase (se 5 (by rfl) ⟨60680, by rfl⟩ : syracuseStep 1294517 = 121361) (by norm_num)
theorem B1360061 : Blo 603293 1360061 := bbase (se 3 (by rfl) ⟨255011, by rfl⟩ : syracuseStep 1360061 = 510023) (by norm_num)
theorem B1360133 : Blo 603293 1360133 := bbase (se 4 (by rfl) ⟨127512, by rfl⟩ : syracuseStep 1360133 = 255025) (by norm_num)
theorem B966973 : Blo 603293 966973 := bbase (se 3 (by rfl) ⟨181307, by rfl⟩ : syracuseStep 966973 = 362615) (by norm_num)
theorem B1360205 : Blo 603293 1360205 := bbase (se 3 (by rfl) ⟨255038, by rfl⟩ : syracuseStep 1360205 = 510077) (by norm_num)
theorem B1360277 : Blo 603293 1360277 := bbase (se 6 (by rfl) ⟨31881, by rfl⟩ : syracuseStep 1360277 = 63763) (by norm_num)
theorem B3064229 : Blo 603293 3064229 := bbase (se 4 (by rfl) ⟨287271, by rfl⟩ : syracuseStep 3064229 = 574543) (by norm_num)
theorem B1360349 : Blo 603293 1360349 := bbase (se 3 (by rfl) ⟨255065, by rfl⟩ : syracuseStep 1360349 = 510131) (by norm_num)
theorem B1360421 : Blo 603293 1360421 := bbase (se 4 (by rfl) ⟨127539, by rfl⟩ : syracuseStep 1360421 = 255079) (by norm_num)
theorem B1720885 : Blo 603293 1720885 := bbase (se 5 (by rfl) ⟨80666, by rfl⟩ : syracuseStep 1720885 = 161333) (by norm_num)
theorem B2048597 : Blo 603293 2048597 := bbase (se 8 (by rfl) ⟨12003, by rfl⟩ : syracuseStep 2048597 = 24007) (by norm_num)
theorem B1458773 : Blo 603293 1458773 := bbase (se 8 (by rfl) ⟨8547, by rfl⟩ : syracuseStep 1458773 = 17095) (by norm_num)
theorem B1229413 : Blo 603293 1229413 := bbase (se 4 (by rfl) ⟨115257, by rfl⟩ : syracuseStep 1229413 = 230515) (by norm_num)
theorem B1360493 : Blo 603293 1360493 := bbase (se 3 (by rfl) ⟨255092, by rfl⟩ : syracuseStep 1360493 = 510185) (by norm_num)
theorem B1360565 : Blo 603293 1360565 := bbase (se 5 (by rfl) ⟨63776, by rfl⟩ : syracuseStep 1360565 = 127553) (by norm_num)
theorem B1360637 : Blo 603293 1360637 := bbase (se 3 (by rfl) ⟨255119, by rfl⟩ : syracuseStep 1360637 = 510239) (by norm_num)
theorem B1458965 : Blo 603293 1458965 := bbase (se 6 (by rfl) ⟨34194, by rfl⟩ : syracuseStep 1458965 = 68389) (by norm_num)
theorem B1295149 : Blo 603293 1295149 := bbase (se 3 (by rfl) ⟨242840, by rfl⟩ : syracuseStep 1295149 = 485681) (by norm_num)
theorem B1360709 : Blo 603293 1360709 := bbase (se 4 (by rfl) ⟨127566, by rfl⟩ : syracuseStep 1360709 = 255133) (by norm_num)
theorem B1360781 : Blo 603293 1360781 := bbase (se 3 (by rfl) ⟨255146, by rfl⟩ : syracuseStep 1360781 = 510293) (by norm_num)
theorem B1360853 : Blo 603293 1360853 := bbase (se 7 (by rfl) ⟨15947, by rfl⟩ : syracuseStep 1360853 = 31895) (by norm_num)
theorem B967645 : Blo 603293 967645 := bbase (se 3 (by rfl) ⟨181433, by rfl⟩ : syracuseStep 967645 = 362867) (by norm_num)
theorem B2049029 : Blo 603293 2049029 := bbase (se 4 (by rfl) ⟨192096, by rfl⟩ : syracuseStep 2049029 = 384193) (by norm_num)
theorem B1360925 : Blo 603293 1360925 := bbase (se 3 (by rfl) ⟨255173, by rfl⟩ : syracuseStep 1360925 = 510347) (by norm_num)
theorem B1360997 : Blo 603293 1360997 := bbase (se 4 (by rfl) ⟨127593, by rfl⟩ : syracuseStep 1360997 = 255187) (by norm_num)
theorem B1361069 : Blo 603293 1361069 := bbase (se 3 (by rfl) ⟨255200, by rfl⟩ : syracuseStep 1361069 = 510401) (by norm_num)
theorem B1557701 : Blo 603293 1557701 := bbase (se 4 (by rfl) ⟨146034, by rfl⟩ : syracuseStep 1557701 = 292069) (by norm_num)
theorem B3261653 : Blo 603293 3261653 := bbase (se 7 (by rfl) ⟨38222, by rfl⟩ : syracuseStep 3261653 = 76445) (by norm_num)
theorem B5817557 : Blo 603293 5817557 := bbase (se 7 (by rfl) ⟨68174, by rfl⟩ : syracuseStep 5817557 = 136349) (by norm_num)
theorem B1361141 : Blo 603293 1361141 := bbase (se 5 (by rfl) ⟨63803, by rfl⟩ : syracuseStep 1361141 = 127607) (by norm_num)
theorem B1361213 : Blo 603293 1361213 := bbase (se 3 (by rfl) ⟨255227, by rfl⟩ : syracuseStep 1361213 = 510455) (by norm_num)
theorem B1033589 : Blo 603293 1033589 := bbase (se 5 (by rfl) ⟨48449, by rfl⟩ : syracuseStep 1033589 = 96899) (by norm_num)
theorem B1361285 : Blo 603293 1361285 := bbase (se 4 (by rfl) ⟨127620, by rfl⟩ : syracuseStep 1361285 = 255241) (by norm_num)
theorem B2049461 : Blo 603293 2049461 := bbase (se 5 (by rfl) ⟨96068, by rfl⟩ : syracuseStep 2049461 = 192137) (by norm_num)
theorem B1361357 : Blo 603293 1361357 := bbase (se 3 (by rfl) ⟨255254, by rfl⟩ : syracuseStep 1361357 = 510509) (by norm_num)
theorem B1361429 : Blo 603293 1361429 := bbase (se 6 (by rfl) ⟨31908, by rfl⟩ : syracuseStep 1361429 = 63817) (by norm_num)
theorem B1361501 : Blo 603293 1361501 := bbase (se 3 (by rfl) ⟨255281, by rfl⟩ : syracuseStep 1361501 = 510563) (by norm_num)
theorem B1721989 : Blo 603293 1721989 := bbase (se 4 (by rfl) ⟨161436, by rfl⟩ : syracuseStep 1721989 = 322873) (by norm_num)
theorem B1361573 : Blo 603293 1361573 := bbase (se 4 (by rfl) ⟨127647, by rfl⟩ : syracuseStep 1361573 = 255295) (by norm_num)
theorem B1296037 : Blo 603293 1296037 := bbase (se 4 (by rfl) ⟨121503, by rfl⟩ : syracuseStep 1296037 = 243007) (by norm_num)
theorem B4966069 : Blo 603293 4966069 := bbase (se 5 (by rfl) ⟨232784, by rfl⟩ : syracuseStep 4966069 = 465569) (by norm_num)
theorem B3065525 : Blo 603293 3065525 := bbase (se 5 (by rfl) ⟨143696, by rfl⟩ : syracuseStep 3065525 = 287393) (by norm_num)
theorem B1361645 : Blo 603293 1361645 := bbase (se 3 (by rfl) ⟨255308, by rfl⟩ : syracuseStep 1361645 = 510617) (by norm_num)
theorem B1296157 : Blo 603293 1296157 := bbase (se 3 (by rfl) ⟨243029, by rfl⟩ : syracuseStep 1296157 = 486059) (by norm_num)
theorem B1361717 : Blo 603293 1361717 := bbase (se 5 (by rfl) ⟨63830, by rfl⟩ : syracuseStep 1361717 = 127661) (by norm_num)
theorem B1361789 : Blo 603293 1361789 := bbase (se 3 (by rfl) ⟨255335, by rfl⟩ : syracuseStep 1361789 = 510671) (by norm_num)
theorem B968645 : Blo 603293 968645 := bbase (se 4 (by rfl) ⟨90810, by rfl⟩ : syracuseStep 968645 = 181621) (by norm_num)
theorem B1361861 : Blo 603293 1361861 := bbase (se 4 (by rfl) ⟨127674, by rfl⟩ : syracuseStep 1361861 = 255349) (by norm_num)
theorem B1361933 : Blo 603293 1361933 := bbase (se 3 (by rfl) ⟨255362, by rfl⟩ : syracuseStep 1361933 = 510725) (by norm_num)
theorem B1296413 : Blo 603293 1296413 := bbase (se 3 (by rfl) ⟨243077, by rfl⟩ : syracuseStep 1296413 = 486155) (by norm_num)
theorem B1362005 : Blo 603293 1362005 := bbase (se 8 (by rfl) ⟨7980, by rfl⟩ : syracuseStep 1362005 = 15961) (by norm_num)
theorem B1362077 : Blo 603293 1362077 := bbase (se 3 (by rfl) ⟨255389, by rfl⟩ : syracuseStep 1362077 = 510779) (by norm_num)
theorem B1362149 : Blo 603293 1362149 := bbase (se 4 (by rfl) ⟨127701, by rfl⟩ : syracuseStep 1362149 = 255403) (by norm_num)
theorem B1362221 : Blo 603293 1362221 := bbase (se 3 (by rfl) ⟨255416, by rfl⟩ : syracuseStep 1362221 = 510833) (by norm_num)
theorem B1362293 : Blo 603293 1362293 := bbase (se 5 (by rfl) ⟨63857, by rfl⟩ : syracuseStep 1362293 = 127715) (by norm_num)
theorem B1362365 : Blo 603293 1362365 := bbase (se 3 (by rfl) ⟨255443, by rfl⟩ : syracuseStep 1362365 = 510887) (by norm_num)
theorem B1362437 : Blo 603293 1362437 := bbase (se 4 (by rfl) ⟨127728, by rfl⟩ : syracuseStep 1362437 = 255457) (by norm_num)
theorem B1362509 : Blo 603293 1362509 := bbase (se 3 (by rfl) ⟨255470, by rfl⟩ : syracuseStep 1362509 = 510941) (by norm_num)
theorem B3263125 : Blo 603293 3263125 := bbase (se 6 (by rfl) ⟨76479, by rfl⟩ : syracuseStep 3263125 = 152959) (by norm_num)
theorem B1362581 : Blo 603293 1362581 := bbase (se 6 (by rfl) ⟨31935, by rfl⟩ : syracuseStep 1362581 = 63871) (by norm_num)
theorem B1362653 : Blo 603293 1362653 := bbase (se 3 (by rfl) ⟨255497, by rfl⟩ : syracuseStep 1362653 = 510995) (by norm_num)
theorem B1362725 : Blo 603293 1362725 := bbase (se 4 (by rfl) ⟨127755, by rfl⟩ : syracuseStep 1362725 = 255511) (by norm_num)
theorem B1362797 : Blo 603293 1362797 := bbase (se 3 (by rfl) ⟨255524, by rfl⟩ : syracuseStep 1362797 = 511049) (by norm_num)
theorem B3263381 : Blo 603293 3263381 := bbase (se 6 (by rfl) ⟨76485, by rfl⟩ : syracuseStep 3263381 = 152971) (by norm_num)
theorem B1362869 : Blo 603293 1362869 := bbase (se 5 (by rfl) ⟨63884, by rfl⟩ : syracuseStep 1362869 = 127769) (by norm_num)
theorem B3066821 : Blo 603293 3066821 := bbase (se 4 (by rfl) ⟨287514, by rfl⟩ : syracuseStep 3066821 = 575029) (by norm_num)
theorem B1362941 : Blo 603293 1362941 := bbase (se 3 (by rfl) ⟨255551, by rfl⟩ : syracuseStep 1362941 = 511103) (by norm_num)
theorem B1363013 : Blo 603293 1363013 := bbase (se 4 (by rfl) ⟨127782, by rfl⟩ : syracuseStep 1363013 = 255565) (by norm_num)
theorem B1723493 : Blo 603293 1723493 := bbase (se 4 (by rfl) ⟨161577, by rfl⟩ : syracuseStep 1723493 = 323155) (by norm_num)
theorem B2182277 : Blo 603293 2182277 := bbase (se 4 (by rfl) ⟨204588, by rfl⟩ : syracuseStep 2182277 = 409177) (by norm_num)
theorem B1363085 : Blo 603293 1363085 := bbase (se 3 (by rfl) ⟨255578, by rfl⟩ : syracuseStep 1363085 = 511157) (by norm_num)
theorem B1363157 : Blo 603293 1363157 := bbase (se 7 (by rfl) ⟨15974, by rfl⟩ : syracuseStep 1363157 = 31949) (by norm_num)
theorem B2182421 : Blo 603293 2182421 := bbase (se 6 (by rfl) ⟨51150, by rfl⟩ : syracuseStep 2182421 = 102301) (by norm_num)
theorem B1363229 : Blo 603293 1363229 := bbase (se 3 (by rfl) ⟨255605, by rfl⟩ : syracuseStep 1363229 = 511211) (by norm_num)
theorem B5918005 : Blo 603293 5918005 := bbase (se 5 (by rfl) ⟨277406, by rfl⟩ : syracuseStep 5918005 = 554813) (by norm_num)
theorem B1527133 : Blo 603293 1527133 := bbase (se 3 (by rfl) ⟨286337, by rfl⟩ : syracuseStep 1527133 = 572675) (by norm_num)
theorem B1363301 : Blo 603293 1363301 := bbase (se 4 (by rfl) ⟨127809, by rfl⟩ : syracuseStep 1363301 = 255619) (by norm_num)
theorem B970157 : Blo 603293 970157 := bbase (se 3 (by rfl) ⟨181904, by rfl⟩ : syracuseStep 970157 = 363809) (by norm_num)
theorem B1363373 : Blo 603293 1363373 := bbase (se 3 (by rfl) ⟨255632, by rfl⟩ : syracuseStep 1363373 = 511265) (by norm_num)
theorem B1527245 : Blo 603293 1527245 := bbase (se 3 (by rfl) ⟨286358, by rfl⟩ : syracuseStep 1527245 = 572717) (by norm_num)
theorem B1363445 : Blo 603293 1363445 := bbase (se 5 (by rfl) ⟨63911, by rfl⟩ : syracuseStep 1363445 = 127823) (by norm_num)
theorem B1363517 : Blo 603293 1363517 := bbase (se 3 (by rfl) ⟨255659, by rfl⟩ : syracuseStep 1363517 = 511319) (by norm_num)
theorem B1330805 : Blo 603293 1330805 := bbase (se 5 (by rfl) ⟨62381, by rfl⟩ : syracuseStep 1330805 = 124763) (by norm_num)
theorem B1363589 : Blo 603293 1363589 := bbase (se 4 (by rfl) ⟨127836, by rfl⟩ : syracuseStep 1363589 = 255673) (by norm_num)
theorem B1527437 : Blo 603293 1527437 := bbase (se 3 (by rfl) ⟨286394, by rfl⟩ : syracuseStep 1527437 = 572789) (by norm_num)
theorem B1035949 : Blo 603293 1035949 := bbase (se 3 (by rfl) ⟨194240, by rfl⟩ : syracuseStep 1035949 = 388481) (by norm_num)
theorem B1363661 : Blo 603293 1363661 := bbase (se 3 (by rfl) ⟨255686, by rfl⟩ : syracuseStep 1363661 = 511373) (by norm_num)
theorem B904949 : Blo 603293 904949 := bbase (se 5 (by rfl) ⟨42419, by rfl⟩ : syracuseStep 904949 = 84839) (by norm_num)
theorem B2838277 : Blo 603293 2838277 := bbase (se 4 (by rfl) ⟨266088, by rfl⟩ : syracuseStep 2838277 = 532177) (by norm_num)
theorem B904973 : Blo 603293 904973 := bbase (se 3 (by rfl) ⟨169682, by rfl⟩ : syracuseStep 904973 = 339365) (by norm_num)
theorem B1363733 : Blo 603293 1363733 := bbase (se 6 (by rfl) ⟨31962, by rfl⟩ : syracuseStep 1363733 = 63925) (by norm_num)
theorem B4607765 : Blo 603293 4607765 := bbase (se 6 (by rfl) ⟨107994, by rfl⟩ : syracuseStep 4607765 = 215989) (by norm_num)
theorem B904997 : Blo 603293 904997 := bbase (se 4 (by rfl) ⟨84843, by rfl⟩ : syracuseStep 904997 = 169687) (by norm_num)
theorem B905021 : Blo 603293 905021 := bbase (se 3 (by rfl) ⟨169691, by rfl⟩ : syracuseStep 905021 = 339383) (by norm_num)
theorem B773965 : Blo 603293 773965 := bbase (se 3 (by rfl) ⟨145118, by rfl⟩ : syracuseStep 773965 = 290237) (by norm_num)
theorem B905045 : Blo 603293 905045 := bbase (se 9 (by rfl) ⟨2651, by rfl⟩ : syracuseStep 905045 = 5303) (by norm_num)
theorem B1363805 : Blo 603293 1363805 := bbase (se 3 (by rfl) ⟨255713, by rfl⟩ : syracuseStep 1363805 = 511427) (by norm_num)
theorem B905069 : Blo 603293 905069 := bbase (se 3 (by rfl) ⟨169700, by rfl⟩ : syracuseStep 905069 = 339401) (by norm_num)
theorem B970613 : Blo 603293 970613 := bbase (se 5 (by rfl) ⟨45497, by rfl⟩ : syracuseStep 970613 = 90995) (by norm_num)
theorem B905093 : Blo 603293 905093 := bbase (se 4 (by rfl) ⟨84852, by rfl⟩ : syracuseStep 905093 = 169705) (by norm_num)
theorem B905117 : Blo 603293 905117 := bbase (se 3 (by rfl) ⟨169709, by rfl⟩ : syracuseStep 905117 = 339419) (by norm_num)
theorem B1363877 : Blo 603293 1363877 := bbase (se 4 (by rfl) ⟨127863, by rfl⟩ : syracuseStep 1363877 = 255727) (by norm_num)
theorem B905141 : Blo 603293 905141 := bbase (se 5 (by rfl) ⟨42428, by rfl⟩ : syracuseStep 905141 = 84857) (by norm_num)
theorem B905165 : Blo 603293 905165 := bbase (se 3 (by rfl) ⟨169718, by rfl⟩ : syracuseStep 905165 = 339437) (by norm_num)
theorem B905189 : Blo 603293 905189 := bbase (se 4 (by rfl) ⟨84861, by rfl⟩ : syracuseStep 905189 = 169723) (by norm_num)
theorem B1527781 : Blo 603293 1527781 := bbase (se 4 (by rfl) ⟨143229, by rfl⟩ : syracuseStep 1527781 = 286459) (by norm_num)
theorem B1363949 : Blo 603293 1363949 := bbase (se 3 (by rfl) ⟨255740, by rfl⟩ : syracuseStep 1363949 = 511481) (by norm_num)
theorem B905213 : Blo 603293 905213 := bbase (se 3 (by rfl) ⟨169727, by rfl⟩ : syracuseStep 905213 = 339455) (by norm_num)
theorem B905237 : Blo 603293 905237 := bbase (se 6 (by rfl) ⟨21216, by rfl⟩ : syracuseStep 905237 = 42433) (by norm_num)
theorem B774181 : Blo 603293 774181 := bbase (se 4 (by rfl) ⟨72579, by rfl⟩ : syracuseStep 774181 = 145159) (by norm_num)
theorem B905261 : Blo 603293 905261 := bbase (se 3 (by rfl) ⟨169736, by rfl⟩ : syracuseStep 905261 = 339473) (by norm_num)
theorem B1364021 : Blo 603293 1364021 := bbase (se 5 (by rfl) ⟨63938, by rfl⟩ : syracuseStep 1364021 = 127877) (by norm_num)
theorem B905285 : Blo 603293 905285 := bbase (se 4 (by rfl) ⟨84870, by rfl⟩ : syracuseStep 905285 = 169741) (by norm_num)
theorem B1527893 : Blo 603293 1527893 := bbase (se 8 (by rfl) ⟨8952, by rfl⟩ : syracuseStep 1527893 = 17905) (by norm_num)
theorem B3887189 : Blo 603293 3887189 := bbase (se 8 (by rfl) ⟨22776, by rfl⟩ : syracuseStep 3887189 = 45553) (by norm_num)
theorem B905309 : Blo 603293 905309 := bbase (se 3 (by rfl) ⟨169745, by rfl⟩ : syracuseStep 905309 = 339491) (by norm_num)
theorem B905333 : Blo 603293 905333 := bbase (se 5 (by rfl) ⟨42437, by rfl⟩ : syracuseStep 905333 = 84875) (by norm_num)
theorem B1364093 : Blo 603293 1364093 := bbase (se 3 (by rfl) ⟨255767, by rfl⟩ : syracuseStep 1364093 = 511535) (by norm_num)
theorem B905357 : Blo 603293 905357 := bbase (se 3 (by rfl) ⟨169754, by rfl⟩ : syracuseStep 905357 = 339509) (by norm_num)
theorem B774293 : Blo 603293 774293 := bbase (se 6 (by rfl) ⟨18147, by rfl⟩ : syracuseStep 774293 = 36295) (by norm_num)
theorem B905381 : Blo 603293 905381 := bbase (se 4 (by rfl) ⟨84879, by rfl⟩ : syracuseStep 905381 = 169759) (by norm_num)
theorem B2904245 : Blo 603293 2904245 := bbase (se 5 (by rfl) ⟨136136, by rfl⟩ : syracuseStep 2904245 = 272273) (by norm_num)
theorem B905405 : Blo 603293 905405 := bbase (se 3 (by rfl) ⟨169763, by rfl⟩ : syracuseStep 905405 = 339527) (by norm_num)
theorem B1364165 : Blo 603293 1364165 := bbase (se 4 (by rfl) ⟨127890, by rfl⟩ : syracuseStep 1364165 = 255781) (by norm_num)
theorem B905429 : Blo 603293 905429 := bbase (se 7 (by rfl) ⟨10610, by rfl⟩ : syracuseStep 905429 = 21221) (by norm_num)
theorem B3068117 : Blo 603293 3068117 := bbase (se 7 (by rfl) ⟨35954, by rfl⟩ : syracuseStep 3068117 = 71909) (by norm_num)
theorem B905453 : Blo 603293 905453 := bbase (se 3 (by rfl) ⟨169772, by rfl⟩ : syracuseStep 905453 = 339545) (by norm_num)
theorem B905477 : Blo 603293 905477 := bbase (se 4 (by rfl) ⟨84888, by rfl⟩ : syracuseStep 905477 = 169777) (by norm_num)
theorem B1364237 : Blo 603293 1364237 := bbase (se 3 (by rfl) ⟨255794, by rfl⟩ : syracuseStep 1364237 = 511589) (by norm_num)
theorem B1528085 : Blo 603293 1528085 := bbase (se 6 (by rfl) ⟨35814, by rfl⟩ : syracuseStep 1528085 = 71629) (by norm_num)
theorem B905501 : Blo 603293 905501 := bbase (se 3 (by rfl) ⟨169781, by rfl⟩ : syracuseStep 905501 = 339563) (by norm_num)
theorem B905525 : Blo 603293 905525 := bbase (se 5 (by rfl) ⟨42446, by rfl⟩ : syracuseStep 905525 = 84893) (by norm_num)
theorem B905549 : Blo 603293 905549 := bbase (se 3 (by rfl) ⟨169790, by rfl⟩ : syracuseStep 905549 = 339581) (by norm_num)
theorem B1364309 : Blo 603293 1364309 := bbase (se 10 (by rfl) ⟨1998, by rfl⟩ : syracuseStep 1364309 = 3997) (by norm_num)
theorem B905573 : Blo 603293 905573 := bbase (se 4 (by rfl) ⟨84897, by rfl⟩ : syracuseStep 905573 = 169795) (by norm_num)
theorem B905597 : Blo 603293 905597 := bbase (se 3 (by rfl) ⟨169799, by rfl⟩ : syracuseStep 905597 = 339599) (by norm_num)
theorem B905621 : Blo 603293 905621 := bbase (se 6 (by rfl) ⟨21225, by rfl⟩ : syracuseStep 905621 = 42451) (by norm_num)
theorem B1364381 : Blo 603293 1364381 := bbase (se 3 (by rfl) ⟨255821, by rfl⟩ : syracuseStep 1364381 = 511643) (by norm_num)
theorem B905645 : Blo 603293 905645 := bbase (se 3 (by rfl) ⟨169808, by rfl⟩ : syracuseStep 905645 = 339617) (by norm_num)
theorem B905669 : Blo 603293 905669 := bbase (se 4 (by rfl) ⟨84906, by rfl⟩ : syracuseStep 905669 = 169813) (by norm_num)
theorem B905693 : Blo 603293 905693 := bbase (se 3 (by rfl) ⟨169817, by rfl⟩ : syracuseStep 905693 = 339635) (by norm_num)
theorem B1364453 : Blo 603293 1364453 := bbase (se 4 (by rfl) ⟨127917, by rfl⟩ : syracuseStep 1364453 = 255835) (by norm_num)
theorem B905717 : Blo 603293 905717 := bbase (se 5 (by rfl) ⟨42455, by rfl⟩ : syracuseStep 905717 = 84911) (by norm_num)
theorem B905741 : Blo 603293 905741 := bbase (se 3 (by rfl) ⟨169826, by rfl⟩ : syracuseStep 905741 = 339653) (by norm_num)
theorem B905765 : Blo 603293 905765 := bbase (se 4 (by rfl) ⟨84915, by rfl⟩ : syracuseStep 905765 = 169831) (by norm_num)
theorem B1364525 : Blo 603293 1364525 := bbase (se 3 (by rfl) ⟨255848, by rfl⟩ : syracuseStep 1364525 = 511697) (by norm_num)
theorem B905789 : Blo 603293 905789 := bbase (se 3 (by rfl) ⟨169835, by rfl⟩ : syracuseStep 905789 = 339671) (by norm_num)
theorem B905813 : Blo 603293 905813 := bbase (se 8 (by rfl) ⟨5307, by rfl⟩ : syracuseStep 905813 = 10615) (by norm_num)
theorem B1528429 : Blo 603293 1528429 := bbase (se 3 (by rfl) ⟨286580, by rfl⟩ : syracuseStep 1528429 = 573161) (by norm_num)
theorem B905837 : Blo 603293 905837 := bbase (se 3 (by rfl) ⟨169844, by rfl⟩ : syracuseStep 905837 = 339689) (by norm_num)
theorem B1364597 : Blo 603293 1364597 := bbase (se 5 (by rfl) ⟨63965, by rfl⟩ : syracuseStep 1364597 = 127931) (by norm_num)
theorem B905861 : Blo 603293 905861 := bbase (se 4 (by rfl) ⟨84924, by rfl⟩ : syracuseStep 905861 = 169849) (by norm_num)
theorem B1725077 : Blo 603293 1725077 := bbase (se 6 (by rfl) ⟨40431, by rfl⟩ : syracuseStep 1725077 = 80863) (by norm_num)
theorem B905885 : Blo 603293 905885 := bbase (se 3 (by rfl) ⟨169853, by rfl⟩ : syracuseStep 905885 = 339707) (by norm_num)
theorem B905909 : Blo 603293 905909 := bbase (se 5 (by rfl) ⟨42464, by rfl⟩ : syracuseStep 905909 = 84929) (by norm_num)
theorem B1364669 : Blo 603293 1364669 := bbase (se 3 (by rfl) ⟨255875, by rfl⟩ : syracuseStep 1364669 = 511751) (by norm_num)
theorem B905933 : Blo 603293 905933 := bbase (se 3 (by rfl) ⟨169862, by rfl⟩ : syracuseStep 905933 = 339725) (by norm_num)
theorem B1528541 : Blo 603293 1528541 := bbase (se 3 (by rfl) ⟨286601, by rfl⟩ : syracuseStep 1528541 = 573203) (by norm_num)
theorem B905957 : Blo 603293 905957 := bbase (se 4 (by rfl) ⟨84933, by rfl⟩ : syracuseStep 905957 = 169867) (by norm_num)
theorem B1037045 : Blo 603293 1037045 := bbase (se 5 (by rfl) ⟨48611, by rfl⟩ : syracuseStep 1037045 = 97223) (by norm_num)
theorem B905981 : Blo 603293 905981 := bbase (se 3 (by rfl) ⟨169871, by rfl⟩ : syracuseStep 905981 = 339743) (by norm_num)
theorem B1364741 : Blo 603293 1364741 := bbase (se 4 (by rfl) ⟨127944, by rfl⟩ : syracuseStep 1364741 = 255889) (by norm_num)
theorem B906005 : Blo 603293 906005 := bbase (se 6 (by rfl) ⟨21234, by rfl⟩ : syracuseStep 906005 = 42469) (by norm_num)
theorem B906029 : Blo 603293 906029 := bbase (se 3 (by rfl) ⟨169880, by rfl⟩ : syracuseStep 906029 = 339761) (by norm_num)
theorem B906053 : Blo 603293 906053 := bbase (se 4 (by rfl) ⟨84942, by rfl⟩ : syracuseStep 906053 = 169885) (by norm_num)
theorem B1037125 : Blo 603293 1037125 := bbase (se 4 (by rfl) ⟨97230, by rfl⟩ : syracuseStep 1037125 = 194461) (by norm_num)
theorem B1364813 : Blo 603293 1364813 := bbase (se 3 (by rfl) ⟨255902, by rfl⟩ : syracuseStep 1364813 = 511805) (by norm_num)
theorem B971605 : Blo 603293 971605 := bbase (se 9 (by rfl) ⟨2846, by rfl⟩ : syracuseStep 971605 = 5693) (by norm_num)
theorem B906077 : Blo 603293 906077 := bbase (se 3 (by rfl) ⟨169889, by rfl⟩ : syracuseStep 906077 = 339779) (by norm_num)
theorem B1168229 : Blo 603293 1168229 := bbase (se 4 (by rfl) ⟨109521, by rfl⟩ : syracuseStep 1168229 = 219043) (by norm_num)
theorem B906101 : Blo 603293 906101 := bbase (se 5 (by rfl) ⟨42473, by rfl⟩ : syracuseStep 906101 = 84947) (by norm_num)
theorem B906125 : Blo 603293 906125 := bbase (se 3 (by rfl) ⟨169898, by rfl⟩ : syracuseStep 906125 = 339797) (by norm_num)
theorem B1364885 : Blo 603293 1364885 := bbase (se 6 (by rfl) ⟨31989, by rfl⟩ : syracuseStep 1364885 = 63979) (by norm_num)
theorem B1528733 : Blo 603293 1528733 := bbase (se 3 (by rfl) ⟨286637, by rfl⟩ : syracuseStep 1528733 = 573275) (by norm_num)
theorem B906149 : Blo 603293 906149 := bbase (se 4 (by rfl) ⟨84951, by rfl⟩ : syracuseStep 906149 = 169903) (by norm_num)
theorem B906173 : Blo 603293 906173 := bbase (se 3 (by rfl) ⟨169907, by rfl⟩ : syracuseStep 906173 = 339815) (by norm_num)
theorem B2577365 : Blo 603293 2577365 := bbase (se 7 (by rfl) ⟨30203, by rfl⟩ : syracuseStep 2577365 = 60407) (by norm_num)
theorem B906197 : Blo 603293 906197 := bbase (se 7 (by rfl) ⟨10619, by rfl⟩ : syracuseStep 906197 = 21239) (by norm_num)
theorem B1364957 : Blo 603293 1364957 := bbase (se 3 (by rfl) ⟨255929, by rfl⟩ : syracuseStep 1364957 = 511859) (by norm_num)
theorem B906221 : Blo 603293 906221 := bbase (se 3 (by rfl) ⟨169916, by rfl⟩ : syracuseStep 906221 = 339833) (by norm_num)
theorem B906245 : Blo 603293 906245 := bbase (se 4 (by rfl) ⟨84960, by rfl⟩ : syracuseStep 906245 = 169921) (by norm_num)
theorem B906269 : Blo 603293 906269 := bbase (se 3 (by rfl) ⟨169925, by rfl⟩ : syracuseStep 906269 = 339851) (by norm_num)
theorem B1365029 : Blo 603293 1365029 := bbase (se 4 (by rfl) ⟨127971, by rfl⟩ : syracuseStep 1365029 = 255943) (by norm_num)
theorem B906293 : Blo 603293 906293 := bbase (se 5 (by rfl) ⟨42482, by rfl⟩ : syracuseStep 906293 = 84965) (by norm_num)
theorem B906317 : Blo 603293 906317 := bbase (se 3 (by rfl) ⟨169934, by rfl⟩ : syracuseStep 906317 = 339869) (by norm_num)
theorem B906341 : Blo 603293 906341 := bbase (se 4 (by rfl) ⟨84969, by rfl⟩ : syracuseStep 906341 = 169939) (by norm_num)
theorem B1365101 : Blo 603293 1365101 := bbase (se 3 (by rfl) ⟨255956, by rfl⟩ : syracuseStep 1365101 = 511913) (by norm_num)
theorem B906365 : Blo 603293 906365 := bbase (se 3 (by rfl) ⟨169943, by rfl⟩ : syracuseStep 906365 = 339887) (by norm_num)
theorem B906389 : Blo 603293 906389 := bbase (se 6 (by rfl) ⟨21243, by rfl⟩ : syracuseStep 906389 = 42487) (by norm_num)
theorem B906413 : Blo 603293 906413 := bbase (se 3 (by rfl) ⟨169952, by rfl⟩ : syracuseStep 906413 = 339905) (by norm_num)
theorem B1365173 : Blo 603293 1365173 := bbase (se 5 (by rfl) ⟨63992, by rfl⟩ : syracuseStep 1365173 = 127985) (by norm_num)
theorem B906437 : Blo 603293 906437 := bbase (se 4 (by rfl) ⟨84978, by rfl⟩ : syracuseStep 906437 = 169957) (by norm_num)
theorem B775381 : Blo 603293 775381 := bbase (se 7 (by rfl) ⟨9086, by rfl⟩ : syracuseStep 775381 = 18173) (by norm_num)
theorem B906461 : Blo 603293 906461 := bbase (se 3 (by rfl) ⟨169961, by rfl⟩ : syracuseStep 906461 = 339923) (by norm_num)
theorem B775397 : Blo 603293 775397 := bbase (se 4 (by rfl) ⟨72693, by rfl⟩ : syracuseStep 775397 = 145387) (by norm_num)
theorem B2577653 : Blo 603293 2577653 := bbase (se 5 (by rfl) ⟨120827, by rfl⟩ : syracuseStep 2577653 = 241655) (by norm_num)
theorem B1529077 : Blo 603293 1529077 := bbase (se 5 (by rfl) ⟨71675, by rfl⟩ : syracuseStep 1529077 = 143351) (by norm_num)
theorem B906485 : Blo 603293 906485 := bbase (se 5 (by rfl) ⟨42491, by rfl⟩ : syracuseStep 906485 = 84983) (by norm_num)
theorem B1365245 : Blo 603293 1365245 := bbase (se 3 (by rfl) ⟨255983, by rfl⟩ : syracuseStep 1365245 = 511967) (by norm_num)
theorem B906509 : Blo 603293 906509 := bbase (se 3 (by rfl) ⟨169970, by rfl⟩ : syracuseStep 906509 = 339941) (by norm_num)
theorem B2446613 : Blo 603293 2446613 := bbase (se 6 (by rfl) ⟨57342, by rfl⟩ : syracuseStep 2446613 = 114685) (by norm_num)
theorem B906533 : Blo 603293 906533 := bbase (se 4 (by rfl) ⟨84987, by rfl⟩ : syracuseStep 906533 = 169975) (by norm_num)
theorem B3495221 : Blo 603293 3495221 := bbase (se 5 (by rfl) ⟨163838, by rfl⟩ : syracuseStep 3495221 = 327677) (by norm_num)
theorem B1725749 : Blo 603293 1725749 := bbase (se 5 (by rfl) ⟨80894, by rfl⟩ : syracuseStep 1725749 = 161789) (by norm_num)
theorem B906557 : Blo 603293 906557 := bbase (se 3 (by rfl) ⟨169979, by rfl⟩ : syracuseStep 906557 = 339959) (by norm_num)
theorem B1365317 : Blo 603293 1365317 := bbase (se 4 (by rfl) ⟨127998, by rfl⟩ : syracuseStep 1365317 = 255997) (by norm_num)
theorem B906581 : Blo 603293 906581 := bbase (se 15 (by rfl) ⟨41, by rfl⟩ : syracuseStep 906581 = 83) (by norm_num)
theorem B1529189 : Blo 603293 1529189 := bbase (se 4 (by rfl) ⟨143361, by rfl⟩ : syracuseStep 1529189 = 286723) (by norm_num)
theorem B906605 : Blo 603293 906605 := bbase (se 3 (by rfl) ⟨169988, by rfl⟩ : syracuseStep 906605 = 339977) (by norm_num)
theorem B906629 : Blo 603293 906629 := bbase (se 4 (by rfl) ⟨84996, by rfl⟩ : syracuseStep 906629 = 169993) (by norm_num)
theorem B1365389 : Blo 603293 1365389 := bbase (se 3 (by rfl) ⟨256010, by rfl⟩ : syracuseStep 1365389 = 512021) (by norm_num)
theorem B906653 : Blo 603293 906653 := bbase (se 3 (by rfl) ⟨169997, by rfl⟩ : syracuseStep 906653 = 339995) (by norm_num)
theorem B906677 : Blo 603293 906677 := bbase (se 5 (by rfl) ⟨42500, by rfl⟩ : syracuseStep 906677 = 85001) (by norm_num)
theorem B906701 : Blo 603293 906701 := bbase (se 3 (by rfl) ⟨170006, by rfl⟩ : syracuseStep 906701 = 340013) (by norm_num)
theorem B1365461 : Blo 603293 1365461 := bbase (se 7 (by rfl) ⟨16001, by rfl⟩ : syracuseStep 1365461 = 32003) (by norm_num)
theorem B972253 : Blo 603293 972253 := bbase (se 3 (by rfl) ⟨182297, by rfl⟩ : syracuseStep 972253 = 364595) (by norm_num)
theorem B906725 : Blo 603293 906725 := bbase (se 4 (by rfl) ⟨85005, by rfl⟩ : syracuseStep 906725 = 170011) (by norm_num)
theorem B3069413 : Blo 603293 3069413 := bbase (se 4 (by rfl) ⟨287757, by rfl⟩ : syracuseStep 3069413 = 575515) (by norm_num)
theorem B644593 : Blo 603293 644593 := bbase (se 2 (by rfl) ⟨241722, by rfl⟩ : syracuseStep 644593 = 483445) (by norm_num)
theorem B906749 : Blo 603293 906749 := bbase (se 3 (by rfl) ⟨170015, by rfl⟩ : syracuseStep 906749 = 340031) (by norm_num)
theorem B906773 : Blo 603293 906773 := bbase (se 6 (by rfl) ⟨21252, by rfl⟩ : syracuseStep 906773 = 42505) (by norm_num)
theorem B1365533 : Blo 603293 1365533 := bbase (se 3 (by rfl) ⟨256037, by rfl⟩ : syracuseStep 1365533 = 512075) (by norm_num)
theorem B1529381 : Blo 603293 1529381 := bbase (se 4 (by rfl) ⟨143379, by rfl⟩ : syracuseStep 1529381 = 286759) (by norm_num)
theorem B906797 : Blo 603293 906797 := bbase (se 3 (by rfl) ⟨170024, by rfl⟩ : syracuseStep 906797 = 340049) (by norm_num)
theorem B906821 : Blo 603293 906821 := bbase (se 4 (by rfl) ⟨85014, by rfl⟩ : syracuseStep 906821 = 170029) (by norm_num)
theorem B1037893 : Blo 603293 1037893 := bbase (se 4 (by rfl) ⟨97302, by rfl⟩ : syracuseStep 1037893 = 194605) (by norm_num)
theorem B611933 : Blo 603293 611933 := bbase (se 3 (by rfl) ⟨114737, by rfl⟩ : syracuseStep 611933 = 229475) (by norm_num)
theorem B906845 : Blo 603293 906845 := bbase (se 3 (by rfl) ⟨170033, by rfl⟩ : syracuseStep 906845 = 340067) (by norm_num)
theorem B1365605 : Blo 603293 1365605 := bbase (se 4 (by rfl) ⟨128025, by rfl⟩ : syracuseStep 1365605 = 256051) (by norm_num)
theorem B644717 : Blo 603293 644717 := bbase (se 3 (by rfl) ⟨120884, by rfl⟩ : syracuseStep 644717 = 241769) (by norm_num)
theorem B906869 : Blo 603293 906869 := bbase (se 5 (by rfl) ⟨42509, by rfl⟩ : syracuseStep 906869 = 85019) (by norm_num)
theorem B906893 : Blo 603293 906893 := bbase (se 3 (by rfl) ⟨170042, by rfl⟩ : syracuseStep 906893 = 340085) (by norm_num)
theorem B2479781 : Blo 603293 2479781 := bbase (se 4 (by rfl) ⟨232479, by rfl⟩ : syracuseStep 2479781 = 464959) (by norm_num)
theorem B906917 : Blo 603293 906917 := bbase (se 4 (by rfl) ⟨85023, by rfl⟩ : syracuseStep 906917 = 170047) (by norm_num)
theorem B1365677 : Blo 603293 1365677 := bbase (se 3 (by rfl) ⟨256064, by rfl⟩ : syracuseStep 1365677 = 512129) (by norm_num)
theorem B906941 : Blo 603293 906941 := bbase (se 3 (by rfl) ⟨170051, by rfl⟩ : syracuseStep 906941 = 340103) (by norm_num)
theorem B906965 : Blo 603293 906965 := bbase (se 7 (by rfl) ⟨10628, by rfl⟩ : syracuseStep 906965 = 21257) (by norm_num)
theorem B1726181 : Blo 603293 1726181 := bbase (se 4 (by rfl) ⟨161829, by rfl⟩ : syracuseStep 1726181 = 323659) (by norm_num)
theorem B906989 : Blo 603293 906989 := bbase (se 3 (by rfl) ⟨170060, by rfl⟩ : syracuseStep 906989 = 340121) (by norm_num)
theorem B1365749 : Blo 603293 1365749 := bbase (se 5 (by rfl) ⟨64019, by rfl⟩ : syracuseStep 1365749 = 128039) (by norm_num)
theorem B907013 : Blo 603293 907013 := bbase (se 4 (by rfl) ⟨85032, by rfl⟩ : syracuseStep 907013 = 170065) (by norm_num)
theorem B907037 : Blo 603293 907037 := bbase (se 3 (by rfl) ⟨170069, by rfl⟩ : syracuseStep 907037 = 340139) (by norm_num)
theorem B907061 : Blo 603293 907061 := bbase (se 5 (by rfl) ⟨42518, by rfl⟩ : syracuseStep 907061 = 85037) (by norm_num)
theorem B1365821 : Blo 603293 1365821 := bbase (se 3 (by rfl) ⟨256091, by rfl⟩ : syracuseStep 1365821 = 512183) (by norm_num)
theorem B907085 : Blo 603293 907085 := bbase (se 3 (by rfl) ⟨170078, by rfl⟩ : syracuseStep 907085 = 340157) (by norm_num)
theorem B907109 : Blo 603293 907109 := bbase (se 4 (by rfl) ⟨85041, by rfl⟩ : syracuseStep 907109 = 170083) (by norm_num)
theorem B644969 : Blo 603293 644969 := bbase (se 2 (by rfl) ⟨241863, by rfl⟩ : syracuseStep 644969 = 483727) (by norm_num)
theorem B1529725 : Blo 603293 1529725 := bbase (se 3 (by rfl) ⟨286823, by rfl⟩ : syracuseStep 1529725 = 573647) (by norm_num)
theorem B907133 : Blo 603293 907133 := bbase (se 3 (by rfl) ⟨170087, by rfl⟩ : syracuseStep 907133 = 340175) (by norm_num)
theorem B1365893 : Blo 603293 1365893 := bbase (se 4 (by rfl) ⟨128052, by rfl⟩ : syracuseStep 1365893 = 256105) (by norm_num)
theorem B907157 : Blo 603293 907157 := bbase (se 6 (by rfl) ⟨21261, by rfl⟩ : syracuseStep 907157 = 42523) (by norm_num)
theorem B907181 : Blo 603293 907181 := bbase (se 3 (by rfl) ⟨170096, by rfl⟩ : syracuseStep 907181 = 340193) (by norm_num)
theorem B907205 : Blo 603293 907205 := bbase (se 4 (by rfl) ⟨85050, by rfl⟩ : syracuseStep 907205 = 170101) (by norm_num)
theorem B1365965 : Blo 603293 1365965 := bbase (se 3 (by rfl) ⟨256118, by rfl⟩ : syracuseStep 1365965 = 512237) (by norm_num)
theorem B5167061 : Blo 603293 5167061 := bbase (se 7 (by rfl) ⟨60551, by rfl⟩ : syracuseStep 5167061 = 121103) (by norm_num)
theorem B2807765 : Blo 603293 2807765 := bbase (se 7 (by rfl) ⟨32903, by rfl⟩ : syracuseStep 2807765 = 65807) (by norm_num)
theorem B907229 : Blo 603293 907229 := bbase (se 3 (by rfl) ⟨170105, by rfl⟩ : syracuseStep 907229 = 340211) (by norm_num)
theorem B2578405 : Blo 603293 2578405 := bbase (se 4 (by rfl) ⟨241725, by rfl⟩ : syracuseStep 2578405 = 483451) (by norm_num)
theorem B1529837 : Blo 603293 1529837 := bbase (se 3 (by rfl) ⟨286844, by rfl⟩ : syracuseStep 1529837 = 573689) (by norm_num)
theorem B907253 : Blo 603293 907253 := bbase (se 5 (by rfl) ⟨42527, by rfl⟩ : syracuseStep 907253 = 85055) (by norm_num)
theorem B5527541 : Blo 603293 5527541 := bbase (se 5 (by rfl) ⟨259103, by rfl⟩ : syracuseStep 5527541 = 518207) (by norm_num)
theorem B907277 : Blo 603293 907277 := bbase (se 3 (by rfl) ⟨170114, by rfl⟩ : syracuseStep 907277 = 340229) (by norm_num)
theorem B1366037 : Blo 603293 1366037 := bbase (se 6 (by rfl) ⟨32016, by rfl⟩ : syracuseStep 1366037 = 64033) (by norm_num)
theorem B907301 : Blo 603293 907301 := bbase (se 4 (by rfl) ⟨85059, by rfl⟩ : syracuseStep 907301 = 170119) (by norm_num)
theorem B907325 : Blo 603293 907325 := bbase (se 3 (by rfl) ⟨170123, by rfl⟩ : syracuseStep 907325 = 340247) (by norm_num)
theorem B907349 : Blo 603293 907349 := bbase (se 8 (by rfl) ⟨5316, by rfl⟩ : syracuseStep 907349 = 10633) (by norm_num)
theorem B1366109 : Blo 603293 1366109 := bbase (se 3 (by rfl) ⟨256145, by rfl⟩ : syracuseStep 1366109 = 512291) (by norm_num)
theorem B907373 : Blo 603293 907373 := bbase (se 3 (by rfl) ⟨170132, by rfl⟩ : syracuseStep 907373 = 340265) (by norm_num)
theorem B907397 : Blo 603293 907397 := bbase (se 4 (by rfl) ⟨85068, by rfl⟩ : syracuseStep 907397 = 170137) (by norm_num)
theorem B907421 : Blo 603293 907421 := bbase (se 3 (by rfl) ⟨170141, by rfl⟩ : syracuseStep 907421 = 340283) (by norm_num)
theorem B612517 : Blo 603293 612517 := bbase (se 4 (by rfl) ⟨57423, by rfl⟩ : syracuseStep 612517 = 114847) (by norm_num)
theorem B1366181 : Blo 603293 1366181 := bbase (se 4 (by rfl) ⟨128079, by rfl⟩ : syracuseStep 1366181 = 256159) (by norm_num)
theorem B1530029 : Blo 603293 1530029 := bbase (se 3 (by rfl) ⟨286880, by rfl⟩ : syracuseStep 1530029 = 573761) (by norm_num)
theorem B612533 : Blo 603293 612533 := bbase (se 5 (by rfl) ⟨28712, by rfl⟩ : syracuseStep 612533 = 57425) (by norm_num)
theorem B907445 : Blo 603293 907445 := bbase (se 5 (by rfl) ⟨42536, by rfl⟩ : syracuseStep 907445 = 85073) (by norm_num)
theorem B907469 : Blo 603293 907469 := bbase (se 3 (by rfl) ⟨170150, by rfl⟩ : syracuseStep 907469 = 340301) (by norm_num)
theorem B907493 : Blo 603293 907493 := bbase (se 4 (by rfl) ⟨85077, by rfl⟩ : syracuseStep 907493 = 170155) (by norm_num)
theorem B1366253 : Blo 603293 1366253 := bbase (se 3 (by rfl) ⟨256172, by rfl⟩ : syracuseStep 1366253 = 512345) (by norm_num)
theorem B907517 : Blo 603293 907517 := bbase (se 3 (by rfl) ⟨170159, by rfl⟩ : syracuseStep 907517 = 340319) (by norm_num)
theorem B907541 : Blo 603293 907541 := bbase (se 6 (by rfl) ⟨21270, by rfl⟩ : syracuseStep 907541 = 42541) (by norm_num)
theorem B645413 : Blo 603293 645413 := bbase (se 4 (by rfl) ⟨60507, by rfl⟩ : syracuseStep 645413 = 121015) (by norm_num)
theorem B907565 : Blo 603293 907565 := bbase (se 3 (by rfl) ⟨170168, by rfl⟩ : syracuseStep 907565 = 340337) (by norm_num)
theorem B1366325 : Blo 603293 1366325 := bbase (se 5 (by rfl) ⟨64046, by rfl⟩ : syracuseStep 1366325 = 128093) (by norm_num)
theorem B907589 : Blo 603293 907589 := bbase (se 4 (by rfl) ⟨85086, by rfl⟩ : syracuseStep 907589 = 170173) (by norm_num)
theorem B907613 : Blo 603293 907613 := bbase (se 3 (by rfl) ⟨170177, by rfl⟩ : syracuseStep 907613 = 340355) (by norm_num)
theorem B907637 : Blo 603293 907637 := bbase (se 5 (by rfl) ⟨42545, by rfl⟩ : syracuseStep 907637 = 85091) (by norm_num)
theorem B1366397 : Blo 603293 1366397 := bbase (se 3 (by rfl) ⟨256199, by rfl⟩ : syracuseStep 1366397 = 512399) (by norm_num)
theorem B907661 : Blo 603293 907661 := bbase (se 3 (by rfl) ⟨170186, by rfl⟩ : syracuseStep 907661 = 340373) (by norm_num)
theorem B907685 : Blo 603293 907685 := bbase (se 4 (by rfl) ⟨85095, by rfl⟩ : syracuseStep 907685 = 170191) (by norm_num)
theorem B612793 : Blo 603293 612793 := bbase (se 2 (by rfl) ⟨229797, by rfl⟩ : syracuseStep 612793 = 459595) (by norm_num)
theorem B907709 : Blo 603293 907709 := bbase (se 3 (by rfl) ⟨170195, by rfl⟩ : syracuseStep 907709 = 340391) (by norm_num)
theorem B907733 : Blo 603293 907733 := bbase (se 7 (by rfl) ⟨10637, by rfl⟩ : syracuseStep 907733 = 21275) (by norm_num)
theorem B1726933 : Blo 603293 1726933 := bbase (se 7 (by rfl) ⟨20237, by rfl⟩ : syracuseStep 1726933 = 40475) (by norm_num)
theorem B907757 : Blo 603293 907757 := bbase (se 3 (by rfl) ⟨170204, by rfl⟩ : syracuseStep 907757 = 340409) (by norm_num)
theorem B1530373 : Blo 603293 1530373 := bbase (se 4 (by rfl) ⟨143472, by rfl⟩ : syracuseStep 1530373 = 286945) (by norm_num)
theorem B1104389 : Blo 603293 1104389 := bbase (se 4 (by rfl) ⟨103536, by rfl⟩ : syracuseStep 1104389 = 207073) (by norm_num)
theorem B907781 : Blo 603293 907781 := bbase (se 4 (by rfl) ⟨85104, by rfl⟩ : syracuseStep 907781 = 170209) (by norm_num)
theorem B645661 : Blo 603293 645661 := bbase (se 3 (by rfl) ⟨121061, by rfl⟩ : syracuseStep 645661 = 242123) (by norm_num)
theorem B907805 : Blo 603293 907805 := bbase (se 3 (by rfl) ⟨170213, by rfl⟩ : syracuseStep 907805 = 340427) (by norm_num)
theorem B907829 : Blo 603293 907829 := bbase (se 5 (by rfl) ⟨42554, by rfl⟩ : syracuseStep 907829 = 85109) (by norm_num)
theorem B907853 : Blo 603293 907853 := bbase (se 3 (by rfl) ⟨170222, by rfl⟩ : syracuseStep 907853 = 340445) (by norm_num)
theorem B907877 : Blo 603293 907877 := bbase (se 4 (by rfl) ⟨85113, by rfl⟩ : syracuseStep 907877 = 170227) (by norm_num)
theorem B1530485 : Blo 603293 1530485 := bbase (se 5 (by rfl) ⟨71741, by rfl⟩ : syracuseStep 1530485 = 143483) (by norm_num)
theorem B907901 : Blo 603293 907901 := bbase (se 3 (by rfl) ⟨170231, by rfl⟩ : syracuseStep 907901 = 340463) (by norm_num)
theorem B907925 : Blo 603293 907925 := bbase (se 6 (by rfl) ⟨21279, by rfl⟩ : syracuseStep 907925 = 42559) (by norm_num)
theorem B1399445 : Blo 603293 1399445 := bbase (se 6 (by rfl) ⟨32799, by rfl⟩ : syracuseStep 1399445 = 65599) (by norm_num)
theorem B907949 : Blo 603293 907949 := bbase (se 3 (by rfl) ⟨170240, by rfl⟩ : syracuseStep 907949 = 340481) (by norm_num)
theorem B2579141 : Blo 603293 2579141 := bbase (se 4 (by rfl) ⟨241794, by rfl⟩ : syracuseStep 2579141 = 483589) (by norm_num)
theorem B907973 : Blo 603293 907973 := bbase (se 4 (by rfl) ⟨85122, by rfl⟩ : syracuseStep 907973 = 170245) (by norm_num)
theorem B907997 : Blo 603293 907997 := bbase (se 3 (by rfl) ⟨170249, by rfl⟩ : syracuseStep 907997 = 340499) (by norm_num)
theorem B613093 : Blo 603293 613093 := bbase (se 4 (by rfl) ⟨57477, by rfl⟩ : syracuseStep 613093 = 114955) (by norm_num)
theorem B908021 : Blo 603293 908021 := bbase (se 5 (by rfl) ⟨42563, by rfl⟩ : syracuseStep 908021 = 85127) (by norm_num)
theorem B3496693 : Blo 603293 3496693 := bbase (se 5 (by rfl) ⟨163907, by rfl⟩ : syracuseStep 3496693 = 327815) (by norm_num)
theorem B3070709 : Blo 603293 3070709 := bbase (se 5 (by rfl) ⟨143939, by rfl⟩ : syracuseStep 3070709 = 287879) (by norm_num)
theorem B613117 : Blo 603293 613117 := bbase (se 3 (by rfl) ⟨114959, by rfl⟩ : syracuseStep 613117 = 229919) (by norm_num)
theorem B908045 : Blo 603293 908045 := bbase (se 3 (by rfl) ⟨170258, by rfl⟩ : syracuseStep 908045 = 340517) (by norm_num)
theorem B908069 : Blo 603293 908069 := bbase (se 4 (by rfl) ⟨85131, by rfl⟩ : syracuseStep 908069 = 170263) (by norm_num)
theorem B1530677 : Blo 603293 1530677 := bbase (se 5 (by rfl) ⟨71750, by rfl⟩ : syracuseStep 1530677 = 143501) (by norm_num)
theorem B2906933 : Blo 603293 2906933 := bbase (se 5 (by rfl) ⟨136262, by rfl⟩ : syracuseStep 2906933 = 272525) (by norm_num)
theorem B908093 : Blo 603293 908093 := bbase (se 3 (by rfl) ⟨170267, by rfl⟩ : syracuseStep 908093 = 340535) (by norm_num)
theorem B678721 : Blo 603293 678721 := bbase (se 2 (by rfl) ⟨254520, by rfl⟩ : syracuseStep 678721 = 509041) (by norm_num)
theorem B908117 : Blo 603293 908117 := bbase (se 9 (by rfl) ⟨2660, by rfl⟩ : syracuseStep 908117 = 5321) (by norm_num)
theorem B678757 : Blo 603293 678757 := bbase (se 4 (by rfl) ⟨63633, by rfl⟩ : syracuseStep 678757 = 127267) (by norm_num)
theorem B908141 : Blo 603293 908141 := bbase (se 3 (by rfl) ⟨170276, by rfl⟩ : syracuseStep 908141 = 340553) (by norm_num)
theorem B908165 : Blo 603293 908165 := bbase (se 4 (by rfl) ⟨85140, by rfl⟩ : syracuseStep 908165 = 170281) (by norm_num)
theorem B678793 : Blo 603293 678793 := bbase (se 2 (by rfl) ⟨254547, by rfl⟩ : syracuseStep 678793 = 509095) (by norm_num)
theorem B908189 : Blo 603293 908189 := bbase (se 3 (by rfl) ⟨170285, by rfl⟩ : syracuseStep 908189 = 340571) (by norm_num)
theorem B678829 : Blo 603293 678829 := bbase (se 3 (by rfl) ⟨127280, by rfl⟩ : syracuseStep 678829 = 254561) (by norm_num)
theorem B908213 : Blo 603293 908213 := bbase (se 5 (by rfl) ⟨42572, by rfl⟩ : syracuseStep 908213 = 85145) (by norm_num)
theorem B908237 : Blo 603293 908237 := bbase (se 3 (by rfl) ⟨170294, by rfl⟩ : syracuseStep 908237 = 340589) (by norm_num)
theorem B678865 : Blo 603293 678865 := bbase (se 2 (by rfl) ⟨254574, by rfl⟩ : syracuseStep 678865 = 509149) (by norm_num)
theorem B7003093 : Blo 603293 7003093 := bbase (se 7 (by rfl) ⟨82067, by rfl⟩ : syracuseStep 7003093 = 164135) (by norm_num)
theorem B646105 : Blo 603293 646105 := bbase (se 2 (by rfl) ⟨242289, by rfl⟩ : syracuseStep 646105 = 484579) (by norm_num)
theorem B908261 : Blo 603293 908261 := bbase (se 4 (by rfl) ⟨85149, by rfl⟩ : syracuseStep 908261 = 170299) (by norm_num)
theorem B678901 : Blo 603293 678901 := bbase (se 5 (by rfl) ⟨31823, by rfl⟩ : syracuseStep 678901 = 63647) (by norm_num)
theorem B908285 : Blo 603293 908285 := bbase (se 3 (by rfl) ⟨170303, by rfl⟩ : syracuseStep 908285 = 340607) (by norm_num)
theorem B646165 : Blo 603293 646165 := bbase (se 6 (by rfl) ⟨15144, by rfl⟩ : syracuseStep 646165 = 30289) (by norm_num)
theorem B908309 : Blo 603293 908309 := bbase (se 6 (by rfl) ⟨21288, by rfl⟩ : syracuseStep 908309 = 42577) (by norm_num)
theorem B678937 : Blo 603293 678937 := bbase (se 2 (by rfl) ⟨254601, by rfl⟩ : syracuseStep 678937 = 509203) (by norm_num)
theorem B908333 : Blo 603293 908333 := bbase (se 3 (by rfl) ⟨170312, by rfl⟩ : syracuseStep 908333 = 340625) (by norm_num)
theorem B678973 : Blo 603293 678973 := bbase (se 3 (by rfl) ⟨127307, by rfl⟩ : syracuseStep 678973 = 254615) (by norm_num)
theorem B908357 : Blo 603293 908357 := bbase (se 4 (by rfl) ⟨85158, by rfl⟩ : syracuseStep 908357 = 170317) (by norm_num)
theorem B908381 : Blo 603293 908381 := bbase (se 3 (by rfl) ⟨170321, by rfl⟩ : syracuseStep 908381 = 340643) (by norm_num)
theorem B679009 : Blo 603293 679009 := bbase (se 2 (by rfl) ⟨254628, by rfl⟩ : syracuseStep 679009 = 509257) (by norm_num)
theorem B908405 : Blo 603293 908405 := bbase (se 5 (by rfl) ⟨42581, by rfl⟩ : syracuseStep 908405 = 85163) (by norm_num)
theorem B679045 : Blo 603293 679045 := bbase (se 4 (by rfl) ⟨63660, by rfl⟩ : syracuseStep 679045 = 127321) (by norm_num)
theorem B1531021 : Blo 603293 1531021 := bbase (se 3 (by rfl) ⟨287066, by rfl⟩ : syracuseStep 1531021 = 574133) (by norm_num)
theorem B908429 : Blo 603293 908429 := bbase (se 3 (by rfl) ⟨170330, by rfl⟩ : syracuseStep 908429 = 340661) (by norm_num)
theorem B908453 : Blo 603293 908453 := bbase (se 4 (by rfl) ⟨85167, by rfl⟩ : syracuseStep 908453 = 170335) (by norm_num)
theorem B679081 : Blo 603293 679081 := bbase (se 2 (by rfl) ⟨254655, by rfl⟩ : syracuseStep 679081 = 509311) (by norm_num)
theorem B908477 : Blo 603293 908477 := bbase (se 3 (by rfl) ⟨170339, by rfl⟩ : syracuseStep 908477 = 340679) (by norm_num)
theorem B679117 : Blo 603293 679117 := bbase (se 3 (by rfl) ⟨127334, by rfl⟩ : syracuseStep 679117 = 254669) (by norm_num)
theorem B908501 : Blo 603293 908501 := bbase (se 7 (by rfl) ⟨10646, by rfl⟩ : syracuseStep 908501 = 21293) (by norm_num)
theorem B908525 : Blo 603293 908525 := bbase (se 3 (by rfl) ⟨170348, by rfl⟩ : syracuseStep 908525 = 340697) (by norm_num)
theorem B679153 : Blo 603293 679153 := bbase (se 2 (by rfl) ⟨254682, by rfl⟩ : syracuseStep 679153 = 509365) (by norm_num)
theorem B1531133 : Blo 603293 1531133 := bbase (se 3 (by rfl) ⟨287087, by rfl⟩ : syracuseStep 1531133 = 574175) (by norm_num)
theorem B908549 : Blo 603293 908549 := bbase (se 4 (by rfl) ⟨85176, by rfl⟩ : syracuseStep 908549 = 170353) (by norm_num)
theorem B679189 : Blo 603293 679189 := bbase (se 6 (by rfl) ⟨15918, by rfl⟩ : syracuseStep 679189 = 31837) (by norm_num)
theorem B908573 : Blo 603293 908573 := bbase (se 3 (by rfl) ⟨170357, by rfl⟩ : syracuseStep 908573 = 340715) (by norm_num)
theorem B908597 : Blo 603293 908597 := bbase (se 5 (by rfl) ⟨42590, by rfl⟩ : syracuseStep 908597 = 85181) (by norm_num)
theorem B679225 : Blo 603293 679225 := bbase (se 2 (by rfl) ⟨254709, by rfl⟩ : syracuseStep 679225 = 509419) (by norm_num)
theorem B908621 : Blo 603293 908621 := bbase (se 3 (by rfl) ⟨170366, by rfl⟩ : syracuseStep 908621 = 340733) (by norm_num)
theorem B646481 : Blo 603293 646481 := bbase (se 2 (by rfl) ⟨242430, by rfl⟩ : syracuseStep 646481 = 484861) (by norm_num)
theorem B679261 : Blo 603293 679261 := bbase (se 3 (by rfl) ⟨127361, by rfl⟩ : syracuseStep 679261 = 254723) (by norm_num)
theorem B908645 : Blo 603293 908645 := bbase (se 4 (by rfl) ⟨85185, by rfl⟩ : syracuseStep 908645 = 170371) (by norm_num)
theorem B908669 : Blo 603293 908669 := bbase (se 3 (by rfl) ⟨170375, by rfl⟩ : syracuseStep 908669 = 340751) (by norm_num)
theorem B679297 : Blo 603293 679297 := bbase (se 2 (by rfl) ⟨254736, by rfl⟩ : syracuseStep 679297 = 509473) (by norm_num)
theorem B908693 : Blo 603293 908693 := bbase (se 6 (by rfl) ⟨21297, by rfl⟩ : syracuseStep 908693 = 42595) (by norm_num)
theorem B679333 : Blo 603293 679333 := bbase (se 4 (by rfl) ⟨63687, by rfl⟩ : syracuseStep 679333 = 127375) (by norm_num)
theorem B908717 : Blo 603293 908717 := bbase (se 3 (by rfl) ⟨170384, by rfl⟩ : syracuseStep 908717 = 340769) (by norm_num)
theorem B1531325 : Blo 603293 1531325 := bbase (se 3 (by rfl) ⟨287123, by rfl⟩ : syracuseStep 1531325 = 574247) (by norm_num)
theorem B908741 : Blo 603293 908741 := bbase (se 4 (by rfl) ⟨85194, by rfl⟩ : syracuseStep 908741 = 170389) (by norm_num)
theorem B679369 : Blo 603293 679369 := bbase (se 2 (by rfl) ⟨254763, by rfl⟩ : syracuseStep 679369 = 509527) (by norm_num)
theorem B908765 : Blo 603293 908765 := bbase (se 3 (by rfl) ⟨170393, by rfl⟩ : syracuseStep 908765 = 340787) (by norm_num)
theorem B679405 : Blo 603293 679405 := bbase (se 3 (by rfl) ⟨127388, by rfl⟩ : syracuseStep 679405 = 254777) (by norm_num)
theorem B908789 : Blo 603293 908789 := bbase (se 5 (by rfl) ⟨42599, by rfl⟩ : syracuseStep 908789 = 85199) (by norm_num)
theorem B908813 : Blo 603293 908813 := bbase (se 3 (by rfl) ⟨170402, by rfl⟩ : syracuseStep 908813 = 340805) (by norm_num)
theorem B679441 : Blo 603293 679441 := bbase (se 2 (by rfl) ⟨254790, by rfl⟩ : syracuseStep 679441 = 509581) (by norm_num)
theorem B908837 : Blo 603293 908837 := bbase (se 4 (by rfl) ⟨85203, by rfl⟩ : syracuseStep 908837 = 170407) (by norm_num)
theorem B679477 : Blo 603293 679477 := bbase (se 5 (by rfl) ⟨31850, by rfl⟩ : syracuseStep 679477 = 63701) (by norm_num)
theorem B908861 : Blo 603293 908861 := bbase (se 3 (by rfl) ⟨170411, by rfl⟩ : syracuseStep 908861 = 340823) (by norm_num)
theorem B908885 : Blo 603293 908885 := bbase (se 8 (by rfl) ⟨5325, by rfl⟩ : syracuseStep 908885 = 10651) (by norm_num)
theorem B679513 : Blo 603293 679513 := bbase (se 2 (by rfl) ⟨254817, by rfl⟩ : syracuseStep 679513 = 509635) (by norm_num)
theorem B908909 : Blo 603293 908909 := bbase (se 3 (by rfl) ⟨170420, by rfl⟩ : syracuseStep 908909 = 340841) (by norm_num)
theorem B679549 : Blo 603293 679549 := bbase (se 3 (by rfl) ⟨127415, by rfl⟩ : syracuseStep 679549 = 254831) (by norm_num)
theorem B908933 : Blo 603293 908933 := bbase (se 4 (by rfl) ⟨85212, by rfl⟩ : syracuseStep 908933 = 170425) (by norm_num)
theorem B908957 : Blo 603293 908957 := bbase (se 3 (by rfl) ⟨170429, by rfl⟩ : syracuseStep 908957 = 340859) (by norm_num)
theorem B679585 : Blo 603293 679585 := bbase (se 2 (by rfl) ⟨254844, by rfl⟩ : syracuseStep 679585 = 509689) (by norm_num)
theorem B908981 : Blo 603293 908981 := bbase (se 5 (by rfl) ⟨42608, by rfl⟩ : syracuseStep 908981 = 85217) (by norm_num)
theorem B679621 : Blo 603293 679621 := bbase (se 4 (by rfl) ⟨63714, by rfl⟩ : syracuseStep 679621 = 127429) (by norm_num)
theorem B909005 : Blo 603293 909005 := bbase (se 3 (by rfl) ⟨170438, by rfl⟩ : syracuseStep 909005 = 340877) (by norm_num)
theorem B909029 : Blo 603293 909029 := bbase (se 4 (by rfl) ⟨85221, by rfl⟩ : syracuseStep 909029 = 170443) (by norm_num)
theorem B679657 : Blo 603293 679657 := bbase (se 2 (by rfl) ⟨254871, by rfl⟩ : syracuseStep 679657 = 509743) (by norm_num)
theorem B909053 : Blo 603293 909053 := bbase (se 3 (by rfl) ⟨170447, by rfl⟩ : syracuseStep 909053 = 340895) (by norm_num)
theorem B679693 : Blo 603293 679693 := bbase (se 3 (by rfl) ⟨127442, by rfl⟩ : syracuseStep 679693 = 254885) (by norm_num)
theorem B646925 : Blo 603293 646925 := bbase (se 3 (by rfl) ⟨121298, by rfl⟩ : syracuseStep 646925 = 242597) (by norm_num)
theorem B1531669 : Blo 603293 1531669 := bbase (se 6 (by rfl) ⟨35898, by rfl⟩ : syracuseStep 1531669 = 71797) (by norm_num)
theorem B909077 : Blo 603293 909077 := bbase (se 6 (by rfl) ⟨21306, by rfl⟩ : syracuseStep 909077 = 42613) (by norm_num)
theorem B909101 : Blo 603293 909101 := bbase (se 3 (by rfl) ⟨170456, by rfl⟩ : syracuseStep 909101 = 340913) (by norm_num)
theorem B679729 : Blo 603293 679729 := bbase (se 2 (by rfl) ⟨254898, by rfl⟩ : syracuseStep 679729 = 509797) (by norm_num)
theorem B909125 : Blo 603293 909125 := bbase (se 4 (by rfl) ⟨85230, by rfl⟩ : syracuseStep 909125 = 170461) (by norm_num)
theorem B646985 : Blo 603293 646985 := bbase (se 2 (by rfl) ⟨242619, by rfl⟩ : syracuseStep 646985 = 485239) (by norm_num)
theorem B679765 : Blo 603293 679765 := bbase (se 9 (by rfl) ⟨1991, by rfl⟩ : syracuseStep 679765 = 3983) (by norm_num)
theorem B909149 : Blo 603293 909149 := bbase (se 3 (by rfl) ⟨170465, by rfl⟩ : syracuseStep 909149 = 340931) (by norm_num)
theorem B909173 : Blo 603293 909173 := bbase (se 5 (by rfl) ⟨42617, by rfl⟩ : syracuseStep 909173 = 85235) (by norm_num)
theorem B679801 : Blo 603293 679801 := bbase (se 2 (by rfl) ⟨254925, by rfl⟩ : syracuseStep 679801 = 509851) (by norm_num)
theorem B1531781 : Blo 603293 1531781 := bbase (se 4 (by rfl) ⟨143604, by rfl⟩ : syracuseStep 1531781 = 287209) (by norm_num)
theorem B909197 : Blo 603293 909197 := bbase (se 3 (by rfl) ⟨170474, by rfl⟩ : syracuseStep 909197 = 340949) (by norm_num)
theorem B679837 : Blo 603293 679837 := bbase (se 3 (by rfl) ⟨127469, by rfl⟩ : syracuseStep 679837 = 254939) (by norm_num)
theorem B909221 : Blo 603293 909221 := bbase (se 4 (by rfl) ⟨85239, by rfl⟩ : syracuseStep 909221 = 170479) (by norm_num)
theorem B909245 : Blo 603293 909245 := bbase (se 3 (by rfl) ⟨170483, by rfl⟩ : syracuseStep 909245 = 340967) (by norm_num)
theorem B679873 : Blo 603293 679873 := bbase (se 2 (by rfl) ⟨254952, by rfl⟩ : syracuseStep 679873 = 509905) (by norm_num)
theorem B647113 : Blo 603293 647113 := bbase (se 2 (by rfl) ⟨242667, by rfl⟩ : syracuseStep 647113 = 485335) (by norm_num)
theorem B909269 : Blo 603293 909269 := bbase (se 7 (by rfl) ⟨10655, by rfl⟩ : syracuseStep 909269 = 21311) (by norm_num)
theorem B679909 : Blo 603293 679909 := bbase (se 4 (by rfl) ⟨63741, by rfl⟩ : syracuseStep 679909 = 127483) (by norm_num)
theorem B909293 : Blo 603293 909293 := bbase (se 3 (by rfl) ⟨170492, by rfl⟩ : syracuseStep 909293 = 340985) (by norm_num)
theorem B909317 : Blo 603293 909317 := bbase (se 4 (by rfl) ⟨85248, by rfl⟩ : syracuseStep 909317 = 170497) (by norm_num)
theorem B3072005 : Blo 603293 3072005 := bbase (se 4 (by rfl) ⟨288000, by rfl⟩ : syracuseStep 3072005 = 576001) (by norm_num)
theorem B679945 : Blo 603293 679945 := bbase (se 2 (by rfl) ⟨254979, by rfl⟩ : syracuseStep 679945 = 509959) (by norm_num)
theorem B909341 : Blo 603293 909341 := bbase (se 3 (by rfl) ⟨170501, by rfl⟩ : syracuseStep 909341 = 341003) (by norm_num)
theorem B679981 : Blo 603293 679981 := bbase (se 3 (by rfl) ⟨127496, by rfl⟩ : syracuseStep 679981 = 254993) (by norm_num)
theorem B909365 : Blo 603293 909365 := bbase (se 5 (by rfl) ⟨42626, by rfl⟩ : syracuseStep 909365 = 85253) (by norm_num)
theorem B1531973 : Blo 603293 1531973 := bbase (se 4 (by rfl) ⟨143622, by rfl⟩ : syracuseStep 1531973 = 287245) (by norm_num)
theorem B909389 : Blo 603293 909389 := bbase (se 3 (by rfl) ⟨170510, by rfl⟩ : syracuseStep 909389 = 341021) (by norm_num)
theorem B680017 : Blo 603293 680017 := bbase (se 2 (by rfl) ⟨255006, by rfl⟩ : syracuseStep 680017 = 510013) (by norm_num)
theorem B909413 : Blo 603293 909413 := bbase (se 4 (by rfl) ⟨85257, by rfl⟩ : syracuseStep 909413 = 170515) (by norm_num)
theorem B680053 : Blo 603293 680053 := bbase (se 5 (by rfl) ⟨31877, by rfl⟩ : syracuseStep 680053 = 63755) (by norm_num)
theorem B909437 : Blo 603293 909437 := bbase (se 3 (by rfl) ⟨170519, by rfl⟩ : syracuseStep 909437 = 341039) (by norm_num)
theorem B909461 : Blo 603293 909461 := bbase (se 6 (by rfl) ⟨21315, by rfl⟩ : syracuseStep 909461 = 42631) (by norm_num)
theorem B680089 : Blo 603293 680089 := bbase (se 2 (by rfl) ⟨255033, by rfl⟩ : syracuseStep 680089 = 510067) (by norm_num)
theorem B909485 : Blo 603293 909485 := bbase (se 3 (by rfl) ⟨170528, by rfl⟩ : syracuseStep 909485 = 341057) (by norm_num)
theorem B614585 : Blo 603293 614585 := bbase (se 2 (by rfl) ⟨230469, by rfl⟩ : syracuseStep 614585 = 460939) (by norm_num)
theorem B680125 : Blo 603293 680125 := bbase (se 3 (by rfl) ⟨127523, by rfl⟩ : syracuseStep 680125 = 255047) (by norm_num)
theorem B909509 : Blo 603293 909509 := bbase (se 4 (by rfl) ⟨85266, by rfl⟩ : syracuseStep 909509 = 170533) (by norm_num)
theorem B909533 : Blo 603293 909533 := bbase (se 3 (by rfl) ⟨170537, by rfl⟩ : syracuseStep 909533 = 341075) (by norm_num)
theorem B680161 : Blo 603293 680161 := bbase (se 2 (by rfl) ⟨255060, by rfl⟩ : syracuseStep 680161 = 510121) (by norm_num)
theorem B909557 : Blo 603293 909557 := bbase (se 5 (by rfl) ⟨42635, by rfl⟩ : syracuseStep 909557 = 85271) (by norm_num)
theorem B1138933 : Blo 603293 1138933 := bbase (se 5 (by rfl) ⟨53387, by rfl⟩ : syracuseStep 1138933 = 106775) (by norm_num)
theorem B680197 : Blo 603293 680197 := bbase (se 4 (by rfl) ⟨63768, by rfl⟩ : syracuseStep 680197 = 127537) (by norm_num)
theorem B909581 : Blo 603293 909581 := bbase (se 3 (by rfl) ⟨170546, by rfl⟩ : syracuseStep 909581 = 341093) (by norm_num)
theorem B909605 : Blo 603293 909605 := bbase (se 4 (by rfl) ⟨85275, by rfl⟩ : syracuseStep 909605 = 170551) (by norm_num)
theorem B680233 : Blo 603293 680233 := bbase (se 2 (by rfl) ⟨255087, by rfl⟩ : syracuseStep 680233 = 510175) (by norm_num)
theorem B909629 : Blo 603293 909629 := bbase (se 3 (by rfl) ⟨170555, by rfl⟩ : syracuseStep 909629 = 341111) (by norm_num)
theorem B680269 : Blo 603293 680269 := bbase (se 3 (by rfl) ⟨127550, by rfl⟩ : syracuseStep 680269 = 255101) (by norm_num)
theorem B909653 : Blo 603293 909653 := bbase (se 10 (by rfl) ⟨1332, by rfl⟩ : syracuseStep 909653 = 2665) (by norm_num)
theorem B909677 : Blo 603293 909677 := bbase (se 3 (by rfl) ⟨170564, by rfl⟩ : syracuseStep 909677 = 341129) (by norm_num)
theorem B680305 : Blo 603293 680305 := bbase (se 2 (by rfl) ⟨255114, by rfl⟩ : syracuseStep 680305 = 510229) (by norm_num)
theorem B647557 : Blo 603293 647557 := bbase (se 4 (by rfl) ⟨60708, by rfl⟩ : syracuseStep 647557 = 121417) (by norm_num)
theorem B909701 : Blo 603293 909701 := bbase (se 4 (by rfl) ⟨85284, by rfl⟩ : syracuseStep 909701 = 170569) (by norm_num)
theorem B680341 : Blo 603293 680341 := bbase (se 6 (by rfl) ⟨15945, by rfl⟩ : syracuseStep 680341 = 31891) (by norm_num)
theorem B1532317 : Blo 603293 1532317 := bbase (se 3 (by rfl) ⟨287309, by rfl⟩ : syracuseStep 1532317 = 574619) (by norm_num)
theorem B909725 : Blo 603293 909725 := bbase (se 3 (by rfl) ⟨170573, by rfl⟩ : syracuseStep 909725 = 341147) (by norm_num)
theorem B909749 : Blo 603293 909749 := bbase (se 5 (by rfl) ⟨42644, by rfl⟩ : syracuseStep 909749 = 85289) (by norm_num)
theorem B680377 : Blo 603293 680377 := bbase (se 2 (by rfl) ⟨255141, by rfl⟩ : syracuseStep 680377 = 510283) (by norm_num)
theorem B909773 : Blo 603293 909773 := bbase (se 3 (by rfl) ⟨170582, by rfl⟩ : syracuseStep 909773 = 341165) (by norm_num)
theorem B680413 : Blo 603293 680413 := bbase (se 3 (by rfl) ⟨127577, by rfl⟩ : syracuseStep 680413 = 255155) (by norm_num)
theorem B909797 : Blo 603293 909797 := bbase (se 4 (by rfl) ⟨85293, by rfl⟩ : syracuseStep 909797 = 170587) (by norm_num)
theorem B647677 : Blo 603293 647677 := bbase (se 3 (by rfl) ⟨121439, by rfl⟩ : syracuseStep 647677 = 242879) (by norm_num)
theorem B909821 : Blo 603293 909821 := bbase (se 3 (by rfl) ⟨170591, by rfl⟩ : syracuseStep 909821 = 341183) (by norm_num)
theorem B680449 : Blo 603293 680449 := bbase (se 2 (by rfl) ⟨255168, by rfl⟩ : syracuseStep 680449 = 510337) (by norm_num)
theorem B1532429 : Blo 603293 1532429 := bbase (se 3 (by rfl) ⟨287330, by rfl⟩ : syracuseStep 1532429 = 574661) (by norm_num)
theorem B909845 : Blo 603293 909845 := bbase (se 6 (by rfl) ⟨21324, by rfl⟩ : syracuseStep 909845 = 42649) (by norm_num)
theorem B680485 : Blo 603293 680485 := bbase (se 4 (by rfl) ⟨63795, by rfl⟩ : syracuseStep 680485 = 127591) (by norm_num)
theorem B909869 : Blo 603293 909869 := bbase (se 3 (by rfl) ⟨170600, by rfl⟩ : syracuseStep 909869 = 341201) (by norm_num)
theorem B909893 : Blo 603293 909893 := bbase (se 4 (by rfl) ⟨85302, by rfl⟩ : syracuseStep 909893 = 170605) (by norm_num)
theorem B680521 : Blo 603293 680521 := bbase (se 2 (by rfl) ⟨255195, by rfl⟩ : syracuseStep 680521 = 510391) (by norm_num)
theorem B909917 : Blo 603293 909917 := bbase (se 3 (by rfl) ⟨170609, by rfl⟩ : syracuseStep 909917 = 341219) (by norm_num)
theorem B680557 : Blo 603293 680557 := bbase (se 3 (by rfl) ⟨127604, by rfl⟩ : syracuseStep 680557 = 255209) (by norm_num)
theorem B909941 : Blo 603293 909941 := bbase (se 5 (by rfl) ⟨42653, by rfl⟩ : syracuseStep 909941 = 85307) (by norm_num)
theorem B909965 : Blo 603293 909965 := bbase (se 3 (by rfl) ⟨170618, by rfl⟩ : syracuseStep 909965 = 341237) (by norm_num)
theorem B680593 : Blo 603293 680593 := bbase (se 2 (by rfl) ⟨255222, by rfl⟩ : syracuseStep 680593 = 510445) (by norm_num)
theorem B909989 : Blo 603293 909989 := bbase (se 4 (by rfl) ⟨85311, by rfl⟩ : syracuseStep 909989 = 170623) (by norm_num)
theorem B1401517 : Blo 603293 1401517 := bbase (se 3 (by rfl) ⟨262784, by rfl⟩ : syracuseStep 1401517 = 525569) (by norm_num)
theorem B680629 : Blo 603293 680629 := bbase (se 5 (by rfl) ⟨31904, by rfl⟩ : syracuseStep 680629 = 63809) (by norm_num)
theorem B910013 : Blo 603293 910013 := bbase (se 3 (by rfl) ⟨170627, by rfl⟩ : syracuseStep 910013 = 341255) (by norm_num)
theorem B1532621 : Blo 603293 1532621 := bbase (se 3 (by rfl) ⟨287366, by rfl⟩ : syracuseStep 1532621 = 574733) (by norm_num)
theorem B910037 : Blo 603293 910037 := bbase (se 7 (by rfl) ⟨10664, by rfl⟩ : syracuseStep 910037 = 21329) (by norm_num)
theorem B680665 : Blo 603293 680665 := bbase (se 2 (by rfl) ⟨255249, by rfl⟩ : syracuseStep 680665 = 510499) (by norm_num)
theorem B910061 : Blo 603293 910061 := bbase (se 3 (by rfl) ⟨170636, by rfl⟩ : syracuseStep 910061 = 341273) (by norm_num)
theorem B647929 : Blo 603293 647929 := bbase (se 2 (by rfl) ⟨242973, by rfl⟩ : syracuseStep 647929 = 485947) (by norm_num)
theorem B680701 : Blo 603293 680701 := bbase (se 3 (by rfl) ⟨127631, by rfl⟩ : syracuseStep 680701 = 255263) (by norm_num)
theorem B647933 : Blo 603293 647933 := bbase (se 3 (by rfl) ⟨121487, by rfl⟩ : syracuseStep 647933 = 242975) (by norm_num)
theorem B910085 : Blo 603293 910085 := bbase (se 4 (by rfl) ⟨85320, by rfl⟩ : syracuseStep 910085 = 170641) (by norm_num)
theorem B3498773 : Blo 603293 3498773 := bbase (se 6 (by rfl) ⟨82002, by rfl⟩ : syracuseStep 3498773 = 164005) (by norm_num)
theorem B910109 : Blo 603293 910109 := bbase (se 3 (by rfl) ⟨170645, by rfl⟩ : syracuseStep 910109 = 341291) (by norm_num)
theorem B680737 : Blo 603293 680737 := bbase (se 2 (by rfl) ⟨255276, by rfl⟩ : syracuseStep 680737 = 510553) (by norm_num)
theorem B910133 : Blo 603293 910133 := bbase (se 5 (by rfl) ⟨42662, by rfl⟩ : syracuseStep 910133 = 85325) (by norm_num)
theorem B680773 : Blo 603293 680773 := bbase (se 4 (by rfl) ⟨63822, by rfl⟩ : syracuseStep 680773 = 127645) (by norm_num)
theorem B910157 : Blo 603293 910157 := bbase (se 3 (by rfl) ⟨170654, by rfl⟩ : syracuseStep 910157 = 341309) (by norm_num)
theorem B910181 : Blo 603293 910181 := bbase (se 4 (by rfl) ⟨85329, by rfl⟩ : syracuseStep 910181 = 170659) (by norm_num)
theorem B680809 : Blo 603293 680809 := bbase (se 2 (by rfl) ⟨255303, by rfl⟩ : syracuseStep 680809 = 510607) (by norm_num)
theorem B910205 : Blo 603293 910205 := bbase (se 3 (by rfl) ⟨170663, by rfl⟩ : syracuseStep 910205 = 341327) (by norm_num)
theorem B680845 : Blo 603293 680845 := bbase (se 3 (by rfl) ⟨127658, by rfl⟩ : syracuseStep 680845 = 255317) (by norm_num)
theorem B910229 : Blo 603293 910229 := bbase (se 6 (by rfl) ⟨21333, by rfl⟩ : syracuseStep 910229 = 42667) (by norm_num)
theorem B910253 : Blo 603293 910253 := bbase (se 3 (by rfl) ⟨170672, by rfl⟩ : syracuseStep 910253 = 341345) (by norm_num)
theorem B680881 : Blo 603293 680881 := bbase (se 2 (by rfl) ⟨255330, by rfl⟩ : syracuseStep 680881 = 510661) (by norm_num)
theorem B910277 : Blo 603293 910277 := bbase (se 4 (by rfl) ⟨85338, by rfl⟩ : syracuseStep 910277 = 170677) (by norm_num)
theorem B680917 : Blo 603293 680917 := bbase (se 7 (by rfl) ⟨7979, by rfl⟩ : syracuseStep 680917 = 15959) (by norm_num)
theorem B910301 : Blo 603293 910301 := bbase (se 3 (by rfl) ⟨170681, by rfl⟩ : syracuseStep 910301 = 341363) (by norm_num)
theorem B910325 : Blo 603293 910325 := bbase (se 5 (by rfl) ⟨42671, by rfl⟩ : syracuseStep 910325 = 85343) (by norm_num)
theorem B680953 : Blo 603293 680953 := bbase (se 2 (by rfl) ⟨255357, by rfl⟩ : syracuseStep 680953 = 510715) (by norm_num)
theorem B910349 : Blo 603293 910349 := bbase (se 3 (by rfl) ⟨170690, by rfl⟩ : syracuseStep 910349 = 341381) (by norm_num)
theorem B680989 : Blo 603293 680989 := bbase (se 3 (by rfl) ⟨127685, by rfl⟩ : syracuseStep 680989 = 255371) (by norm_num)
theorem B1532965 : Blo 603293 1532965 := bbase (se 4 (by rfl) ⟨143715, by rfl⟩ : syracuseStep 1532965 = 287431) (by norm_num)
theorem B910373 : Blo 603293 910373 := bbase (se 4 (by rfl) ⟨85347, by rfl⟩ : syracuseStep 910373 = 170695) (by norm_num)
theorem B910397 : Blo 603293 910397 := bbase (se 3 (by rfl) ⟨170699, by rfl⟩ : syracuseStep 910397 = 341399) (by norm_num)
theorem B615485 : Blo 603293 615485 := bbase (se 3 (by rfl) ⟨115403, by rfl⟩ : syracuseStep 615485 = 230807) (by norm_num)
theorem B681025 : Blo 603293 681025 := bbase (se 2 (by rfl) ⟨255384, by rfl⟩ : syracuseStep 681025 = 510769) (by norm_num)
theorem B910421 : Blo 603293 910421 := bbase (se 8 (by rfl) ⟨5334, by rfl⟩ : syracuseStep 910421 = 10669) (by norm_num)
theorem B681061 : Blo 603293 681061 := bbase (se 4 (by rfl) ⟨63849, by rfl⟩ : syracuseStep 681061 = 127699) (by norm_num)
theorem B910445 : Blo 603293 910445 := bbase (se 3 (by rfl) ⟨170708, by rfl⟩ : syracuseStep 910445 = 341417) (by norm_num)
theorem B910469 : Blo 603293 910469 := bbase (se 4 (by rfl) ⟨85356, by rfl⟩ : syracuseStep 910469 = 170713) (by norm_num)
theorem B681097 : Blo 603293 681097 := bbase (se 2 (by rfl) ⟨255411, by rfl⟩ : syracuseStep 681097 = 510823) (by norm_num)
theorem B1533077 : Blo 603293 1533077 := bbase (se 6 (by rfl) ⟨35931, by rfl⟩ : syracuseStep 1533077 = 71863) (by norm_num)
theorem B910493 : Blo 603293 910493 := bbase (se 3 (by rfl) ⟨170717, by rfl⟩ : syracuseStep 910493 = 341435) (by norm_num)
theorem B681133 : Blo 603293 681133 := bbase (se 3 (by rfl) ⟨127712, by rfl⟩ : syracuseStep 681133 = 255425) (by norm_num)
theorem B910517 : Blo 603293 910517 := bbase (se 5 (by rfl) ⟨42680, by rfl⟩ : syracuseStep 910517 = 85361) (by norm_num)
theorem B910541 : Blo 603293 910541 := bbase (se 3 (by rfl) ⟨170726, by rfl⟩ : syracuseStep 910541 = 341453) (by norm_num)
theorem B681169 : Blo 603293 681169 := bbase (se 2 (by rfl) ⟨255438, by rfl⟩ : syracuseStep 681169 = 510877) (by norm_num)
theorem B910565 : Blo 603293 910565 := bbase (se 4 (by rfl) ⟨85365, by rfl⟩ : syracuseStep 910565 = 170731) (by norm_num)
theorem B681205 : Blo 603293 681205 := bbase (se 5 (by rfl) ⟨31931, by rfl⟩ : syracuseStep 681205 = 63863) (by norm_num)
theorem B910589 : Blo 603293 910589 := bbase (se 3 (by rfl) ⟨170735, by rfl⟩ : syracuseStep 910589 = 341471) (by norm_num)
theorem B3073301 : Blo 603293 3073301 := bbase (se 6 (by rfl) ⟨72030, by rfl⟩ : syracuseStep 3073301 = 144061) (by norm_num)
theorem B910613 : Blo 603293 910613 := bbase (se 6 (by rfl) ⟨21342, by rfl⟩ : syracuseStep 910613 = 42685) (by norm_num)
theorem B681241 : Blo 603293 681241 := bbase (se 2 (by rfl) ⟨255465, by rfl⟩ : syracuseStep 681241 = 510931) (by norm_num)
theorem B910637 : Blo 603293 910637 := bbase (se 3 (by rfl) ⟨170744, by rfl⟩ : syracuseStep 910637 = 341489) (by norm_num)
theorem B648497 : Blo 603293 648497 := bbase (se 2 (by rfl) ⟨243186, by rfl⟩ : syracuseStep 648497 = 486373) (by norm_num)
theorem B681277 : Blo 603293 681277 := bbase (se 3 (by rfl) ⟨127739, by rfl⟩ : syracuseStep 681277 = 255479) (by norm_num)
theorem B1402181 : Blo 603293 1402181 := bbase (se 4 (by rfl) ⟨131454, by rfl⟩ : syracuseStep 1402181 = 262909) (by norm_num)
theorem B910661 : Blo 603293 910661 := bbase (se 4 (by rfl) ⟨85374, by rfl⟩ : syracuseStep 910661 = 170749) (by norm_num)
theorem B1533269 : Blo 603293 1533269 := bbase (se 12 (by rfl) ⟨561, by rfl⟩ : syracuseStep 1533269 = 1123) (by norm_num)
theorem B910685 : Blo 603293 910685 := bbase (se 3 (by rfl) ⟨170753, by rfl⟩ : syracuseStep 910685 = 341507) (by norm_num)
theorem B681313 : Blo 603293 681313 := bbase (se 2 (by rfl) ⟨255492, by rfl⟩ : syracuseStep 681313 = 510985) (by norm_num)
theorem B1631605 : Blo 603293 1631605 := bbase (se 5 (by rfl) ⟨76481, by rfl⟩ : syracuseStep 1631605 = 152963) (by norm_num)
theorem B910709 : Blo 603293 910709 := bbase (se 5 (by rfl) ⟨42689, by rfl⟩ : syracuseStep 910709 = 85379) (by norm_num)
theorem B681349 : Blo 603293 681349 := bbase (se 4 (by rfl) ⟨63876, by rfl⟩ : syracuseStep 681349 = 127753) (by norm_num)
theorem B910733 : Blo 603293 910733 := bbase (se 3 (by rfl) ⟨170762, by rfl⟩ : syracuseStep 910733 = 341525) (by norm_num)
theorem B910757 : Blo 603293 910757 := bbase (se 4 (by rfl) ⟨85383, by rfl⟩ : syracuseStep 910757 = 170767) (by norm_num)
theorem B681385 : Blo 603293 681385 := bbase (se 2 (by rfl) ⟨255519, by rfl⟩ : syracuseStep 681385 = 511039) (by norm_num)
theorem B910781 : Blo 603293 910781 := bbase (se 3 (by rfl) ⟨170771, by rfl⟩ : syracuseStep 910781 = 341543) (by norm_num)
theorem B681421 : Blo 603293 681421 := bbase (se 3 (by rfl) ⟨127766, by rfl⟩ : syracuseStep 681421 = 255533) (by norm_num)
theorem B910805 : Blo 603293 910805 := bbase (se 7 (by rfl) ⟨10673, by rfl⟩ : syracuseStep 910805 = 21347) (by norm_num)
theorem B910829 : Blo 603293 910829 := bbase (se 3 (by rfl) ⟨170780, by rfl⟩ : syracuseStep 910829 = 341561) (by norm_num)
theorem B681457 : Blo 603293 681457 := bbase (se 2 (by rfl) ⟨255546, by rfl⟩ : syracuseStep 681457 = 511093) (by norm_num)
theorem B910853 : Blo 603293 910853 := bbase (se 4 (by rfl) ⟨85392, by rfl⟩ : syracuseStep 910853 = 170785) (by norm_num)
theorem B681493 : Blo 603293 681493 := bbase (se 6 (by rfl) ⟨15972, by rfl⟩ : syracuseStep 681493 = 31945) (by norm_num)
theorem B910877 : Blo 603293 910877 := bbase (se 3 (by rfl) ⟨170789, by rfl⟩ : syracuseStep 910877 = 341579) (by norm_num)
theorem B4154933 : Blo 603293 4154933 := bbase (se 5 (by rfl) ⟨194762, by rfl⟩ : syracuseStep 4154933 = 389525) (by norm_num)
theorem B910901 : Blo 603293 910901 := bbase (se 5 (by rfl) ⟨42698, by rfl⟩ : syracuseStep 910901 = 85397) (by norm_num)
theorem B681529 : Blo 603293 681529 := bbase (se 2 (by rfl) ⟨255573, by rfl⟩ : syracuseStep 681529 = 511147) (by norm_num)
theorem B910925 : Blo 603293 910925 := bbase (se 3 (by rfl) ⟨170798, by rfl⟩ : syracuseStep 910925 = 341597) (by norm_num)
theorem B681565 : Blo 603293 681565 := bbase (se 3 (by rfl) ⟨127793, by rfl⟩ : syracuseStep 681565 = 255587) (by norm_num)
theorem B681601 : Blo 603293 681601 := bbase (se 2 (by rfl) ⟨255600, by rfl⟩ : syracuseStep 681601 = 511201) (by norm_num)
theorem B681637 : Blo 603293 681637 := bbase (se 4 (by rfl) ⟨63903, by rfl⟩ : syracuseStep 681637 = 127807) (by norm_num)
theorem B1533613 : Blo 603293 1533613 := bbase (se 3 (by rfl) ⟨287552, by rfl⟩ : syracuseStep 1533613 = 575105) (by norm_num)
theorem B681673 : Blo 603293 681673 := bbase (se 2 (by rfl) ⟨255627, by rfl⟩ : syracuseStep 681673 = 511255) (by norm_num)
theorem B681709 : Blo 603293 681709 := bbase (se 3 (by rfl) ⟨127820, by rfl⟩ : syracuseStep 681709 = 255641) (by norm_num)
theorem B681745 : Blo 603293 681745 := bbase (se 2 (by rfl) ⟨255654, by rfl⟩ : syracuseStep 681745 = 511309) (by norm_num)
theorem B1533725 : Blo 603293 1533725 := bbase (se 3 (by rfl) ⟨287573, by rfl⟩ : syracuseStep 1533725 = 575147) (by norm_num)
theorem B681781 : Blo 603293 681781 := bbase (se 5 (by rfl) ⟨31958, by rfl⟩ : syracuseStep 681781 = 63917) (by norm_num)
theorem B681817 : Blo 603293 681817 := bbase (se 2 (by rfl) ⟨255681, by rfl⟩ : syracuseStep 681817 = 511363) (by norm_num)
theorem B681853 : Blo 603293 681853 := bbase (se 3 (by rfl) ⟨127847, by rfl⟩ : syracuseStep 681853 = 255695) (by norm_num)
theorem B681889 : Blo 603293 681889 := bbase (se 2 (by rfl) ⟨255708, by rfl⟩ : syracuseStep 681889 = 511417) (by norm_num)
theorem B2582437 : Blo 603293 2582437 := bbase (se 4 (by rfl) ⟨242103, by rfl⟩ : syracuseStep 2582437 = 484207) (by norm_num)
theorem B681925 : Blo 603293 681925 := bbase (se 4 (by rfl) ⟨63930, by rfl⟩ : syracuseStep 681925 = 127861) (by norm_num)
theorem B1533917 : Blo 603293 1533917 := bbase (se 3 (by rfl) ⟨287609, by rfl⟩ : syracuseStep 1533917 = 575219) (by norm_num)
theorem B681961 : Blo 603293 681961 := bbase (se 2 (by rfl) ⟨255735, by rfl⟩ : syracuseStep 681961 = 511471) (by norm_num)
theorem B681997 : Blo 603293 681997 := bbase (se 3 (by rfl) ⟨127874, by rfl⟩ : syracuseStep 681997 = 255749) (by norm_num)
theorem B682033 : Blo 603293 682033 := bbase (se 2 (by rfl) ⟨255762, by rfl⟩ : syracuseStep 682033 = 511525) (by norm_num)
theorem B682069 : Blo 603293 682069 := bbase (se 8 (by rfl) ⟨3996, by rfl⟩ : syracuseStep 682069 = 7993) (by norm_num)
theorem B682105 : Blo 603293 682105 := bbase (se 2 (by rfl) ⟨255789, by rfl⟩ : syracuseStep 682105 = 511579) (by norm_num)
theorem B682141 : Blo 603293 682141 := bbase (se 3 (by rfl) ⟨127901, by rfl⟩ : syracuseStep 682141 = 255803) (by norm_num)
theorem B682177 : Blo 603293 682177 := bbase (se 2 (by rfl) ⟨255816, by rfl⟩ : syracuseStep 682177 = 511633) (by norm_num)
theorem B682213 : Blo 603293 682213 := bbase (se 4 (by rfl) ⟨63957, by rfl⟩ : syracuseStep 682213 = 127915) (by norm_num)
theorem B682249 : Blo 603293 682249 := bbase (se 2 (by rfl) ⟨255843, by rfl⟩ : syracuseStep 682249 = 511687) (by norm_num)
theorem B682285 : Blo 603293 682285 := bbase (se 3 (by rfl) ⟨127928, by rfl⟩ : syracuseStep 682285 = 255857) (by norm_num)
theorem B1534261 : Blo 603293 1534261 := bbase (se 5 (by rfl) ⟨71918, by rfl⟩ : syracuseStep 1534261 = 143837) (by norm_num)
theorem B682321 : Blo 603293 682321 := bbase (se 2 (by rfl) ⟨255870, by rfl⟩ : syracuseStep 682321 = 511741) (by norm_num)
theorem B682357 : Blo 603293 682357 := bbase (se 5 (by rfl) ⟨31985, by rfl⟩ : syracuseStep 682357 = 63971) (by norm_num)
theorem B682393 : Blo 603293 682393 := bbase (se 2 (by rfl) ⟨255897, by rfl⟩ : syracuseStep 682393 = 511795) (by norm_num)
theorem B1534373 : Blo 603293 1534373 := bbase (se 4 (by rfl) ⟨143847, by rfl⟩ : syracuseStep 1534373 = 287695) (by norm_num)
theorem B682429 : Blo 603293 682429 := bbase (se 3 (by rfl) ⟨127955, by rfl⟩ : syracuseStep 682429 = 255911) (by norm_num)
theorem B682465 : Blo 603293 682465 := bbase (se 2 (by rfl) ⟨255924, by rfl⟩ : syracuseStep 682465 = 511849) (by norm_num)
theorem B682501 : Blo 603293 682501 := bbase (se 4 (by rfl) ⟨63984, by rfl⟩ : syracuseStep 682501 = 127969) (by norm_num)
theorem B682537 : Blo 603293 682537 := bbase (se 2 (by rfl) ⟨255951, by rfl⟩ : syracuseStep 682537 = 511903) (by norm_num)
theorem B682573 : Blo 603293 682573 := bbase (se 3 (by rfl) ⟨127982, by rfl⟩ : syracuseStep 682573 = 255965) (by norm_num)
theorem B1534565 : Blo 603293 1534565 := bbase (se 4 (by rfl) ⟨143865, by rfl⟩ : syracuseStep 1534565 = 287731) (by norm_num)
theorem B682609 : Blo 603293 682609 := bbase (se 2 (by rfl) ⟨255978, by rfl⟩ : syracuseStep 682609 = 511957) (by norm_num)
theorem B682645 : Blo 603293 682645 := bbase (se 6 (by rfl) ⟨15999, by rfl⟩ : syracuseStep 682645 = 31999) (by norm_num)
theorem B682681 : Blo 603293 682681 := bbase (se 2 (by rfl) ⟨256005, by rfl⟩ : syracuseStep 682681 = 512011) (by norm_num)
theorem B682717 : Blo 603293 682717 := bbase (se 3 (by rfl) ⟨128009, by rfl⟩ : syracuseStep 682717 = 256019) (by norm_num)
theorem B682753 : Blo 603293 682753 := bbase (se 2 (by rfl) ⟨256032, by rfl⟩ : syracuseStep 682753 = 512065) (by norm_num)
theorem B682789 : Blo 603293 682789 := bbase (se 4 (by rfl) ⟨64011, by rfl⟩ : syracuseStep 682789 = 128023) (by norm_num)
theorem B682825 : Blo 603293 682825 := bbase (se 2 (by rfl) ⟨256059, by rfl⟩ : syracuseStep 682825 = 512119) (by norm_num)
theorem B682861 : Blo 603293 682861 := bbase (se 3 (by rfl) ⟨128036, by rfl⟩ : syracuseStep 682861 = 256073) (by norm_num)
theorem B682897 : Blo 603293 682897 := bbase (se 2 (by rfl) ⟨256086, by rfl⟩ : syracuseStep 682897 = 512173) (by norm_num)
theorem B682933 : Blo 603293 682933 := bbase (se 5 (by rfl) ⟨32012, by rfl⟩ : syracuseStep 682933 = 64025) (by norm_num)
theorem B1534909 : Blo 603293 1534909 := bbase (se 3 (by rfl) ⟨287795, by rfl⟩ : syracuseStep 1534909 = 575591) (by norm_num)
theorem B682969 : Blo 603293 682969 := bbase (se 2 (by rfl) ⟨256113, by rfl⟩ : syracuseStep 682969 = 512227) (by norm_num)
theorem B683005 : Blo 603293 683005 := bbase (se 3 (by rfl) ⟨128063, by rfl⟩ : syracuseStep 683005 = 256127) (by norm_num)
theorem B683041 : Blo 603293 683041 := bbase (se 2 (by rfl) ⟨256140, by rfl⟩ : syracuseStep 683041 = 512281) (by norm_num)
theorem B1535021 : Blo 603293 1535021 := bbase (se 3 (by rfl) ⟨287816, by rfl⟩ : syracuseStep 1535021 = 575633) (by norm_num)
theorem B683077 : Blo 603293 683077 := bbase (se 4 (by rfl) ⟨64038, by rfl⟩ : syracuseStep 683077 = 128077) (by norm_num)
theorem B683113 : Blo 603293 683113 := bbase (se 2 (by rfl) ⟨256167, by rfl⟩ : syracuseStep 683113 = 512335) (by norm_num)
theorem B683149 : Blo 603293 683149 := bbase (se 3 (by rfl) ⟨128090, by rfl⟩ : syracuseStep 683149 = 256181) (by norm_num)
theorem B683185 : Blo 603293 683185 := bbase (se 2 (by rfl) ⟨256194, by rfl⟩ : syracuseStep 683185 = 512389) (by norm_num)
theorem B1535213 : Blo 603293 1535213 := bbase (se 3 (by rfl) ⟨287852, by rfl⟩ : syracuseStep 1535213 = 575705) (by norm_num)
theorem B6909461 : Blo 603293 6909461 := bbase (se 6 (by rfl) ⟨161940, by rfl⟩ : syracuseStep 6909461 = 323881) (by norm_num)
theorem B1535557 : Blo 603293 1535557 := bbase (se 4 (by rfl) ⟨143958, by rfl⟩ : syracuseStep 1535557 = 287917) (by norm_num)
theorem B2944613 : Blo 603293 2944613 := bbase (se 4 (by rfl) ⟨276057, by rfl⟩ : syracuseStep 2944613 = 552115) (by norm_num)
theorem B1961621 : Blo 603293 1961621 := bbase (se 6 (by rfl) ⟨45975, by rfl⟩ : syracuseStep 1961621 = 91951) (by norm_num)
theorem B1535669 : Blo 603293 1535669 := bbase (se 5 (by rfl) ⟨71984, by rfl⟩ : syracuseStep 1535669 = 143969) (by norm_num)
theorem B1535861 : Blo 603293 1535861 := bbase (se 5 (by rfl) ⟨71993, by rfl⟩ : syracuseStep 1535861 = 143987) (by norm_num)
theorem B3502037 : Blo 603293 3502037 := bbase (se 7 (by rfl) ⟨41039, by rfl⟩ : syracuseStep 3502037 = 82079) (by norm_num)
theorem B5828597 : Blo 603293 5828597 := bbase (se 5 (by rfl) ⟨273215, by rfl⟩ : syracuseStep 5828597 = 546431) (by norm_num)
theorem B1536205 : Blo 603293 1536205 := bbase (se 3 (by rfl) ⟨288038, by rfl⟩ : syracuseStep 1536205 = 576077) (by norm_num)
theorem B1536317 : Blo 603293 1536317 := bbase (se 3 (by rfl) ⟨288059, by rfl⟩ : syracuseStep 1536317 = 576119) (by norm_num)
theorem B717209 : Blo 603293 717209 := bbase (se 2 (by rfl) ⟨268953, by rfl⟩ : syracuseStep 717209 = 537907) (by norm_num)
theorem B1536509 : Blo 603293 1536509 := bbase (se 3 (by rfl) ⟨288095, by rfl⟩ : syracuseStep 1536509 = 576191) (by norm_num)
theorem B1766021 : Blo 603293 1766021 := bbase (se 4 (by rfl) ⟨165564, by rfl⟩ : syracuseStep 1766021 = 331129) (by norm_num)
theorem B2585429 : Blo 603293 2585429 := bbase (se 9 (by rfl) ⟨7574, by rfl⟩ : syracuseStep 2585429 = 15149) (by norm_num)
theorem B13103957 : Blo 603293 13103957 := bbase (se 9 (by rfl) ⟨38390, by rfl⟩ : syracuseStep 13103957 = 76781) (by norm_num)
theorem B1536853 : Blo 603293 1536853 := bbase (se 9 (by rfl) ⟨4502, by rfl⟩ : syracuseStep 1536853 = 9005) (by norm_num)
theorem B2913221 : Blo 603293 2913221 := bbase (se 4 (by rfl) ⟨273114, by rfl⟩ : syracuseStep 2913221 = 546229) (by norm_num)
theorem B1536965 : Blo 603293 1536965 := bbase (se 4 (by rfl) ⟨144090, by rfl⟩ : syracuseStep 1536965 = 288181) (by norm_num)
theorem B4584437 : Blo 603293 4584437 := bbase (se 5 (by rfl) ⟨214895, by rfl⟩ : syracuseStep 4584437 = 429791) (by norm_num)
theorem B2913317 : Blo 603293 2913317 := bbase (se 4 (by rfl) ⟨273123, by rfl⟩ : syracuseStep 2913317 = 546247) (by norm_num)
theorem B5534837 : Blo 603293 5534837 := bbase (se 5 (by rfl) ⟨259445, by rfl⟩ : syracuseStep 5534837 = 518891) (by norm_num)
theorem B1537157 : Blo 603293 1537157 := bbase (se 4 (by rfl) ⟨144108, by rfl⟩ : syracuseStep 1537157 = 288217) (by norm_num)
theorem B1766677 : Blo 603293 1766677 := bbase (se 6 (by rfl) ⟨41406, by rfl⟩ : syracuseStep 1766677 = 82813) (by norm_num)
theorem B2291125 : Blo 603293 2291125 := bbase (se 5 (by rfl) ⟨107396, by rfl⟩ : syracuseStep 2291125 = 214793) (by norm_num)
theorem B816581 : Blo 603293 816581 := bbase (se 4 (by rfl) ⟨76554, by rfl⟩ : syracuseStep 816581 = 153109) (by norm_num)
theorem B2291429 : Blo 603293 2291429 := bbase (se 4 (by rfl) ⟨214821, by rfl⟩ : syracuseStep 2291429 = 429643) (by norm_num)
theorem B2586437 : Blo 603293 2586437 := bbase (se 4 (by rfl) ⟨242478, by rfl⟩ : syracuseStep 2586437 = 484957) (by norm_num)
theorem B4913237 : Blo 603293 4913237 := bbase (se 8 (by rfl) ⟨28788, by rfl⟩ : syracuseStep 4913237 = 57577) (by norm_num)
theorem B4421749 : Blo 603293 4421749 := bbase (se 5 (by rfl) ⟨207269, by rfl⟩ : syracuseStep 4421749 = 414539) (by norm_num)
theorem B1964245 : Blo 603293 1964245 := bbase (se 7 (by rfl) ⟨23018, by rfl⟩ : syracuseStep 1964245 = 46037) (by norm_num)
theorem B817381 : Blo 603293 817381 := bbase (se 4 (by rfl) ⟨76629, by rfl⟩ : syracuseStep 817381 = 153259) (by norm_num)
theorem B1243853 : Blo 603293 1243853 := bbase (se 3 (by rfl) ⟨233222, by rfl⟩ : syracuseStep 1243853 = 466445) (by norm_num)
theorem B1145677 : Blo 603293 1145677 := bbase (se 3 (by rfl) ⟨214814, by rfl⟩ : syracuseStep 1145677 = 429629) (by norm_num)
theorem B2915237 : Blo 603293 2915237 := bbase (se 4 (by rfl) ⟨273303, by rfl⟩ : syracuseStep 2915237 = 546607) (by norm_num)
theorem B1145821 : Blo 603293 1145821 := bbase (se 3 (by rfl) ⟨214841, by rfl⟩ : syracuseStep 1145821 = 429683) (by norm_num)
theorem B818149 : Blo 603293 818149 := bbase (se 4 (by rfl) ⟨76701, by rfl⟩ : syracuseStep 818149 = 153403) (by norm_num)
theorem B1145981 : Blo 603293 1145981 := bbase (se 3 (by rfl) ⟨214871, by rfl⟩ : syracuseStep 1145981 = 429743) (by norm_num)
theorem B1637509 : Blo 603293 1637509 := bbase (se 4 (by rfl) ⟨153516, by rfl⟩ : syracuseStep 1637509 = 307033) (by norm_num)
theorem B1146125 : Blo 603293 1146125 := bbase (se 3 (by rfl) ⟨214898, by rfl⟩ : syracuseStep 1146125 = 429797) (by norm_num)
theorem B785857 : Blo 603293 785857 := bbase (se 2 (by rfl) ⟨294696, by rfl⟩ : syracuseStep 785857 = 589393) (by norm_num)
theorem B3866069 : Blo 603293 3866069 := bbase (se 7 (by rfl) ⟨45305, by rfl⟩ : syracuseStep 3866069 = 90611) (by norm_num)
theorem B1146413 : Blo 603293 1146413 := bbase (se 3 (by rfl) ⟨214952, by rfl⟩ : syracuseStep 1146413 = 429905) (by norm_num)
theorem B2588213 : Blo 603293 2588213 := bbase (se 5 (by rfl) ⟨121322, by rfl⟩ : syracuseStep 2588213 = 242645) (by norm_num)
theorem B1146565 : Blo 603293 1146565 := bbase (se 4 (by rfl) ⟨107490, by rfl⟩ : syracuseStep 1146565 = 214981) (by norm_num)
theorem B1375957 : Blo 603293 1375957 := bbase (se 7 (by rfl) ⟨16124, by rfl⟩ : syracuseStep 1375957 = 32249) (by norm_num)
theorem B2293541 : Blo 603293 2293541 := bbase (se 4 (by rfl) ⟨215019, by rfl⟩ : syracuseStep 2293541 = 430039) (by norm_num)
theorem B819085 : Blo 603293 819085 := bbase (se 3 (by rfl) ⟨153578, by rfl⟩ : syracuseStep 819085 = 307157) (by norm_num)
theorem B1146869 : Blo 603293 1146869 := bbase (se 5 (by rfl) ⟨53759, by rfl⟩ : syracuseStep 1146869 = 107519) (by norm_num)
theorem B2293859 : Blo 603293 2293859 := bstep (se 1 (by rfl) ⟨1720394, by rfl⟩ : syracuseStep 2293859 = 3440789) B3440789
theorem B3866737 : Blo 603293 3866737 := bstep (se 2 (by rfl) ⟨1450026, by rfl⟩ : syracuseStep 3866737 = 2900053) B2900053
theorem B4915313 : Blo 603293 4915313 := bstep (se 2 (by rfl) ⟨1843242, by rfl⟩ : syracuseStep 4915313 = 3686485) B3686485
theorem B4128965 : Blo 603293 4128965 := bstep (se 4 (by rfl) ⟨387090, by rfl⟩ : syracuseStep 4128965 = 774181) B774181
theorem B2064781 : Blo 603293 2064781 := bstep (se 3 (by rfl) ⟨387146, by rfl⟩ : syracuseStep 2064781 = 774293) B774293
theorem B1638893 : Blo 603293 1638893 := bstep (se 3 (by rfl) ⟨307292, by rfl⟩ : syracuseStep 1638893 = 614585) B614585
theorem B1639043 : Blo 603293 1639043 := bstep (se 1 (by rfl) ⟨1229282, by rfl⟩ : syracuseStep 1639043 = 2458565) B2458565
theorem B1147537 : Blo 603293 1147537 := bstep (se 2 (by rfl) ⟨430326, by rfl⟩ : syracuseStep 1147537 = 860653) B860653
theorem B2294513 : Blo 603293 2294513 := bstep (se 2 (by rfl) ⟨860442, by rfl⟩ : syracuseStep 2294513 = 1720885) B1720885
theorem B1639217 : Blo 603293 1639217 := bstep (se 2 (by rfl) ⟨614706, by rfl⟩ : syracuseStep 1639217 = 1229413) B1229413
theorem B1934189 : Blo 603293 1934189 := bstep (se 3 (by rfl) ⟨362660, by rfl⟩ : syracuseStep 1934189 = 725321) B725321
theorem B1868689 : Blo 603293 1868689 := bstep (se 2 (by rfl) ⟨700758, by rfl⟩ : syracuseStep 1868689 = 1401517) B1401517
theorem B689059 : Blo 603293 689059 := bstep (se 1 (by rfl) ⟨516794, by rfl⟩ : syracuseStep 689059 = 1033589) B1033589
theorem B4359365 : Blo 603293 4359365 := bstep (se 4 (by rfl) ⟨408690, by rfl⟩ : syracuseStep 4359365 = 817381) B817381
theorem B918947 : Blo 603293 918947 := bstep (se 1 (by rfl) ⟨689210, by rfl⟩ : syracuseStep 918947 = 1378421) B1378421
theorem B2328113 : Blo 603293 2328113 := bstep (se 2 (by rfl) ⟨873042, by rfl⟩ : syracuseStep 2328113 = 1746085) B1746085
theorem B656947 : Blo 603293 656947 := bstep (se 1 (by rfl) ⟨492710, by rfl⟩ : syracuseStep 656947 = 985421) B985421
theorem B1148593 : Blo 603293 1148593 := bstep (se 2 (by rfl) ⟨430722, by rfl⟩ : syracuseStep 1148593 = 861445) B861445
theorem B1935085 : Blo 603293 1935085 := bstep (se 3 (by rfl) ⟨362828, by rfl⟩ : syracuseStep 1935085 = 725657) B725657
theorem B4589297 : Blo 603293 4589297 := bstep (se 2 (by rfl) ⟨1720986, by rfl⟩ : syracuseStep 4589297 = 3441973) B3441973
theorem B1148995 : Blo 603293 1148995 := bstep (se 1 (by rfl) ⟨861746, by rfl⟩ : syracuseStep 1148995 = 1723493) B1723493
theorem B1149041 : Blo 603293 1149041 := bstep (se 2 (by rfl) ⟨430890, by rfl⟩ : syracuseStep 1149041 = 861781) B861781
theorem B1837201 : Blo 603293 1837201 := bstep (se 2 (by rfl) ⟨688950, by rfl⟩ : syracuseStep 1837201 = 1377901) B1377901
theorem B2295971 : Blo 603293 2295971 := bstep (se 1 (by rfl) ⟨1721978, by rfl⟩ : syracuseStep 2295971 = 3443957) B3443957
theorem B2295985 : Blo 603293 2295985 := bstep (se 2 (by rfl) ⟨860994, by rfl⟩ : syracuseStep 2295985 = 1721989) B1721989
theorem B6621425 : Blo 603293 6621425 := bstep (se 2 (by rfl) ⟨2483034, by rfl⟩ : syracuseStep 6621425 = 4966069) B4966069
theorem B1018129 : Blo 603293 1018129 := bstep (se 2 (by rfl) ⟨381798, by rfl⟩ : syracuseStep 1018129 = 763597) B763597
theorem B1181969 : Blo 603293 1181969 := bstep (se 2 (by rfl) ⟨443238, by rfl⟩ : syracuseStep 1181969 = 886477) B886477
theorem B1018163 : Blo 603293 1018163 := bstep (se 1 (by rfl) ⟨763622, by rfl⟩ : syracuseStep 1018163 = 1527245) B1527245
theorem B1149329 : Blo 603293 1149329 := bstep (se 2 (by rfl) ⟨430998, by rfl⟩ : syracuseStep 1149329 = 861997) B861997
theorem B887203 : Blo 603293 887203 := bstep (se 1 (by rfl) ⟨665402, by rfl⟩ : syracuseStep 887203 = 1330805) B1330805
theorem B1018291 : Blo 603293 1018291 := bstep (se 1 (by rfl) ⟨763718, by rfl⟩ : syracuseStep 1018291 = 1527437) B1527437
theorem B3443249 : Blo 603293 3443249 := bstep (se 2 (by rfl) ⟨1291218, by rfl⟩ : syracuseStep 3443249 = 2582437) B2582437
theorem B1018433 : Blo 603293 1018433 := bstep (se 2 (by rfl) ⟨381912, by rfl⟩ : syracuseStep 1018433 = 763825) B763825
theorem B1018561 : Blo 603293 1018561 := bstep (se 2 (by rfl) ⟨381960, by rfl⟩ : syracuseStep 1018561 = 763921) B763921
theorem B1018595 : Blo 603293 1018595 := bstep (se 1 (by rfl) ⟨763946, by rfl⟩ : syracuseStep 1018595 = 1527893) B1527893
theorem B2591459 : Blo 603293 2591459 := bstep (se 1 (by rfl) ⟨1943594, by rfl⟩ : syracuseStep 2591459 = 3887189) B3887189
theorem B1936163 : Blo 603293 1936163 := bstep (se 1 (by rfl) ⟨1452122, by rfl⟩ : syracuseStep 1936163 = 2904245) B2904245
theorem B1641293 : Blo 603293 1641293 := bstep (se 3 (by rfl) ⟨307742, by rfl⟩ : syracuseStep 1641293 = 615485) B615485
theorem B1018723 : Blo 603293 1018723 := bstep (se 1 (by rfl) ⟨764042, by rfl⟩ : syracuseStep 1018723 = 1528085) B1528085
theorem B1018865 : Blo 603293 1018865 := bstep (se 2 (by rfl) ⟨382074, by rfl⟩ : syracuseStep 1018865 = 764149) B764149
theorem B1150051 : Blo 603293 1150051 := bstep (se 1 (by rfl) ⟨862538, by rfl⟩ : syracuseStep 1150051 = 1725077) B1725077
theorem B1018993 : Blo 603293 1018993 := bstep (se 2 (by rfl) ⟨382122, by rfl⟩ : syracuseStep 1018993 = 764245) B764245
theorem B1019027 : Blo 603293 1019027 := bstep (se 1 (by rfl) ⟨764270, by rfl⟩ : syracuseStep 1019027 = 1528541) B1528541
theorem B691363 : Blo 603293 691363 := bstep (se 1 (by rfl) ⟨518522, by rfl⟩ : syracuseStep 691363 = 1037045) B1037045
theorem B2067725 : Blo 603293 2067725 := bstep (se 3 (by rfl) ⟨387698, by rfl⟩ : syracuseStep 2067725 = 775397) B775397
theorem B1019155 : Blo 603293 1019155 := bstep (se 1 (by rfl) ⟨764366, by rfl⟩ : syracuseStep 1019155 = 1528733) B1528733
theorem B1051969 : Blo 603293 1051969 := bstep (se 2 (by rfl) ⟨394488, by rfl⟩ : syracuseStep 1051969 = 788977) B788977
theorem B1019297 : Blo 603293 1019297 := bstep (se 2 (by rfl) ⟨382236, by rfl⟩ : syracuseStep 1019297 = 764473) B764473
theorem B1936817 : Blo 603293 1936817 := bstep (se 2 (by rfl) ⟨726306, by rfl⟩ : syracuseStep 1936817 = 1452613) B1452613
theorem B1019425 : Blo 603293 1019425 := bstep (se 2 (by rfl) ⟨382284, by rfl⟩ : syracuseStep 1019425 = 764569) B764569
theorem B2330147 : Blo 603293 2330147 := bstep (se 1 (by rfl) ⟨1747610, by rfl⟩ : syracuseStep 2330147 = 3495221) B3495221
theorem B1150499 : Blo 603293 1150499 := bstep (se 1 (by rfl) ⟨862874, by rfl⟩ : syracuseStep 1150499 = 1725749) B1725749
theorem B1019459 : Blo 603293 1019459 := bstep (se 1 (by rfl) ⟨764594, by rfl⟩ : syracuseStep 1019459 = 1529189) B1529189
theorem B2297443 : Blo 603293 2297443 := bstep (se 1 (by rfl) ⟨1723082, by rfl⟩ : syracuseStep 2297443 = 3446165) B3446165
theorem B1019587 : Blo 603293 1019587 := bstep (se 1 (by rfl) ⟨764690, by rfl⟩ : syracuseStep 1019587 = 1529381) B1529381
theorem B7737059 : Blo 603293 7737059 := bstep (se 1 (by rfl) ⟨5802794, by rfl⟩ : syracuseStep 7737059 = 11605589) B11605589
theorem B1150787 : Blo 603293 1150787 := bstep (se 1 (by rfl) ⟨863090, by rfl⟩ : syracuseStep 1150787 = 1726181) B1726181
theorem B1019729 : Blo 603293 1019729 := bstep (se 2 (by rfl) ⟨382398, by rfl⟩ : syracuseStep 1019729 = 764797) B764797
theorem B8753093 : Blo 603293 8753093 := bstep (se 4 (by rfl) ⟨820602, by rfl⟩ : syracuseStep 8753093 = 1641205) B1641205
theorem B1019857 : Blo 603293 1019857 := bstep (se 2 (by rfl) ⟨382446, by rfl⟩ : syracuseStep 1019857 = 764893) B764893
theorem B3444707 : Blo 603293 3444707 := bstep (se 1 (by rfl) ⟨2583530, by rfl⟩ : syracuseStep 3444707 = 5167061) B5167061
theorem B8851427 : Blo 603293 8851427 := bstep (se 1 (by rfl) ⟨6638570, by rfl⟩ : syracuseStep 8851427 = 13277141) B13277141
theorem B1871843 : Blo 603293 1871843 := bstep (se 1 (by rfl) ⟨1403882, by rfl⟩ : syracuseStep 1871843 = 2807765) B2807765
theorem B1019891 : Blo 603293 1019891 := bstep (se 1 (by rfl) ⟨764918, by rfl⟩ : syracuseStep 1019891 = 1529837) B1529837
theorem B1020019 : Blo 603293 1020019 := bstep (se 1 (by rfl) ⟨765014, by rfl⟩ : syracuseStep 1020019 = 1530029) B1530029
theorem B11079821 : Blo 603293 11079821 := bstep (se 3 (by rfl) ⟨2077466, by rfl⟩ : syracuseStep 11079821 = 4154933) B4154933
theorem B1020161 : Blo 603293 1020161 := bstep (se 2 (by rfl) ⟨382560, by rfl⟩ : syracuseStep 1020161 = 765121) B765121
theorem B1020289 : Blo 603293 1020289 := bstep (se 2 (by rfl) ⟨382608, by rfl⟩ : syracuseStep 1020289 = 765217) B765217
theorem B1020323 : Blo 603293 1020323 := bstep (se 1 (by rfl) ⟨765242, by rfl⟩ : syracuseStep 1020323 = 1530485) B1530485
theorem B14913989 : Blo 603293 14913989 := bstep (se 4 (by rfl) ⟨1398186, by rfl⟩ : syracuseStep 14913989 = 2796373) B2796373
theorem B5181893 : Blo 603293 5181893 := bstep (se 4 (by rfl) ⟨485802, by rfl⟩ : syracuseStep 5181893 = 971605) B971605
theorem B2036177 : Blo 603293 2036177 := bstep (se 2 (by rfl) ⟨763566, by rfl⟩ : syracuseStep 2036177 = 1527133) B1527133
theorem B1020451 : Blo 603293 1020451 := bstep (se 1 (by rfl) ⟨765338, by rfl⟩ : syracuseStep 1020451 = 1530677) B1530677
theorem B1020593 : Blo 603293 1020593 := bstep (se 2 (by rfl) ⟨382722, by rfl⟩ : syracuseStep 1020593 = 765445) B765445
theorem B6197957 : Blo 603293 6197957 := bstep (se 4 (by rfl) ⟨581058, by rfl⟩ : syracuseStep 6197957 = 1162117) B1162117
theorem B1938161 : Blo 603293 1938161 := bstep (se 2 (by rfl) ⟨726810, by rfl⟩ : syracuseStep 1938161 = 1453621) B1453621
theorem B1151729 : Blo 603293 1151729 := bstep (se 2 (by rfl) ⟨431898, by rfl⟩ : syracuseStep 1151729 = 863797) B863797
theorem B1020721 : Blo 603293 1020721 := bstep (se 2 (by rfl) ⟨382770, by rfl⟩ : syracuseStep 1020721 = 765541) B765541
theorem B1020755 : Blo 603293 1020755 := bstep (se 1 (by rfl) ⟨765566, by rfl⟩ : syracuseStep 1020755 = 1531133) B1531133
theorem B1381265 : Blo 603293 1381265 := bstep (se 2 (by rfl) ⟨517974, by rfl⟩ : syracuseStep 1381265 = 1035949) B1035949
theorem B1020883 : Blo 603293 1020883 := bstep (se 1 (by rfl) ⟨765662, by rfl⟩ : syracuseStep 1020883 = 1531325) B1531325
theorem B2036717 : Blo 603293 2036717 := bstep (se 3 (by rfl) ⟨381884, by rfl⟩ : syracuseStep 2036717 = 763769) B763769
theorem B2036771 : Blo 603293 2036771 := bstep (se 1 (by rfl) ⟨1527578, by rfl⟩ : syracuseStep 2036771 = 3055157) B3055157
theorem B1021025 : Blo 603293 1021025 := bstep (se 2 (by rfl) ⟨382884, by rfl⟩ : syracuseStep 1021025 = 765769) B765769
theorem B1021153 : Blo 603293 1021153 := bstep (se 2 (by rfl) ⟨382932, by rfl⟩ : syracuseStep 1021153 = 765865) B765865
theorem B1021187 : Blo 603293 1021187 := bstep (se 1 (by rfl) ⟨765890, by rfl⟩ : syracuseStep 1021187 = 1531781) B1531781
theorem B2037041 : Blo 603293 2037041 := bstep (se 2 (by rfl) ⟨763890, by rfl⟩ : syracuseStep 2037041 = 1527781) B1527781
theorem B3872069 : Blo 603293 3872069 := bstep (se 4 (by rfl) ⟨363006, by rfl⟩ : syracuseStep 3872069 = 726013) B726013
theorem B1021315 : Blo 603293 1021315 := bstep (se 1 (by rfl) ⟨765986, by rfl⟩ : syracuseStep 1021315 = 1531973) B1531973
theorem B1021457 : Blo 603293 1021457 := bstep (se 2 (by rfl) ⟨383046, by rfl⟩ : syracuseStep 1021457 = 766093) B766093
theorem B1152625 : Blo 603293 1152625 := bstep (se 2 (by rfl) ⟨432234, by rfl⟩ : syracuseStep 1152625 = 864469) B864469
theorem B1021585 : Blo 603293 1021585 := bstep (se 2 (by rfl) ⟨383094, by rfl⟩ : syracuseStep 1021585 = 766189) B766189
theorem B1021619 : Blo 603293 1021619 := bstep (se 1 (by rfl) ⟨766214, by rfl⟩ : syracuseStep 1021619 = 1532429) B1532429
theorem B2299661 : Blo 603293 2299661 := bstep (se 3 (by rfl) ⟨431186, by rfl⟩ : syracuseStep 2299661 = 862373) B862373
theorem B1152785 : Blo 603293 1152785 := bstep (se 2 (by rfl) ⟨432294, by rfl⟩ : syracuseStep 1152785 = 864589) B864589
theorem B1021747 : Blo 603293 1021747 := bstep (se 1 (by rfl) ⟨766310, by rfl⟩ : syracuseStep 1021747 = 1532621) B1532621
theorem B2037581 : Blo 603293 2037581 := bstep (se 3 (by rfl) ⟨382046, by rfl⟩ : syracuseStep 2037581 = 764093) B764093
theorem B1939277 : Blo 603293 1939277 := bstep (se 3 (by rfl) ⟨363614, by rfl⟩ : syracuseStep 1939277 = 727229) B727229
theorem B2037635 : Blo 603293 2037635 := bstep (se 1 (by rfl) ⟨1528226, by rfl⟩ : syracuseStep 2037635 = 3056453) B3056453
theorem B1021889 : Blo 603293 1021889 := bstep (se 2 (by rfl) ⟨383208, by rfl⟩ : syracuseStep 1021889 = 766417) B766417
theorem B2758627 : Blo 603293 2758627 := bstep (se 1 (by rfl) ⟨2068970, by rfl⟩ : syracuseStep 2758627 = 4137941) B4137941
theorem B727075 : Blo 603293 727075 := bstep (se 1 (by rfl) ⟨545306, by rfl⟩ : syracuseStep 727075 = 1090613) B1090613
theorem B1022017 : Blo 603293 1022017 := bstep (se 2 (by rfl) ⟨383256, by rfl⟩ : syracuseStep 1022017 = 766513) B766513
theorem B1022051 : Blo 603293 1022051 := bstep (se 1 (by rfl) ⟨766538, by rfl⟩ : syracuseStep 1022051 = 1533077) B1533077
theorem B13080689 : Blo 603293 13080689 := bstep (se 2 (by rfl) ⟨4905258, by rfl⟩ : syracuseStep 13080689 = 9810517) B9810517
theorem B2037905 : Blo 603293 2037905 := bstep (se 2 (by rfl) ⟨764214, by rfl⟩ : syracuseStep 2037905 = 1528429) B1528429
theorem B1022179 : Blo 603293 1022179 := bstep (se 1 (by rfl) ⟨766634, by rfl⟩ : syracuseStep 1022179 = 1533269) B1533269
theorem B1022209 : Blo 603293 1022209 := bstep (se 2 (by rfl) ⟨383328, by rfl⟩ : syracuseStep 1022209 = 766657) B766657
theorem B1022321 : Blo 603293 1022321 := bstep (se 2 (by rfl) ⟨383370, by rfl⟩ : syracuseStep 1022321 = 766741) B766741
theorem B1022449 : Blo 603293 1022449 := bstep (se 2 (by rfl) ⟨383418, by rfl⟩ : syracuseStep 1022449 = 766837) B766837
theorem B1022483 : Blo 603293 1022483 := bstep (se 1 (by rfl) ⟨766862, by rfl⟩ : syracuseStep 1022483 = 1533725) B1533725
theorem B1022611 : Blo 603293 1022611 := bstep (se 1 (by rfl) ⟨766958, by rfl⟩ : syracuseStep 1022611 = 1533917) B1533917
theorem B2038445 : Blo 603293 2038445 := bstep (se 3 (by rfl) ⟨382208, by rfl⟩ : syracuseStep 2038445 = 764417) B764417
theorem B2038499 : Blo 603293 2038499 := bstep (se 1 (by rfl) ⟨1528874, by rfl⟩ : syracuseStep 2038499 = 3057749) B3057749
theorem B1022753 : Blo 603293 1022753 := bstep (se 2 (by rfl) ⟨383532, by rfl⟩ : syracuseStep 1022753 = 767065) B767065
theorem B1940365 : Blo 603293 1940365 := bstep (se 3 (by rfl) ⟨363818, by rfl⟩ : syracuseStep 1940365 = 727637) B727637
theorem B1022881 : Blo 603293 1022881 := bstep (se 2 (by rfl) ⟨383580, by rfl⟩ : syracuseStep 1022881 = 767161) B767161
theorem B1022915 : Blo 603293 1022915 := bstep (se 1 (by rfl) ⟨767186, by rfl⟩ : syracuseStep 1022915 = 1534373) B1534373
theorem B31562693 : Blo 603293 31562693 := bstep (se 4 (by rfl) ⟨2959002, by rfl⟩ : syracuseStep 31562693 = 5918005) B5918005
theorem B2038769 : Blo 603293 2038769 := bstep (se 2 (by rfl) ⟨764538, by rfl⟩ : syracuseStep 2038769 = 1529077) B1529077
theorem B1023043 : Blo 603293 1023043 := bstep (se 1 (by rfl) ⟨767282, by rfl⟩ : syracuseStep 1023043 = 1534565) B1534565
theorem B1023185 : Blo 603293 1023185 := bstep (se 2 (by rfl) ⟨383694, by rfl⟩ : syracuseStep 1023185 = 767389) B767389
theorem B3054833 : Blo 603293 3054833 := bstep (se 2 (by rfl) ⟨1145562, by rfl⟩ : syracuseStep 3054833 = 2291125) B2291125
theorem B859457 : Blo 603293 859457 := bstep (se 2 (by rfl) ⟨322296, by rfl⟩ : syracuseStep 859457 = 644593) B644593
theorem B1023313 : Blo 603293 1023313 := bstep (se 2 (by rfl) ⟨383742, by rfl⟩ : syracuseStep 1023313 = 767485) B767485
theorem B1023347 : Blo 603293 1023347 := bstep (se 1 (by rfl) ⟨767510, by rfl⟩ : syracuseStep 1023347 = 1535021) B1535021
theorem B1383857 : Blo 603293 1383857 := bstep (se 2 (by rfl) ⟨518946, by rfl⟩ : syracuseStep 1383857 = 1037893) B1037893
theorem B1023475 : Blo 603293 1023475 := bstep (se 1 (by rfl) ⟨767606, by rfl⟩ : syracuseStep 1023475 = 1535213) B1535213
theorem B2039309 : Blo 603293 2039309 := bstep (se 3 (by rfl) ⟨382370, by rfl⟩ : syracuseStep 2039309 = 764741) B764741
theorem B2039363 : Blo 603293 2039363 := bstep (se 1 (by rfl) ⟨1529522, by rfl⟩ : syracuseStep 2039363 = 3059045) B3059045
theorem B1023617 : Blo 603293 1023617 := bstep (se 2 (by rfl) ⟨383856, by rfl⟩ : syracuseStep 1023617 = 767713) B767713
theorem B728771 : Blo 603293 728771 := bstep (se 1 (by rfl) ⟨546578, by rfl⟩ : syracuseStep 728771 = 1093157) B1093157
theorem B5119685 : Blo 603293 5119685 := bstep (se 4 (by rfl) ⟨479970, by rfl⟩ : syracuseStep 5119685 = 959941) B959941
theorem B1023745 : Blo 603293 1023745 := bstep (se 2 (by rfl) ⟨383904, by rfl⟩ : syracuseStep 1023745 = 767809) B767809
theorem B7773965 : Blo 603293 7773965 := bstep (se 3 (by rfl) ⟨1457618, by rfl⟩ : syracuseStep 7773965 = 2915237) B2915237
theorem B1023779 : Blo 603293 1023779 := bstep (se 1 (by rfl) ⟨767834, by rfl⟩ : syracuseStep 1023779 = 1535669) B1535669
theorem B2039633 : Blo 603293 2039633 := bstep (se 2 (by rfl) ⟨764862, by rfl⟩ : syracuseStep 2039633 = 1529725) B1529725
theorem B859987 : Blo 603293 859987 := bstep (se 1 (by rfl) ⟨644990, by rfl⟩ : syracuseStep 859987 = 1289981) B1289981
theorem B1023907 : Blo 603293 1023907 := bstep (se 1 (by rfl) ⟨767930, by rfl⟩ : syracuseStep 1023907 = 1535861) B1535861
theorem B2334691 : Blo 603293 2334691 := bstep (se 1 (by rfl) ⟨1751018, by rfl⟩ : syracuseStep 2334691 = 3502037) B3502037
theorem B1024049 : Blo 603293 1024049 := bstep (se 2 (by rfl) ⟨384018, by rfl⟩ : syracuseStep 1024049 = 768037) B768037
theorem B860323 : Blo 603293 860323 := bstep (se 1 (by rfl) ⟨645242, by rfl⟩ : syracuseStep 860323 = 1290485) B1290485
theorem B1024177 : Blo 603293 1024177 := bstep (se 2 (by rfl) ⟨384066, by rfl⟩ : syracuseStep 1024177 = 768133) B768133
theorem B1024211 : Blo 603293 1024211 := bstep (se 1 (by rfl) ⟨768158, by rfl⟩ : syracuseStep 1024211 = 1536317) B1536317
theorem B1024339 : Blo 603293 1024339 := bstep (se 1 (by rfl) ⟨768254, by rfl⟩ : syracuseStep 1024339 = 1536509) B1536509
theorem B2040173 : Blo 603293 2040173 := bstep (se 3 (by rfl) ⟨382532, by rfl⟩ : syracuseStep 2040173 = 765065) B765065
theorem B2040227 : Blo 603293 2040227 := bstep (se 1 (by rfl) ⟨1530170, by rfl⟩ : syracuseStep 2040227 = 3060341) B3060341
theorem B1024481 : Blo 603293 1024481 := bstep (se 2 (by rfl) ⟨384180, by rfl⟩ : syracuseStep 1024481 = 768361) B768361
theorem B1516099 : Blo 603293 1516099 := bstep (se 1 (by rfl) ⟨1137074, by rfl⟩ : syracuseStep 1516099 = 2274149) B2274149
theorem B1024609 : Blo 603293 1024609 := bstep (se 2 (by rfl) ⟨384228, by rfl⟩ : syracuseStep 1024609 = 768457) B768457
theorem B2302577 : Blo 603293 2302577 := bstep (se 2 (by rfl) ⟨863466, by rfl⟩ : syracuseStep 2302577 = 1726933) B1726933
theorem B1942147 : Blo 603293 1942147 := bstep (se 1 (by rfl) ⟨1456610, by rfl⟩ : syracuseStep 1942147 = 2913221) B2913221
theorem B1024643 : Blo 603293 1024643 := bstep (se 1 (by rfl) ⟨768482, by rfl⟩ : syracuseStep 1024643 = 1536965) B1536965
theorem B3056291 : Blo 603293 3056291 := bstep (se 1 (by rfl) ⟨2292218, by rfl⟩ : syracuseStep 3056291 = 4584437) B4584437
theorem B2040497 : Blo 603293 2040497 := bstep (se 2 (by rfl) ⟨765186, by rfl⟩ : syracuseStep 2040497 = 1530373) B1530373
theorem B1942211 : Blo 603293 1942211 := bstep (se 1 (by rfl) ⟨1456658, by rfl⟩ : syracuseStep 1942211 = 2913317) B2913317
theorem B860881 : Blo 603293 860881 := bstep (se 2 (by rfl) ⟨322830, by rfl⟩ : syracuseStep 860881 = 645661) B645661
theorem B1843949 : Blo 603293 1843949 := bstep (se 3 (by rfl) ⟨345740, by rfl⟩ : syracuseStep 1843949 = 691481) B691481
theorem B860915 : Blo 603293 860915 := bstep (se 1 (by rfl) ⟨645686, by rfl⟩ : syracuseStep 860915 = 1291373) B1291373
theorem B1024771 : Blo 603293 1024771 := bstep (se 1 (by rfl) ⟨768578, by rfl⟩ : syracuseStep 1024771 = 1537157) B1537157
theorem B1942289 : Blo 603293 1942289 := bstep (se 2 (by rfl) ⟨728358, by rfl⟩ : syracuseStep 1942289 = 1456717) B1456717
theorem B4662257 : Blo 603293 4662257 := bstep (se 2 (by rfl) ⟨1748346, by rfl⟩ : syracuseStep 4662257 = 3496693) B3496693
theorem B3941453 : Blo 603293 3941453 := bstep (se 3 (by rfl) ⟨739022, by rfl⟩ : syracuseStep 3941453 = 1478045) B1478045
theorem B2041037 : Blo 603293 2041037 := bstep (se 3 (by rfl) ⟨382694, by rfl⟩ : syracuseStep 2041037 = 765389) B765389
theorem B2041091 : Blo 603293 2041091 := bstep (se 1 (by rfl) ⟨1530818, by rfl⟩ : syracuseStep 2041091 = 3061637) B3061637
theorem B861473 : Blo 603293 861473 := bstep (se 2 (by rfl) ⟨323052, by rfl⟩ : syracuseStep 861473 = 646105) B646105
theorem B1090865 : Blo 603293 1090865 := bstep (se 2 (by rfl) ⟨409074, by rfl⟩ : syracuseStep 1090865 = 818149) B818149
theorem B861553 : Blo 603293 861553 := bstep (se 2 (by rfl) ⟨323082, by rfl⟩ : syracuseStep 861553 = 646165) B646165
theorem B3057101 : Blo 603293 3057101 := bstep (se 3 (by rfl) ⟨573206, by rfl⟩ : syracuseStep 3057101 = 1146413) B1146413
theorem B2041361 : Blo 603293 2041361 := bstep (se 2 (by rfl) ⟨765510, by rfl⟩ : syracuseStep 2041361 = 1531021) B1531021
theorem B829235 : Blo 603293 829235 := bstep (se 1 (by rfl) ⟨621926, by rfl⟩ : syracuseStep 829235 = 1243853) B1243853
theorem B11610053 : Blo 603293 11610053 := bstep (se 4 (by rfl) ⟨1088442, by rfl⟩ : syracuseStep 11610053 = 2176885) B2176885
theorem B2304035 : Blo 603293 2304035 := bstep (se 1 (by rfl) ⟨1728026, by rfl⟩ : syracuseStep 2304035 = 3456053) B3456053
theorem B2041901 : Blo 603293 2041901 := bstep (se 3 (by rfl) ⟨382856, by rfl⟩ : syracuseStep 2041901 = 765713) B765713
theorem B763987 : Blo 603293 763987 := bstep (se 1 (by rfl) ⟨572990, by rfl⟩ : syracuseStep 763987 = 1145981) B1145981
theorem B2041955 : Blo 603293 2041955 := bstep (se 1 (by rfl) ⟨1531466, by rfl⟩ : syracuseStep 2041955 = 3062933) B3062933
theorem B862339 : Blo 603293 862339 := bstep (se 1 (by rfl) ⟨646754, by rfl⟩ : syracuseStep 862339 = 1293509) B1293509
theorem B764083 : Blo 603293 764083 := bstep (se 1 (by rfl) ⟨573062, by rfl⟩ : syracuseStep 764083 = 1146125) B1146125
theorem B1452305 : Blo 603293 1452305 := bstep (se 2 (by rfl) ⟨544614, by rfl⟩ : syracuseStep 1452305 = 1089229) B1089229
theorem B2042225 : Blo 603293 2042225 := bstep (se 2 (by rfl) ⟨765834, by rfl⟩ : syracuseStep 2042225 = 1531669) B1531669
theorem B1845773 : Blo 603293 1845773 := bstep (se 3 (by rfl) ⟨346082, by rfl⟩ : syracuseStep 1845773 = 692165) B692165
theorem B1092113 : Blo 603293 1092113 := bstep (se 2 (by rfl) ⟨409542, by rfl⟩ : syracuseStep 1092113 = 819085) B819085
theorem B862817 : Blo 603293 862817 := bstep (se 2 (by rfl) ⟨323556, by rfl⟩ : syracuseStep 862817 = 647113) B647113
theorem B1944209 : Blo 603293 1944209 := bstep (se 2 (by rfl) ⟨729078, by rfl⟩ : syracuseStep 1944209 = 1458157) B1458157
theorem B764579 : Blo 603293 764579 := bstep (se 1 (by rfl) ⟨573434, by rfl⟩ : syracuseStep 764579 = 1146869) B1146869
theorem B862931 : Blo 603293 862931 := bstep (se 1 (by rfl) ⟨647198, by rfl⟩ : syracuseStep 862931 = 1294397) B1294397
theorem B1288963 : Blo 603293 1288963 := bstep (se 1 (by rfl) ⟨966722, by rfl⟩ : syracuseStep 1288963 = 1933445) B1933445
theorem B17705749 : Blo 603293 17705749 := bstep (se 6 (by rfl) ⟨414978, by rfl⟩ : syracuseStep 17705749 = 829957) B829957
theorem B863011 : Blo 603293 863011 := bstep (se 1 (by rfl) ⟨647258, by rfl⟩ : syracuseStep 863011 = 1294517) B1294517
theorem B2042765 : Blo 603293 2042765 := bstep (se 3 (by rfl) ⟨383018, by rfl⟩ : syracuseStep 2042765 = 766037) B766037
theorem B2042819 : Blo 603293 2042819 := bstep (se 1 (by rfl) ⟨1532114, by rfl⟩ : syracuseStep 2042819 = 3064229) B3064229
theorem B2305037 : Blo 603293 2305037 := bstep (se 3 (by rfl) ⟨432194, by rfl⟩ : syracuseStep 2305037 = 864389) B864389
theorem B1289297 : Blo 603293 1289297 := bstep (se 2 (by rfl) ⟨483486, by rfl⟩ : syracuseStep 1289297 = 966973) B966973
theorem B1944749 : Blo 603293 1944749 := bstep (se 3 (by rfl) ⟨364640, by rfl⟩ : syracuseStep 1944749 = 729281) B729281
theorem B2043089 : Blo 603293 2043089 := bstep (se 2 (by rfl) ⟨766158, by rfl⟩ : syracuseStep 2043089 = 1532317) B1532317
theorem B863569 : Blo 603293 863569 := bstep (se 2 (by rfl) ⟨323838, by rfl⟩ : syracuseStep 863569 = 647677) B647677
theorem B765283 : Blo 603293 765283 := bstep (se 1 (by rfl) ⟨573962, by rfl⟩ : syracuseStep 765283 = 1147925) B1147925
theorem B765379 : Blo 603293 765379 := bstep (se 1 (by rfl) ⟨574034, by rfl⟩ : syracuseStep 765379 = 1148069) B1148069
theorem B2174435 : Blo 603293 2174435 := bstep (se 1 (by rfl) ⟨1630826, by rfl⟩ : syracuseStep 2174435 = 3261653) B3261653
theorem B3878371 : Blo 603293 3878371 := bstep (se 1 (by rfl) ⟨2908778, by rfl⟩ : syracuseStep 3878371 = 5817557) B5817557
theorem B2043629 : Blo 603293 2043629 := bstep (se 3 (by rfl) ⟨383180, by rfl⟩ : syracuseStep 2043629 = 766361) B766361
theorem B2043683 : Blo 603293 2043683 := bstep (se 1 (by rfl) ⟨1532762, by rfl⟩ : syracuseStep 2043683 = 3065525) B3065525
theorem B1224515 : Blo 603293 1224515 := bstep (se 1 (by rfl) ⟨918386, by rfl⟩ : syracuseStep 1224515 = 1836773) B1836773
theorem B765875 : Blo 603293 765875 := bstep (se 1 (by rfl) ⟨574406, by rfl⟩ : syracuseStep 765875 = 1148813) B1148813
theorem B6074309 : Blo 603293 6074309 := bstep (se 4 (by rfl) ⟨569466, by rfl⟩ : syracuseStep 6074309 = 1138933) B1138933
theorem B864275 : Blo 603293 864275 := bstep (se 1 (by rfl) ⟨648206, by rfl⟩ : syracuseStep 864275 = 1296413) B1296413
theorem B2043953 : Blo 603293 2043953 := bstep (se 2 (by rfl) ⟨766482, by rfl⟩ : syracuseStep 2043953 = 1532965) B1532965
theorem B1290467 : Blo 603293 1290467 := bstep (se 1 (by rfl) ⟨967850, by rfl⟩ : syracuseStep 1290467 = 1935701) B1935701
theorem B3060017 : Blo 603293 3060017 := bstep (se 2 (by rfl) ⟨1147506, by rfl⟩ : syracuseStep 3060017 = 2295013) B2295013
theorem B3879373 : Blo 603293 3879373 := bstep (se 3 (by rfl) ⟨727382, by rfl⟩ : syracuseStep 3879373 = 1454765) B1454765
theorem B2175473 : Blo 603293 2175473 := bstep (se 2 (by rfl) ⟨815802, by rfl⟩ : syracuseStep 2175473 = 1631605) B1631605
theorem B2044493 : Blo 603293 2044493 := bstep (se 3 (by rfl) ⟨383342, by rfl⟩ : syracuseStep 2044493 = 766685) B766685
theorem B2175587 : Blo 603293 2175587 := bstep (se 1 (by rfl) ⟨1631690, by rfl⟩ : syracuseStep 2175587 = 3263381) B3263381
theorem B766579 : Blo 603293 766579 := bstep (se 1 (by rfl) ⟨574934, by rfl⟩ : syracuseStep 766579 = 1149869) B1149869
theorem B2044547 : Blo 603293 2044547 := bstep (se 1 (by rfl) ⟨1533410, by rfl⟩ : syracuseStep 2044547 = 3066821) B3066821
theorem B3453637 : Blo 603293 3453637 := bstep (se 4 (by rfl) ⟨323778, by rfl⟩ : syracuseStep 3453637 = 647557) B647557
theorem B766675 : Blo 603293 766675 := bstep (se 1 (by rfl) ⟨575006, by rfl⟩ : syracuseStep 766675 = 1150013) B1150013
theorem B1454851 : Blo 603293 1454851 := bstep (se 1 (by rfl) ⟨1091138, by rfl⟩ : syracuseStep 1454851 = 2182277) B2182277
theorem B2044817 : Blo 603293 2044817 := bstep (se 2 (by rfl) ⟨766806, by rfl⟩ : syracuseStep 2044817 = 1533613) B1533613
theorem B603299 : Blo 603293 603299 := bstep (se 1 (by rfl) ⟨452474, by rfl⟩ : syracuseStep 603299 = 904949) B904949
theorem B603315 : Blo 603293 603315 := bstep (se 1 (by rfl) ⟨452486, by rfl⟩ : syracuseStep 603315 = 904973) B904973
theorem B603331 : Blo 603293 603331 := bstep (se 1 (by rfl) ⟨452498, by rfl⟩ : syracuseStep 603331 = 904997) B904997
theorem B767171 : Blo 603293 767171 := bstep (se 1 (by rfl) ⟨575378, by rfl⟩ : syracuseStep 767171 = 1150757) B1150757
theorem B603347 : Blo 603293 603347 := bstep (se 1 (by rfl) ⟨452510, by rfl⟩ : syracuseStep 603347 = 905021) B905021
theorem B603363 : Blo 603293 603363 := bstep (se 1 (by rfl) ⟨452522, by rfl⟩ : syracuseStep 603363 = 905045) B905045
theorem B603379 : Blo 603293 603379 := bstep (se 1 (by rfl) ⟨452534, by rfl⟩ : syracuseStep 603379 = 905069) B905069
theorem B603395 : Blo 603293 603395 := bstep (se 1 (by rfl) ⟨452546, by rfl⟩ : syracuseStep 603395 = 905093) B905093
theorem B603411 : Blo 603293 603411 := bstep (se 1 (by rfl) ⟨452558, by rfl⟩ : syracuseStep 603411 = 905117) B905117
theorem B603427 : Blo 603293 603427 := bstep (se 1 (by rfl) ⟨452570, by rfl⟩ : syracuseStep 603427 = 905141) B905141
theorem B603443 : Blo 603293 603443 := bstep (se 1 (by rfl) ⟨452582, by rfl⟩ : syracuseStep 603443 = 905165) B905165
theorem B603459 : Blo 603293 603459 := bstep (se 1 (by rfl) ⟨452594, by rfl⟩ : syracuseStep 603459 = 905189) B905189
theorem B603475 : Blo 603293 603475 := bstep (se 1 (by rfl) ⟨452606, by rfl⟩ : syracuseStep 603475 = 905213) B905213
theorem B603491 : Blo 603293 603491 := bstep (se 1 (by rfl) ⟨452618, by rfl⟩ : syracuseStep 603491 = 905237) B905237
theorem B603507 : Blo 603293 603507 := bstep (se 1 (by rfl) ⟨452630, by rfl⟩ : syracuseStep 603507 = 905261) B905261
theorem B603523 : Blo 603293 603523 := bstep (se 1 (by rfl) ⟨452642, by rfl⟩ : syracuseStep 603523 = 905285) B905285
theorem B603539 : Blo 603293 603539 := bstep (se 1 (by rfl) ⟨452654, by rfl⟩ : syracuseStep 603539 = 905309) B905309
theorem B603555 : Blo 603293 603555 := bstep (se 1 (by rfl) ⟨452666, by rfl⟩ : syracuseStep 603555 = 905333) B905333
theorem B2045357 : Blo 603293 2045357 := bstep (se 3 (by rfl) ⟨383504, by rfl⟩ : syracuseStep 2045357 = 767009) B767009
theorem B1226161 : Blo 603293 1226161 := bstep (se 2 (by rfl) ⟨459810, by rfl⟩ : syracuseStep 1226161 = 919621) B919621
theorem B603571 : Blo 603293 603571 := bstep (se 1 (by rfl) ⟨452678, by rfl⟩ : syracuseStep 603571 = 905357) B905357
theorem B603587 : Blo 603293 603587 := bstep (se 1 (by rfl) ⟨452690, by rfl⟩ : syracuseStep 603587 = 905381) B905381
theorem B603603 : Blo 603293 603603 := bstep (se 1 (by rfl) ⟨452702, by rfl⟩ : syracuseStep 603603 = 905405) B905405
theorem B603619 : Blo 603293 603619 := bstep (se 1 (by rfl) ⟨452714, by rfl⟩ : syracuseStep 603619 = 905429) B905429
theorem B2045411 : Blo 603293 2045411 := bstep (se 1 (by rfl) ⟨1534058, by rfl⟩ : syracuseStep 2045411 = 3068117) B3068117
theorem B603635 : Blo 603293 603635 := bstep (se 1 (by rfl) ⟨452726, by rfl⟩ : syracuseStep 603635 = 905453) B905453
theorem B603651 : Blo 603293 603651 := bstep (se 1 (by rfl) ⟨452738, by rfl⟩ : syracuseStep 603651 = 905477) B905477
theorem B603667 : Blo 603293 603667 := bstep (se 1 (by rfl) ⟨452750, by rfl⟩ : syracuseStep 603667 = 905501) B905501
theorem B603683 : Blo 603293 603683 := bstep (se 1 (by rfl) ⟨452762, by rfl⟩ : syracuseStep 603683 = 905525) B905525
theorem B603699 : Blo 603293 603699 := bstep (se 1 (by rfl) ⟨452774, by rfl⟩ : syracuseStep 603699 = 905549) B905549
theorem B603715 : Blo 603293 603715 := bstep (se 1 (by rfl) ⟨452786, by rfl⟩ : syracuseStep 603715 = 905573) B905573
theorem B603731 : Blo 603293 603731 := bstep (se 1 (by rfl) ⟨452798, by rfl⟩ : syracuseStep 603731 = 905597) B905597
theorem B603747 : Blo 603293 603747 := bstep (se 1 (by rfl) ⟨452810, by rfl⟩ : syracuseStep 603747 = 905621) B905621
theorem B603763 : Blo 603293 603763 := bstep (se 1 (by rfl) ⟨452822, by rfl⟩ : syracuseStep 603763 = 905645) B905645
theorem B603779 : Blo 603293 603779 := bstep (se 1 (by rfl) ⟨452834, by rfl⟩ : syracuseStep 603779 = 905669) B905669
theorem B603795 : Blo 603293 603795 := bstep (se 1 (by rfl) ⟨452846, by rfl⟩ : syracuseStep 603795 = 905693) B905693
theorem B603811 : Blo 603293 603811 := bstep (se 1 (by rfl) ⟨452858, by rfl⟩ : syracuseStep 603811 = 905717) B905717
theorem B603827 : Blo 603293 603827 := bstep (se 1 (by rfl) ⟨452870, by rfl⟩ : syracuseStep 603827 = 905741) B905741
theorem B603843 : Blo 603293 603843 := bstep (se 1 (by rfl) ⟨452882, by rfl⟩ : syracuseStep 603843 = 905765) B905765
theorem B603859 : Blo 603293 603859 := bstep (se 1 (by rfl) ⟨452894, by rfl⟩ : syracuseStep 603859 = 905789) B905789
theorem B603875 : Blo 603293 603875 := bstep (se 1 (by rfl) ⟨452906, by rfl⟩ : syracuseStep 603875 = 905813) B905813
theorem B3061475 : Blo 603293 3061475 := bstep (se 1 (by rfl) ⟨2296106, by rfl⟩ : syracuseStep 3061475 = 4592213) B4592213
theorem B2045681 : Blo 603293 2045681 := bstep (se 2 (by rfl) ⟨767130, by rfl⟩ : syracuseStep 2045681 = 1534261) B1534261
theorem B603891 : Blo 603293 603891 := bstep (se 1 (by rfl) ⟨452918, by rfl⟩ : syracuseStep 603891 = 905837) B905837
theorem B603907 : Blo 603293 603907 := bstep (se 1 (by rfl) ⟨452930, by rfl⟩ : syracuseStep 603907 = 905861) B905861
theorem B1455889 : Blo 603293 1455889 := bstep (se 2 (by rfl) ⟨545958, by rfl⟩ : syracuseStep 1455889 = 1091917) B1091917
theorem B603923 : Blo 603293 603923 := bstep (se 1 (by rfl) ⟨452942, by rfl⟩ : syracuseStep 603923 = 905885) B905885
theorem B603939 : Blo 603293 603939 := bstep (se 1 (by rfl) ⟨452954, by rfl⟩ : syracuseStep 603939 = 905909) B905909
theorem B603955 : Blo 603293 603955 := bstep (se 1 (by rfl) ⟨452966, by rfl⟩ : syracuseStep 603955 = 905933) B905933
theorem B603971 : Blo 603293 603971 := bstep (se 1 (by rfl) ⟨452978, by rfl⟩ : syracuseStep 603971 = 905957) B905957
theorem B1357649 : Blo 603293 1357649 := bstep (se 2 (by rfl) ⟨509118, by rfl⟩ : syracuseStep 1357649 = 1018237) B1018237
theorem B603987 : Blo 603293 603987 := bstep (se 1 (by rfl) ⟨452990, by rfl⟩ : syracuseStep 603987 = 905981) B905981
theorem B1357667 : Blo 603293 1357667 := bstep (se 1 (by rfl) ⟨1018250, by rfl⟩ : syracuseStep 1357667 = 2036501) B2036501
theorem B604003 : Blo 603293 604003 := bstep (se 1 (by rfl) ⟨453002, by rfl⟩ : syracuseStep 604003 = 906005) B906005
theorem B604019 : Blo 603293 604019 := bstep (se 1 (by rfl) ⟨453014, by rfl⟩ : syracuseStep 604019 = 906029) B906029
theorem B604035 : Blo 603293 604035 := bstep (se 1 (by rfl) ⟨453026, by rfl⟩ : syracuseStep 604035 = 906053) B906053
theorem B767875 : Blo 603293 767875 := bstep (se 1 (by rfl) ⟨575906, by rfl⟩ : syracuseStep 767875 = 1151813) B1151813
theorem B604051 : Blo 603293 604051 := bstep (se 1 (by rfl) ⟨453038, by rfl⟩ : syracuseStep 604051 = 906077) B906077
theorem B604067 : Blo 603293 604067 := bstep (se 1 (by rfl) ⟨453050, by rfl⟩ : syracuseStep 604067 = 906101) B906101
theorem B604083 : Blo 603293 604083 := bstep (se 1 (by rfl) ⟨453062, by rfl⟩ : syracuseStep 604083 = 906125) B906125
theorem B604099 : Blo 603293 604099 := bstep (se 1 (by rfl) ⟨453074, by rfl⟩ : syracuseStep 604099 = 906149) B906149
theorem B604115 : Blo 603293 604115 := bstep (se 1 (by rfl) ⟨453086, by rfl⟩ : syracuseStep 604115 = 906173) B906173
theorem B1718243 : Blo 603293 1718243 := bstep (se 1 (by rfl) ⟨1288682, by rfl⟩ : syracuseStep 1718243 = 2577365) B2577365
theorem B604131 : Blo 603293 604131 := bstep (se 1 (by rfl) ⟨453098, by rfl⟩ : syracuseStep 604131 = 906197) B906197
theorem B767971 : Blo 603293 767971 := bstep (se 1 (by rfl) ⟨575978, by rfl⟩ : syracuseStep 767971 = 1151957) B1151957
theorem B604147 : Blo 603293 604147 := bstep (se 1 (by rfl) ⟨453110, by rfl⟩ : syracuseStep 604147 = 906221) B906221
theorem B604163 : Blo 603293 604163 := bstep (se 1 (by rfl) ⟨453122, by rfl⟩ : syracuseStep 604163 = 906245) B906245
theorem B604179 : Blo 603293 604179 := bstep (se 1 (by rfl) ⟨453134, by rfl⟩ : syracuseStep 604179 = 906269) B906269
theorem B604195 : Blo 603293 604195 := bstep (se 1 (by rfl) ⟨453146, by rfl⟩ : syracuseStep 604195 = 906293) B906293
theorem B604211 : Blo 603293 604211 := bstep (se 1 (by rfl) ⟨453158, by rfl⟩ : syracuseStep 604211 = 906317) B906317
theorem B14956597 : Blo 603293 14956597 := bstep (se 5 (by rfl) ⟨701090, by rfl⟩ : syracuseStep 14956597 = 1402181) B1402181
theorem B604227 : Blo 603293 604227 := bstep (se 1 (by rfl) ⟨453170, by rfl⟩ : syracuseStep 604227 = 906341) B906341
theorem B1226819 : Blo 603293 1226819 := bstep (se 1 (by rfl) ⟨920114, by rfl⟩ : syracuseStep 1226819 = 1840229) B1840229
theorem B604243 : Blo 603293 604243 := bstep (se 1 (by rfl) ⟨453182, by rfl⟩ : syracuseStep 604243 = 906365) B906365
theorem B604259 : Blo 603293 604259 := bstep (se 1 (by rfl) ⟨453194, by rfl⟩ : syracuseStep 604259 = 906389) B906389
theorem B1357937 : Blo 603293 1357937 := bstep (se 2 (by rfl) ⟨509226, by rfl⟩ : syracuseStep 1357937 = 1018453) B1018453
theorem B604275 : Blo 603293 604275 := bstep (se 1 (by rfl) ⟨453206, by rfl⟩ : syracuseStep 604275 = 906413) B906413
theorem B1357955 : Blo 603293 1357955 := bstep (se 1 (by rfl) ⟨1018466, by rfl⟩ : syracuseStep 1357955 = 2036933) B2036933
theorem B604291 : Blo 603293 604291 := bstep (se 1 (by rfl) ⟨453218, by rfl⟩ : syracuseStep 604291 = 906437) B906437
theorem B604307 : Blo 603293 604307 := bstep (se 1 (by rfl) ⟨453230, by rfl⟩ : syracuseStep 604307 = 906461) B906461
theorem B1718435 : Blo 603293 1718435 := bstep (se 1 (by rfl) ⟨1288826, by rfl⟩ : syracuseStep 1718435 = 2577653) B2577653
theorem B604323 : Blo 603293 604323 := bstep (se 1 (by rfl) ⟨453242, by rfl⟩ : syracuseStep 604323 = 906485) B906485
theorem B604339 : Blo 603293 604339 := bstep (se 1 (by rfl) ⟨453254, by rfl⟩ : syracuseStep 604339 = 906509) B906509
theorem B604355 : Blo 603293 604355 := bstep (se 1 (by rfl) ⟨453266, by rfl⟩ : syracuseStep 604355 = 906533) B906533
theorem B1292483 : Blo 603293 1292483 := bstep (se 1 (by rfl) ⟨969362, by rfl⟩ : syracuseStep 1292483 = 1938725) B1938725
theorem B604371 : Blo 603293 604371 := bstep (se 1 (by rfl) ⟨453278, by rfl⟩ : syracuseStep 604371 = 906557) B906557
theorem B604387 : Blo 603293 604387 := bstep (se 1 (by rfl) ⟨453290, by rfl⟩ : syracuseStep 604387 = 906581) B906581
theorem B604403 : Blo 603293 604403 := bstep (se 1 (by rfl) ⟨453302, by rfl⟩ : syracuseStep 604403 = 906605) B906605
theorem B604419 : Blo 603293 604419 := bstep (se 1 (by rfl) ⟨453314, by rfl⟩ : syracuseStep 604419 = 906629) B906629
theorem B2046221 : Blo 603293 2046221 := bstep (se 3 (by rfl) ⟨383666, by rfl⟩ : syracuseStep 2046221 = 767333) B767333
theorem B604435 : Blo 603293 604435 := bstep (se 1 (by rfl) ⟨453326, by rfl⟩ : syracuseStep 604435 = 906653) B906653
theorem B604451 : Blo 603293 604451 := bstep (se 1 (by rfl) ⟨453338, by rfl⟩ : syracuseStep 604451 = 906677) B906677
theorem B604467 : Blo 603293 604467 := bstep (se 1 (by rfl) ⟨453350, by rfl⟩ : syracuseStep 604467 = 906701) B906701
theorem B604483 : Blo 603293 604483 := bstep (se 1 (by rfl) ⟨453362, by rfl⟩ : syracuseStep 604483 = 906725) B906725
theorem B2046275 : Blo 603293 2046275 := bstep (se 1 (by rfl) ⟨1534706, by rfl⟩ : syracuseStep 2046275 = 3069413) B3069413
theorem B604499 : Blo 603293 604499 := bstep (se 1 (by rfl) ⟨453374, by rfl⟩ : syracuseStep 604499 = 906749) B906749
theorem B604515 : Blo 603293 604515 := bstep (se 1 (by rfl) ⟨453386, by rfl⟩ : syracuseStep 604515 = 906773) B906773
theorem B604531 : Blo 603293 604531 := bstep (se 1 (by rfl) ⟨453398, by rfl⟩ : syracuseStep 604531 = 906797) B906797
theorem B604547 : Blo 603293 604547 := bstep (se 1 (by rfl) ⟨453410, by rfl⟩ : syracuseStep 604547 = 906821) B906821
theorem B1358225 : Blo 603293 1358225 := bstep (se 2 (by rfl) ⟨509334, by rfl⟩ : syracuseStep 1358225 = 1018669) B1018669
theorem B604563 : Blo 603293 604563 := bstep (se 1 (by rfl) ⟨453422, by rfl⟩ : syracuseStep 604563 = 906845) B906845
theorem B1358243 : Blo 603293 1358243 := bstep (se 1 (by rfl) ⟨1018682, by rfl⟩ : syracuseStep 1358243 = 2037365) B2037365
theorem B604579 : Blo 603293 604579 := bstep (se 1 (by rfl) ⟨453434, by rfl⟩ : syracuseStep 604579 = 906869) B906869
theorem B604595 : Blo 603293 604595 := bstep (se 1 (by rfl) ⟨453446, by rfl⟩ : syracuseStep 604595 = 906893) B906893
theorem B604611 : Blo 603293 604611 := bstep (se 1 (by rfl) ⟨453458, by rfl⟩ : syracuseStep 604611 = 906917) B906917
theorem B604627 : Blo 603293 604627 := bstep (se 1 (by rfl) ⟨453470, by rfl⟩ : syracuseStep 604627 = 906941) B906941
theorem B768467 : Blo 603293 768467 := bstep (se 1 (by rfl) ⟨576350, by rfl⟩ : syracuseStep 768467 = 1152701) B1152701
theorem B604643 : Blo 603293 604643 := bstep (se 1 (by rfl) ⟨453482, by rfl⟩ : syracuseStep 604643 = 906965) B906965
theorem B604659 : Blo 603293 604659 := bstep (se 1 (by rfl) ⟨453494, by rfl⟩ : syracuseStep 604659 = 906989) B906989
theorem B604675 : Blo 603293 604675 := bstep (se 1 (by rfl) ⟨453506, by rfl⟩ : syracuseStep 604675 = 907013) B907013
theorem B2177549 : Blo 603293 2177549 := bstep (se 3 (by rfl) ⟨408290, by rfl⟩ : syracuseStep 2177549 = 816581) B816581
theorem B3062285 : Blo 603293 3062285 := bstep (se 3 (by rfl) ⟨574178, by rfl⟩ : syracuseStep 3062285 = 1148357) B1148357
theorem B604691 : Blo 603293 604691 := bstep (se 1 (by rfl) ⟨453518, by rfl⟩ : syracuseStep 604691 = 907037) B907037
theorem B604707 : Blo 603293 604707 := bstep (se 1 (by rfl) ⟨453530, by rfl⟩ : syracuseStep 604707 = 907061) B907061
theorem B604723 : Blo 603293 604723 := bstep (se 1 (by rfl) ⟨453542, by rfl⟩ : syracuseStep 604723 = 907085) B907085
theorem B604739 : Blo 603293 604739 := bstep (se 1 (by rfl) ⟨453554, by rfl⟩ : syracuseStep 604739 = 907109) B907109
theorem B2046545 : Blo 603293 2046545 := bstep (se 2 (by rfl) ⟨767454, by rfl⟩ : syracuseStep 2046545 = 1534909) B1534909
theorem B604755 : Blo 603293 604755 := bstep (se 1 (by rfl) ⟨453566, by rfl⟩ : syracuseStep 604755 = 907133) B907133
theorem B604771 : Blo 603293 604771 := bstep (se 1 (by rfl) ⟨453578, by rfl⟩ : syracuseStep 604771 = 907157) B907157
theorem B604787 : Blo 603293 604787 := bstep (se 1 (by rfl) ⟨453590, by rfl⟩ : syracuseStep 604787 = 907181) B907181
theorem B604803 : Blo 603293 604803 := bstep (se 1 (by rfl) ⟨453602, by rfl⟩ : syracuseStep 604803 = 907205) B907205
theorem B1227395 : Blo 603293 1227395 := bstep (se 1 (by rfl) ⟨920546, by rfl⟩ : syracuseStep 1227395 = 1841093) B1841093
theorem B3455621 : Blo 603293 3455621 := bstep (se 4 (by rfl) ⟨323964, by rfl⟩ : syracuseStep 3455621 = 647929) B647929
theorem B604819 : Blo 603293 604819 := bstep (se 1 (by rfl) ⟨453614, by rfl⟩ : syracuseStep 604819 = 907229) B907229
theorem B604835 : Blo 603293 604835 := bstep (se 1 (by rfl) ⟨453626, by rfl⟩ : syracuseStep 604835 = 907253) B907253
theorem B3685027 : Blo 603293 3685027 := bstep (se 1 (by rfl) ⟨2763770, by rfl⟩ : syracuseStep 3685027 = 5527541) B5527541
theorem B1358513 : Blo 603293 1358513 := bstep (se 2 (by rfl) ⟨509442, by rfl⟩ : syracuseStep 1358513 = 1018885) B1018885
theorem B604851 : Blo 603293 604851 := bstep (se 1 (by rfl) ⟨453638, by rfl⟩ : syracuseStep 604851 = 907277) B907277
theorem B1358531 : Blo 603293 1358531 := bstep (se 1 (by rfl) ⟨1018898, by rfl⟩ : syracuseStep 1358531 = 2037797) B2037797
theorem B604867 : Blo 603293 604867 := bstep (se 1 (by rfl) ⟨453650, by rfl⟩ : syracuseStep 604867 = 907301) B907301
theorem B604883 : Blo 603293 604883 := bstep (se 1 (by rfl) ⟨453662, by rfl⟩ : syracuseStep 604883 = 907325) B907325
theorem B604899 : Blo 603293 604899 := bstep (se 1 (by rfl) ⟨453674, by rfl⟩ : syracuseStep 604899 = 907349) B907349
theorem B604915 : Blo 603293 604915 := bstep (se 1 (by rfl) ⟨453686, by rfl⟩ : syracuseStep 604915 = 907373) B907373
theorem B604931 : Blo 603293 604931 := bstep (se 1 (by rfl) ⟨453698, by rfl⟩ : syracuseStep 604931 = 907397) B907397
theorem B604947 : Blo 603293 604947 := bstep (se 1 (by rfl) ⟨453710, by rfl⟩ : syracuseStep 604947 = 907421) B907421
theorem B604963 : Blo 603293 604963 := bstep (se 1 (by rfl) ⟨453722, by rfl⟩ : syracuseStep 604963 = 907445) B907445
theorem B604979 : Blo 603293 604979 := bstep (se 1 (by rfl) ⟨453734, by rfl⟩ : syracuseStep 604979 = 907469) B907469
theorem B604995 : Blo 603293 604995 := bstep (se 1 (by rfl) ⟨453746, by rfl⟩ : syracuseStep 604995 = 907493) B907493
theorem B605011 : Blo 603293 605011 := bstep (se 1 (by rfl) ⟨453758, by rfl⟩ : syracuseStep 605011 = 907517) B907517
theorem B605027 : Blo 603293 605027 := bstep (se 1 (by rfl) ⟨453770, by rfl⟩ : syracuseStep 605027 = 907541) B907541
theorem B605043 : Blo 603293 605043 := bstep (se 1 (by rfl) ⟨453782, by rfl⟩ : syracuseStep 605043 = 907565) B907565
theorem B605059 : Blo 603293 605059 := bstep (se 1 (by rfl) ⟨453794, by rfl⟩ : syracuseStep 605059 = 907589) B907589
theorem B605075 : Blo 603293 605075 := bstep (se 1 (by rfl) ⟨453806, by rfl⟩ : syracuseStep 605075 = 907613) B907613
theorem B605091 : Blo 603293 605091 := bstep (se 1 (by rfl) ⟨453818, by rfl⟩ : syracuseStep 605091 = 907637) B907637
theorem B605107 : Blo 603293 605107 := bstep (se 1 (by rfl) ⟨453830, by rfl⟩ : syracuseStep 605107 = 907661) B907661
theorem B7650229 : Blo 603293 7650229 := bstep (se 5 (by rfl) ⟨358604, by rfl⟩ : syracuseStep 7650229 = 717209) B717209
theorem B605123 : Blo 603293 605123 := bstep (se 1 (by rfl) ⟨453842, by rfl⟩ : syracuseStep 605123 = 907685) B907685
theorem B1719245 : Blo 603293 1719245 := bstep (se 3 (by rfl) ⟨322358, by rfl⟩ : syracuseStep 1719245 = 644717) B644717
theorem B1358801 : Blo 603293 1358801 := bstep (se 2 (by rfl) ⟨509550, by rfl⟩ : syracuseStep 1358801 = 1019101) B1019101
theorem B605139 : Blo 603293 605139 := bstep (se 1 (by rfl) ⟨453854, by rfl⟩ : syracuseStep 605139 = 907709) B907709
theorem B1358819 : Blo 603293 1358819 := bstep (se 1 (by rfl) ⟨1019114, by rfl⟩ : syracuseStep 1358819 = 2038229) B2038229
theorem B605155 : Blo 603293 605155 := bstep (se 1 (by rfl) ⟨453866, by rfl⟩ : syracuseStep 605155 = 907733) B907733
theorem B605171 : Blo 603293 605171 := bstep (se 1 (by rfl) ⟨453878, by rfl⟩ : syracuseStep 605171 = 907757) B907757
theorem B736259 : Blo 603293 736259 := bstep (se 1 (by rfl) ⟨552194, by rfl⟩ : syracuseStep 736259 = 1104389) B1104389
theorem B605187 : Blo 603293 605187 := bstep (se 1 (by rfl) ⟨453890, by rfl⟩ : syracuseStep 605187 = 907781) B907781
theorem B605203 : Blo 603293 605203 := bstep (se 1 (by rfl) ⟨453902, by rfl⟩ : syracuseStep 605203 = 907805) B907805
theorem B605219 : Blo 603293 605219 := bstep (se 1 (by rfl) ⟨453914, by rfl⟩ : syracuseStep 605219 = 907829) B907829
theorem B605235 : Blo 603293 605235 := bstep (se 1 (by rfl) ⟨453926, by rfl⟩ : syracuseStep 605235 = 907853) B907853
theorem B605251 : Blo 603293 605251 := bstep (se 1 (by rfl) ⟨453938, by rfl⟩ : syracuseStep 605251 = 907877) B907877
theorem B605267 : Blo 603293 605267 := bstep (se 1 (by rfl) ⟨453950, by rfl⟩ : syracuseStep 605267 = 907901) B907901
theorem B605283 : Blo 603293 605283 := bstep (se 1 (by rfl) ⟨453962, by rfl⟩ : syracuseStep 605283 = 907925) B907925
theorem B932963 : Blo 603293 932963 := bstep (se 1 (by rfl) ⟨699722, by rfl⟩ : syracuseStep 932963 = 1399445) B1399445
theorem B2047085 : Blo 603293 2047085 := bstep (se 3 (by rfl) ⟨383828, by rfl⟩ : syracuseStep 2047085 = 767657) B767657
theorem B605299 : Blo 603293 605299 := bstep (se 1 (by rfl) ⟨453974, by rfl⟩ : syracuseStep 605299 = 907949) B907949
theorem B1719427 : Blo 603293 1719427 := bstep (se 1 (by rfl) ⟨1289570, by rfl⟩ : syracuseStep 1719427 = 2579141) B2579141
theorem B605315 : Blo 603293 605315 := bstep (se 1 (by rfl) ⟨453986, by rfl⟩ : syracuseStep 605315 = 907973) B907973
theorem B605331 : Blo 603293 605331 := bstep (se 1 (by rfl) ⟨453998, by rfl⟩ : syracuseStep 605331 = 907997) B907997
theorem B605347 : Blo 603293 605347 := bstep (se 1 (by rfl) ⟨454010, by rfl⟩ : syracuseStep 605347 = 908021) B908021
theorem B2047139 : Blo 603293 2047139 := bstep (se 1 (by rfl) ⟨1535354, by rfl⟩ : syracuseStep 2047139 = 3070709) B3070709
theorem B605363 : Blo 603293 605363 := bstep (se 1 (by rfl) ⟨454022, by rfl⟩ : syracuseStep 605363 = 908045) B908045
theorem B605379 : Blo 603293 605379 := bstep (se 1 (by rfl) ⟨454034, by rfl⟩ : syracuseStep 605379 = 908069) B908069
theorem B605395 : Blo 603293 605395 := bstep (se 1 (by rfl) ⟨454046, by rfl⟩ : syracuseStep 605395 = 908093) B908093
theorem B605411 : Blo 603293 605411 := bstep (se 1 (by rfl) ⟨454058, by rfl⟩ : syracuseStep 605411 = 908117) B908117
theorem B1359089 : Blo 603293 1359089 := bstep (se 2 (by rfl) ⟨509658, by rfl⟩ : syracuseStep 1359089 = 1019317) B1019317
theorem B6208753 : Blo 603293 6208753 := bstep (se 2 (by rfl) ⟨2328282, by rfl⟩ : syracuseStep 6208753 = 4656565) B4656565
theorem B605427 : Blo 603293 605427 := bstep (se 1 (by rfl) ⟨454070, by rfl⟩ : syracuseStep 605427 = 908141) B908141
theorem B1359107 : Blo 603293 1359107 := bstep (se 1 (by rfl) ⟨1019330, by rfl⟩ : syracuseStep 1359107 = 2038661) B2038661
theorem B605443 : Blo 603293 605443 := bstep (se 1 (by rfl) ⟨454082, by rfl⟩ : syracuseStep 605443 = 908165) B908165
theorem B605459 : Blo 603293 605459 := bstep (se 1 (by rfl) ⟨454094, by rfl⟩ : syracuseStep 605459 = 908189) B908189
theorem B605475 : Blo 603293 605475 := bstep (se 1 (by rfl) ⟨454106, by rfl⟩ : syracuseStep 605475 = 908213) B908213
theorem B605491 : Blo 603293 605491 := bstep (se 1 (by rfl) ⟨454118, by rfl⟩ : syracuseStep 605491 = 908237) B908237
theorem B605507 : Blo 603293 605507 := bstep (se 1 (by rfl) ⟨454130, by rfl⟩ : syracuseStep 605507 = 908261) B908261
theorem B605523 : Blo 603293 605523 := bstep (se 1 (by rfl) ⟨454142, by rfl⟩ : syracuseStep 605523 = 908285) B908285
theorem B605539 : Blo 603293 605539 := bstep (se 1 (by rfl) ⟨454154, by rfl⟩ : syracuseStep 605539 = 908309) B908309
theorem B605555 : Blo 603293 605555 := bstep (se 1 (by rfl) ⟨454166, by rfl⟩ : syracuseStep 605555 = 908333) B908333
theorem B605571 : Blo 603293 605571 := bstep (se 1 (by rfl) ⟨454178, by rfl⟩ : syracuseStep 605571 = 908357) B908357
theorem B605587 : Blo 603293 605587 := bstep (se 1 (by rfl) ⟨454190, by rfl⟩ : syracuseStep 605587 = 908381) B908381
theorem B605603 : Blo 603293 605603 := bstep (se 1 (by rfl) ⟨454202, by rfl⟩ : syracuseStep 605603 = 908405) B908405
theorem B2047409 : Blo 603293 2047409 := bstep (se 2 (by rfl) ⟨767778, by rfl⟩ : syracuseStep 2047409 = 1535557) B1535557
theorem B605619 : Blo 603293 605619 := bstep (se 1 (by rfl) ⟨454214, by rfl⟩ : syracuseStep 605619 = 908429) B908429
theorem B605635 : Blo 603293 605635 := bstep (se 1 (by rfl) ⟨454226, by rfl⟩ : syracuseStep 605635 = 908453) B908453
theorem B605651 : Blo 603293 605651 := bstep (se 1 (by rfl) ⟨454238, by rfl⟩ : syracuseStep 605651 = 908477) B908477
theorem B605667 : Blo 603293 605667 := bstep (se 1 (by rfl) ⟨454250, by rfl⟩ : syracuseStep 605667 = 908501) B908501
theorem B605683 : Blo 603293 605683 := bstep (se 1 (by rfl) ⟨454262, by rfl⟩ : syracuseStep 605683 = 908525) B908525
theorem B605699 : Blo 603293 605699 := bstep (se 1 (by rfl) ⟨454274, by rfl⟩ : syracuseStep 605699 = 908549) B908549
theorem B1359377 : Blo 603293 1359377 := bstep (se 2 (by rfl) ⟨509766, by rfl⟩ : syracuseStep 1359377 = 1019533) B1019533
theorem B605715 : Blo 603293 605715 := bstep (se 1 (by rfl) ⟨454286, by rfl⟩ : syracuseStep 605715 = 908573) B908573
theorem B1359395 : Blo 603293 1359395 := bstep (se 1 (by rfl) ⟨1019546, by rfl⟩ : syracuseStep 1359395 = 2039093) B2039093
theorem B605731 : Blo 603293 605731 := bstep (se 1 (by rfl) ⟨454298, by rfl⟩ : syracuseStep 605731 = 908597) B908597
theorem B605747 : Blo 603293 605747 := bstep (se 1 (by rfl) ⟨454310, by rfl⟩ : syracuseStep 605747 = 908621) B908621
theorem B605763 : Blo 603293 605763 := bstep (se 1 (by rfl) ⟨454322, by rfl⟩ : syracuseStep 605763 = 908645) B908645
theorem B605779 : Blo 603293 605779 := bstep (se 1 (by rfl) ⟨454334, by rfl⟩ : syracuseStep 605779 = 908669) B908669
theorem B605795 : Blo 603293 605795 := bstep (se 1 (by rfl) ⟨454346, by rfl⟩ : syracuseStep 605795 = 908693) B908693
theorem B1719917 : Blo 603293 1719917 := bstep (se 3 (by rfl) ⟨322484, by rfl⟩ : syracuseStep 1719917 = 644969) B644969
theorem B605811 : Blo 603293 605811 := bstep (se 1 (by rfl) ⟨454358, by rfl⟩ : syracuseStep 605811 = 908717) B908717
theorem B605827 : Blo 603293 605827 := bstep (se 1 (by rfl) ⟨454370, by rfl⟩ : syracuseStep 605827 = 908741) B908741
theorem B605843 : Blo 603293 605843 := bstep (se 1 (by rfl) ⟨454382, by rfl⟩ : syracuseStep 605843 = 908765) B908765
theorem B605859 : Blo 603293 605859 := bstep (se 1 (by rfl) ⟨454394, by rfl⟩ : syracuseStep 605859 = 908789) B908789
theorem B1556131 : Blo 603293 1556131 := bstep (se 1 (by rfl) ⟨1167098, by rfl⟩ : syracuseStep 1556131 = 2334197) B2334197
theorem B3784369 : Blo 603293 3784369 := bstep (se 2 (by rfl) ⟨1419138, by rfl⟩ : syracuseStep 3784369 = 2838277) B2838277
theorem B605875 : Blo 603293 605875 := bstep (se 1 (by rfl) ⟨454406, by rfl⟩ : syracuseStep 605875 = 908813) B908813
theorem B605891 : Blo 603293 605891 := bstep (se 1 (by rfl) ⟨454418, by rfl⟩ : syracuseStep 605891 = 908837) B908837
theorem B1752781 : Blo 603293 1752781 := bstep (se 3 (by rfl) ⟨328646, by rfl⟩ : syracuseStep 1752781 = 657293) B657293
theorem B605907 : Blo 603293 605907 := bstep (se 1 (by rfl) ⟨454430, by rfl⟩ : syracuseStep 605907 = 908861) B908861
theorem B605923 : Blo 603293 605923 := bstep (se 1 (by rfl) ⟨454442, by rfl⟩ : syracuseStep 605923 = 908885) B908885
theorem B605939 : Blo 603293 605939 := bstep (se 1 (by rfl) ⟨454454, by rfl⟩ : syracuseStep 605939 = 908909) B908909
theorem B605955 : Blo 603293 605955 := bstep (se 1 (by rfl) ⟨454466, by rfl⟩ : syracuseStep 605955 = 908933) B908933
theorem B1031953 : Blo 603293 1031953 := bstep (se 2 (by rfl) ⟨386982, by rfl⟩ : syracuseStep 1031953 = 773965) B773965
theorem B605971 : Blo 603293 605971 := bstep (se 1 (by rfl) ⟨454478, by rfl⟩ : syracuseStep 605971 = 908957) B908957
theorem B605987 : Blo 603293 605987 := bstep (se 1 (by rfl) ⟨454490, by rfl⟩ : syracuseStep 605987 = 908981) B908981
theorem B1359665 : Blo 603293 1359665 := bstep (se 2 (by rfl) ⟨509874, by rfl⟩ : syracuseStep 1359665 = 1019749) B1019749
theorem B606003 : Blo 603293 606003 := bstep (se 1 (by rfl) ⟨454502, by rfl⟩ : syracuseStep 606003 = 909005) B909005
theorem B966467 : Blo 603293 966467 := bstep (se 1 (by rfl) ⟨724850, by rfl⟩ : syracuseStep 966467 = 1449701) B1449701
theorem B1359683 : Blo 603293 1359683 := bstep (se 1 (by rfl) ⟨1019762, by rfl⟩ : syracuseStep 1359683 = 2039525) B2039525
theorem B5160773 : Blo 603293 5160773 := bstep (se 4 (by rfl) ⟨483822, by rfl⟩ : syracuseStep 5160773 = 967645) B967645
theorem B606019 : Blo 603293 606019 := bstep (se 1 (by rfl) ⟨454514, by rfl⟩ : syracuseStep 606019 = 909029) B909029
theorem B606035 : Blo 603293 606035 := bstep (se 1 (by rfl) ⟨454526, by rfl⟩ : syracuseStep 606035 = 909053) B909053
theorem B606051 : Blo 603293 606051 := bstep (se 1 (by rfl) ⟨454538, by rfl⟩ : syracuseStep 606051 = 909077) B909077
theorem B606067 : Blo 603293 606067 := bstep (se 1 (by rfl) ⟨454550, by rfl⟩ : syracuseStep 606067 = 909101) B909101
theorem B606083 : Blo 603293 606083 := bstep (se 1 (by rfl) ⟨454562, by rfl⟩ : syracuseStep 606083 = 909125) B909125
theorem B606099 : Blo 603293 606099 := bstep (se 1 (by rfl) ⟨454574, by rfl⟩ : syracuseStep 606099 = 909149) B909149
theorem B606115 : Blo 603293 606115 := bstep (se 1 (by rfl) ⟨454586, by rfl⟩ : syracuseStep 606115 = 909173) B909173
theorem B606131 : Blo 603293 606131 := bstep (se 1 (by rfl) ⟨454598, by rfl⟩ : syracuseStep 606131 = 909197) B909197
theorem B966595 : Blo 603293 966595 := bstep (se 1 (by rfl) ⟨724946, by rfl⟩ : syracuseStep 966595 = 1449893) B1449893
theorem B606147 : Blo 603293 606147 := bstep (se 1 (by rfl) ⟨454610, by rfl⟩ : syracuseStep 606147 = 909221) B909221
theorem B2047949 : Blo 603293 2047949 := bstep (se 3 (by rfl) ⟨383990, by rfl⟩ : syracuseStep 2047949 = 767981) B767981
theorem B606163 : Blo 603293 606163 := bstep (se 1 (by rfl) ⟨454622, by rfl⟩ : syracuseStep 606163 = 909245) B909245
theorem B606179 : Blo 603293 606179 := bstep (se 1 (by rfl) ⟨454634, by rfl⟩ : syracuseStep 606179 = 909269) B909269
theorem B606195 : Blo 603293 606195 := bstep (se 1 (by rfl) ⟨454646, by rfl⟩ : syracuseStep 606195 = 909293) B909293
theorem B606211 : Blo 603293 606211 := bstep (se 1 (by rfl) ⟨454658, by rfl⟩ : syracuseStep 606211 = 909317) B909317
theorem B2048003 : Blo 603293 2048003 := bstep (se 1 (by rfl) ⟨1536002, by rfl⟩ : syracuseStep 2048003 = 3072005) B3072005
theorem B606227 : Blo 603293 606227 := bstep (se 1 (by rfl) ⟨454670, by rfl⟩ : syracuseStep 606227 = 909341) B909341
theorem B606243 : Blo 603293 606243 := bstep (se 1 (by rfl) ⟨454682, by rfl⟩ : syracuseStep 606243 = 909365) B909365
theorem B606259 : Blo 603293 606259 := bstep (se 1 (by rfl) ⟨454694, by rfl⟩ : syracuseStep 606259 = 909389) B909389
theorem B606275 : Blo 603293 606275 := bstep (se 1 (by rfl) ⟨454706, by rfl⟩ : syracuseStep 606275 = 909413) B909413
theorem B1359953 : Blo 603293 1359953 := bstep (se 2 (by rfl) ⟨509982, by rfl⟩ : syracuseStep 1359953 = 1019965) B1019965
theorem B606291 : Blo 603293 606291 := bstep (se 1 (by rfl) ⟨454718, by rfl⟩ : syracuseStep 606291 = 909437) B909437
theorem B1359971 : Blo 603293 1359971 := bstep (se 1 (by rfl) ⟨1019978, by rfl⟩ : syracuseStep 1359971 = 2039957) B2039957
theorem B606307 : Blo 603293 606307 := bstep (se 1 (by rfl) ⟨454730, by rfl⟩ : syracuseStep 606307 = 909461) B909461
theorem B606323 : Blo 603293 606323 := bstep (se 1 (by rfl) ⟨454742, by rfl⟩ : syracuseStep 606323 = 909485) B909485
theorem B606339 : Blo 603293 606339 := bstep (se 1 (by rfl) ⟨454754, by rfl⟩ : syracuseStep 606339 = 909509) B909509
theorem B606355 : Blo 603293 606355 := bstep (se 1 (by rfl) ⟨454766, by rfl⟩ : syracuseStep 606355 = 909533) B909533
theorem B1294499 : Blo 603293 1294499 := bstep (se 1 (by rfl) ⟨970874, by rfl⟩ : syracuseStep 1294499 = 1941749) B1941749
theorem B606371 : Blo 603293 606371 := bstep (se 1 (by rfl) ⟨454778, by rfl⟩ : syracuseStep 606371 = 909557) B909557
theorem B606387 : Blo 603293 606387 := bstep (se 1 (by rfl) ⟨454790, by rfl⟩ : syracuseStep 606387 = 909581) B909581
theorem B606403 : Blo 603293 606403 := bstep (se 1 (by rfl) ⟨454802, by rfl⟩ : syracuseStep 606403 = 909605) B909605
theorem B606419 : Blo 603293 606419 := bstep (se 1 (by rfl) ⟨454814, by rfl⟩ : syracuseStep 606419 = 909629) B909629
theorem B606435 : Blo 603293 606435 := bstep (se 1 (by rfl) ⟨454826, by rfl⟩ : syracuseStep 606435 = 909653) B909653
theorem B6209777 : Blo 603293 6209777 := bstep (se 2 (by rfl) ⟨2328666, by rfl⟩ : syracuseStep 6209777 = 4657333) B4657333
theorem B606451 : Blo 603293 606451 := bstep (se 1 (by rfl) ⟨454838, by rfl⟩ : syracuseStep 606451 = 909677) B909677
theorem B606467 : Blo 603293 606467 := bstep (se 1 (by rfl) ⟨454850, by rfl⟩ : syracuseStep 606467 = 909701) B909701
theorem B2048273 : Blo 603293 2048273 := bstep (se 2 (by rfl) ⟨768102, by rfl⟩ : syracuseStep 2048273 = 1536205) B1536205
theorem B606483 : Blo 603293 606483 := bstep (se 1 (by rfl) ⟨454862, by rfl⟩ : syracuseStep 606483 = 909725) B909725
theorem B606499 : Blo 603293 606499 := bstep (se 1 (by rfl) ⟨454874, by rfl⟩ : syracuseStep 606499 = 909749) B909749
theorem B606515 : Blo 603293 606515 := bstep (se 1 (by rfl) ⟨454886, by rfl⟩ : syracuseStep 606515 = 909773) B909773
theorem B966979 : Blo 603293 966979 := bstep (se 1 (by rfl) ⟨725234, by rfl⟩ : syracuseStep 966979 = 1450469) B1450469
theorem B606531 : Blo 603293 606531 := bstep (se 1 (by rfl) ⟨454898, by rfl⟩ : syracuseStep 606531 = 909797) B909797
theorem B606547 : Blo 603293 606547 := bstep (se 1 (by rfl) ⟨454910, by rfl⟩ : syracuseStep 606547 = 909821) B909821
theorem B606563 : Blo 603293 606563 := bstep (se 1 (by rfl) ⟨454922, by rfl⟩ : syracuseStep 606563 = 909845) B909845
theorem B1360241 : Blo 603293 1360241 := bstep (se 2 (by rfl) ⟨510090, by rfl⟩ : syracuseStep 1360241 = 1020181) B1020181
theorem B606579 : Blo 603293 606579 := bstep (se 1 (by rfl) ⟨454934, by rfl⟩ : syracuseStep 606579 = 909869) B909869
theorem B1360259 : Blo 603293 1360259 := bstep (se 1 (by rfl) ⟨1020194, by rfl⟩ : syracuseStep 1360259 = 2040389) B2040389
theorem B606595 : Blo 603293 606595 := bstep (se 1 (by rfl) ⟨454946, by rfl⟩ : syracuseStep 606595 = 909893) B909893
theorem B606611 : Blo 603293 606611 := bstep (se 1 (by rfl) ⟨454958, by rfl⟩ : syracuseStep 606611 = 909917) B909917
theorem B606627 : Blo 603293 606627 := bstep (se 1 (by rfl) ⟨454970, by rfl⟩ : syracuseStep 606627 = 909941) B909941
theorem B606643 : Blo 603293 606643 := bstep (se 1 (by rfl) ⟨454982, by rfl⟩ : syracuseStep 606643 = 909965) B909965
theorem B606659 : Blo 603293 606659 := bstep (se 1 (by rfl) ⟨454994, by rfl⟩ : syracuseStep 606659 = 909989) B909989
theorem B606675 : Blo 603293 606675 := bstep (se 1 (by rfl) ⟨455006, by rfl⟩ : syracuseStep 606675 = 910013) B910013
theorem B606691 : Blo 603293 606691 := bstep (se 1 (by rfl) ⟨455018, by rfl⟩ : syracuseStep 606691 = 910037) B910037
theorem B606707 : Blo 603293 606707 := bstep (se 1 (by rfl) ⟨455030, by rfl⟩ : syracuseStep 606707 = 910061) B910061
theorem B606723 : Blo 603293 606723 := bstep (se 1 (by rfl) ⟨455042, by rfl⟩ : syracuseStep 606723 = 910085) B910085
theorem B606739 : Blo 603293 606739 := bstep (se 1 (by rfl) ⟨455054, by rfl⟩ : syracuseStep 606739 = 910109) B910109
theorem B606755 : Blo 603293 606755 := bstep (se 1 (by rfl) ⟨455066, by rfl⟩ : syracuseStep 606755 = 910133) B910133
theorem B606771 : Blo 603293 606771 := bstep (se 1 (by rfl) ⟨455078, by rfl⟩ : syracuseStep 606771 = 910157) B910157
theorem B967235 : Blo 603293 967235 := bstep (se 1 (by rfl) ⟨725426, by rfl⟩ : syracuseStep 967235 = 1450853) B1450853
theorem B606787 : Blo 603293 606787 := bstep (se 1 (by rfl) ⟨455090, by rfl⟩ : syracuseStep 606787 = 910181) B910181
theorem B606803 : Blo 603293 606803 := bstep (se 1 (by rfl) ⟨455102, by rfl⟩ : syracuseStep 606803 = 910205) B910205
theorem B606819 : Blo 603293 606819 := bstep (se 1 (by rfl) ⟨455114, by rfl⟩ : syracuseStep 606819 = 910229) B910229
theorem B606835 : Blo 603293 606835 := bstep (se 1 (by rfl) ⟨455126, by rfl⟩ : syracuseStep 606835 = 910253) B910253
theorem B606851 : Blo 603293 606851 := bstep (se 1 (by rfl) ⟨455138, by rfl⟩ : syracuseStep 606851 = 910277) B910277
theorem B1360529 : Blo 603293 1360529 := bstep (se 2 (by rfl) ⟨510198, by rfl⟩ : syracuseStep 1360529 = 1020397) B1020397
theorem B606867 : Blo 603293 606867 := bstep (se 1 (by rfl) ⟨455150, by rfl⟩ : syracuseStep 606867 = 910301) B910301
theorem B1360547 : Blo 603293 1360547 := bstep (se 1 (by rfl) ⟨1020410, by rfl⟩ : syracuseStep 1360547 = 2040821) B2040821
theorem B606883 : Blo 603293 606883 := bstep (se 1 (by rfl) ⟨455162, by rfl⟩ : syracuseStep 606883 = 910325) B910325
theorem B606899 : Blo 603293 606899 := bstep (se 1 (by rfl) ⟨455174, by rfl⟩ : syracuseStep 606899 = 910349) B910349
theorem B606915 : Blo 603293 606915 := bstep (se 1 (by rfl) ⟨455186, by rfl⟩ : syracuseStep 606915 = 910373) B910373
theorem B606931 : Blo 603293 606931 := bstep (se 1 (by rfl) ⟨455198, by rfl⟩ : syracuseStep 606931 = 910397) B910397
theorem B606947 : Blo 603293 606947 := bstep (se 1 (by rfl) ⟨455210, by rfl⟩ : syracuseStep 606947 = 910421) B910421
theorem B606963 : Blo 603293 606963 := bstep (se 1 (by rfl) ⟨455222, by rfl⟩ : syracuseStep 606963 = 910445) B910445
theorem B606979 : Blo 603293 606979 := bstep (se 1 (by rfl) ⟨455234, by rfl⟩ : syracuseStep 606979 = 910469) B910469
theorem B1721101 : Blo 603293 1721101 := bstep (se 3 (by rfl) ⟨322706, by rfl⟩ : syracuseStep 1721101 = 645413) B645413
theorem B606995 : Blo 603293 606995 := bstep (se 1 (by rfl) ⟨455246, by rfl⟩ : syracuseStep 606995 = 910493) B910493
theorem B607011 : Blo 603293 607011 := bstep (se 1 (by rfl) ⟨455258, by rfl⟩ : syracuseStep 607011 = 910517) B910517
theorem B2048813 : Blo 603293 2048813 := bstep (se 3 (by rfl) ⟨384152, by rfl⟩ : syracuseStep 2048813 = 768305) B768305
theorem B607027 : Blo 603293 607027 := bstep (se 1 (by rfl) ⟨455270, by rfl⟩ : syracuseStep 607027 = 910541) B910541
theorem B607043 : Blo 603293 607043 := bstep (se 1 (by rfl) ⟨455282, by rfl⟩ : syracuseStep 607043 = 910565) B910565
theorem B607059 : Blo 603293 607059 := bstep (se 1 (by rfl) ⟨455294, by rfl⟩ : syracuseStep 607059 = 910589) B910589
theorem B2048867 : Blo 603293 2048867 := bstep (se 1 (by rfl) ⟨1536650, by rfl⟩ : syracuseStep 2048867 = 3073301) B3073301
theorem B607075 : Blo 603293 607075 := bstep (se 1 (by rfl) ⟨455306, by rfl⟩ : syracuseStep 607075 = 910613) B910613
theorem B607091 : Blo 603293 607091 := bstep (se 1 (by rfl) ⟨455318, by rfl⟩ : syracuseStep 607091 = 910637) B910637
theorem B607107 : Blo 603293 607107 := bstep (se 1 (by rfl) ⟨455330, by rfl⟩ : syracuseStep 607107 = 910661) B910661
theorem B607123 : Blo 603293 607123 := bstep (se 1 (by rfl) ⟨455342, by rfl⟩ : syracuseStep 607123 = 910685) B910685
theorem B607139 : Blo 603293 607139 := bstep (se 1 (by rfl) ⟨455354, by rfl⟩ : syracuseStep 607139 = 910709) B910709
theorem B1360817 : Blo 603293 1360817 := bstep (se 2 (by rfl) ⟨510306, by rfl⟩ : syracuseStep 1360817 = 1020613) B1020613
theorem B607155 : Blo 603293 607155 := bstep (se 1 (by rfl) ⟨455366, by rfl⟩ : syracuseStep 607155 = 910733) B910733
theorem B1360835 : Blo 603293 1360835 := bstep (se 1 (by rfl) ⟨1020626, by rfl⟩ : syracuseStep 1360835 = 2041253) B2041253
theorem B607171 : Blo 603293 607171 := bstep (se 1 (by rfl) ⟨455378, by rfl⟩ : syracuseStep 607171 = 910757) B910757
theorem B607187 : Blo 603293 607187 := bstep (se 1 (by rfl) ⟨455390, by rfl⟩ : syracuseStep 607187 = 910781) B910781
theorem B607203 : Blo 603293 607203 := bstep (se 1 (by rfl) ⟨455402, by rfl⟩ : syracuseStep 607203 = 910805) B910805
theorem B5817329 : Blo 603293 5817329 := bstep (se 2 (by rfl) ⟨2181498, by rfl⟩ : syracuseStep 5817329 = 4362997) B4362997
theorem B607219 : Blo 603293 607219 := bstep (se 1 (by rfl) ⟨455414, by rfl⟩ : syracuseStep 607219 = 910829) B910829
theorem B607235 : Blo 603293 607235 := bstep (se 1 (by rfl) ⟨455426, by rfl⟩ : syracuseStep 607235 = 910853) B910853
theorem B3687437 : Blo 603293 3687437 := bstep (se 3 (by rfl) ⟨691394, by rfl⟩ : syracuseStep 3687437 = 1382789) B1382789
theorem B967697 : Blo 603293 967697 := bstep (se 2 (by rfl) ⟨362886, by rfl⟩ : syracuseStep 967697 = 725773) B725773
theorem B607251 : Blo 603293 607251 := bstep (se 1 (by rfl) ⟨455438, by rfl⟩ : syracuseStep 607251 = 910877) B910877
theorem B1557539 : Blo 603293 1557539 := bstep (se 1 (by rfl) ⟨1168154, by rfl⟩ : syracuseStep 1557539 = 2336309) B2336309
theorem B607267 : Blo 603293 607267 := bstep (se 1 (by rfl) ⟨455450, by rfl⟩ : syracuseStep 607267 = 910901) B910901
theorem B607283 : Blo 603293 607283 := bstep (se 1 (by rfl) ⟨455462, by rfl⟩ : syracuseStep 607283 = 910925) B910925
theorem B967793 : Blo 603293 967793 := bstep (se 2 (by rfl) ⟨362922, by rfl⟩ : syracuseStep 967793 = 725845) B725845
theorem B2049137 : Blo 603293 2049137 := bstep (se 2 (by rfl) ⟨768426, by rfl⟩ : syracuseStep 2049137 = 1536853) B1536853
theorem B967825 : Blo 603293 967825 := bstep (se 2 (by rfl) ⟨362934, by rfl⟩ : syracuseStep 967825 = 725869) B725869
theorem B1361105 : Blo 603293 1361105 := bstep (se 2 (by rfl) ⟨510414, by rfl⟩ : syracuseStep 1361105 = 1020829) B1020829
theorem B1361123 : Blo 603293 1361123 := bstep (se 1 (by rfl) ⟨1020842, by rfl⟩ : syracuseStep 1361123 = 2041685) B2041685
theorem B3065201 : Blo 603293 3065201 := bstep (se 2 (by rfl) ⟨1149450, by rfl⟩ : syracuseStep 3065201 = 2298901) B2298901
theorem B1295747 : Blo 603293 1295747 := bstep (se 1 (by rfl) ⟨971810, by rfl⟩ : syracuseStep 1295747 = 1943621) B1943621
theorem B1361393 : Blo 603293 1361393 := bstep (se 2 (by rfl) ⟨510522, by rfl⟩ : syracuseStep 1361393 = 1021045) B1021045
theorem B1361411 : Blo 603293 1361411 := bstep (se 1 (by rfl) ⟨1021058, by rfl⟩ : syracuseStep 1361411 = 2042117) B2042117
theorem B1033841 : Blo 603293 1033841 := bstep (se 2 (by rfl) ⟨387690, by rfl⟩ : syracuseStep 1033841 = 775381) B775381
theorem B1361681 : Blo 603293 1361681 := bstep (se 2 (by rfl) ⟨510630, by rfl⟩ : syracuseStep 1361681 = 1021261) B1021261
theorem B1361699 : Blo 603293 1361699 := bstep (se 1 (by rfl) ⟨1021274, by rfl⟩ : syracuseStep 1361699 = 2042549) B2042549
theorem B1722161 : Blo 603293 1722161 := bstep (se 2 (by rfl) ⟨645810, by rfl⟩ : syracuseStep 1722161 = 1291621) B1291621
theorem B1296337 : Blo 603293 1296337 := bstep (se 2 (by rfl) ⟨486126, by rfl⟩ : syracuseStep 1296337 = 972253) B972253
theorem B1361969 : Blo 603293 1361969 := bstep (se 2 (by rfl) ⟨510738, by rfl⟩ : syracuseStep 1361969 = 1021477) B1021477
theorem B1361987 : Blo 603293 1361987 := bstep (se 1 (by rfl) ⟨1021490, by rfl⟩ : syracuseStep 1361987 = 2042981) B2042981
theorem B7751821 : Blo 603293 7751821 := bstep (se 3 (by rfl) ⟨1453466, by rfl⟩ : syracuseStep 7751821 = 2906933) B2906933
theorem B1362257 : Blo 603293 1362257 := bstep (se 2 (by rfl) ⟨510846, by rfl⟩ : syracuseStep 1362257 = 1021693) B1021693
theorem B1362275 : Blo 603293 1362275 := bstep (se 1 (by rfl) ⟨1021706, by rfl⟩ : syracuseStep 1362275 = 2043413) B2043413
theorem B4606307 : Blo 603293 4606307 := bstep (se 1 (by rfl) ⟨3454730, by rfl⟩ : syracuseStep 4606307 = 6909461) B6909461
theorem B1722833 : Blo 603293 1722833 := bstep (se 2 (by rfl) ⟨646062, by rfl⟩ : syracuseStep 1722833 = 1292125) B1292125
theorem B1362545 : Blo 603293 1362545 := bstep (se 2 (by rfl) ⟨510954, by rfl⟩ : syracuseStep 1362545 = 1021909) B1021909
theorem B1362563 : Blo 603293 1362563 := bstep (se 1 (by rfl) ⟨1021922, by rfl⟩ : syracuseStep 1362563 = 2043845) B2043845
theorem B3885731 : Blo 603293 3885731 := bstep (se 1 (by rfl) ⟨2914298, by rfl⟩ : syracuseStep 3885731 = 5828597) B5828597
theorem B969491 : Blo 603293 969491 := bstep (se 1 (by rfl) ⟨727118, by rfl⟩ : syracuseStep 969491 = 1454237) B1454237
theorem B3066659 : Blo 603293 3066659 := bstep (se 1 (by rfl) ⟨2299994, by rfl⟩ : syracuseStep 3066659 = 4599989) B4599989
theorem B1362833 : Blo 603293 1362833 := bstep (se 2 (by rfl) ⟨511062, by rfl⟩ : syracuseStep 1362833 = 1022125) B1022125
theorem B1362851 : Blo 603293 1362851 := bstep (se 1 (by rfl) ⟨1022138, by rfl⟩ : syracuseStep 1362851 = 2044277) B2044277
theorem B1363121 : Blo 603293 1363121 := bstep (se 2 (by rfl) ⟨511170, by rfl⟩ : syracuseStep 1363121 = 1022341) B1022341
theorem B1363139 : Blo 603293 1363139 := bstep (se 1 (by rfl) ⟨1022354, by rfl⟩ : syracuseStep 1363139 = 2044709) B2044709
theorem B1723619 : Blo 603293 1723619 := bstep (se 1 (by rfl) ⟨1292714, by rfl⟩ : syracuseStep 1723619 = 2585429) B2585429
theorem B8735971 : Blo 603293 8735971 := bstep (se 1 (by rfl) ⟨6551978, by rfl⟩ : syracuseStep 8735971 = 13103957) B13103957
theorem B970003 : Blo 603293 970003 := bstep (se 1 (by rfl) ⟨727502, by rfl⟩ : syracuseStep 970003 = 1455005) B1455005
theorem B970049 : Blo 603293 970049 := bstep (se 2 (by rfl) ⟨363768, by rfl⟩ : syracuseStep 970049 = 727537) B727537
theorem B5819789 : Blo 603293 5819789 := bstep (se 3 (by rfl) ⟨1091210, by rfl⟩ : syracuseStep 5819789 = 2182421) B2182421
theorem B3689891 : Blo 603293 3689891 := bstep (se 1 (by rfl) ⟨2767418, by rfl⟩ : syracuseStep 3689891 = 5534837) B5534837
theorem B7753157 : Blo 603293 7753157 := bstep (se 4 (by rfl) ⟨726858, by rfl⟩ : syracuseStep 7753157 = 1453717) B1453717
theorem B1363409 : Blo 603293 1363409 := bstep (se 2 (by rfl) ⟨511278, by rfl⟩ : syracuseStep 1363409 = 1022557) B1022557
theorem B1363427 : Blo 603293 1363427 := bstep (se 1 (by rfl) ⟨1022570, by rfl⟩ : syracuseStep 1363427 = 2045141) B2045141
theorem B1723949 : Blo 603293 1723949 := bstep (se 3 (by rfl) ⟨323240, by rfl⟩ : syracuseStep 1723949 = 646481) B646481
theorem B3067469 : Blo 603293 3067469 := bstep (se 3 (by rfl) ⟨575150, by rfl⟩ : syracuseStep 3067469 = 1150301) B1150301
theorem B1724017 : Blo 603293 1724017 := bstep (se 2 (by rfl) ⟨646506, by rfl⟩ : syracuseStep 1724017 = 1293013) B1293013
theorem B1363697 : Blo 603293 1363697 := bstep (se 2 (by rfl) ⟨511386, by rfl⟩ : syracuseStep 1363697 = 1022773) B1022773
theorem B904961 : Blo 603293 904961 := bstep (se 2 (by rfl) ⟨339360, by rfl⟩ : syracuseStep 904961 = 678721) B678721
theorem B1363715 : Blo 603293 1363715 := bstep (se 1 (by rfl) ⟨1022786, by rfl⟩ : syracuseStep 1363715 = 2045573) B2045573
theorem B7884557 : Blo 603293 7884557 := bstep (se 3 (by rfl) ⟨1478354, by rfl⟩ : syracuseStep 7884557 = 2956709) B2956709
theorem B1527569 : Blo 603293 1527569 := bstep (se 2 (by rfl) ⟨572838, by rfl⟩ : syracuseStep 1527569 = 1145677) B1145677
theorem B904979 : Blo 603293 904979 := bstep (se 1 (by rfl) ⟨678734, by rfl⟩ : syracuseStep 904979 = 1357469) B1357469
theorem B905009 : Blo 603293 905009 := bstep (se 2 (by rfl) ⟨339378, by rfl⟩ : syracuseStep 905009 = 678757) B678757
theorem B1527619 : Blo 603293 1527619 := bstep (se 1 (by rfl) ⟨1145714, by rfl⟩ : syracuseStep 1527619 = 2291429) B2291429
theorem B905027 : Blo 603293 905027 := bstep (se 1 (by rfl) ⟨678770, by rfl⟩ : syracuseStep 905027 = 1357541) B1357541
theorem B905057 : Blo 603293 905057 := bstep (se 2 (by rfl) ⟨339396, by rfl⟩ : syracuseStep 905057 = 678793) B678793
theorem B905075 : Blo 603293 905075 := bstep (se 1 (by rfl) ⟨678806, by rfl⟩ : syracuseStep 905075 = 1357613) B1357613
theorem B1724291 : Blo 603293 1724291 := bstep (se 1 (by rfl) ⟨1293218, by rfl⟩ : syracuseStep 1724291 = 2586437) B2586437
theorem B10309517 : Blo 603293 10309517 := bstep (se 3 (by rfl) ⟨1933034, by rfl⟩ : syracuseStep 10309517 = 3866069) B3866069
theorem B905105 : Blo 603293 905105 := bstep (se 2 (by rfl) ⟨339414, by rfl⟩ : syracuseStep 905105 = 678829) B678829
theorem B905123 : Blo 603293 905123 := bstep (se 1 (by rfl) ⟨678842, by rfl⟩ : syracuseStep 905123 = 1357685) B1357685
theorem B774067 : Blo 603293 774067 := bstep (se 1 (by rfl) ⟨580550, by rfl⟩ : syracuseStep 774067 = 1161101) B1161101
theorem B905153 : Blo 603293 905153 := bstep (se 2 (by rfl) ⟨339432, by rfl⟩ : syracuseStep 905153 = 678865) B678865
theorem B1527761 : Blo 603293 1527761 := bstep (se 2 (by rfl) ⟨572910, by rfl⟩ : syracuseStep 1527761 = 1145821) B1145821
theorem B905171 : Blo 603293 905171 := bstep (se 1 (by rfl) ⟨678878, by rfl⟩ : syracuseStep 905171 = 1357757) B1357757
theorem B970721 : Blo 603293 970721 := bstep (se 2 (by rfl) ⟨364020, by rfl⟩ : syracuseStep 970721 = 728041) B728041
theorem B905201 : Blo 603293 905201 := bstep (se 2 (by rfl) ⟨339450, by rfl⟩ : syracuseStep 905201 = 678901) B678901
theorem B905219 : Blo 603293 905219 := bstep (se 1 (by rfl) ⟨678914, by rfl⟩ : syracuseStep 905219 = 1357829) B1357829
theorem B1363985 : Blo 603293 1363985 := bstep (se 2 (by rfl) ⟨511494, by rfl⟩ : syracuseStep 1363985 = 1022989) B1022989
theorem B905249 : Blo 603293 905249 := bstep (se 2 (by rfl) ⟨339468, by rfl⟩ : syracuseStep 905249 = 678937) B678937
theorem B1364003 : Blo 603293 1364003 := bstep (se 1 (by rfl) ⟨1023002, by rfl⟩ : syracuseStep 1364003 = 2046005) B2046005
theorem B905267 : Blo 603293 905267 := bstep (se 1 (by rfl) ⟨678950, by rfl⟩ : syracuseStep 905267 = 1357901) B1357901
theorem B905297 : Blo 603293 905297 := bstep (se 2 (by rfl) ⟨339486, by rfl⟩ : syracuseStep 905297 = 678973) B678973
theorem B905315 : Blo 603293 905315 := bstep (se 1 (by rfl) ⟨678986, by rfl⟩ : syracuseStep 905315 = 1357973) B1357973
theorem B905345 : Blo 603293 905345 := bstep (se 2 (by rfl) ⟨339504, by rfl⟩ : syracuseStep 905345 = 679009) B679009
theorem B905363 : Blo 603293 905363 := bstep (se 1 (by rfl) ⟨679022, by rfl⟩ : syracuseStep 905363 = 1358045) B1358045
theorem B905393 : Blo 603293 905393 := bstep (se 2 (by rfl) ⟨339522, by rfl⟩ : syracuseStep 905393 = 679045) B679045
theorem B2183345 : Blo 603293 2183345 := bstep (se 2 (by rfl) ⟨818754, by rfl⟩ : syracuseStep 2183345 = 1637509) B1637509
theorem B905411 : Blo 603293 905411 := bstep (se 1 (by rfl) ⟨679058, by rfl⟩ : syracuseStep 905411 = 1358117) B1358117
theorem B905441 : Blo 603293 905441 := bstep (se 2 (by rfl) ⟨339540, by rfl⟩ : syracuseStep 905441 = 679081) B679081
theorem B905459 : Blo 603293 905459 := bstep (se 1 (by rfl) ⟨679094, by rfl⟩ : syracuseStep 905459 = 1358189) B1358189
theorem B7852301 : Blo 603293 7852301 := bstep (se 3 (by rfl) ⟨1472306, by rfl⟩ : syracuseStep 7852301 = 2944613) B2944613
theorem B905489 : Blo 603293 905489 := bstep (se 2 (by rfl) ⟨339558, by rfl⟩ : syracuseStep 905489 = 679117) B679117
theorem B905507 : Blo 603293 905507 := bstep (se 1 (by rfl) ⟨679130, by rfl⟩ : syracuseStep 905507 = 1358261) B1358261
theorem B1364273 : Blo 603293 1364273 := bstep (se 2 (by rfl) ⟨511602, by rfl⟩ : syracuseStep 1364273 = 1023205) B1023205
theorem B905537 : Blo 603293 905537 := bstep (se 2 (by rfl) ⟨339576, by rfl⟩ : syracuseStep 905537 = 679153) B679153
theorem B1364291 : Blo 603293 1364291 := bstep (se 1 (by rfl) ⟨1023218, by rfl⟩ : syracuseStep 1364291 = 2046437) B2046437
theorem B905555 : Blo 603293 905555 := bstep (se 1 (by rfl) ⟨679166, by rfl⟩ : syracuseStep 905555 = 1358333) B1358333
theorem B905585 : Blo 603293 905585 := bstep (se 2 (by rfl) ⟨339594, by rfl⟩ : syracuseStep 905585 = 679189) B679189
theorem B905603 : Blo 603293 905603 := bstep (se 1 (by rfl) ⟨679202, by rfl⟩ : syracuseStep 905603 = 1358405) B1358405
theorem B905633 : Blo 603293 905633 := bstep (se 2 (by rfl) ⟨339612, by rfl⟩ : syracuseStep 905633 = 679225) B679225
theorem B905651 : Blo 603293 905651 := bstep (se 1 (by rfl) ⟨679238, by rfl⟩ : syracuseStep 905651 = 1358477) B1358477
theorem B17912261 : Blo 603293 17912261 := bstep (se 4 (by rfl) ⟨1679274, by rfl⟩ : syracuseStep 17912261 = 3358549) B3358549
theorem B905681 : Blo 603293 905681 := bstep (se 2 (by rfl) ⟨339630, by rfl⟩ : syracuseStep 905681 = 679261) B679261
theorem B971233 : Blo 603293 971233 := bstep (se 2 (by rfl) ⟨364212, by rfl⟩ : syracuseStep 971233 = 728425) B728425
theorem B905699 : Blo 603293 905699 := bstep (se 1 (by rfl) ⟨679274, by rfl⟩ : syracuseStep 905699 = 1358549) B1358549
theorem B905729 : Blo 603293 905729 := bstep (se 2 (by rfl) ⟨339648, by rfl⟩ : syracuseStep 905729 = 679297) B679297
theorem B905747 : Blo 603293 905747 := bstep (se 1 (by rfl) ⟨679310, by rfl⟩ : syracuseStep 905747 = 1358621) B1358621
theorem B905777 : Blo 603293 905777 := bstep (se 2 (by rfl) ⟨339666, by rfl⟩ : syracuseStep 905777 = 679333) B679333
theorem B905795 : Blo 603293 905795 := bstep (se 1 (by rfl) ⟨679346, by rfl⟩ : syracuseStep 905795 = 1358693) B1358693
theorem B1364561 : Blo 603293 1364561 := bstep (se 2 (by rfl) ⟨511710, by rfl⟩ : syracuseStep 1364561 = 1023421) B1023421
theorem B905825 : Blo 603293 905825 := bstep (se 2 (by rfl) ⟨339684, by rfl⟩ : syracuseStep 905825 = 679369) B679369
theorem B1364579 : Blo 603293 1364579 := bstep (se 1 (by rfl) ⟨1023434, by rfl⟩ : syracuseStep 1364579 = 2046869) B2046869
theorem B905843 : Blo 603293 905843 := bstep (se 1 (by rfl) ⟨679382, by rfl⟩ : syracuseStep 905843 = 1358765) B1358765
theorem B905873 : Blo 603293 905873 := bstep (se 2 (by rfl) ⟨339702, by rfl⟩ : syracuseStep 905873 = 679405) B679405
theorem B905891 : Blo 603293 905891 := bstep (se 1 (by rfl) ⟨679418, by rfl⟩ : syracuseStep 905891 = 1358837) B1358837
theorem B905921 : Blo 603293 905921 := bstep (se 2 (by rfl) ⟨339720, by rfl⟩ : syracuseStep 905921 = 679441) B679441
theorem B2904781 : Blo 603293 2904781 := bstep (se 3 (by rfl) ⟨544646, by rfl⟩ : syracuseStep 2904781 = 1089293) B1089293
theorem B1725133 : Blo 603293 1725133 := bstep (se 3 (by rfl) ⟨323462, by rfl⟩ : syracuseStep 1725133 = 646925) B646925
theorem B905939 : Blo 603293 905939 := bstep (se 1 (by rfl) ⟨679454, by rfl⟩ : syracuseStep 905939 = 1358909) B1358909
theorem B905969 : Blo 603293 905969 := bstep (se 2 (by rfl) ⟨339738, by rfl⟩ : syracuseStep 905969 = 679477) B679477
theorem B905987 : Blo 603293 905987 := bstep (se 1 (by rfl) ⟨679490, by rfl⟩ : syracuseStep 905987 = 1358981) B1358981
theorem B906017 : Blo 603293 906017 := bstep (se 2 (by rfl) ⟨339756, by rfl⟩ : syracuseStep 906017 = 679513) B679513
theorem B906035 : Blo 603293 906035 := bstep (se 1 (by rfl) ⟨679526, by rfl⟩ : syracuseStep 906035 = 1359053) B1359053
theorem B906065 : Blo 603293 906065 := bstep (se 2 (by rfl) ⟨339774, by rfl⟩ : syracuseStep 906065 = 679549) B679549
theorem B906083 : Blo 603293 906083 := bstep (se 1 (by rfl) ⟨679562, by rfl⟩ : syracuseStep 906083 = 1359125) B1359125
theorem B1725293 : Blo 603293 1725293 := bstep (se 3 (by rfl) ⟨323492, by rfl⟩ : syracuseStep 1725293 = 646985) B646985
theorem B1364849 : Blo 603293 1364849 := bstep (se 2 (by rfl) ⟨511818, by rfl⟩ : syracuseStep 1364849 = 1023637) B1023637
theorem B906113 : Blo 603293 906113 := bstep (se 2 (by rfl) ⟨339792, by rfl⟩ : syracuseStep 906113 = 679585) B679585
theorem B1364867 : Blo 603293 1364867 := bstep (se 1 (by rfl) ⟨1023650, by rfl⟩ : syracuseStep 1364867 = 2047301) B2047301
theorem B906131 : Blo 603293 906131 := bstep (se 1 (by rfl) ⟨679598, by rfl⟩ : syracuseStep 906131 = 1359197) B1359197
theorem B1528753 : Blo 603293 1528753 := bstep (se 2 (by rfl) ⟨573282, by rfl⟩ : syracuseStep 1528753 = 1146565) B1146565
theorem B906161 : Blo 603293 906161 := bstep (se 2 (by rfl) ⟨339810, by rfl⟩ : syracuseStep 906161 = 679621) B679621
theorem B906179 : Blo 603293 906179 := bstep (se 1 (by rfl) ⟨679634, by rfl⟩ : syracuseStep 906179 = 1359269) B1359269
theorem B906209 : Blo 603293 906209 := bstep (se 2 (by rfl) ⟨339828, by rfl⟩ : syracuseStep 906209 = 679657) B679657
theorem B906227 : Blo 603293 906227 := bstep (se 1 (by rfl) ⟨679670, by rfl⟩ : syracuseStep 906227 = 1359341) B1359341
theorem B906257 : Blo 603293 906257 := bstep (se 2 (by rfl) ⟨339846, by rfl⟩ : syracuseStep 906257 = 679693) B679693
theorem B906275 : Blo 603293 906275 := bstep (se 1 (by rfl) ⟨679706, by rfl⟩ : syracuseStep 906275 = 1359413) B1359413
theorem B1725475 : Blo 603293 1725475 := bstep (se 1 (by rfl) ⟨1294106, by rfl⟩ : syracuseStep 1725475 = 2588213) B2588213
theorem B906305 : Blo 603293 906305 := bstep (se 2 (by rfl) ⟨339864, by rfl⟩ : syracuseStep 906305 = 679729) B679729
theorem B906323 : Blo 603293 906323 := bstep (se 1 (by rfl) ⟨679742, by rfl⟩ : syracuseStep 906323 = 1359485) B1359485
theorem B906353 : Blo 603293 906353 := bstep (se 2 (by rfl) ⟨339882, by rfl⟩ : syracuseStep 906353 = 679765) B679765
theorem B906371 : Blo 603293 906371 := bstep (se 1 (by rfl) ⟨679778, by rfl⟩ : syracuseStep 906371 = 1359557) B1359557
theorem B1365137 : Blo 603293 1365137 := bstep (se 2 (by rfl) ⟨511926, by rfl⟩ : syracuseStep 1365137 = 1023853) B1023853
theorem B906401 : Blo 603293 906401 := bstep (se 2 (by rfl) ⟨339900, by rfl⟩ : syracuseStep 906401 = 679801) B679801
theorem B1365155 : Blo 603293 1365155 := bstep (se 1 (by rfl) ⟨1023866, by rfl⟩ : syracuseStep 1365155 = 2047733) B2047733
theorem B906419 : Blo 603293 906419 := bstep (se 1 (by rfl) ⟨679814, by rfl⟩ : syracuseStep 906419 = 1359629) B1359629
theorem B1529027 : Blo 603293 1529027 := bstep (se 1 (by rfl) ⟨1146770, by rfl⟩ : syracuseStep 1529027 = 2293541) B2293541
theorem B906449 : Blo 603293 906449 := bstep (se 2 (by rfl) ⟨339918, by rfl⟩ : syracuseStep 906449 = 679837) B679837
theorem B906467 : Blo 603293 906467 := bstep (se 1 (by rfl) ⟨679850, by rfl⟩ : syracuseStep 906467 = 1359701) B1359701
theorem B906497 : Blo 603293 906497 := bstep (se 2 (by rfl) ⟨339936, by rfl⟩ : syracuseStep 906497 = 679873) B679873
theorem B906515 : Blo 603293 906515 := bstep (se 1 (by rfl) ⟨679886, by rfl⟩ : syracuseStep 906515 = 1359773) B1359773
theorem B906545 : Blo 603293 906545 := bstep (se 2 (by rfl) ⟨339954, by rfl⟩ : syracuseStep 906545 = 679909) B679909
theorem B906563 : Blo 603293 906563 := bstep (se 1 (by rfl) ⟨679922, by rfl⟩ : syracuseStep 906563 = 1359845) B1359845
theorem B906593 : Blo 603293 906593 := bstep (se 2 (by rfl) ⟨339972, by rfl⟩ : syracuseStep 906593 = 679945) B679945
theorem B906611 : Blo 603293 906611 := bstep (se 1 (by rfl) ⟨679958, by rfl⟩ : syracuseStep 906611 = 1359917) B1359917
theorem B1529219 : Blo 603293 1529219 := bstep (se 1 (by rfl) ⟨1146914, by rfl⟩ : syracuseStep 1529219 = 2293829) B2293829
theorem B906641 : Blo 603293 906641 := bstep (se 2 (by rfl) ⟨339990, by rfl⟩ : syracuseStep 906641 = 679981) B679981
theorem B873875 : Blo 603293 873875 := bstep (se 1 (by rfl) ⟨655406, by rfl⟩ : syracuseStep 873875 = 1310813) B1310813
theorem B906659 : Blo 603293 906659 := bstep (se 1 (by rfl) ⟨679994, by rfl⟩ : syracuseStep 906659 = 1359989) B1359989
theorem B1365425 : Blo 603293 1365425 := bstep (se 2 (by rfl) ⟨512034, by rfl⟩ : syracuseStep 1365425 = 1024069) B1024069
theorem B906689 : Blo 603293 906689 := bstep (se 2 (by rfl) ⟨340008, by rfl⟩ : syracuseStep 906689 = 680017) B680017
theorem B1365443 : Blo 603293 1365443 := bstep (se 1 (by rfl) ⟨1024082, by rfl⟩ : syracuseStep 1365443 = 2048165) B2048165
theorem B906707 : Blo 603293 906707 := bstep (se 1 (by rfl) ⟨680030, by rfl⟩ : syracuseStep 906707 = 1360061) B1360061
theorem B906737 : Blo 603293 906737 := bstep (se 2 (by rfl) ⟨340026, by rfl⟩ : syracuseStep 906737 = 680053) B680053
theorem B906755 : Blo 603293 906755 := bstep (se 1 (by rfl) ⟨680066, by rfl⟩ : syracuseStep 906755 = 1360133) B1360133
theorem B906785 : Blo 603293 906785 := bstep (se 2 (by rfl) ⟨340044, by rfl⟩ : syracuseStep 906785 = 680089) B680089
theorem B906803 : Blo 603293 906803 := bstep (se 1 (by rfl) ⟨680102, by rfl⟩ : syracuseStep 906803 = 1360205) B1360205
theorem B906833 : Blo 603293 906833 := bstep (se 2 (by rfl) ⟨340062, by rfl⟩ : syracuseStep 906833 = 680125) B680125
theorem B906851 : Blo 603293 906851 := bstep (se 1 (by rfl) ⟨680138, by rfl⟩ : syracuseStep 906851 = 1360277) B1360277
theorem B2184803 : Blo 603293 2184803 := bstep (se 1 (by rfl) ⟨1638602, by rfl⟩ : syracuseStep 2184803 = 3277205) B3277205
theorem B906881 : Blo 603293 906881 := bstep (se 2 (by rfl) ⟨340080, by rfl⟩ : syracuseStep 906881 = 680161) B680161
theorem B906899 : Blo 603293 906899 := bstep (se 1 (by rfl) ⟨680174, by rfl⟩ : syracuseStep 906899 = 1360349) B1360349
theorem B906929 : Blo 603293 906929 := bstep (se 2 (by rfl) ⟨340098, by rfl⟩ : syracuseStep 906929 = 680197) B680197
theorem B906947 : Blo 603293 906947 := bstep (se 1 (by rfl) ⟨680210, by rfl⟩ : syracuseStep 906947 = 1360421) B1360421
theorem B1660621 : Blo 603293 1660621 := bstep (se 3 (by rfl) ⟨311366, by rfl⟩ : syracuseStep 1660621 = 622733) B622733
theorem B1365713 : Blo 603293 1365713 := bstep (se 2 (by rfl) ⟨512142, by rfl⟩ : syracuseStep 1365713 = 1024285) B1024285
theorem B906977 : Blo 603293 906977 := bstep (se 2 (by rfl) ⟨340116, by rfl⟩ : syracuseStep 906977 = 680233) B680233
theorem B1365731 : Blo 603293 1365731 := bstep (se 1 (by rfl) ⟨1024298, by rfl⟩ : syracuseStep 1365731 = 2048597) B2048597
theorem B972515 : Blo 603293 972515 := bstep (se 1 (by rfl) ⟨729386, by rfl⟩ : syracuseStep 972515 = 1458773) B1458773
theorem B3888881 : Blo 603293 3888881 := bstep (se 2 (by rfl) ⟨1458330, by rfl⟩ : syracuseStep 3888881 = 2916661) B2916661
theorem B906995 : Blo 603293 906995 := bstep (se 1 (by rfl) ⟨680246, by rfl⟩ : syracuseStep 906995 = 1360493) B1360493
theorem B907025 : Blo 603293 907025 := bstep (se 2 (by rfl) ⟨340134, by rfl⟩ : syracuseStep 907025 = 680269) B680269
theorem B907043 : Blo 603293 907043 := bstep (se 1 (by rfl) ⟨680282, by rfl⟩ : syracuseStep 907043 = 1360565) B1360565
theorem B3888931 : Blo 603293 3888931 := bstep (se 1 (by rfl) ⟨2916698, by rfl⟩ : syracuseStep 3888931 = 5833397) B5833397
theorem B907073 : Blo 603293 907073 := bstep (se 2 (by rfl) ⟨340152, by rfl⟩ : syracuseStep 907073 = 680305) B680305
theorem B907091 : Blo 603293 907091 := bstep (se 1 (by rfl) ⟨680318, by rfl⟩ : syracuseStep 907091 = 1360637) B1360637
theorem B972643 : Blo 603293 972643 := bstep (se 1 (by rfl) ⟨729482, by rfl⟩ : syracuseStep 972643 = 1458965) B1458965
theorem B907121 : Blo 603293 907121 := bstep (se 2 (by rfl) ⟨340170, by rfl⟩ : syracuseStep 907121 = 680341) B680341
theorem B907139 : Blo 603293 907139 := bstep (se 1 (by rfl) ⟨680354, by rfl⟩ : syracuseStep 907139 = 1360709) B1360709
theorem B907169 : Blo 603293 907169 := bstep (se 2 (by rfl) ⟨340188, by rfl⟩ : syracuseStep 907169 = 680377) B680377
theorem B907187 : Blo 603293 907187 := bstep (se 1 (by rfl) ⟨680390, by rfl⟩ : syracuseStep 907187 = 1360781) B1360781
theorem B907217 : Blo 603293 907217 := bstep (se 2 (by rfl) ⟨340206, by rfl⟩ : syracuseStep 907217 = 680413) B680413
theorem B907235 : Blo 603293 907235 := bstep (se 1 (by rfl) ⟨680426, by rfl⟩ : syracuseStep 907235 = 1360853) B1360853
theorem B1366001 : Blo 603293 1366001 := bstep (se 2 (by rfl) ⟨512250, by rfl⟩ : syracuseStep 1366001 = 1024501) B1024501
theorem B907265 : Blo 603293 907265 := bstep (se 2 (by rfl) ⟨340224, by rfl⟩ : syracuseStep 907265 = 680449) B680449
theorem B1366019 : Blo 603293 1366019 := bstep (se 1 (by rfl) ⟨1024514, by rfl⟩ : syracuseStep 1366019 = 2049029) B2049029
theorem B907283 : Blo 603293 907283 := bstep (se 1 (by rfl) ⟨680462, by rfl⟩ : syracuseStep 907283 = 1360925) B1360925
theorem B907313 : Blo 603293 907313 := bstep (se 2 (by rfl) ⟨340242, by rfl⟩ : syracuseStep 907313 = 680485) B680485
theorem B907331 : Blo 603293 907331 := bstep (se 1 (by rfl) ⟨680498, by rfl⟩ : syracuseStep 907331 = 1360997) B1360997
theorem B907361 : Blo 603293 907361 := bstep (se 2 (by rfl) ⟨340260, by rfl⟩ : syracuseStep 907361 = 680521) B680521
theorem B907379 : Blo 603293 907379 := bstep (se 1 (by rfl) ⟨680534, by rfl⟩ : syracuseStep 907379 = 1361069) B1361069
theorem B1038467 : Blo 603293 1038467 := bstep (se 1 (by rfl) ⟨778850, by rfl⟩ : syracuseStep 1038467 = 1557701) B1557701
theorem B907409 : Blo 603293 907409 := bstep (se 2 (by rfl) ⟨340278, by rfl⟩ : syracuseStep 907409 = 680557) B680557
theorem B907427 : Blo 603293 907427 := bstep (se 1 (by rfl) ⟨680570, by rfl⟩ : syracuseStep 907427 = 1361141) B1361141
theorem B2185379 : Blo 603293 2185379 := bstep (se 1 (by rfl) ⟨1639034, by rfl⟩ : syracuseStep 2185379 = 3278069) B3278069
theorem B907457 : Blo 603293 907457 := bstep (se 2 (by rfl) ⟨340296, by rfl⟩ : syracuseStep 907457 = 680593) B680593
theorem B907475 : Blo 603293 907475 := bstep (se 1 (by rfl) ⟨680606, by rfl⟩ : syracuseStep 907475 = 1361213) B1361213
theorem B907505 : Blo 603293 907505 := bstep (se 2 (by rfl) ⟨340314, by rfl⟩ : syracuseStep 907505 = 680629) B680629
theorem B907523 : Blo 603293 907523 := bstep (se 1 (by rfl) ⟨680642, by rfl⟩ : syracuseStep 907523 = 1361285) B1361285
theorem B1366289 : Blo 603293 1366289 := bstep (se 2 (by rfl) ⟨512358, by rfl⟩ : syracuseStep 1366289 = 1024717) B1024717
theorem B907553 : Blo 603293 907553 := bstep (se 2 (by rfl) ⟨340332, by rfl⟩ : syracuseStep 907553 = 680665) B680665
theorem B1366307 : Blo 603293 1366307 := bstep (se 1 (by rfl) ⟨1024730, by rfl⟩ : syracuseStep 1366307 = 2049461) B2049461
theorem B1530161 : Blo 603293 1530161 := bstep (se 2 (by rfl) ⟨573810, by rfl⟩ : syracuseStep 1530161 = 1147621) B1147621
theorem B907571 : Blo 603293 907571 := bstep (se 1 (by rfl) ⟨680678, by rfl⟩ : syracuseStep 907571 = 1361357) B1361357
theorem B907601 : Blo 603293 907601 := bstep (se 2 (by rfl) ⟨340350, by rfl⟩ : syracuseStep 907601 = 680701) B680701
theorem B1530211 : Blo 603293 1530211 := bstep (se 1 (by rfl) ⟨1147658, by rfl⟩ : syracuseStep 1530211 = 2295317) B2295317
theorem B907619 : Blo 603293 907619 := bstep (se 1 (by rfl) ⟨680714, by rfl⟩ : syracuseStep 907619 = 1361429) B1361429
theorem B907649 : Blo 603293 907649 := bstep (se 2 (by rfl) ⟨340368, by rfl⟩ : syracuseStep 907649 = 680737) B680737
theorem B1726865 : Blo 603293 1726865 := bstep (se 2 (by rfl) ⟨647574, by rfl⟩ : syracuseStep 1726865 = 1295149) B1295149
theorem B907667 : Blo 603293 907667 := bstep (se 1 (by rfl) ⟨680750, by rfl⟩ : syracuseStep 907667 = 1361501) B1361501
theorem B907697 : Blo 603293 907697 := bstep (se 2 (by rfl) ⟨340386, by rfl⟩ : syracuseStep 907697 = 680773) B680773
theorem B3070385 : Blo 603293 3070385 := bstep (se 2 (by rfl) ⟨1151394, by rfl⟩ : syracuseStep 3070385 = 2302789) B2302789
theorem B907715 : Blo 603293 907715 := bstep (se 1 (by rfl) ⟨680786, by rfl⟩ : syracuseStep 907715 = 1361573) B1361573
theorem B907745 : Blo 603293 907745 := bstep (se 2 (by rfl) ⟨340404, by rfl⟩ : syracuseStep 907745 = 680809) B680809
theorem B1530353 : Blo 603293 1530353 := bstep (se 2 (by rfl) ⟨573882, by rfl⟩ : syracuseStep 1530353 = 1147765) B1147765
theorem B907763 : Blo 603293 907763 := bstep (se 1 (by rfl) ⟨680822, by rfl⟩ : syracuseStep 907763 = 1361645) B1361645
theorem B907793 : Blo 603293 907793 := bstep (se 2 (by rfl) ⟨340422, by rfl⟩ : syracuseStep 907793 = 680845) B680845
theorem B907811 : Blo 603293 907811 := bstep (se 1 (by rfl) ⟨680858, by rfl⟩ : syracuseStep 907811 = 1361717) B1361717
theorem B907841 : Blo 603293 907841 := bstep (se 2 (by rfl) ⟨340440, by rfl⟩ : syracuseStep 907841 = 680881) B680881
theorem B907859 : Blo 603293 907859 := bstep (se 1 (by rfl) ⟨680894, by rfl⟩ : syracuseStep 907859 = 1361789) B1361789
theorem B907889 : Blo 603293 907889 := bstep (se 2 (by rfl) ⟨340458, by rfl⟩ : syracuseStep 907889 = 680917) B680917
theorem B907907 : Blo 603293 907907 := bstep (se 1 (by rfl) ⟨680930, by rfl⟩ : syracuseStep 907907 = 1361861) B1361861
theorem B907937 : Blo 603293 907937 := bstep (se 2 (by rfl) ⟨340476, by rfl⟩ : syracuseStep 907937 = 680953) B680953
theorem B907955 : Blo 603293 907955 := bstep (se 1 (by rfl) ⟨680966, by rfl⟩ : syracuseStep 907955 = 1361933) B1361933
theorem B907985 : Blo 603293 907985 := bstep (se 2 (by rfl) ⟨340494, by rfl⟩ : syracuseStep 907985 = 680989) B680989
theorem B908003 : Blo 603293 908003 := bstep (se 1 (by rfl) ⟨681002, by rfl⟩ : syracuseStep 908003 = 1362005) B1362005
theorem B908033 : Blo 603293 908033 := bstep (se 2 (by rfl) ⟨340512, by rfl⟩ : syracuseStep 908033 = 681025) B681025
theorem B908051 : Blo 603293 908051 := bstep (se 1 (by rfl) ⟨681038, by rfl⟩ : syracuseStep 908051 = 1362077) B1362077
theorem B908081 : Blo 603293 908081 := bstep (se 2 (by rfl) ⟨340530, by rfl⟩ : syracuseStep 908081 = 681061) B681061
theorem B908099 : Blo 603293 908099 := bstep (se 1 (by rfl) ⟨681074, by rfl⟩ : syracuseStep 908099 = 1362149) B1362149
theorem B678739 : Blo 603293 678739 := bstep (se 1 (by rfl) ⟨509054, by rfl⟩ : syracuseStep 678739 = 1018109) B1018109
theorem B908129 : Blo 603293 908129 := bstep (se 2 (by rfl) ⟨340548, by rfl⟩ : syracuseStep 908129 = 681097) B681097
theorem B908147 : Blo 603293 908147 := bstep (se 1 (by rfl) ⟨681110, by rfl⟩ : syracuseStep 908147 = 1362221) B1362221
theorem B908177 : Blo 603293 908177 := bstep (se 2 (by rfl) ⟨340566, by rfl⟩ : syracuseStep 908177 = 681133) B681133
theorem B2579363 : Blo 603293 2579363 := bstep (se 1 (by rfl) ⟨1934522, by rfl⟩ : syracuseStep 2579363 = 3869045) B3869045
theorem B908195 : Blo 603293 908195 := bstep (se 1 (by rfl) ⟨681146, by rfl⟩ : syracuseStep 908195 = 1362293) B1362293
theorem B908225 : Blo 603293 908225 := bstep (se 2 (by rfl) ⟨340584, by rfl⟩ : syracuseStep 908225 = 681169) B681169
theorem B3267533 : Blo 603293 3267533 := bstep (se 3 (by rfl) ⟨612662, by rfl⟩ : syracuseStep 3267533 = 1225325) B1225325
theorem B908243 : Blo 603293 908243 := bstep (se 1 (by rfl) ⟨681182, by rfl⟩ : syracuseStep 908243 = 1362365) B1362365
theorem B678883 : Blo 603293 678883 := bstep (se 1 (by rfl) ⟨509162, by rfl⟩ : syracuseStep 678883 = 1018325) B1018325
theorem B908273 : Blo 603293 908273 := bstep (se 2 (by rfl) ⟨340602, by rfl⟩ : syracuseStep 908273 = 681205) B681205
theorem B908291 : Blo 603293 908291 := bstep (se 1 (by rfl) ⟨681218, by rfl⟩ : syracuseStep 908291 = 1362437) B1362437
theorem B4709389 : Blo 603293 4709389 := bstep (se 3 (by rfl) ⟨883010, by rfl⟩ : syracuseStep 4709389 = 1766021) B1766021
theorem B908321 : Blo 603293 908321 := bstep (se 2 (by rfl) ⟨340620, by rfl⟩ : syracuseStep 908321 = 681241) B681241
theorem B908339 : Blo 603293 908339 := bstep (se 1 (by rfl) ⟨681254, by rfl⟩ : syracuseStep 908339 = 1362509) B1362509
theorem B908369 : Blo 603293 908369 := bstep (se 2 (by rfl) ⟨340638, by rfl⟩ : syracuseStep 908369 = 681277) B681277
theorem B908387 : Blo 603293 908387 := bstep (se 1 (by rfl) ⟨681290, by rfl⟩ : syracuseStep 908387 = 1362581) B1362581
theorem B679027 : Blo 603293 679027 := bstep (se 1 (by rfl) ⟨509270, by rfl⟩ : syracuseStep 679027 = 1018541) B1018541
theorem B908417 : Blo 603293 908417 := bstep (se 2 (by rfl) ⟨340656, by rfl⟩ : syracuseStep 908417 = 681313) B681313
theorem B908435 : Blo 603293 908435 := bstep (se 1 (by rfl) ⟨681326, by rfl⟩ : syracuseStep 908435 = 1362653) B1362653
theorem B908465 : Blo 603293 908465 := bstep (se 2 (by rfl) ⟨340674, by rfl⟩ : syracuseStep 908465 = 681349) B681349
theorem B908483 : Blo 603293 908483 := bstep (se 1 (by rfl) ⟨681362, by rfl⟩ : syracuseStep 908483 = 1362725) B1362725
theorem B908513 : Blo 603293 908513 := bstep (se 2 (by rfl) ⟨340692, by rfl⟩ : syracuseStep 908513 = 681385) B681385
theorem B908531 : Blo 603293 908531 := bstep (se 1 (by rfl) ⟨681398, by rfl⟩ : syracuseStep 908531 = 1362797) B1362797
theorem B679171 : Blo 603293 679171 := bstep (se 1 (by rfl) ⟨509378, by rfl⟩ : syracuseStep 679171 = 1018757) B1018757
theorem B908561 : Blo 603293 908561 := bstep (se 2 (by rfl) ⟨340710, by rfl⟩ : syracuseStep 908561 = 681421) B681421
theorem B908579 : Blo 603293 908579 := bstep (se 1 (by rfl) ⟨681434, by rfl⟩ : syracuseStep 908579 = 1362869) B1362869
theorem B908609 : Blo 603293 908609 := bstep (se 2 (by rfl) ⟨340728, by rfl⟩ : syracuseStep 908609 = 681457) B681457
theorem B1727821 : Blo 603293 1727821 := bstep (se 3 (by rfl) ⟨323966, by rfl⟩ : syracuseStep 1727821 = 647933) B647933
theorem B908627 : Blo 603293 908627 := bstep (se 1 (by rfl) ⟨681470, by rfl⟩ : syracuseStep 908627 = 1362941) B1362941
theorem B908657 : Blo 603293 908657 := bstep (se 2 (by rfl) ⟨340746, by rfl⟩ : syracuseStep 908657 = 681493) B681493
theorem B908675 : Blo 603293 908675 := bstep (se 1 (by rfl) ⟨681506, by rfl⟩ : syracuseStep 908675 = 1363013) B1363013
theorem B9330061 : Blo 603293 9330061 := bstep (se 3 (by rfl) ⟨1749386, by rfl⟩ : syracuseStep 9330061 = 3498773) B3498773
theorem B679315 : Blo 603293 679315 := bstep (se 1 (by rfl) ⟨509486, by rfl⟩ : syracuseStep 679315 = 1018973) B1018973
theorem B908705 : Blo 603293 908705 := bstep (se 2 (by rfl) ⟨340764, by rfl⟩ : syracuseStep 908705 = 681529) B681529
theorem B908723 : Blo 603293 908723 := bstep (se 1 (by rfl) ⟨681542, by rfl⟩ : syracuseStep 908723 = 1363085) B1363085
theorem B1531345 : Blo 603293 1531345 := bstep (se 2 (by rfl) ⟨574254, by rfl⟩ : syracuseStep 1531345 = 1148509) B1148509
theorem B908753 : Blo 603293 908753 := bstep (se 2 (by rfl) ⟨340782, by rfl⟩ : syracuseStep 908753 = 681565) B681565
theorem B908771 : Blo 603293 908771 := bstep (se 1 (by rfl) ⟨681578, by rfl⟩ : syracuseStep 908771 = 1363157) B1363157
theorem B908801 : Blo 603293 908801 := bstep (se 2 (by rfl) ⟨340800, by rfl⟩ : syracuseStep 908801 = 681601) B681601
theorem B908819 : Blo 603293 908819 := bstep (se 1 (by rfl) ⟨681614, by rfl⟩ : syracuseStep 908819 = 1363229) B1363229
theorem B679459 : Blo 603293 679459 := bstep (se 1 (by rfl) ⟨509594, by rfl⟩ : syracuseStep 679459 = 1019189) B1019189
theorem B908849 : Blo 603293 908849 := bstep (se 2 (by rfl) ⟨340818, by rfl⟩ : syracuseStep 908849 = 681637) B681637
theorem B1728049 : Blo 603293 1728049 := bstep (se 2 (by rfl) ⟨648018, by rfl⟩ : syracuseStep 1728049 = 1296037) B1296037
theorem B908867 : Blo 603293 908867 := bstep (se 1 (by rfl) ⟨681650, by rfl⟩ : syracuseStep 908867 = 1363301) B1363301
theorem B908897 : Blo 603293 908897 := bstep (se 2 (by rfl) ⟨340836, by rfl⟩ : syracuseStep 908897 = 681673) B681673
theorem B908915 : Blo 603293 908915 := bstep (se 1 (by rfl) ⟨681686, by rfl⟩ : syracuseStep 908915 = 1363373) B1363373
theorem B908945 : Blo 603293 908945 := bstep (se 2 (by rfl) ⟨340854, by rfl⟩ : syracuseStep 908945 = 681709) B681709
theorem B1990307 : Blo 603293 1990307 := bstep (se 1 (by rfl) ⟨1492730, by rfl⟩ : syracuseStep 1990307 = 2985461) B2985461
theorem B908963 : Blo 603293 908963 := bstep (se 1 (by rfl) ⟨681722, by rfl⟩ : syracuseStep 908963 = 1363445) B1363445
theorem B679603 : Blo 603293 679603 := bstep (se 1 (by rfl) ⟨509702, by rfl⟩ : syracuseStep 679603 = 1019405) B1019405
theorem B908993 : Blo 603293 908993 := bstep (se 2 (by rfl) ⟨340872, by rfl⟩ : syracuseStep 908993 = 681745) B681745
theorem B1728209 : Blo 603293 1728209 := bstep (se 2 (by rfl) ⟨648078, by rfl⟩ : syracuseStep 1728209 = 1296157) B1296157
theorem B909011 : Blo 603293 909011 := bstep (se 1 (by rfl) ⟨681758, by rfl⟩ : syracuseStep 909011 = 1363517) B1363517
theorem B1531619 : Blo 603293 1531619 := bstep (se 1 (by rfl) ⟨1148714, by rfl⟩ : syracuseStep 1531619 = 2297429) B2297429
theorem B909041 : Blo 603293 909041 := bstep (se 2 (by rfl) ⟨340890, by rfl⟩ : syracuseStep 909041 = 681781) B681781
theorem B2186993 : Blo 603293 2186993 := bstep (se 2 (by rfl) ⟨820122, by rfl⟩ : syracuseStep 2186993 = 1640245) B1640245
theorem B909059 : Blo 603293 909059 := bstep (se 1 (by rfl) ⟨681794, by rfl⟩ : syracuseStep 909059 = 1363589) B1363589
theorem B909089 : Blo 603293 909089 := bstep (se 2 (by rfl) ⟨340908, by rfl⟩ : syracuseStep 909089 = 681817) B681817
theorem B909107 : Blo 603293 909107 := bstep (se 1 (by rfl) ⟨681830, by rfl⟩ : syracuseStep 909107 = 1363661) B1363661
theorem B679747 : Blo 603293 679747 := bstep (se 1 (by rfl) ⟨509810, by rfl⟩ : syracuseStep 679747 = 1019621) B1019621
theorem B1728323 : Blo 603293 1728323 := bstep (se 1 (by rfl) ⟨1296242, by rfl⟩ : syracuseStep 1728323 = 2592485) B2592485
theorem B909137 : Blo 603293 909137 := bstep (se 2 (by rfl) ⟨340926, by rfl⟩ : syracuseStep 909137 = 681853) B681853
theorem B909155 : Blo 603293 909155 := bstep (se 1 (by rfl) ⟨681866, by rfl⟩ : syracuseStep 909155 = 1363733) B1363733
theorem B3071843 : Blo 603293 3071843 := bstep (se 1 (by rfl) ⟨2303882, by rfl⟩ : syracuseStep 3071843 = 4607765) B4607765
theorem B909185 : Blo 603293 909185 := bstep (se 2 (by rfl) ⟨340944, by rfl⟩ : syracuseStep 909185 = 681889) B681889
theorem B909203 : Blo 603293 909203 := bstep (se 1 (by rfl) ⟨681902, by rfl⟩ : syracuseStep 909203 = 1363805) B1363805
theorem B1531811 : Blo 603293 1531811 := bstep (se 1 (by rfl) ⟨1148858, by rfl⟩ : syracuseStep 1531811 = 2297717) B2297717
theorem B647075 : Blo 603293 647075 := bstep (se 1 (by rfl) ⟨485306, by rfl⟩ : syracuseStep 647075 = 970613) B970613
theorem B909233 : Blo 603293 909233 := bstep (se 2 (by rfl) ⟨340962, by rfl⟩ : syracuseStep 909233 = 681925) B681925
theorem B909251 : Blo 603293 909251 := bstep (se 1 (by rfl) ⟨681938, by rfl⟩ : syracuseStep 909251 = 1363877) B1363877
theorem B679891 : Blo 603293 679891 := bstep (se 1 (by rfl) ⟨509918, by rfl⟩ : syracuseStep 679891 = 1019837) B1019837
theorem B909281 : Blo 603293 909281 := bstep (se 2 (by rfl) ⟨340980, by rfl⟩ : syracuseStep 909281 = 681961) B681961
theorem B909299 : Blo 603293 909299 := bstep (se 1 (by rfl) ⟨681974, by rfl⟩ : syracuseStep 909299 = 1363949) B1363949
theorem B909329 : Blo 603293 909329 := bstep (se 2 (by rfl) ⟨340998, by rfl⟩ : syracuseStep 909329 = 681997) B681997
theorem B909347 : Blo 603293 909347 := bstep (se 1 (by rfl) ⟨682010, by rfl⟩ : syracuseStep 909347 = 1364021) B1364021
theorem B909377 : Blo 603293 909377 := bstep (se 2 (by rfl) ⟨341016, by rfl⟩ : syracuseStep 909377 = 682033) B682033
theorem B909395 : Blo 603293 909395 := bstep (se 1 (by rfl) ⟨682046, by rfl⟩ : syracuseStep 909395 = 1364093) B1364093
theorem B680035 : Blo 603293 680035 := bstep (se 1 (by rfl) ⟨510026, by rfl⟩ : syracuseStep 680035 = 1020053) B1020053
theorem B909425 : Blo 603293 909425 := bstep (se 2 (by rfl) ⟨341034, by rfl⟩ : syracuseStep 909425 = 682069) B682069
theorem B909443 : Blo 603293 909443 := bstep (se 1 (by rfl) ⟨682082, by rfl⟩ : syracuseStep 909443 = 1364165) B1364165
theorem B909473 : Blo 603293 909473 := bstep (se 2 (by rfl) ⟨341052, by rfl⟩ : syracuseStep 909473 = 682105) B682105
theorem B909491 : Blo 603293 909491 := bstep (se 1 (by rfl) ⟨682118, by rfl⟩ : syracuseStep 909491 = 1364237) B1364237
theorem B909521 : Blo 603293 909521 := bstep (se 2 (by rfl) ⟨341070, by rfl⟩ : syracuseStep 909521 = 682141) B682141
theorem B909539 : Blo 603293 909539 := bstep (se 1 (by rfl) ⟨682154, by rfl⟩ : syracuseStep 909539 = 1364309) B1364309
theorem B680179 : Blo 603293 680179 := bstep (se 1 (by rfl) ⟨510134, by rfl⟩ : syracuseStep 680179 = 1020269) B1020269
theorem B909569 : Blo 603293 909569 := bstep (se 2 (by rfl) ⟨341088, by rfl⟩ : syracuseStep 909569 = 682177) B682177
theorem B909587 : Blo 603293 909587 := bstep (se 1 (by rfl) ⟨682190, by rfl⟩ : syracuseStep 909587 = 1364381) B1364381
theorem B909617 : Blo 603293 909617 := bstep (se 2 (by rfl) ⟨341106, by rfl⟩ : syracuseStep 909617 = 682213) B682213
theorem B909635 : Blo 603293 909635 := bstep (se 1 (by rfl) ⟨682226, by rfl⟩ : syracuseStep 909635 = 1364453) B1364453
theorem B909665 : Blo 603293 909665 := bstep (se 2 (by rfl) ⟨341124, by rfl⟩ : syracuseStep 909665 = 682249) B682249
theorem B7758179 : Blo 603293 7758179 := bstep (se 1 (by rfl) ⟨5818634, by rfl⟩ : syracuseStep 7758179 = 11637269) B11637269
theorem B5169521 : Blo 603293 5169521 := bstep (se 2 (by rfl) ⟨1938570, by rfl⟩ : syracuseStep 5169521 = 3877141) B3877141
theorem B909683 : Blo 603293 909683 := bstep (se 1 (by rfl) ⟨682262, by rfl⟩ : syracuseStep 909683 = 1364525) B1364525
theorem B680323 : Blo 603293 680323 := bstep (se 1 (by rfl) ⟨510242, by rfl⟩ : syracuseStep 680323 = 1020485) B1020485
theorem B909713 : Blo 603293 909713 := bstep (se 2 (by rfl) ⟨341142, by rfl⟩ : syracuseStep 909713 = 682285) B682285
theorem B909731 : Blo 603293 909731 := bstep (se 1 (by rfl) ⟨682298, by rfl⟩ : syracuseStep 909731 = 1364597) B1364597
theorem B909761 : Blo 603293 909761 := bstep (se 2 (by rfl) ⟨341160, by rfl⟩ : syracuseStep 909761 = 682321) B682321
theorem B909779 : Blo 603293 909779 := bstep (se 1 (by rfl) ⟨682334, by rfl⟩ : syracuseStep 909779 = 1364669) B1364669
theorem B909809 : Blo 603293 909809 := bstep (se 2 (by rfl) ⟨341178, by rfl⟩ : syracuseStep 909809 = 682357) B682357
theorem B909827 : Blo 603293 909827 := bstep (se 1 (by rfl) ⟨682370, by rfl⟩ : syracuseStep 909827 = 1364741) B1364741
theorem B680467 : Blo 603293 680467 := bstep (se 1 (by rfl) ⟨510350, by rfl⟩ : syracuseStep 680467 = 1020701) B1020701
theorem B909857 : Blo 603293 909857 := bstep (se 2 (by rfl) ⟨341196, by rfl⟩ : syracuseStep 909857 = 682393) B682393
theorem B909875 : Blo 603293 909875 := bstep (se 1 (by rfl) ⟨682406, by rfl⟩ : syracuseStep 909875 = 1364813) B1364813
theorem B778819 : Blo 603293 778819 := bstep (se 1 (by rfl) ⟨584114, by rfl⟩ : syracuseStep 778819 = 1168229) B1168229
theorem B909905 : Blo 603293 909905 := bstep (se 2 (by rfl) ⟨341214, by rfl⟩ : syracuseStep 909905 = 682429) B682429
theorem B909923 : Blo 603293 909923 := bstep (se 1 (by rfl) ⟨682442, by rfl⟩ : syracuseStep 909923 = 1364885) B1364885
theorem B2581105 : Blo 603293 2581105 := bstep (se 2 (by rfl) ⟨967914, by rfl⟩ : syracuseStep 2581105 = 1935829) B1935829
theorem B909953 : Blo 603293 909953 := bstep (se 2 (by rfl) ⟨341232, by rfl⟩ : syracuseStep 909953 = 682465) B682465
theorem B3072653 : Blo 603293 3072653 := bstep (se 3 (by rfl) ⟨576122, by rfl⟩ : syracuseStep 3072653 = 1152245) B1152245
theorem B2187917 : Blo 603293 2187917 := bstep (se 3 (by rfl) ⟨410234, by rfl⟩ : syracuseStep 2187917 = 820469) B820469
theorem B909971 : Blo 603293 909971 := bstep (se 1 (by rfl) ⟨682478, by rfl⟩ : syracuseStep 909971 = 1364957) B1364957
theorem B680611 : Blo 603293 680611 := bstep (se 1 (by rfl) ⟨510458, by rfl⟩ : syracuseStep 680611 = 1020917) B1020917
theorem B910001 : Blo 603293 910001 := bstep (se 2 (by rfl) ⟨341250, by rfl⟩ : syracuseStep 910001 = 682501) B682501
theorem B910019 : Blo 603293 910019 := bstep (se 1 (by rfl) ⟨682514, by rfl⟩ : syracuseStep 910019 = 1365029) B1365029
theorem B910049 : Blo 603293 910049 := bstep (se 2 (by rfl) ⟨341268, by rfl⟩ : syracuseStep 910049 = 682537) B682537
theorem B910067 : Blo 603293 910067 := bstep (se 1 (by rfl) ⟨682550, by rfl⟩ : syracuseStep 910067 = 1365101) B1365101
theorem B4907789 : Blo 603293 4907789 := bstep (se 3 (by rfl) ⟨920210, by rfl⟩ : syracuseStep 4907789 = 1840421) B1840421
theorem B910097 : Blo 603293 910097 := bstep (se 2 (by rfl) ⟨341286, by rfl⟩ : syracuseStep 910097 = 682573) B682573
theorem B910115 : Blo 603293 910115 := bstep (se 1 (by rfl) ⟨682586, by rfl⟩ : syracuseStep 910115 = 1365173) B1365173
theorem B1729325 : Blo 603293 1729325 := bstep (se 3 (by rfl) ⟨324248, by rfl⟩ : syracuseStep 1729325 = 648497) B648497
theorem B680755 : Blo 603293 680755 := bstep (se 1 (by rfl) ⟨510566, by rfl⟩ : syracuseStep 680755 = 1021133) B1021133
theorem B910145 : Blo 603293 910145 := bstep (se 2 (by rfl) ⟨341304, by rfl⟩ : syracuseStep 910145 = 682609) B682609
theorem B1532753 : Blo 603293 1532753 := bstep (se 2 (by rfl) ⟨574782, by rfl⟩ : syracuseStep 1532753 = 1149565) B1149565
theorem B910163 : Blo 603293 910163 := bstep (se 1 (by rfl) ⟨682622, by rfl⟩ : syracuseStep 910163 = 1365245) B1365245
theorem B1631075 : Blo 603293 1631075 := bstep (se 1 (by rfl) ⟨1223306, by rfl⟩ : syracuseStep 1631075 = 2446613) B2446613
theorem B4350833 : Blo 603293 4350833 := bstep (se 2 (by rfl) ⟨1631562, by rfl⟩ : syracuseStep 4350833 = 3263125) B3263125
theorem B910193 : Blo 603293 910193 := bstep (se 2 (by rfl) ⟨341322, by rfl⟩ : syracuseStep 910193 = 682645) B682645
theorem B1532803 : Blo 603293 1532803 := bstep (se 1 (by rfl) ⟨1149602, by rfl⟩ : syracuseStep 1532803 = 2299205) B2299205
theorem B910211 : Blo 603293 910211 := bstep (se 1 (by rfl) ⟨682658, by rfl⟩ : syracuseStep 910211 = 1365317) B1365317
theorem B910241 : Blo 603293 910241 := bstep (se 2 (by rfl) ⟨341340, by rfl⟩ : syracuseStep 910241 = 682681) B682681
theorem B910259 : Blo 603293 910259 := bstep (se 1 (by rfl) ⟨682694, by rfl⟩ : syracuseStep 910259 = 1365389) B1365389
theorem B680899 : Blo 603293 680899 := bstep (se 1 (by rfl) ⟨510674, by rfl⟩ : syracuseStep 680899 = 1021349) B1021349
theorem B910289 : Blo 603293 910289 := bstep (se 2 (by rfl) ⟨341358, by rfl⟩ : syracuseStep 910289 = 682717) B682717
theorem B910307 : Blo 603293 910307 := bstep (se 1 (by rfl) ⟨682730, by rfl⟩ : syracuseStep 910307 = 1365461) B1365461
theorem B910337 : Blo 603293 910337 := bstep (se 2 (by rfl) ⟨341376, by rfl⟩ : syracuseStep 910337 = 682753) B682753
theorem B1532945 : Blo 603293 1532945 := bstep (se 2 (by rfl) ⟨574854, by rfl⟩ : syracuseStep 1532945 = 1149709) B1149709
theorem B910355 : Blo 603293 910355 := bstep (se 1 (by rfl) ⟨682766, by rfl⟩ : syracuseStep 910355 = 1365533) B1365533
theorem B910385 : Blo 603293 910385 := bstep (se 2 (by rfl) ⟨341394, by rfl⟩ : syracuseStep 910385 = 682789) B682789
theorem B910403 : Blo 603293 910403 := bstep (se 1 (by rfl) ⟨682802, by rfl⟩ : syracuseStep 910403 = 1365605) B1365605
theorem B681043 : Blo 603293 681043 := bstep (se 1 (by rfl) ⟨510782, by rfl⟩ : syracuseStep 681043 = 1021565) B1021565
theorem B910433 : Blo 603293 910433 := bstep (se 2 (by rfl) ⟨341412, by rfl⟩ : syracuseStep 910433 = 682825) B682825
theorem B910451 : Blo 603293 910451 := bstep (se 1 (by rfl) ⟨682838, by rfl⟩ : syracuseStep 910451 = 1365677) B1365677
theorem B910481 : Blo 603293 910481 := bstep (se 2 (by rfl) ⟨341430, by rfl⟩ : syracuseStep 910481 = 682861) B682861
theorem B910499 : Blo 603293 910499 := bstep (se 1 (by rfl) ⟨682874, by rfl⟩ : syracuseStep 910499 = 1365749) B1365749
theorem B910529 : Blo 603293 910529 := bstep (se 2 (by rfl) ⟨341448, by rfl⟩ : syracuseStep 910529 = 682897) B682897
theorem B910547 : Blo 603293 910547 := bstep (se 1 (by rfl) ⟨682910, by rfl⟩ : syracuseStep 910547 = 1365821) B1365821
theorem B681187 : Blo 603293 681187 := bstep (se 1 (by rfl) ⟨510890, by rfl⟩ : syracuseStep 681187 = 1021781) B1021781
theorem B910577 : Blo 603293 910577 := bstep (se 2 (by rfl) ⟨341466, by rfl⟩ : syracuseStep 910577 = 682933) B682933
theorem B910595 : Blo 603293 910595 := bstep (se 1 (by rfl) ⟨682946, by rfl⟩ : syracuseStep 910595 = 1365893) B1365893
theorem B910625 : Blo 603293 910625 := bstep (se 2 (by rfl) ⟨341484, by rfl⟩ : syracuseStep 910625 = 682969) B682969
theorem B910643 : Blo 603293 910643 := bstep (se 1 (by rfl) ⟨682982, by rfl⟩ : syracuseStep 910643 = 1365965) B1365965
theorem B910673 : Blo 603293 910673 := bstep (se 2 (by rfl) ⟨341502, by rfl⟩ : syracuseStep 910673 = 683005) B683005
theorem B910691 : Blo 603293 910691 := bstep (se 1 (by rfl) ⟨683018, by rfl⟩ : syracuseStep 910691 = 1366037) B1366037
theorem B681331 : Blo 603293 681331 := bstep (se 1 (by rfl) ⟨510998, by rfl⟩ : syracuseStep 681331 = 1021997) B1021997
theorem B910721 : Blo 603293 910721 := bstep (se 2 (by rfl) ⟨341520, by rfl⟩ : syracuseStep 910721 = 683041) B683041
theorem B910739 : Blo 603293 910739 := bstep (se 1 (by rfl) ⟨683054, by rfl⟩ : syracuseStep 910739 = 1366109) B1366109
theorem B910769 : Blo 603293 910769 := bstep (se 2 (by rfl) ⟨341538, by rfl⟩ : syracuseStep 910769 = 683077) B683077
theorem B910787 : Blo 603293 910787 := bstep (se 1 (by rfl) ⟨683090, by rfl⟩ : syracuseStep 910787 = 1366181) B1366181
theorem B910817 : Blo 603293 910817 := bstep (se 2 (by rfl) ⟨341556, by rfl⟩ : syracuseStep 910817 = 683113) B683113
theorem B910835 : Blo 603293 910835 := bstep (se 1 (by rfl) ⟨683126, by rfl⟩ : syracuseStep 910835 = 1366253) B1366253
theorem B681475 : Blo 603293 681475 := bstep (se 1 (by rfl) ⟨511106, by rfl⟩ : syracuseStep 681475 = 1022213) B1022213
theorem B910865 : Blo 603293 910865 := bstep (se 2 (by rfl) ⟨341574, by rfl⟩ : syracuseStep 910865 = 683149) B683149
theorem B910883 : Blo 603293 910883 := bstep (se 1 (by rfl) ⟨683162, by rfl⟩ : syracuseStep 910883 = 1366325) B1366325
theorem B910913 : Blo 603293 910913 := bstep (se 2 (by rfl) ⟨341592, by rfl⟩ : syracuseStep 910913 = 683185) B683185
theorem B1631821 : Blo 603293 1631821 := bstep (se 3 (by rfl) ⟨305966, by rfl⟩ : syracuseStep 1631821 = 611933) B611933
theorem B910931 : Blo 603293 910931 := bstep (se 1 (by rfl) ⟨683198, by rfl⟩ : syracuseStep 910931 = 1366397) B1366397
theorem B681619 : Blo 603293 681619 := bstep (se 1 (by rfl) ⟨511214, by rfl⟩ : syracuseStep 681619 = 1022429) B1022429
theorem B5531333 : Blo 603293 5531333 := bstep (se 4 (by rfl) ⟨518562, by rfl⟩ : syracuseStep 5531333 = 1037125) B1037125
theorem B3106531 : Blo 603293 3106531 := bstep (se 1 (by rfl) ⟨2329898, by rfl⟩ : syracuseStep 3106531 = 4659797) B4659797
theorem B6612749 : Blo 603293 6612749 := bstep (se 3 (by rfl) ⟨1239890, by rfl⟩ : syracuseStep 6612749 = 2479781) B2479781
theorem B681763 : Blo 603293 681763 := bstep (se 1 (by rfl) ⟨511322, by rfl⟩ : syracuseStep 681763 = 1022645) B1022645
theorem B681907 : Blo 603293 681907 := bstep (se 1 (by rfl) ⟨511430, by rfl⟩ : syracuseStep 681907 = 1022861) B1022861
theorem B1533937 : Blo 603293 1533937 := bstep (se 2 (by rfl) ⟨575226, by rfl⟩ : syracuseStep 1533937 = 1150453) B1150453
theorem B682051 : Blo 603293 682051 := bstep (se 1 (by rfl) ⟨511538, by rfl⟩ : syracuseStep 682051 = 1023077) B1023077
theorem B6908003 : Blo 603293 6908003 := bstep (se 1 (by rfl) ⟨5181002, by rfl⟩ : syracuseStep 6908003 = 10362005) B10362005
theorem B682195 : Blo 603293 682195 := bstep (se 1 (by rfl) ⟨511646, by rfl⟩ : syracuseStep 682195 = 1023293) B1023293
theorem B1534211 : Blo 603293 1534211 := bstep (se 1 (by rfl) ⟨1150658, by rfl⟩ : syracuseStep 1534211 = 2301317) B2301317
theorem B682339 : Blo 603293 682339 := bstep (se 1 (by rfl) ⟨511754, by rfl⟩ : syracuseStep 682339 = 1023509) B1023509
theorem B1534403 : Blo 603293 1534403 := bstep (se 1 (by rfl) ⟨1150802, by rfl⟩ : syracuseStep 1534403 = 2301605) B2301605
theorem B682483 : Blo 603293 682483 := bstep (se 1 (by rfl) ⟨511862, by rfl⟩ : syracuseStep 682483 = 1023725) B1023725
theorem B2583053 : Blo 603293 2583053 := bstep (se 3 (by rfl) ⟨484322, by rfl⟩ : syracuseStep 2583053 = 968645) B968645
theorem B682627 : Blo 603293 682627 := bstep (se 1 (by rfl) ⟨511970, by rfl⟩ : syracuseStep 682627 = 1023941) B1023941
theorem B682771 : Blo 603293 682771 := bstep (se 1 (by rfl) ⟨512078, by rfl⟩ : syracuseStep 682771 = 1024157) B1024157
theorem B682915 : Blo 603293 682915 := bstep (se 1 (by rfl) ⟨512186, by rfl⟩ : syracuseStep 682915 = 1024373) B1024373
theorem B683059 : Blo 603293 683059 := bstep (se 1 (by rfl) ⟨512294, by rfl⟩ : syracuseStep 683059 = 1024589) B1024589
theorem B1633421 : Blo 603293 1633421 := bstep (se 3 (by rfl) ⟨306266, by rfl⟩ : syracuseStep 1633421 = 612533) B612533
theorem B683203 : Blo 603293 683203 := bstep (se 1 (by rfl) ⟨512402, by rfl⟩ : syracuseStep 683203 = 1024805) B1024805
theorem B1961165 : Blo 603293 1961165 := bstep (se 3 (by rfl) ⟨367718, by rfl⟩ : syracuseStep 1961165 = 735437) B735437
theorem B1535345 : Blo 603293 1535345 := bstep (se 2 (by rfl) ⟨575754, by rfl⟩ : syracuseStep 1535345 = 1151509) B1151509
theorem B1535395 : Blo 603293 1535395 := bstep (se 1 (by rfl) ⟨1151546, by rfl⟩ : syracuseStep 1535395 = 2303093) B2303093
theorem B1535537 : Blo 603293 1535537 := bstep (se 2 (by rfl) ⟨575826, by rfl⟩ : syracuseStep 1535537 = 1151653) B1151653
theorem B2355569 : Blo 603293 2355569 := bstep (se 2 (by rfl) ⟨883338, by rfl⟩ : syracuseStep 2355569 = 1766677) B1766677
theorem B1536529 : Blo 603293 1536529 := bstep (se 2 (by rfl) ⟨576198, by rfl⟩ : syracuseStep 1536529 = 1152397) B1152397
theorem B1536803 : Blo 603293 1536803 := bstep (se 1 (by rfl) ⟨1152602, by rfl⟩ : syracuseStep 1536803 = 2305205) B2305205
theorem B4911941 : Blo 603293 4911941 := bstep (se 4 (by rfl) ⟨460494, by rfl⟩ : syracuseStep 4911941 = 920989) B920989
theorem B1536995 : Blo 603293 1536995 := bstep (se 1 (by rfl) ⟨1152746, by rfl⟩ : syracuseStep 1536995 = 2305493) B2305493
theorem B1307747 : Blo 603293 1307747 := bstep (se 1 (by rfl) ⟨980810, by rfl⟩ : syracuseStep 1307747 = 1961621) B1961621
theorem B3437873 : Blo 603293 3437873 := bstep (se 2 (by rfl) ⟨1289202, by rfl⟩ : syracuseStep 3437873 = 2578405) B2578405
theorem B5895665 : Blo 603293 5895665 := bstep (se 2 (by rfl) ⟨2210874, by rfl⟩ : syracuseStep 5895665 = 4421749) B4421749
theorem B1963565 : Blo 603293 1963565 := bstep (se 3 (by rfl) ⟨368168, by rfl⟩ : syracuseStep 1963565 = 736337) B736337
theorem B816689 : Blo 603293 816689 := bstep (se 2 (by rfl) ⟨306258, by rfl⟩ : syracuseStep 816689 = 612517) B612517
theorem B2618993 : Blo 603293 2618993 := bstep (se 2 (by rfl) ⟨982122, by rfl⟩ : syracuseStep 2618993 = 1964245) B1964245
theorem B2291597 : Blo 603293 2291597 := bstep (se 3 (by rfl) ⟨429674, by rfl⟩ : syracuseStep 2291597 = 859349) B859349
theorem B817057 : Blo 603293 817057 := bstep (se 2 (by rfl) ⟨306396, by rfl⟩ : syracuseStep 817057 = 612793) B612793
theorem B817457 : Blo 603293 817457 := bstep (se 2 (by rfl) ⟨306546, by rfl⟩ : syracuseStep 817457 = 613093) B613093
theorem B817489 : Blo 603293 817489 := bstep (se 2 (by rfl) ⟨306558, by rfl⟩ : syracuseStep 817489 = 613117) B613117
theorem B817571 : Blo 603293 817571 := bstep (se 1 (by rfl) ⟨613178, by rfl⟩ : syracuseStep 817571 = 1226357) B1226357
theorem B2587085 : Blo 603293 2587085 := bstep (se 3 (by rfl) ⟨485078, by rfl⟩ : syracuseStep 2587085 = 970157) B970157
theorem B817619 : Blo 603293 817619 := bstep (se 1 (by rfl) ⟨613214, by rfl⟩ : syracuseStep 817619 = 1226429) B1226429
theorem B1145411 : Blo 603293 1145411 := bstep (se 1 (by rfl) ⟨859058, by rfl⟩ : syracuseStep 1145411 = 1718117) B1718117
theorem B9337457 : Blo 603293 9337457 := bstep (se 2 (by rfl) ⟨3501546, by rfl⟩ : syracuseStep 9337457 = 7003093) B7003093
theorem B2292401 : Blo 603293 2292401 := bstep (se 2 (by rfl) ⟨859650, by rfl⟩ : syracuseStep 2292401 = 1719301) B1719301
theorem B3275491 : Blo 603293 3275491 := bstep (se 1 (by rfl) ⟨2456618, by rfl⟩ : syracuseStep 3275491 = 4913237) B4913237
theorem B3439331 : Blo 603293 3439331 := bstep (se 1 (by rfl) ⟨2579498, by rfl⟩ : syracuseStep 3439331 = 5158997) B5158997
theorem B2587427 : Blo 603293 2587427 := bstep (se 1 (by rfl) ⟨1940570, by rfl⟩ : syracuseStep 2587427 = 3881141) B3881141
theorem B4586381 : Blo 603293 4586381 := bstep (se 3 (by rfl) ⟨859946, by rfl⟩ : syracuseStep 4586381 = 1719893) B1719893
theorem B11041933 : Blo 603293 11041933 := bstep (se 3 (by rfl) ⟨2070362, by rfl⟩ : syracuseStep 11041933 = 4140725) B4140725
theorem B2587889 : Blo 603293 2587889 := bstep (se 2 (by rfl) ⟨970458, by rfl⟩ : syracuseStep 2587889 = 1940917) B1940917
theorem B1047809 : Blo 603293 1047809 := bstep (se 2 (by rfl) ⟨392928, by rfl⟩ : syracuseStep 1047809 = 785857) B785857
theorem B2293069 : Blo 603293 2293069 := bstep (se 3 (by rfl) ⟨429950, by rfl⟩ : syracuseStep 2293069 = 859901) B859901
theorem B1146307 : Blo 603293 1146307 := bstep (se 1 (by rfl) ⟨859730, by rfl⟩ : syracuseStep 1146307 = 1719461) B1719461
theorem B1146467 : Blo 603293 1146467 := bstep (se 1 (by rfl) ⟨859850, by rfl⟩ : syracuseStep 1146467 = 1719701) B1719701
theorem B1834609 : Blo 603293 1834609 := bstep (se 2 (by rfl) ⟨687978, by rfl⟩ : syracuseStep 1834609 = 1375957) B1375957
theorem B3440333 : Blo 603293 3440333 := bstep (se 3 (by rfl) ⟨645062, by rfl⟩ : syracuseStep 3440333 = 1290125) B1290125
theorem B3276875 : Blo 603293 3276875 := bstep (se 1 (by rfl) ⟨2457656, by rfl⟩ : syracuseStep 3276875 = 4915313) B4915313
theorem B2752643 : Blo 603293 2752643 := bstep (se 1 (by rfl) ⟨2064482, by rfl⟩ : syracuseStep 2752643 = 4128965) B4128965
theorem B1147097 : Blo 603293 1147097 := bstep (se 2 (by rfl) ⟨430161, by rfl⟩ : syracuseStep 1147097 = 860323) B860323
theorem B2753041 : Blo 603293 2753041 := bstep (se 2 (by rfl) ⟨1032390, by rfl⟩ : syracuseStep 2753041 = 2064781) B2064781
theorem B2458291 : Blo 603293 2458291 := bstep (se 1 (by rfl) ⟨1843718, by rfl⟩ : syracuseStep 2458291 = 3687437) B3687437
theorem B3441473 : Blo 603293 3441473 := bstep (se 2 (by rfl) ⟨1290552, by rfl⟩ : syracuseStep 3441473 = 2581105) B2581105
theorem B2589529 : Blo 603293 2589529 := bstep (se 2 (by rfl) ⟨971073, by rfl⟩ : syracuseStep 2589529 = 1942147) B1942147
theorem B1147841 : Blo 603293 1147841 := bstep (se 2 (by rfl) ⟨430440, by rfl⟩ : syracuseStep 1147841 = 860881) B860881
theorem B2294801 : Blo 603293 2294801 := bstep (se 2 (by rfl) ⟨860550, by rfl⟩ : syracuseStep 2294801 = 1721101) B1721101
theorem B1148107 : Blo 603293 1148107 := bstep (se 1 (by rfl) ⟨861080, by rfl⟩ : syracuseStep 1148107 = 1722161) B1722161
theorem B918745 : Blo 603293 918745 := bstep (se 2 (by rfl) ⟨344529, by rfl⟩ : syracuseStep 918745 = 689059) B689059
theorem B787979 : Blo 603293 787979 := bstep (se 1 (by rfl) ⟨590984, by rfl⟩ : syracuseStep 787979 = 1181969) B1181969
theorem B1148555 : Blo 603293 1148555 := bstep (se 1 (by rfl) ⟨861416, by rfl⟩ : syracuseStep 1148555 = 1722833) B1722833
theorem B2295499 : Blo 603293 2295499 := bstep (se 1 (by rfl) ⟨1721624, by rfl⟩ : syracuseStep 2295499 = 3443249) B3443249
theorem B2590487 : Blo 603293 2590487 := bstep (se 1 (by rfl) ⟨1942865, by rfl⟩ : syracuseStep 2590487 = 3885731) B3885731
theorem B1148737 : Blo 603293 1148737 := bstep (se 2 (by rfl) ⟨430776, by rfl⟩ : syracuseStep 1148737 = 861553) B861553
theorem B2295773 : Blo 603293 2295773 := bstep (se 3 (by rfl) ⟨430457, by rfl⟩ : syracuseStep 2295773 = 860915) B860915
theorem B1149079 : Blo 603293 1149079 := bstep (se 1 (by rfl) ⟨861809, by rfl⟩ : syracuseStep 1149079 = 1723619) B1723619
theorem B2459927 : Blo 603293 2459927 := bstep (se 1 (by rfl) ⟨1844945, by rfl⟩ : syracuseStep 2459927 = 3689891) B3689891
theorem B1149299 : Blo 603293 1149299 := bstep (se 1 (by rfl) ⟨861974, by rfl⟩ : syracuseStep 1149299 = 1723949) B1723949
theorem B5179909 : Blo 603293 5179909 := bstep (se 4 (by rfl) ⟨485616, by rfl⟩ : syracuseStep 5179909 = 971233) B971233
theorem B1018379 : Blo 603293 1018379 := bstep (se 1 (by rfl) ⟨763784, by rfl⟩ : syracuseStep 1018379 = 1527569) B1527569
theorem B1149527 : Blo 603293 1149527 := bstep (se 1 (by rfl) ⟨862145, by rfl⟩ : syracuseStep 1149527 = 1724291) B1724291
theorem B5835395 : Blo 603293 5835395 := bstep (se 1 (by rfl) ⟨4376546, by rfl⟩ : syracuseStep 5835395 = 8753093) B8753093
theorem B1018507 : Blo 603293 1018507 := bstep (se 1 (by rfl) ⟨763880, by rfl⟩ : syracuseStep 1018507 = 1527761) B1527761
theorem B2296471 : Blo 603293 2296471 := bstep (se 1 (by rfl) ⟨1722353, by rfl⟩ : syracuseStep 2296471 = 3444707) B3444707
theorem B5900951 : Blo 603293 5900951 := bstep (se 1 (by rfl) ⟨4425713, by rfl⟩ : syracuseStep 5900951 = 8851427) B8851427
theorem B1018649 : Blo 603293 1018649 := bstep (se 2 (by rfl) ⟨381993, by rfl⟩ : syracuseStep 1018649 = 763987) B763987
theorem B1149785 : Blo 603293 1149785 := bstep (se 2 (by rfl) ⟨431169, by rfl⟩ : syracuseStep 1149785 = 862339) B862339
theorem B1018777 : Blo 603293 1018777 := bstep (se 2 (by rfl) ⟨382041, by rfl⟩ : syracuseStep 1018777 = 764083) B764083
theorem B4131971 : Blo 603293 4131971 := bstep (se 1 (by rfl) ⟨3098978, by rfl⟩ : syracuseStep 4131971 = 6197957) B6197957
theorem B1182937 : Blo 603293 1182937 := bstep (se 2 (by rfl) ⟨443601, by rfl⟩ : syracuseStep 1182937 = 887203) B887203
theorem B1150195 : Blo 603293 1150195 := bstep (se 1 (by rfl) ⟨862646, by rfl⟩ : syracuseStep 1150195 = 1725293) B1725293
theorem B920843 : Blo 603293 920843 := bstep (se 1 (by rfl) ⟨690632, by rfl⟩ : syracuseStep 920843 = 1381265) B1381265
theorem B2297261 : Blo 603293 2297261 := bstep (se 3 (by rfl) ⟨430736, by rfl⟩ : syracuseStep 2297261 = 861473) B861473
theorem B1019351 : Blo 603293 1019351 := bstep (se 1 (by rfl) ⟨764513, by rfl⟩ : syracuseStep 1019351 = 1529027) B1529027
theorem B1019479 : Blo 603293 1019479 := bstep (se 1 (by rfl) ⟨764609, by rfl⟩ : syracuseStep 1019479 = 1529219) B1529219
theorem B1150681 : Blo 603293 1150681 := bstep (se 2 (by rfl) ⟨431505, by rfl⟩ : syracuseStep 1150681 = 863011) B863011
theorem B2330333 : Blo 603293 2330333 := bstep (se 3 (by rfl) ⟨436937, by rfl⟩ : syracuseStep 2330333 = 873875) B873875
theorem B2592587 : Blo 603293 2592587 := bstep (se 1 (by rfl) ⟨1944440, by rfl⟩ : syracuseStep 2592587 = 3888881) B3888881
theorem B8720459 : Blo 603293 8720459 := bstep (se 1 (by rfl) ⟨6540344, by rfl⟩ : syracuseStep 8720459 = 13080689) B13080689
theorem B692311 : Blo 603293 692311 := bstep (se 1 (by rfl) ⟨519233, by rfl⟩ : syracuseStep 692311 = 1038467) B1038467
theorem B1020107 : Blo 603293 1020107 := bstep (se 1 (by rfl) ⟨765080, by rfl⟩ : syracuseStep 1020107 = 1530161) B1530161
theorem B921817 : Blo 603293 921817 := bstep (se 2 (by rfl) ⟨345681, by rfl⟩ : syracuseStep 921817 = 691363) B691363
theorem B1151243 : Blo 603293 1151243 := bstep (se 1 (by rfl) ⟨863432, by rfl⟩ : syracuseStep 1151243 = 1726865) B1726865
theorem B2756909 : Blo 603293 2756909 := bstep (se 3 (by rfl) ⟨516920, by rfl⟩ : syracuseStep 2756909 = 1033841) B1033841
theorem B6983981 : Blo 603293 6983981 := bstep (se 3 (by rfl) ⟨1309496, by rfl⟩ : syracuseStep 6983981 = 2618993) B2618993
theorem B1020235 : Blo 603293 1020235 := bstep (se 1 (by rfl) ⟨765176, by rfl⟩ : syracuseStep 1020235 = 1530353) B1530353
theorem B1151425 : Blo 603293 1151425 := bstep (se 2 (by rfl) ⟨431784, by rfl⟩ : syracuseStep 1151425 = 863569) B863569
theorem B1020377 : Blo 603293 1020377 := bstep (se 2 (by rfl) ⟨382641, by rfl⟩ : syracuseStep 1020377 = 765283) B765283
theorem B14750221 : Blo 603293 14750221 := bstep (se 3 (by rfl) ⟨2765666, by rfl⟩ : syracuseStep 14750221 = 5531333) B5531333
theorem B1020505 : Blo 603293 1020505 := bstep (se 2 (by rfl) ⟨382689, by rfl⟩ : syracuseStep 1020505 = 765379) B765379
theorem B21041795 : Blo 603293 21041795 := bstep (se 1 (by rfl) ⟨15781346, by rfl⟩ : syracuseStep 21041795 = 31562693) B31562693
theorem B9966341 : Blo 603293 9966341 := bstep (se 4 (by rfl) ⟨934344, by rfl⟩ : syracuseStep 9966341 = 1868689) B1868689
theorem B2298689 : Blo 603293 2298689 := bstep (se 2 (by rfl) ⟨862008, by rfl⟩ : syracuseStep 2298689 = 1724017) B1724017
theorem B2036555 : Blo 603293 2036555 := bstep (se 1 (by rfl) ⟨1527416, by rfl⟩ : syracuseStep 2036555 = 3054833) B3054833
theorem B922571 : Blo 603293 922571 := bstep (se 1 (by rfl) ⟨691928, by rfl⟩ : syracuseStep 922571 = 1383857) B1383857
theorem B2036825 : Blo 603293 2036825 := bstep (se 2 (by rfl) ⟨763809, by rfl⟩ : syracuseStep 2036825 = 1527619) B1527619
theorem B3413123 : Blo 603293 3413123 := bstep (se 1 (by rfl) ⟨2559842, by rfl⟩ : syracuseStep 3413123 = 5119685) B5119685
theorem B1152139 : Blo 603293 1152139 := bstep (se 1 (by rfl) ⟨864104, by rfl⟩ : syracuseStep 1152139 = 1728209) B1728209
theorem B1021079 : Blo 603293 1021079 := bstep (se 1 (by rfl) ⟨765809, by rfl⟩ : syracuseStep 1021079 = 1531619) B1531619
theorem B5182643 : Blo 603293 5182643 := bstep (se 1 (by rfl) ⟨3886982, by rfl⟩ : syracuseStep 5182643 = 7773965) B7773965
theorem B1152215 : Blo 603293 1152215 := bstep (se 1 (by rfl) ⟨864161, by rfl⟩ : syracuseStep 1152215 = 1728323) B1728323
theorem B1021207 : Blo 603293 1021207 := bstep (se 1 (by rfl) ⟨765905, by rfl⟩ : syracuseStep 1021207 = 1531811) B1531811
theorem B3446347 : Blo 603293 3446347 := bstep (se 1 (by rfl) ⟨2584760, by rfl⟩ : syracuseStep 3446347 = 5169521) B5169521
theorem B2037527 : Blo 603293 2037527 := bstep (se 1 (by rfl) ⟨1528145, by rfl⟩ : syracuseStep 2037527 = 3056291) B3056291
theorem B3446621 : Blo 603293 3446621 := bstep (se 3 (by rfl) ⟨646241, by rfl⟩ : syracuseStep 3446621 = 1292483) B1292483
theorem B1152883 : Blo 603293 1152883 := bstep (se 1 (by rfl) ⟨864662, by rfl⟩ : syracuseStep 1152883 = 1729325) B1729325
theorem B1021835 : Blo 603293 1021835 := bstep (se 1 (by rfl) ⟨766376, by rfl⟩ : syracuseStep 1021835 = 1532753) B1532753
theorem B1021963 : Blo 603293 1021963 := bstep (se 1 (by rfl) ⟨766472, by rfl⟩ : syracuseStep 1021963 = 1532945) B1532945
theorem B2627635 : Blo 603293 2627635 := bstep (se 1 (by rfl) ⟨1970726, by rfl⟩ : syracuseStep 2627635 = 3941453) B3941453
theorem B1022105 : Blo 603293 1022105 := bstep (se 2 (by rfl) ⟨383289, by rfl⟩ : syracuseStep 1022105 = 766579) B766579
theorem B3873041 : Blo 603293 3873041 := bstep (se 2 (by rfl) ⟨1452390, by rfl⟩ : syracuseStep 3873041 = 2904781) B2904781
theorem B2300177 : Blo 603293 2300177 := bstep (se 2 (by rfl) ⟨862566, by rfl⟩ : syracuseStep 2300177 = 1725133) B1725133
theorem B1022233 : Blo 603293 1022233 := bstep (se 2 (by rfl) ⟨383337, by rfl⟩ : syracuseStep 1022233 = 766675) B766675
theorem B2038067 : Blo 603293 2038067 := bstep (se 1 (by rfl) ⟨1528550, by rfl⟩ : syracuseStep 2038067 = 3057101) B3057101
theorem B1939801 : Blo 603293 1939801 := bstep (se 2 (by rfl) ⟨727425, by rfl⟩ : syracuseStep 1939801 = 1454851) B1454851
theorem B2038337 : Blo 603293 2038337 := bstep (se 2 (by rfl) ⟨764376, by rfl⟩ : syracuseStep 2038337 = 1528753) B1528753
theorem B7740035 : Blo 603293 7740035 := bstep (se 1 (by rfl) ⟨5805026, by rfl⟩ : syracuseStep 7740035 = 11610053) B11610053
theorem B2300633 : Blo 603293 2300633 := bstep (se 2 (by rfl) ⟨862737, by rfl⟩ : syracuseStep 2300633 = 1725475) B1725475
theorem B1022807 : Blo 603293 1022807 := bstep (se 1 (by rfl) ⟨767105, by rfl⟩ : syracuseStep 1022807 = 1534211) B1534211
theorem B2300845 : Blo 603293 2300845 := bstep (se 3 (by rfl) ⟨431408, by rfl⟩ : syracuseStep 2300845 = 862817) B862817
theorem B1022935 : Blo 603293 1022935 := bstep (se 1 (by rfl) ⟨767201, by rfl⟩ : syracuseStep 1022935 = 1534403) B1534403
theorem B728075 : Blo 603293 728075 := bstep (se 1 (by rfl) ⟨546056, by rfl⟩ : syracuseStep 728075 = 1092113) B1092113
theorem B5184557 : Blo 603293 5184557 := bstep (se 3 (by rfl) ⟨972104, by rfl⟩ : syracuseStep 5184557 = 1944209) B1944209
theorem B2038877 : Blo 603293 2038877 := bstep (se 3 (by rfl) ⟨382289, by rfl⟩ : syracuseStep 2038877 = 764579) B764579
theorem B2301149 : Blo 603293 2301149 := bstep (se 3 (by rfl) ⟨431465, by rfl⟩ : syracuseStep 2301149 = 862931) B862931
theorem B1088947 : Blo 603293 1088947 := bstep (se 1 (by rfl) ⟨816710, by rfl⟩ : syracuseStep 1088947 = 1633421) B1633421
theorem B1023563 : Blo 603293 1023563 := bstep (se 1 (by rfl) ⟨767672, by rfl⟩ : syracuseStep 1023563 = 1535345) B1535345
theorem B1449623 : Blo 603293 1449623 := bstep (se 1 (by rfl) ⟨1087217, by rfl⟩ : syracuseStep 1449623 = 2174435) B2174435
theorem B1941185 : Blo 603293 1941185 := bstep (se 2 (by rfl) ⟨727944, by rfl⟩ : syracuseStep 1941185 = 1455889) B1455889
theorem B1023691 : Blo 603293 1023691 := bstep (se 1 (by rfl) ⟨767768, by rfl⟩ : syracuseStep 1023691 = 1535537) B1535537
theorem B5185241 : Blo 603293 5185241 := bstep (se 2 (by rfl) ⟨1944465, by rfl⟩ : syracuseStep 5185241 = 3888931) B3888931
theorem B1023833 : Blo 603293 1023833 := bstep (se 2 (by rfl) ⟨383937, by rfl⟩ : syracuseStep 1023833 = 767875) B767875
theorem B1089409 : Blo 603293 1089409 := bstep (se 2 (by rfl) ⟨408528, by rfl⟩ : syracuseStep 1089409 = 817057) B817057
theorem B3678169 : Blo 603293 3678169 := bstep (se 2 (by rfl) ⟨1379313, by rfl⟩ : syracuseStep 3678169 = 2758627) B2758627
theorem B1023961 : Blo 603293 1023961 := bstep (se 2 (by rfl) ⟨383985, by rfl⟩ : syracuseStep 1023961 = 767971) B767971
theorem B860311 : Blo 603293 860311 := bstep (se 1 (by rfl) ⟨645233, by rfl⟩ : syracuseStep 860311 = 1290467) B1290467
theorem B2040011 : Blo 603293 2040011 := bstep (se 1 (by rfl) ⟨1530008, by rfl⟩ : syracuseStep 2040011 = 3060017) B3060017
theorem B1450315 : Blo 603293 1450315 := bstep (se 1 (by rfl) ⟨1087736, by rfl⟩ : syracuseStep 1450315 = 2175473) B2175473
theorem B1450391 : Blo 603293 1450391 := bstep (se 1 (by rfl) ⟨1087793, by rfl⟩ : syracuseStep 1450391 = 2175587) B2175587
theorem B1089985 : Blo 603293 1089985 := bstep (se 2 (by rfl) ⟨408744, by rfl⟩ : syracuseStep 1089985 = 817489) B817489
theorem B2040281 : Blo 603293 2040281 := bstep (se 2 (by rfl) ⟨765105, by rfl⟩ : syracuseStep 2040281 = 1530211) B1530211
theorem B1024535 : Blo 603293 1024535 := bstep (se 1 (by rfl) ⟨768401, by rfl⟩ : syracuseStep 1024535 = 1536803) B1536803
theorem B1024663 : Blo 603293 1024663 := bstep (se 1 (by rfl) ⟨768497, by rfl⟩ : syracuseStep 1024663 = 1536995) B1536995
theorem B5513933 : Blo 603293 5513933 := bstep (se 3 (by rfl) ⟨1033862, by rfl⟩ : syracuseStep 5513933 = 2067725) B2067725
theorem B4367321 : Blo 603293 4367321 := bstep (se 2 (by rfl) ⟨1637745, by rfl⟩ : syracuseStep 4367321 = 3275491) B3275491
theorem B2040983 : Blo 603293 2040983 := bstep (se 1 (by rfl) ⟨1530737, by rfl⟩ : syracuseStep 2040983 = 3061475) B3061475
theorem B10200305 : Blo 603293 10200305 := bstep (se 2 (by rfl) ⟨3825114, by rfl⟩ : syracuseStep 10200305 = 7650229) B7650229
theorem B14722577 : Blo 603293 14722577 := bstep (se 2 (by rfl) ⟨5520966, by rfl⟩ : syracuseStep 14722577 = 11041933) B11041933
theorem B1451699 : Blo 603293 1451699 := bstep (se 1 (by rfl) ⟨1088774, by rfl⟩ : syracuseStep 1451699 = 2177549) B2177549
theorem B2041523 : Blo 603293 2041523 := bstep (se 1 (by rfl) ⟨1531142, by rfl⟩ : syracuseStep 2041523 = 3062285) B3062285
theorem B763607 : Blo 603293 763607 := bstep (se 1 (by rfl) ⟨572705, by rfl⟩ : syracuseStep 763607 = 1145411) B1145411
theorem B2303747 : Blo 603293 2303747 := bstep (se 1 (by rfl) ⟨1727810, by rfl⟩ : syracuseStep 2303747 = 3455621) B3455621
theorem B3057425 : Blo 603293 3057425 := bstep (se 2 (by rfl) ⟨1146534, by rfl⟩ : syracuseStep 3057425 = 2293069) B2293069
theorem B2303761 : Blo 603293 2303761 := bstep (se 2 (by rfl) ⟨863910, by rfl⟩ : syracuseStep 2303761 = 1727821) B1727821
theorem B1943389 : Blo 603293 1943389 := bstep (se 3 (by rfl) ⟨364385, by rfl⟩ : syracuseStep 1943389 = 728771) B728771
theorem B3057587 : Blo 603293 3057587 := bstep (se 1 (by rfl) ⟨2293190, by rfl⟩ : syracuseStep 3057587 = 4586381) B4586381
theorem B2041793 : Blo 603293 2041793 := bstep (se 2 (by rfl) ⟨765672, by rfl⟩ : syracuseStep 2041793 = 1531345) B1531345
theorem B2304065 : Blo 603293 2304065 := bstep (se 2 (by rfl) ⟨864024, by rfl⟩ : syracuseStep 2304065 = 1728049) B1728049
theorem B698539 : Blo 603293 698539 := bstep (se 1 (by rfl) ⟨523904, by rfl⟩ : syracuseStep 698539 = 1047809) B1047809
theorem B2074841 : Blo 603293 2074841 := bstep (se 2 (by rfl) ⟨778065, by rfl⟩ : syracuseStep 2074841 = 1556131) B1556131
theorem B2337041 : Blo 603293 2337041 := bstep (se 2 (by rfl) ⟨876390, by rfl⟩ : syracuseStep 2337041 = 1752781) B1752781
theorem B764311 : Blo 603293 764311 := bstep (se 1 (by rfl) ⟨573233, by rfl⟩ : syracuseStep 764311 = 1146467) B1146467
theorem B2042333 : Blo 603293 2042333 := bstep (se 3 (by rfl) ⟨382937, by rfl⟩ : syracuseStep 2042333 = 765875) B765875
theorem B16198157 : Blo 603293 16198157 := bstep (se 3 (by rfl) ⟨3037154, by rfl⟩ : syracuseStep 16198157 = 6074309) B6074309
theorem B1288793 : Blo 603293 1288793 := bstep (se 2 (by rfl) ⟨483297, by rfl⟩ : syracuseStep 1288793 = 966595) B966595
theorem B4991581 : Blo 603293 4991581 := bstep (se 3 (by rfl) ⟨935921, by rfl⟩ : syracuseStep 4991581 = 1871843) B1871843
theorem B2304733 : Blo 603293 2304733 := bstep (se 3 (by rfl) ⟨432137, by rfl⟩ : syracuseStep 2304733 = 864275) B864275
theorem B5155649 : Blo 603293 5155649 := bstep (se 2 (by rfl) ⟨1933368, by rfl⟩ : syracuseStep 5155649 = 3866737) B3866737
theorem B4139851 : Blo 603293 4139851 := bstep (se 1 (by rfl) ⟨3104888, by rfl⟩ : syracuseStep 4139851 = 6209777) B6209777
theorem B3877733 : Blo 603293 3877733 := bstep (se 4 (by rfl) ⟨363537, by rfl⟩ : syracuseStep 3877733 = 727075) B727075
theorem B1092595 : Blo 603293 1092595 := bstep (se 1 (by rfl) ⟨819446, by rfl⟩ : syracuseStep 1092595 = 1638893) B1638893
theorem B1092695 : Blo 603293 1092695 := bstep (se 1 (by rfl) ⟨819521, by rfl⟩ : syracuseStep 1092695 = 1639043) B1639043
theorem B1289305 : Blo 603293 1289305 := bstep (se 2 (by rfl) ⟨483489, by rfl⟩ : syracuseStep 1289305 = 966979) B966979
theorem B3451997 : Blo 603293 3451997 := bstep (se 3 (by rfl) ⟨647249, by rfl⟩ : syracuseStep 3451997 = 1294499) B1294499
theorem B1289459 : Blo 603293 1289459 := bstep (se 1 (by rfl) ⟨967094, by rfl⟩ : syracuseStep 1289459 = 1934189) B1934189
theorem B3878219 : Blo 603293 3878219 := bstep (se 1 (by rfl) ⟨2908664, by rfl⟩ : syracuseStep 3878219 = 5817329) B5817329
theorem B2043467 : Blo 603293 2043467 := bstep (se 1 (by rfl) ⟨1532600, by rfl⟩ : syracuseStep 2043467 = 3065201) B3065201
theorem B863831 : Blo 603293 863831 := bstep (se 1 (by rfl) ⟨647873, by rfl⟩ : syracuseStep 863831 = 1295747) B1295747
theorem B3059531 : Blo 603293 3059531 := bstep (se 1 (by rfl) ⟨2294648, by rfl⟩ : syracuseStep 3059531 = 4589297) B4589297
theorem B2043737 : Blo 603293 2043737 := bstep (se 2 (by rfl) ⟨766401, by rfl⟩ : syracuseStep 2043737 = 1532803) B1532803
theorem B5451781 : Blo 603293 5451781 := bstep (se 4 (by rfl) ⟨511104, by rfl⟩ : syracuseStep 5451781 = 1022209) B1022209
theorem B766027 : Blo 603293 766027 := bstep (se 1 (by rfl) ⟨574520, by rfl⟩ : syracuseStep 766027 = 1149041) B1149041
theorem B1290433 : Blo 603293 1290433 := bstep (se 2 (by rfl) ⟨483912, by rfl⟩ : syracuseStep 1290433 = 967825) B967825
theorem B1290775 : Blo 603293 1290775 := bstep (se 1 (by rfl) ⟨968081, by rfl⟩ : syracuseStep 1290775 = 1936163) B1936163
theorem B2044439 : Blo 603293 2044439 := bstep (se 1 (by rfl) ⟨1533329, by rfl⟩ : syracuseStep 2044439 = 3066659) B3066659
theorem B1094195 : Blo 603293 1094195 := bstep (se 1 (by rfl) ⟨820646, by rfl⟩ : syracuseStep 1094195 = 1641293) B1641293
theorem B2175761 : Blo 603293 2175761 := bstep (se 2 (by rfl) ⟨815910, by rfl⟩ : syracuseStep 2175761 = 1631821) B1631821
theorem B4371245 : Blo 603293 4371245 := bstep (se 3 (by rfl) ⟨819608, by rfl⟩ : syracuseStep 4371245 = 1639217) B1639217
theorem B3879859 : Blo 603293 3879859 := bstep (se 1 (by rfl) ⟨2909894, by rfl⟩ : syracuseStep 3879859 = 5819789) B5819789
theorem B1291211 : Blo 603293 1291211 := bstep (se 1 (by rfl) ⟨968408, by rfl⟩ : syracuseStep 1291211 = 1936817) B1936817
theorem B1553431 : Blo 603293 1553431 := bstep (se 1 (by rfl) ⟨1165073, by rfl⟩ : syracuseStep 1553431 = 2330147) B2330147
theorem B766999 : Blo 603293 766999 := bstep (se 1 (by rfl) ⟨575249, by rfl⟩ : syracuseStep 766999 = 1150499) B1150499
theorem B2044979 : Blo 603293 2044979 := bstep (se 1 (by rfl) ⟨1533734, by rfl⟩ : syracuseStep 2044979 = 3067469) B3067469
theorem B5158039 : Blo 603293 5158039 := bstep (se 1 (by rfl) ⟨3868529, by rfl⟩ : syracuseStep 5158039 = 7737059) B7737059
theorem B603307 : Blo 603293 603307 := bstep (se 1 (by rfl) ⟨452480, by rfl⟩ : syracuseStep 603307 = 904961) B904961
theorem B5256371 : Blo 603293 5256371 := bstep (se 1 (by rfl) ⟨3942278, by rfl⟩ : syracuseStep 5256371 = 7884557) B7884557
theorem B603319 : Blo 603293 603319 := bstep (se 1 (by rfl) ⟨452489, by rfl⟩ : syracuseStep 603319 = 904979) B904979
theorem B603339 : Blo 603293 603339 := bstep (se 1 (by rfl) ⟨452504, by rfl⟩ : syracuseStep 603339 = 905009) B905009
theorem B603351 : Blo 603293 603351 := bstep (se 1 (by rfl) ⟨452513, by rfl⟩ : syracuseStep 603351 = 905027) B905027
theorem B603371 : Blo 603293 603371 := bstep (se 1 (by rfl) ⟨452528, by rfl⟩ : syracuseStep 603371 = 905057) B905057
theorem B603383 : Blo 603293 603383 := bstep (se 1 (by rfl) ⟨452537, by rfl⟩ : syracuseStep 603383 = 905075) B905075
theorem B603403 : Blo 603293 603403 := bstep (se 1 (by rfl) ⟨452552, by rfl⟩ : syracuseStep 603403 = 905105) B905105
theorem B603415 : Blo 603293 603415 := bstep (se 1 (by rfl) ⟨452561, by rfl⟩ : syracuseStep 603415 = 905123) B905123
theorem B603435 : Blo 603293 603435 := bstep (se 1 (by rfl) ⟨452576, by rfl⟩ : syracuseStep 603435 = 905153) B905153
theorem B12432685 : Blo 603293 12432685 := bstep (se 3 (by rfl) ⟨2331128, by rfl⟩ : syracuseStep 12432685 = 4662257) B4662257
theorem B603447 : Blo 603293 603447 := bstep (se 1 (by rfl) ⟨452585, by rfl⟩ : syracuseStep 603447 = 905171) B905171
theorem B2045249 : Blo 603293 2045249 := bstep (se 2 (by rfl) ⟨766968, by rfl⟩ : syracuseStep 2045249 = 1533937) B1533937
theorem B603467 : Blo 603293 603467 := bstep (se 1 (by rfl) ⟨452600, by rfl⟩ : syracuseStep 603467 = 905201) B905201
theorem B603479 : Blo 603293 603479 := bstep (se 1 (by rfl) ⟨452609, by rfl⟩ : syracuseStep 603479 = 905219) B905219
theorem B603499 : Blo 603293 603499 := bstep (se 1 (by rfl) ⟨452624, by rfl⟩ : syracuseStep 603499 = 905249) B905249
theorem B603511 : Blo 603293 603511 := bstep (se 1 (by rfl) ⟨452633, by rfl⟩ : syracuseStep 603511 = 905267) B905267
theorem B603531 : Blo 603293 603531 := bstep (se 1 (by rfl) ⟨452648, by rfl⟩ : syracuseStep 603531 = 905297) B905297
theorem B603543 : Blo 603293 603543 := bstep (se 1 (by rfl) ⟨452657, by rfl⟩ : syracuseStep 603543 = 905315) B905315
theorem B603563 : Blo 603293 603563 := bstep (se 1 (by rfl) ⟨452672, by rfl⟩ : syracuseStep 603563 = 905345) B905345
theorem B7386547 : Blo 603293 7386547 := bstep (se 1 (by rfl) ⟨5539910, by rfl⟩ : syracuseStep 7386547 = 11079821) B11079821
theorem B603575 : Blo 603293 603575 := bstep (se 1 (by rfl) ⟨452681, by rfl⟩ : syracuseStep 603575 = 905363) B905363
theorem B603595 : Blo 603293 603595 := bstep (se 1 (by rfl) ⟨452696, by rfl⟩ : syracuseStep 603595 = 905393) B905393
theorem B1455563 : Blo 603293 1455563 := bstep (se 1 (by rfl) ⟨1091672, by rfl⟩ : syracuseStep 1455563 = 2183345) B2183345
theorem B603607 : Blo 603293 603607 := bstep (se 1 (by rfl) ⟨452705, by rfl⟩ : syracuseStep 603607 = 905411) B905411
theorem B603627 : Blo 603293 603627 := bstep (se 1 (by rfl) ⟨452720, by rfl⟩ : syracuseStep 603627 = 905441) B905441
theorem B603639 : Blo 603293 603639 := bstep (se 1 (by rfl) ⟨452729, by rfl⟩ : syracuseStep 603639 = 905459) B905459
theorem B603659 : Blo 603293 603659 := bstep (se 1 (by rfl) ⟨452744, by rfl⟩ : syracuseStep 603659 = 905489) B905489
theorem B10335761 : Blo 603293 10335761 := bstep (se 2 (by rfl) ⟨3875910, by rfl⟩ : syracuseStep 10335761 = 7751821) B7751821
theorem B603671 : Blo 603293 603671 := bstep (se 1 (by rfl) ⟨452753, by rfl⟩ : syracuseStep 603671 = 905507) B905507
theorem B603691 : Blo 603293 603691 := bstep (se 1 (by rfl) ⟨452768, by rfl⟩ : syracuseStep 603691 = 905537) B905537
theorem B603703 : Blo 603293 603703 := bstep (se 1 (by rfl) ⟨452777, by rfl⟩ : syracuseStep 603703 = 905555) B905555
theorem B3061313 : Blo 603293 3061313 := bstep (se 2 (by rfl) ⟨1147992, by rfl⟩ : syracuseStep 3061313 = 2295985) B2295985
theorem B603723 : Blo 603293 603723 := bstep (se 1 (by rfl) ⟨452792, by rfl⟩ : syracuseStep 603723 = 905585) B905585
theorem B603735 : Blo 603293 603735 := bstep (se 1 (by rfl) ⟨452801, by rfl⟩ : syracuseStep 603735 = 905603) B905603
theorem B603755 : Blo 603293 603755 := bstep (se 1 (by rfl) ⟨452816, by rfl⟩ : syracuseStep 603755 = 905633) B905633
theorem B603767 : Blo 603293 603767 := bstep (se 1 (by rfl) ⟨452825, by rfl⟩ : syracuseStep 603767 = 905651) B905651
theorem B11941507 : Blo 603293 11941507 := bstep (se 1 (by rfl) ⟨8956130, by rfl⟩ : syracuseStep 11941507 = 17912261) B17912261
theorem B9942659 : Blo 603293 9942659 := bstep (se 1 (by rfl) ⟨7456994, by rfl⟩ : syracuseStep 9942659 = 14913989) B14913989
theorem B3454595 : Blo 603293 3454595 := bstep (se 1 (by rfl) ⟨2590946, by rfl⟩ : syracuseStep 3454595 = 5181893) B5181893
theorem B1357451 : Blo 603293 1357451 := bstep (se 1 (by rfl) ⟨1018088, by rfl⟩ : syracuseStep 1357451 = 2036177) B2036177
theorem B603787 : Blo 603293 603787 := bstep (se 1 (by rfl) ⟨452840, by rfl⟩ : syracuseStep 603787 = 905681) B905681
theorem B603799 : Blo 603293 603799 := bstep (se 1 (by rfl) ⟨452849, by rfl⟩ : syracuseStep 603799 = 905699) B905699
theorem B603819 : Blo 603293 603819 := bstep (se 1 (by rfl) ⟨452864, by rfl⟩ : syracuseStep 603819 = 905729) B905729
theorem B603831 : Blo 603293 603831 := bstep (se 1 (by rfl) ⟨452873, by rfl⟩ : syracuseStep 603831 = 905747) B905747
theorem B1357505 : Blo 603293 1357505 := bstep (se 2 (by rfl) ⟨509064, by rfl⟩ : syracuseStep 1357505 = 1018129) B1018129
theorem B603851 : Blo 603293 603851 := bstep (se 1 (by rfl) ⟨452888, by rfl⟩ : syracuseStep 603851 = 905777) B905777
theorem B603863 : Blo 603293 603863 := bstep (se 1 (by rfl) ⟨452897, by rfl⟩ : syracuseStep 603863 = 905795) B905795
theorem B603883 : Blo 603293 603883 := bstep (se 1 (by rfl) ⟨452912, by rfl⟩ : syracuseStep 603883 = 905825) B905825
theorem B603895 : Blo 603293 603895 := bstep (se 1 (by rfl) ⟨452921, by rfl⟩ : syracuseStep 603895 = 905843) B905843
theorem B603915 : Blo 603293 603915 := bstep (se 1 (by rfl) ⟨452936, by rfl⟩ : syracuseStep 603915 = 905873) B905873
theorem B603927 : Blo 603293 603927 := bstep (se 1 (by rfl) ⟨452945, by rfl⟩ : syracuseStep 603927 = 905891) B905891
theorem B603947 : Blo 603293 603947 := bstep (se 1 (by rfl) ⟨452960, by rfl⟩ : syracuseStep 603947 = 905921) B905921
theorem B603959 : Blo 603293 603959 := bstep (se 1 (by rfl) ⟨452969, by rfl⟩ : syracuseStep 603959 = 905939) B905939
theorem B603979 : Blo 603293 603979 := bstep (se 1 (by rfl) ⟨452984, by rfl⟩ : syracuseStep 603979 = 905969) B905969
theorem B1292107 : Blo 603293 1292107 := bstep (se 1 (by rfl) ⟨969080, by rfl⟩ : syracuseStep 1292107 = 1938161) B1938161
theorem B767819 : Blo 603293 767819 := bstep (se 1 (by rfl) ⟨575864, by rfl⟩ : syracuseStep 767819 = 1151729) B1151729
theorem B603991 : Blo 603293 603991 := bstep (se 1 (by rfl) ⟨452993, by rfl⟩ : syracuseStep 603991 = 905987) B905987
theorem B2045789 : Blo 603293 2045789 := bstep (se 3 (by rfl) ⟨383585, by rfl⟩ : syracuseStep 2045789 = 767171) B767171
theorem B604011 : Blo 603293 604011 := bstep (se 1 (by rfl) ⟨453008, by rfl⟩ : syracuseStep 604011 = 906017) B906017
theorem B604023 : Blo 603293 604023 := bstep (se 1 (by rfl) ⟨453017, by rfl⟩ : syracuseStep 604023 = 906035) B906035
theorem B604043 : Blo 603293 604043 := bstep (se 1 (by rfl) ⟨453032, by rfl⟩ : syracuseStep 604043 = 906065) B906065
theorem B604055 : Blo 603293 604055 := bstep (se 1 (by rfl) ⟨453041, by rfl⟩ : syracuseStep 604055 = 906083) B906083
theorem B1357721 : Blo 603293 1357721 := bstep (se 2 (by rfl) ⟨509145, by rfl⟩ : syracuseStep 1357721 = 1018291) B1018291
theorem B604075 : Blo 603293 604075 := bstep (se 1 (by rfl) ⟨453056, by rfl⟩ : syracuseStep 604075 = 906113) B906113
theorem B604087 : Blo 603293 604087 := bstep (se 1 (by rfl) ⟨453065, by rfl⟩ : syracuseStep 604087 = 906131) B906131
theorem B604107 : Blo 603293 604107 := bstep (se 1 (by rfl) ⟨453080, by rfl⟩ : syracuseStep 604107 = 906161) B906161
theorem B604119 : Blo 603293 604119 := bstep (se 1 (by rfl) ⟨453089, by rfl⟩ : syracuseStep 604119 = 906179) B906179
theorem B604139 : Blo 603293 604139 := bstep (se 1 (by rfl) ⟨453104, by rfl⟩ : syracuseStep 604139 = 906209) B906209
theorem B1357811 : Blo 603293 1357811 := bstep (se 1 (by rfl) ⟨1018358, by rfl⟩ : syracuseStep 1357811 = 2036717) B2036717
theorem B604151 : Blo 603293 604151 := bstep (se 1 (by rfl) ⟨453113, by rfl⟩ : syracuseStep 604151 = 906227) B906227
theorem B604171 : Blo 603293 604171 := bstep (se 1 (by rfl) ⟨453128, by rfl⟩ : syracuseStep 604171 = 906257) B906257
theorem B1357847 : Blo 603293 1357847 := bstep (se 1 (by rfl) ⟨1018385, by rfl⟩ : syracuseStep 1357847 = 2036771) B2036771
theorem B604183 : Blo 603293 604183 := bstep (se 1 (by rfl) ⟨453137, by rfl⟩ : syracuseStep 604183 = 906275) B906275
theorem B604203 : Blo 603293 604203 := bstep (se 1 (by rfl) ⟨453152, by rfl⟩ : syracuseStep 604203 = 906305) B906305
theorem B604215 : Blo 603293 604215 := bstep (se 1 (by rfl) ⟨453161, by rfl⟩ : syracuseStep 604215 = 906323) B906323
theorem B604235 : Blo 603293 604235 := bstep (se 1 (by rfl) ⟨453176, by rfl⟩ : syracuseStep 604235 = 906353) B906353
theorem B604247 : Blo 603293 604247 := bstep (se 1 (by rfl) ⟨453185, by rfl⟩ : syracuseStep 604247 = 906371) B906371
theorem B604267 : Blo 603293 604267 := bstep (se 1 (by rfl) ⟨453200, by rfl⟩ : syracuseStep 604267 = 906401) B906401
theorem B604279 : Blo 603293 604279 := bstep (se 1 (by rfl) ⟨453209, by rfl⟩ : syracuseStep 604279 = 906419) B906419
theorem B604299 : Blo 603293 604299 := bstep (se 1 (by rfl) ⟨453224, by rfl⟩ : syracuseStep 604299 = 906449) B906449
theorem B604311 : Blo 603293 604311 := bstep (se 1 (by rfl) ⟨453233, by rfl⟩ : syracuseStep 604311 = 906467) B906467
theorem B604331 : Blo 603293 604331 := bstep (se 1 (by rfl) ⟨453248, by rfl⟩ : syracuseStep 604331 = 906497) B906497
theorem B604343 : Blo 603293 604343 := bstep (se 1 (by rfl) ⟨453257, by rfl⟩ : syracuseStep 604343 = 906515) B906515
theorem B1358027 : Blo 603293 1358027 := bstep (se 1 (by rfl) ⟨1018520, by rfl⟩ : syracuseStep 1358027 = 2037041) B2037041
theorem B604363 : Blo 603293 604363 := bstep (se 1 (by rfl) ⟨453272, by rfl⟩ : syracuseStep 604363 = 906545) B906545
theorem B604375 : Blo 603293 604375 := bstep (se 1 (by rfl) ⟨453281, by rfl⟩ : syracuseStep 604375 = 906563) B906563
theorem B604395 : Blo 603293 604395 := bstep (se 1 (by rfl) ⟨453296, by rfl⟩ : syracuseStep 604395 = 906593) B906593
theorem B604407 : Blo 603293 604407 := bstep (se 1 (by rfl) ⟨453305, by rfl⟩ : syracuseStep 604407 = 906611) B906611
theorem B1358081 : Blo 603293 1358081 := bstep (se 2 (by rfl) ⟨509280, by rfl⟩ : syracuseStep 1358081 = 1018561) B1018561
theorem B604427 : Blo 603293 604427 := bstep (se 1 (by rfl) ⟨453320, by rfl⟩ : syracuseStep 604427 = 906641) B906641
theorem B604439 : Blo 603293 604439 := bstep (se 1 (by rfl) ⟨453329, by rfl⟩ : syracuseStep 604439 = 906659) B906659
theorem B604459 : Blo 603293 604459 := bstep (se 1 (by rfl) ⟨453344, by rfl⟩ : syracuseStep 604459 = 906689) B906689
theorem B604471 : Blo 603293 604471 := bstep (se 1 (by rfl) ⟨453353, by rfl⟩ : syracuseStep 604471 = 906707) B906707
theorem B604491 : Blo 603293 604491 := bstep (se 1 (by rfl) ⟨453368, by rfl⟩ : syracuseStep 604491 = 906737) B906737
theorem B604503 : Blo 603293 604503 := bstep (se 1 (by rfl) ⟨453377, by rfl⟩ : syracuseStep 604503 = 906755) B906755
theorem B604523 : Blo 603293 604523 := bstep (se 1 (by rfl) ⟨453392, by rfl⟩ : syracuseStep 604523 = 906785) B906785
theorem B23607665 : Blo 603293 23607665 := bstep (se 2 (by rfl) ⟨8852874, by rfl⟩ : syracuseStep 23607665 = 17705749) B17705749
theorem B604535 : Blo 603293 604535 := bstep (se 1 (by rfl) ⟨453401, by rfl⟩ : syracuseStep 604535 = 906803) B906803
theorem B604555 : Blo 603293 604555 := bstep (se 1 (by rfl) ⟨453416, by rfl⟩ : syracuseStep 604555 = 906833) B906833
theorem B604567 : Blo 603293 604567 := bstep (se 1 (by rfl) ⟨453425, by rfl⟩ : syracuseStep 604567 = 906851) B906851
theorem B1456535 : Blo 603293 1456535 := bstep (se 1 (by rfl) ⟨1092401, by rfl⟩ : syracuseStep 1456535 = 2184803) B2184803
theorem B604587 : Blo 603293 604587 := bstep (se 1 (by rfl) ⟨453440, by rfl⟩ : syracuseStep 604587 = 906881) B906881
theorem B604599 : Blo 603293 604599 := bstep (se 1 (by rfl) ⟨453449, by rfl⟩ : syracuseStep 604599 = 906899) B906899
theorem B604619 : Blo 603293 604619 := bstep (se 1 (by rfl) ⟨453464, by rfl⟩ : syracuseStep 604619 = 906929) B906929
theorem B604631 : Blo 603293 604631 := bstep (se 1 (by rfl) ⟨453473, by rfl⟩ : syracuseStep 604631 = 906947) B906947
theorem B1358297 : Blo 603293 1358297 := bstep (se 2 (by rfl) ⟨509361, by rfl⟩ : syracuseStep 1358297 = 1018723) B1018723
theorem B604651 : Blo 603293 604651 := bstep (se 1 (by rfl) ⟨453488, by rfl⟩ : syracuseStep 604651 = 906977) B906977
theorem B604663 : Blo 603293 604663 := bstep (se 1 (by rfl) ⟨453497, by rfl⟩ : syracuseStep 604663 = 906995) B906995
theorem B604683 : Blo 603293 604683 := bstep (se 1 (by rfl) ⟨453512, by rfl⟩ : syracuseStep 604683 = 907025) B907025
theorem B768523 : Blo 603293 768523 := bstep (se 1 (by rfl) ⟨576392, by rfl⟩ : syracuseStep 768523 = 1152785) B1152785
theorem B604695 : Blo 603293 604695 := bstep (se 1 (by rfl) ⟨453521, by rfl⟩ : syracuseStep 604695 = 907043) B907043
theorem B604715 : Blo 603293 604715 := bstep (se 1 (by rfl) ⟨453536, by rfl⟩ : syracuseStep 604715 = 907073) B907073
theorem B1358387 : Blo 603293 1358387 := bstep (se 1 (by rfl) ⟨1018790, by rfl⟩ : syracuseStep 1358387 = 2037581) B2037581
theorem B1292851 : Blo 603293 1292851 := bstep (se 1 (by rfl) ⟨969638, by rfl⟩ : syracuseStep 1292851 = 1939277) B1939277
theorem B604727 : Blo 603293 604727 := bstep (se 1 (by rfl) ⟨453545, by rfl⟩ : syracuseStep 604727 = 907091) B907091
theorem B604747 : Blo 603293 604747 := bstep (se 1 (by rfl) ⟨453560, by rfl⟩ : syracuseStep 604747 = 907121) B907121
theorem B1358423 : Blo 603293 1358423 := bstep (se 1 (by rfl) ⟨1018817, by rfl⟩ : syracuseStep 1358423 = 2037635) B2037635
theorem B604759 : Blo 603293 604759 := bstep (se 1 (by rfl) ⟨453569, by rfl⟩ : syracuseStep 604759 = 907139) B907139
theorem B604779 : Blo 603293 604779 := bstep (se 1 (by rfl) ⟨453584, by rfl⟩ : syracuseStep 604779 = 907169) B907169
theorem B604791 : Blo 603293 604791 := bstep (se 1 (by rfl) ⟨453593, by rfl⟩ : syracuseStep 604791 = 907187) B907187
theorem B604811 : Blo 603293 604811 := bstep (se 1 (by rfl) ⟨453608, by rfl⟩ : syracuseStep 604811 = 907217) B907217
theorem B604823 : Blo 603293 604823 := bstep (se 1 (by rfl) ⟨453617, by rfl⟩ : syracuseStep 604823 = 907235) B907235
theorem B604843 : Blo 603293 604843 := bstep (se 1 (by rfl) ⟨453632, by rfl⟩ : syracuseStep 604843 = 907265) B907265
theorem B604855 : Blo 603293 604855 := bstep (se 1 (by rfl) ⟨453641, by rfl⟩ : syracuseStep 604855 = 907283) B907283
theorem B604875 : Blo 603293 604875 := bstep (se 1 (by rfl) ⟨453656, by rfl⟩ : syracuseStep 604875 = 907313) B907313
theorem B604887 : Blo 603293 604887 := bstep (se 1 (by rfl) ⟨453665, by rfl⟩ : syracuseStep 604887 = 907331) B907331
theorem B604907 : Blo 603293 604907 := bstep (se 1 (by rfl) ⟨453680, by rfl⟩ : syracuseStep 604907 = 907361) B907361
theorem B604919 : Blo 603293 604919 := bstep (se 1 (by rfl) ⟨453689, by rfl⟩ : syracuseStep 604919 = 907379) B907379
theorem B1358603 : Blo 603293 1358603 := bstep (se 1 (by rfl) ⟨1018952, by rfl⟩ : syracuseStep 1358603 = 2037905) B2037905
theorem B604939 : Blo 603293 604939 := bstep (se 1 (by rfl) ⟨453704, by rfl⟩ : syracuseStep 604939 = 907409) B907409
theorem B604951 : Blo 603293 604951 := bstep (se 1 (by rfl) ⟨453713, by rfl⟩ : syracuseStep 604951 = 907427) B907427
theorem B1456919 : Blo 603293 1456919 := bstep (se 1 (by rfl) ⟨1092689, by rfl⟩ : syracuseStep 1456919 = 2185379) B2185379
theorem B604971 : Blo 603293 604971 := bstep (se 1 (by rfl) ⟨453728, by rfl⟩ : syracuseStep 604971 = 907457) B907457
theorem B2177837 : Blo 603293 2177837 := bstep (se 3 (by rfl) ⟨408344, by rfl⟩ : syracuseStep 2177837 = 816689) B816689
theorem B6208301 : Blo 603293 6208301 := bstep (se 3 (by rfl) ⟨1164056, by rfl⟩ : syracuseStep 6208301 = 2328113) B2328113
theorem B604983 : Blo 603293 604983 := bstep (se 1 (by rfl) ⟨453737, by rfl⟩ : syracuseStep 604983 = 907475) B907475
theorem B1358657 : Blo 603293 1358657 := bstep (se 2 (by rfl) ⟨509496, by rfl⟩ : syracuseStep 1358657 = 1018993) B1018993
theorem B605003 : Blo 603293 605003 := bstep (se 1 (by rfl) ⟨453752, by rfl⟩ : syracuseStep 605003 = 907505) B907505
theorem B605015 : Blo 603293 605015 := bstep (se 1 (by rfl) ⟨453761, by rfl⟩ : syracuseStep 605015 = 907523) B907523
theorem B605035 : Blo 603293 605035 := bstep (se 1 (by rfl) ⟨453776, by rfl⟩ : syracuseStep 605035 = 907553) B907553
theorem B605047 : Blo 603293 605047 := bstep (se 1 (by rfl) ⟨453785, by rfl⟩ : syracuseStep 605047 = 907571) B907571
theorem B605067 : Blo 603293 605067 := bstep (se 1 (by rfl) ⟨453800, by rfl⟩ : syracuseStep 605067 = 907601) B907601
theorem B605079 : Blo 603293 605079 := bstep (se 1 (by rfl) ⟨453809, by rfl⟩ : syracuseStep 605079 = 907619) B907619
theorem B605099 : Blo 603293 605099 := bstep (se 1 (by rfl) ⟨453824, by rfl⟩ : syracuseStep 605099 = 907649) B907649
theorem B605111 : Blo 603293 605111 := bstep (se 1 (by rfl) ⟨453833, by rfl⟩ : syracuseStep 605111 = 907667) B907667
theorem B2046923 : Blo 603293 2046923 := bstep (se 1 (by rfl) ⟨1535192, by rfl⟩ : syracuseStep 2046923 = 3070385) B3070385
theorem B605131 : Blo 603293 605131 := bstep (se 1 (by rfl) ⟨453848, by rfl⟩ : syracuseStep 605131 = 907697) B907697
theorem B605143 : Blo 603293 605143 := bstep (se 1 (by rfl) ⟨453857, by rfl⟩ : syracuseStep 605143 = 907715) B907715
theorem B11647961 : Blo 603293 11647961 := bstep (se 2 (by rfl) ⟨4367985, by rfl⟩ : syracuseStep 11647961 = 8735971) B8735971
theorem B605163 : Blo 603293 605163 := bstep (se 1 (by rfl) ⟨453872, by rfl⟩ : syracuseStep 605163 = 907745) B907745
theorem B605175 : Blo 603293 605175 := bstep (se 1 (by rfl) ⟨453881, by rfl⟩ : syracuseStep 605175 = 907763) B907763
theorem B605195 : Blo 603293 605195 := bstep (se 1 (by rfl) ⟨453896, by rfl⟩ : syracuseStep 605195 = 907793) B907793
theorem B605207 : Blo 603293 605207 := bstep (se 1 (by rfl) ⟨453905, by rfl⟩ : syracuseStep 605207 = 907811) B907811
theorem B1358873 : Blo 603293 1358873 := bstep (se 2 (by rfl) ⟨509577, by rfl⟩ : syracuseStep 1358873 = 1019155) B1019155
theorem B1293337 : Blo 603293 1293337 := bstep (se 2 (by rfl) ⟨485001, by rfl⟩ : syracuseStep 1293337 = 970003) B970003
theorem B605227 : Blo 603293 605227 := bstep (se 1 (by rfl) ⟨453920, by rfl⟩ : syracuseStep 605227 = 907841) B907841
theorem B605239 : Blo 603293 605239 := bstep (se 1 (by rfl) ⟨453929, by rfl⟩ : syracuseStep 605239 = 907859) B907859
theorem B605259 : Blo 603293 605259 := bstep (se 1 (by rfl) ⟨453944, by rfl⟩ : syracuseStep 605259 = 907889) B907889
theorem B605271 : Blo 603293 605271 := bstep (se 1 (by rfl) ⟨453953, by rfl⟩ : syracuseStep 605271 = 907907) B907907
theorem B605291 : Blo 603293 605291 := bstep (se 1 (by rfl) ⟨453968, by rfl⟩ : syracuseStep 605291 = 907937) B907937
theorem B1358963 : Blo 603293 1358963 := bstep (se 1 (by rfl) ⟨1019222, by rfl⟩ : syracuseStep 1358963 = 2038445) B2038445
theorem B605303 : Blo 603293 605303 := bstep (se 1 (by rfl) ⟨453977, by rfl⟩ : syracuseStep 605303 = 907955) B907955
theorem B605323 : Blo 603293 605323 := bstep (se 1 (by rfl) ⟨453992, by rfl⟩ : syracuseStep 605323 = 907985) B907985
theorem B1358999 : Blo 603293 1358999 := bstep (se 1 (by rfl) ⟨1019249, by rfl⟩ : syracuseStep 1358999 = 2038499) B2038499
theorem B605335 : Blo 603293 605335 := bstep (se 1 (by rfl) ⟨454001, by rfl⟩ : syracuseStep 605335 = 908003) B908003
theorem B605355 : Blo 603293 605355 := bstep (se 1 (by rfl) ⟨454016, by rfl⟩ : syracuseStep 605355 = 908033) B908033
theorem B605367 : Blo 603293 605367 := bstep (se 1 (by rfl) ⟨454025, by rfl⟩ : syracuseStep 605367 = 908051) B908051
theorem B605387 : Blo 603293 605387 := bstep (se 1 (by rfl) ⟨454040, by rfl⟩ : syracuseStep 605387 = 908081) B908081
theorem B605399 : Blo 603293 605399 := bstep (se 1 (by rfl) ⟨454049, by rfl⟩ : syracuseStep 605399 = 908099) B908099
theorem B2047193 : Blo 603293 2047193 := bstep (se 2 (by rfl) ⟨767697, by rfl⟩ : syracuseStep 2047193 = 1535395) B1535395
theorem B605419 : Blo 603293 605419 := bstep (se 1 (by rfl) ⟨454064, by rfl⟩ : syracuseStep 605419 = 908129) B908129
theorem B605431 : Blo 603293 605431 := bstep (se 1 (by rfl) ⟨454073, by rfl⟩ : syracuseStep 605431 = 908147) B908147
theorem B605451 : Blo 603293 605451 := bstep (se 1 (by rfl) ⟨454088, by rfl⟩ : syracuseStep 605451 = 908177) B908177
theorem B1719575 : Blo 603293 1719575 := bstep (se 1 (by rfl) ⟨1289681, by rfl⟩ : syracuseStep 1719575 = 2579363) B2579363
theorem B605463 : Blo 603293 605463 := bstep (se 1 (by rfl) ⟨454097, by rfl⟩ : syracuseStep 605463 = 908195) B908195
theorem B605483 : Blo 603293 605483 := bstep (se 1 (by rfl) ⟨454112, by rfl⟩ : syracuseStep 605483 = 908225) B908225
theorem B2178355 : Blo 603293 2178355 := bstep (se 1 (by rfl) ⟨1633766, by rfl⟩ : syracuseStep 2178355 = 3267533) B3267533
theorem B605495 : Blo 603293 605495 := bstep (se 1 (by rfl) ⟨454121, by rfl⟩ : syracuseStep 605495 = 908243) B908243
theorem B1359179 : Blo 603293 1359179 := bstep (se 1 (by rfl) ⟨1019384, by rfl⟩ : syracuseStep 1359179 = 2038769) B2038769
theorem B605515 : Blo 603293 605515 := bstep (se 1 (by rfl) ⟨454136, by rfl⟩ : syracuseStep 605515 = 908273) B908273
theorem B605527 : Blo 603293 605527 := bstep (se 1 (by rfl) ⟨454145, by rfl⟩ : syracuseStep 605527 = 908291) B908291
theorem B605547 : Blo 603293 605547 := bstep (se 1 (by rfl) ⟨454160, by rfl⟩ : syracuseStep 605547 = 908321) B908321
theorem B605559 : Blo 603293 605559 := bstep (se 1 (by rfl) ⟨454169, by rfl⟩ : syracuseStep 605559 = 908339) B908339
theorem B1359233 : Blo 603293 1359233 := bstep (se 2 (by rfl) ⟨509712, by rfl⟩ : syracuseStep 1359233 = 1019425) B1019425
theorem B605579 : Blo 603293 605579 := bstep (se 1 (by rfl) ⟨454184, by rfl⟩ : syracuseStep 605579 = 908369) B908369
theorem B605591 : Blo 603293 605591 := bstep (se 1 (by rfl) ⟨454193, by rfl⟩ : syracuseStep 605591 = 908387) B908387
theorem B605611 : Blo 603293 605611 := bstep (se 1 (by rfl) ⟨454208, by rfl⟩ : syracuseStep 605611 = 908417) B908417
theorem B605623 : Blo 603293 605623 := bstep (se 1 (by rfl) ⟨454217, by rfl⟩ : syracuseStep 605623 = 908435) B908435
theorem B605643 : Blo 603293 605643 := bstep (se 1 (by rfl) ⟨454232, by rfl⟩ : syracuseStep 605643 = 908465) B908465
theorem B605655 : Blo 603293 605655 := bstep (se 1 (by rfl) ⟨454241, by rfl⟩ : syracuseStep 605655 = 908483) B908483
theorem B3063257 : Blo 603293 3063257 := bstep (se 2 (by rfl) ⟨1148721, by rfl⟩ : syracuseStep 3063257 = 2297443) B2297443
theorem B2211293 : Blo 603293 2211293 := bstep (se 3 (by rfl) ⟨414617, by rfl⟩ : syracuseStep 2211293 = 829235) B829235
theorem B605675 : Blo 603293 605675 := bstep (se 1 (by rfl) ⟨454256, by rfl⟩ : syracuseStep 605675 = 908513) B908513
theorem B605687 : Blo 603293 605687 := bstep (se 1 (by rfl) ⟨454265, by rfl⟩ : syracuseStep 605687 = 908531) B908531
theorem B605707 : Blo 603293 605707 := bstep (se 1 (by rfl) ⟨454280, by rfl⟩ : syracuseStep 605707 = 908561) B908561
theorem B605719 : Blo 603293 605719 := bstep (se 1 (by rfl) ⟨454289, by rfl⟩ : syracuseStep 605719 = 908579) B908579
theorem B605739 : Blo 603293 605739 := bstep (se 1 (by rfl) ⟨454304, by rfl⟩ : syracuseStep 605739 = 908609) B908609
theorem B605751 : Blo 603293 605751 := bstep (se 1 (by rfl) ⟨454313, by rfl⟩ : syracuseStep 605751 = 908627) B908627
theorem B605771 : Blo 603293 605771 := bstep (se 1 (by rfl) ⟨454328, by rfl⟩ : syracuseStep 605771 = 908657) B908657
theorem B605783 : Blo 603293 605783 := bstep (se 1 (by rfl) ⟨454337, by rfl⟩ : syracuseStep 605783 = 908675) B908675
theorem B1359449 : Blo 603293 1359449 := bstep (se 2 (by rfl) ⟨509793, by rfl⟩ : syracuseStep 1359449 = 1019587) B1019587
theorem B605803 : Blo 603293 605803 := bstep (se 1 (by rfl) ⟨454352, by rfl⟩ : syracuseStep 605803 = 908705) B908705
theorem B605815 : Blo 603293 605815 := bstep (se 1 (by rfl) ⟨454361, by rfl⟩ : syracuseStep 605815 = 908723) B908723
theorem B605835 : Blo 603293 605835 := bstep (se 1 (by rfl) ⟨454376, by rfl⟩ : syracuseStep 605835 = 908753) B908753
theorem B605847 : Blo 603293 605847 := bstep (se 1 (by rfl) ⟨454385, by rfl⟩ : syracuseStep 605847 = 908771) B908771
theorem B605867 : Blo 603293 605867 := bstep (se 1 (by rfl) ⟨454400, by rfl⟩ : syracuseStep 605867 = 908801) B908801
theorem B1359539 : Blo 603293 1359539 := bstep (se 1 (by rfl) ⟨1019654, by rfl⟩ : syracuseStep 1359539 = 2039309) B2039309
theorem B605879 : Blo 603293 605879 := bstep (se 1 (by rfl) ⟨454409, by rfl⟩ : syracuseStep 605879 = 908819) B908819
theorem B605899 : Blo 603293 605899 := bstep (se 1 (by rfl) ⟨454424, by rfl⟩ : syracuseStep 605899 = 908849) B908849
theorem B1359575 : Blo 603293 1359575 := bstep (se 1 (by rfl) ⟨1019681, by rfl⟩ : syracuseStep 1359575 = 2039363) B2039363
theorem B605911 : Blo 603293 605911 := bstep (se 1 (by rfl) ⟨454433, by rfl⟩ : syracuseStep 605911 = 908867) B908867
theorem B605931 : Blo 603293 605931 := bstep (se 1 (by rfl) ⟨454448, by rfl⟩ : syracuseStep 605931 = 908897) B908897
theorem B605943 : Blo 603293 605943 := bstep (se 1 (by rfl) ⟨454457, by rfl⟩ : syracuseStep 605943 = 908915) B908915
theorem B605963 : Blo 603293 605963 := bstep (se 1 (by rfl) ⟨454472, by rfl⟩ : syracuseStep 605963 = 908945) B908945
theorem B1326871 : Blo 603293 1326871 := bstep (se 1 (by rfl) ⟨995153, by rfl⟩ : syracuseStep 1326871 = 1990307) B1990307
theorem B605975 : Blo 603293 605975 := bstep (se 1 (by rfl) ⟨454481, by rfl⟩ : syracuseStep 605975 = 908963) B908963
theorem B605995 : Blo 603293 605995 := bstep (se 1 (by rfl) ⟨454496, by rfl⟩ : syracuseStep 605995 = 908993) B908993
theorem B606007 : Blo 603293 606007 := bstep (se 1 (by rfl) ⟨454505, by rfl⟩ : syracuseStep 606007 = 909011) B909011
theorem B606027 : Blo 603293 606027 := bstep (se 1 (by rfl) ⟨454520, by rfl⟩ : syracuseStep 606027 = 909041) B909041
theorem B1457995 : Blo 603293 1457995 := bstep (se 1 (by rfl) ⟨1093496, by rfl⟩ : syracuseStep 1457995 = 2186993) B2186993
theorem B606039 : Blo 603293 606039 := bstep (se 1 (by rfl) ⟨454529, by rfl⟩ : syracuseStep 606039 = 909059) B909059
theorem B606059 : Blo 603293 606059 := bstep (se 1 (by rfl) ⟨454544, by rfl⟩ : syracuseStep 606059 = 909089) B909089
theorem B606071 : Blo 603293 606071 := bstep (se 1 (by rfl) ⟨454553, by rfl⟩ : syracuseStep 606071 = 909107) B909107
theorem B1359755 : Blo 603293 1359755 := bstep (se 1 (by rfl) ⟨1019816, by rfl⟩ : syracuseStep 1359755 = 2039633) B2039633
theorem B606091 : Blo 603293 606091 := bstep (se 1 (by rfl) ⟨454568, by rfl⟩ : syracuseStep 606091 = 909137) B909137
theorem B606103 : Blo 603293 606103 := bstep (se 1 (by rfl) ⟨454577, by rfl⟩ : syracuseStep 606103 = 909155) B909155
theorem B2047895 : Blo 603293 2047895 := bstep (se 1 (by rfl) ⟨1535921, by rfl⟩ : syracuseStep 2047895 = 3071843) B3071843
theorem B1032089 : Blo 603293 1032089 := bstep (se 2 (by rfl) ⟨387033, by rfl⟩ : syracuseStep 1032089 = 774067) B774067
theorem B606123 : Blo 603293 606123 := bstep (se 1 (by rfl) ⟨454592, by rfl⟩ : syracuseStep 606123 = 909185) B909185
theorem B606135 : Blo 603293 606135 := bstep (se 1 (by rfl) ⟨454601, by rfl⟩ : syracuseStep 606135 = 909203) B909203
theorem B1359809 : Blo 603293 1359809 := bstep (se 2 (by rfl) ⟨509928, by rfl⟩ : syracuseStep 1359809 = 1019857) B1019857
theorem B606155 : Blo 603293 606155 := bstep (se 1 (by rfl) ⟨454616, by rfl⟩ : syracuseStep 606155 = 909233) B909233
theorem B606167 : Blo 603293 606167 := bstep (se 1 (by rfl) ⟨454625, by rfl⟩ : syracuseStep 606167 = 909251) B909251
theorem B606187 : Blo 603293 606187 := bstep (se 1 (by rfl) ⟨454640, by rfl⟩ : syracuseStep 606187 = 909281) B909281
theorem B606199 : Blo 603293 606199 := bstep (se 1 (by rfl) ⟨454649, by rfl⟩ : syracuseStep 606199 = 909299) B909299
theorem B606219 : Blo 603293 606219 := bstep (se 1 (by rfl) ⟨454664, by rfl⟩ : syracuseStep 606219 = 909329) B909329
theorem B606231 : Blo 603293 606231 := bstep (se 1 (by rfl) ⟨454673, by rfl⟩ : syracuseStep 606231 = 909347) B909347
theorem B606251 : Blo 603293 606251 := bstep (se 1 (by rfl) ⟨454688, by rfl⟩ : syracuseStep 606251 = 909377) B909377
theorem B606263 : Blo 603293 606263 := bstep (se 1 (by rfl) ⟨454697, by rfl⟩ : syracuseStep 606263 = 909395) B909395
theorem B606283 : Blo 603293 606283 := bstep (se 1 (by rfl) ⟨454712, by rfl⟩ : syracuseStep 606283 = 909425) B909425
theorem B606295 : Blo 603293 606295 := bstep (se 1 (by rfl) ⟨454721, by rfl⟩ : syracuseStep 606295 = 909443) B909443
theorem B606315 : Blo 603293 606315 := bstep (se 1 (by rfl) ⟨454736, by rfl⟩ : syracuseStep 606315 = 909473) B909473
theorem B606327 : Blo 603293 606327 := bstep (se 1 (by rfl) ⟨454745, by rfl⟩ : syracuseStep 606327 = 909491) B909491
theorem B606347 : Blo 603293 606347 := bstep (se 1 (by rfl) ⟨454760, by rfl⟩ : syracuseStep 606347 = 909521) B909521
theorem B606359 : Blo 603293 606359 := bstep (se 1 (by rfl) ⟨454769, by rfl⟩ : syracuseStep 606359 = 909539) B909539
theorem B1360025 : Blo 603293 1360025 := bstep (se 2 (by rfl) ⟨510009, by rfl⟩ : syracuseStep 1360025 = 1020019) B1020019
theorem B606379 : Blo 603293 606379 := bstep (se 1 (by rfl) ⟨454784, by rfl⟩ : syracuseStep 606379 = 909569) B909569
theorem B606391 : Blo 603293 606391 := bstep (se 1 (by rfl) ⟨454793, by rfl⟩ : syracuseStep 606391 = 909587) B909587
theorem B606411 : Blo 603293 606411 := bstep (se 1 (by rfl) ⟨454808, by rfl⟩ : syracuseStep 606411 = 909617) B909617
theorem B606423 : Blo 603293 606423 := bstep (se 1 (by rfl) ⟨454817, by rfl⟩ : syracuseStep 606423 = 909635) B909635
theorem B606443 : Blo 603293 606443 := bstep (se 1 (by rfl) ⟨454832, by rfl⟩ : syracuseStep 606443 = 909665) B909665
theorem B1360115 : Blo 603293 1360115 := bstep (se 1 (by rfl) ⟨1020086, by rfl⟩ : syracuseStep 1360115 = 2040173) B2040173
theorem B606455 : Blo 603293 606455 := bstep (se 1 (by rfl) ⟨454841, by rfl⟩ : syracuseStep 606455 = 909683) B909683
theorem B606475 : Blo 603293 606475 := bstep (se 1 (by rfl) ⟨454856, by rfl⟩ : syracuseStep 606475 = 909713) B909713
theorem B1360151 : Blo 603293 1360151 := bstep (se 1 (by rfl) ⟨1020113, by rfl⟩ : syracuseStep 1360151 = 2040227) B2040227
theorem B606487 : Blo 603293 606487 := bstep (se 1 (by rfl) ⟨454865, by rfl⟩ : syracuseStep 606487 = 909731) B909731
theorem B606507 : Blo 603293 606507 := bstep (se 1 (by rfl) ⟨454880, by rfl⟩ : syracuseStep 606507 = 909761) B909761
theorem B606519 : Blo 603293 606519 := bstep (se 1 (by rfl) ⟨454889, by rfl⟩ : syracuseStep 606519 = 909779) B909779
theorem B606539 : Blo 603293 606539 := bstep (se 1 (by rfl) ⟨454904, by rfl⟩ : syracuseStep 606539 = 909809) B909809
theorem B606551 : Blo 603293 606551 := bstep (se 1 (by rfl) ⟨454913, by rfl⟩ : syracuseStep 606551 = 909827) B909827
theorem B606571 : Blo 603293 606571 := bstep (se 1 (by rfl) ⟨454928, by rfl⟩ : syracuseStep 606571 = 909857) B909857
theorem B606583 : Blo 603293 606583 := bstep (se 1 (by rfl) ⟨454937, by rfl⟩ : syracuseStep 606583 = 909875) B909875
theorem B606603 : Blo 603293 606603 := bstep (se 1 (by rfl) ⟨454952, by rfl⟩ : syracuseStep 606603 = 909905) B909905
theorem B606615 : Blo 603293 606615 := bstep (se 1 (by rfl) ⟨454961, by rfl⟩ : syracuseStep 606615 = 909923) B909923
theorem B606635 : Blo 603293 606635 := bstep (se 1 (by rfl) ⟨454976, by rfl⟩ : syracuseStep 606635 = 909953) B909953
theorem B2048435 : Blo 603293 2048435 := bstep (se 1 (by rfl) ⟨1536326, by rfl⟩ : syracuseStep 2048435 = 3072653) B3072653
theorem B1458611 : Blo 603293 1458611 := bstep (se 1 (by rfl) ⟨1093958, by rfl⟩ : syracuseStep 1458611 = 2187917) B2187917
theorem B606647 : Blo 603293 606647 := bstep (se 1 (by rfl) ⟨454985, by rfl⟩ : syracuseStep 606647 = 909971) B909971
theorem B1360331 : Blo 603293 1360331 := bstep (se 1 (by rfl) ⟨1020248, by rfl⟩ : syracuseStep 1360331 = 2040497) B2040497
theorem B606667 : Blo 603293 606667 := bstep (se 1 (by rfl) ⟨455000, by rfl⟩ : syracuseStep 606667 = 910001) B910001
theorem B1294807 : Blo 603293 1294807 := bstep (se 1 (by rfl) ⟨971105, by rfl⟩ : syracuseStep 1294807 = 1942211) B1942211
theorem B606679 : Blo 603293 606679 := bstep (se 1 (by rfl) ⟨455009, by rfl⟩ : syracuseStep 606679 = 910019) B910019
theorem B606699 : Blo 603293 606699 := bstep (se 1 (by rfl) ⟨455024, by rfl⟩ : syracuseStep 606699 = 910049) B910049
theorem B1229299 : Blo 603293 1229299 := bstep (se 1 (by rfl) ⟨921974, by rfl⟩ : syracuseStep 1229299 = 1843949) B1843949
theorem B606711 : Blo 603293 606711 := bstep (se 1 (by rfl) ⟨455033, by rfl⟩ : syracuseStep 606711 = 910067) B910067
theorem B1360385 : Blo 603293 1360385 := bstep (se 2 (by rfl) ⟨510144, by rfl⟩ : syracuseStep 1360385 = 1020289) B1020289
theorem B1294859 : Blo 603293 1294859 := bstep (se 1 (by rfl) ⟨971144, by rfl⟩ : syracuseStep 1294859 = 1942289) B1942289
theorem B606731 : Blo 603293 606731 := bstep (se 1 (by rfl) ⟨455048, by rfl⟩ : syracuseStep 606731 = 910097) B910097
theorem B606743 : Blo 603293 606743 := bstep (se 1 (by rfl) ⟨455057, by rfl⟩ : syracuseStep 606743 = 910115) B910115
theorem B606763 : Blo 603293 606763 := bstep (se 1 (by rfl) ⟨455072, by rfl⟩ : syracuseStep 606763 = 910145) B910145
theorem B606775 : Blo 603293 606775 := bstep (se 1 (by rfl) ⟨455081, by rfl⟩ : syracuseStep 606775 = 910163) B910163
theorem B2900555 : Blo 603293 2900555 := bstep (se 1 (by rfl) ⟨2175416, by rfl⟩ : syracuseStep 2900555 = 4350833) B4350833
theorem B606795 : Blo 603293 606795 := bstep (se 1 (by rfl) ⟨455096, by rfl⟩ : syracuseStep 606795 = 910193) B910193
theorem B606807 : Blo 603293 606807 := bstep (se 1 (by rfl) ⟨455105, by rfl⟩ : syracuseStep 606807 = 910211) B910211
theorem B606827 : Blo 603293 606827 := bstep (se 1 (by rfl) ⟨455120, by rfl⟩ : syracuseStep 606827 = 910241) B910241
theorem B606839 : Blo 603293 606839 := bstep (se 1 (by rfl) ⟨455129, by rfl⟩ : syracuseStep 606839 = 910259) B910259
theorem B606859 : Blo 603293 606859 := bstep (se 1 (by rfl) ⟨455144, by rfl⟩ : syracuseStep 606859 = 910289) B910289
theorem B606871 : Blo 603293 606871 := bstep (se 1 (by rfl) ⟨455153, by rfl⟩ : syracuseStep 606871 = 910307) B910307
theorem B606891 : Blo 603293 606891 := bstep (se 1 (by rfl) ⟨455168, by rfl⟩ : syracuseStep 606891 = 910337) B910337
theorem B606903 : Blo 603293 606903 := bstep (se 1 (by rfl) ⟨455177, by rfl⟩ : syracuseStep 606903 = 910355) B910355
theorem B2048705 : Blo 603293 2048705 := bstep (se 2 (by rfl) ⟨768264, by rfl⟩ : syracuseStep 2048705 = 1536529) B1536529
theorem B606923 : Blo 603293 606923 := bstep (se 1 (by rfl) ⟨455192, by rfl⟩ : syracuseStep 606923 = 910385) B910385
theorem B606935 : Blo 603293 606935 := bstep (se 1 (by rfl) ⟨455201, by rfl⟩ : syracuseStep 606935 = 910403) B910403
theorem B1360601 : Blo 603293 1360601 := bstep (se 2 (by rfl) ⟨510225, by rfl⟩ : syracuseStep 1360601 = 1020451) B1020451
theorem B606955 : Blo 603293 606955 := bstep (se 1 (by rfl) ⟨455216, by rfl⟩ : syracuseStep 606955 = 910433) B910433
theorem B606967 : Blo 603293 606967 := bstep (se 1 (by rfl) ⟨455225, by rfl⟩ : syracuseStep 606967 = 910451) B910451
theorem B606987 : Blo 603293 606987 := bstep (se 1 (by rfl) ⟨455240, by rfl⟩ : syracuseStep 606987 = 910481) B910481
theorem B606999 : Blo 603293 606999 := bstep (se 1 (by rfl) ⟨455249, by rfl⟩ : syracuseStep 606999 = 910499) B910499
theorem B607019 : Blo 603293 607019 := bstep (se 1 (by rfl) ⟨455264, by rfl⟩ : syracuseStep 607019 = 910529) B910529
theorem B2179885 : Blo 603293 2179885 := bstep (se 3 (by rfl) ⟨408728, by rfl⟩ : syracuseStep 2179885 = 817457) B817457
theorem B1360691 : Blo 603293 1360691 := bstep (se 1 (by rfl) ⟨1020518, by rfl⟩ : syracuseStep 1360691 = 2041037) B2041037
theorem B607031 : Blo 603293 607031 := bstep (se 1 (by rfl) ⟨455273, by rfl⟩ : syracuseStep 607031 = 910547) B910547
theorem B607051 : Blo 603293 607051 := bstep (se 1 (by rfl) ⟨455288, by rfl⟩ : syracuseStep 607051 = 910577) B910577
theorem B1360727 : Blo 603293 1360727 := bstep (se 1 (by rfl) ⟨1020545, by rfl⟩ : syracuseStep 1360727 = 2041091) B2041091
theorem B607063 : Blo 603293 607063 := bstep (se 1 (by rfl) ⟨455297, by rfl⟩ : syracuseStep 607063 = 910595) B910595
theorem B607083 : Blo 603293 607083 := bstep (se 1 (by rfl) ⟨455312, by rfl⟩ : syracuseStep 607083 = 910625) B910625
theorem B607095 : Blo 603293 607095 := bstep (se 1 (by rfl) ⟨455321, by rfl⟩ : syracuseStep 607095 = 910643) B910643
theorem B607115 : Blo 603293 607115 := bstep (se 1 (by rfl) ⟨455336, by rfl⟩ : syracuseStep 607115 = 910673) B910673
theorem B607127 : Blo 603293 607127 := bstep (se 1 (by rfl) ⟨455345, by rfl⟩ : syracuseStep 607127 = 910691) B910691
theorem B607147 : Blo 603293 607147 := bstep (se 1 (by rfl) ⟨455360, by rfl⟩ : syracuseStep 607147 = 910721) B910721
theorem B4604849 : Blo 603293 4604849 := bstep (se 2 (by rfl) ⟨1726818, by rfl⟩ : syracuseStep 4604849 = 3453637) B3453637
theorem B607159 : Blo 603293 607159 := bstep (se 1 (by rfl) ⟨455369, by rfl⟩ : syracuseStep 607159 = 910739) B910739
theorem B607179 : Blo 603293 607179 := bstep (se 1 (by rfl) ⟨455384, by rfl⟩ : syracuseStep 607179 = 910769) B910769
theorem B607191 : Blo 603293 607191 := bstep (se 1 (by rfl) ⟨455393, by rfl⟩ : syracuseStep 607191 = 910787) B910787
theorem B607211 : Blo 603293 607211 := bstep (se 1 (by rfl) ⟨455408, by rfl⟩ : syracuseStep 607211 = 910817) B910817
theorem B607223 : Blo 603293 607223 := bstep (se 1 (by rfl) ⟨455417, by rfl⟩ : syracuseStep 607223 = 910835) B910835
theorem B1360907 : Blo 603293 1360907 := bstep (se 1 (by rfl) ⟨1020680, by rfl⟩ : syracuseStep 1360907 = 2041361) B2041361
theorem B607243 : Blo 603293 607243 := bstep (se 1 (by rfl) ⟨455432, by rfl⟩ : syracuseStep 607243 = 910865) B910865
theorem B607255 : Blo 603293 607255 := bstep (se 1 (by rfl) ⟨455441, by rfl⟩ : syracuseStep 607255 = 910883) B910883
theorem B607275 : Blo 603293 607275 := bstep (se 1 (by rfl) ⟨455456, by rfl⟩ : syracuseStep 607275 = 910913) B910913
theorem B3064877 : Blo 603293 3064877 := bstep (se 3 (by rfl) ⟨574664, by rfl⟩ : syracuseStep 3064877 = 1149329) B1149329
theorem B607287 : Blo 603293 607287 := bstep (se 1 (by rfl) ⟨455465, by rfl⟩ : syracuseStep 607287 = 910931) B910931
theorem B1360961 : Blo 603293 1360961 := bstep (se 2 (by rfl) ⟨510360, by rfl⟩ : syracuseStep 1360961 = 1020721) B1020721
theorem B2180189 : Blo 603293 2180189 := bstep (se 3 (by rfl) ⟨408785, by rfl⟩ : syracuseStep 2180189 = 817571) B817571
theorem B4408499 : Blo 603293 4408499 := bstep (se 1 (by rfl) ⟨3306374, by rfl⟩ : syracuseStep 4408499 = 6612749) B6612749
theorem B2180317 : Blo 603293 2180317 := bstep (se 3 (by rfl) ⟨408809, by rfl⟩ : syracuseStep 2180317 = 817619) B817619
theorem B2049245 : Blo 603293 2049245 := bstep (se 3 (by rfl) ⟨384233, by rfl⟩ : syracuseStep 2049245 = 768467) B768467
theorem B1361177 : Blo 603293 1361177 := bstep (se 2 (by rfl) ⟨510441, by rfl⟩ : syracuseStep 1361177 = 1020883) B1020883
theorem B1361267 : Blo 603293 1361267 := bstep (se 1 (by rfl) ⟨1020950, by rfl⟩ : syracuseStep 1361267 = 2041901) B2041901
theorem B1361303 : Blo 603293 1361303 := bstep (se 1 (by rfl) ⟨1020977, by rfl⟩ : syracuseStep 1361303 = 2041955) B2041955
theorem B4605335 : Blo 603293 4605335 := bstep (se 1 (by rfl) ⟨3454001, by rfl⟩ : syracuseStep 4605335 = 6908003) B6908003
theorem B968203 : Blo 603293 968203 := bstep (se 1 (by rfl) ⟨726152, by rfl⟩ : syracuseStep 968203 = 1452305) B1452305
theorem B1361483 : Blo 603293 1361483 := bstep (se 1 (by rfl) ⟨1021112, by rfl⟩ : syracuseStep 1361483 = 2042225) B2042225
theorem B1361537 : Blo 603293 1361537 := bstep (se 2 (by rfl) ⟨510576, by rfl⟩ : syracuseStep 1361537 = 1021153) B1021153
theorem B1722035 : Blo 603293 1722035 := bstep (se 1 (by rfl) ⟨1291526, by rfl⟩ : syracuseStep 1722035 = 2583053) B2583053
theorem B1230515 : Blo 603293 1230515 := bstep (se 1 (by rfl) ⟨922886, by rfl⟩ : syracuseStep 1230515 = 1845773) B1845773
theorem B1361753 : Blo 603293 1361753 := bstep (se 2 (by rfl) ⟨510657, by rfl⟩ : syracuseStep 1361753 = 1021315) B1021315
theorem B1361843 : Blo 603293 1361843 := bstep (se 1 (by rfl) ⟨1021382, by rfl⟩ : syracuseStep 1361843 = 2042765) B2042765
theorem B1361879 : Blo 603293 1361879 := bstep (se 1 (by rfl) ⟨1021409, by rfl⟩ : syracuseStep 1361879 = 2042819) B2042819
theorem B1296499 : Blo 603293 1296499 := bstep (se 1 (by rfl) ⟨972374, by rfl⟩ : syracuseStep 1296499 = 1944749) B1944749
theorem B1362059 : Blo 603293 1362059 := bstep (se 1 (by rfl) ⟨1021544, by rfl⟩ : syracuseStep 1362059 = 2043089) B2043089
theorem B1362113 : Blo 603293 1362113 := bstep (se 2 (by rfl) ⟨510792, by rfl⟩ : syracuseStep 1362113 = 1021585) B1021585
theorem B6539525 : Blo 603293 6539525 := bstep (se 4 (by rfl) ⟨613080, by rfl⟩ : syracuseStep 6539525 = 1226161) B1226161
theorem B2214161 : Blo 603293 2214161 := bstep (se 2 (by rfl) ⟨830310, by rfl⟩ : syracuseStep 2214161 = 1660621) B1660621
theorem B1362329 : Blo 603293 1362329 := bstep (se 2 (by rfl) ⟨510873, by rfl⟩ : syracuseStep 1362329 = 1021747) B1021747
theorem B1296857 : Blo 603293 1296857 := bstep (se 2 (by rfl) ⟨486321, by rfl⟩ : syracuseStep 1296857 = 972643) B972643
theorem B1362419 : Blo 603293 1362419 := bstep (se 1 (by rfl) ⟨1021814, by rfl⟩ : syracuseStep 1362419 = 2043629) B2043629
theorem B1362455 : Blo 603293 1362455 := bstep (se 1 (by rfl) ⟨1021841, by rfl⟩ : syracuseStep 1362455 = 2043683) B2043683
theorem B1362635 : Blo 603293 1362635 := bstep (se 1 (by rfl) ⟨1021976, by rfl⟩ : syracuseStep 1362635 = 2043953) B2043953
theorem B19942129 : Blo 603293 19942129 := bstep (se 2 (by rfl) ⟨7478298, by rfl⟩ : syracuseStep 19942129 = 14956597) B14956597
theorem B1362689 : Blo 603293 1362689 := bstep (se 2 (by rfl) ⟨511008, by rfl⟩ : syracuseStep 1362689 = 1022017) B1022017
theorem B1362905 : Blo 603293 1362905 := bstep (se 2 (by rfl) ⟨511089, by rfl⟩ : syracuseStep 1362905 = 1022179) B1022179
theorem B1362995 : Blo 603293 1362995 := bstep (se 1 (by rfl) ⟨1022246, by rfl⟩ : syracuseStep 1362995 = 2044493) B2044493
theorem B1363031 : Blo 603293 1363031 := bstep (se 1 (by rfl) ⟨1022273, by rfl⟩ : syracuseStep 1363031 = 2044547) B2044547
theorem B1363211 : Blo 603293 1363211 := bstep (se 1 (by rfl) ⟨1022408, by rfl⟩ : syracuseStep 1363211 = 2044817) B2044817
theorem B1363265 : Blo 603293 1363265 := bstep (se 2 (by rfl) ⟨511224, by rfl⟩ : syracuseStep 1363265 = 1022449) B1022449
theorem B871831 : Blo 603293 871831 := bstep (se 1 (by rfl) ⟨653873, by rfl⟩ : syracuseStep 871831 = 1307747) B1307747
theorem B1363481 : Blo 603293 1363481 := bstep (se 2 (by rfl) ⟨511305, by rfl⟩ : syracuseStep 1363481 = 1022611) B1022611
theorem B1363571 : Blo 603293 1363571 := bstep (se 1 (by rfl) ⟨1022678, by rfl⟩ : syracuseStep 1363571 = 2045357) B2045357
theorem B1363607 : Blo 603293 1363607 := bstep (se 1 (by rfl) ⟨1022705, by rfl⟩ : syracuseStep 1363607 = 2045411) B2045411
theorem B904985 : Blo 603293 904985 := bstep (se 2 (by rfl) ⟨339369, by rfl⟩ : syracuseStep 904985 = 678739) B678739
theorem B1363787 : Blo 603293 1363787 := bstep (se 1 (by rfl) ⟨1022840, by rfl⟩ : syracuseStep 1363787 = 2045681) B2045681
theorem B16568165 : Blo 603293 16568165 := bstep (se 4 (by rfl) ⟨1553265, by rfl⟩ : syracuseStep 16568165 = 3106531) B3106531
theorem B1363841 : Blo 603293 1363841 := bstep (se 2 (by rfl) ⟨511440, by rfl⟩ : syracuseStep 1363841 = 1022881) B1022881
theorem B905099 : Blo 603293 905099 := bstep (se 1 (by rfl) ⟨678824, by rfl⟩ : syracuseStep 905099 = 1357649) B1357649
theorem B905111 : Blo 603293 905111 := bstep (se 1 (by rfl) ⟨678833, by rfl⟩ : syracuseStep 905111 = 1357667) B1357667
theorem B1527731 : Blo 603293 1527731 := bstep (se 1 (by rfl) ⟨1145798, by rfl⟩ : syracuseStep 1527731 = 2291597) B2291597
theorem B905177 : Blo 603293 905177 := bstep (se 2 (by rfl) ⟨339441, by rfl⟩ : syracuseStep 905177 = 678883) B678883
theorem B6279185 : Blo 603293 6279185 := bstep (se 2 (by rfl) ⟨2354694, by rfl⟩ : syracuseStep 6279185 = 4709389) B4709389
theorem B905291 : Blo 603293 905291 := bstep (se 1 (by rfl) ⟨678968, by rfl⟩ : syracuseStep 905291 = 1357937) B1357937
theorem B905303 : Blo 603293 905303 := bstep (se 1 (by rfl) ⟨678977, by rfl⟩ : syracuseStep 905303 = 1357955) B1357955
theorem B1364057 : Blo 603293 1364057 := bstep (se 2 (by rfl) ⟨511521, by rfl⟩ : syracuseStep 1364057 = 1023043) B1023043
theorem B905369 : Blo 603293 905369 := bstep (se 2 (by rfl) ⟨339513, by rfl⟩ : syracuseStep 905369 = 679027) B679027
theorem B1364147 : Blo 603293 1364147 := bstep (se 1 (by rfl) ⟨1023110, by rfl⟩ : syracuseStep 1364147 = 2046221) B2046221
theorem B1364183 : Blo 603293 1364183 := bstep (se 1 (by rfl) ⟨1023137, by rfl⟩ : syracuseStep 1364183 = 2046275) B2046275
theorem B905483 : Blo 603293 905483 := bstep (se 1 (by rfl) ⟨679112, by rfl⟩ : syracuseStep 905483 = 1358225) B1358225
theorem B905495 : Blo 603293 905495 := bstep (se 1 (by rfl) ⟨679121, by rfl⟩ : syracuseStep 905495 = 1358243) B1358243
theorem B1724723 : Blo 603293 1724723 := bstep (se 1 (by rfl) ⟨1293542, by rfl⟩ : syracuseStep 1724723 = 2587085) B2587085
theorem B8278337 : Blo 603293 8278337 := bstep (se 2 (by rfl) ⟨3104376, by rfl⟩ : syracuseStep 8278337 = 6208753) B6208753
theorem B905561 : Blo 603293 905561 := bstep (se 2 (by rfl) ⟨339585, by rfl⟩ : syracuseStep 905561 = 679171) B679171
theorem B1364363 : Blo 603293 1364363 := bstep (se 1 (by rfl) ⟨1023272, by rfl⟩ : syracuseStep 1364363 = 2046545) B2046545
theorem B1364417 : Blo 603293 1364417 := bstep (se 2 (by rfl) ⟨511656, by rfl⟩ : syracuseStep 1364417 = 1023313) B1023313
theorem B1528267 : Blo 603293 1528267 := bstep (se 1 (by rfl) ⟨1146200, by rfl⟩ : syracuseStep 1528267 = 2292401) B2292401
theorem B905675 : Blo 603293 905675 := bstep (se 1 (by rfl) ⟨679256, by rfl⟩ : syracuseStep 905675 = 1358513) B1358513
theorem B905687 : Blo 603293 905687 := bstep (se 1 (by rfl) ⟨679265, by rfl⟩ : syracuseStep 905687 = 1358531) B1358531
theorem B12440081 : Blo 603293 12440081 := bstep (se 2 (by rfl) ⟨4665030, by rfl⟩ : syracuseStep 12440081 = 9330061) B9330061
theorem B1724951 : Blo 603293 1724951 := bstep (se 1 (by rfl) ⟨1293713, by rfl⟩ : syracuseStep 1724951 = 2587427) B2587427
theorem B905753 : Blo 603293 905753 := bstep (se 2 (by rfl) ⟨339657, by rfl⟩ : syracuseStep 905753 = 679315) B679315
theorem B1528409 : Blo 603293 1528409 := bstep (se 2 (by rfl) ⟨573153, by rfl⟩ : syracuseStep 1528409 = 1146307) B1146307
theorem B905867 : Blo 603293 905867 := bstep (se 1 (by rfl) ⟨679400, by rfl⟩ : syracuseStep 905867 = 1358801) B1358801
theorem B905879 : Blo 603293 905879 := bstep (se 1 (by rfl) ⟨679409, by rfl⟩ : syracuseStep 905879 = 1358819) B1358819
theorem B1364633 : Blo 603293 1364633 := bstep (se 2 (by rfl) ⟨511737, by rfl⟩ : syracuseStep 1364633 = 1023475) B1023475
theorem B905945 : Blo 603293 905945 := bstep (se 2 (by rfl) ⟨339729, by rfl⟩ : syracuseStep 905945 = 679459) B679459
theorem B1364723 : Blo 603293 1364723 := bstep (se 1 (by rfl) ⟨1023542, by rfl⟩ : syracuseStep 1364723 = 2047085) B2047085
theorem B1364759 : Blo 603293 1364759 := bstep (se 1 (by rfl) ⟨1023569, by rfl⟩ : syracuseStep 1364759 = 2047139) B2047139
theorem B2446145 : Blo 603293 2446145 := bstep (se 2 (by rfl) ⟨917304, by rfl⟩ : syracuseStep 2446145 = 1834609) B1834609
theorem B906059 : Blo 603293 906059 := bstep (se 1 (by rfl) ⟨679544, by rfl⟩ : syracuseStep 906059 = 1359089) B1359089
theorem B1725259 : Blo 603293 1725259 := bstep (se 1 (by rfl) ⟨1293944, by rfl⟩ : syracuseStep 1725259 = 2587889) B2587889
theorem B906071 : Blo 603293 906071 := bstep (se 1 (by rfl) ⟨679553, by rfl⟩ : syracuseStep 906071 = 1359107) B1359107
theorem B3265373 : Blo 603293 3265373 := bstep (se 3 (by rfl) ⟨612257, by rfl⟩ : syracuseStep 3265373 = 1224515) B1224515
theorem B3068765 : Blo 603293 3068765 := bstep (se 3 (by rfl) ⟨575393, by rfl⟩ : syracuseStep 3068765 = 1150787) B1150787
theorem B906137 : Blo 603293 906137 := bstep (se 2 (by rfl) ⟨339801, by rfl⟩ : syracuseStep 906137 = 679603) B679603
theorem B1364939 : Blo 603293 1364939 := bstep (se 1 (by rfl) ⟨1023704, by rfl⟩ : syracuseStep 1364939 = 2047409) B2047409
theorem B1364993 : Blo 603293 1364993 := bstep (se 2 (by rfl) ⟨511872, by rfl⟩ : syracuseStep 1364993 = 1023745) B1023745
theorem B906251 : Blo 603293 906251 := bstep (se 1 (by rfl) ⟨679688, by rfl⟩ : syracuseStep 906251 = 1359377) B1359377
theorem B906263 : Blo 603293 906263 := bstep (se 1 (by rfl) ⟨679697, by rfl⟩ : syracuseStep 906263 = 1359395) B1359395
theorem B906329 : Blo 603293 906329 := bstep (se 2 (by rfl) ⟨339873, by rfl⟩ : syracuseStep 906329 = 679747) B679747
theorem B1725533 : Blo 603293 1725533 := bstep (se 3 (by rfl) ⟨323537, by rfl⟩ : syracuseStep 1725533 = 647075) B647075
theorem B906443 : Blo 603293 906443 := bstep (se 1 (by rfl) ⟨679832, by rfl⟩ : syracuseStep 906443 = 1359665) B1359665
theorem B644311 : Blo 603293 644311 := bstep (se 1 (by rfl) ⟨483233, by rfl⟩ : syracuseStep 644311 = 966467) B966467
theorem B906455 : Blo 603293 906455 := bstep (se 1 (by rfl) ⟨679841, by rfl⟩ : syracuseStep 906455 = 1359683) B1359683
theorem B1365209 : Blo 603293 1365209 := bstep (se 2 (by rfl) ⟨511953, by rfl⟩ : syracuseStep 1365209 = 1023907) B1023907
theorem B906521 : Blo 603293 906521 := bstep (se 2 (by rfl) ⟨339945, by rfl⟩ : syracuseStep 906521 = 679891) B679891
theorem B1365299 : Blo 603293 1365299 := bstep (se 1 (by rfl) ⟨1023974, by rfl⟩ : syracuseStep 1365299 = 2047949) B2047949
theorem B1365335 : Blo 603293 1365335 := bstep (se 1 (by rfl) ⟨1024001, by rfl⟩ : syracuseStep 1365335 = 2048003) B2048003
theorem B7853429 : Blo 603293 7853429 := bstep (se 5 (by rfl) ⟨368129, by rfl⟩ : syracuseStep 7853429 = 736259) B736259
theorem B906635 : Blo 603293 906635 := bstep (se 1 (by rfl) ⟨679976, by rfl⟩ : syracuseStep 906635 = 1359953) B1359953
theorem B1529239 : Blo 603293 1529239 := bstep (se 1 (by rfl) ⟨1146929, by rfl⟩ : syracuseStep 1529239 = 2293859) B2293859
theorem B906647 : Blo 603293 906647 := bstep (se 1 (by rfl) ⟨679985, by rfl⟩ : syracuseStep 906647 = 1359971) B1359971
theorem B906713 : Blo 603293 906713 := bstep (se 2 (by rfl) ⟨340017, by rfl⟩ : syracuseStep 906713 = 680035) B680035
theorem B1365515 : Blo 603293 1365515 := bstep (se 1 (by rfl) ⟨1024136, by rfl⟩ : syracuseStep 1365515 = 2048273) B2048273
theorem B1365569 : Blo 603293 1365569 := bstep (se 2 (by rfl) ⟨512088, by rfl⟩ : syracuseStep 1365569 = 1024177) B1024177
theorem B906827 : Blo 603293 906827 := bstep (se 1 (by rfl) ⟨680120, by rfl⟩ : syracuseStep 906827 = 1360241) B1360241
theorem B906839 : Blo 603293 906839 := bstep (se 1 (by rfl) ⟨680129, by rfl⟩ : syracuseStep 906839 = 1360259) B1360259
theorem B906905 : Blo 603293 906905 := bstep (se 2 (by rfl) ⟨340089, by rfl⟩ : syracuseStep 906905 = 680179) B680179
theorem B907019 : Blo 603293 907019 := bstep (se 1 (by rfl) ⟨680264, by rfl⟩ : syracuseStep 907019 = 1360529) B1360529
theorem B907031 : Blo 603293 907031 := bstep (se 1 (by rfl) ⟨680273, by rfl⟩ : syracuseStep 907031 = 1360547) B1360547
theorem B1365785 : Blo 603293 1365785 := bstep (se 2 (by rfl) ⟨512169, by rfl⟩ : syracuseStep 1365785 = 1024339) B1024339
theorem B1529675 : Blo 603293 1529675 := bstep (se 1 (by rfl) ⟨1147256, by rfl⟩ : syracuseStep 1529675 = 2294513) B2294513
theorem B907097 : Blo 603293 907097 := bstep (se 2 (by rfl) ⟨340161, by rfl⟩ : syracuseStep 907097 = 680323) B680323
theorem B1365875 : Blo 603293 1365875 := bstep (se 1 (by rfl) ⟨1024406, by rfl⟩ : syracuseStep 1365875 = 2048813) B2048813
theorem B1365911 : Blo 603293 1365911 := bstep (se 1 (by rfl) ⟨1024433, by rfl⟩ : syracuseStep 1365911 = 2048867) B2048867
theorem B907211 : Blo 603293 907211 := bstep (se 1 (by rfl) ⟨680408, by rfl⟩ : syracuseStep 907211 = 1360817) B1360817
theorem B907223 : Blo 603293 907223 := bstep (se 1 (by rfl) ⟨680417, by rfl⟩ : syracuseStep 907223 = 1360835) B1360835
theorem B645131 : Blo 603293 645131 := bstep (se 1 (by rfl) ⟨483848, by rfl⟩ : syracuseStep 645131 = 967697) B967697
theorem B1038359 : Blo 603293 1038359 := bstep (se 1 (by rfl) ⟨778769, by rfl⟩ : syracuseStep 1038359 = 1557539) B1557539
theorem B907289 : Blo 603293 907289 := bstep (se 2 (by rfl) ⟨340233, by rfl⟩ : syracuseStep 907289 = 680467) B680467
theorem B1366091 : Blo 603293 1366091 := bstep (se 1 (by rfl) ⟨1024568, by rfl⟩ : syracuseStep 1366091 = 2049137) B2049137
theorem B2021465 : Blo 603293 2021465 := bstep (se 2 (by rfl) ⟨758049, by rfl⟩ : syracuseStep 2021465 = 1516099) B1516099
theorem B1038425 : Blo 603293 1038425 := bstep (se 2 (by rfl) ⟨389409, by rfl⟩ : syracuseStep 1038425 = 778819) B778819
theorem B1366145 : Blo 603293 1366145 := bstep (se 2 (by rfl) ⟨512304, by rfl⟩ : syracuseStep 1366145 = 1024609) B1024609
theorem B2906243 : Blo 603293 2906243 := bstep (se 1 (by rfl) ⟨2179682, by rfl⟩ : syracuseStep 2906243 = 4359365) B4359365
theorem B907403 : Blo 603293 907403 := bstep (se 1 (by rfl) ⟨680552, by rfl⟩ : syracuseStep 907403 = 1361105) B1361105
theorem B907415 : Blo 603293 907415 := bstep (se 1 (by rfl) ⟨680561, by rfl⟩ : syracuseStep 907415 = 1361123) B1361123
theorem B1530049 : Blo 603293 1530049 := bstep (se 2 (by rfl) ⟨573768, by rfl⟩ : syracuseStep 1530049 = 1147537) B1147537
theorem B907481 : Blo 603293 907481 := bstep (se 2 (by rfl) ⟨340305, by rfl⟩ : syracuseStep 907481 = 680611) B680611
theorem B612631 : Blo 603293 612631 := bstep (se 1 (by rfl) ⟨459473, by rfl⟩ : syracuseStep 612631 = 918947) B918947
theorem B907595 : Blo 603293 907595 := bstep (se 1 (by rfl) ⟨680696, by rfl⟩ : syracuseStep 907595 = 1361393) B1361393
theorem B907607 : Blo 603293 907607 := bstep (se 1 (by rfl) ⟨680705, by rfl⟩ : syracuseStep 907607 = 1361411) B1361411
theorem B1366361 : Blo 603293 1366361 := bstep (se 2 (by rfl) ⟨512385, by rfl⟩ : syracuseStep 1366361 = 1024771) B1024771
theorem B907673 : Blo 603293 907673 := bstep (se 2 (by rfl) ⟨340377, by rfl⟩ : syracuseStep 907673 = 680755) B680755
theorem B907787 : Blo 603293 907787 := bstep (se 1 (by rfl) ⟨680840, by rfl⟩ : syracuseStep 907787 = 1361681) B1361681
theorem B907799 : Blo 603293 907799 := bstep (se 1 (by rfl) ⟨680849, by rfl⟩ : syracuseStep 907799 = 1361699) B1361699
theorem B907865 : Blo 603293 907865 := bstep (se 2 (by rfl) ⟨340449, by rfl⟩ : syracuseStep 907865 = 680899) B680899
theorem B907979 : Blo 603293 907979 := bstep (se 1 (by rfl) ⟨680984, by rfl⟩ : syracuseStep 907979 = 1361969) B1361969
theorem B907991 : Blo 603293 907991 := bstep (se 1 (by rfl) ⟨680993, by rfl⟩ : syracuseStep 907991 = 1361987) B1361987
theorem B1530647 : Blo 603293 1530647 := bstep (se 1 (by rfl) ⟨1147985, by rfl⟩ : syracuseStep 1530647 = 2295971) B2295971
theorem B908057 : Blo 603293 908057 := bstep (se 2 (by rfl) ⟨340521, by rfl⟩ : syracuseStep 908057 = 681043) B681043
theorem B4414283 : Blo 603293 4414283 := bstep (se 1 (by rfl) ⟨3310712, by rfl⟩ : syracuseStep 4414283 = 6621425) B6621425
theorem B2579293 : Blo 603293 2579293 := bstep (se 3 (by rfl) ⟨483617, by rfl⟩ : syracuseStep 2579293 = 967235) B967235
theorem B678775 : Blo 603293 678775 := bstep (se 1 (by rfl) ⟨509081, by rfl⟩ : syracuseStep 678775 = 1018163) B1018163
theorem B908171 : Blo 603293 908171 := bstep (se 1 (by rfl) ⟨681128, by rfl⟩ : syracuseStep 908171 = 1362257) B1362257
theorem B908183 : Blo 603293 908183 := bstep (se 1 (by rfl) ⟨681137, by rfl⟩ : syracuseStep 908183 = 1362275) B1362275
theorem B3070871 : Blo 603293 3070871 := bstep (se 1 (by rfl) ⟨2303153, by rfl⟩ : syracuseStep 3070871 = 4606307) B4606307
theorem B908249 : Blo 603293 908249 := bstep (se 2 (by rfl) ⟨340593, by rfl⟩ : syracuseStep 908249 = 681187) B681187
theorem B678955 : Blo 603293 678955 := bstep (se 1 (by rfl) ⟨509216, by rfl⟩ : syracuseStep 678955 = 1018433) B1018433
theorem B908363 : Blo 603293 908363 := bstep (se 1 (by rfl) ⟨681272, by rfl⟩ : syracuseStep 908363 = 1362545) B1362545
theorem B908375 : Blo 603293 908375 := bstep (se 1 (by rfl) ⟨681281, by rfl⟩ : syracuseStep 908375 = 1362563) B1362563
theorem B679063 : Blo 603293 679063 := bstep (se 1 (by rfl) ⟨509297, by rfl⟩ : syracuseStep 679063 = 1018595) B1018595
theorem B1727639 : Blo 603293 1727639 := bstep (se 1 (by rfl) ⟨1295729, by rfl⟩ : syracuseStep 1727639 = 2591459) B2591459
theorem B908441 : Blo 603293 908441 := bstep (se 2 (by rfl) ⟨340665, by rfl⟩ : syracuseStep 908441 = 681331) B681331
theorem B646327 : Blo 603293 646327 := bstep (se 1 (by rfl) ⟨484745, by rfl⟩ : syracuseStep 646327 = 969491) B969491
theorem B908555 : Blo 603293 908555 := bstep (se 1 (by rfl) ⟨681416, by rfl⟩ : syracuseStep 908555 = 1362833) B1362833
theorem B908567 : Blo 603293 908567 := bstep (se 1 (by rfl) ⟨681425, by rfl⟩ : syracuseStep 908567 = 1362851) B1362851
theorem B679243 : Blo 603293 679243 := bstep (se 1 (by rfl) ⟨509432, by rfl⟩ : syracuseStep 679243 = 1018865) B1018865
theorem B908633 : Blo 603293 908633 := bstep (se 2 (by rfl) ⟨340737, by rfl⟩ : syracuseStep 908633 = 681475) B681475
theorem B875929 : Blo 603293 875929 := bstep (se 2 (by rfl) ⟨328473, by rfl⟩ : syracuseStep 875929 = 656947) B656947
theorem B679351 : Blo 603293 679351 := bstep (se 1 (by rfl) ⟨509513, by rfl⟩ : syracuseStep 679351 = 1019027) B1019027
theorem B908747 : Blo 603293 908747 := bstep (se 1 (by rfl) ⟨681560, by rfl⟩ : syracuseStep 908747 = 1363121) B1363121
theorem B908759 : Blo 603293 908759 := bstep (se 1 (by rfl) ⟨681569, by rfl⟩ : syracuseStep 908759 = 1363139) B1363139
theorem B908825 : Blo 603293 908825 := bstep (se 2 (by rfl) ⟨340809, by rfl⟩ : syracuseStep 908825 = 681619) B681619
theorem B646699 : Blo 603293 646699 := bstep (se 1 (by rfl) ⟨485024, by rfl⟩ : syracuseStep 646699 = 970049) B970049
theorem B1531457 : Blo 603293 1531457 := bstep (se 2 (by rfl) ⟨574296, by rfl⟩ : syracuseStep 1531457 = 1148593) B1148593
theorem B4349533 : Blo 603293 4349533 := bstep (se 3 (by rfl) ⟨815537, by rfl⟩ : syracuseStep 4349533 = 1631075) B1631075
theorem B679531 : Blo 603293 679531 := bstep (se 1 (by rfl) ⟨509648, by rfl⟩ : syracuseStep 679531 = 1019297) B1019297
theorem B5168771 : Blo 603293 5168771 := bstep (se 1 (by rfl) ⟨3876578, by rfl⟩ : syracuseStep 5168771 = 7753157) B7753157
theorem B908939 : Blo 603293 908939 := bstep (se 1 (by rfl) ⟨681704, by rfl⟩ : syracuseStep 908939 = 1363409) B1363409
theorem B2580113 : Blo 603293 2580113 := bstep (se 2 (by rfl) ⟨967542, by rfl⟩ : syracuseStep 2580113 = 1935085) B1935085
theorem B908951 : Blo 603293 908951 := bstep (se 1 (by rfl) ⟨681713, by rfl⟩ : syracuseStep 908951 = 1363427) B1363427
theorem B679639 : Blo 603293 679639 := bstep (se 1 (by rfl) ⟨509729, by rfl⟩ : syracuseStep 679639 = 1019459) B1019459
theorem B909017 : Blo 603293 909017 := bstep (se 2 (by rfl) ⟨340881, by rfl⟩ : syracuseStep 909017 = 681763) B681763
theorem B909131 : Blo 603293 909131 := bstep (se 1 (by rfl) ⟨681848, by rfl⟩ : syracuseStep 909131 = 1363697) B1363697
theorem B909143 : Blo 603293 909143 := bstep (se 1 (by rfl) ⟨681857, by rfl⟩ : syracuseStep 909143 = 1363715) B1363715
theorem B679819 : Blo 603293 679819 := bstep (se 1 (by rfl) ⟨509864, by rfl⟩ : syracuseStep 679819 = 1019729) B1019729
theorem B909209 : Blo 603293 909209 := bstep (se 2 (by rfl) ⟨340953, by rfl⟩ : syracuseStep 909209 = 681907) B681907
theorem B6873011 : Blo 603293 6873011 := bstep (se 1 (by rfl) ⟨5154758, by rfl⟩ : syracuseStep 6873011 = 10309517) B10309517
theorem B1728449 : Blo 603293 1728449 := bstep (se 2 (by rfl) ⟨648168, by rfl⟩ : syracuseStep 1728449 = 1296337) B1296337
theorem B647147 : Blo 603293 647147 := bstep (se 1 (by rfl) ⟨485360, by rfl⟩ : syracuseStep 647147 = 970721) B970721
theorem B679927 : Blo 603293 679927 := bstep (se 1 (by rfl) ⟨509945, by rfl⟩ : syracuseStep 679927 = 1019891) B1019891
theorem B909323 : Blo 603293 909323 := bstep (se 1 (by rfl) ⟨681992, by rfl⟩ : syracuseStep 909323 = 1363985) B1363985
theorem B909335 : Blo 603293 909335 := bstep (se 1 (by rfl) ⟨682001, by rfl⟩ : syracuseStep 909335 = 1364003) B1364003
theorem B1531993 : Blo 603293 1531993 := bstep (se 2 (by rfl) ⟨574497, by rfl⟩ : syracuseStep 1531993 = 1148995) B1148995
theorem B909401 : Blo 603293 909401 := bstep (se 2 (by rfl) ⟨341025, by rfl⟩ : syracuseStep 909401 = 682051) B682051
theorem B680107 : Blo 603293 680107 := bstep (se 1 (by rfl) ⟨510080, by rfl⟩ : syracuseStep 680107 = 1020161) B1020161
theorem B5234867 : Blo 603293 5234867 := bstep (se 1 (by rfl) ⟨3926150, by rfl⟩ : syracuseStep 5234867 = 7852301) B7852301
theorem B2449601 : Blo 603293 2449601 := bstep (se 2 (by rfl) ⟨918600, by rfl⟩ : syracuseStep 2449601 = 1837201) B1837201
theorem B909515 : Blo 603293 909515 := bstep (se 1 (by rfl) ⟨682136, by rfl⟩ : syracuseStep 909515 = 1364273) B1364273
theorem B909527 : Blo 603293 909527 := bstep (se 1 (by rfl) ⟨682145, by rfl⟩ : syracuseStep 909527 = 1364291) B1364291
theorem B680215 : Blo 603293 680215 := bstep (se 1 (by rfl) ⟨510161, by rfl⟩ : syracuseStep 680215 = 1020323) B1020323
theorem B909593 : Blo 603293 909593 := bstep (se 2 (by rfl) ⟨341097, by rfl⟩ : syracuseStep 909593 = 682195) B682195
theorem B2580781 : Blo 603293 2580781 := bstep (se 3 (by rfl) ⟨483896, by rfl⟩ : syracuseStep 2580781 = 967793) B967793
theorem B909707 : Blo 603293 909707 := bstep (se 1 (by rfl) ⟨682280, by rfl⟩ : syracuseStep 909707 = 1364561) B1364561
theorem B909719 : Blo 603293 909719 := bstep (se 1 (by rfl) ⟨682289, by rfl⟩ : syracuseStep 909719 = 1364579) B1364579
theorem B680395 : Blo 603293 680395 := bstep (se 1 (by rfl) ⟨510296, by rfl⟩ : syracuseStep 680395 = 1020593) B1020593
theorem B909785 : Blo 603293 909785 := bstep (se 2 (by rfl) ⟨341169, by rfl⟩ : syracuseStep 909785 = 682339) B682339
theorem B680503 : Blo 603293 680503 := bstep (se 1 (by rfl) ⟨510377, by rfl⟩ : syracuseStep 680503 = 1020755) B1020755
theorem B909899 : Blo 603293 909899 := bstep (se 1 (by rfl) ⟨682424, by rfl⟩ : syracuseStep 909899 = 1364849) B1364849
theorem B909911 : Blo 603293 909911 := bstep (se 1 (by rfl) ⟨682433, by rfl⟩ : syracuseStep 909911 = 1364867) B1364867
theorem B909977 : Blo 603293 909977 := bstep (se 2 (by rfl) ⟨341241, by rfl⟩ : syracuseStep 909977 = 682483) B682483
theorem B680683 : Blo 603293 680683 := bstep (se 1 (by rfl) ⟨510512, by rfl⟩ : syracuseStep 680683 = 1021025) B1021025
theorem B910091 : Blo 603293 910091 := bstep (se 1 (by rfl) ⟨682568, by rfl⟩ : syracuseStep 910091 = 1365137) B1365137
theorem B910103 : Blo 603293 910103 := bstep (se 1 (by rfl) ⟨682577, by rfl⟩ : syracuseStep 910103 = 1365155) B1365155
theorem B2908973 : Blo 603293 2908973 := bstep (se 3 (by rfl) ⟨545432, by rfl⟩ : syracuseStep 2908973 = 1090865) B1090865
theorem B680791 : Blo 603293 680791 := bstep (se 1 (by rfl) ⟨510593, by rfl⟩ : syracuseStep 680791 = 1021187) B1021187
theorem B910169 : Blo 603293 910169 := bstep (se 2 (by rfl) ⟨341313, by rfl⟩ : syracuseStep 910169 = 682627) B682627
theorem B2581379 : Blo 603293 2581379 := bstep (se 1 (by rfl) ⟨1936034, by rfl⟩ : syracuseStep 2581379 = 3872069) B3872069
theorem B910283 : Blo 603293 910283 := bstep (se 1 (by rfl) ⟨682712, by rfl⟩ : syracuseStep 910283 = 1365425) B1365425
theorem B910295 : Blo 603293 910295 := bstep (se 1 (by rfl) ⟨682721, by rfl⟩ : syracuseStep 910295 = 1365443) B1365443
theorem B680971 : Blo 603293 680971 := bstep (se 1 (by rfl) ⟨510728, by rfl⟩ : syracuseStep 680971 = 1021457) B1021457
theorem B910361 : Blo 603293 910361 := bstep (se 2 (by rfl) ⟨341385, by rfl⟩ : syracuseStep 910361 = 682771) B682771
theorem B681079 : Blo 603293 681079 := bstep (se 1 (by rfl) ⟨510809, by rfl⟩ : syracuseStep 681079 = 1021619) B1021619
theorem B910475 : Blo 603293 910475 := bstep (se 1 (by rfl) ⟨682856, by rfl⟩ : syracuseStep 910475 = 1365713) B1365713
theorem B910487 : Blo 603293 910487 := bstep (se 1 (by rfl) ⟨682865, by rfl⟩ : syracuseStep 910487 = 1365731) B1365731
theorem B648343 : Blo 603293 648343 := bstep (se 1 (by rfl) ⟨486257, by rfl⟩ : syracuseStep 648343 = 972515) B972515
theorem B1533107 : Blo 603293 1533107 := bstep (se 1 (by rfl) ⟨1149830, by rfl⟩ : syracuseStep 1533107 = 2299661) B2299661
theorem B910553 : Blo 603293 910553 := bstep (se 2 (by rfl) ⟨341457, by rfl⟩ : syracuseStep 910553 = 682915) B682915
theorem B681259 : Blo 603293 681259 := bstep (se 1 (by rfl) ⟨510944, by rfl⟩ : syracuseStep 681259 = 1021889) B1021889
theorem B910667 : Blo 603293 910667 := bstep (se 1 (by rfl) ⟨683000, by rfl⟩ : syracuseStep 910667 = 1366001) B1366001
theorem B910679 : Blo 603293 910679 := bstep (se 1 (by rfl) ⟨683009, by rfl⟩ : syracuseStep 910679 = 1366019) B1366019
theorem B6874469 : Blo 603293 6874469 := bstep (se 4 (by rfl) ⟨644481, by rfl⟩ : syracuseStep 6874469 = 1288963) B1288963
theorem B681367 : Blo 603293 681367 := bstep (se 1 (by rfl) ⟨511025, by rfl⟩ : syracuseStep 681367 = 1022051) B1022051
theorem B910745 : Blo 603293 910745 := bstep (se 2 (by rfl) ⟨341529, by rfl⟩ : syracuseStep 910745 = 683059) B683059
theorem B1533401 : Blo 603293 1533401 := bstep (se 2 (by rfl) ⟨575025, by rfl⟩ : syracuseStep 1533401 = 1150051) B1150051
theorem B910859 : Blo 603293 910859 := bstep (se 1 (by rfl) ⟨683144, by rfl⟩ : syracuseStep 910859 = 1366289) B1366289
theorem B910871 : Blo 603293 910871 := bstep (se 1 (by rfl) ⟨683153, by rfl⟩ : syracuseStep 910871 = 1366307) B1366307
theorem B681547 : Blo 603293 681547 := bstep (se 1 (by rfl) ⟨511160, by rfl⟩ : syracuseStep 681547 = 1022321) B1022321
theorem B910937 : Blo 603293 910937 := bstep (se 2 (by rfl) ⟨341601, by rfl⟩ : syracuseStep 910937 = 683203) B683203
theorem B681655 : Blo 603293 681655 := bstep (se 1 (by rfl) ⟨511241, by rfl⟩ : syracuseStep 681655 = 1022483) B1022483
theorem B1402625 : Blo 603293 1402625 := bstep (se 2 (by rfl) ⟨525984, by rfl⟩ : syracuseStep 1402625 = 1051969) B1051969
theorem B681835 : Blo 603293 681835 := bstep (se 1 (by rfl) ⟨511376, by rfl⟩ : syracuseStep 681835 = 1022753) B1022753
theorem B681943 : Blo 603293 681943 := bstep (se 1 (by rfl) ⟨511457, by rfl⟩ : syracuseStep 681943 = 1022915) B1022915
theorem B5171161 : Blo 603293 5171161 := bstep (se 2 (by rfl) ⟨1939185, by rfl⟩ : syracuseStep 5171161 = 3878371) B3878371
theorem B682123 : Blo 603293 682123 := bstep (se 1 (by rfl) ⟨511592, by rfl⟩ : syracuseStep 682123 = 1023185) B1023185
theorem B682231 : Blo 603293 682231 := bstep (se 1 (by rfl) ⟨511673, by rfl⟩ : syracuseStep 682231 = 1023347) B1023347
theorem B682411 : Blo 603293 682411 := bstep (se 1 (by rfl) ⟨511808, by rfl⟩ : syracuseStep 682411 = 1023617) B1023617
theorem B682519 : Blo 603293 682519 := bstep (se 1 (by rfl) ⟨511889, by rfl⟩ : syracuseStep 682519 = 1023779) B1023779
theorem B682699 : Blo 603293 682699 := bstep (se 1 (by rfl) ⟨512024, by rfl⟩ : syracuseStep 682699 = 1024049) B1024049
theorem B682807 : Blo 603293 682807 := bstep (se 1 (by rfl) ⟨512105, by rfl⟩ : syracuseStep 682807 = 1024211) B1024211
theorem B5172119 : Blo 603293 5172119 := bstep (se 1 (by rfl) ⟨3879089, by rfl⟩ : syracuseStep 5172119 = 7758179) B7758179
theorem B682987 : Blo 603293 682987 := bstep (se 1 (by rfl) ⟨512240, by rfl⟩ : syracuseStep 682987 = 1024481) B1024481
theorem B1535051 : Blo 603293 1535051 := bstep (se 1 (by rfl) ⟨1151288, by rfl⟩ : syracuseStep 1535051 = 2302577) B2302577
theorem B683095 : Blo 603293 683095 := bstep (se 1 (by rfl) ⟨512321, by rfl⟩ : syracuseStep 683095 = 1024643) B1024643
theorem B4582493 : Blo 603293 4582493 := bstep (se 3 (by rfl) ⟨859217, by rfl⟩ : syracuseStep 4582493 = 1718435) B1718435
theorem B3271859 : Blo 603293 3271859 := bstep (se 1 (by rfl) ⟨2453894, by rfl⟩ : syracuseStep 3271859 = 4907789) B4907789
theorem B5172497 : Blo 603293 5172497 := bstep (se 2 (by rfl) ⟨1939686, by rfl⟩ : syracuseStep 5172497 = 3879373) B3879373
theorem B1536023 : Blo 603293 1536023 := bstep (se 1 (by rfl) ⟨1152017, by rfl⟩ : syracuseStep 1536023 = 2304035) B2304035
theorem B24899885 : Blo 603293 24899885 := bstep (se 3 (by rfl) ⟨4668728, by rfl⟩ : syracuseStep 24899885 = 9337457) B9337457
theorem B1536691 : Blo 603293 1536691 := bstep (se 1 (by rfl) ⟨1152518, by rfl⟩ : syracuseStep 1536691 = 2305037) B2305037
theorem B1307443 : Blo 603293 1307443 := bstep (se 1 (by rfl) ⟨980582, by rfl⟩ : syracuseStep 1307443 = 1961165) B1961165
theorem B1536833 : Blo 603293 1536833 := bstep (se 2 (by rfl) ⟨576312, by rfl⟩ : syracuseStep 1536833 = 1152625) B1152625
theorem B3438125 : Blo 603293 3438125 := bstep (se 3 (by rfl) ⟨644648, by rfl⟩ : syracuseStep 3438125 = 1289297) B1289297
theorem B1570379 : Blo 603293 1570379 := bstep (se 1 (by rfl) ⟨1177784, by rfl⟩ : syracuseStep 1570379 = 2355569) B2355569
theorem B2487901 : Blo 603293 2487901 := bstep (se 3 (by rfl) ⟨466481, by rfl⟩ : syracuseStep 2487901 = 932963) B932963
theorem B3274627 : Blo 603293 3274627 := bstep (se 1 (by rfl) ⟨2455970, by rfl⟩ : syracuseStep 3274627 = 4911941) B4911941
theorem B2291885 : Blo 603293 2291885 := bstep (se 3 (by rfl) ⟨429728, by rfl⟩ : syracuseStep 2291885 = 859457) B859457
theorem B2291915 : Blo 603293 2291915 := bstep (se 1 (by rfl) ⟨1718936, by rfl⟩ : syracuseStep 2291915 = 3437873) B3437873
theorem B4913369 : Blo 603293 4913369 := bstep (se 2 (by rfl) ⟨1842513, by rfl⟩ : syracuseStep 4913369 = 3685027) B3685027
theorem B3930443 : Blo 603293 3930443 := bstep (se 1 (by rfl) ⟨2947832, by rfl⟩ : syracuseStep 3930443 = 5895665) B5895665
theorem B1309043 : Blo 603293 1309043 := bstep (se 1 (by rfl) ⟨981782, by rfl⟩ : syracuseStep 1309043 = 1963565) B1963565
theorem B2587153 : Blo 603293 2587153 := bstep (se 2 (by rfl) ⟨970182, by rfl⟩ : syracuseStep 2587153 = 1940365) B1940365
theorem B1145495 : Blo 603293 1145495 := bstep (se 1 (by rfl) ⟨859121, by rfl⟩ : syracuseStep 1145495 = 1718243) B1718243
theorem B817879 : Blo 603293 817879 := bstep (se 1 (by rfl) ⟨613409, by rfl⟩ : syracuseStep 817879 = 1226819) B1226819
theorem B2292569 : Blo 603293 2292569 := bstep (se 2 (by rfl) ⟨859713, by rfl⟩ : syracuseStep 2292569 = 1719427) B1719427
theorem B818263 : Blo 603293 818263 := bstep (se 1 (by rfl) ⟨613697, by rfl⟩ : syracuseStep 818263 = 1227395) B1227395
theorem B2292887 : Blo 603293 2292887 := bstep (se 1 (by rfl) ⟨1719665, by rfl⟩ : syracuseStep 2292887 = 3439331) B3439331
theorem B1146163 : Blo 603293 1146163 := bstep (se 1 (by rfl) ⟨859622, by rfl⟩ : syracuseStep 1146163 = 1719245) B1719245
theorem B5045825 : Blo 603293 5045825 := bstep (se 2 (by rfl) ⟨1892184, by rfl⟩ : syracuseStep 5045825 = 3784369) B3784369
theorem B1375937 : Blo 603293 1375937 := bstep (se 2 (by rfl) ⟨515976, by rfl⟩ : syracuseStep 1375937 = 1031953) B1031953
theorem B1146611 : Blo 603293 1146611 := bstep (se 1 (by rfl) ⟨859958, by rfl⟩ : syracuseStep 1146611 = 1719917) B1719917
theorem B1146649 : Blo 603293 1146649 := bstep (se 2 (by rfl) ⟨429993, by rfl⟩ : syracuseStep 1146649 = 859987) B859987
theorem B2293555 : Blo 603293 2293555 := bstep (se 1 (by rfl) ⟨1720166, by rfl⟩ : syracuseStep 2293555 = 3440333) B3440333
theorem B3440515 : Blo 603293 3440515 := bstep (se 1 (by rfl) ⟨2580386, by rfl⟩ : syracuseStep 3440515 = 5160773) B5160773
theorem B3112921 : Blo 603293 3112921 := bstep (se 2 (by rfl) ⟨1167345, by rfl⟩ : syracuseStep 3112921 = 2334691) B2334691
theorem B1835095 : Blo 603293 1835095 := bstep (se 1 (by rfl) ⟨1376321, by rfl⟩ : syracuseStep 1835095 = 2752643) B2752643
theorem B1933703 : Blo 603293 1933703 := bstep (se 1 (by rfl) ⟨1450277, by rfl⟩ : syracuseStep 1933703 = 2900555) B2900555
theorem B3441041 : Blo 603293 3441041 := bstep (se 2 (by rfl) ⟨1290390, by rfl⟩ : syracuseStep 3441041 = 2580781) B2580781
theorem B1933753 : Blo 603293 1933753 := bstep (se 2 (by rfl) ⟨725157, by rfl⟩ : syracuseStep 1933753 = 1450315) B1450315
theorem B2294315 : Blo 603293 2294315 := bstep (se 1 (by rfl) ⟨1720736, by rfl⟩ : syracuseStep 2294315 = 3441473) B3441473
theorem B3670721 : Blo 603293 3670721 := bstep (se 2 (by rfl) ⟨1376520, by rfl⟩ : syracuseStep 3670721 = 2753041) B2753041
theorem B4588325 : Blo 603293 4588325 := bstep (se 4 (by rfl) ⟨430155, by rfl⟩ : syracuseStep 4588325 = 860311) B860311
theorem B3277721 : Blo 603293 3277721 := bstep (se 2 (by rfl) ⟨1229145, by rfl⟩ : syracuseStep 3277721 = 2458291) B2458291
theorem B11076533 : Blo 603293 11076533 := bstep (se 5 (by rfl) ⟨519212, by rfl⟩ : syracuseStep 11076533 = 1038425) B1038425
theorem B1148023 : Blo 603293 1148023 := bstep (se 1 (by rfl) ⟨861017, by rfl⟩ : syracuseStep 1148023 = 1722035) B1722035
theorem B820343 : Blo 603293 820343 := bstep (se 1 (by rfl) ⟨615257, by rfl⟩ : syracuseStep 820343 = 1230515) B1230515
theorem B2917853 : Blo 603293 2917853 := bstep (se 3 (by rfl) ⟨547097, by rfl⟩ : syracuseStep 2917853 = 1094195) B1094195
theorem B4359683 : Blo 603293 4359683 := bstep (se 1 (by rfl) ⟨3269762, by rfl⟩ : syracuseStep 4359683 = 6539525) B6539525
theorem B1476107 : Blo 603293 1476107 := bstep (se 1 (by rfl) ⟨1107080, by rfl⟩ : syracuseStep 1476107 = 2214161) B2214161
theorem B5802029 : Blo 603293 5802029 := bstep (se 3 (by rfl) ⟨1087880, by rfl⟩ : syracuseStep 5802029 = 2175761) B2175761
theorem B2754647 : Blo 603293 2754647 := bstep (se 1 (by rfl) ⟨2065985, by rfl⟩ : syracuseStep 2754647 = 4131971) B4131971
theorem B2591185 : Blo 603293 2591185 := bstep (se 2 (by rfl) ⟨971694, by rfl⟩ : syracuseStep 2591185 = 1943389) B1943389
theorem B11045443 : Blo 603293 11045443 := bstep (se 1 (by rfl) ⟨8284082, by rfl⟩ : syracuseStep 11045443 = 16568165) B16568165
theorem B6556261 : Blo 603293 6556261 := bstep (se 4 (by rfl) ⟨614649, by rfl⟩ : syracuseStep 6556261 = 1229299) B1229299
theorem B1018487 : Blo 603293 1018487 := bstep (se 1 (by rfl) ⟨763865, by rfl⟩ : syracuseStep 1018487 = 1527731) B1527731
theorem B1837939 : Blo 603293 1837939 := bstep (se 1 (by rfl) ⟨1378454, by rfl⟩ : syracuseStep 1837939 = 2756909) B2756909
theorem B4655987 : Blo 603293 4655987 := bstep (se 1 (by rfl) ⟨3491990, by rfl⟩ : syracuseStep 4655987 = 6983981) B6983981
theorem B1149815 : Blo 603293 1149815 := bstep (se 1 (by rfl) ⟨862361, by rfl⟩ : syracuseStep 1149815 = 1724723) B1724723
theorem B8293387 : Blo 603293 8293387 := bstep (se 1 (by rfl) ⟨6220040, by rfl⟩ : syracuseStep 8293387 = 12440081) B12440081
theorem B1149967 : Blo 603293 1149967 := bstep (se 1 (by rfl) ⟨862475, by rfl⟩ : syracuseStep 1149967 = 1724951) B1724951
theorem B1018939 : Blo 603293 1018939 := bstep (se 1 (by rfl) ⟨764204, by rfl⟩ : syracuseStep 1018939 = 1528409) B1528409
theorem B14027863 : Blo 603293 14027863 := bstep (se 1 (by rfl) ⟨10520897, by rfl⟩ : syracuseStep 14027863 = 21041795) B21041795
theorem B1019081 : Blo 603293 1019081 := bstep (se 2 (by rfl) ⟨382155, by rfl⟩ : syracuseStep 1019081 = 764311) B764311
theorem B1150355 : Blo 603293 1150355 := bstep (se 1 (by rfl) ⟨862766, by rfl⟩ : syracuseStep 1150355 = 1725533) B1725533
theorem B6655441 : Blo 603293 6655441 := bstep (se 2 (by rfl) ⟨2495790, by rfl⟩ : syracuseStep 6655441 = 4991581) B4991581
theorem B1019783 : Blo 603293 1019783 := bstep (se 1 (by rfl) ⟨764837, by rfl⟩ : syracuseStep 1019783 = 1529675) B1529675
theorem B2297747 : Blo 603293 2297747 := bstep (se 1 (by rfl) ⟨1723310, by rfl⟩ : syracuseStep 2297747 = 3446621) B3446621
theorem B692239 : Blo 603293 692239 := bstep (se 1 (by rfl) ⟨519179, by rfl⟩ : syracuseStep 692239 = 1038359) B1038359
theorem B2101277 : Blo 603293 2101277 := bstep (se 3 (by rfl) ⟨393989, by rfl⟩ : syracuseStep 2101277 = 787979) B787979
theorem B1347643 : Blo 603293 1347643 := bstep (se 1 (by rfl) ⟨1010732, by rfl⟩ : syracuseStep 1347643 = 2021465) B2021465
theorem B1937495 : Blo 603293 1937495 := bstep (se 1 (by rfl) ⟨1453121, by rfl⟩ : syracuseStep 1937495 = 2906243) B2906243
theorem B15470837 : Blo 603293 15470837 := bstep (se 5 (by rfl) ⟨725195, by rfl⟩ : syracuseStep 15470837 = 1450391) B1450391
theorem B1577249 : Blo 603293 1577249 := bstep (se 2 (by rfl) ⟨591468, by rfl⟩ : syracuseStep 1577249 = 1182937) B1182937
theorem B1020431 : Blo 603293 1020431 := bstep (se 1 (by rfl) ⟨765323, by rfl⟩ : syracuseStep 1020431 = 1530647) B1530647
theorem B19599893 : Blo 603293 19599893 := bstep (se 6 (by rfl) ⟨459372, by rfl⟩ : syracuseStep 19599893 = 918745) B918745
theorem B2036285 : Blo 603293 2036285 := bstep (se 3 (by rfl) ⟨381803, by rfl⟩ : syracuseStep 2036285 = 763607) B763607
theorem B1151759 : Blo 603293 1151759 := bstep (se 1 (by rfl) ⟨863819, by rfl⟩ : syracuseStep 1151759 = 1727639) B1727639
theorem B1020971 : Blo 603293 1020971 := bstep (se 1 (by rfl) ⟨765728, by rfl⟩ : syracuseStep 1020971 = 1531457) B1531457
theorem B3445847 : Blo 603293 3445847 := bstep (se 1 (by rfl) ⟨2584385, by rfl⟩ : syracuseStep 3445847 = 5168771) B5168771
theorem B1152299 : Blo 603293 1152299 := bstep (se 1 (by rfl) ⟨864224, by rfl⟩ : syracuseStep 1152299 = 1728449) B1728449
theorem B1021369 : Blo 603293 1021369 := bstep (se 2 (by rfl) ⟨383013, by rfl⟩ : syracuseStep 1021369 = 766027) B766027
theorem B923081 : Blo 603293 923081 := bstep (se 2 (by rfl) ⟨346155, by rfl⟩ : syracuseStep 923081 = 692311) B692311
theorem B3675955 : Blo 603293 3675955 := bstep (se 1 (by rfl) ⟨2756966, by rfl⟩ : syracuseStep 3675955 = 5513933) B5513933
theorem B1939315 : Blo 603293 1939315 := bstep (se 1 (by rfl) ⟨1454486, by rfl⟩ : syracuseStep 1939315 = 2908973) B2908973
theorem B2037689 : Blo 603293 2037689 := bstep (se 2 (by rfl) ⟨764133, by rfl⟩ : syracuseStep 2037689 = 1528267) B1528267
theorem B19666961 : Blo 603293 19666961 := bstep (se 2 (by rfl) ⟨7375110, by rfl⟩ : syracuseStep 19666961 = 14750221) B14750221
theorem B6559805 : Blo 603293 6559805 := bstep (se 3 (by rfl) ⟨1229963, by rfl⟩ : syracuseStep 6559805 = 2459927) B2459927
theorem B16750709 : Blo 603293 16750709 := bstep (se 5 (by rfl) ⟨785189, by rfl⟩ : syracuseStep 16750709 = 1570379) B1570379
theorem B1022071 : Blo 603293 1022071 := bstep (se 1 (by rfl) ⟨766553, by rfl⟩ : syracuseStep 1022071 = 1533107) B1533107
theorem B1022267 : Blo 603293 1022267 := bstep (se 1 (by rfl) ⟨766700, by rfl⟩ : syracuseStep 1022267 = 1533401) B1533401
theorem B1743257 : Blo 603293 1743257 := bstep (se 2 (by rfl) ⟨653721, by rfl⟩ : syracuseStep 1743257 = 1307443) B1307443
theorem B2300345 : Blo 603293 2300345 := bstep (se 2 (by rfl) ⟨862629, by rfl⟩ : syracuseStep 2300345 = 1725259) B1725259
theorem B2038283 : Blo 603293 2038283 := bstep (se 1 (by rfl) ⟨1528712, by rfl⟩ : syracuseStep 2038283 = 3057425) B3057425
theorem B2038391 : Blo 603293 2038391 := bstep (se 1 (by rfl) ⟨1528793, by rfl⟩ : syracuseStep 2038391 = 3057587) B3057587
theorem B2071241 : Blo 603293 2071241 := bstep (se 2 (by rfl) ⟨776715, by rfl⟩ : syracuseStep 2071241 = 1553431) B1553431
theorem B1022665 : Blo 603293 1022665 := bstep (se 2 (by rfl) ⟨383499, by rfl⟩ : syracuseStep 1022665 = 766999) B766999
theorem B1383227 : Blo 603293 1383227 := bstep (se 1 (by rfl) ⟨1037420, by rfl⟩ : syracuseStep 1383227 = 2074841) B2074841
theorem B859081 : Blo 603293 859081 := bstep (se 2 (by rfl) ⟨322155, by rfl⟩ : syracuseStep 859081 = 644311) B644311
theorem B859195 : Blo 603293 859195 := bstep (se 1 (by rfl) ⟨644396, by rfl⟩ : syracuseStep 859195 = 1288793) B1288793
theorem B15735869 : Blo 603293 15735869 := bstep (se 3 (by rfl) ⟨2950475, by rfl⟩ : syracuseStep 15735869 = 5900951) B5900951
theorem B2038985 : Blo 603293 2038985 := bstep (se 2 (by rfl) ⟨764619, by rfl⟩ : syracuseStep 2038985 = 1529239) B1529239
theorem B3448079 : Blo 603293 3448079 := bstep (se 1 (by rfl) ⟨2586059, by rfl⟩ : syracuseStep 3448079 = 5172119) B5172119
theorem B1023367 : Blo 603293 1023367 := bstep (se 1 (by rfl) ⟨767525, by rfl⟩ : syracuseStep 1023367 = 1535051) B1535051
theorem B3054995 : Blo 603293 3054995 := bstep (se 1 (by rfl) ⟨2291246, by rfl⟩ : syracuseStep 3054995 = 4582493) B4582493
theorem B2301331 : Blo 603293 2301331 := bstep (se 1 (by rfl) ⟨1725998, by rfl⟩ : syracuseStep 2301331 = 3451997) B3451997
theorem B4595129 : Blo 603293 4595129 := bstep (se 2 (by rfl) ⟨1723173, by rfl⟩ : syracuseStep 4595129 = 3446347) B3446347
theorem B3317201 : Blo 603293 3317201 := bstep (se 2 (by rfl) ⟨1243950, by rfl⟩ : syracuseStep 3317201 = 2487901) B2487901
theorem B3448331 : Blo 603293 3448331 := bstep (se 1 (by rfl) ⟨2586248, by rfl⟩ : syracuseStep 3448331 = 5172497) B5172497
theorem B4366169 : Blo 603293 4366169 := bstep (se 2 (by rfl) ⟨1637313, by rfl⟩ : syracuseStep 4366169 = 3274627) B3274627
theorem B2039687 : Blo 603293 2039687 := bstep (se 1 (by rfl) ⟨1529765, by rfl⟩ : syracuseStep 2039687 = 3059531) B3059531
theorem B1024015 : Blo 603293 1024015 := bstep (se 1 (by rfl) ⟨768011, by rfl⟩ : syracuseStep 1024015 = 1536023) B1536023
theorem B1941533 : Blo 603293 1941533 := bstep (se 3 (by rfl) ⟨364037, by rfl⟩ : syracuseStep 1941533 = 728075) B728075
theorem B2040065 : Blo 603293 2040065 := bstep (se 2 (by rfl) ⟨765024, by rfl⟩ : syracuseStep 2040065 = 1530049) B1530049
theorem B1024555 : Blo 603293 1024555 := bstep (se 1 (by rfl) ⟨768416, by rfl⟩ : syracuseStep 1024555 = 1536833) B1536833
theorem B860807 : Blo 603293 860807 := bstep (se 1 (by rfl) ⟨645605, by rfl⟩ : syracuseStep 860807 = 1291211) B1291211
theorem B1024697 : Blo 603293 1024697 := bstep (se 2 (by rfl) ⟨384261, by rfl⟩ : syracuseStep 1024697 = 768523) B768523
theorem B3449537 : Blo 603293 3449537 := bstep (se 2 (by rfl) ⟨1293576, by rfl⟩ : syracuseStep 3449537 = 2587153) B2587153
theorem B1090505 : Blo 603293 1090505 := bstep (se 2 (by rfl) ⟨408939, by rfl⟩ : syracuseStep 1090505 = 817879) B817879
theorem B6890507 : Blo 603293 6890507 := bstep (se 1 (by rfl) ⟨5167880, by rfl⟩ : syracuseStep 6890507 = 10335761) B10335761
theorem B2040875 : Blo 603293 2040875 := bstep (se 1 (by rfl) ⟨1530656, by rfl⟩ : syracuseStep 2040875 = 3061313) B3061313
theorem B6628439 : Blo 603293 6628439 := bstep (se 1 (by rfl) ⟨4971329, by rfl⟩ : syracuseStep 6628439 = 9942659) B9942659
theorem B2303063 : Blo 603293 2303063 := bstep (se 1 (by rfl) ⟨1727297, by rfl⟩ : syracuseStep 2303063 = 3454595) B3454595
theorem B1091017 : Blo 603293 1091017 := bstep (se 2 (by rfl) ⟨409131, by rfl⟩ : syracuseStep 1091017 = 818263) B818263
theorem B2303549 : Blo 603293 2303549 := bstep (se 3 (by rfl) ⟨431915, by rfl⟩ : syracuseStep 2303549 = 863831) B863831
theorem B861769 : Blo 603293 861769 := bstep (se 2 (by rfl) ⟨323163, by rfl⟩ : syracuseStep 861769 = 646327) B646327
theorem B15738443 : Blo 603293 15738443 := bstep (se 1 (by rfl) ⟨11803832, by rfl⟩ : syracuseStep 15738443 = 23607665) B23607665
theorem B763663 : Blo 603293 763663 := bstep (se 1 (by rfl) ⟨572747, by rfl⟩ : syracuseStep 763663 = 1145495) B1145495
theorem B1451891 : Blo 603293 1451891 := bstep (se 1 (by rfl) ⟨1088918, by rfl⟩ : syracuseStep 1451891 = 2177837) B2177837
theorem B4138867 : Blo 603293 4138867 := bstep (se 1 (by rfl) ⟨3104150, by rfl⟩ : syracuseStep 4138867 = 6208301) B6208301
theorem B1451929 : Blo 603293 1451929 := bstep (se 2 (by rfl) ⟨544473, by rfl⟩ : syracuseStep 1451929 = 1088947) B1088947
theorem B862265 : Blo 603293 862265 := bstep (se 2 (by rfl) ⟨323349, by rfl⟩ : syracuseStep 862265 = 646699) B646699
theorem B2042171 : Blo 603293 2042171 := bstep (se 1 (by rfl) ⟨1531628, by rfl⟩ : syracuseStep 2042171 = 3063257) B3063257
theorem B3058073 : Blo 603293 3058073 := bstep (se 2 (by rfl) ⟨1146777, by rfl⟩ : syracuseStep 3058073 = 2293555) B2293555
theorem B1943993 : Blo 603293 1943993 := bstep (se 2 (by rfl) ⟨728997, by rfl⟩ : syracuseStep 1943993 = 1457995) B1457995
theorem B764407 : Blo 603293 764407 := bstep (se 1 (by rfl) ⟨573305, by rfl⟩ : syracuseStep 764407 = 1146611) B1146611
theorem B1452545 : Blo 603293 1452545 := bstep (se 2 (by rfl) ⟨544704, by rfl⟩ : syracuseStep 1452545 = 1089409) B1089409
theorem B2042657 : Blo 603293 2042657 := bstep (se 2 (by rfl) ⟨765996, by rfl⟩ : syracuseStep 2042657 = 1531993) B1531993
theorem B764731 : Blo 603293 764731 := bstep (se 1 (by rfl) ⟨573548, by rfl⟩ : syracuseStep 764731 = 1147097) B1147097
theorem B863239 : Blo 603293 863239 := bstep (se 1 (by rfl) ⟨647429, by rfl⟩ : syracuseStep 863239 = 1294859) B1294859
theorem B1453313 : Blo 603293 1453313 := bstep (se 2 (by rfl) ⟨544992, by rfl⟩ : syracuseStep 1453313 = 1089985) B1089985
theorem B765227 : Blo 603293 765227 := bstep (se 1 (by rfl) ⟨573920, by rfl⟩ : syracuseStep 765227 = 1147841) B1147841
theorem B2043251 : Blo 603293 2043251 := bstep (se 1 (by rfl) ⟨1532438, by rfl⟩ : syracuseStep 2043251 = 3064877) B3064877
theorem B1453459 : Blo 603293 1453459 := bstep (se 1 (by rfl) ⟨1090094, by rfl⟩ : syracuseStep 1453459 = 2180189) B2180189
theorem B765703 : Blo 603293 765703 := bstep (se 1 (by rfl) ⟨574277, by rfl⟩ : syracuseStep 765703 = 1148555) B1148555
theorem B3452705 : Blo 603293 3452705 := bstep (se 2 (by rfl) ⟨1294764, by rfl⟩ : syracuseStep 3452705 = 2589529) B2589529
theorem B766199 : Blo 603293 766199 := bstep (se 1 (by rfl) ⟨574649, by rfl⟩ : syracuseStep 766199 = 1149299) B1149299
theorem B766351 : Blo 603293 766351 := bstep (se 1 (by rfl) ⟨574763, by rfl⟩ : syracuseStep 766351 = 1149527) B1149527
theorem B766523 : Blo 603293 766523 := bstep (se 1 (by rfl) ⟨574892, by rfl⟩ : syracuseStep 766523 = 1149785) B1149785
theorem B3060665 : Blo 603293 3060665 := bstep (se 2 (by rfl) ⟨1147749, by rfl⟩ : syracuseStep 3060665 = 2295499) B2295499
theorem B1553555 : Blo 603293 1553555 := bstep (se 1 (by rfl) ⟨1165166, by rfl⟩ : syracuseStep 1553555 = 2330333) B2330333
theorem B603323 : Blo 603293 603323 := bstep (se 1 (by rfl) ⟨452492, by rfl⟩ : syracuseStep 603323 = 904985) B904985
theorem B603399 : Blo 603293 603399 := bstep (se 1 (by rfl) ⟨452549, by rfl⟩ : syracuseStep 603399 = 905099) B905099
theorem B603407 : Blo 603293 603407 := bstep (se 1 (by rfl) ⟨452555, by rfl⟩ : syracuseStep 603407 = 905111) B905111
theorem B6894881 : Blo 603293 6894881 := bstep (se 2 (by rfl) ⟨2585580, by rfl⟩ : syracuseStep 6894881 = 5171161) B5171161
theorem B603451 : Blo 603293 603451 := bstep (se 1 (by rfl) ⟨452588, by rfl⟩ : syracuseStep 603451 = 905177) B905177
theorem B603527 : Blo 603293 603527 := bstep (se 1 (by rfl) ⟨452645, by rfl⟩ : syracuseStep 603527 = 905291) B905291
theorem B5813639 : Blo 603293 5813639 := bstep (se 1 (by rfl) ⟨4360229, by rfl⟩ : syracuseStep 5813639 = 8720459) B8720459
theorem B603535 : Blo 603293 603535 := bstep (se 1 (by rfl) ⟨452651, by rfl⟩ : syracuseStep 603535 = 905303) B905303
theorem B603579 : Blo 603293 603579 := bstep (se 1 (by rfl) ⟨452684, by rfl⟩ : syracuseStep 603579 = 905369) B905369
theorem B603655 : Blo 603293 603655 := bstep (se 1 (by rfl) ⟨452741, by rfl⟩ : syracuseStep 603655 = 905483) B905483
theorem B767495 : Blo 603293 767495 := bstep (se 1 (by rfl) ⟨575621, by rfl⟩ : syracuseStep 767495 = 1151243) B1151243
theorem B603663 : Blo 603293 603663 := bstep (se 1 (by rfl) ⟨452747, by rfl⟩ : syracuseStep 603663 = 905495) B905495
theorem B5518891 : Blo 603293 5518891 := bstep (se 1 (by rfl) ⟨4139168, by rfl⟩ : syracuseStep 5518891 = 8278337) B8278337
theorem B931385 : Blo 603293 931385 := bstep (se 2 (by rfl) ⟨349269, by rfl⟩ : syracuseStep 931385 = 698539) B698539
theorem B603707 : Blo 603293 603707 := bstep (se 1 (by rfl) ⟨452780, by rfl⟩ : syracuseStep 603707 = 905561) B905561
theorem B603783 : Blo 603293 603783 := bstep (se 1 (by rfl) ⟨452837, by rfl⟩ : syracuseStep 603783 = 905675) B905675
theorem B603791 : Blo 603293 603791 := bstep (se 1 (by rfl) ⟨452843, by rfl⟩ : syracuseStep 603791 = 905687) B905687
theorem B603835 : Blo 603293 603835 := bstep (se 1 (by rfl) ⟨452876, by rfl⟩ : syracuseStep 603835 = 905753) B905753
theorem B603911 : Blo 603293 603911 := bstep (se 1 (by rfl) ⟨452933, by rfl⟩ : syracuseStep 603911 = 905867) B905867
theorem B603919 : Blo 603293 603919 := bstep (se 1 (by rfl) ⟨452939, by rfl⟩ : syracuseStep 603919 = 905879) B905879
theorem B603963 : Blo 603293 603963 := bstep (se 1 (by rfl) ⟨452972, by rfl⟩ : syracuseStep 603963 = 905945) B905945
theorem B1357703 : Blo 603293 1357703 := bstep (se 1 (by rfl) ⟨1018277, by rfl⟩ : syracuseStep 1357703 = 2036555) B2036555
theorem B604039 : Blo 603293 604039 := bstep (se 1 (by rfl) ⟨453029, by rfl⟩ : syracuseStep 604039 = 906059) B906059
theorem B604047 : Blo 603293 604047 := bstep (se 1 (by rfl) ⟨453035, by rfl⟩ : syracuseStep 604047 = 906071) B906071
theorem B2176915 : Blo 603293 2176915 := bstep (se 1 (by rfl) ⟨1632686, by rfl⟩ : syracuseStep 2176915 = 3265373) B3265373
theorem B2045843 : Blo 603293 2045843 := bstep (se 1 (by rfl) ⟨1534382, by rfl⟩ : syracuseStep 2045843 = 3068765) B3068765
theorem B604091 : Blo 603293 604091 := bstep (se 1 (by rfl) ⟨453068, by rfl⟩ : syracuseStep 604091 = 906137) B906137
theorem B604167 : Blo 603293 604167 := bstep (se 1 (by rfl) ⟨453125, by rfl⟩ : syracuseStep 604167 = 906251) B906251
theorem B604175 : Blo 603293 604175 := bstep (se 1 (by rfl) ⟨453131, by rfl⟩ : syracuseStep 604175 = 906263) B906263
theorem B1357883 : Blo 603293 1357883 := bstep (se 1 (by rfl) ⟨1018412, by rfl⟩ : syracuseStep 1357883 = 2036825) B2036825
theorem B604219 : Blo 603293 604219 := bstep (se 1 (by rfl) ⟨453164, by rfl⟩ : syracuseStep 604219 = 906329) B906329
theorem B2275415 : Blo 603293 2275415 := bstep (se 1 (by rfl) ⟨1706561, by rfl⟩ : syracuseStep 2275415 = 3413123) B3413123
theorem B3455095 : Blo 603293 3455095 := bstep (se 1 (by rfl) ⟨2591321, by rfl⟩ : syracuseStep 3455095 = 5182643) B5182643
theorem B604295 : Blo 603293 604295 := bstep (se 1 (by rfl) ⟨453221, by rfl⟩ : syracuseStep 604295 = 906443) B906443
theorem B604303 : Blo 603293 604303 := bstep (se 1 (by rfl) ⟨453227, by rfl⟩ : syracuseStep 604303 = 906455) B906455
theorem B768143 : Blo 603293 768143 := bstep (se 1 (by rfl) ⟨576107, by rfl⟩ : syracuseStep 768143 = 1152215) B1152215
theorem B1358009 : Blo 603293 1358009 := bstep (se 2 (by rfl) ⟨509253, by rfl⟩ : syracuseStep 1358009 = 1018507) B1018507
theorem B604347 : Blo 603293 604347 := bstep (se 1 (by rfl) ⟨453260, by rfl⟩ : syracuseStep 604347 = 906521) B906521
theorem B3061961 : Blo 603293 3061961 := bstep (se 2 (by rfl) ⟨1148235, by rfl⟩ : syracuseStep 3061961 = 2296471) B2296471
theorem B604423 : Blo 603293 604423 := bstep (se 1 (by rfl) ⟨453317, by rfl⟩ : syracuseStep 604423 = 906635) B906635
theorem B604431 : Blo 603293 604431 := bstep (se 1 (by rfl) ⟨453323, by rfl⟩ : syracuseStep 604431 = 906647) B906647
theorem B604475 : Blo 603293 604475 := bstep (se 1 (by rfl) ⟨453356, by rfl⟩ : syracuseStep 604475 = 906713) B906713
theorem B26589505 : Blo 603293 26589505 := bstep (se 2 (by rfl) ⟨9971064, by rfl⟩ : syracuseStep 26589505 = 19942129) B19942129
theorem B604551 : Blo 603293 604551 := bstep (se 1 (by rfl) ⟨453413, by rfl⟩ : syracuseStep 604551 = 906827) B906827
theorem B604559 : Blo 603293 604559 := bstep (se 1 (by rfl) ⟨453419, by rfl⟩ : syracuseStep 604559 = 906839) B906839
theorem B5519801 : Blo 603293 5519801 := bstep (se 2 (by rfl) ⟨2069925, by rfl⟩ : syracuseStep 5519801 = 4139851) B4139851
theorem B604603 : Blo 603293 604603 := bstep (se 1 (by rfl) ⟨453452, by rfl⟩ : syracuseStep 604603 = 906905) B906905
theorem B604679 : Blo 603293 604679 := bstep (se 1 (by rfl) ⟨453509, by rfl⟩ : syracuseStep 604679 = 907019) B907019
theorem B1358351 : Blo 603293 1358351 := bstep (se 1 (by rfl) ⟨1018763, by rfl⟩ : syracuseStep 1358351 = 2037527) B2037527
theorem B604687 : Blo 603293 604687 := bstep (se 1 (by rfl) ⟨453515, by rfl⟩ : syracuseStep 604687 = 907031) B907031
theorem B1358369 : Blo 603293 1358369 := bstep (se 2 (by rfl) ⟨509388, by rfl⟩ : syracuseStep 1358369 = 1018777) B1018777
theorem B604731 : Blo 603293 604731 := bstep (se 1 (by rfl) ⟨453548, by rfl⟩ : syracuseStep 604731 = 907097) B907097
theorem B604807 : Blo 603293 604807 := bstep (se 1 (by rfl) ⟨453605, by rfl⟩ : syracuseStep 604807 = 907211) B907211
theorem B604815 : Blo 603293 604815 := bstep (se 1 (by rfl) ⟨453611, by rfl⟩ : syracuseStep 604815 = 907223) B907223
theorem B1456793 : Blo 603293 1456793 := bstep (se 2 (by rfl) ⟨546297, by rfl⟩ : syracuseStep 1456793 = 1092595) B1092595
theorem B604859 : Blo 603293 604859 := bstep (se 1 (by rfl) ⟨453644, by rfl⟩ : syracuseStep 604859 = 907289) B907289
theorem B604935 : Blo 603293 604935 := bstep (se 1 (by rfl) ⟨453701, by rfl⟩ : syracuseStep 604935 = 907403) B907403
theorem B604943 : Blo 603293 604943 := bstep (se 1 (by rfl) ⟨453707, by rfl⟩ : syracuseStep 604943 = 907415) B907415
theorem B1719073 : Blo 603293 1719073 := bstep (se 2 (by rfl) ⟨644652, by rfl⟩ : syracuseStep 1719073 = 1289305) B1289305
theorem B604987 : Blo 603293 604987 := bstep (se 1 (by rfl) ⟨453740, by rfl⟩ : syracuseStep 604987 = 907481) B907481
theorem B1358711 : Blo 603293 1358711 := bstep (se 1 (by rfl) ⟨1019033, by rfl⟩ : syracuseStep 1358711 = 2038067) B2038067
theorem B605063 : Blo 603293 605063 := bstep (se 1 (by rfl) ⟨453797, by rfl⟩ : syracuseStep 605063 = 907595) B907595
theorem B605071 : Blo 603293 605071 := bstep (se 1 (by rfl) ⟨453803, by rfl⟩ : syracuseStep 605071 = 907607) B907607
theorem B605115 : Blo 603293 605115 := bstep (se 1 (by rfl) ⟨453836, by rfl⟩ : syracuseStep 605115 = 907673) B907673
theorem B605191 : Blo 603293 605191 := bstep (se 1 (by rfl) ⟨453893, by rfl⟩ : syracuseStep 605191 = 907787) B907787
theorem B605199 : Blo 603293 605199 := bstep (se 1 (by rfl) ⟨453899, by rfl⟩ : syracuseStep 605199 = 907799) B907799
theorem B1358891 : Blo 603293 1358891 := bstep (se 1 (by rfl) ⟨1019168, by rfl⟩ : syracuseStep 1358891 = 2038337) B2038337
theorem B605243 : Blo 603293 605243 := bstep (se 1 (by rfl) ⟨453932, by rfl⟩ : syracuseStep 605243 = 907865) B907865
theorem B5160023 : Blo 603293 5160023 := bstep (se 1 (by rfl) ⟨3870017, by rfl⟩ : syracuseStep 5160023 = 7740035) B7740035
theorem B605319 : Blo 603293 605319 := bstep (se 1 (by rfl) ⟨453989, by rfl⟩ : syracuseStep 605319 = 907979) B907979
theorem B605327 : Blo 603293 605327 := bstep (se 1 (by rfl) ⟨453995, by rfl⟩ : syracuseStep 605327 = 907991) B907991
theorem B605371 : Blo 603293 605371 := bstep (se 1 (by rfl) ⟨454028, by rfl⟩ : syracuseStep 605371 = 908057) B908057
theorem B1162441 : Blo 603293 1162441 := bstep (se 2 (by rfl) ⟨435915, by rfl⟩ : syracuseStep 1162441 = 871831) B871831
theorem B605447 : Blo 603293 605447 := bstep (se 1 (by rfl) ⟨454085, by rfl⟩ : syracuseStep 605447 = 908171) B908171
theorem B2047247 : Blo 603293 2047247 := bstep (se 1 (by rfl) ⟨1535435, by rfl⟩ : syracuseStep 2047247 = 3070871) B3070871
theorem B605455 : Blo 603293 605455 := bstep (se 1 (by rfl) ⟨454091, by rfl⟩ : syracuseStep 605455 = 908183) B908183
theorem B605499 : Blo 603293 605499 := bstep (se 1 (by rfl) ⟨454124, by rfl⟩ : syracuseStep 605499 = 908249) B908249
theorem B3456371 : Blo 603293 3456371 := bstep (se 1 (by rfl) ⟨2592278, by rfl⟩ : syracuseStep 3456371 = 5184557) B5184557
theorem B605575 : Blo 603293 605575 := bstep (se 1 (by rfl) ⟨454181, by rfl⟩ : syracuseStep 605575 = 908363) B908363
theorem B605583 : Blo 603293 605583 := bstep (se 1 (by rfl) ⟨454187, by rfl⟩ : syracuseStep 605583 = 908375) B908375
theorem B1359251 : Blo 603293 1359251 := bstep (se 1 (by rfl) ⟨1019438, by rfl⟩ : syracuseStep 1359251 = 2038877) B2038877
theorem B605627 : Blo 603293 605627 := bstep (se 1 (by rfl) ⟨454220, by rfl⟩ : syracuseStep 605627 = 908441) B908441
theorem B1359305 : Blo 603293 1359305 := bstep (se 2 (by rfl) ⟨509739, by rfl⟩ : syracuseStep 1359305 = 1019479) B1019479
theorem B605703 : Blo 603293 605703 := bstep (se 1 (by rfl) ⟨454277, by rfl⟩ : syracuseStep 605703 = 908555) B908555
theorem B605711 : Blo 603293 605711 := bstep (se 1 (by rfl) ⟨454283, by rfl⟩ : syracuseStep 605711 = 908567) B908567
theorem B2047517 : Blo 603293 2047517 := bstep (se 3 (by rfl) ⟨383909, by rfl⟩ : syracuseStep 2047517 = 767819) B767819
theorem B605755 : Blo 603293 605755 := bstep (se 1 (by rfl) ⟨454316, by rfl⟩ : syracuseStep 605755 = 908633) B908633
theorem B605831 : Blo 603293 605831 := bstep (se 1 (by rfl) ⟨454373, by rfl⟩ : syracuseStep 605831 = 908747) B908747
theorem B605839 : Blo 603293 605839 := bstep (se 1 (by rfl) ⟨454379, by rfl⟩ : syracuseStep 605839 = 908759) B908759
theorem B605883 : Blo 603293 605883 := bstep (se 1 (by rfl) ⟨454412, by rfl⟩ : syracuseStep 605883 = 908825) B908825
theorem B605959 : Blo 603293 605959 := bstep (se 1 (by rfl) ⟨454469, by rfl⟩ : syracuseStep 605959 = 908939) B908939
theorem B966415 : Blo 603293 966415 := bstep (se 1 (by rfl) ⟨724811, by rfl⟩ : syracuseStep 966415 = 1449623) B1449623
theorem B605967 : Blo 603293 605967 := bstep (se 1 (by rfl) ⟨454475, by rfl⟩ : syracuseStep 605967 = 908951) B908951
theorem B606011 : Blo 603293 606011 := bstep (se 1 (by rfl) ⟨454508, by rfl⟩ : syracuseStep 606011 = 909017) B909017
theorem B3456827 : Blo 603293 3456827 := bstep (se 1 (by rfl) ⟨2592620, by rfl⟩ : syracuseStep 3456827 = 5185241) B5185241
theorem B606087 : Blo 603293 606087 := bstep (se 1 (by rfl) ⟨454565, by rfl⟩ : syracuseStep 606087 = 909131) B909131
theorem B606095 : Blo 603293 606095 := bstep (se 1 (by rfl) ⟨454571, by rfl⟩ : syracuseStep 606095 = 909143) B909143
theorem B606139 : Blo 603293 606139 := bstep (se 1 (by rfl) ⟨454604, by rfl⟩ : syracuseStep 606139 = 909209) B909209
theorem B606215 : Blo 603293 606215 := bstep (se 1 (by rfl) ⟨454661, by rfl⟩ : syracuseStep 606215 = 909323) B909323
theorem B606223 : Blo 603293 606223 := bstep (se 1 (by rfl) ⟨454667, by rfl⟩ : syracuseStep 606223 = 909335) B909335
theorem B1720349 : Blo 603293 1720349 := bstep (se 3 (by rfl) ⟨322565, by rfl⟩ : syracuseStep 1720349 = 645131) B645131
theorem B606267 : Blo 603293 606267 := bstep (se 1 (by rfl) ⟨454700, by rfl⟩ : syracuseStep 606267 = 909401) B909401
theorem B3489911 : Blo 603293 3489911 := bstep (se 1 (by rfl) ⟨2617433, by rfl⟩ : syracuseStep 3489911 = 5234867) B5234867
theorem B6897797 : Blo 603293 6897797 := bstep (se 4 (by rfl) ⟨646668, by rfl⟩ : syracuseStep 6897797 = 1293337) B1293337
theorem B1360007 : Blo 603293 1360007 := bstep (se 1 (by rfl) ⟨1020005, by rfl⟩ : syracuseStep 1360007 = 2040011) B2040011
theorem B606343 : Blo 603293 606343 := bstep (se 1 (by rfl) ⟨454757, by rfl⟩ : syracuseStep 606343 = 909515) B909515
theorem B606351 : Blo 603293 606351 := bstep (se 1 (by rfl) ⟨454763, by rfl⟩ : syracuseStep 606351 = 909527) B909527
theorem B606395 : Blo 603293 606395 := bstep (se 1 (by rfl) ⟨454796, by rfl⟩ : syracuseStep 606395 = 909593) B909593
theorem B1720577 : Blo 603293 1720577 := bstep (se 2 (by rfl) ⟨645216, by rfl⟩ : syracuseStep 1720577 = 1290433) B1290433
theorem B606471 : Blo 603293 606471 := bstep (se 1 (by rfl) ⟨454853, by rfl⟩ : syracuseStep 606471 = 909707) B909707
theorem B606479 : Blo 603293 606479 := bstep (se 1 (by rfl) ⟨454859, by rfl⟩ : syracuseStep 606479 = 909719) B909719
theorem B1229089 : Blo 603293 1229089 := bstep (se 2 (by rfl) ⟨460908, by rfl⟩ : syracuseStep 1229089 = 921817) B921817
theorem B1360187 : Blo 603293 1360187 := bstep (se 1 (by rfl) ⟨1020140, by rfl⟩ : syracuseStep 1360187 = 2040281) B2040281
theorem B606523 : Blo 603293 606523 := bstep (se 1 (by rfl) ⟨454892, by rfl⟩ : syracuseStep 606523 = 909785) B909785
theorem B606599 : Blo 603293 606599 := bstep (se 1 (by rfl) ⟨454949, by rfl⟩ : syracuseStep 606599 = 909899) B909899
theorem B606607 : Blo 603293 606607 := bstep (se 1 (by rfl) ⟨454955, by rfl⟩ : syracuseStep 606607 = 909911) B909911
theorem B1360313 : Blo 603293 1360313 := bstep (se 2 (by rfl) ⟨510117, by rfl⟩ : syracuseStep 1360313 = 1020235) B1020235
theorem B606651 : Blo 603293 606651 := bstep (se 1 (by rfl) ⟨454988, by rfl⟩ : syracuseStep 606651 = 909977) B909977
theorem B606727 : Blo 603293 606727 := bstep (se 1 (by rfl) ⟨455045, by rfl⟩ : syracuseStep 606727 = 910091) B910091
theorem B606735 : Blo 603293 606735 := bstep (se 1 (by rfl) ⟨455051, by rfl⟩ : syracuseStep 606735 = 910103) B910103
theorem B606779 : Blo 603293 606779 := bstep (se 1 (by rfl) ⟨455084, by rfl⟩ : syracuseStep 606779 = 910169) B910169
theorem B1720919 : Blo 603293 1720919 := bstep (se 1 (by rfl) ⟨1290689, by rfl⟩ : syracuseStep 1720919 = 2581379) B2581379
theorem B606855 : Blo 603293 606855 := bstep (se 1 (by rfl) ⟨455141, by rfl⟩ : syracuseStep 606855 = 910283) B910283
theorem B606863 : Blo 603293 606863 := bstep (se 1 (by rfl) ⟨455147, by rfl⟩ : syracuseStep 606863 = 910295) B910295
theorem B606907 : Blo 603293 606907 := bstep (se 1 (by rfl) ⟨455180, by rfl⟩ : syracuseStep 606907 = 910361) B910361
theorem B1721033 : Blo 603293 1721033 := bstep (se 2 (by rfl) ⟨645387, by rfl⟩ : syracuseStep 1721033 = 1290775) B1290775
theorem B606983 : Blo 603293 606983 := bstep (se 1 (by rfl) ⟨455237, by rfl⟩ : syracuseStep 606983 = 910475) B910475
theorem B1360655 : Blo 603293 1360655 := bstep (se 1 (by rfl) ⟨1020491, by rfl⟩ : syracuseStep 1360655 = 2040983) B2040983
theorem B606991 : Blo 603293 606991 := bstep (se 1 (by rfl) ⟨455243, by rfl⟩ : syracuseStep 606991 = 910487) B910487
theorem B1360673 : Blo 603293 1360673 := bstep (se 2 (by rfl) ⟨510252, by rfl⟩ : syracuseStep 1360673 = 1020505) B1020505
theorem B3457829 : Blo 603293 3457829 := bstep (se 4 (by rfl) ⟨324171, by rfl⟩ : syracuseStep 3457829 = 648343) B648343
theorem B607035 : Blo 603293 607035 := bstep (se 1 (by rfl) ⟨455276, by rfl⟩ : syracuseStep 607035 = 910553) B910553
theorem B6800203 : Blo 603293 6800203 := bstep (se 1 (by rfl) ⟨5100152, by rfl⟩ : syracuseStep 6800203 = 10200305) B10200305
theorem B607111 : Blo 603293 607111 := bstep (se 1 (by rfl) ⟨455333, by rfl⟩ : syracuseStep 607111 = 910667) B910667
theorem B607119 : Blo 603293 607119 := bstep (se 1 (by rfl) ⟨455339, by rfl⟩ : syracuseStep 607119 = 910679) B910679
theorem B2048921 : Blo 603293 2048921 := bstep (se 2 (by rfl) ⟨768345, by rfl⟩ : syracuseStep 2048921 = 1536691) B1536691
theorem B607163 : Blo 603293 607163 := bstep (se 1 (by rfl) ⟨455372, by rfl⟩ : syracuseStep 607163 = 910745) B910745
theorem B3490781 : Blo 603293 3490781 := bstep (se 3 (by rfl) ⟨654521, by rfl⟩ : syracuseStep 3490781 = 1309043) B1309043
theorem B607239 : Blo 603293 607239 := bstep (se 1 (by rfl) ⟨455429, by rfl⟩ : syracuseStep 607239 = 910859) B910859
theorem B9815051 : Blo 603293 9815051 := bstep (se 1 (by rfl) ⟨7361288, by rfl⟩ : syracuseStep 9815051 = 14722577) B14722577
theorem B607247 : Blo 603293 607247 := bstep (se 1 (by rfl) ⟨455435, by rfl⟩ : syracuseStep 607247 = 910871) B910871
theorem B607291 : Blo 603293 607291 := bstep (se 1 (by rfl) ⟨455468, by rfl⟩ : syracuseStep 607291 = 910937) B910937
theorem B967799 : Blo 603293 967799 := bstep (se 1 (by rfl) ⟨725849, by rfl⟩ : syracuseStep 967799 = 1451699) B1451699
theorem B1361015 : Blo 603293 1361015 := bstep (se 1 (by rfl) ⟨1020761, by rfl⟩ : syracuseStep 1361015 = 2041523) B2041523
theorem B935083 : Blo 603293 935083 := bstep (se 1 (by rfl) ⟨701312, by rfl⟩ : syracuseStep 935083 = 1402625) B1402625
theorem B3458285 : Blo 603293 3458285 := bstep (se 3 (by rfl) ⟨648428, by rfl⟩ : syracuseStep 3458285 = 1296857) B1296857
theorem B1361195 : Blo 603293 1361195 := bstep (se 1 (by rfl) ⟨1020896, by rfl⟩ : syracuseStep 1361195 = 2041793) B2041793
theorem B1558027 : Blo 603293 1558027 := bstep (se 1 (by rfl) ⟨1168520, by rfl⟩ : syracuseStep 1558027 = 2337041) B2337041
theorem B1361555 : Blo 603293 1361555 := bstep (se 1 (by rfl) ⟨1021166, by rfl⟩ : syracuseStep 1361555 = 2042333) B2042333
theorem B10798771 : Blo 603293 10798771 := bstep (se 1 (by rfl) ⟨8099078, by rfl⟩ : syracuseStep 10798771 = 16198157) B16198157
theorem B1361609 : Blo 603293 1361609 := bstep (se 2 (by rfl) ⟨510603, by rfl⟩ : syracuseStep 1361609 = 1021207) B1021207
theorem B9848729 : Blo 603293 9848729 := bstep (se 2 (by rfl) ⟨3693273, by rfl⟩ : syracuseStep 9848729 = 7386547) B7386547
theorem B2181239 : Blo 603293 2181239 := bstep (se 1 (by rfl) ⟨1635929, by rfl⟩ : syracuseStep 2181239 = 3271859) B3271859
theorem B1362311 : Blo 603293 1362311 := bstep (se 1 (by rfl) ⟨1021733, by rfl⟩ : syracuseStep 1362311 = 2043467) B2043467
theorem B1722809 : Blo 603293 1722809 := bstep (se 2 (by rfl) ⟨646053, by rfl⟩ : syracuseStep 1722809 = 1292107) B1292107
theorem B1362491 : Blo 603293 1362491 := bstep (se 1 (by rfl) ⟨1021868, by rfl⟩ : syracuseStep 1362491 = 2043737) B2043737
theorem B1362617 : Blo 603293 1362617 := bstep (se 2 (by rfl) ⟨510981, by rfl⟩ : syracuseStep 1362617 = 1021963) B1021963
theorem B5163749 : Blo 603293 5163749 := bstep (se 4 (by rfl) ⟨484101, by rfl⟩ : syracuseStep 5163749 = 968203) B968203
theorem B16599923 : Blo 603293 16599923 := bstep (se 1 (by rfl) ⟨12449942, by rfl⟩ : syracuseStep 16599923 = 24899885) B24899885
theorem B1362959 : Blo 603293 1362959 := bstep (se 1 (by rfl) ⟨1022219, by rfl⟩ : syracuseStep 1362959 = 2044439) B2044439
theorem B1362977 : Blo 603293 1362977 := bstep (se 2 (by rfl) ⟨511116, by rfl⟩ : syracuseStep 1362977 = 1022233) B1022233
theorem B63688037 : Blo 603293 63688037 := bstep (se 4 (by rfl) ⟨5970753, by rfl⟩ : syracuseStep 63688037 = 11941507) B11941507
theorem B1363319 : Blo 603293 1363319 := bstep (se 1 (by rfl) ⟨1022489, by rfl⟩ : syracuseStep 1363319 = 2044979) B2044979
theorem B1723801 : Blo 603293 1723801 := bstep (se 2 (by rfl) ⟨646425, by rfl⟩ : syracuseStep 1723801 = 1292851) B1292851
theorem B1363499 : Blo 603293 1363499 := bstep (se 1 (by rfl) ⟨1022624, by rfl⟩ : syracuseStep 1363499 = 2045249) B2045249
theorem B970375 : Blo 603293 970375 := bstep (se 1 (by rfl) ⟨727781, by rfl⟩ : syracuseStep 970375 = 1455563) B1455563
theorem B904967 : Blo 603293 904967 := bstep (se 1 (by rfl) ⟨678725, by rfl⟩ : syracuseStep 904967 = 1357451) B1357451
theorem B905003 : Blo 603293 905003 := bstep (se 1 (by rfl) ⟨678752, by rfl⟩ : syracuseStep 905003 = 1357505) B1357505
theorem B905033 : Blo 603293 905033 := bstep (se 2 (by rfl) ⟨339387, by rfl⟩ : syracuseStep 905033 = 678775) B678775
theorem B3067793 : Blo 603293 3067793 := bstep (se 2 (by rfl) ⟨1150422, by rfl⟩ : syracuseStep 3067793 = 2300845) B2300845
theorem B1363859 : Blo 603293 1363859 := bstep (se 1 (by rfl) ⟨1022894, by rfl⟩ : syracuseStep 1363859 = 2045789) B2045789
theorem B905147 : Blo 603293 905147 := bstep (se 1 (by rfl) ⟨678860, by rfl⟩ : syracuseStep 905147 = 1357721) B1357721
theorem B1363913 : Blo 603293 1363913 := bstep (se 2 (by rfl) ⟨511467, by rfl⟩ : syracuseStep 1363913 = 1022935) B1022935
theorem B905207 : Blo 603293 905207 := bstep (se 1 (by rfl) ⟨678905, by rfl⟩ : syracuseStep 905207 = 1357811) B1357811
theorem B905231 : Blo 603293 905231 := bstep (se 1 (by rfl) ⟨678923, by rfl⟩ : syracuseStep 905231 = 1357847) B1357847
theorem B905273 : Blo 603293 905273 := bstep (se 2 (by rfl) ⟨339477, by rfl⟩ : syracuseStep 905273 = 678955) B678955
theorem B1527923 : Blo 603293 1527923 := bstep (se 1 (by rfl) ⟨1145942, by rfl⟩ : syracuseStep 1527923 = 2291885) B2291885
theorem B905351 : Blo 603293 905351 := bstep (se 1 (by rfl) ⟨679013, by rfl⟩ : syracuseStep 905351 = 1358027) B1358027
theorem B1527943 : Blo 603293 1527943 := bstep (se 1 (by rfl) ⟨1145957, by rfl⟩ : syracuseStep 1527943 = 2291915) B2291915
theorem B905387 : Blo 603293 905387 := bstep (se 1 (by rfl) ⟨679040, by rfl⟩ : syracuseStep 905387 = 1358081) B1358081
theorem B13455533 : Blo 603293 13455533 := bstep (se 3 (by rfl) ⟨2522912, by rfl⟩ : syracuseStep 13455533 = 5045825) B5045825
theorem B905417 : Blo 603293 905417 := bstep (se 2 (by rfl) ⟨339531, by rfl⟩ : syracuseStep 905417 = 679063) B679063
theorem B971023 : Blo 603293 971023 := bstep (se 1 (by rfl) ⟨728267, by rfl⟩ : syracuseStep 971023 = 1456535) B1456535
theorem B905531 : Blo 603293 905531 := bstep (se 1 (by rfl) ⟨679148, by rfl⟩ : syracuseStep 905531 = 1358297) B1358297
theorem B905591 : Blo 603293 905591 := bstep (se 1 (by rfl) ⟨679193, by rfl⟩ : syracuseStep 905591 = 1358387) B1358387
theorem B905615 : Blo 603293 905615 := bstep (se 1 (by rfl) ⟨679211, by rfl⟩ : syracuseStep 905615 = 1358423) B1358423
theorem B1528217 : Blo 603293 1528217 := bstep (se 2 (by rfl) ⟨573081, by rfl⟩ : syracuseStep 1528217 = 1146163) B1146163
theorem B2904473 : Blo 603293 2904473 := bstep (se 2 (by rfl) ⟨1089177, by rfl⟩ : syracuseStep 2904473 = 2178355) B2178355
theorem B905657 : Blo 603293 905657 := bstep (se 2 (by rfl) ⟨339621, by rfl⟩ : syracuseStep 905657 = 679243) B679243
theorem B905735 : Blo 603293 905735 := bstep (se 1 (by rfl) ⟨679301, by rfl⟩ : syracuseStep 905735 = 1358603) B1358603
theorem B971279 : Blo 603293 971279 := bstep (se 1 (by rfl) ⟨728459, by rfl⟩ : syracuseStep 971279 = 1456919) B1456919
theorem B1167905 : Blo 603293 1167905 := bstep (se 2 (by rfl) ⟨437964, by rfl⟩ : syracuseStep 1167905 = 875929) B875929
theorem B905771 : Blo 603293 905771 := bstep (se 1 (by rfl) ⟨679328, by rfl⟩ : syracuseStep 905771 = 1358657) B1358657
theorem B1528379 : Blo 603293 1528379 := bstep (se 1 (by rfl) ⟨1146284, by rfl⟩ : syracuseStep 1528379 = 2292569) B2292569
theorem B905801 : Blo 603293 905801 := bstep (se 2 (by rfl) ⟨339675, by rfl⟩ : syracuseStep 905801 = 679351) B679351
theorem B1364615 : Blo 603293 1364615 := bstep (se 1 (by rfl) ⟨1023461, by rfl⟩ : syracuseStep 1364615 = 2046923) B2046923
theorem B905915 : Blo 603293 905915 := bstep (se 1 (by rfl) ⟨679436, by rfl⟩ : syracuseStep 905915 = 1358873) B1358873
theorem B905975 : Blo 603293 905975 := bstep (se 1 (by rfl) ⟨679481, by rfl⟩ : syracuseStep 905975 = 1358963) B1358963
theorem B1528591 : Blo 603293 1528591 := bstep (se 1 (by rfl) ⟨1146443, by rfl⟩ : syracuseStep 1528591 = 2292887) B2292887
theorem B905999 : Blo 603293 905999 := bstep (se 1 (by rfl) ⟨679499, by rfl⟩ : syracuseStep 905999 = 1358999) B1358999
theorem B906041 : Blo 603293 906041 := bstep (se 2 (by rfl) ⟨339765, by rfl⟩ : syracuseStep 906041 = 679531) B679531
theorem B1364795 : Blo 603293 1364795 := bstep (se 1 (by rfl) ⟨1023596, by rfl⟩ : syracuseStep 1364795 = 2047193) B2047193
theorem B906119 : Blo 603293 906119 := bstep (se 1 (by rfl) ⟨679589, by rfl⟩ : syracuseStep 906119 = 1359179) B1359179
theorem B906155 : Blo 603293 906155 := bstep (se 1 (by rfl) ⟨679616, by rfl⟩ : syracuseStep 906155 = 1359233) B1359233
theorem B1364921 : Blo 603293 1364921 := bstep (se 2 (by rfl) ⟨511845, by rfl⟩ : syracuseStep 1364921 = 1023691) B1023691
theorem B906185 : Blo 603293 906185 := bstep (se 2 (by rfl) ⟨339819, by rfl⟩ : syracuseStep 906185 = 679639) B679639
theorem B1528865 : Blo 603293 1528865 := bstep (se 2 (by rfl) ⟨573324, by rfl⟩ : syracuseStep 1528865 = 1146649) B1146649
theorem B906299 : Blo 603293 906299 := bstep (se 1 (by rfl) ⟨679724, by rfl⟩ : syracuseStep 906299 = 1359449) B1359449
theorem B906359 : Blo 603293 906359 := bstep (se 1 (by rfl) ⟨679769, by rfl⟩ : syracuseStep 906359 = 1359539) B1359539
theorem B906383 : Blo 603293 906383 := bstep (se 1 (by rfl) ⟨679787, by rfl⟩ : syracuseStep 906383 = 1359575) B1359575
theorem B906425 : Blo 603293 906425 := bstep (se 2 (by rfl) ⟨339909, by rfl⟩ : syracuseStep 906425 = 679819) B679819
theorem B906503 : Blo 603293 906503 := bstep (se 1 (by rfl) ⟨679877, by rfl⟩ : syracuseStep 906503 = 1359755) B1359755
theorem B1365263 : Blo 603293 1365263 := bstep (se 1 (by rfl) ⟨1023947, by rfl⟩ : syracuseStep 1365263 = 2047895) B2047895
theorem B1725725 : Blo 603293 1725725 := bstep (se 3 (by rfl) ⟨323573, by rfl⟩ : syracuseStep 1725725 = 647147) B647147
theorem B4904225 : Blo 603293 4904225 := bstep (se 2 (by rfl) ⟨1839084, by rfl⟩ : syracuseStep 4904225 = 3678169) B3678169
theorem B4150561 : Blo 603293 4150561 := bstep (se 2 (by rfl) ⟨1556460, by rfl⟩ : syracuseStep 4150561 = 3112921) B3112921
theorem B1365281 : Blo 603293 1365281 := bstep (se 2 (by rfl) ⟨511980, by rfl⟩ : syracuseStep 1365281 = 1023961) B1023961
theorem B906539 : Blo 603293 906539 := bstep (se 1 (by rfl) ⟨679904, by rfl⟩ : syracuseStep 906539 = 1359809) B1359809
theorem B906569 : Blo 603293 906569 := bstep (se 2 (by rfl) ⟨339963, by rfl⟩ : syracuseStep 906569 = 679927) B679927
theorem B2184583 : Blo 603293 2184583 := bstep (se 1 (by rfl) ⟨1638437, by rfl⟩ : syracuseStep 2184583 = 3276875) B3276875
theorem B906683 : Blo 603293 906683 := bstep (se 1 (by rfl) ⟨680012, by rfl⟩ : syracuseStep 906683 = 1360025) B1360025
theorem B906743 : Blo 603293 906743 := bstep (se 1 (by rfl) ⟨680057, by rfl⟩ : syracuseStep 906743 = 1360115) B1360115
theorem B906767 : Blo 603293 906767 := bstep (se 1 (by rfl) ⟨680075, by rfl⟩ : syracuseStep 906767 = 1360151) B1360151
theorem B906809 : Blo 603293 906809 := bstep (se 2 (by rfl) ⟨340053, by rfl⟩ : syracuseStep 906809 = 680107) B680107
theorem B1365623 : Blo 603293 1365623 := bstep (se 1 (by rfl) ⟨1024217, by rfl⟩ : syracuseStep 1365623 = 2048435) B2048435
theorem B972407 : Blo 603293 972407 := bstep (se 1 (by rfl) ⟨729305, by rfl⟩ : syracuseStep 972407 = 1458611) B1458611
theorem B906887 : Blo 603293 906887 := bstep (se 1 (by rfl) ⟨680165, by rfl⟩ : syracuseStep 906887 = 1360331) B1360331
theorem B906923 : Blo 603293 906923 := bstep (se 1 (by rfl) ⟨680192, by rfl⟩ : syracuseStep 906923 = 1360385) B1360385
theorem B906953 : Blo 603293 906953 := bstep (se 2 (by rfl) ⟨340107, by rfl⟩ : syracuseStep 906953 = 680215) B680215
theorem B1365803 : Blo 603293 1365803 := bstep (se 1 (by rfl) ⟨1024352, by rfl⟩ : syracuseStep 1365803 = 2048705) B2048705
theorem B907067 : Blo 603293 907067 := bstep (se 1 (by rfl) ⟨680300, by rfl⟩ : syracuseStep 907067 = 1360601) B1360601
theorem B907127 : Blo 603293 907127 := bstep (se 1 (by rfl) ⟨680345, by rfl⟩ : syracuseStep 907127 = 1360691) B1360691
theorem B907151 : Blo 603293 907151 := bstep (se 1 (by rfl) ⟨680363, by rfl⟩ : syracuseStep 907151 = 1360727) B1360727
theorem B907193 : Blo 603293 907193 := bstep (se 2 (by rfl) ⟨340197, by rfl⟩ : syracuseStep 907193 = 680395) B680395
theorem B1726409 : Blo 603293 1726409 := bstep (se 2 (by rfl) ⟨647403, by rfl⟩ : syracuseStep 1726409 = 1294807) B1294807
theorem B3069899 : Blo 603293 3069899 := bstep (se 1 (by rfl) ⟨2302424, by rfl⟩ : syracuseStep 3069899 = 4604849) B4604849
theorem B907271 : Blo 603293 907271 := bstep (se 1 (by rfl) ⟨680453, by rfl⟩ : syracuseStep 907271 = 1360907) B1360907
theorem B1529867 : Blo 603293 1529867 := bstep (se 1 (by rfl) ⟨1147400, by rfl⟩ : syracuseStep 1529867 = 2294801) B2294801
theorem B907307 : Blo 603293 907307 := bstep (se 1 (by rfl) ⟨680480, by rfl⟩ : syracuseStep 907307 = 1360961) B1360961
theorem B907337 : Blo 603293 907337 := bstep (se 2 (by rfl) ⟨340251, by rfl⟩ : syracuseStep 907337 = 680503) B680503
theorem B2938999 : Blo 603293 2938999 := bstep (se 1 (by rfl) ⟨2204249, by rfl⟩ : syracuseStep 2938999 = 4408499) B4408499
theorem B1366163 : Blo 603293 1366163 := bstep (se 1 (by rfl) ⟨1024622, by rfl⟩ : syracuseStep 1366163 = 2049245) B2049245
theorem B907451 : Blo 603293 907451 := bstep (se 1 (by rfl) ⟨680588, by rfl⟩ : syracuseStep 907451 = 1361177) B1361177
theorem B1366217 : Blo 603293 1366217 := bstep (se 2 (by rfl) ⟨512331, by rfl⟩ : syracuseStep 1366217 = 1024663) B1024663
theorem B11655413 : Blo 603293 11655413 := bstep (se 5 (by rfl) ⟨546347, by rfl⟩ : syracuseStep 11655413 = 1092695) B1092695
theorem B907511 : Blo 603293 907511 := bstep (se 1 (by rfl) ⟨680633, by rfl⟩ : syracuseStep 907511 = 1361267) B1361267
theorem B907535 : Blo 603293 907535 := bstep (se 1 (by rfl) ⟨680651, by rfl⟩ : syracuseStep 907535 = 1361303) B1361303
theorem B3070223 : Blo 603293 3070223 := bstep (se 1 (by rfl) ⟨2302667, by rfl⟩ : syracuseStep 3070223 = 4605335) B4605335
theorem B907577 : Blo 603293 907577 := bstep (se 2 (by rfl) ⟨340341, by rfl⟩ : syracuseStep 907577 = 680683) B680683
theorem B907655 : Blo 603293 907655 := bstep (se 1 (by rfl) ⟨680741, by rfl⟩ : syracuseStep 907655 = 1361483) B1361483
theorem B2906513 : Blo 603293 2906513 := bstep (se 2 (by rfl) ⟨1089942, by rfl⟩ : syracuseStep 2906513 = 2179885) B2179885
theorem B907691 : Blo 603293 907691 := bstep (se 1 (by rfl) ⟨680768, by rfl⟩ : syracuseStep 907691 = 1361537) B1361537
theorem B907721 : Blo 603293 907721 := bstep (se 2 (by rfl) ⟨340395, by rfl⟩ : syracuseStep 907721 = 680791) B680791
theorem B1726991 : Blo 603293 1726991 := bstep (se 1 (by rfl) ⟨1295243, by rfl⟩ : syracuseStep 1726991 = 2590487) B2590487
theorem B907835 : Blo 603293 907835 := bstep (se 1 (by rfl) ⟨680876, by rfl⟩ : syracuseStep 907835 = 1361753) B1361753
theorem B907895 : Blo 603293 907895 := bstep (se 1 (by rfl) ⟨680921, by rfl⟩ : syracuseStep 907895 = 1361843) B1361843
theorem B907919 : Blo 603293 907919 := bstep (se 1 (by rfl) ⟨680939, by rfl⟩ : syracuseStep 907919 = 1361879) B1361879
theorem B1530515 : Blo 603293 1530515 := bstep (se 1 (by rfl) ⟨1147886, by rfl⟩ : syracuseStep 1530515 = 2295773) B2295773
theorem B907961 : Blo 603293 907961 := bstep (se 2 (by rfl) ⟨340485, by rfl⟩ : syracuseStep 907961 = 680971) B680971
theorem B908039 : Blo 603293 908039 := bstep (se 1 (by rfl) ⟨681029, by rfl⟩ : syracuseStep 908039 = 1362059) B1362059
theorem B908075 : Blo 603293 908075 := bstep (se 1 (by rfl) ⟨681056, by rfl⟩ : syracuseStep 908075 = 1362113) B1362113
theorem B908105 : Blo 603293 908105 := bstep (se 2 (by rfl) ⟨340539, by rfl⟩ : syracuseStep 908105 = 681079) B681079
theorem B1530809 : Blo 603293 1530809 := bstep (se 2 (by rfl) ⟨574053, by rfl⟩ : syracuseStep 1530809 = 1148107) B1148107
theorem B908219 : Blo 603293 908219 := bstep (se 1 (by rfl) ⟨681164, by rfl⟩ : syracuseStep 908219 = 1362329) B1362329
theorem B2907089 : Blo 603293 2907089 := bstep (se 2 (by rfl) ⟨1090158, by rfl⟩ : syracuseStep 2907089 = 2180317) B2180317
theorem B908279 : Blo 603293 908279 := bstep (se 1 (by rfl) ⟨681209, by rfl⟩ : syracuseStep 908279 = 1362419) B1362419
theorem B678919 : Blo 603293 678919 := bstep (se 1 (by rfl) ⟨509189, by rfl⟩ : syracuseStep 678919 = 1018379) B1018379
theorem B908303 : Blo 603293 908303 := bstep (se 1 (by rfl) ⟨681227, by rfl⟩ : syracuseStep 908303 = 1362455) B1362455
theorem B908345 : Blo 603293 908345 := bstep (se 2 (by rfl) ⟨340629, by rfl⟩ : syracuseStep 908345 = 681259) B681259
theorem B3890263 : Blo 603293 3890263 := bstep (se 1 (by rfl) ⟨2917697, by rfl⟩ : syracuseStep 3890263 = 5835395) B5835395
theorem B908423 : Blo 603293 908423 := bstep (se 1 (by rfl) ⟨681317, by rfl⟩ : syracuseStep 908423 = 1362635) B1362635
theorem B908459 : Blo 603293 908459 := bstep (se 1 (by rfl) ⟨681344, by rfl⟩ : syracuseStep 908459 = 1362689) B1362689
theorem B679099 : Blo 603293 679099 := bstep (se 1 (by rfl) ⟨509324, by rfl⟩ : syracuseStep 679099 = 1018649) B1018649
theorem B908489 : Blo 603293 908489 := bstep (se 2 (by rfl) ⟨340683, by rfl⟩ : syracuseStep 908489 = 681367) B681367
theorem B908603 : Blo 603293 908603 := bstep (se 1 (by rfl) ⟨681452, by rfl⟩ : syracuseStep 908603 = 1362905) B1362905
theorem B908663 : Blo 603293 908663 := bstep (se 1 (by rfl) ⟨681497, by rfl⟩ : syracuseStep 908663 = 1362995) B1362995
theorem B908687 : Blo 603293 908687 := bstep (se 1 (by rfl) ⟨681515, by rfl⟩ : syracuseStep 908687 = 1363031) B1363031
theorem B908729 : Blo 603293 908729 := bstep (se 2 (by rfl) ⟨340773, by rfl⟩ : syracuseStep 908729 = 681547) B681547
theorem B613895 : Blo 603293 613895 := bstep (se 1 (by rfl) ⟨460421, by rfl⟩ : syracuseStep 613895 = 920843) B920843
theorem B908807 : Blo 603293 908807 := bstep (se 1 (by rfl) ⟨681605, by rfl⟩ : syracuseStep 908807 = 1363211) B1363211
theorem B908843 : Blo 603293 908843 := bstep (se 1 (by rfl) ⟨681632, by rfl⟩ : syracuseStep 908843 = 1363265) B1363265
theorem B908873 : Blo 603293 908873 := bstep (se 2 (by rfl) ⟨340827, by rfl⟩ : syracuseStep 908873 = 681655) B681655
theorem B1531507 : Blo 603293 1531507 := bstep (se 1 (by rfl) ⟨1148630, by rfl⟩ : syracuseStep 1531507 = 2297261) B2297261
theorem B679567 : Blo 603293 679567 := bstep (se 1 (by rfl) ⟨509675, by rfl⟩ : syracuseStep 679567 = 1019351) B1019351
theorem B908987 : Blo 603293 908987 := bstep (se 1 (by rfl) ⟨681740, by rfl⟩ : syracuseStep 908987 = 1363481) B1363481
theorem B3071681 : Blo 603293 3071681 := bstep (se 2 (by rfl) ⟨1151880, by rfl⟩ : syracuseStep 3071681 = 2303761) B2303761
theorem B909047 : Blo 603293 909047 := bstep (se 1 (by rfl) ⟨681785, by rfl⟩ : syracuseStep 909047 = 1363571) B1363571
theorem B1531649 : Blo 603293 1531649 := bstep (se 2 (by rfl) ⟨574368, by rfl⟩ : syracuseStep 1531649 = 1148737) B1148737
theorem B909071 : Blo 603293 909071 := bstep (se 1 (by rfl) ⟨681803, by rfl⟩ : syracuseStep 909071 = 1363607) B1363607
theorem B909113 : Blo 603293 909113 := bstep (se 2 (by rfl) ⟨340917, by rfl⟩ : syracuseStep 909113 = 681835) B681835
theorem B909191 : Blo 603293 909191 := bstep (se 1 (by rfl) ⟨681893, by rfl⟩ : syracuseStep 909191 = 1363787) B1363787
theorem B1728391 : Blo 603293 1728391 := bstep (se 1 (by rfl) ⟨1296293, by rfl⟩ : syracuseStep 1728391 = 2592587) B2592587
theorem B909227 : Blo 603293 909227 := bstep (se 1 (by rfl) ⟨681920, by rfl⟩ : syracuseStep 909227 = 1363841) B1363841
theorem B909257 : Blo 603293 909257 := bstep (se 2 (by rfl) ⟨340971, by rfl⟩ : syracuseStep 909257 = 681943) B681943
theorem B4186123 : Blo 603293 4186123 := bstep (se 1 (by rfl) ⟨3139592, by rfl⟩ : syracuseStep 4186123 = 6279185) B6279185
theorem B909371 : Blo 603293 909371 := bstep (se 1 (by rfl) ⟨682028, by rfl⟩ : syracuseStep 909371 = 1364057) B1364057
theorem B909431 : Blo 603293 909431 := bstep (se 1 (by rfl) ⟨682073, by rfl⟩ : syracuseStep 909431 = 1364147) B1364147
theorem B680071 : Blo 603293 680071 := bstep (se 1 (by rfl) ⟨510053, by rfl⟩ : syracuseStep 680071 = 1020107) B1020107
theorem B909455 : Blo 603293 909455 := bstep (se 1 (by rfl) ⟨682091, by rfl⟩ : syracuseStep 909455 = 1364183) B1364183
theorem B1728665 : Blo 603293 1728665 := bstep (se 2 (by rfl) ⟨648249, by rfl⟩ : syracuseStep 1728665 = 1296499) B1296499
theorem B909497 : Blo 603293 909497 := bstep (se 2 (by rfl) ⟨341061, by rfl⟩ : syracuseStep 909497 = 682123) B682123
theorem B1532105 : Blo 603293 1532105 := bstep (se 2 (by rfl) ⟨574539, by rfl⟩ : syracuseStep 1532105 = 1149079) B1149079
theorem B909575 : Blo 603293 909575 := bstep (se 1 (by rfl) ⟨682181, by rfl⟩ : syracuseStep 909575 = 1364363) B1364363
theorem B909611 : Blo 603293 909611 := bstep (se 1 (by rfl) ⟨682208, by rfl⟩ : syracuseStep 909611 = 1364417) B1364417
theorem B680251 : Blo 603293 680251 := bstep (se 1 (by rfl) ⟨510188, by rfl⟩ : syracuseStep 680251 = 1020377) B1020377
theorem B909641 : Blo 603293 909641 := bstep (se 2 (by rfl) ⟨341115, by rfl⟩ : syracuseStep 909641 = 682231) B682231
theorem B909755 : Blo 603293 909755 := bstep (se 1 (by rfl) ⟨682316, by rfl⟩ : syracuseStep 909755 = 1364633) B1364633
theorem B14016989 : Blo 603293 14016989 := bstep (se 3 (by rfl) ⟨2628185, by rfl⟩ : syracuseStep 14016989 = 5256371) B5256371
theorem B909815 : Blo 603293 909815 := bstep (se 1 (by rfl) ⟨682361, by rfl⟩ : syracuseStep 909815 = 1364723) B1364723
theorem B6644227 : Blo 603293 6644227 := bstep (se 1 (by rfl) ⟨4983170, by rfl⟩ : syracuseStep 6644227 = 9966341) B9966341
theorem B909839 : Blo 603293 909839 := bstep (se 1 (by rfl) ⟨682379, by rfl⟩ : syracuseStep 909839 = 1364759) B1364759
theorem B1630763 : Blo 603293 1630763 := bstep (se 1 (by rfl) ⟨1223072, by rfl⟩ : syracuseStep 1630763 = 2446145) B2446145
theorem B1532459 : Blo 603293 1532459 := bstep (se 1 (by rfl) ⟨1149344, by rfl⟩ : syracuseStep 1532459 = 2298689) B2298689
theorem B909881 : Blo 603293 909881 := bstep (se 2 (by rfl) ⟨341205, by rfl⟩ : syracuseStep 909881 = 682411) B682411
theorem B909959 : Blo 603293 909959 := bstep (se 1 (by rfl) ⟨682469, by rfl⟩ : syracuseStep 909959 = 1364939) B1364939
theorem B615047 : Blo 603293 615047 := bstep (se 1 (by rfl) ⟨461285, by rfl⟩ : syracuseStep 615047 = 922571) B922571
theorem B909995 : Blo 603293 909995 := bstep (se 1 (by rfl) ⟨682496, by rfl⟩ : syracuseStep 909995 = 1364993) B1364993
theorem B6906545 : Blo 603293 6906545 := bstep (se 2 (by rfl) ⟨2589954, by rfl⟩ : syracuseStep 6906545 = 5179909) B5179909
theorem B910025 : Blo 603293 910025 := bstep (se 2 (by rfl) ⟨341259, by rfl⟩ : syracuseStep 910025 = 682519) B682519
theorem B680719 : Blo 603293 680719 := bstep (se 1 (by rfl) ⟨510539, by rfl⟩ : syracuseStep 680719 = 1021079) B1021079
theorem B910139 : Blo 603293 910139 := bstep (se 1 (by rfl) ⟨682604, by rfl⟩ : syracuseStep 910139 = 1365209) B1365209
theorem B910199 : Blo 603293 910199 := bstep (se 1 (by rfl) ⟨682649, by rfl⟩ : syracuseStep 910199 = 1365299) B1365299
theorem B910223 : Blo 603293 910223 := bstep (se 1 (by rfl) ⟨682667, by rfl⟩ : syracuseStep 910223 = 1365335) B1365335
theorem B5235619 : Blo 603293 5235619 := bstep (se 1 (by rfl) ⟨3926714, by rfl⟩ : syracuseStep 5235619 = 7853429) B7853429
theorem B910265 : Blo 603293 910265 := bstep (se 2 (by rfl) ⟨341349, by rfl⟩ : syracuseStep 910265 = 682699) B682699
theorem B3072977 : Blo 603293 3072977 := bstep (se 2 (by rfl) ⟨1152366, by rfl⟩ : syracuseStep 3072977 = 2304733) B2304733
theorem B910343 : Blo 603293 910343 := bstep (se 1 (by rfl) ⟨682757, by rfl⟩ : syracuseStep 910343 = 1365515) B1365515
theorem B910379 : Blo 603293 910379 := bstep (se 1 (by rfl) ⟨682784, by rfl⟩ : syracuseStep 910379 = 1365569) B1365569
theorem B910409 : Blo 603293 910409 := bstep (se 2 (by rfl) ⟨341403, by rfl⟩ : syracuseStep 910409 = 682807) B682807
theorem B910523 : Blo 603293 910523 := bstep (se 1 (by rfl) ⟨682892, by rfl⟩ : syracuseStep 910523 = 1365785) B1365785
theorem B910583 : Blo 603293 910583 := bstep (se 1 (by rfl) ⟨682937, by rfl⟩ : syracuseStep 910583 = 1365875) B1365875
theorem B681223 : Blo 603293 681223 := bstep (se 1 (by rfl) ⟨510917, by rfl⟩ : syracuseStep 681223 = 1021835) B1021835
theorem B910607 : Blo 603293 910607 := bstep (se 1 (by rfl) ⟨682955, by rfl⟩ : syracuseStep 910607 = 1365911) B1365911
theorem B910649 : Blo 603293 910649 := bstep (se 2 (by rfl) ⟨341493, by rfl⟩ : syracuseStep 910649 = 682987) B682987
theorem B910727 : Blo 603293 910727 := bstep (se 1 (by rfl) ⟨683045, by rfl⟩ : syracuseStep 910727 = 1366091) B1366091
theorem B910763 : Blo 603293 910763 := bstep (se 1 (by rfl) ⟨683072, by rfl⟩ : syracuseStep 910763 = 1366145) B1366145
theorem B681403 : Blo 603293 681403 := bstep (se 1 (by rfl) ⟨511052, by rfl⟩ : syracuseStep 681403 = 1022105) B1022105
theorem B910793 : Blo 603293 910793 := bstep (se 2 (by rfl) ⟨341547, by rfl⟩ : syracuseStep 910793 = 683095) B683095
theorem B2582027 : Blo 603293 2582027 := bstep (se 1 (by rfl) ⟨1936520, by rfl⟩ : syracuseStep 2582027 = 3873041) B3873041
theorem B1533451 : Blo 603293 1533451 := bstep (se 1 (by rfl) ⟨1150088, by rfl⟩ : syracuseStep 1533451 = 2300177) B2300177
theorem B910907 : Blo 603293 910907 := bstep (se 1 (by rfl) ⟨683180, by rfl⟩ : syracuseStep 910907 = 1366361) B1366361
theorem B1533593 : Blo 603293 1533593 := bstep (se 2 (by rfl) ⟨575097, by rfl⟩ : syracuseStep 1533593 = 1150195) B1150195
theorem B1533755 : Blo 603293 1533755 := bstep (se 1 (by rfl) ⟨1150316, by rfl⟩ : syracuseStep 1533755 = 2300633) B2300633
theorem B2942855 : Blo 603293 2942855 := bstep (se 1 (by rfl) ⟨2207141, by rfl⟩ : syracuseStep 2942855 = 4414283) B4414283
theorem B681871 : Blo 603293 681871 := bstep (se 1 (by rfl) ⟨511403, by rfl⟩ : syracuseStep 681871 = 1022807) B1022807
theorem B1534099 : Blo 603293 1534099 := bstep (se 1 (by rfl) ⟨1150574, by rfl⟩ : syracuseStep 1534099 = 2301149) B2301149
theorem B1534241 : Blo 603293 1534241 := bstep (se 2 (by rfl) ⟨575340, by rfl⟩ : syracuseStep 1534241 = 1150681) B1150681
theorem B682375 : Blo 603293 682375 := bstep (se 1 (by rfl) ⟨511781, by rfl⟩ : syracuseStep 682375 = 1023563) B1023563
theorem B682555 : Blo 603293 682555 := bstep (se 1 (by rfl) ⟨511916, by rfl⟩ : syracuseStep 682555 = 1023833) B1023833
theorem B4582007 : Blo 603293 4582007 := bstep (se 1 (by rfl) ⟨3436505, by rfl⟩ : syracuseStep 4582007 = 6873011) B6873011
theorem B7269041 : Blo 603293 7269041 := bstep (se 2 (by rfl) ⟨2725890, by rfl⟩ : syracuseStep 7269041 = 5451781) B5451781
theorem B1633067 : Blo 603293 1633067 := bstep (se 1 (by rfl) ⟨1224800, by rfl⟩ : syracuseStep 1633067 = 2449601) B2449601
theorem B683023 : Blo 603293 683023 := bstep (se 1 (by rfl) ⟨512267, by rfl⟩ : syracuseStep 683023 = 1024535) B1024535
theorem B1535233 : Blo 603293 1535233 := bstep (se 2 (by rfl) ⟨575712, by rfl⟩ : syracuseStep 1535233 = 1151425) B1151425
theorem B2911547 : Blo 603293 2911547 := bstep (se 1 (by rfl) ⟨2183660, by rfl⟩ : syracuseStep 2911547 = 4367321) B4367321
theorem B4582979 : Blo 603293 4582979 := bstep (se 1 (by rfl) ⟨3437234, by rfl⟩ : syracuseStep 4582979 = 6874469) B6874469
theorem B1535831 : Blo 603293 1535831 := bstep (se 1 (by rfl) ⟨1151873, by rfl⟩ : syracuseStep 1535831 = 2303747) B2303747
theorem B5173145 : Blo 603293 5173145 := bstep (se 2 (by rfl) ⟨1939929, by rfl⟩ : syracuseStep 5173145 = 3879859) B3879859
theorem B1536043 : Blo 603293 1536043 := bstep (se 1 (by rfl) ⟨1152032, by rfl⟩ : syracuseStep 1536043 = 2304065) B2304065
theorem B1536185 : Blo 603293 1536185 := bstep (se 2 (by rfl) ⟨576069, by rfl⟩ : syracuseStep 1536185 = 1152139) B1152139
theorem B6877385 : Blo 603293 6877385 := bstep (se 2 (by rfl) ⟨2579019, by rfl⟩ : syracuseStep 6877385 = 5158039) B5158039
theorem B16576913 : Blo 603293 16576913 := bstep (se 2 (by rfl) ⟨6216342, by rfl⟩ : syracuseStep 16576913 = 12432685) B12432685
theorem B3437099 : Blo 603293 3437099 := bstep (se 1 (by rfl) ⟨2577824, by rfl⟩ : syracuseStep 3437099 = 5155649) B5155649
theorem B2585155 : Blo 603293 2585155 := bstep (se 1 (by rfl) ⟨1938866, by rfl⟩ : syracuseStep 2585155 = 3877733) B3877733
theorem B2585479 : Blo 603293 2585479 := bstep (se 1 (by rfl) ⟨1939109, by rfl⟩ : syracuseStep 2585479 = 3878219) B3878219
theorem B1537177 : Blo 603293 1537177 := bstep (se 2 (by rfl) ⟨576441, by rfl⟩ : syracuseStep 1537177 = 1152883) B1152883
theorem B3503513 : Blo 603293 3503513 := bstep (se 2 (by rfl) ⟨1313817, by rfl⟩ : syracuseStep 3503513 = 2627635) B2627635
theorem B816841 : Blo 603293 816841 := bstep (se 2 (by rfl) ⟨306315, by rfl⟩ : syracuseStep 816841 = 612631) B612631
theorem B2586401 : Blo 603293 2586401 := bstep (se 2 (by rfl) ⟨969900, by rfl⟩ : syracuseStep 2586401 = 1939801) B1939801
theorem B2914163 : Blo 603293 2914163 := bstep (se 1 (by rfl) ⟨2185622, by rfl⟩ : syracuseStep 2914163 = 4371245) B4371245
theorem B3438557 : Blo 603293 3438557 := bstep (se 3 (by rfl) ⟨644729, by rfl⟩ : syracuseStep 3438557 = 1289459) B1289459
theorem B2292083 : Blo 603293 2292083 := bstep (se 1 (by rfl) ⟨1719062, by rfl⟩ : syracuseStep 2292083 = 3438125) B3438125
theorem B3439057 : Blo 603293 3439057 := bstep (se 2 (by rfl) ⟨1289646, by rfl⟩ : syracuseStep 3439057 = 2579293) B2579293
theorem B3275579 : Blo 603293 3275579 := bstep (se 1 (by rfl) ⟨2456684, by rfl⟩ : syracuseStep 3275579 = 4913369) B4913369
theorem B2620295 : Blo 603293 2620295 := bstep (se 1 (by rfl) ⟨1965221, by rfl⟩ : syracuseStep 2620295 = 3930443) B3930443
theorem B6880301 : Blo 603293 6880301 := bstep (se 3 (by rfl) ⟨1290056, by rfl⟩ : syracuseStep 6880301 = 2580113) B2580113
theorem B5176493 : Blo 603293 5176493 := bstep (se 3 (by rfl) ⟨970592, by rfl⟩ : syracuseStep 5176493 = 1941185) B1941185
theorem B7765307 : Blo 603293 7765307 := bstep (se 1 (by rfl) ⟨5823980, by rfl⟩ : syracuseStep 7765307 = 11647961) B11647961
theorem B5799377 : Blo 603293 5799377 := bstep (se 2 (by rfl) ⟨2174766, by rfl⟩ : syracuseStep 5799377 = 4349533) B4349533
theorem B1146383 : Blo 603293 1146383 := bstep (se 1 (by rfl) ⟨859787, by rfl⟩ : syracuseStep 1146383 = 1719575) B1719575
theorem B1474195 : Blo 603293 1474195 := bstep (se 1 (by rfl) ⟨1105646, by rfl⟩ : syracuseStep 1474195 = 2211293) B2211293
theorem B1769161 : Blo 603293 1769161 := bstep (se 2 (by rfl) ⟨663435, by rfl⟩ : syracuseStep 1769161 = 1326871) B1326871
theorem B2752237 : Blo 603293 2752237 := bstep (se 3 (by rfl) ⟨516044, by rfl⟩ : syracuseStep 2752237 = 1032089) B1032089
theorem B917291 : Blo 603293 917291 := bstep (se 1 (by rfl) ⟨687968, by rfl⟩ : syracuseStep 917291 = 1375937) B1375937
theorem B4587353 : Blo 603293 4587353 := bstep (se 2 (by rfl) ⟨1720257, by rfl⟩ : syracuseStep 4587353 = 3440515) B3440515
theorem B1146899 : Blo 603293 1146899 := bstep (se 1 (by rfl) ⟨860174, by rfl⟩ : syracuseStep 1146899 = 1720349) B1720349
theorem B2326607 : Blo 603293 2326607 := bstep (se 1 (by rfl) ⟨1744955, by rfl⟩ : syracuseStep 2326607 = 3489911) B3489911
theorem B1147051 : Blo 603293 1147051 := bstep (se 1 (by rfl) ⟨860288, by rfl⟩ : syracuseStep 1147051 = 1720577) B1720577
theorem B2294027 : Blo 603293 2294027 := bstep (se 1 (by rfl) ⟨1720520, by rfl⟩ : syracuseStep 2294027 = 3441041) B3441041
theorem B1638785 : Blo 603293 1638785 := bstep (se 2 (by rfl) ⟨614544, by rfl⟩ : syracuseStep 1638785 = 1229089) B1229089
theorem B1147279 : Blo 603293 1147279 := bstep (se 1 (by rfl) ⟨860459, by rfl⟩ : syracuseStep 1147279 = 1720919) B1720919
theorem B1147355 : Blo 603293 1147355 := bstep (se 1 (by rfl) ⟨860516, by rfl⟩ : syracuseStep 1147355 = 1721033) B1721033
theorem B984071 : Blo 603293 984071 := bstep (se 1 (by rfl) ⟨738053, by rfl⟩ : syracuseStep 984071 = 1476107) B1476107
theorem B44205101 : Blo 603293 44205101 := bstep (se 3 (by rfl) ⟨8288456, by rfl⟩ : syracuseStep 44205101 = 16576913) B16576913
theorem B6980825 : Blo 603293 6980825 := bstep (se 2 (by rfl) ⟨2617809, by rfl⟩ : syracuseStep 6980825 = 5235619) B5235619
theorem B3868019 : Blo 603293 3868019 := bstep (se 1 (by rfl) ⟨2901014, by rfl⟩ : syracuseStep 3868019 = 5802029) B5802029
theorem B1836431 : Blo 603293 1836431 := bstep (se 1 (by rfl) ⟨1377323, by rfl⟩ : syracuseStep 1836431 = 2754647) B2754647
theorem B2295485 : Blo 603293 2295485 := bstep (se 3 (by rfl) ⟨430403, by rfl⟩ : syracuseStep 2295485 = 860807) B860807
theorem B1640125 : Blo 603293 1640125 := bstep (se 3 (by rfl) ⟨307523, by rfl⟩ : syracuseStep 1640125 = 615047) B615047
theorem B3442499 : Blo 603293 3442499 := bstep (se 1 (by rfl) ⟨2581874, by rfl⟩ : syracuseStep 3442499 = 5163749) B5163749
theorem B1018217 : Blo 603293 1018217 := bstep (se 2 (by rfl) ⟨381831, by rfl⟩ : syracuseStep 1018217 = 763663) B763663
theorem B1935905 : Blo 603293 1935905 := bstep (se 2 (by rfl) ⟨725964, by rfl⟩ : syracuseStep 1935905 = 1451929) B1451929
theorem B1018615 : Blo 603293 1018615 := bstep (se 1 (by rfl) ⟨763961, by rfl⟩ : syracuseStep 1018615 = 1527923) B1527923
theorem B1051499 : Blo 603293 1051499 := bstep (se 1 (by rfl) ⟨788624, by rfl⟩ : syracuseStep 1051499 = 1577249) B1577249
theorem B1018811 : Blo 603293 1018811 := bstep (se 1 (by rfl) ⟨764108, by rfl⟩ : syracuseStep 1018811 = 1528217) B1528217
theorem B1936315 : Blo 603293 1936315 := bstep (se 1 (by rfl) ⟨1452236, by rfl⟩ : syracuseStep 1936315 = 2904473) B2904473
theorem B1018919 : Blo 603293 1018919 := bstep (se 1 (by rfl) ⟨764189, by rfl⟩ : syracuseStep 1018919 = 1528379) B1528379
theorem B1019209 : Blo 603293 1019209 := bstep (se 2 (by rfl) ⟨382203, by rfl⟩ : syracuseStep 1019209 = 764407) B764407
theorem B1019243 : Blo 603293 1019243 := bstep (se 1 (by rfl) ⟨764432, by rfl⟩ : syracuseStep 1019243 = 1528865) B1528865
theorem B2297231 : Blo 603293 2297231 := bstep (se 1 (by rfl) ⟨1722923, by rfl⟩ : syracuseStep 2297231 = 3445847) B3445847
theorem B1019641 : Blo 603293 1019641 := bstep (se 2 (by rfl) ⟨382365, by rfl⟩ : syracuseStep 1019641 = 764731) B764731
theorem B2461549 : Blo 603293 2461549 := bstep (se 3 (by rfl) ⟨461540, by rfl⟩ : syracuseStep 2461549 = 923081) B923081
theorem B1150939 : Blo 603293 1150939 := bstep (se 1 (by rfl) ⟨863204, by rfl⟩ : syracuseStep 1150939 = 1726409) B1726409
theorem B1019911 : Blo 603293 1019911 := bstep (se 1 (by rfl) ⟨764933, by rfl⟩ : syracuseStep 1019911 = 1529867) B1529867
theorem B1150985 : Blo 603293 1150985 := bstep (se 2 (by rfl) ⟨431619, by rfl⟩ : syracuseStep 1150985 = 863239) B863239
theorem B13111307 : Blo 603293 13111307 := bstep (se 1 (by rfl) ⟨9833480, by rfl⟩ : syracuseStep 13111307 = 19666961) B19666961
theorem B7770275 : Blo 603293 7770275 := bstep (se 1 (by rfl) ⟨5827706, by rfl⟩ : syracuseStep 7770275 = 11655413) B11655413
theorem B1937675 : Blo 603293 1937675 := bstep (se 1 (by rfl) ⟨1453256, by rfl⟩ : syracuseStep 1937675 = 2906513) B2906513
theorem B1151327 : Blo 603293 1151327 := bstep (se 1 (by rfl) ⟨863495, by rfl⟩ : syracuseStep 1151327 = 1726991) B1726991
theorem B1020343 : Blo 603293 1020343 := bstep (se 1 (by rfl) ⟨765257, by rfl⟩ : syracuseStep 1020343 = 1530515) B1530515
theorem B1380827 : Blo 603293 1380827 := bstep (se 1 (by rfl) ⟨1035620, by rfl⟩ : syracuseStep 1380827 = 2071241) B2071241
theorem B1937945 : Blo 603293 1937945 := bstep (se 2 (by rfl) ⟨726729, by rfl⟩ : syracuseStep 1937945 = 1453459) B1453459
theorem B2298401 : Blo 603293 2298401 := bstep (se 2 (by rfl) ⟨861900, by rfl⟩ : syracuseStep 2298401 = 1723801) B1723801
theorem B922151 : Blo 603293 922151 := bstep (se 1 (by rfl) ⟨691613, by rfl⟩ : syracuseStep 922151 = 1383227) B1383227
theorem B1020539 : Blo 603293 1020539 := bstep (se 1 (by rfl) ⟨765404, by rfl⟩ : syracuseStep 1020539 = 1530809) B1530809
theorem B1938059 : Blo 603293 1938059 := bstep (se 1 (by rfl) ⟨1453544, by rfl⟩ : syracuseStep 1938059 = 2907089) B2907089
theorem B10490579 : Blo 603293 10490579 := bstep (se 1 (by rfl) ⟨7867934, by rfl⟩ : syracuseStep 10490579 = 15735869) B15735869
theorem B2298719 : Blo 603293 2298719 := bstep (se 1 (by rfl) ⟨1724039, by rfl⟩ : syracuseStep 2298719 = 3448079) B3448079
theorem B2036663 : Blo 603293 2036663 := bstep (se 1 (by rfl) ⟨1527497, by rfl⟩ : syracuseStep 2036663 = 3054995) B3054995
theorem B3871709 : Blo 603293 3871709 := bstep (se 3 (by rfl) ⟨725945, by rfl⟩ : syracuseStep 3871709 = 1451891) B1451891
theorem B2298887 : Blo 603293 2298887 := bstep (se 1 (by rfl) ⟨1724165, by rfl⟩ : syracuseStep 2298887 = 3448331) B3448331
theorem B1020937 : Blo 603293 1020937 := bstep (se 2 (by rfl) ⟨382851, by rfl⟩ : syracuseStep 1020937 = 765703) B765703
theorem B1021099 : Blo 603293 1021099 := bstep (se 1 (by rfl) ⟨765824, by rfl⟩ : syracuseStep 1021099 = 1531649) B1531649
theorem B922985 : Blo 603293 922985 := bstep (se 2 (by rfl) ⟨346119, by rfl⟩ : syracuseStep 922985 = 692239) B692239
theorem B1152443 : Blo 603293 1152443 := bstep (se 1 (by rfl) ⟨864332, by rfl⟩ : syracuseStep 1152443 = 1728665) B1728665
theorem B1021403 : Blo 603293 1021403 := bstep (se 1 (by rfl) ⟨766052, by rfl⟩ : syracuseStep 1021403 = 1532105) B1532105
theorem B2299373 : Blo 603293 2299373 := bstep (se 3 (by rfl) ⟨431132, by rfl⟩ : syracuseStep 2299373 = 862265) B862265
theorem B2037257 : Blo 603293 2037257 := bstep (se 2 (by rfl) ⟨763971, by rfl⟩ : syracuseStep 2037257 = 1527943) B1527943
theorem B9344659 : Blo 603293 9344659 := bstep (se 1 (by rfl) ⟨7008494, by rfl⟩ : syracuseStep 9344659 = 14016989) B14016989
theorem B1021639 : Blo 603293 1021639 := bstep (se 1 (by rfl) ⟨766229, by rfl⟩ : syracuseStep 1021639 = 1532459) B1532459
theorem B1087175 : Blo 603293 1087175 := bstep (se 1 (by rfl) ⟨815381, by rfl⟩ : syracuseStep 1087175 = 1630763) B1630763
theorem B2299691 : Blo 603293 2299691 := bstep (se 1 (by rfl) ⟨1724768, by rfl⟩ : syracuseStep 2299691 = 3449537) B3449537
theorem B1021801 : Blo 603293 1021801 := bstep (se 2 (by rfl) ⟨383175, by rfl⟩ : syracuseStep 1021801 = 766351) B766351
theorem B727003 : Blo 603293 727003 := bstep (se 1 (by rfl) ⟨545252, by rfl⟩ : syracuseStep 727003 = 1090505) B1090505
theorem B4593671 : Blo 603293 4593671 := bstep (se 1 (by rfl) ⟨3445253, by rfl⟩ : syracuseStep 4593671 = 6890507) B6890507
theorem B3446873 : Blo 603293 3446873 := bstep (se 2 (by rfl) ⟨1292577, by rfl⟩ : syracuseStep 3446873 = 2585155) B2585155
theorem B4987109 : Blo 603293 4987109 := bstep (se 4 (by rfl) ⟨467541, by rfl⟩ : syracuseStep 4987109 = 935083) B935083
theorem B2038121 : Blo 603293 2038121 := bstep (se 2 (by rfl) ⟨764295, by rfl⟩ : syracuseStep 2038121 = 1528591) B1528591
theorem B6199685 : Blo 603293 6199685 := bstep (se 4 (by rfl) ⟨581220, by rfl⟩ : syracuseStep 6199685 = 1162441) B1162441
theorem B10492295 : Blo 603293 10492295 := bstep (se 1 (by rfl) ⟨7869221, by rfl⟩ : syracuseStep 10492295 = 15738443) B15738443
theorem B1022395 : Blo 603293 1022395 := bstep (se 1 (by rfl) ⟨766796, by rfl⟩ : syracuseStep 1022395 = 1533593) B1533593
theorem B4594157 : Blo 603293 4594157 := bstep (se 3 (by rfl) ⟨861404, by rfl⟩ : syracuseStep 4594157 = 1722809) B1722809
theorem B3447305 : Blo 603293 3447305 := bstep (se 2 (by rfl) ⟨1292739, by rfl⟩ : syracuseStep 3447305 = 2585479) B2585479
theorem B1022503 : Blo 603293 1022503 := bstep (se 1 (by rfl) ⟨766877, by rfl⟩ : syracuseStep 1022503 = 1533755) B1533755
theorem B1022827 : Blo 603293 1022827 := bstep (se 1 (by rfl) ⟨767120, by rfl⟩ : syracuseStep 1022827 = 1534241) B1534241
theorem B2038715 : Blo 603293 2038715 := bstep (se 1 (by rfl) ⟨1529036, by rfl⟩ : syracuseStep 2038715 = 3058073) B3058073
theorem B3054671 : Blo 603293 3054671 := bstep (se 1 (by rfl) ⟨2291003, by rfl⟩ : syracuseStep 3054671 = 4582007) B4582007
theorem B1088711 : Blo 603293 1088711 := bstep (se 1 (by rfl) ⟨816533, by rfl⟩ : syracuseStep 1088711 = 1633067) B1633067
theorem B1941031 : Blo 603293 1941031 := bstep (se 1 (by rfl) ⟨1455773, by rfl⟩ : syracuseStep 1941031 = 2911547) B2911547
theorem B1089121 : Blo 603293 1089121 := bstep (se 2 (by rfl) ⟨408420, by rfl⟩ : syracuseStep 1089121 = 816841) B816841
theorem B3055319 : Blo 603293 3055319 := bstep (se 1 (by rfl) ⟨2291489, by rfl⟩ : syracuseStep 3055319 = 4582979) B4582979
theorem B2301803 : Blo 603293 2301803 := bstep (se 1 (by rfl) ⟨1726352, by rfl⟩ : syracuseStep 2301803 = 3452705) B3452705
theorem B1023887 : Blo 603293 1023887 := bstep (se 1 (by rfl) ⟨767915, by rfl⟩ : syracuseStep 1023887 = 1535831) B1535831
theorem B3448763 : Blo 603293 3448763 := bstep (se 1 (by rfl) ⟨2586572, by rfl⟩ : syracuseStep 3448763 = 5173145) B5173145
theorem B1024123 : Blo 603293 1024123 := bstep (se 1 (by rfl) ⟨768092, by rfl⟩ : syracuseStep 1024123 = 1536185) B1536185
theorem B4596101 : Blo 603293 4596101 := bstep (se 4 (by rfl) ⟨430884, by rfl⟩ : syracuseStep 4596101 = 861769) B861769
theorem B2040443 : Blo 603293 2040443 := bstep (se 1 (by rfl) ⟨1530332, by rfl⟩ : syracuseStep 2040443 = 3060665) B3060665
theorem B3875501 : Blo 603293 3875501 := bstep (se 3 (by rfl) ⟨726656, by rfl⟩ : syracuseStep 3875501 = 1453313) B1453313
theorem B2040605 : Blo 603293 2040605 := bstep (se 3 (by rfl) ⟨382613, by rfl⟩ : syracuseStep 2040605 = 765227) B765227
theorem B4596587 : Blo 603293 4596587 := bstep (se 1 (by rfl) ⟨3447440, by rfl⟩ : syracuseStep 4596587 = 6894881) B6894881
theorem B3875759 : Blo 603293 3875759 := bstep (se 1 (by rfl) ⟨2906819, by rfl⟩ : syracuseStep 3875759 = 5813639) B5813639
theorem B2335675 : Blo 603293 2335675 := bstep (se 1 (by rfl) ⟨1751756, by rfl⟩ : syracuseStep 2335675 = 3503513) B3503513
theorem B1942775 : Blo 603293 1942775 := bstep (se 1 (by rfl) ⟨1457081, by rfl⟩ : syracuseStep 1942775 = 2914163) B2914163
theorem B1516943 : Blo 603293 1516943 := bstep (se 1 (by rfl) ⟨1137707, by rfl⟩ : syracuseStep 1516943 = 2275415) B2275415
theorem B5187017 : Blo 603293 5187017 := bstep (se 2 (by rfl) ⟨1945131, by rfl⟩ : syracuseStep 5187017 = 3890263) B3890263
theorem B2041307 : Blo 603293 2041307 := bstep (se 1 (by rfl) ⟨1530980, by rfl⟩ : syracuseStep 2041307 = 3061961) B3061961
theorem B3679867 : Blo 603293 3679867 := bstep (se 1 (by rfl) ⟨2759900, by rfl⟩ : syracuseStep 3679867 = 5519801) B5519801
theorem B1746863 : Blo 603293 1746863 := bstep (se 1 (by rfl) ⟨1310147, by rfl⟩ : syracuseStep 1746863 = 2620295) B2620295
theorem B3450995 : Blo 603293 3450995 := bstep (se 1 (by rfl) ⟨2588246, by rfl⟩ : syracuseStep 3450995 = 5176493) B5176493
theorem B2042009 : Blo 603293 2042009 := bstep (se 2 (by rfl) ⟨765753, by rfl⟩ : syracuseStep 2042009 = 1531507) B1531507
theorem B2304247 : Blo 603293 2304247 := bstep (se 1 (by rfl) ⟨1728185, by rfl⟩ : syracuseStep 2304247 = 3456371) B3456371
theorem B37234997 : Blo 603293 37234997 := bstep (se 5 (by rfl) ⟨1745390, by rfl⟩ : syracuseStep 37234997 = 3490781) B3490781
theorem B764255 : Blo 603293 764255 := bstep (se 1 (by rfl) ⟨573191, by rfl⟩ : syracuseStep 764255 = 1146383) B1146383
theorem B1288553 : Blo 603293 1288553 := bstep (se 2 (by rfl) ⟨483207, by rfl⟩ : syracuseStep 1288553 = 966415) B966415
theorem B2304521 : Blo 603293 2304521 := bstep (se 2 (by rfl) ⟨864195, by rfl⟩ : syracuseStep 2304521 = 1728391) B1728391
theorem B2304551 : Blo 603293 2304551 := bstep (se 1 (by rfl) ⟨1728413, by rfl⟩ : syracuseStep 2304551 = 3456827) B3456827
theorem B3058235 : Blo 603293 3058235 := bstep (se 1 (by rfl) ⟨2293676, by rfl⟩ : syracuseStep 3058235 = 4587353) B4587353
theorem B4598531 : Blo 603293 4598531 := bstep (se 1 (by rfl) ⟨3448898, by rfl⟩ : syracuseStep 4598531 = 6897797) B6897797
theorem B89303957 : Blo 603293 89303957 := bstep (se 6 (by rfl) ⟨2093061, by rfl⟩ : syracuseStep 89303957 = 4186123) B4186123
theorem B1289135 : Blo 603293 1289135 := bstep (se 1 (by rfl) ⟨966851, by rfl⟩ : syracuseStep 1289135 = 1933703) B1933703
theorem B7187429 : Blo 603293 7187429 := bstep (se 4 (by rfl) ⟨673821, by rfl⟩ : syracuseStep 7187429 = 1347643) B1347643
theorem B3058883 : Blo 603293 3058883 := bstep (se 1 (by rfl) ⟨2294162, by rfl⟩ : syracuseStep 3058883 = 4588325) B4588325
theorem B2305219 : Blo 603293 2305219 := bstep (se 1 (by rfl) ⟨1728914, by rfl⟩ : syracuseStep 2305219 = 3457829) B3457829
theorem B7384355 : Blo 603293 7384355 := bstep (se 1 (by rfl) ⟨5538266, by rfl⟩ : syracuseStep 7384355 = 11076533) B11076533
theorem B2043197 : Blo 603293 2043197 := bstep (se 3 (by rfl) ⟨383099, by rfl⟩ : syracuseStep 2043197 = 766199) B766199
theorem B8858969 : Blo 603293 8858969 := bstep (se 2 (by rfl) ⟨3322113, by rfl⟩ : syracuseStep 8858969 = 6644227) B6644227
theorem B2305523 : Blo 603293 2305523 := bstep (se 1 (by rfl) ⟨1729142, by rfl⟩ : syracuseStep 2305523 = 3458285) B3458285
theorem B1945235 : Blo 603293 1945235 := bstep (se 1 (by rfl) ⟨1458926, by rfl⟩ : syracuseStep 1945235 = 2917853) B2917853
theorem B6565819 : Blo 603293 6565819 := bstep (se 1 (by rfl) ⟨4924364, by rfl⟩ : syracuseStep 6565819 = 9848729) B9848729
theorem B1454159 : Blo 603293 1454159 := bstep (se 1 (by rfl) ⟨1090619, by rfl⟩ : syracuseStep 1454159 = 2181239) B2181239
theorem B2044061 : Blo 603293 2044061 := bstep (se 3 (by rfl) ⟨383261, by rfl⟩ : syracuseStep 2044061 = 766523) B766523
theorem B1454689 : Blo 603293 1454689 := bstep (se 2 (by rfl) ⟨545508, by rfl⟩ : syracuseStep 1454689 = 1091017) B1091017
theorem B2044601 : Blo 603293 2044601 := bstep (se 2 (by rfl) ⟨766725, by rfl⟩ : syracuseStep 2044601 = 1533451) B1533451
theorem B2077369 : Blo 603293 2077369 := bstep (se 2 (by rfl) ⟨779013, by rfl⟩ : syracuseStep 2077369 = 1558027) B1558027
theorem B14398361 : Blo 603293 14398361 := bstep (se 2 (by rfl) ⟨5399385, by rfl⟩ : syracuseStep 14398361 = 10798771) B10798771
theorem B766903 : Blo 603293 766903 := bstep (se 1 (by rfl) ⟨575177, by rfl⟩ : syracuseStep 766903 = 1150355) B1150355
theorem B5518489 : Blo 603293 5518489 := bstep (se 2 (by rfl) ⟨2069433, by rfl⟩ : syracuseStep 5518489 = 4138867) B4138867
theorem B603311 : Blo 603293 603311 := bstep (se 1 (by rfl) ⟨452483, by rfl⟩ : syracuseStep 603311 = 904967) B904967
theorem B603335 : Blo 603293 603335 := bstep (se 1 (by rfl) ⟨452501, by rfl⟩ : syracuseStep 603335 = 905003) B905003
theorem B603355 : Blo 603293 603355 := bstep (se 1 (by rfl) ⟨452516, by rfl⟩ : syracuseStep 603355 = 905033) B905033
theorem B2045195 : Blo 603293 2045195 := bstep (se 1 (by rfl) ⟨1533896, by rfl⟩ : syracuseStep 2045195 = 3067793) B3067793
theorem B603431 : Blo 603293 603431 := bstep (se 1 (by rfl) ⟨452573, by rfl⟩ : syracuseStep 603431 = 905147) B905147
theorem B603471 : Blo 603293 603471 := bstep (se 1 (by rfl) ⟨452603, by rfl⟩ : syracuseStep 603471 = 905207) B905207
theorem B603487 : Blo 603293 603487 := bstep (se 1 (by rfl) ⟨452615, by rfl⟩ : syracuseStep 603487 = 905231) B905231
theorem B603515 : Blo 603293 603515 := bstep (se 1 (by rfl) ⟨452636, by rfl⟩ : syracuseStep 603515 = 905273) B905273
theorem B1291663 : Blo 603293 1291663 := bstep (se 1 (by rfl) ⟨968747, by rfl⟩ : syracuseStep 1291663 = 1937495) B1937495
theorem B603567 : Blo 603293 603567 := bstep (se 1 (by rfl) ⟨452675, by rfl⟩ : syracuseStep 603567 = 905351) B905351
theorem B603591 : Blo 603293 603591 := bstep (se 1 (by rfl) ⟨452693, by rfl⟩ : syracuseStep 603591 = 905387) B905387
theorem B603611 : Blo 603293 603611 := bstep (se 1 (by rfl) ⟨452708, by rfl⟩ : syracuseStep 603611 = 905417) B905417
theorem B2045465 : Blo 603293 2045465 := bstep (se 2 (by rfl) ⟨767049, by rfl⟩ : syracuseStep 2045465 = 1534099) B1534099
theorem B603687 : Blo 603293 603687 := bstep (se 1 (by rfl) ⟨452765, by rfl⟩ : syracuseStep 603687 = 905531) B905531
theorem B603727 : Blo 603293 603727 := bstep (se 1 (by rfl) ⟨452795, by rfl⟩ : syracuseStep 603727 = 905591) B905591
theorem B603743 : Blo 603293 603743 := bstep (se 1 (by rfl) ⟨452807, by rfl⟩ : syracuseStep 603743 = 905615) B905615
theorem B603771 : Blo 603293 603771 := bstep (se 1 (by rfl) ⟨452828, by rfl⟩ : syracuseStep 603771 = 905657) B905657
theorem B603823 : Blo 603293 603823 := bstep (se 1 (by rfl) ⟨452867, by rfl⟩ : syracuseStep 603823 = 905735) B905735
theorem B603847 : Blo 603293 603847 := bstep (se 1 (by rfl) ⟨452885, by rfl⟩ : syracuseStep 603847 = 905771) B905771
theorem B1357523 : Blo 603293 1357523 := bstep (se 1 (by rfl) ⟨1018142, by rfl⟩ : syracuseStep 1357523 = 2036285) B2036285
theorem B603867 : Blo 603293 603867 := bstep (se 1 (by rfl) ⟨452900, by rfl⟩ : syracuseStep 603867 = 905801) B905801
theorem B603943 : Blo 603293 603943 := bstep (se 1 (by rfl) ⟨452957, by rfl⟩ : syracuseStep 603943 = 905915) B905915
theorem B603983 : Blo 603293 603983 := bstep (se 1 (by rfl) ⟨452987, by rfl⟩ : syracuseStep 603983 = 905975) B905975
theorem B603999 : Blo 603293 603999 := bstep (se 1 (by rfl) ⟨452999, by rfl⟩ : syracuseStep 603999 = 905999) B905999
theorem B604027 : Blo 603293 604027 := bstep (se 1 (by rfl) ⟨453020, by rfl⟩ : syracuseStep 604027 = 906041) B906041
theorem B604079 : Blo 603293 604079 := bstep (se 1 (by rfl) ⟨453059, by rfl⟩ : syracuseStep 604079 = 906119) B906119
theorem B3454913 : Blo 603293 3454913 := bstep (se 2 (by rfl) ⟨1295592, by rfl⟩ : syracuseStep 3454913 = 2591185) B2591185
theorem B604103 : Blo 603293 604103 := bstep (se 1 (by rfl) ⟨453077, by rfl⟩ : syracuseStep 604103 = 906155) B906155
theorem B604123 : Blo 603293 604123 := bstep (se 1 (by rfl) ⟨453092, by rfl⟩ : syracuseStep 604123 = 906185) B906185
theorem B604199 : Blo 603293 604199 := bstep (se 1 (by rfl) ⟨453149, by rfl⟩ : syracuseStep 604199 = 906299) B906299
theorem B604239 : Blo 603293 604239 := bstep (se 1 (by rfl) ⟨453179, by rfl⟩ : syracuseStep 604239 = 906359) B906359
theorem B4601933 : Blo 603293 4601933 := bstep (se 3 (by rfl) ⟨862862, by rfl⟩ : syracuseStep 4601933 = 1725725) B1725725
theorem B14727257 : Blo 603293 14727257 := bstep (se 2 (by rfl) ⟨5522721, by rfl⟩ : syracuseStep 14727257 = 11045443) B11045443
theorem B604255 : Blo 603293 604255 := bstep (se 1 (by rfl) ⟨453191, by rfl⟩ : syracuseStep 604255 = 906383) B906383
theorem B604283 : Blo 603293 604283 := bstep (se 1 (by rfl) ⟨453212, by rfl⟩ : syracuseStep 604283 = 906425) B906425
theorem B604335 : Blo 603293 604335 := bstep (se 1 (by rfl) ⟨453251, by rfl⟩ : syracuseStep 604335 = 906503) B906503
theorem B604359 : Blo 603293 604359 := bstep (se 1 (by rfl) ⟨453269, by rfl⟩ : syracuseStep 604359 = 906539) B906539
theorem B768199 : Blo 603293 768199 := bstep (se 1 (by rfl) ⟨576149, by rfl⟩ : syracuseStep 768199 = 1152299) B1152299
theorem B604379 : Blo 603293 604379 := bstep (se 1 (by rfl) ⟨453284, by rfl⟩ : syracuseStep 604379 = 906569) B906569
theorem B604455 : Blo 603293 604455 := bstep (se 1 (by rfl) ⟨453341, by rfl⟩ : syracuseStep 604455 = 906683) B906683
theorem B604495 : Blo 603293 604495 := bstep (se 1 (by rfl) ⟨453371, by rfl⟩ : syracuseStep 604495 = 906743) B906743
theorem B604511 : Blo 603293 604511 := bstep (se 1 (by rfl) ⟨453383, by rfl⟩ : syracuseStep 604511 = 906767) B906767
theorem B604539 : Blo 603293 604539 := bstep (se 1 (by rfl) ⟨453404, by rfl⟩ : syracuseStep 604539 = 906809) B906809
theorem B604591 : Blo 603293 604591 := bstep (se 1 (by rfl) ⟨453443, by rfl⟩ : syracuseStep 604591 = 906887) B906887
theorem B604615 : Blo 603293 604615 := bstep (se 1 (by rfl) ⟨453461, by rfl⟩ : syracuseStep 604615 = 906923) B906923
theorem B604635 : Blo 603293 604635 := bstep (se 1 (by rfl) ⟨453476, by rfl⟩ : syracuseStep 604635 = 906953) B906953
theorem B604711 : Blo 603293 604711 := bstep (se 1 (by rfl) ⟨453533, by rfl⟩ : syracuseStep 604711 = 907067) B907067
theorem B604751 : Blo 603293 604751 := bstep (se 1 (by rfl) ⟨453563, by rfl⟩ : syracuseStep 604751 = 907127) B907127
theorem B604767 : Blo 603293 604767 := bstep (se 1 (by rfl) ⟨453575, by rfl⟩ : syracuseStep 604767 = 907151) B907151
theorem B1358459 : Blo 603293 1358459 := bstep (se 1 (by rfl) ⟨1018844, by rfl⟩ : syracuseStep 1358459 = 2037689) B2037689
theorem B604795 : Blo 603293 604795 := bstep (se 1 (by rfl) ⟨453596, by rfl⟩ : syracuseStep 604795 = 907193) B907193
theorem B2046599 : Blo 603293 2046599 := bstep (se 1 (by rfl) ⟨1534949, by rfl⟩ : syracuseStep 2046599 = 3069899) B3069899
theorem B604847 : Blo 603293 604847 := bstep (se 1 (by rfl) ⟨453635, by rfl⟩ : syracuseStep 604847 = 907271) B907271
theorem B11057849 : Blo 603293 11057849 := bstep (se 2 (by rfl) ⟨4146693, by rfl⟩ : syracuseStep 11057849 = 8293387) B8293387
theorem B2046653 : Blo 603293 2046653 := bstep (se 3 (by rfl) ⟨383747, by rfl⟩ : syracuseStep 2046653 = 767495) B767495
theorem B604871 : Blo 603293 604871 := bstep (se 1 (by rfl) ⟨453653, by rfl⟩ : syracuseStep 604871 = 907307) B907307
theorem B4373203 : Blo 603293 4373203 := bstep (se 1 (by rfl) ⟨3279902, by rfl⟩ : syracuseStep 4373203 = 6559805) B6559805
theorem B604891 : Blo 603293 604891 := bstep (se 1 (by rfl) ⟨453668, by rfl⟩ : syracuseStep 604891 = 907337) B907337
theorem B1358585 : Blo 603293 1358585 := bstep (se 2 (by rfl) ⟨509469, by rfl⟩ : syracuseStep 1358585 = 1018939) B1018939
theorem B604967 : Blo 603293 604967 := bstep (se 1 (by rfl) ⟨453725, by rfl⟩ : syracuseStep 604967 = 907451) B907451
theorem B605007 : Blo 603293 605007 := bstep (se 1 (by rfl) ⟨453755, by rfl⟩ : syracuseStep 605007 = 907511) B907511
theorem B605023 : Blo 603293 605023 := bstep (se 1 (by rfl) ⟨453767, by rfl⟩ : syracuseStep 605023 = 907535) B907535
theorem B2046815 : Blo 603293 2046815 := bstep (se 1 (by rfl) ⟨1535111, by rfl⟩ : syracuseStep 2046815 = 3070223) B3070223
theorem B605051 : Blo 603293 605051 := bstep (se 1 (by rfl) ⟨453788, by rfl⟩ : syracuseStep 605051 = 907577) B907577
theorem B605103 : Blo 603293 605103 := bstep (se 1 (by rfl) ⟨453827, by rfl⟩ : syracuseStep 605103 = 907655) B907655
theorem B1162171 : Blo 603293 1162171 := bstep (se 1 (by rfl) ⟨871628, by rfl⟩ : syracuseStep 1162171 = 1743257) B1743257
theorem B605127 : Blo 603293 605127 := bstep (se 1 (by rfl) ⟨453845, by rfl⟩ : syracuseStep 605127 = 907691) B907691
theorem B605147 : Blo 603293 605147 := bstep (se 1 (by rfl) ⟨453860, by rfl⟩ : syracuseStep 605147 = 907721) B907721
theorem B2046977 : Blo 603293 2046977 := bstep (se 2 (by rfl) ⟨767616, by rfl⟩ : syracuseStep 2046977 = 1535233) B1535233
theorem B1358855 : Blo 603293 1358855 := bstep (se 1 (by rfl) ⟨1019141, by rfl⟩ : syracuseStep 1358855 = 2038283) B2038283
theorem B605223 : Blo 603293 605223 := bstep (se 1 (by rfl) ⟨453917, by rfl⟩ : syracuseStep 605223 = 907835) B907835
theorem B1358927 : Blo 603293 1358927 := bstep (se 1 (by rfl) ⟨1019195, by rfl⟩ : syracuseStep 1358927 = 2038391) B2038391
theorem B605263 : Blo 603293 605263 := bstep (se 1 (by rfl) ⟨453947, by rfl⟩ : syracuseStep 605263 = 907895) B907895
theorem B605279 : Blo 603293 605279 := bstep (se 1 (by rfl) ⟨453959, by rfl⟩ : syracuseStep 605279 = 907919) B907919
theorem B605307 : Blo 603293 605307 := bstep (se 1 (by rfl) ⟨453980, by rfl⟩ : syracuseStep 605307 = 907961) B907961
theorem B605359 : Blo 603293 605359 := bstep (se 1 (by rfl) ⟨454019, by rfl⟩ : syracuseStep 605359 = 908039) B908039
theorem B605383 : Blo 603293 605383 := bstep (se 1 (by rfl) ⟨454037, by rfl⟩ : syracuseStep 605383 = 908075) B908075
theorem B605403 : Blo 603293 605403 := bstep (se 1 (by rfl) ⟨454052, by rfl⟩ : syracuseStep 605403 = 908105) B908105
theorem B605479 : Blo 603293 605479 := bstep (se 1 (by rfl) ⟨454109, by rfl⟩ : syracuseStep 605479 = 908219) B908219
theorem B605519 : Blo 603293 605519 := bstep (se 1 (by rfl) ⟨454139, by rfl⟩ : syracuseStep 605519 = 908279) B908279
theorem B605535 : Blo 603293 605535 := bstep (se 1 (by rfl) ⟨454151, by rfl⟩ : syracuseStep 605535 = 908303) B908303
theorem B605563 : Blo 603293 605563 := bstep (se 1 (by rfl) ⟨454172, by rfl⟩ : syracuseStep 605563 = 908345) B908345
theorem B605615 : Blo 603293 605615 := bstep (se 1 (by rfl) ⟨454211, by rfl⟩ : syracuseStep 605615 = 908423) B908423
theorem B605639 : Blo 603293 605639 := bstep (se 1 (by rfl) ⟨454229, by rfl⟩ : syracuseStep 605639 = 908459) B908459
theorem B1359323 : Blo 603293 1359323 := bstep (se 1 (by rfl) ⟨1019492, by rfl⟩ : syracuseStep 1359323 = 2038985) B2038985
theorem B605659 : Blo 603293 605659 := bstep (se 1 (by rfl) ⟨454244, by rfl⟩ : syracuseStep 605659 = 908489) B908489
theorem B1293833 : Blo 603293 1293833 := bstep (se 2 (by rfl) ⟨485187, by rfl⟩ : syracuseStep 1293833 = 970375) B970375
theorem B605735 : Blo 603293 605735 := bstep (se 1 (by rfl) ⟨454301, by rfl⟩ : syracuseStep 605735 = 908603) B908603
theorem B605775 : Blo 603293 605775 := bstep (se 1 (by rfl) ⟨454331, by rfl⟩ : syracuseStep 605775 = 908663) B908663
theorem B605791 : Blo 603293 605791 := bstep (se 1 (by rfl) ⟨454343, by rfl⟩ : syracuseStep 605791 = 908687) B908687
theorem B3063419 : Blo 603293 3063419 := bstep (se 1 (by rfl) ⟨2297564, by rfl⟩ : syracuseStep 3063419 = 4595129) B4595129
theorem B605819 : Blo 603293 605819 := bstep (se 1 (by rfl) ⟨454364, by rfl⟩ : syracuseStep 605819 = 908729) B908729
theorem B2211467 : Blo 603293 2211467 := bstep (se 1 (by rfl) ⟨1658600, by rfl⟩ : syracuseStep 2211467 = 3317201) B3317201
theorem B605871 : Blo 603293 605871 := bstep (se 1 (by rfl) ⟨454403, by rfl⟩ : syracuseStep 605871 = 908807) B908807
theorem B605895 : Blo 603293 605895 := bstep (se 1 (by rfl) ⟨454421, by rfl⟩ : syracuseStep 605895 = 908843) B908843
theorem B605915 : Blo 603293 605915 := bstep (se 1 (by rfl) ⟨454436, by rfl⟩ : syracuseStep 605915 = 908873) B908873
theorem B605991 : Blo 603293 605991 := bstep (se 1 (by rfl) ⟨454493, by rfl⟩ : syracuseStep 605991 = 908987) B908987
theorem B2047787 : Blo 603293 2047787 := bstep (se 1 (by rfl) ⟨1535840, by rfl⟩ : syracuseStep 2047787 = 3071681) B3071681
theorem B606031 : Blo 603293 606031 := bstep (se 1 (by rfl) ⟨454523, by rfl⟩ : syracuseStep 606031 = 909047) B909047
theorem B606047 : Blo 603293 606047 := bstep (se 1 (by rfl) ⟨454535, by rfl⟩ : syracuseStep 606047 = 909071) B909071
theorem B606075 : Blo 603293 606075 := bstep (se 1 (by rfl) ⟨454556, by rfl⟩ : syracuseStep 606075 = 909113) B909113
theorem B1359791 : Blo 603293 1359791 := bstep (se 1 (by rfl) ⟨1019843, by rfl⟩ : syracuseStep 1359791 = 2039687) B2039687
theorem B606127 : Blo 603293 606127 := bstep (se 1 (by rfl) ⟨454595, by rfl⟩ : syracuseStep 606127 = 909191) B909191
theorem B606151 : Blo 603293 606151 := bstep (se 1 (by rfl) ⟨454613, by rfl⟩ : syracuseStep 606151 = 909227) B909227
theorem B606171 : Blo 603293 606171 := bstep (se 1 (by rfl) ⟨454628, by rfl⟩ : syracuseStep 606171 = 909257) B909257
theorem B1294355 : Blo 603293 1294355 := bstep (se 1 (by rfl) ⟨970766, by rfl⟩ : syracuseStep 1294355 = 1941533) B1941533
theorem B606247 : Blo 603293 606247 := bstep (se 1 (by rfl) ⟨454685, by rfl⟩ : syracuseStep 606247 = 909371) B909371
theorem B2048057 : Blo 603293 2048057 := bstep (se 2 (by rfl) ⟨768021, by rfl⟩ : syracuseStep 2048057 = 1536043) B1536043
theorem B606287 : Blo 603293 606287 := bstep (se 1 (by rfl) ⟨454715, by rfl⟩ : syracuseStep 606287 = 909431) B909431
theorem B606303 : Blo 603293 606303 := bstep (se 1 (by rfl) ⟨454727, by rfl⟩ : syracuseStep 606303 = 909455) B909455
theorem B606331 : Blo 603293 606331 := bstep (se 1 (by rfl) ⟨454748, by rfl⟩ : syracuseStep 606331 = 909497) B909497
theorem B1360043 : Blo 603293 1360043 := bstep (se 1 (by rfl) ⟨1020032, by rfl⟩ : syracuseStep 1360043 = 2040065) B2040065
theorem B606383 : Blo 603293 606383 := bstep (se 1 (by rfl) ⟨454787, by rfl⟩ : syracuseStep 606383 = 909575) B909575
theorem B606407 : Blo 603293 606407 := bstep (se 1 (by rfl) ⟨454805, by rfl⟩ : syracuseStep 606407 = 909611) B909611
theorem B606427 : Blo 603293 606427 := bstep (se 1 (by rfl) ⟨454820, by rfl⟩ : syracuseStep 606427 = 909641) B909641
theorem B606503 : Blo 603293 606503 := bstep (se 1 (by rfl) ⟨454877, by rfl⟩ : syracuseStep 606503 = 909755) B909755
theorem B606543 : Blo 603293 606543 := bstep (se 1 (by rfl) ⟨454907, by rfl⟩ : syracuseStep 606543 = 909815) B909815
theorem B606559 : Blo 603293 606559 := bstep (se 1 (by rfl) ⟨454919, by rfl⟩ : syracuseStep 606559 = 909839) B909839
theorem B1294697 : Blo 603293 1294697 := bstep (se 2 (by rfl) ⟨485511, by rfl⟩ : syracuseStep 1294697 = 971023) B971023
theorem B606587 : Blo 603293 606587 := bstep (se 1 (by rfl) ⟨454940, by rfl⟩ : syracuseStep 606587 = 909881) B909881
theorem B2048381 : Blo 603293 2048381 := bstep (se 3 (by rfl) ⟨384071, by rfl⟩ : syracuseStep 2048381 = 768143) B768143
theorem B606639 : Blo 603293 606639 := bstep (se 1 (by rfl) ⟨454979, by rfl⟩ : syracuseStep 606639 = 909959) B909959
theorem B606663 : Blo 603293 606663 := bstep (se 1 (by rfl) ⟨454997, by rfl⟩ : syracuseStep 606663 = 909995) B909995
theorem B4604363 : Blo 603293 4604363 := bstep (se 1 (by rfl) ⟨3453272, by rfl⟩ : syracuseStep 4604363 = 6906545) B6906545
theorem B606683 : Blo 603293 606683 := bstep (se 1 (by rfl) ⟨455012, by rfl⟩ : syracuseStep 606683 = 910025) B910025
theorem B606759 : Blo 603293 606759 := bstep (se 1 (by rfl) ⟨455069, by rfl⟩ : syracuseStep 606759 = 910139) B910139
theorem B606799 : Blo 603293 606799 := bstep (se 1 (by rfl) ⟨455099, by rfl⟩ : syracuseStep 606799 = 910199) B910199
theorem B606815 : Blo 603293 606815 := bstep (se 1 (by rfl) ⟨455111, by rfl⟩ : syracuseStep 606815 = 910223) B910223
theorem B606843 : Blo 603293 606843 := bstep (se 1 (by rfl) ⟨455132, by rfl⟩ : syracuseStep 606843 = 910265) B910265
theorem B2048651 : Blo 603293 2048651 := bstep (se 1 (by rfl) ⟨1536488, by rfl⟩ : syracuseStep 2048651 = 3072977) B3072977
theorem B606895 : Blo 603293 606895 := bstep (se 1 (by rfl) ⟨455171, by rfl⟩ : syracuseStep 606895 = 910343) B910343
theorem B1360583 : Blo 603293 1360583 := bstep (se 1 (by rfl) ⟨1020437, by rfl⟩ : syracuseStep 1360583 = 2040875) B2040875
theorem B606919 : Blo 603293 606919 := bstep (se 1 (by rfl) ⟨455189, by rfl⟩ : syracuseStep 606919 = 910379) B910379
theorem B606939 : Blo 603293 606939 := bstep (se 1 (by rfl) ⟨455204, by rfl⟩ : syracuseStep 606939 = 910409) B910409
theorem B607015 : Blo 603293 607015 := bstep (se 1 (by rfl) ⟨455261, by rfl⟩ : syracuseStep 607015 = 910523) B910523
theorem B607055 : Blo 603293 607055 := bstep (se 1 (by rfl) ⟨455291, by rfl⟩ : syracuseStep 607055 = 910583) B910583
theorem B607071 : Blo 603293 607071 := bstep (se 1 (by rfl) ⟨455303, by rfl⟩ : syracuseStep 607071 = 910607) B910607
theorem B607099 : Blo 603293 607099 := bstep (se 1 (by rfl) ⟨455324, by rfl⟩ : syracuseStep 607099 = 910649) B910649
theorem B607151 : Blo 603293 607151 := bstep (se 1 (by rfl) ⟨455363, by rfl⟩ : syracuseStep 607151 = 910727) B910727
theorem B607175 : Blo 603293 607175 := bstep (se 1 (by rfl) ⟨455381, by rfl⟩ : syracuseStep 607175 = 910763) B910763
theorem B607195 : Blo 603293 607195 := bstep (se 1 (by rfl) ⟨455396, by rfl⟩ : syracuseStep 607195 = 910793) B910793
theorem B1721351 : Blo 603293 1721351 := bstep (se 1 (by rfl) ⟨1291013, by rfl⟩ : syracuseStep 1721351 = 2582027) B2582027
theorem B607271 : Blo 603293 607271 := bstep (se 1 (by rfl) ⟨455453, by rfl⟩ : syracuseStep 607271 = 910907) B910907
theorem B2049569 : Blo 603293 2049569 := bstep (se 2 (by rfl) ⟨768588, by rfl⟩ : syracuseStep 2049569 = 1537177) B1537177
theorem B1361447 : Blo 603293 1361447 := bstep (se 1 (by rfl) ⟨1021085, by rfl⟩ : syracuseStep 1361447 = 2042171) B2042171
theorem B1295995 : Blo 603293 1295995 := bstep (se 1 (by rfl) ⟨971996, by rfl⟩ : syracuseStep 1295995 = 1943993) B1943993
theorem B968363 : Blo 603293 968363 := bstep (se 1 (by rfl) ⟨726272, by rfl⟩ : syracuseStep 968363 = 1452545) B1452545
theorem B19384109 : Blo 603293 19384109 := bstep (se 3 (by rfl) ⟨3634520, by rfl⟩ : syracuseStep 19384109 = 7269041) B7269041
theorem B1361771 : Blo 603293 1361771 := bstep (se 1 (by rfl) ⟨1021328, by rfl⟩ : syracuseStep 1361771 = 2042657) B2042657
theorem B1361825 : Blo 603293 1361825 := bstep (se 2 (by rfl) ⟨510684, by rfl⟩ : syracuseStep 1361825 = 1021369) B1021369
theorem B7358521 : Blo 603293 7358521 := bstep (se 2 (by rfl) ⟨2759445, by rfl⟩ : syracuseStep 7358521 = 5518891) B5518891
theorem B8734877 : Blo 603293 8734877 := bstep (se 3 (by rfl) ⟨1637789, by rfl⟩ : syracuseStep 8734877 = 3275579) B3275579
theorem B1362167 : Blo 603293 1362167 := bstep (se 1 (by rfl) ⟨1021625, by rfl⟩ : syracuseStep 1362167 = 2043251) B2043251
theorem B3066173 : Blo 603293 3066173 := bstep (se 3 (by rfl) ⟨574907, by rfl⟩ : syracuseStep 3066173 = 1149815) B1149815
theorem B4901273 : Blo 603293 4901273 := bstep (se 2 (by rfl) ⟨1837977, by rfl⟩ : syracuseStep 4901273 = 3675955) B3675955
theorem B2902553 : Blo 603293 2902553 := bstep (se 2 (by rfl) ⟨1088457, by rfl⟩ : syracuseStep 2902553 = 2176915) B2176915
theorem B3918665 : Blo 603293 3918665 := bstep (se 2 (by rfl) ⟨1469499, by rfl⟩ : syracuseStep 3918665 = 2938999) B2938999
theorem B1362761 : Blo 603293 1362761 := bstep (se 2 (by rfl) ⟨511035, by rfl⟩ : syracuseStep 1362761 = 1022071) B1022071
theorem B4606793 : Blo 603293 4606793 := bstep (se 2 (by rfl) ⟨1727547, by rfl⟩ : syracuseStep 4606793 = 3455095) B3455095
theorem B1035703 : Blo 603293 1035703 := bstep (se 1 (by rfl) ⟨776777, by rfl⟩ : syracuseStep 1035703 = 1553555) B1553555
theorem B1363553 : Blo 603293 1363553 := bstep (se 2 (by rfl) ⟨511332, by rfl⟩ : syracuseStep 1363553 = 1022665) B1022665
theorem B1724267 : Blo 603293 1724267 := bstep (se 1 (by rfl) ⟨1293200, by rfl⟩ : syracuseStep 1724267 = 2586401) B2586401
theorem B905135 : Blo 603293 905135 := bstep (se 1 (by rfl) ⟨678851, by rfl⟩ : syracuseStep 905135 = 1357703) B1357703
theorem B1363895 : Blo 603293 1363895 := bstep (se 1 (by rfl) ⟨1022921, by rfl⟩ : syracuseStep 1363895 = 2045843) B2045843
theorem B905225 : Blo 603293 905225 := bstep (se 2 (by rfl) ⟨339459, by rfl⟩ : syracuseStep 905225 = 678919) B678919
theorem B905255 : Blo 603293 905255 := bstep (se 1 (by rfl) ⟨678941, by rfl⟩ : syracuseStep 905255 = 1357883) B1357883
theorem B905339 : Blo 603293 905339 := bstep (se 1 (by rfl) ⟨679004, by rfl⟩ : syracuseStep 905339 = 1358009) B1358009
theorem B1528055 : Blo 603293 1528055 := bstep (se 1 (by rfl) ⟨1146041, by rfl⟩ : syracuseStep 1528055 = 2292083) B2292083
theorem B905465 : Blo 603293 905465 := bstep (se 2 (by rfl) ⟨339549, by rfl⟩ : syracuseStep 905465 = 679099) B679099
theorem B905567 : Blo 603293 905567 := bstep (se 1 (by rfl) ⟨679175, by rfl⟩ : syracuseStep 905567 = 1358351) B1358351
theorem B905579 : Blo 603293 905579 := bstep (se 1 (by rfl) ⟨679184, by rfl⟩ : syracuseStep 905579 = 1358369) B1358369
theorem B971195 : Blo 603293 971195 := bstep (se 1 (by rfl) ⟨728396, by rfl⟩ : syracuseStep 971195 = 1456793) B1456793
theorem B1364489 : Blo 603293 1364489 := bstep (se 2 (by rfl) ⟨511683, by rfl⟩ : syracuseStep 1364489 = 1023367) B1023367
theorem B3068441 : Blo 603293 3068441 := bstep (se 2 (by rfl) ⟨1150665, by rfl⟩ : syracuseStep 3068441 = 2301331) B2301331
theorem B905807 : Blo 603293 905807 := bstep (se 1 (by rfl) ⟨679355, by rfl⟩ : syracuseStep 905807 = 1358711) B1358711
theorem B905927 : Blo 603293 905927 := bstep (se 1 (by rfl) ⟨679445, by rfl⟩ : syracuseStep 905927 = 1358891) B1358891
theorem B2446109 : Blo 603293 2446109 := bstep (se 3 (by rfl) ⟨458645, by rfl⟩ : syracuseStep 2446109 = 917291) B917291
theorem B1364831 : Blo 603293 1364831 := bstep (se 1 (by rfl) ⟨1023623, by rfl⟩ : syracuseStep 1364831 = 2047247) B2047247
theorem B906089 : Blo 603293 906089 := bstep (se 2 (by rfl) ⟨339783, by rfl⟩ : syracuseStep 906089 = 679567) B679567
theorem B906167 : Blo 603293 906167 := bstep (se 1 (by rfl) ⟨679625, by rfl⟩ : syracuseStep 906167 = 1359251) B1359251
theorem B906203 : Blo 603293 906203 := bstep (se 1 (by rfl) ⟨679652, by rfl⟩ : syracuseStep 906203 = 1359305) B1359305
theorem B1365011 : Blo 603293 1365011 := bstep (se 1 (by rfl) ⟨1023758, by rfl⟩ : syracuseStep 1365011 = 2047517) B2047517
theorem B1365353 : Blo 603293 1365353 := bstep (se 2 (by rfl) ⟨512007, by rfl⟩ : syracuseStep 1365353 = 1024015) B1024015
theorem B906671 : Blo 603293 906671 := bstep (se 1 (by rfl) ⟨680003, by rfl⟩ : syracuseStep 906671 = 1360007) B1360007
theorem B2446793 : Blo 603293 2446793 := bstep (se 2 (by rfl) ⟨917547, by rfl⟩ : syracuseStep 2446793 = 1835095) B1835095
theorem B906761 : Blo 603293 906761 := bstep (se 2 (by rfl) ⟨340035, by rfl⟩ : syracuseStep 906761 = 680071) B680071
theorem B906791 : Blo 603293 906791 := bstep (se 1 (by rfl) ⟨680093, by rfl⟩ : syracuseStep 906791 = 1360187) B1360187
theorem B906875 : Blo 603293 906875 := bstep (se 1 (by rfl) ⟨680156, by rfl⟩ : syracuseStep 906875 = 1360313) B1360313
theorem B1529543 : Blo 603293 1529543 := bstep (se 1 (by rfl) ⟨1147157, by rfl⟩ : syracuseStep 1529543 = 2294315) B2294315
theorem B907001 : Blo 603293 907001 := bstep (se 2 (by rfl) ⟨340125, by rfl⟩ : syracuseStep 907001 = 680251) B680251
theorem B2447147 : Blo 603293 2447147 := bstep (se 1 (by rfl) ⟨1835360, by rfl⟩ : syracuseStep 2447147 = 3670721) B3670721
theorem B907103 : Blo 603293 907103 := bstep (se 1 (by rfl) ⟨680327, by rfl⟩ : syracuseStep 907103 = 1360655) B1360655
theorem B907115 : Blo 603293 907115 := bstep (se 1 (by rfl) ⟨680336, by rfl⟩ : syracuseStep 907115 = 1360673) B1360673
theorem B2578337 : Blo 603293 2578337 := bstep (se 2 (by rfl) ⟨966876, by rfl⟩ : syracuseStep 2578337 = 1933753) B1933753
theorem B2185147 : Blo 603293 2185147 := bstep (se 1 (by rfl) ⟨1638860, by rfl⟩ : syracuseStep 2185147 = 3277721) B3277721
theorem B1365947 : Blo 603293 1365947 := bstep (se 1 (by rfl) ⟨1024460, by rfl⟩ : syracuseStep 1365947 = 2048921) B2048921
theorem B1366073 : Blo 603293 1366073 := bstep (se 2 (by rfl) ⟨512277, by rfl⟩ : syracuseStep 1366073 = 1024555) B1024555
theorem B907343 : Blo 603293 907343 := bstep (se 1 (by rfl) ⟨680507, by rfl⟩ : syracuseStep 907343 = 1361015) B1361015
theorem B907463 : Blo 603293 907463 := bstep (se 1 (by rfl) ⟨680597, by rfl⟩ : syracuseStep 907463 = 1361195) B1361195
theorem B2906455 : Blo 603293 2906455 := bstep (se 1 (by rfl) ⟨2179841, by rfl⟩ : syracuseStep 2906455 = 4359683) B4359683
theorem B907625 : Blo 603293 907625 := bstep (se 2 (by rfl) ⟨340359, by rfl⟩ : syracuseStep 907625 = 680719) B680719
theorem B907703 : Blo 603293 907703 := bstep (se 1 (by rfl) ⟨680777, by rfl⟩ : syracuseStep 907703 = 1361555) B1361555
theorem B9066937 : Blo 603293 9066937 := bstep (se 2 (by rfl) ⟨3400101, by rfl⟩ : syracuseStep 9066937 = 6800203) B6800203
theorem B907739 : Blo 603293 907739 := bstep (se 1 (by rfl) ⟨680804, by rfl⟩ : syracuseStep 907739 = 1361609) B1361609
theorem B1530697 : Blo 603293 1530697 := bstep (se 2 (by rfl) ⟨574011, by rfl⟩ : syracuseStep 1530697 = 1148023) B1148023
theorem B908207 : Blo 603293 908207 := bstep (se 1 (by rfl) ⟨681155, by rfl⟩ : syracuseStep 908207 = 1362311) B1362311
theorem B908297 : Blo 603293 908297 := bstep (se 2 (by rfl) ⟨340611, by rfl⟩ : syracuseStep 908297 = 681223) B681223
theorem B908327 : Blo 603293 908327 := bstep (se 1 (by rfl) ⟨681245, by rfl⟩ : syracuseStep 908327 = 1362491) B1362491
theorem B678991 : Blo 603293 678991 := bstep (se 1 (by rfl) ⟨509243, by rfl⟩ : syracuseStep 678991 = 1018487) B1018487
theorem B908411 : Blo 603293 908411 := bstep (se 1 (by rfl) ⟨681308, by rfl⟩ : syracuseStep 908411 = 1362617) B1362617
theorem B3103991 : Blo 603293 3103991 := bstep (se 1 (by rfl) ⟨2327993, by rfl⟩ : syracuseStep 3103991 = 4655987) B4655987
theorem B11066615 : Blo 603293 11066615 := bstep (se 1 (by rfl) ⟨8299961, by rfl⟩ : syracuseStep 11066615 = 16599923) B16599923
theorem B908537 : Blo 603293 908537 := bstep (se 2 (by rfl) ⟨340701, by rfl⟩ : syracuseStep 908537 = 681403) B681403
theorem B908639 : Blo 603293 908639 := bstep (se 1 (by rfl) ⟨681479, by rfl⟩ : syracuseStep 908639 = 1362959) B1362959
theorem B908651 : Blo 603293 908651 := bstep (se 1 (by rfl) ⟨681488, by rfl⟩ : syracuseStep 908651 = 1362977) B1362977
theorem B3071357 : Blo 603293 3071357 := bstep (se 3 (by rfl) ⟨575879, by rfl⟩ : syracuseStep 3071357 = 1151759) B1151759
theorem B679387 : Blo 603293 679387 := bstep (se 1 (by rfl) ⟨509540, by rfl⟩ : syracuseStep 679387 = 1019081) B1019081
theorem B908879 : Blo 603293 908879 := bstep (se 1 (by rfl) ⟨681659, by rfl⟩ : syracuseStep 908879 = 1363319) B1363319
theorem B908999 : Blo 603293 908999 := bstep (se 1 (by rfl) ⟨681749, by rfl⟩ : syracuseStep 908999 = 1363499) B1363499
theorem B909161 : Blo 603293 909161 := bstep (se 2 (by rfl) ⟨340935, by rfl⟩ : syracuseStep 909161 = 681871) B681871
theorem B679855 : Blo 603293 679855 := bstep (se 1 (by rfl) ⟨509891, by rfl⟩ : syracuseStep 679855 = 1019783) B1019783
theorem B1531831 : Blo 603293 1531831 := bstep (se 1 (by rfl) ⟨1148873, by rfl⟩ : syracuseStep 1531831 = 2297747) B2297747
theorem B909239 : Blo 603293 909239 := bstep (se 1 (by rfl) ⟨681929, by rfl⟩ : syracuseStep 909239 = 1363859) B1363859
theorem B909275 : Blo 603293 909275 := bstep (se 1 (by rfl) ⟨681956, by rfl⟩ : syracuseStep 909275 = 1363913) B1363913
theorem B1400851 : Blo 603293 1400851 := bstep (se 1 (by rfl) ⟨1050638, by rfl⟩ : syracuseStep 1400851 = 2101277) B2101277
theorem B26173469 : Blo 603293 26173469 := bstep (se 3 (by rfl) ⟨4907525, by rfl⟩ : syracuseStep 26173469 = 9815051) B9815051
theorem B8970355 : Blo 603293 8970355 := bstep (se 1 (by rfl) ⟨6727766, by rfl⟩ : syracuseStep 8970355 = 13455533) B13455533
theorem B10313891 : Blo 603293 10313891 := bstep (se 1 (by rfl) ⟨7735418, by rfl⟩ : syracuseStep 10313891 = 15470837) B15470837
theorem B2580797 : Blo 603293 2580797 := bstep (se 3 (by rfl) ⟨483899, by rfl⟩ : syracuseStep 2580797 = 967799) B967799
theorem B2187581 : Blo 603293 2187581 := bstep (se 3 (by rfl) ⟨410171, by rfl⟩ : syracuseStep 2187581 = 820343) B820343
theorem B680287 : Blo 603293 680287 := bstep (se 1 (by rfl) ⟨510215, by rfl⟩ : syracuseStep 680287 = 1020431) B1020431
theorem B647519 : Blo 603293 647519 := bstep (se 1 (by rfl) ⟨485639, by rfl⟩ : syracuseStep 647519 = 971279) B971279
theorem B13066595 : Blo 603293 13066595 := bstep (se 1 (by rfl) ⟨9799946, by rfl⟩ : syracuseStep 13066595 = 19599893) B19599893
theorem B778603 : Blo 603293 778603 := bstep (se 1 (by rfl) ⟨583952, by rfl⟩ : syracuseStep 778603 = 1167905) B1167905
theorem B909743 : Blo 603293 909743 := bstep (se 1 (by rfl) ⟨682307, by rfl⟩ : syracuseStep 909743 = 1364615) B1364615
theorem B909833 : Blo 603293 909833 := bstep (se 2 (by rfl) ⟨341187, by rfl⟩ : syracuseStep 909833 = 682375) B682375
theorem B909863 : Blo 603293 909863 := bstep (se 1 (by rfl) ⟨682397, by rfl⟩ : syracuseStep 909863 = 1364795) B1364795
theorem B909947 : Blo 603293 909947 := bstep (se 1 (by rfl) ⟨682460, by rfl⟩ : syracuseStep 909947 = 1364921) B1364921
theorem B680647 : Blo 603293 680647 := bstep (se 1 (by rfl) ⟨510485, by rfl⟩ : syracuseStep 680647 = 1020971) B1020971
theorem B910073 : Blo 603293 910073 := bstep (se 2 (by rfl) ⟨341277, by rfl⟩ : syracuseStep 910073 = 682555) B682555
theorem B8741681 : Blo 603293 8741681 := bstep (se 2 (by rfl) ⟨3278130, by rfl⟩ : syracuseStep 8741681 = 6556261) B6556261
theorem B910175 : Blo 603293 910175 := bstep (se 1 (by rfl) ⟨682631, by rfl⟩ : syracuseStep 910175 = 1365263) B1365263
theorem B3269483 : Blo 603293 3269483 := bstep (se 1 (by rfl) ⟨2452112, by rfl⟩ : syracuseStep 3269483 = 4904225) B4904225
theorem B910187 : Blo 603293 910187 := bstep (se 1 (by rfl) ⟨682640, by rfl⟩ : syracuseStep 910187 = 1365281) B1365281
theorem B910415 : Blo 603293 910415 := bstep (se 1 (by rfl) ⟨682811, by rfl⟩ : syracuseStep 910415 = 1365623) B1365623
theorem B648271 : Blo 603293 648271 := bstep (se 1 (by rfl) ⟨486203, by rfl⟩ : syracuseStep 648271 = 972407) B972407
theorem B2450585 : Blo 603293 2450585 := bstep (se 2 (by rfl) ⟨918969, by rfl⟩ : syracuseStep 2450585 = 1837939) B1837939
theorem B910535 : Blo 603293 910535 := bstep (se 1 (by rfl) ⟨682901, by rfl⟩ : syracuseStep 910535 = 1365803) B1365803
theorem B1533289 : Blo 603293 1533289 := bstep (se 2 (by rfl) ⟨574983, by rfl⟩ : syracuseStep 1533289 = 1149967) B1149967
theorem B910697 : Blo 603293 910697 := bstep (se 2 (by rfl) ⟨341511, by rfl⟩ : syracuseStep 910697 = 683023) B683023
theorem B11167139 : Blo 603293 11167139 := bstep (se 1 (by rfl) ⟨8375354, by rfl⟩ : syracuseStep 11167139 = 16750709) B16750709
theorem B910775 : Blo 603293 910775 := bstep (se 1 (by rfl) ⟨683081, by rfl⟩ : syracuseStep 910775 = 1366163) B1366163
theorem B18703817 : Blo 603293 18703817 := bstep (se 2 (by rfl) ⟨7013931, by rfl⟩ : syracuseStep 18703817 = 14027863) B14027863
theorem B910811 : Blo 603293 910811 := bstep (se 1 (by rfl) ⟨683108, by rfl⟩ : syracuseStep 910811 = 1366217) B1366217
theorem B2483693 : Blo 603293 2483693 := bstep (se 3 (by rfl) ⟨465692, by rfl⟩ : syracuseStep 2483693 = 931385) B931385
theorem B681511 : Blo 603293 681511 := bstep (se 1 (by rfl) ⟨511133, by rfl⟩ : syracuseStep 681511 = 1022267) B1022267
theorem B1533563 : Blo 603293 1533563 := bstep (se 1 (by rfl) ⟨1150172, by rfl⟩ : syracuseStep 1533563 = 2300345) B2300345
theorem B8873921 : Blo 603293 8873921 := bstep (se 2 (by rfl) ⟨3327720, by rfl⟩ : syracuseStep 8873921 = 6655441) B6655441
theorem B2910779 : Blo 603293 2910779 := bstep (se 1 (by rfl) ⟨2183084, by rfl⟩ : syracuseStep 2910779 = 4366169) B4366169
theorem B683131 : Blo 603293 683131 := bstep (se 1 (by rfl) ⟨512348, by rfl⟩ : syracuseStep 683131 = 1024697) B1024697
theorem B4418959 : Blo 603293 4418959 := bstep (se 1 (by rfl) ⟨3314219, by rfl⟩ : syracuseStep 4418959 = 6628439) B6628439
theorem B1535375 : Blo 603293 1535375 := bstep (se 1 (by rfl) ⟨1151531, by rfl⟩ : syracuseStep 1535375 = 2303063) B2303063
theorem B1535699 : Blo 603293 1535699 := bstep (se 1 (by rfl) ⟨1151774, by rfl⟩ : syracuseStep 1535699 = 2303549) B2303549
theorem B1961903 : Blo 603293 1961903 := bstep (se 1 (by rfl) ⟨1471427, by rfl⟩ : syracuseStep 1961903 = 2942855) B2942855
theorem B5534081 : Blo 603293 5534081 := bstep (se 2 (by rfl) ⟨2075280, by rfl⟩ : syracuseStep 5534081 = 4150561) B4150561
theorem B2912777 : Blo 603293 2912777 := bstep (se 2 (by rfl) ⟨1092291, by rfl⟩ : syracuseStep 2912777 = 2184583) B2184583
theorem B2585753 : Blo 603293 2585753 := bstep (se 2 (by rfl) ⟨969657, by rfl⟩ : syracuseStep 2585753 = 1939315) B1939315
theorem B4584923 : Blo 603293 4584923 := bstep (se 1 (by rfl) ⟨3438692, by rfl⟩ : syracuseStep 4584923 = 6877385) B6877385
theorem B2291399 : Blo 603293 2291399 := bstep (se 1 (by rfl) ⟨1718549, by rfl⟩ : syracuseStep 2291399 = 3437099) B3437099
theorem B35452673 : Blo 603293 35452673 := bstep (se 2 (by rfl) ⟨13294752, by rfl⟩ : syracuseStep 35452673 = 26589505) B26589505
theorem B4585409 : Blo 603293 4585409 := bstep (se 2 (by rfl) ⟨1719528, by rfl⟩ : syracuseStep 4585409 = 3439057) B3439057
theorem B169834765 : Blo 603293 169834765 := bstep (se 3 (by rfl) ⟨31844018, by rfl⟩ : syracuseStep 169834765 = 63688037) B63688037
theorem B2292097 : Blo 603293 2292097 := bstep (se 2 (by rfl) ⟨859536, by rfl⟩ : syracuseStep 2292097 = 1719073) B1719073
theorem B14678597 : Blo 603293 14678597 := bstep (se 4 (by rfl) ⟨1376118, by rfl⟩ : syracuseStep 14678597 = 2752237) B2752237
theorem B1145441 : Blo 603293 1145441 := bstep (se 2 (by rfl) ⟨429540, by rfl⟩ : syracuseStep 1145441 = 859081) B859081
theorem B2292371 : Blo 603293 2292371 := bstep (se 1 (by rfl) ⟨1719278, by rfl⟩ : syracuseStep 2292371 = 3438557) B3438557
theorem B1637053 : Blo 603293 1637053 := bstep (se 3 (by rfl) ⟨306947, by rfl⟩ : syracuseStep 1637053 = 613895) B613895
theorem B1145593 : Blo 603293 1145593 := bstep (se 2 (by rfl) ⟨429597, by rfl⟩ : syracuseStep 1145593 = 859195) B859195
theorem B4586867 : Blo 603293 4586867 := bstep (se 1 (by rfl) ⟨3440150, by rfl⟩ : syracuseStep 4586867 = 6880301) B6880301
theorem B3440015 : Blo 603293 3440015 := bstep (se 1 (by rfl) ⟨2580011, by rfl⟩ : syracuseStep 3440015 = 5160023) B5160023
theorem B1965593 : Blo 603293 1965593 := bstep (se 2 (by rfl) ⟨737097, by rfl⟩ : syracuseStep 1965593 = 1474195) B1474195
theorem B5176871 : Blo 603293 5176871 := bstep (se 1 (by rfl) ⟨3882653, by rfl⟩ : syracuseStep 5176871 = 7765307) B7765307
theorem B2358881 : Blo 603293 2358881 := bstep (se 2 (by rfl) ⟨884580, by rfl⟩ : syracuseStep 2358881 = 1769161) B1769161
theorem B3866251 : Blo 603293 3866251 := bstep (se 1 (by rfl) ⟨2899688, by rfl⟩ : syracuseStep 3866251 = 5799377) B5799377
theorem B1867801 : Blo 603293 1867801 := bstep (se 2 (by rfl) ⟨700425, by rfl⟩ : syracuseStep 1867801 = 1400851) B1400851
theorem B11960473 : Blo 603293 11960473 := bstep (se 2 (by rfl) ⟨4485177, by rfl⟩ : syracuseStep 11960473 = 8970355) B8970355
theorem B656047 : Blo 603293 656047 := bstep (se 1 (by rfl) ⟨492035, by rfl⟩ : syracuseStep 656047 = 984071) B984071
theorem B4653883 : Blo 603293 4653883 := bstep (se 1 (by rfl) ⟨3490412, by rfl⟩ : syracuseStep 4653883 = 6980825) B6980825
theorem B5833549 : Blo 603293 5833549 := bstep (se 3 (by rfl) ⟨1093790, by rfl⟩ : syracuseStep 5833549 = 2187581) B2187581
theorem B2589853 : Blo 603293 2589853 := bstep (se 3 (by rfl) ⟨485597, by rfl⟩ : syracuseStep 2589853 = 971195) B971195
theorem B2294999 : Blo 603293 2294999 := bstep (se 1 (by rfl) ⟨1721249, by rfl⟩ : syracuseStep 2294999 = 3442499) B3442499
theorem B3114233 : Blo 603293 3114233 := bstep (se 2 (by rfl) ⟨1167837, by rfl⟩ : syracuseStep 3114233 = 2335675) B2335675
theorem B2459069 : Blo 603293 2459069 := bstep (se 3 (by rfl) ⟨461075, by rfl⟩ : syracuseStep 2459069 = 922151) B922151
theorem B1935035 : Blo 603293 1935035 := bstep (se 1 (by rfl) ⟨1451276, by rfl⟩ : syracuseStep 1935035 = 2902553) B2902553
theorem B4590269 : Blo 603293 4590269 := bstep (se 3 (by rfl) ⟨860675, by rfl⟩ : syracuseStep 4590269 = 1721351) B1721351
theorem B5180183 : Blo 603293 5180183 := bstep (se 1 (by rfl) ⟨3885137, by rfl⟩ : syracuseStep 5180183 = 7770275) B7770275
theorem B1018703 : Blo 603293 1018703 := bstep (se 1 (by rfl) ⟨764027, by rfl⟩ : syracuseStep 1018703 = 1528055) B1528055
theorem B920551 : Blo 603293 920551 := bstep (se 1 (by rfl) ⟨690413, by rfl⟩ : syracuseStep 920551 = 1380827) B1380827
theorem B11079301 : Blo 603293 11079301 := bstep (se 4 (by rfl) ⟨1038684, by rfl⟩ : syracuseStep 11079301 = 2077369) B2077369
theorem B724783 : Blo 603293 724783 := bstep (se 1 (by rfl) ⟨543587, by rfl⟩ : syracuseStep 724783 = 1087175) B1087175
theorem B1019695 : Blo 603293 1019695 := bstep (se 1 (by rfl) ⟨764771, by rfl⟩ : syracuseStep 1019695 = 1529543) B1529543
theorem B2297915 : Blo 603293 2297915 := bstep (se 1 (by rfl) ⟨1723436, by rfl⟩ : syracuseStep 2297915 = 3446873) B3446873
theorem B4133123 : Blo 603293 4133123 := bstep (se 1 (by rfl) ⟨3099842, by rfl⟩ : syracuseStep 4133123 = 6199685) B6199685
theorem B2298203 : Blo 603293 2298203 := bstep (se 1 (by rfl) ⟨1723652, by rfl⟩ : syracuseStep 2298203 = 3447305) B3447305
theorem B1380937 : Blo 603293 1380937 := bstep (se 2 (by rfl) ⟨517851, by rfl⟩ : syracuseStep 1380937 = 1035703) B1035703
theorem B2036447 : Blo 603293 2036447 := bstep (se 1 (by rfl) ⟨1527335, by rfl⟩ : syracuseStep 2036447 = 3054671) B3054671
theorem B725807 : Blo 603293 725807 := bstep (se 1 (by rfl) ⟨544355, by rfl⟩ : syracuseStep 725807 = 1088711) B1088711
theorem B2069327 : Blo 603293 2069327 := bstep (se 1 (by rfl) ⟨1551995, by rfl⟩ : syracuseStep 2069327 = 3103991) B3103991
theorem B7377743 : Blo 603293 7377743 := bstep (se 1 (by rfl) ⟨5533307, by rfl⟩ : syracuseStep 7377743 = 11066615) B11066615
theorem B10327013 : Blo 603293 10327013 := bstep (se 4 (by rfl) ⟨968157, by rfl⟩ : syracuseStep 10327013 = 1936315) B1936315
theorem B2036879 : Blo 603293 2036879 := bstep (se 1 (by rfl) ⟨1527659, by rfl⟩ : syracuseStep 2036879 = 3055319) B3055319
theorem B3282065 : Blo 603293 3282065 := bstep (se 2 (by rfl) ⟨1230774, by rfl⟩ : syracuseStep 3282065 = 2461549) B2461549
theorem B23663789 : Blo 603293 23663789 := bstep (se 3 (by rfl) ⟨4436960, by rfl⟩ : syracuseStep 23663789 = 8873921) B8873921
theorem B8754425 : Blo 603293 8754425 := bstep (se 2 (by rfl) ⟨3282909, by rfl⟩ : syracuseStep 8754425 = 6565819) B6565819
theorem B2299175 : Blo 603293 2299175 := bstep (se 1 (by rfl) ⟨1724381, by rfl⟩ : syracuseStep 2299175 = 3448763) B3448763
theorem B1939585 : Blo 603293 1939585 := bstep (se 2 (by rfl) ⟨727344, by rfl⟩ : syracuseStep 1939585 = 1454689) B1454689
theorem B2038013 : Blo 603293 2038013 := bstep (se 3 (by rfl) ⟨382127, by rfl⟩ : syracuseStep 2038013 = 764255) B764255
theorem B7444759 : Blo 603293 7444759 := bstep (se 1 (by rfl) ⟨5583569, by rfl⟩ : syracuseStep 7444759 = 11167139) B11167139
theorem B1022375 : Blo 603293 1022375 := bstep (se 1 (by rfl) ⟨766781, by rfl⟩ : syracuseStep 1022375 = 1533563) B1533563
theorem B1022537 : Blo 603293 1022537 := bstep (se 2 (by rfl) ⟨383451, by rfl⟩ : syracuseStep 1022537 = 766903) B766903
theorem B2300663 : Blo 603293 2300663 := bstep (se 1 (by rfl) ⟨1725497, by rfl⟩ : syracuseStep 2300663 = 3450995) B3450995
theorem B3054509 : Blo 603293 3054509 := bstep (se 3 (by rfl) ⟨572720, by rfl⟩ : syracuseStep 3054509 = 1145441) B1145441
theorem B1940519 : Blo 603293 1940519 := bstep (se 1 (by rfl) ⟨1455389, by rfl⟩ : syracuseStep 1940519 = 2910779) B2910779
theorem B2038823 : Blo 603293 2038823 := bstep (se 1 (by rfl) ⟨1529117, by rfl⟩ : syracuseStep 2038823 = 3058235) B3058235
theorem B859423 : Blo 603293 859423 := bstep (se 1 (by rfl) ⟨644567, by rfl⟩ : syracuseStep 859423 = 1289135) B1289135
theorem B4791619 : Blo 603293 4791619 := bstep (se 1 (by rfl) ⟨3593714, by rfl⟩ : syracuseStep 4791619 = 7187429) B7187429
theorem B2039255 : Blo 603293 2039255 := bstep (se 1 (by rfl) ⟨1529441, by rfl⟩ : syracuseStep 2039255 = 3058883) B3058883
theorem B4922903 : Blo 603293 4922903 := bstep (se 1 (by rfl) ⟨3692177, by rfl⟩ : syracuseStep 4922903 = 7384355) B7384355
theorem B12459545 : Blo 603293 12459545 := bstep (se 2 (by rfl) ⟨4672329, by rfl⟩ : syracuseStep 12459545 = 9344659) B9344659
theorem B5905979 : Blo 603293 5905979 := bstep (se 1 (by rfl) ⟨4429484, by rfl⟩ : syracuseStep 5905979 = 8858969) B8858969
theorem B1023583 : Blo 603293 1023583 := bstep (se 1 (by rfl) ⟨767687, by rfl⟩ : syracuseStep 1023583 = 1535375) B1535375
theorem B1023799 : Blo 603293 1023799 := bstep (se 1 (by rfl) ⟨767849, by rfl⟩ : syracuseStep 1023799 = 1535699) B1535699
theorem B1024265 : Blo 603293 1024265 := bstep (se 2 (by rfl) ⟨384099, by rfl⟩ : syracuseStep 1024265 = 768199) B768199
theorem B1941851 : Blo 603293 1941851 := bstep (se 1 (by rfl) ⟨1456388, by rfl⟩ : syracuseStep 1941851 = 2912777) B2912777
theorem B3875273 : Blo 603293 3875273 := bstep (se 2 (by rfl) ⟨1453227, by rfl⟩ : syracuseStep 3875273 = 2906455) B2906455
theorem B3056129 : Blo 603293 3056129 := bstep (se 2 (by rfl) ⟨1146048, by rfl⟩ : syracuseStep 3056129 = 2292097) B2292097
theorem B3056615 : Blo 603293 3056615 := bstep (se 1 (by rfl) ⟨2292461, by rfl⟩ : syracuseStep 3056615 = 4584923) B4584923
theorem B2040929 : Blo 603293 2040929 := bstep (se 2 (by rfl) ⟨765348, by rfl⟩ : syracuseStep 2040929 = 1530697) B1530697
theorem B23635115 : Blo 603293 23635115 := bstep (se 1 (by rfl) ⟨17726336, by rfl⟩ : syracuseStep 23635115 = 35452673) B35452673
theorem B1549561 : Blo 603293 1549561 := bstep (se 2 (by rfl) ⟨581085, by rfl⟩ : syracuseStep 1549561 = 1162171) B1162171
theorem B3056939 : Blo 603293 3056939 := bstep (se 1 (by rfl) ⟨2292704, by rfl⟩ : syracuseStep 3056939 = 4585409) B4585409
theorem B2303275 : Blo 603293 2303275 := bstep (se 1 (by rfl) ⟨1727456, by rfl⟩ : syracuseStep 2303275 = 3454913) B3454913
theorem B3450221 : Blo 603293 3450221 := bstep (se 3 (by rfl) ⟨646916, by rfl⟩ : syracuseStep 3450221 = 1293833) B1293833
theorem B1452161 : Blo 603293 1452161 := bstep (se 2 (by rfl) ⟨544560, by rfl⟩ : syracuseStep 1452161 = 1089121) B1089121
theorem B5155001 : Blo 603293 5155001 := bstep (se 2 (by rfl) ⟨1933125, by rfl⟩ : syracuseStep 5155001 = 3866251) B3866251
theorem B3057911 : Blo 603293 3057911 := bstep (se 1 (by rfl) ⟨2293433, by rfl⟩ : syracuseStep 3057911 = 4586867) B4586867
theorem B4598045 : Blo 603293 4598045 := bstep (se 3 (by rfl) ⟨862133, by rfl⟩ : syracuseStep 4598045 = 1724267) B1724267
theorem B3451247 : Blo 603293 3451247 := bstep (se 1 (by rfl) ⟨2588435, by rfl⟩ : syracuseStep 3451247 = 5176871) B5176871
theorem B2042279 : Blo 603293 2042279 := bstep (se 1 (by rfl) ⟨1531709, by rfl⟩ : syracuseStep 2042279 = 3063419) B3063419
theorem B2042441 : Blo 603293 2042441 := bstep (se 2 (by rfl) ⟨765915, by rfl⟩ : syracuseStep 2042441 = 1531831) B1531831
theorem B862903 : Blo 603293 862903 := bstep (se 1 (by rfl) ⟨647177, by rfl⟩ : syracuseStep 862903 = 1294355) B1294355
theorem B3058397 : Blo 603293 3058397 := bstep (se 3 (by rfl) ⟨573449, by rfl⟩ : syracuseStep 3058397 = 1146899) B1146899
theorem B1551071 : Blo 603293 1551071 := bstep (se 1 (by rfl) ⟨1163303, by rfl⟩ : syracuseStep 1551071 = 2326607) B2326607
theorem B3877757 : Blo 603293 3877757 := bstep (se 3 (by rfl) ⟨727079, by rfl⟩ : syracuseStep 3877757 = 1454159) B1454159
theorem B863131 : Blo 603293 863131 := bstep (se 1 (by rfl) ⟨647348, by rfl⟩ : syracuseStep 863131 = 1294697) B1294697
theorem B1092523 : Blo 603293 1092523 := bstep (se 1 (by rfl) ⟨819392, by rfl⟩ : syracuseStep 1092523 = 1638785) B1638785
theorem B764903 : Blo 603293 764903 := bstep (se 1 (by rfl) ⟨573677, by rfl⟩ : syracuseStep 764903 = 1147355) B1147355
theorem B29470067 : Blo 603293 29470067 := bstep (se 1 (by rfl) ⟨22102550, by rfl⟩ : syracuseStep 29470067 = 44205101) B44205101
theorem B1224287 : Blo 603293 1224287 := bstep (se 1 (by rfl) ⟨918215, by rfl⟩ : syracuseStep 1224287 = 1836431) B1836431
theorem B12922739 : Blo 603293 12922739 := bstep (se 1 (by rfl) ⟨9692054, by rfl⟩ : syracuseStep 12922739 = 19384109) B19384109
theorem B864361 : Blo 603293 864361 := bstep (se 2 (by rfl) ⟨324135, by rfl⟩ : syracuseStep 864361 = 648271) B648271
theorem B2044115 : Blo 603293 2044115 := bstep (se 1 (by rfl) ⟨1533086, by rfl⟩ : syracuseStep 2044115 = 3066173) B3066173
theorem B2044385 : Blo 603293 2044385 := bstep (se 2 (by rfl) ⟨766644, by rfl⟩ : syracuseStep 2044385 = 1533289) B1533289
theorem B603423 : Blo 603293 603423 := bstep (se 1 (by rfl) ⟨452567, by rfl⟩ : syracuseStep 603423 = 905135) B905135
theorem B603483 : Blo 603293 603483 := bstep (se 1 (by rfl) ⟨452612, by rfl⟩ : syracuseStep 603483 = 905225) B905225
theorem B767323 : Blo 603293 767323 := bstep (se 1 (by rfl) ⟨575492, by rfl⟩ : syracuseStep 767323 = 1150985) B1150985
theorem B603503 : Blo 603293 603503 := bstep (se 1 (by rfl) ⟨452627, by rfl⟩ : syracuseStep 603503 = 905255) B905255
theorem B9811361 : Blo 603293 9811361 := bstep (se 2 (by rfl) ⟨3679260, by rfl⟩ : syracuseStep 9811361 = 7358521) B7358521
theorem B603559 : Blo 603293 603559 := bstep (se 1 (by rfl) ⟨452669, by rfl⟩ : syracuseStep 603559 = 905339) B905339
theorem B603643 : Blo 603293 603643 := bstep (se 1 (by rfl) ⟨452732, by rfl⟩ : syracuseStep 603643 = 905465) B905465
theorem B1291783 : Blo 603293 1291783 := bstep (se 1 (by rfl) ⟨968837, by rfl⟩ : syracuseStep 1291783 = 1937675) B1937675
theorem B767551 : Blo 603293 767551 := bstep (se 1 (by rfl) ⟨575663, by rfl⟩ : syracuseStep 767551 = 1151327) B1151327
theorem B603711 : Blo 603293 603711 := bstep (se 1 (by rfl) ⟨452783, by rfl⟩ : syracuseStep 603711 = 905567) B905567
theorem B603719 : Blo 603293 603719 := bstep (se 1 (by rfl) ⟨452789, by rfl⟩ : syracuseStep 603719 = 905579) B905579
theorem B1291963 : Blo 603293 1291963 := bstep (se 1 (by rfl) ⟨968972, by rfl⟩ : syracuseStep 1291963 = 1937945) B1937945
theorem B2045627 : Blo 603293 2045627 := bstep (se 1 (by rfl) ⟨1534220, by rfl⟩ : syracuseStep 2045627 = 3068441) B3068441
theorem B603871 : Blo 603293 603871 := bstep (se 1 (by rfl) ⟨452903, by rfl⟩ : syracuseStep 603871 = 905807) B905807
theorem B6534893 : Blo 603293 6534893 := bstep (se 3 (by rfl) ⟨1225292, by rfl⟩ : syracuseStep 6534893 = 2450585) B2450585
theorem B1292039 : Blo 603293 1292039 := bstep (se 1 (by rfl) ⟨969029, by rfl⟩ : syracuseStep 1292039 = 1938059) B1938059
theorem B603951 : Blo 603293 603951 := bstep (se 1 (by rfl) ⟨452963, by rfl⟩ : syracuseStep 603951 = 905927) B905927
theorem B6993719 : Blo 603293 6993719 := bstep (se 1 (by rfl) ⟨5245289, by rfl⟩ : syracuseStep 6993719 = 10490579) B10490579
theorem B604059 : Blo 603293 604059 := bstep (se 1 (by rfl) ⟨453044, by rfl⟩ : syracuseStep 604059 = 906089) B906089
theorem B1357775 : Blo 603293 1357775 := bstep (se 1 (by rfl) ⟨1018331, by rfl⟩ : syracuseStep 1357775 = 2036663) B2036663
theorem B604111 : Blo 603293 604111 := bstep (se 1 (by rfl) ⟨453083, by rfl⟩ : syracuseStep 604111 = 906167) B906167
theorem B604135 : Blo 603293 604135 := bstep (se 1 (by rfl) ⟨453101, by rfl⟩ : syracuseStep 604135 = 906203) B906203
theorem B604447 : Blo 603293 604447 := bstep (se 1 (by rfl) ⟨453335, by rfl⟩ : syracuseStep 604447 = 906671) B906671
theorem B768295 : Blo 603293 768295 := bstep (se 1 (by rfl) ⟨576221, by rfl⟩ : syracuseStep 768295 = 1152443) B1152443
theorem B8730949 : Blo 603293 8730949 := bstep (se 4 (by rfl) ⟨818526, by rfl⟩ : syracuseStep 8730949 = 1637053) B1637053
theorem B1358153 : Blo 603293 1358153 := bstep (se 2 (by rfl) ⟨509307, by rfl⟩ : syracuseStep 1358153 = 1018615) B1018615
theorem B1358171 : Blo 603293 1358171 := bstep (se 1 (by rfl) ⟨1018628, by rfl⟩ : syracuseStep 1358171 = 2037257) B2037257
theorem B604507 : Blo 603293 604507 := bstep (se 1 (by rfl) ⟨453380, by rfl⟩ : syracuseStep 604507 = 906761) B906761
theorem B604527 : Blo 603293 604527 := bstep (se 1 (by rfl) ⟨453395, by rfl⟩ : syracuseStep 604527 = 906791) B906791
theorem B604583 : Blo 603293 604583 := bstep (se 1 (by rfl) ⟨453437, by rfl⟩ : syracuseStep 604583 = 906875) B906875
theorem B604667 : Blo 603293 604667 := bstep (se 1 (by rfl) ⟨453500, by rfl⟩ : syracuseStep 604667 = 907001) B907001
theorem B604735 : Blo 603293 604735 := bstep (se 1 (by rfl) ⟨453551, by rfl⟩ : syracuseStep 604735 = 907103) B907103
theorem B604743 : Blo 603293 604743 := bstep (se 1 (by rfl) ⟨453557, by rfl⟩ : syracuseStep 604743 = 907115) B907115
theorem B1718891 : Blo 603293 1718891 := bstep (se 1 (by rfl) ⟨1289168, by rfl⟩ : syracuseStep 1718891 = 2578337) B2578337
theorem B3062447 : Blo 603293 3062447 := bstep (se 1 (by rfl) ⟨2296835, by rfl⟩ : syracuseStep 3062447 = 4593671) B4593671
theorem B604895 : Blo 603293 604895 := bstep (se 1 (by rfl) ⟨453671, by rfl⟩ : syracuseStep 604895 = 907343) B907343
theorem B604975 : Blo 603293 604975 := bstep (se 1 (by rfl) ⟨453731, by rfl⟩ : syracuseStep 604975 = 907463) B907463
theorem B3324739 : Blo 603293 3324739 := bstep (se 1 (by rfl) ⟨2493554, by rfl⟩ : syracuseStep 3324739 = 4987109) B4987109
theorem B1358747 : Blo 603293 1358747 := bstep (se 1 (by rfl) ⟨1019060, by rfl⟩ : syracuseStep 1358747 = 2038121) B2038121
theorem B605083 : Blo 603293 605083 := bstep (se 1 (by rfl) ⟨453812, by rfl⟩ : syracuseStep 605083 = 907625) B907625
theorem B605135 : Blo 603293 605135 := bstep (se 1 (by rfl) ⟨453851, by rfl⟩ : syracuseStep 605135 = 907703) B907703
theorem B605159 : Blo 603293 605159 := bstep (se 1 (by rfl) ⟨453869, by rfl⟩ : syracuseStep 605159 = 907739) B907739
theorem B3062771 : Blo 603293 3062771 := bstep (se 1 (by rfl) ⟨2297078, by rfl⟩ : syracuseStep 3062771 = 4594157) B4594157
theorem B1358945 : Blo 603293 1358945 := bstep (se 2 (by rfl) ⟨509604, by rfl⟩ : syracuseStep 1358945 = 1019209) B1019209
theorem B605471 : Blo 603293 605471 := bstep (se 1 (by rfl) ⟨454103, by rfl⟩ : syracuseStep 605471 = 908207) B908207
theorem B1359143 : Blo 603293 1359143 := bstep (se 1 (by rfl) ⟨1019357, by rfl⟩ : syracuseStep 1359143 = 2038715) B2038715
theorem B605531 : Blo 603293 605531 := bstep (se 1 (by rfl) ⟨454148, by rfl⟩ : syracuseStep 605531 = 908297) B908297
theorem B605551 : Blo 603293 605551 := bstep (se 1 (by rfl) ⟨454163, by rfl⟩ : syracuseStep 605551 = 908327) B908327
theorem B605607 : Blo 603293 605607 := bstep (se 1 (by rfl) ⟨454205, by rfl⟩ : syracuseStep 605607 = 908411) B908411
theorem B605691 : Blo 603293 605691 := bstep (se 1 (by rfl) ⟨454268, by rfl⟩ : syracuseStep 605691 = 908537) B908537
theorem B605759 : Blo 603293 605759 := bstep (se 1 (by rfl) ⟨454319, by rfl⟩ : syracuseStep 605759 = 908639) B908639
theorem B605767 : Blo 603293 605767 := bstep (se 1 (by rfl) ⟨454325, by rfl⟩ : syracuseStep 605767 = 908651) B908651
theorem B2047571 : Blo 603293 2047571 := bstep (se 1 (by rfl) ⟨1535678, by rfl⟩ : syracuseStep 2047571 = 3071357) B3071357
theorem B1359521 : Blo 603293 1359521 := bstep (se 2 (by rfl) ⟨509820, by rfl⟩ : syracuseStep 1359521 = 1019641) B1019641
theorem B605919 : Blo 603293 605919 := bstep (se 1 (by rfl) ⟨454439, by rfl⟩ : syracuseStep 605919 = 908879) B908879
theorem B605999 : Blo 603293 605999 := bstep (se 1 (by rfl) ⟨454499, by rfl⟩ : syracuseStep 605999 = 908999) B908999
theorem B606107 : Blo 603293 606107 := bstep (se 1 (by rfl) ⟨454580, by rfl⟩ : syracuseStep 606107 = 909161) B909161
theorem B606159 : Blo 603293 606159 := bstep (se 1 (by rfl) ⟨454619, by rfl⟩ : syracuseStep 606159 = 909239) B909239
theorem B606183 : Blo 603293 606183 := bstep (se 1 (by rfl) ⟨454637, by rfl⟩ : syracuseStep 606183 = 909275) B909275
theorem B1359881 : Blo 603293 1359881 := bstep (se 2 (by rfl) ⟨509955, by rfl⟩ : syracuseStep 1359881 = 1019911) B1019911
theorem B17448979 : Blo 603293 17448979 := bstep (se 1 (by rfl) ⟨13086734, by rfl⟩ : syracuseStep 17448979 = 26173469) B26173469
theorem B1720531 : Blo 603293 1720531 := bstep (se 1 (by rfl) ⟨1290398, by rfl⟩ : syracuseStep 1720531 = 2580797) B2580797
theorem B3064067 : Blo 603293 3064067 := bstep (se 1 (by rfl) ⟨2298050, by rfl⟩ : syracuseStep 3064067 = 4596101) B4596101
theorem B606495 : Blo 603293 606495 := bstep (se 1 (by rfl) ⟨454871, by rfl⟩ : syracuseStep 606495 = 909743) B909743
theorem B606555 : Blo 603293 606555 := bstep (se 1 (by rfl) ⟨454916, by rfl⟩ : syracuseStep 606555 = 909833) B909833
theorem B606575 : Blo 603293 606575 := bstep (se 1 (by rfl) ⟨454931, by rfl⟩ : syracuseStep 606575 = 909863) B909863
theorem B1360295 : Blo 603293 1360295 := bstep (se 1 (by rfl) ⟨1020221, by rfl⟩ : syracuseStep 1360295 = 2040443) B2040443
theorem B606631 : Blo 603293 606631 := bstep (se 1 (by rfl) ⟨454973, by rfl⟩ : syracuseStep 606631 = 909947) B909947
theorem B606715 : Blo 603293 606715 := bstep (se 1 (by rfl) ⟨455036, by rfl⟩ : syracuseStep 606715 = 910073) B910073
theorem B1360403 : Blo 603293 1360403 := bstep (se 1 (by rfl) ⟨1020302, by rfl⟩ : syracuseStep 1360403 = 2040605) B2040605
theorem B606783 : Blo 603293 606783 := bstep (se 1 (by rfl) ⟨455087, by rfl⟩ : syracuseStep 606783 = 910175) B910175
theorem B2179655 : Blo 603293 2179655 := bstep (se 1 (by rfl) ⟨1634741, by rfl⟩ : syracuseStep 2179655 = 3269483) B3269483
theorem B3064391 : Blo 603293 3064391 := bstep (se 1 (by rfl) ⟨2298293, by rfl⟩ : syracuseStep 3064391 = 4596587) B4596587
theorem B1360457 : Blo 603293 1360457 := bstep (se 2 (by rfl) ⟨510171, by rfl⟩ : syracuseStep 1360457 = 1020343) B1020343
theorem B606791 : Blo 603293 606791 := bstep (se 1 (by rfl) ⟨455093, by rfl⟩ : syracuseStep 606791 = 910187) B910187
theorem B606943 : Blo 603293 606943 := bstep (se 1 (by rfl) ⟨455207, by rfl⟩ : syracuseStep 606943 = 910415) B910415
theorem B607023 : Blo 603293 607023 := bstep (se 1 (by rfl) ⟨455267, by rfl⟩ : syracuseStep 607023 = 910535) B910535
theorem B1295183 : Blo 603293 1295183 := bstep (se 1 (by rfl) ⟨971387, by rfl⟩ : syracuseStep 1295183 = 1942775) B1942775
theorem B607131 : Blo 603293 607131 := bstep (se 1 (by rfl) ⟨455348, by rfl⟩ : syracuseStep 607131 = 910697) B910697
theorem B607183 : Blo 603293 607183 := bstep (se 1 (by rfl) ⟨455387, by rfl⟩ : syracuseStep 607183 = 910775) B910775
theorem B12469211 : Blo 603293 12469211 := bstep (se 1 (by rfl) ⟨9351908, by rfl⟩ : syracuseStep 12469211 = 18703817) B18703817
theorem B3458011 : Blo 603293 3458011 := bstep (se 1 (by rfl) ⟨2593508, by rfl⟩ : syracuseStep 3458011 = 5187017) B5187017
theorem B1360871 : Blo 603293 1360871 := bstep (se 1 (by rfl) ⟨1020653, by rfl⟩ : syracuseStep 1360871 = 2041307) B2041307
theorem B607207 : Blo 603293 607207 := bstep (se 1 (by rfl) ⟨455405, by rfl⟩ : syracuseStep 607207 = 910811) B910811
theorem B1655795 : Blo 603293 1655795 := bstep (se 1 (by rfl) ⟨1241846, by rfl⟩ : syracuseStep 1655795 = 2483693) B2483693
theorem B1164575 : Blo 603293 1164575 := bstep (se 1 (by rfl) ⟨873431, by rfl⟩ : syracuseStep 1164575 = 1746863) B1746863
theorem B1361249 : Blo 603293 1361249 := bstep (se 2 (by rfl) ⟨510468, by rfl⟩ : syracuseStep 1361249 = 1020937) B1020937
theorem B5162413 : Blo 603293 5162413 := bstep (se 3 (by rfl) ⟨967952, by rfl⟩ : syracuseStep 5162413 = 1935905) B1935905
theorem B1361339 : Blo 603293 1361339 := bstep (se 1 (by rfl) ⟨1021004, by rfl⟩ : syracuseStep 1361339 = 2042009) B2042009
theorem B39142925 : Blo 603293 39142925 := bstep (se 3 (by rfl) ⟨7339298, by rfl⟩ : syracuseStep 39142925 = 14678597) B14678597
theorem B7357985 : Blo 603293 7357985 := bstep (se 2 (by rfl) ⟨2759244, by rfl⟩ : syracuseStep 7357985 = 5518489) B5518489
theorem B24823331 : Blo 603293 24823331 := bstep (se 1 (by rfl) ⟨18617498, by rfl⟩ : syracuseStep 24823331 = 37234997) B37234997
theorem B1361465 : Blo 603293 1361465 := bstep (se 2 (by rfl) ⟨510549, by rfl⟩ : syracuseStep 1361465 = 1021099) B1021099
theorem B3065687 : Blo 603293 3065687 := bstep (se 1 (by rfl) ⟨2299265, by rfl⟩ : syracuseStep 3065687 = 4598531) B4598531
theorem B1722217 : Blo 603293 1722217 := bstep (se 2 (by rfl) ⟨645831, by rfl⟩ : syracuseStep 1722217 = 1291663) B1291663
theorem B1362131 : Blo 603293 1362131 := bstep (se 1 (by rfl) ⟨1021598, by rfl⟩ : syracuseStep 1362131 = 2043197) B2043197
theorem B1362185 : Blo 603293 1362185 := bstep (se 2 (by rfl) ⟨510819, by rfl⟩ : syracuseStep 1362185 = 1021639) B1021639
theorem B2803997 : Blo 603293 2803997 := bstep (se 3 (by rfl) ⟨525749, by rfl⟩ : syracuseStep 2803997 = 1051499) B1051499
theorem B1296823 : Blo 603293 1296823 := bstep (se 1 (by rfl) ⟨972617, by rfl⟩ : syracuseStep 1296823 = 1945235) B1945235
theorem B1362401 : Blo 603293 1362401 := bstep (se 2 (by rfl) ⟨510900, by rfl⟩ : syracuseStep 1362401 = 1021801) B1021801
theorem B969337 : Blo 603293 969337 := bstep (se 2 (by rfl) ⟨363501, by rfl⟩ : syracuseStep 969337 = 727003) B727003
theorem B1362707 : Blo 603293 1362707 := bstep (se 1 (by rfl) ⟨1022030, by rfl⟩ : syracuseStep 1362707 = 2044061) B2044061
theorem B3689387 : Blo 603293 3689387 := bstep (se 1 (by rfl) ⟨2767040, by rfl⟩ : syracuseStep 3689387 = 5534081) B5534081
theorem B226446353 : Blo 603293 226446353 := bstep (se 2 (by rfl) ⟨84917382, by rfl⟩ : syracuseStep 226446353 = 169834765) B169834765
theorem B1363067 : Blo 603293 1363067 := bstep (se 1 (by rfl) ⟨1022300, by rfl⟩ : syracuseStep 1363067 = 2044601) B2044601
theorem B1363193 : Blo 603293 1363193 := bstep (se 2 (by rfl) ⟨511197, by rfl⟩ : syracuseStep 1363193 = 1022395) B1022395
theorem B1363337 : Blo 603293 1363337 := bstep (se 2 (by rfl) ⟨511251, by rfl⟩ : syracuseStep 1363337 = 1022503) B1022503
theorem B1723835 : Blo 603293 1723835 := bstep (se 1 (by rfl) ⟨1292876, by rfl⟩ : syracuseStep 1723835 = 2585753) B2585753
theorem B1363463 : Blo 603293 1363463 := bstep (se 1 (by rfl) ⟨1022597, by rfl⟩ : syracuseStep 1363463 = 2045195) B2045195
theorem B1527457 : Blo 603293 1527457 := bstep (se 2 (by rfl) ⟨572796, by rfl⟩ : syracuseStep 1527457 = 1145593) B1145593
theorem B1363643 : Blo 603293 1363643 := bstep (se 1 (by rfl) ⟨1022732, by rfl⟩ : syracuseStep 1363643 = 2045465) B2045465
theorem B1527599 : Blo 603293 1527599 := bstep (se 1 (by rfl) ⟨1145699, by rfl⟩ : syracuseStep 1527599 = 2291399) B2291399
theorem B905015 : Blo 603293 905015 := bstep (se 1 (by rfl) ⟨678761, by rfl⟩ : syracuseStep 905015 = 1357523) B1357523
theorem B1363769 : Blo 603293 1363769 := bstep (se 2 (by rfl) ⟨511413, by rfl⟩ : syracuseStep 1363769 = 1022827) B1022827
theorem B3067955 : Blo 603293 3067955 := bstep (se 1 (by rfl) ⟨2300966, by rfl⟩ : syracuseStep 3067955 = 4601933) B4601933
theorem B9818171 : Blo 603293 9818171 := bstep (se 1 (by rfl) ⟨7363628, by rfl⟩ : syracuseStep 9818171 = 14727257) B14727257
theorem B905321 : Blo 603293 905321 := bstep (se 2 (by rfl) ⟨339495, by rfl⟩ : syracuseStep 905321 = 678991) B678991
theorem B905639 : Blo 603293 905639 := bstep (se 1 (by rfl) ⟨679229, by rfl⟩ : syracuseStep 905639 = 1358459) B1358459
theorem B1364399 : Blo 603293 1364399 := bstep (se 1 (by rfl) ⟨1023299, by rfl⟩ : syracuseStep 1364399 = 2046599) B2046599
theorem B1528247 : Blo 603293 1528247 := bstep (se 1 (by rfl) ⟨1146185, by rfl⟩ : syracuseStep 1528247 = 2292371) B2292371
theorem B1364435 : Blo 603293 1364435 := bstep (se 1 (by rfl) ⟨1023326, by rfl⟩ : syracuseStep 1364435 = 2046653) B2046653
theorem B905723 : Blo 603293 905723 := bstep (se 1 (by rfl) ⟨679292, by rfl⟩ : syracuseStep 905723 = 1358585) B1358585
theorem B1364543 : Blo 603293 1364543 := bstep (se 1 (by rfl) ⟨1023407, by rfl⟩ : syracuseStep 1364543 = 2046815) B2046815
theorem B905849 : Blo 603293 905849 := bstep (se 2 (by rfl) ⟨339693, by rfl⟩ : syracuseStep 905849 = 679387) B679387
theorem B1364651 : Blo 603293 1364651 := bstep (se 1 (by rfl) ⟨1023488, by rfl⟩ : syracuseStep 1364651 = 2046977) B2046977
theorem B905903 : Blo 603293 905903 := bstep (se 1 (by rfl) ⟨679427, by rfl⟩ : syracuseStep 905903 = 1358855) B1358855
theorem B905951 : Blo 603293 905951 := bstep (se 1 (by rfl) ⟨679463, by rfl⟩ : syracuseStep 905951 = 1358927) B1358927
theorem B906215 : Blo 603293 906215 := bstep (se 1 (by rfl) ⟨679661, by rfl⟩ : syracuseStep 906215 = 1359323) B1359323
theorem B1365191 : Blo 603293 1365191 := bstep (se 1 (by rfl) ⟨1023893, by rfl⟩ : syracuseStep 1365191 = 2047787) B2047787
theorem B906473 : Blo 603293 906473 := bstep (se 2 (by rfl) ⟨339927, by rfl⟩ : syracuseStep 906473 = 679855) B679855
theorem B906527 : Blo 603293 906527 := bstep (se 1 (by rfl) ⟨679895, by rfl⟩ : syracuseStep 906527 = 1359791) B1359791
theorem B1365371 : Blo 603293 1365371 := bstep (se 1 (by rfl) ⟨1024028, by rfl⟩ : syracuseStep 1365371 = 2048057) B2048057
theorem B906695 : Blo 603293 906695 := bstep (se 1 (by rfl) ⟨680021, by rfl⟩ : syracuseStep 906695 = 1360043) B1360043
theorem B1365497 : Blo 603293 1365497 := bstep (se 2 (by rfl) ⟨512061, by rfl⟩ : syracuseStep 1365497 = 1024123) B1024123
theorem B1529351 : Blo 603293 1529351 := bstep (se 1 (by rfl) ⟨1147013, by rfl⟩ : syracuseStep 1529351 = 2294027) B2294027
theorem B1529401 : Blo 603293 1529401 := bstep (se 2 (by rfl) ⟨573525, by rfl⟩ : syracuseStep 1529401 = 1147051) B1147051
theorem B1365587 : Blo 603293 1365587 := bstep (se 1 (by rfl) ⟨1024190, by rfl⟩ : syracuseStep 1365587 = 2048381) B2048381
theorem B3069575 : Blo 603293 3069575 := bstep (se 1 (by rfl) ⟨2302181, by rfl⟩ : syracuseStep 3069575 = 4604363) B4604363
theorem B1365767 : Blo 603293 1365767 := bstep (se 1 (by rfl) ⟨1024325, by rfl⟩ : syracuseStep 1365767 = 2048651) B2048651
theorem B907049 : Blo 603293 907049 := bstep (se 2 (by rfl) ⟨340143, by rfl⟩ : syracuseStep 907049 = 680287) B680287
theorem B907055 : Blo 603293 907055 := bstep (se 1 (by rfl) ⟨680291, by rfl⟩ : syracuseStep 907055 = 1360583) B1360583
theorem B1529705 : Blo 603293 1529705 := bstep (se 2 (by rfl) ⟨573639, by rfl⟩ : syracuseStep 1529705 = 1147279) B1147279
theorem B2578679 : Blo 603293 2578679 := bstep (se 1 (by rfl) ⟨1934009, by rfl⟩ : syracuseStep 2578679 = 3868019) B3868019
theorem B1726717 : Blo 603293 1726717 := bstep (se 3 (by rfl) ⟨323759, by rfl⟩ : syracuseStep 1726717 = 647519) B647519
theorem B907529 : Blo 603293 907529 := bstep (se 2 (by rfl) ⟨340323, by rfl⟩ : syracuseStep 907529 = 680647) B680647
theorem B1366379 : Blo 603293 1366379 := bstep (se 1 (by rfl) ⟨1024784, by rfl⟩ : syracuseStep 1366379 = 2049569) B2049569
theorem B907631 : Blo 603293 907631 := bstep (se 1 (by rfl) ⟨680723, by rfl⟩ : syracuseStep 907631 = 1361447) B1361447
theorem B645575 : Blo 603293 645575 := bstep (se 1 (by rfl) ⟨484181, by rfl⟩ : syracuseStep 645575 = 968363) B968363
theorem B1530323 : Blo 603293 1530323 := bstep (se 1 (by rfl) ⟨1147742, by rfl⟩ : syracuseStep 1530323 = 2295485) B2295485
theorem B907847 : Blo 603293 907847 := bstep (se 1 (by rfl) ⟨680885, by rfl⟩ : syracuseStep 907847 = 1361771) B1361771
theorem B907883 : Blo 603293 907883 := bstep (se 1 (by rfl) ⟨680912, by rfl⟩ : syracuseStep 907883 = 1361825) B1361825
theorem B5823251 : Blo 603293 5823251 := bstep (se 1 (by rfl) ⟨4367438, by rfl⟩ : syracuseStep 5823251 = 8734877) B8734877
theorem B908111 : Blo 603293 908111 := bstep (se 1 (by rfl) ⟨681083, by rfl⟩ : syracuseStep 908111 = 1362167) B1362167
theorem B678811 : Blo 603293 678811 := bstep (se 1 (by rfl) ⟨509108, by rfl⟩ : syracuseStep 678811 = 1018217) B1018217
theorem B3267515 : Blo 603293 3267515 := bstep (se 1 (by rfl) ⟨2450636, by rfl⟩ : syracuseStep 3267515 = 4901273) B4901273
theorem B2612443 : Blo 603293 2612443 := bstep (se 1 (by rfl) ⟨1959332, by rfl⟩ : syracuseStep 2612443 = 3918665) B3918665
theorem B908507 : Blo 603293 908507 := bstep (se 1 (by rfl) ⟨681380, by rfl⟩ : syracuseStep 908507 = 1362761) B1362761
theorem B3071195 : Blo 603293 3071195 := bstep (se 1 (by rfl) ⟨2303396, by rfl⟩ : syracuseStep 3071195 = 4606793) B4606793
theorem B679207 : Blo 603293 679207 := bstep (se 1 (by rfl) ⟨509405, by rfl⟩ : syracuseStep 679207 = 1018811) B1018811
theorem B679279 : Blo 603293 679279 := bstep (se 1 (by rfl) ⟨509459, by rfl⟩ : syracuseStep 679279 = 1018919) B1018919
theorem B908681 : Blo 603293 908681 := bstep (se 2 (by rfl) ⟨340755, by rfl⟩ : syracuseStep 908681 = 681511) B681511
theorem B4906489 : Blo 603293 4906489 := bstep (se 2 (by rfl) ⟨1839933, by rfl⟩ : syracuseStep 4906489 = 3679867) B3679867
theorem B1727993 : Blo 603293 1727993 := bstep (se 2 (by rfl) ⟨647997, by rfl⟩ : syracuseStep 1727993 = 1295995) B1295995
theorem B679495 : Blo 603293 679495 := bstep (se 1 (by rfl) ⟨509621, by rfl⟩ : syracuseStep 679495 = 1019243) B1019243
theorem B2186833 : Blo 603293 2186833 := bstep (se 2 (by rfl) ⟨820062, by rfl⟩ : syracuseStep 2186833 = 1640125) B1640125
theorem B1531487 : Blo 603293 1531487 := bstep (se 1 (by rfl) ⟨1148615, by rfl⟩ : syracuseStep 1531487 = 2297231) B2297231
theorem B909035 : Blo 603293 909035 := bstep (se 1 (by rfl) ⟨681776, by rfl⟩ : syracuseStep 909035 = 1363553) B1363553
theorem B909263 : Blo 603293 909263 := bstep (se 1 (by rfl) ⟨681947, by rfl⟩ : syracuseStep 909263 = 1363895) B1363895
theorem B8740871 : Blo 603293 8740871 := bstep (se 1 (by rfl) ⟨6555653, by rfl⟩ : syracuseStep 8740871 = 13111307) B13111307
theorem B3072329 : Blo 603293 3072329 := bstep (se 2 (by rfl) ⟨1152123, by rfl⟩ : syracuseStep 3072329 = 2304247) B2304247
theorem B909659 : Blo 603293 909659 := bstep (se 1 (by rfl) ⟨682244, by rfl⟩ : syracuseStep 909659 = 1364489) B1364489
theorem B1532267 : Blo 603293 1532267 := bstep (se 1 (by rfl) ⟨1149200, by rfl⟩ : syracuseStep 1532267 = 2298401) B2298401
theorem B680359 : Blo 603293 680359 := bstep (se 1 (by rfl) ⟨510269, by rfl⟩ : syracuseStep 680359 = 1020539) B1020539
theorem B1630739 : Blo 603293 1630739 := bstep (se 1 (by rfl) ⟨1223054, by rfl⟩ : syracuseStep 1630739 = 2446109) B2446109
theorem B1532479 : Blo 603293 1532479 := bstep (se 1 (by rfl) ⟨1149359, by rfl⟩ : syracuseStep 1532479 = 2298719) B2298719
theorem B909887 : Blo 603293 909887 := bstep (se 1 (by rfl) ⟨682415, by rfl⟩ : syracuseStep 909887 = 1364831) B1364831
theorem B2581139 : Blo 603293 2581139 := bstep (se 1 (by rfl) ⟨1935854, by rfl⟩ : syracuseStep 2581139 = 3871709) B3871709
theorem B1532591 : Blo 603293 1532591 := bstep (se 1 (by rfl) ⟨1149443, by rfl⟩ : syracuseStep 1532591 = 2298887) B2298887
theorem B910007 : Blo 603293 910007 := bstep (se 1 (by rfl) ⟨682505, by rfl⟩ : syracuseStep 910007 = 1365011) B1365011
theorem B910235 : Blo 603293 910235 := bstep (se 1 (by rfl) ⟨682676, by rfl⟩ : syracuseStep 910235 = 1365353) B1365353
theorem B615323 : Blo 603293 615323 := bstep (se 1 (by rfl) ⟨461492, by rfl⟩ : syracuseStep 615323 = 922985) B922985
theorem B1631195 : Blo 603293 1631195 := bstep (se 1 (by rfl) ⟨1223396, by rfl⟩ : syracuseStep 1631195 = 2446793) B2446793
theorem B680935 : Blo 603293 680935 := bstep (se 1 (by rfl) ⟨510701, by rfl⟩ : syracuseStep 680935 = 1021403) B1021403
theorem B1532915 : Blo 603293 1532915 := bstep (se 1 (by rfl) ⟨1149686, by rfl⟩ : syracuseStep 1532915 = 2299373) B2299373
theorem B1631431 : Blo 603293 1631431 := bstep (se 1 (by rfl) ⟨1223573, by rfl⟩ : syracuseStep 1631431 = 2447147) B2447147
theorem B1533127 : Blo 603293 1533127 := bstep (se 1 (by rfl) ⟨1149845, by rfl⟩ : syracuseStep 1533127 = 2299691) B2299691
theorem B910631 : Blo 603293 910631 := bstep (se 1 (by rfl) ⟨682973, by rfl⟩ : syracuseStep 910631 = 1365947) B1365947
theorem B910715 : Blo 603293 910715 := bstep (se 1 (by rfl) ⟨683036, by rfl⟩ : syracuseStep 910715 = 1366073) B1366073
theorem B910841 : Blo 603293 910841 := bstep (se 2 (by rfl) ⟨341565, by rfl⟩ : syracuseStep 910841 = 683131) B683131
theorem B3073625 : Blo 603293 3073625 := bstep (se 2 (by rfl) ⟨1152609, by rfl⟩ : syracuseStep 3073625 = 2305219) B2305219
theorem B5891945 : Blo 603293 5891945 := bstep (se 2 (by rfl) ⟨2209479, by rfl⟩ : syracuseStep 5891945 = 4418959) B4418959
theorem B1534535 : Blo 603293 1534535 := bstep (se 1 (by rfl) ⟨1150901, by rfl⟩ : syracuseStep 1534535 = 2301803) B2301803
theorem B682591 : Blo 603293 682591 := bstep (se 1 (by rfl) ⟨511943, by rfl⟩ : syracuseStep 682591 = 1023887) B1023887
theorem B1534585 : Blo 603293 1534585 := bstep (se 2 (by rfl) ⟨575469, by rfl⟩ : syracuseStep 1534585 = 1150939) B1150939
theorem B6875927 : Blo 603293 6875927 := bstep (se 1 (by rfl) ⟨5156945, by rfl⟩ : syracuseStep 6875927 = 10313891) B10313891
theorem B8711063 : Blo 603293 8711063 := bstep (se 1 (by rfl) ⟨6533297, by rfl⟩ : syracuseStep 8711063 = 13066595) B13066595
theorem B2583667 : Blo 603293 2583667 := bstep (se 1 (by rfl) ⟨1937750, by rfl⟩ : syracuseStep 2583667 = 3875501) B3875501
theorem B5827787 : Blo 603293 5827787 := bstep (se 1 (by rfl) ⟨4370840, by rfl⟩ : syracuseStep 5827787 = 8741681) B8741681
theorem B2583839 : Blo 603293 2583839 := bstep (se 1 (by rfl) ⟨1937879, by rfl⟩ : syracuseStep 2583839 = 3875759) B3875759
theorem B1011295 : Blo 603293 1011295 := bstep (se 1 (by rfl) ⟨758471, by rfl⟩ : syracuseStep 1011295 = 1516943) B1516943
theorem B3436141 : Blo 603293 3436141 := bstep (se 3 (by rfl) ⟨644276, by rfl⟩ : syracuseStep 3436141 = 1288553) B1288553
theorem B27979453 : Blo 603293 27979453 := bstep (se 3 (by rfl) ⟨5246147, by rfl⟩ : syracuseStep 27979453 = 10492295) B10492295
theorem B23588981 : Blo 603293 23588981 := bstep (se 5 (by rfl) ⟨1105733, by rfl⟩ : syracuseStep 23588981 = 2211467) B2211467
theorem B1536347 : Blo 603293 1536347 := bstep (se 1 (by rfl) ⟨1152260, by rfl⟩ : syracuseStep 1536347 = 2304521) B2304521
theorem B1536367 : Blo 603293 1536367 := bstep (se 1 (by rfl) ⟨1152275, by rfl⟩ : syracuseStep 1536367 = 2304551) B2304551
theorem B59535971 : Blo 603293 59535971 := bstep (se 1 (by rfl) ⟨44651978, by rfl⟩ : syracuseStep 59535971 = 89303957) B89303957
theorem B16610197 : Blo 603293 16610197 := bstep (se 6 (by rfl) ⟨389301, by rfl⟩ : syracuseStep 16610197 = 778603) B778603
theorem B1537015 : Blo 603293 1537015 := bstep (se 1 (by rfl) ⟨1152761, by rfl⟩ : syracuseStep 1537015 = 2305523) B2305523
theorem B2913529 : Blo 603293 2913529 := bstep (se 2 (by rfl) ⟨1092573, by rfl⟩ : syracuseStep 2913529 = 2185147) B2185147
theorem B1307935 : Blo 603293 1307935 := bstep (se 1 (by rfl) ⟨980951, by rfl⟩ : syracuseStep 1307935 = 1961903) B1961903
theorem B12089249 : Blo 603293 12089249 := bstep (se 2 (by rfl) ⟨4533468, by rfl⟩ : syracuseStep 12089249 = 9066937) B9066937
theorem B9598907 : Blo 603293 9598907 := bstep (se 1 (by rfl) ⟨7199180, by rfl⟩ : syracuseStep 9598907 = 14398361) B14398361
theorem B5830937 : Blo 603293 5830937 := bstep (se 2 (by rfl) ⟨2186601, by rfl⟩ : syracuseStep 5830937 = 4373203) B4373203
theorem B5241581 : Blo 603293 5241581 := bstep (se 3 (by rfl) ⟨982796, by rfl⟩ : syracuseStep 5241581 = 1965593) B1965593
theorem B7371899 : Blo 603293 7371899 := bstep (se 1 (by rfl) ⟨5528924, by rfl⟩ : syracuseStep 7371899 = 11057849) B11057849
theorem B2588041 : Blo 603293 2588041 := bstep (se 2 (by rfl) ⟨970515, by rfl⟩ : syracuseStep 2588041 = 1941031) B1941031
theorem B2293343 : Blo 603293 2293343 := bstep (se 1 (by rfl) ⟨1720007, by rfl⟩ : syracuseStep 2293343 = 3440015) B3440015
theorem B1572587 : Blo 603293 1572587 := bstep (se 1 (by rfl) ⟨1179440, by rfl⟩ : syracuseStep 1572587 = 2358881) B2358881
theorem B23265305 : Blo 603293 23265305 := bstep (se 2 (by rfl) ⟨8724489, by rfl⟩ : syracuseStep 23265305 = 17448979) B17448979
theorem B2490401 : Blo 603293 2490401 := bstep (se 2 (by rfl) ⟨933900, by rfl⟩ : syracuseStep 2490401 = 1867801) B1867801
theorem B2294041 : Blo 603293 2294041 := bstep (se 2 (by rfl) ⟨860265, by rfl⟩ : syracuseStep 2294041 = 1720531) B1720531
theorem B5178269 : Blo 603293 5178269 := bstep (se 3 (by rfl) ⟨970925, by rfl⟩ : syracuseStep 5178269 = 1941851) B1941851
theorem B1639379 : Blo 603293 1639379 := bstep (se 1 (by rfl) ⟨1229534, by rfl⟩ : syracuseStep 1639379 = 2459069) B2459069
theorem B16548887 : Blo 603293 16548887 := bstep (se 1 (by rfl) ⟨12411665, by rfl⟩ : syracuseStep 16548887 = 24823331) B24823331
theorem B1869331 : Blo 603293 1869331 := bstep (se 1 (by rfl) ⟨1401998, by rfl⟩ : syracuseStep 1869331 = 2803997) B2803997
theorem B2066081 : Blo 603293 2066081 := bstep (se 2 (by rfl) ⟨774780, by rfl⟩ : syracuseStep 2066081 = 1549561) B1549561
theorem B6883217 : Blo 603293 6883217 := bstep (se 2 (by rfl) ⟨2581206, by rfl⟩ : syracuseStep 6883217 = 5162413) B5162413
theorem B2459591 : Blo 603293 2459591 := bstep (se 1 (by rfl) ⟨1844693, by rfl⟩ : syracuseStep 2459591 = 3689387) B3689387
theorem B150964235 : Blo 603293 150964235 := bstep (se 1 (by rfl) ⟨113223176, by rfl⟩ : syracuseStep 150964235 = 226446353) B226446353
theorem B1935485 : Blo 603293 1935485 := bstep (se 3 (by rfl) ⟨362903, by rfl⟩ : syracuseStep 1935485 = 725807) B725807
theorem B1149223 : Blo 603293 1149223 := bstep (se 1 (by rfl) ⟨861917, by rfl⟩ : syracuseStep 1149223 = 1723835) B1723835
theorem B1640861 : Blo 603293 1640861 := bstep (se 3 (by rfl) ⟨307661, by rfl⟩ : syracuseStep 1640861 = 615323) B615323
theorem B2296289 : Blo 603293 2296289 := bstep (se 2 (by rfl) ⟨861108, by rfl⟩ : syracuseStep 2296289 = 1722217) B1722217
theorem B1018399 : Blo 603293 1018399 := bstep (se 1 (by rfl) ⟨763799, by rfl⟩ : syracuseStep 1018399 = 1527599) B1527599
theorem B2755415 : Blo 603293 2755415 := bstep (se 1 (by rfl) ⟨2066561, by rfl⟩ : syracuseStep 2755415 = 4133123) B4133123
theorem B1018831 : Blo 603293 1018831 := bstep (se 1 (by rfl) ⟨764123, by rfl⟩ : syracuseStep 1018831 = 1528247) B1528247
theorem B1379551 : Blo 603293 1379551 := bstep (se 1 (by rfl) ⟨1034663, by rfl⟩ : syracuseStep 1379551 = 2069327) B2069327
theorem B4918495 : Blo 603293 4918495 := bstep (se 1 (by rfl) ⟨3688871, by rfl⟩ : syracuseStep 4918495 = 7377743) B7377743
theorem B6884675 : Blo 603293 6884675 := bstep (se 1 (by rfl) ⟨5163506, by rfl⟩ : syracuseStep 6884675 = 10327013) B10327013
theorem B5836283 : Blo 603293 5836283 := bstep (se 1 (by rfl) ⟨4377212, by rfl⟩ : syracuseStep 5836283 = 8754425) B8754425
theorem B1150537 : Blo 603293 1150537 := bstep (se 2 (by rfl) ⟨431451, by rfl⟩ : syracuseStep 1150537 = 862903) B862903
theorem B1019567 : Blo 603293 1019567 := bstep (se 1 (by rfl) ⟨764675, by rfl⟩ : syracuseStep 1019567 = 1529351) B1529351
theorem B1150841 : Blo 603293 1150841 := bstep (se 2 (by rfl) ⟨431565, by rfl⟩ : syracuseStep 1150841 = 863131) B863131
theorem B1019803 : Blo 603293 1019803 := bstep (se 1 (by rfl) ⟨764852, by rfl⟩ : syracuseStep 1019803 = 1529705) B1529705
theorem B3444889 : Blo 603293 3444889 := bstep (se 2 (by rfl) ⟨1291833, by rfl⟩ : syracuseStep 3444889 = 2583667) B2583667
theorem B1020215 : Blo 603293 1020215 := bstep (se 1 (by rfl) ⟨765161, by rfl⟩ : syracuseStep 1020215 = 1530323) B1530323
theorem B2036339 : Blo 603293 2036339 := bstep (se 1 (by rfl) ⟨1527254, by rfl⟩ : syracuseStep 2036339 = 3054509) B3054509
theorem B6886133 : Blo 603293 6886133 := bstep (se 5 (by rfl) ⟨322787, by rfl⟩ : syracuseStep 6886133 = 645575) B645575
theorem B1348393 : Blo 603293 1348393 := bstep (se 2 (by rfl) ⟨505647, by rfl⟩ : syracuseStep 1348393 = 1011295) B1011295
theorem B2036609 : Blo 603293 2036609 := bstep (se 2 (by rfl) ⟨763728, by rfl⟩ : syracuseStep 2036609 = 1527457) B1527457
theorem B1151995 : Blo 603293 1151995 := bstep (se 1 (by rfl) ⟨863996, by rfl⟩ : syracuseStep 1151995 = 1727993) B1727993
theorem B3937319 : Blo 603293 3937319 := bstep (se 1 (by rfl) ⟨2952989, by rfl⟩ : syracuseStep 3937319 = 5905979) B5905979
theorem B1020991 : Blo 603293 1020991 := bstep (se 1 (by rfl) ⟨765743, by rfl⟩ : syracuseStep 1020991 = 1531487) B1531487
theorem B1152481 : Blo 603293 1152481 := bstep (se 2 (by rfl) ⟨432180, by rfl⟩ : syracuseStep 1152481 = 864361) B864361
theorem B1021511 : Blo 603293 1021511 := bstep (se 1 (by rfl) ⟨766133, by rfl⟩ : syracuseStep 1021511 = 1532267) B1532267
theorem B2037419 : Blo 603293 2037419 := bstep (se 1 (by rfl) ⟨1528064, by rfl⟩ : syracuseStep 2037419 = 3056129) B3056129
theorem B1021727 : Blo 603293 1021727 := bstep (se 1 (by rfl) ⟨766295, by rfl⟩ : syracuseStep 1021727 = 1532591) B1532591
theorem B1087463 : Blo 603293 1087463 := bstep (se 1 (by rfl) ⟨815597, by rfl⟩ : syracuseStep 1087463 = 1631195) B1631195
theorem B2037743 : Blo 603293 2037743 := bstep (se 1 (by rfl) ⟨1528307, by rfl⟩ : syracuseStep 2037743 = 3056615) B3056615
theorem B1021943 : Blo 603293 1021943 := bstep (se 1 (by rfl) ⟨766457, by rfl⟩ : syracuseStep 1021943 = 1532915) B1532915
theorem B1841249 : Blo 603293 1841249 := bstep (se 2 (by rfl) ⟨690468, by rfl⟩ : syracuseStep 1841249 = 1380937) B1380937
theorem B2037959 : Blo 603293 2037959 := bstep (se 1 (by rfl) ⟨1528469, by rfl⟩ : syracuseStep 2037959 = 3056939) B3056939
theorem B2300147 : Blo 603293 2300147 := bstep (se 1 (by rfl) ⟨1725110, by rfl⟩ : syracuseStep 2300147 = 3450221) B3450221
theorem B2038607 : Blo 603293 2038607 := bstep (se 1 (by rfl) ⟨1528955, by rfl⟩ : syracuseStep 2038607 = 3057911) B3057911
theorem B2300831 : Blo 603293 2300831 := bstep (se 1 (by rfl) ⟨1725623, by rfl⟩ : syracuseStep 2300831 = 3451247) B3451247
theorem B1743913 : Blo 603293 1743913 := bstep (se 2 (by rfl) ⟨653967, by rfl⟩ : syracuseStep 1743913 = 1307935) B1307935
theorem B1023023 : Blo 603293 1023023 := bstep (se 1 (by rfl) ⟨767267, by rfl⟩ : syracuseStep 1023023 = 1534535) B1534535
theorem B1023097 : Blo 603293 1023097 := bstep (se 2 (by rfl) ⟨383661, by rfl⟩ : syracuseStep 1023097 = 767323) B767323
theorem B2038931 : Blo 603293 2038931 := bstep (se 1 (by rfl) ⟨1529198, by rfl⟩ : syracuseStep 2038931 = 3058397) B3058397
theorem B5807375 : Blo 603293 5807375 := bstep (se 1 (by rfl) ⟨4355531, by rfl⟩ : syracuseStep 5807375 = 8711063) B8711063
theorem B2039201 : Blo 603293 2039201 := bstep (se 2 (by rfl) ⟨764700, by rfl⟩ : syracuseStep 2039201 = 1529401) B1529401
theorem B1023401 : Blo 603293 1023401 := bstep (se 2 (by rfl) ⟨383775, by rfl⟩ : syracuseStep 1023401 = 767551) B767551
theorem B2039741 : Blo 603293 2039741 := bstep (se 3 (by rfl) ⟨382451, by rfl⟩ : syracuseStep 2039741 = 764903) B764903
theorem B1024231 : Blo 603293 1024231 := bstep (se 1 (by rfl) ⟨768173, by rfl⟩ : syracuseStep 1024231 = 1536347) B1536347
theorem B2302289 : Blo 603293 2302289 := bstep (se 2 (by rfl) ⟨863358, by rfl⟩ : syracuseStep 2302289 = 1726717) B1726717
theorem B1024393 : Blo 603293 1024393 := bstep (se 2 (by rfl) ⟨384147, by rfl⟩ : syracuseStep 1024393 = 768295) B768295
theorem B39690647 : Blo 603293 39690647 := bstep (se 1 (by rfl) ⟨29767985, by rfl⟩ : syracuseStep 39690647 = 59535971) B59535971
theorem B11641265 : Blo 603293 11641265 := bstep (se 2 (by rfl) ⟨4365474, by rfl⟩ : syracuseStep 11641265 = 8730949) B8730949
theorem B4432985 : Blo 603293 4432985 := bstep (se 2 (by rfl) ⟨1662369, by rfl⟩ : syracuseStep 4432985 = 3324739) B3324739
theorem B861359 : Blo 603293 861359 := bstep (se 1 (by rfl) ⟨646019, by rfl⟩ : syracuseStep 861359 = 1292039) B1292039
theorem B4662479 : Blo 603293 4662479 := bstep (se 1 (by rfl) ⟨3496859, by rfl⟩ : syracuseStep 4662479 = 6993719) B6993719
theorem B6399271 : Blo 603293 6399271 := bstep (se 1 (by rfl) ⟨4799453, by rfl⟩ : syracuseStep 6399271 = 9598907) B9598907
theorem B3483257 : Blo 603293 3483257 := bstep (se 2 (by rfl) ⟨1306221, by rfl⟩ : syracuseStep 3483257 = 2612443) B2612443
theorem B2041631 : Blo 603293 2041631 := bstep (se 1 (by rfl) ⟨1531223, by rfl⟩ : syracuseStep 2041631 = 3062447) B3062447
theorem B3450721 : Blo 603293 3450721 := bstep (se 2 (by rfl) ⟨1294020, by rfl⟩ : syracuseStep 3450721 = 2588041) B2588041
theorem B2041847 : Blo 603293 2041847 := bstep (se 1 (by rfl) ⟨1531385, by rfl⟩ : syracuseStep 2041847 = 3062771) B3062771
theorem B2042711 : Blo 603293 2042711 := bstep (se 1 (by rfl) ⟨1532033, by rfl⟩ : syracuseStep 2042711 = 3064067) B3064067
theorem B1453103 : Blo 603293 1453103 := bstep (se 1 (by rfl) ⟨1089827, by rfl⟩ : syracuseStep 1453103 = 2179655) B2179655
theorem B2042927 : Blo 603293 2042927 := bstep (se 1 (by rfl) ⟨1532195, by rfl⟩ : syracuseStep 2042927 = 3064391) B3064391
theorem B863455 : Blo 603293 863455 := bstep (se 1 (by rfl) ⟨647591, by rfl⟩ : syracuseStep 863455 = 1295183) B1295183
theorem B2043305 : Blo 603293 2043305 := bstep (se 2 (by rfl) ⟨766239, by rfl⟩ : syracuseStep 2043305 = 1532479) B1532479
theorem B2076155 : Blo 603293 2076155 := bstep (se 1 (by rfl) ⟨1557116, by rfl⟩ : syracuseStep 2076155 = 3114233) B3114233
theorem B26095283 : Blo 603293 26095283 := bstep (se 1 (by rfl) ⟨19571462, by rfl⟩ : syracuseStep 26095283 = 39142925) B39142925
theorem B6205177 : Blo 603293 6205177 := bstep (se 2 (by rfl) ⟨2326941, by rfl⟩ : syracuseStep 6205177 = 4653883) B4653883
theorem B7778065 : Blo 603293 7778065 := bstep (se 2 (by rfl) ⟨2916774, by rfl⟩ : syracuseStep 7778065 = 5833549) B5833549
theorem B1290023 : Blo 603293 1290023 := bstep (se 1 (by rfl) ⟨967517, by rfl⟩ : syracuseStep 1290023 = 1935035) B1935035
theorem B2043791 : Blo 603293 2043791 := bstep (se 1 (by rfl) ⟨1532843, by rfl⟩ : syracuseStep 2043791 = 3065687) B3065687
theorem B3453137 : Blo 603293 3453137 := bstep (se 2 (by rfl) ⟨1294926, by rfl⟩ : syracuseStep 3453137 = 2589853) B2589853
theorem B2044169 : Blo 603293 2044169 := bstep (se 2 (by rfl) ⟨766563, by rfl⟩ : syracuseStep 2044169 = 1533127) B1533127
theorem B3060179 : Blo 603293 3060179 := bstep (se 1 (by rfl) ⟨2295134, by rfl⟩ : syracuseStep 3060179 = 4590269) B4590269
theorem B3453455 : Blo 603293 3453455 := bstep (se 1 (by rfl) ⟨2590091, by rfl⟩ : syracuseStep 3453455 = 5180183) B5180183
theorem B603343 : Blo 603293 603343 := bstep (se 1 (by rfl) ⟨452507, by rfl⟩ : syracuseStep 603343 = 905015) B905015
theorem B2045303 : Blo 603293 2045303 := bstep (se 1 (by rfl) ⟨1533977, by rfl⟩ : syracuseStep 2045303 = 3067955) B3067955
theorem B603547 : Blo 603293 603547 := bstep (se 1 (by rfl) ⟨452660, by rfl⟩ : syracuseStep 603547 = 905321) B905321
theorem B603759 : Blo 603293 603759 := bstep (se 1 (by rfl) ⟨452819, by rfl⟩ : syracuseStep 603759 = 905639) B905639
theorem B603815 : Blo 603293 603815 := bstep (se 1 (by rfl) ⟨452861, by rfl⟩ : syracuseStep 603815 = 905723) B905723
theorem B603899 : Blo 603293 603899 := bstep (se 1 (by rfl) ⟨452924, by rfl⟩ : syracuseStep 603899 = 905849) B905849
theorem B603935 : Blo 603293 603935 := bstep (se 1 (by rfl) ⟨452951, by rfl⟩ : syracuseStep 603935 = 905903) B905903
theorem B1357631 : Blo 603293 1357631 := bstep (se 1 (by rfl) ⟨1018223, by rfl⟩ : syracuseStep 1357631 = 2036447) B2036447
theorem B603967 : Blo 603293 603967 := bstep (se 1 (by rfl) ⟨452975, by rfl⟩ : syracuseStep 603967 = 905951) B905951
theorem B604143 : Blo 603293 604143 := bstep (se 1 (by rfl) ⟨453107, by rfl⟩ : syracuseStep 604143 = 906215) B906215
theorem B1357919 : Blo 603293 1357919 := bstep (se 1 (by rfl) ⟨1018439, by rfl⟩ : syracuseStep 1357919 = 2036879) B2036879
theorem B15775859 : Blo 603293 15775859 := bstep (se 1 (by rfl) ⟨11831894, by rfl⟩ : syracuseStep 15775859 = 23663789) B23663789
theorem B604315 : Blo 603293 604315 := bstep (se 1 (by rfl) ⟨453236, by rfl⟩ : syracuseStep 604315 = 906473) B906473
theorem B1292449 : Blo 603293 1292449 := bstep (se 2 (by rfl) ⟨484668, by rfl⟩ : syracuseStep 1292449 = 969337) B969337
theorem B2046113 : Blo 603293 2046113 := bstep (se 2 (by rfl) ⟨767292, by rfl⟩ : syracuseStep 2046113 = 1534585) B1534585
theorem B604351 : Blo 603293 604351 := bstep (se 1 (by rfl) ⟨453263, by rfl⟩ : syracuseStep 604351 = 906527) B906527
theorem B604463 : Blo 603293 604463 := bstep (se 1 (by rfl) ⟨453347, by rfl⟩ : syracuseStep 604463 = 906695) B906695
theorem B2046383 : Blo 603293 2046383 := bstep (se 1 (by rfl) ⟨1534787, by rfl⟩ : syracuseStep 2046383 = 3069575) B3069575
theorem B604699 : Blo 603293 604699 := bstep (se 1 (by rfl) ⟨453524, by rfl⟩ : syracuseStep 604699 = 907049) B907049
theorem B604703 : Blo 603293 604703 := bstep (se 1 (by rfl) ⟨453527, by rfl⟩ : syracuseStep 604703 = 907055) B907055
theorem B1456697 : Blo 603293 1456697 := bstep (se 2 (by rfl) ⟨546261, by rfl⟩ : syracuseStep 1456697 = 1092523) B1092523
theorem B1227401 : Blo 603293 1227401 := bstep (se 2 (by rfl) ⟨460275, by rfl⟩ : syracuseStep 1227401 = 920551) B920551
theorem B1719119 : Blo 603293 1719119 := bstep (se 1 (by rfl) ⟨1289339, by rfl⟩ : syracuseStep 1719119 = 2578679) B2578679
theorem B1358675 : Blo 603293 1358675 := bstep (se 1 (by rfl) ⟨1019006, by rfl⟩ : syracuseStep 1358675 = 2038013) B2038013
theorem B605019 : Blo 603293 605019 := bstep (se 1 (by rfl) ⟨453764, by rfl⟩ : syracuseStep 605019 = 907529) B907529
theorem B605087 : Blo 603293 605087 := bstep (se 1 (by rfl) ⟨453815, by rfl⟩ : syracuseStep 605087 = 907631) B907631
theorem B605231 : Blo 603293 605231 := bstep (se 1 (by rfl) ⟨453923, by rfl⟩ : syracuseStep 605231 = 907847) B907847
theorem B605255 : Blo 603293 605255 := bstep (se 1 (by rfl) ⟨453941, by rfl⟩ : syracuseStep 605255 = 907883) B907883
theorem B3882167 : Blo 603293 3882167 := bstep (se 1 (by rfl) ⟨2911625, by rfl⟩ : syracuseStep 3882167 = 5823251) B5823251
theorem B605407 : Blo 603293 605407 := bstep (se 1 (by rfl) ⟨454055, by rfl⟩ : syracuseStep 605407 = 908111) B908111
theorem B2178343 : Blo 603293 2178343 := bstep (se 1 (by rfl) ⟨1633757, by rfl⟩ : syracuseStep 2178343 = 3267515) B3267515
theorem B1359215 : Blo 603293 1359215 := bstep (se 1 (by rfl) ⟨1019411, by rfl⟩ : syracuseStep 1359215 = 2038823) B2038823
theorem B1293679 : Blo 603293 1293679 := bstep (se 1 (by rfl) ⟨970259, by rfl⟩ : syracuseStep 1293679 = 1940519) B1940519
theorem B605671 : Blo 603293 605671 := bstep (se 1 (by rfl) ⟨454253, by rfl⟩ : syracuseStep 605671 = 908507) B908507
theorem B2047463 : Blo 603293 2047463 := bstep (se 1 (by rfl) ⟨1535597, by rfl⟩ : syracuseStep 2047463 = 3071195) B3071195
theorem B37305937 : Blo 603293 37305937 := bstep (se 2 (by rfl) ⟨13989726, by rfl⟩ : syracuseStep 37305937 = 27979453) B27979453
theorem B605787 : Blo 603293 605787 := bstep (se 1 (by rfl) ⟨454340, by rfl⟩ : syracuseStep 605787 = 908681) B908681
theorem B15711853 : Blo 603293 15711853 := bstep (se 3 (by rfl) ⟨2945972, by rfl⟩ : syracuseStep 15711853 = 5891945) B5891945
theorem B1359503 : Blo 603293 1359503 := bstep (se 1 (by rfl) ⟨1019627, by rfl⟩ : syracuseStep 1359503 = 2039255) B2039255
theorem B8306363 : Blo 603293 8306363 := bstep (se 1 (by rfl) ⟨6229772, by rfl⟩ : syracuseStep 8306363 = 12459545) B12459545
theorem B966377 : Blo 603293 966377 := bstep (se 2 (by rfl) ⟨362391, by rfl⟩ : syracuseStep 966377 = 724783) B724783
theorem B1359593 : Blo 603293 1359593 := bstep (se 2 (by rfl) ⟨509847, by rfl⟩ : syracuseStep 1359593 = 1019695) B1019695
theorem B606023 : Blo 603293 606023 := bstep (se 1 (by rfl) ⟨454517, by rfl⟩ : syracuseStep 606023 = 909035) B909035
theorem B606175 : Blo 603293 606175 := bstep (se 1 (by rfl) ⟨454631, by rfl⟩ : syracuseStep 606175 = 909263) B909263
theorem B2048219 : Blo 603293 2048219 := bstep (se 1 (by rfl) ⟨1536164, by rfl⟩ : syracuseStep 2048219 = 3072329) B3072329
theorem B606439 : Blo 603293 606439 := bstep (se 1 (by rfl) ⟨454829, by rfl⟩ : syracuseStep 606439 = 909659) B909659
theorem B606591 : Blo 603293 606591 := bstep (se 1 (by rfl) ⟨454943, by rfl⟩ : syracuseStep 606591 = 909887) B909887
theorem B1720759 : Blo 603293 1720759 := bstep (se 1 (by rfl) ⟨1290569, by rfl⟩ : syracuseStep 1720759 = 2581139) B2581139
theorem B606671 : Blo 603293 606671 := bstep (se 1 (by rfl) ⟨455003, by rfl⟩ : syracuseStep 606671 = 910007) B910007
theorem B2048489 : Blo 603293 2048489 := bstep (se 2 (by rfl) ⟨768183, by rfl⟩ : syracuseStep 2048489 = 1536367) B1536367
theorem B606823 : Blo 603293 606823 := bstep (se 1 (by rfl) ⟨455117, by rfl⟩ : syracuseStep 606823 = 910235) B910235
theorem B1360619 : Blo 603293 1360619 := bstep (se 1 (by rfl) ⟨1020464, by rfl⟩ : syracuseStep 1360619 = 2040929) B2040929
theorem B607087 : Blo 603293 607087 := bstep (se 1 (by rfl) ⟨455315, by rfl⟩ : syracuseStep 607087 = 910631) B910631
theorem B607143 : Blo 603293 607143 := bstep (se 1 (by rfl) ⟨455357, by rfl⟩ : syracuseStep 607143 = 910715) B910715
theorem B607227 : Blo 603293 607227 := bstep (se 1 (by rfl) ⟨455420, by rfl⟩ : syracuseStep 607227 = 910841) B910841
theorem B8700965 : Blo 603293 8700965 := bstep (se 4 (by rfl) ⟨815715, by rfl⟩ : syracuseStep 8700965 = 1631431) B1631431
theorem B2049083 : Blo 603293 2049083 := bstep (se 1 (by rfl) ⟨1536812, by rfl⟩ : syracuseStep 2049083 = 3073625) B3073625
theorem B2049353 : Blo 603293 2049353 := bstep (se 2 (by rfl) ⟨768507, by rfl⟩ : syracuseStep 2049353 = 1537015) B1537015
theorem B968107 : Blo 603293 968107 := bstep (se 1 (by rfl) ⟨726080, by rfl⟩ : syracuseStep 968107 = 1452161) B1452161
theorem B3065363 : Blo 603293 3065363 := bstep (se 1 (by rfl) ⟨2299022, by rfl⟩ : syracuseStep 3065363 = 4598045) B4598045
theorem B1361519 : Blo 603293 1361519 := bstep (se 1 (by rfl) ⟨1021139, by rfl⟩ : syracuseStep 1361519 = 2042279) B2042279
theorem B3884705 : Blo 603293 3884705 := bstep (se 2 (by rfl) ⟨1456764, by rfl⟩ : syracuseStep 3884705 = 2913529) B2913529
theorem B1361627 : Blo 603293 1361627 := bstep (se 1 (by rfl) ⟨1021220, by rfl⟩ : syracuseStep 1361627 = 2042441) B2042441
theorem B1034047 : Blo 603293 1034047 := bstep (se 1 (by rfl) ⟨775535, by rfl⟩ : syracuseStep 1034047 = 1551071) B1551071
theorem B1722377 : Blo 603293 1722377 := bstep (se 2 (by rfl) ⟨645891, by rfl⟩ : syracuseStep 1722377 = 1291783) B1291783
theorem B3885191 : Blo 603293 3885191 := bstep (se 1 (by rfl) ⟨2913893, by rfl⟩ : syracuseStep 3885191 = 5827787) B5827787
theorem B1722559 : Blo 603293 1722559 := bstep (se 1 (by rfl) ⟨1291919, by rfl⟩ : syracuseStep 1722559 = 2583839) B2583839
theorem B19646711 : Blo 603293 19646711 := bstep (se 1 (by rfl) ⟨14735033, by rfl⟩ : syracuseStep 19646711 = 29470067) B29470067
theorem B1722617 : Blo 603293 1722617 := bstep (se 2 (by rfl) ⟨645981, by rfl⟩ : syracuseStep 1722617 = 1291963) B1291963
theorem B1362743 : Blo 603293 1362743 := bstep (se 1 (by rfl) ⟨1022057, by rfl⟩ : syracuseStep 1362743 = 2044115) B2044115
theorem B1362923 : Blo 603293 1362923 := bstep (se 1 (by rfl) ⟨1022192, by rfl⟩ : syracuseStep 1362923 = 2044385) B2044385
theorem B6540907 : Blo 603293 6540907 := bstep (se 1 (by rfl) ⟨4905680, by rfl⟩ : syracuseStep 6540907 = 9811361) B9811361
theorem B1363751 : Blo 603293 1363751 := bstep (se 1 (by rfl) ⟨1022813, by rfl⟩ : syracuseStep 1363751 = 2045627) B2045627
theorem B905081 : Blo 603293 905081 := bstep (se 2 (by rfl) ⟨339405, by rfl⟩ : syracuseStep 905081 = 678811) B678811
theorem B905183 : Blo 603293 905183 := bstep (se 1 (by rfl) ⟨678887, by rfl⟩ : syracuseStep 905183 = 1357775) B1357775
theorem B13127741 : Blo 603293 13127741 := bstep (se 3 (by rfl) ⟨2461451, by rfl⟩ : syracuseStep 13127741 = 4922903) B4922903
theorem B3887291 : Blo 603293 3887291 := bstep (se 1 (by rfl) ⟨2915468, by rfl⟩ : syracuseStep 3887291 = 5830937) B5830937
theorem B905435 : Blo 603293 905435 := bstep (se 1 (by rfl) ⟨679076, by rfl⟩ : syracuseStep 905435 = 1358153) B1358153
theorem B905447 : Blo 603293 905447 := bstep (se 1 (by rfl) ⟨679085, by rfl⟩ : syracuseStep 905447 = 1358171) B1358171
theorem B905609 : Blo 603293 905609 := bstep (se 2 (by rfl) ⟨339603, by rfl⟩ : syracuseStep 905609 = 679207) B679207
theorem B905705 : Blo 603293 905705 := bstep (se 2 (by rfl) ⟨339639, by rfl⟩ : syracuseStep 905705 = 679279) B679279
theorem B3494387 : Blo 603293 3494387 := bstep (se 1 (by rfl) ⟨2620790, by rfl⟩ : syracuseStep 3494387 = 5241581) B5241581
theorem B905831 : Blo 603293 905831 := bstep (se 1 (by rfl) ⟨679373, by rfl⟩ : syracuseStep 905831 = 1358747) B1358747
theorem B6541985 : Blo 603293 6541985 := bstep (se 2 (by rfl) ⟨2453244, by rfl⟩ : syracuseStep 6541985 = 4906489) B4906489
theorem B905963 : Blo 603293 905963 := bstep (se 1 (by rfl) ⟨679472, by rfl⟩ : syracuseStep 905963 = 1358945) B1358945
theorem B905993 : Blo 603293 905993 := bstep (se 2 (by rfl) ⟨339747, by rfl⟩ : syracuseStep 905993 = 679495) B679495
theorem B1364777 : Blo 603293 1364777 := bstep (se 2 (by rfl) ⟨511791, by rfl⟩ : syracuseStep 1364777 = 1023583) B1023583
theorem B906095 : Blo 603293 906095 := bstep (se 1 (by rfl) ⟨679571, by rfl⟩ : syracuseStep 906095 = 1359143) B1359143
theorem B1365047 : Blo 603293 1365047 := bstep (se 1 (by rfl) ⟨1023785, by rfl⟩ : syracuseStep 1365047 = 2047571) B2047571
theorem B1528895 : Blo 603293 1528895 := bstep (se 1 (by rfl) ⟨1146671, by rfl⟩ : syracuseStep 1528895 = 2293343) B2293343
theorem B1365065 : Blo 603293 1365065 := bstep (se 2 (by rfl) ⟨511899, by rfl⟩ : syracuseStep 1365065 = 1023799) B1023799
theorem B906347 : Blo 603293 906347 := bstep (se 1 (by rfl) ⟨679760, by rfl⟩ : syracuseStep 906347 = 1359521) B1359521
theorem B906587 : Blo 603293 906587 := bstep (se 1 (by rfl) ⟨679940, by rfl⟩ : syracuseStep 906587 = 1359881) B1359881
theorem B15947297 : Blo 603293 15947297 := bstep (se 2 (by rfl) ⟨5980236, by rfl⟩ : syracuseStep 15947297 = 11960473) B11960473
theorem B906863 : Blo 603293 906863 := bstep (se 1 (by rfl) ⟨680147, by rfl⟩ : syracuseStep 906863 = 1360295) B1360295
theorem B906935 : Blo 603293 906935 := bstep (se 1 (by rfl) ⟨680201, by rfl⟩ : syracuseStep 906935 = 1360403) B1360403
theorem B906971 : Blo 603293 906971 := bstep (se 1 (by rfl) ⟨680228, by rfl⟩ : syracuseStep 906971 = 1360457) B1360457
theorem B907145 : Blo 603293 907145 := bstep (se 2 (by rfl) ⟨340179, by rfl⟩ : syracuseStep 907145 = 680359) B680359
theorem B8312807 : Blo 603293 8312807 := bstep (se 1 (by rfl) ⟨6234605, by rfl⟩ : syracuseStep 8312807 = 12469211) B12469211
theorem B907247 : Blo 603293 907247 := bstep (se 1 (by rfl) ⟨680435, by rfl⟩ : syracuseStep 907247 = 1360871) B1360871
theorem B1103863 : Blo 603293 1103863 := bstep (se 1 (by rfl) ⟨827897, by rfl⟩ : syracuseStep 1103863 = 1655795) B1655795
theorem B1529999 : Blo 603293 1529999 := bstep (se 1 (by rfl) ⟨1147499, by rfl⟩ : syracuseStep 1529999 = 2294999) B2294999
theorem B874729 : Blo 603293 874729 := bstep (se 2 (by rfl) ⟨328023, by rfl⟩ : syracuseStep 874729 = 656047) B656047
theorem B907499 : Blo 603293 907499 := bstep (se 1 (by rfl) ⟨680624, by rfl⟩ : syracuseStep 907499 = 1361249) B1361249
theorem B907559 : Blo 603293 907559 := bstep (se 1 (by rfl) ⟨680669, by rfl⟩ : syracuseStep 907559 = 1361339) B1361339
theorem B4905323 : Blo 603293 4905323 := bstep (se 1 (by rfl) ⟨3678992, by rfl⟩ : syracuseStep 4905323 = 7357985) B7357985
theorem B907643 : Blo 603293 907643 := bstep (se 1 (by rfl) ⟨680732, by rfl⟩ : syracuseStep 907643 = 1361465) B1361465
theorem B4610681 : Blo 603293 4610681 := bstep (se 2 (by rfl) ⟨1729005, by rfl⟩ : syracuseStep 4610681 = 3458011) B3458011
theorem B907913 : Blo 603293 907913 := bstep (se 2 (by rfl) ⟨340467, by rfl⟩ : syracuseStep 907913 = 680935) B680935
theorem B4348637 : Blo 603293 4348637 := bstep (se 3 (by rfl) ⟨815369, by rfl⟩ : syracuseStep 4348637 = 1630739) B1630739
theorem B908087 : Blo 603293 908087 := bstep (se 1 (by rfl) ⟨681065, by rfl⟩ : syracuseStep 908087 = 1362131) B1362131
theorem B908123 : Blo 603293 908123 := bstep (se 1 (by rfl) ⟨681092, by rfl⟩ : syracuseStep 908123 = 1362185) B1362185
theorem B908267 : Blo 603293 908267 := bstep (se 1 (by rfl) ⟨681200, by rfl⟩ : syracuseStep 908267 = 1362401) B1362401
theorem B3071033 : Blo 603293 3071033 := bstep (se 2 (by rfl) ⟨1151637, by rfl⟩ : syracuseStep 3071033 = 2303275) B2303275
theorem B908471 : Blo 603293 908471 := bstep (se 1 (by rfl) ⟨681353, by rfl⟩ : syracuseStep 908471 = 1362707) B1362707
theorem B679135 : Blo 603293 679135 := bstep (se 1 (by rfl) ⟨509351, by rfl⟩ : syracuseStep 679135 = 1018703) B1018703
theorem B908711 : Blo 603293 908711 := bstep (se 1 (by rfl) ⟨681533, by rfl⟩ : syracuseStep 908711 = 1363067) B1363067
theorem B908795 : Blo 603293 908795 := bstep (se 1 (by rfl) ⟨681596, by rfl⟩ : syracuseStep 908795 = 1363193) B1363193
theorem B908891 : Blo 603293 908891 := bstep (se 1 (by rfl) ⟨681668, by rfl⟩ : syracuseStep 908891 = 1363337) B1363337
theorem B908975 : Blo 603293 908975 := bstep (se 1 (by rfl) ⟨681731, by rfl⟩ : syracuseStep 908975 = 1363463) B1363463
theorem B909095 : Blo 603293 909095 := bstep (se 1 (by rfl) ⟨681821, by rfl⟩ : syracuseStep 909095 = 1363643) B1363643
theorem B909179 : Blo 603293 909179 := bstep (se 1 (by rfl) ⟨681884, by rfl⟩ : syracuseStep 909179 = 1363769) B1363769
theorem B1531943 : Blo 603293 1531943 := bstep (se 1 (by rfl) ⟨1148957, by rfl⟩ : syracuseStep 1531943 = 2297915) B2297915
theorem B6545447 : Blo 603293 6545447 := bstep (se 1 (by rfl) ⟨4909085, by rfl⟩ : syracuseStep 6545447 = 9818171) B9818171
theorem B1532135 : Blo 603293 1532135 := bstep (se 1 (by rfl) ⟨1149101, by rfl⟩ : syracuseStep 1532135 = 2298203) B2298203
theorem B909599 : Blo 603293 909599 := bstep (se 1 (by rfl) ⟨682199, by rfl⟩ : syracuseStep 909599 = 1364399) B1364399
theorem B909623 : Blo 603293 909623 := bstep (se 1 (by rfl) ⟨682217, by rfl⟩ : syracuseStep 909623 = 1364435) B1364435
theorem B909695 : Blo 603293 909695 := bstep (se 1 (by rfl) ⟨682271, by rfl⟩ : syracuseStep 909695 = 1364543) B1364543
theorem B909767 : Blo 603293 909767 := bstep (se 1 (by rfl) ⟨682325, by rfl⟩ : syracuseStep 909767 = 1364651) B1364651
theorem B1729097 : Blo 603293 1729097 := bstep (se 2 (by rfl) ⟨648411, by rfl⟩ : syracuseStep 1729097 = 1296823) B1296823
theorem B3105533 : Blo 603293 3105533 := bstep (se 3 (by rfl) ⟨582287, by rfl⟩ : syracuseStep 3105533 = 1164575) B1164575
theorem B2188043 : Blo 603293 2188043 := bstep (se 1 (by rfl) ⟨1641032, by rfl⟩ : syracuseStep 2188043 = 3282065) B3282065
theorem B910121 : Blo 603293 910121 := bstep (se 2 (by rfl) ⟨341295, by rfl⟩ : syracuseStep 910121 = 682591) B682591
theorem B910127 : Blo 603293 910127 := bstep (se 1 (by rfl) ⟨682595, by rfl⟩ : syracuseStep 910127 = 1365191) B1365191
theorem B1532783 : Blo 603293 1532783 := bstep (se 1 (by rfl) ⟨1149587, by rfl⟩ : syracuseStep 1532783 = 2299175) B2299175
theorem B910247 : Blo 603293 910247 := bstep (se 1 (by rfl) ⟨682685, by rfl⟩ : syracuseStep 910247 = 1365371) B1365371
theorem B910331 : Blo 603293 910331 := bstep (se 1 (by rfl) ⟨682748, by rfl⟩ : syracuseStep 910331 = 1365497) B1365497
theorem B910391 : Blo 603293 910391 := bstep (se 1 (by rfl) ⟨682793, by rfl⟩ : syracuseStep 910391 = 1365587) B1365587
theorem B910511 : Blo 603293 910511 := bstep (se 1 (by rfl) ⟨682883, by rfl⟩ : syracuseStep 910511 = 1365767) B1365767
theorem B910919 : Blo 603293 910919 := bstep (se 1 (by rfl) ⟨683189, by rfl⟩ : syracuseStep 910919 = 1366379) B1366379
theorem B681583 : Blo 603293 681583 := bstep (se 1 (by rfl) ⟨511187, by rfl⟩ : syracuseStep 681583 = 1022375) B1022375
theorem B681691 : Blo 603293 681691 := bstep (se 1 (by rfl) ⟨511268, by rfl⟩ : syracuseStep 681691 = 1022537) B1022537
theorem B1533775 : Blo 603293 1533775 := bstep (se 1 (by rfl) ⟨1150331, by rfl⟩ : syracuseStep 1533775 = 2300663) B2300663
theorem B4581521 : Blo 603293 4581521 := bstep (se 2 (by rfl) ⟨1718070, by rfl⟩ : syracuseStep 4581521 = 3436141) B3436141
theorem B14772401 : Blo 603293 14772401 := bstep (se 2 (by rfl) ⟨5539650, by rfl⟩ : syracuseStep 14772401 = 11079301) B11079301
theorem B5827247 : Blo 603293 5827247 := bstep (se 1 (by rfl) ⟨4370435, by rfl⟩ : syracuseStep 5827247 = 8740871) B8740871
theorem B682843 : Blo 603293 682843 := bstep (se 1 (by rfl) ⟨512132, by rfl⟩ : syracuseStep 682843 = 1024265) B1024265
theorem B2583515 : Blo 603293 2583515 := bstep (se 1 (by rfl) ⟨1937636, by rfl⟩ : syracuseStep 2583515 = 3875273) B3875273
theorem B15756743 : Blo 603293 15756743 := bstep (se 1 (by rfl) ⟨11817557, by rfl⟩ : syracuseStep 15756743 = 23635115) B23635115
theorem B22146929 : Blo 603293 22146929 := bstep (se 2 (by rfl) ⟨8305098, by rfl⟩ : syracuseStep 22146929 = 16610197) B16610197
theorem B3436667 : Blo 603293 3436667 := bstep (se 1 (by rfl) ⟨2577500, by rfl⟩ : syracuseStep 3436667 = 5155001) B5155001
theorem B25555301 : Blo 603293 25555301 := bstep (se 4 (by rfl) ⟨2395809, by rfl⟩ : syracuseStep 25555301 = 4791619) B4791619
theorem B4583951 : Blo 603293 4583951 := bstep (se 1 (by rfl) ⟨3437963, by rfl⟩ : syracuseStep 4583951 = 6875927) B6875927
theorem B2585171 : Blo 603293 2585171 := bstep (se 1 (by rfl) ⟨1938878, by rfl⟩ : syracuseStep 2585171 = 3877757) B3877757
theorem B816191 : Blo 603293 816191 := bstep (se 1 (by rfl) ⟨612143, by rfl⟩ : syracuseStep 816191 = 1224287) B1224287
theorem B8615159 : Blo 603293 8615159 := bstep (se 1 (by rfl) ⟨6461369, by rfl⟩ : syracuseStep 8615159 = 12922739) B12922739
theorem B15725987 : Blo 603293 15725987 := bstep (se 1 (by rfl) ⟨11794490, by rfl⟩ : syracuseStep 15725987 = 23588981) B23588981
theorem B2586113 : Blo 603293 2586113 := bstep (se 2 (by rfl) ⟨969792, by rfl⟩ : syracuseStep 2586113 = 1939585) B1939585
theorem B9926345 : Blo 603293 9926345 := bstep (se 2 (by rfl) ⟨3722379, by rfl⟩ : syracuseStep 9926345 = 7444759) B7444759
theorem B4356595 : Blo 603293 4356595 := bstep (se 1 (by rfl) ⟨3267446, by rfl⟩ : syracuseStep 4356595 = 6534893) B6534893
theorem B8059499 : Blo 603293 8059499 := bstep (se 1 (by rfl) ⟨6044624, by rfl⟩ : syracuseStep 8059499 = 12089249) B12089249
theorem B1145897 : Blo 603293 1145897 := bstep (se 2 (by rfl) ⟨429711, by rfl⟩ : syracuseStep 1145897 = 859423) B859423
theorem B1145927 : Blo 603293 1145927 := bstep (se 1 (by rfl) ⟨859445, by rfl⟩ : syracuseStep 1145927 = 1718891) B1718891
theorem B4914599 : Blo 603293 4914599 := bstep (se 1 (by rfl) ⟨3685949, by rfl⟩ : syracuseStep 4914599 = 7371899) B7371899
theorem B2915777 : Blo 603293 2915777 := bstep (se 2 (by rfl) ⟨1093416, by rfl⟩ : syracuseStep 2915777 = 2186833) B2186833
theorem B1048391 : Blo 603293 1048391 := bstep (se 1 (by rfl) ⟨786293, by rfl⟩ : syracuseStep 1048391 = 1572587) B1572587
theorem B2294345 : Blo 603293 2294345 := bstep (se 2 (by rfl) ⟨860379, by rfl⟩ : syracuseStep 2294345 = 1720759) B1720759
theorem B5800643 : Blo 603293 5800643 := bstep (se 1 (by rfl) ⟨4350482, by rfl⟩ : syracuseStep 5800643 = 8700965) B8700965
theorem B2589803 : Blo 603293 2589803 := bstep (se 1 (by rfl) ⟨1942352, by rfl⟩ : syracuseStep 2589803 = 3884705) B3884705
theorem B4588811 : Blo 603293 4588811 := bstep (se 1 (by rfl) ⟨3441608, by rfl⟩ : syracuseStep 4588811 = 6883217) B6883217
theorem B1639727 : Blo 603293 1639727 := bstep (se 1 (by rfl) ⟨1229795, by rfl⟩ : syracuseStep 1639727 = 2459591) B2459591
theorem B1148251 : Blo 603293 1148251 := bstep (se 1 (by rfl) ⟨861188, by rfl⟩ : syracuseStep 1148251 = 1722377) B1722377
theorem B2590127 : Blo 603293 2590127 := bstep (se 1 (by rfl) ⟨1942595, by rfl⟩ : syracuseStep 2590127 = 3885191) B3885191
theorem B1148411 : Blo 603293 1148411 := bstep (se 1 (by rfl) ⟨861308, by rfl⟩ : syracuseStep 1148411 = 1722617) B1722617
theorem B2492441 : Blo 603293 2492441 := bstep (se 2 (by rfl) ⟨934665, by rfl⟩ : syracuseStep 2492441 = 1869331) B1869331
theorem B4589783 : Blo 603293 4589783 := bstep (se 1 (by rfl) ⟨3442337, by rfl⟩ : syracuseStep 4589783 = 6884675) B6884675
theorem B1378729 : Blo 603293 1378729 := bstep (se 2 (by rfl) ⟨517023, by rfl⟩ : syracuseStep 1378729 = 1034047) B1034047
theorem B8751827 : Blo 603293 8751827 := bstep (se 1 (by rfl) ⟨6563870, by rfl⟩ : syracuseStep 8751827 = 13127741) B13127741
theorem B2591527 : Blo 603293 2591527 := bstep (se 1 (by rfl) ⟨1943645, by rfl⟩ : syracuseStep 2591527 = 3887291) B3887291
theorem B2296745 : Blo 603293 2296745 := bstep (se 2 (by rfl) ⟨861279, by rfl⟩ : syracuseStep 2296745 = 1722559) B1722559
theorem B2329591 : Blo 603293 2329591 := bstep (se 1 (by rfl) ⟨1747193, by rfl⟩ : syracuseStep 2329591 = 3494387) B3494387
theorem B4361323 : Blo 603293 4361323 := bstep (se 1 (by rfl) ⟨3270992, by rfl⟩ : syracuseStep 4361323 = 6541985) B6541985
theorem B2296957 : Blo 603293 2296957 := bstep (se 3 (by rfl) ⟨430679, by rfl⟩ : syracuseStep 2296957 = 861359) B861359
theorem B4590755 : Blo 603293 4590755 := bstep (se 1 (by rfl) ⟨3443066, by rfl⟩ : syracuseStep 4590755 = 6886133) B6886133
theorem B2624879 : Blo 603293 2624879 := bstep (se 1 (by rfl) ⟨1968659, by rfl⟩ : syracuseStep 2624879 = 3937319) B3937319
theorem B1019263 : Blo 603293 1019263 := bstep (se 1 (by rfl) ⟨764447, by rfl⟩ : syracuseStep 1019263 = 1528895) B1528895
theorem B5541871 : Blo 603293 5541871 := bstep (se 1 (by rfl) ⟨4156403, by rfl⟩ : syracuseStep 5541871 = 8312807) B8312807
theorem B1019999 : Blo 603293 1019999 := bstep (se 1 (by rfl) ⟨764999, by rfl⟩ : syracuseStep 1019999 = 1529999) B1529999
theorem B1839401 : Blo 603293 1839401 := bstep (se 2 (by rfl) ⟨689775, by rfl⟩ : syracuseStep 1839401 = 1379551) B1379551
theorem B1151273 : Blo 603293 1151273 := bstep (se 2 (by rfl) ⟨431727, by rfl⟩ : syracuseStep 1151273 = 863455) B863455
theorem B6557993 : Blo 603293 6557993 := bstep (se 2 (by rfl) ⟨2459247, by rfl⟩ : syracuseStep 6557993 = 4918495) B4918495
theorem B5509549 : Blo 603293 5509549 := bstep (se 3 (by rfl) ⟨1033040, by rfl⟩ : syracuseStep 5509549 = 2066081) B2066081
theorem B8721209 : Blo 603293 8721209 := bstep (se 2 (by rfl) ⟨3270453, by rfl⟩ : syracuseStep 8721209 = 6540907) B6540907
theorem B3871583 : Blo 603293 3871583 := bstep (se 1 (by rfl) ⟨2903687, by rfl⟩ : syracuseStep 3871583 = 5807375) B5807375
theorem B1021295 : Blo 603293 1021295 := bstep (se 1 (by rfl) ⟨765971, by rfl⟩ : syracuseStep 1021295 = 1531943) B1531943
theorem B4363631 : Blo 603293 4363631 := bstep (se 1 (by rfl) ⟨3272723, by rfl⟩ : syracuseStep 4363631 = 6545447) B6545447
theorem B1021423 : Blo 603293 1021423 := bstep (se 1 (by rfl) ⟨766067, by rfl⟩ : syracuseStep 1021423 = 1532135) B1532135
theorem B4593185 : Blo 603293 4593185 := bstep (se 2 (by rfl) ⟨1722444, by rfl⟩ : syracuseStep 4593185 = 3444889) B3444889
theorem B1152731 : Blo 603293 1152731 := bstep (se 1 (by rfl) ⟨864548, by rfl⟩ : syracuseStep 1152731 = 1729097) B1729097
theorem B2070355 : Blo 603293 2070355 := bstep (se 1 (by rfl) ⟨1552766, by rfl⟩ : syracuseStep 2070355 = 3105533) B3105533
theorem B1021855 : Blo 603293 1021855 := bstep (se 1 (by rfl) ⟨766391, by rfl⟩ : syracuseStep 1021855 = 1532783) B1532783
theorem B2955323 : Blo 603293 2955323 := bstep (se 1 (by rfl) ⟨2216492, by rfl⟩ : syracuseStep 2955323 = 4432985) B4432985
theorem B3054347 : Blo 603293 3054347 := bstep (se 1 (by rfl) ⟨2290760, by rfl⟩ : syracuseStep 3054347 = 4581521) B4581521
theorem B7347773 : Blo 603293 7347773 := bstep (se 3 (by rfl) ⟨1377707, by rfl⟩ : syracuseStep 7347773 = 2755415) B2755415
theorem B1384103 : Blo 603293 1384103 := bstep (se 1 (by rfl) ⟨1038077, by rfl⟩ : syracuseStep 1384103 = 2076155) B2076155
theorem B860015 : Blo 603293 860015 := bstep (se 1 (by rfl) ⟨645011, by rfl⟩ : syracuseStep 860015 = 1290023) B1290023
theorem B2302091 : Blo 603293 2302091 := bstep (se 1 (by rfl) ⟨1726568, by rfl⟩ : syracuseStep 2302091 = 3453137) B3453137
theorem B3055805 : Blo 603293 3055805 := bstep (se 3 (by rfl) ⟨572963, by rfl⟩ : syracuseStep 3055805 = 1145927) B1145927
theorem B2040119 : Blo 603293 2040119 := bstep (se 1 (by rfl) ⟨1530089, by rfl⟩ : syracuseStep 2040119 = 3060179) B3060179
theorem B3055967 : Blo 603293 3055967 := bstep (se 1 (by rfl) ⟨2291975, by rfl⟩ : syracuseStep 3055967 = 4583951) B4583951
theorem B2302303 : Blo 603293 2302303 := bstep (se 1 (by rfl) ⟨1726727, by rfl⟩ : syracuseStep 2302303 = 3453455) B3453455
theorem B5808793 : Blo 603293 5808793 := bstep (se 2 (by rfl) ⟨2178297, by rfl⟩ : syracuseStep 5808793 = 4356595) B4356595
theorem B5743439 : Blo 603293 5743439 := bstep (se 1 (by rfl) ⟨4307579, by rfl⟩ : syracuseStep 5743439 = 8615159) B8615159
theorem B763931 : Blo 603293 763931 := bstep (se 1 (by rfl) ⟨572948, by rfl⟩ : syracuseStep 763931 = 1145897) B1145897
theorem B20949137 : Blo 603293 20949137 := bstep (se 2 (by rfl) ⟨7855926, by rfl⟩ : syracuseStep 20949137 = 15711853) B15711853
theorem B1943851 : Blo 603293 1943851 := bstep (se 1 (by rfl) ⟨1457888, by rfl⟩ : syracuseStep 1943851 = 2915777) B2915777
theorem B698927 : Blo 603293 698927 := bstep (se 1 (by rfl) ⟨524195, by rfl⟩ : syracuseStep 698927 = 1048391) B1048391
theorem B15510203 : Blo 603293 15510203 := bstep (se 1 (by rfl) ⟨11632652, by rfl⟩ : syracuseStep 15510203 = 23265305) B23265305
theorem B3058721 : Blo 603293 3058721 := bstep (se 2 (by rfl) ⟨1147020, by rfl⟩ : syracuseStep 3058721 = 2294041) B2294041
theorem B3452179 : Blo 603293 3452179 := bstep (se 1 (by rfl) ⟨2589134, by rfl⟩ : syracuseStep 3452179 = 5178269) B5178269
theorem B2043575 : Blo 603293 2043575 := bstep (se 1 (by rfl) ⟨1532681, by rfl⟩ : syracuseStep 2043575 = 3065363) B3065363
theorem B4665221 : Blo 603293 4665221 := bstep (se 4 (by rfl) ⟨437364, by rfl⟩ : syracuseStep 4665221 = 874729) B874729
theorem B100642823 : Blo 603293 100642823 := bstep (se 1 (by rfl) ⟨75482117, by rfl⟩ : syracuseStep 100642823 = 150964235) B150964235
theorem B1290323 : Blo 603293 1290323 := bstep (se 1 (by rfl) ⟨967742, by rfl⟩ : syracuseStep 1290323 = 1935485) B1935485
theorem B1093907 : Blo 603293 1093907 := bstep (se 1 (by rfl) ⟨820430, by rfl⟩ : syracuseStep 1093907 = 1640861) B1640861
theorem B8532361 : Blo 603293 8532361 := bstep (se 2 (by rfl) ⟨3199635, by rfl⟩ : syracuseStep 8532361 = 6399271) B6399271
theorem B1290809 : Blo 603293 1290809 := bstep (se 2 (by rfl) ⟨484053, by rfl⟩ : syracuseStep 1290809 = 968107) B968107
theorem B2045033 : Blo 603293 2045033 := bstep (se 2 (by rfl) ⟨766887, by rfl⟩ : syracuseStep 2045033 = 1533775) B1533775
theorem B4600961 : Blo 603293 4600961 := bstep (se 2 (by rfl) ⟨1725360, by rfl⟩ : syracuseStep 4600961 = 3450721) B3450721
theorem B4371677 : Blo 603293 4371677 := bstep (se 3 (by rfl) ⟨819689, by rfl⟩ : syracuseStep 4371677 = 1639379) B1639379
theorem B603387 : Blo 603293 603387 := bstep (se 1 (by rfl) ⟨452540, by rfl⟩ : syracuseStep 603387 = 905081) B905081
theorem B767227 : Blo 603293 767227 := bstep (se 1 (by rfl) ⟨575420, by rfl⟩ : syracuseStep 767227 = 1150841) B1150841
theorem B603455 : Blo 603293 603455 := bstep (se 1 (by rfl) ⟨452591, by rfl⟩ : syracuseStep 603455 = 905183) B905183
theorem B603623 : Blo 603293 603623 := bstep (se 1 (by rfl) ⟨452717, by rfl⟩ : syracuseStep 603623 = 905435) B905435
theorem B603631 : Blo 603293 603631 := bstep (se 1 (by rfl) ⟨452723, by rfl⟩ : syracuseStep 603631 = 905447) B905447
theorem B603739 : Blo 603293 603739 := bstep (se 1 (by rfl) ⟨452804, by rfl⟩ : syracuseStep 603739 = 905609) B905609
theorem B603803 : Blo 603293 603803 := bstep (se 1 (by rfl) ⟨452852, by rfl⟩ : syracuseStep 603803 = 905705) B905705
theorem B603887 : Blo 603293 603887 := bstep (se 1 (by rfl) ⟨452915, by rfl⟩ : syracuseStep 603887 = 905831) B905831
theorem B1357559 : Blo 603293 1357559 := bstep (se 1 (by rfl) ⟨1018169, by rfl⟩ : syracuseStep 1357559 = 2036339) B2036339
theorem B603975 : Blo 603293 603975 := bstep (se 1 (by rfl) ⟨452981, by rfl⟩ : syracuseStep 603975 = 905963) B905963
theorem B603995 : Blo 603293 603995 := bstep (se 1 (by rfl) ⟨452996, by rfl⟩ : syracuseStep 603995 = 905993) B905993
theorem B12433277 : Blo 603293 12433277 := bstep (se 3 (by rfl) ⟨2331239, by rfl⟩ : syracuseStep 12433277 = 4662479) B4662479
theorem B604063 : Blo 603293 604063 := bstep (se 1 (by rfl) ⟨453047, by rfl⟩ : syracuseStep 604063 = 906095) B906095
theorem B1357739 : Blo 603293 1357739 := bstep (se 1 (by rfl) ⟨1018304, by rfl⟩ : syracuseStep 1357739 = 2036609) B2036609
theorem B1357865 : Blo 603293 1357865 := bstep (se 2 (by rfl) ⟨509199, by rfl⟩ : syracuseStep 1357865 = 1018399) B1018399
theorem B604231 : Blo 603293 604231 := bstep (se 1 (by rfl) ⟨453173, by rfl⟩ : syracuseStep 604231 = 906347) B906347
theorem B604391 : Blo 603293 604391 := bstep (se 1 (by rfl) ⟨453293, by rfl⟩ : syracuseStep 604391 = 906587) B906587
theorem B10631531 : Blo 603293 10631531 := bstep (se 1 (by rfl) ⟨7973648, by rfl⟩ : syracuseStep 10631531 = 15947297) B15947297
theorem B604575 : Blo 603293 604575 := bstep (se 1 (by rfl) ⟨453431, by rfl⟩ : syracuseStep 604575 = 906863) B906863
theorem B1358279 : Blo 603293 1358279 := bstep (se 1 (by rfl) ⟨1018709, by rfl⟩ : syracuseStep 1358279 = 2037419) B2037419
theorem B604623 : Blo 603293 604623 := bstep (se 1 (by rfl) ⟨453467, by rfl⟩ : syracuseStep 604623 = 906935) B906935
theorem B604647 : Blo 603293 604647 := bstep (se 1 (by rfl) ⟨453485, by rfl⟩ : syracuseStep 604647 = 906971) B906971
theorem B604763 : Blo 603293 604763 := bstep (se 1 (by rfl) ⟨453572, by rfl⟩ : syracuseStep 604763 = 907145) B907145
theorem B1358441 : Blo 603293 1358441 := bstep (se 2 (by rfl) ⟨509415, by rfl⟩ : syracuseStep 1358441 = 1018831) B1018831
theorem B1358495 : Blo 603293 1358495 := bstep (se 1 (by rfl) ⟨1018871, by rfl⟩ : syracuseStep 1358495 = 2037743) B2037743
theorem B604831 : Blo 603293 604831 := bstep (se 1 (by rfl) ⟨453623, by rfl⟩ : syracuseStep 604831 = 907247) B907247
theorem B1358639 : Blo 603293 1358639 := bstep (se 1 (by rfl) ⟨1018979, by rfl⟩ : syracuseStep 1358639 = 2037959) B2037959
theorem B604999 : Blo 603293 604999 := bstep (se 1 (by rfl) ⟨453749, by rfl⟩ : syracuseStep 604999 = 907499) B907499
theorem B605039 : Blo 603293 605039 := bstep (se 1 (by rfl) ⟨453779, by rfl⟩ : syracuseStep 605039 = 907559) B907559
theorem B605095 : Blo 603293 605095 := bstep (se 1 (by rfl) ⟨453821, by rfl⟩ : syracuseStep 605095 = 907643) B907643
theorem B9288685 : Blo 603293 9288685 := bstep (se 3 (by rfl) ⟨1741628, by rfl⟩ : syracuseStep 9288685 = 3483257) B3483257
theorem B605275 : Blo 603293 605275 := bstep (se 1 (by rfl) ⟨453956, by rfl⟩ : syracuseStep 605275 = 907913) B907913
theorem B2899091 : Blo 603293 2899091 := bstep (se 1 (by rfl) ⟨2174318, by rfl⟩ : syracuseStep 2899091 = 4348637) B4348637
theorem B605391 : Blo 603293 605391 := bstep (se 1 (by rfl) ⟨454043, by rfl⟩ : syracuseStep 605391 = 908087) B908087
theorem B1359071 : Blo 603293 1359071 := bstep (se 1 (by rfl) ⟨1019303, by rfl⟩ : syracuseStep 1359071 = 2038607) B2038607
theorem B605415 : Blo 603293 605415 := bstep (se 1 (by rfl) ⟨454061, by rfl⟩ : syracuseStep 605415 = 908123) B908123
theorem B605511 : Blo 603293 605511 := bstep (se 1 (by rfl) ⟨454133, by rfl⟩ : syracuseStep 605511 = 908267) B908267
theorem B2047355 : Blo 603293 2047355 := bstep (se 1 (by rfl) ⟨1535516, by rfl⟩ : syracuseStep 2047355 = 3071033) B3071033
theorem B1359287 : Blo 603293 1359287 := bstep (se 1 (by rfl) ⟨1019465, by rfl⟩ : syracuseStep 1359287 = 2038931) B2038931
theorem B605647 : Blo 603293 605647 := bstep (se 1 (by rfl) ⟨454235, by rfl⟩ : syracuseStep 605647 = 908471) B908471
theorem B1359467 : Blo 603293 1359467 := bstep (se 1 (by rfl) ⟨1019600, by rfl⟩ : syracuseStep 1359467 = 2039201) B2039201
theorem B605807 : Blo 603293 605807 := bstep (se 1 (by rfl) ⟨454355, by rfl⟩ : syracuseStep 605807 = 908711) B908711
theorem B605863 : Blo 603293 605863 := bstep (se 1 (by rfl) ⟨454397, by rfl⟩ : syracuseStep 605863 = 908795) B908795
theorem B10370753 : Blo 603293 10370753 := bstep (se 2 (by rfl) ⟨3889032, by rfl⟩ : syracuseStep 10370753 = 7778065) B7778065
theorem B605927 : Blo 603293 605927 := bstep (se 1 (by rfl) ⟨454445, by rfl⟩ : syracuseStep 605927 = 908891) B908891
theorem B605983 : Blo 603293 605983 := bstep (se 1 (by rfl) ⟨454487, by rfl⟩ : syracuseStep 605983 = 908975) B908975
theorem B606063 : Blo 603293 606063 := bstep (se 1 (by rfl) ⟨454547, by rfl⟩ : syracuseStep 606063 = 909095) B909095
theorem B1359737 : Blo 603293 1359737 := bstep (se 2 (by rfl) ⟨509901, by rfl⟩ : syracuseStep 1359737 = 1019803) B1019803
theorem B606119 : Blo 603293 606119 := bstep (se 1 (by rfl) ⟨454589, by rfl⟩ : syracuseStep 606119 = 909179) B909179
theorem B2899901 : Blo 603293 2899901 := bstep (se 3 (by rfl) ⟨543731, by rfl⟩ : syracuseStep 2899901 = 1087463) B1087463
theorem B1359827 : Blo 603293 1359827 := bstep (se 1 (by rfl) ⟨1019870, by rfl⟩ : syracuseStep 1359827 = 2039741) B2039741
theorem B606399 : Blo 603293 606399 := bstep (se 1 (by rfl) ⟨454799, by rfl⟩ : syracuseStep 606399 = 909599) B909599
theorem B606415 : Blo 603293 606415 := bstep (se 1 (by rfl) ⟨454811, by rfl⟩ : syracuseStep 606415 = 909623) B909623
theorem B606463 : Blo 603293 606463 := bstep (se 1 (by rfl) ⟨454847, by rfl⟩ : syracuseStep 606463 = 909695) B909695
theorem B26460431 : Blo 603293 26460431 := bstep (se 1 (by rfl) ⟨19845323, by rfl⟩ : syracuseStep 26460431 = 39690647) B39690647
theorem B606511 : Blo 603293 606511 := bstep (se 1 (by rfl) ⟨454883, by rfl⟩ : syracuseStep 606511 = 909767) B909767
theorem B1458695 : Blo 603293 1458695 := bstep (se 1 (by rfl) ⟨1094021, by rfl⟩ : syracuseStep 1458695 = 2188043) B2188043
theorem B606747 : Blo 603293 606747 := bstep (se 1 (by rfl) ⟨455060, by rfl⟩ : syracuseStep 606747 = 910121) B910121
theorem B606751 : Blo 603293 606751 := bstep (se 1 (by rfl) ⟨455063, by rfl⟩ : syracuseStep 606751 = 910127) B910127
theorem B606831 : Blo 603293 606831 := bstep (se 1 (by rfl) ⟨455123, by rfl⟩ : syracuseStep 606831 = 910247) B910247
theorem B606887 : Blo 603293 606887 := bstep (se 1 (by rfl) ⟨455165, by rfl⟩ : syracuseStep 606887 = 910331) B910331
theorem B606927 : Blo 603293 606927 := bstep (se 1 (by rfl) ⟨455195, by rfl⟩ : syracuseStep 606927 = 910391) B910391
theorem B607007 : Blo 603293 607007 := bstep (se 1 (by rfl) ⟨455255, by rfl⟩ : syracuseStep 607007 = 910511) B910511
theorem B607279 : Blo 603293 607279 := bstep (se 1 (by rfl) ⟨455459, by rfl⟩ : syracuseStep 607279 = 910919) B910919
theorem B1361087 : Blo 603293 1361087 := bstep (se 1 (by rfl) ⟨1020815, by rfl⟩ : syracuseStep 1361087 = 2041631) B2041631
theorem B1361231 : Blo 603293 1361231 := bstep (se 1 (by rfl) ⟨1020923, by rfl⟩ : syracuseStep 1361231 = 2041847) B2041847
theorem B1361321 : Blo 603293 1361321 := bstep (se 2 (by rfl) ⟨510495, by rfl⟩ : syracuseStep 1361321 = 1020991) B1020991
theorem B9848267 : Blo 603293 9848267 := bstep (se 1 (by rfl) ⟨7386200, by rfl⟩ : syracuseStep 9848267 = 14772401) B14772401
theorem B3884831 : Blo 603293 3884831 := bstep (se 1 (by rfl) ⟨2913623, by rfl⟩ : syracuseStep 3884831 = 5827247) B5827247
theorem B1361807 : Blo 603293 1361807 := bstep (se 1 (by rfl) ⟨1021355, by rfl⟩ : syracuseStep 1361807 = 2042711) B2042711
theorem B1722343 : Blo 603293 1722343 := bstep (se 1 (by rfl) ⟨1291757, by rfl⟩ : syracuseStep 1722343 = 2583515) B2583515
theorem B968735 : Blo 603293 968735 := bstep (se 1 (by rfl) ⟨726551, by rfl⟩ : syracuseStep 968735 = 1453103) B1453103
theorem B1361951 : Blo 603293 1361951 := bstep (se 1 (by rfl) ⟨1021463, by rfl⟩ : syracuseStep 1361951 = 2042927) B2042927
theorem B1362203 : Blo 603293 1362203 := bstep (se 1 (by rfl) ⟨1021652, by rfl⟩ : syracuseStep 1362203 = 2043305) B2043305
theorem B10504495 : Blo 603293 10504495 := bstep (se 1 (by rfl) ⟨7878371, by rfl⟩ : syracuseStep 10504495 = 15756743) B15756743
theorem B14764619 : Blo 603293 14764619 := bstep (se 1 (by rfl) ⟨11073464, by rfl⟩ : syracuseStep 14764619 = 22146929) B22146929
theorem B1362527 : Blo 603293 1362527 := bstep (se 1 (by rfl) ⟨1021895, by rfl⟩ : syracuseStep 1362527 = 2043791) B2043791
theorem B1362779 : Blo 603293 1362779 := bstep (se 1 (by rfl) ⟨1022084, by rfl⟩ : syracuseStep 1362779 = 2044169) B2044169
theorem B1723265 : Blo 603293 1723265 := bstep (se 2 (by rfl) ⟨646224, by rfl⟩ : syracuseStep 1723265 = 1292449) B1292449
theorem B1723447 : Blo 603293 1723447 := bstep (se 1 (by rfl) ⟨1292585, by rfl⟩ : syracuseStep 1723447 = 2585171) B2585171
theorem B1363535 : Blo 603293 1363535 := bstep (se 1 (by rfl) ⟨1022651, by rfl⟩ : syracuseStep 1363535 = 2045303) B2045303
theorem B1724075 : Blo 603293 1724075 := bstep (se 1 (by rfl) ⟨1293056, by rfl⟩ : syracuseStep 1724075 = 2586113) B2586113
theorem B905087 : Blo 603293 905087 := bstep (se 1 (by rfl) ⟨678815, by rfl⟩ : syracuseStep 905087 = 1357631) B1357631
theorem B905279 : Blo 603293 905279 := bstep (se 1 (by rfl) ⟨678959, by rfl⟩ : syracuseStep 905279 = 1357919) B1357919
theorem B1364075 : Blo 603293 1364075 := bstep (se 1 (by rfl) ⟨1023056, by rfl⟩ : syracuseStep 1364075 = 2046113) B2046113
theorem B1364129 : Blo 603293 1364129 := bstep (se 2 (by rfl) ⟨511548, by rfl⟩ : syracuseStep 1364129 = 1023097) B1023097
theorem B1364255 : Blo 603293 1364255 := bstep (se 1 (by rfl) ⟨1023191, by rfl⟩ : syracuseStep 1364255 = 2046383) B2046383
theorem B905513 : Blo 603293 905513 := bstep (se 2 (by rfl) ⟨339567, by rfl⟩ : syracuseStep 905513 = 679135) B679135
theorem B971131 : Blo 603293 971131 := bstep (se 1 (by rfl) ⟨728348, by rfl⟩ : syracuseStep 971131 = 1456697) B1456697
theorem B2904457 : Blo 603293 2904457 := bstep (se 2 (by rfl) ⟨1089171, by rfl⟩ : syracuseStep 2904457 = 2178343) B2178343
theorem B1724905 : Blo 603293 1724905 := bstep (se 2 (by rfl) ⟨646839, by rfl⟩ : syracuseStep 1724905 = 1293679) B1293679
theorem B905783 : Blo 603293 905783 := bstep (se 1 (by rfl) ⟨679337, by rfl⟩ : syracuseStep 905783 = 1358675) B1358675
theorem B2577005 : Blo 603293 2577005 := bstep (se 3 (by rfl) ⟨483188, by rfl⟩ : syracuseStep 2577005 = 966377) B966377
theorem B906143 : Blo 603293 906143 := bstep (se 1 (by rfl) ⟨679607, by rfl⟩ : syracuseStep 906143 = 1359215) B1359215
theorem B1364975 : Blo 603293 1364975 := bstep (se 1 (by rfl) ⟨1023731, by rfl⟩ : syracuseStep 1364975 = 2047463) B2047463
theorem B906335 : Blo 603293 906335 := bstep (se 1 (by rfl) ⟨679751, by rfl⟩ : syracuseStep 906335 = 1359503) B1359503
theorem B906395 : Blo 603293 906395 := bstep (se 1 (by rfl) ⟨679796, by rfl⟩ : syracuseStep 906395 = 1359593) B1359593
theorem B1660267 : Blo 603293 1660267 := bstep (se 1 (by rfl) ⟨1245200, by rfl⟩ : syracuseStep 1660267 = 2490401) B2490401
theorem B1365479 : Blo 603293 1365479 := bstep (se 1 (by rfl) ⟨1024109, by rfl⟩ : syracuseStep 1365479 = 2048219) B2048219
theorem B1365641 : Blo 603293 1365641 := bstep (se 2 (by rfl) ⟨512115, by rfl⟩ : syracuseStep 1365641 = 1024231) B1024231
theorem B1365659 : Blo 603293 1365659 := bstep (se 1 (by rfl) ⟨1024244, by rfl⟩ : syracuseStep 1365659 = 2048489) B2048489
theorem B907079 : Blo 603293 907079 := bstep (se 1 (by rfl) ⟨680309, by rfl⟩ : syracuseStep 907079 = 1360619) B1360619
theorem B1365857 : Blo 603293 1365857 := bstep (se 2 (by rfl) ⟨512196, by rfl⟩ : syracuseStep 1365857 = 1024393) B1024393
theorem B8706037 : Blo 603293 8706037 := bstep (se 5 (by rfl) ⟨408095, by rfl⟩ : syracuseStep 8706037 = 816191) B816191
theorem B1366055 : Blo 603293 1366055 := bstep (se 1 (by rfl) ⟨1024541, by rfl⟩ : syracuseStep 1366055 = 2049083) B2049083
theorem B1366235 : Blo 603293 1366235 := bstep (se 1 (by rfl) ⟨1024676, by rfl⟩ : syracuseStep 1366235 = 2049353) B2049353
theorem B907679 : Blo 603293 907679 := bstep (se 1 (by rfl) ⟨680759, by rfl⟩ : syracuseStep 907679 = 1361519) B1361519
theorem B907751 : Blo 603293 907751 := bstep (se 1 (by rfl) ⟨680813, by rfl⟩ : syracuseStep 907751 = 1361627) B1361627
theorem B13097807 : Blo 603293 13097807 := bstep (se 1 (by rfl) ⟨9823355, by rfl⟩ : syracuseStep 13097807 = 19646711) B19646711
theorem B1530859 : Blo 603293 1530859 := bstep (se 1 (by rfl) ⟨1148144, by rfl⟩ : syracuseStep 1530859 = 2296289) B2296289
theorem B908495 : Blo 603293 908495 := bstep (se 1 (by rfl) ⟨681371, by rfl⟩ : syracuseStep 908495 = 1362743) B1362743
theorem B908615 : Blo 603293 908615 := bstep (se 1 (by rfl) ⟨681461, by rfl⟩ : syracuseStep 908615 = 1362923) B1362923
theorem B908777 : Blo 603293 908777 := bstep (se 2 (by rfl) ⟨340791, by rfl⟩ : syracuseStep 908777 = 681583) B681583
theorem B908921 : Blo 603293 908921 := bstep (se 2 (by rfl) ⟨340845, by rfl⟩ : syracuseStep 908921 = 681691) B681691
theorem B3890855 : Blo 603293 3890855 := bstep (se 1 (by rfl) ⟨2918141, by rfl⟩ : syracuseStep 3890855 = 5836283) B5836283
theorem B679711 : Blo 603293 679711 := bstep (se 1 (by rfl) ⟨509783, by rfl⟩ : syracuseStep 679711 = 1019567) B1019567
theorem B909167 : Blo 603293 909167 := bstep (se 1 (by rfl) ⟨681875, by rfl⟩ : syracuseStep 909167 = 1363751) B1363751
theorem B44130365 : Blo 603293 44130365 := bstep (se 3 (by rfl) ⟨8274443, by rfl⟩ : syracuseStep 44130365 = 16548887) B16548887
theorem B680143 : Blo 603293 680143 := bstep (se 1 (by rfl) ⟨510107, by rfl⟩ : syracuseStep 680143 = 1020215) B1020215
theorem B1532297 : Blo 603293 1532297 := bstep (se 2 (by rfl) ⟨574611, by rfl⟩ : syracuseStep 1532297 = 1149223) B1149223
theorem B909851 : Blo 603293 909851 := bstep (se 1 (by rfl) ⟨682388, by rfl⟩ : syracuseStep 909851 = 1364777) B1364777
theorem B910031 : Blo 603293 910031 := bstep (se 1 (by rfl) ⟨682523, by rfl⟩ : syracuseStep 910031 = 1365047) B1365047
theorem B910043 : Blo 603293 910043 := bstep (se 1 (by rfl) ⟨682532, by rfl⟩ : syracuseStep 910043 = 1365065) B1365065
theorem B681007 : Blo 603293 681007 := bstep (se 1 (by rfl) ⟨510755, by rfl⟩ : syracuseStep 681007 = 1021511) B1021511
theorem B910457 : Blo 603293 910457 := bstep (se 2 (by rfl) ⟨341421, by rfl⟩ : syracuseStep 910457 = 682843) B682843
theorem B681151 : Blo 603293 681151 := bstep (se 1 (by rfl) ⟨510863, by rfl⟩ : syracuseStep 681151 = 1021727) B1021727
theorem B681295 : Blo 603293 681295 := bstep (se 1 (by rfl) ⟨510971, by rfl⟩ : syracuseStep 681295 = 1021943) B1021943
theorem B1533431 : Blo 603293 1533431 := bstep (se 1 (by rfl) ⟨1150073, by rfl⟩ : syracuseStep 1533431 = 2300147) B2300147
theorem B3270215 : Blo 603293 3270215 := bstep (se 1 (by rfl) ⟨2452661, by rfl⟩ : syracuseStep 3270215 = 4905323) B4905323
theorem B3073787 : Blo 603293 3073787 := bstep (se 1 (by rfl) ⟨2305340, by rfl⟩ : syracuseStep 3073787 = 4610681) B4610681
theorem B26470253 : Blo 603293 26470253 := bstep (se 3 (by rfl) ⟨4963172, by rfl⟩ : syracuseStep 26470253 = 9926345) B9926345
theorem B1533887 : Blo 603293 1533887 := bstep (se 1 (by rfl) ⟨1150415, by rfl⟩ : syracuseStep 1533887 = 2300831) B2300831
theorem B682015 : Blo 603293 682015 := bstep (se 1 (by rfl) ⟨511511, by rfl⟩ : syracuseStep 682015 = 1023023) B1023023
theorem B1534049 : Blo 603293 1534049 := bstep (se 2 (by rfl) ⟨575268, by rfl⟩ : syracuseStep 1534049 = 1150537) B1150537
theorem B682267 : Blo 603293 682267 := bstep (se 1 (by rfl) ⟨511700, by rfl⟩ : syracuseStep 682267 = 1023401) B1023401
theorem B1534859 : Blo 603293 1534859 := bstep (se 1 (by rfl) ⟨1151144, by rfl⟩ : syracuseStep 1534859 = 2302289) B2302289
theorem B4909997 : Blo 603293 4909997 := bstep (se 3 (by rfl) ⟨920624, by rfl⟩ : syracuseStep 4909997 = 1841249) B1841249
theorem B7760843 : Blo 603293 7760843 := bstep (se 1 (by rfl) ⟨5820632, by rfl⟩ : syracuseStep 7760843 = 11641265) B11641265
theorem B1797857 : Blo 603293 1797857 := bstep (se 2 (by rfl) ⟨674196, by rfl⟩ : syracuseStep 1797857 = 1348393) B1348393
theorem B1535993 : Blo 603293 1535993 := bstep (se 2 (by rfl) ⟨575997, by rfl⟩ : syracuseStep 1535993 = 1151995) B1151995
theorem B1536641 : Blo 603293 1536641 := bstep (se 2 (by rfl) ⟨576240, by rfl⟩ : syracuseStep 1536641 = 1152481) B1152481
theorem B17396855 : Blo 603293 17396855 := bstep (se 1 (by rfl) ⟨13047641, by rfl⟩ : syracuseStep 17396855 = 26095283) B26095283
theorem B1471817 : Blo 603293 1471817 := bstep (se 2 (by rfl) ⟨551931, by rfl⟩ : syracuseStep 1471817 = 1103863) B1103863
theorem B2291111 : Blo 603293 2291111 := bstep (se 1 (by rfl) ⟨1718333, by rfl⟩ : syracuseStep 2291111 = 3436667) B3436667
theorem B17036867 : Blo 603293 17036867 := bstep (se 1 (by rfl) ⟨12777650, by rfl⟩ : syracuseStep 17036867 = 25555301) B25555301
theorem B10483991 : Blo 603293 10483991 := bstep (se 1 (by rfl) ⟨7862993, by rfl⟩ : syracuseStep 10483991 = 15725987) B15725987
theorem B13105597 : Blo 603293 13105597 := bstep (se 3 (by rfl) ⟨2457299, by rfl⟩ : syracuseStep 13105597 = 4914599) B4914599
theorem B33094277 : Blo 603293 33094277 := bstep (se 4 (by rfl) ⟨3102588, by rfl⟩ : syracuseStep 33094277 = 6205177) B6205177
theorem B2325217 : Blo 603293 2325217 := bstep (se 2 (by rfl) ⟨871956, by rfl⟩ : syracuseStep 2325217 = 1743913) B1743913
theorem B10517239 : Blo 603293 10517239 := bstep (se 1 (by rfl) ⟨7887929, by rfl⟩ : syracuseStep 10517239 = 15775859) B15775859
theorem B5372999 : Blo 603293 5372999 := bstep (se 1 (by rfl) ⟨4029749, by rfl⟩ : syracuseStep 5372999 = 8059499) B8059499
theorem B818267 : Blo 603293 818267 := bstep (se 1 (by rfl) ⟨613700, by rfl⟩ : syracuseStep 818267 = 1227401) B1227401
theorem B1146079 : Blo 603293 1146079 := bstep (se 1 (by rfl) ⟨859559, by rfl⟩ : syracuseStep 1146079 = 1719119) B1719119
theorem B49741249 : Blo 603293 49741249 := bstep (se 2 (by rfl) ⟨18652968, by rfl⟩ : syracuseStep 49741249 = 37305937) B37305937
theorem B2588111 : Blo 603293 2588111 := bstep (se 1 (by rfl) ⟨1941083, by rfl⟩ : syracuseStep 2588111 = 3882167) B3882167
theorem B5537575 : Blo 603293 5537575 := bstep (se 1 (by rfl) ⟨4153181, by rfl⟩ : syracuseStep 5537575 = 8306363) B8306363
theorem B3867095 : Blo 603293 3867095 := bstep (se 1 (by rfl) ⟨2900321, by rfl⟩ : syracuseStep 3867095 = 5800643) B5800643
theorem B2589887 : Blo 603293 2589887 := bstep (se 1 (by rfl) ⟨1942415, by rfl⟩ : syracuseStep 2589887 = 3884831) B3884831
theorem B5834551 : Blo 603293 5834551 := bstep (se 1 (by rfl) ⟨4375913, by rfl⟩ : syracuseStep 5834551 = 8751827) B8751827
theorem B1148843 : Blo 603293 1148843 := bstep (se 1 (by rfl) ⟨861632, by rfl⟩ : syracuseStep 1148843 = 1723265) B1723265
theorem B1149383 : Blo 603293 1149383 := bstep (se 1 (by rfl) ⟨862037, by rfl⟩ : syracuseStep 1149383 = 1724075) B1724075
theorem B2296457 : Blo 603293 2296457 := bstep (se 2 (by rfl) ⟨861171, by rfl⟩ : syracuseStep 2296457 = 1722343) B1722343
theorem B2591801 : Blo 603293 2591801 := bstep (se 2 (by rfl) ⟨971925, by rfl⟩ : syracuseStep 2591801 = 1943851) B1943851
theorem B1838305 : Blo 603293 1838305 := bstep (se 2 (by rfl) ⟨689364, by rfl⟩ : syracuseStep 1838305 = 1378729) B1378729
theorem B2297929 : Blo 603293 2297929 := bstep (se 2 (by rfl) ⟨861723, by rfl⟩ : syracuseStep 2297929 = 1723447) B1723447
theorem B2036231 : Blo 603293 2036231 := bstep (se 1 (by rfl) ⟨1527173, by rfl⟩ : syracuseStep 2036231 = 3054347) B3054347
theorem B922735 : Blo 603293 922735 := bstep (se 1 (by rfl) ⟨692051, by rfl⟩ : syracuseStep 922735 = 1384103) B1384103
theorem B2593903 : Blo 603293 2593903 := bstep (se 1 (by rfl) ⟨1945427, by rfl⟩ : syracuseStep 2593903 = 3890855) B3890855
theorem B2037149 : Blo 603293 2037149 := bstep (se 3 (by rfl) ⟨381965, by rfl⟩ : syracuseStep 2037149 = 763931) B763931
theorem B2037203 : Blo 603293 2037203 := bstep (se 1 (by rfl) ⟨1527902, by rfl⟩ : syracuseStep 2037203 = 3055805) B3055805
theorem B2037311 : Blo 603293 2037311 := bstep (se 1 (by rfl) ⟨1527983, by rfl⟩ : syracuseStep 2037311 = 3055967) B3055967
theorem B1021531 : Blo 603293 1021531 := bstep (se 1 (by rfl) ⟨766148, by rfl⟩ : syracuseStep 1021531 = 1532297) B1532297
theorem B3872609 : Blo 603293 3872609 := bstep (se 2 (by rfl) ⟨1452228, by rfl⟩ : syracuseStep 3872609 = 2904457) B2904457
theorem B7346065 : Blo 603293 7346065 := bstep (se 2 (by rfl) ⟨2754774, by rfl⟩ : syracuseStep 7346065 = 5509549) B5509549
theorem B2299873 : Blo 603293 2299873 := bstep (se 2 (by rfl) ⟨862452, by rfl⟩ : syracuseStep 2299873 = 1724905) B1724905
theorem B28350749 : Blo 603293 28350749 := bstep (se 3 (by rfl) ⟨5315765, by rfl⟩ : syracuseStep 28350749 = 10631531) B10631531
theorem B1022287 : Blo 603293 1022287 := bstep (se 1 (by rfl) ⟨766715, by rfl⟩ : syracuseStep 1022287 = 1533431) B1533431
theorem B1022591 : Blo 603293 1022591 := bstep (se 1 (by rfl) ⟨766943, by rfl⟩ : syracuseStep 1022591 = 1533887) B1533887
theorem B1022699 : Blo 603293 1022699 := bstep (se 1 (by rfl) ⟨767024, by rfl⟩ : syracuseStep 1022699 = 1534049) B1534049
theorem B13966091 : Blo 603293 13966091 := bstep (se 1 (by rfl) ⟨10474568, by rfl⟩ : syracuseStep 13966091 = 20949137) B20949137
theorem B1022969 : Blo 603293 1022969 := bstep (se 2 (by rfl) ⟨383613, by rfl⟩ : syracuseStep 1022969 = 767227) B767227
theorem B1023239 : Blo 603293 1023239 := bstep (se 1 (by rfl) ⟨767429, by rfl⟩ : syracuseStep 1023239 = 1534859) B1534859
theorem B2039147 : Blo 603293 2039147 := bstep (se 1 (by rfl) ⟨1529360, by rfl⟩ : syracuseStep 2039147 = 3058721) B3058721
theorem B2760473 : Blo 603293 2760473 := bstep (se 2 (by rfl) ⟨1035177, by rfl⟩ : syracuseStep 2760473 = 2070355) B2070355
theorem B11608049 : Blo 603293 11608049 := bstep (se 2 (by rfl) ⟨4353018, by rfl⟩ : syracuseStep 11608049 = 8706037) B8706037
theorem B1023995 : Blo 603293 1023995 := bstep (se 1 (by rfl) ⟨767996, by rfl⟩ : syracuseStep 1023995 = 1535993) B1535993
theorem B860215 : Blo 603293 860215 := bstep (se 1 (by rfl) ⟨645161, by rfl⟩ : syracuseStep 860215 = 1290323) B1290323
theorem B729271 : Blo 603293 729271 := bstep (se 1 (by rfl) ⟨546953, by rfl⟩ : syracuseStep 729271 = 1093907) B1093907
theorem B860539 : Blo 603293 860539 := bstep (se 1 (by rfl) ⟨645404, by rfl⟩ : syracuseStep 860539 = 1290809) B1290809
theorem B1024427 : Blo 603293 1024427 := bstep (se 1 (by rfl) ⟨768320, by rfl⟩ : syracuseStep 1024427 = 1536641) B1536641
theorem B17474129 : Blo 603293 17474129 := bstep (se 2 (by rfl) ⟨6552798, by rfl⟩ : syracuseStep 17474129 = 13105597) B13105597
theorem B2041145 : Blo 603293 2041145 := bstep (se 2 (by rfl) ⟨765429, by rfl⟩ : syracuseStep 2041145 = 1530859) B1530859
theorem B6989327 : Blo 603293 6989327 := bstep (se 1 (by rfl) ⟨5241995, by rfl⟩ : syracuseStep 6989327 = 10483991) B10483991
theorem B22062851 : Blo 603293 22062851 := bstep (se 1 (by rfl) ⟨16547138, by rfl⟩ : syracuseStep 22062851 = 33094277) B33094277
theorem B3581999 : Blo 603293 3581999 := bstep (se 1 (by rfl) ⟨2686499, by rfl⟩ : syracuseStep 3581999 = 5372999) B5372999
theorem B7383433 : Blo 603293 7383433 := bstep (se 2 (by rfl) ⟨2768787, by rfl⟩ : syracuseStep 7383433 = 5537575) B5537575
theorem B17640287 : Blo 603293 17640287 := bstep (se 1 (by rfl) ⟨13230215, by rfl⟩ : syracuseStep 17640287 = 26460431) B26460431
theorem B3059207 : Blo 603293 3059207 := bstep (se 1 (by rfl) ⟨2294405, by rfl⟩ : syracuseStep 3059207 = 4588811) B4588811
theorem B1093151 : Blo 603293 1093151 := bstep (se 1 (by rfl) ⟨819863, by rfl⟩ : syracuseStep 1093151 = 1639727) B1639727
theorem B7745057 : Blo 603293 7745057 := bstep (se 2 (by rfl) ⟨2904396, by rfl⟩ : syracuseStep 7745057 = 5808793) B5808793
theorem B8728181 : Blo 603293 8728181 := bstep (se 5 (by rfl) ⟨409133, by rfl⟩ : syracuseStep 8728181 = 818267) B818267
theorem B6565511 : Blo 603293 6565511 := bstep (se 1 (by rfl) ⟨4924133, by rfl⟩ : syracuseStep 6565511 = 9848267) B9848267
theorem B765607 : Blo 603293 765607 := bstep (se 1 (by rfl) ⟨574205, by rfl⟩ : syracuseStep 765607 = 1148411) B1148411
theorem B3059855 : Blo 603293 3059855 := bstep (se 1 (by rfl) ⟨2294891, by rfl⟩ : syracuseStep 3059855 = 4589783) B4589783
theorem B9843079 : Blo 603293 9843079 := bstep (se 1 (by rfl) ⟨7382309, by rfl⟩ : syracuseStep 9843079 = 14764619) B14764619
theorem B3060503 : Blo 603293 3060503 := bstep (se 1 (by rfl) ⟨2295377, by rfl⟩ : syracuseStep 3060503 = 4590755) B4590755
theorem B1749919 : Blo 603293 1749919 := bstep (se 1 (by rfl) ⟨1312439, by rfl⟩ : syracuseStep 1749919 = 2624879) B2624879
theorem B603391 : Blo 603293 603391 := bstep (se 1 (by rfl) ⟨452543, by rfl⟩ : syracuseStep 603391 = 905087) B905087
theorem B603519 : Blo 603293 603519 := bstep (se 1 (by rfl) ⟨452639, by rfl⟩ : syracuseStep 603519 = 905279) B905279
theorem B4371995 : Blo 603293 4371995 := bstep (se 1 (by rfl) ⟨3278996, by rfl⟩ : syracuseStep 4371995 = 6557993) B6557993
theorem B603675 : Blo 603293 603675 := bstep (se 1 (by rfl) ⟨452756, by rfl⟩ : syracuseStep 603675 = 905513) B905513
theorem B1226267 : Blo 603293 1226267 := bstep (se 1 (by rfl) ⟨919700, by rfl⟩ : syracuseStep 1226267 = 1839401) B1839401
theorem B603855 : Blo 603293 603855 := bstep (se 1 (by rfl) ⟨452891, by rfl⟩ : syracuseStep 603855 = 905783) B905783
theorem B14005993 : Blo 603293 14005993 := bstep (se 2 (by rfl) ⟨5252247, by rfl⟩ : syracuseStep 14005993 = 10504495) B10504495
theorem B1718003 : Blo 603293 1718003 := bstep (se 1 (by rfl) ⟨1288502, by rfl⟩ : syracuseStep 1718003 = 2577005) B2577005
theorem B5814139 : Blo 603293 5814139 := bstep (se 1 (by rfl) ⟨4360604, by rfl⟩ : syracuseStep 5814139 = 8721209) B8721209
theorem B604095 : Blo 603293 604095 := bstep (se 1 (by rfl) ⟨453071, by rfl⟩ : syracuseStep 604095 = 906143) B906143
theorem B604223 : Blo 603293 604223 := bstep (se 1 (by rfl) ⟨453167, by rfl⟩ : syracuseStep 604223 = 906335) B906335
theorem B604263 : Blo 603293 604263 := bstep (se 1 (by rfl) ⟨453197, by rfl⟩ : syracuseStep 604263 = 906395) B906395
theorem B3062123 : Blo 603293 3062123 := bstep (se 1 (by rfl) ⟨2296592, by rfl⟩ : syracuseStep 3062123 = 4593185) B4593185
theorem B3455369 : Blo 603293 3455369 := bstep (se 2 (by rfl) ⟨1295763, by rfl⟩ : syracuseStep 3455369 = 2591527) B2591527
theorem B604719 : Blo 603293 604719 := bstep (se 1 (by rfl) ⟨453539, by rfl⟩ : syracuseStep 604719 = 907079) B907079
theorem B5815097 : Blo 603293 5815097 := bstep (se 2 (by rfl) ⟨2180661, by rfl⟩ : syracuseStep 5815097 = 4361323) B4361323
theorem B3062609 : Blo 603293 3062609 := bstep (se 2 (by rfl) ⟨1148478, by rfl⟩ : syracuseStep 3062609 = 2296957) B2296957
theorem B605119 : Blo 603293 605119 := bstep (se 1 (by rfl) ⟨453839, by rfl⟩ : syracuseStep 605119 = 907679) B907679
theorem B605167 : Blo 603293 605167 := bstep (se 1 (by rfl) ⟨453875, by rfl⟩ : syracuseStep 605167 = 907751) B907751
theorem B4602905 : Blo 603293 4602905 := bstep (se 2 (by rfl) ⟨1726089, by rfl⟩ : syracuseStep 4602905 = 3452179) B3452179
theorem B1359017 : Blo 603293 1359017 := bstep (se 2 (by rfl) ⟨509631, by rfl⟩ : syracuseStep 1359017 = 1019263) B1019263
theorem B8731871 : Blo 603293 8731871 := bstep (se 1 (by rfl) ⟨6548903, by rfl⟩ : syracuseStep 8731871 = 13097807) B13097807
theorem B605663 : Blo 603293 605663 := bstep (se 1 (by rfl) ⟨454247, by rfl⟩ : syracuseStep 605663 = 908495) B908495
theorem B605743 : Blo 603293 605743 := bstep (se 1 (by rfl) ⟨454307, by rfl⟩ : syracuseStep 605743 = 908615) B908615
theorem B605851 : Blo 603293 605851 := bstep (se 1 (by rfl) ⟨454388, by rfl⟩ : syracuseStep 605851 = 908777) B908777
theorem B4898515 : Blo 603293 4898515 := bstep (se 1 (by rfl) ⟨3673886, by rfl⟩ : syracuseStep 4898515 = 7347773) B7347773
theorem B605947 : Blo 603293 605947 := bstep (se 1 (by rfl) ⟨454460, by rfl⟩ : syracuseStep 605947 = 908921) B908921
theorem B606111 : Blo 603293 606111 := bstep (se 1 (by rfl) ⟨454583, by rfl⟩ : syracuseStep 606111 = 909167) B909167
theorem B7389161 : Blo 603293 7389161 := bstep (se 2 (by rfl) ⟨2770935, by rfl⟩ : syracuseStep 7389161 = 5541871) B5541871
theorem B7880861 : Blo 603293 7880861 := bstep (se 3 (by rfl) ⟨1477661, by rfl⟩ : syracuseStep 7880861 = 2955323) B2955323
theorem B1360079 : Blo 603293 1360079 := bstep (se 1 (by rfl) ⟨1020059, by rfl⟩ : syracuseStep 1360079 = 2040119) B2040119
theorem B606567 : Blo 603293 606567 := bstep (se 1 (by rfl) ⟨454925, by rfl⟩ : syracuseStep 606567 = 909851) B909851
theorem B606687 : Blo 603293 606687 := bstep (se 1 (by rfl) ⟨455015, by rfl⟩ : syracuseStep 606687 = 910031) B910031
theorem B606695 : Blo 603293 606695 := bstep (se 1 (by rfl) ⟨455021, by rfl⟩ : syracuseStep 606695 = 910043) B910043
theorem B1294841 : Blo 603293 1294841 := bstep (se 2 (by rfl) ⟨485565, by rfl⟩ : syracuseStep 1294841 = 971131) B971131
theorem B606971 : Blo 603293 606971 := bstep (se 1 (by rfl) ⟨455228, by rfl⟩ : syracuseStep 606971 = 910457) B910457
theorem B2180143 : Blo 603293 2180143 := bstep (se 1 (by rfl) ⟨1635107, by rfl⟩ : syracuseStep 2180143 = 3270215) B3270215
theorem B2049191 : Blo 603293 2049191 := bstep (se 1 (by rfl) ⟨1536893, by rfl⟩ : syracuseStep 2049191 = 3073787) B3073787
theorem B17646835 : Blo 603293 17646835 := bstep (se 1 (by rfl) ⟨13235126, by rfl⟩ : syracuseStep 17646835 = 26470253) B26470253
theorem B10340135 : Blo 603293 10340135 := bstep (se 1 (by rfl) ⟨7755101, by rfl⟩ : syracuseStep 10340135 = 15510203) B15510203
theorem B2213689 : Blo 603293 2213689 := bstep (se 2 (by rfl) ⟨830133, by rfl⟩ : syracuseStep 2213689 = 1660267) B1660267
theorem B1361897 : Blo 603293 1361897 := bstep (se 2 (by rfl) ⟨510711, by rfl⟩ : syracuseStep 1361897 = 1021423) B1021423
theorem B1362383 : Blo 603293 1362383 := bstep (se 1 (by rfl) ⟨1021787, by rfl⟩ : syracuseStep 1362383 = 2043575) B2043575
theorem B1198571 : Blo 603293 1198571 := bstep (se 1 (by rfl) ⟨898928, by rfl⟩ : syracuseStep 1198571 = 1797857) B1797857
theorem B1362473 : Blo 603293 1362473 := bstep (se 2 (by rfl) ⟨510927, by rfl⟩ : syracuseStep 1362473 = 1021855) B1021855
theorem B67095215 : Blo 603293 67095215 := bstep (se 1 (by rfl) ⟨50321411, by rfl⟩ : syracuseStep 67095215 = 100642823) B100642823
theorem B1363355 : Blo 603293 1363355 := bstep (se 1 (by rfl) ⟨1022516, by rfl⟩ : syracuseStep 1363355 = 2045033) B2045033
theorem B3067307 : Blo 603293 3067307 := bstep (se 1 (by rfl) ⟨2300480, by rfl⟩ : syracuseStep 3067307 = 4600961) B4600961
theorem B1527407 : Blo 603293 1527407 := bstep (se 1 (by rfl) ⟨1145555, by rfl⟩ : syracuseStep 1527407 = 2291111) B2291111
theorem B3100289 : Blo 603293 3100289 := bstep (se 2 (by rfl) ⟨1162608, by rfl⟩ : syracuseStep 3100289 = 2325217) B2325217
theorem B11357911 : Blo 603293 11357911 := bstep (se 1 (by rfl) ⟨8518433, by rfl⟩ : syracuseStep 11357911 = 17036867) B17036867
theorem B905039 : Blo 603293 905039 := bstep (se 1 (by rfl) ⟨678779, by rfl⟩ : syracuseStep 905039 = 1357559) B1357559
theorem B905159 : Blo 603293 905159 := bstep (se 1 (by rfl) ⟨678869, by rfl⟩ : syracuseStep 905159 = 1357739) B1357739
theorem B905243 : Blo 603293 905243 := bstep (se 1 (by rfl) ⟨678932, by rfl⟩ : syracuseStep 905243 = 1357865) B1357865
theorem B1528105 : Blo 603293 1528105 := bstep (se 2 (by rfl) ⟨573039, by rfl⟩ : syracuseStep 1528105 = 1146079) B1146079
theorem B905519 : Blo 603293 905519 := bstep (se 1 (by rfl) ⟨679139, by rfl⟩ : syracuseStep 905519 = 1358279) B1358279
theorem B905627 : Blo 603293 905627 := bstep (se 1 (by rfl) ⟨679220, by rfl⟩ : syracuseStep 905627 = 1358441) B1358441
theorem B905663 : Blo 603293 905663 := bstep (se 1 (by rfl) ⟨679247, by rfl⟩ : syracuseStep 905663 = 1358495) B1358495
theorem B905759 : Blo 603293 905759 := bstep (se 1 (by rfl) ⟨679319, by rfl⟩ : syracuseStep 905759 = 1358639) B1358639
theorem B906047 : Blo 603293 906047 := bstep (se 1 (by rfl) ⟨679535, by rfl⟩ : syracuseStep 906047 = 1359071) B1359071
theorem B1364903 : Blo 603293 1364903 := bstep (se 1 (by rfl) ⟨1023677, by rfl⟩ : syracuseStep 1364903 = 2047355) B2047355
theorem B906191 : Blo 603293 906191 := bstep (se 1 (by rfl) ⟨679643, by rfl⟩ : syracuseStep 906191 = 1359287) B1359287
theorem B1725407 : Blo 603293 1725407 := bstep (se 1 (by rfl) ⟨1294055, by rfl⟩ : syracuseStep 1725407 = 2588111) B2588111
theorem B906281 : Blo 603293 906281 := bstep (se 2 (by rfl) ⟨339855, by rfl⟩ : syracuseStep 906281 = 679711) B679711
theorem B906311 : Blo 603293 906311 := bstep (se 1 (by rfl) ⟨679733, by rfl⟩ : syracuseStep 906311 = 1359467) B1359467
theorem B906491 : Blo 603293 906491 := bstep (se 1 (by rfl) ⟨679868, by rfl⟩ : syracuseStep 906491 = 1359737) B1359737
theorem B906551 : Blo 603293 906551 := bstep (se 1 (by rfl) ⟨679913, by rfl⟩ : syracuseStep 906551 = 1359827) B1359827
theorem B906857 : Blo 603293 906857 := bstep (se 2 (by rfl) ⟨340071, by rfl⟩ : syracuseStep 906857 = 680143) B680143
theorem B1529563 : Blo 603293 1529563 := bstep (se 1 (by rfl) ⟨1147172, by rfl⟩ : syracuseStep 1529563 = 2294345) B2294345
theorem B3069737 : Blo 603293 3069737 := bstep (se 2 (by rfl) ⟨1151151, by rfl⟩ : syracuseStep 3069737 = 2302303) B2302303
theorem B1726535 : Blo 603293 1726535 := bstep (se 1 (by rfl) ⟨1294901, by rfl⟩ : syracuseStep 1726535 = 2589803) B2589803
theorem B3070061 : Blo 603293 3070061 := bstep (se 3 (by rfl) ⟨575636, by rfl⟩ : syracuseStep 3070061 = 1151273) B1151273
theorem B907391 : Blo 603293 907391 := bstep (se 1 (by rfl) ⟨680543, by rfl⟩ : syracuseStep 907391 = 1361087) B1361087
theorem B907487 : Blo 603293 907487 := bstep (se 1 (by rfl) ⟨680615, by rfl⟩ : syracuseStep 907487 = 1361231) B1361231
theorem B907547 : Blo 603293 907547 := bstep (se 1 (by rfl) ⟨680660, by rfl⟩ : syracuseStep 907547 = 1361321) B1361321
theorem B1726751 : Blo 603293 1726751 := bstep (se 1 (by rfl) ⟨1295063, by rfl⟩ : syracuseStep 1726751 = 2590127) B2590127
theorem B907871 : Blo 603293 907871 := bstep (se 1 (by rfl) ⟨680903, by rfl⟩ : syracuseStep 907871 = 1361807) B1361807
theorem B1661627 : Blo 603293 1661627 := bstep (se 1 (by rfl) ⟨1246220, by rfl⟩ : syracuseStep 1661627 = 2492441) B2492441
theorem B3889853 : Blo 603293 3889853 := bstep (se 3 (by rfl) ⟨729347, by rfl⟩ : syracuseStep 3889853 = 1458695) B1458695
theorem B645823 : Blo 603293 645823 := bstep (se 1 (by rfl) ⟨484367, by rfl⟩ : syracuseStep 645823 = 968735) B968735
theorem B907967 : Blo 603293 907967 := bstep (se 1 (by rfl) ⟨680975, by rfl⟩ : syracuseStep 907967 = 1361951) B1361951
theorem B908009 : Blo 603293 908009 := bstep (se 2 (by rfl) ⟨340503, by rfl⟩ : syracuseStep 908009 = 681007) B681007
theorem B908135 : Blo 603293 908135 := bstep (se 1 (by rfl) ⟨681101, by rfl⟩ : syracuseStep 908135 = 1362203) B1362203
theorem B908201 : Blo 603293 908201 := bstep (se 2 (by rfl) ⟨340575, by rfl⟩ : syracuseStep 908201 = 681151) B681151
theorem B908351 : Blo 603293 908351 := bstep (se 1 (by rfl) ⟨681263, by rfl⟩ : syracuseStep 908351 = 1362527) B1362527
theorem B908393 : Blo 603293 908393 := bstep (se 2 (by rfl) ⟨340647, by rfl⟩ : syracuseStep 908393 = 681295) B681295
theorem B1531001 : Blo 603293 1531001 := bstep (se 2 (by rfl) ⟨574125, by rfl⟩ : syracuseStep 1531001 = 1148251) B1148251
theorem B908519 : Blo 603293 908519 := bstep (se 1 (by rfl) ⟨681389, by rfl⟩ : syracuseStep 908519 = 1362779) B1362779
theorem B1531163 : Blo 603293 1531163 := bstep (se 1 (by rfl) ⟨1148372, by rfl⟩ : syracuseStep 1531163 = 2296745) B2296745
theorem B45505925 : Blo 603293 45505925 := bstep (se 4 (by rfl) ⟨4266180, by rfl⟩ : syracuseStep 45505925 = 8532361) B8532361
theorem B909023 : Blo 603293 909023 := bstep (se 1 (by rfl) ⟨681767, by rfl⟩ : syracuseStep 909023 = 1363535) B1363535
theorem B909353 : Blo 603293 909353 := bstep (se 2 (by rfl) ⟨341007, by rfl⟩ : syracuseStep 909353 = 682015) B682015
theorem B679999 : Blo 603293 679999 := bstep (se 1 (by rfl) ⟨509999, by rfl⟩ : syracuseStep 679999 = 1019999) B1019999
theorem B909383 : Blo 603293 909383 := bstep (se 1 (by rfl) ⟨682037, by rfl⟩ : syracuseStep 909383 = 1364075) B1364075
theorem B909419 : Blo 603293 909419 := bstep (se 1 (by rfl) ⟨682064, by rfl⟩ : syracuseStep 909419 = 1364129) B1364129
theorem B909503 : Blo 603293 909503 := bstep (se 1 (by rfl) ⟨682127, by rfl⟩ : syracuseStep 909503 = 1364255) B1364255
theorem B909689 : Blo 603293 909689 := bstep (se 2 (by rfl) ⟨341133, by rfl⟩ : syracuseStep 909689 = 682267) B682267
theorem B2581055 : Blo 603293 2581055 := bstep (se 1 (by rfl) ⟨1935791, by rfl⟩ : syracuseStep 2581055 = 3871583) B3871583
theorem B909983 : Blo 603293 909983 := bstep (se 1 (by rfl) ⟨682487, by rfl⟩ : syracuseStep 909983 = 1364975) B1364975
theorem B3924845 : Blo 603293 3924845 := bstep (se 3 (by rfl) ⟨735908, by rfl⟩ : syracuseStep 3924845 = 1471817) B1471817
theorem B680863 : Blo 603293 680863 := bstep (se 1 (by rfl) ⟨510647, by rfl⟩ : syracuseStep 680863 = 1021295) B1021295
theorem B2909087 : Blo 603293 2909087 := bstep (se 1 (by rfl) ⟨2181815, by rfl⟩ : syracuseStep 2909087 = 4363631) B4363631
theorem B910319 : Blo 603293 910319 := bstep (se 1 (by rfl) ⟨682739, by rfl⟩ : syracuseStep 910319 = 1365479) B1365479
theorem B910427 : Blo 603293 910427 := bstep (se 1 (by rfl) ⟨682820, by rfl⟩ : syracuseStep 910427 = 1365641) B1365641
theorem B910439 : Blo 603293 910439 := bstep (se 1 (by rfl) ⟨682829, by rfl⟩ : syracuseStep 910439 = 1365659) B1365659
theorem B910571 : Blo 603293 910571 := bstep (se 1 (by rfl) ⟨682928, by rfl⟩ : syracuseStep 910571 = 1365857) B1365857
theorem B3106121 : Blo 603293 3106121 := bstep (se 2 (by rfl) ⟨1164795, by rfl⟩ : syracuseStep 3106121 = 2329591) B2329591
theorem B910703 : Blo 603293 910703 := bstep (se 1 (by rfl) ⟨683027, by rfl⟩ : syracuseStep 910703 = 1366055) B1366055
theorem B910823 : Blo 603293 910823 := bstep (se 1 (by rfl) ⟨683117, by rfl⟩ : syracuseStep 910823 = 1366235) B1366235
theorem B3073949 : Blo 603293 3073949 := bstep (se 3 (by rfl) ⟨576365, by rfl⟩ : syracuseStep 3073949 = 1152731) B1152731
theorem B29420243 : Blo 603293 29420243 := bstep (se 1 (by rfl) ⟨22065182, by rfl⟩ : syracuseStep 29420243 = 44130365) B44130365
theorem B1534727 : Blo 603293 1534727 := bstep (se 1 (by rfl) ⟨1151045, by rfl⟩ : syracuseStep 1534727 = 2302091) B2302091
theorem B3828959 : Blo 603293 3828959 := bstep (se 1 (by rfl) ⟨2871719, by rfl⟩ : syracuseStep 3828959 = 5743439) B5743439
theorem B1863805 : Blo 603293 1863805 := bstep (se 3 (by rfl) ⟨349463, by rfl⟩ : syracuseStep 1863805 = 698927) B698927
theorem B3273331 : Blo 603293 3273331 := bstep (se 1 (by rfl) ⟨2454998, by rfl⟩ : syracuseStep 3273331 = 4909997) B4909997
theorem B5173895 : Blo 603293 5173895 := bstep (se 1 (by rfl) ⟨3880421, by rfl⟩ : syracuseStep 5173895 = 7760843) B7760843
theorem B3110147 : Blo 603293 3110147 := bstep (se 1 (by rfl) ⟨2332610, by rfl⟩ : syracuseStep 3110147 = 4665221) B4665221
theorem B7730909 : Blo 603293 7730909 := bstep (se 3 (by rfl) ⟨1449545, by rfl⟩ : syracuseStep 7730909 = 2899091) B2899091
theorem B11597903 : Blo 603293 11597903 := bstep (se 1 (by rfl) ⟨8698427, by rfl⟩ : syracuseStep 11597903 = 17396855) B17396855
theorem B2914451 : Blo 603293 2914451 := bstep (se 1 (by rfl) ⟨2185838, by rfl⟩ : syracuseStep 2914451 = 4371677) B4371677
theorem B14022985 : Blo 603293 14022985 := bstep (se 2 (by rfl) ⟨5258619, by rfl⟩ : syracuseStep 14022985 = 10517239) B10517239
theorem B8288851 : Blo 603293 8288851 := bstep (se 1 (by rfl) ⟨6216638, by rfl⟩ : syracuseStep 8288851 = 12433277) B12433277
theorem B12384913 : Blo 603293 12384913 := bstep (se 2 (by rfl) ⟨4644342, by rfl⟩ : syracuseStep 12384913 = 9288685) B9288685
theorem B66321665 : Blo 603293 66321665 := bstep (se 2 (by rfl) ⟨24870624, by rfl⟩ : syracuseStep 66321665 = 49741249) B49741249
theorem B2293373 : Blo 603293 2293373 := bstep (se 3 (by rfl) ⟨430007, by rfl⟩ : syracuseStep 2293373 = 860015) B860015
theorem B6913835 : Blo 603293 6913835 := bstep (se 1 (by rfl) ⟨5185376, by rfl⟩ : syracuseStep 6913835 = 10370753) B10370753
theorem B1933267 : Blo 603293 1933267 := bstep (se 1 (by rfl) ⟨1449950, by rfl⟩ : syracuseStep 1933267 = 2899901) B2899901
theorem B1146953 : Blo 603293 1146953 := bstep (se 2 (by rfl) ⟨430107, by rfl⟩ : syracuseStep 1146953 = 860215) B860215
theorem B1147385 : Blo 603293 1147385 := bstep (se 2 (by rfl) ⟨430269, by rfl⟩ : syracuseStep 1147385 = 860539) B860539
theorem B23529113 : Blo 603293 23529113 := bstep (se 2 (by rfl) ⟨8823417, by rfl⟩ : syracuseStep 23529113 = 17646835) B17646835
theorem B44730143 : Blo 603293 44730143 := bstep (se 1 (by rfl) ⟨33547607, by rfl⟩ : syracuseStep 44730143 = 67095215) B67095215
theorem B1018271 : Blo 603293 1018271 := bstep (se 1 (by rfl) ⟨763703, by rfl⟩ : syracuseStep 1018271 = 1527407) B1527407
theorem B2951585 : Blo 603293 2951585 := bstep (se 2 (by rfl) ⟨1106844, by rfl⟩ : syracuseStep 2951585 = 2213689) B2213689
theorem B1150271 : Blo 603293 1150271 := bstep (se 1 (by rfl) ⟨862703, by rfl⟩ : syracuseStep 1150271 = 1725407) B1725407
theorem B3444389 : Blo 603293 3444389 := bstep (se 4 (by rfl) ⟨322911, by rfl⟩ : syracuseStep 3444389 = 645823) B645823
theorem B1151023 : Blo 603293 1151023 := bstep (se 1 (by rfl) ⟨863267, by rfl⟩ : syracuseStep 1151023 = 1726535) B1726535
theorem B1151167 : Blo 603293 1151167 := bstep (se 1 (by rfl) ⟨863375, by rfl⟩ : syracuseStep 1151167 = 1726751) B1726751
theorem B2593235 : Blo 603293 2593235 := bstep (se 1 (by rfl) ⟨1944926, by rfl⟩ : syracuseStep 2593235 = 3889853) B3889853
theorem B9310727 : Blo 603293 9310727 := bstep (se 1 (by rfl) ⟨6983045, by rfl⟩ : syracuseStep 9310727 = 13966091) B13966091
theorem B1020667 : Blo 603293 1020667 := bstep (se 1 (by rfl) ⟨765500, by rfl⟩ : syracuseStep 1020667 = 1531001) B1531001
theorem B1020775 : Blo 603293 1020775 := bstep (se 1 (by rfl) ⟨765581, by rfl⟩ : syracuseStep 1020775 = 1531163) B1531163
theorem B1020809 : Blo 603293 1020809 := bstep (se 2 (by rfl) ⟨382803, by rfl⟩ : syracuseStep 1020809 = 765607) B765607
theorem B15143881 : Blo 603293 15143881 := bstep (se 2 (by rfl) ⟨5678955, by rfl⟩ : syracuseStep 15143881 = 11357911) B11357911
theorem B1840315 : Blo 603293 1840315 := bstep (se 1 (by rfl) ⟨1380236, by rfl⟩ : syracuseStep 1840315 = 2760473) B2760473
theorem B7738699 : Blo 603293 7738699 := bstep (se 1 (by rfl) ⟨5804024, by rfl⟩ : syracuseStep 7738699 = 11608049) B11608049
theorem B2037473 : Blo 603293 2037473 := bstep (se 2 (by rfl) ⟨764052, by rfl⟩ : syracuseStep 2037473 = 1528105) B1528105
theorem B1939391 : Blo 603293 1939391 := bstep (se 1 (by rfl) ⟨1454543, by rfl⟩ : syracuseStep 1939391 = 2909087) B2909087
theorem B4364441 : Blo 603293 4364441 := bstep (se 2 (by rfl) ⟨1636665, by rfl⟩ : syracuseStep 4364441 = 3273331) B3273331
theorem B4659551 : Blo 603293 4659551 := bstep (se 1 (by rfl) ⟨3494663, by rfl⟩ : syracuseStep 4659551 = 6989327) B6989327
theorem B2333225 : Blo 603293 2333225 := bstep (se 2 (by rfl) ⟨874959, by rfl⟩ : syracuseStep 2333225 = 1749919) B1749919
theorem B1023151 : Blo 603293 1023151 := bstep (se 1 (by rfl) ⟨767363, by rfl⟩ : syracuseStep 1023151 = 1534727) B1534727
theorem B2039417 : Blo 603293 2039417 := bstep (se 2 (by rfl) ⟨764781, by rfl⟩ : syracuseStep 2039417 = 1529563) B1529563
theorem B2039471 : Blo 603293 2039471 := bstep (se 1 (by rfl) ⟨1529603, by rfl⟩ : syracuseStep 2039471 = 3059207) B3059207
theorem B728767 : Blo 603293 728767 := bstep (se 1 (by rfl) ⟨546575, by rfl⟩ : syracuseStep 728767 = 1093151) B1093151
theorem B2039903 : Blo 603293 2039903 := bstep (se 1 (by rfl) ⟨1529927, by rfl⟩ : syracuseStep 2039903 = 3059855) B3059855
theorem B3449263 : Blo 603293 3449263 := bstep (se 1 (by rfl) ⟨2586947, by rfl⟩ : syracuseStep 3449263 = 5173895) B5173895
theorem B2040335 : Blo 603293 2040335 := bstep (se 1 (by rfl) ⟨1530251, by rfl⟩ : syracuseStep 2040335 = 3060503) B3060503
theorem B11051801 : Blo 603293 11051801 := bstep (se 2 (by rfl) ⟨4144425, by rfl⟩ : syracuseStep 11051801 = 8288851) B8288851
theorem B2073431 : Blo 603293 2073431 := bstep (se 1 (by rfl) ⟨1555073, by rfl⟩ : syracuseStep 2073431 = 3110147) B3110147
theorem B5153939 : Blo 603293 5153939 := bstep (se 1 (by rfl) ⟨3865454, by rfl⟩ : syracuseStep 5153939 = 7730909) B7730909
theorem B1942967 : Blo 603293 1942967 := bstep (se 1 (by rfl) ⟨1457225, by rfl⟩ : syracuseStep 1942967 = 2914451) B2914451
theorem B2041415 : Blo 603293 2041415 := bstep (se 1 (by rfl) ⟨1531061, by rfl⟩ : syracuseStep 2041415 = 3062123) B3062123
theorem B2303579 : Blo 603293 2303579 := bstep (se 1 (by rfl) ⟨1727684, by rfl⟩ : syracuseStep 2303579 = 3455369) B3455369
theorem B8267437 : Blo 603293 8267437 := bstep (se 3 (by rfl) ⟨1550144, by rfl⟩ : syracuseStep 8267437 = 3100289) B3100289
theorem B3876731 : Blo 603293 3876731 := bstep (se 1 (by rfl) ⟨2907548, by rfl⟩ : syracuseStep 3876731 = 5815097) B5815097
theorem B2041739 : Blo 603293 2041739 := bstep (se 1 (by rfl) ⟨1531304, by rfl⟩ : syracuseStep 2041739 = 3062609) B3062609
theorem B44214443 : Blo 603293 44214443 := bstep (se 1 (by rfl) ⟨33160832, by rfl⟩ : syracuseStep 44214443 = 66321665) B66321665
theorem B6531353 : Blo 603293 6531353 := bstep (se 2 (by rfl) ⟨2449257, by rfl⟩ : syracuseStep 6531353 = 4898515) B4898515
theorem B4926107 : Blo 603293 4926107 := bstep (se 1 (by rfl) ⟨3694580, by rfl⟩ : syracuseStep 4926107 = 7389161) B7389161
theorem B5253907 : Blo 603293 5253907 := bstep (se 1 (by rfl) ⟨3940430, by rfl⟩ : syracuseStep 5253907 = 7880861) B7880861
theorem B863227 : Blo 603293 863227 := bstep (se 1 (by rfl) ⟨647420, by rfl⟩ : syracuseStep 863227 = 1294841) B1294841
theorem B6893423 : Blo 603293 6893423 := bstep (se 1 (by rfl) ⟨5170067, by rfl⟩ : syracuseStep 6893423 = 10340135) B10340135
theorem B766255 : Blo 603293 766255 := bstep (se 1 (by rfl) ⟨574691, by rfl⟩ : syracuseStep 766255 = 1149383) B1149383
theorem B2044871 : Blo 603293 2044871 := bstep (se 1 (by rfl) ⟨1533653, by rfl⟩ : syracuseStep 2044871 = 3067307) B3067307
theorem B7779401 : Blo 603293 7779401 := bstep (se 2 (by rfl) ⟨2917275, by rfl⟩ : syracuseStep 7779401 = 5834551) B5834551
theorem B603359 : Blo 603293 603359 := bstep (se 1 (by rfl) ⟨452519, by rfl⟩ : syracuseStep 603359 = 905039) B905039
theorem B603439 : Blo 603293 603439 := bstep (se 1 (by rfl) ⟨452579, by rfl⟩ : syracuseStep 603439 = 905159) B905159
theorem B603495 : Blo 603293 603495 := bstep (se 1 (by rfl) ⟨452621, by rfl⟩ : syracuseStep 603495 = 905243) B905243
theorem B603679 : Blo 603293 603679 := bstep (se 1 (by rfl) ⟨452759, by rfl⟩ : syracuseStep 603679 = 905519) B905519
theorem B603751 : Blo 603293 603751 := bstep (se 1 (by rfl) ⟨452813, by rfl⟩ : syracuseStep 603751 = 905627) B905627
theorem B603775 : Blo 603293 603775 := bstep (se 1 (by rfl) ⟨452831, by rfl⟩ : syracuseStep 603775 = 905663) B905663
theorem B1357487 : Blo 603293 1357487 := bstep (se 1 (by rfl) ⟨1018115, by rfl⟩ : syracuseStep 1357487 = 2036231) B2036231
theorem B603839 : Blo 603293 603839 := bstep (se 1 (by rfl) ⟨452879, by rfl⟩ : syracuseStep 603839 = 905759) B905759
theorem B9844577 : Blo 603293 9844577 := bstep (se 2 (by rfl) ⟨3691716, by rfl⟩ : syracuseStep 9844577 = 7383433) B7383433
theorem B604031 : Blo 603293 604031 := bstep (se 1 (by rfl) ⟨453023, by rfl⟩ : syracuseStep 604031 = 906047) B906047
theorem B604127 : Blo 603293 604127 := bstep (se 1 (by rfl) ⟨453095, by rfl⟩ : syracuseStep 604127 = 906191) B906191
theorem B604187 : Blo 603293 604187 := bstep (se 1 (by rfl) ⟨453140, by rfl⟩ : syracuseStep 604187 = 906281) B906281
theorem B604207 : Blo 603293 604207 := bstep (se 1 (by rfl) ⟨453155, by rfl⟩ : syracuseStep 604207 = 906311) B906311
theorem B604327 : Blo 603293 604327 := bstep (se 1 (by rfl) ⟨453245, by rfl⟩ : syracuseStep 604327 = 906491) B906491
theorem B604367 : Blo 603293 604367 := bstep (se 1 (by rfl) ⟨453275, by rfl⟩ : syracuseStep 604367 = 906551) B906551
theorem B1358099 : Blo 603293 1358099 := bstep (se 1 (by rfl) ⟨1018574, by rfl⟩ : syracuseStep 1358099 = 2037149) B2037149
theorem B1358135 : Blo 603293 1358135 := bstep (se 1 (by rfl) ⟨1018601, by rfl⟩ : syracuseStep 1358135 = 2037203) B2037203
theorem B1358207 : Blo 603293 1358207 := bstep (se 1 (by rfl) ⟨1018655, by rfl⟩ : syracuseStep 1358207 = 2037311) B2037311
theorem B604571 : Blo 603293 604571 := bstep (se 1 (by rfl) ⟨453428, by rfl⟩ : syracuseStep 604571 = 906857) B906857
theorem B2046491 : Blo 603293 2046491 := bstep (se 1 (by rfl) ⟨1534868, by rfl⟩ : syracuseStep 2046491 = 3069737) B3069737
theorem B2046707 : Blo 603293 2046707 := bstep (se 1 (by rfl) ⟨1535030, by rfl⟩ : syracuseStep 2046707 = 3070061) B3070061
theorem B604927 : Blo 603293 604927 := bstep (se 1 (by rfl) ⟨453695, by rfl⟩ : syracuseStep 604927 = 907391) B907391
theorem B604991 : Blo 603293 604991 := bstep (se 1 (by rfl) ⟨453743, by rfl⟩ : syracuseStep 604991 = 907487) B907487
theorem B605031 : Blo 603293 605031 := bstep (se 1 (by rfl) ⟨453773, by rfl⟩ : syracuseStep 605031 = 907547) B907547
theorem B605247 : Blo 603293 605247 := bstep (se 1 (by rfl) ⟨453935, by rfl⟩ : syracuseStep 605247 = 907871) B907871
theorem B605311 : Blo 603293 605311 := bstep (se 1 (by rfl) ⟨453983, by rfl⟩ : syracuseStep 605311 = 907967) B907967
theorem B605339 : Blo 603293 605339 := bstep (se 1 (by rfl) ⟨454004, by rfl⟩ : syracuseStep 605339 = 908009) B908009
theorem B605423 : Blo 603293 605423 := bstep (se 1 (by rfl) ⟨454067, by rfl⟩ : syracuseStep 605423 = 908135) B908135
theorem B605467 : Blo 603293 605467 := bstep (se 1 (by rfl) ⟨454100, by rfl⟩ : syracuseStep 605467 = 908201) B908201
theorem B605567 : Blo 603293 605567 := bstep (se 1 (by rfl) ⟨454175, by rfl⟩ : syracuseStep 605567 = 908351) B908351
theorem B605595 : Blo 603293 605595 := bstep (se 1 (by rfl) ⟨454196, by rfl⟩ : syracuseStep 605595 = 908393) B908393
theorem B605679 : Blo 603293 605679 := bstep (se 1 (by rfl) ⟨454259, by rfl⟩ : syracuseStep 605679 = 908519) B908519
theorem B1359431 : Blo 603293 1359431 := bstep (se 1 (by rfl) ⟨1019573, by rfl⟩ : syracuseStep 1359431 = 2039147) B2039147
theorem B3063581 : Blo 603293 3063581 := bstep (se 3 (by rfl) ⟨574421, by rfl⟩ : syracuseStep 3063581 = 1148843) B1148843
theorem B606015 : Blo 603293 606015 := bstep (se 1 (by rfl) ⟨454511, by rfl⟩ : syracuseStep 606015 = 909023) B909023
theorem B606235 : Blo 603293 606235 := bstep (se 1 (by rfl) ⟨454676, by rfl⟩ : syracuseStep 606235 = 909353) B909353
theorem B606255 : Blo 603293 606255 := bstep (se 1 (by rfl) ⟨454691, by rfl⟩ : syracuseStep 606255 = 909383) B909383
theorem B606279 : Blo 603293 606279 := bstep (se 1 (by rfl) ⟨454709, by rfl⟩ : syracuseStep 606279 = 909419) B909419
theorem B3063905 : Blo 603293 3063905 := bstep (se 2 (by rfl) ⟨1148964, by rfl⟩ : syracuseStep 3063905 = 2297929) B2297929
theorem B606335 : Blo 603293 606335 := bstep (se 1 (by rfl) ⟨454751, by rfl⟩ : syracuseStep 606335 = 909503) B909503
theorem B606459 : Blo 603293 606459 := bstep (se 1 (by rfl) ⟨454844, by rfl⟩ : syracuseStep 606459 = 909689) B909689
theorem B1720703 : Blo 603293 1720703 := bstep (se 1 (by rfl) ⟨1290527, by rfl⟩ : syracuseStep 1720703 = 2581055) B2581055
theorem B11649419 : Blo 603293 11649419 := bstep (se 1 (by rfl) ⟨8737064, by rfl⟩ : syracuseStep 11649419 = 17474129) B17474129
theorem B606655 : Blo 603293 606655 := bstep (se 1 (by rfl) ⟨454991, by rfl⟩ : syracuseStep 606655 = 909983) B909983
theorem B13124105 : Blo 603293 13124105 := bstep (se 2 (by rfl) ⟨4921539, by rfl⟩ : syracuseStep 13124105 = 9843079) B9843079
theorem B606879 : Blo 603293 606879 := bstep (se 1 (by rfl) ⟨455159, by rfl⟩ : syracuseStep 606879 = 910319) B910319
theorem B606951 : Blo 603293 606951 := bstep (se 1 (by rfl) ⟨455213, by rfl⟩ : syracuseStep 606951 = 910427) B910427
theorem B606959 : Blo 603293 606959 := bstep (se 1 (by rfl) ⟨455219, by rfl⟩ : syracuseStep 606959 = 910439) B910439
theorem B607047 : Blo 603293 607047 := bstep (se 1 (by rfl) ⟨455285, by rfl⟩ : syracuseStep 607047 = 910571) B910571
theorem B1360763 : Blo 603293 1360763 := bstep (se 1 (by rfl) ⟨1020572, by rfl⟩ : syracuseStep 1360763 = 2041145) B2041145
theorem B607135 : Blo 603293 607135 := bstep (se 1 (by rfl) ⟨455351, by rfl⟩ : syracuseStep 607135 = 910703) B910703
theorem B607215 : Blo 603293 607215 := bstep (se 1 (by rfl) ⟨455411, by rfl⟩ : syracuseStep 607215 = 910823) B910823
theorem B2049299 : Blo 603293 2049299 := bstep (se 1 (by rfl) ⟨1536974, by rfl⟩ : syracuseStep 2049299 = 3073949) B3073949
theorem B3196189 : Blo 603293 3196189 := bstep (se 3 (by rfl) ⟨599285, by rfl⟩ : syracuseStep 3196189 = 1198571) B1198571
theorem B1230313 : Blo 603293 1230313 := bstep (se 2 (by rfl) ⟨461367, by rfl⟩ : syracuseStep 1230313 = 922735) B922735
theorem B3458537 : Blo 603293 3458537 := bstep (se 2 (by rfl) ⟨1296951, by rfl⟩ : syracuseStep 3458537 = 2593903) B2593903
theorem B19613495 : Blo 603293 19613495 := bstep (se 1 (by rfl) ⟨14710121, by rfl⟩ : syracuseStep 19613495 = 29420243) B29420243
theorem B1362041 : Blo 603293 1362041 := bstep (se 2 (by rfl) ⟨510765, by rfl⟩ : syracuseStep 1362041 = 1021531) B1021531
theorem B5163371 : Blo 603293 5163371 := bstep (se 1 (by rfl) ⟨3872528, by rfl⟩ : syracuseStep 5163371 = 7745057) B7745057
theorem B5818787 : Blo 603293 5818787 := bstep (se 1 (by rfl) ⟨4364090, by rfl⟩ : syracuseStep 5818787 = 8728181) B8728181
theorem B4377007 : Blo 603293 4377007 := bstep (se 1 (by rfl) ⟨3282755, by rfl⟩ : syracuseStep 4377007 = 6565511) B6565511
theorem B7752185 : Blo 603293 7752185 := bstep (se 2 (by rfl) ⟨2907069, by rfl⟩ : syracuseStep 7752185 = 5814139) B5814139
theorem B3066497 : Blo 603293 3066497 := bstep (se 2 (by rfl) ⟨1149936, by rfl⟩ : syracuseStep 3066497 = 2299873) B2299873
theorem B18697313 : Blo 603293 18697313 := bstep (se 2 (by rfl) ⟨7011492, by rfl⟩ : syracuseStep 18697313 = 14022985) B14022985
theorem B1363049 : Blo 603293 1363049 := bstep (se 2 (by rfl) ⟨511143, by rfl⟩ : syracuseStep 1363049 = 1022287) B1022287
theorem B3068603 : Blo 603293 3068603 := bstep (se 1 (by rfl) ⟨2301452, by rfl⟩ : syracuseStep 3068603 = 4602905) B4602905
theorem B906011 : Blo 603293 906011 := bstep (se 1 (by rfl) ⟨679508, by rfl⟩ : syracuseStep 906011 = 1359017) B1359017
theorem B5821247 : Blo 603293 5821247 := bstep (se 1 (by rfl) ⟨4365935, by rfl⟩ : syracuseStep 5821247 = 8731871) B8731871
theorem B1528915 : Blo 603293 1528915 := bstep (se 1 (by rfl) ⟨1146686, by rfl⟩ : syracuseStep 1528915 = 2293373) B2293373
theorem B4609223 : Blo 603293 4609223 := bstep (se 1 (by rfl) ⟨3456917, by rfl⟩ : syracuseStep 4609223 = 6913835) B6913835
theorem B2577689 : Blo 603293 2577689 := bstep (se 2 (by rfl) ⟨966633, by rfl⟩ : syracuseStep 2577689 = 1933267) B1933267
theorem B906665 : Blo 603293 906665 := bstep (se 2 (by rfl) ⟨339999, by rfl⟩ : syracuseStep 906665 = 679999) B679999
theorem B906719 : Blo 603293 906719 := bstep (se 1 (by rfl) ⟨680039, by rfl⟩ : syracuseStep 906719 = 1360079) B1360079
theorem B972361 : Blo 603293 972361 := bstep (se 2 (by rfl) ⟨364635, by rfl⟩ : syracuseStep 972361 = 729271) B729271
theorem B2578063 : Blo 603293 2578063 := bstep (se 1 (by rfl) ⟨1933547, by rfl⟩ : syracuseStep 2578063 = 3867095) B3867095
theorem B1366127 : Blo 603293 1366127 := bstep (se 1 (by rfl) ⟨1024595, by rfl⟩ : syracuseStep 1366127 = 2049191) B2049191
theorem B1726591 : Blo 603293 1726591 := bstep (se 1 (by rfl) ⟨1294943, by rfl⟩ : syracuseStep 1726591 = 2589887) B2589887
theorem B907817 : Blo 603293 907817 := bstep (se 2 (by rfl) ⟨340431, by rfl⟩ : syracuseStep 907817 = 680863) B680863
theorem B907931 : Blo 603293 907931 := bstep (se 1 (by rfl) ⟨680948, by rfl⟩ : syracuseStep 907931 = 1361897) B1361897
theorem B2906857 : Blo 603293 2906857 := bstep (se 2 (by rfl) ⟨1090071, by rfl⟩ : syracuseStep 2906857 = 2180143) B2180143
theorem B908255 : Blo 603293 908255 := bstep (se 1 (by rfl) ⟨681191, by rfl⟩ : syracuseStep 908255 = 1362383) B1362383
theorem B908315 : Blo 603293 908315 := bstep (se 1 (by rfl) ⟨681236, by rfl⟩ : syracuseStep 908315 = 1362473) B1362473
theorem B1530971 : Blo 603293 1530971 := bstep (se 1 (by rfl) ⟨1148228, by rfl⟩ : syracuseStep 1530971 = 2296457) B2296457
theorem B1727867 : Blo 603293 1727867 := bstep (se 1 (by rfl) ⟨1295900, by rfl⟩ : syracuseStep 1727867 = 2591801) B2591801
theorem B908903 : Blo 603293 908903 := bstep (se 1 (by rfl) ⟨681677, by rfl⟩ : syracuseStep 908903 = 1363355) B1363355
theorem B909935 : Blo 603293 909935 := bstep (se 1 (by rfl) ⟨682451, by rfl⟩ : syracuseStep 909935 = 1364903) B1364903
theorem B8282989 : Blo 603293 8282989 := bstep (se 3 (by rfl) ⟨1553060, by rfl⟩ : syracuseStep 8282989 = 3106121) B3106121
theorem B2581739 : Blo 603293 2581739 := bstep (se 1 (by rfl) ⟨1936304, by rfl⟩ : syracuseStep 2581739 = 3872609) B3872609
theorem B18900499 : Blo 603293 18900499 := bstep (se 1 (by rfl) ⟨14175374, by rfl⟩ : syracuseStep 18900499 = 28350749) B28350749
theorem B2451073 : Blo 603293 2451073 := bstep (se 2 (by rfl) ⟨919152, by rfl⟩ : syracuseStep 2451073 = 1838305) B1838305
theorem B681727 : Blo 603293 681727 := bstep (se 1 (by rfl) ⟨511295, by rfl⟩ : syracuseStep 681727 = 1022591) B1022591
theorem B1107751 : Blo 603293 1107751 := bstep (se 1 (by rfl) ⟨830813, by rfl⟩ : syracuseStep 1107751 = 1661627) B1661627
theorem B681799 : Blo 603293 681799 := bstep (se 1 (by rfl) ⟨511349, by rfl⟩ : syracuseStep 681799 = 1022699) B1022699
theorem B681979 : Blo 603293 681979 := bstep (se 1 (by rfl) ⟨511484, by rfl⟩ : syracuseStep 681979 = 1022969) B1022969
theorem B682159 : Blo 603293 682159 := bstep (se 1 (by rfl) ⟨511619, by rfl⟩ : syracuseStep 682159 = 1023239) B1023239
theorem B30337283 : Blo 603293 30337283 := bstep (se 1 (by rfl) ⟨22752962, by rfl⟩ : syracuseStep 30337283 = 45505925) B45505925
theorem B682663 : Blo 603293 682663 := bstep (se 1 (by rfl) ⟨511997, by rfl⟩ : syracuseStep 682663 = 1023995) B1023995
theorem B2485073 : Blo 603293 2485073 := bstep (se 2 (by rfl) ⟨931902, by rfl⟩ : syracuseStep 2485073 = 1863805) B1863805
theorem B682951 : Blo 603293 682951 := bstep (se 1 (by rfl) ⟨512213, by rfl⟩ : syracuseStep 682951 = 1024427) B1024427
theorem B2616563 : Blo 603293 2616563 := bstep (se 1 (by rfl) ⟨1962422, by rfl⟩ : syracuseStep 2616563 = 3924845) B3924845
theorem B14708567 : Blo 603293 14708567 := bstep (se 1 (by rfl) ⟨11031425, by rfl⟩ : syracuseStep 14708567 = 22062851) B22062851
theorem B2387999 : Blo 603293 2387999 := bstep (se 1 (by rfl) ⟨1790999, by rfl⟩ : syracuseStep 2387999 = 3581999) B3581999
theorem B11760191 : Blo 603293 11760191 := bstep (se 1 (by rfl) ⟨8820143, by rfl⟩ : syracuseStep 11760191 = 17640287) B17640287
theorem B2552639 : Blo 603293 2552639 := bstep (se 1 (by rfl) ⟨1914479, by rfl⟩ : syracuseStep 2552639 = 3828959) B3828959
theorem B18674657 : Blo 603293 18674657 := bstep (se 2 (by rfl) ⟨7002996, by rfl⟩ : syracuseStep 18674657 = 14005993) B14005993
theorem B9794753 : Blo 603293 9794753 := bstep (se 2 (by rfl) ⟨3673032, by rfl⟩ : syracuseStep 9794753 = 7346065) B7346065
theorem B16513217 : Blo 603293 16513217 := bstep (se 2 (by rfl) ⟨6192456, by rfl⟩ : syracuseStep 16513217 = 12384913) B12384913
theorem B2914663 : Blo 603293 2914663 := bstep (se 1 (by rfl) ⟨2185997, by rfl⟩ : syracuseStep 2914663 = 4371995) B4371995
theorem B817511 : Blo 603293 817511 := bstep (se 1 (by rfl) ⟨613133, by rfl⟩ : syracuseStep 817511 = 1226267) B1226267
theorem B1145335 : Blo 603293 1145335 := bstep (se 1 (by rfl) ⟨859001, by rfl⟩ : syracuseStep 1145335 = 1718003) B1718003
theorem B7731935 : Blo 603293 7731935 := bstep (se 1 (by rfl) ⟨5798951, by rfl⟩ : syracuseStep 7731935 = 11597903) B11597903
theorem B1147135 : Blo 603293 1147135 := bstep (se 1 (by rfl) ⟨860351, by rfl⟩ : syracuseStep 1147135 = 1720703) B1720703
theorem B7766279 : Blo 603293 7766279 := bstep (se 1 (by rfl) ⟨5824709, by rfl⟩ : syracuseStep 7766279 = 11649419) B11649419
theorem B8749403 : Blo 603293 8749403 := bstep (se 1 (by rfl) ⟨6562052, by rfl⟩ : syracuseStep 8749403 = 13124105) B13124105
theorem B11043985 : Blo 603293 11043985 := bstep (se 2 (by rfl) ⟨4141494, by rfl⟩ : syracuseStep 11043985 = 8282989) B8282989
theorem B29820095 : Blo 603293 29820095 := bstep (se 1 (by rfl) ⟨22365071, by rfl⟩ : syracuseStep 29820095 = 44730143) B44730143
theorem B13075663 : Blo 603293 13075663 := bstep (se 1 (by rfl) ⟨9806747, by rfl⟩ : syracuseStep 13075663 = 19613495) B19613495
theorem B6915293 : Blo 603293 6915293 := bstep (se 3 (by rfl) ⟨1296617, by rfl⟩ : syracuseStep 6915293 = 2593235) B2593235
theorem B3442247 : Blo 603293 3442247 := bstep (se 1 (by rfl) ⟨2581685, by rfl⟩ : syracuseStep 3442247 = 5163371) B5163371
theorem B1967723 : Blo 603293 1967723 := bstep (se 1 (by rfl) ⟨1475792, by rfl⟩ : syracuseStep 1967723 = 2951585) B2951585
theorem B4261585 : Blo 603293 4261585 := bstep (se 2 (by rfl) ⟨1598094, by rfl⟩ : syracuseStep 4261585 = 3196189) B3196189
theorem B1640417 : Blo 603293 1640417 := bstep (se 2 (by rfl) ⟨615156, by rfl⟩ : syracuseStep 1640417 = 1230313) B1230313
theorem B25200665 : Blo 603293 25200665 := bstep (se 2 (by rfl) ⟨9450249, by rfl⟩ : syracuseStep 25200665 = 18900499) B18900499
theorem B1477001 : Blo 603293 1477001 := bstep (se 2 (by rfl) ⟨553875, by rfl⟩ : syracuseStep 1477001 = 1107751) B1107751
theorem B2296259 : Blo 603293 2296259 := bstep (se 1 (by rfl) ⟨1722194, by rfl⟩ : syracuseStep 2296259 = 3444389) B3444389
theorem B5181245 : Blo 603293 5181245 := bstep (se 3 (by rfl) ⟨971483, by rfl⟩ : syracuseStep 5181245 = 1942967) B1942967
theorem B1020647 : Blo 603293 1020647 := bstep (se 1 (by rfl) ⟨765485, by rfl⟩ : syracuseStep 1020647 = 1530971) B1530971
theorem B1151911 : Blo 603293 1151911 := bstep (se 1 (by rfl) ⟨863933, by rfl⟩ : syracuseStep 1151911 = 1727867) B1727867
theorem B1021673 : Blo 603293 1021673 := bstep (se 2 (by rfl) ⟨383127, by rfl⟩ : syracuseStep 1021673 = 766255) B766255
theorem B1382287 : Blo 603293 1382287 := bstep (se 1 (by rfl) ⟨1036715, by rfl⟩ : syracuseStep 1382287 = 2073431) B2073431
theorem B20191841 : Blo 603293 20191841 := bstep (se 2 (by rfl) ⟨7571940, by rfl⟩ : syracuseStep 20191841 = 15143881) B15143881
theorem B2038553 : Blo 603293 2038553 := bstep (se 2 (by rfl) ⟨764457, by rfl⟩ : syracuseStep 2038553 = 1528915) B1528915
theorem B20224855 : Blo 603293 20224855 := bstep (se 1 (by rfl) ⟨15168641, by rfl⟩ : syracuseStep 20224855 = 30337283) B30337283
theorem B3284071 : Blo 603293 3284071 := bstep (se 1 (by rfl) ⟨2463053, by rfl⟩ : syracuseStep 3284071 = 4926107) B4926107
theorem B6626861 : Blo 603293 6626861 := bstep (se 3 (by rfl) ⟨1242536, by rfl⟩ : syracuseStep 6626861 = 2485073) B2485073
theorem B9805711 : Blo 603293 9805711 := bstep (se 1 (by rfl) ⟨7354283, by rfl⟩ : syracuseStep 9805711 = 14708567) B14708567
theorem B4595615 : Blo 603293 4595615 := bstep (se 1 (by rfl) ⟨3446711, by rfl⟩ : syracuseStep 4595615 = 6893423) B6893423
theorem B2302121 : Blo 603293 2302121 := bstep (se 2 (by rfl) ⟨863295, by rfl⟩ : syracuseStep 2302121 = 1726591) B1726591
theorem B7840127 : Blo 603293 7840127 := bstep (se 1 (by rfl) ⟨5880095, by rfl⟩ : syracuseStep 7840127 = 11760191) B11760191
theorem B5186267 : Blo 603293 5186267 := bstep (se 1 (by rfl) ⟨3889700, by rfl⟩ : syracuseStep 5186267 = 7779401) B7779401
theorem B6529835 : Blo 603293 6529835 := bstep (se 1 (by rfl) ⟨4897376, by rfl⟩ : syracuseStep 6529835 = 9794753) B9794753
theorem B3875809 : Blo 603293 3875809 := bstep (se 2 (by rfl) ⟨1453428, by rfl⟩ : syracuseStep 3875809 = 2906857) B2906857
theorem B6563051 : Blo 603293 6563051 := bstep (se 1 (by rfl) ⟨4922288, by rfl⟩ : syracuseStep 6563051 = 9844577) B9844577
theorem B5154623 : Blo 603293 5154623 := bstep (se 1 (by rfl) ⟨3865967, by rfl⟩ : syracuseStep 5154623 = 7731935) B7731935
theorem B2042387 : Blo 603293 2042387 := bstep (se 1 (by rfl) ⟨1531790, by rfl⟩ : syracuseStep 2042387 = 3063581) B3063581
theorem B764635 : Blo 603293 764635 := bstep (se 1 (by rfl) ⟨573476, by rfl⟩ : syracuseStep 764635 = 1146953) B1146953
theorem B2042603 : Blo 603293 2042603 := bstep (se 1 (by rfl) ⟨1531952, by rfl⟩ : syracuseStep 2042603 = 3063905) B3063905
theorem B6367997 : Blo 603293 6367997 := bstep (se 3 (by rfl) ⟨1193999, by rfl⟩ : syracuseStep 6367997 = 2387999) B2387999
theorem B4599017 : Blo 603293 4599017 := bstep (se 2 (by rfl) ⟨1724631, by rfl⟩ : syracuseStep 4599017 = 3449263) B3449263
theorem B2305691 : Blo 603293 2305691 := bstep (se 1 (by rfl) ⟨1729268, by rfl⟩ : syracuseStep 2305691 = 3458537) B3458537
theorem B3059693 : Blo 603293 3059693 := bstep (se 3 (by rfl) ⟨573692, by rfl⟩ : syracuseStep 3059693 = 1147385) B1147385
theorem B3879191 : Blo 603293 3879191 := bstep (se 1 (by rfl) ⟨2909393, by rfl⟩ : syracuseStep 3879191 = 5818787) B5818787
theorem B2044331 : Blo 603293 2044331 := bstep (se 1 (by rfl) ⟨1533248, by rfl⟩ : syracuseStep 2044331 = 3066497) B3066497
theorem B12464875 : Blo 603293 12464875 := bstep (se 1 (by rfl) ⟨9348656, by rfl⟩ : syracuseStep 12464875 = 18697313) B18697313
theorem B766847 : Blo 603293 766847 := bstep (se 1 (by rfl) ⟨575135, by rfl⟩ : syracuseStep 766847 = 1150271) B1150271
theorem B23344037 : Blo 603293 23344037 := bstep (se 4 (by rfl) ⟨2188503, by rfl⟩ : syracuseStep 23344037 = 4377007) B4377007
theorem B6207151 : Blo 603293 6207151 := bstep (se 1 (by rfl) ⟨4655363, by rfl⟩ : syracuseStep 6207151 = 9310727) B9310727
theorem B2045735 : Blo 603293 2045735 := bstep (se 1 (by rfl) ⟨1534301, by rfl⟩ : syracuseStep 2045735 = 3068603) B3068603
theorem B604007 : Blo 603293 604007 := bstep (se 1 (by rfl) ⟨453005, by rfl⟩ : syracuseStep 604007 = 906011) B906011
theorem B1718459 : Blo 603293 1718459 := bstep (se 1 (by rfl) ⟨1288844, by rfl⟩ : syracuseStep 1718459 = 2577689) B2577689
theorem B604443 : Blo 603293 604443 := bstep (se 1 (by rfl) ⟨453332, by rfl⟩ : syracuseStep 604443 = 906665) B906665
theorem B604479 : Blo 603293 604479 := bstep (se 1 (by rfl) ⟨453359, by rfl⟩ : syracuseStep 604479 = 906719) B906719
theorem B1358315 : Blo 603293 1358315 := bstep (se 1 (by rfl) ⟨1018736, by rfl⟩ : syracuseStep 1358315 = 2037473) B2037473
theorem B1292927 : Blo 603293 1292927 := bstep (se 1 (by rfl) ⟨969695, by rfl⟩ : syracuseStep 1292927 = 1939391) B1939391
theorem B605211 : Blo 603293 605211 := bstep (se 1 (by rfl) ⟨453908, by rfl⟩ : syracuseStep 605211 = 907817) B907817
theorem B605287 : Blo 603293 605287 := bstep (se 1 (by rfl) ⟨453965, by rfl⟩ : syracuseStep 605287 = 907931) B907931
theorem B605503 : Blo 603293 605503 := bstep (se 1 (by rfl) ⟨454127, by rfl⟩ : syracuseStep 605503 = 908255) B908255
theorem B605543 : Blo 603293 605543 := bstep (se 1 (by rfl) ⟨454157, by rfl⟩ : syracuseStep 605543 = 908315) B908315
theorem B605935 : Blo 603293 605935 := bstep (se 1 (by rfl) ⟨454451, by rfl⟩ : syracuseStep 605935 = 908903) B908903
theorem B1359611 : Blo 603293 1359611 := bstep (se 1 (by rfl) ⟨1019708, by rfl⟩ : syracuseStep 1359611 = 2039417) B2039417
theorem B1359647 : Blo 603293 1359647 := bstep (se 1 (by rfl) ⟨1019735, by rfl⟩ : syracuseStep 1359647 = 2039471) B2039471
theorem B4603877 : Blo 603293 4603877 := bstep (se 4 (by rfl) ⟨431613, by rfl⟩ : syracuseStep 4603877 = 863227) B863227
theorem B1359935 : Blo 603293 1359935 := bstep (se 1 (by rfl) ⟨1019951, by rfl⟩ : syracuseStep 1359935 = 2039903) B2039903
theorem B1360223 : Blo 603293 1360223 := bstep (se 1 (by rfl) ⟨1020167, by rfl⟩ : syracuseStep 1360223 = 2040335) B2040335
theorem B606623 : Blo 603293 606623 := bstep (se 1 (by rfl) ⟨454967, by rfl⟩ : syracuseStep 606623 = 909935) B909935
theorem B1721159 : Blo 603293 1721159 := bstep (se 1 (by rfl) ⟨1290869, by rfl⟩ : syracuseStep 1721159 = 2581739) B2581739
theorem B2180029 : Blo 603293 2180029 := bstep (se 3 (by rfl) ⟨408755, by rfl⟩ : syracuseStep 2180029 = 817511) B817511
theorem B1360889 : Blo 603293 1360889 := bstep (se 2 (by rfl) ⟨510333, by rfl⟩ : syracuseStep 1360889 = 1020667) B1020667
theorem B1360943 : Blo 603293 1360943 := bstep (se 1 (by rfl) ⟨1020707, by rfl⟩ : syracuseStep 1360943 = 2041415) B2041415
theorem B1361033 : Blo 603293 1361033 := bstep (se 2 (by rfl) ⟨510387, by rfl⟩ : syracuseStep 1361033 = 1020775) B1020775
theorem B1361159 : Blo 603293 1361159 := bstep (se 1 (by rfl) ⟨1020869, by rfl⟩ : syracuseStep 1361159 = 2041739) B2041739
theorem B29476295 : Blo 603293 29476295 := bstep (se 1 (by rfl) ⟨22107221, by rfl⟩ : syracuseStep 29476295 = 44214443) B44214443
theorem B1296481 : Blo 603293 1296481 := bstep (se 2 (by rfl) ⟨486180, by rfl⟩ : syracuseStep 1296481 = 972361) B972361
theorem B3886217 : Blo 603293 3886217 := bstep (se 2 (by rfl) ⟨1457331, by rfl⟩ : syracuseStep 3886217 = 2914663) B2914663
theorem B1363247 : Blo 603293 1363247 := bstep (se 1 (by rfl) ⟨1022435, by rfl⟩ : syracuseStep 1363247 = 2044871) B2044871
theorem B1527113 : Blo 603293 1527113 := bstep (se 2 (by rfl) ⟨572667, by rfl⟩ : syracuseStep 1527113 = 1145335) B1145335
theorem B44092997 : Blo 603293 44092997 := bstep (se 4 (by rfl) ⟨4133718, by rfl⟩ : syracuseStep 44092997 = 8267437) B8267437
theorem B904991 : Blo 603293 904991 := bstep (se 1 (by rfl) ⟨678743, by rfl⟩ : syracuseStep 904991 = 1357487) B1357487
theorem B905399 : Blo 603293 905399 := bstep (se 1 (by rfl) ⟨679049, by rfl⟩ : syracuseStep 905399 = 1358099) B1358099
theorem B905423 : Blo 603293 905423 := bstep (se 1 (by rfl) ⟨679067, by rfl⟩ : syracuseStep 905423 = 1358135) B1358135
theorem B1364201 : Blo 603293 1364201 := bstep (se 2 (by rfl) ⟨511575, by rfl⟩ : syracuseStep 1364201 = 1023151) B1023151
theorem B905471 : Blo 603293 905471 := bstep (se 1 (by rfl) ⟨679103, by rfl⟩ : syracuseStep 905471 = 1358207) B1358207
theorem B1364327 : Blo 603293 1364327 := bstep (se 1 (by rfl) ⟨1023245, by rfl⟩ : syracuseStep 1364327 = 2046491) B2046491
theorem B1364471 : Blo 603293 1364471 := bstep (se 1 (by rfl) ⟨1023353, by rfl⟩ : syracuseStep 1364471 = 2046707) B2046707
theorem B971689 : Blo 603293 971689 := bstep (se 2 (by rfl) ⟨364383, by rfl⟩ : syracuseStep 971689 = 728767) B728767
theorem B906287 : Blo 603293 906287 := bstep (se 1 (by rfl) ⟨679715, by rfl⟩ : syracuseStep 906287 = 1359431) B1359431
theorem B907175 : Blo 603293 907175 := bstep (se 1 (by rfl) ⟨680381, by rfl⟩ : syracuseStep 907175 = 1360763) B1360763
theorem B1366199 : Blo 603293 1366199 := bstep (se 1 (by rfl) ⟨1024649, by rfl⟩ : syracuseStep 1366199 = 2049299) B2049299
theorem B15686075 : Blo 603293 15686075 := bstep (se 1 (by rfl) ⟨11764556, by rfl⟩ : syracuseStep 15686075 = 23529113) B23529113
theorem B908027 : Blo 603293 908027 := bstep (se 1 (by rfl) ⟨681020, by rfl⟩ : syracuseStep 908027 = 1362041) B1362041
theorem B678847 : Blo 603293 678847 := bstep (se 1 (by rfl) ⟨509135, by rfl⟩ : syracuseStep 678847 = 1018271) B1018271
theorem B5168123 : Blo 603293 5168123 := bstep (se 1 (by rfl) ⟨3876092, by rfl⟩ : syracuseStep 5168123 = 7752185) B7752185
theorem B908699 : Blo 603293 908699 := bstep (se 1 (by rfl) ⟨681524, by rfl⟩ : syracuseStep 908699 = 1363049) B1363049
theorem B15523325 : Blo 603293 15523325 := bstep (se 3 (by rfl) ⟨2910623, by rfl⟩ : syracuseStep 15523325 = 5821247) B5821247
theorem B3268097 : Blo 603293 3268097 := bstep (se 2 (by rfl) ⟨1225536, by rfl⟩ : syracuseStep 3268097 = 2451073) B2451073
theorem B908969 : Blo 603293 908969 := bstep (se 2 (by rfl) ⟨340863, by rfl⟩ : syracuseStep 908969 = 681727) B681727
theorem B909065 : Blo 603293 909065 := bstep (se 2 (by rfl) ⟨340899, by rfl⟩ : syracuseStep 909065 = 681799) B681799
theorem B909305 : Blo 603293 909305 := bstep (se 2 (by rfl) ⟨340989, by rfl⟩ : syracuseStep 909305 = 681979) B681979
theorem B909545 : Blo 603293 909545 := bstep (se 2 (by rfl) ⟨341079, by rfl⟩ : syracuseStep 909545 = 682159) B682159
theorem B680539 : Blo 603293 680539 := bstep (se 1 (by rfl) ⟨510404, by rfl⟩ : syracuseStep 680539 = 1020809) B1020809
theorem B3072815 : Blo 603293 3072815 := bstep (se 1 (by rfl) ⟨2304611, by rfl⟩ : syracuseStep 3072815 = 4609223) B4609223
theorem B910217 : Blo 603293 910217 := bstep (se 2 (by rfl) ⟨341331, by rfl⟩ : syracuseStep 910217 = 682663) B682663
theorem B7005209 : Blo 603293 7005209 := bstep (se 2 (by rfl) ⟨2626953, by rfl⟩ : syracuseStep 7005209 = 5253907) B5253907
theorem B910601 : Blo 603293 910601 := bstep (se 2 (by rfl) ⟨341475, by rfl⟩ : syracuseStep 910601 = 682951) B682951
theorem B910751 : Blo 603293 910751 := bstep (se 1 (by rfl) ⟨683063, by rfl⟩ : syracuseStep 910751 = 1366127) B1366127
theorem B2909627 : Blo 603293 2909627 := bstep (se 1 (by rfl) ⟨2182220, by rfl⟩ : syracuseStep 2909627 = 4364441) B4364441
theorem B3106367 : Blo 603293 3106367 := bstep (se 1 (by rfl) ⟨2329775, by rfl⟩ : syracuseStep 3106367 = 4659551) B4659551
theorem B1534697 : Blo 603293 1534697 := bstep (se 2 (by rfl) ⟨575511, by rfl⟩ : syracuseStep 1534697 = 1151023) B1151023
theorem B1534889 : Blo 603293 1534889 := bstep (se 2 (by rfl) ⟨575583, by rfl⟩ : syracuseStep 1534889 = 1151167) B1151167
theorem B7367867 : Blo 603293 7367867 := bstep (se 1 (by rfl) ⟨5525900, by rfl⟩ : syracuseStep 7367867 = 11051801) B11051801
theorem B3435959 : Blo 603293 3435959 := bstep (se 1 (by rfl) ⟨2576969, by rfl⟩ : syracuseStep 3435959 = 5153939) B5153939
theorem B1535719 : Blo 603293 1535719 := bstep (se 1 (by rfl) ⟨1151789, by rfl⟩ : syracuseStep 1535719 = 2303579) B2303579
theorem B2584487 : Blo 603293 2584487 := bstep (se 1 (by rfl) ⟨1938365, by rfl⟩ : syracuseStep 2584487 = 3876731) B3876731
theorem B6221933 : Blo 603293 6221933 := bstep (se 3 (by rfl) ⟨1166612, by rfl⟩ : syracuseStep 6221933 = 2333225) B2333225
theorem B4354235 : Blo 603293 4354235 := bstep (se 1 (by rfl) ⟨3265676, by rfl⟩ : syracuseStep 4354235 = 6531353) B6531353
theorem B2453753 : Blo 603293 2453753 := bstep (se 2 (by rfl) ⟨920157, by rfl⟩ : syracuseStep 2453753 = 1840315) B1840315
theorem B10318265 : Blo 603293 10318265 := bstep (se 2 (by rfl) ⟨3869349, by rfl⟩ : syracuseStep 10318265 = 7738699) B7738699
theorem B3437417 : Blo 603293 3437417 := bstep (se 2 (by rfl) ⟨1289031, by rfl⟩ : syracuseStep 3437417 = 2578063) B2578063
theorem B6977501 : Blo 603293 6977501 := bstep (se 3 (by rfl) ⟨1308281, by rfl⟩ : syracuseStep 6977501 = 2616563) B2616563
theorem B12449771 : Blo 603293 12449771 := bstep (se 1 (by rfl) ⟨9337328, by rfl⟩ : syracuseStep 12449771 = 18674657) B18674657
theorem B27228149 : Blo 603293 27228149 := bstep (se 5 (by rfl) ⟨1276319, by rfl⟩ : syracuseStep 27228149 = 2552639) B2552639
theorem B11008811 : Blo 603293 11008811 := bstep (se 1 (by rfl) ⟨8256608, by rfl⟩ : syracuseStep 11008811 = 16513217) B16513217
theorem B5177519 : Blo 603293 5177519 := bstep (se 1 (by rfl) ⟨3883139, by rfl⟩ : syracuseStep 5177519 = 7766279) B7766279
theorem B5832935 : Blo 603293 5832935 := bstep (se 1 (by rfl) ⟨4374701, by rfl⟩ : syracuseStep 5832935 = 8749403) B8749403
theorem B1147439 : Blo 603293 1147439 := bstep (se 1 (by rfl) ⟨860579, by rfl⟩ : syracuseStep 1147439 = 1721159) B1721159
theorem B2294831 : Blo 603293 2294831 := bstep (se 1 (by rfl) ⟨1721123, by rfl⟩ : syracuseStep 2294831 = 3442247) B3442247
theorem B1311815 : Blo 603293 1311815 := bstep (se 1 (by rfl) ⟨983861, by rfl⟩ : syracuseStep 1311815 = 1967723) B1967723
theorem B17434217 : Blo 603293 17434217 := bstep (se 2 (by rfl) ⟨6537831, by rfl⟩ : syracuseStep 17434217 = 13075663) B13075663
theorem B2590811 : Blo 603293 2590811 := bstep (se 1 (by rfl) ⟨1943108, by rfl⟩ : syracuseStep 2590811 = 3886217) B3886217
theorem B1018075 : Blo 603293 1018075 := bstep (se 1 (by rfl) ⟨763556, by rfl⟩ : syracuseStep 1018075 = 1527113) B1527113
theorem B29395331 : Blo 603293 29395331 := bstep (se 1 (by rfl) ⟨22046498, by rfl⟩ : syracuseStep 29395331 = 44092997) B44092997
theorem B18680557 : Blo 603293 18680557 := bstep (se 3 (by rfl) ⟨3502604, by rfl⟩ : syracuseStep 18680557 = 7005209) B7005209
theorem B1019513 : Blo 603293 1019513 := bstep (se 2 (by rfl) ⟨382317, by rfl⟩ : syracuseStep 1019513 = 764635) B764635
theorem B3445415 : Blo 603293 3445415 := bstep (se 1 (by rfl) ⟨2584061, by rfl⟩ : syracuseStep 3445415 = 5168123) B5168123
theorem B1939751 : Blo 603293 1939751 := bstep (se 1 (by rfl) ⟨1454813, by rfl⟩ : syracuseStep 1939751 = 2909627) B2909627
theorem B16619833 : Blo 603293 16619833 := bstep (se 2 (by rfl) ⟨6232437, by rfl⟩ : syracuseStep 16619833 = 12464875) B12464875
theorem B3938669 : Blo 603293 3938669 := bstep (se 3 (by rfl) ⟨738500, by rfl⟩ : syracuseStep 3938669 = 1477001) B1477001
theorem B2070911 : Blo 603293 2070911 := bstep (se 1 (by rfl) ⟨1553183, by rfl⟩ : syracuseStep 2070911 = 3106367) B3106367
theorem B3447805 : Blo 603293 3447805 := bstep (se 3 (by rfl) ⟨646463, by rfl⟩ : syracuseStep 3447805 = 1292927) B1292927
theorem B1023131 : Blo 603293 1023131 := bstep (se 1 (by rfl) ⟨767348, by rfl⟩ : syracuseStep 1023131 = 1534697) B1534697
theorem B1023259 : Blo 603293 1023259 := bstep (se 1 (by rfl) ⟨767444, by rfl⟩ : syracuseStep 1023259 = 1534889) B1534889
theorem B16981325 : Blo 603293 16981325 := bstep (se 3 (by rfl) ⟨3183998, by rfl⟩ : syracuseStep 16981325 = 6367997) B6367997
theorem B1843049 : Blo 603293 1843049 := bstep (se 2 (by rfl) ⟨691143, by rfl⟩ : syracuseStep 1843049 = 1382287) B1382287
theorem B2039795 : Blo 603293 2039795 := bstep (se 1 (by rfl) ⟨1529846, by rfl⟩ : syracuseStep 2039795 = 3059693) B3059693
theorem B8299847 : Blo 603293 8299847 := bstep (se 1 (by rfl) ⟨6224885, by rfl⟩ : syracuseStep 8299847 = 12449771) B12449771
theorem B6891965 : Blo 603293 6891965 := bstep (se 3 (by rfl) ⟨1292243, by rfl⟩ : syracuseStep 6891965 = 2584487) B2584487
theorem B14725313 : Blo 603293 14725313 := bstep (se 2 (by rfl) ⟨5521992, by rfl⟩ : syracuseStep 14725313 = 11043985) B11043985
theorem B17412893 : Blo 603293 17412893 := bstep (se 3 (by rfl) ⟨3264917, by rfl⟩ : syracuseStep 17412893 = 6529835) B6529835
theorem B5682113 : Blo 603293 5682113 := bstep (se 2 (by rfl) ⟨2130792, by rfl⟩ : syracuseStep 5682113 = 4261585) B4261585
theorem B2044925 : Blo 603293 2044925 := bstep (se 3 (by rfl) ⟨383423, by rfl⟩ : syracuseStep 2044925 = 766847) B766847
theorem B603327 : Blo 603293 603327 := bstep (se 1 (by rfl) ⟨452495, by rfl⟩ : syracuseStep 603327 = 904991) B904991
theorem B3454163 : Blo 603293 3454163 := bstep (se 1 (by rfl) ⟨2590622, by rfl⟩ : syracuseStep 3454163 = 5181245) B5181245
theorem B603599 : Blo 603293 603599 := bstep (se 1 (by rfl) ⟨452699, by rfl⟩ : syracuseStep 603599 = 905399) B905399
theorem B603615 : Blo 603293 603615 := bstep (se 1 (by rfl) ⟨452711, by rfl⟩ : syracuseStep 603615 = 905423) B905423
theorem B603647 : Blo 603293 603647 := bstep (se 1 (by rfl) ⟨452735, by rfl⟩ : syracuseStep 603647 = 905471) B905471
theorem B604191 : Blo 603293 604191 := bstep (se 1 (by rfl) ⟨453143, by rfl⟩ : syracuseStep 604191 = 906287) B906287
theorem B604783 : Blo 603293 604783 := bstep (se 1 (by rfl) ⟨453587, by rfl⟩ : syracuseStep 604783 = 907175) B907175
theorem B605351 : Blo 603293 605351 := bstep (se 1 (by rfl) ⟨454013, by rfl⟩ : syracuseStep 605351 = 908027) B908027
theorem B1359035 : Blo 603293 1359035 := bstep (se 1 (by rfl) ⟨1019276, by rfl⟩ : syracuseStep 1359035 = 2038553) B2038553
theorem B605799 : Blo 603293 605799 := bstep (se 1 (by rfl) ⟨454349, by rfl⟩ : syracuseStep 605799 = 908699) B908699
theorem B2047625 : Blo 603293 2047625 := bstep (se 2 (by rfl) ⟨767859, by rfl⟩ : syracuseStep 2047625 = 1535719) B1535719
theorem B2178731 : Blo 603293 2178731 := bstep (se 1 (by rfl) ⟨1634048, by rfl⟩ : syracuseStep 2178731 = 3268097) B3268097
theorem B605979 : Blo 603293 605979 := bstep (se 1 (by rfl) ⟨454484, by rfl⟩ : syracuseStep 605979 = 908969) B908969
theorem B606043 : Blo 603293 606043 := bstep (se 1 (by rfl) ⟨454532, by rfl⟩ : syracuseStep 606043 = 909065) B909065
theorem B4374445 : Blo 603293 4374445 := bstep (se 3 (by rfl) ⟨820208, by rfl⟩ : syracuseStep 4374445 = 1640417) B1640417
theorem B3063743 : Blo 603293 3063743 := bstep (se 1 (by rfl) ⟨2297807, by rfl⟩ : syracuseStep 3063743 = 4595615) B4595615
theorem B606203 : Blo 603293 606203 := bstep (se 1 (by rfl) ⟨454652, by rfl⟩ : syracuseStep 606203 = 909305) B909305
theorem B606363 : Blo 603293 606363 := bstep (se 1 (by rfl) ⟨454772, by rfl⟩ : syracuseStep 606363 = 909545) B909545
theorem B5226751 : Blo 603293 5226751 := bstep (se 1 (by rfl) ⟨3920063, by rfl⟩ : syracuseStep 5226751 = 7840127) B7840127
theorem B3457511 : Blo 603293 3457511 := bstep (se 1 (by rfl) ⟨2593133, by rfl⟩ : syracuseStep 3457511 = 5186267) B5186267
theorem B2048543 : Blo 603293 2048543 := bstep (se 1 (by rfl) ⟨1536407, by rfl⟩ : syracuseStep 2048543 = 3072815) B3072815
theorem B17515045 : Blo 603293 17515045 := bstep (se 4 (by rfl) ⟨1642035, by rfl⟩ : syracuseStep 17515045 = 3284071) B3284071
theorem B606811 : Blo 603293 606811 := bstep (se 1 (by rfl) ⟨455108, by rfl⟩ : syracuseStep 606811 = 910217) B910217
theorem B4375367 : Blo 603293 4375367 := bstep (se 1 (by rfl) ⟨3281525, by rfl⟩ : syracuseStep 4375367 = 6563051) B6563051
theorem B607067 : Blo 603293 607067 := bstep (se 1 (by rfl) ⟨455300, by rfl⟩ : syracuseStep 607067 = 910601) B910601
theorem B607167 : Blo 603293 607167 := bstep (se 1 (by rfl) ⟨455375, by rfl⟩ : syracuseStep 607167 = 910751) B910751
theorem B41829533 : Blo 603293 41829533 := bstep (se 3 (by rfl) ⟨7843037, by rfl⟩ : syracuseStep 41829533 = 15686075) B15686075
theorem B1295585 : Blo 603293 1295585 := bstep (se 2 (by rfl) ⟨485844, by rfl⟩ : syracuseStep 1295585 = 971689) B971689
theorem B1361591 : Blo 603293 1361591 := bstep (se 1 (by rfl) ⟨1021193, by rfl⟩ : syracuseStep 1361591 = 2042387) B2042387
theorem B1361735 : Blo 603293 1361735 := bstep (se 1 (by rfl) ⟨1021301, by rfl⟩ : syracuseStep 1361735 = 2042603) B2042603
theorem B3066011 : Blo 603293 3066011 := bstep (se 1 (by rfl) ⟨2299508, by rfl⟩ : syracuseStep 3066011 = 4599017) B4599017
theorem B8276201 : Blo 603293 8276201 := bstep (se 2 (by rfl) ⟨3103575, by rfl⟩ : syracuseStep 8276201 = 6207151) B6207151
theorem B4147955 : Blo 603293 4147955 := bstep (se 1 (by rfl) ⟨3110966, by rfl⟩ : syracuseStep 4147955 = 6221933) B6221933
theorem B2902823 : Blo 603293 2902823 := bstep (se 1 (by rfl) ⟨2177117, by rfl⟩ : syracuseStep 2902823 = 4354235) B4354235
theorem B1362887 : Blo 603293 1362887 := bstep (se 1 (by rfl) ⟨1022165, by rfl⟩ : syracuseStep 1362887 = 2044331) B2044331
theorem B1363823 : Blo 603293 1363823 := bstep (se 1 (by rfl) ⟨1022867, by rfl⟩ : syracuseStep 1363823 = 2045735) B2045735
theorem B905129 : Blo 603293 905129 := bstep (se 2 (by rfl) ⟨339423, by rfl⟩ : syracuseStep 905129 = 678847) B678847
theorem B905543 : Blo 603293 905543 := bstep (se 1 (by rfl) ⟨679157, by rfl⟩ : syracuseStep 905543 = 1358315) B1358315
theorem B906407 : Blo 603293 906407 := bstep (se 1 (by rfl) ⟨679805, by rfl⟩ : syracuseStep 906407 = 1359611) B1359611
theorem B906431 : Blo 603293 906431 := bstep (se 1 (by rfl) ⟨679823, by rfl⟩ : syracuseStep 906431 = 1359647) B1359647
theorem B3069251 : Blo 603293 3069251 := bstep (se 1 (by rfl) ⟨2301938, by rfl⟩ : syracuseStep 3069251 = 4603877) B4603877
theorem B906623 : Blo 603293 906623 := bstep (se 1 (by rfl) ⟨679967, by rfl⟩ : syracuseStep 906623 = 1359935) B1359935
theorem B906815 : Blo 603293 906815 := bstep (se 1 (by rfl) ⟨680111, by rfl⟩ : syracuseStep 906815 = 1360223) B1360223
theorem B1529513 : Blo 603293 1529513 := bstep (se 2 (by rfl) ⟨573567, by rfl⟩ : syracuseStep 1529513 = 1147135) B1147135
theorem B907259 : Blo 603293 907259 := bstep (se 1 (by rfl) ⟨680444, by rfl⟩ : syracuseStep 907259 = 1360889) B1360889
theorem B907295 : Blo 603293 907295 := bstep (se 1 (by rfl) ⟨680471, by rfl⟩ : syracuseStep 907295 = 1360943) B1360943
theorem B10344509 : Blo 603293 10344509 := bstep (se 3 (by rfl) ⟨1939595, by rfl⟩ : syracuseStep 10344509 = 3879191) B3879191
theorem B907355 : Blo 603293 907355 := bstep (se 1 (by rfl) ⟨680516, by rfl⟩ : syracuseStep 907355 = 1361033) B1361033
theorem B907385 : Blo 603293 907385 := bstep (se 2 (by rfl) ⟨340269, by rfl⟩ : syracuseStep 907385 = 680539) B680539
theorem B19880063 : Blo 603293 19880063 := bstep (se 1 (by rfl) ⟨14910047, by rfl⟩ : syracuseStep 19880063 = 29820095) B29820095
theorem B4610195 : Blo 603293 4610195 := bstep (se 1 (by rfl) ⟨3457646, by rfl⟩ : syracuseStep 4610195 = 6915293) B6915293
theorem B907439 : Blo 603293 907439 := bstep (se 1 (by rfl) ⟨680579, by rfl⟩ : syracuseStep 907439 = 1361159) B1361159
theorem B19650863 : Blo 603293 19650863 := bstep (se 1 (by rfl) ⟨14738147, by rfl⟩ : syracuseStep 19650863 = 29476295) B29476295
theorem B2906705 : Blo 603293 2906705 := bstep (se 2 (by rfl) ⟨1090014, by rfl⟩ : syracuseStep 2906705 = 2180029) B2180029
theorem B5167745 : Blo 603293 5167745 := bstep (se 2 (by rfl) ⟨1937904, by rfl⟩ : syracuseStep 5167745 = 3875809) B3875809
theorem B16800443 : Blo 603293 16800443 := bstep (se 1 (by rfl) ⟨12600332, by rfl⟩ : syracuseStep 16800443 = 25200665) B25200665
theorem B1530839 : Blo 603293 1530839 := bstep (se 1 (by rfl) ⟨1148129, by rfl⟩ : syracuseStep 1530839 = 2296259) B2296259
theorem B908831 : Blo 603293 908831 := bstep (se 1 (by rfl) ⟨681623, by rfl⟩ : syracuseStep 908831 = 1363247) B1363247
theorem B1728641 : Blo 603293 1728641 := bstep (se 2 (by rfl) ⟨648240, by rfl⟩ : syracuseStep 1728641 = 1296481) B1296481
theorem B909467 : Blo 603293 909467 := bstep (se 1 (by rfl) ⟨682100, by rfl⟩ : syracuseStep 909467 = 1364201) B1364201
theorem B909551 : Blo 603293 909551 := bstep (se 1 (by rfl) ⟨682163, by rfl⟩ : syracuseStep 909551 = 1364327) B1364327
theorem B909647 : Blo 603293 909647 := bstep (se 1 (by rfl) ⟨682235, by rfl⟩ : syracuseStep 909647 = 1364471) B1364471
theorem B680431 : Blo 603293 680431 := bstep (se 1 (by rfl) ⟨510323, by rfl⟩ : syracuseStep 680431 = 1020647) B1020647
theorem B681115 : Blo 603293 681115 := bstep (se 1 (by rfl) ⟨510836, by rfl⟩ : syracuseStep 681115 = 1021673) B1021673
theorem B910799 : Blo 603293 910799 := bstep (se 1 (by rfl) ⟨683099, by rfl⟩ : syracuseStep 910799 = 1366199) B1366199
theorem B13461227 : Blo 603293 13461227 := bstep (se 1 (by rfl) ⟨10095920, by rfl⟩ : syracuseStep 13461227 = 20191841) B20191841
theorem B107865893 : Blo 603293 107865893 := bstep (se 4 (by rfl) ⟨10112427, by rfl⟩ : syracuseStep 107865893 = 20224855) B20224855
theorem B10348883 : Blo 603293 10348883 := bstep (se 1 (by rfl) ⟨7761662, by rfl⟩ : syracuseStep 10348883 = 15523325) B15523325
theorem B4417907 : Blo 603293 4417907 := bstep (se 1 (by rfl) ⟨3313430, by rfl⟩ : syracuseStep 4417907 = 6626861) B6626861
theorem B1534747 : Blo 603293 1534747 := bstep (se 1 (by rfl) ⟨1151060, by rfl⟩ : syracuseStep 1534747 = 2302121) B2302121
theorem B3436415 : Blo 603293 3436415 := bstep (se 1 (by rfl) ⟨2577311, by rfl⟩ : syracuseStep 3436415 = 5154623) B5154623
theorem B1535881 : Blo 603293 1535881 := bstep (se 2 (by rfl) ⟨575955, by rfl⟩ : syracuseStep 1535881 = 1151911) B1151911
theorem B4911911 : Blo 603293 4911911 := bstep (se 1 (by rfl) ⟨3683933, by rfl⟩ : syracuseStep 4911911 = 7367867) B7367867
theorem B2290639 : Blo 603293 2290639 := bstep (se 1 (by rfl) ⟨1717979, by rfl⟩ : syracuseStep 2290639 = 3435959) B3435959
theorem B1537127 : Blo 603293 1537127 := bstep (se 1 (by rfl) ⟨1152845, by rfl⟩ : syracuseStep 1537127 = 2305691) B2305691
theorem B1635835 : Blo 603293 1635835 := bstep (se 1 (by rfl) ⟨1226876, by rfl⟩ : syracuseStep 1635835 = 2453753) B2453753
theorem B6878843 : Blo 603293 6878843 := bstep (se 1 (by rfl) ⟨5159132, by rfl⟩ : syracuseStep 6878843 = 10318265) B10318265
theorem B2291611 : Blo 603293 2291611 := bstep (se 1 (by rfl) ⟨1718708, by rfl⟩ : syracuseStep 2291611 = 3437417) B3437417
theorem B15562691 : Blo 603293 15562691 := bstep (se 1 (by rfl) ⟨11672018, by rfl⟩ : syracuseStep 15562691 = 23344037) B23344037
theorem B4651667 : Blo 603293 4651667 := bstep (se 1 (by rfl) ⟨3488750, by rfl⟩ : syracuseStep 4651667 = 6977501) B6977501
theorem B18152099 : Blo 603293 18152099 := bstep (se 1 (by rfl) ⟨13614074, by rfl⟩ : syracuseStep 18152099 = 27228149) B27228149
theorem B1145639 : Blo 603293 1145639 := bstep (se 1 (by rfl) ⟨859229, by rfl⟩ : syracuseStep 1145639 = 1718459) B1718459
theorem B7339207 : Blo 603293 7339207 := bstep (se 1 (by rfl) ⟨5504405, by rfl⟩ : syracuseStep 7339207 = 11008811) B11008811
theorem B13074281 : Blo 603293 13074281 := bstep (se 2 (by rfl) ⟨4902855, by rfl⟩ : syracuseStep 13074281 = 9805711) B9805711
theorem B2916911 : Blo 603293 2916911 := bstep (se 1 (by rfl) ⟨2187683, by rfl⟩ : syracuseStep 2916911 = 4375367) B4375367
theorem B27886355 : Blo 603293 27886355 := bstep (se 1 (by rfl) ⟨20914766, by rfl⟩ : syracuseStep 27886355 = 41829533) B41829533
theorem B19596887 : Blo 603293 19596887 := bstep (se 1 (by rfl) ⟨14697665, by rfl⟩ : syracuseStep 19596887 = 29395331) B29395331
theorem B1935215 : Blo 603293 1935215 := bstep (se 1 (by rfl) ⟨1451411, by rfl⟩ : syracuseStep 1935215 = 2902823) B2902823
theorem B2296943 : Blo 603293 2296943 := bstep (se 1 (by rfl) ⟨1722707, by rfl⟩ : syracuseStep 2296943 = 3445415) B3445415
theorem B24907409 : Blo 603293 24907409 := bstep (se 2 (by rfl) ⟨9340278, by rfl⟩ : syracuseStep 24907409 = 18680557) B18680557
theorem B1019675 : Blo 603293 1019675 := bstep (se 1 (by rfl) ⟨764756, by rfl⟩ : syracuseStep 1019675 = 1529513) B1529513
theorem B2625779 : Blo 603293 2625779 := bstep (se 1 (by rfl) ⟨1969334, by rfl⟩ : syracuseStep 2625779 = 3938669) B3938669
theorem B1380607 : Blo 603293 1380607 := bstep (se 1 (by rfl) ⟨1035455, by rfl⟩ : syracuseStep 1380607 = 2070911) B2070911
theorem B1937803 : Blo 603293 1937803 := bstep (se 1 (by rfl) ⟨1453352, by rfl⟩ : syracuseStep 1937803 = 2906705) B2906705
theorem B3445163 : Blo 603293 3445163 := bstep (se 1 (by rfl) ⟨2583872, by rfl⟩ : syracuseStep 3445163 = 5167745) B5167745
theorem B1020559 : Blo 603293 1020559 := bstep (se 1 (by rfl) ⟨765419, by rfl⟩ : syracuseStep 1020559 = 1530839) B1530839
theorem B3054185 : Blo 603293 3054185 := bstep (se 2 (by rfl) ⟨1145319, by rfl⟩ : syracuseStep 3054185 = 2290639) B2290639
theorem B4594643 : Blo 603293 4594643 := bstep (se 1 (by rfl) ⟨3445982, by rfl⟩ : syracuseStep 4594643 = 6891965) B6891965
theorem B3055481 : Blo 603293 3055481 := bstep (se 2 (by rfl) ⟨1145805, by rfl⟩ : syracuseStep 3055481 = 2291611) B2291611
theorem B22159777 : Blo 603293 22159777 := bstep (se 2 (by rfl) ⟨8309916, by rfl⟩ : syracuseStep 22159777 = 16619833) B16619833
theorem B11608595 : Blo 603293 11608595 := bstep (se 1 (by rfl) ⟨8706446, by rfl⟩ : syracuseStep 11608595 = 17412893) B17412893
theorem B1024751 : Blo 603293 1024751 := bstep (se 1 (by rfl) ⟨768563, by rfl⟩ : syracuseStep 1024751 = 1537127) B1537127
theorem B2302775 : Blo 603293 2302775 := bstep (se 1 (by rfl) ⟨1727081, by rfl⟩ : syracuseStep 2302775 = 3454163) B3454163
theorem B4597073 : Blo 603293 4597073 := bstep (se 2 (by rfl) ⟨1723902, by rfl⟩ : syracuseStep 4597073 = 3447805) B3447805
theorem B12101399 : Blo 603293 12101399 := bstep (se 1 (by rfl) ⟨9076049, by rfl⟩ : syracuseStep 12101399 = 18152099) B18152099
theorem B763759 : Blo 603293 763759 := bstep (se 1 (by rfl) ⟨572819, by rfl⟩ : syracuseStep 763759 = 1145639) B1145639
theorem B1452487 : Blo 603293 1452487 := bstep (se 1 (by rfl) ⟨1089365, by rfl⟩ : syracuseStep 1452487 = 2178731) B2178731
theorem B2042495 : Blo 603293 2042495 := bstep (se 1 (by rfl) ⟨1531871, by rfl⟩ : syracuseStep 2042495 = 3063743) B3063743
theorem B3451679 : Blo 603293 3451679 := bstep (se 1 (by rfl) ⟨2588759, by rfl⟩ : syracuseStep 3451679 = 5177519) B5177519
theorem B2305007 : Blo 603293 2305007 := bstep (se 1 (by rfl) ⟨1728755, by rfl⟩ : syracuseStep 2305007 = 3457511) B3457511
theorem B764959 : Blo 603293 764959 := bstep (se 1 (by rfl) ⟨573719, by rfl⟩ : syracuseStep 764959 = 1147439) B1147439
theorem B863723 : Blo 603293 863723 := bstep (se 1 (by rfl) ⟨647792, by rfl⟩ : syracuseStep 863723 = 1295585) B1295585
theorem B2044007 : Blo 603293 2044007 := bstep (se 1 (by rfl) ⟨1533005, by rfl⟩ : syracuseStep 2044007 = 3066011) B3066011
theorem B5517467 : Blo 603293 5517467 := bstep (se 1 (by rfl) ⟨4138100, by rfl⟩ : syracuseStep 5517467 = 8276201) B8276201
theorem B2765303 : Blo 603293 2765303 := bstep (se 1 (by rfl) ⟨2073977, by rfl⟩ : syracuseStep 2765303 = 4147955) B4147955
theorem B603419 : Blo 603293 603419 := bstep (se 1 (by rfl) ⟨452564, by rfl⟩ : syracuseStep 603419 = 905129) B905129
theorem B603695 : Blo 603293 603695 := bstep (se 1 (by rfl) ⟨452771, by rfl⟩ : syracuseStep 603695 = 905543) B905543
theorem B1357433 : Blo 603293 1357433 := bstep (se 2 (by rfl) ⟨509037, by rfl⟩ : syracuseStep 1357433 = 1018075) B1018075
theorem B604271 : Blo 603293 604271 := bstep (se 1 (by rfl) ⟨453203, by rfl⟩ : syracuseStep 604271 = 906407) B906407
theorem B604287 : Blo 603293 604287 := bstep (se 1 (by rfl) ⟨453215, by rfl⟩ : syracuseStep 604287 = 906431) B906431
theorem B2046167 : Blo 603293 2046167 := bstep (se 1 (by rfl) ⟨1534625, by rfl⟩ : syracuseStep 2046167 = 3069251) B3069251
theorem B604415 : Blo 603293 604415 := bstep (se 1 (by rfl) ⟨453311, by rfl⟩ : syracuseStep 604415 = 906623) B906623
theorem B2046329 : Blo 603293 2046329 := bstep (se 2 (by rfl) ⟨767373, by rfl⟩ : syracuseStep 2046329 = 1534747) B1534747
theorem B604543 : Blo 603293 604543 := bstep (se 1 (by rfl) ⟨453407, by rfl⟩ : syracuseStep 604543 = 906815) B906815
theorem B604839 : Blo 603293 604839 := bstep (se 1 (by rfl) ⟨453629, by rfl⟩ : syracuseStep 604839 = 907259) B907259
theorem B604863 : Blo 603293 604863 := bstep (se 1 (by rfl) ⟨453647, by rfl⟩ : syracuseStep 604863 = 907295) B907295
theorem B6896339 : Blo 603293 6896339 := bstep (se 1 (by rfl) ⟨5172254, by rfl⟩ : syracuseStep 6896339 = 10344509) B10344509
theorem B604903 : Blo 603293 604903 := bstep (se 1 (by rfl) ⟨453677, by rfl⟩ : syracuseStep 604903 = 907355) B907355
theorem B604923 : Blo 603293 604923 := bstep (se 1 (by rfl) ⟨453692, by rfl⟩ : syracuseStep 604923 = 907385) B907385
theorem B13253375 : Blo 603293 13253375 := bstep (se 1 (by rfl) ⟨9940031, by rfl⟩ : syracuseStep 13253375 = 19880063) B19880063
theorem B604959 : Blo 603293 604959 := bstep (se 1 (by rfl) ⟨453719, by rfl⟩ : syracuseStep 604959 = 907439) B907439
theorem B1293167 : Blo 603293 1293167 := bstep (se 1 (by rfl) ⟨969875, by rfl⟩ : syracuseStep 1293167 = 1939751) B1939751
theorem B11320883 : Blo 603293 11320883 := bstep (se 1 (by rfl) ⟨8490662, by rfl⟩ : syracuseStep 11320883 = 16981325) B16981325
theorem B605887 : Blo 603293 605887 := bstep (se 1 (by rfl) ⟨454415, by rfl⟩ : syracuseStep 605887 = 908831) B908831
theorem B2047841 : Blo 603293 2047841 := bstep (se 2 (by rfl) ⟨767940, by rfl⟩ : syracuseStep 2047841 = 1535881) B1535881
theorem B1228699 : Blo 603293 1228699 := bstep (se 1 (by rfl) ⟨921524, by rfl⟩ : syracuseStep 1228699 = 1843049) B1843049
theorem B1359863 : Blo 603293 1359863 := bstep (se 1 (by rfl) ⟨1019897, by rfl⟩ : syracuseStep 1359863 = 2039795) B2039795
theorem B606311 : Blo 603293 606311 := bstep (se 1 (by rfl) ⟨454733, by rfl⟩ : syracuseStep 606311 = 909467) B909467
theorem B606367 : Blo 603293 606367 := bstep (se 1 (by rfl) ⟨454775, by rfl⟩ : syracuseStep 606367 = 909551) B909551
theorem B606431 : Blo 603293 606431 := bstep (se 1 (by rfl) ⟨454823, by rfl⟩ : syracuseStep 606431 = 909647) B909647
theorem B11781085 : Blo 603293 11781085 := bstep (se 3 (by rfl) ⟨2208953, by rfl⟩ : syracuseStep 11781085 = 4417907) B4417907
theorem B607199 : Blo 603293 607199 := bstep (se 1 (by rfl) ⟨455399, by rfl⟩ : syracuseStep 607199 = 910799) B910799
theorem B71910595 : Blo 603293 71910595 := bstep (se 1 (by rfl) ⟨53932946, by rfl⟩ : syracuseStep 71910595 = 107865893) B107865893
theorem B6899255 : Blo 603293 6899255 := bstep (se 1 (by rfl) ⟨5174441, by rfl⟩ : syracuseStep 6899255 = 10348883) B10348883
theorem B2181113 : Blo 603293 2181113 := bstep (se 2 (by rfl) ⟨817917, by rfl⟩ : syracuseStep 2181113 = 1635835) B1635835
theorem B9816875 : Blo 603293 9816875 := bstep (se 1 (by rfl) ⟨7362656, by rfl⟩ : syracuseStep 9816875 = 14725313) B14725313
theorem B3788075 : Blo 603293 3788075 := bstep (se 1 (by rfl) ⟨2841056, by rfl⟩ : syracuseStep 3788075 = 5682113) B5682113
theorem B1363283 : Blo 603293 1363283 := bstep (se 1 (by rfl) ⟨1022462, by rfl⟩ : syracuseStep 1363283 = 2044925) B2044925
theorem B10375127 : Blo 603293 10375127 := bstep (se 1 (by rfl) ⟨7781345, by rfl⟩ : syracuseStep 10375127 = 15562691) B15562691
theorem B9785609 : Blo 603293 9785609 := bstep (se 2 (by rfl) ⟨3669603, by rfl⟩ : syracuseStep 9785609 = 7339207) B7339207
theorem B1364345 : Blo 603293 1364345 := bstep (se 2 (by rfl) ⟨511629, by rfl⟩ : syracuseStep 1364345 = 1023259) B1023259
theorem B3101111 : Blo 603293 3101111 := bstep (se 1 (by rfl) ⟨2325833, by rfl⟩ : syracuseStep 3101111 = 4651667) B4651667
theorem B906023 : Blo 603293 906023 := bstep (se 1 (by rfl) ⟨679517, by rfl⟩ : syracuseStep 906023 = 1359035) B1359035
theorem B1365083 : Blo 603293 1365083 := bstep (se 1 (by rfl) ⟨1023812, by rfl⟩ : syracuseStep 1365083 = 2047625) B2047625
theorem B3888623 : Blo 603293 3888623 := bstep (se 1 (by rfl) ⟨2916467, by rfl⟩ : syracuseStep 3888623 = 5832935) B5832935
theorem B6969001 : Blo 603293 6969001 := bstep (se 2 (by rfl) ⟨2613375, by rfl⟩ : syracuseStep 6969001 = 5226751) B5226751
theorem B4609709 : Blo 603293 4609709 := bstep (se 3 (by rfl) ⟨864320, by rfl⟩ : syracuseStep 4609709 = 1728641) B1728641
theorem B1365695 : Blo 603293 1365695 := bstep (se 1 (by rfl) ⟨1024271, by rfl⟩ : syracuseStep 1365695 = 2048543) B2048543
theorem B907241 : Blo 603293 907241 := bstep (se 2 (by rfl) ⟨340215, by rfl⟩ : syracuseStep 907241 = 680431) B680431
theorem B1529887 : Blo 603293 1529887 := bstep (se 1 (by rfl) ⟨1147415, by rfl⟩ : syracuseStep 1529887 = 2294831) B2294831
theorem B11622811 : Blo 603293 11622811 := bstep (se 1 (by rfl) ⟨8717108, by rfl⟩ : syracuseStep 11622811 = 17434217) B17434217
theorem B907727 : Blo 603293 907727 := bstep (se 1 (by rfl) ⟨680795, by rfl⟩ : syracuseStep 907727 = 1361591) B1361591
theorem B907823 : Blo 603293 907823 := bstep (se 1 (by rfl) ⟨680867, by rfl⟩ : syracuseStep 907823 = 1361735) B1361735
theorem B1727207 : Blo 603293 1727207 := bstep (se 1 (by rfl) ⟨1295405, by rfl⟩ : syracuseStep 1727207 = 2590811) B2590811
theorem B908153 : Blo 603293 908153 := bstep (se 2 (by rfl) ⟨340557, by rfl⟩ : syracuseStep 908153 = 681115) B681115
theorem B908591 : Blo 603293 908591 := bstep (se 1 (by rfl) ⟨681443, by rfl⟩ : syracuseStep 908591 = 1362887) B1362887
theorem B679675 : Blo 603293 679675 := bstep (se 1 (by rfl) ⟨509756, by rfl⟩ : syracuseStep 679675 = 1019513) B1019513
theorem B909215 : Blo 603293 909215 := bstep (se 1 (by rfl) ⟨681911, by rfl⟩ : syracuseStep 909215 = 1363823) B1363823
theorem B3498173 : Blo 603293 3498173 := bstep (se 3 (by rfl) ⟨655907, by rfl⟩ : syracuseStep 3498173 = 1311815) B1311815
theorem B93413573 : Blo 603293 93413573 := bstep (se 4 (by rfl) ⟨8757522, by rfl⟩ : syracuseStep 93413573 = 17515045) B17515045
theorem B3073463 : Blo 603293 3073463 := bstep (se 1 (by rfl) ⟨2305097, by rfl⟩ : syracuseStep 3073463 = 4610195) B4610195
theorem B13100575 : Blo 603293 13100575 := bstep (se 1 (by rfl) ⟨9825431, by rfl⟩ : syracuseStep 13100575 = 19650863) B19650863
theorem B11200295 : Blo 603293 11200295 := bstep (se 1 (by rfl) ⟨8400221, by rfl⟩ : syracuseStep 11200295 = 16800443) B16800443
theorem B682087 : Blo 603293 682087 := bstep (se 1 (by rfl) ⟨511565, by rfl⟩ : syracuseStep 682087 = 1023131) B1023131
theorem B5533231 : Blo 603293 5533231 := bstep (se 1 (by rfl) ⟨4149923, by rfl⟩ : syracuseStep 5533231 = 8299847) B8299847
theorem B8974151 : Blo 603293 8974151 := bstep (se 1 (by rfl) ⟨6730613, by rfl⟩ : syracuseStep 8974151 = 13461227) B13461227
theorem B2290943 : Blo 603293 2290943 := bstep (se 1 (by rfl) ⟨1718207, by rfl⟩ : syracuseStep 2290943 = 3436415) B3436415
theorem B3274607 : Blo 603293 3274607 := bstep (se 1 (by rfl) ⟨2455955, by rfl⟩ : syracuseStep 3274607 = 4911911) B4911911
theorem B4585895 : Blo 603293 4585895 := bstep (se 1 (by rfl) ⟨3439421, by rfl⟩ : syracuseStep 4585895 = 6878843) B6878843
theorem B5832593 : Blo 603293 5832593 := bstep (se 2 (by rfl) ⟨2187222, by rfl⟩ : syracuseStep 5832593 = 4374445) B4374445
theorem B8716187 : Blo 603293 8716187 := bstep (se 1 (by rfl) ⟨6537140, by rfl⟩ : syracuseStep 8716187 = 13074281) B13074281
theorem B17467433 : Blo 603293 17467433 := bstep (se 2 (by rfl) ⟨6550287, by rfl⟩ : syracuseStep 17467433 = 13100575) B13100575
theorem B2525383 : Blo 603293 2525383 := bstep (se 1 (by rfl) ⟨1894037, by rfl⟩ : syracuseStep 2525383 = 3788075) B3788075
theorem B1018345 : Blo 603293 1018345 := bstep (se 2 (by rfl) ⟨381879, by rfl⟩ : syracuseStep 1018345 = 763759) B763759
theorem B6916751 : Blo 603293 6916751 := bstep (se 1 (by rfl) ⟨5187563, by rfl⟩ : syracuseStep 6916751 = 10375127) B10375127
theorem B6523739 : Blo 603293 6523739 := bstep (se 1 (by rfl) ⟨4892804, by rfl⟩ : syracuseStep 6523739 = 9785609) B9785609
theorem B2296775 : Blo 603293 2296775 := bstep (se 1 (by rfl) ⟨1722581, by rfl⟩ : syracuseStep 2296775 = 3445163) B3445163
theorem B2067407 : Blo 603293 2067407 := bstep (se 1 (by rfl) ⟨1550555, by rfl⟩ : syracuseStep 2067407 = 3101111) B3101111
theorem B1936649 : Blo 603293 1936649 := bstep (se 2 (by rfl) ⟨726243, by rfl⟩ : syracuseStep 1936649 = 1452487) B1452487
theorem B2592415 : Blo 603293 2592415 := bstep (se 1 (by rfl) ⟨1944311, by rfl⟩ : syracuseStep 2592415 = 3888623) B3888623
theorem B1019945 : Blo 603293 1019945 := bstep (se 2 (by rfl) ⟨382479, by rfl⟩ : syracuseStep 1019945 = 764959) B764959
theorem B2036123 : Blo 603293 2036123 := bstep (se 1 (by rfl) ⟨1527092, by rfl⟩ : syracuseStep 2036123 = 3054185) B3054185
theorem B1151471 : Blo 603293 1151471 := bstep (se 1 (by rfl) ⟨863603, by rfl⟩ : syracuseStep 1151471 = 1727207) B1727207
theorem B7377641 : Blo 603293 7377641 := bstep (se 2 (by rfl) ⟨2766615, by rfl⟩ : syracuseStep 7377641 = 5533231) B5533231
theorem B2036987 : Blo 603293 2036987 := bstep (se 1 (by rfl) ⟨1527740, by rfl⟩ : syracuseStep 2036987 = 3055481) B3055481
theorem B2332115 : Blo 603293 2332115 := bstep (se 1 (by rfl) ⟨1749086, by rfl⟩ : syracuseStep 2332115 = 3498173) B3498173
theorem B7739063 : Blo 603293 7739063 := bstep (se 1 (by rfl) ⟨5804297, by rfl⟩ : syracuseStep 7739063 = 11608595) B11608595
theorem B383523173 : Blo 603293 383523173 := bstep (se 4 (by rfl) ⟨35955297, by rfl⟩ : syracuseStep 383523173 = 71910595) B71910595
theorem B8067599 : Blo 603293 8067599 := bstep (se 1 (by rfl) ⟨6050699, by rfl⟩ : syracuseStep 8067599 = 12101399) B12101399
theorem B2301119 : Blo 603293 2301119 := bstep (se 1 (by rfl) ⟨1725839, by rfl⟩ : syracuseStep 2301119 = 3451679) B3451679
theorem B2039849 : Blo 603293 2039849 := bstep (se 2 (by rfl) ⟨764943, by rfl⟩ : syracuseStep 2039849 = 1529887) B1529887
theorem B3678311 : Blo 603293 3678311 := bstep (se 1 (by rfl) ⟨2758733, by rfl⟩ : syracuseStep 3678311 = 5517467) B5517467
theorem B1843535 : Blo 603293 1843535 := bstep (se 1 (by rfl) ⟨1382651, by rfl⟩ : syracuseStep 1843535 = 2765303) B2765303
theorem B2303261 : Blo 603293 2303261 := bstep (se 3 (by rfl) ⟨431861, by rfl⟩ : syracuseStep 2303261 = 863723) B863723
theorem B3057263 : Blo 603293 3057263 := bstep (se 1 (by rfl) ⟨2292947, by rfl⟩ : syracuseStep 3057263 = 4585895) B4585895
theorem B4597559 : Blo 603293 4597559 := bstep (se 1 (by rfl) ⟨3448169, by rfl⟩ : syracuseStep 4597559 = 6896339) B6896339
theorem B862111 : Blo 603293 862111 := bstep (se 1 (by rfl) ⟨646583, by rfl⟩ : syracuseStep 862111 = 1293167) B1293167
theorem B7547255 : Blo 603293 7547255 := bstep (se 1 (by rfl) ⟨5660441, by rfl⟩ : syracuseStep 7547255 = 11320883) B11320883
theorem B5810791 : Blo 603293 5810791 := bstep (se 1 (by rfl) ⟨4358093, by rfl⟩ : syracuseStep 5810791 = 8716187) B8716187
theorem B18590903 : Blo 603293 18590903 := bstep (se 1 (by rfl) ⟨13943177, by rfl⟩ : syracuseStep 18590903 = 27886355) B27886355
theorem B4599503 : Blo 603293 4599503 := bstep (se 1 (by rfl) ⟨3449627, by rfl⟩ : syracuseStep 4599503 = 6899255) B6899255
theorem B1290143 : Blo 603293 1290143 := bstep (se 1 (by rfl) ⟨967607, by rfl⟩ : syracuseStep 1290143 = 1935215) B1935215
theorem B15708113 : Blo 603293 15708113 := bstep (se 2 (by rfl) ⟨5890542, by rfl⟩ : syracuseStep 15708113 = 11781085) B11781085
theorem B1454075 : Blo 603293 1454075 := bstep (se 1 (by rfl) ⟨1090556, by rfl⟩ : syracuseStep 1454075 = 2181113) B2181113
theorem B7778429 : Blo 603293 7778429 := bstep (se 3 (by rfl) ⟨1458455, by rfl⟩ : syracuseStep 7778429 = 2916911) B2916911
theorem B1750519 : Blo 603293 1750519 := bstep (se 1 (by rfl) ⟨1312889, by rfl⟩ : syracuseStep 1750519 = 2625779) B2625779
theorem B604015 : Blo 603293 604015 := bstep (se 1 (by rfl) ⟨453011, by rfl⟩ : syracuseStep 604015 = 906023) B906023
theorem B604827 : Blo 603293 604827 := bstep (se 1 (by rfl) ⟨453620, by rfl⟩ : syracuseStep 604827 = 907241) B907241
theorem B605151 : Blo 603293 605151 := bstep (se 1 (by rfl) ⟨453863, by rfl⟩ : syracuseStep 605151 = 907727) B907727
theorem B605215 : Blo 603293 605215 := bstep (se 1 (by rfl) ⟨453911, by rfl⟩ : syracuseStep 605215 = 907823) B907823
theorem B605435 : Blo 603293 605435 := bstep (se 1 (by rfl) ⟨454076, by rfl⟩ : syracuseStep 605435 = 908153) B908153
theorem B3063095 : Blo 603293 3063095 := bstep (se 1 (by rfl) ⟨2297321, by rfl⟩ : syracuseStep 3063095 = 4594643) B4594643
theorem B605727 : Blo 603293 605727 := bstep (se 1 (by rfl) ⟨454295, by rfl⟩ : syracuseStep 605727 = 908591) B908591
theorem B606143 : Blo 603293 606143 := bstep (se 1 (by rfl) ⟨454607, by rfl⟩ : syracuseStep 606143 = 909215) B909215
theorem B62275715 : Blo 603293 62275715 := bstep (se 1 (by rfl) ⟨46706786, by rfl⟩ : syracuseStep 62275715 = 93413573) B93413573
theorem B1360745 : Blo 603293 1360745 := bstep (se 2 (by rfl) ⟨510279, by rfl⟩ : syracuseStep 1360745 = 1020559) B1020559
theorem B3064715 : Blo 603293 3064715 := bstep (se 1 (by rfl) ⟨2298536, by rfl⟩ : syracuseStep 3064715 = 4597073) B4597073
theorem B2048975 : Blo 603293 2048975 := bstep (se 1 (by rfl) ⟨1536731, by rfl⟩ : syracuseStep 2048975 = 3073463) B3073463
theorem B1361663 : Blo 603293 1361663 := bstep (se 1 (by rfl) ⟨1021247, by rfl⟩ : syracuseStep 1361663 = 2042495) B2042495
theorem B9292001 : Blo 603293 9292001 := bstep (se 2 (by rfl) ⟨3484500, by rfl⟩ : syracuseStep 9292001 = 6969001) B6969001
theorem B5982767 : Blo 603293 5982767 := bstep (se 1 (by rfl) ⟨4487075, by rfl⟩ : syracuseStep 5982767 = 8974151) B8974151
theorem B1362671 : Blo 603293 1362671 := bstep (se 1 (by rfl) ⟨1022003, by rfl⟩ : syracuseStep 1362671 = 2044007) B2044007
theorem B1527295 : Blo 603293 1527295 := bstep (se 1 (by rfl) ⟨1145471, by rfl⟩ : syracuseStep 1527295 = 2290943) B2290943
theorem B904955 : Blo 603293 904955 := bstep (se 1 (by rfl) ⟨678716, by rfl⟩ : syracuseStep 904955 = 1357433) B1357433
theorem B2183071 : Blo 603293 2183071 := bstep (se 1 (by rfl) ⟨1637303, by rfl⟩ : syracuseStep 2183071 = 3274607) B3274607
theorem B1364111 : Blo 603293 1364111 := bstep (se 1 (by rfl) ⟨1023083, by rfl⟩ : syracuseStep 1364111 = 2046167) B2046167
theorem B1364219 : Blo 603293 1364219 := bstep (se 1 (by rfl) ⟨1023164, by rfl⟩ : syracuseStep 1364219 = 2046329) B2046329
theorem B8835583 : Blo 603293 8835583 := bstep (se 1 (by rfl) ⟨6626687, by rfl⟩ : syracuseStep 8835583 = 13253375) B13253375
theorem B906233 : Blo 603293 906233 := bstep (se 2 (by rfl) ⟨339837, by rfl⟩ : syracuseStep 906233 = 679675) B679675
theorem B1365227 : Blo 603293 1365227 := bstep (se 1 (by rfl) ⟨1023920, by rfl⟩ : syracuseStep 1365227 = 2047841) B2047841
theorem B3888395 : Blo 603293 3888395 := bstep (se 1 (by rfl) ⟨2916296, by rfl⟩ : syracuseStep 3888395 = 5832593) B5832593
theorem B906575 : Blo 603293 906575 := bstep (se 1 (by rfl) ⟨679931, by rfl⟩ : syracuseStep 906575 = 1359863) B1359863
theorem B29546369 : Blo 603293 29546369 := bstep (se 2 (by rfl) ⟨11079888, by rfl⟩ : syracuseStep 29546369 = 22159777) B22159777
theorem B13064591 : Blo 603293 13064591 := bstep (se 1 (by rfl) ⟨9798443, by rfl⟩ : syracuseStep 13064591 = 19596887) B19596887
theorem B7363237 : Blo 603293 7363237 := bstep (se 4 (by rfl) ⟨690303, by rfl⟩ : syracuseStep 7363237 = 1380607) B1380607
theorem B6544583 : Blo 603293 6544583 := bstep (se 1 (by rfl) ⟨4908437, by rfl⟩ : syracuseStep 6544583 = 9816875) B9816875
theorem B1531295 : Blo 603293 1531295 := bstep (se 1 (by rfl) ⟨1148471, by rfl⟩ : syracuseStep 1531295 = 2296943) B2296943
theorem B908855 : Blo 603293 908855 := bstep (se 1 (by rfl) ⟨681641, by rfl⟩ : syracuseStep 908855 = 1363283) B1363283
theorem B16604939 : Blo 603293 16604939 := bstep (se 1 (by rfl) ⟨12453704, by rfl⟩ : syracuseStep 16604939 = 24907409) B24907409
theorem B679783 : Blo 603293 679783 := bstep (se 1 (by rfl) ⟨509837, by rfl⟩ : syracuseStep 679783 = 1019675) B1019675
theorem B909449 : Blo 603293 909449 := bstep (se 2 (by rfl) ⟨341043, by rfl⟩ : syracuseStep 909449 = 682087) B682087
theorem B909563 : Blo 603293 909563 := bstep (se 1 (by rfl) ⟨682172, by rfl⟩ : syracuseStep 909563 = 1364345) B1364345
theorem B910055 : Blo 603293 910055 := bstep (se 1 (by rfl) ⟨682541, by rfl⟩ : syracuseStep 910055 = 1365083) B1365083
theorem B3073139 : Blo 603293 3073139 := bstep (se 1 (by rfl) ⟨2304854, by rfl⟩ : syracuseStep 3073139 = 4609709) B4609709
theorem B910463 : Blo 603293 910463 := bstep (se 1 (by rfl) ⟨682847, by rfl⟩ : syracuseStep 910463 = 1365695) B1365695
theorem B683167 : Blo 603293 683167 := bstep (se 1 (by rfl) ⟨512375, by rfl⟩ : syracuseStep 683167 = 1024751) B1024751
theorem B2583737 : Blo 603293 2583737 := bstep (se 2 (by rfl) ⟨968901, by rfl⟩ : syracuseStep 2583737 = 1937803) B1937803
theorem B1535183 : Blo 603293 1535183 := bstep (se 1 (by rfl) ⟨1151387, by rfl⟩ : syracuseStep 1535183 = 2302775) B2302775
theorem B7466863 : Blo 603293 7466863 := bstep (se 1 (by rfl) ⟨5600147, by rfl⟩ : syracuseStep 7466863 = 11200295) B11200295
theorem B1536671 : Blo 603293 1536671 := bstep (se 1 (by rfl) ⟨1152503, by rfl⟩ : syracuseStep 1536671 = 2305007) B2305007
theorem B15497081 : Blo 603293 15497081 := bstep (se 2 (by rfl) ⟨5811405, by rfl⟩ : syracuseStep 15497081 = 11622811) B11622811
theorem B1638265 : Blo 603293 1638265 := bstep (se 2 (by rfl) ⟨614349, by rfl⟩ : syracuseStep 1638265 = 1228699) B1228699
theorem B41517143 : Blo 603293 41517143 := bstep (se 1 (by rfl) ⟨31137857, by rfl⟩ : syracuseStep 41517143 = 62275715) B62275715
theorem B1149481 : Blo 603293 1149481 := bstep (se 2 (by rfl) ⟨431055, by rfl⟩ : syracuseStep 1149481 = 862111) B862111
theorem B4918427 : Blo 603293 4918427 := bstep (se 1 (by rfl) ⟨3688820, by rfl⟩ : syracuseStep 4918427 = 7377641) B7377641
theorem B2592263 : Blo 603293 2592263 := bstep (se 1 (by rfl) ⟨1944197, by rfl⟩ : syracuseStep 2592263 = 3888395) B3888395
theorem B19697579 : Blo 603293 19697579 := bstep (se 1 (by rfl) ⟨14773184, by rfl⟩ : syracuseStep 19697579 = 29546369) B29546369
theorem B5378399 : Blo 603293 5378399 := bstep (se 1 (by rfl) ⟨4033799, by rfl⟩ : syracuseStep 5378399 = 8067599) B8067599
theorem B2036393 : Blo 603293 2036393 := bstep (se 2 (by rfl) ⟨763647, by rfl⟩ : syracuseStep 2036393 = 1527295) B1527295
theorem B4363055 : Blo 603293 4363055 := bstep (se 1 (by rfl) ⟨3272291, by rfl⟩ : syracuseStep 4363055 = 6544583) B6544583
theorem B1020863 : Blo 603293 1020863 := bstep (se 1 (by rfl) ⟨765647, by rfl⟩ : syracuseStep 1020863 = 1531295) B1531295
theorem B24778669 : Blo 603293 24778669 := bstep (se 3 (by rfl) ⟨4646000, by rfl⟩ : syracuseStep 24778669 = 9292001) B9292001
theorem B34838909 : Blo 603293 34838909 := bstep (se 3 (by rfl) ⟨6532295, by rfl⟩ : syracuseStep 34838909 = 13064591) B13064591
theorem B2038175 : Blo 603293 2038175 := bstep (se 1 (by rfl) ⟨1528631, by rfl⟩ : syracuseStep 2038175 = 3057263) B3057263
theorem B2334025 : Blo 603293 2334025 := bstep (se 2 (by rfl) ⟨875259, by rfl⟩ : syracuseStep 2334025 = 1750519) B1750519
theorem B12393935 : Blo 603293 12393935 := bstep (se 1 (by rfl) ⟨9295451, by rfl⟩ : syracuseStep 12393935 = 18590903) B18590903
theorem B1023455 : Blo 603293 1023455 := bstep (se 1 (by rfl) ⟨767591, by rfl⟩ : syracuseStep 1023455 = 1535183) B1535183
theorem B860095 : Blo 603293 860095 := bstep (se 1 (by rfl) ⟨645071, by rfl⟩ : syracuseStep 860095 = 1290143) B1290143
theorem B5185619 : Blo 603293 5185619 := bstep (se 1 (by rfl) ⟨3889214, by rfl⟩ : syracuseStep 5185619 = 7778429) B7778429
theorem B1024447 : Blo 603293 1024447 := bstep (se 1 (by rfl) ⟨768335, by rfl⟩ : syracuseStep 1024447 = 1536671) B1536671
theorem B10331387 : Blo 603293 10331387 := bstep (se 1 (by rfl) ⟨7748540, by rfl⟩ : syracuseStep 10331387 = 15497081) B15497081
theorem B2042063 : Blo 603293 2042063 := bstep (se 1 (by rfl) ⟨1531547, by rfl⟩ : syracuseStep 2042063 = 3063095) B3063095
theorem B2043143 : Blo 603293 2043143 := bstep (se 1 (by rfl) ⟨1532357, by rfl⟩ : syracuseStep 2043143 = 3064715) B3064715
theorem B11644955 : Blo 603293 11644955 := bstep (se 1 (by rfl) ⟨8733716, by rfl⟩ : syracuseStep 11644955 = 17467433) B17467433
theorem B603303 : Blo 603293 603303 := bstep (se 1 (by rfl) ⟨452477, by rfl⟩ : syracuseStep 603303 = 904955) B904955
theorem B1357415 : Blo 603293 1357415 := bstep (se 1 (by rfl) ⟨1018061, by rfl⟩ : syracuseStep 1357415 = 2036123) B2036123
theorem B767647 : Blo 603293 767647 := bstep (se 1 (by rfl) ⟨575735, by rfl⟩ : syracuseStep 767647 = 1151471) B1151471
theorem B1357793 : Blo 603293 1357793 := bstep (se 2 (by rfl) ⟨509172, by rfl⟩ : syracuseStep 1357793 = 1018345) B1018345
theorem B604155 : Blo 603293 604155 := bstep (se 1 (by rfl) ⟨453116, by rfl⟩ : syracuseStep 604155 = 906233) B906233
theorem B7747721 : Blo 603293 7747721 := bstep (se 2 (by rfl) ⟨2905395, by rfl⟩ : syracuseStep 7747721 = 5810791) B5810791
theorem B1357991 : Blo 603293 1357991 := bstep (se 1 (by rfl) ⟨1018493, by rfl⟩ : syracuseStep 1357991 = 2036987) B2036987
theorem B604383 : Blo 603293 604383 := bstep (se 1 (by rfl) ⟨453287, by rfl⟩ : syracuseStep 604383 = 906575) B906575
theorem B1554743 : Blo 603293 1554743 := bstep (se 1 (by rfl) ⟨1166057, by rfl⟩ : syracuseStep 1554743 = 2332115) B2332115
theorem B5159375 : Blo 603293 5159375 := bstep (se 1 (by rfl) ⟨3869531, by rfl⟩ : syracuseStep 5159375 = 7739063) B7739063
theorem B3456553 : Blo 603293 3456553 := bstep (se 2 (by rfl) ⟨1296207, by rfl⟩ : syracuseStep 3456553 = 2592415) B2592415
theorem B605903 : Blo 603293 605903 := bstep (se 1 (by rfl) ⟨454427, by rfl⟩ : syracuseStep 605903 = 908855) B908855
theorem B1359899 : Blo 603293 1359899 := bstep (se 1 (by rfl) ⟨1019924, by rfl⟩ : syracuseStep 1359899 = 2039849) B2039849
theorem B606299 : Blo 603293 606299 := bstep (se 1 (by rfl) ⟨454724, by rfl⟩ : syracuseStep 606299 = 909449) B909449
theorem B606375 : Blo 603293 606375 := bstep (se 1 (by rfl) ⟨454781, by rfl⟩ : syracuseStep 606375 = 909563) B909563
theorem B1229023 : Blo 603293 1229023 := bstep (se 1 (by rfl) ⟨921767, by rfl⟩ : syracuseStep 1229023 = 1843535) B1843535
theorem B606703 : Blo 603293 606703 := bstep (se 1 (by rfl) ⟨455027, by rfl⟩ : syracuseStep 606703 = 910055) B910055
theorem B11780777 : Blo 603293 11780777 := bstep (se 2 (by rfl) ⟨4417791, by rfl⟩ : syracuseStep 11780777 = 8835583) B8835583
theorem B2048759 : Blo 603293 2048759 := bstep (se 1 (by rfl) ⟨1536569, by rfl⟩ : syracuseStep 2048759 = 3073139) B3073139
theorem B606975 : Blo 603293 606975 := bstep (se 1 (by rfl) ⟨455231, by rfl⟩ : syracuseStep 606975 = 910463) B910463
theorem B3065039 : Blo 603293 3065039 := bstep (se 1 (by rfl) ⟨2298779, by rfl⟩ : syracuseStep 3065039 = 4597559) B4597559
theorem B5031503 : Blo 603293 5031503 := bstep (se 1 (by rfl) ⟨3773627, by rfl⟩ : syracuseStep 5031503 = 7547255) B7547255
theorem B1722491 : Blo 603293 1722491 := bstep (se 1 (by rfl) ⟨1291868, by rfl⟩ : syracuseStep 1722491 = 2583737) B2583737
theorem B3066335 : Blo 603293 3066335 := bstep (se 1 (by rfl) ⟨2299751, by rfl⟩ : syracuseStep 3066335 = 4599503) B4599503
theorem B10472075 : Blo 603293 10472075 := bstep (se 1 (by rfl) ⟨7854056, by rfl⟩ : syracuseStep 10472075 = 15708113) B15708113
theorem B969383 : Blo 603293 969383 := bstep (se 1 (by rfl) ⟨727037, by rfl⟩ : syracuseStep 969383 = 1454075) B1454075
theorem B5164397 : Blo 603293 5164397 := bstep (se 3 (by rfl) ⟨968324, by rfl⟩ : syracuseStep 5164397 = 1936649) B1936649
theorem B9817649 : Blo 603293 9817649 := bstep (se 2 (by rfl) ⟨3681618, by rfl⟩ : syracuseStep 9817649 = 7363237) B7363237
theorem B906377 : Blo 603293 906377 := bstep (se 2 (by rfl) ⟨339891, by rfl⟩ : syracuseStep 906377 = 679783) B679783
theorem B2184353 : Blo 603293 2184353 := bstep (se 2 (by rfl) ⟨819132, by rfl⟩ : syracuseStep 2184353 = 1638265) B1638265
theorem B907163 : Blo 603293 907163 := bstep (se 1 (by rfl) ⟨680372, by rfl⟩ : syracuseStep 907163 = 1360745) B1360745
theorem B1365983 : Blo 603293 1365983 := bstep (se 1 (by rfl) ⟨1024487, by rfl⟩ : syracuseStep 1365983 = 2048975) B2048975
theorem B907775 : Blo 603293 907775 := bstep (se 1 (by rfl) ⟨680831, by rfl⟩ : syracuseStep 907775 = 1361663) B1361663
theorem B3988511 : Blo 603293 3988511 := bstep (se 1 (by rfl) ⟨2991383, by rfl⟩ : syracuseStep 3988511 = 5982767) B5982767
theorem B4611167 : Blo 603293 4611167 := bstep (se 1 (by rfl) ⟨3458375, by rfl⟩ : syracuseStep 4611167 = 6916751) B6916751
theorem B908447 : Blo 603293 908447 := bstep (se 1 (by rfl) ⟨681335, by rfl⟩ : syracuseStep 908447 = 1362671) B1362671
theorem B4349159 : Blo 603293 4349159 := bstep (se 1 (by rfl) ⟨3261869, by rfl⟩ : syracuseStep 4349159 = 6523739) B6523739
theorem B1531183 : Blo 603293 1531183 := bstep (se 1 (by rfl) ⟨1148387, by rfl⟩ : syracuseStep 1531183 = 2296775) B2296775
theorem B679963 : Blo 603293 679963 := bstep (se 1 (by rfl) ⟨509972, by rfl⟩ : syracuseStep 679963 = 1019945) B1019945
theorem B909407 : Blo 603293 909407 := bstep (se 1 (by rfl) ⟨682055, by rfl⟩ : syracuseStep 909407 = 1364111) B1364111
theorem B909479 : Blo 603293 909479 := bstep (se 1 (by rfl) ⟨682109, by rfl⟩ : syracuseStep 909479 = 1364219) B1364219
theorem B3367177 : Blo 603293 3367177 := bstep (se 2 (by rfl) ⟨1262691, by rfl⟩ : syracuseStep 3367177 = 2525383) B2525383
theorem B910151 : Blo 603293 910151 := bstep (se 1 (by rfl) ⟨682613, by rfl⟩ : syracuseStep 910151 = 1365227) B1365227
theorem B910889 : Blo 603293 910889 := bstep (se 2 (by rfl) ⟨341583, by rfl⟩ : syracuseStep 910889 = 683167) B683167
theorem B255682115 : Blo 603293 255682115 := bstep (se 1 (by rfl) ⟨191761586, by rfl⟩ : syracuseStep 255682115 = 383523173) B383523173
theorem B1534079 : Blo 603293 1534079 := bstep (se 1 (by rfl) ⟨1150559, by rfl⟩ : syracuseStep 1534079 = 2301119) B2301119
theorem B9955817 : Blo 603293 9955817 := bstep (se 2 (by rfl) ⟨3733431, by rfl⟩ : syracuseStep 9955817 = 7466863) B7466863
theorem B11069959 : Blo 603293 11069959 := bstep (se 1 (by rfl) ⟨8302469, by rfl⟩ : syracuseStep 11069959 = 16604939) B16604939
theorem B2910761 : Blo 603293 2910761 := bstep (se 2 (by rfl) ⟨1091535, by rfl⟩ : syracuseStep 2910761 = 2183071) B2183071
theorem B2452207 : Blo 603293 2452207 := bstep (se 1 (by rfl) ⟨1839155, by rfl⟩ : syracuseStep 2452207 = 3678311) B3678311
theorem B1535507 : Blo 603293 1535507 := bstep (se 1 (by rfl) ⟨1151630, by rfl⟩ : syracuseStep 1535507 = 2303261) B2303261
theorem B22052341 : Blo 603293 22052341 := bstep (se 5 (by rfl) ⟨1033703, by rfl⟩ : syracuseStep 22052341 = 2067407) B2067407
theorem B6554789 : Blo 603293 6554789 := bstep (se 4 (by rfl) ⟨614511, by rfl⟩ : syracuseStep 6554789 = 1229023) B1229023
theorem B17958277 : Blo 603293 17958277 := bstep (se 4 (by rfl) ⟨1683588, by rfl⟩ : syracuseStep 17958277 = 3367177) B3367177
theorem B1148327 : Blo 603293 1148327 := bstep (se 1 (by rfl) ⟨861245, by rfl⟩ : syracuseStep 1148327 = 1722491) B1722491
theorem B6981383 : Blo 603293 6981383 := bstep (se 1 (by rfl) ⟨5236037, by rfl⟩ : syracuseStep 6981383 = 10472075) B10472075
theorem B3278951 : Blo 603293 3278951 := bstep (se 1 (by rfl) ⟨2459213, by rfl⟩ : syracuseStep 3278951 = 4918427) B4918427
theorem B3442931 : Blo 603293 3442931 := bstep (se 1 (by rfl) ⟨2582198, by rfl⟩ : syracuseStep 3442931 = 5164397) B5164397
theorem B2659007 : Blo 603293 2659007 := bstep (se 1 (by rfl) ⟨1994255, by rfl⟩ : syracuseStep 2659007 = 3988511) B3988511
theorem B8262623 : Blo 603293 8262623 := bstep (se 1 (by rfl) ⟨6196967, by rfl⟩ : syracuseStep 8262623 = 12393935) B12393935
theorem B6887591 : Blo 603293 6887591 := bstep (se 1 (by rfl) ⟨5165693, by rfl⟩ : syracuseStep 6887591 = 10331387) B10331387
theorem B1022719 : Blo 603293 1022719 := bstep (se 1 (by rfl) ⟨767039, by rfl⟩ : syracuseStep 1022719 = 1534079) B1534079
theorem B1940507 : Blo 603293 1940507 := bstep (se 1 (by rfl) ⟨1455380, by rfl⟩ : syracuseStep 1940507 = 2910761) B2910761
theorem B1023529 : Blo 603293 1023529 := bstep (se 2 (by rfl) ⟨383823, by rfl⟩ : syracuseStep 1023529 = 767647) B767647
theorem B1023671 : Blo 603293 1023671 := bstep (se 1 (by rfl) ⟨767753, by rfl⟩ : syracuseStep 1023671 = 1535507) B1535507
theorem B33038225 : Blo 603293 33038225 := bstep (se 2 (by rfl) ⟨12389334, by rfl⟩ : syracuseStep 33038225 = 24778669) B24778669
theorem B2041577 : Blo 603293 2041577 := bstep (se 2 (by rfl) ⟨765591, by rfl⟩ : syracuseStep 2041577 = 1531183) B1531183
theorem B29403121 : Blo 603293 29403121 := bstep (se 2 (by rfl) ⟨11026170, by rfl⟩ : syracuseStep 29403121 = 22052341) B22052341
theorem B2043359 : Blo 603293 2043359 := bstep (se 1 (by rfl) ⟨1532519, by rfl⟩ : syracuseStep 2043359 = 3065039) B3065039
theorem B3354335 : Blo 603293 3354335 := bstep (se 1 (by rfl) ⟨2515751, by rfl⟩ : syracuseStep 3354335 = 5031503) B5031503
theorem B2044223 : Blo 603293 2044223 := bstep (se 1 (by rfl) ⟨1533167, by rfl⟩ : syracuseStep 2044223 = 3066335) B3066335
theorem B3585599 : Blo 603293 3585599 := bstep (se 1 (by rfl) ⟨2689199, by rfl⟩ : syracuseStep 3585599 = 5378399) B5378399
theorem B1357595 : Blo 603293 1357595 := bstep (se 1 (by rfl) ⟨1018196, by rfl⟩ : syracuseStep 1357595 = 2036393) B2036393
theorem B14759945 : Blo 603293 14759945 := bstep (se 2 (by rfl) ⟨5534979, by rfl⟩ : syracuseStep 14759945 = 11069959) B11069959
theorem B604251 : Blo 603293 604251 := bstep (se 1 (by rfl) ⟨453188, by rfl⟩ : syracuseStep 604251 = 906377) B906377
theorem B1456235 : Blo 603293 1456235 := bstep (se 1 (by rfl) ⟨1092176, by rfl⟩ : syracuseStep 1456235 = 2184353) B2184353
theorem B604775 : Blo 603293 604775 := bstep (se 1 (by rfl) ⟨453581, by rfl⟩ : syracuseStep 604775 = 907163) B907163
theorem B1358783 : Blo 603293 1358783 := bstep (se 1 (by rfl) ⟨1019087, by rfl⟩ : syracuseStep 1358783 = 2038175) B2038175
theorem B605183 : Blo 603293 605183 := bstep (se 1 (by rfl) ⟨453887, by rfl⟩ : syracuseStep 605183 = 907775) B907775
theorem B605631 : Blo 603293 605631 := bstep (se 1 (by rfl) ⟨454223, by rfl⟩ : syracuseStep 605631 = 908447) B908447
theorem B2899439 : Blo 603293 2899439 := bstep (se 1 (by rfl) ⟨2174579, by rfl⟩ : syracuseStep 2899439 = 4349159) B4349159
theorem B3457079 : Blo 603293 3457079 := bstep (se 1 (by rfl) ⟨2592809, by rfl⟩ : syracuseStep 3457079 = 5185619) B5185619
theorem B606271 : Blo 603293 606271 := bstep (se 1 (by rfl) ⟨454703, by rfl⟩ : syracuseStep 606271 = 909407) B909407
theorem B606319 : Blo 603293 606319 := bstep (se 1 (by rfl) ⟨454739, by rfl⟩ : syracuseStep 606319 = 909479) B909479
theorem B606767 : Blo 603293 606767 := bstep (se 1 (by rfl) ⟨455075, by rfl⟩ : syracuseStep 606767 = 910151) B910151
theorem B607259 : Blo 603293 607259 := bstep (se 1 (by rfl) ⟨455444, by rfl⟩ : syracuseStep 607259 = 910889) B910889
theorem B1361375 : Blo 603293 1361375 := bstep (se 1 (by rfl) ⟨1021031, by rfl⟩ : syracuseStep 1361375 = 2042063) B2042063
theorem B6637211 : Blo 603293 6637211 := bstep (se 1 (by rfl) ⟨4977908, by rfl⟩ : syracuseStep 6637211 = 9955817) B9955817
theorem B1362095 : Blo 603293 1362095 := bstep (se 1 (by rfl) ⟨1021571, by rfl⟩ : syracuseStep 1362095 = 2043143) B2043143
theorem B904943 : Blo 603293 904943 := bstep (se 1 (by rfl) ⟨678707, by rfl⟩ : syracuseStep 904943 = 1357415) B1357415
theorem B905195 : Blo 603293 905195 := bstep (se 1 (by rfl) ⟨678896, by rfl⟩ : syracuseStep 905195 = 1357793) B1357793
theorem B5165147 : Blo 603293 5165147 := bstep (se 1 (by rfl) ⟨3873860, by rfl⟩ : syracuseStep 5165147 = 7747721) B7747721
theorem B905327 : Blo 603293 905327 := bstep (se 1 (by rfl) ⟨678995, by rfl⟩ : syracuseStep 905327 = 1357991) B1357991
theorem B1036495 : Blo 603293 1036495 := bstep (se 1 (by rfl) ⟨777371, by rfl⟩ : syracuseStep 1036495 = 1554743) B1554743
theorem B4608737 : Blo 603293 4608737 := bstep (se 2 (by rfl) ⟨1728276, by rfl⟩ : syracuseStep 4608737 = 3456553) B3456553
theorem B906599 : Blo 603293 906599 := bstep (se 1 (by rfl) ⟨679949, by rfl⟩ : syracuseStep 906599 = 1359899) B1359899
theorem B906617 : Blo 603293 906617 := bstep (se 2 (by rfl) ⟨339981, by rfl⟩ : syracuseStep 906617 = 679963) B679963
theorem B27678095 : Blo 603293 27678095 := bstep (se 1 (by rfl) ⟨20758571, by rfl⟩ : syracuseStep 27678095 = 41517143) B41517143
theorem B7853851 : Blo 603293 7853851 := bstep (se 1 (by rfl) ⟨5890388, by rfl⟩ : syracuseStep 7853851 = 11780777) B11780777
theorem B1365839 : Blo 603293 1365839 := bstep (se 1 (by rfl) ⟨1024379, by rfl⟩ : syracuseStep 1365839 = 2048759) B2048759
theorem B1365929 : Blo 603293 1365929 := bstep (se 2 (by rfl) ⟨512223, by rfl⟩ : syracuseStep 1365929 = 1024447) B1024447
theorem B646255 : Blo 603293 646255 := bstep (se 1 (by rfl) ⟨484691, by rfl⟩ : syracuseStep 646255 = 969383) B969383
theorem B1728175 : Blo 603293 1728175 := bstep (se 1 (by rfl) ⟨1296131, by rfl⟩ : syracuseStep 1728175 = 2592263) B2592263
theorem B6545099 : Blo 603293 6545099 := bstep (se 1 (by rfl) ⟨4908824, by rfl⟩ : syracuseStep 6545099 = 9817649) B9817649
theorem B13131719 : Blo 603293 13131719 := bstep (se 1 (by rfl) ⟨9848789, by rfl⟩ : syracuseStep 13131719 = 19697579) B19697579
theorem B2908703 : Blo 603293 2908703 := bstep (se 1 (by rfl) ⟨2181527, by rfl⟩ : syracuseStep 2908703 = 4363055) B4363055
theorem B680575 : Blo 603293 680575 := bstep (se 1 (by rfl) ⟨510431, by rfl⟩ : syracuseStep 680575 = 1020863) B1020863
theorem B1532641 : Blo 603293 1532641 := bstep (se 2 (by rfl) ⟨574740, by rfl⟩ : syracuseStep 1532641 = 1149481) B1149481
theorem B3269609 : Blo 603293 3269609 := bstep (se 2 (by rfl) ⟨1226103, by rfl⟩ : syracuseStep 3269609 = 2452207) B2452207
theorem B910655 : Blo 603293 910655 := bstep (se 1 (by rfl) ⟨682991, by rfl⟩ : syracuseStep 910655 = 1365983) B1365983
theorem B23225939 : Blo 603293 23225939 := bstep (se 1 (by rfl) ⟨17419454, by rfl⟩ : syracuseStep 23225939 = 34838909) B34838909
theorem B3074111 : Blo 603293 3074111 := bstep (se 1 (by rfl) ⟨2305583, by rfl⟩ : syracuseStep 3074111 = 4611167) B4611167
theorem B682303 : Blo 603293 682303 := bstep (se 1 (by rfl) ⟨511727, by rfl⟩ : syracuseStep 682303 = 1023455) B1023455
theorem B170454743 : Blo 603293 170454743 := bstep (se 1 (by rfl) ⟨127841057, by rfl⟩ : syracuseStep 170454743 = 255682115) B255682115
theorem B7763303 : Blo 603293 7763303 := bstep (se 1 (by rfl) ⟨5822477, by rfl⟩ : syracuseStep 7763303 = 11644955) B11644955
theorem B3439583 : Blo 603293 3439583 := bstep (se 1 (by rfl) ⟨2579687, by rfl⟩ : syracuseStep 3439583 = 5159375) B5159375
theorem B3112033 : Blo 603293 3112033 := bstep (se 2 (by rfl) ⟨1167012, by rfl⟩ : syracuseStep 3112033 = 2334025) B2334025
theorem B1146793 : Blo 603293 1146793 := bstep (se 2 (by rfl) ⟨430047, by rfl⟩ : syracuseStep 1146793 = 860095) B860095
theorem B4424807 : Blo 603293 4424807 := bstep (se 1 (by rfl) ⟨3318605, by rfl⟩ : syracuseStep 4424807 = 6637211) B6637211
theorem B4654255 : Blo 603293 4654255 := bstep (se 1 (by rfl) ⟨3490691, by rfl⟩ : syracuseStep 4654255 = 6981383) B6981383
theorem B2295287 : Blo 603293 2295287 := bstep (se 1 (by rfl) ⟨1721465, by rfl⟩ : syracuseStep 2295287 = 3442931) B3442931
theorem B3443431 : Blo 603293 3443431 := bstep (se 1 (by rfl) ⟨2582573, by rfl⟩ : syracuseStep 3443431 = 5165147) B5165147
theorem B1772671 : Blo 603293 1772671 := bstep (se 1 (by rfl) ⟨1329503, by rfl⟩ : syracuseStep 1772671 = 2659007) B2659007
theorem B5508415 : Blo 603293 5508415 := bstep (se 1 (by rfl) ⟨4131311, by rfl⟩ : syracuseStep 5508415 = 8262623) B8262623
theorem B18452063 : Blo 603293 18452063 := bstep (se 1 (by rfl) ⟨13839047, by rfl⟩ : syracuseStep 18452063 = 27678095) B27678095
theorem B4591727 : Blo 603293 4591727 := bstep (se 1 (by rfl) ⟨3443795, by rfl⟩ : syracuseStep 4591727 = 6887591) B6887591
theorem B4363399 : Blo 603293 4363399 := bstep (se 1 (by rfl) ⟨3272549, by rfl⟩ : syracuseStep 4363399 = 6545099) B6545099
theorem B22025483 : Blo 603293 22025483 := bstep (se 1 (by rfl) ⟨16519112, by rfl⟩ : syracuseStep 22025483 = 33038225) B33038225
theorem B8754479 : Blo 603293 8754479 := bstep (se 1 (by rfl) ⟨6565859, by rfl⟩ : syracuseStep 8754479 = 13131719) B13131719
theorem B1939135 : Blo 603293 1939135 := bstep (se 1 (by rfl) ⟨1454351, by rfl⟩ : syracuseStep 1939135 = 2908703) B2908703
theorem B2236223 : Blo 603293 2236223 := bstep (se 1 (by rfl) ⟨1677167, by rfl⟩ : syracuseStep 2236223 = 3354335) B3354335
theorem B9839963 : Blo 603293 9839963 := bstep (se 1 (by rfl) ⟨7379972, by rfl⟩ : syracuseStep 9839963 = 14759945) B14759945
theorem B861673 : Blo 603293 861673 := bstep (se 2 (by rfl) ⟨323127, by rfl⟩ : syracuseStep 861673 = 646255) B646255
theorem B2304233 : Blo 603293 2304233 := bstep (se 2 (by rfl) ⟨864087, by rfl⟩ : syracuseStep 2304233 = 1728175) B1728175
theorem B2304719 : Blo 603293 2304719 := bstep (se 1 (by rfl) ⟨1728539, by rfl⟩ : syracuseStep 2304719 = 3457079) B3457079
theorem B4369859 : Blo 603293 4369859 := bstep (se 1 (by rfl) ⟨3277394, by rfl⟩ : syracuseStep 4369859 = 6554789) B6554789
theorem B765551 : Blo 603293 765551 := bstep (se 1 (by rfl) ⟨574163, by rfl⟩ : syracuseStep 765551 = 1148327) B1148327
theorem B2043521 : Blo 603293 2043521 := bstep (se 2 (by rfl) ⟨766320, by rfl⟩ : syracuseStep 2043521 = 1532641) B1532641
theorem B603295 : Blo 603293 603295 := bstep (se 1 (by rfl) ⟨452471, by rfl⟩ : syracuseStep 603295 = 904943) B904943
theorem B39204161 : Blo 603293 39204161 := bstep (se 2 (by rfl) ⟨14701560, by rfl⟩ : syracuseStep 39204161 = 29403121) B29403121
theorem B603463 : Blo 603293 603463 := bstep (se 1 (by rfl) ⟨452597, by rfl⟩ : syracuseStep 603463 = 905195) B905195
theorem B603551 : Blo 603293 603551 := bstep (se 1 (by rfl) ⟨452663, by rfl⟩ : syracuseStep 603551 = 905327) B905327
theorem B604399 : Blo 603293 604399 := bstep (se 1 (by rfl) ⟨453299, by rfl⟩ : syracuseStep 604399 = 906599) B906599
theorem B604411 : Blo 603293 604411 := bstep (se 1 (by rfl) ⟨453308, by rfl⟩ : syracuseStep 604411 = 906617) B906617
theorem B1293671 : Blo 603293 1293671 := bstep (se 1 (by rfl) ⟨970253, by rfl⟩ : syracuseStep 1293671 = 1940507) B1940507
theorem B2179739 : Blo 603293 2179739 := bstep (se 1 (by rfl) ⟨1634804, by rfl⟩ : syracuseStep 2179739 = 3269609) B3269609
theorem B607103 : Blo 603293 607103 := bstep (se 1 (by rfl) ⟨455327, by rfl⟩ : syracuseStep 607103 = 910655) B910655
theorem B15483959 : Blo 603293 15483959 := bstep (se 1 (by rfl) ⟨11612969, by rfl⟩ : syracuseStep 15483959 = 23225939) B23225939
theorem B1361051 : Blo 603293 1361051 := bstep (se 1 (by rfl) ⟨1020788, by rfl⟩ : syracuseStep 1361051 = 2041577) B2041577
theorem B2049407 : Blo 603293 2049407 := bstep (se 1 (by rfl) ⟨1537055, by rfl⟩ : syracuseStep 2049407 = 3074111) B3074111
theorem B1362239 : Blo 603293 1362239 := bstep (se 1 (by rfl) ⟨1021679, by rfl⟩ : syracuseStep 1362239 = 2043359) B2043359
theorem B10471801 : Blo 603293 10471801 := bstep (se 2 (by rfl) ⟨3926925, by rfl⟩ : syracuseStep 10471801 = 7853851) B7853851
theorem B1362815 : Blo 603293 1362815 := bstep (se 1 (by rfl) ⟨1022111, by rfl⟩ : syracuseStep 1362815 = 2044223) B2044223
theorem B1363625 : Blo 603293 1363625 := bstep (se 2 (by rfl) ⟨511359, by rfl⟩ : syracuseStep 1363625 = 1022719) B1022719
theorem B905063 : Blo 603293 905063 := bstep (se 1 (by rfl) ⟨678797, by rfl⟩ : syracuseStep 905063 = 1357595) B1357595
theorem B970823 : Blo 603293 970823 := bstep (se 1 (by rfl) ⟨728117, by rfl⟩ : syracuseStep 970823 = 1456235) B1456235
theorem B4149377 : Blo 603293 4149377 := bstep (se 2 (by rfl) ⟨1556016, by rfl⟩ : syracuseStep 4149377 = 3112033) B3112033
theorem B905855 : Blo 603293 905855 := bstep (se 1 (by rfl) ⟨679391, by rfl⟩ : syracuseStep 905855 = 1358783) B1358783
theorem B1364705 : Blo 603293 1364705 := bstep (se 2 (by rfl) ⟨511764, by rfl⟩ : syracuseStep 1364705 = 1023529) B1023529
theorem B1529057 : Blo 603293 1529057 := bstep (se 2 (by rfl) ⟨573396, by rfl⟩ : syracuseStep 1529057 = 1146793) B1146793
theorem B907433 : Blo 603293 907433 := bstep (se 2 (by rfl) ⟨340287, by rfl⟩ : syracuseStep 907433 = 680575) B680575
theorem B907583 : Blo 603293 907583 := bstep (se 1 (by rfl) ⟨680687, by rfl⟩ : syracuseStep 907583 = 1361375) B1361375
theorem B5527973 : Blo 603293 5527973 := bstep (se 4 (by rfl) ⟨518247, by rfl⟩ : syracuseStep 5527973 = 1036495) B1036495
theorem B2185967 : Blo 603293 2185967 := bstep (se 1 (by rfl) ⟨1639475, by rfl⟩ : syracuseStep 2185967 = 3278951) B3278951
theorem B908063 : Blo 603293 908063 := bstep (se 1 (by rfl) ⟨681047, by rfl⟩ : syracuseStep 908063 = 1362095) B1362095
theorem B909737 : Blo 603293 909737 := bstep (se 2 (by rfl) ⟨341151, by rfl⟩ : syracuseStep 909737 = 682303) B682303
theorem B3072491 : Blo 603293 3072491 := bstep (se 1 (by rfl) ⟨2304368, by rfl⟩ : syracuseStep 3072491 = 4608737) B4608737
theorem B910559 : Blo 603293 910559 := bstep (se 1 (by rfl) ⟨682919, by rfl⟩ : syracuseStep 910559 = 1365839) B1365839
theorem B910619 : Blo 603293 910619 := bstep (se 1 (by rfl) ⟨682964, by rfl⟩ : syracuseStep 910619 = 1365929) B1365929
theorem B682447 : Blo 603293 682447 := bstep (se 1 (by rfl) ⟨511835, by rfl⟩ : syracuseStep 682447 = 1023671) B1023671
theorem B95777477 : Blo 603293 95777477 := bstep (se 4 (by rfl) ⟨8979138, by rfl⟩ : syracuseStep 95777477 = 17958277) B17958277
theorem B113636495 : Blo 603293 113636495 := bstep (se 1 (by rfl) ⟨85227371, by rfl⟩ : syracuseStep 113636495 = 170454743) B170454743
theorem B5175535 : Blo 603293 5175535 := bstep (se 1 (by rfl) ⟨3881651, by rfl⟩ : syracuseStep 5175535 = 7763303) B7763303
theorem B2390399 : Blo 603293 2390399 := bstep (se 1 (by rfl) ⟨1792799, by rfl⟩ : syracuseStep 2390399 = 3585599) B3585599
theorem B2293055 : Blo 603293 2293055 := bstep (se 1 (by rfl) ⟨1719791, by rfl⟩ : syracuseStep 2293055 = 3439583) B3439583
theorem B1932959 : Blo 603293 1932959 := bstep (se 1 (by rfl) ⟨1449719, by rfl⟩ : syracuseStep 1932959 = 2899439) B2899439
theorem B2588861 : Blo 603293 2588861 := bstep (se 3 (by rfl) ⟨485411, by rfl⟩ : syracuseStep 2588861 = 970823) B970823
theorem B10322639 : Blo 603293 10322639 := bstep (se 1 (by rfl) ⟨7741979, by rfl⟩ : syracuseStep 10322639 = 15483959) B15483959
theorem B2949871 : Blo 603293 2949871 := bstep (se 1 (by rfl) ⟨2212403, by rfl⟩ : syracuseStep 2949871 = 4424807) B4424807
theorem B1148897 : Blo 603293 1148897 := bstep (se 2 (by rfl) ⟨430836, by rfl⟩ : syracuseStep 1148897 = 861673) B861673
theorem B13962401 : Blo 603293 13962401 := bstep (se 2 (by rfl) ⟨5235900, by rfl⟩ : syracuseStep 13962401 = 10471801) B10471801
theorem B1019371 : Blo 603293 1019371 := bstep (se 1 (by rfl) ⟨764528, by rfl⟩ : syracuseStep 1019371 = 1529057) B1529057
theorem B14683655 : Blo 603293 14683655 := bstep (se 1 (by rfl) ⟨11012741, by rfl⟩ : syracuseStep 14683655 = 22025483) B22025483
theorem B5836319 : Blo 603293 5836319 := bstep (se 1 (by rfl) ⟨4377239, by rfl⟩ : syracuseStep 5836319 = 8754479) B8754479
theorem B4591241 : Blo 603293 4591241 := bstep (se 2 (by rfl) ⟨1721715, by rfl⟩ : syracuseStep 4591241 = 3443431) B3443431
theorem B2363561 : Blo 603293 2363561 := bstep (se 2 (by rfl) ⟨886335, by rfl⟩ : syracuseStep 2363561 = 1772671) B1772671
theorem B6559975 : Blo 603293 6559975 := bstep (se 1 (by rfl) ⟨4919981, by rfl⟩ : syracuseStep 6559975 = 9839963) B9839963
theorem B3449789 : Blo 603293 3449789 := bstep (se 3 (by rfl) ⟨646835, by rfl⟩ : syracuseStep 3449789 = 1293671) B1293671
theorem B2041469 : Blo 603293 2041469 := bstep (se 3 (by rfl) ⟨382775, by rfl⟩ : syracuseStep 2041469 = 765551) B765551
theorem B1288639 : Blo 603293 1288639 := bstep (se 1 (by rfl) ⟨966479, by rfl⟩ : syracuseStep 1288639 = 1932959) B1932959
theorem B1453159 : Blo 603293 1453159 := bstep (se 1 (by rfl) ⟨1089869, by rfl⟩ : syracuseStep 1453159 = 2179739) B2179739
theorem B6205673 : Blo 603293 6205673 := bstep (se 2 (by rfl) ⟨2327127, by rfl⟩ : syracuseStep 6205673 = 4654255) B4654255
theorem B12301375 : Blo 603293 12301375 := bstep (se 1 (by rfl) ⟨9226031, by rfl⟩ : syracuseStep 12301375 = 18452063) B18452063
theorem B603375 : Blo 603293 603375 := bstep (se 1 (by rfl) ⟨452531, by rfl⟩ : syracuseStep 603375 = 905063) B905063
theorem B3061151 : Blo 603293 3061151 := bstep (se 1 (by rfl) ⟨2295863, by rfl⟩ : syracuseStep 3061151 = 4591727) B4591727
theorem B2766251 : Blo 603293 2766251 := bstep (se 1 (by rfl) ⟨2074688, by rfl⟩ : syracuseStep 2766251 = 4149377) B4149377
theorem B603903 : Blo 603293 603903 := bstep (se 1 (by rfl) ⟨452927, by rfl⟩ : syracuseStep 603903 = 905855) B905855
theorem B604955 : Blo 603293 604955 := bstep (se 1 (by rfl) ⟨453716, by rfl⟩ : syracuseStep 604955 = 907433) B907433
theorem B605055 : Blo 603293 605055 := bstep (se 1 (by rfl) ⟨453791, by rfl⟩ : syracuseStep 605055 = 907583) B907583
theorem B605375 : Blo 603293 605375 := bstep (se 1 (by rfl) ⟨454031, by rfl⟩ : syracuseStep 605375 = 908063) B908063
theorem B1490815 : Blo 603293 1490815 := bstep (se 1 (by rfl) ⟨1118111, by rfl⟩ : syracuseStep 1490815 = 2236223) B2236223
theorem B606491 : Blo 603293 606491 := bstep (se 1 (by rfl) ⟨454868, by rfl⟩ : syracuseStep 606491 = 909737) B909737
theorem B2048327 : Blo 603293 2048327 := bstep (se 1 (by rfl) ⟨1536245, by rfl⟩ : syracuseStep 2048327 = 3072491) B3072491
theorem B607039 : Blo 603293 607039 := bstep (se 1 (by rfl) ⟨455279, by rfl⟩ : syracuseStep 607039 = 910559) B910559
theorem B607079 : Blo 603293 607079 := bstep (se 1 (by rfl) ⟨455309, by rfl⟩ : syracuseStep 607079 = 910619) B910619
theorem B5817865 : Blo 603293 5817865 := bstep (se 2 (by rfl) ⟨2181699, by rfl⟩ : syracuseStep 5817865 = 4363399) B4363399
theorem B29378213 : Blo 603293 29378213 := bstep (se 4 (by rfl) ⟨2754207, by rfl⟩ : syracuseStep 29378213 = 5508415) B5508415
theorem B1362347 : Blo 603293 1362347 := bstep (se 1 (by rfl) ⟨1021760, by rfl⟩ : syracuseStep 1362347 = 2043521) B2043521
theorem B6900713 : Blo 603293 6900713 := bstep (se 2 (by rfl) ⟨2587767, by rfl⟩ : syracuseStep 6900713 = 5175535) B5175535
theorem B63851651 : Blo 603293 63851651 := bstep (se 1 (by rfl) ⟨47888738, by rfl⟩ : syracuseStep 63851651 = 95777477) B95777477
theorem B26136107 : Blo 603293 26136107 := bstep (se 1 (by rfl) ⟨19602080, by rfl⟩ : syracuseStep 26136107 = 39204161) B39204161
theorem B1593599 : Blo 603293 1593599 := bstep (se 1 (by rfl) ⟨1195199, by rfl⟩ : syracuseStep 1593599 = 2390399) B2390399
theorem B1528703 : Blo 603293 1528703 := bstep (se 1 (by rfl) ⟨1146527, by rfl⟩ : syracuseStep 1528703 = 2293055) B2293055
theorem B907367 : Blo 603293 907367 := bstep (se 1 (by rfl) ⟨680525, by rfl⟩ : syracuseStep 907367 = 1361051) B1361051
theorem B1366271 : Blo 603293 1366271 := bstep (se 1 (by rfl) ⟨1024703, by rfl⟩ : syracuseStep 1366271 = 2049407) B2049407
theorem B1530191 : Blo 603293 1530191 := bstep (se 1 (by rfl) ⟨1147643, by rfl⟩ : syracuseStep 1530191 = 2295287) B2295287
theorem B908159 : Blo 603293 908159 := bstep (se 1 (by rfl) ⟨681119, by rfl⟩ : syracuseStep 908159 = 1362239) B1362239
theorem B908543 : Blo 603293 908543 := bstep (se 1 (by rfl) ⟨681407, by rfl⟩ : syracuseStep 908543 = 1362815) B1362815
theorem B909083 : Blo 603293 909083 := bstep (se 1 (by rfl) ⟨681812, by rfl⟩ : syracuseStep 909083 = 1363625) B1363625
theorem B909803 : Blo 603293 909803 := bstep (se 1 (by rfl) ⟨682352, by rfl⟩ : syracuseStep 909803 = 1364705) B1364705
theorem B909929 : Blo 603293 909929 := bstep (se 2 (by rfl) ⟨341223, by rfl⟩ : syracuseStep 909929 = 682447) B682447
theorem B14741261 : Blo 603293 14741261 := bstep (se 3 (by rfl) ⟨2763986, by rfl⟩ : syracuseStep 14741261 = 5527973) B5527973
theorem B1536155 : Blo 603293 1536155 := bstep (se 1 (by rfl) ⟨1152116, by rfl⟩ : syracuseStep 1536155 = 2304233) B2304233
theorem B1536479 : Blo 603293 1536479 := bstep (se 1 (by rfl) ⟨1152359, by rfl⟩ : syracuseStep 1536479 = 2304719) B2304719
theorem B5829245 : Blo 603293 5829245 := bstep (se 3 (by rfl) ⟨1092983, by rfl⟩ : syracuseStep 5829245 = 2185967) B2185967
theorem B2585513 : Blo 603293 2585513 := bstep (se 2 (by rfl) ⟨969567, by rfl⟩ : syracuseStep 2585513 = 1939135) B1939135
theorem B2913239 : Blo 603293 2913239 := bstep (se 1 (by rfl) ⟨2184929, by rfl⟩ : syracuseStep 2913239 = 4369859) B4369859
theorem B75757663 : Blo 603293 75757663 := bstep (se 1 (by rfl) ⟨56818247, by rfl⟩ : syracuseStep 75757663 = 113636495) B113636495
theorem B6881759 : Blo 603293 6881759 := bstep (se 1 (by rfl) ⟨5161319, by rfl⟩ : syracuseStep 6881759 = 10322639) B10322639
theorem B16548461 : Blo 603293 16548461 := bstep (se 3 (by rfl) ⟨3102836, by rfl⟩ : syracuseStep 16548461 = 6205673) B6205673
theorem B3933161 : Blo 603293 3933161 := bstep (se 2 (by rfl) ⟨1474935, by rfl⟩ : syracuseStep 3933161 = 2949871) B2949871
theorem B42567767 : Blo 603293 42567767 := bstep (se 1 (by rfl) ⟨31925825, by rfl⟩ : syracuseStep 42567767 = 63851651) B63851651
theorem B9308267 : Blo 603293 9308267 := bstep (se 1 (by rfl) ⟨6981200, by rfl⟩ : syracuseStep 9308267 = 13962401) B13962401
theorem B1575707 : Blo 603293 1575707 := bstep (se 1 (by rfl) ⟨1181780, by rfl⟩ : syracuseStep 1575707 = 2363561) B2363561
theorem B1019135 : Blo 603293 1019135 := bstep (se 1 (by rfl) ⟨764351, by rfl⟩ : syracuseStep 1019135 = 1528703) B1528703
theorem B7376669 : Blo 603293 7376669 := bstep (se 3 (by rfl) ⟨1383125, by rfl⟩ : syracuseStep 7376669 = 2766251) B2766251
theorem B1020127 : Blo 603293 1020127 := bstep (se 1 (by rfl) ⟨765095, by rfl⟩ : syracuseStep 1020127 = 1530191) B1530191
theorem B2299859 : Blo 603293 2299859 := bstep (se 1 (by rfl) ⟨1724894, by rfl⟩ : syracuseStep 2299859 = 3449789) B3449789
theorem B1024103 : Blo 603293 1024103 := bstep (se 1 (by rfl) ⟨768077, by rfl⟩ : syracuseStep 1024103 = 1536155) B1536155
theorem B1024319 : Blo 603293 1024319 := bstep (se 1 (by rfl) ⟨768239, by rfl⟩ : syracuseStep 1024319 = 1536479) B1536479
theorem B1942159 : Blo 603293 1942159 := bstep (se 1 (by rfl) ⟨1456619, by rfl⟩ : syracuseStep 1942159 = 2913239) B2913239
theorem B2040767 : Blo 603293 2040767 := bstep (se 1 (by rfl) ⟨1530575, by rfl⟩ : syracuseStep 2040767 = 3061151) B3061151
theorem B404040869 : Blo 603293 404040869 := bstep (se 4 (by rfl) ⟨37878831, by rfl⟩ : syracuseStep 404040869 = 75757663) B75757663
theorem B765931 : Blo 603293 765931 := bstep (se 1 (by rfl) ⟨574448, by rfl⟩ : syracuseStep 765931 = 1148897) B1148897
theorem B4600475 : Blo 603293 4600475 := bstep (se 1 (by rfl) ⟨3450356, by rfl⟩ : syracuseStep 4600475 = 6900713) B6900713
theorem B3060827 : Blo 603293 3060827 := bstep (se 1 (by rfl) ⟨2295620, by rfl⟩ : syracuseStep 3060827 = 4591241) B4591241
theorem B1718185 : Blo 603293 1718185 := bstep (se 2 (by rfl) ⟨644319, by rfl⟩ : syracuseStep 1718185 = 1288639) B1288639
theorem B604911 : Blo 603293 604911 := bstep (se 1 (by rfl) ⟨453683, by rfl⟩ : syracuseStep 604911 = 907367) B907367
theorem B605439 : Blo 603293 605439 := bstep (se 1 (by rfl) ⟨454079, by rfl⟩ : syracuseStep 605439 = 908159) B908159
theorem B1359161 : Blo 603293 1359161 := bstep (se 2 (by rfl) ⟨509685, by rfl⟩ : syracuseStep 1359161 = 1019371) B1019371
theorem B605695 : Blo 603293 605695 := bstep (se 1 (by rfl) ⟨454271, by rfl⟩ : syracuseStep 605695 = 908543) B908543
theorem B606055 : Blo 603293 606055 := bstep (se 1 (by rfl) ⟨454541, by rfl⟩ : syracuseStep 606055 = 909083) B909083
theorem B606535 : Blo 603293 606535 := bstep (se 1 (by rfl) ⟨454901, by rfl⟩ : syracuseStep 606535 = 909803) B909803
theorem B606619 : Blo 603293 606619 := bstep (se 1 (by rfl) ⟨454964, by rfl⟩ : syracuseStep 606619 = 909929) B909929
theorem B7750181 : Blo 603293 7750181 := bstep (se 4 (by rfl) ⟨726579, by rfl⟩ : syracuseStep 7750181 = 1453159) B1453159
theorem B1360979 : Blo 603293 1360979 := bstep (se 1 (by rfl) ⟨1020734, by rfl⟩ : syracuseStep 1360979 = 2041469) B2041469
theorem B16401833 : Blo 603293 16401833 := bstep (se 2 (by rfl) ⟨6150687, by rfl⟩ : syracuseStep 16401833 = 12301375) B12301375
theorem B3886163 : Blo 603293 3886163 := bstep (se 1 (by rfl) ⟨2914622, by rfl⟩ : syracuseStep 3886163 = 5829245) B5829245
theorem B1723675 : Blo 603293 1723675 := bstep (se 1 (by rfl) ⟨1292756, by rfl⟩ : syracuseStep 1723675 = 2585513) B2585513
theorem B1987753 : Blo 603293 1987753 := bstep (se 2 (by rfl) ⟨745407, by rfl⟩ : syracuseStep 1987753 = 1490815) B1490815
theorem B1365551 : Blo 603293 1365551 := bstep (se 1 (by rfl) ⟨1024163, by rfl⟩ : syracuseStep 1365551 = 2048327) B2048327
theorem B6903629 : Blo 603293 6903629 := bstep (se 3 (by rfl) ⟨1294430, by rfl⟩ : syracuseStep 6903629 = 2588861) B2588861
theorem B4249597 : Blo 603293 4249597 := bstep (se 3 (by rfl) ⟨796799, by rfl⟩ : syracuseStep 4249597 = 1593599) B1593599
theorem B19585475 : Blo 603293 19585475 := bstep (se 1 (by rfl) ⟨14689106, by rfl⟩ : syracuseStep 19585475 = 29378213) B29378213
theorem B908231 : Blo 603293 908231 := bstep (se 1 (by rfl) ⟨681173, by rfl⟩ : syracuseStep 908231 = 1362347) B1362347
theorem B7757153 : Blo 603293 7757153 := bstep (se 2 (by rfl) ⟨2908932, by rfl⟩ : syracuseStep 7757153 = 5817865) B5817865
theorem B9789103 : Blo 603293 9789103 := bstep (se 1 (by rfl) ⟨7341827, by rfl⟩ : syracuseStep 9789103 = 14683655) B14683655
theorem B3890879 : Blo 603293 3890879 := bstep (se 1 (by rfl) ⟨2918159, by rfl⟩ : syracuseStep 3890879 = 5836319) B5836319
theorem B17424071 : Blo 603293 17424071 := bstep (se 1 (by rfl) ⟨13068053, by rfl⟩ : syracuseStep 17424071 = 26136107) B26136107
theorem B910847 : Blo 603293 910847 := bstep (se 1 (by rfl) ⟨683135, by rfl⟩ : syracuseStep 910847 = 1366271) B1366271
theorem B9827507 : Blo 603293 9827507 := bstep (se 1 (by rfl) ⟨7370630, by rfl⟩ : syracuseStep 9827507 = 14741261) B14741261
theorem B8746633 : Blo 603293 8746633 := bstep (se 2 (by rfl) ⟨3279987, by rfl⟩ : syracuseStep 8746633 = 6559975) B6559975
theorem B4587839 : Blo 603293 4587839 := bstep (se 1 (by rfl) ⟨3440879, by rfl⟩ : syracuseStep 4587839 = 6881759) B6881759
theorem B2622107 : Blo 603293 2622107 := bstep (se 1 (by rfl) ⟨1966580, by rfl⟩ : syracuseStep 2622107 = 3933161) B3933161
theorem B2589545 : Blo 603293 2589545 := bstep (se 2 (by rfl) ⟨971079, by rfl⟩ : syracuseStep 2589545 = 1942159) B1942159
theorem B28378511 : Blo 603293 28378511 := bstep (se 1 (by rfl) ⟨21283883, by rfl⟩ : syracuseStep 28378511 = 42567767) B42567767
theorem B2590775 : Blo 603293 2590775 := bstep (se 1 (by rfl) ⟨1943081, by rfl⟩ : syracuseStep 2590775 = 3886163) B3886163
theorem B4917779 : Blo 603293 4917779 := bstep (se 1 (by rfl) ⟨3688334, by rfl⟩ : syracuseStep 4917779 = 7376669) B7376669
theorem B2298233 : Blo 603293 2298233 := bstep (se 2 (by rfl) ⟨861837, by rfl⟩ : syracuseStep 2298233 = 1723675) B1723675
theorem B174952885 : Blo 603293 174952885 := bstep (se 5 (by rfl) ⟨8200916, by rfl⟩ : syracuseStep 174952885 = 16401833) B16401833
theorem B2593919 : Blo 603293 2593919 := bstep (se 1 (by rfl) ⟨1945439, by rfl⟩ : syracuseStep 2593919 = 3890879) B3890879
theorem B1021241 : Blo 603293 1021241 := bstep (se 2 (by rfl) ⟨382965, by rfl⟩ : syracuseStep 1021241 = 765931) B765931
theorem B4201885 : Blo 603293 4201885 := bstep (se 3 (by rfl) ⟨787853, by rfl⟩ : syracuseStep 4201885 = 1575707) B1575707
theorem B269360579 : Blo 603293 269360579 := bstep (se 1 (by rfl) ⟨202020434, by rfl⟩ : syracuseStep 269360579 = 404040869) B404040869
theorem B2040551 : Blo 603293 2040551 := bstep (se 1 (by rfl) ⟨1530413, by rfl⟩ : syracuseStep 2040551 = 3060827) B3060827
theorem B13052137 : Blo 603293 13052137 := bstep (se 2 (by rfl) ⟨4894551, by rfl⟩ : syracuseStep 13052137 = 9789103) B9789103
theorem B6205511 : Blo 603293 6205511 := bstep (se 1 (by rfl) ⟨4654133, by rfl⟩ : syracuseStep 6205511 = 9308267) B9308267
theorem B4602419 : Blo 603293 4602419 := bstep (se 1 (by rfl) ⟨3451814, by rfl⟩ : syracuseStep 4602419 = 6903629) B6903629
theorem B13056983 : Blo 603293 13056983 := bstep (se 1 (by rfl) ⟨9792737, by rfl⟩ : syracuseStep 13056983 = 19585475) B19585475
theorem B605487 : Blo 603293 605487 := bstep (se 1 (by rfl) ⟨454115, by rfl⟩ : syracuseStep 605487 = 908231) B908231
theorem B11616047 : Blo 603293 11616047 := bstep (se 1 (by rfl) ⟨8712035, by rfl⟩ : syracuseStep 11616047 = 17424071) B17424071
theorem B1360169 : Blo 603293 1360169 := bstep (se 2 (by rfl) ⟨510063, by rfl⟩ : syracuseStep 1360169 = 1020127) B1020127
theorem B1360511 : Blo 603293 1360511 := bstep (se 1 (by rfl) ⟨1020383, by rfl⟩ : syracuseStep 1360511 = 2040767) B2040767
theorem B607231 : Blo 603293 607231 := bstep (se 1 (by rfl) ⟨455423, by rfl⟩ : syracuseStep 607231 = 910847) B910847
theorem B3066983 : Blo 603293 3066983 := bstep (se 1 (by rfl) ⟨2300237, by rfl⟩ : syracuseStep 3066983 = 4600475) B4600475
theorem B906107 : Blo 603293 906107 := bstep (se 1 (by rfl) ⟨679580, by rfl⟩ : syracuseStep 906107 = 1359161) B1359161
theorem B5166787 : Blo 603293 5166787 := bstep (se 1 (by rfl) ⟨3875090, by rfl⟩ : syracuseStep 5166787 = 7750181) B7750181
theorem B11032307 : Blo 603293 11032307 := bstep (se 1 (by rfl) ⟨8274230, by rfl⟩ : syracuseStep 11032307 = 16548461) B16548461
theorem B907319 : Blo 603293 907319 := bstep (se 1 (by rfl) ⟨680489, by rfl⟩ : syracuseStep 907319 = 1360979) B1360979
theorem B679423 : Blo 603293 679423 := bstep (se 1 (by rfl) ⟨509567, by rfl⟩ : syracuseStep 679423 = 1019135) B1019135
theorem B26206685 : Blo 603293 26206685 := bstep (se 3 (by rfl) ⟨4913753, by rfl⟩ : syracuseStep 26206685 = 9827507) B9827507
theorem B910367 : Blo 603293 910367 := bstep (se 1 (by rfl) ⟨682775, by rfl⟩ : syracuseStep 910367 = 1365551) B1365551
theorem B1533239 : Blo 603293 1533239 := bstep (se 1 (by rfl) ⟨1149929, by rfl⟩ : syracuseStep 1533239 = 2299859) B2299859
theorem B5171435 : Blo 603293 5171435 := bstep (se 1 (by rfl) ⟨3878576, by rfl⟩ : syracuseStep 5171435 = 7757153) B7757153
theorem B682735 : Blo 603293 682735 := bstep (se 1 (by rfl) ⟨512051, by rfl⟩ : syracuseStep 682735 = 1024103) B1024103
theorem B682879 : Blo 603293 682879 := bstep (se 1 (by rfl) ⟨512159, by rfl⟩ : syracuseStep 682879 = 1024319) B1024319
theorem B2650337 : Blo 603293 2650337 := bstep (se 2 (by rfl) ⟨993876, by rfl⟩ : syracuseStep 2650337 = 1987753) B1987753
theorem B11662177 : Blo 603293 11662177 := bstep (se 2 (by rfl) ⟨4373316, by rfl⟩ : syracuseStep 11662177 = 8746633) B8746633
theorem B2290913 : Blo 603293 2290913 := bstep (se 2 (by rfl) ⟨859092, by rfl⟩ : syracuseStep 2290913 = 1718185) B1718185
theorem B5666129 : Blo 603293 5666129 := bstep (se 2 (by rfl) ⟨2124798, by rfl⟩ : syracuseStep 5666129 = 4249597) B4249597
theorem B3278519 : Blo 603293 3278519 := bstep (se 1 (by rfl) ⟨2458889, by rfl⟩ : syracuseStep 3278519 = 4917779) B4917779
theorem B17402849 : Blo 603293 17402849 := bstep (se 2 (by rfl) ⟨6526068, by rfl⟩ : syracuseStep 17402849 = 13052137) B13052137
theorem B17471123 : Blo 603293 17471123 := bstep (se 1 (by rfl) ⟨13103342, by rfl⟩ : syracuseStep 17471123 = 26206685) B26206685
theorem B1022159 : Blo 603293 1022159 := bstep (se 1 (by rfl) ⟨766619, by rfl⟩ : syracuseStep 1022159 = 1533239) B1533239
theorem B3447623 : Blo 603293 3447623 := bstep (se 1 (by rfl) ⟨2585717, by rfl⟩ : syracuseStep 3447623 = 5171435) B5171435
theorem B6889049 : Blo 603293 6889049 := bstep (se 2 (by rfl) ⟨2583393, by rfl⟩ : syracuseStep 6889049 = 5166787) B5166787
theorem B4137007 : Blo 603293 4137007 := bstep (se 1 (by rfl) ⟨3102755, by rfl⟩ : syracuseStep 4137007 = 6205511) B6205511
theorem B3777419 : Blo 603293 3777419 := bstep (se 1 (by rfl) ⟨2833064, by rfl⟩ : syracuseStep 3777419 = 5666129) B5666129
theorem B7744031 : Blo 603293 7744031 := bstep (se 1 (by rfl) ⟨5808023, by rfl⟩ : syracuseStep 7744031 = 11616047) B11616047
theorem B3058559 : Blo 603293 3058559 := bstep (se 1 (by rfl) ⟨2293919, by rfl⟩ : syracuseStep 3058559 = 4587839) B4587839
theorem B1748071 : Blo 603293 1748071 := bstep (se 1 (by rfl) ⟨1311053, by rfl⟩ : syracuseStep 1748071 = 2622107) B2622107
theorem B18919007 : Blo 603293 18919007 := bstep (se 1 (by rfl) ⟨14189255, by rfl⟩ : syracuseStep 18919007 = 28378511) B28378511
theorem B2044655 : Blo 603293 2044655 := bstep (se 1 (by rfl) ⟨1533491, by rfl⟩ : syracuseStep 2044655 = 3066983) B3066983
theorem B604071 : Blo 603293 604071 := bstep (se 1 (by rfl) ⟨453053, by rfl⟩ : syracuseStep 604071 = 906107) B906107
theorem B7354871 : Blo 603293 7354871 := bstep (se 1 (by rfl) ⟨5516153, by rfl⟩ : syracuseStep 7354871 = 11032307) B11032307
theorem B604879 : Blo 603293 604879 := bstep (se 1 (by rfl) ⟨453659, by rfl⟩ : syracuseStep 604879 = 907319) B907319
theorem B1360367 : Blo 603293 1360367 := bstep (se 1 (by rfl) ⟨1020275, by rfl⟩ : syracuseStep 1360367 = 2040551) B2040551
theorem B606911 : Blo 603293 606911 := bstep (se 1 (by rfl) ⟨455183, by rfl⟩ : syracuseStep 606911 = 910367) B910367
theorem B15549569 : Blo 603293 15549569 := bstep (se 2 (by rfl) ⟨5831088, by rfl⟩ : syracuseStep 15549569 = 11662177) B11662177
theorem B1527275 : Blo 603293 1527275 := bstep (se 1 (by rfl) ⟨1145456, by rfl⟩ : syracuseStep 1527275 = 2290913) B2290913
theorem B718294877 : Blo 603293 718294877 := bstep (se 3 (by rfl) ⟨134680289, by rfl⟩ : syracuseStep 718294877 = 269360579) B269360579
theorem B3068279 : Blo 603293 3068279 := bstep (se 1 (by rfl) ⟨2301209, by rfl⟩ : syracuseStep 3068279 = 4602419) B4602419
theorem B8704655 : Blo 603293 8704655 := bstep (se 1 (by rfl) ⟨6528491, by rfl⟩ : syracuseStep 8704655 = 13056983) B13056983
theorem B905897 : Blo 603293 905897 := bstep (se 2 (by rfl) ⟨339711, by rfl⟩ : syracuseStep 905897 = 679423) B679423
theorem B906779 : Blo 603293 906779 := bstep (se 1 (by rfl) ⟨680084, by rfl⟩ : syracuseStep 906779 = 1360169) B1360169
theorem B907007 : Blo 603293 907007 := bstep (se 1 (by rfl) ⟨680255, by rfl⟩ : syracuseStep 907007 = 1360511) B1360511
theorem B1726363 : Blo 603293 1726363 := bstep (se 1 (by rfl) ⟨1294772, by rfl⟩ : syracuseStep 1726363 = 2589545) B2589545
theorem B1727183 : Blo 603293 1727183 := bstep (se 1 (by rfl) ⟨1295387, by rfl⟩ : syracuseStep 1727183 = 2590775) B2590775
theorem B1532155 : Blo 603293 1532155 := bstep (se 1 (by rfl) ⟨1149116, by rfl⟩ : syracuseStep 1532155 = 2298233) B2298233
theorem B1729279 : Blo 603293 1729279 := bstep (se 1 (by rfl) ⟨1296959, by rfl⟩ : syracuseStep 1729279 = 2593919) B2593919
theorem B680827 : Blo 603293 680827 := bstep (se 1 (by rfl) ⟨510620, by rfl⟩ : syracuseStep 680827 = 1021241) B1021241
theorem B910313 : Blo 603293 910313 := bstep (se 2 (by rfl) ⟨341367, by rfl⟩ : syracuseStep 910313 = 682735) B682735
theorem B910505 : Blo 603293 910505 := bstep (se 2 (by rfl) ⟨341439, by rfl⟩ : syracuseStep 910505 = 682879) B682879
theorem B233270513 : Blo 603293 233270513 := bstep (se 2 (by rfl) ⟨87476442, by rfl⟩ : syracuseStep 233270513 = 174952885) B174952885
theorem B22410053 : Blo 603293 22410053 := bstep (se 4 (by rfl) ⟨2100942, by rfl⟩ : syracuseStep 22410053 = 4201885) B4201885
theorem B1766891 : Blo 603293 1766891 := bstep (se 1 (by rfl) ⟨1325168, by rfl⟩ : syracuseStep 1766891 = 2650337) B2650337
theorem B11601899 : Blo 603293 11601899 := bstep (se 1 (by rfl) ⟨8701424, by rfl⟩ : syracuseStep 11601899 = 17402849) B17402849
theorem B1018183 : Blo 603293 1018183 := bstep (se 1 (by rfl) ⟨763637, by rfl⟩ : syracuseStep 1018183 = 1527275) B1527275
theorem B5803103 : Blo 603293 5803103 := bstep (se 1 (by rfl) ⟨4352327, by rfl⟩ : syracuseStep 5803103 = 8704655) B8704655
theorem B2298415 : Blo 603293 2298415 := bstep (se 1 (by rfl) ⟨1723811, by rfl⟩ : syracuseStep 2298415 = 3447623) B3447623
theorem B4592699 : Blo 603293 4592699 := bstep (se 1 (by rfl) ⟨3444524, by rfl⟩ : syracuseStep 4592699 = 6889049) B6889049
theorem B2039039 : Blo 603293 2039039 := bstep (se 1 (by rfl) ⟨1529279, by rfl⟩ : syracuseStep 2039039 = 3058559) B3058559
theorem B2301817 : Blo 603293 2301817 := bstep (se 2 (by rfl) ⟨863181, by rfl⟩ : syracuseStep 2301817 = 1726363) B1726363
theorem B5516009 : Blo 603293 5516009 := bstep (se 2 (by rfl) ⟨2068503, by rfl⟩ : syracuseStep 5516009 = 4137007) B4137007
theorem B2042873 : Blo 603293 2042873 := bstep (se 2 (by rfl) ⟨766077, by rfl⟩ : syracuseStep 2042873 = 1532155) B1532155
theorem B10366379 : Blo 603293 10366379 := bstep (se 1 (by rfl) ⟨7774784, by rfl⟩ : syracuseStep 10366379 = 15549569) B15549569
theorem B2305705 : Blo 603293 2305705 := bstep (se 2 (by rfl) ⟨864639, by rfl⟩ : syracuseStep 2305705 = 1729279) B1729279
theorem B10073117 : Blo 603293 10073117 := bstep (se 3 (by rfl) ⟨1888709, by rfl⟩ : syracuseStep 10073117 = 3777419) B3777419
theorem B2045519 : Blo 603293 2045519 := bstep (se 1 (by rfl) ⟨1534139, by rfl⟩ : syracuseStep 2045519 = 3068279) B3068279
theorem B603931 : Blo 603293 603931 := bstep (se 1 (by rfl) ⟨452948, by rfl⟩ : syracuseStep 603931 = 905897) B905897
theorem B604519 : Blo 603293 604519 := bstep (se 1 (by rfl) ⟨453389, by rfl⟩ : syracuseStep 604519 = 906779) B906779
theorem B11647415 : Blo 603293 11647415 := bstep (se 1 (by rfl) ⟨8735561, by rfl⟩ : syracuseStep 11647415 = 17471123) B17471123
theorem B604671 : Blo 603293 604671 := bstep (se 1 (by rfl) ⟨453503, by rfl⟩ : syracuseStep 604671 = 907007) B907007
theorem B9323045 : Blo 603293 9323045 := bstep (se 4 (by rfl) ⟨874035, by rfl⟩ : syracuseStep 9323045 = 1748071) B1748071
theorem B606875 : Blo 603293 606875 := bstep (se 1 (by rfl) ⟨455156, by rfl⟩ : syracuseStep 606875 = 910313) B910313
theorem B607003 : Blo 603293 607003 := bstep (se 1 (by rfl) ⟨455252, by rfl⟩ : syracuseStep 607003 = 910505) B910505
theorem B5162687 : Blo 603293 5162687 := bstep (se 1 (by rfl) ⟨3872015, by rfl⟩ : syracuseStep 5162687 = 7744031) B7744031
theorem B4605821 : Blo 603293 4605821 := bstep (se 3 (by rfl) ⟨863591, by rfl⟩ : syracuseStep 4605821 = 1727183) B1727183
theorem B1363103 : Blo 603293 1363103 := bstep (se 1 (by rfl) ⟨1022327, by rfl⟩ : syracuseStep 1363103 = 2044655) B2044655
theorem B4903247 : Blo 603293 4903247 := bstep (se 1 (by rfl) ⟨3677435, by rfl⟩ : syracuseStep 4903247 = 7354871) B7354871
theorem B906911 : Blo 603293 906911 := bstep (se 1 (by rfl) ⟨680183, by rfl⟩ : syracuseStep 906911 = 1360367) B1360367
theorem B2185679 : Blo 603293 2185679 := bstep (se 1 (by rfl) ⟨1639259, by rfl⟩ : syracuseStep 2185679 = 3278519) B3278519
theorem B907769 : Blo 603293 907769 := bstep (se 2 (by rfl) ⟨340413, by rfl⟩ : syracuseStep 907769 = 680827) B680827
theorem B478863251 : Blo 603293 478863251 := bstep (se 1 (by rfl) ⟨359147438, by rfl⟩ : syracuseStep 478863251 = 718294877) B718294877
theorem B4711709 : Blo 603293 4711709 := bstep (se 3 (by rfl) ⟨883445, by rfl⟩ : syracuseStep 4711709 = 1766891) B1766891
theorem B681439 : Blo 603293 681439 := bstep (se 1 (by rfl) ⟨511079, by rfl⟩ : syracuseStep 681439 = 1022159) B1022159
theorem B155513675 : Blo 603293 155513675 := bstep (se 1 (by rfl) ⟨116635256, by rfl⟩ : syracuseStep 155513675 = 233270513) B233270513
theorem B12612671 : Blo 603293 12612671 := bstep (se 1 (by rfl) ⟨9459503, by rfl⟩ : syracuseStep 12612671 = 18919007) B18919007
theorem B14940035 : Blo 603293 14940035 := bstep (se 1 (by rfl) ⟨11205026, by rfl⟩ : syracuseStep 14940035 = 22410053) B22410053
theorem B3441791 : Blo 603293 3441791 := bstep (se 1 (by rfl) ⟨2581343, by rfl⟩ : syracuseStep 3441791 = 5162687) B5162687
theorem B7734599 : Blo 603293 7734599 := bstep (se 1 (by rfl) ⟨5800949, by rfl⟩ : syracuseStep 7734599 = 11601899) B11601899
theorem B3868735 : Blo 603293 3868735 := bstep (se 1 (by rfl) ⟨2901551, by rfl⟩ : syracuseStep 3868735 = 5803103) B5803103
theorem B3677339 : Blo 603293 3677339 := bstep (se 1 (by rfl) ⟨2758004, by rfl⟩ : syracuseStep 3677339 = 5516009) B5516009
theorem B1357577 : Blo 603293 1357577 := bstep (se 2 (by rfl) ⟨509091, by rfl⟩ : syracuseStep 1357577 = 1018183) B1018183
theorem B3061799 : Blo 603293 3061799 := bstep (se 1 (by rfl) ⟨2296349, by rfl⟩ : syracuseStep 3061799 = 4592699) B4592699
theorem B12564557 : Blo 603293 12564557 := bstep (se 3 (by rfl) ⟨2355854, by rfl⟩ : syracuseStep 12564557 = 4711709) B4711709
theorem B604607 : Blo 603293 604607 := bstep (se 1 (by rfl) ⟨453455, by rfl⟩ : syracuseStep 604607 = 906911) B906911
theorem B1457119 : Blo 603293 1457119 := bstep (se 1 (by rfl) ⟨1092839, by rfl⟩ : syracuseStep 1457119 = 2185679) B2185679
theorem B605179 : Blo 603293 605179 := bstep (se 1 (by rfl) ⟨453884, by rfl⟩ : syracuseStep 605179 = 907769) B907769
theorem B1359359 : Blo 603293 1359359 := bstep (se 1 (by rfl) ⟨1019519, by rfl⟩ : syracuseStep 1359359 = 2039039) B2039039
theorem B319242167 : Blo 603293 319242167 := bstep (se 1 (by rfl) ⟨239431625, by rfl⟩ : syracuseStep 319242167 = 478863251) B478863251
theorem B3064553 : Blo 603293 3064553 := bstep (se 2 (by rfl) ⟨1149207, by rfl⟩ : syracuseStep 3064553 = 2298415) B2298415
theorem B1361915 : Blo 603293 1361915 := bstep (se 1 (by rfl) ⟨1021436, by rfl⟩ : syracuseStep 1361915 = 2042873) B2042873
theorem B8408447 : Blo 603293 8408447 := bstep (se 1 (by rfl) ⟨6306335, by rfl⟩ : syracuseStep 8408447 = 12612671) B12612671
theorem B1363679 : Blo 603293 1363679 := bstep (se 1 (by rfl) ⟨1022759, by rfl⟩ : syracuseStep 1363679 = 2045519) B2045519
theorem B3069089 : Blo 603293 3069089 := bstep (se 2 (by rfl) ⟨1150908, by rfl⟩ : syracuseStep 3069089 = 2301817) B2301817
theorem B6215363 : Blo 603293 6215363 := bstep (se 1 (by rfl) ⟨4661522, by rfl⟩ : syracuseStep 6215363 = 9323045) B9323045
theorem B3070547 : Blo 603293 3070547 := bstep (se 1 (by rfl) ⟨2302910, by rfl⟩ : syracuseStep 3070547 = 4605821) B4605821
theorem B908585 : Blo 603293 908585 := bstep (se 2 (by rfl) ⟨340719, by rfl⟩ : syracuseStep 908585 = 681439) B681439
theorem B908735 : Blo 603293 908735 := bstep (se 1 (by rfl) ⟨681551, by rfl⟩ : syracuseStep 908735 = 1363103) B1363103
theorem B26861645 : Blo 603293 26861645 := bstep (se 3 (by rfl) ⟨5036558, by rfl⟩ : syracuseStep 26861645 = 10073117) B10073117
theorem B3268831 : Blo 603293 3268831 := bstep (se 1 (by rfl) ⟨2451623, by rfl⟩ : syracuseStep 3268831 = 4903247) B4903247
theorem B3074273 : Blo 603293 3074273 := bstep (se 2 (by rfl) ⟨1152852, by rfl⟩ : syracuseStep 3074273 = 2305705) B2305705
theorem B6910919 : Blo 603293 6910919 := bstep (se 1 (by rfl) ⟨5183189, by rfl⟩ : syracuseStep 6910919 = 10366379) B10366379
theorem B103675783 : Blo 603293 103675783 := bstep (se 1 (by rfl) ⟨77756837, by rfl⟩ : syracuseStep 103675783 = 155513675) B155513675
theorem B9960023 : Blo 603293 9960023 := bstep (se 1 (by rfl) ⟨7470017, by rfl⟩ : syracuseStep 9960023 = 14940035) B14940035
theorem B7764943 : Blo 603293 7764943 := bstep (se 1 (by rfl) ⟨5823707, by rfl⟩ : syracuseStep 7764943 = 11647415) B11647415
theorem B71631053 : Blo 603293 71631053 := bstep (se 3 (by rfl) ⟨13430822, by rfl⟩ : syracuseStep 71631053 = 26861645) B26861645
theorem B4358441 : Blo 603293 4358441 := bstep (se 2 (by rfl) ⟨1634415, by rfl⟩ : syracuseStep 4358441 = 3268831) B3268831
theorem B2294527 : Blo 603293 2294527 := bstep (se 1 (by rfl) ⟨1720895, by rfl⟩ : syracuseStep 2294527 = 3441791) B3441791
theorem B5605631 : Blo 603293 5605631 := bstep (se 1 (by rfl) ⟨4204223, by rfl⟩ : syracuseStep 5605631 = 8408447) B8408447
theorem B7771301 : Blo 603293 7771301 := bstep (se 4 (by rfl) ⟨728559, by rfl⟩ : syracuseStep 7771301 = 1457119) B1457119
theorem B2041199 : Blo 603293 2041199 := bstep (se 1 (by rfl) ⟨1530899, by rfl⟩ : syracuseStep 2041199 = 3061799) B3061799
theorem B2043035 : Blo 603293 2043035 := bstep (se 1 (by rfl) ⟨1532276, by rfl⟩ : syracuseStep 2043035 = 3064553) B3064553
theorem B5156399 : Blo 603293 5156399 := bstep (se 1 (by rfl) ⟨3867299, by rfl⟩ : syracuseStep 5156399 = 7734599) B7734599
theorem B5158313 : Blo 603293 5158313 := bstep (se 2 (by rfl) ⟨1934367, by rfl⟩ : syracuseStep 5158313 = 3868735) B3868735
theorem B2046059 : Blo 603293 2046059 := bstep (se 1 (by rfl) ⟨1534544, by rfl⟩ : syracuseStep 2046059 = 3069089) B3069089
theorem B4143575 : Blo 603293 4143575 := bstep (se 1 (by rfl) ⟨3107681, by rfl⟩ : syracuseStep 4143575 = 6215363) B6215363
theorem B2047031 : Blo 603293 2047031 := bstep (se 1 (by rfl) ⟨1535273, by rfl⟩ : syracuseStep 2047031 = 3070547) B3070547
theorem B605723 : Blo 603293 605723 := bstep (se 1 (by rfl) ⟨454292, by rfl⟩ : syracuseStep 605723 = 908585) B908585
theorem B605823 : Blo 603293 605823 := bstep (se 1 (by rfl) ⟨454367, by rfl⟩ : syracuseStep 605823 = 908735) B908735
theorem B2049515 : Blo 603293 2049515 := bstep (se 1 (by rfl) ⟨1537136, by rfl⟩ : syracuseStep 2049515 = 3074273) B3074273
theorem B138234377 : Blo 603293 138234377 := bstep (se 2 (by rfl) ⟨51837891, by rfl⟩ : syracuseStep 138234377 = 103675783) B103675783
theorem B4607279 : Blo 603293 4607279 := bstep (se 1 (by rfl) ⟨3455459, by rfl⟩ : syracuseStep 4607279 = 6910919) B6910919
theorem B905051 : Blo 603293 905051 := bstep (se 1 (by rfl) ⟨678788, by rfl⟩ : syracuseStep 905051 = 1357577) B1357577
theorem B8376371 : Blo 603293 8376371 := bstep (se 1 (by rfl) ⟨6282278, by rfl⟩ : syracuseStep 8376371 = 12564557) B12564557
theorem B6640015 : Blo 603293 6640015 := bstep (se 1 (by rfl) ⟨4980011, by rfl⟩ : syracuseStep 6640015 = 9960023) B9960023
theorem B906239 : Blo 603293 906239 := bstep (se 1 (by rfl) ⟨679679, by rfl⟩ : syracuseStep 906239 = 1359359) B1359359
theorem B907943 : Blo 603293 907943 := bstep (se 1 (by rfl) ⟨680957, by rfl⟩ : syracuseStep 907943 = 1361915) B1361915
theorem B909119 : Blo 603293 909119 := bstep (se 1 (by rfl) ⟨681839, by rfl⟩ : syracuseStep 909119 = 1363679) B1363679
theorem B2451559 : Blo 603293 2451559 := bstep (se 1 (by rfl) ⟨1838669, by rfl⟩ : syracuseStep 2451559 = 3677339) B3677339
theorem B10353257 : Blo 603293 10353257 := bstep (se 2 (by rfl) ⟨3882471, by rfl⟩ : syracuseStep 10353257 = 7764943) B7764943
theorem B212828111 : Blo 603293 212828111 := bstep (se 1 (by rfl) ⟨159621083, by rfl⟩ : syracuseStep 212828111 = 319242167) B319242167
theorem B3737087 : Blo 603293 3737087 := bstep (se 1 (by rfl) ⟨2802815, by rfl⟩ : syracuseStep 3737087 = 5605631) B5605631
theorem B5180867 : Blo 603293 5180867 := bstep (se 1 (by rfl) ⟨3885650, by rfl⟩ : syracuseStep 5180867 = 7771301) B7771301
theorem B8853353 : Blo 603293 8853353 := bstep (se 2 (by rfl) ⟨3320007, by rfl⟩ : syracuseStep 8853353 = 6640015) B6640015
theorem B2762383 : Blo 603293 2762383 := bstep (se 1 (by rfl) ⟨2071787, by rfl⟩ : syracuseStep 2762383 = 4143575) B4143575
theorem B47754035 : Blo 603293 47754035 := bstep (se 1 (by rfl) ⟨35815526, by rfl⟩ : syracuseStep 47754035 = 71631053) B71631053
theorem B3059369 : Blo 603293 3059369 := bstep (se 2 (by rfl) ⟨1147263, by rfl⟩ : syracuseStep 3059369 = 2294527) B2294527
theorem B92156251 : Blo 603293 92156251 := bstep (se 1 (by rfl) ⟨69117188, by rfl⟩ : syracuseStep 92156251 = 138234377) B138234377
theorem B603367 : Blo 603293 603367 := bstep (se 1 (by rfl) ⟨452525, by rfl⟩ : syracuseStep 603367 = 905051) B905051
theorem B5584247 : Blo 603293 5584247 := bstep (se 1 (by rfl) ⟨4188185, by rfl⟩ : syracuseStep 5584247 = 8376371) B8376371
theorem B604159 : Blo 603293 604159 := bstep (se 1 (by rfl) ⟨453119, by rfl⟩ : syracuseStep 604159 = 906239) B906239
theorem B605295 : Blo 603293 605295 := bstep (se 1 (by rfl) ⟨453971, by rfl⟩ : syracuseStep 605295 = 907943) B907943
theorem B606079 : Blo 603293 606079 := bstep (se 1 (by rfl) ⟨454559, by rfl⟩ : syracuseStep 606079 = 909119) B909119
theorem B1360799 : Blo 603293 1360799 := bstep (se 1 (by rfl) ⟨1020599, by rfl⟩ : syracuseStep 1360799 = 2041199) B2041199
theorem B1362023 : Blo 603293 1362023 := bstep (se 1 (by rfl) ⟨1021517, by rfl⟩ : syracuseStep 1362023 = 2043035) B2043035
theorem B1364039 : Blo 603293 1364039 := bstep (se 1 (by rfl) ⟨1023029, by rfl⟩ : syracuseStep 1364039 = 2046059) B2046059
theorem B6902171 : Blo 603293 6902171 := bstep (se 1 (by rfl) ⟨5176628, by rfl⟩ : syracuseStep 6902171 = 10353257) B10353257
theorem B1364687 : Blo 603293 1364687 := bstep (se 1 (by rfl) ⟨1023515, by rfl⟩ : syracuseStep 1364687 = 2047031) B2047031
theorem B2905627 : Blo 603293 2905627 := bstep (se 1 (by rfl) ⟨2179220, by rfl⟩ : syracuseStep 2905627 = 4358441) B4358441
theorem B1366343 : Blo 603293 1366343 := bstep (se 1 (by rfl) ⟨1024757, by rfl⟩ : syracuseStep 1366343 = 2049515) B2049515
theorem B3071519 : Blo 603293 3071519 := bstep (se 1 (by rfl) ⟨2303639, by rfl⟩ : syracuseStep 3071519 = 4607279) B4607279
theorem B3268745 : Blo 603293 3268745 := bstep (se 2 (by rfl) ⟨1225779, by rfl⟩ : syracuseStep 3268745 = 2451559) B2451559
theorem B3437599 : Blo 603293 3437599 := bstep (se 1 (by rfl) ⟨2578199, by rfl⟩ : syracuseStep 3437599 = 5156399) B5156399
theorem B3438875 : Blo 603293 3438875 := bstep (se 1 (by rfl) ⟨2579156, by rfl⟩ : syracuseStep 3438875 = 5158313) B5158313
theorem B141885407 : Blo 603293 141885407 := bstep (se 1 (by rfl) ⟨106414055, by rfl⟩ : syracuseStep 141885407 = 212828111) B212828111
theorem B2491391 : Blo 603293 2491391 := bstep (se 1 (by rfl) ⟨1868543, by rfl⟩ : syracuseStep 2491391 = 3737087) B3737087
theorem B5902235 : Blo 603293 5902235 := bstep (se 1 (by rfl) ⟨4426676, by rfl⟩ : syracuseStep 5902235 = 8853353) B8853353
theorem B3874169 : Blo 603293 3874169 := bstep (se 2 (by rfl) ⟨1452813, by rfl⟩ : syracuseStep 3874169 = 2905627) B2905627
theorem B2039579 : Blo 603293 2039579 := bstep (se 1 (by rfl) ⟨1529684, by rfl⟩ : syracuseStep 2039579 = 3059369) B3059369
theorem B3683177 : Blo 603293 3683177 := bstep (se 2 (by rfl) ⟨1381191, by rfl⟩ : syracuseStep 3683177 = 2762383) B2762383
theorem B3453911 : Blo 603293 3453911 := bstep (se 1 (by rfl) ⟨2590433, by rfl⟩ : syracuseStep 3453911 = 5180867) B5180867
theorem B4601447 : Blo 603293 4601447 := bstep (se 1 (by rfl) ⟨3451085, by rfl⟩ : syracuseStep 4601447 = 6902171) B6902171
theorem B2047679 : Blo 603293 2047679 := bstep (se 1 (by rfl) ⟨1535759, by rfl⟩ : syracuseStep 2047679 = 3071519) B3071519
theorem B2179163 : Blo 603293 2179163 := bstep (se 1 (by rfl) ⟨1634372, by rfl⟩ : syracuseStep 2179163 = 3268745) B3268745
theorem B31836023 : Blo 603293 31836023 := bstep (se 1 (by rfl) ⟨23877017, by rfl⟩ : syracuseStep 31836023 = 47754035) B47754035
theorem B3722831 : Blo 603293 3722831 := bstep (se 1 (by rfl) ⟨2792123, by rfl⟩ : syracuseStep 3722831 = 5584247) B5584247
theorem B94590271 : Blo 603293 94590271 := bstep (se 1 (by rfl) ⟨70942703, by rfl⟩ : syracuseStep 94590271 = 141885407) B141885407
theorem B907199 : Blo 603293 907199 := bstep (se 1 (by rfl) ⟨680399, by rfl⟩ : syracuseStep 907199 = 1360799) B1360799
theorem B908015 : Blo 603293 908015 := bstep (se 1 (by rfl) ⟨681011, by rfl⟩ : syracuseStep 908015 = 1362023) B1362023
theorem B909359 : Blo 603293 909359 := bstep (se 1 (by rfl) ⟨682019, by rfl⟩ : syracuseStep 909359 = 1364039) B1364039
theorem B909791 : Blo 603293 909791 := bstep (se 1 (by rfl) ⟨682343, by rfl⟩ : syracuseStep 909791 = 1364687) B1364687
theorem B910895 : Blo 603293 910895 := bstep (se 1 (by rfl) ⟨683171, by rfl⟩ : syracuseStep 910895 = 1366343) B1366343
theorem B122875001 : Blo 603293 122875001 := bstep (se 2 (by rfl) ⟨46078125, by rfl⟩ : syracuseStep 122875001 = 92156251) B92156251
theorem B4583465 : Blo 603293 4583465 := bstep (se 2 (by rfl) ⟨1718799, by rfl⟩ : syracuseStep 4583465 = 3437599) B3437599
theorem B2292583 : Blo 603293 2292583 := bstep (se 1 (by rfl) ⟨1719437, by rfl⟩ : syracuseStep 2292583 = 3438875) B3438875
theorem B3934823 : Blo 603293 3934823 := bstep (se 1 (by rfl) ⟨2951117, by rfl⟩ : syracuseStep 3934823 = 5902235) B5902235
theorem B3055643 : Blo 603293 3055643 := bstep (se 1 (by rfl) ⟨2291732, by rfl⟩ : syracuseStep 3055643 = 4583465) B4583465
theorem B2302607 : Blo 603293 2302607 := bstep (se 1 (by rfl) ⟨1726955, by rfl⟩ : syracuseStep 2302607 = 3453911) B3453911
theorem B3056777 : Blo 603293 3056777 := bstep (se 2 (by rfl) ⟨1146291, by rfl⟩ : syracuseStep 3056777 = 2292583) B2292583
theorem B5811101 : Blo 603293 5811101 := bstep (se 3 (by rfl) ⟨1089581, by rfl⟩ : syracuseStep 5811101 = 2179163) B2179163
theorem B604799 : Blo 603293 604799 := bstep (se 1 (by rfl) ⟨453599, by rfl⟩ : syracuseStep 604799 = 907199) B907199
theorem B605343 : Blo 603293 605343 := bstep (se 1 (by rfl) ⟨454007, by rfl⟩ : syracuseStep 605343 = 908015) B908015
theorem B1359719 : Blo 603293 1359719 := bstep (se 1 (by rfl) ⟨1019789, by rfl⟩ : syracuseStep 1359719 = 2039579) B2039579
theorem B606239 : Blo 603293 606239 := bstep (se 1 (by rfl) ⟨454679, by rfl⟩ : syracuseStep 606239 = 909359) B909359
theorem B606527 : Blo 603293 606527 := bstep (se 1 (by rfl) ⟨454895, by rfl⟩ : syracuseStep 606527 = 909791) B909791
theorem B607263 : Blo 603293 607263 := bstep (se 1 (by rfl) ⟨455447, by rfl⟩ : syracuseStep 607263 = 910895) B910895
theorem B3067631 : Blo 603293 3067631 := bstep (se 1 (by rfl) ⟨2300723, by rfl⟩ : syracuseStep 3067631 = 4601447) B4601447
theorem B1365119 : Blo 603293 1365119 := bstep (se 1 (by rfl) ⟨1023839, by rfl⟩ : syracuseStep 1365119 = 2047679) B2047679
theorem B1660927 : Blo 603293 1660927 := bstep (se 1 (by rfl) ⟨1245695, by rfl⟩ : syracuseStep 1660927 = 2491391) B2491391
theorem B21224015 : Blo 603293 21224015 := bstep (se 1 (by rfl) ⟨15918011, by rfl⟩ : syracuseStep 21224015 = 31836023) B31836023
theorem B2481887 : Blo 603293 2481887 := bstep (se 1 (by rfl) ⟨1861415, by rfl⟩ : syracuseStep 2481887 = 3722831) B3722831
theorem B2582779 : Blo 603293 2582779 := bstep (se 1 (by rfl) ⟨1937084, by rfl⟩ : syracuseStep 2582779 = 3874169) B3874169
theorem B126120361 : Blo 603293 126120361 := bstep (se 2 (by rfl) ⟨47295135, by rfl⟩ : syracuseStep 126120361 = 94590271) B94590271
theorem B81916667 : Blo 603293 81916667 := bstep (se 1 (by rfl) ⟨61437500, by rfl⟩ : syracuseStep 81916667 = 122875001) B122875001
theorem B2455451 : Blo 603293 2455451 := bstep (se 1 (by rfl) ⟨1841588, by rfl⟩ : syracuseStep 2455451 = 3683177) B3683177
theorem B3443705 : Blo 603293 3443705 := bstep (se 2 (by rfl) ⟨1291389, by rfl⟩ : syracuseStep 3443705 = 2582779) B2582779
theorem B2037095 : Blo 603293 2037095 := bstep (se 1 (by rfl) ⟨1527821, by rfl⟩ : syracuseStep 2037095 = 3055643) B3055643
theorem B2037851 : Blo 603293 2037851 := bstep (se 1 (by rfl) ⟨1528388, by rfl⟩ : syracuseStep 2037851 = 3056777) B3056777
theorem B10492861 : Blo 603293 10492861 := bstep (se 3 (by rfl) ⟨1967411, by rfl⟩ : syracuseStep 10492861 = 3934823) B3934823
theorem B3874067 : Blo 603293 3874067 := bstep (se 1 (by rfl) ⟨2905550, by rfl⟩ : syracuseStep 3874067 = 5811101) B5811101
theorem B2045087 : Blo 603293 2045087 := bstep (se 1 (by rfl) ⟨1533815, by rfl⟩ : syracuseStep 2045087 = 3067631) B3067631
theorem B1654591 : Blo 603293 1654591 := bstep (se 1 (by rfl) ⟨1240943, by rfl⟩ : syracuseStep 1654591 = 2481887) B2481887
theorem B2214569 : Blo 603293 2214569 := bstep (se 2 (by rfl) ⟨830463, by rfl⟩ : syracuseStep 2214569 = 1660927) B1660927
theorem B54611111 : Blo 603293 54611111 := bstep (se 1 (by rfl) ⟨40958333, by rfl⟩ : syracuseStep 54611111 = 81916667) B81916667
theorem B906479 : Blo 603293 906479 := bstep (se 1 (by rfl) ⟨679859, by rfl⟩ : syracuseStep 906479 = 1359719) B1359719
theorem B910079 : Blo 603293 910079 := bstep (se 1 (by rfl) ⟨682559, by rfl⟩ : syracuseStep 910079 = 1365119) B1365119
theorem B14149343 : Blo 603293 14149343 := bstep (se 1 (by rfl) ⟨10612007, by rfl⟩ : syracuseStep 14149343 = 21224015) B21224015
theorem B1535071 : Blo 603293 1535071 := bstep (se 1 (by rfl) ⟨1151303, by rfl⟩ : syracuseStep 1535071 = 2302607) B2302607
theorem B168160481 : Blo 603293 168160481 := bstep (se 2 (by rfl) ⟨63060180, by rfl⟩ : syracuseStep 168160481 = 126120361) B126120361
theorem B1636967 : Blo 603293 1636967 := bstep (se 1 (by rfl) ⟨1227725, by rfl⟩ : syracuseStep 1636967 = 2455451) B2455451
theorem B1476379 : Blo 603293 1476379 := bstep (se 1 (by rfl) ⟨1107284, by rfl⟩ : syracuseStep 1476379 = 2214569) B2214569
theorem B2295803 : Blo 603293 2295803 := bstep (se 1 (by rfl) ⟨1721852, by rfl⟩ : syracuseStep 2295803 = 3443705) B3443705
theorem B36407407 : Blo 603293 36407407 := bstep (se 1 (by rfl) ⟨27305555, by rfl⟩ : syracuseStep 36407407 = 54611111) B54611111
theorem B4365245 : Blo 603293 4365245 := bstep (se 3 (by rfl) ⟨818483, by rfl⟩ : syracuseStep 4365245 = 1636967) B1636967
theorem B112106987 : Blo 603293 112106987 := bstep (se 1 (by rfl) ⟨84080240, by rfl⟩ : syracuseStep 112106987 = 168160481) B168160481
theorem B2206121 : Blo 603293 2206121 := bstep (se 2 (by rfl) ⟨827295, by rfl⟩ : syracuseStep 2206121 = 1654591) B1654591
theorem B604319 : Blo 603293 604319 := bstep (se 1 (by rfl) ⟨453239, by rfl⟩ : syracuseStep 604319 = 906479) B906479
theorem B1358063 : Blo 603293 1358063 := bstep (se 1 (by rfl) ⟨1018547, by rfl⟩ : syracuseStep 1358063 = 2037095) B2037095
theorem B1358567 : Blo 603293 1358567 := bstep (se 1 (by rfl) ⟨1018925, by rfl⟩ : syracuseStep 1358567 = 2037851) B2037851
theorem B2046761 : Blo 603293 2046761 := bstep (se 2 (by rfl) ⟨767535, by rfl⟩ : syracuseStep 2046761 = 1535071) B1535071
theorem B606719 : Blo 603293 606719 := bstep (se 1 (by rfl) ⟨455039, by rfl⟩ : syracuseStep 606719 = 910079) B910079
theorem B1363391 : Blo 603293 1363391 := bstep (se 1 (by rfl) ⟨1022543, by rfl⟩ : syracuseStep 1363391 = 2045087) B2045087
theorem B2582711 : Blo 603293 2582711 := bstep (se 1 (by rfl) ⟨1937033, by rfl⟩ : syracuseStep 2582711 = 3874067) B3874067
theorem B9432895 : Blo 603293 9432895 := bstep (se 1 (by rfl) ⟨7074671, by rfl⟩ : syracuseStep 9432895 = 14149343) B14149343
theorem B13990481 : Blo 603293 13990481 := bstep (se 2 (by rfl) ⟨5246430, by rfl⟩ : syracuseStep 13990481 = 10492861) B10492861
theorem B1968505 : Blo 603293 1968505 := bstep (se 2 (by rfl) ⟨738189, by rfl⟩ : syracuseStep 1968505 = 1476379) B1476379
theorem B48543209 : Blo 603293 48543209 := bstep (se 2 (by rfl) ⟨18203703, by rfl⟩ : syracuseStep 48543209 = 36407407) B36407407
theorem B5882989 : Blo 603293 5882989 := bstep (se 3 (by rfl) ⟨1103060, by rfl⟩ : syracuseStep 5882989 = 2206121) B2206121
theorem B1721807 : Blo 603293 1721807 := bstep (se 1 (by rfl) ⟨1291355, by rfl⟩ : syracuseStep 1721807 = 2582711) B2582711
theorem B905375 : Blo 603293 905375 := bstep (se 1 (by rfl) ⟨679031, by rfl⟩ : syracuseStep 905375 = 1358063) B1358063
theorem B9326987 : Blo 603293 9326987 := bstep (se 1 (by rfl) ⟨6995240, by rfl⟩ : syracuseStep 9326987 = 13990481) B13990481
theorem B905711 : Blo 603293 905711 := bstep (se 1 (by rfl) ⟨679283, by rfl⟩ : syracuseStep 905711 = 1358567) B1358567
theorem B1364507 : Blo 603293 1364507 := bstep (se 1 (by rfl) ⟨1023380, by rfl⟩ : syracuseStep 1364507 = 2046761) B2046761
theorem B1530535 : Blo 603293 1530535 := bstep (se 1 (by rfl) ⟨1147901, by rfl⟩ : syracuseStep 1530535 = 2295803) B2295803
theorem B908927 : Blo 603293 908927 := bstep (se 1 (by rfl) ⟨681695, by rfl⟩ : syracuseStep 908927 = 1363391) B1363391
theorem B2910163 : Blo 603293 2910163 := bstep (se 1 (by rfl) ⟨2182622, by rfl⟩ : syracuseStep 2910163 = 4365245) B4365245
theorem B74737991 : Blo 603293 74737991 := bstep (se 1 (by rfl) ⟨56053493, by rfl⟩ : syracuseStep 74737991 = 112106987) B112106987
theorem B12577193 : Blo 603293 12577193 := bstep (se 2 (by rfl) ⟨4716447, by rfl⟩ : syracuseStep 12577193 = 9432895) B9432895
theorem B1147871 : Blo 603293 1147871 := bstep (se 1 (by rfl) ⟨860903, by rfl⟩ : syracuseStep 1147871 = 1721807) B1721807
theorem B2040713 : Blo 603293 2040713 := bstep (se 2 (by rfl) ⟨765267, by rfl⟩ : syracuseStep 2040713 = 1530535) B1530535
theorem B7843985 : Blo 603293 7843985 := bstep (se 2 (by rfl) ⟨2941494, by rfl⟩ : syracuseStep 7843985 = 5882989) B5882989
theorem B10498693 : Blo 603293 10498693 := bstep (se 4 (by rfl) ⟨984252, by rfl⟩ : syracuseStep 10498693 = 1968505) B1968505
theorem B3880217 : Blo 603293 3880217 := bstep (se 2 (by rfl) ⟨1455081, by rfl⟩ : syracuseStep 3880217 = 2910163) B2910163
theorem B603583 : Blo 603293 603583 := bstep (se 1 (by rfl) ⟨452687, by rfl⟩ : syracuseStep 603583 = 905375) B905375
theorem B603807 : Blo 603293 603807 := bstep (se 1 (by rfl) ⟨452855, by rfl⟩ : syracuseStep 603807 = 905711) B905711
theorem B605951 : Blo 603293 605951 := bstep (se 1 (by rfl) ⟨454463, by rfl⟩ : syracuseStep 605951 = 908927) B908927
theorem B49825327 : Blo 603293 49825327 := bstep (se 1 (by rfl) ⟨37368995, by rfl⟩ : syracuseStep 49825327 = 74737991) B74737991
theorem B32362139 : Blo 603293 32362139 := bstep (se 1 (by rfl) ⟨24271604, by rfl⟩ : syracuseStep 32362139 = 48543209) B48543209
theorem B6217991 : Blo 603293 6217991 := bstep (se 1 (by rfl) ⟨4663493, by rfl⟩ : syracuseStep 6217991 = 9326987) B9326987
theorem B909671 : Blo 603293 909671 := bstep (se 1 (by rfl) ⟨682253, by rfl⟩ : syracuseStep 909671 = 1364507) B1364507
theorem B8384795 : Blo 603293 8384795 := bstep (se 1 (by rfl) ⟨6288596, by rfl⟩ : syracuseStep 8384795 = 12577193) B12577193
theorem B13998257 : Blo 603293 13998257 := bstep (se 2 (by rfl) ⟨5249346, by rfl⟩ : syracuseStep 13998257 = 10498693) B10498693
theorem B66433769 : Blo 603293 66433769 := bstep (se 2 (by rfl) ⟨24912663, by rfl⟩ : syracuseStep 66433769 = 49825327) B49825327
theorem B21574759 : Blo 603293 21574759 := bstep (se 1 (by rfl) ⟨16181069, by rfl⟩ : syracuseStep 21574759 = 32362139) B32362139
theorem B3060989 : Blo 603293 3060989 := bstep (se 3 (by rfl) ⟨573935, by rfl⟩ : syracuseStep 3060989 = 1147871) B1147871
theorem B4145327 : Blo 603293 4145327 := bstep (se 1 (by rfl) ⟨3108995, by rfl⟩ : syracuseStep 4145327 = 6217991) B6217991
theorem B606447 : Blo 603293 606447 := bstep (se 1 (by rfl) ⟨454835, by rfl⟩ : syracuseStep 606447 = 909671) B909671
theorem B1360475 : Blo 603293 1360475 := bstep (se 1 (by rfl) ⟨1020356, by rfl⟩ : syracuseStep 1360475 = 2040713) B2040713
theorem B5229323 : Blo 603293 5229323 := bstep (se 1 (by rfl) ⟨3921992, by rfl⟩ : syracuseStep 5229323 = 7843985) B7843985
theorem B5589863 : Blo 603293 5589863 := bstep (se 1 (by rfl) ⟨4192397, by rfl⟩ : syracuseStep 5589863 = 8384795) B8384795
theorem B2586811 : Blo 603293 2586811 := bstep (se 1 (by rfl) ⟨1940108, by rfl⟩ : syracuseStep 2586811 = 3880217) B3880217
theorem B3449081 : Blo 603293 3449081 := bstep (se 2 (by rfl) ⟨1293405, by rfl⟩ : syracuseStep 3449081 = 2586811) B2586811
theorem B2040659 : Blo 603293 2040659 := bstep (se 1 (by rfl) ⟨1530494, by rfl⟩ : syracuseStep 2040659 = 3060989) B3060989
theorem B2763551 : Blo 603293 2763551 := bstep (se 1 (by rfl) ⟨2072663, by rfl⟩ : syracuseStep 2763551 = 4145327) B4145327
theorem B3486215 : Blo 603293 3486215 := bstep (se 1 (by rfl) ⟨2614661, by rfl⟩ : syracuseStep 3486215 = 5229323) B5229323
theorem B44289179 : Blo 603293 44289179 := bstep (se 1 (by rfl) ⟨33216884, by rfl⟩ : syracuseStep 44289179 = 66433769) B66433769
theorem B906983 : Blo 603293 906983 := bstep (se 1 (by rfl) ⟨680237, by rfl⟩ : syracuseStep 906983 = 1360475) B1360475
theorem B3726575 : Blo 603293 3726575 := bstep (se 1 (by rfl) ⟨2794931, by rfl⟩ : syracuseStep 3726575 = 5589863) B5589863
theorem B9332171 : Blo 603293 9332171 := bstep (se 1 (by rfl) ⟨6999128, by rfl⟩ : syracuseStep 9332171 = 13998257) B13998257
theorem B28766345 : Blo 603293 28766345 := bstep (se 2 (by rfl) ⟨10787379, by rfl⟩ : syracuseStep 28766345 = 21574759) B21574759
theorem B76710253 : Blo 603293 76710253 := bstep (se 3 (by rfl) ⟨14383172, by rfl⟩ : syracuseStep 76710253 = 28766345) B28766345
theorem B29526119 : Blo 603293 29526119 := bstep (se 1 (by rfl) ⟨22144589, by rfl⟩ : syracuseStep 29526119 = 44289179) B44289179
theorem B2299387 : Blo 603293 2299387 := bstep (se 1 (by rfl) ⟨1724540, by rfl⟩ : syracuseStep 2299387 = 3449081) B3449081
theorem B1842367 : Blo 603293 1842367 := bstep (se 1 (by rfl) ⟨1381775, by rfl⟩ : syracuseStep 1842367 = 2763551) B2763551
theorem B604655 : Blo 603293 604655 := bstep (se 1 (by rfl) ⟨453491, by rfl⟩ : syracuseStep 604655 = 906983) B906983
theorem B1360439 : Blo 603293 1360439 := bstep (se 1 (by rfl) ⟨1020329, by rfl⟩ : syracuseStep 1360439 = 2040659) B2040659
theorem B2484383 : Blo 603293 2484383 := bstep (se 1 (by rfl) ⟨1863287, by rfl⟩ : syracuseStep 2484383 = 3726575) B3726575
theorem B6221447 : Blo 603293 6221447 := bstep (se 1 (by rfl) ⟨4666085, by rfl⟩ : syracuseStep 6221447 = 9332171) B9332171
theorem B2324143 : Blo 603293 2324143 := bstep (se 1 (by rfl) ⟨1743107, by rfl⟩ : syracuseStep 2324143 = 3486215) B3486215
theorem B6625021 : Blo 603293 6625021 := bstep (se 3 (by rfl) ⟨1242191, by rfl⟩ : syracuseStep 6625021 = 2484383) B2484383
theorem B102280337 : Blo 603293 102280337 := bstep (se 2 (by rfl) ⟨38355126, by rfl⟩ : syracuseStep 102280337 = 76710253) B76710253
theorem B3065849 : Blo 603293 3065849 := bstep (se 2 (by rfl) ⟨1149693, by rfl⟩ : syracuseStep 3065849 = 2299387) B2299387
theorem B3098857 : Blo 603293 3098857 := bstep (se 2 (by rfl) ⟨1162071, by rfl⟩ : syracuseStep 3098857 = 2324143) B2324143
theorem B4147631 : Blo 603293 4147631 := bstep (se 1 (by rfl) ⟨3110723, by rfl⟩ : syracuseStep 4147631 = 6221447) B6221447
theorem B906959 : Blo 603293 906959 := bstep (se 1 (by rfl) ⟨680219, by rfl⟩ : syracuseStep 906959 = 1360439) B1360439
theorem B19684079 : Blo 603293 19684079 := bstep (se 1 (by rfl) ⟨14763059, by rfl⟩ : syracuseStep 19684079 = 29526119) B29526119
theorem B2456489 : Blo 603293 2456489 := bstep (se 2 (by rfl) ⟨921183, by rfl⟩ : syracuseStep 2456489 = 1842367) B1842367
theorem B4131809 : Blo 603293 4131809 := bstep (se 2 (by rfl) ⟨1549428, by rfl⟩ : syracuseStep 4131809 = 3098857) B3098857
theorem B141333781 : Blo 603293 141333781 := bstep (se 6 (by rfl) ⟨3312510, by rfl⟩ : syracuseStep 141333781 = 6625021) B6625021
theorem B2043899 : Blo 603293 2043899 := bstep (se 1 (by rfl) ⟨1532924, by rfl⟩ : syracuseStep 2043899 = 3065849) B3065849
theorem B2765087 : Blo 603293 2765087 := bstep (se 1 (by rfl) ⟨2073815, by rfl⟩ : syracuseStep 2765087 = 4147631) B4147631
theorem B604639 : Blo 603293 604639 := bstep (se 1 (by rfl) ⟨453479, by rfl⟩ : syracuseStep 604639 = 906959) B906959
theorem B13122719 : Blo 603293 13122719 := bstep (se 1 (by rfl) ⟨9842039, by rfl⟩ : syracuseStep 13122719 = 19684079) B19684079
theorem B68186891 : Blo 603293 68186891 := bstep (se 1 (by rfl) ⟨51140168, by rfl⟩ : syracuseStep 68186891 = 102280337) B102280337
theorem B1637659 : Blo 603293 1637659 := bstep (se 1 (by rfl) ⟨1228244, by rfl⟩ : syracuseStep 1637659 = 2456489) B2456489
theorem B2754539 : Blo 603293 2754539 := bstep (se 1 (by rfl) ⟨2065904, by rfl⟩ : syracuseStep 2754539 = 4131809) B4131809
theorem B181831709 : Blo 603293 181831709 := bstep (se 3 (by rfl) ⟨34093445, by rfl⟩ : syracuseStep 181831709 = 68186891) B68186891
theorem B1843391 : Blo 603293 1843391 := bstep (se 1 (by rfl) ⟨1382543, by rfl⟩ : syracuseStep 1843391 = 2765087) B2765087
theorem B1362599 : Blo 603293 1362599 := bstep (se 1 (by rfl) ⟨1021949, by rfl⟩ : syracuseStep 1362599 = 2043899) B2043899
theorem B2183545 : Blo 603293 2183545 := bstep (se 2 (by rfl) ⟨818829, by rfl⟩ : syracuseStep 2183545 = 1637659) B1637659
theorem B188445041 : Blo 603293 188445041 := bstep (se 2 (by rfl) ⟨70666890, by rfl⟩ : syracuseStep 188445041 = 141333781) B141333781
theorem B8748479 : Blo 603293 8748479 := bstep (se 1 (by rfl) ⟨6561359, by rfl⟩ : syracuseStep 8748479 = 13122719) B13122719
theorem B1836359 : Blo 603293 1836359 := bstep (se 1 (by rfl) ⟨1377269, by rfl⟩ : syracuseStep 1836359 = 2754539) B2754539
theorem B121221139 : Blo 603293 121221139 := bstep (se 1 (by rfl) ⟨90915854, by rfl⟩ : syracuseStep 121221139 = 181831709) B181831709
theorem B1228927 : Blo 603293 1228927 := bstep (se 1 (by rfl) ⟨921695, by rfl⟩ : syracuseStep 1228927 = 1843391) B1843391
theorem B908399 : Blo 603293 908399 := bstep (se 1 (by rfl) ⟨681299, by rfl⟩ : syracuseStep 908399 = 1362599) B1362599
theorem B2911393 : Blo 603293 2911393 := bstep (se 2 (by rfl) ⟨1091772, by rfl⟩ : syracuseStep 2911393 = 2183545) B2183545
theorem B125630027 : Blo 603293 125630027 := bstep (se 1 (by rfl) ⟨94222520, by rfl⟩ : syracuseStep 125630027 = 188445041) B188445041
theorem B5832319 : Blo 603293 5832319 := bstep (se 1 (by rfl) ⟨4374239, by rfl⟩ : syracuseStep 5832319 = 8748479) B8748479
theorem B1638569 : Blo 603293 1638569 := bstep (se 2 (by rfl) ⟨614463, by rfl⟩ : syracuseStep 1638569 = 1228927) B1228927
theorem B7776425 : Blo 603293 7776425 := bstep (se 2 (by rfl) ⟨2916159, by rfl⟩ : syracuseStep 7776425 = 5832319) B5832319
theorem B1224239 : Blo 603293 1224239 := bstep (se 1 (by rfl) ⟨918179, by rfl⟩ : syracuseStep 1224239 = 1836359) B1836359
theorem B3881857 : Blo 603293 3881857 := bstep (se 2 (by rfl) ⟨1455696, by rfl⟩ : syracuseStep 3881857 = 2911393) B2911393
theorem B605599 : Blo 603293 605599 := bstep (se 1 (by rfl) ⟨454199, by rfl⟩ : syracuseStep 605599 = 908399) B908399
theorem B161628185 : Blo 603293 161628185 := bstep (se 2 (by rfl) ⟨60610569, by rfl⟩ : syracuseStep 161628185 = 121221139) B121221139
theorem B83753351 : Blo 603293 83753351 := bstep (se 1 (by rfl) ⟨62815013, by rfl⟩ : syracuseStep 83753351 = 125630027) B125630027
theorem B5184283 : Blo 603293 5184283 := bstep (se 1 (by rfl) ⟨3888212, by rfl⟩ : syracuseStep 5184283 = 7776425) B7776425
theorem B107752123 : Blo 603293 107752123 := bstep (se 1 (by rfl) ⟨80814092, by rfl⟩ : syracuseStep 107752123 = 161628185) B161628185
theorem B1092379 : Blo 603293 1092379 := bstep (se 1 (by rfl) ⟨819284, by rfl⟩ : syracuseStep 1092379 = 1638569) B1638569
theorem B3264637 : Blo 603293 3264637 := bstep (se 3 (by rfl) ⟨612119, by rfl⟩ : syracuseStep 3264637 = 1224239) B1224239
theorem B5175809 : Blo 603293 5175809 := bstep (se 2 (by rfl) ⟨1940928, by rfl⟩ : syracuseStep 5175809 = 3881857) B3881857
theorem B55835567 : Blo 603293 55835567 := bstep (se 1 (by rfl) ⟨41876675, by rfl⟩ : syracuseStep 55835567 = 83753351) B83753351
theorem B3450539 : Blo 603293 3450539 := bstep (se 1 (by rfl) ⟨2587904, by rfl⟩ : syracuseStep 3450539 = 5175809) B5175809
theorem B143669497 : Blo 603293 143669497 := bstep (se 2 (by rfl) ⟨53876061, by rfl⟩ : syracuseStep 143669497 = 107752123) B107752123
theorem B1456505 : Blo 603293 1456505 := bstep (se 2 (by rfl) ⟨546189, by rfl⟩ : syracuseStep 1456505 = 1092379) B1092379
theorem B4352849 : Blo 603293 4352849 := bstep (se 2 (by rfl) ⟨1632318, by rfl⟩ : syracuseStep 4352849 = 3264637) B3264637
theorem B6912377 : Blo 603293 6912377 := bstep (se 2 (by rfl) ⟨2592141, by rfl⟩ : syracuseStep 6912377 = 5184283) B5184283
theorem B37223711 : Blo 603293 37223711 := bstep (se 1 (by rfl) ⟨27917783, by rfl⟩ : syracuseStep 37223711 = 55835567) B55835567
theorem B2300359 : Blo 603293 2300359 := bstep (se 1 (by rfl) ⟨1725269, by rfl⟩ : syracuseStep 2300359 = 3450539) B3450539
theorem B24815807 : Blo 603293 24815807 := bstep (se 1 (by rfl) ⟨18611855, by rfl⟩ : syracuseStep 24815807 = 37223711) B37223711
theorem B2901899 : Blo 603293 2901899 := bstep (se 1 (by rfl) ⟨2176424, by rfl⟩ : syracuseStep 2901899 = 4352849) B4352849
theorem B971003 : Blo 603293 971003 := bstep (se 1 (by rfl) ⟨728252, by rfl⟩ : syracuseStep 971003 = 1456505) B1456505
theorem B4608251 : Blo 603293 4608251 := bstep (se 1 (by rfl) ⟨3456188, by rfl⟩ : syracuseStep 4608251 = 6912377) B6912377
theorem B191559329 : Blo 603293 191559329 := bstep (se 2 (by rfl) ⟨71834748, by rfl⟩ : syracuseStep 191559329 = 143669497) B143669497
theorem B1934599 : Blo 603293 1934599 := bstep (se 1 (by rfl) ⟨1450949, by rfl⟩ : syracuseStep 1934599 = 2901899) B2901899
theorem B127706219 : Blo 603293 127706219 := bstep (se 1 (by rfl) ⟨95779664, by rfl⟩ : syracuseStep 127706219 = 191559329) B191559329
theorem B3067145 : Blo 603293 3067145 := bstep (se 2 (by rfl) ⟨1150179, by rfl⟩ : syracuseStep 3067145 = 2300359) B2300359
theorem B647335 : Blo 603293 647335 := bstep (se 1 (by rfl) ⟨485501, by rfl⟩ : syracuseStep 647335 = 971003) B971003
theorem B3072167 : Blo 603293 3072167 := bstep (se 1 (by rfl) ⟨2304125, by rfl⟩ : syracuseStep 3072167 = 4608251) B4608251
theorem B16543871 : Blo 603293 16543871 := bstep (se 1 (by rfl) ⟨12407903, by rfl⟩ : syracuseStep 16543871 = 24815807) B24815807
theorem B85137479 : Blo 603293 85137479 := bstep (se 1 (by rfl) ⟨63853109, by rfl⟩ : syracuseStep 85137479 = 127706219) B127706219
theorem B3452453 : Blo 603293 3452453 := bstep (se 4 (by rfl) ⟨323667, by rfl⟩ : syracuseStep 3452453 = 647335) B647335
theorem B2044763 : Blo 603293 2044763 := bstep (se 1 (by rfl) ⟨1533572, by rfl⟩ : syracuseStep 2044763 = 3067145) B3067145
theorem B2048111 : Blo 603293 2048111 := bstep (se 1 (by rfl) ⟨1536083, by rfl⟩ : syracuseStep 2048111 = 3072167) B3072167
theorem B11029247 : Blo 603293 11029247 := bstep (se 1 (by rfl) ⟨8271935, by rfl⟩ : syracuseStep 11029247 = 16543871) B16543871
theorem B2579465 : Blo 603293 2579465 := bstep (se 2 (by rfl) ⟨967299, by rfl⟩ : syracuseStep 2579465 = 1934599) B1934599
theorem B56758319 : Blo 603293 56758319 := bstep (se 1 (by rfl) ⟨42568739, by rfl⟩ : syracuseStep 56758319 = 85137479) B85137479
theorem B2301635 : Blo 603293 2301635 := bstep (se 1 (by rfl) ⟨1726226, by rfl⟩ : syracuseStep 2301635 = 3452453) B3452453
theorem B7352831 : Blo 603293 7352831 := bstep (se 1 (by rfl) ⟨5514623, by rfl⟩ : syracuseStep 7352831 = 11029247) B11029247
theorem B1719643 : Blo 603293 1719643 := bstep (se 1 (by rfl) ⟨1289732, by rfl⟩ : syracuseStep 1719643 = 2579465) B2579465
theorem B1363175 : Blo 603293 1363175 := bstep (se 1 (by rfl) ⟨1022381, by rfl⟩ : syracuseStep 1363175 = 2044763) B2044763
theorem B1365407 : Blo 603293 1365407 := bstep (se 1 (by rfl) ⟨1024055, by rfl⟩ : syracuseStep 1365407 = 2048111) B2048111
theorem B4901887 : Blo 603293 4901887 := bstep (se 1 (by rfl) ⟨3676415, by rfl⟩ : syracuseStep 4901887 = 7352831) B7352831
theorem B908783 : Blo 603293 908783 := bstep (se 1 (by rfl) ⟨681587, by rfl⟩ : syracuseStep 908783 = 1363175) B1363175
theorem B37838879 : Blo 603293 37838879 := bstep (se 1 (by rfl) ⟨28379159, by rfl⟩ : syracuseStep 37838879 = 56758319) B56758319
theorem B910271 : Blo 603293 910271 := bstep (se 1 (by rfl) ⟨682703, by rfl⟩ : syracuseStep 910271 = 1365407) B1365407
theorem B1534423 : Blo 603293 1534423 := bstep (se 1 (by rfl) ⟨1150817, by rfl⟩ : syracuseStep 1534423 = 2301635) B2301635
theorem B2292857 : Blo 603293 2292857 := bstep (se 2 (by rfl) ⟨859821, by rfl⟩ : syracuseStep 2292857 = 1719643) B1719643
theorem B2045897 : Blo 603293 2045897 := bstep (se 2 (by rfl) ⟨767211, by rfl⟩ : syracuseStep 2045897 = 1534423) B1534423
theorem B6535849 : Blo 603293 6535849 := bstep (se 2 (by rfl) ⟨2450943, by rfl⟩ : syracuseStep 6535849 = 4901887) B4901887
theorem B605855 : Blo 603293 605855 := bstep (se 1 (by rfl) ⟨454391, by rfl⟩ : syracuseStep 605855 = 908783) B908783
theorem B606847 : Blo 603293 606847 := bstep (se 1 (by rfl) ⟨455135, by rfl⟩ : syracuseStep 606847 = 910271) B910271
theorem B1528571 : Blo 603293 1528571 := bstep (se 1 (by rfl) ⟨1146428, by rfl⟩ : syracuseStep 1528571 = 2292857) B2292857
theorem B25225919 : Blo 603293 25225919 := bstep (se 1 (by rfl) ⟨18919439, by rfl⟩ : syracuseStep 25225919 = 37838879) B37838879
theorem B1019047 : Blo 603293 1019047 := bstep (se 1 (by rfl) ⟨764285, by rfl⟩ : syracuseStep 1019047 = 1528571) B1528571
theorem B16817279 : Blo 603293 16817279 := bstep (se 1 (by rfl) ⟨12612959, by rfl⟩ : syracuseStep 16817279 = 25225919) B25225919
theorem B1363931 : Blo 603293 1363931 := bstep (se 1 (by rfl) ⟨1022948, by rfl⟩ : syracuseStep 1363931 = 2045897) B2045897
theorem B8714465 : Blo 603293 8714465 := bstep (se 2 (by rfl) ⟨3267924, by rfl⟩ : syracuseStep 8714465 = 6535849) B6535849
theorem B5809643 : Blo 603293 5809643 := bstep (se 1 (by rfl) ⟨4357232, by rfl⟩ : syracuseStep 5809643 = 8714465) B8714465
theorem B1358729 : Blo 603293 1358729 := bstep (se 2 (by rfl) ⟨509523, by rfl⟩ : syracuseStep 1358729 = 1019047) B1019047
theorem B44846077 : Blo 603293 44846077 := bstep (se 3 (by rfl) ⟨8408639, by rfl⟩ : syracuseStep 44846077 = 16817279) B16817279
theorem B909287 : Blo 603293 909287 := bstep (se 1 (by rfl) ⟨681965, by rfl⟩ : syracuseStep 909287 = 1363931) B1363931
theorem B3873095 : Blo 603293 3873095 := bstep (se 1 (by rfl) ⟨2904821, by rfl⟩ : syracuseStep 3873095 = 5809643) B5809643
theorem B606191 : Blo 603293 606191 := bstep (se 1 (by rfl) ⟨454643, by rfl⟩ : syracuseStep 606191 = 909287) B909287
theorem B905819 : Blo 603293 905819 := bstep (se 1 (by rfl) ⟨679364, by rfl⟩ : syracuseStep 905819 = 1358729) B1358729
theorem B59794769 : Blo 603293 59794769 := bstep (se 2 (by rfl) ⟨22423038, by rfl⟩ : syracuseStep 59794769 = 44846077) B44846077
theorem B603879 : Blo 603293 603879 := bstep (se 1 (by rfl) ⟨452909, by rfl⟩ : syracuseStep 603879 = 905819) B905819
theorem B39863179 : Blo 603293 39863179 := bstep (se 1 (by rfl) ⟨29897384, by rfl⟩ : syracuseStep 39863179 = 59794769) B59794769
theorem B2582063 : Blo 603293 2582063 := bstep (se 1 (by rfl) ⟨1936547, by rfl⟩ : syracuseStep 2582063 = 3873095) B3873095
theorem B53150905 : Blo 603293 53150905 := bstep (se 2 (by rfl) ⟨19931589, by rfl⟩ : syracuseStep 53150905 = 39863179) B39863179
theorem B1721375 : Blo 603293 1721375 := bstep (se 1 (by rfl) ⟨1291031, by rfl⟩ : syracuseStep 1721375 = 2582063) B2582063
theorem B1147583 : Blo 603293 1147583 := bstep (se 1 (by rfl) ⟨860687, by rfl⟩ : syracuseStep 1147583 = 1721375) B1721375
theorem B70867873 : Blo 603293 70867873 := bstep (se 2 (by rfl) ⟨26575452, by rfl⟩ : syracuseStep 70867873 = 53150905) B53150905
theorem B765055 : Blo 603293 765055 := bstep (se 1 (by rfl) ⟨573791, by rfl⟩ : syracuseStep 765055 = 1147583) B1147583
theorem B94490497 : Blo 603293 94490497 := bstep (se 2 (by rfl) ⟨35433936, by rfl⟩ : syracuseStep 94490497 = 70867873) B70867873
theorem B1020073 : Blo 603293 1020073 := bstep (se 2 (by rfl) ⟨382527, by rfl⟩ : syracuseStep 1020073 = 765055) B765055
theorem B125987329 : Blo 603293 125987329 := bstep (se 2 (by rfl) ⟨47245248, by rfl⟩ : syracuseStep 125987329 = 94490497) B94490497
theorem B167983105 : Blo 603293 167983105 := bstep (se 2 (by rfl) ⟨62993664, by rfl⟩ : syracuseStep 167983105 = 125987329) B125987329
theorem B1360097 : Blo 603293 1360097 := bstep (se 2 (by rfl) ⟨510036, by rfl⟩ : syracuseStep 1360097 = 1020073) B1020073
theorem B223977473 : Blo 603293 223977473 := bstep (se 2 (by rfl) ⟨83991552, by rfl⟩ : syracuseStep 223977473 = 167983105) B167983105
theorem B906731 : Blo 603293 906731 := bstep (se 1 (by rfl) ⟨680048, by rfl⟩ : syracuseStep 906731 = 1360097) B1360097
theorem B604487 : Blo 603293 604487 := bstep (se 1 (by rfl) ⟨453365, by rfl⟩ : syracuseStep 604487 = 906731) B906731
theorem B149318315 : Blo 603293 149318315 := bstep (se 1 (by rfl) ⟨111988736, by rfl⟩ : syracuseStep 149318315 = 223977473) B223977473
theorem B99545543 : Blo 603293 99545543 := bstep (se 1 (by rfl) ⟨74659157, by rfl⟩ : syracuseStep 99545543 = 149318315) B149318315
theorem B66363695 : Blo 603293 66363695 := bstep (se 1 (by rfl) ⟨49772771, by rfl⟩ : syracuseStep 66363695 = 99545543) B99545543
theorem B44242463 : Blo 603293 44242463 := bstep (se 1 (by rfl) ⟨33181847, by rfl⟩ : syracuseStep 44242463 = 66363695) B66363695
theorem B117979901 : Blo 603293 117979901 := bstep (se 3 (by rfl) ⟨22121231, by rfl⟩ : syracuseStep 117979901 = 44242463) B44242463
theorem B78653267 : Blo 603293 78653267 := bstep (se 1 (by rfl) ⟨58989950, by rfl⟩ : syracuseStep 78653267 = 117979901) B117979901
theorem B52435511 : Blo 603293 52435511 := bstep (se 1 (by rfl) ⟨39326633, by rfl⟩ : syracuseStep 52435511 = 78653267) B78653267
theorem B34957007 : Blo 603293 34957007 := bstep (se 1 (by rfl) ⟨26217755, by rfl⟩ : syracuseStep 34957007 = 52435511) B52435511
theorem B23304671 : Blo 603293 23304671 := bstep (se 1 (by rfl) ⟨17478503, by rfl⟩ : syracuseStep 23304671 = 34957007) B34957007
theorem B15536447 : Blo 603293 15536447 := bstep (se 1 (by rfl) ⟨11652335, by rfl⟩ : syracuseStep 15536447 = 23304671) B23304671
theorem B10357631 : Blo 603293 10357631 := bstep (se 1 (by rfl) ⟨7768223, by rfl⟩ : syracuseStep 10357631 = 15536447) B15536447
theorem B6905087 : Blo 603293 6905087 := bstep (se 1 (by rfl) ⟨5178815, by rfl⟩ : syracuseStep 6905087 = 10357631) B10357631
theorem B4603391 : Blo 603293 4603391 := bstep (se 1 (by rfl) ⟨3452543, by rfl⟩ : syracuseStep 4603391 = 6905087) B6905087
theorem B3068927 : Blo 603293 3068927 := bstep (se 1 (by rfl) ⟨2301695, by rfl⟩ : syracuseStep 3068927 = 4603391) B4603391
theorem B2045951 : Blo 603293 2045951 := bstep (se 1 (by rfl) ⟨1534463, by rfl⟩ : syracuseStep 2045951 = 3068927) B3068927
theorem B1363967 : Blo 603293 1363967 := bstep (se 1 (by rfl) ⟨1022975, by rfl⟩ : syracuseStep 1363967 = 2045951) B2045951
theorem B909311 : Blo 603293 909311 := bstep (se 1 (by rfl) ⟨681983, by rfl⟩ : syracuseStep 909311 = 1363967) B1363967
theorem B606207 : Blo 603293 606207 := bstep (se 1 (by rfl) ⟨454655, by rfl⟩ : syracuseStep 606207 = 909311) B909311

theorem C0 (j : ℕ) (h1 : 150823 ≤ j) (h2 : j ≤ 151522) : Blo 603293 (4 * j + 3) := by
  interval_cases j
  · exact B603295
  · exact B603299
  · exact B603303
  · exact B603307
  · exact B603311
  · exact B603315
  · exact B603319
  · exact B603323
  · exact B603327
  · exact B603331
  · exact B603335
  · exact B603339
  · exact B603343
  · exact B603347
  · exact B603351
  · exact B603355
  · exact B603359
  · exact B603363
  · exact B603367
  · exact B603371
  · exact B603375
  · exact B603379
  · exact B603383
  · exact B603387
  · exact B603391
  · exact B603395
  · exact B603399
  · exact B603403
  · exact B603407
  · exact B603411
  · exact B603415
  · exact B603419
  · exact B603423
  · exact B603427
  · exact B603431
  · exact B603435
  · exact B603439
  · exact B603443
  · exact B603447
  · exact B603451
  · exact B603455
  · exact B603459
  · exact B603463
  · exact B603467
  · exact B603471
  · exact B603475
  · exact B603479
  · exact B603483
  · exact B603487
  · exact B603491
  · exact B603495
  · exact B603499
  · exact B603503
  · exact B603507
  · exact B603511
  · exact B603515
  · exact B603519
  · exact B603523
  · exact B603527
  · exact B603531
  · exact B603535
  · exact B603539
  · exact B603543
  · exact B603547
  · exact B603551
  · exact B603555
  · exact B603559
  · exact B603563
  · exact B603567
  · exact B603571
  · exact B603575
  · exact B603579
  · exact B603583
  · exact B603587
  · exact B603591
  · exact B603595
  · exact B603599
  · exact B603603
  · exact B603607
  · exact B603611
  · exact B603615
  · exact B603619
  · exact B603623
  · exact B603627
  · exact B603631
  · exact B603635
  · exact B603639
  · exact B603643
  · exact B603647
  · exact B603651
  · exact B603655
  · exact B603659
  · exact B603663
  · exact B603667
  · exact B603671
  · exact B603675
  · exact B603679
  · exact B603683
  · exact B603687
  · exact B603691
  · exact B603695
  · exact B603699
  · exact B603703
  · exact B603707
  · exact B603711
  · exact B603715
  · exact B603719
  · exact B603723
  · exact B603727
  · exact B603731
  · exact B603735
  · exact B603739
  · exact B603743
  · exact B603747
  · exact B603751
  · exact B603755
  · exact B603759
  · exact B603763
  · exact B603767
  · exact B603771
  · exact B603775
  · exact B603779
  · exact B603783
  · exact B603787
  · exact B603791
  · exact B603795
  · exact B603799
  · exact B603803
  · exact B603807
  · exact B603811
  · exact B603815
  · exact B603819
  · exact B603823
  · exact B603827
  · exact B603831
  · exact B603835
  · exact B603839
  · exact B603843
  · exact B603847
  · exact B603851
  · exact B603855
  · exact B603859
  · exact B603863
  · exact B603867
  · exact B603871
  · exact B603875
  · exact B603879
  · exact B603883
  · exact B603887
  · exact B603891
  · exact B603895
  · exact B603899
  · exact B603903
  · exact B603907
  · exact B603911
  · exact B603915
  · exact B603919
  · exact B603923
  · exact B603927
  · exact B603931
  · exact B603935
  · exact B603939
  · exact B603943
  · exact B603947
  · exact B603951
  · exact B603955
  · exact B603959
  · exact B603963
  · exact B603967
  · exact B603971
  · exact B603975
  · exact B603979
  · exact B603983
  · exact B603987
  · exact B603991
  · exact B603995
  · exact B603999
  · exact B604003
  · exact B604007
  · exact B604011
  · exact B604015
  · exact B604019
  · exact B604023
  · exact B604027
  · exact B604031
  · exact B604035
  · exact B604039
  · exact B604043
  · exact B604047
  · exact B604051
  · exact B604055
  · exact B604059
  · exact B604063
  · exact B604067
  · exact B604071
  · exact B604075
  · exact B604079
  · exact B604083
  · exact B604087
  · exact B604091
  · exact B604095
  · exact B604099
  · exact B604103
  · exact B604107
  · exact B604111
  · exact B604115
  · exact B604119
  · exact B604123
  · exact B604127
  · exact B604131
  · exact B604135
  · exact B604139
  · exact B604143
  · exact B604147
  · exact B604151
  · exact B604155
  · exact B604159
  · exact B604163
  · exact B604167
  · exact B604171
  · exact B604175
  · exact B604179
  · exact B604183
  · exact B604187
  · exact B604191
  · exact B604195
  · exact B604199
  · exact B604203
  · exact B604207
  · exact B604211
  · exact B604215
  · exact B604219
  · exact B604223
  · exact B604227
  · exact B604231
  · exact B604235
  · exact B604239
  · exact B604243
  · exact B604247
  · exact B604251
  · exact B604255
  · exact B604259
  · exact B604263
  · exact B604267
  · exact B604271
  · exact B604275
  · exact B604279
  · exact B604283
  · exact B604287
  · exact B604291
  · exact B604295
  · exact B604299
  · exact B604303
  · exact B604307
  · exact B604311
  · exact B604315
  · exact B604319
  · exact B604323
  · exact B604327
  · exact B604331
  · exact B604335
  · exact B604339
  · exact B604343
  · exact B604347
  · exact B604351
  · exact B604355
  · exact B604359
  · exact B604363
  · exact B604367
  · exact B604371
  · exact B604375
  · exact B604379
  · exact B604383
  · exact B604387
  · exact B604391
  · exact B604395
  · exact B604399
  · exact B604403
  · exact B604407
  · exact B604411
  · exact B604415
  · exact B604419
  · exact B604423
  · exact B604427
  · exact B604431
  · exact B604435
  · exact B604439
  · exact B604443
  · exact B604447
  · exact B604451
  · exact B604455
  · exact B604459
  · exact B604463
  · exact B604467
  · exact B604471
  · exact B604475
  · exact B604479
  · exact B604483
  · exact B604487
  · exact B604491
  · exact B604495
  · exact B604499
  · exact B604503
  · exact B604507
  · exact B604511
  · exact B604515
  · exact B604519
  · exact B604523
  · exact B604527
  · exact B604531
  · exact B604535
  · exact B604539
  · exact B604543
  · exact B604547
  · exact B604551
  · exact B604555
  · exact B604559
  · exact B604563
  · exact B604567
  · exact B604571
  · exact B604575
  · exact B604579
  · exact B604583
  · exact B604587
  · exact B604591
  · exact B604595
  · exact B604599
  · exact B604603
  · exact B604607
  · exact B604611
  · exact B604615
  · exact B604619
  · exact B604623
  · exact B604627
  · exact B604631
  · exact B604635
  · exact B604639
  · exact B604643
  · exact B604647
  · exact B604651
  · exact B604655
  · exact B604659
  · exact B604663
  · exact B604667
  · exact B604671
  · exact B604675
  · exact B604679
  · exact B604683
  · exact B604687
  · exact B604691
  · exact B604695
  · exact B604699
  · exact B604703
  · exact B604707
  · exact B604711
  · exact B604715
  · exact B604719
  · exact B604723
  · exact B604727
  · exact B604731
  · exact B604735
  · exact B604739
  · exact B604743
  · exact B604747
  · exact B604751
  · exact B604755
  · exact B604759
  · exact B604763
  · exact B604767
  · exact B604771
  · exact B604775
  · exact B604779
  · exact B604783
  · exact B604787
  · exact B604791
  · exact B604795
  · exact B604799
  · exact B604803
  · exact B604807
  · exact B604811
  · exact B604815
  · exact B604819
  · exact B604823
  · exact B604827
  · exact B604831
  · exact B604835
  · exact B604839
  · exact B604843
  · exact B604847
  · exact B604851
  · exact B604855
  · exact B604859
  · exact B604863
  · exact B604867
  · exact B604871
  · exact B604875
  · exact B604879
  · exact B604883
  · exact B604887
  · exact B604891
  · exact B604895
  · exact B604899
  · exact B604903
  · exact B604907
  · exact B604911
  · exact B604915
  · exact B604919
  · exact B604923
  · exact B604927
  · exact B604931
  · exact B604935
  · exact B604939
  · exact B604943
  · exact B604947
  · exact B604951
  · exact B604955
  · exact B604959
  · exact B604963
  · exact B604967
  · exact B604971
  · exact B604975
  · exact B604979
  · exact B604983
  · exact B604987
  · exact B604991
  · exact B604995
  · exact B604999
  · exact B605003
  · exact B605007
  · exact B605011
  · exact B605015
  · exact B605019
  · exact B605023
  · exact B605027
  · exact B605031
  · exact B605035
  · exact B605039
  · exact B605043
  · exact B605047
  · exact B605051
  · exact B605055
  · exact B605059
  · exact B605063
  · exact B605067
  · exact B605071
  · exact B605075
  · exact B605079
  · exact B605083
  · exact B605087
  · exact B605091
  · exact B605095
  · exact B605099
  · exact B605103
  · exact B605107
  · exact B605111
  · exact B605115
  · exact B605119
  · exact B605123
  · exact B605127
  · exact B605131
  · exact B605135
  · exact B605139
  · exact B605143
  · exact B605147
  · exact B605151
  · exact B605155
  · exact B605159
  · exact B605163
  · exact B605167
  · exact B605171
  · exact B605175
  · exact B605179
  · exact B605183
  · exact B605187
  · exact B605191
  · exact B605195
  · exact B605199
  · exact B605203
  · exact B605207
  · exact B605211
  · exact B605215
  · exact B605219
  · exact B605223
  · exact B605227
  · exact B605231
  · exact B605235
  · exact B605239
  · exact B605243
  · exact B605247
  · exact B605251
  · exact B605255
  · exact B605259
  · exact B605263
  · exact B605267
  · exact B605271
  · exact B605275
  · exact B605279
  · exact B605283
  · exact B605287
  · exact B605291
  · exact B605295
  · exact B605299
  · exact B605303
  · exact B605307
  · exact B605311
  · exact B605315
  · exact B605319
  · exact B605323
  · exact B605327
  · exact B605331
  · exact B605335
  · exact B605339
  · exact B605343
  · exact B605347
  · exact B605351
  · exact B605355
  · exact B605359
  · exact B605363
  · exact B605367
  · exact B605371
  · exact B605375
  · exact B605379
  · exact B605383
  · exact B605387
  · exact B605391
  · exact B605395
  · exact B605399
  · exact B605403
  · exact B605407
  · exact B605411
  · exact B605415
  · exact B605419
  · exact B605423
  · exact B605427
  · exact B605431
  · exact B605435
  · exact B605439
  · exact B605443
  · exact B605447
  · exact B605451
  · exact B605455
  · exact B605459
  · exact B605463
  · exact B605467
  · exact B605471
  · exact B605475
  · exact B605479
  · exact B605483
  · exact B605487
  · exact B605491
  · exact B605495
  · exact B605499
  · exact B605503
  · exact B605507
  · exact B605511
  · exact B605515
  · exact B605519
  · exact B605523
  · exact B605527
  · exact B605531
  · exact B605535
  · exact B605539
  · exact B605543
  · exact B605547
  · exact B605551
  · exact B605555
  · exact B605559
  · exact B605563
  · exact B605567
  · exact B605571
  · exact B605575
  · exact B605579
  · exact B605583
  · exact B605587
  · exact B605591
  · exact B605595
  · exact B605599
  · exact B605603
  · exact B605607
  · exact B605611
  · exact B605615
  · exact B605619
  · exact B605623
  · exact B605627
  · exact B605631
  · exact B605635
  · exact B605639
  · exact B605643
  · exact B605647
  · exact B605651
  · exact B605655
  · exact B605659
  · exact B605663
  · exact B605667
  · exact B605671
  · exact B605675
  · exact B605679
  · exact B605683
  · exact B605687
  · exact B605691
  · exact B605695
  · exact B605699
  · exact B605703
  · exact B605707
  · exact B605711
  · exact B605715
  · exact B605719
  · exact B605723
  · exact B605727
  · exact B605731
  · exact B605735
  · exact B605739
  · exact B605743
  · exact B605747
  · exact B605751
  · exact B605755
  · exact B605759
  · exact B605763
  · exact B605767
  · exact B605771
  · exact B605775
  · exact B605779
  · exact B605783
  · exact B605787
  · exact B605791
  · exact B605795
  · exact B605799
  · exact B605803
  · exact B605807
  · exact B605811
  · exact B605815
  · exact B605819
  · exact B605823
  · exact B605827
  · exact B605831
  · exact B605835
  · exact B605839
  · exact B605843
  · exact B605847
  · exact B605851
  · exact B605855
  · exact B605859
  · exact B605863
  · exact B605867
  · exact B605871
  · exact B605875
  · exact B605879
  · exact B605883
  · exact B605887
  · exact B605891
  · exact B605895
  · exact B605899
  · exact B605903
  · exact B605907
  · exact B605911
  · exact B605915
  · exact B605919
  · exact B605923
  · exact B605927
  · exact B605931
  · exact B605935
  · exact B605939
  · exact B605943
  · exact B605947
  · exact B605951
  · exact B605955
  · exact B605959
  · exact B605963
  · exact B605967
  · exact B605971
  · exact B605975
  · exact B605979
  · exact B605983
  · exact B605987
  · exact B605991
  · exact B605995
  · exact B605999
  · exact B606003
  · exact B606007
  · exact B606011
  · exact B606015
  · exact B606019
  · exact B606023
  · exact B606027
  · exact B606031
  · exact B606035
  · exact B606039
  · exact B606043
  · exact B606047
  · exact B606051
  · exact B606055
  · exact B606059
  · exact B606063
  · exact B606067
  · exact B606071
  · exact B606075
  · exact B606079
  · exact B606083
  · exact B606087
  · exact B606091

theorem C1 (j : ℕ) (h1 : 151523 ≤ j) (h2 : j ≤ 151822) : Blo 603293 (4 * j + 3) := by
  interval_cases j
  · exact B606095
  · exact B606099
  · exact B606103
  · exact B606107
  · exact B606111
  · exact B606115
  · exact B606119
  · exact B606123
  · exact B606127
  · exact B606131
  · exact B606135
  · exact B606139
  · exact B606143
  · exact B606147
  · exact B606151
  · exact B606155
  · exact B606159
  · exact B606163
  · exact B606167
  · exact B606171
  · exact B606175
  · exact B606179
  · exact B606183
  · exact B606187
  · exact B606191
  · exact B606195
  · exact B606199
  · exact B606203
  · exact B606207
  · exact B606211
  · exact B606215
  · exact B606219
  · exact B606223
  · exact B606227
  · exact B606231
  · exact B606235
  · exact B606239
  · exact B606243
  · exact B606247
  · exact B606251
  · exact B606255
  · exact B606259
  · exact B606263
  · exact B606267
  · exact B606271
  · exact B606275
  · exact B606279
  · exact B606283
  · exact B606287
  · exact B606291
  · exact B606295
  · exact B606299
  · exact B606303
  · exact B606307
  · exact B606311
  · exact B606315
  · exact B606319
  · exact B606323
  · exact B606327
  · exact B606331
  · exact B606335
  · exact B606339
  · exact B606343
  · exact B606347
  · exact B606351
  · exact B606355
  · exact B606359
  · exact B606363
  · exact B606367
  · exact B606371
  · exact B606375
  · exact B606379
  · exact B606383
  · exact B606387
  · exact B606391
  · exact B606395
  · exact B606399
  · exact B606403
  · exact B606407
  · exact B606411
  · exact B606415
  · exact B606419
  · exact B606423
  · exact B606427
  · exact B606431
  · exact B606435
  · exact B606439
  · exact B606443
  · exact B606447
  · exact B606451
  · exact B606455
  · exact B606459
  · exact B606463
  · exact B606467
  · exact B606471
  · exact B606475
  · exact B606479
  · exact B606483
  · exact B606487
  · exact B606491
  · exact B606495
  · exact B606499
  · exact B606503
  · exact B606507
  · exact B606511
  · exact B606515
  · exact B606519
  · exact B606523
  · exact B606527
  · exact B606531
  · exact B606535
  · exact B606539
  · exact B606543
  · exact B606547
  · exact B606551
  · exact B606555
  · exact B606559
  · exact B606563
  · exact B606567
  · exact B606571
  · exact B606575
  · exact B606579
  · exact B606583
  · exact B606587
  · exact B606591
  · exact B606595
  · exact B606599
  · exact B606603
  · exact B606607
  · exact B606611
  · exact B606615
  · exact B606619
  · exact B606623
  · exact B606627
  · exact B606631
  · exact B606635
  · exact B606639
  · exact B606643
  · exact B606647
  · exact B606651
  · exact B606655
  · exact B606659
  · exact B606663
  · exact B606667
  · exact B606671
  · exact B606675
  · exact B606679
  · exact B606683
  · exact B606687
  · exact B606691
  · exact B606695
  · exact B606699
  · exact B606703
  · exact B606707
  · exact B606711
  · exact B606715
  · exact B606719
  · exact B606723
  · exact B606727
  · exact B606731
  · exact B606735
  · exact B606739
  · exact B606743
  · exact B606747
  · exact B606751
  · exact B606755
  · exact B606759
  · exact B606763
  · exact B606767
  · exact B606771
  · exact B606775
  · exact B606779
  · exact B606783
  · exact B606787
  · exact B606791
  · exact B606795
  · exact B606799
  · exact B606803
  · exact B606807
  · exact B606811
  · exact B606815
  · exact B606819
  · exact B606823
  · exact B606827
  · exact B606831
  · exact B606835
  · exact B606839
  · exact B606843
  · exact B606847
  · exact B606851
  · exact B606855
  · exact B606859
  · exact B606863
  · exact B606867
  · exact B606871
  · exact B606875
  · exact B606879
  · exact B606883
  · exact B606887
  · exact B606891
  · exact B606895
  · exact B606899
  · exact B606903
  · exact B606907
  · exact B606911
  · exact B606915
  · exact B606919
  · exact B606923
  · exact B606927
  · exact B606931
  · exact B606935
  · exact B606939
  · exact B606943
  · exact B606947
  · exact B606951
  · exact B606955
  · exact B606959
  · exact B606963
  · exact B606967
  · exact B606971
  · exact B606975
  · exact B606979
  · exact B606983
  · exact B606987
  · exact B606991
  · exact B606995
  · exact B606999
  · exact B607003
  · exact B607007
  · exact B607011
  · exact B607015
  · exact B607019
  · exact B607023
  · exact B607027
  · exact B607031
  · exact B607035
  · exact B607039
  · exact B607043
  · exact B607047
  · exact B607051
  · exact B607055
  · exact B607059
  · exact B607063
  · exact B607067
  · exact B607071
  · exact B607075
  · exact B607079
  · exact B607083
  · exact B607087
  · exact B607091
  · exact B607095
  · exact B607099
  · exact B607103
  · exact B607107
  · exact B607111
  · exact B607115
  · exact B607119
  · exact B607123
  · exact B607127
  · exact B607131
  · exact B607135
  · exact B607139
  · exact B607143
  · exact B607147
  · exact B607151
  · exact B607155
  · exact B607159
  · exact B607163
  · exact B607167
  · exact B607171
  · exact B607175
  · exact B607179
  · exact B607183
  · exact B607187
  · exact B607191
  · exact B607195
  · exact B607199
  · exact B607203
  · exact B607207
  · exact B607211
  · exact B607215
  · exact B607219
  · exact B607223
  · exact B607227
  · exact B607231
  · exact B607235
  · exact B607239
  · exact B607243
  · exact B607247
  · exact B607251
  · exact B607255
  · exact B607259
  · exact B607263
  · exact B607267
  · exact B607271
  · exact B607275
  · exact B607279
  · exact B607283
  · exact B607287
  · exact B607291

theorem solution (m : ℕ) (hlo : 603293 ≤ m) (hhi : m ≤ 607293) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 150823 ≤ j := by omega
    have hj2 : j ≤ 151822 := by omega
    have hb : Blo 603293 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 151523 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
