-- Prove2me | solution 1 for syracuse_descends_range_1646022_1648022
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:16:59.127444+00:00
-- url     : https://prove2.me/submissions/e00dbf67-e57a-4103-979e-b12f1eb287cb

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


theorem B4169789 : Blo 1646022 4169789 := bbase (se 3 (by rfl) ⟨781835, by rfl⟩ : syracuseStep 4169789 = 1563671) (by norm_num)
theorem B10018997 : Blo 1646022 10018997 := bbase (se 5 (by rfl) ⟨469640, by rfl⟩ : syracuseStep 10018997 = 939281) (by norm_num)
theorem B4169981 : Blo 1646022 4169981 := bbase (se 3 (by rfl) ⟨781871, by rfl⟩ : syracuseStep 4169981 = 1563743) (by norm_num)
theorem B3170573 : Blo 1646022 3170573 := bbase (se 3 (by rfl) ⟨594482, by rfl⟩ : syracuseStep 3170573 = 1188965) (by norm_num)
theorem B4227349 : Blo 1646022 4227349 := bbase (se 6 (by rfl) ⟨99078, by rfl⟩ : syracuseStep 4227349 = 198157) (by norm_num)
theorem B85524821 : Blo 1646022 85524821 := bbase (se 10 (by rfl) ⟨125280, by rfl⟩ : syracuseStep 85524821 = 250561) (by norm_num)
theorem B1851781 : Blo 1646022 1851781 := bbase (se 4 (by rfl) ⟨173604, by rfl⟩ : syracuseStep 1851781 = 347209) (by norm_num)
theorem B18760085 : Blo 1646022 18760085 := bbase (se 6 (by rfl) ⟨439689, by rfl⟩ : syracuseStep 18760085 = 879379) (by norm_num)
theorem B3957149 : Blo 1646022 3957149 := bbase (se 3 (by rfl) ⟨741965, by rfl⟩ : syracuseStep 3957149 = 1483931) (by norm_num)
theorem B1851817 : Blo 1646022 1851817 := bbase (se 2 (by rfl) ⟨694431, by rfl⟩ : syracuseStep 1851817 = 1388863) (by norm_num)
theorem B1851853 : Blo 1646022 1851853 := bbase (se 3 (by rfl) ⟨347222, by rfl⟩ : syracuseStep 1851853 = 694445) (by norm_num)
theorem B1851889 : Blo 1646022 1851889 := bbase (se 2 (by rfl) ⟨694458, by rfl⟩ : syracuseStep 1851889 = 1388917) (by norm_num)
theorem B1851925 : Blo 1646022 1851925 := bbase (se 6 (by rfl) ⟨43404, by rfl⟩ : syracuseStep 1851925 = 86809) (by norm_num)
theorem B1851961 : Blo 1646022 1851961 := bbase (se 2 (by rfl) ⟨694485, by rfl⟩ : syracuseStep 1851961 = 1388971) (by norm_num)
theorem B4170325 : Blo 1646022 4170325 := bbase (se 8 (by rfl) ⟨24435, by rfl⟩ : syracuseStep 4170325 = 48871) (by norm_num)
theorem B1851997 : Blo 1646022 1851997 := bbase (se 3 (by rfl) ⟨347249, by rfl⟩ : syracuseStep 1851997 = 694499) (by norm_num)
theorem B1852033 : Blo 1646022 1852033 := bbase (se 2 (by rfl) ⟨694512, by rfl⟩ : syracuseStep 1852033 = 1389025) (by norm_num)
theorem B21103253 : Blo 1646022 21103253 := bbase (se 6 (by rfl) ⟨494607, by rfl⟩ : syracuseStep 21103253 = 989215) (by norm_num)
theorem B1852069 : Blo 1646022 1852069 := bbase (se 4 (by rfl) ⟨173631, by rfl⟩ : syracuseStep 1852069 = 347263) (by norm_num)
theorem B2777773 : Blo 1646022 2777773 := bbase (se 3 (by rfl) ⟨520832, by rfl⟩ : syracuseStep 2777773 = 1041665) (by norm_num)
theorem B3957437 : Blo 1646022 3957437 := bbase (se 3 (by rfl) ⟨742019, by rfl⟩ : syracuseStep 3957437 = 1484039) (by norm_num)
theorem B4170437 : Blo 1646022 4170437 := bbase (se 4 (by rfl) ⟨390978, by rfl⟩ : syracuseStep 4170437 = 781957) (by norm_num)
theorem B1852105 : Blo 1646022 1852105 := bbase (se 2 (by rfl) ⟨694539, by rfl⟩ : syracuseStep 1852105 = 1389079) (by norm_num)
theorem B1852141 : Blo 1646022 1852141 := bbase (se 3 (by rfl) ⟨347276, by rfl⟩ : syracuseStep 1852141 = 694553) (by norm_num)
theorem B2777861 : Blo 1646022 2777861 := bbase (se 4 (by rfl) ⟨260424, by rfl⟩ : syracuseStep 2777861 = 520849) (by norm_num)
theorem B1852177 : Blo 1646022 1852177 := bbase (se 2 (by rfl) ⟨694566, by rfl⟩ : syracuseStep 1852177 = 1389133) (by norm_num)
theorem B2343701 : Blo 1646022 2343701 := bbase (se 6 (by rfl) ⟨54930, by rfl⟩ : syracuseStep 2343701 = 109861) (by norm_num)
theorem B8340245 : Blo 1646022 8340245 := bbase (se 6 (by rfl) ⟨195474, by rfl⟩ : syracuseStep 8340245 = 390949) (by norm_num)
theorem B3703589 : Blo 1646022 3703589 := bbase (se 4 (by rfl) ⟨347211, by rfl⟩ : syracuseStep 3703589 = 694423) (by norm_num)
theorem B1852213 : Blo 1646022 1852213 := bbase (se 5 (by rfl) ⟨86822, by rfl⟩ : syracuseStep 1852213 = 173645) (by norm_num)
theorem B1852249 : Blo 1646022 1852249 := bbase (se 2 (by rfl) ⟨694593, by rfl⟩ : syracuseStep 1852249 = 1389187) (by norm_num)
theorem B3703661 : Blo 1646022 3703661 := bbase (se 3 (by rfl) ⟨694436, by rfl⟩ : syracuseStep 3703661 = 1388873) (by norm_num)
theorem B4752245 : Blo 1646022 4752245 := bbase (se 5 (by rfl) ⟨222761, by rfl⟩ : syracuseStep 4752245 = 445523) (by norm_num)
theorem B1852285 : Blo 1646022 1852285 := bbase (se 3 (by rfl) ⟨347303, by rfl⟩ : syracuseStep 1852285 = 694607) (by norm_num)
theorem B2777989 : Blo 1646022 2777989 := bbase (se 4 (by rfl) ⟨260436, by rfl⟩ : syracuseStep 2777989 = 520873) (by norm_num)
theorem B4170629 : Blo 1646022 4170629 := bbase (se 4 (by rfl) ⟨390996, by rfl⟩ : syracuseStep 4170629 = 781993) (by norm_num)
theorem B1852321 : Blo 1646022 1852321 := bbase (se 2 (by rfl) ⟨694620, by rfl⟩ : syracuseStep 1852321 = 1389241) (by norm_num)
theorem B3703733 : Blo 1646022 3703733 := bbase (se 5 (by rfl) ⟨173612, by rfl⟩ : syracuseStep 3703733 = 347225) (by norm_num)
theorem B11871157 : Blo 1646022 11871157 := bbase (se 5 (by rfl) ⟨556460, by rfl⟩ : syracuseStep 11871157 = 1112921) (by norm_num)
theorem B1852357 : Blo 1646022 1852357 := bbase (se 4 (by rfl) ⟨173658, by rfl⟩ : syracuseStep 1852357 = 347317) (by norm_num)
theorem B2778077 : Blo 1646022 2778077 := bbase (se 3 (by rfl) ⟨520889, by rfl⟩ : syracuseStep 2778077 = 1041779) (by norm_num)
theorem B1852393 : Blo 1646022 1852393 := bbase (se 2 (by rfl) ⟨694647, by rfl⟩ : syracuseStep 1852393 = 1389295) (by norm_num)
theorem B3703805 : Blo 1646022 3703805 := bbase (se 3 (by rfl) ⟨694463, by rfl⟩ : syracuseStep 3703805 = 1388927) (by norm_num)
theorem B6251525 : Blo 1646022 6251525 := bbase (se 4 (by rfl) ⟨586080, by rfl⟩ : syracuseStep 6251525 = 1172161) (by norm_num)
theorem B1852429 : Blo 1646022 1852429 := bbase (se 3 (by rfl) ⟨347330, by rfl⟩ : syracuseStep 1852429 = 694661) (by norm_num)
theorem B1852465 : Blo 1646022 1852465 := bbase (se 2 (by rfl) ⟨694674, by rfl⟩ : syracuseStep 1852465 = 1389349) (by norm_num)
theorem B2638901 : Blo 1646022 2638901 := bbase (se 5 (by rfl) ⟨123698, by rfl⟩ : syracuseStep 2638901 = 247397) (by norm_num)
theorem B3703877 : Blo 1646022 3703877 := bbase (se 4 (by rfl) ⟨347238, by rfl⟩ : syracuseStep 3703877 = 694477) (by norm_num)
theorem B1852501 : Blo 1646022 1852501 := bbase (se 8 (by rfl) ⟨10854, by rfl⟩ : syracuseStep 1852501 = 21709) (by norm_num)
theorem B2778205 : Blo 1646022 2778205 := bbase (se 3 (by rfl) ⟨520913, by rfl⟩ : syracuseStep 2778205 = 1041827) (by norm_num)
theorem B3515501 : Blo 1646022 3515501 := bbase (se 3 (by rfl) ⟨659156, by rfl⟩ : syracuseStep 3515501 = 1318313) (by norm_num)
theorem B1852537 : Blo 1646022 1852537 := bbase (se 2 (by rfl) ⟨694701, by rfl⟩ : syracuseStep 1852537 = 1389403) (by norm_num)
theorem B3703949 : Blo 1646022 3703949 := bbase (se 3 (by rfl) ⟨694490, by rfl⟩ : syracuseStep 3703949 = 1388981) (by norm_num)
theorem B1852573 : Blo 1646022 1852573 := bbase (se 3 (by rfl) ⟨347357, by rfl⟩ : syracuseStep 1852573 = 694715) (by norm_num)
theorem B2778293 : Blo 1646022 2778293 := bbase (se 5 (by rfl) ⟨130232, by rfl⟩ : syracuseStep 2778293 = 260465) (by norm_num)
theorem B1852609 : Blo 1646022 1852609 := bbase (se 2 (by rfl) ⟨694728, by rfl⟩ : syracuseStep 1852609 = 1389457) (by norm_num)
theorem B3704021 : Blo 1646022 3704021 := bbase (se 7 (by rfl) ⟨43406, by rfl⟩ : syracuseStep 3704021 = 86813) (by norm_num)
theorem B4170973 : Blo 1646022 4170973 := bbase (se 3 (by rfl) ⟨782057, by rfl⟩ : syracuseStep 4170973 = 1564115) (by norm_num)
theorem B1852645 : Blo 1646022 1852645 := bbase (se 4 (by rfl) ⟨173685, by rfl⟩ : syracuseStep 1852645 = 347371) (by norm_num)
theorem B1852681 : Blo 1646022 1852681 := bbase (se 2 (by rfl) ⟨694755, by rfl⟩ : syracuseStep 1852681 = 1389511) (by norm_num)
theorem B3704093 : Blo 1646022 3704093 := bbase (se 3 (by rfl) ⟨694517, by rfl⟩ : syracuseStep 3704093 = 1389035) (by norm_num)
theorem B6251813 : Blo 1646022 6251813 := bbase (se 4 (by rfl) ⟨586107, by rfl⟩ : syracuseStep 6251813 = 1172215) (by norm_num)
theorem B7038245 : Blo 1646022 7038245 := bbase (se 4 (by rfl) ⟨659835, by rfl⟩ : syracuseStep 7038245 = 1319671) (by norm_num)
theorem B1852717 : Blo 1646022 1852717 := bbase (se 3 (by rfl) ⟨347384, by rfl⟩ : syracuseStep 1852717 = 694769) (by norm_num)
theorem B2778421 : Blo 1646022 2778421 := bbase (se 5 (by rfl) ⟨130238, by rfl⟩ : syracuseStep 2778421 = 260477) (by norm_num)
theorem B5276981 : Blo 1646022 5276981 := bbase (se 5 (by rfl) ⟨247358, by rfl⟩ : syracuseStep 5276981 = 494717) (by norm_num)
theorem B4171085 : Blo 1646022 4171085 := bbase (se 3 (by rfl) ⟨782078, by rfl⟩ : syracuseStep 4171085 = 1564157) (by norm_num)
theorem B1852753 : Blo 1646022 1852753 := bbase (se 2 (by rfl) ⟨694782, by rfl⟩ : syracuseStep 1852753 = 1389565) (by norm_num)
theorem B10020181 : Blo 1646022 10020181 := bbase (se 12 (by rfl) ⟨3669, by rfl⟩ : syracuseStep 10020181 = 7339) (by norm_num)
theorem B3704165 : Blo 1646022 3704165 := bbase (se 4 (by rfl) ⟨347265, by rfl⟩ : syracuseStep 3704165 = 694531) (by norm_num)
theorem B5555573 : Blo 1646022 5555573 := bbase (se 5 (by rfl) ⟨260417, by rfl⟩ : syracuseStep 5555573 = 520835) (by norm_num)
theorem B1852789 : Blo 1646022 1852789 := bbase (se 5 (by rfl) ⟨86849, by rfl⟩ : syracuseStep 1852789 = 173699) (by norm_num)
theorem B2778509 : Blo 1646022 2778509 := bbase (se 3 (by rfl) ⟨520970, by rfl⟩ : syracuseStep 2778509 = 1041941) (by norm_num)
theorem B1852825 : Blo 1646022 1852825 := bbase (se 2 (by rfl) ⟨694809, by rfl⟩ : syracuseStep 1852825 = 1389619) (by norm_num)
theorem B3704237 : Blo 1646022 3704237 := bbase (se 3 (by rfl) ⟨694544, by rfl⟩ : syracuseStep 3704237 = 1389089) (by norm_num)
theorem B1852861 : Blo 1646022 1852861 := bbase (se 3 (by rfl) ⟨347411, by rfl⟩ : syracuseStep 1852861 = 694823) (by norm_num)
theorem B1852897 : Blo 1646022 1852897 := bbase (se 2 (by rfl) ⟨694836, by rfl⟩ : syracuseStep 1852897 = 1389673) (by norm_num)
theorem B3704309 : Blo 1646022 3704309 := bbase (se 5 (by rfl) ⟨173639, by rfl⟩ : syracuseStep 3704309 = 347279) (by norm_num)
theorem B9381365 : Blo 1646022 9381365 := bbase (se 5 (by rfl) ⟨439751, by rfl⟩ : syracuseStep 9381365 = 879503) (by norm_num)
theorem B1852933 : Blo 1646022 1852933 := bbase (se 4 (by rfl) ⟨173712, by rfl⟩ : syracuseStep 1852933 = 347425) (by norm_num)
theorem B2778637 : Blo 1646022 2778637 := bbase (se 3 (by rfl) ⟨520994, by rfl⟩ : syracuseStep 2778637 = 1041989) (by norm_num)
theorem B4171277 : Blo 1646022 4171277 := bbase (se 3 (by rfl) ⟨782114, by rfl⟩ : syracuseStep 4171277 = 1564229) (by norm_num)
theorem B7038485 : Blo 1646022 7038485 := bbase (se 6 (by rfl) ⟨164964, by rfl⟩ : syracuseStep 7038485 = 329929) (by norm_num)
theorem B1852969 : Blo 1646022 1852969 := bbase (se 2 (by rfl) ⟨694863, by rfl⟩ : syracuseStep 1852969 = 1389727) (by norm_num)
theorem B2639413 : Blo 1646022 2639413 := bbase (se 5 (by rfl) ⟨123722, by rfl⟩ : syracuseStep 2639413 = 247445) (by norm_num)
theorem B3704381 : Blo 1646022 3704381 := bbase (se 3 (by rfl) ⟨694571, by rfl⟩ : syracuseStep 3704381 = 1389143) (by norm_num)
theorem B1853005 : Blo 1646022 1853005 := bbase (se 3 (by rfl) ⟨347438, by rfl⟩ : syracuseStep 1853005 = 694877) (by norm_num)
theorem B2778725 : Blo 1646022 2778725 := bbase (se 4 (by rfl) ⟨260505, by rfl⟩ : syracuseStep 2778725 = 521011) (by norm_num)
theorem B1877617 : Blo 1646022 1877617 := bbase (se 2 (by rfl) ⟨704106, by rfl⟩ : syracuseStep 1877617 = 1408213) (by norm_num)
theorem B1853041 : Blo 1646022 1853041 := bbase (se 2 (by rfl) ⟨694890, by rfl⟩ : syracuseStep 1853041 = 1389781) (by norm_num)
theorem B3704453 : Blo 1646022 3704453 := bbase (se 4 (by rfl) ⟨347292, by rfl⟩ : syracuseStep 3704453 = 694585) (by norm_num)
theorem B1853077 : Blo 1646022 1853077 := bbase (se 6 (by rfl) ⟨43431, by rfl⟩ : syracuseStep 1853077 = 86863) (by norm_num)
theorem B1877689 : Blo 1646022 1877689 := bbase (se 2 (by rfl) ⟨704133, by rfl⟩ : syracuseStep 1877689 = 1408267) (by norm_num)
theorem B1853113 : Blo 1646022 1853113 := bbase (se 2 (by rfl) ⟨694917, by rfl⟩ : syracuseStep 1853113 = 1389835) (by norm_num)
theorem B3704525 : Blo 1646022 3704525 := bbase (se 3 (by rfl) ⟨694598, by rfl⟩ : syracuseStep 3704525 = 1389197) (by norm_num)
theorem B1853149 : Blo 1646022 1853149 := bbase (se 3 (by rfl) ⟨347465, by rfl⟩ : syracuseStep 1853149 = 694931) (by norm_num)
theorem B2778853 : Blo 1646022 2778853 := bbase (se 4 (by rfl) ⟨260517, by rfl⟩ : syracuseStep 2778853 = 521035) (by norm_num)
theorem B1853185 : Blo 1646022 1853185 := bbase (se 2 (by rfl) ⟨694944, by rfl⟩ : syracuseStep 1853185 = 1389889) (by norm_num)
theorem B3704597 : Blo 1646022 3704597 := bbase (se 6 (by rfl) ⟨86826, by rfl⟩ : syracuseStep 3704597 = 173653) (by norm_num)
theorem B5556005 : Blo 1646022 5556005 := bbase (se 4 (by rfl) ⟨520875, by rfl⟩ : syracuseStep 5556005 = 1041751) (by norm_num)
theorem B4450085 : Blo 1646022 4450085 := bbase (se 4 (by rfl) ⟨417195, by rfl⟩ : syracuseStep 4450085 = 834391) (by norm_num)
theorem B1853221 : Blo 1646022 1853221 := bbase (se 4 (by rfl) ⟨173739, by rfl⟩ : syracuseStep 1853221 = 347479) (by norm_num)
theorem B2778941 : Blo 1646022 2778941 := bbase (se 3 (by rfl) ⟨521051, by rfl⟩ : syracuseStep 2778941 = 1042103) (by norm_num)
theorem B1853257 : Blo 1646022 1853257 := bbase (se 2 (by rfl) ⟨694971, by rfl⟩ : syracuseStep 1853257 = 1389943) (by norm_num)
theorem B3704669 : Blo 1646022 3704669 := bbase (se 3 (by rfl) ⟨694625, by rfl⟩ : syracuseStep 3704669 = 1389251) (by norm_num)
theorem B1853293 : Blo 1646022 1853293 := bbase (se 3 (by rfl) ⟨347492, by rfl⟩ : syracuseStep 1853293 = 694985) (by norm_num)
theorem B4687733 : Blo 1646022 4687733 := bbase (se 5 (by rfl) ⟨219737, by rfl⟩ : syracuseStep 4687733 = 439475) (by norm_num)
theorem B6014837 : Blo 1646022 6014837 := bbase (se 5 (by rfl) ⟨281945, by rfl⟩ : syracuseStep 6014837 = 563891) (by norm_num)
theorem B6342533 : Blo 1646022 6342533 := bbase (se 4 (by rfl) ⟨594612, by rfl⟩ : syracuseStep 6342533 = 1189225) (by norm_num)
theorem B1853329 : Blo 1646022 1853329 := bbase (se 2 (by rfl) ⟨694998, by rfl⟩ : syracuseStep 1853329 = 1389997) (by norm_num)
theorem B3704741 : Blo 1646022 3704741 := bbase (se 4 (by rfl) ⟨347319, by rfl⟩ : syracuseStep 3704741 = 694639) (by norm_num)
theorem B1853365 : Blo 1646022 1853365 := bbase (se 5 (by rfl) ⟨86876, by rfl⟩ : syracuseStep 1853365 = 173753) (by norm_num)
theorem B2779069 : Blo 1646022 2779069 := bbase (se 3 (by rfl) ⟨521075, by rfl⟩ : syracuseStep 2779069 = 1042151) (by norm_num)
theorem B1853401 : Blo 1646022 1853401 := bbase (se 2 (by rfl) ⟨695025, by rfl⟩ : syracuseStep 1853401 = 1390051) (by norm_num)
theorem B3516389 : Blo 1646022 3516389 := bbase (se 4 (by rfl) ⟨329661, by rfl⟩ : syracuseStep 3516389 = 659323) (by norm_num)
theorem B3704813 : Blo 1646022 3704813 := bbase (se 3 (by rfl) ⟨694652, by rfl⟩ : syracuseStep 3704813 = 1389305) (by norm_num)
theorem B1853437 : Blo 1646022 1853437 := bbase (se 3 (by rfl) ⟨347519, by rfl⟩ : syracuseStep 1853437 = 695039) (by norm_num)
theorem B2779157 : Blo 1646022 2779157 := bbase (se 6 (by rfl) ⟨65136, by rfl⟩ : syracuseStep 2779157 = 130273) (by norm_num)
theorem B1853473 : Blo 1646022 1853473 := bbase (se 2 (by rfl) ⟨695052, by rfl⟩ : syracuseStep 1853473 = 1390105) (by norm_num)
theorem B8341541 : Blo 1646022 8341541 := bbase (se 4 (by rfl) ⟨782019, by rfl⟩ : syracuseStep 8341541 = 1564039) (by norm_num)
theorem B3704885 : Blo 1646022 3704885 := bbase (se 5 (by rfl) ⟨173666, by rfl⟩ : syracuseStep 3704885 = 347333) (by norm_num)
theorem B1853509 : Blo 1646022 1853509 := bbase (se 4 (by rfl) ⟨173766, by rfl⟩ : syracuseStep 1853509 = 347533) (by norm_num)
theorem B3516509 : Blo 1646022 3516509 := bbase (se 3 (by rfl) ⟨659345, by rfl⟩ : syracuseStep 3516509 = 1318691) (by norm_num)
theorem B1853545 : Blo 1646022 1853545 := bbase (se 2 (by rfl) ⟨695079, by rfl⟩ : syracuseStep 1853545 = 1390159) (by norm_num)
theorem B3704957 : Blo 1646022 3704957 := bbase (se 3 (by rfl) ⟨694679, by rfl⟩ : syracuseStep 3704957 = 1389359) (by norm_num)
theorem B1853581 : Blo 1646022 1853581 := bbase (se 3 (by rfl) ⟨347546, by rfl⟩ : syracuseStep 1853581 = 695093) (by norm_num)
theorem B2779285 : Blo 1646022 2779285 := bbase (se 6 (by rfl) ⟨65139, by rfl⟩ : syracuseStep 2779285 = 130279) (by norm_num)
theorem B7514261 : Blo 1646022 7514261 := bbase (se 6 (by rfl) ⟨176115, by rfl⟩ : syracuseStep 7514261 = 352231) (by norm_num)
theorem B2345125 : Blo 1646022 2345125 := bbase (se 4 (by rfl) ⟨219855, by rfl⟩ : syracuseStep 2345125 = 439711) (by norm_num)
theorem B2967725 : Blo 1646022 2967725 := bbase (se 3 (by rfl) ⟨556448, by rfl⟩ : syracuseStep 2967725 = 1112897) (by norm_num)
theorem B1853617 : Blo 1646022 1853617 := bbase (se 2 (by rfl) ⟨695106, by rfl⟩ : syracuseStep 1853617 = 1390213) (by norm_num)
theorem B3705029 : Blo 1646022 3705029 := bbase (se 4 (by rfl) ⟨347346, by rfl⟩ : syracuseStep 3705029 = 694693) (by norm_num)
theorem B26699989 : Blo 1646022 26699989 := bbase (se 7 (by rfl) ⟨312890, by rfl⟩ : syracuseStep 26699989 = 625781) (by norm_num)
theorem B5556437 : Blo 1646022 5556437 := bbase (se 7 (by rfl) ⟨65114, by rfl⟩ : syracuseStep 5556437 = 130229) (by norm_num)
theorem B1853653 : Blo 1646022 1853653 := bbase (se 7 (by rfl) ⟨21722, by rfl⟩ : syracuseStep 1853653 = 43445) (by norm_num)
theorem B2779373 : Blo 1646022 2779373 := bbase (se 3 (by rfl) ⟨521132, by rfl⟩ : syracuseStep 2779373 = 1042265) (by norm_num)
theorem B1853689 : Blo 1646022 1853689 := bbase (se 2 (by rfl) ⟨695133, by rfl⟩ : syracuseStep 1853689 = 1390267) (by norm_num)
theorem B3705101 : Blo 1646022 3705101 := bbase (se 3 (by rfl) ⟨694706, by rfl⟩ : syracuseStep 3705101 = 1389413) (by norm_num)
theorem B1853725 : Blo 1646022 1853725 := bbase (se 3 (by rfl) ⟨347573, by rfl⟩ : syracuseStep 1853725 = 695147) (by norm_num)
theorem B8898869 : Blo 1646022 8898869 := bbase (se 5 (by rfl) ⟨417134, by rfl⟩ : syracuseStep 8898869 = 834269) (by norm_num)
theorem B1853761 : Blo 1646022 1853761 := bbase (se 2 (by rfl) ⟨695160, by rfl⟩ : syracuseStep 1853761 = 1390321) (by norm_num)
theorem B3705173 : Blo 1646022 3705173 := bbase (se 10 (by rfl) ⟨5427, by rfl⟩ : syracuseStep 3705173 = 10855) (by norm_num)
theorem B1853797 : Blo 1646022 1853797 := bbase (se 4 (by rfl) ⟨173793, by rfl⟩ : syracuseStep 1853797 = 347587) (by norm_num)
theorem B2779501 : Blo 1646022 2779501 := bbase (se 3 (by rfl) ⟨521156, by rfl⟩ : syracuseStep 2779501 = 1042313) (by norm_num)
theorem B1853833 : Blo 1646022 1853833 := bbase (se 2 (by rfl) ⟨695187, by rfl⟩ : syracuseStep 1853833 = 1390375) (by norm_num)
theorem B3705245 : Blo 1646022 3705245 := bbase (se 3 (by rfl) ⟨694733, by rfl⟩ : syracuseStep 3705245 = 1389467) (by norm_num)
theorem B1853869 : Blo 1646022 1853869 := bbase (se 3 (by rfl) ⟨347600, by rfl⟩ : syracuseStep 1853869 = 695201) (by norm_num)
theorem B2083249 : Blo 1646022 2083249 := bbase (se 2 (by rfl) ⟨781218, by rfl⟩ : syracuseStep 2083249 = 1562437) (by norm_num)
theorem B8333765 : Blo 1646022 8333765 := bbase (se 4 (by rfl) ⟨781290, by rfl⟩ : syracuseStep 8333765 = 1562581) (by norm_num)
theorem B6252997 : Blo 1646022 6252997 := bbase (se 4 (by rfl) ⟨586218, by rfl⟩ : syracuseStep 6252997 = 1172437) (by norm_num)
theorem B2779589 : Blo 1646022 2779589 := bbase (se 4 (by rfl) ⟨260586, by rfl⟩ : syracuseStep 2779589 = 521173) (by norm_num)
theorem B1853905 : Blo 1646022 1853905 := bbase (se 2 (by rfl) ⟨695214, by rfl⟩ : syracuseStep 1853905 = 1390429) (by norm_num)
theorem B3705317 : Blo 1646022 3705317 := bbase (se 4 (by rfl) ⟨347373, by rfl⟩ : syracuseStep 3705317 = 694747) (by norm_num)
theorem B2288101 : Blo 1646022 2288101 := bbase (se 4 (by rfl) ⟨214509, by rfl⟩ : syracuseStep 2288101 = 429019) (by norm_num)
theorem B1853941 : Blo 1646022 1853941 := bbase (se 5 (by rfl) ⟨86903, by rfl⟩ : syracuseStep 1853941 = 173807) (by norm_num)
theorem B4688405 : Blo 1646022 4688405 := bbase (se 6 (by rfl) ⟨109884, by rfl⟩ : syracuseStep 4688405 = 219769) (by norm_num)
theorem B1853977 : Blo 1646022 1853977 := bbase (se 2 (by rfl) ⟨695241, by rfl⟩ : syracuseStep 1853977 = 1390483) (by norm_num)
theorem B2968093 : Blo 1646022 2968093 := bbase (se 3 (by rfl) ⟨556517, by rfl⟩ : syracuseStep 2968093 = 1113035) (by norm_num)
theorem B2673197 : Blo 1646022 2673197 := bbase (se 3 (by rfl) ⟨501224, by rfl⟩ : syracuseStep 2673197 = 1002449) (by norm_num)
theorem B3705389 : Blo 1646022 3705389 := bbase (se 3 (by rfl) ⟨694760, by rfl⟩ : syracuseStep 3705389 = 1389521) (by norm_num)
theorem B1854013 : Blo 1646022 1854013 := bbase (se 3 (by rfl) ⟨347627, by rfl⟩ : syracuseStep 1854013 = 695255) (by norm_num)
theorem B2779717 : Blo 1646022 2779717 := bbase (se 4 (by rfl) ⟨260598, by rfl⟩ : syracuseStep 2779717 = 521197) (by norm_num)
theorem B10152533 : Blo 1646022 10152533 := bbase (se 8 (by rfl) ⟨59487, by rfl⟩ : syracuseStep 10152533 = 118975) (by norm_num)
theorem B2083421 : Blo 1646022 2083421 := bbase (se 3 (by rfl) ⟨390641, by rfl⟩ : syracuseStep 2083421 = 781283) (by norm_num)
theorem B3705461 : Blo 1646022 3705461 := bbase (se 5 (by rfl) ⟨173693, by rfl⟩ : syracuseStep 3705461 = 347387) (by norm_num)
theorem B5556869 : Blo 1646022 5556869 := bbase (se 4 (by rfl) ⟨520956, by rfl⟩ : syracuseStep 5556869 = 1041913) (by norm_num)
theorem B2083477 : Blo 1646022 2083477 := bbase (se 6 (by rfl) ⟨48831, by rfl⟩ : syracuseStep 2083477 = 97663) (by norm_num)
theorem B2779805 : Blo 1646022 2779805 := bbase (se 3 (by rfl) ⟨521213, by rfl⟩ : syracuseStep 2779805 = 1042427) (by norm_num)
theorem B3705533 : Blo 1646022 3705533 := bbase (se 3 (by rfl) ⟨694787, by rfl⟩ : syracuseStep 3705533 = 1389575) (by norm_num)
theorem B3517141 : Blo 1646022 3517141 := bbase (se 7 (by rfl) ⟨41216, by rfl⟩ : syracuseStep 3517141 = 82433) (by norm_num)
theorem B3959533 : Blo 1646022 3959533 := bbase (se 3 (by rfl) ⟨742412, by rfl⟩ : syracuseStep 3959533 = 1484825) (by norm_num)
theorem B2083573 : Blo 1646022 2083573 := bbase (se 5 (by rfl) ⟨97667, by rfl⟩ : syracuseStep 2083573 = 195335) (by norm_num)
theorem B6253301 : Blo 1646022 6253301 := bbase (se 5 (by rfl) ⟨293123, by rfl⟩ : syracuseStep 6253301 = 586247) (by norm_num)
theorem B2345717 : Blo 1646022 2345717 := bbase (se 5 (by rfl) ⟨109955, by rfl⟩ : syracuseStep 2345717 = 219911) (by norm_num)
theorem B3705605 : Blo 1646022 3705605 := bbase (se 4 (by rfl) ⟨347400, by rfl⟩ : syracuseStep 3705605 = 694801) (by norm_num)
theorem B2779933 : Blo 1646022 2779933 := bbase (se 3 (by rfl) ⟨521237, by rfl⟩ : syracuseStep 2779933 = 1042475) (by norm_num)
theorem B3337013 : Blo 1646022 3337013 := bbase (se 5 (by rfl) ⟨156422, by rfl⟩ : syracuseStep 3337013 = 312845) (by norm_num)
theorem B2345797 : Blo 1646022 2345797 := bbase (se 4 (by rfl) ⟨219918, by rfl⟩ : syracuseStep 2345797 = 439837) (by norm_num)
theorem B3705677 : Blo 1646022 3705677 := bbase (se 3 (by rfl) ⟨694814, by rfl⟩ : syracuseStep 3705677 = 1389629) (by norm_num)
theorem B2780021 : Blo 1646022 2780021 := bbase (se 5 (by rfl) ⟨130313, by rfl⟩ : syracuseStep 2780021 = 260627) (by norm_num)
theorem B3705749 : Blo 1646022 3705749 := bbase (se 6 (by rfl) ⟨86853, by rfl⟩ : syracuseStep 3705749 = 173707) (by norm_num)
theorem B2083745 : Blo 1646022 2083745 := bbase (se 2 (by rfl) ⟨781404, by rfl⟩ : syracuseStep 2083745 = 1562809) (by norm_num)
theorem B2345917 : Blo 1646022 2345917 := bbase (se 3 (by rfl) ⟨439859, by rfl⟩ : syracuseStep 2345917 = 879719) (by norm_num)
theorem B4688837 : Blo 1646022 4688837 := bbase (se 4 (by rfl) ⟨439578, by rfl⟩ : syracuseStep 4688837 = 879157) (by norm_num)
theorem B2083801 : Blo 1646022 2083801 := bbase (se 2 (by rfl) ⟨781425, by rfl⟩ : syracuseStep 2083801 = 1562851) (by norm_num)
theorem B3705821 : Blo 1646022 3705821 := bbase (se 3 (by rfl) ⟨694841, by rfl⟩ : syracuseStep 3705821 = 1389683) (by norm_num)
theorem B2780149 : Blo 1646022 2780149 := bbase (se 5 (by rfl) ⟨130319, by rfl⟩ : syracuseStep 2780149 = 260639) (by norm_num)
theorem B2346013 : Blo 1646022 2346013 := bbase (se 3 (by rfl) ⟨439877, by rfl⟩ : syracuseStep 2346013 = 879755) (by norm_num)
theorem B3705893 : Blo 1646022 3705893 := bbase (se 4 (by rfl) ⟨347427, by rfl⟩ : syracuseStep 3705893 = 694855) (by norm_num)
theorem B5557301 : Blo 1646022 5557301 := bbase (se 5 (by rfl) ⟨260498, by rfl⟩ : syracuseStep 5557301 = 520997) (by norm_num)
theorem B2083897 : Blo 1646022 2083897 := bbase (se 2 (by rfl) ⟨781461, by rfl⟩ : syracuseStep 2083897 = 1562923) (by norm_num)
theorem B2780237 : Blo 1646022 2780237 := bbase (se 3 (by rfl) ⟨521294, by rfl⟩ : syracuseStep 2780237 = 1042589) (by norm_num)
theorem B20024405 : Blo 1646022 20024405 := bbase (se 8 (by rfl) ⟨117330, by rfl⟩ : syracuseStep 20024405 = 234661) (by norm_num)
theorem B3705965 : Blo 1646022 3705965 := bbase (se 3 (by rfl) ⟨694868, by rfl⟩ : syracuseStep 3705965 = 1389737) (by norm_num)
theorem B3706037 : Blo 1646022 3706037 := bbase (se 5 (by rfl) ⟨173720, by rfl⟩ : syracuseStep 3706037 = 347441) (by norm_num)
theorem B2469053 : Blo 1646022 2469053 := bbase (se 3 (by rfl) ⟨462947, by rfl⟩ : syracuseStep 2469053 = 925895) (by norm_num)
theorem B2780365 : Blo 1646022 2780365 := bbase (se 3 (by rfl) ⟨521318, by rfl⟩ : syracuseStep 2780365 = 1042637) (by norm_num)
theorem B2469077 : Blo 1646022 2469077 := bbase (se 7 (by rfl) ⟨28934, by rfl⟩ : syracuseStep 2469077 = 57869) (by norm_num)
theorem B2084069 : Blo 1646022 2084069 := bbase (se 4 (by rfl) ⟨195381, by rfl⟩ : syracuseStep 2084069 = 390763) (by norm_num)
theorem B2469101 : Blo 1646022 2469101 := bbase (se 3 (by rfl) ⟨462956, by rfl⟩ : syracuseStep 2469101 = 925913) (by norm_num)
theorem B3706109 : Blo 1646022 3706109 := bbase (se 3 (by rfl) ⟨694895, by rfl⟩ : syracuseStep 3706109 = 1389791) (by norm_num)
theorem B2469125 : Blo 1646022 2469125 := bbase (se 4 (by rfl) ⟨231480, by rfl⟩ : syracuseStep 2469125 = 462961) (by norm_num)
theorem B11865365 : Blo 1646022 11865365 := bbase (se 6 (by rfl) ⟨278094, by rfl⟩ : syracuseStep 11865365 = 556189) (by norm_num)
theorem B2469149 : Blo 1646022 2469149 := bbase (se 3 (by rfl) ⟨462965, by rfl⟩ : syracuseStep 2469149 = 925931) (by norm_num)
theorem B2084125 : Blo 1646022 2084125 := bbase (se 3 (by rfl) ⟨390773, by rfl⟩ : syracuseStep 2084125 = 781547) (by norm_num)
theorem B2780453 : Blo 1646022 2780453 := bbase (se 4 (by rfl) ⟨260667, by rfl⟩ : syracuseStep 2780453 = 521335) (by norm_num)
theorem B2469173 : Blo 1646022 2469173 := bbase (se 5 (by rfl) ⟨115742, by rfl⟩ : syracuseStep 2469173 = 231485) (by norm_num)
theorem B15650101 : Blo 1646022 15650101 := bbase (se 5 (by rfl) ⟨733598, by rfl⟩ : syracuseStep 15650101 = 1467197) (by norm_num)
theorem B8342837 : Blo 1646022 8342837 := bbase (se 5 (by rfl) ⟨391070, by rfl⟩ : syracuseStep 8342837 = 782141) (by norm_num)
theorem B3706181 : Blo 1646022 3706181 := bbase (se 4 (by rfl) ⟨347454, by rfl⟩ : syracuseStep 3706181 = 694909) (by norm_num)
theorem B2469197 : Blo 1646022 2469197 := bbase (se 3 (by rfl) ⟨462974, by rfl⟩ : syracuseStep 2469197 = 925949) (by norm_num)
theorem B2469221 : Blo 1646022 2469221 := bbase (se 4 (by rfl) ⟨231489, by rfl⟩ : syracuseStep 2469221 = 462979) (by norm_num)
theorem B2469245 : Blo 1646022 2469245 := bbase (se 3 (by rfl) ⟨462983, by rfl⟩ : syracuseStep 2469245 = 925967) (by norm_num)
theorem B2084221 : Blo 1646022 2084221 := bbase (se 3 (by rfl) ⟨390791, by rfl⟩ : syracuseStep 2084221 = 781583) (by norm_num)
theorem B7032197 : Blo 1646022 7032197 := bbase (se 4 (by rfl) ⟨659268, by rfl⟩ : syracuseStep 7032197 = 1318537) (by norm_num)
theorem B3706253 : Blo 1646022 3706253 := bbase (se 3 (by rfl) ⟨694922, by rfl⟩ : syracuseStep 3706253 = 1389845) (by norm_num)
theorem B2469269 : Blo 1646022 2469269 := bbase (se 6 (by rfl) ⟨57873, by rfl⟩ : syracuseStep 2469269 = 115747) (by norm_num)
theorem B2780581 : Blo 1646022 2780581 := bbase (se 4 (by rfl) ⟨260679, by rfl⟩ : syracuseStep 2780581 = 521359) (by norm_num)
theorem B2469293 : Blo 1646022 2469293 := bbase (se 3 (by rfl) ⟨462992, by rfl⟩ : syracuseStep 2469293 = 925985) (by norm_num)
theorem B2469317 : Blo 1646022 2469317 := bbase (se 4 (by rfl) ⟨231498, by rfl⟩ : syracuseStep 2469317 = 462997) (by norm_num)
theorem B3706325 : Blo 1646022 3706325 := bbase (se 7 (by rfl) ⟨43433, by rfl⟩ : syracuseStep 3706325 = 86867) (by norm_num)
theorem B2469341 : Blo 1646022 2469341 := bbase (se 3 (by rfl) ⟨463001, by rfl⟩ : syracuseStep 2469341 = 926003) (by norm_num)
theorem B5557733 : Blo 1646022 5557733 := bbase (se 4 (by rfl) ⟨521037, by rfl⟩ : syracuseStep 5557733 = 1042075) (by norm_num)
theorem B2469365 : Blo 1646022 2469365 := bbase (se 5 (by rfl) ⟨115751, by rfl⟩ : syracuseStep 2469365 = 231503) (by norm_num)
theorem B2780669 : Blo 1646022 2780669 := bbase (se 3 (by rfl) ⟨521375, by rfl⟩ : syracuseStep 2780669 = 1042751) (by norm_num)
theorem B2469389 : Blo 1646022 2469389 := bbase (se 3 (by rfl) ⟨463010, by rfl⟩ : syracuseStep 2469389 = 926021) (by norm_num)
theorem B3706397 : Blo 1646022 3706397 := bbase (se 3 (by rfl) ⟨694949, by rfl⟩ : syracuseStep 3706397 = 1389899) (by norm_num)
theorem B2469413 : Blo 1646022 2469413 := bbase (se 4 (by rfl) ⟨231507, by rfl⟩ : syracuseStep 2469413 = 463015) (by norm_num)
theorem B2084393 : Blo 1646022 2084393 := bbase (se 2 (by rfl) ⟨781647, by rfl⟩ : syracuseStep 2084393 = 1563295) (by norm_num)
theorem B2469437 : Blo 1646022 2469437 := bbase (se 3 (by rfl) ⟨463019, by rfl⟩ : syracuseStep 2469437 = 926039) (by norm_num)
theorem B3518029 : Blo 1646022 3518029 := bbase (se 3 (by rfl) ⟨659630, by rfl⟩ : syracuseStep 3518029 = 1319261) (by norm_num)
theorem B2469461 : Blo 1646022 2469461 := bbase (se 8 (by rfl) ⟨14469, by rfl⟩ : syracuseStep 2469461 = 28939) (by norm_num)
theorem B2084449 : Blo 1646022 2084449 := bbase (se 2 (by rfl) ⟨781668, by rfl⟩ : syracuseStep 2084449 = 1563337) (by norm_num)
theorem B3706469 : Blo 1646022 3706469 := bbase (se 4 (by rfl) ⟨347481, by rfl⟩ : syracuseStep 3706469 = 694963) (by norm_num)
theorem B2469485 : Blo 1646022 2469485 := bbase (se 3 (by rfl) ⟨463028, by rfl⟩ : syracuseStep 2469485 = 926057) (by norm_num)
theorem B2780797 : Blo 1646022 2780797 := bbase (se 3 (by rfl) ⟨521399, by rfl⟩ : syracuseStep 2780797 = 1042799) (by norm_num)
theorem B2469509 : Blo 1646022 2469509 := bbase (se 4 (by rfl) ⟨231516, by rfl⟩ : syracuseStep 2469509 = 463033) (by norm_num)
theorem B2469533 : Blo 1646022 2469533 := bbase (se 3 (by rfl) ⟨463037, by rfl⟩ : syracuseStep 2469533 = 926075) (by norm_num)
theorem B3526301 : Blo 1646022 3526301 := bbase (se 3 (by rfl) ⟨661181, by rfl⟩ : syracuseStep 3526301 = 1322363) (by norm_num)
theorem B3706541 : Blo 1646022 3706541 := bbase (se 3 (by rfl) ⟨694976, by rfl⟩ : syracuseStep 3706541 = 1389953) (by norm_num)
theorem B4689589 : Blo 1646022 4689589 := bbase (se 5 (by rfl) ⟨219824, by rfl⟩ : syracuseStep 4689589 = 439649) (by norm_num)
theorem B2469557 : Blo 1646022 2469557 := bbase (se 5 (by rfl) ⟨115760, by rfl⟩ : syracuseStep 2469557 = 231521) (by norm_num)
theorem B2084545 : Blo 1646022 2084545 := bbase (se 2 (by rfl) ⟨781704, by rfl⟩ : syracuseStep 2084545 = 1563409) (by norm_num)
theorem B3518149 : Blo 1646022 3518149 := bbase (se 4 (by rfl) ⟨329826, by rfl⟩ : syracuseStep 3518149 = 659653) (by norm_num)
theorem B2469581 : Blo 1646022 2469581 := bbase (se 3 (by rfl) ⟨463046, by rfl⟩ : syracuseStep 2469581 = 926093) (by norm_num)
theorem B8335061 : Blo 1646022 8335061 := bbase (se 7 (by rfl) ⟨97676, by rfl⟩ : syracuseStep 8335061 = 195353) (by norm_num)
theorem B2780885 : Blo 1646022 2780885 := bbase (se 7 (by rfl) ⟨32588, by rfl⟩ : syracuseStep 2780885 = 65177) (by norm_num)
theorem B2469605 : Blo 1646022 2469605 := bbase (se 4 (by rfl) ⟨231525, by rfl⟩ : syracuseStep 2469605 = 463051) (by norm_num)
theorem B3124973 : Blo 1646022 3124973 := bbase (se 3 (by rfl) ⟨585932, by rfl⟩ : syracuseStep 3124973 = 1171865) (by norm_num)
theorem B3706613 : Blo 1646022 3706613 := bbase (se 5 (by rfl) ⟨173747, by rfl⟩ : syracuseStep 3706613 = 347495) (by norm_num)
theorem B2469629 : Blo 1646022 2469629 := bbase (se 3 (by rfl) ⟨463055, by rfl⟩ : syracuseStep 2469629 = 926111) (by norm_num)
theorem B2469653 : Blo 1646022 2469653 := bbase (se 6 (by rfl) ⟨57882, by rfl⟩ : syracuseStep 2469653 = 115765) (by norm_num)
theorem B2469677 : Blo 1646022 2469677 := bbase (se 3 (by rfl) ⟨463064, by rfl⟩ : syracuseStep 2469677 = 926129) (by norm_num)
theorem B3567413 : Blo 1646022 3567413 := bbase (se 5 (by rfl) ⟨167222, by rfl⟩ : syracuseStep 3567413 = 334445) (by norm_num)
theorem B3706685 : Blo 1646022 3706685 := bbase (se 3 (by rfl) ⟨695003, by rfl⟩ : syracuseStep 3706685 = 1390007) (by norm_num)
theorem B2469701 : Blo 1646022 2469701 := bbase (se 4 (by rfl) ⟨231534, by rfl⟩ : syracuseStep 2469701 = 463069) (by norm_num)
theorem B2781013 : Blo 1646022 2781013 := bbase (se 9 (by rfl) ⟨8147, by rfl⟩ : syracuseStep 2781013 = 16295) (by norm_num)
theorem B2469725 : Blo 1646022 2469725 := bbase (se 3 (by rfl) ⟨463073, by rfl⟩ : syracuseStep 2469725 = 926147) (by norm_num)
theorem B2084717 : Blo 1646022 2084717 := bbase (se 3 (by rfl) ⟨390884, by rfl⟩ : syracuseStep 2084717 = 781769) (by norm_num)
theorem B2469749 : Blo 1646022 2469749 := bbase (se 5 (by rfl) ⟨115769, by rfl⟩ : syracuseStep 2469749 = 231539) (by norm_num)
theorem B1978229 : Blo 1646022 1978229 := bbase (se 5 (by rfl) ⟨92729, by rfl⟩ : syracuseStep 1978229 = 185459) (by norm_num)
theorem B3125117 : Blo 1646022 3125117 := bbase (se 3 (by rfl) ⟨585959, by rfl⟩ : syracuseStep 3125117 = 1171919) (by norm_num)
theorem B3706757 : Blo 1646022 3706757 := bbase (se 4 (by rfl) ⟨347508, by rfl⟩ : syracuseStep 3706757 = 695017) (by norm_num)
theorem B2969477 : Blo 1646022 2969477 := bbase (se 4 (by rfl) ⟨278388, by rfl⟩ : syracuseStep 2969477 = 556777) (by norm_num)
theorem B2469773 : Blo 1646022 2469773 := bbase (se 3 (by rfl) ⟨463082, by rfl⟩ : syracuseStep 2469773 = 926165) (by norm_num)
theorem B5558165 : Blo 1646022 5558165 := bbase (se 6 (by rfl) ⟨130269, by rfl⟩ : syracuseStep 5558165 = 260539) (by norm_num)
theorem B2469797 : Blo 1646022 2469797 := bbase (se 4 (by rfl) ⟨231543, by rfl⟩ : syracuseStep 2469797 = 463087) (by norm_num)
theorem B2084773 : Blo 1646022 2084773 := bbase (se 4 (by rfl) ⟨195447, by rfl⟩ : syracuseStep 2084773 = 390895) (by norm_num)
theorem B2142137 : Blo 1646022 2142137 := bbase (se 2 (by rfl) ⟨803301, by rfl⟩ : syracuseStep 2142137 = 1606603) (by norm_num)
theorem B2469821 : Blo 1646022 2469821 := bbase (se 3 (by rfl) ⟨463091, by rfl⟩ : syracuseStep 2469821 = 926183) (by norm_num)
theorem B3518405 : Blo 1646022 3518405 := bbase (se 4 (by rfl) ⟨329850, by rfl⟩ : syracuseStep 3518405 = 659701) (by norm_num)
theorem B3706829 : Blo 1646022 3706829 := bbase (se 3 (by rfl) ⟨695030, by rfl⟩ : syracuseStep 3706829 = 1390061) (by norm_num)
theorem B2469845 : Blo 1646022 2469845 := bbase (se 7 (by rfl) ⟨28943, by rfl⟩ : syracuseStep 2469845 = 57887) (by norm_num)
theorem B2469869 : Blo 1646022 2469869 := bbase (se 3 (by rfl) ⟨463100, by rfl⟩ : syracuseStep 2469869 = 926201) (by norm_num)
theorem B2469893 : Blo 1646022 2469893 := bbase (se 4 (by rfl) ⟨231552, by rfl⟩ : syracuseStep 2469893 = 463105) (by norm_num)
theorem B2084869 : Blo 1646022 2084869 := bbase (se 4 (by rfl) ⟨195456, by rfl⟩ : syracuseStep 2084869 = 390913) (by norm_num)
theorem B3706901 : Blo 1646022 3706901 := bbase (se 6 (by rfl) ⟨86880, by rfl⟩ : syracuseStep 3706901 = 173761) (by norm_num)
theorem B2469917 : Blo 1646022 2469917 := bbase (se 3 (by rfl) ⟨463109, by rfl⟩ : syracuseStep 2469917 = 926219) (by norm_num)
theorem B2256925 : Blo 1646022 2256925 := bbase (se 3 (by rfl) ⟨423173, by rfl⟩ : syracuseStep 2256925 = 846347) (by norm_num)
theorem B2469941 : Blo 1646022 2469941 := bbase (se 5 (by rfl) ⟨115778, by rfl⟩ : syracuseStep 2469941 = 231557) (by norm_num)
theorem B2469965 : Blo 1646022 2469965 := bbase (se 3 (by rfl) ⟨463118, by rfl⟩ : syracuseStep 2469965 = 926237) (by norm_num)
theorem B3706973 : Blo 1646022 3706973 := bbase (se 3 (by rfl) ⟨695057, by rfl⟩ : syracuseStep 3706973 = 1390115) (by norm_num)
theorem B2469989 : Blo 1646022 2469989 := bbase (se 4 (by rfl) ⟨231561, by rfl⟩ : syracuseStep 2469989 = 463123) (by norm_num)
theorem B6680677 : Blo 1646022 6680677 := bbase (se 4 (by rfl) ⟨626313, by rfl⟩ : syracuseStep 6680677 = 1252627) (by norm_num)
theorem B2470013 : Blo 1646022 2470013 := bbase (se 3 (by rfl) ⟨463127, by rfl⟩ : syracuseStep 2470013 = 926255) (by norm_num)
theorem B2470037 : Blo 1646022 2470037 := bbase (se 6 (by rfl) ⟨57891, by rfl⟩ : syracuseStep 2470037 = 115783) (by norm_num)
theorem B3125405 : Blo 1646022 3125405 := bbase (se 3 (by rfl) ⟨586013, by rfl⟩ : syracuseStep 3125405 = 1172027) (by norm_num)
theorem B3707045 : Blo 1646022 3707045 := bbase (se 4 (by rfl) ⟨347535, by rfl⟩ : syracuseStep 3707045 = 695071) (by norm_num)
theorem B2470061 : Blo 1646022 2470061 := bbase (se 3 (by rfl) ⟨463136, by rfl⟩ : syracuseStep 2470061 = 926273) (by norm_num)
theorem B2085041 : Blo 1646022 2085041 := bbase (se 2 (by rfl) ⟨781890, by rfl⟩ : syracuseStep 2085041 = 1563781) (by norm_num)
theorem B2470085 : Blo 1646022 2470085 := bbase (se 4 (by rfl) ⟨231570, by rfl⟩ : syracuseStep 2470085 = 463141) (by norm_num)
theorem B2855125 : Blo 1646022 2855125 := bbase (se 7 (by rfl) ⟨33458, by rfl⟩ : syracuseStep 2855125 = 66917) (by norm_num)
theorem B8450261 : Blo 1646022 8450261 := bbase (se 7 (by rfl) ⟨99026, by rfl⟩ : syracuseStep 8450261 = 198053) (by norm_num)
theorem B2470109 : Blo 1646022 2470109 := bbase (se 3 (by rfl) ⟨463145, by rfl⟩ : syracuseStep 2470109 = 926291) (by norm_num)
theorem B2085097 : Blo 1646022 2085097 := bbase (se 2 (by rfl) ⟨781911, by rfl⟩ : syracuseStep 2085097 = 1563823) (by norm_num)
theorem B3707117 : Blo 1646022 3707117 := bbase (se 3 (by rfl) ⟨695084, by rfl⟩ : syracuseStep 3707117 = 1390169) (by norm_num)
theorem B2470133 : Blo 1646022 2470133 := bbase (se 5 (by rfl) ⟨115787, by rfl⟩ : syracuseStep 2470133 = 231575) (by norm_num)
theorem B2470157 : Blo 1646022 2470157 := bbase (se 3 (by rfl) ⟨463154, by rfl⟩ : syracuseStep 2470157 = 926309) (by norm_num)
theorem B2470181 : Blo 1646022 2470181 := bbase (se 4 (by rfl) ⟨231579, by rfl⟩ : syracuseStep 2470181 = 463159) (by norm_num)
theorem B3125557 : Blo 1646022 3125557 := bbase (se 5 (by rfl) ⟨146510, by rfl⟩ : syracuseStep 3125557 = 293021) (by norm_num)
theorem B3707189 : Blo 1646022 3707189 := bbase (se 5 (by rfl) ⟨173774, by rfl⟩ : syracuseStep 3707189 = 347549) (by norm_num)
theorem B2470205 : Blo 1646022 2470205 := bbase (se 3 (by rfl) ⟨463163, by rfl⟩ : syracuseStep 2470205 = 926327) (by norm_num)
theorem B5558597 : Blo 1646022 5558597 := bbase (se 4 (by rfl) ⟨521118, by rfl⟩ : syracuseStep 5558597 = 1042237) (by norm_num)
theorem B2085193 : Blo 1646022 2085193 := bbase (se 2 (by rfl) ⟨781947, by rfl⟩ : syracuseStep 2085193 = 1563895) (by norm_num)
theorem B2470229 : Blo 1646022 2470229 := bbase (se 10 (by rfl) ⟨3618, by rfl⟩ : syracuseStep 2470229 = 7237) (by norm_num)
theorem B2470253 : Blo 1646022 2470253 := bbase (se 3 (by rfl) ⟨463172, by rfl⟩ : syracuseStep 2470253 = 926345) (by norm_num)
theorem B3707261 : Blo 1646022 3707261 := bbase (se 3 (by rfl) ⟨695111, by rfl⟩ : syracuseStep 3707261 = 1390223) (by norm_num)
theorem B2470277 : Blo 1646022 2470277 := bbase (se 4 (by rfl) ⟨231588, by rfl⟩ : syracuseStep 2470277 = 463177) (by norm_num)
theorem B4010381 : Blo 1646022 4010381 := bbase (se 3 (by rfl) ⟨751946, by rfl⟩ : syracuseStep 4010381 = 1503893) (by norm_num)
theorem B2470301 : Blo 1646022 2470301 := bbase (se 3 (by rfl) ⟨463181, by rfl⟩ : syracuseStep 2470301 = 926363) (by norm_num)
theorem B2470325 : Blo 1646022 2470325 := bbase (se 5 (by rfl) ⟨115796, by rfl⟩ : syracuseStep 2470325 = 231593) (by norm_num)
theorem B10555829 : Blo 1646022 10555829 := bbase (se 5 (by rfl) ⟨494804, by rfl⟩ : syracuseStep 10555829 = 989609) (by norm_num)
theorem B7516597 : Blo 1646022 7516597 := bbase (se 5 (by rfl) ⟨352340, by rfl⟩ : syracuseStep 7516597 = 704681) (by norm_num)
theorem B3707333 : Blo 1646022 3707333 := bbase (se 4 (by rfl) ⟨347562, by rfl⟩ : syracuseStep 3707333 = 695125) (by norm_num)
theorem B2470349 : Blo 1646022 2470349 := bbase (se 3 (by rfl) ⟨463190, by rfl⟩ : syracuseStep 2470349 = 926381) (by norm_num)
theorem B21115349 : Blo 1646022 21115349 := bbase (se 7 (by rfl) ⟨247445, by rfl⟩ : syracuseStep 21115349 = 494891) (by norm_num)
theorem B2470373 : Blo 1646022 2470373 := bbase (se 4 (by rfl) ⟨231597, by rfl⟩ : syracuseStep 2470373 = 463195) (by norm_num)
theorem B2085365 : Blo 1646022 2085365 := bbase (se 5 (by rfl) ⟨97751, by rfl⟩ : syracuseStep 2085365 = 195503) (by norm_num)
theorem B2470397 : Blo 1646022 2470397 := bbase (se 3 (by rfl) ⟨463199, by rfl⟩ : syracuseStep 2470397 = 926399) (by norm_num)
theorem B3707405 : Blo 1646022 3707405 := bbase (se 3 (by rfl) ⟨695138, by rfl⟩ : syracuseStep 3707405 = 1390277) (by norm_num)
theorem B2470421 : Blo 1646022 2470421 := bbase (se 6 (by rfl) ⟨57900, by rfl⟩ : syracuseStep 2470421 = 115801) (by norm_num)
theorem B2470445 : Blo 1646022 2470445 := bbase (se 3 (by rfl) ⟨463208, by rfl⟩ : syracuseStep 2470445 = 926417) (by norm_num)
theorem B2085421 : Blo 1646022 2085421 := bbase (se 3 (by rfl) ⟨391016, by rfl⟩ : syracuseStep 2085421 = 782033) (by norm_num)
theorem B2470469 : Blo 1646022 2470469 := bbase (se 4 (by rfl) ⟨231606, by rfl⟩ : syracuseStep 2470469 = 463213) (by norm_num)
theorem B1978949 : Blo 1646022 1978949 := bbase (se 4 (by rfl) ⟨185526, by rfl⟩ : syracuseStep 1978949 = 371053) (by norm_num)
theorem B3707477 : Blo 1646022 3707477 := bbase (se 8 (by rfl) ⟨21723, by rfl⟩ : syracuseStep 3707477 = 43447) (by norm_num)
theorem B2470493 : Blo 1646022 2470493 := bbase (se 3 (by rfl) ⟨463217, by rfl⟩ : syracuseStep 2470493 = 926435) (by norm_num)
theorem B3125861 : Blo 1646022 3125861 := bbase (se 4 (by rfl) ⟨293049, by rfl⟩ : syracuseStep 3125861 = 586099) (by norm_num)
theorem B2470517 : Blo 1646022 2470517 := bbase (se 5 (by rfl) ⟨115805, by rfl⟩ : syracuseStep 2470517 = 231611) (by norm_num)
theorem B2470541 : Blo 1646022 2470541 := bbase (se 3 (by rfl) ⟨463226, by rfl⟩ : syracuseStep 2470541 = 926453) (by norm_num)
theorem B2085517 : Blo 1646022 2085517 := bbase (se 3 (by rfl) ⟨391034, by rfl⟩ : syracuseStep 2085517 = 782069) (by norm_num)
theorem B3707549 : Blo 1646022 3707549 := bbase (se 3 (by rfl) ⟨695165, by rfl⟩ : syracuseStep 3707549 = 1390331) (by norm_num)
theorem B2257565 : Blo 1646022 2257565 := bbase (se 3 (by rfl) ⟨423293, by rfl⟩ : syracuseStep 2257565 = 846587) (by norm_num)
theorem B7508645 : Blo 1646022 7508645 := bbase (se 4 (by rfl) ⟨703935, by rfl⟩ : syracuseStep 7508645 = 1407871) (by norm_num)
theorem B2470565 : Blo 1646022 2470565 := bbase (se 4 (by rfl) ⟨231615, by rfl⟩ : syracuseStep 2470565 = 463231) (by norm_num)
theorem B2470589 : Blo 1646022 2470589 := bbase (se 3 (by rfl) ⟨463235, by rfl⟩ : syracuseStep 2470589 = 926471) (by norm_num)
theorem B2470613 : Blo 1646022 2470613 := bbase (se 7 (by rfl) ⟨28952, by rfl⟩ : syracuseStep 2470613 = 57905) (by norm_num)
theorem B1757921 : Blo 1646022 1757921 := bbase (se 2 (by rfl) ⟨659220, by rfl⟩ : syracuseStep 1757921 = 1318441) (by norm_num)
theorem B3707621 : Blo 1646022 3707621 := bbase (se 4 (by rfl) ⟨347589, by rfl⟩ : syracuseStep 3707621 = 695179) (by norm_num)
theorem B2470637 : Blo 1646022 2470637 := bbase (se 3 (by rfl) ⟨463244, by rfl⟩ : syracuseStep 2470637 = 926489) (by norm_num)
theorem B5559029 : Blo 1646022 5559029 := bbase (se 5 (by rfl) ⟨260579, by rfl⟩ : syracuseStep 5559029 = 521159) (by norm_num)
theorem B2470661 : Blo 1646022 2470661 := bbase (se 4 (by rfl) ⟨231624, by rfl⟩ : syracuseStep 2470661 = 463249) (by norm_num)
theorem B1757981 : Blo 1646022 1757981 := bbase (se 3 (by rfl) ⟨329621, by rfl⟩ : syracuseStep 1757981 = 659243) (by norm_num)
theorem B2470685 : Blo 1646022 2470685 := bbase (se 3 (by rfl) ⟨463253, by rfl⟩ : syracuseStep 2470685 = 926507) (by norm_num)
theorem B3707693 : Blo 1646022 3707693 := bbase (se 3 (by rfl) ⟨695192, by rfl⟩ : syracuseStep 3707693 = 1390385) (by norm_num)
theorem B5935925 : Blo 1646022 5935925 := bbase (se 5 (by rfl) ⟨278246, by rfl⟩ : syracuseStep 5935925 = 556493) (by norm_num)
theorem B2470709 : Blo 1646022 2470709 := bbase (se 5 (by rfl) ⟨115814, by rfl⟩ : syracuseStep 2470709 = 231629) (by norm_num)
theorem B6255413 : Blo 1646022 6255413 := bbase (se 5 (by rfl) ⟨293222, by rfl⟩ : syracuseStep 6255413 = 586445) (by norm_num)
theorem B2085689 : Blo 1646022 2085689 := bbase (se 2 (by rfl) ⟨782133, by rfl⟩ : syracuseStep 2085689 = 1564267) (by norm_num)
theorem B3519293 : Blo 1646022 3519293 := bbase (se 3 (by rfl) ⟨659867, by rfl⟩ : syracuseStep 3519293 = 1319735) (by norm_num)
theorem B2470733 : Blo 1646022 2470733 := bbase (se 3 (by rfl) ⟨463262, by rfl⟩ : syracuseStep 2470733 = 926525) (by norm_num)
theorem B2470757 : Blo 1646022 2470757 := bbase (se 4 (by rfl) ⟨231633, by rfl⟩ : syracuseStep 2470757 = 463267) (by norm_num)
theorem B2085745 : Blo 1646022 2085745 := bbase (se 2 (by rfl) ⟨782154, by rfl⟩ : syracuseStep 2085745 = 1564309) (by norm_num)
theorem B7910261 : Blo 1646022 7910261 := bbase (se 5 (by rfl) ⟨370793, by rfl⟩ : syracuseStep 7910261 = 741587) (by norm_num)
theorem B3707765 : Blo 1646022 3707765 := bbase (se 5 (by rfl) ⟨173801, by rfl⟩ : syracuseStep 3707765 = 347603) (by norm_num)
theorem B1979257 : Blo 1646022 1979257 := bbase (se 2 (by rfl) ⟨742221, by rfl⟩ : syracuseStep 1979257 = 1484443) (by norm_num)
theorem B2470781 : Blo 1646022 2470781 := bbase (se 3 (by rfl) ⟨463271, by rfl⟩ : syracuseStep 2470781 = 926543) (by norm_num)
theorem B2675581 : Blo 1646022 2675581 := bbase (se 3 (by rfl) ⟨501671, by rfl⟩ : syracuseStep 2675581 = 1003343) (by norm_num)
theorem B4166549 : Blo 1646022 4166549 := bbase (se 6 (by rfl) ⟨97653, by rfl⟩ : syracuseStep 4166549 = 195307) (by norm_num)
theorem B2470805 : Blo 1646022 2470805 := bbase (se 6 (by rfl) ⟨57909, by rfl⟩ : syracuseStep 2470805 = 115819) (by norm_num)
theorem B1758109 : Blo 1646022 1758109 := bbase (se 3 (by rfl) ⟨329645, by rfl⟩ : syracuseStep 1758109 = 659291) (by norm_num)
theorem B2470829 : Blo 1646022 2470829 := bbase (se 3 (by rfl) ⟨463280, by rfl⟩ : syracuseStep 2470829 = 926561) (by norm_num)
theorem B3707837 : Blo 1646022 3707837 := bbase (se 3 (by rfl) ⟨695219, by rfl⟩ : syracuseStep 3707837 = 1390439) (by norm_num)
theorem B2470853 : Blo 1646022 2470853 := bbase (se 4 (by rfl) ⟨231642, by rfl⟩ : syracuseStep 2470853 = 463285) (by norm_num)
theorem B1979353 : Blo 1646022 1979353 := bbase (se 2 (by rfl) ⟨742257, by rfl⟩ : syracuseStep 1979353 = 1484515) (by norm_num)
theorem B2470877 : Blo 1646022 2470877 := bbase (se 3 (by rfl) ⟨463289, by rfl⟩ : syracuseStep 2470877 = 926579) (by norm_num)
theorem B8336357 : Blo 1646022 8336357 := bbase (se 4 (by rfl) ⟨781533, by rfl⟩ : syracuseStep 8336357 = 1563067) (by norm_num)
theorem B2470901 : Blo 1646022 2470901 := bbase (se 5 (by rfl) ⟨115823, by rfl⟩ : syracuseStep 2470901 = 231647) (by norm_num)
theorem B2503685 : Blo 1646022 2503685 := bbase (se 4 (by rfl) ⟨234720, by rfl⟩ : syracuseStep 2503685 = 469441) (by norm_num)
theorem B3707909 : Blo 1646022 3707909 := bbase (se 4 (by rfl) ⟨347616, by rfl⟩ : syracuseStep 3707909 = 695233) (by norm_num)
theorem B2470925 : Blo 1646022 2470925 := bbase (se 3 (by rfl) ⟨463298, by rfl⟩ : syracuseStep 2470925 = 926597) (by norm_num)
theorem B2225189 : Blo 1646022 2225189 := bbase (se 4 (by rfl) ⟨208611, by rfl⟩ : syracuseStep 2225189 = 417223) (by norm_num)
theorem B2470949 : Blo 1646022 2470949 := bbase (se 4 (by rfl) ⟨231651, by rfl⟩ : syracuseStep 2470949 = 463303) (by norm_num)
theorem B3519533 : Blo 1646022 3519533 := bbase (se 3 (by rfl) ⟨659912, by rfl⟩ : syracuseStep 3519533 = 1319825) (by norm_num)
theorem B1692725 : Blo 1646022 1692725 := bbase (se 5 (by rfl) ⟨79346, by rfl⟩ : syracuseStep 1692725 = 158693) (by norm_num)
theorem B2470973 : Blo 1646022 2470973 := bbase (se 3 (by rfl) ⟨463307, by rfl⟩ : syracuseStep 2470973 = 926615) (by norm_num)
theorem B2503757 : Blo 1646022 2503757 := bbase (se 3 (by rfl) ⟨469454, by rfl⟩ : syracuseStep 2503757 = 938909) (by norm_num)
theorem B3707981 : Blo 1646022 3707981 := bbase (se 3 (by rfl) ⟨695246, by rfl⟩ : syracuseStep 3707981 = 1390493) (by norm_num)
theorem B4166741 : Blo 1646022 4166741 := bbase (se 8 (by rfl) ⟨24414, by rfl⟩ : syracuseStep 4166741 = 48829) (by norm_num)
theorem B5936213 : Blo 1646022 5936213 := bbase (se 8 (by rfl) ⟨34782, by rfl⟩ : syracuseStep 5936213 = 69565) (by norm_num)
theorem B2470997 : Blo 1646022 2470997 := bbase (se 8 (by rfl) ⟨14478, by rfl⟩ : syracuseStep 2470997 = 28957) (by norm_num)
theorem B6255701 : Blo 1646022 6255701 := bbase (se 8 (by rfl) ⟨36654, by rfl⟩ : syracuseStep 6255701 = 73309) (by norm_num)
theorem B1979497 : Blo 1646022 1979497 := bbase (se 2 (by rfl) ⟨742311, by rfl⟩ : syracuseStep 1979497 = 1484623) (by norm_num)
theorem B2471021 : Blo 1646022 2471021 := bbase (se 3 (by rfl) ⟨463316, by rfl⟩ : syracuseStep 2471021 = 926633) (by norm_num)
theorem B2471045 : Blo 1646022 2471045 := bbase (se 4 (by rfl) ⟨231660, by rfl⟩ : syracuseStep 2471045 = 463321) (by norm_num)
theorem B2503829 : Blo 1646022 2503829 := bbase (se 6 (by rfl) ⟨58683, by rfl⟩ : syracuseStep 2503829 = 117367) (by norm_num)
theorem B2471069 : Blo 1646022 2471069 := bbase (se 3 (by rfl) ⟨463325, by rfl⟩ : syracuseStep 2471069 = 926651) (by norm_num)
theorem B5559461 : Blo 1646022 5559461 := bbase (se 4 (by rfl) ⟨521199, by rfl⟩ : syracuseStep 5559461 = 1042399) (by norm_num)
theorem B2471093 : Blo 1646022 2471093 := bbase (se 5 (by rfl) ⟨115832, by rfl⟩ : syracuseStep 2471093 = 231665) (by norm_num)
theorem B2471117 : Blo 1646022 2471117 := bbase (se 3 (by rfl) ⟨463334, by rfl⟩ : syracuseStep 2471117 = 926669) (by norm_num)
theorem B2471141 : Blo 1646022 2471141 := bbase (se 4 (by rfl) ⟨231669, by rfl⟩ : syracuseStep 2471141 = 463339) (by norm_num)
theorem B2225389 : Blo 1646022 2225389 := bbase (se 3 (by rfl) ⟨417260, by rfl⟩ : syracuseStep 2225389 = 834521) (by norm_num)
theorem B2471165 : Blo 1646022 2471165 := bbase (se 3 (by rfl) ⟨463343, by rfl⟩ : syracuseStep 2471165 = 926687) (by norm_num)
theorem B2471189 : Blo 1646022 2471189 := bbase (se 6 (by rfl) ⟨57918, by rfl⟩ : syracuseStep 2471189 = 115837) (by norm_num)
theorem B2225453 : Blo 1646022 2225453 := bbase (se 3 (by rfl) ⟨417272, by rfl⟩ : syracuseStep 2225453 = 834545) (by norm_num)
theorem B2471213 : Blo 1646022 2471213 := bbase (se 3 (by rfl) ⟨463352, by rfl⟩ : syracuseStep 2471213 = 926705) (by norm_num)
theorem B2471237 : Blo 1646022 2471237 := bbase (se 4 (by rfl) ⟨231678, by rfl⟩ : syracuseStep 2471237 = 463357) (by norm_num)
theorem B3126613 : Blo 1646022 3126613 := bbase (se 13 (by rfl) ⟨572, by rfl⟩ : syracuseStep 3126613 = 1145) (by norm_num)
theorem B33813845 : Blo 1646022 33813845 := bbase (se 13 (by rfl) ⟨6191, by rfl⟩ : syracuseStep 33813845 = 12383) (by norm_num)
theorem B1758553 : Blo 1646022 1758553 := bbase (se 2 (by rfl) ⟨659457, by rfl⟩ : syracuseStep 1758553 = 1318915) (by norm_num)
theorem B2471261 : Blo 1646022 2471261 := bbase (se 3 (by rfl) ⟨463361, by rfl⟩ : syracuseStep 2471261 = 926723) (by norm_num)
theorem B2471285 : Blo 1646022 2471285 := bbase (se 5 (by rfl) ⟨115841, by rfl⟩ : syracuseStep 2471285 = 231683) (by norm_num)
theorem B2471309 : Blo 1646022 2471309 := bbase (se 3 (by rfl) ⟨463370, by rfl⟩ : syracuseStep 2471309 = 926741) (by norm_num)
theorem B2471333 : Blo 1646022 2471333 := bbase (se 4 (by rfl) ⟨231687, by rfl⟩ : syracuseStep 2471333 = 463375) (by norm_num)
theorem B4167085 : Blo 1646022 4167085 := bbase (se 3 (by rfl) ⟨781328, by rfl⟩ : syracuseStep 4167085 = 1562657) (by norm_num)
theorem B2471357 : Blo 1646022 2471357 := bbase (se 3 (by rfl) ⟨463379, by rfl⟩ : syracuseStep 2471357 = 926759) (by norm_num)
theorem B1758673 : Blo 1646022 1758673 := bbase (se 2 (by rfl) ⟨659502, by rfl⟩ : syracuseStep 1758673 = 1319005) (by norm_num)
theorem B2471381 : Blo 1646022 2471381 := bbase (se 7 (by rfl) ⟨28961, by rfl⟩ : syracuseStep 2471381 = 57923) (by norm_num)
theorem B3126757 : Blo 1646022 3126757 := bbase (se 4 (by rfl) ⟨293133, by rfl⟩ : syracuseStep 3126757 = 586267) (by norm_num)
theorem B2471405 : Blo 1646022 2471405 := bbase (se 3 (by rfl) ⟨463388, by rfl⟩ : syracuseStep 2471405 = 926777) (by norm_num)
theorem B2471429 : Blo 1646022 2471429 := bbase (se 4 (by rfl) ⟨231696, by rfl⟩ : syracuseStep 2471429 = 463393) (by norm_num)
theorem B4167197 : Blo 1646022 4167197 := bbase (se 3 (by rfl) ⟨781349, by rfl⟩ : syracuseStep 4167197 = 1562699) (by norm_num)
theorem B2471453 : Blo 1646022 2471453 := bbase (se 3 (by rfl) ⟨463397, by rfl⟩ : syracuseStep 2471453 = 926795) (by norm_num)
theorem B2471477 : Blo 1646022 2471477 := bbase (se 5 (by rfl) ⟨115850, by rfl⟩ : syracuseStep 2471477 = 231701) (by norm_num)
theorem B2471501 : Blo 1646022 2471501 := bbase (se 3 (by rfl) ⟨463406, by rfl⟩ : syracuseStep 2471501 = 926813) (by norm_num)
theorem B5559893 : Blo 1646022 5559893 := bbase (se 8 (by rfl) ⟨32577, by rfl⟩ : syracuseStep 5559893 = 65155) (by norm_num)
theorem B2471525 : Blo 1646022 2471525 := bbase (se 4 (by rfl) ⟨231705, by rfl⟩ : syracuseStep 2471525 = 463411) (by norm_num)
theorem B7911029 : Blo 1646022 7911029 := bbase (se 5 (by rfl) ⟨370829, by rfl⟩ : syracuseStep 7911029 = 741659) (by norm_num)
theorem B2471549 : Blo 1646022 2471549 := bbase (se 3 (by rfl) ⟨463415, by rfl⟩ : syracuseStep 2471549 = 926831) (by norm_num)
theorem B3126917 : Blo 1646022 3126917 := bbase (se 4 (by rfl) ⟨293148, by rfl⟩ : syracuseStep 3126917 = 586297) (by norm_num)
theorem B2471573 : Blo 1646022 2471573 := bbase (se 6 (by rfl) ⟨57927, by rfl⟩ : syracuseStep 2471573 = 115855) (by norm_num)
theorem B2471597 : Blo 1646022 2471597 := bbase (se 3 (by rfl) ⟨463424, by rfl⟩ : syracuseStep 2471597 = 926849) (by norm_num)
theorem B2471621 : Blo 1646022 2471621 := bbase (se 4 (by rfl) ⟨231714, by rfl⟩ : syracuseStep 2471621 = 463429) (by norm_num)
theorem B1758925 : Blo 1646022 1758925 := bbase (se 3 (by rfl) ⟨329798, by rfl⟩ : syracuseStep 1758925 = 659597) (by norm_num)
theorem B1758929 : Blo 1646022 1758929 := bbase (se 2 (by rfl) ⟨659598, by rfl⟩ : syracuseStep 1758929 = 1319197) (by norm_num)
theorem B64149205 : Blo 1646022 64149205 := bbase (se 7 (by rfl) ⟨751748, by rfl⟩ : syracuseStep 64149205 = 1503497) (by norm_num)
theorem B4167389 : Blo 1646022 4167389 := bbase (se 3 (by rfl) ⟨781385, by rfl⟩ : syracuseStep 4167389 = 1562771) (by norm_num)
theorem B2471645 : Blo 1646022 2471645 := bbase (se 3 (by rfl) ⟨463433, by rfl⟩ : syracuseStep 2471645 = 926867) (by norm_num)
theorem B7919333 : Blo 1646022 7919333 := bbase (se 4 (by rfl) ⟨742437, by rfl⟩ : syracuseStep 7919333 = 1484875) (by norm_num)
theorem B2471669 : Blo 1646022 2471669 := bbase (se 5 (by rfl) ⟨115859, by rfl⟩ : syracuseStep 2471669 = 231719) (by norm_num)
theorem B2471693 : Blo 1646022 2471693 := bbase (se 3 (by rfl) ⟨463442, by rfl⟩ : syracuseStep 2471693 = 926885) (by norm_num)
theorem B3127061 : Blo 1646022 3127061 := bbase (se 6 (by rfl) ⟨73290, by rfl⟩ : syracuseStep 3127061 = 146581) (by norm_num)
theorem B3807005 : Blo 1646022 3807005 := bbase (se 3 (by rfl) ⟨713813, by rfl⟩ : syracuseStep 3807005 = 1427627) (by norm_num)
theorem B2471717 : Blo 1646022 2471717 := bbase (se 4 (by rfl) ⟨231723, by rfl⟩ : syracuseStep 2471717 = 463447) (by norm_num)
theorem B4011821 : Blo 1646022 4011821 := bbase (se 3 (by rfl) ⟨752216, by rfl⟩ : syracuseStep 4011821 = 1504433) (by norm_num)
theorem B2471741 : Blo 1646022 2471741 := bbase (se 3 (by rfl) ⟨463451, by rfl⟩ : syracuseStep 2471741 = 926903) (by norm_num)
theorem B2471765 : Blo 1646022 2471765 := bbase (se 9 (by rfl) ⟨7241, by rfl⟩ : syracuseStep 2471765 = 14483) (by norm_num)
theorem B2471789 : Blo 1646022 2471789 := bbase (se 3 (by rfl) ⟨463460, by rfl⟩ : syracuseStep 2471789 = 926921) (by norm_num)
theorem B4011893 : Blo 1646022 4011893 := bbase (se 5 (by rfl) ⟨188057, by rfl⟩ : syracuseStep 4011893 = 376115) (by norm_num)
theorem B4511621 : Blo 1646022 4511621 := bbase (se 4 (by rfl) ⟨422964, by rfl⟩ : syracuseStep 4511621 = 845929) (by norm_num)
theorem B2471813 : Blo 1646022 2471813 := bbase (se 4 (by rfl) ⟨231732, by rfl⟩ : syracuseStep 2471813 = 463465) (by norm_num)
theorem B9508757 : Blo 1646022 9508757 := bbase (se 6 (by rfl) ⟨222861, by rfl⟩ : syracuseStep 9508757 = 445723) (by norm_num)
theorem B2471837 : Blo 1646022 2471837 := bbase (se 3 (by rfl) ⟨463469, by rfl⟩ : syracuseStep 2471837 = 926939) (by norm_num)
theorem B2471861 : Blo 1646022 2471861 := bbase (se 5 (by rfl) ⟨115868, by rfl⟩ : syracuseStep 2471861 = 231737) (by norm_num)
theorem B2471885 : Blo 1646022 2471885 := bbase (se 3 (by rfl) ⟨463478, by rfl⟩ : syracuseStep 2471885 = 926957) (by norm_num)
theorem B2471909 : Blo 1646022 2471909 := bbase (se 4 (by rfl) ⟨231741, by rfl⟩ : syracuseStep 2471909 = 463483) (by norm_num)
theorem B2471933 : Blo 1646022 2471933 := bbase (se 3 (by rfl) ⟨463487, by rfl⟩ : syracuseStep 2471933 = 926975) (by norm_num)
theorem B5560325 : Blo 1646022 5560325 := bbase (se 4 (by rfl) ⟨521280, by rfl⟩ : syracuseStep 5560325 = 1042561) (by norm_num)
theorem B2471957 : Blo 1646022 2471957 := bbase (se 6 (by rfl) ⟨57936, by rfl⟩ : syracuseStep 2471957 = 115873) (by norm_num)
theorem B2471981 : Blo 1646022 2471981 := bbase (se 3 (by rfl) ⟨463496, by rfl⟩ : syracuseStep 2471981 = 926993) (by norm_num)
theorem B4167733 : Blo 1646022 4167733 := bbase (se 5 (by rfl) ⟨195362, by rfl⟩ : syracuseStep 4167733 = 390725) (by norm_num)
theorem B3127349 : Blo 1646022 3127349 := bbase (se 5 (by rfl) ⟨146594, by rfl⟩ : syracuseStep 3127349 = 293189) (by norm_num)
theorem B4454453 : Blo 1646022 4454453 := bbase (se 5 (by rfl) ⟨208802, by rfl⟩ : syracuseStep 4454453 = 417605) (by norm_num)
theorem B2472005 : Blo 1646022 2472005 := bbase (se 4 (by rfl) ⟨231750, by rfl⟩ : syracuseStep 2472005 = 463501) (by norm_num)
theorem B2472029 : Blo 1646022 2472029 := bbase (se 3 (by rfl) ⟨463505, by rfl⟩ : syracuseStep 2472029 = 927011) (by norm_num)
theorem B4167845 : Blo 1646022 4167845 := bbase (se 4 (by rfl) ⟨390735, by rfl⟩ : syracuseStep 4167845 = 781471) (by norm_num)
theorem B1669285 : Blo 1646022 1669285 := bbase (se 4 (by rfl) ⟨156495, by rfl⟩ : syracuseStep 1669285 = 312991) (by norm_num)
theorem B3127501 : Blo 1646022 3127501 := bbase (se 3 (by rfl) ⟨586406, by rfl⟩ : syracuseStep 3127501 = 1172813) (by norm_num)
theorem B3299557 : Blo 1646022 3299557 := bbase (se 4 (by rfl) ⟨309333, by rfl⟩ : syracuseStep 3299557 = 618667) (by norm_num)
theorem B8337653 : Blo 1646022 8337653 := bbase (se 5 (by rfl) ⟨390827, by rfl⟩ : syracuseStep 8337653 = 781655) (by norm_num)
theorem B6256885 : Blo 1646022 6256885 := bbase (se 5 (by rfl) ⟨293291, by rfl⟩ : syracuseStep 6256885 = 586583) (by norm_num)
theorem B1759493 : Blo 1646022 1759493 := bbase (se 4 (by rfl) ⟨164952, by rfl⟩ : syracuseStep 1759493 = 329905) (by norm_num)
theorem B4168037 : Blo 1646022 4168037 := bbase (se 4 (by rfl) ⟨390753, by rfl⟩ : syracuseStep 4168037 = 781507) (by norm_num)
theorem B5560757 : Blo 1646022 5560757 := bbase (se 5 (by rfl) ⟨260660, by rfl⟩ : syracuseStep 5560757 = 521321) (by norm_num)
theorem B1759681 : Blo 1646022 1759681 := bbase (se 2 (by rfl) ⟨659880, by rfl⟩ : syracuseStep 1759681 = 1319761) (by norm_num)
theorem B28137941 : Blo 1646022 28137941 := bbase (se 7 (by rfl) ⟨329741, by rfl⟩ : syracuseStep 28137941 = 659483) (by norm_num)
theorem B4692437 : Blo 1646022 4692437 := bbase (se 7 (by rfl) ⟨54989, by rfl⟩ : syracuseStep 4692437 = 109979) (by norm_num)
theorem B3127805 : Blo 1646022 3127805 := bbase (se 3 (by rfl) ⟨586463, by rfl⟩ : syracuseStep 3127805 = 1172927) (by norm_num)
theorem B6257189 : Blo 1646022 6257189 := bbase (se 4 (by rfl) ⟨586611, by rfl⟩ : syracuseStep 6257189 = 1173223) (by norm_num)
theorem B4225645 : Blo 1646022 4225645 := bbase (se 3 (by rfl) ⟨792308, by rfl⟩ : syracuseStep 4225645 = 1584617) (by norm_num)
theorem B4168381 : Blo 1646022 4168381 := bbase (se 3 (by rfl) ⟨781571, by rfl⟩ : syracuseStep 4168381 = 1563143) (by norm_num)
theorem B3955429 : Blo 1646022 3955429 := bbase (se 4 (by rfl) ⟨370821, by rfl⟩ : syracuseStep 3955429 = 741643) (by norm_num)
theorem B1669901 : Blo 1646022 1669901 := bbase (se 3 (by rfl) ⟨313106, by rfl⟩ : syracuseStep 1669901 = 626213) (by norm_num)
theorem B5077781 : Blo 1646022 5077781 := bbase (se 6 (by rfl) ⟨119010, by rfl⟩ : syracuseStep 5077781 = 238021) (by norm_num)
theorem B4168493 : Blo 1646022 4168493 := bbase (se 3 (by rfl) ⟨781592, by rfl⟩ : syracuseStep 4168493 = 1563185) (by norm_num)
theorem B4225861 : Blo 1646022 4225861 := bbase (se 4 (by rfl) ⟨396174, by rfl⟩ : syracuseStep 4225861 = 792349) (by norm_num)
theorem B5561189 : Blo 1646022 5561189 := bbase (se 4 (by rfl) ⟨521361, by rfl⟩ : syracuseStep 5561189 = 1042723) (by norm_num)
theorem B3955661 : Blo 1646022 3955661 := bbase (se 3 (by rfl) ⟨741686, by rfl⟩ : syracuseStep 3955661 = 1483373) (by norm_num)
theorem B4168685 : Blo 1646022 4168685 := bbase (se 3 (by rfl) ⟨781628, by rfl⟩ : syracuseStep 4168685 = 1563257) (by norm_num)
theorem B4512773 : Blo 1646022 4512773 := bbase (se 4 (by rfl) ⟨423072, by rfl⟩ : syracuseStep 4512773 = 846145) (by norm_num)
theorem B12508181 : Blo 1646022 12508181 := bbase (se 6 (by rfl) ⟨293160, by rfl⟩ : syracuseStep 12508181 = 586321) (by norm_num)
theorem B2636869 : Blo 1646022 2636869 := bbase (se 4 (by rfl) ⟨247206, by rfl⟩ : syracuseStep 2636869 = 494413) (by norm_num)
theorem B1670225 : Blo 1646022 1670225 := bbase (se 2 (by rfl) ⟨626334, by rfl⟩ : syracuseStep 1670225 = 1252669) (by norm_num)
theorem B7511237 : Blo 1646022 7511237 := bbase (se 4 (by rfl) ⟨704178, by rfl⟩ : syracuseStep 7511237 = 1408357) (by norm_num)
theorem B3128557 : Blo 1646022 3128557 := bbase (se 3 (by rfl) ⟨586604, by rfl⟩ : syracuseStep 3128557 = 1173209) (by norm_num)
theorem B5561621 : Blo 1646022 5561621 := bbase (se 6 (by rfl) ⟨130350, by rfl⟩ : syracuseStep 5561621 = 260701) (by norm_num)
theorem B4169029 : Blo 1646022 4169029 := bbase (se 4 (by rfl) ⟨390846, by rfl⟩ : syracuseStep 4169029 = 781693) (by norm_num)
theorem B3956053 : Blo 1646022 3956053 := bbase (se 11 (by rfl) ⟨2897, by rfl⟩ : syracuseStep 3956053 = 5795) (by norm_num)
theorem B2006417 : Blo 1646022 2006417 := bbase (se 2 (by rfl) ⟨752406, by rfl⟩ : syracuseStep 2006417 = 1504813) (by norm_num)
theorem B12500405 : Blo 1646022 12500405 := bbase (se 5 (by rfl) ⟨585956, by rfl⟩ : syracuseStep 12500405 = 1171913) (by norm_num)
theorem B4169141 : Blo 1646022 4169141 := bbase (se 5 (by rfl) ⟨195428, by rfl⟩ : syracuseStep 4169141 = 390857) (by norm_num)
theorem B2637317 : Blo 1646022 2637317 := bbase (se 4 (by rfl) ⟨247248, by rfl⟩ : syracuseStep 2637317 = 494497) (by norm_num)
theorem B8338949 : Blo 1646022 8338949 := bbase (se 4 (by rfl) ⟨781776, by rfl⟩ : syracuseStep 8338949 = 1563553) (by norm_num)
theorem B7036469 : Blo 1646022 7036469 := bbase (se 5 (by rfl) ⟨329834, by rfl⟩ : syracuseStep 7036469 = 659669) (by norm_num)
theorem B4169333 : Blo 1646022 4169333 := bbase (se 5 (by rfl) ⟨195437, by rfl⟩ : syracuseStep 4169333 = 390875) (by norm_num)
theorem B5562053 : Blo 1646022 5562053 := bbase (se 4 (by rfl) ⟨521442, by rfl⟩ : syracuseStep 5562053 = 1042885) (by norm_num)
theorem B2637517 : Blo 1646022 2637517 := bbase (se 3 (by rfl) ⟨494534, by rfl⟩ : syracuseStep 2637517 = 989069) (by norm_num)
theorem B4226845 : Blo 1646022 4226845 := bbase (se 3 (by rfl) ⟨792533, by rfl⟩ : syracuseStep 4226845 = 1585067) (by norm_num)
theorem B2637773 : Blo 1646022 2637773 := bbase (se 3 (by rfl) ⟨494582, by rfl⟩ : syracuseStep 2637773 = 989165) (by norm_num)
theorem B4169677 : Blo 1646022 4169677 := bbase (se 3 (by rfl) ⟨781814, by rfl⟩ : syracuseStep 4169677 = 1563629) (by norm_num)
theorem B1646595 : Blo 1646022 1646595 := bstep (se 1 (by rfl) ⟨1234946, by rfl⟩ : syracuseStep 1646595 = 2469893) B2469893
theorem B1646611 : Blo 1646022 1646611 := bstep (se 1 (by rfl) ⟨1234958, by rfl⟩ : syracuseStep 1646611 = 2469917) B2469917
theorem B1646627 : Blo 1646022 1646627 := bstep (se 1 (by rfl) ⟨1234970, by rfl⟩ : syracuseStep 1646627 = 2469941) B2469941
theorem B1646643 : Blo 1646022 1646643 := bstep (se 1 (by rfl) ⟨1234982, by rfl⟩ : syracuseStep 1646643 = 2469965) B2469965
theorem B1646659 : Blo 1646022 1646659 := bstep (se 1 (by rfl) ⟨1234994, by rfl⟩ : syracuseStep 1646659 = 2469989) B2469989
theorem B1646675 : Blo 1646022 1646675 := bstep (se 1 (by rfl) ⟨1235006, by rfl⟩ : syracuseStep 1646675 = 2470013) B2470013
theorem B1646691 : Blo 1646022 1646691 := bstep (se 1 (by rfl) ⟨1235018, by rfl⟩ : syracuseStep 1646691 = 2470037) B2470037
theorem B1646707 : Blo 1646022 1646707 := bstep (se 1 (by rfl) ⟨1235030, by rfl⟩ : syracuseStep 1646707 = 2470061) B2470061
theorem B1646723 : Blo 1646022 1646723 := bstep (se 1 (by rfl) ⟨1235042, by rfl⟩ : syracuseStep 1646723 = 2470085) B2470085
theorem B8339597 : Blo 1646022 8339597 := bstep (se 3 (by rfl) ⟨1563674, by rfl⟩ : syracuseStep 8339597 = 3127349) B3127349
theorem B4513933 : Blo 1646022 4513933 := bstep (se 3 (by rfl) ⟨846362, by rfl⟩ : syracuseStep 4513933 = 1692725) B1692725
theorem B1646739 : Blo 1646022 1646739 := bstep (se 1 (by rfl) ⟨1235054, by rfl⟩ : syracuseStep 1646739 = 2470109) B2470109
theorem B1646755 : Blo 1646022 1646755 := bstep (se 1 (by rfl) ⟨1235066, by rfl⟩ : syracuseStep 1646755 = 2470133) B2470133
theorem B1646771 : Blo 1646022 1646771 := bstep (se 1 (by rfl) ⟨1235078, by rfl⟩ : syracuseStep 1646771 = 2470157) B2470157
theorem B2113715 : Blo 1646022 2113715 := bstep (se 1 (by rfl) ⟨1585286, by rfl⟩ : syracuseStep 2113715 = 3170573) B3170573
theorem B1646787 : Blo 1646022 1646787 := bstep (se 1 (by rfl) ⟨1235090, by rfl⟩ : syracuseStep 1646787 = 2470181) B2470181
theorem B1646803 : Blo 1646022 1646803 := bstep (se 1 (by rfl) ⟨1235102, by rfl⟩ : syracuseStep 1646803 = 2470205) B2470205
theorem B57016547 : Blo 1646022 57016547 := bstep (se 1 (by rfl) ⟨42762410, by rfl⟩ : syracuseStep 57016547 = 85524821) B85524821
theorem B1646819 : Blo 1646022 1646819 := bstep (se 1 (by rfl) ⟨1235114, by rfl⟩ : syracuseStep 1646819 = 2470229) B2470229
theorem B1646835 : Blo 1646022 1646835 := bstep (se 1 (by rfl) ⟨1235126, by rfl⟩ : syracuseStep 1646835 = 2470253) B2470253
theorem B1646851 : Blo 1646022 1646851 := bstep (se 1 (by rfl) ⟨1235138, by rfl⟩ : syracuseStep 1646851 = 2470277) B2470277
theorem B4170001 : Blo 1646022 4170001 := bstep (se 2 (by rfl) ⟨1563750, by rfl⟩ : syracuseStep 4170001 = 3127501) B3127501
theorem B1646867 : Blo 1646022 1646867 := bstep (se 1 (by rfl) ⟨1235150, by rfl⟩ : syracuseStep 1646867 = 2470301) B2470301
theorem B2638099 : Blo 1646022 2638099 := bstep (se 1 (by rfl) ⟨1978574, by rfl⟩ : syracuseStep 2638099 = 3957149) B3957149
theorem B1646883 : Blo 1646022 1646883 := bstep (se 1 (by rfl) ⟨1235162, by rfl⟩ : syracuseStep 1646883 = 2470325) B2470325
theorem B7037219 : Blo 1646022 7037219 := bstep (se 1 (by rfl) ⟨5277914, by rfl⟩ : syracuseStep 7037219 = 10555829) B10555829
theorem B4399409 : Blo 1646022 4399409 := bstep (se 2 (by rfl) ⟨1649778, by rfl⟩ : syracuseStep 4399409 = 3299557) B3299557
theorem B1646899 : Blo 1646022 1646899 := bstep (se 1 (by rfl) ⟨1235174, by rfl⟩ : syracuseStep 1646899 = 2470349) B2470349
theorem B1646915 : Blo 1646022 1646915 := bstep (se 1 (by rfl) ⟨1235186, by rfl⟩ : syracuseStep 1646915 = 2470373) B2470373
theorem B1646931 : Blo 1646022 1646931 := bstep (se 1 (by rfl) ⟨1235198, by rfl⟩ : syracuseStep 1646931 = 2470397) B2470397
theorem B1646947 : Blo 1646022 1646947 := bstep (se 1 (by rfl) ⟨1235210, by rfl⟩ : syracuseStep 1646947 = 2470421) B2470421
theorem B5636465 : Blo 1646022 5636465 := bstep (se 2 (by rfl) ⟨2113674, by rfl⟩ : syracuseStep 5636465 = 4227349) B4227349
theorem B1646963 : Blo 1646022 1646963 := bstep (se 1 (by rfl) ⟨1235222, by rfl⟩ : syracuseStep 1646963 = 2470445) B2470445
theorem B1646979 : Blo 1646022 1646979 := bstep (se 1 (by rfl) ⟨1235234, by rfl⟩ : syracuseStep 1646979 = 2470469) B2470469
theorem B6676877 : Blo 1646022 6676877 := bstep (se 3 (by rfl) ⟨1251914, by rfl⟩ : syracuseStep 6676877 = 2503829) B2503829
theorem B1646995 : Blo 1646022 1646995 := bstep (se 1 (by rfl) ⟨1235246, by rfl⟩ : syracuseStep 1646995 = 2470493) B2470493
theorem B1647011 : Blo 1646022 1647011 := bstep (se 1 (by rfl) ⟨1235258, by rfl⟩ : syracuseStep 1647011 = 2470517) B2470517
theorem B1647027 : Blo 1646022 1647027 := bstep (se 1 (by rfl) ⟨1235270, by rfl⟩ : syracuseStep 1647027 = 2470541) B2470541
theorem B5005763 : Blo 1646022 5005763 := bstep (se 1 (by rfl) ⟨3754322, by rfl⟩ : syracuseStep 5005763 = 7508645) B7508645
theorem B1647043 : Blo 1646022 1647043 := bstep (se 1 (by rfl) ⟨1235282, by rfl⟩ : syracuseStep 1647043 = 2470565) B2470565
theorem B7913933 : Blo 1646022 7913933 := bstep (se 3 (by rfl) ⟨1483862, by rfl⟩ : syracuseStep 7913933 = 2967725) B2967725
theorem B1647059 : Blo 1646022 1647059 := bstep (se 1 (by rfl) ⟨1235294, by rfl⟩ : syracuseStep 1647059 = 2470589) B2470589
theorem B1647075 : Blo 1646022 1647075 := bstep (se 1 (by rfl) ⟨1235306, by rfl⟩ : syracuseStep 1647075 = 2470613) B2470613
theorem B1647091 : Blo 1646022 1647091 := bstep (se 1 (by rfl) ⟨1235318, by rfl⟩ : syracuseStep 1647091 = 2470637) B2470637
theorem B1851907 : Blo 1646022 1851907 := bstep (se 1 (by rfl) ⟨1388930, by rfl⟩ : syracuseStep 1851907 = 2777861) B2777861
theorem B1647107 : Blo 1646022 1647107 := bstep (se 1 (by rfl) ⟨1235330, by rfl⟩ : syracuseStep 1647107 = 2470661) B2470661
theorem B1647123 : Blo 1646022 1647123 := bstep (se 1 (by rfl) ⟨1235342, by rfl⟩ : syracuseStep 1647123 = 2470685) B2470685
theorem B3957283 : Blo 1646022 3957283 := bstep (se 1 (by rfl) ⟨2967962, by rfl⟩ : syracuseStep 3957283 = 5935925) B5935925
theorem B1647139 : Blo 1646022 1647139 := bstep (se 1 (by rfl) ⟨1235354, by rfl⟩ : syracuseStep 1647139 = 2470709) B2470709
theorem B4170275 : Blo 1646022 4170275 := bstep (se 1 (by rfl) ⟨3127706, by rfl⟩ : syracuseStep 4170275 = 6255413) B6255413
theorem B1647155 : Blo 1646022 1647155 := bstep (se 1 (by rfl) ⟨1235366, by rfl⟩ : syracuseStep 1647155 = 2470733) B2470733
theorem B2777665 : Blo 1646022 2777665 := bstep (se 2 (by rfl) ⟨1041624, by rfl⟩ : syracuseStep 2777665 = 2083249) B2083249
theorem B1647171 : Blo 1646022 1647171 := bstep (se 1 (by rfl) ⟨1235378, by rfl⟩ : syracuseStep 1647171 = 2470757) B2470757
theorem B1647187 : Blo 1646022 1647187 := bstep (se 1 (by rfl) ⟨1235390, by rfl⟩ : syracuseStep 1647187 = 2470781) B2470781
theorem B2777699 : Blo 1646022 2777699 := bstep (se 1 (by rfl) ⟨2083274, by rfl⟩ : syracuseStep 2777699 = 4166549) B4166549
theorem B1647203 : Blo 1646022 1647203 := bstep (se 1 (by rfl) ⟨1235402, by rfl⟩ : syracuseStep 1647203 = 2470805) B2470805
theorem B1647219 : Blo 1646022 1647219 := bstep (se 1 (by rfl) ⟨1235414, by rfl⟩ : syracuseStep 1647219 = 2470829) B2470829
theorem B1647235 : Blo 1646022 1647235 := bstep (se 1 (by rfl) ⟨1235426, by rfl⟩ : syracuseStep 1647235 = 2470853) B2470853
theorem B1852051 : Blo 1646022 1852051 := bstep (se 1 (by rfl) ⟨1389038, by rfl⟩ : syracuseStep 1852051 = 2778077) B2778077
theorem B1647251 : Blo 1646022 1647251 := bstep (se 1 (by rfl) ⟨1235438, by rfl⟩ : syracuseStep 1647251 = 2470877) B2470877
theorem B1647267 : Blo 1646022 1647267 := bstep (se 1 (by rfl) ⟨1235450, by rfl⟩ : syracuseStep 1647267 = 2470901) B2470901
theorem B1647283 : Blo 1646022 1647283 := bstep (se 1 (by rfl) ⟨1235462, by rfl⟩ : syracuseStep 1647283 = 2470925) B2470925
theorem B1647299 : Blo 1646022 1647299 := bstep (se 1 (by rfl) ⟨1235474, by rfl⟩ : syracuseStep 1647299 = 2470949) B2470949
theorem B3957457 : Blo 1646022 3957457 := bstep (se 2 (by rfl) ⟨1484046, by rfl⟩ : syracuseStep 3957457 = 2968093) B2968093
theorem B1647315 : Blo 1646022 1647315 := bstep (se 1 (by rfl) ⟨1235486, by rfl⟩ : syracuseStep 1647315 = 2470973) B2470973
theorem B2777827 : Blo 1646022 2777827 := bstep (se 1 (by rfl) ⟨2083370, by rfl⟩ : syracuseStep 2777827 = 4166741) B4166741
theorem B1647331 : Blo 1646022 1647331 := bstep (se 1 (by rfl) ⟨1235498, by rfl⟩ : syracuseStep 1647331 = 2470997) B2470997
theorem B4170467 : Blo 1646022 4170467 := bstep (se 1 (by rfl) ⟨3127850, by rfl⟩ : syracuseStep 4170467 = 6255701) B6255701
theorem B2343667 : Blo 1646022 2343667 := bstep (se 1 (by rfl) ⟨1757750, by rfl⟩ : syracuseStep 2343667 = 3515501) B3515501
theorem B1647347 : Blo 1646022 1647347 := bstep (se 1 (by rfl) ⟨1235510, by rfl⟩ : syracuseStep 1647347 = 2471021) B2471021
theorem B1647363 : Blo 1646022 1647363 := bstep (se 1 (by rfl) ⟨1235522, by rfl⟩ : syracuseStep 1647363 = 2471045) B2471045
theorem B1647379 : Blo 1646022 1647379 := bstep (se 1 (by rfl) ⟨1235534, by rfl⟩ : syracuseStep 1647379 = 2471069) B2471069
theorem B1852195 : Blo 1646022 1852195 := bstep (se 1 (by rfl) ⟨1389146, by rfl⟩ : syracuseStep 1852195 = 2778293) B2778293
theorem B1647395 : Blo 1646022 1647395 := bstep (se 1 (by rfl) ⟨1235546, by rfl⟩ : syracuseStep 1647395 = 2471093) B2471093
theorem B1647411 : Blo 1646022 1647411 := bstep (se 1 (by rfl) ⟨1235558, by rfl⟩ : syracuseStep 1647411 = 2471117) B2471117
theorem B1647427 : Blo 1646022 1647427 := bstep (se 1 (by rfl) ⟨1235570, by rfl⟩ : syracuseStep 1647427 = 2471141) B2471141
theorem B1647443 : Blo 1646022 1647443 := bstep (se 1 (by rfl) ⟨1235582, by rfl⟩ : syracuseStep 1647443 = 2471165) B2471165
theorem B1647459 : Blo 1646022 1647459 := bstep (se 1 (by rfl) ⟨1235594, by rfl⟩ : syracuseStep 1647459 = 2471189) B2471189
theorem B2777969 : Blo 1646022 2777969 := bstep (se 2 (by rfl) ⟨1041738, by rfl⟩ : syracuseStep 2777969 = 2083477) B2083477
theorem B1647475 : Blo 1646022 1647475 := bstep (se 1 (by rfl) ⟨1235606, by rfl⟩ : syracuseStep 1647475 = 2471213) B2471213
theorem B1647491 : Blo 1646022 1647491 := bstep (se 1 (by rfl) ⟨1235618, by rfl⟩ : syracuseStep 1647491 = 2471237) B2471237
theorem B3703697 : Blo 1646022 3703697 := bstep (se 2 (by rfl) ⟨1388886, by rfl⟩ : syracuseStep 3703697 = 2777773) B2777773
theorem B1647507 : Blo 1646022 1647507 := bstep (se 1 (by rfl) ⟨1235630, by rfl⟩ : syracuseStep 1647507 = 2471261) B2471261
theorem B3703715 : Blo 1646022 3703715 := bstep (se 1 (by rfl) ⟨2777786, by rfl⟩ : syracuseStep 3703715 = 5555573) B5555573
theorem B1647523 : Blo 1646022 1647523 := bstep (se 1 (by rfl) ⟨1235642, by rfl⟩ : syracuseStep 1647523 = 2471285) B2471285
theorem B1852339 : Blo 1646022 1852339 := bstep (se 1 (by rfl) ⟨1389254, by rfl⟩ : syracuseStep 1852339 = 2778509) B2778509
theorem B1647539 : Blo 1646022 1647539 := bstep (se 1 (by rfl) ⟨1235654, by rfl⟩ : syracuseStep 1647539 = 2471309) B2471309
theorem B1647555 : Blo 1646022 1647555 := bstep (se 1 (by rfl) ⟨1235666, by rfl⟩ : syracuseStep 1647555 = 2471333) B2471333
theorem B1647571 : Blo 1646022 1647571 := bstep (se 1 (by rfl) ⟨1235678, by rfl⟩ : syracuseStep 1647571 = 2471357) B2471357
theorem B1647587 : Blo 1646022 1647587 := bstep (se 1 (by rfl) ⟨1235690, by rfl⟩ : syracuseStep 1647587 = 2471381) B2471381
theorem B2778097 : Blo 1646022 2778097 := bstep (se 2 (by rfl) ⟨1041786, by rfl⟩ : syracuseStep 2778097 = 2083573) B2083573
theorem B1647603 : Blo 1646022 1647603 := bstep (se 1 (by rfl) ⟨1235702, by rfl⟩ : syracuseStep 1647603 = 2471405) B2471405
theorem B1647619 : Blo 1646022 1647619 := bstep (se 1 (by rfl) ⟨1235714, by rfl⟩ : syracuseStep 1647619 = 2471429) B2471429
theorem B2778131 : Blo 1646022 2778131 := bstep (se 1 (by rfl) ⟨2083598, by rfl⟩ : syracuseStep 2778131 = 4167197) B4167197
theorem B1647635 : Blo 1646022 1647635 := bstep (se 1 (by rfl) ⟨1235726, by rfl⟩ : syracuseStep 1647635 = 2471453) B2471453
theorem B1647651 : Blo 1646022 1647651 := bstep (se 1 (by rfl) ⟨1235738, by rfl⟩ : syracuseStep 1647651 = 2471477) B2471477
theorem B5350445 : Blo 1646022 5350445 := bstep (se 3 (by rfl) ⟨1003208, by rfl⟩ : syracuseStep 5350445 = 2006417) B2006417
theorem B1647667 : Blo 1646022 1647667 := bstep (se 1 (by rfl) ⟨1235750, by rfl⟩ : syracuseStep 1647667 = 2471501) B2471501
theorem B1852483 : Blo 1646022 1852483 := bstep (se 1 (by rfl) ⟨1389362, by rfl⟩ : syracuseStep 1852483 = 2778725) B2778725
theorem B1647683 : Blo 1646022 1647683 := bstep (se 1 (by rfl) ⟨1235762, by rfl⟩ : syracuseStep 1647683 = 2471525) B2471525
theorem B9380933 : Blo 1646022 9380933 := bstep (se 4 (by rfl) ⟨879462, by rfl⟩ : syracuseStep 9380933 = 1758925) B1758925
theorem B1647699 : Blo 1646022 1647699 := bstep (se 1 (by rfl) ⟨1235774, by rfl⟩ : syracuseStep 1647699 = 2471549) B2471549
theorem B1647715 : Blo 1646022 1647715 := bstep (se 1 (by rfl) ⟨1235786, by rfl⟩ : syracuseStep 1647715 = 2471573) B2471573
theorem B1647731 : Blo 1646022 1647731 := bstep (se 1 (by rfl) ⟨1235798, by rfl⟩ : syracuseStep 1647731 = 2471597) B2471597
theorem B1647747 : Blo 1646022 1647747 := bstep (se 1 (by rfl) ⟨1235810, by rfl⟩ : syracuseStep 1647747 = 2471621) B2471621
theorem B2778259 : Blo 1646022 2778259 := bstep (se 1 (by rfl) ⟨2083694, by rfl⟩ : syracuseStep 2778259 = 4167389) B4167389
theorem B1647763 : Blo 1646022 1647763 := bstep (se 1 (by rfl) ⟨1235822, by rfl⟩ : syracuseStep 1647763 = 2471645) B2471645
theorem B2639009 : Blo 1646022 2639009 := bstep (se 2 (by rfl) ⟨989628, by rfl⟩ : syracuseStep 2639009 = 1979257) B1979257
theorem B1647779 : Blo 1646022 1647779 := bstep (se 1 (by rfl) ⟨1235834, by rfl⟩ : syracuseStep 1647779 = 2471669) B2471669
theorem B3703985 : Blo 1646022 3703985 := bstep (se 2 (by rfl) ⟨1388994, by rfl⟩ : syracuseStep 3703985 = 2777989) B2777989
theorem B1647795 : Blo 1646022 1647795 := bstep (se 1 (by rfl) ⟨1235846, by rfl⟩ : syracuseStep 1647795 = 2471693) B2471693
theorem B3704003 : Blo 1646022 3704003 := bstep (se 1 (by rfl) ⟨2778002, by rfl⟩ : syracuseStep 3704003 = 5556005) B5556005
theorem B2966723 : Blo 1646022 2966723 := bstep (se 1 (by rfl) ⟨2225042, by rfl⟩ : syracuseStep 2966723 = 4450085) B4450085
theorem B1647811 : Blo 1646022 1647811 := bstep (se 1 (by rfl) ⟨1235858, by rfl⟩ : syracuseStep 1647811 = 2471717) B2471717
theorem B2344145 : Blo 1646022 2344145 := bstep (se 2 (by rfl) ⟨879054, by rfl⟩ : syracuseStep 2344145 = 1758109) B1758109
theorem B1852627 : Blo 1646022 1852627 := bstep (se 1 (by rfl) ⟨1389470, by rfl⟩ : syracuseStep 1852627 = 2778941) B2778941
theorem B1647827 : Blo 1646022 1647827 := bstep (se 1 (by rfl) ⟨1235870, by rfl⟩ : syracuseStep 1647827 = 2471741) B2471741
theorem B1647843 : Blo 1646022 1647843 := bstep (se 1 (by rfl) ⟨1235882, by rfl⟩ : syracuseStep 1647843 = 2471765) B2471765
theorem B15828209 : Blo 1646022 15828209 := bstep (se 2 (by rfl) ⟨5935578, by rfl⟩ : syracuseStep 15828209 = 11871157) B11871157
theorem B1647859 : Blo 1646022 1647859 := bstep (se 1 (by rfl) ⟨1235894, by rfl⟩ : syracuseStep 1647859 = 2471789) B2471789
theorem B1647875 : Blo 1646022 1647875 := bstep (se 1 (by rfl) ⟨1235906, by rfl⟩ : syracuseStep 1647875 = 2471813) B2471813
theorem B4228355 : Blo 1646022 4228355 := bstep (se 1 (by rfl) ⟨3171266, by rfl⟩ : syracuseStep 4228355 = 6342533) B6342533
theorem B1647891 : Blo 1646022 1647891 := bstep (se 1 (by rfl) ⟨1235918, by rfl⟩ : syracuseStep 1647891 = 2471837) B2471837
theorem B2778401 : Blo 1646022 2778401 := bstep (se 2 (by rfl) ⟨1041900, by rfl⟩ : syracuseStep 2778401 = 2083801) B2083801
theorem B2639137 : Blo 1646022 2639137 := bstep (se 2 (by rfl) ⟨989676, by rfl⟩ : syracuseStep 2639137 = 1979353) B1979353
theorem B1647907 : Blo 1646022 1647907 := bstep (se 1 (by rfl) ⟨1235930, by rfl⟩ : syracuseStep 1647907 = 2471861) B2471861
theorem B1647923 : Blo 1646022 1647923 := bstep (se 1 (by rfl) ⟨1235942, by rfl⟩ : syracuseStep 1647923 = 2471885) B2471885
theorem B2344259 : Blo 1646022 2344259 := bstep (se 1 (by rfl) ⟨1758194, by rfl⟩ : syracuseStep 2344259 = 3516389) B3516389
theorem B1647939 : Blo 1646022 1647939 := bstep (se 1 (by rfl) ⟨1235954, by rfl⟩ : syracuseStep 1647939 = 2471909) B2471909
theorem B1647955 : Blo 1646022 1647955 := bstep (se 1 (by rfl) ⟨1235966, by rfl⟩ : syracuseStep 1647955 = 2471933) B2471933
theorem B1852771 : Blo 1646022 1852771 := bstep (se 1 (by rfl) ⟨1389578, by rfl⟩ : syracuseStep 1852771 = 2779157) B2779157
theorem B1647971 : Blo 1646022 1647971 := bstep (se 1 (by rfl) ⟨1235978, by rfl⟩ : syracuseStep 1647971 = 2471957) B2471957
theorem B1647987 : Blo 1646022 1647987 := bstep (se 1 (by rfl) ⟨1235990, by rfl⟩ : syracuseStep 1647987 = 2471981) B2471981
theorem B1648003 : Blo 1646022 1648003 := bstep (se 1 (by rfl) ⟨1236002, by rfl⟩ : syracuseStep 1648003 = 2472005) B2472005
theorem B2344339 : Blo 1646022 2344339 := bstep (se 1 (by rfl) ⟨1758254, by rfl⟩ : syracuseStep 2344339 = 3516509) B3516509
theorem B1648019 : Blo 1646022 1648019 := bstep (se 1 (by rfl) ⟨1236014, by rfl⟩ : syracuseStep 1648019 = 2472029) B2472029
theorem B2778529 : Blo 1646022 2778529 := bstep (se 2 (by rfl) ⟨1041948, by rfl⟩ : syracuseStep 2778529 = 2083897) B2083897
theorem B3515825 : Blo 1646022 3515825 := bstep (se 2 (by rfl) ⟨1318434, by rfl⟩ : syracuseStep 3515825 = 2636869) B2636869
theorem B2778563 : Blo 1646022 2778563 := bstep (se 1 (by rfl) ⟨2083922, by rfl⟩ : syracuseStep 2778563 = 4167845) B4167845
theorem B3704273 : Blo 1646022 3704273 := bstep (se 2 (by rfl) ⟨1389102, by rfl⟩ : syracuseStep 3704273 = 2778205) B2778205
theorem B3704291 : Blo 1646022 3704291 := bstep (se 1 (by rfl) ⟨2778218, by rfl⟩ : syracuseStep 3704291 = 5556437) B5556437
theorem B1852915 : Blo 1646022 1852915 := bstep (se 1 (by rfl) ⟨1389686, by rfl⟩ : syracuseStep 1852915 = 2779373) B2779373
theorem B5277197 : Blo 1646022 5277197 := bstep (se 3 (by rfl) ⟨989474, by rfl⟩ : syracuseStep 5277197 = 1978949) B1978949
theorem B101426741 : Blo 1646022 101426741 := bstep (se 5 (by rfl) ⟨4754378, by rfl⟩ : syracuseStep 101426741 = 9508757) B9508757
theorem B2778691 : Blo 1646022 2778691 := bstep (se 1 (by rfl) ⟨2084018, by rfl⟩ : syracuseStep 2778691 = 4168037) B4168037
theorem B5555789 : Blo 1646022 5555789 := bstep (se 3 (by rfl) ⟨1041710, by rfl⟩ : syracuseStep 5555789 = 2083421) B2083421
theorem B5555843 : Blo 1646022 5555843 := bstep (se 1 (by rfl) ⟨4166882, by rfl⟩ : syracuseStep 5555843 = 8333765) B8333765
theorem B1853059 : Blo 1646022 1853059 := bstep (se 1 (by rfl) ⟨1389794, by rfl⟩ : syracuseStep 1853059 = 2779589) B2779589
theorem B2967185 : Blo 1646022 2967185 := bstep (se 2 (by rfl) ⟨1112694, by rfl⟩ : syracuseStep 2967185 = 2225389) B2225389
theorem B4171409 : Blo 1646022 4171409 := bstep (se 2 (by rfl) ⟨1564278, by rfl⟩ : syracuseStep 4171409 = 3128557) B3128557
theorem B4171459 : Blo 1646022 4171459 := bstep (se 1 (by rfl) ⟨3128594, by rfl⟩ : syracuseStep 4171459 = 6257189) B6257189
theorem B22537925 : Blo 1646022 22537925 := bstep (se 4 (by rfl) ⟨2112930, by rfl⟩ : syracuseStep 22537925 = 4225861) B4225861
theorem B2778833 : Blo 1646022 2778833 := bstep (se 2 (by rfl) ⟨1042062, by rfl⟩ : syracuseStep 2778833 = 2084125) B2084125
theorem B6768355 : Blo 1646022 6768355 := bstep (se 1 (by rfl) ⟨5076266, by rfl⟩ : syracuseStep 6768355 = 10152533) B10152533
theorem B3704561 : Blo 1646022 3704561 := bstep (se 2 (by rfl) ⟨1389210, by rfl⟩ : syracuseStep 3704561 = 2778421) B2778421
theorem B3704579 : Blo 1646022 3704579 := bstep (se 1 (by rfl) ⟨2778434, by rfl⟩ : syracuseStep 3704579 = 5556869) B5556869
theorem B1853203 : Blo 1646022 1853203 := bstep (se 1 (by rfl) ⟨1389902, by rfl⟩ : syracuseStep 1853203 = 2779805) B2779805
theorem B10553165 : Blo 1646022 10553165 := bstep (se 3 (by rfl) ⟨1978718, by rfl⟩ : syracuseStep 10553165 = 3957437) B3957437
theorem B2778961 : Blo 1646022 2778961 := bstep (se 2 (by rfl) ⟨1042110, by rfl⟩ : syracuseStep 2778961 = 2084221) B2084221
theorem B3385187 : Blo 1646022 3385187 := bstep (se 1 (by rfl) ⟨2538890, by rfl⟩ : syracuseStep 3385187 = 5077781) B5077781
theorem B2778995 : Blo 1646022 2778995 := bstep (se 1 (by rfl) ⟨2084246, by rfl⟩ : syracuseStep 2778995 = 4168493) B4168493
theorem B5556113 : Blo 1646022 5556113 := bstep (se 2 (by rfl) ⟨2083542, by rfl⟩ : syracuseStep 5556113 = 4167085) B4167085
theorem B1853347 : Blo 1646022 1853347 := bstep (se 1 (by rfl) ⟨1390010, by rfl⟩ : syracuseStep 1853347 = 2780021) B2780021
theorem B4687789 : Blo 1646022 4687789 := bstep (se 3 (by rfl) ⟨878960, by rfl⟩ : syracuseStep 4687789 = 1757921) B1757921
theorem B2344897 : Blo 1646022 2344897 := bstep (se 2 (by rfl) ⟨879336, by rfl⟩ : syracuseStep 2344897 = 1758673) B1758673
theorem B2779123 : Blo 1646022 2779123 := bstep (se 1 (by rfl) ⟨2084342, by rfl⟩ : syracuseStep 2779123 = 4168685) B4168685
theorem B3008515 : Blo 1646022 3008515 := bstep (se 1 (by rfl) ⟨2256386, by rfl⟩ : syracuseStep 3008515 = 4512773) B4512773
theorem B3704849 : Blo 1646022 3704849 := bstep (se 2 (by rfl) ⟨1389318, by rfl⟩ : syracuseStep 3704849 = 2778637) B2778637
theorem B3704867 : Blo 1646022 3704867 := bstep (se 1 (by rfl) ⟨2778650, by rfl⟩ : syracuseStep 3704867 = 5557301) B5557301
theorem B1853491 : Blo 1646022 1853491 := bstep (se 1 (by rfl) ⟨1390118, by rfl⟩ : syracuseStep 1853491 = 2780237) B2780237
theorem B4687949 : Blo 1646022 4687949 := bstep (se 3 (by rfl) ⟨878990, by rfl⟩ : syracuseStep 4687949 = 1757981) B1757981
theorem B10152013 : Blo 1646022 10152013 := bstep (se 3 (by rfl) ⟨1903502, by rfl⟩ : syracuseStep 10152013 = 3807005) B3807005
theorem B160229461 : Blo 1646022 160229461 := bstep (se 8 (by rfl) ⟨938844, by rfl⟩ : syracuseStep 160229461 = 1877689) B1877689
theorem B2779265 : Blo 1646022 2779265 := bstep (se 2 (by rfl) ⟨1042224, by rfl⟩ : syracuseStep 2779265 = 2084449) B2084449
theorem B5007491 : Blo 1646022 5007491 := bstep (se 1 (by rfl) ⟨3755618, by rfl⟩ : syracuseStep 5007491 = 7511237) B7511237
theorem B9513101 : Blo 1646022 9513101 := bstep (se 3 (by rfl) ⟨1783706, by rfl⟩ : syracuseStep 9513101 = 3567413) B3567413
theorem B1853635 : Blo 1646022 1853635 := bstep (se 1 (by rfl) ⟨1390226, by rfl⟩ : syracuseStep 1853635 = 2780453) B2780453
theorem B6252785 : Blo 1646022 6252785 := bstep (se 2 (by rfl) ⟨2344794, by rfl⟩ : syracuseStep 6252785 = 4689589) B4689589
theorem B2779393 : Blo 1646022 2779393 := bstep (se 2 (by rfl) ⟨1042272, by rfl⟩ : syracuseStep 2779393 = 2084545) B2084545
theorem B4688131 : Blo 1646022 4688131 := bstep (se 1 (by rfl) ⟨3516098, by rfl⟩ : syracuseStep 4688131 = 7032197) B7032197
theorem B3516689 : Blo 1646022 3516689 := bstep (se 2 (by rfl) ⟨1318758, by rfl⟩ : syracuseStep 3516689 = 2637517) B2637517
theorem B8333603 : Blo 1646022 8333603 := bstep (se 1 (by rfl) ⟨6250202, by rfl⟩ : syracuseStep 8333603 = 12500405) B12500405
theorem B2779427 : Blo 1646022 2779427 := bstep (se 1 (by rfl) ⟨2084570, by rfl⟩ : syracuseStep 2779427 = 4169141) B4169141
theorem B3705137 : Blo 1646022 3705137 := bstep (se 2 (by rfl) ⟨1389426, by rfl⟩ : syracuseStep 3705137 = 2778853) B2778853
theorem B3705155 : Blo 1646022 3705155 := bstep (se 1 (by rfl) ⟨2778866, by rfl⟩ : syracuseStep 3705155 = 5557733) B5557733
theorem B1853779 : Blo 1646022 1853779 := bstep (se 1 (by rfl) ⟨1390334, by rfl⟩ : syracuseStep 1853779 = 2780669) B2780669
theorem B2779555 : Blo 1646022 2779555 := bstep (se 1 (by rfl) ⟨2084666, by rfl⟩ : syracuseStep 2779555 = 4169333) B4169333
theorem B5556653 : Blo 1646022 5556653 := bstep (se 3 (by rfl) ⟨1041872, by rfl⟩ : syracuseStep 5556653 = 2083745) B2083745
theorem B5556707 : Blo 1646022 5556707 := bstep (se 1 (by rfl) ⟨4167530, by rfl⟩ : syracuseStep 5556707 = 8335061) B8335061
theorem B1853923 : Blo 1646022 1853923 := bstep (se 1 (by rfl) ⟨1390442, by rfl⟩ : syracuseStep 1853923 = 2780885) B2780885
theorem B5712365 : Blo 1646022 5712365 := bstep (se 3 (by rfl) ⟨1071068, by rfl⟩ : syracuseStep 5712365 = 2142137) B2142137
theorem B2083315 : Blo 1646022 2083315 := bstep (se 1 (by rfl) ⟨1562486, by rfl⟩ : syracuseStep 2083315 = 3124973) B3124973
theorem B2779697 : Blo 1646022 2779697 := bstep (se 2 (by rfl) ⟨1042386, by rfl⟩ : syracuseStep 2779697 = 2084773) B2084773
theorem B3705425 : Blo 1646022 3705425 := bstep (se 2 (by rfl) ⟨1389534, by rfl⟩ : syracuseStep 3705425 = 2779069) B2779069
theorem B2083411 : Blo 1646022 2083411 := bstep (se 1 (by rfl) ⟨1562558, by rfl⟩ : syracuseStep 2083411 = 3125117) B3125117
theorem B3705443 : Blo 1646022 3705443 := bstep (se 1 (by rfl) ⟨2779082, by rfl⟩ : syracuseStep 3705443 = 5558165) B5558165
theorem B2345603 : Blo 1646022 2345603 := bstep (se 1 (by rfl) ⟨1759202, by rfl⟩ : syracuseStep 2345603 = 3518405) B3518405
theorem B2779825 : Blo 1646022 2779825 := bstep (se 2 (by rfl) ⟨1042434, by rfl⟩ : syracuseStep 2779825 = 2084869) B2084869
theorem B3009233 : Blo 1646022 3009233 := bstep (se 2 (by rfl) ⟨1128462, by rfl⟩ : syracuseStep 3009233 = 2256925) B2256925
theorem B2779859 : Blo 1646022 2779859 := bstep (se 1 (by rfl) ⟨2084894, by rfl⟩ : syracuseStep 2779859 = 4169789) B4169789
theorem B5556977 : Blo 1646022 5556977 := bstep (se 2 (by rfl) ⟨2083866, by rfl⟩ : syracuseStep 5556977 = 4167733) B4167733
theorem B5933837 : Blo 1646022 5933837 := bstep (se 3 (by rfl) ⟨1112594, by rfl⟩ : syracuseStep 5933837 = 2225189) B2225189
theorem B6679331 : Blo 1646022 6679331 := bstep (se 1 (by rfl) ⟨5009498, by rfl⟩ : syracuseStep 6679331 = 10018997) B10018997
theorem B8907569 : Blo 1646022 8907569 := bstep (se 2 (by rfl) ⟨3340338, by rfl⟩ : syracuseStep 8907569 = 6680677) B6680677
theorem B12512069 : Blo 1646022 12512069 := bstep (se 4 (by rfl) ⟨1173006, by rfl⟩ : syracuseStep 12512069 = 2346013) B2346013
theorem B2779987 : Blo 1646022 2779987 := bstep (se 1 (by rfl) ⟨2084990, by rfl⟩ : syracuseStep 2779987 = 4169981) B4169981
theorem B3705713 : Blo 1646022 3705713 := bstep (se 2 (by rfl) ⟨1389642, by rfl⟩ : syracuseStep 3705713 = 2779285) B2779285
theorem B3705731 : Blo 1646022 3705731 := bstep (se 1 (by rfl) ⟨2779298, by rfl⟩ : syracuseStep 3705731 = 5558597) B5558597
theorem B15829901 : Blo 1646022 15829901 := bstep (se 3 (by rfl) ⟨2968106, by rfl⟩ : syracuseStep 15829901 = 5936213) B5936213
theorem B2673587 : Blo 1646022 2673587 := bstep (se 1 (by rfl) ⟨2005190, by rfl⟩ : syracuseStep 2673587 = 4010381) B4010381
theorem B2780129 : Blo 1646022 2780129 := bstep (se 2 (by rfl) ⟨1042548, by rfl⟩ : syracuseStep 2780129 = 2085097) B2085097
theorem B14076899 : Blo 1646022 14076899 := bstep (se 1 (by rfl) ⟨10557674, by rfl⟩ : syracuseStep 14076899 = 21115349) B21115349
theorem B8342513 : Blo 1646022 8342513 := bstep (se 2 (by rfl) ⟨3128442, by rfl⟩ : syracuseStep 8342513 = 6256885) B6256885
theorem B2083907 : Blo 1646022 2083907 := bstep (se 1 (by rfl) ⟨1562930, by rfl⟩ : syracuseStep 2083907 = 3125861) B3125861
theorem B8334413 : Blo 1646022 8334413 := bstep (se 3 (by rfl) ⟨1562702, by rfl⟩ : syracuseStep 8334413 = 3125405) B3125405
theorem B2780257 : Blo 1646022 2780257 := bstep (se 2 (by rfl) ⟨1042596, by rfl⟩ : syracuseStep 2780257 = 2085193) B2085193
theorem B14068835 : Blo 1646022 14068835 := bstep (se 1 (by rfl) ⟨10551626, by rfl⟩ : syracuseStep 14068835 = 21103253) B21103253
theorem B2780291 : Blo 1646022 2780291 := bstep (se 1 (by rfl) ⟨2085218, by rfl⟩ : syracuseStep 2780291 = 4170437) B4170437
theorem B3706001 : Blo 1646022 3706001 := bstep (se 2 (by rfl) ⟨1389750, by rfl⟩ : syracuseStep 3706001 = 2779501) B2779501
theorem B3706019 : Blo 1646022 3706019 := bstep (se 1 (by rfl) ⟨2779514, by rfl⟩ : syracuseStep 3706019 = 5559029) B5559029
theorem B2469041 : Blo 1646022 2469041 := bstep (se 2 (by rfl) ⟨925890, by rfl⟩ : syracuseStep 2469041 = 1851781) B1851781
theorem B2469059 : Blo 1646022 2469059 := bstep (se 1 (by rfl) ⟨1851794, by rfl⟩ : syracuseStep 2469059 = 3703589) B3703589
theorem B2469089 : Blo 1646022 2469089 := bstep (se 2 (by rfl) ⟨925908, by rfl⟩ : syracuseStep 2469089 = 1851817) B1851817
theorem B10022129 : Blo 1646022 10022129 := bstep (se 2 (by rfl) ⟨3758298, by rfl⟩ : syracuseStep 10022129 = 7516597) B7516597
theorem B2469107 : Blo 1646022 2469107 := bstep (se 1 (by rfl) ⟨1851830, by rfl⟩ : syracuseStep 2469107 = 3703661) B3703661
theorem B2346241 : Blo 1646022 2346241 := bstep (se 2 (by rfl) ⟨879840, by rfl⟩ : syracuseStep 2346241 = 1759681) B1759681
theorem B2780419 : Blo 1646022 2780419 := bstep (se 1 (by rfl) ⟨2085314, by rfl⟩ : syracuseStep 2780419 = 4170629) B4170629
theorem B5557517 : Blo 1646022 5557517 := bstep (se 3 (by rfl) ⟨1042034, by rfl⟩ : syracuseStep 5557517 = 2084069) B2084069
theorem B2469137 : Blo 1646022 2469137 := bstep (se 2 (by rfl) ⟨925926, by rfl⟩ : syracuseStep 2469137 = 1851853) B1851853
theorem B2469155 : Blo 1646022 2469155 := bstep (se 1 (by rfl) ⟨1851866, by rfl⟩ : syracuseStep 2469155 = 3703733) B3703733
theorem B3050801 : Blo 1646022 3050801 := bstep (se 2 (by rfl) ⟨1144050, by rfl⟩ : syracuseStep 3050801 = 2288101) B2288101
theorem B2469185 : Blo 1646022 2469185 := bstep (se 2 (by rfl) ⟨925944, by rfl⟩ : syracuseStep 2469185 = 1851889) B1851889
theorem B5557571 : Blo 1646022 5557571 := bstep (se 1 (by rfl) ⟨4168178, by rfl⟩ : syracuseStep 5557571 = 8336357) B8336357
theorem B2469203 : Blo 1646022 2469203 := bstep (se 1 (by rfl) ⟨1851902, by rfl⟩ : syracuseStep 2469203 = 3703805) B3703805
theorem B2469233 : Blo 1646022 2469233 := bstep (se 2 (by rfl) ⟨925962, by rfl⟩ : syracuseStep 2469233 = 1851925) B1851925
theorem B2346355 : Blo 1646022 2346355 := bstep (se 1 (by rfl) ⟨1759766, by rfl⟩ : syracuseStep 2346355 = 3519533) B3519533
theorem B2469251 : Blo 1646022 2469251 := bstep (se 1 (by rfl) ⟨1851938, by rfl⟩ : syracuseStep 2469251 = 3703877) B3703877
theorem B2780561 : Blo 1646022 2780561 := bstep (se 2 (by rfl) ⟨1042710, by rfl⟩ : syracuseStep 2780561 = 2085421) B2085421
theorem B2469281 : Blo 1646022 2469281 := bstep (se 2 (by rfl) ⟨925980, by rfl⟩ : syracuseStep 2469281 = 1851961) B1851961
theorem B3706289 : Blo 1646022 3706289 := bstep (se 2 (by rfl) ⟨1389858, by rfl⟩ : syracuseStep 3706289 = 2779717) B2779717
theorem B2469299 : Blo 1646022 2469299 := bstep (se 1 (by rfl) ⟨1851974, by rfl⟩ : syracuseStep 2469299 = 3703949) B3703949
theorem B3706307 : Blo 1646022 3706307 := bstep (se 1 (by rfl) ⟨2779730, by rfl⟩ : syracuseStep 3706307 = 5559461) B5559461
theorem B5934541 : Blo 1646022 5934541 := bstep (se 3 (by rfl) ⟨1112726, by rfl⟩ : syracuseStep 5934541 = 2225453) B2225453
theorem B2469329 : Blo 1646022 2469329 := bstep (se 2 (by rfl) ⟨925998, by rfl⟩ : syracuseStep 2469329 = 1851997) B1851997
theorem B2469347 : Blo 1646022 2469347 := bstep (se 1 (by rfl) ⟨1852010, by rfl⟩ : syracuseStep 2469347 = 3704021) B3704021
theorem B2469377 : Blo 1646022 2469377 := bstep (se 2 (by rfl) ⟨926016, by rfl⟩ : syracuseStep 2469377 = 1852033) B1852033
theorem B2780689 : Blo 1646022 2780689 := bstep (se 2 (by rfl) ⟨1042758, by rfl⟩ : syracuseStep 2780689 = 2085517) B2085517
theorem B2469395 : Blo 1646022 2469395 := bstep (se 1 (by rfl) ⟨1852046, by rfl⟩ : syracuseStep 2469395 = 3704093) B3704093
theorem B3517987 : Blo 1646022 3517987 := bstep (se 1 (by rfl) ⟨2638490, by rfl⟩ : syracuseStep 3517987 = 5276981) B5276981
theorem B2469425 : Blo 1646022 2469425 := bstep (se 2 (by rfl) ⟨926034, by rfl⟩ : syracuseStep 2469425 = 1852069) B1852069
theorem B2780723 : Blo 1646022 2780723 := bstep (se 1 (by rfl) ⟨2085542, by rfl⟩ : syracuseStep 2780723 = 4171085) B4171085
theorem B2469443 : Blo 1646022 2469443 := bstep (se 1 (by rfl) ⟨1852082, by rfl⟩ : syracuseStep 2469443 = 3704165) B3704165
theorem B5557841 : Blo 1646022 5557841 := bstep (se 2 (by rfl) ⟨2084190, by rfl⟩ : syracuseStep 5557841 = 4168381) B4168381
theorem B2469473 : Blo 1646022 2469473 := bstep (se 2 (by rfl) ⟨926052, by rfl⟩ : syracuseStep 2469473 = 1852105) B1852105
theorem B4689521 : Blo 1646022 4689521 := bstep (se 2 (by rfl) ⟨1758570, by rfl⟩ : syracuseStep 4689521 = 3517141) B3517141
theorem B2469491 : Blo 1646022 2469491 := bstep (se 1 (by rfl) ⟨1852118, by rfl⟩ : syracuseStep 2469491 = 3704237) B3704237
theorem B2469521 : Blo 1646022 2469521 := bstep (se 2 (by rfl) ⟨926070, by rfl⟩ : syracuseStep 2469521 = 1852141) B1852141
theorem B5279377 : Blo 1646022 5279377 := bstep (se 2 (by rfl) ⟨1979766, by rfl⟩ : syracuseStep 5279377 = 3959533) B3959533
theorem B2469539 : Blo 1646022 2469539 := bstep (se 1 (by rfl) ⟨1852154, by rfl⟩ : syracuseStep 2469539 = 3704309) B3704309
theorem B6254243 : Blo 1646022 6254243 := bstep (se 1 (by rfl) ⟨4690682, by rfl⟩ : syracuseStep 6254243 = 9381365) B9381365
theorem B2780851 : Blo 1646022 2780851 := bstep (se 1 (by rfl) ⟨2085638, by rfl⟩ : syracuseStep 2780851 = 4171277) B4171277
theorem B2469569 : Blo 1646022 2469569 := bstep (se 2 (by rfl) ⟨926088, by rfl⟩ : syracuseStep 2469569 = 1852177) B1852177
theorem B3706577 : Blo 1646022 3706577 := bstep (se 2 (by rfl) ⟨1389966, by rfl⟩ : syracuseStep 3706577 = 2779933) B2779933
theorem B2469587 : Blo 1646022 2469587 := bstep (se 1 (by rfl) ⟨1852190, by rfl⟩ : syracuseStep 2469587 = 3704381) B3704381
theorem B3706595 : Blo 1646022 3706595 := bstep (se 1 (by rfl) ⟨2779946, by rfl⟩ : syracuseStep 3706595 = 5559893) B5559893
theorem B2469617 : Blo 1646022 2469617 := bstep (se 2 (by rfl) ⟨926106, by rfl⟩ : syracuseStep 2469617 = 1852213) B1852213
theorem B2469635 : Blo 1646022 2469635 := bstep (se 1 (by rfl) ⟨1852226, by rfl⟩ : syracuseStep 2469635 = 3704453) B3704453
theorem B2084611 : Blo 1646022 2084611 := bstep (se 1 (by rfl) ⟨1563458, by rfl⟩ : syracuseStep 2084611 = 3126917) B3126917
theorem B2469665 : Blo 1646022 2469665 := bstep (se 2 (by rfl) ⟨926124, by rfl⟩ : syracuseStep 2469665 = 1852249) B1852249
theorem B2469683 : Blo 1646022 2469683 := bstep (se 1 (by rfl) ⟨1852262, by rfl⟩ : syracuseStep 2469683 = 3704525) B3704525
theorem B2780993 : Blo 1646022 2780993 := bstep (se 2 (by rfl) ⟨1042872, by rfl⟩ : syracuseStep 2780993 = 2085745) B2085745
theorem B5279555 : Blo 1646022 5279555 := bstep (se 1 (by rfl) ⟨3959666, by rfl⟩ : syracuseStep 5279555 = 7919333) B7919333
theorem B2469713 : Blo 1646022 2469713 := bstep (se 2 (by rfl) ⟨926142, by rfl⟩ : syracuseStep 2469713 = 1852285) B1852285
theorem B2469731 : Blo 1646022 2469731 := bstep (se 1 (by rfl) ⟨1852298, by rfl⟩ : syracuseStep 2469731 = 3704597) B3704597
theorem B2084707 : Blo 1646022 2084707 := bstep (se 1 (by rfl) ⟨1563530, by rfl⟩ : syracuseStep 2084707 = 3127061) B3127061
theorem B2674547 : Blo 1646022 2674547 := bstep (se 1 (by rfl) ⟨2005910, by rfl⟩ : syracuseStep 2674547 = 4011821) B4011821
theorem B2469761 : Blo 1646022 2469761 := bstep (se 2 (by rfl) ⟨926160, by rfl⟩ : syracuseStep 2469761 = 1852321) B1852321
theorem B2469779 : Blo 1646022 2469779 := bstep (se 1 (by rfl) ⟨1852334, by rfl⟩ : syracuseStep 2469779 = 3704669) B3704669
theorem B3125155 : Blo 1646022 3125155 := bstep (se 1 (by rfl) ⟨2343866, by rfl⟩ : syracuseStep 3125155 = 4687733) B4687733
theorem B2674595 : Blo 1646022 2674595 := bstep (se 1 (by rfl) ⟨2005946, by rfl⟩ : syracuseStep 2674595 = 4011893) B4011893
theorem B2469809 : Blo 1646022 2469809 := bstep (se 2 (by rfl) ⟨926178, by rfl⟩ : syracuseStep 2469809 = 1852357) B1852357
theorem B2469827 : Blo 1646022 2469827 := bstep (se 1 (by rfl) ⟨1852370, by rfl⟩ : syracuseStep 2469827 = 3704741) B3704741
theorem B2469857 : Blo 1646022 2469857 := bstep (se 2 (by rfl) ⟨926196, by rfl⟩ : syracuseStep 2469857 = 1852393) B1852393
theorem B3706865 : Blo 1646022 3706865 := bstep (se 2 (by rfl) ⟨1390074, by rfl⟩ : syracuseStep 3706865 = 2780149) B2780149
theorem B2469875 : Blo 1646022 2469875 := bstep (se 1 (by rfl) ⟨1852406, by rfl⟩ : syracuseStep 2469875 = 3704813) B3704813
theorem B3706883 : Blo 1646022 3706883 := bstep (se 1 (by rfl) ⟨2780162, by rfl⟩ : syracuseStep 3706883 = 5560325) B5560325
theorem B7032845 : Blo 1646022 7032845 := bstep (se 3 (by rfl) ⟨1318658, by rfl⟩ : syracuseStep 7032845 = 2637317) B2637317
theorem B2469905 : Blo 1646022 2469905 := bstep (se 2 (by rfl) ⟨926214, by rfl⟩ : syracuseStep 2469905 = 1852429) B1852429
theorem B2469923 : Blo 1646022 2469923 := bstep (se 1 (by rfl) ⟨1852442, by rfl⟩ : syracuseStep 2469923 = 3704885) B3704885
theorem B2969635 : Blo 1646022 2969635 := bstep (se 1 (by rfl) ⟨2227226, by rfl⟩ : syracuseStep 2969635 = 4454453) B4454453
theorem B2469953 : Blo 1646022 2469953 := bstep (se 2 (by rfl) ⟨926232, by rfl⟩ : syracuseStep 2469953 = 1852465) B1852465
theorem B2469971 : Blo 1646022 2469971 := bstep (se 1 (by rfl) ⟨1852478, by rfl⟩ : syracuseStep 2469971 = 3704957) B3704957
theorem B5009507 : Blo 1646022 5009507 := bstep (se 1 (by rfl) ⟨3757130, by rfl⟩ : syracuseStep 5009507 = 7514261) B7514261
theorem B5558381 : Blo 1646022 5558381 := bstep (se 3 (by rfl) ⟨1042196, by rfl⟩ : syracuseStep 5558381 = 2084393) B2084393
theorem B2470001 : Blo 1646022 2470001 := bstep (se 2 (by rfl) ⟨926250, by rfl⟩ : syracuseStep 2470001 = 1852501) B1852501
theorem B2470019 : Blo 1646022 2470019 := bstep (se 1 (by rfl) ⟨1852514, by rfl⟩ : syracuseStep 2470019 = 3705029) B3705029
theorem B2470049 : Blo 1646022 2470049 := bstep (se 2 (by rfl) ⟨926268, by rfl⟩ : syracuseStep 2470049 = 1852537) B1852537
theorem B5558435 : Blo 1646022 5558435 := bstep (se 1 (by rfl) ⟨4168826, by rfl⟩ : syracuseStep 5558435 = 8337653) B8337653
theorem B2470067 : Blo 1646022 2470067 := bstep (se 1 (by rfl) ⟨1852550, by rfl⟩ : syracuseStep 2470067 = 3705101) B3705101
theorem B2470097 : Blo 1646022 2470097 := bstep (se 2 (by rfl) ⟨926286, by rfl⟩ : syracuseStep 2470097 = 1852573) B1852573
theorem B2470115 : Blo 1646022 2470115 := bstep (se 1 (by rfl) ⟨1852586, by rfl⟩ : syracuseStep 2470115 = 3705173) B3705173
theorem B2470145 : Blo 1646022 2470145 := bstep (se 2 (by rfl) ⟨926304, by rfl⟩ : syracuseStep 2470145 = 1852609) B1852609
theorem B3707153 : Blo 1646022 3707153 := bstep (se 2 (by rfl) ⟨1390182, by rfl⟩ : syracuseStep 3707153 = 2780365) B2780365
theorem B2470163 : Blo 1646022 2470163 := bstep (se 1 (by rfl) ⟨1852622, by rfl⟩ : syracuseStep 2470163 = 3705245) B3705245
theorem B3707171 : Blo 1646022 3707171 := bstep (se 1 (by rfl) ⟨2780378, by rfl⟩ : syracuseStep 3707171 = 5560757) B5560757
theorem B2470193 : Blo 1646022 2470193 := bstep (se 2 (by rfl) ⟨926322, by rfl⟩ : syracuseStep 2470193 = 1852645) B1852645
theorem B2470211 : Blo 1646022 2470211 := bstep (se 1 (by rfl) ⟨1852658, by rfl⟩ : syracuseStep 2470211 = 3705317) B3705317
theorem B2085203 : Blo 1646022 2085203 := bstep (se 1 (by rfl) ⟨1563902, by rfl⟩ : syracuseStep 2085203 = 3127805) B3127805
theorem B2470241 : Blo 1646022 2470241 := bstep (se 2 (by rfl) ⟨926340, by rfl⟩ : syracuseStep 2470241 = 1852681) B1852681
theorem B3125603 : Blo 1646022 3125603 := bstep (se 1 (by rfl) ⟨2344202, by rfl⟩ : syracuseStep 3125603 = 4688405) B4688405
theorem B1782131 : Blo 1646022 1782131 := bstep (se 1 (by rfl) ⟨1336598, by rfl⟩ : syracuseStep 1782131 = 2673197) B2673197
theorem B2470259 : Blo 1646022 2470259 := bstep (se 1 (by rfl) ⟨1852694, by rfl⟩ : syracuseStep 2470259 = 3705389) B3705389
theorem B2470289 : Blo 1646022 2470289 := bstep (se 2 (by rfl) ⟨926358, by rfl⟩ : syracuseStep 2470289 = 1852717) B1852717
theorem B2470307 : Blo 1646022 2470307 := bstep (se 1 (by rfl) ⟨1852730, by rfl⟩ : syracuseStep 2470307 = 3705461) B3705461
theorem B5558705 : Blo 1646022 5558705 := bstep (se 2 (by rfl) ⟨2084514, by rfl⟩ : syracuseStep 5558705 = 4169029) B4169029
theorem B2470337 : Blo 1646022 2470337 := bstep (se 2 (by rfl) ⟨926376, by rfl⟩ : syracuseStep 2470337 = 1852753) B1852753
theorem B2470355 : Blo 1646022 2470355 := bstep (se 1 (by rfl) ⟨1852766, by rfl⟩ : syracuseStep 2470355 = 3705533) B3705533
theorem B2470385 : Blo 1646022 2470385 := bstep (se 2 (by rfl) ⟨926394, by rfl⟩ : syracuseStep 2470385 = 1852789) B1852789
theorem B2470403 : Blo 1646022 2470403 := bstep (se 1 (by rfl) ⟨1852802, by rfl⟩ : syracuseStep 2470403 = 3705605) B3705605
theorem B2470433 : Blo 1646022 2470433 := bstep (se 2 (by rfl) ⟨926412, by rfl⟩ : syracuseStep 2470433 = 1852825) B1852825
theorem B2224675 : Blo 1646022 2224675 := bstep (se 1 (by rfl) ⟨1668506, by rfl⟩ : syracuseStep 2224675 = 3337013) B3337013
theorem B4690477 : Blo 1646022 4690477 := bstep (se 3 (by rfl) ⟨879464, by rfl⟩ : syracuseStep 4690477 = 1758929) B1758929
theorem B3707441 : Blo 1646022 3707441 := bstep (se 2 (by rfl) ⟨1390290, by rfl⟩ : syracuseStep 3707441 = 2780581) B2780581
theorem B2470451 : Blo 1646022 2470451 := bstep (se 1 (by rfl) ⟨1852838, by rfl⟩ : syracuseStep 2470451 = 3705677) B3705677
theorem B3707459 : Blo 1646022 3707459 := bstep (se 1 (by rfl) ⟨2780594, by rfl⟩ : syracuseStep 3707459 = 5561189) B5561189
theorem B2470481 : Blo 1646022 2470481 := bstep (se 2 (by rfl) ⟨926430, by rfl⟩ : syracuseStep 2470481 = 1852861) B1852861
theorem B2470499 : Blo 1646022 2470499 := bstep (se 1 (by rfl) ⟨1852874, by rfl⟩ : syracuseStep 2470499 = 3705749) B3705749
theorem B2470529 : Blo 1646022 2470529 := bstep (se 2 (by rfl) ⟨926448, by rfl⟩ : syracuseStep 2470529 = 1852897) B1852897
theorem B3125891 : Blo 1646022 3125891 := bstep (se 1 (by rfl) ⟨2344418, by rfl⟩ : syracuseStep 3125891 = 4688837) B4688837
theorem B6255245 : Blo 1646022 6255245 := bstep (se 3 (by rfl) ⟨1172858, by rfl⟩ : syracuseStep 6255245 = 2345717) B2345717
theorem B2470547 : Blo 1646022 2470547 := bstep (se 1 (by rfl) ⟨1852910, by rfl⟩ : syracuseStep 2470547 = 3705821) B3705821
theorem B2470577 : Blo 1646022 2470577 := bstep (se 2 (by rfl) ⟨926466, by rfl⟩ : syracuseStep 2470577 = 1852933) B1852933
theorem B2470595 : Blo 1646022 2470595 := bstep (se 1 (by rfl) ⟨1852946, by rfl⟩ : syracuseStep 2470595 = 3705893) B3705893
theorem B4453069 : Blo 1646022 4453069 := bstep (se 3 (by rfl) ⟨834950, by rfl⟩ : syracuseStep 4453069 = 1669901) B1669901
theorem B2470625 : Blo 1646022 2470625 := bstep (se 2 (by rfl) ⟨926484, by rfl⟩ : syracuseStep 2470625 = 1852969) B1852969
theorem B13349603 : Blo 1646022 13349603 := bstep (se 1 (by rfl) ⟨10012202, by rfl⟩ : syracuseStep 13349603 = 20024405) B20024405
theorem B3519217 : Blo 1646022 3519217 := bstep (se 2 (by rfl) ⟨1319706, by rfl⟩ : syracuseStep 3519217 = 2639413) B2639413
theorem B2470643 : Blo 1646022 2470643 := bstep (se 1 (by rfl) ⟨1852982, by rfl⟩ : syracuseStep 2470643 = 3705965) B3705965
theorem B2470673 : Blo 1646022 2470673 := bstep (se 2 (by rfl) ⟨926502, by rfl⟩ : syracuseStep 2470673 = 1853005) B1853005
theorem B4690705 : Blo 1646022 4690705 := bstep (se 2 (by rfl) ⟨1759014, by rfl⟩ : syracuseStep 4690705 = 3518029) B3518029
theorem B2470691 : Blo 1646022 2470691 := bstep (se 1 (by rfl) ⟨1853018, by rfl⟩ : syracuseStep 2470691 = 3706037) B3706037
theorem B2503489 : Blo 1646022 2503489 := bstep (se 2 (by rfl) ⟨938808, by rfl⟩ : syracuseStep 2503489 = 1877617) B1877617
theorem B2470721 : Blo 1646022 2470721 := bstep (se 2 (by rfl) ⟨926520, by rfl⟩ : syracuseStep 2470721 = 1853041) B1853041
theorem B9384781 : Blo 1646022 9384781 := bstep (se 3 (by rfl) ⟨1759646, by rfl⟩ : syracuseStep 9384781 = 3519293) B3519293
theorem B3707729 : Blo 1646022 3707729 := bstep (se 2 (by rfl) ⟨1390398, by rfl⟩ : syracuseStep 3707729 = 2780797) B2780797
theorem B2470739 : Blo 1646022 2470739 := bstep (se 1 (by rfl) ⟨1853054, by rfl⟩ : syracuseStep 2470739 = 3706109) B3706109
theorem B7910243 : Blo 1646022 7910243 := bstep (se 1 (by rfl) ⟨5932682, by rfl⟩ : syracuseStep 7910243 = 11865365) B11865365
theorem B3707747 : Blo 1646022 3707747 := bstep (se 1 (by rfl) ⟨2780810, by rfl⟩ : syracuseStep 3707747 = 5561621) B5561621
theorem B2470769 : Blo 1646022 2470769 := bstep (se 2 (by rfl) ⟨926538, by rfl⟩ : syracuseStep 2470769 = 1853077) B1853077
theorem B2470787 : Blo 1646022 2470787 := bstep (se 1 (by rfl) ⟨1853090, by rfl⟩ : syracuseStep 2470787 = 3706181) B3706181
theorem B2470817 : Blo 1646022 2470817 := bstep (se 2 (by rfl) ⟨926556, by rfl⟩ : syracuseStep 2470817 = 1853113) B1853113
theorem B4690865 : Blo 1646022 4690865 := bstep (se 2 (by rfl) ⟨1759074, by rfl⟩ : syracuseStep 4690865 = 3518149) B3518149
theorem B2470835 : Blo 1646022 2470835 := bstep (se 1 (by rfl) ⟨1853126, by rfl⟩ : syracuseStep 2470835 = 3706253) B3706253
theorem B5559245 : Blo 1646022 5559245 := bstep (se 3 (by rfl) ⟨1042358, by rfl⟩ : syracuseStep 5559245 = 2084717) B2084717
theorem B2470865 : Blo 1646022 2470865 := bstep (se 2 (by rfl) ⟨926574, by rfl⟩ : syracuseStep 2470865 = 1853149) B1853149
theorem B2470883 : Blo 1646022 2470883 := bstep (se 1 (by rfl) ⟨1853162, by rfl⟩ : syracuseStep 2470883 = 3706325) B3706325
theorem B2470913 : Blo 1646022 2470913 := bstep (se 2 (by rfl) ⟨926592, by rfl⟩ : syracuseStep 2470913 = 1853185) B1853185
theorem B5559299 : Blo 1646022 5559299 := bstep (se 1 (by rfl) ⟨4169474, by rfl⟩ : syracuseStep 5559299 = 8338949) B8338949
theorem B12030989 : Blo 1646022 12030989 := bstep (se 3 (by rfl) ⟨2255810, by rfl⟩ : syracuseStep 12030989 = 4511621) B4511621
theorem B2470931 : Blo 1646022 2470931 := bstep (se 1 (by rfl) ⟨1853198, by rfl⟩ : syracuseStep 2470931 = 3706397) B3706397
theorem B4690979 : Blo 1646022 4690979 := bstep (se 1 (by rfl) ⟨3518234, by rfl⟩ : syracuseStep 4690979 = 7036469) B7036469
theorem B2470961 : Blo 1646022 2470961 := bstep (se 2 (by rfl) ⟨926610, by rfl⟩ : syracuseStep 2470961 = 1853221) B1853221
theorem B2470979 : Blo 1646022 2470979 := bstep (se 1 (by rfl) ⟨1853234, by rfl⟩ : syracuseStep 2470979 = 3706469) B3706469
theorem B2471009 : Blo 1646022 2471009 := bstep (se 2 (by rfl) ⟨926628, by rfl⟩ : syracuseStep 2471009 = 1853257) B1853257
theorem B3708017 : Blo 1646022 3708017 := bstep (se 2 (by rfl) ⟨1390506, by rfl⟩ : syracuseStep 3708017 = 2781013) B2781013
theorem B2471027 : Blo 1646022 2471027 := bstep (se 1 (by rfl) ⟨1853270, by rfl⟩ : syracuseStep 2471027 = 3706541) B3706541
theorem B3708035 : Blo 1646022 3708035 := bstep (se 1 (by rfl) ⟨2781026, by rfl⟩ : syracuseStep 3708035 = 5562053) B5562053
theorem B2471057 : Blo 1646022 2471057 := bstep (se 2 (by rfl) ⟨926646, by rfl⟩ : syracuseStep 2471057 = 1853293) B1853293
theorem B2471075 : Blo 1646022 2471075 := bstep (se 1 (by rfl) ⟨1853306, by rfl⟩ : syracuseStep 2471075 = 3706613) B3706613
theorem B2471105 : Blo 1646022 2471105 := bstep (se 2 (by rfl) ⟨926664, by rfl⟩ : syracuseStep 2471105 = 1853329) B1853329
theorem B2471123 : Blo 1646022 2471123 := bstep (se 1 (by rfl) ⟨1853342, by rfl⟩ : syracuseStep 2471123 = 3706685) B3706685
theorem B2471153 : Blo 1646022 2471153 := bstep (se 2 (by rfl) ⟨926682, by rfl⟩ : syracuseStep 2471153 = 1853365) B1853365
theorem B2471171 : Blo 1646022 2471171 := bstep (se 1 (by rfl) ⟨1853378, by rfl⟩ : syracuseStep 2471171 = 3706757) B3706757
theorem B1979651 : Blo 1646022 1979651 := bstep (se 1 (by rfl) ⟨1484738, by rfl⟩ : syracuseStep 1979651 = 2969477) B2969477
theorem B5559569 : Blo 1646022 5559569 := bstep (se 2 (by rfl) ⟨2084838, by rfl⟩ : syracuseStep 5559569 = 4169677) B4169677
theorem B2471201 : Blo 1646022 2471201 := bstep (se 2 (by rfl) ⟨926700, by rfl⟩ : syracuseStep 2471201 = 1853401) B1853401
theorem B1758515 : Blo 1646022 1758515 := bstep (se 1 (by rfl) ⟨1318886, by rfl⟩ : syracuseStep 1758515 = 2637773) B2637773
theorem B2471219 : Blo 1646022 2471219 := bstep (se 1 (by rfl) ⟨1853414, by rfl⟩ : syracuseStep 2471219 = 3706829) B3706829
theorem B2471249 : Blo 1646022 2471249 := bstep (se 2 (by rfl) ⟨926718, by rfl⟩ : syracuseStep 2471249 = 1853437) B1853437
theorem B2471267 : Blo 1646022 2471267 := bstep (se 1 (by rfl) ⟨1853450, by rfl⟩ : syracuseStep 2471267 = 3706901) B3706901
theorem B2471297 : Blo 1646022 2471297 := bstep (se 2 (by rfl) ⟨926736, by rfl⟩ : syracuseStep 2471297 = 1853473) B1853473
theorem B2471315 : Blo 1646022 2471315 := bstep (se 1 (by rfl) ⟨1853486, by rfl⟩ : syracuseStep 2471315 = 3706973) B3706973
theorem B2471345 : Blo 1646022 2471345 := bstep (se 2 (by rfl) ⟨926754, by rfl⟩ : syracuseStep 2471345 = 1853509) B1853509
theorem B2471363 : Blo 1646022 2471363 := bstep (se 1 (by rfl) ⟨1853522, by rfl⟩ : syracuseStep 2471363 = 3707045) B3707045
theorem B2471393 : Blo 1646022 2471393 := bstep (se 2 (by rfl) ⟨926772, by rfl⟩ : syracuseStep 2471393 = 1853545) B1853545
theorem B5633507 : Blo 1646022 5633507 := bstep (se 1 (by rfl) ⟨4225130, by rfl⟩ : syracuseStep 5633507 = 8450261) B8450261
theorem B2471411 : Blo 1646022 2471411 := bstep (se 1 (by rfl) ⟨1853558, by rfl⟩ : syracuseStep 2471411 = 3707117) B3707117
theorem B2471441 : Blo 1646022 2471441 := bstep (se 2 (by rfl) ⟨926790, by rfl⟩ : syracuseStep 2471441 = 1853581) B1853581
theorem B2471459 : Blo 1646022 2471459 := bstep (se 1 (by rfl) ⟨1853594, by rfl⟩ : syracuseStep 2471459 = 3707189) B3707189
theorem B4453933 : Blo 1646022 4453933 := bstep (se 3 (by rfl) ⟨835112, by rfl⟩ : syracuseStep 4453933 = 1670225) B1670225
theorem B2225713 : Blo 1646022 2225713 := bstep (se 2 (by rfl) ⟨834642, by rfl⟩ : syracuseStep 2225713 = 1669285) B1669285
theorem B3126833 : Blo 1646022 3126833 := bstep (se 2 (by rfl) ⟨1172562, by rfl⟩ : syracuseStep 3126833 = 2345125) B2345125
theorem B2471489 : Blo 1646022 2471489 := bstep (se 2 (by rfl) ⟨926808, by rfl⟩ : syracuseStep 2471489 = 1853617) B1853617
theorem B2471507 : Blo 1646022 2471507 := bstep (se 1 (by rfl) ⟨1853630, by rfl⟩ : syracuseStep 2471507 = 3707261) B3707261
theorem B12506723 : Blo 1646022 12506723 := bstep (se 1 (by rfl) ⟨9380042, by rfl⟩ : syracuseStep 12506723 = 18760085) B18760085
theorem B3806833 : Blo 1646022 3806833 := bstep (se 2 (by rfl) ⟨1427562, by rfl⟩ : syracuseStep 3806833 = 2855125) B2855125
theorem B35599985 : Blo 1646022 35599985 := bstep (se 2 (by rfl) ⟨13349994, by rfl⟩ : syracuseStep 35599985 = 26699989) B26699989
theorem B2471537 : Blo 1646022 2471537 := bstep (se 2 (by rfl) ⟨926826, by rfl⟩ : syracuseStep 2471537 = 1853653) B1853653
theorem B2471555 : Blo 1646022 2471555 := bstep (se 1 (by rfl) ⟨1853666, by rfl⟩ : syracuseStep 2471555 = 3707333) B3707333
theorem B2471585 : Blo 1646022 2471585 := bstep (se 2 (by rfl) ⟨926844, by rfl⟩ : syracuseStep 2471585 = 1853689) B1853689
theorem B2471603 : Blo 1646022 2471603 := bstep (se 1 (by rfl) ⟨1853702, by rfl⟩ : syracuseStep 2471603 = 3707405) B3707405
theorem B2471633 : Blo 1646022 2471633 := bstep (se 2 (by rfl) ⟨926862, by rfl⟩ : syracuseStep 2471633 = 1853725) B1853725
theorem B2471651 : Blo 1646022 2471651 := bstep (se 1 (by rfl) ⟨1853738, by rfl⟩ : syracuseStep 2471651 = 3707477) B3707477
theorem B4167409 : Blo 1646022 4167409 := bstep (se 2 (by rfl) ⟨1562778, by rfl⟩ : syracuseStep 4167409 = 3125557) B3125557
theorem B2471681 : Blo 1646022 2471681 := bstep (se 2 (by rfl) ⟨926880, by rfl⟩ : syracuseStep 2471681 = 1853761) B1853761
theorem B2471699 : Blo 1646022 2471699 := bstep (se 1 (by rfl) ⟨1853774, by rfl⟩ : syracuseStep 2471699 = 3707549) B3707549
theorem B5560109 : Blo 1646022 5560109 := bstep (se 3 (by rfl) ⟨1042520, by rfl⟩ : syracuseStep 5560109 = 2085041) B2085041
theorem B2471729 : Blo 1646022 2471729 := bstep (se 2 (by rfl) ⟨926898, by rfl⟩ : syracuseStep 2471729 = 1853797) B1853797
theorem B2471747 : Blo 1646022 2471747 := bstep (se 1 (by rfl) ⟨1853810, by rfl⟩ : syracuseStep 2471747 = 3707621) B3707621
theorem B2471777 : Blo 1646022 2471777 := bstep (se 2 (by rfl) ⟨926916, by rfl⟩ : syracuseStep 2471777 = 1853833) B1853833
theorem B5560163 : Blo 1646022 5560163 := bstep (se 1 (by rfl) ⟨4170122, by rfl⟩ : syracuseStep 5560163 = 8340245) B8340245
theorem B2471795 : Blo 1646022 2471795 := bstep (se 1 (by rfl) ⟨1853846, by rfl⟩ : syracuseStep 2471795 = 3707693) B3707693
theorem B10557317 : Blo 1646022 10557317 := bstep (se 4 (by rfl) ⟨989748, by rfl⟩ : syracuseStep 10557317 = 1979497) B1979497
theorem B2471825 : Blo 1646022 2471825 := bstep (se 2 (by rfl) ⟨926934, by rfl⟩ : syracuseStep 2471825 = 1853869) B1853869
theorem B5273507 : Blo 1646022 5273507 := bstep (se 1 (by rfl) ⟨3955130, by rfl⟩ : syracuseStep 5273507 = 7910261) B7910261
theorem B3168163 : Blo 1646022 3168163 := bstep (se 1 (by rfl) ⟨2376122, by rfl⟩ : syracuseStep 3168163 = 4752245) B4752245
theorem B2471843 : Blo 1646022 2471843 := bstep (se 1 (by rfl) ⟨1853882, by rfl⟩ : syracuseStep 2471843 = 3707765) B3707765
theorem B8337329 : Blo 1646022 8337329 := bstep (se 2 (by rfl) ⟨3126498, by rfl⟩ : syracuseStep 8337329 = 6252997) B6252997
theorem B2471873 : Blo 1646022 2471873 := bstep (se 2 (by rfl) ⟨926952, by rfl⟩ : syracuseStep 2471873 = 1853905) B1853905
theorem B2471891 : Blo 1646022 2471891 := bstep (se 1 (by rfl) ⟨1853918, by rfl⟩ : syracuseStep 2471891 = 3707837) B3707837
theorem B2471921 : Blo 1646022 2471921 := bstep (se 2 (by rfl) ⟨926970, by rfl⟩ : syracuseStep 2471921 = 1853941) B1853941
theorem B4167683 : Blo 1646022 4167683 := bstep (se 1 (by rfl) ⟨3125762, by rfl⟩ : syracuseStep 4167683 = 6251525) B6251525
theorem B1669123 : Blo 1646022 1669123 := bstep (se 1 (by rfl) ⟨1251842, by rfl⟩ : syracuseStep 1669123 = 2503685) B2503685
theorem B2471939 : Blo 1646022 2471939 := bstep (se 1 (by rfl) ⟨1853954, by rfl⟩ : syracuseStep 2471939 = 3707909) B3707909
theorem B4691981 : Blo 1646022 4691981 := bstep (se 3 (by rfl) ⟨879746, by rfl⟩ : syracuseStep 4691981 = 1759493) B1759493
theorem B1759267 : Blo 1646022 1759267 := bstep (se 1 (by rfl) ⟨1319450, by rfl⟩ : syracuseStep 1759267 = 2638901) B2638901
theorem B2471969 : Blo 1646022 2471969 := bstep (se 2 (by rfl) ⟨926988, by rfl⟩ : syracuseStep 2471969 = 1853977) B1853977
theorem B1669171 : Blo 1646022 1669171 := bstep (se 1 (by rfl) ⟨1251878, by rfl⟩ : syracuseStep 1669171 = 2503757) B2503757
theorem B2471987 : Blo 1646022 2471987 := bstep (se 1 (by rfl) ⟨1853990, by rfl⟩ : syracuseStep 2471987 = 3707981) B3707981
theorem B2472017 : Blo 1646022 2472017 := bstep (se 2 (by rfl) ⟨927006, by rfl⟩ : syracuseStep 2472017 = 1854013) B1854013
theorem B5560433 : Blo 1646022 5560433 := bstep (se 2 (by rfl) ⟨2085162, by rfl⟩ : syracuseStep 5560433 = 4170325) B4170325
theorem B23730317 : Blo 1646022 23730317 := bstep (se 3 (by rfl) ⟨4449434, by rfl⟩ : syracuseStep 23730317 = 8898869) B8898869
theorem B5634193 : Blo 1646022 5634193 := bstep (se 2 (by rfl) ⟨2112822, by rfl⟩ : syracuseStep 5634193 = 4225645) B4225645
theorem B4167875 : Blo 1646022 4167875 := bstep (se 1 (by rfl) ⟨3125906, by rfl⟩ : syracuseStep 4167875 = 6251813) B6251813
theorem B4692163 : Blo 1646022 4692163 := bstep (se 1 (by rfl) ⟨3519122, by rfl⟩ : syracuseStep 4692163 = 7038245) B7038245
theorem B22542563 : Blo 1646022 22542563 := bstep (se 1 (by rfl) ⟨16906922, by rfl⟩ : syracuseStep 22542563 = 33813845) B33813845
theorem B5273905 : Blo 1646022 5273905 := bstep (se 2 (by rfl) ⟨1977714, by rfl⟩ : syracuseStep 5273905 = 3955429) B3955429
theorem B4692323 : Blo 1646022 4692323 := bstep (se 1 (by rfl) ⟨3519242, by rfl⟩ : syracuseStep 4692323 = 7038485) B7038485
theorem B5274019 : Blo 1646022 5274019 := bstep (se 1 (by rfl) ⟨3955514, by rfl⟩ : syracuseStep 5274019 = 7911029) B7911029
theorem B3127729 : Blo 1646022 3127729 := bstep (se 2 (by rfl) ⟨1172898, by rfl⟩ : syracuseStep 3127729 = 2345797) B2345797
theorem B3127889 : Blo 1646022 3127889 := bstep (se 2 (by rfl) ⟨1172958, by rfl⟩ : syracuseStep 3127889 = 2345917) B2345917
theorem B5560973 : Blo 1646022 5560973 := bstep (se 3 (by rfl) ⟨1042682, by rfl⟩ : syracuseStep 5560973 = 2085365) B2085365
theorem B5561027 : Blo 1646022 5561027 := bstep (se 1 (by rfl) ⟨4170770, by rfl⟩ : syracuseStep 5561027 = 8341541) B8341541
theorem B83467205 : Blo 1646022 83467205 := bstep (se 4 (by rfl) ⟨7825050, by rfl⟩ : syracuseStep 83467205 = 15650101) B15650101
theorem B5561297 : Blo 1646022 5561297 := bstep (se 2 (by rfl) ⟨2085486, by rfl⟩ : syracuseStep 5561297 = 4170973) B4170973
theorem B18758627 : Blo 1646022 18758627 := bstep (se 1 (by rfl) ⟨14068970, by rfl⟩ : syracuseStep 18758627 = 28137941) B28137941
theorem B3128291 : Blo 1646022 3128291 := bstep (se 1 (by rfl) ⟨2346218, by rfl⟩ : syracuseStep 3128291 = 4692437) B4692437
theorem B9403469 : Blo 1646022 9403469 := bstep (se 3 (by rfl) ⟨1763150, by rfl⟩ : syracuseStep 9403469 = 3526301) B3526301
theorem B6020173 : Blo 1646022 6020173 := bstep (se 3 (by rfl) ⟨1128782, by rfl⟩ : syracuseStep 6020173 = 2257565) B2257565
theorem B5274737 : Blo 1646022 5274737 := bstep (se 2 (by rfl) ⟨1978026, by rfl⟩ : syracuseStep 5274737 = 3956053) B3956053
theorem B4168817 : Blo 1646022 4168817 := bstep (se 2 (by rfl) ⟨1563306, by rfl⟩ : syracuseStep 4168817 = 3126613) B3126613
theorem B13360241 : Blo 1646022 13360241 := bstep (se 2 (by rfl) ⟨5010090, by rfl⟩ : syracuseStep 13360241 = 10020181) B10020181
theorem B9378949 : Blo 1646022 9378949 := bstep (se 4 (by rfl) ⟨879276, by rfl⟩ : syracuseStep 9378949 = 1758553) B1758553
theorem B4168867 : Blo 1646022 4168867 := bstep (se 1 (by rfl) ⟨3126650, by rfl⟩ : syracuseStep 4168867 = 6253301) B6253301
theorem B4169009 : Blo 1646022 4169009 := bstep (se 2 (by rfl) ⟨1563378, by rfl⟩ : syracuseStep 4169009 = 3126757) B3126757
theorem B2637107 : Blo 1646022 2637107 := bstep (se 1 (by rfl) ⟨1977830, by rfl⟩ : syracuseStep 2637107 = 3955661) B3955661
theorem B14269765 : Blo 1646022 14269765 := bstep (se 4 (by rfl) ⟨1337790, by rfl⟩ : syracuseStep 14269765 = 2675581) B2675581
theorem B8338787 : Blo 1646022 8338787 := bstep (se 1 (by rfl) ⟨6254090, by rfl⟩ : syracuseStep 8338787 = 12508181) B12508181
theorem B6249869 : Blo 1646022 6249869 := bstep (se 3 (by rfl) ⟨1171850, by rfl⟩ : syracuseStep 6249869 = 2343701) B2343701
theorem B1646035 : Blo 1646022 1646035 := bstep (se 1 (by rfl) ⟨1234526, by rfl⟩ : syracuseStep 1646035 = 2469053) B2469053
theorem B1646051 : Blo 1646022 1646051 := bstep (se 1 (by rfl) ⟨1234538, by rfl⟩ : syracuseStep 1646051 = 2469077) B2469077
theorem B5561837 : Blo 1646022 5561837 := bstep (se 3 (by rfl) ⟨1042844, by rfl⟩ : syracuseStep 5561837 = 2085689) B2085689
theorem B1646067 : Blo 1646022 1646067 := bstep (se 1 (by rfl) ⟨1234550, by rfl⟩ : syracuseStep 1646067 = 2469101) B2469101
theorem B1646083 : Blo 1646022 1646083 := bstep (se 1 (by rfl) ⟨1234562, by rfl⟩ : syracuseStep 1646083 = 2469125) B2469125
theorem B1646099 : Blo 1646022 1646099 := bstep (se 1 (by rfl) ⟨1234574, by rfl⟩ : syracuseStep 1646099 = 2469149) B2469149
theorem B1646115 : Blo 1646022 1646115 := bstep (se 1 (by rfl) ⟨1234586, by rfl⟩ : syracuseStep 1646115 = 2469173) B2469173
theorem B5561891 : Blo 1646022 5561891 := bstep (se 1 (by rfl) ⟨4171418, by rfl⟩ : syracuseStep 5561891 = 8342837) B8342837
theorem B1646131 : Blo 1646022 1646131 := bstep (se 1 (by rfl) ⟨1234598, by rfl⟩ : syracuseStep 1646131 = 2469197) B2469197
theorem B1646147 : Blo 1646022 1646147 := bstep (se 1 (by rfl) ⟨1234610, by rfl⟩ : syracuseStep 1646147 = 2469221) B2469221
theorem B1646163 : Blo 1646022 1646163 := bstep (se 1 (by rfl) ⟨1234622, by rfl⟩ : syracuseStep 1646163 = 2469245) B2469245
theorem B1646179 : Blo 1646022 1646179 := bstep (se 1 (by rfl) ⟨1234634, by rfl⟩ : syracuseStep 1646179 = 2469269) B2469269
theorem B85532273 : Blo 1646022 85532273 := bstep (se 2 (by rfl) ⟨32074602, by rfl⟩ : syracuseStep 85532273 = 64149205) B64149205
theorem B1646195 : Blo 1646022 1646195 := bstep (se 1 (by rfl) ⟨1234646, by rfl⟩ : syracuseStep 1646195 = 2469293) B2469293
theorem B1646211 : Blo 1646022 1646211 := bstep (se 1 (by rfl) ⟨1234658, by rfl⟩ : syracuseStep 1646211 = 2469317) B2469317
theorem B16039565 : Blo 1646022 16039565 := bstep (se 3 (by rfl) ⟨3007418, by rfl⟩ : syracuseStep 16039565 = 6014837) B6014837
theorem B5275277 : Blo 1646022 5275277 := bstep (se 3 (by rfl) ⟨989114, by rfl⟩ : syracuseStep 5275277 = 1978229) B1978229
theorem B1646227 : Blo 1646022 1646227 := bstep (se 1 (by rfl) ⟨1234670, by rfl⟩ : syracuseStep 1646227 = 2469341) B2469341
theorem B1646243 : Blo 1646022 1646243 := bstep (se 1 (by rfl) ⟨1234682, by rfl⟩ : syracuseStep 1646243 = 2469365) B2469365
theorem B1646259 : Blo 1646022 1646259 := bstep (se 1 (by rfl) ⟨1234694, by rfl⟩ : syracuseStep 1646259 = 2469389) B2469389
theorem B1646275 : Blo 1646022 1646275 := bstep (se 1 (by rfl) ⟨1234706, by rfl⟩ : syracuseStep 1646275 = 2469413) B2469413
theorem B5635793 : Blo 1646022 5635793 := bstep (se 2 (by rfl) ⟨2113422, by rfl⟩ : syracuseStep 5635793 = 4226845) B4226845
theorem B1646291 : Blo 1646022 1646291 := bstep (se 1 (by rfl) ⟨1234718, by rfl⟩ : syracuseStep 1646291 = 2469437) B2469437
theorem B1646307 : Blo 1646022 1646307 := bstep (se 1 (by rfl) ⟨1234730, by rfl⟩ : syracuseStep 1646307 = 2469461) B2469461
theorem B1646323 : Blo 1646022 1646323 := bstep (se 1 (by rfl) ⟨1234742, by rfl⟩ : syracuseStep 1646323 = 2469485) B2469485
theorem B1646339 : Blo 1646022 1646339 := bstep (se 1 (by rfl) ⟨1234754, by rfl⟩ : syracuseStep 1646339 = 2469509) B2469509
theorem B1646355 : Blo 1646022 1646355 := bstep (se 1 (by rfl) ⟨1234766, by rfl⟩ : syracuseStep 1646355 = 2469533) B2469533
theorem B1646371 : Blo 1646022 1646371 := bstep (se 1 (by rfl) ⟨1234778, by rfl⟩ : syracuseStep 1646371 = 2469557) B2469557
theorem B1646387 : Blo 1646022 1646387 := bstep (se 1 (by rfl) ⟨1234790, by rfl⟩ : syracuseStep 1646387 = 2469581) B2469581
theorem B1646403 : Blo 1646022 1646403 := bstep (se 1 (by rfl) ⟨1234802, by rfl⟩ : syracuseStep 1646403 = 2469605) B2469605
theorem B1646419 : Blo 1646022 1646419 := bstep (se 1 (by rfl) ⟨1234814, by rfl⟩ : syracuseStep 1646419 = 2469629) B2469629
theorem B1646435 : Blo 1646022 1646435 := bstep (se 1 (by rfl) ⟨1234826, by rfl⟩ : syracuseStep 1646435 = 2469653) B2469653
theorem B1646451 : Blo 1646022 1646451 := bstep (se 1 (by rfl) ⟨1234838, by rfl⟩ : syracuseStep 1646451 = 2469677) B2469677
theorem B1646467 : Blo 1646022 1646467 := bstep (se 1 (by rfl) ⟨1234850, by rfl⟩ : syracuseStep 1646467 = 2469701) B2469701
theorem B1646483 : Blo 1646022 1646483 := bstep (se 1 (by rfl) ⟨1234862, by rfl⟩ : syracuseStep 1646483 = 2469725) B2469725
theorem B1646499 : Blo 1646022 1646499 := bstep (se 1 (by rfl) ⟨1234874, by rfl⟩ : syracuseStep 1646499 = 2469749) B2469749
theorem B1646515 : Blo 1646022 1646515 := bstep (se 1 (by rfl) ⟨1234886, by rfl⟩ : syracuseStep 1646515 = 2469773) B2469773
theorem B1646531 : Blo 1646022 1646531 := bstep (se 1 (by rfl) ⟨1234898, by rfl⟩ : syracuseStep 1646531 = 2469797) B2469797
theorem B1646547 : Blo 1646022 1646547 := bstep (se 1 (by rfl) ⟨1234910, by rfl⟩ : syracuseStep 1646547 = 2469821) B2469821
theorem B1646563 : Blo 1646022 1646563 := bstep (se 1 (by rfl) ⟨1234922, by rfl⟩ : syracuseStep 1646563 = 2469845) B2469845
theorem B1646579 : Blo 1646022 1646579 := bstep (se 1 (by rfl) ⟨1234934, by rfl⟩ : syracuseStep 1646579 = 2469869) B2469869
theorem B1646603 : Blo 1646022 1646603 := bstep (se 1 (by rfl) ⟨1234952, by rfl⟩ : syracuseStep 1646603 = 2469905) B2469905
theorem B1646615 : Blo 1646022 1646615 := bstep (se 1 (by rfl) ⟨1234961, by rfl⟩ : syracuseStep 1646615 = 2469923) B2469923
theorem B1646635 : Blo 1646022 1646635 := bstep (se 1 (by rfl) ⟨1234976, by rfl⟩ : syracuseStep 1646635 = 2469953) B2469953
theorem B1646647 : Blo 1646022 1646647 := bstep (se 1 (by rfl) ⟨1234985, by rfl⟩ : syracuseStep 1646647 = 2469971) B2469971
theorem B1646667 : Blo 1646022 1646667 := bstep (se 1 (by rfl) ⟨1235000, by rfl⟩ : syracuseStep 1646667 = 2470001) B2470001
theorem B1646679 : Blo 1646022 1646679 := bstep (se 1 (by rfl) ⟨1235009, by rfl⟩ : syracuseStep 1646679 = 2470019) B2470019
theorem B1646699 : Blo 1646022 1646699 := bstep (se 1 (by rfl) ⟨1235024, by rfl⟩ : syracuseStep 1646699 = 2470049) B2470049
theorem B213639281 : Blo 1646022 213639281 := bstep (se 2 (by rfl) ⟨80114730, by rfl⟩ : syracuseStep 213639281 = 160229461) B160229461
theorem B1646711 : Blo 1646022 1646711 := bstep (se 1 (by rfl) ⟨1235033, by rfl⟩ : syracuseStep 1646711 = 2470067) B2470067
theorem B1646731 : Blo 1646022 1646731 := bstep (se 1 (by rfl) ⟨1235048, by rfl⟩ : syracuseStep 1646731 = 2470097) B2470097
theorem B38011031 : Blo 1646022 38011031 := bstep (se 1 (by rfl) ⟨28508273, by rfl⟩ : syracuseStep 38011031 = 57016547) B57016547
theorem B1646743 : Blo 1646022 1646743 := bstep (se 1 (by rfl) ⟨1235057, by rfl⟩ : syracuseStep 1646743 = 2470115) B2470115
theorem B1646763 : Blo 1646022 1646763 := bstep (se 1 (by rfl) ⟨1235072, by rfl⟩ : syracuseStep 1646763 = 2470145) B2470145
theorem B1646775 : Blo 1646022 1646775 := bstep (se 1 (by rfl) ⟨1235081, by rfl⟩ : syracuseStep 1646775 = 2470163) B2470163
theorem B7512257 : Blo 1646022 7512257 := bstep (se 2 (by rfl) ⟨2817096, by rfl⟩ : syracuseStep 7512257 = 5634193) B5634193
theorem B2932939 : Blo 1646022 2932939 := bstep (se 1 (by rfl) ⟨2199704, by rfl⟩ : syracuseStep 2932939 = 4399409) B4399409
theorem B1646795 : Blo 1646022 1646795 := bstep (se 1 (by rfl) ⟨1235096, by rfl⟩ : syracuseStep 1646795 = 2470193) B2470193
theorem B1646807 : Blo 1646022 1646807 := bstep (se 1 (by rfl) ⟨1235105, by rfl⟩ : syracuseStep 1646807 = 2470211) B2470211
theorem B1646827 : Blo 1646022 1646827 := bstep (se 1 (by rfl) ⟨1235120, by rfl⟩ : syracuseStep 1646827 = 2470241) B2470241
theorem B1646839 : Blo 1646022 1646839 := bstep (se 1 (by rfl) ⟨1235129, by rfl⟩ : syracuseStep 1646839 = 2470259) B2470259
theorem B1646859 : Blo 1646022 1646859 := bstep (se 1 (by rfl) ⟨1235144, by rfl⟩ : syracuseStep 1646859 = 2470289) B2470289
theorem B1646871 : Blo 1646022 1646871 := bstep (se 1 (by rfl) ⟨1235153, by rfl⟩ : syracuseStep 1646871 = 2470307) B2470307
theorem B1646891 : Blo 1646022 1646891 := bstep (se 1 (by rfl) ⟨1235168, by rfl⟩ : syracuseStep 1646891 = 2470337) B2470337
theorem B35627309 : Blo 1646022 35627309 := bstep (se 3 (by rfl) ⟨6680120, by rfl⟩ : syracuseStep 35627309 = 13360241) B13360241
theorem B5275955 : Blo 1646022 5275955 := bstep (se 1 (by rfl) ⟨3956966, by rfl⟩ : syracuseStep 5275955 = 7913933) B7913933
theorem B1646903 : Blo 1646022 1646903 := bstep (se 1 (by rfl) ⟨1235177, by rfl⟩ : syracuseStep 1646903 = 2470355) B2470355
theorem B1646923 : Blo 1646022 1646923 := bstep (se 1 (by rfl) ⟨1235192, by rfl⟩ : syracuseStep 1646923 = 2470385) B2470385
theorem B1646935 : Blo 1646022 1646935 := bstep (se 1 (by rfl) ⟨1235201, by rfl⟩ : syracuseStep 1646935 = 2470403) B2470403
theorem B6250841 : Blo 1646022 6250841 := bstep (se 2 (by rfl) ⟨2344065, by rfl⟩ : syracuseStep 6250841 = 4688131) B4688131
theorem B1646955 : Blo 1646022 1646955 := bstep (se 1 (by rfl) ⟨1235216, by rfl⟩ : syracuseStep 1646955 = 2470433) B2470433
theorem B1646967 : Blo 1646022 1646967 := bstep (se 1 (by rfl) ⟨1235225, by rfl⟩ : syracuseStep 1646967 = 2470451) B2470451
theorem B1646987 : Blo 1646022 1646987 := bstep (se 1 (by rfl) ⟨1235240, by rfl⟩ : syracuseStep 1646987 = 2470481) B2470481
theorem B1851799 : Blo 1646022 1851799 := bstep (se 1 (by rfl) ⟨1388849, by rfl⟩ : syracuseStep 1851799 = 2777699) B2777699
theorem B1646999 : Blo 1646022 1646999 := bstep (se 1 (by rfl) ⟨1235249, by rfl⟩ : syracuseStep 1646999 = 2470499) B2470499
theorem B1647019 : Blo 1646022 1647019 := bstep (se 1 (by rfl) ⟨1235264, by rfl⟩ : syracuseStep 1647019 = 2470529) B2470529
theorem B4170163 : Blo 1646022 4170163 := bstep (se 1 (by rfl) ⟨3127622, by rfl⟩ : syracuseStep 4170163 = 6255245) B6255245
theorem B1647031 : Blo 1646022 1647031 := bstep (se 1 (by rfl) ⟨1235273, by rfl⟩ : syracuseStep 1647031 = 2470547) B2470547
theorem B1647051 : Blo 1646022 1647051 := bstep (se 1 (by rfl) ⟨1235288, by rfl⟩ : syracuseStep 1647051 = 2470577) B2470577
theorem B1647063 : Blo 1646022 1647063 := bstep (se 1 (by rfl) ⟨1235297, by rfl⟩ : syracuseStep 1647063 = 2470595) B2470595
theorem B5636573 : Blo 1646022 5636573 := bstep (se 3 (by rfl) ⟨1056857, by rfl⟩ : syracuseStep 5636573 = 2113715) B2113715
theorem B1647083 : Blo 1646022 1647083 := bstep (se 1 (by rfl) ⟨1235312, by rfl⟩ : syracuseStep 1647083 = 2470625) B2470625
theorem B1647095 : Blo 1646022 1647095 := bstep (se 1 (by rfl) ⟨1235321, by rfl⟩ : syracuseStep 1647095 = 2470643) B2470643
theorem B1647115 : Blo 1646022 1647115 := bstep (se 1 (by rfl) ⟨1235336, by rfl⟩ : syracuseStep 1647115 = 2470673) B2470673
theorem B1647127 : Blo 1646022 1647127 := bstep (se 1 (by rfl) ⟨1235345, by rfl⟩ : syracuseStep 1647127 = 2470691) B2470691
theorem B1647147 : Blo 1646022 1647147 := bstep (se 1 (by rfl) ⟨1235360, by rfl⟩ : syracuseStep 1647147 = 2470721) B2470721
theorem B6251053 : Blo 1646022 6251053 := bstep (se 3 (by rfl) ⟨1172072, by rfl⟩ : syracuseStep 6251053 = 2344145) B2344145
theorem B1647159 : Blo 1646022 1647159 := bstep (se 1 (by rfl) ⟨1235369, by rfl⟩ : syracuseStep 1647159 = 2470739) B2470739
theorem B4170305 : Blo 1646022 4170305 := bstep (se 2 (by rfl) ⟨1563864, by rfl⟩ : syracuseStep 4170305 = 3127729) B3127729
theorem B1851979 : Blo 1646022 1851979 := bstep (se 1 (by rfl) ⟨1388984, by rfl⟩ : syracuseStep 1851979 = 2777969) B2777969
theorem B1647179 : Blo 1646022 1647179 := bstep (se 1 (by rfl) ⟨1235384, by rfl⟩ : syracuseStep 1647179 = 2470769) B2470769
theorem B1647191 : Blo 1646022 1647191 := bstep (se 1 (by rfl) ⟨1235393, by rfl⟩ : syracuseStep 1647191 = 2470787) B2470787
theorem B60113501 : Blo 1646022 60113501 := bstep (se 3 (by rfl) ⟨11271281, by rfl⟩ : syracuseStep 60113501 = 22542563) B22542563
theorem B1647211 : Blo 1646022 1647211 := bstep (se 1 (by rfl) ⟨1235408, by rfl⟩ : syracuseStep 1647211 = 2470817) B2470817
theorem B1647223 : Blo 1646022 1647223 := bstep (se 1 (by rfl) ⟨1235417, by rfl⟩ : syracuseStep 1647223 = 2470835) B2470835
theorem B1647243 : Blo 1646022 1647243 := bstep (se 1 (by rfl) ⟨1235432, by rfl⟩ : syracuseStep 1647243 = 2470865) B2470865
theorem B1647255 : Blo 1646022 1647255 := bstep (se 1 (by rfl) ⟨1235441, by rfl⟩ : syracuseStep 1647255 = 2470883) B2470883
theorem B2777753 : Blo 1646022 2777753 := bstep (se 2 (by rfl) ⟨1041657, by rfl⟩ : syracuseStep 2777753 = 2083315) B2083315
theorem B1647275 : Blo 1646022 1647275 := bstep (se 1 (by rfl) ⟨1235456, by rfl⟩ : syracuseStep 1647275 = 2470913) B2470913
theorem B1852087 : Blo 1646022 1852087 := bstep (se 1 (by rfl) ⟨1389065, by rfl⟩ : syracuseStep 1852087 = 2778131) B2778131
theorem B1647287 : Blo 1646022 1647287 := bstep (se 1 (by rfl) ⟨1235465, by rfl⟩ : syracuseStep 1647287 = 2470931) B2470931
theorem B1647307 : Blo 1646022 1647307 := bstep (se 1 (by rfl) ⟨1235480, by rfl⟩ : syracuseStep 1647307 = 2470961) B2470961
theorem B1647319 : Blo 1646022 1647319 := bstep (se 1 (by rfl) ⟨1235489, by rfl⟩ : syracuseStep 1647319 = 2470979) B2470979
theorem B2966233 : Blo 1646022 2966233 := bstep (se 2 (by rfl) ⟨1112337, by rfl⟩ : syracuseStep 2966233 = 2224675) B2224675
theorem B5276377 : Blo 1646022 5276377 := bstep (se 2 (by rfl) ⟨1978641, by rfl⟩ : syracuseStep 5276377 = 3957283) B3957283
theorem B1647339 : Blo 1646022 1647339 := bstep (se 1 (by rfl) ⟨1235504, by rfl⟩ : syracuseStep 1647339 = 2471009) B2471009
theorem B1647351 : Blo 1646022 1647351 := bstep (se 1 (by rfl) ⟨1235513, by rfl⟩ : syracuseStep 1647351 = 2471027) B2471027
theorem B3703553 : Blo 1646022 3703553 := bstep (se 2 (by rfl) ⟨1388832, by rfl⟩ : syracuseStep 3703553 = 2777665) B2777665
theorem B1647371 : Blo 1646022 1647371 := bstep (se 1 (by rfl) ⟨1235528, by rfl⟩ : syracuseStep 1647371 = 2471057) B2471057
theorem B1647383 : Blo 1646022 1647383 := bstep (se 1 (by rfl) ⟨1235537, by rfl⟩ : syracuseStep 1647383 = 2471075) B2471075
theorem B2777881 : Blo 1646022 2777881 := bstep (se 2 (by rfl) ⟨1041705, by rfl⟩ : syracuseStep 2777881 = 2083411) B2083411
theorem B1647403 : Blo 1646022 1647403 := bstep (se 1 (by rfl) ⟨1235552, by rfl⟩ : syracuseStep 1647403 = 2471105) B2471105
theorem B1647415 : Blo 1646022 1647415 := bstep (se 1 (by rfl) ⟨1235561, by rfl⟩ : syracuseStep 1647415 = 2471123) B2471123
theorem B10552139 : Blo 1646022 10552139 := bstep (se 1 (by rfl) ⟨7914104, by rfl⟩ : syracuseStep 10552139 = 15828209) B15828209
theorem B1647435 : Blo 1646022 1647435 := bstep (se 1 (by rfl) ⟨1235576, by rfl⟩ : syracuseStep 1647435 = 2471153) B2471153
theorem B1647447 : Blo 1646022 1647447 := bstep (se 1 (by rfl) ⟨1235585, by rfl⟩ : syracuseStep 1647447 = 2471171) B2471171
theorem B2818903 : Blo 1646022 2818903 := bstep (se 1 (by rfl) ⟨2114177, by rfl⟩ : syracuseStep 2818903 = 4228355) B4228355
theorem B6251357 : Blo 1646022 6251357 := bstep (se 3 (by rfl) ⟨1172129, by rfl⟩ : syracuseStep 6251357 = 2344259) B2344259
theorem B1852267 : Blo 1646022 1852267 := bstep (se 1 (by rfl) ⟨1389200, by rfl⟩ : syracuseStep 1852267 = 2778401) B2778401
theorem B1647467 : Blo 1646022 1647467 := bstep (se 1 (by rfl) ⟨1235600, by rfl⟩ : syracuseStep 1647467 = 2471201) B2471201
theorem B1647479 : Blo 1646022 1647479 := bstep (se 1 (by rfl) ⟨1235609, by rfl⟩ : syracuseStep 1647479 = 2471219) B2471219
theorem B1647499 : Blo 1646022 1647499 := bstep (se 1 (by rfl) ⟨1235624, by rfl⟩ : syracuseStep 1647499 = 2471249) B2471249
theorem B1647511 : Blo 1646022 1647511 := bstep (se 1 (by rfl) ⟨1235633, by rfl⟩ : syracuseStep 1647511 = 2471267) B2471267
theorem B1647531 : Blo 1646022 1647531 := bstep (se 1 (by rfl) ⟨1235648, by rfl⟩ : syracuseStep 1647531 = 2471297) B2471297
theorem B1647543 : Blo 1646022 1647543 := bstep (se 1 (by rfl) ⟨1235657, by rfl⟩ : syracuseStep 1647543 = 2471315) B2471315
theorem B5276609 : Blo 1646022 5276609 := bstep (se 2 (by rfl) ⟨1978728, by rfl⟩ : syracuseStep 5276609 = 3957457) B3957457
theorem B1647563 : Blo 1646022 1647563 := bstep (se 1 (by rfl) ⟨1235672, by rfl⟩ : syracuseStep 1647563 = 2471345) B2471345
theorem B1852375 : Blo 1646022 1852375 := bstep (se 1 (by rfl) ⟨1389281, by rfl⟩ : syracuseStep 1852375 = 2778563) B2778563
theorem B1647575 : Blo 1646022 1647575 := bstep (se 1 (by rfl) ⟨1235681, by rfl⟩ : syracuseStep 1647575 = 2471363) B2471363
theorem B3703769 : Blo 1646022 3703769 := bstep (se 2 (by rfl) ⟨1388913, by rfl⟩ : syracuseStep 3703769 = 2777827) B2777827
theorem B1647595 : Blo 1646022 1647595 := bstep (se 1 (by rfl) ⟨1235696, by rfl⟩ : syracuseStep 1647595 = 2471393) B2471393
theorem B1647607 : Blo 1646022 1647607 := bstep (se 1 (by rfl) ⟨1235705, by rfl⟩ : syracuseStep 1647607 = 2471411) B2471411
theorem B1647627 : Blo 1646022 1647627 := bstep (se 1 (by rfl) ⟨1235720, by rfl⟩ : syracuseStep 1647627 = 2471441) B2471441
theorem B1647639 : Blo 1646022 1647639 := bstep (se 1 (by rfl) ⟨1235729, by rfl⟩ : syracuseStep 1647639 = 2471459) B2471459
theorem B67617827 : Blo 1646022 67617827 := bstep (se 1 (by rfl) ⟨50713370, by rfl⟩ : syracuseStep 67617827 = 101426741) B101426741
theorem B1647659 : Blo 1646022 1647659 := bstep (se 1 (by rfl) ⟨1235744, by rfl⟩ : syracuseStep 1647659 = 2471489) B2471489
theorem B3703859 : Blo 1646022 3703859 := bstep (se 1 (by rfl) ⟨2777894, by rfl⟩ : syracuseStep 3703859 = 5555789) B5555789
theorem B1647671 : Blo 1646022 1647671 := bstep (se 1 (by rfl) ⟨1235753, by rfl⟩ : syracuseStep 1647671 = 2471507) B2471507
theorem B23733323 : Blo 1646022 23733323 := bstep (se 1 (by rfl) ⟨17799992, by rfl⟩ : syracuseStep 23733323 = 35599985) B35599985
theorem B1647691 : Blo 1646022 1647691 := bstep (se 1 (by rfl) ⟨1235768, by rfl⟩ : syracuseStep 1647691 = 2471537) B2471537
theorem B3703895 : Blo 1646022 3703895 := bstep (se 1 (by rfl) ⟨2777921, by rfl⟩ : syracuseStep 3703895 = 5555843) B5555843
theorem B1647703 : Blo 1646022 1647703 := bstep (se 1 (by rfl) ⟨1235777, by rfl⟩ : syracuseStep 1647703 = 2471555) B2471555
theorem B1647723 : Blo 1646022 1647723 := bstep (se 1 (by rfl) ⟨1235792, by rfl⟩ : syracuseStep 1647723 = 2471585) B2471585
theorem B1647735 : Blo 1646022 1647735 := bstep (se 1 (by rfl) ⟨1235801, by rfl⟩ : syracuseStep 1647735 = 2471603) B2471603
theorem B15025283 : Blo 1646022 15025283 := bstep (se 1 (by rfl) ⟨11268962, by rfl⟩ : syracuseStep 15025283 = 22537925) B22537925
theorem B1852555 : Blo 1646022 1852555 := bstep (se 1 (by rfl) ⟨1389416, by rfl⟩ : syracuseStep 1852555 = 2778833) B2778833
theorem B1647755 : Blo 1646022 1647755 := bstep (se 1 (by rfl) ⟨1235816, by rfl⟩ : syracuseStep 1647755 = 2471633) B2471633
theorem B1647767 : Blo 1646022 1647767 := bstep (se 1 (by rfl) ⟨1235825, by rfl⟩ : syracuseStep 1647767 = 2471651) B2471651
theorem B1647787 : Blo 1646022 1647787 := bstep (se 1 (by rfl) ⟨1235840, by rfl⟩ : syracuseStep 1647787 = 2471681) B2471681
theorem B1647799 : Blo 1646022 1647799 := bstep (se 1 (by rfl) ⟨1235849, by rfl⟩ : syracuseStep 1647799 = 2471699) B2471699
theorem B1647819 : Blo 1646022 1647819 := bstep (se 1 (by rfl) ⟨1235864, by rfl⟩ : syracuseStep 1647819 = 2471729) B2471729
theorem B1647831 : Blo 1646022 1647831 := bstep (se 1 (by rfl) ⟨1235873, by rfl⟩ : syracuseStep 1647831 = 2471747) B2471747
theorem B1647851 : Blo 1646022 1647851 := bstep (se 1 (by rfl) ⟨1235888, by rfl⟩ : syracuseStep 1647851 = 2471777) B2471777
theorem B1852663 : Blo 1646022 1852663 := bstep (se 1 (by rfl) ⟨1389497, by rfl⟩ : syracuseStep 1852663 = 2778995) B2778995
theorem B1647863 : Blo 1646022 1647863 := bstep (se 1 (by rfl) ⟨1235897, by rfl⟩ : syracuseStep 1647863 = 2471795) B2471795
theorem B7038211 : Blo 1646022 7038211 := bstep (se 1 (by rfl) ⟨5278658, by rfl⟩ : syracuseStep 7038211 = 10557317) B10557317
theorem B3704075 : Blo 1646022 3704075 := bstep (se 1 (by rfl) ⟨2778056, by rfl⟩ : syracuseStep 3704075 = 5556113) B5556113
theorem B1647883 : Blo 1646022 1647883 := bstep (se 1 (by rfl) ⟨1235912, by rfl⟩ : syracuseStep 1647883 = 2471825) B2471825
theorem B3515671 : Blo 1646022 3515671 := bstep (se 1 (by rfl) ⟨2636753, by rfl⟩ : syracuseStep 3515671 = 5273507) B5273507
theorem B1647895 : Blo 1646022 1647895 := bstep (se 1 (by rfl) ⟨1235921, by rfl⟩ : syracuseStep 1647895 = 2471843) B2471843
theorem B1647915 : Blo 1646022 1647915 := bstep (se 1 (by rfl) ⟨1235936, by rfl⟩ : syracuseStep 1647915 = 2471873) B2471873
theorem B1647927 : Blo 1646022 1647927 := bstep (se 1 (by rfl) ⟨1235945, by rfl⟩ : syracuseStep 1647927 = 2471891) B2471891
theorem B3704129 : Blo 1646022 3704129 := bstep (se 2 (by rfl) ⟨1389048, by rfl⟩ : syracuseStep 3704129 = 2778097) B2778097
theorem B1647947 : Blo 1646022 1647947 := bstep (se 1 (by rfl) ⟨1235960, by rfl⟩ : syracuseStep 1647947 = 2471921) B2471921
theorem B2778455 : Blo 1646022 2778455 := bstep (se 1 (by rfl) ⟨2083841, by rfl⟩ : syracuseStep 2778455 = 4167683) B4167683
theorem B1647959 : Blo 1646022 1647959 := bstep (se 1 (by rfl) ⟨1235969, by rfl⟩ : syracuseStep 1647959 = 2471939) B2471939
theorem B1647979 : Blo 1646022 1647979 := bstep (se 1 (by rfl) ⟨1235984, by rfl⟩ : syracuseStep 1647979 = 2471969) B2471969
theorem B1647991 : Blo 1646022 1647991 := bstep (se 1 (by rfl) ⟨1235993, by rfl⟩ : syracuseStep 1647991 = 2471987) B2471987
theorem B1648011 : Blo 1646022 1648011 := bstep (se 1 (by rfl) ⟨1236008, by rfl⟩ : syracuseStep 1648011 = 2472017) B2472017
theorem B1852843 : Blo 1646022 1852843 := bstep (se 1 (by rfl) ⟨1389632, by rfl⟩ : syracuseStep 1852843 = 2779265) B2779265
theorem B15820211 : Blo 1646022 15820211 := bstep (se 1 (by rfl) ⟨11865158, by rfl⟩ : syracuseStep 15820211 = 23730317) B23730317
theorem B6342067 : Blo 1646022 6342067 := bstep (se 1 (by rfl) ⟨4756550, by rfl⟩ : syracuseStep 6342067 = 9513101) B9513101
theorem B2778583 : Blo 1646022 2778583 := bstep (se 1 (by rfl) ⟨2083937, by rfl⟩ : syracuseStep 2778583 = 4167875) B4167875
theorem B2344459 : Blo 1646022 2344459 := bstep (se 1 (by rfl) ⟨1758344, by rfl⟩ : syracuseStep 2344459 = 3516689) B3516689
theorem B5555735 : Blo 1646022 5555735 := bstep (se 1 (by rfl) ⟨4166801, by rfl⟩ : syracuseStep 5555735 = 8333603) B8333603
theorem B1852951 : Blo 1646022 1852951 := bstep (se 1 (by rfl) ⟨1389713, by rfl⟩ : syracuseStep 1852951 = 2779427) B2779427
theorem B3704345 : Blo 1646022 3704345 := bstep (se 2 (by rfl) ⟨1389129, by rfl⟩ : syracuseStep 3704345 = 2778259) B2778259
theorem B3704435 : Blo 1646022 3704435 := bstep (se 1 (by rfl) ⟨2778326, by rfl⟩ : syracuseStep 3704435 = 5556653) B5556653
theorem B3704471 : Blo 1646022 3704471 := bstep (se 1 (by rfl) ⟨2778353, by rfl⟩ : syracuseStep 3704471 = 5556707) B5556707
theorem B1853131 : Blo 1646022 1853131 := bstep (se 1 (by rfl) ⟨1389848, by rfl⟩ : syracuseStep 1853131 = 2779697) B2779697
theorem B1853239 : Blo 1646022 1853239 := bstep (se 1 (by rfl) ⟨1389929, by rfl⟩ : syracuseStep 1853239 = 2779859) B2779859
theorem B3704651 : Blo 1646022 3704651 := bstep (se 1 (by rfl) ⟨2778488, by rfl⟩ : syracuseStep 3704651 = 5556977) B5556977
theorem B3704705 : Blo 1646022 3704705 := bstep (se 2 (by rfl) ⟨1389264, by rfl⟩ : syracuseStep 3704705 = 2778529) B2778529
theorem B8341379 : Blo 1646022 8341379 := bstep (se 1 (by rfl) ⟨6256034, by rfl⟩ : syracuseStep 8341379 = 12512069) B12512069
theorem B10553267 : Blo 1646022 10553267 := bstep (se 1 (by rfl) ⟨7914950, by rfl⟩ : syracuseStep 10553267 = 15829901) B15829901
theorem B1853419 : Blo 1646022 1853419 := bstep (se 1 (by rfl) ⟨1390064, by rfl⟩ : syracuseStep 1853419 = 2780129) B2780129
theorem B5556275 : Blo 1646022 5556275 := bstep (se 1 (by rfl) ⟨4167206, by rfl⟩ : syracuseStep 5556275 = 8334413) B8334413
theorem B6268979 : Blo 1646022 6268979 := bstep (se 1 (by rfl) ⟨4701734, by rfl⟩ : syracuseStep 6268979 = 9403469) B9403469
theorem B2967617 : Blo 1646022 2967617 := bstep (se 2 (by rfl) ⟨1112856, by rfl⟩ : syracuseStep 2967617 = 2225713) B2225713
theorem B3516491 : Blo 1646022 3516491 := bstep (se 1 (by rfl) ⟨2637368, by rfl⟩ : syracuseStep 3516491 = 5274737) B5274737
theorem B2779211 : Blo 1646022 2779211 := bstep (se 1 (by rfl) ⟨2084408, by rfl⟩ : syracuseStep 2779211 = 4168817) B4168817
theorem B1853527 : Blo 1646022 1853527 := bstep (se 1 (by rfl) ⟨1390145, by rfl⟩ : syracuseStep 1853527 = 2780291) B2780291
theorem B3704921 : Blo 1646022 3704921 := bstep (se 2 (by rfl) ⟨1389345, by rfl⟩ : syracuseStep 3704921 = 2778691) B2778691
theorem B3705011 : Blo 1646022 3705011 := bstep (se 1 (by rfl) ⟨2778758, by rfl⟩ : syracuseStep 3705011 = 5557517) B5557517
theorem B7039169 : Blo 1646022 7039169 := bstep (se 2 (by rfl) ⟨2639688, by rfl⟩ : syracuseStep 7039169 = 5279377) B5279377
theorem B2779339 : Blo 1646022 2779339 := bstep (se 1 (by rfl) ⟨2084504, by rfl⟩ : syracuseStep 2779339 = 4169009) B4169009
theorem B2033867 : Blo 1646022 2033867 := bstep (se 1 (by rfl) ⟨1525400, by rfl⟩ : syracuseStep 2033867 = 3050801) B3050801
theorem B3705047 : Blo 1646022 3705047 := bstep (se 1 (by rfl) ⟨2778785, by rfl⟩ : syracuseStep 3705047 = 5557571) B5557571
theorem B1853707 : Blo 1646022 1853707 := bstep (se 1 (by rfl) ⟨1390280, by rfl⟩ : syracuseStep 1853707 = 2780561) B2780561
theorem B5556545 : Blo 1646022 5556545 := bstep (se 2 (by rfl) ⟨2083704, by rfl⟩ : syracuseStep 5556545 = 4167409) B4167409
theorem B2779481 : Blo 1646022 2779481 := bstep (se 2 (by rfl) ⟨1042305, by rfl⟩ : syracuseStep 2779481 = 2084611) B2084611
theorem B1853815 : Blo 1646022 1853815 := bstep (se 1 (by rfl) ⟨1390361, by rfl⟩ : syracuseStep 1853815 = 2780723) B2780723
theorem B3705227 : Blo 1646022 3705227 := bstep (se 1 (by rfl) ⟨2778920, by rfl⟩ : syracuseStep 3705227 = 5557841) B5557841
theorem B10693043 : Blo 1646022 10693043 := bstep (se 1 (by rfl) ⟨8019782, by rfl⟩ : syracuseStep 10693043 = 16039565) B16039565
theorem B3516851 : Blo 1646022 3516851 := bstep (se 1 (by rfl) ⟨2637638, by rfl⟩ : syracuseStep 3516851 = 5275277) B5275277
theorem B3705281 : Blo 1646022 3705281 := bstep (se 2 (by rfl) ⟨1389480, by rfl⟩ : syracuseStep 3705281 = 2778961) B2778961
theorem B2779609 : Blo 1646022 2779609 := bstep (se 2 (by rfl) ⟨1042353, by rfl⟩ : syracuseStep 2779609 = 2084707) B2084707
theorem B7129565 : Blo 1646022 7129565 := bstep (se 3 (by rfl) ⟨1336793, by rfl⟩ : syracuseStep 7129565 = 2673587) B2673587
theorem B1853995 : Blo 1646022 1853995 := bstep (se 1 (by rfl) ⟨1390496, by rfl⟩ : syracuseStep 1853995 = 2780993) B2780993
theorem B3705497 : Blo 1646022 3705497 := bstep (se 2 (by rfl) ⟨1389561, by rfl⟩ : syracuseStep 3705497 = 2779123) B2779123
theorem B18754253 : Blo 1646022 18754253 := bstep (se 3 (by rfl) ⟨3516422, by rfl⟩ : syracuseStep 18754253 = 7032845) B7032845
theorem B32082637 : Blo 1646022 32082637 := bstep (se 3 (by rfl) ⟨6015494, by rfl⟩ : syracuseStep 32082637 = 12030989) B12030989
theorem B2345689 : Blo 1646022 2345689 := bstep (se 2 (by rfl) ⟨879633, by rfl⟩ : syracuseStep 2345689 = 1759267) B1759267
theorem B3959513 : Blo 1646022 3959513 := bstep (se 2 (by rfl) ⟨1484817, by rfl⟩ : syracuseStep 3959513 = 2969635) B2969635
theorem B3705587 : Blo 1646022 3705587 := bstep (se 1 (by rfl) ⟨2779190, by rfl⟩ : syracuseStep 3705587 = 5558381) B5558381
theorem B13536017 : Blo 1646022 13536017 := bstep (se 2 (by rfl) ⟨5076006, by rfl⟩ : syracuseStep 13536017 = 10152013) B10152013
theorem B3705623 : Blo 1646022 3705623 := bstep (se 1 (by rfl) ⟨2779217, by rfl⟩ : syracuseStep 3705623 = 5558435) B5558435
theorem B5557085 : Blo 1646022 5557085 := bstep (se 3 (by rfl) ⟨1041953, by rfl⟩ : syracuseStep 5557085 = 2083907) B2083907
theorem B2083735 : Blo 1646022 2083735 := bstep (se 1 (by rfl) ⟨1562801, by rfl⟩ : syracuseStep 2083735 = 3125603) B3125603
theorem B3705803 : Blo 1646022 3705803 := bstep (se 1 (by rfl) ⟨2779352, by rfl⟩ : syracuseStep 3705803 = 5558705) B5558705
theorem B3337175 : Blo 1646022 3337175 := bstep (se 1 (by rfl) ⟨2502881, by rfl⟩ : syracuseStep 3337175 = 5005763) B5005763
theorem B3705857 : Blo 1646022 3705857 := bstep (se 2 (by rfl) ⟨1389696, by rfl⟩ : syracuseStep 3705857 = 2779393) B2779393
theorem B2780183 : Blo 1646022 2780183 := bstep (se 1 (by rfl) ⟨2085137, by rfl⟩ : syracuseStep 2780183 = 4170275) B4170275
theorem B7031873 : Blo 1646022 7031873 := bstep (se 2 (by rfl) ⟨2636952, by rfl⟩ : syracuseStep 7031873 = 5273905) B5273905
theorem B32107589 : Blo 1646022 32107589 := bstep (se 4 (by rfl) ⟨3010086, by rfl⟩ : syracuseStep 32107589 = 6020173) B6020173
theorem B8899735 : Blo 1646022 8899735 := bstep (se 1 (by rfl) ⟨6674801, by rfl⟩ : syracuseStep 8899735 = 13349603) B13349603
theorem B2780311 : Blo 1646022 2780311 := bstep (se 1 (by rfl) ⟨2085233, by rfl⟩ : syracuseStep 2780311 = 4170467) B4170467
theorem B7032025 : Blo 1646022 7032025 := bstep (se 2 (by rfl) ⟨2637009, by rfl⟩ : syracuseStep 7032025 = 5274019) B5274019
theorem B3706073 : Blo 1646022 3706073 := bstep (se 2 (by rfl) ⟨1389777, by rfl⟩ : syracuseStep 3706073 = 2779555) B2779555
theorem B2469131 : Blo 1646022 2469131 := bstep (se 1 (by rfl) ⟨1851848, by rfl⟩ : syracuseStep 2469131 = 3703697) B3703697
theorem B2469143 : Blo 1646022 2469143 := bstep (se 1 (by rfl) ⟨1851857, by rfl⟩ : syracuseStep 2469143 = 3703715) B3703715
theorem B3706163 : Blo 1646022 3706163 := bstep (se 1 (by rfl) ⟨2779622, by rfl⟩ : syracuseStep 3706163 = 5559245) B5559245
theorem B3706199 : Blo 1646022 3706199 := bstep (se 1 (by rfl) ⟨2779649, by rfl⟩ : syracuseStep 3706199 = 5559299) B5559299
theorem B2469209 : Blo 1646022 2469209 := bstep (se 2 (by rfl) ⟨925953, by rfl⟩ : syracuseStep 2469209 = 1851907) B1851907
theorem B5279069 : Blo 1646022 5279069 := bstep (se 3 (by rfl) ⟨989825, by rfl⟩ : syracuseStep 5279069 = 1979651) B1979651
theorem B3566963 : Blo 1646022 3566963 := bstep (se 1 (by rfl) ⟨2675222, by rfl⟩ : syracuseStep 3566963 = 5350445) B5350445
theorem B6253955 : Blo 1646022 6253955 := bstep (se 1 (by rfl) ⟨4690466, by rfl⟩ : syracuseStep 6253955 = 9380933) B9380933
theorem B6253969 : Blo 1646022 6253969 := bstep (se 2 (by rfl) ⟨2345238, by rfl⟩ : syracuseStep 6253969 = 4690477) B4690477
theorem B2469323 : Blo 1646022 2469323 := bstep (se 1 (by rfl) ⟨1851992, by rfl⟩ : syracuseStep 2469323 = 3703985) B3703985
theorem B2469335 : Blo 1646022 2469335 := bstep (se 1 (by rfl) ⟨1852001, by rfl⟩ : syracuseStep 2469335 = 3704003) B3704003
theorem B1977815 : Blo 1646022 1977815 := bstep (se 1 (by rfl) ⟨1483361, by rfl⟩ : syracuseStep 1977815 = 2966723) B2966723
theorem B4689373 : Blo 1646022 4689373 := bstep (se 3 (by rfl) ⟨879257, by rfl⟩ : syracuseStep 4689373 = 1758515) B1758515
theorem B3706379 : Blo 1646022 3706379 := bstep (se 1 (by rfl) ⟨2779784, by rfl⟩ : syracuseStep 3706379 = 5559569) B5559569
theorem B2469401 : Blo 1646022 2469401 := bstep (se 2 (by rfl) ⟨926025, by rfl⟩ : syracuseStep 2469401 = 1852051) B1852051
theorem B3706433 : Blo 1646022 3706433 := bstep (se 2 (by rfl) ⟨1389912, by rfl⟩ : syracuseStep 3706433 = 2779825) B2779825
theorem B2469515 : Blo 1646022 2469515 := bstep (se 1 (by rfl) ⟨1852136, by rfl⟩ : syracuseStep 2469515 = 3704273) B3704273
theorem B2469527 : Blo 1646022 2469527 := bstep (se 1 (by rfl) ⟨1852145, by rfl⟩ : syracuseStep 2469527 = 3704291) B3704291
theorem B3124889 : Blo 1646022 3124889 := bstep (se 2 (by rfl) ⟨1171833, by rfl⟩ : syracuseStep 3124889 = 2343667) B2343667
theorem B6254273 : Blo 1646022 6254273 := bstep (se 2 (by rfl) ⟨2345352, by rfl⟩ : syracuseStep 6254273 = 4690705) B4690705
theorem B2084555 : Blo 1646022 2084555 := bstep (se 1 (by rfl) ⟨1563416, by rfl⟩ : syracuseStep 2084555 = 3126833) B3126833
theorem B17805005 : Blo 1646022 17805005 := bstep (se 3 (by rfl) ⟨3338438, by rfl⟩ : syracuseStep 17805005 = 6676877) B6676877
theorem B2469593 : Blo 1646022 2469593 := bstep (se 2 (by rfl) ⟨926097, by rfl⟩ : syracuseStep 2469593 = 1852195) B1852195
theorem B3337985 : Blo 1646022 3337985 := bstep (se 2 (by rfl) ⟨1251744, by rfl⟩ : syracuseStep 3337985 = 2503489) B2503489
theorem B1978123 : Blo 1646022 1978123 := bstep (se 1 (by rfl) ⟨1483592, by rfl⟩ : syracuseStep 1978123 = 2967185) B2967185
theorem B2780939 : Blo 1646022 2780939 := bstep (se 1 (by rfl) ⟨2085704, by rfl⟩ : syracuseStep 2780939 = 4171409) B4171409
theorem B12513041 : Blo 1646022 12513041 := bstep (se 2 (by rfl) ⟨4692390, by rfl⟩ : syracuseStep 12513041 = 9384781) B9384781
theorem B3706649 : Blo 1646022 3706649 := bstep (se 2 (by rfl) ⟨1389993, by rfl⟩ : syracuseStep 3706649 = 2779987) B2779987
theorem B9375533 : Blo 1646022 9375533 := bstep (se 3 (by rfl) ⟨1757912, by rfl⟩ : syracuseStep 9375533 = 3515825) B3515825
theorem B2469707 : Blo 1646022 2469707 := bstep (se 1 (by rfl) ⟨1852280, by rfl⟩ : syracuseStep 2469707 = 3704561) B3704561
theorem B2469719 : Blo 1646022 2469719 := bstep (se 1 (by rfl) ⟨1852289, by rfl⟩ : syracuseStep 2469719 = 3704579) B3704579
theorem B3706739 : Blo 1646022 3706739 := bstep (se 1 (by rfl) ⟨2780054, by rfl⟩ : syracuseStep 3706739 = 5560109) B5560109
theorem B19009397 : Blo 1646022 19009397 := bstep (se 5 (by rfl) ⟨891065, by rfl⟩ : syracuseStep 19009397 = 1782131) B1782131
theorem B3706775 : Blo 1646022 3706775 := bstep (se 1 (by rfl) ⟨2780081, by rfl⟩ : syracuseStep 3706775 = 5560163) B5560163
theorem B2469785 : Blo 1646022 2469785 := bstep (se 2 (by rfl) ⟨926169, by rfl⟩ : syracuseStep 2469785 = 1852339) B1852339
theorem B5558219 : Blo 1646022 5558219 := bstep (se 1 (by rfl) ⟨4168664, by rfl⟩ : syracuseStep 5558219 = 8337329) B8337329
theorem B2469899 : Blo 1646022 2469899 := bstep (se 1 (by rfl) ⟨1852424, by rfl⟩ : syracuseStep 2469899 = 3704849) B3704849
theorem B2469911 : Blo 1646022 2469911 := bstep (se 1 (by rfl) ⟨1852433, by rfl⟩ : syracuseStep 2469911 = 3704867) B3704867
theorem B3125299 : Blo 1646022 3125299 := bstep (se 1 (by rfl) ⟨2343974, by rfl⟩ : syracuseStep 3125299 = 4687949) B4687949
theorem B3706955 : Blo 1646022 3706955 := bstep (se 1 (by rfl) ⟨2780216, by rfl⟩ : syracuseStep 3706955 = 5560433) B5560433
theorem B3338327 : Blo 1646022 3338327 := bstep (se 1 (by rfl) ⟨2503745, by rfl⟩ : syracuseStep 3338327 = 5007491) B5007491
theorem B2469977 : Blo 1646022 2469977 := bstep (se 2 (by rfl) ⟨926241, by rfl⟩ : syracuseStep 2469977 = 1852483) B1852483
theorem B14069861 : Blo 1646022 14069861 := bstep (se 4 (by rfl) ⟨1319049, by rfl⟩ : syracuseStep 14069861 = 2638099) B2638099
theorem B3707009 : Blo 1646022 3707009 := bstep (se 2 (by rfl) ⟨1390128, by rfl⟩ : syracuseStep 3707009 = 2780257) B2780257
theorem B12505265 : Blo 1646022 12505265 := bstep (se 2 (by rfl) ⟨4689474, by rfl⟩ : syracuseStep 12505265 = 9378949) B9378949
theorem B2470091 : Blo 1646022 2470091 := bstep (se 1 (by rfl) ⟨1852568, by rfl⟩ : syracuseStep 2470091 = 3705137) B3705137
theorem B2470103 : Blo 1646022 2470103 := bstep (se 1 (by rfl) ⟨1852577, by rfl⟩ : syracuseStep 2470103 = 3705155) B3705155
theorem B5558489 : Blo 1646022 5558489 := bstep (se 2 (by rfl) ⟨2084433, by rfl⟩ : syracuseStep 5558489 = 4168867) B4168867
theorem B2470169 : Blo 1646022 2470169 := bstep (se 2 (by rfl) ⟨926313, by rfl⟩ : syracuseStep 2470169 = 1852627) B1852627
theorem B3707225 : Blo 1646022 3707225 := bstep (se 2 (by rfl) ⟨1390209, by rfl⟩ : syracuseStep 3707225 = 2780419) B2780419
theorem B8335709 : Blo 1646022 8335709 := bstep (se 3 (by rfl) ⟨1562945, by rfl⟩ : syracuseStep 8335709 = 3125891) B3125891
theorem B6254941 : Blo 1646022 6254941 := bstep (se 3 (by rfl) ⟨1172801, by rfl⟩ : syracuseStep 6254941 = 2345603) B2345603
theorem B3518849 : Blo 1646022 3518849 := bstep (se 2 (by rfl) ⟨1319568, by rfl⟩ : syracuseStep 3518849 = 2639137) B2639137
theorem B2470283 : Blo 1646022 2470283 := bstep (se 1 (by rfl) ⟨1852712, by rfl⟩ : syracuseStep 2470283 = 3705425) B3705425
theorem B2085259 : Blo 1646022 2085259 := bstep (se 1 (by rfl) ⟨1563944, by rfl⟩ : syracuseStep 2085259 = 3127889) B3127889
theorem B2470295 : Blo 1646022 2470295 := bstep (se 1 (by rfl) ⟨1852721, by rfl⟩ : syracuseStep 2470295 = 3705443) B3705443
theorem B19026353 : Blo 1646022 19026353 := bstep (se 2 (by rfl) ⟨7134882, by rfl⟩ : syracuseStep 19026353 = 14269765) B14269765
theorem B3707315 : Blo 1646022 3707315 := bstep (se 1 (by rfl) ⟨2780486, by rfl⟩ : syracuseStep 3707315 = 5560973) B5560973
theorem B3707351 : Blo 1646022 3707351 := bstep (se 1 (by rfl) ⟨2780513, by rfl⟩ : syracuseStep 3707351 = 5561027) B5561027
theorem B2470361 : Blo 1646022 2470361 := bstep (se 2 (by rfl) ⟨926385, by rfl⟩ : syracuseStep 2470361 = 1852771) B1852771
theorem B4452887 : Blo 1646022 4452887 := bstep (se 1 (by rfl) ⟨3339665, by rfl⟩ : syracuseStep 4452887 = 6679331) B6679331
theorem B3125785 : Blo 1646022 3125785 := bstep (se 2 (by rfl) ⟨1172169, by rfl⟩ : syracuseStep 3125785 = 2344339) B2344339
theorem B2470475 : Blo 1646022 2470475 := bstep (se 1 (by rfl) ⟨1852856, by rfl⟩ : syracuseStep 2470475 = 3705713) B3705713
theorem B2470487 : Blo 1646022 2470487 := bstep (se 1 (by rfl) ⟨1852865, by rfl⟩ : syracuseStep 2470487 = 3705731) B3705731
theorem B55644803 : Blo 1646022 55644803 := bstep (se 1 (by rfl) ⟨41733602, by rfl⟩ : syracuseStep 55644803 = 83467205) B83467205
theorem B3707531 : Blo 1646022 3707531 := bstep (se 1 (by rfl) ⟨2780648, by rfl⟩ : syracuseStep 3707531 = 5561297) B5561297
theorem B12505751 : Blo 1646022 12505751 := bstep (se 1 (by rfl) ⟨9379313, by rfl⟩ : syracuseStep 12505751 = 18758627) B18758627
theorem B9384599 : Blo 1646022 9384599 := bstep (se 1 (by rfl) ⟨7038449, by rfl⟩ : syracuseStep 9384599 = 14076899) B14076899
theorem B2470553 : Blo 1646022 2470553 := bstep (se 2 (by rfl) ⟨926457, by rfl⟩ : syracuseStep 2470553 = 1852915) B1852915
theorem B2085527 : Blo 1646022 2085527 := bstep (se 1 (by rfl) ⟨1564145, by rfl⟩ : syracuseStep 2085527 = 3128291) B3128291
theorem B3707585 : Blo 1646022 3707585 := bstep (se 2 (by rfl) ⟨1390344, by rfl⟩ : syracuseStep 3707585 = 2780689) B2780689
theorem B4690649 : Blo 1646022 4690649 := bstep (se 2 (by rfl) ⟨1758993, by rfl⟩ : syracuseStep 4690649 = 3517987) B3517987
theorem B2470667 : Blo 1646022 2470667 := bstep (se 1 (by rfl) ⟨1853000, by rfl⟩ : syracuseStep 2470667 = 3706001) B3706001
theorem B2470679 : Blo 1646022 2470679 := bstep (se 1 (by rfl) ⟨1853009, by rfl⟩ : syracuseStep 2470679 = 3706019) B3706019
theorem B5075777 : Blo 1646022 5075777 := bstep (se 2 (by rfl) ⟨1903416, by rfl⟩ : syracuseStep 5075777 = 3806833) B3806833
theorem B6681419 : Blo 1646022 6681419 := bstep (se 1 (by rfl) ⟨5011064, by rfl⟩ : syracuseStep 6681419 = 10022129) B10022129
theorem B2470745 : Blo 1646022 2470745 := bstep (se 2 (by rfl) ⟨926529, by rfl⟩ : syracuseStep 2470745 = 1853059) B1853059
theorem B16896869 : Blo 1646022 16896869 := bstep (se 4 (by rfl) ⟨1584081, by rfl⟩ : syracuseStep 16896869 = 3168163) B3168163
theorem B1758071 : Blo 1646022 1758071 := bstep (se 1 (by rfl) ⟨1318553, by rfl⟩ : syracuseStep 1758071 = 2637107) B2637107
theorem B5559191 : Blo 1646022 5559191 := bstep (se 1 (by rfl) ⟨4169393, by rfl⟩ : syracuseStep 5559191 = 8338787) B8338787
theorem B3707801 : Blo 1646022 3707801 := bstep (se 2 (by rfl) ⟨1390425, by rfl⟩ : syracuseStep 3707801 = 2780851) B2780851
theorem B4166579 : Blo 1646022 4166579 := bstep (se 1 (by rfl) ⟨3124934, by rfl⟩ : syracuseStep 4166579 = 6249869) B6249869
theorem B2470859 : Blo 1646022 2470859 := bstep (se 1 (by rfl) ⟨1853144, by rfl⟩ : syracuseStep 2470859 = 3706289) B3706289
theorem B2470871 : Blo 1646022 2470871 := bstep (se 1 (by rfl) ⟨1853153, by rfl⟩ : syracuseStep 2470871 = 3706307) B3706307
theorem B9024473 : Blo 1646022 9024473 := bstep (se 2 (by rfl) ⟨3384177, by rfl⟩ : syracuseStep 9024473 = 6768355) B6768355
theorem B3707891 : Blo 1646022 3707891 := bstep (se 1 (by rfl) ⟨2780918, by rfl⟩ : syracuseStep 3707891 = 5561837) B5561837
theorem B3707927 : Blo 1646022 3707927 := bstep (se 1 (by rfl) ⟨2780945, by rfl⟩ : syracuseStep 3707927 = 5561891) B5561891
theorem B2470937 : Blo 1646022 2470937 := bstep (se 2 (by rfl) ⟨926601, by rfl⟩ : syracuseStep 2470937 = 1853203) B1853203
theorem B57021515 : Blo 1646022 57021515 := bstep (se 1 (by rfl) ⟨42766136, by rfl⟩ : syracuseStep 57021515 = 85532273) B85532273
theorem B3126347 : Blo 1646022 3126347 := bstep (se 1 (by rfl) ⟨2344760, by rfl⟩ : syracuseStep 3126347 = 4689521) B4689521
theorem B2471051 : Blo 1646022 2471051 := bstep (se 1 (by rfl) ⟨1853288, by rfl⟩ : syracuseStep 2471051 = 3706577) B3706577
theorem B3757195 : Blo 1646022 3757195 := bstep (se 1 (by rfl) ⟨2817896, by rfl⟩ : syracuseStep 3757195 = 5635793) B5635793
theorem B2471063 : Blo 1646022 2471063 := bstep (se 1 (by rfl) ⟨1853297, by rfl⟩ : syracuseStep 2471063 = 3706595) B3706595
theorem B3519703 : Blo 1646022 3519703 := bstep (se 1 (by rfl) ⟨2639777, by rfl⟩ : syracuseStep 3519703 = 5279555) B5279555
theorem B4166873 : Blo 1646022 4166873 := bstep (se 2 (by rfl) ⟨1562577, by rfl⟩ : syracuseStep 4166873 = 3125155) B3125155
theorem B2471129 : Blo 1646022 2471129 := bstep (se 2 (by rfl) ⟨926673, by rfl⟩ : syracuseStep 2471129 = 1853347) B1853347
theorem B1783031 : Blo 1646022 1783031 := bstep (se 1 (by rfl) ⟨1337273, by rfl⟩ : syracuseStep 1783031 = 2674547) B2674547
theorem B3126529 : Blo 1646022 3126529 := bstep (se 2 (by rfl) ⟨1172448, by rfl⟩ : syracuseStep 3126529 = 2344897) B2344897
theorem B1783063 : Blo 1646022 1783063 := bstep (se 1 (by rfl) ⟨1337297, by rfl⟩ : syracuseStep 1783063 = 2674595) B2674595
theorem B2471243 : Blo 1646022 2471243 := bstep (se 1 (by rfl) ⟨1853432, by rfl⟩ : syracuseStep 2471243 = 3706865) B3706865
theorem B2471255 : Blo 1646022 2471255 := bstep (se 1 (by rfl) ⟨1853441, by rfl⟩ : syracuseStep 2471255 = 3706883) B3706883
theorem B2225497 : Blo 1646022 2225497 := bstep (se 2 (by rfl) ⟨834561, by rfl⟩ : syracuseStep 2225497 = 1669123) B1669123
theorem B4011353 : Blo 1646022 4011353 := bstep (se 2 (by rfl) ⟨1504257, by rfl⟩ : syracuseStep 4011353 = 3008515) B3008515
theorem B3339671 : Blo 1646022 3339671 := bstep (se 1 (by rfl) ⟨2504753, by rfl⟩ : syracuseStep 3339671 = 5009507) B5009507
theorem B2225561 : Blo 1646022 2225561 := bstep (se 2 (by rfl) ⟨834585, by rfl⟩ : syracuseStep 2225561 = 1669171) B1669171
theorem B2471321 : Blo 1646022 2471321 := bstep (se 2 (by rfl) ⟨926745, by rfl⟩ : syracuseStep 2471321 = 1853491) B1853491
theorem B5559731 : Blo 1646022 5559731 := bstep (se 1 (by rfl) ⟨4169798, by rfl⟩ : syracuseStep 5559731 = 8339597) B8339597
theorem B2471435 : Blo 1646022 2471435 := bstep (se 1 (by rfl) ⟨1853576, by rfl⟩ : syracuseStep 2471435 = 3707153) B3707153
theorem B2471447 : Blo 1646022 2471447 := bstep (se 1 (by rfl) ⟨1853585, by rfl⟩ : syracuseStep 2471447 = 3707171) B3707171
theorem B3757643 : Blo 1646022 3757643 := bstep (se 1 (by rfl) ⟨2818232, by rfl⟩ : syracuseStep 3757643 = 5636465) B5636465
theorem B2471513 : Blo 1646022 2471513 := bstep (se 2 (by rfl) ⟨926817, by rfl⟩ : syracuseStep 2471513 = 1853635) B1853635
theorem B6256217 : Blo 1646022 6256217 := bstep (se 2 (by rfl) ⟨2346081, by rfl⟩ : syracuseStep 6256217 = 4692163) B4692163
theorem B5560001 : Blo 1646022 5560001 := bstep (se 2 (by rfl) ⟨2085000, by rfl⟩ : syracuseStep 5560001 = 4170001) B4170001
theorem B2471627 : Blo 1646022 2471627 := bstep (se 1 (by rfl) ⟨1853720, by rfl⟩ : syracuseStep 2471627 = 3707441) B3707441
theorem B2471639 : Blo 1646022 2471639 := bstep (se 1 (by rfl) ⟨1853729, by rfl⟩ : syracuseStep 2471639 = 3707459) B3707459
theorem B2471705 : Blo 1646022 2471705 := bstep (se 2 (by rfl) ⟨926889, by rfl⟩ : syracuseStep 2471705 = 1853779) B1853779
theorem B2471819 : Blo 1646022 2471819 := bstep (se 1 (by rfl) ⟨1853864, by rfl⟩ : syracuseStep 2471819 = 3707729) B3707729
theorem B5273495 : Blo 1646022 5273495 := bstep (se 1 (by rfl) ⟨3955121, by rfl⟩ : syracuseStep 5273495 = 7910243) B7910243
theorem B2471831 : Blo 1646022 2471831 := bstep (se 1 (by rfl) ⟨1853873, by rfl⟩ : syracuseStep 2471831 = 3707747) B3707747
theorem B3127243 : Blo 1646022 3127243 := bstep (se 1 (by rfl) ⟨2345432, by rfl⟩ : syracuseStep 3127243 = 4690865) B4690865
theorem B2471897 : Blo 1646022 2471897 := bstep (se 2 (by rfl) ⟨926961, by rfl⟩ : syracuseStep 2471897 = 1853923) B1853923
theorem B3127319 : Blo 1646022 3127319 := bstep (se 1 (by rfl) ⟨2345489, by rfl⟩ : syracuseStep 3127319 = 4690979) B4690979
theorem B24074309 : Blo 1646022 24074309 := bstep (se 4 (by rfl) ⟨2256966, by rfl⟩ : syracuseStep 24074309 = 4513933) B4513933
theorem B2472011 : Blo 1646022 2472011 := bstep (se 1 (by rfl) ⟨1854008, by rfl⟩ : syracuseStep 2472011 = 3708017) B3708017
theorem B2472023 : Blo 1646022 2472023 := bstep (se 1 (by rfl) ⟨1854017, by rfl⟩ : syracuseStep 2472023 = 3708035) B3708035
theorem B18765917 : Blo 1646022 18765917 := bstep (se 3 (by rfl) ⟨3518609, by rfl⟩ : syracuseStep 18765917 = 7037219) B7037219
theorem B1759339 : Blo 1646022 1759339 := bstep (se 1 (by rfl) ⟨1319504, by rfl⟩ : syracuseStep 1759339 = 2639009) B2639009
theorem B5560541 : Blo 1646022 5560541 := bstep (se 3 (by rfl) ⟨1042601, by rfl⟩ : syracuseStep 5560541 = 2085203) B2085203
theorem B5937425 : Blo 1646022 5937425 := bstep (se 2 (by rfl) ⟨2226534, by rfl⟩ : syracuseStep 5937425 = 4453069) B4453069
theorem B4692289 : Blo 1646022 4692289 := bstep (se 2 (by rfl) ⟨1759608, by rfl⟩ : syracuseStep 4692289 = 3519217) B3519217
theorem B36108661 : Blo 1646022 36108661 := bstep (se 5 (by rfl) ⟨1692593, by rfl⟩ : syracuseStep 36108661 = 3385187) B3385187
theorem B8337815 : Blo 1646022 8337815 := bstep (se 1 (by rfl) ⟨6253361, by rfl⟩ : syracuseStep 8337815 = 12506723) B12506723
theorem B7035443 : Blo 1646022 7035443 := bstep (se 1 (by rfl) ⟨5276582, by rfl⟩ : syracuseStep 7035443 = 10553165) B10553165
theorem B15022685 : Blo 1646022 15022685 := bstep (se 3 (by rfl) ⟨2816753, by rfl⟩ : syracuseStep 15022685 = 5633507) B5633507
theorem B3127987 : Blo 1646022 3127987 := bstep (se 1 (by rfl) ⟨2345990, by rfl⟩ : syracuseStep 3127987 = 4691981) B4691981
theorem B14072525 : Blo 1646022 14072525 := bstep (se 3 (by rfl) ⟨2638598, by rfl⟩ : syracuseStep 14072525 = 5277197) B5277197
theorem B4168523 : Blo 1646022 4168523 := bstep (se 1 (by rfl) ⟨3126392, by rfl⟩ : syracuseStep 4168523 = 6252785) B6252785
theorem B3128215 : Blo 1646022 3128215 := bstep (se 1 (by rfl) ⟨2346161, by rfl⟩ : syracuseStep 3128215 = 4692323) B4692323
theorem B3808243 : Blo 1646022 3808243 := bstep (se 1 (by rfl) ⟨2856182, by rfl⟩ : syracuseStep 3808243 = 5712365) B5712365
theorem B3128321 : Blo 1646022 3128321 := bstep (se 2 (by rfl) ⟨1173120, by rfl⟩ : syracuseStep 3128321 = 2346241) B2346241
theorem B2006155 : Blo 1646022 2006155 := bstep (se 1 (by rfl) ⟨1504616, by rfl⟩ : syracuseStep 2006155 = 3009233) B3009233
theorem B3128473 : Blo 1646022 3128473 := bstep (se 2 (by rfl) ⟨1173177, by rfl⟩ : syracuseStep 3128473 = 2346355) B2346355
theorem B3955891 : Blo 1646022 3955891 := bstep (se 1 (by rfl) ⟨2966918, by rfl⟩ : syracuseStep 3955891 = 5933837) B5933837
theorem B5938379 : Blo 1646022 5938379 := bstep (se 1 (by rfl) ⟨4453784, by rfl⟩ : syracuseStep 5938379 = 8907569) B8907569
theorem B7912721 : Blo 1646022 7912721 := bstep (se 2 (by rfl) ⟨2967270, by rfl⟩ : syracuseStep 7912721 = 5934541) B5934541
theorem B5561675 : Blo 1646022 5561675 := bstep (se 1 (by rfl) ⟨4171256, by rfl⟩ : syracuseStep 5561675 = 8342513) B8342513
theorem B5938577 : Blo 1646022 5938577 := bstep (se 2 (by rfl) ⟨2226966, by rfl⟩ : syracuseStep 5938577 = 4453933) B4453933
theorem B9379223 : Blo 1646022 9379223 := bstep (se 1 (by rfl) ⟨7034417, by rfl⟩ : syracuseStep 9379223 = 14068835) B14068835
theorem B1646027 : Blo 1646022 1646027 := bstep (se 1 (by rfl) ⟨1234520, by rfl⟩ : syracuseStep 1646027 = 2469041) B2469041
theorem B1646039 : Blo 1646022 1646039 := bstep (se 1 (by rfl) ⟨1234529, by rfl⟩ : syracuseStep 1646039 = 2469059) B2469059
theorem B1646059 : Blo 1646022 1646059 := bstep (se 1 (by rfl) ⟨1234544, by rfl⟩ : syracuseStep 1646059 = 2469089) B2469089
theorem B1646071 : Blo 1646022 1646071 := bstep (se 1 (by rfl) ⟨1234553, by rfl⟩ : syracuseStep 1646071 = 2469107) B2469107
theorem B1646091 : Blo 1646022 1646091 := bstep (se 1 (by rfl) ⟨1234568, by rfl⟩ : syracuseStep 1646091 = 2469137) B2469137
theorem B1646103 : Blo 1646022 1646103 := bstep (se 1 (by rfl) ⟨1234577, by rfl⟩ : syracuseStep 1646103 = 2469155) B2469155
theorem B1646123 : Blo 1646022 1646123 := bstep (se 1 (by rfl) ⟨1234592, by rfl⟩ : syracuseStep 1646123 = 2469185) B2469185
theorem B1646135 : Blo 1646022 1646135 := bstep (se 1 (by rfl) ⟨1234601, by rfl⟩ : syracuseStep 1646135 = 2469203) B2469203
theorem B1646155 : Blo 1646022 1646155 := bstep (se 1 (by rfl) ⟨1234616, by rfl⟩ : syracuseStep 1646155 = 2469233) B2469233
theorem B1646167 : Blo 1646022 1646167 := bstep (se 1 (by rfl) ⟨1234625, by rfl⟩ : syracuseStep 1646167 = 2469251) B2469251
theorem B5561945 : Blo 1646022 5561945 := bstep (se 2 (by rfl) ⟨2085729, by rfl⟩ : syracuseStep 5561945 = 4171459) B4171459
theorem B1646187 : Blo 1646022 1646187 := bstep (se 1 (by rfl) ⟨1234640, by rfl⟩ : syracuseStep 1646187 = 2469281) B2469281
theorem B1646199 : Blo 1646022 1646199 := bstep (se 1 (by rfl) ⟨1234649, by rfl⟩ : syracuseStep 1646199 = 2469299) B2469299
theorem B1646219 : Blo 1646022 1646219 := bstep (se 1 (by rfl) ⟨1234664, by rfl⟩ : syracuseStep 1646219 = 2469329) B2469329
theorem B1646231 : Blo 1646022 1646231 := bstep (se 1 (by rfl) ⟨1234673, by rfl⟩ : syracuseStep 1646231 = 2469347) B2469347
theorem B1646251 : Blo 1646022 1646251 := bstep (se 1 (by rfl) ⟨1234688, by rfl⟩ : syracuseStep 1646251 = 2469377) B2469377
theorem B1646263 : Blo 1646022 1646263 := bstep (se 1 (by rfl) ⟨1234697, by rfl⟩ : syracuseStep 1646263 = 2469395) B2469395
theorem B1646283 : Blo 1646022 1646283 := bstep (se 1 (by rfl) ⟨1234712, by rfl⟩ : syracuseStep 1646283 = 2469425) B2469425
theorem B1646295 : Blo 1646022 1646295 := bstep (se 1 (by rfl) ⟨1234721, by rfl⟩ : syracuseStep 1646295 = 2469443) B2469443
theorem B1646315 : Blo 1646022 1646315 := bstep (se 1 (by rfl) ⟨1234736, by rfl⟩ : syracuseStep 1646315 = 2469473) B2469473
theorem B1646327 : Blo 1646022 1646327 := bstep (se 1 (by rfl) ⟨1234745, by rfl⟩ : syracuseStep 1646327 = 2469491) B2469491
theorem B1646347 : Blo 1646022 1646347 := bstep (se 1 (by rfl) ⟨1234760, by rfl⟩ : syracuseStep 1646347 = 2469521) B2469521
theorem B1646359 : Blo 1646022 1646359 := bstep (se 1 (by rfl) ⟨1234769, by rfl⟩ : syracuseStep 1646359 = 2469539) B2469539
theorem B4169495 : Blo 1646022 4169495 := bstep (se 1 (by rfl) ⟨3127121, by rfl⟩ : syracuseStep 4169495 = 6254243) B6254243
theorem B1646379 : Blo 1646022 1646379 := bstep (se 1 (by rfl) ⟨1234784, by rfl⟩ : syracuseStep 1646379 = 2469569) B2469569
theorem B1646391 : Blo 1646022 1646391 := bstep (se 1 (by rfl) ⟨1234793, by rfl⟩ : syracuseStep 1646391 = 2469587) B2469587
theorem B1646411 : Blo 1646022 1646411 := bstep (se 1 (by rfl) ⟨1234808, by rfl⟩ : syracuseStep 1646411 = 2469617) B2469617
theorem B1646423 : Blo 1646022 1646423 := bstep (se 1 (by rfl) ⟨1234817, by rfl⟩ : syracuseStep 1646423 = 2469635) B2469635
theorem B1646443 : Blo 1646022 1646443 := bstep (se 1 (by rfl) ⟨1234832, by rfl⟩ : syracuseStep 1646443 = 2469665) B2469665
theorem B1646455 : Blo 1646022 1646455 := bstep (se 1 (by rfl) ⟨1234841, by rfl⟩ : syracuseStep 1646455 = 2469683) B2469683
theorem B1646475 : Blo 1646022 1646475 := bstep (se 1 (by rfl) ⟨1234856, by rfl⟩ : syracuseStep 1646475 = 2469713) B2469713
theorem B6250385 : Blo 1646022 6250385 := bstep (se 2 (by rfl) ⟨2343894, by rfl⟩ : syracuseStep 6250385 = 4687789) B4687789
theorem B1646487 : Blo 1646022 1646487 := bstep (se 1 (by rfl) ⟨1234865, by rfl⟩ : syracuseStep 1646487 = 2469731) B2469731
theorem B1646507 : Blo 1646022 1646507 := bstep (se 1 (by rfl) ⟨1234880, by rfl⟩ : syracuseStep 1646507 = 2469761) B2469761
theorem B1646519 : Blo 1646022 1646519 := bstep (se 1 (by rfl) ⟨1234889, by rfl⟩ : syracuseStep 1646519 = 2469779) B2469779
theorem B1646539 : Blo 1646022 1646539 := bstep (se 1 (by rfl) ⟨1234904, by rfl⟩ : syracuseStep 1646539 = 2469809) B2469809
theorem B1646551 : Blo 1646022 1646551 := bstep (se 1 (by rfl) ⟨1234913, by rfl⟩ : syracuseStep 1646551 = 2469827) B2469827
theorem B1646571 : Blo 1646022 1646571 := bstep (se 1 (by rfl) ⟨1234928, by rfl⟩ : syracuseStep 1646571 = 2469857) B2469857
theorem B1646583 : Blo 1646022 1646583 := bstep (se 1 (by rfl) ⟨1234937, by rfl⟩ : syracuseStep 1646583 = 2469875) B2469875
theorem B1646599 : Blo 1646022 1646599 := bstep (se 1 (by rfl) ⟨1234949, by rfl⟩ : syracuseStep 1646599 = 2469899) B2469899
theorem B1646607 : Blo 1646022 1646607 := bstep (se 1 (by rfl) ⟨1234955, by rfl⟩ : syracuseStep 1646607 = 2469911) B2469911
theorem B1646651 : Blo 1646022 1646651 := bstep (se 1 (by rfl) ⟨1234988, by rfl⟩ : syracuseStep 1646651 = 2469977) B2469977
theorem B9379907 : Blo 1646022 9379907 := bstep (se 1 (by rfl) ⟨7034930, by rfl⟩ : syracuseStep 9379907 = 14069861) B14069861
theorem B142426187 : Blo 1646022 142426187 := bstep (se 1 (by rfl) ⟨106819640, by rfl⟩ : syracuseStep 142426187 = 213639281) B213639281
theorem B1646727 : Blo 1646022 1646727 := bstep (se 1 (by rfl) ⟨1235045, by rfl⟩ : syracuseStep 1646727 = 2470091) B2470091
theorem B1646735 : Blo 1646022 1646735 := bstep (se 1 (by rfl) ⟨1235051, by rfl⟩ : syracuseStep 1646735 = 2470103) B2470103
theorem B7913645 : Blo 1646022 7913645 := bstep (se 3 (by rfl) ⟨1483808, by rfl⟩ : syracuseStep 7913645 = 2967617) B2967617
theorem B1646779 : Blo 1646022 1646779 := bstep (se 1 (by rfl) ⟨1235084, by rfl⟩ : syracuseStep 1646779 = 2470169) B2470169
theorem B1646855 : Blo 1646022 1646855 := bstep (se 1 (by rfl) ⟨1235141, by rfl⟩ : syracuseStep 1646855 = 2470283) B2470283
theorem B1646863 : Blo 1646022 1646863 := bstep (se 1 (by rfl) ⟨1235147, by rfl⟩ : syracuseStep 1646863 = 2470295) B2470295
theorem B1646907 : Blo 1646022 1646907 := bstep (se 1 (by rfl) ⟨1235180, by rfl⟩ : syracuseStep 1646907 = 2470361) B2470361
theorem B1646983 : Blo 1646022 1646983 := bstep (se 1 (by rfl) ⟨1235237, by rfl⟩ : syracuseStep 1646983 = 2470475) B2470475
theorem B1646991 : Blo 1646022 1646991 := bstep (se 1 (by rfl) ⟨1235243, by rfl⟩ : syracuseStep 1646991 = 2470487) B2470487
theorem B40075667 : Blo 1646022 40075667 := bstep (se 1 (by rfl) ⟨30056750, by rfl⟩ : syracuseStep 40075667 = 60113501) B60113501
theorem B1851835 : Blo 1646022 1851835 := bstep (se 1 (by rfl) ⟨1388876, by rfl⟩ : syracuseStep 1851835 = 2777753) B2777753
theorem B1647035 : Blo 1646022 1647035 := bstep (se 1 (by rfl) ⟨1235276, by rfl⟩ : syracuseStep 1647035 = 2470553) B2470553
theorem B8339921 : Blo 1646022 8339921 := bstep (se 2 (by rfl) ⟨3127470, by rfl⟩ : syracuseStep 8339921 = 6254941) B6254941
theorem B48144881 : Blo 1646022 48144881 := bstep (se 2 (by rfl) ⟨18054330, by rfl⟩ : syracuseStep 48144881 = 36108661) B36108661
theorem B1647111 : Blo 1646022 1647111 := bstep (se 1 (by rfl) ⟨1235333, by rfl⟩ : syracuseStep 1647111 = 2470667) B2470667
theorem B1647119 : Blo 1646022 1647119 := bstep (se 1 (by rfl) ⟨1235339, by rfl⟩ : syracuseStep 1647119 = 2470679) B2470679
theorem B5423645 : Blo 1646022 5423645 := bstep (se 3 (by rfl) ⟨1016933, by rfl⟩ : syracuseStep 5423645 = 2033867) B2033867
theorem B3383851 : Blo 1646022 3383851 := bstep (se 1 (by rfl) ⟨2537888, by rfl⟩ : syracuseStep 3383851 = 5075777) B5075777
theorem B1647163 : Blo 1646022 1647163 := bstep (se 1 (by rfl) ⟨1235372, by rfl⟩ : syracuseStep 1647163 = 2470745) B2470745
theorem B11264579 : Blo 1646022 11264579 := bstep (se 1 (by rfl) ⟨8448434, by rfl⟩ : syracuseStep 11264579 = 16896869) B16896869
theorem B2777719 : Blo 1646022 2777719 := bstep (se 1 (by rfl) ⟨2083289, by rfl⟩ : syracuseStep 2777719 = 4166579) B4166579
theorem B1647239 : Blo 1646022 1647239 := bstep (se 1 (by rfl) ⟨1235429, by rfl⟩ : syracuseStep 1647239 = 2470859) B2470859
theorem B1647247 : Blo 1646022 1647247 := bstep (se 1 (by rfl) ⟨1235435, by rfl⟩ : syracuseStep 1647247 = 2470871) B2470871
theorem B1647291 : Blo 1646022 1647291 := bstep (se 1 (by rfl) ⟨1235468, by rfl⟩ : syracuseStep 1647291 = 2470937) B2470937
theorem B20038373 : Blo 1646022 20038373 := bstep (se 4 (by rfl) ⟨1878597, by rfl⟩ : syracuseStep 20038373 = 3757195) B3757195
theorem B1647367 : Blo 1646022 1647367 := bstep (se 1 (by rfl) ⟨1235525, by rfl⟩ : syracuseStep 1647367 = 2471051) B2471051
theorem B1647375 : Blo 1646022 1647375 := bstep (se 1 (by rfl) ⟨1235531, by rfl⟩ : syracuseStep 1647375 = 2471063) B2471063
theorem B2777915 : Blo 1646022 2777915 := bstep (se 1 (by rfl) ⟨2083436, by rfl⟩ : syracuseStep 2777915 = 4166873) B4166873
theorem B1647419 : Blo 1646022 1647419 := bstep (se 1 (by rfl) ⟨1235564, by rfl⟩ : syracuseStep 1647419 = 2471129) B2471129
theorem B1647495 : Blo 1646022 1647495 := bstep (se 1 (by rfl) ⟨1235621, by rfl⟩ : syracuseStep 1647495 = 2471243) B2471243
theorem B1852303 : Blo 1646022 1852303 := bstep (se 1 (by rfl) ⟨1389227, by rfl⟩ : syracuseStep 1852303 = 2778455) B2778455
theorem B1647503 : Blo 1646022 1647503 := bstep (se 1 (by rfl) ⟨1235627, by rfl⟩ : syracuseStep 1647503 = 2471255) B2471255
theorem B4170649 : Blo 1646022 4170649 := bstep (se 2 (by rfl) ⟨1563993, by rfl⟩ : syracuseStep 4170649 = 3127987) B3127987
theorem B1647547 : Blo 1646022 1647547 := bstep (se 1 (by rfl) ⟨1235660, by rfl⟩ : syracuseStep 1647547 = 2471321) B2471321
theorem B9511901 : Blo 1646022 9511901 := bstep (se 3 (by rfl) ⟨1783481, by rfl⟩ : syracuseStep 9511901 = 3566963) B3566963
theorem B1647623 : Blo 1646022 1647623 := bstep (se 1 (by rfl) ⟨1235717, by rfl⟩ : syracuseStep 1647623 = 2471435) B2471435
theorem B3703823 : Blo 1646022 3703823 := bstep (se 1 (by rfl) ⟨2777867, by rfl⟩ : syracuseStep 3703823 = 5555735) B5555735
theorem B1647631 : Blo 1646022 1647631 := bstep (se 1 (by rfl) ⟨1235723, by rfl⟩ : syracuseStep 1647631 = 2471447) B2471447
theorem B3703841 : Blo 1646022 3703841 := bstep (se 2 (by rfl) ⟨1388940, by rfl⟩ : syracuseStep 3703841 = 2777881) B2777881
theorem B1647675 : Blo 1646022 1647675 := bstep (se 1 (by rfl) ⟨1235756, by rfl⟩ : syracuseStep 1647675 = 2471513) B2471513
theorem B4170811 : Blo 1646022 4170811 := bstep (se 1 (by rfl) ⟨3128108, by rfl⟩ : syracuseStep 4170811 = 6256217) B6256217
theorem B8905789 : Blo 1646022 8905789 := bstep (se 3 (by rfl) ⟨1669835, by rfl⟩ : syracuseStep 8905789 = 3339671) B3339671
theorem B1647751 : Blo 1646022 1647751 := bstep (se 1 (by rfl) ⟨1235813, by rfl⟩ : syracuseStep 1647751 = 2471627) B2471627
theorem B1647759 : Blo 1646022 1647759 := bstep (se 1 (by rfl) ⟨1235819, by rfl⟩ : syracuseStep 1647759 = 2471639) B2471639
theorem B1647803 : Blo 1646022 1647803 := bstep (se 1 (by rfl) ⟨1235852, by rfl⟩ : syracuseStep 1647803 = 2471705) B2471705
theorem B2778313 : Blo 1646022 2778313 := bstep (se 2 (by rfl) ⟨1041867, by rfl⟩ : syracuseStep 2778313 = 2083735) B2083735
theorem B4170953 : Blo 1646022 4170953 := bstep (se 2 (by rfl) ⟨1564107, by rfl⟩ : syracuseStep 4170953 = 3128215) B3128215
theorem B1647879 : Blo 1646022 1647879 := bstep (se 1 (by rfl) ⟨1235909, by rfl⟩ : syracuseStep 1647879 = 2471819) B2471819
theorem B3515663 : Blo 1646022 3515663 := bstep (se 1 (by rfl) ⟨2636747, by rfl⟩ : syracuseStep 3515663 = 5273495) B5273495
theorem B1647887 : Blo 1646022 1647887 := bstep (se 1 (by rfl) ⟨1235915, by rfl⟩ : syracuseStep 1647887 = 2471831) B2471831
theorem B1647931 : Blo 1646022 1647931 := bstep (se 1 (by rfl) ⟨1235948, by rfl⟩ : syracuseStep 1647931 = 2471897) B2471897
theorem B3704183 : Blo 1646022 3704183 := bstep (se 1 (by rfl) ⟨2778137, by rfl⟩ : syracuseStep 3704183 = 5556275) B5556275
theorem B4179319 : Blo 1646022 4179319 := bstep (se 1 (by rfl) ⟨3134489, by rfl⟩ : syracuseStep 4179319 = 6268979) B6268979
theorem B16049539 : Blo 1646022 16049539 := bstep (se 1 (by rfl) ⟨12037154, by rfl⟩ : syracuseStep 16049539 = 24074309) B24074309
theorem B1852807 : Blo 1646022 1852807 := bstep (se 1 (by rfl) ⟨1389605, by rfl⟩ : syracuseStep 1852807 = 2779211) B2779211
theorem B1648007 : Blo 1646022 1648007 := bstep (se 1 (by rfl) ⟨1236005, by rfl⟩ : syracuseStep 1648007 = 2472011) B2472011
theorem B1648015 : Blo 1646022 1648015 := bstep (se 1 (by rfl) ⟨1236011, by rfl⟩ : syracuseStep 1648015 = 2472023) B2472023
theorem B12510611 : Blo 1646022 12510611 := bstep (se 1 (by rfl) ⟨9382958, by rfl⟩ : syracuseStep 12510611 = 18765917) B18765917
theorem B3958283 : Blo 1646022 3958283 := bstep (se 1 (by rfl) ⟨2968712, by rfl⟩ : syracuseStep 3958283 = 5937425) B5937425
theorem B4171297 : Blo 1646022 4171297 := bstep (se 2 (by rfl) ⟨1564236, by rfl⟩ : syracuseStep 4171297 = 3128473) B3128473
theorem B3704363 : Blo 1646022 3704363 := bstep (se 1 (by rfl) ⟨2778272, by rfl⟩ : syracuseStep 3704363 = 5556545) B5556545
theorem B1852987 : Blo 1646022 1852987 := bstep (se 1 (by rfl) ⟨1389740, by rfl⟩ : syracuseStep 1852987 = 2779481) B2779481
theorem B7128695 : Blo 1646022 7128695 := bstep (se 1 (by rfl) ⟨5346521, by rfl⟩ : syracuseStep 7128695 = 10693043) B10693043
theorem B2344567 : Blo 1646022 2344567 := bstep (se 1 (by rfl) ⟨1758425, by rfl⟩ : syracuseStep 2344567 = 3516851) B3516851
theorem B4753043 : Blo 1646022 4753043 := bstep (se 1 (by rfl) ⟨3564782, by rfl⟩ : syracuseStep 4753043 = 7129565) B7129565
theorem B4687561 : Blo 1646022 4687561 := bstep (se 2 (by rfl) ⟨1757835, by rfl⟩ : syracuseStep 4687561 = 3515671) B3515671
theorem B2967329 : Blo 1646022 2967329 := bstep (se 2 (by rfl) ⟨1112748, by rfl⟩ : syracuseStep 2967329 = 2225497) B2225497
theorem B12502835 : Blo 1646022 12502835 := bstep (se 1 (by rfl) ⟨9377126, by rfl⟩ : syracuseStep 12502835 = 18754253) B18754253
theorem B9381683 : Blo 1646022 9381683 := bstep (se 1 (by rfl) ⟨7036262, by rfl⟩ : syracuseStep 9381683 = 14072525) B14072525
theorem B2639675 : Blo 1646022 2639675 := bstep (se 1 (by rfl) ⟨1979756, by rfl⟩ : syracuseStep 2639675 = 3959513) B3959513
theorem B2779015 : Blo 1646022 2779015 := bstep (se 1 (by rfl) ⟨2084261, by rfl⟩ : syracuseStep 2779015 = 4168523) B4168523
theorem B3704723 : Blo 1646022 3704723 := bstep (se 1 (by rfl) ⟨2778542, by rfl⟩ : syracuseStep 3704723 = 5557085) B5557085
theorem B8456089 : Blo 1646022 8456089 := bstep (se 2 (by rfl) ⟨3171033, by rfl⟩ : syracuseStep 8456089 = 6342067) B6342067
theorem B3704777 : Blo 1646022 3704777 := bstep (se 2 (by rfl) ⟨1389291, by rfl⟩ : syracuseStep 3704777 = 2778583) B2778583
theorem B6252497 : Blo 1646022 6252497 := bstep (se 2 (by rfl) ⟨2344686, by rfl⟩ : syracuseStep 6252497 = 4689373) B4689373
theorem B1853455 : Blo 1646022 1853455 := bstep (se 1 (by rfl) ⟨1390091, by rfl⟩ : syracuseStep 1853455 = 2780183) B2780183
theorem B4687915 : Blo 1646022 4687915 := bstep (se 1 (by rfl) ⟨3515936, by rfl⟩ : syracuseStep 4687915 = 7031873) B7031873
theorem B3958919 : Blo 1646022 3958919 := bstep (se 1 (by rfl) ⟨2969189, by rfl⟩ : syracuseStep 3958919 = 5938379) B5938379
theorem B3959051 : Blo 1646022 3959051 := bstep (se 1 (by rfl) ⟨2969288, by rfl⟩ : syracuseStep 3959051 = 5938577) B5938577
theorem B6252815 : Blo 1646022 6252815 := bstep (se 1 (by rfl) ⟨4689611, by rfl⟩ : syracuseStep 6252815 = 9379223) B9379223
theorem B4688189 : Blo 1646022 4688189 := bstep (se 3 (by rfl) ⟨879035, by rfl⟩ : syracuseStep 4688189 = 1758071) B1758071
theorem B2083259 : Blo 1646022 2083259 := bstep (se 1 (by rfl) ⟨1562444, by rfl⟩ : syracuseStep 2083259 = 3124889) B3124889
theorem B1853959 : Blo 1646022 1853959 := bstep (se 1 (by rfl) ⟨1390469, by rfl⟩ : syracuseStep 1853959 = 2780939) B2780939
theorem B8342027 : Blo 1646022 8342027 := bstep (se 1 (by rfl) ⟨6256520, by rfl⟩ : syracuseStep 8342027 = 12513041) B12513041
theorem B2779663 : Blo 1646022 2779663 := bstep (se 1 (by rfl) ⟨2084747, by rfl⟩ : syracuseStep 2779663 = 4169495) B4169495
theorem B3705479 : Blo 1646022 3705479 := bstep (se 1 (by rfl) ⟨2779109, by rfl⟩ : syracuseStep 3705479 = 5558219) B5558219
theorem B8342189 : Blo 1646022 8342189 := bstep (se 3 (by rfl) ⟨1564160, by rfl⟩ : syracuseStep 8342189 = 3128321) B3128321
theorem B25340687 : Blo 1646022 25340687 := bstep (se 1 (by rfl) ⟨19005515, by rfl⟩ : syracuseStep 25340687 = 38011031) B38011031
theorem B5008171 : Blo 1646022 5008171 := bstep (se 1 (by rfl) ⟨3756128, by rfl⟩ : syracuseStep 5008171 = 7512257) B7512257
theorem B3705659 : Blo 1646022 3705659 := bstep (se 1 (by rfl) ⟨2779244, by rfl⟩ : syracuseStep 3705659 = 5558489) B5558489
theorem B23751539 : Blo 1646022 23751539 := bstep (se 1 (by rfl) ⟨17813654, by rfl⟩ : syracuseStep 23751539 = 35627309) B35627309
theorem B5557139 : Blo 1646022 5557139 := bstep (se 1 (by rfl) ⟨4167854, by rfl⟩ : syracuseStep 5557139 = 8335709) B8335709
theorem B3705785 : Blo 1646022 3705785 := bstep (se 2 (by rfl) ⟨1389669, by rfl⟩ : syracuseStep 3705785 = 2779339) B2779339
theorem B12684235 : Blo 1646022 12684235 := bstep (se 1 (by rfl) ⟨9513176, by rfl⟩ : syracuseStep 12684235 = 19026353) B19026353
theorem B2968591 : Blo 1646022 2968591 := bstep (se 1 (by rfl) ⟨2226443, by rfl⟩ : syracuseStep 2968591 = 4452887) B4452887
theorem B2780203 : Blo 1646022 2780203 := bstep (se 1 (by rfl) ⟨2085152, by rfl⟩ : syracuseStep 2780203 = 4170305) B4170305
theorem B37096535 : Blo 1646022 37096535 := bstep (se 1 (by rfl) ⟨27822401, by rfl⟩ : syracuseStep 37096535 = 55644803) B55644803
theorem B2469035 : Blo 1646022 2469035 := bstep (se 1 (by rfl) ⟨1851776, by rfl⟩ : syracuseStep 2469035 = 3703553) B3703553
theorem B2780345 : Blo 1646022 2780345 := bstep (se 2 (by rfl) ⟨1042629, by rfl⟩ : syracuseStep 2780345 = 2085259) B2085259
theorem B2469065 : Blo 1646022 2469065 := bstep (se 2 (by rfl) ⟨925899, by rfl⟩ : syracuseStep 2469065 = 1851799) B1851799
theorem B9383141 : Blo 1646022 9383141 := bstep (se 4 (by rfl) ⟨879669, by rfl⟩ : syracuseStep 9383141 = 1759339) B1759339
theorem B3706127 : Blo 1646022 3706127 := bstep (se 1 (by rfl) ⟨2779595, by rfl⟩ : syracuseStep 3706127 = 5559191) B5559191
theorem B3706145 : Blo 1646022 3706145 := bstep (se 2 (by rfl) ⟨1389804, by rfl⟩ : syracuseStep 3706145 = 2779609) B2779609
theorem B3517739 : Blo 1646022 3517739 := bstep (se 1 (by rfl) ⟨2638304, by rfl⟩ : syracuseStep 3517739 = 5276609) B5276609
theorem B2469179 : Blo 1646022 2469179 := bstep (se 1 (by rfl) ⟨1851884, by rfl⟩ : syracuseStep 2469179 = 3703769) B3703769
theorem B4754749 : Blo 1646022 4754749 := bstep (se 3 (by rfl) ⟨891515, by rfl⟩ : syracuseStep 4754749 = 1783031) B1783031
theorem B2469239 : Blo 1646022 2469239 := bstep (se 1 (by rfl) ⟨1851929, by rfl⟩ : syracuseStep 2469239 = 3703859) B3703859
theorem B38014343 : Blo 1646022 38014343 := bstep (se 1 (by rfl) ⟨28510757, by rfl⟩ : syracuseStep 38014343 = 57021515) B57021515
theorem B15822215 : Blo 1646022 15822215 := bstep (se 1 (by rfl) ⟨11866661, by rfl⟩ : syracuseStep 15822215 = 23733323) B23733323
theorem B2084231 : Blo 1646022 2084231 := bstep (se 1 (by rfl) ⟨1563173, by rfl⟩ : syracuseStep 2084231 = 3126347) B3126347
theorem B2469263 : Blo 1646022 2469263 := bstep (se 1 (by rfl) ⟨1851947, by rfl⟩ : syracuseStep 2469263 = 3703895) B3703895
theorem B8334737 : Blo 1646022 8334737 := bstep (se 2 (by rfl) ⟨3125526, by rfl⟩ : syracuseStep 8334737 = 6251053) B6251053
theorem B2469305 : Blo 1646022 2469305 := bstep (se 2 (by rfl) ⟨925989, by rfl⟩ : syracuseStep 2469305 = 1851979) B1851979
theorem B14069213 : Blo 1646022 14069213 := bstep (se 3 (by rfl) ⟨2637977, by rfl⟩ : syracuseStep 14069213 = 5275955) B5275955
theorem B2469383 : Blo 1646022 2469383 := bstep (se 1 (by rfl) ⟨1852037, by rfl⟩ : syracuseStep 2469383 = 3704075) B3704075
theorem B2469419 : Blo 1646022 2469419 := bstep (se 1 (by rfl) ⟨1852064, by rfl⟩ : syracuseStep 2469419 = 3704129) B3704129
theorem B2674235 : Blo 1646022 2674235 := bstep (se 1 (by rfl) ⟨2005676, by rfl⟩ : syracuseStep 2674235 = 4011353) B4011353
theorem B2469449 : Blo 1646022 2469449 := bstep (se 2 (by rfl) ⟨926043, by rfl⟩ : syracuseStep 2469449 = 1852087) B1852087
theorem B3706487 : Blo 1646022 3706487 := bstep (se 1 (by rfl) ⟨2779865, by rfl⟩ : syracuseStep 3706487 = 5559731) B5559731
theorem B9383597 : Blo 1646022 9383597 := bstep (se 3 (by rfl) ⟨1759424, by rfl⟩ : syracuseStep 9383597 = 3518849) B3518849
theorem B2469563 : Blo 1646022 2469563 := bstep (se 1 (by rfl) ⟨1852172, by rfl⟩ : syracuseStep 2469563 = 3704345) B3704345
theorem B15642341 : Blo 1646022 15642341 := bstep (se 4 (by rfl) ⟨1466469, by rfl⟩ : syracuseStep 15642341 = 2932939) B2932939
theorem B2469623 : Blo 1646022 2469623 := bstep (se 1 (by rfl) ⟨1852217, by rfl⟩ : syracuseStep 2469623 = 3704435) B3704435
theorem B2469647 : Blo 1646022 2469647 := bstep (se 1 (by rfl) ⟨1852235, by rfl⟩ : syracuseStep 2469647 = 3704471) B3704471
theorem B18771749 : Blo 1646022 18771749 := bstep (se 4 (by rfl) ⟨1759851, by rfl⟩ : syracuseStep 18771749 = 3519703) B3519703
theorem B3706667 : Blo 1646022 3706667 := bstep (se 1 (by rfl) ⟨2780000, by rfl⟩ : syracuseStep 3706667 = 5560001) B5560001
theorem B2469689 : Blo 1646022 2469689 := bstep (se 2 (by rfl) ⟨926133, by rfl⟩ : syracuseStep 2469689 = 1852267) B1852267
theorem B2469767 : Blo 1646022 2469767 := bstep (se 1 (by rfl) ⟨1852325, by rfl⟩ : syracuseStep 2469767 = 3704651) B3704651
theorem B2469803 : Blo 1646022 2469803 := bstep (se 1 (by rfl) ⟨1852352, by rfl⟩ : syracuseStep 2469803 = 3704705) B3704705
theorem B2469833 : Blo 1646022 2469833 := bstep (se 2 (by rfl) ⟨926187, by rfl⟩ : syracuseStep 2469833 = 1852375) B1852375
theorem B2084879 : Blo 1646022 2084879 := bstep (se 1 (by rfl) ⟨1563659, by rfl⟩ : syracuseStep 2084879 = 3127319) B3127319
theorem B2469947 : Blo 1646022 2469947 := bstep (se 1 (by rfl) ⟨1852460, by rfl⟩ : syracuseStep 2469947 = 3704921) B3704921
theorem B2470007 : Blo 1646022 2470007 := bstep (se 1 (by rfl) ⟨1852505, by rfl⟩ : syracuseStep 2470007 = 3705011) B3705011
theorem B2470031 : Blo 1646022 2470031 := bstep (se 1 (by rfl) ⟨1852523, by rfl⟩ : syracuseStep 2470031 = 3705047) B3705047
theorem B3707027 : Blo 1646022 3707027 := bstep (se 1 (by rfl) ⟨2780270, by rfl⟩ : syracuseStep 3707027 = 5560541) B5560541
theorem B2470073 : Blo 1646022 2470073 := bstep (se 2 (by rfl) ⟨926277, by rfl⟩ : syracuseStep 2470073 = 1852555) B1852555
theorem B2674873 : Blo 1646022 2674873 := bstep (se 2 (by rfl) ⟨1003077, by rfl⟩ : syracuseStep 2674873 = 2006155) B2006155
theorem B11866313 : Blo 1646022 11866313 := bstep (se 2 (by rfl) ⟨4449867, by rfl⟩ : syracuseStep 11866313 = 8899735) B8899735
theorem B3707081 : Blo 1646022 3707081 := bstep (se 2 (by rfl) ⟨1390155, by rfl⟩ : syracuseStep 3707081 = 2780311) B2780311
theorem B2470151 : Blo 1646022 2470151 := bstep (se 1 (by rfl) ⟨1852613, by rfl⟩ : syracuseStep 2470151 = 3705227) B3705227
theorem B5558543 : Blo 1646022 5558543 := bstep (se 1 (by rfl) ⟨4168907, by rfl⟩ : syracuseStep 5558543 = 8337815) B8337815
theorem B9376033 : Blo 1646022 9376033 := bstep (se 2 (by rfl) ⟨3516012, by rfl⟩ : syracuseStep 9376033 = 7032025) B7032025
theorem B2470187 : Blo 1646022 2470187 := bstep (se 1 (by rfl) ⟨1852640, by rfl⟩ : syracuseStep 2470187 = 3705281) B3705281
theorem B2470217 : Blo 1646022 2470217 := bstep (se 2 (by rfl) ⟨926331, by rfl⟩ : syracuseStep 2470217 = 1852663) B1852663
theorem B9384281 : Blo 1646022 9384281 := bstep (se 2 (by rfl) ⟨3519105, by rfl⟩ : syracuseStep 9384281 = 7038211) B7038211
theorem B4690295 : Blo 1646022 4690295 := bstep (se 1 (by rfl) ⟨3517721, by rfl⟩ : syracuseStep 4690295 = 7035443) B7035443
theorem B10015123 : Blo 1646022 10015123 := bstep (se 1 (by rfl) ⟨7511342, by rfl⟩ : syracuseStep 10015123 = 15022685) B15022685
theorem B2470331 : Blo 1646022 2470331 := bstep (se 1 (by rfl) ⟨1852748, by rfl⟩ : syracuseStep 2470331 = 3705497) B3705497
theorem B2470391 : Blo 1646022 2470391 := bstep (se 1 (by rfl) ⟨1852793, by rfl⟩ : syracuseStep 2470391 = 3705587) B3705587
theorem B9024011 : Blo 1646022 9024011 := bstep (se 1 (by rfl) ⟨6768008, by rfl⟩ : syracuseStep 9024011 = 13536017) B13536017
theorem B2470415 : Blo 1646022 2470415 := bstep (se 1 (by rfl) ⟨1852811, by rfl⟩ : syracuseStep 2470415 = 3705623) B3705623
theorem B5558813 : Blo 1646022 5558813 := bstep (se 3 (by rfl) ⟨1042277, by rfl⟩ : syracuseStep 5558813 = 2084555) B2084555
theorem B2470457 : Blo 1646022 2470457 := bstep (se 2 (by rfl) ⟨926421, by rfl⟩ : syracuseStep 2470457 = 1852843) B1852843
theorem B2470535 : Blo 1646022 2470535 := bstep (se 1 (by rfl) ⟨1852901, by rfl⟩ : syracuseStep 2470535 = 3705803) B3705803
theorem B2224783 : Blo 1646022 2224783 := bstep (se 1 (by rfl) ⟨1668587, by rfl⟩ : syracuseStep 2224783 = 3337175) B3337175
theorem B2470571 : Blo 1646022 2470571 := bstep (se 1 (by rfl) ⟨1852928, by rfl⟩ : syracuseStep 2470571 = 3705857) B3705857
theorem B3125945 : Blo 1646022 3125945 := bstep (se 2 (by rfl) ⟨1172229, by rfl⟩ : syracuseStep 3125945 = 2344459) B2344459
theorem B2470601 : Blo 1646022 2470601 := bstep (se 2 (by rfl) ⟨926475, by rfl⟩ : syracuseStep 2470601 = 1852951) B1852951
theorem B2470715 : Blo 1646022 2470715 := bstep (se 1 (by rfl) ⟨1853036, by rfl⟩ : syracuseStep 2470715 = 3706073) B3706073
theorem B2470775 : Blo 1646022 2470775 := bstep (se 1 (by rfl) ⟨1853081, by rfl⟩ : syracuseStep 2470775 = 3706163) B3706163
theorem B3707783 : Blo 1646022 3707783 := bstep (se 1 (by rfl) ⟨2780837, by rfl⟩ : syracuseStep 3707783 = 5561675) B5561675
theorem B2470799 : Blo 1646022 2470799 := bstep (se 1 (by rfl) ⟨1853099, by rfl⟩ : syracuseStep 2470799 = 3706199) B3706199
theorem B3519379 : Blo 1646022 3519379 := bstep (se 1 (by rfl) ⟨2639534, by rfl⟩ : syracuseStep 3519379 = 5279069) B5279069
theorem B2470841 : Blo 1646022 2470841 := bstep (se 2 (by rfl) ⟨926565, by rfl⟩ : syracuseStep 2470841 = 1853131) B1853131
theorem B2470919 : Blo 1646022 2470919 := bstep (se 1 (by rfl) ⟨1853189, by rfl⟩ : syracuseStep 2470919 = 3706379) B3706379
theorem B2470955 : Blo 1646022 2470955 := bstep (se 1 (by rfl) ⟨1853216, by rfl⟩ : syracuseStep 2470955 = 3706433) B3706433
theorem B3707963 : Blo 1646022 3707963 := bstep (se 1 (by rfl) ⟨2780972, by rfl⟩ : syracuseStep 3707963 = 5561945) B5561945
theorem B2470985 : Blo 1646022 2470985 := bstep (se 2 (by rfl) ⟨926619, by rfl⟩ : syracuseStep 2470985 = 1853239) B1853239
theorem B2225323 : Blo 1646022 2225323 := bstep (se 1 (by rfl) ⟨1668992, by rfl⟩ : syracuseStep 2225323 = 3337985) B3337985
theorem B2471099 : Blo 1646022 2471099 := bstep (se 1 (by rfl) ⟨1853324, by rfl⟩ : syracuseStep 2471099 = 3706649) B3706649
theorem B24065261 : Blo 1646022 24065261 := bstep (se 3 (by rfl) ⟨4512236, by rfl⟩ : syracuseStep 24065261 = 9024473) B9024473
theorem B2471159 : Blo 1646022 2471159 := bstep (se 1 (by rfl) ⟨1853369, by rfl⟩ : syracuseStep 2471159 = 3706739) B3706739
theorem B4166923 : Blo 1646022 4166923 := bstep (se 1 (by rfl) ⟨3125192, by rfl⟩ : syracuseStep 4166923 = 6250385) B6250385
theorem B2471183 : Blo 1646022 2471183 := bstep (se 1 (by rfl) ⟨1853387, by rfl⟩ : syracuseStep 2471183 = 3706775) B3706775
theorem B2471225 : Blo 1646022 2471225 := bstep (se 2 (by rfl) ⟨926709, by rfl⟩ : syracuseStep 2471225 = 1853419) B1853419
theorem B2471303 : Blo 1646022 2471303 := bstep (se 1 (by rfl) ⟨1853477, by rfl⟩ : syracuseStep 2471303 = 3706955) B3706955
theorem B2225551 : Blo 1646022 2225551 := bstep (se 1 (by rfl) ⟨1669163, by rfl⟩ : syracuseStep 2225551 = 3338327) B3338327
theorem B4167065 : Blo 1646022 4167065 := bstep (se 2 (by rfl) ⟨1562649, by rfl⟩ : syracuseStep 4167065 = 3125299) B3125299
theorem B2471339 : Blo 1646022 2471339 := bstep (se 1 (by rfl) ⟨1853504, by rfl⟩ : syracuseStep 2471339 = 3707009) B3707009
theorem B2471369 : Blo 1646022 2471369 := bstep (se 2 (by rfl) ⟨926763, by rfl⟩ : syracuseStep 2471369 = 1853527) B1853527
theorem B8336843 : Blo 1646022 8336843 := bstep (se 1 (by rfl) ⟨6252632, by rfl⟩ : syracuseStep 8336843 = 12505265) B12505265
theorem B9377309 : Blo 1646022 9377309 := bstep (se 3 (by rfl) ⟨1758245, by rfl⟩ : syracuseStep 9377309 = 3516491) B3516491
theorem B4167227 : Blo 1646022 4167227 := bstep (se 1 (by rfl) ⟨3125420, by rfl⟩ : syracuseStep 4167227 = 6250841) B6250841
theorem B2471483 : Blo 1646022 2471483 := bstep (se 1 (by rfl) ⟨1853612, by rfl⟩ : syracuseStep 2471483 = 3707225) B3707225
theorem B2471543 : Blo 1646022 2471543 := bstep (se 1 (by rfl) ⟨1853657, by rfl⟩ : syracuseStep 2471543 = 3707315) B3707315
theorem B2471567 : Blo 1646022 2471567 := bstep (se 1 (by rfl) ⟨1853675, by rfl⟩ : syracuseStep 2471567 = 3707351) B3707351
theorem B3757715 : Blo 1646022 3757715 := bstep (se 1 (by rfl) ⟨2818286, by rfl⟩ : syracuseStep 3757715 = 5636573) B5636573
theorem B2471609 : Blo 1646022 2471609 := bstep (se 2 (by rfl) ⟨926853, by rfl⟩ : syracuseStep 2471609 = 1853707) B1853707
theorem B6256385 : Blo 1646022 6256385 := bstep (se 2 (by rfl) ⟨2346144, by rfl⟩ : syracuseStep 6256385 = 4692289) B4692289
theorem B2471687 : Blo 1646022 2471687 := bstep (se 1 (by rfl) ⟨1853765, by rfl⟩ : syracuseStep 2471687 = 3707531) B3707531
theorem B8337167 : Blo 1646022 8337167 := bstep (se 1 (by rfl) ⟨6252875, by rfl⟩ : syracuseStep 8337167 = 12505751) B12505751
theorem B6256399 : Blo 1646022 6256399 := bstep (se 1 (by rfl) ⟨4692299, by rfl⟩ : syracuseStep 6256399 = 9384599) B9384599
theorem B2471723 : Blo 1646022 2471723 := bstep (se 1 (by rfl) ⟨1853792, by rfl⟩ : syracuseStep 2471723 = 3707585) B3707585
theorem B3127099 : Blo 1646022 3127099 := bstep (se 1 (by rfl) ⟨2345324, by rfl⟩ : syracuseStep 3127099 = 4690649) B4690649
theorem B2471753 : Blo 1646022 2471753 := bstep (se 2 (by rfl) ⟨926907, by rfl⟩ : syracuseStep 2471753 = 1853815) B1853815
theorem B7034759 : Blo 1646022 7034759 := bstep (se 1 (by rfl) ⟨5276069, by rfl⟩ : syracuseStep 7034759 = 10552139) B10552139
theorem B4454279 : Blo 1646022 4454279 := bstep (se 1 (by rfl) ⟨3340709, by rfl⟩ : syracuseStep 4454279 = 6681419) B6681419
theorem B4167571 : Blo 1646022 4167571 := bstep (se 1 (by rfl) ⟨3125678, by rfl⟩ : syracuseStep 4167571 = 6251357) B6251357
theorem B5560217 : Blo 1646022 5560217 := bstep (se 2 (by rfl) ⟨2085081, by rfl⟩ : syracuseStep 5560217 = 4170163) B4170163
theorem B2471867 : Blo 1646022 2471867 := bstep (se 1 (by rfl) ⟨1853900, by rfl⟩ : syracuseStep 2471867 = 3707801) B3707801
theorem B2471927 : Blo 1646022 2471927 := bstep (se 1 (by rfl) ⟨1853945, by rfl⟩ : syracuseStep 2471927 = 3707891) B3707891
theorem B2471951 : Blo 1646022 2471951 := bstep (se 1 (by rfl) ⟨1853963, by rfl⟩ : syracuseStep 2471951 = 3707927) B3707927
theorem B45078551 : Blo 1646022 45078551 := bstep (se 1 (by rfl) ⟨33808913, by rfl⟩ : syracuseStep 45078551 = 67617827) B67617827
theorem B4167713 : Blo 1646022 4167713 := bstep (se 2 (by rfl) ⟨1562892, by rfl⟩ : syracuseStep 4167713 = 3125785) B3125785
theorem B2471993 : Blo 1646022 2471993 := bstep (se 2 (by rfl) ⟨926997, by rfl⟩ : syracuseStep 2471993 = 1853995) B1853995
theorem B10016855 : Blo 1646022 10016855 := bstep (se 1 (by rfl) ⟨7512641, by rfl⟩ : syracuseStep 10016855 = 15025283) B15025283
theorem B42776849 : Blo 1646022 42776849 := bstep (se 2 (by rfl) ⟨16041318, by rfl⟩ : syracuseStep 42776849 = 32082637) B32082637
theorem B3954977 : Blo 1646022 3954977 := bstep (se 2 (by rfl) ⟨1483116, by rfl⟩ : syracuseStep 3954977 = 2966233) B2966233
theorem B7035169 : Blo 1646022 7035169 := bstep (se 2 (by rfl) ⟨2638188, by rfl⟩ : syracuseStep 7035169 = 5276377) B5276377
theorem B3127585 : Blo 1646022 3127585 := bstep (se 2 (by rfl) ⟨1172844, by rfl⟩ : syracuseStep 3127585 = 2345689) B2345689
theorem B2505095 : Blo 1646022 2505095 := bstep (se 1 (by rfl) ⟨1878821, by rfl⟩ : syracuseStep 2505095 = 3757643) B3757643
theorem B3758537 : Blo 1646022 3758537 := bstep (se 2 (by rfl) ⟨1409451, by rfl⟩ : syracuseStep 3758537 = 2818903) B2818903
theorem B42187229 : Blo 1646022 42187229 := bstep (se 3 (by rfl) ⟨7910105, by rfl⟩ : syracuseStep 42187229 = 15820211) B15820211
theorem B5274173 : Blo 1646022 5274173 := bstep (se 3 (by rfl) ⟨988907, by rfl⟩ : syracuseStep 5274173 = 1977815) B1977815
theorem B5560919 : Blo 1646022 5560919 := bstep (se 1 (by rfl) ⟨4170689, by rfl⟩ : syracuseStep 5560919 = 8341379) B8341379
theorem B7035511 : Blo 1646022 7035511 := bstep (se 1 (by rfl) ⟨5276633, by rfl⟩ : syracuseStep 7035511 = 10553267) B10553267
theorem B5077657 : Blo 1646022 5077657 := bstep (se 2 (by rfl) ⟨1904121, by rfl⟩ : syracuseStep 5077657 = 3808243) B3808243
theorem B9509669 : Blo 1646022 9509669 := bstep (se 4 (by rfl) ⟨891531, by rfl⟩ : syracuseStep 9509669 = 1783063) B1783063
theorem B4692779 : Blo 1646022 4692779 := bstep (se 1 (by rfl) ⟨3519584, by rfl⟩ : syracuseStep 4692779 = 7039169) B7039169
theorem B5274521 : Blo 1646022 5274521 := bstep (se 2 (by rfl) ⟨1977945, by rfl⟩ : syracuseStep 5274521 = 3955891) B3955891
theorem B23739317 : Blo 1646022 23739317 := bstep (se 5 (by rfl) ⟨1112780, by rfl⟩ : syracuseStep 23739317 = 2225561) B2225561
theorem B4168705 : Blo 1646022 4168705 := bstep (se 2 (by rfl) ⟨1563264, by rfl⟩ : syracuseStep 4168705 = 3126529) B3126529
theorem B5561405 : Blo 1646022 5561405 := bstep (se 3 (by rfl) ⟨1042763, by rfl⟩ : syracuseStep 5561405 = 2085527) B2085527
theorem B8338625 : Blo 1646022 8338625 := bstep (se 2 (by rfl) ⟨3126984, by rfl⟩ : syracuseStep 8338625 = 6253969) B6253969
theorem B21405059 : Blo 1646022 21405059 := bstep (se 1 (by rfl) ⟨16053794, by rfl⟩ : syracuseStep 21405059 = 32107589) B32107589
theorem B1646087 : Blo 1646022 1646087 := bstep (se 1 (by rfl) ⟨1234565, by rfl⟩ : syracuseStep 1646087 = 2469131) B2469131
theorem B5275147 : Blo 1646022 5275147 := bstep (se 1 (by rfl) ⟨3956360, by rfl⟩ : syracuseStep 5275147 = 7912721) B7912721
theorem B1646095 : Blo 1646022 1646095 := bstep (se 1 (by rfl) ⟨1234571, by rfl⟩ : syracuseStep 1646095 = 2469143) B2469143
theorem B1646139 : Blo 1646022 1646139 := bstep (se 1 (by rfl) ⟨1234604, by rfl⟩ : syracuseStep 1646139 = 2469209) B2469209
theorem B4169303 : Blo 1646022 4169303 := bstep (se 1 (by rfl) ⟨3126977, by rfl⟩ : syracuseStep 4169303 = 6253955) B6253955
theorem B1646215 : Blo 1646022 1646215 := bstep (se 1 (by rfl) ⟨1234661, by rfl⟩ : syracuseStep 1646215 = 2469323) B2469323
theorem B1646223 : Blo 1646022 1646223 := bstep (se 1 (by rfl) ⟨1234667, by rfl⟩ : syracuseStep 1646223 = 2469335) B2469335
theorem B2637497 : Blo 1646022 2637497 := bstep (se 2 (by rfl) ⟨989061, by rfl⟩ : syracuseStep 2637497 = 1978123) B1978123
theorem B1646267 : Blo 1646022 1646267 := bstep (se 1 (by rfl) ⟨1234700, by rfl⟩ : syracuseStep 1646267 = 2469401) B2469401
theorem B1646343 : Blo 1646022 1646343 := bstep (se 1 (by rfl) ⟨1234757, by rfl⟩ : syracuseStep 1646343 = 2469515) B2469515
theorem B1646351 : Blo 1646022 1646351 := bstep (se 1 (by rfl) ⟨1234763, by rfl⟩ : syracuseStep 1646351 = 2469527) B2469527
theorem B4169515 : Blo 1646022 4169515 := bstep (se 1 (by rfl) ⟨3127136, by rfl⟩ : syracuseStep 4169515 = 6254273) B6254273
theorem B11870003 : Blo 1646022 11870003 := bstep (se 1 (by rfl) ⟨8902502, by rfl⟩ : syracuseStep 11870003 = 17805005) B17805005
theorem B1646395 : Blo 1646022 1646395 := bstep (se 1 (by rfl) ⟨1234796, by rfl⟩ : syracuseStep 1646395 = 2469593) B2469593
theorem B6250355 : Blo 1646022 6250355 := bstep (se 1 (by rfl) ⟨4687766, by rfl⟩ : syracuseStep 6250355 = 9375533) B9375533
theorem B1646471 : Blo 1646022 1646471 := bstep (se 1 (by rfl) ⟨1234853, by rfl⟩ : syracuseStep 1646471 = 2469707) B2469707
theorem B1646479 : Blo 1646022 1646479 := bstep (se 1 (by rfl) ⟨1234859, by rfl⟩ : syracuseStep 1646479 = 2469719) B2469719
theorem B12672931 : Blo 1646022 12672931 := bstep (se 1 (by rfl) ⟨9504698, by rfl⟩ : syracuseStep 12672931 = 19009397) B19009397
theorem B4169657 : Blo 1646022 4169657 := bstep (se 2 (by rfl) ⟨1563621, by rfl⟩ : syracuseStep 4169657 = 3127243) B3127243
theorem B1646523 : Blo 1646022 1646523 := bstep (se 1 (by rfl) ⟨1234892, by rfl⟩ : syracuseStep 1646523 = 2469785) B2469785
theorem B1646631 : Blo 1646022 1646631 := bstep (se 1 (by rfl) ⟨1234973, by rfl⟩ : syracuseStep 1646631 = 2469947) B2469947
theorem B6250553 : Blo 1646022 6250553 := bstep (se 2 (by rfl) ⟨2343957, by rfl⟩ : syracuseStep 6250553 = 4687915) B4687915
theorem B1646671 : Blo 1646022 1646671 := bstep (se 1 (by rfl) ⟨1235003, by rfl⟩ : syracuseStep 1646671 = 2470007) B2470007
theorem B1646687 : Blo 1646022 1646687 := bstep (se 1 (by rfl) ⟨1235015, by rfl⟩ : syracuseStep 1646687 = 2470031) B2470031
theorem B5275763 : Blo 1646022 5275763 := bstep (se 1 (by rfl) ⟨3956822, by rfl⟩ : syracuseStep 5275763 = 7913645) B7913645
theorem B1646715 : Blo 1646022 1646715 := bstep (se 1 (by rfl) ⟨1235036, by rfl⟩ : syracuseStep 1646715 = 2470073) B2470073
theorem B1646767 : Blo 1646022 1646767 := bstep (se 1 (by rfl) ⟨1235075, by rfl⟩ : syracuseStep 1646767 = 2470151) B2470151
theorem B1646791 : Blo 1646022 1646791 := bstep (se 1 (by rfl) ⟨1235093, by rfl⟩ : syracuseStep 1646791 = 2470187) B2470187
theorem B1646811 : Blo 1646022 1646811 := bstep (se 1 (by rfl) ⟨1235108, by rfl⟩ : syracuseStep 1646811 = 2470217) B2470217
theorem B1646887 : Blo 1646022 1646887 := bstep (se 1 (by rfl) ⟨1235165, by rfl⟩ : syracuseStep 1646887 = 2470331) B2470331
theorem B32096587 : Blo 1646022 32096587 := bstep (se 1 (by rfl) ⟨24072440, by rfl⟩ : syracuseStep 32096587 = 48144881) B48144881
theorem B1646927 : Blo 1646022 1646927 := bstep (se 1 (by rfl) ⟨1235195, by rfl⟩ : syracuseStep 1646927 = 2470391) B2470391
theorem B1646943 : Blo 1646022 1646943 := bstep (se 1 (by rfl) ⟨1235207, by rfl⟩ : syracuseStep 1646943 = 2470415) B2470415
theorem B1646971 : Blo 1646022 1646971 := bstep (se 1 (by rfl) ⟨1235228, by rfl⟩ : syracuseStep 1646971 = 2470457) B2470457
theorem B12501377 : Blo 1646022 12501377 := bstep (se 2 (by rfl) ⟨4688016, by rfl⟩ : syracuseStep 12501377 = 9376033) B9376033
theorem B9380225 : Blo 1646022 9380225 := bstep (se 2 (by rfl) ⟨3517584, by rfl⟩ : syracuseStep 9380225 = 7035169) B7035169
theorem B4170113 : Blo 1646022 4170113 := bstep (se 2 (by rfl) ⟨1563792, by rfl⟩ : syracuseStep 4170113 = 3127585) B3127585
theorem B1647023 : Blo 1646022 1647023 := bstep (se 1 (by rfl) ⟨1235267, by rfl⟩ : syracuseStep 1647023 = 2470535) B2470535
theorem B1647047 : Blo 1646022 1647047 := bstep (se 1 (by rfl) ⟨1235285, by rfl⟩ : syracuseStep 1647047 = 2470571) B2470571
theorem B1647067 : Blo 1646022 1647067 := bstep (se 1 (by rfl) ⟨1235300, by rfl⟩ : syracuseStep 1647067 = 2470601) B2470601
theorem B13353497 : Blo 1646022 13353497 := bstep (se 2 (by rfl) ⟨5007561, by rfl⟩ : syracuseStep 13353497 = 10015123) B10015123
theorem B1851943 : Blo 1646022 1851943 := bstep (se 1 (by rfl) ⟨1388957, by rfl⟩ : syracuseStep 1851943 = 2777915) B2777915
theorem B1647143 : Blo 1646022 1647143 := bstep (se 1 (by rfl) ⟨1235357, by rfl⟩ : syracuseStep 1647143 = 2470715) B2470715
theorem B1647183 : Blo 1646022 1647183 := bstep (se 1 (by rfl) ⟨1235387, by rfl⟩ : syracuseStep 1647183 = 2470775) B2470775
theorem B1647199 : Blo 1646022 1647199 := bstep (se 1 (by rfl) ⟨1235399, by rfl⟩ : syracuseStep 1647199 = 2470799) B2470799
theorem B1647227 : Blo 1646022 1647227 := bstep (se 1 (by rfl) ⟨1235420, by rfl⟩ : syracuseStep 1647227 = 2470841) B2470841
theorem B6341267 : Blo 1646022 6341267 := bstep (se 1 (by rfl) ⟨4755950, by rfl⟩ : syracuseStep 6341267 = 9511901) B9511901
theorem B1647279 : Blo 1646022 1647279 := bstep (se 1 (by rfl) ⟨1235459, by rfl⟩ : syracuseStep 1647279 = 2470919) B2470919
theorem B1647303 : Blo 1646022 1647303 := bstep (se 1 (by rfl) ⟨1235477, by rfl⟩ : syracuseStep 1647303 = 2470955) B2470955
theorem B1647323 : Blo 1646022 1647323 := bstep (se 1 (by rfl) ⟨1235492, by rfl⟩ : syracuseStep 1647323 = 2470985) B2470985
theorem B1647399 : Blo 1646022 1647399 := bstep (se 1 (by rfl) ⟨1235549, by rfl⟩ : syracuseStep 1647399 = 2471099) B2471099
theorem B3703625 : Blo 1646022 3703625 := bstep (se 2 (by rfl) ⟨1388859, by rfl⟩ : syracuseStep 3703625 = 2777719) B2777719
theorem B9380681 : Blo 1646022 9380681 := bstep (se 2 (by rfl) ⟨3517755, by rfl⟩ : syracuseStep 9380681 = 7035511) B7035511
theorem B1647439 : Blo 1646022 1647439 := bstep (se 1 (by rfl) ⟨1235579, by rfl⟩ : syracuseStep 1647439 = 2471159) B2471159
theorem B1647455 : Blo 1646022 1647455 := bstep (se 1 (by rfl) ⟨1235591, by rfl⟩ : syracuseStep 1647455 = 2471183) B2471183
theorem B2966377 : Blo 1646022 2966377 := bstep (se 2 (by rfl) ⟨1112391, by rfl⟩ : syracuseStep 2966377 = 2224783) B2224783
theorem B1647483 : Blo 1646022 1647483 := bstep (se 1 (by rfl) ⟨1235612, by rfl⟩ : syracuseStep 1647483 = 2471225) B2471225
theorem B1647535 : Blo 1646022 1647535 := bstep (se 1 (by rfl) ⟨1235651, by rfl⟩ : syracuseStep 1647535 = 2471303) B2471303
theorem B8340407 : Blo 1646022 8340407 := bstep (se 1 (by rfl) ⟨6255305, by rfl⟩ : syracuseStep 8340407 = 12510611) B12510611
theorem B2778043 : Blo 1646022 2778043 := bstep (se 1 (by rfl) ⟨2083532, by rfl⟩ : syracuseStep 2778043 = 4167065) B4167065
theorem B1647559 : Blo 1646022 1647559 := bstep (se 1 (by rfl) ⟨1235669, by rfl⟩ : syracuseStep 1647559 = 2471339) B2471339
theorem B1647579 : Blo 1646022 1647579 := bstep (se 1 (by rfl) ⟨1235684, by rfl⟩ : syracuseStep 1647579 = 2471369) B2471369
theorem B2638855 : Blo 1646022 2638855 := bstep (se 1 (by rfl) ⟨1979141, by rfl⟩ : syracuseStep 2638855 = 3958283) B3958283
theorem B6251539 : Blo 1646022 6251539 := bstep (se 1 (by rfl) ⟨4688654, by rfl⟩ : syracuseStep 6251539 = 9377309) B9377309
theorem B2778151 : Blo 1646022 2778151 := bstep (se 1 (by rfl) ⟨2083613, by rfl⟩ : syracuseStep 2778151 = 4167227) B4167227
theorem B1647655 : Blo 1646022 1647655 := bstep (se 1 (by rfl) ⟨1235741, by rfl⟩ : syracuseStep 1647655 = 2471483) B2471483
theorem B6677561 : Blo 1646022 6677561 := bstep (se 2 (by rfl) ⟨2504085, by rfl⟩ : syracuseStep 6677561 = 5008171) B5008171
theorem B1647695 : Blo 1646022 1647695 := bstep (se 1 (by rfl) ⟨1235771, by rfl⟩ : syracuseStep 1647695 = 2471543) B2471543
theorem B1647711 : Blo 1646022 1647711 := bstep (se 1 (by rfl) ⟨1235783, by rfl⟩ : syracuseStep 1647711 = 2471567) B2471567
theorem B1647739 : Blo 1646022 1647739 := bstep (se 1 (by rfl) ⟨1235804, by rfl⟩ : syracuseStep 1647739 = 2471609) B2471609
theorem B5555357 : Blo 1646022 5555357 := bstep (se 3 (by rfl) ⟨1041629, by rfl⟩ : syracuseStep 5555357 = 2083259) B2083259
theorem B4170923 : Blo 1646022 4170923 := bstep (se 1 (by rfl) ⟨3128192, by rfl⟩ : syracuseStep 4170923 = 6256385) B6256385
theorem B1647791 : Blo 1646022 1647791 := bstep (se 1 (by rfl) ⟨1235843, by rfl⟩ : syracuseStep 1647791 = 2471687) B2471687
theorem B1647815 : Blo 1646022 1647815 := bstep (se 1 (by rfl) ⟨1235861, by rfl⟩ : syracuseStep 1647815 = 2471723) B2471723
theorem B1647835 : Blo 1646022 1647835 := bstep (se 1 (by rfl) ⟨1235876, by rfl⟩ : syracuseStep 1647835 = 2471753) B2471753
theorem B1647911 : Blo 1646022 1647911 := bstep (se 1 (by rfl) ⟨1235933, by rfl⟩ : syracuseStep 1647911 = 2471867) B2471867
theorem B1647951 : Blo 1646022 1647951 := bstep (se 1 (by rfl) ⟨1235963, by rfl⟩ : syracuseStep 1647951 = 2471927) B2471927
theorem B1647967 : Blo 1646022 1647967 := bstep (se 1 (by rfl) ⟨1235975, by rfl⟩ : syracuseStep 1647967 = 2471951) B2471951
theorem B3958121 : Blo 1646022 3958121 := bstep (se 2 (by rfl) ⟨1484295, by rfl⟩ : syracuseStep 3958121 = 2968591) B2968591
theorem B2778475 : Blo 1646022 2778475 := bstep (se 1 (by rfl) ⟨2083856, by rfl⟩ : syracuseStep 2778475 = 4167713) B4167713
theorem B1647995 : Blo 1646022 1647995 := bstep (se 1 (by rfl) ⟨1235996, by rfl⟩ : syracuseStep 1647995 = 2471993) B2471993
theorem B6677903 : Blo 1646022 6677903 := bstep (se 1 (by rfl) ⟨5008427, by rfl⟩ : syracuseStep 6677903 = 10016855) B10016855
theorem B2639279 : Blo 1646022 2639279 := bstep (se 1 (by rfl) ⟨1979459, by rfl⟩ : syracuseStep 2639279 = 3958919) B3958919
theorem B3704417 : Blo 1646022 3704417 := bstep (se 2 (by rfl) ⟨1389156, by rfl⟩ : syracuseStep 3704417 = 2778313) B2778313
theorem B28124819 : Blo 1646022 28124819 := bstep (se 1 (by rfl) ⟨21093614, by rfl⟩ : syracuseStep 28124819 = 42187229) B42187229
theorem B5555897 : Blo 1646022 5555897 := bstep (se 2 (by rfl) ⟨2083461, by rfl⟩ : syracuseStep 5555897 = 4166923) B4166923
theorem B21399385 : Blo 1646022 21399385 := bstep (se 2 (by rfl) ⟨8024769, by rfl⟩ : syracuseStep 21399385 = 16049539) B16049539
theorem B16893791 : Blo 1646022 16893791 := bstep (se 1 (by rfl) ⟨12670343, by rfl⟩ : syracuseStep 16893791 = 25340687) B25340687
theorem B2967401 : Blo 1646022 2967401 := bstep (se 2 (by rfl) ⟨1112775, by rfl⟩ : syracuseStep 2967401 = 2225551) B2225551
theorem B3704759 : Blo 1646022 3704759 := bstep (se 1 (by rfl) ⟨2778569, by rfl⟩ : syracuseStep 3704759 = 5557139) B5557139
theorem B3516347 : Blo 1646022 3516347 := bstep (se 1 (by rfl) ⟨2637260, by rfl⟩ : syracuseStep 3516347 = 5274521) B5274521
theorem B1853563 : Blo 1646022 1853563 := bstep (se 1 (by rfl) ⟨1390172, by rfl⟩ : syracuseStep 1853563 = 2780345) B2780345
theorem B7039133 : Blo 1646022 7039133 := bstep (se 3 (by rfl) ⟨1319837, by rfl⟩ : syracuseStep 7039133 = 2639675) B2639675
theorem B2345159 : Blo 1646022 2345159 := bstep (se 1 (by rfl) ⟨1758869, by rfl⟩ : syracuseStep 2345159 = 3517739) B3517739
theorem B5556491 : Blo 1646022 5556491 := bstep (se 1 (by rfl) ⟨4167368, by rfl⟩ : syracuseStep 5556491 = 8334737) B8334737
theorem B8341865 : Blo 1646022 8341865 := bstep (se 2 (by rfl) ⟨3128199, by rfl⟩ : syracuseStep 8341865 = 6256399) B6256399
theorem B2779535 : Blo 1646022 2779535 := bstep (se 1 (by rfl) ⟨2084651, by rfl⟩ : syracuseStep 2779535 = 4169303) B4169303
theorem B3705353 : Blo 1646022 3705353 := bstep (se 2 (by rfl) ⟨1389507, by rfl⟩ : syracuseStep 3705353 = 2779015) B2779015
theorem B5556761 : Blo 1646022 5556761 := bstep (se 2 (by rfl) ⟨2083785, by rfl⟩ : syracuseStep 5556761 = 4167571) B4167571
theorem B11274785 : Blo 1646022 11274785 := bstep (se 2 (by rfl) ⟨4228044, by rfl⟩ : syracuseStep 11274785 = 8456089) B8456089
theorem B2779771 : Blo 1646022 2779771 := bstep (se 1 (by rfl) ⟨2084828, by rfl⟩ : syracuseStep 2779771 = 4169657) B4169657
theorem B6253271 : Blo 1646022 6253271 := bstep (se 1 (by rfl) ⟨4689953, by rfl⟩ : syracuseStep 6253271 = 9379907) B9379907
theorem B3705695 : Blo 1646022 3705695 := bstep (se 1 (by rfl) ⟨2779271, by rfl⟩ : syracuseStep 3705695 = 5558543) B5558543
theorem B3566497 : Blo 1646022 3566497 := bstep (se 2 (by rfl) ⟨1337436, by rfl⟩ : syracuseStep 3566497 = 2674873) B2674873
theorem B26717111 : Blo 1646022 26717111 := bstep (se 1 (by rfl) ⟨20037833, by rfl⟩ : syracuseStep 26717111 = 40075667) B40075667
theorem B6016007 : Blo 1646022 6016007 := bstep (se 1 (by rfl) ⟨4512005, by rfl⟩ : syracuseStep 6016007 = 9024011) B9024011
theorem B3705875 : Blo 1646022 3705875 := bstep (se 1 (by rfl) ⟨2779406, by rfl⟩ : syracuseStep 3705875 = 5558813) B5558813
theorem B2083963 : Blo 1646022 2083963 := bstep (se 1 (by rfl) ⟨1562972, by rfl⟩ : syracuseStep 2083963 = 3125945) B3125945
theorem B2469113 : Blo 1646022 2469113 := bstep (se 2 (by rfl) ⟨925917, by rfl⟩ : syracuseStep 2469113 = 1851835) B1851835
theorem B2469215 : Blo 1646022 2469215 := bstep (se 1 (by rfl) ⟨1851911, by rfl⟩ : syracuseStep 2469215 = 3703823) B3703823
theorem B3706217 : Blo 1646022 3706217 := bstep (se 2 (by rfl) ⟨1389831, by rfl⟩ : syracuseStep 3706217 = 2779663) B2779663
theorem B2469227 : Blo 1646022 2469227 := bstep (se 1 (by rfl) ⟨1851920, by rfl⟩ : syracuseStep 2469227 = 3703841) B3703841
theorem B9375101 : Blo 1646022 9375101 := bstep (se 3 (by rfl) ⟨1757831, by rfl⟩ : syracuseStep 9375101 = 3515663) B3515663
theorem B2780635 : Blo 1646022 2780635 := bstep (se 1 (by rfl) ⟨2085476, by rfl⟩ : syracuseStep 2780635 = 4170953) B4170953
theorem B16043507 : Blo 1646022 16043507 := bstep (se 1 (by rfl) ⟨12032630, by rfl⟩ : syracuseStep 16043507 = 24065261) B24065261
theorem B2469455 : Blo 1646022 2469455 := bstep (se 1 (by rfl) ⟨1852091, by rfl⟩ : syracuseStep 2469455 = 3704183) B3704183
theorem B5557895 : Blo 1646022 5557895 := bstep (se 1 (by rfl) ⟨4168421, by rfl⟩ : syracuseStep 5557895 = 8336843) B8336843
theorem B5557949 : Blo 1646022 5557949 := bstep (se 3 (by rfl) ⟨1042115, by rfl⟩ : syracuseStep 5557949 = 2084231) B2084231
theorem B2469575 : Blo 1646022 2469575 := bstep (se 1 (by rfl) ⟨1852181, by rfl⟩ : syracuseStep 2469575 = 3704363) B3704363
theorem B5558111 : Blo 1646022 5558111 := bstep (se 1 (by rfl) ⟨4168583, by rfl⟩ : syracuseStep 5558111 = 8337167) B8337167
theorem B2469737 : Blo 1646022 2469737 := bstep (se 2 (by rfl) ⟨926151, by rfl⟩ : syracuseStep 2469737 = 1852303) B1852303
theorem B1978219 : Blo 1646022 1978219 := bstep (se 1 (by rfl) ⟨1483664, by rfl⟩ : syracuseStep 1978219 = 2967329) B2967329
theorem B8335223 : Blo 1646022 8335223 := bstep (se 1 (by rfl) ⟨6251417, by rfl⟩ : syracuseStep 8335223 = 12502835) B12502835
theorem B6254455 : Blo 1646022 6254455 := bstep (se 1 (by rfl) ⟨4690841, by rfl⟩ : syracuseStep 6254455 = 9381683) B9381683
theorem B4689839 : Blo 1646022 4689839 := bstep (se 1 (by rfl) ⟨3517379, by rfl⟩ : syracuseStep 4689839 = 7034759) B7034759
theorem B2969519 : Blo 1646022 2969519 := bstep (se 1 (by rfl) ⟨2227139, by rfl⟩ : syracuseStep 2969519 = 4454279) B4454279
theorem B2469815 : Blo 1646022 2469815 := bstep (se 1 (by rfl) ⟨1852361, by rfl⟩ : syracuseStep 2469815 = 3704723) B3704723
theorem B16912313 : Blo 1646022 16912313 := bstep (se 2 (by rfl) ⟨6342117, by rfl⟩ : syracuseStep 16912313 = 12684235) B12684235
theorem B3706811 : Blo 1646022 3706811 := bstep (se 1 (by rfl) ⟨2780108, by rfl⟩ : syracuseStep 3706811 = 5560217) B5560217
theorem B2469851 : Blo 1646022 2469851 := bstep (se 1 (by rfl) ⟨1852388, by rfl⟩ : syracuseStep 2469851 = 3704777) B3704777
theorem B5558273 : Blo 1646022 5558273 := bstep (se 2 (by rfl) ⟨2084352, by rfl⟩ : syracuseStep 5558273 = 4168705) B4168705
theorem B30052367 : Blo 1646022 30052367 := bstep (se 1 (by rfl) ⟨22539275, by rfl⟩ : syracuseStep 30052367 = 45078551) B45078551
theorem B3706937 : Blo 1646022 3706937 := bstep (se 2 (by rfl) ⟨1390101, by rfl⟩ : syracuseStep 3706937 = 2780203) B2780203
theorem B14463053 : Blo 1646022 14463053 := bstep (se 3 (by rfl) ⟨2711822, by rfl⟩ : syracuseStep 14463053 = 5423645) B5423645
theorem B11874385 : Blo 1646022 11874385 := bstep (se 2 (by rfl) ⟨4452894, by rfl⟩ : syracuseStep 11874385 = 8905789) B8905789
theorem B7131293 : Blo 1646022 7131293 := bstep (se 3 (by rfl) ⟨1337117, by rfl⟩ : syracuseStep 7131293 = 2674235) B2674235
theorem B3125459 : Blo 1646022 3125459 := bstep (se 1 (by rfl) ⟨2344094, by rfl⟩ : syracuseStep 3125459 = 4688189) B4688189
theorem B19009853 : Blo 1646022 19009853 := bstep (se 3 (by rfl) ⟨3564347, by rfl⟩ : syracuseStep 19009853 = 7128695) B7128695
theorem B3707279 : Blo 1646022 3707279 := bstep (se 1 (by rfl) ⟨2780459, by rfl⟩ : syracuseStep 3707279 = 5560919) B5560919
theorem B2470319 : Blo 1646022 2470319 := bstep (se 1 (by rfl) ⟨1852739, by rfl⟩ : syracuseStep 2470319 = 3705479) B3705479
theorem B2470409 : Blo 1646022 2470409 := bstep (se 2 (by rfl) ⟨926403, by rfl⟩ : syracuseStep 2470409 = 1852807) B1852807
theorem B2470439 : Blo 1646022 2470439 := bstep (se 1 (by rfl) ⟨1852829, by rfl⟩ : syracuseStep 2470439 = 3705659) B3705659
theorem B2470523 : Blo 1646022 2470523 := bstep (se 1 (by rfl) ⟨1852892, by rfl⟩ : syracuseStep 2470523 = 3705785) B3705785
theorem B7033529 : Blo 1646022 7033529 := bstep (se 2 (by rfl) ⟨2637573, by rfl⟩ : syracuseStep 7033529 = 5275147) B5275147
theorem B3707603 : Blo 1646022 3707603 := bstep (se 1 (by rfl) ⟨2780702, by rfl⟩ : syracuseStep 3707603 = 5561405) B5561405
theorem B2470649 : Blo 1646022 2470649 := bstep (se 2 (by rfl) ⟨926493, by rfl⟩ : syracuseStep 2470649 = 1852987) B1852987
theorem B5559083 : Blo 1646022 5559083 := bstep (se 1 (by rfl) ⟨4169312, by rfl⟩ : syracuseStep 5559083 = 8338625) B8338625
theorem B6255427 : Blo 1646022 6255427 := bstep (se 1 (by rfl) ⟨4691570, by rfl⟩ : syracuseStep 6255427 = 9383141) B9383141
theorem B3126089 : Blo 1646022 3126089 := bstep (se 2 (by rfl) ⟨1172283, by rfl⟩ : syracuseStep 3126089 = 2344567) B2344567
theorem B2470751 : Blo 1646022 2470751 := bstep (se 1 (by rfl) ⟨1853063, by rfl⟩ : syracuseStep 2470751 = 3706127) B3706127
theorem B2470763 : Blo 1646022 2470763 := bstep (se 1 (by rfl) ⟨1853072, by rfl⟩ : syracuseStep 2470763 = 3706145) B3706145
theorem B25342895 : Blo 1646022 25342895 := bstep (se 1 (by rfl) ⟨19007171, by rfl⟩ : syracuseStep 25342895 = 38014343) B38014343
theorem B10548143 : Blo 1646022 10548143 := bstep (se 1 (by rfl) ⟨7911107, by rfl⟩ : syracuseStep 10548143 = 15822215) B15822215
theorem B5559353 : Blo 1646022 5559353 := bstep (se 2 (by rfl) ⟨2084757, by rfl⟩ : syracuseStep 5559353 = 4169515) B4169515
theorem B2470991 : Blo 1646022 2470991 := bstep (se 1 (by rfl) ⟨1853243, by rfl⟩ : syracuseStep 2470991 = 3706487) B3706487
theorem B6255731 : Blo 1646022 6255731 := bstep (se 1 (by rfl) ⟨4691798, by rfl⟩ : syracuseStep 6255731 = 9383597) B9383597
theorem B1758331 : Blo 1646022 1758331 := bstep (se 1 (by rfl) ⟨1318748, by rfl⟩ : syracuseStep 1758331 = 2637497) B2637497
theorem B89158805 : Blo 1646022 89158805 := bstep (se 6 (by rfl) ⟨2089659, by rfl⟩ : syracuseStep 89158805 = 4179319) B4179319
theorem B12514499 : Blo 1646022 12514499 := bstep (se 1 (by rfl) ⟨9385874, by rfl⟩ : syracuseStep 12514499 = 18771749) B18771749
theorem B2471111 : Blo 1646022 2471111 := bstep (se 1 (by rfl) ⟨1853333, by rfl⟩ : syracuseStep 2471111 = 3706667) B3706667
theorem B16897241 : Blo 1646022 16897241 := bstep (se 2 (by rfl) ⟨6336465, by rfl⟩ : syracuseStep 16897241 = 12672931) B12672931
theorem B4166903 : Blo 1646022 4166903 := bstep (se 1 (by rfl) ⟨3125177, by rfl⟩ : syracuseStep 4166903 = 6250355) B6250355
theorem B2471273 : Blo 1646022 2471273 := bstep (se 2 (by rfl) ⟨926727, by rfl⟩ : syracuseStep 2471273 = 1853455) B1853455
theorem B5559677 : Blo 1646022 5559677 := bstep (se 3 (by rfl) ⟨1042439, by rfl⟩ : syracuseStep 5559677 = 2084879) B2084879
theorem B94950791 : Blo 1646022 94950791 := bstep (se 1 (by rfl) ⟨71213093, by rfl⟩ : syracuseStep 94950791 = 142426187) B142426187
theorem B2471351 : Blo 1646022 2471351 := bstep (se 1 (by rfl) ⟨1853513, by rfl⟩ : syracuseStep 2471351 = 3707027) B3707027
theorem B7910875 : Blo 1646022 7910875 := bstep (se 1 (by rfl) ⟨5933156, by rfl⟩ : syracuseStep 7910875 = 11866313) B11866313
theorem B2471387 : Blo 1646022 2471387 := bstep (se 1 (by rfl) ⟨1853540, by rfl⟩ : syracuseStep 2471387 = 3707081) B3707081
theorem B98924093 : Blo 1646022 98924093 := bstep (se 3 (by rfl) ⟨18548267, by rfl⟩ : syracuseStep 98924093 = 37096535) B37096535
theorem B6256187 : Blo 1646022 6256187 := bstep (se 1 (by rfl) ⟨4692140, by rfl⟩ : syracuseStep 6256187 = 9384281) B9384281
theorem B3126863 : Blo 1646022 3126863 := bstep (se 1 (by rfl) ⟨2345147, by rfl⟩ : syracuseStep 3126863 = 4690295) B4690295
theorem B5559947 : Blo 1646022 5559947 := bstep (se 1 (by rfl) ⟨4169960, by rfl⟩ : syracuseStep 5559947 = 8339921) B8339921
theorem B7509719 : Blo 1646022 7509719 := bstep (se 1 (by rfl) ⟨5632289, by rfl⟩ : syracuseStep 7509719 = 11264579) B11264579
theorem B13358915 : Blo 1646022 13358915 := bstep (se 1 (by rfl) ⟨10019186, by rfl⟩ : syracuseStep 13358915 = 20038373) B20038373
theorem B2471855 : Blo 1646022 2471855 := bstep (se 1 (by rfl) ⟨1853891, by rfl⟩ : syracuseStep 2471855 = 3707783) B3707783
theorem B2471945 : Blo 1646022 2471945 := bstep (se 2 (by rfl) ⟨926979, by rfl⟩ : syracuseStep 2471945 = 1853959) B1853959
theorem B10557469 : Blo 1646022 10557469 := bstep (se 3 (by rfl) ⟨1979525, by rfl⟩ : syracuseStep 10557469 = 3959051) B3959051
theorem B2471975 : Blo 1646022 2471975 := bstep (se 1 (by rfl) ⟨1853981, by rfl⟩ : syracuseStep 2471975 = 3707963) B3707963
theorem B114071597 : Blo 1646022 114071597 := bstep (se 3 (by rfl) ⟨21388424, by rfl⟩ : syracuseStep 114071597 = 42776849) B42776849
theorem B4511801 : Blo 1646022 4511801 := bstep (se 2 (by rfl) ⟨1691925, by rfl⟩ : syracuseStep 4511801 = 3383851) B3383851
theorem B27080837 : Blo 1646022 27080837 := bstep (se 4 (by rfl) ⟨2538828, by rfl⟩ : syracuseStep 27080837 = 5077657) B5077657
theorem B11868389 : Blo 1646022 11868389 := bstep (se 4 (by rfl) ⟨1112661, by rfl⟩ : syracuseStep 11868389 = 2225323) B2225323
theorem B3168695 : Blo 1646022 3168695 := bstep (se 1 (by rfl) ⟨2376521, by rfl⟩ : syracuseStep 3168695 = 4753043) B4753043
theorem B2505143 : Blo 1646022 2505143 := bstep (se 1 (by rfl) ⟨1878857, by rfl⟩ : syracuseStep 2505143 = 3757715) B3757715
theorem B4692505 : Blo 1646022 4692505 := bstep (se 2 (by rfl) ⟨1759689, by rfl⟩ : syracuseStep 4692505 = 3519379) B3519379
theorem B5560865 : Blo 1646022 5560865 := bstep (se 2 (by rfl) ⟨2085324, by rfl⟩ : syracuseStep 5560865 = 4170649) B4170649
theorem B4168331 : Blo 1646022 4168331 := bstep (se 1 (by rfl) ⟨3126248, by rfl⟩ : syracuseStep 4168331 = 6252497) B6252497
theorem B5561081 : Blo 1646022 5561081 := bstep (se 2 (by rfl) ⟨2085405, by rfl⟩ : syracuseStep 5561081 = 4170811) B4170811
theorem B14064461 : Blo 1646022 14064461 := bstep (se 3 (by rfl) ⟨2637086, by rfl⟩ : syracuseStep 14064461 = 5274173) B5274173
theorem B4168543 : Blo 1646022 4168543 := bstep (se 1 (by rfl) ⟨3126407, by rfl⟩ : syracuseStep 4168543 = 6252815) B6252815
theorem B2636651 : Blo 1646022 2636651 := bstep (se 1 (by rfl) ⟨1977488, by rfl⟩ : syracuseStep 2636651 = 3954977) B3954977
theorem B1670063 : Blo 1646022 1670063 := bstep (se 1 (by rfl) ⟨1252547, by rfl⟩ : syracuseStep 1670063 = 2505095) B2505095
theorem B2505691 : Blo 1646022 2505691 := bstep (se 1 (by rfl) ⟨1879268, by rfl⟩ : syracuseStep 2505691 = 3758537) B3758537
theorem B5561351 : Blo 1646022 5561351 := bstep (se 1 (by rfl) ⟨4171013, by rfl⟩ : syracuseStep 5561351 = 8342027) B8342027
theorem B6339665 : Blo 1646022 6339665 := bstep (se 2 (by rfl) ⟨2377374, by rfl⟩ : syracuseStep 6339665 = 4754749) B4754749
theorem B5561459 : Blo 1646022 5561459 := bstep (se 1 (by rfl) ⟨4171094, by rfl⟩ : syracuseStep 5561459 = 8342189) B8342189
theorem B6339779 : Blo 1646022 6339779 := bstep (se 1 (by rfl) ⟨4754834, by rfl⟩ : syracuseStep 6339779 = 9509669) B9509669
theorem B3128519 : Blo 1646022 3128519 := bstep (se 1 (by rfl) ⟨2346389, by rfl⟩ : syracuseStep 3128519 = 4692779) B4692779
theorem B15834359 : Blo 1646022 15834359 := bstep (se 1 (by rfl) ⟨11875769, by rfl⟩ : syracuseStep 15834359 = 23751539) B23751539
theorem B15826211 : Blo 1646022 15826211 := bstep (se 1 (by rfl) ⟨11869658, by rfl⟩ : syracuseStep 15826211 = 23739317) B23739317
theorem B5561729 : Blo 1646022 5561729 := bstep (se 2 (by rfl) ⟨2085648, by rfl⟩ : syracuseStep 5561729 = 4171297) B4171297
theorem B1646023 : Blo 1646022 1646023 := bstep (se 1 (by rfl) ⟨1234517, by rfl⟩ : syracuseStep 1646023 = 2469035) B2469035
theorem B1646043 : Blo 1646022 1646043 := bstep (se 1 (by rfl) ⟨1234532, by rfl⟩ : syracuseStep 1646043 = 2469065) B2469065
theorem B31653341 : Blo 1646022 31653341 := bstep (se 3 (by rfl) ⟨5935001, by rfl⟩ : syracuseStep 31653341 = 11870003) B11870003
theorem B1646119 : Blo 1646022 1646119 := bstep (se 1 (by rfl) ⟨1234589, by rfl⟩ : syracuseStep 1646119 = 2469179) B2469179
theorem B1646159 : Blo 1646022 1646159 := bstep (se 1 (by rfl) ⟨1234619, by rfl⟩ : syracuseStep 1646159 = 2469239) B2469239
theorem B14270039 : Blo 1646022 14270039 := bstep (se 1 (by rfl) ⟨10702529, by rfl⟩ : syracuseStep 14270039 = 21405059) B21405059
theorem B1646175 : Blo 1646022 1646175 := bstep (se 1 (by rfl) ⟨1234631, by rfl⟩ : syracuseStep 1646175 = 2469263) B2469263
theorem B6250081 : Blo 1646022 6250081 := bstep (se 2 (by rfl) ⟨2343780, by rfl⟩ : syracuseStep 6250081 = 4687561) B4687561
theorem B1646203 : Blo 1646022 1646203 := bstep (se 1 (by rfl) ⟨1234652, by rfl⟩ : syracuseStep 1646203 = 2469305) B2469305
theorem B9379475 : Blo 1646022 9379475 := bstep (se 1 (by rfl) ⟨7034606, by rfl⟩ : syracuseStep 9379475 = 14069213) B14069213
theorem B1646255 : Blo 1646022 1646255 := bstep (se 1 (by rfl) ⟨1234691, by rfl⟩ : syracuseStep 1646255 = 2469383) B2469383
theorem B1646279 : Blo 1646022 1646279 := bstep (se 1 (by rfl) ⟨1234709, by rfl⟩ : syracuseStep 1646279 = 2469419) B2469419
theorem B1646299 : Blo 1646022 1646299 := bstep (se 1 (by rfl) ⟨1234724, by rfl⟩ : syracuseStep 1646299 = 2469449) B2469449
theorem B4169465 : Blo 1646022 4169465 := bstep (se 2 (by rfl) ⟨1563549, by rfl⟩ : syracuseStep 4169465 = 3127099) B3127099
theorem B1646375 : Blo 1646022 1646375 := bstep (se 1 (by rfl) ⟨1234781, by rfl⟩ : syracuseStep 1646375 = 2469563) B2469563
theorem B10428227 : Blo 1646022 10428227 := bstep (se 1 (by rfl) ⟨7821170, by rfl⟩ : syracuseStep 10428227 = 15642341) B15642341
theorem B1646415 : Blo 1646022 1646415 := bstep (se 1 (by rfl) ⟨1234811, by rfl⟩ : syracuseStep 1646415 = 2469623) B2469623
theorem B1646431 : Blo 1646022 1646431 := bstep (se 1 (by rfl) ⟨1234823, by rfl⟩ : syracuseStep 1646431 = 2469647) B2469647
theorem B1646459 : Blo 1646022 1646459 := bstep (se 1 (by rfl) ⟨1234844, by rfl⟩ : syracuseStep 1646459 = 2469689) B2469689
theorem B1646511 : Blo 1646022 1646511 := bstep (se 1 (by rfl) ⟨1234883, by rfl⟩ : syracuseStep 1646511 = 2469767) B2469767
theorem B1646535 : Blo 1646022 1646535 := bstep (se 1 (by rfl) ⟨1234901, by rfl⟩ : syracuseStep 1646535 = 2469803) B2469803
theorem B1646555 : Blo 1646022 1646555 := bstep (se 1 (by rfl) ⟨1234916, by rfl⟩ : syracuseStep 1646555 = 2469833) B2469833
theorem B9642035 : Blo 1646022 9642035 := bstep (se 1 (by rfl) ⟨7231526, by rfl⟩ : syracuseStep 9642035 = 14463053) B14463053
theorem B12673235 : Blo 1646022 12673235 := bstep (se 1 (by rfl) ⟨9504926, by rfl⟩ : syracuseStep 12673235 = 19009853) B19009853
theorem B1646879 : Blo 1646022 1646879 := bstep (se 1 (by rfl) ⟨1235159, by rfl⟩ : syracuseStep 1646879 = 2470319) B2470319
theorem B1646939 : Blo 1646022 1646939 := bstep (se 1 (by rfl) ⟨1235204, by rfl⟩ : syracuseStep 1646939 = 2470409) B2470409
theorem B1646959 : Blo 1646022 1646959 := bstep (se 1 (by rfl) ⟨1235219, by rfl⟩ : syracuseStep 1646959 = 2470439) B2470439
theorem B1647015 : Blo 1646022 1647015 := bstep (se 1 (by rfl) ⟨1235261, by rfl⟩ : syracuseStep 1647015 = 2470523) B2470523
theorem B42795449 : Blo 1646022 42795449 := bstep (se 2 (by rfl) ⟨16048293, by rfl⟩ : syracuseStep 42795449 = 32096587) B32096587
theorem B1647099 : Blo 1646022 1647099 := bstep (se 1 (by rfl) ⟨1235324, by rfl⟩ : syracuseStep 1647099 = 2470649) B2470649
theorem B1647167 : Blo 1646022 1647167 := bstep (se 1 (by rfl) ⟨1235375, by rfl⟩ : syracuseStep 1647167 = 2470751) B2470751
theorem B1647175 : Blo 1646022 1647175 := bstep (se 1 (by rfl) ⟨1235381, by rfl⟩ : syracuseStep 1647175 = 2470763) B2470763
theorem B1647327 : Blo 1646022 1647327 := bstep (se 1 (by rfl) ⟨1235495, by rfl⟩ : syracuseStep 1647327 = 2470991) B2470991
theorem B4170487 : Blo 1646022 4170487 := bstep (se 1 (by rfl) ⟨3127865, by rfl⟩ : syracuseStep 4170487 = 6255731) B6255731
theorem B3703571 : Blo 1646022 3703571 := bstep (se 1 (by rfl) ⟨2777678, by rfl⟩ : syracuseStep 3703571 = 5555357) B5555357
theorem B1647407 : Blo 1646022 1647407 := bstep (se 1 (by rfl) ⟨1235555, by rfl⟩ : syracuseStep 1647407 = 2471111) B2471111
theorem B11264827 : Blo 1646022 11264827 := bstep (se 1 (by rfl) ⟨8448620, by rfl⟩ : syracuseStep 11264827 = 16897241) B16897241
theorem B2777935 : Blo 1646022 2777935 := bstep (se 1 (by rfl) ⟨2083451, by rfl⟩ : syracuseStep 2777935 = 4166903) B4166903
theorem B2638747 : Blo 1646022 2638747 := bstep (se 1 (by rfl) ⟨1979060, by rfl⟩ : syracuseStep 2638747 = 3958121) B3958121
theorem B1647515 : Blo 1646022 1647515 := bstep (se 1 (by rfl) ⟨1235636, by rfl⟩ : syracuseStep 1647515 = 2471273) B2471273
theorem B63300527 : Blo 1646022 63300527 := bstep (se 1 (by rfl) ⟨47475395, by rfl⟩ : syracuseStep 63300527 = 94950791) B94950791
theorem B1647567 : Blo 1646022 1647567 := bstep (se 1 (by rfl) ⟨1235675, by rfl⟩ : syracuseStep 1647567 = 2471351) B2471351
theorem B1647591 : Blo 1646022 1647591 := bstep (se 1 (by rfl) ⟨1235693, by rfl⟩ : syracuseStep 1647591 = 2471387) B2471387
theorem B4170791 : Blo 1646022 4170791 := bstep (se 1 (by rfl) ⟨3128093, by rfl⟩ : syracuseStep 4170791 = 6256187) B6256187
theorem B8340569 : Blo 1646022 8340569 := bstep (se 2 (by rfl) ⟨3127713, by rfl⟩ : syracuseStep 8340569 = 6255427) B6255427
theorem B3703931 : Blo 1646022 3703931 := bstep (se 1 (by rfl) ⟨2777948, by rfl⟩ : syracuseStep 3703931 = 5555897) B5555897
theorem B5006479 : Blo 1646022 5006479 := bstep (se 1 (by rfl) ⟨3754859, by rfl⟩ : syracuseStep 5006479 = 7509719) B7509719
theorem B8905943 : Blo 1646022 8905943 := bstep (se 1 (by rfl) ⟨6679457, by rfl⟩ : syracuseStep 8905943 = 13358915) B13358915
theorem B3704057 : Blo 1646022 3704057 := bstep (se 2 (by rfl) ⟨1389021, by rfl⟩ : syracuseStep 3704057 = 2778043) B2778043
theorem B1647903 : Blo 1646022 1647903 := bstep (se 1 (by rfl) ⟨1235927, by rfl⟩ : syracuseStep 1647903 = 2471855) B2471855
theorem B2344231 : Blo 1646022 2344231 := bstep (se 1 (by rfl) ⟨1758173, by rfl⟩ : syracuseStep 2344231 = 3516347) B3516347
theorem B1647963 : Blo 1646022 1647963 := bstep (se 1 (by rfl) ⟨1235972, by rfl⟩ : syracuseStep 1647963 = 2471945) B2471945
theorem B1647983 : Blo 1646022 1647983 := bstep (se 1 (by rfl) ⟨1235987, by rfl⟩ : syracuseStep 1647983 = 2471975) B2471975
theorem B76047731 : Blo 1646022 76047731 := bstep (se 1 (by rfl) ⟨57035798, by rfl⟩ : syracuseStep 76047731 = 114071597) B114071597
theorem B3007867 : Blo 1646022 3007867 := bstep (se 1 (by rfl) ⟨2255900, by rfl⟩ : syracuseStep 3007867 = 4511801) B4511801
theorem B3704201 : Blo 1646022 3704201 := bstep (se 2 (by rfl) ⟨1389075, by rfl⟩ : syracuseStep 3704201 = 2778151) B2778151
theorem B2778617 : Blo 1646022 2778617 := bstep (se 2 (by rfl) ⟨1041981, by rfl⟩ : syracuseStep 2778617 = 2083963) B2083963
theorem B3704327 : Blo 1646022 3704327 := bstep (se 1 (by rfl) ⟨2778245, by rfl⟩ : syracuseStep 3704327 = 5556491) B5556491
theorem B1853023 : Blo 1646022 1853023 := bstep (se 1 (by rfl) ⟨1389767, by rfl⟩ : syracuseStep 1853023 = 2779535) B2779535
theorem B3704507 : Blo 1646022 3704507 := bstep (se 1 (by rfl) ⟨2778380, by rfl⟩ : syracuseStep 3704507 = 5556761) B5556761
theorem B16910045 : Blo 1646022 16910045 := bstep (se 3 (by rfl) ⟨3170633, by rfl⟩ : syracuseStep 16910045 = 6341267) B6341267
theorem B2778887 : Blo 1646022 2778887 := bstep (se 1 (by rfl) ⟨2084165, by rfl⟩ : syracuseStep 2778887 = 4168331) B4168331
theorem B3704633 : Blo 1646022 3704633 := bstep (se 2 (by rfl) ⟨1389237, by rfl⟩ : syracuseStep 3704633 = 2778475) B2778475
theorem B17811407 : Blo 1646022 17811407 := bstep (se 1 (by rfl) ⟨13358555, by rfl⟩ : syracuseStep 17811407 = 26717111) B26717111
theorem B8333441 : Blo 1646022 8333441 := bstep (se 2 (by rfl) ⟨3125040, by rfl⟩ : syracuseStep 8333441 = 6250081) B6250081
theorem B7031069 : Blo 1646022 7031069 := bstep (se 3 (by rfl) ⟨1318325, by rfl⟩ : syracuseStep 7031069 = 2636651) B2636651
theorem B9513359 : Blo 1646022 9513359 := bstep (se 1 (by rfl) ⟨7135019, by rfl⟩ : syracuseStep 9513359 = 14270039) B14270039
theorem B3705263 : Blo 1646022 3705263 := bstep (se 1 (by rfl) ⟨2778947, by rfl⟩ : syracuseStep 3705263 = 5557895) B5557895
theorem B6252983 : Blo 1646022 6252983 := bstep (se 1 (by rfl) ⟨4689737, by rfl⟩ : syracuseStep 6252983 = 9379475) B9379475
theorem B3705299 : Blo 1646022 3705299 := bstep (se 1 (by rfl) ⟨2778974, by rfl⟩ : syracuseStep 3705299 = 5557949) B5557949
theorem B2779643 : Blo 1646022 2779643 := bstep (se 1 (by rfl) ⟨2084732, by rfl⟩ : syracuseStep 2779643 = 4169465) B4169465
theorem B3705407 : Blo 1646022 3705407 := bstep (se 1 (by rfl) ⟨2779055, by rfl⟩ : syracuseStep 3705407 = 5558111) B5558111
theorem B5556815 : Blo 1646022 5556815 := bstep (se 1 (by rfl) ⟨4167611, by rfl⟩ : syracuseStep 5556815 = 8335223) B8335223
theorem B11274875 : Blo 1646022 11274875 := bstep (se 1 (by rfl) ⟨8456156, by rfl⟩ : syracuseStep 11274875 = 16912313) B16912313
theorem B3705515 : Blo 1646022 3705515 := bstep (se 1 (by rfl) ⟨2779136, by rfl⟩ : syracuseStep 3705515 = 5558273) B5558273
theorem B14076625 : Blo 1646022 14076625 := bstep (se 2 (by rfl) ⟨5278734, by rfl⟩ : syracuseStep 14076625 = 10557469) B10557469
theorem B3517175 : Blo 1646022 3517175 := bstep (se 1 (by rfl) ⟨2637881, by rfl⟩ : syracuseStep 3517175 = 5275763) B5275763
theorem B4754195 : Blo 1646022 4754195 := bstep (se 1 (by rfl) ⟨3565646, by rfl⟩ : syracuseStep 4754195 = 7131293) B7131293
theorem B2083639 : Blo 1646022 2083639 := bstep (se 1 (by rfl) ⟨1562729, by rfl⟩ : syracuseStep 2083639 = 3125459) B3125459
theorem B8334251 : Blo 1646022 8334251 := bstep (se 1 (by rfl) ⟨6250688, by rfl⟩ : syracuseStep 8334251 = 12501377) B12501377
theorem B6253483 : Blo 1646022 6253483 := bstep (se 1 (by rfl) ⟨4690112, by rfl⟩ : syracuseStep 6253483 = 9380225) B9380225
theorem B2780075 : Blo 1646022 2780075 := bstep (se 1 (by rfl) ⟨2085056, by rfl⟩ : syracuseStep 2780075 = 4170113) B4170113
theorem B4689019 : Blo 1646022 4689019 := bstep (se 1 (by rfl) ⟨3516764, by rfl⟩ : syracuseStep 4689019 = 7033529) B7033529
theorem B6253757 : Blo 1646022 6253757 := bstep (se 3 (by rfl) ⟨1172579, by rfl⟩ : syracuseStep 6253757 = 2345159) B2345159
theorem B3706055 : Blo 1646022 3706055 := bstep (se 1 (by rfl) ⟨2779541, by rfl⟩ : syracuseStep 3706055 = 5559083) B5559083
theorem B2469083 : Blo 1646022 2469083 := bstep (se 1 (by rfl) ⟨1851812, by rfl⟩ : syracuseStep 2469083 = 3703625) B3703625
theorem B2084059 : Blo 1646022 2084059 := bstep (se 1 (by rfl) ⟨1563044, by rfl⟩ : syracuseStep 2084059 = 3126089) B3126089
theorem B6253787 : Blo 1646022 6253787 := bstep (se 1 (by rfl) ⟨4690340, by rfl⟩ : syracuseStep 6253787 = 9380681) B9380681
theorem B16895263 : Blo 1646022 16895263 := bstep (se 1 (by rfl) ⟨12671447, by rfl⟩ : syracuseStep 16895263 = 25342895) B25342895
theorem B7032095 : Blo 1646022 7032095 := bstep (se 1 (by rfl) ⟨5274071, by rfl⟩ : syracuseStep 7032095 = 10548143) B10548143
theorem B4451707 : Blo 1646022 4451707 := bstep (se 1 (by rfl) ⟨3338780, by rfl⟩ : syracuseStep 4451707 = 6677561) B6677561
theorem B3706235 : Blo 1646022 3706235 := bstep (se 1 (by rfl) ⟨2779676, by rfl⟩ : syracuseStep 3706235 = 5559353) B5559353
theorem B2469257 : Blo 1646022 2469257 := bstep (se 2 (by rfl) ⟨925971, by rfl⟩ : syracuseStep 2469257 = 1851943) B1851943
theorem B2780615 : Blo 1646022 2780615 := bstep (se 1 (by rfl) ⟨2085461, by rfl⟩ : syracuseStep 2780615 = 4170923) B4170923
theorem B8342999 : Blo 1646022 8342999 := bstep (se 1 (by rfl) ⟨6257249, by rfl⟩ : syracuseStep 8342999 = 12514499) B12514499
theorem B3706361 : Blo 1646022 3706361 := bstep (se 2 (by rfl) ⟨1389885, by rfl⟩ : syracuseStep 3706361 = 2779771) B2779771
theorem B3706451 : Blo 1646022 3706451 := bstep (se 1 (by rfl) ⟨2779838, by rfl⟩ : syracuseStep 3706451 = 5559677) B5559677
theorem B4451935 : Blo 1646022 4451935 := bstep (se 1 (by rfl) ⟨3338951, by rfl⟩ : syracuseStep 4451935 = 6677903) B6677903
theorem B65949395 : Blo 1646022 65949395 := bstep (se 1 (by rfl) ⟨49462046, by rfl⟩ : syracuseStep 65949395 = 98924093) B98924093
theorem B2469611 : Blo 1646022 2469611 := bstep (se 1 (by rfl) ⟨1852208, by rfl⟩ : syracuseStep 2469611 = 3704417) B3704417
theorem B3706631 : Blo 1646022 3706631 := bstep (se 1 (by rfl) ⟨2779973, by rfl⟩ : syracuseStep 3706631 = 5559947) B5559947
theorem B5558057 : Blo 1646022 5558057 := bstep (se 2 (by rfl) ⟨2084271, by rfl⟩ : syracuseStep 5558057 = 4168543) B4168543
theorem B4755329 : Blo 1646022 4755329 := bstep (se 2 (by rfl) ⟨1783248, by rfl⟩ : syracuseStep 4755329 = 3566497) B3566497
theorem B1978267 : Blo 1646022 1978267 := bstep (se 1 (by rfl) ⟨1483700, by rfl⟩ : syracuseStep 1978267 = 2967401) B2967401
theorem B2469839 : Blo 1646022 2469839 := bstep (se 1 (by rfl) ⟨1852379, by rfl⟩ : syracuseStep 2469839 = 3704759) B3704759
theorem B3518473 : Blo 1646022 3518473 := bstep (se 2 (by rfl) ⟨1319427, by rfl⟩ : syracuseStep 3518473 = 2638855) B2638855
theorem B8335385 : Blo 1646022 8335385 := bstep (se 2 (by rfl) ⟨3125769, by rfl⟩ : syracuseStep 8335385 = 6251539) B6251539
theorem B2470235 : Blo 1646022 2470235 := bstep (se 1 (by rfl) ⟨1852676, by rfl⟩ : syracuseStep 2470235 = 3705353) B3705353
theorem B3707243 : Blo 1646022 3707243 := bstep (se 1 (by rfl) ⟨2780432, by rfl⟩ : syracuseStep 3707243 = 5560865) B5560865
theorem B7516523 : Blo 1646022 7516523 := bstep (se 1 (by rfl) ⟨5637392, by rfl⟩ : syracuseStep 7516523 = 11274785) B11274785
theorem B17814005 : Blo 1646022 17814005 := bstep (se 5 (by rfl) ⟨835031, by rfl⟩ : syracuseStep 17814005 = 1670063) B1670063
theorem B3707387 : Blo 1646022 3707387 := bstep (se 1 (by rfl) ⟨2780540, by rfl⟩ : syracuseStep 3707387 = 5561081) B5561081
theorem B9376307 : Blo 1646022 9376307 := bstep (se 1 (by rfl) ⟨7032230, by rfl⟩ : syracuseStep 9376307 = 14064461) B14064461
theorem B2470463 : Blo 1646022 2470463 := bstep (se 1 (by rfl) ⟨1852847, by rfl⟩ : syracuseStep 2470463 = 3705695) B3705695
theorem B10547833 : Blo 1646022 10547833 := bstep (se 2 (by rfl) ⟨3955437, by rfl⟩ : syracuseStep 10547833 = 7910875) B7910875
theorem B3707513 : Blo 1646022 3707513 := bstep (se 2 (by rfl) ⟨1390317, by rfl⟩ : syracuseStep 3707513 = 2780635) B2780635
theorem B4010671 : Blo 1646022 4010671 := bstep (se 1 (by rfl) ⟨3008003, by rfl⟩ : syracuseStep 4010671 = 6016007) B6016007
theorem B3707567 : Blo 1646022 3707567 := bstep (se 1 (by rfl) ⟨2780675, by rfl⟩ : syracuseStep 3707567 = 5561351) B5561351
theorem B2470583 : Blo 1646022 2470583 := bstep (se 1 (by rfl) ⟨1852937, by rfl⟩ : syracuseStep 2470583 = 3705875) B3705875
theorem B3707639 : Blo 1646022 3707639 := bstep (se 1 (by rfl) ⟨2780729, by rfl⟩ : syracuseStep 3707639 = 5561459) B5561459
theorem B2085679 : Blo 1646022 2085679 := bstep (se 1 (by rfl) ⟨1564259, by rfl⟩ : syracuseStep 2085679 = 3128519) B3128519
theorem B10556239 : Blo 1646022 10556239 := bstep (se 1 (by rfl) ⟨7917179, by rfl⟩ : syracuseStep 10556239 = 15834359) B15834359
theorem B2470811 : Blo 1646022 2470811 := bstep (se 1 (by rfl) ⟨1853108, by rfl⟩ : syracuseStep 2470811 = 3706217) B3706217
theorem B3707819 : Blo 1646022 3707819 := bstep (se 1 (by rfl) ⟨2780864, by rfl⟩ : syracuseStep 3707819 = 5561729) B5561729
theorem B10695671 : Blo 1646022 10695671 := bstep (se 1 (by rfl) ⟨8021753, by rfl⟩ : syracuseStep 10695671 = 16043507) B16043507
theorem B12506237 : Blo 1646022 12506237 := bstep (se 3 (by rfl) ⟨2344919, by rfl⟩ : syracuseStep 12506237 = 4689839) B4689839
theorem B7918717 : Blo 1646022 7918717 := bstep (se 3 (by rfl) ⟨1484759, by rfl⟩ : syracuseStep 7918717 = 2969519) B2969519
theorem B6952151 : Blo 1646022 6952151 := bstep (se 1 (by rfl) ⟨5214113, by rfl⟩ : syracuseStep 6952151 = 10428227) B10428227
theorem B2471207 : Blo 1646022 2471207 := bstep (se 1 (by rfl) ⟨1853405, by rfl⟩ : syracuseStep 2471207 = 3706811) B3706811
theorem B20034911 : Blo 1646022 20034911 := bstep (se 1 (by rfl) ⟨15026183, by rfl⟩ : syracuseStep 20034911 = 30052367) B30052367
theorem B4167035 : Blo 1646022 4167035 := bstep (se 1 (by rfl) ⟨3125276, by rfl⟩ : syracuseStep 4167035 = 6250553) B6250553
theorem B2471291 : Blo 1646022 2471291 := bstep (se 1 (by rfl) ⟨1853468, by rfl⟩ : syracuseStep 2471291 = 3706937) B3706937
theorem B15832513 : Blo 1646022 15832513 := bstep (se 2 (by rfl) ⟨5937192, by rfl⟩ : syracuseStep 15832513 = 11874385) B11874385
theorem B2471417 : Blo 1646022 2471417 := bstep (se 2 (by rfl) ⟨926781, by rfl⟩ : syracuseStep 2471417 = 1853563) B1853563
theorem B16905773 : Blo 1646022 16905773 := bstep (se 3 (by rfl) ⟨3169832, by rfl⟩ : syracuseStep 16905773 = 6339665) B6339665
theorem B2471519 : Blo 1646022 2471519 := bstep (se 1 (by rfl) ⟨1853639, by rfl⟩ : syracuseStep 2471519 = 3707279) B3707279
theorem B8902331 : Blo 1646022 8902331 := bstep (se 1 (by rfl) ⟨6676748, by rfl⟩ : syracuseStep 8902331 = 13353497) B13353497
theorem B2471735 : Blo 1646022 2471735 := bstep (se 1 (by rfl) ⟨1853801, by rfl⟩ : syracuseStep 2471735 = 3707603) B3707603
theorem B5560271 : Blo 1646022 5560271 := bstep (se 1 (by rfl) ⟨4170203, by rfl⟩ : syracuseStep 5560271 = 8340407) B8340407
theorem B9377765 : Blo 1646022 9377765 := bstep (se 4 (by rfl) ⟨879165, by rfl⟩ : syracuseStep 9377765 = 1758331) B1758331
theorem B6256673 : Blo 1646022 6256673 := bstep (se 2 (by rfl) ⟨2346252, by rfl⟩ : syracuseStep 6256673 = 4692505) B4692505
theorem B59439203 : Blo 1646022 59439203 := bstep (se 1 (by rfl) ⟨44579402, by rfl⟩ : syracuseStep 59439203 = 89158805) B89158805
theorem B1759519 : Blo 1646022 1759519 := bstep (se 1 (by rfl) ⟨1319639, by rfl⟩ : syracuseStep 1759519 = 2639279) B2639279
theorem B18749879 : Blo 1646022 18749879 := bstep (se 1 (by rfl) ⟨14062409, by rfl⟩ : syracuseStep 18749879 = 28124819) B28124819
theorem B3955169 : Blo 1646022 3955169 := bstep (se 2 (by rfl) ⟨1483188, by rfl⟩ : syracuseStep 3955169 = 2966377) B2966377
theorem B11262527 : Blo 1646022 11262527 := bstep (se 1 (by rfl) ⟨8446895, by rfl⟩ : syracuseStep 11262527 = 16893791) B16893791
theorem B3340921 : Blo 1646022 3340921 := bstep (se 2 (by rfl) ⟨1252845, by rfl⟩ : syracuseStep 3340921 = 2505691) B2505691
theorem B18053891 : Blo 1646022 18053891 := bstep (se 1 (by rfl) ⟨13540418, by rfl⟩ : syracuseStep 18053891 = 27080837) B27080837
theorem B4692755 : Blo 1646022 4692755 := bstep (se 1 (by rfl) ⟨3519566, by rfl⟩ : syracuseStep 4692755 = 7039133) B7039133
theorem B7912259 : Blo 1646022 7912259 := bstep (se 1 (by rfl) ⟨5934194, by rfl⟩ : syracuseStep 7912259 = 11868389) B11868389
theorem B8338301 : Blo 1646022 8338301 := bstep (se 3 (by rfl) ⟨1563431, by rfl⟩ : syracuseStep 8338301 = 3126863) B3126863
theorem B5561243 : Blo 1646022 5561243 := bstep (se 1 (by rfl) ⟨4170932, by rfl⟩ : syracuseStep 5561243 = 8341865) B8341865
theorem B2112463 : Blo 1646022 2112463 := bstep (se 1 (by rfl) ⟨1584347, by rfl⟩ : syracuseStep 2112463 = 3168695) B3168695
theorem B1670095 : Blo 1646022 1670095 := bstep (se 1 (by rfl) ⟨1252571, by rfl⟩ : syracuseStep 1670095 = 2505143) B2505143
theorem B4168847 : Blo 1646022 4168847 := bstep (se 1 (by rfl) ⟨3126635, by rfl⟩ : syracuseStep 4168847 = 6253271) B6253271
theorem B4226519 : Blo 1646022 4226519 := bstep (se 1 (by rfl) ⟨3169889, by rfl⟩ : syracuseStep 4226519 = 6339779) B6339779
theorem B1646075 : Blo 1646022 1646075 := bstep (se 1 (by rfl) ⟨1234556, by rfl⟩ : syracuseStep 1646075 = 2469113) B2469113
theorem B10550807 : Blo 1646022 10550807 := bstep (se 1 (by rfl) ⟨7913105, by rfl⟩ : syracuseStep 10550807 = 15826211) B15826211
theorem B1646143 : Blo 1646022 1646143 := bstep (se 1 (by rfl) ⟨1234607, by rfl⟩ : syracuseStep 1646143 = 2469215) B2469215
theorem B1646151 : Blo 1646022 1646151 := bstep (se 1 (by rfl) ⟨1234613, by rfl⟩ : syracuseStep 1646151 = 2469227) B2469227
theorem B6250067 : Blo 1646022 6250067 := bstep (se 1 (by rfl) ⟨4687550, by rfl⟩ : syracuseStep 6250067 = 9375101) B9375101
theorem B21102227 : Blo 1646022 21102227 := bstep (se 1 (by rfl) ⟨15826670, by rfl⟩ : syracuseStep 21102227 = 31653341) B31653341
theorem B1646303 : Blo 1646022 1646303 := bstep (se 1 (by rfl) ⟨1234727, by rfl⟩ : syracuseStep 1646303 = 2469455) B2469455
theorem B28532513 : Blo 1646022 28532513 := bstep (se 2 (by rfl) ⟨10699692, by rfl⟩ : syracuseStep 28532513 = 21399385) B21399385
theorem B1646383 : Blo 1646022 1646383 := bstep (se 1 (by rfl) ⟨1234787, by rfl⟩ : syracuseStep 1646383 = 2469575) B2469575
theorem B2637625 : Blo 1646022 2637625 := bstep (se 2 (by rfl) ⟨989109, by rfl⟩ : syracuseStep 2637625 = 1978219) B1978219
theorem B8339273 : Blo 1646022 8339273 := bstep (se 2 (by rfl) ⟨3127227, by rfl⟩ : syracuseStep 8339273 = 6254455) B6254455
theorem B1646491 : Blo 1646022 1646491 := bstep (se 1 (by rfl) ⟨1234868, by rfl⟩ : syracuseStep 1646491 = 2469737) B2469737
theorem B1646543 : Blo 1646022 1646543 := bstep (se 1 (by rfl) ⟨1234907, by rfl⟩ : syracuseStep 1646543 = 2469815) B2469815
theorem B1646567 : Blo 1646022 1646567 := bstep (se 1 (by rfl) ⟨1234925, by rfl⟩ : syracuseStep 1646567 = 2469851) B2469851
theorem B1646823 : Blo 1646022 1646823 := bstep (se 1 (by rfl) ⟨1235117, by rfl⟩ : syracuseStep 1646823 = 2470235) B2470235
theorem B6250871 : Blo 1646022 6250871 := bstep (se 1 (by rfl) ⟨4688153, by rfl⟩ : syracuseStep 6250871 = 9376307) B9376307
theorem B1646975 : Blo 1646022 1646975 := bstep (se 1 (by rfl) ⟨1235231, by rfl⟩ : syracuseStep 1646975 = 2470463) B2470463
theorem B1647055 : Blo 1646022 1647055 := bstep (se 1 (by rfl) ⟨1235291, by rfl⟩ : syracuseStep 1647055 = 2470583) B2470583
theorem B1647207 : Blo 1646022 1647207 := bstep (se 1 (by rfl) ⟨1235405, by rfl⟩ : syracuseStep 1647207 = 2470811) B2470811
theorem B1647471 : Blo 1646022 1647471 := bstep (se 1 (by rfl) ⟨1235603, by rfl⟩ : syracuseStep 1647471 = 2471207) B2471207
theorem B2778023 : Blo 1646022 2778023 := bstep (se 1 (by rfl) ⟨2083517, by rfl⟩ : syracuseStep 2778023 = 4167035) B4167035
theorem B1647527 : Blo 1646022 1647527 := bstep (se 1 (by rfl) ⟨1235645, by rfl⟩ : syracuseStep 1647527 = 2471291) B2471291
theorem B18768833 : Blo 1646022 18768833 := bstep (se 2 (by rfl) ⟨7038312, by rfl⟩ : syracuseStep 18768833 = 14076625) B14076625
theorem B1852411 : Blo 1646022 1852411 := bstep (se 1 (by rfl) ⟨1389308, by rfl⟩ : syracuseStep 1852411 = 2778617) B2778617
theorem B1647611 : Blo 1646022 1647611 := bstep (se 1 (by rfl) ⟨1235708, by rfl⟩ : syracuseStep 1647611 = 2471417) B2471417
theorem B1647679 : Blo 1646022 1647679 := bstep (se 1 (by rfl) ⟨1235759, by rfl⟩ : syracuseStep 1647679 = 2471519) B2471519
theorem B2778185 : Blo 1646022 2778185 := bstep (se 2 (by rfl) ⟨1041819, by rfl⟩ : syracuseStep 2778185 = 2083639) B2083639
theorem B3703913 : Blo 1646022 3703913 := bstep (se 2 (by rfl) ⟨1388967, by rfl⟩ : syracuseStep 3703913 = 2777935) B2777935
theorem B14074985 : Blo 1646022 14074985 := bstep (se 2 (by rfl) ⟨5278119, by rfl⟩ : syracuseStep 14074985 = 10556239) B10556239
theorem B11273363 : Blo 1646022 11273363 := bstep (se 1 (by rfl) ⟨8455022, by rfl⟩ : syracuseStep 11273363 = 16910045) B16910045
theorem B1852591 : Blo 1646022 1852591 := bstep (se 1 (by rfl) ⟨1389443, by rfl⟩ : syracuseStep 1852591 = 2778887) B2778887
theorem B1647823 : Blo 1646022 1647823 := bstep (se 1 (by rfl) ⟨1235867, by rfl⟩ : syracuseStep 1647823 = 2471735) B2471735
theorem B6251843 : Blo 1646022 6251843 := bstep (se 1 (by rfl) ⟨4688882, by rfl⟩ : syracuseStep 6251843 = 9377765) B9377765
theorem B4171115 : Blo 1646022 4171115 := bstep (se 1 (by rfl) ⟨3128336, by rfl⟩ : syracuseStep 4171115 = 6256673) B6256673
theorem B39626135 : Blo 1646022 39626135 := bstep (se 1 (by rfl) ⟨29719601, by rfl⟩ : syracuseStep 39626135 = 59439203) B59439203
theorem B5555627 : Blo 1646022 5555627 := bstep (se 1 (by rfl) ⟨4166720, by rfl⟩ : syracuseStep 5555627 = 8333441) B8333441
theorem B6252025 : Blo 1646022 6252025 := bstep (se 2 (by rfl) ⟨2344509, by rfl⟩ : syracuseStep 6252025 = 4689019) B4689019
theorem B4687379 : Blo 1646022 4687379 := bstep (se 1 (by rfl) ⟨3515534, by rfl⟩ : syracuseStep 4687379 = 7031069) B7031069
theorem B6342239 : Blo 1646022 6342239 := bstep (se 1 (by rfl) ⟨4756679, by rfl⟩ : syracuseStep 6342239 = 9513359) B9513359
theorem B2778745 : Blo 1646022 2778745 := bstep (se 2 (by rfl) ⟨1042029, by rfl⟩ : syracuseStep 2778745 = 2084059) B2084059
theorem B1853095 : Blo 1646022 1853095 := bstep (se 1 (by rfl) ⟨1389821, by rfl⟩ : syracuseStep 1853095 = 2779643) B2779643
theorem B3704543 : Blo 1646022 3704543 := bstep (se 1 (by rfl) ⟨2778407, by rfl⟩ : syracuseStep 3704543 = 5556815) B5556815
theorem B2344783 : Blo 1646022 2344783 := bstep (se 1 (by rfl) ⟨1758587, by rfl⟩ : syracuseStep 2344783 = 3517175) B3517175
theorem B12035927 : Blo 1646022 12035927 := bstep (se 1 (by rfl) ⟨9026945, by rfl⟩ : syracuseStep 12035927 = 18053891) B18053891
theorem B5556167 : Blo 1646022 5556167 := bstep (se 1 (by rfl) ⟨4167125, by rfl⟩ : syracuseStep 5556167 = 8334251) B8334251
theorem B1853383 : Blo 1646022 1853383 := bstep (se 1 (by rfl) ⟨1390037, by rfl⟩ : syracuseStep 1853383 = 2780075) B2780075
theorem B2779231 : Blo 1646022 2779231 := bstep (se 1 (by rfl) ⟨2084423, by rfl⟩ : syracuseStep 2779231 = 4168847) B4168847
theorem B4688063 : Blo 1646022 4688063 := bstep (se 1 (by rfl) ⟨3516047, by rfl⟩ : syracuseStep 4688063 = 7032095) B7032095
theorem B1853743 : Blo 1646022 1853743 := bstep (se 1 (by rfl) ⟨1390307, by rfl⟩ : syracuseStep 1853743 = 2780615) B2780615
theorem B3516833 : Blo 1646022 3516833 := bstep (se 2 (by rfl) ⟨1318812, by rfl⟩ : syracuseStep 3516833 = 2637625) B2637625
theorem B8907173 : Blo 1646022 8907173 := bstep (se 4 (by rfl) ⟨835047, by rfl⟩ : syracuseStep 8907173 = 1670095) B1670095
theorem B14068151 : Blo 1646022 14068151 := bstep (se 1 (by rfl) ⟨10551113, by rfl⟩ : syracuseStep 14068151 = 21102227) B21102227
theorem B3705371 : Blo 1646022 3705371 := bstep (se 1 (by rfl) ⟨2779028, by rfl⟩ : syracuseStep 3705371 = 5558057) B5558057
theorem B5556923 : Blo 1646022 5556923 := bstep (se 1 (by rfl) ⟨4167692, by rfl⟩ : syracuseStep 5556923 = 8335385) B8335385
theorem B8448823 : Blo 1646022 8448823 := bstep (se 1 (by rfl) ⟨6336617, by rfl⟩ : syracuseStep 8448823 = 12673235) B12673235
theorem B2346025 : Blo 1646022 2346025 := bstep (se 2 (by rfl) ⟨879759, by rfl⟩ : syracuseStep 2346025 = 1759519) B1759519
theorem B2469047 : Blo 1646022 2469047 := bstep (se 1 (by rfl) ⟨1851785, by rfl⟩ : syracuseStep 2469047 = 3703571) B3703571
theorem B42200351 : Blo 1646022 42200351 := bstep (se 1 (by rfl) ⟨31650263, by rfl⟩ : syracuseStep 42200351 = 63300527) B63300527
theorem B7130447 : Blo 1646022 7130447 := bstep (se 1 (by rfl) ⟨5347835, by rfl⟩ : syracuseStep 7130447 = 10695671) B10695671
theorem B2780527 : Blo 1646022 2780527 := bstep (se 1 (by rfl) ⟨2085395, by rfl⟩ : syracuseStep 2780527 = 4170791) B4170791
theorem B2469287 : Blo 1646022 2469287 := bstep (se 1 (by rfl) ⟨1851965, by rfl⟩ : syracuseStep 2469287 = 3703931) B3703931
theorem B2469371 : Blo 1646022 2469371 := bstep (se 1 (by rfl) ⟨1852028, by rfl⟩ : syracuseStep 2469371 = 3704057) B3704057
theorem B2469467 : Blo 1646022 2469467 := bstep (se 1 (by rfl) ⟨1852100, by rfl⟩ : syracuseStep 2469467 = 3704201) B3704201
theorem B2469551 : Blo 1646022 2469551 := bstep (se 1 (by rfl) ⟨1852163, by rfl⟩ : syracuseStep 2469551 = 3704327) B3704327
theorem B2780905 : Blo 1646022 2780905 := bstep (se 2 (by rfl) ⟨1042839, by rfl⟩ : syracuseStep 2780905 = 2085679) B2085679
theorem B15019769 : Blo 1646022 15019769 := bstep (se 2 (by rfl) ⟨5632413, by rfl⟩ : syracuseStep 15019769 = 11264827) B11264827
theorem B2469671 : Blo 1646022 2469671 := bstep (se 1 (by rfl) ⟨1852253, by rfl⟩ : syracuseStep 2469671 = 3704507) B3704507
theorem B5934887 : Blo 1646022 5934887 := bstep (se 1 (by rfl) ⟨4451165, by rfl⟩ : syracuseStep 5934887 = 8902331) B8902331
theorem B3518329 : Blo 1646022 3518329 := bstep (se 2 (by rfl) ⟨1319373, by rfl⟩ : syracuseStep 3518329 = 2638747) B2638747
theorem B2469755 : Blo 1646022 2469755 := bstep (se 1 (by rfl) ⟨1852316, by rfl⟩ : syracuseStep 2469755 = 3704633) B3704633
theorem B10547117 : Blo 1646022 10547117 := bstep (se 3 (by rfl) ⟨1977584, by rfl⟩ : syracuseStep 10547117 = 3955169) B3955169
theorem B11874271 : Blo 1646022 11874271 := bstep (se 1 (by rfl) ⟨8905703, by rfl⟩ : syracuseStep 11874271 = 17811407) B17811407
theorem B3706847 : Blo 1646022 3706847 := bstep (se 1 (by rfl) ⟨2780135, by rfl⟩ : syracuseStep 3706847 = 5560271) B5560271
theorem B2470175 : Blo 1646022 2470175 := bstep (se 1 (by rfl) ⟨1852631, by rfl⟩ : syracuseStep 2470175 = 3705263) B3705263
theorem B2470199 : Blo 1646022 2470199 := bstep (se 1 (by rfl) ⟨1852649, by rfl⟩ : syracuseStep 2470199 = 3705299) B3705299
theorem B7508351 : Blo 1646022 7508351 := bstep (se 1 (by rfl) ⟨5631263, by rfl⟩ : syracuseStep 7508351 = 11262527) B11262527
theorem B2470271 : Blo 1646022 2470271 := bstep (se 1 (by rfl) ⟨1852703, by rfl⟩ : syracuseStep 2470271 = 3705407) B3705407
theorem B3125641 : Blo 1646022 3125641 := bstep (se 2 (by rfl) ⟨1172115, by rfl⟩ : syracuseStep 3125641 = 2344231) B2344231
theorem B7516583 : Blo 1646022 7516583 := bstep (se 1 (by rfl) ⟨5637437, by rfl⟩ : syracuseStep 7516583 = 11274875) B11274875
theorem B2470343 : Blo 1646022 2470343 := bstep (se 1 (by rfl) ⟨1852757, by rfl⟩ : syracuseStep 2470343 = 3705515) B3705515
theorem B4010489 : Blo 1646022 4010489 := bstep (se 2 (by rfl) ⟨1503933, by rfl⟩ : syracuseStep 4010489 = 3007867) B3007867
theorem B5935609 : Blo 1646022 5935609 := bstep (se 2 (by rfl) ⟨2225853, by rfl⟩ : syracuseStep 5935609 = 4451707) B4451707
theorem B5558867 : Blo 1646022 5558867 := bstep (se 1 (by rfl) ⟨4169150, by rfl⟩ : syracuseStep 5558867 = 8338301) B8338301
theorem B3707495 : Blo 1646022 3707495 := bstep (se 1 (by rfl) ⟨2780621, by rfl⟩ : syracuseStep 3707495 = 5561243) B5561243
theorem B12514013 : Blo 1646022 12514013 := bstep (se 3 (by rfl) ⟨2346377, by rfl⟩ : syracuseStep 12514013 = 4692755) B4692755
theorem B5935913 : Blo 1646022 5935913 := bstep (se 2 (by rfl) ⟨2225967, by rfl⟩ : syracuseStep 5935913 = 4451935) B4451935
theorem B2470697 : Blo 1646022 2470697 := bstep (se 2 (by rfl) ⟨926511, by rfl⟩ : syracuseStep 2470697 = 1853023) B1853023
theorem B2470703 : Blo 1646022 2470703 := bstep (se 1 (by rfl) ⟨1853027, by rfl⟩ : syracuseStep 2470703 = 3706055) B3706055
theorem B2470823 : Blo 1646022 2470823 := bstep (se 1 (by rfl) ⟨1853117, by rfl⟩ : syracuseStep 2470823 = 3706235) B3706235
theorem B2470907 : Blo 1646022 2470907 := bstep (se 1 (by rfl) ⟨1853180, by rfl⟩ : syracuseStep 2470907 = 3706361) B3706361
theorem B7033871 : Blo 1646022 7033871 := bstep (se 1 (by rfl) ⟨5275403, by rfl⟩ : syracuseStep 7033871 = 10550807) B10550807
theorem B4166711 : Blo 1646022 4166711 := bstep (se 1 (by rfl) ⟨3125033, by rfl⟩ : syracuseStep 4166711 = 6250067) B6250067
theorem B2470967 : Blo 1646022 2470967 := bstep (se 1 (by rfl) ⟨1853225, by rfl⟩ : syracuseStep 2470967 = 3706451) B3706451
theorem B2471087 : Blo 1646022 2471087 := bstep (se 1 (by rfl) ⟨1853315, by rfl⟩ : syracuseStep 2471087 = 3706631) B3706631
theorem B5559515 : Blo 1646022 5559515 := bstep (se 1 (by rfl) ⟨4169636, by rfl⟩ : syracuseStep 5559515 = 8339273) B8339273
theorem B4691297 : Blo 1646022 4691297 := bstep (se 2 (by rfl) ⟨1759236, by rfl⟩ : syracuseStep 4691297 = 3518473) B3518473
theorem B25712093 : Blo 1646022 25712093 := bstep (se 3 (by rfl) ⟨4821017, by rfl⟩ : syracuseStep 25712093 = 9642035) B9642035
theorem B2471495 : Blo 1646022 2471495 := bstep (se 1 (by rfl) ⟨1853621, by rfl⟩ : syracuseStep 2471495 = 3707243) B3707243
theorem B28530299 : Blo 1646022 28530299 := bstep (se 1 (by rfl) ⟨21397724, by rfl⟩ : syracuseStep 28530299 = 42795449) B42795449
theorem B11876003 : Blo 1646022 11876003 := bstep (se 1 (by rfl) ⟨8907002, by rfl⟩ : syracuseStep 11876003 = 17814005) B17814005
theorem B2471591 : Blo 1646022 2471591 := bstep (se 1 (by rfl) ⟨1853693, by rfl⟩ : syracuseStep 2471591 = 3707387) B3707387
theorem B2471675 : Blo 1646022 2471675 := bstep (se 1 (by rfl) ⟨1853756, by rfl⟩ : syracuseStep 2471675 = 3707513) B3707513
theorem B2471711 : Blo 1646022 2471711 := bstep (se 1 (by rfl) ⟨1853783, by rfl⟩ : syracuseStep 2471711 = 3707567) B3707567
theorem B2471759 : Blo 1646022 2471759 := bstep (se 1 (by rfl) ⟨1853819, by rfl⟩ : syracuseStep 2471759 = 3707639) B3707639
theorem B2471879 : Blo 1646022 2471879 := bstep (se 1 (by rfl) ⟨1853909, by rfl⟩ : syracuseStep 2471879 = 3707819) B3707819
theorem B5560379 : Blo 1646022 5560379 := bstep (se 1 (by rfl) ⟨4170284, by rfl⟩ : syracuseStep 5560379 = 8340569) B8340569
theorem B8337491 : Blo 1646022 8337491 := bstep (se 1 (by rfl) ⟨6253118, by rfl⟩ : syracuseStep 8337491 = 12506237) B12506237
theorem B4634767 : Blo 1646022 4634767 := bstep (se 1 (by rfl) ⟨3476075, by rfl⟩ : syracuseStep 4634767 = 6952151) B6952151
theorem B5937295 : Blo 1646022 5937295 := bstep (se 1 (by rfl) ⟨4452971, by rfl⟩ : syracuseStep 5937295 = 8905943) B8905943
theorem B14063777 : Blo 1646022 14063777 := bstep (se 2 (by rfl) ⟨5273916, by rfl⟩ : syracuseStep 14063777 = 10547833) B10547833
theorem B4454561 : Blo 1646022 4454561 := bstep (se 2 (by rfl) ⟨1670460, by rfl⟩ : syracuseStep 4454561 = 3340921) B3340921
theorem B5347561 : Blo 1646022 5347561 := bstep (se 2 (by rfl) ⟨2005335, by rfl⟩ : syracuseStep 5347561 = 4010671) B4010671
theorem B50698487 : Blo 1646022 50698487 := bstep (se 1 (by rfl) ⟨38023865, by rfl⟩ : syracuseStep 50698487 = 76047731) B76047731
theorem B53426429 : Blo 1646022 53426429 := bstep (se 3 (by rfl) ⟨10017455, by rfl⟩ : syracuseStep 53426429 = 20034911) B20034911
theorem B20044061 : Blo 1646022 20044061 := bstep (se 3 (by rfl) ⟨3758261, by rfl⟩ : syracuseStep 20044061 = 7516523) B7516523
theorem B5560649 : Blo 1646022 5560649 := bstep (se 2 (by rfl) ⟨2085243, by rfl⟩ : syracuseStep 5560649 = 4170487) B4170487
theorem B11270515 : Blo 1646022 11270515 := bstep (se 1 (by rfl) ⟨8452886, by rfl⟩ : syracuseStep 11270515 = 16905773) B16905773
theorem B8337977 : Blo 1646022 8337977 := bstep (se 2 (by rfl) ⟨3126741, by rfl⟩ : syracuseStep 8337977 = 6253483) B6253483
theorem B2816617 : Blo 1646022 2816617 := bstep (se 2 (by rfl) ⟨1056231, by rfl⟩ : syracuseStep 2816617 = 2112463) B2112463
theorem B10558289 : Blo 1646022 10558289 := bstep (se 2 (by rfl) ⟨3959358, by rfl⟩ : syracuseStep 10558289 = 7918717) B7918717
theorem B6675305 : Blo 1646022 6675305 := bstep (se 2 (by rfl) ⟨2503239, by rfl⟩ : syracuseStep 6675305 = 5006479) B5006479
theorem B12499919 : Blo 1646022 12499919 := bstep (se 1 (by rfl) ⟨9374939, by rfl⟩ : syracuseStep 12499919 = 18749879) B18749879
theorem B4168655 : Blo 1646022 4168655 := bstep (se 1 (by rfl) ⟨3126491, by rfl⟩ : syracuseStep 4168655 = 6252983) B6252983
theorem B22527017 : Blo 1646022 22527017 := bstep (se 2 (by rfl) ⟨8447631, by rfl⟩ : syracuseStep 22527017 = 16895263) B16895263
theorem B3169463 : Blo 1646022 3169463 := bstep (se 1 (by rfl) ⟨2377097, by rfl⟩ : syracuseStep 3169463 = 4754195) B4754195
theorem B5274839 : Blo 1646022 5274839 := bstep (se 1 (by rfl) ⟨3956129, by rfl⟩ : syracuseStep 5274839 = 7912259) B7912259
theorem B175865053 : Blo 1646022 175865053 := bstep (se 3 (by rfl) ⟨32974697, by rfl⟩ : syracuseStep 175865053 = 65949395) B65949395
theorem B21110017 : Blo 1646022 21110017 := bstep (se 2 (by rfl) ⟨7916256, by rfl⟩ : syracuseStep 21110017 = 15832513) B15832513
theorem B76086701 : Blo 1646022 76086701 := bstep (se 3 (by rfl) ⟨14266256, by rfl⟩ : syracuseStep 76086701 = 28532513) B28532513
theorem B4169171 : Blo 1646022 4169171 := bstep (se 1 (by rfl) ⟨3126878, by rfl⟩ : syracuseStep 4169171 = 6253757) B6253757
theorem B1646055 : Blo 1646022 1646055 := bstep (se 1 (by rfl) ⟨1234541, by rfl⟩ : syracuseStep 1646055 = 2469083) B2469083
theorem B4169191 : Blo 1646022 4169191 := bstep (se 1 (by rfl) ⟨3126893, by rfl⟩ : syracuseStep 4169191 = 6253787) B6253787
theorem B1646171 : Blo 1646022 1646171 := bstep (se 1 (by rfl) ⟨1234628, by rfl⟩ : syracuseStep 1646171 = 2469257) B2469257
theorem B2817679 : Blo 1646022 2817679 := bstep (se 1 (by rfl) ⟨2113259, by rfl⟩ : syracuseStep 2817679 = 4226519) B4226519
theorem B5561999 : Blo 1646022 5561999 := bstep (se 1 (by rfl) ⟨4171499, by rfl⟩ : syracuseStep 5561999 = 8342999) B8342999
theorem B1646407 : Blo 1646022 1646407 := bstep (se 1 (by rfl) ⟨1234805, by rfl⟩ : syracuseStep 1646407 = 2469611) B2469611
theorem B2637689 : Blo 1646022 2637689 := bstep (se 2 (by rfl) ⟨989133, by rfl⟩ : syracuseStep 2637689 = 1978267) B1978267
theorem B3170219 : Blo 1646022 3170219 := bstep (se 1 (by rfl) ⟨2377664, by rfl⟩ : syracuseStep 3170219 = 4755329) B4755329
theorem B1646559 : Blo 1646022 1646559 := bstep (se 1 (by rfl) ⟨1234919, by rfl⟩ : syracuseStep 1646559 = 2469839) B2469839
theorem B1646783 : Blo 1646022 1646783 := bstep (se 1 (by rfl) ⟨1235087, by rfl⟩ : syracuseStep 1646783 = 2470175) B2470175
theorem B1646799 : Blo 1646022 1646799 := bstep (se 1 (by rfl) ⟨1235099, by rfl⟩ : syracuseStep 1646799 = 2470199) B2470199
theorem B5005567 : Blo 1646022 5005567 := bstep (se 1 (by rfl) ⟨3754175, by rfl⟩ : syracuseStep 5005567 = 7508351) B7508351
theorem B1646847 : Blo 1646022 1646847 := bstep (se 1 (by rfl) ⟨1235135, by rfl⟩ : syracuseStep 1646847 = 2470271) B2470271
theorem B1646895 : Blo 1646022 1646895 := bstep (se 1 (by rfl) ⟨1235171, by rfl⟩ : syracuseStep 1646895 = 2470343) B2470343
theorem B3957275 : Blo 1646022 3957275 := bstep (se 1 (by rfl) ⟨2967956, by rfl⟩ : syracuseStep 3957275 = 5935913) B5935913
theorem B1647131 : Blo 1646022 1647131 := bstep (se 1 (by rfl) ⟨1235348, by rfl⟩ : syracuseStep 1647131 = 2470697) B2470697
theorem B1647135 : Blo 1646022 1647135 := bstep (se 1 (by rfl) ⟨1235351, by rfl⟩ : syracuseStep 1647135 = 2470703) B2470703
theorem B14066237 : Blo 1646022 14066237 := bstep (se 3 (by rfl) ⟨2637419, by rfl⟩ : syracuseStep 14066237 = 5274839) B5274839
theorem B1852015 : Blo 1646022 1852015 := bstep (se 1 (by rfl) ⟨1389011, by rfl⟩ : syracuseStep 1852015 = 2778023) B2778023
theorem B1647215 : Blo 1646022 1647215 := bstep (se 1 (by rfl) ⟨1235411, by rfl⟩ : syracuseStep 1647215 = 2470823) B2470823
theorem B7914145 : Blo 1646022 7914145 := bstep (se 2 (by rfl) ⟨2967804, by rfl⟩ : syracuseStep 7914145 = 5935609) B5935609
theorem B1647271 : Blo 1646022 1647271 := bstep (se 1 (by rfl) ⟨1235453, by rfl⟩ : syracuseStep 1647271 = 2470907) B2470907
theorem B2777807 : Blo 1646022 2777807 := bstep (se 1 (by rfl) ⟨2083355, by rfl⟩ : syracuseStep 2777807 = 4166711) B4166711
theorem B1647311 : Blo 1646022 1647311 := bstep (se 1 (by rfl) ⟨1235483, by rfl⟩ : syracuseStep 1647311 = 2470967) B2470967
theorem B1852123 : Blo 1646022 1852123 := bstep (se 1 (by rfl) ⟨1389092, by rfl⟩ : syracuseStep 1852123 = 2778185) B2778185
theorem B1647391 : Blo 1646022 1647391 := bstep (se 1 (by rfl) ⟨1235543, by rfl⟩ : syracuseStep 1647391 = 2471087) B2471087
theorem B12510125 : Blo 1646022 12510125 := bstep (se 3 (by rfl) ⟨2345648, by rfl⟩ : syracuseStep 12510125 = 4691297) B4691297
theorem B3703751 : Blo 1646022 3703751 := bstep (se 1 (by rfl) ⟨2777813, by rfl⟩ : syracuseStep 3703751 = 5555627) B5555627
theorem B1647663 : Blo 1646022 1647663 := bstep (se 1 (by rfl) ⟨1235747, by rfl⟩ : syracuseStep 1647663 = 2471495) B2471495
theorem B4228159 : Blo 1646022 4228159 := bstep (se 1 (by rfl) ⟨3171119, by rfl⟩ : syracuseStep 4228159 = 6342239) B6342239
theorem B11265097 : Blo 1646022 11265097 := bstep (se 2 (by rfl) ⟨4224411, by rfl⟩ : syracuseStep 11265097 = 8448823) B8448823
theorem B1647727 : Blo 1646022 1647727 := bstep (se 1 (by rfl) ⟨1235795, by rfl⟩ : syracuseStep 1647727 = 2471591) B2471591
theorem B1647783 : Blo 1646022 1647783 := bstep (se 1 (by rfl) ⟨1235837, by rfl⟩ : syracuseStep 1647783 = 2471675) B2471675
theorem B1647807 : Blo 1646022 1647807 := bstep (se 1 (by rfl) ⟨1235855, by rfl⟩ : syracuseStep 1647807 = 2471711) B2471711
theorem B1647839 : Blo 1646022 1647839 := bstep (se 1 (by rfl) ⟨1235879, by rfl⟩ : syracuseStep 1647839 = 2471759) B2471759
theorem B3704111 : Blo 1646022 3704111 := bstep (se 1 (by rfl) ⟨2778083, by rfl⟩ : syracuseStep 3704111 = 5556167) B5556167
theorem B1647919 : Blo 1646022 1647919 := bstep (se 1 (by rfl) ⟨1235939, by rfl⟩ : syracuseStep 1647919 = 2471879) B2471879
theorem B13362707 : Blo 1646022 13362707 := bstep (se 1 (by rfl) ⟨10022030, by rfl⟩ : syracuseStep 13362707 = 20044061) B20044061
theorem B2344555 : Blo 1646022 2344555 := bstep (se 1 (by rfl) ⟨1758416, by rfl⟩ : syracuseStep 2344555 = 3516833) B3516833
theorem B3704615 : Blo 1646022 3704615 := bstep (se 1 (by rfl) ⟨2778461, by rfl⟩ : syracuseStep 3704615 = 5556923) B5556923
theorem B8333279 : Blo 1646022 8333279 := bstep (se 1 (by rfl) ⟨6249959, by rfl⟩ : syracuseStep 8333279 = 12499919) B12499919
theorem B2779103 : Blo 1646022 2779103 := bstep (se 1 (by rfl) ⟨2084327, by rfl⟩ : syracuseStep 2779103 = 4168655) B4168655
theorem B15018011 : Blo 1646022 15018011 := bstep (se 1 (by rfl) ⟨11263508, by rfl⟩ : syracuseStep 15018011 = 22527017) B22527017
theorem B3704993 : Blo 1646022 3704993 := bstep (se 2 (by rfl) ⟨1389372, by rfl⟩ : syracuseStep 3704993 = 2778745) B2778745
theorem B28133567 : Blo 1646022 28133567 := bstep (se 1 (by rfl) ⟨21100175, by rfl⟩ : syracuseStep 28133567 = 42200351) B42200351
theorem B4753631 : Blo 1646022 4753631 := bstep (se 1 (by rfl) ⟨3565223, by rfl⟩ : syracuseStep 4753631 = 7130447) B7130447
theorem B2779447 : Blo 1646022 2779447 := bstep (se 1 (by rfl) ⟨2084585, by rfl⟩ : syracuseStep 2779447 = 4169171) B4169171
theorem B10013179 : Blo 1646022 10013179 := bstep (se 1 (by rfl) ⟨7509884, by rfl⟩ : syracuseStep 10013179 = 15019769) B15019769
theorem B7031411 : Blo 1646022 7031411 := bstep (se 1 (by rfl) ⟨5273558, by rfl⟩ : syracuseStep 7031411 = 10547117) B10547117
theorem B3705641 : Blo 1646022 3705641 := bstep (se 2 (by rfl) ⟨1389615, by rfl⟩ : syracuseStep 3705641 = 2779231) B2779231
theorem B6179689 : Blo 1646022 6179689 := bstep (se 2 (by rfl) ⟨2317383, by rfl⟩ : syracuseStep 6179689 = 4634767) B4634767
theorem B7916393 : Blo 1646022 7916393 := bstep (se 2 (by rfl) ⟨2968647, by rfl⟩ : syracuseStep 7916393 = 5937295) B5937295
theorem B7130081 : Blo 1646022 7130081 := bstep (se 2 (by rfl) ⟨2673780, by rfl⟩ : syracuseStep 7130081 = 5347561) B5347561
theorem B2673659 : Blo 1646022 2673659 := bstep (se 1 (by rfl) ⟨2005244, by rfl⟩ : syracuseStep 2673659 = 4010489) B4010489
theorem B3705911 : Blo 1646022 3705911 := bstep (se 1 (by rfl) ⟨2779433, by rfl⟩ : syracuseStep 3705911 = 5558867) B5558867
theorem B8342675 : Blo 1646022 8342675 := bstep (se 1 (by rfl) ⟨6257006, by rfl⟩ : syracuseStep 8342675 = 12514013) B12514013
theorem B15027353 : Blo 1646022 15027353 := bstep (se 2 (by rfl) ⟨5635257, by rfl⟩ : syracuseStep 15027353 = 11270515) B11270515
theorem B12512555 : Blo 1646022 12512555 := bstep (se 1 (by rfl) ⟨9384416, by rfl⟩ : syracuseStep 12512555 = 18768833) B18768833
theorem B135195965 : Blo 1646022 135195965 := bstep (se 3 (by rfl) ⟨25349243, by rfl⟩ : syracuseStep 135195965 = 50698487) B50698487
theorem B4689247 : Blo 1646022 4689247 := bstep (se 1 (by rfl) ⟨3516935, by rfl⟩ : syracuseStep 4689247 = 7033871) B7033871
theorem B2469275 : Blo 1646022 2469275 := bstep (se 1 (by rfl) ⟨1851956, by rfl⟩ : syracuseStep 2469275 = 3703913) B3703913
theorem B9383323 : Blo 1646022 9383323 := bstep (se 1 (by rfl) ⟨7037492, by rfl⟩ : syracuseStep 9383323 = 14074985) B14074985
theorem B7515575 : Blo 1646022 7515575 := bstep (se 1 (by rfl) ⟨5636681, by rfl⟩ : syracuseStep 7515575 = 11273363) B11273363
theorem B3755489 : Blo 1646022 3755489 := bstep (se 2 (by rfl) ⟨1408308, by rfl⟩ : syracuseStep 3755489 = 2816617) B2816617
theorem B3706343 : Blo 1646022 3706343 := bstep (se 1 (by rfl) ⟨2779757, by rfl⟩ : syracuseStep 3706343 = 5559515) B5559515
theorem B2780743 : Blo 1646022 2780743 := bstep (se 1 (by rfl) ⟨2085557, by rfl⟩ : syracuseStep 2780743 = 4171115) B4171115
theorem B17141395 : Blo 1646022 17141395 := bstep (se 1 (by rfl) ⟨12856046, by rfl⟩ : syracuseStep 17141395 = 25712093) B25712093
theorem B3124919 : Blo 1646022 3124919 := bstep (se 1 (by rfl) ⟨2343689, by rfl⟩ : syracuseStep 3124919 = 4687379) B4687379
theorem B7917335 : Blo 1646022 7917335 := bstep (se 1 (by rfl) ⟨5938001, by rfl⟩ : syracuseStep 7917335 = 11876003) B11876003
theorem B2469695 : Blo 1646022 2469695 := bstep (se 1 (by rfl) ⟨1852271, by rfl⟩ : syracuseStep 2469695 = 3704543) B3704543
theorem B8023951 : Blo 1646022 8023951 := bstep (se 1 (by rfl) ⟨6017963, by rfl⟩ : syracuseStep 8023951 = 12035927) B12035927
theorem B2469881 : Blo 1646022 2469881 := bstep (se 2 (by rfl) ⟨926205, by rfl⟩ : syracuseStep 2469881 = 1852411) B1852411
theorem B3706919 : Blo 1646022 3706919 := bstep (se 1 (by rfl) ⟨2780189, by rfl⟩ : syracuseStep 3706919 = 5560379) B5560379
theorem B5558327 : Blo 1646022 5558327 := bstep (se 1 (by rfl) ⟨4168745, by rfl⟩ : syracuseStep 5558327 = 8337491) B8337491
theorem B9375851 : Blo 1646022 9375851 := bstep (se 1 (by rfl) ⟨7031888, by rfl⟩ : syracuseStep 9375851 = 14063777) B14063777
theorem B2969707 : Blo 1646022 2969707 := bstep (se 1 (by rfl) ⟨2227280, by rfl⟩ : syracuseStep 2969707 = 4454561) B4454561
theorem B3125375 : Blo 1646022 3125375 := bstep (se 1 (by rfl) ⟨2344031, by rfl⟩ : syracuseStep 3125375 = 4688063) B4688063
theorem B3707099 : Blo 1646022 3707099 := bstep (se 1 (by rfl) ⟨2780324, by rfl⟩ : syracuseStep 3707099 = 5560649) B5560649
theorem B2470121 : Blo 1646022 2470121 := bstep (se 2 (by rfl) ⟨926295, by rfl⟩ : syracuseStep 2470121 = 1852591) B1852591
theorem B2470247 : Blo 1646022 2470247 := bstep (se 1 (by rfl) ⟨1852685, by rfl⟩ : syracuseStep 2470247 = 3705371) B3705371
theorem B5558651 : Blo 1646022 5558651 := bstep (se 1 (by rfl) ⟨4168988, by rfl⟩ : syracuseStep 5558651 = 8337977) B8337977
theorem B3707369 : Blo 1646022 3707369 := bstep (se 2 (by rfl) ⟨1390263, by rfl⟩ : syracuseStep 3707369 = 2780527) B2780527
theorem B5558921 : Blo 1646022 5558921 := bstep (se 2 (by rfl) ⟨2084595, by rfl⟩ : syracuseStep 5558921 = 4169191) B4169191
theorem B8336033 : Blo 1646022 8336033 := bstep (se 2 (by rfl) ⟨3126012, by rfl⟩ : syracuseStep 8336033 = 6252025) B6252025
theorem B3756905 : Blo 1646022 3756905 := bstep (se 2 (by rfl) ⟨1408839, by rfl⟩ : syracuseStep 3756905 = 2817679) B2817679
theorem B2470793 : Blo 1646022 2470793 := bstep (se 2 (by rfl) ⟨926547, by rfl⟩ : syracuseStep 2470793 = 1853095) B1853095
theorem B3707873 : Blo 1646022 3707873 := bstep (se 2 (by rfl) ⟨1390452, by rfl⟩ : syracuseStep 3707873 = 2780905) B2780905
theorem B7033837 : Blo 1646022 7033837 := bstep (se 3 (by rfl) ⟨1318844, by rfl⟩ : syracuseStep 7033837 = 2637689) B2637689
theorem B3707999 : Blo 1646022 3707999 := bstep (se 1 (by rfl) ⟨2780999, by rfl⟩ : syracuseStep 3707999 = 5561999) B5561999
theorem B3126377 : Blo 1646022 3126377 := bstep (se 2 (by rfl) ⟨1172391, by rfl⟩ : syracuseStep 3126377 = 2344783) B2344783
theorem B4691105 : Blo 1646022 4691105 := bstep (se 2 (by rfl) ⟨1759164, by rfl⟩ : syracuseStep 4691105 = 3518329) B3518329
theorem B2471177 : Blo 1646022 2471177 := bstep (se 2 (by rfl) ⟨926691, by rfl⟩ : syracuseStep 2471177 = 1853383) B1853383
theorem B15832361 : Blo 1646022 15832361 := bstep (se 2 (by rfl) ⟨5937135, by rfl⟩ : syracuseStep 15832361 = 11874271) B11874271
theorem B2471231 : Blo 1646022 2471231 := bstep (se 1 (by rfl) ⟨1853423, by rfl⟩ : syracuseStep 2471231 = 3706847) B3706847
theorem B4167247 : Blo 1646022 4167247 := bstep (se 1 (by rfl) ⟨3125435, by rfl⟩ : syracuseStep 4167247 = 6250871) B6250871
theorem B5011055 : Blo 1646022 5011055 := bstep (se 1 (by rfl) ⟨3758291, by rfl⟩ : syracuseStep 5011055 = 7516583) B7516583
theorem B2471657 : Blo 1646022 2471657 := bstep (se 2 (by rfl) ⟨926871, by rfl⟩ : syracuseStep 2471657 = 1853743) B1853743
theorem B2471663 : Blo 1646022 2471663 := bstep (se 1 (by rfl) ⟨1853747, by rfl⟩ : syracuseStep 2471663 = 3707495) B3707495
theorem B8451901 : Blo 1646022 8451901 := bstep (se 3 (by rfl) ⟨1584731, by rfl⟩ : syracuseStep 8451901 = 3169463) B3169463
theorem B4167521 : Blo 1646022 4167521 := bstep (se 2 (by rfl) ⟨1562820, by rfl⟩ : syracuseStep 4167521 = 3125641) B3125641
theorem B4167895 : Blo 1646022 4167895 := bstep (se 1 (by rfl) ⟨3125921, by rfl⟩ : syracuseStep 4167895 = 6251843) B6251843
theorem B26417423 : Blo 1646022 26417423 := bstep (se 1 (by rfl) ⟨19813067, by rfl⟩ : syracuseStep 26417423 = 39626135) B39626135
theorem B19020199 : Blo 1646022 19020199 := bstep (se 1 (by rfl) ⟨14265149, by rfl⟩ : syracuseStep 19020199 = 28530299) B28530299
theorem B3128033 : Blo 1646022 3128033 := bstep (se 2 (by rfl) ⟨1173012, by rfl⟩ : syracuseStep 3128033 = 2346025) B2346025
theorem B35617619 : Blo 1646022 35617619 := bstep (se 1 (by rfl) ⟨26713214, by rfl⟩ : syracuseStep 35617619 = 53426429) B53426429
theorem B5938115 : Blo 1646022 5938115 := bstep (se 1 (by rfl) ⟨4453586, by rfl⟩ : syracuseStep 5938115 = 8907173) B8907173
theorem B9378767 : Blo 1646022 9378767 := bstep (se 1 (by rfl) ⟨7034075, by rfl⟩ : syracuseStep 9378767 = 14068151) B14068151
theorem B234486737 : Blo 1646022 234486737 := bstep (se 2 (by rfl) ⟨87932526, by rfl⟩ : syracuseStep 234486737 = 175865053) B175865053
theorem B28146689 : Blo 1646022 28146689 := bstep (se 2 (by rfl) ⟨10555008, by rfl⟩ : syracuseStep 28146689 = 21110017) B21110017
theorem B1646031 : Blo 1646022 1646031 := bstep (se 1 (by rfl) ⟨1234523, by rfl⟩ : syracuseStep 1646031 = 2469047) B2469047
theorem B28155437 : Blo 1646022 28155437 := bstep (se 3 (by rfl) ⟨5279144, by rfl⟩ : syracuseStep 28155437 = 10558289) B10558289
theorem B17800813 : Blo 1646022 17800813 := bstep (se 3 (by rfl) ⟨3337652, by rfl⟩ : syracuseStep 17800813 = 6675305) B6675305
theorem B1646191 : Blo 1646022 1646191 := bstep (se 1 (by rfl) ⟨1234643, by rfl⟩ : syracuseStep 1646191 = 2469287) B2469287
theorem B50724467 : Blo 1646022 50724467 := bstep (se 1 (by rfl) ⟨38043350, by rfl⟩ : syracuseStep 50724467 = 76086701) B76086701
theorem B1646247 : Blo 1646022 1646247 := bstep (se 1 (by rfl) ⟨1234685, by rfl⟩ : syracuseStep 1646247 = 2469371) B2469371
theorem B1646311 : Blo 1646022 1646311 := bstep (se 1 (by rfl) ⟨1234733, by rfl⟩ : syracuseStep 1646311 = 2469467) B2469467
theorem B8453917 : Blo 1646022 8453917 := bstep (se 3 (by rfl) ⟨1585109, by rfl⟩ : syracuseStep 8453917 = 3170219) B3170219
theorem B1646367 : Blo 1646022 1646367 := bstep (se 1 (by rfl) ⟨1234775, by rfl⟩ : syracuseStep 1646367 = 2469551) B2469551
theorem B1646447 : Blo 1646022 1646447 := bstep (se 1 (by rfl) ⟨1234835, by rfl⟩ : syracuseStep 1646447 = 2469671) B2469671
theorem B3956591 : Blo 1646022 3956591 := bstep (se 1 (by rfl) ⟨2967443, by rfl⟩ : syracuseStep 3956591 = 5934887) B5934887
theorem B1646503 : Blo 1646022 1646503 := bstep (se 1 (by rfl) ⟨1234877, by rfl⟩ : syracuseStep 1646503 = 2469755) B2469755
theorem B6250567 : Blo 1646022 6250567 := bstep (se 1 (by rfl) ⟨4687925, by rfl⟩ : syracuseStep 6250567 = 9375851) B9375851
theorem B1646747 : Blo 1646022 1646747 := bstep (se 1 (by rfl) ⟨1235060, by rfl⟩ : syracuseStep 1646747 = 2470121) B2470121
theorem B1646831 : Blo 1646022 1646831 := bstep (se 1 (by rfl) ⟨1235123, by rfl⟩ : syracuseStep 1646831 = 2470247) B2470247
theorem B2638183 : Blo 1646022 2638183 := bstep (se 1 (by rfl) ⟨1978637, by rfl⟩ : syracuseStep 2638183 = 3957275) B3957275
theorem B1851871 : Blo 1646022 1851871 := bstep (se 1 (by rfl) ⟨1388903, by rfl⟩ : syracuseStep 1851871 = 2777807) B2777807
theorem B1647195 : Blo 1646022 1647195 := bstep (se 1 (by rfl) ⟨1235396, by rfl⟩ : syracuseStep 1647195 = 2470793) B2470793
theorem B8340083 : Blo 1646022 8340083 := bstep (se 1 (by rfl) ⟨6255062, by rfl⟩ : syracuseStep 8340083 = 12510125) B12510125
theorem B1647451 : Blo 1646022 1647451 := bstep (se 1 (by rfl) ⟨1235588, by rfl⟩ : syracuseStep 1647451 = 2471177) B2471177
theorem B1647487 : Blo 1646022 1647487 := bstep (se 1 (by rfl) ⟨1235615, by rfl⟩ : syracuseStep 1647487 = 2471231) B2471231
theorem B10552193 : Blo 1646022 10552193 := bstep (se 2 (by rfl) ⟨3957072, by rfl⟩ : syracuseStep 10552193 = 7914145) B7914145
theorem B1647771 : Blo 1646022 1647771 := bstep (se 1 (by rfl) ⟨1235828, by rfl⟩ : syracuseStep 1647771 = 2471657) B2471657
theorem B1647775 : Blo 1646022 1647775 := bstep (se 1 (by rfl) ⟨1235831, by rfl⟩ : syracuseStep 1647775 = 2471663) B2471663
theorem B2778347 : Blo 1646022 2778347 := bstep (se 1 (by rfl) ⟨2083760, by rfl⟩ : syracuseStep 2778347 = 4167521) B4167521
theorem B5555519 : Blo 1646022 5555519 := bstep (se 1 (by rfl) ⟨4166639, by rfl⟩ : syracuseStep 5555519 = 8333279) B8333279
theorem B1852735 : Blo 1646022 1852735 := bstep (se 1 (by rfl) ⟨1389551, by rfl⟩ : syracuseStep 1852735 = 2779103) B2779103
theorem B10012007 : Blo 1646022 10012007 := bstep (se 1 (by rfl) ⟨7509005, by rfl⟩ : syracuseStep 10012007 = 15018011) B15018011
theorem B5637545 : Blo 1646022 5637545 := bstep (se 2 (by rfl) ⟨2114079, by rfl⟩ : syracuseStep 5637545 = 4228159) B4228159
theorem B4687607 : Blo 1646022 4687607 := bstep (se 1 (by rfl) ⟨3515705, by rfl⟩ : syracuseStep 4687607 = 7031411) B7031411
theorem B6252329 : Blo 1646022 6252329 := bstep (se 2 (by rfl) ⟨2344623, by rfl⟩ : syracuseStep 6252329 = 4689247) B4689247
theorem B8333117 : Blo 1646022 8333117 := bstep (se 3 (by rfl) ⟨1562459, by rfl⟩ : syracuseStep 8333117 = 3124919) B3124919
theorem B12511097 : Blo 1646022 12511097 := bstep (se 2 (by rfl) ⟨4691661, by rfl⟩ : syracuseStep 12511097 = 9383323) B9383323
theorem B6252511 : Blo 1646022 6252511 := bstep (se 1 (by rfl) ⟨4689383, by rfl⟩ : syracuseStep 6252511 = 9378767) B9378767
theorem B4753387 : Blo 1646022 4753387 := bstep (se 1 (by rfl) ⟨3565040, by rfl⟩ : syracuseStep 4753387 = 7130081) B7130081
theorem B5556329 : Blo 1646022 5556329 := bstep (se 2 (by rfl) ⟨2083623, by rfl⟩ : syracuseStep 5556329 = 4167247) B4167247
theorem B23734417 : Blo 1646022 23734417 := bstep (se 2 (by rfl) ⟨8900406, by rfl⟩ : syracuseStep 23734417 = 17800813) B17800813
theorem B8341703 : Blo 1646022 8341703 := bstep (se 1 (by rfl) ⟨6256277, by rfl⟩ : syracuseStep 8341703 = 12512555) B12512555
theorem B90130643 : Blo 1646022 90130643 := bstep (se 1 (by rfl) ⟨67597982, by rfl⟩ : syracuseStep 90130643 = 135195965) B135195965
theorem B18770291 : Blo 1646022 18770291 := bstep (se 1 (by rfl) ⟨14077718, by rfl⟩ : syracuseStep 18770291 = 28155437) B28155437
theorem B5278223 : Blo 1646022 5278223 := bstep (se 1 (by rfl) ⟨3958667, by rfl⟩ : syracuseStep 5278223 = 7917335) B7917335
theorem B7129757 : Blo 1646022 7129757 := bstep (se 3 (by rfl) ⟨1336829, by rfl⟩ : syracuseStep 7129757 = 2673659) B2673659
theorem B3705551 : Blo 1646022 3705551 := bstep (se 1 (by rfl) ⟨2779163, by rfl⟩ : syracuseStep 3705551 = 5558327) B5558327
theorem B2083583 : Blo 1646022 2083583 := bstep (se 1 (by rfl) ⟨1562687, by rfl⟩ : syracuseStep 2083583 = 3125375) B3125375
theorem B3959609 : Blo 1646022 3959609 := bstep (se 2 (by rfl) ⟨1484853, by rfl⟩ : syracuseStep 3959609 = 2969707) B2969707
theorem B3705767 : Blo 1646022 3705767 := bstep (se 1 (by rfl) ⟨2779325, by rfl⟩ : syracuseStep 3705767 = 5558651) B5558651
theorem B5557193 : Blo 1646022 5557193 := bstep (se 2 (by rfl) ⟨2083947, by rfl⟩ : syracuseStep 5557193 = 4167895) B4167895
theorem B3705929 : Blo 1646022 3705929 := bstep (se 2 (by rfl) ⟨1389723, by rfl⟩ : syracuseStep 3705929 = 2779447) B2779447
theorem B3705947 : Blo 1646022 3705947 := bstep (se 1 (by rfl) ⟨2779460, by rfl⟩ : syracuseStep 3705947 = 5558921) B5558921
theorem B5557355 : Blo 1646022 5557355 := bstep (se 1 (by rfl) ⟨4168016, by rfl⟩ : syracuseStep 5557355 = 8336033) B8336033
theorem B12504293 : Blo 1646022 12504293 := bstep (se 4 (by rfl) ⟨1172277, by rfl⟩ : syracuseStep 12504293 = 2344555) B2344555
theorem B2469167 : Blo 1646022 2469167 := bstep (se 1 (by rfl) ⟨1851875, by rfl⟩ : syracuseStep 2469167 = 3703751) B3703751
theorem B2469353 : Blo 1646022 2469353 := bstep (se 2 (by rfl) ⟨926007, by rfl⟩ : syracuseStep 2469353 = 1852015) B1852015
theorem B10554907 : Blo 1646022 10554907 := bstep (se 1 (by rfl) ⟨7916180, by rfl⟩ : syracuseStep 10554907 = 15832361) B15832361
theorem B2469407 : Blo 1646022 2469407 := bstep (se 1 (by rfl) ⟨1852055, by rfl⟩ : syracuseStep 2469407 = 3704111) B3704111
theorem B2469497 : Blo 1646022 2469497 := bstep (se 2 (by rfl) ⟨926061, by rfl⟩ : syracuseStep 2469497 = 1852123) B1852123
theorem B8908471 : Blo 1646022 8908471 := bstep (se 1 (by rfl) ⟨6681353, by rfl⟩ : syracuseStep 8908471 = 13362707) B13362707
theorem B2469743 : Blo 1646022 2469743 := bstep (se 1 (by rfl) ⟨1852307, by rfl⟩ : syracuseStep 2469743 = 3704615) B3704615
theorem B15020129 : Blo 1646022 15020129 := bstep (se 2 (by rfl) ⟨5632548, by rfl⟩ : syracuseStep 15020129 = 11265097) B11265097
theorem B2469995 : Blo 1646022 2469995 := bstep (se 1 (by rfl) ⟨1852496, by rfl⟩ : syracuseStep 2469995 = 3704993) B3704993
theorem B18755711 : Blo 1646022 18755711 := bstep (se 1 (by rfl) ⟨14066783, by rfl⟩ : syracuseStep 18755711 = 28133567) B28133567
theorem B2085355 : Blo 1646022 2085355 := bstep (se 1 (by rfl) ⟨1564016, by rfl⟩ : syracuseStep 2085355 = 3128033) B3128033
theorem B2470427 : Blo 1646022 2470427 := bstep (se 1 (by rfl) ⟨1852820, by rfl⟩ : syracuseStep 2470427 = 3705641) B3705641
theorem B23745079 : Blo 1646022 23745079 := bstep (se 1 (by rfl) ⟨17808809, by rfl⟩ : syracuseStep 23745079 = 35617619) B35617619
theorem B156324491 : Blo 1646022 156324491 := bstep (se 1 (by rfl) ⟨117243368, by rfl⟩ : syracuseStep 156324491 = 234486737) B234486737
theorem B18764459 : Blo 1646022 18764459 := bstep (se 1 (by rfl) ⟨14073344, by rfl⟩ : syracuseStep 18764459 = 28146689) B28146689
theorem B2470607 : Blo 1646022 2470607 := bstep (se 1 (by rfl) ⟨1852955, by rfl⟩ : syracuseStep 2470607 = 3705911) B3705911
theorem B3707657 : Blo 1646022 3707657 := bstep (se 2 (by rfl) ⟨1390371, by rfl⟩ : syracuseStep 3707657 = 2780743) B2780743
theorem B5010383 : Blo 1646022 5010383 := bstep (se 1 (by rfl) ⟨3757787, by rfl⟩ : syracuseStep 5010383 = 7515575) B7515575
theorem B2470895 : Blo 1646022 2470895 := bstep (se 1 (by rfl) ⟨1853171, by rfl⟩ : syracuseStep 2470895 = 3706343) B3706343
theorem B11269201 : Blo 1646022 11269201 := bstep (se 2 (by rfl) ⟨4225950, by rfl⟩ : syracuseStep 11269201 = 8451901) B8451901
theorem B2471279 : Blo 1646022 2471279 := bstep (se 1 (by rfl) ⟨1853459, by rfl⟩ : syracuseStep 2471279 = 3706919) B3706919
theorem B2471399 : Blo 1646022 2471399 := bstep (se 1 (by rfl) ⟨1853549, by rfl⟩ : syracuseStep 2471399 = 3707099) B3707099
theorem B8337005 : Blo 1646022 8337005 := bstep (se 3 (by rfl) ⟨1563188, by rfl⟩ : syracuseStep 8337005 = 3126377) B3126377
theorem B2471579 : Blo 1646022 2471579 := bstep (se 1 (by rfl) ⟨1853684, by rfl⟩ : syracuseStep 2471579 = 3707369) B3707369
theorem B6674089 : Blo 1646022 6674089 := bstep (se 2 (by rfl) ⟨2502783, by rfl⟩ : syracuseStep 6674089 = 5005567) B5005567
theorem B9377491 : Blo 1646022 9377491 := bstep (se 1 (by rfl) ⟨7033118, by rfl⟩ : syracuseStep 9377491 = 14066237) B14066237
theorem B25360265 : Blo 1646022 25360265 := bstep (se 2 (by rfl) ⟨9510099, by rfl⟩ : syracuseStep 25360265 = 19020199) B19020199
theorem B2504603 : Blo 1646022 2504603 := bstep (se 1 (by rfl) ⟨1878452, by rfl⟩ : syracuseStep 2504603 = 3756905) B3756905
theorem B2471915 : Blo 1646022 2471915 := bstep (se 1 (by rfl) ⟨1853936, by rfl⟩ : syracuseStep 2471915 = 3707873) B3707873
theorem B13350905 : Blo 1646022 13350905 := bstep (se 2 (by rfl) ⟨5006589, by rfl⟩ : syracuseStep 13350905 = 10013179) B10013179
theorem B2471999 : Blo 1646022 2471999 := bstep (se 1 (by rfl) ⟨1853999, by rfl⟩ : syracuseStep 2471999 = 3707999) B3707999
theorem B3127403 : Blo 1646022 3127403 := bstep (se 1 (by rfl) ⟨2345552, by rfl⟩ : syracuseStep 3127403 = 4691105) B4691105
theorem B3340703 : Blo 1646022 3340703 := bstep (se 1 (by rfl) ⟨2505527, by rfl⟩ : syracuseStep 3340703 = 5011055) B5011055
theorem B8239585 : Blo 1646022 8239585 := bstep (se 2 (by rfl) ⟨3089844, by rfl⟩ : syracuseStep 8239585 = 6179689) B6179689
theorem B9378449 : Blo 1646022 9378449 := bstep (se 2 (by rfl) ⟨3516918, by rfl⟩ : syracuseStep 9378449 = 7033837) B7033837
theorem B3169087 : Blo 1646022 3169087 := bstep (se 1 (by rfl) ⟨2376815, by rfl⟩ : syracuseStep 3169087 = 4753631) B4753631
theorem B17611615 : Blo 1646022 17611615 := bstep (se 1 (by rfl) ⟨13208711, by rfl⟩ : syracuseStep 17611615 = 26417423) B26417423
theorem B63339893 : Blo 1646022 63339893 := bstep (se 5 (by rfl) ⟨2969057, by rfl⟩ : syracuseStep 63339893 = 5938115) B5938115
theorem B5561783 : Blo 1646022 5561783 := bstep (se 1 (by rfl) ⟨4171337, by rfl⟩ : syracuseStep 5561783 = 8342675) B8342675
theorem B10018235 : Blo 1646022 10018235 := bstep (se 1 (by rfl) ⟨7513676, by rfl⟩ : syracuseStep 10018235 = 15027353) B15027353
theorem B22855193 : Blo 1646022 22855193 := bstep (se 2 (by rfl) ⟨8570697, by rfl⟩ : syracuseStep 22855193 = 17141395) B17141395
theorem B1646183 : Blo 1646022 1646183 := bstep (se 1 (by rfl) ⟨1234637, by rfl⟩ : syracuseStep 1646183 = 2469275) B2469275
theorem B21110381 : Blo 1646022 21110381 := bstep (se 3 (by rfl) ⟨3958196, by rfl⟩ : syracuseStep 21110381 = 7916393) B7916393
theorem B40058549 : Blo 1646022 40058549 := bstep (se 5 (by rfl) ⟨1877744, by rfl⟩ : syracuseStep 40058549 = 3755489) B3755489
theorem B11271889 : Blo 1646022 11271889 := bstep (se 2 (by rfl) ⟨4226958, by rfl⟩ : syracuseStep 11271889 = 8453917) B8453917
theorem B33816311 : Blo 1646022 33816311 := bstep (se 1 (by rfl) ⟨25362233, by rfl⟩ : syracuseStep 33816311 = 50724467) B50724467
theorem B10698601 : Blo 1646022 10698601 := bstep (se 2 (by rfl) ⟨4011975, by rfl⟩ : syracuseStep 10698601 = 8023951) B8023951
theorem B1646463 : Blo 1646022 1646463 := bstep (se 1 (by rfl) ⟨1234847, by rfl⟩ : syracuseStep 1646463 = 2469695) B2469695
theorem B2637727 : Blo 1646022 2637727 := bstep (se 1 (by rfl) ⟨1978295, by rfl⟩ : syracuseStep 2637727 = 3956591) B3956591
theorem B1646587 : Blo 1646022 1646587 := bstep (se 1 (by rfl) ⟨1234940, by rfl⟩ : syracuseStep 1646587 = 2469881) B2469881
theorem B1646663 : Blo 1646022 1646663 := bstep (se 1 (by rfl) ⟨1234997, by rfl⟩ : syracuseStep 1646663 = 2469995) B2469995
theorem B31645889 : Blo 1646022 31645889 := bstep (se 2 (by rfl) ⟨11867208, by rfl⟩ : syracuseStep 31645889 = 23734417) B23734417
theorem B1646951 : Blo 1646022 1646951 := bstep (se 1 (by rfl) ⟨1235213, by rfl⟩ : syracuseStep 1646951 = 2470427) B2470427
theorem B12509639 : Blo 1646022 12509639 := bstep (se 1 (by rfl) ⟨9382229, by rfl⟩ : syracuseStep 12509639 = 18764459) B18764459
theorem B1647071 : Blo 1646022 1647071 := bstep (se 1 (by rfl) ⟨1235303, by rfl⟩ : syracuseStep 1647071 = 2470607) B2470607
theorem B10986113 : Blo 1646022 10986113 := bstep (se 2 (by rfl) ⟨4119792, by rfl⟩ : syracuseStep 10986113 = 8239585) B8239585
theorem B1647263 : Blo 1646022 1647263 := bstep (se 1 (by rfl) ⟨1235447, by rfl⟩ : syracuseStep 1647263 = 2470895) B2470895
theorem B1852231 : Blo 1646022 1852231 := bstep (se 1 (by rfl) ⟨1389173, by rfl⟩ : syracuseStep 1852231 = 2778347) B2778347
theorem B3703679 : Blo 1646022 3703679 := bstep (se 1 (by rfl) ⟨2777759, by rfl⟩ : syracuseStep 3703679 = 5555519) B5555519
theorem B1647519 : Blo 1646022 1647519 := bstep (se 1 (by rfl) ⟨1235639, by rfl⟩ : syracuseStep 1647519 = 2471279) B2471279
theorem B1647599 : Blo 1646022 1647599 := bstep (se 1 (by rfl) ⟨1235699, by rfl⟩ : syracuseStep 1647599 = 2471399) B2471399
theorem B1647719 : Blo 1646022 1647719 := bstep (se 1 (by rfl) ⟨1235789, by rfl⟩ : syracuseStep 1647719 = 2471579) B2471579
theorem B5555411 : Blo 1646022 5555411 := bstep (se 1 (by rfl) ⟨4166558, by rfl⟩ : syracuseStep 5555411 = 8333117) B8333117
theorem B8340731 : Blo 1646022 8340731 := bstep (se 1 (by rfl) ⟨6255548, by rfl⟩ : syracuseStep 8340731 = 12511097) B12511097
theorem B1647943 : Blo 1646022 1647943 := bstep (se 1 (by rfl) ⟨1235957, by rfl⟩ : syracuseStep 1647943 = 2471915) B2471915
theorem B1647999 : Blo 1646022 1647999 := bstep (se 1 (by rfl) ⟨1235999, by rfl⟩ : syracuseStep 1647999 = 2471999) B2471999
theorem B3704219 : Blo 1646022 3704219 := bstep (se 1 (by rfl) ⟨2778164, by rfl⟩ : syracuseStep 3704219 = 5556329) B5556329
theorem B15025601 : Blo 1646022 15025601 := bstep (se 2 (by rfl) ⟨5634600, by rfl⟩ : syracuseStep 15025601 = 11269201) B11269201
theorem B16901797 : Blo 1646022 16901797 := bstep (se 4 (by rfl) ⟨1584543, by rfl⟩ : syracuseStep 16901797 = 3169087) B3169087
theorem B6252299 : Blo 1646022 6252299 := bstep (se 1 (by rfl) ⟨4689224, by rfl⟩ : syracuseStep 6252299 = 9378449) B9378449
theorem B4753171 : Blo 1646022 4753171 := bstep (se 1 (by rfl) ⟨3564878, by rfl⟩ : syracuseStep 4753171 = 7129757) B7129757
theorem B3704795 : Blo 1646022 3704795 := bstep (se 1 (by rfl) ⟨2778596, by rfl⟩ : syracuseStep 3704795 = 5557193) B5557193
theorem B5556221 : Blo 1646022 5556221 := bstep (se 3 (by rfl) ⟨1041791, by rfl⟩ : syracuseStep 5556221 = 2083583) B2083583
theorem B3704903 : Blo 1646022 3704903 := bstep (se 1 (by rfl) ⟨2778677, by rfl⟩ : syracuseStep 3704903 = 5557355) B5557355
theorem B14067877 : Blo 1646022 14067877 := bstep (se 4 (by rfl) ⟨1318863, by rfl⟩ : syracuseStep 14067877 = 2637727) B2637727
theorem B8898785 : Blo 1646022 8898785 := bstep (se 2 (by rfl) ⟨3337044, by rfl⟩ : syracuseStep 8898785 = 6674089) B6674089
theorem B12503321 : Blo 1646022 12503321 := bstep (se 2 (by rfl) ⟨4688745, by rfl⟩ : syracuseStep 12503321 = 9377491) B9377491
theorem B6678823 : Blo 1646022 6678823 := bstep (se 1 (by rfl) ⟨5009117, by rfl⟩ : syracuseStep 6678823 = 10018235) B10018235
theorem B14264801 : Blo 1646022 14264801 := bstep (se 2 (by rfl) ⟨5349300, by rfl⟩ : syracuseStep 14264801 = 10698601) B10698601
theorem B10013419 : Blo 1646022 10013419 := bstep (se 1 (by rfl) ⟨7510064, by rfl⟩ : syracuseStep 10013419 = 15020129) B15020129
theorem B12503807 : Blo 1646022 12503807 := bstep (se 1 (by rfl) ⟨9377855, by rfl⟩ : syracuseStep 12503807 = 18755711) B18755711
theorem B8334089 : Blo 1646022 8334089 := bstep (se 2 (by rfl) ⟨3125283, by rfl⟩ : syracuseStep 8334089 = 6250567) B6250567
theorem B3517577 : Blo 1646022 3517577 := bstep (se 2 (by rfl) ⟨1319091, by rfl⟩ : syracuseStep 3517577 = 2638183) B2638183
theorem B2469161 : Blo 1646022 2469161 := bstep (se 2 (by rfl) ⟨925935, by rfl⟩ : syracuseStep 2469161 = 1851871) B1851871
theorem B2780473 : Blo 1646022 2780473 := bstep (se 2 (by rfl) ⟨1042677, by rfl⟩ : syracuseStep 2780473 = 2085355) B2085355
theorem B5558003 : Blo 1646022 5558003 := bstep (se 1 (by rfl) ⟨4168502, by rfl⟩ : syracuseStep 5558003 = 8337005) B8337005
theorem B8908541 : Blo 1646022 8908541 := bstep (se 3 (by rfl) ⟨1670351, by rfl⟩ : syracuseStep 8908541 = 3340703) B3340703
theorem B23482153 : Blo 1646022 23482153 := bstep (se 2 (by rfl) ⟨8805807, by rfl⟩ : syracuseStep 23482153 = 17611615) B17611615
theorem B3125071 : Blo 1646022 3125071 := bstep (se 1 (by rfl) ⟨2343803, by rfl⟩ : syracuseStep 3125071 = 4687607) B4687607
theorem B8900603 : Blo 1646022 8900603 := bstep (se 1 (by rfl) ⟨6675452, by rfl⟩ : syracuseStep 8900603 = 13350905) B13350905
theorem B2084935 : Blo 1646022 2084935 := bstep (se 1 (by rfl) ⟨1563701, by rfl⟩ : syracuseStep 2084935 = 3127403) B3127403
theorem B12513527 : Blo 1646022 12513527 := bstep (se 1 (by rfl) ⟨9385145, by rfl⟩ : syracuseStep 12513527 = 18770291) B18770291
theorem B3518815 : Blo 1646022 3518815 := bstep (se 1 (by rfl) ⟨2639111, by rfl⟩ : syracuseStep 3518815 = 5278223) B5278223
theorem B2470313 : Blo 1646022 2470313 := bstep (se 2 (by rfl) ⟨926367, by rfl⟩ : syracuseStep 2470313 = 1852735) B1852735
theorem B2470367 : Blo 1646022 2470367 := bstep (se 1 (by rfl) ⟨1852775, by rfl⟩ : syracuseStep 2470367 = 3705551) B3705551
theorem B2470511 : Blo 1646022 2470511 := bstep (se 1 (by rfl) ⟨1852883, by rfl⟩ : syracuseStep 2470511 = 3705767) B3705767
theorem B2470619 : Blo 1646022 2470619 := bstep (se 1 (by rfl) ⟨1852964, by rfl⟩ : syracuseStep 2470619 = 3705929) B3705929
theorem B2470631 : Blo 1646022 2470631 := bstep (se 1 (by rfl) ⟨1852973, by rfl⟩ : syracuseStep 2470631 = 3705947) B3705947
theorem B8336195 : Blo 1646022 8336195 := bstep (se 1 (by rfl) ⟨6252146, by rfl⟩ : syracuseStep 8336195 = 12504293) B12504293
theorem B42226595 : Blo 1646022 42226595 := bstep (se 1 (by rfl) ⟨31669946, by rfl⟩ : syracuseStep 42226595 = 63339893) B63339893
theorem B15029185 : Blo 1646022 15029185 := bstep (se 2 (by rfl) ⟨5635944, by rfl⟩ : syracuseStep 15029185 = 11271889) B11271889
theorem B3707855 : Blo 1646022 3707855 := bstep (se 1 (by rfl) ⟨2780891, by rfl⟩ : syracuseStep 3707855 = 5561783) B5561783
theorem B25351397 : Blo 1646022 25351397 := bstep (se 4 (by rfl) ⟨2376693, by rfl⟩ : syracuseStep 25351397 = 4753387) B4753387
theorem B8336681 : Blo 1646022 8336681 := bstep (se 2 (by rfl) ⟨3126255, by rfl⟩ : syracuseStep 8336681 = 6252511) B6252511
theorem B5560055 : Blo 1646022 5560055 := bstep (se 1 (by rfl) ⟨4170041, by rfl⟩ : syracuseStep 5560055 = 8340083) B8340083
theorem B104216327 : Blo 1646022 104216327 := bstep (se 1 (by rfl) ⟨78162245, by rfl⟩ : syracuseStep 104216327 = 156324491) B156324491
theorem B2471771 : Blo 1646022 2471771 := bstep (se 1 (by rfl) ⟨1853828, by rfl⟩ : syracuseStep 2471771 = 3707657) B3707657
theorem B7034795 : Blo 1646022 7034795 := bstep (se 1 (by rfl) ⟨5276096, by rfl⟩ : syracuseStep 7034795 = 10552193) B10552193
theorem B31660105 : Blo 1646022 31660105 := bstep (se 2 (by rfl) ⟨11872539, by rfl⟩ : syracuseStep 31660105 = 23745079) B23745079
theorem B6674671 : Blo 1646022 6674671 := bstep (se 1 (by rfl) ⟨5006003, by rfl⟩ : syracuseStep 6674671 = 10012007) B10012007
theorem B3758363 : Blo 1646022 3758363 := bstep (se 1 (by rfl) ⟨2818772, by rfl⟩ : syracuseStep 3758363 = 5637545) B5637545
theorem B47511845 : Blo 1646022 47511845 := bstep (se 4 (by rfl) ⟨4454235, by rfl⟩ : syracuseStep 47511845 = 8908471) B8908471
theorem B4168219 : Blo 1646022 4168219 := bstep (se 1 (by rfl) ⟨3126164, by rfl⟩ : syracuseStep 4168219 = 6252329) B6252329
theorem B16906843 : Blo 1646022 16906843 := bstep (se 1 (by rfl) ⟨12680132, by rfl⟩ : syracuseStep 16906843 = 25360265) B25360265
theorem B1669735 : Blo 1646022 1669735 := bstep (se 1 (by rfl) ⟨1252301, by rfl⟩ : syracuseStep 1669735 = 2504603) B2504603
theorem B5561135 : Blo 1646022 5561135 := bstep (se 1 (by rfl) ⟨4170851, by rfl⟩ : syracuseStep 5561135 = 8341703) B8341703
theorem B60087095 : Blo 1646022 60087095 := bstep (se 1 (by rfl) ⟨45065321, by rfl⟩ : syracuseStep 60087095 = 90130643) B90130643
theorem B14073209 : Blo 1646022 14073209 := bstep (se 2 (by rfl) ⟨5277453, by rfl⟩ : syracuseStep 14073209 = 10554907) B10554907
theorem B10558957 : Blo 1646022 10558957 := bstep (se 3 (by rfl) ⟨1979804, by rfl⟩ : syracuseStep 10558957 = 3959609) B3959609
theorem B1646111 : Blo 1646022 1646111 := bstep (se 1 (by rfl) ⟨1234583, by rfl⟩ : syracuseStep 1646111 = 2469167) B2469167
theorem B1646235 : Blo 1646022 1646235 := bstep (se 1 (by rfl) ⟨1234676, by rfl⟩ : syracuseStep 1646235 = 2469353) B2469353
theorem B15236795 : Blo 1646022 15236795 := bstep (se 1 (by rfl) ⟨11427596, by rfl⟩ : syracuseStep 15236795 = 22855193) B22855193
theorem B1646271 : Blo 1646022 1646271 := bstep (se 1 (by rfl) ⟨1234703, by rfl⟩ : syracuseStep 1646271 = 2469407) B2469407
theorem B14073587 : Blo 1646022 14073587 := bstep (se 1 (by rfl) ⟨10555190, by rfl⟩ : syracuseStep 14073587 = 21110381) B21110381
theorem B1646331 : Blo 1646022 1646331 := bstep (se 1 (by rfl) ⟨1234748, by rfl⟩ : syracuseStep 1646331 = 2469497) B2469497
theorem B26705699 : Blo 1646022 26705699 := bstep (se 1 (by rfl) ⟨20029274, by rfl⟩ : syracuseStep 26705699 = 40058549) B40058549
theorem B22544207 : Blo 1646022 22544207 := bstep (se 1 (by rfl) ⟨16908155, by rfl⟩ : syracuseStep 22544207 = 33816311) B33816311
theorem B13361021 : Blo 1646022 13361021 := bstep (se 3 (by rfl) ⟨2505191, by rfl⟩ : syracuseStep 13361021 = 5010383) B5010383
theorem B1646495 : Blo 1646022 1646495 := bstep (se 1 (by rfl) ⟨1234871, by rfl⟩ : syracuseStep 1646495 = 2469743) B2469743
theorem B42213473 : Blo 1646022 42213473 := bstep (se 2 (by rfl) ⟨15830052, by rfl⟩ : syracuseStep 42213473 = 31660105) B31660105
theorem B1646875 : Blo 1646022 1646875 := bstep (se 1 (by rfl) ⟨1235156, by rfl⟩ : syracuseStep 1646875 = 2470313) B2470313
theorem B8339759 : Blo 1646022 8339759 := bstep (se 1 (by rfl) ⟨6254819, by rfl⟩ : syracuseStep 8339759 = 12509639) B12509639
theorem B1646911 : Blo 1646022 1646911 := bstep (se 1 (by rfl) ⟨1235183, by rfl⟩ : syracuseStep 1646911 = 2470367) B2470367
theorem B8905097 : Blo 1646022 8905097 := bstep (se 2 (by rfl) ⟨3339411, by rfl⟩ : syracuseStep 8905097 = 6678823) B6678823
theorem B1647007 : Blo 1646022 1647007 := bstep (se 1 (by rfl) ⟨1235255, by rfl⟩ : syracuseStep 1647007 = 2470511) B2470511
theorem B7324075 : Blo 1646022 7324075 := bstep (se 1 (by rfl) ⟨5493056, by rfl⟩ : syracuseStep 7324075 = 10986113) B10986113
theorem B1647079 : Blo 1646022 1647079 := bstep (se 1 (by rfl) ⟨1235309, by rfl⟩ : syracuseStep 1647079 = 2470619) B2470619
theorem B1647087 : Blo 1646022 1647087 := bstep (se 1 (by rfl) ⟨1235315, by rfl⟩ : syracuseStep 1647087 = 2470631) B2470631
theorem B3703607 : Blo 1646022 3703607 := bstep (se 1 (by rfl) ⟨2777705, by rfl⟩ : syracuseStep 3703607 = 5555411) B5555411
theorem B16900931 : Blo 1646022 16900931 := bstep (se 1 (by rfl) ⟨12675698, by rfl⟩ : syracuseStep 16900931 = 25351397) B25351397
theorem B40068269 : Blo 1646022 40068269 := bstep (se 3 (by rfl) ⟨7512800, by rfl⟩ : syracuseStep 40068269 = 15025601) B15025601
theorem B69477551 : Blo 1646022 69477551 := bstep (se 1 (by rfl) ⟨52108163, by rfl⟩ : syracuseStep 69477551 = 104216327) B104216327
theorem B1647847 : Blo 1646022 1647847 := bstep (se 1 (by rfl) ⟨1235885, by rfl⟩ : syracuseStep 1647847 = 2471771) B2471771
theorem B20038913 : Blo 1646022 20038913 := bstep (se 2 (by rfl) ⟨7514592, by rfl⟩ : syracuseStep 20038913 = 15029185) B15029185
theorem B3704147 : Blo 1646022 3704147 := bstep (se 1 (by rfl) ⟨2778110, by rfl⟩ : syracuseStep 3704147 = 5556221) B5556221
theorem B5932523 : Blo 1646022 5932523 := bstep (se 1 (by rfl) ⟨4449392, by rfl⟩ : syracuseStep 5932523 = 8898785) B8898785
theorem B5556059 : Blo 1646022 5556059 := bstep (se 1 (by rfl) ⟨4167044, by rfl⟩ : syracuseStep 5556059 = 8334089) B8334089
theorem B2345051 : Blo 1646022 2345051 := bstep (se 1 (by rfl) ⟨1758788, by rfl⟩ : syracuseStep 2345051 = 3517577) B3517577
theorem B9382139 : Blo 1646022 9382139 := bstep (se 1 (by rfl) ⟨7036604, by rfl⟩ : syracuseStep 9382139 = 14073209) B14073209
theorem B3705335 : Blo 1646022 3705335 := bstep (se 1 (by rfl) ⟨2779001, by rfl⟩ : syracuseStep 3705335 = 5558003) B5558003
theorem B9382391 : Blo 1646022 9382391 := bstep (se 1 (by rfl) ⟨7036793, by rfl⟩ : syracuseStep 9382391 = 14073587) B14073587
theorem B17803799 : Blo 1646022 17803799 := bstep (se 1 (by rfl) ⟨13352849, by rfl⟩ : syracuseStep 17803799 = 26705699) B26705699
theorem B8907347 : Blo 1646022 8907347 := bstep (se 1 (by rfl) ⟨6680510, by rfl⟩ : syracuseStep 8907347 = 13361021) B13361021
theorem B5933735 : Blo 1646022 5933735 := bstep (se 1 (by rfl) ⟨4450301, by rfl⟩ : syracuseStep 5933735 = 8900603) B8900603
theorem B2779913 : Blo 1646022 2779913 := bstep (se 2 (by rfl) ⟨1042467, by rfl⟩ : syracuseStep 2779913 = 2084935) B2084935
theorem B21097259 : Blo 1646022 21097259 := bstep (se 1 (by rfl) ⟨15822944, by rfl⟩ : syracuseStep 21097259 = 31645889) B31645889
theorem B8342351 : Blo 1646022 8342351 := bstep (se 1 (by rfl) ⟨6256763, by rfl⟩ : syracuseStep 8342351 = 12513527) B12513527
theorem B8899561 : Blo 1646022 8899561 := bstep (se 2 (by rfl) ⟨3337335, by rfl⟩ : syracuseStep 8899561 = 6674671) B6674671
theorem B5557463 : Blo 1646022 5557463 := bstep (se 1 (by rfl) ⟨4168097, by rfl⟩ : syracuseStep 5557463 = 8336195) B8336195
theorem B2469119 : Blo 1646022 2469119 := bstep (se 1 (by rfl) ⟨1851839, by rfl⟩ : syracuseStep 2469119 = 3703679) B3703679
theorem B28151063 : Blo 1646022 28151063 := bstep (se 1 (by rfl) ⟨21113297, by rfl⟩ : syracuseStep 28151063 = 42226595) B42226595
theorem B5557625 : Blo 1646022 5557625 := bstep (se 2 (by rfl) ⟨2084109, by rfl⟩ : syracuseStep 5557625 = 4168219) B4168219
theorem B5557787 : Blo 1646022 5557787 := bstep (se 1 (by rfl) ⟨4168340, by rfl⟩ : syracuseStep 5557787 = 8336681) B8336681
theorem B2469479 : Blo 1646022 2469479 := bstep (se 1 (by rfl) ⟨1852109, by rfl⟩ : syracuseStep 2469479 = 3704219) B3704219
theorem B2469641 : Blo 1646022 2469641 := bstep (se 2 (by rfl) ⟨926115, by rfl⟩ : syracuseStep 2469641 = 1852231) B1852231
theorem B3706703 : Blo 1646022 3706703 := bstep (se 1 (by rfl) ⟨2780027, by rfl⟩ : syracuseStep 3706703 = 5560055) B5560055
theorem B4689863 : Blo 1646022 4689863 := bstep (se 1 (by rfl) ⟨3517397, by rfl⟩ : syracuseStep 4689863 = 7034795) B7034795
theorem B2469863 : Blo 1646022 2469863 := bstep (se 1 (by rfl) ⟨1852397, by rfl⟩ : syracuseStep 2469863 = 3704795) B3704795
theorem B2469935 : Blo 1646022 2469935 := bstep (se 1 (by rfl) ⟨1852451, by rfl⟩ : syracuseStep 2469935 = 3704903) B3704903
theorem B8335547 : Blo 1646022 8335547 := bstep (se 1 (by rfl) ⟨6251660, by rfl⟩ : syracuseStep 8335547 = 12503321) B12503321
theorem B31674563 : Blo 1646022 31674563 := bstep (se 1 (by rfl) ⟨23755922, by rfl⟩ : syracuseStep 31674563 = 47511845) B47511845
theorem B3707297 : Blo 1646022 3707297 := bstep (se 2 (by rfl) ⟨1390236, by rfl⟩ : syracuseStep 3707297 = 2780473) B2780473
theorem B8335871 : Blo 1646022 8335871 := bstep (se 1 (by rfl) ⟨6251903, by rfl⟩ : syracuseStep 8335871 = 12503807) B12503807
theorem B3707423 : Blo 1646022 3707423 := bstep (se 1 (by rfl) ⟨2780567, by rfl⟩ : syracuseStep 3707423 = 5561135) B5561135
theorem B14078609 : Blo 1646022 14078609 := bstep (se 2 (by rfl) ⟨5279478, by rfl⟩ : syracuseStep 14078609 = 10558957) B10558957
theorem B6337561 : Blo 1646022 6337561 := bstep (se 2 (by rfl) ⟨2376585, by rfl⟩ : syracuseStep 6337561 = 4753171) B4753171
theorem B4166761 : Blo 1646022 4166761 := bstep (se 2 (by rfl) ⟨1562535, by rfl⟩ : syracuseStep 4166761 = 3125071) B3125071
theorem B15029471 : Blo 1646022 15029471 := bstep (se 1 (by rfl) ⟨11272103, by rfl⟩ : syracuseStep 15029471 = 22544207) B22544207
theorem B18757169 : Blo 1646022 18757169 := bstep (se 2 (by rfl) ⟨7033938, by rfl⟩ : syracuseStep 18757169 = 14067877) B14067877
theorem B4691753 : Blo 1646022 4691753 := bstep (se 2 (by rfl) ⟨1759407, by rfl⟩ : syracuseStep 4691753 = 3518815) B3518815
theorem B2471903 : Blo 1646022 2471903 := bstep (se 1 (by rfl) ⟨1853927, by rfl⟩ : syracuseStep 2471903 = 3707855) B3707855
theorem B22542457 : Blo 1646022 22542457 := bstep (se 2 (by rfl) ⟨8453421, by rfl⟩ : syracuseStep 22542457 = 16906843) B16906843
theorem B2226313 : Blo 1646022 2226313 := bstep (se 2 (by rfl) ⟨834867, by rfl⟩ : syracuseStep 2226313 = 1669735) B1669735
theorem B5560487 : Blo 1646022 5560487 := bstep (se 1 (by rfl) ⟨4170365, by rfl⟩ : syracuseStep 5560487 = 8340731) B8340731
theorem B13351225 : Blo 1646022 13351225 := bstep (se 2 (by rfl) ⟨5006709, by rfl⟩ : syracuseStep 13351225 = 10013419) B10013419
theorem B4168199 : Blo 1646022 4168199 := bstep (se 1 (by rfl) ⟨3126149, by rfl⟩ : syracuseStep 4168199 = 6252299) B6252299
theorem B2505575 : Blo 1646022 2505575 := bstep (se 1 (by rfl) ⟨1879181, by rfl⟩ : syracuseStep 2505575 = 3758363) B3758363
theorem B9509867 : Blo 1646022 9509867 := bstep (se 1 (by rfl) ⟨7132400, by rfl⟩ : syracuseStep 9509867 = 14264801) B14264801
theorem B40631453 : Blo 1646022 40631453 := bstep (se 3 (by rfl) ⟨7618397, by rfl⟩ : syracuseStep 40631453 = 15236795) B15236795
theorem B40058063 : Blo 1646022 40058063 := bstep (se 1 (by rfl) ⟨30043547, by rfl⟩ : syracuseStep 40058063 = 60087095) B60087095
theorem B1646107 : Blo 1646022 1646107 := bstep (se 1 (by rfl) ⟨1234580, by rfl⟩ : syracuseStep 1646107 = 2469161) B2469161
theorem B22535729 : Blo 1646022 22535729 := bstep (se 2 (by rfl) ⟨8450898, by rfl⟩ : syracuseStep 22535729 = 16901797) B16901797
theorem B31309537 : Blo 1646022 31309537 := bstep (se 2 (by rfl) ⟨11741076, by rfl⟩ : syracuseStep 31309537 = 23482153) B23482153
theorem B5939027 : Blo 1646022 5939027 := bstep (se 1 (by rfl) ⟨4454270, by rfl⟩ : syracuseStep 5939027 = 8908541) B8908541
theorem B1646623 : Blo 1646022 1646623 := bstep (se 1 (by rfl) ⟨1234967, by rfl⟩ : syracuseStep 1646623 = 2469935) B2469935
theorem B30056609 : Blo 1646022 30056609 := bstep (se 2 (by rfl) ⟨11271228, by rfl⟩ : syracuseStep 30056609 = 22542457) B22542457
theorem B17801633 : Blo 1646022 17801633 := bstep (se 2 (by rfl) ⟨6675612, by rfl⟩ : syracuseStep 17801633 = 13351225) B13351225
theorem B9765433 : Blo 1646022 9765433 := bstep (se 2 (by rfl) ⟨3662037, by rfl⟩ : syracuseStep 9765433 = 7324075) B7324075
theorem B46318367 : Blo 1646022 46318367 := bstep (se 1 (by rfl) ⟨34738775, by rfl⟩ : syracuseStep 46318367 = 69477551) B69477551
theorem B10019647 : Blo 1646022 10019647 := bstep (se 1 (by rfl) ⟨7514735, by rfl⟩ : syracuseStep 10019647 = 15029471) B15029471
theorem B3704039 : Blo 1646022 3704039 := bstep (se 1 (by rfl) ⟨2778029, by rfl⟩ : syracuseStep 3704039 = 5556059) B5556059
theorem B1647935 : Blo 1646022 1647935 := bstep (se 1 (by rfl) ⟨1235951, by rfl⟩ : syracuseStep 1647935 = 2471903) B2471903
theorem B5555681 : Blo 1646022 5555681 := bstep (se 2 (by rfl) ⟨2083380, by rfl⟩ : syracuseStep 5555681 = 4166761) B4166761
theorem B2778799 : Blo 1646022 2778799 := bstep (se 1 (by rfl) ⟨2084099, by rfl⟩ : syracuseStep 2778799 = 4168199) B4168199
theorem B1853275 : Blo 1646022 1853275 := bstep (se 1 (by rfl) ⟨1389956, by rfl⟩ : syracuseStep 1853275 = 2779913) B2779913
theorem B3704975 : Blo 1646022 3704975 := bstep (se 1 (by rfl) ⟨2778731, by rfl⟩ : syracuseStep 3704975 = 5557463) B5557463
theorem B3705083 : Blo 1646022 3705083 := bstep (se 1 (by rfl) ⟨2778812, by rfl⟩ : syracuseStep 3705083 = 5557625) B5557625
theorem B3705191 : Blo 1646022 3705191 := bstep (se 1 (by rfl) ⟨2778893, by rfl⟩ : syracuseStep 3705191 = 5557787) B5557787
theorem B3959351 : Blo 1646022 3959351 := bstep (se 1 (by rfl) ⟨2969513, by rfl⟩ : syracuseStep 3959351 = 5939027) B5939027
theorem B28142315 : Blo 1646022 28142315 := bstep (se 1 (by rfl) ⟨21106736, by rfl⟩ : syracuseStep 28142315 = 42213473) B42213473
theorem B5557031 : Blo 1646022 5557031 := bstep (se 1 (by rfl) ⟨4167773, by rfl⟩ : syracuseStep 5557031 = 8335547) B8335547
theorem B2968417 : Blo 1646022 2968417 := bstep (se 2 (by rfl) ⟨1113156, by rfl⟩ : syracuseStep 2968417 = 2226313) B2226313
theorem B6253469 : Blo 1646022 6253469 := bstep (se 3 (by rfl) ⟨1172525, by rfl⟩ : syracuseStep 6253469 = 2345051) B2345051
theorem B5557247 : Blo 1646022 5557247 := bstep (se 1 (by rfl) ⟨4167935, by rfl⟩ : syracuseStep 5557247 = 8335871) B8335871
theorem B2469071 : Blo 1646022 2469071 := bstep (se 1 (by rfl) ⟨1851803, by rfl⟩ : syracuseStep 2469071 = 3703607) B3703607
theorem B2469431 : Blo 1646022 2469431 := bstep (se 1 (by rfl) ⟨1852073, by rfl⟩ : syracuseStep 2469431 = 3704147) B3704147
theorem B12504779 : Blo 1646022 12504779 := bstep (se 1 (by rfl) ⟨9378584, by rfl⟩ : syracuseStep 12504779 = 18757169) B18757169
theorem B8450081 : Blo 1646022 8450081 := bstep (se 2 (by rfl) ⟨3168780, by rfl⟩ : syracuseStep 8450081 = 6337561) B6337561
theorem B3706991 : Blo 1646022 3706991 := bstep (se 1 (by rfl) ⟨2780243, by rfl⟩ : syracuseStep 3706991 = 5560487) B5560487
theorem B6254759 : Blo 1646022 6254759 := bstep (se 1 (by rfl) ⟨4691069, by rfl⟩ : syracuseStep 6254759 = 9382139) B9382139
theorem B23752925 : Blo 1646022 23752925 := bstep (se 3 (by rfl) ⟨4453673, by rfl⟩ : syracuseStep 23752925 = 8907347) B8907347
theorem B2470223 : Blo 1646022 2470223 := bstep (se 1 (by rfl) ⟨1852667, by rfl⟩ : syracuseStep 2470223 = 3705335) B3705335
theorem B6254927 : Blo 1646022 6254927 := bstep (se 1 (by rfl) ⟨4691195, by rfl⟩ : syracuseStep 6254927 = 9382391) B9382391
theorem B27087635 : Blo 1646022 27087635 := bstep (se 1 (by rfl) ⟨20315726, by rfl⟩ : syracuseStep 27087635 = 40631453) B40631453
theorem B45069149 : Blo 1646022 45069149 := bstep (se 3 (by rfl) ⟨8450465, by rfl⟩ : syracuseStep 45069149 = 16900931) B16900931
theorem B6681533 : Blo 1646022 6681533 := bstep (se 3 (by rfl) ⟨1252787, by rfl⟩ : syracuseStep 6681533 = 2505575) B2505575
theorem B2471135 : Blo 1646022 2471135 := bstep (se 1 (by rfl) ⟨1853351, by rfl⟩ : syracuseStep 2471135 = 3706703) B3706703
theorem B3126575 : Blo 1646022 3126575 := bstep (se 1 (by rfl) ⟨2344931, by rfl⟩ : syracuseStep 3126575 = 4689863) B4689863
theorem B21116375 : Blo 1646022 21116375 := bstep (se 1 (by rfl) ⟨15837281, by rfl⟩ : syracuseStep 21116375 = 31674563) B31674563
theorem B5559839 : Blo 1646022 5559839 := bstep (se 1 (by rfl) ⟨4169879, by rfl⟩ : syracuseStep 5559839 = 8339759) B8339759
theorem B2471531 : Blo 1646022 2471531 := bstep (se 1 (by rfl) ⟨1853648, by rfl⟩ : syracuseStep 2471531 = 3707297) B3707297
theorem B2471615 : Blo 1646022 2471615 := bstep (se 1 (by rfl) ⟨1853711, by rfl⟩ : syracuseStep 2471615 = 3707423) B3707423
theorem B9385739 : Blo 1646022 9385739 := bstep (se 1 (by rfl) ⟨7039304, by rfl⟩ : syracuseStep 9385739 = 14078609) B14078609
theorem B26712179 : Blo 1646022 26712179 := bstep (se 1 (by rfl) ⟨20034134, by rfl⟩ : syracuseStep 26712179 = 40068269) B40068269
theorem B13359275 : Blo 1646022 13359275 := bstep (se 1 (by rfl) ⟨10019456, by rfl⟩ : syracuseStep 13359275 = 20038913) B20038913
theorem B3955015 : Blo 1646022 3955015 := bstep (se 1 (by rfl) ⟨2966261, by rfl⟩ : syracuseStep 3955015 = 5932523) B5932523
theorem B23746925 : Blo 1646022 23746925 := bstep (se 3 (by rfl) ⟨4452548, by rfl⟩ : syracuseStep 23746925 = 8905097) B8905097
theorem B3127835 : Blo 1646022 3127835 := bstep (se 1 (by rfl) ⟨2345876, by rfl⟩ : syracuseStep 3127835 = 4691753) B4691753
theorem B11869199 : Blo 1646022 11869199 := bstep (se 1 (by rfl) ⟨8901899, by rfl⟩ : syracuseStep 11869199 = 17803799) B17803799
theorem B3955823 : Blo 1646022 3955823 := bstep (se 1 (by rfl) ⟨2966867, by rfl⟩ : syracuseStep 3955823 = 5933735) B5933735
theorem B14064839 : Blo 1646022 14064839 := bstep (se 1 (by rfl) ⟨10548629, by rfl⟩ : syracuseStep 14064839 = 21097259) B21097259
theorem B5561567 : Blo 1646022 5561567 := bstep (se 1 (by rfl) ⟨4171175, by rfl⟩ : syracuseStep 5561567 = 8342351) B8342351
theorem B6339911 : Blo 1646022 6339911 := bstep (se 1 (by rfl) ⟨4754933, by rfl⟩ : syracuseStep 6339911 = 9509867) B9509867
theorem B26705375 : Blo 1646022 26705375 := bstep (se 1 (by rfl) ⟨20029031, by rfl⟩ : syracuseStep 26705375 = 40058063) B40058063
theorem B1646079 : Blo 1646022 1646079 := bstep (se 1 (by rfl) ⟨1234559, by rfl⟩ : syracuseStep 1646079 = 2469119) B2469119
theorem B18767375 : Blo 1646022 18767375 := bstep (se 1 (by rfl) ⟨14075531, by rfl⟩ : syracuseStep 18767375 = 28151063) B28151063
theorem B41746049 : Blo 1646022 41746049 := bstep (se 2 (by rfl) ⟨15654768, by rfl⟩ : syracuseStep 41746049 = 31309537) B31309537
theorem B15023819 : Blo 1646022 15023819 := bstep (se 1 (by rfl) ⟨11267864, by rfl⟩ : syracuseStep 15023819 = 22535729) B22535729
theorem B1646319 : Blo 1646022 1646319 := bstep (se 1 (by rfl) ⟨1234739, by rfl⟩ : syracuseStep 1646319 = 2469479) B2469479
theorem B1646427 : Blo 1646022 1646427 := bstep (se 1 (by rfl) ⟨1234820, by rfl⟩ : syracuseStep 1646427 = 2469641) B2469641
theorem B47464325 : Blo 1646022 47464325 := bstep (se 4 (by rfl) ⟨4449780, by rfl⟩ : syracuseStep 47464325 = 8899561) B8899561
theorem B1646575 : Blo 1646022 1646575 := bstep (se 1 (by rfl) ⟨1234931, by rfl⟩ : syracuseStep 1646575 = 2469863) B2469863
theorem B20037739 : Blo 1646022 20037739 := bstep (se 1 (by rfl) ⟨15028304, by rfl⟩ : syracuseStep 20037739 = 30056609) B30056609
theorem B4169839 : Blo 1646022 4169839 := bstep (se 1 (by rfl) ⟨3127379, by rfl⟩ : syracuseStep 4169839 = 6254759) B6254759
theorem B15835283 : Blo 1646022 15835283 := bstep (se 1 (by rfl) ⟨11876462, by rfl⟩ : syracuseStep 15835283 = 23752925) B23752925
theorem B1646815 : Blo 1646022 1646815 := bstep (se 1 (by rfl) ⟨1235111, by rfl⟩ : syracuseStep 1646815 = 2470223) B2470223
theorem B4169951 : Blo 1646022 4169951 := bstep (se 1 (by rfl) ⟨3127463, by rfl⟩ : syracuseStep 4169951 = 6254927) B6254927
theorem B1647423 : Blo 1646022 1647423 := bstep (se 1 (by rfl) ⟨1235567, by rfl⟩ : syracuseStep 1647423 = 2471135) B2471135
theorem B3703787 : Blo 1646022 3703787 := bstep (se 1 (by rfl) ⟨2777840, by rfl⟩ : syracuseStep 3703787 = 5555681) B5555681
theorem B1647687 : Blo 1646022 1647687 := bstep (se 1 (by rfl) ⟨1235765, by rfl⟩ : syracuseStep 1647687 = 2471531) B2471531
theorem B1647743 : Blo 1646022 1647743 := bstep (se 1 (by rfl) ⟨1235807, by rfl⟩ : syracuseStep 1647743 = 2471615) B2471615
theorem B8340893 : Blo 1646022 8340893 := bstep (se 3 (by rfl) ⟨1563917, by rfl⟩ : syracuseStep 8340893 = 3127835) B3127835
theorem B8906183 : Blo 1646022 8906183 := bstep (se 1 (by rfl) ⟨6679637, by rfl⟩ : syracuseStep 8906183 = 13359275) B13359275
theorem B2639567 : Blo 1646022 2639567 := bstep (se 1 (by rfl) ⟨1979675, by rfl⟩ : syracuseStep 2639567 = 3959351) B3959351
theorem B18761543 : Blo 1646022 18761543 := bstep (se 1 (by rfl) ⟨14071157, by rfl⟩ : syracuseStep 18761543 = 28142315) B28142315
theorem B3704687 : Blo 1646022 3704687 := bstep (se 1 (by rfl) ⟨2778515, by rfl⟩ : syracuseStep 3704687 = 5557031) B5557031
theorem B3704831 : Blo 1646022 3704831 := bstep (se 1 (by rfl) ⟨2778623, by rfl⟩ : syracuseStep 3704831 = 5557247) B5557247
theorem B3705065 : Blo 1646022 3705065 := bstep (se 2 (by rfl) ⟨1389399, by rfl⟩ : syracuseStep 3705065 = 2778799) B2778799
theorem B17803583 : Blo 1646022 17803583 := bstep (se 1 (by rfl) ⟨13352687, by rfl⟩ : syracuseStep 17803583 = 26705375) B26705375
theorem B12511583 : Blo 1646022 12511583 := bstep (se 1 (by rfl) ⟨9383687, by rfl⟩ : syracuseStep 12511583 = 18767375) B18767375
theorem B27830699 : Blo 1646022 27830699 := bstep (se 1 (by rfl) ⟨20873024, by rfl⟩ : syracuseStep 27830699 = 41746049) B41746049
theorem B30878911 : Blo 1646022 30878911 := bstep (se 1 (by rfl) ⟨23159183, by rfl⟩ : syracuseStep 30878911 = 46318367) B46318367
theorem B13020577 : Blo 1646022 13020577 := bstep (se 2 (by rfl) ⟨4882716, by rfl⟩ : syracuseStep 13020577 = 9765433) B9765433
theorem B2469359 : Blo 1646022 2469359 := bstep (se 1 (by rfl) ⟨1852019, by rfl⟩ : syracuseStep 2469359 = 3704039) B3704039
theorem B2084383 : Blo 1646022 2084383 := bstep (se 1 (by rfl) ⟨1563287, by rfl⟩ : syracuseStep 2084383 = 3126575) B3126575
theorem B14077583 : Blo 1646022 14077583 := bstep (se 1 (by rfl) ⟨10558187, by rfl⟩ : syracuseStep 14077583 = 21116375) B21116375
theorem B3706559 : Blo 1646022 3706559 := bstep (se 1 (by rfl) ⟨2779919, by rfl⟩ : syracuseStep 3706559 = 5559839) B5559839
theorem B2469983 : Blo 1646022 2469983 := bstep (se 1 (by rfl) ⟨1852487, by rfl⟩ : syracuseStep 2469983 = 3704975) B3704975
theorem B2470055 : Blo 1646022 2470055 := bstep (se 1 (by rfl) ⟨1852541, by rfl⟩ : syracuseStep 2470055 = 3705083) B3705083
theorem B2470127 : Blo 1646022 2470127 := bstep (se 1 (by rfl) ⟨1852595, by rfl⟩ : syracuseStep 2470127 = 3705191) B3705191
theorem B15831283 : Blo 1646022 15831283 := bstep (se 1 (by rfl) ⟨11873462, by rfl⟩ : syracuseStep 15831283 = 23746925) B23746925
theorem B15831557 : Blo 1646022 15831557 := bstep (se 4 (by rfl) ⟨1484208, by rfl⟩ : syracuseStep 15831557 = 2968417) B2968417
theorem B40063517 : Blo 1646022 40063517 := bstep (se 3 (by rfl) ⟨7511909, by rfl⟩ : syracuseStep 40063517 = 15023819) B15023819
theorem B72233693 : Blo 1646022 72233693 := bstep (se 3 (by rfl) ⟨13543817, by rfl⟩ : syracuseStep 72233693 = 27087635) B27087635
theorem B9376559 : Blo 1646022 9376559 := bstep (se 1 (by rfl) ⟨7032419, by rfl⟩ : syracuseStep 9376559 = 14064839) B14064839
theorem B3707711 : Blo 1646022 3707711 := bstep (se 1 (by rfl) ⟨2780783, by rfl⟩ : syracuseStep 3707711 = 5561567) B5561567
theorem B2471033 : Blo 1646022 2471033 := bstep (se 2 (by rfl) ⟨926637, by rfl⟩ : syracuseStep 2471033 = 1853275) B1853275
theorem B8336519 : Blo 1646022 8336519 := bstep (se 1 (by rfl) ⟨6252389, by rfl⟩ : syracuseStep 8336519 = 12504779) B12504779
theorem B31642883 : Blo 1646022 31642883 := bstep (se 1 (by rfl) ⟨23732162, by rfl⟩ : syracuseStep 31642883 = 47464325) B47464325
theorem B5633387 : Blo 1646022 5633387 := bstep (se 1 (by rfl) ⟨4225040, by rfl⟩ : syracuseStep 5633387 = 8450081) B8450081
theorem B2471327 : Blo 1646022 2471327 := bstep (se 1 (by rfl) ⟨1853495, by rfl⟩ : syracuseStep 2471327 = 3706991) B3706991
theorem B5273353 : Blo 1646022 5273353 := bstep (se 2 (by rfl) ⟨1977507, by rfl⟩ : syracuseStep 5273353 = 3955015) B3955015
theorem B16906429 : Blo 1646022 16906429 := bstep (se 3 (by rfl) ⟨3169955, by rfl⟩ : syracuseStep 16906429 = 6339911) B6339911
theorem B13359529 : Blo 1646022 13359529 := bstep (se 2 (by rfl) ⟨5009823, by rfl⟩ : syracuseStep 13359529 = 10019647) B10019647
theorem B47471021 : Blo 1646022 47471021 := bstep (se 3 (by rfl) ⟨8900816, by rfl⟩ : syracuseStep 47471021 = 17801633) B17801633
theorem B6257159 : Blo 1646022 6257159 := bstep (se 1 (by rfl) ⟨4692869, by rfl⟩ : syracuseStep 6257159 = 9385739) B9385739
theorem B17808119 : Blo 1646022 17808119 := bstep (se 1 (by rfl) ⟨13356089, by rfl⟩ : syracuseStep 17808119 = 26712179) B26712179
theorem B4168979 : Blo 1646022 4168979 := bstep (se 1 (by rfl) ⟨3126734, by rfl⟩ : syracuseStep 4168979 = 6253469) B6253469
theorem B7912799 : Blo 1646022 7912799 := bstep (se 1 (by rfl) ⟨5934599, by rfl⟩ : syracuseStep 7912799 = 11869199) B11869199
theorem B2637215 : Blo 1646022 2637215 := bstep (se 1 (by rfl) ⟨1977911, by rfl⟩ : syracuseStep 2637215 = 3955823) B3955823
theorem B1646047 : Blo 1646022 1646047 := bstep (se 1 (by rfl) ⟨1234535, by rfl⟩ : syracuseStep 1646047 = 2469071) B2469071
theorem B120184397 : Blo 1646022 120184397 := bstep (se 3 (by rfl) ⟨22534574, by rfl⟩ : syracuseStep 120184397 = 45069149) B45069149
theorem B1646287 : Blo 1646022 1646287 := bstep (se 1 (by rfl) ⟨1234715, by rfl⟩ : syracuseStep 1646287 = 2469431) B2469431
theorem B17817421 : Blo 1646022 17817421 := bstep (se 3 (by rfl) ⟨3340766, by rfl⟩ : syracuseStep 17817421 = 6681533) B6681533
theorem B1646655 : Blo 1646022 1646655 := bstep (se 1 (by rfl) ⟨1234991, by rfl⟩ : syracuseStep 1646655 = 2469983) B2469983
theorem B1646703 : Blo 1646022 1646703 := bstep (se 1 (by rfl) ⟨1235027, by rfl⟩ : syracuseStep 1646703 = 2470055) B2470055
theorem B1646751 : Blo 1646022 1646751 := bstep (se 1 (by rfl) ⟨1235063, by rfl⟩ : syracuseStep 1646751 = 2470127) B2470127
theorem B6251039 : Blo 1646022 6251039 := bstep (se 1 (by rfl) ⟨4688279, by rfl⟩ : syracuseStep 6251039 = 9376559) B9376559
theorem B1647355 : Blo 1646022 1647355 := bstep (se 1 (by rfl) ⟨1235516, by rfl⟩ : syracuseStep 1647355 = 2471033) B2471033
theorem B21095255 : Blo 1646022 21095255 := bstep (se 1 (by rfl) ⟨15821441, by rfl⟩ : syracuseStep 21095255 = 31642883) B31642883
theorem B1647551 : Blo 1646022 1647551 := bstep (se 1 (by rfl) ⟨1235663, by rfl⟩ : syracuseStep 1647551 = 2471327) B2471327
theorem B8341055 : Blo 1646022 8341055 := bstep (se 1 (by rfl) ⟨6255791, by rfl⟩ : syracuseStep 8341055 = 12511583) B12511583
theorem B31647347 : Blo 1646022 31647347 := bstep (se 1 (by rfl) ⟨23735510, by rfl⟩ : syracuseStep 31647347 = 47471021) B47471021
theorem B4171439 : Blo 1646022 4171439 := bstep (se 1 (by rfl) ⟨3128579, by rfl⟩ : syracuseStep 4171439 = 6257159) B6257159
theorem B11872079 : Blo 1646022 11872079 := bstep (se 1 (by rfl) ⟨8904059, by rfl⟩ : syracuseStep 11872079 = 17808119) B17808119
theorem B7038845 : Blo 1646022 7038845 := bstep (se 3 (by rfl) ⟨1319783, by rfl⟩ : syracuseStep 7038845 = 2639567) B2639567
theorem B2779177 : Blo 1646022 2779177 := bstep (se 2 (by rfl) ⟨1042191, by rfl⟩ : syracuseStep 2779177 = 2084383) B2084383
theorem B2779319 : Blo 1646022 2779319 := bstep (se 1 (by rfl) ⟨2084489, by rfl⟩ : syracuseStep 2779319 = 4168979) B4168979
theorem B7031137 : Blo 1646022 7031137 := bstep (se 2 (by rfl) ⟨2636676, by rfl⟩ : syracuseStep 7031137 = 5273353) B5273353
theorem B26716985 : Blo 1646022 26716985 := bstep (se 2 (by rfl) ⟨10018869, by rfl⟩ : syracuseStep 26716985 = 20037739) B20037739
theorem B2779967 : Blo 1646022 2779967 := bstep (se 1 (by rfl) ⟨2084975, by rfl⟩ : syracuseStep 2779967 = 4169951) B4169951
theorem B10554371 : Blo 1646022 10554371 := bstep (se 1 (by rfl) ⟨7915778, by rfl⟩ : syracuseStep 10554371 = 15831557) B15831557
theorem B26709011 : Blo 1646022 26709011 := bstep (se 1 (by rfl) ⟨20031758, by rfl⟩ : syracuseStep 26709011 = 40063517) B40063517
theorem B48155795 : Blo 1646022 48155795 := bstep (se 1 (by rfl) ⟨36116846, by rfl⟩ : syracuseStep 48155795 = 72233693) B72233693
theorem B17812705 : Blo 1646022 17812705 := bstep (se 2 (by rfl) ⟨6679764, by rfl⟩ : syracuseStep 17812705 = 13359529) B13359529
theorem B2469191 : Blo 1646022 2469191 := bstep (se 1 (by rfl) ⟨1851893, by rfl⟩ : syracuseStep 2469191 = 3703787) B3703787
theorem B5557679 : Blo 1646022 5557679 := bstep (se 1 (by rfl) ⟨4168259, by rfl⟩ : syracuseStep 5557679 = 8336519) B8336519
theorem B3755591 : Blo 1646022 3755591 := bstep (se 1 (by rfl) ⟨2816693, by rfl⟩ : syracuseStep 3755591 = 5633387) B5633387
theorem B164687525 : Blo 1646022 164687525 := bstep (se 4 (by rfl) ⟨15439455, by rfl⟩ : syracuseStep 164687525 = 30878911) B30878911
theorem B2469791 : Blo 1646022 2469791 := bstep (se 1 (by rfl) ⟨1852343, by rfl⟩ : syracuseStep 2469791 = 3704687) B3704687
theorem B2469887 : Blo 1646022 2469887 := bstep (se 1 (by rfl) ⟨1852415, by rfl⟩ : syracuseStep 2469887 = 3704831) B3704831
theorem B2470043 : Blo 1646022 2470043 := bstep (se 1 (by rfl) ⟨1852532, by rfl⟩ : syracuseStep 2470043 = 3705065) B3705065
theorem B1758143 : Blo 1646022 1758143 := bstep (se 1 (by rfl) ⟨1318607, by rfl⟩ : syracuseStep 1758143 = 2637215) B2637215
theorem B80122931 : Blo 1646022 80122931 := bstep (se 1 (by rfl) ⟨60092198, by rfl⟩ : syracuseStep 80122931 = 120184397) B120184397
theorem B9385055 : Blo 1646022 9385055 := bstep (se 1 (by rfl) ⟨7038791, by rfl⟩ : syracuseStep 9385055 = 14077583) B14077583
theorem B2471039 : Blo 1646022 2471039 := bstep (se 1 (by rfl) ⟨1853279, by rfl⟩ : syracuseStep 2471039 = 3706559) B3706559
theorem B10556855 : Blo 1646022 10556855 := bstep (se 1 (by rfl) ⟨7917641, by rfl⟩ : syracuseStep 10556855 = 15835283) B15835283
theorem B5559785 : Blo 1646022 5559785 := bstep (se 2 (by rfl) ⟨2084919, by rfl⟩ : syracuseStep 5559785 = 4169839) B4169839
theorem B22541905 : Blo 1646022 22541905 := bstep (se 2 (by rfl) ⟨8453214, by rfl⟩ : syracuseStep 22541905 = 16906429) B16906429
theorem B21108377 : Blo 1646022 21108377 := bstep (se 2 (by rfl) ⟨7915641, by rfl⟩ : syracuseStep 21108377 = 15831283) B15831283
theorem B2471807 : Blo 1646022 2471807 := bstep (se 1 (by rfl) ⟨1853855, by rfl⟩ : syracuseStep 2471807 = 3707711) B3707711
theorem B5560595 : Blo 1646022 5560595 := bstep (se 1 (by rfl) ⟨4170446, by rfl⟩ : syracuseStep 5560595 = 8340893) B8340893
theorem B5937455 : Blo 1646022 5937455 := bstep (se 1 (by rfl) ⟨4453091, by rfl⟩ : syracuseStep 5937455 = 8906183) B8906183
theorem B12507695 : Blo 1646022 12507695 := bstep (se 1 (by rfl) ⟨9380771, by rfl⟩ : syracuseStep 12507695 = 18761543) B18761543
theorem B11869055 : Blo 1646022 11869055 := bstep (se 1 (by rfl) ⟨8901791, by rfl⟩ : syracuseStep 11869055 = 17803583) B17803583
theorem B18553799 : Blo 1646022 18553799 := bstep (se 1 (by rfl) ⟨13915349, by rfl⟩ : syracuseStep 18553799 = 27830699) B27830699
theorem B69443077 : Blo 1646022 69443077 := bstep (se 4 (by rfl) ⟨6510288, by rfl⟩ : syracuseStep 69443077 = 13020577) B13020577
theorem B5275199 : Blo 1646022 5275199 := bstep (se 1 (by rfl) ⟨3956399, by rfl⟩ : syracuseStep 5275199 = 7912799) B7912799
theorem B1646239 : Blo 1646022 1646239 := bstep (se 1 (by rfl) ⟨1234679, by rfl⟩ : syracuseStep 1646239 = 2469359) B2469359
theorem B23756561 : Blo 1646022 23756561 := bstep (se 2 (by rfl) ⟨8908710, by rfl⟩ : syracuseStep 23756561 = 17817421) B17817421
theorem B1646695 : Blo 1646022 1646695 := bstep (se 1 (by rfl) ⟨1235021, by rfl⟩ : syracuseStep 1646695 = 2470043) B2470043
theorem B1647359 : Blo 1646022 1647359 := bstep (se 1 (by rfl) ⟨1235519, by rfl⟩ : syracuseStep 1647359 = 2471039) B2471039
theorem B7037903 : Blo 1646022 7037903 := bstep (se 1 (by rfl) ⟨5278427, by rfl⟩ : syracuseStep 7037903 = 10556855) B10556855
theorem B7914719 : Blo 1646022 7914719 := bstep (se 1 (by rfl) ⟨5936039, by rfl⟩ : syracuseStep 7914719 = 11872079) B11872079
theorem B1647871 : Blo 1646022 1647871 := bstep (se 1 (by rfl) ⟨1235903, by rfl⟩ : syracuseStep 1647871 = 2471807) B2471807
theorem B1852879 : Blo 1646022 1852879 := bstep (se 1 (by rfl) ⟨1389659, by rfl⟩ : syracuseStep 1852879 = 2779319) B2779319
theorem B3958303 : Blo 1646022 3958303 := bstep (se 1 (by rfl) ⟨2968727, by rfl⟩ : syracuseStep 3958303 = 5937455) B5937455
theorem B23750273 : Blo 1646022 23750273 := bstep (se 2 (by rfl) ⟨8906352, by rfl⟩ : syracuseStep 23750273 = 17812705) B17812705
theorem B17811323 : Blo 1646022 17811323 := bstep (se 1 (by rfl) ⟨13358492, by rfl⟩ : syracuseStep 17811323 = 26716985) B26716985
theorem B1853311 : Blo 1646022 1853311 := bstep (se 1 (by rfl) ⟨1389983, by rfl⟩ : syracuseStep 1853311 = 2779967) B2779967
theorem B3705119 : Blo 1646022 3705119 := bstep (se 1 (by rfl) ⟨2778839, by rfl⟩ : syracuseStep 3705119 = 5557679) B5557679
theorem B3516799 : Blo 1646022 3516799 := bstep (se 1 (by rfl) ⟨2637599, by rfl⟩ : syracuseStep 3516799 = 5275199) B5275199
theorem B109791683 : Blo 1646022 109791683 := bstep (se 1 (by rfl) ⟨82343762, by rfl⟩ : syracuseStep 109791683 = 164687525) B164687525
theorem B4688381 : Blo 1646022 4688381 := bstep (se 3 (by rfl) ⟨879071, by rfl⟩ : syracuseStep 4688381 = 1758143) B1758143
theorem B15837707 : Blo 1646022 15837707 := bstep (se 1 (by rfl) ⟨11878280, by rfl⟩ : syracuseStep 15837707 = 23756561) B23756561
theorem B3705569 : Blo 1646022 3705569 := bstep (se 2 (by rfl) ⟨1389588, by rfl⟩ : syracuseStep 3705569 = 2779177) B2779177
theorem B9374849 : Blo 1646022 9374849 := bstep (se 2 (by rfl) ⟨3515568, by rfl⟩ : syracuseStep 9374849 = 7031137) B7031137
theorem B53415287 : Blo 1646022 53415287 := bstep (se 1 (by rfl) ⟨40061465, by rfl⟩ : syracuseStep 53415287 = 80122931) B80122931
theorem B3706523 : Blo 1646022 3706523 := bstep (se 1 (by rfl) ⟨2779892, by rfl⟩ : syracuseStep 3706523 = 5559785) B5559785
theorem B21098231 : Blo 1646022 21098231 := bstep (se 1 (by rfl) ⟨15823673, by rfl⟩ : syracuseStep 21098231 = 31647347) B31647347
theorem B2780959 : Blo 1646022 2780959 := bstep (se 1 (by rfl) ⟨2085719, by rfl⟩ : syracuseStep 2780959 = 4171439) B4171439
theorem B3707063 : Blo 1646022 3707063 := bstep (se 1 (by rfl) ⟨2780297, by rfl⟩ : syracuseStep 3707063 = 5560595) B5560595
theorem B92590769 : Blo 1646022 92590769 := bstep (se 2 (by rfl) ⟨34721538, by rfl⟩ : syracuseStep 92590769 = 69443077) B69443077
theorem B17806007 : Blo 1646022 17806007 := bstep (se 1 (by rfl) ⟨13354505, by rfl⟩ : syracuseStep 17806007 = 26709011) B26709011
theorem B2503727 : Blo 1646022 2503727 := bstep (se 1 (by rfl) ⟨1877795, by rfl⟩ : syracuseStep 2503727 = 3755591) B3755591
theorem B4167359 : Blo 1646022 4167359 := bstep (se 1 (by rfl) ⟨3125519, by rfl⟩ : syracuseStep 4167359 = 6251039) B6251039
theorem B14063503 : Blo 1646022 14063503 := bstep (se 1 (by rfl) ⟨10547627, by rfl⟩ : syracuseStep 14063503 = 21095255) B21095255
theorem B6256703 : Blo 1646022 6256703 := bstep (se 1 (by rfl) ⟨4692527, by rfl⟩ : syracuseStep 6256703 = 9385055) B9385055
theorem B5560703 : Blo 1646022 5560703 := bstep (se 1 (by rfl) ⟨4170527, by rfl⟩ : syracuseStep 5560703 = 8341055) B8341055
theorem B14072251 : Blo 1646022 14072251 := bstep (se 1 (by rfl) ⟨10554188, by rfl⟩ : syracuseStep 14072251 = 21108377) B21108377
theorem B4692563 : Blo 1646022 4692563 := bstep (se 1 (by rfl) ⟨3519422, by rfl⟩ : syracuseStep 4692563 = 7038845) B7038845
theorem B8338463 : Blo 1646022 8338463 := bstep (se 1 (by rfl) ⟨6253847, by rfl⟩ : syracuseStep 8338463 = 12507695) B12507695
theorem B7912703 : Blo 1646022 7912703 := bstep (se 1 (by rfl) ⟨5934527, by rfl⟩ : syracuseStep 7912703 = 11869055) B11869055
theorem B12369199 : Blo 1646022 12369199 := bstep (se 1 (by rfl) ⟨9276899, by rfl⟩ : syracuseStep 12369199 = 18553799) B18553799
theorem B7036247 : Blo 1646022 7036247 := bstep (se 1 (by rfl) ⟨5277185, by rfl⟩ : syracuseStep 7036247 = 10554371) B10554371
theorem B32103863 : Blo 1646022 32103863 := bstep (se 1 (by rfl) ⟨24077897, by rfl⟩ : syracuseStep 32103863 = 48155795) B48155795
theorem B30055873 : Blo 1646022 30055873 := bstep (se 2 (by rfl) ⟨11270952, by rfl⟩ : syracuseStep 30055873 = 22541905) B22541905
theorem B1646127 : Blo 1646022 1646127 := bstep (se 1 (by rfl) ⟨1234595, by rfl⟩ : syracuseStep 1646127 = 2469191) B2469191
theorem B1646527 : Blo 1646022 1646527 := bstep (se 1 (by rfl) ⟨1234895, by rfl⟩ : syracuseStep 1646527 = 2469791) B2469791
theorem B1646591 : Blo 1646022 1646591 := bstep (se 1 (by rfl) ⟨1234943, by rfl⟩ : syracuseStep 1646591 = 2469887) B2469887
theorem B61727179 : Blo 1646022 61727179 := bstep (se 1 (by rfl) ⟨46295384, by rfl⟩ : syracuseStep 61727179 = 92590769) B92590769
theorem B11870671 : Blo 1646022 11870671 := bstep (se 1 (by rfl) ⟨8903003, by rfl⟩ : syracuseStep 11870671 = 17806007) B17806007
theorem B2778239 : Blo 1646022 2778239 := bstep (se 1 (by rfl) ⟨2083679, by rfl⟩ : syracuseStep 2778239 = 4167359) B4167359
theorem B12502349 : Blo 1646022 12502349 := bstep (se 3 (by rfl) ⟨2344190, by rfl⟩ : syracuseStep 12502349 = 4688381) B4688381
theorem B4171135 : Blo 1646022 4171135 := bstep (se 1 (by rfl) ⟨3128351, by rfl⟩ : syracuseStep 4171135 = 6256703) B6256703
theorem B16492265 : Blo 1646022 16492265 := bstep (se 2 (by rfl) ⟨6184599, by rfl⟩ : syracuseStep 16492265 = 12369199) B12369199
theorem B5277737 : Blo 1646022 5277737 := bstep (se 2 (by rfl) ⟨1979151, by rfl⟩ : syracuseStep 5277737 = 3958303) B3958303
theorem B4689065 : Blo 1646022 4689065 := bstep (se 2 (by rfl) ⟨1758399, by rfl⟩ : syracuseStep 4689065 = 3516799) B3516799
theorem B18763001 : Blo 1646022 18763001 := bstep (se 2 (by rfl) ⟨7036125, by rfl⟩ : syracuseStep 18763001 = 14072251) B14072251
theorem B21105917 : Blo 1646022 21105917 := bstep (se 3 (by rfl) ⟨3957359, by rfl⟩ : syracuseStep 21105917 = 7914719) B7914719
theorem B11874215 : Blo 1646022 11874215 := bstep (se 1 (by rfl) ⟨8905661, by rfl⟩ : syracuseStep 11874215 = 17811323) B17811323
theorem B2470079 : Blo 1646022 2470079 := bstep (se 1 (by rfl) ⟨1852559, by rfl⟩ : syracuseStep 2470079 = 3705119) B3705119
theorem B3707135 : Blo 1646022 3707135 := bstep (se 1 (by rfl) ⟨2780351, by rfl⟩ : syracuseStep 3707135 = 5560703) B5560703
theorem B2470379 : Blo 1646022 2470379 := bstep (se 1 (by rfl) ⟨1852784, by rfl⟩ : syracuseStep 2470379 = 3705569) B3705569
theorem B2470505 : Blo 1646022 2470505 := bstep (se 2 (by rfl) ⟨926439, by rfl⟩ : syracuseStep 2470505 = 1852879) B1852879
theorem B5558975 : Blo 1646022 5558975 := bstep (se 1 (by rfl) ⟨4169231, by rfl⟩ : syracuseStep 5558975 = 8338463) B8338463
theorem B4690831 : Blo 1646022 4690831 := bstep (se 1 (by rfl) ⟨3518123, by rfl⟩ : syracuseStep 4690831 = 7036247) B7036247
theorem B21402575 : Blo 1646022 21402575 := bstep (se 1 (by rfl) ⟨16051931, by rfl⟩ : syracuseStep 21402575 = 32103863) B32103863
theorem B3707945 : Blo 1646022 3707945 := bstep (se 2 (by rfl) ⟨1390479, by rfl⟩ : syracuseStep 3707945 = 2780959) B2780959
theorem B2471015 : Blo 1646022 2471015 := bstep (se 1 (by rfl) ⟨1853261, by rfl⟩ : syracuseStep 2471015 = 3706523) B3706523
theorem B2471081 : Blo 1646022 2471081 := bstep (se 2 (by rfl) ⟨926655, by rfl⟩ : syracuseStep 2471081 = 1853311) B1853311
theorem B2471375 : Blo 1646022 2471375 := bstep (se 1 (by rfl) ⟨1853531, by rfl⟩ : syracuseStep 2471375 = 3707063) B3707063
theorem B4691935 : Blo 1646022 4691935 := bstep (se 1 (by rfl) ⟨3518951, by rfl⟩ : syracuseStep 4691935 = 7037903) B7037903
theorem B1669151 : Blo 1646022 1669151 := bstep (se 1 (by rfl) ⟨1251863, by rfl⟩ : syracuseStep 1669151 = 2503727) B2503727
theorem B15833515 : Blo 1646022 15833515 := bstep (se 1 (by rfl) ⟨11875136, by rfl⟩ : syracuseStep 15833515 = 23750273) B23750273
theorem B73194455 : Blo 1646022 73194455 := bstep (se 1 (by rfl) ⟨54895841, by rfl⟩ : syracuseStep 73194455 = 109791683) B109791683
theorem B10558471 : Blo 1646022 10558471 := bstep (se 1 (by rfl) ⟨7918853, by rfl⟩ : syracuseStep 10558471 = 15837707) B15837707
theorem B3128375 : Blo 1646022 3128375 := bstep (se 1 (by rfl) ⟨2346281, by rfl⟩ : syracuseStep 3128375 = 4692563) B4692563
theorem B40074497 : Blo 1646022 40074497 := bstep (se 2 (by rfl) ⟨15027936, by rfl⟩ : syracuseStep 40074497 = 30055873) B30055873
theorem B6249899 : Blo 1646022 6249899 := bstep (se 1 (by rfl) ⟨4687424, by rfl⟩ : syracuseStep 6249899 = 9374849) B9374849
theorem B5275135 : Blo 1646022 5275135 := bstep (se 1 (by rfl) ⟨3956351, by rfl⟩ : syracuseStep 5275135 = 7912703) B7912703
theorem B35610191 : Blo 1646022 35610191 := bstep (se 1 (by rfl) ⟨26707643, by rfl⟩ : syracuseStep 35610191 = 53415287) B53415287
theorem B14065487 : Blo 1646022 14065487 := bstep (se 1 (by rfl) ⟨10549115, by rfl⟩ : syracuseStep 14065487 = 21098231) B21098231
theorem B18751337 : Blo 1646022 18751337 := bstep (se 2 (by rfl) ⟨7031751, by rfl⟩ : syracuseStep 18751337 = 14063503) B14063503
theorem B1646719 : Blo 1646022 1646719 := bstep (se 1 (by rfl) ⟨1235039, by rfl⟩ : syracuseStep 1646719 = 2470079) B2470079
theorem B1646919 : Blo 1646022 1646919 := bstep (se 1 (by rfl) ⟨1235189, by rfl⟩ : syracuseStep 1646919 = 2470379) B2470379
theorem B1647003 : Blo 1646022 1647003 := bstep (se 1 (by rfl) ⟨1235252, by rfl⟩ : syracuseStep 1647003 = 2470505) B2470505
theorem B21111353 : Blo 1646022 21111353 := bstep (se 2 (by rfl) ⟨7916757, by rfl⟩ : syracuseStep 21111353 = 15833515) B15833515
theorem B15827561 : Blo 1646022 15827561 := bstep (se 2 (by rfl) ⟨5935335, by rfl⟩ : syracuseStep 15827561 = 11870671) B11870671
theorem B1647343 : Blo 1646022 1647343 := bstep (se 1 (by rfl) ⟨1235507, by rfl⟩ : syracuseStep 1647343 = 2471015) B2471015
theorem B1852159 : Blo 1646022 1852159 := bstep (se 1 (by rfl) ⟨1389119, by rfl⟩ : syracuseStep 1852159 = 2778239) B2778239
theorem B1647387 : Blo 1646022 1647387 := bstep (se 1 (by rfl) ⟨1235540, by rfl⟩ : syracuseStep 1647387 = 2471081) B2471081
theorem B1647583 : Blo 1646022 1647583 := bstep (se 1 (by rfl) ⟨1235687, by rfl⟩ : syracuseStep 1647583 = 2471375) B2471375
theorem B26716331 : Blo 1646022 26716331 := bstep (se 1 (by rfl) ⟨20037248, by rfl⟩ : syracuseStep 26716331 = 40074497) B40074497
theorem B175917493 : Blo 1646022 175917493 := bstep (se 5 (by rfl) ⟨8246132, by rfl⟩ : syracuseStep 175917493 = 16492265) B16492265
theorem B7916143 : Blo 1646022 7916143 := bstep (se 1 (by rfl) ⟨5937107, by rfl⟩ : syracuseStep 7916143 = 11874215) B11874215
theorem B4451069 : Blo 1646022 4451069 := bstep (se 3 (by rfl) ⟨834575, by rfl⟩ : syracuseStep 4451069 = 1669151) B1669151
theorem B3705983 : Blo 1646022 3705983 := bstep (se 1 (by rfl) ⟨2779487, by rfl⟩ : syracuseStep 3705983 = 5558975) B5558975
theorem B8334899 : Blo 1646022 8334899 := bstep (se 1 (by rfl) ⟨6251174, by rfl⟩ : syracuseStep 8334899 = 12502349) B12502349
theorem B6254441 : Blo 1646022 6254441 := bstep (se 2 (by rfl) ⟨2345415, by rfl⟩ : syracuseStep 6254441 = 4690831) B4690831
theorem B14077961 : Blo 1646022 14077961 := bstep (se 2 (by rfl) ⟨5279235, by rfl⟩ : syracuseStep 14077961 = 10558471) B10558471
theorem B3518491 : Blo 1646022 3518491 := bstep (se 1 (by rfl) ⟨2638868, by rfl⟩ : syracuseStep 3518491 = 5277737) B5277737
theorem B48796303 : Blo 1646022 48796303 := bstep (se 1 (by rfl) ⟨36597227, by rfl⟩ : syracuseStep 48796303 = 73194455) B73194455
theorem B7033513 : Blo 1646022 7033513 := bstep (se 2 (by rfl) ⟨2637567, by rfl⟩ : syracuseStep 7033513 = 5275135) B5275135
theorem B2085583 : Blo 1646022 2085583 := bstep (se 1 (by rfl) ⟨1564187, by rfl⟩ : syracuseStep 2085583 = 3128375) B3128375
theorem B3126043 : Blo 1646022 3126043 := bstep (se 1 (by rfl) ⟨2344532, by rfl⟩ : syracuseStep 3126043 = 4689065) B4689065
theorem B14070611 : Blo 1646022 14070611 := bstep (se 1 (by rfl) ⟨10552958, by rfl⟩ : syracuseStep 14070611 = 21105917) B21105917
theorem B4166599 : Blo 1646022 4166599 := bstep (se 1 (by rfl) ⟨3124949, by rfl⟩ : syracuseStep 4166599 = 6249899) B6249899
theorem B9376991 : Blo 1646022 9376991 := bstep (se 1 (by rfl) ⟨7032743, by rfl⟩ : syracuseStep 9376991 = 14065487) B14065487
theorem B6255913 : Blo 1646022 6255913 := bstep (se 2 (by rfl) ⟨2345967, by rfl⟩ : syracuseStep 6255913 = 4691935) B4691935
theorem B2471423 : Blo 1646022 2471423 := bstep (se 1 (by rfl) ⟨1853567, by rfl⟩ : syracuseStep 2471423 = 3707135) B3707135
theorem B82302905 : Blo 1646022 82302905 := bstep (se 2 (by rfl) ⟨30863589, by rfl⟩ : syracuseStep 82302905 = 61727179) B61727179
theorem B14268383 : Blo 1646022 14268383 := bstep (se 1 (by rfl) ⟨10701287, by rfl⟩ : syracuseStep 14268383 = 21402575) B21402575
theorem B2471963 : Blo 1646022 2471963 := bstep (se 1 (by rfl) ⟨1853972, by rfl⟩ : syracuseStep 2471963 = 3707945) B3707945
theorem B5561513 : Blo 1646022 5561513 := bstep (se 2 (by rfl) ⟨2085567, by rfl⟩ : syracuseStep 5561513 = 4171135) B4171135
theorem B12508667 : Blo 1646022 12508667 := bstep (se 1 (by rfl) ⟨9381500, by rfl⟩ : syracuseStep 12508667 = 18763001) B18763001
theorem B23740127 : Blo 1646022 23740127 := bstep (se 1 (by rfl) ⟨17805095, by rfl⟩ : syracuseStep 23740127 = 35610191) B35610191
theorem B12500891 : Blo 1646022 12500891 := bstep (se 1 (by rfl) ⟨9375668, by rfl⟩ : syracuseStep 12500891 = 18751337) B18751337
theorem B14074235 : Blo 1646022 14074235 := bstep (se 1 (by rfl) ⟨10555676, by rfl⟩ : syracuseStep 14074235 = 21111353) B21111353
theorem B10551707 : Blo 1646022 10551707 := bstep (se 1 (by rfl) ⟨7913780, by rfl⟩ : syracuseStep 10551707 = 15827561) B15827561
theorem B9380407 : Blo 1646022 9380407 := bstep (se 1 (by rfl) ⟨7035305, by rfl⟩ : syracuseStep 9380407 = 14070611) B14070611
theorem B6251327 : Blo 1646022 6251327 := bstep (se 1 (by rfl) ⟨4688495, by rfl⟩ : syracuseStep 6251327 = 9376991) B9376991
theorem B65061737 : Blo 1646022 65061737 := bstep (se 2 (by rfl) ⟨24398151, by rfl⟩ : syracuseStep 65061737 = 48796303) B48796303
theorem B1647615 : Blo 1646022 1647615 := bstep (se 1 (by rfl) ⟨1235711, by rfl⟩ : syracuseStep 1647615 = 2471423) B2471423
theorem B5555465 : Blo 1646022 5555465 := bstep (se 2 (by rfl) ⟨2083299, by rfl⟩ : syracuseStep 5555465 = 4166599) B4166599
theorem B9512255 : Blo 1646022 9512255 := bstep (se 1 (by rfl) ⟨7134191, by rfl⟩ : syracuseStep 9512255 = 14268383) B14268383
theorem B1647975 : Blo 1646022 1647975 := bstep (se 1 (by rfl) ⟨1235981, by rfl⟩ : syracuseStep 1647975 = 2471963) B2471963
theorem B17810887 : Blo 1646022 17810887 := bstep (se 1 (by rfl) ⟨13358165, by rfl⟩ : syracuseStep 17810887 = 26716331) B26716331
theorem B8341217 : Blo 1646022 8341217 := bstep (se 2 (by rfl) ⟨3127956, by rfl⟩ : syracuseStep 8341217 = 6255913) B6255913
theorem B5556599 : Blo 1646022 5556599 := bstep (se 1 (by rfl) ⟨4167449, by rfl⟩ : syracuseStep 5556599 = 8334899) B8334899
theorem B8333927 : Blo 1646022 8333927 := bstep (se 1 (by rfl) ⟨6250445, by rfl⟩ : syracuseStep 8333927 = 12500891) B12500891
theorem B234556657 : Blo 1646022 234556657 := bstep (se 2 (by rfl) ⟨87958746, by rfl⟩ : syracuseStep 234556657 = 175917493) B175917493
theorem B10554857 : Blo 1646022 10554857 := bstep (se 2 (by rfl) ⟨3958071, by rfl⟩ : syracuseStep 10554857 = 7916143) B7916143
theorem B2780777 : Blo 1646022 2780777 := bstep (se 2 (by rfl) ⟨1042791, by rfl⟩ : syracuseStep 2780777 = 2085583) B2085583
theorem B2469545 : Blo 1646022 2469545 := bstep (se 2 (by rfl) ⟨926079, by rfl⟩ : syracuseStep 2469545 = 1852159) B1852159
theorem B2470655 : Blo 1646022 2470655 := bstep (se 1 (by rfl) ⟨1852991, by rfl⟩ : syracuseStep 2470655 = 3705983) B3705983
theorem B3707675 : Blo 1646022 3707675 := bstep (se 1 (by rfl) ⟨2780756, by rfl⟩ : syracuseStep 3707675 = 5561513) B5561513
theorem B9385307 : Blo 1646022 9385307 := bstep (se 1 (by rfl) ⟨7038980, by rfl⟩ : syracuseStep 9385307 = 14077961) B14077961
theorem B4691321 : Blo 1646022 4691321 := bstep (se 2 (by rfl) ⟨1759245, by rfl⟩ : syracuseStep 4691321 = 3518491) B3518491
theorem B9378017 : Blo 1646022 9378017 := bstep (se 2 (by rfl) ⟨3516756, by rfl⟩ : syracuseStep 9378017 = 7033513) B7033513
theorem B4168057 : Blo 1646022 4168057 := bstep (se 2 (by rfl) ⟨1563021, by rfl⟩ : syracuseStep 4168057 = 3126043) B3126043
theorem B54868603 : Blo 1646022 54868603 := bstep (se 1 (by rfl) ⟨41151452, by rfl⟩ : syracuseStep 54868603 = 82302905) B82302905
theorem B11869517 : Blo 1646022 11869517 := bstep (se 3 (by rfl) ⟨2225534, by rfl⟩ : syracuseStep 11869517 = 4451069) B4451069
theorem B8339111 : Blo 1646022 8339111 := bstep (se 1 (by rfl) ⟨6254333, by rfl⟩ : syracuseStep 8339111 = 12508667) B12508667
theorem B15826751 : Blo 1646022 15826751 := bstep (se 1 (by rfl) ⟨11870063, by rfl⟩ : syracuseStep 15826751 = 23740127) B23740127
theorem B4169627 : Blo 1646022 4169627 := bstep (se 1 (by rfl) ⟨3127220, by rfl⟩ : syracuseStep 4169627 = 6254441) B6254441
theorem B1647103 : Blo 1646022 1647103 := bstep (se 1 (by rfl) ⟨1235327, by rfl⟩ : syracuseStep 1647103 = 2470655) B2470655
theorem B3703643 : Blo 1646022 3703643 := bstep (se 1 (by rfl) ⟨2777732, by rfl⟩ : syracuseStep 3703643 = 5555465) B5555465
theorem B6341503 : Blo 1646022 6341503 := bstep (se 1 (by rfl) ⟨4756127, by rfl⟩ : syracuseStep 6341503 = 9512255) B9512255
theorem B6252011 : Blo 1646022 6252011 := bstep (se 1 (by rfl) ⟨4689008, by rfl⟩ : syracuseStep 6252011 = 9378017) B9378017
theorem B3704399 : Blo 1646022 3704399 := bstep (se 1 (by rfl) ⟨2778299, by rfl⟩ : syracuseStep 3704399 = 5556599) B5556599
theorem B5555951 : Blo 1646022 5555951 := bstep (se 1 (by rfl) ⟨4166963, by rfl⟩ : syracuseStep 5555951 = 8333927) B8333927
theorem B1853851 : Blo 1646022 1853851 := bstep (se 1 (by rfl) ⟨1390388, by rfl⟩ : syracuseStep 1853851 = 2780777) B2780777
theorem B2779751 : Blo 1646022 2779751 := bstep (se 1 (by rfl) ⟨2084813, by rfl⟩ : syracuseStep 2779751 = 4169627) B4169627
theorem B9382823 : Blo 1646022 9382823 := bstep (se 1 (by rfl) ⟨7037117, by rfl⟩ : syracuseStep 9382823 = 14074235) B14074235
theorem B5557409 : Blo 1646022 5557409 := bstep (se 2 (by rfl) ⟨2084028, by rfl⟩ : syracuseStep 5557409 = 4168057) B4168057
theorem B73158137 : Blo 1646022 73158137 := bstep (se 2 (by rfl) ⟨27434301, by rfl⟩ : syracuseStep 73158137 = 54868603) B54868603
theorem B5003875349 : Blo 1646022 5003875349 := bstep (se 6 (by rfl) ⟨117278328, by rfl⟩ : syracuseStep 5003875349 = 234556657) B234556657
theorem B5559407 : Blo 1646022 5559407 := bstep (se 1 (by rfl) ⟨4169555, by rfl⟩ : syracuseStep 5559407 = 8339111) B8339111
theorem B7034471 : Blo 1646022 7034471 := bstep (se 1 (by rfl) ⟨5275853, by rfl⟩ : syracuseStep 7034471 = 10551707) B10551707
theorem B2471783 : Blo 1646022 2471783 := bstep (se 1 (by rfl) ⟨1853837, by rfl⟩ : syracuseStep 2471783 = 3707675) B3707675
theorem B4167551 : Blo 1646022 4167551 := bstep (se 1 (by rfl) ⟨3125663, by rfl⟩ : syracuseStep 4167551 = 6251327) B6251327
theorem B43374491 : Blo 1646022 43374491 := bstep (se 1 (by rfl) ⟨32530868, by rfl⟩ : syracuseStep 43374491 = 65061737) B65061737
theorem B12507209 : Blo 1646022 12507209 := bstep (se 2 (by rfl) ⟨4690203, by rfl⟩ : syracuseStep 12507209 = 9380407) B9380407
theorem B6256871 : Blo 1646022 6256871 := bstep (se 1 (by rfl) ⟨4692653, by rfl⟩ : syracuseStep 6256871 = 9385307) B9385307
theorem B3127547 : Blo 1646022 3127547 := bstep (se 1 (by rfl) ⟨2345660, by rfl⟩ : syracuseStep 3127547 = 4691321) B4691321
theorem B5560811 : Blo 1646022 5560811 := bstep (se 1 (by rfl) ⟨4170608, by rfl⟩ : syracuseStep 5560811 = 8341217) B8341217
theorem B23747849 : Blo 1646022 23747849 := bstep (se 2 (by rfl) ⟨8905443, by rfl⟩ : syracuseStep 23747849 = 17810887) B17810887
theorem B7913011 : Blo 1646022 7913011 := bstep (se 1 (by rfl) ⟨5934758, by rfl⟩ : syracuseStep 7913011 = 11869517) B11869517
theorem B7036571 : Blo 1646022 7036571 := bstep (se 1 (by rfl) ⟨5277428, by rfl⟩ : syracuseStep 7036571 = 10554857) B10554857
theorem B1646363 : Blo 1646022 1646363 := bstep (se 1 (by rfl) ⟨1234772, by rfl⟩ : syracuseStep 1646363 = 2469545) B2469545
theorem B10551167 : Blo 1646022 10551167 := bstep (se 1 (by rfl) ⟨7913375, by rfl⟩ : syracuseStep 10551167 = 15826751) B15826751
theorem B3703967 : Blo 1646022 3703967 := bstep (se 1 (by rfl) ⟨2777975, by rfl⟩ : syracuseStep 3703967 = 5555951) B5555951
theorem B8455337 : Blo 1646022 8455337 := bstep (se 2 (by rfl) ⟨3170751, by rfl⟩ : syracuseStep 8455337 = 6341503) B6341503
theorem B1647855 : Blo 1646022 1647855 := bstep (se 1 (by rfl) ⟨1235891, by rfl⟩ : syracuseStep 1647855 = 2471783) B2471783
theorem B2778367 : Blo 1646022 2778367 := bstep (se 1 (by rfl) ⟨2083775, by rfl⟩ : syracuseStep 2778367 = 4167551) B4167551
theorem B4171247 : Blo 1646022 4171247 := bstep (se 1 (by rfl) ⟨3128435, by rfl⟩ : syracuseStep 4171247 = 6256871) B6256871
theorem B1853167 : Blo 1646022 1853167 := bstep (se 1 (by rfl) ⟨1389875, by rfl⟩ : syracuseStep 1853167 = 2779751) B2779751
theorem B3704939 : Blo 1646022 3704939 := bstep (se 1 (by rfl) ⟨2778704, by rfl⟩ : syracuseStep 3704939 = 5557409) B5557409
theorem B2469095 : Blo 1646022 2469095 := bstep (se 1 (by rfl) ⟨1851821, by rfl⟩ : syracuseStep 2469095 = 3703643) B3703643
theorem B3335916899 : Blo 1646022 3335916899 := bstep (se 1 (by rfl) ⟨2501937674, by rfl⟩ : syracuseStep 3335916899 = 5003875349) B5003875349
theorem B3706271 : Blo 1646022 3706271 := bstep (se 1 (by rfl) ⟨2779703, by rfl⟩ : syracuseStep 3706271 = 5559407) B5559407
theorem B2469599 : Blo 1646022 2469599 := bstep (se 1 (by rfl) ⟨1852199, by rfl⟩ : syracuseStep 2469599 = 3704399) B3704399
theorem B4689647 : Blo 1646022 4689647 := bstep (se 1 (by rfl) ⟨3517235, by rfl⟩ : syracuseStep 4689647 = 7034471) B7034471
theorem B2085031 : Blo 1646022 2085031 := bstep (se 1 (by rfl) ⟨1563773, by rfl⟩ : syracuseStep 2085031 = 3127547) B3127547
theorem B3707207 : Blo 1646022 3707207 := bstep (se 1 (by rfl) ⟨2780405, by rfl⟩ : syracuseStep 3707207 = 5560811) B5560811
theorem B6255215 : Blo 1646022 6255215 := bstep (se 1 (by rfl) ⟨4691411, by rfl⟩ : syracuseStep 6255215 = 9382823) B9382823
theorem B15831899 : Blo 1646022 15831899 := bstep (se 1 (by rfl) ⟨11873924, by rfl⟩ : syracuseStep 15831899 = 23747849) B23747849
theorem B48772091 : Blo 1646022 48772091 := bstep (se 1 (by rfl) ⟨36579068, by rfl⟩ : syracuseStep 48772091 = 73158137) B73158137
theorem B4691047 : Blo 1646022 4691047 := bstep (se 1 (by rfl) ⟨3518285, by rfl⟩ : syracuseStep 4691047 = 7036571) B7036571
theorem B7034111 : Blo 1646022 7034111 := bstep (se 1 (by rfl) ⟨5275583, by rfl⟩ : syracuseStep 7034111 = 10551167) B10551167
theorem B2471801 : Blo 1646022 2471801 := bstep (se 2 (by rfl) ⟨926925, by rfl⟩ : syracuseStep 2471801 = 1853851) B1853851
theorem B4168007 : Blo 1646022 4168007 := bstep (se 1 (by rfl) ⟨3126005, by rfl⟩ : syracuseStep 4168007 = 6252011) B6252011
theorem B28916327 : Blo 1646022 28916327 := bstep (se 1 (by rfl) ⟨21687245, by rfl⟩ : syracuseStep 28916327 = 43374491) B43374491
theorem B8338139 : Blo 1646022 8338139 := bstep (se 1 (by rfl) ⟨6253604, by rfl⟩ : syracuseStep 8338139 = 12507209) B12507209
theorem B10550681 : Blo 1646022 10550681 := bstep (se 2 (by rfl) ⟨3956505, by rfl⟩ : syracuseStep 10550681 = 7913011) B7913011
theorem B4170143 : Blo 1646022 4170143 := bstep (se 1 (by rfl) ⟨3127607, by rfl⟩ : syracuseStep 4170143 = 6255215) B6255215
theorem B5636891 : Blo 1646022 5636891 := bstep (se 1 (by rfl) ⟨4227668, by rfl⟩ : syracuseStep 5636891 = 8455337) B8455337
theorem B1647867 : Blo 1646022 1647867 := bstep (se 1 (by rfl) ⟨1235900, by rfl⟩ : syracuseStep 1647867 = 2471801) B2471801
theorem B2778671 : Blo 1646022 2778671 := bstep (se 1 (by rfl) ⟨2084003, by rfl⟩ : syracuseStep 2778671 = 4168007) B4168007
theorem B3704489 : Blo 1646022 3704489 := bstep (se 2 (by rfl) ⟨1389183, by rfl⟩ : syracuseStep 3704489 = 2778367) B2778367
theorem B19277551 : Blo 1646022 19277551 := bstep (se 1 (by rfl) ⟨14458163, by rfl⟩ : syracuseStep 19277551 = 28916327) B28916327
theorem B130058909 : Blo 1646022 130058909 := bstep (se 3 (by rfl) ⟨24386045, by rfl⟩ : syracuseStep 130058909 = 48772091) B48772091
theorem B2780041 : Blo 1646022 2780041 := bstep (se 2 (by rfl) ⟨1042515, by rfl⟩ : syracuseStep 2780041 = 2085031) B2085031
theorem B10554599 : Blo 1646022 10554599 := bstep (se 1 (by rfl) ⟨7915949, by rfl⟩ : syracuseStep 10554599 = 15831899) B15831899
theorem B2469311 : Blo 1646022 2469311 := bstep (se 1 (by rfl) ⟨1851983, by rfl⟩ : syracuseStep 2469311 = 3703967) B3703967
theorem B4689407 : Blo 1646022 4689407 := bstep (se 1 (by rfl) ⟨3517055, by rfl⟩ : syracuseStep 4689407 = 7034111) B7034111
theorem B2780831 : Blo 1646022 2780831 := bstep (se 1 (by rfl) ⟨2085623, by rfl⟩ : syracuseStep 2780831 = 4171247) B4171247
theorem B2469959 : Blo 1646022 2469959 := bstep (se 1 (by rfl) ⟨1852469, by rfl⟩ : syracuseStep 2469959 = 3704939) B3704939
theorem B6254729 : Blo 1646022 6254729 := bstep (se 2 (by rfl) ⟨2345523, by rfl⟩ : syracuseStep 6254729 = 4691047) B4691047
theorem B5558759 : Blo 1646022 5558759 := bstep (se 1 (by rfl) ⟨4169069, by rfl⟩ : syracuseStep 5558759 = 8338139) B8338139
theorem B2223944599 : Blo 1646022 2223944599 := bstep (se 1 (by rfl) ⟨1667958449, by rfl⟩ : syracuseStep 2223944599 = 3335916899) B3335916899
theorem B7033787 : Blo 1646022 7033787 := bstep (se 1 (by rfl) ⟨5275340, by rfl⟩ : syracuseStep 7033787 = 10550681) B10550681
theorem B2470847 : Blo 1646022 2470847 := bstep (se 1 (by rfl) ⟨1853135, by rfl⟩ : syracuseStep 2470847 = 3706271) B3706271
theorem B2470889 : Blo 1646022 2470889 := bstep (se 2 (by rfl) ⟨926583, by rfl⟩ : syracuseStep 2470889 = 1853167) B1853167
theorem B3126431 : Blo 1646022 3126431 := bstep (se 1 (by rfl) ⟨2344823, by rfl⟩ : syracuseStep 3126431 = 4689647) B4689647
theorem B2471471 : Blo 1646022 2471471 := bstep (se 1 (by rfl) ⟨1853603, by rfl⟩ : syracuseStep 2471471 = 3707207) B3707207
theorem B1646063 : Blo 1646022 1646063 := bstep (se 1 (by rfl) ⟨1234547, by rfl⟩ : syracuseStep 1646063 = 2469095) B2469095
theorem B1646399 : Blo 1646022 1646399 := bstep (se 1 (by rfl) ⟨1234799, by rfl⟩ : syracuseStep 1646399 = 2469599) B2469599
theorem B1646639 : Blo 1646022 1646639 := bstep (se 1 (by rfl) ⟨1234979, by rfl⟩ : syracuseStep 1646639 = 2469959) B2469959
theorem B4169819 : Blo 1646022 4169819 := bstep (se 1 (by rfl) ⟨3127364, by rfl⟩ : syracuseStep 4169819 = 6254729) B6254729
theorem B1647231 : Blo 1646022 1647231 := bstep (se 1 (by rfl) ⟨1235423, by rfl⟩ : syracuseStep 1647231 = 2470847) B2470847
theorem B1647259 : Blo 1646022 1647259 := bstep (se 1 (by rfl) ⟨1235444, by rfl⟩ : syracuseStep 1647259 = 2470889) B2470889
theorem B1852447 : Blo 1646022 1852447 := bstep (se 1 (by rfl) ⟨1389335, by rfl⟩ : syracuseStep 1852447 = 2778671) B2778671
theorem B1647647 : Blo 1646022 1647647 := bstep (se 1 (by rfl) ⟨1235735, by rfl⟩ : syracuseStep 1647647 = 2471471) B2471471
theorem B2965259465 : Blo 1646022 2965259465 := bstep (se 2 (by rfl) ⟨1111972299, by rfl⟩ : syracuseStep 2965259465 = 2223944599) B2223944599
theorem B86705939 : Blo 1646022 86705939 := bstep (se 1 (by rfl) ⟨65029454, by rfl⟩ : syracuseStep 86705939 = 130058909) B130058909
theorem B1853887 : Blo 1646022 1853887 := bstep (se 1 (by rfl) ⟨1390415, by rfl⟩ : syracuseStep 1853887 = 2780831) B2780831
theorem B2780095 : Blo 1646022 2780095 := bstep (se 1 (by rfl) ⟨2085071, by rfl⟩ : syracuseStep 2780095 = 4170143) B4170143
theorem B3705839 : Blo 1646022 3705839 := bstep (se 1 (by rfl) ⟨2779379, by rfl⟩ : syracuseStep 3705839 = 5558759) B5558759
theorem B4689191 : Blo 1646022 4689191 := bstep (se 1 (by rfl) ⟨3516893, by rfl⟩ : syracuseStep 4689191 = 7033787) B7033787
theorem B2084287 : Blo 1646022 2084287 := bstep (se 1 (by rfl) ⟨1563215, by rfl⟩ : syracuseStep 2084287 = 3126431) B3126431
theorem B2469659 : Blo 1646022 2469659 := bstep (se 1 (by rfl) ⟨1852244, by rfl⟩ : syracuseStep 2469659 = 3704489) B3704489
theorem B3706721 : Blo 1646022 3706721 := bstep (se 2 (by rfl) ⟨1390020, by rfl⟩ : syracuseStep 3706721 = 2780041) B2780041
theorem B25703401 : Blo 1646022 25703401 := bstep (se 2 (by rfl) ⟨9638775, by rfl⟩ : syracuseStep 25703401 = 19277551) B19277551
theorem B3126271 : Blo 1646022 3126271 := bstep (se 1 (by rfl) ⟨2344703, by rfl⟩ : syracuseStep 3126271 = 4689407) B4689407
theorem B3757927 : Blo 1646022 3757927 := bstep (se 1 (by rfl) ⟨2818445, by rfl⟩ : syracuseStep 3757927 = 5636891) B5636891
theorem B7036399 : Blo 1646022 7036399 := bstep (se 1 (by rfl) ⟨5277299, by rfl⟩ : syracuseStep 7036399 = 10554599) B10554599
theorem B1646207 : Blo 1646022 1646207 := bstep (se 1 (by rfl) ⟨1234655, by rfl⟩ : syracuseStep 1646207 = 2469311) B2469311
theorem B57803959 : Blo 1646022 57803959 := bstep (se 1 (by rfl) ⟨43352969, by rfl⟩ : syracuseStep 57803959 = 86705939) B86705939
theorem B2779049 : Blo 1646022 2779049 := bstep (se 2 (by rfl) ⟨1042143, by rfl⟩ : syracuseStep 2779049 = 2084287) B2084287
theorem B9381865 : Blo 1646022 9381865 := bstep (se 2 (by rfl) ⟨3518199, by rfl⟩ : syracuseStep 9381865 = 7036399) B7036399
theorem B2779879 : Blo 1646022 2779879 := bstep (se 1 (by rfl) ⟨2084909, by rfl⟩ : syracuseStep 2779879 = 4169819) B4169819
theorem B1976839643 : Blo 1646022 1976839643 := bstep (se 1 (by rfl) ⟨1482629732, by rfl⟩ : syracuseStep 1976839643 = 2965259465) B2965259465
theorem B3706793 : Blo 1646022 3706793 := bstep (se 2 (by rfl) ⟨1390047, by rfl⟩ : syracuseStep 3706793 = 2780095) B2780095
theorem B34271201 : Blo 1646022 34271201 := bstep (se 2 (by rfl) ⟨12851700, by rfl⟩ : syracuseStep 34271201 = 25703401) B25703401
theorem B2469929 : Blo 1646022 2469929 := bstep (se 2 (by rfl) ⟨926223, by rfl⟩ : syracuseStep 2469929 = 1852447) B1852447
theorem B2470559 : Blo 1646022 2470559 := bstep (se 1 (by rfl) ⟨1852919, by rfl⟩ : syracuseStep 2470559 = 3705839) B3705839
theorem B3126127 : Blo 1646022 3126127 := bstep (se 1 (by rfl) ⟨2344595, by rfl⟩ : syracuseStep 3126127 = 4689191) B4689191
theorem B5010569 : Blo 1646022 5010569 := bstep (se 2 (by rfl) ⟨1878963, by rfl⟩ : syracuseStep 5010569 = 3757927) B3757927
theorem B2471147 : Blo 1646022 2471147 := bstep (se 1 (by rfl) ⟨1853360, by rfl⟩ : syracuseStep 2471147 = 3706721) B3706721
theorem B2471849 : Blo 1646022 2471849 := bstep (se 2 (by rfl) ⟨926943, by rfl⟩ : syracuseStep 2471849 = 1853887) B1853887
theorem B4168361 : Blo 1646022 4168361 := bstep (se 2 (by rfl) ⟨1563135, by rfl⟩ : syracuseStep 4168361 = 3126271) B3126271
theorem B1646439 : Blo 1646022 1646439 := bstep (se 1 (by rfl) ⟨1234829, by rfl⟩ : syracuseStep 1646439 = 2469659) B2469659
theorem B1646619 : Blo 1646022 1646619 := bstep (se 1 (by rfl) ⟨1234964, by rfl⟩ : syracuseStep 1646619 = 2469929) B2469929
theorem B1647039 : Blo 1646022 1647039 := bstep (se 1 (by rfl) ⟨1235279, by rfl⟩ : syracuseStep 1647039 = 2470559) B2470559
theorem B1647431 : Blo 1646022 1647431 := bstep (se 1 (by rfl) ⟨1235573, by rfl⟩ : syracuseStep 1647431 = 2471147) B2471147
theorem B1852699 : Blo 1646022 1852699 := bstep (se 1 (by rfl) ⟨1389524, by rfl⟩ : syracuseStep 1852699 = 2779049) B2779049
theorem B1647899 : Blo 1646022 1647899 := bstep (se 1 (by rfl) ⟨1235924, by rfl⟩ : syracuseStep 1647899 = 2471849) B2471849
theorem B2778907 : Blo 1646022 2778907 := bstep (se 1 (by rfl) ⟨2084180, by rfl⟩ : syracuseStep 2778907 = 4168361) B4168361
theorem B3706505 : Blo 1646022 3706505 := bstep (se 2 (by rfl) ⟨1389939, by rfl⟩ : syracuseStep 3706505 = 2779879) B2779879
theorem B1317893095 : Blo 1646022 1317893095 := bstep (se 1 (by rfl) ⟨988419821, by rfl⟩ : syracuseStep 1317893095 = 1976839643) B1976839643
theorem B2471195 : Blo 1646022 2471195 := bstep (se 1 (by rfl) ⟨1853396, by rfl⟩ : syracuseStep 2471195 = 3706793) B3706793
theorem B3340379 : Blo 1646022 3340379 := bstep (se 1 (by rfl) ⟨2505284, by rfl⟩ : syracuseStep 3340379 = 5010569) B5010569
theorem B308287781 : Blo 1646022 308287781 := bstep (se 4 (by rfl) ⟨28901979, by rfl⟩ : syracuseStep 308287781 = 57803959) B57803959
theorem B4168169 : Blo 1646022 4168169 := bstep (se 2 (by rfl) ⟨1563063, by rfl⟩ : syracuseStep 4168169 = 3126127) B3126127
theorem B12509153 : Blo 1646022 12509153 := bstep (se 2 (by rfl) ⟨4690932, by rfl⟩ : syracuseStep 12509153 = 9381865) B9381865
theorem B22847467 : Blo 1646022 22847467 := bstep (se 1 (by rfl) ⟨17135600, by rfl⟩ : syracuseStep 22847467 = 34271201) B34271201
theorem B1647463 : Blo 1646022 1647463 := bstep (se 1 (by rfl) ⟨1235597, by rfl⟩ : syracuseStep 1647463 = 2471195) B2471195
theorem B2778779 : Blo 1646022 2778779 := bstep (se 1 (by rfl) ⟨2084084, by rfl⟩ : syracuseStep 2778779 = 4168169) B4168169
theorem B3705209 : Blo 1646022 3705209 := bstep (se 2 (by rfl) ⟨1389453, by rfl⟩ : syracuseStep 3705209 = 2778907) B2778907
theorem B205525187 : Blo 1646022 205525187 := bstep (se 1 (by rfl) ⟨154143890, by rfl⟩ : syracuseStep 205525187 = 308287781) B308287781
theorem B2470265 : Blo 1646022 2470265 := bstep (se 2 (by rfl) ⟨926349, by rfl⟩ : syracuseStep 2470265 = 1852699) B1852699
theorem B2471003 : Blo 1646022 2471003 := bstep (se 1 (by rfl) ⟨1853252, by rfl⟩ : syracuseStep 2471003 = 3706505) B3706505
theorem B30463289 : Blo 1646022 30463289 := bstep (se 2 (by rfl) ⟨11423733, by rfl⟩ : syracuseStep 30463289 = 22847467) B22847467
theorem B1757190793 : Blo 1646022 1757190793 := bstep (se 2 (by rfl) ⟨658946547, by rfl⟩ : syracuseStep 1757190793 = 1317893095) B1317893095
theorem B2226919 : Blo 1646022 2226919 := bstep (se 1 (by rfl) ⟨1670189, by rfl⟩ : syracuseStep 2226919 = 3340379) B3340379
theorem B8339435 : Blo 1646022 8339435 := bstep (se 1 (by rfl) ⟨6254576, by rfl⟩ : syracuseStep 8339435 = 12509153) B12509153
theorem B1646843 : Blo 1646022 1646843 := bstep (se 1 (by rfl) ⟨1235132, by rfl⟩ : syracuseStep 1646843 = 2470265) B2470265
theorem B1647335 : Blo 1646022 1647335 := bstep (se 1 (by rfl) ⟨1235501, by rfl⟩ : syracuseStep 1647335 = 2471003) B2471003
theorem B2342921057 : Blo 1646022 2342921057 := bstep (se 2 (by rfl) ⟨878595396, by rfl⟩ : syracuseStep 2342921057 = 1757190793) B1757190793
theorem B20308859 : Blo 1646022 20308859 := bstep (se 1 (by rfl) ⟨15231644, by rfl⟩ : syracuseStep 20308859 = 30463289) B30463289
theorem B1852519 : Blo 1646022 1852519 := bstep (se 1 (by rfl) ⟨1389389, by rfl⟩ : syracuseStep 1852519 = 2778779) B2778779
theorem B2969225 : Blo 1646022 2969225 := bstep (se 2 (by rfl) ⟨1113459, by rfl⟩ : syracuseStep 2969225 = 2226919) B2226919
theorem B2470139 : Blo 1646022 2470139 := bstep (se 1 (by rfl) ⟨1852604, by rfl⟩ : syracuseStep 2470139 = 3705209) B3705209
theorem B5559623 : Blo 1646022 5559623 := bstep (se 1 (by rfl) ⟨4169717, by rfl⟩ : syracuseStep 5559623 = 8339435) B8339435
theorem B137016791 : Blo 1646022 137016791 := bstep (se 1 (by rfl) ⟨102762593, by rfl⟩ : syracuseStep 137016791 = 205525187) B205525187
theorem B1646759 : Blo 1646022 1646759 := bstep (se 1 (by rfl) ⟨1235069, by rfl⟩ : syracuseStep 1646759 = 2470139) B2470139
theorem B1561947371 : Blo 1646022 1561947371 := bstep (se 1 (by rfl) ⟨1171460528, by rfl⟩ : syracuseStep 1561947371 = 2342921057) B2342921057
theorem B3706415 : Blo 1646022 3706415 := bstep (se 1 (by rfl) ⟨2779811, by rfl⟩ : syracuseStep 3706415 = 5559623) B5559623
theorem B91344527 : Blo 1646022 91344527 := bstep (se 1 (by rfl) ⟨68508395, by rfl⟩ : syracuseStep 91344527 = 137016791) B137016791
theorem B2470025 : Blo 1646022 2470025 := bstep (se 2 (by rfl) ⟨926259, by rfl⟩ : syracuseStep 2470025 = 1852519) B1852519
theorem B1979483 : Blo 1646022 1979483 := bstep (se 1 (by rfl) ⟨1484612, by rfl⟩ : syracuseStep 1979483 = 2969225) B2969225
theorem B13539239 : Blo 1646022 13539239 := bstep (se 1 (by rfl) ⟨10154429, by rfl⟩ : syracuseStep 13539239 = 20308859) B20308859
theorem B1646683 : Blo 1646022 1646683 := bstep (se 1 (by rfl) ⟨1235012, by rfl⟩ : syracuseStep 1646683 = 2470025) B2470025
theorem B5278621 : Blo 1646022 5278621 := bstep (se 3 (by rfl) ⟨989741, by rfl⟩ : syracuseStep 5278621 = 1979483) B1979483
theorem B1041298247 : Blo 1646022 1041298247 := bstep (se 1 (by rfl) ⟨780973685, by rfl⟩ : syracuseStep 1041298247 = 1561947371) B1561947371
theorem B2470943 : Blo 1646022 2470943 := bstep (se 1 (by rfl) ⟨1853207, by rfl⟩ : syracuseStep 2470943 = 3706415) B3706415
theorem B60896351 : Blo 1646022 60896351 := bstep (se 1 (by rfl) ⟨45672263, by rfl⟩ : syracuseStep 60896351 = 91344527) B91344527
theorem B9026159 : Blo 1646022 9026159 := bstep (se 1 (by rfl) ⟨6769619, by rfl⟩ : syracuseStep 9026159 = 13539239) B13539239
theorem B162390269 : Blo 1646022 162390269 := bstep (se 3 (by rfl) ⟨30448175, by rfl⟩ : syracuseStep 162390269 = 60896351) B60896351
theorem B694198831 : Blo 1646022 694198831 := bstep (se 1 (by rfl) ⟨520649123, by rfl⟩ : syracuseStep 694198831 = 1041298247) B1041298247
theorem B1647295 : Blo 1646022 1647295 := bstep (se 1 (by rfl) ⟨1235471, by rfl⟩ : syracuseStep 1647295 = 2470943) B2470943
theorem B7038161 : Blo 1646022 7038161 := bstep (se 2 (by rfl) ⟨2639310, by rfl⟩ : syracuseStep 7038161 = 5278621) B5278621
theorem B24069757 : Blo 1646022 24069757 := bstep (se 3 (by rfl) ⟨4513079, by rfl⟩ : syracuseStep 24069757 = 9026159) B9026159
theorem B925598441 : Blo 1646022 925598441 := bstep (se 2 (by rfl) ⟨347099415, by rfl⟩ : syracuseStep 925598441 = 694198831) B694198831
theorem B433040717 : Blo 1646022 433040717 := bstep (se 3 (by rfl) ⟨81195134, by rfl⟩ : syracuseStep 433040717 = 162390269) B162390269
theorem B32093009 : Blo 1646022 32093009 := bstep (se 2 (by rfl) ⟨12034878, by rfl⟩ : syracuseStep 32093009 = 24069757) B24069757
theorem B4692107 : Blo 1646022 4692107 := bstep (se 1 (by rfl) ⟨3519080, by rfl⟩ : syracuseStep 4692107 = 7038161) B7038161
theorem B617065627 : Blo 1646022 617065627 := bstep (se 1 (by rfl) ⟨462799220, by rfl⟩ : syracuseStep 617065627 = 925598441) B925598441
theorem B21395339 : Blo 1646022 21395339 := bstep (se 1 (by rfl) ⟨16046504, by rfl⟩ : syracuseStep 21395339 = 32093009) B32093009
theorem B3128071 : Blo 1646022 3128071 := bstep (se 1 (by rfl) ⟨2346053, by rfl⟩ : syracuseStep 3128071 = 4692107) B4692107
theorem B288693811 : Blo 1646022 288693811 := bstep (se 1 (by rfl) ⟨216520358, by rfl⟩ : syracuseStep 288693811 = 433040717) B433040717
theorem B4170761 : Blo 1646022 4170761 := bstep (se 2 (by rfl) ⟨1564035, by rfl⟩ : syracuseStep 4170761 = 3128071) B3128071
theorem B14263559 : Blo 1646022 14263559 := bstep (se 1 (by rfl) ⟨10697669, by rfl⟩ : syracuseStep 14263559 = 21395339) B21395339
theorem B822754169 : Blo 1646022 822754169 := bstep (se 2 (by rfl) ⟨308532813, by rfl⟩ : syracuseStep 822754169 = 617065627) B617065627
theorem B384925081 : Blo 1646022 384925081 := bstep (se 2 (by rfl) ⟨144346905, by rfl⟩ : syracuseStep 384925081 = 288693811) B288693811
theorem B2780507 : Blo 1646022 2780507 := bstep (se 1 (by rfl) ⟨2085380, by rfl⟩ : syracuseStep 2780507 = 4170761) B4170761
theorem B513233441 : Blo 1646022 513233441 := bstep (se 2 (by rfl) ⟨192462540, by rfl⟩ : syracuseStep 513233441 = 384925081) B384925081
theorem B9509039 : Blo 1646022 9509039 := bstep (se 1 (by rfl) ⟨7131779, by rfl⟩ : syracuseStep 9509039 = 14263559) B14263559
theorem B548502779 : Blo 1646022 548502779 := bstep (se 1 (by rfl) ⟨411377084, by rfl⟩ : syracuseStep 548502779 = 822754169) B822754169
theorem B342155627 : Blo 1646022 342155627 := bstep (se 1 (by rfl) ⟨256616720, by rfl⟩ : syracuseStep 342155627 = 513233441) B513233441
theorem B365668519 : Blo 1646022 365668519 := bstep (se 1 (by rfl) ⟨274251389, by rfl⟩ : syracuseStep 365668519 = 548502779) B548502779
theorem B1853671 : Blo 1646022 1853671 := bstep (se 1 (by rfl) ⟨1390253, by rfl⟩ : syracuseStep 1853671 = 2780507) B2780507
theorem B6339359 : Blo 1646022 6339359 := bstep (se 1 (by rfl) ⟨4754519, by rfl⟩ : syracuseStep 6339359 = 9509039) B9509039
theorem B487558025 : Blo 1646022 487558025 := bstep (se 2 (by rfl) ⟨182834259, by rfl⟩ : syracuseStep 487558025 = 365668519) B365668519
theorem B228103751 : Blo 1646022 228103751 := bstep (se 1 (by rfl) ⟨171077813, by rfl⟩ : syracuseStep 228103751 = 342155627) B342155627
theorem B2471561 : Blo 1646022 2471561 := bstep (se 2 (by rfl) ⟨926835, by rfl⟩ : syracuseStep 2471561 = 1853671) B1853671
theorem B4226239 : Blo 1646022 4226239 := bstep (se 1 (by rfl) ⟨3169679, by rfl⟩ : syracuseStep 4226239 = 6339359) B6339359
theorem B152069167 : Blo 1646022 152069167 := bstep (se 1 (by rfl) ⟨114051875, by rfl⟩ : syracuseStep 152069167 = 228103751) B228103751
theorem B1647707 : Blo 1646022 1647707 := bstep (se 1 (by rfl) ⟨1235780, by rfl⟩ : syracuseStep 1647707 = 2471561) B2471561
theorem B22539941 : Blo 1646022 22539941 := bstep (se 4 (by rfl) ⟨2113119, by rfl⟩ : syracuseStep 22539941 = 4226239) B4226239
theorem B325038683 : Blo 1646022 325038683 := bstep (se 1 (by rfl) ⟨243779012, by rfl⟩ : syracuseStep 325038683 = 487558025) B487558025
theorem B15026627 : Blo 1646022 15026627 := bstep (se 1 (by rfl) ⟨11269970, by rfl⟩ : syracuseStep 15026627 = 22539941) B22539941
theorem B216692455 : Blo 1646022 216692455 := bstep (se 1 (by rfl) ⟨162519341, by rfl⟩ : syracuseStep 216692455 = 325038683) B325038683
theorem B202758889 : Blo 1646022 202758889 := bstep (se 2 (by rfl) ⟨76034583, by rfl⟩ : syracuseStep 202758889 = 152069167) B152069167
theorem B270345185 : Blo 1646022 270345185 := bstep (se 2 (by rfl) ⟨101379444, by rfl⟩ : syracuseStep 270345185 = 202758889) B202758889
theorem B10017751 : Blo 1646022 10017751 := bstep (se 1 (by rfl) ⟨7513313, by rfl⟩ : syracuseStep 10017751 = 15026627) B15026627
theorem B288923273 : Blo 1646022 288923273 := bstep (se 2 (by rfl) ⟨108346227, by rfl⟩ : syracuseStep 288923273 = 216692455) B216692455
theorem B13357001 : Blo 1646022 13357001 := bstep (se 2 (by rfl) ⟨5008875, by rfl⟩ : syracuseStep 13357001 = 10017751) B10017751
theorem B192615515 : Blo 1646022 192615515 := bstep (se 1 (by rfl) ⟨144461636, by rfl⟩ : syracuseStep 192615515 = 288923273) B288923273
theorem B180230123 : Blo 1646022 180230123 := bstep (se 1 (by rfl) ⟨135172592, by rfl⟩ : syracuseStep 180230123 = 270345185) B270345185
theorem B128410343 : Blo 1646022 128410343 := bstep (se 1 (by rfl) ⟨96307757, by rfl⟩ : syracuseStep 128410343 = 192615515) B192615515
theorem B120153415 : Blo 1646022 120153415 := bstep (se 1 (by rfl) ⟨90115061, by rfl⟩ : syracuseStep 120153415 = 180230123) B180230123
theorem B8904667 : Blo 1646022 8904667 := bstep (se 1 (by rfl) ⟨6678500, by rfl⟩ : syracuseStep 8904667 = 13357001) B13357001
theorem B85606895 : Blo 1646022 85606895 := bstep (se 1 (by rfl) ⟨64205171, by rfl⟩ : syracuseStep 85606895 = 128410343) B128410343
theorem B160204553 : Blo 1646022 160204553 := bstep (se 2 (by rfl) ⟨60076707, by rfl⟩ : syracuseStep 160204553 = 120153415) B120153415
theorem B11872889 : Blo 1646022 11872889 := bstep (se 2 (by rfl) ⟨4452333, by rfl⟩ : syracuseStep 11872889 = 8904667) B8904667
theorem B7915259 : Blo 1646022 7915259 := bstep (se 1 (by rfl) ⟨5936444, by rfl⟩ : syracuseStep 7915259 = 11872889) B11872889
theorem B106803035 : Blo 1646022 106803035 := bstep (se 1 (by rfl) ⟨80102276, by rfl⟩ : syracuseStep 106803035 = 160204553) B160204553
theorem B228285053 : Blo 1646022 228285053 := bstep (se 3 (by rfl) ⟨42803447, by rfl⟩ : syracuseStep 228285053 = 85606895) B85606895
theorem B5276839 : Blo 1646022 5276839 := bstep (se 1 (by rfl) ⟨3957629, by rfl⟩ : syracuseStep 5276839 = 7915259) B7915259
theorem B71202023 : Blo 1646022 71202023 := bstep (se 1 (by rfl) ⟨53401517, by rfl⟩ : syracuseStep 71202023 = 106803035) B106803035
theorem B152190035 : Blo 1646022 152190035 := bstep (se 1 (by rfl) ⟨114142526, by rfl⟩ : syracuseStep 152190035 = 228285053) B228285053
theorem B101460023 : Blo 1646022 101460023 := bstep (se 1 (by rfl) ⟨76095017, by rfl⟩ : syracuseStep 101460023 = 152190035) B152190035
theorem B47468015 : Blo 1646022 47468015 := bstep (se 1 (by rfl) ⟨35601011, by rfl⟩ : syracuseStep 47468015 = 71202023) B71202023
theorem B7035785 : Blo 1646022 7035785 := bstep (se 2 (by rfl) ⟨2638419, by rfl⟩ : syracuseStep 7035785 = 5276839) B5276839
theorem B4690523 : Blo 1646022 4690523 := bstep (se 1 (by rfl) ⟨3517892, by rfl⟩ : syracuseStep 4690523 = 7035785) B7035785
theorem B67640015 : Blo 1646022 67640015 := bstep (se 1 (by rfl) ⟨50730011, by rfl⟩ : syracuseStep 67640015 = 101460023) B101460023
theorem B31645343 : Blo 1646022 31645343 := bstep (se 1 (by rfl) ⟨23734007, by rfl⟩ : syracuseStep 31645343 = 47468015) B47468015
theorem B21096895 : Blo 1646022 21096895 := bstep (se 1 (by rfl) ⟨15822671, by rfl⟩ : syracuseStep 21096895 = 31645343) B31645343
theorem B45093343 : Blo 1646022 45093343 := bstep (se 1 (by rfl) ⟨33820007, by rfl⟩ : syracuseStep 45093343 = 67640015) B67640015
theorem B3127015 : Blo 1646022 3127015 := bstep (se 1 (by rfl) ⟨2345261, by rfl⟩ : syracuseStep 3127015 = 4690523) B4690523
theorem B60124457 : Blo 1646022 60124457 := bstep (se 2 (by rfl) ⟨22546671, by rfl⟩ : syracuseStep 60124457 = 45093343) B45093343
theorem B28129193 : Blo 1646022 28129193 := bstep (se 2 (by rfl) ⟨10548447, by rfl⟩ : syracuseStep 28129193 = 21096895) B21096895
theorem B4169353 : Blo 1646022 4169353 := bstep (se 2 (by rfl) ⟨1563507, by rfl⟩ : syracuseStep 4169353 = 3127015) B3127015
theorem B18752795 : Blo 1646022 18752795 := bstep (se 1 (by rfl) ⟨14064596, by rfl⟩ : syracuseStep 18752795 = 28129193) B28129193
theorem B5559137 : Blo 1646022 5559137 := bstep (se 2 (by rfl) ⟨2084676, by rfl⟩ : syracuseStep 5559137 = 4169353) B4169353
theorem B40082971 : Blo 1646022 40082971 := bstep (se 1 (by rfl) ⟨30062228, by rfl⟩ : syracuseStep 40082971 = 60124457) B60124457
theorem B12501863 : Blo 1646022 12501863 := bstep (se 1 (by rfl) ⟨9376397, by rfl⟩ : syracuseStep 12501863 = 18752795) B18752795
theorem B3706091 : Blo 1646022 3706091 := bstep (se 1 (by rfl) ⟨2779568, by rfl⟩ : syracuseStep 3706091 = 5559137) B5559137
theorem B53443961 : Blo 1646022 53443961 := bstep (se 2 (by rfl) ⟨20041485, by rfl⟩ : syracuseStep 53443961 = 40082971) B40082971
theorem B35629307 : Blo 1646022 35629307 := bstep (se 1 (by rfl) ⟨26721980, by rfl⟩ : syracuseStep 35629307 = 53443961) B53443961
theorem B8334575 : Blo 1646022 8334575 := bstep (se 1 (by rfl) ⟨6250931, by rfl⟩ : syracuseStep 8334575 = 12501863) B12501863
theorem B2470727 : Blo 1646022 2470727 := bstep (se 1 (by rfl) ⟨1853045, by rfl⟩ : syracuseStep 2470727 = 3706091) B3706091
theorem B1647151 : Blo 1646022 1647151 := bstep (se 1 (by rfl) ⟨1235363, by rfl⟩ : syracuseStep 1647151 = 2470727) B2470727
theorem B5556383 : Blo 1646022 5556383 := bstep (se 1 (by rfl) ⟨4167287, by rfl⟩ : syracuseStep 5556383 = 8334575) B8334575
theorem B23752871 : Blo 1646022 23752871 := bstep (se 1 (by rfl) ⟨17814653, by rfl⟩ : syracuseStep 23752871 = 35629307) B35629307
theorem B15835247 : Blo 1646022 15835247 := bstep (se 1 (by rfl) ⟨11876435, by rfl⟩ : syracuseStep 15835247 = 23752871) B23752871
theorem B3704255 : Blo 1646022 3704255 := bstep (se 1 (by rfl) ⟨2778191, by rfl⟩ : syracuseStep 3704255 = 5556383) B5556383
theorem B2469503 : Blo 1646022 2469503 := bstep (se 1 (by rfl) ⟨1852127, by rfl⟩ : syracuseStep 2469503 = 3704255) B3704255
theorem B10556831 : Blo 1646022 10556831 := bstep (se 1 (by rfl) ⟨7917623, by rfl⟩ : syracuseStep 10556831 = 15835247) B15835247
theorem B7037887 : Blo 1646022 7037887 := bstep (se 1 (by rfl) ⟨5278415, by rfl⟩ : syracuseStep 7037887 = 10556831) B10556831
theorem B1646335 : Blo 1646022 1646335 := bstep (se 1 (by rfl) ⟨1234751, by rfl⟩ : syracuseStep 1646335 = 2469503) B2469503
theorem B9383849 : Blo 1646022 9383849 := bstep (se 2 (by rfl) ⟨3518943, by rfl⟩ : syracuseStep 9383849 = 7037887) B7037887
theorem B6255899 : Blo 1646022 6255899 := bstep (se 1 (by rfl) ⟨4691924, by rfl⟩ : syracuseStep 6255899 = 9383849) B9383849
theorem B4170599 : Blo 1646022 4170599 := bstep (se 1 (by rfl) ⟨3127949, by rfl⟩ : syracuseStep 4170599 = 6255899) B6255899
theorem B2780399 : Blo 1646022 2780399 := bstep (se 1 (by rfl) ⟨2085299, by rfl⟩ : syracuseStep 2780399 = 4170599) B4170599
theorem B1853599 : Blo 1646022 1853599 := bstep (se 1 (by rfl) ⟨1390199, by rfl⟩ : syracuseStep 1853599 = 2780399) B2780399
theorem B2471465 : Blo 1646022 2471465 := bstep (se 2 (by rfl) ⟨926799, by rfl⟩ : syracuseStep 2471465 = 1853599) B1853599
theorem B1647643 : Blo 1646022 1647643 := bstep (se 1 (by rfl) ⟨1235732, by rfl⟩ : syracuseStep 1647643 = 2471465) B2471465

theorem C0 (j : ℕ) (h1 : 411505 ≤ j) (h2 : j ≤ 412004) : Blo 1646022 (4 * j + 3) := by
  interval_cases j
  · exact B1646023
  · exact B1646027
  · exact B1646031
  · exact B1646035
  · exact B1646039
  · exact B1646043
  · exact B1646047
  · exact B1646051
  · exact B1646055
  · exact B1646059
  · exact B1646063
  · exact B1646067
  · exact B1646071
  · exact B1646075
  · exact B1646079
  · exact B1646083
  · exact B1646087
  · exact B1646091
  · exact B1646095
  · exact B1646099
  · exact B1646103
  · exact B1646107
  · exact B1646111
  · exact B1646115
  · exact B1646119
  · exact B1646123
  · exact B1646127
  · exact B1646131
  · exact B1646135
  · exact B1646139
  · exact B1646143
  · exact B1646147
  · exact B1646151
  · exact B1646155
  · exact B1646159
  · exact B1646163
  · exact B1646167
  · exact B1646171
  · exact B1646175
  · exact B1646179
  · exact B1646183
  · exact B1646187
  · exact B1646191
  · exact B1646195
  · exact B1646199
  · exact B1646203
  · exact B1646207
  · exact B1646211
  · exact B1646215
  · exact B1646219
  · exact B1646223
  · exact B1646227
  · exact B1646231
  · exact B1646235
  · exact B1646239
  · exact B1646243
  · exact B1646247
  · exact B1646251
  · exact B1646255
  · exact B1646259
  · exact B1646263
  · exact B1646267
  · exact B1646271
  · exact B1646275
  · exact B1646279
  · exact B1646283
  · exact B1646287
  · exact B1646291
  · exact B1646295
  · exact B1646299
  · exact B1646303
  · exact B1646307
  · exact B1646311
  · exact B1646315
  · exact B1646319
  · exact B1646323
  · exact B1646327
  · exact B1646331
  · exact B1646335
  · exact B1646339
  · exact B1646343
  · exact B1646347
  · exact B1646351
  · exact B1646355
  · exact B1646359
  · exact B1646363
  · exact B1646367
  · exact B1646371
  · exact B1646375
  · exact B1646379
  · exact B1646383
  · exact B1646387
  · exact B1646391
  · exact B1646395
  · exact B1646399
  · exact B1646403
  · exact B1646407
  · exact B1646411
  · exact B1646415
  · exact B1646419
  · exact B1646423
  · exact B1646427
  · exact B1646431
  · exact B1646435
  · exact B1646439
  · exact B1646443
  · exact B1646447
  · exact B1646451
  · exact B1646455
  · exact B1646459
  · exact B1646463
  · exact B1646467
  · exact B1646471
  · exact B1646475
  · exact B1646479
  · exact B1646483
  · exact B1646487
  · exact B1646491
  · exact B1646495
  · exact B1646499
  · exact B1646503
  · exact B1646507
  · exact B1646511
  · exact B1646515
  · exact B1646519
  · exact B1646523
  · exact B1646527
  · exact B1646531
  · exact B1646535
  · exact B1646539
  · exact B1646543
  · exact B1646547
  · exact B1646551
  · exact B1646555
  · exact B1646559
  · exact B1646563
  · exact B1646567
  · exact B1646571
  · exact B1646575
  · exact B1646579
  · exact B1646583
  · exact B1646587
  · exact B1646591
  · exact B1646595
  · exact B1646599
  · exact B1646603
  · exact B1646607
  · exact B1646611
  · exact B1646615
  · exact B1646619
  · exact B1646623
  · exact B1646627
  · exact B1646631
  · exact B1646635
  · exact B1646639
  · exact B1646643
  · exact B1646647
  · exact B1646651
  · exact B1646655
  · exact B1646659
  · exact B1646663
  · exact B1646667
  · exact B1646671
  · exact B1646675
  · exact B1646679
  · exact B1646683
  · exact B1646687
  · exact B1646691
  · exact B1646695
  · exact B1646699
  · exact B1646703
  · exact B1646707
  · exact B1646711
  · exact B1646715
  · exact B1646719
  · exact B1646723
  · exact B1646727
  · exact B1646731
  · exact B1646735
  · exact B1646739
  · exact B1646743
  · exact B1646747
  · exact B1646751
  · exact B1646755
  · exact B1646759
  · exact B1646763
  · exact B1646767
  · exact B1646771
  · exact B1646775
  · exact B1646779
  · exact B1646783
  · exact B1646787
  · exact B1646791
  · exact B1646795
  · exact B1646799
  · exact B1646803
  · exact B1646807
  · exact B1646811
  · exact B1646815
  · exact B1646819
  · exact B1646823
  · exact B1646827
  · exact B1646831
  · exact B1646835
  · exact B1646839
  · exact B1646843
  · exact B1646847
  · exact B1646851
  · exact B1646855
  · exact B1646859
  · exact B1646863
  · exact B1646867
  · exact B1646871
  · exact B1646875
  · exact B1646879
  · exact B1646883
  · exact B1646887
  · exact B1646891
  · exact B1646895
  · exact B1646899
  · exact B1646903
  · exact B1646907
  · exact B1646911
  · exact B1646915
  · exact B1646919
  · exact B1646923
  · exact B1646927
  · exact B1646931
  · exact B1646935
  · exact B1646939
  · exact B1646943
  · exact B1646947
  · exact B1646951
  · exact B1646955
  · exact B1646959
  · exact B1646963
  · exact B1646967
  · exact B1646971
  · exact B1646975
  · exact B1646979
  · exact B1646983
  · exact B1646987
  · exact B1646991
  · exact B1646995
  · exact B1646999
  · exact B1647003
  · exact B1647007
  · exact B1647011
  · exact B1647015
  · exact B1647019
  · exact B1647023
  · exact B1647027
  · exact B1647031
  · exact B1647035
  · exact B1647039
  · exact B1647043
  · exact B1647047
  · exact B1647051
  · exact B1647055
  · exact B1647059
  · exact B1647063
  · exact B1647067
  · exact B1647071
  · exact B1647075
  · exact B1647079
  · exact B1647083
  · exact B1647087
  · exact B1647091
  · exact B1647095
  · exact B1647099
  · exact B1647103
  · exact B1647107
  · exact B1647111
  · exact B1647115
  · exact B1647119
  · exact B1647123
  · exact B1647127
  · exact B1647131
  · exact B1647135
  · exact B1647139
  · exact B1647143
  · exact B1647147
  · exact B1647151
  · exact B1647155
  · exact B1647159
  · exact B1647163
  · exact B1647167
  · exact B1647171
  · exact B1647175
  · exact B1647179
  · exact B1647183
  · exact B1647187
  · exact B1647191
  · exact B1647195
  · exact B1647199
  · exact B1647203
  · exact B1647207
  · exact B1647211
  · exact B1647215
  · exact B1647219
  · exact B1647223
  · exact B1647227
  · exact B1647231
  · exact B1647235
  · exact B1647239
  · exact B1647243
  · exact B1647247
  · exact B1647251
  · exact B1647255
  · exact B1647259
  · exact B1647263
  · exact B1647267
  · exact B1647271
  · exact B1647275
  · exact B1647279
  · exact B1647283
  · exact B1647287
  · exact B1647291
  · exact B1647295
  · exact B1647299
  · exact B1647303
  · exact B1647307
  · exact B1647311
  · exact B1647315
  · exact B1647319
  · exact B1647323
  · exact B1647327
  · exact B1647331
  · exact B1647335
  · exact B1647339
  · exact B1647343
  · exact B1647347
  · exact B1647351
  · exact B1647355
  · exact B1647359
  · exact B1647363
  · exact B1647367
  · exact B1647371
  · exact B1647375
  · exact B1647379
  · exact B1647383
  · exact B1647387
  · exact B1647391
  · exact B1647395
  · exact B1647399
  · exact B1647403
  · exact B1647407
  · exact B1647411
  · exact B1647415
  · exact B1647419
  · exact B1647423
  · exact B1647427
  · exact B1647431
  · exact B1647435
  · exact B1647439
  · exact B1647443
  · exact B1647447
  · exact B1647451
  · exact B1647455
  · exact B1647459
  · exact B1647463
  · exact B1647467
  · exact B1647471
  · exact B1647475
  · exact B1647479
  · exact B1647483
  · exact B1647487
  · exact B1647491
  · exact B1647495
  · exact B1647499
  · exact B1647503
  · exact B1647507
  · exact B1647511
  · exact B1647515
  · exact B1647519
  · exact B1647523
  · exact B1647527
  · exact B1647531
  · exact B1647535
  · exact B1647539
  · exact B1647543
  · exact B1647547
  · exact B1647551
  · exact B1647555
  · exact B1647559
  · exact B1647563
  · exact B1647567
  · exact B1647571
  · exact B1647575
  · exact B1647579
  · exact B1647583
  · exact B1647587
  · exact B1647591
  · exact B1647595
  · exact B1647599
  · exact B1647603
  · exact B1647607
  · exact B1647611
  · exact B1647615
  · exact B1647619
  · exact B1647623
  · exact B1647627
  · exact B1647631
  · exact B1647635
  · exact B1647639
  · exact B1647643
  · exact B1647647
  · exact B1647651
  · exact B1647655
  · exact B1647659
  · exact B1647663
  · exact B1647667
  · exact B1647671
  · exact B1647675
  · exact B1647679
  · exact B1647683
  · exact B1647687
  · exact B1647691
  · exact B1647695
  · exact B1647699
  · exact B1647703
  · exact B1647707
  · exact B1647711
  · exact B1647715
  · exact B1647719
  · exact B1647723
  · exact B1647727
  · exact B1647731
  · exact B1647735
  · exact B1647739
  · exact B1647743
  · exact B1647747
  · exact B1647751
  · exact B1647755
  · exact B1647759
  · exact B1647763
  · exact B1647767
  · exact B1647771
  · exact B1647775
  · exact B1647779
  · exact B1647783
  · exact B1647787
  · exact B1647791
  · exact B1647795
  · exact B1647799
  · exact B1647803
  · exact B1647807
  · exact B1647811
  · exact B1647815
  · exact B1647819
  · exact B1647823
  · exact B1647827
  · exact B1647831
  · exact B1647835
  · exact B1647839
  · exact B1647843
  · exact B1647847
  · exact B1647851
  · exact B1647855
  · exact B1647859
  · exact B1647863
  · exact B1647867
  · exact B1647871
  · exact B1647875
  · exact B1647879
  · exact B1647883
  · exact B1647887
  · exact B1647891
  · exact B1647895
  · exact B1647899
  · exact B1647903
  · exact B1647907
  · exact B1647911
  · exact B1647915
  · exact B1647919
  · exact B1647923
  · exact B1647927
  · exact B1647931
  · exact B1647935
  · exact B1647939
  · exact B1647943
  · exact B1647947
  · exact B1647951
  · exact B1647955
  · exact B1647959
  · exact B1647963
  · exact B1647967
  · exact B1647971
  · exact B1647975
  · exact B1647979
  · exact B1647983
  · exact B1647987
  · exact B1647991
  · exact B1647995
  · exact B1647999
  · exact B1648003
  · exact B1648007
  · exact B1648011
  · exact B1648015
  · exact B1648019

theorem solution (m : ℕ) (hlo : 1646022 ≤ m) (hhi : m ≤ 1648022) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 411505 ≤ j := by omega
    have hj2 : j ≤ 412004 := by omega
    have hb : Blo 1646022 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
