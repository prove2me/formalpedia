-- Prove2me | solution 1 for syracuse_descends_range_646304_650304
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T19:04:46.582052+00:00
-- url     : https://prove2.me/submissions/62089a74-73c9-496f-8b40-ff4162efc8d9

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


theorem B819229 : Blo 646304 819229 := bbase (se 3 (by rfl) ⟨153605, by rfl⟩ : syracuseStep 819229 = 307211) (by norm_num)
theorem B819325 : Blo 646304 819325 := bbase (se 3 (by rfl) ⟨153623, by rfl⟩ : syracuseStep 819325 = 307247) (by norm_num)
theorem B1638589 : Blo 646304 1638589 := bbase (se 3 (by rfl) ⟨307235, by rfl⟩ : syracuseStep 1638589 = 614471) (by norm_num)
theorem B1474757 : Blo 646304 1474757 := bbase (se 4 (by rfl) ⟨138258, by rfl⟩ : syracuseStep 1474757 = 276517) (by norm_num)
theorem B819497 : Blo 646304 819497 := bbase (se 2 (by rfl) ⟨307311, by rfl⟩ : syracuseStep 819497 = 614623) (by norm_num)
theorem B1638701 : Blo 646304 1638701 := bbase (se 3 (by rfl) ⟨307256, by rfl⟩ : syracuseStep 1638701 = 614513) (by norm_num)
theorem B819553 : Blo 646304 819553 := bbase (se 2 (by rfl) ⟨307332, by rfl⟩ : syracuseStep 819553 = 614665) (by norm_num)
theorem B819649 : Blo 646304 819649 := bbase (se 2 (by rfl) ⟨307368, by rfl⟩ : syracuseStep 819649 = 614737) (by norm_num)
theorem B1638893 : Blo 646304 1638893 := bbase (se 3 (by rfl) ⟨307292, by rfl⟩ : syracuseStep 1638893 = 614585) (by norm_num)
theorem B819821 : Blo 646304 819821 := bbase (se 3 (by rfl) ⟨153716, by rfl⟩ : syracuseStep 819821 = 307433) (by norm_num)
theorem B819877 : Blo 646304 819877 := bbase (se 4 (by rfl) ⟨76863, by rfl⟩ : syracuseStep 819877 = 153727) (by norm_num)
theorem B2458309 : Blo 646304 2458309 := bbase (se 4 (by rfl) ⟨230466, by rfl⟩ : syracuseStep 2458309 = 460933) (by norm_num)
theorem B819973 : Blo 646304 819973 := bbase (se 4 (by rfl) ⟨76872, by rfl⟩ : syracuseStep 819973 = 153745) (by norm_num)
theorem B1639237 : Blo 646304 1639237 := bbase (se 4 (by rfl) ⟨153678, by rfl⟩ : syracuseStep 1639237 = 307357) (by norm_num)
theorem B820145 : Blo 646304 820145 := bbase (se 2 (by rfl) ⟨307554, by rfl⟩ : syracuseStep 820145 = 615109) (by norm_num)
theorem B1639349 : Blo 646304 1639349 := bbase (se 5 (by rfl) ⟨76844, by rfl⟩ : syracuseStep 1639349 = 153689) (by norm_num)
theorem B820201 : Blo 646304 820201 := bbase (se 2 (by rfl) ⟨307575, by rfl⟩ : syracuseStep 820201 = 615151) (by norm_num)
theorem B2458613 : Blo 646304 2458613 := bbase (se 5 (by rfl) ⟨115247, by rfl⟩ : syracuseStep 2458613 = 230495) (by norm_num)
theorem B820297 : Blo 646304 820297 := bbase (se 2 (by rfl) ⟨307611, by rfl⟩ : syracuseStep 820297 = 615223) (by norm_num)
theorem B1639541 : Blo 646304 1639541 := bbase (se 5 (by rfl) ⟨76853, by rfl⟩ : syracuseStep 1639541 = 153707) (by norm_num)
theorem B1246357 : Blo 646304 1246357 := bbase (se 6 (by rfl) ⟨29211, by rfl⟩ : syracuseStep 1246357 = 58423) (by norm_num)
theorem B3278069 : Blo 646304 3278069 := bbase (se 5 (by rfl) ⟨153659, by rfl⟩ : syracuseStep 3278069 = 307319) (by norm_num)
theorem B820469 : Blo 646304 820469 := bbase (se 5 (by rfl) ⟨38459, by rfl⟩ : syracuseStep 820469 = 76919) (by norm_num)
theorem B820525 : Blo 646304 820525 := bbase (se 3 (by rfl) ⟨153848, by rfl⟩ : syracuseStep 820525 = 307697) (by norm_num)
theorem B820621 : Blo 646304 820621 := bbase (se 3 (by rfl) ⟨153866, by rfl⟩ : syracuseStep 820621 = 307733) (by norm_num)
theorem B1181077 : Blo 646304 1181077 := bbase (se 6 (by rfl) ⟨27681, by rfl⟩ : syracuseStep 1181077 = 55363) (by norm_num)
theorem B1639885 : Blo 646304 1639885 := bbase (se 3 (by rfl) ⟨307478, by rfl⟩ : syracuseStep 1639885 = 614957) (by norm_num)
theorem B820793 : Blo 646304 820793 := bbase (se 2 (by rfl) ⟨307797, by rfl⟩ : syracuseStep 820793 = 615595) (by norm_num)
theorem B1639997 : Blo 646304 1639997 := bbase (se 3 (by rfl) ⟨307499, by rfl⟩ : syracuseStep 1639997 = 614999) (by norm_num)
theorem B820849 : Blo 646304 820849 := bbase (se 2 (by rfl) ⟨307818, by rfl⟩ : syracuseStep 820849 = 615637) (by norm_num)
theorem B820945 : Blo 646304 820945 := bbase (se 2 (by rfl) ⟨307854, by rfl⟩ : syracuseStep 820945 = 615709) (by norm_num)
theorem B1640189 : Blo 646304 1640189 := bbase (se 3 (by rfl) ⟨307535, by rfl⟩ : syracuseStep 1640189 = 615071) (by norm_num)
theorem B5605141 : Blo 646304 5605141 := bbase (se 6 (by rfl) ⟨131370, by rfl⟩ : syracuseStep 5605141 = 262741) (by norm_num)
theorem B3508085 : Blo 646304 3508085 := bbase (se 5 (by rfl) ⟨164441, by rfl⟩ : syracuseStep 3508085 = 328883) (by norm_num)
theorem B821117 : Blo 646304 821117 := bbase (se 3 (by rfl) ⟨153959, by rfl⟩ : syracuseStep 821117 = 307919) (by norm_num)
theorem B821173 : Blo 646304 821173 := bbase (se 5 (by rfl) ⟨38492, by rfl⟩ : syracuseStep 821173 = 76985) (by norm_num)
theorem B657401 : Blo 646304 657401 := bbase (se 2 (by rfl) ⟨246525, by rfl⟩ : syracuseStep 657401 = 493051) (by norm_num)
theorem B821269 : Blo 646304 821269 := bbase (se 6 (by rfl) ⟨19248, by rfl⟩ : syracuseStep 821269 = 38497) (by norm_num)
theorem B690221 : Blo 646304 690221 := bbase (se 3 (by rfl) ⟨129416, by rfl⟩ : syracuseStep 690221 = 258833) (by norm_num)
theorem B1640533 : Blo 646304 1640533 := bbase (se 8 (by rfl) ⟨9612, by rfl⟩ : syracuseStep 1640533 = 19225) (by norm_num)
theorem B1476725 : Blo 646304 1476725 := bbase (se 5 (by rfl) ⟨69221, by rfl⟩ : syracuseStep 1476725 = 138443) (by norm_num)
theorem B821441 : Blo 646304 821441 := bbase (se 2 (by rfl) ⟨308040, by rfl⟩ : syracuseStep 821441 = 616081) (by norm_num)
theorem B1640645 : Blo 646304 1640645 := bbase (se 4 (by rfl) ⟨153810, by rfl⟩ : syracuseStep 1640645 = 307621) (by norm_num)
theorem B657649 : Blo 646304 657649 := bbase (se 2 (by rfl) ⟨246618, by rfl⟩ : syracuseStep 657649 = 493237) (by norm_num)
theorem B821497 : Blo 646304 821497 := bbase (se 2 (by rfl) ⟨308061, by rfl⟩ : syracuseStep 821497 = 616123) (by norm_num)
theorem B821593 : Blo 646304 821593 := bbase (se 2 (by rfl) ⟨308097, by rfl⟩ : syracuseStep 821593 = 616195) (by norm_num)
theorem B4163957 : Blo 646304 4163957 := bbase (se 5 (by rfl) ⟨195185, by rfl⟩ : syracuseStep 4163957 = 390371) (by norm_num)
theorem B1640837 : Blo 646304 1640837 := bbase (se 4 (by rfl) ⟨153828, by rfl⟩ : syracuseStep 1640837 = 307657) (by norm_num)
theorem B788945 : Blo 646304 788945 := bbase (se 2 (by rfl) ⟨295854, by rfl⟩ : syracuseStep 788945 = 591709) (by norm_num)
theorem B690665 : Blo 646304 690665 := bbase (se 2 (by rfl) ⟨258999, by rfl⟩ : syracuseStep 690665 = 517999) (by norm_num)
theorem B3279365 : Blo 646304 3279365 := bbase (se 4 (by rfl) ⟨307440, by rfl⟩ : syracuseStep 3279365 = 614881) (by norm_num)
theorem B821765 : Blo 646304 821765 := bbase (se 4 (by rfl) ⟨77040, by rfl⟩ : syracuseStep 821765 = 154081) (by norm_num)
theorem B690725 : Blo 646304 690725 := bbase (se 4 (by rfl) ⟨64755, by rfl⟩ : syracuseStep 690725 = 129511) (by norm_num)
theorem B1968677 : Blo 646304 1968677 := bbase (se 4 (by rfl) ⟨184563, by rfl⟩ : syracuseStep 1968677 = 369127) (by norm_num)
theorem B1804853 : Blo 646304 1804853 := bbase (se 5 (by rfl) ⟨84602, by rfl⟩ : syracuseStep 1804853 = 169205) (by norm_num)
theorem B821821 : Blo 646304 821821 := bbase (se 3 (by rfl) ⟨154091, by rfl⟩ : syracuseStep 821821 = 308183) (by norm_num)
theorem B887365 : Blo 646304 887365 := bbase (se 4 (by rfl) ⟨83190, by rfl⟩ : syracuseStep 887365 = 166381) (by norm_num)
theorem B1968725 : Blo 646304 1968725 := bbase (se 8 (by rfl) ⟨11535, by rfl⟩ : syracuseStep 1968725 = 23071) (by norm_num)
theorem B789149 : Blo 646304 789149 := bbase (se 3 (by rfl) ⟨147965, by rfl⟩ : syracuseStep 789149 = 295931) (by norm_num)
theorem B821917 : Blo 646304 821917 := bbase (se 3 (by rfl) ⟨154109, by rfl⟩ : syracuseStep 821917 = 308219) (by norm_num)
theorem B690853 : Blo 646304 690853 := bbase (se 4 (by rfl) ⟨64767, by rfl⟩ : syracuseStep 690853 = 129535) (by norm_num)
theorem B1641181 : Blo 646304 1641181 := bbase (se 3 (by rfl) ⟨307721, by rfl⟩ : syracuseStep 1641181 = 615443) (by norm_num)
theorem B920317 : Blo 646304 920317 := bbase (se 3 (by rfl) ⟨172559, by rfl⟩ : syracuseStep 920317 = 345119) (by norm_num)
theorem B822089 : Blo 646304 822089 := bbase (se 2 (by rfl) ⟨308283, by rfl⟩ : syracuseStep 822089 = 616567) (by norm_num)
theorem B1641293 : Blo 646304 1641293 := bbase (se 3 (by rfl) ⟨307742, by rfl⟩ : syracuseStep 1641293 = 615485) (by norm_num)
theorem B789373 : Blo 646304 789373 := bbase (se 3 (by rfl) ⟨148007, by rfl⟩ : syracuseStep 789373 = 296015) (by norm_num)
theorem B822145 : Blo 646304 822145 := bbase (se 2 (by rfl) ⟨308304, by rfl⟩ : syracuseStep 822145 = 616609) (by norm_num)
theorem B2493317 : Blo 646304 2493317 := bbase (se 4 (by rfl) ⟨233748, by rfl⟩ : syracuseStep 2493317 = 467497) (by norm_num)
theorem B822241 : Blo 646304 822241 := bbase (se 2 (by rfl) ⟨308340, by rfl⟩ : syracuseStep 822241 = 616681) (by norm_num)
theorem B1641485 : Blo 646304 1641485 := bbase (se 3 (by rfl) ⟨307778, by rfl⟩ : syracuseStep 1641485 = 615557) (by norm_num)
theorem B1313813 : Blo 646304 1313813 := bbase (se 6 (by rfl) ⟨30792, by rfl⟩ : syracuseStep 1313813 = 61585) (by norm_num)
theorem B2460725 : Blo 646304 2460725 := bbase (se 5 (by rfl) ⟨115346, by rfl⟩ : syracuseStep 2460725 = 230693) (by norm_num)
theorem B1477693 : Blo 646304 1477693 := bbase (se 3 (by rfl) ⟨277067, by rfl⟩ : syracuseStep 1477693 = 554135) (by norm_num)
theorem B691297 : Blo 646304 691297 := bbase (se 2 (by rfl) ⟨259236, by rfl⟩ : syracuseStep 691297 = 518473) (by norm_num)
theorem B920693 : Blo 646304 920693 := bbase (se 5 (by rfl) ⟨43157, by rfl⟩ : syracuseStep 920693 = 86315) (by norm_num)
theorem B822413 : Blo 646304 822413 := bbase (se 3 (by rfl) ⟨154202, by rfl⟩ : syracuseStep 822413 = 308405) (by norm_num)
theorem B658577 : Blo 646304 658577 := bbase (se 2 (by rfl) ⟨246966, by rfl⟩ : syracuseStep 658577 = 493933) (by norm_num)
theorem B7376021 : Blo 646304 7376021 := bbase (se 6 (by rfl) ⟨172875, by rfl⟩ : syracuseStep 7376021 = 345751) (by norm_num)
theorem B2100421 : Blo 646304 2100421 := bbase (se 4 (by rfl) ⟨196914, by rfl⟩ : syracuseStep 2100421 = 393829) (by norm_num)
theorem B822469 : Blo 646304 822469 := bbase (se 4 (by rfl) ⟨77106, by rfl⟩ : syracuseStep 822469 = 154213) (by norm_num)
theorem B691417 : Blo 646304 691417 := bbase (se 2 (by rfl) ⟨259281, by rfl⟩ : syracuseStep 691417 = 518563) (by norm_num)
theorem B822565 : Blo 646304 822565 := bbase (se 4 (by rfl) ⟨77115, by rfl⟩ : syracuseStep 822565 = 154231) (by norm_num)
theorem B2461013 : Blo 646304 2461013 := bbase (se 11 (by rfl) ⟨1802, by rfl⟩ : syracuseStep 2461013 = 3605) (by norm_num)
theorem B1641829 : Blo 646304 1641829 := bbase (se 4 (by rfl) ⟨153921, by rfl⟩ : syracuseStep 1641829 = 307843) (by norm_num)
theorem B1052029 : Blo 646304 1052029 := bbase (se 3 (by rfl) ⟨197255, by rfl⟩ : syracuseStep 1052029 = 394511) (by norm_num)
theorem B822737 : Blo 646304 822737 := bbase (se 2 (by rfl) ⟨308526, by rfl⟩ : syracuseStep 822737 = 617053) (by norm_num)
theorem B691669 : Blo 646304 691669 := bbase (se 7 (by rfl) ⟨8105, by rfl⟩ : syracuseStep 691669 = 16211) (by norm_num)
theorem B1641941 : Blo 646304 1641941 := bbase (se 7 (by rfl) ⟨19241, by rfl⟩ : syracuseStep 1641941 = 38483) (by norm_num)
theorem B691673 : Blo 646304 691673 := bbase (se 2 (by rfl) ⟨259377, by rfl⟩ : syracuseStep 691673 = 518755) (by norm_num)
theorem B2100725 : Blo 646304 2100725 := bbase (se 5 (by rfl) ⟨98471, by rfl⟩ : syracuseStep 2100725 = 196943) (by norm_num)
theorem B822793 : Blo 646304 822793 := bbase (se 2 (by rfl) ⟨308547, by rfl⟩ : syracuseStep 822793 = 617095) (by norm_num)
theorem B4918805 : Blo 646304 4918805 := bbase (se 6 (by rfl) ⟨115284, by rfl⟩ : syracuseStep 4918805 = 230569) (by norm_num)
theorem B822889 : Blo 646304 822889 := bbase (se 2 (by rfl) ⟨308583, by rfl⟩ : syracuseStep 822889 = 617167) (by norm_num)
theorem B2330245 : Blo 646304 2330245 := bbase (se 4 (by rfl) ⟨218460, by rfl⟩ : syracuseStep 2330245 = 436921) (by norm_num)
theorem B1642133 : Blo 646304 1642133 := bbase (se 6 (by rfl) ⟨38487, by rfl⟩ : syracuseStep 1642133 = 76975) (by norm_num)
theorem B3280661 : Blo 646304 3280661 := bbase (se 6 (by rfl) ⟨76890, by rfl⟩ : syracuseStep 3280661 = 153781) (by norm_num)
theorem B6655861 : Blo 646304 6655861 := bbase (se 5 (by rfl) ⟨311993, by rfl⟩ : syracuseStep 6655861 = 623987) (by norm_num)
theorem B1642477 : Blo 646304 1642477 := bbase (se 3 (by rfl) ⟨307964, by rfl⟩ : syracuseStep 1642477 = 615929) (by norm_num)
theorem B692237 : Blo 646304 692237 := bbase (se 3 (by rfl) ⟨129794, by rfl⟩ : syracuseStep 692237 = 259589) (by norm_num)
theorem B1642589 : Blo 646304 1642589 := bbase (se 3 (by rfl) ⟨307985, by rfl⟩ : syracuseStep 1642589 = 615971) (by norm_num)
theorem B1380493 : Blo 646304 1380493 := bbase (se 3 (by rfl) ⟨258842, by rfl⟩ : syracuseStep 1380493 = 517685) (by norm_num)
theorem B692425 : Blo 646304 692425 := bbase (se 2 (by rfl) ⟨259659, by rfl⟩ : syracuseStep 692425 = 519319) (by norm_num)
theorem B1315045 : Blo 646304 1315045 := bbase (se 4 (by rfl) ⟨123285, by rfl⟩ : syracuseStep 1315045 = 246571) (by norm_num)
theorem B1642781 : Blo 646304 1642781 := bbase (se 3 (by rfl) ⟨308021, by rfl⟩ : syracuseStep 1642781 = 616043) (by norm_num)
theorem B1184053 : Blo 646304 1184053 := bbase (se 5 (by rfl) ⟨55502, by rfl⟩ : syracuseStep 1184053 = 111005) (by norm_num)
theorem B2462197 : Blo 646304 2462197 := bbase (se 5 (by rfl) ⟨115415, by rfl⟩ : syracuseStep 2462197 = 230831) (by norm_num)
theorem B922117 : Blo 646304 922117 := bbase (se 4 (by rfl) ⟨86448, by rfl⟩ : syracuseStep 922117 = 172897) (by norm_num)
theorem B1643125 : Blo 646304 1643125 := bbase (se 5 (by rfl) ⟨77021, by rfl⟩ : syracuseStep 1643125 = 154043) (by norm_num)
theorem B1380989 : Blo 646304 1380989 := bbase (se 3 (by rfl) ⟨258935, by rfl⟩ : syracuseStep 1380989 = 517871) (by norm_num)
theorem B3117797 : Blo 646304 3117797 := bbase (se 4 (by rfl) ⟨292293, by rfl⟩ : syracuseStep 3117797 = 584587) (by norm_num)
theorem B1643237 : Blo 646304 1643237 := bbase (se 4 (by rfl) ⟨154053, by rfl⟩ : syracuseStep 1643237 = 308107) (by norm_num)
theorem B1315597 : Blo 646304 1315597 := bbase (se 3 (by rfl) ⟨246674, by rfl⟩ : syracuseStep 1315597 = 493349) (by norm_num)
theorem B2462501 : Blo 646304 2462501 := bbase (se 4 (by rfl) ⟨230859, by rfl⟩ : syracuseStep 2462501 = 461719) (by norm_num)
theorem B1643429 : Blo 646304 1643429 := bbase (se 4 (by rfl) ⟨154071, by rfl⟩ : syracuseStep 1643429 = 308143) (by norm_num)
theorem B2888677 : Blo 646304 2888677 := bbase (se 4 (by rfl) ⟨270813, by rfl⟩ : syracuseStep 2888677 = 541627) (by norm_num)
theorem B693245 : Blo 646304 693245 := bbase (se 3 (by rfl) ⟨129983, by rfl⟩ : syracuseStep 693245 = 259967) (by norm_num)
theorem B3281957 : Blo 646304 3281957 := bbase (se 4 (by rfl) ⟨307683, by rfl⟩ : syracuseStep 3281957 = 615367) (by norm_num)
theorem B922709 : Blo 646304 922709 := bbase (se 8 (by rfl) ⟨5406, by rfl⟩ : syracuseStep 922709 = 10813) (by norm_num)
theorem B922789 : Blo 646304 922789 := bbase (se 4 (by rfl) ⟨86511, by rfl⟩ : syracuseStep 922789 = 173023) (by norm_num)
theorem B1643773 : Blo 646304 1643773 := bbase (se 3 (by rfl) ⟨308207, by rfl⟩ : syracuseStep 1643773 = 616415) (by norm_num)
theorem B922909 : Blo 646304 922909 := bbase (se 3 (by rfl) ⟨173045, by rfl⟩ : syracuseStep 922909 = 346091) (by norm_num)
theorem B1643885 : Blo 646304 1643885 := bbase (se 3 (by rfl) ⟨308228, by rfl⟩ : syracuseStep 1643885 = 616457) (by norm_num)
theorem B923005 : Blo 646304 923005 := bbase (se 3 (by rfl) ⟨173063, by rfl⟩ : syracuseStep 923005 = 346127) (by norm_num)
theorem B3151237 : Blo 646304 3151237 := bbase (se 4 (by rfl) ⟨295428, by rfl⟩ : syracuseStep 3151237 = 590857) (by norm_num)
theorem B693689 : Blo 646304 693689 := bbase (se 2 (by rfl) ⟨260133, by rfl⟩ : syracuseStep 693689 = 520267) (by norm_num)
theorem B1381877 : Blo 646304 1381877 := bbase (se 5 (by rfl) ⟨64775, by rfl⟩ : syracuseStep 1381877 = 129551) (by norm_num)
theorem B2627093 : Blo 646304 2627093 := bbase (se 6 (by rfl) ⟨61572, by rfl⟩ : syracuseStep 2627093 = 123145) (by norm_num)
theorem B1644077 : Blo 646304 1644077 := bbase (se 3 (by rfl) ⟨308264, by rfl⟩ : syracuseStep 1644077 = 616529) (by norm_num)
theorem B1381997 : Blo 646304 1381997 := bbase (se 3 (by rfl) ⟨259124, by rfl⟩ : syracuseStep 1381997 = 518249) (by norm_num)
theorem B3511957 : Blo 646304 3511957 := bbase (se 6 (by rfl) ⟨82311, by rfl⟩ : syracuseStep 3511957 = 164623) (by norm_num)
theorem B1971877 : Blo 646304 1971877 := bbase (se 4 (by rfl) ⟨184863, by rfl⟩ : syracuseStep 1971877 = 369727) (by norm_num)
theorem B693937 : Blo 646304 693937 := bbase (se 2 (by rfl) ⟨260226, by rfl⟩ : syracuseStep 693937 = 520453) (by norm_num)
theorem B923501 : Blo 646304 923501 := bbase (se 3 (by rfl) ⟨173156, by rfl⟩ : syracuseStep 923501 = 346313) (by norm_num)
theorem B1644421 : Blo 646304 1644421 := bbase (se 4 (by rfl) ⟨154164, by rfl⟩ : syracuseStep 1644421 = 308329) (by norm_num)
theorem B1644533 : Blo 646304 1644533 := bbase (se 5 (by rfl) ⟨77087, by rfl⟩ : syracuseStep 1644533 = 154175) (by norm_num)
theorem B4659221 : Blo 646304 4659221 := bbase (se 6 (by rfl) ⟨109200, by rfl⟩ : syracuseStep 4659221 = 218401) (by norm_num)
theorem B3119141 : Blo 646304 3119141 := bbase (se 4 (by rfl) ⟨292419, by rfl⟩ : syracuseStep 3119141 = 584839) (by norm_num)
theorem B727105 : Blo 646304 727105 := bbase (se 2 (by rfl) ⟨272664, by rfl⟩ : syracuseStep 727105 = 545329) (by norm_num)
theorem B694369 : Blo 646304 694369 := bbase (se 2 (by rfl) ⟨260388, by rfl⟩ : syracuseStep 694369 = 520777) (by norm_num)
theorem B727141 : Blo 646304 727141 := bbase (se 4 (by rfl) ⟨68169, by rfl⟩ : syracuseStep 727141 = 136339) (by norm_num)
theorem B727177 : Blo 646304 727177 := bbase (se 2 (by rfl) ⟨272691, by rfl⟩ : syracuseStep 727177 = 545383) (by norm_num)
theorem B694441 : Blo 646304 694441 := bbase (se 2 (by rfl) ⟨260415, by rfl⟩ : syracuseStep 694441 = 520831) (by norm_num)
theorem B727213 : Blo 646304 727213 := bbase (se 3 (by rfl) ⟨136352, by rfl⟩ : syracuseStep 727213 = 272705) (by norm_num)
theorem B1644725 : Blo 646304 1644725 := bbase (se 5 (by rfl) ⟨77096, by rfl⟩ : syracuseStep 1644725 = 154193) (by norm_num)
theorem B727249 : Blo 646304 727249 := bbase (se 2 (by rfl) ⟨272718, by rfl⟩ : syracuseStep 727249 = 545437) (by norm_num)
theorem B1382629 : Blo 646304 1382629 := bbase (se 4 (by rfl) ⟨129621, by rfl⟩ : syracuseStep 1382629 = 259243) (by norm_num)
theorem B727285 : Blo 646304 727285 := bbase (se 5 (by rfl) ⟨34091, by rfl⟩ : syracuseStep 727285 = 68183) (by norm_num)
theorem B2070805 : Blo 646304 2070805 := bbase (se 6 (by rfl) ⟨48534, by rfl⟩ : syracuseStep 2070805 = 97069) (by norm_num)
theorem B727321 : Blo 646304 727321 := bbase (se 2 (by rfl) ⟨272745, by rfl⟩ : syracuseStep 727321 = 545491) (by norm_num)
theorem B3283253 : Blo 646304 3283253 := bbase (se 5 (by rfl) ⟨153902, by rfl⟩ : syracuseStep 3283253 = 307805) (by norm_num)
theorem B727357 : Blo 646304 727357 := bbase (se 3 (by rfl) ⟨136379, by rfl⟩ : syracuseStep 727357 = 272759) (by norm_num)
theorem B727393 : Blo 646304 727393 := bbase (se 2 (by rfl) ⟨272772, by rfl⟩ : syracuseStep 727393 = 545545) (by norm_num)
theorem B727429 : Blo 646304 727429 := bbase (se 4 (by rfl) ⟨68196, by rfl⟩ : syracuseStep 727429 = 136393) (by norm_num)
theorem B924053 : Blo 646304 924053 := bbase (se 6 (by rfl) ⟨21657, by rfl⟩ : syracuseStep 924053 = 43315) (by norm_num)
theorem B727465 : Blo 646304 727465 := bbase (se 2 (by rfl) ⟨272799, by rfl⟩ : syracuseStep 727465 = 545599) (by norm_num)
theorem B694729 : Blo 646304 694729 := bbase (se 2 (by rfl) ⟨260523, by rfl⟩ : syracuseStep 694729 = 521047) (by norm_num)
theorem B727501 : Blo 646304 727501 := bbase (se 3 (by rfl) ⟨136406, by rfl⟩ : syracuseStep 727501 = 272813) (by norm_num)
theorem B727537 : Blo 646304 727537 := bbase (se 2 (by rfl) ⟨272826, by rfl⟩ : syracuseStep 727537 = 545653) (by norm_num)
theorem B1645069 : Blo 646304 1645069 := bbase (se 3 (by rfl) ⟨308450, by rfl⟩ : syracuseStep 1645069 = 616901) (by norm_num)
theorem B727573 : Blo 646304 727573 := bbase (se 6 (by rfl) ⟨17052, by rfl⟩ : syracuseStep 727573 = 34105) (by norm_num)
theorem B1841717 : Blo 646304 1841717 := bbase (se 5 (by rfl) ⟨86330, by rfl⟩ : syracuseStep 1841717 = 172661) (by norm_num)
theorem B727609 : Blo 646304 727609 := bbase (se 2 (by rfl) ⟨272853, by rfl⟩ : syracuseStep 727609 = 545707) (by norm_num)
theorem B727645 : Blo 646304 727645 := bbase (se 3 (by rfl) ⟨136433, by rfl⟩ : syracuseStep 727645 = 272867) (by norm_num)
theorem B1645181 : Blo 646304 1645181 := bbase (se 3 (by rfl) ⟨308471, by rfl⟩ : syracuseStep 1645181 = 616943) (by norm_num)
theorem B727681 : Blo 646304 727681 := bbase (se 2 (by rfl) ⟨272880, by rfl⟩ : syracuseStep 727681 = 545761) (by norm_num)
theorem B727717 : Blo 646304 727717 := bbase (se 4 (by rfl) ⟨68223, by rfl⟩ : syracuseStep 727717 = 136447) (by norm_num)
theorem B727753 : Blo 646304 727753 := bbase (se 2 (by rfl) ⟨272907, by rfl⟩ : syracuseStep 727753 = 545815) (by norm_num)
theorem B727789 : Blo 646304 727789 := bbase (se 3 (by rfl) ⟨136460, by rfl⟩ : syracuseStep 727789 = 272921) (by norm_num)
theorem B727825 : Blo 646304 727825 := bbase (se 2 (by rfl) ⟨272934, by rfl⟩ : syracuseStep 727825 = 545869) (by norm_num)
theorem B2333461 : Blo 646304 2333461 := bbase (se 6 (by rfl) ⟨54690, by rfl⟩ : syracuseStep 2333461 = 109381) (by norm_num)
theorem B5315381 : Blo 646304 5315381 := bbase (se 5 (by rfl) ⟨249158, by rfl⟩ : syracuseStep 5315381 = 498317) (by norm_num)
theorem B727861 : Blo 646304 727861 := bbase (se 5 (by rfl) ⟨34118, by rfl⟩ : syracuseStep 727861 = 68237) (by norm_num)
theorem B1645373 : Blo 646304 1645373 := bbase (se 3 (by rfl) ⟨308507, by rfl⟩ : syracuseStep 1645373 = 617015) (by norm_num)
theorem B727897 : Blo 646304 727897 := bbase (se 2 (by rfl) ⟨272961, by rfl⟩ : syracuseStep 727897 = 545923) (by norm_num)
theorem B2464613 : Blo 646304 2464613 := bbase (se 4 (by rfl) ⟨231057, by rfl⟩ : syracuseStep 2464613 = 462115) (by norm_num)
theorem B727933 : Blo 646304 727933 := bbase (se 3 (by rfl) ⟨136487, by rfl⟩ : syracuseStep 727933 = 272975) (by norm_num)
theorem B727969 : Blo 646304 727969 := bbase (se 2 (by rfl) ⟨272988, by rfl⟩ : syracuseStep 727969 = 545977) (by norm_num)
theorem B728005 : Blo 646304 728005 := bbase (se 4 (by rfl) ⟨68250, by rfl⟩ : syracuseStep 728005 = 136501) (by norm_num)
theorem B1874917 : Blo 646304 1874917 := bbase (se 4 (by rfl) ⟨175773, by rfl⟩ : syracuseStep 1874917 = 351547) (by norm_num)
theorem B728041 : Blo 646304 728041 := bbase (se 2 (by rfl) ⟨273015, by rfl⟩ : syracuseStep 728041 = 546031) (by norm_num)
theorem B728077 : Blo 646304 728077 := bbase (se 3 (by rfl) ⟨136514, by rfl⟩ : syracuseStep 728077 = 273029) (by norm_num)
theorem B728113 : Blo 646304 728113 := bbase (se 2 (by rfl) ⟨273042, by rfl⟩ : syracuseStep 728113 = 546085) (by norm_num)
theorem B728149 : Blo 646304 728149 := bbase (se 8 (by rfl) ⟨4266, by rfl⟩ : syracuseStep 728149 = 8533) (by norm_num)
theorem B1383517 : Blo 646304 1383517 := bbase (se 3 (by rfl) ⟨259409, by rfl⟩ : syracuseStep 1383517 = 518819) (by norm_num)
theorem B728185 : Blo 646304 728185 := bbase (se 2 (by rfl) ⟨273069, by rfl⟩ : syracuseStep 728185 = 546139) (by norm_num)
theorem B2464901 : Blo 646304 2464901 := bbase (se 4 (by rfl) ⟨231084, by rfl⟩ : syracuseStep 2464901 = 462169) (by norm_num)
theorem B924805 : Blo 646304 924805 := bbase (se 4 (by rfl) ⟨86700, by rfl⟩ : syracuseStep 924805 = 173401) (by norm_num)
theorem B1645717 : Blo 646304 1645717 := bbase (se 6 (by rfl) ⟨38571, by rfl⟩ : syracuseStep 1645717 = 77143) (by norm_num)
theorem B728221 : Blo 646304 728221 := bbase (se 3 (by rfl) ⟨136541, by rfl⟩ : syracuseStep 728221 = 273083) (by norm_num)
theorem B728257 : Blo 646304 728257 := bbase (se 2 (by rfl) ⟨273096, by rfl⟩ : syracuseStep 728257 = 546193) (by norm_num)
theorem B1842389 : Blo 646304 1842389 := bbase (se 7 (by rfl) ⟨21590, by rfl⟩ : syracuseStep 1842389 = 43181) (by norm_num)
theorem B1383637 : Blo 646304 1383637 := bbase (se 7 (by rfl) ⟨16214, by rfl⟩ : syracuseStep 1383637 = 32429) (by norm_num)
theorem B728293 : Blo 646304 728293 := bbase (se 4 (by rfl) ⟨68277, by rfl⟩ : syracuseStep 728293 = 136555) (by norm_num)
theorem B2956517 : Blo 646304 2956517 := bbase (se 4 (by rfl) ⟨277173, by rfl⟩ : syracuseStep 2956517 = 554347) (by norm_num)
theorem B1645829 : Blo 646304 1645829 := bbase (se 4 (by rfl) ⟨154296, by rfl⟩ : syracuseStep 1645829 = 308593) (by norm_num)
theorem B728329 : Blo 646304 728329 := bbase (se 2 (by rfl) ⟨273123, by rfl⟩ : syracuseStep 728329 = 546247) (by norm_num)
theorem B728365 : Blo 646304 728365 := bbase (se 3 (by rfl) ⟨136568, by rfl⟩ : syracuseStep 728365 = 273137) (by norm_num)
theorem B728401 : Blo 646304 728401 := bbase (se 2 (by rfl) ⟨273150, by rfl⟩ : syracuseStep 728401 = 546301) (by norm_num)
theorem B2694485 : Blo 646304 2694485 := bbase (se 11 (by rfl) ⟨1973, by rfl⟩ : syracuseStep 2694485 = 3947) (by norm_num)
theorem B728437 : Blo 646304 728437 := bbase (se 5 (by rfl) ⟨34145, by rfl⟩ : syracuseStep 728437 = 68291) (by norm_num)
theorem B728473 : Blo 646304 728473 := bbase (se 2 (by rfl) ⟨273177, by rfl⟩ : syracuseStep 728473 = 546355) (by norm_num)
theorem B3120565 : Blo 646304 3120565 := bbase (se 5 (by rfl) ⟨146276, by rfl⟩ : syracuseStep 3120565 = 292553) (by norm_num)
theorem B728509 : Blo 646304 728509 := bbase (se 3 (by rfl) ⟨136595, by rfl⟩ : syracuseStep 728509 = 273191) (by norm_num)
theorem B1646021 : Blo 646304 1646021 := bbase (se 4 (by rfl) ⟨154314, by rfl⟩ : syracuseStep 1646021 = 308629) (by norm_num)
theorem B1383893 : Blo 646304 1383893 := bbase (se 7 (by rfl) ⟨16217, by rfl⟩ : syracuseStep 1383893 = 32435) (by norm_num)
theorem B728545 : Blo 646304 728545 := bbase (se 2 (by rfl) ⟨273204, by rfl⟩ : syracuseStep 728545 = 546409) (by norm_num)
theorem B2334197 : Blo 646304 2334197 := bbase (se 5 (by rfl) ⟨109415, by rfl⟩ : syracuseStep 2334197 = 218831) (by norm_num)
theorem B728581 : Blo 646304 728581 := bbase (se 4 (by rfl) ⟨68304, by rfl⟩ : syracuseStep 728581 = 136609) (by norm_num)
theorem B728617 : Blo 646304 728617 := bbase (se 2 (by rfl) ⟨273231, by rfl⟩ : syracuseStep 728617 = 546463) (by norm_num)
theorem B3284549 : Blo 646304 3284549 := bbase (se 4 (by rfl) ⟨307926, by rfl⟩ : syracuseStep 3284549 = 615853) (by norm_num)
theorem B728653 : Blo 646304 728653 := bbase (se 3 (by rfl) ⟨136622, by rfl⟩ : syracuseStep 728653 = 273245) (by norm_num)
theorem B728689 : Blo 646304 728689 := bbase (se 2 (by rfl) ⟨273258, by rfl⟩ : syracuseStep 728689 = 546517) (by norm_num)
theorem B1842821 : Blo 646304 1842821 := bbase (se 4 (by rfl) ⟨172764, by rfl⟩ : syracuseStep 1842821 = 345529) (by norm_num)
theorem B728725 : Blo 646304 728725 := bbase (se 6 (by rfl) ⟨17079, by rfl⟩ : syracuseStep 728725 = 34159) (by norm_num)
theorem B728761 : Blo 646304 728761 := bbase (se 2 (by rfl) ⟨273285, by rfl⟩ : syracuseStep 728761 = 546571) (by norm_num)
theorem B1121989 : Blo 646304 1121989 := bbase (se 4 (by rfl) ⟨105186, by rfl⟩ : syracuseStep 1121989 = 210373) (by norm_num)
theorem B5545685 : Blo 646304 5545685 := bbase (se 7 (by rfl) ⟨64988, by rfl⟩ : syracuseStep 5545685 = 129977) (by norm_num)
theorem B728797 : Blo 646304 728797 := bbase (se 3 (by rfl) ⟨136649, by rfl⟩ : syracuseStep 728797 = 273299) (by norm_num)
theorem B728833 : Blo 646304 728833 := bbase (se 2 (by rfl) ⟨273312, by rfl⟩ : syracuseStep 728833 = 546625) (by norm_num)
theorem B728869 : Blo 646304 728869 := bbase (se 4 (by rfl) ⟨68331, by rfl⟩ : syracuseStep 728869 = 136663) (by norm_num)
theorem B728905 : Blo 646304 728905 := bbase (se 2 (by rfl) ⟨273339, by rfl⟩ : syracuseStep 728905 = 546679) (by norm_num)
theorem B2072405 : Blo 646304 2072405 := bbase (se 9 (by rfl) ⟨6071, by rfl⟩ : syracuseStep 2072405 = 12143) (by norm_num)
theorem B728941 : Blo 646304 728941 := bbase (se 3 (by rfl) ⟨136676, by rfl⟩ : syracuseStep 728941 = 273353) (by norm_num)
theorem B728977 : Blo 646304 728977 := bbase (se 2 (by rfl) ⟨273366, by rfl⟩ : syracuseStep 728977 = 546733) (by norm_num)
theorem B925597 : Blo 646304 925597 := bbase (se 3 (by rfl) ⟨173549, by rfl⟩ : syracuseStep 925597 = 347099) (by norm_num)
theorem B729013 : Blo 646304 729013 := bbase (se 5 (by rfl) ⟨34172, by rfl⟩ : syracuseStep 729013 = 68345) (by norm_num)
theorem B729049 : Blo 646304 729049 := bbase (se 2 (by rfl) ⟨273393, by rfl⟩ : syracuseStep 729049 = 546787) (by norm_num)
theorem B729085 : Blo 646304 729085 := bbase (se 3 (by rfl) ⟨136703, by rfl⟩ : syracuseStep 729085 = 273407) (by norm_num)
theorem B729121 : Blo 646304 729121 := bbase (se 2 (by rfl) ⟨273420, by rfl⟩ : syracuseStep 729121 = 546841) (by norm_num)
theorem B729157 : Blo 646304 729157 := bbase (se 4 (by rfl) ⟨68358, by rfl⟩ : syracuseStep 729157 = 136717) (by norm_num)
theorem B729193 : Blo 646304 729193 := bbase (se 2 (by rfl) ⟨273447, by rfl⟩ : syracuseStep 729193 = 546895) (by norm_num)
theorem B729229 : Blo 646304 729229 := bbase (se 3 (by rfl) ⟨136730, by rfl⟩ : syracuseStep 729229 = 273461) (by norm_num)
theorem B1876117 : Blo 646304 1876117 := bbase (se 6 (by rfl) ⟨43971, by rfl⟩ : syracuseStep 1876117 = 87943) (by norm_num)
theorem B729265 : Blo 646304 729265 := bbase (se 2 (by rfl) ⟨273474, by rfl⟩ : syracuseStep 729265 = 546949) (by norm_num)
theorem B729301 : Blo 646304 729301 := bbase (se 7 (by rfl) ⟨8546, by rfl⟩ : syracuseStep 729301 = 17093) (by norm_num)
theorem B6004949 : Blo 646304 6004949 := bbase (se 7 (by rfl) ⟨70370, by rfl⟩ : syracuseStep 6004949 = 140741) (by norm_num)
theorem B729337 : Blo 646304 729337 := bbase (se 2 (by rfl) ⟨273501, by rfl⟩ : syracuseStep 729337 = 547003) (by norm_num)
theorem B729373 : Blo 646304 729373 := bbase (se 3 (by rfl) ⟨136757, by rfl⟩ : syracuseStep 729373 = 273515) (by norm_num)
theorem B2466085 : Blo 646304 2466085 := bbase (se 4 (by rfl) ⟨231195, by rfl⟩ : syracuseStep 2466085 = 462391) (by norm_num)
theorem B729409 : Blo 646304 729409 := bbase (se 2 (by rfl) ⟨273528, by rfl⟩ : syracuseStep 729409 = 547057) (by norm_num)
theorem B1384781 : Blo 646304 1384781 := bbase (se 3 (by rfl) ⟨259646, by rfl⟩ : syracuseStep 1384781 = 519293) (by norm_num)
theorem B729445 : Blo 646304 729445 := bbase (se 4 (by rfl) ⟨68385, by rfl⟩ : syracuseStep 729445 = 136771) (by norm_num)
theorem B1843573 : Blo 646304 1843573 := bbase (se 5 (by rfl) ⟨86417, by rfl⟩ : syracuseStep 1843573 = 172835) (by norm_num)
theorem B729481 : Blo 646304 729481 := bbase (se 2 (by rfl) ⟨273555, by rfl⟩ : syracuseStep 729481 = 547111) (by norm_num)
theorem B729517 : Blo 646304 729517 := bbase (se 3 (by rfl) ⟨136784, by rfl⟩ : syracuseStep 729517 = 273569) (by norm_num)
theorem B729553 : Blo 646304 729553 := bbase (se 2 (by rfl) ⟨273582, by rfl⟩ : syracuseStep 729553 = 547165) (by norm_num)
theorem B2105813 : Blo 646304 2105813 := bbase (se 7 (by rfl) ⟨24677, by rfl⟩ : syracuseStep 2105813 = 49355) (by norm_num)
theorem B729589 : Blo 646304 729589 := bbase (se 5 (by rfl) ⟨34199, by rfl⟩ : syracuseStep 729589 = 68399) (by norm_num)
theorem B729625 : Blo 646304 729625 := bbase (se 2 (by rfl) ⟨273609, by rfl⟩ : syracuseStep 729625 = 547219) (by norm_num)
theorem B1385021 : Blo 646304 1385021 := bbase (se 3 (by rfl) ⟨259691, by rfl⟩ : syracuseStep 1385021 = 519383) (by norm_num)
theorem B729661 : Blo 646304 729661 := bbase (se 3 (by rfl) ⟨136811, by rfl⟩ : syracuseStep 729661 = 273623) (by norm_num)
theorem B2466389 : Blo 646304 2466389 := bbase (se 8 (by rfl) ⟨14451, by rfl⟩ : syracuseStep 2466389 = 28903) (by norm_num)
theorem B729697 : Blo 646304 729697 := bbase (se 2 (by rfl) ⟨273636, by rfl⟩ : syracuseStep 729697 = 547273) (by norm_num)
theorem B729733 : Blo 646304 729733 := bbase (se 4 (by rfl) ⟨68412, by rfl⟩ : syracuseStep 729733 = 136825) (by norm_num)
theorem B729769 : Blo 646304 729769 := bbase (se 2 (by rfl) ⟨273663, by rfl⟩ : syracuseStep 729769 = 547327) (by norm_num)
theorem B2761397 : Blo 646304 2761397 := bbase (se 5 (by rfl) ⟨129440, by rfl⟩ : syracuseStep 2761397 = 258881) (by norm_num)
theorem B5415605 : Blo 646304 5415605 := bbase (se 5 (by rfl) ⟨253856, by rfl⟩ : syracuseStep 5415605 = 507713) (by norm_num)
theorem B729805 : Blo 646304 729805 := bbase (se 3 (by rfl) ⟨136838, by rfl⟩ : syracuseStep 729805 = 273677) (by norm_num)
theorem B729841 : Blo 646304 729841 := bbase (se 2 (by rfl) ⟨273690, by rfl⟩ : syracuseStep 729841 = 547381) (by norm_num)
theorem B729877 : Blo 646304 729877 := bbase (se 6 (by rfl) ⟨17106, by rfl⟩ : syracuseStep 729877 = 34213) (by norm_num)
theorem B729913 : Blo 646304 729913 := bbase (se 2 (by rfl) ⟨273717, by rfl⟩ : syracuseStep 729913 = 547435) (by norm_num)
theorem B3285845 : Blo 646304 3285845 := bbase (se 9 (by rfl) ⟨9626, by rfl⟩ : syracuseStep 3285845 = 19253) (by norm_num)
theorem B729949 : Blo 646304 729949 := bbase (se 3 (by rfl) ⟨136865, by rfl⟩ : syracuseStep 729949 = 273731) (by norm_num)
theorem B729985 : Blo 646304 729985 := bbase (se 2 (by rfl) ⟨273744, by rfl⟩ : syracuseStep 729985 = 547489) (by norm_num)
theorem B2073509 : Blo 646304 2073509 := bbase (se 4 (by rfl) ⟨194391, by rfl⟩ : syracuseStep 2073509 = 388783) (by norm_num)
theorem B730021 : Blo 646304 730021 := bbase (se 4 (by rfl) ⟨68439, by rfl⟩ : syracuseStep 730021 = 136879) (by norm_num)
theorem B730057 : Blo 646304 730057 := bbase (se 2 (by rfl) ⟨273771, by rfl⟩ : syracuseStep 730057 = 547543) (by norm_num)
theorem B730093 : Blo 646304 730093 := bbase (se 3 (by rfl) ⟨136892, by rfl⟩ : syracuseStep 730093 = 273785) (by norm_num)
theorem B730129 : Blo 646304 730129 := bbase (se 2 (by rfl) ⟨273798, by rfl⟩ : syracuseStep 730129 = 547597) (by norm_num)
theorem B1385525 : Blo 646304 1385525 := bbase (se 5 (by rfl) ⟨64946, by rfl⟩ : syracuseStep 1385525 = 129893) (by norm_num)
theorem B730165 : Blo 646304 730165 := bbase (se 5 (by rfl) ⟨34226, by rfl⟩ : syracuseStep 730165 = 68453) (by norm_num)
theorem B1385533 : Blo 646304 1385533 := bbase (se 3 (by rfl) ⟨259787, by rfl⟩ : syracuseStep 1385533 = 519575) (by norm_num)
theorem B730201 : Blo 646304 730201 := bbase (se 2 (by rfl) ⟨273825, by rfl⟩ : syracuseStep 730201 = 547651) (by norm_num)
theorem B1090685 : Blo 646304 1090685 := bbase (se 3 (by rfl) ⟨204503, by rfl⟩ : syracuseStep 1090685 = 409007) (by norm_num)
theorem B730237 : Blo 646304 730237 := bbase (se 3 (by rfl) ⟨136919, by rfl⟩ : syracuseStep 730237 = 273839) (by norm_num)
theorem B730273 : Blo 646304 730273 := bbase (se 2 (by rfl) ⟨273852, by rfl⟩ : syracuseStep 730273 = 547705) (by norm_num)
theorem B730309 : Blo 646304 730309 := bbase (se 4 (by rfl) ⟨68466, by rfl⟩ : syracuseStep 730309 = 136933) (by norm_num)
theorem B730345 : Blo 646304 730345 := bbase (se 2 (by rfl) ⟨273879, by rfl⟩ : syracuseStep 730345 = 547759) (by norm_num)
theorem B1090813 : Blo 646304 1090813 := bbase (se 3 (by rfl) ⟨204527, by rfl⟩ : syracuseStep 1090813 = 409055) (by norm_num)
theorem B730381 : Blo 646304 730381 := bbase (se 3 (by rfl) ⟨136946, by rfl⟩ : syracuseStep 730381 = 273893) (by norm_num)
theorem B730417 : Blo 646304 730417 := bbase (se 2 (by rfl) ⟨273906, by rfl⟩ : syracuseStep 730417 = 547813) (by norm_num)
theorem B1090901 : Blo 646304 1090901 := bbase (se 12 (by rfl) ⟨399, by rfl⟩ : syracuseStep 1090901 = 799) (by norm_num)
theorem B730453 : Blo 646304 730453 := bbase (se 12 (by rfl) ⟨267, by rfl⟩ : syracuseStep 730453 = 535) (by norm_num)
theorem B730489 : Blo 646304 730489 := bbase (se 2 (by rfl) ⟨273933, by rfl⟩ : syracuseStep 730489 = 547867) (by norm_num)
theorem B730525 : Blo 646304 730525 := bbase (se 3 (by rfl) ⟨136973, by rfl⟩ : syracuseStep 730525 = 273947) (by norm_num)
theorem B730561 : Blo 646304 730561 := bbase (se 2 (by rfl) ⟨273960, by rfl⟩ : syracuseStep 730561 = 547921) (by norm_num)
theorem B959941 : Blo 646304 959941 := bbase (se 4 (by rfl) ⟨89994, by rfl⟩ : syracuseStep 959941 = 179989) (by norm_num)
theorem B1091029 : Blo 646304 1091029 := bbase (se 7 (by rfl) ⟨12785, by rfl⟩ : syracuseStep 1091029 = 25571) (by norm_num)
theorem B730597 : Blo 646304 730597 := bbase (se 4 (by rfl) ⟨68493, by rfl⟩ : syracuseStep 730597 = 136987) (by norm_num)
theorem B730633 : Blo 646304 730633 := bbase (se 2 (by rfl) ⟨273987, by rfl⟩ : syracuseStep 730633 = 547975) (by norm_num)
theorem B1123877 : Blo 646304 1123877 := bbase (se 4 (by rfl) ⟨105363, by rfl⟩ : syracuseStep 1123877 = 210727) (by norm_num)
theorem B1091117 : Blo 646304 1091117 := bbase (se 3 (by rfl) ⟨204584, by rfl⟩ : syracuseStep 1091117 = 409169) (by norm_num)
theorem B730669 : Blo 646304 730669 := bbase (se 3 (by rfl) ⟨137000, by rfl⟩ : syracuseStep 730669 = 274001) (by norm_num)
theorem B730705 : Blo 646304 730705 := bbase (se 2 (by rfl) ⟨274014, by rfl⟩ : syracuseStep 730705 = 548029) (by norm_num)
theorem B730741 : Blo 646304 730741 := bbase (se 5 (by rfl) ⟨34253, by rfl⟩ : syracuseStep 730741 = 68507) (by norm_num)
theorem B730777 : Blo 646304 730777 := bbase (se 2 (by rfl) ⟨274041, by rfl⟩ : syracuseStep 730777 = 548083) (by norm_num)
theorem B1091245 : Blo 646304 1091245 := bbase (se 3 (by rfl) ⟨204608, by rfl⟩ : syracuseStep 1091245 = 409217) (by norm_num)
theorem B730813 : Blo 646304 730813 := bbase (se 3 (by rfl) ⟨137027, by rfl⟩ : syracuseStep 730813 = 274055) (by norm_num)
theorem B730849 : Blo 646304 730849 := bbase (se 2 (by rfl) ⟨274068, by rfl⟩ : syracuseStep 730849 = 548137) (by norm_num)
theorem B1419005 : Blo 646304 1419005 := bbase (se 3 (by rfl) ⟨266063, by rfl⟩ : syracuseStep 1419005 = 532127) (by norm_num)
theorem B1091333 : Blo 646304 1091333 := bbase (se 4 (by rfl) ⟨102312, by rfl⟩ : syracuseStep 1091333 = 204625) (by norm_num)
theorem B730885 : Blo 646304 730885 := bbase (se 4 (by rfl) ⟨68520, by rfl⟩ : syracuseStep 730885 = 137041) (by norm_num)
theorem B730921 : Blo 646304 730921 := bbase (se 2 (by rfl) ⟨274095, by rfl⟩ : syracuseStep 730921 = 548191) (by norm_num)
theorem B730957 : Blo 646304 730957 := bbase (se 3 (by rfl) ⟨137054, by rfl⟩ : syracuseStep 730957 = 274109) (by norm_num)
theorem B730993 : Blo 646304 730993 := bbase (se 2 (by rfl) ⟨274122, by rfl⟩ : syracuseStep 730993 = 548245) (by norm_num)
theorem B1091461 : Blo 646304 1091461 := bbase (se 4 (by rfl) ⟨102324, by rfl⟩ : syracuseStep 1091461 = 204649) (by norm_num)
theorem B829325 : Blo 646304 829325 := bbase (se 3 (by rfl) ⟨155498, by rfl⟩ : syracuseStep 829325 = 310997) (by norm_num)
theorem B731029 : Blo 646304 731029 := bbase (se 6 (by rfl) ⟨17133, by rfl⟩ : syracuseStep 731029 = 34267) (by norm_num)
theorem B731065 : Blo 646304 731065 := bbase (se 2 (by rfl) ⟨274149, by rfl⟩ : syracuseStep 731065 = 548299) (by norm_num)
theorem B1091549 : Blo 646304 1091549 := bbase (se 3 (by rfl) ⟨204665, by rfl⟩ : syracuseStep 1091549 = 409331) (by norm_num)
theorem B731101 : Blo 646304 731101 := bbase (se 3 (by rfl) ⟨137081, by rfl⟩ : syracuseStep 731101 = 274163) (by norm_num)
theorem B1583101 : Blo 646304 1583101 := bbase (se 3 (by rfl) ⟨296831, by rfl⟩ : syracuseStep 1583101 = 593663) (by norm_num)
theorem B731137 : Blo 646304 731137 := bbase (se 2 (by rfl) ⟨274176, by rfl⟩ : syracuseStep 731137 = 548353) (by norm_num)
theorem B731173 : Blo 646304 731173 := bbase (se 4 (by rfl) ⟨68547, by rfl⟩ : syracuseStep 731173 = 137095) (by norm_num)
theorem B731209 : Blo 646304 731209 := bbase (se 2 (by rfl) ⟨274203, by rfl⟩ : syracuseStep 731209 = 548407) (by norm_num)
theorem B1091677 : Blo 646304 1091677 := bbase (se 3 (by rfl) ⟨204689, by rfl⟩ : syracuseStep 1091677 = 409379) (by norm_num)
theorem B3287141 : Blo 646304 3287141 := bbase (se 4 (by rfl) ⟨308169, by rfl⟩ : syracuseStep 3287141 = 616339) (by norm_num)
theorem B731245 : Blo 646304 731245 := bbase (se 3 (by rfl) ⟨137108, by rfl⟩ : syracuseStep 731245 = 274217) (by norm_num)
theorem B731281 : Blo 646304 731281 := bbase (se 2 (by rfl) ⟨274230, by rfl⟩ : syracuseStep 731281 = 548461) (by norm_num)
theorem B1386661 : Blo 646304 1386661 := bbase (se 4 (by rfl) ⟨129999, by rfl⟩ : syracuseStep 1386661 = 259999) (by norm_num)
theorem B1091765 : Blo 646304 1091765 := bbase (se 5 (by rfl) ⟨51176, by rfl⟩ : syracuseStep 1091765 = 102353) (by norm_num)
theorem B731317 : Blo 646304 731317 := bbase (se 5 (by rfl) ⟨34280, by rfl⟩ : syracuseStep 731317 = 68561) (by norm_num)
theorem B731353 : Blo 646304 731353 := bbase (se 2 (by rfl) ⟨274257, by rfl⟩ : syracuseStep 731353 = 548515) (by norm_num)
theorem B731389 : Blo 646304 731389 := bbase (se 3 (by rfl) ⟨137135, by rfl⟩ : syracuseStep 731389 = 274271) (by norm_num)
theorem B731425 : Blo 646304 731425 := bbase (se 2 (by rfl) ⟨274284, by rfl⟩ : syracuseStep 731425 = 548569) (by norm_num)
theorem B1091893 : Blo 646304 1091893 := bbase (se 5 (by rfl) ⟨51182, by rfl⟩ : syracuseStep 1091893 = 102365) (by norm_num)
theorem B731461 : Blo 646304 731461 := bbase (se 4 (by rfl) ⟨68574, by rfl⟩ : syracuseStep 731461 = 137149) (by norm_num)
theorem B731497 : Blo 646304 731497 := bbase (se 2 (by rfl) ⟨274311, by rfl⟩ : syracuseStep 731497 = 548623) (by norm_num)
theorem B1091981 : Blo 646304 1091981 := bbase (se 3 (by rfl) ⟨204746, by rfl⟩ : syracuseStep 1091981 = 409493) (by norm_num)
theorem B731533 : Blo 646304 731533 := bbase (se 3 (by rfl) ⟨137162, by rfl⟩ : syracuseStep 731533 = 274325) (by norm_num)
theorem B2763173 : Blo 646304 2763173 := bbase (se 4 (by rfl) ⟨259047, by rfl⟩ : syracuseStep 2763173 = 518095) (by norm_num)
theorem B731569 : Blo 646304 731569 := bbase (se 2 (by rfl) ⟨274338, by rfl⟩ : syracuseStep 731569 = 548677) (by norm_num)
theorem B1092109 : Blo 646304 1092109 := bbase (se 3 (by rfl) ⟨204770, by rfl⟩ : syracuseStep 1092109 = 409541) (by norm_num)
theorem B1387037 : Blo 646304 1387037 := bbase (se 3 (by rfl) ⟨260069, by rfl⟩ : syracuseStep 1387037 = 520139) (by norm_num)
theorem B1092197 : Blo 646304 1092197 := bbase (se 4 (by rfl) ⟨102393, by rfl⟩ : syracuseStep 1092197 = 204787) (by norm_num)
theorem B5548661 : Blo 646304 5548661 := bbase (se 5 (by rfl) ⟨260093, by rfl⟩ : syracuseStep 5548661 = 520187) (by norm_num)
theorem B2468501 : Blo 646304 2468501 := bbase (se 6 (by rfl) ⟨57855, by rfl⟩ : syracuseStep 2468501 = 115711) (by norm_num)
theorem B830125 : Blo 646304 830125 := bbase (se 3 (by rfl) ⟨155648, by rfl⟩ : syracuseStep 830125 = 311297) (by norm_num)
theorem B1092325 : Blo 646304 1092325 := bbase (se 4 (by rfl) ⟨102405, by rfl⟩ : syracuseStep 1092325 = 204811) (by norm_num)
theorem B2075429 : Blo 646304 2075429 := bbase (se 4 (by rfl) ⟨194571, by rfl⟩ : syracuseStep 2075429 = 389143) (by norm_num)
theorem B2960165 : Blo 646304 2960165 := bbase (se 4 (by rfl) ⟨277515, by rfl⟩ : syracuseStep 2960165 = 555031) (by norm_num)
theorem B1092413 : Blo 646304 1092413 := bbase (se 3 (by rfl) ⟨204827, by rfl⟩ : syracuseStep 1092413 = 409655) (by norm_num)
theorem B2960293 : Blo 646304 2960293 := bbase (se 4 (by rfl) ⟨277527, by rfl⟩ : syracuseStep 2960293 = 555055) (by norm_num)
theorem B2468789 : Blo 646304 2468789 := bbase (se 5 (by rfl) ⟨115724, by rfl⟩ : syracuseStep 2468789 = 231449) (by norm_num)
theorem B1092541 : Blo 646304 1092541 := bbase (se 3 (by rfl) ⟨204851, by rfl⟩ : syracuseStep 1092541 = 409703) (by norm_num)
theorem B1092629 : Blo 646304 1092629 := bbase (se 6 (by rfl) ⟨25608, by rfl⟩ : syracuseStep 1092629 = 51217) (by norm_num)
theorem B4926581 : Blo 646304 4926581 := bbase (se 5 (by rfl) ⟨230933, by rfl⟩ : syracuseStep 4926581 = 461867) (by norm_num)
theorem B1092757 : Blo 646304 1092757 := bbase (se 6 (by rfl) ⟨25611, by rfl⟩ : syracuseStep 1092757 = 51223) (by norm_num)
theorem B1846421 : Blo 646304 1846421 := bbase (se 6 (by rfl) ⟨43275, by rfl⟩ : syracuseStep 1846421 = 86551) (by norm_num)
theorem B1092845 : Blo 646304 1092845 := bbase (se 3 (by rfl) ⟨204908, by rfl⟩ : syracuseStep 1092845 = 409817) (by norm_num)
theorem B1092973 : Blo 646304 1092973 := bbase (se 3 (by rfl) ⟨204932, by rfl⟩ : syracuseStep 1092973 = 409865) (by norm_num)
theorem B3288437 : Blo 646304 3288437 := bbase (se 5 (by rfl) ⟨154145, by rfl⟩ : syracuseStep 3288437 = 308291) (by norm_num)
theorem B2633141 : Blo 646304 2633141 := bbase (se 5 (by rfl) ⟨123428, by rfl⟩ : syracuseStep 2633141 = 246857) (by norm_num)
theorem B1093061 : Blo 646304 1093061 := bbase (se 4 (by rfl) ⟨102474, by rfl⟩ : syracuseStep 1093061 = 204949) (by norm_num)
theorem B1093189 : Blo 646304 1093189 := bbase (se 4 (by rfl) ⟨102486, by rfl⟩ : syracuseStep 1093189 = 204973) (by norm_num)
theorem B1093277 : Blo 646304 1093277 := bbase (se 3 (by rfl) ⟨204989, by rfl⟩ : syracuseStep 1093277 = 409979) (by norm_num)
theorem B1683149 : Blo 646304 1683149 := bbase (se 3 (by rfl) ⟨315590, by rfl⟩ : syracuseStep 1683149 = 631181) (by norm_num)
theorem B4665077 : Blo 646304 4665077 := bbase (se 5 (by rfl) ⟨218675, by rfl⟩ : syracuseStep 4665077 = 437351) (by norm_num)
theorem B1093405 : Blo 646304 1093405 := bbase (se 3 (by rfl) ⟨205013, by rfl⟩ : syracuseStep 1093405 = 410027) (by norm_num)
theorem B1093493 : Blo 646304 1093493 := bbase (se 5 (by rfl) ⟨51257, by rfl⟩ : syracuseStep 1093493 = 102515) (by norm_num)
theorem B1093621 : Blo 646304 1093621 := bbase (se 5 (by rfl) ⟨51263, by rfl⟩ : syracuseStep 1093621 = 102527) (by norm_num)
theorem B1093709 : Blo 646304 1093709 := bbase (se 3 (by rfl) ⟨205070, by rfl⟩ : syracuseStep 1093709 = 410141) (by norm_num)
theorem B1388677 : Blo 646304 1388677 := bbase (se 4 (by rfl) ⟨130188, by rfl⟩ : syracuseStep 1388677 = 260377) (by norm_num)
theorem B1454237 : Blo 646304 1454237 := bbase (se 3 (by rfl) ⟨272669, by rfl⟩ : syracuseStep 1454237 = 545339) (by norm_num)
theorem B2076853 : Blo 646304 2076853 := bbase (se 5 (by rfl) ⟨97352, by rfl⟩ : syracuseStep 2076853 = 194705) (by norm_num)
theorem B1093837 : Blo 646304 1093837 := bbase (se 3 (by rfl) ⟨205094, by rfl⟩ : syracuseStep 1093837 = 410189) (by norm_num)
theorem B1454309 : Blo 646304 1454309 := bbase (se 4 (by rfl) ⟨136341, by rfl⟩ : syracuseStep 1454309 = 272683) (by norm_num)
theorem B1093925 : Blo 646304 1093925 := bbase (se 4 (by rfl) ⟨102555, by rfl⟩ : syracuseStep 1093925 = 205111) (by norm_num)
theorem B1454381 : Blo 646304 1454381 := bbase (se 3 (by rfl) ⟨272696, by rfl⟩ : syracuseStep 1454381 = 545393) (by norm_num)
theorem B1847605 : Blo 646304 1847605 := bbase (se 5 (by rfl) ⟨86606, by rfl⟩ : syracuseStep 1847605 = 173213) (by norm_num)
theorem B1454453 : Blo 646304 1454453 := bbase (se 5 (by rfl) ⟨68177, by rfl⟩ : syracuseStep 1454453 = 136355) (by norm_num)
theorem B1094053 : Blo 646304 1094053 := bbase (se 4 (by rfl) ⟨102567, by rfl⟩ : syracuseStep 1094053 = 205135) (by norm_num)
theorem B668089 : Blo 646304 668089 := bbase (se 2 (by rfl) ⟨250533, by rfl⟩ : syracuseStep 668089 = 501067) (by norm_num)
theorem B1454525 : Blo 646304 1454525 := bbase (se 3 (by rfl) ⟨272723, by rfl⟩ : syracuseStep 1454525 = 545447) (by norm_num)
theorem B1847765 : Blo 646304 1847765 := bbase (se 7 (by rfl) ⟨21653, by rfl⟩ : syracuseStep 1847765 = 43307) (by norm_num)
theorem B831973 : Blo 646304 831973 := bbase (se 4 (by rfl) ⟨77997, by rfl⟩ : syracuseStep 831973 = 155995) (by norm_num)
theorem B1094141 : Blo 646304 1094141 := bbase (se 3 (by rfl) ⟨205151, by rfl⟩ : syracuseStep 1094141 = 410303) (by norm_num)
theorem B1454597 : Blo 646304 1454597 := bbase (se 4 (by rfl) ⟨136368, by rfl⟩ : syracuseStep 1454597 = 272737) (by norm_num)
theorem B1454669 : Blo 646304 1454669 := bbase (se 3 (by rfl) ⟨272750, by rfl⟩ : syracuseStep 1454669 = 545501) (by norm_num)
theorem B2077301 : Blo 646304 2077301 := bbase (se 5 (by rfl) ⟨97373, by rfl⟩ : syracuseStep 2077301 = 194747) (by norm_num)
theorem B1094269 : Blo 646304 1094269 := bbase (se 3 (by rfl) ⟨205175, by rfl⟩ : syracuseStep 1094269 = 410351) (by norm_num)
theorem B3289733 : Blo 646304 3289733 := bbase (se 4 (by rfl) ⟨308412, by rfl⟩ : syracuseStep 3289733 = 616825) (by norm_num)
theorem B1454741 : Blo 646304 1454741 := bbase (se 6 (by rfl) ⟨34095, by rfl⟩ : syracuseStep 1454741 = 68191) (by norm_num)
theorem B1848005 : Blo 646304 1848005 := bbase (se 4 (by rfl) ⟨173250, by rfl⟩ : syracuseStep 1848005 = 346501) (by norm_num)
theorem B1094357 : Blo 646304 1094357 := bbase (se 7 (by rfl) ⟨12824, by rfl⟩ : syracuseStep 1094357 = 25649) (by norm_num)
theorem B1454813 : Blo 646304 1454813 := bbase (se 3 (by rfl) ⟨272777, by rfl⟩ : syracuseStep 1454813 = 545555) (by norm_num)
theorem B4141813 : Blo 646304 4141813 := bbase (se 5 (by rfl) ⟨194147, by rfl⟩ : syracuseStep 4141813 = 388295) (by norm_num)
theorem B1454885 : Blo 646304 1454885 := bbase (se 4 (by rfl) ⟨136395, by rfl⟩ : syracuseStep 1454885 = 272791) (by norm_num)
theorem B1094485 : Blo 646304 1094485 := bbase (se 9 (by rfl) ⟨3206, by rfl⟩ : syracuseStep 1094485 = 6413) (by norm_num)
theorem B1454957 : Blo 646304 1454957 := bbase (se 3 (by rfl) ⟨272804, by rfl⟩ : syracuseStep 1454957 = 545609) (by norm_num)
theorem B1848197 : Blo 646304 1848197 := bbase (se 4 (by rfl) ⟨173268, by rfl⟩ : syracuseStep 1848197 = 346537) (by norm_num)
theorem B1094573 : Blo 646304 1094573 := bbase (se 3 (by rfl) ⟨205232, by rfl⟩ : syracuseStep 1094573 = 410465) (by norm_num)
theorem B1455029 : Blo 646304 1455029 := bbase (se 5 (by rfl) ⟨68204, by rfl⟩ : syracuseStep 1455029 = 136409) (by norm_num)
theorem B1455101 : Blo 646304 1455101 := bbase (se 3 (by rfl) ⟨272831, by rfl⟩ : syracuseStep 1455101 = 545663) (by norm_num)
theorem B1094701 : Blo 646304 1094701 := bbase (se 3 (by rfl) ⟨205256, by rfl⟩ : syracuseStep 1094701 = 410513) (by norm_num)
theorem B1455173 : Blo 646304 1455173 := bbase (se 4 (by rfl) ⟨136422, by rfl⟩ : syracuseStep 1455173 = 272845) (by norm_num)
theorem B1094789 : Blo 646304 1094789 := bbase (se 4 (by rfl) ⟨102636, by rfl⟩ : syracuseStep 1094789 = 205273) (by norm_num)
theorem B1455245 : Blo 646304 1455245 := bbase (se 3 (by rfl) ⟨272858, by rfl⟩ : syracuseStep 1455245 = 545717) (by norm_num)
theorem B3159205 : Blo 646304 3159205 := bbase (se 4 (by rfl) ⟨296175, by rfl⟩ : syracuseStep 3159205 = 592351) (by norm_num)
theorem B1455317 : Blo 646304 1455317 := bbase (se 7 (by rfl) ⟨17054, by rfl⟩ : syracuseStep 1455317 = 34109) (by norm_num)
theorem B4568309 : Blo 646304 4568309 := bbase (se 5 (by rfl) ⟨214139, by rfl⟩ : syracuseStep 4568309 = 428279) (by norm_num)
theorem B1094917 : Blo 646304 1094917 := bbase (se 4 (by rfl) ⟨102648, by rfl⟩ : syracuseStep 1094917 = 205297) (by norm_num)
theorem B1455389 : Blo 646304 1455389 := bbase (se 3 (by rfl) ⟨272885, by rfl⟩ : syracuseStep 1455389 = 545771) (by norm_num)
theorem B1095005 : Blo 646304 1095005 := bbase (se 3 (by rfl) ⟨205313, by rfl⟩ : syracuseStep 1095005 = 410627) (by norm_num)
theorem B1455461 : Blo 646304 1455461 := bbase (se 4 (by rfl) ⟨136449, by rfl⟩ : syracuseStep 1455461 = 272899) (by norm_num)
theorem B1455533 : Blo 646304 1455533 := bbase (se 3 (by rfl) ⟨272912, by rfl⟩ : syracuseStep 1455533 = 545825) (by norm_num)
theorem B1095133 : Blo 646304 1095133 := bbase (se 3 (by rfl) ⟨205337, by rfl⟩ : syracuseStep 1095133 = 410675) (by norm_num)
theorem B833009 : Blo 646304 833009 := bbase (se 2 (by rfl) ⟨312378, by rfl⟩ : syracuseStep 833009 = 624757) (by norm_num)
theorem B1455605 : Blo 646304 1455605 := bbase (se 5 (by rfl) ⟨68231, by rfl⟩ : syracuseStep 1455605 = 136463) (by norm_num)
theorem B1095221 : Blo 646304 1095221 := bbase (se 5 (by rfl) ⟨51338, by rfl⟩ : syracuseStep 1095221 = 102677) (by norm_num)
theorem B1455677 : Blo 646304 1455677 := bbase (se 3 (by rfl) ⟨272939, by rfl⟩ : syracuseStep 1455677 = 545879) (by norm_num)
theorem B1455749 : Blo 646304 1455749 := bbase (se 4 (by rfl) ⟨136476, by rfl⟩ : syracuseStep 1455749 = 272953) (by norm_num)
theorem B1095349 : Blo 646304 1095349 := bbase (se 5 (by rfl) ⟨51344, by rfl⟩ : syracuseStep 1095349 = 102689) (by norm_num)
theorem B1455821 : Blo 646304 1455821 := bbase (se 3 (by rfl) ⟨272966, by rfl⟩ : syracuseStep 1455821 = 545933) (by norm_num)
theorem B1095437 : Blo 646304 1095437 := bbase (se 3 (by rfl) ⟨205394, by rfl⟩ : syracuseStep 1095437 = 410789) (by norm_num)
theorem B1455893 : Blo 646304 1455893 := bbase (se 6 (by rfl) ⟨34122, by rfl⟩ : syracuseStep 1455893 = 68245) (by norm_num)
theorem B2635541 : Blo 646304 2635541 := bbase (se 6 (by rfl) ⟨61770, by rfl⟩ : syracuseStep 2635541 = 123541) (by norm_num)
theorem B1455965 : Blo 646304 1455965 := bbase (se 3 (by rfl) ⟨272993, by rfl⟩ : syracuseStep 1455965 = 545987) (by norm_num)
theorem B1849189 : Blo 646304 1849189 := bbase (se 4 (by rfl) ⟨173361, by rfl⟩ : syracuseStep 1849189 = 346723) (by norm_num)
theorem B1095565 : Blo 646304 1095565 := bbase (se 3 (by rfl) ⟨205418, by rfl⟩ : syracuseStep 1095565 = 410837) (by norm_num)
theorem B2635669 : Blo 646304 2635669 := bbase (se 6 (by rfl) ⟨61773, by rfl⟩ : syracuseStep 2635669 = 123547) (by norm_num)
theorem B3291029 : Blo 646304 3291029 := bbase (se 6 (by rfl) ⟨77133, by rfl⟩ : syracuseStep 3291029 = 154267) (by norm_num)
theorem B1456037 : Blo 646304 1456037 := bbase (se 4 (by rfl) ⟨136503, by rfl⟩ : syracuseStep 1456037 = 273007) (by norm_num)
theorem B1095653 : Blo 646304 1095653 := bbase (se 4 (by rfl) ⟨102717, by rfl⟩ : syracuseStep 1095653 = 205435) (by norm_num)
theorem B1456109 : Blo 646304 1456109 := bbase (se 3 (by rfl) ⟨273020, by rfl⟩ : syracuseStep 1456109 = 546041) (by norm_num)
theorem B1456181 : Blo 646304 1456181 := bbase (se 5 (by rfl) ⟨68258, by rfl⟩ : syracuseStep 1456181 = 136517) (by norm_num)
theorem B1095781 : Blo 646304 1095781 := bbase (se 4 (by rfl) ⟨102729, by rfl⟩ : syracuseStep 1095781 = 205459) (by norm_num)
theorem B1456253 : Blo 646304 1456253 := bbase (se 3 (by rfl) ⟨273047, by rfl⟩ : syracuseStep 1456253 = 546095) (by norm_num)
theorem B1554565 : Blo 646304 1554565 := bbase (se 4 (by rfl) ⟨145740, by rfl⟩ : syracuseStep 1554565 = 291481) (by norm_num)
theorem B1095869 : Blo 646304 1095869 := bbase (se 3 (by rfl) ⟨205475, by rfl⟩ : syracuseStep 1095869 = 410951) (by norm_num)
theorem B1456325 : Blo 646304 1456325 := bbase (se 4 (by rfl) ⟨136530, by rfl⟩ : syracuseStep 1456325 = 273061) (by norm_num)
theorem B1456397 : Blo 646304 1456397 := bbase (se 3 (by rfl) ⟨273074, by rfl⟩ : syracuseStep 1456397 = 546149) (by norm_num)
theorem B1095997 : Blo 646304 1095997 := bbase (se 3 (by rfl) ⟨205499, by rfl⟩ : syracuseStep 1095997 = 410999) (by norm_num)
theorem B1456469 : Blo 646304 1456469 := bbase (se 10 (by rfl) ⟨2133, by rfl⟩ : syracuseStep 1456469 = 4267) (by norm_num)
theorem B1096085 : Blo 646304 1096085 := bbase (se 6 (by rfl) ⟨25689, by rfl⟩ : syracuseStep 1096085 = 51379) (by norm_num)
theorem B1456541 : Blo 646304 1456541 := bbase (se 3 (by rfl) ⟨273101, by rfl⟩ : syracuseStep 1456541 = 546203) (by norm_num)
theorem B1456613 : Blo 646304 1456613 := bbase (se 4 (by rfl) ⟨136557, by rfl⟩ : syracuseStep 1456613 = 273115) (by norm_num)
theorem B1096213 : Blo 646304 1096213 := bbase (se 6 (by rfl) ⟨25692, by rfl⟩ : syracuseStep 1096213 = 51385) (by norm_num)
theorem B1456685 : Blo 646304 1456685 := bbase (se 3 (by rfl) ⟨273128, by rfl⟩ : syracuseStep 1456685 = 546257) (by norm_num)
theorem B1227325 : Blo 646304 1227325 := bbase (se 3 (by rfl) ⟨230123, by rfl⟩ : syracuseStep 1227325 = 460247) (by norm_num)
theorem B2767445 : Blo 646304 2767445 := bbase (se 8 (by rfl) ⟨16215, by rfl⟩ : syracuseStep 2767445 = 32431) (by norm_num)
theorem B2374229 : Blo 646304 2374229 := bbase (se 8 (by rfl) ⟨13911, by rfl⟩ : syracuseStep 2374229 = 27823) (by norm_num)
theorem B703085 : Blo 646304 703085 := bbase (se 3 (by rfl) ⟨131828, by rfl⟩ : syracuseStep 703085 = 263657) (by norm_num)
theorem B1096301 : Blo 646304 1096301 := bbase (se 3 (by rfl) ⟨205556, by rfl⟩ : syracuseStep 1096301 = 411113) (by norm_num)
theorem B1456757 : Blo 646304 1456757 := bbase (se 5 (by rfl) ⟨68285, by rfl⟩ : syracuseStep 1456757 = 136571) (by norm_num)
theorem B2341493 : Blo 646304 2341493 := bbase (se 5 (by rfl) ⟨109757, by rfl⟩ : syracuseStep 2341493 = 219515) (by norm_num)
theorem B1456829 : Blo 646304 1456829 := bbase (se 3 (by rfl) ⟨273155, by rfl⟩ : syracuseStep 1456829 = 546311) (by norm_num)
theorem B1227469 : Blo 646304 1227469 := bbase (se 3 (by rfl) ⟨230150, by rfl⟩ : syracuseStep 1227469 = 460301) (by norm_num)
theorem B1096429 : Blo 646304 1096429 := bbase (se 3 (by rfl) ⟨205580, by rfl⟩ : syracuseStep 1096429 = 411161) (by norm_num)
theorem B1456901 : Blo 646304 1456901 := bbase (se 4 (by rfl) ⟨136584, by rfl⟩ : syracuseStep 1456901 = 273169) (by norm_num)
theorem B2079557 : Blo 646304 2079557 := bbase (se 4 (by rfl) ⟨194958, by rfl⟩ : syracuseStep 2079557 = 389917) (by norm_num)
theorem B1096517 : Blo 646304 1096517 := bbase (se 4 (by rfl) ⟨102798, by rfl⟩ : syracuseStep 1096517 = 205597) (by norm_num)
theorem B1456973 : Blo 646304 1456973 := bbase (se 3 (by rfl) ⟨273182, by rfl⟩ : syracuseStep 1456973 = 546365) (by norm_num)
theorem B1227629 : Blo 646304 1227629 := bbase (se 3 (by rfl) ⟨230180, by rfl⟩ : syracuseStep 1227629 = 460361) (by norm_num)
theorem B1457045 : Blo 646304 1457045 := bbase (se 6 (by rfl) ⟨34149, by rfl⟩ : syracuseStep 1457045 = 68299) (by norm_num)
theorem B1850293 : Blo 646304 1850293 := bbase (se 5 (by rfl) ⟨86732, by rfl⟩ : syracuseStep 1850293 = 173465) (by norm_num)
theorem B1096645 : Blo 646304 1096645 := bbase (se 4 (by rfl) ⟨102810, by rfl⟩ : syracuseStep 1096645 = 205621) (by norm_num)
theorem B1457117 : Blo 646304 1457117 := bbase (se 3 (by rfl) ⟨273209, by rfl⟩ : syracuseStep 1457117 = 546419) (by norm_num)
theorem B1227773 : Blo 646304 1227773 := bbase (se 3 (by rfl) ⟨230207, by rfl⟩ : syracuseStep 1227773 = 460415) (by norm_num)
theorem B1096733 : Blo 646304 1096733 := bbase (se 3 (by rfl) ⟨205637, by rfl⟩ : syracuseStep 1096733 = 411275) (by norm_num)
theorem B1457189 : Blo 646304 1457189 := bbase (se 4 (by rfl) ⟨136611, by rfl⟩ : syracuseStep 1457189 = 273223) (by norm_num)
theorem B1457261 : Blo 646304 1457261 := bbase (se 3 (by rfl) ⟨273236, by rfl⟩ : syracuseStep 1457261 = 546473) (by norm_num)
theorem B1096861 : Blo 646304 1096861 := bbase (se 3 (by rfl) ⟨205661, by rfl⟩ : syracuseStep 1096861 = 411323) (by norm_num)
theorem B1457333 : Blo 646304 1457333 := bbase (se 5 (by rfl) ⟨68312, by rfl⟩ : syracuseStep 1457333 = 136625) (by norm_num)
theorem B1752293 : Blo 646304 1752293 := bbase (se 4 (by rfl) ⟨164277, by rfl⟩ : syracuseStep 1752293 = 328555) (by norm_num)
theorem B1096949 : Blo 646304 1096949 := bbase (se 5 (by rfl) ⟨51419, by rfl⟩ : syracuseStep 1096949 = 102839) (by norm_num)
theorem B1457405 : Blo 646304 1457405 := bbase (se 3 (by rfl) ⟨273263, by rfl⟩ : syracuseStep 1457405 = 546527) (by norm_num)
theorem B1228061 : Blo 646304 1228061 := bbase (se 3 (by rfl) ⟨230261, by rfl⟩ : syracuseStep 1228061 = 460523) (by norm_num)
theorem B1457477 : Blo 646304 1457477 := bbase (se 4 (by rfl) ⟨136638, by rfl⟩ : syracuseStep 1457477 = 273277) (by norm_num)
theorem B1097077 : Blo 646304 1097077 := bbase (se 5 (by rfl) ⟨51425, by rfl⟩ : syracuseStep 1097077 = 102851) (by norm_num)
theorem B1457549 : Blo 646304 1457549 := bbase (se 3 (by rfl) ⟨273290, by rfl⟩ : syracuseStep 1457549 = 546581) (by norm_num)
theorem B1228213 : Blo 646304 1228213 := bbase (se 5 (by rfl) ⟨57572, by rfl⟩ : syracuseStep 1228213 = 115145) (by norm_num)
theorem B1097165 : Blo 646304 1097165 := bbase (se 3 (by rfl) ⟨205718, by rfl⟩ : syracuseStep 1097165 = 411437) (by norm_num)
theorem B1457621 : Blo 646304 1457621 := bbase (se 7 (by rfl) ⟨17081, by rfl⟩ : syracuseStep 1457621 = 34163) (by norm_num)
theorem B1555949 : Blo 646304 1555949 := bbase (se 3 (by rfl) ⟨291740, by rfl⟩ : syracuseStep 1555949 = 583481) (by norm_num)
theorem B1555957 : Blo 646304 1555957 := bbase (se 5 (by rfl) ⟨72935, by rfl⟩ : syracuseStep 1555957 = 145871) (by norm_num)
theorem B1457693 : Blo 646304 1457693 := bbase (se 3 (by rfl) ⟨273317, by rfl⟩ : syracuseStep 1457693 = 546635) (by norm_num)
theorem B2211365 : Blo 646304 2211365 := bbase (se 4 (by rfl) ⟨207315, by rfl⟩ : syracuseStep 2211365 = 414631) (by norm_num)
theorem B1097293 : Blo 646304 1097293 := bbase (se 3 (by rfl) ⟨205742, by rfl⟩ : syracuseStep 1097293 = 411485) (by norm_num)
theorem B1457765 : Blo 646304 1457765 := bbase (se 4 (by rfl) ⟨136665, by rfl⟩ : syracuseStep 1457765 = 273331) (by norm_num)
theorem B1097381 : Blo 646304 1097381 := bbase (se 4 (by rfl) ⟨102879, by rfl⟩ : syracuseStep 1097381 = 205759) (by norm_num)
theorem B1457837 : Blo 646304 1457837 := bbase (se 3 (by rfl) ⟨273344, by rfl⟩ : syracuseStep 1457837 = 546689) (by norm_num)
theorem B1228517 : Blo 646304 1228517 := bbase (se 4 (by rfl) ⟨115173, by rfl⟩ : syracuseStep 1228517 = 230347) (by norm_num)
theorem B1457909 : Blo 646304 1457909 := bbase (se 5 (by rfl) ⟨68339, by rfl⟩ : syracuseStep 1457909 = 136679) (by norm_num)
theorem B2801429 : Blo 646304 2801429 := bbase (se 6 (by rfl) ⟨65658, by rfl⟩ : syracuseStep 2801429 = 131317) (by norm_num)
theorem B1457981 : Blo 646304 1457981 := bbase (se 3 (by rfl) ⟨273371, by rfl⟩ : syracuseStep 1457981 = 546743) (by norm_num)
theorem B1458053 : Blo 646304 1458053 := bbase (se 4 (by rfl) ⟨136692, by rfl⟩ : syracuseStep 1458053 = 273385) (by norm_num)
theorem B1458125 : Blo 646304 1458125 := bbase (se 3 (by rfl) ⟨273398, by rfl⟩ : syracuseStep 1458125 = 546797) (by norm_num)
theorem B1458197 : Blo 646304 1458197 := bbase (se 6 (by rfl) ⟨34176, by rfl⟩ : syracuseStep 1458197 = 68353) (by norm_num)
theorem B1458269 : Blo 646304 1458269 := bbase (se 3 (by rfl) ⟨273425, by rfl⟩ : syracuseStep 1458269 = 546851) (by norm_num)
theorem B1458341 : Blo 646304 1458341 := bbase (se 4 (by rfl) ⟨136719, by rfl⟩ : syracuseStep 1458341 = 273439) (by norm_num)
theorem B1458413 : Blo 646304 1458413 := bbase (se 3 (by rfl) ⟨273452, by rfl⟩ : syracuseStep 1458413 = 546905) (by norm_num)
theorem B1458485 : Blo 646304 1458485 := bbase (se 5 (by rfl) ⟨68366, by rfl⟩ : syracuseStep 1458485 = 136733) (by norm_num)
theorem B2769221 : Blo 646304 2769221 := bbase (se 4 (by rfl) ⟨259614, by rfl⟩ : syracuseStep 2769221 = 519229) (by norm_num)
theorem B737633 : Blo 646304 737633 := bbase (se 2 (by rfl) ⟨276612, by rfl⟩ : syracuseStep 737633 = 553225) (by norm_num)
theorem B1458557 : Blo 646304 1458557 := bbase (se 3 (by rfl) ⟨273479, by rfl⟩ : syracuseStep 1458557 = 546959) (by norm_num)
theorem B1851797 : Blo 646304 1851797 := bbase (se 6 (by rfl) ⟨43401, by rfl⟩ : syracuseStep 1851797 = 86803) (by norm_num)
theorem B1458629 : Blo 646304 1458629 := bbase (se 4 (by rfl) ⟨136746, by rfl⟩ : syracuseStep 1458629 = 273493) (by norm_num)
theorem B1229269 : Blo 646304 1229269 := bbase (se 7 (by rfl) ⟨14405, by rfl⟩ : syracuseStep 1229269 = 28811) (by norm_num)
theorem B1556957 : Blo 646304 1556957 := bbase (se 3 (by rfl) ⟨291929, by rfl⟩ : syracuseStep 1556957 = 583859) (by norm_num)
theorem B1458701 : Blo 646304 1458701 := bbase (se 3 (by rfl) ⟨273506, by rfl⟩ : syracuseStep 1458701 = 547013) (by norm_num)
theorem B2769461 : Blo 646304 2769461 := bbase (se 5 (by rfl) ⟨129818, by rfl⟩ : syracuseStep 2769461 = 259637) (by norm_num)
theorem B1458773 : Blo 646304 1458773 := bbase (se 8 (by rfl) ⟨8547, by rfl⟩ : syracuseStep 1458773 = 17095) (by norm_num)
theorem B1229413 : Blo 646304 1229413 := bbase (se 4 (by rfl) ⟨115257, by rfl⟩ : syracuseStep 1229413 = 230515) (by norm_num)
theorem B2966149 : Blo 646304 2966149 := bbase (se 4 (by rfl) ⟨278076, by rfl⟩ : syracuseStep 2966149 = 556153) (by norm_num)
theorem B1458845 : Blo 646304 1458845 := bbase (se 3 (by rfl) ⟨273533, by rfl⟩ : syracuseStep 1458845 = 547067) (by norm_num)
theorem B1458917 : Blo 646304 1458917 := bbase (se 4 (by rfl) ⟨136773, by rfl⟩ : syracuseStep 1458917 = 273547) (by norm_num)
theorem B1229573 : Blo 646304 1229573 := bbase (se 4 (by rfl) ⟨115272, by rfl⟩ : syracuseStep 1229573 = 230545) (by norm_num)
theorem B1458989 : Blo 646304 1458989 := bbase (se 3 (by rfl) ⟨273560, by rfl⟩ : syracuseStep 1458989 = 547121) (by norm_num)
theorem B4670293 : Blo 646304 4670293 := bbase (se 9 (by rfl) ⟨13682, by rfl⟩ : syracuseStep 4670293 = 27365) (by norm_num)
theorem B1459061 : Blo 646304 1459061 := bbase (se 5 (by rfl) ⟨68393, by rfl⟩ : syracuseStep 1459061 = 136787) (by norm_num)
theorem B1229717 : Blo 646304 1229717 := bbase (se 6 (by rfl) ⟨28821, by rfl⟩ : syracuseStep 1229717 = 57643) (by norm_num)
theorem B1459133 : Blo 646304 1459133 := bbase (se 3 (by rfl) ⟨273587, by rfl⟩ : syracuseStep 1459133 = 547175) (by norm_num)
theorem B1459205 : Blo 646304 1459205 := bbase (se 4 (by rfl) ⟨136800, by rfl⟩ : syracuseStep 1459205 = 273601) (by norm_num)
theorem B1459277 : Blo 646304 1459277 := bbase (se 3 (by rfl) ⟨273614, by rfl⟩ : syracuseStep 1459277 = 547229) (by norm_num)
theorem B1459349 : Blo 646304 1459349 := bbase (se 6 (by rfl) ⟨34203, by rfl⟩ : syracuseStep 1459349 = 68407) (by norm_num)
theorem B1230005 : Blo 646304 1230005 := bbase (se 5 (by rfl) ⟨57656, by rfl⟩ : syracuseStep 1230005 = 115313) (by norm_num)
theorem B1557725 : Blo 646304 1557725 := bbase (se 3 (by rfl) ⟨292073, by rfl⟩ : syracuseStep 1557725 = 584147) (by norm_num)
theorem B1459421 : Blo 646304 1459421 := bbase (se 3 (by rfl) ⟨273641, by rfl⟩ : syracuseStep 1459421 = 547283) (by norm_num)
theorem B1459493 : Blo 646304 1459493 := bbase (se 4 (by rfl) ⟨136827, by rfl⟩ : syracuseStep 1459493 = 273655) (by norm_num)
theorem B1230157 : Blo 646304 1230157 := bbase (se 3 (by rfl) ⟨230654, by rfl⟩ : syracuseStep 1230157 = 461309) (by norm_num)
theorem B1459565 : Blo 646304 1459565 := bbase (se 3 (by rfl) ⟨273668, by rfl⟩ : syracuseStep 1459565 = 547337) (by norm_num)
theorem B1459637 : Blo 646304 1459637 := bbase (se 5 (by rfl) ⟨68420, by rfl⟩ : syracuseStep 1459637 = 136841) (by norm_num)
theorem B8898005 : Blo 646304 8898005 := bbase (se 7 (by rfl) ⟨104273, by rfl⟩ : syracuseStep 8898005 = 208547) (by norm_num)
theorem B1459709 : Blo 646304 1459709 := bbase (se 3 (by rfl) ⟨273695, by rfl⟩ : syracuseStep 1459709 = 547391) (by norm_num)
theorem B5064245 : Blo 646304 5064245 := bbase (se 5 (by rfl) ⟨237386, by rfl⟩ : syracuseStep 5064245 = 474773) (by norm_num)
theorem B1459781 : Blo 646304 1459781 := bbase (se 4 (by rfl) ⟨136854, by rfl⟩ : syracuseStep 1459781 = 273709) (by norm_num)
theorem B1230461 : Blo 646304 1230461 := bbase (se 3 (by rfl) ⟨230711, by rfl⟩ : syracuseStep 1230461 = 461423) (by norm_num)
theorem B1459853 : Blo 646304 1459853 := bbase (se 3 (by rfl) ⟨273722, by rfl⟩ : syracuseStep 1459853 = 547445) (by norm_num)
theorem B1459925 : Blo 646304 1459925 := bbase (se 7 (by rfl) ⟨17108, by rfl⟩ : syracuseStep 1459925 = 34217) (by norm_num)
theorem B1459997 : Blo 646304 1459997 := bbase (se 3 (by rfl) ⟨273749, by rfl⟩ : syracuseStep 1459997 = 547499) (by norm_num)
theorem B1001269 : Blo 646304 1001269 := bbase (se 5 (by rfl) ⟨46934, by rfl⟩ : syracuseStep 1001269 = 93869) (by norm_num)
theorem B1165117 : Blo 646304 1165117 := bbase (se 3 (by rfl) ⟨218459, by rfl⟩ : syracuseStep 1165117 = 436919) (by norm_num)
theorem B1460069 : Blo 646304 1460069 := bbase (se 4 (by rfl) ⟨136881, by rfl⟩ : syracuseStep 1460069 = 273763) (by norm_num)
theorem B1460141 : Blo 646304 1460141 := bbase (se 3 (by rfl) ⟨273776, by rfl⟩ : syracuseStep 1460141 = 547553) (by norm_num)
theorem B1460213 : Blo 646304 1460213 := bbase (se 5 (by rfl) ⟨68447, by rfl⟩ : syracuseStep 1460213 = 136895) (by norm_num)
theorem B1460285 : Blo 646304 1460285 := bbase (se 3 (by rfl) ⟨273803, by rfl⟩ : syracuseStep 1460285 = 547607) (by norm_num)
theorem B1460357 : Blo 646304 1460357 := bbase (se 4 (by rfl) ⟨136908, by rfl⟩ : syracuseStep 1460357 = 273817) (by norm_num)
theorem B1460429 : Blo 646304 1460429 := bbase (se 3 (by rfl) ⟨273830, by rfl⟩ : syracuseStep 1460429 = 547661) (by norm_num)
theorem B1460501 : Blo 646304 1460501 := bbase (se 6 (by rfl) ⟨34230, by rfl⟩ : syracuseStep 1460501 = 68461) (by norm_num)
theorem B1460573 : Blo 646304 1460573 := bbase (se 3 (by rfl) ⟨273857, by rfl⟩ : syracuseStep 1460573 = 547715) (by norm_num)
theorem B1231213 : Blo 646304 1231213 := bbase (se 3 (by rfl) ⟨230852, by rfl⟩ : syracuseStep 1231213 = 461705) (by norm_num)
theorem B1460645 : Blo 646304 1460645 := bbase (se 4 (by rfl) ⟨136935, by rfl⟩ : syracuseStep 1460645 = 273871) (by norm_num)
theorem B1460717 : Blo 646304 1460717 := bbase (se 3 (by rfl) ⟨273884, by rfl⟩ : syracuseStep 1460717 = 547769) (by norm_num)
theorem B1231357 : Blo 646304 1231357 := bbase (se 3 (by rfl) ⟨230879, by rfl⟩ : syracuseStep 1231357 = 461759) (by norm_num)
theorem B2181653 : Blo 646304 2181653 := bbase (se 6 (by rfl) ⟨51132, by rfl⟩ : syracuseStep 2181653 = 102265) (by norm_num)
theorem B1460789 : Blo 646304 1460789 := bbase (se 5 (by rfl) ⟨68474, by rfl⟩ : syracuseStep 1460789 = 136949) (by norm_num)
theorem B11061845 : Blo 646304 11061845 := bbase (se 8 (by rfl) ⟨64815, by rfl⟩ : syracuseStep 11061845 = 129631) (by norm_num)
theorem B1460861 : Blo 646304 1460861 := bbase (se 3 (by rfl) ⟨273911, by rfl⟩ : syracuseStep 1460861 = 547823) (by norm_num)
theorem B1231517 : Blo 646304 1231517 := bbase (se 3 (by rfl) ⟨230909, by rfl⟩ : syracuseStep 1231517 = 461819) (by norm_num)
theorem B1460933 : Blo 646304 1460933 := bbase (se 4 (by rfl) ⟨136962, by rfl⟩ : syracuseStep 1460933 = 273925) (by norm_num)
theorem B4934357 : Blo 646304 4934357 := bbase (se 7 (by rfl) ⟨57824, by rfl⟩ : syracuseStep 4934357 = 115649) (by norm_num)
theorem B969461 : Blo 646304 969461 := bbase (se 5 (by rfl) ⟨45443, by rfl⟩ : syracuseStep 969461 = 90887) (by norm_num)
theorem B969485 : Blo 646304 969485 := bbase (se 3 (by rfl) ⟨181778, by rfl⟩ : syracuseStep 969485 = 363557) (by norm_num)
theorem B1461005 : Blo 646304 1461005 := bbase (se 3 (by rfl) ⟨273938, by rfl⟩ : syracuseStep 1461005 = 547877) (by norm_num)
theorem B740125 : Blo 646304 740125 := bbase (se 3 (by rfl) ⟨138773, by rfl⟩ : syracuseStep 740125 = 277547) (by norm_num)
theorem B969509 : Blo 646304 969509 := bbase (se 4 (by rfl) ⟨90891, by rfl⟩ : syracuseStep 969509 = 181783) (by norm_num)
theorem B2771749 : Blo 646304 2771749 := bbase (se 4 (by rfl) ⟨259851, by rfl⟩ : syracuseStep 2771749 = 519703) (by norm_num)
theorem B1231661 : Blo 646304 1231661 := bbase (se 3 (by rfl) ⟨230936, by rfl⟩ : syracuseStep 1231661 = 461873) (by norm_num)
theorem B969533 : Blo 646304 969533 := bbase (se 3 (by rfl) ⟨181787, by rfl⟩ : syracuseStep 969533 = 363575) (by norm_num)
theorem B969557 : Blo 646304 969557 := bbase (se 9 (by rfl) ⟨2840, by rfl⟩ : syracuseStep 969557 = 5681) (by norm_num)
theorem B1461077 : Blo 646304 1461077 := bbase (se 9 (by rfl) ⟨4280, by rfl⟩ : syracuseStep 1461077 = 8561) (by norm_num)
theorem B1755989 : Blo 646304 1755989 := bbase (se 9 (by rfl) ⟨5144, by rfl⟩ : syracuseStep 1755989 = 10289) (by norm_num)
theorem B969581 : Blo 646304 969581 := bbase (se 3 (by rfl) ⟨181796, by rfl⟩ : syracuseStep 969581 = 363593) (by norm_num)
theorem B3689333 : Blo 646304 3689333 := bbase (se 5 (by rfl) ⟨172937, by rfl⟩ : syracuseStep 3689333 = 345875) (by norm_num)
theorem B969605 : Blo 646304 969605 := bbase (se 4 (by rfl) ⟨90900, by rfl⟩ : syracuseStep 969605 = 181801) (by norm_num)
theorem B1166213 : Blo 646304 1166213 := bbase (se 4 (by rfl) ⟨109332, by rfl⟩ : syracuseStep 1166213 = 218665) (by norm_num)
theorem B969629 : Blo 646304 969629 := bbase (se 3 (by rfl) ⟨181805, by rfl⟩ : syracuseStep 969629 = 363611) (by norm_num)
theorem B1461149 : Blo 646304 1461149 := bbase (se 3 (by rfl) ⟨273965, by rfl⟩ : syracuseStep 1461149 = 547931) (by norm_num)
theorem B969653 : Blo 646304 969653 := bbase (se 5 (by rfl) ⟨45452, by rfl⟩ : syracuseStep 969653 = 90905) (by norm_num)
theorem B5622709 : Blo 646304 5622709 := bbase (se 5 (by rfl) ⟨263564, by rfl⟩ : syracuseStep 5622709 = 527129) (by norm_num)
theorem B2182085 : Blo 646304 2182085 := bbase (se 4 (by rfl) ⟨204570, by rfl⟩ : syracuseStep 2182085 = 409141) (by norm_num)
theorem B969677 : Blo 646304 969677 := bbase (se 3 (by rfl) ⟨181814, by rfl⟩ : syracuseStep 969677 = 363629) (by norm_num)
theorem B969701 : Blo 646304 969701 := bbase (se 4 (by rfl) ⟨90909, by rfl⟩ : syracuseStep 969701 = 181819) (by norm_num)
theorem B1461221 : Blo 646304 1461221 := bbase (se 4 (by rfl) ⟨136989, by rfl⟩ : syracuseStep 1461221 = 273979) (by norm_num)
theorem B1559533 : Blo 646304 1559533 := bbase (se 3 (by rfl) ⟨292412, by rfl⟩ : syracuseStep 1559533 = 584825) (by norm_num)
theorem B969725 : Blo 646304 969725 := bbase (se 3 (by rfl) ⟨181823, by rfl⟩ : syracuseStep 969725 = 363647) (by norm_num)
theorem B969749 : Blo 646304 969749 := bbase (se 6 (by rfl) ⟨22728, by rfl⟩ : syracuseStep 969749 = 45457) (by norm_num)
theorem B969773 : Blo 646304 969773 := bbase (se 3 (by rfl) ⟨181832, by rfl⟩ : syracuseStep 969773 = 363665) (by norm_num)
theorem B1461293 : Blo 646304 1461293 := bbase (se 3 (by rfl) ⟨273992, by rfl⟩ : syracuseStep 1461293 = 547985) (by norm_num)
theorem B969797 : Blo 646304 969797 := bbase (se 4 (by rfl) ⟨90918, by rfl⟩ : syracuseStep 969797 = 181837) (by norm_num)
theorem B1231949 : Blo 646304 1231949 := bbase (se 3 (by rfl) ⟨230990, by rfl⟩ : syracuseStep 1231949 = 461981) (by norm_num)
theorem B969821 : Blo 646304 969821 := bbase (se 3 (by rfl) ⟨181841, by rfl⟩ : syracuseStep 969821 = 363683) (by norm_num)
theorem B969845 : Blo 646304 969845 := bbase (se 5 (by rfl) ⟨45461, by rfl⟩ : syracuseStep 969845 = 90923) (by norm_num)
theorem B1461365 : Blo 646304 1461365 := bbase (se 5 (by rfl) ⟨68501, by rfl⟩ : syracuseStep 1461365 = 137003) (by norm_num)
theorem B969869 : Blo 646304 969869 := bbase (se 3 (by rfl) ⟨181850, by rfl⟩ : syracuseStep 969869 = 363701) (by norm_num)
theorem B969893 : Blo 646304 969893 := bbase (se 4 (by rfl) ⟨90927, by rfl⟩ : syracuseStep 969893 = 181855) (by norm_num)
theorem B1166501 : Blo 646304 1166501 := bbase (se 4 (by rfl) ⟨109359, by rfl⟩ : syracuseStep 1166501 = 218719) (by norm_num)
theorem B969917 : Blo 646304 969917 := bbase (se 3 (by rfl) ⟨181859, by rfl⟩ : syracuseStep 969917 = 363719) (by norm_num)
theorem B1461437 : Blo 646304 1461437 := bbase (se 3 (by rfl) ⟨274019, by rfl⟩ : syracuseStep 1461437 = 548039) (by norm_num)
theorem B969941 : Blo 646304 969941 := bbase (se 7 (by rfl) ⟨11366, by rfl⟩ : syracuseStep 969941 = 22733) (by norm_num)
theorem B1232101 : Blo 646304 1232101 := bbase (se 4 (by rfl) ⟨115509, by rfl⟩ : syracuseStep 1232101 = 231019) (by norm_num)
theorem B969965 : Blo 646304 969965 := bbase (se 3 (by rfl) ⟨181868, by rfl⟩ : syracuseStep 969965 = 363737) (by norm_num)
theorem B969989 : Blo 646304 969989 := bbase (se 4 (by rfl) ⟨90936, by rfl⟩ : syracuseStep 969989 = 181873) (by norm_num)
theorem B1461509 : Blo 646304 1461509 := bbase (se 4 (by rfl) ⟨137016, by rfl⟩ : syracuseStep 1461509 = 274033) (by norm_num)
theorem B970013 : Blo 646304 970013 := bbase (se 3 (by rfl) ⟨181877, by rfl⟩ : syracuseStep 970013 = 363755) (by norm_num)
theorem B970037 : Blo 646304 970037 := bbase (se 5 (by rfl) ⟨45470, by rfl⟩ : syracuseStep 970037 = 90941) (by norm_num)
theorem B970061 : Blo 646304 970061 := bbase (se 3 (by rfl) ⟨181886, by rfl⟩ : syracuseStep 970061 = 363773) (by norm_num)
theorem B1461581 : Blo 646304 1461581 := bbase (se 3 (by rfl) ⟨274046, by rfl⟩ : syracuseStep 1461581 = 548093) (by norm_num)
theorem B1035613 : Blo 646304 1035613 := bbase (se 3 (by rfl) ⟨194177, by rfl⟩ : syracuseStep 1035613 = 388355) (by norm_num)
theorem B970085 : Blo 646304 970085 := bbase (se 4 (by rfl) ⟨90945, by rfl⟩ : syracuseStep 970085 = 181891) (by norm_num)
theorem B2182517 : Blo 646304 2182517 := bbase (se 5 (by rfl) ⟨102305, by rfl⟩ : syracuseStep 2182517 = 204611) (by norm_num)
theorem B970109 : Blo 646304 970109 := bbase (se 3 (by rfl) ⟨181895, by rfl⟩ : syracuseStep 970109 = 363791) (by norm_num)
theorem B970133 : Blo 646304 970133 := bbase (se 6 (by rfl) ⟨22737, by rfl⟩ : syracuseStep 970133 = 45475) (by norm_num)
theorem B1461653 : Blo 646304 1461653 := bbase (se 6 (by rfl) ⟨34257, by rfl⟩ : syracuseStep 1461653 = 68515) (by norm_num)
theorem B970157 : Blo 646304 970157 := bbase (se 3 (by rfl) ⟨181904, by rfl⟩ : syracuseStep 970157 = 363809) (by norm_num)
theorem B970181 : Blo 646304 970181 := bbase (se 4 (by rfl) ⟨90954, by rfl⟩ : syracuseStep 970181 = 181909) (by norm_num)
theorem B1068485 : Blo 646304 1068485 := bbase (se 4 (by rfl) ⟨100170, by rfl⟩ : syracuseStep 1068485 = 200341) (by norm_num)
theorem B970205 : Blo 646304 970205 := bbase (se 3 (by rfl) ⟨181913, by rfl⟩ : syracuseStep 970205 = 363827) (by norm_num)
theorem B1461725 : Blo 646304 1461725 := bbase (se 3 (by rfl) ⟨274073, by rfl⟩ : syracuseStep 1461725 = 548147) (by norm_num)
theorem B970229 : Blo 646304 970229 := bbase (se 5 (by rfl) ⟨45479, by rfl⟩ : syracuseStep 970229 = 90959) (by norm_num)
theorem B1560053 : Blo 646304 1560053 := bbase (se 5 (by rfl) ⟨73127, by rfl⟩ : syracuseStep 1560053 = 146255) (by norm_num)
theorem B970253 : Blo 646304 970253 := bbase (se 3 (by rfl) ⟨181922, by rfl⟩ : syracuseStep 970253 = 363845) (by norm_num)
theorem B1232405 : Blo 646304 1232405 := bbase (se 6 (by rfl) ⟨28884, by rfl⟩ : syracuseStep 1232405 = 57769) (by norm_num)
theorem B970277 : Blo 646304 970277 := bbase (se 4 (by rfl) ⟨90963, by rfl⟩ : syracuseStep 970277 = 181927) (by norm_num)
theorem B1461797 : Blo 646304 1461797 := bbase (se 4 (by rfl) ⟨137043, by rfl⟩ : syracuseStep 1461797 = 274087) (by norm_num)
theorem B970301 : Blo 646304 970301 := bbase (se 3 (by rfl) ⟨181931, by rfl⟩ : syracuseStep 970301 = 363863) (by norm_num)
theorem B970325 : Blo 646304 970325 := bbase (se 8 (by rfl) ⟨5685, by rfl⟩ : syracuseStep 970325 = 11371) (by norm_num)
theorem B970349 : Blo 646304 970349 := bbase (se 3 (by rfl) ⟨181940, by rfl⟩ : syracuseStep 970349 = 363881) (by norm_num)
theorem B1461869 : Blo 646304 1461869 := bbase (se 3 (by rfl) ⟨274100, by rfl⟩ : syracuseStep 1461869 = 548201) (by norm_num)
theorem B970373 : Blo 646304 970373 := bbase (se 4 (by rfl) ⟨90972, by rfl⟩ : syracuseStep 970373 = 181945) (by norm_num)
theorem B970397 : Blo 646304 970397 := bbase (se 3 (by rfl) ⟨181949, by rfl⟩ : syracuseStep 970397 = 363899) (by norm_num)
theorem B1068701 : Blo 646304 1068701 := bbase (se 3 (by rfl) ⟨200381, by rfl⟩ : syracuseStep 1068701 = 400763) (by norm_num)
theorem B970421 : Blo 646304 970421 := bbase (se 5 (by rfl) ⟨45488, by rfl⟩ : syracuseStep 970421 = 90977) (by norm_num)
theorem B1461941 : Blo 646304 1461941 := bbase (se 5 (by rfl) ⟨68528, by rfl⟩ : syracuseStep 1461941 = 137057) (by norm_num)
theorem B970445 : Blo 646304 970445 := bbase (se 3 (by rfl) ⟨181958, by rfl⟩ : syracuseStep 970445 = 363917) (by norm_num)
theorem B2215637 : Blo 646304 2215637 := bbase (se 7 (by rfl) ⟨25964, by rfl⟩ : syracuseStep 2215637 = 51929) (by norm_num)
theorem B970469 : Blo 646304 970469 := bbase (se 4 (by rfl) ⟨90981, by rfl⟩ : syracuseStep 970469 = 181963) (by norm_num)
theorem B970493 : Blo 646304 970493 := bbase (se 3 (by rfl) ⟨181967, by rfl⟩ : syracuseStep 970493 = 363935) (by norm_num)
theorem B1462013 : Blo 646304 1462013 := bbase (se 3 (by rfl) ⟨274127, by rfl⟩ : syracuseStep 1462013 = 548255) (by norm_num)
theorem B970517 : Blo 646304 970517 := bbase (se 6 (by rfl) ⟨22746, by rfl⟩ : syracuseStep 970517 = 45493) (by norm_num)
theorem B2182949 : Blo 646304 2182949 := bbase (se 4 (by rfl) ⟨204651, by rfl⟩ : syracuseStep 2182949 = 409303) (by norm_num)
theorem B970541 : Blo 646304 970541 := bbase (se 3 (by rfl) ⟨181976, by rfl⟩ : syracuseStep 970541 = 363953) (by norm_num)
theorem B970565 : Blo 646304 970565 := bbase (se 4 (by rfl) ⟨90990, by rfl⟩ : syracuseStep 970565 = 181981) (by norm_num)
theorem B1462085 : Blo 646304 1462085 := bbase (se 4 (by rfl) ⟨137070, by rfl⟩ : syracuseStep 1462085 = 274141) (by norm_num)
theorem B741209 : Blo 646304 741209 := bbase (se 2 (by rfl) ⟨277953, by rfl⟩ : syracuseStep 741209 = 555907) (by norm_num)
theorem B970589 : Blo 646304 970589 := bbase (se 3 (by rfl) ⟨181985, by rfl⟩ : syracuseStep 970589 = 363971) (by norm_num)
theorem B970613 : Blo 646304 970613 := bbase (se 5 (by rfl) ⟨45497, by rfl⟩ : syracuseStep 970613 = 90995) (by norm_num)
theorem B1560437 : Blo 646304 1560437 := bbase (se 5 (by rfl) ⟨73145, by rfl⟩ : syracuseStep 1560437 = 146291) (by norm_num)
theorem B970637 : Blo 646304 970637 := bbase (se 3 (by rfl) ⟨181994, by rfl⟩ : syracuseStep 970637 = 363989) (by norm_num)
theorem B1462157 : Blo 646304 1462157 := bbase (se 3 (by rfl) ⟨274154, by rfl⟩ : syracuseStep 1462157 = 548309) (by norm_num)
theorem B970661 : Blo 646304 970661 := bbase (se 4 (by rfl) ⟨90999, by rfl⟩ : syracuseStep 970661 = 181999) (by norm_num)
theorem B1560485 : Blo 646304 1560485 := bbase (se 4 (by rfl) ⟨146295, by rfl⟩ : syracuseStep 1560485 = 292591) (by norm_num)
theorem B1560493 : Blo 646304 1560493 := bbase (se 3 (by rfl) ⟨292592, by rfl⟩ : syracuseStep 1560493 = 585185) (by norm_num)
theorem B970685 : Blo 646304 970685 := bbase (se 3 (by rfl) ⟨182003, by rfl⟩ : syracuseStep 970685 = 364007) (by norm_num)
theorem B970709 : Blo 646304 970709 := bbase (se 7 (by rfl) ⟨11375, by rfl⟩ : syracuseStep 970709 = 22751) (by norm_num)
theorem B1462229 : Blo 646304 1462229 := bbase (se 7 (by rfl) ⟨17135, by rfl⟩ : syracuseStep 1462229 = 34271) (by norm_num)
theorem B970733 : Blo 646304 970733 := bbase (se 3 (by rfl) ⟨182012, by rfl⟩ : syracuseStep 970733 = 364025) (by norm_num)
theorem B970757 : Blo 646304 970757 := bbase (se 4 (by rfl) ⟨91008, by rfl⟩ : syracuseStep 970757 = 182017) (by norm_num)
theorem B970781 : Blo 646304 970781 := bbase (se 3 (by rfl) ⟨182021, by rfl⟩ : syracuseStep 970781 = 364043) (by norm_num)
theorem B1462301 : Blo 646304 1462301 := bbase (se 3 (by rfl) ⟨274181, by rfl⟩ : syracuseStep 1462301 = 548363) (by norm_num)
theorem B970805 : Blo 646304 970805 := bbase (se 5 (by rfl) ⟨45506, by rfl⟩ : syracuseStep 970805 = 91013) (by norm_num)
theorem B970829 : Blo 646304 970829 := bbase (se 3 (by rfl) ⟨182030, by rfl⟩ : syracuseStep 970829 = 364061) (by norm_num)
theorem B970853 : Blo 646304 970853 := bbase (se 4 (by rfl) ⟨91017, by rfl⟩ : syracuseStep 970853 = 182035) (by norm_num)
theorem B1462373 : Blo 646304 1462373 := bbase (se 4 (by rfl) ⟨137097, by rfl⟩ : syracuseStep 1462373 = 274195) (by norm_num)
theorem B970877 : Blo 646304 970877 := bbase (se 3 (by rfl) ⟨182039, by rfl⟩ : syracuseStep 970877 = 364079) (by norm_num)
theorem B970901 : Blo 646304 970901 := bbase (se 6 (by rfl) ⟨22755, by rfl⟩ : syracuseStep 970901 = 45511) (by norm_num)
theorem B970925 : Blo 646304 970925 := bbase (se 3 (by rfl) ⟨182048, by rfl⟩ : syracuseStep 970925 = 364097) (by norm_num)
theorem B1462445 : Blo 646304 1462445 := bbase (se 3 (by rfl) ⟨274208, by rfl⟩ : syracuseStep 1462445 = 548417) (by norm_num)
theorem B970949 : Blo 646304 970949 := bbase (se 4 (by rfl) ⟨91026, by rfl⟩ : syracuseStep 970949 = 182053) (by norm_num)
theorem B2183381 : Blo 646304 2183381 := bbase (se 7 (by rfl) ⟨25586, by rfl⟩ : syracuseStep 2183381 = 51173) (by norm_num)
theorem B970973 : Blo 646304 970973 := bbase (se 3 (by rfl) ⟨182057, by rfl⟩ : syracuseStep 970973 = 364115) (by norm_num)
theorem B970997 : Blo 646304 970997 := bbase (se 5 (by rfl) ⟨45515, by rfl⟩ : syracuseStep 970997 = 91031) (by norm_num)
theorem B2773237 : Blo 646304 2773237 := bbase (se 5 (by rfl) ⟨129995, by rfl⟩ : syracuseStep 2773237 = 259991) (by norm_num)
theorem B1462517 : Blo 646304 1462517 := bbase (se 5 (by rfl) ⟨68555, by rfl⟩ : syracuseStep 1462517 = 137111) (by norm_num)
theorem B2773253 : Blo 646304 2773253 := bbase (se 4 (by rfl) ⟨259992, by rfl⟩ : syracuseStep 2773253 = 519985) (by norm_num)
theorem B1233157 : Blo 646304 1233157 := bbase (se 4 (by rfl) ⟨115608, by rfl⟩ : syracuseStep 1233157 = 231217) (by norm_num)
theorem B971021 : Blo 646304 971021 := bbase (se 3 (by rfl) ⟨182066, by rfl⟩ : syracuseStep 971021 = 364133) (by norm_num)
theorem B971045 : Blo 646304 971045 := bbase (se 4 (by rfl) ⟨91035, by rfl⟩ : syracuseStep 971045 = 182071) (by norm_num)
theorem B1167653 : Blo 646304 1167653 := bbase (se 4 (by rfl) ⟨109467, by rfl⟩ : syracuseStep 1167653 = 218935) (by norm_num)
theorem B971069 : Blo 646304 971069 := bbase (se 3 (by rfl) ⟨182075, by rfl⟩ : syracuseStep 971069 = 364151) (by norm_num)
theorem B1462589 : Blo 646304 1462589 := bbase (se 3 (by rfl) ⟨274235, by rfl⟩ : syracuseStep 1462589 = 548471) (by norm_num)
theorem B1036613 : Blo 646304 1036613 := bbase (se 4 (by rfl) ⟨97182, by rfl⟩ : syracuseStep 1036613 = 194365) (by norm_num)
theorem B971093 : Blo 646304 971093 := bbase (se 10 (by rfl) ⟨1422, by rfl⟩ : syracuseStep 971093 = 2845) (by norm_num)
theorem B971117 : Blo 646304 971117 := bbase (se 3 (by rfl) ⟨182084, by rfl⟩ : syracuseStep 971117 = 364169) (by norm_num)
theorem B1167733 : Blo 646304 1167733 := bbase (se 5 (by rfl) ⟨54737, by rfl⟩ : syracuseStep 1167733 = 109475) (by norm_num)
theorem B971141 : Blo 646304 971141 := bbase (se 4 (by rfl) ⟨91044, by rfl⟩ : syracuseStep 971141 = 182089) (by norm_num)
theorem B1462661 : Blo 646304 1462661 := bbase (se 4 (by rfl) ⟨137124, by rfl⟩ : syracuseStep 1462661 = 274249) (by norm_num)
theorem B1233301 : Blo 646304 1233301 := bbase (se 6 (by rfl) ⟨28905, by rfl⟩ : syracuseStep 1233301 = 57811) (by norm_num)
theorem B971165 : Blo 646304 971165 := bbase (se 3 (by rfl) ⟨182093, by rfl⟩ : syracuseStep 971165 = 364187) (by norm_num)
theorem B971189 : Blo 646304 971189 := bbase (se 5 (by rfl) ⟨45524, by rfl⟩ : syracuseStep 971189 = 91049) (by norm_num)
theorem B1036741 : Blo 646304 1036741 := bbase (se 4 (by rfl) ⟨97194, by rfl⟩ : syracuseStep 1036741 = 194389) (by norm_num)
theorem B971213 : Blo 646304 971213 := bbase (se 3 (by rfl) ⟨182102, by rfl⟩ : syracuseStep 971213 = 364205) (by norm_num)
theorem B1462733 : Blo 646304 1462733 := bbase (se 3 (by rfl) ⟨274262, by rfl⟩ : syracuseStep 1462733 = 548525) (by norm_num)
theorem B971237 : Blo 646304 971237 := bbase (se 4 (by rfl) ⟨91053, by rfl⟩ : syracuseStep 971237 = 182107) (by norm_num)
theorem B971261 : Blo 646304 971261 := bbase (se 3 (by rfl) ⟨182111, by rfl⟩ : syracuseStep 971261 = 364223) (by norm_num)
theorem B1036805 : Blo 646304 1036805 := bbase (se 4 (by rfl) ⟨97200, by rfl⟩ : syracuseStep 1036805 = 194401) (by norm_num)
theorem B971285 : Blo 646304 971285 := bbase (se 6 (by rfl) ⟨22764, by rfl⟩ : syracuseStep 971285 = 45529) (by norm_num)
theorem B1462805 : Blo 646304 1462805 := bbase (se 6 (by rfl) ⟨34284, by rfl⟩ : syracuseStep 1462805 = 68569) (by norm_num)
theorem B971309 : Blo 646304 971309 := bbase (se 3 (by rfl) ⟨182120, by rfl⟩ : syracuseStep 971309 = 364241) (by norm_num)
theorem B1233461 : Blo 646304 1233461 := bbase (se 5 (by rfl) ⟨57818, by rfl⟩ : syracuseStep 1233461 = 115637) (by norm_num)
theorem B971333 : Blo 646304 971333 := bbase (se 4 (by rfl) ⟨91062, by rfl⟩ : syracuseStep 971333 = 182125) (by norm_num)
theorem B15782485 : Blo 646304 15782485 := bbase (se 8 (by rfl) ⟨92475, by rfl⟩ : syracuseStep 15782485 = 184951) (by norm_num)
theorem B971357 : Blo 646304 971357 := bbase (se 3 (by rfl) ⟨182129, by rfl⟩ : syracuseStep 971357 = 364259) (by norm_num)
theorem B1462877 : Blo 646304 1462877 := bbase (se 3 (by rfl) ⟨274289, by rfl⟩ : syracuseStep 1462877 = 548579) (by norm_num)
theorem B971381 : Blo 646304 971381 := bbase (se 5 (by rfl) ⟨45533, by rfl⟩ : syracuseStep 971381 = 91067) (by norm_num)
theorem B2183813 : Blo 646304 2183813 := bbase (se 4 (by rfl) ⟨204732, by rfl⟩ : syracuseStep 2183813 = 409465) (by norm_num)
theorem B971405 : Blo 646304 971405 := bbase (se 3 (by rfl) ⟨182138, by rfl⟩ : syracuseStep 971405 = 364277) (by norm_num)
theorem B971429 : Blo 646304 971429 := bbase (se 4 (by rfl) ⟨91071, by rfl⟩ : syracuseStep 971429 = 182143) (by norm_num)
theorem B1462949 : Blo 646304 1462949 := bbase (se 4 (by rfl) ⟨137151, by rfl⟩ : syracuseStep 1462949 = 274303) (by norm_num)
theorem B971453 : Blo 646304 971453 := bbase (se 3 (by rfl) ⟨182147, by rfl⟩ : syracuseStep 971453 = 364295) (by norm_num)
theorem B1233605 : Blo 646304 1233605 := bbase (se 4 (by rfl) ⟨115650, by rfl⟩ : syracuseStep 1233605 = 231301) (by norm_num)
theorem B971477 : Blo 646304 971477 := bbase (se 7 (by rfl) ⟨11384, by rfl⟩ : syracuseStep 971477 = 22769) (by norm_num)
theorem B971501 : Blo 646304 971501 := bbase (se 3 (by rfl) ⟨182156, by rfl⟩ : syracuseStep 971501 = 364313) (by norm_num)
theorem B1463021 : Blo 646304 1463021 := bbase (se 3 (by rfl) ⟨274316, by rfl⟩ : syracuseStep 1463021 = 548633) (by norm_num)
theorem B971525 : Blo 646304 971525 := bbase (se 4 (by rfl) ⟨91080, by rfl⟩ : syracuseStep 971525 = 182161) (by norm_num)
theorem B971549 : Blo 646304 971549 := bbase (se 3 (by rfl) ⟨182165, by rfl⟩ : syracuseStep 971549 = 364331) (by norm_num)
theorem B971573 : Blo 646304 971573 := bbase (se 5 (by rfl) ⟨45542, by rfl⟩ : syracuseStep 971573 = 91085) (by norm_num)
theorem B1463093 : Blo 646304 1463093 := bbase (se 5 (by rfl) ⟨68582, by rfl⟩ : syracuseStep 1463093 = 137165) (by norm_num)
theorem B971597 : Blo 646304 971597 := bbase (se 3 (by rfl) ⟨182174, by rfl⟩ : syracuseStep 971597 = 364349) (by norm_num)
theorem B971621 : Blo 646304 971621 := bbase (se 4 (by rfl) ⟨91089, by rfl⟩ : syracuseStep 971621 = 182179) (by norm_num)
theorem B971645 : Blo 646304 971645 := bbase (se 3 (by rfl) ⟨182183, by rfl⟩ : syracuseStep 971645 = 364367) (by norm_num)
theorem B1463165 : Blo 646304 1463165 := bbase (se 3 (by rfl) ⟨274343, by rfl⟩ : syracuseStep 1463165 = 548687) (by norm_num)
theorem B971669 : Blo 646304 971669 := bbase (se 6 (by rfl) ⟨22773, by rfl⟩ : syracuseStep 971669 = 45547) (by norm_num)
theorem B1561493 : Blo 646304 1561493 := bbase (se 6 (by rfl) ⟨36597, by rfl⟩ : syracuseStep 1561493 = 73195) (by norm_num)
theorem B971693 : Blo 646304 971693 := bbase (se 3 (by rfl) ⟨182192, by rfl⟩ : syracuseStep 971693 = 364385) (by norm_num)
theorem B971717 : Blo 646304 971717 := bbase (se 4 (by rfl) ⟨91098, by rfl⟩ : syracuseStep 971717 = 182197) (by norm_num)
theorem B971741 : Blo 646304 971741 := bbase (se 3 (by rfl) ⟨182201, by rfl⟩ : syracuseStep 971741 = 364403) (by norm_num)
theorem B1233893 : Blo 646304 1233893 := bbase (se 4 (by rfl) ⟨115677, by rfl⟩ : syracuseStep 1233893 = 231355) (by norm_num)
theorem B971765 : Blo 646304 971765 := bbase (se 5 (by rfl) ⟨45551, by rfl⟩ : syracuseStep 971765 = 91103) (by norm_num)
theorem B971789 : Blo 646304 971789 := bbase (se 3 (by rfl) ⟨182210, by rfl⟩ : syracuseStep 971789 = 364421) (by norm_num)
theorem B971813 : Blo 646304 971813 := bbase (se 4 (by rfl) ⟨91107, by rfl⟩ : syracuseStep 971813 = 182215) (by norm_num)
theorem B2184245 : Blo 646304 2184245 := bbase (se 5 (by rfl) ⟨102386, by rfl⟩ : syracuseStep 2184245 = 204773) (by norm_num)
theorem B971837 : Blo 646304 971837 := bbase (se 3 (by rfl) ⟨182219, by rfl⟩ : syracuseStep 971837 = 364439) (by norm_num)
theorem B971861 : Blo 646304 971861 := bbase (se 8 (by rfl) ⟨5694, by rfl⟩ : syracuseStep 971861 = 11389) (by norm_num)
theorem B21353557 : Blo 646304 21353557 := bbase (se 8 (by rfl) ⟨125118, by rfl⟩ : syracuseStep 21353557 = 250237) (by norm_num)
theorem B1561685 : Blo 646304 1561685 := bbase (se 8 (by rfl) ⟨9150, by rfl⟩ : syracuseStep 1561685 = 18301) (by norm_num)
theorem B971885 : Blo 646304 971885 := bbase (se 3 (by rfl) ⟨182228, by rfl⟩ : syracuseStep 971885 = 364457) (by norm_num)
theorem B1234045 : Blo 646304 1234045 := bbase (se 3 (by rfl) ⟨231383, by rfl⟩ : syracuseStep 1234045 = 462767) (by norm_num)
theorem B971909 : Blo 646304 971909 := bbase (se 4 (by rfl) ⟨91116, by rfl⟩ : syracuseStep 971909 = 182233) (by norm_num)
theorem B971933 : Blo 646304 971933 := bbase (se 3 (by rfl) ⟨182237, by rfl⟩ : syracuseStep 971933 = 364475) (by norm_num)
theorem B971957 : Blo 646304 971957 := bbase (se 5 (by rfl) ⟨45560, by rfl⟩ : syracuseStep 971957 = 91121) (by norm_num)
theorem B971981 : Blo 646304 971981 := bbase (se 3 (by rfl) ⟨182246, by rfl⟩ : syracuseStep 971981 = 364493) (by norm_num)
theorem B972005 : Blo 646304 972005 := bbase (se 4 (by rfl) ⟨91125, by rfl⟩ : syracuseStep 972005 = 182251) (by norm_num)
theorem B972029 : Blo 646304 972029 := bbase (se 3 (by rfl) ⟨182255, by rfl⟩ : syracuseStep 972029 = 364511) (by norm_num)
theorem B972053 : Blo 646304 972053 := bbase (se 6 (by rfl) ⟨22782, by rfl⟩ : syracuseStep 972053 = 45565) (by norm_num)
theorem B972077 : Blo 646304 972077 := bbase (se 3 (by rfl) ⟨182264, by rfl⟩ : syracuseStep 972077 = 364529) (by norm_num)
theorem B972101 : Blo 646304 972101 := bbase (se 4 (by rfl) ⟨91134, by rfl⟩ : syracuseStep 972101 = 182269) (by norm_num)
theorem B972125 : Blo 646304 972125 := bbase (se 3 (by rfl) ⟨182273, by rfl⟩ : syracuseStep 972125 = 364547) (by norm_num)
theorem B972149 : Blo 646304 972149 := bbase (se 5 (by rfl) ⟨45569, by rfl⟩ : syracuseStep 972149 = 91139) (by norm_num)
theorem B972173 : Blo 646304 972173 := bbase (se 3 (by rfl) ⟨182282, by rfl⟩ : syracuseStep 972173 = 364565) (by norm_num)
theorem B972197 : Blo 646304 972197 := bbase (se 4 (by rfl) ⟨91143, by rfl⟩ : syracuseStep 972197 = 182287) (by norm_num)
theorem B1168813 : Blo 646304 1168813 := bbase (se 3 (by rfl) ⟨219152, by rfl⟩ : syracuseStep 1168813 = 438305) (by norm_num)
theorem B1234349 : Blo 646304 1234349 := bbase (se 3 (by rfl) ⟨231440, by rfl⟩ : syracuseStep 1234349 = 462881) (by norm_num)
theorem B972221 : Blo 646304 972221 := bbase (se 3 (by rfl) ⟨182291, by rfl⟩ : syracuseStep 972221 = 364583) (by norm_num)
theorem B972245 : Blo 646304 972245 := bbase (se 7 (by rfl) ⟨11393, by rfl⟩ : syracuseStep 972245 = 22787) (by norm_num)
theorem B2184677 : Blo 646304 2184677 := bbase (se 4 (by rfl) ⟨204813, by rfl⟩ : syracuseStep 2184677 = 409627) (by norm_num)
theorem B972269 : Blo 646304 972269 := bbase (se 3 (by rfl) ⟨182300, by rfl⟩ : syracuseStep 972269 = 364601) (by norm_num)
theorem B972293 : Blo 646304 972293 := bbase (se 4 (by rfl) ⟨91152, by rfl⟩ : syracuseStep 972293 = 182305) (by norm_num)
theorem B1168901 : Blo 646304 1168901 := bbase (se 4 (by rfl) ⟨109584, by rfl⟩ : syracuseStep 1168901 = 219169) (by norm_num)
theorem B972317 : Blo 646304 972317 := bbase (se 3 (by rfl) ⟨182309, by rfl⟩ : syracuseStep 972317 = 364619) (by norm_num)
theorem B874037 : Blo 646304 874037 := bbase (se 5 (by rfl) ⟨40970, by rfl⟩ : syracuseStep 874037 = 81941) (by norm_num)
theorem B972341 : Blo 646304 972341 := bbase (se 5 (by rfl) ⟨45578, by rfl⟩ : syracuseStep 972341 = 91157) (by norm_num)
theorem B972365 : Blo 646304 972365 := bbase (se 3 (by rfl) ⟨182318, by rfl⟩ : syracuseStep 972365 = 364637) (by norm_num)
theorem B972389 : Blo 646304 972389 := bbase (se 4 (by rfl) ⟨91161, by rfl⟩ : syracuseStep 972389 = 182323) (by norm_num)
theorem B972413 : Blo 646304 972413 := bbase (se 3 (by rfl) ⟨182327, by rfl⟩ : syracuseStep 972413 = 364655) (by norm_num)
theorem B972437 : Blo 646304 972437 := bbase (se 6 (by rfl) ⟨22791, by rfl⟩ : syracuseStep 972437 = 45583) (by norm_num)
theorem B972461 : Blo 646304 972461 := bbase (se 3 (by rfl) ⟨182336, by rfl⟩ : syracuseStep 972461 = 364673) (by norm_num)
theorem B972485 : Blo 646304 972485 := bbase (se 4 (by rfl) ⟨91170, by rfl⟩ : syracuseStep 972485 = 182341) (by norm_num)
theorem B1660621 : Blo 646304 1660621 := bbase (se 3 (by rfl) ⟨311366, by rfl⟩ : syracuseStep 1660621 = 622733) (by norm_num)
theorem B972509 : Blo 646304 972509 := bbase (se 3 (by rfl) ⟨182345, by rfl⟩ : syracuseStep 972509 = 364691) (by norm_num)
theorem B972533 : Blo 646304 972533 := bbase (se 5 (by rfl) ⟨45587, by rfl⟩ : syracuseStep 972533 = 91175) (by norm_num)
theorem B2807557 : Blo 646304 2807557 := bbase (se 4 (by rfl) ⟨263208, by rfl⟩ : syracuseStep 2807557 = 526417) (by norm_num)
theorem B972557 : Blo 646304 972557 := bbase (se 3 (by rfl) ⟨182354, by rfl⟩ : syracuseStep 972557 = 364709) (by norm_num)
theorem B972581 : Blo 646304 972581 := bbase (se 4 (by rfl) ⟨91179, by rfl⟩ : syracuseStep 972581 = 182359) (by norm_num)
theorem B1038125 : Blo 646304 1038125 := bbase (se 3 (by rfl) ⟨194648, by rfl⟩ : syracuseStep 1038125 = 389297) (by norm_num)
theorem B1660733 : Blo 646304 1660733 := bbase (se 3 (by rfl) ⟨311387, by rfl⟩ : syracuseStep 1660733 = 622775) (by norm_num)
theorem B972605 : Blo 646304 972605 := bbase (se 3 (by rfl) ⟨182363, by rfl⟩ : syracuseStep 972605 = 364727) (by norm_num)
theorem B972629 : Blo 646304 972629 := bbase (se 9 (by rfl) ⟨2849, by rfl⟩ : syracuseStep 972629 = 5699) (by norm_num)
theorem B972653 : Blo 646304 972653 := bbase (se 3 (by rfl) ⟨182372, by rfl⟩ : syracuseStep 972653 = 364745) (by norm_num)
theorem B972677 : Blo 646304 972677 := bbase (se 4 (by rfl) ⟨91188, by rfl⟩ : syracuseStep 972677 = 182377) (by norm_num)
theorem B2185109 : Blo 646304 2185109 := bbase (se 6 (by rfl) ⟨51213, by rfl⟩ : syracuseStep 2185109 = 102427) (by norm_num)
theorem B972701 : Blo 646304 972701 := bbase (se 3 (by rfl) ⟨182381, by rfl⟩ : syracuseStep 972701 = 364763) (by norm_num)
theorem B874405 : Blo 646304 874405 := bbase (se 4 (by rfl) ⟨81975, by rfl⟩ : syracuseStep 874405 = 163951) (by norm_num)
theorem B1038253 : Blo 646304 1038253 := bbase (se 3 (by rfl) ⟨194672, by rfl⟩ : syracuseStep 1038253 = 389345) (by norm_num)
theorem B972725 : Blo 646304 972725 := bbase (se 5 (by rfl) ⟨45596, by rfl⟩ : syracuseStep 972725 = 91193) (by norm_num)
theorem B972749 : Blo 646304 972749 := bbase (se 3 (by rfl) ⟨182390, by rfl⟩ : syracuseStep 972749 = 364781) (by norm_num)
theorem B972773 : Blo 646304 972773 := bbase (se 4 (by rfl) ⟨91197, by rfl⟩ : syracuseStep 972773 = 182395) (by norm_num)
theorem B972797 : Blo 646304 972797 := bbase (se 3 (by rfl) ⟨182399, by rfl⟩ : syracuseStep 972797 = 364799) (by norm_num)
theorem B1169405 : Blo 646304 1169405 := bbase (se 3 (by rfl) ⟨219263, by rfl⟩ : syracuseStep 1169405 = 438527) (by norm_num)
theorem B972821 : Blo 646304 972821 := bbase (se 6 (by rfl) ⟨22800, by rfl⟩ : syracuseStep 972821 = 45601) (by norm_num)
theorem B972845 : Blo 646304 972845 := bbase (se 3 (by rfl) ⟨182408, by rfl⟩ : syracuseStep 972845 = 364817) (by norm_num)
theorem B972869 : Blo 646304 972869 := bbase (se 4 (by rfl) ⟨91206, by rfl⟩ : syracuseStep 972869 = 182413) (by norm_num)
theorem B972893 : Blo 646304 972893 := bbase (se 3 (by rfl) ⟨182417, by rfl⟩ : syracuseStep 972893 = 364835) (by norm_num)
theorem B972917 : Blo 646304 972917 := bbase (se 5 (by rfl) ⟨45605, by rfl⟩ : syracuseStep 972917 = 91211) (by norm_num)
theorem B972941 : Blo 646304 972941 := bbase (se 3 (by rfl) ⟨182426, by rfl⟩ : syracuseStep 972941 = 364853) (by norm_num)
theorem B972965 : Blo 646304 972965 := bbase (se 4 (by rfl) ⟨91215, by rfl⟩ : syracuseStep 972965 = 182431) (by norm_num)
theorem B972989 : Blo 646304 972989 := bbase (se 3 (by rfl) ⟨182435, by rfl⟩ : syracuseStep 972989 = 364871) (by norm_num)
theorem B973013 : Blo 646304 973013 := bbase (se 7 (by rfl) ⟨11402, by rfl⟩ : syracuseStep 973013 = 22805) (by norm_num)
theorem B973037 : Blo 646304 973037 := bbase (se 3 (by rfl) ⟨182444, by rfl⟩ : syracuseStep 973037 = 364889) (by norm_num)
theorem B973061 : Blo 646304 973061 := bbase (se 4 (by rfl) ⟨91224, by rfl⟩ : syracuseStep 973061 = 182449) (by norm_num)
theorem B973085 : Blo 646304 973085 := bbase (se 3 (by rfl) ⟨182453, by rfl⟩ : syracuseStep 973085 = 364907) (by norm_num)
theorem B973109 : Blo 646304 973109 := bbase (se 5 (by rfl) ⟨45614, by rfl⟩ : syracuseStep 973109 = 91229) (by norm_num)
theorem B2185541 : Blo 646304 2185541 := bbase (se 4 (by rfl) ⟨204894, by rfl⟩ : syracuseStep 2185541 = 409789) (by norm_num)
theorem B973133 : Blo 646304 973133 := bbase (se 3 (by rfl) ⟨182462, by rfl⟩ : syracuseStep 973133 = 364925) (by norm_num)
theorem B874837 : Blo 646304 874837 := bbase (se 10 (by rfl) ⟨1281, by rfl⟩ : syracuseStep 874837 = 2563) (by norm_num)
theorem B973157 : Blo 646304 973157 := bbase (se 4 (by rfl) ⟨91233, by rfl⟩ : syracuseStep 973157 = 182467) (by norm_num)
theorem B973181 : Blo 646304 973181 := bbase (se 3 (by rfl) ⟨182471, by rfl⟩ : syracuseStep 973181 = 364943) (by norm_num)
theorem B2218373 : Blo 646304 2218373 := bbase (se 4 (by rfl) ⟨207972, by rfl⟩ : syracuseStep 2218373 = 415945) (by norm_num)
theorem B973205 : Blo 646304 973205 := bbase (se 6 (by rfl) ⟨22809, by rfl⟩ : syracuseStep 973205 = 45619) (by norm_num)
theorem B973229 : Blo 646304 973229 := bbase (se 3 (by rfl) ⟨182480, by rfl⟩ : syracuseStep 973229 = 364961) (by norm_num)
theorem B776633 : Blo 646304 776633 := bbase (se 2 (by rfl) ⟨291237, by rfl⟩ : syracuseStep 776633 = 582475) (by norm_num)
theorem B973253 : Blo 646304 973253 := bbase (se 4 (by rfl) ⟨91242, by rfl⟩ : syracuseStep 973253 = 182485) (by norm_num)
theorem B2775509 : Blo 646304 2775509 := bbase (se 7 (by rfl) ⟨32525, by rfl⟩ : syracuseStep 2775509 = 65051) (by norm_num)
theorem B973277 : Blo 646304 973277 := bbase (se 3 (by rfl) ⟨182489, by rfl⟩ : syracuseStep 973277 = 364979) (by norm_num)
theorem B973301 : Blo 646304 973301 := bbase (se 5 (by rfl) ⟨45623, by rfl⟩ : syracuseStep 973301 = 91247) (by norm_num)
theorem B875005 : Blo 646304 875005 := bbase (se 3 (by rfl) ⟨164063, by rfl⟩ : syracuseStep 875005 = 328127) (by norm_num)
theorem B973325 : Blo 646304 973325 := bbase (se 3 (by rfl) ⟨182498, by rfl⟩ : syracuseStep 973325 = 364997) (by norm_num)
theorem B973349 : Blo 646304 973349 := bbase (se 4 (by rfl) ⟨91251, by rfl⟩ : syracuseStep 973349 = 182503) (by norm_num)
theorem B973373 : Blo 646304 973373 := bbase (se 3 (by rfl) ⟨182507, by rfl⟩ : syracuseStep 973373 = 365015) (by norm_num)
theorem B973397 : Blo 646304 973397 := bbase (se 8 (by rfl) ⟨5703, by rfl⟩ : syracuseStep 973397 = 11407) (by norm_num)
theorem B973421 : Blo 646304 973421 := bbase (se 3 (by rfl) ⟨182516, by rfl⟩ : syracuseStep 973421 = 365033) (by norm_num)
theorem B973445 : Blo 646304 973445 := bbase (se 4 (by rfl) ⟨91260, by rfl⟩ : syracuseStep 973445 = 182521) (by norm_num)
theorem B973469 : Blo 646304 973469 := bbase (se 3 (by rfl) ⟨182525, by rfl⟩ : syracuseStep 973469 = 365051) (by norm_num)
theorem B973493 : Blo 646304 973493 := bbase (se 5 (by rfl) ⟨45632, by rfl⟩ : syracuseStep 973493 = 91265) (by norm_num)
theorem B973517 : Blo 646304 973517 := bbase (se 3 (by rfl) ⟨182534, by rfl⟩ : syracuseStep 973517 = 365069) (by norm_num)
theorem B1039061 : Blo 646304 1039061 := bbase (se 7 (by rfl) ⟨12176, by rfl⟩ : syracuseStep 1039061 = 24353) (by norm_num)
theorem B973541 : Blo 646304 973541 := bbase (se 4 (by rfl) ⟨91269, by rfl⟩ : syracuseStep 973541 = 182539) (by norm_num)
theorem B2185973 : Blo 646304 2185973 := bbase (se 5 (by rfl) ⟨102467, by rfl⟩ : syracuseStep 2185973 = 204935) (by norm_num)
theorem B973565 : Blo 646304 973565 := bbase (se 3 (by rfl) ⟨182543, by rfl⟩ : syracuseStep 973565 = 365087) (by norm_num)
theorem B875269 : Blo 646304 875269 := bbase (se 4 (by rfl) ⟨82056, by rfl⟩ : syracuseStep 875269 = 164113) (by norm_num)
theorem B973589 : Blo 646304 973589 := bbase (se 6 (by rfl) ⟨22818, by rfl⟩ : syracuseStep 973589 = 45637) (by norm_num)
theorem B776989 : Blo 646304 776989 := bbase (se 3 (by rfl) ⟨145685, by rfl⟩ : syracuseStep 776989 = 291371) (by norm_num)
theorem B973613 : Blo 646304 973613 := bbase (se 3 (by rfl) ⟨182552, by rfl⟩ : syracuseStep 973613 = 365105) (by norm_num)
theorem B973637 : Blo 646304 973637 := bbase (se 4 (by rfl) ⟨91278, by rfl⟩ : syracuseStep 973637 = 182557) (by norm_num)
theorem B973661 : Blo 646304 973661 := bbase (se 3 (by rfl) ⟨182561, by rfl⟩ : syracuseStep 973661 = 365123) (by norm_num)
theorem B973685 : Blo 646304 973685 := bbase (se 5 (by rfl) ⟨45641, by rfl⟩ : syracuseStep 973685 = 91283) (by norm_num)
theorem B973709 : Blo 646304 973709 := bbase (se 3 (by rfl) ⟨182570, by rfl⟩ : syracuseStep 973709 = 365141) (by norm_num)
theorem B973733 : Blo 646304 973733 := bbase (se 4 (by rfl) ⟨91287, by rfl⟩ : syracuseStep 973733 = 182575) (by norm_num)
theorem B973757 : Blo 646304 973757 := bbase (se 3 (by rfl) ⟨182579, by rfl⟩ : syracuseStep 973757 = 365159) (by norm_num)
theorem B973781 : Blo 646304 973781 := bbase (se 7 (by rfl) ⟨11411, by rfl⟩ : syracuseStep 973781 = 22823) (by norm_num)
theorem B973805 : Blo 646304 973805 := bbase (se 3 (by rfl) ⟨182588, by rfl⟩ : syracuseStep 973805 = 365177) (by norm_num)
theorem B1039349 : Blo 646304 1039349 := bbase (se 5 (by rfl) ⟨48719, by rfl⟩ : syracuseStep 1039349 = 97439) (by norm_num)
theorem B973829 : Blo 646304 973829 := bbase (se 4 (by rfl) ⟨91296, by rfl⟩ : syracuseStep 973829 = 182593) (by norm_num)
theorem B973853 : Blo 646304 973853 := bbase (se 3 (by rfl) ⟨182597, by rfl⟩ : syracuseStep 973853 = 365195) (by norm_num)
theorem B973877 : Blo 646304 973877 := bbase (se 5 (by rfl) ⟨45650, by rfl⟩ : syracuseStep 973877 = 91301) (by norm_num)
theorem B973901 : Blo 646304 973901 := bbase (se 3 (by rfl) ⟨182606, by rfl⟩ : syracuseStep 973901 = 365213) (by norm_num)
theorem B973925 : Blo 646304 973925 := bbase (se 4 (by rfl) ⟨91305, by rfl⟩ : syracuseStep 973925 = 182611) (by norm_num)
theorem B777325 : Blo 646304 777325 := bbase (se 3 (by rfl) ⟨145748, by rfl⟩ : syracuseStep 777325 = 291497) (by norm_num)
theorem B973949 : Blo 646304 973949 := bbase (se 3 (by rfl) ⟨182615, by rfl⟩ : syracuseStep 973949 = 365231) (by norm_num)
theorem B973973 : Blo 646304 973973 := bbase (se 6 (by rfl) ⟨22827, by rfl⟩ : syracuseStep 973973 = 45655) (by norm_num)
theorem B2022565 : Blo 646304 2022565 := bbase (se 4 (by rfl) ⟨189615, by rfl⟩ : syracuseStep 2022565 = 379231) (by norm_num)
theorem B2186405 : Blo 646304 2186405 := bbase (se 4 (by rfl) ⟨204975, by rfl⟩ : syracuseStep 2186405 = 409951) (by norm_num)
theorem B973997 : Blo 646304 973997 := bbase (se 3 (by rfl) ⟨182624, by rfl⟩ : syracuseStep 973997 = 365249) (by norm_num)
theorem B1399997 : Blo 646304 1399997 := bbase (se 3 (by rfl) ⟨262499, by rfl⟩ : syracuseStep 1399997 = 524999) (by norm_num)
theorem B1400005 : Blo 646304 1400005 := bbase (se 4 (by rfl) ⟨131250, by rfl⟩ : syracuseStep 1400005 = 262501) (by norm_num)
theorem B974021 : Blo 646304 974021 := bbase (se 4 (by rfl) ⟨91314, by rfl⟩ : syracuseStep 974021 = 182629) (by norm_num)
theorem B974045 : Blo 646304 974045 := bbase (se 3 (by rfl) ⟨182633, by rfl⟩ : syracuseStep 974045 = 365267) (by norm_num)
theorem B974069 : Blo 646304 974069 := bbase (se 5 (by rfl) ⟨45659, by rfl⟩ : syracuseStep 974069 = 91319) (by norm_num)
theorem B974093 : Blo 646304 974093 := bbase (se 3 (by rfl) ⟨182642, by rfl⟩ : syracuseStep 974093 = 365285) (by norm_num)
theorem B974117 : Blo 646304 974117 := bbase (se 4 (by rfl) ⟨91323, by rfl⟩ : syracuseStep 974117 = 182647) (by norm_num)
theorem B974141 : Blo 646304 974141 := bbase (se 3 (by rfl) ⟨182651, by rfl⟩ : syracuseStep 974141 = 365303) (by norm_num)
theorem B974165 : Blo 646304 974165 := bbase (se 11 (by rfl) ⟨713, by rfl⟩ : syracuseStep 974165 = 1427) (by norm_num)
theorem B974189 : Blo 646304 974189 := bbase (se 3 (by rfl) ⟨182660, by rfl⟩ : syracuseStep 974189 = 365321) (by norm_num)
theorem B974213 : Blo 646304 974213 := bbase (se 4 (by rfl) ⟨91332, by rfl⟩ : syracuseStep 974213 = 182665) (by norm_num)
theorem B1039765 : Blo 646304 1039765 := bbase (se 6 (by rfl) ⟨24369, by rfl⟩ : syracuseStep 1039765 = 48739) (by norm_num)
theorem B974237 : Blo 646304 974237 := bbase (se 3 (by rfl) ⟨182669, by rfl⟩ : syracuseStep 974237 = 365339) (by norm_num)
theorem B974261 : Blo 646304 974261 := bbase (se 5 (by rfl) ⟨45668, by rfl⟩ : syracuseStep 974261 = 91337) (by norm_num)
theorem B974285 : Blo 646304 974285 := bbase (se 3 (by rfl) ⟨182678, by rfl⟩ : syracuseStep 974285 = 365357) (by norm_num)
theorem B974309 : Blo 646304 974309 := bbase (se 4 (by rfl) ⟨91341, by rfl⟩ : syracuseStep 974309 = 182683) (by norm_num)
theorem B974333 : Blo 646304 974333 := bbase (se 3 (by rfl) ⟨182687, by rfl⟩ : syracuseStep 974333 = 365375) (by norm_num)
theorem B974357 : Blo 646304 974357 := bbase (se 6 (by rfl) ⟨22836, by rfl⟩ : syracuseStep 974357 = 45673) (by norm_num)
theorem B974381 : Blo 646304 974381 := bbase (se 3 (by rfl) ⟨182696, by rfl⟩ : syracuseStep 974381 = 365393) (by norm_num)
theorem B1334845 : Blo 646304 1334845 := bbase (se 3 (by rfl) ⟨250283, by rfl⟩ : syracuseStep 1334845 = 500567) (by norm_num)
theorem B974405 : Blo 646304 974405 := bbase (se 4 (by rfl) ⟨91350, by rfl⟩ : syracuseStep 974405 = 182701) (by norm_num)
theorem B2186837 : Blo 646304 2186837 := bbase (se 8 (by rfl) ⟨12813, by rfl⟩ : syracuseStep 2186837 = 25627) (by norm_num)
theorem B974429 : Blo 646304 974429 := bbase (se 3 (by rfl) ⟨182705, by rfl⟩ : syracuseStep 974429 = 365411) (by norm_num)
theorem B974453 : Blo 646304 974453 := bbase (se 5 (by rfl) ⟨45677, by rfl⟩ : syracuseStep 974453 = 91355) (by norm_num)
theorem B974477 : Blo 646304 974477 := bbase (se 3 (by rfl) ⟨182714, by rfl⟩ : syracuseStep 974477 = 365429) (by norm_num)
theorem B974501 : Blo 646304 974501 := bbase (se 4 (by rfl) ⟨91359, by rfl⟩ : syracuseStep 974501 = 182719) (by norm_num)
theorem B974525 : Blo 646304 974525 := bbase (se 3 (by rfl) ⟨182723, by rfl⟩ : syracuseStep 974525 = 365447) (by norm_num)
theorem B974549 : Blo 646304 974549 := bbase (se 7 (by rfl) ⟨11420, by rfl⟩ : syracuseStep 974549 = 22841) (by norm_num)
theorem B974573 : Blo 646304 974573 := bbase (se 3 (by rfl) ⟨182732, by rfl⟩ : syracuseStep 974573 = 365465) (by norm_num)
theorem B974597 : Blo 646304 974597 := bbase (se 4 (by rfl) ⟨91368, by rfl⟩ : syracuseStep 974597 = 182737) (by norm_num)
theorem B974621 : Blo 646304 974621 := bbase (se 3 (by rfl) ⟨182741, by rfl⟩ : syracuseStep 974621 = 365483) (by norm_num)
theorem B974645 : Blo 646304 974645 := bbase (se 5 (by rfl) ⟨45686, by rfl⟩ : syracuseStep 974645 = 91373) (by norm_num)
theorem B974669 : Blo 646304 974669 := bbase (se 3 (by rfl) ⟨182750, by rfl⟩ : syracuseStep 974669 = 365501) (by norm_num)
theorem B974693 : Blo 646304 974693 := bbase (se 4 (by rfl) ⟨91377, by rfl⟩ : syracuseStep 974693 = 182755) (by norm_num)
theorem B974717 : Blo 646304 974717 := bbase (se 3 (by rfl) ⟨182759, by rfl⟩ : syracuseStep 974717 = 365519) (by norm_num)
theorem B974741 : Blo 646304 974741 := bbase (se 6 (by rfl) ⟨22845, by rfl⟩ : syracuseStep 974741 = 45691) (by norm_num)
theorem B974765 : Blo 646304 974765 := bbase (se 3 (by rfl) ⟨182768, by rfl⟩ : syracuseStep 974765 = 365537) (by norm_num)
theorem B1105861 : Blo 646304 1105861 := bbase (se 4 (by rfl) ⟨103674, by rfl⟩ : syracuseStep 1105861 = 207349) (by norm_num)
theorem B974789 : Blo 646304 974789 := bbase (se 4 (by rfl) ⟨91386, by rfl⟩ : syracuseStep 974789 = 182773) (by norm_num)
theorem B778205 : Blo 646304 778205 := bbase (se 3 (by rfl) ⟨145913, by rfl⟩ : syracuseStep 778205 = 291827) (by norm_num)
theorem B974813 : Blo 646304 974813 := bbase (se 3 (by rfl) ⟨182777, by rfl⟩ : syracuseStep 974813 = 365555) (by norm_num)
theorem B974837 : Blo 646304 974837 := bbase (se 5 (by rfl) ⟨45695, by rfl⟩ : syracuseStep 974837 = 91391) (by norm_num)
theorem B2187269 : Blo 646304 2187269 := bbase (se 4 (by rfl) ⟨205056, by rfl⟩ : syracuseStep 2187269 = 410113) (by norm_num)
theorem B974861 : Blo 646304 974861 := bbase (se 3 (by rfl) ⟨182786, by rfl⟩ : syracuseStep 974861 = 365573) (by norm_num)
theorem B974885 : Blo 646304 974885 := bbase (se 4 (by rfl) ⟨91395, by rfl⟩ : syracuseStep 974885 = 182791) (by norm_num)
theorem B974909 : Blo 646304 974909 := bbase (se 3 (by rfl) ⟨182795, by rfl⟩ : syracuseStep 974909 = 365591) (by norm_num)
theorem B974933 : Blo 646304 974933 := bbase (se 8 (by rfl) ⟨5712, by rfl⟩ : syracuseStep 974933 = 11425) (by norm_num)
theorem B974957 : Blo 646304 974957 := bbase (se 3 (by rfl) ⟨182804, by rfl⟩ : syracuseStep 974957 = 365609) (by norm_num)
theorem B974981 : Blo 646304 974981 := bbase (se 4 (by rfl) ⟨91404, by rfl⟩ : syracuseStep 974981 = 182809) (by norm_num)
theorem B1171597 : Blo 646304 1171597 := bbase (se 3 (by rfl) ⟨219674, by rfl⟩ : syracuseStep 1171597 = 439349) (by norm_num)
theorem B975005 : Blo 646304 975005 := bbase (se 3 (by rfl) ⟨182813, by rfl⟩ : syracuseStep 975005 = 365627) (by norm_num)
theorem B975029 : Blo 646304 975029 := bbase (se 5 (by rfl) ⟨45704, by rfl⟩ : syracuseStep 975029 = 91409) (by norm_num)
theorem B975053 : Blo 646304 975053 := bbase (se 3 (by rfl) ⟨182822, by rfl⟩ : syracuseStep 975053 = 365645) (by norm_num)
theorem B975077 : Blo 646304 975077 := bbase (se 4 (by rfl) ⟨91413, by rfl⟩ : syracuseStep 975077 = 182827) (by norm_num)
theorem B975101 : Blo 646304 975101 := bbase (se 3 (by rfl) ⟨182831, by rfl⟩ : syracuseStep 975101 = 365663) (by norm_num)
theorem B778513 : Blo 646304 778513 := bbase (se 2 (by rfl) ⟨291942, by rfl⟩ : syracuseStep 778513 = 583885) (by norm_num)
theorem B975125 : Blo 646304 975125 := bbase (se 6 (by rfl) ⟨22854, by rfl⟩ : syracuseStep 975125 = 45709) (by norm_num)
theorem B975149 : Blo 646304 975149 := bbase (se 3 (by rfl) ⟨182840, by rfl⟩ : syracuseStep 975149 = 365681) (by norm_num)
theorem B1040701 : Blo 646304 1040701 := bbase (se 3 (by rfl) ⟨195131, by rfl⟩ : syracuseStep 1040701 = 390263) (by norm_num)
theorem B975173 : Blo 646304 975173 := bbase (se 4 (by rfl) ⟨91422, by rfl⟩ : syracuseStep 975173 = 182845) (by norm_num)
theorem B975197 : Blo 646304 975197 := bbase (se 3 (by rfl) ⟨182849, by rfl⟩ : syracuseStep 975197 = 365699) (by norm_num)
theorem B1171805 : Blo 646304 1171805 := bbase (se 3 (by rfl) ⟨219713, by rfl⟩ : syracuseStep 1171805 = 439427) (by norm_num)
theorem B975221 : Blo 646304 975221 := bbase (se 5 (by rfl) ⟨45713, by rfl⟩ : syracuseStep 975221 = 91427) (by norm_num)
theorem B975245 : Blo 646304 975245 := bbase (se 3 (by rfl) ⟨182858, by rfl⟩ : syracuseStep 975245 = 365717) (by norm_num)
theorem B975269 : Blo 646304 975269 := bbase (se 4 (by rfl) ⟨91431, by rfl⟩ : syracuseStep 975269 = 182863) (by norm_num)
theorem B2187701 : Blo 646304 2187701 := bbase (se 5 (by rfl) ⟨102548, by rfl⟩ : syracuseStep 2187701 = 205097) (by norm_num)
theorem B4153781 : Blo 646304 4153781 := bbase (se 5 (by rfl) ⟨194708, by rfl⟩ : syracuseStep 4153781 = 389417) (by norm_num)
theorem B975293 : Blo 646304 975293 := bbase (se 3 (by rfl) ⟨182867, by rfl⟩ : syracuseStep 975293 = 365735) (by norm_num)
theorem B1106389 : Blo 646304 1106389 := bbase (se 7 (by rfl) ⟨12965, by rfl⟩ : syracuseStep 1106389 = 25931) (by norm_num)
theorem B975317 : Blo 646304 975317 := bbase (se 7 (by rfl) ⟨11429, by rfl⟩ : syracuseStep 975317 = 22859) (by norm_num)
theorem B975341 : Blo 646304 975341 := bbase (se 3 (by rfl) ⟨182876, by rfl⟩ : syracuseStep 975341 = 365753) (by norm_num)
theorem B975365 : Blo 646304 975365 := bbase (se 4 (by rfl) ⟨91440, by rfl⟩ : syracuseStep 975365 = 182881) (by norm_num)
theorem B975389 : Blo 646304 975389 := bbase (se 3 (by rfl) ⟨182885, by rfl⟩ : syracuseStep 975389 = 365771) (by norm_num)
theorem B975413 : Blo 646304 975413 := bbase (se 5 (by rfl) ⟨45722, by rfl⟩ : syracuseStep 975413 = 91445) (by norm_num)
theorem B975437 : Blo 646304 975437 := bbase (se 3 (by rfl) ⟨182894, by rfl⟩ : syracuseStep 975437 = 365789) (by norm_num)
theorem B811661 : Blo 646304 811661 := bbase (se 3 (by rfl) ⟨152186, by rfl⟩ : syracuseStep 811661 = 304373) (by norm_num)
theorem B778897 : Blo 646304 778897 := bbase (se 2 (by rfl) ⟨292086, by rfl⟩ : syracuseStep 778897 = 584173) (by norm_num)
theorem B778901 : Blo 646304 778901 := bbase (se 6 (by rfl) ⟨18255, by rfl⟩ : syracuseStep 778901 = 36511) (by norm_num)
theorem B2188133 : Blo 646304 2188133 := bbase (se 4 (by rfl) ⟨205137, by rfl⟩ : syracuseStep 2188133 = 410275) (by norm_num)
theorem B779305 : Blo 646304 779305 := bbase (se 2 (by rfl) ⟨292239, by rfl⟩ : syracuseStep 779305 = 584479) (by norm_num)
theorem B2188565 : Blo 646304 2188565 := bbase (se 6 (by rfl) ⟨51294, by rfl⟩ : syracuseStep 2188565 = 102589) (by norm_num)
theorem B1500493 : Blo 646304 1500493 := bbase (se 3 (by rfl) ⟨281342, by rfl⟩ : syracuseStep 1500493 = 562685) (by norm_num)
theorem B1402429 : Blo 646304 1402429 := bbase (se 3 (by rfl) ⟨262955, by rfl⟩ : syracuseStep 1402429 = 525911) (by norm_num)
theorem B1107613 : Blo 646304 1107613 := bbase (se 3 (by rfl) ⟨207677, by rfl⟩ : syracuseStep 1107613 = 415355) (by norm_num)
theorem B2188997 : Blo 646304 2188997 := bbase (se 4 (by rfl) ⟨205218, by rfl⟩ : syracuseStep 2188997 = 410437) (by norm_num)
theorem B1664765 : Blo 646304 1664765 := bbase (se 3 (by rfl) ⟨312143, by rfl⟩ : syracuseStep 1664765 = 624287) (by norm_num)
theorem B2189429 : Blo 646304 2189429 := bbase (se 5 (by rfl) ⟨102629, by rfl⟩ : syracuseStep 2189429 = 205259) (by norm_num)
theorem B780689 : Blo 646304 780689 := bbase (se 2 (by rfl) ⟨292758, by rfl⟩ : syracuseStep 780689 = 585517) (by norm_num)
theorem B2189861 : Blo 646304 2189861 := bbase (se 4 (by rfl) ⟨205299, by rfl⟩ : syracuseStep 2189861 = 410599) (by norm_num)
theorem B780949 : Blo 646304 780949 := bbase (se 6 (by rfl) ⟨18303, by rfl⟩ : syracuseStep 780949 = 36607) (by norm_num)
theorem B780997 : Blo 646304 780997 := bbase (se 4 (by rfl) ⟨73218, by rfl⟩ : syracuseStep 780997 = 146437) (by norm_num)
theorem B3697397 : Blo 646304 3697397 := bbase (se 5 (by rfl) ⟨173315, by rfl⟩ : syracuseStep 3697397 = 346631) (by norm_num)
theorem B1665917 : Blo 646304 1665917 := bbase (se 3 (by rfl) ⟨312359, by rfl⟩ : syracuseStep 1665917 = 624719) (by norm_num)
theorem B9989077 : Blo 646304 9989077 := bbase (se 7 (by rfl) ⟨117059, by rfl⟩ : syracuseStep 9989077 = 234119) (by norm_num)
theorem B2190293 : Blo 646304 2190293 := bbase (se 7 (by rfl) ⟨25667, by rfl⟩ : syracuseStep 2190293 = 51335) (by norm_num)
theorem B2190725 : Blo 646304 2190725 := bbase (se 4 (by rfl) ⟨205380, by rfl⟩ : syracuseStep 2190725 = 410761) (by norm_num)
theorem B1502885 : Blo 646304 1502885 := bbase (se 4 (by rfl) ⟨140895, by rfl⟩ : syracuseStep 1502885 = 281791) (by norm_num)
theorem B2191157 : Blo 646304 2191157 := bbase (se 5 (by rfl) ⟨102710, by rfl⟩ : syracuseStep 2191157 = 205421) (by norm_num)
theorem B3698581 : Blo 646304 3698581 := bbase (se 6 (by rfl) ⟨86685, by rfl⟩ : syracuseStep 3698581 = 173371) (by norm_num)
theorem B1666981 : Blo 646304 1666981 := bbase (se 4 (by rfl) ⟨156279, by rfl⟩ : syracuseStep 1666981 = 312559) (by norm_num)
theorem B4911029 : Blo 646304 4911029 := bbase (se 5 (by rfl) ⟨230204, by rfl⟩ : syracuseStep 4911029 = 460409) (by norm_num)
theorem B3272885 : Blo 646304 3272885 := bbase (se 5 (by rfl) ⟨153416, by rfl⟩ : syracuseStep 3272885 = 306833) (by norm_num)
theorem B2191589 : Blo 646304 2191589 := bbase (se 4 (by rfl) ⟨205461, by rfl⟩ : syracuseStep 2191589 = 410923) (by norm_num)
theorem B1667557 : Blo 646304 1667557 := bbase (se 4 (by rfl) ⟨156333, by rfl⟩ : syracuseStep 1667557 = 312667) (by norm_num)
theorem B2192021 : Blo 646304 2192021 := bbase (se 6 (by rfl) ⟨51375, by rfl⟩ : syracuseStep 2192021 = 102751) (by norm_num)
theorem B2454421 : Blo 646304 2454421 := bbase (se 6 (by rfl) ⟨57525, by rfl⟩ : syracuseStep 2454421 = 115051) (by norm_num)
theorem B2192453 : Blo 646304 2192453 := bbase (se 4 (by rfl) ⟨205542, by rfl⟩ : syracuseStep 2192453 = 411085) (by norm_num)
theorem B3110069 : Blo 646304 3110069 := bbase (se 5 (by rfl) ⟨145784, by rfl⟩ : syracuseStep 3110069 = 291569) (by norm_num)
theorem B2454725 : Blo 646304 2454725 := bbase (se 4 (by rfl) ⟨230130, by rfl⟩ : syracuseStep 2454725 = 460261) (by norm_num)
theorem B3274181 : Blo 646304 3274181 := bbase (se 4 (by rfl) ⟨306954, by rfl⟩ : syracuseStep 3274181 = 613909) (by norm_num)
theorem B2192885 : Blo 646304 2192885 := bbase (se 5 (by rfl) ⟨102791, by rfl⟩ : syracuseStep 2192885 = 205583) (by norm_num)
theorem B1635997 : Blo 646304 1635997 := bbase (se 3 (by rfl) ⟨306749, by rfl⟩ : syracuseStep 1635997 = 613499) (by norm_num)
theorem B1111733 : Blo 646304 1111733 := bbase (se 5 (by rfl) ⟨52112, by rfl⟩ : syracuseStep 1111733 = 104225) (by norm_num)
theorem B1636109 : Blo 646304 1636109 := bbase (se 3 (by rfl) ⟨306770, by rfl⟩ : syracuseStep 1636109 = 613541) (by norm_num)
theorem B3700565 : Blo 646304 3700565 := bbase (se 9 (by rfl) ⟨10841, by rfl⟩ : syracuseStep 3700565 = 21683) (by norm_num)
theorem B2193317 : Blo 646304 2193317 := bbase (se 4 (by rfl) ⟨205623, by rfl⟩ : syracuseStep 2193317 = 411247) (by norm_num)
theorem B1636301 : Blo 646304 1636301 := bbase (se 3 (by rfl) ⟨306806, by rfl⟩ : syracuseStep 1636301 = 613613) (by norm_num)
theorem B1636645 : Blo 646304 1636645 := bbase (se 4 (by rfl) ⟨153435, by rfl⟩ : syracuseStep 1636645 = 306871) (by norm_num)
theorem B2193749 : Blo 646304 2193749 := bbase (se 10 (by rfl) ⟨3213, by rfl⟩ : syracuseStep 2193749 = 6427) (by norm_num)
theorem B1636757 : Blo 646304 1636757 := bbase (se 6 (by rfl) ⟨38361, by rfl⟩ : syracuseStep 1636757 = 76723) (by norm_num)
theorem B1603997 : Blo 646304 1603997 := bbase (se 3 (by rfl) ⟨300749, by rfl⟩ : syracuseStep 1603997 = 601499) (by norm_num)
theorem B3111493 : Blo 646304 3111493 := bbase (se 4 (by rfl) ⟨291702, by rfl⟩ : syracuseStep 3111493 = 583405) (by norm_num)
theorem B1407557 : Blo 646304 1407557 := bbase (se 4 (by rfl) ⟨131958, by rfl⟩ : syracuseStep 1407557 = 263917) (by norm_num)
theorem B1636949 : Blo 646304 1636949 := bbase (se 8 (by rfl) ⟨9591, by rfl⟩ : syracuseStep 1636949 = 19183) (by norm_num)
theorem B948925 : Blo 646304 948925 := bbase (se 3 (by rfl) ⟨177923, by rfl⟩ : syracuseStep 948925 = 355847) (by norm_num)
theorem B3275477 : Blo 646304 3275477 := bbase (se 7 (by rfl) ⟨38384, by rfl⟩ : syracuseStep 3275477 = 76769) (by norm_num)
theorem B6224597 : Blo 646304 6224597 := bbase (se 7 (by rfl) ⟨72944, by rfl⟩ : syracuseStep 6224597 = 145889) (by norm_num)
theorem B2194181 : Blo 646304 2194181 := bbase (se 4 (by rfl) ⟨205704, by rfl⟩ : syracuseStep 2194181 = 411409) (by norm_num)
theorem B818029 : Blo 646304 818029 := bbase (se 3 (by rfl) ⟨153380, by rfl⟩ : syracuseStep 818029 = 306761) (by norm_num)
theorem B1637293 : Blo 646304 1637293 := bbase (se 3 (by rfl) ⟨306992, by rfl⟩ : syracuseStep 1637293 = 613985) (by norm_num)
theorem B818201 : Blo 646304 818201 := bbase (se 2 (by rfl) ⟨306825, by rfl⟩ : syracuseStep 818201 = 613651) (by norm_num)
theorem B1637405 : Blo 646304 1637405 := bbase (se 3 (by rfl) ⟨307013, by rfl⟩ : syracuseStep 1637405 = 614027) (by norm_num)
theorem B818257 : Blo 646304 818257 := bbase (se 2 (by rfl) ⟨306846, by rfl⟩ : syracuseStep 818257 = 613693) (by norm_num)
theorem B2948197 : Blo 646304 2948197 := bbase (se 4 (by rfl) ⟨276393, by rfl⟩ : syracuseStep 2948197 = 552787) (by norm_num)
theorem B818353 : Blo 646304 818353 := bbase (se 2 (by rfl) ⟨306882, by rfl⟩ : syracuseStep 818353 = 613765) (by norm_num)
theorem B2194613 : Blo 646304 2194613 := bbase (se 5 (by rfl) ⟨102872, by rfl⟩ : syracuseStep 2194613 = 205745) (by norm_num)
theorem B1637597 : Blo 646304 1637597 := bbase (se 3 (by rfl) ⟨307049, by rfl⟩ : syracuseStep 1637597 = 614099) (by norm_num)
theorem B2489573 : Blo 646304 2489573 := bbase (se 4 (by rfl) ⟨233397, by rfl⟩ : syracuseStep 2489573 = 466795) (by norm_num)
theorem B2456837 : Blo 646304 2456837 := bbase (se 4 (by rfl) ⟨230328, by rfl⟩ : syracuseStep 2456837 = 460657) (by norm_num)
theorem B818525 : Blo 646304 818525 := bbase (se 3 (by rfl) ⟨153473, by rfl⟩ : syracuseStep 818525 = 306947) (by norm_num)
theorem B818581 : Blo 646304 818581 := bbase (se 6 (by rfl) ⟨19185, by rfl⟩ : syracuseStep 818581 = 38371) (by norm_num)
theorem B18906581 : Blo 646304 18906581 := bbase (se 7 (by rfl) ⟨221561, by rfl⟩ : syracuseStep 18906581 = 443123) (by norm_num)
theorem B818677 : Blo 646304 818677 := bbase (se 5 (by rfl) ⟨38375, by rfl⟩ : syracuseStep 818677 = 76751) (by norm_num)
theorem B2457125 : Blo 646304 2457125 := bbase (se 4 (by rfl) ⟨230355, by rfl⟩ : syracuseStep 2457125 = 460711) (by norm_num)
theorem B1310261 : Blo 646304 1310261 := bbase (se 5 (by rfl) ⟨61418, by rfl⟩ : syracuseStep 1310261 = 122837) (by norm_num)
theorem B1637941 : Blo 646304 1637941 := bbase (se 5 (by rfl) ⟨76778, by rfl⟩ : syracuseStep 1637941 = 153557) (by norm_num)
theorem B818849 : Blo 646304 818849 := bbase (se 2 (by rfl) ⟨307068, by rfl⟩ : syracuseStep 818849 = 614137) (by norm_num)
theorem B1638053 : Blo 646304 1638053 := bbase (se 4 (by rfl) ⟨153567, by rfl⟩ : syracuseStep 1638053 = 307135) (by norm_num)
theorem B818905 : Blo 646304 818905 := bbase (se 2 (by rfl) ⟨307089, by rfl⟩ : syracuseStep 818905 = 614179) (by norm_num)
theorem B819001 : Blo 646304 819001 := bbase (se 2 (by rfl) ⟨307125, by rfl⟩ : syracuseStep 819001 = 614251) (by norm_num)
theorem B5930837 : Blo 646304 5930837 := bbase (se 9 (by rfl) ⟨17375, by rfl⟩ : syracuseStep 5930837 = 34751) (by norm_num)
theorem B1638245 : Blo 646304 1638245 := bbase (se 4 (by rfl) ⟨153585, by rfl⟩ : syracuseStep 1638245 = 307171) (by norm_num)
theorem B6651829 : Blo 646304 6651829 := bbase (se 5 (by rfl) ⟨311804, by rfl⟩ : syracuseStep 6651829 = 623609) (by norm_num)
theorem B819173 : Blo 646304 819173 := bbase (se 4 (by rfl) ⟨76797, by rfl⟩ : syracuseStep 819173 = 153595) (by norm_num)
theorem B3276773 : Blo 646304 3276773 := bbase (se 4 (by rfl) ⟨307197, by rfl⟩ : syracuseStep 3276773 = 614395) (by norm_num)
theorem B3702773 : Blo 646304 3702773 := bbase (se 5 (by rfl) ⟨173567, by rfl⟩ : syracuseStep 3702773 = 347135) (by norm_num)
theorem B983171 : Blo 646304 983171 := bstep (se 1 (by rfl) ⟨737378, by rfl⟩ : syracuseStep 983171 = 1474757) B1474757
theorem B2458097 : Blo 646304 2458097 := bstep (se 2 (by rfl) ⟨921786, by rfl⟩ : syracuseStep 2458097 = 1843573) B1843573
theorem B819715 : Blo 646304 819715 := bstep (se 1 (by rfl) ⟨614786, by rfl⟩ : syracuseStep 819715 = 1229573) B1229573
theorem B819811 : Blo 646304 819811 := bstep (se 1 (by rfl) ⟨614858, by rfl⟩ : syracuseStep 819811 = 1229717) B1229717
theorem B1475185 : Blo 646304 1475185 := bstep (se 2 (by rfl) ⟨553194, by rfl⟩ : syracuseStep 1475185 = 1106389) B1106389
theorem B1639025 : Blo 646304 1639025 := bstep (se 2 (by rfl) ⟨614634, by rfl⟩ : syracuseStep 1639025 = 1229269) B1229269
theorem B1639075 : Blo 646304 1639075 := bstep (se 1 (by rfl) ⟨1229306, by rfl⟩ : syracuseStep 1639075 = 2458613) B2458613
theorem B3113741 : Blo 646304 3113741 := bstep (se 3 (by rfl) ⟨583826, by rfl⟩ : syracuseStep 3113741 = 1167653) B1167653
theorem B1639217 : Blo 646304 1639217 := bstep (se 2 (by rfl) ⟨614706, by rfl⟩ : syracuseStep 1639217 = 1229413) B1229413
theorem B1967021 : Blo 646304 1967021 := bstep (se 3 (by rfl) ⟨368816, by rfl⟩ : syracuseStep 1967021 = 737633) B737633
theorem B3277745 : Blo 646304 3277745 := bstep (se 2 (by rfl) ⟨1229154, by rfl⟩ : syracuseStep 3277745 = 2458309) B2458309
theorem B5932003 : Blo 646304 5932003 := bstep (se 1 (by rfl) ⟨4449002, by rfl⟩ : syracuseStep 5932003 = 8898005) B8898005
theorem B3376163 : Blo 646304 3376163 := bstep (se 1 (by rfl) ⟨2532122, by rfl⟩ : syracuseStep 3376163 = 5064245) B5064245
theorem B820307 : Blo 646304 820307 := bstep (se 1 (by rfl) ⟨615230, by rfl⟩ : syracuseStep 820307 = 1230461) B1230461
theorem B6227057 : Blo 646304 6227057 := bstep (se 2 (by rfl) ⟨2335146, by rfl⟩ : syracuseStep 6227057 = 4670293) B4670293
theorem B7013573 : Blo 646304 7013573 := bstep (se 4 (by rfl) ⟨657522, by rfl⟩ : syracuseStep 7013573 = 1315045) B1315045
theorem B3507461 : Blo 646304 3507461 := bstep (se 4 (by rfl) ⟨328824, by rfl⟩ : syracuseStep 3507461 = 657649) B657649
theorem B1312451 : Blo 646304 1312451 := bstep (se 1 (by rfl) ⟨984338, by rfl⟩ : syracuseStep 1312451 = 1968677) B1968677
theorem B2164429 : Blo 646304 2164429 := bstep (se 3 (by rfl) ⟨405830, by rfl⟩ : syracuseStep 2164429 = 811661) B811661
theorem B1312483 : Blo 646304 1312483 := bstep (se 1 (by rfl) ⟨984362, by rfl⟩ : syracuseStep 1312483 = 1968725) B1968725
theorem B7374563 : Blo 646304 7374563 := bstep (se 1 (by rfl) ⟨5530922, by rfl⟩ : syracuseStep 7374563 = 11061845) B11061845
theorem B1640209 : Blo 646304 1640209 := bstep (se 2 (by rfl) ⟨615078, by rfl⟩ : syracuseStep 1640209 = 1230157) B1230157
theorem B2000657 : Blo 646304 2000657 := bstep (se 2 (by rfl) ⟨750246, by rfl⟩ : syracuseStep 2000657 = 1500493) B1500493
theorem B821011 : Blo 646304 821011 := bstep (se 1 (by rfl) ⟨615758, by rfl⟩ : syracuseStep 821011 = 1231517) B1231517
theorem B821107 : Blo 646304 821107 := bstep (se 1 (by rfl) ⟨615830, by rfl⟩ : syracuseStep 821107 = 1231661) B1231661
theorem B2459555 : Blo 646304 2459555 := bstep (se 1 (by rfl) ⟨1844666, by rfl⟩ : syracuseStep 2459555 = 3689333) B3689333
theorem B1640483 : Blo 646304 1640483 := bstep (se 1 (by rfl) ⟨1230362, by rfl⟩ : syracuseStep 1640483 = 2460725) B2460725
theorem B1869905 : Blo 646304 1869905 := bstep (se 2 (by rfl) ⟨701214, by rfl⟩ : syracuseStep 1869905 = 1402429) B1402429
theorem B4917347 : Blo 646304 4917347 := bstep (se 1 (by rfl) ⟨3688010, by rfl⟩ : syracuseStep 4917347 = 7376021) B7376021
theorem B1640675 : Blo 646304 1640675 := bstep (se 1 (by rfl) ⟨1230506, by rfl⟩ : syracuseStep 1640675 = 2461013) B2461013
theorem B3279203 : Blo 646304 3279203 := bstep (se 1 (by rfl) ⟨2459402, by rfl⟩ : syracuseStep 3279203 = 4918805) B4918805
theorem B821603 : Blo 646304 821603 := bstep (se 1 (by rfl) ⟨616202, by rfl⟩ : syracuseStep 821603 = 1232405) B1232405
theorem B7473521 : Blo 646304 7473521 := bstep (se 2 (by rfl) ⟨2802570, by rfl⟩ : syracuseStep 7473521 = 5605141) B5605141
theorem B1477091 : Blo 646304 1477091 := bstep (se 1 (by rfl) ⟨1107818, by rfl⟩ : syracuseStep 1477091 = 2215637) B2215637
theorem B691075 : Blo 646304 691075 := bstep (se 1 (by rfl) ⟨518306, by rfl⟩ : syracuseStep 691075 = 1036613) B1036613
theorem B2460557 : Blo 646304 2460557 := bstep (se 3 (by rfl) ⟨461354, by rfl⟩ : syracuseStep 2460557 = 922709) B922709
theorem B4164493 : Blo 646304 4164493 := bstep (se 3 (by rfl) ⟨780842, by rfl⟩ : syracuseStep 4164493 = 1561685) B1561685
theorem B822307 : Blo 646304 822307 := bstep (se 1 (by rfl) ⟨616730, by rfl⟩ : syracuseStep 822307 = 1233461) B1233461
theorem B920659 : Blo 646304 920659 := bstep (se 1 (by rfl) ⟨690494, by rfl⟩ : syracuseStep 920659 = 1380989) B1380989
theorem B822403 : Blo 646304 822403 := bstep (se 1 (by rfl) ⟨616802, by rfl⟩ : syracuseStep 822403 = 1233605) B1233605
theorem B3280013 : Blo 646304 3280013 := bstep (se 3 (by rfl) ⟨615002, by rfl⟩ : syracuseStep 3280013 = 1230005) B1230005
theorem B1641617 : Blo 646304 1641617 := bstep (se 2 (by rfl) ⟨615606, by rfl⟩ : syracuseStep 1641617 = 1231213) B1231213
theorem B1641667 : Blo 646304 1641667 := bstep (se 1 (by rfl) ⟨1231250, by rfl⟩ : syracuseStep 1641667 = 2462501) B2462501
theorem B1641809 : Blo 646304 1641809 := bstep (se 2 (by rfl) ⟨615678, by rfl⟩ : syracuseStep 1641809 = 1231357) B1231357
theorem B921137 : Blo 646304 921137 := bstep (se 2 (by rfl) ⟨345426, by rfl⟩ : syracuseStep 921137 = 690853) B690853
theorem B822899 : Blo 646304 822899 := bstep (se 1 (by rfl) ⟨617174, by rfl⟩ : syracuseStep 822899 = 1234349) B1234349
theorem B921251 : Blo 646304 921251 := bstep (se 1 (by rfl) ⟨690938, by rfl⟩ : syracuseStep 921251 = 1381877) B1381877
theorem B986833 : Blo 646304 986833 := bstep (se 2 (by rfl) ⟨370062, by rfl⟩ : syracuseStep 986833 = 740125) B740125
theorem B921331 : Blo 646304 921331 := bstep (se 1 (by rfl) ⟨690998, by rfl⟩ : syracuseStep 921331 = 1381997) B1381997
theorem B1052497 : Blo 646304 1052497 := bstep (se 2 (by rfl) ⟨394686, by rfl⟩ : syracuseStep 1052497 = 789373) B789373
theorem B692083 : Blo 646304 692083 := bstep (se 1 (by rfl) ⟨519062, by rfl⟩ : syracuseStep 692083 = 1038125) B1038125
theorem B1970257 : Blo 646304 1970257 := bstep (se 2 (by rfl) ⟨738846, by rfl⟩ : syracuseStep 1970257 = 1477693) B1477693
theorem B2330765 : Blo 646304 2330765 := bstep (se 3 (by rfl) ⟨437018, by rfl⟩ : syracuseStep 2330765 = 874037) B874037
theorem B1478915 : Blo 646304 1478915 := bstep (se 1 (by rfl) ⟨1109186, by rfl⟩ : syracuseStep 1478915 = 2218373) B2218373
theorem B921889 : Blo 646304 921889 := bstep (se 2 (by rfl) ⟨345708, by rfl⟩ : syracuseStep 921889 = 691417) B691417
theorem B1642801 : Blo 646304 1642801 := bstep (se 2 (by rfl) ⟨616050, by rfl⟩ : syracuseStep 1642801 = 1232101) B1232101
theorem B1380817 : Blo 646304 1380817 := bstep (se 2 (by rfl) ⟨517806, by rfl⟩ : syracuseStep 1380817 = 1035613) B1035613
theorem B692707 : Blo 646304 692707 := bstep (se 1 (by rfl) ⟨519530, by rfl⟩ : syracuseStep 692707 = 1039061) B1039061
theorem B3543587 : Blo 646304 3543587 := bstep (se 1 (by rfl) ⟨2657690, by rfl⟩ : syracuseStep 3543587 = 5315381) B5315381
theorem B1643075 : Blo 646304 1643075 := bstep (se 1 (by rfl) ⟨1232306, by rfl⟩ : syracuseStep 1643075 = 2464613) B2464613
theorem B1643267 : Blo 646304 1643267 := bstep (se 1 (by rfl) ⟨1232450, by rfl⟩ : syracuseStep 1643267 = 2464901) B2464901
theorem B1971011 : Blo 646304 1971011 := bstep (se 1 (by rfl) ⟨1478258, by rfl⟩ : syracuseStep 1971011 = 2956517) B2956517
theorem B2462669 : Blo 646304 2462669 := bstep (se 3 (by rfl) ⟨461750, by rfl⟩ : syracuseStep 2462669 = 923501) B923501
theorem B922595 : Blo 646304 922595 := bstep (se 1 (by rfl) ⟨691946, by rfl⟩ : syracuseStep 922595 = 1383893) B1383893
theorem B9999557 : Blo 646304 9999557 := bstep (se 4 (by rfl) ⟨937458, by rfl⟩ : syracuseStep 9999557 = 1874917) B1874917
theorem B12424589 : Blo 646304 12424589 := bstep (se 3 (by rfl) ⟨2329610, by rfl⟩ : syracuseStep 12424589 = 4659221) B4659221
theorem B1840589 : Blo 646304 1840589 := bstep (se 3 (by rfl) ⟨345110, by rfl⟩ : syracuseStep 1840589 = 690221) B690221
theorem B1840657 : Blo 646304 1840657 := bstep (se 2 (by rfl) ⟨690246, by rfl⟩ : syracuseStep 1840657 = 1380493) B1380493
theorem B923233 : Blo 646304 923233 := bstep (se 2 (by rfl) ⟨346212, by rfl⟩ : syracuseStep 923233 = 692425) B692425
theorem B3937933 : Blo 646304 3937933 := bstep (se 3 (by rfl) ⟨738362, by rfl⟩ : syracuseStep 3937933 = 1476725) B1476725
theorem B1644209 : Blo 646304 1644209 := bstep (se 2 (by rfl) ⟨616578, by rfl⟩ : syracuseStep 1644209 = 1233157) B1233157
theorem B923347 : Blo 646304 923347 := bstep (se 1 (by rfl) ⟨692510, by rfl⟩ : syracuseStep 923347 = 1385021) B1385021
theorem B1644259 : Blo 646304 1644259 := bstep (se 1 (by rfl) ⟨1233194, by rfl⟩ : syracuseStep 1644259 = 2466389) B2466389
theorem B1578737 : Blo 646304 1578737 := bstep (se 2 (by rfl) ⟨592026, by rfl⟩ : syracuseStep 1578737 = 1184053) B1184053
theorem B2463473 : Blo 646304 2463473 := bstep (se 2 (by rfl) ⟨923802, by rfl⟩ : syracuseStep 2463473 = 1847605) B1847605
theorem B1840931 : Blo 646304 1840931 := bstep (se 1 (by rfl) ⟨1380698, by rfl⟩ : syracuseStep 1840931 = 2761397) B2761397
theorem B3610403 : Blo 646304 3610403 := bstep (se 1 (by rfl) ⟨2707802, by rfl⟩ : syracuseStep 3610403 = 5415605) B5415605
theorem B1644401 : Blo 646304 1644401 := bstep (se 2 (by rfl) ⟨616650, by rfl⟩ : syracuseStep 1644401 = 1233301) B1233301
theorem B890785 : Blo 646304 890785 := bstep (se 2 (by rfl) ⟨334044, by rfl⟩ : syracuseStep 890785 = 668089) B668089
theorem B1382321 : Blo 646304 1382321 := bstep (se 2 (by rfl) ⟨518370, by rfl⟩ : syracuseStep 1382321 = 1036741) B1036741
theorem B1382339 : Blo 646304 1382339 := bstep (se 1 (by rfl) ⟨1036754, by rfl⟩ : syracuseStep 1382339 = 2073509) B2073509
theorem B3282929 : Blo 646304 3282929 := bstep (se 2 (by rfl) ⟨1231098, by rfl⟩ : syracuseStep 3282929 = 2462197) B2462197
theorem B727123 : Blo 646304 727123 := bstep (se 1 (by rfl) ⟨545342, by rfl⟩ : syracuseStep 727123 = 1090685) B1090685
theorem B21043313 : Blo 646304 21043313 := bstep (se 2 (by rfl) ⟨7891242, by rfl⟩ : syracuseStep 21043313 = 15782485) B15782485
theorem B16849093 : Blo 646304 16849093 := bstep (se 4 (by rfl) ⟨1579602, by rfl⟩ : syracuseStep 16849093 = 3159205) B3159205
theorem B727267 : Blo 646304 727267 := bstep (se 1 (by rfl) ⟨545450, by rfl⟩ : syracuseStep 727267 = 1090901) B1090901
theorem B727411 : Blo 646304 727411 := bstep (se 1 (by rfl) ⟨545558, by rfl⟩ : syracuseStep 727411 = 1091117) B1091117
theorem B2464141 : Blo 646304 2464141 := bstep (se 3 (by rfl) ⟨462026, by rfl⟩ : syracuseStep 2464141 = 924053) B924053
theorem B2071021 : Blo 646304 2071021 := bstep (se 3 (by rfl) ⟨388316, by rfl⟩ : syracuseStep 2071021 = 776633) B776633
theorem B727555 : Blo 646304 727555 := bstep (se 1 (by rfl) ⟨545666, by rfl⟩ : syracuseStep 727555 = 1091333) B1091333
theorem B2103853 : Blo 646304 2103853 := bstep (se 3 (by rfl) ⟨394472, by rfl⟩ : syracuseStep 2103853 = 788945) B788945
theorem B1841773 : Blo 646304 1841773 := bstep (se 3 (by rfl) ⟨345332, by rfl⟩ : syracuseStep 1841773 = 690665) B690665
theorem B727699 : Blo 646304 727699 := bstep (se 1 (by rfl) ⟨545774, by rfl⟩ : syracuseStep 727699 = 1091549) B1091549
theorem B1841933 : Blo 646304 1841933 := bstep (se 3 (by rfl) ⟨345362, by rfl⟩ : syracuseStep 1841933 = 690725) B690725
theorem B727843 : Blo 646304 727843 := bstep (se 1 (by rfl) ⟨545882, by rfl⟩ : syracuseStep 727843 = 1091765) B1091765
theorem B1645393 : Blo 646304 1645393 := bstep (se 2 (by rfl) ⟨617022, by rfl⟩ : syracuseStep 1645393 = 1234045) B1234045
theorem B6331277 : Blo 646304 6331277 := bstep (se 3 (by rfl) ⟨1187114, by rfl⟩ : syracuseStep 6331277 = 2374229) B2374229
theorem B727987 : Blo 646304 727987 := bstep (se 1 (by rfl) ⟨545990, by rfl⟩ : syracuseStep 727987 = 1091981) B1091981
theorem B1842115 : Blo 646304 1842115 := bstep (se 1 (by rfl) ⟨1381586, by rfl⟩ : syracuseStep 1842115 = 2763173) B2763173
theorem B924691 : Blo 646304 924691 := bstep (se 1 (by rfl) ⟨693518, by rfl⟩ : syracuseStep 924691 = 1387037) B1387037
theorem B728131 : Blo 646304 728131 := bstep (se 1 (by rfl) ⟨546098, by rfl⟩ : syracuseStep 728131 = 1092197) B1092197
theorem B2104397 : Blo 646304 2104397 := bstep (se 3 (by rfl) ⟨394574, by rfl⟩ : syracuseStep 2104397 = 789149) B789149
theorem B1645667 : Blo 646304 1645667 := bstep (se 1 (by rfl) ⟨1234250, by rfl⟩ : syracuseStep 1645667 = 2468501) B2468501
theorem B2464931 : Blo 646304 2464931 := bstep (se 1 (by rfl) ⟨1848698, by rfl⟩ : syracuseStep 2464931 = 3697397) B3697397
theorem B4201649 : Blo 646304 4201649 := bstep (se 2 (by rfl) ⟨1575618, by rfl⟩ : syracuseStep 4201649 = 3151237) B3151237
theorem B1973443 : Blo 646304 1973443 := bstep (se 1 (by rfl) ⟨1480082, by rfl⟩ : syracuseStep 1973443 = 2960165) B2960165
theorem B728275 : Blo 646304 728275 := bstep (se 1 (by rfl) ⟨546206, by rfl⟩ : syracuseStep 728275 = 1092413) B1092413
theorem B1645859 : Blo 646304 1645859 := bstep (se 1 (by rfl) ⟨1234394, by rfl⟩ : syracuseStep 1645859 = 2468789) B2468789
theorem B4922693 : Blo 646304 4922693 := bstep (se 4 (by rfl) ⟨461502, by rfl⟩ : syracuseStep 4922693 = 923005) B923005
theorem B728419 : Blo 646304 728419 := bstep (se 1 (by rfl) ⟨546314, by rfl⟩ : syracuseStep 728419 = 1092629) B1092629
theorem B3284387 : Blo 646304 3284387 := bstep (se 1 (by rfl) ⟨2463290, by rfl⟩ : syracuseStep 3284387 = 4926581) B4926581
theorem B728563 : Blo 646304 728563 := bstep (se 1 (by rfl) ⟨546422, by rfl⟩ : syracuseStep 728563 = 1092845) B1092845
theorem B2629169 : Blo 646304 2629169 := bstep (se 2 (by rfl) ⟨985938, by rfl⟩ : syracuseStep 2629169 = 1971877) B1971877
theorem B6233669 : Blo 646304 6233669 := bstep (se 4 (by rfl) ⟨584406, by rfl⟩ : syracuseStep 6233669 = 1168813) B1168813
theorem B728707 : Blo 646304 728707 := bstep (se 1 (by rfl) ⟨546530, by rfl⟩ : syracuseStep 728707 = 1093061) B1093061
theorem B5119685 : Blo 646304 5119685 := bstep (se 4 (by rfl) ⟨479970, by rfl⟩ : syracuseStep 5119685 = 959941) B959941
theorem B728851 : Blo 646304 728851 := bstep (se 1 (by rfl) ⟨546638, by rfl⟩ : syracuseStep 728851 = 1093277) B1093277
theorem B2465585 : Blo 646304 2465585 := bstep (se 2 (by rfl) ⟨924594, by rfl⟩ : syracuseStep 2465585 = 1849189) B1849189
theorem B3514225 : Blo 646304 3514225 := bstep (se 2 (by rfl) ⟨1317834, by rfl⟩ : syracuseStep 3514225 = 2635669) B2635669
theorem B1384337 : Blo 646304 1384337 := bstep (se 2 (by rfl) ⟨519126, by rfl⟩ : syracuseStep 1384337 = 1038253) B1038253
theorem B728995 : Blo 646304 728995 := bstep (se 1 (by rfl) ⟨546746, by rfl⟩ : syracuseStep 728995 = 1093493) B1093493
theorem B729139 : Blo 646304 729139 := bstep (se 1 (by rfl) ⟨546854, by rfl⟩ : syracuseStep 729139 = 1093709) B1093709
theorem B925825 : Blo 646304 925825 := bstep (se 2 (by rfl) ⟨347184, by rfl⟩ : syracuseStep 925825 = 694369) B694369
theorem B2072753 : Blo 646304 2072753 := bstep (se 2 (by rfl) ⟨777282, by rfl⟩ : syracuseStep 2072753 = 1554565) B1554565
theorem B729283 : Blo 646304 729283 := bstep (se 1 (by rfl) ⟨546962, by rfl⟩ : syracuseStep 729283 = 1093925) B1093925
theorem B3285197 : Blo 646304 3285197 := bstep (se 3 (by rfl) ⟨615974, by rfl⟩ : syracuseStep 3285197 = 1231949) B1231949
theorem B925921 : Blo 646304 925921 := bstep (se 2 (by rfl) ⟨347220, by rfl⟩ : syracuseStep 925921 = 694441) B694441
theorem B1843505 : Blo 646304 1843505 := bstep (se 2 (by rfl) ⟨691314, by rfl⟩ : syracuseStep 1843505 = 1382629) B1382629
theorem B7119173 : Blo 646304 7119173 := bstep (se 4 (by rfl) ⟨667422, by rfl⟩ : syracuseStep 7119173 = 1334845) B1334845
theorem B729427 : Blo 646304 729427 := bstep (se 1 (by rfl) ⟨547070, by rfl⟩ : syracuseStep 729427 = 1094141) B1094141
theorem B2761073 : Blo 646304 2761073 := bstep (se 2 (by rfl) ⟨1035402, by rfl⟩ : syracuseStep 2761073 = 2070805) B2070805
theorem B1384867 : Blo 646304 1384867 := bstep (se 1 (by rfl) ⟨1038650, by rfl⟩ : syracuseStep 1384867 = 2077301) B2077301
theorem B729571 : Blo 646304 729571 := bstep (se 1 (by rfl) ⟨547178, by rfl⟩ : syracuseStep 729571 = 1094357) B1094357
theorem B926305 : Blo 646304 926305 := bstep (se 2 (by rfl) ⟨347364, by rfl⟩ : syracuseStep 926305 = 694729) B694729
theorem B729715 : Blo 646304 729715 := bstep (se 1 (by rfl) ⟨547286, by rfl⟩ : syracuseStep 729715 = 1094573) B1094573
theorem B729859 : Blo 646304 729859 := bstep (se 1 (by rfl) ⟨547394, by rfl⟩ : syracuseStep 729859 = 1094789) B1094789
theorem B2073379 : Blo 646304 2073379 := bstep (se 1 (by rfl) ⟨1555034, by rfl⟩ : syracuseStep 2073379 = 3110069) B3110069
theorem B5907269 : Blo 646304 5907269 := bstep (se 4 (by rfl) ⟨553806, by rfl⟩ : syracuseStep 5907269 = 1107613) B1107613
theorem B730003 : Blo 646304 730003 := bstep (se 1 (by rfl) ⟨547502, by rfl⟩ : syracuseStep 730003 = 1095005) B1095005
theorem B730147 : Blo 646304 730147 := bstep (se 1 (by rfl) ⟨547610, by rfl⟩ : syracuseStep 730147 = 1095221) B1095221
theorem B1090705 : Blo 646304 1090705 := bstep (se 2 (by rfl) ⟨409014, by rfl⟩ : syracuseStep 1090705 = 818029) B818029
theorem B1090739 : Blo 646304 1090739 := bstep (se 1 (by rfl) ⟨818054, by rfl⟩ : syracuseStep 1090739 = 1636109) B1636109
theorem B730291 : Blo 646304 730291 := bstep (se 1 (by rfl) ⟨547718, by rfl⟩ : syracuseStep 730291 = 1095437) B1095437
theorem B2467043 : Blo 646304 2467043 := bstep (se 1 (by rfl) ⟨1850282, by rfl⟩ : syracuseStep 2467043 = 3700565) B3700565
theorem B1844461 : Blo 646304 1844461 := bstep (se 3 (by rfl) ⟨345836, by rfl⟩ : syracuseStep 1844461 = 691673) B691673
theorem B2467057 : Blo 646304 2467057 := bstep (se 2 (by rfl) ⟨925146, by rfl⟩ : syracuseStep 2467057 = 1850293) B1850293
theorem B1090867 : Blo 646304 1090867 := bstep (se 1 (by rfl) ⟨818150, by rfl⟩ : syracuseStep 1090867 = 1636301) B1636301
theorem B730435 : Blo 646304 730435 := bstep (se 1 (by rfl) ⟨547826, by rfl⟩ : syracuseStep 730435 = 1095653) B1095653
theorem B1091009 : Blo 646304 1091009 := bstep (se 2 (by rfl) ⟨409128, by rfl⟩ : syracuseStep 1091009 = 818257) B818257
theorem B1844689 : Blo 646304 1844689 := bstep (se 2 (by rfl) ⟨691758, by rfl⟩ : syracuseStep 1844689 = 1383517) B1383517
theorem B730579 : Blo 646304 730579 := bstep (se 1 (by rfl) ⟨547934, by rfl⟩ : syracuseStep 730579 = 1095869) B1095869
theorem B2696753 : Blo 646304 2696753 := bstep (se 2 (by rfl) ⟨1011282, by rfl⟩ : syracuseStep 2696753 = 2022565) B2022565
theorem B1091137 : Blo 646304 1091137 := bstep (se 2 (by rfl) ⟨409176, by rfl⟩ : syracuseStep 1091137 = 818353) B818353
theorem B1091171 : Blo 646304 1091171 := bstep (se 1 (by rfl) ⟨818378, by rfl⟩ : syracuseStep 1091171 = 1636757) B1636757
theorem B730723 : Blo 646304 730723 := bstep (se 1 (by rfl) ⟨548042, by rfl⟩ : syracuseStep 730723 = 1096085) B1096085
theorem B1844849 : Blo 646304 1844849 := bstep (se 2 (by rfl) ⟨691818, by rfl⟩ : syracuseStep 1844849 = 1383637) B1383637
theorem B1091299 : Blo 646304 1091299 := bstep (se 1 (by rfl) ⟨818474, by rfl⟩ : syracuseStep 1091299 = 1636949) B1636949
theorem B1844963 : Blo 646304 1844963 := bstep (se 1 (by rfl) ⟨1383722, by rfl⟩ : syracuseStep 1844963 = 2767445) B2767445
theorem B730867 : Blo 646304 730867 := bstep (se 1 (by rfl) ⟨548150, by rfl⟩ : syracuseStep 730867 = 1096301) B1096301
theorem B4007693 : Blo 646304 4007693 := bstep (se 3 (by rfl) ⟨751442, by rfl⟩ : syracuseStep 4007693 = 1502885) B1502885
theorem B1091441 : Blo 646304 1091441 := bstep (se 2 (by rfl) ⟨409290, by rfl⟩ : syracuseStep 1091441 = 818581) B818581
theorem B1386353 : Blo 646304 1386353 := bstep (se 2 (by rfl) ⟨519882, by rfl⟩ : syracuseStep 1386353 = 1039765) B1039765
theorem B1386371 : Blo 646304 1386371 := bstep (se 1 (by rfl) ⟨1039778, by rfl⟩ : syracuseStep 1386371 = 2079557) B2079557
theorem B731011 : Blo 646304 731011 := bstep (se 1 (by rfl) ⟨548258, by rfl⟩ : syracuseStep 731011 = 1096517) B1096517
theorem B1091569 : Blo 646304 1091569 := bstep (se 2 (by rfl) ⟨409338, by rfl⟩ : syracuseStep 1091569 = 818677) B818677
theorem B2074609 : Blo 646304 2074609 := bstep (se 2 (by rfl) ⟨777978, by rfl⟩ : syracuseStep 2074609 = 1555957) B1555957
theorem B1091603 : Blo 646304 1091603 := bstep (se 1 (by rfl) ⟨818702, by rfl⟩ : syracuseStep 1091603 = 1637405) B1637405
theorem B731155 : Blo 646304 731155 := bstep (se 1 (by rfl) ⟨548366, by rfl⟩ : syracuseStep 731155 = 1096733) B1096733
theorem B1091731 : Blo 646304 1091731 := bstep (se 1 (by rfl) ⟨818798, by rfl⟩ : syracuseStep 1091731 = 1637597) B1637597
theorem B731299 : Blo 646304 731299 := bstep (se 1 (by rfl) ⟨548474, by rfl⟩ : syracuseStep 731299 = 1096949) B1096949
theorem B8890565 : Blo 646304 8890565 := bstep (se 4 (by rfl) ⟨833490, by rfl⟩ : syracuseStep 8890565 = 1666981) B1666981
theorem B1976557 : Blo 646304 1976557 := bstep (se 3 (by rfl) ⟨370604, by rfl⟩ : syracuseStep 1976557 = 741209) B741209
theorem B1091873 : Blo 646304 1091873 := bstep (se 2 (by rfl) ⟨409452, by rfl⟩ : syracuseStep 1091873 = 818905) B818905
theorem B731443 : Blo 646304 731443 := bstep (se 1 (by rfl) ⟨548582, by rfl⟩ : syracuseStep 731443 = 1097165) B1097165
theorem B1092001 : Blo 646304 1092001 := bstep (se 2 (by rfl) ⟨409500, by rfl⟩ : syracuseStep 1092001 = 819001) B819001
theorem B1092035 : Blo 646304 1092035 := bstep (se 1 (by rfl) ⟨819026, by rfl⟩ : syracuseStep 1092035 = 1638053) B1638053
theorem B731587 : Blo 646304 731587 := bstep (se 1 (by rfl) ⟨548690, by rfl⟩ : syracuseStep 731587 = 1097381) B1097381
theorem B1092163 : Blo 646304 1092163 := bstep (se 1 (by rfl) ⟨819122, by rfl⟩ : syracuseStep 1092163 = 1638245) B1638245
theorem B2075213 : Blo 646304 2075213 := bstep (se 3 (by rfl) ⟨389102, by rfl⟩ : syracuseStep 2075213 = 778205) B778205
theorem B2468515 : Blo 646304 2468515 := bstep (se 1 (by rfl) ⟨1851386, by rfl⟩ : syracuseStep 2468515 = 3702773) B3702773
theorem B1845965 : Blo 646304 1845965 := bstep (se 3 (by rfl) ⟨346118, by rfl⟩ : syracuseStep 1845965 = 692237) B692237
theorem B1092305 : Blo 646304 1092305 := bstep (se 2 (by rfl) ⟨409614, by rfl⟩ : syracuseStep 1092305 = 819229) B819229
theorem B1092433 : Blo 646304 1092433 := bstep (se 2 (by rfl) ⟨409662, by rfl⟩ : syracuseStep 1092433 = 819325) B819325
theorem B2501489 : Blo 646304 2501489 := bstep (se 2 (by rfl) ⟨938058, by rfl⟩ : syracuseStep 2501489 = 1876117) B1876117
theorem B1092467 : Blo 646304 1092467 := bstep (se 1 (by rfl) ⟨819350, by rfl⟩ : syracuseStep 1092467 = 1638701) B1638701
theorem B1846147 : Blo 646304 1846147 := bstep (se 1 (by rfl) ⟨1384610, by rfl⟩ : syracuseStep 1846147 = 2769221) B2769221
theorem B1092595 : Blo 646304 1092595 := bstep (se 1 (by rfl) ⟨819446, by rfl⟩ : syracuseStep 1092595 = 1638893) B1638893
theorem B1846307 : Blo 646304 1846307 := bstep (se 1 (by rfl) ⟨1384730, by rfl⟩ : syracuseStep 1846307 = 2769461) B2769461
theorem B3288113 : Blo 646304 3288113 := bstep (se 2 (by rfl) ⟨1233042, by rfl⟩ : syracuseStep 3288113 = 2466085) B2466085
theorem B1387601 : Blo 646304 1387601 := bstep (se 2 (by rfl) ⟨520350, by rfl⟩ : syracuseStep 1387601 = 1040701) B1040701
theorem B1092737 : Blo 646304 1092737 := bstep (se 2 (by rfl) ⟨409776, by rfl⟩ : syracuseStep 1092737 = 819553) B819553
theorem B1092865 : Blo 646304 1092865 := bstep (se 2 (by rfl) ⟨409824, by rfl⟩ : syracuseStep 1092865 = 819649) B819649
theorem B1092899 : Blo 646304 1092899 := bstep (se 1 (by rfl) ⟨819674, by rfl⟩ : syracuseStep 1092899 = 1639349) B1639349
theorem B1093027 : Blo 646304 1093027 := bstep (se 1 (by rfl) ⟨819770, by rfl⟩ : syracuseStep 1093027 = 1639541) B1639541
theorem B1093169 : Blo 646304 1093169 := bstep (se 2 (by rfl) ⟨409938, by rfl⟩ : syracuseStep 1093169 = 819877) B819877
theorem B3124813 : Blo 646304 3124813 := bstep (se 3 (by rfl) ⟨585902, by rfl⟩ : syracuseStep 3124813 = 1171805) B1171805
theorem B1093297 : Blo 646304 1093297 := bstep (se 2 (by rfl) ⟨409986, by rfl⟩ : syracuseStep 1093297 = 819973) B819973
theorem B1093331 : Blo 646304 1093331 := bstep (se 1 (by rfl) ⟨819998, by rfl⟩ : syracuseStep 1093331 = 1639997) B1639997
theorem B1093459 : Blo 646304 1093459 := bstep (se 1 (by rfl) ⟨820094, by rfl⟩ : syracuseStep 1093459 = 1640189) B1640189
theorem B2338723 : Blo 646304 2338723 := bstep (se 1 (by rfl) ⟨1754042, by rfl⟩ : syracuseStep 2338723 = 3508085) B3508085
theorem B1093601 : Blo 646304 1093601 := bstep (se 2 (by rfl) ⟨410100, by rfl⟩ : syracuseStep 1093601 = 820201) B820201
theorem B2764813 : Blo 646304 2764813 := bstep (se 3 (by rfl) ⟨518402, by rfl⟩ : syracuseStep 2764813 = 1036805) B1036805
theorem B1847377 : Blo 646304 1847377 := bstep (se 2 (by rfl) ⟨692766, by rfl⟩ : syracuseStep 1847377 = 1385533) B1385533
theorem B1093729 : Blo 646304 1093729 := bstep (se 2 (by rfl) ⟨410148, by rfl⟩ : syracuseStep 1093729 = 820297) B820297
theorem B1093763 : Blo 646304 1093763 := bstep (se 1 (by rfl) ⟨820322, by rfl⟩ : syracuseStep 1093763 = 1640645) B1640645
theorem B1093891 : Blo 646304 1093891 := bstep (se 1 (by rfl) ⟨820418, by rfl⟩ : syracuseStep 1093891 = 1640837) B1640837
theorem B1454417 : Blo 646304 1454417 := bstep (se 2 (by rfl) ⟨545406, by rfl⟩ : syracuseStep 1454417 = 1090813) B1090813
theorem B1454435 : Blo 646304 1454435 := bstep (se 1 (by rfl) ⟨1090826, by rfl⟩ : syracuseStep 1454435 = 2181653) B2181653
theorem B1094033 : Blo 646304 1094033 := bstep (se 2 (by rfl) ⟨410262, by rfl⟩ : syracuseStep 1094033 = 820525) B820525
theorem B3289571 : Blo 646304 3289571 := bstep (se 1 (by rfl) ⟨2467178, by rfl⟩ : syracuseStep 3289571 = 4934357) B4934357
theorem B1094161 : Blo 646304 1094161 := bstep (se 2 (by rfl) ⟨410310, by rfl⟩ : syracuseStep 1094161 = 820621) B820621
theorem B1094195 : Blo 646304 1094195 := bstep (se 1 (by rfl) ⟨820646, by rfl⟩ : syracuseStep 1094195 = 1641293) B1641293
theorem B1454705 : Blo 646304 1454705 := bstep (se 2 (by rfl) ⟨545514, by rfl⟩ : syracuseStep 1454705 = 1091029) B1091029
theorem B1454723 : Blo 646304 1454723 := bstep (se 1 (by rfl) ⟨1091042, by rfl⟩ : syracuseStep 1454723 = 2182085) B2182085
theorem B1094323 : Blo 646304 1094323 := bstep (se 1 (by rfl) ⟨820742, by rfl⟩ : syracuseStep 1094323 = 1641485) B1641485
theorem B1094465 : Blo 646304 1094465 := bstep (se 2 (by rfl) ⟨410424, by rfl⟩ : syracuseStep 1094465 = 820849) B820849
theorem B1454993 : Blo 646304 1454993 := bstep (se 2 (by rfl) ⟨545622, by rfl⟩ : syracuseStep 1454993 = 1091245) B1091245
theorem B1455011 : Blo 646304 1455011 := bstep (se 1 (by rfl) ⟨1091258, by rfl⟩ : syracuseStep 1455011 = 2182517) B2182517
theorem B1094593 : Blo 646304 1094593 := bstep (se 2 (by rfl) ⟨410472, by rfl⟩ : syracuseStep 1094593 = 820945) B820945
theorem B1094627 : Blo 646304 1094627 := bstep (se 1 (by rfl) ⟨820970, by rfl⟩ : syracuseStep 1094627 = 1641941) B1641941
theorem B4928525 : Blo 646304 4928525 := bstep (se 3 (by rfl) ⟨924098, by rfl⟩ : syracuseStep 4928525 = 1848197) B1848197
theorem B1553489 : Blo 646304 1553489 := bstep (se 2 (by rfl) ⟨582558, by rfl⟩ : syracuseStep 1553489 = 1165117) B1165117
theorem B1094755 : Blo 646304 1094755 := bstep (se 1 (by rfl) ⟨821066, by rfl⟩ : syracuseStep 1094755 = 1642133) B1642133
theorem B1455281 : Blo 646304 1455281 := bstep (se 2 (by rfl) ⟨545730, by rfl⟩ : syracuseStep 1455281 = 1091461) B1091461
theorem B1455299 : Blo 646304 1455299 := bstep (se 1 (by rfl) ⟨1091474, by rfl⟩ : syracuseStep 1455299 = 2182949) B2182949
theorem B1094897 : Blo 646304 1094897 := bstep (se 2 (by rfl) ⟨410586, by rfl⟩ : syracuseStep 1094897 = 821173) B821173
theorem B3290381 : Blo 646304 3290381 := bstep (se 3 (by rfl) ⟨616946, by rfl⟩ : syracuseStep 3290381 = 1233893) B1233893
theorem B4666693 : Blo 646304 4666693 := bstep (se 4 (by rfl) ⟨437502, by rfl⟩ : syracuseStep 4666693 = 875005) B875005
theorem B1848653 : Blo 646304 1848653 := bstep (se 3 (by rfl) ⟨346622, by rfl⟩ : syracuseStep 1848653 = 693245) B693245
theorem B2110801 : Blo 646304 2110801 := bstep (se 2 (by rfl) ⟨791550, by rfl⟩ : syracuseStep 2110801 = 1583101) B1583101
theorem B1095025 : Blo 646304 1095025 := bstep (se 2 (by rfl) ⟨410634, by rfl⟩ : syracuseStep 1095025 = 821269) B821269
theorem B1095059 : Blo 646304 1095059 := bstep (se 1 (by rfl) ⟨821294, by rfl⟩ : syracuseStep 1095059 = 1642589) B1642589
theorem B1455569 : Blo 646304 1455569 := bstep (se 2 (by rfl) ⟨545838, by rfl⟩ : syracuseStep 1455569 = 1091677) B1091677
theorem B1455587 : Blo 646304 1455587 := bstep (se 1 (by rfl) ⟨1091690, by rfl⟩ : syracuseStep 1455587 = 2183381) B2183381
theorem B1848835 : Blo 646304 1848835 := bstep (se 1 (by rfl) ⟨1386626, by rfl⟩ : syracuseStep 1848835 = 2773253) B2773253
theorem B1095187 : Blo 646304 1095187 := bstep (se 1 (by rfl) ⟨821390, by rfl⟩ : syracuseStep 1095187 = 1642781) B1642781
theorem B1848881 : Blo 646304 1848881 := bstep (se 2 (by rfl) ⟨693330, by rfl⟩ : syracuseStep 1848881 = 1386661) B1386661
theorem B1095329 : Blo 646304 1095329 := bstep (se 2 (by rfl) ⟨410748, by rfl⟩ : syracuseStep 1095329 = 821497) B821497
theorem B4732613 : Blo 646304 4732613 := bstep (se 4 (by rfl) ⟨443682, by rfl⟩ : syracuseStep 4732613 = 887365) B887365
theorem B1455857 : Blo 646304 1455857 := bstep (se 2 (by rfl) ⟨545946, by rfl⟩ : syracuseStep 1455857 = 1091893) B1091893
theorem B1455875 : Blo 646304 1455875 := bstep (se 1 (by rfl) ⟨1091906, by rfl⟩ : syracuseStep 1455875 = 2183813) B2183813
theorem B1095457 : Blo 646304 1095457 := bstep (se 2 (by rfl) ⟨410796, by rfl⟩ : syracuseStep 1095457 = 821593) B821593
theorem B2078531 : Blo 646304 2078531 := bstep (se 1 (by rfl) ⟨1558898, by rfl⟩ : syracuseStep 2078531 = 3117797) B3117797
theorem B1095491 : Blo 646304 1095491 := bstep (se 1 (by rfl) ⟨821618, by rfl⟩ : syracuseStep 1095491 = 1643237) B1643237
theorem B1095619 : Blo 646304 1095619 := bstep (se 1 (by rfl) ⟨821714, by rfl⟩ : syracuseStep 1095619 = 1643429) B1643429
theorem B1456145 : Blo 646304 1456145 := bstep (se 2 (by rfl) ⟨546054, by rfl⟩ : syracuseStep 1456145 = 1092109) B1092109
theorem B1456163 : Blo 646304 1456163 := bstep (se 1 (by rfl) ⟨1092122, by rfl⟩ : syracuseStep 1456163 = 2184245) B2184245
theorem B1095761 : Blo 646304 1095761 := bstep (se 2 (by rfl) ⟨410910, by rfl⟩ : syracuseStep 1095761 = 821821) B821821
theorem B1095889 : Blo 646304 1095889 := bstep (se 2 (by rfl) ⟨410958, by rfl⟩ : syracuseStep 1095889 = 821917) B821917
theorem B1095923 : Blo 646304 1095923 := bstep (se 1 (by rfl) ⟨821942, by rfl⟩ : syracuseStep 1095923 = 1643885) B1643885
theorem B1456433 : Blo 646304 1456433 := bstep (se 2 (by rfl) ⟨546162, by rfl⟩ : syracuseStep 1456433 = 1092325) B1092325
theorem B1456451 : Blo 646304 1456451 := bstep (se 1 (by rfl) ⟨1092338, by rfl⟩ : syracuseStep 1456451 = 2184677) B2184677
theorem B1227089 : Blo 646304 1227089 := bstep (se 2 (by rfl) ⟨460158, by rfl⟩ : syracuseStep 1227089 = 920317) B920317
theorem B1751395 : Blo 646304 1751395 := bstep (se 1 (by rfl) ⟨1313546, by rfl⟩ : syracuseStep 1751395 = 2627093) B2627093
theorem B1096051 : Blo 646304 1096051 := bstep (se 1 (by rfl) ⟨822038, by rfl⟩ : syracuseStep 1096051 = 1644077) B1644077
theorem B1096193 : Blo 646304 1096193 := bstep (se 2 (by rfl) ⟨411072, by rfl⟩ : syracuseStep 1096193 = 822145) B822145
theorem B3947057 : Blo 646304 3947057 := bstep (se 2 (by rfl) ⟨1480146, by rfl⟩ : syracuseStep 3947057 = 2960293) B2960293
theorem B1456721 : Blo 646304 1456721 := bstep (se 2 (by rfl) ⟨546270, by rfl⟩ : syracuseStep 1456721 = 1092541) B1092541
theorem B1456739 : Blo 646304 1456739 := bstep (se 1 (by rfl) ⟨1092554, by rfl⟩ : syracuseStep 1456739 = 2185109) B2185109
theorem B13318769 : Blo 646304 13318769 := bstep (se 2 (by rfl) ⟨4994538, by rfl⟩ : syracuseStep 13318769 = 9989077) B9989077
theorem B1096321 : Blo 646304 1096321 := bstep (se 2 (by rfl) ⟨411120, by rfl⟩ : syracuseStep 1096321 = 822241) B822241
theorem B2079377 : Blo 646304 2079377 := bstep (se 2 (by rfl) ⟨779766, by rfl⟩ : syracuseStep 2079377 = 1559533) B1559533
theorem B1096355 : Blo 646304 1096355 := bstep (se 1 (by rfl) ⟨822266, by rfl⟩ : syracuseStep 1096355 = 1644533) B1644533
theorem B2079427 : Blo 646304 2079427 := bstep (se 1 (by rfl) ⟨1559570, by rfl⟩ : syracuseStep 2079427 = 3119141) B3119141
theorem B4668101 : Blo 646304 4668101 := bstep (se 4 (by rfl) ⟨437634, by rfl⟩ : syracuseStep 4668101 = 875269) B875269
theorem B1096483 : Blo 646304 1096483 := bstep (se 1 (by rfl) ⟨822362, by rfl⟩ : syracuseStep 1096483 = 1644725) B1644725
theorem B1457009 : Blo 646304 1457009 := bstep (se 2 (by rfl) ⟨546378, by rfl⟩ : syracuseStep 1457009 = 1092757) B1092757
theorem B1457027 : Blo 646304 1457027 := bstep (se 1 (by rfl) ⟨1092770, by rfl⟩ : syracuseStep 1457027 = 2185541) B2185541
theorem B2800561 : Blo 646304 2800561 := bstep (se 2 (by rfl) ⟨1050210, by rfl⟩ : syracuseStep 2800561 = 2100421) B2100421
theorem B1096625 : Blo 646304 1096625 := bstep (se 2 (by rfl) ⟨411234, by rfl⟩ : syracuseStep 1096625 = 822469) B822469
theorem B1850339 : Blo 646304 1850339 := bstep (se 1 (by rfl) ⟨1387754, by rfl⟩ : syracuseStep 1850339 = 2775509) B2775509
theorem B1227811 : Blo 646304 1227811 := bstep (se 1 (by rfl) ⟨920858, by rfl⟩ : syracuseStep 1227811 = 1841717) B1841717
theorem B1096753 : Blo 646304 1096753 := bstep (se 2 (by rfl) ⟨411282, by rfl⟩ : syracuseStep 1096753 = 822565) B822565
theorem B1096787 : Blo 646304 1096787 := bstep (se 1 (by rfl) ⟨822590, by rfl⟩ : syracuseStep 1096787 = 1645181) B1645181
theorem B1457297 : Blo 646304 1457297 := bstep (se 2 (by rfl) ⟨546486, by rfl⟩ : syracuseStep 1457297 = 1092973) B1092973
theorem B1457315 : Blo 646304 1457315 := bstep (se 1 (by rfl) ⟨1092986, by rfl⟩ : syracuseStep 1457315 = 2185973) B2185973
theorem B1096915 : Blo 646304 1096915 := bstep (se 1 (by rfl) ⟨822686, by rfl⟩ : syracuseStep 1096915 = 1645373) B1645373
theorem B1097057 : Blo 646304 1097057 := bstep (se 2 (by rfl) ⟨411396, by rfl⟩ : syracuseStep 1097057 = 822793) B822793
theorem B1457585 : Blo 646304 1457585 := bstep (se 2 (by rfl) ⟨546594, by rfl⟩ : syracuseStep 1457585 = 1093189) B1093189
theorem B1457603 : Blo 646304 1457603 := bstep (se 1 (by rfl) ⟨1093202, by rfl⟩ : syracuseStep 1457603 = 2186405) B2186405
theorem B933331 : Blo 646304 933331 := bstep (se 1 (by rfl) ⟨699998, by rfl⟩ : syracuseStep 933331 = 1399997) B1399997
theorem B1097185 : Blo 646304 1097185 := bstep (se 2 (by rfl) ⟨411444, by rfl⟩ : syracuseStep 1097185 = 822889) B822889
theorem B1228259 : Blo 646304 1228259 := bstep (se 1 (by rfl) ⟨921194, by rfl⟩ : syracuseStep 1228259 = 1842389) B1842389
theorem B1097219 : Blo 646304 1097219 := bstep (se 1 (by rfl) ⟨822914, by rfl⟩ : syracuseStep 1097219 = 1645829) B1645829
theorem B1097347 : Blo 646304 1097347 := bstep (se 1 (by rfl) ⟨823010, by rfl⟩ : syracuseStep 1097347 = 1646021) B1646021
theorem B1556131 : Blo 646304 1556131 := bstep (se 1 (by rfl) ⟨1167098, by rfl⟩ : syracuseStep 1556131 = 2334197) B2334197
theorem B2211533 : Blo 646304 2211533 := bstep (se 3 (by rfl) ⟨414662, by rfl⟩ : syracuseStep 2211533 = 829325) B829325
theorem B1457873 : Blo 646304 1457873 := bstep (se 2 (by rfl) ⟨546702, by rfl⟩ : syracuseStep 1457873 = 1093405) B1093405
theorem B1457891 : Blo 646304 1457891 := bstep (se 1 (by rfl) ⟨1093418, by rfl⟩ : syracuseStep 1457891 = 2186837) B2186837
theorem B1228547 : Blo 646304 1228547 := bstep (se 1 (by rfl) ⟨921410, by rfl⟩ : syracuseStep 1228547 = 1842821) B1842821
theorem B4931441 : Blo 646304 4931441 := bstep (se 2 (by rfl) ⟨1849290, by rfl⟩ : syracuseStep 4931441 = 3698581) B3698581
theorem B2080657 : Blo 646304 2080657 := bstep (se 2 (by rfl) ⟨780246, by rfl⟩ : syracuseStep 2080657 = 1560493) B1560493
theorem B1753069 : Blo 646304 1753069 := bstep (se 3 (by rfl) ⟨328700, by rfl⟩ : syracuseStep 1753069 = 657401) B657401
theorem B1458161 : Blo 646304 1458161 := bstep (se 2 (by rfl) ⟨546810, by rfl⟩ : syracuseStep 1458161 = 1093621) B1093621
theorem B1458179 : Blo 646304 1458179 := bstep (se 1 (by rfl) ⟨1093634, by rfl⟩ : syracuseStep 1458179 = 2187269) B2187269
theorem B1851569 : Blo 646304 1851569 := bstep (se 2 (by rfl) ⟨694338, by rfl⟩ : syracuseStep 1851569 = 1388677) B1388677
theorem B2769137 : Blo 646304 2769137 := bstep (se 2 (by rfl) ⟨1038426, by rfl⟩ : syracuseStep 2769137 = 2076853) B2076853
theorem B1458449 : Blo 646304 1458449 := bstep (se 2 (by rfl) ⟨546918, by rfl⟩ : syracuseStep 1458449 = 1093837) B1093837
theorem B1458467 : Blo 646304 1458467 := bstep (se 1 (by rfl) ⟨1093850, by rfl⟩ : syracuseStep 1458467 = 2187701) B2187701
theorem B2769187 : Blo 646304 2769187 := bstep (se 1 (by rfl) ⟨2076890, by rfl⟩ : syracuseStep 2769187 = 4153781) B4153781
theorem B1556977 : Blo 646304 1556977 := bstep (se 2 (by rfl) ⟨583866, by rfl⟩ : syracuseStep 1556977 = 1167733) B1167733
theorem B3686917 : Blo 646304 3686917 := bstep (se 4 (by rfl) ⟨345648, by rfl⟩ : syracuseStep 3686917 = 691297) B691297
theorem B1458737 : Blo 646304 1458737 := bstep (se 2 (by rfl) ⟨547026, by rfl⟩ : syracuseStep 1458737 = 1094053) B1094053
theorem B1458755 : Blo 646304 1458755 := bstep (se 1 (by rfl) ⟨1094066, by rfl⟩ : syracuseStep 1458755 = 2188133) B2188133
theorem B1229489 : Blo 646304 1229489 := bstep (se 2 (by rfl) ⟨461058, by rfl⟩ : syracuseStep 1229489 = 922117) B922117
theorem B1459025 : Blo 646304 1459025 := bstep (se 2 (by rfl) ⟨547134, by rfl⟩ : syracuseStep 1459025 = 1094269) B1094269
theorem B1459043 : Blo 646304 1459043 := bstep (se 1 (by rfl) ⟨1094282, by rfl⟩ : syracuseStep 1459043 = 2188565) B2188565
theorem B5522417 : Blo 646304 5522417 := bstep (se 2 (by rfl) ⟨2070906, by rfl⟩ : syracuseStep 5522417 = 4141813) B4141813
theorem B1754129 : Blo 646304 1754129 := bstep (se 2 (by rfl) ⟨657798, by rfl⟩ : syracuseStep 1754129 = 1315597) B1315597
theorem B2081837 : Blo 646304 2081837 := bstep (se 3 (by rfl) ⟨390344, by rfl⟩ : syracuseStep 2081837 = 780689) B780689
theorem B1459313 : Blo 646304 1459313 := bstep (se 2 (by rfl) ⟨547242, by rfl⟩ : syracuseStep 1459313 = 1094485) B1094485
theorem B1459331 : Blo 646304 1459331 := bstep (se 1 (by rfl) ⟨1094498, by rfl⟩ : syracuseStep 1459331 = 2188997) B2188997
theorem B3851569 : Blo 646304 3851569 := bstep (se 2 (by rfl) ⟨1444338, by rfl⟩ : syracuseStep 3851569 = 2888677) B2888677
theorem B1459601 : Blo 646304 1459601 := bstep (se 2 (by rfl) ⟨547350, by rfl⟩ : syracuseStep 1459601 = 1094701) B1094701
theorem B1459619 : Blo 646304 1459619 := bstep (se 1 (by rfl) ⟨1094714, by rfl⟩ : syracuseStep 1459619 = 2189429) B2189429
theorem B3753485 : Blo 646304 3753485 := bstep (se 3 (by rfl) ⟨703778, by rfl⟩ : syracuseStep 3753485 = 1407557) B1407557
theorem B1230385 : Blo 646304 1230385 := bstep (se 2 (by rfl) ⟨461394, by rfl⟩ : syracuseStep 1230385 = 922789) B922789
theorem B8308277 : Blo 646304 8308277 := bstep (se 5 (by rfl) ⟨389450, by rfl⟩ : syracuseStep 8308277 = 778901) B778901
theorem B1459889 : Blo 646304 1459889 := bstep (se 2 (by rfl) ⟨547458, by rfl⟩ : syracuseStep 1459889 = 1094917) B1094917
theorem B1459907 : Blo 646304 1459907 := bstep (se 1 (by rfl) ⟨1094930, by rfl⟩ : syracuseStep 1459907 = 2189861) B2189861
theorem B1230545 : Blo 646304 1230545 := bstep (se 2 (by rfl) ⟨461454, by rfl⟩ : syracuseStep 1230545 = 922909) B922909
theorem B1460177 : Blo 646304 1460177 := bstep (se 2 (by rfl) ⟨547566, by rfl⟩ : syracuseStep 1460177 = 1095133) B1095133
theorem B1460195 : Blo 646304 1460195 := bstep (se 1 (by rfl) ⟨1095146, by rfl⟩ : syracuseStep 1460195 = 2190293) B2190293
theorem B1230947 : Blo 646304 1230947 := bstep (se 1 (by rfl) ⟨923210, by rfl⟩ : syracuseStep 1230947 = 1846421) B1846421
theorem B2181329 : Blo 646304 2181329 := bstep (se 2 (by rfl) ⟨817998, by rfl⟩ : syracuseStep 2181329 = 1635997) B1635997
theorem B1460465 : Blo 646304 1460465 := bstep (se 2 (by rfl) ⟨547674, by rfl⟩ : syracuseStep 1460465 = 1095349) B1095349
theorem B1460483 : Blo 646304 1460483 := bstep (se 1 (by rfl) ⟨1095362, by rfl⟩ : syracuseStep 1460483 = 2190725) B2190725
theorem B2214161 : Blo 646304 2214161 := bstep (se 2 (by rfl) ⟨830310, by rfl⟩ : syracuseStep 2214161 = 1660621) B1660621
theorem B1755427 : Blo 646304 1755427 := bstep (se 1 (by rfl) ⟨1316570, by rfl⟩ : syracuseStep 1755427 = 2633141) B2633141
theorem B3688901 : Blo 646304 3688901 := bstep (se 4 (by rfl) ⟨345834, by rfl⟩ : syracuseStep 3688901 = 691669) B691669
theorem B1460753 : Blo 646304 1460753 := bstep (se 2 (by rfl) ⟨547782, by rfl⟩ : syracuseStep 1460753 = 1095565) B1095565
theorem B1460771 : Blo 646304 1460771 := bstep (se 1 (by rfl) ⟨1095578, by rfl⟩ : syracuseStep 1460771 = 2191157) B2191157
theorem B1165873 : Blo 646304 1165873 := bstep (se 2 (by rfl) ⟨437202, by rfl⟩ : syracuseStep 1165873 = 874405) B874405
theorem B2771597 : Blo 646304 2771597 := bstep (se 3 (by rfl) ⟨519674, by rfl⟩ : syracuseStep 2771597 = 1039349) B1039349
theorem B2181869 : Blo 646304 2181869 := bstep (se 3 (by rfl) ⟨409100, by rfl⟩ : syracuseStep 2181869 = 818201) B818201
theorem B969473 : Blo 646304 969473 := bstep (se 2 (by rfl) ⟨363552, by rfl⟩ : syracuseStep 969473 = 727105) B727105
theorem B969491 : Blo 646304 969491 := bstep (se 1 (by rfl) ⟨727118, by rfl⟩ : syracuseStep 969491 = 1454237) B1454237
theorem B2181923 : Blo 646304 2181923 := bstep (se 1 (by rfl) ⟨1636442, by rfl⟩ : syracuseStep 2181923 = 3272885) B3272885
theorem B969521 : Blo 646304 969521 := bstep (se 2 (by rfl) ⟨363570, by rfl⟩ : syracuseStep 969521 = 727141) B727141
theorem B1461041 : Blo 646304 1461041 := bstep (se 2 (by rfl) ⟨547890, by rfl⟩ : syracuseStep 1461041 = 1095781) B1095781
theorem B969539 : Blo 646304 969539 := bstep (se 1 (by rfl) ⟨727154, by rfl⟩ : syracuseStep 969539 = 1454309) B1454309
theorem B1461059 : Blo 646304 1461059 := bstep (se 1 (by rfl) ⟨1095794, by rfl⟩ : syracuseStep 1461059 = 2191589) B2191589
theorem B969569 : Blo 646304 969569 := bstep (se 2 (by rfl) ⟨363588, by rfl⟩ : syracuseStep 969569 = 727177) B727177
theorem B969587 : Blo 646304 969587 := bstep (se 1 (by rfl) ⟨727190, by rfl⟩ : syracuseStep 969587 = 1454381) B1454381
theorem B969617 : Blo 646304 969617 := bstep (se 2 (by rfl) ⟨363606, by rfl⟩ : syracuseStep 969617 = 727213) B727213
theorem B969635 : Blo 646304 969635 := bstep (se 1 (by rfl) ⟨727226, by rfl⟩ : syracuseStep 969635 = 1454453) B1454453
theorem B969665 : Blo 646304 969665 := bstep (se 2 (by rfl) ⟨363624, by rfl⟩ : syracuseStep 969665 = 727249) B727249
theorem B969683 : Blo 646304 969683 := bstep (se 1 (by rfl) ⟨727262, by rfl⟩ : syracuseStep 969683 = 1454525) B1454525
theorem B1231843 : Blo 646304 1231843 := bstep (se 1 (by rfl) ⟨923882, by rfl⟩ : syracuseStep 1231843 = 1847765) B1847765
theorem B969713 : Blo 646304 969713 := bstep (se 2 (by rfl) ⟨363642, by rfl⟩ : syracuseStep 969713 = 727285) B727285
theorem B969731 : Blo 646304 969731 := bstep (se 1 (by rfl) ⟨727298, by rfl⟩ : syracuseStep 969731 = 1454597) B1454597
theorem B969761 : Blo 646304 969761 := bstep (se 2 (by rfl) ⟨363660, by rfl⟩ : syracuseStep 969761 = 727321) B727321
theorem B1756205 : Blo 646304 1756205 := bstep (se 3 (by rfl) ⟨329288, by rfl⟩ : syracuseStep 1756205 = 658577) B658577
theorem B2182193 : Blo 646304 2182193 := bstep (se 2 (by rfl) ⟨818322, by rfl⟩ : syracuseStep 2182193 = 1636645) B1636645
theorem B969779 : Blo 646304 969779 := bstep (se 1 (by rfl) ⟨727334, by rfl⟩ : syracuseStep 969779 = 1454669) B1454669
theorem B969809 : Blo 646304 969809 := bstep (se 2 (by rfl) ⟨363678, by rfl⟩ : syracuseStep 969809 = 727357) B727357
theorem B1461329 : Blo 646304 1461329 := bstep (se 2 (by rfl) ⟨547998, by rfl⟩ : syracuseStep 1461329 = 1095997) B1095997
theorem B969827 : Blo 646304 969827 := bstep (se 1 (by rfl) ⟨727370, by rfl⟩ : syracuseStep 969827 = 1454741) B1454741
theorem B1461347 : Blo 646304 1461347 := bstep (se 1 (by rfl) ⟨1096010, by rfl⟩ : syracuseStep 1461347 = 2192021) B2192021
theorem B1166449 : Blo 646304 1166449 := bstep (se 2 (by rfl) ⟨437418, by rfl⟩ : syracuseStep 1166449 = 874837) B874837
theorem B969857 : Blo 646304 969857 := bstep (se 2 (by rfl) ⟨363696, by rfl⟩ : syracuseStep 969857 = 727393) B727393
theorem B1232003 : Blo 646304 1232003 := bstep (se 1 (by rfl) ⟨924002, by rfl⟩ : syracuseStep 1232003 = 1848005) B1848005
theorem B969875 : Blo 646304 969875 := bstep (se 1 (by rfl) ⟨727406, by rfl⟩ : syracuseStep 969875 = 1454813) B1454813
theorem B969905 : Blo 646304 969905 := bstep (se 2 (by rfl) ⟨363714, by rfl⟩ : syracuseStep 969905 = 727429) B727429
theorem B969923 : Blo 646304 969923 := bstep (se 1 (by rfl) ⟨727442, by rfl⟩ : syracuseStep 969923 = 1454885) B1454885
theorem B969953 : Blo 646304 969953 := bstep (se 2 (by rfl) ⟨363732, by rfl⟩ : syracuseStep 969953 = 727465) B727465
theorem B969971 : Blo 646304 969971 := bstep (se 1 (by rfl) ⟨727478, by rfl⟩ : syracuseStep 969971 = 1454957) B1454957
theorem B6638861 : Blo 646304 6638861 := bstep (se 3 (by rfl) ⟨1244786, by rfl⟩ : syracuseStep 6638861 = 2489573) B2489573
theorem B970001 : Blo 646304 970001 := bstep (se 2 (by rfl) ⟨363750, by rfl⟩ : syracuseStep 970001 = 727501) B727501
theorem B970019 : Blo 646304 970019 := bstep (se 1 (by rfl) ⟨727514, by rfl⟩ : syracuseStep 970019 = 1455029) B1455029
theorem B970049 : Blo 646304 970049 := bstep (se 2 (by rfl) ⟨363768, by rfl⟩ : syracuseStep 970049 = 727537) B727537
theorem B970067 : Blo 646304 970067 := bstep (se 1 (by rfl) ⟨727550, by rfl⟩ : syracuseStep 970067 = 1455101) B1455101
theorem B970097 : Blo 646304 970097 := bstep (se 2 (by rfl) ⟨363786, by rfl⟩ : syracuseStep 970097 = 727573) B727573
theorem B1461617 : Blo 646304 1461617 := bstep (se 2 (by rfl) ⟨548106, by rfl⟩ : syracuseStep 1461617 = 1096213) B1096213
theorem B970115 : Blo 646304 970115 := bstep (se 1 (by rfl) ⟨727586, by rfl⟩ : syracuseStep 970115 = 1455173) B1455173
theorem B1461635 : Blo 646304 1461635 := bstep (se 1 (by rfl) ⟨1096226, by rfl⟩ : syracuseStep 1461635 = 2192453) B2192453
theorem B970145 : Blo 646304 970145 := bstep (se 2 (by rfl) ⟨363804, by rfl⟩ : syracuseStep 970145 = 727609) B727609
theorem B4148657 : Blo 646304 4148657 := bstep (se 2 (by rfl) ⟨1555746, by rfl⟩ : syracuseStep 4148657 = 3111493) B3111493
theorem B970163 : Blo 646304 970163 := bstep (se 1 (by rfl) ⟨727622, by rfl⟩ : syracuseStep 970163 = 1455245) B1455245
theorem B970193 : Blo 646304 970193 := bstep (se 2 (by rfl) ⟨363822, by rfl⟩ : syracuseStep 970193 = 727645) B727645
theorem B970211 : Blo 646304 970211 := bstep (se 1 (by rfl) ⟨727658, by rfl⟩ : syracuseStep 970211 = 1455317) B1455317
theorem B970241 : Blo 646304 970241 := bstep (se 2 (by rfl) ⟨363840, by rfl⟩ : syracuseStep 970241 = 727681) B727681
theorem B970259 : Blo 646304 970259 := bstep (se 1 (by rfl) ⟨727694, by rfl⟩ : syracuseStep 970259 = 1455389) B1455389
theorem B970289 : Blo 646304 970289 := bstep (se 2 (by rfl) ⟨363858, by rfl⟩ : syracuseStep 970289 = 727717) B727717
theorem B970307 : Blo 646304 970307 := bstep (se 1 (by rfl) ⟨727730, by rfl⟩ : syracuseStep 970307 = 1455461) B1455461
theorem B2182733 : Blo 646304 2182733 := bstep (se 3 (by rfl) ⟨409262, by rfl⟩ : syracuseStep 2182733 = 818525) B818525
theorem B1265233 : Blo 646304 1265233 := bstep (se 2 (by rfl) ⟨474462, by rfl⟩ : syracuseStep 1265233 = 948925) B948925
theorem B970337 : Blo 646304 970337 := bstep (se 2 (by rfl) ⟨363876, by rfl⟩ : syracuseStep 970337 = 727753) B727753
theorem B970355 : Blo 646304 970355 := bstep (se 1 (by rfl) ⟨727766, by rfl⟩ : syracuseStep 970355 = 1455533) B1455533
theorem B2182787 : Blo 646304 2182787 := bstep (se 1 (by rfl) ⟨1637090, by rfl⟩ : syracuseStep 2182787 = 3274181) B3274181
theorem B970385 : Blo 646304 970385 := bstep (se 2 (by rfl) ⟨363894, by rfl⟩ : syracuseStep 970385 = 727789) B727789
theorem B1461905 : Blo 646304 1461905 := bstep (se 2 (by rfl) ⟨548214, by rfl⟩ : syracuseStep 1461905 = 1096429) B1096429
theorem B970403 : Blo 646304 970403 := bstep (se 1 (by rfl) ⟨727802, by rfl⟩ : syracuseStep 970403 = 1455605) B1455605
theorem B1461923 : Blo 646304 1461923 := bstep (se 1 (by rfl) ⟨1096442, by rfl⟩ : syracuseStep 1461923 = 2192885) B2192885
theorem B970433 : Blo 646304 970433 := bstep (se 2 (by rfl) ⟨363912, by rfl⟩ : syracuseStep 970433 = 727825) B727825
theorem B1035985 : Blo 646304 1035985 := bstep (se 2 (by rfl) ⟨388494, by rfl⟩ : syracuseStep 1035985 = 776989) B776989
theorem B970451 : Blo 646304 970451 := bstep (se 1 (by rfl) ⟨727838, by rfl⟩ : syracuseStep 970451 = 1455677) B1455677
theorem B970481 : Blo 646304 970481 := bstep (se 2 (by rfl) ⟨363930, by rfl⟩ : syracuseStep 970481 = 727861) B727861
theorem B970499 : Blo 646304 970499 := bstep (se 1 (by rfl) ⟨727874, by rfl⟩ : syracuseStep 970499 = 1455749) B1455749
theorem B970529 : Blo 646304 970529 := bstep (se 2 (by rfl) ⟨363948, by rfl⟩ : syracuseStep 970529 = 727897) B727897
theorem B741155 : Blo 646304 741155 := bstep (se 1 (by rfl) ⟨555866, by rfl⟩ : syracuseStep 741155 = 1111733) B1111733
theorem B970547 : Blo 646304 970547 := bstep (se 1 (by rfl) ⟨727910, by rfl⟩ : syracuseStep 970547 = 1455821) B1455821
theorem B970577 : Blo 646304 970577 := bstep (se 2 (by rfl) ⟨363966, by rfl⟩ : syracuseStep 970577 = 727933) B727933
theorem B970595 : Blo 646304 970595 := bstep (se 1 (by rfl) ⟨727946, by rfl⟩ : syracuseStep 970595 = 1455893) B1455893
theorem B1757027 : Blo 646304 1757027 := bstep (se 1 (by rfl) ⟨1317770, by rfl⟩ : syracuseStep 1757027 = 2635541) B2635541
theorem B970625 : Blo 646304 970625 := bstep (se 2 (by rfl) ⟨363984, by rfl⟩ : syracuseStep 970625 = 727969) B727969
theorem B50417549 : Blo 646304 50417549 := bstep (se 3 (by rfl) ⟨9453290, by rfl⟩ : syracuseStep 50417549 = 18906581) B18906581
theorem B2183057 : Blo 646304 2183057 := bstep (se 2 (by rfl) ⟨818646, by rfl⟩ : syracuseStep 2183057 = 1637293) B1637293
theorem B970643 : Blo 646304 970643 := bstep (se 1 (by rfl) ⟨727982, by rfl⟩ : syracuseStep 970643 = 1455965) B1455965
theorem B970673 : Blo 646304 970673 := bstep (se 2 (by rfl) ⟨364002, by rfl⟩ : syracuseStep 970673 = 728005) B728005
theorem B1462193 : Blo 646304 1462193 := bstep (se 2 (by rfl) ⟨548322, by rfl⟩ : syracuseStep 1462193 = 1096645) B1096645
theorem B970691 : Blo 646304 970691 := bstep (se 1 (by rfl) ⟨728018, by rfl⟩ : syracuseStep 970691 = 1456037) B1456037
theorem B1462211 : Blo 646304 1462211 := bstep (se 1 (by rfl) ⟨1096658, by rfl⟩ : syracuseStep 1462211 = 2193317) B2193317
theorem B970721 : Blo 646304 970721 := bstep (se 2 (by rfl) ⟨364020, by rfl⟩ : syracuseStep 970721 = 728041) B728041
theorem B970739 : Blo 646304 970739 := bstep (se 1 (by rfl) ⟨728054, by rfl⟩ : syracuseStep 970739 = 1456109) B1456109
theorem B970769 : Blo 646304 970769 := bstep (se 2 (by rfl) ⟨364038, by rfl⟩ : syracuseStep 970769 = 728077) B728077
theorem B970787 : Blo 646304 970787 := bstep (se 1 (by rfl) ⟨728090, by rfl⟩ : syracuseStep 970787 = 1456181) B1456181
theorem B970817 : Blo 646304 970817 := bstep (se 2 (by rfl) ⟨364056, by rfl⟩ : syracuseStep 970817 = 728113) B728113
theorem B970835 : Blo 646304 970835 := bstep (se 1 (by rfl) ⟨728126, by rfl⟩ : syracuseStep 970835 = 1456253) B1456253
theorem B970865 : Blo 646304 970865 := bstep (se 2 (by rfl) ⟨364074, by rfl⟩ : syracuseStep 970865 = 728149) B728149
theorem B970883 : Blo 646304 970883 := bstep (se 1 (by rfl) ⟨728162, by rfl⟩ : syracuseStep 970883 = 1456325) B1456325
theorem B3494029 : Blo 646304 3494029 := bstep (se 3 (by rfl) ⟨655130, by rfl⟩ : syracuseStep 3494029 = 1310261) B1310261
theorem B1036433 : Blo 646304 1036433 := bstep (se 2 (by rfl) ⟨388662, by rfl⟩ : syracuseStep 1036433 = 777325) B777325
theorem B970913 : Blo 646304 970913 := bstep (se 2 (by rfl) ⟨364092, by rfl⟩ : syracuseStep 970913 = 728185) B728185
theorem B1233073 : Blo 646304 1233073 := bstep (se 2 (by rfl) ⟨462402, by rfl⟩ : syracuseStep 1233073 = 924805) B924805
theorem B970931 : Blo 646304 970931 := bstep (se 1 (by rfl) ⟨728198, by rfl⟩ : syracuseStep 970931 = 1456397) B1456397
theorem B970961 : Blo 646304 970961 := bstep (se 2 (by rfl) ⟨364110, by rfl⟩ : syracuseStep 970961 = 728221) B728221
theorem B1462481 : Blo 646304 1462481 := bstep (se 2 (by rfl) ⟨548430, by rfl⟩ : syracuseStep 1462481 = 1096861) B1096861
theorem B970979 : Blo 646304 970979 := bstep (se 1 (by rfl) ⟨728234, by rfl⟩ : syracuseStep 970979 = 1456469) B1456469
theorem B1462499 : Blo 646304 1462499 := bstep (se 1 (by rfl) ⟨1096874, by rfl⟩ : syracuseStep 1462499 = 2193749) B2193749
theorem B971009 : Blo 646304 971009 := bstep (se 2 (by rfl) ⟨364128, by rfl⟩ : syracuseStep 971009 = 728257) B728257
theorem B971027 : Blo 646304 971027 := bstep (se 1 (by rfl) ⟨728270, by rfl⟩ : syracuseStep 971027 = 1456541) B1456541
theorem B1069331 : Blo 646304 1069331 := bstep (se 1 (by rfl) ⟨801998, by rfl⟩ : syracuseStep 1069331 = 1603997) B1603997
theorem B971057 : Blo 646304 971057 := bstep (se 2 (by rfl) ⟨364146, by rfl⟩ : syracuseStep 971057 = 728293) B728293
theorem B971075 : Blo 646304 971075 := bstep (se 1 (by rfl) ⟨728306, by rfl⟩ : syracuseStep 971075 = 1456613) B1456613
theorem B971105 : Blo 646304 971105 := bstep (se 2 (by rfl) ⟨364164, by rfl⟩ : syracuseStep 971105 = 728329) B728329
theorem B971123 : Blo 646304 971123 := bstep (se 1 (by rfl) ⟨728342, by rfl⟩ : syracuseStep 971123 = 1456685) B1456685
theorem B971153 : Blo 646304 971153 := bstep (se 2 (by rfl) ⟨364182, by rfl⟩ : syracuseStep 971153 = 728365) B728365
theorem B971171 : Blo 646304 971171 := bstep (se 1 (by rfl) ⟨728378, by rfl⟩ : syracuseStep 971171 = 1456757) B1456757
theorem B1560995 : Blo 646304 1560995 := bstep (se 1 (by rfl) ⟨1170746, by rfl⟩ : syracuseStep 1560995 = 2341493) B2341493
theorem B2183597 : Blo 646304 2183597 := bstep (se 3 (by rfl) ⟨409424, by rfl⟩ : syracuseStep 2183597 = 818849) B818849
theorem B971201 : Blo 646304 971201 := bstep (se 2 (by rfl) ⟨364200, by rfl⟩ : syracuseStep 971201 = 728401) B728401
theorem B971219 : Blo 646304 971219 := bstep (se 1 (by rfl) ⟨728414, by rfl⟩ : syracuseStep 971219 = 1456829) B1456829
theorem B2183651 : Blo 646304 2183651 := bstep (se 1 (by rfl) ⟨1637738, by rfl⟩ : syracuseStep 2183651 = 3275477) B3275477
theorem B4149731 : Blo 646304 4149731 := bstep (se 1 (by rfl) ⟨3112298, by rfl⟩ : syracuseStep 4149731 = 6224597) B6224597
theorem B971249 : Blo 646304 971249 := bstep (se 2 (by rfl) ⟨364218, by rfl⟩ : syracuseStep 971249 = 728437) B728437
theorem B1462769 : Blo 646304 1462769 := bstep (se 2 (by rfl) ⟨548538, by rfl⟩ : syracuseStep 1462769 = 1097077) B1097077
theorem B971267 : Blo 646304 971267 := bstep (se 1 (by rfl) ⟨728450, by rfl⟩ : syracuseStep 971267 = 1456901) B1456901
theorem B1462787 : Blo 646304 1462787 := bstep (se 1 (by rfl) ⟨1097090, by rfl⟩ : syracuseStep 1462787 = 2194181) B2194181
theorem B971297 : Blo 646304 971297 := bstep (se 2 (by rfl) ⟨364236, by rfl⟩ : syracuseStep 971297 = 728473) B728473
theorem B971315 : Blo 646304 971315 := bstep (se 1 (by rfl) ⟨728486, by rfl⟩ : syracuseStep 971315 = 1456973) B1456973
theorem B971345 : Blo 646304 971345 := bstep (se 2 (by rfl) ⟨364254, by rfl⟩ : syracuseStep 971345 = 728509) B728509
theorem B971363 : Blo 646304 971363 := bstep (se 1 (by rfl) ⟨728522, by rfl⟩ : syracuseStep 971363 = 1457045) B1457045
theorem B971393 : Blo 646304 971393 := bstep (se 2 (by rfl) ⟨364272, by rfl⟩ : syracuseStep 971393 = 728545) B728545
theorem B971411 : Blo 646304 971411 := bstep (se 1 (by rfl) ⟨728558, by rfl⟩ : syracuseStep 971411 = 1457117) B1457117
theorem B971441 : Blo 646304 971441 := bstep (se 2 (by rfl) ⟨364290, by rfl⟩ : syracuseStep 971441 = 728581) B728581
theorem B971459 : Blo 646304 971459 := bstep (se 1 (by rfl) ⟨728594, by rfl⟩ : syracuseStep 971459 = 1457189) B1457189
theorem B971489 : Blo 646304 971489 := bstep (se 2 (by rfl) ⟨364308, by rfl⟩ : syracuseStep 971489 = 728617) B728617
theorem B2183921 : Blo 646304 2183921 := bstep (se 2 (by rfl) ⟨818970, by rfl⟩ : syracuseStep 2183921 = 1637941) B1637941
theorem B971507 : Blo 646304 971507 := bstep (se 1 (by rfl) ⟨728630, by rfl⟩ : syracuseStep 971507 = 1457261) B1457261
theorem B971537 : Blo 646304 971537 := bstep (se 2 (by rfl) ⟨364326, by rfl⟩ : syracuseStep 971537 = 728653) B728653
theorem B1463057 : Blo 646304 1463057 := bstep (se 2 (by rfl) ⟨548646, by rfl⟩ : syracuseStep 1463057 = 1097293) B1097293
theorem B971555 : Blo 646304 971555 := bstep (se 1 (by rfl) ⟨728666, by rfl⟩ : syracuseStep 971555 = 1457333) B1457333
theorem B1463075 : Blo 646304 1463075 := bstep (se 1 (by rfl) ⟨1097306, by rfl⟩ : syracuseStep 1463075 = 2194613) B2194613
theorem B971585 : Blo 646304 971585 := bstep (se 2 (by rfl) ⟨364344, by rfl⟩ : syracuseStep 971585 = 728689) B728689
theorem B1168195 : Blo 646304 1168195 := bstep (se 1 (by rfl) ⟨876146, by rfl⟩ : syracuseStep 1168195 = 1752293) B1752293
theorem B971603 : Blo 646304 971603 := bstep (se 1 (by rfl) ⟨728702, by rfl⟩ : syracuseStep 971603 = 1457405) B1457405
theorem B971633 : Blo 646304 971633 := bstep (se 2 (by rfl) ⟨364362, by rfl⟩ : syracuseStep 971633 = 728725) B728725
theorem B971651 : Blo 646304 971651 := bstep (se 1 (by rfl) ⟨728738, by rfl⟩ : syracuseStep 971651 = 1457477) B1457477
theorem B5526413 : Blo 646304 5526413 := bstep (se 3 (by rfl) ⟨1036202, by rfl⟩ : syracuseStep 5526413 = 2072405) B2072405
theorem B971681 : Blo 646304 971681 := bstep (se 2 (by rfl) ⟨364380, by rfl⟩ : syracuseStep 971681 = 728761) B728761
theorem B1495985 : Blo 646304 1495985 := bstep (se 2 (by rfl) ⟨560994, by rfl⟩ : syracuseStep 1495985 = 1121989) B1121989
theorem B971699 : Blo 646304 971699 := bstep (se 1 (by rfl) ⟨728774, by rfl⟩ : syracuseStep 971699 = 1457549) B1457549
theorem B971729 : Blo 646304 971729 := bstep (se 2 (by rfl) ⟨364398, by rfl⟩ : syracuseStep 971729 = 728797) B728797
theorem B971747 : Blo 646304 971747 := bstep (se 1 (by rfl) ⟨728810, by rfl⟩ : syracuseStep 971747 = 1457621) B1457621
theorem B1037299 : Blo 646304 1037299 := bstep (se 1 (by rfl) ⟨777974, by rfl⟩ : syracuseStep 1037299 = 1555949) B1555949
theorem B971777 : Blo 646304 971777 := bstep (se 2 (by rfl) ⟨364416, by rfl⟩ : syracuseStep 971777 = 728833) B728833
theorem B971795 : Blo 646304 971795 := bstep (se 1 (by rfl) ⟨728846, by rfl⟩ : syracuseStep 971795 = 1457693) B1457693
theorem B971825 : Blo 646304 971825 := bstep (se 2 (by rfl) ⟨364434, by rfl⟩ : syracuseStep 971825 = 728869) B728869
theorem B971843 : Blo 646304 971843 := bstep (se 1 (by rfl) ⟨728882, by rfl⟩ : syracuseStep 971843 = 1457765) B1457765
theorem B971873 : Blo 646304 971873 := bstep (se 2 (by rfl) ⟨364452, by rfl⟩ : syracuseStep 971873 = 728905) B728905
theorem B971891 : Blo 646304 971891 := bstep (se 1 (by rfl) ⟨728918, by rfl⟩ : syracuseStep 971891 = 1457837) B1457837
theorem B971921 : Blo 646304 971921 := bstep (se 2 (by rfl) ⟨364470, by rfl⟩ : syracuseStep 971921 = 728941) B728941
theorem B971939 : Blo 646304 971939 := bstep (se 1 (by rfl) ⟨728954, by rfl⟩ : syracuseStep 971939 = 1457909) B1457909
theorem B971969 : Blo 646304 971969 := bstep (se 2 (by rfl) ⟨364488, by rfl⟩ : syracuseStep 971969 = 728977) B728977
theorem B1234129 : Blo 646304 1234129 := bstep (se 2 (by rfl) ⟨462798, by rfl⟩ : syracuseStep 1234129 = 925597) B925597
theorem B971987 : Blo 646304 971987 := bstep (se 1 (by rfl) ⟨728990, by rfl⟩ : syracuseStep 971987 = 1457981) B1457981
theorem B3953891 : Blo 646304 3953891 := bstep (se 1 (by rfl) ⟨2965418, by rfl⟩ : syracuseStep 3953891 = 5930837) B5930837
theorem B972017 : Blo 646304 972017 := bstep (se 2 (by rfl) ⟨364506, by rfl⟩ : syracuseStep 972017 = 729013) B729013
theorem B8869105 : Blo 646304 8869105 := bstep (se 2 (by rfl) ⟨3325914, by rfl⟩ : syracuseStep 8869105 = 6651829) B6651829
theorem B972035 : Blo 646304 972035 := bstep (se 1 (by rfl) ⟨729026, by rfl⟩ : syracuseStep 972035 = 1458053) B1458053
theorem B2184461 : Blo 646304 2184461 := bstep (se 3 (by rfl) ⟨409586, by rfl⟩ : syracuseStep 2184461 = 819173) B819173
theorem B972065 : Blo 646304 972065 := bstep (se 2 (by rfl) ⟨364524, by rfl⟩ : syracuseStep 972065 = 729049) B729049
theorem B972083 : Blo 646304 972083 := bstep (se 1 (by rfl) ⟨729062, by rfl⟩ : syracuseStep 972083 = 1458125) B1458125
theorem B2184515 : Blo 646304 2184515 := bstep (se 1 (by rfl) ⟨1638386, by rfl⟩ : syracuseStep 2184515 = 3276773) B3276773
theorem B972113 : Blo 646304 972113 := bstep (se 2 (by rfl) ⟨364542, by rfl⟩ : syracuseStep 972113 = 729085) B729085
theorem B972131 : Blo 646304 972131 := bstep (se 1 (by rfl) ⟨729098, by rfl⟩ : syracuseStep 972131 = 1458197) B1458197
theorem B972161 : Blo 646304 972161 := bstep (se 2 (by rfl) ⟨364560, by rfl⟩ : syracuseStep 972161 = 729121) B729121
theorem B972179 : Blo 646304 972179 := bstep (se 1 (by rfl) ⟨729134, by rfl⟩ : syracuseStep 972179 = 1458269) B1458269
theorem B972209 : Blo 646304 972209 := bstep (se 2 (by rfl) ⟨364578, by rfl⟩ : syracuseStep 972209 = 729157) B729157
theorem B972227 : Blo 646304 972227 := bstep (se 1 (by rfl) ⟨729170, by rfl⟩ : syracuseStep 972227 = 1458341) B1458341
theorem B972257 : Blo 646304 972257 := bstep (se 2 (by rfl) ⟨364596, by rfl⟩ : syracuseStep 972257 = 729193) B729193
theorem B972275 : Blo 646304 972275 := bstep (se 1 (by rfl) ⟨729206, by rfl⟩ : syracuseStep 972275 = 1458413) B1458413
theorem B972305 : Blo 646304 972305 := bstep (se 2 (by rfl) ⟨364614, by rfl⟩ : syracuseStep 972305 = 729229) B729229
theorem B1562129 : Blo 646304 1562129 := bstep (se 2 (by rfl) ⟨585798, by rfl⟩ : syracuseStep 1562129 = 1171597) B1171597
theorem B972323 : Blo 646304 972323 := bstep (se 1 (by rfl) ⟨729242, by rfl⟩ : syracuseStep 972323 = 1458485) B1458485
theorem B972353 : Blo 646304 972353 := bstep (se 2 (by rfl) ⟨364632, by rfl⟩ : syracuseStep 972353 = 729265) B729265
theorem B2184785 : Blo 646304 2184785 := bstep (se 2 (by rfl) ⟨819294, by rfl⟩ : syracuseStep 2184785 = 1638589) B1638589
theorem B972371 : Blo 646304 972371 := bstep (se 1 (by rfl) ⟨729278, by rfl⟩ : syracuseStep 972371 = 1458557) B1458557
theorem B1234531 : Blo 646304 1234531 := bstep (se 1 (by rfl) ⟨925898, by rfl⟩ : syracuseStep 1234531 = 1851797) B1851797
theorem B972401 : Blo 646304 972401 := bstep (se 2 (by rfl) ⟨364650, by rfl⟩ : syracuseStep 972401 = 729301) B729301
theorem B972419 : Blo 646304 972419 := bstep (se 1 (by rfl) ⟨729314, by rfl⟩ : syracuseStep 972419 = 1458629) B1458629
theorem B1037971 : Blo 646304 1037971 := bstep (se 1 (by rfl) ⟨778478, by rfl⟩ : syracuseStep 1037971 = 1556957) B1556957
theorem B972449 : Blo 646304 972449 := bstep (se 2 (by rfl) ⟨364668, by rfl⟩ : syracuseStep 972449 = 729337) B729337
theorem B972467 : Blo 646304 972467 := bstep (se 1 (by rfl) ⟨729350, by rfl⟩ : syracuseStep 972467 = 1458701) B1458701
theorem B1038017 : Blo 646304 1038017 := bstep (se 2 (by rfl) ⟨389256, by rfl⟩ : syracuseStep 1038017 = 778513) B778513
theorem B972497 : Blo 646304 972497 := bstep (se 2 (by rfl) ⟨364686, by rfl⟩ : syracuseStep 972497 = 729373) B729373
theorem B972515 : Blo 646304 972515 := bstep (se 1 (by rfl) ⟨729386, by rfl⟩ : syracuseStep 972515 = 1458773) B1458773
theorem B972545 : Blo 646304 972545 := bstep (se 2 (by rfl) ⟨364704, by rfl⟩ : syracuseStep 972545 = 729409) B729409
theorem B972563 : Blo 646304 972563 := bstep (se 1 (by rfl) ⟨729422, by rfl⟩ : syracuseStep 972563 = 1458845) B1458845
theorem B972593 : Blo 646304 972593 := bstep (se 2 (by rfl) ⟨364722, by rfl⟩ : syracuseStep 972593 = 729445) B729445
theorem B972611 : Blo 646304 972611 := bstep (se 1 (by rfl) ⟨729458, by rfl⟩ : syracuseStep 972611 = 1458917) B1458917
theorem B972641 : Blo 646304 972641 := bstep (se 2 (by rfl) ⟨364740, by rfl⟩ : syracuseStep 972641 = 729481) B729481
theorem B972659 : Blo 646304 972659 := bstep (se 1 (by rfl) ⟨729494, by rfl⟩ : syracuseStep 972659 = 1458989) B1458989
theorem B16013197 : Blo 646304 16013197 := bstep (se 3 (by rfl) ⟨3002474, by rfl⟩ : syracuseStep 16013197 = 6004949) B6004949
theorem B972689 : Blo 646304 972689 := bstep (se 2 (by rfl) ⟨364758, by rfl⟩ : syracuseStep 972689 = 729517) B729517
theorem B972707 : Blo 646304 972707 := bstep (se 1 (by rfl) ⟨729530, by rfl⟩ : syracuseStep 972707 = 1459061) B1459061
theorem B972737 : Blo 646304 972737 := bstep (se 2 (by rfl) ⟨364776, by rfl⟩ : syracuseStep 972737 = 729553) B729553
theorem B972755 : Blo 646304 972755 := bstep (se 1 (by rfl) ⟨729566, by rfl⟩ : syracuseStep 972755 = 1459133) B1459133
theorem B972785 : Blo 646304 972785 := bstep (se 2 (by rfl) ⟨364794, by rfl⟩ : syracuseStep 972785 = 729589) B729589
theorem B972803 : Blo 646304 972803 := bstep (se 1 (by rfl) ⟨729602, by rfl⟩ : syracuseStep 972803 = 1459205) B1459205
theorem B972833 : Blo 646304 972833 := bstep (se 2 (by rfl) ⟨364812, by rfl⟩ : syracuseStep 972833 = 729625) B729625
theorem B972851 : Blo 646304 972851 := bstep (se 1 (by rfl) ⟨729638, by rfl⟩ : syracuseStep 972851 = 1459277) B1459277
theorem B972881 : Blo 646304 972881 := bstep (se 2 (by rfl) ⟨364830, by rfl⟩ : syracuseStep 972881 = 729661) B729661
theorem B972899 : Blo 646304 972899 := bstep (se 1 (by rfl) ⟨729674, by rfl⟩ : syracuseStep 972899 = 1459349) B1459349
theorem B2185325 : Blo 646304 2185325 := bstep (se 3 (by rfl) ⟨409748, by rfl⟩ : syracuseStep 2185325 = 819497) B819497
theorem B972929 : Blo 646304 972929 := bstep (se 2 (by rfl) ⟨364848, by rfl⟩ : syracuseStep 972929 = 729697) B729697
theorem B972947 : Blo 646304 972947 := bstep (se 1 (by rfl) ⟨729710, by rfl⟩ : syracuseStep 972947 = 1459421) B1459421
theorem B2185379 : Blo 646304 2185379 := bstep (se 1 (by rfl) ⟨1639034, by rfl⟩ : syracuseStep 2185379 = 3278069) B3278069
theorem B972977 : Blo 646304 972977 := bstep (se 2 (by rfl) ⟨364866, by rfl⟩ : syracuseStep 972977 = 729733) B729733
theorem B1038529 : Blo 646304 1038529 := bstep (se 2 (by rfl) ⟨389448, by rfl⟩ : syracuseStep 1038529 = 778897) B778897
theorem B972995 : Blo 646304 972995 := bstep (se 1 (by rfl) ⟨729746, by rfl⟩ : syracuseStep 972995 = 1459493) B1459493
theorem B3692749 : Blo 646304 3692749 := bstep (se 3 (by rfl) ⟨692390, by rfl⟩ : syracuseStep 3692749 = 1384781) B1384781
theorem B973025 : Blo 646304 973025 := bstep (se 2 (by rfl) ⟨364884, by rfl⟩ : syracuseStep 973025 = 729769) B729769
theorem B973043 : Blo 646304 973043 := bstep (se 1 (by rfl) ⟨729782, by rfl⟩ : syracuseStep 973043 = 1459565) B1459565
theorem B973073 : Blo 646304 973073 := bstep (se 2 (by rfl) ⟨364902, by rfl⟩ : syracuseStep 973073 = 729805) B729805
theorem B973091 : Blo 646304 973091 := bstep (se 1 (by rfl) ⟨729818, by rfl⟩ : syracuseStep 973091 = 1459637) B1459637
theorem B973121 : Blo 646304 973121 := bstep (se 2 (by rfl) ⟨364920, by rfl⟩ : syracuseStep 973121 = 729841) B729841
theorem B973139 : Blo 646304 973139 := bstep (se 1 (by rfl) ⟨729854, by rfl⟩ : syracuseStep 973139 = 1459709) B1459709
theorem B973169 : Blo 646304 973169 := bstep (se 2 (by rfl) ⟨364938, by rfl⟩ : syracuseStep 973169 = 729877) B729877
theorem B973187 : Blo 646304 973187 := bstep (se 1 (by rfl) ⟨729890, by rfl⟩ : syracuseStep 973187 = 1459781) B1459781
theorem B973217 : Blo 646304 973217 := bstep (se 2 (by rfl) ⟨364956, by rfl⟩ : syracuseStep 973217 = 729913) B729913
theorem B2185649 : Blo 646304 2185649 := bstep (se 2 (by rfl) ⟨819618, by rfl⟩ : syracuseStep 2185649 = 1639237) B1639237
theorem B973235 : Blo 646304 973235 := bstep (se 1 (by rfl) ⟨729926, by rfl⟩ : syracuseStep 973235 = 1459853) B1459853
theorem B973265 : Blo 646304 973265 := bstep (se 2 (by rfl) ⟨364974, by rfl⟩ : syracuseStep 973265 = 729949) B729949
theorem B973283 : Blo 646304 973283 := bstep (se 1 (by rfl) ⟨729962, by rfl⟩ : syracuseStep 973283 = 1459925) B1459925
theorem B973313 : Blo 646304 973313 := bstep (se 2 (by rfl) ⟨364992, by rfl⟩ : syracuseStep 973313 = 729985) B729985
theorem B973331 : Blo 646304 973331 := bstep (se 1 (by rfl) ⟨729998, by rfl⟩ : syracuseStep 973331 = 1459997) B1459997
theorem B973361 : Blo 646304 973361 := bstep (se 2 (by rfl) ⟨365010, by rfl⟩ : syracuseStep 973361 = 730021) B730021
theorem B973379 : Blo 646304 973379 := bstep (se 1 (by rfl) ⟨730034, by rfl⟩ : syracuseStep 973379 = 1460069) B1460069
theorem B973409 : Blo 646304 973409 := bstep (se 2 (by rfl) ⟨365028, by rfl⟩ : syracuseStep 973409 = 730057) B730057
theorem B973427 : Blo 646304 973427 := bstep (se 1 (by rfl) ⟨730070, by rfl⟩ : syracuseStep 973427 = 1460141) B1460141
theorem B973457 : Blo 646304 973457 := bstep (se 2 (by rfl) ⟨365046, by rfl⟩ : syracuseStep 973457 = 730093) B730093
theorem B973475 : Blo 646304 973475 := bstep (se 1 (by rfl) ⟨730106, by rfl⟩ : syracuseStep 973475 = 1460213) B1460213
theorem B973505 : Blo 646304 973505 := bstep (se 2 (by rfl) ⟨365064, by rfl⟩ : syracuseStep 973505 = 730129) B730129
theorem B973523 : Blo 646304 973523 := bstep (se 1 (by rfl) ⟨730142, by rfl⟩ : syracuseStep 973523 = 1460285) B1460285
theorem B1039073 : Blo 646304 1039073 := bstep (se 2 (by rfl) ⟨389652, by rfl⟩ : syracuseStep 1039073 = 779305) B779305
theorem B973553 : Blo 646304 973553 := bstep (se 2 (by rfl) ⟨365082, by rfl⟩ : syracuseStep 973553 = 730165) B730165
theorem B973571 : Blo 646304 973571 := bstep (se 1 (by rfl) ⟨730178, by rfl⟩ : syracuseStep 973571 = 1460357) B1460357
theorem B973601 : Blo 646304 973601 := bstep (se 2 (by rfl) ⟨365100, by rfl⟩ : syracuseStep 973601 = 730201) B730201
theorem B973619 : Blo 646304 973619 := bstep (se 1 (by rfl) ⟨730214, by rfl⟩ : syracuseStep 973619 = 1460429) B1460429
theorem B973649 : Blo 646304 973649 := bstep (se 2 (by rfl) ⟨365118, by rfl⟩ : syracuseStep 973649 = 730237) B730237
theorem B973667 : Blo 646304 973667 := bstep (se 1 (by rfl) ⟨730250, by rfl⟩ : syracuseStep 973667 = 1460501) B1460501
theorem B1661809 : Blo 646304 1661809 := bstep (se 2 (by rfl) ⟨623178, by rfl⟩ : syracuseStep 1661809 = 1246357) B1246357
theorem B973697 : Blo 646304 973697 := bstep (se 2 (by rfl) ⟨365136, by rfl⟩ : syracuseStep 973697 = 730273) B730273
theorem B973715 : Blo 646304 973715 := bstep (se 1 (by rfl) ⟨730286, by rfl⟩ : syracuseStep 973715 = 1460573) B1460573
theorem B2775971 : Blo 646304 2775971 := bstep (se 1 (by rfl) ⟨2081978, by rfl⟩ : syracuseStep 2775971 = 4163957) B4163957
theorem B973745 : Blo 646304 973745 := bstep (se 2 (by rfl) ⟨365154, by rfl⟩ : syracuseStep 973745 = 730309) B730309
theorem B973763 : Blo 646304 973763 := bstep (se 1 (by rfl) ⟨730322, by rfl⟩ : syracuseStep 973763 = 1460645) B1460645
theorem B2186189 : Blo 646304 2186189 := bstep (se 3 (by rfl) ⟨409910, by rfl⟩ : syracuseStep 2186189 = 819821) B819821
theorem B973793 : Blo 646304 973793 := bstep (se 2 (by rfl) ⟨365172, by rfl⟩ : syracuseStep 973793 = 730345) B730345
theorem B973811 : Blo 646304 973811 := bstep (se 1 (by rfl) ⟨730358, by rfl⟩ : syracuseStep 973811 = 1460717) B1460717
theorem B2186243 : Blo 646304 2186243 := bstep (se 1 (by rfl) ⟨1639682, by rfl⟩ : syracuseStep 2186243 = 3279365) B3279365
theorem B973841 : Blo 646304 973841 := bstep (se 2 (by rfl) ⟨365190, by rfl⟩ : syracuseStep 973841 = 730381) B730381
theorem B973859 : Blo 646304 973859 := bstep (se 1 (by rfl) ⟨730394, by rfl⟩ : syracuseStep 973859 = 1460789) B1460789
theorem B973889 : Blo 646304 973889 := bstep (se 2 (by rfl) ⟨365208, by rfl⟩ : syracuseStep 973889 = 730417) B730417
theorem B973907 : Blo 646304 973907 := bstep (se 1 (by rfl) ⟨730430, by rfl⟩ : syracuseStep 973907 = 1460861) B1460861
theorem B973937 : Blo 646304 973937 := bstep (se 2 (by rfl) ⟨365226, by rfl⟩ : syracuseStep 973937 = 730453) B730453
theorem B973955 : Blo 646304 973955 := bstep (se 1 (by rfl) ⟨730466, by rfl⟩ : syracuseStep 973955 = 1460933) B1460933
theorem B973985 : Blo 646304 973985 := bstep (se 2 (by rfl) ⟨365244, by rfl⟩ : syracuseStep 973985 = 730489) B730489
theorem B646307 : Blo 646304 646307 := bstep (se 1 (by rfl) ⟨484730, by rfl⟩ : syracuseStep 646307 = 969461) B969461
theorem B646323 : Blo 646304 646323 := bstep (se 1 (by rfl) ⟨484742, by rfl⟩ : syracuseStep 646323 = 969485) B969485
theorem B974003 : Blo 646304 974003 := bstep (se 1 (by rfl) ⟨730502, by rfl⟩ : syracuseStep 974003 = 1461005) B1461005
theorem B646339 : Blo 646304 646339 := bstep (se 1 (by rfl) ⟨484754, by rfl⟩ : syracuseStep 646339 = 969509) B969509
theorem B974033 : Blo 646304 974033 := bstep (se 2 (by rfl) ⟨365262, by rfl⟩ : syracuseStep 974033 = 730525) B730525
theorem B646355 : Blo 646304 646355 := bstep (se 1 (by rfl) ⟨484766, by rfl⟩ : syracuseStep 646355 = 969533) B969533
theorem B646371 : Blo 646304 646371 := bstep (se 1 (by rfl) ⟨484778, by rfl⟩ : syracuseStep 646371 = 969557) B969557
theorem B974051 : Blo 646304 974051 := bstep (se 1 (by rfl) ⟨730538, by rfl⟩ : syracuseStep 974051 = 1461077) B1461077
theorem B1170659 : Blo 646304 1170659 := bstep (se 1 (by rfl) ⟨877994, by rfl⟩ : syracuseStep 1170659 = 1755989) B1755989
theorem B646387 : Blo 646304 646387 := bstep (se 1 (by rfl) ⟨484790, by rfl⟩ : syracuseStep 646387 = 969581) B969581
theorem B974081 : Blo 646304 974081 := bstep (se 2 (by rfl) ⟨365280, by rfl⟩ : syracuseStep 974081 = 730561) B730561
theorem B646403 : Blo 646304 646403 := bstep (se 1 (by rfl) ⟨484802, by rfl⟩ : syracuseStep 646403 = 969605) B969605
theorem B777475 : Blo 646304 777475 := bstep (se 1 (by rfl) ⟨583106, by rfl⟩ : syracuseStep 777475 = 1166213) B1166213
theorem B1662211 : Blo 646304 1662211 := bstep (se 1 (by rfl) ⟨1246658, by rfl⟩ : syracuseStep 1662211 = 2493317) B2493317
theorem B2186513 : Blo 646304 2186513 := bstep (se 2 (by rfl) ⟨819942, by rfl⟩ : syracuseStep 2186513 = 1639885) B1639885
theorem B646419 : Blo 646304 646419 := bstep (se 1 (by rfl) ⟨484814, by rfl⟩ : syracuseStep 646419 = 969629) B969629
theorem B974099 : Blo 646304 974099 := bstep (se 1 (by rfl) ⟨730574, by rfl⟩ : syracuseStep 974099 = 1461149) B1461149
theorem B646435 : Blo 646304 646435 := bstep (se 1 (by rfl) ⟨484826, by rfl⟩ : syracuseStep 646435 = 969653) B969653
theorem B974129 : Blo 646304 974129 := bstep (se 2 (by rfl) ⟨365298, by rfl⟩ : syracuseStep 974129 = 730597) B730597
theorem B646451 : Blo 646304 646451 := bstep (se 1 (by rfl) ⟨484838, by rfl⟩ : syracuseStep 646451 = 969677) B969677
theorem B646467 : Blo 646304 646467 := bstep (se 1 (by rfl) ⟨484850, by rfl⟩ : syracuseStep 646467 = 969701) B969701
theorem B974147 : Blo 646304 974147 := bstep (se 1 (by rfl) ⟨730610, by rfl⟩ : syracuseStep 974147 = 1461221) B1461221
theorem B646483 : Blo 646304 646483 := bstep (se 1 (by rfl) ⟨484862, by rfl⟩ : syracuseStep 646483 = 969725) B969725
theorem B974177 : Blo 646304 974177 := bstep (se 2 (by rfl) ⟨365316, by rfl⟩ : syracuseStep 974177 = 730633) B730633
theorem B646499 : Blo 646304 646499 := bstep (se 1 (by rfl) ⟨484874, by rfl⟩ : syracuseStep 646499 = 969749) B969749
theorem B875875 : Blo 646304 875875 := bstep (se 1 (by rfl) ⟨656906, by rfl⟩ : syracuseStep 875875 = 1313813) B1313813
theorem B646515 : Blo 646304 646515 := bstep (se 1 (by rfl) ⟨484886, by rfl⟩ : syracuseStep 646515 = 969773) B969773
theorem B974195 : Blo 646304 974195 := bstep (se 1 (by rfl) ⟨730646, by rfl⟩ : syracuseStep 974195 = 1461293) B1461293
theorem B646531 : Blo 646304 646531 := bstep (se 1 (by rfl) ⟨484898, by rfl⟩ : syracuseStep 646531 = 969797) B969797
theorem B974225 : Blo 646304 974225 := bstep (se 2 (by rfl) ⟨365334, by rfl⟩ : syracuseStep 974225 = 730669) B730669
theorem B646547 : Blo 646304 646547 := bstep (se 1 (by rfl) ⟨484910, by rfl⟩ : syracuseStep 646547 = 969821) B969821
theorem B646563 : Blo 646304 646563 := bstep (se 1 (by rfl) ⟨484922, by rfl⟩ : syracuseStep 646563 = 969845) B969845
theorem B974243 : Blo 646304 974243 := bstep (se 1 (by rfl) ⟨730682, by rfl⟩ : syracuseStep 974243 = 1461365) B1461365
theorem B646579 : Blo 646304 646579 := bstep (se 1 (by rfl) ⟨484934, by rfl⟩ : syracuseStep 646579 = 969869) B969869
theorem B974273 : Blo 646304 974273 := bstep (se 2 (by rfl) ⟨365352, by rfl⟩ : syracuseStep 974273 = 730705) B730705
theorem B646595 : Blo 646304 646595 := bstep (se 1 (by rfl) ⟨484946, by rfl⟩ : syracuseStep 646595 = 969893) B969893
theorem B777667 : Blo 646304 777667 := bstep (se 1 (by rfl) ⟨583250, by rfl⟩ : syracuseStep 777667 = 1166501) B1166501
theorem B646611 : Blo 646304 646611 := bstep (se 1 (by rfl) ⟨484958, by rfl⟩ : syracuseStep 646611 = 969917) B969917
theorem B974291 : Blo 646304 974291 := bstep (se 1 (by rfl) ⟨730718, by rfl⟩ : syracuseStep 974291 = 1461437) B1461437
theorem B646627 : Blo 646304 646627 := bstep (se 1 (by rfl) ⟨484970, by rfl⟩ : syracuseStep 646627 = 969941) B969941
theorem B974321 : Blo 646304 974321 := bstep (se 2 (by rfl) ⟨365370, by rfl⟩ : syracuseStep 974321 = 730741) B730741
theorem B646643 : Blo 646304 646643 := bstep (se 1 (by rfl) ⟨484982, by rfl⟩ : syracuseStep 646643 = 969965) B969965
theorem B646659 : Blo 646304 646659 := bstep (se 1 (by rfl) ⟨484994, by rfl⟩ : syracuseStep 646659 = 969989) B969989
theorem B974339 : Blo 646304 974339 := bstep (se 1 (by rfl) ⟨730754, by rfl⟩ : syracuseStep 974339 = 1461509) B1461509
theorem B646675 : Blo 646304 646675 := bstep (se 1 (by rfl) ⟨485006, by rfl⟩ : syracuseStep 646675 = 970013) B970013
theorem B974369 : Blo 646304 974369 := bstep (se 2 (by rfl) ⟨365388, by rfl⟩ : syracuseStep 974369 = 730777) B730777
theorem B646691 : Blo 646304 646691 := bstep (se 1 (by rfl) ⟨485018, by rfl⟩ : syracuseStep 646691 = 970037) B970037
theorem B646707 : Blo 646304 646707 := bstep (se 1 (by rfl) ⟨485030, by rfl⟩ : syracuseStep 646707 = 970061) B970061
theorem B974387 : Blo 646304 974387 := bstep (se 1 (by rfl) ⟨730790, by rfl⟩ : syracuseStep 974387 = 1461581) B1461581
theorem B646723 : Blo 646304 646723 := bstep (se 1 (by rfl) ⟨485042, by rfl⟩ : syracuseStep 646723 = 970085) B970085
theorem B974417 : Blo 646304 974417 := bstep (se 2 (by rfl) ⟨365406, by rfl⟩ : syracuseStep 974417 = 730813) B730813
theorem B646739 : Blo 646304 646739 := bstep (se 1 (by rfl) ⟨485054, by rfl⟩ : syracuseStep 646739 = 970109) B970109
theorem B646755 : Blo 646304 646755 := bstep (se 1 (by rfl) ⟨485066, by rfl⟩ : syracuseStep 646755 = 970133) B970133
theorem B974435 : Blo 646304 974435 := bstep (se 1 (by rfl) ⟨730826, by rfl⟩ : syracuseStep 974435 = 1461653) B1461653
theorem B646771 : Blo 646304 646771 := bstep (se 1 (by rfl) ⟨485078, by rfl⟩ : syracuseStep 646771 = 970157) B970157
theorem B974465 : Blo 646304 974465 := bstep (se 2 (by rfl) ⟨365424, by rfl⟩ : syracuseStep 974465 = 730849) B730849
theorem B646787 : Blo 646304 646787 := bstep (se 1 (by rfl) ⟨485090, by rfl⟩ : syracuseStep 646787 = 970181) B970181
theorem B646803 : Blo 646304 646803 := bstep (se 1 (by rfl) ⟨485102, by rfl⟩ : syracuseStep 646803 = 970205) B970205
theorem B974483 : Blo 646304 974483 := bstep (se 1 (by rfl) ⟨730862, by rfl⟩ : syracuseStep 974483 = 1461725) B1461725
theorem B646819 : Blo 646304 646819 := bstep (se 1 (by rfl) ⟨485114, by rfl⟩ : syracuseStep 646819 = 970229) B970229
theorem B1400483 : Blo 646304 1400483 := bstep (se 1 (by rfl) ⟨1050362, by rfl⟩ : syracuseStep 1400483 = 2100725) B2100725
theorem B1040035 : Blo 646304 1040035 := bstep (se 1 (by rfl) ⟨780026, by rfl⟩ : syracuseStep 1040035 = 1560053) B1560053
theorem B974513 : Blo 646304 974513 := bstep (se 2 (by rfl) ⟨365442, by rfl⟩ : syracuseStep 974513 = 730885) B730885
theorem B646835 : Blo 646304 646835 := bstep (se 1 (by rfl) ⟨485126, by rfl⟩ : syracuseStep 646835 = 970253) B970253
theorem B646851 : Blo 646304 646851 := bstep (se 1 (by rfl) ⟨485138, by rfl⟩ : syracuseStep 646851 = 970277) B970277
theorem B974531 : Blo 646304 974531 := bstep (se 1 (by rfl) ⟨730898, by rfl⟩ : syracuseStep 974531 = 1461797) B1461797
theorem B646867 : Blo 646304 646867 := bstep (se 1 (by rfl) ⟨485150, by rfl⟩ : syracuseStep 646867 = 970301) B970301
theorem B974561 : Blo 646304 974561 := bstep (se 2 (by rfl) ⟨365460, by rfl⟩ : syracuseStep 974561 = 730921) B730921
theorem B646883 : Blo 646304 646883 := bstep (se 1 (by rfl) ⟨485162, by rfl⟩ : syracuseStep 646883 = 970325) B970325
theorem B1335025 : Blo 646304 1335025 := bstep (se 2 (by rfl) ⟨500634, by rfl⟩ : syracuseStep 1335025 = 1001269) B1001269
theorem B646899 : Blo 646304 646899 := bstep (se 1 (by rfl) ⟨485174, by rfl⟩ : syracuseStep 646899 = 970349) B970349
theorem B974579 : Blo 646304 974579 := bstep (se 1 (by rfl) ⟨730934, by rfl⟩ : syracuseStep 974579 = 1461869) B1461869
theorem B646915 : Blo 646304 646915 := bstep (se 1 (by rfl) ⟨485186, by rfl⟩ : syracuseStep 646915 = 970373) B970373
theorem B974609 : Blo 646304 974609 := bstep (se 2 (by rfl) ⟨365478, by rfl⟩ : syracuseStep 974609 = 730957) B730957
theorem B646931 : Blo 646304 646931 := bstep (se 1 (by rfl) ⟨485198, by rfl⟩ : syracuseStep 646931 = 970397) B970397
theorem B646947 : Blo 646304 646947 := bstep (se 1 (by rfl) ⟨485210, by rfl⟩ : syracuseStep 646947 = 970421) B970421
theorem B974627 : Blo 646304 974627 := bstep (se 1 (by rfl) ⟨730970, by rfl⟩ : syracuseStep 974627 = 1461941) B1461941
theorem B2187053 : Blo 646304 2187053 := bstep (se 3 (by rfl) ⟨410072, by rfl⟩ : syracuseStep 2187053 = 820145) B820145
theorem B646963 : Blo 646304 646963 := bstep (se 1 (by rfl) ⟨485222, by rfl⟩ : syracuseStep 646963 = 970445) B970445
theorem B974657 : Blo 646304 974657 := bstep (se 2 (by rfl) ⟨365496, by rfl⟩ : syracuseStep 974657 = 730993) B730993
theorem B646979 : Blo 646304 646979 := bstep (se 1 (by rfl) ⟨485234, by rfl⟩ : syracuseStep 646979 = 970469) B970469
theorem B646995 : Blo 646304 646995 := bstep (se 1 (by rfl) ⟨485246, by rfl⟩ : syracuseStep 646995 = 970493) B970493
theorem B974675 : Blo 646304 974675 := bstep (se 1 (by rfl) ⟨731006, by rfl⟩ : syracuseStep 974675 = 1462013) B1462013
theorem B647011 : Blo 646304 647011 := bstep (se 1 (by rfl) ⟨485258, by rfl⟩ : syracuseStep 647011 = 970517) B970517
theorem B2187107 : Blo 646304 2187107 := bstep (se 1 (by rfl) ⟨1640330, by rfl⟩ : syracuseStep 2187107 = 3280661) B3280661
theorem B974705 : Blo 646304 974705 := bstep (se 2 (by rfl) ⟨365514, by rfl⟩ : syracuseStep 974705 = 731029) B731029
theorem B647027 : Blo 646304 647027 := bstep (se 1 (by rfl) ⟨485270, by rfl⟩ : syracuseStep 647027 = 970541) B970541
theorem B647043 : Blo 646304 647043 := bstep (se 1 (by rfl) ⟨485282, by rfl⟩ : syracuseStep 647043 = 970565) B970565
theorem B974723 : Blo 646304 974723 := bstep (se 1 (by rfl) ⟨731042, by rfl⟩ : syracuseStep 974723 = 1462085) B1462085
theorem B647059 : Blo 646304 647059 := bstep (se 1 (by rfl) ⟨485294, by rfl⟩ : syracuseStep 647059 = 970589) B970589
theorem B974753 : Blo 646304 974753 := bstep (se 2 (by rfl) ⟨365532, by rfl⟩ : syracuseStep 974753 = 731065) B731065
theorem B647075 : Blo 646304 647075 := bstep (se 1 (by rfl) ⟨485306, by rfl⟩ : syracuseStep 647075 = 970613) B970613
theorem B1040291 : Blo 646304 1040291 := bstep (se 1 (by rfl) ⟨780218, by rfl⟩ : syracuseStep 1040291 = 1560437) B1560437
theorem B647091 : Blo 646304 647091 := bstep (se 1 (by rfl) ⟨485318, by rfl⟩ : syracuseStep 647091 = 970637) B970637
theorem B974771 : Blo 646304 974771 := bstep (se 1 (by rfl) ⟨731078, by rfl⟩ : syracuseStep 974771 = 1462157) B1462157
theorem B647107 : Blo 646304 647107 := bstep (se 1 (by rfl) ⟨485330, by rfl⟩ : syracuseStep 647107 = 970661) B970661
theorem B974801 : Blo 646304 974801 := bstep (se 2 (by rfl) ⟨365550, by rfl⟩ : syracuseStep 974801 = 731101) B731101
theorem B647123 : Blo 646304 647123 := bstep (se 1 (by rfl) ⟨485342, by rfl⟩ : syracuseStep 647123 = 970685) B970685
theorem B647139 : Blo 646304 647139 := bstep (se 1 (by rfl) ⟨485354, by rfl⟩ : syracuseStep 647139 = 970709) B970709
theorem B974819 : Blo 646304 974819 := bstep (se 1 (by rfl) ⟨731114, by rfl⟩ : syracuseStep 974819 = 1462229) B1462229
theorem B647155 : Blo 646304 647155 := bstep (se 1 (by rfl) ⟨485366, by rfl⟩ : syracuseStep 647155 = 970733) B970733
theorem B974849 : Blo 646304 974849 := bstep (se 2 (by rfl) ⟨365568, by rfl⟩ : syracuseStep 974849 = 731137) B731137
theorem B647171 : Blo 646304 647171 := bstep (se 1 (by rfl) ⟨485378, by rfl⟩ : syracuseStep 647171 = 970757) B970757
theorem B647187 : Blo 646304 647187 := bstep (se 1 (by rfl) ⟨485390, by rfl⟩ : syracuseStep 647187 = 970781) B970781
theorem B974867 : Blo 646304 974867 := bstep (se 1 (by rfl) ⟨731150, by rfl⟩ : syracuseStep 974867 = 1462301) B1462301
theorem B647203 : Blo 646304 647203 := bstep (se 1 (by rfl) ⟨485402, by rfl⟩ : syracuseStep 647203 = 970805) B970805
theorem B974897 : Blo 646304 974897 := bstep (se 2 (by rfl) ⟨365586, by rfl⟩ : syracuseStep 974897 = 731173) B731173
theorem B647219 : Blo 646304 647219 := bstep (se 1 (by rfl) ⟨485414, by rfl⟩ : syracuseStep 647219 = 970829) B970829
theorem B647235 : Blo 646304 647235 := bstep (se 1 (by rfl) ⟨485426, by rfl⟩ : syracuseStep 647235 = 970853) B970853
theorem B974915 : Blo 646304 974915 := bstep (se 1 (by rfl) ⟨731186, by rfl⟩ : syracuseStep 974915 = 1462373) B1462373
theorem B647251 : Blo 646304 647251 := bstep (se 1 (by rfl) ⟨485438, by rfl⟩ : syracuseStep 647251 = 970877) B970877
theorem B974945 : Blo 646304 974945 := bstep (se 2 (by rfl) ⟨365604, by rfl⟩ : syracuseStep 974945 = 731209) B731209
theorem B647267 : Blo 646304 647267 := bstep (se 1 (by rfl) ⟨485450, by rfl⟩ : syracuseStep 647267 = 970901) B970901
theorem B2187377 : Blo 646304 2187377 := bstep (se 2 (by rfl) ⟨820266, by rfl⟩ : syracuseStep 2187377 = 1640533) B1640533
theorem B647283 : Blo 646304 647283 := bstep (se 1 (by rfl) ⟨485462, by rfl⟩ : syracuseStep 647283 = 970925) B970925
theorem B974963 : Blo 646304 974963 := bstep (se 1 (by rfl) ⟨731222, by rfl⟩ : syracuseStep 974963 = 1462445) B1462445
theorem B647299 : Blo 646304 647299 := bstep (se 1 (by rfl) ⟨485474, by rfl⟩ : syracuseStep 647299 = 970949) B970949
theorem B3694733 : Blo 646304 3694733 := bstep (se 3 (by rfl) ⟨692762, by rfl⟩ : syracuseStep 3694733 = 1385525) B1385525
theorem B974993 : Blo 646304 974993 := bstep (se 2 (by rfl) ⟨365622, by rfl⟩ : syracuseStep 974993 = 731245) B731245
theorem B647315 : Blo 646304 647315 := bstep (se 1 (by rfl) ⟨485486, by rfl⟩ : syracuseStep 647315 = 970973) B970973
theorem B647331 : Blo 646304 647331 := bstep (se 1 (by rfl) ⟨485498, by rfl⟩ : syracuseStep 647331 = 970997) B970997
theorem B975011 : Blo 646304 975011 := bstep (se 1 (by rfl) ⟨731258, by rfl⟩ : syracuseStep 975011 = 1462517) B1462517
theorem B647347 : Blo 646304 647347 := bstep (se 1 (by rfl) ⟨485510, by rfl⟩ : syracuseStep 647347 = 971021) B971021
theorem B975041 : Blo 646304 975041 := bstep (se 2 (by rfl) ⟨365640, by rfl⟩ : syracuseStep 975041 = 731281) B731281
theorem B647363 : Blo 646304 647363 := bstep (se 1 (by rfl) ⟨485522, by rfl⟩ : syracuseStep 647363 = 971045) B971045
theorem B647379 : Blo 646304 647379 := bstep (se 1 (by rfl) ⟨485534, by rfl⟩ : syracuseStep 647379 = 971069) B971069
theorem B975059 : Blo 646304 975059 := bstep (se 1 (by rfl) ⟨731294, by rfl⟩ : syracuseStep 975059 = 1462589) B1462589
theorem B647395 : Blo 646304 647395 := bstep (se 1 (by rfl) ⟨485546, by rfl⟩ : syracuseStep 647395 = 971093) B971093
theorem B975089 : Blo 646304 975089 := bstep (se 2 (by rfl) ⟨365658, by rfl⟩ : syracuseStep 975089 = 731317) B731317
theorem B647411 : Blo 646304 647411 := bstep (se 1 (by rfl) ⟨485558, by rfl⟩ : syracuseStep 647411 = 971117) B971117
theorem B647427 : Blo 646304 647427 := bstep (se 1 (by rfl) ⟨485570, by rfl⟩ : syracuseStep 647427 = 971141) B971141
theorem B975107 : Blo 646304 975107 := bstep (se 1 (by rfl) ⟨731330, by rfl⟩ : syracuseStep 975107 = 1462661) B1462661
theorem B647443 : Blo 646304 647443 := bstep (se 1 (by rfl) ⟨485582, by rfl⟩ : syracuseStep 647443 = 971165) B971165
theorem B975137 : Blo 646304 975137 := bstep (se 2 (by rfl) ⟨365676, by rfl⟩ : syracuseStep 975137 = 731353) B731353
theorem B647459 : Blo 646304 647459 := bstep (se 1 (by rfl) ⟨485594, by rfl⟩ : syracuseStep 647459 = 971189) B971189
theorem B647475 : Blo 646304 647475 := bstep (se 1 (by rfl) ⟨485606, by rfl⟩ : syracuseStep 647475 = 971213) B971213
theorem B975155 : Blo 646304 975155 := bstep (se 1 (by rfl) ⟨731366, by rfl⟩ : syracuseStep 975155 = 1462733) B1462733
theorem B647491 : Blo 646304 647491 := bstep (se 1 (by rfl) ⟨485618, by rfl⟩ : syracuseStep 647491 = 971237) B971237
theorem B975185 : Blo 646304 975185 := bstep (se 2 (by rfl) ⟨365694, by rfl⟩ : syracuseStep 975185 = 731389) B731389
theorem B647507 : Blo 646304 647507 := bstep (se 1 (by rfl) ⟨485630, by rfl⟩ : syracuseStep 647507 = 971261) B971261
theorem B647523 : Blo 646304 647523 := bstep (se 1 (by rfl) ⟨485642, by rfl⟩ : syracuseStep 647523 = 971285) B971285
theorem B975203 : Blo 646304 975203 := bstep (se 1 (by rfl) ⟨731402, by rfl⟩ : syracuseStep 975203 = 1462805) B1462805
theorem B647539 : Blo 646304 647539 := bstep (se 1 (by rfl) ⟨485654, by rfl⟩ : syracuseStep 647539 = 971309) B971309
theorem B975233 : Blo 646304 975233 := bstep (se 2 (by rfl) ⟨365712, by rfl⟩ : syracuseStep 975233 = 731425) B731425
theorem B647555 : Blo 646304 647555 := bstep (se 1 (by rfl) ⟨485666, by rfl⟩ : syracuseStep 647555 = 971333) B971333
theorem B647571 : Blo 646304 647571 := bstep (se 1 (by rfl) ⟨485678, by rfl⟩ : syracuseStep 647571 = 971357) B971357
theorem B975251 : Blo 646304 975251 := bstep (se 1 (by rfl) ⟨731438, by rfl⟩ : syracuseStep 975251 = 1462877) B1462877
theorem B647587 : Blo 646304 647587 := bstep (se 1 (by rfl) ⟨485690, by rfl⟩ : syracuseStep 647587 = 971381) B971381
theorem B975281 : Blo 646304 975281 := bstep (se 2 (by rfl) ⟨365730, by rfl⟩ : syracuseStep 975281 = 731461) B731461
theorem B647603 : Blo 646304 647603 := bstep (se 1 (by rfl) ⟨485702, by rfl⟩ : syracuseStep 647603 = 971405) B971405
theorem B647619 : Blo 646304 647619 := bstep (se 1 (by rfl) ⟨485714, by rfl⟩ : syracuseStep 647619 = 971429) B971429
theorem B975299 : Blo 646304 975299 := bstep (se 1 (by rfl) ⟨731474, by rfl⟩ : syracuseStep 975299 = 1462949) B1462949
theorem B647635 : Blo 646304 647635 := bstep (se 1 (by rfl) ⟨485726, by rfl⟩ : syracuseStep 647635 = 971453) B971453
theorem B975329 : Blo 646304 975329 := bstep (se 2 (by rfl) ⟨365748, by rfl⟩ : syracuseStep 975329 = 731497) B731497
theorem B647651 : Blo 646304 647651 := bstep (se 1 (by rfl) ⟨485738, by rfl⟩ : syracuseStep 647651 = 971477) B971477
theorem B647667 : Blo 646304 647667 := bstep (se 1 (by rfl) ⟨485750, by rfl⟩ : syracuseStep 647667 = 971501) B971501
theorem B975347 : Blo 646304 975347 := bstep (se 1 (by rfl) ⟨731510, by rfl⟩ : syracuseStep 975347 = 1463021) B1463021
theorem B647683 : Blo 646304 647683 := bstep (se 1 (by rfl) ⟨485762, by rfl⟩ : syracuseStep 647683 = 971525) B971525
theorem B975377 : Blo 646304 975377 := bstep (se 2 (by rfl) ⟨365766, by rfl⟩ : syracuseStep 975377 = 731533) B731533
theorem B647699 : Blo 646304 647699 := bstep (se 1 (by rfl) ⟨485774, by rfl⟩ : syracuseStep 647699 = 971549) B971549
theorem B647715 : Blo 646304 647715 := bstep (se 1 (by rfl) ⟨485786, by rfl⟩ : syracuseStep 647715 = 971573) B971573
theorem B975395 : Blo 646304 975395 := bstep (se 1 (by rfl) ⟨731546, by rfl⟩ : syracuseStep 975395 = 1463093) B1463093
theorem B647731 : Blo 646304 647731 := bstep (se 1 (by rfl) ⟨485798, by rfl⟩ : syracuseStep 647731 = 971597) B971597
theorem B975425 : Blo 646304 975425 := bstep (se 2 (by rfl) ⟨365784, by rfl⟩ : syracuseStep 975425 = 731569) B731569
theorem B647747 : Blo 646304 647747 := bstep (se 1 (by rfl) ⟨485810, by rfl⟩ : syracuseStep 647747 = 971621) B971621
theorem B4153933 : Blo 646304 4153933 := bstep (se 3 (by rfl) ⟨778862, by rfl⟩ : syracuseStep 4153933 = 1557725) B1557725
theorem B647763 : Blo 646304 647763 := bstep (se 1 (by rfl) ⟨485822, by rfl⟩ : syracuseStep 647763 = 971645) B971645
theorem B975443 : Blo 646304 975443 := bstep (se 1 (by rfl) ⟨731582, by rfl⟩ : syracuseStep 975443 = 1463165) B1463165
theorem B647779 : Blo 646304 647779 := bstep (se 1 (by rfl) ⟨485834, by rfl⟩ : syracuseStep 647779 = 971669) B971669
theorem B1040995 : Blo 646304 1040995 := bstep (se 1 (by rfl) ⟨780746, by rfl⟩ : syracuseStep 1040995 = 1561493) B1561493
theorem B647795 : Blo 646304 647795 := bstep (se 1 (by rfl) ⟨485846, by rfl⟩ : syracuseStep 647795 = 971693) B971693
theorem B647811 : Blo 646304 647811 := bstep (se 1 (by rfl) ⟨485858, by rfl⟩ : syracuseStep 647811 = 971717) B971717
theorem B2187917 : Blo 646304 2187917 := bstep (se 3 (by rfl) ⟨410234, by rfl⟩ : syracuseStep 2187917 = 820469) B820469
theorem B647827 : Blo 646304 647827 := bstep (se 1 (by rfl) ⟨485870, by rfl⟩ : syracuseStep 647827 = 971741) B971741
theorem B647843 : Blo 646304 647843 := bstep (se 1 (by rfl) ⟨485882, by rfl⟩ : syracuseStep 647843 = 971765) B971765
theorem B647859 : Blo 646304 647859 := bstep (se 1 (by rfl) ⟨485894, by rfl⟩ : syracuseStep 647859 = 971789) B971789
theorem B647875 : Blo 646304 647875 := bstep (se 1 (by rfl) ⟨485906, by rfl⟩ : syracuseStep 647875 = 971813) B971813
theorem B2187971 : Blo 646304 2187971 := bstep (se 1 (by rfl) ⟨1640978, by rfl⟩ : syracuseStep 2187971 = 3281957) B3281957
theorem B15819461 : Blo 646304 15819461 := bstep (se 4 (by rfl) ⟨1483074, by rfl⟩ : syracuseStep 15819461 = 2966149) B2966149
theorem B647891 : Blo 646304 647891 := bstep (se 1 (by rfl) ⟨485918, by rfl⟩ : syracuseStep 647891 = 971837) B971837
theorem B647907 : Blo 646304 647907 := bstep (se 1 (by rfl) ⟨485930, by rfl⟩ : syracuseStep 647907 = 971861) B971861
theorem B647923 : Blo 646304 647923 := bstep (se 1 (by rfl) ⟨485942, by rfl⟩ : syracuseStep 647923 = 971885) B971885
theorem B647939 : Blo 646304 647939 := bstep (se 1 (by rfl) ⟨485954, by rfl⟩ : syracuseStep 647939 = 971909) B971909
theorem B647955 : Blo 646304 647955 := bstep (se 1 (by rfl) ⟨485966, by rfl⟩ : syracuseStep 647955 = 971933) B971933
theorem B647971 : Blo 646304 647971 := bstep (se 1 (by rfl) ⟨485978, by rfl⟩ : syracuseStep 647971 = 971957) B971957
theorem B647987 : Blo 646304 647987 := bstep (se 1 (by rfl) ⟨485990, by rfl⟩ : syracuseStep 647987 = 971981) B971981
theorem B648003 : Blo 646304 648003 := bstep (se 1 (by rfl) ⟨486002, by rfl⟩ : syracuseStep 648003 = 972005) B972005
theorem B648019 : Blo 646304 648019 := bstep (se 1 (by rfl) ⟨486014, by rfl⟩ : syracuseStep 648019 = 972029) B972029
theorem B648035 : Blo 646304 648035 := bstep (se 1 (by rfl) ⟨486026, by rfl⟩ : syracuseStep 648035 = 972053) B972053
theorem B1041265 : Blo 646304 1041265 := bstep (se 2 (by rfl) ⟨390474, by rfl⟩ : syracuseStep 1041265 = 780949) B780949
theorem B648051 : Blo 646304 648051 := bstep (se 1 (by rfl) ⟨486038, by rfl⟩ : syracuseStep 648051 = 972077) B972077
theorem B648067 : Blo 646304 648067 := bstep (se 1 (by rfl) ⟨486050, by rfl⟩ : syracuseStep 648067 = 972101) B972101
theorem B1106833 : Blo 646304 1106833 := bstep (se 2 (by rfl) ⟨415062, by rfl⟩ : syracuseStep 1106833 = 830125) B830125
theorem B648083 : Blo 646304 648083 := bstep (se 1 (by rfl) ⟨486062, by rfl⟩ : syracuseStep 648083 = 972125) B972125
theorem B648099 : Blo 646304 648099 := bstep (se 1 (by rfl) ⟨486074, by rfl⟩ : syracuseStep 648099 = 972149) B972149
theorem B1041329 : Blo 646304 1041329 := bstep (se 2 (by rfl) ⟨390498, by rfl⟩ : syracuseStep 1041329 = 780997) B780997
theorem B648115 : Blo 646304 648115 := bstep (se 1 (by rfl) ⟨486086, by rfl⟩ : syracuseStep 648115 = 972173) B972173
theorem B648131 : Blo 646304 648131 := bstep (se 1 (by rfl) ⟨486098, by rfl⟩ : syracuseStep 648131 = 972197) B972197
theorem B2188241 : Blo 646304 2188241 := bstep (se 2 (by rfl) ⟨820590, by rfl⟩ : syracuseStep 2188241 = 1641181) B1641181
theorem B648147 : Blo 646304 648147 := bstep (se 1 (by rfl) ⟨486110, by rfl⟩ : syracuseStep 648147 = 972221) B972221
theorem B648163 : Blo 646304 648163 := bstep (se 1 (by rfl) ⟨486122, by rfl⟩ : syracuseStep 648163 = 972245) B972245
theorem B648179 : Blo 646304 648179 := bstep (se 1 (by rfl) ⟨486134, by rfl⟩ : syracuseStep 648179 = 972269) B972269
theorem B648195 : Blo 646304 648195 := bstep (se 1 (by rfl) ⟨486146, by rfl⟩ : syracuseStep 648195 = 972293) B972293
theorem B779267 : Blo 646304 779267 := bstep (se 1 (by rfl) ⟨584450, by rfl⟩ : syracuseStep 779267 = 1168901) B1168901
theorem B648211 : Blo 646304 648211 := bstep (se 1 (by rfl) ⟨486158, by rfl⟩ : syracuseStep 648211 = 972317) B972317
theorem B648227 : Blo 646304 648227 := bstep (se 1 (by rfl) ⟨486170, by rfl⟩ : syracuseStep 648227 = 972341) B972341
theorem B3695665 : Blo 646304 3695665 := bstep (se 2 (by rfl) ⟨1385874, by rfl⟩ : syracuseStep 3695665 = 2771749) B2771749
theorem B648243 : Blo 646304 648243 := bstep (se 1 (by rfl) ⟨486182, by rfl⟩ : syracuseStep 648243 = 972365) B972365
theorem B648259 : Blo 646304 648259 := bstep (se 1 (by rfl) ⟨486194, by rfl⟩ : syracuseStep 648259 = 972389) B972389
theorem B648275 : Blo 646304 648275 := bstep (se 1 (by rfl) ⟨486206, by rfl⟩ : syracuseStep 648275 = 972413) B972413
theorem B648291 : Blo 646304 648291 := bstep (se 1 (by rfl) ⟨486218, by rfl⟩ : syracuseStep 648291 = 972437) B972437
theorem B648307 : Blo 646304 648307 := bstep (se 1 (by rfl) ⟨486230, by rfl⟩ : syracuseStep 648307 = 972461) B972461
theorem B648323 : Blo 646304 648323 := bstep (se 1 (by rfl) ⟨486242, by rfl⟩ : syracuseStep 648323 = 972485) B972485
theorem B648339 : Blo 646304 648339 := bstep (se 1 (by rfl) ⟨486254, by rfl⟩ : syracuseStep 648339 = 972509) B972509
theorem B648355 : Blo 646304 648355 := bstep (se 1 (by rfl) ⟨486266, by rfl⟩ : syracuseStep 648355 = 972533) B972533
theorem B648371 : Blo 646304 648371 := bstep (se 1 (by rfl) ⟨486278, by rfl⟩ : syracuseStep 648371 = 972557) B972557
theorem B648387 : Blo 646304 648387 := bstep (se 1 (by rfl) ⟨486290, by rfl⟩ : syracuseStep 648387 = 972581) B972581
theorem B1107155 : Blo 646304 1107155 := bstep (se 1 (by rfl) ⟨830366, by rfl⟩ : syracuseStep 1107155 = 1660733) B1660733
theorem B648403 : Blo 646304 648403 := bstep (se 1 (by rfl) ⟨486302, by rfl⟩ : syracuseStep 648403 = 972605) B972605
theorem B648419 : Blo 646304 648419 := bstep (se 1 (by rfl) ⟨486314, by rfl⟩ : syracuseStep 648419 = 972629) B972629
theorem B7496945 : Blo 646304 7496945 := bstep (se 2 (by rfl) ⟨2811354, by rfl⟩ : syracuseStep 7496945 = 5622709) B5622709
theorem B648435 : Blo 646304 648435 := bstep (se 1 (by rfl) ⟨486326, by rfl⟩ : syracuseStep 648435 = 972653) B972653
theorem B648451 : Blo 646304 648451 := bstep (se 1 (by rfl) ⟨486338, by rfl⟩ : syracuseStep 648451 = 972677) B972677
theorem B648467 : Blo 646304 648467 := bstep (se 1 (by rfl) ⟨486350, by rfl⟩ : syracuseStep 648467 = 972701) B972701
theorem B648483 : Blo 646304 648483 := bstep (se 1 (by rfl) ⟨486362, by rfl⟩ : syracuseStep 648483 = 972725) B972725
theorem B2221357 : Blo 646304 2221357 := bstep (se 3 (by rfl) ⟨416504, by rfl⟩ : syracuseStep 2221357 = 833009) B833009
theorem B648499 : Blo 646304 648499 := bstep (se 1 (by rfl) ⟨486374, by rfl⟩ : syracuseStep 648499 = 972749) B972749
theorem B648515 : Blo 646304 648515 := bstep (se 1 (by rfl) ⟨486386, by rfl⟩ : syracuseStep 648515 = 972773) B972773
theorem B648531 : Blo 646304 648531 := bstep (se 1 (by rfl) ⟨486398, by rfl⟩ : syracuseStep 648531 = 972797) B972797
theorem B779603 : Blo 646304 779603 := bstep (se 1 (by rfl) ⟨584702, by rfl⟩ : syracuseStep 779603 = 1169405) B1169405
theorem B648547 : Blo 646304 648547 := bstep (se 1 (by rfl) ⟨486410, by rfl⟩ : syracuseStep 648547 = 972821) B972821
theorem B648563 : Blo 646304 648563 := bstep (se 1 (by rfl) ⟨486422, by rfl⟩ : syracuseStep 648563 = 972845) B972845
theorem B648579 : Blo 646304 648579 := bstep (se 1 (by rfl) ⟨486434, by rfl⟩ : syracuseStep 648579 = 972869) B972869
theorem B648595 : Blo 646304 648595 := bstep (se 1 (by rfl) ⟨486446, by rfl⟩ : syracuseStep 648595 = 972893) B972893
theorem B648611 : Blo 646304 648611 := bstep (se 1 (by rfl) ⟨486458, by rfl⟩ : syracuseStep 648611 = 972917) B972917
theorem B648627 : Blo 646304 648627 := bstep (se 1 (by rfl) ⟨486470, by rfl⟩ : syracuseStep 648627 = 972941) B972941
theorem B648643 : Blo 646304 648643 := bstep (se 1 (by rfl) ⟨486482, by rfl⟩ : syracuseStep 648643 = 972965) B972965
theorem B648659 : Blo 646304 648659 := bstep (se 1 (by rfl) ⟨486494, by rfl⟩ : syracuseStep 648659 = 972989) B972989
theorem B648675 : Blo 646304 648675 := bstep (se 1 (by rfl) ⟨486506, by rfl⟩ : syracuseStep 648675 = 973013) B973013
theorem B2188781 : Blo 646304 2188781 := bstep (se 3 (by rfl) ⟨410396, by rfl⟩ : syracuseStep 2188781 = 820793) B820793
theorem B648691 : Blo 646304 648691 := bstep (se 1 (by rfl) ⟨486518, by rfl⟩ : syracuseStep 648691 = 973037) B973037
theorem B648707 : Blo 646304 648707 := bstep (se 1 (by rfl) ⟨486530, by rfl⟩ : syracuseStep 648707 = 973061) B973061
theorem B648723 : Blo 646304 648723 := bstep (se 1 (by rfl) ⟨486542, by rfl⟩ : syracuseStep 648723 = 973085) B973085
theorem B2188835 : Blo 646304 2188835 := bstep (se 1 (by rfl) ⟨1641626, by rfl⟩ : syracuseStep 2188835 = 3283253) B3283253
theorem B648739 : Blo 646304 648739 := bstep (se 1 (by rfl) ⟨486554, by rfl⟩ : syracuseStep 648739 = 973109) B973109
theorem B648755 : Blo 646304 648755 := bstep (se 1 (by rfl) ⟨486566, by rfl⟩ : syracuseStep 648755 = 973133) B973133
theorem B648771 : Blo 646304 648771 := bstep (se 1 (by rfl) ⟨486578, by rfl⟩ : syracuseStep 648771 = 973157) B973157
theorem B648787 : Blo 646304 648787 := bstep (se 1 (by rfl) ⟨486590, by rfl⟩ : syracuseStep 648787 = 973181) B973181
theorem B648803 : Blo 646304 648803 := bstep (se 1 (by rfl) ⟨486602, by rfl⟩ : syracuseStep 648803 = 973205) B973205
theorem B648819 : Blo 646304 648819 := bstep (se 1 (by rfl) ⟨486614, by rfl⟩ : syracuseStep 648819 = 973229) B973229
theorem B648835 : Blo 646304 648835 := bstep (se 1 (by rfl) ⟨486626, by rfl⟩ : syracuseStep 648835 = 973253) B973253
theorem B648851 : Blo 646304 648851 := bstep (se 1 (by rfl) ⟨486638, by rfl⟩ : syracuseStep 648851 = 973277) B973277
theorem B648867 : Blo 646304 648867 := bstep (se 1 (by rfl) ⟨486650, by rfl⟩ : syracuseStep 648867 = 973301) B973301
theorem B648883 : Blo 646304 648883 := bstep (se 1 (by rfl) ⟨486662, by rfl⟩ : syracuseStep 648883 = 973325) B973325
theorem B648899 : Blo 646304 648899 := bstep (se 1 (by rfl) ⟨486674, by rfl⟩ : syracuseStep 648899 = 973349) B973349
theorem B648915 : Blo 646304 648915 := bstep (se 1 (by rfl) ⟨486686, by rfl⟩ : syracuseStep 648915 = 973373) B973373
theorem B648931 : Blo 646304 648931 := bstep (se 1 (by rfl) ⟨486698, by rfl⟩ : syracuseStep 648931 = 973397) B973397
theorem B648947 : Blo 646304 648947 := bstep (se 1 (by rfl) ⟨486710, by rfl⟩ : syracuseStep 648947 = 973421) B973421
theorem B648963 : Blo 646304 648963 := bstep (se 1 (by rfl) ⟨486722, by rfl⟩ : syracuseStep 648963 = 973445) B973445
theorem B648979 : Blo 646304 648979 := bstep (se 1 (by rfl) ⟨486734, by rfl⟩ : syracuseStep 648979 = 973469) B973469
theorem B648995 : Blo 646304 648995 := bstep (se 1 (by rfl) ⟨486746, by rfl⟩ : syracuseStep 648995 = 973493) B973493
theorem B2189105 : Blo 646304 2189105 := bstep (se 2 (by rfl) ⟨820914, by rfl⟩ : syracuseStep 2189105 = 1641829) B1641829
theorem B649011 : Blo 646304 649011 := bstep (se 1 (by rfl) ⟨486758, by rfl⟩ : syracuseStep 649011 = 973517) B973517
theorem B649027 : Blo 646304 649027 := bstep (se 1 (by rfl) ⟨486770, by rfl⟩ : syracuseStep 649027 = 973541) B973541
theorem B1402705 : Blo 646304 1402705 := bstep (se 2 (by rfl) ⟨526014, by rfl⟩ : syracuseStep 1402705 = 1052029) B1052029
theorem B649043 : Blo 646304 649043 := bstep (se 1 (by rfl) ⟨486782, by rfl⟩ : syracuseStep 649043 = 973565) B973565
theorem B649059 : Blo 646304 649059 := bstep (se 1 (by rfl) ⟨486794, by rfl⟩ : syracuseStep 649059 = 973589) B973589
theorem B649075 : Blo 646304 649075 := bstep (se 1 (by rfl) ⟨486806, by rfl⟩ : syracuseStep 649075 = 973613) B973613
theorem B649091 : Blo 646304 649091 := bstep (se 1 (by rfl) ⟨486818, by rfl⟩ : syracuseStep 649091 = 973637) B973637
theorem B649107 : Blo 646304 649107 := bstep (se 1 (by rfl) ⟨486830, by rfl⟩ : syracuseStep 649107 = 973661) B973661
theorem B649123 : Blo 646304 649123 := bstep (se 1 (by rfl) ⟨486842, by rfl⟩ : syracuseStep 649123 = 973685) B973685
theorem B649139 : Blo 646304 649139 := bstep (se 1 (by rfl) ⟨486854, by rfl⟩ : syracuseStep 649139 = 973709) B973709
theorem B7399349 : Blo 646304 7399349 := bstep (se 5 (by rfl) ⟨346844, by rfl⟩ : syracuseStep 7399349 = 693689) B693689
theorem B649155 : Blo 646304 649155 := bstep (se 1 (by rfl) ⟨486866, by rfl⟩ : syracuseStep 649155 = 973733) B973733
theorem B649171 : Blo 646304 649171 := bstep (se 1 (by rfl) ⟨486878, by rfl⟩ : syracuseStep 649171 = 973757) B973757
theorem B649187 : Blo 646304 649187 := bstep (se 1 (by rfl) ⟨486890, by rfl⟩ : syracuseStep 649187 = 973781) B973781
theorem B649203 : Blo 646304 649203 := bstep (se 1 (by rfl) ⟨486902, by rfl⟩ : syracuseStep 649203 = 973805) B973805
theorem B649219 : Blo 646304 649219 := bstep (se 1 (by rfl) ⟨486914, by rfl⟩ : syracuseStep 649219 = 973829) B973829
theorem B649235 : Blo 646304 649235 := bstep (se 1 (by rfl) ⟨486926, by rfl⟩ : syracuseStep 649235 = 973853) B973853
theorem B649251 : Blo 646304 649251 := bstep (se 1 (by rfl) ⟨486938, by rfl⟩ : syracuseStep 649251 = 973877) B973877
theorem B649267 : Blo 646304 649267 := bstep (se 1 (by rfl) ⟨486950, by rfl⟩ : syracuseStep 649267 = 973901) B973901
theorem B649283 : Blo 646304 649283 := bstep (se 1 (by rfl) ⟨486962, by rfl⟩ : syracuseStep 649283 = 973925) B973925
theorem B649299 : Blo 646304 649299 := bstep (se 1 (by rfl) ⟨486974, by rfl⟩ : syracuseStep 649299 = 973949) B973949
theorem B649315 : Blo 646304 649315 := bstep (se 1 (by rfl) ⟨486986, by rfl⟩ : syracuseStep 649315 = 973973) B973973
theorem B649331 : Blo 646304 649331 := bstep (se 1 (by rfl) ⟨486998, by rfl⟩ : syracuseStep 649331 = 973997) B973997
theorem B649347 : Blo 646304 649347 := bstep (se 1 (by rfl) ⟨487010, by rfl⟩ : syracuseStep 649347 = 974021) B974021
theorem B649363 : Blo 646304 649363 := bstep (se 1 (by rfl) ⟨487022, by rfl⟩ : syracuseStep 649363 = 974045) B974045
theorem B649379 : Blo 646304 649379 := bstep (se 1 (by rfl) ⟨487034, by rfl⟩ : syracuseStep 649379 = 974069) B974069
theorem B3106993 : Blo 646304 3106993 := bstep (se 2 (by rfl) ⟨1165122, by rfl⟩ : syracuseStep 3106993 = 2330245) B2330245
theorem B649395 : Blo 646304 649395 := bstep (se 1 (by rfl) ⟨487046, by rfl⟩ : syracuseStep 649395 = 974093) B974093
theorem B649411 : Blo 646304 649411 := bstep (se 1 (by rfl) ⟨487058, by rfl⟩ : syracuseStep 649411 = 974117) B974117
theorem B649427 : Blo 646304 649427 := bstep (se 1 (by rfl) ⟨487070, by rfl⟩ : syracuseStep 649427 = 974141) B974141
theorem B1796323 : Blo 646304 1796323 := bstep (se 1 (by rfl) ⟨1347242, by rfl⟩ : syracuseStep 1796323 = 2694485) B2694485
theorem B649443 : Blo 646304 649443 := bstep (se 1 (by rfl) ⟨487082, by rfl⟩ : syracuseStep 649443 = 974165) B974165
theorem B649459 : Blo 646304 649459 := bstep (se 1 (by rfl) ⟨487094, by rfl⟩ : syracuseStep 649459 = 974189) B974189
theorem B649475 : Blo 646304 649475 := bstep (se 1 (by rfl) ⟨487106, by rfl⟩ : syracuseStep 649475 = 974213) B974213
theorem B649491 : Blo 646304 649491 := bstep (se 1 (by rfl) ⟨487118, by rfl⟩ : syracuseStep 649491 = 974237) B974237
theorem B649507 : Blo 646304 649507 := bstep (se 1 (by rfl) ⟨487130, by rfl⟩ : syracuseStep 649507 = 974261) B974261
theorem B649523 : Blo 646304 649523 := bstep (se 1 (by rfl) ⟨487142, by rfl⟩ : syracuseStep 649523 = 974285) B974285
theorem B649539 : Blo 646304 649539 := bstep (se 1 (by rfl) ⟨487154, by rfl⟩ : syracuseStep 649539 = 974309) B974309
theorem B2189645 : Blo 646304 2189645 := bstep (se 3 (by rfl) ⟨410558, by rfl⟩ : syracuseStep 2189645 = 821117) B821117
theorem B649555 : Blo 646304 649555 := bstep (se 1 (by rfl) ⟨487166, by rfl⟩ : syracuseStep 649555 = 974333) B974333
theorem B649571 : Blo 646304 649571 := bstep (se 1 (by rfl) ⟨487178, by rfl⟩ : syracuseStep 649571 = 974357) B974357
theorem B649587 : Blo 646304 649587 := bstep (se 1 (by rfl) ⟨487190, by rfl⟩ : syracuseStep 649587 = 974381) B974381
theorem B2189699 : Blo 646304 2189699 := bstep (se 1 (by rfl) ⟨1642274, by rfl⟩ : syracuseStep 2189699 = 3284549) B3284549
theorem B649603 : Blo 646304 649603 := bstep (se 1 (by rfl) ⟨487202, by rfl⟩ : syracuseStep 649603 = 974405) B974405
theorem B649619 : Blo 646304 649619 := bstep (se 1 (by rfl) ⟨487214, by rfl⟩ : syracuseStep 649619 = 974429) B974429
theorem B649635 : Blo 646304 649635 := bstep (se 1 (by rfl) ⟨487226, by rfl⟩ : syracuseStep 649635 = 974453) B974453
theorem B649651 : Blo 646304 649651 := bstep (se 1 (by rfl) ⟨487238, by rfl⟩ : syracuseStep 649651 = 974477) B974477
theorem B649667 : Blo 646304 649667 := bstep (se 1 (by rfl) ⟨487250, by rfl⟩ : syracuseStep 649667 = 974501) B974501
theorem B649683 : Blo 646304 649683 := bstep (se 1 (by rfl) ⟨487262, by rfl⟩ : syracuseStep 649683 = 974525) B974525
theorem B3697123 : Blo 646304 3697123 := bstep (se 1 (by rfl) ⟨2772842, by rfl⟩ : syracuseStep 3697123 = 5545685) B5545685
theorem B649699 : Blo 646304 649699 := bstep (se 1 (by rfl) ⟨487274, by rfl⟩ : syracuseStep 649699 = 974549) B974549
theorem B8874481 : Blo 646304 8874481 := bstep (se 2 (by rfl) ⟨3327930, by rfl⟩ : syracuseStep 8874481 = 6655861) B6655861
theorem B649715 : Blo 646304 649715 := bstep (se 1 (by rfl) ⟨487286, by rfl⟩ : syracuseStep 649715 = 974573) B974573
theorem B649731 : Blo 646304 649731 := bstep (se 1 (by rfl) ⟨487298, by rfl⟩ : syracuseStep 649731 = 974597) B974597
theorem B649747 : Blo 646304 649747 := bstep (se 1 (by rfl) ⟨487310, by rfl⟩ : syracuseStep 649747 = 974621) B974621
theorem B649763 : Blo 646304 649763 := bstep (se 1 (by rfl) ⟨487322, by rfl⟩ : syracuseStep 649763 = 974645) B974645
theorem B649779 : Blo 646304 649779 := bstep (se 1 (by rfl) ⟨487334, by rfl⟩ : syracuseStep 649779 = 974669) B974669
theorem B649795 : Blo 646304 649795 := bstep (se 1 (by rfl) ⟨487346, by rfl⟩ : syracuseStep 649795 = 974693) B974693
theorem B649811 : Blo 646304 649811 := bstep (se 1 (by rfl) ⟨487358, by rfl⟩ : syracuseStep 649811 = 974717) B974717
theorem B649827 : Blo 646304 649827 := bstep (se 1 (by rfl) ⟨487370, by rfl⟩ : syracuseStep 649827 = 974741) B974741
theorem B649843 : Blo 646304 649843 := bstep (se 1 (by rfl) ⟨487382, by rfl⟩ : syracuseStep 649843 = 974765) B974765
theorem B649859 : Blo 646304 649859 := bstep (se 1 (by rfl) ⟨487394, by rfl⟩ : syracuseStep 649859 = 974789) B974789
theorem B2189969 : Blo 646304 2189969 := bstep (se 2 (by rfl) ⟨821238, by rfl⟩ : syracuseStep 2189969 = 1642477) B1642477
theorem B649875 : Blo 646304 649875 := bstep (se 1 (by rfl) ⟨487406, by rfl⟩ : syracuseStep 649875 = 974813) B974813
theorem B649891 : Blo 646304 649891 := bstep (se 1 (by rfl) ⟨487418, by rfl⟩ : syracuseStep 649891 = 974837) B974837
theorem B649907 : Blo 646304 649907 := bstep (se 1 (by rfl) ⟨487430, by rfl⟩ : syracuseStep 649907 = 974861) B974861
theorem B649923 : Blo 646304 649923 := bstep (se 1 (by rfl) ⟨487442, by rfl⟩ : syracuseStep 649923 = 974885) B974885
theorem B649939 : Blo 646304 649939 := bstep (se 1 (by rfl) ⟨487454, by rfl⟩ : syracuseStep 649939 = 974909) B974909
theorem B649955 : Blo 646304 649955 := bstep (se 1 (by rfl) ⟨487466, by rfl⟩ : syracuseStep 649955 = 974933) B974933
theorem B649971 : Blo 646304 649971 := bstep (se 1 (by rfl) ⟨487478, by rfl⟩ : syracuseStep 649971 = 974957) B974957
theorem B649987 : Blo 646304 649987 := bstep (se 1 (by rfl) ⟨487490, by rfl⟩ : syracuseStep 649987 = 974981) B974981
theorem B650003 : Blo 646304 650003 := bstep (se 1 (by rfl) ⟨487502, by rfl⟩ : syracuseStep 650003 = 975005) B975005
theorem B59894549 : Blo 646304 59894549 := bstep (se 6 (by rfl) ⟨1403778, by rfl⟩ : syracuseStep 59894549 = 2807557) B2807557
theorem B650019 : Blo 646304 650019 := bstep (se 1 (by rfl) ⟨487514, by rfl⟩ : syracuseStep 650019 = 975029) B975029
theorem B650035 : Blo 646304 650035 := bstep (se 1 (by rfl) ⟨487526, by rfl⟩ : syracuseStep 650035 = 975053) B975053
theorem B650051 : Blo 646304 650051 := bstep (se 1 (by rfl) ⟨487538, by rfl⟩ : syracuseStep 650051 = 975077) B975077
theorem B650067 : Blo 646304 650067 := bstep (se 1 (by rfl) ⟨487550, by rfl⟩ : syracuseStep 650067 = 975101) B975101
theorem B650083 : Blo 646304 650083 := bstep (se 1 (by rfl) ⟨487562, by rfl⟩ : syracuseStep 650083 = 975125) B975125
theorem B650099 : Blo 646304 650099 := bstep (se 1 (by rfl) ⟨487574, by rfl⟩ : syracuseStep 650099 = 975149) B975149
theorem B650115 : Blo 646304 650115 := bstep (se 1 (by rfl) ⟨487586, by rfl⟩ : syracuseStep 650115 = 975173) B975173
theorem B650131 : Blo 646304 650131 := bstep (se 1 (by rfl) ⟨487598, by rfl⟩ : syracuseStep 650131 = 975197) B975197
theorem B650147 : Blo 646304 650147 := bstep (se 1 (by rfl) ⟨487610, by rfl⟩ : syracuseStep 650147 = 975221) B975221
theorem B650163 : Blo 646304 650163 := bstep (se 1 (by rfl) ⟨487622, by rfl⟩ : syracuseStep 650163 = 975245) B975245
theorem B650179 : Blo 646304 650179 := bstep (se 1 (by rfl) ⟨487634, by rfl⟩ : syracuseStep 650179 = 975269) B975269
theorem B650195 : Blo 646304 650195 := bstep (se 1 (by rfl) ⟨487646, by rfl⟩ : syracuseStep 650195 = 975293) B975293
theorem B1403875 : Blo 646304 1403875 := bstep (se 1 (by rfl) ⟨1052906, by rfl⟩ : syracuseStep 1403875 = 2105813) B2105813
theorem B650211 : Blo 646304 650211 := bstep (se 1 (by rfl) ⟨487658, by rfl⟩ : syracuseStep 650211 = 975317) B975317
theorem B3697649 : Blo 646304 3697649 := bstep (se 2 (by rfl) ⟨1386618, by rfl⟩ : syracuseStep 3697649 = 2773237) B2773237
theorem B650227 : Blo 646304 650227 := bstep (se 1 (by rfl) ⟨487670, by rfl⟩ : syracuseStep 650227 = 975341) B975341
theorem B650243 : Blo 646304 650243 := bstep (se 1 (by rfl) ⟨487682, by rfl⟩ : syracuseStep 650243 = 975365) B975365
theorem B650259 : Blo 646304 650259 := bstep (se 1 (by rfl) ⟨487694, by rfl⟩ : syracuseStep 650259 = 975389) B975389
theorem B650275 : Blo 646304 650275 := bstep (se 1 (by rfl) ⟨487706, by rfl⟩ : syracuseStep 650275 = 975413) B975413
theorem B650291 : Blo 646304 650291 := bstep (se 1 (by rfl) ⟨487718, by rfl⟩ : syracuseStep 650291 = 975437) B975437
theorem B2190509 : Blo 646304 2190509 := bstep (se 3 (by rfl) ⟨410720, by rfl⟩ : syracuseStep 2190509 = 821441) B821441
theorem B2190563 : Blo 646304 2190563 := bstep (se 1 (by rfl) ⟨1642922, by rfl⟩ : syracuseStep 2190563 = 3285845) B3285845
theorem B1109297 : Blo 646304 1109297 := bstep (se 2 (by rfl) ⟨415986, by rfl⟩ : syracuseStep 1109297 = 831973) B831973
theorem B2223409 : Blo 646304 2223409 := bstep (se 2 (by rfl) ⟨833778, by rfl⟩ : syracuseStep 2223409 = 1667557) B1667557
theorem B2190833 : Blo 646304 2190833 := bstep (se 2 (by rfl) ⟨821562, by rfl⟩ : syracuseStep 2190833 = 1643125) B1643125
theorem B749251 : Blo 646304 749251 := bstep (se 1 (by rfl) ⟨561938, by rfl⟩ : syracuseStep 749251 = 1123877) B1123877
theorem B7499573 : Blo 646304 7499573 := bstep (se 5 (by rfl) ⟨351542, by rfl⟩ : syracuseStep 7499573 = 703085) B703085
theorem B946003 : Blo 646304 946003 := bstep (se 1 (by rfl) ⟨709502, by rfl⟩ : syracuseStep 946003 = 1419005) B1419005
theorem B1109843 : Blo 646304 1109843 := bstep (se 1 (by rfl) ⟨832382, by rfl⟩ : syracuseStep 1109843 = 1664765) B1664765
theorem B3272561 : Blo 646304 3272561 := bstep (se 2 (by rfl) ⟨1227210, by rfl⟩ : syracuseStep 3272561 = 2454421) B2454421
theorem B2191373 : Blo 646304 2191373 := bstep (se 3 (by rfl) ⟨410882, by rfl⟩ : syracuseStep 2191373 = 821765) B821765
theorem B2191427 : Blo 646304 2191427 := bstep (se 1 (by rfl) ⟨1643570, by rfl⟩ : syracuseStep 2191427 = 3287141) B3287141
theorem B28471409 : Blo 646304 28471409 := bstep (se 2 (by rfl) ⟨10676778, by rfl⟩ : syracuseStep 28471409 = 21353557) B21353557
theorem B4812941 : Blo 646304 4812941 := bstep (se 3 (by rfl) ⟨902426, by rfl⟩ : syracuseStep 4812941 = 1804853) B1804853
theorem B2191697 : Blo 646304 2191697 := bstep (se 2 (by rfl) ⟨821886, by rfl⟩ : syracuseStep 2191697 = 1643773) B1643773
theorem B3699107 : Blo 646304 3699107 := bstep (se 1 (by rfl) ⟨2774330, by rfl⟩ : syracuseStep 3699107 = 5548661) B5548661
theorem B1110611 : Blo 646304 1110611 := bstep (se 1 (by rfl) ⟨832958, by rfl⟩ : syracuseStep 1110611 = 1665917) B1665917
theorem B5534477 : Blo 646304 5534477 := bstep (se 3 (by rfl) ⟨1037714, by rfl⟩ : syracuseStep 5534477 = 2075429) B2075429
theorem B17953589 : Blo 646304 17953589 := bstep (se 5 (by rfl) ⟨841574, by rfl⟩ : syracuseStep 17953589 = 1683149) B1683149
theorem B2192237 : Blo 646304 2192237 := bstep (se 3 (by rfl) ⟨411044, by rfl⟩ : syracuseStep 2192237 = 822089) B822089
theorem B4682609 : Blo 646304 4682609 := bstep (se 2 (by rfl) ⟨1755978, by rfl⟩ : syracuseStep 4682609 = 3511957) B3511957
theorem B2192291 : Blo 646304 2192291 := bstep (se 1 (by rfl) ⟨1644218, by rfl⟩ : syracuseStep 2192291 = 3288437) B3288437
theorem B3110051 : Blo 646304 3110051 := bstep (se 1 (by rfl) ⟨2332538, by rfl⟩ : syracuseStep 3110051 = 4665077) B4665077
theorem B2192561 : Blo 646304 2192561 := bstep (se 2 (by rfl) ⟨822210, by rfl⟩ : syracuseStep 2192561 = 1644421) B1644421
theorem B3274019 : Blo 646304 3274019 := bstep (se 1 (by rfl) ⟨2455514, by rfl⟩ : syracuseStep 3274019 = 4911029) B4911029
theorem B2455181 : Blo 646304 2455181 := bstep (se 3 (by rfl) ⟨460346, by rfl⟩ : syracuseStep 2455181 = 920693) B920693
theorem B2193101 : Blo 646304 2193101 := bstep (se 3 (by rfl) ⟨411206, by rfl⟩ : syracuseStep 2193101 = 822413) B822413
theorem B2193155 : Blo 646304 2193155 := bstep (se 1 (by rfl) ⟨1644866, by rfl⟩ : syracuseStep 2193155 = 3289733) B3289733
theorem B25196309 : Blo 646304 25196309 := bstep (se 6 (by rfl) ⟨590538, by rfl⟩ : syracuseStep 25196309 = 1181077) B1181077
theorem B2193425 : Blo 646304 2193425 := bstep (se 2 (by rfl) ⟨822534, by rfl⟩ : syracuseStep 2193425 = 1645069) B1645069
theorem B3274829 : Blo 646304 3274829 := bstep (se 3 (by rfl) ⟨614030, by rfl⟩ : syracuseStep 3274829 = 1228061) B1228061
theorem B1636433 : Blo 646304 1636433 := bstep (se 2 (by rfl) ⟨613662, by rfl⟩ : syracuseStep 1636433 = 1227325) B1227325
theorem B1636483 : Blo 646304 1636483 := bstep (se 1 (by rfl) ⟨1227362, by rfl⟩ : syracuseStep 1636483 = 2454725) B2454725
theorem B3045539 : Blo 646304 3045539 := bstep (se 1 (by rfl) ⟨2284154, by rfl⟩ : syracuseStep 3045539 = 4568309) B4568309
theorem B3700997 : Blo 646304 3700997 := bstep (se 4 (by rfl) ⟨346968, by rfl⟩ : syracuseStep 3700997 = 693937) B693937
theorem B1636625 : Blo 646304 1636625 := bstep (se 2 (by rfl) ⟨613734, by rfl⟩ : syracuseStep 1636625 = 1227469) B1227469
theorem B3111281 : Blo 646304 3111281 := bstep (se 2 (by rfl) ⟨1166730, by rfl⟩ : syracuseStep 3111281 = 2333461) B2333461
theorem B2849293 : Blo 646304 2849293 := bstep (se 3 (by rfl) ⟨534242, by rfl⟩ : syracuseStep 2849293 = 1068485) B1068485
theorem B2193965 : Blo 646304 2193965 := bstep (se 3 (by rfl) ⟨411368, by rfl⟩ : syracuseStep 2193965 = 822737) B822737
theorem B2194019 : Blo 646304 2194019 := bstep (se 1 (by rfl) ⟨1645514, by rfl⟩ : syracuseStep 2194019 = 3291029) B3291029
theorem B3930929 : Blo 646304 3930929 := bstep (se 2 (by rfl) ⟨1474098, by rfl⟩ : syracuseStep 3930929 = 2948197) B2948197
theorem B2194289 : Blo 646304 2194289 := bstep (se 2 (by rfl) ⟨822858, by rfl⟩ : syracuseStep 2194289 = 1645717) B1645717
theorem B1866673 : Blo 646304 1866673 := bstep (se 2 (by rfl) ⟨700002, by rfl⟩ : syracuseStep 1866673 = 1400005) B1400005
theorem B2849869 : Blo 646304 2849869 := bstep (se 3 (by rfl) ⟨534350, by rfl⟩ : syracuseStep 2849869 = 1068701) B1068701
theorem B1637617 : Blo 646304 1637617 := bstep (se 2 (by rfl) ⟨614106, by rfl⟩ : syracuseStep 1637617 = 1228213) B1228213
theorem B4160753 : Blo 646304 4160753 := bstep (se 2 (by rfl) ⟨1560282, by rfl⟩ : syracuseStep 4160753 = 3120565) B3120565
theorem B818419 : Blo 646304 818419 := bstep (se 1 (by rfl) ⟨613814, by rfl⟩ : syracuseStep 818419 = 1227629) B1227629
theorem B818515 : Blo 646304 818515 := bstep (se 1 (by rfl) ⟨613886, by rfl⟩ : syracuseStep 818515 = 1227773) B1227773
theorem B1637891 : Blo 646304 1637891 := bstep (se 1 (by rfl) ⟨1228418, by rfl⟩ : syracuseStep 1637891 = 2456837) B2456837
theorem B1474243 : Blo 646304 1474243 := bstep (se 1 (by rfl) ⟨1105682, by rfl⟩ : syracuseStep 1474243 = 2211365) B2211365
theorem B1638083 : Blo 646304 1638083 := bstep (se 1 (by rfl) ⟨1228562, by rfl⟩ : syracuseStep 1638083 = 2457125) B2457125
theorem B4161293 : Blo 646304 4161293 := bstep (se 3 (by rfl) ⟨780242, by rfl⟩ : syracuseStep 4161293 = 1560485) B1560485
theorem B819011 : Blo 646304 819011 := bstep (se 1 (by rfl) ⟨614258, by rfl⟩ : syracuseStep 819011 = 1228517) B1228517
theorem B1867619 : Blo 646304 1867619 := bstep (se 1 (by rfl) ⟨1400714, by rfl⟩ : syracuseStep 1867619 = 2801429) B2801429
theorem B1474481 : Blo 646304 1474481 := bstep (se 2 (by rfl) ⟨552930, by rfl⟩ : syracuseStep 1474481 = 1105861) B1105861
theorem B655447 : Blo 646304 655447 := bstep (se 1 (by rfl) ⟨491585, by rfl⟩ : syracuseStep 655447 = 983171) B983171
theorem B1638731 : Blo 646304 1638731 := bstep (se 1 (by rfl) ⟨1229048, by rfl⟩ : syracuseStep 1638731 = 2458097) B2458097
theorem B819659 : Blo 646304 819659 := bstep (se 1 (by rfl) ⟨614744, by rfl⟩ : syracuseStep 819659 = 1229489) B1229489
theorem B1311347 : Blo 646304 1311347 := bstep (se 1 (by rfl) ⟨983510, by rfl⟩ : syracuseStep 1311347 = 1967021) B1967021
theorem B4915889 : Blo 646304 4915889 := bstep (se 2 (by rfl) ⟨1843458, by rfl⟩ : syracuseStep 4915889 = 3686917) B3686917
theorem B2851549 : Blo 646304 2851549 := bstep (se 3 (by rfl) ⟨534665, by rfl⟩ : syracuseStep 2851549 = 1069331) B1069331
theorem B5538577 : Blo 646304 5538577 := bstep (se 2 (by rfl) ⟨2076966, by rfl⟩ : syracuseStep 5538577 = 4153933) B4153933
theorem B1966913 : Blo 646304 1966913 := bstep (se 2 (by rfl) ⟨737592, by rfl⟩ : syracuseStep 1966913 = 1475185) B1475185
theorem B5538851 : Blo 646304 5538851 := bstep (se 1 (by rfl) ⟨4154138, by rfl⟩ : syracuseStep 5538851 = 8308277) B8308277
theorem B820363 : Blo 646304 820363 := bstep (se 1 (by rfl) ⟨615272, by rfl⟩ : syracuseStep 820363 = 1230545) B1230545
theorem B4916375 : Blo 646304 4916375 := bstep (se 1 (by rfl) ⟨3687281, by rfl⟩ : syracuseStep 4916375 = 7374563) B7374563
theorem B1475777 : Blo 646304 1475777 := bstep (se 2 (by rfl) ⟨553416, by rfl⟩ : syracuseStep 1475777 = 1106833) B1106833
theorem B1639703 : Blo 646304 1639703 := bstep (se 1 (by rfl) ⟨1229777, by rfl⟩ : syracuseStep 1639703 = 2459555) B2459555
theorem B1246603 : Blo 646304 1246603 := bstep (se 1 (by rfl) ⟨934952, by rfl⟩ : syracuseStep 1246603 = 1869905) B1869905
theorem B3278231 : Blo 646304 3278231 := bstep (se 1 (by rfl) ⟨2458673, by rfl⟩ : syracuseStep 3278231 = 4917347) B4917347
theorem B820631 : Blo 646304 820631 := bstep (se 1 (by rfl) ⟨615473, by rfl⟩ : syracuseStep 820631 = 1230947) B1230947
theorem B1476107 : Blo 646304 1476107 := bstep (se 1 (by rfl) ⟨1107080, by rfl⟩ : syracuseStep 1476107 = 2214161) B2214161
theorem B4982347 : Blo 646304 4982347 := bstep (se 1 (by rfl) ⟨3736760, by rfl⟩ : syracuseStep 4982347 = 7473521) B7473521
theorem B2459267 : Blo 646304 2459267 := bstep (se 1 (by rfl) ⟨1844450, by rfl⟩ : syracuseStep 2459267 = 3688901) B3688901
theorem B2459281 : Blo 646304 2459281 := bstep (se 2 (by rfl) ⟨922230, by rfl⟩ : syracuseStep 2459281 = 1844461) B1844461
theorem B984727 : Blo 646304 984727 := bstep (se 1 (by rfl) ⟨738545, by rfl⟩ : syracuseStep 984727 = 1477091) B1477091
theorem B1640371 : Blo 646304 1640371 := bstep (se 1 (by rfl) ⟨1230278, by rfl⟩ : syracuseStep 1640371 = 2460557) B2460557
theorem B2459585 : Blo 646304 2459585 := bstep (se 2 (by rfl) ⟨922344, by rfl⟩ : syracuseStep 2459585 = 1844689) B1844689
theorem B1640513 : Blo 646304 1640513 := bstep (se 2 (by rfl) ⟨615192, by rfl⟩ : syracuseStep 1640513 = 1230385) B1230385
theorem B821335 : Blo 646304 821335 := bstep (se 1 (by rfl) ⟨616001, by rfl⟩ : syracuseStep 821335 = 1232003) B1232003
theorem B2885905 : Blo 646304 2885905 := bstep (se 2 (by rfl) ⟨1082214, by rfl⟩ : syracuseStep 2885905 = 2164429) B2164429
theorem B1870273 : Blo 646304 1870273 := bstep (se 2 (by rfl) ⟨701352, by rfl⟩ : syracuseStep 1870273 = 1402705) B1402705
theorem B2460253 : Blo 646304 2460253 := bstep (se 3 (by rfl) ⟨461297, by rfl⟩ : syracuseStep 2460253 = 922595) B922595
theorem B985943 : Blo 646304 985943 := bstep (se 1 (by rfl) ⟨739457, by rfl⟩ : syracuseStep 985943 = 1478915) B1478915
theorem B2395097 : Blo 646304 2395097 := bstep (se 2 (by rfl) ⟨898161, by rfl⟩ : syracuseStep 2395097 = 1796323) B1796323
theorem B2362391 : Blo 646304 2362391 := bstep (se 1 (by rfl) ⟨1771793, by rfl⟩ : syracuseStep 2362391 = 3543587) B3543587
theorem B2952413 : Blo 646304 2952413 := bstep (se 3 (by rfl) ⟨553577, by rfl⟩ : syracuseStep 2952413 = 1107155) B1107155
theorem B1641779 : Blo 646304 1641779 := bstep (se 1 (by rfl) ⟨1231334, by rfl⟩ : syracuseStep 1641779 = 2462669) B2462669
theorem B11832641 : Blo 646304 11832641 := bstep (se 2 (by rfl) ⟨4437240, by rfl⟩ : syracuseStep 11832641 = 8874481) B8874481
theorem B692011 : Blo 646304 692011 := bstep (se 1 (by rfl) ⟨519008, by rfl⟩ : syracuseStep 692011 = 1038017) B1038017
theorem B1642315 : Blo 646304 1642315 := bstep (se 1 (by rfl) ⟨1231736, by rfl⟩ : syracuseStep 1642315 = 2463473) B2463473
theorem B2461529 : Blo 646304 2461529 := bstep (se 2 (by rfl) ⟨923073, by rfl⟩ : syracuseStep 2461529 = 1846147) B1846147
theorem B921547 : Blo 646304 921547 := bstep (se 1 (by rfl) ⟨691160, by rfl⟩ : syracuseStep 921547 = 1382321) B1382321
theorem B921559 : Blo 646304 921559 := bstep (se 1 (by rfl) ⟨691169, by rfl⟩ : syracuseStep 921559 = 1382339) B1382339
theorem B1871833 : Blo 646304 1871833 := bstep (se 2 (by rfl) ⟨701937, by rfl⟩ : syracuseStep 1871833 = 1403875) B1403875
theorem B1642457 : Blo 646304 1642457 := bstep (se 2 (by rfl) ⟨615921, by rfl⟩ : syracuseStep 1642457 = 1231843) B1231843
theorem B14028875 : Blo 646304 14028875 := bstep (se 1 (by rfl) ⟨10521656, by rfl⟩ : syracuseStep 14028875 = 21043313) B21043313
theorem B4166417 : Blo 646304 4166417 := bstep (se 2 (by rfl) ⟨1562406, by rfl⟩ : syracuseStep 4166417 = 3124813) B3124813
theorem B1643287 : Blo 646304 1643287 := bstep (se 1 (by rfl) ⟨1232465, by rfl⟩ : syracuseStep 1643287 = 2464931) B2464931
theorem B3281795 : Blo 646304 3281795 := bstep (se 1 (by rfl) ⟨2461346, by rfl⟩ : syracuseStep 3281795 = 4922693) B4922693
theorem B1381313 : Blo 646304 1381313 := bstep (se 2 (by rfl) ⟨517992, by rfl⟩ : syracuseStep 1381313 = 1035985) B1035985
theorem B1315777 : Blo 646304 1315777 := bstep (se 2 (by rfl) ⟨493416, by rfl⟩ : syracuseStep 1315777 = 986833) B986833
theorem B3413123 : Blo 646304 3413123 := bstep (se 1 (by rfl) ⟨2559842, by rfl⟩ : syracuseStep 3413123 = 5119685) B5119685
theorem B1643723 : Blo 646304 1643723 := bstep (se 1 (by rfl) ⟨1232792, by rfl⟩ : syracuseStep 1643723 = 2465585) B2465585
theorem B3118297 : Blo 646304 3118297 := bstep (se 2 (by rfl) ⟨1169361, by rfl⟩ : syracuseStep 3118297 = 2338723) B2338723
theorem B693527 : Blo 646304 693527 := bstep (se 1 (by rfl) ⟨520145, by rfl⟩ : syracuseStep 693527 = 1040291) B1040291
theorem B2463155 : Blo 646304 2463155 := bstep (se 1 (by rfl) ⟨1847366, by rfl⟩ : syracuseStep 2463155 = 3694733) B3694733
theorem B2627009 : Blo 646304 2627009 := bstep (se 2 (by rfl) ⟨985128, by rfl⟩ : syracuseStep 2627009 = 1970257) B1970257
theorem B2463169 : Blo 646304 2463169 := bstep (se 2 (by rfl) ⟨923688, by rfl⟩ : syracuseStep 2463169 = 1847377) B1847377
theorem B1381835 : Blo 646304 1381835 := bstep (se 1 (by rfl) ⟨1036376, by rfl⟩ : syracuseStep 1381835 = 2072753) B2072753
theorem B4658705 : Blo 646304 4658705 := bstep (se 2 (by rfl) ⟨1747014, by rfl⟩ : syracuseStep 4658705 = 3494029) B3494029
theorem B1644097 : Blo 646304 1644097 := bstep (se 2 (by rfl) ⟨616536, by rfl⟩ : syracuseStep 1644097 = 1233073) B1233073
theorem B1840715 : Blo 646304 1840715 := bstep (se 1 (by rfl) ⟨1380536, by rfl⟩ : syracuseStep 1840715 = 2761073) B2761073
theorem B3938179 : Blo 646304 3938179 := bstep (se 1 (by rfl) ⟨2953634, by rfl⟩ : syracuseStep 3938179 = 5907269) B5907269
theorem B694219 : Blo 646304 694219 := bstep (se 1 (by rfl) ⟨520664, by rfl⟩ : syracuseStep 694219 = 1041329) B1041329
theorem B923609 : Blo 646304 923609 := bstep (se 2 (by rfl) ⟨346353, by rfl⟩ : syracuseStep 923609 = 692707) B692707
theorem B727159 : Blo 646304 727159 := bstep (se 1 (by rfl) ⟨545369, by rfl⟩ : syracuseStep 727159 = 1090739) B1090739
theorem B1644695 : Blo 646304 1644695 := bstep (se 1 (by rfl) ⟨1233521, by rfl⟩ : syracuseStep 1644695 = 2467043) B2467043
theorem B727339 : Blo 646304 727339 := bstep (se 1 (by rfl) ⟨545504, by rfl⟩ : syracuseStep 727339 = 1091009) B1091009
theorem B727447 : Blo 646304 727447 := bstep (se 1 (by rfl) ⟨545585, by rfl⟩ : syracuseStep 727447 = 1091171) B1091171
theorem B727627 : Blo 646304 727627 := bstep (se 1 (by rfl) ⟨545720, by rfl⟩ : syracuseStep 727627 = 1091441) B1091441
theorem B924247 : Blo 646304 924247 := bstep (se 1 (by rfl) ⟨693185, by rfl⟩ : syracuseStep 924247 = 1386371) B1386371
theorem B1383065 : Blo 646304 1383065 := bstep (se 2 (by rfl) ⟨518649, by rfl⟩ : syracuseStep 1383065 = 1037299) B1037299
theorem B727735 : Blo 646304 727735 := bstep (se 1 (by rfl) ⟨545801, by rfl⟩ : syracuseStep 727735 = 1091603) B1091603
theorem B727915 : Blo 646304 727915 := bstep (se 1 (by rfl) ⟨545936, by rfl⟩ : syracuseStep 727915 = 1091873) B1091873
theorem B1645505 : Blo 646304 1645505 := bstep (se 2 (by rfl) ⟨617064, by rfl⟩ : syracuseStep 1645505 = 1234129) B1234129
theorem B728023 : Blo 646304 728023 := bstep (se 1 (by rfl) ⟨546017, by rfl⟩ : syracuseStep 728023 = 1092035) B1092035
theorem B1383475 : Blo 646304 1383475 := bstep (se 1 (by rfl) ⟨1037606, by rfl⟩ : syracuseStep 1383475 = 2075213) B2075213
theorem B728203 : Blo 646304 728203 := bstep (se 1 (by rfl) ⟨546152, by rfl⟩ : syracuseStep 728203 = 1092305) B1092305
theorem B728311 : Blo 646304 728311 := bstep (se 1 (by rfl) ⟨546233, by rfl⟩ : syracuseStep 728311 = 1092467) B1092467
theorem B2465099 : Blo 646304 2465099 := bstep (se 1 (by rfl) ⟨1848824, by rfl⟩ : syracuseStep 2465099 = 3697649) B3697649
theorem B2465113 : Blo 646304 2465113 := bstep (se 2 (by rfl) ⟨924417, by rfl⟩ : syracuseStep 2465113 = 1848835) B1848835
theorem B925067 : Blo 646304 925067 := bstep (se 1 (by rfl) ⟨693800, by rfl⟩ : syracuseStep 925067 = 1387601) B1387601
theorem B728491 : Blo 646304 728491 := bstep (se 1 (by rfl) ⟨546368, by rfl⟩ : syracuseStep 728491 = 1092737) B1092737
theorem B1646041 : Blo 646304 1646041 := bstep (se 2 (by rfl) ⟨617265, by rfl⟩ : syracuseStep 1646041 = 1234531) B1234531
theorem B5250577 : Blo 646304 5250577 := bstep (se 2 (by rfl) ⟨1968966, by rfl⟩ : syracuseStep 5250577 = 3937933) B3937933
theorem B728599 : Blo 646304 728599 := bstep (se 1 (by rfl) ⟨546449, by rfl⟩ : syracuseStep 728599 = 1092899) B1092899
theorem B1383961 : Blo 646304 1383961 := bstep (se 2 (by rfl) ⟨518985, by rfl⟩ : syracuseStep 1383961 = 1037971) B1037971
theorem B728779 : Blo 646304 728779 := bstep (se 1 (by rfl) ⟨546584, by rfl⟩ : syracuseStep 728779 = 1093169) B1093169
theorem B728887 : Blo 646304 728887 := bstep (se 1 (by rfl) ⟨546665, by rfl⟩ : syracuseStep 728887 = 1093331) B1093331
theorem B1187713 : Blo 646304 1187713 := bstep (se 2 (by rfl) ⟨445392, by rfl⟩ : syracuseStep 1187713 = 890785) B890785
theorem B729067 : Blo 646304 729067 := bstep (se 1 (by rfl) ⟨546800, by rfl⟩ : syracuseStep 729067 = 1093601) B1093601
theorem B18980939 : Blo 646304 18980939 := bstep (se 1 (by rfl) ⟨14235704, by rfl⟩ : syracuseStep 18980939 = 28471409) B28471409
theorem B729175 : Blo 646304 729175 := bstep (se 1 (by rfl) ⟨546881, by rfl⟩ : syracuseStep 729175 = 1093763) B1093763
theorem B1384705 : Blo 646304 1384705 := bstep (se 2 (by rfl) ⟨519264, by rfl⟩ : syracuseStep 1384705 = 1038529) B1038529
theorem B729355 : Blo 646304 729355 := bstep (se 1 (by rfl) ⟨547016, by rfl⟩ : syracuseStep 729355 = 1094033) B1094033
theorem B4923665 : Blo 646304 4923665 := bstep (se 2 (by rfl) ⟨1846374, by rfl⟩ : syracuseStep 4923665 = 3692749) B3692749
theorem B2466071 : Blo 646304 2466071 := bstep (se 1 (by rfl) ⟨1849553, by rfl⟩ : syracuseStep 2466071 = 3699107) B3699107
theorem B729463 : Blo 646304 729463 := bstep (se 1 (by rfl) ⟨547097, by rfl⟩ : syracuseStep 729463 = 1094195) B1094195
theorem B2335193 : Blo 646304 2335193 := bstep (se 2 (by rfl) ⟨875697, by rfl⟩ : syracuseStep 2335193 = 1751395) B1751395
theorem B3285521 : Blo 646304 3285521 := bstep (se 2 (by rfl) ⟨1232070, by rfl⟩ : syracuseStep 3285521 = 2464141) B2464141
theorem B11969059 : Blo 646304 11969059 := bstep (se 1 (by rfl) ⟨8976794, by rfl⟩ : syracuseStep 11969059 = 17953589) B17953589
theorem B729643 : Blo 646304 729643 := bstep (se 1 (by rfl) ⟨547232, by rfl⟩ : syracuseStep 729643 = 1094465) B1094465
theorem B3121739 : Blo 646304 3121739 := bstep (se 1 (by rfl) ⟨2341304, by rfl⟩ : syracuseStep 3121739 = 4682609) B4682609
theorem B2761361 : Blo 646304 2761361 := bstep (se 2 (by rfl) ⟨1035510, by rfl⟩ : syracuseStep 2761361 = 2071021) B2071021
theorem B729751 : Blo 646304 729751 := bstep (se 1 (by rfl) ⟨547313, by rfl⟩ : syracuseStep 729751 = 1094627) B1094627
theorem B3285683 : Blo 646304 3285683 := bstep (se 1 (by rfl) ⟨2464262, by rfl⟩ : syracuseStep 3285683 = 4928525) B4928525
theorem B17703629 : Blo 646304 17703629 := bstep (se 3 (by rfl) ⟨3319430, by rfl⟩ : syracuseStep 17703629 = 6638861) B6638861
theorem B2073367 : Blo 646304 2073367 := bstep (se 1 (by rfl) ⟨1555025, by rfl⟩ : syracuseStep 2073367 = 3110051) B3110051
theorem B729931 : Blo 646304 729931 := bstep (se 1 (by rfl) ⟨547448, by rfl⟩ : syracuseStep 729931 = 1094897) B1094897
theorem B730039 : Blo 646304 730039 := bstep (se 1 (by rfl) ⟨547529, by rfl⟩ : syracuseStep 730039 = 1095059) B1095059
theorem B730219 : Blo 646304 730219 := bstep (se 1 (by rfl) ⟨547664, by rfl⟩ : syracuseStep 730219 = 1095329) B1095329
theorem B3155075 : Blo 646304 3155075 := bstep (se 1 (by rfl) ⟨2366306, by rfl⟩ : syracuseStep 3155075 = 4732613) B4732613
theorem B1385687 : Blo 646304 1385687 := bstep (se 1 (by rfl) ⟨1039265, by rfl⟩ : syracuseStep 1385687 = 2078531) B2078531
theorem B730327 : Blo 646304 730327 := bstep (se 1 (by rfl) ⟨547745, by rfl⟩ : syracuseStep 730327 = 1095491) B1095491
theorem B7120133 : Blo 646304 7120133 := bstep (se 4 (by rfl) ⟨667512, by rfl⟩ : syracuseStep 7120133 = 1335025) B1335025
theorem B1090955 : Blo 646304 1090955 := bstep (se 1 (by rfl) ⟨818216, by rfl⟩ : syracuseStep 1090955 = 1636433) B1636433
theorem B730507 : Blo 646304 730507 := bstep (se 1 (by rfl) ⟨547880, by rfl⟩ : syracuseStep 730507 = 1095761) B1095761
theorem B730615 : Blo 646304 730615 := bstep (se 1 (by rfl) ⟨547961, by rfl⟩ : syracuseStep 730615 = 1095923) B1095923
theorem B2467331 : Blo 646304 2467331 := bstep (se 1 (by rfl) ⟨1850498, by rfl⟩ : syracuseStep 2467331 = 3700997) B3700997
theorem B1091083 : Blo 646304 1091083 := bstep (se 1 (by rfl) ⟨818312, by rfl⟩ : syracuseStep 1091083 = 1636625) B1636625
theorem B2074187 : Blo 646304 2074187 := bstep (se 1 (by rfl) ⟨1555640, by rfl⟩ : syracuseStep 2074187 = 3111281) B3111281
theorem B2631257 : Blo 646304 2631257 := bstep (se 2 (by rfl) ⟨986721, by rfl⟩ : syracuseStep 2631257 = 1973443) B1973443
theorem B1091225 : Blo 646304 1091225 := bstep (se 2 (by rfl) ⟨409209, by rfl⟩ : syracuseStep 1091225 = 818419) B818419
theorem B730795 : Blo 646304 730795 := bstep (se 1 (by rfl) ⟨548096, by rfl⟩ : syracuseStep 730795 = 1096193) B1096193
theorem B2631371 : Blo 646304 2631371 := bstep (se 1 (by rfl) ⟨1973528, by rfl⟩ : syracuseStep 2631371 = 3947057) B3947057
theorem B1386251 : Blo 646304 1386251 := bstep (se 1 (by rfl) ⟨1039688, by rfl⟩ : syracuseStep 1386251 = 2079377) B2079377
theorem B730903 : Blo 646304 730903 := bstep (se 1 (by rfl) ⟨548177, by rfl⟩ : syracuseStep 730903 = 1096355) B1096355
theorem B1091353 : Blo 646304 1091353 := bstep (se 2 (by rfl) ⟨409257, by rfl⟩ : syracuseStep 1091353 = 818515) B818515
theorem B731083 : Blo 646304 731083 := bstep (se 1 (by rfl) ⟨548312, by rfl⟩ : syracuseStep 731083 = 1096625) B1096625
theorem B731191 : Blo 646304 731191 := bstep (se 1 (by rfl) ⟨548393, by rfl⟩ : syracuseStep 731191 = 1096787) B1096787
theorem B85403717 : Blo 646304 85403717 := bstep (se 4 (by rfl) ⟨8006598, by rfl⟩ : syracuseStep 85403717 = 16013197) B16013197
theorem B1976413 : Blo 646304 1976413 := bstep (se 3 (by rfl) ⟨370577, by rfl⟩ : syracuseStep 1976413 = 741155) B741155
theorem B2074841 : Blo 646304 2074841 := bstep (se 2 (by rfl) ⟨778065, by rfl⟩ : syracuseStep 2074841 = 1556131) B1556131
theorem B1386713 : Blo 646304 1386713 := bstep (se 2 (by rfl) ⟨520017, by rfl⟩ : syracuseStep 1386713 = 1040035) B1040035
theorem B731371 : Blo 646304 731371 := bstep (se 1 (by rfl) ⟨548528, by rfl⟩ : syracuseStep 731371 = 1097057) B1097057
theorem B1091927 : Blo 646304 1091927 := bstep (se 1 (by rfl) ⟨818945, by rfl⟩ : syracuseStep 1091927 = 1637891) B1637891
theorem B731479 : Blo 646304 731479 := bstep (se 1 (by rfl) ⟨548609, by rfl⟩ : syracuseStep 731479 = 1097219) B1097219
theorem B1092055 : Blo 646304 1092055 := bstep (se 1 (by rfl) ⟨819041, by rfl⟩ : syracuseStep 1092055 = 1638083) B1638083
theorem B3287627 : Blo 646304 3287627 := bstep (se 1 (by rfl) ⟨2465720, by rfl⟩ : syracuseStep 3287627 = 4931441) B4931441
theorem B2337425 : Blo 646304 2337425 := bstep (se 2 (by rfl) ⟨876534, by rfl⟩ : syracuseStep 2337425 = 1753069) B1753069
theorem B1846091 : Blo 646304 1846091 := bstep (se 1 (by rfl) ⟨1384568, by rfl⟩ : syracuseStep 1846091 = 2769137) B2769137
theorem B2763821 : Blo 646304 2763821 := bstep (se 3 (by rfl) ⟨518216, by rfl⟩ : syracuseStep 2763821 = 1036433) B1036433
theorem B1092683 : Blo 646304 1092683 := bstep (se 1 (by rfl) ⟨819512, by rfl⟩ : syracuseStep 1092683 = 1639025) B1639025
theorem B1092811 : Blo 646304 1092811 := bstep (se 1 (by rfl) ⟨819608, by rfl⟩ : syracuseStep 1092811 = 1639217) B1639217
theorem B1846489 : Blo 646304 1846489 := bstep (se 2 (by rfl) ⟨692433, by rfl⟩ : syracuseStep 1846489 = 1384867) B1384867
theorem B2075969 : Blo 646304 2075969 := bstep (se 2 (by rfl) ⟨778488, by rfl⟩ : syracuseStep 2075969 = 1556977) B1556977
theorem B3681611 : Blo 646304 3681611 := bstep (se 1 (by rfl) ⟨2761208, by rfl⟩ : syracuseStep 3681611 = 5522417) B5522417
theorem B1092953 : Blo 646304 1092953 := bstep (se 2 (by rfl) ⟨409857, by rfl⟩ : syracuseStep 1092953 = 819715) B819715
theorem B1387891 : Blo 646304 1387891 := bstep (se 1 (by rfl) ⟨1040918, by rfl⟩ : syracuseStep 1387891 = 2081837) B2081837
theorem B1093081 : Blo 646304 1093081 := bstep (se 2 (by rfl) ⟨409905, by rfl⟩ : syracuseStep 1093081 = 819811) B819811
theorem B2338307 : Blo 646304 2338307 := bstep (se 1 (by rfl) ⟨1753730, by rfl⟩ : syracuseStep 2338307 = 3507461) B3507461
theorem B2502323 : Blo 646304 2502323 := bstep (se 1 (by rfl) ⟨1876742, by rfl⟩ : syracuseStep 2502323 = 3753485) B3753485
theorem B2764505 : Blo 646304 2764505 := bstep (se 2 (by rfl) ⟨1036689, by rfl⟩ : syracuseStep 2764505 = 2073379) B2073379
theorem B1388353 : Blo 646304 1388353 := bstep (se 2 (by rfl) ⟨520632, by rfl⟩ : syracuseStep 1388353 = 1041265) B1041265
theorem B7909337 : Blo 646304 7909337 := bstep (se 2 (by rfl) ⟨2966001, by rfl⟩ : syracuseStep 7909337 = 5932003) B5932003
theorem B1093655 : Blo 646304 1093655 := bstep (se 1 (by rfl) ⟨820241, by rfl⟩ : syracuseStep 1093655 = 1640483) B1640483
theorem B4927553 : Blo 646304 4927553 := bstep (se 2 (by rfl) ⟨1847832, by rfl⟩ : syracuseStep 4927553 = 3695665) B3695665
theorem B1454219 : Blo 646304 1454219 := bstep (se 1 (by rfl) ⟨1090664, by rfl⟩ : syracuseStep 1454219 = 2181329) B2181329
theorem B1093783 : Blo 646304 1093783 := bstep (se 1 (by rfl) ⟨820337, by rfl⟩ : syracuseStep 1093783 = 1640675) B1640675
theorem B1454273 : Blo 646304 1454273 := bstep (se 2 (by rfl) ⟨545352, by rfl⟩ : syracuseStep 1454273 = 1090705) B1090705
theorem B3289409 : Blo 646304 3289409 := bstep (se 2 (by rfl) ⟨1233528, by rfl⟩ : syracuseStep 3289409 = 2467057) B2467057
theorem B2961809 : Blo 646304 2961809 := bstep (se 2 (by rfl) ⟨1110678, by rfl⟩ : syracuseStep 2961809 = 2221357) B2221357
theorem B1454489 : Blo 646304 1454489 := bstep (se 2 (by rfl) ⟨545433, by rfl⟩ : syracuseStep 1454489 = 1090867) B1090867
theorem B1847731 : Blo 646304 1847731 := bstep (se 1 (by rfl) ⟨1385798, by rfl⟩ : syracuseStep 1847731 = 2771597) B2771597
theorem B1454579 : Blo 646304 1454579 := bstep (se 1 (by rfl) ⟨1090934, by rfl⟩ : syracuseStep 1454579 = 2181869) B2181869
theorem B1454615 : Blo 646304 1454615 := bstep (se 1 (by rfl) ⟨1090961, by rfl⟩ : syracuseStep 1454615 = 2181923) B2181923
theorem B1454795 : Blo 646304 1454795 := bstep (se 1 (by rfl) ⟨1091096, by rfl⟩ : syracuseStep 1454795 = 2182193) B2182193
theorem B8303309 : Blo 646304 8303309 := bstep (se 3 (by rfl) ⟨1556870, by rfl⟩ : syracuseStep 8303309 = 3113741) B3113741
theorem B1454849 : Blo 646304 1454849 := bstep (se 2 (by rfl) ⟨545568, by rfl⟩ : syracuseStep 1454849 = 1091137) B1091137
theorem B1094411 : Blo 646304 1094411 := bstep (se 1 (by rfl) ⟨820808, by rfl⟩ : syracuseStep 1094411 = 1641617) B1641617
theorem B5256029 : Blo 646304 5256029 := bstep (se 3 (by rfl) ⟨985505, by rfl⟩ : syracuseStep 5256029 = 1971011) B1971011
theorem B1094539 : Blo 646304 1094539 := bstep (se 1 (by rfl) ⟨820904, by rfl⟩ : syracuseStep 1094539 = 1641809) B1641809
theorem B2765771 : Blo 646304 2765771 := bstep (se 1 (by rfl) ⟨2074328, by rfl⟩ : syracuseStep 2765771 = 4148657) B4148657
theorem B1455065 : Blo 646304 1455065 := bstep (se 2 (by rfl) ⟨545649, by rfl⟩ : syracuseStep 1455065 = 1091299) B1091299
theorem B1749977 : Blo 646304 1749977 := bstep (se 2 (by rfl) ⟨656241, by rfl⟩ : syracuseStep 1749977 = 1312483) B1312483
theorem B1094681 : Blo 646304 1094681 := bstep (se 2 (by rfl) ⟨410505, by rfl⟩ : syracuseStep 1094681 = 821011) B821011
theorem B1455155 : Blo 646304 1455155 := bstep (se 1 (by rfl) ⟨1091366, by rfl⟩ : syracuseStep 1455155 = 2182733) B2182733
theorem B1455191 : Blo 646304 1455191 := bstep (se 1 (by rfl) ⟨1091393, by rfl⟩ : syracuseStep 1455191 = 2182787) B2182787
theorem B1094809 : Blo 646304 1094809 := bstep (se 2 (by rfl) ⟨410553, by rfl⟩ : syracuseStep 1094809 = 821107) B821107
theorem B1455371 : Blo 646304 1455371 := bstep (se 1 (by rfl) ⟨1091528, by rfl⟩ : syracuseStep 1455371 = 2183057) B2183057
theorem B1455425 : Blo 646304 1455425 := bstep (se 2 (by rfl) ⟨545784, by rfl⟩ : syracuseStep 1455425 = 1091569) B1091569
theorem B2766145 : Blo 646304 2766145 := bstep (se 2 (by rfl) ⟨1037304, by rfl⟩ : syracuseStep 2766145 = 2074609) B2074609
theorem B2078045 : Blo 646304 2078045 := bstep (se 3 (by rfl) ⟨389633, by rfl⟩ : syracuseStep 2078045 = 779267) B779267
theorem B1553843 : Blo 646304 1553843 := bstep (se 1 (by rfl) ⟨1165382, by rfl⟩ : syracuseStep 1553843 = 2330765) B2330765
theorem B1455641 : Blo 646304 1455641 := bstep (se 2 (by rfl) ⟨545865, by rfl⟩ : syracuseStep 1455641 = 1091731) B1091731
theorem B4142657 : Blo 646304 4142657 := bstep (se 2 (by rfl) ⟨1553496, by rfl⟩ : syracuseStep 4142657 = 3106993) B3106993
theorem B1455731 : Blo 646304 1455731 := bstep (se 1 (by rfl) ⟨1091798, by rfl⟩ : syracuseStep 1455731 = 2183597) B2183597
theorem B2635409 : Blo 646304 2635409 := bstep (se 2 (by rfl) ⟨988278, by rfl⟩ : syracuseStep 2635409 = 1976557) B1976557
theorem B1455767 : Blo 646304 1455767 := bstep (se 1 (by rfl) ⟨1091825, by rfl⟩ : syracuseStep 1455767 = 2183651) B2183651
theorem B2766487 : Blo 646304 2766487 := bstep (se 1 (by rfl) ⟨2074865, by rfl⟩ : syracuseStep 2766487 = 4149731) B4149731
theorem B1095383 : Blo 646304 1095383 := bstep (se 1 (by rfl) ⟨821537, by rfl⟩ : syracuseStep 1095383 = 1643075) B1643075
theorem B2340569 : Blo 646304 2340569 := bstep (se 2 (by rfl) ⟨877713, by rfl⟩ : syracuseStep 2340569 = 1755427) B1755427
theorem B1455947 : Blo 646304 1455947 := bstep (se 1 (by rfl) ⟨1091960, by rfl⟩ : syracuseStep 1455947 = 2183921) B2183921
theorem B1095511 : Blo 646304 1095511 := bstep (se 1 (by rfl) ⟨821633, by rfl⟩ : syracuseStep 1095511 = 1643267) B1643267
theorem B5551973 : Blo 646304 5551973 := bstep (se 4 (by rfl) ⟨520497, by rfl⟩ : syracuseStep 5551973 = 1040995) B1040995
theorem B1456001 : Blo 646304 1456001 := bstep (se 2 (by rfl) ⟨546000, by rfl⟩ : syracuseStep 1456001 = 1092001) B1092001
theorem B3684275 : Blo 646304 3684275 := bstep (se 1 (by rfl) ⟨2763206, by rfl⟩ : syracuseStep 3684275 = 5526413) B5526413
theorem B4929497 : Blo 646304 4929497 := bstep (se 2 (by rfl) ⟨1848561, by rfl⟩ : syracuseStep 4929497 = 3697123) B3697123
theorem B1554497 : Blo 646304 1554497 := bstep (se 2 (by rfl) ⟨582936, by rfl⟩ : syracuseStep 1554497 = 1165873) B1165873
theorem B1456217 : Blo 646304 1456217 := bstep (se 2 (by rfl) ⟨546081, by rfl⟩ : syracuseStep 1456217 = 1092163) B1092163
theorem B6666371 : Blo 646304 6666371 := bstep (se 1 (by rfl) ⟨4999778, by rfl⟩ : syracuseStep 6666371 = 9999557) B9999557
theorem B1456307 : Blo 646304 1456307 := bstep (se 1 (by rfl) ⟨1092230, by rfl⟩ : syracuseStep 1456307 = 2184461) B2184461
theorem B1456343 : Blo 646304 1456343 := bstep (se 1 (by rfl) ⟨1092257, by rfl⟩ : syracuseStep 1456343 = 2184515) B2184515
theorem B3291353 : Blo 646304 3291353 := bstep (se 2 (by rfl) ⟨1234257, by rfl⟩ : syracuseStep 3291353 = 2468515) B2468515
theorem B2078941 : Blo 646304 2078941 := bstep (se 3 (by rfl) ⟨389801, by rfl⟩ : syracuseStep 2078941 = 779603) B779603
theorem B1227059 : Blo 646304 1227059 := bstep (se 1 (by rfl) ⟨920294, by rfl⟩ : syracuseStep 1227059 = 1840589) B1840589
theorem B1456523 : Blo 646304 1456523 := bstep (se 1 (by rfl) ⟨1092392, by rfl⟩ : syracuseStep 1456523 = 2184785) B2184785
theorem B1456577 : Blo 646304 1456577 := bstep (se 2 (by rfl) ⟨546216, by rfl⟩ : syracuseStep 1456577 = 1092433) B1092433
theorem B1096139 : Blo 646304 1096139 := bstep (se 1 (by rfl) ⟨822104, by rfl⟩ : syracuseStep 1096139 = 1644209) B1644209
theorem B5552657 : Blo 646304 5552657 := bstep (se 2 (by rfl) ⟨2082246, by rfl⟩ : syracuseStep 5552657 = 4164493) B4164493
theorem B1227287 : Blo 646304 1227287 := bstep (se 1 (by rfl) ⟨920465, by rfl⟩ : syracuseStep 1227287 = 1840931) B1840931
theorem B2406935 : Blo 646304 2406935 := bstep (se 1 (by rfl) ⟨1805201, by rfl⟩ : syracuseStep 2406935 = 3610403) B3610403
theorem B1096267 : Blo 646304 1096267 := bstep (se 1 (by rfl) ⟨822200, by rfl⟩ : syracuseStep 1096267 = 1644401) B1644401
theorem B1456793 : Blo 646304 1456793 := bstep (se 2 (by rfl) ⟨546297, by rfl⟩ : syracuseStep 1456793 = 1092595) B1092595
theorem B1096409 : Blo 646304 1096409 := bstep (se 2 (by rfl) ⟨411153, by rfl⟩ : syracuseStep 1096409 = 822307) B822307
theorem B1456883 : Blo 646304 1456883 := bstep (se 1 (by rfl) ⟨1092662, by rfl⟩ : syracuseStep 1456883 = 2185325) B2185325
theorem B1456919 : Blo 646304 1456919 := bstep (se 1 (by rfl) ⟨1092689, by rfl⟩ : syracuseStep 1456919 = 2185379) B2185379
theorem B1227545 : Blo 646304 1227545 := bstep (se 2 (by rfl) ⟨460329, by rfl⟩ : syracuseStep 1227545 = 920659) B920659
theorem B1555265 : Blo 646304 1555265 := bstep (se 2 (by rfl) ⟨583224, by rfl⟩ : syracuseStep 1555265 = 1166449) B1166449
theorem B1096537 : Blo 646304 1096537 := bstep (se 2 (by rfl) ⟨411201, by rfl⟩ : syracuseStep 1096537 = 822403) B822403
theorem B1457099 : Blo 646304 1457099 := bstep (se 1 (by rfl) ⟨1092824, by rfl⟩ : syracuseStep 1457099 = 2185649) B2185649
theorem B1457153 : Blo 646304 1457153 := bstep (se 2 (by rfl) ⟨546432, by rfl⟩ : syracuseStep 1457153 = 1092865) B1092865
theorem B2964545 : Blo 646304 2964545 := bstep (se 2 (by rfl) ⟨1111704, by rfl⟩ : syracuseStep 2964545 = 2223409) B2223409
theorem B1227955 : Blo 646304 1227955 := bstep (se 1 (by rfl) ⟨920966, by rfl⟩ : syracuseStep 1227955 = 1841933) B1841933
theorem B1457369 : Blo 646304 1457369 := bstep (se 2 (by rfl) ⟨546513, by rfl⟩ : syracuseStep 1457369 = 1093027) B1093027
theorem B1850647 : Blo 646304 1850647 := bstep (se 1 (by rfl) ⟨1387985, by rfl⟩ : syracuseStep 1850647 = 2775971) B2775971
theorem B4209965 : Blo 646304 4209965 := bstep (se 3 (by rfl) ⟨789368, by rfl⟩ : syracuseStep 4209965 = 1578737) B1578737
theorem B1457459 : Blo 646304 1457459 := bstep (se 1 (by rfl) ⟨1093094, by rfl⟩ : syracuseStep 1457459 = 2186189) B2186189
theorem B1457495 : Blo 646304 1457495 := bstep (se 1 (by rfl) ⟨1093121, by rfl⟩ : syracuseStep 1457495 = 2186243) B2186243
theorem B3685733 : Blo 646304 3685733 := bstep (se 4 (by rfl) ⟨345537, by rfl⟩ : syracuseStep 3685733 = 691075) B691075
theorem B1097111 : Blo 646304 1097111 := bstep (se 1 (by rfl) ⟨822833, by rfl⟩ : syracuseStep 1097111 = 1645667) B1645667
theorem B1686977 : Blo 646304 1686977 := bstep (se 2 (by rfl) ⟨632616, by rfl⟩ : syracuseStep 1686977 = 1265233) B1265233
theorem B2801099 : Blo 646304 2801099 := bstep (se 1 (by rfl) ⟨2100824, by rfl⟩ : syracuseStep 2801099 = 4201649) B4201649
theorem B1457675 : Blo 646304 1457675 := bstep (se 1 (by rfl) ⟨1093256, by rfl⟩ : syracuseStep 1457675 = 2186513) B2186513
theorem B1097239 : Blo 646304 1097239 := bstep (se 1 (by rfl) ⟨822929, by rfl⟩ : syracuseStep 1097239 = 1645859) B1645859
theorem B1457729 : Blo 646304 1457729 := bstep (se 2 (by rfl) ⟨546648, by rfl⟩ : syracuseStep 1457729 = 1093297) B1093297
theorem B999001 : Blo 646304 999001 := bstep (se 2 (by rfl) ⟨374625, by rfl⟩ : syracuseStep 999001 = 749251) B749251
theorem B1228441 : Blo 646304 1228441 := bstep (se 2 (by rfl) ⟨460665, by rfl⟩ : syracuseStep 1228441 = 921331) B921331
theorem B1752779 : Blo 646304 1752779 := bstep (se 1 (by rfl) ⟨1314584, by rfl⟩ : syracuseStep 1752779 = 2629169) B2629169
theorem B933655 : Blo 646304 933655 := bstep (se 1 (by rfl) ⟨700241, by rfl⟩ : syracuseStep 933655 = 1400483) B1400483
theorem B1261337 : Blo 646304 1261337 := bstep (se 2 (by rfl) ⟨473001, by rfl⟩ : syracuseStep 1261337 = 946003) B946003
theorem B1457945 : Blo 646304 1457945 := bstep (se 2 (by rfl) ⟨546729, by rfl⟩ : syracuseStep 1457945 = 1093459) B1093459
theorem B1458035 : Blo 646304 1458035 := bstep (se 1 (by rfl) ⟨1093526, by rfl⟩ : syracuseStep 1458035 = 2187053) B2187053
theorem B1458071 : Blo 646304 1458071 := bstep (se 1 (by rfl) ⟨1093553, by rfl⟩ : syracuseStep 1458071 = 2187107) B2187107
theorem B3686417 : Blo 646304 3686417 := bstep (se 2 (by rfl) ⟨1382406, by rfl⟩ : syracuseStep 3686417 = 2764813) B2764813
theorem B1458251 : Blo 646304 1458251 := bstep (se 1 (by rfl) ⟨1093688, by rfl⟩ : syracuseStep 1458251 = 2187377) B2187377
theorem B1458305 : Blo 646304 1458305 := bstep (se 2 (by rfl) ⟨546864, by rfl⟩ : syracuseStep 1458305 = 1093729) B1093729
theorem B1229003 : Blo 646304 1229003 := bstep (se 1 (by rfl) ⟨921752, by rfl⟩ : syracuseStep 1229003 = 1843505) B1843505
theorem B1458521 : Blo 646304 1458521 := bstep (se 2 (by rfl) ⟨546945, by rfl⟩ : syracuseStep 1458521 = 1093891) B1093891
theorem B1229185 : Blo 646304 1229185 := bstep (se 2 (by rfl) ⟨460944, by rfl⟩ : syracuseStep 1229185 = 921889) B921889
theorem B1458611 : Blo 646304 1458611 := bstep (se 1 (by rfl) ⟨1093958, by rfl⟩ : syracuseStep 1458611 = 2187917) B2187917
theorem B1458647 : Blo 646304 1458647 := bstep (se 1 (by rfl) ⟨1093985, by rfl⟩ : syracuseStep 1458647 = 2187971) B2187971
theorem B23708173 : Blo 646304 23708173 := bstep (se 3 (by rfl) ⟨4445282, by rfl⟩ : syracuseStep 23708173 = 8890565) B8890565
theorem B1458827 : Blo 646304 1458827 := bstep (se 1 (by rfl) ⟨1094120, by rfl⟩ : syracuseStep 1458827 = 2188241) B2188241
theorem B1458881 : Blo 646304 1458881 := bstep (se 2 (by rfl) ⟨547080, by rfl⟩ : syracuseStep 1458881 = 1094161) B1094161
theorem B4997963 : Blo 646304 4997963 := bstep (se 1 (by rfl) ⟨3748472, by rfl⟩ : syracuseStep 4997963 = 7496945) B7496945
theorem B1459097 : Blo 646304 1459097 := bstep (se 2 (by rfl) ⟨547161, by rfl⟩ : syracuseStep 1459097 = 1094323) B1094323
theorem B1459187 : Blo 646304 1459187 := bstep (se 1 (by rfl) ⟨1094390, by rfl⟩ : syracuseStep 1459187 = 2188781) B2188781
theorem B1459223 : Blo 646304 1459223 := bstep (se 1 (by rfl) ⟨1094417, by rfl⟩ : syracuseStep 1459223 = 2188835) B2188835
theorem B1229899 : Blo 646304 1229899 := bstep (se 1 (by rfl) ⟨922424, by rfl⟩ : syracuseStep 1229899 = 1844849) B1844849
theorem B1557593 : Blo 646304 1557593 := bstep (se 2 (by rfl) ⟨584097, by rfl⟩ : syracuseStep 1557593 = 1168195) B1168195
theorem B1229975 : Blo 646304 1229975 := bstep (se 1 (by rfl) ⟨922481, by rfl⟩ : syracuseStep 1229975 = 1844963) B1844963
theorem B2671795 : Blo 646304 2671795 := bstep (se 1 (by rfl) ⟨2003846, by rfl⟩ : syracuseStep 2671795 = 4007693) B4007693
theorem B1459403 : Blo 646304 1459403 := bstep (se 1 (by rfl) ⟨1094552, by rfl⟩ : syracuseStep 1459403 = 2189105) B2189105
theorem B1459457 : Blo 646304 1459457 := bstep (se 2 (by rfl) ⟨547296, by rfl⟩ : syracuseStep 1459457 = 1094593) B1094593
theorem B47301893 : Blo 646304 47301893 := bstep (se 4 (by rfl) ⟨4434552, by rfl⟩ : syracuseStep 47301893 = 8869105) B8869105
theorem B4932899 : Blo 646304 4932899 := bstep (se 1 (by rfl) ⟨3699674, by rfl⟩ : syracuseStep 4932899 = 7399349) B7399349
theorem B1459673 : Blo 646304 1459673 := bstep (se 2 (by rfl) ⟨547377, by rfl⟩ : syracuseStep 1459673 = 1094755) B1094755
theorem B1459763 : Blo 646304 1459763 := bstep (se 1 (by rfl) ⟨1094822, by rfl⟩ : syracuseStep 1459763 = 2189645) B2189645
theorem B1459799 : Blo 646304 1459799 := bstep (se 1 (by rfl) ⟨1094849, by rfl⟩ : syracuseStep 1459799 = 2189699) B2189699
theorem B1459979 : Blo 646304 1459979 := bstep (se 1 (by rfl) ⟨1094984, by rfl⟩ : syracuseStep 1459979 = 2189969) B2189969
theorem B1230643 : Blo 646304 1230643 := bstep (se 1 (by rfl) ⟨922982, by rfl⟩ : syracuseStep 1230643 = 1845965) B1845965
theorem B1460033 : Blo 646304 1460033 := bstep (se 2 (by rfl) ⟨547512, by rfl⟩ : syracuseStep 1460033 = 1095025) B1095025
theorem B39929699 : Blo 646304 39929699 := bstep (se 1 (by rfl) ⟨29947274, by rfl⟩ : syracuseStep 39929699 = 59894549) B59894549
theorem B2770861 : Blo 646304 2770861 := bstep (se 3 (by rfl) ⟨519536, by rfl⟩ : syracuseStep 2770861 = 1039073) B1039073
theorem B1230871 : Blo 646304 1230871 := bstep (se 1 (by rfl) ⟨923153, by rfl⟩ : syracuseStep 1230871 = 1846307) B1846307
theorem B1460249 : Blo 646304 1460249 := bstep (se 2 (by rfl) ⟨547593, by rfl⟩ : syracuseStep 1460249 = 1095187) B1095187
theorem B1460339 : Blo 646304 1460339 := bstep (se 1 (by rfl) ⟨1095254, by rfl⟩ : syracuseStep 1460339 = 2190509) B2190509
theorem B1230977 : Blo 646304 1230977 := bstep (se 2 (by rfl) ⟨461616, by rfl⟩ : syracuseStep 1230977 = 923233) B923233
theorem B1460375 : Blo 646304 1460375 := bstep (se 1 (by rfl) ⟨1095281, by rfl⟩ : syracuseStep 1460375 = 2190563) B2190563
theorem B739531 : Blo 646304 739531 := bstep (se 1 (by rfl) ⟨554648, by rfl⟩ : syracuseStep 739531 = 1109297) B1109297
theorem B1231129 : Blo 646304 1231129 := bstep (se 2 (by rfl) ⟨461673, by rfl⟩ : syracuseStep 1231129 = 923347) B923347
theorem B1460555 : Blo 646304 1460555 := bstep (se 1 (by rfl) ⟨1095416, by rfl⟩ : syracuseStep 1460555 = 2190833) B2190833
theorem B1460609 : Blo 646304 1460609 := bstep (se 2 (by rfl) ⟨547728, by rfl⟩ : syracuseStep 1460609 = 1095457) B1095457
theorem B4999715 : Blo 646304 4999715 := bstep (se 1 (by rfl) ⟨3749786, by rfl⟩ : syracuseStep 4999715 = 7499573) B7499573
theorem B739895 : Blo 646304 739895 := bstep (se 1 (by rfl) ⟨554921, by rfl⟩ : syracuseStep 739895 = 1109843) B1109843
theorem B2181707 : Blo 646304 2181707 := bstep (se 1 (by rfl) ⟨1636280, by rfl⟩ : syracuseStep 2181707 = 3272561) B3272561
theorem B1460825 : Blo 646304 1460825 := bstep (se 2 (by rfl) ⟨547809, by rfl⟩ : syracuseStep 1460825 = 1095619) B1095619
theorem B1460915 : Blo 646304 1460915 := bstep (se 1 (by rfl) ⟨1095686, by rfl⟩ : syracuseStep 1460915 = 2191373) B2191373
theorem B1460951 : Blo 646304 1460951 := bstep (se 1 (by rfl) ⟨1095713, by rfl⟩ : syracuseStep 1460951 = 2191427) B2191427
theorem B969497 : Blo 646304 969497 := bstep (se 2 (by rfl) ⟨363561, by rfl⟩ : syracuseStep 969497 = 727123) B727123
theorem B2181977 : Blo 646304 2181977 := bstep (se 2 (by rfl) ⟨818241, by rfl⟩ : syracuseStep 2181977 = 1636483) B1636483
theorem B969611 : Blo 646304 969611 := bstep (se 1 (by rfl) ⟨727208, by rfl⟩ : syracuseStep 969611 = 1454417) B1454417
theorem B1461131 : Blo 646304 1461131 := bstep (se 1 (by rfl) ⟨1095848, by rfl⟩ : syracuseStep 1461131 = 2191697) B2191697
theorem B969623 : Blo 646304 969623 := bstep (se 1 (by rfl) ⟨727217, by rfl⟩ : syracuseStep 969623 = 1454435) B1454435
theorem B22465457 : Blo 646304 22465457 := bstep (se 2 (by rfl) ⟨8424546, by rfl⟩ : syracuseStep 22465457 = 16849093) B16849093
theorem B1461185 : Blo 646304 1461185 := bstep (se 2 (by rfl) ⟨547944, by rfl⟩ : syracuseStep 1461185 = 1095889) B1095889
theorem B969689 : Blo 646304 969689 := bstep (se 2 (by rfl) ⟨363633, by rfl⟩ : syracuseStep 969689 = 727267) B727267
theorem B740407 : Blo 646304 740407 := bstep (se 1 (by rfl) ⟨555305, by rfl⟩ : syracuseStep 740407 = 1110611) B1110611
theorem B969803 : Blo 646304 969803 := bstep (se 1 (by rfl) ⟨727352, by rfl⟩ : syracuseStep 969803 = 1454705) B1454705
theorem B969815 : Blo 646304 969815 := bstep (se 1 (by rfl) ⟨727361, by rfl⟩ : syracuseStep 969815 = 1454723) B1454723
theorem B969881 : Blo 646304 969881 := bstep (se 2 (by rfl) ⟨363705, by rfl⟩ : syracuseStep 969881 = 727411) B727411
theorem B1461401 : Blo 646304 1461401 := bstep (se 2 (by rfl) ⟨548025, by rfl⟩ : syracuseStep 1461401 = 1096051) B1096051
theorem B3689651 : Blo 646304 3689651 := bstep (se 1 (by rfl) ⟨2767238, by rfl⟩ : syracuseStep 3689651 = 5534477) B5534477
theorem B1461491 : Blo 646304 1461491 := bstep (se 1 (by rfl) ⟨1096118, by rfl⟩ : syracuseStep 1461491 = 2192237) B2192237
theorem B969995 : Blo 646304 969995 := bstep (se 1 (by rfl) ⟨727496, by rfl⟩ : syracuseStep 969995 = 1454993) B1454993
theorem B970007 : Blo 646304 970007 := bstep (se 1 (by rfl) ⟨727505, by rfl⟩ : syracuseStep 970007 = 1455011) B1455011
theorem B1461527 : Blo 646304 1461527 := bstep (se 1 (by rfl) ⟨1096145, by rfl⟩ : syracuseStep 1461527 = 2192291) B2192291
theorem B970073 : Blo 646304 970073 := bstep (se 2 (by rfl) ⟨363777, by rfl⟩ : syracuseStep 970073 = 727555) B727555
theorem B1035659 : Blo 646304 1035659 := bstep (se 1 (by rfl) ⟨776744, by rfl⟩ : syracuseStep 1035659 = 1553489) B1553489
theorem B2805137 : Blo 646304 2805137 := bstep (se 2 (by rfl) ⟨1051926, by rfl⟩ : syracuseStep 2805137 = 2103853) B2103853
theorem B970187 : Blo 646304 970187 := bstep (se 1 (by rfl) ⟨727640, by rfl⟩ : syracuseStep 970187 = 1455281) B1455281
theorem B1461707 : Blo 646304 1461707 := bstep (se 1 (by rfl) ⟨1096280, by rfl⟩ : syracuseStep 1461707 = 2192561) B2192561
theorem B970199 : Blo 646304 970199 := bstep (se 1 (by rfl) ⟨727649, by rfl⟩ : syracuseStep 970199 = 1455299) B1455299
theorem B1461761 : Blo 646304 1461761 := bstep (se 2 (by rfl) ⟨548160, by rfl⟩ : syracuseStep 1461761 = 1096321) B1096321
theorem B2182679 : Blo 646304 2182679 := bstep (se 1 (by rfl) ⟨1637009, by rfl⟩ : syracuseStep 2182679 = 3274019) B3274019
theorem B970265 : Blo 646304 970265 := bstep (se 2 (by rfl) ⟨363849, by rfl⟩ : syracuseStep 970265 = 727699) B727699
theorem B1232435 : Blo 646304 1232435 := bstep (se 1 (by rfl) ⟨924326, by rfl⟩ : syracuseStep 1232435 = 1848653) B1848653
theorem B2772569 : Blo 646304 2772569 := bstep (se 2 (by rfl) ⟨1039713, by rfl⟩ : syracuseStep 2772569 = 2079427) B2079427
theorem B970379 : Blo 646304 970379 := bstep (se 1 (by rfl) ⟨727784, by rfl⟩ : syracuseStep 970379 = 1455569) B1455569
theorem B970391 : Blo 646304 970391 := bstep (se 1 (by rfl) ⟨727793, by rfl⟩ : syracuseStep 970391 = 1455587) B1455587
theorem B1232587 : Blo 646304 1232587 := bstep (se 1 (by rfl) ⟨924440, by rfl⟩ : syracuseStep 1232587 = 1848881) B1848881
theorem B970457 : Blo 646304 970457 := bstep (se 2 (by rfl) ⟨363921, by rfl⟩ : syracuseStep 970457 = 727843) B727843
theorem B1461977 : Blo 646304 1461977 := bstep (se 2 (by rfl) ⟨548241, by rfl⟩ : syracuseStep 1461977 = 1096483) B1096483
theorem B1462067 : Blo 646304 1462067 := bstep (se 1 (by rfl) ⟨1096550, by rfl⟩ : syracuseStep 1462067 = 2193101) B2193101
theorem B2215745 : Blo 646304 2215745 := bstep (se 2 (by rfl) ⟨830904, by rfl⟩ : syracuseStep 2215745 = 1661809) B1661809
theorem B970571 : Blo 646304 970571 := bstep (se 1 (by rfl) ⟨727928, by rfl⟩ : syracuseStep 970571 = 1455857) B1455857
theorem B970583 : Blo 646304 970583 := bstep (se 1 (by rfl) ⟨727937, by rfl⟩ : syracuseStep 970583 = 1455875) B1455875
theorem B1462103 : Blo 646304 1462103 := bstep (se 1 (by rfl) ⟨1096577, by rfl⟩ : syracuseStep 1462103 = 2193155) B2193155
theorem B16797539 : Blo 646304 16797539 := bstep (se 1 (by rfl) ⟨12598154, by rfl⟩ : syracuseStep 16797539 = 25196309) B25196309
theorem B970649 : Blo 646304 970649 := bstep (se 2 (by rfl) ⟨363993, by rfl⟩ : syracuseStep 970649 = 727987) B727987
theorem B970763 : Blo 646304 970763 := bstep (se 1 (by rfl) ⟨728072, by rfl⟩ : syracuseStep 970763 = 1456145) B1456145
theorem B1462283 : Blo 646304 1462283 := bstep (se 1 (by rfl) ⟨1096712, by rfl⟩ : syracuseStep 1462283 = 2193425) B2193425
theorem B970775 : Blo 646304 970775 := bstep (se 1 (by rfl) ⟨728081, by rfl⟩ : syracuseStep 970775 = 1456163) B1456163
theorem B1232921 : Blo 646304 1232921 := bstep (se 2 (by rfl) ⟨462345, by rfl⟩ : syracuseStep 1232921 = 924691) B924691
theorem B2183219 : Blo 646304 2183219 := bstep (se 1 (by rfl) ⟨1637414, by rfl⟩ : syracuseStep 2183219 = 3274829) B3274829
theorem B1462337 : Blo 646304 1462337 := bstep (se 2 (by rfl) ⟨548376, by rfl⟩ : syracuseStep 1462337 = 1096753) B1096753
theorem B970841 : Blo 646304 970841 := bstep (se 2 (by rfl) ⟨364065, by rfl⟩ : syracuseStep 970841 = 728131) B728131
theorem B970955 : Blo 646304 970955 := bstep (se 1 (by rfl) ⟨728216, by rfl⟩ : syracuseStep 970955 = 1456433) B1456433
theorem B970967 : Blo 646304 970967 := bstep (se 1 (by rfl) ⟨728225, by rfl⟩ : syracuseStep 970967 = 1456451) B1456451
theorem B971033 : Blo 646304 971033 := bstep (se 2 (by rfl) ⟨364137, by rfl⟩ : syracuseStep 971033 = 728275) B728275
theorem B1462553 : Blo 646304 1462553 := bstep (se 2 (by rfl) ⟨548457, by rfl⟩ : syracuseStep 1462553 = 1096915) B1096915
theorem B2183489 : Blo 646304 2183489 := bstep (se 2 (by rfl) ⟨818808, by rfl⟩ : syracuseStep 2183489 = 1637617) B1637617
theorem B1036633 : Blo 646304 1036633 := bstep (se 2 (by rfl) ⟨388737, by rfl⟩ : syracuseStep 1036633 = 777475) B777475
theorem B2216281 : Blo 646304 2216281 := bstep (se 2 (by rfl) ⟨831105, by rfl⟩ : syracuseStep 2216281 = 1662211) B1662211
theorem B1462643 : Blo 646304 1462643 := bstep (se 1 (by rfl) ⟨1096982, by rfl⟩ : syracuseStep 1462643 = 2193965) B2193965
theorem B971147 : Blo 646304 971147 := bstep (se 1 (by rfl) ⟨728360, by rfl⟩ : syracuseStep 971147 = 1456721) B1456721
theorem B971159 : Blo 646304 971159 := bstep (se 1 (by rfl) ⟨728369, by rfl⟩ : syracuseStep 971159 = 1456739) B1456739
theorem B1462679 : Blo 646304 1462679 := bstep (se 1 (by rfl) ⟨1097009, by rfl⟩ : syracuseStep 1462679 = 2194019) B2194019
theorem B971225 : Blo 646304 971225 := bstep (se 2 (by rfl) ⟨364209, by rfl⟩ : syracuseStep 971225 = 728419) B728419
theorem B1167833 : Blo 646304 1167833 := bstep (se 2 (by rfl) ⟨437937, by rfl⟩ : syracuseStep 1167833 = 875875) B875875
theorem B971339 : Blo 646304 971339 := bstep (se 1 (by rfl) ⟨728504, by rfl⟩ : syracuseStep 971339 = 1457009) B1457009
theorem B1462859 : Blo 646304 1462859 := bstep (se 1 (by rfl) ⟨1097144, by rfl⟩ : syracuseStep 1462859 = 2194289) B2194289
theorem B971351 : Blo 646304 971351 := bstep (se 1 (by rfl) ⟨728513, by rfl⟩ : syracuseStep 971351 = 1457027) B1457027
theorem B1036889 : Blo 646304 1036889 := bstep (se 2 (by rfl) ⟨388833, by rfl⟩ : syracuseStep 1036889 = 777667) B777667
theorem B3691109 : Blo 646304 3691109 := bstep (se 4 (by rfl) ⟨346041, by rfl⟩ : syracuseStep 3691109 = 692083) B692083
theorem B1462913 : Blo 646304 1462913 := bstep (se 2 (by rfl) ⟨548592, by rfl⟩ : syracuseStep 1462913 = 1097185) B1097185
theorem B1233559 : Blo 646304 1233559 := bstep (se 1 (by rfl) ⟨925169, by rfl⟩ : syracuseStep 1233559 = 1850339) B1850339
theorem B971417 : Blo 646304 971417 := bstep (se 2 (by rfl) ⟨364281, by rfl⟩ : syracuseStep 971417 = 728563) B728563
theorem B11096837 : Blo 646304 11096837 := bstep (se 4 (by rfl) ⟨1040328, by rfl⟩ : syracuseStep 11096837 = 2080657) B2080657
theorem B971531 : Blo 646304 971531 := bstep (se 1 (by rfl) ⟨728648, by rfl⟩ : syracuseStep 971531 = 1457297) B1457297
theorem B971543 : Blo 646304 971543 := bstep (se 1 (by rfl) ⟨728657, by rfl⟩ : syracuseStep 971543 = 1457315) B1457315
theorem B2773835 : Blo 646304 2773835 := bstep (se 1 (by rfl) ⟨2080376, by rfl⟩ : syracuseStep 2773835 = 4160753) B4160753
theorem B971609 : Blo 646304 971609 := bstep (se 2 (by rfl) ⟨364353, by rfl⟩ : syracuseStep 971609 = 728707) B728707
theorem B1463129 : Blo 646304 1463129 := bstep (se 2 (by rfl) ⟨548673, by rfl⟩ : syracuseStep 1463129 = 1097347) B1097347
theorem B2184029 : Blo 646304 2184029 := bstep (se 3 (by rfl) ⟨409505, by rfl⟩ : syracuseStep 2184029 = 819011) B819011
theorem B971723 : Blo 646304 971723 := bstep (se 1 (by rfl) ⟨728792, by rfl⟩ : syracuseStep 971723 = 1457585) B1457585
theorem B971735 : Blo 646304 971735 := bstep (se 1 (by rfl) ⟨728801, by rfl⟩ : syracuseStep 971735 = 1457603) B1457603
theorem B971801 : Blo 646304 971801 := bstep (se 2 (by rfl) ⟨364425, by rfl⟩ : syracuseStep 971801 = 728851) B728851
theorem B3691565 : Blo 646304 3691565 := bstep (se 3 (by rfl) ⟨692168, by rfl⟩ : syracuseStep 3691565 = 1384337) B1384337
theorem B971915 : Blo 646304 971915 := bstep (se 1 (by rfl) ⟨728936, by rfl⟩ : syracuseStep 971915 = 1457873) B1457873
theorem B971927 : Blo 646304 971927 := bstep (se 1 (by rfl) ⟨728945, by rfl⟩ : syracuseStep 971927 = 1457891) B1457891
theorem B2774195 : Blo 646304 2774195 := bstep (se 1 (by rfl) ⟨2080646, by rfl⟩ : syracuseStep 2774195 = 4161293) B4161293
theorem B971993 : Blo 646304 971993 := bstep (se 2 (by rfl) ⟨364497, by rfl⟩ : syracuseStep 971993 = 728995) B728995
theorem B972107 : Blo 646304 972107 := bstep (se 1 (by rfl) ⟨729080, by rfl⟩ : syracuseStep 972107 = 1458161) B1458161
theorem B972119 : Blo 646304 972119 := bstep (se 1 (by rfl) ⟨729089, by rfl⟩ : syracuseStep 972119 = 1458179) B1458179
theorem B972185 : Blo 646304 972185 := bstep (se 2 (by rfl) ⟨364569, by rfl⟩ : syracuseStep 972185 = 729139) B729139
theorem B1234379 : Blo 646304 1234379 := bstep (se 1 (by rfl) ⟨925784, by rfl⟩ : syracuseStep 1234379 = 1851569) B1851569
theorem B1234433 : Blo 646304 1234433 := bstep (se 2 (by rfl) ⟨462912, by rfl⟩ : syracuseStep 1234433 = 925825) B925825
theorem B972299 : Blo 646304 972299 := bstep (se 1 (by rfl) ⟨729224, by rfl⟩ : syracuseStep 972299 = 1458449) B1458449
theorem B972311 : Blo 646304 972311 := bstep (se 1 (by rfl) ⟨729233, by rfl⟩ : syracuseStep 972311 = 1458467) B1458467
theorem B972377 : Blo 646304 972377 := bstep (se 2 (by rfl) ⟨364641, by rfl⟩ : syracuseStep 972377 = 729283) B729283
theorem B972491 : Blo 646304 972491 := bstep (se 1 (by rfl) ⟨729368, by rfl⟩ : syracuseStep 972491 = 1458737) B1458737
theorem B972503 : Blo 646304 972503 := bstep (se 1 (by rfl) ⟨729377, by rfl⟩ : syracuseStep 972503 = 1458755) B1458755
theorem B3692249 : Blo 646304 3692249 := bstep (se 2 (by rfl) ⟨1384593, by rfl⟩ : syracuseStep 3692249 = 2769187) B2769187
theorem B972569 : Blo 646304 972569 := bstep (se 2 (by rfl) ⟨364713, by rfl⟩ : syracuseStep 972569 = 729427) B729427
theorem B972683 : Blo 646304 972683 := bstep (se 1 (by rfl) ⟨729512, by rfl⟩ : syracuseStep 972683 = 1459025) B1459025
theorem B972695 : Blo 646304 972695 := bstep (se 1 (by rfl) ⟨729521, by rfl⟩ : syracuseStep 972695 = 1459043) B1459043
theorem B2185163 : Blo 646304 2185163 := bstep (se 1 (by rfl) ⟨1638872, by rfl⟩ : syracuseStep 2185163 = 3277745) B3277745
theorem B972761 : Blo 646304 972761 := bstep (se 2 (by rfl) ⟨364785, by rfl⟩ : syracuseStep 972761 = 729571) B729571
theorem B1169419 : Blo 646304 1169419 := bstep (se 1 (by rfl) ⟨877064, by rfl⟩ : syracuseStep 1169419 = 1754129) B1754129
theorem B2250775 : Blo 646304 2250775 := bstep (se 1 (by rfl) ⟨1688081, by rfl⟩ : syracuseStep 2250775 = 3376163) B3376163
theorem B4151371 : Blo 646304 4151371 := bstep (se 1 (by rfl) ⟨3113528, by rfl⟩ : syracuseStep 4151371 = 6227057) B6227057
theorem B972875 : Blo 646304 972875 := bstep (se 1 (by rfl) ⟨729656, by rfl⟩ : syracuseStep 972875 = 1459313) B1459313
theorem B972887 : Blo 646304 972887 := bstep (se 1 (by rfl) ⟨729665, by rfl⟩ : syracuseStep 972887 = 1459331) B1459331
theorem B4675715 : Blo 646304 4675715 := bstep (se 1 (by rfl) ⟨3506786, by rfl⟩ : syracuseStep 4675715 = 7013573) B7013573
theorem B972953 : Blo 646304 972953 := bstep (se 2 (by rfl) ⟨364857, by rfl⟩ : syracuseStep 972953 = 729715) B729715
theorem B2185433 : Blo 646304 2185433 := bstep (se 2 (by rfl) ⟨819537, by rfl⟩ : syracuseStep 2185433 = 1639075) B1639075
theorem B973067 : Blo 646304 973067 := bstep (se 1 (by rfl) ⟨729800, by rfl⟩ : syracuseStep 973067 = 1459601) B1459601
theorem B973079 : Blo 646304 973079 := bstep (se 1 (by rfl) ⟨729809, by rfl⟩ : syracuseStep 973079 = 1459619) B1459619
theorem B973145 : Blo 646304 973145 := bstep (se 2 (by rfl) ⟨364929, by rfl⟩ : syracuseStep 973145 = 729859) B729859
theorem B973259 : Blo 646304 973259 := bstep (se 1 (by rfl) ⟨729944, by rfl⟩ : syracuseStep 973259 = 1459889) B1459889
theorem B874967 : Blo 646304 874967 := bstep (se 1 (by rfl) ⟨656225, by rfl⟩ : syracuseStep 874967 = 1312451) B1312451
theorem B973271 : Blo 646304 973271 := bstep (se 1 (by rfl) ⟨729953, by rfl⟩ : syracuseStep 973271 = 1459907) B1459907
theorem B4938245 : Blo 646304 4938245 := bstep (se 4 (by rfl) ⟨462960, by rfl⟩ : syracuseStep 4938245 = 925921) B925921
theorem B973337 : Blo 646304 973337 := bstep (se 2 (by rfl) ⟨365001, by rfl⟩ : syracuseStep 973337 = 730003) B730003
theorem B973451 : Blo 646304 973451 := bstep (se 1 (by rfl) ⟨730088, by rfl⟩ : syracuseStep 973451 = 1460177) B1460177
theorem B973463 : Blo 646304 973463 := bstep (se 1 (by rfl) ⟨730097, by rfl⟩ : syracuseStep 973463 = 1460195) B1460195
theorem B973529 : Blo 646304 973529 := bstep (se 2 (by rfl) ⟨365073, by rfl⟩ : syracuseStep 973529 = 730147) B730147
theorem B973643 : Blo 646304 973643 := bstep (se 1 (by rfl) ⟨730232, by rfl⟩ : syracuseStep 973643 = 1460465) B1460465
theorem B973655 : Blo 646304 973655 := bstep (se 1 (by rfl) ⟨730241, by rfl⟩ : syracuseStep 973655 = 1460483) B1460483
theorem B2186135 : Blo 646304 2186135 := bstep (se 1 (by rfl) ⟨1639601, by rfl⟩ : syracuseStep 2186135 = 3279203) B3279203
theorem B973721 : Blo 646304 973721 := bstep (se 2 (by rfl) ⟨365145, by rfl⟩ : syracuseStep 973721 = 730291) B730291
theorem B973835 : Blo 646304 973835 := bstep (se 1 (by rfl) ⟨730376, by rfl⟩ : syracuseStep 973835 = 1460753) B1460753
theorem B973847 : Blo 646304 973847 := bstep (se 1 (by rfl) ⟨730385, by rfl⟩ : syracuseStep 973847 = 1460771) B1460771
theorem B5135425 : Blo 646304 5135425 := bstep (se 2 (by rfl) ⟨1925784, by rfl⟩ : syracuseStep 5135425 = 3851569) B3851569
theorem B973913 : Blo 646304 973913 := bstep (se 2 (by rfl) ⟨365217, by rfl⟩ : syracuseStep 973913 = 730435) B730435
theorem B646315 : Blo 646304 646315 := bstep (se 1 (by rfl) ⟨484736, by rfl⟩ : syracuseStep 646315 = 969473) B969473
theorem B646327 : Blo 646304 646327 := bstep (se 1 (by rfl) ⟨484745, by rfl⟩ : syracuseStep 646327 = 969491) B969491
theorem B646347 : Blo 646304 646347 := bstep (se 1 (by rfl) ⟨484760, by rfl⟩ : syracuseStep 646347 = 969521) B969521
theorem B974027 : Blo 646304 974027 := bstep (se 1 (by rfl) ⟨730520, by rfl⟩ : syracuseStep 974027 = 1461041) B1461041
theorem B646359 : Blo 646304 646359 := bstep (se 1 (by rfl) ⟨484769, by rfl⟩ : syracuseStep 646359 = 969539) B969539
theorem B974039 : Blo 646304 974039 := bstep (se 1 (by rfl) ⟨730529, by rfl⟩ : syracuseStep 974039 = 1461059) B1461059
theorem B646379 : Blo 646304 646379 := bstep (se 1 (by rfl) ⟨484784, by rfl⟩ : syracuseStep 646379 = 969569) B969569
theorem B646391 : Blo 646304 646391 := bstep (se 1 (by rfl) ⟨484793, by rfl⟩ : syracuseStep 646391 = 969587) B969587
theorem B646411 : Blo 646304 646411 := bstep (se 1 (by rfl) ⟨484808, by rfl⟩ : syracuseStep 646411 = 969617) B969617
theorem B646423 : Blo 646304 646423 := bstep (se 1 (by rfl) ⟨484817, by rfl⟩ : syracuseStep 646423 = 969635) B969635
theorem B974105 : Blo 646304 974105 := bstep (se 2 (by rfl) ⟨365289, by rfl⟩ : syracuseStep 974105 = 730579) B730579
theorem B646443 : Blo 646304 646443 := bstep (se 1 (by rfl) ⟨484832, by rfl⟩ : syracuseStep 646443 = 969665) B969665
theorem B646455 : Blo 646304 646455 := bstep (se 1 (by rfl) ⟨484841, by rfl⟩ : syracuseStep 646455 = 969683) B969683
theorem B646475 : Blo 646304 646475 := bstep (se 1 (by rfl) ⟨484856, by rfl⟩ : syracuseStep 646475 = 969713) B969713
theorem B646487 : Blo 646304 646487 := bstep (se 1 (by rfl) ⟨484865, by rfl⟩ : syracuseStep 646487 = 969731) B969731
theorem B646507 : Blo 646304 646507 := bstep (se 1 (by rfl) ⟨484880, by rfl⟩ : syracuseStep 646507 = 969761) B969761
theorem B1170803 : Blo 646304 1170803 := bstep (se 1 (by rfl) ⟨878102, by rfl⟩ : syracuseStep 1170803 = 1756205) B1756205
theorem B646519 : Blo 646304 646519 := bstep (se 1 (by rfl) ⟨484889, by rfl⟩ : syracuseStep 646519 = 969779) B969779
theorem B646539 : Blo 646304 646539 := bstep (se 1 (by rfl) ⟨484904, by rfl⟩ : syracuseStep 646539 = 969809) B969809
theorem B974219 : Blo 646304 974219 := bstep (se 1 (by rfl) ⟨730664, by rfl⟩ : syracuseStep 974219 = 1461329) B1461329
theorem B646551 : Blo 646304 646551 := bstep (se 1 (by rfl) ⟨484913, by rfl⟩ : syracuseStep 646551 = 969827) B969827
theorem B974231 : Blo 646304 974231 := bstep (se 1 (by rfl) ⟨730673, by rfl⟩ : syracuseStep 974231 = 1461347) B1461347
theorem B646571 : Blo 646304 646571 := bstep (se 1 (by rfl) ⟨484928, by rfl⟩ : syracuseStep 646571 = 969857) B969857
theorem B2186675 : Blo 646304 2186675 := bstep (se 1 (by rfl) ⟨1640006, by rfl⟩ : syracuseStep 2186675 = 3280013) B3280013
theorem B646583 : Blo 646304 646583 := bstep (se 1 (by rfl) ⟨484937, by rfl⟩ : syracuseStep 646583 = 969875) B969875
theorem B646603 : Blo 646304 646603 := bstep (se 1 (by rfl) ⟨484952, by rfl⟩ : syracuseStep 646603 = 969905) B969905
theorem B646615 : Blo 646304 646615 := bstep (se 1 (by rfl) ⟨484961, by rfl⟩ : syracuseStep 646615 = 969923) B969923
theorem B974297 : Blo 646304 974297 := bstep (se 2 (by rfl) ⟨365361, by rfl⟩ : syracuseStep 974297 = 730723) B730723
theorem B646635 : Blo 646304 646635 := bstep (se 1 (by rfl) ⟨484976, by rfl⟩ : syracuseStep 646635 = 969953) B969953
theorem B646647 : Blo 646304 646647 := bstep (se 1 (by rfl) ⟨484985, by rfl⟩ : syracuseStep 646647 = 969971) B969971
theorem B646667 : Blo 646304 646667 := bstep (se 1 (by rfl) ⟨485000, by rfl⟩ : syracuseStep 646667 = 970001) B970001
theorem B646679 : Blo 646304 646679 := bstep (se 1 (by rfl) ⟨485009, by rfl⟩ : syracuseStep 646679 = 970019) B970019
theorem B646699 : Blo 646304 646699 := bstep (se 1 (by rfl) ⟨485024, by rfl⟩ : syracuseStep 646699 = 970049) B970049
theorem B646711 : Blo 646304 646711 := bstep (se 1 (by rfl) ⟨485033, by rfl⟩ : syracuseStep 646711 = 970067) B970067
theorem B646731 : Blo 646304 646731 := bstep (se 1 (by rfl) ⟨485048, by rfl⟩ : syracuseStep 646731 = 970097) B970097
theorem B974411 : Blo 646304 974411 := bstep (se 1 (by rfl) ⟨730808, by rfl⟩ : syracuseStep 974411 = 1461617) B1461617
theorem B646743 : Blo 646304 646743 := bstep (se 1 (by rfl) ⟨485057, by rfl⟩ : syracuseStep 646743 = 970115) B970115
theorem B974423 : Blo 646304 974423 := bstep (se 1 (by rfl) ⟨730817, by rfl⟩ : syracuseStep 974423 = 1461635) B1461635
theorem B646763 : Blo 646304 646763 := bstep (se 1 (by rfl) ⟨485072, by rfl⟩ : syracuseStep 646763 = 970145) B970145
theorem B646775 : Blo 646304 646775 := bstep (se 1 (by rfl) ⟨485081, by rfl⟩ : syracuseStep 646775 = 970163) B970163
theorem B646795 : Blo 646304 646795 := bstep (se 1 (by rfl) ⟨485096, by rfl⟩ : syracuseStep 646795 = 970193) B970193
theorem B646807 : Blo 646304 646807 := bstep (se 1 (by rfl) ⟨485105, by rfl⟩ : syracuseStep 646807 = 970211) B970211
theorem B974489 : Blo 646304 974489 := bstep (se 2 (by rfl) ⟨365433, by rfl⟩ : syracuseStep 974489 = 730867) B730867
theorem B646827 : Blo 646304 646827 := bstep (se 1 (by rfl) ⟨485120, by rfl⟩ : syracuseStep 646827 = 970241) B970241
theorem B646839 : Blo 646304 646839 := bstep (se 1 (by rfl) ⟨485129, by rfl⟩ : syracuseStep 646839 = 970259) B970259
theorem B2186945 : Blo 646304 2186945 := bstep (se 2 (by rfl) ⟨820104, by rfl⟩ : syracuseStep 2186945 = 1640209) B1640209
theorem B646859 : Blo 646304 646859 := bstep (se 1 (by rfl) ⟨485144, by rfl⟩ : syracuseStep 646859 = 970289) B970289
theorem B646871 : Blo 646304 646871 := bstep (se 1 (by rfl) ⟨485153, by rfl⟩ : syracuseStep 646871 = 970307) B970307
theorem B646891 : Blo 646304 646891 := bstep (se 1 (by rfl) ⟨485168, by rfl⟩ : syracuseStep 646891 = 970337) B970337
theorem B646903 : Blo 646304 646903 := bstep (se 1 (by rfl) ⟨485177, by rfl⟩ : syracuseStep 646903 = 970355) B970355
theorem B7364357 : Blo 646304 7364357 := bstep (se 4 (by rfl) ⟨690408, by rfl⟩ : syracuseStep 7364357 = 1380817) B1380817
theorem B646923 : Blo 646304 646923 := bstep (se 1 (by rfl) ⟨485192, by rfl⟩ : syracuseStep 646923 = 970385) B970385
theorem B974603 : Blo 646304 974603 := bstep (se 1 (by rfl) ⟨730952, by rfl⟩ : syracuseStep 974603 = 1461905) B1461905
theorem B646935 : Blo 646304 646935 := bstep (se 1 (by rfl) ⟨485201, by rfl⟩ : syracuseStep 646935 = 970403) B970403
theorem B974615 : Blo 646304 974615 := bstep (se 1 (by rfl) ⟨730961, by rfl⟩ : syracuseStep 974615 = 1461923) B1461923
theorem B646955 : Blo 646304 646955 := bstep (se 1 (by rfl) ⟨485216, by rfl⟩ : syracuseStep 646955 = 970433) B970433
theorem B3989293 : Blo 646304 3989293 := bstep (se 3 (by rfl) ⟨747992, by rfl⟩ : syracuseStep 3989293 = 1495985) B1495985
theorem B646967 : Blo 646304 646967 := bstep (se 1 (by rfl) ⟨485225, by rfl⟩ : syracuseStep 646967 = 970451) B970451
theorem B646987 : Blo 646304 646987 := bstep (se 1 (by rfl) ⟨485240, by rfl⟩ : syracuseStep 646987 = 970481) B970481
theorem B646999 : Blo 646304 646999 := bstep (se 1 (by rfl) ⟨485249, by rfl⟩ : syracuseStep 646999 = 970499) B970499
theorem B974681 : Blo 646304 974681 := bstep (se 2 (by rfl) ⟨365505, by rfl⟩ : syracuseStep 974681 = 731011) B731011
theorem B647019 : Blo 646304 647019 := bstep (se 1 (by rfl) ⟨485264, by rfl⟩ : syracuseStep 647019 = 970529) B970529
theorem B647031 : Blo 646304 647031 := bstep (se 1 (by rfl) ⟨485273, by rfl⟩ : syracuseStep 647031 = 970547) B970547
theorem B647051 : Blo 646304 647051 := bstep (se 1 (by rfl) ⟨485288, by rfl⟩ : syracuseStep 647051 = 970577) B970577
theorem B647063 : Blo 646304 647063 := bstep (se 1 (by rfl) ⟨485297, by rfl⟩ : syracuseStep 647063 = 970595) B970595
theorem B1171351 : Blo 646304 1171351 := bstep (se 1 (by rfl) ⟨878513, by rfl⟩ : syracuseStep 1171351 = 1757027) B1757027
theorem B647083 : Blo 646304 647083 := bstep (se 1 (by rfl) ⟨485312, by rfl⟩ : syracuseStep 647083 = 970625) B970625
theorem B33611699 : Blo 646304 33611699 := bstep (se 1 (by rfl) ⟨25208774, by rfl⟩ : syracuseStep 33611699 = 50417549) B50417549
theorem B647095 : Blo 646304 647095 := bstep (se 1 (by rfl) ⟨485321, by rfl⟩ : syracuseStep 647095 = 970643) B970643
theorem B647115 : Blo 646304 647115 := bstep (se 1 (by rfl) ⟨485336, by rfl⟩ : syracuseStep 647115 = 970673) B970673
theorem B974795 : Blo 646304 974795 := bstep (se 1 (by rfl) ⟨731096, by rfl⟩ : syracuseStep 974795 = 1462193) B1462193
theorem B647127 : Blo 646304 647127 := bstep (se 1 (by rfl) ⟨485345, by rfl⟩ : syracuseStep 647127 = 970691) B970691
theorem B974807 : Blo 646304 974807 := bstep (se 1 (by rfl) ⟨731105, by rfl⟩ : syracuseStep 974807 = 1462211) B1462211
theorem B647147 : Blo 646304 647147 := bstep (se 1 (by rfl) ⟨485360, by rfl⟩ : syracuseStep 647147 = 970721) B970721
theorem B647159 : Blo 646304 647159 := bstep (se 1 (by rfl) ⟨485369, by rfl⟩ : syracuseStep 647159 = 970739) B970739
theorem B647179 : Blo 646304 647179 := bstep (se 1 (by rfl) ⟨485384, by rfl⟩ : syracuseStep 647179 = 970769) B970769
theorem B647191 : Blo 646304 647191 := bstep (se 1 (by rfl) ⟨485393, by rfl⟩ : syracuseStep 647191 = 970787) B970787
theorem B974873 : Blo 646304 974873 := bstep (se 2 (by rfl) ⟨365577, by rfl⟩ : syracuseStep 974873 = 731155) B731155
theorem B647211 : Blo 646304 647211 := bstep (se 1 (by rfl) ⟨485408, by rfl⟩ : syracuseStep 647211 = 970817) B970817
theorem B647223 : Blo 646304 647223 := bstep (se 1 (by rfl) ⟨485417, by rfl⟩ : syracuseStep 647223 = 970835) B970835
theorem B647243 : Blo 646304 647243 := bstep (se 1 (by rfl) ⟨485432, by rfl⟩ : syracuseStep 647243 = 970865) B970865
theorem B647255 : Blo 646304 647255 := bstep (se 1 (by rfl) ⟨485441, by rfl⟩ : syracuseStep 647255 = 970883) B970883
theorem B647275 : Blo 646304 647275 := bstep (se 1 (by rfl) ⟨485456, by rfl⟩ : syracuseStep 647275 = 970913) B970913
theorem B647287 : Blo 646304 647287 := bstep (se 1 (by rfl) ⟨485465, by rfl⟩ : syracuseStep 647287 = 970931) B970931
theorem B647307 : Blo 646304 647307 := bstep (se 1 (by rfl) ⟨485480, by rfl⟩ : syracuseStep 647307 = 970961) B970961
theorem B974987 : Blo 646304 974987 := bstep (se 1 (by rfl) ⟨731240, by rfl⟩ : syracuseStep 974987 = 1462481) B1462481
theorem B647319 : Blo 646304 647319 := bstep (se 1 (by rfl) ⟨485489, by rfl⟩ : syracuseStep 647319 = 970979) B970979
theorem B974999 : Blo 646304 974999 := bstep (se 1 (by rfl) ⟨731249, by rfl⟩ : syracuseStep 974999 = 1462499) B1462499
theorem B647339 : Blo 646304 647339 := bstep (se 1 (by rfl) ⟨485504, by rfl⟩ : syracuseStep 647339 = 971009) B971009
theorem B647351 : Blo 646304 647351 := bstep (se 1 (by rfl) ⟨485513, by rfl⟩ : syracuseStep 647351 = 971027) B971027
theorem B647371 : Blo 646304 647371 := bstep (se 1 (by rfl) ⟨485528, by rfl⟩ : syracuseStep 647371 = 971057) B971057
theorem B647383 : Blo 646304 647383 := bstep (se 1 (by rfl) ⟨485537, by rfl⟩ : syracuseStep 647383 = 971075) B971075
theorem B975065 : Blo 646304 975065 := bstep (se 2 (by rfl) ⟨365649, by rfl⟩ : syracuseStep 975065 = 731299) B731299
theorem B2187485 : Blo 646304 2187485 := bstep (se 3 (by rfl) ⟨410153, by rfl⟩ : syracuseStep 2187485 = 820307) B820307
theorem B647403 : Blo 646304 647403 := bstep (se 1 (by rfl) ⟨485552, by rfl⟩ : syracuseStep 647403 = 971105) B971105
theorem B647415 : Blo 646304 647415 := bstep (se 1 (by rfl) ⟨485561, by rfl⟩ : syracuseStep 647415 = 971123) B971123
theorem B647435 : Blo 646304 647435 := bstep (se 1 (by rfl) ⟨485576, by rfl⟩ : syracuseStep 647435 = 971153) B971153
theorem B647447 : Blo 646304 647447 := bstep (se 1 (by rfl) ⟨485585, by rfl⟩ : syracuseStep 647447 = 971171) B971171
theorem B1040663 : Blo 646304 1040663 := bstep (se 1 (by rfl) ⟨780497, by rfl⟩ : syracuseStep 1040663 = 1560995) B1560995
theorem B647467 : Blo 646304 647467 := bstep (se 1 (by rfl) ⟨485600, by rfl⟩ : syracuseStep 647467 = 971201) B971201
theorem B647479 : Blo 646304 647479 := bstep (se 1 (by rfl) ⟨485609, by rfl⟩ : syracuseStep 647479 = 971219) B971219
theorem B647499 : Blo 646304 647499 := bstep (se 1 (by rfl) ⟨485624, by rfl⟩ : syracuseStep 647499 = 971249) B971249
theorem B975179 : Blo 646304 975179 := bstep (se 1 (by rfl) ⟨731384, by rfl⟩ : syracuseStep 975179 = 1462769) B1462769
theorem B647511 : Blo 646304 647511 := bstep (se 1 (by rfl) ⟨485633, by rfl⟩ : syracuseStep 647511 = 971267) B971267
theorem B975191 : Blo 646304 975191 := bstep (se 1 (by rfl) ⟨731393, by rfl⟩ : syracuseStep 975191 = 1462787) B1462787
theorem B647531 : Blo 646304 647531 := bstep (se 1 (by rfl) ⟨485648, by rfl⟩ : syracuseStep 647531 = 971297) B971297
theorem B647543 : Blo 646304 647543 := bstep (se 1 (by rfl) ⟨485657, by rfl⟩ : syracuseStep 647543 = 971315) B971315
theorem B647563 : Blo 646304 647563 := bstep (se 1 (by rfl) ⟨485672, by rfl⟩ : syracuseStep 647563 = 971345) B971345
theorem B647575 : Blo 646304 647575 := bstep (se 1 (by rfl) ⟨485681, by rfl⟩ : syracuseStep 647575 = 971363) B971363
theorem B975257 : Blo 646304 975257 := bstep (se 2 (by rfl) ⟨365721, by rfl⟩ : syracuseStep 975257 = 731443) B731443
theorem B647595 : Blo 646304 647595 := bstep (se 1 (by rfl) ⟨485696, by rfl⟩ : syracuseStep 647595 = 971393) B971393
theorem B647607 : Blo 646304 647607 := bstep (se 1 (by rfl) ⟨485705, by rfl⟩ : syracuseStep 647607 = 971411) B971411
theorem B647627 : Blo 646304 647627 := bstep (se 1 (by rfl) ⟨485720, by rfl⟩ : syracuseStep 647627 = 971441) B971441
theorem B647639 : Blo 646304 647639 := bstep (se 1 (by rfl) ⟨485729, by rfl⟩ : syracuseStep 647639 = 971459) B971459
theorem B647659 : Blo 646304 647659 := bstep (se 1 (by rfl) ⟨485744, by rfl⟩ : syracuseStep 647659 = 971489) B971489
theorem B647671 : Blo 646304 647671 := bstep (se 1 (by rfl) ⟨485753, by rfl⟩ : syracuseStep 647671 = 971507) B971507
theorem B4940293 : Blo 646304 4940293 := bstep (se 4 (by rfl) ⟨463152, by rfl⟩ : syracuseStep 4940293 = 926305) B926305
theorem B647691 : Blo 646304 647691 := bstep (se 1 (by rfl) ⟨485768, by rfl⟩ : syracuseStep 647691 = 971537) B971537
theorem B975371 : Blo 646304 975371 := bstep (se 1 (by rfl) ⟨731528, by rfl⟩ : syracuseStep 975371 = 1463057) B1463057
theorem B647703 : Blo 646304 647703 := bstep (se 1 (by rfl) ⟨485777, by rfl⟩ : syracuseStep 647703 = 971555) B971555
theorem B975383 : Blo 646304 975383 := bstep (se 1 (by rfl) ⟨731537, by rfl⟩ : syracuseStep 975383 = 1463075) B1463075
theorem B647723 : Blo 646304 647723 := bstep (se 1 (by rfl) ⟨485792, by rfl⟩ : syracuseStep 647723 = 971585) B971585
theorem B647735 : Blo 646304 647735 := bstep (se 1 (by rfl) ⟨485801, by rfl⟩ : syracuseStep 647735 = 971603) B971603
theorem B647755 : Blo 646304 647755 := bstep (se 1 (by rfl) ⟨485816, by rfl⟩ : syracuseStep 647755 = 971633) B971633
theorem B647767 : Blo 646304 647767 := bstep (se 1 (by rfl) ⟨485825, by rfl⟩ : syracuseStep 647767 = 971651) B971651
theorem B975449 : Blo 646304 975449 := bstep (se 2 (by rfl) ⟨365793, by rfl⟩ : syracuseStep 975449 = 731587) B731587
theorem B10543709 : Blo 646304 10543709 := bstep (se 3 (by rfl) ⟨1976945, by rfl⟩ : syracuseStep 10543709 = 3953891) B3953891
theorem B647787 : Blo 646304 647787 := bstep (se 1 (by rfl) ⟨485840, by rfl⟩ : syracuseStep 647787 = 971681) B971681
theorem B647799 : Blo 646304 647799 := bstep (se 1 (by rfl) ⟨485849, by rfl⟩ : syracuseStep 647799 = 971699) B971699
theorem B647819 : Blo 646304 647819 := bstep (se 1 (by rfl) ⟨485864, by rfl⟩ : syracuseStep 647819 = 971729) B971729
theorem B647831 : Blo 646304 647831 := bstep (se 1 (by rfl) ⟨485873, by rfl⟩ : syracuseStep 647831 = 971747) B971747
theorem B647851 : Blo 646304 647851 := bstep (se 1 (by rfl) ⟨485888, by rfl⟩ : syracuseStep 647851 = 971777) B971777
theorem B647863 : Blo 646304 647863 := bstep (se 1 (by rfl) ⟨485897, by rfl⟩ : syracuseStep 647863 = 971795) B971795
theorem B647883 : Blo 646304 647883 := bstep (se 1 (by rfl) ⟨485912, by rfl⟩ : syracuseStep 647883 = 971825) B971825
theorem B647895 : Blo 646304 647895 := bstep (se 1 (by rfl) ⟨485921, by rfl⟩ : syracuseStep 647895 = 971843) B971843
theorem B647915 : Blo 646304 647915 := bstep (se 1 (by rfl) ⟨485936, by rfl⟩ : syracuseStep 647915 = 971873) B971873
theorem B647927 : Blo 646304 647927 := bstep (se 1 (by rfl) ⟨485945, by rfl⟩ : syracuseStep 647927 = 971891) B971891
theorem B647947 : Blo 646304 647947 := bstep (se 1 (by rfl) ⟨485960, by rfl⟩ : syracuseStep 647947 = 971921) B971921
theorem B647959 : Blo 646304 647959 := bstep (se 1 (by rfl) ⟨485969, by rfl⟩ : syracuseStep 647959 = 971939) B971939
theorem B647979 : Blo 646304 647979 := bstep (se 1 (by rfl) ⟨485984, by rfl⟩ : syracuseStep 647979 = 971969) B971969
theorem B647991 : Blo 646304 647991 := bstep (se 1 (by rfl) ⟨485993, by rfl⟩ : syracuseStep 647991 = 971987) B971987
theorem B648011 : Blo 646304 648011 := bstep (se 1 (by rfl) ⟨486008, by rfl⟩ : syracuseStep 648011 = 972017) B972017
theorem B648023 : Blo 646304 648023 := bstep (se 1 (by rfl) ⟨486017, by rfl⟩ : syracuseStep 648023 = 972035) B972035
theorem B648043 : Blo 646304 648043 := bstep (se 1 (by rfl) ⟨486032, by rfl⟩ : syracuseStep 648043 = 972065) B972065
theorem B648055 : Blo 646304 648055 := bstep (se 1 (by rfl) ⟨486041, by rfl⟩ : syracuseStep 648055 = 972083) B972083
theorem B648075 : Blo 646304 648075 := bstep (se 1 (by rfl) ⟨486056, by rfl⟩ : syracuseStep 648075 = 972113) B972113
theorem B648087 : Blo 646304 648087 := bstep (se 1 (by rfl) ⟨486065, by rfl⟩ : syracuseStep 648087 = 972131) B972131
theorem B648107 : Blo 646304 648107 := bstep (se 1 (by rfl) ⟨486080, by rfl⟩ : syracuseStep 648107 = 972161) B972161
theorem B8283059 : Blo 646304 8283059 := bstep (se 1 (by rfl) ⟨6212294, by rfl⟩ : syracuseStep 8283059 = 12424589) B12424589
theorem B648119 : Blo 646304 648119 := bstep (se 1 (by rfl) ⟨486089, by rfl⟩ : syracuseStep 648119 = 972179) B972179
theorem B648139 : Blo 646304 648139 := bstep (se 1 (by rfl) ⟨486104, by rfl⟩ : syracuseStep 648139 = 972209) B972209
theorem B648151 : Blo 646304 648151 := bstep (se 1 (by rfl) ⟨486113, by rfl⟩ : syracuseStep 648151 = 972227) B972227
theorem B648171 : Blo 646304 648171 := bstep (se 1 (by rfl) ⟨486128, by rfl⟩ : syracuseStep 648171 = 972257) B972257
theorem B648183 : Blo 646304 648183 := bstep (se 1 (by rfl) ⟨486137, by rfl⟩ : syracuseStep 648183 = 972275) B972275
theorem B648203 : Blo 646304 648203 := bstep (se 1 (by rfl) ⟨486152, by rfl⟩ : syracuseStep 648203 = 972305) B972305
theorem B1041419 : Blo 646304 1041419 := bstep (se 1 (by rfl) ⟨781064, by rfl⟩ : syracuseStep 1041419 = 1562129) B1562129
theorem B648215 : Blo 646304 648215 := bstep (se 1 (by rfl) ⟨486161, by rfl⟩ : syracuseStep 648215 = 972323) B972323
theorem B648235 : Blo 646304 648235 := bstep (se 1 (by rfl) ⟨486176, by rfl⟩ : syracuseStep 648235 = 972353) B972353
theorem B648247 : Blo 646304 648247 := bstep (se 1 (by rfl) ⟨486185, by rfl⟩ : syracuseStep 648247 = 972371) B972371
theorem B648267 : Blo 646304 648267 := bstep (se 1 (by rfl) ⟨486200, by rfl⟩ : syracuseStep 648267 = 972401) B972401
theorem B648279 : Blo 646304 648279 := bstep (se 1 (by rfl) ⟨486209, by rfl⟩ : syracuseStep 648279 = 972419) B972419
theorem B648299 : Blo 646304 648299 := bstep (se 1 (by rfl) ⟨486224, by rfl⟩ : syracuseStep 648299 = 972449) B972449
theorem B648311 : Blo 646304 648311 := bstep (se 1 (by rfl) ⟨486233, by rfl⟩ : syracuseStep 648311 = 972467) B972467
theorem B648331 : Blo 646304 648331 := bstep (se 1 (by rfl) ⟨486248, by rfl⟩ : syracuseStep 648331 = 972497) B972497
theorem B648343 : Blo 646304 648343 := bstep (se 1 (by rfl) ⟨486257, by rfl⟩ : syracuseStep 648343 = 972515) B972515
theorem B648363 : Blo 646304 648363 := bstep (se 1 (by rfl) ⟨486272, by rfl⟩ : syracuseStep 648363 = 972545) B972545
theorem B648375 : Blo 646304 648375 := bstep (se 1 (by rfl) ⟨486281, by rfl⟩ : syracuseStep 648375 = 972563) B972563
theorem B648395 : Blo 646304 648395 := bstep (se 1 (by rfl) ⟨486296, by rfl⟩ : syracuseStep 648395 = 972593) B972593
theorem B648407 : Blo 646304 648407 := bstep (se 1 (by rfl) ⟨486305, by rfl⟩ : syracuseStep 648407 = 972611) B972611
theorem B648427 : Blo 646304 648427 := bstep (se 1 (by rfl) ⟨486320, by rfl⟩ : syracuseStep 648427 = 972641) B972641
theorem B648439 : Blo 646304 648439 := bstep (se 1 (by rfl) ⟨486329, by rfl⟩ : syracuseStep 648439 = 972659) B972659
theorem B648459 : Blo 646304 648459 := bstep (se 1 (by rfl) ⟨486344, by rfl⟩ : syracuseStep 648459 = 972689) B972689
theorem B648471 : Blo 646304 648471 := bstep (se 1 (by rfl) ⟨486353, by rfl⟩ : syracuseStep 648471 = 972707) B972707
theorem B648491 : Blo 646304 648491 := bstep (se 1 (by rfl) ⟨486368, by rfl⟩ : syracuseStep 648491 = 972737) B972737
theorem B648503 : Blo 646304 648503 := bstep (se 1 (by rfl) ⟨486377, by rfl⟩ : syracuseStep 648503 = 972755) B972755
theorem B2188619 : Blo 646304 2188619 := bstep (se 1 (by rfl) ⟨1641464, by rfl⟩ : syracuseStep 2188619 = 3282929) B3282929
theorem B648523 : Blo 646304 648523 := bstep (se 1 (by rfl) ⟨486392, by rfl⟩ : syracuseStep 648523 = 972785) B972785
theorem B648535 : Blo 646304 648535 := bstep (se 1 (by rfl) ⟨486401, by rfl⟩ : syracuseStep 648535 = 972803) B972803
theorem B648555 : Blo 646304 648555 := bstep (se 1 (by rfl) ⟨486416, by rfl⟩ : syracuseStep 648555 = 972833) B972833
theorem B648567 : Blo 646304 648567 := bstep (se 1 (by rfl) ⟨486425, by rfl⟩ : syracuseStep 648567 = 972851) B972851
theorem B648587 : Blo 646304 648587 := bstep (se 1 (by rfl) ⟨486440, by rfl⟩ : syracuseStep 648587 = 972881) B972881
theorem B31450517 : Blo 646304 31450517 := bstep (se 6 (by rfl) ⟨737121, by rfl⟩ : syracuseStep 31450517 = 1474243) B1474243
theorem B648599 : Blo 646304 648599 := bstep (se 1 (by rfl) ⟨486449, by rfl⟩ : syracuseStep 648599 = 972899) B972899
theorem B648619 : Blo 646304 648619 := bstep (se 1 (by rfl) ⟨486464, by rfl⟩ : syracuseStep 648619 = 972929) B972929
theorem B648631 : Blo 646304 648631 := bstep (se 1 (by rfl) ⟨486473, by rfl⟩ : syracuseStep 648631 = 972947) B972947
theorem B648651 : Blo 646304 648651 := bstep (se 1 (by rfl) ⟨486488, by rfl⟩ : syracuseStep 648651 = 972977) B972977
theorem B648663 : Blo 646304 648663 := bstep (se 1 (by rfl) ⟨486497, by rfl⟩ : syracuseStep 648663 = 972995) B972995
theorem B648683 : Blo 646304 648683 := bstep (se 1 (by rfl) ⟨486512, by rfl⟩ : syracuseStep 648683 = 973025) B973025
theorem B648695 : Blo 646304 648695 := bstep (se 1 (by rfl) ⟨486521, by rfl⟩ : syracuseStep 648695 = 973043) B973043
theorem B648715 : Blo 646304 648715 := bstep (se 1 (by rfl) ⟨486536, by rfl⟩ : syracuseStep 648715 = 973073) B973073
theorem B648727 : Blo 646304 648727 := bstep (se 1 (by rfl) ⟨486545, by rfl⟩ : syracuseStep 648727 = 973091) B973091
theorem B648747 : Blo 646304 648747 := bstep (se 1 (by rfl) ⟨486560, by rfl⟩ : syracuseStep 648747 = 973121) B973121
theorem B648759 : Blo 646304 648759 := bstep (se 1 (by rfl) ⟨486569, by rfl⟩ : syracuseStep 648759 = 973139) B973139
theorem B648779 : Blo 646304 648779 := bstep (se 1 (by rfl) ⟨486584, by rfl⟩ : syracuseStep 648779 = 973169) B973169
theorem B648791 : Blo 646304 648791 := bstep (se 1 (by rfl) ⟨486593, by rfl⟩ : syracuseStep 648791 = 973187) B973187
theorem B2188889 : Blo 646304 2188889 := bstep (se 2 (by rfl) ⟨820833, by rfl⟩ : syracuseStep 2188889 = 1641667) B1641667
theorem B648811 : Blo 646304 648811 := bstep (se 1 (by rfl) ⟨486608, by rfl⟩ : syracuseStep 648811 = 973217) B973217
theorem B648823 : Blo 646304 648823 := bstep (se 1 (by rfl) ⟨486617, by rfl⟩ : syracuseStep 648823 = 973235) B973235
theorem B648843 : Blo 646304 648843 := bstep (se 1 (by rfl) ⟨486632, by rfl⟩ : syracuseStep 648843 = 973265) B973265
theorem B648855 : Blo 646304 648855 := bstep (se 1 (by rfl) ⟨486641, by rfl⟩ : syracuseStep 648855 = 973283) B973283
theorem B648875 : Blo 646304 648875 := bstep (se 1 (by rfl) ⟨486656, by rfl⟩ : syracuseStep 648875 = 973313) B973313
theorem B648887 : Blo 646304 648887 := bstep (se 1 (by rfl) ⟨486665, by rfl⟩ : syracuseStep 648887 = 973331) B973331
theorem B648907 : Blo 646304 648907 := bstep (se 1 (by rfl) ⟨486680, by rfl⟩ : syracuseStep 648907 = 973361) B973361
theorem B648919 : Blo 646304 648919 := bstep (se 1 (by rfl) ⟨486689, by rfl⟩ : syracuseStep 648919 = 973379) B973379
theorem B648939 : Blo 646304 648939 := bstep (se 1 (by rfl) ⟨486704, by rfl⟩ : syracuseStep 648939 = 973409) B973409
theorem B648951 : Blo 646304 648951 := bstep (se 1 (by rfl) ⟨486713, by rfl⟩ : syracuseStep 648951 = 973427) B973427
theorem B648971 : Blo 646304 648971 := bstep (se 1 (by rfl) ⟨486728, by rfl⟩ : syracuseStep 648971 = 973457) B973457
theorem B648983 : Blo 646304 648983 := bstep (se 1 (by rfl) ⟨486737, by rfl⟩ : syracuseStep 648983 = 973475) B973475
theorem B649003 : Blo 646304 649003 := bstep (se 1 (by rfl) ⟨486752, by rfl⟩ : syracuseStep 649003 = 973505) B973505
theorem B649015 : Blo 646304 649015 := bstep (se 1 (by rfl) ⟨486761, by rfl⟩ : syracuseStep 649015 = 973523) B973523
theorem B649035 : Blo 646304 649035 := bstep (se 1 (by rfl) ⟨486776, by rfl⟩ : syracuseStep 649035 = 973553) B973553
theorem B649047 : Blo 646304 649047 := bstep (se 1 (by rfl) ⟨486785, by rfl⟩ : syracuseStep 649047 = 973571) B973571
theorem B649067 : Blo 646304 649067 := bstep (se 1 (by rfl) ⟨486800, by rfl⟩ : syracuseStep 649067 = 973601) B973601
theorem B649079 : Blo 646304 649079 := bstep (se 1 (by rfl) ⟨486809, by rfl⟩ : syracuseStep 649079 = 973619) B973619
theorem B649099 : Blo 646304 649099 := bstep (se 1 (by rfl) ⟨486824, by rfl⟩ : syracuseStep 649099 = 973649) B973649
theorem B649111 : Blo 646304 649111 := bstep (se 1 (by rfl) ⟨486833, by rfl⟩ : syracuseStep 649111 = 973667) B973667
theorem B649131 : Blo 646304 649131 := bstep (se 1 (by rfl) ⟨486848, by rfl⟩ : syracuseStep 649131 = 973697) B973697
theorem B4220851 : Blo 646304 4220851 := bstep (se 1 (by rfl) ⟨3165638, by rfl⟩ : syracuseStep 4220851 = 6331277) B6331277
theorem B649143 : Blo 646304 649143 := bstep (se 1 (by rfl) ⟨486857, by rfl⟩ : syracuseStep 649143 = 973715) B973715
theorem B649163 : Blo 646304 649163 := bstep (se 1 (by rfl) ⟨486872, by rfl⟩ : syracuseStep 649163 = 973745) B973745
theorem B649175 : Blo 646304 649175 := bstep (se 1 (by rfl) ⟨486881, by rfl⟩ : syracuseStep 649175 = 973763) B973763
theorem B649195 : Blo 646304 649195 := bstep (se 1 (by rfl) ⟨486896, by rfl⟩ : syracuseStep 649195 = 973793) B973793
theorem B649207 : Blo 646304 649207 := bstep (se 1 (by rfl) ⟨486905, by rfl⟩ : syracuseStep 649207 = 973811) B973811
theorem B649227 : Blo 646304 649227 := bstep (se 1 (by rfl) ⟨486920, by rfl⟩ : syracuseStep 649227 = 973841) B973841
theorem B649239 : Blo 646304 649239 := bstep (se 1 (by rfl) ⟨486929, by rfl⟩ : syracuseStep 649239 = 973859) B973859
theorem B649259 : Blo 646304 649259 := bstep (se 1 (by rfl) ⟨486944, by rfl⟩ : syracuseStep 649259 = 973889) B973889
theorem B5335085 : Blo 646304 5335085 := bstep (se 3 (by rfl) ⟨1000328, by rfl⟩ : syracuseStep 5335085 = 2000657) B2000657
theorem B1402931 : Blo 646304 1402931 := bstep (se 1 (by rfl) ⟨1052198, by rfl⟩ : syracuseStep 1402931 = 2104397) B2104397
theorem B649271 : Blo 646304 649271 := bstep (se 1 (by rfl) ⟨486953, by rfl⟩ : syracuseStep 649271 = 973907) B973907
theorem B649291 : Blo 646304 649291 := bstep (se 1 (by rfl) ⟨486968, by rfl⟩ : syracuseStep 649291 = 973937) B973937
theorem B649303 : Blo 646304 649303 := bstep (se 1 (by rfl) ⟨486977, by rfl⟩ : syracuseStep 649303 = 973955) B973955
theorem B649323 : Blo 646304 649323 := bstep (se 1 (by rfl) ⟨486992, by rfl⟩ : syracuseStep 649323 = 973985) B973985
theorem B649335 : Blo 646304 649335 := bstep (se 1 (by rfl) ⟨487001, by rfl⟩ : syracuseStep 649335 = 974003) B974003
theorem B649355 : Blo 646304 649355 := bstep (se 1 (by rfl) ⟨487016, by rfl⟩ : syracuseStep 649355 = 974033) B974033
theorem B649367 : Blo 646304 649367 := bstep (se 1 (by rfl) ⟨487025, by rfl⟩ : syracuseStep 649367 = 974051) B974051
theorem B780439 : Blo 646304 780439 := bstep (se 1 (by rfl) ⟨585329, by rfl⟩ : syracuseStep 780439 = 1170659) B1170659
theorem B649387 : Blo 646304 649387 := bstep (se 1 (by rfl) ⟨487040, by rfl⟩ : syracuseStep 649387 = 974081) B974081
theorem B649399 : Blo 646304 649399 := bstep (se 1 (by rfl) ⟨487049, by rfl⟩ : syracuseStep 649399 = 974099) B974099
theorem B649419 : Blo 646304 649419 := bstep (se 1 (by rfl) ⟨487064, by rfl⟩ : syracuseStep 649419 = 974129) B974129
theorem B649431 : Blo 646304 649431 := bstep (se 1 (by rfl) ⟨487073, by rfl⟩ : syracuseStep 649431 = 974147) B974147
theorem B649451 : Blo 646304 649451 := bstep (se 1 (by rfl) ⟨487088, by rfl⟩ : syracuseStep 649451 = 974177) B974177
theorem B649463 : Blo 646304 649463 := bstep (se 1 (by rfl) ⟨487097, by rfl⟩ : syracuseStep 649463 = 974195) B974195
theorem B649483 : Blo 646304 649483 := bstep (se 1 (by rfl) ⟨487112, by rfl⟩ : syracuseStep 649483 = 974225) B974225
theorem B2189591 : Blo 646304 2189591 := bstep (se 1 (by rfl) ⟨1642193, by rfl⟩ : syracuseStep 2189591 = 3284387) B3284387
theorem B649495 : Blo 646304 649495 := bstep (se 1 (by rfl) ⟨487121, by rfl⟩ : syracuseStep 649495 = 974243) B974243
theorem B649515 : Blo 646304 649515 := bstep (se 1 (by rfl) ⟨487136, by rfl⟩ : syracuseStep 649515 = 974273) B974273
theorem B3696941 : Blo 646304 3696941 := bstep (se 3 (by rfl) ⟨693176, by rfl⟩ : syracuseStep 3696941 = 1386353) B1386353
theorem B649527 : Blo 646304 649527 := bstep (se 1 (by rfl) ⟨487145, by rfl⟩ : syracuseStep 649527 = 974291) B974291
theorem B649547 : Blo 646304 649547 := bstep (se 1 (by rfl) ⟨487160, by rfl⟩ : syracuseStep 649547 = 974321) B974321
theorem B649559 : Blo 646304 649559 := bstep (se 1 (by rfl) ⟨487169, by rfl⟩ : syracuseStep 649559 = 974339) B974339
theorem B649579 : Blo 646304 649579 := bstep (se 1 (by rfl) ⟨487184, by rfl⟩ : syracuseStep 649579 = 974369) B974369
theorem B649591 : Blo 646304 649591 := bstep (se 1 (by rfl) ⟨487193, by rfl⟩ : syracuseStep 649591 = 974387) B974387
theorem B4155779 : Blo 646304 4155779 := bstep (se 1 (by rfl) ⟨3116834, by rfl⟩ : syracuseStep 4155779 = 6233669) B6233669
theorem B649611 : Blo 646304 649611 := bstep (se 1 (by rfl) ⟨487208, by rfl⟩ : syracuseStep 649611 = 974417) B974417
theorem B649623 : Blo 646304 649623 := bstep (se 1 (by rfl) ⟨487217, by rfl⟩ : syracuseStep 649623 = 974435) B974435
theorem B649643 : Blo 646304 649643 := bstep (se 1 (by rfl) ⟨487232, by rfl⟩ : syracuseStep 649643 = 974465) B974465
theorem B649655 : Blo 646304 649655 := bstep (se 1 (by rfl) ⟨487241, by rfl⟩ : syracuseStep 649655 = 974483) B974483
theorem B1403329 : Blo 646304 1403329 := bstep (se 2 (by rfl) ⟨526248, by rfl⟩ : syracuseStep 1403329 = 1052497) B1052497
theorem B649675 : Blo 646304 649675 := bstep (se 1 (by rfl) ⟨487256, by rfl⟩ : syracuseStep 649675 = 974513) B974513
theorem B649687 : Blo 646304 649687 := bstep (se 1 (by rfl) ⟨487265, by rfl⟩ : syracuseStep 649687 = 974531) B974531
theorem B649707 : Blo 646304 649707 := bstep (se 1 (by rfl) ⟨487280, by rfl⟩ : syracuseStep 649707 = 974561) B974561
theorem B649719 : Blo 646304 649719 := bstep (se 1 (by rfl) ⟨487289, by rfl⟩ : syracuseStep 649719 = 974579) B974579
theorem B649739 : Blo 646304 649739 := bstep (se 1 (by rfl) ⟨487304, by rfl⟩ : syracuseStep 649739 = 974609) B974609
theorem B649751 : Blo 646304 649751 := bstep (se 1 (by rfl) ⟨487313, by rfl⟩ : syracuseStep 649751 = 974627) B974627
theorem B649771 : Blo 646304 649771 := bstep (se 1 (by rfl) ⟨487328, by rfl⟩ : syracuseStep 649771 = 974657) B974657
theorem B649783 : Blo 646304 649783 := bstep (se 1 (by rfl) ⟨487337, by rfl⟩ : syracuseStep 649783 = 974675) B974675
theorem B649803 : Blo 646304 649803 := bstep (se 1 (by rfl) ⟨487352, by rfl⟩ : syracuseStep 649803 = 974705) B974705
theorem B649815 : Blo 646304 649815 := bstep (se 1 (by rfl) ⟨487361, by rfl⟩ : syracuseStep 649815 = 974723) B974723
theorem B649835 : Blo 646304 649835 := bstep (se 1 (by rfl) ⟨487376, by rfl⟩ : syracuseStep 649835 = 974753) B974753
theorem B649847 : Blo 646304 649847 := bstep (se 1 (by rfl) ⟨487385, by rfl⟩ : syracuseStep 649847 = 974771) B974771
theorem B649867 : Blo 646304 649867 := bstep (se 1 (by rfl) ⟨487400, by rfl⟩ : syracuseStep 649867 = 974801) B974801
theorem B649879 : Blo 646304 649879 := bstep (se 1 (by rfl) ⟨487409, by rfl⟩ : syracuseStep 649879 = 974819) B974819
theorem B649899 : Blo 646304 649899 := bstep (se 1 (by rfl) ⟨487424, by rfl⟩ : syracuseStep 649899 = 974849) B974849
theorem B649911 : Blo 646304 649911 := bstep (se 1 (by rfl) ⟨487433, by rfl⟩ : syracuseStep 649911 = 974867) B974867
theorem B649931 : Blo 646304 649931 := bstep (se 1 (by rfl) ⟨487448, by rfl⟩ : syracuseStep 649931 = 974897) B974897
theorem B649943 : Blo 646304 649943 := bstep (se 1 (by rfl) ⟨487457, by rfl⟩ : syracuseStep 649943 = 974915) B974915
theorem B649963 : Blo 646304 649963 := bstep (se 1 (by rfl) ⟨487472, by rfl⟩ : syracuseStep 649963 = 974945) B974945
theorem B649975 : Blo 646304 649975 := bstep (se 1 (by rfl) ⟨487481, by rfl⟩ : syracuseStep 649975 = 974963) B974963
theorem B649995 : Blo 646304 649995 := bstep (se 1 (by rfl) ⟨487496, by rfl⟩ : syracuseStep 649995 = 974993) B974993
theorem B650007 : Blo 646304 650007 := bstep (se 1 (by rfl) ⟨487505, by rfl⟩ : syracuseStep 650007 = 975011) B975011
theorem B650027 : Blo 646304 650027 := bstep (se 1 (by rfl) ⟨487520, by rfl⟩ : syracuseStep 650027 = 975041) B975041
theorem B2190131 : Blo 646304 2190131 := bstep (se 1 (by rfl) ⟨1642598, by rfl⟩ : syracuseStep 2190131 = 3285197) B3285197
theorem B650039 : Blo 646304 650039 := bstep (se 1 (by rfl) ⟨487529, by rfl⟩ : syracuseStep 650039 = 975059) B975059
theorem B650059 : Blo 646304 650059 := bstep (se 1 (by rfl) ⟨487544, by rfl⟩ : syracuseStep 650059 = 975089) B975089
theorem B650071 : Blo 646304 650071 := bstep (se 1 (by rfl) ⟨487553, by rfl⟩ : syracuseStep 650071 = 975107) B975107
theorem B650091 : Blo 646304 650091 := bstep (se 1 (by rfl) ⟨487568, by rfl⟩ : syracuseStep 650091 = 975137) B975137
theorem B650103 : Blo 646304 650103 := bstep (se 1 (by rfl) ⟨487577, by rfl⟩ : syracuseStep 650103 = 975155) B975155
theorem B4746115 : Blo 646304 4746115 := bstep (se 1 (by rfl) ⟨3559586, by rfl⟩ : syracuseStep 4746115 = 7119173) B7119173
theorem B650123 : Blo 646304 650123 := bstep (se 1 (by rfl) ⟨487592, by rfl⟩ : syracuseStep 650123 = 975185) B975185
theorem B650135 : Blo 646304 650135 := bstep (se 1 (by rfl) ⟨487601, by rfl⟩ : syracuseStep 650135 = 975203) B975203
theorem B650155 : Blo 646304 650155 := bstep (se 1 (by rfl) ⟨487616, by rfl⟩ : syracuseStep 650155 = 975233) B975233
theorem B650167 : Blo 646304 650167 := bstep (se 1 (by rfl) ⟨487625, by rfl⟩ : syracuseStep 650167 = 975251) B975251
theorem B650187 : Blo 646304 650187 := bstep (se 1 (by rfl) ⟨487640, by rfl⟩ : syracuseStep 650187 = 975281) B975281
theorem B650199 : Blo 646304 650199 := bstep (se 1 (by rfl) ⟨487649, by rfl⟩ : syracuseStep 650199 = 975299) B975299
theorem B650219 : Blo 646304 650219 := bstep (se 1 (by rfl) ⟨487664, by rfl⟩ : syracuseStep 650219 = 975329) B975329
theorem B650231 : Blo 646304 650231 := bstep (se 1 (by rfl) ⟨487673, by rfl⟩ : syracuseStep 650231 = 975347) B975347
theorem B650251 : Blo 646304 650251 := bstep (se 1 (by rfl) ⟨487688, by rfl⟩ : syracuseStep 650251 = 975377) B975377
theorem B650263 : Blo 646304 650263 := bstep (se 1 (by rfl) ⟨487697, by rfl⟩ : syracuseStep 650263 = 975395) B975395
theorem B650283 : Blo 646304 650283 := bstep (se 1 (by rfl) ⟨487712, by rfl⟩ : syracuseStep 650283 = 975425) B975425
theorem B650295 : Blo 646304 650295 := bstep (se 1 (by rfl) ⟨487721, by rfl⟩ : syracuseStep 650295 = 975443) B975443
theorem B2190401 : Blo 646304 2190401 := bstep (se 2 (by rfl) ⟨821400, by rfl⟩ : syracuseStep 2190401 = 1642801) B1642801
theorem B15199301 : Blo 646304 15199301 := bstep (se 4 (by rfl) ⟨1424934, by rfl⟩ : syracuseStep 15199301 = 2849869) B2849869
theorem B10546307 : Blo 646304 10546307 := bstep (se 1 (by rfl) ⟨7909730, by rfl⟩ : syracuseStep 10546307 = 15819461) B15819461
theorem B3272237 : Blo 646304 3272237 := bstep (se 3 (by rfl) ⟨613544, by rfl⟩ : syracuseStep 3272237 = 1227089) B1227089
theorem B2190941 : Blo 646304 2190941 := bstep (se 3 (by rfl) ⟨410801, by rfl⟩ : syracuseStep 2190941 = 821603) B821603
theorem B1797835 : Blo 646304 1797835 := bstep (se 1 (by rfl) ⟨1348376, by rfl⟩ : syracuseStep 1797835 = 2696753) B2696753
theorem B6222257 : Blo 646304 6222257 := bstep (se 2 (by rfl) ⟨2333346, by rfl⟩ : syracuseStep 6222257 = 4666693) B4666693
theorem B2814401 : Blo 646304 2814401 := bstep (se 2 (by rfl) ⟨1055400, by rfl⟩ : syracuseStep 2814401 = 2110801) B2110801
theorem B1667659 : Blo 646304 1667659 := bstep (se 1 (by rfl) ⟨1250744, by rfl⟩ : syracuseStep 1667659 = 2501489) B2501489
theorem B2454209 : Blo 646304 2454209 := bstep (se 2 (by rfl) ⟨920328, by rfl⟩ : syracuseStep 2454209 = 1840657) B1840657
theorem B2192075 : Blo 646304 2192075 := bstep (se 1 (by rfl) ⟨1644056, by rfl⟩ : syracuseStep 2192075 = 3288113) B3288113
theorem B2192345 : Blo 646304 2192345 := bstep (se 2 (by rfl) ⟨822129, by rfl⟩ : syracuseStep 2192345 = 1644259) B1644259
theorem B3208627 : Blo 646304 3208627 := bstep (se 1 (by rfl) ⟨2406470, by rfl⟩ : syracuseStep 3208627 = 4812941) B4812941
theorem B2193047 : Blo 646304 2193047 := bstep (se 1 (by rfl) ⟨1644785, by rfl⟩ : syracuseStep 2193047 = 3289571) B3289571
theorem B3799057 : Blo 646304 3799057 := bstep (se 2 (by rfl) ⟨1424646, by rfl⟩ : syracuseStep 3799057 = 2849293) B2849293
theorem B2455697 : Blo 646304 2455697 := bstep (se 2 (by rfl) ⟨920886, by rfl⟩ : syracuseStep 2455697 = 1841773) B1841773
theorem B2193587 : Blo 646304 2193587 := bstep (se 1 (by rfl) ⟨1645190, by rfl⟩ : syracuseStep 2193587 = 3290381) B3290381
theorem B1636787 : Blo 646304 1636787 := bstep (se 1 (by rfl) ⟨1227590, by rfl⟩ : syracuseStep 1636787 = 2455181) B2455181
theorem B2193857 : Blo 646304 2193857 := bstep (se 2 (by rfl) ⟨822696, by rfl⟩ : syracuseStep 2193857 = 1645393) B1645393
theorem B2488897 : Blo 646304 2488897 := bstep (se 2 (by rfl) ⟨933336, by rfl⟩ : syracuseStep 2488897 = 1866673) B1866673
theorem B3734081 : Blo 646304 3734081 := bstep (se 2 (by rfl) ⟨1400280, by rfl⟩ : syracuseStep 3734081 = 2800561) B2800561
theorem B2456153 : Blo 646304 2456153 := bstep (se 2 (by rfl) ⟨921057, by rfl⟩ : syracuseStep 2456153 = 1842115) B1842115
theorem B1637081 : Blo 646304 1637081 := bstep (se 2 (by rfl) ⟨613905, by rfl⟩ : syracuseStep 1637081 = 1227811) B1227811
theorem B2030359 : Blo 646304 2030359 := bstep (se 1 (by rfl) ⟨1522769, by rfl⟩ : syracuseStep 2030359 = 3045539) B3045539
theorem B2456365 : Blo 646304 2456365 := bstep (se 3 (by rfl) ⟨460568, by rfl⟩ : syracuseStep 2456365 = 921137) B921137
theorem B2194397 : Blo 646304 2194397 := bstep (se 3 (by rfl) ⟨411449, by rfl⟩ : syracuseStep 2194397 = 822899) B822899
theorem B8879179 : Blo 646304 8879179 := bstep (se 1 (by rfl) ⟨6659384, by rfl⟩ : syracuseStep 8879179 = 13318769) B13318769
theorem B2456669 : Blo 646304 2456669 := bstep (se 3 (by rfl) ⟨460625, by rfl⟩ : syracuseStep 2456669 = 921251) B921251
theorem B3112067 : Blo 646304 3112067 := bstep (se 1 (by rfl) ⟨2334050, by rfl⟩ : syracuseStep 3112067 = 4668101) B4668101
theorem B2620619 : Blo 646304 2620619 := bstep (se 1 (by rfl) ⟨1965464, by rfl⟩ : syracuseStep 2620619 = 3930929) B3930929
theorem B1244441 : Blo 646304 1244441 := bstep (se 2 (by rfl) ⟨466665, by rfl⟩ : syracuseStep 1244441 = 933331) B933331
theorem B3276125 : Blo 646304 3276125 := bstep (se 3 (by rfl) ⟨614273, by rfl⟩ : syracuseStep 3276125 = 1228547) B1228547
theorem B818839 : Blo 646304 818839 := bstep (se 1 (by rfl) ⟨614129, by rfl⟩ : syracuseStep 818839 = 1228259) B1228259
theorem B3931949 : Blo 646304 3931949 := bstep (se 3 (by rfl) ⟨737240, by rfl⟩ : syracuseStep 3931949 = 1474481) B1474481
theorem B1474355 : Blo 646304 1474355 := bstep (se 1 (by rfl) ⟨1105766, by rfl⟩ : syracuseStep 1474355 = 2211533) B2211533
theorem B4685633 : Blo 646304 4685633 := bstep (se 2 (by rfl) ⟨1757112, by rfl⟩ : syracuseStep 4685633 = 3514225) B3514225
theorem B1245079 : Blo 646304 1245079 := bstep (se 1 (by rfl) ⟨933809, by rfl⟩ : syracuseStep 1245079 = 1867619) B1867619
theorem B2457611 : Blo 646304 2457611 := bstep (se 1 (by rfl) ⟨1843208, by rfl⟩ : syracuseStep 2457611 = 3686417) B3686417
theorem B819335 : Blo 646304 819335 := bstep (se 1 (by rfl) ⟨614501, by rfl⟩ : syracuseStep 819335 = 1229003) B1229003
theorem B3277259 : Blo 646304 3277259 := bstep (se 1 (by rfl) ⟨2457944, by rfl⟩ : syracuseStep 3277259 = 4915889) B4915889
theorem B1638913 : Blo 646304 1638913 := bstep (se 2 (by rfl) ⟨614592, by rfl⟩ : syracuseStep 1638913 = 1229185) B1229185
theorem B1311275 : Blo 646304 1311275 := bstep (se 1 (by rfl) ⟨983456, by rfl⟩ : syracuseStep 1311275 = 1966913) B1966913
theorem B6587057 : Blo 646304 6587057 := bstep (se 2 (by rfl) ⟨2470146, by rfl⟩ : syracuseStep 6587057 = 4940293) B4940293
theorem B15958745 : Blo 646304 15958745 := bstep (se 2 (by rfl) ⟨5984529, by rfl⟩ : syracuseStep 15958745 = 11969059) B11969059
theorem B3277583 : Blo 646304 3277583 := bstep (se 1 (by rfl) ⟨2458187, by rfl⟩ : syracuseStep 3277583 = 4916375) B4916375
theorem B819983 : Blo 646304 819983 := bstep (se 1 (by rfl) ⟨614987, by rfl⟩ : syracuseStep 819983 = 1229975) B1229975
theorem B984071 : Blo 646304 984071 := bstep (se 1 (by rfl) ⟨738053, by rfl⟩ : syracuseStep 984071 = 1476107) B1476107
theorem B1639511 : Blo 646304 1639511 := bstep (se 1 (by rfl) ⟨1229633, by rfl⟩ : syracuseStep 1639511 = 2459267) B2459267
theorem B1639723 : Blo 646304 1639723 := bstep (se 1 (by rfl) ⟨1229792, by rfl⟩ : syracuseStep 1639723 = 2459585) B2459585
theorem B1639865 : Blo 646304 1639865 := bstep (se 2 (by rfl) ⟨614949, by rfl⟩ : syracuseStep 1639865 = 1229899) B1229899
theorem B14976971 : Blo 646304 14976971 := bstep (se 1 (by rfl) ⟨11232728, by rfl⟩ : syracuseStep 14976971 = 22465457) B22465457
theorem B1574927 : Blo 646304 1574927 := bstep (se 1 (by rfl) ⟨1181195, by rfl⟩ : syracuseStep 1574927 = 2362391) B2362391
theorem B2459767 : Blo 646304 2459767 := bstep (se 1 (by rfl) ⟨1844825, by rfl⟩ : syracuseStep 2459767 = 3689651) B3689651
theorem B1968275 : Blo 646304 1968275 := bstep (se 1 (by rfl) ⟨1476206, by rfl⟩ : syracuseStep 1968275 = 2952413) B2952413
theorem B3279041 : Blo 646304 3279041 := bstep (se 2 (by rfl) ⟨1229640, by rfl⟩ : syracuseStep 3279041 = 2459281) B2459281
theorem B690439 : Blo 646304 690439 := bstep (se 1 (by rfl) ⟨517829, by rfl⟩ : syracuseStep 690439 = 1035659) B1035659
theorem B1870091 : Blo 646304 1870091 := bstep (se 1 (by rfl) ⟨1402568, by rfl⟩ : syracuseStep 1870091 = 2805137) B2805137
theorem B1640857 : Blo 646304 1640857 := bstep (se 2 (by rfl) ⟨615321, by rfl⟩ : syracuseStep 1640857 = 1230643) B1230643
theorem B1477163 : Blo 646304 1477163 := bstep (se 1 (by rfl) ⟨1107872, by rfl⟩ : syracuseStep 1477163 = 2215745) B2215745
theorem B1641019 : Blo 646304 1641019 := bstep (se 1 (by rfl) ⟨1230764, by rfl⟩ : syracuseStep 1641019 = 2461529) B2461529
theorem B1641161 : Blo 646304 1641161 := bstep (se 2 (by rfl) ⟨615435, by rfl⟩ : syracuseStep 1641161 = 1230871) B1230871
theorem B986041 : Blo 646304 986041 := bstep (se 2 (by rfl) ⟨369765, by rfl⟩ : syracuseStep 986041 = 739531) B739531
theorem B1641505 : Blo 646304 1641505 := bstep (se 2 (by rfl) ⟨615564, by rfl⟩ : syracuseStep 1641505 = 1231129) B1231129
theorem B691259 : Blo 646304 691259 := bstep (se 1 (by rfl) ⟨518444, by rfl⟩ : syracuseStep 691259 = 1036889) B1036889
theorem B2460739 : Blo 646304 2460739 := bstep (se 1 (by rfl) ⟨1845554, by rfl⟩ : syracuseStep 2460739 = 3691109) B3691109
theorem B3935405 : Blo 646304 3935405 := bstep (se 3 (by rfl) ⟨737888, by rfl⟩ : syracuseStep 3935405 = 1475777) B1475777
theorem B1871105 : Blo 646304 1871105 := bstep (se 2 (by rfl) ⟨701664, by rfl⟩ : syracuseStep 1871105 = 1403329) B1403329
theorem B2461043 : Blo 646304 2461043 := bstep (se 1 (by rfl) ⟨1845782, by rfl⟩ : syracuseStep 2461043 = 3691565) B3691565
theorem B3280337 : Blo 646304 3280337 := bstep (se 2 (by rfl) ⟨1230126, by rfl⟩ : syracuseStep 3280337 = 2460253) B2460253
theorem B1642103 : Blo 646304 1642103 := bstep (se 1 (by rfl) ⟨1231577, by rfl⟩ : syracuseStep 1642103 = 2463155) B2463155
theorem B921223 : Blo 646304 921223 := bstep (se 1 (by rfl) ⟨690917, by rfl⟩ : syracuseStep 921223 = 1381835) B1381835
theorem B822955 : Blo 646304 822955 := bstep (se 1 (by rfl) ⟨617216, by rfl⟩ : syracuseStep 822955 = 1234433) B1234433
theorem B2461499 : Blo 646304 2461499 := bstep (se 1 (by rfl) ⟨1846124, by rfl⟩ : syracuseStep 2461499 = 3692249) B3692249
theorem B6328153 : Blo 646304 6328153 := bstep (se 2 (by rfl) ⟨2373057, by rfl⟩ : syracuseStep 6328153 = 4746115) B4746115
theorem B987209 : Blo 646304 987209 := bstep (se 2 (by rfl) ⟨370203, by rfl⟩ : syracuseStep 987209 = 740407) B740407
theorem B3117143 : Blo 646304 3117143 := bstep (se 1 (by rfl) ⟨2337857, by rfl⟩ : syracuseStep 3117143 = 4675715) B4675715
theorem B2461985 : Blo 646304 2461985 := bstep (se 2 (by rfl) ⟨923244, by rfl⟩ : syracuseStep 2461985 = 1846489) B1846489
theorem B922043 : Blo 646304 922043 := bstep (se 1 (by rfl) ⟨691532, by rfl⟩ : syracuseStep 922043 = 1383065) B1383065
theorem B17994421 : Blo 646304 17994421 := bstep (se 5 (by rfl) ⟨843488, by rfl⟩ : syracuseStep 17994421 = 1686977) B1686977
theorem B1643399 : Blo 646304 1643399 := bstep (se 1 (by rfl) ⟨1232549, by rfl⟩ : syracuseStep 1643399 = 2465099) B2465099
theorem B2397113 : Blo 646304 2397113 := bstep (se 2 (by rfl) ⟨898917, by rfl⟩ : syracuseStep 2397113 = 1797835) B1797835
theorem B1643449 : Blo 646304 1643449 := bstep (se 2 (by rfl) ⟨616293, by rfl⟩ : syracuseStep 1643449 = 1232587) B1232587
theorem B922681 : Blo 646304 922681 := bstep (se 2 (by rfl) ⟨346005, by rfl⟩ : syracuseStep 922681 = 692011) B692011
theorem B2462957 : Blo 646304 2462957 := bstep (se 3 (by rfl) ⟨461804, by rfl⟩ : syracuseStep 2462957 = 923609) B923609
theorem B2495777 : Blo 646304 2495777 := bstep (se 2 (by rfl) ⟨935916, by rfl⟩ : syracuseStep 2495777 = 1871833) B1871833
theorem B3741149 : Blo 646304 3741149 := bstep (se 3 (by rfl) ⟨701465, by rfl⟩ : syracuseStep 3741149 = 1402931) B1402931
theorem B3282443 : Blo 646304 3282443 := bstep (se 1 (by rfl) ⟨2461832, by rfl⟩ : syracuseStep 3282443 = 4923665) B4923665
theorem B1644047 : Blo 646304 1644047 := bstep (se 1 (by rfl) ⟨1233035, by rfl⟩ : syracuseStep 1644047 = 2466071) B2466071
theorem B693775 : Blo 646304 693775 := bstep (se 1 (by rfl) ⟨520331, by rfl⟩ : syracuseStep 693775 = 1040663) B1040663
theorem B3282605 : Blo 646304 3282605 := bstep (se 3 (by rfl) ⟨615488, by rfl⟩ : syracuseStep 3282605 = 1230977) B1230977
theorem B1840907 : Blo 646304 1840907 := bstep (se 1 (by rfl) ⟨1380680, by rfl⟩ : syracuseStep 1840907 = 2761361) B2761361
theorem B1382177 : Blo 646304 1382177 := bstep (se 2 (by rfl) ⟨518316, by rfl⟩ : syracuseStep 1382177 = 1036633) B1036633
theorem B2955041 : Blo 646304 2955041 := bstep (se 2 (by rfl) ⟨1108140, by rfl⟩ : syracuseStep 2955041 = 2216281) B2216281
theorem B11802419 : Blo 646304 11802419 := bstep (se 1 (by rfl) ⟨8851814, by rfl⟩ : syracuseStep 11802419 = 17703629) B17703629
theorem B2463641 : Blo 646304 2463641 := bstep (se 2 (by rfl) ⟨923865, by rfl⟩ : syracuseStep 2463641 = 1847731) B1847731
theorem B694279 : Blo 646304 694279 := bstep (se 1 (by rfl) ⟨520709, by rfl⟩ : syracuseStep 694279 = 1041419) B1041419
theorem B2103383 : Blo 646304 2103383 := bstep (se 1 (by rfl) ⟨1577537, by rfl⟩ : syracuseStep 2103383 = 3155075) B3155075
theorem B1644745 : Blo 646304 1644745 := bstep (se 2 (by rfl) ⟨616779, by rfl⟩ : syracuseStep 1644745 = 1233559) B1233559
theorem B727303 : Blo 646304 727303 := bstep (se 1 (by rfl) ⟨545477, by rfl⟩ : syracuseStep 727303 = 1090955) B1090955
theorem B85104917 : Blo 646304 85104917 := bstep (se 6 (by rfl) ⟨1994646, by rfl⟩ : syracuseStep 85104917 = 3989293) B3989293
theorem B1644887 : Blo 646304 1644887 := bstep (se 1 (by rfl) ⟨1233665, by rfl⟩ : syracuseStep 1644887 = 2467331) B2467331
theorem B727483 : Blo 646304 727483 := bstep (se 1 (by rfl) ⟨545612, by rfl⟩ : syracuseStep 727483 = 1091225) B1091225
theorem B924167 : Blo 646304 924167 := bstep (se 1 (by rfl) ⟨693125, by rfl⟩ : syracuseStep 924167 = 1386251) B1386251
theorem B2333245 : Blo 646304 2333245 := bstep (se 3 (by rfl) ⟨437483, by rfl⟩ : syracuseStep 2333245 = 874967) B874967
theorem B1383227 : Blo 646304 1383227 := bstep (se 1 (by rfl) ⟨1037420, by rfl⟩ : syracuseStep 1383227 = 2074841) B2074841
theorem B924475 : Blo 646304 924475 := bstep (se 1 (by rfl) ⟨693356, by rfl⟩ : syracuseStep 924475 = 1386713) B1386713
theorem B1973053 : Blo 646304 1973053 := bstep (se 3 (by rfl) ⟨369947, by rfl⟩ : syracuseStep 1973053 = 739895) B739895
theorem B2464627 : Blo 646304 2464627 := bstep (se 1 (by rfl) ⟨1848470, by rfl⟩ : syracuseStep 2464627 = 3696941) B3696941
theorem B727951 : Blo 646304 727951 := bstep (se 1 (by rfl) ⟨545963, by rfl⟩ : syracuseStep 727951 = 1091927) B1091927
theorem B3284225 : Blo 646304 3284225 := bstep (se 2 (by rfl) ⟨1231584, by rfl⟩ : syracuseStep 3284225 = 2463169) B2463169
theorem B10132867 : Blo 646304 10132867 := bstep (se 1 (by rfl) ⟨7599650, by rfl⟩ : syracuseStep 10132867 = 15199301) B15199301
theorem B728455 : Blo 646304 728455 := bstep (se 1 (by rfl) ⟨546341, by rfl⟩ : syracuseStep 728455 = 1092683) B1092683
theorem B1383979 : Blo 646304 1383979 := bstep (se 1 (by rfl) ⟨1037984, by rfl⟩ : syracuseStep 1383979 = 2075969) B2075969
theorem B728635 : Blo 646304 728635 := bstep (se 1 (by rfl) ⟨546476, by rfl⟩ : syracuseStep 728635 = 1092953) B1092953
theorem B2629181 : Blo 646304 2629181 := bstep (se 3 (by rfl) ⟨492971, by rfl⟩ : syracuseStep 2629181 = 985943) B985943
theorem B1843003 : Blo 646304 1843003 := bstep (se 1 (by rfl) ⟨1382252, by rfl⟩ : syracuseStep 1843003 = 2764505) B2764505
theorem B5250905 : Blo 646304 5250905 := bstep (se 2 (by rfl) ⟨1969089, by rfl⟩ : syracuseStep 5250905 = 3938179) B3938179
theorem B925625 : Blo 646304 925625 := bstep (se 2 (by rfl) ⟨347109, by rfl⟩ : syracuseStep 925625 = 694219) B694219
theorem B729103 : Blo 646304 729103 := bstep (se 1 (by rfl) ⟨546827, by rfl⟩ : syracuseStep 729103 = 1093655) B1093655
theorem B3285035 : Blo 646304 3285035 := bstep (se 1 (by rfl) ⟨2463776, by rfl⟩ : syracuseStep 3285035 = 4927553) B4927553
theorem B1974539 : Blo 646304 1974539 := bstep (se 1 (by rfl) ⟨1480904, by rfl⟩ : syracuseStep 1974539 = 2961809) B2961809
theorem B1876267 : Blo 646304 1876267 := bstep (se 1 (by rfl) ⟨1407200, by rfl⟩ : syracuseStep 1876267 = 2814401) B2814401
theorem B8298845 : Blo 646304 8298845 := bstep (se 3 (by rfl) ⟨1556033, by rfl⟩ : syracuseStep 8298845 = 3112067) B3112067
theorem B729607 : Blo 646304 729607 := bstep (se 1 (by rfl) ⟨547205, by rfl⟩ : syracuseStep 729607 = 1094411) B1094411
theorem B1843847 : Blo 646304 1843847 := bstep (se 1 (by rfl) ⟨1382885, by rfl⟩ : syracuseStep 1843847 = 2765771) B2765771
theorem B729787 : Blo 646304 729787 := bstep (se 1 (by rfl) ⟨547340, by rfl⟩ : syracuseStep 729787 = 1094681) B1094681
theorem B3318509 : Blo 646304 3318509 := bstep (se 3 (by rfl) ⟨622220, by rfl⟩ : syracuseStep 3318509 = 1244441) B1244441
theorem B3318529 : Blo 646304 3318529 := bstep (se 2 (by rfl) ⟨1244448, by rfl⟩ : syracuseStep 3318529 = 2488897) B2488897
theorem B5251877 : Blo 646304 5251877 := bstep (se 4 (by rfl) ⟨492363, by rfl⟩ : syracuseStep 5251877 = 984727) B984727
theorem B1385363 : Blo 646304 1385363 := bstep (se 1 (by rfl) ⟨1039022, by rfl⟩ : syracuseStep 1385363 = 2078045) B2078045
theorem B2466845 : Blo 646304 2466845 := bstep (se 3 (by rfl) ⟨462533, by rfl⟩ : syracuseStep 2466845 = 925067) B925067
theorem B2761771 : Blo 646304 2761771 := bstep (se 1 (by rfl) ⟨2071328, by rfl⟩ : syracuseStep 2761771 = 4142657) B4142657
theorem B730255 : Blo 646304 730255 := bstep (se 1 (by rfl) ⟨547691, by rfl⟩ : syracuseStep 730255 = 1095383) B1095383
theorem B3286331 : Blo 646304 3286331 := bstep (se 1 (by rfl) ⟨2464748, by rfl⟩ : syracuseStep 3286331 = 4929497) B4929497
theorem B1844633 : Blo 646304 1844633 := bstep (se 2 (by rfl) ⟨691737, by rfl⟩ : syracuseStep 1844633 = 1383475) B1383475
theorem B11838905 : Blo 646304 11838905 := bstep (se 2 (by rfl) ⟨4439589, by rfl⟩ : syracuseStep 11838905 = 8879179) B8879179
theorem B3286493 : Blo 646304 3286493 := bstep (se 3 (by rfl) ⟨616217, by rfl⟩ : syracuseStep 3286493 = 1232435) B1232435
theorem B1091191 : Blo 646304 1091191 := bstep (se 1 (by rfl) ⟨818393, by rfl⟩ : syracuseStep 1091191 = 1636787) B1636787
theorem B730759 : Blo 646304 730759 := bstep (se 1 (by rfl) ⟨548069, by rfl⟩ : syracuseStep 730759 = 1096139) B1096139
theorem B2467529 : Blo 646304 2467529 := bstep (se 2 (by rfl) ⟨925323, by rfl⟩ : syracuseStep 2467529 = 1850647) B1850647
theorem B3286817 : Blo 646304 3286817 := bstep (se 2 (by rfl) ⟨1232556, by rfl⟩ : syracuseStep 3286817 = 2465113) B2465113
theorem B1091387 : Blo 646304 1091387 := bstep (se 1 (by rfl) ⟨818540, by rfl⟩ : syracuseStep 1091387 = 1637081) B1637081
theorem B730939 : Blo 646304 730939 := bstep (se 1 (by rfl) ⟨548204, by rfl⟩ : syracuseStep 730939 = 1096409) B1096409
theorem B6334469 : Blo 646304 6334469 := bstep (se 4 (by rfl) ⟨593856, by rfl⟩ : syracuseStep 6334469 = 1187713) B1187713
theorem B1845281 : Blo 646304 1845281 := bstep (se 2 (by rfl) ⟨691980, by rfl⟩ : syracuseStep 1845281 = 1383961) B1383961
theorem B1976363 : Blo 646304 1976363 := bstep (se 1 (by rfl) ⟨1482272, by rfl⟩ : syracuseStep 1976363 = 2964545) B2964545
theorem B1747079 : Blo 646304 1747079 := bstep (se 1 (by rfl) ⟨1310309, by rfl⟩ : syracuseStep 1747079 = 2620619) B2620619
theorem B1091785 : Blo 646304 1091785 := bstep (se 2 (by rfl) ⟨409419, by rfl⟩ : syracuseStep 1091785 = 818839) B818839
theorem B731407 : Blo 646304 731407 := bstep (se 1 (by rfl) ⟨548555, by rfl⟩ : syracuseStep 731407 = 1097111) B1097111
theorem B89631197 : Blo 646304 89631197 := bstep (se 3 (by rfl) ⟨16805849, by rfl⟩ : syracuseStep 89631197 = 33611699) B33611699
theorem B3123755 : Blo 646304 3123755 := bstep (se 1 (by rfl) ⟨2342816, by rfl⟩ : syracuseStep 3123755 = 4685633) B4685633
theorem B3287789 : Blo 646304 3287789 := bstep (se 3 (by rfl) ⟨616460, by rfl⟩ : syracuseStep 3287789 = 1232921) B1232921
theorem B1092487 : Blo 646304 1092487 := bstep (se 1 (by rfl) ⟨819365, by rfl⟩ : syracuseStep 1092487 = 1638731) B1638731
theorem B1846273 : Blo 646304 1846273 := bstep (se 2 (by rfl) ⟨692352, by rfl⟩ : syracuseStep 1846273 = 1384705) B1384705
theorem B31534595 : Blo 646304 31534595 := bstep (se 1 (by rfl) ⟨23650946, by rfl⟩ : syracuseStep 31534595 = 47301893) B47301893
theorem B1093135 : Blo 646304 1093135 := bstep (se 1 (by rfl) ⟨819851, by rfl⟩ : syracuseStep 1093135 = 1639703) B1639703
theorem B3288599 : Blo 646304 3288599 := bstep (se 1 (by rfl) ⟨2466449, by rfl⟩ : syracuseStep 3288599 = 4932899) B4932899
theorem B7384769 : Blo 646304 7384769 := bstep (se 2 (by rfl) ⟨2769288, by rfl⟩ : syracuseStep 7384769 = 5538577) B5538577
theorem B2764489 : Blo 646304 2764489 := bstep (se 2 (by rfl) ⟨1036683, by rfl⟩ : syracuseStep 2764489 = 2073367) B2073367
theorem B26619799 : Blo 646304 26619799 := bstep (se 1 (by rfl) ⟨19964849, by rfl⟩ : syracuseStep 26619799 = 39929699) B39929699
theorem B109555733 : Blo 646304 109555733 := bstep (se 6 (by rfl) ⟨2567712, by rfl⟩ : syracuseStep 109555733 = 5135425) B5135425
theorem B1093675 : Blo 646304 1093675 := bstep (se 1 (by rfl) ⟨820256, by rfl⟩ : syracuseStep 1093675 = 1640513) B1640513
theorem B1093817 : Blo 646304 1093817 := bstep (se 2 (by rfl) ⟨410181, by rfl⟩ : syracuseStep 1093817 = 820363) B820363
theorem B1454471 : Blo 646304 1454471 := bstep (se 1 (by rfl) ⟨1090853, by rfl⟩ : syracuseStep 1454471 = 2181707) B2181707
theorem B1454651 : Blo 646304 1454651 := bstep (se 1 (by rfl) ⟨1090988, by rfl⟩ : syracuseStep 1454651 = 2181977) B2181977
theorem B1454777 : Blo 646304 1454777 := bstep (se 2 (by rfl) ⟨545541, by rfl⟩ : syracuseStep 1454777 = 1091083) B1091083
theorem B1094519 : Blo 646304 1094519 := bstep (se 1 (by rfl) ⟨820889, by rfl⟩ : syracuseStep 1094519 = 1641779) B1641779
theorem B9974789 : Blo 646304 9974789 := bstep (se 4 (by rfl) ⟨935136, by rfl⟩ : syracuseStep 9974789 = 1870273) B1870273
theorem B1455119 : Blo 646304 1455119 := bstep (se 1 (by rfl) ⟨1091339, by rfl⟩ : syracuseStep 1455119 = 2182679) B2182679
theorem B1455137 : Blo 646304 1455137 := bstep (se 2 (by rfl) ⟨545676, by rfl⟩ : syracuseStep 1455137 = 1091353) B1091353
theorem B3683501 : Blo 646304 3683501 := bstep (se 3 (by rfl) ⟨690656, by rfl⟩ : syracuseStep 3683501 = 1381313) B1381313
theorem B1094971 : Blo 646304 1094971 := bstep (se 1 (by rfl) ⟨821228, by rfl⟩ : syracuseStep 1094971 = 1642457) B1642457
theorem B1455479 : Blo 646304 1455479 := bstep (se 1 (by rfl) ⟨1091609, by rfl⟩ : syracuseStep 1455479 = 2183219) B2183219
theorem B9352583 : Blo 646304 9352583 := bstep (se 1 (by rfl) ⟨7014437, by rfl⟩ : syracuseStep 9352583 = 14028875) B14028875
theorem B1095113 : Blo 646304 1095113 := bstep (se 2 (by rfl) ⟨410667, by rfl⟩ : syracuseStep 1095113 = 821335) B821335
theorem B2635217 : Blo 646304 2635217 := bstep (se 2 (by rfl) ⟨988206, by rfl⟩ : syracuseStep 2635217 = 1976413) B1976413
theorem B1455659 : Blo 646304 1455659 := bstep (se 1 (by rfl) ⟨1091744, by rfl⟩ : syracuseStep 1455659 = 2183489) B2183489
theorem B3847873 : Blo 646304 3847873 := bstep (se 2 (by rfl) ⟨1442952, by rfl⟩ : syracuseStep 3847873 = 2885905) B2885905
theorem B1849223 : Blo 646304 1849223 := bstep (se 1 (by rfl) ⟨1386917, by rfl⟩ : syracuseStep 1849223 = 2773835) B2773835
theorem B1456019 : Blo 646304 1456019 := bstep (se 1 (by rfl) ⟨1092014, by rfl⟩ : syracuseStep 1456019 = 2184029) B2184029
theorem B1456073 : Blo 646304 1456073 := bstep (se 2 (by rfl) ⟨546027, by rfl⟩ : syracuseStep 1456073 = 1092055) B1092055
theorem B1849405 : Blo 646304 1849405 := bstep (se 3 (by rfl) ⟨346763, by rfl⟩ : syracuseStep 1849405 = 693527) B693527
theorem B2275415 : Blo 646304 2275415 := bstep (se 1 (by rfl) ⟨1706561, by rfl⟩ : syracuseStep 2275415 = 3413123) B3413123
theorem B1849463 : Blo 646304 1849463 := bstep (se 1 (by rfl) ⟨1387097, by rfl⟩ : syracuseStep 1849463 = 2774195) B2774195
theorem B1095815 : Blo 646304 1095815 := bstep (se 1 (by rfl) ⟨821861, by rfl⟩ : syracuseStep 1095815 = 1643723) B1643723
theorem B1751339 : Blo 646304 1751339 := bstep (se 1 (by rfl) ⟨1313504, by rfl⟩ : syracuseStep 1751339 = 2627009) B2627009
theorem B1227143 : Blo 646304 1227143 := bstep (se 1 (by rfl) ⟨920357, by rfl⟩ : syracuseStep 1227143 = 1840715) B1840715
theorem B4143581 : Blo 646304 4143581 := bstep (se 3 (by rfl) ⟨776921, by rfl⟩ : syracuseStep 4143581 = 1553843) B1553843
theorem B3291677 : Blo 646304 3291677 := bstep (se 3 (by rfl) ⟨617189, by rfl⟩ : syracuseStep 3291677 = 1234379) B1234379
theorem B1456775 : Blo 646304 1456775 := bstep (se 1 (by rfl) ⟨1092581, by rfl⟩ : syracuseStep 1456775 = 2185163) B2185163
theorem B1096463 : Blo 646304 1096463 := bstep (se 1 (by rfl) ⟨822347, by rfl⟩ : syracuseStep 1096463 = 1644695) B1644695
theorem B1456955 : Blo 646304 1456955 := bstep (se 1 (by rfl) ⟨1092716, by rfl⟩ : syracuseStep 1456955 = 2185433) B2185433
theorem B1457081 : Blo 646304 1457081 := bstep (se 2 (by rfl) ⟨546405, by rfl⟩ : syracuseStep 1457081 = 1092811) B1092811
theorem B3292163 : Blo 646304 3292163 := bstep (se 1 (by rfl) ⟨2469122, by rfl⟩ : syracuseStep 3292163 = 4938245) B4938245
theorem B1850521 : Blo 646304 1850521 := bstep (se 2 (by rfl) ⟨693945, by rfl⟩ : syracuseStep 1850521 = 1387891) B1387891
theorem B1457423 : Blo 646304 1457423 := bstep (se 1 (by rfl) ⟨1093067, by rfl⟩ : syracuseStep 1457423 = 2186135) B2186135
theorem B60833045 : Blo 646304 60833045 := bstep (se 6 (by rfl) ⟨1425774, by rfl⟩ : syracuseStep 60833045 = 2851549) B2851549
theorem B1457441 : Blo 646304 1457441 := bstep (se 2 (by rfl) ⟨546540, by rfl⟩ : syracuseStep 1457441 = 1093081) B1093081
theorem B1097003 : Blo 646304 1097003 := bstep (se 1 (by rfl) ⟨822752, by rfl⟩ : syracuseStep 1097003 = 1645505) B1645505
theorem B1457783 : Blo 646304 1457783 := bstep (se 1 (by rfl) ⟨1093337, by rfl⟩ : syracuseStep 1457783 = 2186675) B2186675
theorem B1851137 : Blo 646304 1851137 := bstep (se 2 (by rfl) ⟨694176, by rfl⟩ : syracuseStep 1851137 = 1388353) B1388353
theorem B1457963 : Blo 646304 1457963 := bstep (se 1 (by rfl) ⟨1093472, by rfl⟩ : syracuseStep 1457963 = 2186945) B2186945
theorem B1228745 : Blo 646304 1228745 := bstep (se 2 (by rfl) ⟨460779, by rfl⟩ : syracuseStep 1228745 = 921559) B921559
theorem B1458323 : Blo 646304 1458323 := bstep (se 1 (by rfl) ⟨1093742, by rfl⟩ : syracuseStep 1458323 = 2187485) B2187485
theorem B1458377 : Blo 646304 1458377 := bstep (se 2 (by rfl) ⟨546891, by rfl⟩ : syracuseStep 1458377 = 1093783) B1093783
theorem B1556795 : Blo 646304 1556795 := bstep (se 1 (by rfl) ⟨1167596, by rfl⟩ : syracuseStep 1556795 = 2335193) B2335193
theorem B2081159 : Blo 646304 2081159 := bstep (se 1 (by rfl) ⟨1560869, by rfl⟩ : syracuseStep 2081159 = 3121739) B3121739
theorem B7029139 : Blo 646304 7029139 := bstep (se 1 (by rfl) ⟨5271854, by rfl⟩ : syracuseStep 7029139 = 10543709) B10543709
theorem B5522039 : Blo 646304 5522039 := bstep (se 1 (by rfl) ⟨4141529, by rfl⟩ : syracuseStep 5522039 = 8283059) B8283059
theorem B1459079 : Blo 646304 1459079 := bstep (se 1 (by rfl) ⟨1094309, by rfl⟩ : syracuseStep 1459079 = 2188619) B2188619
theorem B1459259 : Blo 646304 1459259 := bstep (se 1 (by rfl) ⟨1094444, by rfl⟩ : syracuseStep 1459259 = 2188889) B2188889
theorem B1754171 : Blo 646304 1754171 := bstep (se 1 (by rfl) ⟨1315628, by rfl⟩ : syracuseStep 1754171 = 2631257) B2631257
theorem B1459385 : Blo 646304 1459385 := bstep (se 2 (by rfl) ⟨547269, by rfl⟩ : syracuseStep 1459385 = 1094539) B1094539
theorem B1754369 : Blo 646304 1754369 := bstep (se 2 (by rfl) ⟨657888, by rfl⟩ : syracuseStep 1754369 = 1315777) B1315777
theorem B3556723 : Blo 646304 3556723 := bstep (se 1 (by rfl) ⟨2667542, by rfl⟩ : syracuseStep 3556723 = 5335085) B5335085
theorem B56935811 : Blo 646304 56935811 := bstep (se 1 (by rfl) ⟨42701858, by rfl⟩ : syracuseStep 56935811 = 85403717) B85403717
theorem B1459727 : Blo 646304 1459727 := bstep (se 1 (by rfl) ⟨1094795, by rfl⟩ : syracuseStep 1459727 = 2189591) B2189591
theorem B1459745 : Blo 646304 1459745 := bstep (se 2 (by rfl) ⟨547404, by rfl⟩ : syracuseStep 1459745 = 1094809) B1094809
theorem B2770519 : Blo 646304 2770519 := bstep (se 1 (by rfl) ⟨2077889, by rfl⟩ : syracuseStep 2770519 = 4155779) B4155779
theorem B3688193 : Blo 646304 3688193 := bstep (se 2 (by rfl) ⟨1383072, by rfl⟩ : syracuseStep 3688193 = 2766145) B2766145
theorem B1558283 : Blo 646304 1558283 := bstep (se 1 (by rfl) ⟨1168712, by rfl⟩ : syracuseStep 1558283 = 2337425) B2337425
theorem B1460087 : Blo 646304 1460087 := bstep (se 1 (by rfl) ⟨1095065, by rfl⟩ : syracuseStep 1460087 = 2190131) B2190131
theorem B1230727 : Blo 646304 1230727 := bstep (se 1 (by rfl) ⟨923045, by rfl⟩ : syracuseStep 1230727 = 1846091) B1846091
theorem B4278169 : Blo 646304 4278169 := bstep (se 2 (by rfl) ⟨1604313, by rfl⟩ : syracuseStep 4278169 = 3208627) B3208627
theorem B1460267 : Blo 646304 1460267 := bstep (se 1 (by rfl) ⟨1095200, by rfl⟩ : syracuseStep 1460267 = 2190401) B2190401
theorem B7030871 : Blo 646304 7030871 := bstep (se 1 (by rfl) ⟨5273153, by rfl⟩ : syracuseStep 7030871 = 10546307) B10546307
theorem B28067957 : Blo 646304 28067957 := bstep (se 5 (by rfl) ⟨1315685, by rfl⟩ : syracuseStep 28067957 = 2631371) B2631371
theorem B3688649 : Blo 646304 3688649 := bstep (se 2 (by rfl) ⟨1383243, by rfl⟩ : syracuseStep 3688649 = 2766487) B2766487
theorem B1558871 : Blo 646304 1558871 := bstep (se 1 (by rfl) ⟨1169153, by rfl⟩ : syracuseStep 1558871 = 2338307) B2338307
theorem B2181491 : Blo 646304 2181491 := bstep (se 1 (by rfl) ⟨1636118, by rfl⟩ : syracuseStep 2181491 = 3272237) B3272237
theorem B1460627 : Blo 646304 1460627 := bstep (se 1 (by rfl) ⟨1095470, by rfl⟩ : syracuseStep 1460627 = 2190941) B2190941
theorem B1460681 : Blo 646304 1460681 := bstep (se 2 (by rfl) ⟨547755, by rfl⟩ : syracuseStep 1460681 = 1095511) B1095511
theorem B1559225 : Blo 646304 1559225 := bstep (se 2 (by rfl) ⟨584709, by rfl⟩ : syracuseStep 1559225 = 1169419) B1169419
theorem B5065409 : Blo 646304 5065409 := bstep (se 2 (by rfl) ⟨1899528, by rfl⟩ : syracuseStep 5065409 = 3799057) B3799057
theorem B3001033 : Blo 646304 3001033 := bstep (se 2 (by rfl) ⟨1125387, by rfl⟩ : syracuseStep 3001033 = 2250775) B2250775
theorem B969479 : Blo 646304 969479 := bstep (se 1 (by rfl) ⟨727109, by rfl⟩ : syracuseStep 969479 = 1454219) B1454219
theorem B969515 : Blo 646304 969515 := bstep (se 1 (by rfl) ⟨727136, by rfl⟩ : syracuseStep 969515 = 1454273) B1454273
theorem B969545 : Blo 646304 969545 := bstep (se 2 (by rfl) ⟨363579, by rfl⟩ : syracuseStep 969545 = 727159) B727159
theorem B969659 : Blo 646304 969659 := bstep (se 1 (by rfl) ⟨727244, by rfl⟩ : syracuseStep 969659 = 1454489) B1454489
theorem B4148171 : Blo 646304 4148171 := bstep (se 1 (by rfl) ⟨3111128, by rfl⟩ : syracuseStep 4148171 = 6222257) B6222257
theorem B2771921 : Blo 646304 2771921 := bstep (se 2 (by rfl) ⟨1039470, by rfl⟩ : syracuseStep 2771921 = 2078941) B2078941
theorem B969719 : Blo 646304 969719 := bstep (se 1 (by rfl) ⟨727289, by rfl⟩ : syracuseStep 969719 = 1454579) B1454579
theorem B969743 : Blo 646304 969743 := bstep (se 1 (by rfl) ⟨727307, by rfl⟩ : syracuseStep 969743 = 1454615) B1454615
theorem B969785 : Blo 646304 969785 := bstep (se 2 (by rfl) ⟨363669, by rfl⟩ : syracuseStep 969785 = 727339) B727339
theorem B969863 : Blo 646304 969863 := bstep (se 1 (by rfl) ⟨727397, by rfl⟩ : syracuseStep 969863 = 1454795) B1454795
theorem B1461383 : Blo 646304 1461383 := bstep (se 1 (by rfl) ⟨1096037, by rfl⟩ : syracuseStep 1461383 = 2192075) B2192075
theorem B969899 : Blo 646304 969899 := bstep (se 1 (by rfl) ⟨727424, by rfl⟩ : syracuseStep 969899 = 1454849) B1454849
theorem B969929 : Blo 646304 969929 := bstep (se 2 (by rfl) ⟨363723, by rfl⟩ : syracuseStep 969929 = 727447) B727447
theorem B970043 : Blo 646304 970043 := bstep (se 1 (by rfl) ⟨727532, by rfl⟩ : syracuseStep 970043 = 1455065) B1455065
theorem B1166651 : Blo 646304 1166651 := bstep (se 1 (by rfl) ⟨874988, by rfl⟩ : syracuseStep 1166651 = 1749977) B1749977
theorem B1461563 : Blo 646304 1461563 := bstep (se 1 (by rfl) ⟨1096172, by rfl⟩ : syracuseStep 1461563 = 2192345) B2192345
theorem B970103 : Blo 646304 970103 := bstep (se 1 (by rfl) ⟨727577, by rfl⟩ : syracuseStep 970103 = 1455155) B1455155
theorem B970127 : Blo 646304 970127 := bstep (se 1 (by rfl) ⟨727595, by rfl⟩ : syracuseStep 970127 = 1455191) B1455191
theorem B970169 : Blo 646304 970169 := bstep (se 2 (by rfl) ⟨363813, by rfl⟩ : syracuseStep 970169 = 727627) B727627
theorem B1461689 : Blo 646304 1461689 := bstep (se 2 (by rfl) ⟨548133, by rfl⟩ : syracuseStep 1461689 = 1096267) B1096267
theorem B1232329 : Blo 646304 1232329 := bstep (se 2 (by rfl) ⟨462123, by rfl⟩ : syracuseStep 1232329 = 924247) B924247
theorem B970247 : Blo 646304 970247 := bstep (se 1 (by rfl) ⟨727685, by rfl⟩ : syracuseStep 970247 = 1455371) B1455371
theorem B970283 : Blo 646304 970283 := bstep (se 1 (by rfl) ⟨727712, by rfl⟩ : syracuseStep 970283 = 1455425) B1455425
theorem B970313 : Blo 646304 970313 := bstep (se 2 (by rfl) ⟨363867, by rfl⟩ : syracuseStep 970313 = 727735) B727735
theorem B970427 : Blo 646304 970427 := bstep (se 1 (by rfl) ⟨727820, by rfl⟩ : syracuseStep 970427 = 1455641) B1455641
theorem B2707145 : Blo 646304 2707145 := bstep (se 2 (by rfl) ⟨1015179, by rfl⟩ : syracuseStep 2707145 = 2030359) B2030359
theorem B970487 : Blo 646304 970487 := bstep (se 1 (by rfl) ⟨727865, by rfl⟩ : syracuseStep 970487 = 1455731) B1455731
theorem B1756939 : Blo 646304 1756939 := bstep (se 1 (by rfl) ⟨1317704, by rfl⟩ : syracuseStep 1756939 = 2635409) B2635409
theorem B970511 : Blo 646304 970511 := bstep (se 1 (by rfl) ⟨727883, by rfl⟩ : syracuseStep 970511 = 1455767) B1455767
theorem B1462031 : Blo 646304 1462031 := bstep (se 1 (by rfl) ⟨1096523, by rfl⟩ : syracuseStep 1462031 = 2193047) B2193047
theorem B1462049 : Blo 646304 1462049 := bstep (se 2 (by rfl) ⟨548268, by rfl⟩ : syracuseStep 1462049 = 1096537) B1096537
theorem B970553 : Blo 646304 970553 := bstep (se 2 (by rfl) ⟨363957, by rfl⟩ : syracuseStep 970553 = 727915) B727915
theorem B1560379 : Blo 646304 1560379 := bstep (se 1 (by rfl) ⟨1170284, by rfl⟩ : syracuseStep 1560379 = 2340569) B2340569
theorem B970631 : Blo 646304 970631 := bstep (se 1 (by rfl) ⟨727973, by rfl⟩ : syracuseStep 970631 = 1455947) B1455947
theorem B970667 : Blo 646304 970667 := bstep (se 1 (by rfl) ⟨728000, by rfl⟩ : syracuseStep 970667 = 1456001) B1456001
theorem B970697 : Blo 646304 970697 := bstep (se 2 (by rfl) ⟨364011, by rfl⟩ : syracuseStep 970697 = 728023) B728023
theorem B1036331 : Blo 646304 1036331 := bstep (se 1 (by rfl) ⟨777248, by rfl⟩ : syracuseStep 1036331 = 1554497) B1554497
theorem B970811 : Blo 646304 970811 := bstep (se 1 (by rfl) ⟨728108, by rfl⟩ : syracuseStep 970811 = 1456217) B1456217
theorem B4444247 : Blo 646304 4444247 := bstep (se 1 (by rfl) ⟨3333185, by rfl⟩ : syracuseStep 4444247 = 6666371) B6666371
theorem B970871 : Blo 646304 970871 := bstep (se 1 (by rfl) ⟨728153, by rfl⟩ : syracuseStep 970871 = 1456307) B1456307
theorem B1462391 : Blo 646304 1462391 := bstep (se 1 (by rfl) ⟨1096793, by rfl⟩ : syracuseStep 1462391 = 2193587) B2193587
theorem B970895 : Blo 646304 970895 := bstep (se 1 (by rfl) ⟨728171, by rfl⟩ : syracuseStep 970895 = 1456343) B1456343
theorem B970937 : Blo 646304 970937 := bstep (se 2 (by rfl) ⟨364101, by rfl⟩ : syracuseStep 970937 = 728203) B728203
theorem B7393517 : Blo 646304 7393517 := bstep (se 3 (by rfl) ⟨1386284, by rfl⟩ : syracuseStep 7393517 = 2772569) B2772569
theorem B971015 : Blo 646304 971015 := bstep (se 1 (by rfl) ⟨728261, by rfl⟩ : syracuseStep 971015 = 1456523) B1456523
theorem B971051 : Blo 646304 971051 := bstep (se 1 (by rfl) ⟨728288, by rfl⟩ : syracuseStep 971051 = 1456577) B1456577
theorem B1462571 : Blo 646304 1462571 := bstep (se 1 (by rfl) ⟨1096928, by rfl⟩ : syracuseStep 1462571 = 2193857) B2193857
theorem B971081 : Blo 646304 971081 := bstep (se 2 (by rfl) ⟨364155, by rfl⟩ : syracuseStep 971081 = 728311) B728311
theorem B971195 : Blo 646304 971195 := bstep (se 1 (by rfl) ⟨728396, by rfl⟩ : syracuseStep 971195 = 1456793) B1456793
theorem B971255 : Blo 646304 971255 := bstep (se 1 (by rfl) ⟨728441, by rfl⟩ : syracuseStep 971255 = 1456883) B1456883
theorem B971279 : Blo 646304 971279 := bstep (se 1 (by rfl) ⟨728459, by rfl⟩ : syracuseStep 971279 = 1456919) B1456919
theorem B1036843 : Blo 646304 1036843 := bstep (se 1 (by rfl) ⟨777632, by rfl⟩ : syracuseStep 1036843 = 1555265) B1555265
theorem B971321 : Blo 646304 971321 := bstep (se 2 (by rfl) ⟨364245, by rfl⟩ : syracuseStep 971321 = 728491) B728491
theorem B971399 : Blo 646304 971399 := bstep (se 1 (by rfl) ⟨728549, by rfl⟩ : syracuseStep 971399 = 1457099) B1457099
theorem B1462931 : Blo 646304 1462931 := bstep (se 1 (by rfl) ⟨1097198, by rfl⟩ : syracuseStep 1462931 = 2194397) B2194397
theorem B971435 : Blo 646304 971435 := bstep (se 1 (by rfl) ⟨728576, by rfl⟩ : syracuseStep 971435 = 1457153) B1457153
theorem B7000769 : Blo 646304 7000769 := bstep (se 2 (by rfl) ⟨2625288, by rfl⟩ : syracuseStep 7000769 = 5250577) B5250577
theorem B971465 : Blo 646304 971465 := bstep (se 2 (by rfl) ⟨364299, by rfl⟩ : syracuseStep 971465 = 728599) B728599
theorem B1462985 : Blo 646304 1462985 := bstep (se 2 (by rfl) ⟨548619, by rfl⟩ : syracuseStep 1462985 = 1097239) B1097239
theorem B3363565 : Blo 646304 3363565 := bstep (se 3 (by rfl) ⟨630668, by rfl⟩ : syracuseStep 3363565 = 1261337) B1261337
theorem B1332001 : Blo 646304 1332001 := bstep (se 2 (by rfl) ⟨499500, by rfl⟩ : syracuseStep 1332001 = 999001) B999001
theorem B971579 : Blo 646304 971579 := bstep (se 1 (by rfl) ⟨728684, by rfl⟩ : syracuseStep 971579 = 1457369) B1457369
theorem B2806643 : Blo 646304 2806643 := bstep (se 1 (by rfl) ⟨2104982, by rfl⟩ : syracuseStep 2806643 = 4209965) B4209965
theorem B971639 : Blo 646304 971639 := bstep (se 1 (by rfl) ⟨728729, by rfl⟩ : syracuseStep 971639 = 1457459) B1457459
theorem B971663 : Blo 646304 971663 := bstep (se 1 (by rfl) ⟨728747, by rfl⟩ : syracuseStep 971663 = 1457495) B1457495
theorem B2184083 : Blo 646304 2184083 := bstep (se 1 (by rfl) ⟨1638062, by rfl⟩ : syracuseStep 2184083 = 3276125) B3276125
theorem B971705 : Blo 646304 971705 := bstep (se 2 (by rfl) ⟨364389, by rfl⟩ : syracuseStep 971705 = 728779) B728779
theorem B971783 : Blo 646304 971783 := bstep (se 1 (by rfl) ⟨728837, by rfl⟩ : syracuseStep 971783 = 1457675) B1457675
theorem B971819 : Blo 646304 971819 := bstep (se 1 (by rfl) ⟨728864, by rfl⟩ : syracuseStep 971819 = 1457729) B1457729
theorem B971849 : Blo 646304 971849 := bstep (se 2 (by rfl) ⟨364443, by rfl⟩ : syracuseStep 971849 = 728887) B728887
theorem B1168519 : Blo 646304 1168519 := bstep (se 1 (by rfl) ⟨876389, by rfl⟩ : syracuseStep 1168519 = 1752779) B1752779
theorem B971963 : Blo 646304 971963 := bstep (se 1 (by rfl) ⟨728972, by rfl⟩ : syracuseStep 971963 = 1457945) B1457945
theorem B1660105 : Blo 646304 1660105 := bstep (se 2 (by rfl) ⟨622539, by rfl⟩ : syracuseStep 1660105 = 1245079) B1245079
theorem B1561801 : Blo 646304 1561801 := bstep (se 2 (by rfl) ⟨585675, by rfl⟩ : syracuseStep 1561801 = 1171351) B1171351
theorem B21091565 : Blo 646304 21091565 := bstep (se 3 (by rfl) ⟨3954668, by rfl⟩ : syracuseStep 21091565 = 7909337) B7909337
theorem B972023 : Blo 646304 972023 := bstep (se 1 (by rfl) ⟨729017, by rfl⟩ : syracuseStep 972023 = 1458035) B1458035
theorem B972047 : Blo 646304 972047 := bstep (se 1 (by rfl) ⟨729035, by rfl⟩ : syracuseStep 972047 = 1458071) B1458071
theorem B972089 : Blo 646304 972089 := bstep (se 2 (by rfl) ⟨364533, by rfl⟩ : syracuseStep 972089 = 729067) B729067
theorem B972167 : Blo 646304 972167 := bstep (se 1 (by rfl) ⟨729125, by rfl⟩ : syracuseStep 972167 = 1458251) B1458251
theorem B972203 : Blo 646304 972203 := bstep (se 1 (by rfl) ⟨729152, by rfl⟩ : syracuseStep 972203 = 1458305) B1458305
theorem B873929 : Blo 646304 873929 := bstep (se 2 (by rfl) ⟨327723, by rfl⟩ : syracuseStep 873929 = 655447) B655447
theorem B972233 : Blo 646304 972233 := bstep (se 2 (by rfl) ⟨364587, by rfl⟩ : syracuseStep 972233 = 729175) B729175
theorem B50615837 : Blo 646304 50615837 := bstep (se 3 (by rfl) ⟨9490469, by rfl⟩ : syracuseStep 50615837 = 18980939) B18980939
theorem B972347 : Blo 646304 972347 := bstep (se 1 (by rfl) ⟨729260, by rfl⟩ : syracuseStep 972347 = 1458521) B1458521
theorem B972407 : Blo 646304 972407 := bstep (se 1 (by rfl) ⟨729305, by rfl⟩ : syracuseStep 972407 = 1458611) B1458611
theorem B972431 : Blo 646304 972431 := bstep (se 1 (by rfl) ⟨729323, by rfl⟩ : syracuseStep 972431 = 1458647) B1458647
theorem B972473 : Blo 646304 972473 := bstep (se 2 (by rfl) ⟨364677, by rfl⟩ : syracuseStep 972473 = 729355) B729355
theorem B972551 : Blo 646304 972551 := bstep (se 1 (by rfl) ⟨729413, by rfl⟩ : syracuseStep 972551 = 1458827) B1458827
theorem B972587 : Blo 646304 972587 := bstep (se 1 (by rfl) ⟨729440, by rfl⟩ : syracuseStep 972587 = 1458881) B1458881
theorem B972617 : Blo 646304 972617 := bstep (se 2 (by rfl) ⟨364731, by rfl⟩ : syracuseStep 972617 = 729463) B729463
theorem B3331975 : Blo 646304 3331975 := bstep (se 1 (by rfl) ⟨2498981, by rfl⟩ : syracuseStep 3331975 = 4997963) B4997963
theorem B972731 : Blo 646304 972731 := bstep (se 1 (by rfl) ⟨729548, by rfl⟩ : syracuseStep 972731 = 1459097) B1459097
theorem B972791 : Blo 646304 972791 := bstep (se 1 (by rfl) ⟨729593, by rfl⟩ : syracuseStep 972791 = 1459187) B1459187
theorem B972815 : Blo 646304 972815 := bstep (se 1 (by rfl) ⟨729611, by rfl⟩ : syracuseStep 972815 = 1459223) B1459223
theorem B31610897 : Blo 646304 31610897 := bstep (se 2 (by rfl) ⟨11854086, by rfl⟩ : syracuseStep 31610897 = 23708173) B23708173
theorem B3692567 : Blo 646304 3692567 := bstep (se 1 (by rfl) ⟨2769425, by rfl⟩ : syracuseStep 3692567 = 5538851) B5538851
theorem B972857 : Blo 646304 972857 := bstep (se 2 (by rfl) ⟨364821, by rfl⟩ : syracuseStep 972857 = 729643) B729643
theorem B1038395 : Blo 646304 1038395 := bstep (se 1 (by rfl) ⟨778796, by rfl⟩ : syracuseStep 1038395 = 1557593) B1557593
theorem B972935 : Blo 646304 972935 := bstep (se 1 (by rfl) ⟨729701, by rfl⟩ : syracuseStep 972935 = 1459403) B1459403
theorem B972971 : Blo 646304 972971 := bstep (se 1 (by rfl) ⟨729728, by rfl⟩ : syracuseStep 972971 = 1459457) B1459457
theorem B973001 : Blo 646304 973001 := bstep (se 2 (by rfl) ⟨364875, by rfl⟩ : syracuseStep 973001 = 729751) B729751
theorem B2185487 : Blo 646304 2185487 := bstep (se 1 (by rfl) ⟨1639115, by rfl⟩ : syracuseStep 2185487 = 3278231) B3278231
theorem B973115 : Blo 646304 973115 := bstep (se 1 (by rfl) ⟨729836, by rfl⟩ : syracuseStep 973115 = 1459673) B1459673
theorem B973175 : Blo 646304 973175 := bstep (se 1 (by rfl) ⟨729881, by rfl⟩ : syracuseStep 973175 = 1459763) B1459763
theorem B973199 : Blo 646304 973199 := bstep (se 1 (by rfl) ⟨729899, by rfl⟩ : syracuseStep 973199 = 1459799) B1459799
theorem B973241 : Blo 646304 973241 := bstep (se 2 (by rfl) ⟨364965, by rfl⟩ : syracuseStep 973241 = 729931) B729931
theorem B973319 : Blo 646304 973319 := bstep (se 1 (by rfl) ⟨729989, by rfl⟩ : syracuseStep 973319 = 1459979) B1459979
theorem B2185757 : Blo 646304 2185757 := bstep (se 3 (by rfl) ⟨409829, by rfl⟩ : syracuseStep 2185757 = 819659) B819659
theorem B973355 : Blo 646304 973355 := bstep (se 1 (by rfl) ⟨730016, by rfl⟩ : syracuseStep 973355 = 1460033) B1460033
theorem B973385 : Blo 646304 973385 := bstep (se 2 (by rfl) ⟨365019, by rfl⟩ : syracuseStep 973385 = 730039) B730039
theorem B973499 : Blo 646304 973499 := bstep (se 1 (by rfl) ⟨730124, by rfl⟩ : syracuseStep 973499 = 1460249) B1460249
theorem B973559 : Blo 646304 973559 := bstep (se 1 (by rfl) ⟨730169, by rfl⟩ : syracuseStep 973559 = 1460339) B1460339
theorem B973583 : Blo 646304 973583 := bstep (se 1 (by rfl) ⟨730187, by rfl⟩ : syracuseStep 973583 = 1460375) B1460375
theorem B973625 : Blo 646304 973625 := bstep (se 2 (by rfl) ⟨365109, by rfl⟩ : syracuseStep 973625 = 730219) B730219
theorem B973703 : Blo 646304 973703 := bstep (se 1 (by rfl) ⟨730277, by rfl⟩ : syracuseStep 973703 = 1460555) B1460555
theorem B3562393 : Blo 646304 3562393 := bstep (se 2 (by rfl) ⟨1335897, by rfl⟩ : syracuseStep 3562393 = 2671795) B2671795
theorem B973739 : Blo 646304 973739 := bstep (se 1 (by rfl) ⟨730304, by rfl⟩ : syracuseStep 973739 = 1460609) B1460609
theorem B973769 : Blo 646304 973769 := bstep (se 2 (by rfl) ⟨365163, by rfl⟩ : syracuseStep 973769 = 730327) B730327
theorem B3496925 : Blo 646304 3496925 := bstep (se 3 (by rfl) ⟨655673, by rfl⟩ : syracuseStep 3496925 = 1311347) B1311347
theorem B3333143 : Blo 646304 3333143 := bstep (se 1 (by rfl) ⟨2499857, by rfl⟩ : syracuseStep 3333143 = 4999715) B4999715
theorem B973883 : Blo 646304 973883 := bstep (se 1 (by rfl) ⟨730412, by rfl⟩ : syracuseStep 973883 = 1460825) B1460825
theorem B973943 : Blo 646304 973943 := bstep (se 1 (by rfl) ⟨730457, by rfl⟩ : syracuseStep 973943 = 1460915) B1460915
theorem B973967 : Blo 646304 973967 := bstep (se 1 (by rfl) ⟨730475, by rfl⟩ : syracuseStep 973967 = 1460951) B1460951
theorem B1662137 : Blo 646304 1662137 := bstep (se 2 (by rfl) ⟨623301, by rfl⟩ : syracuseStep 1662137 = 1246603) B1246603
theorem B974009 : Blo 646304 974009 := bstep (se 2 (by rfl) ⟨365253, by rfl⟩ : syracuseStep 974009 = 730507) B730507
theorem B646331 : Blo 646304 646331 := bstep (se 1 (by rfl) ⟨484748, by rfl⟩ : syracuseStep 646331 = 969497) B969497
theorem B646407 : Blo 646304 646407 := bstep (se 1 (by rfl) ⟨484805, by rfl⟩ : syracuseStep 646407 = 969611) B969611
theorem B974087 : Blo 646304 974087 := bstep (se 1 (by rfl) ⟨730565, by rfl⟩ : syracuseStep 974087 = 1461131) B1461131
theorem B646415 : Blo 646304 646415 := bstep (se 1 (by rfl) ⟨484811, by rfl⟩ : syracuseStep 646415 = 969623) B969623
theorem B974123 : Blo 646304 974123 := bstep (se 1 (by rfl) ⟨730592, by rfl⟩ : syracuseStep 974123 = 1461185) B1461185
theorem B646459 : Blo 646304 646459 := bstep (se 1 (by rfl) ⟨484844, by rfl⟩ : syracuseStep 646459 = 969689) B969689
theorem B1596731 : Blo 646304 1596731 := bstep (se 1 (by rfl) ⟨1197548, by rfl⟩ : syracuseStep 1596731 = 2395097) B2395097
theorem B974153 : Blo 646304 974153 := bstep (se 2 (by rfl) ⟨365307, by rfl⟩ : syracuseStep 974153 = 730615) B730615
theorem B646535 : Blo 646304 646535 := bstep (se 1 (by rfl) ⟨484901, by rfl⟩ : syracuseStep 646535 = 969803) B969803
theorem B646543 : Blo 646304 646543 := bstep (se 1 (by rfl) ⟨484907, by rfl⟩ : syracuseStep 646543 = 969815) B969815
theorem B6643129 : Blo 646304 6643129 := bstep (se 2 (by rfl) ⟨2491173, by rfl⟩ : syracuseStep 6643129 = 4982347) B4982347
theorem B646587 : Blo 646304 646587 := bstep (se 1 (by rfl) ⟨484940, by rfl⟩ : syracuseStep 646587 = 969881) B969881
theorem B974267 : Blo 646304 974267 := bstep (se 1 (by rfl) ⟨730700, by rfl⟩ : syracuseStep 974267 = 1461401) B1461401
theorem B974327 : Blo 646304 974327 := bstep (se 1 (by rfl) ⟨730745, by rfl⟩ : syracuseStep 974327 = 1461491) B1461491
theorem B646663 : Blo 646304 646663 := bstep (se 1 (by rfl) ⟨484997, by rfl⟩ : syracuseStep 646663 = 969995) B969995
theorem B646671 : Blo 646304 646671 := bstep (se 1 (by rfl) ⟨485003, by rfl⟩ : syracuseStep 646671 = 970007) B970007
theorem B974351 : Blo 646304 974351 := bstep (se 1 (by rfl) ⟨730763, by rfl⟩ : syracuseStep 974351 = 1461527) B1461527
theorem B7888427 : Blo 646304 7888427 := bstep (se 1 (by rfl) ⟨5916320, by rfl⟩ : syracuseStep 7888427 = 11832641) B11832641
theorem B974393 : Blo 646304 974393 := bstep (se 2 (by rfl) ⟨365397, by rfl⟩ : syracuseStep 974393 = 730795) B730795
theorem B646715 : Blo 646304 646715 := bstep (se 1 (by rfl) ⟨485036, by rfl⟩ : syracuseStep 646715 = 970073) B970073
theorem B646791 : Blo 646304 646791 := bstep (se 1 (by rfl) ⟨485093, by rfl⟩ : syracuseStep 646791 = 970187) B970187
theorem B974471 : Blo 646304 974471 := bstep (se 1 (by rfl) ⟨730853, by rfl⟩ : syracuseStep 974471 = 1461707) B1461707
theorem B646799 : Blo 646304 646799 := bstep (se 1 (by rfl) ⟨485099, by rfl⟩ : syracuseStep 646799 = 970199) B970199
theorem B974507 : Blo 646304 974507 := bstep (se 1 (by rfl) ⟨730880, by rfl⟩ : syracuseStep 974507 = 1461761) B1461761
theorem B646843 : Blo 646304 646843 := bstep (se 1 (by rfl) ⟨485132, by rfl⟩ : syracuseStep 646843 = 970265) B970265
theorem B974537 : Blo 646304 974537 := bstep (se 2 (by rfl) ⟨365451, by rfl⟩ : syracuseStep 974537 = 730903) B730903
theorem B646919 : Blo 646304 646919 := bstep (se 1 (by rfl) ⟨485189, by rfl⟩ : syracuseStep 646919 = 970379) B970379
theorem B646927 : Blo 646304 646927 := bstep (se 1 (by rfl) ⟨485195, by rfl⟩ : syracuseStep 646927 = 970391) B970391
theorem B646971 : Blo 646304 646971 := bstep (se 1 (by rfl) ⟨485228, by rfl⟩ : syracuseStep 646971 = 970457) B970457
theorem B974651 : Blo 646304 974651 := bstep (se 1 (by rfl) ⟨730988, by rfl⟩ : syracuseStep 974651 = 1461977) B1461977
theorem B974711 : Blo 646304 974711 := bstep (se 1 (by rfl) ⟨731033, by rfl⟩ : syracuseStep 974711 = 1462067) B1462067
theorem B647047 : Blo 646304 647047 := bstep (se 1 (by rfl) ⟨485285, by rfl⟩ : syracuseStep 647047 = 970571) B970571
theorem B647055 : Blo 646304 647055 := bstep (se 1 (by rfl) ⟨485291, by rfl⟩ : syracuseStep 647055 = 970583) B970583
theorem B974735 : Blo 646304 974735 := bstep (se 1 (by rfl) ⟨731051, by rfl⟩ : syracuseStep 974735 = 1462103) B1462103
theorem B3694481 : Blo 646304 3694481 := bstep (se 2 (by rfl) ⟨1385430, by rfl⟩ : syracuseStep 3694481 = 2770861) B2770861
theorem B11198359 : Blo 646304 11198359 := bstep (se 1 (by rfl) ⟨8398769, by rfl⟩ : syracuseStep 11198359 = 16797539) B16797539
theorem B2187161 : Blo 646304 2187161 := bstep (se 2 (by rfl) ⟨820185, by rfl⟩ : syracuseStep 2187161 = 1640371) B1640371
theorem B5627801 : Blo 646304 5627801 := bstep (se 2 (by rfl) ⟨2110425, by rfl⟩ : syracuseStep 5627801 = 4220851) B4220851
theorem B974777 : Blo 646304 974777 := bstep (se 2 (by rfl) ⟨365541, by rfl⟩ : syracuseStep 974777 = 731083) B731083
theorem B647099 : Blo 646304 647099 := bstep (se 1 (by rfl) ⟨485324, by rfl⟩ : syracuseStep 647099 = 970649) B970649
theorem B647175 : Blo 646304 647175 := bstep (se 1 (by rfl) ⟨485381, by rfl⟩ : syracuseStep 647175 = 970763) B970763
theorem B974855 : Blo 646304 974855 := bstep (se 1 (by rfl) ⟨731141, by rfl⟩ : syracuseStep 974855 = 1462283) B1462283
theorem B647183 : Blo 646304 647183 := bstep (se 1 (by rfl) ⟨485387, by rfl⟩ : syracuseStep 647183 = 970775) B970775
theorem B974891 : Blo 646304 974891 := bstep (se 1 (by rfl) ⟨731168, by rfl⟩ : syracuseStep 974891 = 1462337) B1462337
theorem B647227 : Blo 646304 647227 := bstep (se 1 (by rfl) ⟨485420, by rfl⟩ : syracuseStep 647227 = 970841) B970841
theorem B974921 : Blo 646304 974921 := bstep (se 2 (by rfl) ⟨365595, by rfl⟩ : syracuseStep 974921 = 731191) B731191
theorem B647303 : Blo 646304 647303 := bstep (se 1 (by rfl) ⟨485477, by rfl⟩ : syracuseStep 647303 = 970955) B970955
theorem B647311 : Blo 646304 647311 := bstep (se 1 (by rfl) ⟨485483, by rfl⟩ : syracuseStep 647311 = 970967) B970967
theorem B647355 : Blo 646304 647355 := bstep (se 1 (by rfl) ⟨485516, by rfl⟩ : syracuseStep 647355 = 971033) B971033
theorem B975035 : Blo 646304 975035 := bstep (se 1 (by rfl) ⟨731276, by rfl⟩ : syracuseStep 975035 = 1462553) B1462553
theorem B1040585 : Blo 646304 1040585 := bstep (se 2 (by rfl) ⟨390219, by rfl⟩ : syracuseStep 1040585 = 780439) B780439
theorem B975095 : Blo 646304 975095 := bstep (se 1 (by rfl) ⟨731321, by rfl⟩ : syracuseStep 975095 = 1462643) B1462643
theorem B647431 : Blo 646304 647431 := bstep (se 1 (by rfl) ⟨485573, by rfl⟩ : syracuseStep 647431 = 971147) B971147
theorem B647439 : Blo 646304 647439 := bstep (se 1 (by rfl) ⟨485579, by rfl⟩ : syracuseStep 647439 = 971159) B971159
theorem B975119 : Blo 646304 975119 := bstep (se 1 (by rfl) ⟨731339, by rfl⟩ : syracuseStep 975119 = 1462679) B1462679
theorem B975161 : Blo 646304 975161 := bstep (se 2 (by rfl) ⟨365685, by rfl⟩ : syracuseStep 975161 = 731371) B731371
theorem B647483 : Blo 646304 647483 := bstep (se 1 (by rfl) ⟨485612, by rfl⟩ : syracuseStep 647483 = 971225) B971225
theorem B778555 : Blo 646304 778555 := bstep (se 1 (by rfl) ⟨583916, by rfl⟩ : syracuseStep 778555 = 1167833) B1167833
theorem B647559 : Blo 646304 647559 := bstep (se 1 (by rfl) ⟨485669, by rfl⟩ : syracuseStep 647559 = 971339) B971339
theorem B975239 : Blo 646304 975239 := bstep (se 1 (by rfl) ⟨731429, by rfl⟩ : syracuseStep 975239 = 1462859) B1462859
theorem B647567 : Blo 646304 647567 := bstep (se 1 (by rfl) ⟨485675, by rfl⟩ : syracuseStep 647567 = 971351) B971351
theorem B975275 : Blo 646304 975275 := bstep (se 1 (by rfl) ⟨731456, by rfl⟩ : syracuseStep 975275 = 1462913) B1462913
theorem B647611 : Blo 646304 647611 := bstep (se 1 (by rfl) ⟨485708, by rfl⟩ : syracuseStep 647611 = 971417) B971417
theorem B975305 : Blo 646304 975305 := bstep (se 2 (by rfl) ⟨365739, by rfl⟩ : syracuseStep 975305 = 731479) B731479
theorem B7397891 : Blo 646304 7397891 := bstep (se 1 (by rfl) ⟨5548418, by rfl⟩ : syracuseStep 7397891 = 11096837) B11096837
theorem B647687 : Blo 646304 647687 := bstep (se 1 (by rfl) ⟨485765, by rfl⟩ : syracuseStep 647687 = 971531) B971531
theorem B2777611 : Blo 646304 2777611 := bstep (se 1 (by rfl) ⟨2083208, by rfl⟩ : syracuseStep 2777611 = 4166417) B4166417
theorem B647695 : Blo 646304 647695 := bstep (se 1 (by rfl) ⟨485771, by rfl⟩ : syracuseStep 647695 = 971543) B971543
theorem B647739 : Blo 646304 647739 := bstep (se 1 (by rfl) ⟨485804, by rfl⟩ : syracuseStep 647739 = 971609) B971609
theorem B975419 : Blo 646304 975419 := bstep (se 1 (by rfl) ⟨731564, by rfl⟩ : syracuseStep 975419 = 1463129) B1463129
theorem B3695165 : Blo 646304 3695165 := bstep (se 3 (by rfl) ⟨692843, by rfl⟩ : syracuseStep 3695165 = 1385687) B1385687
theorem B2187863 : Blo 646304 2187863 := bstep (se 1 (by rfl) ⟨1640897, by rfl⟩ : syracuseStep 2187863 = 3281795) B3281795
theorem B647815 : Blo 646304 647815 := bstep (se 1 (by rfl) ⟨485861, by rfl⟩ : syracuseStep 647815 = 971723) B971723
theorem B647823 : Blo 646304 647823 := bstep (se 1 (by rfl) ⟨485867, by rfl⟩ : syracuseStep 647823 = 971735) B971735
theorem B647867 : Blo 646304 647867 := bstep (se 1 (by rfl) ⟨485900, by rfl⟩ : syracuseStep 647867 = 971801) B971801
theorem B647943 : Blo 646304 647943 := bstep (se 1 (by rfl) ⟨485957, by rfl⟩ : syracuseStep 647943 = 971915) B971915
theorem B647951 : Blo 646304 647951 := bstep (se 1 (by rfl) ⟨485963, by rfl⟩ : syracuseStep 647951 = 971927) B971927
theorem B647995 : Blo 646304 647995 := bstep (se 1 (by rfl) ⟨485996, by rfl⟩ : syracuseStep 647995 = 971993) B971993
theorem B648071 : Blo 646304 648071 := bstep (se 1 (by rfl) ⟨486053, by rfl⟩ : syracuseStep 648071 = 972107) B972107
theorem B648079 : Blo 646304 648079 := bstep (se 1 (by rfl) ⟨486059, by rfl⟩ : syracuseStep 648079 = 972119) B972119
theorem B648123 : Blo 646304 648123 := bstep (se 1 (by rfl) ⟨486092, by rfl⟩ : syracuseStep 648123 = 972185) B972185
theorem B648199 : Blo 646304 648199 := bstep (se 1 (by rfl) ⟨486149, by rfl⟩ : syracuseStep 648199 = 972299) B972299
theorem B3105803 : Blo 646304 3105803 := bstep (se 1 (by rfl) ⟨2329352, by rfl⟩ : syracuseStep 3105803 = 4658705) B4658705
theorem B648207 : Blo 646304 648207 := bstep (se 1 (by rfl) ⟨486155, by rfl⟩ : syracuseStep 648207 = 972311) B972311
theorem B648251 : Blo 646304 648251 := bstep (se 1 (by rfl) ⟨486188, by rfl⟩ : syracuseStep 648251 = 972377) B972377
theorem B2188349 : Blo 646304 2188349 := bstep (se 3 (by rfl) ⟨410315, by rfl⟩ : syracuseStep 2188349 = 820631) B820631
theorem B648327 : Blo 646304 648327 := bstep (se 1 (by rfl) ⟨486245, by rfl⟩ : syracuseStep 648327 = 972491) B972491
theorem B648335 : Blo 646304 648335 := bstep (se 1 (by rfl) ⟨486251, by rfl⟩ : syracuseStep 648335 = 972503) B972503
theorem B648379 : Blo 646304 648379 := bstep (se 1 (by rfl) ⟨486284, by rfl⟩ : syracuseStep 648379 = 972569) B972569
theorem B648455 : Blo 646304 648455 := bstep (se 1 (by rfl) ⟨486341, by rfl⟩ : syracuseStep 648455 = 972683) B972683
theorem B648463 : Blo 646304 648463 := bstep (se 1 (by rfl) ⟨486347, by rfl⟩ : syracuseStep 648463 = 972695) B972695
theorem B648507 : Blo 646304 648507 := bstep (se 1 (by rfl) ⟨486380, by rfl⟩ : syracuseStep 648507 = 972761) B972761
theorem B648583 : Blo 646304 648583 := bstep (se 1 (by rfl) ⟨486437, by rfl⟩ : syracuseStep 648583 = 972875) B972875
theorem B648591 : Blo 646304 648591 := bstep (se 1 (by rfl) ⟨486443, by rfl⟩ : syracuseStep 648591 = 972887) B972887
theorem B648635 : Blo 646304 648635 := bstep (se 1 (by rfl) ⟨486476, by rfl⟩ : syracuseStep 648635 = 972953) B972953
theorem B648711 : Blo 646304 648711 := bstep (se 1 (by rfl) ⟨486533, by rfl⟩ : syracuseStep 648711 = 973067) B973067
theorem B648719 : Blo 646304 648719 := bstep (se 1 (by rfl) ⟨486539, by rfl⟩ : syracuseStep 648719 = 973079) B973079
theorem B5531165 : Blo 646304 5531165 := bstep (se 3 (by rfl) ⟨1037093, by rfl⟩ : syracuseStep 5531165 = 2074187) B2074187
theorem B648763 : Blo 646304 648763 := bstep (se 1 (by rfl) ⟨486572, by rfl⟩ : syracuseStep 648763 = 973145) B973145
theorem B648839 : Blo 646304 648839 := bstep (se 1 (by rfl) ⟨486629, by rfl⟩ : syracuseStep 648839 = 973259) B973259
theorem B648847 : Blo 646304 648847 := bstep (se 1 (by rfl) ⟨486635, by rfl⟩ : syracuseStep 648847 = 973271) B973271
theorem B648891 : Blo 646304 648891 := bstep (se 1 (by rfl) ⟨486668, by rfl⟩ : syracuseStep 648891 = 973337) B973337
theorem B648967 : Blo 646304 648967 := bstep (se 1 (by rfl) ⟨486725, by rfl⟩ : syracuseStep 648967 = 973451) B973451
theorem B648975 : Blo 646304 648975 := bstep (se 1 (by rfl) ⟨486731, by rfl⟩ : syracuseStep 648975 = 973463) B973463
theorem B649019 : Blo 646304 649019 := bstep (se 1 (by rfl) ⟨486764, by rfl⟩ : syracuseStep 649019 = 973529) B973529
theorem B649095 : Blo 646304 649095 := bstep (se 1 (by rfl) ⟨486821, by rfl⟩ : syracuseStep 649095 = 973643) B973643
theorem B649103 : Blo 646304 649103 := bstep (se 1 (by rfl) ⟨486827, by rfl⟩ : syracuseStep 649103 = 973655) B973655
theorem B649147 : Blo 646304 649147 := bstep (se 1 (by rfl) ⟨486860, by rfl⟩ : syracuseStep 649147 = 973721) B973721
theorem B649223 : Blo 646304 649223 := bstep (se 1 (by rfl) ⟨486917, by rfl⟩ : syracuseStep 649223 = 973835) B973835
theorem B649231 : Blo 646304 649231 := bstep (se 1 (by rfl) ⟨486923, by rfl⟩ : syracuseStep 649231 = 973847) B973847
theorem B649275 : Blo 646304 649275 := bstep (se 1 (by rfl) ⟨486956, by rfl⟩ : syracuseStep 649275 = 973913) B973913
theorem B649351 : Blo 646304 649351 := bstep (se 1 (by rfl) ⟨487013, by rfl⟩ : syracuseStep 649351 = 974027) B974027
theorem B649359 : Blo 646304 649359 := bstep (se 1 (by rfl) ⟨487019, by rfl⟩ : syracuseStep 649359 = 974039) B974039
theorem B649403 : Blo 646304 649403 := bstep (se 1 (by rfl) ⟨487052, by rfl⟩ : syracuseStep 649403 = 974105) B974105
theorem B780535 : Blo 646304 780535 := bstep (se 1 (by rfl) ⟨585401, by rfl⟩ : syracuseStep 780535 = 1170803) B1170803
theorem B649479 : Blo 646304 649479 := bstep (se 1 (by rfl) ⟨487109, by rfl⟩ : syracuseStep 649479 = 974219) B974219
theorem B649487 : Blo 646304 649487 := bstep (se 1 (by rfl) ⟨487115, by rfl⟩ : syracuseStep 649487 = 974231) B974231
theorem B649531 : Blo 646304 649531 := bstep (se 1 (by rfl) ⟨487148, by rfl⟩ : syracuseStep 649531 = 974297) B974297
theorem B649607 : Blo 646304 649607 := bstep (se 1 (by rfl) ⟨487205, by rfl⟩ : syracuseStep 649607 = 974411) B974411
theorem B649615 : Blo 646304 649615 := bstep (se 1 (by rfl) ⟨487211, by rfl⟩ : syracuseStep 649615 = 974423) B974423
theorem B2189753 : Blo 646304 2189753 := bstep (se 2 (by rfl) ⟨821157, by rfl⟩ : syracuseStep 2189753 = 1642315) B1642315
theorem B649659 : Blo 646304 649659 := bstep (se 1 (by rfl) ⟨487244, by rfl⟩ : syracuseStep 649659 = 974489) B974489
theorem B4909571 : Blo 646304 4909571 := bstep (se 1 (by rfl) ⟨3682178, by rfl⟩ : syracuseStep 4909571 = 7364357) B7364357
theorem B649735 : Blo 646304 649735 := bstep (se 1 (by rfl) ⟨487301, by rfl⟩ : syracuseStep 649735 = 974603) B974603
theorem B649743 : Blo 646304 649743 := bstep (se 1 (by rfl) ⟨487307, by rfl⟩ : syracuseStep 649743 = 974615) B974615
theorem B649787 : Blo 646304 649787 := bstep (se 1 (by rfl) ⟨487340, by rfl⟩ : syracuseStep 649787 = 974681) B974681
theorem B649863 : Blo 646304 649863 := bstep (se 1 (by rfl) ⟨487397, by rfl⟩ : syracuseStep 649863 = 974795) B974795
theorem B649871 : Blo 646304 649871 := bstep (se 1 (by rfl) ⟨487403, by rfl⟩ : syracuseStep 649871 = 974807) B974807
theorem B649915 : Blo 646304 649915 := bstep (se 1 (by rfl) ⟨487436, by rfl⟩ : syracuseStep 649915 = 974873) B974873
theorem B649991 : Blo 646304 649991 := bstep (se 1 (by rfl) ⟨487493, by rfl⟩ : syracuseStep 649991 = 974987) B974987
theorem B649999 : Blo 646304 649999 := bstep (se 1 (by rfl) ⟨487499, by rfl⟩ : syracuseStep 649999 = 974999) B974999
theorem B650043 : Blo 646304 650043 := bstep (se 1 (by rfl) ⟨487532, by rfl⟩ : syracuseStep 650043 = 975065) B975065
theorem B650119 : Blo 646304 650119 := bstep (se 1 (by rfl) ⟨487589, by rfl⟩ : syracuseStep 650119 = 975179) B975179
theorem B650127 : Blo 646304 650127 := bstep (se 1 (by rfl) ⟨487595, by rfl⟩ : syracuseStep 650127 = 975191) B975191
theorem B650171 : Blo 646304 650171 := bstep (se 1 (by rfl) ⟨487628, by rfl⟩ : syracuseStep 650171 = 975257) B975257
theorem B650247 : Blo 646304 650247 := bstep (se 1 (by rfl) ⟨487685, by rfl⟩ : syracuseStep 650247 = 975371) B975371
theorem B2190347 : Blo 646304 2190347 := bstep (se 1 (by rfl) ⟨1642760, by rfl⟩ : syracuseStep 2190347 = 3285521) B3285521
theorem B650255 : Blo 646304 650255 := bstep (se 1 (by rfl) ⟨487691, by rfl⟩ : syracuseStep 650255 = 975383) B975383
theorem B650299 : Blo 646304 650299 := bstep (se 1 (by rfl) ⟨487724, by rfl⟩ : syracuseStep 650299 = 975449) B975449
theorem B2190455 : Blo 646304 2190455 := bstep (se 1 (by rfl) ⟨1642841, by rfl⟩ : syracuseStep 2190455 = 3285683) B3285683
theorem B2223545 : Blo 646304 2223545 := bstep (se 2 (by rfl) ⟨833829, by rfl⟩ : syracuseStep 2223545 = 1667659) B1667659
theorem B4746755 : Blo 646304 4746755 := bstep (se 1 (by rfl) ⟨3560066, by rfl⟩ : syracuseStep 4746755 = 7120133) B7120133
theorem B20967011 : Blo 646304 20967011 := bstep (se 1 (by rfl) ⟨15725258, by rfl⟩ : syracuseStep 20967011 = 31450517) B31450517
theorem B2191049 : Blo 646304 2191049 := bstep (se 2 (by rfl) ⟨821643, by rfl⟩ : syracuseStep 2191049 = 1643287) B1643287
theorem B4157729 : Blo 646304 4157729 := bstep (se 2 (by rfl) ⟨1559148, by rfl⟩ : syracuseStep 4157729 = 3118297) B3118297
theorem B2191751 : Blo 646304 2191751 := bstep (se 1 (by rfl) ⟨1643813, by rfl⟩ : syracuseStep 2191751 = 3287627) B3287627
theorem B2192129 : Blo 646304 2192129 := bstep (se 2 (by rfl) ⟨822048, by rfl⟩ : syracuseStep 2192129 = 1644097) B1644097
theorem B2454407 : Blo 646304 2454407 := bstep (se 1 (by rfl) ⟨1840805, by rfl⟩ : syracuseStep 2454407 = 3681611) B3681611
theorem B1668215 : Blo 646304 1668215 := bstep (se 1 (by rfl) ⟨1251161, by rfl⟩ : syracuseStep 1668215 = 2502323) B2502323
theorem B5535161 : Blo 646304 5535161 := bstep (se 2 (by rfl) ⟨2075685, by rfl⟩ : syracuseStep 5535161 = 4151371) B4151371
theorem B7370189 : Blo 646304 7370189 := bstep (se 3 (by rfl) ⟨1381910, by rfl⟩ : syracuseStep 7370189 = 2763821) B2763821
theorem B2192939 : Blo 646304 2192939 := bstep (se 1 (by rfl) ⟨1644704, by rfl⟩ : syracuseStep 2192939 = 3289409) B3289409
theorem B1636139 : Blo 646304 1636139 := bstep (se 1 (by rfl) ⟨1227104, by rfl⟩ : syracuseStep 1636139 = 2454209) B2454209
theorem B5535539 : Blo 646304 5535539 := bstep (se 1 (by rfl) ⟨4151654, by rfl⟩ : syracuseStep 5535539 = 8303309) B8303309
theorem B3504019 : Blo 646304 3504019 := bstep (se 1 (by rfl) ⟨2628014, by rfl⟩ : syracuseStep 3504019 = 5256029) B5256029
theorem B3275153 : Blo 646304 3275153 := bstep (se 2 (by rfl) ⟨1228182, by rfl⟩ : syracuseStep 3275153 = 2456365) B2456365
theorem B7469597 : Blo 646304 7469597 := bstep (se 3 (by rfl) ⟨1400549, by rfl⟩ : syracuseStep 7469597 = 2801099) B2801099
theorem B3701315 : Blo 646304 3701315 := bstep (se 1 (by rfl) ⟨2775986, by rfl⟩ : syracuseStep 3701315 = 5551973) B5551973
theorem B2456183 : Blo 646304 2456183 := bstep (se 1 (by rfl) ⟨1842137, by rfl⟩ : syracuseStep 2456183 = 3684275) B3684275
theorem B1637131 : Blo 646304 1637131 := bstep (se 1 (by rfl) ⟨1227848, by rfl⟩ : syracuseStep 1637131 = 2455697) B2455697
theorem B2194235 : Blo 646304 2194235 := bstep (se 1 (by rfl) ⟨1645676, by rfl⟩ : syracuseStep 2194235 = 3291353) B3291353
theorem B818039 : Blo 646304 818039 := bstep (se 1 (by rfl) ⟨613529, by rfl⟩ : syracuseStep 818039 = 1227059) B1227059
theorem B1637273 : Blo 646304 1637273 := bstep (se 2 (by rfl) ⟨613977, by rfl⟩ : syracuseStep 1637273 = 1227955) B1227955
theorem B3701771 : Blo 646304 3701771 := bstep (se 1 (by rfl) ⟨2776328, by rfl⟩ : syracuseStep 3701771 = 5552657) B5552657
theorem B818191 : Blo 646304 818191 := bstep (se 1 (by rfl) ⟨613643, by rfl⟩ : syracuseStep 818191 = 1227287) B1227287
theorem B1604623 : Blo 646304 1604623 := bstep (se 1 (by rfl) ⟨1203467, by rfl⟩ : syracuseStep 1604623 = 2406935) B2406935
theorem B2489387 : Blo 646304 2489387 := bstep (se 1 (by rfl) ⟨1867040, by rfl⟩ : syracuseStep 2489387 = 3734081) B3734081
theorem B1637435 : Blo 646304 1637435 := bstep (se 1 (by rfl) ⟨1228076, by rfl⟩ : syracuseStep 1637435 = 2456153) B2456153
theorem B818363 : Blo 646304 818363 := bstep (se 1 (by rfl) ⟨613772, by rfl⟩ : syracuseStep 818363 = 1227545) B1227545
theorem B2194721 : Blo 646304 2194721 := bstep (se 2 (by rfl) ⟨823020, by rfl⟩ : syracuseStep 2194721 = 1646041) B1646041
theorem B1637779 : Blo 646304 1637779 := bstep (se 1 (by rfl) ⟨1228334, by rfl⟩ : syracuseStep 1637779 = 2456669) B2456669
theorem B10485197 : Blo 646304 10485197 := bstep (se 3 (by rfl) ⟨1965974, by rfl⟩ : syracuseStep 10485197 = 3931949) B3931949
theorem B1637921 : Blo 646304 1637921 := bstep (se 2 (by rfl) ⟨614220, by rfl⟩ : syracuseStep 1637921 = 1228441) B1228441
theorem B2457155 : Blo 646304 2457155 := bstep (se 1 (by rfl) ⟨1842866, by rfl⟩ : syracuseStep 2457155 = 3685733) B3685733
theorem B1244873 : Blo 646304 1244873 := bstep (se 2 (by rfl) ⟨466827, by rfl⟩ : syracuseStep 1244873 = 933655) B933655
theorem B4914917 : Blo 646304 4914917 := bstep (se 4 (by rfl) ⟨460773, by rfl⟩ : syracuseStep 4914917 = 921547) B921547
theorem B982903 : Blo 646304 982903 := bstep (se 1 (by rfl) ⟨737177, by rfl⟩ : syracuseStep 982903 = 1474355) B1474355
theorem B1638407 : Blo 646304 1638407 := bstep (se 1 (by rfl) ⟨1228805, by rfl⟩ : syracuseStep 1638407 = 2457611) B2457611
theorem B4391371 : Blo 646304 4391371 := bstep (se 1 (by rfl) ⟨3293528, by rfl⟩ : syracuseStep 4391371 = 6587057) B6587057
theorem B9372185 : Blo 646304 9372185 := bstep (se 2 (by rfl) ⟨3514569, by rfl⟩ : syracuseStep 9372185 = 7029139) B7029139
theorem B656047 : Blo 646304 656047 := bstep (se 1 (by rfl) ⟨492035, by rfl⟩ : syracuseStep 656047 = 984071) B984071
theorem B3703481 : Blo 646304 3703481 := bstep (se 2 (by rfl) ⟨1388805, by rfl⟩ : syracuseStep 3703481 = 2777611) B2777611
theorem B4424705 : Blo 646304 4424705 := bstep (se 2 (by rfl) ⟨1659264, by rfl⟩ : syracuseStep 4424705 = 3318529) B3318529
theorem B2458781 : Blo 646304 2458781 := bstep (se 3 (by rfl) ⟨461021, by rfl⟩ : syracuseStep 2458781 = 922043) B922043
theorem B2458795 : Blo 646304 2458795 := bstep (se 1 (by rfl) ⟨1844096, by rfl⟩ : syracuseStep 2458795 = 3688193) B3688193
theorem B4162853 : Blo 646304 4162853 := bstep (se 4 (by rfl) ⟨390267, by rfl⟩ : syracuseStep 4162853 = 780535) B780535
theorem B1049951 : Blo 646304 1049951 := bstep (se 1 (by rfl) ⟨787463, by rfl⟩ : syracuseStep 1049951 = 1574927) B1574927
theorem B4687247 : Blo 646304 4687247 := bstep (se 1 (by rfl) ⟨3515435, by rfl⟩ : syracuseStep 4687247 = 7030871) B7030871
theorem B18711971 : Blo 646304 18711971 := bstep (se 1 (by rfl) ⟨14033978, by rfl⟩ : syracuseStep 18711971 = 28067957) B28067957
theorem B1312183 : Blo 646304 1312183 := bstep (se 1 (by rfl) ⟨984137, by rfl⟩ : syracuseStep 1312183 = 1968275) B1968275
theorem B2459099 : Blo 646304 2459099 := bstep (se 1 (by rfl) ⟨1844324, by rfl⟩ : syracuseStep 2459099 = 3688649) B3688649
theorem B1246727 : Blo 646304 1246727 := bstep (se 1 (by rfl) ⟨935045, by rfl⟩ : syracuseStep 1246727 = 1870091) B1870091
theorem B984775 : Blo 646304 984775 := bstep (se 1 (by rfl) ⟨738581, by rfl⟩ : syracuseStep 984775 = 1477163) B1477163
theorem B3376939 : Blo 646304 3376939 := bstep (se 1 (by rfl) ⟨2532704, by rfl⟩ : syracuseStep 3376939 = 5065409) B5065409
theorem B2623603 : Blo 646304 2623603 := bstep (se 1 (by rfl) ⟨1967702, by rfl⟩ : syracuseStep 2623603 = 3935405) B3935405
theorem B1640695 : Blo 646304 1640695 := bstep (se 1 (by rfl) ⟨1230521, by rfl⟩ : syracuseStep 1640695 = 2461043) B2461043
theorem B1804763 : Blo 646304 1804763 := bstep (se 1 (by rfl) ⟨1353572, by rfl⟩ : syracuseStep 1804763 = 2707145) B2707145
theorem B1640969 : Blo 646304 1640969 := bstep (se 2 (by rfl) ⟨615363, by rfl⟩ : syracuseStep 1640969 = 1230727) B1230727
theorem B5704225 : Blo 646304 5704225 := bstep (se 2 (by rfl) ⟨2139084, by rfl⟩ : syracuseStep 5704225 = 4278169) B4278169
theorem B1640999 : Blo 646304 1640999 := bstep (se 1 (by rfl) ⟨1230749, by rfl⟩ : syracuseStep 1640999 = 2461499) B2461499
theorem B690887 : Blo 646304 690887 := bstep (se 1 (by rfl) ⟨518165, by rfl⟩ : syracuseStep 690887 = 1036331) B1036331
theorem B658139 : Blo 646304 658139 := bstep (se 1 (by rfl) ⟨493604, by rfl⟩ : syracuseStep 658139 = 987209) B987209
theorem B3279689 : Blo 646304 3279689 := bstep (se 2 (by rfl) ⟨1229883, by rfl⟩ : syracuseStep 3279689 = 2459767) B2459767
theorem B1641323 : Blo 646304 1641323 := bstep (se 1 (by rfl) ⟨1230992, by rfl⟩ : syracuseStep 1641323 = 2461985) B2461985
theorem B920585 : Blo 646304 920585 := bstep (se 2 (by rfl) ⟨345219, by rfl⟩ : syracuseStep 920585 = 690439) B690439
theorem B1871095 : Blo 646304 1871095 := bstep (se 1 (by rfl) ⟨1403321, by rfl⟩ : syracuseStep 1871095 = 2806643) B2806643
theorem B1641971 : Blo 646304 1641971 := bstep (se 1 (by rfl) ⟨1231478, by rfl⟩ : syracuseStep 1641971 = 2462957) B2462957
theorem B14061043 : Blo 646304 14061043 := bstep (se 1 (by rfl) ⟨10545782, by rfl⟩ : syracuseStep 14061043 = 21091565) B21091565
theorem B2494099 : Blo 646304 2494099 := bstep (se 1 (by rfl) ⟨1870574, by rfl⟩ : syracuseStep 2494099 = 3741149) B3741149
theorem B921451 : Blo 646304 921451 := bstep (se 1 (by rfl) ⟨691088, by rfl⟩ : syracuseStep 921451 = 1382177) B1382177
theorem B1970027 : Blo 646304 1970027 := bstep (se 1 (by rfl) ⟨1477520, by rfl⟩ : syracuseStep 1970027 = 2955041) B2955041
theorem B2330477 : Blo 646304 2330477 := bstep (se 3 (by rfl) ⟨436964, by rfl⟩ : syracuseStep 2330477 = 873929) B873929
theorem B7868279 : Blo 646304 7868279 := bstep (se 1 (by rfl) ⟨5901209, by rfl⟩ : syracuseStep 7868279 = 11802419) B11802419
theorem B1314721 : Blo 646304 1314721 := bstep (se 2 (by rfl) ⟨493020, by rfl⟩ : syracuseStep 1314721 = 986041) B986041
theorem B1642427 : Blo 646304 1642427 := bstep (se 1 (by rfl) ⟨1231820, by rfl⟩ : syracuseStep 1642427 = 2463641) B2463641
theorem B2461697 : Blo 646304 2461697 := bstep (se 2 (by rfl) ⟨923136, by rfl⟩ : syracuseStep 2461697 = 1846273) B1846273
theorem B21073931 : Blo 646304 21073931 := bstep (se 1 (by rfl) ⟨15805448, by rfl⟩ : syracuseStep 21073931 = 31610897) B31610897
theorem B2461711 : Blo 646304 2461711 := bstep (se 1 (by rfl) ⟨1846283, by rfl⟩ : syracuseStep 2461711 = 3692567) B3692567
theorem B692263 : Blo 646304 692263 := bstep (se 1 (by rfl) ⟨519197, by rfl⟩ : syracuseStep 692263 = 1038395) B1038395
theorem B3280985 : Blo 646304 3280985 := bstep (se 2 (by rfl) ⟨1230369, by rfl⟩ : syracuseStep 3280985 = 2460739) B2460739
theorem B922151 : Blo 646304 922151 := bstep (se 1 (by rfl) ⟨691613, by rfl⟩ : syracuseStep 922151 = 1383227) B1383227
theorem B1643105 : Blo 646304 1643105 := bstep (se 2 (by rfl) ⟨616164, by rfl⟩ : syracuseStep 1643105 = 1232329) B1232329
theorem B2331283 : Blo 646304 2331283 := bstep (se 1 (by rfl) ⟨1748462, by rfl⟩ : syracuseStep 2331283 = 3496925) B3496925
theorem B35493065 : Blo 646304 35493065 := bstep (se 2 (by rfl) ⟨13309899, by rfl⟩ : syracuseStep 35493065 = 26619799) B26619799
theorem B2462987 : Blo 646304 2462987 := bstep (se 1 (by rfl) ⟨1847240, by rfl⟩ : syracuseStep 2462987 = 3694481) B3694481
theorem B4920749 : Blo 646304 4920749 := bstep (se 3 (by rfl) ⟨922640, by rfl⟩ : syracuseStep 4920749 = 1845281) B1845281
theorem B1316359 : Blo 646304 1316359 := bstep (se 1 (by rfl) ⟨987269, by rfl⟩ : syracuseStep 1316359 = 1974539) B1974539
theorem B5609021 : Blo 646304 5609021 := bstep (se 3 (by rfl) ⟨1051691, by rfl⟩ : syracuseStep 5609021 = 2103383) B2103383
theorem B2463443 : Blo 646304 2463443 := bstep (se 1 (by rfl) ⟨1847582, by rfl⟩ : syracuseStep 2463443 = 3695165) B3695165
theorem B923575 : Blo 646304 923575 := bstep (se 1 (by rfl) ⟨692681, by rfl⟩ : syracuseStep 923575 = 1385363) B1385363
theorem B2070535 : Blo 646304 2070535 := bstep (se 1 (by rfl) ⟨1552901, by rfl⟩ : syracuseStep 2070535 = 3105803) B3105803
theorem B1644563 : Blo 646304 1644563 := bstep (se 1 (by rfl) ⟨1233422, by rfl⟩ : syracuseStep 1644563 = 2466845) B2466845
theorem B23992561 : Blo 646304 23992561 := bstep (se 2 (by rfl) ⟨8997210, by rfl⟩ : syracuseStep 23992561 = 17994421) B17994421
theorem B1776001 : Blo 646304 1776001 := bstep (se 2 (by rfl) ⟨666000, by rfl⟩ : syracuseStep 1776001 = 1332001) B1332001
theorem B8853893 : Blo 646304 8853893 := bstep (se 4 (by rfl) ⟨830052, by rfl⟩ : syracuseStep 8853893 = 1660105) B1660105
theorem B1645019 : Blo 646304 1645019 := bstep (se 1 (by rfl) ⟨1233764, by rfl⟩ : syracuseStep 1645019 = 2467529) B2467529
theorem B727591 : Blo 646304 727591 := bstep (se 1 (by rfl) ⟨545693, by rfl⟩ : syracuseStep 727591 = 1091387) B1091387
theorem B2464445 : Blo 646304 2464445 := bstep (se 3 (by rfl) ⟨462083, by rfl⟩ : syracuseStep 2464445 = 924167) B924167
theorem B1317575 : Blo 646304 1317575 := bstep (se 1 (by rfl) ⟨988181, by rfl⟩ : syracuseStep 1317575 = 1976363) B1976363
theorem B925033 : Blo 646304 925033 := bstep (se 2 (by rfl) ⟨346887, by rfl⟩ : syracuseStep 925033 = 693775) B693775
theorem B4923179 : Blo 646304 4923179 := bstep (se 1 (by rfl) ⟨3692384, by rfl⟩ : syracuseStep 4923179 = 7384769) B7384769
theorem B925705 : Blo 646304 925705 := bstep (se 2 (by rfl) ⟨347139, by rfl⟩ : syracuseStep 925705 = 694279) B694279
theorem B2465873 : Blo 646304 2465873 := bstep (se 2 (by rfl) ⟨924702, by rfl⟩ : syracuseStep 2465873 = 1849405) B1849405
theorem B729211 : Blo 646304 729211 := bstep (se 1 (by rfl) ⟨546908, by rfl⟩ : syracuseStep 729211 = 1093817) B1093817
theorem B1843357 : Blo 646304 1843357 := bstep (se 3 (by rfl) ⟨345629, by rfl⟩ : syracuseStep 1843357 = 691259) B691259
theorem B729679 : Blo 646304 729679 := bstep (se 1 (by rfl) ⟨547259, by rfl⟩ : syracuseStep 729679 = 1094519) B1094519
theorem B4989613 : Blo 646304 4989613 := bstep (se 3 (by rfl) ⟨935552, by rfl⟩ : syracuseStep 4989613 = 1871105) B1871105
theorem B6235055 : Blo 646304 6235055 := bstep (se 1 (by rfl) ⟨4676291, by rfl⟩ : syracuseStep 6235055 = 9352583) B9352583
theorem B730075 : Blo 646304 730075 := bstep (se 1 (by rfl) ⟨547556, by rfl⟩ : syracuseStep 730075 = 1095113) B1095113
theorem B2630737 : Blo 646304 2630737 := bstep (se 2 (by rfl) ⟨986526, by rfl⟩ : syracuseStep 2630737 = 1973053) B1973053
theorem B3286169 : Blo 646304 3286169 := bstep (se 2 (by rfl) ⟨1232313, by rfl⟩ : syracuseStep 3286169 = 2464627) B2464627
theorem B1090759 : Blo 646304 1090759 := bstep (se 1 (by rfl) ⟨818069, by rfl⟩ : syracuseStep 1090759 = 1636139) B1636139
theorem B1090921 : Blo 646304 1090921 := bstep (se 2 (by rfl) ⟨409095, by rfl⟩ : syracuseStep 1090921 = 818191) B818191
theorem B2139497 : Blo 646304 2139497 := bstep (se 2 (by rfl) ⟨802311, by rfl⟩ : syracuseStep 2139497 = 1604623) B1604623
theorem B1516943 : Blo 646304 1516943 := bstep (se 1 (by rfl) ⟨1137707, by rfl⟩ : syracuseStep 1516943 = 2275415) B2275415
theorem B730543 : Blo 646304 730543 := bstep (se 1 (by rfl) ⟨547907, by rfl⟩ : syracuseStep 730543 = 1095815) B1095815
theorem B2467361 : Blo 646304 2467361 := bstep (se 2 (by rfl) ⟨925260, by rfl⟩ : syracuseStep 2467361 = 1850521) B1850521
theorem B2762387 : Blo 646304 2762387 := bstep (se 1 (by rfl) ⟨2071790, by rfl⟩ : syracuseStep 2762387 = 4143581) B4143581
theorem B2467543 : Blo 646304 2467543 := bstep (se 1 (by rfl) ⟨1850657, by rfl⟩ : syracuseStep 2467543 = 3701315) B3701315
theorem B13510489 : Blo 646304 13510489 := bstep (se 2 (by rfl) ⟨5066433, by rfl⟩ : syracuseStep 13510489 = 10132867) B10132867
theorem B730975 : Blo 646304 730975 := bstep (se 1 (by rfl) ⟨548231, by rfl⟩ : syracuseStep 730975 = 1096463) B1096463
theorem B3319661 : Blo 646304 3319661 := bstep (se 3 (by rfl) ⟨622436, by rfl⟩ : syracuseStep 3319661 = 1244873) B1244873
theorem B8857505 : Blo 646304 8857505 := bstep (se 2 (by rfl) ⟨3321564, by rfl⟩ : syracuseStep 8857505 = 6643129) B6643129
theorem B1091515 : Blo 646304 1091515 := bstep (se 1 (by rfl) ⟨818636, by rfl⟩ : syracuseStep 1091515 = 1637273) B1637273
theorem B2467847 : Blo 646304 2467847 := bstep (se 1 (by rfl) ⟨1850885, by rfl⟩ : syracuseStep 2467847 = 3701771) B3701771
theorem B1091623 : Blo 646304 1091623 := bstep (se 1 (by rfl) ⟨818717, by rfl⟩ : syracuseStep 1091623 = 1637435) B1637435
theorem B1845305 : Blo 646304 1845305 := bstep (se 2 (by rfl) ⟨691989, by rfl⟩ : syracuseStep 1845305 = 1383979) B1383979
theorem B731335 : Blo 646304 731335 := bstep (se 1 (by rfl) ⟨548501, by rfl⟩ : syracuseStep 731335 = 1097003) B1097003
theorem B6990131 : Blo 646304 6990131 := bstep (se 1 (by rfl) ⟨5242598, by rfl⟩ : syracuseStep 6990131 = 10485197) B10485197
theorem B1091947 : Blo 646304 1091947 := bstep (se 1 (by rfl) ⟨818960, by rfl⟩ : syracuseStep 1091947 = 1637921) B1637921
theorem B2468333 : Blo 646304 2468333 := bstep (se 3 (by rfl) ⟨462812, by rfl⟩ : syracuseStep 2468333 = 925625) B925625
theorem B1387439 : Blo 646304 1387439 := bstep (se 1 (by rfl) ⟨1040579, by rfl⟩ : syracuseStep 1387439 = 2081159) B2081159
theorem B2501689 : Blo 646304 2501689 := bstep (se 2 (by rfl) ⟨938133, by rfl⟩ : syracuseStep 2501689 = 1876267) B1876267
theorem B3681359 : Blo 646304 3681359 := bstep (se 1 (by rfl) ⟨2761019, by rfl⟩ : syracuseStep 3681359 = 5522039) B5522039
theorem B1093007 : Blo 646304 1093007 := bstep (se 1 (by rfl) ⟨819755, by rfl⟩ : syracuseStep 1093007 = 1639511) B1639511
theorem B37957207 : Blo 646304 37957207 := bstep (se 1 (by rfl) ⟨28467905, by rfl⟩ : syracuseStep 37957207 = 56935811) B56935811
theorem B1093243 : Blo 646304 1093243 := bstep (se 1 (by rfl) ⟨819932, by rfl⟩ : syracuseStep 1093243 = 1639865) B1639865
theorem B3682361 : Blo 646304 3682361 := bstep (se 2 (by rfl) ⟨1380885, by rfl⟩ : syracuseStep 3682361 = 2761771) B2761771
theorem B1454327 : Blo 646304 1454327 := bstep (se 1 (by rfl) ⟨1090745, by rfl⟩ : syracuseStep 1454327 = 2181491) B2181491
theorem B1094107 : Blo 646304 1094107 := bstep (se 1 (by rfl) ⟨820580, by rfl⟩ : syracuseStep 1094107 = 1641161) B1641161
theorem B2765447 : Blo 646304 2765447 := bstep (se 1 (by rfl) ⟨2074085, by rfl⟩ : syracuseStep 2765447 = 4148171) B4148171
theorem B1847947 : Blo 646304 1847947 := bstep (se 1 (by rfl) ⟨1385960, by rfl⟩ : syracuseStep 1847947 = 2771921) B2771921
theorem B1454921 : Blo 646304 1454921 := bstep (se 2 (by rfl) ⟨545595, by rfl⟩ : syracuseStep 1454921 = 1091191) B1091191
theorem B1094735 : Blo 646304 1094735 := bstep (se 1 (by rfl) ⟨821051, by rfl⟩ : syracuseStep 1094735 = 1642103) B1642103
theorem B2078095 : Blo 646304 2078095 := bstep (se 1 (by rfl) ⟨1558571, by rfl⟩ : syracuseStep 2078095 = 3117143) B3117143
theorem B2962831 : Blo 646304 2962831 := bstep (se 1 (by rfl) ⟨2222123, by rfl⟩ : syracuseStep 2962831 = 4444247) B4444247
theorem B4929011 : Blo 646304 4929011 := bstep (se 1 (by rfl) ⟨3696758, by rfl⟩ : syracuseStep 4929011 = 7393517) B7393517
theorem B1455713 : Blo 646304 1455713 := bstep (se 2 (by rfl) ⟨545892, by rfl⟩ : syracuseStep 1455713 = 1091785) B1091785
theorem B26621621 : Blo 646304 26621621 := bstep (se 5 (by rfl) ⟨1247888, by rfl⟩ : syracuseStep 26621621 = 2495777) B2495777
theorem B4667179 : Blo 646304 4667179 := bstep (se 1 (by rfl) ⟨3500384, by rfl⟩ : syracuseStep 4667179 = 7000769) B7000769
theorem B1095599 : Blo 646304 1095599 := bstep (se 1 (by rfl) ⟨821699, by rfl⟩ : syracuseStep 1095599 = 1643399) B1643399
theorem B1456055 : Blo 646304 1456055 := bstep (se 1 (by rfl) ⟨1092041, by rfl⟩ : syracuseStep 1456055 = 2184083) B2184083
theorem B1096031 : Blo 646304 1096031 := bstep (se 1 (by rfl) ⟨822023, by rfl⟩ : syracuseStep 1096031 = 1644047) B1644047
theorem B16005509 : Blo 646304 16005509 := bstep (se 4 (by rfl) ⟨1500516, by rfl⟩ : syracuseStep 16005509 = 3001033) B3001033
theorem B1456649 : Blo 646304 1456649 := bstep (se 2 (by rfl) ⟨546243, by rfl⟩ : syracuseStep 1456649 = 1092487) B1092487
theorem B1456991 : Blo 646304 1456991 := bstep (se 1 (by rfl) ⟨1092743, by rfl⟩ : syracuseStep 1456991 = 2185487) B2185487
theorem B56736611 : Blo 646304 56736611 := bstep (se 1 (by rfl) ⟨42552458, by rfl⟩ : syracuseStep 56736611 = 85104917) B85104917
theorem B1096591 : Blo 646304 1096591 := bstep (se 1 (by rfl) ⟨822443, by rfl⟩ : syracuseStep 1096591 = 1644887) B1644887
theorem B1457171 : Blo 646304 1457171 := bstep (se 1 (by rfl) ⟨1092878, by rfl⟩ : syracuseStep 1457171 = 2185757) B2185757
theorem B1457513 : Blo 646304 1457513 := bstep (se 2 (by rfl) ⟨546567, by rfl⟩ : syracuseStep 1457513 = 1093135) B1093135
theorem B1228297 : Blo 646304 1228297 := bstep (se 2 (by rfl) ⟨460611, by rfl⟩ : syracuseStep 1228297 = 921223) B921223
theorem B1097273 : Blo 646304 1097273 := bstep (se 2 (by rfl) ⟨411477, by rfl⟩ : syracuseStep 1097273 = 822955) B822955
theorem B3685985 : Blo 646304 3685985 := bstep (se 2 (by rfl) ⟨1382244, by rfl⟩ : syracuseStep 3685985 = 2764489) B2764489
theorem B2342585 : Blo 646304 2342585 := bstep (se 2 (by rfl) ⟨878469, by rfl⟩ : syracuseStep 2342585 = 1756939) B1756939
theorem B5258951 : Blo 646304 5258951 := bstep (se 1 (by rfl) ⟨3944213, by rfl⟩ : syracuseStep 5258951 = 7888427) B7888427
theorem B1752787 : Blo 646304 1752787 := bstep (se 1 (by rfl) ⟨1314590, by rfl⟩ : syracuseStep 1752787 = 2629181) B2629181
theorem B2080505 : Blo 646304 2080505 := bstep (se 2 (by rfl) ⟨780189, by rfl⟩ : syracuseStep 2080505 = 1560379) B1560379
theorem B8437537 : Blo 646304 8437537 := bstep (se 2 (by rfl) ⟨3164076, by rfl⟩ : syracuseStep 8437537 = 6328153) B6328153
theorem B1458107 : Blo 646304 1458107 := bstep (se 1 (by rfl) ⟨1093580, by rfl⟩ : syracuseStep 1458107 = 2187161) B2187161
theorem B3751867 : Blo 646304 3751867 := bstep (se 1 (by rfl) ⟨2813900, by rfl⟩ : syracuseStep 3751867 = 5627801) B5627801
theorem B1458233 : Blo 646304 1458233 := bstep (se 2 (by rfl) ⟨546837, by rfl⟩ : syracuseStep 1458233 = 1093675) B1093675
theorem B4931927 : Blo 646304 4931927 := bstep (se 1 (by rfl) ⟨3698945, by rfl⟩ : syracuseStep 4931927 = 7397891) B7397891
theorem B1458575 : Blo 646304 1458575 := bstep (se 1 (by rfl) ⟨1093931, by rfl⟩ : syracuseStep 1458575 = 2187863) B2187863
theorem B1229231 : Blo 646304 1229231 := bstep (se 1 (by rfl) ⟨921923, by rfl⟩ : syracuseStep 1229231 = 1843847) B1843847
theorem B2212339 : Blo 646304 2212339 := bstep (se 1 (by rfl) ⟨1659254, by rfl⟩ : syracuseStep 2212339 = 3318509) B3318509
theorem B1458899 : Blo 646304 1458899 := bstep (se 1 (by rfl) ⟨1094174, by rfl⟩ : syracuseStep 1458899 = 2188349) B2188349
theorem B4670237 : Blo 646304 4670237 := bstep (se 3 (by rfl) ⟨875669, by rfl⟩ : syracuseStep 4670237 = 1751339) B1751339
theorem B1229755 : Blo 646304 1229755 := bstep (se 1 (by rfl) ⟨922316, by rfl⟩ : syracuseStep 1229755 = 1844633) B1844633
theorem B3687443 : Blo 646304 3687443 := bstep (se 1 (by rfl) ⟨2765582, by rfl⟩ : syracuseStep 3687443 = 5531165) B5531165
theorem B1230241 : Blo 646304 1230241 := bstep (se 2 (by rfl) ⟨461340, by rfl⟩ : syracuseStep 1230241 = 922681) B922681
theorem B1164719 : Blo 646304 1164719 := bstep (se 1 (by rfl) ⟨873539, by rfl⟩ : syracuseStep 1164719 = 1747079) B1747079
theorem B1558025 : Blo 646304 1558025 := bstep (se 2 (by rfl) ⟨584259, by rfl⟩ : syracuseStep 1558025 = 1168519) B1168519
theorem B2082401 : Blo 646304 2082401 := bstep (se 2 (by rfl) ⟨780900, by rfl⟩ : syracuseStep 2082401 = 1561801) B1561801
theorem B1459835 : Blo 646304 1459835 := bstep (se 1 (by rfl) ⟨1094876, by rfl⟩ : syracuseStep 1459835 = 2189753) B2189753
theorem B59754131 : Blo 646304 59754131 := bstep (se 1 (by rfl) ⟨44815598, by rfl⟩ : syracuseStep 59754131 = 89631197) B89631197
theorem B2082503 : Blo 646304 2082503 := bstep (se 1 (by rfl) ⟨1561877, by rfl⟩ : syracuseStep 2082503 = 3123755) B3123755
theorem B1459961 : Blo 646304 1459961 := bstep (se 2 (by rfl) ⟨547485, by rfl⟩ : syracuseStep 1459961 = 1094971) B1094971
theorem B1460231 : Blo 646304 1460231 := bstep (se 1 (by rfl) ⟨1095173, by rfl⟩ : syracuseStep 1460231 = 2190347) B2190347
theorem B1460303 : Blo 646304 1460303 := bstep (se 1 (by rfl) ⟨1095227, by rfl⟩ : syracuseStep 1460303 = 2190455) B2190455
theorem B5130497 : Blo 646304 5130497 := bstep (se 2 (by rfl) ⟨1923936, by rfl⟩ : syracuseStep 5130497 = 3847873) B3847873
theorem B2181437 : Blo 646304 2181437 := bstep (se 3 (by rfl) ⟨409019, by rfl⟩ : syracuseStep 2181437 = 818039) B818039
theorem B21023063 : Blo 646304 21023063 := bstep (se 1 (by rfl) ⟨15767297, by rfl⟩ : syracuseStep 21023063 = 31534595) B31534595
theorem B3164503 : Blo 646304 3164503 := bstep (se 1 (by rfl) ⟨2373377, by rfl⟩ : syracuseStep 3164503 = 4746755) B4746755
theorem B13978007 : Blo 646304 13978007 := bstep (se 1 (by rfl) ⟨10483505, by rfl⟩ : syracuseStep 13978007 = 20967011) B20967011
theorem B1460699 : Blo 646304 1460699 := bstep (se 1 (by rfl) ⟨1095524, by rfl⟩ : syracuseStep 1460699 = 2191049) B2191049
theorem B4442633 : Blo 646304 4442633 := bstep (se 2 (by rfl) ⟨1665987, by rfl⟩ : syracuseStep 4442633 = 3331975) B3331975
theorem B4672025 : Blo 646304 4672025 := bstep (se 2 (by rfl) ⟨1752009, by rfl⟩ : syracuseStep 4672025 = 3504019) B3504019
theorem B6638365 : Blo 646304 6638365 := bstep (se 3 (by rfl) ⟨1244693, by rfl⟩ : syracuseStep 6638365 = 2489387) B2489387
theorem B2771819 : Blo 646304 2771819 := bstep (se 1 (by rfl) ⟨2078864, by rfl⟩ : syracuseStep 2771819 = 4157729) B4157729
theorem B969647 : Blo 646304 969647 := bstep (se 1 (by rfl) ⟨727235, by rfl⟩ : syracuseStep 969647 = 1454471) B1454471
theorem B1461167 : Blo 646304 1461167 := bstep (se 1 (by rfl) ⟨1095875, by rfl⟩ : syracuseStep 1461167 = 2191751) B2191751
theorem B969737 : Blo 646304 969737 := bstep (se 2 (by rfl) ⟨363651, by rfl⟩ : syracuseStep 969737 = 727303) B727303
theorem B969767 : Blo 646304 969767 := bstep (se 1 (by rfl) ⟨727325, by rfl⟩ : syracuseStep 969767 = 1454651) B1454651
theorem B969851 : Blo 646304 969851 := bstep (se 1 (by rfl) ⟨727388, by rfl⟩ : syracuseStep 969851 = 1454777) B1454777
theorem B2182301 : Blo 646304 2182301 := bstep (se 3 (by rfl) ⟨409181, by rfl⟩ : syracuseStep 2182301 = 818363) B818363
theorem B1461419 : Blo 646304 1461419 := bstep (se 1 (by rfl) ⟨1096064, by rfl⟩ : syracuseStep 1461419 = 2192129) B2192129
theorem B969977 : Blo 646304 969977 := bstep (se 2 (by rfl) ⟨363741, by rfl⟩ : syracuseStep 969977 = 727483) B727483
theorem B970079 : Blo 646304 970079 := bstep (se 1 (by rfl) ⟨727559, by rfl⟩ : syracuseStep 970079 = 1455119) B1455119
theorem B970091 : Blo 646304 970091 := bstep (se 1 (by rfl) ⟨727568, by rfl⟩ : syracuseStep 970091 = 1455137) B1455137
theorem B970319 : Blo 646304 970319 := bstep (se 1 (by rfl) ⟨727739, by rfl⟩ : syracuseStep 970319 = 1455479) B1455479
theorem B3690107 : Blo 646304 3690107 := bstep (se 1 (by rfl) ⟨2767580, by rfl⟩ : syracuseStep 3690107 = 5535161) B5535161
theorem B1756811 : Blo 646304 1756811 := bstep (se 1 (by rfl) ⟨1317608, by rfl⟩ : syracuseStep 1756811 = 2635217) B2635217
theorem B2182841 : Blo 646304 2182841 := bstep (se 2 (by rfl) ⟨818565, by rfl⟩ : syracuseStep 2182841 = 1637131) B1637131
theorem B970439 : Blo 646304 970439 := bstep (se 1 (by rfl) ⟨727829, by rfl⟩ : syracuseStep 970439 = 1455659) B1455659
theorem B1461959 : Blo 646304 1461959 := bstep (se 1 (by rfl) ⟨1096469, by rfl⟩ : syracuseStep 1461959 = 2192939) B2192939
theorem B1232633 : Blo 646304 1232633 := bstep (se 2 (by rfl) ⟨462237, by rfl⟩ : syracuseStep 1232633 = 924475) B924475
theorem B970601 : Blo 646304 970601 := bstep (se 2 (by rfl) ⟨363975, by rfl⟩ : syracuseStep 970601 = 727951) B727951
theorem B3690359 : Blo 646304 3690359 := bstep (se 1 (by rfl) ⟨2767769, by rfl⟩ : syracuseStep 3690359 = 5535539) B5535539
theorem B1232815 : Blo 646304 1232815 := bstep (se 1 (by rfl) ⟨924611, by rfl⟩ : syracuseStep 1232815 = 1849223) B1849223
theorem B970679 : Blo 646304 970679 := bstep (se 1 (by rfl) ⟨728009, by rfl⟩ : syracuseStep 970679 = 1456019) B1456019
theorem B970715 : Blo 646304 970715 := bstep (se 1 (by rfl) ⟨728036, by rfl⟩ : syracuseStep 970715 = 1456073) B1456073
theorem B1232975 : Blo 646304 1232975 := bstep (se 1 (by rfl) ⟨924731, by rfl⟩ : syracuseStep 1232975 = 1849463) B1849463
theorem B2183435 : Blo 646304 2183435 := bstep (se 1 (by rfl) ⟨1637576, by rfl⟩ : syracuseStep 2183435 = 3275153) B3275153
theorem B971183 : Blo 646304 971183 := bstep (se 1 (by rfl) ⟨728387, by rfl⟩ : syracuseStep 971183 = 1456775) B1456775
theorem B971273 : Blo 646304 971273 := bstep (se 2 (by rfl) ⟨364227, by rfl⟩ : syracuseStep 971273 = 728455) B728455
theorem B2183705 : Blo 646304 2183705 := bstep (se 2 (by rfl) ⟨818889, by rfl⟩ : syracuseStep 2183705 = 1637779) B1637779
theorem B971303 : Blo 646304 971303 := bstep (se 1 (by rfl) ⟨728477, by rfl⟩ : syracuseStep 971303 = 1456955) B1456955
theorem B1462823 : Blo 646304 1462823 := bstep (se 1 (by rfl) ⟨1097117, by rfl⟩ : syracuseStep 1462823 = 2194235) B2194235
theorem B971387 : Blo 646304 971387 := bstep (se 1 (by rfl) ⟨728540, by rfl⟩ : syracuseStep 971387 = 1457081) B1457081
theorem B971513 : Blo 646304 971513 := bstep (se 2 (by rfl) ⟨364317, by rfl⟩ : syracuseStep 971513 = 728635) B728635
theorem B971615 : Blo 646304 971615 := bstep (se 1 (by rfl) ⟨728711, by rfl⟩ : syracuseStep 971615 = 1457423) B1457423
theorem B40555363 : Blo 646304 40555363 := bstep (se 1 (by rfl) ⟨30416522, by rfl⟩ : syracuseStep 40555363 = 60833045) B60833045
theorem B971627 : Blo 646304 971627 := bstep (se 1 (by rfl) ⟨728720, by rfl⟩ : syracuseStep 971627 = 1457441) B1457441
theorem B1463147 : Blo 646304 1463147 := bstep (se 1 (by rfl) ⟨1097360, by rfl⟩ : syracuseStep 1463147 = 2194721) B2194721
theorem B971855 : Blo 646304 971855 := bstep (se 1 (by rfl) ⟨728891, by rfl⟩ : syracuseStep 971855 = 1457783) B1457783
theorem B1234091 : Blo 646304 1234091 := bstep (se 1 (by rfl) ⟨925568, by rfl⟩ : syracuseStep 1234091 = 1851137) B1851137
theorem B971975 : Blo 646304 971975 := bstep (se 1 (by rfl) ⟨728981, by rfl⟩ : syracuseStep 971975 = 1457963) B1457963
theorem B14931145 : Blo 646304 14931145 := bstep (se 2 (by rfl) ⟨5599179, by rfl⟩ : syracuseStep 14931145 = 11198359) B11198359
theorem B972137 : Blo 646304 972137 := bstep (se 2 (by rfl) ⟨364551, by rfl⟩ : syracuseStep 972137 = 729103) B729103
theorem B972215 : Blo 646304 972215 := bstep (se 1 (by rfl) ⟨729161, by rfl⟩ : syracuseStep 972215 = 1458323) B1458323
theorem B972251 : Blo 646304 972251 := bstep (se 1 (by rfl) ⟨729188, by rfl⟩ : syracuseStep 972251 = 1458377) B1458377
theorem B1037863 : Blo 646304 1037863 := bstep (se 1 (by rfl) ⟨778397, by rfl⟩ : syracuseStep 1037863 = 1556795) B1556795
theorem B2184839 : Blo 646304 2184839 := bstep (se 1 (by rfl) ⟨1638629, by rfl⟩ : syracuseStep 2184839 = 3277259) B3277259
theorem B2184893 : Blo 646304 2184893 := bstep (se 3 (by rfl) ⟨409667, by rfl⟩ : syracuseStep 2184893 = 819335) B819335
theorem B10639163 : Blo 646304 10639163 := bstep (se 1 (by rfl) ⟨7979372, by rfl⟩ : syracuseStep 10639163 = 15958745) B15958745
theorem B2185055 : Blo 646304 2185055 := bstep (se 1 (by rfl) ⟨1638791, by rfl⟩ : syracuseStep 2185055 = 3277583) B3277583
theorem B2774893 : Blo 646304 2774893 := bstep (se 3 (by rfl) ⟨520292, by rfl⟩ : syracuseStep 2774893 = 1040585) B1040585
theorem B972719 : Blo 646304 972719 := bstep (se 1 (by rfl) ⟨729539, by rfl⟩ : syracuseStep 972719 = 1459079) B1459079
theorem B2185217 : Blo 646304 2185217 := bstep (se 2 (by rfl) ⟨819456, by rfl⟩ : syracuseStep 2185217 = 1638913) B1638913
theorem B972809 : Blo 646304 972809 := bstep (se 2 (by rfl) ⟨364803, by rfl⟩ : syracuseStep 972809 = 729607) B729607
theorem B972839 : Blo 646304 972839 := bstep (se 1 (by rfl) ⟨729629, by rfl⟩ : syracuseStep 972839 = 1459259) B1459259
theorem B1169447 : Blo 646304 1169447 := bstep (se 1 (by rfl) ⟨877085, by rfl⟩ : syracuseStep 1169447 = 1754171) B1754171
theorem B972923 : Blo 646304 972923 := bstep (se 1 (by rfl) ⟨729692, by rfl⟩ : syracuseStep 972923 = 1459385) B1459385
theorem B1169579 : Blo 646304 1169579 := bstep (se 1 (by rfl) ⟨877184, by rfl⟩ : syracuseStep 1169579 = 1754369) B1754369
theorem B973049 : Blo 646304 973049 := bstep (se 2 (by rfl) ⟨364893, by rfl⟩ : syracuseStep 973049 = 729787) B729787
theorem B973151 : Blo 646304 973151 := bstep (se 1 (by rfl) ⟨729863, by rfl⟩ : syracuseStep 973151 = 1459727) B1459727
theorem B973163 : Blo 646304 973163 := bstep (se 1 (by rfl) ⟨729872, by rfl⟩ : syracuseStep 973163 = 1459745) B1459745
theorem B973391 : Blo 646304 973391 := bstep (se 1 (by rfl) ⟨730043, by rfl⟩ : syracuseStep 973391 = 1460087) B1460087
theorem B9984647 : Blo 646304 9984647 := bstep (se 1 (by rfl) ⟨7488485, by rfl⟩ : syracuseStep 9984647 = 14976971) B14976971
theorem B973511 : Blo 646304 973511 := bstep (se 1 (by rfl) ⟨730133, by rfl⟩ : syracuseStep 973511 = 1460267) B1460267
theorem B3496733 : Blo 646304 3496733 := bstep (se 3 (by rfl) ⟨655637, by rfl⟩ : syracuseStep 3496733 = 1311275) B1311275
theorem B2186027 : Blo 646304 2186027 := bstep (se 1 (by rfl) ⟨1639520, by rfl⟩ : syracuseStep 2186027 = 3279041) B3279041
theorem B973673 : Blo 646304 973673 := bstep (se 2 (by rfl) ⟨365127, by rfl⟩ : syracuseStep 973673 = 730255) B730255
theorem B1039247 : Blo 646304 1039247 := bstep (se 1 (by rfl) ⟨779435, by rfl⟩ : syracuseStep 1039247 = 1558871) B1558871
theorem B973751 : Blo 646304 973751 := bstep (se 1 (by rfl) ⟨730313, by rfl⟩ : syracuseStep 973751 = 1460627) B1460627
theorem B973787 : Blo 646304 973787 := bstep (se 1 (by rfl) ⟨730340, by rfl⟩ : syracuseStep 973787 = 1460681) B1460681
theorem B4152293 : Blo 646304 4152293 := bstep (se 4 (by rfl) ⟨389277, by rfl⟩ : syracuseStep 4152293 = 778555) B778555
theorem B2186297 : Blo 646304 2186297 := bstep (se 2 (by rfl) ⟨819861, by rfl⟩ : syracuseStep 2186297 = 1639723) B1639723
theorem B1039483 : Blo 646304 1039483 := bstep (se 1 (by rfl) ⟨779612, by rfl⟩ : syracuseStep 1039483 = 1559225) B1559225
theorem B4742297 : Blo 646304 4742297 := bstep (se 2 (by rfl) ⟨1778361, by rfl⟩ : syracuseStep 4742297 = 3556723) B3556723
theorem B646319 : Blo 646304 646319 := bstep (se 1 (by rfl) ⟨484739, by rfl⟩ : syracuseStep 646319 = 969479) B969479
theorem B646343 : Blo 646304 646343 := bstep (se 1 (by rfl) ⟨484757, by rfl⟩ : syracuseStep 646343 = 969515) B969515
theorem B646363 : Blo 646304 646363 := bstep (se 1 (by rfl) ⟨484772, by rfl⟩ : syracuseStep 646363 = 969545) B969545
theorem B646439 : Blo 646304 646439 := bstep (se 1 (by rfl) ⟨484829, by rfl⟩ : syracuseStep 646439 = 969659) B969659
theorem B646479 : Blo 646304 646479 := bstep (se 1 (by rfl) ⟨484859, by rfl⟩ : syracuseStep 646479 = 969719) B969719
theorem B646495 : Blo 646304 646495 := bstep (se 1 (by rfl) ⟨484871, by rfl⟩ : syracuseStep 646495 = 969743) B969743
theorem B646523 : Blo 646304 646523 := bstep (se 1 (by rfl) ⟨484892, by rfl⟩ : syracuseStep 646523 = 969785) B969785
theorem B2186621 : Blo 646304 2186621 := bstep (se 3 (by rfl) ⟨409991, by rfl⟩ : syracuseStep 2186621 = 819983) B819983
theorem B646575 : Blo 646304 646575 := bstep (se 1 (by rfl) ⟨484931, by rfl⟩ : syracuseStep 646575 = 969863) B969863
theorem B974255 : Blo 646304 974255 := bstep (se 1 (by rfl) ⟨730691, by rfl⟩ : syracuseStep 974255 = 1461383) B1461383
theorem B646599 : Blo 646304 646599 := bstep (se 1 (by rfl) ⟨484949, by rfl⟩ : syracuseStep 646599 = 969899) B969899
theorem B3694025 : Blo 646304 3694025 := bstep (se 2 (by rfl) ⟨1385259, by rfl⟩ : syracuseStep 3694025 = 2770519) B2770519
theorem B646619 : Blo 646304 646619 := bstep (se 1 (by rfl) ⟨484964, by rfl⟩ : syracuseStep 646619 = 969929) B969929
theorem B974345 : Blo 646304 974345 := bstep (se 2 (by rfl) ⟨365379, by rfl⟩ : syracuseStep 974345 = 730759) B730759
theorem B646695 : Blo 646304 646695 := bstep (se 1 (by rfl) ⟨485021, by rfl⟩ : syracuseStep 646695 = 970043) B970043
theorem B777767 : Blo 646304 777767 := bstep (se 1 (by rfl) ⟨583325, by rfl⟩ : syracuseStep 777767 = 1166651) B1166651
theorem B974375 : Blo 646304 974375 := bstep (se 1 (by rfl) ⟨730781, by rfl⟩ : syracuseStep 974375 = 1461563) B1461563
theorem B646735 : Blo 646304 646735 := bstep (se 1 (by rfl) ⟨485051, by rfl⟩ : syracuseStep 646735 = 970103) B970103
theorem B646751 : Blo 646304 646751 := bstep (se 1 (by rfl) ⟨485063, by rfl⟩ : syracuseStep 646751 = 970127) B970127
theorem B646779 : Blo 646304 646779 := bstep (se 1 (by rfl) ⟨485084, by rfl⟩ : syracuseStep 646779 = 970169) B970169
theorem B974459 : Blo 646304 974459 := bstep (se 1 (by rfl) ⟨730844, by rfl⟩ : syracuseStep 974459 = 1461689) B1461689
theorem B2186891 : Blo 646304 2186891 := bstep (se 1 (by rfl) ⟨1640168, by rfl⟩ : syracuseStep 2186891 = 3280337) B3280337
theorem B646831 : Blo 646304 646831 := bstep (se 1 (by rfl) ⟨485123, by rfl⟩ : syracuseStep 646831 = 970247) B970247
theorem B646855 : Blo 646304 646855 := bstep (se 1 (by rfl) ⟨485141, by rfl⟩ : syracuseStep 646855 = 970283) B970283
theorem B646875 : Blo 646304 646875 := bstep (se 1 (by rfl) ⟨485156, by rfl⟩ : syracuseStep 646875 = 970313) B970313
theorem B974585 : Blo 646304 974585 := bstep (se 2 (by rfl) ⟨365469, by rfl⟩ : syracuseStep 974585 = 730939) B730939
theorem B646951 : Blo 646304 646951 := bstep (se 1 (by rfl) ⟨485213, by rfl⟩ : syracuseStep 646951 = 970427) B970427
theorem B646991 : Blo 646304 646991 := bstep (se 1 (by rfl) ⟨485243, by rfl⟩ : syracuseStep 646991 = 970487) B970487
theorem B647007 : Blo 646304 647007 := bstep (se 1 (by rfl) ⟨485255, by rfl⟩ : syracuseStep 647007 = 970511) B970511
theorem B974687 : Blo 646304 974687 := bstep (se 1 (by rfl) ⟨731015, by rfl⟩ : syracuseStep 974687 = 1462031) B1462031
theorem B974699 : Blo 646304 974699 := bstep (se 1 (by rfl) ⟨731024, by rfl⟩ : syracuseStep 974699 = 1462049) B1462049
theorem B647035 : Blo 646304 647035 := bstep (se 1 (by rfl) ⟨485276, by rfl⟩ : syracuseStep 647035 = 970553) B970553
theorem B647087 : Blo 646304 647087 := bstep (se 1 (by rfl) ⟨485315, by rfl⟩ : syracuseStep 647087 = 970631) B970631
theorem B647111 : Blo 646304 647111 := bstep (se 1 (by rfl) ⟨485333, by rfl⟩ : syracuseStep 647111 = 970667) B970667
theorem B647131 : Blo 646304 647131 := bstep (se 1 (by rfl) ⟨485348, by rfl⟩ : syracuseStep 647131 = 970697) B970697
theorem B647207 : Blo 646304 647207 := bstep (se 1 (by rfl) ⟨485405, by rfl⟩ : syracuseStep 647207 = 970811) B970811
theorem B647247 : Blo 646304 647247 := bstep (se 1 (by rfl) ⟨485435, by rfl⟩ : syracuseStep 647247 = 970871) B970871
theorem B974927 : Blo 646304 974927 := bstep (se 1 (by rfl) ⟨731195, by rfl⟩ : syracuseStep 974927 = 1462391) B1462391
theorem B647263 : Blo 646304 647263 := bstep (se 1 (by rfl) ⟨485447, by rfl⟩ : syracuseStep 647263 = 970895) B970895
theorem B647291 : Blo 646304 647291 := bstep (se 1 (by rfl) ⟨485468, by rfl⟩ : syracuseStep 647291 = 970937) B970937
theorem B647343 : Blo 646304 647343 := bstep (se 1 (by rfl) ⟨485507, by rfl⟩ : syracuseStep 647343 = 971015) B971015
theorem B647367 : Blo 646304 647367 := bstep (se 1 (by rfl) ⟨485525, by rfl⟩ : syracuseStep 647367 = 971051) B971051
theorem B975047 : Blo 646304 975047 := bstep (se 1 (by rfl) ⟨731285, by rfl⟩ : syracuseStep 975047 = 1462571) B1462571
theorem B647387 : Blo 646304 647387 := bstep (se 1 (by rfl) ⟨485540, by rfl⟩ : syracuseStep 647387 = 971081) B971081
theorem B5529829 : Blo 646304 5529829 := bstep (se 4 (by rfl) ⟨518421, by rfl⟩ : syracuseStep 5529829 = 1036843) B1036843
theorem B647463 : Blo 646304 647463 := bstep (se 1 (by rfl) ⟨485597, by rfl⟩ : syracuseStep 647463 = 971195) B971195
theorem B647503 : Blo 646304 647503 := bstep (se 1 (by rfl) ⟨485627, by rfl⟩ : syracuseStep 647503 = 971255) B971255
theorem B647519 : Blo 646304 647519 := bstep (se 1 (by rfl) ⟨485639, by rfl⟩ : syracuseStep 647519 = 971279) B971279
theorem B975209 : Blo 646304 975209 := bstep (se 2 (by rfl) ⟨365703, by rfl⟩ : syracuseStep 975209 = 731407) B731407
theorem B647547 : Blo 646304 647547 := bstep (se 1 (by rfl) ⟨485660, by rfl⟩ : syracuseStep 647547 = 971321) B971321
theorem B647599 : Blo 646304 647599 := bstep (se 1 (by rfl) ⟨485699, by rfl⟩ : syracuseStep 647599 = 971399) B971399
theorem B975287 : Blo 646304 975287 := bstep (se 1 (by rfl) ⟨731465, by rfl⟩ : syracuseStep 975287 = 1462931) B1462931
theorem B647623 : Blo 646304 647623 := bstep (se 1 (by rfl) ⟨485717, by rfl⟩ : syracuseStep 647623 = 971435) B971435
theorem B647643 : Blo 646304 647643 := bstep (se 1 (by rfl) ⟨485732, by rfl⟩ : syracuseStep 647643 = 971465) B971465
theorem B975323 : Blo 646304 975323 := bstep (se 1 (by rfl) ⟨731492, by rfl⟩ : syracuseStep 975323 = 1462985) B1462985
theorem B2187809 : Blo 646304 2187809 := bstep (se 2 (by rfl) ⟨820428, by rfl⟩ : syracuseStep 2187809 = 1640857) B1640857
theorem B647719 : Blo 646304 647719 := bstep (se 1 (by rfl) ⟨485789, by rfl⟩ : syracuseStep 647719 = 971579) B971579
theorem B647759 : Blo 646304 647759 := bstep (se 1 (by rfl) ⟨485819, by rfl⟩ : syracuseStep 647759 = 971639) B971639
theorem B647775 : Blo 646304 647775 := bstep (se 1 (by rfl) ⟨485831, by rfl⟩ : syracuseStep 647775 = 971663) B971663
theorem B1598075 : Blo 646304 1598075 := bstep (se 1 (by rfl) ⟨1198556, by rfl⟩ : syracuseStep 1598075 = 2397113) B2397113
theorem B647803 : Blo 646304 647803 := bstep (se 1 (by rfl) ⟨485852, by rfl⟩ : syracuseStep 647803 = 971705) B971705
theorem B647855 : Blo 646304 647855 := bstep (se 1 (by rfl) ⟨485891, by rfl⟩ : syracuseStep 647855 = 971783) B971783
theorem B647879 : Blo 646304 647879 := bstep (se 1 (by rfl) ⟨485909, by rfl⟩ : syracuseStep 647879 = 971819) B971819
theorem B647899 : Blo 646304 647899 := bstep (se 1 (by rfl) ⟨485924, by rfl⟩ : syracuseStep 647899 = 971849) B971849
theorem B2188025 : Blo 646304 2188025 := bstep (se 2 (by rfl) ⟨820509, by rfl⟩ : syracuseStep 2188025 = 1641019) B1641019
theorem B647975 : Blo 646304 647975 := bstep (se 1 (by rfl) ⟨485981, by rfl⟩ : syracuseStep 647975 = 971963) B971963
theorem B648015 : Blo 646304 648015 := bstep (se 1 (by rfl) ⟨486011, by rfl⟩ : syracuseStep 648015 = 972023) B972023
theorem B648031 : Blo 646304 648031 := bstep (se 1 (by rfl) ⟨486023, by rfl⟩ : syracuseStep 648031 = 972047) B972047
theorem B648059 : Blo 646304 648059 := bstep (se 1 (by rfl) ⟨486044, by rfl⟩ : syracuseStep 648059 = 972089) B972089
theorem B648111 : Blo 646304 648111 := bstep (se 1 (by rfl) ⟨486083, by rfl⟩ : syracuseStep 648111 = 972167) B972167
theorem B648135 : Blo 646304 648135 := bstep (se 1 (by rfl) ⟨486101, by rfl⟩ : syracuseStep 648135 = 972203) B972203
theorem B648155 : Blo 646304 648155 := bstep (se 1 (by rfl) ⟨486116, by rfl⟩ : syracuseStep 648155 = 972233) B972233
theorem B2188295 : Blo 646304 2188295 := bstep (se 1 (by rfl) ⟨1641221, by rfl⟩ : syracuseStep 2188295 = 3282443) B3282443
theorem B33743891 : Blo 646304 33743891 := bstep (se 1 (by rfl) ⟨25307918, by rfl⟩ : syracuseStep 33743891 = 50615837) B50615837
theorem B648231 : Blo 646304 648231 := bstep (se 1 (by rfl) ⟨486173, by rfl⟩ : syracuseStep 648231 = 972347) B972347
theorem B648271 : Blo 646304 648271 := bstep (se 1 (by rfl) ⟨486203, by rfl⟩ : syracuseStep 648271 = 972407) B972407
theorem B648287 : Blo 646304 648287 := bstep (se 1 (by rfl) ⟨486215, by rfl⟩ : syracuseStep 648287 = 972431) B972431
theorem B2188403 : Blo 646304 2188403 := bstep (se 1 (by rfl) ⟨1641302, by rfl⟩ : syracuseStep 2188403 = 3282605) B3282605
theorem B648315 : Blo 646304 648315 := bstep (se 1 (by rfl) ⟨486236, by rfl⟩ : syracuseStep 648315 = 972473) B972473
theorem B648367 : Blo 646304 648367 := bstep (se 1 (by rfl) ⟨486275, by rfl⟩ : syracuseStep 648367 = 972551) B972551
theorem B648391 : Blo 646304 648391 := bstep (se 1 (by rfl) ⟨486293, by rfl⟩ : syracuseStep 648391 = 972587) B972587
theorem B648411 : Blo 646304 648411 := bstep (se 1 (by rfl) ⟨486308, by rfl⟩ : syracuseStep 648411 = 972617) B972617
theorem B648487 : Blo 646304 648487 := bstep (se 1 (by rfl) ⟨486365, by rfl⟩ : syracuseStep 648487 = 972731) B972731
theorem B648527 : Blo 646304 648527 := bstep (se 1 (by rfl) ⟨486395, by rfl⟩ : syracuseStep 648527 = 972791) B972791
theorem B648543 : Blo 646304 648543 := bstep (se 1 (by rfl) ⟨486407, by rfl⟩ : syracuseStep 648543 = 972815) B972815
theorem B648571 : Blo 646304 648571 := bstep (se 1 (by rfl) ⟨486428, by rfl⟩ : syracuseStep 648571 = 972857) B972857
theorem B2188673 : Blo 646304 2188673 := bstep (se 2 (by rfl) ⟨820752, by rfl⟩ : syracuseStep 2188673 = 1641505) B1641505
theorem B648623 : Blo 646304 648623 := bstep (se 1 (by rfl) ⟨486467, by rfl⟩ : syracuseStep 648623 = 972935) B972935
theorem B648647 : Blo 646304 648647 := bstep (se 1 (by rfl) ⟨486485, by rfl⟩ : syracuseStep 648647 = 972971) B972971
theorem B648667 : Blo 646304 648667 := bstep (se 1 (by rfl) ⟨486500, by rfl⟩ : syracuseStep 648667 = 973001) B973001
theorem B648743 : Blo 646304 648743 := bstep (se 1 (by rfl) ⟨486557, by rfl⟩ : syracuseStep 648743 = 973115) B973115
theorem B648783 : Blo 646304 648783 := bstep (se 1 (by rfl) ⟨486587, by rfl⟩ : syracuseStep 648783 = 973175) B973175
theorem B648799 : Blo 646304 648799 := bstep (se 1 (by rfl) ⟨486599, by rfl⟩ : syracuseStep 648799 = 973199) B973199
theorem B648827 : Blo 646304 648827 := bstep (se 1 (by rfl) ⟨486620, by rfl⟩ : syracuseStep 648827 = 973241) B973241
theorem B648879 : Blo 646304 648879 := bstep (se 1 (by rfl) ⟨486659, by rfl⟩ : syracuseStep 648879 = 973319) B973319
theorem B648903 : Blo 646304 648903 := bstep (se 1 (by rfl) ⟨486677, by rfl⟩ : syracuseStep 648903 = 973355) B973355
theorem B648923 : Blo 646304 648923 := bstep (se 1 (by rfl) ⟨486692, by rfl⟩ : syracuseStep 648923 = 973385) B973385
theorem B648999 : Blo 646304 648999 := bstep (se 1 (by rfl) ⟨486749, by rfl⟩ : syracuseStep 648999 = 973499) B973499
theorem B649039 : Blo 646304 649039 := bstep (se 1 (by rfl) ⟨486779, by rfl⟩ : syracuseStep 649039 = 973559) B973559
theorem B649055 : Blo 646304 649055 := bstep (se 1 (by rfl) ⟨486791, by rfl⟩ : syracuseStep 649055 = 973583) B973583
theorem B649083 : Blo 646304 649083 := bstep (se 1 (by rfl) ⟨486812, by rfl⟩ : syracuseStep 649083 = 973625) B973625
theorem B649135 : Blo 646304 649135 := bstep (se 1 (by rfl) ⟨486851, by rfl⟩ : syracuseStep 649135 = 973703) B973703
theorem B649159 : Blo 646304 649159 := bstep (se 1 (by rfl) ⟨486869, by rfl⟩ : syracuseStep 649159 = 973739) B973739
theorem B649179 : Blo 646304 649179 := bstep (se 1 (by rfl) ⟨486884, by rfl⟩ : syracuseStep 649179 = 973769) B973769
theorem B2222095 : Blo 646304 2222095 := bstep (se 1 (by rfl) ⟨1666571, by rfl⟩ : syracuseStep 2222095 = 3333143) B3333143
theorem B4909085 : Blo 646304 4909085 := bstep (se 3 (by rfl) ⟨920453, by rfl⟩ : syracuseStep 4909085 = 1840907) B1840907
theorem B4155421 : Blo 646304 4155421 := bstep (se 3 (by rfl) ⟨779141, by rfl⟩ : syracuseStep 4155421 = 1558283) B1558283
theorem B649255 : Blo 646304 649255 := bstep (se 1 (by rfl) ⟨486941, by rfl⟩ : syracuseStep 649255 = 973883) B973883
theorem B649295 : Blo 646304 649295 := bstep (se 1 (by rfl) ⟨486971, by rfl⟩ : syracuseStep 649295 = 973943) B973943
theorem B649311 : Blo 646304 649311 := bstep (se 1 (by rfl) ⟨486983, by rfl⟩ : syracuseStep 649311 = 973967) B973967
theorem B1108091 : Blo 646304 1108091 := bstep (se 1 (by rfl) ⟨831068, by rfl⟩ : syracuseStep 1108091 = 1662137) B1662137
theorem B649339 : Blo 646304 649339 := bstep (se 1 (by rfl) ⟨487004, by rfl⟩ : syracuseStep 649339 = 974009) B974009
theorem B2189483 : Blo 646304 2189483 := bstep (se 1 (by rfl) ⟨1642112, by rfl⟩ : syracuseStep 2189483 = 3284225) B3284225
theorem B649391 : Blo 646304 649391 := bstep (se 1 (by rfl) ⟨487043, by rfl⟩ : syracuseStep 649391 = 974087) B974087
theorem B649415 : Blo 646304 649415 := bstep (se 1 (by rfl) ⟨487061, by rfl⟩ : syracuseStep 649415 = 974123) B974123
theorem B649435 : Blo 646304 649435 := bstep (se 1 (by rfl) ⟨487076, by rfl⟩ : syracuseStep 649435 = 974153) B974153
theorem B649511 : Blo 646304 649511 := bstep (se 1 (by rfl) ⟨487133, by rfl⟩ : syracuseStep 649511 = 974267) B974267
theorem B649551 : Blo 646304 649551 := bstep (se 1 (by rfl) ⟨487163, by rfl⟩ : syracuseStep 649551 = 974327) B974327
theorem B649567 : Blo 646304 649567 := bstep (se 1 (by rfl) ⟨487175, by rfl⟩ : syracuseStep 649567 = 974351) B974351
theorem B649595 : Blo 646304 649595 := bstep (se 1 (by rfl) ⟨487196, by rfl⟩ : syracuseStep 649595 = 974393) B974393
theorem B649647 : Blo 646304 649647 := bstep (se 1 (by rfl) ⟨487235, by rfl⟩ : syracuseStep 649647 = 974471) B974471
theorem B649671 : Blo 646304 649671 := bstep (se 1 (by rfl) ⟨487253, by rfl⟩ : syracuseStep 649671 = 974507) B974507
theorem B649691 : Blo 646304 649691 := bstep (se 1 (by rfl) ⟨487268, by rfl⟩ : syracuseStep 649691 = 974537) B974537
theorem B649767 : Blo 646304 649767 := bstep (se 1 (by rfl) ⟨487325, by rfl⟩ : syracuseStep 649767 = 974651) B974651
theorem B3500603 : Blo 646304 3500603 := bstep (se 1 (by rfl) ⟨2625452, by rfl⟩ : syracuseStep 3500603 = 5250905) B5250905
theorem B649807 : Blo 646304 649807 := bstep (se 1 (by rfl) ⟨487355, by rfl⟩ : syracuseStep 649807 = 974711) B974711
theorem B649823 : Blo 646304 649823 := bstep (se 1 (by rfl) ⟨487367, by rfl⟩ : syracuseStep 649823 = 974735) B974735
theorem B649851 : Blo 646304 649851 := bstep (se 1 (by rfl) ⟨487388, by rfl⟩ : syracuseStep 649851 = 974777) B974777
theorem B649903 : Blo 646304 649903 := bstep (se 1 (by rfl) ⟨487427, by rfl⟩ : syracuseStep 649903 = 974855) B974855
theorem B2190023 : Blo 646304 2190023 := bstep (se 1 (by rfl) ⟨1642517, by rfl⟩ : syracuseStep 2190023 = 3285035) B3285035
theorem B649927 : Blo 646304 649927 := bstep (se 1 (by rfl) ⟨487445, by rfl⟩ : syracuseStep 649927 = 974891) B974891
theorem B649947 : Blo 646304 649947 := bstep (se 1 (by rfl) ⟨487460, by rfl⟩ : syracuseStep 649947 = 974921) B974921
theorem B650023 : Blo 646304 650023 := bstep (se 1 (by rfl) ⟨487517, by rfl⟩ : syracuseStep 650023 = 975035) B975035
theorem B650063 : Blo 646304 650063 := bstep (se 1 (by rfl) ⟨487547, by rfl⟩ : syracuseStep 650063 = 975095) B975095
theorem B650079 : Blo 646304 650079 := bstep (se 1 (by rfl) ⟨487559, by rfl⟩ : syracuseStep 650079 = 975119) B975119
theorem B650107 : Blo 646304 650107 := bstep (se 1 (by rfl) ⟨487580, by rfl⟩ : syracuseStep 650107 = 975161) B975161
theorem B5532563 : Blo 646304 5532563 := bstep (se 1 (by rfl) ⟨4149422, by rfl⟩ : syracuseStep 5532563 = 8298845) B8298845
theorem B650159 : Blo 646304 650159 := bstep (se 1 (by rfl) ⟨487619, by rfl⟩ : syracuseStep 650159 = 975239) B975239
theorem B650183 : Blo 646304 650183 := bstep (se 1 (by rfl) ⟨487637, by rfl⟩ : syracuseStep 650183 = 975275) B975275
theorem B650203 : Blo 646304 650203 := bstep (se 1 (by rfl) ⟨487652, by rfl⟩ : syracuseStep 650203 = 975305) B975305
theorem B650279 : Blo 646304 650279 := bstep (se 1 (by rfl) ⟨487709, by rfl⟩ : syracuseStep 650279 = 975419) B975419
theorem B3501251 : Blo 646304 3501251 := bstep (se 1 (by rfl) ⟨2625938, by rfl⟩ : syracuseStep 3501251 = 5251877) B5251877
theorem B2190887 : Blo 646304 2190887 := bstep (se 1 (by rfl) ⟨1643165, by rfl⟩ : syracuseStep 2190887 = 3286331) B3286331
theorem B7892603 : Blo 646304 7892603 := bstep (se 1 (by rfl) ⟨5919452, by rfl⟩ : syracuseStep 7892603 = 11838905) B11838905
theorem B4484753 : Blo 646304 4484753 := bstep (se 2 (by rfl) ⟨1681782, by rfl⟩ : syracuseStep 4484753 = 3363565) B3363565
theorem B2190995 : Blo 646304 2190995 := bstep (se 1 (by rfl) ⟨1643246, by rfl⟩ : syracuseStep 2190995 = 3286493) B3286493
theorem B2191211 : Blo 646304 2191211 := bstep (se 1 (by rfl) ⟨1643408, by rfl⟩ : syracuseStep 2191211 = 3286817) B3286817
theorem B2191265 : Blo 646304 2191265 := bstep (se 2 (by rfl) ⟨821724, by rfl⟩ : syracuseStep 2191265 = 1643449) B1643449
theorem B4222979 : Blo 646304 4222979 := bstep (se 1 (by rfl) ⟨3167234, by rfl⟩ : syracuseStep 4222979 = 6334469) B6334469
theorem B3273047 : Blo 646304 3273047 := bstep (se 1 (by rfl) ⟨2454785, by rfl⟩ : syracuseStep 3273047 = 4909571) B4909571
theorem B2191859 : Blo 646304 2191859 := bstep (se 1 (by rfl) ⟨1643894, by rfl⟩ : syracuseStep 2191859 = 3287789) B3287789
theorem B2192399 : Blo 646304 2192399 := bstep (se 1 (by rfl) ⟨1644299, by rfl⟩ : syracuseStep 2192399 = 3288599) B3288599
theorem B73037155 : Blo 646304 73037155 := bstep (se 1 (by rfl) ⟨54777866, by rfl⟩ : syracuseStep 73037155 = 109555733) B109555733
theorem B2192993 : Blo 646304 2192993 := bstep (se 2 (by rfl) ⟨822372, by rfl⟩ : syracuseStep 2192993 = 1644745) B1644745
theorem B1636271 : Blo 646304 1636271 := bstep (se 1 (by rfl) ⟨1227203, by rfl⟩ : syracuseStep 1636271 = 2454407) B2454407
theorem B6649859 : Blo 646304 6649859 := bstep (se 1 (by rfl) ⟨4987394, by rfl⟩ : syracuseStep 6649859 = 9974789) B9974789
theorem B1112143 : Blo 646304 1112143 := bstep (se 1 (by rfl) ⟨834107, by rfl⟩ : syracuseStep 1112143 = 1668215) B1668215
theorem B3110993 : Blo 646304 3110993 := bstep (se 2 (by rfl) ⟨1166622, by rfl⟩ : syracuseStep 3110993 = 2333245) B2333245
theorem B2455667 : Blo 646304 2455667 := bstep (se 1 (by rfl) ⟨1841750, by rfl⟩ : syracuseStep 2455667 = 3683501) B3683501
theorem B4257949 : Blo 646304 4257949 := bstep (se 3 (by rfl) ⟨798365, by rfl⟩ : syracuseStep 4257949 = 1596731) B1596731
theorem B4913459 : Blo 646304 4913459 := bstep (se 1 (by rfl) ⟨3685094, by rfl⟩ : syracuseStep 4913459 = 7370189) B7370189
theorem B5929453 : Blo 646304 5929453 := bstep (se 3 (by rfl) ⟨1111772, by rfl⟩ : syracuseStep 5929453 = 2223545) B2223545
theorem B4749857 : Blo 646304 4749857 := bstep (se 2 (by rfl) ⟨1781196, by rfl⟩ : syracuseStep 4749857 = 3562393) B3562393
theorem B818095 : Blo 646304 818095 := bstep (se 1 (by rfl) ⟨613571, by rfl⟩ : syracuseStep 818095 = 1227143) B1227143
theorem B4979731 : Blo 646304 4979731 := bstep (se 1 (by rfl) ⟨3734798, by rfl⟩ : syracuseStep 4979731 = 7469597) B7469597
theorem B2194451 : Blo 646304 2194451 := bstep (se 1 (by rfl) ⟨1645838, by rfl⟩ : syracuseStep 2194451 = 3291677) B3291677
theorem B1637455 : Blo 646304 1637455 := bstep (se 1 (by rfl) ⟨1228091, by rfl⟩ : syracuseStep 1637455 = 2456183) B2456183
theorem B2194775 : Blo 646304 2194775 := bstep (se 1 (by rfl) ⟨1646081, by rfl⟩ : syracuseStep 2194775 = 3292163) B3292163
theorem B1638103 : Blo 646304 1638103 := bstep (se 1 (by rfl) ⟨1228577, by rfl⟩ : syracuseStep 1638103 = 2457155) B2457155
theorem B2457337 : Blo 646304 2457337 := bstep (se 2 (by rfl) ⟨921501, by rfl⟩ : syracuseStep 2457337 = 1843003) B1843003
theorem B3276611 : Blo 646304 3276611 := bstep (se 1 (by rfl) ⟨2457458, by rfl⟩ : syracuseStep 3276611 = 4914917) B4914917
theorem B1310537 : Blo 646304 1310537 := bstep (se 2 (by rfl) ⟨491451, by rfl⟩ : syracuseStep 1310537 = 982903) B982903
theorem B819163 : Blo 646304 819163 := bstep (se 1 (by rfl) ⟨614372, by rfl⟩ : syracuseStep 819163 = 1228745) B1228745
theorem B2457809 : Blo 646304 2457809 := bstep (se 2 (by rfl) ⟨921678, by rfl⟩ : syracuseStep 2457809 = 1843357) B1843357
theorem B819487 : Blo 646304 819487 := bstep (se 1 (by rfl) ⟨614615, by rfl⟩ : syracuseStep 819487 = 1229231) B1229231
theorem B7373105 : Blo 646304 7373105 := bstep (se 2 (by rfl) ⟨2764914, by rfl⟩ : syracuseStep 7373105 = 5529829) B5529829
theorem B3113491 : Blo 646304 3113491 := bstep (se 1 (by rfl) ⟨2335118, by rfl⟩ : syracuseStep 3113491 = 4670237) B4670237
theorem B2949785 : Blo 646304 2949785 := bstep (se 2 (by rfl) ⟨1106169, by rfl⟩ : syracuseStep 2949785 = 2212339) B2212339
theorem B2949803 : Blo 646304 2949803 := bstep (se 1 (by rfl) ⟨2212352, by rfl⟩ : syracuseStep 2949803 = 4424705) B4424705
theorem B2458295 : Blo 646304 2458295 := bstep (se 1 (by rfl) ⟨1843721, by rfl⟩ : syracuseStep 2458295 = 3687443) B3687443
theorem B1639187 : Blo 646304 1639187 := bstep (se 1 (by rfl) ⟨1229390, by rfl⟩ : syracuseStep 1639187 = 2458781) B2458781
theorem B6652817 : Blo 646304 6652817 := bstep (se 2 (by rfl) ⟨2494806, by rfl⟩ : syracuseStep 6652817 = 4989613) B4989613
theorem B1639399 : Blo 646304 1639399 := bstep (se 1 (by rfl) ⟨1229549, by rfl⟩ : syracuseStep 1639399 = 2459099) B2459099
theorem B1639673 : Blo 646304 1639673 := bstep (se 2 (by rfl) ⟨614877, by rfl⟩ : syracuseStep 1639673 = 1229755) B1229755
theorem B2459069 : Blo 646304 2459069 := bstep (se 3 (by rfl) ⟨461075, by rfl⟩ : syracuseStep 2459069 = 922151) B922151
theorem B3278393 : Blo 646304 3278393 := bstep (se 2 (by rfl) ⟨1229397, by rfl⟩ : syracuseStep 3278393 = 2458795) B2458795
theorem B3114683 : Blo 646304 3114683 := bstep (se 1 (by rfl) ⟨2336012, by rfl⟩ : syracuseStep 3114683 = 4672025) B4672025
theorem B1640321 : Blo 646304 1640321 := bstep (se 2 (by rfl) ⟨615120, by rfl⟩ : syracuseStep 1640321 = 1230241) B1230241
theorem B1313033 : Blo 646304 1313033 := bstep (se 2 (by rfl) ⟨492387, by rfl⟩ : syracuseStep 1313033 = 984775) B984775
theorem B2460071 : Blo 646304 2460071 := bstep (se 1 (by rfl) ⟨1845053, by rfl⟩ : syracuseStep 2460071 = 3690107) B3690107
theorem B821755 : Blo 646304 821755 := bstep (se 1 (by rfl) ⟨616316, by rfl⟩ : syracuseStep 821755 = 1232633) B1232633
theorem B1313351 : Blo 646304 1313351 := bstep (se 1 (by rfl) ⟨985013, by rfl⟩ : syracuseStep 1313351 = 1970027) B1970027
theorem B2460239 : Blo 646304 2460239 := bstep (se 1 (by rfl) ⟨1845179, by rfl⟩ : syracuseStep 2460239 = 3690359) B3690359
theorem B1641131 : Blo 646304 1641131 := bstep (se 1 (by rfl) ⟨1230848, by rfl⟩ : syracuseStep 1641131 = 2461697) B2461697
theorem B5540561 : Blo 646304 5540561 := bstep (se 2 (by rfl) ⟨2077710, by rfl⟩ : syracuseStep 5540561 = 4155421) B4155421
theorem B821983 : Blo 646304 821983 := bstep (se 1 (by rfl) ⟨616487, by rfl⟩ : syracuseStep 821983 = 1232975) B1232975
theorem B822727 : Blo 646304 822727 := bstep (se 1 (by rfl) ⟨617045, by rfl⟩ : syracuseStep 822727 = 1234091) B1234091
theorem B23662043 : Blo 646304 23662043 := bstep (se 1 (by rfl) ⟨17746532, by rfl⟩ : syracuseStep 23662043 = 35493065) B35493065
theorem B1641991 : Blo 646304 1641991 := bstep (se 1 (by rfl) ⟨1231493, by rfl⟩ : syracuseStep 1641991 = 2462987) B2462987
theorem B3280499 : Blo 646304 3280499 := bstep (se 1 (by rfl) ⟨2460374, by rfl⟩ : syracuseStep 3280499 = 4920749) B4920749
theorem B1642295 : Blo 646304 1642295 := bstep (se 1 (by rfl) ⟨1231721, by rfl⟩ : syracuseStep 1642295 = 2463443) B2463443
theorem B5902595 : Blo 646304 5902595 := bstep (se 1 (by rfl) ⟨4426946, by rfl⟩ : syracuseStep 5902595 = 8853893) B8853893
theorem B2494793 : Blo 646304 2494793 := bstep (se 2 (by rfl) ⟨935547, by rfl⟩ : syracuseStep 2494793 = 1871095) B1871095
theorem B6656431 : Blo 646304 6656431 := bstep (se 1 (by rfl) ⟨4992323, by rfl⟩ : syracuseStep 6656431 = 9984647) B9984647
theorem B1642963 : Blo 646304 1642963 := bstep (se 1 (by rfl) ⟨1232222, by rfl⟩ : syracuseStep 1642963 = 2464445) B2464445
theorem B2331155 : Blo 646304 2331155 := bstep (se 1 (by rfl) ⟨1748366, by rfl⟩ : syracuseStep 2331155 = 3496733) B3496733
theorem B692831 : Blo 646304 692831 := bstep (se 1 (by rfl) ⟨519623, by rfl⟩ : syracuseStep 692831 = 1039247) B1039247
theorem B18748057 : Blo 646304 18748057 := bstep (se 2 (by rfl) ⟨7030521, by rfl⟩ : syracuseStep 18748057 = 14061043) B14061043
theorem B8852429 : Blo 646304 8852429 := bstep (se 3 (by rfl) ⟨1659830, by rfl⟩ : syracuseStep 8852429 = 3319661) B3319661
theorem B2462683 : Blo 646304 2462683 := bstep (se 1 (by rfl) ⟨1847012, by rfl⟩ : syracuseStep 2462683 = 3694025) B3694025
theorem B3282119 : Blo 646304 3282119 := bstep (se 1 (by rfl) ⟨2461589, by rfl⟩ : syracuseStep 3282119 = 4923179) B4923179
theorem B1643753 : Blo 646304 1643753 := bstep (se 2 (by rfl) ⟨616407, by rfl⟩ : syracuseStep 1643753 = 1232815) B1232815
theorem B3282281 : Blo 646304 3282281 := bstep (se 2 (by rfl) ⟨1230855, by rfl⟩ : syracuseStep 3282281 = 2461711) B2461711
theorem B923017 : Blo 646304 923017 := bstep (se 2 (by rfl) ⟨346131, by rfl⟩ : syracuseStep 923017 = 692263) B692263
theorem B1643915 : Blo 646304 1643915 := bstep (se 1 (by rfl) ⟨1232936, by rfl⟩ : syracuseStep 1643915 = 2465873) B2465873
theorem B2954909 : Blo 646304 2954909 := bstep (se 3 (by rfl) ⟨554045, by rfl⟩ : syracuseStep 2954909 = 1108091) B1108091
theorem B8296181 : Blo 646304 8296181 := bstep (se 5 (by rfl) ⟨388883, by rfl⟩ : syracuseStep 8296181 = 777767) B777767
theorem B14030597 : Blo 646304 14030597 := bstep (se 4 (by rfl) ⟨1315368, by rfl⟩ : syracuseStep 14030597 = 2630737) B2630737
theorem B5543909 : Blo 646304 5543909 := bstep (se 4 (by rfl) ⟨519741, by rfl⟩ : syracuseStep 5543909 = 1039483) B1039483
theorem B2463929 : Blo 646304 2463929 := bstep (se 2 (by rfl) ⟨923973, by rfl⟩ : syracuseStep 2463929 = 1847947) B1847947
theorem B1644907 : Blo 646304 1644907 := bstep (se 1 (by rfl) ⟨1233680, by rfl⟩ : syracuseStep 1644907 = 2467361) B2467361
theorem B1841591 : Blo 646304 1841591 := bstep (se 1 (by rfl) ⟨1381193, by rfl⟩ : syracuseStep 1841591 = 2762387) B2762387
theorem B54073817 : Blo 646304 54073817 := bstep (se 2 (by rfl) ⟨20277681, by rfl⟩ : syracuseStep 54073817 = 40555363) B40555363
theorem B5905003 : Blo 646304 5905003 := bstep (se 1 (by rfl) ⟨4428752, by rfl⟩ : syracuseStep 5905003 = 8857505) B8857505
theorem B1645231 : Blo 646304 1645231 := bstep (se 1 (by rfl) ⟨1233923, by rfl⟩ : syracuseStep 1645231 = 2467847) B2467847
theorem B4660087 : Blo 646304 4660087 := bstep (se 1 (by rfl) ⟨3495065, by rfl⟩ : syracuseStep 4660087 = 6990131) B6990131
theorem B1645555 : Blo 646304 1645555 := bstep (se 1 (by rfl) ⟨1234166, by rfl⟩ : syracuseStep 1645555 = 2468333) B2468333
theorem B2333735 : Blo 646304 2333735 := bstep (se 1 (by rfl) ⟨1750301, by rfl⟩ : syracuseStep 2333735 = 3500603) B3500603
theorem B1842365 : Blo 646304 1842365 := bstep (se 3 (by rfl) ⟨345443, by rfl⟩ : syracuseStep 1842365 = 690887) B690887
theorem B924959 : Blo 646304 924959 := bstep (se 1 (by rfl) ⟨693719, by rfl⟩ : syracuseStep 924959 = 1387439) B1387439
theorem B1383817 : Blo 646304 1383817 := bstep (se 2 (by rfl) ⟨518931, by rfl⟩ : syracuseStep 1383817 = 1037863) B1037863
theorem B2334167 : Blo 646304 2334167 := bstep (se 1 (by rfl) ⟨1750625, by rfl⟩ : syracuseStep 2334167 = 3501251) B3501251
theorem B728671 : Blo 646304 728671 := bstep (se 1 (by rfl) ⟨546503, by rfl⟩ : syracuseStep 728671 = 1093007) B1093007
theorem B2989835 : Blo 646304 2989835 := bstep (se 1 (by rfl) ⟨2242376, by rfl⟩ : syracuseStep 2989835 = 4484753) B4484753
theorem B2760713 : Blo 646304 2760713 := bstep (se 2 (by rfl) ⟨1035267, by rfl⟩ : syracuseStep 2760713 = 2070535) B2070535
theorem B1482857 : Blo 646304 1482857 := bstep (se 2 (by rfl) ⟨556071, by rfl⟩ : syracuseStep 1482857 = 1112143) B1112143
theorem B5677265 : Blo 646304 5677265 := bstep (se 2 (by rfl) ⟨2128974, by rfl⟩ : syracuseStep 5677265 = 4257949) B4257949
theorem B31990081 : Blo 646304 31990081 := bstep (se 2 (by rfl) ⟨11996280, by rfl⟩ : syracuseStep 31990081 = 23992561) B23992561
theorem B1843631 : Blo 646304 1843631 := bstep (se 1 (by rfl) ⟨1382723, by rfl⟩ : syracuseStep 1843631 = 2765447) B2765447
theorem B2368001 : Blo 646304 2368001 := bstep (se 2 (by rfl) ⟨888000, by rfl⟩ : syracuseStep 2368001 = 1776001) B1776001
theorem B7905937 : Blo 646304 7905937 := bstep (se 2 (by rfl) ⟨2964726, by rfl⟩ : syracuseStep 7905937 = 5929453) B5929453
theorem B729823 : Blo 646304 729823 := bstep (se 1 (by rfl) ⟨547367, by rfl⟩ : syracuseStep 729823 = 1094735) B1094735
theorem B3286007 : Blo 646304 3286007 := bstep (se 1 (by rfl) ⟨2464505, by rfl⟩ : syracuseStep 3286007 = 4929011) B4929011
theorem B1090793 : Blo 646304 1090793 := bstep (se 2 (by rfl) ⟨409047, by rfl⟩ : syracuseStep 1090793 = 818095) B818095
theorem B1090847 : Blo 646304 1090847 := bstep (se 1 (by rfl) ⟨818135, by rfl⟩ : syracuseStep 1090847 = 1636271) B1636271
theorem B730399 : Blo 646304 730399 := bstep (se 1 (by rfl) ⟨547799, by rfl⟩ : syracuseStep 730399 = 1095599) B1095599
theorem B4433239 : Blo 646304 4433239 := bstep (se 1 (by rfl) ⟨3324929, by rfl⟩ : syracuseStep 4433239 = 6649859) B6649859
theorem B2073995 : Blo 646304 2073995 := bstep (se 1 (by rfl) ⟨1555496, by rfl⟩ : syracuseStep 2073995 = 3110993) B3110993
theorem B730687 : Blo 646304 730687 := bstep (se 1 (by rfl) ⟨548015, by rfl⟩ : syracuseStep 730687 = 1096031) B1096031
theorem B37824407 : Blo 646304 37824407 := bstep (se 1 (by rfl) ⟨28368305, by rfl⟩ : syracuseStep 37824407 = 56736611) B56736611
theorem B2337049 : Blo 646304 2337049 := bstep (se 2 (by rfl) ⟨876393, by rfl⟩ : syracuseStep 2337049 = 1752787) B1752787
theorem B20982077 : Blo 646304 20982077 := bstep (se 3 (by rfl) ⟨3934139, by rfl⟩ : syracuseStep 20982077 = 7868279) B7868279
theorem B731515 : Blo 646304 731515 := bstep (se 1 (by rfl) ⟨548636, by rfl⟩ : syracuseStep 731515 = 1097273) B1097273
theorem B11250049 : Blo 646304 11250049 := bstep (se 2 (by rfl) ⟨4218768, by rfl⟩ : syracuseStep 11250049 = 8437537) B8437537
theorem B1387003 : Blo 646304 1387003 := bstep (se 1 (by rfl) ⟨1040252, by rfl⟩ : syracuseStep 1387003 = 2080505) B2080505
theorem B1092217 : Blo 646304 1092217 := bstep (se 2 (by rfl) ⟨409581, by rfl⟩ : syracuseStep 1092217 = 819163) B819163
theorem B1092271 : Blo 646304 1092271 := bstep (se 1 (by rfl) ⟨819203, by rfl⟩ : syracuseStep 1092271 = 1638407) B1638407
theorem B3287951 : Blo 646304 3287951 := bstep (se 1 (by rfl) ⟨2465963, by rfl⟩ : syracuseStep 3287951 = 4931927) B4931927
theorem B2468987 : Blo 646304 2468987 := bstep (se 1 (by rfl) ⟨1851740, by rfl⟩ : syracuseStep 2468987 = 3703481) B3703481
theorem B699967 : Blo 646304 699967 := bstep (se 1 (by rfl) ⟨524975, by rfl⟩ : syracuseStep 699967 = 1049951) B1049951
theorem B3124831 : Blo 646304 3124831 := bstep (se 1 (by rfl) ⟨2343623, by rfl⟩ : syracuseStep 3124831 = 4687247) B4687247
theorem B831151 : Blo 646304 831151 := bstep (se 1 (by rfl) ⟨623363, by rfl⟩ : syracuseStep 831151 = 1246727) B1246727
theorem B1388267 : Blo 646304 1388267 := bstep (se 1 (by rfl) ⟨1041200, by rfl⟩ : syracuseStep 1388267 = 2082401) B2082401
theorem B1388335 : Blo 646304 1388335 := bstep (se 1 (by rfl) ⟨1041251, by rfl⟩ : syracuseStep 1388335 = 2082503) B2082503
theorem B1454291 : Blo 646304 1454291 := bstep (se 1 (by rfl) ⟨1090718, by rfl⟩ : syracuseStep 1454291 = 2181437) B2181437
theorem B1454345 : Blo 646304 1454345 := bstep (se 2 (by rfl) ⟨545379, by rfl⟩ : syracuseStep 1454345 = 1090759) B1090759
theorem B9318671 : Blo 646304 9318671 := bstep (se 1 (by rfl) ⟨6989003, by rfl⟩ : syracuseStep 9318671 = 13978007) B13978007
theorem B1093979 : Blo 646304 1093979 := bstep (se 1 (by rfl) ⟨820484, by rfl⟩ : syracuseStep 1093979 = 1640969) B1640969
theorem B2961755 : Blo 646304 2961755 := bstep (se 1 (by rfl) ⟨2221316, by rfl⟩ : syracuseStep 2961755 = 4442633) B4442633
theorem B1093999 : Blo 646304 1093999 := bstep (se 1 (by rfl) ⟨820499, by rfl⟩ : syracuseStep 1093999 = 1640999) B1640999
theorem B1454561 : Blo 646304 1454561 := bstep (se 2 (by rfl) ⟨545460, by rfl⟩ : syracuseStep 1454561 = 1090921) B1090921
theorem B1094215 : Blo 646304 1094215 := bstep (se 1 (by rfl) ⟨820661, by rfl⟩ : syracuseStep 1094215 = 1641323) B1641323
theorem B1847879 : Blo 646304 1847879 := bstep (se 1 (by rfl) ⟨1385909, by rfl⟩ : syracuseStep 1847879 = 2771819) B2771819
theorem B1454867 : Blo 646304 1454867 := bstep (se 1 (by rfl) ⟨1091150, by rfl⟩ : syracuseStep 1454867 = 2182301) B2182301
theorem B3290057 : Blo 646304 3290057 := bstep (se 2 (by rfl) ⟨1233771, by rfl⟩ : syracuseStep 3290057 = 2467543) B2467543
theorem B1094647 : Blo 646304 1094647 := bstep (se 1 (by rfl) ⟨820985, by rfl⟩ : syracuseStep 1094647 = 1641971) B1641971
theorem B4502585 : Blo 646304 4502585 := bstep (se 2 (by rfl) ⟨1688469, by rfl⟩ : syracuseStep 4502585 = 3376939) B3376939
theorem B1455227 : Blo 646304 1455227 := bstep (se 1 (by rfl) ⟨1091420, by rfl⟩ : syracuseStep 1455227 = 2182841) B2182841
theorem B1553651 : Blo 646304 1553651 := bstep (se 1 (by rfl) ⟨1165238, by rfl⟩ : syracuseStep 1553651 = 2330477) B2330477
theorem B1455353 : Blo 646304 1455353 := bstep (se 2 (by rfl) ⟨545757, by rfl⟩ : syracuseStep 1455353 = 1091515) B1091515
theorem B1094951 : Blo 646304 1094951 := bstep (se 1 (by rfl) ⟨821213, by rfl⟩ : syracuseStep 1094951 = 1642427) B1642427
theorem B2962793 : Blo 646304 2962793 := bstep (se 2 (by rfl) ⟨1111047, by rfl⟩ : syracuseStep 2962793 = 2222095) B2222095
theorem B1455497 : Blo 646304 1455497 := bstep (se 2 (by rfl) ⟨545811, by rfl⟩ : syracuseStep 1455497 = 1091623) B1091623
theorem B1455623 : Blo 646304 1455623 := bstep (se 1 (by rfl) ⟨1091717, by rfl⟩ : syracuseStep 1455623 = 2183435) B2183435
theorem B1455803 : Blo 646304 1455803 := bstep (se 1 (by rfl) ⟨1091852, by rfl⟩ : syracuseStep 1455803 = 2183705) B2183705
theorem B1095403 : Blo 646304 1095403 := bstep (se 1 (by rfl) ⟨821552, by rfl⟩ : syracuseStep 1095403 = 1643105) B1643105
theorem B1455929 : Blo 646304 1455929 := bstep (se 2 (by rfl) ⟨545973, by rfl⟩ : syracuseStep 1455929 = 1091947) B1091947
theorem B1456559 : Blo 646304 1456559 := bstep (se 1 (by rfl) ⟨1092419, by rfl⟩ : syracuseStep 1456559 = 2184839) B2184839
theorem B1456595 : Blo 646304 1456595 := bstep (se 1 (by rfl) ⟨1092446, by rfl⟩ : syracuseStep 1456595 = 2184893) B2184893
theorem B7092775 : Blo 646304 7092775 := bstep (se 1 (by rfl) ⟨5319581, by rfl⟩ : syracuseStep 7092775 = 10639163) B10639163
theorem B1456703 : Blo 646304 1456703 := bstep (se 1 (by rfl) ⟨1092527, by rfl⟩ : syracuseStep 1456703 = 2185055) B2185055
theorem B1456811 : Blo 646304 1456811 := bstep (se 1 (by rfl) ⟨1092608, by rfl⟩ : syracuseStep 1456811 = 2185217) B2185217
theorem B1096375 : Blo 646304 1096375 := bstep (se 1 (by rfl) ⟨822281, by rfl⟩ : syracuseStep 1096375 = 1644563) B1644563
theorem B35404613 : Blo 646304 35404613 := bstep (se 4 (by rfl) ⟨3319182, by rfl⟩ : syracuseStep 35404613 = 6638365) B6638365
theorem B14957389 : Blo 646304 14957389 := bstep (se 3 (by rfl) ⟨2804510, by rfl⟩ : syracuseStep 14957389 = 5609021) B5609021
theorem B1096679 : Blo 646304 1096679 := bstep (se 1 (by rfl) ⟨822509, by rfl⟩ : syracuseStep 1096679 = 1645019) B1645019
theorem B1457351 : Blo 646304 1457351 := bstep (se 1 (by rfl) ⟨1093013, by rfl⟩ : syracuseStep 1457351 = 2186027) B2186027
theorem B2768195 : Blo 646304 2768195 := bstep (se 1 (by rfl) ⟨2076146, by rfl⟩ : syracuseStep 2768195 = 4152293) B4152293
theorem B1457531 : Blo 646304 1457531 := bstep (se 1 (by rfl) ⟨1093148, by rfl⟩ : syracuseStep 1457531 = 2186297) B2186297
theorem B3161531 : Blo 646304 3161531 := bstep (se 1 (by rfl) ⟨2371148, by rfl⟩ : syracuseStep 3161531 = 4742297) B4742297
theorem B50609609 : Blo 646304 50609609 := bstep (se 2 (by rfl) ⟨18978603, by rfl⟩ : syracuseStep 50609609 = 37957207) B37957207
theorem B1457657 : Blo 646304 1457657 := bstep (se 2 (by rfl) ⟨546621, by rfl⟩ : syracuseStep 1457657 = 1093243) B1093243
theorem B3325465 : Blo 646304 3325465 := bstep (se 2 (by rfl) ⟨1247049, by rfl⟩ : syracuseStep 3325465 = 2494099) B2494099
theorem B1457747 : Blo 646304 1457747 := bstep (se 1 (by rfl) ⟨1093310, by rfl⟩ : syracuseStep 1457747 = 2186621) B2186621
theorem B1457927 : Blo 646304 1457927 := bstep (se 1 (by rfl) ⟨1093445, by rfl⟩ : syracuseStep 1457927 = 2186891) B2186891
theorem B1228601 : Blo 646304 1228601 := bstep (se 2 (by rfl) ⟨460725, by rfl⟩ : syracuseStep 1228601 = 921451) B921451
theorem B1752961 : Blo 646304 1752961 := bstep (se 2 (by rfl) ⟨657360, by rfl⟩ : syracuseStep 1752961 = 1314721) B1314721
theorem B1458539 : Blo 646304 1458539 := bstep (se 1 (by rfl) ⟨1093904, by rfl⟩ : syracuseStep 1458539 = 2187809) B2187809
theorem B1065383 : Blo 646304 1065383 := bstep (se 1 (by rfl) ⟨799037, by rfl⟩ : syracuseStep 1065383 = 1598075) B1598075
theorem B1458683 : Blo 646304 1458683 := bstep (se 1 (by rfl) ⟨1094012, by rfl⟩ : syracuseStep 1458683 = 2188025) B2188025
theorem B1458809 : Blo 646304 1458809 := bstep (se 2 (by rfl) ⟨547053, by rfl⟩ : syracuseStep 1458809 = 1094107) B1094107
theorem B13681325 : Blo 646304 13681325 := bstep (se 3 (by rfl) ⟨2565248, by rfl⟩ : syracuseStep 13681325 = 5130497) B5130497
theorem B1458863 : Blo 646304 1458863 := bstep (se 1 (by rfl) ⟨1094147, by rfl⟩ : syracuseStep 1458863 = 2188295) B2188295
theorem B22495927 : Blo 646304 22495927 := bstep (se 1 (by rfl) ⟨16871945, by rfl⟩ : syracuseStep 22495927 = 33743891) B33743891
theorem B1458935 : Blo 646304 1458935 := bstep (se 1 (by rfl) ⟨1094201, by rfl⟩ : syracuseStep 1458935 = 2188403) B2188403
theorem B1426331 : Blo 646304 1426331 := bstep (se 1 (by rfl) ⟨1069748, by rfl⟩ : syracuseStep 1426331 = 2139497) B2139497
theorem B1459115 : Blo 646304 1459115 := bstep (se 1 (by rfl) ⟨1094336, by rfl⟩ : syracuseStep 1459115 = 2188673) B2188673
theorem B1230203 : Blo 646304 1230203 := bstep (se 1 (by rfl) ⟨922652, by rfl⟩ : syracuseStep 1230203 = 1845305) B1845305
theorem B1459655 : Blo 646304 1459655 := bstep (se 1 (by rfl) ⟨1094741, by rfl⟩ : syracuseStep 1459655 = 2189483) B2189483
theorem B19908193 : Blo 646304 19908193 := bstep (se 2 (by rfl) ⟨7465572, by rfl⟩ : syracuseStep 19908193 = 14931145) B14931145
theorem B1460015 : Blo 646304 1460015 := bstep (se 1 (by rfl) ⟨1095011, by rfl⟩ : syracuseStep 1460015 = 2190023) B2190023
theorem B2770793 : Blo 646304 2770793 := bstep (se 2 (by rfl) ⟨1039047, by rfl⟩ : syracuseStep 2770793 = 2078095) B2078095
theorem B3950441 : Blo 646304 3950441 := bstep (se 2 (by rfl) ⟨1481415, by rfl⟩ : syracuseStep 3950441 = 2962831) B2962831
theorem B1755037 : Blo 646304 1755037 := bstep (se 3 (by rfl) ⟨329069, by rfl⟩ : syracuseStep 1755037 = 658139) B658139
theorem B3688375 : Blo 646304 3688375 := bstep (se 1 (by rfl) ⟨2766281, by rfl⟩ : syracuseStep 3688375 = 5532563) B5532563
theorem B1755145 : Blo 646304 1755145 := bstep (se 2 (by rfl) ⟨658179, by rfl⟩ : syracuseStep 1755145 = 1316359) B1316359
theorem B6998309 : Blo 646304 6998309 := bstep (se 4 (by rfl) ⟨656091, by rfl⟩ : syracuseStep 6998309 = 1312183) B1312183
theorem B1460591 : Blo 646304 1460591 := bstep (se 1 (by rfl) ⟨1095443, by rfl⟩ : syracuseStep 1460591 = 2190887) B2190887
theorem B5261735 : Blo 646304 5261735 := bstep (se 1 (by rfl) ⟨3946301, by rfl⟩ : syracuseStep 5261735 = 7892603) B7892603
theorem B1460663 : Blo 646304 1460663 := bstep (se 1 (by rfl) ⟨1095497, by rfl⟩ : syracuseStep 1460663 = 2190995) B2190995
theorem B1460807 : Blo 646304 1460807 := bstep (se 1 (by rfl) ⟨1095605, by rfl⟩ : syracuseStep 1460807 = 2191211) B2191211
theorem B1231433 : Blo 646304 1231433 := bstep (se 2 (by rfl) ⟨461787, by rfl⟩ : syracuseStep 1231433 = 923575) B923575
theorem B1460843 : Blo 646304 1460843 := bstep (se 1 (by rfl) ⟨1095632, by rfl⟩ : syracuseStep 1460843 = 2191265) B2191265
theorem B969551 : Blo 646304 969551 := bstep (se 1 (by rfl) ⟨727163, by rfl⟩ : syracuseStep 969551 = 1454327) B1454327
theorem B2182031 : Blo 646304 2182031 := bstep (se 1 (by rfl) ⟨1636523, by rfl⟩ : syracuseStep 2182031 = 3273047) B3273047
theorem B1461239 : Blo 646304 1461239 := bstep (se 1 (by rfl) ⟨1095929, by rfl⟩ : syracuseStep 1461239 = 2191859) B2191859
theorem B969947 : Blo 646304 969947 := bstep (se 1 (by rfl) ⟨727460, by rfl⟩ : syracuseStep 969947 = 1454921) B1454921
theorem B1461599 : Blo 646304 1461599 := bstep (se 1 (by rfl) ⟨1096199, by rfl⟩ : syracuseStep 1461599 = 2192399) B2192399
theorem B970121 : Blo 646304 970121 := bstep (se 2 (by rfl) ⟨363795, by rfl⟩ : syracuseStep 970121 = 727591) B727591
theorem B970475 : Blo 646304 970475 := bstep (se 1 (by rfl) ⟨727856, by rfl⟩ : syracuseStep 970475 = 1455713) B1455713
theorem B1461995 : Blo 646304 1461995 := bstep (se 1 (by rfl) ⟨1096496, by rfl⟩ : syracuseStep 1461995 = 2192993) B2192993
theorem B17747747 : Blo 646304 17747747 := bstep (se 1 (by rfl) ⟨13310810, by rfl⟩ : syracuseStep 17747747 = 26621621) B26621621
theorem B1462121 : Blo 646304 1462121 := bstep (se 2 (by rfl) ⟨548295, by rfl⟩ : syracuseStep 1462121 = 1096591) B1096591
theorem B970703 : Blo 646304 970703 := bstep (se 1 (by rfl) ⟨728027, by rfl⟩ : syracuseStep 970703 = 1456055) B1456055
theorem B6639641 : Blo 646304 6639641 := bstep (se 2 (by rfl) ⟨2489865, by rfl⟩ : syracuseStep 6639641 = 4979731) B4979731
theorem B2183273 : Blo 646304 2183273 := bstep (se 2 (by rfl) ⟨818727, by rfl⟩ : syracuseStep 2183273 = 1637455) B1637455
theorem B10670339 : Blo 646304 10670339 := bstep (se 1 (by rfl) ⟨8002754, by rfl⟩ : syracuseStep 10670339 = 16005509) B16005509
theorem B971099 : Blo 646304 971099 := bstep (se 1 (by rfl) ⟨728324, by rfl⟩ : syracuseStep 971099 = 1456649) B1456649
theorem B3166571 : Blo 646304 3166571 := bstep (se 1 (by rfl) ⟨2374928, by rfl⟩ : syracuseStep 3166571 = 4749857) B4749857
theorem B1233377 : Blo 646304 1233377 := bstep (se 2 (by rfl) ⟨462516, by rfl⟩ : syracuseStep 1233377 = 925033) B925033
theorem B971327 : Blo 646304 971327 := bstep (se 1 (by rfl) ⟨728495, by rfl⟩ : syracuseStep 971327 = 1456991) B1456991
theorem B971447 : Blo 646304 971447 := bstep (se 1 (by rfl) ⟨728585, by rfl⟩ : syracuseStep 971447 = 1457171) B1457171
theorem B1462967 : Blo 646304 1462967 := bstep (se 1 (by rfl) ⟨1097225, by rfl⟩ : syracuseStep 1462967 = 2194451) B2194451
theorem B3494765 : Blo 646304 3494765 := bstep (se 3 (by rfl) ⟨655268, by rfl⟩ : syracuseStep 3494765 = 1310537) B1310537
theorem B1463183 : Blo 646304 1463183 := bstep (se 1 (by rfl) ⟨1097387, by rfl⟩ : syracuseStep 1463183 = 2194775) B2194775
theorem B971675 : Blo 646304 971675 := bstep (se 1 (by rfl) ⟨728756, by rfl⟩ : syracuseStep 971675 = 1457513) B1457513
theorem B2184137 : Blo 646304 2184137 := bstep (se 2 (by rfl) ⟨819051, by rfl⟩ : syracuseStep 2184137 = 1638103) B1638103
theorem B1561723 : Blo 646304 1561723 := bstep (se 1 (by rfl) ⟨1171292, by rfl⟩ : syracuseStep 1561723 = 2342585) B2342585
theorem B2184407 : Blo 646304 2184407 := bstep (se 1 (by rfl) ⟨1638305, by rfl⟩ : syracuseStep 2184407 = 3276611) B3276611
theorem B5002489 : Blo 646304 5002489 := bstep (se 2 (by rfl) ⟨1875933, by rfl⟩ : syracuseStep 5002489 = 3751867) B3751867
theorem B972071 : Blo 646304 972071 := bstep (se 1 (by rfl) ⟨729053, by rfl⟩ : syracuseStep 972071 = 1458107) B1458107
theorem B1234273 : Blo 646304 1234273 := bstep (se 2 (by rfl) ⟨462852, by rfl⟩ : syracuseStep 1234273 = 925705) B925705
theorem B972155 : Blo 646304 972155 := bstep (se 1 (by rfl) ⟨729116, by rfl⟩ : syracuseStep 972155 = 1458233) B1458233
theorem B972281 : Blo 646304 972281 := bstep (se 2 (by rfl) ⟨364605, by rfl⟩ : syracuseStep 972281 = 729211) B729211
theorem B972383 : Blo 646304 972383 := bstep (se 1 (by rfl) ⟨729287, by rfl⟩ : syracuseStep 972383 = 1458575) B1458575
theorem B6248123 : Blo 646304 6248123 := bstep (se 1 (by rfl) ⟨4686092, by rfl⟩ : syracuseStep 6248123 = 9372185) B9372185
theorem B12474101 : Blo 646304 12474101 := bstep (se 5 (by rfl) ⟨584723, by rfl⟩ : syracuseStep 12474101 = 1169447) B1169447
theorem B972599 : Blo 646304 972599 := bstep (se 1 (by rfl) ⟨729449, by rfl⟩ : syracuseStep 972599 = 1458899) B1458899
theorem B5855161 : Blo 646304 5855161 := bstep (se 2 (by rfl) ⟨2195685, by rfl⟩ : syracuseStep 5855161 = 4391371) B4391371
theorem B121690133 : Blo 646304 121690133 := bstep (se 6 (by rfl) ⟨2852112, by rfl⟩ : syracuseStep 121690133 = 5704225) B5704225
theorem B972905 : Blo 646304 972905 := bstep (se 2 (by rfl) ⟨364839, by rfl⟩ : syracuseStep 972905 = 729679) B729679
theorem B2775235 : Blo 646304 2775235 := bstep (se 1 (by rfl) ⟨2081426, by rfl⟩ : syracuseStep 2775235 = 4162853) B4162853
theorem B874729 : Blo 646304 874729 := bstep (se 2 (by rfl) ⟨328023, by rfl⟩ : syracuseStep 874729 = 656047) B656047
theorem B12474647 : Blo 646304 12474647 := bstep (se 1 (by rfl) ⟨9355985, by rfl⟩ : syracuseStep 12474647 = 18711971) B18711971
theorem B1038683 : Blo 646304 1038683 := bstep (se 1 (by rfl) ⟨779012, by rfl⟩ : syracuseStep 1038683 = 1558025) B1558025
theorem B973223 : Blo 646304 973223 := bstep (se 1 (by rfl) ⟨729917, by rfl⟩ : syracuseStep 973223 = 1459835) B1459835
theorem B39836087 : Blo 646304 39836087 := bstep (se 1 (by rfl) ⟨29877065, by rfl⟩ : syracuseStep 39836087 = 59754131) B59754131
theorem B973307 : Blo 646304 973307 := bstep (se 1 (by rfl) ⟨729980, by rfl⟩ : syracuseStep 973307 = 1459961) B1459961
theorem B973433 : Blo 646304 973433 := bstep (se 2 (by rfl) ⟨365037, by rfl⟩ : syracuseStep 973433 = 730075) B730075
theorem B973487 : Blo 646304 973487 := bstep (se 1 (by rfl) ⟨730115, by rfl⟩ : syracuseStep 973487 = 1460231) B1460231
theorem B973535 : Blo 646304 973535 := bstep (se 1 (by rfl) ⟨730151, by rfl⟩ : syracuseStep 973535 = 1460303) B1460303
theorem B14015375 : Blo 646304 14015375 := bstep (se 1 (by rfl) ⟨10511531, by rfl⟩ : syracuseStep 14015375 = 21023063) B21023063
theorem B973799 : Blo 646304 973799 := bstep (se 1 (by rfl) ⟨730349, by rfl⟩ : syracuseStep 973799 = 1460699) B1460699
theorem B1203175 : Blo 646304 1203175 := bstep (se 1 (by rfl) ⟨902381, by rfl⟩ : syracuseStep 1203175 = 1804763) B1804763
theorem B2186459 : Blo 646304 2186459 := bstep (se 1 (by rfl) ⟨1639844, by rfl⟩ : syracuseStep 2186459 = 3279689) B3279689
theorem B974057 : Blo 646304 974057 := bstep (se 2 (by rfl) ⟨365271, by rfl⟩ : syracuseStep 974057 = 730543) B730543
theorem B646431 : Blo 646304 646431 := bstep (se 1 (by rfl) ⟨484823, by rfl⟩ : syracuseStep 646431 = 969647) B969647
theorem B974111 : Blo 646304 974111 := bstep (se 1 (by rfl) ⟨730583, by rfl⟩ : syracuseStep 974111 = 1461167) B1461167
theorem B646491 : Blo 646304 646491 := bstep (se 1 (by rfl) ⟨484868, by rfl⟩ : syracuseStep 646491 = 969737) B969737
theorem B646511 : Blo 646304 646511 := bstep (se 1 (by rfl) ⟨484883, by rfl⟩ : syracuseStep 646511 = 969767) B969767
theorem B646567 : Blo 646304 646567 := bstep (se 1 (by rfl) ⟨484925, by rfl⟩ : syracuseStep 646567 = 969851) B969851
theorem B974279 : Blo 646304 974279 := bstep (se 1 (by rfl) ⟨730709, by rfl⟩ : syracuseStep 974279 = 1461419) B1461419
theorem B646651 : Blo 646304 646651 := bstep (se 1 (by rfl) ⟨484988, by rfl⟩ : syracuseStep 646651 = 969977) B969977
theorem B646719 : Blo 646304 646719 := bstep (se 1 (by rfl) ⟨485039, by rfl⟩ : syracuseStep 646719 = 970079) B970079
theorem B646727 : Blo 646304 646727 := bstep (se 1 (by rfl) ⟨485045, by rfl⟩ : syracuseStep 646727 = 970091) B970091
theorem B646879 : Blo 646304 646879 := bstep (se 1 (by rfl) ⟨485159, by rfl⟩ : syracuseStep 646879 = 970319) B970319
theorem B1171207 : Blo 646304 1171207 := bstep (se 1 (by rfl) ⟨878405, by rfl⟩ : syracuseStep 1171207 = 1756811) B1756811
theorem B18013985 : Blo 646304 18013985 := bstep (se 2 (by rfl) ⟨6755244, by rfl⟩ : syracuseStep 18013985 = 13510489) B13510489
theorem B974633 : Blo 646304 974633 := bstep (se 2 (by rfl) ⟨365487, by rfl⟩ : syracuseStep 974633 = 730975) B730975
theorem B646959 : Blo 646304 646959 := bstep (se 1 (by rfl) ⟨485219, by rfl⟩ : syracuseStep 646959 = 970439) B970439
theorem B974639 : Blo 646304 974639 := bstep (se 1 (by rfl) ⟨730979, by rfl⟩ : syracuseStep 974639 = 1461959) B1461959
theorem B647067 : Blo 646304 647067 := bstep (se 1 (by rfl) ⟨485300, by rfl⟩ : syracuseStep 647067 = 970601) B970601
theorem B647119 : Blo 646304 647119 := bstep (se 1 (by rfl) ⟨485339, by rfl⟩ : syracuseStep 647119 = 970679) B970679
theorem B647143 : Blo 646304 647143 := bstep (se 1 (by rfl) ⟨485357, by rfl⟩ : syracuseStep 647143 = 970715) B970715
theorem B14049287 : Blo 646304 14049287 := bstep (se 1 (by rfl) ⟨10536965, by rfl⟩ : syracuseStep 14049287 = 21073931) B21073931
theorem B2187323 : Blo 646304 2187323 := bstep (se 1 (by rfl) ⟨1640492, by rfl⟩ : syracuseStep 2187323 = 3280985) B3280985
theorem B3498137 : Blo 646304 3498137 := bstep (se 2 (by rfl) ⟨1311801, by rfl⟩ : syracuseStep 3498137 = 2623603) B2623603
theorem B975113 : Blo 646304 975113 := bstep (se 2 (by rfl) ⟨365667, by rfl⟩ : syracuseStep 975113 = 731335) B731335
theorem B647455 : Blo 646304 647455 := bstep (se 1 (by rfl) ⟨485591, by rfl⟩ : syracuseStep 647455 = 971183) B971183
theorem B2187593 : Blo 646304 2187593 := bstep (se 2 (by rfl) ⟨820347, by rfl⟩ : syracuseStep 2187593 = 1640695) B1640695
theorem B647515 : Blo 646304 647515 := bstep (se 1 (by rfl) ⟨485636, by rfl⟩ : syracuseStep 647515 = 971273) B971273
theorem B647535 : Blo 646304 647535 := bstep (se 1 (by rfl) ⟨485651, by rfl⟩ : syracuseStep 647535 = 971303) B971303
theorem B975215 : Blo 646304 975215 := bstep (se 1 (by rfl) ⟨731411, by rfl⟩ : syracuseStep 975215 = 1462823) B1462823
theorem B647591 : Blo 646304 647591 := bstep (se 1 (by rfl) ⟨485693, by rfl⟩ : syracuseStep 647591 = 971387) B971387
theorem B4219337 : Blo 646304 4219337 := bstep (se 2 (by rfl) ⟨1582251, by rfl⟩ : syracuseStep 4219337 = 3164503) B3164503
theorem B647675 : Blo 646304 647675 := bstep (se 1 (by rfl) ⟨485756, by rfl⟩ : syracuseStep 647675 = 971513) B971513
theorem B647743 : Blo 646304 647743 := bstep (se 1 (by rfl) ⟨485807, by rfl⟩ : syracuseStep 647743 = 971615) B971615
theorem B647751 : Blo 646304 647751 := bstep (se 1 (by rfl) ⟨485813, by rfl⟩ : syracuseStep 647751 = 971627) B971627
theorem B975431 : Blo 646304 975431 := bstep (se 1 (by rfl) ⟨731573, by rfl⟩ : syracuseStep 975431 = 1463147) B1463147
theorem B647903 : Blo 646304 647903 := bstep (se 1 (by rfl) ⟨485927, by rfl⟩ : syracuseStep 647903 = 971855) B971855
theorem B647983 : Blo 646304 647983 := bstep (se 1 (by rfl) ⟨485987, by rfl⟩ : syracuseStep 647983 = 971975) B971975
theorem B648091 : Blo 646304 648091 := bstep (se 1 (by rfl) ⟨486068, by rfl⟩ : syracuseStep 648091 = 972137) B972137
theorem B648143 : Blo 646304 648143 := bstep (se 1 (by rfl) ⟨486107, by rfl⟩ : syracuseStep 648143 = 972215) B972215
theorem B648167 : Blo 646304 648167 := bstep (se 1 (by rfl) ⟨486125, by rfl⟩ : syracuseStep 648167 = 972251) B972251
theorem B3105917 : Blo 646304 3105917 := bstep (se 3 (by rfl) ⟨582359, by rfl⟩ : syracuseStep 3105917 = 1164719) B1164719
theorem B648479 : Blo 646304 648479 := bstep (se 1 (by rfl) ⟨486359, by rfl⟩ : syracuseStep 648479 = 972719) B972719
theorem B648539 : Blo 646304 648539 := bstep (se 1 (by rfl) ⟨486404, by rfl⟩ : syracuseStep 648539 = 972809) B972809
theorem B648559 : Blo 646304 648559 := bstep (se 1 (by rfl) ⟨486419, by rfl⟩ : syracuseStep 648559 = 972839) B972839
theorem B3335585 : Blo 646304 3335585 := bstep (se 2 (by rfl) ⟨1250844, by rfl⟩ : syracuseStep 3335585 = 2501689) B2501689
theorem B648615 : Blo 646304 648615 := bstep (se 1 (by rfl) ⟨486461, by rfl⟩ : syracuseStep 648615 = 972923) B972923
theorem B779719 : Blo 646304 779719 := bstep (se 1 (by rfl) ⟨584789, by rfl⟩ : syracuseStep 779719 = 1169579) B1169579
theorem B648699 : Blo 646304 648699 := bstep (se 1 (by rfl) ⟨486524, by rfl⟩ : syracuseStep 648699 = 973049) B973049
theorem B648767 : Blo 646304 648767 := bstep (se 1 (by rfl) ⟨486575, by rfl⟩ : syracuseStep 648767 = 973151) B973151
theorem B648775 : Blo 646304 648775 := bstep (se 1 (by rfl) ⟨486581, by rfl⟩ : syracuseStep 648775 = 973163) B973163
theorem B648927 : Blo 646304 648927 := bstep (se 1 (by rfl) ⟨486695, by rfl⟩ : syracuseStep 648927 = 973391) B973391
theorem B649007 : Blo 646304 649007 := bstep (se 1 (by rfl) ⟨486755, by rfl⟩ : syracuseStep 649007 = 973511) B973511
theorem B878383 : Blo 646304 878383 := bstep (se 1 (by rfl) ⟨658787, by rfl⟩ : syracuseStep 878383 = 1317575) B1317575
theorem B649115 : Blo 646304 649115 := bstep (se 1 (by rfl) ⟨486836, by rfl⟩ : syracuseStep 649115 = 973673) B973673
theorem B649167 : Blo 646304 649167 := bstep (se 1 (by rfl) ⟨486875, by rfl⟩ : syracuseStep 649167 = 973751) B973751
theorem B649191 : Blo 646304 649191 := bstep (se 1 (by rfl) ⟨486893, by rfl⟩ : syracuseStep 649191 = 973787) B973787
theorem B649503 : Blo 646304 649503 := bstep (se 1 (by rfl) ⟨487127, by rfl⟩ : syracuseStep 649503 = 974255) B974255
theorem B649563 : Blo 646304 649563 := bstep (se 1 (by rfl) ⟨487172, by rfl⟩ : syracuseStep 649563 = 974345) B974345
theorem B649583 : Blo 646304 649583 := bstep (se 1 (by rfl) ⟨487187, by rfl⟩ : syracuseStep 649583 = 974375) B974375
theorem B649639 : Blo 646304 649639 := bstep (se 1 (by rfl) ⟨487229, by rfl⟩ : syracuseStep 649639 = 974459) B974459
theorem B649723 : Blo 646304 649723 := bstep (se 1 (by rfl) ⟨487292, by rfl⟩ : syracuseStep 649723 = 974585) B974585
theorem B649791 : Blo 646304 649791 := bstep (se 1 (by rfl) ⟨487343, by rfl⟩ : syracuseStep 649791 = 974687) B974687
theorem B649799 : Blo 646304 649799 := bstep (se 1 (by rfl) ⟨487349, by rfl⟩ : syracuseStep 649799 = 974699) B974699
theorem B649951 : Blo 646304 649951 := bstep (se 1 (by rfl) ⟨487463, by rfl⟩ : syracuseStep 649951 = 974927) B974927
theorem B650031 : Blo 646304 650031 := bstep (se 1 (by rfl) ⟨487523, by rfl⟩ : syracuseStep 650031 = 975047) B975047
theorem B650139 : Blo 646304 650139 := bstep (se 1 (by rfl) ⟨487604, by rfl⟩ : syracuseStep 650139 = 975209) B975209
theorem B650191 : Blo 646304 650191 := bstep (se 1 (by rfl) ⟨487643, by rfl⟩ : syracuseStep 650191 = 975287) B975287
theorem B650215 : Blo 646304 650215 := bstep (se 1 (by rfl) ⟨487661, by rfl⟩ : syracuseStep 650215 = 975323) B975323
theorem B4156703 : Blo 646304 4156703 := bstep (se 1 (by rfl) ⟨3117527, by rfl⟩ : syracuseStep 4156703 = 6235055) B6235055
theorem B2190779 : Blo 646304 2190779 := bstep (se 1 (by rfl) ⟨1643084, by rfl⟩ : syracuseStep 2190779 = 3286169) B3286169
theorem B3108377 : Blo 646304 3108377 := bstep (se 2 (by rfl) ⟨1165641, by rfl⟩ : syracuseStep 3108377 = 2331283) B2331283
theorem B1011295 : Blo 646304 1011295 := bstep (se 1 (by rfl) ⟨758471, by rfl⟩ : syracuseStep 1011295 = 1516943) B1516943
theorem B3272723 : Blo 646304 3272723 := bstep (se 1 (by rfl) ⟨2454542, by rfl⟩ : syracuseStep 3272723 = 4909085) B4909085
theorem B97382873 : Blo 646304 97382873 := bstep (se 2 (by rfl) ⟨36518577, by rfl⟩ : syracuseStep 97382873 = 73037155) B73037155
theorem B2454239 : Blo 646304 2454239 := bstep (se 1 (by rfl) ⟨1840679, by rfl⟩ : syracuseStep 2454239 = 3681359) B3681359
theorem B6222905 : Blo 646304 6222905 := bstep (se 2 (by rfl) ⟨2333589, by rfl⟩ : syracuseStep 6222905 = 4667179) B4667179
theorem B3699857 : Blo 646304 3699857 := bstep (se 2 (by rfl) ⟨1387446, by rfl⟩ : syracuseStep 3699857 = 2774893) B2774893
theorem B2815319 : Blo 646304 2815319 := bstep (se 1 (by rfl) ⟨2111489, by rfl⟩ : syracuseStep 2815319 = 4222979) B4222979
theorem B2454893 : Blo 646304 2454893 := bstep (se 3 (by rfl) ⟨460292, by rfl⟩ : syracuseStep 2454893 = 920585) B920585
theorem B2454907 : Blo 646304 2454907 := bstep (se 1 (by rfl) ⟨1841180, by rfl⟩ : syracuseStep 2454907 = 3682361) B3682361
theorem B1637111 : Blo 646304 1637111 := bstep (se 1 (by rfl) ⟨1227833, by rfl⟩ : syracuseStep 1637111 = 2455667) B2455667
theorem B3275639 : Blo 646304 3275639 := bstep (se 1 (by rfl) ⟨2456729, by rfl⟩ : syracuseStep 3275639 = 4913459) B4913459
theorem B1637729 : Blo 646304 1637729 := bstep (se 2 (by rfl) ⟨614148, by rfl⟩ : syracuseStep 1637729 = 1228297) B1228297
theorem B3276449 : Blo 646304 3276449 := bstep (se 2 (by rfl) ⟨1228668, by rfl⟩ : syracuseStep 3276449 = 2457337) B2457337
theorem B2457323 : Blo 646304 2457323 := bstep (se 1 (by rfl) ⟨1842992, by rfl⟩ : syracuseStep 2457323 = 3685985) B3685985
theorem B3505967 : Blo 646304 3505967 := bstep (se 1 (by rfl) ⟨2629475, by rfl⟩ : syracuseStep 3505967 = 5258951) B5258951
theorem B1638539 : Blo 646304 1638539 := bstep (se 1 (by rfl) ⟨1228904, by rfl⟩ : syracuseStep 1638539 = 2457809) B2457809
theorem B4915403 : Blo 646304 4915403 := bstep (se 1 (by rfl) ⟨3686552, by rfl⟩ : syracuseStep 4915403 = 7373105) B7373105
theorem B1966523 : Blo 646304 1966523 := bstep (se 1 (by rfl) ⟨1474892, by rfl⟩ : syracuseStep 1966523 = 2949785) B2949785
theorem B1966535 : Blo 646304 1966535 := bstep (se 1 (by rfl) ⟨1474901, by rfl⟩ : syracuseStep 1966535 = 2949803) B2949803
theorem B1638863 : Blo 646304 1638863 := bstep (se 1 (by rfl) ⟨1229147, by rfl⟩ : syracuseStep 1638863 = 2458295) B2458295
theorem B950887 : Blo 646304 950887 := bstep (se 1 (by rfl) ⟨713165, by rfl⟩ : syracuseStep 950887 = 1426331) B1426331
theorem B820135 : Blo 646304 820135 := bstep (se 1 (by rfl) ⟨615101, by rfl⟩ : syracuseStep 820135 = 1230203) B1230203
theorem B1639379 : Blo 646304 1639379 := bstep (se 1 (by rfl) ⟨1229534, by rfl⟩ : syracuseStep 1639379 = 2459069) B2459069
theorem B1640047 : Blo 646304 1640047 := bstep (se 1 (by rfl) ⟨1230035, by rfl⟩ : syracuseStep 1640047 = 2460071) B2460071
theorem B3507823 : Blo 646304 3507823 := bstep (se 1 (by rfl) ⟨2630867, by rfl⟩ : syracuseStep 3507823 = 5261735) B5261735
theorem B820955 : Blo 646304 820955 := bstep (se 1 (by rfl) ⟨615716, by rfl⟩ : syracuseStep 820955 = 1231433) B1231433
theorem B1640159 : Blo 646304 1640159 := bstep (se 1 (by rfl) ⟨1230119, by rfl⟩ : syracuseStep 1640159 = 2460239) B2460239
theorem B26544257 : Blo 646304 26544257 := bstep (se 2 (by rfl) ⟨9954096, by rfl⟩ : syracuseStep 26544257 = 19908193) B19908193
theorem B11831831 : Blo 646304 11831831 := bstep (se 1 (by rfl) ⟨8873873, by rfl⟩ : syracuseStep 11831831 = 17747747) B17747747
theorem B4917833 : Blo 646304 4917833 := bstep (se 2 (by rfl) ⟨1844187, by rfl⟩ : syracuseStep 4917833 = 3688375) B3688375
theorem B4426427 : Blo 646304 4426427 := bstep (se 1 (by rfl) ⟨3319820, by rfl⟩ : syracuseStep 4426427 = 6639641) B6639641
theorem B3935063 : Blo 646304 3935063 := bstep (se 1 (by rfl) ⟨2951297, by rfl⟩ : syracuseStep 3935063 = 5902595) B5902595
theorem B822251 : Blo 646304 822251 := bstep (se 1 (by rfl) ⟨616688, by rfl⟩ : syracuseStep 822251 = 1233377) B1233377
theorem B3116065 : Blo 646304 3116065 := bstep (se 2 (by rfl) ⟨1168524, by rfl⟩ : syracuseStep 3116065 = 2337049) B2337049
theorem B2329843 : Blo 646304 2329843 := bstep (se 1 (by rfl) ⟨1747382, by rfl⟩ : syracuseStep 2329843 = 3494765) B3494765
theorem B5901619 : Blo 646304 5901619 := bstep (se 1 (by rfl) ⟨4426214, by rfl⟩ : syracuseStep 5901619 = 8852429) B8852429
theorem B1969939 : Blo 646304 1969939 := bstep (se 1 (by rfl) ⟨1477454, by rfl⟩ : syracuseStep 1969939 = 2954909) B2954909
theorem B4165415 : Blo 646304 4165415 := bstep (se 1 (by rfl) ⟨3124061, by rfl⟩ : syracuseStep 4165415 = 6248123) B6248123
theorem B1642619 : Blo 646304 1642619 := bstep (se 1 (by rfl) ⟨1231964, by rfl⟩ : syracuseStep 1642619 = 2463929) B2463929
theorem B36049211 : Blo 646304 36049211 := bstep (se 1 (by rfl) ⟨27036908, by rfl⟩ : syracuseStep 36049211 = 54073817) B54073817
theorem B9343583 : Blo 646304 9343583 := bstep (se 1 (by rfl) ⟨7007687, by rfl⟩ : syracuseStep 9343583 = 14015375) B14015375
theorem B1348393 : Blo 646304 1348393 := bstep (se 2 (by rfl) ⟨505647, by rfl⟩ : syracuseStep 1348393 = 1011295) B1011295
theorem B4166441 : Blo 646304 4166441 := bstep (se 2 (by rfl) ⟨1562415, by rfl⟩ : syracuseStep 4166441 = 3124831) B3124831
theorem B1840475 : Blo 646304 1840475 := bstep (se 1 (by rfl) ⟨1380356, by rfl⟩ : syracuseStep 1840475 = 2760713) B2760713
theorem B988571 : Blo 646304 988571 := bstep (se 1 (by rfl) ⟨741428, by rfl⟩ : syracuseStep 988571 = 1482857) B1482857
theorem B2332091 : Blo 646304 2332091 := bstep (se 1 (by rfl) ⟨1749068, by rfl⟩ : syracuseStep 2332091 = 3498137) B3498137
theorem B8329189 : Blo 646304 8329189 := bstep (se 4 (by rfl) ⟨780861, by rfl⟩ : syracuseStep 8329189 = 1561723) B1561723
theorem B2070611 : Blo 646304 2070611 := bstep (se 1 (by rfl) ⟨1552958, by rfl⟩ : syracuseStep 2070611 = 3105917) B3105917
theorem B727195 : Blo 646304 727195 := bstep (se 1 (by rfl) ⟨545396, by rfl⟩ : syracuseStep 727195 = 1090793) B1090793
theorem B727231 : Blo 646304 727231 := bstep (se 1 (by rfl) ⟨545423, by rfl⟩ : syracuseStep 727231 = 1090847) B1090847
theorem B1382663 : Blo 646304 1382663 := bstep (se 1 (by rfl) ⟨1036997, by rfl⟩ : syracuseStep 1382663 = 2073995) B2073995
theorem B3283577 : Blo 646304 3283577 := bstep (se 2 (by rfl) ⟨1231341, by rfl⟩ : syracuseStep 3283577 = 2462683) B2462683
theorem B1645697 : Blo 646304 1645697 := bstep (se 2 (by rfl) ⟨617136, by rfl⟩ : syracuseStep 1645697 = 1234273) B1234273
theorem B1645991 : Blo 646304 1645991 := bstep (se 1 (by rfl) ⟨1234493, by rfl⟩ : syracuseStep 1645991 = 2468987) B2468987
theorem B2072251 : Blo 646304 2072251 := bstep (se 1 (by rfl) ⟨1554188, by rfl⟩ : syracuseStep 2072251 = 3108377) B3108377
theorem B925511 : Blo 646304 925511 := bstep (se 1 (by rfl) ⟨694133, by rfl⟩ : syracuseStep 925511 = 1388267) B1388267
theorem B7806881 : Blo 646304 7806881 := bstep (se 2 (by rfl) ⟨2927580, by rfl⟩ : syracuseStep 7806881 = 5855161) B5855161
theorem B729319 : Blo 646304 729319 := bstep (se 1 (by rfl) ⟨546989, by rfl⟩ : syracuseStep 729319 = 1093979) B1093979
theorem B1974503 : Blo 646304 1974503 := bstep (se 1 (by rfl) ⟨1480877, by rfl⟩ : syracuseStep 1974503 = 2961755) B2961755
theorem B64921915 : Blo 646304 64921915 := bstep (se 1 (by rfl) ⟨48691436, by rfl⟩ : syracuseStep 64921915 = 97382873) B97382873
theorem B2466557 : Blo 646304 2466557 := bstep (se 3 (by rfl) ⟨462479, by rfl⟩ : syracuseStep 2466557 = 924959) B924959
theorem B2466571 : Blo 646304 2466571 := bstep (se 1 (by rfl) ⟨1849928, by rfl⟩ : syracuseStep 2466571 = 3699857) B3699857
theorem B7873337 : Blo 646304 7873337 := bstep (se 2 (by rfl) ⟨2952501, by rfl⟩ : syracuseStep 7873337 = 5905003) B5905003
theorem B7381853 : Blo 646304 7381853 := bstep (se 3 (by rfl) ⟨1384097, by rfl⟩ : syracuseStep 7381853 = 2768195) B2768195
theorem B729967 : Blo 646304 729967 := bstep (se 1 (by rfl) ⟨547475, by rfl⟩ : syracuseStep 729967 = 1094951) B1094951
theorem B1876879 : Blo 646304 1876879 := bstep (se 1 (by rfl) ⟨1407659, by rfl⟩ : syracuseStep 1876879 = 2815319) B2815319
theorem B1975195 : Blo 646304 1975195 := bstep (se 1 (by rfl) ⟨1481396, by rfl⟩ : syracuseStep 1975195 = 2962793) B2962793
theorem B4432805 : Blo 646304 4432805 := bstep (se 4 (by rfl) ⟨415575, by rfl⟩ : syracuseStep 4432805 = 831151) B831151
theorem B8430749 : Blo 646304 8430749 := bstep (se 3 (by rfl) ⟨1580765, by rfl⟩ : syracuseStep 8430749 = 3161531) B3161531
theorem B1091407 : Blo 646304 1091407 := bstep (se 1 (by rfl) ⟨818555, by rfl⟩ : syracuseStep 1091407 = 1637111) B1637111
theorem B1845089 : Blo 646304 1845089 := bstep (se 2 (by rfl) ⟨691908, by rfl⟩ : syracuseStep 1845089 = 1383817) B1383817
theorem B23603075 : Blo 646304 23603075 := bstep (se 1 (by rfl) ⟨17702306, by rfl⟩ : syracuseStep 23603075 = 35404613) B35404613
theorem B731119 : Blo 646304 731119 := bstep (se 1 (by rfl) ⟨548339, by rfl⟩ : syracuseStep 731119 = 1096679) B1096679
theorem B4433953 : Blo 646304 4433953 := bstep (se 2 (by rfl) ⟨1662732, by rfl⟩ : syracuseStep 4433953 = 3325465) B3325465
theorem B1091819 : Blo 646304 1091819 := bstep (se 1 (by rfl) ⟨818864, by rfl⟩ : syracuseStep 1091819 = 1637729) B1637729
theorem B2337281 : Blo 646304 2337281 := bstep (se 2 (by rfl) ⟨876480, by rfl⟩ : syracuseStep 2337281 = 1752961) B1752961
theorem B2337311 : Blo 646304 2337311 := bstep (se 1 (by rfl) ⟨1752983, by rfl⟩ : syracuseStep 2337311 = 3505967) B3505967
theorem B1092649 : Blo 646304 1092649 := bstep (se 2 (by rfl) ⟨409743, by rfl⟩ : syracuseStep 1092649 = 819487) B819487
theorem B9120883 : Blo 646304 9120883 := bstep (se 1 (by rfl) ⟨6840662, by rfl⟩ : syracuseStep 9120883 = 13681325) B13681325
theorem B1092791 : Blo 646304 1092791 := bstep (se 1 (by rfl) ⟨819593, by rfl⟩ : syracuseStep 1092791 = 1639187) B1639187
theorem B4435211 : Blo 646304 4435211 := bstep (se 1 (by rfl) ⟨3326408, by rfl⟩ : syracuseStep 4435211 = 6652817) B6652817
theorem B28454237 : Blo 646304 28454237 := bstep (se 3 (by rfl) ⟨5335169, by rfl⟩ : syracuseStep 28454237 = 10670339) B10670339
theorem B1093115 : Blo 646304 1093115 := bstep (se 1 (by rfl) ⟨819836, by rfl⟩ : syracuseStep 1093115 = 1639673) B1639673
theorem B29994569 : Blo 646304 29994569 := bstep (se 2 (by rfl) ⟨11247963, by rfl⟩ : syracuseStep 29994569 = 22495927) B22495927
theorem B2076455 : Blo 646304 2076455 := bstep (se 1 (by rfl) ⟨1557341, by rfl⟩ : syracuseStep 2076455 = 3114683) B3114683
theorem B11251565 : Blo 646304 11251565 := bstep (se 3 (by rfl) ⟨2109668, by rfl⟩ : syracuseStep 11251565 = 4219337) B4219337
theorem B4665221 : Blo 646304 4665221 := bstep (se 4 (by rfl) ⟨437364, by rfl⟩ : syracuseStep 4665221 = 874729) B874729
theorem B1847195 : Blo 646304 1847195 := bstep (se 1 (by rfl) ⟨1385396, by rfl⟩ : syracuseStep 1847195 = 2770793) B2770793
theorem B2633627 : Blo 646304 2633627 := bstep (se 1 (by rfl) ⟨1975220, by rfl⟩ : syracuseStep 2633627 = 3950441) B3950441
theorem B1093547 : Blo 646304 1093547 := bstep (se 1 (by rfl) ⟨820160, by rfl⟩ : syracuseStep 1093547 = 1640321) B1640321
theorem B4665539 : Blo 646304 4665539 := bstep (se 1 (by rfl) ⟨3499154, by rfl⟩ : syracuseStep 4665539 = 6998309) B6998309
theorem B1847549 : Blo 646304 1847549 := bstep (se 3 (by rfl) ⟨346415, by rfl⟩ : syracuseStep 1847549 = 692831) B692831
theorem B1094087 : Blo 646304 1094087 := bstep (se 1 (by rfl) ⟨820565, by rfl⟩ : syracuseStep 1094087 = 1641131) B1641131
theorem B5910985 : Blo 646304 5910985 := bstep (se 2 (by rfl) ⟨2216619, by rfl⟩ : syracuseStep 5910985 = 4433239) B4433239
theorem B1454687 : Blo 646304 1454687 := bstep (se 1 (by rfl) ⟨1091015, by rfl⟩ : syracuseStep 1454687 = 2182031) B2182031
theorem B15774695 : Blo 646304 15774695 := bstep (se 1 (by rfl) ⟨11831021, by rfl⟩ : syracuseStep 15774695 = 23662043) B23662043
theorem B1094863 : Blo 646304 1094863 := bstep (se 1 (by rfl) ⟨821147, by rfl⟩ : syracuseStep 1094863 = 1642295) B1642295
theorem B2340049 : Blo 646304 2340049 := bstep (se 2 (by rfl) ⟨877518, by rfl⟩ : syracuseStep 2340049 = 1755037) B1755037
theorem B2340193 : Blo 646304 2340193 := bstep (se 2 (by rfl) ⟨877572, by rfl⟩ : syracuseStep 2340193 = 1755145) B1755145
theorem B1455515 : Blo 646304 1455515 := bstep (se 1 (by rfl) ⟨1091636, by rfl⟩ : syracuseStep 1455515 = 2183273) B2183273
theorem B14005685 : Blo 646304 14005685 := bstep (se 5 (by rfl) ⟨656516, by rfl⟩ : syracuseStep 14005685 = 1313033) B1313033
theorem B12006893 : Blo 646304 12006893 := bstep (se 3 (by rfl) ⟨2251292, by rfl⟩ : syracuseStep 12006893 = 4502585) B4502585
theorem B1554103 : Blo 646304 1554103 := bstep (se 1 (by rfl) ⟨1165577, by rfl⟩ : syracuseStep 1554103 = 2331155) B2331155
theorem B1456091 : Blo 646304 1456091 := bstep (se 1 (by rfl) ⟨1092068, by rfl⟩ : syracuseStep 1456091 = 2184137) B2184137
theorem B1095673 : Blo 646304 1095673 := bstep (se 2 (by rfl) ⟨410877, by rfl⟩ : syracuseStep 1095673 = 821755) B821755
theorem B1849337 : Blo 646304 1849337 := bstep (se 2 (by rfl) ⟨693501, by rfl⟩ : syracuseStep 1849337 = 1387003) B1387003
theorem B1456271 : Blo 646304 1456271 := bstep (se 1 (by rfl) ⟨1092203, by rfl⟩ : syracuseStep 1456271 = 2184407) B2184407
theorem B1095835 : Blo 646304 1095835 := bstep (se 1 (by rfl) ⟨821876, by rfl⟩ : syracuseStep 1095835 = 1643753) B1643753
theorem B1456289 : Blo 646304 1456289 := bstep (se 2 (by rfl) ⟨546108, by rfl⟩ : syracuseStep 1456289 = 1092217) B1092217
theorem B1456361 : Blo 646304 1456361 := bstep (se 2 (by rfl) ⟨546135, by rfl⟩ : syracuseStep 1456361 = 1092271) B1092271
theorem B1095943 : Blo 646304 1095943 := bstep (se 1 (by rfl) ⟨821957, by rfl⟩ : syracuseStep 1095943 = 1643915) B1643915
theorem B1095977 : Blo 646304 1095977 := bstep (se 2 (by rfl) ⟨410991, by rfl⟩ : syracuseStep 1095977 = 821983) B821983
theorem B8894893 : Blo 646304 8894893 := bstep (se 3 (by rfl) ⟨1667792, by rfl⟩ : syracuseStep 8894893 = 3335585) B3335585
theorem B9353731 : Blo 646304 9353731 := bstep (se 1 (by rfl) ⟨7015298, by rfl⟩ : syracuseStep 9353731 = 14030597) B14030597
theorem B1227727 : Blo 646304 1227727 := bstep (se 1 (by rfl) ⟨920795, by rfl⟩ : syracuseStep 1227727 = 1841591) B1841591
theorem B26557391 : Blo 646304 26557391 := bstep (se 1 (by rfl) ⟨19918043, by rfl⟩ : syracuseStep 26557391 = 39836087) B39836087
theorem B1096969 : Blo 646304 1096969 := bstep (se 2 (by rfl) ⟨411363, by rfl⟩ : syracuseStep 1096969 = 822727) B822727
theorem B1555823 : Blo 646304 1555823 := bstep (se 1 (by rfl) ⟨1166867, by rfl⟩ : syracuseStep 1555823 = 2333735) B2333735
theorem B933289 : Blo 646304 933289 := bstep (se 2 (by rfl) ⟨349983, by rfl⟩ : syracuseStep 933289 = 699967) B699967
theorem B1457639 : Blo 646304 1457639 := bstep (se 1 (by rfl) ⟨1093229, by rfl⟩ : syracuseStep 1457639 = 2186459) B2186459
theorem B1556111 : Blo 646304 1556111 := bstep (se 1 (by rfl) ⟨1167083, by rfl⟩ : syracuseStep 1556111 = 2334167) B2334167
theorem B1851113 : Blo 646304 1851113 := bstep (se 2 (by rfl) ⟨694167, by rfl⟩ : syracuseStep 1851113 = 1388335) B1388335
theorem B12009323 : Blo 646304 12009323 := bstep (se 1 (by rfl) ⟨9006992, by rfl⟩ : syracuseStep 12009323 = 18013985) B18013985
theorem B1458215 : Blo 646304 1458215 := bstep (se 1 (by rfl) ⟨1093661, by rfl⟩ : syracuseStep 1458215 = 2187323) B2187323
theorem B3784843 : Blo 646304 3784843 := bstep (se 1 (by rfl) ⟨2838632, by rfl⟩ : syracuseStep 3784843 = 5677265) B5677265
theorem B1458395 : Blo 646304 1458395 := bstep (se 1 (by rfl) ⟨1093796, by rfl⟩ : syracuseStep 1458395 = 2187593) B2187593
theorem B1229087 : Blo 646304 1229087 := bstep (se 1 (by rfl) ⟨921815, by rfl⟩ : syracuseStep 1229087 = 1843631) B1843631
theorem B1458665 : Blo 646304 1458665 := bstep (se 2 (by rfl) ⟨546999, by rfl⟩ : syracuseStep 1458665 = 1093999) B1093999
theorem B1458953 : Blo 646304 1458953 := bstep (se 2 (by rfl) ⟨547107, by rfl⟩ : syracuseStep 1458953 = 1094215) B1094215
theorem B2769821 : Blo 646304 2769821 := bstep (se 3 (by rfl) ⟨519341, by rfl⟩ : syracuseStep 2769821 = 1038683) B1038683
theorem B25216271 : Blo 646304 25216271 := bstep (se 1 (by rfl) ⟨18912203, by rfl⟩ : syracuseStep 25216271 = 37824407) B37824407
theorem B1459529 : Blo 646304 1459529 := bstep (se 2 (by rfl) ⟨547323, by rfl⟩ : syracuseStep 1459529 = 1094647) B1094647
theorem B6669985 : Blo 646304 6669985 := bstep (se 2 (by rfl) ⟨2501244, by rfl⟩ : syracuseStep 6669985 = 5002489) B5002489
theorem B1230689 : Blo 646304 1230689 := bstep (se 2 (by rfl) ⟨461508, by rfl⟩ : syracuseStep 1230689 = 923017) B923017
theorem B2771135 : Blo 646304 2771135 := bstep (se 1 (by rfl) ⟨2078351, by rfl⟩ : syracuseStep 2771135 = 4156703) B4156703
theorem B1460519 : Blo 646304 1460519 := bstep (se 1 (by rfl) ⟨1095389, by rfl⟩ : syracuseStep 1460519 = 2190779) B2190779
theorem B1460537 : Blo 646304 1460537 := bstep (se 2 (by rfl) ⟨547701, by rfl⟩ : syracuseStep 1460537 = 1095403) B1095403
theorem B2181815 : Blo 646304 2181815 := bstep (se 1 (by rfl) ⟨1636361, by rfl⟩ : syracuseStep 2181815 = 3272723) B3272723
theorem B969527 : Blo 646304 969527 := bstep (se 1 (by rfl) ⟨727145, by rfl⟩ : syracuseStep 969527 = 1454291) B1454291
theorem B969563 : Blo 646304 969563 := bstep (se 1 (by rfl) ⟨727172, by rfl⟩ : syracuseStep 969563 = 1454345) B1454345
theorem B6212447 : Blo 646304 6212447 := bstep (se 1 (by rfl) ⟨4659335, by rfl⟩ : syracuseStep 6212447 = 9318671) B9318671
theorem B969707 : Blo 646304 969707 := bstep (se 1 (by rfl) ⟨727280, by rfl⟩ : syracuseStep 969707 = 1454561) B1454561
theorem B1231919 : Blo 646304 1231919 := bstep (se 1 (by rfl) ⟨923939, by rfl⟩ : syracuseStep 1231919 = 1847879) B1847879
theorem B969911 : Blo 646304 969911 := bstep (se 1 (by rfl) ⟨727433, by rfl⟩ : syracuseStep 969911 = 1454867) B1454867
theorem B4148603 : Blo 646304 4148603 := bstep (se 1 (by rfl) ⟨3111452, by rfl⟩ : syracuseStep 4148603 = 6222905) B6222905
theorem B9457033 : Blo 646304 9457033 := bstep (se 2 (by rfl) ⟨3546387, by rfl⟩ : syracuseStep 9457033 = 7092775) B7092775
theorem B970151 : Blo 646304 970151 := bstep (se 1 (by rfl) ⟨727613, by rfl⟩ : syracuseStep 970151 = 1455227) B1455227
theorem B1035767 : Blo 646304 1035767 := bstep (se 1 (by rfl) ⟨776825, by rfl⟩ : syracuseStep 1035767 = 1553651) B1553651
theorem B970235 : Blo 646304 970235 := bstep (se 1 (by rfl) ⟨727676, by rfl⟩ : syracuseStep 970235 = 1455353) B1455353
theorem B1461833 : Blo 646304 1461833 := bstep (se 2 (by rfl) ⟨548187, by rfl⟩ : syracuseStep 1461833 = 1096375) B1096375
theorem B970331 : Blo 646304 970331 := bstep (se 1 (by rfl) ⟨727748, by rfl⟩ : syracuseStep 970331 = 1455497) B1455497
theorem B970415 : Blo 646304 970415 := bstep (se 1 (by rfl) ⟨727811, by rfl⟩ : syracuseStep 970415 = 1455623) B1455623
theorem B19943185 : Blo 646304 19943185 := bstep (se 2 (by rfl) ⟨7478694, by rfl⟩ : syracuseStep 19943185 = 14957389) B14957389
theorem B970535 : Blo 646304 970535 := bstep (se 1 (by rfl) ⟨727901, by rfl⟩ : syracuseStep 970535 = 1455803) B1455803
theorem B6213449 : Blo 646304 6213449 := bstep (se 2 (by rfl) ⟨2330043, by rfl⟩ : syracuseStep 6213449 = 4660087) B4660087
theorem B970619 : Blo 646304 970619 := bstep (se 1 (by rfl) ⟨727964, by rfl⟩ : syracuseStep 970619 = 1455929) B1455929
theorem B971039 : Blo 646304 971039 := bstep (se 1 (by rfl) ⟨728279, by rfl⟩ : syracuseStep 971039 = 1456559) B1456559
theorem B971063 : Blo 646304 971063 := bstep (se 1 (by rfl) ⟨728297, by rfl⟩ : syracuseStep 971063 = 1456595) B1456595
theorem B971135 : Blo 646304 971135 := bstep (se 1 (by rfl) ⟨728351, by rfl⟩ : syracuseStep 971135 = 1456703) B1456703
theorem B971207 : Blo 646304 971207 := bstep (se 1 (by rfl) ⟨728405, by rfl⟩ : syracuseStep 971207 = 1456811) B1456811
theorem B2183759 : Blo 646304 2183759 := bstep (se 1 (by rfl) ⟨1637819, by rfl⟩ : syracuseStep 2183759 = 3275639) B3275639
theorem B971561 : Blo 646304 971561 := bstep (se 2 (by rfl) ⟨364335, by rfl⟩ : syracuseStep 971561 = 728671) B728671
theorem B971567 : Blo 646304 971567 := bstep (se 1 (by rfl) ⟨728675, by rfl⟩ : syracuseStep 971567 = 1457351) B1457351
theorem B971687 : Blo 646304 971687 := bstep (se 1 (by rfl) ⟨728765, by rfl⟩ : syracuseStep 971687 = 1457531) B1457531
theorem B33739739 : Blo 646304 33739739 := bstep (se 1 (by rfl) ⟨25304804, by rfl⟩ : syracuseStep 33739739 = 50609609) B50609609
theorem B971771 : Blo 646304 971771 := bstep (se 1 (by rfl) ⟨728828, by rfl⟩ : syracuseStep 971771 = 1457657) B1457657
theorem B1561609 : Blo 646304 1561609 := bstep (se 2 (by rfl) ⟨585603, by rfl⟩ : syracuseStep 1561609 = 1171207) B1171207
theorem B971831 : Blo 646304 971831 := bstep (se 1 (by rfl) ⟨728873, by rfl⟩ : syracuseStep 971831 = 1457747) B1457747
theorem B2184299 : Blo 646304 2184299 := bstep (se 1 (by rfl) ⟨1638224, by rfl⟩ : syracuseStep 2184299 = 3276449) B3276449
theorem B971951 : Blo 646304 971951 := bstep (se 1 (by rfl) ⟨728963, by rfl⟩ : syracuseStep 971951 = 1457927) B1457927
theorem B972359 : Blo 646304 972359 := bstep (se 1 (by rfl) ⟨729269, by rfl⟩ : syracuseStep 972359 = 1458539) B1458539
theorem B710255 : Blo 646304 710255 := bstep (se 1 (by rfl) ⟨532691, by rfl⟩ : syracuseStep 710255 = 1065383) B1065383
theorem B972455 : Blo 646304 972455 := bstep (se 1 (by rfl) ⟨729341, by rfl⟩ : syracuseStep 972455 = 1458683) B1458683
theorem B972539 : Blo 646304 972539 := bstep (se 1 (by rfl) ⟨729404, by rfl⟩ : syracuseStep 972539 = 1458809) B1458809
theorem B42653441 : Blo 646304 42653441 := bstep (se 2 (by rfl) ⟨15995040, by rfl⟩ : syracuseStep 42653441 = 31990081) B31990081
theorem B972575 : Blo 646304 972575 := bstep (se 1 (by rfl) ⟨729431, by rfl⟩ : syracuseStep 972575 = 1458863) B1458863
theorem B972623 : Blo 646304 972623 := bstep (se 1 (by rfl) ⟨729467, by rfl⟩ : syracuseStep 972623 = 1458935) B1458935
theorem B972743 : Blo 646304 972743 := bstep (se 1 (by rfl) ⟨729557, by rfl⟩ : syracuseStep 972743 = 1459115) B1459115
theorem B4151321 : Blo 646304 4151321 := bstep (se 2 (by rfl) ⟨1556745, by rfl⟩ : syracuseStep 4151321 = 3113491) B3113491
theorem B10541249 : Blo 646304 10541249 := bstep (se 2 (by rfl) ⟨3952968, by rfl⟩ : syracuseStep 10541249 = 7905937) B7905937
theorem B8444189 : Blo 646304 8444189 := bstep (se 3 (by rfl) ⟨1583285, by rfl⟩ : syracuseStep 8444189 = 3166571) B3166571
theorem B973097 : Blo 646304 973097 := bstep (se 2 (by rfl) ⟨364911, by rfl⟩ : syracuseStep 973097 = 729823) B729823
theorem B973103 : Blo 646304 973103 := bstep (se 1 (by rfl) ⟨729827, by rfl⟩ : syracuseStep 973103 = 1459655) B1459655
theorem B2185595 : Blo 646304 2185595 := bstep (se 1 (by rfl) ⟨1639196, by rfl⟩ : syracuseStep 2185595 = 3278393) B3278393
theorem B973343 : Blo 646304 973343 := bstep (se 1 (by rfl) ⟨730007, by rfl⟩ : syracuseStep 973343 = 1460015) B1460015
theorem B2185865 : Blo 646304 2185865 := bstep (se 2 (by rfl) ⟨819699, by rfl⟩ : syracuseStep 2185865 = 1639399) B1639399
theorem B6314669 : Blo 646304 6314669 := bstep (se 3 (by rfl) ⟨1184000, by rfl⟩ : syracuseStep 6314669 = 2368001) B2368001
theorem B973727 : Blo 646304 973727 := bstep (se 1 (by rfl) ⟨730295, by rfl⟩ : syracuseStep 973727 = 1460591) B1460591
theorem B973775 : Blo 646304 973775 := bstep (se 1 (by rfl) ⟨730331, by rfl⟩ : syracuseStep 973775 = 1460663) B1460663
theorem B973865 : Blo 646304 973865 := bstep (se 2 (by rfl) ⟨365199, by rfl⟩ : syracuseStep 973865 = 730399) B730399
theorem B875567 : Blo 646304 875567 := bstep (se 1 (by rfl) ⟨656675, by rfl⟩ : syracuseStep 875567 = 1313351) B1313351
theorem B973871 : Blo 646304 973871 := bstep (se 1 (by rfl) ⟨730403, by rfl⟩ : syracuseStep 973871 = 1460807) B1460807
theorem B973895 : Blo 646304 973895 := bstep (se 1 (by rfl) ⟨730421, by rfl⟩ : syracuseStep 973895 = 1460843) B1460843
theorem B3693707 : Blo 646304 3693707 := bstep (se 1 (by rfl) ⟨2770280, by rfl⟩ : syracuseStep 3693707 = 5540561) B5540561
theorem B646367 : Blo 646304 646367 := bstep (se 1 (by rfl) ⟨484775, by rfl⟩ : syracuseStep 646367 = 969551) B969551
theorem B1039625 : Blo 646304 1039625 := bstep (se 2 (by rfl) ⟨389859, by rfl⟩ : syracuseStep 1039625 = 779719) B779719
theorem B974159 : Blo 646304 974159 := bstep (se 1 (by rfl) ⟨730619, by rfl⟩ : syracuseStep 974159 = 1461239) B1461239
theorem B974249 : Blo 646304 974249 := bstep (se 2 (by rfl) ⟨365343, by rfl⟩ : syracuseStep 974249 = 730687) B730687
theorem B646631 : Blo 646304 646631 := bstep (se 1 (by rfl) ⟨484973, by rfl⟩ : syracuseStep 646631 = 969947) B969947
theorem B974399 : Blo 646304 974399 := bstep (se 1 (by rfl) ⟨730799, by rfl⟩ : syracuseStep 974399 = 1461599) B1461599
theorem B646747 : Blo 646304 646747 := bstep (se 1 (by rfl) ⟨485060, by rfl⟩ : syracuseStep 646747 = 970121) B970121
theorem B2186999 : Blo 646304 2186999 := bstep (se 1 (by rfl) ⟨1640249, by rfl⟩ : syracuseStep 2186999 = 3280499) B3280499
theorem B646983 : Blo 646304 646983 := bstep (se 1 (by rfl) ⟨485237, by rfl⟩ : syracuseStep 646983 = 970475) B970475
theorem B974663 : Blo 646304 974663 := bstep (se 1 (by rfl) ⟨730997, by rfl⟩ : syracuseStep 974663 = 1461995) B1461995
theorem B974747 : Blo 646304 974747 := bstep (se 1 (by rfl) ⟨731060, by rfl⟩ : syracuseStep 974747 = 1462121) B1462121
theorem B647135 : Blo 646304 647135 := bstep (se 1 (by rfl) ⟨485351, by rfl⟩ : syracuseStep 647135 = 970703) B970703
theorem B1663195 : Blo 646304 1663195 := bstep (se 1 (by rfl) ⟨1247396, by rfl⟩ : syracuseStep 1663195 = 2494793) B2494793
theorem B647399 : Blo 646304 647399 := bstep (se 1 (by rfl) ⟨485549, by rfl⟩ : syracuseStep 647399 = 971099) B971099
theorem B647551 : Blo 646304 647551 := bstep (se 1 (by rfl) ⟨485663, by rfl⟩ : syracuseStep 647551 = 971327) B971327
theorem B647631 : Blo 646304 647631 := bstep (se 1 (by rfl) ⟨485723, by rfl⟩ : syracuseStep 647631 = 971447) B971447
theorem B975311 : Blo 646304 975311 := bstep (se 1 (by rfl) ⟨731483, by rfl⟩ : syracuseStep 975311 = 1462967) B1462967
theorem B975353 : Blo 646304 975353 := bstep (se 2 (by rfl) ⟨365757, by rfl⟩ : syracuseStep 975353 = 731515) B731515
theorem B15000065 : Blo 646304 15000065 := bstep (se 2 (by rfl) ⟨5625024, by rfl⟩ : syracuseStep 15000065 = 11250049) B11250049
theorem B975455 : Blo 646304 975455 := bstep (se 1 (by rfl) ⟨731591, by rfl⟩ : syracuseStep 975455 = 1463183) B1463183
theorem B647783 : Blo 646304 647783 := bstep (se 1 (by rfl) ⟨485837, by rfl⟩ : syracuseStep 647783 = 971675) B971675
theorem B2188079 : Blo 646304 2188079 := bstep (se 1 (by rfl) ⟨1641059, by rfl⟩ : syracuseStep 2188079 = 3282119) B3282119
theorem B648047 : Blo 646304 648047 := bstep (se 1 (by rfl) ⟨486035, by rfl⟩ : syracuseStep 648047 = 972071) B972071
theorem B2188187 : Blo 646304 2188187 := bstep (se 1 (by rfl) ⟨1641140, by rfl⟩ : syracuseStep 2188187 = 3282281) B3282281
theorem B648103 : Blo 646304 648103 := bstep (se 1 (by rfl) ⟨486077, by rfl⟩ : syracuseStep 648103 = 972155) B972155
theorem B648187 : Blo 646304 648187 := bstep (se 1 (by rfl) ⟨486140, by rfl⟩ : syracuseStep 648187 = 972281) B972281
theorem B648255 : Blo 646304 648255 := bstep (se 1 (by rfl) ⟨486191, by rfl⟩ : syracuseStep 648255 = 972383) B972383
theorem B5530787 : Blo 646304 5530787 := bstep (se 1 (by rfl) ⟨4148090, by rfl⟩ : syracuseStep 5530787 = 8296181) B8296181
theorem B8316067 : Blo 646304 8316067 := bstep (se 1 (by rfl) ⟨6237050, by rfl⟩ : syracuseStep 8316067 = 12474101) B12474101
theorem B648399 : Blo 646304 648399 := bstep (se 1 (by rfl) ⟨486299, by rfl⟩ : syracuseStep 648399 = 972599) B972599
theorem B3695939 : Blo 646304 3695939 := bstep (se 1 (by rfl) ⟨2771954, by rfl⟩ : syracuseStep 3695939 = 5543909) B5543909
theorem B81126755 : Blo 646304 81126755 := bstep (se 1 (by rfl) ⟨60845066, by rfl⟩ : syracuseStep 81126755 = 121690133) B121690133
theorem B648603 : Blo 646304 648603 := bstep (se 1 (by rfl) ⟨486452, by rfl⟩ : syracuseStep 648603 = 972905) B972905
theorem B8316431 : Blo 646304 8316431 := bstep (se 1 (by rfl) ⟨6237323, by rfl⟩ : syracuseStep 8316431 = 12474647) B12474647
theorem B648815 : Blo 646304 648815 := bstep (se 1 (by rfl) ⟨486611, by rfl⟩ : syracuseStep 648815 = 973223) B973223
theorem B648871 : Blo 646304 648871 := bstep (se 1 (by rfl) ⟨486653, by rfl⟩ : syracuseStep 648871 = 973307) B973307
theorem B648955 : Blo 646304 648955 := bstep (se 1 (by rfl) ⟨486716, by rfl⟩ : syracuseStep 648955 = 973433) B973433
theorem B648991 : Blo 646304 648991 := bstep (se 1 (by rfl) ⟨486743, by rfl⟩ : syracuseStep 648991 = 973487) B973487
theorem B649023 : Blo 646304 649023 := bstep (se 1 (by rfl) ⟨486767, by rfl⟩ : syracuseStep 649023 = 973535) B973535
theorem B649199 : Blo 646304 649199 := bstep (se 1 (by rfl) ⟨486899, by rfl⟩ : syracuseStep 649199 = 973799) B973799
theorem B2189321 : Blo 646304 2189321 := bstep (se 2 (by rfl) ⟨820995, by rfl⟩ : syracuseStep 2189321 = 1641991) B1641991
theorem B649371 : Blo 646304 649371 := bstep (se 1 (by rfl) ⟨487028, by rfl⟩ : syracuseStep 649371 = 974057) B974057
theorem B649407 : Blo 646304 649407 := bstep (se 1 (by rfl) ⟨487055, by rfl⟩ : syracuseStep 649407 = 974111) B974111
theorem B649519 : Blo 646304 649519 := bstep (se 1 (by rfl) ⟨487139, by rfl⟩ : syracuseStep 649519 = 974279) B974279
theorem B1993223 : Blo 646304 1993223 := bstep (se 1 (by rfl) ⟨1494917, by rfl⟩ : syracuseStep 1993223 = 2989835) B2989835
theorem B649755 : Blo 646304 649755 := bstep (se 1 (by rfl) ⟨487316, by rfl⟩ : syracuseStep 649755 = 974633) B974633
theorem B649759 : Blo 646304 649759 := bstep (se 1 (by rfl) ⟨487319, by rfl⟩ : syracuseStep 649759 = 974639) B974639
theorem B9366191 : Blo 646304 9366191 := bstep (se 1 (by rfl) ⟨7024643, by rfl⟩ : syracuseStep 9366191 = 14049287) B14049287
theorem B650075 : Blo 646304 650075 := bstep (se 1 (by rfl) ⟨487556, by rfl⟩ : syracuseStep 650075 = 975113) B975113
theorem B650143 : Blo 646304 650143 := bstep (se 1 (by rfl) ⟨487607, by rfl⟩ : syracuseStep 650143 = 975215) B975215
theorem B650287 : Blo 646304 650287 := bstep (se 1 (by rfl) ⟨487715, by rfl⟩ : syracuseStep 650287 = 975431) B975431
theorem B8875241 : Blo 646304 8875241 := bstep (se 2 (by rfl) ⟨3328215, by rfl⟩ : syracuseStep 8875241 = 6656431) B6656431
theorem B2190617 : Blo 646304 2190617 := bstep (se 2 (by rfl) ⟨821481, by rfl⟩ : syracuseStep 2190617 = 1642963) B1642963
theorem B2190671 : Blo 646304 2190671 := bstep (se 1 (by rfl) ⟨1643003, by rfl⟩ : syracuseStep 2190671 = 3286007) B3286007
theorem B24997409 : Blo 646304 24997409 := bstep (se 2 (by rfl) ⟨9374028, by rfl⟩ : syracuseStep 24997409 = 18748057) B18748057
theorem B13988051 : Blo 646304 13988051 := bstep (se 1 (by rfl) ⟨10491038, by rfl⟩ : syracuseStep 13988051 = 20982077) B20982077
theorem B3273209 : Blo 646304 3273209 := bstep (se 2 (by rfl) ⟨1227453, by rfl⟩ : syracuseStep 3273209 = 2454907) B2454907
theorem B2191967 : Blo 646304 2191967 := bstep (se 1 (by rfl) ⟨1643975, by rfl⟩ : syracuseStep 2191967 = 3287951) B3287951
theorem B3700313 : Blo 646304 3700313 := bstep (se 2 (by rfl) ⟨1387617, by rfl⟩ : syracuseStep 3700313 = 2775235) B2775235
theorem B2193209 : Blo 646304 2193209 := bstep (se 2 (by rfl) ⟨822453, by rfl⟩ : syracuseStep 2193209 = 1644907) B1644907
theorem B1636159 : Blo 646304 1636159 := bstep (se 1 (by rfl) ⟨1227119, by rfl⟩ : syracuseStep 1636159 = 2454239) B2454239
theorem B4912973 : Blo 646304 4912973 := bstep (se 3 (by rfl) ⟨921182, by rfl⟩ : syracuseStep 4912973 = 1842365) B1842365
theorem B2193371 : Blo 646304 2193371 := bstep (se 1 (by rfl) ⟨1645028, by rfl⟩ : syracuseStep 2193371 = 3290057) B3290057
theorem B2193641 : Blo 646304 2193641 := bstep (se 2 (by rfl) ⟨822615, by rfl⟩ : syracuseStep 2193641 = 1645231) B1645231
theorem B1636595 : Blo 646304 1636595 := bstep (se 1 (by rfl) ⟨1227446, by rfl⟩ : syracuseStep 1636595 = 2454893) B2454893
theorem B1604233 : Blo 646304 1604233 := bstep (se 2 (by rfl) ⟨601587, by rfl⟩ : syracuseStep 1604233 = 1203175) B1203175
theorem B2194073 : Blo 646304 2194073 := bstep (se 2 (by rfl) ⟨822777, by rfl⟩ : syracuseStep 2194073 = 1645555) B1645555
theorem B4684709 : Blo 646304 4684709 := bstep (se 4 (by rfl) ⟨439191, by rfl⟩ : syracuseStep 4684709 = 878383) B878383
theorem B1638215 : Blo 646304 1638215 := bstep (se 1 (by rfl) ⟨1228661, by rfl⟩ : syracuseStep 1638215 = 2457323) B2457323
theorem B819067 : Blo 646304 819067 := bstep (se 1 (by rfl) ⟨614300, by rfl⟩ : syracuseStep 819067 = 1228601) B1228601
theorem B3276935 : Blo 646304 3276935 := bstep (se 1 (by rfl) ⟨2457701, by rfl⟩ : syracuseStep 3276935 = 4915403) B4915403
theorem B5046457 : Blo 646304 5046457 := bstep (se 2 (by rfl) ⟨1892421, by rfl⟩ : syracuseStep 5046457 = 3784843) B3784843
theorem B819391 : Blo 646304 819391 := bstep (se 1 (by rfl) ⟨614543, by rfl⟩ : syracuseStep 819391 = 1229087) B1229087
theorem B1311023 : Blo 646304 1311023 := bstep (se 1 (by rfl) ⟨983267, by rfl⟩ : syracuseStep 1311023 = 1966535) B1966535
theorem B16810847 : Blo 646304 16810847 := bstep (se 1 (by rfl) ⟨12608135, by rfl⟩ : syracuseStep 16810847 = 25216271) B25216271
theorem B5244061 : Blo 646304 5244061 := bstep (se 3 (by rfl) ⟨983261, by rfl⟩ : syracuseStep 5244061 = 1966523) B1966523
theorem B820459 : Blo 646304 820459 := bstep (se 1 (by rfl) ⟨615344, by rfl⟩ : syracuseStep 820459 = 1230689) B1230689
theorem B17696171 : Blo 646304 17696171 := bstep (se 1 (by rfl) ⟨13272128, by rfl⟩ : syracuseStep 17696171 = 26544257) B26544257
theorem B3278555 : Blo 646304 3278555 := bstep (se 1 (by rfl) ⟨2458916, by rfl⟩ : syracuseStep 3278555 = 4917833) B4917833
theorem B2623375 : Blo 646304 2623375 := bstep (se 1 (by rfl) ⟨1967531, by rfl⟩ : syracuseStep 2623375 = 3935063) B3935063
theorem B821279 : Blo 646304 821279 := bstep (se 1 (by rfl) ⟨615959, by rfl⟩ : syracuseStep 821279 = 1231919) B1231919
theorem B6229055 : Blo 646304 6229055 := bstep (se 1 (by rfl) ⟨4671791, by rfl⟩ : syracuseStep 6229055 = 9343583) B9343583
theorem B659047 : Blo 646304 659047 := bstep (se 1 (by rfl) ⟨494285, by rfl⟩ : syracuseStep 659047 = 988571) B988571
theorem B1380407 : Blo 646304 1380407 := bstep (se 1 (by rfl) ⟨1035305, by rfl⟩ : syracuseStep 1380407 = 2070611) B2070611
theorem B12161177 : Blo 646304 12161177 := bstep (se 2 (by rfl) ⟨4560441, by rfl⟩ : syracuseStep 12161177 = 9120883) B9120883
theorem B921775 : Blo 646304 921775 := bstep (se 1 (by rfl) ⟨691331, by rfl⟩ : syracuseStep 921775 = 1382663) B1382663
theorem B7868825 : Blo 646304 7868825 := bstep (se 2 (by rfl) ⟨2950809, by rfl⟩ : syracuseStep 7868825 = 5901619) B5901619
theorem B2462471 : Blo 646304 2462471 := bstep (se 1 (by rfl) ⟨1846853, by rfl⟩ : syracuseStep 2462471 = 3693707) B3693707
theorem B693083 : Blo 646304 693083 := bstep (se 1 (by rfl) ⟨519812, by rfl⟩ : syracuseStep 693083 = 1039625) B1039625
theorem B1316335 : Blo 646304 1316335 := bstep (se 1 (by rfl) ⟨987251, by rfl⟩ : syracuseStep 1316335 = 1974503) B1974503
theorem B10000043 : Blo 646304 10000043 := bstep (se 1 (by rfl) ⟨7500032, by rfl⟩ : syracuseStep 10000043 = 15000065) B15000065
theorem B1644371 : Blo 646304 1644371 := bstep (se 1 (by rfl) ⟨1233278, by rfl⟩ : syracuseStep 1644371 = 2466557) B2466557
theorem B5248891 : Blo 646304 5248891 := bstep (se 1 (by rfl) ⟨3936668, by rfl⟩ : syracuseStep 5248891 = 7873337) B7873337
theorem B4921235 : Blo 646304 4921235 := bstep (se 1 (by rfl) ⟨3690926, by rfl⟩ : syracuseStep 4921235 = 7381853) B7381853
theorem B2955203 : Blo 646304 2955203 := bstep (se 1 (by rfl) ⟨2216402, by rfl⟩ : syracuseStep 2955203 = 4432805) B4432805
theorem B2463959 : Blo 646304 2463959 := bstep (se 1 (by rfl) ⟨1847969, by rfl⟩ : syracuseStep 2463959 = 3695939) B3695939
theorem B5544287 : Blo 646304 5544287 := bstep (se 1 (by rfl) ⟨4158215, by rfl⟩ : syracuseStep 5544287 = 8316431) B8316431
theorem B15735383 : Blo 646304 15735383 := bstep (se 1 (by rfl) ⟨11801537, by rfl⟩ : syracuseStep 15735383 = 23603075) B23603075
theorem B727879 : Blo 646304 727879 := bstep (se 1 (by rfl) ⟨545909, by rfl⟩ : syracuseStep 727879 = 1091819) B1091819
theorem B3120065 : Blo 646304 3120065 := bstep (se 2 (by rfl) ⟨1170024, by rfl⟩ : syracuseStep 3120065 = 2340049) B2340049
theorem B3120257 : Blo 646304 3120257 := bstep (se 2 (by rfl) ⟨1170096, by rfl⟩ : syracuseStep 3120257 = 2340193) B2340193
theorem B11803805 : Blo 646304 11803805 := bstep (se 3 (by rfl) ⟨2213213, by rfl⟩ : syracuseStep 11803805 = 4426427) B4426427
theorem B728527 : Blo 646304 728527 := bstep (se 1 (by rfl) ⟨546395, by rfl⟩ : syracuseStep 728527 = 1092791) B1092791
theorem B2956807 : Blo 646304 2956807 := bstep (se 1 (by rfl) ⟨2217605, by rfl⟩ : syracuseStep 2956807 = 4435211) B4435211
theorem B2072137 : Blo 646304 2072137 := bstep (se 2 (by rfl) ⟨777051, by rfl⟩ : syracuseStep 2072137 = 1554103) B1554103
theorem B728743 : Blo 646304 728743 := bstep (se 1 (by rfl) ⟨546557, by rfl⟩ : syracuseStep 728743 = 1093115) B1093115
theorem B19996379 : Blo 646304 19996379 := bstep (se 1 (by rfl) ⟨14997284, by rfl⟩ : syracuseStep 19996379 = 29994569) B29994569
theorem B1384303 : Blo 646304 1384303 := bstep (se 1 (by rfl) ⟨1038227, by rfl⟩ : syracuseStep 1384303 = 2076455) B2076455
theorem B729031 : Blo 646304 729031 := bstep (se 1 (by rfl) ⟨546773, by rfl⟩ : syracuseStep 729031 = 1093547) B1093547
theorem B2334845 : Blo 646304 2334845 := bstep (se 3 (by rfl) ⟨437783, by rfl⟩ : syracuseStep 2334845 = 875567) B875567
theorem B729391 : Blo 646304 729391 := bstep (se 1 (by rfl) ⟨547043, by rfl⟩ : syracuseStep 729391 = 1094087) B1094087
theorem B2138977 : Blo 646304 2138977 := bstep (se 2 (by rfl) ⟨802116, by rfl⟩ : syracuseStep 2138977 = 1604233) B1604233
theorem B8004595 : Blo 646304 8004595 := bstep (se 1 (by rfl) ⟨6003446, by rfl⟩ : syracuseStep 8004595 = 12006893) B12006893
theorem B2466875 : Blo 646304 2466875 := bstep (se 1 (by rfl) ⟨1850156, by rfl⟩ : syracuseStep 2466875 = 3700313) B3700313
theorem B2762045 : Blo 646304 2762045 := bstep (se 3 (by rfl) ⟨517883, by rfl⟩ : syracuseStep 2762045 = 1035767) B1035767
theorem B1091063 : Blo 646304 1091063 := bstep (se 1 (by rfl) ⟨818297, by rfl⟩ : syracuseStep 1091063 = 1636595) B1636595
theorem B730651 : Blo 646304 730651 := bstep (se 1 (by rfl) ⟨547988, by rfl⟩ : syracuseStep 730651 = 1095977) B1095977
theorem B3123139 : Blo 646304 3123139 := bstep (se 1 (by rfl) ⟨2342354, by rfl⟩ : syracuseStep 3123139 = 4684709) B4684709
theorem B17704927 : Blo 646304 17704927 := bstep (se 1 (by rfl) ⟨13278695, by rfl⟩ : syracuseStep 17704927 = 26557391) B26557391
theorem B2468029 : Blo 646304 2468029 := bstep (se 3 (by rfl) ⟨462755, by rfl⟩ : syracuseStep 2468029 = 925511) B925511
theorem B2763001 : Blo 646304 2763001 := bstep (se 2 (by rfl) ⟨1036125, by rfl⟩ : syracuseStep 2763001 = 2072251) B2072251
theorem B1092089 : Blo 646304 1092089 := bstep (se 2 (by rfl) ⟨409533, by rfl⟩ : syracuseStep 1092089 = 819067) B819067
theorem B1092143 : Blo 646304 1092143 := bstep (se 1 (by rfl) ⟨819107, by rfl⟩ : syracuseStep 1092143 = 1638215) B1638215
theorem B8006215 : Blo 646304 8006215 := bstep (se 1 (by rfl) ⟨6004661, by rfl⟩ : syracuseStep 8006215 = 12009323) B12009323
theorem B1092359 : Blo 646304 1092359 := bstep (se 1 (by rfl) ⟨819269, by rfl⟩ : syracuseStep 1092359 = 1638539) B1638539
theorem B1092575 : Blo 646304 1092575 := bstep (se 1 (by rfl) ⟨819431, by rfl⟩ : syracuseStep 1092575 = 1638863) B1638863
theorem B1846547 : Blo 646304 1846547 := bstep (se 1 (by rfl) ⟨1384910, by rfl⟩ : syracuseStep 1846547 = 2769821) B2769821
theorem B1092919 : Blo 646304 1092919 := bstep (se 1 (by rfl) ⟨819689, by rfl⟩ : syracuseStep 1092919 = 1639379) B1639379
theorem B3288761 : Blo 646304 3288761 := bstep (se 2 (by rfl) ⟨1233285, by rfl⟩ : syracuseStep 3288761 = 2466571) B2466571
theorem B1093439 : Blo 646304 1093439 := bstep (se 1 (by rfl) ⟨820079, by rfl⟩ : syracuseStep 1093439 = 1640159) B1640159
theorem B2502505 : Blo 646304 2502505 := bstep (se 2 (by rfl) ⟨938439, by rfl⟩ : syracuseStep 2502505 = 1876879) B1876879
theorem B2633593 : Blo 646304 2633593 := bstep (se 2 (by rfl) ⟨987597, by rfl⟩ : syracuseStep 2633593 = 1975195) B1975195
theorem B1093513 : Blo 646304 1093513 := bstep (se 2 (by rfl) ⟨410067, by rfl⟩ : syracuseStep 1093513 = 820135) B820135
theorem B1847423 : Blo 646304 1847423 := bstep (se 1 (by rfl) ⟨1385567, by rfl⟩ : syracuseStep 1847423 = 2771135) B2771135
theorem B11088089 : Blo 646304 11088089 := bstep (se 2 (by rfl) ⟨4158033, by rfl⟩ : syracuseStep 11088089 = 8316067) B8316067
theorem B1454543 : Blo 646304 1454543 := bstep (se 1 (by rfl) ⟨1090907, by rfl⟩ : syracuseStep 1454543 = 2181815) B2181815
theorem B4141631 : Blo 646304 4141631 := bstep (se 1 (by rfl) ⟨3106223, by rfl⟩ : syracuseStep 4141631 = 6212447) B6212447
theorem B8893313 : Blo 646304 8893313 := bstep (se 2 (by rfl) ⟨3334992, by rfl⟩ : syracuseStep 8893313 = 6669985) B6669985
theorem B2765735 : Blo 646304 2765735 := bstep (se 1 (by rfl) ⟨2074301, by rfl⟩ : syracuseStep 2765735 = 4148603) B4148603
theorem B1455209 : Blo 646304 1455209 := bstep (se 2 (by rfl) ⟨545703, by rfl⟩ : syracuseStep 1455209 = 1091407) B1091407
theorem B4142299 : Blo 646304 4142299 := bstep (se 1 (by rfl) ⟨3106724, by rfl⟩ : syracuseStep 4142299 = 6213449) B6213449
theorem B5911937 : Blo 646304 5911937 := bstep (se 2 (by rfl) ⟨2216976, by rfl⟩ : syracuseStep 5911937 = 4433953) B4433953
theorem B1095079 : Blo 646304 1095079 := bstep (se 1 (by rfl) ⟨821309, by rfl⟩ : syracuseStep 1095079 = 1642619) B1642619
theorem B24032807 : Blo 646304 24032807 := bstep (se 1 (by rfl) ⟨18024605, by rfl⟩ : syracuseStep 24032807 = 36049211) B36049211
theorem B1455839 : Blo 646304 1455839 := bstep (se 1 (by rfl) ⟨1091879, by rfl⟩ : syracuseStep 1455839 = 2183759) B2183759
theorem B22493159 : Blo 646304 22493159 := bstep (se 1 (by rfl) ⟨16869869, by rfl⟩ : syracuseStep 22493159 = 33739739) B33739739
theorem B1456199 : Blo 646304 1456199 := bstep (se 1 (by rfl) ⟨1092149, by rfl⟩ : syracuseStep 1456199 = 2184299) B2184299
theorem B1226983 : Blo 646304 1226983 := bstep (se 1 (by rfl) ⟨920237, by rfl⟩ : syracuseStep 1226983 = 1840475) B1840475
theorem B1554727 : Blo 646304 1554727 := bstep (se 1 (by rfl) ⟨1166045, by rfl⟩ : syracuseStep 1554727 = 2332091) B2332091
theorem B2767547 : Blo 646304 2767547 := bstep (se 1 (by rfl) ⟨2075660, by rfl⟩ : syracuseStep 2767547 = 4151321) B4151321
theorem B1456865 : Blo 646304 1456865 := bstep (se 2 (by rfl) ⟨546324, by rfl⟩ : syracuseStep 1456865 = 1092649) B1092649
theorem B7027499 : Blo 646304 7027499 := bstep (se 1 (by rfl) ⟨5270624, by rfl⟩ : syracuseStep 7027499 = 10541249) B10541249
theorem B1457063 : Blo 646304 1457063 := bstep (se 1 (by rfl) ⟨1092797, by rfl⟩ : syracuseStep 1457063 = 2185595) B2185595
theorem B1457243 : Blo 646304 1457243 := bstep (se 1 (by rfl) ⟨1092932, by rfl⟩ : syracuseStep 1457243 = 2185865) B2185865
theorem B4209779 : Blo 646304 4209779 := bstep (se 1 (by rfl) ⟨3157334, by rfl⟩ : syracuseStep 4209779 = 6314669) B6314669
theorem B1097131 : Blo 646304 1097131 := bstep (se 1 (by rfl) ⟨822848, by rfl⟩ : syracuseStep 1097131 = 1645697) B1645697
theorem B1097327 : Blo 646304 1097327 := bstep (se 1 (by rfl) ⟨822995, by rfl⟩ : syracuseStep 1097327 = 1645991) B1645991
theorem B26590913 : Blo 646304 26590913 := bstep (se 2 (by rfl) ⟨9971592, by rfl⟩ : syracuseStep 26590913 = 19943185) B19943185
theorem B1457999 : Blo 646304 1457999 := bstep (se 1 (by rfl) ⟨1093499, by rfl⟩ : syracuseStep 1457999 = 2186999) B2186999
theorem B1458719 : Blo 646304 1458719 := bstep (se 1 (by rfl) ⟨1094039, by rfl⟩ : syracuseStep 1458719 = 2188079) B2188079
theorem B7881313 : Blo 646304 7881313 := bstep (se 2 (by rfl) ⟨2955492, by rfl⟩ : syracuseStep 7881313 = 5910985) B5910985
theorem B1458791 : Blo 646304 1458791 := bstep (se 1 (by rfl) ⟨1094093, by rfl⟩ : syracuseStep 1458791 = 2188187) B2188187
theorem B5620499 : Blo 646304 5620499 := bstep (se 1 (by rfl) ⟨4215374, by rfl⟩ : syracuseStep 5620499 = 8430749) B8430749
theorem B3687191 : Blo 646304 3687191 := bstep (se 1 (by rfl) ⟨2765393, by rfl⟩ : syracuseStep 3687191 = 5530787) B5530787
theorem B54084503 : Blo 646304 54084503 := bstep (se 1 (by rfl) ⟨40563377, by rfl⟩ : syracuseStep 54084503 = 81126755) B81126755
theorem B1230059 : Blo 646304 1230059 := bstep (se 1 (by rfl) ⟨922544, by rfl⟩ : syracuseStep 1230059 = 1845089) B1845089
theorem B1459547 : Blo 646304 1459547 := bstep (se 1 (by rfl) ⟨1094660, by rfl⟩ : syracuseStep 1459547 = 2189321) B2189321
theorem B2082145 : Blo 646304 2082145 := bstep (se 2 (by rfl) ⟨780804, by rfl⟩ : syracuseStep 2082145 = 1561609) B1561609
theorem B1459817 : Blo 646304 1459817 := bstep (se 2 (by rfl) ⟨547431, by rfl⟩ : syracuseStep 1459817 = 1094863) B1094863
theorem B1558187 : Blo 646304 1558187 := bstep (se 1 (by rfl) ⟨1168640, by rfl⟩ : syracuseStep 1558187 = 2337281) B2337281
theorem B1328815 : Blo 646304 1328815 := bstep (se 1 (by rfl) ⟨996611, by rfl⟩ : syracuseStep 1328815 = 1993223) B1993223
theorem B1558207 : Blo 646304 1558207 := bstep (se 1 (by rfl) ⟨1168655, by rfl⟩ : syracuseStep 1558207 = 2337311) B2337311
theorem B6244127 : Blo 646304 6244127 := bstep (se 1 (by rfl) ⟨4683095, by rfl⟩ : syracuseStep 6244127 = 9366191) B9366191
theorem B5916827 : Blo 646304 5916827 := bstep (se 1 (by rfl) ⟨4437620, by rfl⟩ : syracuseStep 5916827 = 8875241) B8875241
theorem B1460411 : Blo 646304 1460411 := bstep (se 1 (by rfl) ⟨1095308, by rfl⟩ : syracuseStep 1460411 = 2190617) B2190617
theorem B1460447 : Blo 646304 1460447 := bstep (se 1 (by rfl) ⟨1095335, by rfl⟩ : syracuseStep 1460447 = 2190671) B2190671
theorem B16664939 : Blo 646304 16664939 := bstep (se 1 (by rfl) ⟨12498704, by rfl⟩ : syracuseStep 16664939 = 24997409) B24997409
theorem B2181545 : Blo 646304 2181545 := bstep (se 2 (by rfl) ⟨818079, by rfl⟩ : syracuseStep 2181545 = 1636159) B1636159
theorem B1231463 : Blo 646304 1231463 := bstep (se 1 (by rfl) ⟨923597, by rfl⟩ : syracuseStep 1231463 = 1847195) B1847195
theorem B1755751 : Blo 646304 1755751 := bstep (se 1 (by rfl) ⟨1316813, by rfl⟩ : syracuseStep 1755751 = 2633627) B2633627
theorem B1460897 : Blo 646304 1460897 := bstep (se 2 (by rfl) ⟨547836, by rfl⟩ : syracuseStep 1460897 = 1095673) B1095673
theorem B9325367 : Blo 646304 9325367 := bstep (se 1 (by rfl) ⟨6994025, by rfl⟩ : syracuseStep 9325367 = 13988051) B13988051
theorem B1231699 : Blo 646304 1231699 := bstep (se 1 (by rfl) ⟨923774, by rfl⟩ : syracuseStep 1231699 = 1847549) B1847549
theorem B969593 : Blo 646304 969593 := bstep (se 2 (by rfl) ⟨363597, by rfl⟩ : syracuseStep 969593 = 727195) B727195
theorem B1461113 : Blo 646304 1461113 := bstep (se 2 (by rfl) ⟨547917, by rfl⟩ : syracuseStep 1461113 = 1095835) B1095835
theorem B969641 : Blo 646304 969641 := bstep (se 2 (by rfl) ⟨363615, by rfl⟩ : syracuseStep 969641 = 727231) B727231
theorem B2182139 : Blo 646304 2182139 := bstep (se 1 (by rfl) ⟨1636604, by rfl⟩ : syracuseStep 2182139 = 3273209) B3273209
theorem B1461257 : Blo 646304 1461257 := bstep (se 2 (by rfl) ⟨547971, by rfl⟩ : syracuseStep 1461257 = 1095943) B1095943
theorem B969791 : Blo 646304 969791 := bstep (se 1 (by rfl) ⟨727343, by rfl⟩ : syracuseStep 969791 = 1454687) B1454687
theorem B1461311 : Blo 646304 1461311 := bstep (se 1 (by rfl) ⟨1095983, by rfl⟩ : syracuseStep 1461311 = 2191967) B2191967
theorem B12471641 : Blo 646304 12471641 := bstep (se 2 (by rfl) ⟨4676865, by rfl⟩ : syracuseStep 12471641 = 9353731) B9353731
theorem B970343 : Blo 646304 970343 := bstep (se 1 (by rfl) ⟨727757, by rfl⟩ : syracuseStep 970343 = 1455515) B1455515
theorem B1462139 : Blo 646304 1462139 := bstep (se 1 (by rfl) ⟨1096604, by rfl⟩ : syracuseStep 1462139 = 2193209) B2193209
theorem B970727 : Blo 646304 970727 := bstep (se 1 (by rfl) ⟨728045, by rfl⟩ : syracuseStep 970727 = 1456091) B1456091
theorem B1462247 : Blo 646304 1462247 := bstep (se 1 (by rfl) ⟨1096685, by rfl⟩ : syracuseStep 1462247 = 2193371) B2193371
theorem B1232891 : Blo 646304 1232891 := bstep (se 1 (by rfl) ⟨924668, by rfl⟩ : syracuseStep 1232891 = 1849337) B1849337
theorem B970847 : Blo 646304 970847 := bstep (se 1 (by rfl) ⟨728135, by rfl⟩ : syracuseStep 970847 = 1456271) B1456271
theorem B10506341 : Blo 646304 10506341 := bstep (se 4 (by rfl) ⟨984969, by rfl⟩ : syracuseStep 10506341 = 1969939) B1969939
theorem B970859 : Blo 646304 970859 := bstep (se 1 (by rfl) ⟨728144, by rfl⟩ : syracuseStep 970859 = 1456289) B1456289
theorem B970907 : Blo 646304 970907 := bstep (se 1 (by rfl) ⟨728180, by rfl⟩ : syracuseStep 970907 = 1456361) B1456361
theorem B1462427 : Blo 646304 1462427 := bstep (se 1 (by rfl) ⟨1096820, by rfl⟩ : syracuseStep 1462427 = 2193641) B2193641
theorem B1462625 : Blo 646304 1462625 := bstep (se 2 (by rfl) ⟨548484, by rfl⟩ : syracuseStep 1462625 = 1096969) B1096969
theorem B4149629 : Blo 646304 4149629 := bstep (se 3 (by rfl) ⟨778055, by rfl⟩ : syracuseStep 4149629 = 1556111) B1556111
theorem B1462715 : Blo 646304 1462715 := bstep (se 1 (by rfl) ⟨1097036, by rfl⟩ : syracuseStep 1462715 = 2194073) B2194073
theorem B4936301 : Blo 646304 4936301 := bstep (se 3 (by rfl) ⟨925556, by rfl⟩ : syracuseStep 4936301 = 1851113) B1851113
theorem B1037215 : Blo 646304 1037215 := bstep (se 1 (by rfl) ⟨777911, by rfl⟩ : syracuseStep 1037215 = 1555823) B1555823
theorem B971759 : Blo 646304 971759 := bstep (se 1 (by rfl) ⟨728819, by rfl⟩ : syracuseStep 971759 = 1457639) B1457639
theorem B972143 : Blo 646304 972143 := bstep (se 1 (by rfl) ⟨729107, by rfl⟩ : syracuseStep 972143 = 1458215) B1458215
theorem B972263 : Blo 646304 972263 := bstep (se 1 (by rfl) ⟨729197, by rfl⟩ : syracuseStep 972263 = 1458395) B1458395
theorem B2217593 : Blo 646304 2217593 := bstep (se 2 (by rfl) ⟨831597, by rfl⟩ : syracuseStep 2217593 = 1663195) B1663195
theorem B972425 : Blo 646304 972425 := bstep (se 2 (by rfl) ⟨364659, by rfl⟩ : syracuseStep 972425 = 729319) B729319
theorem B972443 : Blo 646304 972443 := bstep (se 1 (by rfl) ⟨729332, by rfl⟩ : syracuseStep 972443 = 1458665) B1458665
theorem B86562553 : Blo 646304 86562553 := bstep (se 2 (by rfl) ⟨32460957, by rfl⟩ : syracuseStep 86562553 = 64921915) B64921915
theorem B972635 : Blo 646304 972635 := bstep (se 1 (by rfl) ⟨729476, by rfl⟩ : syracuseStep 972635 = 1458953) B1458953
theorem B1267849 : Blo 646304 1267849 := bstep (se 2 (by rfl) ⟨475443, by rfl⟩ : syracuseStep 1267849 = 950887) B950887
theorem B973019 : Blo 646304 973019 := bstep (se 1 (by rfl) ⟨729764, by rfl⟩ : syracuseStep 973019 = 1459529) B1459529
theorem B973289 : Blo 646304 973289 := bstep (se 2 (by rfl) ⟨364983, by rfl⟩ : syracuseStep 973289 = 729967) B729967
theorem B973679 : Blo 646304 973679 := bstep (se 1 (by rfl) ⟨730259, by rfl⟩ : syracuseStep 973679 = 1460519) B1460519
theorem B973691 : Blo 646304 973691 := bstep (se 1 (by rfl) ⟨730268, by rfl⟩ : syracuseStep 973691 = 1460537) B1460537
theorem B7887887 : Blo 646304 7887887 := bstep (se 1 (by rfl) ⟨5915915, by rfl⟩ : syracuseStep 7887887 = 11831831) B11831831
theorem B646351 : Blo 646304 646351 := bstep (se 1 (by rfl) ⟨484763, by rfl⟩ : syracuseStep 646351 = 969527) B969527
theorem B646375 : Blo 646304 646375 := bstep (se 1 (by rfl) ⟨484781, by rfl⟩ : syracuseStep 646375 = 969563) B969563
theorem B646471 : Blo 646304 646471 := bstep (se 1 (by rfl) ⟨484853, by rfl⟩ : syracuseStep 646471 = 969707) B969707
theorem B646607 : Blo 646304 646607 := bstep (se 1 (by rfl) ⟨484955, by rfl⟩ : syracuseStep 646607 = 969911) B969911
theorem B2186729 : Blo 646304 2186729 := bstep (se 2 (by rfl) ⟨820023, by rfl⟩ : syracuseStep 2186729 = 1640047) B1640047
theorem B4677097 : Blo 646304 4677097 := bstep (se 2 (by rfl) ⟨1753911, by rfl⟩ : syracuseStep 4677097 = 3507823) B3507823
theorem B646767 : Blo 646304 646767 := bstep (se 1 (by rfl) ⟨485075, by rfl⟩ : syracuseStep 646767 = 970151) B970151
theorem B646823 : Blo 646304 646823 := bstep (se 1 (by rfl) ⟨485117, by rfl⟩ : syracuseStep 646823 = 970235) B970235
theorem B974555 : Blo 646304 974555 := bstep (se 1 (by rfl) ⟨730916, by rfl⟩ : syracuseStep 974555 = 1461833) B1461833
theorem B646887 : Blo 646304 646887 := bstep (se 1 (by rfl) ⟨485165, by rfl⟩ : syracuseStep 646887 = 970331) B970331
theorem B646943 : Blo 646304 646943 := bstep (se 1 (by rfl) ⟨485207, by rfl⟩ : syracuseStep 646943 = 970415) B970415
theorem B647023 : Blo 646304 647023 := bstep (se 1 (by rfl) ⟨485267, by rfl⟩ : syracuseStep 647023 = 970535) B970535
theorem B2776943 : Blo 646304 2776943 := bstep (se 1 (by rfl) ⟨2082707, by rfl⟩ : syracuseStep 2776943 = 4165415) B4165415
theorem B647079 : Blo 646304 647079 := bstep (se 1 (by rfl) ⟨485309, by rfl⟩ : syracuseStep 647079 = 970619) B970619
theorem B974825 : Blo 646304 974825 := bstep (se 2 (by rfl) ⟨365559, by rfl⟩ : syracuseStep 974825 = 731119) B731119
theorem B647359 : Blo 646304 647359 := bstep (se 1 (by rfl) ⟨485519, by rfl⟩ : syracuseStep 647359 = 971039) B971039
theorem B647375 : Blo 646304 647375 := bstep (se 1 (by rfl) ⟨485531, by rfl⟩ : syracuseStep 647375 = 971063) B971063
theorem B647423 : Blo 646304 647423 := bstep (se 1 (by rfl) ⟨485567, by rfl⟩ : syracuseStep 647423 = 971135) B971135
theorem B647471 : Blo 646304 647471 := bstep (se 1 (by rfl) ⟨485603, by rfl⟩ : syracuseStep 647471 = 971207) B971207
theorem B647707 : Blo 646304 647707 := bstep (se 1 (by rfl) ⟨485780, by rfl⟩ : syracuseStep 647707 = 971561) B971561
theorem B2777627 : Blo 646304 2777627 := bstep (se 1 (by rfl) ⟨2083220, by rfl⟩ : syracuseStep 2777627 = 4166441) B4166441
theorem B647711 : Blo 646304 647711 := bstep (se 1 (by rfl) ⟨485783, by rfl⟩ : syracuseStep 647711 = 971567) B971567
theorem B647791 : Blo 646304 647791 := bstep (se 1 (by rfl) ⟨485843, by rfl⟩ : syracuseStep 647791 = 971687) B971687
theorem B647847 : Blo 646304 647847 := bstep (se 1 (by rfl) ⟨485885, by rfl⟩ : syracuseStep 647847 = 971771) B971771
theorem B647887 : Blo 646304 647887 := bstep (se 1 (by rfl) ⟨485915, by rfl⟩ : syracuseStep 647887 = 971831) B971831
theorem B647967 : Blo 646304 647967 := bstep (se 1 (by rfl) ⟨485975, by rfl⟩ : syracuseStep 647967 = 971951) B971951
theorem B648239 : Blo 646304 648239 := bstep (se 1 (by rfl) ⟨486179, by rfl⟩ : syracuseStep 648239 = 972359) B972359
theorem B648303 : Blo 646304 648303 := bstep (se 1 (by rfl) ⟨486227, by rfl⟩ : syracuseStep 648303 = 972455) B972455
theorem B648359 : Blo 646304 648359 := bstep (se 1 (by rfl) ⟨486269, by rfl⟩ : syracuseStep 648359 = 972539) B972539
theorem B28435627 : Blo 646304 28435627 := bstep (se 1 (by rfl) ⟨21326720, by rfl⟩ : syracuseStep 28435627 = 42653441) B42653441
theorem B648383 : Blo 646304 648383 := bstep (se 1 (by rfl) ⟨486287, by rfl⟩ : syracuseStep 648383 = 972575) B972575
theorem B648415 : Blo 646304 648415 := bstep (se 1 (by rfl) ⟨486311, by rfl⟩ : syracuseStep 648415 = 972623) B972623
theorem B648495 : Blo 646304 648495 := bstep (se 1 (by rfl) ⟨486371, by rfl⟩ : syracuseStep 648495 = 972743) B972743
theorem B4154753 : Blo 646304 4154753 := bstep (se 2 (by rfl) ⟨1558032, by rfl⟩ : syracuseStep 4154753 = 3116065) B3116065
theorem B5629459 : Blo 646304 5629459 := bstep (se 1 (by rfl) ⟨4222094, by rfl⟩ : syracuseStep 5629459 = 8444189) B8444189
theorem B648731 : Blo 646304 648731 := bstep (se 1 (by rfl) ⟨486548, by rfl⟩ : syracuseStep 648731 = 973097) B973097
theorem B648735 : Blo 646304 648735 := bstep (se 1 (by rfl) ⟨486551, by rfl⟩ : syracuseStep 648735 = 973103) B973103
theorem B1894013 : Blo 646304 1894013 := bstep (se 3 (by rfl) ⟨355127, by rfl⟩ : syracuseStep 1894013 = 710255) B710255
theorem B3106457 : Blo 646304 3106457 := bstep (se 2 (by rfl) ⟨1164921, by rfl⟩ : syracuseStep 3106457 = 2329843) B2329843
theorem B648895 : Blo 646304 648895 := bstep (se 1 (by rfl) ⟨486671, by rfl⟩ : syracuseStep 648895 = 973343) B973343
theorem B2189051 : Blo 646304 2189051 := bstep (se 1 (by rfl) ⟨1641788, by rfl⟩ : syracuseStep 2189051 = 3283577) B3283577
theorem B12609377 : Blo 646304 12609377 := bstep (se 2 (by rfl) ⟨4728516, by rfl⟩ : syracuseStep 12609377 = 9457033) B9457033
theorem B2189213 : Blo 646304 2189213 := bstep (se 3 (by rfl) ⟨410477, by rfl⟩ : syracuseStep 2189213 = 820955) B820955
theorem B649151 : Blo 646304 649151 := bstep (se 1 (by rfl) ⟨486863, by rfl⟩ : syracuseStep 649151 = 973727) B973727
theorem B649183 : Blo 646304 649183 := bstep (se 1 (by rfl) ⟨486887, by rfl⟩ : syracuseStep 649183 = 973775) B973775
theorem B649243 : Blo 646304 649243 := bstep (se 1 (by rfl) ⟨486932, by rfl⟩ : syracuseStep 649243 = 973865) B973865
theorem B649247 : Blo 646304 649247 := bstep (se 1 (by rfl) ⟨486935, by rfl⟩ : syracuseStep 649247 = 973871) B973871
theorem B649263 : Blo 646304 649263 := bstep (se 1 (by rfl) ⟨486947, by rfl⟩ : syracuseStep 649263 = 973895) B973895
theorem B649439 : Blo 646304 649439 := bstep (se 1 (by rfl) ⟨487079, by rfl⟩ : syracuseStep 649439 = 974159) B974159
theorem B649499 : Blo 646304 649499 := bstep (se 1 (by rfl) ⟨487124, by rfl⟩ : syracuseStep 649499 = 974249) B974249
theorem B649599 : Blo 646304 649599 := bstep (se 1 (by rfl) ⟨487199, by rfl⟩ : syracuseStep 649599 = 974399) B974399
theorem B649775 : Blo 646304 649775 := bstep (se 1 (by rfl) ⟨487331, by rfl⟩ : syracuseStep 649775 = 974663) B974663
theorem B649831 : Blo 646304 649831 := bstep (se 1 (by rfl) ⟨487373, by rfl⟩ : syracuseStep 649831 = 974747) B974747
theorem B5204587 : Blo 646304 5204587 := bstep (se 1 (by rfl) ⟨3903440, by rfl⟩ : syracuseStep 5204587 = 7806881) B7806881
theorem B650207 : Blo 646304 650207 := bstep (se 1 (by rfl) ⟨487655, by rfl⟩ : syracuseStep 650207 = 975311) B975311
theorem B650235 : Blo 646304 650235 := bstep (se 1 (by rfl) ⟨487676, by rfl⟩ : syracuseStep 650235 = 975353) B975353
theorem B650303 : Blo 646304 650303 := bstep (se 1 (by rfl) ⟨487727, by rfl⟩ : syracuseStep 650303 = 975455) B975455
theorem B1797857 : Blo 646304 1797857 := bstep (se 2 (by rfl) ⟨674196, by rfl⟩ : syracuseStep 1797857 = 1348393) B1348393
theorem B4977541 : Blo 646304 4977541 := bstep (se 4 (by rfl) ⟨466644, by rfl⟩ : syracuseStep 4977541 = 933289) B933289
theorem B18969491 : Blo 646304 18969491 := bstep (se 1 (by rfl) ⟨14227118, by rfl⟩ : syracuseStep 18969491 = 28454237) B28454237
theorem B7501043 : Blo 646304 7501043 := bstep (se 1 (by rfl) ⟨5625782, by rfl⟩ : syracuseStep 7501043 = 11251565) B11251565
theorem B3110147 : Blo 646304 3110147 := bstep (se 1 (by rfl) ⟨2332610, by rfl⟩ : syracuseStep 3110147 = 4665221) B4665221
theorem B2192669 : Blo 646304 2192669 := bstep (se 3 (by rfl) ⟨411125, by rfl⟩ : syracuseStep 2192669 = 822251) B822251
theorem B11105585 : Blo 646304 11105585 := bstep (se 2 (by rfl) ⟨4164594, by rfl⟩ : syracuseStep 11105585 = 8329189) B8329189
theorem B3110359 : Blo 646304 3110359 := bstep (se 1 (by rfl) ⟨2332769, by rfl⟩ : syracuseStep 3110359 = 4665539) B4665539
theorem B11859857 : Blo 646304 11859857 := bstep (se 2 (by rfl) ⟨4447446, by rfl⟩ : syracuseStep 11859857 = 8894893) B8894893
theorem B10516463 : Blo 646304 10516463 := bstep (se 1 (by rfl) ⟨7887347, by rfl⟩ : syracuseStep 10516463 = 15774695) B15774695
theorem B9337123 : Blo 646304 9337123 := bstep (se 1 (by rfl) ⟨7002842, by rfl⟩ : syracuseStep 9337123 = 14005685) B14005685
theorem B3275315 : Blo 646304 3275315 := bstep (se 1 (by rfl) ⟨2456486, by rfl⟩ : syracuseStep 3275315 = 4912973) B4912973
theorem B1636969 : Blo 646304 1636969 := bstep (se 2 (by rfl) ⟨613863, by rfl⟩ : syracuseStep 1636969 = 1227727) B1227727
theorem B6226253 : Blo 646304 6226253 := bstep (se 3 (by rfl) ⟨1167422, by rfl⟩ : syracuseStep 6226253 = 2334845) B2334845
theorem B2458127 : Blo 646304 2458127 := bstep (se 1 (by rfl) ⟨1843595, by rfl⟩ : syracuseStep 2458127 = 3687191) B3687191
theorem B11207231 : Blo 646304 11207231 := bstep (se 1 (by rfl) ⟨8405423, by rfl⟩ : syracuseStep 11207231 = 16810847) B16810847
theorem B820039 : Blo 646304 820039 := bstep (se 1 (by rfl) ⟨615029, by rfl⟩ : syracuseStep 820039 = 1230059) B1230059
theorem B2851969 : Blo 646304 2851969 := bstep (se 2 (by rfl) ⟨1069488, by rfl⟩ : syracuseStep 2851969 = 2138977) B2138977
theorem B4162751 : Blo 646304 4162751 := bstep (se 1 (by rfl) ⟨3122063, by rfl⟩ : syracuseStep 4162751 = 6244127) B6244127
theorem B11044349 : Blo 646304 11044349 := bstep (se 3 (by rfl) ⟨2070815, by rfl⟩ : syracuseStep 11044349 = 4141631) B4141631
theorem B37914169 : Blo 646304 37914169 := bstep (se 2 (by rfl) ⟨14217813, by rfl⟩ : syracuseStep 37914169 = 28435627) B28435627
theorem B11109959 : Blo 646304 11109959 := bstep (se 1 (by rfl) ⟨8332469, by rfl⟩ : syracuseStep 11109959 = 16664939) B16664939
theorem B7505945 : Blo 646304 7505945 := bstep (se 2 (by rfl) ⟨2814729, by rfl⟩ : syracuseStep 7505945 = 5629459) B5629459
theorem B1771753 : Blo 646304 1771753 := bstep (se 2 (by rfl) ⟨664407, by rfl⟩ : syracuseStep 1771753 = 1328815) B1328815
theorem B4164185 : Blo 646304 4164185 := bstep (se 2 (by rfl) ⟨1561569, by rfl⟩ : syracuseStep 4164185 = 3123139) B3123139
theorem B821927 : Blo 646304 821927 := bstep (se 1 (by rfl) ⟨616445, by rfl⟩ : syracuseStep 821927 = 1232891) B1232891
theorem B5245883 : Blo 646304 5245883 := bstep (se 1 (by rfl) ⟨3934412, by rfl⟩ : syracuseStep 5245883 = 7868825) B7868825
theorem B1641647 : Blo 646304 1641647 := bstep (se 1 (by rfl) ⟨1231235, by rfl⟩ : syracuseStep 1641647 = 2462471) B2462471
theorem B11079341 : Blo 646304 11079341 := bstep (se 3 (by rfl) ⟨2077376, by rfl⟩ : syracuseStep 11079341 = 4154753) B4154753
theorem B1478395 : Blo 646304 1478395 := bstep (se 1 (by rfl) ⟨1108796, by rfl⟩ : syracuseStep 1478395 = 2217593) B2217593
theorem B1642265 : Blo 646304 1642265 := bstep (se 2 (by rfl) ⟨615849, by rfl⟩ : syracuseStep 1642265 = 1231699) B1231699
theorem B47189789 : Blo 646304 47189789 := bstep (se 3 (by rfl) ⟨8848085, by rfl⟩ : syracuseStep 47189789 = 17696171) B17696171
theorem B3280823 : Blo 646304 3280823 := bstep (se 1 (by rfl) ⟨2460617, by rfl⟩ : syracuseStep 3280823 = 4921235) B4921235
theorem B1970135 : Blo 646304 1970135 := bstep (se 1 (by rfl) ⟨1477601, by rfl⟩ : syracuseStep 1970135 = 2955203) B2955203
theorem B1642639 : Blo 646304 1642639 := bstep (se 1 (by rfl) ⟨1231979, by rfl⟩ : syracuseStep 1642639 = 2463959) B2463959
theorem B10490255 : Blo 646304 10490255 := bstep (se 1 (by rfl) ⟨7867691, by rfl⟩ : syracuseStep 10490255 = 15735383) B15735383
theorem B26546885 : Blo 646304 26546885 := bstep (se 4 (by rfl) ⟨2488770, by rfl⟩ : syracuseStep 26546885 = 4977541) B4977541
theorem B7869203 : Blo 646304 7869203 := bstep (se 1 (by rfl) ⟨5901902, by rfl⟩ : syracuseStep 7869203 = 11803805) B11803805
theorem B3511457 : Blo 646304 3511457 := bstep (se 2 (by rfl) ⟨1316796, by rfl⟩ : syracuseStep 3511457 = 2633593) B2633593
theorem B1644583 : Blo 646304 1644583 := bstep (se 1 (by rfl) ⟨1233437, by rfl⟩ : syracuseStep 1644583 = 2466875) B2466875
theorem B1841363 : Blo 646304 1841363 := bstep (se 1 (by rfl) ⟨1381022, by rfl⟩ : syracuseStep 1841363 = 2762045) B2762045
theorem B727375 : Blo 646304 727375 := bstep (se 1 (by rfl) ⟨545531, by rfl⟩ : syracuseStep 727375 = 1091063) B1091063
theorem B2070971 : Blo 646304 2070971 := bstep (se 1 (by rfl) ⟨1553228, by rfl⟩ : syracuseStep 2070971 = 3106457) B3106457
theorem B3283901 : Blo 646304 3283901 := bstep (se 3 (by rfl) ⟨615731, by rfl⟩ : syracuseStep 3283901 = 1231463) B1231463
theorem B728059 : Blo 646304 728059 := bstep (se 1 (by rfl) ⟨546044, by rfl⟩ : syracuseStep 728059 = 1092089) B1092089
theorem B728095 : Blo 646304 728095 := bstep (se 1 (by rfl) ⟨546071, by rfl⟩ : syracuseStep 728095 = 1092143) B1092143
theorem B728239 : Blo 646304 728239 := bstep (se 1 (by rfl) ⟨546179, by rfl⟩ : syracuseStep 728239 = 1092359) B1092359
theorem B728383 : Blo 646304 728383 := bstep (se 1 (by rfl) ⟨546287, by rfl⟩ : syracuseStep 728383 = 1092575) B1092575
theorem B115416737 : Blo 646304 115416737 := bstep (se 2 (by rfl) ⟨43281276, by rfl⟩ : syracuseStep 115416737 = 86562553) B86562553
theorem B728959 : Blo 646304 728959 := bstep (se 1 (by rfl) ⟨546719, by rfl⟩ : syracuseStep 728959 = 1093439) B1093439
theorem B15769637 : Blo 646304 15769637 := bstep (se 4 (by rfl) ⟨1478403, by rfl⟩ : syracuseStep 15769637 = 2956807) B2956807
theorem B2072969 : Blo 646304 2072969 := bstep (se 2 (by rfl) ⟨777363, by rfl⟩ : syracuseStep 2072969 = 1554727) B1554727
theorem B1843823 : Blo 646304 1843823 := bstep (se 1 (by rfl) ⟨1382867, by rfl⟩ : syracuseStep 1843823 = 2765735) B2765735
theorem B2073431 : Blo 646304 2073431 := bstep (se 1 (by rfl) ⟨1555073, by rfl⟩ : syracuseStep 2073431 = 3110147) B3110147
theorem B3941291 : Blo 646304 3941291 := bstep (se 1 (by rfl) ⟨2955968, by rfl⟩ : syracuseStep 3941291 = 5911937) B5911937
theorem B7906571 : Blo 646304 7906571 := bstep (se 1 (by rfl) ⟨5929928, by rfl⟩ : syracuseStep 7906571 = 11859857) B11859857
theorem B1845031 : Blo 646304 1845031 := bstep (se 1 (by rfl) ⟨1383773, by rfl⟩ : syracuseStep 1845031 = 2767547) B2767547
theorem B13346693 : Blo 646304 13346693 := bstep (se 4 (by rfl) ⟨1251252, by rfl⟩ : syracuseStep 13346693 = 2502505) B2502505
theorem B6236129 : Blo 646304 6236129 := bstep (se 2 (by rfl) ⟨2338548, by rfl⟩ : syracuseStep 6236129 = 4677097) B4677097
theorem B2762849 : Blo 646304 2762849 := bstep (se 2 (by rfl) ⟨1036068, by rfl⟩ : syracuseStep 2762849 = 2072137) B2072137
theorem B731551 : Blo 646304 731551 := bstep (se 1 (by rfl) ⟨548663, by rfl⟩ : syracuseStep 731551 = 1097327) B1097327
theorem B1845737 : Blo 646304 1845737 := bstep (se 2 (by rfl) ⟨692151, by rfl⟩ : syracuseStep 1845737 = 1384303) B1384303
theorem B3681085 : Blo 646304 3681085 := bstep (se 3 (by rfl) ⟨690203, by rfl⟩ : syracuseStep 3681085 = 1380407) B1380407
theorem B6728609 : Blo 646304 6728609 := bstep (se 2 (by rfl) ⟨2523228, by rfl⟩ : syracuseStep 6728609 = 5046457) B5046457
theorem B1092521 : Blo 646304 1092521 := bstep (se 2 (by rfl) ⟨409695, by rfl⟩ : syracuseStep 1092521 = 819391) B819391
theorem B3746999 : Blo 646304 3746999 := bstep (se 1 (by rfl) ⟨2810249, by rfl⟩ : syracuseStep 3746999 = 5620499) B5620499
theorem B36056335 : Blo 646304 36056335 := bstep (se 1 (by rfl) ⟨27042251, by rfl⟩ : syracuseStep 36056335 = 54084503) B54084503
theorem B6761861 : Blo 646304 6761861 := bstep (se 4 (by rfl) ⟨633924, by rfl⟩ : syracuseStep 6761861 = 1267849) B1267849
theorem B3944551 : Blo 646304 3944551 := bstep (se 1 (by rfl) ⟨2958413, by rfl⟩ : syracuseStep 3944551 = 5916827) B5916827
theorem B6992081 : Blo 646304 6992081 := bstep (se 2 (by rfl) ⟨2622030, by rfl⟩ : syracuseStep 6992081 = 5244061) B5244061
theorem B1454363 : Blo 646304 1454363 := bstep (se 1 (by rfl) ⟨1090772, by rfl⟩ : syracuseStep 1454363 = 2181545) B2181545
theorem B1093945 : Blo 646304 1093945 := bstep (se 2 (by rfl) ⟨410229, by rfl⟩ : syracuseStep 1093945 = 820459) B820459
theorem B1454759 : Blo 646304 1454759 := bstep (se 1 (by rfl) ⟨1091069, by rfl⟩ : syracuseStep 1454759 = 2182139) B2182139
theorem B1848221 : Blo 646304 1848221 := bstep (se 3 (by rfl) ⟨346541, by rfl⟩ : syracuseStep 1848221 = 693083) B693083
theorem B2077609 : Blo 646304 2077609 := bstep (se 2 (by rfl) ⟨779103, by rfl⟩ : syracuseStep 2077609 = 1558207) B1558207
theorem B23606569 : Blo 646304 23606569 := bstep (se 2 (by rfl) ⟨8852463, by rfl⟩ : syracuseStep 23606569 = 17704927) B17704927
theorem B8107451 : Blo 646304 8107451 := bstep (se 1 (by rfl) ⟨6080588, by rfl⟩ : syracuseStep 8107451 = 12161177) B12161177
theorem B3290705 : Blo 646304 3290705 := bstep (se 2 (by rfl) ⟨1234014, by rfl⟩ : syracuseStep 3290705 = 2468029) B2468029
theorem B2766419 : Blo 646304 2766419 := bstep (se 1 (by rfl) ⟨2074814, by rfl⟩ : syracuseStep 2766419 = 4149629) B4149629
theorem B3684001 : Blo 646304 3684001 := bstep (se 2 (by rfl) ⟨1381500, by rfl⟩ : syracuseStep 3684001 = 2763001) B2763001
theorem B3290867 : Blo 646304 3290867 := bstep (se 1 (by rfl) ⟨2468150, by rfl⟩ : syracuseStep 3290867 = 4936301) B4936301
theorem B20002781 : Blo 646304 20002781 := bstep (se 3 (by rfl) ⟨3750521, by rfl⟩ : syracuseStep 20002781 = 7501043) B7501043
theorem B2341001 : Blo 646304 2341001 := bstep (se 2 (by rfl) ⟨877875, by rfl⟩ : syracuseStep 2341001 = 1755751) B1755751
theorem B6666695 : Blo 646304 6666695 := bstep (se 1 (by rfl) ⟨5000021, by rfl⟩ : syracuseStep 6666695 = 10000043) B10000043
theorem B1096247 : Blo 646304 1096247 := bstep (se 1 (by rfl) ⟨822185, by rfl⟩ : syracuseStep 1096247 = 1644371) B1644371
theorem B1457225 : Blo 646304 1457225 := bstep (se 2 (by rfl) ⟨546459, by rfl⟩ : syracuseStep 1457225 = 1092919) B1092919
theorem B2080043 : Blo 646304 2080043 := bstep (se 1 (by rfl) ⟨1560032, by rfl⟩ : syracuseStep 2080043 = 3120065) B3120065
theorem B5258591 : Blo 646304 5258591 := bstep (se 1 (by rfl) ⟨3943943, by rfl⟩ : syracuseStep 5258591 = 7887887) B7887887
theorem B2080171 : Blo 646304 2080171 := bstep (se 1 (by rfl) ⟨1560128, by rfl⟩ : syracuseStep 2080171 = 3120257) B3120257
theorem B1457819 : Blo 646304 1457819 := bstep (se 1 (by rfl) ⟨1093364, by rfl⟩ : syracuseStep 1457819 = 2186729) B2186729
theorem B1458017 : Blo 646304 1458017 := bstep (se 2 (by rfl) ⟨546756, by rfl⟩ : syracuseStep 1458017 = 1093513) B1093513
theorem B1229033 : Blo 646304 1229033 := bstep (se 2 (by rfl) ⟨460887, by rfl⟩ : syracuseStep 1229033 = 921775) B921775
theorem B1851751 : Blo 646304 1851751 := bstep (se 1 (by rfl) ⟨1388813, by rfl⟩ : syracuseStep 1851751 = 2777627) B2777627
theorem B1262675 : Blo 646304 1262675 := bstep (se 1 (by rfl) ⟨947006, by rfl⟩ : syracuseStep 1262675 = 1894013) B1894013
theorem B1459367 : Blo 646304 1459367 := bstep (se 1 (by rfl) ⟨1094525, by rfl⟩ : syracuseStep 1459367 = 2189051) B2189051
theorem B8406251 : Blo 646304 8406251 := bstep (se 1 (by rfl) ⟨6304688, by rfl⟩ : syracuseStep 8406251 = 12609377) B12609377
theorem B1459475 : Blo 646304 1459475 := bstep (se 1 (by rfl) ⟨1094606, by rfl⟩ : syracuseStep 1459475 = 2189213) B2189213
theorem B5523065 : Blo 646304 5523065 := bstep (se 2 (by rfl) ⟨2071149, by rfl⟩ : syracuseStep 5523065 = 4142299) B4142299
theorem B1460105 : Blo 646304 1460105 := bstep (se 2 (by rfl) ⟨547539, by rfl⟩ : syracuseStep 1460105 = 1095079) B1095079
theorem B4147145 : Blo 646304 4147145 := bstep (se 2 (by rfl) ⟨1555179, by rfl⟩ : syracuseStep 4147145 = 3110359) B3110359
theorem B1755113 : Blo 646304 1755113 := bstep (se 2 (by rfl) ⟨658167, by rfl⟩ : syracuseStep 1755113 = 1316335) B1316335
theorem B1231031 : Blo 646304 1231031 := bstep (se 1 (by rfl) ⟨923273, by rfl⟩ : syracuseStep 1231031 = 1846547) B1846547
theorem B1198571 : Blo 646304 1198571 := bstep (se 1 (by rfl) ⟨898928, by rfl⟩ : syracuseStep 1198571 = 1797857) B1797857
theorem B6998521 : Blo 646304 6998521 := bstep (se 2 (by rfl) ⟨2624445, by rfl⟩ : syracuseStep 6998521 = 5248891) B5248891
theorem B1231615 : Blo 646304 1231615 := bstep (se 1 (by rfl) ⟨923711, by rfl⟩ : syracuseStep 1231615 = 1847423) B1847423
theorem B7392059 : Blo 646304 7392059 := bstep (se 1 (by rfl) ⟨5544044, by rfl⟩ : syracuseStep 7392059 = 11088089) B11088089
theorem B11226077 : Blo 646304 11226077 := bstep (se 3 (by rfl) ⟨2104889, by rfl⟩ : syracuseStep 11226077 = 4209779) B4209779
theorem B969695 : Blo 646304 969695 := bstep (se 1 (by rfl) ⟨727271, by rfl⟩ : syracuseStep 969695 = 1454543) B1454543
theorem B970139 : Blo 646304 970139 := bstep (se 1 (by rfl) ⟨727604, by rfl⟩ : syracuseStep 970139 = 1455209) B1455209
theorem B2182625 : Blo 646304 2182625 := bstep (se 2 (by rfl) ⟨818484, by rfl⟩ : syracuseStep 2182625 = 1636969) B1636969
theorem B1461779 : Blo 646304 1461779 := bstep (se 1 (by rfl) ⟨1096334, by rfl⟩ : syracuseStep 1461779 = 2192669) B2192669
theorem B970505 : Blo 646304 970505 := bstep (se 2 (by rfl) ⟨363939, by rfl⟩ : syracuseStep 970505 = 727879) B727879
theorem B970559 : Blo 646304 970559 := bstep (se 1 (by rfl) ⟨727919, by rfl⟩ : syracuseStep 970559 = 1455839) B1455839
theorem B14995439 : Blo 646304 14995439 := bstep (se 1 (by rfl) ⟨11246579, by rfl⟩ : syracuseStep 14995439 = 22493159) B22493159
theorem B970799 : Blo 646304 970799 := bstep (se 1 (by rfl) ⟨728099, by rfl⟩ : syracuseStep 970799 = 1456199) B1456199
theorem B2183543 : Blo 646304 2183543 := bstep (se 1 (by rfl) ⟨1637657, by rfl⟩ : syracuseStep 2183543 = 3275315) B3275315
theorem B971243 : Blo 646304 971243 := bstep (se 1 (by rfl) ⟨728432, by rfl⟩ : syracuseStep 971243 = 1456865) B1456865
theorem B1462841 : Blo 646304 1462841 := bstep (se 2 (by rfl) ⟨548565, by rfl⟩ : syracuseStep 1462841 = 1097131) B1097131
theorem B971369 : Blo 646304 971369 := bstep (se 2 (by rfl) ⟨364263, by rfl⟩ : syracuseStep 971369 = 728527) B728527
theorem B971375 : Blo 646304 971375 := bstep (se 1 (by rfl) ⟨728531, by rfl⟩ : syracuseStep 971375 = 1457063) B1457063
theorem B971495 : Blo 646304 971495 := bstep (se 1 (by rfl) ⟨728621, by rfl⟩ : syracuseStep 971495 = 1457243) B1457243
theorem B971657 : Blo 646304 971657 := bstep (se 2 (by rfl) ⟨364371, by rfl⟩ : syracuseStep 971657 = 728743) B728743
theorem B971999 : Blo 646304 971999 := bstep (se 1 (by rfl) ⟨728999, by rfl⟩ : syracuseStep 971999 = 1457999) B1457999
theorem B972041 : Blo 646304 972041 := bstep (se 2 (by rfl) ⟨364515, by rfl⟩ : syracuseStep 972041 = 729031) B729031
theorem B2184623 : Blo 646304 2184623 := bstep (se 1 (by rfl) ⟨1638467, by rfl⟩ : syracuseStep 2184623 = 3276935) B3276935
theorem B972479 : Blo 646304 972479 := bstep (se 1 (by rfl) ⟨729359, by rfl⟩ : syracuseStep 972479 = 1458719) B1458719
theorem B972521 : Blo 646304 972521 := bstep (se 2 (by rfl) ⟨364695, by rfl⟩ : syracuseStep 972521 = 729391) B729391
theorem B972527 : Blo 646304 972527 := bstep (se 1 (by rfl) ⟨729395, by rfl⟩ : syracuseStep 972527 = 1458791) B1458791
theorem B3496061 : Blo 646304 3496061 := bstep (se 3 (by rfl) ⟨655511, by rfl⟩ : syracuseStep 3496061 = 1311023) B1311023
theorem B10508417 : Blo 646304 10508417 := bstep (se 2 (by rfl) ⟨3940656, by rfl⟩ : syracuseStep 10508417 = 7881313) B7881313
theorem B973031 : Blo 646304 973031 := bstep (se 1 (by rfl) ⟨729773, by rfl⟩ : syracuseStep 973031 = 1459547) B1459547
theorem B973211 : Blo 646304 973211 := bstep (se 1 (by rfl) ⟨729908, by rfl⟩ : syracuseStep 973211 = 1459817) B1459817
theorem B1038791 : Blo 646304 1038791 := bstep (se 1 (by rfl) ⟨779093, by rfl⟩ : syracuseStep 1038791 = 1558187) B1558187
theorem B2185703 : Blo 646304 2185703 := bstep (se 1 (by rfl) ⟨1639277, by rfl⟩ : syracuseStep 2185703 = 3278555) B3278555
theorem B10672793 : Blo 646304 10672793 := bstep (se 2 (by rfl) ⟨4002297, by rfl⟩ : syracuseStep 10672793 = 8004595) B8004595
theorem B973607 : Blo 646304 973607 := bstep (se 1 (by rfl) ⟨730205, by rfl⟩ : syracuseStep 973607 = 1460411) B1460411
theorem B973631 : Blo 646304 973631 := bstep (se 1 (by rfl) ⟨730223, by rfl⟩ : syracuseStep 973631 = 1460447) B1460447
theorem B973931 : Blo 646304 973931 := bstep (se 1 (by rfl) ⟨730448, by rfl⟩ : syracuseStep 973931 = 1460897) B1460897
theorem B2776193 : Blo 646304 2776193 := bstep (se 2 (by rfl) ⟨1041072, by rfl⟩ : syracuseStep 2776193 = 2082145) B2082145
theorem B6216911 : Blo 646304 6216911 := bstep (se 1 (by rfl) ⟨4662683, by rfl⟩ : syracuseStep 6216911 = 9325367) B9325367
theorem B646395 : Blo 646304 646395 := bstep (se 1 (by rfl) ⟨484796, by rfl⟩ : syracuseStep 646395 = 969593) B969593
theorem B974075 : Blo 646304 974075 := bstep (se 1 (by rfl) ⟨730556, by rfl⟩ : syracuseStep 974075 = 1461113) B1461113
theorem B646427 : Blo 646304 646427 := bstep (se 1 (by rfl) ⟨484820, by rfl⟩ : syracuseStep 646427 = 969641) B969641
theorem B974171 : Blo 646304 974171 := bstep (se 1 (by rfl) ⟨730628, by rfl⟩ : syracuseStep 974171 = 1461257) B1461257
theorem B974201 : Blo 646304 974201 := bstep (se 2 (by rfl) ⟨365325, by rfl⟩ : syracuseStep 974201 = 730651) B730651
theorem B646527 : Blo 646304 646527 := bstep (se 1 (by rfl) ⟨484895, by rfl⟩ : syracuseStep 646527 = 969791) B969791
theorem B4152703 : Blo 646304 4152703 := bstep (se 1 (by rfl) ⟨3114527, by rfl⟩ : syracuseStep 4152703 = 6229055) B6229055
theorem B974207 : Blo 646304 974207 := bstep (se 1 (by rfl) ⟨730655, by rfl⟩ : syracuseStep 974207 = 1461311) B1461311
theorem B8314427 : Blo 646304 8314427 := bstep (se 1 (by rfl) ⟨6235820, by rfl⟩ : syracuseStep 8314427 = 12471641) B12471641
theorem B50585309 : Blo 646304 50585309 := bstep (se 3 (by rfl) ⟨9484745, by rfl⟩ : syracuseStep 50585309 = 18969491) B18969491
theorem B646895 : Blo 646304 646895 := bstep (se 1 (by rfl) ⟨485171, by rfl⟩ : syracuseStep 646895 = 970343) B970343
theorem B3497833 : Blo 646304 3497833 := bstep (se 2 (by rfl) ⟨1311687, by rfl⟩ : syracuseStep 3497833 = 2623375) B2623375
theorem B974759 : Blo 646304 974759 := bstep (se 1 (by rfl) ⟨731069, by rfl⟩ : syracuseStep 974759 = 1462139) B1462139
theorem B647151 : Blo 646304 647151 := bstep (se 1 (by rfl) ⟨485363, by rfl⟩ : syracuseStep 647151 = 970727) B970727
theorem B974831 : Blo 646304 974831 := bstep (se 1 (by rfl) ⟨731123, by rfl⟩ : syracuseStep 974831 = 1462247) B1462247
theorem B647231 : Blo 646304 647231 := bstep (se 1 (by rfl) ⟨485423, by rfl⟩ : syracuseStep 647231 = 970847) B970847
theorem B7004227 : Blo 646304 7004227 := bstep (se 1 (by rfl) ⟨5253170, by rfl⟩ : syracuseStep 7004227 = 10506341) B10506341
theorem B647239 : Blo 646304 647239 := bstep (se 1 (by rfl) ⟨485429, by rfl⟩ : syracuseStep 647239 = 970859) B970859
theorem B647271 : Blo 646304 647271 := bstep (se 1 (by rfl) ⟨485453, by rfl⟩ : syracuseStep 647271 = 970907) B970907
theorem B974951 : Blo 646304 974951 := bstep (se 1 (by rfl) ⟨731213, by rfl⟩ : syracuseStep 974951 = 1462427) B1462427
theorem B975083 : Blo 646304 975083 := bstep (se 1 (by rfl) ⟨731312, by rfl⟩ : syracuseStep 975083 = 1462625) B1462625
theorem B975143 : Blo 646304 975143 := bstep (se 1 (by rfl) ⟨731357, by rfl⟩ : syracuseStep 975143 = 1462715) B1462715
theorem B647839 : Blo 646304 647839 := bstep (se 1 (by rfl) ⟨485879, by rfl⟩ : syracuseStep 647839 = 971759) B971759
theorem B10674953 : Blo 646304 10674953 := bstep (se 2 (by rfl) ⟨4003107, by rfl⟩ : syracuseStep 10674953 = 8006215) B8006215
theorem B6939449 : Blo 646304 6939449 := bstep (se 2 (by rfl) ⟨2602293, by rfl⟩ : syracuseStep 6939449 = 5204587) B5204587
theorem B648095 : Blo 646304 648095 := bstep (se 1 (by rfl) ⟨486071, by rfl⟩ : syracuseStep 648095 = 972143) B972143
theorem B648175 : Blo 646304 648175 := bstep (se 1 (by rfl) ⟨486131, by rfl⟩ : syracuseStep 648175 = 972263) B972263
theorem B648283 : Blo 646304 648283 := bstep (se 1 (by rfl) ⟨486212, by rfl⟩ : syracuseStep 648283 = 972425) B972425
theorem B648295 : Blo 646304 648295 := bstep (se 1 (by rfl) ⟨486221, by rfl⟩ : syracuseStep 648295 = 972443) B972443
theorem B648423 : Blo 646304 648423 := bstep (se 1 (by rfl) ⟨486317, by rfl⟩ : syracuseStep 648423 = 972635) B972635
theorem B648679 : Blo 646304 648679 := bstep (se 1 (by rfl) ⟨486509, by rfl⟩ : syracuseStep 648679 = 973019) B973019
theorem B3696191 : Blo 646304 3696191 := bstep (se 1 (by rfl) ⟨2772143, by rfl⟩ : syracuseStep 3696191 = 5544287) B5544287
theorem B648859 : Blo 646304 648859 := bstep (se 1 (by rfl) ⟨486644, by rfl⟩ : syracuseStep 648859 = 973289) B973289
theorem B649119 : Blo 646304 649119 := bstep (se 1 (by rfl) ⟨486839, by rfl⟩ : syracuseStep 649119 = 973679) B973679
theorem B649127 : Blo 646304 649127 := bstep (se 1 (by rfl) ⟨486845, by rfl⟩ : syracuseStep 649127 = 973691) B973691
theorem B878729 : Blo 646304 878729 := bstep (se 2 (by rfl) ⟨329523, by rfl⟩ : syracuseStep 878729 = 659047) B659047
theorem B5531813 : Blo 646304 5531813 := bstep (se 4 (by rfl) ⟨518607, by rfl⟩ : syracuseStep 5531813 = 1037215) B1037215
theorem B13330919 : Blo 646304 13330919 := bstep (se 1 (by rfl) ⟨9998189, by rfl⟩ : syracuseStep 13330919 = 19996379) B19996379
theorem B649703 : Blo 646304 649703 := bstep (se 1 (by rfl) ⟨487277, by rfl⟩ : syracuseStep 649703 = 974555) B974555
theorem B649883 : Blo 646304 649883 := bstep (se 1 (by rfl) ⟨487412, by rfl⟩ : syracuseStep 649883 = 974825) B974825
theorem B2190077 : Blo 646304 2190077 := bstep (se 3 (by rfl) ⟨410639, by rfl⟩ : syracuseStep 2190077 = 821279) B821279
theorem B2192507 : Blo 646304 2192507 := bstep (se 1 (by rfl) ⟨1644380, by rfl⟩ : syracuseStep 2192507 = 3288761) B3288761
theorem B1635977 : Blo 646304 1635977 := bstep (se 2 (by rfl) ⟨613491, by rfl⟩ : syracuseStep 1635977 = 1226983) B1226983
theorem B12449497 : Blo 646304 12449497 := bstep (se 2 (by rfl) ⟨4668561, by rfl⟩ : syracuseStep 12449497 = 9337123) B9337123
theorem B5928875 : Blo 646304 5928875 := bstep (se 1 (by rfl) ⟨4446656, by rfl⟩ : syracuseStep 5928875 = 8893313) B8893313
theorem B7403723 : Blo 646304 7403723 := bstep (se 1 (by rfl) ⟨5552792, by rfl⟩ : syracuseStep 7403723 = 11105585) B11105585
theorem B16021871 : Blo 646304 16021871 := bstep (se 1 (by rfl) ⟨12016403, by rfl⟩ : syracuseStep 16021871 = 24032807) B24032807
theorem B7010975 : Blo 646304 7010975 := bstep (se 1 (by rfl) ⟨5258231, by rfl⟩ : syracuseStep 7010975 = 10516463) B10516463
theorem B4684999 : Blo 646304 4684999 := bstep (se 1 (by rfl) ⟨3513749, by rfl⟩ : syracuseStep 4684999 = 7027499) B7027499
theorem B7405181 : Blo 646304 7405181 := bstep (se 3 (by rfl) ⟨1388471, by rfl⟩ : syracuseStep 7405181 = 2776943) B2776943
theorem B17727275 : Blo 646304 17727275 := bstep (se 1 (by rfl) ⟨13295456, by rfl⟩ : syracuseStep 17727275 = 26590913) B26590913
theorem B9338969 : Blo 646304 9338969 := bstep (se 2 (by rfl) ⟨3502113, by rfl⟩ : syracuseStep 9338969 = 7004227) B7004227
theorem B1638751 : Blo 646304 1638751 := bstep (se 1 (by rfl) ⟨1229063, by rfl⟩ : syracuseStep 1638751 = 2458127) B2458127
theorem B7471487 : Blo 646304 7471487 := bstep (se 1 (by rfl) ⟨5603615, by rfl⟩ : syracuseStep 7471487 = 11207231) B11207231
theorem B3277421 : Blo 646304 3277421 := bstep (se 3 (by rfl) ⟨614516, by rfl⟩ : syracuseStep 3277421 = 1229033) B1229033
theorem B5604167 : Blo 646304 5604167 := bstep (se 1 (by rfl) ⟨4203125, by rfl⟩ : syracuseStep 5604167 = 8406251) B8406251
theorem B7406639 : Blo 646304 7406639 := bstep (se 1 (by rfl) ⟨5554979, by rfl⟩ : syracuseStep 7406639 = 11109959) B11109959
theorem B820687 : Blo 646304 820687 := bstep (se 1 (by rfl) ⟨615515, by rfl⟩ : syracuseStep 820687 = 1231031) B1231031
theorem B3802625 : Blo 646304 3802625 := bstep (se 2 (by rfl) ⟨1425984, by rfl⟩ : syracuseStep 3802625 = 2851969) B2851969
theorem B4916861 : Blo 646304 4916861 := bstep (se 3 (by rfl) ⟨921911, by rfl⟩ : syracuseStep 4916861 = 1843823) B1843823
theorem B2460041 : Blo 646304 2460041 := bstep (se 2 (by rfl) ⟨922515, by rfl⟩ : syracuseStep 2460041 = 1845031) B1845031
theorem B31459859 : Blo 646304 31459859 := bstep (se 1 (by rfl) ⟨23594894, by rfl⟩ : syracuseStep 31459859 = 47189789) B47189789
theorem B1313423 : Blo 646304 1313423 := bstep (se 1 (by rfl) ⟨985067, by rfl⟩ : syracuseStep 1313423 = 1970135) B1970135
theorem B9996959 : Blo 646304 9996959 := bstep (se 1 (by rfl) ⟨7497719, by rfl⟩ : syracuseStep 9996959 = 14995439) B14995439
theorem B2362337 : Blo 646304 2362337 := bstep (se 2 (by rfl) ⟨885876, by rfl⟩ : syracuseStep 2362337 = 1771753) B1771753
theorem B17697923 : Blo 646304 17697923 := bstep (se 1 (by rfl) ⟨13273442, by rfl⟩ : syracuseStep 17697923 = 26546885) B26546885
theorem B5246135 : Blo 646304 5246135 := bstep (se 1 (by rfl) ⟨3934601, by rfl⟩ : syracuseStep 5246135 = 7869203) B7869203
theorem B1642153 : Blo 646304 1642153 := bstep (se 2 (by rfl) ⟨615807, by rfl⟩ : syracuseStep 1642153 = 1231615) B1231615
theorem B2330707 : Blo 646304 2330707 := bstep (se 1 (by rfl) ⟨1748030, by rfl⟩ : syracuseStep 2330707 = 3496061) B3496061
theorem B1380647 : Blo 646304 1380647 := bstep (se 1 (by rfl) ⟨1035485, by rfl⟩ : syracuseStep 1380647 = 2070971) B2070971
theorem B48075113 : Blo 646304 48075113 := bstep (se 2 (by rfl) ⟨18028167, by rfl⟩ : syracuseStep 48075113 = 36056335) B36056335
theorem B7115195 : Blo 646304 7115195 := bstep (se 1 (by rfl) ⟨5336396, by rfl⟩ : syracuseStep 7115195 = 10672793) B10672793
theorem B5542951 : Blo 646304 5542951 := bstep (se 1 (by rfl) ⟨4157213, by rfl⟩ : syracuseStep 5542951 = 8314427) B8314427
theorem B76944491 : Blo 646304 76944491 := bstep (se 1 (by rfl) ⟨57708368, by rfl⟩ : syracuseStep 76944491 = 115416737) B115416737
theorem B33723539 : Blo 646304 33723539 := bstep (se 1 (by rfl) ⟨25292654, by rfl⟩ : syracuseStep 33723539 = 50585309) B50585309
theorem B1381979 : Blo 646304 1381979 := bstep (se 1 (by rfl) ⟨1036484, by rfl⟩ : syracuseStep 1381979 = 2072969) B2072969
theorem B7116635 : Blo 646304 7116635 := bstep (se 1 (by rfl) ⟨5337476, by rfl⟩ : syracuseStep 7116635 = 10674953) B10674953
theorem B4626299 : Blo 646304 4626299 := bstep (se 1 (by rfl) ⟨3469724, by rfl⟩ : syracuseStep 4626299 = 6939449) B6939449
theorem B1382287 : Blo 646304 1382287 := bstep (se 1 (by rfl) ⟨1036715, by rfl⟩ : syracuseStep 1382287 = 2073431) B2073431
theorem B2627527 : Blo 646304 2627527 := bstep (se 1 (by rfl) ⟨1970645, by rfl⟩ : syracuseStep 2627527 = 3941291) B3941291
theorem B2464127 : Blo 646304 2464127 := bstep (se 1 (by rfl) ⟨1848095, by rfl⟩ : syracuseStep 2464127 = 3696191) B3696191
theorem B1841899 : Blo 646304 1841899 := bstep (se 1 (by rfl) ⟨1381424, by rfl⟩ : syracuseStep 1841899 = 2762849) B2762849
theorem B728347 : Blo 646304 728347 := bstep (se 1 (by rfl) ⟨546260, by rfl⟩ : syracuseStep 728347 = 1092521) B1092521
theorem B2497999 : Blo 646304 2497999 := bstep (se 1 (by rfl) ⟨1873499, by rfl⟩ : syracuseStep 2497999 = 3746999) B3746999
theorem B4661387 : Blo 646304 4661387 := bstep (se 1 (by rfl) ⟨3496040, by rfl⟩ : syracuseStep 4661387 = 6992081) B6992081
theorem B1844279 : Blo 646304 1844279 := bstep (se 1 (by rfl) ⟨1383209, by rfl⟩ : syracuseStep 1844279 = 2766419) B2766419
theorem B1090651 : Blo 646304 1090651 := bstep (se 1 (by rfl) ⟨817988, by rfl⟩ : syracuseStep 1090651 = 1635977) B1635977
theorem B730831 : Blo 646304 730831 := bstep (se 1 (by rfl) ⟨548123, by rfl⟩ : syracuseStep 730831 = 1096247) B1096247
theorem B18655109 : Blo 646304 18655109 := bstep (se 4 (by rfl) ⟨1748916, by rfl⟩ : syracuseStep 18655109 = 3497833) B3497833
theorem B1386695 : Blo 646304 1386695 := bstep (se 1 (by rfl) ⟨1040021, by rfl⟩ : syracuseStep 1386695 = 2080043) B2080043
theorem B2469001 : Blo 646304 2469001 := bstep (se 2 (by rfl) ⟨925875, by rfl⟩ : syracuseStep 2469001 = 1851751) B1851751
theorem B3682043 : Blo 646304 3682043 := bstep (se 1 (by rfl) ⟨2761532, by rfl⟩ : syracuseStep 3682043 = 5523065) B5523065
theorem B1093385 : Blo 646304 1093385 := bstep (se 2 (by rfl) ⟨410019, by rfl⟩ : syracuseStep 1093385 = 820039) B820039
theorem B2764763 : Blo 646304 2764763 := bstep (se 1 (by rfl) ⟨2073572, by rfl⟩ : syracuseStep 2764763 = 4147145) B4147145
theorem B4928039 : Blo 646304 4928039 := bstep (se 1 (by rfl) ⟨3696029, by rfl⟩ : syracuseStep 4928039 = 7392059) B7392059
theorem B7484051 : Blo 646304 7484051 := bstep (se 1 (by rfl) ⟨5613038, by rfl⟩ : syracuseStep 7484051 = 11226077) B11226077
theorem B1094431 : Blo 646304 1094431 := bstep (se 1 (by rfl) ⟨820823, by rfl⟩ : syracuseStep 1094431 = 1641647) B1641647
theorem B1455083 : Blo 646304 1455083 := bstep (se 1 (by rfl) ⟨1091312, by rfl⟩ : syracuseStep 1455083 = 2182625) B2182625
theorem B7386227 : Blo 646304 7386227 := bstep (se 1 (by rfl) ⟨5539670, by rfl⟩ : syracuseStep 7386227 = 11079341) B11079341
theorem B1094843 : Blo 646304 1094843 := bstep (se 1 (by rfl) ⟨821132, by rfl⟩ : syracuseStep 1094843 = 1642265) B1642265
theorem B1455695 : Blo 646304 1455695 := bstep (se 1 (by rfl) ⟨1091771, by rfl⟩ : syracuseStep 1455695 = 2183543) B2183543
theorem B6993503 : Blo 646304 6993503 := bstep (se 1 (by rfl) ⟨5245127, by rfl⟩ : syracuseStep 6993503 = 10490255) B10490255
theorem B2340971 : Blo 646304 2340971 := bstep (se 1 (by rfl) ⟨1755728, by rfl⟩ : syracuseStep 2340971 = 3511457) B3511457
theorem B1456415 : Blo 646304 1456415 := bstep (se 1 (by rfl) ⟨1092311, by rfl⟩ : syracuseStep 1456415 = 2184623) B2184623
theorem B1227575 : Blo 646304 1227575 := bstep (se 1 (by rfl) ⟨920681, by rfl⟩ : syracuseStep 1227575 = 1841363) B1841363
theorem B1457135 : Blo 646304 1457135 := bstep (se 1 (by rfl) ⟨1092851, by rfl⟩ : syracuseStep 1457135 = 2185703) B2185703
theorem B1850795 : Blo 646304 1850795 := bstep (se 1 (by rfl) ⟨1388096, by rfl⟩ : syracuseStep 1850795 = 2776193) B2776193
theorem B4144607 : Blo 646304 4144607 := bstep (se 1 (by rfl) ⟨3108455, by rfl⟩ : syracuseStep 4144607 = 6216911) B6216911
theorem B5259401 : Blo 646304 5259401 := bstep (se 2 (by rfl) ⟨1972275, by rfl⟩ : syracuseStep 5259401 = 3944551) B3944551
theorem B6242669 : Blo 646304 6242669 := bstep (se 3 (by rfl) ⟨1170500, by rfl⟩ : syracuseStep 6242669 = 2341001) B2341001
theorem B2343277 : Blo 646304 2343277 := bstep (se 3 (by rfl) ⟨439364, by rfl⟩ : syracuseStep 2343277 = 878729) B878729
theorem B1458593 : Blo 646304 1458593 := bstep (se 2 (by rfl) ⟨546972, by rfl⟩ : syracuseStep 1458593 = 1093945) B1093945
theorem B2770109 : Blo 646304 2770109 := bstep (se 3 (by rfl) ⟨519395, by rfl⟩ : syracuseStep 2770109 = 1038791) B1038791
theorem B2770145 : Blo 646304 2770145 := bstep (se 2 (by rfl) ⟨1038804, by rfl⟩ : syracuseStep 2770145 = 2077609) B2077609
theorem B8897795 : Blo 646304 8897795 := bstep (se 1 (by rfl) ⟨6673346, by rfl⟩ : syracuseStep 8897795 = 13346693) B13346693
theorem B3196189 : Blo 646304 3196189 := bstep (se 3 (by rfl) ⟨599285, by rfl⟩ : syracuseStep 3196189 = 1198571) B1198571
theorem B3687875 : Blo 646304 3687875 := bstep (se 1 (by rfl) ⟨2765906, by rfl⟩ : syracuseStep 3687875 = 5531813) B5531813
theorem B1230491 : Blo 646304 1230491 := bstep (se 1 (by rfl) ⟨922868, by rfl⟩ : syracuseStep 1230491 = 1845737) B1845737
theorem B31475425 : Blo 646304 31475425 := bstep (se 2 (by rfl) ⟨11803284, by rfl⟩ : syracuseStep 31475425 = 23606569) B23606569
theorem B18695933 : Blo 646304 18695933 := bstep (se 3 (by rfl) ⟨3505487, by rfl⟩ : syracuseStep 18695933 = 7010975) B7010975
theorem B1460051 : Blo 646304 1460051 := bstep (se 1 (by rfl) ⟨1095038, by rfl⟩ : syracuseStep 1460051 = 2190077) B2190077
theorem B4507907 : Blo 646304 4507907 := bstep (se 1 (by rfl) ⟨3380930, by rfl⟩ : syracuseStep 4507907 = 6761861) B6761861
theorem B16599329 : Blo 646304 16599329 := bstep (se 2 (by rfl) ⟨6224748, by rfl⟩ : syracuseStep 16599329 = 12449497) B12449497
theorem B969575 : Blo 646304 969575 := bstep (se 1 (by rfl) ⟨727181, by rfl⟩ : syracuseStep 969575 = 1454363) B1454363
theorem B969833 : Blo 646304 969833 := bstep (se 2 (by rfl) ⟨363687, by rfl⟩ : syracuseStep 969833 = 727375) B727375
theorem B969839 : Blo 646304 969839 := bstep (se 1 (by rfl) ⟨727379, by rfl⟩ : syracuseStep 969839 = 1454759) B1454759
theorem B1232147 : Blo 646304 1232147 := bstep (se 1 (by rfl) ⟨924110, by rfl⟩ : syracuseStep 1232147 = 1848221) B1848221
theorem B1461671 : Blo 646304 1461671 := bstep (se 1 (by rfl) ⟨1096253, by rfl⟩ : syracuseStep 1461671 = 2192507) B2192507
theorem B3952583 : Blo 646304 3952583 := bstep (se 1 (by rfl) ⟨2964437, by rfl⟩ : syracuseStep 3952583 = 5928875) B5928875
theorem B7884773 : Blo 646304 7884773 := bstep (se 4 (by rfl) ⟨739197, by rfl⟩ : syracuseStep 7884773 = 1478395) B1478395
theorem B970745 : Blo 646304 970745 := bstep (se 2 (by rfl) ⟨364029, by rfl⟩ : syracuseStep 970745 = 728059) B728059
theorem B970793 : Blo 646304 970793 := bstep (se 2 (by rfl) ⟨364047, by rfl⟩ : syracuseStep 970793 = 728095) B728095
theorem B4935815 : Blo 646304 4935815 := bstep (se 1 (by rfl) ⟨3701861, by rfl⟩ : syracuseStep 4935815 = 7403723) B7403723
theorem B970985 : Blo 646304 970985 := bstep (se 2 (by rfl) ⟨364119, by rfl⟩ : syracuseStep 970985 = 728239) B728239
theorem B6246665 : Blo 646304 6246665 := bstep (se 2 (by rfl) ⟨2342499, by rfl⟩ : syracuseStep 6246665 = 4684999) B4684999
theorem B4444463 : Blo 646304 4444463 := bstep (se 1 (by rfl) ⟨3333347, by rfl⟩ : syracuseStep 4444463 = 6666695) B6666695
theorem B971177 : Blo 646304 971177 := bstep (se 2 (by rfl) ⟨364191, by rfl⟩ : syracuseStep 971177 = 728383) B728383
theorem B2773561 : Blo 646304 2773561 := bstep (se 2 (by rfl) ⟨1040085, by rfl⟩ : syracuseStep 2773561 = 2080171) B2080171
theorem B971483 : Blo 646304 971483 := bstep (se 1 (by rfl) ⟨728612, by rfl⟩ : syracuseStep 971483 = 1457225) B1457225
theorem B4936787 : Blo 646304 4936787 := bstep (se 1 (by rfl) ⟨3702590, by rfl⟩ : syracuseStep 4936787 = 7405181) B7405181
theorem B971879 : Blo 646304 971879 := bstep (se 1 (by rfl) ⟨728909, by rfl⟩ : syracuseStep 971879 = 1457819) B1457819
theorem B971945 : Blo 646304 971945 := bstep (se 2 (by rfl) ⟨364479, by rfl⟩ : syracuseStep 971945 = 728959) B728959
theorem B11818183 : Blo 646304 11818183 := bstep (se 1 (by rfl) ⟨8863637, by rfl⟩ : syracuseStep 11818183 = 17727275) B17727275
theorem B972011 : Blo 646304 972011 := bstep (se 1 (by rfl) ⟨729008, by rfl⟩ : syracuseStep 972011 = 1458017) B1458017
theorem B4150835 : Blo 646304 4150835 := bstep (se 1 (by rfl) ⟨3113126, by rfl⟩ : syracuseStep 4150835 = 6226253) B6226253
theorem B972911 : Blo 646304 972911 := bstep (se 1 (by rfl) ⟨729683, by rfl⟩ : syracuseStep 972911 = 1459367) B1459367
theorem B2775167 : Blo 646304 2775167 := bstep (se 1 (by rfl) ⟨2081375, by rfl⟩ : syracuseStep 2775167 = 4162751) B4162751
theorem B972983 : Blo 646304 972983 := bstep (se 1 (by rfl) ⟨729737, by rfl⟩ : syracuseStep 972983 = 1459475) B1459475
theorem B7362899 : Blo 646304 7362899 := bstep (se 1 (by rfl) ⟨5522174, by rfl⟩ : syracuseStep 7362899 = 11044349) B11044349
theorem B973403 : Blo 646304 973403 := bstep (se 1 (by rfl) ⟨730052, by rfl⟩ : syracuseStep 973403 = 1460105) B1460105
theorem B5003963 : Blo 646304 5003963 := bstep (se 1 (by rfl) ⟨3752972, by rfl⟩ : syracuseStep 5003963 = 7505945) B7505945
theorem B2776123 : Blo 646304 2776123 := bstep (se 1 (by rfl) ⟨2082092, by rfl⟩ : syracuseStep 2776123 = 4164185) B4164185
theorem B3497255 : Blo 646304 3497255 := bstep (se 1 (by rfl) ⟨2622941, by rfl⟩ : syracuseStep 3497255 = 5245883) B5245883
theorem B646463 : Blo 646304 646463 := bstep (se 1 (by rfl) ⟨484847, by rfl⟩ : syracuseStep 646463 = 969695) B969695
theorem B50552225 : Blo 646304 50552225 := bstep (se 2 (by rfl) ⟨18957084, by rfl⟩ : syracuseStep 50552225 = 37914169) B37914169
theorem B646759 : Blo 646304 646759 := bstep (se 1 (by rfl) ⟨485069, by rfl⟩ : syracuseStep 646759 = 970139) B970139
theorem B974519 : Blo 646304 974519 := bstep (se 1 (by rfl) ⟨730889, by rfl⟩ : syracuseStep 974519 = 1461779) B1461779
theorem B647003 : Blo 646304 647003 := bstep (se 1 (by rfl) ⟨485252, by rfl⟩ : syracuseStep 647003 = 970505) B970505
theorem B647039 : Blo 646304 647039 := bstep (se 1 (by rfl) ⟨485279, by rfl⟩ : syracuseStep 647039 = 970559) B970559
theorem B2187215 : Blo 646304 2187215 := bstep (se 1 (by rfl) ⟨1640411, by rfl⟩ : syracuseStep 2187215 = 3280823) B3280823
theorem B647199 : Blo 646304 647199 := bstep (se 1 (by rfl) ⟨485399, by rfl⟩ : syracuseStep 647199 = 970799) B970799
theorem B3367133 : Blo 646304 3367133 := bstep (se 3 (by rfl) ⟨631337, by rfl⟩ : syracuseStep 3367133 = 1262675) B1262675
theorem B647495 : Blo 646304 647495 := bstep (se 1 (by rfl) ⟨485621, by rfl⟩ : syracuseStep 647495 = 971243) B971243
theorem B975227 : Blo 646304 975227 := bstep (se 1 (by rfl) ⟨731420, by rfl⟩ : syracuseStep 975227 = 1462841) B1462841
theorem B647579 : Blo 646304 647579 := bstep (se 1 (by rfl) ⟨485684, by rfl⟩ : syracuseStep 647579 = 971369) B971369
theorem B647583 : Blo 646304 647583 := bstep (se 1 (by rfl) ⟨485687, by rfl⟩ : syracuseStep 647583 = 971375) B971375
theorem B647663 : Blo 646304 647663 := bstep (se 1 (by rfl) ⟨485747, by rfl⟩ : syracuseStep 647663 = 971495) B971495
theorem B975401 : Blo 646304 975401 := bstep (se 2 (by rfl) ⟨365775, by rfl⟩ : syracuseStep 975401 = 731551) B731551
theorem B647771 : Blo 646304 647771 := bstep (se 1 (by rfl) ⟨485828, by rfl⟩ : syracuseStep 647771 = 971657) B971657
theorem B9331361 : Blo 646304 9331361 := bstep (se 2 (by rfl) ⟨3499260, by rfl⟩ : syracuseStep 9331361 = 6998521) B6998521
theorem B647999 : Blo 646304 647999 := bstep (se 1 (by rfl) ⟨485999, by rfl⟩ : syracuseStep 647999 = 971999) B971999
theorem B648027 : Blo 646304 648027 := bstep (se 1 (by rfl) ⟨486020, by rfl⟩ : syracuseStep 648027 = 972041) B972041
theorem B4908113 : Blo 646304 4908113 := bstep (se 2 (by rfl) ⟨1840542, by rfl⟩ : syracuseStep 4908113 = 3681085) B3681085
theorem B648319 : Blo 646304 648319 := bstep (se 1 (by rfl) ⟨486239, by rfl⟩ : syracuseStep 648319 = 972479) B972479
theorem B648347 : Blo 646304 648347 := bstep (se 1 (by rfl) ⟨486260, by rfl⟩ : syracuseStep 648347 = 972521) B972521
theorem B648351 : Blo 646304 648351 := bstep (se 1 (by rfl) ⟨486263, by rfl⟩ : syracuseStep 648351 = 972527) B972527
theorem B7005611 : Blo 646304 7005611 := bstep (se 1 (by rfl) ⟨5254208, by rfl⟩ : syracuseStep 7005611 = 10508417) B10508417
theorem B648687 : Blo 646304 648687 := bstep (se 1 (by rfl) ⟨486515, by rfl⟩ : syracuseStep 648687 = 973031) B973031
theorem B648807 : Blo 646304 648807 := bstep (se 1 (by rfl) ⟨486605, by rfl⟩ : syracuseStep 648807 = 973211) B973211
theorem B649071 : Blo 646304 649071 := bstep (se 1 (by rfl) ⟨486803, by rfl⟩ : syracuseStep 649071 = 973607) B973607
theorem B649087 : Blo 646304 649087 := bstep (se 1 (by rfl) ⟨486815, by rfl⟩ : syracuseStep 649087 = 973631) B973631
theorem B2189267 : Blo 646304 2189267 := bstep (se 1 (by rfl) ⟨1641950, by rfl⟩ : syracuseStep 2189267 = 3283901) B3283901
theorem B649287 : Blo 646304 649287 := bstep (se 1 (by rfl) ⟨486965, by rfl⟩ : syracuseStep 649287 = 973931) B973931
theorem B649383 : Blo 646304 649383 := bstep (se 1 (by rfl) ⟨487037, by rfl⟩ : syracuseStep 649383 = 974075) B974075
theorem B649447 : Blo 646304 649447 := bstep (se 1 (by rfl) ⟨487085, by rfl⟩ : syracuseStep 649447 = 974171) B974171
theorem B649467 : Blo 646304 649467 := bstep (se 1 (by rfl) ⟨487100, by rfl⟩ : syracuseStep 649467 = 974201) B974201
theorem B649471 : Blo 646304 649471 := bstep (se 1 (by rfl) ⟨487103, by rfl⟩ : syracuseStep 649471 = 974207) B974207
theorem B4680301 : Blo 646304 4680301 := bstep (se 3 (by rfl) ⟨877556, by rfl⟩ : syracuseStep 4680301 = 1755113) B1755113
theorem B649839 : Blo 646304 649839 := bstep (se 1 (by rfl) ⟨487379, by rfl⟩ : syracuseStep 649839 = 974759) B974759
theorem B649887 : Blo 646304 649887 := bstep (se 1 (by rfl) ⟨487415, by rfl⟩ : syracuseStep 649887 = 974831) B974831
theorem B10513091 : Blo 646304 10513091 := bstep (se 1 (by rfl) ⟨7884818, by rfl⟩ : syracuseStep 10513091 = 15769637) B15769637
theorem B649967 : Blo 646304 649967 := bstep (se 1 (by rfl) ⟨487475, by rfl⟩ : syracuseStep 649967 = 974951) B974951
theorem B650055 : Blo 646304 650055 := bstep (se 1 (by rfl) ⟨487541, by rfl⟩ : syracuseStep 650055 = 975083) B975083
theorem B2190185 : Blo 646304 2190185 := bstep (se 2 (by rfl) ⟨821319, by rfl⟩ : syracuseStep 2190185 = 1642639) B1642639
theorem B650095 : Blo 646304 650095 := bstep (se 1 (by rfl) ⟨487571, by rfl⟩ : syracuseStep 650095 = 975143) B975143
theorem B5271047 : Blo 646304 5271047 := bstep (se 1 (by rfl) ⟨3953285, by rfl⟩ : syracuseStep 5271047 = 7906571) B7906571
theorem B35549117 : Blo 646304 35549117 := bstep (se 3 (by rfl) ⟨6665459, by rfl⟩ : syracuseStep 35549117 = 13330919) B13330919
theorem B4157419 : Blo 646304 4157419 := bstep (se 1 (by rfl) ⟨3118064, by rfl⟩ : syracuseStep 4157419 = 6236129) B6236129
theorem B2191805 : Blo 646304 2191805 := bstep (se 3 (by rfl) ⟨410963, by rfl⟩ : syracuseStep 2191805 = 821927) B821927
theorem B4485739 : Blo 646304 4485739 := bstep (se 1 (by rfl) ⟨3364304, by rfl⟩ : syracuseStep 4485739 = 6728609) B6728609
theorem B4912001 : Blo 646304 4912001 := bstep (se 2 (by rfl) ⟨1842000, by rfl⟩ : syracuseStep 4912001 = 3684001) B3684001
theorem B2192777 : Blo 646304 2192777 := bstep (se 2 (by rfl) ⟨822291, by rfl⟩ : syracuseStep 2192777 = 1644583) B1644583
theorem B5404967 : Blo 646304 5404967 := bstep (se 1 (by rfl) ⟨4053725, by rfl⟩ : syracuseStep 5404967 = 8107451) B8107451
theorem B2193803 : Blo 646304 2193803 := bstep (se 1 (by rfl) ⟨1645352, by rfl⟩ : syracuseStep 2193803 = 3290705) B3290705
theorem B2193911 : Blo 646304 2193911 := bstep (se 1 (by rfl) ⟨1645433, by rfl⟩ : syracuseStep 2193911 = 3290867) B3290867
theorem B13335187 : Blo 646304 13335187 := bstep (se 1 (by rfl) ⟨10001390, by rfl⟩ : syracuseStep 13335187 = 20002781) B20002781
theorem B10681247 : Blo 646304 10681247 := bstep (se 1 (by rfl) ⟨8010935, by rfl⟩ : syracuseStep 10681247 = 16021871) B16021871
theorem B5536937 : Blo 646304 5536937 := bstep (se 2 (by rfl) ⟨2076351, by rfl⟩ : syracuseStep 5536937 = 4152703) B4152703
theorem B3505727 : Blo 646304 3505727 := bstep (se 1 (by rfl) ⟨2629295, by rfl⟩ : syracuseStep 3505727 = 5258591) B5258591
theorem B6225979 : Blo 646304 6225979 := bstep (se 1 (by rfl) ⟨4669484, by rfl⟩ : syracuseStep 6225979 = 9338969) B9338969
theorem B3506267 : Blo 646304 3506267 := bstep (se 1 (by rfl) ⟨2629700, by rfl⟩ : syracuseStep 3506267 = 5259401) B5259401
theorem B4161779 : Blo 646304 4161779 := bstep (se 1 (by rfl) ⟨3121334, by rfl⟩ : syracuseStep 4161779 = 6242669) B6242669
theorem B3736111 : Blo 646304 3736111 := bstep (se 1 (by rfl) ⟨2802083, by rfl⟩ : syracuseStep 3736111 = 5604167) B5604167
theorem B5931863 : Blo 646304 5931863 := bstep (se 1 (by rfl) ⟨4448897, by rfl⟩ : syracuseStep 5931863 = 8897795) B8897795
theorem B2458583 : Blo 646304 2458583 := bstep (se 1 (by rfl) ⟨1843937, by rfl⟩ : syracuseStep 2458583 = 3687875) B3687875
theorem B19923965 : Blo 646304 19923965 := bstep (se 3 (by rfl) ⟨3735743, by rfl⟩ : syracuseStep 19923965 = 7471487) B7471487
theorem B3277907 : Blo 646304 3277907 := bstep (se 1 (by rfl) ⟨2458430, by rfl⟩ : syracuseStep 3277907 = 4916861) B4916861
theorem B1640027 : Blo 646304 1640027 := bstep (se 1 (by rfl) ⟨1230020, by rfl⟩ : syracuseStep 1640027 = 2460041) B2460041
theorem B20973239 : Blo 646304 20973239 := bstep (se 1 (by rfl) ⟨15729929, by rfl⟩ : syracuseStep 20973239 = 31459859) B31459859
theorem B4261585 : Blo 646304 4261585 := bstep (se 2 (by rfl) ⟨1598094, by rfl⟩ : syracuseStep 4261585 = 3196189) B3196189
theorem B1574891 : Blo 646304 1574891 := bstep (se 1 (by rfl) ⟨1181168, by rfl⟩ : syracuseStep 1574891 = 2362337) B2362337
theorem B11798615 : Blo 646304 11798615 := bstep (se 1 (by rfl) ⟨8848961, by rfl⟩ : syracuseStep 11798615 = 17697923) B17697923
theorem B821431 : Blo 646304 821431 := bstep (se 1 (by rfl) ⟨616073, by rfl⟩ : syracuseStep 821431 = 1232147) B1232147
theorem B4164443 : Blo 646304 4164443 := bstep (se 1 (by rfl) ⟨3123332, by rfl⟩ : syracuseStep 4164443 = 6246665) B6246665
theorem B920431 : Blo 646304 920431 := bstep (se 1 (by rfl) ⟨690323, by rfl⟩ : syracuseStep 920431 = 1380647) B1380647
theorem B32050075 : Blo 646304 32050075 := bstep (se 1 (by rfl) ⟨24037556, by rfl⟩ : syracuseStep 32050075 = 48075113) B48075113
theorem B22482359 : Blo 646304 22482359 := bstep (se 1 (by rfl) ⟨16861769, by rfl⟩ : syracuseStep 22482359 = 33723539) B33723539
theorem B3084199 : Blo 646304 3084199 := bstep (se 1 (by rfl) ⟨2313149, by rfl⟩ : syracuseStep 3084199 = 4626299) B4626299
theorem B1642751 : Blo 646304 1642751 := bstep (se 1 (by rfl) ⟨1232063, by rfl⟩ : syracuseStep 1642751 = 2464127) B2464127
theorem B3281309 : Blo 646304 3281309 := bstep (se 3 (by rfl) ⟨615245, by rfl⟩ : syracuseStep 3281309 = 1230491) B1230491
theorem B2331503 : Blo 646304 2331503 := bstep (se 1 (by rfl) ⟨1748627, by rfl⟩ : syracuseStep 2331503 = 3497255) B3497255
theorem B5543225 : Blo 646304 5543225 := bstep (se 2 (by rfl) ⟨2078709, by rfl⟩ : syracuseStep 5543225 = 4157419) B4157419
theorem B924463 : Blo 646304 924463 := bstep (se 1 (by rfl) ⟨693347, by rfl⟩ : syracuseStep 924463 = 1386695) B1386695
theorem B3514031 : Blo 646304 3514031 := bstep (se 1 (by rfl) ⟨2635523, by rfl⟩ : syracuseStep 3514031 = 5271047) B5271047
theorem B728923 : Blo 646304 728923 := bstep (se 1 (by rfl) ⟨546692, by rfl⟩ : syracuseStep 728923 = 1093385) B1093385
theorem B1843049 : Blo 646304 1843049 := bstep (se 2 (by rfl) ⟨691143, by rfl⟩ : syracuseStep 1843049 = 1382287) B1382287
theorem B23699411 : Blo 646304 23699411 := bstep (se 1 (by rfl) ⟨17774558, by rfl⟩ : syracuseStep 23699411 = 35549117) B35549117
theorem B1843175 : Blo 646304 1843175 := bstep (se 1 (by rfl) ⟨1382381, by rfl⟩ : syracuseStep 1843175 = 2764763) B2764763
theorem B3285359 : Blo 646304 3285359 := bstep (se 1 (by rfl) ⟨2464019, by rfl⟩ : syracuseStep 3285359 = 4928039) B4928039
theorem B4989367 : Blo 646304 4989367 := bstep (se 1 (by rfl) ⟨3742025, by rfl⟩ : syracuseStep 4989367 = 7484051) B7484051
theorem B4924151 : Blo 646304 4924151 := bstep (se 1 (by rfl) ⟨3693113, by rfl⟩ : syracuseStep 4924151 = 7386227) B7386227
theorem B729895 : Blo 646304 729895 := bstep (se 1 (by rfl) ⟨547421, by rfl⟩ : syracuseStep 729895 = 1094843) B1094843
theorem B4662335 : Blo 646304 4662335 := bstep (se 1 (by rfl) ⟨3496751, by rfl⟩ : syracuseStep 4662335 = 6993503) B6993503
theorem B9348605 : Blo 646304 9348605 := bstep (se 3 (by rfl) ⟨1752863, by rfl⟩ : syracuseStep 9348605 = 3505727) B3505727
theorem B7120831 : Blo 646304 7120831 := bstep (se 1 (by rfl) ⟨5340623, by rfl⟩ : syracuseStep 7120831 = 10681247) B10681247
theorem B2763071 : Blo 646304 2763071 := bstep (se 1 (by rfl) ⟨2072303, by rfl⟩ : syracuseStep 2763071 = 4144607) B4144607
theorem B3124369 : Blo 646304 3124369 := bstep (se 2 (by rfl) ⟨1171638, by rfl⟩ : syracuseStep 3124369 = 2343277) B2343277
theorem B1846739 : Blo 646304 1846739 := bstep (se 1 (by rfl) ⟨1385054, by rfl⟩ : syracuseStep 1846739 = 2770109) B2770109
theorem B1846763 : Blo 646304 1846763 := bstep (se 1 (by rfl) ⟨1385072, by rfl⟩ : syracuseStep 1846763 = 2770145) B2770145
theorem B2535083 : Blo 646304 2535083 := bstep (se 1 (by rfl) ⟨1901312, by rfl⟩ : syracuseStep 2535083 = 3802625) B3802625
theorem B12463955 : Blo 646304 12463955 := bstep (se 1 (by rfl) ⟨9347966, by rfl⟩ : syracuseStep 12463955 = 18695933) B18695933
theorem B1454201 : Blo 646304 1454201 := bstep (se 2 (by rfl) ⟨545325, by rfl⟩ : syracuseStep 1454201 = 1090651) B1090651
theorem B6664639 : Blo 646304 6664639 := bstep (se 1 (by rfl) ⟨4998479, by rfl⟩ : syracuseStep 6664639 = 9996959) B9996959
theorem B1094249 : Blo 646304 1094249 := bstep (se 2 (by rfl) ⟨410343, by rfl⟩ : syracuseStep 1094249 = 820687) B820687
theorem B2635055 : Blo 646304 2635055 := bstep (se 1 (by rfl) ⟨1976291, by rfl⟩ : syracuseStep 2635055 = 3952583) B3952583
theorem B5256515 : Blo 646304 5256515 := bstep (se 1 (by rfl) ⟨3942386, by rfl⟩ : syracuseStep 5256515 = 7884773) B7884773
theorem B3290543 : Blo 646304 3290543 := bstep (se 1 (by rfl) ⟨2467907, by rfl⟩ : syracuseStep 3290543 = 4935815) B4935815
theorem B2962975 : Blo 646304 2962975 := bstep (se 1 (by rfl) ⟨2222231, by rfl⟩ : syracuseStep 2962975 = 4444463) B4444463
theorem B3291191 : Blo 646304 3291191 := bstep (se 1 (by rfl) ⟨2468393, by rfl⟩ : syracuseStep 3291191 = 4936787) B4936787
theorem B51296327 : Blo 646304 51296327 := bstep (se 1 (by rfl) ⟨38472245, by rfl⟩ : syracuseStep 51296327 = 76944491) B76944491
theorem B6240401 : Blo 646304 6240401 := bstep (se 2 (by rfl) ⟨2340150, by rfl⟩ : syracuseStep 6240401 = 4680301) B4680301
theorem B2767223 : Blo 646304 2767223 := bstep (se 1 (by rfl) ⟨2075417, by rfl⟩ : syracuseStep 2767223 = 4150835) B4150835
theorem B1850111 : Blo 646304 1850111 := bstep (se 1 (by rfl) ⟨1387583, by rfl⟩ : syracuseStep 1850111 = 2775167) B2775167
theorem B3292001 : Blo 646304 3292001 := bstep (se 2 (by rfl) ⟨1234500, by rfl⟩ : syracuseStep 3292001 = 2469001) B2469001
theorem B3685277 : Blo 646304 3685277 := bstep (se 3 (by rfl) ⟨690989, by rfl⟩ : syracuseStep 3685277 = 1381979) B1381979
theorem B33701483 : Blo 646304 33701483 := bstep (se 1 (by rfl) ⟨25276112, by rfl⟩ : syracuseStep 33701483 = 50552225) B50552225
theorem B1458143 : Blo 646304 1458143 := bstep (se 1 (by rfl) ⟨1093607, by rfl⟩ : syracuseStep 1458143 = 2187215) B2187215
theorem B2244755 : Blo 646304 2244755 := bstep (se 1 (by rfl) ⟨1683566, by rfl⟩ : syracuseStep 2244755 = 3367133) B3367133
theorem B1229519 : Blo 646304 1229519 := bstep (se 1 (by rfl) ⟨922139, by rfl⟩ : syracuseStep 1229519 = 1844279) B1844279
theorem B5980985 : Blo 646304 5980985 := bstep (se 2 (by rfl) ⟨2242869, by rfl⟩ : syracuseStep 5980985 = 4485739) B4485739
theorem B4670407 : Blo 646304 4670407 := bstep (se 1 (by rfl) ⟨3502805, by rfl⟩ : syracuseStep 4670407 = 7005611) B7005611
theorem B1459241 : Blo 646304 1459241 := bstep (se 2 (by rfl) ⟨547215, by rfl⟩ : syracuseStep 1459241 = 1094431) B1094431
theorem B12436739 : Blo 646304 12436739 := bstep (se 1 (by rfl) ⟨9327554, by rfl⟩ : syracuseStep 12436739 = 18655109) B18655109
theorem B1459511 : Blo 646304 1459511 := bstep (se 1 (by rfl) ⟨1094633, by rfl⟩ : syracuseStep 1459511 = 2189267) B2189267
theorem B7390601 : Blo 646304 7390601 := bstep (se 2 (by rfl) ⟨2771475, by rfl⟩ : syracuseStep 7390601 = 5542951) B5542951
theorem B1460123 : Blo 646304 1460123 := bstep (se 1 (by rfl) ⟨1095092, by rfl⟩ : syracuseStep 1460123 = 2190185) B2190185
theorem B1461203 : Blo 646304 1461203 := bstep (se 1 (by rfl) ⟨1095902, by rfl⟩ : syracuseStep 1461203 = 2191805) B2191805
theorem B970055 : Blo 646304 970055 := bstep (se 1 (by rfl) ⟨727541, by rfl⟩ : syracuseStep 970055 = 1455083) B1455083
theorem B17780249 : Blo 646304 17780249 := bstep (se 2 (by rfl) ⟨6667593, by rfl⟩ : syracuseStep 17780249 = 13335187) B13335187
theorem B1461851 : Blo 646304 1461851 := bstep (se 1 (by rfl) ⟨1096388, by rfl⟩ : syracuseStep 1461851 = 2192777) B2192777
theorem B970463 : Blo 646304 970463 := bstep (se 1 (by rfl) ⟨727847, by rfl⟩ : syracuseStep 970463 = 1455695) B1455695
theorem B1560647 : Blo 646304 1560647 := bstep (se 1 (by rfl) ⟨1170485, by rfl⟩ : syracuseStep 1560647 = 2340971) B2340971
theorem B970943 : Blo 646304 970943 := bstep (se 1 (by rfl) ⟨728207, by rfl⟩ : syracuseStep 970943 = 1456415) B1456415
theorem B1462535 : Blo 646304 1462535 := bstep (se 1 (by rfl) ⟨1096901, by rfl⟩ : syracuseStep 1462535 = 2193803) B2193803
theorem B1462607 : Blo 646304 1462607 := bstep (se 1 (by rfl) ⟨1096955, by rfl⟩ : syracuseStep 1462607 = 2193911) B2193911
theorem B971129 : Blo 646304 971129 := bstep (se 2 (by rfl) ⟨364173, by rfl⟩ : syracuseStep 971129 = 728347) B728347
theorem B3330665 : Blo 646304 3330665 := bstep (se 2 (by rfl) ⟨1248999, by rfl⟩ : syracuseStep 3330665 = 2497999) B2497999
theorem B971423 : Blo 646304 971423 := bstep (se 1 (by rfl) ⟨728567, by rfl⟩ : syracuseStep 971423 = 1457135) B1457135
theorem B3691291 : Blo 646304 3691291 := bstep (se 1 (by rfl) ⟨2768468, by rfl⟩ : syracuseStep 3691291 = 5536937) B5536937
theorem B1233863 : Blo 646304 1233863 := bstep (se 1 (by rfl) ⟨925397, by rfl⟩ : syracuseStep 1233863 = 1850795) B1850795
theorem B972395 : Blo 646304 972395 := bstep (se 1 (by rfl) ⟨729296, by rfl⟩ : syracuseStep 972395 = 1458593) B1458593
theorem B2184947 : Blo 646304 2184947 := bstep (se 1 (by rfl) ⟨1638710, by rfl⟩ : syracuseStep 2184947 = 3277421) B3277421
theorem B2185001 : Blo 646304 2185001 := bstep (se 2 (by rfl) ⟨819375, by rfl⟩ : syracuseStep 2185001 = 1638751) B1638751
theorem B4937759 : Blo 646304 4937759 := bstep (se 1 (by rfl) ⟨3703319, by rfl⟩ : syracuseStep 4937759 = 7406639) B7406639
theorem B973367 : Blo 646304 973367 := bstep (se 1 (by rfl) ⟨730025, by rfl⟩ : syracuseStep 973367 = 1460051) B1460051
theorem B11066219 : Blo 646304 11066219 := bstep (se 1 (by rfl) ⟨8299664, by rfl⟩ : syracuseStep 11066219 = 16599329) B16599329
theorem B875615 : Blo 646304 875615 := bstep (se 1 (by rfl) ⟨656711, by rfl⟩ : syracuseStep 875615 = 1313423) B1313423
theorem B646383 : Blo 646304 646383 := bstep (se 1 (by rfl) ⟨484787, by rfl⟩ : syracuseStep 646383 = 969575) B969575
theorem B646555 : Blo 646304 646555 := bstep (se 1 (by rfl) ⟨484916, by rfl⟩ : syracuseStep 646555 = 969833) B969833
theorem B646559 : Blo 646304 646559 := bstep (se 1 (by rfl) ⟨484919, by rfl⟩ : syracuseStep 646559 = 969839) B969839
theorem B3497423 : Blo 646304 3497423 := bstep (se 1 (by rfl) ⟨2623067, by rfl⟩ : syracuseStep 3497423 = 5246135) B5246135
theorem B974441 : Blo 646304 974441 := bstep (se 2 (by rfl) ⟨365415, by rfl⟩ : syracuseStep 974441 = 730831) B730831
theorem B974447 : Blo 646304 974447 := bstep (se 1 (by rfl) ⟨730835, by rfl⟩ : syracuseStep 974447 = 1461671) B1461671
theorem B41967233 : Blo 646304 41967233 := bstep (se 2 (by rfl) ⟨15737712, by rfl⟩ : syracuseStep 41967233 = 31475425) B31475425
theorem B647163 : Blo 646304 647163 := bstep (se 1 (by rfl) ⟨485372, by rfl⟩ : syracuseStep 647163 = 970745) B970745
theorem B647195 : Blo 646304 647195 := bstep (se 1 (by rfl) ⟨485396, by rfl⟩ : syracuseStep 647195 = 970793) B970793
theorem B647323 : Blo 646304 647323 := bstep (se 1 (by rfl) ⟨485492, by rfl⟩ : syracuseStep 647323 = 970985) B970985
theorem B647451 : Blo 646304 647451 := bstep (se 1 (by rfl) ⟨485588, by rfl⟩ : syracuseStep 647451 = 971177) B971177
theorem B4743463 : Blo 646304 4743463 := bstep (se 1 (by rfl) ⟨3557597, by rfl⟩ : syracuseStep 4743463 = 7115195) B7115195
theorem B647655 : Blo 646304 647655 := bstep (se 1 (by rfl) ⟨485741, by rfl⟩ : syracuseStep 647655 = 971483) B971483
theorem B647919 : Blo 646304 647919 := bstep (se 1 (by rfl) ⟨485939, by rfl⟩ : syracuseStep 647919 = 971879) B971879
theorem B647963 : Blo 646304 647963 := bstep (se 1 (by rfl) ⟨485972, by rfl⟩ : syracuseStep 647963 = 971945) B971945
theorem B648007 : Blo 646304 648007 := bstep (se 1 (by rfl) ⟨486005, by rfl⟩ : syracuseStep 648007 = 972011) B972011
theorem B4744423 : Blo 646304 4744423 := bstep (se 1 (by rfl) ⟨3558317, by rfl⟩ : syracuseStep 4744423 = 7116635) B7116635
theorem B648607 : Blo 646304 648607 := bstep (se 1 (by rfl) ⟨486455, by rfl⟩ : syracuseStep 648607 = 972911) B972911
theorem B648655 : Blo 646304 648655 := bstep (se 1 (by rfl) ⟨486491, by rfl⟩ : syracuseStep 648655 = 972983) B972983
theorem B4908599 : Blo 646304 4908599 := bstep (se 1 (by rfl) ⟨3681449, by rfl⟩ : syracuseStep 4908599 = 7362899) B7362899
theorem B648935 : Blo 646304 648935 := bstep (se 1 (by rfl) ⟨486701, by rfl⟩ : syracuseStep 648935 = 973403) B973403
theorem B3335975 : Blo 646304 3335975 := bstep (se 1 (by rfl) ⟨2501981, by rfl⟩ : syracuseStep 3335975 = 5003963) B5003963
theorem B2189537 : Blo 646304 2189537 := bstep (se 2 (by rfl) ⟨821076, by rfl⟩ : syracuseStep 2189537 = 1642153) B1642153
theorem B649679 : Blo 646304 649679 := bstep (se 1 (by rfl) ⟨487259, by rfl⟩ : syracuseStep 649679 = 974519) B974519
theorem B3107591 : Blo 646304 3107591 := bstep (se 1 (by rfl) ⟨2330693, by rfl⟩ : syracuseStep 3107591 = 4661387) B4661387
theorem B3107609 : Blo 646304 3107609 := bstep (se 2 (by rfl) ⟨1165353, by rfl⟩ : syracuseStep 3107609 = 2330707) B2330707
theorem B650151 : Blo 646304 650151 := bstep (se 1 (by rfl) ⟨487613, by rfl⟩ : syracuseStep 650151 = 975227) B975227
theorem B650267 : Blo 646304 650267 := bstep (se 1 (by rfl) ⟨487700, by rfl⟩ : syracuseStep 650267 = 975401) B975401
theorem B6220907 : Blo 646304 6220907 := bstep (se 1 (by rfl) ⟨4665680, by rfl⟩ : syracuseStep 6220907 = 9331361) B9331361
theorem B12021085 : Blo 646304 12021085 := bstep (se 3 (by rfl) ⟨2253953, by rfl⟩ : syracuseStep 12021085 = 4507907) B4507907
theorem B3272075 : Blo 646304 3272075 := bstep (se 1 (by rfl) ⟨2454056, by rfl⟩ : syracuseStep 3272075 = 4908113) B4908113
theorem B3698081 : Blo 646304 3698081 := bstep (se 2 (by rfl) ⟨1386780, by rfl⟩ : syracuseStep 3698081 = 2773561) B2773561
theorem B15757577 : Blo 646304 15757577 := bstep (se 2 (by rfl) ⟨5909091, by rfl⟩ : syracuseStep 15757577 = 11818183) B11818183
theorem B7008727 : Blo 646304 7008727 := bstep (se 1 (by rfl) ⟨5256545, by rfl⟩ : syracuseStep 7008727 = 10513091) B10513091
theorem B3273533 : Blo 646304 3273533 := bstep (se 3 (by rfl) ⟨613787, by rfl⟩ : syracuseStep 3273533 = 1227575) B1227575
theorem B2454695 : Blo 646304 2454695 := bstep (se 1 (by rfl) ⟨1841021, by rfl⟩ : syracuseStep 2454695 = 3682043) B3682043
theorem B3503369 : Blo 646304 3503369 := bstep (se 2 (by rfl) ⟨1313763, by rfl⟩ : syracuseStep 3503369 = 2627527) B2627527
theorem B3274667 : Blo 646304 3274667 := bstep (se 1 (by rfl) ⟨2456000, by rfl⟩ : syracuseStep 3274667 = 4912001) B4912001
theorem B2455865 : Blo 646304 2455865 := bstep (se 2 (by rfl) ⟨920949, by rfl⟩ : syracuseStep 2455865 = 1841899) B1841899
theorem B3701497 : Blo 646304 3701497 := bstep (se 2 (by rfl) ⟨1388061, by rfl⟩ : syracuseStep 3701497 = 2776123) B2776123
theorem B3603311 : Blo 646304 3603311 := bstep (se 1 (by rfl) ⟨2702483, by rfl⟩ : syracuseStep 3603311 = 5404967) B5404967
theorem B4161725 : Blo 646304 4161725 := bstep (se 3 (by rfl) ⟨780323, by rfl⟩ : syracuseStep 4161725 = 1560647) B1560647
theorem B6324617 : Blo 646304 6324617 := bstep (se 2 (by rfl) ⟨2371731, by rfl⟩ : syracuseStep 6324617 = 4743463) B4743463
theorem B6652489 : Blo 646304 6652489 := bstep (se 2 (by rfl) ⟨2494683, by rfl⟩ : syracuseStep 6652489 = 4989367) B4989367
theorem B1639055 : Blo 646304 1639055 := bstep (se 1 (by rfl) ⟨1229291, by rfl⟩ : syracuseStep 1639055 = 2458583) B2458583
theorem B4981481 : Blo 646304 4981481 := bstep (se 2 (by rfl) ⟨1868055, by rfl⟩ : syracuseStep 4981481 = 3736111) B3736111
theorem B8291159 : Blo 646304 8291159 := bstep (se 1 (by rfl) ⟨6218369, by rfl⟩ : syracuseStep 8291159 = 12436739) B12436739
theorem B9339893 : Blo 646304 9339893 := bstep (se 5 (by rfl) ⟨437807, by rfl⟩ : syracuseStep 9339893 = 875615) B875615
theorem B6227209 : Blo 646304 6227209 := bstep (se 2 (by rfl) ⟨2335203, by rfl⟩ : syracuseStep 6227209 = 4670407) B4670407
theorem B1049927 : Blo 646304 1049927 := bstep (se 1 (by rfl) ⟨787445, by rfl⟩ : syracuseStep 1049927 = 1574891) B1574891
theorem B7865743 : Blo 646304 7865743 := bstep (se 1 (by rfl) ⟨5899307, by rfl⟩ : syracuseStep 7865743 = 11798615) B11798615
theorem B6325897 : Blo 646304 6325897 := bstep (se 2 (by rfl) ⟨2372211, by rfl⟩ : syracuseStep 6325897 = 4744423) B4744423
theorem B3278717 : Blo 646304 3278717 := bstep (se 3 (by rfl) ⟨614759, by rfl⟩ : syracuseStep 3278717 = 1229519) B1229519
theorem B822575 : Blo 646304 822575 := bstep (se 1 (by rfl) ⟨616931, by rfl⟩ : syracuseStep 822575 = 1233863) B1233863
theorem B9342317 : Blo 646304 9342317 := bstep (se 3 (by rfl) ⟨1751684, by rfl⟩ : syracuseStep 9342317 = 3503369) B3503369
theorem B42733433 : Blo 646304 42733433 := bstep (se 2 (by rfl) ⟨16025037, by rfl⟩ : syracuseStep 42733433 = 32050075) B32050075
theorem B4165825 : Blo 646304 4165825 := bstep (se 2 (by rfl) ⟨1562184, by rfl⟩ : syracuseStep 4165825 = 3124369) B3124369
theorem B16028113 : Blo 646304 16028113 := bstep (se 2 (by rfl) ⟨6010542, by rfl⟩ : syracuseStep 16028113 = 12021085) B12021085
theorem B7377479 : Blo 646304 7377479 := bstep (se 1 (by rfl) ⟨5533109, by rfl⟩ : syracuseStep 7377479 = 11066219) B11066219
theorem B15799607 : Blo 646304 15799607 := bstep (se 1 (by rfl) ⟨11849705, by rfl⟩ : syracuseStep 15799607 = 23699411) B23699411
theorem B3282767 : Blo 646304 3282767 := bstep (se 1 (by rfl) ⟨2462075, by rfl⟩ : syracuseStep 3282767 = 4924151) B4924151
theorem B8886185 : Blo 646304 8886185 := bstep (se 2 (by rfl) ⟨3332319, by rfl⟩ : syracuseStep 8886185 = 6664639) B6664639
theorem B9344969 : Blo 646304 9344969 := bstep (se 2 (by rfl) ⟨3504363, by rfl⟩ : syracuseStep 9344969 = 7008727) B7008727
theorem B6232403 : Blo 646304 6232403 := bstep (se 1 (by rfl) ⟨4674302, by rfl⟩ : syracuseStep 6232403 = 9348605) B9348605
theorem B4921721 : Blo 646304 4921721 := bstep (se 2 (by rfl) ⟨1845645, by rfl⟩ : syracuseStep 4921721 = 3691291) B3691291
theorem B1842047 : Blo 646304 1842047 := bstep (se 1 (by rfl) ⟨1381535, by rfl⟩ : syracuseStep 1842047 = 2763071) B2763071
theorem B2071727 : Blo 646304 2071727 := bstep (se 1 (by rfl) ⟨1553795, by rfl⟩ : syracuseStep 2071727 = 3107591) B3107591
theorem B2071739 : Blo 646304 2071739 := bstep (se 1 (by rfl) ⟨1553804, by rfl⟩ : syracuseStep 2071739 = 3107609) B3107609
theorem B2465387 : Blo 646304 2465387 := bstep (se 1 (by rfl) ⟨1849040, by rfl⟩ : syracuseStep 2465387 = 3698081) B3698081
theorem B729499 : Blo 646304 729499 := bstep (se 1 (by rfl) ⟨547124, by rfl⟩ : syracuseStep 729499 = 1094249) B1094249
theorem B4924637 : Blo 646304 4924637 := bstep (se 3 (by rfl) ⟨923369, by rfl⟩ : syracuseStep 4924637 = 1846739) B1846739
theorem B1844815 : Blo 646304 1844815 := bstep (se 1 (by rfl) ⟨1383611, by rfl⟩ : syracuseStep 1844815 = 2767223) B2767223
theorem B2402207 : Blo 646304 2402207 := bstep (se 1 (by rfl) ⟨1801655, by rfl⟩ : syracuseStep 2402207 = 3603311) B3603311
theorem B2337511 : Blo 646304 2337511 := bstep (se 1 (by rfl) ⟨1753133, by rfl⟩ : syracuseStep 2337511 = 3506267) B3506267
theorem B8301305 : Blo 646304 8301305 := bstep (se 2 (by rfl) ⟨3112989, by rfl⟩ : syracuseStep 8301305 = 6225979) B6225979
theorem B13282643 : Blo 646304 13282643 := bstep (se 1 (by rfl) ⟨9961982, by rfl⟩ : syracuseStep 13282643 = 19923965) B19923965
theorem B4927067 : Blo 646304 4927067 := bstep (se 1 (by rfl) ⟨3695300, by rfl⟩ : syracuseStep 4927067 = 7390601) B7390601
theorem B1093351 : Blo 646304 1093351 := bstep (se 1 (by rfl) ⟨820013, by rfl⟩ : syracuseStep 1093351 = 1640027) B1640027
theorem B5682113 : Blo 646304 5682113 := bstep (se 2 (by rfl) ⟨2130792, by rfl⟩ : syracuseStep 5682113 = 4261585) B4261585
theorem B14988239 : Blo 646304 14988239 := bstep (se 1 (by rfl) ⟨11241179, by rfl⟩ : syracuseStep 14988239 = 22482359) B22482359
theorem B1095167 : Blo 646304 1095167 := bstep (se 1 (by rfl) ⟨821375, by rfl⟩ : syracuseStep 1095167 = 1642751) B1642751
theorem B1095241 : Blo 646304 1095241 := bstep (se 2 (by rfl) ⟨410715, by rfl⟩ : syracuseStep 1095241 = 821431) B821431
theorem B1554335 : Blo 646304 1554335 := bstep (se 1 (by rfl) ⟨1165751, by rfl⟩ : syracuseStep 1554335 = 2331503) B2331503
theorem B1227241 : Blo 646304 1227241 := bstep (se 2 (by rfl) ⟨460215, by rfl⟩ : syracuseStep 1227241 = 920431) B920431
theorem B1456631 : Blo 646304 1456631 := bstep (se 1 (by rfl) ⟨1092473, by rfl⟩ : syracuseStep 1456631 = 2184947) B2184947
theorem B1456667 : Blo 646304 1456667 := bstep (se 1 (by rfl) ⟨1092500, by rfl⟩ : syracuseStep 1456667 = 2185001) B2185001
theorem B3291839 : Blo 646304 3291839 := bstep (se 1 (by rfl) ⟨2468879, by rfl⟩ : syracuseStep 3291839 = 4937759) B4937759
theorem B4930469 : Blo 646304 4930469 := bstep (se 4 (by rfl) ⟨462231, by rfl⟩ : syracuseStep 4930469 = 924463) B924463
theorem B2342687 : Blo 646304 2342687 := bstep (se 1 (by rfl) ⟨1757015, by rfl⟩ : syracuseStep 2342687 = 3514031) B3514031
theorem B1228699 : Blo 646304 1228699 := bstep (se 1 (by rfl) ⟨921524, by rfl⟩ : syracuseStep 1228699 = 1843049) B1843049
theorem B1228783 : Blo 646304 1228783 := bstep (se 1 (by rfl) ⟨921587, by rfl⟩ : syracuseStep 1228783 = 1843175) B1843175
theorem B1459691 : Blo 646304 1459691 := bstep (se 1 (by rfl) ⟨1094768, by rfl⟩ : syracuseStep 1459691 = 2189537) B2189537
theorem B3950633 : Blo 646304 3950633 := bstep (se 2 (by rfl) ⟨1481487, by rfl⟩ : syracuseStep 3950633 = 2962975) B2962975
theorem B4147271 : Blo 646304 4147271 := bstep (se 1 (by rfl) ⟨3110453, by rfl⟩ : syracuseStep 4147271 = 6220907) B6220907
theorem B2181383 : Blo 646304 2181383 := bstep (se 1 (by rfl) ⟨1636037, by rfl⟩ : syracuseStep 2181383 = 3272075) B3272075
theorem B1231175 : Blo 646304 1231175 := bstep (se 1 (by rfl) ⟨923381, by rfl⟩ : syracuseStep 1231175 = 1846763) B1846763
theorem B1690055 : Blo 646304 1690055 := bstep (se 1 (by rfl) ⟨1267541, by rfl⟩ : syracuseStep 1690055 = 2535083) B2535083
theorem B8309303 : Blo 646304 8309303 := bstep (se 1 (by rfl) ⟨6231977, by rfl⟩ : syracuseStep 8309303 = 12463955) B12463955
theorem B969467 : Blo 646304 969467 := bstep (se 1 (by rfl) ⟨727100, by rfl⟩ : syracuseStep 969467 = 1454201) B1454201
theorem B10505051 : Blo 646304 10505051 := bstep (se 1 (by rfl) ⟨7878788, by rfl⟩ : syracuseStep 10505051 = 15757577) B15757577
theorem B2182355 : Blo 646304 2182355 := bstep (se 1 (by rfl) ⟨1636766, by rfl⟩ : syracuseStep 2182355 = 3273533) B3273533
theorem B1756703 : Blo 646304 1756703 := bstep (se 1 (by rfl) ⟨1317527, by rfl⟩ : syracuseStep 1756703 = 2635055) B2635055
theorem B4935329 : Blo 646304 4935329 := bstep (se 2 (by rfl) ⟨1850748, by rfl⟩ : syracuseStep 4935329 = 3701497) B3701497
theorem B9326461 : Blo 646304 9326461 := bstep (se 3 (by rfl) ⟨1748711, by rfl⟩ : syracuseStep 9326461 = 3497423) B3497423
theorem B2183111 : Blo 646304 2183111 := bstep (se 1 (by rfl) ⟨1637333, by rfl⟩ : syracuseStep 2183111 = 3274667) B3274667
theorem B34197551 : Blo 646304 34197551 := bstep (se 1 (by rfl) ⟨25648163, by rfl⟩ : syracuseStep 34197551 = 51296327) B51296327
theorem B1233407 : Blo 646304 1233407 := bstep (se 1 (by rfl) ⟨925055, by rfl⟩ : syracuseStep 1233407 = 1850111) B1850111
theorem B22467655 : Blo 646304 22467655 := bstep (se 1 (by rfl) ⟨16850741, by rfl⟩ : syracuseStep 22467655 = 33701483) B33701483
theorem B971897 : Blo 646304 971897 := bstep (se 2 (by rfl) ⟨364461, by rfl⟩ : syracuseStep 971897 = 728923) B728923
theorem B972095 : Blo 646304 972095 := bstep (se 1 (by rfl) ⟨729071, by rfl⟩ : syracuseStep 972095 = 1458143) B1458143
theorem B1496503 : Blo 646304 1496503 := bstep (se 1 (by rfl) ⟨1122377, by rfl⟩ : syracuseStep 1496503 = 2244755) B2244755
theorem B2774519 : Blo 646304 2774519 := bstep (se 1 (by rfl) ⟨2080889, by rfl⟩ : syracuseStep 2774519 = 4161779) B4161779
theorem B3987323 : Blo 646304 3987323 := bstep (se 1 (by rfl) ⟨2990492, by rfl⟩ : syracuseStep 3987323 = 5980985) B5980985
theorem B3954575 : Blo 646304 3954575 := bstep (se 1 (by rfl) ⟨2965931, by rfl⟩ : syracuseStep 3954575 = 5931863) B5931863
theorem B972827 : Blo 646304 972827 := bstep (se 1 (by rfl) ⟨729620, by rfl⟩ : syracuseStep 972827 = 1459241) B1459241
theorem B2185271 : Blo 646304 2185271 := bstep (se 1 (by rfl) ⟨1638953, by rfl⟩ : syracuseStep 2185271 = 3277907) B3277907
theorem B973007 : Blo 646304 973007 := bstep (se 1 (by rfl) ⟨729755, by rfl⟩ : syracuseStep 973007 = 1459511) B1459511
theorem B973193 : Blo 646304 973193 := bstep (se 2 (by rfl) ⟨364947, by rfl⟩ : syracuseStep 973193 = 729895) B729895
theorem B13982159 : Blo 646304 13982159 := bstep (se 1 (by rfl) ⟨10486619, by rfl⟩ : syracuseStep 13982159 = 20973239) B20973239
theorem B973415 : Blo 646304 973415 := bstep (se 1 (by rfl) ⟨730061, by rfl⟩ : syracuseStep 973415 = 1460123) B1460123
theorem B2776295 : Blo 646304 2776295 := bstep (se 1 (by rfl) ⟨2082221, by rfl⟩ : syracuseStep 2776295 = 4164443) B4164443
theorem B974135 : Blo 646304 974135 := bstep (se 1 (by rfl) ⟨730601, by rfl⟩ : syracuseStep 974135 = 1461203) B1461203
theorem B646703 : Blo 646304 646703 := bstep (se 1 (by rfl) ⟨485027, by rfl⟩ : syracuseStep 646703 = 970055) B970055
theorem B11853499 : Blo 646304 11853499 := bstep (se 1 (by rfl) ⟨8890124, by rfl⟩ : syracuseStep 11853499 = 17780249) B17780249
theorem B974567 : Blo 646304 974567 := bstep (se 1 (by rfl) ⟨730925, by rfl⟩ : syracuseStep 974567 = 1461851) B1461851
theorem B646975 : Blo 646304 646975 := bstep (se 1 (by rfl) ⟨485231, by rfl⟩ : syracuseStep 646975 = 970463) B970463
theorem B9494441 : Blo 646304 9494441 := bstep (se 2 (by rfl) ⟨3560415, by rfl⟩ : syracuseStep 9494441 = 7120831) B7120831
theorem B647295 : Blo 646304 647295 := bstep (se 1 (by rfl) ⟨485471, by rfl⟩ : syracuseStep 647295 = 970943) B970943
theorem B975023 : Blo 646304 975023 := bstep (se 1 (by rfl) ⟨731267, by rfl⟩ : syracuseStep 975023 = 1462535) B1462535
theorem B975071 : Blo 646304 975071 := bstep (se 1 (by rfl) ⟨731303, by rfl⟩ : syracuseStep 975071 = 1462607) B1462607
theorem B647419 : Blo 646304 647419 := bstep (se 1 (by rfl) ⟨485564, by rfl⟩ : syracuseStep 647419 = 971129) B971129
theorem B2187539 : Blo 646304 2187539 := bstep (se 1 (by rfl) ⟨1640654, by rfl⟩ : syracuseStep 2187539 = 3281309) B3281309
theorem B2220443 : Blo 646304 2220443 := bstep (se 1 (by rfl) ⟨1665332, by rfl⟩ : syracuseStep 2220443 = 3330665) B3330665
theorem B647615 : Blo 646304 647615 := bstep (se 1 (by rfl) ⟨485711, by rfl⟩ : syracuseStep 647615 = 971423) B971423
theorem B14017373 : Blo 646304 14017373 := bstep (se 3 (by rfl) ⟨2628257, by rfl⟩ : syracuseStep 14017373 = 5256515) B5256515
theorem B3695483 : Blo 646304 3695483 := bstep (se 1 (by rfl) ⟨2771612, by rfl⟩ : syracuseStep 3695483 = 5543225) B5543225
theorem B648263 : Blo 646304 648263 := bstep (se 1 (by rfl) ⟨486197, by rfl⟩ : syracuseStep 648263 = 972395) B972395
theorem B648911 : Blo 646304 648911 := bstep (se 1 (by rfl) ⟨486683, by rfl⟩ : syracuseStep 648911 = 973367) B973367
theorem B649627 : Blo 646304 649627 := bstep (se 1 (by rfl) ⟨487220, by rfl⟩ : syracuseStep 649627 = 974441) B974441
theorem B649631 : Blo 646304 649631 := bstep (se 1 (by rfl) ⟨487223, by rfl⟩ : syracuseStep 649631 = 974447) B974447
theorem B27978155 : Blo 646304 27978155 := bstep (se 1 (by rfl) ⟨20983616, by rfl⟩ : syracuseStep 27978155 = 41967233) B41967233
theorem B2190239 : Blo 646304 2190239 := bstep (se 1 (by rfl) ⟨1642679, by rfl⟩ : syracuseStep 2190239 = 3285359) B3285359
theorem B3108223 : Blo 646304 3108223 := bstep (se 1 (by rfl) ⟨2331167, by rfl⟩ : syracuseStep 3108223 = 4662335) B4662335
theorem B3272399 : Blo 646304 3272399 := bstep (se 1 (by rfl) ⟨2454299, by rfl⟩ : syracuseStep 3272399 = 4908599) B4908599
theorem B2223983 : Blo 646304 2223983 := bstep (se 1 (by rfl) ⟨1667987, by rfl⟩ : syracuseStep 2223983 = 3335975) B3335975
theorem B1636463 : Blo 646304 1636463 := bstep (se 1 (by rfl) ⟨1227347, by rfl⟩ : syracuseStep 1636463 = 2454695) B2454695
theorem B65796245 : Blo 646304 65796245 := bstep (se 6 (by rfl) ⟨1542099, by rfl⟩ : syracuseStep 65796245 = 3084199) B3084199
theorem B2193695 : Blo 646304 2193695 := bstep (se 1 (by rfl) ⟨1645271, by rfl⟩ : syracuseStep 2193695 = 3290543) B3290543
theorem B2194127 : Blo 646304 2194127 := bstep (se 1 (by rfl) ⟨1645595, by rfl⟩ : syracuseStep 2194127 = 3291191) B3291191
theorem B4160267 : Blo 646304 4160267 := bstep (se 1 (by rfl) ⟨3120200, by rfl⟩ : syracuseStep 4160267 = 6240401) B6240401
theorem B1637243 : Blo 646304 1637243 := bstep (se 1 (by rfl) ⟨1227932, by rfl⟩ : syracuseStep 1637243 = 2455865) B2455865
theorem B2194667 : Blo 646304 2194667 := bstep (se 1 (by rfl) ⟨1646000, by rfl⟩ : syracuseStep 2194667 = 3292001) B3292001
theorem B2456851 : Blo 646304 2456851 := bstep (se 1 (by rfl) ⟨1842638, by rfl⟩ : syracuseStep 2456851 = 3685277) B3685277
theorem B6226595 : Blo 646304 6226595 := bstep (se 1 (by rfl) ⟨4669946, by rfl⟩ : syracuseStep 6226595 = 9339893) B9339893
theorem B820783 : Blo 646304 820783 := bstep (se 1 (by rfl) ⟨615587, by rfl⟩ : syracuseStep 820783 = 1231175) B1231175
theorem B5539535 : Blo 646304 5539535 := bstep (se 1 (by rfl) ⟨4154651, by rfl⟩ : syracuseStep 5539535 = 8309303) B8309303
theorem B10487657 : Blo 646304 10487657 := bstep (se 2 (by rfl) ⟨3932871, by rfl⟩ : syracuseStep 10487657 = 7865743) B7865743
theorem B2459753 : Blo 646304 2459753 := bstep (se 2 (by rfl) ⟨922407, by rfl⟩ : syracuseStep 2459753 = 1844815) B1844815
theorem B6228211 : Blo 646304 6228211 := bstep (se 1 (by rfl) ⟨4671158, by rfl⟩ : syracuseStep 6228211 = 9342317) B9342317
theorem B4918319 : Blo 646304 4918319 := bstep (se 1 (by rfl) ⟨3688739, by rfl⟩ : syracuseStep 4918319 = 7377479) B7377479
theorem B3116681 : Blo 646304 3116681 := bstep (se 2 (by rfl) ⟨1168755, by rfl⟩ : syracuseStep 3116681 = 2337511) B2337511
theorem B2658215 : Blo 646304 2658215 := bstep (se 1 (by rfl) ⟨1993661, by rfl⟩ : syracuseStep 2658215 = 3987323) B3987323
theorem B6229979 : Blo 646304 6229979 := bstep (se 1 (by rfl) ⟨4672484, by rfl⟩ : syracuseStep 6229979 = 9344969) B9344969
theorem B3281147 : Blo 646304 3281147 := bstep (se 1 (by rfl) ⟨2460860, by rfl⟩ : syracuseStep 3281147 = 4921721) B4921721
theorem B1381151 : Blo 646304 1381151 := bstep (se 1 (by rfl) ⟨1035863, by rfl⟩ : syracuseStep 1381151 = 2071727) B2071727
theorem B1381159 : Blo 646304 1381159 := bstep (se 1 (by rfl) ⟨1035869, by rfl⟩ : syracuseStep 1381159 = 2071739) B2071739
theorem B1643591 : Blo 646304 1643591 := bstep (se 1 (by rfl) ⟨1232693, by rfl⟩ : syracuseStep 1643591 = 2465387) B2465387
theorem B6329627 : Blo 646304 6329627 := bstep (se 1 (by rfl) ⟨4747220, by rfl⟩ : syracuseStep 6329627 = 9494441) B9494441
theorem B1480295 : Blo 646304 1480295 := bstep (se 1 (by rfl) ⟨1110221, by rfl⟩ : syracuseStep 1480295 = 2220443) B2220443
theorem B9344915 : Blo 646304 9344915 := bstep (se 1 (by rfl) ⟨7008686, by rfl⟩ : syracuseStep 9344915 = 14017373) B14017373
theorem B2463655 : Blo 646304 2463655 := bstep (se 1 (by rfl) ⟨1847741, by rfl⟩ : syracuseStep 2463655 = 3695483) B3695483
theorem B21370817 : Blo 646304 21370817 := bstep (se 2 (by rfl) ⟨8014056, by rfl⟩ : syracuseStep 21370817 = 16028113) B16028113
theorem B3283091 : Blo 646304 3283091 := bstep (se 1 (by rfl) ⟨2462318, by rfl⟩ : syracuseStep 3283091 = 4924637) B4924637
theorem B29956873 : Blo 646304 29956873 := bstep (se 2 (by rfl) ⟨11233827, by rfl⟩ : syracuseStep 29956873 = 22467655) B22467655
theorem B18652103 : Blo 646304 18652103 := bstep (se 1 (by rfl) ⟨13989077, by rfl⟩ : syracuseStep 18652103 = 27978155) B27978155
theorem B8855095 : Blo 646304 8855095 := bstep (se 1 (by rfl) ⟨6641321, by rfl⟩ : syracuseStep 8855095 = 13282643) B13282643
theorem B3284711 : Blo 646304 3284711 := bstep (se 1 (by rfl) ⟨2463533, by rfl⟩ : syracuseStep 3284711 = 4927067) B4927067
theorem B730111 : Blo 646304 730111 := bstep (se 1 (by rfl) ⟨547583, by rfl⟩ : syracuseStep 730111 = 1095167) B1095167
theorem B1090975 : Blo 646304 1090975 := bstep (se 1 (by rfl) ⟨818231, by rfl⟩ : syracuseStep 1090975 = 1636463) B1636463
theorem B1091495 : Blo 646304 1091495 := bstep (se 1 (by rfl) ⟨818621, by rfl⟩ : syracuseStep 1091495 = 1637243) B1637243
theorem B3286979 : Blo 646304 3286979 := bstep (se 1 (by rfl) ⟨2465234, by rfl⟩ : syracuseStep 3286979 = 4930469) B4930469
theorem B15804665 : Blo 646304 15804665 := bstep (se 2 (by rfl) ⟨5926749, by rfl⟩ : syracuseStep 15804665 = 11853499) B11853499
theorem B1092703 : Blo 646304 1092703 := bstep (se 1 (by rfl) ⟨819527, by rfl⟩ : syracuseStep 1092703 = 1639055) B1639055
theorem B3289085 : Blo 646304 3289085 := bstep (se 3 (by rfl) ⟨616703, by rfl⟩ : syracuseStep 3289085 = 1233407) B1233407
theorem B2764847 : Blo 646304 2764847 := bstep (se 1 (by rfl) ⟨2073635, by rfl⟩ : syracuseStep 2764847 = 4147271) B4147271
theorem B1454255 : Blo 646304 1454255 := bstep (se 1 (by rfl) ⟨1090691, by rfl⟩ : syracuseStep 1454255 = 2181383) B2181383
theorem B1126703 : Blo 646304 1126703 := bstep (se 1 (by rfl) ⟨845027, by rfl⟩ : syracuseStep 1126703 = 1690055) B1690055
theorem B8302945 : Blo 646304 8302945 := bstep (se 2 (by rfl) ⟨3113604, by rfl⟩ : syracuseStep 8302945 = 6227209) B6227209
theorem B1454903 : Blo 646304 1454903 := bstep (se 1 (by rfl) ⟨1091177, by rfl⟩ : syracuseStep 1454903 = 2182355) B2182355
theorem B8434529 : Blo 646304 8434529 := bstep (se 2 (by rfl) ⟨3162948, by rfl⟩ : syracuseStep 8434529 = 6325897) B6325897
theorem B3290219 : Blo 646304 3290219 := bstep (se 1 (by rfl) ⟨2467664, by rfl⟩ : syracuseStep 3290219 = 4935329) B4935329
theorem B28488955 : Blo 646304 28488955 := bstep (se 1 (by rfl) ⟨21366716, by rfl⟩ : syracuseStep 28488955 = 42733433) B42733433
theorem B1455407 : Blo 646304 1455407 := bstep (se 1 (by rfl) ⟨1091555, by rfl⟩ : syracuseStep 1455407 = 2183111) B2183111
theorem B2799805 : Blo 646304 2799805 := bstep (se 3 (by rfl) ⟨524963, by rfl⟩ : syracuseStep 2799805 = 1049927) B1049927
theorem B10533071 : Blo 646304 10533071 := bstep (se 1 (by rfl) ⟨7899803, by rfl⟩ : syracuseStep 10533071 = 15799607) B15799607
theorem B1849679 : Blo 646304 1849679 := bstep (se 1 (by rfl) ⟨1387259, by rfl⟩ : syracuseStep 1849679 = 2774519) B2774519
theorem B2636383 : Blo 646304 2636383 := bstep (se 1 (by rfl) ⟨1977287, by rfl⟩ : syracuseStep 2636383 = 3954575) B3954575
theorem B1456847 : Blo 646304 1456847 := bstep (se 1 (by rfl) ⟨1092635, by rfl⟩ : syracuseStep 1456847 = 2185271) B2185271
theorem B9321439 : Blo 646304 9321439 := bstep (se 1 (by rfl) ⟨6991079, by rfl⟩ : syracuseStep 9321439 = 13982159) B13982159
theorem B4144297 : Blo 646304 4144297 := bstep (se 2 (by rfl) ⟨1554111, by rfl⟩ : syracuseStep 4144297 = 3108223) B3108223
theorem B1228031 : Blo 646304 1228031 := bstep (se 1 (by rfl) ⟨921023, by rfl⟩ : syracuseStep 1228031 = 1842047) B1842047
theorem B1850863 : Blo 646304 1850863 := bstep (se 1 (by rfl) ⟨1388147, by rfl⟩ : syracuseStep 1850863 = 2776295) B2776295
theorem B1457801 : Blo 646304 1457801 := bstep (se 2 (by rfl) ⟨546675, by rfl⟩ : syracuseStep 1457801 = 1093351) B1093351
theorem B12435281 : Blo 646304 12435281 := bstep (se 2 (by rfl) ⟨4663230, by rfl⟩ : syracuseStep 12435281 = 9326461) B9326461
theorem B10535021 : Blo 646304 10535021 := bstep (se 3 (by rfl) ⟨1975316, by rfl⟩ : syracuseStep 10535021 = 3950633) B3950633
theorem B1458359 : Blo 646304 1458359 := bstep (se 1 (by rfl) ⟨1093769, by rfl⟩ : syracuseStep 1458359 = 2187539) B2187539
theorem B5554433 : Blo 646304 5554433 := bstep (se 2 (by rfl) ⟨2082912, by rfl⟩ : syracuseStep 5554433 = 4165825) B4165825
theorem B1460159 : Blo 646304 1460159 := bstep (se 1 (by rfl) ⟨1095119, by rfl⟩ : syracuseStep 1460159 = 2190239) B2190239
theorem B1460321 : Blo 646304 1460321 := bstep (se 2 (by rfl) ⟨547620, by rfl⟩ : syracuseStep 1460321 = 1095241) B1095241
theorem B53135797 : Blo 646304 53135797 := bstep (se 5 (by rfl) ⟨2490740, by rfl⟩ : syracuseStep 53135797 = 4981481) B4981481
theorem B2181599 : Blo 646304 2181599 := bstep (se 1 (by rfl) ⟨1636199, by rfl⟩ : syracuseStep 2181599 = 3272399) B3272399
theorem B3788075 : Blo 646304 3788075 := bstep (se 1 (by rfl) ⟨2841056, by rfl⟩ : syracuseStep 3788075 = 5682113) B5682113
theorem B1036223 : Blo 646304 1036223 := bstep (se 1 (by rfl) ⟨777167, by rfl⟩ : syracuseStep 1036223 = 1554335) B1554335
theorem B43864163 : Blo 646304 43864163 := bstep (se 1 (by rfl) ⟨32898122, by rfl⟩ : syracuseStep 43864163 = 65796245) B65796245
theorem B1462463 : Blo 646304 1462463 := bstep (se 1 (by rfl) ⟨1096847, by rfl⟩ : syracuseStep 1462463 = 2193695) B2193695
theorem B971087 : Blo 646304 971087 := bstep (se 1 (by rfl) ⟨728315, by rfl⟩ : syracuseStep 971087 = 1456631) B1456631
theorem B971111 : Blo 646304 971111 := bstep (se 1 (by rfl) ⟨728333, by rfl⟩ : syracuseStep 971111 = 1456667) B1456667
theorem B1462751 : Blo 646304 1462751 := bstep (se 1 (by rfl) ⟨1097063, by rfl⟩ : syracuseStep 1462751 = 2194127) B2194127
theorem B2773511 : Blo 646304 2773511 := bstep (se 1 (by rfl) ⟨2080133, by rfl⟩ : syracuseStep 2773511 = 4160267) B4160267
theorem B6247165 : Blo 646304 6247165 := bstep (se 3 (by rfl) ⟨1171343, by rfl⟩ : syracuseStep 6247165 = 2342687) B2342687
theorem B1463111 : Blo 646304 1463111 := bstep (se 1 (by rfl) ⟨1097333, by rfl⟩ : syracuseStep 1463111 = 2194667) B2194667
theorem B2774483 : Blo 646304 2774483 := bstep (se 1 (by rfl) ⟨2080862, by rfl⟩ : syracuseStep 2774483 = 4161725) B4161725
theorem B4216411 : Blo 646304 4216411 := bstep (se 1 (by rfl) ⟨3162308, by rfl⟩ : syracuseStep 4216411 = 6324617) B6324617
theorem B972665 : Blo 646304 972665 := bstep (se 2 (by rfl) ⟨364749, by rfl⟩ : syracuseStep 972665 = 729499) B729499
theorem B5527439 : Blo 646304 5527439 := bstep (se 1 (by rfl) ⟨4145579, by rfl⟩ : syracuseStep 5527439 = 8291159) B8291159
theorem B8869985 : Blo 646304 8869985 := bstep (se 2 (by rfl) ⟨3326244, by rfl⟩ : syracuseStep 8869985 = 6652489) B6652489
theorem B973127 : Blo 646304 973127 := bstep (se 1 (by rfl) ⟨729845, by rfl⟩ : syracuseStep 973127 = 1459691) B1459691
theorem B2185811 : Blo 646304 2185811 := bstep (se 1 (by rfl) ⟨1639358, by rfl⟩ : syracuseStep 2185811 = 3278717) B3278717
theorem B646311 : Blo 646304 646311 := bstep (se 1 (by rfl) ⟨484733, by rfl⟩ : syracuseStep 646311 = 969467) B969467
theorem B7003367 : Blo 646304 7003367 := bstep (se 1 (by rfl) ⟨5252525, by rfl⟩ : syracuseStep 7003367 = 10505051) B10505051
theorem B1171135 : Blo 646304 1171135 := bstep (se 1 (by rfl) ⟨878351, by rfl⟩ : syracuseStep 1171135 = 1756703) B1756703
theorem B22798367 : Blo 646304 22798367 := bstep (se 1 (by rfl) ⟨17098775, by rfl⟩ : syracuseStep 22798367 = 34197551) B34197551
theorem B647931 : Blo 646304 647931 := bstep (se 1 (by rfl) ⟨485948, by rfl⟩ : syracuseStep 647931 = 971897) B971897
theorem B648063 : Blo 646304 648063 := bstep (se 1 (by rfl) ⟨486047, by rfl⟩ : syracuseStep 648063 = 972095) B972095
theorem B2188511 : Blo 646304 2188511 := bstep (se 1 (by rfl) ⟨1641383, by rfl⟩ : syracuseStep 2188511 = 3282767) B3282767
theorem B5924123 : Blo 646304 5924123 := bstep (se 1 (by rfl) ⟨4443092, by rfl⟩ : syracuseStep 5924123 = 8886185) B8886185
theorem B648551 : Blo 646304 648551 := bstep (se 1 (by rfl) ⟨486413, by rfl⟩ : syracuseStep 648551 = 972827) B972827
theorem B648671 : Blo 646304 648671 := bstep (se 1 (by rfl) ⟨486503, by rfl⟩ : syracuseStep 648671 = 973007) B973007
theorem B4154935 : Blo 646304 4154935 := bstep (se 1 (by rfl) ⟨3116201, by rfl⟩ : syracuseStep 4154935 = 6232403) B6232403
theorem B648795 : Blo 646304 648795 := bstep (se 1 (by rfl) ⟨486596, by rfl⟩ : syracuseStep 648795 = 973193) B973193
theorem B648943 : Blo 646304 648943 := bstep (se 1 (by rfl) ⟨486707, by rfl⟩ : syracuseStep 648943 = 973415) B973415
theorem B649423 : Blo 646304 649423 := bstep (se 1 (by rfl) ⟨487067, by rfl⟩ : syracuseStep 649423 = 974135) B974135
theorem B649711 : Blo 646304 649711 := bstep (se 1 (by rfl) ⟨487283, by rfl⟩ : syracuseStep 649711 = 974567) B974567
theorem B650015 : Blo 646304 650015 := bstep (se 1 (by rfl) ⟨487511, by rfl⟩ : syracuseStep 650015 = 975023) B975023
theorem B650047 : Blo 646304 650047 := bstep (se 1 (by rfl) ⟨487535, by rfl⟩ : syracuseStep 650047 = 975071) B975071
theorem B1601471 : Blo 646304 1601471 := bstep (se 1 (by rfl) ⟨1201103, by rfl⟩ : syracuseStep 1601471 = 2402207) B2402207
theorem B5534203 : Blo 646304 5534203 := bstep (se 1 (by rfl) ⟨4150652, by rfl⟩ : syracuseStep 5534203 = 8301305) B8301305
theorem B1995337 : Blo 646304 1995337 := bstep (se 2 (by rfl) ⟨748251, by rfl⟩ : syracuseStep 1995337 = 1496503) B1496503
theorem B9992159 : Blo 646304 9992159 := bstep (se 1 (by rfl) ⟨7494119, by rfl⟩ : syracuseStep 9992159 = 14988239) B14988239
theorem B1636321 : Blo 646304 1636321 := bstep (se 2 (by rfl) ⟨613620, by rfl⟩ : syracuseStep 1636321 = 1227241) B1227241
theorem B2193533 : Blo 646304 2193533 := bstep (se 3 (by rfl) ⟨411287, by rfl⟩ : syracuseStep 2193533 = 822575) B822575
theorem B3275801 : Blo 646304 3275801 := bstep (se 2 (by rfl) ⟨1228425, by rfl⟩ : syracuseStep 3275801 = 2456851) B2456851
theorem B2194559 : Blo 646304 2194559 := bstep (se 1 (by rfl) ⟨1645919, by rfl⟩ : syracuseStep 2194559 = 3291839) B3291839
theorem B5930621 : Blo 646304 5930621 := bstep (se 3 (by rfl) ⟨1111991, by rfl⟩ : syracuseStep 5930621 = 2223983) B2223983
theorem B1638265 : Blo 646304 1638265 := bstep (se 2 (by rfl) ⟨614349, by rfl⟩ : syracuseStep 1638265 = 1228699) B1228699
theorem B1638377 : Blo 646304 1638377 := bstep (se 2 (by rfl) ⟨614391, by rfl⟩ : syracuseStep 1638377 = 1228783) B1228783
theorem B3702955 : Blo 646304 3702955 := bstep (se 1 (by rfl) ⟨2777216, by rfl⟩ : syracuseStep 3702955 = 5554433) B5554433
theorem B1639835 : Blo 646304 1639835 := bstep (se 1 (by rfl) ⟨1229876, by rfl⟩ : syracuseStep 1639835 = 2459753) B2459753
theorem B3278879 : Blo 646304 3278879 := bstep (se 1 (by rfl) ⟨2459159, by rfl⟩ : syracuseStep 3278879 = 4918319) B4918319
theorem B5539913 : Blo 646304 5539913 := bstep (se 2 (by rfl) ⟨2077467, by rfl⟩ : syracuseStep 5539913 = 4154935) B4154935
theorem B2525383 : Blo 646304 2525383 := bstep (se 1 (by rfl) ⟨1894037, by rfl⟩ : syracuseStep 2525383 = 3788075) B3788075
theorem B690815 : Blo 646304 690815 := bstep (se 1 (by rfl) ⟨518111, by rfl⟩ : syracuseStep 690815 = 1036223) B1036223
theorem B70847729 : Blo 646304 70847729 := bstep (se 2 (by rfl) ⟨26567898, by rfl⟩ : syracuseStep 70847729 = 53135797) B53135797
theorem B6229943 : Blo 646304 6229943 := bstep (se 1 (by rfl) ⟨4672457, by rfl⟩ : syracuseStep 6229943 = 9344915) B9344915
theorem B56988845 : Blo 646304 56988845 := bstep (se 3 (by rfl) ⟨10685408, by rfl⟩ : syracuseStep 56988845 = 21370817) B21370817
theorem B7378937 : Blo 646304 7378937 := bstep (se 2 (by rfl) ⟨2767101, by rfl⟩ : syracuseStep 7378937 = 5534203) B5534203
theorem B2660449 : Blo 646304 2660449 := bstep (se 2 (by rfl) ⟨997668, by rfl⟩ : syracuseStep 2660449 = 1995337) B1995337
theorem B8329553 : Blo 646304 8329553 := bstep (se 2 (by rfl) ⟨3123582, by rfl⟩ : syracuseStep 8329553 = 6247165) B6247165
theorem B1841545 : Blo 646304 1841545 := bstep (se 2 (by rfl) ⟨690579, by rfl⟩ : syracuseStep 1841545 = 1381159) B1381159
theorem B727663 : Blo 646304 727663 := bstep (se 1 (by rfl) ⟨545747, by rfl⟩ : syracuseStep 727663 = 1091495) B1091495
theorem B37985273 : Blo 646304 37985273 := bstep (se 2 (by rfl) ⟨14244477, by rfl⟩ : syracuseStep 37985273 = 28488955) B28488955
theorem B3284873 : Blo 646304 3284873 := bstep (se 2 (by rfl) ⟨1231827, by rfl⟩ : syracuseStep 3284873 = 2463655) B2463655
theorem B1843231 : Blo 646304 1843231 := bstep (se 1 (by rfl) ⟨1382423, by rfl⟩ : syracuseStep 1843231 = 2764847) B2764847
theorem B3515177 : Blo 646304 3515177 := bstep (se 2 (by rfl) ⟨1318191, by rfl⟩ : syracuseStep 3515177 = 2636383) B2636383
theorem B12428585 : Blo 646304 12428585 := bstep (se 2 (by rfl) ⟨4660719, by rfl⟩ : syracuseStep 12428585 = 9321439) B9321439
theorem B6661439 : Blo 646304 6661439 := bstep (se 1 (by rfl) ⟨4996079, by rfl⟩ : syracuseStep 6661439 = 9992159) B9992159
theorem B7022047 : Blo 646304 7022047 := bstep (se 1 (by rfl) ⟨5266535, by rfl⟩ : syracuseStep 7022047 = 10533071) B10533071
theorem B2467817 : Blo 646304 2467817 := bstep (se 2 (by rfl) ⟨925431, by rfl⟩ : syracuseStep 2467817 = 1850863) B1850863
theorem B11806793 : Blo 646304 11806793 := bstep (se 2 (by rfl) ⟨4427547, by rfl⟩ : syracuseStep 11806793 = 8855095) B8855095
theorem B7088573 : Blo 646304 7088573 := bstep (se 3 (by rfl) ⟨1329107, by rfl⟩ : syracuseStep 7088573 = 2658215) B2658215
theorem B4270589 : Blo 646304 4270589 := bstep (se 3 (by rfl) ⟨800735, by rfl⟩ : syracuseStep 4270589 = 1601471) B1601471
theorem B1092251 : Blo 646304 1092251 := bstep (se 1 (by rfl) ⟨819188, by rfl⟩ : syracuseStep 1092251 = 1638377) B1638377
theorem B7023347 : Blo 646304 7023347 := bstep (se 1 (by rfl) ⟨5267510, by rfl⟩ : syracuseStep 7023347 = 10535021) B10535021
theorem B6991771 : Blo 646304 6991771 := bstep (se 1 (by rfl) ⟨5243828, by rfl⟩ : syracuseStep 6991771 = 10487657) B10487657
theorem B1454399 : Blo 646304 1454399 := bstep (se 1 (by rfl) ⟨1090799, by rfl⟩ : syracuseStep 1454399 = 2181599) B2181599
theorem B1454633 : Blo 646304 1454633 := bstep (se 2 (by rfl) ⟨545487, by rfl⟩ : syracuseStep 1454633 = 1090975) B1090975
theorem B1094377 : Blo 646304 1094377 := bstep (se 2 (by rfl) ⟨410391, by rfl⟩ : syracuseStep 1094377 = 820783) B820783
theorem B3683069 : Blo 646304 3683069 := bstep (se 3 (by rfl) ⟨690575, by rfl⟩ : syracuseStep 3683069 = 1381151) B1381151
theorem B2077787 : Blo 646304 2077787 := bstep (se 1 (by rfl) ⟨1558340, by rfl⟩ : syracuseStep 2077787 = 3116681) B3116681
theorem B29242775 : Blo 646304 29242775 := bstep (se 1 (by rfl) ⟨21932081, by rfl⟩ : syracuseStep 29242775 = 43864163) B43864163
theorem B8304281 : Blo 646304 8304281 := bstep (se 2 (by rfl) ⟨3114105, by rfl⟩ : syracuseStep 8304281 = 6228211) B6228211
theorem B1849007 : Blo 646304 1849007 := bstep (se 1 (by rfl) ⟨1386755, by rfl⟩ : syracuseStep 1849007 = 2773511) B2773511
theorem B1095727 : Blo 646304 1095727 := bstep (se 1 (by rfl) ⟨821795, by rfl⟩ : syracuseStep 1095727 = 1643591) B1643591
theorem B1849655 : Blo 646304 1849655 := bstep (se 1 (by rfl) ⟨1387241, by rfl⟩ : syracuseStep 1849655 = 2774483) B2774483
theorem B3684959 : Blo 646304 3684959 := bstep (se 1 (by rfl) ⟨2763719, by rfl⟩ : syracuseStep 3684959 = 5527439) B5527439
theorem B5913323 : Blo 646304 5913323 := bstep (se 1 (by rfl) ⟨4434992, by rfl⟩ : syracuseStep 5913323 = 8869985) B8869985
theorem B1456937 : Blo 646304 1456937 := bstep (se 2 (by rfl) ⟨546351, by rfl⟩ : syracuseStep 1456937 = 1092703) B1092703
theorem B3947453 : Blo 646304 3947453 := bstep (se 3 (by rfl) ⟨740147, by rfl⟩ : syracuseStep 3947453 = 1480295) B1480295
theorem B1457207 : Blo 646304 1457207 := bstep (se 1 (by rfl) ⟨1092905, by rfl⟩ : syracuseStep 1457207 = 2185811) B2185811
theorem B12434735 : Blo 646304 12434735 := bstep (se 1 (by rfl) ⟨9326051, by rfl⟩ : syracuseStep 12434735 = 18652103) B18652103
theorem B4668911 : Blo 646304 4668911 := bstep (se 1 (by rfl) ⟨3501683, by rfl⟩ : syracuseStep 4668911 = 7003367) B7003367
theorem B1459007 : Blo 646304 1459007 := bstep (se 1 (by rfl) ⟨1094255, by rfl⟩ : syracuseStep 1459007 = 2188511) B2188511
theorem B3949415 : Blo 646304 3949415 := bstep (se 1 (by rfl) ⟨2962061, by rfl⟩ : syracuseStep 3949415 = 5924123) B5924123
theorem B10536443 : Blo 646304 10536443 := bstep (se 1 (by rfl) ⟨7902332, by rfl⟩ : syracuseStep 10536443 = 15804665) B15804665
theorem B5621881 : Blo 646304 5621881 := bstep (se 2 (by rfl) ⟨2108205, by rfl⟩ : syracuseStep 5621881 = 4216411) B4216411
theorem B2181761 : Blo 646304 2181761 := bstep (se 2 (by rfl) ⟨818160, by rfl⟩ : syracuseStep 2181761 = 1636321) B1636321
theorem B969503 : Blo 646304 969503 := bstep (se 1 (by rfl) ⟨727127, by rfl⟩ : syracuseStep 969503 = 1454255) B1454255
theorem B969935 : Blo 646304 969935 := bstep (se 1 (by rfl) ⟨727451, by rfl⟩ : syracuseStep 969935 = 1454903) B1454903
theorem B5623019 : Blo 646304 5623019 := bstep (se 1 (by rfl) ⟨4217264, by rfl⟩ : syracuseStep 5623019 = 8434529) B8434529
theorem B970271 : Blo 646304 970271 := bstep (se 1 (by rfl) ⟨727703, by rfl⟩ : syracuseStep 970271 = 1455407) B1455407
theorem B1462355 : Blo 646304 1462355 := bstep (se 1 (by rfl) ⟨1096766, by rfl⟩ : syracuseStep 1462355 = 2193533) B2193533
theorem B1233119 : Blo 646304 1233119 := bstep (se 1 (by rfl) ⟨924839, by rfl⟩ : syracuseStep 1233119 = 1849679) B1849679
theorem B5525729 : Blo 646304 5525729 := bstep (se 2 (by rfl) ⟨2072148, by rfl⟩ : syracuseStep 5525729 = 4144297) B4144297
theorem B971231 : Blo 646304 971231 := bstep (se 1 (by rfl) ⟨728423, by rfl⟩ : syracuseStep 971231 = 1456847) B1456847
theorem B2183867 : Blo 646304 2183867 := bstep (se 1 (by rfl) ⟨1637900, by rfl⟩ : syracuseStep 2183867 = 3275801) B3275801
theorem B1463039 : Blo 646304 1463039 := bstep (se 1 (by rfl) ⟨1097279, by rfl⟩ : syracuseStep 1463039 = 2194559) B2194559
theorem B1561513 : Blo 646304 1561513 := bstep (se 2 (by rfl) ⟨585567, by rfl⟩ : syracuseStep 1561513 = 1171135) B1171135
theorem B3953747 : Blo 646304 3953747 := bstep (se 1 (by rfl) ⟨2965310, by rfl⟩ : syracuseStep 3953747 = 5930621) B5930621
theorem B971867 : Blo 646304 971867 := bstep (se 1 (by rfl) ⟨728900, by rfl⟩ : syracuseStep 971867 = 1457801) B1457801
theorem B2184353 : Blo 646304 2184353 := bstep (se 2 (by rfl) ⟨819132, by rfl⟩ : syracuseStep 2184353 = 1638265) B1638265
theorem B972239 : Blo 646304 972239 := bstep (se 1 (by rfl) ⟨729179, by rfl⟩ : syracuseStep 972239 = 1458359) B1458359
theorem B4151063 : Blo 646304 4151063 := bstep (se 1 (by rfl) ⟨3113297, by rfl⟩ : syracuseStep 4151063 = 6226595) B6226595
theorem B3693023 : Blo 646304 3693023 := bstep (se 1 (by rfl) ⟨2769767, by rfl⟩ : syracuseStep 3693023 = 5539535) B5539535
theorem B973439 : Blo 646304 973439 := bstep (se 1 (by rfl) ⟨730079, by rfl⟩ : syracuseStep 973439 = 1460159) B1460159
theorem B973481 : Blo 646304 973481 := bstep (se 2 (by rfl) ⟨365055, by rfl⟩ : syracuseStep 973481 = 730111) B730111
theorem B973547 : Blo 646304 973547 := bstep (se 1 (by rfl) ⟨730160, by rfl⟩ : syracuseStep 973547 = 1460321) B1460321
theorem B4153319 : Blo 646304 4153319 := bstep (se 1 (by rfl) ⟨3114989, by rfl⟩ : syracuseStep 4153319 = 6229979) B6229979
theorem B974975 : Blo 646304 974975 := bstep (se 1 (by rfl) ⟨731231, by rfl⟩ : syracuseStep 974975 = 1462463) B1462463
theorem B2187431 : Blo 646304 2187431 := bstep (se 1 (by rfl) ⟨1640573, by rfl⟩ : syracuseStep 2187431 = 3281147) B3281147
theorem B647391 : Blo 646304 647391 := bstep (se 1 (by rfl) ⟨485543, by rfl⟩ : syracuseStep 647391 = 971087) B971087
theorem B647407 : Blo 646304 647407 := bstep (se 1 (by rfl) ⟨485555, by rfl⟩ : syracuseStep 647407 = 971111) B971111
theorem B975167 : Blo 646304 975167 := bstep (se 1 (by rfl) ⟨731375, by rfl⟩ : syracuseStep 975167 = 1462751) B1462751
theorem B975407 : Blo 646304 975407 := bstep (se 1 (by rfl) ⟨731555, by rfl⟩ : syracuseStep 975407 = 1463111) B1463111
theorem B4219751 : Blo 646304 4219751 := bstep (se 1 (by rfl) ⟨3164813, by rfl⟩ : syracuseStep 4219751 = 6329627) B6329627
theorem B648443 : Blo 646304 648443 := bstep (se 1 (by rfl) ⟨486332, by rfl⟩ : syracuseStep 648443 = 972665) B972665
theorem B2188727 : Blo 646304 2188727 := bstep (se 1 (by rfl) ⟨1641545, by rfl⟩ : syracuseStep 2188727 = 3283091) B3283091
theorem B648751 : Blo 646304 648751 := bstep (se 1 (by rfl) ⟨486563, by rfl⟩ : syracuseStep 648751 = 973127) B973127
theorem B2189807 : Blo 646304 2189807 := bstep (se 1 (by rfl) ⟨1642355, by rfl⟩ : syracuseStep 2189807 = 3284711) B3284711
theorem B15198911 : Blo 646304 15198911 := bstep (se 1 (by rfl) ⟨11399183, by rfl⟩ : syracuseStep 15198911 = 22798367) B22798367
theorem B11070593 : Blo 646304 11070593 := bstep (se 2 (by rfl) ⟨4151472, by rfl⟩ : syracuseStep 11070593 = 8302945) B8302945
theorem B2191319 : Blo 646304 2191319 := bstep (se 1 (by rfl) ⟨1643489, by rfl⟩ : syracuseStep 2191319 = 3286979) B3286979
theorem B2192723 : Blo 646304 2192723 := bstep (se 1 (by rfl) ⟨1644542, by rfl⟩ : syracuseStep 2192723 = 3289085) B3289085
theorem B751135 : Blo 646304 751135 := bstep (se 1 (by rfl) ⟨563351, by rfl⟩ : syracuseStep 751135 = 1126703) B1126703
theorem B3733073 : Blo 646304 3733073 := bstep (se 2 (by rfl) ⟨1399902, by rfl⟩ : syracuseStep 3733073 = 2799805) B2799805
theorem B2193479 : Blo 646304 2193479 := bstep (se 1 (by rfl) ⟨1645109, by rfl⟩ : syracuseStep 2193479 = 3290219) B3290219
theorem B39942497 : Blo 646304 39942497 := bstep (se 2 (by rfl) ⟨14978436, by rfl⟩ : syracuseStep 39942497 = 29956873) B29956873
theorem B818687 : Blo 646304 818687 := bstep (se 1 (by rfl) ⟨614015, by rfl⟩ : syracuseStep 818687 = 1228031) B1228031
theorem B8290187 : Blo 646304 8290187 := bstep (se 1 (by rfl) ⟨6217640, by rfl⟩ : syracuseStep 8290187 = 12435281) B12435281
theorem B2457641 : Blo 646304 2457641 := bstep (se 2 (by rfl) ⟨921615, by rfl⟩ : syracuseStep 2457641 = 1843231) B1843231
theorem B822079 : Blo 646304 822079 := bstep (se 1 (by rfl) ⟨616559, by rfl⟩ : syracuseStep 822079 = 1233119) B1233119
theorem B4919291 : Blo 646304 4919291 := bstep (se 1 (by rfl) ⟨3689468, by rfl⟩ : syracuseStep 4919291 = 7378937) B7378937
theorem B2462015 : Blo 646304 2462015 := bstep (se 1 (by rfl) ⟨1846511, by rfl⟩ : syracuseStep 2462015 = 3693023) B3693023
theorem B1645211 : Blo 646304 1645211 := bstep (se 1 (by rfl) ⟨1233908, by rfl⟩ : syracuseStep 1645211 = 2467817) B2467817
theorem B7871195 : Blo 646304 7871195 := bstep (se 1 (by rfl) ⟨5903396, by rfl⟩ : syracuseStep 7871195 = 11806793) B11806793
theorem B4725715 : Blo 646304 4725715 := bstep (se 1 (by rfl) ⟨3544286, by rfl⟩ : syracuseStep 4725715 = 7088573) B7088573
theorem B1842173 : Blo 646304 1842173 := bstep (se 3 (by rfl) ⟨345407, by rfl⟩ : syracuseStep 1842173 = 690815) B690815
theorem B728167 : Blo 646304 728167 := bstep (se 1 (by rfl) ⟨546125, by rfl⟩ : syracuseStep 728167 = 1092251) B1092251
theorem B10132607 : Blo 646304 10132607 := bstep (se 1 (by rfl) ⟨7599455, by rfl⟩ : syracuseStep 10132607 = 15198911) B15198911
theorem B7380395 : Blo 646304 7380395 := bstep (se 1 (by rfl) ⟨5535296, by rfl⟩ : syracuseStep 7380395 = 11070593) B11070593
theorem B3547265 : Blo 646304 3547265 := bstep (se 2 (by rfl) ⟨1330224, by rfl⟩ : syracuseStep 3547265 = 2660449) B2660449
theorem B1385191 : Blo 646304 1385191 := bstep (se 1 (by rfl) ⟨1038893, by rfl⟩ : syracuseStep 1385191 = 2077787) B2077787
theorem B3942215 : Blo 646304 3942215 := bstep (se 1 (by rfl) ⟨2956661, by rfl⟩ : syracuseStep 3942215 = 5913323) B5913323
theorem B2631635 : Blo 646304 2631635 := bstep (se 1 (by rfl) ⟨1973726, by rfl⟩ : syracuseStep 2631635 = 3947453) B3947453
theorem B2632943 : Blo 646304 2632943 := bstep (se 1 (by rfl) ⟨1974707, by rfl⟩ : syracuseStep 2632943 = 3949415) B3949415
theorem B1093223 : Blo 646304 1093223 := bstep (se 1 (by rfl) ⟨819917, by rfl⟩ : syracuseStep 1093223 = 1639835) B1639835
theorem B7024295 : Blo 646304 7024295 := bstep (se 1 (by rfl) ⟨5268221, by rfl⟩ : syracuseStep 7024295 = 10536443) B10536443
theorem B1454507 : Blo 646304 1454507 := bstep (se 1 (by rfl) ⟨1090880, by rfl⟩ : syracuseStep 1454507 = 2181761) B2181761
theorem B3748679 : Blo 646304 3748679 := bstep (se 1 (by rfl) ⟨2811509, by rfl⟩ : syracuseStep 3748679 = 5623019) B5623019
theorem B47231819 : Blo 646304 47231819 := bstep (se 1 (by rfl) ⟨35423864, by rfl⟩ : syracuseStep 47231819 = 70847729) B70847729
theorem B3683819 : Blo 646304 3683819 := bstep (se 1 (by rfl) ⟨2762864, by rfl⟩ : syracuseStep 3683819 = 5525729) B5525729
theorem B1455911 : Blo 646304 1455911 := bstep (se 1 (by rfl) ⟨1091933, by rfl⟩ : syracuseStep 1455911 = 2183867) B2183867
theorem B2635831 : Blo 646304 2635831 := bstep (se 1 (by rfl) ⟨1976873, by rfl⟩ : syracuseStep 2635831 = 3953747) B3953747
theorem B1456235 : Blo 646304 1456235 := bstep (se 1 (by rfl) ⟨1092176, by rfl⟩ : syracuseStep 1456235 = 2184353) B2184353
theorem B37992563 : Blo 646304 37992563 := bstep (se 1 (by rfl) ⟨28494422, by rfl⟩ : syracuseStep 37992563 = 56988845) B56988845
theorem B2767375 : Blo 646304 2767375 := bstep (se 1 (by rfl) ⟨2075531, by rfl⟩ : syracuseStep 2767375 = 4151063) B4151063
theorem B5553035 : Blo 646304 5553035 := bstep (se 1 (by rfl) ⟨4164776, by rfl⟩ : syracuseStep 5553035 = 8329553) B8329553
theorem B180042709 : Blo 646304 180042709 := bstep (se 7 (by rfl) ⟨2109875, by rfl⟩ : syracuseStep 180042709 = 4219751) B4219751
theorem B9322361 : Blo 646304 9322361 := bstep (se 2 (by rfl) ⟨3495885, by rfl⟩ : syracuseStep 9322361 = 6991771) B6991771
theorem B2768879 : Blo 646304 2768879 := bstep (se 1 (by rfl) ⟨2076659, by rfl⟩ : syracuseStep 2768879 = 4153319) B4153319
theorem B1458287 : Blo 646304 1458287 := bstep (se 1 (by rfl) ⟨1093715, by rfl⟩ : syracuseStep 1458287 = 2187431) B2187431
theorem B2343451 : Blo 646304 2343451 := bstep (se 1 (by rfl) ⟨1757588, by rfl⟩ : syracuseStep 2343451 = 3515177) B3515177
theorem B4932413 : Blo 646304 4932413 := bstep (se 3 (by rfl) ⟨924827, by rfl⟩ : syracuseStep 4932413 = 1849655) B1849655
theorem B4440959 : Blo 646304 4440959 := bstep (se 1 (by rfl) ⟨3330719, by rfl⟩ : syracuseStep 4440959 = 6661439) B6661439
theorem B106513325 : Blo 646304 106513325 := bstep (se 3 (by rfl) ⟨19971248, by rfl⟩ : syracuseStep 106513325 = 39942497) B39942497
theorem B1459151 : Blo 646304 1459151 := bstep (se 1 (by rfl) ⟨1094363, by rfl⟩ : syracuseStep 1459151 = 2188727) B2188727
theorem B1459169 : Blo 646304 1459169 := bstep (se 2 (by rfl) ⟨547188, by rfl⟩ : syracuseStep 1459169 = 1094377) B1094377
theorem B2082017 : Blo 646304 2082017 := bstep (se 2 (by rfl) ⟨780756, by rfl⟩ : syracuseStep 2082017 = 1561513) B1561513
theorem B1459871 : Blo 646304 1459871 := bstep (se 1 (by rfl) ⟨1094903, by rfl⟩ : syracuseStep 1459871 = 2189807) B2189807
theorem B1001513 : Blo 646304 1001513 := bstep (se 2 (by rfl) ⟨375567, by rfl⟩ : syracuseStep 1001513 = 751135) B751135
theorem B1460879 : Blo 646304 1460879 := bstep (se 1 (by rfl) ⟨1095659, by rfl⟩ : syracuseStep 1460879 = 2191319) B2191319
theorem B1460969 : Blo 646304 1460969 := bstep (se 2 (by rfl) ⟨547863, by rfl⟩ : syracuseStep 1460969 = 1095727) B1095727
theorem B969599 : Blo 646304 969599 := bstep (se 1 (by rfl) ⟨727199, by rfl⟩ : syracuseStep 969599 = 1454399) B1454399
theorem B969755 : Blo 646304 969755 := bstep (se 1 (by rfl) ⟨727316, by rfl⟩ : syracuseStep 969755 = 1454633) B1454633
theorem B970217 : Blo 646304 970217 := bstep (se 2 (by rfl) ⟨363831, by rfl⟩ : syracuseStep 970217 = 727663) B727663
theorem B1461815 : Blo 646304 1461815 := bstep (se 1 (by rfl) ⟨1096361, by rfl⟩ : syracuseStep 1461815 = 2192723) B2192723
theorem B1232671 : Blo 646304 1232671 := bstep (se 1 (by rfl) ⟨924503, by rfl⟩ : syracuseStep 1232671 = 1849007) B1849007
theorem B2183165 : Blo 646304 2183165 := bstep (se 3 (by rfl) ⟨409343, by rfl⟩ : syracuseStep 2183165 = 818687) B818687
theorem B1462319 : Blo 646304 1462319 := bstep (se 1 (by rfl) ⟨1096739, by rfl⟩ : syracuseStep 1462319 = 2193479) B2193479
theorem B971291 : Blo 646304 971291 := bstep (se 1 (by rfl) ⟨728468, by rfl⟩ : syracuseStep 971291 = 1456937) B1456937
theorem B971471 : Blo 646304 971471 := bstep (se 1 (by rfl) ⟨728603, by rfl⟩ : syracuseStep 971471 = 1457207) B1457207
theorem B5526791 : Blo 646304 5526791 := bstep (se 1 (by rfl) ⟨4145093, by rfl⟩ : syracuseStep 5526791 = 8290187) B8290187
theorem B4937273 : Blo 646304 4937273 := bstep (se 2 (by rfl) ⟨1851477, by rfl⟩ : syracuseStep 4937273 = 3702955) B3702955
theorem B972671 : Blo 646304 972671 := bstep (se 1 (by rfl) ⟨729503, by rfl⟩ : syracuseStep 972671 = 1459007) B1459007
theorem B2185919 : Blo 646304 2185919 := bstep (se 1 (by rfl) ⟨1639439, by rfl⟩ : syracuseStep 2185919 = 3278879) B3278879
theorem B3693275 : Blo 646304 3693275 := bstep (se 1 (by rfl) ⟨2769956, by rfl⟩ : syracuseStep 3693275 = 5539913) B5539913
theorem B646335 : Blo 646304 646335 := bstep (se 1 (by rfl) ⟨484751, by rfl⟩ : syracuseStep 646335 = 969503) B969503
theorem B9362729 : Blo 646304 9362729 := bstep (se 2 (by rfl) ⟨3511023, by rfl⟩ : syracuseStep 9362729 = 7022047) B7022047
theorem B646623 : Blo 646304 646623 := bstep (se 1 (by rfl) ⟨484967, by rfl⟩ : syracuseStep 646623 = 969935) B969935
theorem B646847 : Blo 646304 646847 := bstep (se 1 (by rfl) ⟨485135, by rfl⟩ : syracuseStep 646847 = 970271) B970271
theorem B4153295 : Blo 646304 4153295 := bstep (se 1 (by rfl) ⟨3114971, by rfl⟩ : syracuseStep 4153295 = 6229943) B6229943
theorem B974903 : Blo 646304 974903 := bstep (se 1 (by rfl) ⟨731177, by rfl⟩ : syracuseStep 974903 = 1462355) B1462355
theorem B7495841 : Blo 646304 7495841 := bstep (se 2 (by rfl) ⟨2810940, by rfl⟩ : syracuseStep 7495841 = 5621881) B5621881
theorem B3367177 : Blo 646304 3367177 := bstep (se 2 (by rfl) ⟨1262691, by rfl⟩ : syracuseStep 3367177 = 2525383) B2525383
theorem B647487 : Blo 646304 647487 := bstep (se 1 (by rfl) ⟨485615, by rfl⟩ : syracuseStep 647487 = 971231) B971231
theorem B975359 : Blo 646304 975359 := bstep (se 1 (by rfl) ⟨731519, by rfl⟩ : syracuseStep 975359 = 1463039) B1463039
theorem B647911 : Blo 646304 647911 := bstep (se 1 (by rfl) ⟨485933, by rfl⟩ : syracuseStep 647911 = 971867) B971867
theorem B648159 : Blo 646304 648159 := bstep (se 1 (by rfl) ⟨486119, by rfl⟩ : syracuseStep 648159 = 972239) B972239
theorem B648959 : Blo 646304 648959 := bstep (se 1 (by rfl) ⟨486719, by rfl⟩ : syracuseStep 648959 = 973439) B973439
theorem B648987 : Blo 646304 648987 := bstep (se 1 (by rfl) ⟨486740, by rfl⟩ : syracuseStep 648987 = 973481) B973481
theorem B649031 : Blo 646304 649031 := bstep (se 1 (by rfl) ⟨486773, by rfl⟩ : syracuseStep 649031 = 973547) B973547
theorem B25323515 : Blo 646304 25323515 := bstep (se 1 (by rfl) ⟨18992636, by rfl⟩ : syracuseStep 25323515 = 37985273) B37985273
theorem B2189915 : Blo 646304 2189915 := bstep (se 1 (by rfl) ⟨1642436, by rfl⟩ : syracuseStep 2189915 = 3284873) B3284873
theorem B649983 : Blo 646304 649983 := bstep (se 1 (by rfl) ⟨487487, by rfl⟩ : syracuseStep 649983 = 974975) B974975
theorem B650111 : Blo 646304 650111 := bstep (se 1 (by rfl) ⟨487583, by rfl⟩ : syracuseStep 650111 = 975167) B975167
theorem B650271 : Blo 646304 650271 := bstep (se 1 (by rfl) ⟨487703, by rfl⟩ : syracuseStep 650271 = 975407) B975407
theorem B8285723 : Blo 646304 8285723 := bstep (se 1 (by rfl) ⟨6214292, by rfl⟩ : syracuseStep 8285723 = 12428585) B12428585
theorem B2847059 : Blo 646304 2847059 := bstep (se 1 (by rfl) ⟨2135294, by rfl⟩ : syracuseStep 2847059 = 4270589) B4270589
theorem B4682231 : Blo 646304 4682231 := bstep (se 1 (by rfl) ⟨3511673, by rfl⟩ : syracuseStep 4682231 = 7023347) B7023347
theorem B2455379 : Blo 646304 2455379 := bstep (se 1 (by rfl) ⟨1841534, by rfl⟩ : syracuseStep 2455379 = 3683069) B3683069
theorem B2455393 : Blo 646304 2455393 := bstep (se 2 (by rfl) ⟨920772, by rfl⟩ : syracuseStep 2455393 = 1841545) B1841545
theorem B19495183 : Blo 646304 19495183 := bstep (se 1 (by rfl) ⟨14621387, by rfl⟩ : syracuseStep 19495183 = 29242775) B29242775
theorem B2488715 : Blo 646304 2488715 := bstep (se 1 (by rfl) ⟨1866536, by rfl⟩ : syracuseStep 2488715 = 3733073) B3733073
theorem B5536187 : Blo 646304 5536187 := bstep (se 1 (by rfl) ⟨4152140, by rfl⟩ : syracuseStep 5536187 = 8304281) B8304281
theorem B2456639 : Blo 646304 2456639 := bstep (se 1 (by rfl) ⟨1842479, by rfl⟩ : syracuseStep 2456639 = 3684959) B3684959
theorem B8289823 : Blo 646304 8289823 := bstep (se 1 (by rfl) ⟨6217367, by rfl⟩ : syracuseStep 8289823 = 12434735) B12434735
theorem B3112607 : Blo 646304 3112607 := bstep (se 1 (by rfl) ⟨2334455, by rfl⟩ : syracuseStep 3112607 = 4668911) B4668911
theorem B1638427 : Blo 646304 1638427 := bstep (se 1 (by rfl) ⟨1228820, by rfl⟩ : syracuseStep 1638427 = 2457641) B2457641
theorem B71008883 : Blo 646304 71008883 := bstep (se 1 (by rfl) ⟨53256662, by rfl⟩ : syracuseStep 71008883 = 106513325) B106513325
theorem B17958277 : Blo 646304 17958277 := bstep (se 4 (by rfl) ⟨1683588, by rfl⟩ : syracuseStep 17958277 = 3367177) B3367177
theorem B3279527 : Blo 646304 3279527 := bstep (se 1 (by rfl) ⟨2459645, by rfl⟩ : syracuseStep 3279527 = 4919291) B4919291
theorem B1641343 : Blo 646304 1641343 := bstep (se 1 (by rfl) ⟨1231007, by rfl⟩ : syracuseStep 1641343 = 2462015) B2462015
theorem B5247463 : Blo 646304 5247463 := bstep (se 1 (by rfl) ⟨3935597, by rfl⟩ : syracuseStep 5247463 = 7871195) B7871195
theorem B2462183 : Blo 646304 2462183 := bstep (se 1 (by rfl) ⟨1846637, by rfl⟩ : syracuseStep 2462183 = 3693275) B3693275
theorem B6755071 : Blo 646304 6755071 := bstep (se 1 (by rfl) ⟨5066303, by rfl⟩ : syracuseStep 6755071 = 10132607) B10132607
theorem B4920263 : Blo 646304 4920263 := bstep (se 1 (by rfl) ⟨3690197, by rfl⟩ : syracuseStep 4920263 = 7380395) B7380395
theorem B1643561 : Blo 646304 1643561 := bstep (se 2 (by rfl) ⟨616335, by rfl⟩ : syracuseStep 1643561 = 1232671) B1232671
theorem B2628143 : Blo 646304 2628143 := bstep (se 1 (by rfl) ⟨1971107, by rfl⟩ : syracuseStep 2628143 = 3942215) B3942215
theorem B16882343 : Blo 646304 16882343 := bstep (se 1 (by rfl) ⟨12661757, by rfl⟩ : syracuseStep 16882343 = 25323515) B25323515
theorem B728815 : Blo 646304 728815 := bstep (se 1 (by rfl) ⟨546611, by rfl⟩ : syracuseStep 728815 = 1093223) B1093223
theorem B3514441 : Blo 646304 3514441 := bstep (se 2 (by rfl) ⟨1317915, by rfl⟩ : syracuseStep 3514441 = 2635831) B2635831
theorem B3121487 : Blo 646304 3121487 := bstep (se 1 (by rfl) ⟨2341115, by rfl⟩ : syracuseStep 3121487 = 4682231) B4682231
theorem B25993577 : Blo 646304 25993577 := bstep (se 2 (by rfl) ⟨9747591, by rfl⟩ : syracuseStep 25993577 = 19495183) B19495183
theorem B2499119 : Blo 646304 2499119 := bstep (se 1 (by rfl) ⟨1874339, by rfl⟩ : syracuseStep 2499119 = 3748679) B3748679
theorem B7021181 : Blo 646304 7021181 := bstep (se 3 (by rfl) ⟨1316471, by rfl⟩ : syracuseStep 7021181 = 2632943) B2632943
theorem B6300953 : Blo 646304 6300953 := bstep (se 2 (by rfl) ⟨2362857, by rfl⟩ : syracuseStep 6300953 = 4725715) B4725715
theorem B11053097 : Blo 646304 11053097 := bstep (se 2 (by rfl) ⟨4144911, by rfl⟩ : syracuseStep 11053097 = 8289823) B8289823
theorem B2075071 : Blo 646304 2075071 := bstep (se 1 (by rfl) ⟨1556303, by rfl⟩ : syracuseStep 2075071 = 3112607) B3112607
theorem B1845919 : Blo 646304 1845919 := bstep (se 1 (by rfl) ⟨1384439, by rfl⟩ : syracuseStep 1845919 = 2768879) B2768879
theorem B3288275 : Blo 646304 3288275 := bstep (se 1 (by rfl) ⟨2466206, by rfl⟩ : syracuseStep 3288275 = 4932413) B4932413
theorem B2960639 : Blo 646304 2960639 := bstep (se 1 (by rfl) ⟨2220479, by rfl⟩ : syracuseStep 2960639 = 4440959) B4440959
theorem B3124601 : Blo 646304 3124601 := bstep (se 2 (by rfl) ⟨1171725, by rfl⟩ : syracuseStep 3124601 = 2343451) B2343451
theorem B1388011 : Blo 646304 1388011 := bstep (se 1 (by rfl) ⟨1041008, by rfl⟩ : syracuseStep 1388011 = 2082017) B2082017
theorem B667675 : Blo 646304 667675 := bstep (se 1 (by rfl) ⟨500756, by rfl⟩ : syracuseStep 667675 = 1001513) B1001513
theorem B1455443 : Blo 646304 1455443 := bstep (se 1 (by rfl) ⟨1091582, by rfl⟩ : syracuseStep 1455443 = 2183165) B2183165
theorem B3684527 : Blo 646304 3684527 := bstep (se 1 (by rfl) ⟨2763395, by rfl⟩ : syracuseStep 3684527 = 5526791) B5526791
theorem B3291515 : Blo 646304 3291515 := bstep (se 1 (by rfl) ⟨2468636, by rfl⟩ : syracuseStep 3291515 = 4937273) B4937273
theorem B1096105 : Blo 646304 1096105 := bstep (se 2 (by rfl) ⟨411039, by rfl⟩ : syracuseStep 1096105 = 822079) B822079
theorem B7387685 : Blo 646304 7387685 := bstep (se 4 (by rfl) ⟨692595, by rfl⟩ : syracuseStep 7387685 = 1385191) B1385191
theorem B1096807 : Blo 646304 1096807 := bstep (se 1 (by rfl) ⟨822605, by rfl⟩ : syracuseStep 1096807 = 1645211) B1645211
theorem B1457279 : Blo 646304 1457279 := bstep (se 1 (by rfl) ⟨1092959, by rfl⟩ : syracuseStep 1457279 = 2185919) B2185919
theorem B1228115 : Blo 646304 1228115 := bstep (se 1 (by rfl) ⟨921086, by rfl⟩ : syracuseStep 1228115 = 1842173) B1842173
theorem B6241819 : Blo 646304 6241819 := bstep (se 1 (by rfl) ⟨4681364, by rfl⟩ : syracuseStep 6241819 = 9362729) B9362729
theorem B2768863 : Blo 646304 2768863 := bstep (se 1 (by rfl) ⟨2076647, by rfl⟩ : syracuseStep 2768863 = 4153295) B4153295
theorem B4997227 : Blo 646304 4997227 := bstep (se 1 (by rfl) ⟨3747920, by rfl⟩ : syracuseStep 4997227 = 7495841) B7495841
theorem B1754423 : Blo 646304 1754423 := bstep (se 1 (by rfl) ⟨1315817, by rfl⟩ : syracuseStep 1754423 = 2631635) B2631635
theorem B1459943 : Blo 646304 1459943 := bstep (se 1 (by rfl) ⟨1094957, by rfl⟩ : syracuseStep 1459943 = 2189915) B2189915
theorem B5523815 : Blo 646304 5523815 := bstep (se 1 (by rfl) ⟨4142861, by rfl⟩ : syracuseStep 5523815 = 8285723) B8285723
theorem B969671 : Blo 646304 969671 := bstep (se 1 (by rfl) ⟨727253, by rfl⟩ : syracuseStep 969671 = 1454507) B1454507
theorem B3689833 : Blo 646304 3689833 := bstep (se 2 (by rfl) ⟨1383687, by rfl⟩ : syracuseStep 3689833 = 2767375) B2767375
theorem B970607 : Blo 646304 970607 := bstep (se 1 (by rfl) ⟨727955, by rfl⟩ : syracuseStep 970607 = 1455911) B1455911
theorem B970823 : Blo 646304 970823 := bstep (se 1 (by rfl) ⟨728117, by rfl⟩ : syracuseStep 970823 = 1456235) B1456235
theorem B970889 : Blo 646304 970889 := bstep (se 2 (by rfl) ⟨364083, by rfl⟩ : syracuseStep 970889 = 728167) B728167
theorem B1659143 : Blo 646304 1659143 := bstep (se 1 (by rfl) ⟨1244357, by rfl⟩ : syracuseStep 1659143 = 2488715) B2488715
theorem B3690791 : Blo 646304 3690791 := bstep (se 1 (by rfl) ⟨2768093, by rfl⟩ : syracuseStep 3690791 = 5536187) B5536187
theorem B6214907 : Blo 646304 6214907 := bstep (se 1 (by rfl) ⟨4661180, by rfl⟩ : syracuseStep 6214907 = 9322361) B9322361
theorem B972191 : Blo 646304 972191 := bstep (se 1 (by rfl) ⟨729143, by rfl⟩ : syracuseStep 972191 = 1458287) B1458287
theorem B972767 : Blo 646304 972767 := bstep (se 1 (by rfl) ⟨729575, by rfl⟩ : syracuseStep 972767 = 1459151) B1459151
theorem B972779 : Blo 646304 972779 := bstep (se 1 (by rfl) ⟨729584, by rfl⟩ : syracuseStep 972779 = 1459169) B1459169
theorem B973247 : Blo 646304 973247 := bstep (se 1 (by rfl) ⟨729935, by rfl⟩ : syracuseStep 973247 = 1459871) B1459871
theorem B37837493 : Blo 646304 37837493 := bstep (se 5 (by rfl) ⟨1773632, by rfl⟩ : syracuseStep 37837493 = 3547265) B3547265
theorem B973919 : Blo 646304 973919 := bstep (se 1 (by rfl) ⟨730439, by rfl⟩ : syracuseStep 973919 = 1460879) B1460879
theorem B973979 : Blo 646304 973979 := bstep (se 1 (by rfl) ⟨730484, by rfl⟩ : syracuseStep 973979 = 1460969) B1460969
theorem B646399 : Blo 646304 646399 := bstep (se 1 (by rfl) ⟨484799, by rfl⟩ : syracuseStep 646399 = 969599) B969599
theorem B646503 : Blo 646304 646503 := bstep (se 1 (by rfl) ⟨484877, by rfl⟩ : syracuseStep 646503 = 969755) B969755
theorem B646811 : Blo 646304 646811 := bstep (se 1 (by rfl) ⟨485108, by rfl⟩ : syracuseStep 646811 = 970217) B970217
theorem B974543 : Blo 646304 974543 := bstep (se 1 (by rfl) ⟨730907, by rfl⟩ : syracuseStep 974543 = 1461815) B1461815
theorem B974879 : Blo 646304 974879 := bstep (se 1 (by rfl) ⟨731159, by rfl⟩ : syracuseStep 974879 = 1462319) B1462319
theorem B647527 : Blo 646304 647527 := bstep (se 1 (by rfl) ⟨485645, by rfl⟩ : syracuseStep 647527 = 971291) B971291
theorem B647647 : Blo 646304 647647 := bstep (se 1 (by rfl) ⟨485735, by rfl⟩ : syracuseStep 647647 = 971471) B971471
theorem B648447 : Blo 646304 648447 := bstep (se 1 (by rfl) ⟨486335, by rfl⟩ : syracuseStep 648447 = 972671) B972671
theorem B649935 : Blo 646304 649935 := bstep (se 1 (by rfl) ⟨487451, by rfl⟩ : syracuseStep 649935 = 974903) B974903
theorem B650239 : Blo 646304 650239 := bstep (se 1 (by rfl) ⟨487679, by rfl⟩ : syracuseStep 650239 = 975359) B975359
theorem B4682863 : Blo 646304 4682863 := bstep (se 1 (by rfl) ⟨3512147, by rfl⟩ : syracuseStep 4682863 = 7024295) B7024295
theorem B3273857 : Blo 646304 3273857 := bstep (se 2 (by rfl) ⟨1227696, by rfl⟩ : syracuseStep 3273857 = 2455393) B2455393
theorem B1898039 : Blo 646304 1898039 := bstep (se 1 (by rfl) ⟨1423529, by rfl⟩ : syracuseStep 1898039 = 2847059) B2847059
theorem B31487879 : Blo 646304 31487879 := bstep (se 1 (by rfl) ⟨23615909, by rfl⟩ : syracuseStep 31487879 = 47231819) B47231819
theorem B2455879 : Blo 646304 2455879 := bstep (se 1 (by rfl) ⟨1841909, by rfl⟩ : syracuseStep 2455879 = 3683819) B3683819
theorem B1636919 : Blo 646304 1636919 := bstep (se 1 (by rfl) ⟨1227689, by rfl⟩ : syracuseStep 1636919 = 2455379) B2455379
theorem B240056945 : Blo 646304 240056945 := bstep (se 2 (by rfl) ⟨90021354, by rfl⟩ : syracuseStep 240056945 = 180042709) B180042709
theorem B25328375 : Blo 646304 25328375 := bstep (se 1 (by rfl) ⟨18996281, by rfl⟩ : syracuseStep 25328375 = 37992563) B37992563
theorem B3702023 : Blo 646304 3702023 := bstep (se 1 (by rfl) ⟨2776517, by rfl⟩ : syracuseStep 3702023 = 5553035) B5553035
theorem B1637759 : Blo 646304 1637759 := bstep (se 1 (by rfl) ⟨1228319, by rfl⟩ : syracuseStep 1637759 = 2456639) B2456639
theorem B4685921 : Blo 646304 4685921 := bstep (se 2 (by rfl) ⟨1757220, by rfl⟩ : syracuseStep 4685921 = 3514441) B3514441
theorem B2460527 : Blo 646304 2460527 := bstep (se 1 (by rfl) ⟨1845395, by rfl⟩ : syracuseStep 2460527 = 3690791) B3690791
theorem B1641455 : Blo 646304 1641455 := bstep (se 1 (by rfl) ⟨1231091, by rfl⟩ : syracuseStep 1641455 = 2462183) B2462183
theorem B3280175 : Blo 646304 3280175 := bstep (se 1 (by rfl) ⟨2460131, by rfl⟩ : syracuseStep 3280175 = 4920263) B4920263
theorem B2461225 : Blo 646304 2461225 := bstep (se 2 (by rfl) ⟨922959, by rfl⟩ : syracuseStep 2461225 = 1845919) B1845919
theorem B4919777 : Blo 646304 4919777 := bstep (se 2 (by rfl) ⟨1844916, by rfl⟩ : syracuseStep 4919777 = 3689833) B3689833
theorem B890233 : Blo 646304 890233 := bstep (se 2 (by rfl) ⟨333837, by rfl⟩ : syracuseStep 890233 = 667675) B667675
theorem B4200635 : Blo 646304 4200635 := bstep (se 1 (by rfl) ⟨3150476, by rfl⟩ : syracuseStep 4200635 = 6300953) B6300953
theorem B1973759 : Blo 646304 1973759 := bstep (se 1 (by rfl) ⟨1480319, by rfl⟩ : syracuseStep 1973759 = 2960639) B2960639
theorem B4925123 : Blo 646304 4925123 := bstep (se 1 (by rfl) ⟨3693842, by rfl⟩ : syracuseStep 4925123 = 7387685) B7387685
theorem B1091279 : Blo 646304 1091279 := bstep (se 1 (by rfl) ⟨818459, by rfl⟩ : syracuseStep 1091279 = 1636919) B1636919
theorem B16885583 : Blo 646304 16885583 := bstep (se 1 (by rfl) ⟨12664187, by rfl⟩ : syracuseStep 16885583 = 25328375) B25328375
theorem B2468015 : Blo 646304 2468015 := bstep (se 1 (by rfl) ⟨1851011, by rfl⟩ : syracuseStep 2468015 = 3702023) B3702023
theorem B1091839 : Blo 646304 1091839 := bstep (se 1 (by rfl) ⟨818879, by rfl⟩ : syracuseStep 1091839 = 1637759) B1637759
theorem B6662969 : Blo 646304 6662969 := bstep (se 2 (by rfl) ⟨2498613, by rfl⟩ : syracuseStep 6662969 = 4997227) B4997227
theorem B3682543 : Blo 646304 3682543 := bstep (se 1 (by rfl) ⟨2761907, by rfl⟩ : syracuseStep 3682543 = 5523815) B5523815
theorem B18723149 : Blo 646304 18723149 := bstep (se 3 (by rfl) ⟨3510590, by rfl⟩ : syracuseStep 18723149 = 7021181) B7021181
theorem B2766761 : Blo 646304 2766761 := bstep (se 2 (by rfl) ⟨1037535, by rfl⟩ : syracuseStep 2766761 = 2075071) B2075071
theorem B1095707 : Blo 646304 1095707 := bstep (se 1 (by rfl) ⟨821780, by rfl⟩ : syracuseStep 1095707 = 1643561) B1643561
theorem B5061437 : Blo 646304 5061437 := bstep (se 3 (by rfl) ⟨949019, by rfl⟩ : syracuseStep 5061437 = 1898039) B1898039
theorem B1752095 : Blo 646304 1752095 := bstep (se 1 (by rfl) ⟨1314071, by rfl⟩ : syracuseStep 1752095 = 2628143) B2628143
theorem B11254895 : Blo 646304 11254895 := bstep (se 1 (by rfl) ⟨8441171, by rfl⟩ : syracuseStep 11254895 = 16882343) B16882343
theorem B1850681 : Blo 646304 1850681 := bstep (se 2 (by rfl) ⟨694005, by rfl⟩ : syracuseStep 1850681 = 1388011) B1388011
theorem B83967677 : Blo 646304 83967677 := bstep (se 3 (by rfl) ⟨15743939, by rfl⟩ : syracuseStep 83967677 = 31487879) B31487879
theorem B2080991 : Blo 646304 2080991 := bstep (se 1 (by rfl) ⟨1560743, by rfl⟩ : syracuseStep 2080991 = 3121487) B3121487
theorem B6996617 : Blo 646304 6996617 := bstep (se 2 (by rfl) ⟨2623731, by rfl⟩ : syracuseStep 6996617 = 5247463) B5247463
theorem B6243817 : Blo 646304 6243817 := bstep (se 2 (by rfl) ⟨2341431, by rfl⟩ : syracuseStep 6243817 = 4682863) B4682863
theorem B2083067 : Blo 646304 2083067 := bstep (se 1 (by rfl) ⟨1562300, by rfl⟩ : syracuseStep 2083067 = 3124601) B3124601
theorem B1461473 : Blo 646304 1461473 := bstep (se 2 (by rfl) ⟨548052, by rfl⟩ : syracuseStep 1461473 = 1096105) B1096105
theorem B2182571 : Blo 646304 2182571 := bstep (se 1 (by rfl) ⟨1636928, by rfl⟩ : syracuseStep 2182571 = 3273857) B3273857
theorem B970295 : Blo 646304 970295 := bstep (se 1 (by rfl) ⟨727721, by rfl⟩ : syracuseStep 970295 = 1455443) B1455443
theorem B1462409 : Blo 646304 1462409 := bstep (se 2 (by rfl) ⟨548403, by rfl⟩ : syracuseStep 1462409 = 1096807) B1096807
theorem B971519 : Blo 646304 971519 := bstep (se 1 (by rfl) ⟨728639, by rfl⟩ : syracuseStep 971519 = 1457279) B1457279
theorem B971753 : Blo 646304 971753 := bstep (se 2 (by rfl) ⟨364407, by rfl⟩ : syracuseStep 971753 = 728815) B728815
theorem B3691817 : Blo 646304 3691817 := bstep (se 2 (by rfl) ⟨1384431, by rfl⟩ : syracuseStep 3691817 = 2768863) B2768863
theorem B2184569 : Blo 646304 2184569 := bstep (se 2 (by rfl) ⟨819213, by rfl⟩ : syracuseStep 2184569 = 1638427) B1638427
theorem B47339255 : Blo 646304 47339255 := bstep (se 1 (by rfl) ⟨35504441, by rfl⟩ : syracuseStep 47339255 = 71008883) B71008883
theorem B1169615 : Blo 646304 1169615 := bstep (se 1 (by rfl) ⟨877211, by rfl⟩ : syracuseStep 1169615 = 1754423) B1754423
theorem B973295 : Blo 646304 973295 := bstep (se 1 (by rfl) ⟨729971, by rfl⟩ : syracuseStep 973295 = 1459943) B1459943
theorem B2186351 : Blo 646304 2186351 := bstep (se 1 (by rfl) ⟨1639763, by rfl⟩ : syracuseStep 2186351 = 3279527) B3279527
theorem B646447 : Blo 646304 646447 := bstep (se 1 (by rfl) ⟨484835, by rfl⟩ : syracuseStep 646447 = 969671) B969671
theorem B647071 : Blo 646304 647071 := bstep (se 1 (by rfl) ⟨485303, by rfl⟩ : syracuseStep 647071 = 970607) B970607
theorem B647215 : Blo 646304 647215 := bstep (se 1 (by rfl) ⟨485411, by rfl⟩ : syracuseStep 647215 = 970823) B970823
theorem B647259 : Blo 646304 647259 := bstep (se 1 (by rfl) ⟨485444, by rfl⟩ : syracuseStep 647259 = 970889) B970889
theorem B1106095 : Blo 646304 1106095 := bstep (se 1 (by rfl) ⟨829571, by rfl⟩ : syracuseStep 1106095 = 1659143) B1659143
theorem B16573085 : Blo 646304 16573085 := bstep (se 3 (by rfl) ⟨3107453, by rfl⟩ : syracuseStep 16573085 = 6214907) B6214907
theorem B648127 : Blo 646304 648127 := bstep (se 1 (by rfl) ⟨486095, by rfl⟩ : syracuseStep 648127 = 972191) B972191
theorem B2188457 : Blo 646304 2188457 := bstep (se 2 (by rfl) ⟨820671, by rfl⟩ : syracuseStep 2188457 = 1641343) B1641343
theorem B648511 : Blo 646304 648511 := bstep (se 1 (by rfl) ⟨486383, by rfl⟩ : syracuseStep 648511 = 972767) B972767
theorem B648519 : Blo 646304 648519 := bstep (se 1 (by rfl) ⟨486389, by rfl⟩ : syracuseStep 648519 = 972779) B972779
theorem B648831 : Blo 646304 648831 := bstep (se 1 (by rfl) ⟨486623, by rfl⟩ : syracuseStep 648831 = 973247) B973247
theorem B25224995 : Blo 646304 25224995 := bstep (se 1 (by rfl) ⟨18918746, by rfl⟩ : syracuseStep 25224995 = 37837493) B37837493
theorem B649279 : Blo 646304 649279 := bstep (se 1 (by rfl) ⟨486959, by rfl⟩ : syracuseStep 649279 = 973919) B973919
theorem B649319 : Blo 646304 649319 := bstep (se 1 (by rfl) ⟨486989, by rfl⟩ : syracuseStep 649319 = 973979) B973979
theorem B649695 : Blo 646304 649695 := bstep (se 1 (by rfl) ⟨487271, by rfl⟩ : syracuseStep 649695 = 974543) B974543
theorem B649919 : Blo 646304 649919 := bstep (se 1 (by rfl) ⟨487439, by rfl⟩ : syracuseStep 649919 = 974879) B974879
theorem B17329051 : Blo 646304 17329051 := bstep (se 1 (by rfl) ⟨12996788, by rfl⟩ : syracuseStep 17329051 = 25993577) B25993577
theorem B1666079 : Blo 646304 1666079 := bstep (se 1 (by rfl) ⟨1249559, by rfl⟩ : syracuseStep 1666079 = 2499119) B2499119
theorem B9006761 : Blo 646304 9006761 := bstep (se 2 (by rfl) ⟨3377535, by rfl⟩ : syracuseStep 9006761 = 6755071) B6755071
theorem B7368731 : Blo 646304 7368731 := bstep (se 1 (by rfl) ⟨5526548, by rfl⟩ : syracuseStep 7368731 = 11053097) B11053097
theorem B95777477 : Blo 646304 95777477 := bstep (se 4 (by rfl) ⟨8979138, by rfl⟩ : syracuseStep 95777477 = 17958277) B17958277
theorem B2192183 : Blo 646304 2192183 := bstep (se 1 (by rfl) ⟨1644137, by rfl⟩ : syracuseStep 2192183 = 3288275) B3288275
theorem B3274505 : Blo 646304 3274505 := bstep (se 2 (by rfl) ⟨1227939, by rfl⟩ : syracuseStep 3274505 = 2455879) B2455879
theorem B2456351 : Blo 646304 2456351 := bstep (se 1 (by rfl) ⟨1842263, by rfl⟩ : syracuseStep 2456351 = 3684527) B3684527
theorem B2194343 : Blo 646304 2194343 := bstep (se 1 (by rfl) ⟨1645757, by rfl⟩ : syracuseStep 2194343 = 3291515) B3291515
theorem B160037963 : Blo 646304 160037963 := bstep (se 1 (by rfl) ⟨120028472, by rfl⟩ : syracuseStep 160037963 = 240056945) B240056945
theorem B8322425 : Blo 646304 8322425 := bstep (se 2 (by rfl) ⟨3120909, by rfl⟩ : syracuseStep 8322425 = 6241819) B6241819
theorem B818743 : Blo 646304 818743 := bstep (se 1 (by rfl) ⟨614057, by rfl⟩ : syracuseStep 818743 = 1228115) B1228115
theorem B1474793 : Blo 646304 1474793 := bstep (se 2 (by rfl) ⟨553047, by rfl⟩ : syracuseStep 1474793 = 1106095) B1106095
theorem B1640351 : Blo 646304 1640351 := bstep (se 1 (by rfl) ⟨1230263, by rfl⟩ : syracuseStep 1640351 = 2460527) B2460527
theorem B8325089 : Blo 646304 8325089 := bstep (se 2 (by rfl) ⟨3121908, by rfl⟩ : syracuseStep 8325089 = 6243817) B6243817
theorem B3279851 : Blo 646304 3279851 := bstep (se 1 (by rfl) ⟨2459888, by rfl⟩ : syracuseStep 3279851 = 4919777) B4919777
theorem B2461211 : Blo 646304 2461211 := bstep (se 1 (by rfl) ⟨1845908, by rfl⟩ : syracuseStep 2461211 = 3691817) B3691817
theorem B31559503 : Blo 646304 31559503 := bstep (se 1 (by rfl) ⟨23669627, by rfl⟩ : syracuseStep 31559503 = 47339255) B47339255
theorem B23105401 : Blo 646304 23105401 := bstep (se 2 (by rfl) ⟨8664525, by rfl⟩ : syracuseStep 23105401 = 17329051) B17329051
theorem B3281633 : Blo 646304 3281633 := bstep (se 2 (by rfl) ⟨1230612, by rfl⟩ : syracuseStep 3281633 = 2461225) B2461225
theorem B11048723 : Blo 646304 11048723 := bstep (se 1 (by rfl) ⟨8286542, by rfl⟩ : syracuseStep 11048723 = 16573085) B16573085
theorem B3283415 : Blo 646304 3283415 := bstep (se 1 (by rfl) ⟨2462561, by rfl⟩ : syracuseStep 3283415 = 4925123) B4925123
theorem B727519 : Blo 646304 727519 := bstep (se 1 (by rfl) ⟨545639, by rfl⟩ : syracuseStep 727519 = 1091279) B1091279
theorem B16816663 : Blo 646304 16816663 := bstep (se 1 (by rfl) ⟨12612497, by rfl⟩ : syracuseStep 16816663 = 25224995) B25224995
theorem B1645343 : Blo 646304 1645343 := bstep (se 1 (by rfl) ⟨1234007, by rfl⟩ : syracuseStep 1645343 = 2468015) B2468015
theorem B6004507 : Blo 646304 6004507 := bstep (se 1 (by rfl) ⟨4503380, by rfl⟩ : syracuseStep 6004507 = 9006761) B9006761
theorem B1844507 : Blo 646304 1844507 := bstep (se 1 (by rfl) ⟨1383380, by rfl⟩ : syracuseStep 1844507 = 2766761) B2766761
theorem B730471 : Blo 646304 730471 := bstep (se 1 (by rfl) ⟨547853, by rfl⟩ : syracuseStep 730471 = 1095707) B1095707
theorem B1091657 : Blo 646304 1091657 := bstep (se 2 (by rfl) ⟨409371, by rfl⟩ : syracuseStep 1091657 = 818743) B818743
theorem B5548283 : Blo 646304 5548283 := bstep (se 1 (by rfl) ⟨4161212, by rfl⟩ : syracuseStep 5548283 = 8322425) B8322425
theorem B55978451 : Blo 646304 55978451 := bstep (se 1 (by rfl) ⟨41983838, by rfl⟩ : syracuseStep 55978451 = 83967677) B83967677
theorem B3123947 : Blo 646304 3123947 := bstep (se 1 (by rfl) ⟨2342960, by rfl⟩ : syracuseStep 3123947 = 4685921) B4685921
theorem B4664411 : Blo 646304 4664411 := bstep (se 1 (by rfl) ⟨3498308, by rfl⟩ : syracuseStep 4664411 = 6996617) B6996617
theorem B5549309 : Blo 646304 5549309 := bstep (se 3 (by rfl) ⟨1040495, by rfl⟩ : syracuseStep 5549309 = 2080991) B2080991
theorem B1388711 : Blo 646304 1388711 := bstep (se 1 (by rfl) ⟨1041533, by rfl⟩ : syracuseStep 1388711 = 2083067) B2083067
theorem B1094303 : Blo 646304 1094303 := bstep (se 1 (by rfl) ⟨820727, by rfl⟩ : syracuseStep 1094303 = 1641455) B1641455
theorem B1455047 : Blo 646304 1455047 := bstep (se 1 (by rfl) ⟨1091285, by rfl⟩ : syracuseStep 1455047 = 2182571) B2182571
theorem B1455785 : Blo 646304 1455785 := bstep (se 2 (by rfl) ⟨545919, by rfl⟩ : syracuseStep 1455785 = 1091839) B1091839
theorem B1456379 : Blo 646304 1456379 := bstep (se 1 (by rfl) ⟨1092284, by rfl⟩ : syracuseStep 1456379 = 2184569) B2184569
theorem B2800423 : Blo 646304 2800423 := bstep (se 1 (by rfl) ⟨2100317, by rfl⟩ : syracuseStep 2800423 = 4200635) B4200635
theorem B1457567 : Blo 646304 1457567 := bstep (se 1 (by rfl) ⟨1093175, by rfl⟩ : syracuseStep 1457567 = 2186351) B2186351
theorem B21053429 : Blo 646304 21053429 := bstep (se 5 (by rfl) ⟨986879, by rfl⟩ : syracuseStep 21053429 = 1973759) B1973759
theorem B1458971 : Blo 646304 1458971 := bstep (se 1 (by rfl) ⟨1094228, by rfl⟩ : syracuseStep 1458971 = 2188457) B2188457
theorem B11257055 : Blo 646304 11257055 := bstep (se 1 (by rfl) ⟨8442791, by rfl⟩ : syracuseStep 11257055 = 16885583) B16885583
theorem B4441979 : Blo 646304 4441979 := bstep (se 1 (by rfl) ⟨3331484, by rfl⟩ : syracuseStep 4441979 = 6662969) B6662969
theorem B63851651 : Blo 646304 63851651 := bstep (se 1 (by rfl) ⟨47888738, by rfl⟩ : syracuseStep 63851651 = 95777477) B95777477
theorem B1461455 : Blo 646304 1461455 := bstep (se 1 (by rfl) ⟨1096091, by rfl⟩ : syracuseStep 1461455 = 2192183) B2192183
theorem B2183003 : Blo 646304 2183003 := bstep (se 1 (by rfl) ⟨1637252, by rfl⟩ : syracuseStep 2183003 = 3274505) B3274505
theorem B1462895 : Blo 646304 1462895 := bstep (se 1 (by rfl) ⟨1097171, by rfl⟩ : syracuseStep 1462895 = 2194343) B2194343
theorem B1168063 : Blo 646304 1168063 := bstep (se 1 (by rfl) ⟨876047, by rfl⟩ : syracuseStep 1168063 = 1752095) B1752095
theorem B1233787 : Blo 646304 1233787 := bstep (se 1 (by rfl) ⟨925340, by rfl⟩ : syracuseStep 1233787 = 1850681) B1850681
theorem B974315 : Blo 646304 974315 := bstep (se 1 (by rfl) ⟨730736, by rfl⟩ : syracuseStep 974315 = 1461473) B1461473
theorem B2186783 : Blo 646304 2186783 := bstep (se 1 (by rfl) ⟨1640087, by rfl⟩ : syracuseStep 2186783 = 3280175) B3280175
theorem B646863 : Blo 646304 646863 := bstep (se 1 (by rfl) ⟨485147, by rfl⟩ : syracuseStep 646863 = 970295) B970295
theorem B974939 : Blo 646304 974939 := bstep (se 1 (by rfl) ⟨731204, by rfl⟩ : syracuseStep 974939 = 1462409) B1462409
theorem B647679 : Blo 646304 647679 := bstep (se 1 (by rfl) ⟨485759, by rfl⟩ : syracuseStep 647679 = 971519) B971519
theorem B647835 : Blo 646304 647835 := bstep (se 1 (by rfl) ⟨485876, by rfl⟩ : syracuseStep 647835 = 971753) B971753
theorem B779743 : Blo 646304 779743 := bstep (se 1 (by rfl) ⟨584807, by rfl⟩ : syracuseStep 779743 = 1169615) B1169615
theorem B648863 : Blo 646304 648863 := bstep (se 1 (by rfl) ⟨486647, by rfl⟩ : syracuseStep 648863 = 973295) B973295
theorem B4910057 : Blo 646304 4910057 := bstep (se 2 (by rfl) ⟨1841271, by rfl⟩ : syracuseStep 4910057 = 3682543) B3682543
theorem B4747909 : Blo 646304 4747909 := bstep (se 4 (by rfl) ⟨445116, by rfl⟩ : syracuseStep 4747909 = 890233) B890233
theorem B1110719 : Blo 646304 1110719 := bstep (se 1 (by rfl) ⟨833039, by rfl⟩ : syracuseStep 1110719 = 1666079) B1666079
theorem B4912487 : Blo 646304 4912487 := bstep (se 1 (by rfl) ⟨3684365, by rfl⟩ : syracuseStep 4912487 = 7368731) B7368731
theorem B12482099 : Blo 646304 12482099 := bstep (se 1 (by rfl) ⟨9361574, by rfl⟩ : syracuseStep 12482099 = 18723149) B18723149
theorem B1637567 : Blo 646304 1637567 := bstep (se 1 (by rfl) ⟨1228175, by rfl⟩ : syracuseStep 1637567 = 2456351) B2456351
theorem B3374291 : Blo 646304 3374291 := bstep (se 1 (by rfl) ⟨2530718, by rfl⟩ : syracuseStep 3374291 = 5061437) B5061437
theorem B106691975 : Blo 646304 106691975 := bstep (se 1 (by rfl) ⟨80018981, by rfl⟩ : syracuseStep 106691975 = 160037963) B160037963
theorem B7503263 : Blo 646304 7503263 := bstep (se 1 (by rfl) ⟨5627447, by rfl⟩ : syracuseStep 7503263 = 11254895) B11254895
theorem B983195 : Blo 646304 983195 := bstep (se 1 (by rfl) ⟨737396, by rfl⟩ : syracuseStep 983195 = 1474793) B1474793
theorem B3703229 : Blo 646304 3703229 := bstep (se 3 (by rfl) ⟨694355, by rfl⟩ : syracuseStep 3703229 = 1388711) B1388711
theorem B7504703 : Blo 646304 7504703 := bstep (se 1 (by rfl) ⟨5628527, by rfl⟩ : syracuseStep 7504703 = 11257055) B11257055
theorem B42567767 : Blo 646304 42567767 := bstep (se 1 (by rfl) ⟨31925825, by rfl⟩ : syracuseStep 42567767 = 63851651) B63851651
theorem B1640807 : Blo 646304 1640807 := bstep (se 1 (by rfl) ⟨1230605, by rfl⟩ : syracuseStep 1640807 = 2461211) B2461211
theorem B89688869 : Blo 646304 89688869 := bstep (se 4 (by rfl) ⟨8408331, by rfl⟩ : syracuseStep 89688869 = 16816663) B16816663
theorem B42079337 : Blo 646304 42079337 := bstep (se 2 (by rfl) ⟨15779751, by rfl⟩ : syracuseStep 42079337 = 31559503) B31559503
theorem B6330545 : Blo 646304 6330545 := bstep (se 2 (by rfl) ⟨2373954, by rfl⟩ : syracuseStep 6330545 = 4747909) B4747909
theorem B1645049 : Blo 646304 1645049 := bstep (se 2 (by rfl) ⟨616893, by rfl⟩ : syracuseStep 1645049 = 1233787) B1233787
theorem B727771 : Blo 646304 727771 := bstep (se 1 (by rfl) ⟨545828, by rfl⟩ : syracuseStep 727771 = 1091657) B1091657
theorem B8330525 : Blo 646304 8330525 := bstep (se 3 (by rfl) ⟨1561973, by rfl⟩ : syracuseStep 8330525 = 3123947) B3123947
theorem B729535 : Blo 646304 729535 := bstep (se 1 (by rfl) ⟨547151, by rfl⟩ : syracuseStep 729535 = 1094303) B1094303
theorem B1091711 : Blo 646304 1091711 := bstep (se 1 (by rfl) ⟨818783, by rfl⟩ : syracuseStep 1091711 = 1637567) B1637567
theorem B8006009 : Blo 646304 8006009 := bstep (se 2 (by rfl) ⟨3002253, by rfl⟩ : syracuseStep 8006009 = 6004507) B6004507
theorem B14035619 : Blo 646304 14035619 := bstep (se 1 (by rfl) ⟨10526714, by rfl⟩ : syracuseStep 14035619 = 21053429) B21053429
theorem B2961319 : Blo 646304 2961319 := bstep (se 1 (by rfl) ⟨2220989, by rfl⟩ : syracuseStep 2961319 = 4441979) B4441979
theorem B1093567 : Blo 646304 1093567 := bstep (se 1 (by rfl) ⟨820175, by rfl⟩ : syracuseStep 1093567 = 1640351) B1640351
theorem B5550059 : Blo 646304 5550059 := bstep (se 1 (by rfl) ⟨4162544, by rfl⟩ : syracuseStep 5550059 = 8325089) B8325089
theorem B2961917 : Blo 646304 2961917 := bstep (se 3 (by rfl) ⟨555359, by rfl⟩ : syracuseStep 2961917 = 1110719) B1110719
theorem B1455335 : Blo 646304 1455335 := bstep (se 1 (by rfl) ⟨1091501, by rfl⟩ : syracuseStep 1455335 = 2183003) B2183003
theorem B24918677 : Blo 646304 24918677 := bstep (se 6 (by rfl) ⟨584031, by rfl⟩ : syracuseStep 24918677 = 1168063) B1168063
theorem B1096895 : Blo 646304 1096895 := bstep (se 1 (by rfl) ⟨822671, by rfl⟩ : syracuseStep 1096895 = 1645343) B1645343
theorem B1457855 : Blo 646304 1457855 := bstep (se 1 (by rfl) ⟨1093391, by rfl⟩ : syracuseStep 1457855 = 2186783) B2186783
theorem B1229671 : Blo 646304 1229671 := bstep (se 1 (by rfl) ⟨922253, by rfl⟩ : syracuseStep 1229671 = 1844507) B1844507
theorem B970025 : Blo 646304 970025 := bstep (se 2 (by rfl) ⟨363759, by rfl⟩ : syracuseStep 970025 = 727519) B727519
theorem B970031 : Blo 646304 970031 := bstep (se 1 (by rfl) ⟨727523, by rfl⟩ : syracuseStep 970031 = 1455047) B1455047
theorem B970523 : Blo 646304 970523 := bstep (se 1 (by rfl) ⟨727892, by rfl⟩ : syracuseStep 970523 = 1455785) B1455785
theorem B970919 : Blo 646304 970919 := bstep (se 1 (by rfl) ⟨728189, by rfl⟩ : syracuseStep 970919 = 1456379) B1456379
theorem B123228805 : Blo 646304 123228805 := bstep (se 4 (by rfl) ⟨11552700, by rfl⟩ : syracuseStep 123228805 = 23105401) B23105401
theorem B2249527 : Blo 646304 2249527 := bstep (se 1 (by rfl) ⟨1687145, by rfl⟩ : syracuseStep 2249527 = 3374291) B3374291
theorem B71127983 : Blo 646304 71127983 := bstep (se 1 (by rfl) ⟨53345987, by rfl⟩ : syracuseStep 71127983 = 106691975) B106691975
theorem B971711 : Blo 646304 971711 := bstep (se 1 (by rfl) ⟨728783, by rfl⟩ : syracuseStep 971711 = 1457567) B1457567
theorem B5002175 : Blo 646304 5002175 := bstep (se 1 (by rfl) ⟨3751631, by rfl⟩ : syracuseStep 5002175 = 7503263) B7503263
theorem B972647 : Blo 646304 972647 := bstep (se 1 (by rfl) ⟨729485, by rfl⟩ : syracuseStep 972647 = 1458971) B1458971
theorem B973961 : Blo 646304 973961 := bstep (se 2 (by rfl) ⟨365235, by rfl⟩ : syracuseStep 973961 = 730471) B730471
theorem B1039657 : Blo 646304 1039657 := bstep (se 2 (by rfl) ⟨389871, by rfl⟩ : syracuseStep 1039657 = 779743) B779743
theorem B2186567 : Blo 646304 2186567 := bstep (se 1 (by rfl) ⟨1639925, by rfl⟩ : syracuseStep 2186567 = 3279851) B3279851
theorem B974303 : Blo 646304 974303 := bstep (se 1 (by rfl) ⟨730727, by rfl⟩ : syracuseStep 974303 = 1461455) B1461455
theorem B975263 : Blo 646304 975263 := bstep (se 1 (by rfl) ⟨731447, by rfl⟩ : syracuseStep 975263 = 1462895) B1462895
theorem B2187755 : Blo 646304 2187755 := bstep (se 1 (by rfl) ⟨1640816, by rfl⟩ : syracuseStep 2187755 = 3281633) B3281633
theorem B7365815 : Blo 646304 7365815 := bstep (se 1 (by rfl) ⟨5524361, by rfl⟩ : syracuseStep 7365815 = 11048723) B11048723
theorem B2188943 : Blo 646304 2188943 := bstep (se 1 (by rfl) ⟨1641707, by rfl⟩ : syracuseStep 2188943 = 3283415) B3283415
theorem B649543 : Blo 646304 649543 := bstep (se 1 (by rfl) ⟨487157, by rfl⟩ : syracuseStep 649543 = 974315) B974315
theorem B649959 : Blo 646304 649959 := bstep (se 1 (by rfl) ⟨487469, by rfl⟩ : syracuseStep 649959 = 974939) B974939
theorem B3698855 : Blo 646304 3698855 := bstep (se 1 (by rfl) ⟨2774141, by rfl⟩ : syracuseStep 3698855 = 5548283) B5548283
theorem B37318967 : Blo 646304 37318967 := bstep (se 1 (by rfl) ⟨27989225, by rfl⟩ : syracuseStep 37318967 = 55978451) B55978451
theorem B3273371 : Blo 646304 3273371 := bstep (se 1 (by rfl) ⟨2455028, by rfl⟩ : syracuseStep 3273371 = 4910057) B4910057
theorem B3109607 : Blo 646304 3109607 := bstep (se 1 (by rfl) ⟨2332205, by rfl⟩ : syracuseStep 3109607 = 4664411) B4664411
theorem B3699539 : Blo 646304 3699539 := bstep (se 1 (by rfl) ⟨2774654, by rfl⟩ : syracuseStep 3699539 = 5549309) B5549309
theorem B3274991 : Blo 646304 3274991 := bstep (se 1 (by rfl) ⟨2456243, by rfl⟩ : syracuseStep 3274991 = 4912487) B4912487
theorem B8321399 : Blo 646304 8321399 := bstep (se 1 (by rfl) ⟨6241049, by rfl⟩ : syracuseStep 8321399 = 12482099) B12482099
theorem B3733897 : Blo 646304 3733897 := bstep (se 2 (by rfl) ⟨1400211, by rfl⟩ : syracuseStep 3733897 = 2800423) B2800423
theorem B655463 : Blo 646304 655463 := bstep (se 1 (by rfl) ⟨491597, by rfl⟩ : syracuseStep 655463 = 983195) B983195
theorem B1639561 : Blo 646304 1639561 := bstep (se 2 (by rfl) ⟨614835, by rfl⟩ : syracuseStep 1639561 = 1229671) B1229671
theorem B28378511 : Blo 646304 28378511 := bstep (se 1 (by rfl) ⟨21283883, by rfl⟩ : syracuseStep 28378511 = 42567767) B42567767
theorem B47418655 : Blo 646304 47418655 := bstep (se 1 (by rfl) ⟨35563991, by rfl⟩ : syracuseStep 47418655 = 71127983) B71127983
theorem B28052891 : Blo 646304 28052891 := bstep (se 1 (by rfl) ⟨21039668, by rfl⟩ : syracuseStep 28052891 = 42079337) B42079337
theorem B85397429 : Blo 646304 85397429 := bstep (se 5 (by rfl) ⟨4003004, by rfl⟩ : syracuseStep 85397429 = 8006009) B8006009
theorem B164305073 : Blo 646304 164305073 := bstep (se 2 (by rfl) ⟨61614402, by rfl⟩ : syracuseStep 164305073 = 123228805) B123228805
theorem B727807 : Blo 646304 727807 := bstep (se 1 (by rfl) ⟨545855, by rfl⟩ : syracuseStep 727807 = 1091711) B1091711
theorem B2465903 : Blo 646304 2465903 := bstep (se 1 (by rfl) ⟨1849427, by rfl⟩ : syracuseStep 2465903 = 3698855) B3698855
theorem B24879311 : Blo 646304 24879311 := bstep (se 1 (by rfl) ⟨18659483, by rfl⟩ : syracuseStep 24879311 = 37318967) B37318967
theorem B1974611 : Blo 646304 1974611 := bstep (se 1 (by rfl) ⟨1480958, by rfl⟩ : syracuseStep 1974611 = 2961917) B2961917
theorem B2073071 : Blo 646304 2073071 := bstep (se 1 (by rfl) ⟨1554803, by rfl⟩ : syracuseStep 2073071 = 3109607) B3109607
theorem B2466359 : Blo 646304 2466359 := bstep (se 1 (by rfl) ⟨1849769, by rfl⟩ : syracuseStep 2466359 = 3699539) B3699539
theorem B5547599 : Blo 646304 5547599 := bstep (se 1 (by rfl) ⟨4160699, by rfl⟩ : syracuseStep 5547599 = 8321399) B8321399
theorem B1386209 : Blo 646304 1386209 := bstep (se 2 (by rfl) ⟨519828, by rfl⟩ : syracuseStep 1386209 = 1039657) B1039657
theorem B731263 : Blo 646304 731263 := bstep (se 1 (by rfl) ⟨548447, by rfl⟩ : syracuseStep 731263 = 1096895) B1096895
theorem B2468819 : Blo 646304 2468819 := bstep (se 1 (by rfl) ⟨1851614, by rfl⟩ : syracuseStep 2468819 = 3703229) B3703229
theorem B1093871 : Blo 646304 1093871 := bstep (se 1 (by rfl) ⟨820403, by rfl⟩ : syracuseStep 1093871 = 1640807) B1640807
theorem B1096699 : Blo 646304 1096699 := bstep (se 1 (by rfl) ⟨822524, by rfl⟩ : syracuseStep 1096699 = 1645049) B1645049
theorem B5553683 : Blo 646304 5553683 := bstep (se 1 (by rfl) ⟨4165262, by rfl⟩ : syracuseStep 5553683 = 8330525) B8330525
theorem B1457711 : Blo 646304 1457711 := bstep (se 1 (by rfl) ⟨1093283, by rfl⟩ : syracuseStep 1457711 = 2186567) B2186567
theorem B3948425 : Blo 646304 3948425 := bstep (se 2 (by rfl) ⟨1480659, by rfl⟩ : syracuseStep 3948425 = 2961319) B2961319
theorem B1458089 : Blo 646304 1458089 := bstep (se 2 (by rfl) ⟨546783, by rfl⟩ : syracuseStep 1458089 = 1093567) B1093567
theorem B1458503 : Blo 646304 1458503 := bstep (se 1 (by rfl) ⟨1093877, by rfl⟩ : syracuseStep 1458503 = 2187755) B2187755
theorem B2999369 : Blo 646304 2999369 := bstep (se 2 (by rfl) ⟨1124763, by rfl⟩ : syracuseStep 2999369 = 2249527) B2249527
theorem B1459295 : Blo 646304 1459295 := bstep (se 1 (by rfl) ⟨1094471, by rfl⟩ : syracuseStep 1459295 = 2188943) B2188943
theorem B9357079 : Blo 646304 9357079 := bstep (se 1 (by rfl) ⟨7017809, by rfl⟩ : syracuseStep 9357079 = 14035619) B14035619
theorem B2182247 : Blo 646304 2182247 := bstep (se 1 (by rfl) ⟨1636685, by rfl⟩ : syracuseStep 2182247 = 3273371) B3273371
theorem B970223 : Blo 646304 970223 := bstep (se 1 (by rfl) ⟨727667, by rfl⟩ : syracuseStep 970223 = 1455335) B1455335
theorem B970361 : Blo 646304 970361 := bstep (se 2 (by rfl) ⟨363885, by rfl⟩ : syracuseStep 970361 = 727771) B727771
theorem B2183327 : Blo 646304 2183327 := bstep (se 1 (by rfl) ⟨1637495, by rfl⟩ : syracuseStep 2183327 = 3274991) B3274991
theorem B971903 : Blo 646304 971903 := bstep (se 1 (by rfl) ⟨728927, by rfl⟩ : syracuseStep 971903 = 1457855) B1457855
theorem B5003135 : Blo 646304 5003135 := bstep (se 1 (by rfl) ⟨3752351, by rfl⟩ : syracuseStep 5003135 = 7504703) B7504703
theorem B972713 : Blo 646304 972713 := bstep (se 2 (by rfl) ⟨364767, by rfl⟩ : syracuseStep 972713 = 729535) B729535
theorem B59792579 : Blo 646304 59792579 := bstep (se 1 (by rfl) ⟨44844434, by rfl⟩ : syracuseStep 59792579 = 89688869) B89688869
theorem B646683 : Blo 646304 646683 := bstep (se 1 (by rfl) ⟨485012, by rfl⟩ : syracuseStep 646683 = 970025) B970025
theorem B646687 : Blo 646304 646687 := bstep (se 1 (by rfl) ⟨485015, by rfl⟩ : syracuseStep 646687 = 970031) B970031
theorem B647015 : Blo 646304 647015 := bstep (se 1 (by rfl) ⟨485261, by rfl⟩ : syracuseStep 647015 = 970523) B970523
theorem B647279 : Blo 646304 647279 := bstep (se 1 (by rfl) ⟨485459, by rfl⟩ : syracuseStep 647279 = 970919) B970919
theorem B647807 : Blo 646304 647807 := bstep (se 1 (by rfl) ⟨485855, by rfl⟩ : syracuseStep 647807 = 971711) B971711
theorem B3334783 : Blo 646304 3334783 := bstep (se 1 (by rfl) ⟨2501087, by rfl⟩ : syracuseStep 3334783 = 5002175) B5002175
theorem B648431 : Blo 646304 648431 := bstep (se 1 (by rfl) ⟨486323, by rfl⟩ : syracuseStep 648431 = 972647) B972647
theorem B4220363 : Blo 646304 4220363 := bstep (se 1 (by rfl) ⟨3165272, by rfl⟩ : syracuseStep 4220363 = 6330545) B6330545
theorem B649307 : Blo 646304 649307 := bstep (se 1 (by rfl) ⟨486980, by rfl⟩ : syracuseStep 649307 = 973961) B973961
theorem B649535 : Blo 646304 649535 := bstep (se 1 (by rfl) ⟨487151, by rfl⟩ : syracuseStep 649535 = 974303) B974303
theorem B650175 : Blo 646304 650175 := bstep (se 1 (by rfl) ⟨487631, by rfl⟩ : syracuseStep 650175 = 975263) B975263
theorem B4910543 : Blo 646304 4910543 := bstep (se 1 (by rfl) ⟨3682907, by rfl⟩ : syracuseStep 4910543 = 7365815) B7365815
theorem B3700039 : Blo 646304 3700039 := bstep (se 1 (by rfl) ⟨2775029, by rfl⟩ : syracuseStep 3700039 = 5550059) B5550059
theorem B4978529 : Blo 646304 4978529 := bstep (se 2 (by rfl) ⟨1866948, by rfl⟩ : syracuseStep 4978529 = 3733897) B3733897
theorem B16612451 : Blo 646304 16612451 := bstep (se 1 (by rfl) ⟨12459338, by rfl⟩ : syracuseStep 16612451 = 24918677) B24918677
theorem B1999579 : Blo 646304 1999579 := bstep (se 1 (by rfl) ⟨1499684, by rfl⟩ : syracuseStep 1999579 = 2999369) B2999369
theorem B1643935 : Blo 646304 1643935 := bstep (se 1 (by rfl) ⟨1232951, by rfl⟩ : syracuseStep 1643935 = 2465903) B2465903
theorem B16586207 : Blo 646304 16586207 := bstep (se 1 (by rfl) ⟨12439655, by rfl⟩ : syracuseStep 16586207 = 24879311) B24879311
theorem B1316407 : Blo 646304 1316407 := bstep (se 1 (by rfl) ⟨987305, by rfl⟩ : syracuseStep 1316407 = 1974611) B1974611
theorem B1644239 : Blo 646304 1644239 := bstep (se 1 (by rfl) ⟨1233179, by rfl⟩ : syracuseStep 1644239 = 2466359) B2466359
theorem B924139 : Blo 646304 924139 := bstep (se 1 (by rfl) ⟨693104, by rfl⟩ : syracuseStep 924139 = 1386209) B1386209
theorem B1645879 : Blo 646304 1645879 := bstep (se 1 (by rfl) ⟨1234409, by rfl⟩ : syracuseStep 1645879 = 2468819) B2468819
theorem B729247 : Blo 646304 729247 := bstep (se 1 (by rfl) ⟨546935, by rfl⟩ : syracuseStep 729247 = 1093871) B1093871
theorem B3319019 : Blo 646304 3319019 := bstep (se 1 (by rfl) ⟨2489264, by rfl⟩ : syracuseStep 3319019 = 4978529) B4978529
theorem B2632283 : Blo 646304 2632283 := bstep (se 1 (by rfl) ⟨1974212, by rfl⟩ : syracuseStep 2632283 = 3948425) B3948425
theorem B1747901 : Blo 646304 1747901 := bstep (se 3 (by rfl) ⟨327731, by rfl⟩ : syracuseStep 1747901 = 655463) B655463
theorem B18919007 : Blo 646304 18919007 := bstep (se 1 (by rfl) ⟨14189255, by rfl⟩ : syracuseStep 18919007 = 28378511) B28378511
theorem B1454831 : Blo 646304 1454831 := bstep (se 1 (by rfl) ⟨1091123, by rfl⟩ : syracuseStep 1454831 = 2182247) B2182247
theorem B56931619 : Blo 646304 56931619 := bstep (se 1 (by rfl) ⟨42698714, by rfl⟩ : syracuseStep 56931619 = 85397429) B85397429
theorem B1455551 : Blo 646304 1455551 := bstep (se 1 (by rfl) ⟨1091663, by rfl⟩ : syracuseStep 1455551 = 2183327) B2183327
theorem B11254301 : Blo 646304 11254301 := bstep (se 3 (by rfl) ⟨2110181, by rfl⟩ : syracuseStep 11254301 = 4220363) B4220363
theorem B63224873 : Blo 646304 63224873 := bstep (se 2 (by rfl) ⟨23709327, by rfl⟩ : syracuseStep 63224873 = 47418655) B47418655
theorem B39861719 : Blo 646304 39861719 := bstep (se 1 (by rfl) ⟨29896289, by rfl⟩ : syracuseStep 39861719 = 59792579) B59792579
theorem B4933385 : Blo 646304 4933385 := bstep (se 2 (by rfl) ⟨1850019, by rfl⟩ : syracuseStep 4933385 = 3700039) B3700039
theorem B970409 : Blo 646304 970409 := bstep (se 2 (by rfl) ⟨363903, by rfl⟩ : syracuseStep 970409 = 727807) B727807
theorem B1462265 : Blo 646304 1462265 := bstep (se 2 (by rfl) ⟨548349, by rfl⟩ : syracuseStep 1462265 = 1096699) B1096699
theorem B971807 : Blo 646304 971807 := bstep (se 1 (by rfl) ⟨728855, by rfl⟩ : syracuseStep 971807 = 1457711) B1457711
theorem B972059 : Blo 646304 972059 := bstep (se 1 (by rfl) ⟨729044, by rfl⟩ : syracuseStep 972059 = 1458089) B1458089
theorem B972335 : Blo 646304 972335 := bstep (se 1 (by rfl) ⟨729251, by rfl⟩ : syracuseStep 972335 = 1458503) B1458503
theorem B972863 : Blo 646304 972863 := bstep (se 1 (by rfl) ⟨729647, by rfl⟩ : syracuseStep 972863 = 1459295) B1459295
theorem B4446377 : Blo 646304 4446377 := bstep (se 2 (by rfl) ⟨1667391, by rfl⟩ : syracuseStep 4446377 = 3334783) B3334783
theorem B5528189 : Blo 646304 5528189 := bstep (se 3 (by rfl) ⟨1036535, by rfl⟩ : syracuseStep 5528189 = 2073071) B2073071
theorem B2186081 : Blo 646304 2186081 := bstep (se 2 (by rfl) ⟨819780, by rfl⟩ : syracuseStep 2186081 = 1639561) B1639561
theorem B18701927 : Blo 646304 18701927 := bstep (se 1 (by rfl) ⟨14026445, by rfl⟩ : syracuseStep 18701927 = 28052891) B28052891
theorem B646815 : Blo 646304 646815 := bstep (se 1 (by rfl) ⟨485111, by rfl⟩ : syracuseStep 646815 = 970223) B970223
theorem B12476105 : Blo 646304 12476105 := bstep (se 2 (by rfl) ⟨4678539, by rfl⟩ : syracuseStep 12476105 = 9357079) B9357079
theorem B646907 : Blo 646304 646907 := bstep (se 1 (by rfl) ⟨485180, by rfl⟩ : syracuseStep 646907 = 970361) B970361
theorem B975017 : Blo 646304 975017 := bstep (se 2 (by rfl) ⟨365631, by rfl⟩ : syracuseStep 975017 = 731263) B731263
theorem B647935 : Blo 646304 647935 := bstep (se 1 (by rfl) ⟨485951, by rfl⟩ : syracuseStep 647935 = 971903) B971903
theorem B3335423 : Blo 646304 3335423 := bstep (se 1 (by rfl) ⟨2501567, by rfl⟩ : syracuseStep 3335423 = 5003135) B5003135
theorem B648475 : Blo 646304 648475 := bstep (se 1 (by rfl) ⟨486356, by rfl⟩ : syracuseStep 648475 = 972713) B972713
theorem B109536715 : Blo 646304 109536715 := bstep (se 1 (by rfl) ⟨82152536, by rfl⟩ : syracuseStep 109536715 = 164305073) B164305073
theorem B3698399 : Blo 646304 3698399 := bstep (se 1 (by rfl) ⟨2773799, by rfl⟩ : syracuseStep 3698399 = 5547599) B5547599
theorem B3273695 : Blo 646304 3273695 := bstep (se 1 (by rfl) ⟨2455271, by rfl⟩ : syracuseStep 3273695 = 4910543) B4910543
theorem B11074967 : Blo 646304 11074967 := bstep (se 1 (by rfl) ⟨8306225, by rfl⟩ : syracuseStep 11074967 = 16612451) B16612451
theorem B3702455 : Blo 646304 3702455 := bstep (se 1 (by rfl) ⟨2776841, by rfl⟩ : syracuseStep 3702455 = 5553683) B5553683
theorem B146048953 : Blo 646304 146048953 := bstep (se 2 (by rfl) ⟨54768357, by rfl⟩ : syracuseStep 146048953 = 109536715) B109536715
theorem B2465599 : Blo 646304 2465599 := bstep (se 1 (by rfl) ⟨1849199, by rfl⟩ : syracuseStep 2465599 = 3698399) B3698399
theorem B42149915 : Blo 646304 42149915 := bstep (se 1 (by rfl) ⟨31612436, by rfl⟩ : syracuseStep 42149915 = 63224873) B63224873
theorem B7383311 : Blo 646304 7383311 := bstep (se 1 (by rfl) ⟨5537483, by rfl⟩ : syracuseStep 7383311 = 11074967) B11074967
theorem B2468303 : Blo 646304 2468303 := bstep (se 1 (by rfl) ⟨1851227, by rfl⟩ : syracuseStep 2468303 = 3702455) B3702455
theorem B2666105 : Blo 646304 2666105 := bstep (se 2 (by rfl) ⟨999789, by rfl⟩ : syracuseStep 2666105 = 1999579) B1999579
theorem B3288923 : Blo 646304 3288923 := bstep (se 1 (by rfl) ⟨2466692, by rfl⟩ : syracuseStep 3288923 = 4933385) B4933385
theorem B8894461 : Blo 646304 8894461 := bstep (se 3 (by rfl) ⟨1667711, by rfl⟩ : syracuseStep 8894461 = 3335423) B3335423
theorem B11057471 : Blo 646304 11057471 := bstep (se 1 (by rfl) ⟨8293103, by rfl⟩ : syracuseStep 11057471 = 16586207) B16586207
theorem B1096159 : Blo 646304 1096159 := bstep (se 1 (by rfl) ⟨822119, by rfl⟩ : syracuseStep 1096159 = 1644239) B1644239
theorem B2964251 : Blo 646304 2964251 := bstep (se 1 (by rfl) ⟨2223188, by rfl⟩ : syracuseStep 2964251 = 4446377) B4446377
theorem B3685459 : Blo 646304 3685459 := bstep (se 1 (by rfl) ⟨2764094, by rfl⟩ : syracuseStep 3685459 = 5528189) B5528189
theorem B1457387 : Blo 646304 1457387 := bstep (se 1 (by rfl) ⟨1093040, by rfl⟩ : syracuseStep 1457387 = 2186081) B2186081
theorem B12467951 : Blo 646304 12467951 := bstep (se 1 (by rfl) ⟨9350963, by rfl⟩ : syracuseStep 12467951 = 18701927) B18701927
theorem B2212679 : Blo 646304 2212679 := bstep (se 1 (by rfl) ⟨1659509, by rfl⟩ : syracuseStep 2212679 = 3319019) B3319019
theorem B75908825 : Blo 646304 75908825 := bstep (se 2 (by rfl) ⟨28465809, by rfl⟩ : syracuseStep 75908825 = 56931619) B56931619
theorem B1754855 : Blo 646304 1754855 := bstep (se 1 (by rfl) ⟨1316141, by rfl⟩ : syracuseStep 1754855 = 2632283) B2632283
theorem B1165267 : Blo 646304 1165267 := bstep (se 1 (by rfl) ⟨873950, by rfl⟩ : syracuseStep 1165267 = 1747901) B1747901
theorem B1755209 : Blo 646304 1755209 := bstep (se 2 (by rfl) ⟨658203, by rfl⟩ : syracuseStep 1755209 = 1316407) B1316407
theorem B969887 : Blo 646304 969887 := bstep (se 1 (by rfl) ⟨727415, by rfl⟩ : syracuseStep 969887 = 1454831) B1454831
theorem B1232185 : Blo 646304 1232185 := bstep (se 2 (by rfl) ⟨462069, by rfl⟩ : syracuseStep 1232185 = 924139) B924139
theorem B2182463 : Blo 646304 2182463 := bstep (se 1 (by rfl) ⟨1636847, by rfl⟩ : syracuseStep 2182463 = 3273695) B3273695
theorem B970367 : Blo 646304 970367 := bstep (se 1 (by rfl) ⟨727775, by rfl⟩ : syracuseStep 970367 = 1455551) B1455551
theorem B972329 : Blo 646304 972329 := bstep (se 2 (by rfl) ⟨364623, by rfl⟩ : syracuseStep 972329 = 729247) B729247
theorem B646939 : Blo 646304 646939 := bstep (se 1 (by rfl) ⟨485204, by rfl⟩ : syracuseStep 646939 = 970409) B970409
theorem B974843 : Blo 646304 974843 := bstep (se 1 (by rfl) ⟨731132, by rfl⟩ : syracuseStep 974843 = 1462265) B1462265
theorem B647871 : Blo 646304 647871 := bstep (se 1 (by rfl) ⟨485903, by rfl⟩ : syracuseStep 647871 = 971807) B971807
theorem B648039 : Blo 646304 648039 := bstep (se 1 (by rfl) ⟨486029, by rfl⟩ : syracuseStep 648039 = 972059) B972059
theorem B648223 : Blo 646304 648223 := bstep (se 1 (by rfl) ⟨486167, by rfl⟩ : syracuseStep 648223 = 972335) B972335
theorem B648575 : Blo 646304 648575 := bstep (se 1 (by rfl) ⟨486431, by rfl⟩ : syracuseStep 648575 = 972863) B972863
theorem B8317403 : Blo 646304 8317403 := bstep (se 1 (by rfl) ⟨6238052, by rfl⟩ : syracuseStep 8317403 = 12476105) B12476105
theorem B650011 : Blo 646304 650011 := bstep (se 1 (by rfl) ⟨487508, by rfl⟩ : syracuseStep 650011 = 975017) B975017
theorem B2191913 : Blo 646304 2191913 := bstep (se 2 (by rfl) ⟨821967, by rfl⟩ : syracuseStep 2191913 = 1643935) B1643935
theorem B12612671 : Blo 646304 12612671 := bstep (se 1 (by rfl) ⟨9459503, by rfl⟩ : syracuseStep 12612671 = 18919007) B18919007
theorem B7502867 : Blo 646304 7502867 := bstep (se 1 (by rfl) ⟨5627150, by rfl⟩ : syracuseStep 7502867 = 11254301) B11254301
theorem B2194505 : Blo 646304 2194505 := bstep (se 2 (by rfl) ⟨822939, by rfl⟩ : syracuseStep 2194505 = 1645879) B1645879
theorem B26574479 : Blo 646304 26574479 := bstep (se 1 (by rfl) ⟨19930859, by rfl⟩ : syracuseStep 26574479 = 39861719) B39861719
theorem B1475119 : Blo 646304 1475119 := bstep (se 1 (by rfl) ⟨1106339, by rfl⟩ : syracuseStep 1475119 = 2212679) B2212679
theorem B1642913 : Blo 646304 1642913 := bstep (se 2 (by rfl) ⟨616092, by rfl⟩ : syracuseStep 1642913 = 1232185) B1232185
theorem B4922207 : Blo 646304 4922207 := bstep (se 1 (by rfl) ⟨3691655, by rfl⟩ : syracuseStep 4922207 = 7383311) B7383311
theorem B1645535 : Blo 646304 1645535 := bstep (se 1 (by rfl) ⟨1234151, by rfl⟩ : syracuseStep 1645535 = 2468303) B2468303
theorem B5544935 : Blo 646304 5544935 := bstep (se 1 (by rfl) ⟨4158701, by rfl⟩ : syracuseStep 5544935 = 8317403) B8317403
theorem B1777403 : Blo 646304 1777403 := bstep (se 1 (by rfl) ⟨1333052, by rfl⟩ : syracuseStep 1777403 = 2666105) B2666105
theorem B1976167 : Blo 646304 1976167 := bstep (se 1 (by rfl) ⟨1482125, by rfl⟩ : syracuseStep 1976167 = 2964251) B2964251
theorem B3287465 : Blo 646304 3287465 := bstep (se 2 (by rfl) ⟨1232799, by rfl⟩ : syracuseStep 3287465 = 2465599) B2465599
theorem B50605883 : Blo 646304 50605883 := bstep (se 1 (by rfl) ⟨37954412, by rfl⟩ : syracuseStep 50605883 = 75908825) B75908825
theorem B1454975 : Blo 646304 1454975 := bstep (se 1 (by rfl) ⟨1091231, by rfl⟩ : syracuseStep 1454975 = 2182463) B2182463
theorem B1553689 : Blo 646304 1553689 := bstep (se 2 (by rfl) ⟨582633, by rfl⟩ : syracuseStep 1553689 = 1165267) B1165267
theorem B28099943 : Blo 646304 28099943 := bstep (se 1 (by rfl) ⟨21074957, by rfl⟩ : syracuseStep 28099943 = 42149915) B42149915
theorem B1461275 : Blo 646304 1461275 := bstep (se 1 (by rfl) ⟨1095956, by rfl⟩ : syracuseStep 1461275 = 2191913) B2191913
theorem B1461545 : Blo 646304 1461545 := bstep (se 2 (by rfl) ⟨548079, by rfl⟩ : syracuseStep 1461545 = 1096159) B1096159
theorem B8408447 : Blo 646304 8408447 := bstep (se 1 (by rfl) ⟨6306335, by rfl⟩ : syracuseStep 8408447 = 12612671) B12612671
theorem B5001911 : Blo 646304 5001911 := bstep (se 1 (by rfl) ⟨3751433, by rfl⟩ : syracuseStep 5001911 = 7502867) B7502867
theorem B1463003 : Blo 646304 1463003 := bstep (se 1 (by rfl) ⟨1097252, by rfl⟩ : syracuseStep 1463003 = 2194505) B2194505
theorem B971591 : Blo 646304 971591 := bstep (se 1 (by rfl) ⟨728693, by rfl⟩ : syracuseStep 971591 = 1457387) B1457387
theorem B17716319 : Blo 646304 17716319 := bstep (se 1 (by rfl) ⟨13287239, by rfl⟩ : syracuseStep 17716319 = 26574479) B26574479
theorem B8311967 : Blo 646304 8311967 := bstep (se 1 (by rfl) ⟨6233975, by rfl⟩ : syracuseStep 8311967 = 12467951) B12467951
theorem B1169903 : Blo 646304 1169903 := bstep (se 1 (by rfl) ⟨877427, by rfl⟩ : syracuseStep 1169903 = 1754855) B1754855
theorem B646591 : Blo 646304 646591 := bstep (se 1 (by rfl) ⟨484943, by rfl⟩ : syracuseStep 646591 = 969887) B969887
theorem B646911 : Blo 646304 646911 := bstep (se 1 (by rfl) ⟨485183, by rfl⟩ : syracuseStep 646911 = 970367) B970367
theorem B194731937 : Blo 646304 194731937 := bstep (se 2 (by rfl) ⟨73024476, by rfl⟩ : syracuseStep 194731937 = 146048953) B146048953
theorem B648219 : Blo 646304 648219 := bstep (se 1 (by rfl) ⟨486164, by rfl⟩ : syracuseStep 648219 = 972329) B972329
theorem B649895 : Blo 646304 649895 := bstep (se 1 (by rfl) ⟨487421, by rfl⟩ : syracuseStep 649895 = 974843) B974843
theorem B4680557 : Blo 646304 4680557 := bstep (se 3 (by rfl) ⟨877604, by rfl⟩ : syracuseStep 4680557 = 1755209) B1755209
theorem B2192615 : Blo 646304 2192615 := bstep (se 1 (by rfl) ⟨1644461, by rfl⟩ : syracuseStep 2192615 = 3288923) B3288923
theorem B11859281 : Blo 646304 11859281 := bstep (se 2 (by rfl) ⟨4447230, by rfl⟩ : syracuseStep 11859281 = 8894461) B8894461
theorem B4913945 : Blo 646304 4913945 := bstep (se 2 (by rfl) ⟨1842729, by rfl⟩ : syracuseStep 4913945 = 3685459) B3685459
theorem B7371647 : Blo 646304 7371647 := bstep (se 1 (by rfl) ⟨5528735, by rfl⟩ : syracuseStep 7371647 = 11057471) B11057471
theorem B1966825 : Blo 646304 1966825 := bstep (se 2 (by rfl) ⟨737559, by rfl⟩ : syracuseStep 1966825 = 1475119) B1475119
theorem B5605631 : Blo 646304 5605631 := bstep (se 1 (by rfl) ⟨4204223, by rfl⟩ : syracuseStep 5605631 = 8408447) B8408447
theorem B5541311 : Blo 646304 5541311 := bstep (se 1 (by rfl) ⟨4155983, by rfl⟩ : syracuseStep 5541311 = 8311967) B8311967
theorem B3281471 : Blo 646304 3281471 := bstep (se 1 (by rfl) ⟨2461103, by rfl⟩ : syracuseStep 3281471 = 4922207) B4922207
theorem B3119741 : Blo 646304 3119741 := bstep (se 3 (by rfl) ⟨584951, by rfl⟩ : syracuseStep 3119741 = 1169903) B1169903
theorem B2071585 : Blo 646304 2071585 := bstep (se 2 (by rfl) ⟨776844, by rfl⟩ : syracuseStep 2071585 = 1553689) B1553689
theorem B3120371 : Blo 646304 3120371 := bstep (se 1 (by rfl) ⟨2340278, by rfl⟩ : syracuseStep 3120371 = 4680557) B4680557
theorem B7906187 : Blo 646304 7906187 := bstep (se 1 (by rfl) ⟨5929640, by rfl⟩ : syracuseStep 7906187 = 11859281) B11859281
theorem B1095275 : Blo 646304 1095275 := bstep (se 1 (by rfl) ⟨821456, by rfl⟩ : syracuseStep 1095275 = 1642913) B1642913
theorem B11810879 : Blo 646304 11810879 := bstep (se 1 (by rfl) ⟨8858159, by rfl⟩ : syracuseStep 11810879 = 17716319) B17716319
theorem B1097023 : Blo 646304 1097023 := bstep (se 1 (by rfl) ⟨822767, by rfl⟩ : syracuseStep 1097023 = 1645535) B1645535
theorem B33737255 : Blo 646304 33737255 := bstep (se 1 (by rfl) ⟨25302941, by rfl⟩ : syracuseStep 33737255 = 50605883) B50605883
theorem B969983 : Blo 646304 969983 := bstep (se 1 (by rfl) ⟨727487, by rfl⟩ : syracuseStep 969983 = 1454975) B1454975
theorem B1461743 : Blo 646304 1461743 := bstep (se 1 (by rfl) ⟨1096307, by rfl⟩ : syracuseStep 1461743 = 2192615) B2192615
theorem B10539557 : Blo 646304 10539557 := bstep (se 4 (by rfl) ⟨988083, by rfl⟩ : syracuseStep 10539557 = 1976167) B1976167
theorem B4739741 : Blo 646304 4739741 := bstep (se 3 (by rfl) ⟨888701, by rfl⟩ : syracuseStep 4739741 = 1777403) B1777403
theorem B18733295 : Blo 646304 18733295 := bstep (se 1 (by rfl) ⟨14049971, by rfl⟩ : syracuseStep 18733295 = 28099943) B28099943
theorem B974183 : Blo 646304 974183 := bstep (se 1 (by rfl) ⟨730637, by rfl⟩ : syracuseStep 974183 = 1461275) B1461275
theorem B974363 : Blo 646304 974363 := bstep (se 1 (by rfl) ⟨730772, by rfl⟩ : syracuseStep 974363 = 1461545) B1461545
theorem B3334607 : Blo 646304 3334607 := bstep (se 1 (by rfl) ⟨2500955, by rfl⟩ : syracuseStep 3334607 = 5001911) B5001911
theorem B975335 : Blo 646304 975335 := bstep (se 1 (by rfl) ⟨731501, by rfl⟩ : syracuseStep 975335 = 1463003) B1463003
theorem B647727 : Blo 646304 647727 := bstep (se 1 (by rfl) ⟨485795, by rfl⟩ : syracuseStep 647727 = 971591) B971591
theorem B3696623 : Blo 646304 3696623 := bstep (se 1 (by rfl) ⟨2772467, by rfl⟩ : syracuseStep 3696623 = 5544935) B5544935
theorem B129821291 : Blo 646304 129821291 := bstep (se 1 (by rfl) ⟨97365968, by rfl⟩ : syracuseStep 129821291 = 194731937) B194731937
theorem B2191643 : Blo 646304 2191643 := bstep (se 1 (by rfl) ⟨1643732, by rfl⟩ : syracuseStep 2191643 = 3287465) B3287465
theorem B3275963 : Blo 646304 3275963 := bstep (se 1 (by rfl) ⟨2456972, by rfl⟩ : syracuseStep 3275963 = 4913945) B4913945
theorem B4914431 : Blo 646304 4914431 := bstep (se 1 (by rfl) ⟨3685823, by rfl⟩ : syracuseStep 4914431 = 7371647) B7371647
theorem B3737087 : Blo 646304 3737087 := bstep (se 1 (by rfl) ⟨2802815, by rfl⟩ : syracuseStep 3737087 = 5605631) B5605631
theorem B10489733 : Blo 646304 10489733 := bstep (se 4 (by rfl) ⟨983412, by rfl⟩ : syracuseStep 10489733 = 1966825) B1966825
theorem B12488863 : Blo 646304 12488863 := bstep (se 1 (by rfl) ⟨9366647, by rfl⟩ : syracuseStep 12488863 = 18733295) B18733295
theorem B2464415 : Blo 646304 2464415 := bstep (se 1 (by rfl) ⟨1848311, by rfl⟩ : syracuseStep 2464415 = 3696623) B3696623
theorem B86547527 : Blo 646304 86547527 := bstep (se 1 (by rfl) ⟨64910645, by rfl⟩ : syracuseStep 86547527 = 129821291) B129821291
theorem B730183 : Blo 646304 730183 := bstep (se 1 (by rfl) ⟨547637, by rfl⟩ : syracuseStep 730183 = 1095275) B1095275
theorem B7873919 : Blo 646304 7873919 := bstep (se 1 (by rfl) ⟨5905439, by rfl⟩ : syracuseStep 7873919 = 11810879) B11810879
theorem B2762113 : Blo 646304 2762113 := bstep (se 2 (by rfl) ⟨1035792, by rfl⟩ : syracuseStep 2762113 = 2071585) B2071585
theorem B22491503 : Blo 646304 22491503 := bstep (se 1 (by rfl) ⟨16868627, by rfl⟩ : syracuseStep 22491503 = 33737255) B33737255
theorem B7026371 : Blo 646304 7026371 := bstep (se 1 (by rfl) ⟨5269778, by rfl⟩ : syracuseStep 7026371 = 10539557) B10539557
theorem B3159827 : Blo 646304 3159827 := bstep (se 1 (by rfl) ⟨2369870, by rfl⟩ : syracuseStep 3159827 = 4739741) B4739741
theorem B2079827 : Blo 646304 2079827 := bstep (se 1 (by rfl) ⟨1559870, by rfl⟩ : syracuseStep 2079827 = 3119741) B3119741
theorem B2080247 : Blo 646304 2080247 := bstep (se 1 (by rfl) ⟨1560185, by rfl⟩ : syracuseStep 2080247 = 3120371) B3120371
theorem B1461095 : Blo 646304 1461095 := bstep (se 1 (by rfl) ⟨1095821, by rfl⟩ : syracuseStep 1461095 = 2191643) B2191643
theorem B1462697 : Blo 646304 1462697 := bstep (se 2 (by rfl) ⟨548511, by rfl⟩ : syracuseStep 1462697 = 1097023) B1097023
theorem B2183975 : Blo 646304 2183975 := bstep (se 1 (by rfl) ⟨1637981, by rfl⟩ : syracuseStep 2183975 = 3275963) B3275963
theorem B646655 : Blo 646304 646655 := bstep (se 1 (by rfl) ⟨484991, by rfl⟩ : syracuseStep 646655 = 969983) B969983
theorem B3694207 : Blo 646304 3694207 := bstep (se 1 (by rfl) ⟨2770655, by rfl⟩ : syracuseStep 3694207 = 5541311) B5541311
theorem B974495 : Blo 646304 974495 := bstep (se 1 (by rfl) ⟨730871, by rfl⟩ : syracuseStep 974495 = 1461743) B1461743
theorem B2187647 : Blo 646304 2187647 := bstep (se 1 (by rfl) ⟨1640735, by rfl⟩ : syracuseStep 2187647 = 3281471) B3281471
theorem B649455 : Blo 646304 649455 := bstep (se 1 (by rfl) ⟨487091, by rfl⟩ : syracuseStep 649455 = 974183) B974183
theorem B649575 : Blo 646304 649575 := bstep (se 1 (by rfl) ⟨487181, by rfl⟩ : syracuseStep 649575 = 974363) B974363
theorem B2223071 : Blo 646304 2223071 := bstep (se 1 (by rfl) ⟨1667303, by rfl⟩ : syracuseStep 2223071 = 3334607) B3334607
theorem B650223 : Blo 646304 650223 := bstep (se 1 (by rfl) ⟨487667, by rfl⟩ : syracuseStep 650223 = 975335) B975335
theorem B5270791 : Blo 646304 5270791 := bstep (se 1 (by rfl) ⟨3953093, by rfl⟩ : syracuseStep 5270791 = 7906187) B7906187
theorem B3276287 : Blo 646304 3276287 := bstep (se 1 (by rfl) ⟨2457215, by rfl⟩ : syracuseStep 3276287 = 4914431) B4914431
theorem B2491391 : Blo 646304 2491391 := bstep (se 1 (by rfl) ⟨1868543, by rfl⟩ : syracuseStep 2491391 = 3737087) B3737087
theorem B1642943 : Blo 646304 1642943 := bstep (se 1 (by rfl) ⟨1232207, by rfl⟩ : syracuseStep 1642943 = 2464415) B2464415
theorem B16651817 : Blo 646304 16651817 := bstep (se 2 (by rfl) ⟨6244431, by rfl⟩ : syracuseStep 16651817 = 12488863) B12488863
theorem B5249279 : Blo 646304 5249279 := bstep (se 1 (by rfl) ⟨3936959, by rfl⟩ : syracuseStep 5249279 = 7873919) B7873919
theorem B1482047 : Blo 646304 1482047 := bstep (se 1 (by rfl) ⟨1111535, by rfl⟩ : syracuseStep 1482047 = 2223071) B2223071
theorem B2106551 : Blo 646304 2106551 := bstep (se 1 (by rfl) ⟨1579913, by rfl⟩ : syracuseStep 2106551 = 3159827) B3159827
theorem B5547325 : Blo 646304 5547325 := bstep (se 3 (by rfl) ⟨1040123, by rfl⟩ : syracuseStep 5547325 = 2080247) B2080247
theorem B1386551 : Blo 646304 1386551 := bstep (se 1 (by rfl) ⟨1039913, by rfl⟩ : syracuseStep 1386551 = 2079827) B2079827
theorem B4925609 : Blo 646304 4925609 := bstep (se 2 (by rfl) ⟨1847103, by rfl⟩ : syracuseStep 4925609 = 3694207) B3694207
theorem B3682817 : Blo 646304 3682817 := bstep (se 2 (by rfl) ⟨1381056, by rfl⟩ : syracuseStep 3682817 = 2762113) B2762113
theorem B6993155 : Blo 646304 6993155 := bstep (se 1 (by rfl) ⟨5244866, by rfl⟩ : syracuseStep 6993155 = 10489733) B10489733
theorem B1455983 : Blo 646304 1455983 := bstep (se 1 (by rfl) ⟨1091987, by rfl⟩ : syracuseStep 1455983 = 2183975) B2183975
theorem B7027721 : Blo 646304 7027721 := bstep (se 2 (by rfl) ⟨2635395, by rfl⟩ : syracuseStep 7027721 = 5270791) B5270791
theorem B1458431 : Blo 646304 1458431 := bstep (se 1 (by rfl) ⟨1093823, by rfl⟩ : syracuseStep 1458431 = 2187647) B2187647
theorem B14994335 : Blo 646304 14994335 := bstep (se 1 (by rfl) ⟨11245751, by rfl⟩ : syracuseStep 14994335 = 22491503) B22491503
theorem B2184191 : Blo 646304 2184191 := bstep (se 1 (by rfl) ⟨1638143, by rfl⟩ : syracuseStep 2184191 = 3276287) B3276287
theorem B973577 : Blo 646304 973577 := bstep (se 2 (by rfl) ⟨365091, by rfl⟩ : syracuseStep 973577 = 730183) B730183
theorem B974063 : Blo 646304 974063 := bstep (se 1 (by rfl) ⟨730547, by rfl⟩ : syracuseStep 974063 = 1461095) B1461095
theorem B975131 : Blo 646304 975131 := bstep (se 1 (by rfl) ⟨731348, by rfl⟩ : syracuseStep 975131 = 1462697) B1462697
theorem B57698351 : Blo 646304 57698351 := bstep (se 1 (by rfl) ⟨43273763, by rfl⟩ : syracuseStep 57698351 = 86547527) B86547527
theorem B649663 : Blo 646304 649663 := bstep (se 1 (by rfl) ⟨487247, by rfl⟩ : syracuseStep 649663 = 974495) B974495
theorem B4684247 : Blo 646304 4684247 := bstep (se 1 (by rfl) ⟨3513185, by rfl⟩ : syracuseStep 4684247 = 7026371) B7026371
theorem B9996223 : Blo 646304 9996223 := bstep (se 1 (by rfl) ⟨7497167, by rfl⟩ : syracuseStep 9996223 = 14994335) B14994335
theorem B18648413 : Blo 646304 18648413 := bstep (se 3 (by rfl) ⟨3496577, by rfl⟩ : syracuseStep 18648413 = 6993155) B6993155
theorem B988031 : Blo 646304 988031 := bstep (se 1 (by rfl) ⟨741023, by rfl⟩ : syracuseStep 988031 = 1482047) B1482047
theorem B924367 : Blo 646304 924367 := bstep (se 1 (by rfl) ⟨693275, by rfl⟩ : syracuseStep 924367 = 1386551) B1386551
theorem B3283739 : Blo 646304 3283739 := bstep (se 1 (by rfl) ⟨2462804, by rfl⟩ : syracuseStep 3283739 = 4925609) B4925609
theorem B3122831 : Blo 646304 3122831 := bstep (se 1 (by rfl) ⟨2342123, by rfl⟩ : syracuseStep 3122831 = 4684247) B4684247
theorem B1095295 : Blo 646304 1095295 := bstep (se 1 (by rfl) ⟨821471, by rfl⟩ : syracuseStep 1095295 = 1642943) B1642943
theorem B5617469 : Blo 646304 5617469 := bstep (se 3 (by rfl) ⟨1053275, by rfl⟩ : syracuseStep 5617469 = 2106551) B2106551
theorem B1456127 : Blo 646304 1456127 := bstep (se 1 (by rfl) ⟨1092095, by rfl⟩ : syracuseStep 1456127 = 2184191) B2184191
theorem B970655 : Blo 646304 970655 := bstep (se 1 (by rfl) ⟨727991, by rfl⟩ : syracuseStep 970655 = 1455983) B1455983
theorem B972287 : Blo 646304 972287 := bstep (se 1 (by rfl) ⟨729215, by rfl⟩ : syracuseStep 972287 = 1458431) B1458431
theorem B1660927 : Blo 646304 1660927 := bstep (se 1 (by rfl) ⟨1245695, by rfl⟩ : syracuseStep 1660927 = 2491391) B2491391
theorem B7396433 : Blo 646304 7396433 := bstep (se 2 (by rfl) ⟨2773662, by rfl⟩ : syracuseStep 7396433 = 5547325) B5547325
theorem B11101211 : Blo 646304 11101211 := bstep (se 1 (by rfl) ⟨8325908, by rfl⟩ : syracuseStep 11101211 = 16651817) B16651817
theorem B3499519 : Blo 646304 3499519 := bstep (se 1 (by rfl) ⟨2624639, by rfl⟩ : syracuseStep 3499519 = 5249279) B5249279
theorem B649051 : Blo 646304 649051 := bstep (se 1 (by rfl) ⟨486788, by rfl⟩ : syracuseStep 649051 = 973577) B973577
theorem B649375 : Blo 646304 649375 := bstep (se 1 (by rfl) ⟨487031, by rfl⟩ : syracuseStep 649375 = 974063) B974063
theorem B650087 : Blo 646304 650087 := bstep (se 1 (by rfl) ⟨487565, by rfl⟩ : syracuseStep 650087 = 975131) B975131
theorem B38465567 : Blo 646304 38465567 := bstep (se 1 (by rfl) ⟨28849175, by rfl⟩ : syracuseStep 38465567 = 57698351) B57698351
theorem B2455211 : Blo 646304 2455211 := bstep (se 1 (by rfl) ⟨1841408, by rfl⟩ : syracuseStep 2455211 = 3682817) B3682817
theorem B4685147 : Blo 646304 4685147 := bstep (se 1 (by rfl) ⟨3513860, by rfl⟩ : syracuseStep 4685147 = 7027721) B7027721
theorem B658687 : Blo 646304 658687 := bstep (se 1 (by rfl) ⟨494015, by rfl⟩ : syracuseStep 658687 = 988031) B988031
theorem B8327549 : Blo 646304 8327549 := bstep (se 3 (by rfl) ⟨1561415, by rfl⟩ : syracuseStep 8327549 = 3122831) B3122831
theorem B14979917 : Blo 646304 14979917 := bstep (se 3 (by rfl) ⟨2808734, by rfl⟩ : syracuseStep 14979917 = 5617469) B5617469
theorem B3123431 : Blo 646304 3123431 := bstep (se 1 (by rfl) ⟨2342573, by rfl⟩ : syracuseStep 3123431 = 4685147) B4685147
theorem B4666025 : Blo 646304 4666025 := bstep (se 2 (by rfl) ⟨1749759, by rfl⟩ : syracuseStep 4666025 = 3499519) B3499519
theorem B12432275 : Blo 646304 12432275 := bstep (se 1 (by rfl) ⟨9324206, by rfl⟩ : syracuseStep 12432275 = 18648413) B18648413
theorem B4930955 : Blo 646304 4930955 := bstep (se 1 (by rfl) ⟨3698216, by rfl⟩ : syracuseStep 4930955 = 7396433) B7396433
theorem B1460393 : Blo 646304 1460393 := bstep (se 2 (by rfl) ⟨547647, by rfl⟩ : syracuseStep 1460393 = 1095295) B1095295
theorem B2214569 : Blo 646304 2214569 := bstep (se 2 (by rfl) ⟨830463, by rfl⟩ : syracuseStep 2214569 = 1660927) B1660927
theorem B25643711 : Blo 646304 25643711 := bstep (se 1 (by rfl) ⟨19232783, by rfl⟩ : syracuseStep 25643711 = 38465567) B38465567
theorem B1232489 : Blo 646304 1232489 := bstep (se 2 (by rfl) ⟨462183, by rfl⟩ : syracuseStep 1232489 = 924367) B924367
theorem B970751 : Blo 646304 970751 := bstep (se 1 (by rfl) ⟨728063, by rfl⟩ : syracuseStep 970751 = 1456127) B1456127
theorem B13328297 : Blo 646304 13328297 := bstep (se 2 (by rfl) ⟨4998111, by rfl⟩ : syracuseStep 13328297 = 9996223) B9996223
theorem B647103 : Blo 646304 647103 := bstep (se 1 (by rfl) ⟨485327, by rfl⟩ : syracuseStep 647103 = 970655) B970655
theorem B648191 : Blo 646304 648191 := bstep (se 1 (by rfl) ⟨486143, by rfl⟩ : syracuseStep 648191 = 972287) B972287
theorem B2189159 : Blo 646304 2189159 := bstep (se 1 (by rfl) ⟨1641869, by rfl⟩ : syracuseStep 2189159 = 3283739) B3283739
theorem B7400807 : Blo 646304 7400807 := bstep (se 1 (by rfl) ⟨5550605, by rfl⟩ : syracuseStep 7400807 = 11101211) B11101211
theorem B1636807 : Blo 646304 1636807 := bstep (se 1 (by rfl) ⟨1227605, by rfl⟩ : syracuseStep 1636807 = 2455211) B2455211
theorem B1476379 : Blo 646304 1476379 := bstep (se 1 (by rfl) ⟨1107284, by rfl⟩ : syracuseStep 1476379 = 2214569) B2214569
theorem B39946445 : Blo 646304 39946445 := bstep (se 3 (by rfl) ⟨7489958, by rfl⟩ : syracuseStep 39946445 = 14979917) B14979917
theorem B821659 : Blo 646304 821659 := bstep (se 1 (by rfl) ⟨616244, by rfl⟩ : syracuseStep 821659 = 1232489) B1232489
theorem B8885531 : Blo 646304 8885531 := bstep (se 1 (by rfl) ⟨6664148, by rfl⟩ : syracuseStep 8885531 = 13328297) B13328297
theorem B3287303 : Blo 646304 3287303 := bstep (se 1 (by rfl) ⟨2465477, by rfl⟩ : syracuseStep 3287303 = 4930955) B4930955
theorem B5551699 : Blo 646304 5551699 := bstep (se 1 (by rfl) ⟨4163774, by rfl⟩ : syracuseStep 5551699 = 8327549) B8327549
theorem B1459439 : Blo 646304 1459439 := bstep (se 1 (by rfl) ⟨1094579, by rfl⟩ : syracuseStep 1459439 = 2189159) B2189159
theorem B2082287 : Blo 646304 2082287 := bstep (se 1 (by rfl) ⟨1561715, by rfl⟩ : syracuseStep 2082287 = 3123431) B3123431
theorem B4933871 : Blo 646304 4933871 := bstep (se 1 (by rfl) ⟨3700403, by rfl⟩ : syracuseStep 4933871 = 7400807) B7400807
theorem B2182409 : Blo 646304 2182409 := bstep (se 2 (by rfl) ⟨818403, by rfl⟩ : syracuseStep 2182409 = 1636807) B1636807
theorem B973595 : Blo 646304 973595 := bstep (se 1 (by rfl) ⟨730196, by rfl⟩ : syracuseStep 973595 = 1460393) B1460393
theorem B12442733 : Blo 646304 12442733 := bstep (se 3 (by rfl) ⟨2333012, by rfl⟩ : syracuseStep 12442733 = 4666025) B4666025
theorem B17095807 : Blo 646304 17095807 := bstep (se 1 (by rfl) ⟨12821855, by rfl⟩ : syracuseStep 17095807 = 25643711) B25643711
theorem B647167 : Blo 646304 647167 := bstep (se 1 (by rfl) ⟨485375, by rfl⟩ : syracuseStep 647167 = 970751) B970751
theorem B878249 : Blo 646304 878249 := bstep (se 2 (by rfl) ⟨329343, by rfl⟩ : syracuseStep 878249 = 658687) B658687
theorem B8288183 : Blo 646304 8288183 := bstep (se 1 (by rfl) ⟨6216137, by rfl⟩ : syracuseStep 8288183 = 12432275) B12432275
theorem B1968505 : Blo 646304 1968505 := bstep (se 2 (by rfl) ⟨738189, by rfl⟩ : syracuseStep 1968505 = 1476379) B1476379
theorem B8295155 : Blo 646304 8295155 := bstep (se 1 (by rfl) ⟨6221366, by rfl⟩ : syracuseStep 8295155 = 12442733) B12442733
theorem B1388191 : Blo 646304 1388191 := bstep (se 1 (by rfl) ⟨1041143, by rfl⟩ : syracuseStep 1388191 = 2082287) B2082287
theorem B3289247 : Blo 646304 3289247 := bstep (se 1 (by rfl) ⟨2466935, by rfl⟩ : syracuseStep 3289247 = 4933871) B4933871
theorem B1454939 : Blo 646304 1454939 := bstep (se 1 (by rfl) ⟨1091204, by rfl⟩ : syracuseStep 1454939 = 2182409) B2182409
theorem B1095545 : Blo 646304 1095545 := bstep (se 2 (by rfl) ⟨410829, by rfl⟩ : syracuseStep 1095545 = 821659) B821659
theorem B2341997 : Blo 646304 2341997 := bstep (se 3 (by rfl) ⟨439124, by rfl⟩ : syracuseStep 2341997 = 878249) B878249
theorem B5525455 : Blo 646304 5525455 := bstep (se 1 (by rfl) ⟨4144091, by rfl⟩ : syracuseStep 5525455 = 8288183) B8288183
theorem B22794409 : Blo 646304 22794409 := bstep (se 2 (by rfl) ⟨8547903, by rfl⟩ : syracuseStep 22794409 = 17095807) B17095807
theorem B972959 : Blo 646304 972959 := bstep (se 1 (by rfl) ⟨729719, by rfl⟩ : syracuseStep 972959 = 1459439) B1459439
theorem B26630963 : Blo 646304 26630963 := bstep (se 1 (by rfl) ⟨19973222, by rfl⟩ : syracuseStep 26630963 = 39946445) B39946445
theorem B5923687 : Blo 646304 5923687 := bstep (se 1 (by rfl) ⟨4442765, by rfl⟩ : syracuseStep 5923687 = 8885531) B8885531
theorem B649063 : Blo 646304 649063 := bstep (se 1 (by rfl) ⟨486797, by rfl⟩ : syracuseStep 649063 = 973595) B973595
theorem B2191535 : Blo 646304 2191535 := bstep (se 1 (by rfl) ⟨1643651, by rfl⟩ : syracuseStep 2191535 = 3287303) B3287303
theorem B7402265 : Blo 646304 7402265 := bstep (se 2 (by rfl) ⟨2775849, by rfl⟩ : syracuseStep 7402265 = 5551699) B5551699
theorem B7898249 : Blo 646304 7898249 := bstep (se 2 (by rfl) ⟨2961843, by rfl⟩ : syracuseStep 7898249 = 5923687) B5923687
theorem B730363 : Blo 646304 730363 := bstep (se 1 (by rfl) ⟨547772, by rfl⟩ : syracuseStep 730363 = 1095545) B1095545
theorem B10498693 : Blo 646304 10498693 := bstep (se 4 (by rfl) ⟨984252, by rfl⟩ : syracuseStep 10498693 = 1968505) B1968505
theorem B1850921 : Blo 646304 1850921 := bstep (se 2 (by rfl) ⟨694095, by rfl⟩ : syracuseStep 1850921 = 1388191) B1388191
theorem B30392545 : Blo 646304 30392545 := bstep (se 2 (by rfl) ⟨11397204, by rfl⟩ : syracuseStep 30392545 = 22794409) B22794409
theorem B1461023 : Blo 646304 1461023 := bstep (se 1 (by rfl) ⟨1095767, by rfl⟩ : syracuseStep 1461023 = 2191535) B2191535
theorem B4934843 : Blo 646304 4934843 := bstep (se 1 (by rfl) ⟨3701132, by rfl⟩ : syracuseStep 4934843 = 7402265) B7402265
theorem B969959 : Blo 646304 969959 := bstep (se 1 (by rfl) ⟨727469, by rfl⟩ : syracuseStep 969959 = 1454939) B1454939
theorem B1561331 : Blo 646304 1561331 := bstep (se 1 (by rfl) ⟨1170998, by rfl⟩ : syracuseStep 1561331 = 2341997) B2341997
theorem B5530103 : Blo 646304 5530103 := bstep (se 1 (by rfl) ⟨4147577, by rfl⟩ : syracuseStep 5530103 = 8295155) B8295155
theorem B648639 : Blo 646304 648639 := bstep (se 1 (by rfl) ⟨486479, by rfl⟩ : syracuseStep 648639 = 972959) B972959
theorem B17753975 : Blo 646304 17753975 := bstep (se 1 (by rfl) ⟨13315481, by rfl⟩ : syracuseStep 17753975 = 26630963) B26630963
theorem B7367273 : Blo 646304 7367273 := bstep (se 2 (by rfl) ⟨2762727, by rfl⟩ : syracuseStep 7367273 = 5525455) B5525455
theorem B2192831 : Blo 646304 2192831 := bstep (se 1 (by rfl) ⟨1644623, by rfl⟩ : syracuseStep 2192831 = 3289247) B3289247
theorem B13998257 : Blo 646304 13998257 := bstep (se 2 (by rfl) ⟨5249346, by rfl⟩ : syracuseStep 13998257 = 10498693) B10498693
theorem B11835983 : Blo 646304 11835983 := bstep (se 1 (by rfl) ⟨8876987, by rfl⟩ : syracuseStep 11835983 = 17753975) B17753975
theorem B3289895 : Blo 646304 3289895 := bstep (se 1 (by rfl) ⟨2467421, by rfl⟩ : syracuseStep 3289895 = 4934843) B4934843
theorem B3686735 : Blo 646304 3686735 := bstep (se 1 (by rfl) ⟨2765051, by rfl⟩ : syracuseStep 3686735 = 5530103) B5530103
theorem B1461887 : Blo 646304 1461887 := bstep (se 1 (by rfl) ⟨1096415, by rfl⟩ : syracuseStep 1461887 = 2192831) B2192831
theorem B1233947 : Blo 646304 1233947 := bstep (se 1 (by rfl) ⟨925460, by rfl⟩ : syracuseStep 1233947 = 1850921) B1850921
theorem B40523393 : Blo 646304 40523393 := bstep (se 2 (by rfl) ⟨15196272, by rfl⟩ : syracuseStep 40523393 = 30392545) B30392545
theorem B5265499 : Blo 646304 5265499 := bstep (se 1 (by rfl) ⟨3949124, by rfl⟩ : syracuseStep 5265499 = 7898249) B7898249
theorem B973817 : Blo 646304 973817 := bstep (se 2 (by rfl) ⟨365181, by rfl⟩ : syracuseStep 973817 = 730363) B730363
theorem B974015 : Blo 646304 974015 := bstep (se 1 (by rfl) ⟨730511, by rfl⟩ : syracuseStep 974015 = 1461023) B1461023
theorem B646639 : Blo 646304 646639 := bstep (se 1 (by rfl) ⟨484979, by rfl⟩ : syracuseStep 646639 = 969959) B969959
theorem B1040887 : Blo 646304 1040887 := bstep (se 1 (by rfl) ⟨780665, by rfl⟩ : syracuseStep 1040887 = 1561331) B1561331
theorem B4911515 : Blo 646304 4911515 := bstep (se 1 (by rfl) ⟨3683636, by rfl⟩ : syracuseStep 4911515 = 7367273) B7367273
theorem B2457823 : Blo 646304 2457823 := bstep (se 1 (by rfl) ⟨1843367, by rfl⟩ : syracuseStep 2457823 = 3686735) B3686735
theorem B822631 : Blo 646304 822631 := bstep (se 1 (by rfl) ⟨616973, by rfl⟩ : syracuseStep 822631 = 1233947) B1233947
theorem B7020665 : Blo 646304 7020665 := bstep (se 2 (by rfl) ⟨2632749, by rfl⟩ : syracuseStep 7020665 = 5265499) B5265499
theorem B1387849 : Blo 646304 1387849 := bstep (se 2 (by rfl) ⟨520443, by rfl⟩ : syracuseStep 1387849 = 1040887) B1040887
theorem B974591 : Blo 646304 974591 := bstep (se 1 (by rfl) ⟨730943, by rfl⟩ : syracuseStep 974591 = 1461887) B1461887
theorem B9332171 : Blo 646304 9332171 := bstep (se 1 (by rfl) ⟨6999128, by rfl⟩ : syracuseStep 9332171 = 13998257) B13998257
theorem B108062381 : Blo 646304 108062381 := bstep (se 3 (by rfl) ⟨20261696, by rfl⟩ : syracuseStep 108062381 = 40523393) B40523393
theorem B7890655 : Blo 646304 7890655 := bstep (se 1 (by rfl) ⟨5917991, by rfl⟩ : syracuseStep 7890655 = 11835983) B11835983
theorem B649211 : Blo 646304 649211 := bstep (se 1 (by rfl) ⟨486908, by rfl⟩ : syracuseStep 649211 = 973817) B973817
theorem B649343 : Blo 646304 649343 := bstep (se 1 (by rfl) ⟨487007, by rfl⟩ : syracuseStep 649343 = 974015) B974015
theorem B3274343 : Blo 646304 3274343 := bstep (se 1 (by rfl) ⟨2455757, by rfl⟩ : syracuseStep 3274343 = 4911515) B4911515
theorem B2193263 : Blo 646304 2193263 := bstep (se 1 (by rfl) ⟨1644947, by rfl⟩ : syracuseStep 2193263 = 3289895) B3289895
theorem B3277097 : Blo 646304 3277097 := bstep (se 2 (by rfl) ⟨1228911, by rfl⟩ : syracuseStep 3277097 = 2457823) B2457823
theorem B10520873 : Blo 646304 10520873 := bstep (se 2 (by rfl) ⟨3945327, by rfl⟩ : syracuseStep 10520873 = 7890655) B7890655
theorem B288166349 : Blo 646304 288166349 := bstep (se 3 (by rfl) ⟨54031190, by rfl⟩ : syracuseStep 288166349 = 108062381) B108062381
theorem B1850465 : Blo 646304 1850465 := bstep (se 2 (by rfl) ⟨693924, by rfl⟩ : syracuseStep 1850465 = 1387849) B1387849
theorem B1096841 : Blo 646304 1096841 := bstep (se 2 (by rfl) ⟨411315, by rfl⟩ : syracuseStep 1096841 = 822631) B822631
theorem B2182895 : Blo 646304 2182895 := bstep (se 1 (by rfl) ⟨1637171, by rfl⟩ : syracuseStep 2182895 = 3274343) B3274343
theorem B1462175 : Blo 646304 1462175 := bstep (se 1 (by rfl) ⟨1096631, by rfl⟩ : syracuseStep 1462175 = 2193263) B2193263
theorem B649727 : Blo 646304 649727 := bstep (se 1 (by rfl) ⟨487295, by rfl⟩ : syracuseStep 649727 = 974591) B974591
theorem B4680443 : Blo 646304 4680443 := bstep (se 1 (by rfl) ⟨3510332, by rfl⟩ : syracuseStep 4680443 = 7020665) B7020665
theorem B6221447 : Blo 646304 6221447 := bstep (se 1 (by rfl) ⟨4666085, by rfl⟩ : syracuseStep 6221447 = 9332171) B9332171
theorem B7013915 : Blo 646304 7013915 := bstep (se 1 (by rfl) ⟨5260436, by rfl⟩ : syracuseStep 7013915 = 10520873) B10520873
theorem B3120295 : Blo 646304 3120295 := bstep (se 1 (by rfl) ⟨2340221, by rfl⟩ : syracuseStep 3120295 = 4680443) B4680443
theorem B731227 : Blo 646304 731227 := bstep (se 1 (by rfl) ⟨548420, by rfl⟩ : syracuseStep 731227 = 1096841) B1096841
theorem B1455263 : Blo 646304 1455263 := bstep (se 1 (by rfl) ⟨1091447, by rfl⟩ : syracuseStep 1455263 = 2182895) B2182895
theorem B4147631 : Blo 646304 4147631 := bstep (se 1 (by rfl) ⟨3110723, by rfl⟩ : syracuseStep 4147631 = 6221447) B6221447
theorem B1233643 : Blo 646304 1233643 := bstep (se 1 (by rfl) ⟨925232, by rfl⟩ : syracuseStep 1233643 = 1850465) B1850465
theorem B2184731 : Blo 646304 2184731 := bstep (se 1 (by rfl) ⟨1638548, by rfl⟩ : syracuseStep 2184731 = 3277097) B3277097
theorem B974783 : Blo 646304 974783 := bstep (se 1 (by rfl) ⟨731087, by rfl⟩ : syracuseStep 974783 = 1462175) B1462175
theorem B192110899 : Blo 646304 192110899 := bstep (se 1 (by rfl) ⟨144083174, by rfl⟩ : syracuseStep 192110899 = 288166349) B288166349
theorem B256147865 : Blo 646304 256147865 := bstep (se 2 (by rfl) ⟨96055449, by rfl⟩ : syracuseStep 256147865 = 192110899) B192110899
theorem B1644857 : Blo 646304 1644857 := bstep (se 2 (by rfl) ⟨616821, by rfl⟩ : syracuseStep 1644857 = 1233643) B1233643
theorem B2765087 : Blo 646304 2765087 := bstep (se 1 (by rfl) ⟨2073815, by rfl⟩ : syracuseStep 2765087 = 4147631) B4147631
theorem B1456487 : Blo 646304 1456487 := bstep (se 1 (by rfl) ⟨1092365, by rfl⟩ : syracuseStep 1456487 = 2184731) B2184731
theorem B970175 : Blo 646304 970175 := bstep (se 1 (by rfl) ⟨727631, by rfl⟩ : syracuseStep 970175 = 1455263) B1455263
theorem B4675943 : Blo 646304 4675943 := bstep (se 1 (by rfl) ⟨3506957, by rfl⟩ : syracuseStep 4675943 = 7013915) B7013915
theorem B974969 : Blo 646304 974969 := bstep (se 2 (by rfl) ⟨365613, by rfl⟩ : syracuseStep 974969 = 731227) B731227
theorem B649855 : Blo 646304 649855 := bstep (se 1 (by rfl) ⟨487391, by rfl⟩ : syracuseStep 649855 = 974783) B974783
theorem B4160393 : Blo 646304 4160393 := bstep (se 2 (by rfl) ⟨1560147, by rfl⟩ : syracuseStep 4160393 = 3120295) B3120295
theorem B3117295 : Blo 646304 3117295 := bstep (se 1 (by rfl) ⟨2337971, by rfl⟩ : syracuseStep 3117295 = 4675943) B4675943
theorem B1843391 : Blo 646304 1843391 := bstep (se 1 (by rfl) ⟨1382543, by rfl⟩ : syracuseStep 1843391 = 2765087) B2765087
theorem B170765243 : Blo 646304 170765243 := bstep (se 1 (by rfl) ⟨128073932, by rfl⟩ : syracuseStep 170765243 = 256147865) B256147865
theorem B1096571 : Blo 646304 1096571 := bstep (se 1 (by rfl) ⟨822428, by rfl⟩ : syracuseStep 1096571 = 1644857) B1644857
theorem B970991 : Blo 646304 970991 := bstep (se 1 (by rfl) ⟨728243, by rfl⟩ : syracuseStep 970991 = 1456487) B1456487
theorem B2773595 : Blo 646304 2773595 := bstep (se 1 (by rfl) ⟨2080196, by rfl⟩ : syracuseStep 2773595 = 4160393) B4160393
theorem B646783 : Blo 646304 646783 := bstep (se 1 (by rfl) ⟨485087, by rfl⟩ : syracuseStep 646783 = 970175) B970175
theorem B649979 : Blo 646304 649979 := bstep (se 1 (by rfl) ⟨487484, by rfl⟩ : syracuseStep 649979 = 974969) B974969
theorem B113843495 : Blo 646304 113843495 := bstep (se 1 (by rfl) ⟨85382621, by rfl⟩ : syracuseStep 113843495 = 170765243) B170765243
theorem B731047 : Blo 646304 731047 := bstep (se 1 (by rfl) ⟨548285, by rfl⟩ : syracuseStep 731047 = 1096571) B1096571
theorem B16625573 : Blo 646304 16625573 := bstep (se 4 (by rfl) ⟨1558647, by rfl⟩ : syracuseStep 16625573 = 3117295) B3117295
theorem B1849063 : Blo 646304 1849063 := bstep (se 1 (by rfl) ⟨1386797, by rfl⟩ : syracuseStep 1849063 = 2773595) B2773595
theorem B1228927 : Blo 646304 1228927 := bstep (se 1 (by rfl) ⟨921695, by rfl⟩ : syracuseStep 1228927 = 1843391) B1843391
theorem B647327 : Blo 646304 647327 := bstep (se 1 (by rfl) ⟨485495, by rfl⟩ : syracuseStep 647327 = 970991) B970991
theorem B1638569 : Blo 646304 1638569 := bstep (se 2 (by rfl) ⟨614463, by rfl⟩ : syracuseStep 1638569 = 1228927) B1228927
theorem B75895663 : Blo 646304 75895663 := bstep (se 1 (by rfl) ⟨56921747, by rfl⟩ : syracuseStep 75895663 = 113843495) B113843495
theorem B2465417 : Blo 646304 2465417 := bstep (se 2 (by rfl) ⟨924531, by rfl⟩ : syracuseStep 2465417 = 1849063) B1849063
theorem B11083715 : Blo 646304 11083715 := bstep (se 1 (by rfl) ⟨8312786, by rfl⟩ : syracuseStep 11083715 = 16625573) B16625573
theorem B974729 : Blo 646304 974729 := bstep (se 2 (by rfl) ⟨365523, by rfl⟩ : syracuseStep 974729 = 731047) B731047
theorem B1643611 : Blo 646304 1643611 := bstep (se 1 (by rfl) ⟨1232708, by rfl⟩ : syracuseStep 1643611 = 2465417) B2465417
theorem B101194217 : Blo 646304 101194217 := bstep (se 2 (by rfl) ⟨37947831, by rfl⟩ : syracuseStep 101194217 = 75895663) B75895663
theorem B1092379 : Blo 646304 1092379 := bstep (se 1 (by rfl) ⟨819284, by rfl⟩ : syracuseStep 1092379 = 1638569) B1638569
theorem B7389143 : Blo 646304 7389143 := bstep (se 1 (by rfl) ⟨5541857, by rfl⟩ : syracuseStep 7389143 = 11083715) B11083715
theorem B649819 : Blo 646304 649819 := bstep (se 1 (by rfl) ⟨487364, by rfl⟩ : syracuseStep 649819 = 974729) B974729
theorem B4926095 : Blo 646304 4926095 := bstep (se 1 (by rfl) ⟨3694571, by rfl⟩ : syracuseStep 4926095 = 7389143) B7389143
theorem B1456505 : Blo 646304 1456505 := bstep (se 2 (by rfl) ⟨546189, by rfl⟩ : syracuseStep 1456505 = 1092379) B1092379
theorem B67462811 : Blo 646304 67462811 := bstep (se 1 (by rfl) ⟨50597108, by rfl⟩ : syracuseStep 67462811 = 101194217) B101194217
theorem B2191481 : Blo 646304 2191481 := bstep (se 2 (by rfl) ⟨821805, by rfl⟩ : syracuseStep 2191481 = 1643611) B1643611
theorem B3284063 : Blo 646304 3284063 := bstep (se 1 (by rfl) ⟨2463047, by rfl⟩ : syracuseStep 3284063 = 4926095) B4926095
theorem B44975207 : Blo 646304 44975207 := bstep (se 1 (by rfl) ⟨33731405, by rfl⟩ : syracuseStep 44975207 = 67462811) B67462811
theorem B1460987 : Blo 646304 1460987 := bstep (se 1 (by rfl) ⟨1095740, by rfl⟩ : syracuseStep 1460987 = 2191481) B2191481
theorem B971003 : Blo 646304 971003 := bstep (se 1 (by rfl) ⟨728252, by rfl⟩ : syracuseStep 971003 = 1456505) B1456505
theorem B119933885 : Blo 646304 119933885 := bstep (se 3 (by rfl) ⟨22487603, by rfl⟩ : syracuseStep 119933885 = 44975207) B44975207
theorem B973991 : Blo 646304 973991 := bstep (se 1 (by rfl) ⟨730493, by rfl⟩ : syracuseStep 973991 = 1460987) B1460987
theorem B647335 : Blo 646304 647335 := bstep (se 1 (by rfl) ⟨485501, by rfl⟩ : syracuseStep 647335 = 971003) B971003
theorem B2189375 : Blo 646304 2189375 := bstep (se 1 (by rfl) ⟨1642031, by rfl⟩ : syracuseStep 2189375 = 3284063) B3284063
theorem B79955923 : Blo 646304 79955923 := bstep (se 1 (by rfl) ⟨59966942, by rfl⟩ : syracuseStep 79955923 = 119933885) B119933885
theorem B1459583 : Blo 646304 1459583 := bstep (se 1 (by rfl) ⟨1094687, by rfl⟩ : syracuseStep 1459583 = 2189375) B2189375
theorem B649327 : Blo 646304 649327 := bstep (se 1 (by rfl) ⟨486995, by rfl⟩ : syracuseStep 649327 = 973991) B973991
theorem B106607897 : Blo 646304 106607897 := bstep (se 2 (by rfl) ⟨39977961, by rfl⟩ : syracuseStep 106607897 = 79955923) B79955923
theorem B973055 : Blo 646304 973055 := bstep (se 1 (by rfl) ⟨729791, by rfl⟩ : syracuseStep 973055 = 1459583) B1459583
theorem B648703 : Blo 646304 648703 := bstep (se 1 (by rfl) ⟨486527, by rfl⟩ : syracuseStep 648703 = 973055) B973055
theorem B71071931 : Blo 646304 71071931 := bstep (se 1 (by rfl) ⟨53303948, by rfl⟩ : syracuseStep 71071931 = 106607897) B106607897
theorem B47381287 : Blo 646304 47381287 := bstep (se 1 (by rfl) ⟨35535965, by rfl⟩ : syracuseStep 47381287 = 71071931) B71071931
theorem B63175049 : Blo 646304 63175049 := bstep (se 2 (by rfl) ⟨23690643, by rfl⟩ : syracuseStep 63175049 = 47381287) B47381287
theorem B42116699 : Blo 646304 42116699 := bstep (se 1 (by rfl) ⟨31587524, by rfl⟩ : syracuseStep 42116699 = 63175049) B63175049
theorem B28077799 : Blo 646304 28077799 := bstep (se 1 (by rfl) ⟨21058349, by rfl⟩ : syracuseStep 28077799 = 42116699) B42116699
theorem B37437065 : Blo 646304 37437065 := bstep (se 2 (by rfl) ⟨14038899, by rfl⟩ : syracuseStep 37437065 = 28077799) B28077799
theorem B24958043 : Blo 646304 24958043 := bstep (se 1 (by rfl) ⟨18718532, by rfl⟩ : syracuseStep 24958043 = 37437065) B37437065
theorem B16638695 : Blo 646304 16638695 := bstep (se 1 (by rfl) ⟨12479021, by rfl⟩ : syracuseStep 16638695 = 24958043) B24958043
theorem B11092463 : Blo 646304 11092463 := bstep (se 1 (by rfl) ⟨8319347, by rfl⟩ : syracuseStep 11092463 = 16638695) B16638695
theorem B7394975 : Blo 646304 7394975 := bstep (se 1 (by rfl) ⟨5546231, by rfl⟩ : syracuseStep 7394975 = 11092463) B11092463
theorem B4929983 : Blo 646304 4929983 := bstep (se 1 (by rfl) ⟨3697487, by rfl⟩ : syracuseStep 4929983 = 7394975) B7394975
theorem B3286655 : Blo 646304 3286655 := bstep (se 1 (by rfl) ⟨2464991, by rfl⟩ : syracuseStep 3286655 = 4929983) B4929983
theorem B2191103 : Blo 646304 2191103 := bstep (se 1 (by rfl) ⟨1643327, by rfl⟩ : syracuseStep 2191103 = 3286655) B3286655
theorem B1460735 : Blo 646304 1460735 := bstep (se 1 (by rfl) ⟨1095551, by rfl⟩ : syracuseStep 1460735 = 2191103) B2191103
theorem B973823 : Blo 646304 973823 := bstep (se 1 (by rfl) ⟨730367, by rfl⟩ : syracuseStep 973823 = 1460735) B1460735
theorem B649215 : Blo 646304 649215 := bstep (se 1 (by rfl) ⟨486911, by rfl⟩ : syracuseStep 649215 = 973823) B973823

theorem C0 (j : ℕ) (h1 : 161576 ≤ j) (h2 : j ≤ 162275) : Blo 646304 (4 * j + 3) := by
  interval_cases j
  · exact B646307
  · exact B646311
  · exact B646315
  · exact B646319
  · exact B646323
  · exact B646327
  · exact B646331
  · exact B646335
  · exact B646339
  · exact B646343
  · exact B646347
  · exact B646351
  · exact B646355
  · exact B646359
  · exact B646363
  · exact B646367
  · exact B646371
  · exact B646375
  · exact B646379
  · exact B646383
  · exact B646387
  · exact B646391
  · exact B646395
  · exact B646399
  · exact B646403
  · exact B646407
  · exact B646411
  · exact B646415
  · exact B646419
  · exact B646423
  · exact B646427
  · exact B646431
  · exact B646435
  · exact B646439
  · exact B646443
  · exact B646447
  · exact B646451
  · exact B646455
  · exact B646459
  · exact B646463
  · exact B646467
  · exact B646471
  · exact B646475
  · exact B646479
  · exact B646483
  · exact B646487
  · exact B646491
  · exact B646495
  · exact B646499
  · exact B646503
  · exact B646507
  · exact B646511
  · exact B646515
  · exact B646519
  · exact B646523
  · exact B646527
  · exact B646531
  · exact B646535
  · exact B646539
  · exact B646543
  · exact B646547
  · exact B646551
  · exact B646555
  · exact B646559
  · exact B646563
  · exact B646567
  · exact B646571
  · exact B646575
  · exact B646579
  · exact B646583
  · exact B646587
  · exact B646591
  · exact B646595
  · exact B646599
  · exact B646603
  · exact B646607
  · exact B646611
  · exact B646615
  · exact B646619
  · exact B646623
  · exact B646627
  · exact B646631
  · exact B646635
  · exact B646639
  · exact B646643
  · exact B646647
  · exact B646651
  · exact B646655
  · exact B646659
  · exact B646663
  · exact B646667
  · exact B646671
  · exact B646675
  · exact B646679
  · exact B646683
  · exact B646687
  · exact B646691
  · exact B646695
  · exact B646699
  · exact B646703
  · exact B646707
  · exact B646711
  · exact B646715
  · exact B646719
  · exact B646723
  · exact B646727
  · exact B646731
  · exact B646735
  · exact B646739
  · exact B646743
  · exact B646747
  · exact B646751
  · exact B646755
  · exact B646759
  · exact B646763
  · exact B646767
  · exact B646771
  · exact B646775
  · exact B646779
  · exact B646783
  · exact B646787
  · exact B646791
  · exact B646795
  · exact B646799
  · exact B646803
  · exact B646807
  · exact B646811
  · exact B646815
  · exact B646819
  · exact B646823
  · exact B646827
  · exact B646831
  · exact B646835
  · exact B646839
  · exact B646843
  · exact B646847
  · exact B646851
  · exact B646855
  · exact B646859
  · exact B646863
  · exact B646867
  · exact B646871
  · exact B646875
  · exact B646879
  · exact B646883
  · exact B646887
  · exact B646891
  · exact B646895
  · exact B646899
  · exact B646903
  · exact B646907
  · exact B646911
  · exact B646915
  · exact B646919
  · exact B646923
  · exact B646927
  · exact B646931
  · exact B646935
  · exact B646939
  · exact B646943
  · exact B646947
  · exact B646951
  · exact B646955
  · exact B646959
  · exact B646963
  · exact B646967
  · exact B646971
  · exact B646975
  · exact B646979
  · exact B646983
  · exact B646987
  · exact B646991
  · exact B646995
  · exact B646999
  · exact B647003
  · exact B647007
  · exact B647011
  · exact B647015
  · exact B647019
  · exact B647023
  · exact B647027
  · exact B647031
  · exact B647035
  · exact B647039
  · exact B647043
  · exact B647047
  · exact B647051
  · exact B647055
  · exact B647059
  · exact B647063
  · exact B647067
  · exact B647071
  · exact B647075
  · exact B647079
  · exact B647083
  · exact B647087
  · exact B647091
  · exact B647095
  · exact B647099
  · exact B647103
  · exact B647107
  · exact B647111
  · exact B647115
  · exact B647119
  · exact B647123
  · exact B647127
  · exact B647131
  · exact B647135
  · exact B647139
  · exact B647143
  · exact B647147
  · exact B647151
  · exact B647155
  · exact B647159
  · exact B647163
  · exact B647167
  · exact B647171
  · exact B647175
  · exact B647179
  · exact B647183
  · exact B647187
  · exact B647191
  · exact B647195
  · exact B647199
  · exact B647203
  · exact B647207
  · exact B647211
  · exact B647215
  · exact B647219
  · exact B647223
  · exact B647227
  · exact B647231
  · exact B647235
  · exact B647239
  · exact B647243
  · exact B647247
  · exact B647251
  · exact B647255
  · exact B647259
  · exact B647263
  · exact B647267
  · exact B647271
  · exact B647275
  · exact B647279
  · exact B647283
  · exact B647287
  · exact B647291
  · exact B647295
  · exact B647299
  · exact B647303
  · exact B647307
  · exact B647311
  · exact B647315
  · exact B647319
  · exact B647323
  · exact B647327
  · exact B647331
  · exact B647335
  · exact B647339
  · exact B647343
  · exact B647347
  · exact B647351
  · exact B647355
  · exact B647359
  · exact B647363
  · exact B647367
  · exact B647371
  · exact B647375
  · exact B647379
  · exact B647383
  · exact B647387
  · exact B647391
  · exact B647395
  · exact B647399
  · exact B647403
  · exact B647407
  · exact B647411
  · exact B647415
  · exact B647419
  · exact B647423
  · exact B647427
  · exact B647431
  · exact B647435
  · exact B647439
  · exact B647443
  · exact B647447
  · exact B647451
  · exact B647455
  · exact B647459
  · exact B647463
  · exact B647467
  · exact B647471
  · exact B647475
  · exact B647479
  · exact B647483
  · exact B647487
  · exact B647491
  · exact B647495
  · exact B647499
  · exact B647503
  · exact B647507
  · exact B647511
  · exact B647515
  · exact B647519
  · exact B647523
  · exact B647527
  · exact B647531
  · exact B647535
  · exact B647539
  · exact B647543
  · exact B647547
  · exact B647551
  · exact B647555
  · exact B647559
  · exact B647563
  · exact B647567
  · exact B647571
  · exact B647575
  · exact B647579
  · exact B647583
  · exact B647587
  · exact B647591
  · exact B647595
  · exact B647599
  · exact B647603
  · exact B647607
  · exact B647611
  · exact B647615
  · exact B647619
  · exact B647623
  · exact B647627
  · exact B647631
  · exact B647635
  · exact B647639
  · exact B647643
  · exact B647647
  · exact B647651
  · exact B647655
  · exact B647659
  · exact B647663
  · exact B647667
  · exact B647671
  · exact B647675
  · exact B647679
  · exact B647683
  · exact B647687
  · exact B647691
  · exact B647695
  · exact B647699
  · exact B647703
  · exact B647707
  · exact B647711
  · exact B647715
  · exact B647719
  · exact B647723
  · exact B647727
  · exact B647731
  · exact B647735
  · exact B647739
  · exact B647743
  · exact B647747
  · exact B647751
  · exact B647755
  · exact B647759
  · exact B647763
  · exact B647767
  · exact B647771
  · exact B647775
  · exact B647779
  · exact B647783
  · exact B647787
  · exact B647791
  · exact B647795
  · exact B647799
  · exact B647803
  · exact B647807
  · exact B647811
  · exact B647815
  · exact B647819
  · exact B647823
  · exact B647827
  · exact B647831
  · exact B647835
  · exact B647839
  · exact B647843
  · exact B647847
  · exact B647851
  · exact B647855
  · exact B647859
  · exact B647863
  · exact B647867
  · exact B647871
  · exact B647875
  · exact B647879
  · exact B647883
  · exact B647887
  · exact B647891
  · exact B647895
  · exact B647899
  · exact B647903
  · exact B647907
  · exact B647911
  · exact B647915
  · exact B647919
  · exact B647923
  · exact B647927
  · exact B647931
  · exact B647935
  · exact B647939
  · exact B647943
  · exact B647947
  · exact B647951
  · exact B647955
  · exact B647959
  · exact B647963
  · exact B647967
  · exact B647971
  · exact B647975
  · exact B647979
  · exact B647983
  · exact B647987
  · exact B647991
  · exact B647995
  · exact B647999
  · exact B648003
  · exact B648007
  · exact B648011
  · exact B648015
  · exact B648019
  · exact B648023
  · exact B648027
  · exact B648031
  · exact B648035
  · exact B648039
  · exact B648043
  · exact B648047
  · exact B648051
  · exact B648055
  · exact B648059
  · exact B648063
  · exact B648067
  · exact B648071
  · exact B648075
  · exact B648079
  · exact B648083
  · exact B648087
  · exact B648091
  · exact B648095
  · exact B648099
  · exact B648103
  · exact B648107
  · exact B648111
  · exact B648115
  · exact B648119
  · exact B648123
  · exact B648127
  · exact B648131
  · exact B648135
  · exact B648139
  · exact B648143
  · exact B648147
  · exact B648151
  · exact B648155
  · exact B648159
  · exact B648163
  · exact B648167
  · exact B648171
  · exact B648175
  · exact B648179
  · exact B648183
  · exact B648187
  · exact B648191
  · exact B648195
  · exact B648199
  · exact B648203
  · exact B648207
  · exact B648211
  · exact B648215
  · exact B648219
  · exact B648223
  · exact B648227
  · exact B648231
  · exact B648235
  · exact B648239
  · exact B648243
  · exact B648247
  · exact B648251
  · exact B648255
  · exact B648259
  · exact B648263
  · exact B648267
  · exact B648271
  · exact B648275
  · exact B648279
  · exact B648283
  · exact B648287
  · exact B648291
  · exact B648295
  · exact B648299
  · exact B648303
  · exact B648307
  · exact B648311
  · exact B648315
  · exact B648319
  · exact B648323
  · exact B648327
  · exact B648331
  · exact B648335
  · exact B648339
  · exact B648343
  · exact B648347
  · exact B648351
  · exact B648355
  · exact B648359
  · exact B648363
  · exact B648367
  · exact B648371
  · exact B648375
  · exact B648379
  · exact B648383
  · exact B648387
  · exact B648391
  · exact B648395
  · exact B648399
  · exact B648403
  · exact B648407
  · exact B648411
  · exact B648415
  · exact B648419
  · exact B648423
  · exact B648427
  · exact B648431
  · exact B648435
  · exact B648439
  · exact B648443
  · exact B648447
  · exact B648451
  · exact B648455
  · exact B648459
  · exact B648463
  · exact B648467
  · exact B648471
  · exact B648475
  · exact B648479
  · exact B648483
  · exact B648487
  · exact B648491
  · exact B648495
  · exact B648499
  · exact B648503
  · exact B648507
  · exact B648511
  · exact B648515
  · exact B648519
  · exact B648523
  · exact B648527
  · exact B648531
  · exact B648535
  · exact B648539
  · exact B648543
  · exact B648547
  · exact B648551
  · exact B648555
  · exact B648559
  · exact B648563
  · exact B648567
  · exact B648571
  · exact B648575
  · exact B648579
  · exact B648583
  · exact B648587
  · exact B648591
  · exact B648595
  · exact B648599
  · exact B648603
  · exact B648607
  · exact B648611
  · exact B648615
  · exact B648619
  · exact B648623
  · exact B648627
  · exact B648631
  · exact B648635
  · exact B648639
  · exact B648643
  · exact B648647
  · exact B648651
  · exact B648655
  · exact B648659
  · exact B648663
  · exact B648667
  · exact B648671
  · exact B648675
  · exact B648679
  · exact B648683
  · exact B648687
  · exact B648691
  · exact B648695
  · exact B648699
  · exact B648703
  · exact B648707
  · exact B648711
  · exact B648715
  · exact B648719
  · exact B648723
  · exact B648727
  · exact B648731
  · exact B648735
  · exact B648739
  · exact B648743
  · exact B648747
  · exact B648751
  · exact B648755
  · exact B648759
  · exact B648763
  · exact B648767
  · exact B648771
  · exact B648775
  · exact B648779
  · exact B648783
  · exact B648787
  · exact B648791
  · exact B648795
  · exact B648799
  · exact B648803
  · exact B648807
  · exact B648811
  · exact B648815
  · exact B648819
  · exact B648823
  · exact B648827
  · exact B648831
  · exact B648835
  · exact B648839
  · exact B648843
  · exact B648847
  · exact B648851
  · exact B648855
  · exact B648859
  · exact B648863
  · exact B648867
  · exact B648871
  · exact B648875
  · exact B648879
  · exact B648883
  · exact B648887
  · exact B648891
  · exact B648895
  · exact B648899
  · exact B648903
  · exact B648907
  · exact B648911
  · exact B648915
  · exact B648919
  · exact B648923
  · exact B648927
  · exact B648931
  · exact B648935
  · exact B648939
  · exact B648943
  · exact B648947
  · exact B648951
  · exact B648955
  · exact B648959
  · exact B648963
  · exact B648967
  · exact B648971
  · exact B648975
  · exact B648979
  · exact B648983
  · exact B648987
  · exact B648991
  · exact B648995
  · exact B648999
  · exact B649003
  · exact B649007
  · exact B649011
  · exact B649015
  · exact B649019
  · exact B649023
  · exact B649027
  · exact B649031
  · exact B649035
  · exact B649039
  · exact B649043
  · exact B649047
  · exact B649051
  · exact B649055
  · exact B649059
  · exact B649063
  · exact B649067
  · exact B649071
  · exact B649075
  · exact B649079
  · exact B649083
  · exact B649087
  · exact B649091
  · exact B649095
  · exact B649099
  · exact B649103

theorem C1 (j : ℕ) (h1 : 162276 ≤ j) (h2 : j ≤ 162575) : Blo 646304 (4 * j + 3) := by
  interval_cases j
  · exact B649107
  · exact B649111
  · exact B649115
  · exact B649119
  · exact B649123
  · exact B649127
  · exact B649131
  · exact B649135
  · exact B649139
  · exact B649143
  · exact B649147
  · exact B649151
  · exact B649155
  · exact B649159
  · exact B649163
  · exact B649167
  · exact B649171
  · exact B649175
  · exact B649179
  · exact B649183
  · exact B649187
  · exact B649191
  · exact B649195
  · exact B649199
  · exact B649203
  · exact B649207
  · exact B649211
  · exact B649215
  · exact B649219
  · exact B649223
  · exact B649227
  · exact B649231
  · exact B649235
  · exact B649239
  · exact B649243
  · exact B649247
  · exact B649251
  · exact B649255
  · exact B649259
  · exact B649263
  · exact B649267
  · exact B649271
  · exact B649275
  · exact B649279
  · exact B649283
  · exact B649287
  · exact B649291
  · exact B649295
  · exact B649299
  · exact B649303
  · exact B649307
  · exact B649311
  · exact B649315
  · exact B649319
  · exact B649323
  · exact B649327
  · exact B649331
  · exact B649335
  · exact B649339
  · exact B649343
  · exact B649347
  · exact B649351
  · exact B649355
  · exact B649359
  · exact B649363
  · exact B649367
  · exact B649371
  · exact B649375
  · exact B649379
  · exact B649383
  · exact B649387
  · exact B649391
  · exact B649395
  · exact B649399
  · exact B649403
  · exact B649407
  · exact B649411
  · exact B649415
  · exact B649419
  · exact B649423
  · exact B649427
  · exact B649431
  · exact B649435
  · exact B649439
  · exact B649443
  · exact B649447
  · exact B649451
  · exact B649455
  · exact B649459
  · exact B649463
  · exact B649467
  · exact B649471
  · exact B649475
  · exact B649479
  · exact B649483
  · exact B649487
  · exact B649491
  · exact B649495
  · exact B649499
  · exact B649503
  · exact B649507
  · exact B649511
  · exact B649515
  · exact B649519
  · exact B649523
  · exact B649527
  · exact B649531
  · exact B649535
  · exact B649539
  · exact B649543
  · exact B649547
  · exact B649551
  · exact B649555
  · exact B649559
  · exact B649563
  · exact B649567
  · exact B649571
  · exact B649575
  · exact B649579
  · exact B649583
  · exact B649587
  · exact B649591
  · exact B649595
  · exact B649599
  · exact B649603
  · exact B649607
  · exact B649611
  · exact B649615
  · exact B649619
  · exact B649623
  · exact B649627
  · exact B649631
  · exact B649635
  · exact B649639
  · exact B649643
  · exact B649647
  · exact B649651
  · exact B649655
  · exact B649659
  · exact B649663
  · exact B649667
  · exact B649671
  · exact B649675
  · exact B649679
  · exact B649683
  · exact B649687
  · exact B649691
  · exact B649695
  · exact B649699
  · exact B649703
  · exact B649707
  · exact B649711
  · exact B649715
  · exact B649719
  · exact B649723
  · exact B649727
  · exact B649731
  · exact B649735
  · exact B649739
  · exact B649743
  · exact B649747
  · exact B649751
  · exact B649755
  · exact B649759
  · exact B649763
  · exact B649767
  · exact B649771
  · exact B649775
  · exact B649779
  · exact B649783
  · exact B649787
  · exact B649791
  · exact B649795
  · exact B649799
  · exact B649803
  · exact B649807
  · exact B649811
  · exact B649815
  · exact B649819
  · exact B649823
  · exact B649827
  · exact B649831
  · exact B649835
  · exact B649839
  · exact B649843
  · exact B649847
  · exact B649851
  · exact B649855
  · exact B649859
  · exact B649863
  · exact B649867
  · exact B649871
  · exact B649875
  · exact B649879
  · exact B649883
  · exact B649887
  · exact B649891
  · exact B649895
  · exact B649899
  · exact B649903
  · exact B649907
  · exact B649911
  · exact B649915
  · exact B649919
  · exact B649923
  · exact B649927
  · exact B649931
  · exact B649935
  · exact B649939
  · exact B649943
  · exact B649947
  · exact B649951
  · exact B649955
  · exact B649959
  · exact B649963
  · exact B649967
  · exact B649971
  · exact B649975
  · exact B649979
  · exact B649983
  · exact B649987
  · exact B649991
  · exact B649995
  · exact B649999
  · exact B650003
  · exact B650007
  · exact B650011
  · exact B650015
  · exact B650019
  · exact B650023
  · exact B650027
  · exact B650031
  · exact B650035
  · exact B650039
  · exact B650043
  · exact B650047
  · exact B650051
  · exact B650055
  · exact B650059
  · exact B650063
  · exact B650067
  · exact B650071
  · exact B650075
  · exact B650079
  · exact B650083
  · exact B650087
  · exact B650091
  · exact B650095
  · exact B650099
  · exact B650103
  · exact B650107
  · exact B650111
  · exact B650115
  · exact B650119
  · exact B650123
  · exact B650127
  · exact B650131
  · exact B650135
  · exact B650139
  · exact B650143
  · exact B650147
  · exact B650151
  · exact B650155
  · exact B650159
  · exact B650163
  · exact B650167
  · exact B650171
  · exact B650175
  · exact B650179
  · exact B650183
  · exact B650187
  · exact B650191
  · exact B650195
  · exact B650199
  · exact B650203
  · exact B650207
  · exact B650211
  · exact B650215
  · exact B650219
  · exact B650223
  · exact B650227
  · exact B650231
  · exact B650235
  · exact B650239
  · exact B650243
  · exact B650247
  · exact B650251
  · exact B650255
  · exact B650259
  · exact B650263
  · exact B650267
  · exact B650271
  · exact B650275
  · exact B650279
  · exact B650283
  · exact B650287
  · exact B650291
  · exact B650295
  · exact B650299
  · exact B650303

theorem solution (m : ℕ) (hlo : 646304 ≤ m) (hhi : m ≤ 650304) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 161576 ≤ j := by omega
    have hj2 : j ≤ 162575 := by omega
    have hb : Blo 646304 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 162276 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
