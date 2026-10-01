-- Prove2me | solution 1 for syracuse_descends_range_2281435_2283435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:49:37.38799+00:00
-- url     : https://prove2.me/submissions/4a878c2d-d6d4-4eba-a831-c7ab054c9c2f

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

theorem B5774885 : Blo 2281435 5774885 := bbase (se 4 (by rfl) ⟨541395, by rfl⟩ : syracuseStep 5774885 = 1082791) (by norm_num)
theorem B3849923 : Blo 2281435 3849923 := bstep (se 1 (by rfl) ⟨2887442, by rfl⟩ : syracuseStep 3849923 = 5774885) B5774885
theorem B2566615 : Blo 2281435 2566615 := bstep (se 1 (by rfl) ⟨1924961, by rfl⟩ : syracuseStep 2566615 = 3849923) B3849923
theorem B3422153 : Blo 2281435 3422153 := bstep (se 2 (by rfl) ⟨1283307, by rfl⟩ : syracuseStep 3422153 = 2566615) B2566615
theorem B2281435 : Blo 2281435 2281435 := bstep (se 1 (by rfl) ⟨1711076, by rfl⟩ : syracuseStep 2281435 = 3422153) B3422153
theorem B6496757 : Blo 2281435 6496757 := bbase (se 5 (by rfl) ⟨304535, by rfl⟩ : syracuseStep 6496757 = 609071) (by norm_num)
theorem B4331171 : Blo 2281435 4331171 := bstep (se 1 (by rfl) ⟨3248378, by rfl⟩ : syracuseStep 4331171 = 6496757) B6496757
theorem B11549789 : Blo 2281435 11549789 := bstep (se 3 (by rfl) ⟨2165585, by rfl⟩ : syracuseStep 11549789 = 4331171) B4331171
theorem B7699859 : Blo 2281435 7699859 := bstep (se 1 (by rfl) ⟨5774894, by rfl⟩ : syracuseStep 7699859 = 11549789) B11549789
theorem B5133239 : Blo 2281435 5133239 := bstep (se 1 (by rfl) ⟨3849929, by rfl⟩ : syracuseStep 5133239 = 7699859) B7699859
theorem B3422159 : Blo 2281435 3422159 := bstep (se 1 (by rfl) ⟨2566619, by rfl⟩ : syracuseStep 3422159 = 5133239) B5133239
theorem B2281439 : Blo 2281435 2281439 := bstep (se 1 (by rfl) ⟨1711079, by rfl⟩ : syracuseStep 2281439 = 3422159) B3422159
theorem B3422165 : Blo 2281435 3422165 := bbase (se 7 (by rfl) ⟨40103, by rfl⟩ : syracuseStep 3422165 = 80207) (by norm_num)
theorem B2281443 : Blo 2281435 2281443 := bstep (se 1 (by rfl) ⟨1711082, by rfl⟩ : syracuseStep 2281443 = 3422165) B3422165
theorem B8662373 : Blo 2281435 8662373 := bbase (se 4 (by rfl) ⟨812097, by rfl⟩ : syracuseStep 8662373 = 1624195) (by norm_num)
theorem B5774915 : Blo 2281435 5774915 := bstep (se 1 (by rfl) ⟨4331186, by rfl⟩ : syracuseStep 5774915 = 8662373) B8662373
theorem B3849943 : Blo 2281435 3849943 := bstep (se 1 (by rfl) ⟨2887457, by rfl⟩ : syracuseStep 3849943 = 5774915) B5774915
theorem B5133257 : Blo 2281435 5133257 := bstep (se 2 (by rfl) ⟨1924971, by rfl⟩ : syracuseStep 5133257 = 3849943) B3849943
theorem B3422171 : Blo 2281435 3422171 := bstep (se 1 (by rfl) ⟨2566628, by rfl⟩ : syracuseStep 3422171 = 5133257) B5133257
theorem B2281447 : Blo 2281435 2281447 := bstep (se 1 (by rfl) ⟨1711085, by rfl⟩ : syracuseStep 2281447 = 3422171) B3422171
theorem B2566633 : Blo 2281435 2566633 := bbase (se 2 (by rfl) ⟨962487, by rfl⟩ : syracuseStep 2566633 = 1924975) (by norm_num)
theorem B3422177 : Blo 2281435 3422177 := bstep (se 2 (by rfl) ⟨1283316, by rfl⟩ : syracuseStep 3422177 = 2566633) B2566633
theorem B2281451 : Blo 2281435 2281451 := bstep (se 1 (by rfl) ⟨1711088, by rfl⟩ : syracuseStep 2281451 = 3422177) B3422177
theorem B2436301 : Blo 2281435 2436301 := bbase (se 3 (by rfl) ⟨456806, by rfl⟩ : syracuseStep 2436301 = 913613) (by norm_num)
theorem B12993605 : Blo 2281435 12993605 := bstep (se 4 (by rfl) ⟨1218150, by rfl⟩ : syracuseStep 12993605 = 2436301) B2436301
theorem B8662403 : Blo 2281435 8662403 := bstep (se 1 (by rfl) ⟨6496802, by rfl⟩ : syracuseStep 8662403 = 12993605) B12993605
theorem B5774935 : Blo 2281435 5774935 := bstep (se 1 (by rfl) ⟨4331201, by rfl⟩ : syracuseStep 5774935 = 8662403) B8662403
theorem B7699913 : Blo 2281435 7699913 := bstep (se 2 (by rfl) ⟨2887467, by rfl⟩ : syracuseStep 7699913 = 5774935) B5774935
theorem B5133275 : Blo 2281435 5133275 := bstep (se 1 (by rfl) ⟨3849956, by rfl⟩ : syracuseStep 5133275 = 7699913) B7699913
theorem B3422183 : Blo 2281435 3422183 := bstep (se 1 (by rfl) ⟨2566637, by rfl⟩ : syracuseStep 3422183 = 5133275) B5133275
theorem B2281455 : Blo 2281435 2281455 := bstep (se 1 (by rfl) ⟨1711091, by rfl⟩ : syracuseStep 2281455 = 3422183) B3422183
theorem B3422189 : Blo 2281435 3422189 := bbase (se 3 (by rfl) ⟨641660, by rfl⟩ : syracuseStep 3422189 = 1283321) (by norm_num)
theorem B2281459 : Blo 2281435 2281459 := bstep (se 1 (by rfl) ⟨1711094, by rfl⟩ : syracuseStep 2281459 = 3422189) B3422189
theorem B5133293 : Blo 2281435 5133293 := bbase (se 3 (by rfl) ⟨962492, by rfl⟩ : syracuseStep 5133293 = 1924985) (by norm_num)
theorem B3422195 : Blo 2281435 3422195 := bstep (se 1 (by rfl) ⟨2566646, by rfl⟩ : syracuseStep 3422195 = 5133293) B5133293
theorem B2281463 : Blo 2281435 2281463 := bstep (se 1 (by rfl) ⟨1711097, by rfl⟩ : syracuseStep 2281463 = 3422195) B3422195
theorem B4872629 : Blo 2281435 4872629 := bbase (se 5 (by rfl) ⟨228404, by rfl⟩ : syracuseStep 4872629 = 456809) (by norm_num)
theorem B3248419 : Blo 2281435 3248419 := bstep (se 1 (by rfl) ⟨2436314, by rfl⟩ : syracuseStep 3248419 = 4872629) B4872629
theorem B4331225 : Blo 2281435 4331225 := bstep (se 2 (by rfl) ⟨1624209, by rfl⟩ : syracuseStep 4331225 = 3248419) B3248419
theorem B2887483 : Blo 2281435 2887483 := bstep (se 1 (by rfl) ⟨2165612, by rfl⟩ : syracuseStep 2887483 = 4331225) B4331225
theorem B3849977 : Blo 2281435 3849977 := bstep (se 2 (by rfl) ⟨1443741, by rfl⟩ : syracuseStep 3849977 = 2887483) B2887483
theorem B2566651 : Blo 2281435 2566651 := bstep (se 1 (by rfl) ⟨1924988, by rfl⟩ : syracuseStep 2566651 = 3849977) B3849977
theorem B3422201 : Blo 2281435 3422201 := bstep (se 2 (by rfl) ⟨1283325, by rfl⟩ : syracuseStep 3422201 = 2566651) B2566651
theorem B2281467 : Blo 2281435 2281467 := bstep (se 1 (by rfl) ⟨1711100, by rfl⟩ : syracuseStep 2281467 = 3422201) B3422201
theorem B5274341 : Blo 2281435 5274341 := bbase (se 4 (by rfl) ⟨494469, by rfl⟩ : syracuseStep 5274341 = 988939) (by norm_num)
theorem B3516227 : Blo 2281435 3516227 := bstep (se 1 (by rfl) ⟨2637170, by rfl⟩ : syracuseStep 3516227 = 5274341) B5274341
theorem B2344151 : Blo 2281435 2344151 := bstep (se 1 (by rfl) ⟨1758113, by rfl⟩ : syracuseStep 2344151 = 3516227) B3516227
theorem B6251069 : Blo 2281435 6251069 := bstep (se 3 (by rfl) ⟨1172075, by rfl⟩ : syracuseStep 6251069 = 2344151) B2344151
theorem B4167379 : Blo 2281435 4167379 := bstep (se 1 (by rfl) ⟨3125534, by rfl⟩ : syracuseStep 4167379 = 6251069) B6251069
theorem B5556505 : Blo 2281435 5556505 := bstep (se 2 (by rfl) ⟨2083689, by rfl⟩ : syracuseStep 5556505 = 4167379) B4167379
theorem B7408673 : Blo 2281435 7408673 := bstep (se 2 (by rfl) ⟨2778252, by rfl⟩ : syracuseStep 7408673 = 5556505) B5556505
theorem B4939115 : Blo 2281435 4939115 := bstep (se 1 (by rfl) ⟨3704336, by rfl⟩ : syracuseStep 4939115 = 7408673) B7408673
theorem B13170973 : Blo 2281435 13170973 := bstep (se 3 (by rfl) ⟨2469557, by rfl⟩ : syracuseStep 13170973 = 4939115) B4939115
theorem B17561297 : Blo 2281435 17561297 := bstep (se 2 (by rfl) ⟨6585486, by rfl⟩ : syracuseStep 17561297 = 13170973) B13170973
theorem B46830125 : Blo 2281435 46830125 := bstep (se 3 (by rfl) ⟨8780648, by rfl⟩ : syracuseStep 46830125 = 17561297) B17561297
theorem B31220083 : Blo 2281435 31220083 := bstep (se 1 (by rfl) ⟨23415062, by rfl⟩ : syracuseStep 31220083 = 46830125) B46830125
theorem B166507109 : Blo 2281435 166507109 := bstep (se 4 (by rfl) ⟨15610041, by rfl⟩ : syracuseStep 166507109 = 31220083) B31220083
theorem B111004739 : Blo 2281435 111004739 := bstep (se 1 (by rfl) ⟨83253554, by rfl⟩ : syracuseStep 111004739 = 166507109) B166507109
theorem B74003159 : Blo 2281435 74003159 := bstep (se 1 (by rfl) ⟨55502369, by rfl⟩ : syracuseStep 74003159 = 111004739) B111004739
theorem B197341757 : Blo 2281435 197341757 := bstep (se 3 (by rfl) ⟨37001579, by rfl⟩ : syracuseStep 197341757 = 74003159) B74003159
theorem B131561171 : Blo 2281435 131561171 := bstep (se 1 (by rfl) ⟨98670878, by rfl⟩ : syracuseStep 131561171 = 197341757) B197341757
theorem B87707447 : Blo 2281435 87707447 := bstep (se 1 (by rfl) ⟨65780585, by rfl⟩ : syracuseStep 87707447 = 131561171) B131561171
theorem B58471631 : Blo 2281435 58471631 := bstep (se 1 (by rfl) ⟨43853723, by rfl⟩ : syracuseStep 58471631 = 87707447) B87707447
theorem B38981087 : Blo 2281435 38981087 := bstep (se 1 (by rfl) ⟨29235815, by rfl⟩ : syracuseStep 38981087 = 58471631) B58471631
theorem B25987391 : Blo 2281435 25987391 := bstep (se 1 (by rfl) ⟨19490543, by rfl⟩ : syracuseStep 25987391 = 38981087) B38981087
theorem B17324927 : Blo 2281435 17324927 := bstep (se 1 (by rfl) ⟨12993695, by rfl⟩ : syracuseStep 17324927 = 25987391) B25987391
theorem B11549951 : Blo 2281435 11549951 := bstep (se 1 (by rfl) ⟨8662463, by rfl⟩ : syracuseStep 11549951 = 17324927) B17324927
theorem B7699967 : Blo 2281435 7699967 := bstep (se 1 (by rfl) ⟨5774975, by rfl⟩ : syracuseStep 7699967 = 11549951) B11549951
theorem B5133311 : Blo 2281435 5133311 := bstep (se 1 (by rfl) ⟨3849983, by rfl⟩ : syracuseStep 5133311 = 7699967) B7699967
theorem B3422207 : Blo 2281435 3422207 := bstep (se 1 (by rfl) ⟨2566655, by rfl⟩ : syracuseStep 3422207 = 5133311) B5133311
theorem B2281471 : Blo 2281435 2281471 := bstep (se 1 (by rfl) ⟨1711103, by rfl⟩ : syracuseStep 2281471 = 3422207) B3422207
theorem B3422213 : Blo 2281435 3422213 := bbase (se 4 (by rfl) ⟨320832, by rfl⟩ : syracuseStep 3422213 = 641665) (by norm_num)
theorem B2281475 : Blo 2281435 2281475 := bstep (se 1 (by rfl) ⟨1711106, by rfl⟩ : syracuseStep 2281475 = 3422213) B3422213
theorem B3849997 : Blo 2281435 3849997 := bbase (se 3 (by rfl) ⟨721874, by rfl⟩ : syracuseStep 3849997 = 1443749) (by norm_num)
theorem B5133329 : Blo 2281435 5133329 := bstep (se 2 (by rfl) ⟨1924998, by rfl⟩ : syracuseStep 5133329 = 3849997) B3849997
theorem B3422219 : Blo 2281435 3422219 := bstep (se 1 (by rfl) ⟨2566664, by rfl⟩ : syracuseStep 3422219 = 5133329) B5133329
theorem B2281479 : Blo 2281435 2281479 := bstep (se 1 (by rfl) ⟨1711109, by rfl⟩ : syracuseStep 2281479 = 3422219) B3422219
theorem B2566669 : Blo 2281435 2566669 := bbase (se 3 (by rfl) ⟨481250, by rfl⟩ : syracuseStep 2566669 = 962501) (by norm_num)
theorem B3422225 : Blo 2281435 3422225 := bstep (se 2 (by rfl) ⟨1283334, by rfl⟩ : syracuseStep 3422225 = 2566669) B2566669
theorem B2281483 : Blo 2281435 2281483 := bstep (se 1 (by rfl) ⟨1711112, by rfl⟩ : syracuseStep 2281483 = 3422225) B3422225
theorem B7700021 : Blo 2281435 7700021 := bbase (se 5 (by rfl) ⟨360938, by rfl⟩ : syracuseStep 7700021 = 721877) (by norm_num)
theorem B5133347 : Blo 2281435 5133347 := bstep (se 1 (by rfl) ⟨3850010, by rfl⟩ : syracuseStep 5133347 = 7700021) B7700021
theorem B3422231 : Blo 2281435 3422231 := bstep (se 1 (by rfl) ⟨2566673, by rfl⟩ : syracuseStep 3422231 = 5133347) B5133347
theorem B2281487 : Blo 2281435 2281487 := bstep (se 1 (by rfl) ⟨1711115, by rfl⟩ : syracuseStep 2281487 = 3422231) B3422231
theorem B3422237 : Blo 2281435 3422237 := bbase (se 3 (by rfl) ⟨641669, by rfl⟩ : syracuseStep 3422237 = 1283339) (by norm_num)
theorem B2281491 : Blo 2281435 2281491 := bstep (se 1 (by rfl) ⟨1711118, by rfl⟩ : syracuseStep 2281491 = 3422237) B3422237
theorem B5133365 : Blo 2281435 5133365 := bbase (se 5 (by rfl) ⟨240626, by rfl⟩ : syracuseStep 5133365 = 481253) (by norm_num)
theorem B3422243 : Blo 2281435 3422243 := bstep (se 1 (by rfl) ⟨2566682, by rfl⟩ : syracuseStep 3422243 = 5133365) B5133365
theorem B2281495 : Blo 2281435 2281495 := bstep (se 1 (by rfl) ⟨1711121, by rfl⟩ : syracuseStep 2281495 = 3422243) B3422243
theorem B7309045 : Blo 2281435 7309045 := bbase (se 5 (by rfl) ⟨342611, by rfl⟩ : syracuseStep 7309045 = 685223) (by norm_num)
theorem B9745393 : Blo 2281435 9745393 := bstep (se 2 (by rfl) ⟨3654522, by rfl⟩ : syracuseStep 9745393 = 7309045) B7309045
theorem B12993857 : Blo 2281435 12993857 := bstep (se 2 (by rfl) ⟨4872696, by rfl⟩ : syracuseStep 12993857 = 9745393) B9745393
theorem B8662571 : Blo 2281435 8662571 := bstep (se 1 (by rfl) ⟨6496928, by rfl⟩ : syracuseStep 8662571 = 12993857) B12993857
theorem B5775047 : Blo 2281435 5775047 := bstep (se 1 (by rfl) ⟨4331285, by rfl⟩ : syracuseStep 5775047 = 8662571) B8662571
theorem B3850031 : Blo 2281435 3850031 := bstep (se 1 (by rfl) ⟨2887523, by rfl⟩ : syracuseStep 3850031 = 5775047) B5775047
theorem B2566687 : Blo 2281435 2566687 := bstep (se 1 (by rfl) ⟨1925015, by rfl⟩ : syracuseStep 2566687 = 3850031) B3850031
theorem B3422249 : Blo 2281435 3422249 := bstep (se 2 (by rfl) ⟨1283343, by rfl⟩ : syracuseStep 3422249 = 2566687) B2566687
theorem B2281499 : Blo 2281435 2281499 := bstep (se 1 (by rfl) ⟨1711124, by rfl⟩ : syracuseStep 2281499 = 3422249) B3422249
theorem B3083509 : Blo 2281435 3083509 := bbase (se 5 (by rfl) ⟨144539, by rfl⟩ : syracuseStep 3083509 = 289079) (by norm_num)
theorem B4111345 : Blo 2281435 4111345 := bstep (se 2 (by rfl) ⟨1541754, by rfl⟩ : syracuseStep 4111345 = 3083509) B3083509
theorem B5481793 : Blo 2281435 5481793 := bstep (se 2 (by rfl) ⟨2055672, by rfl⟩ : syracuseStep 5481793 = 4111345) B4111345
theorem B7309057 : Blo 2281435 7309057 := bstep (se 2 (by rfl) ⟨2740896, by rfl⟩ : syracuseStep 7309057 = 5481793) B5481793
theorem B9745409 : Blo 2281435 9745409 := bstep (se 2 (by rfl) ⟨3654528, by rfl⟩ : syracuseStep 9745409 = 7309057) B7309057
theorem B6496939 : Blo 2281435 6496939 := bstep (se 1 (by rfl) ⟨4872704, by rfl⟩ : syracuseStep 6496939 = 9745409) B9745409
theorem B8662585 : Blo 2281435 8662585 := bstep (se 2 (by rfl) ⟨3248469, by rfl⟩ : syracuseStep 8662585 = 6496939) B6496939
theorem B11550113 : Blo 2281435 11550113 := bstep (se 2 (by rfl) ⟨4331292, by rfl⟩ : syracuseStep 11550113 = 8662585) B8662585
theorem B7700075 : Blo 2281435 7700075 := bstep (se 1 (by rfl) ⟨5775056, by rfl⟩ : syracuseStep 7700075 = 11550113) B11550113
theorem B5133383 : Blo 2281435 5133383 := bstep (se 1 (by rfl) ⟨3850037, by rfl⟩ : syracuseStep 5133383 = 7700075) B7700075
theorem B3422255 : Blo 2281435 3422255 := bstep (se 1 (by rfl) ⟨2566691, by rfl⟩ : syracuseStep 3422255 = 5133383) B5133383
theorem B2281503 : Blo 2281435 2281503 := bstep (se 1 (by rfl) ⟨1711127, by rfl⟩ : syracuseStep 2281503 = 3422255) B3422255
theorem B3422261 : Blo 2281435 3422261 := bbase (se 5 (by rfl) ⟨160418, by rfl⟩ : syracuseStep 3422261 = 320837) (by norm_num)
theorem B2281507 : Blo 2281435 2281507 := bstep (se 1 (by rfl) ⟨1711130, by rfl⟩ : syracuseStep 2281507 = 3422261) B3422261
theorem B5775077 : Blo 2281435 5775077 := bbase (se 4 (by rfl) ⟨541413, by rfl⟩ : syracuseStep 5775077 = 1082827) (by norm_num)
theorem B3850051 : Blo 2281435 3850051 := bstep (se 1 (by rfl) ⟨2887538, by rfl⟩ : syracuseStep 3850051 = 5775077) B5775077
theorem B5133401 : Blo 2281435 5133401 := bstep (se 2 (by rfl) ⟨1925025, by rfl⟩ : syracuseStep 5133401 = 3850051) B3850051
theorem B3422267 : Blo 2281435 3422267 := bstep (se 1 (by rfl) ⟨2566700, by rfl⟩ : syracuseStep 3422267 = 5133401) B5133401
theorem B2281511 : Blo 2281435 2281511 := bstep (se 1 (by rfl) ⟨1711133, by rfl⟩ : syracuseStep 2281511 = 3422267) B3422267
theorem B2566705 : Blo 2281435 2566705 := bbase (se 2 (by rfl) ⟨962514, by rfl⟩ : syracuseStep 2566705 = 1925029) (by norm_num)
theorem B3422273 : Blo 2281435 3422273 := bstep (se 2 (by rfl) ⟨1283352, by rfl⟩ : syracuseStep 3422273 = 2566705) B2566705
theorem B2281515 : Blo 2281435 2281515 := bstep (se 1 (by rfl) ⟨1711136, by rfl⟩ : syracuseStep 2281515 = 3422273) B3422273
theorem B7309109 : Blo 2281435 7309109 := bbase (se 5 (by rfl) ⟨342614, by rfl⟩ : syracuseStep 7309109 = 685229) (by norm_num)
theorem B4872739 : Blo 2281435 4872739 := bstep (se 1 (by rfl) ⟨3654554, by rfl⟩ : syracuseStep 4872739 = 7309109) B7309109
theorem B6496985 : Blo 2281435 6496985 := bstep (se 2 (by rfl) ⟨2436369, by rfl⟩ : syracuseStep 6496985 = 4872739) B4872739
theorem B4331323 : Blo 2281435 4331323 := bstep (se 1 (by rfl) ⟨3248492, by rfl⟩ : syracuseStep 4331323 = 6496985) B6496985
theorem B5775097 : Blo 2281435 5775097 := bstep (se 2 (by rfl) ⟨2165661, by rfl⟩ : syracuseStep 5775097 = 4331323) B4331323
theorem B7700129 : Blo 2281435 7700129 := bstep (se 2 (by rfl) ⟨2887548, by rfl⟩ : syracuseStep 7700129 = 5775097) B5775097
theorem B5133419 : Blo 2281435 5133419 := bstep (se 1 (by rfl) ⟨3850064, by rfl⟩ : syracuseStep 5133419 = 7700129) B7700129
theorem B3422279 : Blo 2281435 3422279 := bstep (se 1 (by rfl) ⟨2566709, by rfl⟩ : syracuseStep 3422279 = 5133419) B5133419
theorem B2281519 : Blo 2281435 2281519 := bstep (se 1 (by rfl) ⟨1711139, by rfl⟩ : syracuseStep 2281519 = 3422279) B3422279
theorem B3422285 : Blo 2281435 3422285 := bbase (se 3 (by rfl) ⟨641678, by rfl⟩ : syracuseStep 3422285 = 1283357) (by norm_num)
theorem B2281523 : Blo 2281435 2281523 := bstep (se 1 (by rfl) ⟨1711142, by rfl⟩ : syracuseStep 2281523 = 3422285) B3422285
theorem B5133437 : Blo 2281435 5133437 := bbase (se 3 (by rfl) ⟨962519, by rfl⟩ : syracuseStep 5133437 = 1925039) (by norm_num)
theorem B3422291 : Blo 2281435 3422291 := bstep (se 1 (by rfl) ⟨2566718, by rfl⟩ : syracuseStep 3422291 = 5133437) B5133437
theorem B2281527 : Blo 2281435 2281527 := bstep (se 1 (by rfl) ⟨1711145, by rfl⟩ : syracuseStep 2281527 = 3422291) B3422291
theorem B3850085 : Blo 2281435 3850085 := bbase (se 4 (by rfl) ⟨360945, by rfl⟩ : syracuseStep 3850085 = 721891) (by norm_num)
theorem B2566723 : Blo 2281435 2566723 := bstep (se 1 (by rfl) ⟨1925042, by rfl⟩ : syracuseStep 2566723 = 3850085) B3850085
theorem B3422297 : Blo 2281435 3422297 := bstep (se 2 (by rfl) ⟨1283361, by rfl⟩ : syracuseStep 3422297 = 2566723) B2566723
theorem B2281531 : Blo 2281435 2281531 := bstep (se 1 (by rfl) ⟨1711148, by rfl⟩ : syracuseStep 2281531 = 3422297) B3422297
theorem B4872773 : Blo 2281435 4872773 := bbase (se 4 (by rfl) ⟨456822, by rfl⟩ : syracuseStep 4872773 = 913645) (by norm_num)
theorem B3248515 : Blo 2281435 3248515 := bstep (se 1 (by rfl) ⟨2436386, by rfl⟩ : syracuseStep 3248515 = 4872773) B4872773
theorem B17325413 : Blo 2281435 17325413 := bstep (se 4 (by rfl) ⟨1624257, by rfl⟩ : syracuseStep 17325413 = 3248515) B3248515
theorem B11550275 : Blo 2281435 11550275 := bstep (se 1 (by rfl) ⟨8662706, by rfl⟩ : syracuseStep 11550275 = 17325413) B17325413
theorem B7700183 : Blo 2281435 7700183 := bstep (se 1 (by rfl) ⟨5775137, by rfl⟩ : syracuseStep 7700183 = 11550275) B11550275
theorem B5133455 : Blo 2281435 5133455 := bstep (se 1 (by rfl) ⟨3850091, by rfl⟩ : syracuseStep 5133455 = 7700183) B7700183
theorem B3422303 : Blo 2281435 3422303 := bstep (se 1 (by rfl) ⟨2566727, by rfl⟩ : syracuseStep 3422303 = 5133455) B5133455
theorem B2281535 : Blo 2281435 2281535 := bstep (se 1 (by rfl) ⟨1711151, by rfl⟩ : syracuseStep 2281535 = 3422303) B3422303
theorem B3422309 : Blo 2281435 3422309 := bbase (se 4 (by rfl) ⟨320841, by rfl⟩ : syracuseStep 3422309 = 641683) (by norm_num)
theorem B2281539 : Blo 2281435 2281539 := bstep (se 1 (by rfl) ⟨1711154, by rfl⟩ : syracuseStep 2281539 = 3422309) B3422309
theorem B10963781 : Blo 2281435 10963781 := bbase (se 4 (by rfl) ⟨1027854, by rfl⟩ : syracuseStep 10963781 = 2055709) (by norm_num)
theorem B7309187 : Blo 2281435 7309187 := bstep (se 1 (by rfl) ⟨5481890, by rfl⟩ : syracuseStep 7309187 = 10963781) B10963781
theorem B4872791 : Blo 2281435 4872791 := bstep (se 1 (by rfl) ⟨3654593, by rfl⟩ : syracuseStep 4872791 = 7309187) B7309187
theorem B3248527 : Blo 2281435 3248527 := bstep (se 1 (by rfl) ⟨2436395, by rfl⟩ : syracuseStep 3248527 = 4872791) B4872791
theorem B4331369 : Blo 2281435 4331369 := bstep (se 2 (by rfl) ⟨1624263, by rfl⟩ : syracuseStep 4331369 = 3248527) B3248527
theorem B2887579 : Blo 2281435 2887579 := bstep (se 1 (by rfl) ⟨2165684, by rfl⟩ : syracuseStep 2887579 = 4331369) B4331369
theorem B3850105 : Blo 2281435 3850105 := bstep (se 2 (by rfl) ⟨1443789, by rfl⟩ : syracuseStep 3850105 = 2887579) B2887579
theorem B5133473 : Blo 2281435 5133473 := bstep (se 2 (by rfl) ⟨1925052, by rfl⟩ : syracuseStep 5133473 = 3850105) B3850105
theorem B3422315 : Blo 2281435 3422315 := bstep (se 1 (by rfl) ⟨2566736, by rfl⟩ : syracuseStep 3422315 = 5133473) B5133473
theorem B2281543 : Blo 2281435 2281543 := bstep (se 1 (by rfl) ⟨1711157, by rfl⟩ : syracuseStep 2281543 = 3422315) B3422315
theorem B2566741 : Blo 2281435 2566741 := bbase (se 8 (by rfl) ⟨15039, by rfl⟩ : syracuseStep 2566741 = 30079) (by norm_num)
theorem B3422321 : Blo 2281435 3422321 := bstep (se 2 (by rfl) ⟨1283370, by rfl⟩ : syracuseStep 3422321 = 2566741) B2566741
theorem B2281547 : Blo 2281435 2281547 := bstep (se 1 (by rfl) ⟨1711160, by rfl⟩ : syracuseStep 2281547 = 3422321) B3422321
theorem B2887589 : Blo 2281435 2887589 := bbase (se 4 (by rfl) ⟨270711, by rfl⟩ : syracuseStep 2887589 = 541423) (by norm_num)
theorem B7700237 : Blo 2281435 7700237 := bstep (se 3 (by rfl) ⟨1443794, by rfl⟩ : syracuseStep 7700237 = 2887589) B2887589
theorem B5133491 : Blo 2281435 5133491 := bstep (se 1 (by rfl) ⟨3850118, by rfl⟩ : syracuseStep 5133491 = 7700237) B7700237
theorem B3422327 : Blo 2281435 3422327 := bstep (se 1 (by rfl) ⟨2566745, by rfl⟩ : syracuseStep 3422327 = 5133491) B5133491
theorem B2281551 : Blo 2281435 2281551 := bstep (se 1 (by rfl) ⟨1711163, by rfl⟩ : syracuseStep 2281551 = 3422327) B3422327
theorem B3422333 : Blo 2281435 3422333 := bbase (se 3 (by rfl) ⟨641687, by rfl⟩ : syracuseStep 3422333 = 1283375) (by norm_num)
theorem B2281555 : Blo 2281435 2281555 := bstep (se 1 (by rfl) ⟨1711166, by rfl⟩ : syracuseStep 2281555 = 3422333) B3422333
theorem B5133509 : Blo 2281435 5133509 := bbase (se 4 (by rfl) ⟨481266, by rfl⟩ : syracuseStep 5133509 = 962533) (by norm_num)
theorem B3422339 : Blo 2281435 3422339 := bstep (se 1 (by rfl) ⟨2566754, by rfl⟩ : syracuseStep 3422339 = 5133509) B5133509
theorem B2281559 : Blo 2281435 2281559 := bstep (se 1 (by rfl) ⟨1711169, by rfl⟩ : syracuseStep 2281559 = 3422339) B3422339
theorem B2740969 : Blo 2281435 2740969 := bbase (se 2 (by rfl) ⟨1027863, by rfl⟩ : syracuseStep 2740969 = 2055727) (by norm_num)
theorem B14618501 : Blo 2281435 14618501 := bstep (se 4 (by rfl) ⟨1370484, by rfl⟩ : syracuseStep 14618501 = 2740969) B2740969
theorem B9745667 : Blo 2281435 9745667 := bstep (se 1 (by rfl) ⟨7309250, by rfl⟩ : syracuseStep 9745667 = 14618501) B14618501
theorem B6497111 : Blo 2281435 6497111 := bstep (se 1 (by rfl) ⟨4872833, by rfl⟩ : syracuseStep 6497111 = 9745667) B9745667
theorem B4331407 : Blo 2281435 4331407 := bstep (se 1 (by rfl) ⟨3248555, by rfl⟩ : syracuseStep 4331407 = 6497111) B6497111
theorem B5775209 : Blo 2281435 5775209 := bstep (se 2 (by rfl) ⟨2165703, by rfl⟩ : syracuseStep 5775209 = 4331407) B4331407
theorem B3850139 : Blo 2281435 3850139 := bstep (se 1 (by rfl) ⟨2887604, by rfl⟩ : syracuseStep 3850139 = 5775209) B5775209
theorem B2566759 : Blo 2281435 2566759 := bstep (se 1 (by rfl) ⟨1925069, by rfl⟩ : syracuseStep 2566759 = 3850139) B3850139
theorem B3422345 : Blo 2281435 3422345 := bstep (se 2 (by rfl) ⟨1283379, by rfl⟩ : syracuseStep 3422345 = 2566759) B2566759
theorem B2281563 : Blo 2281435 2281563 := bstep (se 1 (by rfl) ⟨1711172, by rfl⟩ : syracuseStep 2281563 = 3422345) B3422345
theorem B11550437 : Blo 2281435 11550437 := bbase (se 4 (by rfl) ⟨1082853, by rfl⟩ : syracuseStep 11550437 = 2165707) (by norm_num)
theorem B7700291 : Blo 2281435 7700291 := bstep (se 1 (by rfl) ⟨5775218, by rfl⟩ : syracuseStep 7700291 = 11550437) B11550437
theorem B5133527 : Blo 2281435 5133527 := bstep (se 1 (by rfl) ⟨3850145, by rfl⟩ : syracuseStep 5133527 = 7700291) B7700291
theorem B3422351 : Blo 2281435 3422351 := bstep (se 1 (by rfl) ⟨2566763, by rfl⟩ : syracuseStep 3422351 = 5133527) B5133527
theorem B2281567 : Blo 2281435 2281567 := bstep (se 1 (by rfl) ⟨1711175, by rfl⟩ : syracuseStep 2281567 = 3422351) B3422351
theorem B3422357 : Blo 2281435 3422357 := bbase (se 6 (by rfl) ⟨80211, by rfl⟩ : syracuseStep 3422357 = 160423) (by norm_num)
theorem B2281571 : Blo 2281435 2281571 := bstep (se 1 (by rfl) ⟨1711178, by rfl⟩ : syracuseStep 2281571 = 3422357) B3422357
theorem B9745717 : Blo 2281435 9745717 := bbase (se 5 (by rfl) ⟨456830, by rfl⟩ : syracuseStep 9745717 = 913661) (by norm_num)
theorem B12994289 : Blo 2281435 12994289 := bstep (se 2 (by rfl) ⟨4872858, by rfl⟩ : syracuseStep 12994289 = 9745717) B9745717
theorem B8662859 : Blo 2281435 8662859 := bstep (se 1 (by rfl) ⟨6497144, by rfl⟩ : syracuseStep 8662859 = 12994289) B12994289
theorem B5775239 : Blo 2281435 5775239 := bstep (se 1 (by rfl) ⟨4331429, by rfl⟩ : syracuseStep 5775239 = 8662859) B8662859
theorem B3850159 : Blo 2281435 3850159 := bstep (se 1 (by rfl) ⟨2887619, by rfl⟩ : syracuseStep 3850159 = 5775239) B5775239
theorem B5133545 : Blo 2281435 5133545 := bstep (se 2 (by rfl) ⟨1925079, by rfl⟩ : syracuseStep 5133545 = 3850159) B3850159
theorem B3422363 : Blo 2281435 3422363 := bstep (se 1 (by rfl) ⟨2566772, by rfl⟩ : syracuseStep 3422363 = 5133545) B5133545
theorem B2281575 : Blo 2281435 2281575 := bstep (se 1 (by rfl) ⟨1711181, by rfl⟩ : syracuseStep 2281575 = 3422363) B3422363
theorem B2566777 : Blo 2281435 2566777 := bbase (se 2 (by rfl) ⟨962541, by rfl⟩ : syracuseStep 2566777 = 1925083) (by norm_num)
theorem B3422369 : Blo 2281435 3422369 := bstep (se 2 (by rfl) ⟨1283388, by rfl⟩ : syracuseStep 3422369 = 2566777) B2566777
theorem B2281579 : Blo 2281435 2281579 := bstep (se 1 (by rfl) ⟨1711184, by rfl⟩ : syracuseStep 2281579 = 3422369) B3422369
theorem B2312713 : Blo 2281435 2312713 := bbase (se 2 (by rfl) ⟨867267, by rfl⟩ : syracuseStep 2312713 = 1734535) (by norm_num)
theorem B3083617 : Blo 2281435 3083617 := bstep (se 2 (by rfl) ⟨1156356, by rfl⟩ : syracuseStep 3083617 = 2312713) B2312713
theorem B4111489 : Blo 2281435 4111489 := bstep (se 2 (by rfl) ⟨1541808, by rfl⟩ : syracuseStep 4111489 = 3083617) B3083617
theorem B21927941 : Blo 2281435 21927941 := bstep (se 4 (by rfl) ⟨2055744, by rfl⟩ : syracuseStep 21927941 = 4111489) B4111489
theorem B14618627 : Blo 2281435 14618627 := bstep (se 1 (by rfl) ⟨10963970, by rfl⟩ : syracuseStep 14618627 = 21927941) B21927941
theorem B9745751 : Blo 2281435 9745751 := bstep (se 1 (by rfl) ⟨7309313, by rfl⟩ : syracuseStep 9745751 = 14618627) B14618627
theorem B6497167 : Blo 2281435 6497167 := bstep (se 1 (by rfl) ⟨4872875, by rfl⟩ : syracuseStep 6497167 = 9745751) B9745751
theorem B8662889 : Blo 2281435 8662889 := bstep (se 2 (by rfl) ⟨3248583, by rfl⟩ : syracuseStep 8662889 = 6497167) B6497167
theorem B5775259 : Blo 2281435 5775259 := bstep (se 1 (by rfl) ⟨4331444, by rfl⟩ : syracuseStep 5775259 = 8662889) B8662889
theorem B7700345 : Blo 2281435 7700345 := bstep (se 2 (by rfl) ⟨2887629, by rfl⟩ : syracuseStep 7700345 = 5775259) B5775259
theorem B5133563 : Blo 2281435 5133563 := bstep (se 1 (by rfl) ⟨3850172, by rfl⟩ : syracuseStep 5133563 = 7700345) B7700345
theorem B3422375 : Blo 2281435 3422375 := bstep (se 1 (by rfl) ⟨2566781, by rfl⟩ : syracuseStep 3422375 = 5133563) B5133563
theorem B2281583 : Blo 2281435 2281583 := bstep (se 1 (by rfl) ⟨1711187, by rfl⟩ : syracuseStep 2281583 = 3422375) B3422375
theorem B3422381 : Blo 2281435 3422381 := bbase (se 3 (by rfl) ⟨641696, by rfl⟩ : syracuseStep 3422381 = 1283393) (by norm_num)
theorem B2281587 : Blo 2281435 2281587 := bstep (se 1 (by rfl) ⟨1711190, by rfl⟩ : syracuseStep 2281587 = 3422381) B3422381
theorem B5133581 : Blo 2281435 5133581 := bbase (se 3 (by rfl) ⟨962546, by rfl⟩ : syracuseStep 5133581 = 1925093) (by norm_num)
theorem B3422387 : Blo 2281435 3422387 := bstep (se 1 (by rfl) ⟨2566790, by rfl⟩ : syracuseStep 3422387 = 5133581) B5133581
theorem B2281591 : Blo 2281435 2281591 := bstep (se 1 (by rfl) ⟨1711193, by rfl⟩ : syracuseStep 2281591 = 3422387) B3422387
theorem B2887645 : Blo 2281435 2887645 := bbase (se 3 (by rfl) ⟨541433, by rfl⟩ : syracuseStep 2887645 = 1082867) (by norm_num)
theorem B3850193 : Blo 2281435 3850193 := bstep (se 2 (by rfl) ⟨1443822, by rfl⟩ : syracuseStep 3850193 = 2887645) B2887645
theorem B2566795 : Blo 2281435 2566795 := bstep (se 1 (by rfl) ⟨1925096, by rfl⟩ : syracuseStep 2566795 = 3850193) B3850193
theorem B3422393 : Blo 2281435 3422393 := bstep (se 2 (by rfl) ⟨1283397, by rfl⟩ : syracuseStep 3422393 = 2566795) B2566795
theorem B2281595 : Blo 2281435 2281595 := bstep (se 1 (by rfl) ⟨1711196, by rfl⟩ : syracuseStep 2281595 = 3422393) B3422393
theorem B19491637 : Blo 2281435 19491637 := bbase (se 5 (by rfl) ⟨913670, by rfl⟩ : syracuseStep 19491637 = 1827341) (by norm_num)
theorem B25988849 : Blo 2281435 25988849 := bstep (se 2 (by rfl) ⟨9745818, by rfl⟩ : syracuseStep 25988849 = 19491637) B19491637
theorem B17325899 : Blo 2281435 17325899 := bstep (se 1 (by rfl) ⟨12994424, by rfl⟩ : syracuseStep 17325899 = 25988849) B25988849
theorem B11550599 : Blo 2281435 11550599 := bstep (se 1 (by rfl) ⟨8662949, by rfl⟩ : syracuseStep 11550599 = 17325899) B17325899
theorem B7700399 : Blo 2281435 7700399 := bstep (se 1 (by rfl) ⟨5775299, by rfl⟩ : syracuseStep 7700399 = 11550599) B11550599
theorem B5133599 : Blo 2281435 5133599 := bstep (se 1 (by rfl) ⟨3850199, by rfl⟩ : syracuseStep 5133599 = 7700399) B7700399
theorem B3422399 : Blo 2281435 3422399 := bstep (se 1 (by rfl) ⟨2566799, by rfl⟩ : syracuseStep 3422399 = 5133599) B5133599
theorem B2281599 : Blo 2281435 2281599 := bstep (se 1 (by rfl) ⟨1711199, by rfl⟩ : syracuseStep 2281599 = 3422399) B3422399
theorem B3422405 : Blo 2281435 3422405 := bbase (se 4 (by rfl) ⟨320850, by rfl⟩ : syracuseStep 3422405 = 641701) (by norm_num)
theorem B2281603 : Blo 2281435 2281603 := bstep (se 1 (by rfl) ⟨1711202, by rfl⟩ : syracuseStep 2281603 = 3422405) B3422405
theorem B3850213 : Blo 2281435 3850213 := bbase (se 4 (by rfl) ⟨360957, by rfl⟩ : syracuseStep 3850213 = 721915) (by norm_num)
theorem B5133617 : Blo 2281435 5133617 := bstep (se 2 (by rfl) ⟨1925106, by rfl⟩ : syracuseStep 5133617 = 3850213) B3850213
theorem B3422411 : Blo 2281435 3422411 := bstep (se 1 (by rfl) ⟨2566808, by rfl⟩ : syracuseStep 3422411 = 5133617) B5133617
theorem B2281607 : Blo 2281435 2281607 := bstep (se 1 (by rfl) ⟨1711205, by rfl⟩ : syracuseStep 2281607 = 3422411) B3422411
theorem B2566813 : Blo 2281435 2566813 := bbase (se 3 (by rfl) ⟨481277, by rfl⟩ : syracuseStep 2566813 = 962555) (by norm_num)
theorem B3422417 : Blo 2281435 3422417 := bstep (se 2 (by rfl) ⟨1283406, by rfl⟩ : syracuseStep 3422417 = 2566813) B2566813
theorem B2281611 : Blo 2281435 2281611 := bstep (se 1 (by rfl) ⟨1711208, by rfl⟩ : syracuseStep 2281611 = 3422417) B3422417
theorem B7700453 : Blo 2281435 7700453 := bbase (se 4 (by rfl) ⟨721917, by rfl⟩ : syracuseStep 7700453 = 1443835) (by norm_num)
theorem B5133635 : Blo 2281435 5133635 := bstep (se 1 (by rfl) ⟨3850226, by rfl⟩ : syracuseStep 5133635 = 7700453) B7700453
theorem B3422423 : Blo 2281435 3422423 := bstep (se 1 (by rfl) ⟨2566817, by rfl⟩ : syracuseStep 3422423 = 5133635) B5133635
theorem B2281615 : Blo 2281435 2281615 := bstep (se 1 (by rfl) ⟨1711211, by rfl⟩ : syracuseStep 2281615 = 3422423) B3422423
theorem B3422429 : Blo 2281435 3422429 := bbase (se 3 (by rfl) ⟨641705, by rfl⟩ : syracuseStep 3422429 = 1283411) (by norm_num)
theorem B2281619 : Blo 2281435 2281619 := bstep (se 1 (by rfl) ⟨1711214, by rfl⟩ : syracuseStep 2281619 = 3422429) B3422429
theorem B5133653 : Blo 2281435 5133653 := bbase (se 16 (by rfl) ⟨117, by rfl⟩ : syracuseStep 5133653 = 235) (by norm_num)
theorem B3422435 : Blo 2281435 3422435 := bstep (se 1 (by rfl) ⟨2566826, by rfl⟩ : syracuseStep 3422435 = 5133653) B5133653
theorem B2281623 : Blo 2281435 2281623 := bstep (se 1 (by rfl) ⟨1711217, by rfl⟩ : syracuseStep 2281623 = 3422435) B3422435
theorem B2436485 : Blo 2281435 2436485 := bbase (se 4 (by rfl) ⟨228420, by rfl⟩ : syracuseStep 2436485 = 456841) (by norm_num)
theorem B6497293 : Blo 2281435 6497293 := bstep (se 3 (by rfl) ⟨1218242, by rfl⟩ : syracuseStep 6497293 = 2436485) B2436485
theorem B8663057 : Blo 2281435 8663057 := bstep (se 2 (by rfl) ⟨3248646, by rfl⟩ : syracuseStep 8663057 = 6497293) B6497293
theorem B5775371 : Blo 2281435 5775371 := bstep (se 1 (by rfl) ⟨4331528, by rfl⟩ : syracuseStep 5775371 = 8663057) B8663057
theorem B3850247 : Blo 2281435 3850247 := bstep (se 1 (by rfl) ⟨2887685, by rfl⟩ : syracuseStep 3850247 = 5775371) B5775371
theorem B2566831 : Blo 2281435 2566831 := bstep (se 1 (by rfl) ⟨1925123, by rfl⟩ : syracuseStep 2566831 = 3850247) B3850247
theorem B3422441 : Blo 2281435 3422441 := bstep (se 2 (by rfl) ⟨1283415, by rfl⟩ : syracuseStep 3422441 = 2566831) B2566831
theorem B2281627 : Blo 2281435 2281627 := bstep (se 1 (by rfl) ⟨1711220, by rfl⟩ : syracuseStep 2281627 = 3422441) B3422441
theorem B6251509 : Blo 2281435 6251509 := bbase (se 5 (by rfl) ⟨293039, by rfl⟩ : syracuseStep 6251509 = 586079) (by norm_num)
theorem B8335345 : Blo 2281435 8335345 := bstep (se 2 (by rfl) ⟨3125754, by rfl⟩ : syracuseStep 8335345 = 6251509) B6251509
theorem B11113793 : Blo 2281435 11113793 := bstep (se 2 (by rfl) ⟨4167672, by rfl⟩ : syracuseStep 11113793 = 8335345) B8335345
theorem B7409195 : Blo 2281435 7409195 := bstep (se 1 (by rfl) ⟨5556896, by rfl⟩ : syracuseStep 7409195 = 11113793) B11113793
theorem B4939463 : Blo 2281435 4939463 := bstep (se 1 (by rfl) ⟨3704597, by rfl⟩ : syracuseStep 4939463 = 7409195) B7409195
theorem B3292975 : Blo 2281435 3292975 := bstep (se 1 (by rfl) ⟨2469731, by rfl⟩ : syracuseStep 3292975 = 4939463) B4939463
theorem B4390633 : Blo 2281435 4390633 := bstep (se 2 (by rfl) ⟨1646487, by rfl⟩ : syracuseStep 4390633 = 3292975) B3292975
theorem B5854177 : Blo 2281435 5854177 := bstep (se 2 (by rfl) ⟨2195316, by rfl⟩ : syracuseStep 5854177 = 4390633) B4390633
theorem B7805569 : Blo 2281435 7805569 := bstep (se 2 (by rfl) ⟨2927088, by rfl⟩ : syracuseStep 7805569 = 5854177) B5854177
theorem B10407425 : Blo 2281435 10407425 := bstep (se 2 (by rfl) ⟨3902784, by rfl⟩ : syracuseStep 10407425 = 7805569) B7805569
theorem B27753133 : Blo 2281435 27753133 := bstep (se 3 (by rfl) ⟨5203712, by rfl⟩ : syracuseStep 27753133 = 10407425) B10407425
theorem B37004177 : Blo 2281435 37004177 := bstep (se 2 (by rfl) ⟨13876566, by rfl⟩ : syracuseStep 37004177 = 27753133) B27753133
theorem B24669451 : Blo 2281435 24669451 := bstep (se 1 (by rfl) ⟨18502088, by rfl⟩ : syracuseStep 24669451 = 37004177) B37004177
theorem B32892601 : Blo 2281435 32892601 := bstep (se 2 (by rfl) ⟨12334725, by rfl⟩ : syracuseStep 32892601 = 24669451) B24669451
theorem B43856801 : Blo 2281435 43856801 := bstep (se 2 (by rfl) ⟨16446300, by rfl⟩ : syracuseStep 43856801 = 32892601) B32892601
theorem B29237867 : Blo 2281435 29237867 := bstep (se 1 (by rfl) ⟨21928400, by rfl⟩ : syracuseStep 29237867 = 43856801) B43856801
theorem B19491911 : Blo 2281435 19491911 := bstep (se 1 (by rfl) ⟨14618933, by rfl⟩ : syracuseStep 19491911 = 29237867) B29237867
theorem B12994607 : Blo 2281435 12994607 := bstep (se 1 (by rfl) ⟨9745955, by rfl⟩ : syracuseStep 12994607 = 19491911) B19491911
theorem B8663071 : Blo 2281435 8663071 := bstep (se 1 (by rfl) ⟨6497303, by rfl⟩ : syracuseStep 8663071 = 12994607) B12994607
theorem B11550761 : Blo 2281435 11550761 := bstep (se 2 (by rfl) ⟨4331535, by rfl⟩ : syracuseStep 11550761 = 8663071) B8663071
theorem B7700507 : Blo 2281435 7700507 := bstep (se 1 (by rfl) ⟨5775380, by rfl⟩ : syracuseStep 7700507 = 11550761) B11550761
theorem B5133671 : Blo 2281435 5133671 := bstep (se 1 (by rfl) ⟨3850253, by rfl⟩ : syracuseStep 5133671 = 7700507) B7700507
theorem B3422447 : Blo 2281435 3422447 := bstep (se 1 (by rfl) ⟨2566835, by rfl⟩ : syracuseStep 3422447 = 5133671) B5133671
theorem B2281631 : Blo 2281435 2281631 := bstep (se 1 (by rfl) ⟨1711223, by rfl⟩ : syracuseStep 2281631 = 3422447) B3422447
theorem B3422453 : Blo 2281435 3422453 := bbase (se 5 (by rfl) ⟨160427, by rfl⟩ : syracuseStep 3422453 = 320855) (by norm_num)
theorem B2281635 : Blo 2281435 2281635 := bstep (se 1 (by rfl) ⟨1711226, by rfl⟩ : syracuseStep 2281635 = 3422453) B3422453
theorem B6938309 : Blo 2281435 6938309 := bbase (se 4 (by rfl) ⟨650466, by rfl⟩ : syracuseStep 6938309 = 1300933) (by norm_num)
theorem B18502157 : Blo 2281435 18502157 := bstep (se 3 (by rfl) ⟨3469154, by rfl⟩ : syracuseStep 18502157 = 6938309) B6938309
theorem B12334771 : Blo 2281435 12334771 := bstep (se 1 (by rfl) ⟨9251078, by rfl⟩ : syracuseStep 12334771 = 18502157) B18502157
theorem B16446361 : Blo 2281435 16446361 := bstep (se 2 (by rfl) ⟨6167385, by rfl⟩ : syracuseStep 16446361 = 12334771) B12334771
theorem B21928481 : Blo 2281435 21928481 := bstep (se 2 (by rfl) ⟨8223180, by rfl⟩ : syracuseStep 21928481 = 16446361) B16446361
theorem B14618987 : Blo 2281435 14618987 := bstep (se 1 (by rfl) ⟨10964240, by rfl⟩ : syracuseStep 14618987 = 21928481) B21928481
theorem B9745991 : Blo 2281435 9745991 := bstep (se 1 (by rfl) ⟨7309493, by rfl⟩ : syracuseStep 9745991 = 14618987) B14618987
theorem B6497327 : Blo 2281435 6497327 := bstep (se 1 (by rfl) ⟨4872995, by rfl⟩ : syracuseStep 6497327 = 9745991) B9745991
theorem B4331551 : Blo 2281435 4331551 := bstep (se 1 (by rfl) ⟨3248663, by rfl⟩ : syracuseStep 4331551 = 6497327) B6497327
theorem B5775401 : Blo 2281435 5775401 := bstep (se 2 (by rfl) ⟨2165775, by rfl⟩ : syracuseStep 5775401 = 4331551) B4331551
theorem B3850267 : Blo 2281435 3850267 := bstep (se 1 (by rfl) ⟨2887700, by rfl⟩ : syracuseStep 3850267 = 5775401) B5775401
theorem B5133689 : Blo 2281435 5133689 := bstep (se 2 (by rfl) ⟨1925133, by rfl⟩ : syracuseStep 5133689 = 3850267) B3850267
theorem B3422459 : Blo 2281435 3422459 := bstep (se 1 (by rfl) ⟨2566844, by rfl⟩ : syracuseStep 3422459 = 5133689) B5133689
theorem B2281639 : Blo 2281435 2281639 := bstep (se 1 (by rfl) ⟨1711229, by rfl⟩ : syracuseStep 2281639 = 3422459) B3422459
theorem B2566849 : Blo 2281435 2566849 := bbase (se 2 (by rfl) ⟨962568, by rfl⟩ : syracuseStep 2566849 = 1925137) (by norm_num)
theorem B3422465 : Blo 2281435 3422465 := bstep (se 2 (by rfl) ⟨1283424, by rfl⟩ : syracuseStep 3422465 = 2566849) B2566849
theorem B2281643 : Blo 2281435 2281643 := bstep (se 1 (by rfl) ⟨1711232, by rfl⟩ : syracuseStep 2281643 = 3422465) B3422465
theorem B5775421 : Blo 2281435 5775421 := bbase (se 3 (by rfl) ⟨1082891, by rfl⟩ : syracuseStep 5775421 = 2165783) (by norm_num)
theorem B7700561 : Blo 2281435 7700561 := bstep (se 2 (by rfl) ⟨2887710, by rfl⟩ : syracuseStep 7700561 = 5775421) B5775421
theorem B5133707 : Blo 2281435 5133707 := bstep (se 1 (by rfl) ⟨3850280, by rfl⟩ : syracuseStep 5133707 = 7700561) B7700561
theorem B3422471 : Blo 2281435 3422471 := bstep (se 1 (by rfl) ⟨2566853, by rfl⟩ : syracuseStep 3422471 = 5133707) B5133707
theorem B2281647 : Blo 2281435 2281647 := bstep (se 1 (by rfl) ⟨1711235, by rfl⟩ : syracuseStep 2281647 = 3422471) B3422471
theorem B3422477 : Blo 2281435 3422477 := bbase (se 3 (by rfl) ⟨641714, by rfl⟩ : syracuseStep 3422477 = 1283429) (by norm_num)
theorem B2281651 : Blo 2281435 2281651 := bstep (se 1 (by rfl) ⟨1711238, by rfl⟩ : syracuseStep 2281651 = 3422477) B3422477
theorem B5133725 : Blo 2281435 5133725 := bbase (se 3 (by rfl) ⟨962573, by rfl⟩ : syracuseStep 5133725 = 1925147) (by norm_num)
theorem B3422483 : Blo 2281435 3422483 := bstep (se 1 (by rfl) ⟨2566862, by rfl⟩ : syracuseStep 3422483 = 5133725) B5133725
theorem B2281655 : Blo 2281435 2281655 := bstep (se 1 (by rfl) ⟨1711241, by rfl⟩ : syracuseStep 2281655 = 3422483) B3422483
theorem B3850301 : Blo 2281435 3850301 := bbase (se 3 (by rfl) ⟨721931, by rfl⟩ : syracuseStep 3850301 = 1443863) (by norm_num)
theorem B2566867 : Blo 2281435 2566867 := bstep (se 1 (by rfl) ⟨1925150, by rfl⟩ : syracuseStep 2566867 = 3850301) B3850301
theorem B3422489 : Blo 2281435 3422489 := bstep (se 2 (by rfl) ⟨1283433, by rfl⟩ : syracuseStep 3422489 = 2566867) B2566867
theorem B2281659 : Blo 2281435 2281659 := bstep (se 1 (by rfl) ⟨1711244, by rfl⟩ : syracuseStep 2281659 = 3422489) B3422489
theorem B2741089 : Blo 2281435 2741089 := bbase (se 2 (by rfl) ⟨1027908, by rfl⟩ : syracuseStep 2741089 = 2055817) (by norm_num)
theorem B3654785 : Blo 2281435 3654785 := bstep (se 2 (by rfl) ⟨1370544, by rfl⟩ : syracuseStep 3654785 = 2741089) B2741089
theorem B2436523 : Blo 2281435 2436523 := bstep (se 1 (by rfl) ⟨1827392, by rfl⟩ : syracuseStep 2436523 = 3654785) B3654785
theorem B12994789 : Blo 2281435 12994789 := bstep (se 4 (by rfl) ⟨1218261, by rfl⟩ : syracuseStep 12994789 = 2436523) B2436523
theorem B17326385 : Blo 2281435 17326385 := bstep (se 2 (by rfl) ⟨6497394, by rfl⟩ : syracuseStep 17326385 = 12994789) B12994789
theorem B11550923 : Blo 2281435 11550923 := bstep (se 1 (by rfl) ⟨8663192, by rfl⟩ : syracuseStep 11550923 = 17326385) B17326385
theorem B7700615 : Blo 2281435 7700615 := bstep (se 1 (by rfl) ⟨5775461, by rfl⟩ : syracuseStep 7700615 = 11550923) B11550923
theorem B5133743 : Blo 2281435 5133743 := bstep (se 1 (by rfl) ⟨3850307, by rfl⟩ : syracuseStep 5133743 = 7700615) B7700615
theorem B3422495 : Blo 2281435 3422495 := bstep (se 1 (by rfl) ⟨2566871, by rfl⟩ : syracuseStep 3422495 = 5133743) B5133743
theorem B2281663 : Blo 2281435 2281663 := bstep (se 1 (by rfl) ⟨1711247, by rfl⟩ : syracuseStep 2281663 = 3422495) B3422495
theorem B3422501 : Blo 2281435 3422501 := bbase (se 4 (by rfl) ⟨320859, by rfl⟩ : syracuseStep 3422501 = 641719) (by norm_num)
theorem B2281667 : Blo 2281435 2281667 := bstep (se 1 (by rfl) ⟨1711250, by rfl⟩ : syracuseStep 2281667 = 3422501) B3422501
theorem B2887741 : Blo 2281435 2887741 := bbase (se 3 (by rfl) ⟨541451, by rfl⟩ : syracuseStep 2887741 = 1082903) (by norm_num)
theorem B3850321 : Blo 2281435 3850321 := bstep (se 2 (by rfl) ⟨1443870, by rfl⟩ : syracuseStep 3850321 = 2887741) B2887741
theorem B5133761 : Blo 2281435 5133761 := bstep (se 2 (by rfl) ⟨1925160, by rfl⟩ : syracuseStep 5133761 = 3850321) B3850321
theorem B3422507 : Blo 2281435 3422507 := bstep (se 1 (by rfl) ⟨2566880, by rfl⟩ : syracuseStep 3422507 = 5133761) B5133761
theorem B2281671 : Blo 2281435 2281671 := bstep (se 1 (by rfl) ⟨1711253, by rfl⟩ : syracuseStep 2281671 = 3422507) B3422507
theorem B2566885 : Blo 2281435 2566885 := bbase (se 4 (by rfl) ⟨240645, by rfl⟩ : syracuseStep 2566885 = 481291) (by norm_num)
theorem B3422513 : Blo 2281435 3422513 := bstep (se 2 (by rfl) ⟨1283442, by rfl⟩ : syracuseStep 3422513 = 2566885) B2566885
theorem B2281675 : Blo 2281435 2281675 := bstep (se 1 (by rfl) ⟨1711256, by rfl⟩ : syracuseStep 2281675 = 3422513) B3422513
theorem B12503285 : Blo 2281435 12503285 := bbase (se 5 (by rfl) ⟨586091, by rfl⟩ : syracuseStep 12503285 = 1172183) (by norm_num)
theorem B8335523 : Blo 2281435 8335523 := bstep (se 1 (by rfl) ⟨6251642, by rfl⟩ : syracuseStep 8335523 = 12503285) B12503285
theorem B5557015 : Blo 2281435 5557015 := bstep (se 1 (by rfl) ⟨4167761, by rfl⟩ : syracuseStep 5557015 = 8335523) B8335523
theorem B29637413 : Blo 2281435 29637413 := bstep (se 4 (by rfl) ⟨2778507, by rfl⟩ : syracuseStep 29637413 = 5557015) B5557015
theorem B19758275 : Blo 2281435 19758275 := bstep (se 1 (by rfl) ⟨14818706, by rfl⟩ : syracuseStep 19758275 = 29637413) B29637413
theorem B13172183 : Blo 2281435 13172183 := bstep (se 1 (by rfl) ⟨9879137, by rfl⟩ : syracuseStep 13172183 = 19758275) B19758275
theorem B8781455 : Blo 2281435 8781455 := bstep (se 1 (by rfl) ⟨6586091, by rfl⟩ : syracuseStep 8781455 = 13172183) B13172183
theorem B5854303 : Blo 2281435 5854303 := bstep (se 1 (by rfl) ⟨4390727, by rfl⟩ : syracuseStep 5854303 = 8781455) B8781455
theorem B7805737 : Blo 2281435 7805737 := bstep (se 2 (by rfl) ⟨2927151, by rfl⟩ : syracuseStep 7805737 = 5854303) B5854303
theorem B10407649 : Blo 2281435 10407649 := bstep (se 2 (by rfl) ⟨3902868, by rfl⟩ : syracuseStep 10407649 = 7805737) B7805737
theorem B13876865 : Blo 2281435 13876865 := bstep (se 2 (by rfl) ⟨5203824, by rfl⟩ : syracuseStep 13876865 = 10407649) B10407649
theorem B9251243 : Blo 2281435 9251243 := bstep (se 1 (by rfl) ⟨6938432, by rfl⟩ : syracuseStep 9251243 = 13876865) B13876865
theorem B6167495 : Blo 2281435 6167495 := bstep (se 1 (by rfl) ⟨4625621, by rfl⟩ : syracuseStep 6167495 = 9251243) B9251243
theorem B4111663 : Blo 2281435 4111663 := bstep (se 1 (by rfl) ⟨3083747, by rfl⟩ : syracuseStep 4111663 = 6167495) B6167495
theorem B5482217 : Blo 2281435 5482217 := bstep (se 2 (by rfl) ⟨2055831, by rfl⟩ : syracuseStep 5482217 = 4111663) B4111663
theorem B3654811 : Blo 2281435 3654811 := bstep (se 1 (by rfl) ⟨2741108, by rfl⟩ : syracuseStep 3654811 = 5482217) B5482217
theorem B4873081 : Blo 2281435 4873081 := bstep (se 2 (by rfl) ⟨1827405, by rfl⟩ : syracuseStep 4873081 = 3654811) B3654811
theorem B6497441 : Blo 2281435 6497441 := bstep (se 2 (by rfl) ⟨2436540, by rfl⟩ : syracuseStep 6497441 = 4873081) B4873081
theorem B4331627 : Blo 2281435 4331627 := bstep (se 1 (by rfl) ⟨3248720, by rfl⟩ : syracuseStep 4331627 = 6497441) B6497441
theorem B2887751 : Blo 2281435 2887751 := bstep (se 1 (by rfl) ⟨2165813, by rfl⟩ : syracuseStep 2887751 = 4331627) B4331627
theorem B7700669 : Blo 2281435 7700669 := bstep (se 3 (by rfl) ⟨1443875, by rfl⟩ : syracuseStep 7700669 = 2887751) B2887751
theorem B5133779 : Blo 2281435 5133779 := bstep (se 1 (by rfl) ⟨3850334, by rfl⟩ : syracuseStep 5133779 = 7700669) B7700669
theorem B3422519 : Blo 2281435 3422519 := bstep (se 1 (by rfl) ⟨2566889, by rfl⟩ : syracuseStep 3422519 = 5133779) B5133779
theorem B2281679 : Blo 2281435 2281679 := bstep (se 1 (by rfl) ⟨1711259, by rfl⟩ : syracuseStep 2281679 = 3422519) B3422519
theorem B3422525 : Blo 2281435 3422525 := bbase (se 3 (by rfl) ⟨641723, by rfl⟩ : syracuseStep 3422525 = 1283447) (by norm_num)
theorem B2281683 : Blo 2281435 2281683 := bstep (se 1 (by rfl) ⟨1711262, by rfl⟩ : syracuseStep 2281683 = 3422525) B3422525
theorem B5133797 : Blo 2281435 5133797 := bbase (se 4 (by rfl) ⟨481293, by rfl⟩ : syracuseStep 5133797 = 962587) (by norm_num)
theorem B3422531 : Blo 2281435 3422531 := bstep (se 1 (by rfl) ⟨2566898, by rfl⟩ : syracuseStep 3422531 = 5133797) B5133797
theorem B2281687 : Blo 2281435 2281687 := bstep (se 1 (by rfl) ⟨1711265, by rfl⟩ : syracuseStep 2281687 = 3422531) B3422531
theorem B5775533 : Blo 2281435 5775533 := bbase (se 3 (by rfl) ⟨1082912, by rfl⟩ : syracuseStep 5775533 = 2165825) (by norm_num)
theorem B3850355 : Blo 2281435 3850355 := bstep (se 1 (by rfl) ⟨2887766, by rfl⟩ : syracuseStep 3850355 = 5775533) B5775533
theorem B2566903 : Blo 2281435 2566903 := bstep (se 1 (by rfl) ⟨1925177, by rfl⟩ : syracuseStep 2566903 = 3850355) B3850355
theorem B3422537 : Blo 2281435 3422537 := bstep (se 2 (by rfl) ⟨1283451, by rfl⟩ : syracuseStep 3422537 = 2566903) B2566903
theorem B2281691 : Blo 2281435 2281691 := bstep (se 1 (by rfl) ⟨1711268, by rfl⟩ : syracuseStep 2281691 = 3422537) B3422537
theorem B18502613 : Blo 2281435 18502613 := bbase (se 7 (by rfl) ⟨216827, by rfl⟩ : syracuseStep 18502613 = 433655) (by norm_num)
theorem B12335075 : Blo 2281435 12335075 := bstep (se 1 (by rfl) ⟨9251306, by rfl⟩ : syracuseStep 12335075 = 18502613) B18502613
theorem B8223383 : Blo 2281435 8223383 := bstep (se 1 (by rfl) ⟨6167537, by rfl⟩ : syracuseStep 8223383 = 12335075) B12335075
theorem B5482255 : Blo 2281435 5482255 := bstep (se 1 (by rfl) ⟨4111691, by rfl⟩ : syracuseStep 5482255 = 8223383) B8223383
theorem B7309673 : Blo 2281435 7309673 := bstep (se 2 (by rfl) ⟨2741127, by rfl⟩ : syracuseStep 7309673 = 5482255) B5482255
theorem B4873115 : Blo 2281435 4873115 := bstep (se 1 (by rfl) ⟨3654836, by rfl⟩ : syracuseStep 4873115 = 7309673) B7309673
theorem B3248743 : Blo 2281435 3248743 := bstep (se 1 (by rfl) ⟨2436557, by rfl⟩ : syracuseStep 3248743 = 4873115) B4873115
theorem B4331657 : Blo 2281435 4331657 := bstep (se 2 (by rfl) ⟨1624371, by rfl⟩ : syracuseStep 4331657 = 3248743) B3248743
theorem B11551085 : Blo 2281435 11551085 := bstep (se 3 (by rfl) ⟨2165828, by rfl⟩ : syracuseStep 11551085 = 4331657) B4331657
theorem B7700723 : Blo 2281435 7700723 := bstep (se 1 (by rfl) ⟨5775542, by rfl⟩ : syracuseStep 7700723 = 11551085) B11551085
theorem B5133815 : Blo 2281435 5133815 := bstep (se 1 (by rfl) ⟨3850361, by rfl⟩ : syracuseStep 5133815 = 7700723) B7700723
theorem B3422543 : Blo 2281435 3422543 := bstep (se 1 (by rfl) ⟨2566907, by rfl⟩ : syracuseStep 3422543 = 5133815) B5133815
theorem B2281695 : Blo 2281435 2281695 := bstep (se 1 (by rfl) ⟨1711271, by rfl⟩ : syracuseStep 2281695 = 3422543) B3422543
theorem B3422549 : Blo 2281435 3422549 := bbase (se 10 (by rfl) ⟨5013, by rfl⟩ : syracuseStep 3422549 = 10027) (by norm_num)
theorem B2281699 : Blo 2281435 2281699 := bstep (se 1 (by rfl) ⟨1711274, by rfl⟩ : syracuseStep 2281699 = 3422549) B3422549
theorem B6497509 : Blo 2281435 6497509 := bbase (se 4 (by rfl) ⟨609141, by rfl⟩ : syracuseStep 6497509 = 1218283) (by norm_num)
theorem B8663345 : Blo 2281435 8663345 := bstep (se 2 (by rfl) ⟨3248754, by rfl⟩ : syracuseStep 8663345 = 6497509) B6497509
theorem B5775563 : Blo 2281435 5775563 := bstep (se 1 (by rfl) ⟨4331672, by rfl⟩ : syracuseStep 5775563 = 8663345) B8663345
theorem B3850375 : Blo 2281435 3850375 := bstep (se 1 (by rfl) ⟨2887781, by rfl⟩ : syracuseStep 3850375 = 5775563) B5775563
theorem B5133833 : Blo 2281435 5133833 := bstep (se 2 (by rfl) ⟨1925187, by rfl⟩ : syracuseStep 5133833 = 3850375) B3850375
theorem B3422555 : Blo 2281435 3422555 := bstep (se 1 (by rfl) ⟨2566916, by rfl⟩ : syracuseStep 3422555 = 5133833) B5133833
theorem B2281703 : Blo 2281435 2281703 := bstep (se 1 (by rfl) ⟨1711277, by rfl⟩ : syracuseStep 2281703 = 3422555) B3422555
theorem B2566921 : Blo 2281435 2566921 := bbase (se 2 (by rfl) ⟨962595, by rfl⟩ : syracuseStep 2566921 = 1925191) (by norm_num)
theorem B3422561 : Blo 2281435 3422561 := bstep (se 2 (by rfl) ⟨1283460, by rfl⟩ : syracuseStep 3422561 = 2566921) B2566921
theorem B2281707 : Blo 2281435 2281707 := bstep (se 1 (by rfl) ⟨1711280, by rfl⟩ : syracuseStep 2281707 = 3422561) B3422561
theorem B4450693 : Blo 2281435 4450693 := bbase (se 4 (by rfl) ⟨417252, by rfl⟩ : syracuseStep 4450693 = 834505) (by norm_num)
theorem B5934257 : Blo 2281435 5934257 := bstep (se 2 (by rfl) ⟨2225346, by rfl⟩ : syracuseStep 5934257 = 4450693) B4450693
theorem B3956171 : Blo 2281435 3956171 := bstep (se 1 (by rfl) ⟨2967128, by rfl⟩ : syracuseStep 3956171 = 5934257) B5934257
theorem B42199157 : Blo 2281435 42199157 := bstep (se 5 (by rfl) ⟨1978085, by rfl⟩ : syracuseStep 42199157 = 3956171) B3956171
theorem B28132771 : Blo 2281435 28132771 := bstep (se 1 (by rfl) ⟨21099578, by rfl⟩ : syracuseStep 28132771 = 42199157) B42199157
theorem B37510361 : Blo 2281435 37510361 := bstep (se 2 (by rfl) ⟨14066385, by rfl⟩ : syracuseStep 37510361 = 28132771) B28132771
theorem B25006907 : Blo 2281435 25006907 := bstep (se 1 (by rfl) ⟨18755180, by rfl⟩ : syracuseStep 25006907 = 37510361) B37510361
theorem B16671271 : Blo 2281435 16671271 := bstep (se 1 (by rfl) ⟨12503453, by rfl⟩ : syracuseStep 16671271 = 25006907) B25006907
theorem B22228361 : Blo 2281435 22228361 := bstep (se 2 (by rfl) ⟨8335635, by rfl⟩ : syracuseStep 22228361 = 16671271) B16671271
theorem B14818907 : Blo 2281435 14818907 := bstep (se 1 (by rfl) ⟨11114180, by rfl⟩ : syracuseStep 14818907 = 22228361) B22228361
theorem B39517085 : Blo 2281435 39517085 := bstep (se 3 (by rfl) ⟨7409453, by rfl⟩ : syracuseStep 39517085 = 14818907) B14818907
theorem B26344723 : Blo 2281435 26344723 := bstep (se 1 (by rfl) ⟨19758542, by rfl⟩ : syracuseStep 26344723 = 39517085) B39517085
theorem B35126297 : Blo 2281435 35126297 := bstep (se 2 (by rfl) ⟨13172361, by rfl⟩ : syracuseStep 35126297 = 26344723) B26344723
theorem B23417531 : Blo 2281435 23417531 := bstep (se 1 (by rfl) ⟨17563148, by rfl⟩ : syracuseStep 23417531 = 35126297) B35126297
theorem B15611687 : Blo 2281435 15611687 := bstep (se 1 (by rfl) ⟨11708765, by rfl⟩ : syracuseStep 15611687 = 23417531) B23417531
theorem B10407791 : Blo 2281435 10407791 := bstep (se 1 (by rfl) ⟨7805843, by rfl⟩ : syracuseStep 10407791 = 15611687) B15611687
theorem B27754109 : Blo 2281435 27754109 := bstep (se 3 (by rfl) ⟨5203895, by rfl⟩ : syracuseStep 27754109 = 10407791) B10407791
theorem B18502739 : Blo 2281435 18502739 := bstep (se 1 (by rfl) ⟨13877054, by rfl⟩ : syracuseStep 18502739 = 27754109) B27754109
theorem B12335159 : Blo 2281435 12335159 := bstep (se 1 (by rfl) ⟨9251369, by rfl⟩ : syracuseStep 12335159 = 18502739) B18502739
theorem B8223439 : Blo 2281435 8223439 := bstep (se 1 (by rfl) ⟨6167579, by rfl⟩ : syracuseStep 8223439 = 12335159) B12335159
theorem B10964585 : Blo 2281435 10964585 := bstep (se 2 (by rfl) ⟨4111719, by rfl⟩ : syracuseStep 10964585 = 8223439) B8223439
theorem B29238893 : Blo 2281435 29238893 := bstep (se 3 (by rfl) ⟨5482292, by rfl⟩ : syracuseStep 29238893 = 10964585) B10964585
theorem B19492595 : Blo 2281435 19492595 := bstep (se 1 (by rfl) ⟨14619446, by rfl⟩ : syracuseStep 19492595 = 29238893) B29238893
theorem B12995063 : Blo 2281435 12995063 := bstep (se 1 (by rfl) ⟨9746297, by rfl⟩ : syracuseStep 12995063 = 19492595) B19492595
theorem B8663375 : Blo 2281435 8663375 := bstep (se 1 (by rfl) ⟨6497531, by rfl⟩ : syracuseStep 8663375 = 12995063) B12995063
theorem B5775583 : Blo 2281435 5775583 := bstep (se 1 (by rfl) ⟨4331687, by rfl⟩ : syracuseStep 5775583 = 8663375) B8663375
theorem B7700777 : Blo 2281435 7700777 := bstep (se 2 (by rfl) ⟨2887791, by rfl⟩ : syracuseStep 7700777 = 5775583) B5775583
theorem B5133851 : Blo 2281435 5133851 := bstep (se 1 (by rfl) ⟨3850388, by rfl⟩ : syracuseStep 5133851 = 7700777) B7700777
theorem B3422567 : Blo 2281435 3422567 := bstep (se 1 (by rfl) ⟨2566925, by rfl⟩ : syracuseStep 3422567 = 5133851) B5133851
theorem B2281711 : Blo 2281435 2281711 := bstep (se 1 (by rfl) ⟨1711283, by rfl⟩ : syracuseStep 2281711 = 3422567) B3422567
theorem B3422573 : Blo 2281435 3422573 := bbase (se 3 (by rfl) ⟨641732, by rfl⟩ : syracuseStep 3422573 = 1283465) (by norm_num)
theorem B2281715 : Blo 2281435 2281715 := bstep (se 1 (by rfl) ⟨1711286, by rfl⟩ : syracuseStep 2281715 = 3422573) B3422573
theorem B5133869 : Blo 2281435 5133869 := bbase (se 3 (by rfl) ⟨962600, by rfl⟩ : syracuseStep 5133869 = 1925201) (by norm_num)
theorem B3422579 : Blo 2281435 3422579 := bstep (se 1 (by rfl) ⟨2566934, by rfl⟩ : syracuseStep 3422579 = 5133869) B5133869
theorem B2281719 : Blo 2281435 2281719 := bstep (se 1 (by rfl) ⟨1711289, by rfl⟩ : syracuseStep 2281719 = 3422579) B3422579
theorem B5203925 : Blo 2281435 5203925 := bbase (se 7 (by rfl) ⟨60983, by rfl⟩ : syracuseStep 5203925 = 121967) (by norm_num)
theorem B3469283 : Blo 2281435 3469283 := bstep (se 1 (by rfl) ⟨2601962, by rfl⟩ : syracuseStep 3469283 = 5203925) B5203925
theorem B2312855 : Blo 2281435 2312855 := bstep (se 1 (by rfl) ⟨1734641, by rfl⟩ : syracuseStep 2312855 = 3469283) B3469283
theorem B24670453 : Blo 2281435 24670453 := bstep (se 5 (by rfl) ⟨1156427, by rfl⟩ : syracuseStep 24670453 = 2312855) B2312855
theorem B32893937 : Blo 2281435 32893937 := bstep (se 2 (by rfl) ⟨12335226, by rfl⟩ : syracuseStep 32893937 = 24670453) B24670453
theorem B21929291 : Blo 2281435 21929291 := bstep (se 1 (by rfl) ⟨16446968, by rfl⟩ : syracuseStep 21929291 = 32893937) B32893937
theorem B14619527 : Blo 2281435 14619527 := bstep (se 1 (by rfl) ⟨10964645, by rfl⟩ : syracuseStep 14619527 = 21929291) B21929291
theorem B9746351 : Blo 2281435 9746351 := bstep (se 1 (by rfl) ⟨7309763, by rfl⟩ : syracuseStep 9746351 = 14619527) B14619527
theorem B6497567 : Blo 2281435 6497567 := bstep (se 1 (by rfl) ⟨4873175, by rfl⟩ : syracuseStep 6497567 = 9746351) B9746351
theorem B4331711 : Blo 2281435 4331711 := bstep (se 1 (by rfl) ⟨3248783, by rfl⟩ : syracuseStep 4331711 = 6497567) B6497567
theorem B2887807 : Blo 2281435 2887807 := bstep (se 1 (by rfl) ⟨2165855, by rfl⟩ : syracuseStep 2887807 = 4331711) B4331711
theorem B3850409 : Blo 2281435 3850409 := bstep (se 2 (by rfl) ⟨1443903, by rfl⟩ : syracuseStep 3850409 = 2887807) B2887807
theorem B2566939 : Blo 2281435 2566939 := bstep (se 1 (by rfl) ⟨1925204, by rfl⟩ : syracuseStep 2566939 = 3850409) B3850409
theorem B3422585 : Blo 2281435 3422585 := bstep (se 2 (by rfl) ⟨1283469, by rfl⟩ : syracuseStep 3422585 = 2566939) B2566939
theorem B2281723 : Blo 2281435 2281723 := bstep (se 1 (by rfl) ⟨1711292, by rfl⟩ : syracuseStep 2281723 = 3422585) B3422585
theorem B8781637 : Blo 2281435 8781637 := bbase (se 4 (by rfl) ⟨823278, by rfl⟩ : syracuseStep 8781637 = 1646557) (by norm_num)
theorem B11708849 : Blo 2281435 11708849 := bstep (se 2 (by rfl) ⟨4390818, by rfl⟩ : syracuseStep 11708849 = 8781637) B8781637
theorem B7805899 : Blo 2281435 7805899 := bstep (se 1 (by rfl) ⟨5854424, by rfl⟩ : syracuseStep 7805899 = 11708849) B11708849
theorem B10407865 : Blo 2281435 10407865 := bstep (se 2 (by rfl) ⟨3902949, by rfl⟩ : syracuseStep 10407865 = 7805899) B7805899
theorem B13877153 : Blo 2281435 13877153 := bstep (se 2 (by rfl) ⟨5203932, by rfl⟩ : syracuseStep 13877153 = 10407865) B10407865
theorem B9251435 : Blo 2281435 9251435 := bstep (se 1 (by rfl) ⟨6938576, by rfl⟩ : syracuseStep 9251435 = 13877153) B13877153
theorem B6167623 : Blo 2281435 6167623 := bstep (se 1 (by rfl) ⟨4625717, by rfl⟩ : syracuseStep 6167623 = 9251435) B9251435
theorem B8223497 : Blo 2281435 8223497 := bstep (se 2 (by rfl) ⟨3083811, by rfl⟩ : syracuseStep 8223497 = 6167623) B6167623
theorem B5482331 : Blo 2281435 5482331 := bstep (se 1 (by rfl) ⟨4111748, by rfl⟩ : syracuseStep 5482331 = 8223497) B8223497
theorem B3654887 : Blo 2281435 3654887 := bstep (se 1 (by rfl) ⟨2741165, by rfl⟩ : syracuseStep 3654887 = 5482331) B5482331
theorem B38985461 : Blo 2281435 38985461 := bstep (se 5 (by rfl) ⟨1827443, by rfl⟩ : syracuseStep 38985461 = 3654887) B3654887
theorem B25990307 : Blo 2281435 25990307 := bstep (se 1 (by rfl) ⟨19492730, by rfl⟩ : syracuseStep 25990307 = 38985461) B38985461
theorem B17326871 : Blo 2281435 17326871 := bstep (se 1 (by rfl) ⟨12995153, by rfl⟩ : syracuseStep 17326871 = 25990307) B25990307
theorem B11551247 : Blo 2281435 11551247 := bstep (se 1 (by rfl) ⟨8663435, by rfl⟩ : syracuseStep 11551247 = 17326871) B17326871
theorem B7700831 : Blo 2281435 7700831 := bstep (se 1 (by rfl) ⟨5775623, by rfl⟩ : syracuseStep 7700831 = 11551247) B11551247
theorem B5133887 : Blo 2281435 5133887 := bstep (se 1 (by rfl) ⟨3850415, by rfl⟩ : syracuseStep 5133887 = 7700831) B7700831
theorem B3422591 : Blo 2281435 3422591 := bstep (se 1 (by rfl) ⟨2566943, by rfl⟩ : syracuseStep 3422591 = 5133887) B5133887
theorem B2281727 : Blo 2281435 2281727 := bstep (se 1 (by rfl) ⟨1711295, by rfl⟩ : syracuseStep 2281727 = 3422591) B3422591
theorem B3422597 : Blo 2281435 3422597 := bbase (se 4 (by rfl) ⟨320868, by rfl⟩ : syracuseStep 3422597 = 641737) (by norm_num)
theorem B2281731 : Blo 2281435 2281731 := bstep (se 1 (by rfl) ⟨1711298, by rfl⟩ : syracuseStep 2281731 = 3422597) B3422597
theorem B3850429 : Blo 2281435 3850429 := bbase (se 3 (by rfl) ⟨721955, by rfl⟩ : syracuseStep 3850429 = 1443911) (by norm_num)
theorem B5133905 : Blo 2281435 5133905 := bstep (se 2 (by rfl) ⟨1925214, by rfl⟩ : syracuseStep 5133905 = 3850429) B3850429
theorem B3422603 : Blo 2281435 3422603 := bstep (se 1 (by rfl) ⟨2566952, by rfl⟩ : syracuseStep 3422603 = 5133905) B5133905
theorem B2281735 : Blo 2281435 2281735 := bstep (se 1 (by rfl) ⟨1711301, by rfl⟩ : syracuseStep 2281735 = 3422603) B3422603
theorem B2566957 : Blo 2281435 2566957 := bbase (se 3 (by rfl) ⟨481304, by rfl⟩ : syracuseStep 2566957 = 962609) (by norm_num)
theorem B3422609 : Blo 2281435 3422609 := bstep (se 2 (by rfl) ⟨1283478, by rfl⟩ : syracuseStep 3422609 = 2566957) B2566957
theorem B2281739 : Blo 2281435 2281739 := bstep (se 1 (by rfl) ⟨1711304, by rfl⟩ : syracuseStep 2281739 = 3422609) B3422609
theorem B7700885 : Blo 2281435 7700885 := bbase (se 6 (by rfl) ⟨180489, by rfl⟩ : syracuseStep 7700885 = 360979) (by norm_num)
theorem B5133923 : Blo 2281435 5133923 := bstep (se 1 (by rfl) ⟨3850442, by rfl⟩ : syracuseStep 5133923 = 7700885) B7700885
theorem B3422615 : Blo 2281435 3422615 := bstep (se 1 (by rfl) ⟨2566961, by rfl⟩ : syracuseStep 3422615 = 5133923) B5133923
theorem B2281743 : Blo 2281435 2281743 := bstep (se 1 (by rfl) ⟨1711307, by rfl⟩ : syracuseStep 2281743 = 3422615) B3422615
theorem B3422621 : Blo 2281435 3422621 := bbase (se 3 (by rfl) ⟨641741, by rfl⟩ : syracuseStep 3422621 = 1283483) (by norm_num)
theorem B2281747 : Blo 2281435 2281747 := bstep (se 1 (by rfl) ⟨1711310, by rfl⟩ : syracuseStep 2281747 = 3422621) B3422621
theorem B5133941 : Blo 2281435 5133941 := bbase (se 5 (by rfl) ⟨240653, by rfl⟩ : syracuseStep 5133941 = 481307) (by norm_num)
theorem B3422627 : Blo 2281435 3422627 := bstep (se 1 (by rfl) ⟨2566970, by rfl⟩ : syracuseStep 3422627 = 5133941) B5133941
theorem B2281751 : Blo 2281435 2281751 := bstep (se 1 (by rfl) ⟨1711313, by rfl⟩ : syracuseStep 2281751 = 3422627) B3422627
theorem B6586309 : Blo 2281435 6586309 := bbase (se 4 (by rfl) ⟨617466, by rfl⟩ : syracuseStep 6586309 = 1234933) (by norm_num)
theorem B8781745 : Blo 2281435 8781745 := bstep (se 2 (by rfl) ⟨3293154, by rfl⟩ : syracuseStep 8781745 = 6586309) B6586309
theorem B11708993 : Blo 2281435 11708993 := bstep (se 2 (by rfl) ⟨4390872, by rfl⟩ : syracuseStep 11708993 = 8781745) B8781745
theorem B31223981 : Blo 2281435 31223981 := bstep (se 3 (by rfl) ⟨5854496, by rfl⟩ : syracuseStep 31223981 = 11708993) B11708993
theorem B20815987 : Blo 2281435 20815987 := bstep (se 1 (by rfl) ⟨15611990, by rfl⟩ : syracuseStep 20815987 = 31223981) B31223981
theorem B27754649 : Blo 2281435 27754649 := bstep (se 2 (by rfl) ⟨10407993, by rfl⟩ : syracuseStep 27754649 = 20815987) B20815987
theorem B18503099 : Blo 2281435 18503099 := bstep (se 1 (by rfl) ⟨13877324, by rfl⟩ : syracuseStep 18503099 = 27754649) B27754649
theorem B12335399 : Blo 2281435 12335399 := bstep (se 1 (by rfl) ⟨9251549, by rfl⟩ : syracuseStep 12335399 = 18503099) B18503099
theorem B8223599 : Blo 2281435 8223599 := bstep (se 1 (by rfl) ⟨6167699, by rfl⟩ : syracuseStep 8223599 = 12335399) B12335399
theorem B5482399 : Blo 2281435 5482399 := bstep (se 1 (by rfl) ⟨4111799, by rfl⟩ : syracuseStep 5482399 = 8223599) B8223599
theorem B7309865 : Blo 2281435 7309865 := bstep (se 2 (by rfl) ⟨2741199, by rfl⟩ : syracuseStep 7309865 = 5482399) B5482399
theorem B19492973 : Blo 2281435 19492973 := bstep (se 3 (by rfl) ⟨3654932, by rfl⟩ : syracuseStep 19492973 = 7309865) B7309865
theorem B12995315 : Blo 2281435 12995315 := bstep (se 1 (by rfl) ⟨9746486, by rfl⟩ : syracuseStep 12995315 = 19492973) B19492973
theorem B8663543 : Blo 2281435 8663543 := bstep (se 1 (by rfl) ⟨6497657, by rfl⟩ : syracuseStep 8663543 = 12995315) B12995315
theorem B5775695 : Blo 2281435 5775695 := bstep (se 1 (by rfl) ⟨4331771, by rfl⟩ : syracuseStep 5775695 = 8663543) B8663543
theorem B3850463 : Blo 2281435 3850463 := bstep (se 1 (by rfl) ⟨2887847, by rfl⟩ : syracuseStep 3850463 = 5775695) B5775695
theorem B2566975 : Blo 2281435 2566975 := bstep (se 1 (by rfl) ⟨1925231, by rfl⟩ : syracuseStep 2566975 = 3850463) B3850463
theorem B3422633 : Blo 2281435 3422633 := bstep (se 2 (by rfl) ⟨1283487, by rfl⟩ : syracuseStep 3422633 = 2566975) B2566975
theorem B2281755 : Blo 2281435 2281755 := bstep (se 1 (by rfl) ⟨1711316, by rfl⟩ : syracuseStep 2281755 = 3422633) B3422633
theorem B8663557 : Blo 2281435 8663557 := bbase (se 4 (by rfl) ⟨812208, by rfl⟩ : syracuseStep 8663557 = 1624417) (by norm_num)
theorem B11551409 : Blo 2281435 11551409 := bstep (se 2 (by rfl) ⟨4331778, by rfl⟩ : syracuseStep 11551409 = 8663557) B8663557
theorem B7700939 : Blo 2281435 7700939 := bstep (se 1 (by rfl) ⟨5775704, by rfl⟩ : syracuseStep 7700939 = 11551409) B11551409
theorem B5133959 : Blo 2281435 5133959 := bstep (se 1 (by rfl) ⟨3850469, by rfl⟩ : syracuseStep 5133959 = 7700939) B7700939
theorem B3422639 : Blo 2281435 3422639 := bstep (se 1 (by rfl) ⟨2566979, by rfl⟩ : syracuseStep 3422639 = 5133959) B5133959
theorem B2281759 : Blo 2281435 2281759 := bstep (se 1 (by rfl) ⟨1711319, by rfl⟩ : syracuseStep 2281759 = 3422639) B3422639
theorem B3422645 : Blo 2281435 3422645 := bbase (se 5 (by rfl) ⟨160436, by rfl⟩ : syracuseStep 3422645 = 320873) (by norm_num)
theorem B2281763 : Blo 2281435 2281763 := bstep (se 1 (by rfl) ⟨1711322, by rfl⟩ : syracuseStep 2281763 = 3422645) B3422645
theorem B5775725 : Blo 2281435 5775725 := bbase (se 3 (by rfl) ⟨1082948, by rfl⟩ : syracuseStep 5775725 = 2165897) (by norm_num)
theorem B3850483 : Blo 2281435 3850483 := bstep (se 1 (by rfl) ⟨2887862, by rfl⟩ : syracuseStep 3850483 = 5775725) B5775725
theorem B5133977 : Blo 2281435 5133977 := bstep (se 2 (by rfl) ⟨1925241, by rfl⟩ : syracuseStep 5133977 = 3850483) B3850483
theorem B3422651 : Blo 2281435 3422651 := bstep (se 1 (by rfl) ⟨2566988, by rfl⟩ : syracuseStep 3422651 = 5133977) B5133977
theorem B2281767 : Blo 2281435 2281767 := bstep (se 1 (by rfl) ⟨1711325, by rfl⟩ : syracuseStep 2281767 = 3422651) B3422651
theorem B2566993 : Blo 2281435 2566993 := bbase (se 2 (by rfl) ⟨962622, by rfl⟩ : syracuseStep 2566993 = 1925245) (by norm_num)
theorem B3422657 : Blo 2281435 3422657 := bstep (se 2 (by rfl) ⟨1283496, by rfl⟩ : syracuseStep 3422657 = 2566993) B2566993
theorem B2281771 : Blo 2281435 2281771 := bstep (se 1 (by rfl) ⟨1711328, by rfl⟩ : syracuseStep 2281771 = 3422657) B3422657
theorem B3654965 : Blo 2281435 3654965 := bbase (se 5 (by rfl) ⟨171326, by rfl⟩ : syracuseStep 3654965 = 342653) (by norm_num)
theorem B2436643 : Blo 2281435 2436643 := bstep (se 1 (by rfl) ⟨1827482, by rfl⟩ : syracuseStep 2436643 = 3654965) B3654965
theorem B3248857 : Blo 2281435 3248857 := bstep (se 2 (by rfl) ⟨1218321, by rfl⟩ : syracuseStep 3248857 = 2436643) B2436643
theorem B4331809 : Blo 2281435 4331809 := bstep (se 2 (by rfl) ⟨1624428, by rfl⟩ : syracuseStep 4331809 = 3248857) B3248857
theorem B5775745 : Blo 2281435 5775745 := bstep (se 2 (by rfl) ⟨2165904, by rfl⟩ : syracuseStep 5775745 = 4331809) B4331809
theorem B7700993 : Blo 2281435 7700993 := bstep (se 2 (by rfl) ⟨2887872, by rfl⟩ : syracuseStep 7700993 = 5775745) B5775745
theorem B5133995 : Blo 2281435 5133995 := bstep (se 1 (by rfl) ⟨3850496, by rfl⟩ : syracuseStep 5133995 = 7700993) B7700993
theorem B3422663 : Blo 2281435 3422663 := bstep (se 1 (by rfl) ⟨2566997, by rfl⟩ : syracuseStep 3422663 = 5133995) B5133995
theorem B2281775 : Blo 2281435 2281775 := bstep (se 1 (by rfl) ⟨1711331, by rfl⟩ : syracuseStep 2281775 = 3422663) B3422663
theorem B3422669 : Blo 2281435 3422669 := bbase (se 3 (by rfl) ⟨641750, by rfl⟩ : syracuseStep 3422669 = 1283501) (by norm_num)
theorem B2281779 : Blo 2281435 2281779 := bstep (se 1 (by rfl) ⟨1711334, by rfl⟩ : syracuseStep 2281779 = 3422669) B3422669
theorem B5134013 : Blo 2281435 5134013 := bbase (se 3 (by rfl) ⟨962627, by rfl⟩ : syracuseStep 5134013 = 1925255) (by norm_num)
theorem B3422675 : Blo 2281435 3422675 := bstep (se 1 (by rfl) ⟨2567006, by rfl⟩ : syracuseStep 3422675 = 5134013) B5134013
theorem B2281783 : Blo 2281435 2281783 := bstep (se 1 (by rfl) ⟨1711337, by rfl⟩ : syracuseStep 2281783 = 3422675) B3422675
theorem B3850517 : Blo 2281435 3850517 := bbase (se 6 (by rfl) ⟨90246, by rfl⟩ : syracuseStep 3850517 = 180493) (by norm_num)
theorem B2567011 : Blo 2281435 2567011 := bstep (se 1 (by rfl) ⟨1925258, by rfl⟩ : syracuseStep 2567011 = 3850517) B3850517
theorem B3422681 : Blo 2281435 3422681 := bstep (se 2 (by rfl) ⟨1283505, by rfl⟩ : syracuseStep 3422681 = 2567011) B2567011
theorem B2281787 : Blo 2281435 2281787 := bstep (se 1 (by rfl) ⟨1711340, by rfl⟩ : syracuseStep 2281787 = 3422681) B3422681
theorem B5557285 : Blo 2281435 5557285 := bbase (se 4 (by rfl) ⟨520995, by rfl⟩ : syracuseStep 5557285 = 1041991) (by norm_num)
theorem B7409713 : Blo 2281435 7409713 := bstep (se 2 (by rfl) ⟨2778642, by rfl⟩ : syracuseStep 7409713 = 5557285) B5557285
theorem B9879617 : Blo 2281435 9879617 := bstep (se 2 (by rfl) ⟨3704856, by rfl⟩ : syracuseStep 9879617 = 7409713) B7409713
theorem B26345645 : Blo 2281435 26345645 := bstep (se 3 (by rfl) ⟨4939808, by rfl⟩ : syracuseStep 26345645 = 9879617) B9879617
theorem B17563763 : Blo 2281435 17563763 := bstep (se 1 (by rfl) ⟨13172822, by rfl⟩ : syracuseStep 17563763 = 26345645) B26345645
theorem B46836701 : Blo 2281435 46836701 := bstep (se 3 (by rfl) ⟨8781881, by rfl⟩ : syracuseStep 46836701 = 17563763) B17563763
theorem B31224467 : Blo 2281435 31224467 := bstep (se 1 (by rfl) ⟨23418350, by rfl⟩ : syracuseStep 31224467 = 46836701) B46836701
theorem B20816311 : Blo 2281435 20816311 := bstep (se 1 (by rfl) ⟨15612233, by rfl⟩ : syracuseStep 20816311 = 31224467) B31224467
theorem B27755081 : Blo 2281435 27755081 := bstep (se 2 (by rfl) ⟨10408155, by rfl⟩ : syracuseStep 27755081 = 20816311) B20816311
theorem B18503387 : Blo 2281435 18503387 := bstep (se 1 (by rfl) ⟨13877540, by rfl⟩ : syracuseStep 18503387 = 27755081) B27755081
theorem B12335591 : Blo 2281435 12335591 := bstep (se 1 (by rfl) ⟨9251693, by rfl⟩ : syracuseStep 12335591 = 18503387) B18503387
theorem B32894909 : Blo 2281435 32894909 := bstep (se 3 (by rfl) ⟨6167795, by rfl⟩ : syracuseStep 32894909 = 12335591) B12335591
theorem B21929939 : Blo 2281435 21929939 := bstep (se 1 (by rfl) ⟨16447454, by rfl⟩ : syracuseStep 21929939 = 32894909) B32894909
theorem B14619959 : Blo 2281435 14619959 := bstep (se 1 (by rfl) ⟨10964969, by rfl⟩ : syracuseStep 14619959 = 21929939) B21929939
theorem B9746639 : Blo 2281435 9746639 := bstep (se 1 (by rfl) ⟨7309979, by rfl⟩ : syracuseStep 9746639 = 14619959) B14619959
theorem B6497759 : Blo 2281435 6497759 := bstep (se 1 (by rfl) ⟨4873319, by rfl⟩ : syracuseStep 6497759 = 9746639) B9746639
theorem B17327357 : Blo 2281435 17327357 := bstep (se 3 (by rfl) ⟨3248879, by rfl⟩ : syracuseStep 17327357 = 6497759) B6497759
theorem B11551571 : Blo 2281435 11551571 := bstep (se 1 (by rfl) ⟨8663678, by rfl⟩ : syracuseStep 11551571 = 17327357) B17327357
theorem B7701047 : Blo 2281435 7701047 := bstep (se 1 (by rfl) ⟨5775785, by rfl⟩ : syracuseStep 7701047 = 11551571) B11551571
theorem B5134031 : Blo 2281435 5134031 := bstep (se 1 (by rfl) ⟨3850523, by rfl⟩ : syracuseStep 5134031 = 7701047) B7701047
theorem B3422687 : Blo 2281435 3422687 := bstep (se 1 (by rfl) ⟨2567015, by rfl⟩ : syracuseStep 3422687 = 5134031) B5134031
theorem B2281791 : Blo 2281435 2281791 := bstep (se 1 (by rfl) ⟨1711343, by rfl⟩ : syracuseStep 2281791 = 3422687) B3422687
theorem B3422693 : Blo 2281435 3422693 := bbase (se 4 (by rfl) ⟨320877, by rfl⟩ : syracuseStep 3422693 = 641755) (by norm_num)
theorem B2281795 : Blo 2281435 2281795 := bstep (se 1 (by rfl) ⟨1711346, by rfl⟩ : syracuseStep 2281795 = 3422693) B3422693
theorem B2602049 : Blo 2281435 2602049 := bbase (se 2 (by rfl) ⟨975768, by rfl⟩ : syracuseStep 2602049 = 1951537) (by norm_num)
theorem B6938797 : Blo 2281435 6938797 := bstep (se 3 (by rfl) ⟨1301024, by rfl⟩ : syracuseStep 6938797 = 2602049) B2602049
theorem B9251729 : Blo 2281435 9251729 := bstep (se 2 (by rfl) ⟨3469398, by rfl⟩ : syracuseStep 9251729 = 6938797) B6938797
theorem B6167819 : Blo 2281435 6167819 := bstep (se 1 (by rfl) ⟨4625864, by rfl⟩ : syracuseStep 6167819 = 9251729) B9251729
theorem B4111879 : Blo 2281435 4111879 := bstep (se 1 (by rfl) ⟨3083909, by rfl⟩ : syracuseStep 4111879 = 6167819) B6167819
theorem B5482505 : Blo 2281435 5482505 := bstep (se 2 (by rfl) ⟨2055939, by rfl⟩ : syracuseStep 5482505 = 4111879) B4111879
theorem B14620013 : Blo 2281435 14620013 := bstep (se 3 (by rfl) ⟨2741252, by rfl⟩ : syracuseStep 14620013 = 5482505) B5482505
theorem B9746675 : Blo 2281435 9746675 := bstep (se 1 (by rfl) ⟨7310006, by rfl⟩ : syracuseStep 9746675 = 14620013) B14620013
theorem B6497783 : Blo 2281435 6497783 := bstep (se 1 (by rfl) ⟨4873337, by rfl⟩ : syracuseStep 6497783 = 9746675) B9746675
theorem B4331855 : Blo 2281435 4331855 := bstep (se 1 (by rfl) ⟨3248891, by rfl⟩ : syracuseStep 4331855 = 6497783) B6497783
theorem B2887903 : Blo 2281435 2887903 := bstep (se 1 (by rfl) ⟨2165927, by rfl⟩ : syracuseStep 2887903 = 4331855) B4331855
theorem B3850537 : Blo 2281435 3850537 := bstep (se 2 (by rfl) ⟨1443951, by rfl⟩ : syracuseStep 3850537 = 2887903) B2887903
theorem B5134049 : Blo 2281435 5134049 := bstep (se 2 (by rfl) ⟨1925268, by rfl⟩ : syracuseStep 5134049 = 3850537) B3850537
theorem B3422699 : Blo 2281435 3422699 := bstep (se 1 (by rfl) ⟨2567024, by rfl⟩ : syracuseStep 3422699 = 5134049) B5134049
theorem B2281799 : Blo 2281435 2281799 := bstep (se 1 (by rfl) ⟨1711349, by rfl⟩ : syracuseStep 2281799 = 3422699) B3422699
theorem B2567029 : Blo 2281435 2567029 := bbase (se 5 (by rfl) ⟨120329, by rfl⟩ : syracuseStep 2567029 = 240659) (by norm_num)
theorem B3422705 : Blo 2281435 3422705 := bstep (se 2 (by rfl) ⟨1283514, by rfl⟩ : syracuseStep 3422705 = 2567029) B2567029
theorem B2281803 : Blo 2281435 2281803 := bstep (se 1 (by rfl) ⟨1711352, by rfl⟩ : syracuseStep 2281803 = 3422705) B3422705
theorem B2887913 : Blo 2281435 2887913 := bbase (se 2 (by rfl) ⟨1082967, by rfl⟩ : syracuseStep 2887913 = 2165935) (by norm_num)
theorem B7701101 : Blo 2281435 7701101 := bstep (se 3 (by rfl) ⟨1443956, by rfl⟩ : syracuseStep 7701101 = 2887913) B2887913
theorem B5134067 : Blo 2281435 5134067 := bstep (se 1 (by rfl) ⟨3850550, by rfl⟩ : syracuseStep 5134067 = 7701101) B7701101
theorem B3422711 : Blo 2281435 3422711 := bstep (se 1 (by rfl) ⟨2567033, by rfl⟩ : syracuseStep 3422711 = 5134067) B5134067
theorem B2281807 : Blo 2281435 2281807 := bstep (se 1 (by rfl) ⟨1711355, by rfl⟩ : syracuseStep 2281807 = 3422711) B3422711
theorem B3422717 : Blo 2281435 3422717 := bbase (se 3 (by rfl) ⟨641759, by rfl⟩ : syracuseStep 3422717 = 1283519) (by norm_num)
theorem B2281811 : Blo 2281435 2281811 := bstep (se 1 (by rfl) ⟨1711358, by rfl⟩ : syracuseStep 2281811 = 3422717) B3422717
theorem B5134085 : Blo 2281435 5134085 := bbase (se 4 (by rfl) ⟨481320, by rfl⟩ : syracuseStep 5134085 = 962641) (by norm_num)
theorem B3422723 : Blo 2281435 3422723 := bstep (se 1 (by rfl) ⟨2567042, by rfl⟩ : syracuseStep 3422723 = 5134085) B5134085
theorem B2281815 : Blo 2281435 2281815 := bstep (se 1 (by rfl) ⟨1711361, by rfl⟩ : syracuseStep 2281815 = 3422723) B3422723
theorem B4331893 : Blo 2281435 4331893 := bbase (se 5 (by rfl) ⟨203057, by rfl⟩ : syracuseStep 4331893 = 406115) (by norm_num)
theorem B5775857 : Blo 2281435 5775857 := bstep (se 2 (by rfl) ⟨2165946, by rfl⟩ : syracuseStep 5775857 = 4331893) B4331893
theorem B3850571 : Blo 2281435 3850571 := bstep (se 1 (by rfl) ⟨2887928, by rfl⟩ : syracuseStep 3850571 = 5775857) B5775857
theorem B2567047 : Blo 2281435 2567047 := bstep (se 1 (by rfl) ⟨1925285, by rfl⟩ : syracuseStep 2567047 = 3850571) B3850571
theorem B3422729 : Blo 2281435 3422729 := bstep (se 2 (by rfl) ⟨1283523, by rfl⟩ : syracuseStep 3422729 = 2567047) B2567047
theorem B2281819 : Blo 2281435 2281819 := bstep (se 1 (by rfl) ⟨1711364, by rfl⟩ : syracuseStep 2281819 = 3422729) B3422729
theorem B11551733 : Blo 2281435 11551733 := bbase (se 5 (by rfl) ⟨541487, by rfl⟩ : syracuseStep 11551733 = 1082975) (by norm_num)
theorem B7701155 : Blo 2281435 7701155 := bstep (se 1 (by rfl) ⟨5775866, by rfl⟩ : syracuseStep 7701155 = 11551733) B11551733
theorem B5134103 : Blo 2281435 5134103 := bstep (se 1 (by rfl) ⟨3850577, by rfl⟩ : syracuseStep 5134103 = 7701155) B7701155
theorem B3422735 : Blo 2281435 3422735 := bstep (se 1 (by rfl) ⟨2567051, by rfl⟩ : syracuseStep 3422735 = 5134103) B5134103
theorem B2281823 : Blo 2281435 2281823 := bstep (se 1 (by rfl) ⟨1711367, by rfl⟩ : syracuseStep 2281823 = 3422735) B3422735
theorem B3422741 : Blo 2281435 3422741 := bbase (se 6 (by rfl) ⟨80220, by rfl⟩ : syracuseStep 3422741 = 160441) (by norm_num)
theorem B2281827 : Blo 2281435 2281827 := bstep (se 1 (by rfl) ⟨1711370, by rfl⟩ : syracuseStep 2281827 = 3422741) B3422741
theorem B19493621 : Blo 2281435 19493621 := bbase (se 5 (by rfl) ⟨913763, by rfl⟩ : syracuseStep 19493621 = 1827527) (by norm_num)
theorem B12995747 : Blo 2281435 12995747 := bstep (se 1 (by rfl) ⟨9746810, by rfl⟩ : syracuseStep 12995747 = 19493621) B19493621
theorem B8663831 : Blo 2281435 8663831 := bstep (se 1 (by rfl) ⟨6497873, by rfl⟩ : syracuseStep 8663831 = 12995747) B12995747
theorem B5775887 : Blo 2281435 5775887 := bstep (se 1 (by rfl) ⟨4331915, by rfl⟩ : syracuseStep 5775887 = 8663831) B8663831
theorem B3850591 : Blo 2281435 3850591 := bstep (se 1 (by rfl) ⟨2887943, by rfl⟩ : syracuseStep 3850591 = 5775887) B5775887
theorem B5134121 : Blo 2281435 5134121 := bstep (se 2 (by rfl) ⟨1925295, by rfl⟩ : syracuseStep 5134121 = 3850591) B3850591
theorem B3422747 : Blo 2281435 3422747 := bstep (se 1 (by rfl) ⟨2567060, by rfl⟩ : syracuseStep 3422747 = 5134121) B5134121
theorem B2281831 : Blo 2281435 2281831 := bstep (se 1 (by rfl) ⟨1711373, by rfl⟩ : syracuseStep 2281831 = 3422747) B3422747
theorem B2567065 : Blo 2281435 2567065 := bbase (se 2 (by rfl) ⟨962649, by rfl⟩ : syracuseStep 2567065 = 1925299) (by norm_num)
theorem B3422753 : Blo 2281435 3422753 := bstep (se 2 (by rfl) ⟨1283532, by rfl⟩ : syracuseStep 3422753 = 2567065) B2567065
theorem B2281835 : Blo 2281435 2281835 := bstep (se 1 (by rfl) ⟨1711376, by rfl⟩ : syracuseStep 2281835 = 3422753) B3422753
theorem B8663861 : Blo 2281435 8663861 := bbase (se 5 (by rfl) ⟨406118, by rfl⟩ : syracuseStep 8663861 = 812237) (by norm_num)
theorem B5775907 : Blo 2281435 5775907 := bstep (se 1 (by rfl) ⟨4331930, by rfl⟩ : syracuseStep 5775907 = 8663861) B8663861
theorem B7701209 : Blo 2281435 7701209 := bstep (se 2 (by rfl) ⟨2887953, by rfl⟩ : syracuseStep 7701209 = 5775907) B5775907
theorem B5134139 : Blo 2281435 5134139 := bstep (se 1 (by rfl) ⟨3850604, by rfl⟩ : syracuseStep 5134139 = 7701209) B7701209
theorem B3422759 : Blo 2281435 3422759 := bstep (se 1 (by rfl) ⟨2567069, by rfl⟩ : syracuseStep 3422759 = 5134139) B5134139
theorem B2281839 : Blo 2281435 2281839 := bstep (se 1 (by rfl) ⟨1711379, by rfl⟩ : syracuseStep 2281839 = 3422759) B3422759
theorem B3422765 : Blo 2281435 3422765 := bbase (se 3 (by rfl) ⟨641768, by rfl⟩ : syracuseStep 3422765 = 1283537) (by norm_num)
theorem B2281843 : Blo 2281435 2281843 := bstep (se 1 (by rfl) ⟨1711382, by rfl⟩ : syracuseStep 2281843 = 3422765) B3422765
theorem B5134157 : Blo 2281435 5134157 := bbase (se 3 (by rfl) ⟨962654, by rfl⟩ : syracuseStep 5134157 = 1925309) (by norm_num)
theorem B3422771 : Blo 2281435 3422771 := bstep (se 1 (by rfl) ⟨2567078, by rfl⟩ : syracuseStep 3422771 = 5134157) B5134157
theorem B2281847 : Blo 2281435 2281847 := bstep (se 1 (by rfl) ⟨1711385, by rfl⟩ : syracuseStep 2281847 = 3422771) B3422771
theorem B2887969 : Blo 2281435 2887969 := bbase (se 2 (by rfl) ⟨1082988, by rfl⟩ : syracuseStep 2887969 = 2165977) (by norm_num)
theorem B3850625 : Blo 2281435 3850625 := bstep (se 2 (by rfl) ⟨1443984, by rfl⟩ : syracuseStep 3850625 = 2887969) B2887969
theorem B2567083 : Blo 2281435 2567083 := bstep (se 1 (by rfl) ⟨1925312, by rfl⟩ : syracuseStep 2567083 = 3850625) B3850625
theorem B3422777 : Blo 2281435 3422777 := bstep (se 2 (by rfl) ⟨1283541, by rfl⟩ : syracuseStep 3422777 = 2567083) B2567083
theorem B2281851 : Blo 2281435 2281851 := bstep (se 1 (by rfl) ⟨1711388, by rfl⟩ : syracuseStep 2281851 = 3422777) B3422777
theorem B25991765 : Blo 2281435 25991765 := bbase (se 8 (by rfl) ⟨152295, by rfl⟩ : syracuseStep 25991765 = 304591) (by norm_num)
theorem B17327843 : Blo 2281435 17327843 := bstep (se 1 (by rfl) ⟨12995882, by rfl⟩ : syracuseStep 17327843 = 25991765) B25991765
theorem B11551895 : Blo 2281435 11551895 := bstep (se 1 (by rfl) ⟨8663921, by rfl⟩ : syracuseStep 11551895 = 17327843) B17327843
theorem B7701263 : Blo 2281435 7701263 := bstep (se 1 (by rfl) ⟨5775947, by rfl⟩ : syracuseStep 7701263 = 11551895) B11551895
theorem B5134175 : Blo 2281435 5134175 := bstep (se 1 (by rfl) ⟨3850631, by rfl⟩ : syracuseStep 5134175 = 7701263) B7701263
theorem B3422783 : Blo 2281435 3422783 := bstep (se 1 (by rfl) ⟨2567087, by rfl⟩ : syracuseStep 3422783 = 5134175) B5134175
theorem B2281855 : Blo 2281435 2281855 := bstep (se 1 (by rfl) ⟨1711391, by rfl⟩ : syracuseStep 2281855 = 3422783) B3422783
theorem B3422789 : Blo 2281435 3422789 := bbase (se 4 (by rfl) ⟨320886, by rfl⟩ : syracuseStep 3422789 = 641773) (by norm_num)
theorem B2281859 : Blo 2281435 2281859 := bstep (se 1 (by rfl) ⟨1711394, by rfl⟩ : syracuseStep 2281859 = 3422789) B3422789
theorem B3850645 : Blo 2281435 3850645 := bbase (se 6 (by rfl) ⟨90249, by rfl⟩ : syracuseStep 3850645 = 180499) (by norm_num)
theorem B5134193 : Blo 2281435 5134193 := bstep (se 2 (by rfl) ⟨1925322, by rfl⟩ : syracuseStep 5134193 = 3850645) B3850645
theorem B3422795 : Blo 2281435 3422795 := bstep (se 1 (by rfl) ⟨2567096, by rfl⟩ : syracuseStep 3422795 = 5134193) B5134193
theorem B2281863 : Blo 2281435 2281863 := bstep (se 1 (by rfl) ⟨1711397, by rfl⟩ : syracuseStep 2281863 = 3422795) B3422795
theorem B2567101 : Blo 2281435 2567101 := bbase (se 3 (by rfl) ⟨481331, by rfl⟩ : syracuseStep 2567101 = 962663) (by norm_num)
theorem B3422801 : Blo 2281435 3422801 := bstep (se 2 (by rfl) ⟨1283550, by rfl⟩ : syracuseStep 3422801 = 2567101) B2567101
theorem B2281867 : Blo 2281435 2281867 := bstep (se 1 (by rfl) ⟨1711400, by rfl⟩ : syracuseStep 2281867 = 3422801) B3422801
theorem B7701317 : Blo 2281435 7701317 := bbase (se 4 (by rfl) ⟨721998, by rfl⟩ : syracuseStep 7701317 = 1443997) (by norm_num)
theorem B5134211 : Blo 2281435 5134211 := bstep (se 1 (by rfl) ⟨3850658, by rfl⟩ : syracuseStep 5134211 = 7701317) B7701317
theorem B3422807 : Blo 2281435 3422807 := bstep (se 1 (by rfl) ⟨2567105, by rfl⟩ : syracuseStep 3422807 = 5134211) B5134211
theorem B2281871 : Blo 2281435 2281871 := bstep (se 1 (by rfl) ⟨1711403, by rfl⟩ : syracuseStep 2281871 = 3422807) B3422807
theorem B3422813 : Blo 2281435 3422813 := bbase (se 3 (by rfl) ⟨641777, by rfl⟩ : syracuseStep 3422813 = 1283555) (by norm_num)
theorem B2281875 : Blo 2281435 2281875 := bstep (se 1 (by rfl) ⟨1711406, by rfl⟩ : syracuseStep 2281875 = 3422813) B3422813
theorem B5134229 : Blo 2281435 5134229 := bbase (se 6 (by rfl) ⟨120333, by rfl⟩ : syracuseStep 5134229 = 240667) (by norm_num)
theorem B3422819 : Blo 2281435 3422819 := bstep (se 1 (by rfl) ⟨2567114, by rfl⟩ : syracuseStep 3422819 = 5134229) B5134229
theorem B2281879 : Blo 2281435 2281879 := bstep (se 1 (by rfl) ⟨1711409, by rfl⟩ : syracuseStep 2281879 = 3422819) B3422819
theorem B4873517 : Blo 2281435 4873517 := bbase (se 3 (by rfl) ⟨913784, by rfl⟩ : syracuseStep 4873517 = 1827569) (by norm_num)
theorem B3249011 : Blo 2281435 3249011 := bstep (se 1 (by rfl) ⟨2436758, by rfl⟩ : syracuseStep 3249011 = 4873517) B4873517
theorem B8664029 : Blo 2281435 8664029 := bstep (se 3 (by rfl) ⟨1624505, by rfl⟩ : syracuseStep 8664029 = 3249011) B3249011
theorem B5776019 : Blo 2281435 5776019 := bstep (se 1 (by rfl) ⟨4332014, by rfl⟩ : syracuseStep 5776019 = 8664029) B8664029
theorem B3850679 : Blo 2281435 3850679 := bstep (se 1 (by rfl) ⟨2888009, by rfl⟩ : syracuseStep 3850679 = 5776019) B5776019
theorem B2567119 : Blo 2281435 2567119 := bstep (se 1 (by rfl) ⟨1925339, by rfl⟩ : syracuseStep 2567119 = 3850679) B3850679
theorem B3422825 : Blo 2281435 3422825 := bstep (se 2 (by rfl) ⟨1283559, by rfl⟩ : syracuseStep 3422825 = 2567119) B2567119
theorem B2281883 : Blo 2281435 2281883 := bstep (se 1 (by rfl) ⟨1711412, by rfl⟩ : syracuseStep 2281883 = 3422825) B3422825
theorem B2470009 : Blo 2281435 2470009 := bbase (se 2 (by rfl) ⟨926253, by rfl⟩ : syracuseStep 2470009 = 1852507) (by norm_num)
theorem B3293345 : Blo 2281435 3293345 := bstep (se 2 (by rfl) ⟨1235004, by rfl⟩ : syracuseStep 3293345 = 2470009) B2470009
theorem B8782253 : Blo 2281435 8782253 := bstep (se 3 (by rfl) ⟨1646672, by rfl⟩ : syracuseStep 8782253 = 3293345) B3293345
theorem B5854835 : Blo 2281435 5854835 := bstep (se 1 (by rfl) ⟨4391126, by rfl⟩ : syracuseStep 5854835 = 8782253) B8782253
theorem B3903223 : Blo 2281435 3903223 := bstep (se 1 (by rfl) ⟨2927417, by rfl⟩ : syracuseStep 3903223 = 5854835) B5854835
theorem B5204297 : Blo 2281435 5204297 := bstep (se 2 (by rfl) ⟨1951611, by rfl⟩ : syracuseStep 5204297 = 3903223) B3903223
theorem B13878125 : Blo 2281435 13878125 := bstep (se 3 (by rfl) ⟨2602148, by rfl⟩ : syracuseStep 13878125 = 5204297) B5204297
theorem B9252083 : Blo 2281435 9252083 := bstep (se 1 (by rfl) ⟨6939062, by rfl⟩ : syracuseStep 9252083 = 13878125) B13878125
theorem B24672221 : Blo 2281435 24672221 := bstep (se 3 (by rfl) ⟨4626041, by rfl⟩ : syracuseStep 24672221 = 9252083) B9252083
theorem B16448147 : Blo 2281435 16448147 := bstep (se 1 (by rfl) ⟨12336110, by rfl⟩ : syracuseStep 16448147 = 24672221) B24672221
theorem B10965431 : Blo 2281435 10965431 := bstep (se 1 (by rfl) ⟨8224073, by rfl⟩ : syracuseStep 10965431 = 16448147) B16448147
theorem B7310287 : Blo 2281435 7310287 := bstep (se 1 (by rfl) ⟨5482715, by rfl⟩ : syracuseStep 7310287 = 10965431) B10965431
theorem B9747049 : Blo 2281435 9747049 := bstep (se 2 (by rfl) ⟨3655143, by rfl⟩ : syracuseStep 9747049 = 7310287) B7310287
theorem B12996065 : Blo 2281435 12996065 := bstep (se 2 (by rfl) ⟨4873524, by rfl⟩ : syracuseStep 12996065 = 9747049) B9747049
theorem B8664043 : Blo 2281435 8664043 := bstep (se 1 (by rfl) ⟨6498032, by rfl⟩ : syracuseStep 8664043 = 12996065) B12996065
theorem B11552057 : Blo 2281435 11552057 := bstep (se 2 (by rfl) ⟨4332021, by rfl⟩ : syracuseStep 11552057 = 8664043) B8664043
theorem B7701371 : Blo 2281435 7701371 := bstep (se 1 (by rfl) ⟨5776028, by rfl⟩ : syracuseStep 7701371 = 11552057) B11552057
theorem B5134247 : Blo 2281435 5134247 := bstep (se 1 (by rfl) ⟨3850685, by rfl⟩ : syracuseStep 5134247 = 7701371) B7701371
theorem B3422831 : Blo 2281435 3422831 := bstep (se 1 (by rfl) ⟨2567123, by rfl⟩ : syracuseStep 3422831 = 5134247) B5134247
theorem B2281887 : Blo 2281435 2281887 := bstep (se 1 (by rfl) ⟨1711415, by rfl⟩ : syracuseStep 2281887 = 3422831) B3422831
theorem B3422837 : Blo 2281435 3422837 := bbase (se 5 (by rfl) ⟨160445, by rfl⟩ : syracuseStep 3422837 = 320891) (by norm_num)
theorem B2281891 : Blo 2281435 2281891 := bstep (se 1 (by rfl) ⟨1711418, by rfl⟩ : syracuseStep 2281891 = 3422837) B3422837
theorem B4332037 : Blo 2281435 4332037 := bbase (se 4 (by rfl) ⟨406128, by rfl⟩ : syracuseStep 4332037 = 812257) (by norm_num)
theorem B5776049 : Blo 2281435 5776049 := bstep (se 2 (by rfl) ⟨2166018, by rfl⟩ : syracuseStep 5776049 = 4332037) B4332037
theorem B3850699 : Blo 2281435 3850699 := bstep (se 1 (by rfl) ⟨2888024, by rfl⟩ : syracuseStep 3850699 = 5776049) B5776049
theorem B5134265 : Blo 2281435 5134265 := bstep (se 2 (by rfl) ⟨1925349, by rfl⟩ : syracuseStep 5134265 = 3850699) B3850699
theorem B3422843 : Blo 2281435 3422843 := bstep (se 1 (by rfl) ⟨2567132, by rfl⟩ : syracuseStep 3422843 = 5134265) B5134265
theorem B2281895 : Blo 2281435 2281895 := bstep (se 1 (by rfl) ⟨1711421, by rfl⟩ : syracuseStep 2281895 = 3422843) B3422843
theorem B2567137 : Blo 2281435 2567137 := bbase (se 2 (by rfl) ⟨962676, by rfl⟩ : syracuseStep 2567137 = 1925353) (by norm_num)
theorem B3422849 : Blo 2281435 3422849 := bstep (se 2 (by rfl) ⟨1283568, by rfl⟩ : syracuseStep 3422849 = 2567137) B2567137
theorem B2281899 : Blo 2281435 2281899 := bstep (se 1 (by rfl) ⟨1711424, by rfl⟩ : syracuseStep 2281899 = 3422849) B3422849
theorem B5776069 : Blo 2281435 5776069 := bbase (se 4 (by rfl) ⟨541506, by rfl⟩ : syracuseStep 5776069 = 1083013) (by norm_num)
theorem B7701425 : Blo 2281435 7701425 := bstep (se 2 (by rfl) ⟨2888034, by rfl⟩ : syracuseStep 7701425 = 5776069) B5776069
theorem B5134283 : Blo 2281435 5134283 := bstep (se 1 (by rfl) ⟨3850712, by rfl⟩ : syracuseStep 5134283 = 7701425) B7701425
theorem B3422855 : Blo 2281435 3422855 := bstep (se 1 (by rfl) ⟨2567141, by rfl⟩ : syracuseStep 3422855 = 5134283) B5134283
theorem B2281903 : Blo 2281435 2281903 := bstep (se 1 (by rfl) ⟨1711427, by rfl⟩ : syracuseStep 2281903 = 3422855) B3422855
theorem B3422861 : Blo 2281435 3422861 := bbase (se 3 (by rfl) ⟨641786, by rfl⟩ : syracuseStep 3422861 = 1283573) (by norm_num)
theorem B2281907 : Blo 2281435 2281907 := bstep (se 1 (by rfl) ⟨1711430, by rfl⟩ : syracuseStep 2281907 = 3422861) B3422861
theorem B5134301 : Blo 2281435 5134301 := bbase (se 3 (by rfl) ⟨962681, by rfl⟩ : syracuseStep 5134301 = 1925363) (by norm_num)
theorem B3422867 : Blo 2281435 3422867 := bstep (se 1 (by rfl) ⟨2567150, by rfl⟩ : syracuseStep 3422867 = 5134301) B5134301
theorem B2281911 : Blo 2281435 2281911 := bstep (se 1 (by rfl) ⟨1711433, by rfl⟩ : syracuseStep 2281911 = 3422867) B3422867
theorem B3850733 : Blo 2281435 3850733 := bbase (se 3 (by rfl) ⟨722012, by rfl⟩ : syracuseStep 3850733 = 1444025) (by norm_num)
theorem B2567155 : Blo 2281435 2567155 := bstep (se 1 (by rfl) ⟨1925366, by rfl⟩ : syracuseStep 2567155 = 3850733) B3850733
theorem B3422873 : Blo 2281435 3422873 := bstep (se 2 (by rfl) ⟨1283577, by rfl⟩ : syracuseStep 3422873 = 2567155) B2567155
theorem B2281915 : Blo 2281435 2281915 := bstep (se 1 (by rfl) ⟨1711436, by rfl⟩ : syracuseStep 2281915 = 3422873) B3422873
theorem B29241557 : Blo 2281435 29241557 := bbase (se 7 (by rfl) ⟨342674, by rfl⟩ : syracuseStep 29241557 = 685349) (by norm_num)
theorem B19494371 : Blo 2281435 19494371 := bstep (se 1 (by rfl) ⟨14620778, by rfl⟩ : syracuseStep 19494371 = 29241557) B29241557
theorem B12996247 : Blo 2281435 12996247 := bstep (se 1 (by rfl) ⟨9747185, by rfl⟩ : syracuseStep 12996247 = 19494371) B19494371
theorem B17328329 : Blo 2281435 17328329 := bstep (se 2 (by rfl) ⟨6498123, by rfl⟩ : syracuseStep 17328329 = 12996247) B12996247
theorem B11552219 : Blo 2281435 11552219 := bstep (se 1 (by rfl) ⟨8664164, by rfl⟩ : syracuseStep 11552219 = 17328329) B17328329
theorem B7701479 : Blo 2281435 7701479 := bstep (se 1 (by rfl) ⟨5776109, by rfl⟩ : syracuseStep 7701479 = 11552219) B11552219
theorem B5134319 : Blo 2281435 5134319 := bstep (se 1 (by rfl) ⟨3850739, by rfl⟩ : syracuseStep 5134319 = 7701479) B7701479
theorem B3422879 : Blo 2281435 3422879 := bstep (se 1 (by rfl) ⟨2567159, by rfl⟩ : syracuseStep 3422879 = 5134319) B5134319
theorem B2281919 : Blo 2281435 2281919 := bstep (se 1 (by rfl) ⟨1711439, by rfl⟩ : syracuseStep 2281919 = 3422879) B3422879
theorem B3422885 : Blo 2281435 3422885 := bbase (se 4 (by rfl) ⟨320895, by rfl⟩ : syracuseStep 3422885 = 641791) (by norm_num)
theorem B2281923 : Blo 2281435 2281923 := bstep (se 1 (by rfl) ⟨1711442, by rfl⟩ : syracuseStep 2281923 = 3422885) B3422885
theorem B2888065 : Blo 2281435 2888065 := bbase (se 2 (by rfl) ⟨1083024, by rfl⟩ : syracuseStep 2888065 = 2166049) (by norm_num)
theorem B3850753 : Blo 2281435 3850753 := bstep (se 2 (by rfl) ⟨1444032, by rfl⟩ : syracuseStep 3850753 = 2888065) B2888065
theorem B5134337 : Blo 2281435 5134337 := bstep (se 2 (by rfl) ⟨1925376, by rfl⟩ : syracuseStep 5134337 = 3850753) B3850753
theorem B3422891 : Blo 2281435 3422891 := bstep (se 1 (by rfl) ⟨2567168, by rfl⟩ : syracuseStep 3422891 = 5134337) B5134337
theorem B2281927 : Blo 2281435 2281927 := bstep (se 1 (by rfl) ⟨1711445, by rfl⟩ : syracuseStep 2281927 = 3422891) B3422891
theorem B2567173 : Blo 2281435 2567173 := bbase (se 4 (by rfl) ⟨240672, by rfl⟩ : syracuseStep 2567173 = 481345) (by norm_num)
theorem B3422897 : Blo 2281435 3422897 := bstep (se 2 (by rfl) ⟨1283586, by rfl⟩ : syracuseStep 3422897 = 2567173) B2567173
theorem B2281931 : Blo 2281435 2281931 := bstep (se 1 (by rfl) ⟨1711448, by rfl⟩ : syracuseStep 2281931 = 3422897) B3422897
theorem B3249085 : Blo 2281435 3249085 := bbase (se 3 (by rfl) ⟨609203, by rfl⟩ : syracuseStep 3249085 = 1218407) (by norm_num)
theorem B4332113 : Blo 2281435 4332113 := bstep (se 2 (by rfl) ⟨1624542, by rfl⟩ : syracuseStep 4332113 = 3249085) B3249085
theorem B2888075 : Blo 2281435 2888075 := bstep (se 1 (by rfl) ⟨2166056, by rfl⟩ : syracuseStep 2888075 = 4332113) B4332113
theorem B7701533 : Blo 2281435 7701533 := bstep (se 3 (by rfl) ⟨1444037, by rfl⟩ : syracuseStep 7701533 = 2888075) B2888075
theorem B5134355 : Blo 2281435 5134355 := bstep (se 1 (by rfl) ⟨3850766, by rfl⟩ : syracuseStep 5134355 = 7701533) B7701533
theorem B3422903 : Blo 2281435 3422903 := bstep (se 1 (by rfl) ⟨2567177, by rfl⟩ : syracuseStep 3422903 = 5134355) B5134355
theorem B2281935 : Blo 2281435 2281935 := bstep (se 1 (by rfl) ⟨1711451, by rfl⟩ : syracuseStep 2281935 = 3422903) B3422903
theorem B3422909 : Blo 2281435 3422909 := bbase (se 3 (by rfl) ⟨641795, by rfl⟩ : syracuseStep 3422909 = 1283591) (by norm_num)
theorem B2281939 : Blo 2281435 2281939 := bstep (se 1 (by rfl) ⟨1711454, by rfl⟩ : syracuseStep 2281939 = 3422909) B3422909
theorem B5134373 : Blo 2281435 5134373 := bbase (se 4 (by rfl) ⟨481347, by rfl⟩ : syracuseStep 5134373 = 962695) (by norm_num)
theorem B3422915 : Blo 2281435 3422915 := bstep (se 1 (by rfl) ⟨2567186, by rfl⟩ : syracuseStep 3422915 = 5134373) B5134373
theorem B2281943 : Blo 2281435 2281943 := bstep (se 1 (by rfl) ⟨1711457, by rfl⟩ : syracuseStep 2281943 = 3422915) B3422915
theorem B5776181 : Blo 2281435 5776181 := bbase (se 5 (by rfl) ⟨270758, by rfl⟩ : syracuseStep 5776181 = 541517) (by norm_num)
theorem B3850787 : Blo 2281435 3850787 := bstep (se 1 (by rfl) ⟨2888090, by rfl⟩ : syracuseStep 3850787 = 5776181) B5776181
theorem B2567191 : Blo 2281435 2567191 := bstep (se 1 (by rfl) ⟨1925393, by rfl⟩ : syracuseStep 2567191 = 3850787) B3850787
theorem B3422921 : Blo 2281435 3422921 := bstep (se 2 (by rfl) ⟨1283595, by rfl⟩ : syracuseStep 3422921 = 2567191) B2567191
theorem B2281947 : Blo 2281435 2281947 := bstep (se 1 (by rfl) ⟨1711460, by rfl⟩ : syracuseStep 2281947 = 3422921) B3422921
theorem B13173749 : Blo 2281435 13173749 := bbase (se 5 (by rfl) ⟨617519, by rfl⟩ : syracuseStep 13173749 = 1235039) (by norm_num)
theorem B8782499 : Blo 2281435 8782499 := bstep (se 1 (by rfl) ⟨6586874, by rfl⟩ : syracuseStep 8782499 = 13173749) B13173749
theorem B5854999 : Blo 2281435 5854999 := bstep (se 1 (by rfl) ⟨4391249, by rfl⟩ : syracuseStep 5854999 = 8782499) B8782499
theorem B7806665 : Blo 2281435 7806665 := bstep (se 2 (by rfl) ⟨2927499, by rfl⟩ : syracuseStep 7806665 = 5854999) B5854999
theorem B20817773 : Blo 2281435 20817773 := bstep (se 3 (by rfl) ⟨3903332, by rfl⟩ : syracuseStep 20817773 = 7806665) B7806665
theorem B13878515 : Blo 2281435 13878515 := bstep (se 1 (by rfl) ⟨10408886, by rfl⟩ : syracuseStep 13878515 = 20817773) B20817773
theorem B9252343 : Blo 2281435 9252343 := bstep (se 1 (by rfl) ⟨6939257, by rfl⟩ : syracuseStep 9252343 = 13878515) B13878515
theorem B12336457 : Blo 2281435 12336457 := bstep (se 2 (by rfl) ⟨4626171, by rfl⟩ : syracuseStep 12336457 = 9252343) B9252343
theorem B16448609 : Blo 2281435 16448609 := bstep (se 2 (by rfl) ⟨6168228, by rfl⟩ : syracuseStep 16448609 = 12336457) B12336457
theorem B10965739 : Blo 2281435 10965739 := bstep (se 1 (by rfl) ⟨8224304, by rfl⟩ : syracuseStep 10965739 = 16448609) B16448609
theorem B14620985 : Blo 2281435 14620985 := bstep (se 2 (by rfl) ⟨5482869, by rfl⟩ : syracuseStep 14620985 = 10965739) B10965739
theorem B9747323 : Blo 2281435 9747323 := bstep (se 1 (by rfl) ⟨7310492, by rfl⟩ : syracuseStep 9747323 = 14620985) B14620985
theorem B6498215 : Blo 2281435 6498215 := bstep (se 1 (by rfl) ⟨4873661, by rfl⟩ : syracuseStep 6498215 = 9747323) B9747323
theorem B4332143 : Blo 2281435 4332143 := bstep (se 1 (by rfl) ⟨3249107, by rfl⟩ : syracuseStep 4332143 = 6498215) B6498215
theorem B11552381 : Blo 2281435 11552381 := bstep (se 3 (by rfl) ⟨2166071, by rfl⟩ : syracuseStep 11552381 = 4332143) B4332143
theorem B7701587 : Blo 2281435 7701587 := bstep (se 1 (by rfl) ⟨5776190, by rfl⟩ : syracuseStep 7701587 = 11552381) B11552381
theorem B5134391 : Blo 2281435 5134391 := bstep (se 1 (by rfl) ⟨3850793, by rfl⟩ : syracuseStep 5134391 = 7701587) B7701587
theorem B3422927 : Blo 2281435 3422927 := bstep (se 1 (by rfl) ⟨2567195, by rfl⟩ : syracuseStep 3422927 = 5134391) B5134391
theorem B2281951 : Blo 2281435 2281951 := bstep (se 1 (by rfl) ⟨1711463, by rfl⟩ : syracuseStep 2281951 = 3422927) B3422927
theorem B3422933 : Blo 2281435 3422933 := bbase (se 7 (by rfl) ⟨40112, by rfl⟩ : syracuseStep 3422933 = 80225) (by norm_num)
theorem B2281955 : Blo 2281435 2281955 := bstep (se 1 (by rfl) ⟨1711466, by rfl⟩ : syracuseStep 2281955 = 3422933) B3422933
theorem B5855021 : Blo 2281435 5855021 := bbase (se 3 (by rfl) ⟨1097816, by rfl⟩ : syracuseStep 5855021 = 2195633) (by norm_num)
theorem B3903347 : Blo 2281435 3903347 := bstep (se 1 (by rfl) ⟨2927510, by rfl⟩ : syracuseStep 3903347 = 5855021) B5855021
theorem B10408925 : Blo 2281435 10408925 := bstep (se 3 (by rfl) ⟨1951673, by rfl⟩ : syracuseStep 10408925 = 3903347) B3903347
theorem B6939283 : Blo 2281435 6939283 := bstep (se 1 (by rfl) ⟨5204462, by rfl⟩ : syracuseStep 6939283 = 10408925) B10408925
theorem B9252377 : Blo 2281435 9252377 := bstep (se 2 (by rfl) ⟨3469641, by rfl⟩ : syracuseStep 9252377 = 6939283) B6939283
theorem B6168251 : Blo 2281435 6168251 := bstep (se 1 (by rfl) ⟨4626188, by rfl⟩ : syracuseStep 6168251 = 9252377) B9252377
theorem B16448669 : Blo 2281435 16448669 := bstep (se 3 (by rfl) ⟨3084125, by rfl⟩ : syracuseStep 16448669 = 6168251) B6168251
theorem B10965779 : Blo 2281435 10965779 := bstep (se 1 (by rfl) ⟨8224334, by rfl⟩ : syracuseStep 10965779 = 16448669) B16448669
theorem B7310519 : Blo 2281435 7310519 := bstep (se 1 (by rfl) ⟨5482889, by rfl⟩ : syracuseStep 7310519 = 10965779) B10965779
theorem B4873679 : Blo 2281435 4873679 := bstep (se 1 (by rfl) ⟨3655259, by rfl⟩ : syracuseStep 4873679 = 7310519) B7310519
theorem B3249119 : Blo 2281435 3249119 := bstep (se 1 (by rfl) ⟨2436839, by rfl⟩ : syracuseStep 3249119 = 4873679) B4873679
theorem B8664317 : Blo 2281435 8664317 := bstep (se 3 (by rfl) ⟨1624559, by rfl⟩ : syracuseStep 8664317 = 3249119) B3249119
theorem B5776211 : Blo 2281435 5776211 := bstep (se 1 (by rfl) ⟨4332158, by rfl⟩ : syracuseStep 5776211 = 8664317) B8664317
theorem B3850807 : Blo 2281435 3850807 := bstep (se 1 (by rfl) ⟨2888105, by rfl⟩ : syracuseStep 3850807 = 5776211) B5776211
theorem B5134409 : Blo 2281435 5134409 := bstep (se 2 (by rfl) ⟨1925403, by rfl⟩ : syracuseStep 5134409 = 3850807) B3850807
theorem B3422939 : Blo 2281435 3422939 := bstep (se 1 (by rfl) ⟨2567204, by rfl⟩ : syracuseStep 3422939 = 5134409) B5134409
theorem B2281959 : Blo 2281435 2281959 := bstep (se 1 (by rfl) ⟨1711469, by rfl⟩ : syracuseStep 2281959 = 3422939) B3422939
theorem B2567209 : Blo 2281435 2567209 := bbase (se 2 (by rfl) ⟨962703, by rfl⟩ : syracuseStep 2567209 = 1925407) (by norm_num)
theorem B3422945 : Blo 2281435 3422945 := bstep (se 2 (by rfl) ⟨1283604, by rfl⟩ : syracuseStep 3422945 = 2567209) B2567209
theorem B2281963 : Blo 2281435 2281963 := bstep (se 1 (by rfl) ⟨1711472, by rfl⟩ : syracuseStep 2281963 = 3422945) B3422945
theorem B16673141 : Blo 2281435 16673141 := bbase (se 5 (by rfl) ⟨781553, by rfl⟩ : syracuseStep 16673141 = 1563107) (by norm_num)
theorem B44461709 : Blo 2281435 44461709 := bstep (se 3 (by rfl) ⟨8336570, by rfl⟩ : syracuseStep 44461709 = 16673141) B16673141
theorem B29641139 : Blo 2281435 29641139 := bstep (se 1 (by rfl) ⟨22230854, by rfl⟩ : syracuseStep 29641139 = 44461709) B44461709
theorem B19760759 : Blo 2281435 19760759 := bstep (se 1 (by rfl) ⟨14820569, by rfl⟩ : syracuseStep 19760759 = 29641139) B29641139
theorem B13173839 : Blo 2281435 13173839 := bstep (se 1 (by rfl) ⟨9880379, by rfl⟩ : syracuseStep 13173839 = 19760759) B19760759
theorem B8782559 : Blo 2281435 8782559 := bstep (se 1 (by rfl) ⟨6586919, by rfl⟩ : syracuseStep 8782559 = 13173839) B13173839
theorem B5855039 : Blo 2281435 5855039 := bstep (se 1 (by rfl) ⟨4391279, by rfl⟩ : syracuseStep 5855039 = 8782559) B8782559
theorem B62453749 : Blo 2281435 62453749 := bstep (se 5 (by rfl) ⟨2927519, by rfl⟩ : syracuseStep 62453749 = 5855039) B5855039
theorem B83271665 : Blo 2281435 83271665 := bstep (se 2 (by rfl) ⟨31226874, by rfl⟩ : syracuseStep 83271665 = 62453749) B62453749
theorem B55514443 : Blo 2281435 55514443 := bstep (se 1 (by rfl) ⟨41635832, by rfl⟩ : syracuseStep 55514443 = 83271665) B83271665
theorem B74019257 : Blo 2281435 74019257 := bstep (se 2 (by rfl) ⟨27757221, by rfl⟩ : syracuseStep 74019257 = 55514443) B55514443
theorem B49346171 : Blo 2281435 49346171 := bstep (se 1 (by rfl) ⟨37009628, by rfl⟩ : syracuseStep 49346171 = 74019257) B74019257
theorem B32897447 : Blo 2281435 32897447 := bstep (se 1 (by rfl) ⟨24673085, by rfl⟩ : syracuseStep 32897447 = 49346171) B49346171
theorem B21931631 : Blo 2281435 21931631 := bstep (se 1 (by rfl) ⟨16448723, by rfl⟩ : syracuseStep 21931631 = 32897447) B32897447
theorem B14621087 : Blo 2281435 14621087 := bstep (se 1 (by rfl) ⟨10965815, by rfl⟩ : syracuseStep 14621087 = 21931631) B21931631
theorem B9747391 : Blo 2281435 9747391 := bstep (se 1 (by rfl) ⟨7310543, by rfl⟩ : syracuseStep 9747391 = 14621087) B14621087
theorem B12996521 : Blo 2281435 12996521 := bstep (se 2 (by rfl) ⟨4873695, by rfl⟩ : syracuseStep 12996521 = 9747391) B9747391
theorem B8664347 : Blo 2281435 8664347 := bstep (se 1 (by rfl) ⟨6498260, by rfl⟩ : syracuseStep 8664347 = 12996521) B12996521
theorem B5776231 : Blo 2281435 5776231 := bstep (se 1 (by rfl) ⟨4332173, by rfl⟩ : syracuseStep 5776231 = 8664347) B8664347
theorem B7701641 : Blo 2281435 7701641 := bstep (se 2 (by rfl) ⟨2888115, by rfl⟩ : syracuseStep 7701641 = 5776231) B5776231
theorem B5134427 : Blo 2281435 5134427 := bstep (se 1 (by rfl) ⟨3850820, by rfl⟩ : syracuseStep 5134427 = 7701641) B7701641
theorem B3422951 : Blo 2281435 3422951 := bstep (se 1 (by rfl) ⟨2567213, by rfl⟩ : syracuseStep 3422951 = 5134427) B5134427
theorem B2281967 : Blo 2281435 2281967 := bstep (se 1 (by rfl) ⟨1711475, by rfl⟩ : syracuseStep 2281967 = 3422951) B3422951
theorem B3422957 : Blo 2281435 3422957 := bbase (se 3 (by rfl) ⟨641804, by rfl⟩ : syracuseStep 3422957 = 1283609) (by norm_num)
theorem B2281971 : Blo 2281435 2281971 := bstep (se 1 (by rfl) ⟨1711478, by rfl⟩ : syracuseStep 2281971 = 3422957) B3422957
theorem B5134445 : Blo 2281435 5134445 := bbase (se 3 (by rfl) ⟨962708, by rfl⟩ : syracuseStep 5134445 = 1925417) (by norm_num)
theorem B3422963 : Blo 2281435 3422963 := bstep (se 1 (by rfl) ⟨2567222, by rfl⟩ : syracuseStep 3422963 = 5134445) B5134445
theorem B2281975 : Blo 2281435 2281975 := bstep (se 1 (by rfl) ⟨1711481, by rfl⟩ : syracuseStep 2281975 = 3422963) B3422963
theorem B4332197 : Blo 2281435 4332197 := bbase (se 4 (by rfl) ⟨406143, by rfl⟩ : syracuseStep 4332197 = 812287) (by norm_num)
theorem B2888131 : Blo 2281435 2888131 := bstep (se 1 (by rfl) ⟨2166098, by rfl⟩ : syracuseStep 2888131 = 4332197) B4332197
theorem B3850841 : Blo 2281435 3850841 := bstep (se 2 (by rfl) ⟨1444065, by rfl⟩ : syracuseStep 3850841 = 2888131) B2888131
theorem B2567227 : Blo 2281435 2567227 := bstep (se 1 (by rfl) ⟨1925420, by rfl⟩ : syracuseStep 2567227 = 3850841) B3850841
theorem B3422969 : Blo 2281435 3422969 := bstep (se 2 (by rfl) ⟨1283613, by rfl⟩ : syracuseStep 3422969 = 2567227) B2567227
theorem B2281979 : Blo 2281435 2281979 := bstep (se 1 (by rfl) ⟨1711484, by rfl⟩ : syracuseStep 2281979 = 3422969) B3422969
theorem B3084157 : Blo 2281435 3084157 := bbase (se 3 (by rfl) ⟨578279, by rfl⟩ : syracuseStep 3084157 = 1156559) (by norm_num)
theorem B16448837 : Blo 2281435 16448837 := bstep (se 4 (by rfl) ⟨1542078, by rfl⟩ : syracuseStep 16448837 = 3084157) B3084157
theorem B43863565 : Blo 2281435 43863565 := bstep (se 3 (by rfl) ⟨8224418, by rfl⟩ : syracuseStep 43863565 = 16448837) B16448837
theorem B58484753 : Blo 2281435 58484753 := bstep (se 2 (by rfl) ⟨21931782, by rfl⟩ : syracuseStep 58484753 = 43863565) B43863565
theorem B38989835 : Blo 2281435 38989835 := bstep (se 1 (by rfl) ⟨29242376, by rfl⟩ : syracuseStep 38989835 = 58484753) B58484753
theorem B25993223 : Blo 2281435 25993223 := bstep (se 1 (by rfl) ⟨19494917, by rfl⟩ : syracuseStep 25993223 = 38989835) B38989835
theorem B17328815 : Blo 2281435 17328815 := bstep (se 1 (by rfl) ⟨12996611, by rfl⟩ : syracuseStep 17328815 = 25993223) B25993223
theorem B11552543 : Blo 2281435 11552543 := bstep (se 1 (by rfl) ⟨8664407, by rfl⟩ : syracuseStep 11552543 = 17328815) B17328815
theorem B7701695 : Blo 2281435 7701695 := bstep (se 1 (by rfl) ⟨5776271, by rfl⟩ : syracuseStep 7701695 = 11552543) B11552543
theorem B5134463 : Blo 2281435 5134463 := bstep (se 1 (by rfl) ⟨3850847, by rfl⟩ : syracuseStep 5134463 = 7701695) B7701695
theorem B3422975 : Blo 2281435 3422975 := bstep (se 1 (by rfl) ⟨2567231, by rfl⟩ : syracuseStep 3422975 = 5134463) B5134463
theorem B2281983 : Blo 2281435 2281983 := bstep (se 1 (by rfl) ⟨1711487, by rfl⟩ : syracuseStep 2281983 = 3422975) B3422975
theorem B3422981 : Blo 2281435 3422981 := bbase (se 4 (by rfl) ⟨320904, by rfl⟩ : syracuseStep 3422981 = 641809) (by norm_num)
theorem B2281987 : Blo 2281435 2281987 := bstep (se 1 (by rfl) ⟨1711490, by rfl⟩ : syracuseStep 2281987 = 3422981) B3422981
theorem B3850861 : Blo 2281435 3850861 := bbase (se 3 (by rfl) ⟨722036, by rfl⟩ : syracuseStep 3850861 = 1444073) (by norm_num)
theorem B5134481 : Blo 2281435 5134481 := bstep (se 2 (by rfl) ⟨1925430, by rfl⟩ : syracuseStep 5134481 = 3850861) B3850861
theorem B3422987 : Blo 2281435 3422987 := bstep (se 1 (by rfl) ⟨2567240, by rfl⟩ : syracuseStep 3422987 = 5134481) B5134481
theorem B2281991 : Blo 2281435 2281991 := bstep (se 1 (by rfl) ⟨1711493, by rfl⟩ : syracuseStep 2281991 = 3422987) B3422987
theorem B2567245 : Blo 2281435 2567245 := bbase (se 3 (by rfl) ⟨481358, by rfl⟩ : syracuseStep 2567245 = 962717) (by norm_num)
theorem B3422993 : Blo 2281435 3422993 := bstep (se 2 (by rfl) ⟨1283622, by rfl⟩ : syracuseStep 3422993 = 2567245) B2567245
theorem B2281995 : Blo 2281435 2281995 := bstep (se 1 (by rfl) ⟨1711496, by rfl⟩ : syracuseStep 2281995 = 3422993) B3422993
theorem B7701749 : Blo 2281435 7701749 := bbase (se 5 (by rfl) ⟨361019, by rfl⟩ : syracuseStep 7701749 = 722039) (by norm_num)
theorem B5134499 : Blo 2281435 5134499 := bstep (se 1 (by rfl) ⟨3850874, by rfl⟩ : syracuseStep 5134499 = 7701749) B7701749
theorem B3422999 : Blo 2281435 3422999 := bstep (se 1 (by rfl) ⟨2567249, by rfl⟩ : syracuseStep 3422999 = 5134499) B5134499
theorem B2281999 : Blo 2281435 2281999 := bstep (se 1 (by rfl) ⟨1711499, by rfl⟩ : syracuseStep 2281999 = 3422999) B3422999
theorem B3423005 : Blo 2281435 3423005 := bbase (se 3 (by rfl) ⟨641813, by rfl⟩ : syracuseStep 3423005 = 1283627) (by norm_num)
theorem B2282003 : Blo 2281435 2282003 := bstep (se 1 (by rfl) ⟨1711502, by rfl⟩ : syracuseStep 2282003 = 3423005) B3423005
theorem B5134517 : Blo 2281435 5134517 := bbase (se 5 (by rfl) ⟨240680, by rfl⟩ : syracuseStep 5134517 = 481361) (by norm_num)
theorem B3423011 : Blo 2281435 3423011 := bstep (se 1 (by rfl) ⟨2567258, by rfl⟩ : syracuseStep 3423011 = 5134517) B5134517
theorem B2282007 : Blo 2281435 2282007 := bstep (se 1 (by rfl) ⟨1711505, by rfl⟩ : syracuseStep 2282007 = 3423011) B3423011
theorem B3903437 : Blo 2281435 3903437 := bbase (se 3 (by rfl) ⟨731894, by rfl⟩ : syracuseStep 3903437 = 1463789) (by norm_num)
theorem B2602291 : Blo 2281435 2602291 := bstep (se 1 (by rfl) ⟨1951718, by rfl⟩ : syracuseStep 2602291 = 3903437) B3903437
theorem B3469721 : Blo 2281435 3469721 := bstep (se 2 (by rfl) ⟨1301145, by rfl⟩ : syracuseStep 3469721 = 2602291) B2602291
theorem B9252589 : Blo 2281435 9252589 := bstep (se 3 (by rfl) ⟨1734860, by rfl⟩ : syracuseStep 9252589 = 3469721) B3469721
theorem B12336785 : Blo 2281435 12336785 := bstep (se 2 (by rfl) ⟨4626294, by rfl⟩ : syracuseStep 12336785 = 9252589) B9252589
theorem B8224523 : Blo 2281435 8224523 := bstep (se 1 (by rfl) ⟨6168392, by rfl⟩ : syracuseStep 8224523 = 12336785) B12336785
theorem B5483015 : Blo 2281435 5483015 := bstep (se 1 (by rfl) ⟨4112261, by rfl⟩ : syracuseStep 5483015 = 8224523) B8224523
theorem B3655343 : Blo 2281435 3655343 := bstep (se 1 (by rfl) ⟨2741507, by rfl⟩ : syracuseStep 3655343 = 5483015) B5483015
theorem B2436895 : Blo 2281435 2436895 := bstep (se 1 (by rfl) ⟨1827671, by rfl⟩ : syracuseStep 2436895 = 3655343) B3655343
theorem B12996773 : Blo 2281435 12996773 := bstep (se 4 (by rfl) ⟨1218447, by rfl⟩ : syracuseStep 12996773 = 2436895) B2436895
theorem B8664515 : Blo 2281435 8664515 := bstep (se 1 (by rfl) ⟨6498386, by rfl⟩ : syracuseStep 8664515 = 12996773) B12996773
theorem B5776343 : Blo 2281435 5776343 := bstep (se 1 (by rfl) ⟨4332257, by rfl⟩ : syracuseStep 5776343 = 8664515) B8664515
theorem B3850895 : Blo 2281435 3850895 := bstep (se 1 (by rfl) ⟨2888171, by rfl⟩ : syracuseStep 3850895 = 5776343) B5776343
theorem B2567263 : Blo 2281435 2567263 := bstep (se 1 (by rfl) ⟨1925447, by rfl⟩ : syracuseStep 2567263 = 3850895) B3850895
theorem B3423017 : Blo 2281435 3423017 := bstep (se 2 (by rfl) ⟨1283631, by rfl⟩ : syracuseStep 3423017 = 2567263) B2567263
theorem B2282011 : Blo 2281435 2282011 := bstep (se 1 (by rfl) ⟨1711508, by rfl⟩ : syracuseStep 2282011 = 3423017) B3423017
theorem B3655349 : Blo 2281435 3655349 := bbase (se 5 (by rfl) ⟨171344, by rfl⟩ : syracuseStep 3655349 = 342689) (by norm_num)
theorem B2436899 : Blo 2281435 2436899 := bstep (se 1 (by rfl) ⟨1827674, by rfl⟩ : syracuseStep 2436899 = 3655349) B3655349
theorem B6498397 : Blo 2281435 6498397 := bstep (se 3 (by rfl) ⟨1218449, by rfl⟩ : syracuseStep 6498397 = 2436899) B2436899
theorem B8664529 : Blo 2281435 8664529 := bstep (se 2 (by rfl) ⟨3249198, by rfl⟩ : syracuseStep 8664529 = 6498397) B6498397
theorem B11552705 : Blo 2281435 11552705 := bstep (se 2 (by rfl) ⟨4332264, by rfl⟩ : syracuseStep 11552705 = 8664529) B8664529
theorem B7701803 : Blo 2281435 7701803 := bstep (se 1 (by rfl) ⟨5776352, by rfl⟩ : syracuseStep 7701803 = 11552705) B11552705
theorem B5134535 : Blo 2281435 5134535 := bstep (se 1 (by rfl) ⟨3850901, by rfl⟩ : syracuseStep 5134535 = 7701803) B7701803
theorem B3423023 : Blo 2281435 3423023 := bstep (se 1 (by rfl) ⟨2567267, by rfl⟩ : syracuseStep 3423023 = 5134535) B5134535
theorem B2282015 : Blo 2281435 2282015 := bstep (se 1 (by rfl) ⟨1711511, by rfl⟩ : syracuseStep 2282015 = 3423023) B3423023
theorem B3423029 : Blo 2281435 3423029 := bbase (se 5 (by rfl) ⟨160454, by rfl⟩ : syracuseStep 3423029 = 320909) (by norm_num)
theorem B2282019 : Blo 2281435 2282019 := bstep (se 1 (by rfl) ⟨1711514, by rfl⟩ : syracuseStep 2282019 = 3423029) B3423029
theorem B5776373 : Blo 2281435 5776373 := bbase (se 5 (by rfl) ⟨270767, by rfl⟩ : syracuseStep 5776373 = 541535) (by norm_num)
theorem B3850915 : Blo 2281435 3850915 := bstep (se 1 (by rfl) ⟨2888186, by rfl⟩ : syracuseStep 3850915 = 5776373) B5776373
theorem B5134553 : Blo 2281435 5134553 := bstep (se 2 (by rfl) ⟨1925457, by rfl⟩ : syracuseStep 5134553 = 3850915) B3850915
theorem B3423035 : Blo 2281435 3423035 := bstep (se 1 (by rfl) ⟨2567276, by rfl⟩ : syracuseStep 3423035 = 5134553) B5134553
theorem B2282023 : Blo 2281435 2282023 := bstep (se 1 (by rfl) ⟨1711517, by rfl⟩ : syracuseStep 2282023 = 3423035) B3423035
theorem B2567281 : Blo 2281435 2567281 := bbase (se 2 (by rfl) ⟨962730, by rfl⟩ : syracuseStep 2567281 = 1925461) (by norm_num)
theorem B3423041 : Blo 2281435 3423041 := bstep (se 2 (by rfl) ⟨1283640, by rfl⟩ : syracuseStep 3423041 = 2567281) B2567281
theorem B2282027 : Blo 2281435 2282027 := bstep (se 1 (by rfl) ⟨1711520, by rfl⟩ : syracuseStep 2282027 = 3423041) B3423041
theorem B9880661 : Blo 2281435 9880661 := bbase (se 8 (by rfl) ⟨57894, by rfl⟩ : syracuseStep 9880661 = 115789) (by norm_num)
theorem B26348429 : Blo 2281435 26348429 := bstep (se 3 (by rfl) ⟨4940330, by rfl⟩ : syracuseStep 26348429 = 9880661) B9880661
theorem B17565619 : Blo 2281435 17565619 := bstep (se 1 (by rfl) ⟨13174214, by rfl⟩ : syracuseStep 17565619 = 26348429) B26348429
theorem B23420825 : Blo 2281435 23420825 := bstep (se 2 (by rfl) ⟨8782809, by rfl⟩ : syracuseStep 23420825 = 17565619) B17565619
theorem B15613883 : Blo 2281435 15613883 := bstep (se 1 (by rfl) ⟨11710412, by rfl⟩ : syracuseStep 15613883 = 23420825) B23420825
theorem B10409255 : Blo 2281435 10409255 := bstep (se 1 (by rfl) ⟨7806941, by rfl⟩ : syracuseStep 10409255 = 15613883) B15613883
theorem B6939503 : Blo 2281435 6939503 := bstep (se 1 (by rfl) ⟨5204627, by rfl⟩ : syracuseStep 6939503 = 10409255) B10409255
theorem B4626335 : Blo 2281435 4626335 := bstep (se 1 (by rfl) ⟨3469751, by rfl⟩ : syracuseStep 4626335 = 6939503) B6939503
theorem B3084223 : Blo 2281435 3084223 := bstep (se 1 (by rfl) ⟨2313167, by rfl⟩ : syracuseStep 3084223 = 4626335) B4626335
theorem B4112297 : Blo 2281435 4112297 := bstep (se 2 (by rfl) ⟨1542111, by rfl⟩ : syracuseStep 4112297 = 3084223) B3084223
theorem B2741531 : Blo 2281435 2741531 := bstep (se 1 (by rfl) ⟨2056148, by rfl⟩ : syracuseStep 2741531 = 4112297) B4112297
theorem B7310749 : Blo 2281435 7310749 := bstep (se 3 (by rfl) ⟨1370765, by rfl⟩ : syracuseStep 7310749 = 2741531) B2741531
theorem B9747665 : Blo 2281435 9747665 := bstep (se 2 (by rfl) ⟨3655374, by rfl⟩ : syracuseStep 9747665 = 7310749) B7310749
theorem B6498443 : Blo 2281435 6498443 := bstep (se 1 (by rfl) ⟨4873832, by rfl⟩ : syracuseStep 6498443 = 9747665) B9747665
theorem B4332295 : Blo 2281435 4332295 := bstep (se 1 (by rfl) ⟨3249221, by rfl⟩ : syracuseStep 4332295 = 6498443) B6498443
theorem B5776393 : Blo 2281435 5776393 := bstep (se 2 (by rfl) ⟨2166147, by rfl⟩ : syracuseStep 5776393 = 4332295) B4332295
theorem B7701857 : Blo 2281435 7701857 := bstep (se 2 (by rfl) ⟨2888196, by rfl⟩ : syracuseStep 7701857 = 5776393) B5776393
theorem B5134571 : Blo 2281435 5134571 := bstep (se 1 (by rfl) ⟨3850928, by rfl⟩ : syracuseStep 5134571 = 7701857) B7701857
theorem B3423047 : Blo 2281435 3423047 := bstep (se 1 (by rfl) ⟨2567285, by rfl⟩ : syracuseStep 3423047 = 5134571) B5134571
theorem B2282031 : Blo 2281435 2282031 := bstep (se 1 (by rfl) ⟨1711523, by rfl⟩ : syracuseStep 2282031 = 3423047) B3423047
theorem B3423053 : Blo 2281435 3423053 := bbase (se 3 (by rfl) ⟨641822, by rfl⟩ : syracuseStep 3423053 = 1283645) (by norm_num)
theorem B2282035 : Blo 2281435 2282035 := bstep (se 1 (by rfl) ⟨1711526, by rfl⟩ : syracuseStep 2282035 = 3423053) B3423053
theorem B5134589 : Blo 2281435 5134589 := bbase (se 3 (by rfl) ⟨962735, by rfl⟩ : syracuseStep 5134589 = 1925471) (by norm_num)
theorem B3423059 : Blo 2281435 3423059 := bstep (se 1 (by rfl) ⟨2567294, by rfl⟩ : syracuseStep 3423059 = 5134589) B5134589
theorem B2282039 : Blo 2281435 2282039 := bstep (se 1 (by rfl) ⟨1711529, by rfl⟩ : syracuseStep 2282039 = 3423059) B3423059
theorem B3850949 : Blo 2281435 3850949 := bbase (se 4 (by rfl) ⟨361026, by rfl⟩ : syracuseStep 3850949 = 722053) (by norm_num)
theorem B2567299 : Blo 2281435 2567299 := bstep (se 1 (by rfl) ⟨1925474, by rfl⟩ : syracuseStep 2567299 = 3850949) B3850949
theorem B3423065 : Blo 2281435 3423065 := bstep (se 2 (by rfl) ⟨1283649, by rfl⟩ : syracuseStep 3423065 = 2567299) B2567299
theorem B2282043 : Blo 2281435 2282043 := bstep (se 1 (by rfl) ⟨1711532, by rfl⟩ : syracuseStep 2282043 = 3423065) B3423065
theorem B17329301 : Blo 2281435 17329301 := bbase (se 6 (by rfl) ⟨406155, by rfl⟩ : syracuseStep 17329301 = 812311) (by norm_num)
theorem B11552867 : Blo 2281435 11552867 := bstep (se 1 (by rfl) ⟨8664650, by rfl⟩ : syracuseStep 11552867 = 17329301) B17329301
theorem B7701911 : Blo 2281435 7701911 := bstep (se 1 (by rfl) ⟨5776433, by rfl⟩ : syracuseStep 7701911 = 11552867) B11552867
theorem B5134607 : Blo 2281435 5134607 := bstep (se 1 (by rfl) ⟨3850955, by rfl⟩ : syracuseStep 5134607 = 7701911) B7701911
theorem B3423071 : Blo 2281435 3423071 := bstep (se 1 (by rfl) ⟨2567303, by rfl⟩ : syracuseStep 3423071 = 5134607) B5134607
theorem B2282047 : Blo 2281435 2282047 := bstep (se 1 (by rfl) ⟨1711535, by rfl⟩ : syracuseStep 2282047 = 3423071) B3423071
theorem B3423077 : Blo 2281435 3423077 := bbase (se 4 (by rfl) ⟨320913, by rfl⟩ : syracuseStep 3423077 = 641827) (by norm_num)
theorem B2282051 : Blo 2281435 2282051 := bstep (se 1 (by rfl) ⟨1711538, by rfl⟩ : syracuseStep 2282051 = 3423077) B3423077
theorem B4332341 : Blo 2281435 4332341 := bbase (se 5 (by rfl) ⟨203078, by rfl⟩ : syracuseStep 4332341 = 406157) (by norm_num)
theorem B2888227 : Blo 2281435 2888227 := bstep (se 1 (by rfl) ⟨2166170, by rfl⟩ : syracuseStep 2888227 = 4332341) B4332341
theorem B3850969 : Blo 2281435 3850969 := bstep (se 2 (by rfl) ⟨1444113, by rfl⟩ : syracuseStep 3850969 = 2888227) B2888227
theorem B5134625 : Blo 2281435 5134625 := bstep (se 2 (by rfl) ⟨1925484, by rfl⟩ : syracuseStep 5134625 = 3850969) B3850969
theorem B3423083 : Blo 2281435 3423083 := bstep (se 1 (by rfl) ⟨2567312, by rfl⟩ : syracuseStep 3423083 = 5134625) B5134625
theorem B2282055 : Blo 2281435 2282055 := bstep (se 1 (by rfl) ⟨1711541, by rfl⟩ : syracuseStep 2282055 = 3423083) B3423083
theorem B2567317 : Blo 2281435 2567317 := bbase (se 6 (by rfl) ⟨60171, by rfl⟩ : syracuseStep 2567317 = 120343) (by norm_num)
theorem B3423089 : Blo 2281435 3423089 := bstep (se 2 (by rfl) ⟨1283658, by rfl⟩ : syracuseStep 3423089 = 2567317) B2567317
theorem B2282059 : Blo 2281435 2282059 := bstep (se 1 (by rfl) ⟨1711544, by rfl⟩ : syracuseStep 2282059 = 3423089) B3423089
theorem B2888237 : Blo 2281435 2888237 := bbase (se 3 (by rfl) ⟨541544, by rfl⟩ : syracuseStep 2888237 = 1083089) (by norm_num)
theorem B7701965 : Blo 2281435 7701965 := bstep (se 3 (by rfl) ⟨1444118, by rfl⟩ : syracuseStep 7701965 = 2888237) B2888237
theorem B5134643 : Blo 2281435 5134643 := bstep (se 1 (by rfl) ⟨3850982, by rfl⟩ : syracuseStep 5134643 = 7701965) B7701965
theorem B3423095 : Blo 2281435 3423095 := bstep (se 1 (by rfl) ⟨2567321, by rfl⟩ : syracuseStep 3423095 = 5134643) B5134643
theorem B2282063 : Blo 2281435 2282063 := bstep (se 1 (by rfl) ⟨1711547, by rfl⟩ : syracuseStep 2282063 = 3423095) B3423095
theorem B3423101 : Blo 2281435 3423101 := bbase (se 3 (by rfl) ⟨641831, by rfl⟩ : syracuseStep 3423101 = 1283663) (by norm_num)
theorem B2282067 : Blo 2281435 2282067 := bstep (se 1 (by rfl) ⟨1711550, by rfl⟩ : syracuseStep 2282067 = 3423101) B3423101
theorem B5134661 : Blo 2281435 5134661 := bbase (se 4 (by rfl) ⟨481374, by rfl⟩ : syracuseStep 5134661 = 962749) (by norm_num)
theorem B3423107 : Blo 2281435 3423107 := bstep (se 1 (by rfl) ⟨2567330, by rfl⟩ : syracuseStep 3423107 = 5134661) B5134661
theorem B2282071 : Blo 2281435 2282071 := bstep (se 1 (by rfl) ⟨1711553, by rfl⟩ : syracuseStep 2282071 = 3423107) B3423107
theorem B6168565 : Blo 2281435 6168565 := bbase (se 5 (by rfl) ⟨289151, by rfl⟩ : syracuseStep 6168565 = 578303) (by norm_num)
theorem B8224753 : Blo 2281435 8224753 := bstep (se 2 (by rfl) ⟨3084282, by rfl⟩ : syracuseStep 8224753 = 6168565) B6168565
theorem B10966337 : Blo 2281435 10966337 := bstep (se 2 (by rfl) ⟨4112376, by rfl⟩ : syracuseStep 10966337 = 8224753) B8224753
theorem B7310891 : Blo 2281435 7310891 := bstep (se 1 (by rfl) ⟨5483168, by rfl⟩ : syracuseStep 7310891 = 10966337) B10966337
theorem B4873927 : Blo 2281435 4873927 := bstep (se 1 (by rfl) ⟨3655445, by rfl⟩ : syracuseStep 4873927 = 7310891) B7310891
theorem B6498569 : Blo 2281435 6498569 := bstep (se 2 (by rfl) ⟨2436963, by rfl⟩ : syracuseStep 6498569 = 4873927) B4873927
theorem B4332379 : Blo 2281435 4332379 := bstep (se 1 (by rfl) ⟨3249284, by rfl⟩ : syracuseStep 4332379 = 6498569) B6498569
theorem B5776505 : Blo 2281435 5776505 := bstep (se 2 (by rfl) ⟨2166189, by rfl⟩ : syracuseStep 5776505 = 4332379) B4332379
theorem B3851003 : Blo 2281435 3851003 := bstep (se 1 (by rfl) ⟨2888252, by rfl⟩ : syracuseStep 3851003 = 5776505) B5776505
theorem B2567335 : Blo 2281435 2567335 := bstep (se 1 (by rfl) ⟨1925501, by rfl⟩ : syracuseStep 2567335 = 3851003) B3851003
theorem B3423113 : Blo 2281435 3423113 := bstep (se 2 (by rfl) ⟨1283667, by rfl⟩ : syracuseStep 3423113 = 2567335) B2567335
theorem B2282075 : Blo 2281435 2282075 := bstep (se 1 (by rfl) ⟨1711556, by rfl⟩ : syracuseStep 2282075 = 3423113) B3423113
theorem B11553029 : Blo 2281435 11553029 := bbase (se 4 (by rfl) ⟨1083096, by rfl⟩ : syracuseStep 11553029 = 2166193) (by norm_num)
theorem B7702019 : Blo 2281435 7702019 := bstep (se 1 (by rfl) ⟨5776514, by rfl⟩ : syracuseStep 7702019 = 11553029) B11553029
theorem B5134679 : Blo 2281435 5134679 := bstep (se 1 (by rfl) ⟨3851009, by rfl⟩ : syracuseStep 5134679 = 7702019) B7702019
theorem B3423119 : Blo 2281435 3423119 := bstep (se 1 (by rfl) ⟨2567339, by rfl⟩ : syracuseStep 3423119 = 5134679) B5134679
theorem B2282079 : Blo 2281435 2282079 := bstep (se 1 (by rfl) ⟨1711559, by rfl⟩ : syracuseStep 2282079 = 3423119) B3423119
theorem B3423125 : Blo 2281435 3423125 := bbase (se 6 (by rfl) ⟨80229, by rfl⟩ : syracuseStep 3423125 = 160459) (by norm_num)
theorem B2282083 : Blo 2281435 2282083 := bstep (se 1 (by rfl) ⟨1711562, by rfl⟩ : syracuseStep 2282083 = 3423125) B3423125
theorem B12997205 : Blo 2281435 12997205 := bbase (se 8 (by rfl) ⟨76155, by rfl⟩ : syracuseStep 12997205 = 152311) (by norm_num)
theorem B8664803 : Blo 2281435 8664803 := bstep (se 1 (by rfl) ⟨6498602, by rfl⟩ : syracuseStep 8664803 = 12997205) B12997205
theorem B5776535 : Blo 2281435 5776535 := bstep (se 1 (by rfl) ⟨4332401, by rfl⟩ : syracuseStep 5776535 = 8664803) B8664803
theorem B3851023 : Blo 2281435 3851023 := bstep (se 1 (by rfl) ⟨2888267, by rfl⟩ : syracuseStep 3851023 = 5776535) B5776535
theorem B5134697 : Blo 2281435 5134697 := bstep (se 2 (by rfl) ⟨1925511, by rfl⟩ : syracuseStep 5134697 = 3851023) B3851023
theorem B3423131 : Blo 2281435 3423131 := bstep (se 1 (by rfl) ⟨2567348, by rfl⟩ : syracuseStep 3423131 = 5134697) B5134697
theorem B2282087 : Blo 2281435 2282087 := bstep (se 1 (by rfl) ⟨1711565, by rfl⟩ : syracuseStep 2282087 = 3423131) B3423131
theorem B2567353 : Blo 2281435 2567353 := bbase (se 2 (by rfl) ⟨962757, by rfl⟩ : syracuseStep 2567353 = 1925515) (by norm_num)
theorem B3423137 : Blo 2281435 3423137 := bstep (se 2 (by rfl) ⟨1283676, by rfl⟩ : syracuseStep 3423137 = 2567353) B2567353
theorem B2282091 : Blo 2281435 2282091 := bstep (se 1 (by rfl) ⟨1711568, by rfl⟩ : syracuseStep 2282091 = 3423137) B3423137
theorem B3655477 : Blo 2281435 3655477 := bbase (se 5 (by rfl) ⟨171350, by rfl⟩ : syracuseStep 3655477 = 342701) (by norm_num)
theorem B4873969 : Blo 2281435 4873969 := bstep (se 2 (by rfl) ⟨1827738, by rfl⟩ : syracuseStep 4873969 = 3655477) B3655477
theorem B6498625 : Blo 2281435 6498625 := bstep (se 2 (by rfl) ⟨2436984, by rfl⟩ : syracuseStep 6498625 = 4873969) B4873969
theorem B8664833 : Blo 2281435 8664833 := bstep (se 2 (by rfl) ⟨3249312, by rfl⟩ : syracuseStep 8664833 = 6498625) B6498625
theorem B5776555 : Blo 2281435 5776555 := bstep (se 1 (by rfl) ⟨4332416, by rfl⟩ : syracuseStep 5776555 = 8664833) B8664833
theorem B7702073 : Blo 2281435 7702073 := bstep (se 2 (by rfl) ⟨2888277, by rfl⟩ : syracuseStep 7702073 = 5776555) B5776555
theorem B5134715 : Blo 2281435 5134715 := bstep (se 1 (by rfl) ⟨3851036, by rfl⟩ : syracuseStep 5134715 = 7702073) B7702073
theorem B3423143 : Blo 2281435 3423143 := bstep (se 1 (by rfl) ⟨2567357, by rfl⟩ : syracuseStep 3423143 = 5134715) B5134715
theorem B2282095 : Blo 2281435 2282095 := bstep (se 1 (by rfl) ⟨1711571, by rfl⟩ : syracuseStep 2282095 = 3423143) B3423143
theorem B3423149 : Blo 2281435 3423149 := bbase (se 3 (by rfl) ⟨641840, by rfl⟩ : syracuseStep 3423149 = 1283681) (by norm_num)
theorem B2282099 : Blo 2281435 2282099 := bstep (se 1 (by rfl) ⟨1711574, by rfl⟩ : syracuseStep 2282099 = 3423149) B3423149
theorem B5134733 : Blo 2281435 5134733 := bbase (se 3 (by rfl) ⟨962762, by rfl⟩ : syracuseStep 5134733 = 1925525) (by norm_num)
theorem B3423155 : Blo 2281435 3423155 := bstep (se 1 (by rfl) ⟨2567366, by rfl⟩ : syracuseStep 3423155 = 5134733) B5134733
theorem B2282103 : Blo 2281435 2282103 := bstep (se 1 (by rfl) ⟨1711577, by rfl⟩ : syracuseStep 2282103 = 3423155) B3423155
theorem B2888293 : Blo 2281435 2888293 := bbase (se 4 (by rfl) ⟨270777, by rfl⟩ : syracuseStep 2888293 = 541555) (by norm_num)
theorem B3851057 : Blo 2281435 3851057 := bstep (se 2 (by rfl) ⟨1444146, by rfl⟩ : syracuseStep 3851057 = 2888293) B2888293
theorem B2567371 : Blo 2281435 2567371 := bstep (se 1 (by rfl) ⟨1925528, by rfl⟩ : syracuseStep 2567371 = 3851057) B3851057
theorem B3423161 : Blo 2281435 3423161 := bstep (se 2 (by rfl) ⟨1283685, by rfl⟩ : syracuseStep 3423161 = 2567371) B2567371
theorem B2282107 : Blo 2281435 2282107 := bstep (se 1 (by rfl) ⟨1711580, by rfl⟩ : syracuseStep 2282107 = 3423161) B3423161
theorem B21933013 : Blo 2281435 21933013 := bbase (se 7 (by rfl) ⟨257027, by rfl⟩ : syracuseStep 21933013 = 514055) (by norm_num)
theorem B29244017 : Blo 2281435 29244017 := bstep (se 2 (by rfl) ⟨10966506, by rfl⟩ : syracuseStep 29244017 = 21933013) B21933013
theorem B19496011 : Blo 2281435 19496011 := bstep (se 1 (by rfl) ⟨14622008, by rfl⟩ : syracuseStep 19496011 = 29244017) B29244017
theorem B25994681 : Blo 2281435 25994681 := bstep (se 2 (by rfl) ⟨9748005, by rfl⟩ : syracuseStep 25994681 = 19496011) B19496011
theorem B17329787 : Blo 2281435 17329787 := bstep (se 1 (by rfl) ⟨12997340, by rfl⟩ : syracuseStep 17329787 = 25994681) B25994681
theorem B11553191 : Blo 2281435 11553191 := bstep (se 1 (by rfl) ⟨8664893, by rfl⟩ : syracuseStep 11553191 = 17329787) B17329787
theorem B7702127 : Blo 2281435 7702127 := bstep (se 1 (by rfl) ⟨5776595, by rfl⟩ : syracuseStep 7702127 = 11553191) B11553191
theorem B5134751 : Blo 2281435 5134751 := bstep (se 1 (by rfl) ⟨3851063, by rfl⟩ : syracuseStep 5134751 = 7702127) B7702127
theorem B3423167 : Blo 2281435 3423167 := bstep (se 1 (by rfl) ⟨2567375, by rfl⟩ : syracuseStep 3423167 = 5134751) B5134751
theorem B2282111 : Blo 2281435 2282111 := bstep (se 1 (by rfl) ⟨1711583, by rfl⟩ : syracuseStep 2282111 = 3423167) B3423167
theorem B3423173 : Blo 2281435 3423173 := bbase (se 4 (by rfl) ⟨320922, by rfl⟩ : syracuseStep 3423173 = 641845) (by norm_num)
theorem B2282115 : Blo 2281435 2282115 := bstep (se 1 (by rfl) ⟨1711586, by rfl⟩ : syracuseStep 2282115 = 3423173) B3423173
theorem B3851077 : Blo 2281435 3851077 := bbase (se 4 (by rfl) ⟨361038, by rfl⟩ : syracuseStep 3851077 = 722077) (by norm_num)
theorem B5134769 : Blo 2281435 5134769 := bstep (se 2 (by rfl) ⟨1925538, by rfl⟩ : syracuseStep 5134769 = 3851077) B3851077
theorem B3423179 : Blo 2281435 3423179 := bstep (se 1 (by rfl) ⟨2567384, by rfl⟩ : syracuseStep 3423179 = 5134769) B5134769
theorem B2282119 : Blo 2281435 2282119 := bstep (se 1 (by rfl) ⟨1711589, by rfl⟩ : syracuseStep 2282119 = 3423179) B3423179
theorem B2567389 : Blo 2281435 2567389 := bbase (se 3 (by rfl) ⟨481385, by rfl⟩ : syracuseStep 2567389 = 962771) (by norm_num)
theorem B3423185 : Blo 2281435 3423185 := bstep (se 2 (by rfl) ⟨1283694, by rfl⟩ : syracuseStep 3423185 = 2567389) B2567389
theorem B2282123 : Blo 2281435 2282123 := bstep (se 1 (by rfl) ⟨1711592, by rfl⟩ : syracuseStep 2282123 = 3423185) B3423185
theorem B7702181 : Blo 2281435 7702181 := bbase (se 4 (by rfl) ⟨722079, by rfl⟩ : syracuseStep 7702181 = 1444159) (by norm_num)
theorem B5134787 : Blo 2281435 5134787 := bstep (se 1 (by rfl) ⟨3851090, by rfl⟩ : syracuseStep 5134787 = 7702181) B7702181
theorem B3423191 : Blo 2281435 3423191 := bstep (se 1 (by rfl) ⟨2567393, by rfl⟩ : syracuseStep 3423191 = 5134787) B5134787
theorem B2282127 : Blo 2281435 2282127 := bstep (se 1 (by rfl) ⟨1711595, by rfl⟩ : syracuseStep 2282127 = 3423191) B3423191
theorem B3423197 : Blo 2281435 3423197 := bbase (se 3 (by rfl) ⟨641849, by rfl⟩ : syracuseStep 3423197 = 1283699) (by norm_num)
theorem B2282131 : Blo 2281435 2282131 := bstep (se 1 (by rfl) ⟨1711598, by rfl⟩ : syracuseStep 2282131 = 3423197) B3423197
theorem B5134805 : Blo 2281435 5134805 := bbase (se 7 (by rfl) ⟨60173, by rfl⟩ : syracuseStep 5134805 = 120347) (by norm_num)
theorem B3423203 : Blo 2281435 3423203 := bstep (se 1 (by rfl) ⟨2567402, by rfl⟩ : syracuseStep 3423203 = 5134805) B5134805
theorem B2282135 : Blo 2281435 2282135 := bstep (se 1 (by rfl) ⟨1711601, by rfl⟩ : syracuseStep 2282135 = 3423203) B3423203
theorem B2967685 : Blo 2281435 2967685 := bbase (se 4 (by rfl) ⟨278220, by rfl⟩ : syracuseStep 2967685 = 556441) (by norm_num)
theorem B15827653 : Blo 2281435 15827653 := bstep (se 4 (by rfl) ⟨1483842, by rfl⟩ : syracuseStep 15827653 = 2967685) B2967685
theorem B21103537 : Blo 2281435 21103537 := bstep (se 2 (by rfl) ⟨7913826, by rfl⟩ : syracuseStep 21103537 = 15827653) B15827653
theorem B28138049 : Blo 2281435 28138049 := bstep (se 2 (by rfl) ⟨10551768, by rfl⟩ : syracuseStep 28138049 = 21103537) B21103537
theorem B18758699 : Blo 2281435 18758699 := bstep (se 1 (by rfl) ⟨14069024, by rfl⟩ : syracuseStep 18758699 = 28138049) B28138049
theorem B12505799 : Blo 2281435 12505799 := bstep (se 1 (by rfl) ⟨9379349, by rfl⟩ : syracuseStep 12505799 = 18758699) B18758699
theorem B33348797 : Blo 2281435 33348797 := bstep (se 3 (by rfl) ⟨6252899, by rfl⟩ : syracuseStep 33348797 = 12505799) B12505799
theorem B22232531 : Blo 2281435 22232531 := bstep (se 1 (by rfl) ⟨16674398, by rfl⟩ : syracuseStep 22232531 = 33348797) B33348797
theorem B14821687 : Blo 2281435 14821687 := bstep (se 1 (by rfl) ⟨11116265, by rfl⟩ : syracuseStep 14821687 = 22232531) B22232531
theorem B79048997 : Blo 2281435 79048997 := bstep (se 4 (by rfl) ⟨7410843, by rfl⟩ : syracuseStep 79048997 = 14821687) B14821687
theorem B52699331 : Blo 2281435 52699331 := bstep (se 1 (by rfl) ⟨39524498, by rfl⟩ : syracuseStep 52699331 = 79048997) B79048997
theorem B35132887 : Blo 2281435 35132887 := bstep (se 1 (by rfl) ⟨26349665, by rfl⟩ : syracuseStep 35132887 = 52699331) B52699331
theorem B46843849 : Blo 2281435 46843849 := bstep (se 2 (by rfl) ⟨17566443, by rfl⟩ : syracuseStep 46843849 = 35132887) B35132887
theorem B62458465 : Blo 2281435 62458465 := bstep (se 2 (by rfl) ⟨23421924, by rfl⟩ : syracuseStep 62458465 = 46843849) B46843849
theorem B83277953 : Blo 2281435 83277953 := bstep (se 2 (by rfl) ⟨31229232, by rfl⟩ : syracuseStep 83277953 = 62458465) B62458465
theorem B55518635 : Blo 2281435 55518635 := bstep (se 1 (by rfl) ⟨41638976, by rfl⟩ : syracuseStep 55518635 = 83277953) B83277953
theorem B37012423 : Blo 2281435 37012423 := bstep (se 1 (by rfl) ⟨27759317, by rfl⟩ : syracuseStep 37012423 = 55518635) B55518635
theorem B49349897 : Blo 2281435 49349897 := bstep (se 2 (by rfl) ⟨18506211, by rfl⟩ : syracuseStep 49349897 = 37012423) B37012423
theorem B32899931 : Blo 2281435 32899931 := bstep (se 1 (by rfl) ⟨24674948, by rfl⟩ : syracuseStep 32899931 = 49349897) B49349897
theorem B21933287 : Blo 2281435 21933287 := bstep (se 1 (by rfl) ⟨16449965, by rfl⟩ : syracuseStep 21933287 = 32899931) B32899931
theorem B14622191 : Blo 2281435 14622191 := bstep (se 1 (by rfl) ⟨10966643, by rfl⟩ : syracuseStep 14622191 = 21933287) B21933287
theorem B9748127 : Blo 2281435 9748127 := bstep (se 1 (by rfl) ⟨7311095, by rfl⟩ : syracuseStep 9748127 = 14622191) B14622191
theorem B6498751 : Blo 2281435 6498751 := bstep (se 1 (by rfl) ⟨4874063, by rfl⟩ : syracuseStep 6498751 = 9748127) B9748127
theorem B8665001 : Blo 2281435 8665001 := bstep (se 2 (by rfl) ⟨3249375, by rfl⟩ : syracuseStep 8665001 = 6498751) B6498751
theorem B5776667 : Blo 2281435 5776667 := bstep (se 1 (by rfl) ⟨4332500, by rfl⟩ : syracuseStep 5776667 = 8665001) B8665001
theorem B3851111 : Blo 2281435 3851111 := bstep (se 1 (by rfl) ⟨2888333, by rfl⟩ : syracuseStep 3851111 = 5776667) B5776667
theorem B2567407 : Blo 2281435 2567407 := bstep (se 1 (by rfl) ⟨1925555, by rfl⟩ : syracuseStep 2567407 = 3851111) B3851111
theorem B3423209 : Blo 2281435 3423209 := bstep (se 2 (by rfl) ⟨1283703, by rfl⟩ : syracuseStep 3423209 = 2567407) B2567407
theorem B2282139 : Blo 2281435 2282139 := bstep (se 1 (by rfl) ⟨1711604, by rfl⟩ : syracuseStep 2282139 = 3423209) B3423209
theorem B10966661 : Blo 2281435 10966661 := bbase (se 4 (by rfl) ⟨1028124, by rfl⟩ : syracuseStep 10966661 = 2056249) (by norm_num)
theorem B7311107 : Blo 2281435 7311107 := bstep (se 1 (by rfl) ⟨5483330, by rfl⟩ : syracuseStep 7311107 = 10966661) B10966661
theorem B19496285 : Blo 2281435 19496285 := bstep (se 3 (by rfl) ⟨3655553, by rfl⟩ : syracuseStep 19496285 = 7311107) B7311107
theorem B12997523 : Blo 2281435 12997523 := bstep (se 1 (by rfl) ⟨9748142, by rfl⟩ : syracuseStep 12997523 = 19496285) B19496285
theorem B8665015 : Blo 2281435 8665015 := bstep (se 1 (by rfl) ⟨6498761, by rfl⟩ : syracuseStep 8665015 = 12997523) B12997523
theorem B11553353 : Blo 2281435 11553353 := bstep (se 2 (by rfl) ⟨4332507, by rfl⟩ : syracuseStep 11553353 = 8665015) B8665015
theorem B7702235 : Blo 2281435 7702235 := bstep (se 1 (by rfl) ⟨5776676, by rfl⟩ : syracuseStep 7702235 = 11553353) B11553353
theorem B5134823 : Blo 2281435 5134823 := bstep (se 1 (by rfl) ⟨3851117, by rfl⟩ : syracuseStep 5134823 = 7702235) B7702235
theorem B3423215 : Blo 2281435 3423215 := bstep (se 1 (by rfl) ⟨2567411, by rfl⟩ : syracuseStep 3423215 = 5134823) B5134823
theorem B2282143 : Blo 2281435 2282143 := bstep (se 1 (by rfl) ⟨1711607, by rfl⟩ : syracuseStep 2282143 = 3423215) B3423215
theorem B3423221 : Blo 2281435 3423221 := bbase (se 5 (by rfl) ⟨160463, by rfl⟩ : syracuseStep 3423221 = 320927) (by norm_num)
theorem B2282147 : Blo 2281435 2282147 := bstep (se 1 (by rfl) ⟨1711610, by rfl⟩ : syracuseStep 2282147 = 3423221) B3423221
theorem B2313289 : Blo 2281435 2313289 := bbase (se 2 (by rfl) ⟨867483, by rfl⟩ : syracuseStep 2313289 = 1734967) (by norm_num)
theorem B12337541 : Blo 2281435 12337541 := bstep (se 4 (by rfl) ⟨1156644, by rfl⟩ : syracuseStep 12337541 = 2313289) B2313289
theorem B8225027 : Blo 2281435 8225027 := bstep (se 1 (by rfl) ⟨6168770, by rfl⟩ : syracuseStep 8225027 = 12337541) B12337541
theorem B5483351 : Blo 2281435 5483351 := bstep (se 1 (by rfl) ⟨4112513, by rfl⟩ : syracuseStep 5483351 = 8225027) B8225027
theorem B3655567 : Blo 2281435 3655567 := bstep (se 1 (by rfl) ⟨2741675, by rfl⟩ : syracuseStep 3655567 = 5483351) B5483351
theorem B4874089 : Blo 2281435 4874089 := bstep (se 2 (by rfl) ⟨1827783, by rfl⟩ : syracuseStep 4874089 = 3655567) B3655567
theorem B6498785 : Blo 2281435 6498785 := bstep (se 2 (by rfl) ⟨2437044, by rfl⟩ : syracuseStep 6498785 = 4874089) B4874089
theorem B4332523 : Blo 2281435 4332523 := bstep (se 1 (by rfl) ⟨3249392, by rfl⟩ : syracuseStep 4332523 = 6498785) B6498785
theorem B5776697 : Blo 2281435 5776697 := bstep (se 2 (by rfl) ⟨2166261, by rfl⟩ : syracuseStep 5776697 = 4332523) B4332523
theorem B3851131 : Blo 2281435 3851131 := bstep (se 1 (by rfl) ⟨2888348, by rfl⟩ : syracuseStep 3851131 = 5776697) B5776697
theorem B5134841 : Blo 2281435 5134841 := bstep (se 2 (by rfl) ⟨1925565, by rfl⟩ : syracuseStep 5134841 = 3851131) B3851131
theorem B3423227 : Blo 2281435 3423227 := bstep (se 1 (by rfl) ⟨2567420, by rfl⟩ : syracuseStep 3423227 = 5134841) B5134841
theorem B2282151 : Blo 2281435 2282151 := bstep (se 1 (by rfl) ⟨1711613, by rfl⟩ : syracuseStep 2282151 = 3423227) B3423227
theorem B2567425 : Blo 2281435 2567425 := bbase (se 2 (by rfl) ⟨962784, by rfl⟩ : syracuseStep 2567425 = 1925569) (by norm_num)
theorem B3423233 : Blo 2281435 3423233 := bstep (se 2 (by rfl) ⟨1283712, by rfl⟩ : syracuseStep 3423233 = 2567425) B2567425
theorem B2282155 : Blo 2281435 2282155 := bstep (se 1 (by rfl) ⟨1711616, by rfl⟩ : syracuseStep 2282155 = 3423233) B3423233
theorem B5776717 : Blo 2281435 5776717 := bbase (se 3 (by rfl) ⟨1083134, by rfl⟩ : syracuseStep 5776717 = 2166269) (by norm_num)
theorem B7702289 : Blo 2281435 7702289 := bstep (se 2 (by rfl) ⟨2888358, by rfl⟩ : syracuseStep 7702289 = 5776717) B5776717
theorem B5134859 : Blo 2281435 5134859 := bstep (se 1 (by rfl) ⟨3851144, by rfl⟩ : syracuseStep 5134859 = 7702289) B7702289
theorem B3423239 : Blo 2281435 3423239 := bstep (se 1 (by rfl) ⟨2567429, by rfl⟩ : syracuseStep 3423239 = 5134859) B5134859
theorem B2282159 : Blo 2281435 2282159 := bstep (se 1 (by rfl) ⟨1711619, by rfl⟩ : syracuseStep 2282159 = 3423239) B3423239
theorem B3423245 : Blo 2281435 3423245 := bbase (se 3 (by rfl) ⟨641858, by rfl⟩ : syracuseStep 3423245 = 1283717) (by norm_num)
theorem B2282163 : Blo 2281435 2282163 := bstep (se 1 (by rfl) ⟨1711622, by rfl⟩ : syracuseStep 2282163 = 3423245) B3423245
theorem B5134877 : Blo 2281435 5134877 := bbase (se 3 (by rfl) ⟨962789, by rfl⟩ : syracuseStep 5134877 = 1925579) (by norm_num)
theorem B3423251 : Blo 2281435 3423251 := bstep (se 1 (by rfl) ⟨2567438, by rfl⟩ : syracuseStep 3423251 = 5134877) B5134877
theorem B2282167 : Blo 2281435 2282167 := bstep (se 1 (by rfl) ⟨1711625, by rfl⟩ : syracuseStep 2282167 = 3423251) B3423251
theorem B3851165 : Blo 2281435 3851165 := bbase (se 3 (by rfl) ⟨722093, by rfl⟩ : syracuseStep 3851165 = 1444187) (by norm_num)
theorem B2567443 : Blo 2281435 2567443 := bstep (se 1 (by rfl) ⟨1925582, by rfl⟩ : syracuseStep 2567443 = 3851165) B3851165
theorem B3423257 : Blo 2281435 3423257 := bstep (se 2 (by rfl) ⟨1283721, by rfl⟩ : syracuseStep 3423257 = 2567443) B2567443
theorem B2282171 : Blo 2281435 2282171 := bstep (se 1 (by rfl) ⟨1711628, by rfl⟩ : syracuseStep 2282171 = 3423257) B3423257
theorem B2602477 : Blo 2281435 2602477 := bbase (se 3 (by rfl) ⟨487964, by rfl⟩ : syracuseStep 2602477 = 975929) (by norm_num)
theorem B3469969 : Blo 2281435 3469969 := bstep (se 2 (by rfl) ⟨1301238, by rfl⟩ : syracuseStep 3469969 = 2602477) B2602477
theorem B18506501 : Blo 2281435 18506501 := bstep (se 4 (by rfl) ⟨1734984, by rfl⟩ : syracuseStep 18506501 = 3469969) B3469969
theorem B12337667 : Blo 2281435 12337667 := bstep (se 1 (by rfl) ⟨9253250, by rfl⟩ : syracuseStep 12337667 = 18506501) B18506501
theorem B8225111 : Blo 2281435 8225111 := bstep (se 1 (by rfl) ⟨6168833, by rfl⟩ : syracuseStep 8225111 = 12337667) B12337667
theorem B21933629 : Blo 2281435 21933629 := bstep (se 3 (by rfl) ⟨4112555, by rfl⟩ : syracuseStep 21933629 = 8225111) B8225111
theorem B14622419 : Blo 2281435 14622419 := bstep (se 1 (by rfl) ⟨10966814, by rfl⟩ : syracuseStep 14622419 = 21933629) B21933629
theorem B9748279 : Blo 2281435 9748279 := bstep (se 1 (by rfl) ⟨7311209, by rfl⟩ : syracuseStep 9748279 = 14622419) B14622419
theorem B12997705 : Blo 2281435 12997705 := bstep (se 2 (by rfl) ⟨4874139, by rfl⟩ : syracuseStep 12997705 = 9748279) B9748279
theorem B17330273 : Blo 2281435 17330273 := bstep (se 2 (by rfl) ⟨6498852, by rfl⟩ : syracuseStep 17330273 = 12997705) B12997705
theorem B11553515 : Blo 2281435 11553515 := bstep (se 1 (by rfl) ⟨8665136, by rfl⟩ : syracuseStep 11553515 = 17330273) B17330273
theorem B7702343 : Blo 2281435 7702343 := bstep (se 1 (by rfl) ⟨5776757, by rfl⟩ : syracuseStep 7702343 = 11553515) B11553515
theorem B5134895 : Blo 2281435 5134895 := bstep (se 1 (by rfl) ⟨3851171, by rfl⟩ : syracuseStep 5134895 = 7702343) B7702343
theorem B3423263 : Blo 2281435 3423263 := bstep (se 1 (by rfl) ⟨2567447, by rfl⟩ : syracuseStep 3423263 = 5134895) B5134895
theorem B2282175 : Blo 2281435 2282175 := bstep (se 1 (by rfl) ⟨1711631, by rfl⟩ : syracuseStep 2282175 = 3423263) B3423263
theorem B3423269 : Blo 2281435 3423269 := bbase (se 4 (by rfl) ⟨320931, by rfl⟩ : syracuseStep 3423269 = 641863) (by norm_num)
theorem B2282179 : Blo 2281435 2282179 := bstep (se 1 (by rfl) ⟨1711634, by rfl⟩ : syracuseStep 2282179 = 3423269) B3423269
theorem B2888389 : Blo 2281435 2888389 := bbase (se 4 (by rfl) ⟨270786, by rfl⟩ : syracuseStep 2888389 = 541573) (by norm_num)
theorem B3851185 : Blo 2281435 3851185 := bstep (se 2 (by rfl) ⟨1444194, by rfl⟩ : syracuseStep 3851185 = 2888389) B2888389
theorem B5134913 : Blo 2281435 5134913 := bstep (se 2 (by rfl) ⟨1925592, by rfl⟩ : syracuseStep 5134913 = 3851185) B3851185
theorem B3423275 : Blo 2281435 3423275 := bstep (se 1 (by rfl) ⟨2567456, by rfl⟩ : syracuseStep 3423275 = 5134913) B5134913
theorem B2282183 : Blo 2281435 2282183 := bstep (se 1 (by rfl) ⟨1711637, by rfl⟩ : syracuseStep 2282183 = 3423275) B3423275
theorem B2567461 : Blo 2281435 2567461 := bbase (se 4 (by rfl) ⟨240699, by rfl⟩ : syracuseStep 2567461 = 481399) (by norm_num)
theorem B3423281 : Blo 2281435 3423281 := bstep (se 2 (by rfl) ⟨1283730, by rfl⟩ : syracuseStep 3423281 = 2567461) B2567461
theorem B2282187 : Blo 2281435 2282187 := bstep (se 1 (by rfl) ⟨1711640, by rfl⟩ : syracuseStep 2282187 = 3423281) B3423281
theorem B6939989 : Blo 2281435 6939989 := bbase (se 12 (by rfl) ⟨2541, by rfl⟩ : syracuseStep 6939989 = 5083) (by norm_num)
theorem B4626659 : Blo 2281435 4626659 := bstep (se 1 (by rfl) ⟨3469994, by rfl⟩ : syracuseStep 4626659 = 6939989) B6939989
theorem B12337757 : Blo 2281435 12337757 := bstep (se 3 (by rfl) ⟨2313329, by rfl⟩ : syracuseStep 12337757 = 4626659) B4626659
theorem B8225171 : Blo 2281435 8225171 := bstep (se 1 (by rfl) ⟨6168878, by rfl⟩ : syracuseStep 8225171 = 12337757) B12337757
theorem B5483447 : Blo 2281435 5483447 := bstep (se 1 (by rfl) ⟨4112585, by rfl⟩ : syracuseStep 5483447 = 8225171) B8225171
theorem B3655631 : Blo 2281435 3655631 := bstep (se 1 (by rfl) ⟨2741723, by rfl⟩ : syracuseStep 3655631 = 5483447) B5483447
theorem B9748349 : Blo 2281435 9748349 := bstep (se 3 (by rfl) ⟨1827815, by rfl⟩ : syracuseStep 9748349 = 3655631) B3655631
theorem B6498899 : Blo 2281435 6498899 := bstep (se 1 (by rfl) ⟨4874174, by rfl⟩ : syracuseStep 6498899 = 9748349) B9748349
theorem B4332599 : Blo 2281435 4332599 := bstep (se 1 (by rfl) ⟨3249449, by rfl⟩ : syracuseStep 4332599 = 6498899) B6498899
theorem B2888399 : Blo 2281435 2888399 := bstep (se 1 (by rfl) ⟨2166299, by rfl⟩ : syracuseStep 2888399 = 4332599) B4332599
theorem B7702397 : Blo 2281435 7702397 := bstep (se 3 (by rfl) ⟨1444199, by rfl⟩ : syracuseStep 7702397 = 2888399) B2888399
theorem B5134931 : Blo 2281435 5134931 := bstep (se 1 (by rfl) ⟨3851198, by rfl⟩ : syracuseStep 5134931 = 7702397) B7702397
theorem B3423287 : Blo 2281435 3423287 := bstep (se 1 (by rfl) ⟨2567465, by rfl⟩ : syracuseStep 3423287 = 5134931) B5134931
theorem B2282191 : Blo 2281435 2282191 := bstep (se 1 (by rfl) ⟨1711643, by rfl⟩ : syracuseStep 2282191 = 3423287) B3423287
theorem B3423293 : Blo 2281435 3423293 := bbase (se 3 (by rfl) ⟨641867, by rfl⟩ : syracuseStep 3423293 = 1283735) (by norm_num)
theorem B2282195 : Blo 2281435 2282195 := bstep (se 1 (by rfl) ⟨1711646, by rfl⟩ : syracuseStep 2282195 = 3423293) B3423293
theorem B5134949 : Blo 2281435 5134949 := bbase (se 4 (by rfl) ⟨481401, by rfl⟩ : syracuseStep 5134949 = 962803) (by norm_num)
theorem B3423299 : Blo 2281435 3423299 := bstep (se 1 (by rfl) ⟨2567474, by rfl⟩ : syracuseStep 3423299 = 5134949) B5134949
theorem B2282199 : Blo 2281435 2282199 := bstep (se 1 (by rfl) ⟨1711649, by rfl⟩ : syracuseStep 2282199 = 3423299) B3423299
theorem B5776829 : Blo 2281435 5776829 := bbase (se 3 (by rfl) ⟨1083155, by rfl⟩ : syracuseStep 5776829 = 2166311) (by norm_num)
theorem B3851219 : Blo 2281435 3851219 := bstep (se 1 (by rfl) ⟨2888414, by rfl⟩ : syracuseStep 3851219 = 5776829) B5776829
theorem B2567479 : Blo 2281435 2567479 := bstep (se 1 (by rfl) ⟨1925609, by rfl⟩ : syracuseStep 2567479 = 3851219) B3851219
theorem B3423305 : Blo 2281435 3423305 := bstep (se 2 (by rfl) ⟨1283739, by rfl⟩ : syracuseStep 3423305 = 2567479) B2567479
theorem B2282203 : Blo 2281435 2282203 := bstep (se 1 (by rfl) ⟨1711652, by rfl⟩ : syracuseStep 2282203 = 3423305) B3423305
theorem B4332629 : Blo 2281435 4332629 := bbase (se 8 (by rfl) ⟨25386, by rfl⟩ : syracuseStep 4332629 = 50773) (by norm_num)
theorem B11553677 : Blo 2281435 11553677 := bstep (se 3 (by rfl) ⟨2166314, by rfl⟩ : syracuseStep 11553677 = 4332629) B4332629
theorem B7702451 : Blo 2281435 7702451 := bstep (se 1 (by rfl) ⟨5776838, by rfl⟩ : syracuseStep 7702451 = 11553677) B11553677
theorem B5134967 : Blo 2281435 5134967 := bstep (se 1 (by rfl) ⟨3851225, by rfl⟩ : syracuseStep 5134967 = 7702451) B7702451
theorem B3423311 : Blo 2281435 3423311 := bstep (se 1 (by rfl) ⟨2567483, by rfl⟩ : syracuseStep 3423311 = 5134967) B5134967
theorem B2282207 : Blo 2281435 2282207 := bstep (se 1 (by rfl) ⟨1711655, by rfl⟩ : syracuseStep 2282207 = 3423311) B3423311
theorem B3423317 : Blo 2281435 3423317 := bbase (se 8 (by rfl) ⟨20058, by rfl⟩ : syracuseStep 3423317 = 40117) (by norm_num)
theorem B2282211 : Blo 2281435 2282211 := bstep (se 1 (by rfl) ⟨1711658, by rfl⟩ : syracuseStep 2282211 = 3423317) B3423317
theorem B14622677 : Blo 2281435 14622677 := bbase (se 7 (by rfl) ⟨171359, by rfl⟩ : syracuseStep 14622677 = 342719) (by norm_num)
theorem B9748451 : Blo 2281435 9748451 := bstep (se 1 (by rfl) ⟨7311338, by rfl⟩ : syracuseStep 9748451 = 14622677) B14622677
theorem B6498967 : Blo 2281435 6498967 := bstep (se 1 (by rfl) ⟨4874225, by rfl⟩ : syracuseStep 6498967 = 9748451) B9748451
theorem B8665289 : Blo 2281435 8665289 := bstep (se 2 (by rfl) ⟨3249483, by rfl⟩ : syracuseStep 8665289 = 6498967) B6498967
theorem B5776859 : Blo 2281435 5776859 := bstep (se 1 (by rfl) ⟨4332644, by rfl⟩ : syracuseStep 5776859 = 8665289) B8665289
theorem B3851239 : Blo 2281435 3851239 := bstep (se 1 (by rfl) ⟨2888429, by rfl⟩ : syracuseStep 3851239 = 5776859) B5776859
theorem B5134985 : Blo 2281435 5134985 := bstep (se 2 (by rfl) ⟨1925619, by rfl⟩ : syracuseStep 5134985 = 3851239) B3851239
theorem B3423323 : Blo 2281435 3423323 := bstep (se 1 (by rfl) ⟨2567492, by rfl⟩ : syracuseStep 3423323 = 5134985) B5134985
theorem B2282215 : Blo 2281435 2282215 := bstep (se 1 (by rfl) ⟨1711661, by rfl⟩ : syracuseStep 2282215 = 3423323) B3423323
theorem B2567497 : Blo 2281435 2567497 := bbase (se 2 (by rfl) ⟨962811, by rfl⟩ : syracuseStep 2567497 = 1925623) (by norm_num)
theorem B3423329 : Blo 2281435 3423329 := bstep (se 2 (by rfl) ⟨1283748, by rfl⟩ : syracuseStep 3423329 = 2567497) B2567497
theorem B2282219 : Blo 2281435 2282219 := bstep (se 1 (by rfl) ⟨1711664, by rfl⟩ : syracuseStep 2282219 = 3423329) B3423329
theorem B9253445 : Blo 2281435 9253445 := bbase (se 4 (by rfl) ⟨867510, by rfl⟩ : syracuseStep 9253445 = 1735021) (by norm_num)
theorem B24675853 : Blo 2281435 24675853 := bstep (se 3 (by rfl) ⟨4626722, by rfl⟩ : syracuseStep 24675853 = 9253445) B9253445
theorem B32901137 : Blo 2281435 32901137 := bstep (se 2 (by rfl) ⟨12337926, by rfl⟩ : syracuseStep 32901137 = 24675853) B24675853
theorem B21934091 : Blo 2281435 21934091 := bstep (se 1 (by rfl) ⟨16450568, by rfl⟩ : syracuseStep 21934091 = 32901137) B32901137
theorem B14622727 : Blo 2281435 14622727 := bstep (se 1 (by rfl) ⟨10967045, by rfl⟩ : syracuseStep 14622727 = 21934091) B21934091
theorem B19496969 : Blo 2281435 19496969 := bstep (se 2 (by rfl) ⟨7311363, by rfl⟩ : syracuseStep 19496969 = 14622727) B14622727
theorem B12997979 : Blo 2281435 12997979 := bstep (se 1 (by rfl) ⟨9748484, by rfl⟩ : syracuseStep 12997979 = 19496969) B19496969
theorem B8665319 : Blo 2281435 8665319 := bstep (se 1 (by rfl) ⟨6498989, by rfl⟩ : syracuseStep 8665319 = 12997979) B12997979
theorem B5776879 : Blo 2281435 5776879 := bstep (se 1 (by rfl) ⟨4332659, by rfl⟩ : syracuseStep 5776879 = 8665319) B8665319
theorem B7702505 : Blo 2281435 7702505 := bstep (se 2 (by rfl) ⟨2888439, by rfl⟩ : syracuseStep 7702505 = 5776879) B5776879
theorem B5135003 : Blo 2281435 5135003 := bstep (se 1 (by rfl) ⟨3851252, by rfl⟩ : syracuseStep 5135003 = 7702505) B7702505
theorem B3423335 : Blo 2281435 3423335 := bstep (se 1 (by rfl) ⟨2567501, by rfl⟩ : syracuseStep 3423335 = 5135003) B5135003
theorem B2282223 : Blo 2281435 2282223 := bstep (se 1 (by rfl) ⟨1711667, by rfl⟩ : syracuseStep 2282223 = 3423335) B3423335
theorem B3423341 : Blo 2281435 3423341 := bbase (se 3 (by rfl) ⟨641876, by rfl⟩ : syracuseStep 3423341 = 1283753) (by norm_num)
theorem B2282227 : Blo 2281435 2282227 := bstep (se 1 (by rfl) ⟨1711670, by rfl⟩ : syracuseStep 2282227 = 3423341) B3423341
theorem B5135021 : Blo 2281435 5135021 := bbase (se 3 (by rfl) ⟨962816, by rfl⟩ : syracuseStep 5135021 = 1925633) (by norm_num)
theorem B3423347 : Blo 2281435 3423347 := bstep (se 1 (by rfl) ⟨2567510, by rfl⟩ : syracuseStep 3423347 = 5135021) B5135021
theorem B2282231 : Blo 2281435 2282231 := bstep (se 1 (by rfl) ⟨1711673, by rfl⟩ : syracuseStep 2282231 = 3423347) B3423347
theorem B4874269 : Blo 2281435 4874269 := bbase (se 3 (by rfl) ⟨913925, by rfl⟩ : syracuseStep 4874269 = 1827851) (by norm_num)
theorem B6499025 : Blo 2281435 6499025 := bstep (se 2 (by rfl) ⟨2437134, by rfl⟩ : syracuseStep 6499025 = 4874269) B4874269
theorem B4332683 : Blo 2281435 4332683 := bstep (se 1 (by rfl) ⟨3249512, by rfl⟩ : syracuseStep 4332683 = 6499025) B6499025
theorem B2888455 : Blo 2281435 2888455 := bstep (se 1 (by rfl) ⟨2166341, by rfl⟩ : syracuseStep 2888455 = 4332683) B4332683
theorem B3851273 : Blo 2281435 3851273 := bstep (se 2 (by rfl) ⟨1444227, by rfl⟩ : syracuseStep 3851273 = 2888455) B2888455
theorem B2567515 : Blo 2281435 2567515 := bstep (se 1 (by rfl) ⟨1925636, by rfl⟩ : syracuseStep 2567515 = 3851273) B3851273
theorem B3423353 : Blo 2281435 3423353 := bstep (se 2 (by rfl) ⟨1283757, by rfl⟩ : syracuseStep 3423353 = 2567515) B2567515
theorem B2282235 : Blo 2281435 2282235 := bstep (se 1 (by rfl) ⟨1711676, by rfl⟩ : syracuseStep 2282235 = 3423353) B3423353
theorem B6940133 : Blo 2281435 6940133 := bbase (se 4 (by rfl) ⟨650637, by rfl⟩ : syracuseStep 6940133 = 1301275) (by norm_num)
theorem B4626755 : Blo 2281435 4626755 := bstep (se 1 (by rfl) ⟨3470066, by rfl⟩ : syracuseStep 4626755 = 6940133) B6940133
theorem B3084503 : Blo 2281435 3084503 := bstep (se 1 (by rfl) ⟨2313377, by rfl⟩ : syracuseStep 3084503 = 4626755) B4626755
theorem B32901365 : Blo 2281435 32901365 := bstep (se 5 (by rfl) ⟨1542251, by rfl⟩ : syracuseStep 32901365 = 3084503) B3084503
theorem B21934243 : Blo 2281435 21934243 := bstep (se 1 (by rfl) ⟨16450682, by rfl⟩ : syracuseStep 21934243 = 32901365) B32901365
theorem B29245657 : Blo 2281435 29245657 := bstep (se 2 (by rfl) ⟨10967121, by rfl⟩ : syracuseStep 29245657 = 21934243) B21934243
theorem B38994209 : Blo 2281435 38994209 := bstep (se 2 (by rfl) ⟨14622828, by rfl⟩ : syracuseStep 38994209 = 29245657) B29245657
theorem B25996139 : Blo 2281435 25996139 := bstep (se 1 (by rfl) ⟨19497104, by rfl⟩ : syracuseStep 25996139 = 38994209) B38994209
theorem B17330759 : Blo 2281435 17330759 := bstep (se 1 (by rfl) ⟨12998069, by rfl⟩ : syracuseStep 17330759 = 25996139) B25996139
theorem B11553839 : Blo 2281435 11553839 := bstep (se 1 (by rfl) ⟨8665379, by rfl⟩ : syracuseStep 11553839 = 17330759) B17330759
theorem B7702559 : Blo 2281435 7702559 := bstep (se 1 (by rfl) ⟨5776919, by rfl⟩ : syracuseStep 7702559 = 11553839) B11553839
theorem B5135039 : Blo 2281435 5135039 := bstep (se 1 (by rfl) ⟨3851279, by rfl⟩ : syracuseStep 5135039 = 7702559) B7702559
theorem B3423359 : Blo 2281435 3423359 := bstep (se 1 (by rfl) ⟨2567519, by rfl⟩ : syracuseStep 3423359 = 5135039) B5135039
theorem B2282239 : Blo 2281435 2282239 := bstep (se 1 (by rfl) ⟨1711679, by rfl⟩ : syracuseStep 2282239 = 3423359) B3423359
theorem B3423365 : Blo 2281435 3423365 := bbase (se 4 (by rfl) ⟨320940, by rfl⟩ : syracuseStep 3423365 = 641881) (by norm_num)
theorem B2282243 : Blo 2281435 2282243 := bstep (se 1 (by rfl) ⟨1711682, by rfl⟩ : syracuseStep 2282243 = 3423365) B3423365
theorem B3851293 : Blo 2281435 3851293 := bbase (se 3 (by rfl) ⟨722117, by rfl⟩ : syracuseStep 3851293 = 1444235) (by norm_num)
theorem B5135057 : Blo 2281435 5135057 := bstep (se 2 (by rfl) ⟨1925646, by rfl⟩ : syracuseStep 5135057 = 3851293) B3851293
theorem B3423371 : Blo 2281435 3423371 := bstep (se 1 (by rfl) ⟨2567528, by rfl⟩ : syracuseStep 3423371 = 5135057) B5135057
theorem B2282247 : Blo 2281435 2282247 := bstep (se 1 (by rfl) ⟨1711685, by rfl⟩ : syracuseStep 2282247 = 3423371) B3423371
theorem B2567533 : Blo 2281435 2567533 := bbase (se 3 (by rfl) ⟨481412, by rfl⟩ : syracuseStep 2567533 = 962825) (by norm_num)
theorem B3423377 : Blo 2281435 3423377 := bstep (se 2 (by rfl) ⟨1283766, by rfl⟩ : syracuseStep 3423377 = 2567533) B2567533
theorem B2282251 : Blo 2281435 2282251 := bstep (se 1 (by rfl) ⟨1711688, by rfl⟩ : syracuseStep 2282251 = 3423377) B3423377
theorem B7702613 : Blo 2281435 7702613 := bbase (se 8 (by rfl) ⟨45132, by rfl⟩ : syracuseStep 7702613 = 90265) (by norm_num)
theorem B5135075 : Blo 2281435 5135075 := bstep (se 1 (by rfl) ⟨3851306, by rfl⟩ : syracuseStep 5135075 = 7702613) B7702613
theorem B3423383 : Blo 2281435 3423383 := bstep (se 1 (by rfl) ⟨2567537, by rfl⟩ : syracuseStep 3423383 = 5135075) B5135075
theorem B2282255 : Blo 2281435 2282255 := bstep (se 1 (by rfl) ⟨1711691, by rfl⟩ : syracuseStep 2282255 = 3423383) B3423383
theorem B3423389 : Blo 2281435 3423389 := bbase (se 3 (by rfl) ⟨641885, by rfl⟩ : syracuseStep 3423389 = 1283771) (by norm_num)
theorem B2282259 : Blo 2281435 2282259 := bstep (se 1 (by rfl) ⟨1711694, by rfl⟩ : syracuseStep 2282259 = 3423389) B3423389
theorem B5135093 : Blo 2281435 5135093 := bbase (se 5 (by rfl) ⟨240707, by rfl⟩ : syracuseStep 5135093 = 481415) (by norm_num)
theorem B3423395 : Blo 2281435 3423395 := bstep (se 1 (by rfl) ⟨2567546, by rfl⟩ : syracuseStep 3423395 = 5135093) B5135093
theorem B2282263 : Blo 2281435 2282263 := bstep (se 1 (by rfl) ⟨1711697, by rfl⟩ : syracuseStep 2282263 = 3423395) B3423395
theorem B5483629 : Blo 2281435 5483629 := bbase (se 3 (by rfl) ⟨1028180, by rfl⟩ : syracuseStep 5483629 = 2056361) (by norm_num)
theorem B29246021 : Blo 2281435 29246021 := bstep (se 4 (by rfl) ⟨2741814, by rfl⟩ : syracuseStep 29246021 = 5483629) B5483629
theorem B19497347 : Blo 2281435 19497347 := bstep (se 1 (by rfl) ⟨14623010, by rfl⟩ : syracuseStep 19497347 = 29246021) B29246021
theorem B12998231 : Blo 2281435 12998231 := bstep (se 1 (by rfl) ⟨9748673, by rfl⟩ : syracuseStep 12998231 = 19497347) B19497347
theorem B8665487 : Blo 2281435 8665487 := bstep (se 1 (by rfl) ⟨6499115, by rfl⟩ : syracuseStep 8665487 = 12998231) B12998231
theorem B5776991 : Blo 2281435 5776991 := bstep (se 1 (by rfl) ⟨4332743, by rfl⟩ : syracuseStep 5776991 = 8665487) B8665487
theorem B3851327 : Blo 2281435 3851327 := bstep (se 1 (by rfl) ⟨2888495, by rfl⟩ : syracuseStep 3851327 = 5776991) B5776991
theorem B2567551 : Blo 2281435 2567551 := bstep (se 1 (by rfl) ⟨1925663, by rfl⟩ : syracuseStep 2567551 = 3851327) B3851327
theorem B3423401 : Blo 2281435 3423401 := bstep (se 2 (by rfl) ⟨1283775, by rfl⟩ : syracuseStep 3423401 = 2567551) B2567551
theorem B2282267 : Blo 2281435 2282267 := bstep (se 1 (by rfl) ⟨1711700, by rfl⟩ : syracuseStep 2282267 = 3423401) B3423401
theorem B4626821 : Blo 2281435 4626821 := bbase (se 4 (by rfl) ⟨433764, by rfl⟩ : syracuseStep 4626821 = 867529) (by norm_num)
theorem B12338189 : Blo 2281435 12338189 := bstep (se 3 (by rfl) ⟨2313410, by rfl⟩ : syracuseStep 12338189 = 4626821) B4626821
theorem B8225459 : Blo 2281435 8225459 := bstep (se 1 (by rfl) ⟨6169094, by rfl⟩ : syracuseStep 8225459 = 12338189) B12338189
theorem B5483639 : Blo 2281435 5483639 := bstep (se 1 (by rfl) ⟨4112729, by rfl⟩ : syracuseStep 5483639 = 8225459) B8225459
theorem B3655759 : Blo 2281435 3655759 := bstep (se 1 (by rfl) ⟨2741819, by rfl⟩ : syracuseStep 3655759 = 5483639) B5483639
theorem B4874345 : Blo 2281435 4874345 := bstep (se 2 (by rfl) ⟨1827879, by rfl⟩ : syracuseStep 4874345 = 3655759) B3655759
theorem B3249563 : Blo 2281435 3249563 := bstep (se 1 (by rfl) ⟨2437172, by rfl⟩ : syracuseStep 3249563 = 4874345) B4874345
theorem B8665501 : Blo 2281435 8665501 := bstep (se 3 (by rfl) ⟨1624781, by rfl⟩ : syracuseStep 8665501 = 3249563) B3249563
theorem B11554001 : Blo 2281435 11554001 := bstep (se 2 (by rfl) ⟨4332750, by rfl⟩ : syracuseStep 11554001 = 8665501) B8665501
theorem B7702667 : Blo 2281435 7702667 := bstep (se 1 (by rfl) ⟨5777000, by rfl⟩ : syracuseStep 7702667 = 11554001) B11554001
theorem B5135111 : Blo 2281435 5135111 := bstep (se 1 (by rfl) ⟨3851333, by rfl⟩ : syracuseStep 5135111 = 7702667) B7702667
theorem B3423407 : Blo 2281435 3423407 := bstep (se 1 (by rfl) ⟨2567555, by rfl⟩ : syracuseStep 3423407 = 5135111) B5135111
theorem B2282271 : Blo 2281435 2282271 := bstep (se 1 (by rfl) ⟨1711703, by rfl⟩ : syracuseStep 2282271 = 3423407) B3423407
theorem B3423413 : Blo 2281435 3423413 := bbase (se 5 (by rfl) ⟨160472, by rfl⟩ : syracuseStep 3423413 = 320945) (by norm_num)
theorem B2282275 : Blo 2281435 2282275 := bstep (se 1 (by rfl) ⟨1711706, by rfl⟩ : syracuseStep 2282275 = 3423413) B3423413
theorem B5777021 : Blo 2281435 5777021 := bbase (se 3 (by rfl) ⟨1083191, by rfl⟩ : syracuseStep 5777021 = 2166383) (by norm_num)
theorem B3851347 : Blo 2281435 3851347 := bstep (se 1 (by rfl) ⟨2888510, by rfl⟩ : syracuseStep 3851347 = 5777021) B5777021
theorem B5135129 : Blo 2281435 5135129 := bstep (se 2 (by rfl) ⟨1925673, by rfl⟩ : syracuseStep 5135129 = 3851347) B3851347
theorem B3423419 : Blo 2281435 3423419 := bstep (se 1 (by rfl) ⟨2567564, by rfl⟩ : syracuseStep 3423419 = 5135129) B5135129
theorem B2282279 : Blo 2281435 2282279 := bstep (se 1 (by rfl) ⟨1711709, by rfl⟩ : syracuseStep 2282279 = 3423419) B3423419
theorem B2567569 : Blo 2281435 2567569 := bbase (se 2 (by rfl) ⟨962838, by rfl⟩ : syracuseStep 2567569 = 1925677) (by norm_num)
theorem B3423425 : Blo 2281435 3423425 := bstep (se 2 (by rfl) ⟨1283784, by rfl⟩ : syracuseStep 3423425 = 2567569) B2567569
theorem B2282283 : Blo 2281435 2282283 := bstep (se 1 (by rfl) ⟨1711712, by rfl⟩ : syracuseStep 2282283 = 3423425) B3423425
theorem B4332781 : Blo 2281435 4332781 := bbase (se 3 (by rfl) ⟨812396, by rfl⟩ : syracuseStep 4332781 = 1624793) (by norm_num)
theorem B5777041 : Blo 2281435 5777041 := bstep (se 2 (by rfl) ⟨2166390, by rfl⟩ : syracuseStep 5777041 = 4332781) B4332781
theorem B7702721 : Blo 2281435 7702721 := bstep (se 2 (by rfl) ⟨2888520, by rfl⟩ : syracuseStep 7702721 = 5777041) B5777041
theorem B5135147 : Blo 2281435 5135147 := bstep (se 1 (by rfl) ⟨3851360, by rfl⟩ : syracuseStep 5135147 = 7702721) B7702721
theorem B3423431 : Blo 2281435 3423431 := bstep (se 1 (by rfl) ⟨2567573, by rfl⟩ : syracuseStep 3423431 = 5135147) B5135147
theorem B2282287 : Blo 2281435 2282287 := bstep (se 1 (by rfl) ⟨1711715, by rfl⟩ : syracuseStep 2282287 = 3423431) B3423431
theorem B3423437 : Blo 2281435 3423437 := bbase (se 3 (by rfl) ⟨641894, by rfl⟩ : syracuseStep 3423437 = 1283789) (by norm_num)
theorem B2282291 : Blo 2281435 2282291 := bstep (se 1 (by rfl) ⟨1711718, by rfl⟩ : syracuseStep 2282291 = 3423437) B3423437
theorem B5135165 : Blo 2281435 5135165 := bbase (se 3 (by rfl) ⟨962843, by rfl⟩ : syracuseStep 5135165 = 1925687) (by norm_num)
theorem B3423443 : Blo 2281435 3423443 := bstep (se 1 (by rfl) ⟨2567582, by rfl⟩ : syracuseStep 3423443 = 5135165) B5135165
theorem B2282295 : Blo 2281435 2282295 := bstep (se 1 (by rfl) ⟨1711721, by rfl⟩ : syracuseStep 2282295 = 3423443) B3423443
theorem B3851381 : Blo 2281435 3851381 := bbase (se 5 (by rfl) ⟨180533, by rfl⟩ : syracuseStep 3851381 = 361067) (by norm_num)
theorem B2567587 : Blo 2281435 2567587 := bstep (se 1 (by rfl) ⟨1925690, by rfl⟩ : syracuseStep 2567587 = 3851381) B3851381
theorem B3423449 : Blo 2281435 3423449 := bstep (se 2 (by rfl) ⟨1283793, by rfl⟩ : syracuseStep 3423449 = 2567587) B2567587
theorem B2282299 : Blo 2281435 2282299 := bstep (se 1 (by rfl) ⟨1711724, by rfl⟩ : syracuseStep 2282299 = 3423449) B3423449
theorem B4874413 : Blo 2281435 4874413 := bbase (se 3 (by rfl) ⟨913952, by rfl⟩ : syracuseStep 4874413 = 1827905) (by norm_num)
theorem B6499217 : Blo 2281435 6499217 := bstep (se 2 (by rfl) ⟨2437206, by rfl⟩ : syracuseStep 6499217 = 4874413) B4874413
theorem B17331245 : Blo 2281435 17331245 := bstep (se 3 (by rfl) ⟨3249608, by rfl⟩ : syracuseStep 17331245 = 6499217) B6499217
theorem B11554163 : Blo 2281435 11554163 := bstep (se 1 (by rfl) ⟨8665622, by rfl⟩ : syracuseStep 11554163 = 17331245) B17331245
theorem B7702775 : Blo 2281435 7702775 := bstep (se 1 (by rfl) ⟨5777081, by rfl⟩ : syracuseStep 7702775 = 11554163) B11554163
theorem B5135183 : Blo 2281435 5135183 := bstep (se 1 (by rfl) ⟨3851387, by rfl⟩ : syracuseStep 5135183 = 7702775) B7702775
theorem B3423455 : Blo 2281435 3423455 := bstep (se 1 (by rfl) ⟨2567591, by rfl⟩ : syracuseStep 3423455 = 5135183) B5135183
theorem B2282303 : Blo 2281435 2282303 := bstep (se 1 (by rfl) ⟨1711727, by rfl⟩ : syracuseStep 2282303 = 3423455) B3423455
theorem B3423461 : Blo 2281435 3423461 := bbase (se 4 (by rfl) ⟨320949, by rfl⟩ : syracuseStep 3423461 = 641899) (by norm_num)
theorem B2282307 : Blo 2281435 2282307 := bstep (se 1 (by rfl) ⟨1711730, by rfl⟩ : syracuseStep 2282307 = 3423461) B3423461
theorem B3903949 : Blo 2281435 3903949 := bbase (se 3 (by rfl) ⟨731990, by rfl⟩ : syracuseStep 3903949 = 1463981) (by norm_num)
theorem B5205265 : Blo 2281435 5205265 := bstep (se 2 (by rfl) ⟨1951974, by rfl⟩ : syracuseStep 5205265 = 3903949) B3903949
theorem B27761413 : Blo 2281435 27761413 := bstep (se 4 (by rfl) ⟨2602632, by rfl⟩ : syracuseStep 27761413 = 5205265) B5205265
theorem B37015217 : Blo 2281435 37015217 := bstep (se 2 (by rfl) ⟨13880706, by rfl⟩ : syracuseStep 37015217 = 27761413) B27761413
theorem B24676811 : Blo 2281435 24676811 := bstep (se 1 (by rfl) ⟨18507608, by rfl⟩ : syracuseStep 24676811 = 37015217) B37015217
theorem B16451207 : Blo 2281435 16451207 := bstep (se 1 (by rfl) ⟨12338405, by rfl⟩ : syracuseStep 16451207 = 24676811) B24676811
theorem B10967471 : Blo 2281435 10967471 := bstep (se 1 (by rfl) ⟨8225603, by rfl⟩ : syracuseStep 10967471 = 16451207) B16451207
theorem B7311647 : Blo 2281435 7311647 := bstep (se 1 (by rfl) ⟨5483735, by rfl⟩ : syracuseStep 7311647 = 10967471) B10967471
theorem B4874431 : Blo 2281435 4874431 := bstep (se 1 (by rfl) ⟨3655823, by rfl⟩ : syracuseStep 4874431 = 7311647) B7311647
theorem B6499241 : Blo 2281435 6499241 := bstep (se 2 (by rfl) ⟨2437215, by rfl⟩ : syracuseStep 6499241 = 4874431) B4874431
theorem B4332827 : Blo 2281435 4332827 := bstep (se 1 (by rfl) ⟨3249620, by rfl⟩ : syracuseStep 4332827 = 6499241) B6499241
theorem B2888551 : Blo 2281435 2888551 := bstep (se 1 (by rfl) ⟨2166413, by rfl⟩ : syracuseStep 2888551 = 4332827) B4332827
theorem B3851401 : Blo 2281435 3851401 := bstep (se 2 (by rfl) ⟨1444275, by rfl⟩ : syracuseStep 3851401 = 2888551) B2888551
theorem B5135201 : Blo 2281435 5135201 := bstep (se 2 (by rfl) ⟨1925700, by rfl⟩ : syracuseStep 5135201 = 3851401) B3851401
theorem B3423467 : Blo 2281435 3423467 := bstep (se 1 (by rfl) ⟨2567600, by rfl⟩ : syracuseStep 3423467 = 5135201) B5135201
theorem B2282311 : Blo 2281435 2282311 := bstep (se 1 (by rfl) ⟨1711733, by rfl⟩ : syracuseStep 2282311 = 3423467) B3423467
theorem B2567605 : Blo 2281435 2567605 := bbase (se 5 (by rfl) ⟨120356, by rfl⟩ : syracuseStep 2567605 = 240713) (by norm_num)
theorem B3423473 : Blo 2281435 3423473 := bstep (se 2 (by rfl) ⟨1283802, by rfl⟩ : syracuseStep 3423473 = 2567605) B2567605
theorem B2282315 : Blo 2281435 2282315 := bstep (se 1 (by rfl) ⟨1711736, by rfl⟩ : syracuseStep 2282315 = 3423473) B3423473
theorem B2888561 : Blo 2281435 2888561 := bbase (se 2 (by rfl) ⟨1083210, by rfl⟩ : syracuseStep 2888561 = 2166421) (by norm_num)
theorem B7702829 : Blo 2281435 7702829 := bstep (se 3 (by rfl) ⟨1444280, by rfl⟩ : syracuseStep 7702829 = 2888561) B2888561
theorem B5135219 : Blo 2281435 5135219 := bstep (se 1 (by rfl) ⟨3851414, by rfl⟩ : syracuseStep 5135219 = 7702829) B7702829
theorem B3423479 : Blo 2281435 3423479 := bstep (se 1 (by rfl) ⟨2567609, by rfl⟩ : syracuseStep 3423479 = 5135219) B5135219
theorem B2282319 : Blo 2281435 2282319 := bstep (se 1 (by rfl) ⟨1711739, by rfl⟩ : syracuseStep 2282319 = 3423479) B3423479
theorem B3423485 : Blo 2281435 3423485 := bbase (se 3 (by rfl) ⟨641903, by rfl⟩ : syracuseStep 3423485 = 1283807) (by norm_num)
theorem B2282323 : Blo 2281435 2282323 := bstep (se 1 (by rfl) ⟨1711742, by rfl⟩ : syracuseStep 2282323 = 3423485) B3423485
theorem B5135237 : Blo 2281435 5135237 := bbase (se 4 (by rfl) ⟨481428, by rfl⟩ : syracuseStep 5135237 = 962857) (by norm_num)
theorem B3423491 : Blo 2281435 3423491 := bstep (se 1 (by rfl) ⟨2567618, by rfl⟩ : syracuseStep 3423491 = 5135237) B5135237
theorem B2282327 : Blo 2281435 2282327 := bstep (se 1 (by rfl) ⟨1711745, by rfl⟩ : syracuseStep 2282327 = 3423491) B3423491
theorem B2437237 : Blo 2281435 2437237 := bbase (se 5 (by rfl) ⟨114245, by rfl⟩ : syracuseStep 2437237 = 228491) (by norm_num)
theorem B3249649 : Blo 2281435 3249649 := bstep (se 2 (by rfl) ⟨1218618, by rfl⟩ : syracuseStep 3249649 = 2437237) B2437237
theorem B4332865 : Blo 2281435 4332865 := bstep (se 2 (by rfl) ⟨1624824, by rfl⟩ : syracuseStep 4332865 = 3249649) B3249649
theorem B5777153 : Blo 2281435 5777153 := bstep (se 2 (by rfl) ⟨2166432, by rfl⟩ : syracuseStep 5777153 = 4332865) B4332865
theorem B3851435 : Blo 2281435 3851435 := bstep (se 1 (by rfl) ⟨2888576, by rfl⟩ : syracuseStep 3851435 = 5777153) B5777153
theorem B2567623 : Blo 2281435 2567623 := bstep (se 1 (by rfl) ⟨1925717, by rfl⟩ : syracuseStep 2567623 = 3851435) B3851435
theorem B3423497 : Blo 2281435 3423497 := bstep (se 2 (by rfl) ⟨1283811, by rfl⟩ : syracuseStep 3423497 = 2567623) B2567623
theorem B2282331 : Blo 2281435 2282331 := bstep (se 1 (by rfl) ⟨1711748, by rfl⟩ : syracuseStep 2282331 = 3423497) B3423497
theorem B11554325 : Blo 2281435 11554325 := bbase (se 6 (by rfl) ⟨270804, by rfl⟩ : syracuseStep 11554325 = 541609) (by norm_num)
theorem B7702883 : Blo 2281435 7702883 := bstep (se 1 (by rfl) ⟨5777162, by rfl⟩ : syracuseStep 7702883 = 11554325) B11554325
theorem B5135255 : Blo 2281435 5135255 := bstep (se 1 (by rfl) ⟨3851441, by rfl⟩ : syracuseStep 5135255 = 7702883) B7702883
theorem B3423503 : Blo 2281435 3423503 := bstep (se 1 (by rfl) ⟨2567627, by rfl⟩ : syracuseStep 3423503 = 5135255) B5135255
theorem B2282335 : Blo 2281435 2282335 := bstep (se 1 (by rfl) ⟨1711751, by rfl⟩ : syracuseStep 2282335 = 3423503) B3423503
theorem B3423509 : Blo 2281435 3423509 := bbase (se 6 (by rfl) ⟨80238, by rfl⟩ : syracuseStep 3423509 = 160477) (by norm_num)
theorem B2282339 : Blo 2281435 2282339 := bstep (se 1 (by rfl) ⟨1711754, by rfl⟩ : syracuseStep 2282339 = 3423509) B3423509
theorem B8225717 : Blo 2281435 8225717 := bbase (se 5 (by rfl) ⟨385580, by rfl⟩ : syracuseStep 8225717 = 771161) (by norm_num)
theorem B21935245 : Blo 2281435 21935245 := bstep (se 3 (by rfl) ⟨4112858, by rfl⟩ : syracuseStep 21935245 = 8225717) B8225717
theorem B29246993 : Blo 2281435 29246993 := bstep (se 2 (by rfl) ⟨10967622, by rfl⟩ : syracuseStep 29246993 = 21935245) B21935245
theorem B19497995 : Blo 2281435 19497995 := bstep (se 1 (by rfl) ⟨14623496, by rfl⟩ : syracuseStep 19497995 = 29246993) B29246993
theorem B12998663 : Blo 2281435 12998663 := bstep (se 1 (by rfl) ⟨9748997, by rfl⟩ : syracuseStep 12998663 = 19497995) B19497995
theorem B8665775 : Blo 2281435 8665775 := bstep (se 1 (by rfl) ⟨6499331, by rfl⟩ : syracuseStep 8665775 = 12998663) B12998663
theorem B5777183 : Blo 2281435 5777183 := bstep (se 1 (by rfl) ⟨4332887, by rfl⟩ : syracuseStep 5777183 = 8665775) B8665775
theorem B3851455 : Blo 2281435 3851455 := bstep (se 1 (by rfl) ⟨2888591, by rfl⟩ : syracuseStep 3851455 = 5777183) B5777183
theorem B5135273 : Blo 2281435 5135273 := bstep (se 2 (by rfl) ⟨1925727, by rfl⟩ : syracuseStep 5135273 = 3851455) B3851455
theorem B3423515 : Blo 2281435 3423515 := bstep (se 1 (by rfl) ⟨2567636, by rfl⟩ : syracuseStep 3423515 = 5135273) B5135273
theorem B2282343 : Blo 2281435 2282343 := bstep (se 1 (by rfl) ⟨1711757, by rfl⟩ : syracuseStep 2282343 = 3423515) B3423515
theorem B2567641 : Blo 2281435 2567641 := bbase (se 2 (by rfl) ⟨962865, by rfl⟩ : syracuseStep 2567641 = 1925731) (by norm_num)
theorem B3423521 : Blo 2281435 3423521 := bstep (se 2 (by rfl) ⟨1283820, by rfl⟩ : syracuseStep 3423521 = 2567641) B2567641
theorem B2282347 : Blo 2281435 2282347 := bstep (se 1 (by rfl) ⟨1711760, by rfl⟩ : syracuseStep 2282347 = 3423521) B3423521
theorem B3249677 : Blo 2281435 3249677 := bbase (se 3 (by rfl) ⟨609314, by rfl⟩ : syracuseStep 3249677 = 1218629) (by norm_num)
theorem B8665805 : Blo 2281435 8665805 := bstep (se 3 (by rfl) ⟨1624838, by rfl⟩ : syracuseStep 8665805 = 3249677) B3249677
theorem B5777203 : Blo 2281435 5777203 := bstep (se 1 (by rfl) ⟨4332902, by rfl⟩ : syracuseStep 5777203 = 8665805) B8665805
theorem B7702937 : Blo 2281435 7702937 := bstep (se 2 (by rfl) ⟨2888601, by rfl⟩ : syracuseStep 7702937 = 5777203) B5777203
theorem B5135291 : Blo 2281435 5135291 := bstep (se 1 (by rfl) ⟨3851468, by rfl⟩ : syracuseStep 5135291 = 7702937) B7702937
theorem B3423527 : Blo 2281435 3423527 := bstep (se 1 (by rfl) ⟨2567645, by rfl⟩ : syracuseStep 3423527 = 5135291) B5135291
theorem B2282351 : Blo 2281435 2282351 := bstep (se 1 (by rfl) ⟨1711763, by rfl⟩ : syracuseStep 2282351 = 3423527) B3423527
theorem B3423533 : Blo 2281435 3423533 := bbase (se 3 (by rfl) ⟨641912, by rfl⟩ : syracuseStep 3423533 = 1283825) (by norm_num)
theorem B2282355 : Blo 2281435 2282355 := bstep (se 1 (by rfl) ⟨1711766, by rfl⟩ : syracuseStep 2282355 = 3423533) B3423533
theorem B5135309 : Blo 2281435 5135309 := bbase (se 3 (by rfl) ⟨962870, by rfl⟩ : syracuseStep 5135309 = 1925741) (by norm_num)
theorem B3423539 : Blo 2281435 3423539 := bstep (se 1 (by rfl) ⟨2567654, by rfl⟩ : syracuseStep 3423539 = 5135309) B5135309
theorem B2282359 : Blo 2281435 2282359 := bstep (se 1 (by rfl) ⟨1711769, by rfl⟩ : syracuseStep 2282359 = 3423539) B3423539
theorem B2888617 : Blo 2281435 2888617 := bbase (se 2 (by rfl) ⟨1083231, by rfl⟩ : syracuseStep 2888617 = 2166463) (by norm_num)
theorem B3851489 : Blo 2281435 3851489 := bstep (se 2 (by rfl) ⟨1444308, by rfl⟩ : syracuseStep 3851489 = 2888617) B2888617
theorem B2567659 : Blo 2281435 2567659 := bstep (se 1 (by rfl) ⟨1925744, by rfl⟩ : syracuseStep 2567659 = 3851489) B3851489
theorem B3423545 : Blo 2281435 3423545 := bstep (se 2 (by rfl) ⟨1283829, by rfl⟩ : syracuseStep 3423545 = 2567659) B2567659
theorem B2282363 : Blo 2281435 2282363 := bstep (se 1 (by rfl) ⟨1711772, by rfl⟩ : syracuseStep 2282363 = 3423545) B3423545
theorem B3470261 : Blo 2281435 3470261 := bbase (se 5 (by rfl) ⟨162668, by rfl⟩ : syracuseStep 3470261 = 325337) (by norm_num)
theorem B9254029 : Blo 2281435 9254029 := bstep (se 3 (by rfl) ⟨1735130, by rfl⟩ : syracuseStep 9254029 = 3470261) B3470261
theorem B12338705 : Blo 2281435 12338705 := bstep (se 2 (by rfl) ⟨4627014, by rfl⟩ : syracuseStep 12338705 = 9254029) B9254029
theorem B8225803 : Blo 2281435 8225803 := bstep (se 1 (by rfl) ⟨6169352, by rfl⟩ : syracuseStep 8225803 = 12338705) B12338705
theorem B10967737 : Blo 2281435 10967737 := bstep (se 2 (by rfl) ⟨4112901, by rfl⟩ : syracuseStep 10967737 = 8225803) B8225803
theorem B14623649 : Blo 2281435 14623649 := bstep (se 2 (by rfl) ⟨5483868, by rfl⟩ : syracuseStep 14623649 = 10967737) B10967737
theorem B9749099 : Blo 2281435 9749099 := bstep (se 1 (by rfl) ⟨7311824, by rfl⟩ : syracuseStep 9749099 = 14623649) B14623649
theorem B25997597 : Blo 2281435 25997597 := bstep (se 3 (by rfl) ⟨4874549, by rfl⟩ : syracuseStep 25997597 = 9749099) B9749099
theorem B17331731 : Blo 2281435 17331731 := bstep (se 1 (by rfl) ⟨12998798, by rfl⟩ : syracuseStep 17331731 = 25997597) B25997597
theorem B11554487 : Blo 2281435 11554487 := bstep (se 1 (by rfl) ⟨8665865, by rfl⟩ : syracuseStep 11554487 = 17331731) B17331731
theorem B7702991 : Blo 2281435 7702991 := bstep (se 1 (by rfl) ⟨5777243, by rfl⟩ : syracuseStep 7702991 = 11554487) B11554487
theorem B5135327 : Blo 2281435 5135327 := bstep (se 1 (by rfl) ⟨3851495, by rfl⟩ : syracuseStep 5135327 = 7702991) B7702991
theorem B3423551 : Blo 2281435 3423551 := bstep (se 1 (by rfl) ⟨2567663, by rfl⟩ : syracuseStep 3423551 = 5135327) B5135327
theorem B2282367 : Blo 2281435 2282367 := bstep (se 1 (by rfl) ⟨1711775, by rfl⟩ : syracuseStep 2282367 = 3423551) B3423551
theorem B3423557 : Blo 2281435 3423557 := bbase (se 4 (by rfl) ⟨320958, by rfl⟩ : syracuseStep 3423557 = 641917) (by norm_num)
theorem B2282371 : Blo 2281435 2282371 := bstep (se 1 (by rfl) ⟨1711778, by rfl⟩ : syracuseStep 2282371 = 3423557) B3423557
theorem B3851509 : Blo 2281435 3851509 := bbase (se 5 (by rfl) ⟨180539, by rfl⟩ : syracuseStep 3851509 = 361079) (by norm_num)
theorem B5135345 : Blo 2281435 5135345 := bstep (se 2 (by rfl) ⟨1925754, by rfl⟩ : syracuseStep 5135345 = 3851509) B3851509
theorem B3423563 : Blo 2281435 3423563 := bstep (se 1 (by rfl) ⟨2567672, by rfl⟩ : syracuseStep 3423563 = 5135345) B5135345
theorem B2282375 : Blo 2281435 2282375 := bstep (se 1 (by rfl) ⟨1711781, by rfl⟩ : syracuseStep 2282375 = 3423563) B3423563
theorem B2567677 : Blo 2281435 2567677 := bbase (se 3 (by rfl) ⟨481439, by rfl⟩ : syracuseStep 2567677 = 962879) (by norm_num)
theorem B3423569 : Blo 2281435 3423569 := bstep (se 2 (by rfl) ⟨1283838, by rfl⟩ : syracuseStep 3423569 = 2567677) B2567677
theorem B2282379 : Blo 2281435 2282379 := bstep (se 1 (by rfl) ⟨1711784, by rfl⟩ : syracuseStep 2282379 = 3423569) B3423569
theorem B7703045 : Blo 2281435 7703045 := bbase (se 4 (by rfl) ⟨722160, by rfl⟩ : syracuseStep 7703045 = 1444321) (by norm_num)
theorem B5135363 : Blo 2281435 5135363 := bstep (se 1 (by rfl) ⟨3851522, by rfl⟩ : syracuseStep 5135363 = 7703045) B7703045
theorem B3423575 : Blo 2281435 3423575 := bstep (se 1 (by rfl) ⟨2567681, by rfl⟩ : syracuseStep 3423575 = 5135363) B5135363
theorem B2282383 : Blo 2281435 2282383 := bstep (se 1 (by rfl) ⟨1711787, by rfl⟩ : syracuseStep 2282383 = 3423575) B3423575
theorem B3423581 : Blo 2281435 3423581 := bbase (se 3 (by rfl) ⟨641921, by rfl⟩ : syracuseStep 3423581 = 1283843) (by norm_num)
theorem B2282387 : Blo 2281435 2282387 := bstep (se 1 (by rfl) ⟨1711790, by rfl⟩ : syracuseStep 2282387 = 3423581) B3423581
theorem B5135381 : Blo 2281435 5135381 := bbase (se 6 (by rfl) ⟨120360, by rfl⟩ : syracuseStep 5135381 = 240721) (by norm_num)
theorem B3423587 : Blo 2281435 3423587 := bstep (se 1 (by rfl) ⟨2567690, by rfl⟩ : syracuseStep 3423587 = 5135381) B5135381
theorem B2282391 : Blo 2281435 2282391 := bstep (se 1 (by rfl) ⟨1711793, by rfl⟩ : syracuseStep 2282391 = 3423587) B3423587
theorem B8665973 : Blo 2281435 8665973 := bbase (se 5 (by rfl) ⟨406217, by rfl⟩ : syracuseStep 8665973 = 812435) (by norm_num)
theorem B5777315 : Blo 2281435 5777315 := bstep (se 1 (by rfl) ⟨4332986, by rfl⟩ : syracuseStep 5777315 = 8665973) B8665973
theorem B3851543 : Blo 2281435 3851543 := bstep (se 1 (by rfl) ⟨2888657, by rfl⟩ : syracuseStep 3851543 = 5777315) B5777315
theorem B2567695 : Blo 2281435 2567695 := bstep (se 1 (by rfl) ⟨1925771, by rfl⟩ : syracuseStep 2567695 = 3851543) B3851543
theorem B3423593 : Blo 2281435 3423593 := bstep (se 2 (by rfl) ⟨1283847, by rfl⟩ : syracuseStep 3423593 = 2567695) B2567695
theorem B2282395 : Blo 2281435 2282395 := bstep (se 1 (by rfl) ⟨1711796, by rfl⟩ : syracuseStep 2282395 = 3423593) B3423593
theorem B2437309 : Blo 2281435 2437309 := bbase (se 3 (by rfl) ⟨456995, by rfl⟩ : syracuseStep 2437309 = 913991) (by norm_num)
theorem B12998981 : Blo 2281435 12998981 := bstep (se 4 (by rfl) ⟨1218654, by rfl⟩ : syracuseStep 12998981 = 2437309) B2437309
theorem B8665987 : Blo 2281435 8665987 := bstep (se 1 (by rfl) ⟨6499490, by rfl⟩ : syracuseStep 8665987 = 12998981) B12998981
theorem B11554649 : Blo 2281435 11554649 := bstep (se 2 (by rfl) ⟨4332993, by rfl⟩ : syracuseStep 11554649 = 8665987) B8665987
theorem B7703099 : Blo 2281435 7703099 := bstep (se 1 (by rfl) ⟨5777324, by rfl⟩ : syracuseStep 7703099 = 11554649) B11554649
theorem B5135399 : Blo 2281435 5135399 := bstep (se 1 (by rfl) ⟨3851549, by rfl⟩ : syracuseStep 5135399 = 7703099) B7703099
theorem B3423599 : Blo 2281435 3423599 := bstep (se 1 (by rfl) ⟨2567699, by rfl⟩ : syracuseStep 3423599 = 5135399) B5135399
theorem B2282399 : Blo 2281435 2282399 := bstep (se 1 (by rfl) ⟨1711799, by rfl⟩ : syracuseStep 2282399 = 3423599) B3423599
theorem B3423605 : Blo 2281435 3423605 := bbase (se 5 (by rfl) ⟨160481, by rfl⟩ : syracuseStep 3423605 = 320963) (by norm_num)
theorem B2282403 : Blo 2281435 2282403 := bstep (se 1 (by rfl) ⟨1711802, by rfl⟩ : syracuseStep 2282403 = 3423605) B3423605
theorem B3249757 : Blo 2281435 3249757 := bbase (se 3 (by rfl) ⟨609329, by rfl⟩ : syracuseStep 3249757 = 1218659) (by norm_num)
theorem B4333009 : Blo 2281435 4333009 := bstep (se 2 (by rfl) ⟨1624878, by rfl⟩ : syracuseStep 4333009 = 3249757) B3249757
theorem B5777345 : Blo 2281435 5777345 := bstep (se 2 (by rfl) ⟨2166504, by rfl⟩ : syracuseStep 5777345 = 4333009) B4333009
theorem B3851563 : Blo 2281435 3851563 := bstep (se 1 (by rfl) ⟨2888672, by rfl⟩ : syracuseStep 3851563 = 5777345) B5777345
theorem B5135417 : Blo 2281435 5135417 := bstep (se 2 (by rfl) ⟨1925781, by rfl⟩ : syracuseStep 5135417 = 3851563) B3851563
theorem B3423611 : Blo 2281435 3423611 := bstep (se 1 (by rfl) ⟨2567708, by rfl⟩ : syracuseStep 3423611 = 5135417) B5135417
theorem B2282407 : Blo 2281435 2282407 := bstep (se 1 (by rfl) ⟨1711805, by rfl⟩ : syracuseStep 2282407 = 3423611) B3423611
theorem B2567713 : Blo 2281435 2567713 := bbase (se 2 (by rfl) ⟨962892, by rfl⟩ : syracuseStep 2567713 = 1925785) (by norm_num)
theorem B3423617 : Blo 2281435 3423617 := bstep (se 2 (by rfl) ⟨1283856, by rfl⟩ : syracuseStep 3423617 = 2567713) B2567713
theorem B2282411 : Blo 2281435 2282411 := bstep (se 1 (by rfl) ⟨1711808, by rfl⟩ : syracuseStep 2282411 = 3423617) B3423617
theorem B5777365 : Blo 2281435 5777365 := bbase (se 7 (by rfl) ⟨67703, by rfl⟩ : syracuseStep 5777365 = 135407) (by norm_num)
theorem B7703153 : Blo 2281435 7703153 := bstep (se 2 (by rfl) ⟨2888682, by rfl⟩ : syracuseStep 7703153 = 5777365) B5777365
theorem B5135435 : Blo 2281435 5135435 := bstep (se 1 (by rfl) ⟨3851576, by rfl⟩ : syracuseStep 5135435 = 7703153) B7703153
theorem B3423623 : Blo 2281435 3423623 := bstep (se 1 (by rfl) ⟨2567717, by rfl⟩ : syracuseStep 3423623 = 5135435) B5135435
theorem B2282415 : Blo 2281435 2282415 := bstep (se 1 (by rfl) ⟨1711811, by rfl⟩ : syracuseStep 2282415 = 3423623) B3423623
theorem B3423629 : Blo 2281435 3423629 := bbase (se 3 (by rfl) ⟨641930, by rfl⟩ : syracuseStep 3423629 = 1283861) (by norm_num)
theorem B2282419 : Blo 2281435 2282419 := bstep (se 1 (by rfl) ⟨1711814, by rfl⟩ : syracuseStep 2282419 = 3423629) B3423629
theorem B5135453 : Blo 2281435 5135453 := bbase (se 3 (by rfl) ⟨962897, by rfl⟩ : syracuseStep 5135453 = 1925795) (by norm_num)
theorem B3423635 : Blo 2281435 3423635 := bstep (se 1 (by rfl) ⟨2567726, by rfl⟩ : syracuseStep 3423635 = 5135453) B5135453
theorem B2282423 : Blo 2281435 2282423 := bstep (se 1 (by rfl) ⟨1711817, by rfl⟩ : syracuseStep 2282423 = 3423635) B3423635
theorem B3851597 : Blo 2281435 3851597 := bbase (se 3 (by rfl) ⟨722174, by rfl⟩ : syracuseStep 3851597 = 1444349) (by norm_num)
theorem B2567731 : Blo 2281435 2567731 := bstep (se 1 (by rfl) ⟨1925798, by rfl⟩ : syracuseStep 2567731 = 3851597) B3851597
theorem B3423641 : Blo 2281435 3423641 := bstep (se 2 (by rfl) ⟨1283865, by rfl⟩ : syracuseStep 3423641 = 2567731) B2567731
theorem B2282427 : Blo 2281435 2282427 := bstep (se 1 (by rfl) ⟨1711820, by rfl⟩ : syracuseStep 2282427 = 3423641) B3423641
theorem B24678101 : Blo 2281435 24678101 := bbase (se 7 (by rfl) ⟨289196, by rfl⟩ : syracuseStep 24678101 = 578393) (by norm_num)
theorem B16452067 : Blo 2281435 16452067 := bstep (se 1 (by rfl) ⟨12339050, by rfl⟩ : syracuseStep 16452067 = 24678101) B24678101
theorem B21936089 : Blo 2281435 21936089 := bstep (se 2 (by rfl) ⟨8226033, by rfl⟩ : syracuseStep 21936089 = 16452067) B16452067
theorem B14624059 : Blo 2281435 14624059 := bstep (se 1 (by rfl) ⟨10968044, by rfl⟩ : syracuseStep 14624059 = 21936089) B21936089
theorem B19498745 : Blo 2281435 19498745 := bstep (se 2 (by rfl) ⟨7312029, by rfl⟩ : syracuseStep 19498745 = 14624059) B14624059
theorem B12999163 : Blo 2281435 12999163 := bstep (se 1 (by rfl) ⟨9749372, by rfl⟩ : syracuseStep 12999163 = 19498745) B19498745
theorem B17332217 : Blo 2281435 17332217 := bstep (se 2 (by rfl) ⟨6499581, by rfl⟩ : syracuseStep 17332217 = 12999163) B12999163
theorem B11554811 : Blo 2281435 11554811 := bstep (se 1 (by rfl) ⟨8666108, by rfl⟩ : syracuseStep 11554811 = 17332217) B17332217
theorem B7703207 : Blo 2281435 7703207 := bstep (se 1 (by rfl) ⟨5777405, by rfl⟩ : syracuseStep 7703207 = 11554811) B11554811
theorem B5135471 : Blo 2281435 5135471 := bstep (se 1 (by rfl) ⟨3851603, by rfl⟩ : syracuseStep 5135471 = 7703207) B7703207
theorem B3423647 : Blo 2281435 3423647 := bstep (se 1 (by rfl) ⟨2567735, by rfl⟩ : syracuseStep 3423647 = 5135471) B5135471
theorem B2282431 : Blo 2281435 2282431 := bstep (se 1 (by rfl) ⟨1711823, by rfl⟩ : syracuseStep 2282431 = 3423647) B3423647
theorem B3423653 : Blo 2281435 3423653 := bbase (se 4 (by rfl) ⟨320967, by rfl⟩ : syracuseStep 3423653 = 641935) (by norm_num)
theorem B2282435 : Blo 2281435 2282435 := bstep (se 1 (by rfl) ⟨1711826, by rfl⟩ : syracuseStep 2282435 = 3423653) B3423653
theorem B2888713 : Blo 2281435 2888713 := bbase (se 2 (by rfl) ⟨1083267, by rfl⟩ : syracuseStep 2888713 = 2166535) (by norm_num)
theorem B3851617 : Blo 2281435 3851617 := bstep (se 2 (by rfl) ⟨1444356, by rfl⟩ : syracuseStep 3851617 = 2888713) B2888713
theorem B5135489 : Blo 2281435 5135489 := bstep (se 2 (by rfl) ⟨1925808, by rfl⟩ : syracuseStep 5135489 = 3851617) B3851617
theorem B3423659 : Blo 2281435 3423659 := bstep (se 1 (by rfl) ⟨2567744, by rfl⟩ : syracuseStep 3423659 = 5135489) B5135489
theorem B2282439 : Blo 2281435 2282439 := bstep (se 1 (by rfl) ⟨1711829, by rfl⟩ : syracuseStep 2282439 = 3423659) B3423659
theorem B2567749 : Blo 2281435 2567749 := bbase (se 4 (by rfl) ⟨240726, by rfl⟩ : syracuseStep 2567749 = 481453) (by norm_num)
theorem B3423665 : Blo 2281435 3423665 := bstep (se 2 (by rfl) ⟨1283874, by rfl⟩ : syracuseStep 3423665 = 2567749) B2567749
theorem B2282443 : Blo 2281435 2282443 := bstep (se 1 (by rfl) ⟨1711832, by rfl⟩ : syracuseStep 2282443 = 3423665) B3423665
theorem B4333085 : Blo 2281435 4333085 := bbase (se 3 (by rfl) ⟨812453, by rfl⟩ : syracuseStep 4333085 = 1624907) (by norm_num)
theorem B2888723 : Blo 2281435 2888723 := bstep (se 1 (by rfl) ⟨2166542, by rfl⟩ : syracuseStep 2888723 = 4333085) B4333085
theorem B7703261 : Blo 2281435 7703261 := bstep (se 3 (by rfl) ⟨1444361, by rfl⟩ : syracuseStep 7703261 = 2888723) B2888723
theorem B5135507 : Blo 2281435 5135507 := bstep (se 1 (by rfl) ⟨3851630, by rfl⟩ : syracuseStep 5135507 = 7703261) B7703261
theorem B3423671 : Blo 2281435 3423671 := bstep (se 1 (by rfl) ⟨2567753, by rfl⟩ : syracuseStep 3423671 = 5135507) B5135507
theorem B2282447 : Blo 2281435 2282447 := bstep (se 1 (by rfl) ⟨1711835, by rfl⟩ : syracuseStep 2282447 = 3423671) B3423671
theorem B3423677 : Blo 2281435 3423677 := bbase (se 3 (by rfl) ⟨641939, by rfl⟩ : syracuseStep 3423677 = 1283879) (by norm_num)
theorem B2282451 : Blo 2281435 2282451 := bstep (se 1 (by rfl) ⟨1711838, by rfl⟩ : syracuseStep 2282451 = 3423677) B3423677
theorem B5135525 : Blo 2281435 5135525 := bbase (se 4 (by rfl) ⟨481455, by rfl⟩ : syracuseStep 5135525 = 962911) (by norm_num)
theorem B3423683 : Blo 2281435 3423683 := bstep (se 1 (by rfl) ⟨2567762, by rfl⟩ : syracuseStep 3423683 = 5135525) B5135525
theorem B2282455 : Blo 2281435 2282455 := bstep (se 1 (by rfl) ⟨1711841, by rfl⟩ : syracuseStep 2282455 = 3423683) B3423683
theorem B5777477 : Blo 2281435 5777477 := bbase (se 4 (by rfl) ⟨541638, by rfl⟩ : syracuseStep 5777477 = 1083277) (by norm_num)
theorem B3851651 : Blo 2281435 3851651 := bstep (se 1 (by rfl) ⟨2888738, by rfl⟩ : syracuseStep 3851651 = 5777477) B5777477
theorem B2567767 : Blo 2281435 2567767 := bstep (se 1 (by rfl) ⟨1925825, by rfl⟩ : syracuseStep 2567767 = 3851651) B3851651
theorem B3423689 : Blo 2281435 3423689 := bstep (se 2 (by rfl) ⟨1283883, by rfl⟩ : syracuseStep 3423689 = 2567767) B2567767
theorem B2282459 : Blo 2281435 2282459 := bstep (se 1 (by rfl) ⟨1711844, by rfl⟩ : syracuseStep 2282459 = 3423689) B3423689
theorem B7312133 : Blo 2281435 7312133 := bbase (se 4 (by rfl) ⟨685512, by rfl⟩ : syracuseStep 7312133 = 1371025) (by norm_num)
theorem B4874755 : Blo 2281435 4874755 := bstep (se 1 (by rfl) ⟨3656066, by rfl⟩ : syracuseStep 4874755 = 7312133) B7312133
theorem B6499673 : Blo 2281435 6499673 := bstep (se 2 (by rfl) ⟨2437377, by rfl⟩ : syracuseStep 6499673 = 4874755) B4874755
theorem B4333115 : Blo 2281435 4333115 := bstep (se 1 (by rfl) ⟨3249836, by rfl⟩ : syracuseStep 4333115 = 6499673) B6499673
theorem B11554973 : Blo 2281435 11554973 := bstep (se 3 (by rfl) ⟨2166557, by rfl⟩ : syracuseStep 11554973 = 4333115) B4333115
theorem B7703315 : Blo 2281435 7703315 := bstep (se 1 (by rfl) ⟨5777486, by rfl⟩ : syracuseStep 7703315 = 11554973) B11554973
theorem B5135543 : Blo 2281435 5135543 := bstep (se 1 (by rfl) ⟨3851657, by rfl⟩ : syracuseStep 5135543 = 7703315) B7703315
theorem B3423695 : Blo 2281435 3423695 := bstep (se 1 (by rfl) ⟨2567771, by rfl⟩ : syracuseStep 3423695 = 5135543) B5135543
theorem B2282463 : Blo 2281435 2282463 := bstep (se 1 (by rfl) ⟨1711847, by rfl⟩ : syracuseStep 2282463 = 3423695) B3423695
theorem B3423701 : Blo 2281435 3423701 := bbase (se 7 (by rfl) ⟨40121, by rfl⟩ : syracuseStep 3423701 = 80243) (by norm_num)
theorem B2282467 : Blo 2281435 2282467 := bstep (se 1 (by rfl) ⟨1711850, by rfl⟩ : syracuseStep 2282467 = 3423701) B3423701
theorem B8666261 : Blo 2281435 8666261 := bbase (se 6 (by rfl) ⟨203115, by rfl⟩ : syracuseStep 8666261 = 406231) (by norm_num)
theorem B5777507 : Blo 2281435 5777507 := bstep (se 1 (by rfl) ⟨4333130, by rfl⟩ : syracuseStep 5777507 = 8666261) B8666261
theorem B3851671 : Blo 2281435 3851671 := bstep (se 1 (by rfl) ⟨2888753, by rfl⟩ : syracuseStep 3851671 = 5777507) B5777507
theorem B5135561 : Blo 2281435 5135561 := bstep (se 2 (by rfl) ⟨1925835, by rfl⟩ : syracuseStep 5135561 = 3851671) B3851671
theorem B3423707 : Blo 2281435 3423707 := bstep (se 1 (by rfl) ⟨2567780, by rfl⟩ : syracuseStep 3423707 = 5135561) B5135561
theorem B2282471 : Blo 2281435 2282471 := bstep (se 1 (by rfl) ⟨1711853, by rfl⟩ : syracuseStep 2282471 = 3423707) B3423707
theorem B2567785 : Blo 2281435 2567785 := bbase (se 2 (by rfl) ⟨962919, by rfl⟩ : syracuseStep 2567785 = 1925839) (by norm_num)
theorem B3423713 : Blo 2281435 3423713 := bstep (se 2 (by rfl) ⟨1283892, by rfl⟩ : syracuseStep 3423713 = 2567785) B2567785
theorem B2282475 : Blo 2281435 2282475 := bstep (se 1 (by rfl) ⟨1711856, by rfl⟩ : syracuseStep 2282475 = 3423713) B3423713
theorem B4874789 : Blo 2281435 4874789 := bbase (se 4 (by rfl) ⟨457011, by rfl⟩ : syracuseStep 4874789 = 914023) (by norm_num)
theorem B12999437 : Blo 2281435 12999437 := bstep (se 3 (by rfl) ⟨2437394, by rfl⟩ : syracuseStep 12999437 = 4874789) B4874789
theorem B8666291 : Blo 2281435 8666291 := bstep (se 1 (by rfl) ⟨6499718, by rfl⟩ : syracuseStep 8666291 = 12999437) B12999437
theorem B5777527 : Blo 2281435 5777527 := bstep (se 1 (by rfl) ⟨4333145, by rfl⟩ : syracuseStep 5777527 = 8666291) B8666291
theorem B7703369 : Blo 2281435 7703369 := bstep (se 2 (by rfl) ⟨2888763, by rfl⟩ : syracuseStep 7703369 = 5777527) B5777527
theorem B5135579 : Blo 2281435 5135579 := bstep (se 1 (by rfl) ⟨3851684, by rfl⟩ : syracuseStep 5135579 = 7703369) B7703369
theorem B3423719 : Blo 2281435 3423719 := bstep (se 1 (by rfl) ⟨2567789, by rfl⟩ : syracuseStep 3423719 = 5135579) B5135579
theorem B2282479 : Blo 2281435 2282479 := bstep (se 1 (by rfl) ⟨1711859, by rfl⟩ : syracuseStep 2282479 = 3423719) B3423719
theorem B3423725 : Blo 2281435 3423725 := bbase (se 3 (by rfl) ⟨641948, by rfl⟩ : syracuseStep 3423725 = 1283897) (by norm_num)
theorem B2282483 : Blo 2281435 2282483 := bstep (se 1 (by rfl) ⟨1711862, by rfl⟩ : syracuseStep 2282483 = 3423725) B3423725
theorem B5135597 : Blo 2281435 5135597 := bbase (se 3 (by rfl) ⟨962924, by rfl⟩ : syracuseStep 5135597 = 1925849) (by norm_num)
theorem B3423731 : Blo 2281435 3423731 := bstep (se 1 (by rfl) ⟨2567798, by rfl⟩ : syracuseStep 3423731 = 5135597) B5135597
theorem B2282487 : Blo 2281435 2282487 := bstep (se 1 (by rfl) ⟨1711865, by rfl⟩ : syracuseStep 2282487 = 3423731) B3423731
theorem B3249877 : Blo 2281435 3249877 := bbase (se 7 (by rfl) ⟨38084, by rfl⟩ : syracuseStep 3249877 = 76169) (by norm_num)
theorem B4333169 : Blo 2281435 4333169 := bstep (se 2 (by rfl) ⟨1624938, by rfl⟩ : syracuseStep 4333169 = 3249877) B3249877
theorem B2888779 : Blo 2281435 2888779 := bstep (se 1 (by rfl) ⟨2166584, by rfl⟩ : syracuseStep 2888779 = 4333169) B4333169
theorem B3851705 : Blo 2281435 3851705 := bstep (se 2 (by rfl) ⟨1444389, by rfl⟩ : syracuseStep 3851705 = 2888779) B2888779
theorem B2567803 : Blo 2281435 2567803 := bstep (se 1 (by rfl) ⟨1925852, by rfl⟩ : syracuseStep 2567803 = 3851705) B3851705
theorem B3423737 : Blo 2281435 3423737 := bstep (se 2 (by rfl) ⟨1283901, by rfl⟩ : syracuseStep 3423737 = 2567803) B2567803
theorem B2282491 : Blo 2281435 2282491 := bstep (se 1 (by rfl) ⟨1711868, by rfl⟩ : syracuseStep 2282491 = 3423737) B3423737
theorem B166581845 : Blo 2281435 166581845 := bbase (se 8 (by rfl) ⟨976065, by rfl⟩ : syracuseStep 166581845 = 1952131) (by norm_num)
theorem B111054563 : Blo 2281435 111054563 := bstep (se 1 (by rfl) ⟨83290922, by rfl⟩ : syracuseStep 111054563 = 166581845) B166581845
theorem B74036375 : Blo 2281435 74036375 := bstep (se 1 (by rfl) ⟨55527281, by rfl⟩ : syracuseStep 74036375 = 111054563) B111054563
theorem B49357583 : Blo 2281435 49357583 := bstep (se 1 (by rfl) ⟨37018187, by rfl⟩ : syracuseStep 49357583 = 74036375) B74036375
theorem B32905055 : Blo 2281435 32905055 := bstep (se 1 (by rfl) ⟨24678791, by rfl⟩ : syracuseStep 32905055 = 49357583) B49357583
theorem B87746813 : Blo 2281435 87746813 := bstep (se 3 (by rfl) ⟨16452527, by rfl⟩ : syracuseStep 87746813 = 32905055) B32905055
theorem B58497875 : Blo 2281435 58497875 := bstep (se 1 (by rfl) ⟨43873406, by rfl⟩ : syracuseStep 58497875 = 87746813) B87746813
theorem B38998583 : Blo 2281435 38998583 := bstep (se 1 (by rfl) ⟨29248937, by rfl⟩ : syracuseStep 38998583 = 58497875) B58497875
theorem B25999055 : Blo 2281435 25999055 := bstep (se 1 (by rfl) ⟨19499291, by rfl⟩ : syracuseStep 25999055 = 38998583) B38998583
theorem B17332703 : Blo 2281435 17332703 := bstep (se 1 (by rfl) ⟨12999527, by rfl⟩ : syracuseStep 17332703 = 25999055) B25999055
theorem B11555135 : Blo 2281435 11555135 := bstep (se 1 (by rfl) ⟨8666351, by rfl⟩ : syracuseStep 11555135 = 17332703) B17332703
theorem B7703423 : Blo 2281435 7703423 := bstep (se 1 (by rfl) ⟨5777567, by rfl⟩ : syracuseStep 7703423 = 11555135) B11555135
theorem B5135615 : Blo 2281435 5135615 := bstep (se 1 (by rfl) ⟨3851711, by rfl⟩ : syracuseStep 5135615 = 7703423) B7703423
theorem B3423743 : Blo 2281435 3423743 := bstep (se 1 (by rfl) ⟨2567807, by rfl⟩ : syracuseStep 3423743 = 5135615) B5135615
theorem B2282495 : Blo 2281435 2282495 := bstep (se 1 (by rfl) ⟨1711871, by rfl⟩ : syracuseStep 2282495 = 3423743) B3423743
theorem B3423749 : Blo 2281435 3423749 := bbase (se 4 (by rfl) ⟨320976, by rfl⟩ : syracuseStep 3423749 = 641953) (by norm_num)
theorem B2282499 : Blo 2281435 2282499 := bstep (se 1 (by rfl) ⟨1711874, by rfl⟩ : syracuseStep 2282499 = 3423749) B3423749
theorem B3851725 : Blo 2281435 3851725 := bbase (se 3 (by rfl) ⟨722198, by rfl⟩ : syracuseStep 3851725 = 1444397) (by norm_num)
theorem B5135633 : Blo 2281435 5135633 := bstep (se 2 (by rfl) ⟨1925862, by rfl⟩ : syracuseStep 5135633 = 3851725) B3851725
theorem B3423755 : Blo 2281435 3423755 := bstep (se 1 (by rfl) ⟨2567816, by rfl⟩ : syracuseStep 3423755 = 5135633) B5135633
theorem B2282503 : Blo 2281435 2282503 := bstep (se 1 (by rfl) ⟨1711877, by rfl⟩ : syracuseStep 2282503 = 3423755) B3423755
theorem B2567821 : Blo 2281435 2567821 := bbase (se 3 (by rfl) ⟨481466, by rfl⟩ : syracuseStep 2567821 = 962933) (by norm_num)
theorem B3423761 : Blo 2281435 3423761 := bstep (se 2 (by rfl) ⟨1283910, by rfl⟩ : syracuseStep 3423761 = 2567821) B2567821
theorem B2282507 : Blo 2281435 2282507 := bstep (se 1 (by rfl) ⟨1711880, by rfl⟩ : syracuseStep 2282507 = 3423761) B3423761
theorem B7703477 : Blo 2281435 7703477 := bbase (se 5 (by rfl) ⟨361100, by rfl⟩ : syracuseStep 7703477 = 722201) (by norm_num)
theorem B5135651 : Blo 2281435 5135651 := bstep (se 1 (by rfl) ⟨3851738, by rfl⟩ : syracuseStep 5135651 = 7703477) B7703477
theorem B3423767 : Blo 2281435 3423767 := bstep (se 1 (by rfl) ⟨2567825, by rfl⟩ : syracuseStep 3423767 = 5135651) B5135651
theorem B2282511 : Blo 2281435 2282511 := bstep (se 1 (by rfl) ⟨1711883, by rfl⟩ : syracuseStep 2282511 = 3423767) B3423767
theorem B3423773 : Blo 2281435 3423773 := bbase (se 3 (by rfl) ⟨641957, by rfl⟩ : syracuseStep 3423773 = 1283915) (by norm_num)
theorem B2282515 : Blo 2281435 2282515 := bstep (se 1 (by rfl) ⟨1711886, by rfl⟩ : syracuseStep 2282515 = 3423773) B3423773
theorem B5135669 : Blo 2281435 5135669 := bbase (se 5 (by rfl) ⟨240734, by rfl⟩ : syracuseStep 5135669 = 481469) (by norm_num)
theorem B3423779 : Blo 2281435 3423779 := bstep (se 1 (by rfl) ⟨2567834, by rfl⟩ : syracuseStep 3423779 = 5135669) B5135669
theorem B2282519 : Blo 2281435 2282519 := bstep (se 1 (by rfl) ⟨1711889, by rfl⟩ : syracuseStep 2282519 = 3423779) B3423779
theorem B9380933 : Blo 2281435 9380933 := bbase (se 4 (by rfl) ⟨879462, by rfl⟩ : syracuseStep 9380933 = 1758925) (by norm_num)
theorem B6253955 : Blo 2281435 6253955 := bstep (se 1 (by rfl) ⟨4690466, by rfl⟩ : syracuseStep 6253955 = 9380933) B9380933
theorem B4169303 : Blo 2281435 4169303 := bstep (se 1 (by rfl) ⟨3126977, by rfl⟩ : syracuseStep 4169303 = 6253955) B6253955
theorem B2779535 : Blo 2281435 2779535 := bstep (se 1 (by rfl) ⟨2084651, by rfl⟩ : syracuseStep 2779535 = 4169303) B4169303
theorem B7412093 : Blo 2281435 7412093 := bstep (se 3 (by rfl) ⟨1389767, by rfl⟩ : syracuseStep 7412093 = 2779535) B2779535
theorem B4941395 : Blo 2281435 4941395 := bstep (se 1 (by rfl) ⟨3706046, by rfl⟩ : syracuseStep 4941395 = 7412093) B7412093
theorem B3294263 : Blo 2281435 3294263 := bstep (se 1 (by rfl) ⟨2470697, by rfl⟩ : syracuseStep 3294263 = 4941395) B4941395
theorem B8784701 : Blo 2281435 8784701 := bstep (se 3 (by rfl) ⟨1647131, by rfl⟩ : syracuseStep 8784701 = 3294263) B3294263
theorem B5856467 : Blo 2281435 5856467 := bstep (se 1 (by rfl) ⟨4392350, by rfl⟩ : syracuseStep 5856467 = 8784701) B8784701
theorem B15617245 : Blo 2281435 15617245 := bstep (se 3 (by rfl) ⟨2928233, by rfl⟩ : syracuseStep 15617245 = 5856467) B5856467
theorem B20822993 : Blo 2281435 20822993 := bstep (se 2 (by rfl) ⟨7808622, by rfl⟩ : syracuseStep 20822993 = 15617245) B15617245
theorem B13881995 : Blo 2281435 13881995 := bstep (se 1 (by rfl) ⟨10411496, by rfl⟩ : syracuseStep 13881995 = 20822993) B20822993
theorem B9254663 : Blo 2281435 9254663 := bstep (se 1 (by rfl) ⟨6940997, by rfl⟩ : syracuseStep 9254663 = 13881995) B13881995
theorem B6169775 : Blo 2281435 6169775 := bstep (se 1 (by rfl) ⟨4627331, by rfl⟩ : syracuseStep 6169775 = 9254663) B9254663
theorem B16452733 : Blo 2281435 16452733 := bstep (se 3 (by rfl) ⟨3084887, by rfl⟩ : syracuseStep 16452733 = 6169775) B6169775
theorem B21936977 : Blo 2281435 21936977 := bstep (se 2 (by rfl) ⟨8226366, by rfl⟩ : syracuseStep 21936977 = 16452733) B16452733
theorem B14624651 : Blo 2281435 14624651 := bstep (se 1 (by rfl) ⟨10968488, by rfl⟩ : syracuseStep 14624651 = 21936977) B21936977
theorem B9749767 : Blo 2281435 9749767 := bstep (se 1 (by rfl) ⟨7312325, by rfl⟩ : syracuseStep 9749767 = 14624651) B14624651
theorem B12999689 : Blo 2281435 12999689 := bstep (se 2 (by rfl) ⟨4874883, by rfl⟩ : syracuseStep 12999689 = 9749767) B9749767
theorem B8666459 : Blo 2281435 8666459 := bstep (se 1 (by rfl) ⟨6499844, by rfl⟩ : syracuseStep 8666459 = 12999689) B12999689
theorem B5777639 : Blo 2281435 5777639 := bstep (se 1 (by rfl) ⟨4333229, by rfl⟩ : syracuseStep 5777639 = 8666459) B8666459
theorem B3851759 : Blo 2281435 3851759 := bstep (se 1 (by rfl) ⟨2888819, by rfl⟩ : syracuseStep 3851759 = 5777639) B5777639
theorem B2567839 : Blo 2281435 2567839 := bstep (se 1 (by rfl) ⟨1925879, by rfl⟩ : syracuseStep 2567839 = 3851759) B3851759
theorem B3423785 : Blo 2281435 3423785 := bstep (se 2 (by rfl) ⟨1283919, by rfl⟩ : syracuseStep 3423785 = 2567839) B2567839
theorem B2282523 : Blo 2281435 2282523 := bstep (se 1 (by rfl) ⟨1711892, by rfl⟩ : syracuseStep 2282523 = 3423785) B3423785
theorem B21937013 : Blo 2281435 21937013 := bbase (se 5 (by rfl) ⟨1028297, by rfl⟩ : syracuseStep 21937013 = 2056595) (by norm_num)
theorem B14624675 : Blo 2281435 14624675 := bstep (se 1 (by rfl) ⟨10968506, by rfl⟩ : syracuseStep 14624675 = 21937013) B21937013
theorem B9749783 : Blo 2281435 9749783 := bstep (se 1 (by rfl) ⟨7312337, by rfl⟩ : syracuseStep 9749783 = 14624675) B14624675
theorem B6499855 : Blo 2281435 6499855 := bstep (se 1 (by rfl) ⟨4874891, by rfl⟩ : syracuseStep 6499855 = 9749783) B9749783
theorem B8666473 : Blo 2281435 8666473 := bstep (se 2 (by rfl) ⟨3249927, by rfl⟩ : syracuseStep 8666473 = 6499855) B6499855
theorem B11555297 : Blo 2281435 11555297 := bstep (se 2 (by rfl) ⟨4333236, by rfl⟩ : syracuseStep 11555297 = 8666473) B8666473
theorem B7703531 : Blo 2281435 7703531 := bstep (se 1 (by rfl) ⟨5777648, by rfl⟩ : syracuseStep 7703531 = 11555297) B11555297
theorem B5135687 : Blo 2281435 5135687 := bstep (se 1 (by rfl) ⟨3851765, by rfl⟩ : syracuseStep 5135687 = 7703531) B7703531
theorem B3423791 : Blo 2281435 3423791 := bstep (se 1 (by rfl) ⟨2567843, by rfl⟩ : syracuseStep 3423791 = 5135687) B5135687
theorem B2282527 : Blo 2281435 2282527 := bstep (se 1 (by rfl) ⟨1711895, by rfl⟩ : syracuseStep 2282527 = 3423791) B3423791
theorem B3423797 : Blo 2281435 3423797 := bbase (se 5 (by rfl) ⟨160490, by rfl⟩ : syracuseStep 3423797 = 320981) (by norm_num)
theorem B2282531 : Blo 2281435 2282531 := bstep (se 1 (by rfl) ⟨1711898, by rfl⟩ : syracuseStep 2282531 = 3423797) B3423797
theorem B5777669 : Blo 2281435 5777669 := bbase (se 4 (by rfl) ⟨541656, by rfl⟩ : syracuseStep 5777669 = 1083313) (by norm_num)
theorem B3851779 : Blo 2281435 3851779 := bstep (se 1 (by rfl) ⟨2888834, by rfl⟩ : syracuseStep 3851779 = 5777669) B5777669
theorem B5135705 : Blo 2281435 5135705 := bstep (se 2 (by rfl) ⟨1925889, by rfl⟩ : syracuseStep 5135705 = 3851779) B3851779
theorem B3423803 : Blo 2281435 3423803 := bstep (se 1 (by rfl) ⟨2567852, by rfl⟩ : syracuseStep 3423803 = 5135705) B5135705
theorem B2282535 : Blo 2281435 2282535 := bstep (se 1 (by rfl) ⟨1711901, by rfl⟩ : syracuseStep 2282535 = 3423803) B3423803
theorem B2567857 : Blo 2281435 2567857 := bbase (se 2 (by rfl) ⟨962946, by rfl⟩ : syracuseStep 2567857 = 1925893) (by norm_num)
theorem B3423809 : Blo 2281435 3423809 := bstep (se 2 (by rfl) ⟨1283928, by rfl⟩ : syracuseStep 3423809 = 2567857) B2567857
theorem B2282539 : Blo 2281435 2282539 := bstep (se 1 (by rfl) ⟨1711904, by rfl⟩ : syracuseStep 2282539 = 3423809) B3423809
theorem B5484293 : Blo 2281435 5484293 := bbase (se 4 (by rfl) ⟨514152, by rfl⟩ : syracuseStep 5484293 = 1028305) (by norm_num)
theorem B3656195 : Blo 2281435 3656195 := bstep (se 1 (by rfl) ⟨2742146, by rfl⟩ : syracuseStep 3656195 = 5484293) B5484293
theorem B2437463 : Blo 2281435 2437463 := bstep (se 1 (by rfl) ⟨1828097, by rfl⟩ : syracuseStep 2437463 = 3656195) B3656195
theorem B6499901 : Blo 2281435 6499901 := bstep (se 3 (by rfl) ⟨1218731, by rfl⟩ : syracuseStep 6499901 = 2437463) B2437463
theorem B4333267 : Blo 2281435 4333267 := bstep (se 1 (by rfl) ⟨3249950, by rfl⟩ : syracuseStep 4333267 = 6499901) B6499901
theorem B5777689 : Blo 2281435 5777689 := bstep (se 2 (by rfl) ⟨2166633, by rfl⟩ : syracuseStep 5777689 = 4333267) B4333267
theorem B7703585 : Blo 2281435 7703585 := bstep (se 2 (by rfl) ⟨2888844, by rfl⟩ : syracuseStep 7703585 = 5777689) B5777689
theorem B5135723 : Blo 2281435 5135723 := bstep (se 1 (by rfl) ⟨3851792, by rfl⟩ : syracuseStep 5135723 = 7703585) B7703585
theorem B3423815 : Blo 2281435 3423815 := bstep (se 1 (by rfl) ⟨2567861, by rfl⟩ : syracuseStep 3423815 = 5135723) B5135723
theorem B2282543 : Blo 2281435 2282543 := bstep (se 1 (by rfl) ⟨1711907, by rfl⟩ : syracuseStep 2282543 = 3423815) B3423815
theorem B3423821 : Blo 2281435 3423821 := bbase (se 3 (by rfl) ⟨641966, by rfl⟩ : syracuseStep 3423821 = 1283933) (by norm_num)
theorem B2282547 : Blo 2281435 2282547 := bstep (se 1 (by rfl) ⟨1711910, by rfl⟩ : syracuseStep 2282547 = 3423821) B3423821
theorem B5135741 : Blo 2281435 5135741 := bbase (se 3 (by rfl) ⟨962951, by rfl⟩ : syracuseStep 5135741 = 1925903) (by norm_num)
theorem B3423827 : Blo 2281435 3423827 := bstep (se 1 (by rfl) ⟨2567870, by rfl⟩ : syracuseStep 3423827 = 5135741) B5135741
theorem B2282551 : Blo 2281435 2282551 := bstep (se 1 (by rfl) ⟨1711913, by rfl⟩ : syracuseStep 2282551 = 3423827) B3423827
theorem B3851813 : Blo 2281435 3851813 := bbase (se 4 (by rfl) ⟨361107, by rfl⟩ : syracuseStep 3851813 = 722215) (by norm_num)
theorem B2567875 : Blo 2281435 2567875 := bstep (se 1 (by rfl) ⟨1925906, by rfl⟩ : syracuseStep 2567875 = 3851813) B3851813
theorem B3423833 : Blo 2281435 3423833 := bstep (se 2 (by rfl) ⟨1283937, by rfl⟩ : syracuseStep 3423833 = 2567875) B2567875
theorem B2282555 : Blo 2281435 2282555 := bstep (se 1 (by rfl) ⟨1711916, by rfl⟩ : syracuseStep 2282555 = 3423833) B3423833
theorem B3249973 : Blo 2281435 3249973 := bbase (se 5 (by rfl) ⟨152342, by rfl⟩ : syracuseStep 3249973 = 304685) (by norm_num)
theorem B17333189 : Blo 2281435 17333189 := bstep (se 4 (by rfl) ⟨1624986, by rfl⟩ : syracuseStep 17333189 = 3249973) B3249973
theorem B11555459 : Blo 2281435 11555459 := bstep (se 1 (by rfl) ⟨8666594, by rfl⟩ : syracuseStep 11555459 = 17333189) B17333189
theorem B7703639 : Blo 2281435 7703639 := bstep (se 1 (by rfl) ⟨5777729, by rfl⟩ : syracuseStep 7703639 = 11555459) B11555459
theorem B5135759 : Blo 2281435 5135759 := bstep (se 1 (by rfl) ⟨3851819, by rfl⟩ : syracuseStep 5135759 = 7703639) B7703639
theorem B3423839 : Blo 2281435 3423839 := bstep (se 1 (by rfl) ⟨2567879, by rfl⟩ : syracuseStep 3423839 = 5135759) B5135759
theorem B2282559 : Blo 2281435 2282559 := bstep (se 1 (by rfl) ⟨1711919, by rfl⟩ : syracuseStep 2282559 = 3423839) B3423839
theorem B3423845 : Blo 2281435 3423845 := bbase (se 4 (by rfl) ⟨320985, by rfl⟩ : syracuseStep 3423845 = 641971) (by norm_num)
theorem B2282563 : Blo 2281435 2282563 := bstep (se 1 (by rfl) ⟨1711922, by rfl⟩ : syracuseStep 2282563 = 3423845) B3423845
theorem B2437489 : Blo 2281435 2437489 := bbase (se 2 (by rfl) ⟨914058, by rfl⟩ : syracuseStep 2437489 = 1828117) (by norm_num)
theorem B3249985 : Blo 2281435 3249985 := bstep (se 2 (by rfl) ⟨1218744, by rfl⟩ : syracuseStep 3249985 = 2437489) B2437489
theorem B4333313 : Blo 2281435 4333313 := bstep (se 2 (by rfl) ⟨1624992, by rfl⟩ : syracuseStep 4333313 = 3249985) B3249985
theorem B2888875 : Blo 2281435 2888875 := bstep (se 1 (by rfl) ⟨2166656, by rfl⟩ : syracuseStep 2888875 = 4333313) B4333313
theorem B3851833 : Blo 2281435 3851833 := bstep (se 2 (by rfl) ⟨1444437, by rfl⟩ : syracuseStep 3851833 = 2888875) B2888875
theorem B5135777 : Blo 2281435 5135777 := bstep (se 2 (by rfl) ⟨1925916, by rfl⟩ : syracuseStep 5135777 = 3851833) B3851833
theorem B3423851 : Blo 2281435 3423851 := bstep (se 1 (by rfl) ⟨2567888, by rfl⟩ : syracuseStep 3423851 = 5135777) B5135777
theorem B2282567 : Blo 2281435 2282567 := bstep (se 1 (by rfl) ⟨1711925, by rfl⟩ : syracuseStep 2282567 = 3423851) B3423851
theorem B2567893 : Blo 2281435 2567893 := bbase (se 7 (by rfl) ⟨30092, by rfl⟩ : syracuseStep 2567893 = 60185) (by norm_num)
theorem B3423857 : Blo 2281435 3423857 := bstep (se 2 (by rfl) ⟨1283946, by rfl⟩ : syracuseStep 3423857 = 2567893) B2567893
theorem B2282571 : Blo 2281435 2282571 := bstep (se 1 (by rfl) ⟨1711928, by rfl⟩ : syracuseStep 2282571 = 3423857) B3423857
theorem B2888885 : Blo 2281435 2888885 := bbase (se 5 (by rfl) ⟨135416, by rfl⟩ : syracuseStep 2888885 = 270833) (by norm_num)
theorem B7703693 : Blo 2281435 7703693 := bstep (se 3 (by rfl) ⟨1444442, by rfl⟩ : syracuseStep 7703693 = 2888885) B2888885
theorem B5135795 : Blo 2281435 5135795 := bstep (se 1 (by rfl) ⟨3851846, by rfl⟩ : syracuseStep 5135795 = 7703693) B7703693
theorem B3423863 : Blo 2281435 3423863 := bstep (se 1 (by rfl) ⟨2567897, by rfl⟩ : syracuseStep 3423863 = 5135795) B5135795
theorem B2282575 : Blo 2281435 2282575 := bstep (se 1 (by rfl) ⟨1711931, by rfl⟩ : syracuseStep 2282575 = 3423863) B3423863
theorem B3423869 : Blo 2281435 3423869 := bbase (se 3 (by rfl) ⟨641975, by rfl⟩ : syracuseStep 3423869 = 1283951) (by norm_num)
theorem B2282579 : Blo 2281435 2282579 := bstep (se 1 (by rfl) ⟨1711934, by rfl⟩ : syracuseStep 2282579 = 3423869) B3423869
theorem B5135813 : Blo 2281435 5135813 := bbase (se 4 (by rfl) ⟨481482, by rfl⟩ : syracuseStep 5135813 = 962965) (by norm_num)
theorem B3423875 : Blo 2281435 3423875 := bstep (se 1 (by rfl) ⟨2567906, by rfl⟩ : syracuseStep 3423875 = 5135813) B5135813
theorem B2282583 : Blo 2281435 2282583 := bstep (se 1 (by rfl) ⟨1711937, by rfl⟩ : syracuseStep 2282583 = 3423875) B3423875
theorem B3470597 : Blo 2281435 3470597 := bbase (se 4 (by rfl) ⟨325368, by rfl⟩ : syracuseStep 3470597 = 650737) (by norm_num)
theorem B2313731 : Blo 2281435 2313731 := bstep (se 1 (by rfl) ⟨1735298, by rfl⟩ : syracuseStep 2313731 = 3470597) B3470597
theorem B6169949 : Blo 2281435 6169949 := bstep (se 3 (by rfl) ⟨1156865, by rfl⟩ : syracuseStep 6169949 = 2313731) B2313731
theorem B4113299 : Blo 2281435 4113299 := bstep (se 1 (by rfl) ⟨3084974, by rfl⟩ : syracuseStep 4113299 = 6169949) B6169949
theorem B10968797 : Blo 2281435 10968797 := bstep (se 3 (by rfl) ⟨2056649, by rfl⟩ : syracuseStep 10968797 = 4113299) B4113299
theorem B7312531 : Blo 2281435 7312531 := bstep (se 1 (by rfl) ⟨5484398, by rfl⟩ : syracuseStep 7312531 = 10968797) B10968797
theorem B9750041 : Blo 2281435 9750041 := bstep (se 2 (by rfl) ⟨3656265, by rfl⟩ : syracuseStep 9750041 = 7312531) B7312531
theorem B6500027 : Blo 2281435 6500027 := bstep (se 1 (by rfl) ⟨4875020, by rfl⟩ : syracuseStep 6500027 = 9750041) B9750041
theorem B4333351 : Blo 2281435 4333351 := bstep (se 1 (by rfl) ⟨3250013, by rfl⟩ : syracuseStep 4333351 = 6500027) B6500027
theorem B5777801 : Blo 2281435 5777801 := bstep (se 2 (by rfl) ⟨2166675, by rfl⟩ : syracuseStep 5777801 = 4333351) B4333351
theorem B3851867 : Blo 2281435 3851867 := bstep (se 1 (by rfl) ⟨2888900, by rfl⟩ : syracuseStep 3851867 = 5777801) B5777801
theorem B2567911 : Blo 2281435 2567911 := bstep (se 1 (by rfl) ⟨1925933, by rfl⟩ : syracuseStep 2567911 = 3851867) B3851867
theorem B3423881 : Blo 2281435 3423881 := bstep (se 2 (by rfl) ⟨1283955, by rfl⟩ : syracuseStep 3423881 = 2567911) B2567911
theorem B2282587 : Blo 2281435 2282587 := bstep (se 1 (by rfl) ⟨1711940, by rfl⟩ : syracuseStep 2282587 = 3423881) B3423881
theorem B11555621 : Blo 2281435 11555621 := bbase (se 4 (by rfl) ⟨1083339, by rfl⟩ : syracuseStep 11555621 = 2166679) (by norm_num)
theorem B7703747 : Blo 2281435 7703747 := bstep (se 1 (by rfl) ⟨5777810, by rfl⟩ : syracuseStep 7703747 = 11555621) B11555621
theorem B5135831 : Blo 2281435 5135831 := bstep (se 1 (by rfl) ⟨3851873, by rfl⟩ : syracuseStep 5135831 = 7703747) B7703747
theorem B3423887 : Blo 2281435 3423887 := bstep (se 1 (by rfl) ⟨2567915, by rfl⟩ : syracuseStep 3423887 = 5135831) B5135831
theorem B2282591 : Blo 2281435 2282591 := bstep (se 1 (by rfl) ⟨1711943, by rfl⟩ : syracuseStep 2282591 = 3423887) B3423887
theorem B3423893 : Blo 2281435 3423893 := bbase (se 6 (by rfl) ⟨80247, by rfl⟩ : syracuseStep 3423893 = 160495) (by norm_num)
theorem B2282595 : Blo 2281435 2282595 := bstep (se 1 (by rfl) ⟨1711946, by rfl⟩ : syracuseStep 2282595 = 3423893) B3423893
theorem B10968853 : Blo 2281435 10968853 := bbase (se 6 (by rfl) ⟨257082, by rfl⟩ : syracuseStep 10968853 = 514165) (by norm_num)
theorem B14625137 : Blo 2281435 14625137 := bstep (se 2 (by rfl) ⟨5484426, by rfl⟩ : syracuseStep 14625137 = 10968853) B10968853
theorem B9750091 : Blo 2281435 9750091 := bstep (se 1 (by rfl) ⟨7312568, by rfl⟩ : syracuseStep 9750091 = 14625137) B14625137
theorem B13000121 : Blo 2281435 13000121 := bstep (se 2 (by rfl) ⟨4875045, by rfl⟩ : syracuseStep 13000121 = 9750091) B9750091
theorem B8666747 : Blo 2281435 8666747 := bstep (se 1 (by rfl) ⟨6500060, by rfl⟩ : syracuseStep 8666747 = 13000121) B13000121
theorem B5777831 : Blo 2281435 5777831 := bstep (se 1 (by rfl) ⟨4333373, by rfl⟩ : syracuseStep 5777831 = 8666747) B8666747
theorem B3851887 : Blo 2281435 3851887 := bstep (se 1 (by rfl) ⟨2888915, by rfl⟩ : syracuseStep 3851887 = 5777831) B5777831
theorem B5135849 : Blo 2281435 5135849 := bstep (se 2 (by rfl) ⟨1925943, by rfl⟩ : syracuseStep 5135849 = 3851887) B3851887
theorem B3423899 : Blo 2281435 3423899 := bstep (se 1 (by rfl) ⟨2567924, by rfl⟩ : syracuseStep 3423899 = 5135849) B5135849
theorem B2282599 : Blo 2281435 2282599 := bstep (se 1 (by rfl) ⟨1711949, by rfl⟩ : syracuseStep 2282599 = 3423899) B3423899
theorem B2567929 : Blo 2281435 2567929 := bbase (se 2 (by rfl) ⟨962973, by rfl⟩ : syracuseStep 2567929 = 1925947) (by norm_num)
theorem B3423905 : Blo 2281435 3423905 := bstep (se 2 (by rfl) ⟨1283964, by rfl⟩ : syracuseStep 3423905 = 2567929) B2567929
theorem B2282603 : Blo 2281435 2282603 := bstep (se 1 (by rfl) ⟨1711952, by rfl⟩ : syracuseStep 2282603 = 3423905) B3423905
theorem B5205941 : Blo 2281435 5205941 := bbase (se 5 (by rfl) ⟨244028, by rfl⟩ : syracuseStep 5205941 = 488057) (by norm_num)
theorem B3470627 : Blo 2281435 3470627 := bstep (se 1 (by rfl) ⟨2602970, by rfl⟩ : syracuseStep 3470627 = 5205941) B5205941
theorem B9255005 : Blo 2281435 9255005 := bstep (se 3 (by rfl) ⟨1735313, by rfl⟩ : syracuseStep 9255005 = 3470627) B3470627
theorem B6170003 : Blo 2281435 6170003 := bstep (se 1 (by rfl) ⟨4627502, by rfl⟩ : syracuseStep 6170003 = 9255005) B9255005
theorem B4113335 : Blo 2281435 4113335 := bstep (se 1 (by rfl) ⟨3085001, by rfl⟩ : syracuseStep 4113335 = 6170003) B6170003
theorem B2742223 : Blo 2281435 2742223 := bstep (se 1 (by rfl) ⟨2056667, by rfl⟩ : syracuseStep 2742223 = 4113335) B4113335
theorem B3656297 : Blo 2281435 3656297 := bstep (se 2 (by rfl) ⟨1371111, by rfl⟩ : syracuseStep 3656297 = 2742223) B2742223
theorem B9750125 : Blo 2281435 9750125 := bstep (se 3 (by rfl) ⟨1828148, by rfl⟩ : syracuseStep 9750125 = 3656297) B3656297
theorem B6500083 : Blo 2281435 6500083 := bstep (se 1 (by rfl) ⟨4875062, by rfl⟩ : syracuseStep 6500083 = 9750125) B9750125
theorem B8666777 : Blo 2281435 8666777 := bstep (se 2 (by rfl) ⟨3250041, by rfl⟩ : syracuseStep 8666777 = 6500083) B6500083
theorem B5777851 : Blo 2281435 5777851 := bstep (se 1 (by rfl) ⟨4333388, by rfl⟩ : syracuseStep 5777851 = 8666777) B8666777
theorem B7703801 : Blo 2281435 7703801 := bstep (se 2 (by rfl) ⟨2888925, by rfl⟩ : syracuseStep 7703801 = 5777851) B5777851
theorem B5135867 : Blo 2281435 5135867 := bstep (se 1 (by rfl) ⟨3851900, by rfl⟩ : syracuseStep 5135867 = 7703801) B7703801
theorem B3423911 : Blo 2281435 3423911 := bstep (se 1 (by rfl) ⟨2567933, by rfl⟩ : syracuseStep 3423911 = 5135867) B5135867
theorem B2282607 : Blo 2281435 2282607 := bstep (se 1 (by rfl) ⟨1711955, by rfl⟩ : syracuseStep 2282607 = 3423911) B3423911
theorem B3423917 : Blo 2281435 3423917 := bbase (se 3 (by rfl) ⟨641984, by rfl⟩ : syracuseStep 3423917 = 1283969) (by norm_num)
theorem B2282611 : Blo 2281435 2282611 := bstep (se 1 (by rfl) ⟨1711958, by rfl⟩ : syracuseStep 2282611 = 3423917) B3423917
theorem B5135885 : Blo 2281435 5135885 := bbase (se 3 (by rfl) ⟨962978, by rfl⟩ : syracuseStep 5135885 = 1925957) (by norm_num)
theorem B3423923 : Blo 2281435 3423923 := bstep (se 1 (by rfl) ⟨2567942, by rfl⟩ : syracuseStep 3423923 = 5135885) B5135885
theorem B2282615 : Blo 2281435 2282615 := bstep (se 1 (by rfl) ⟨1711961, by rfl⟩ : syracuseStep 2282615 = 3423923) B3423923
theorem B2888941 : Blo 2281435 2888941 := bbase (se 3 (by rfl) ⟨541676, by rfl⟩ : syracuseStep 2888941 = 1083353) (by norm_num)
theorem B3851921 : Blo 2281435 3851921 := bstep (se 2 (by rfl) ⟨1444470, by rfl⟩ : syracuseStep 3851921 = 2888941) B2888941
theorem B2567947 : Blo 2281435 2567947 := bstep (se 1 (by rfl) ⟨1925960, by rfl⟩ : syracuseStep 2567947 = 3851921) B3851921
theorem B3423929 : Blo 2281435 3423929 := bstep (se 2 (by rfl) ⟨1283973, by rfl⟩ : syracuseStep 3423929 = 2567947) B2567947
theorem B2282619 : Blo 2281435 2282619 := bstep (se 1 (by rfl) ⟨1711964, by rfl⟩ : syracuseStep 2282619 = 3423929) B3423929
theorem B18510133 : Blo 2281435 18510133 := bbase (se 5 (by rfl) ⟨867662, by rfl⟩ : syracuseStep 18510133 = 1735325) (by norm_num)
theorem B24680177 : Blo 2281435 24680177 := bstep (se 2 (by rfl) ⟨9255066, by rfl⟩ : syracuseStep 24680177 = 18510133) B18510133
theorem B16453451 : Blo 2281435 16453451 := bstep (se 1 (by rfl) ⟨12340088, by rfl⟩ : syracuseStep 16453451 = 24680177) B24680177
theorem B10968967 : Blo 2281435 10968967 := bstep (se 1 (by rfl) ⟨8226725, by rfl⟩ : syracuseStep 10968967 = 16453451) B16453451
theorem B14625289 : Blo 2281435 14625289 := bstep (se 2 (by rfl) ⟨5484483, by rfl⟩ : syracuseStep 14625289 = 10968967) B10968967
theorem B19500385 : Blo 2281435 19500385 := bstep (se 2 (by rfl) ⟨7312644, by rfl⟩ : syracuseStep 19500385 = 14625289) B14625289
theorem B26000513 : Blo 2281435 26000513 := bstep (se 2 (by rfl) ⟨9750192, by rfl⟩ : syracuseStep 26000513 = 19500385) B19500385
theorem B17333675 : Blo 2281435 17333675 := bstep (se 1 (by rfl) ⟨13000256, by rfl⟩ : syracuseStep 17333675 = 26000513) B26000513
theorem B11555783 : Blo 2281435 11555783 := bstep (se 1 (by rfl) ⟨8666837, by rfl⟩ : syracuseStep 11555783 = 17333675) B17333675
theorem B7703855 : Blo 2281435 7703855 := bstep (se 1 (by rfl) ⟨5777891, by rfl⟩ : syracuseStep 7703855 = 11555783) B11555783
theorem B5135903 : Blo 2281435 5135903 := bstep (se 1 (by rfl) ⟨3851927, by rfl⟩ : syracuseStep 5135903 = 7703855) B7703855
theorem B3423935 : Blo 2281435 3423935 := bstep (se 1 (by rfl) ⟨2567951, by rfl⟩ : syracuseStep 3423935 = 5135903) B5135903
theorem B2282623 : Blo 2281435 2282623 := bstep (se 1 (by rfl) ⟨1711967, by rfl⟩ : syracuseStep 2282623 = 3423935) B3423935
theorem B3423941 : Blo 2281435 3423941 := bbase (se 4 (by rfl) ⟨320994, by rfl⟩ : syracuseStep 3423941 = 641989) (by norm_num)
theorem B2282627 : Blo 2281435 2282627 := bstep (se 1 (by rfl) ⟨1711970, by rfl⟩ : syracuseStep 2282627 = 3423941) B3423941
theorem B3851941 : Blo 2281435 3851941 := bbase (se 4 (by rfl) ⟨361119, by rfl⟩ : syracuseStep 3851941 = 722239) (by norm_num)
theorem B5135921 : Blo 2281435 5135921 := bstep (se 2 (by rfl) ⟨1925970, by rfl⟩ : syracuseStep 5135921 = 3851941) B3851941
theorem B3423947 : Blo 2281435 3423947 := bstep (se 1 (by rfl) ⟨2567960, by rfl⟩ : syracuseStep 3423947 = 5135921) B5135921
theorem B2282631 : Blo 2281435 2282631 := bstep (se 1 (by rfl) ⟨1711973, by rfl⟩ : syracuseStep 2282631 = 3423947) B3423947
theorem B2567965 : Blo 2281435 2567965 := bbase (se 3 (by rfl) ⟨481493, by rfl⟩ : syracuseStep 2567965 = 962987) (by norm_num)
theorem B3423953 : Blo 2281435 3423953 := bstep (se 2 (by rfl) ⟨1283982, by rfl⟩ : syracuseStep 3423953 = 2567965) B2567965
theorem B2282635 : Blo 2281435 2282635 := bstep (se 1 (by rfl) ⟨1711976, by rfl⟩ : syracuseStep 2282635 = 3423953) B3423953
theorem B7703909 : Blo 2281435 7703909 := bbase (se 4 (by rfl) ⟨722241, by rfl⟩ : syracuseStep 7703909 = 1444483) (by norm_num)
theorem B5135939 : Blo 2281435 5135939 := bstep (se 1 (by rfl) ⟨3851954, by rfl⟩ : syracuseStep 5135939 = 7703909) B7703909
theorem B3423959 : Blo 2281435 3423959 := bstep (se 1 (by rfl) ⟨2567969, by rfl⟩ : syracuseStep 3423959 = 5135939) B5135939
theorem B2282639 : Blo 2281435 2282639 := bstep (se 1 (by rfl) ⟨1711979, by rfl⟩ : syracuseStep 2282639 = 3423959) B3423959
theorem B3423965 : Blo 2281435 3423965 := bbase (se 3 (by rfl) ⟨641993, by rfl⟩ : syracuseStep 3423965 = 1283987) (by norm_num)
theorem B2282643 : Blo 2281435 2282643 := bstep (se 1 (by rfl) ⟨1711982, by rfl⟩ : syracuseStep 2282643 = 3423965) B3423965
theorem B5135957 : Blo 2281435 5135957 := bbase (se 8 (by rfl) ⟨30093, by rfl⟩ : syracuseStep 5135957 = 60187) (by norm_num)
theorem B3423971 : Blo 2281435 3423971 := bstep (se 1 (by rfl) ⟨2567978, by rfl⟩ : syracuseStep 3423971 = 5135957) B5135957
theorem B2282647 : Blo 2281435 2282647 := bstep (se 1 (by rfl) ⟨1711985, by rfl⟩ : syracuseStep 2282647 = 3423971) B3423971
theorem B4875157 : Blo 2281435 4875157 := bbase (se 6 (by rfl) ⟨114261, by rfl⟩ : syracuseStep 4875157 = 228523) (by norm_num)
theorem B6500209 : Blo 2281435 6500209 := bstep (se 2 (by rfl) ⟨2437578, by rfl⟩ : syracuseStep 6500209 = 4875157) B4875157
theorem B8666945 : Blo 2281435 8666945 := bstep (se 2 (by rfl) ⟨3250104, by rfl⟩ : syracuseStep 8666945 = 6500209) B6500209
theorem B5777963 : Blo 2281435 5777963 := bstep (se 1 (by rfl) ⟨4333472, by rfl⟩ : syracuseStep 5777963 = 8666945) B8666945
theorem B3851975 : Blo 2281435 3851975 := bstep (se 1 (by rfl) ⟨2888981, by rfl⟩ : syracuseStep 3851975 = 5777963) B5777963
theorem B2567983 : Blo 2281435 2567983 := bstep (se 1 (by rfl) ⟨1925987, by rfl⟩ : syracuseStep 2567983 = 3851975) B3851975
theorem B3423977 : Blo 2281435 3423977 := bstep (se 2 (by rfl) ⟨1283991, by rfl⟩ : syracuseStep 3423977 = 2567983) B2567983
theorem B2282651 : Blo 2281435 2282651 := bstep (se 1 (by rfl) ⟨1711988, by rfl⟩ : syracuseStep 2282651 = 3423977) B3423977
theorem B4392605 : Blo 2281435 4392605 := bbase (se 3 (by rfl) ⟨823613, by rfl⟩ : syracuseStep 4392605 = 1647227) (by norm_num)
theorem B2928403 : Blo 2281435 2928403 := bstep (se 1 (by rfl) ⟨2196302, by rfl⟩ : syracuseStep 2928403 = 4392605) B4392605
theorem B3904537 : Blo 2281435 3904537 := bstep (se 2 (by rfl) ⟨1464201, by rfl⟩ : syracuseStep 3904537 = 2928403) B2928403
theorem B5206049 : Blo 2281435 5206049 := bstep (se 2 (by rfl) ⟨1952268, by rfl⟩ : syracuseStep 5206049 = 3904537) B3904537
theorem B3470699 : Blo 2281435 3470699 := bstep (se 1 (by rfl) ⟨2603024, by rfl⟩ : syracuseStep 3470699 = 5206049) B5206049
theorem B9255197 : Blo 2281435 9255197 := bstep (se 3 (by rfl) ⟨1735349, by rfl⟩ : syracuseStep 9255197 = 3470699) B3470699
theorem B6170131 : Blo 2281435 6170131 := bstep (se 1 (by rfl) ⟨4627598, by rfl⟩ : syracuseStep 6170131 = 9255197) B9255197
theorem B8226841 : Blo 2281435 8226841 := bstep (se 2 (by rfl) ⟨3085065, by rfl⟩ : syracuseStep 8226841 = 6170131) B6170131
theorem B10969121 : Blo 2281435 10969121 := bstep (se 2 (by rfl) ⟨4113420, by rfl⟩ : syracuseStep 10969121 = 8226841) B8226841
theorem B29250989 : Blo 2281435 29250989 := bstep (se 3 (by rfl) ⟨5484560, by rfl⟩ : syracuseStep 29250989 = 10969121) B10969121
theorem B19500659 : Blo 2281435 19500659 := bstep (se 1 (by rfl) ⟨14625494, by rfl⟩ : syracuseStep 19500659 = 29250989) B29250989
theorem B13000439 : Blo 2281435 13000439 := bstep (se 1 (by rfl) ⟨9750329, by rfl⟩ : syracuseStep 13000439 = 19500659) B19500659
theorem B8666959 : Blo 2281435 8666959 := bstep (se 1 (by rfl) ⟨6500219, by rfl⟩ : syracuseStep 8666959 = 13000439) B13000439
theorem B11555945 : Blo 2281435 11555945 := bstep (se 2 (by rfl) ⟨4333479, by rfl⟩ : syracuseStep 11555945 = 8666959) B8666959
theorem B7703963 : Blo 2281435 7703963 := bstep (se 1 (by rfl) ⟨5777972, by rfl⟩ : syracuseStep 7703963 = 11555945) B11555945
theorem B5135975 : Blo 2281435 5135975 := bstep (se 1 (by rfl) ⟨3851981, by rfl⟩ : syracuseStep 5135975 = 7703963) B7703963
theorem B3423983 : Blo 2281435 3423983 := bstep (se 1 (by rfl) ⟨2567987, by rfl⟩ : syracuseStep 3423983 = 5135975) B5135975
theorem B2282655 : Blo 2281435 2282655 := bstep (se 1 (by rfl) ⟨1711991, by rfl⟩ : syracuseStep 2282655 = 3423983) B3423983
theorem B3423989 : Blo 2281435 3423989 := bbase (se 5 (by rfl) ⟨160499, by rfl⟩ : syracuseStep 3423989 = 320999) (by norm_num)
theorem B2282659 : Blo 2281435 2282659 := bstep (se 1 (by rfl) ⟨1711994, by rfl⟩ : syracuseStep 2282659 = 3423989) B3423989
theorem B5484581 : Blo 2281435 5484581 := bbase (se 4 (by rfl) ⟨514179, by rfl⟩ : syracuseStep 5484581 = 1028359) (by norm_num)
theorem B3656387 : Blo 2281435 3656387 := bstep (se 1 (by rfl) ⟨2742290, by rfl⟩ : syracuseStep 3656387 = 5484581) B5484581
theorem B9750365 : Blo 2281435 9750365 := bstep (se 3 (by rfl) ⟨1828193, by rfl⟩ : syracuseStep 9750365 = 3656387) B3656387
theorem B6500243 : Blo 2281435 6500243 := bstep (se 1 (by rfl) ⟨4875182, by rfl⟩ : syracuseStep 6500243 = 9750365) B9750365
theorem B4333495 : Blo 2281435 4333495 := bstep (se 1 (by rfl) ⟨3250121, by rfl⟩ : syracuseStep 4333495 = 6500243) B6500243
theorem B5777993 : Blo 2281435 5777993 := bstep (se 2 (by rfl) ⟨2166747, by rfl⟩ : syracuseStep 5777993 = 4333495) B4333495
theorem B3851995 : Blo 2281435 3851995 := bstep (se 1 (by rfl) ⟨2888996, by rfl⟩ : syracuseStep 3851995 = 5777993) B5777993
theorem B5135993 : Blo 2281435 5135993 := bstep (se 2 (by rfl) ⟨1925997, by rfl⟩ : syracuseStep 5135993 = 3851995) B3851995
theorem B3423995 : Blo 2281435 3423995 := bstep (se 1 (by rfl) ⟨2567996, by rfl⟩ : syracuseStep 3423995 = 5135993) B5135993
theorem B2282663 : Blo 2281435 2282663 := bstep (se 1 (by rfl) ⟨1711997, by rfl⟩ : syracuseStep 2282663 = 3423995) B3423995
theorem B2568001 : Blo 2281435 2568001 := bbase (se 2 (by rfl) ⟨963000, by rfl⟩ : syracuseStep 2568001 = 1926001) (by norm_num)
theorem B3424001 : Blo 2281435 3424001 := bstep (se 2 (by rfl) ⟨1284000, by rfl⟩ : syracuseStep 3424001 = 2568001) B2568001
theorem B2282667 : Blo 2281435 2282667 := bstep (se 1 (by rfl) ⟨1712000, by rfl⟩ : syracuseStep 2282667 = 3424001) B3424001
theorem B5778013 : Blo 2281435 5778013 := bbase (se 3 (by rfl) ⟨1083377, by rfl⟩ : syracuseStep 5778013 = 2166755) (by norm_num)
theorem B7704017 : Blo 2281435 7704017 := bstep (se 2 (by rfl) ⟨2889006, by rfl⟩ : syracuseStep 7704017 = 5778013) B5778013
theorem B5136011 : Blo 2281435 5136011 := bstep (se 1 (by rfl) ⟨3852008, by rfl⟩ : syracuseStep 5136011 = 7704017) B7704017
theorem B3424007 : Blo 2281435 3424007 := bstep (se 1 (by rfl) ⟨2568005, by rfl⟩ : syracuseStep 3424007 = 5136011) B5136011
theorem B2282671 : Blo 2281435 2282671 := bstep (se 1 (by rfl) ⟨1712003, by rfl⟩ : syracuseStep 2282671 = 3424007) B3424007
theorem B3424013 : Blo 2281435 3424013 := bbase (se 3 (by rfl) ⟨642002, by rfl⟩ : syracuseStep 3424013 = 1284005) (by norm_num)
theorem B2282675 : Blo 2281435 2282675 := bstep (se 1 (by rfl) ⟨1712006, by rfl⟩ : syracuseStep 2282675 = 3424013) B3424013
theorem B5136029 : Blo 2281435 5136029 := bbase (se 3 (by rfl) ⟨963005, by rfl⟩ : syracuseStep 5136029 = 1926011) (by norm_num)
theorem B3424019 : Blo 2281435 3424019 := bstep (se 1 (by rfl) ⟨2568014, by rfl⟩ : syracuseStep 3424019 = 5136029) B5136029
theorem B2282679 : Blo 2281435 2282679 := bstep (se 1 (by rfl) ⟨1712009, by rfl⟩ : syracuseStep 2282679 = 3424019) B3424019
theorem B3852029 : Blo 2281435 3852029 := bbase (se 3 (by rfl) ⟨722255, by rfl⟩ : syracuseStep 3852029 = 1444511) (by norm_num)
theorem B2568019 : Blo 2281435 2568019 := bstep (se 1 (by rfl) ⟨1926014, by rfl⟩ : syracuseStep 2568019 = 3852029) B3852029
theorem B3424025 : Blo 2281435 3424025 := bstep (se 2 (by rfl) ⟨1284009, by rfl⟩ : syracuseStep 3424025 = 2568019) B2568019
theorem B2282683 : Blo 2281435 2282683 := bstep (se 1 (by rfl) ⟨1712012, by rfl⟩ : syracuseStep 2282683 = 3424025) B3424025
theorem B6254405 : Blo 2281435 6254405 := bbase (se 4 (by rfl) ⟨586350, by rfl⟩ : syracuseStep 6254405 = 1172701) (by norm_num)
theorem B4169603 : Blo 2281435 4169603 := bstep (se 1 (by rfl) ⟨3127202, by rfl⟩ : syracuseStep 4169603 = 6254405) B6254405
theorem B11118941 : Blo 2281435 11118941 := bstep (se 3 (by rfl) ⟨2084801, by rfl⟩ : syracuseStep 11118941 = 4169603) B4169603
theorem B7412627 : Blo 2281435 7412627 := bstep (se 1 (by rfl) ⟨5559470, by rfl⟩ : syracuseStep 7412627 = 11118941) B11118941
theorem B4941751 : Blo 2281435 4941751 := bstep (se 1 (by rfl) ⟨3706313, by rfl⟩ : syracuseStep 4941751 = 7412627) B7412627
theorem B6589001 : Blo 2281435 6589001 := bstep (se 2 (by rfl) ⟨2470875, by rfl⟩ : syracuseStep 6589001 = 4941751) B4941751
theorem B4392667 : Blo 2281435 4392667 := bstep (se 1 (by rfl) ⟨3294500, by rfl⟩ : syracuseStep 4392667 = 6589001) B6589001
theorem B5856889 : Blo 2281435 5856889 := bstep (se 2 (by rfl) ⟨2196333, by rfl⟩ : syracuseStep 5856889 = 4392667) B4392667
theorem B7809185 : Blo 2281435 7809185 := bstep (se 2 (by rfl) ⟨2928444, by rfl⟩ : syracuseStep 7809185 = 5856889) B5856889
theorem B5206123 : Blo 2281435 5206123 := bstep (se 1 (by rfl) ⟨3904592, by rfl⟩ : syracuseStep 5206123 = 7809185) B7809185
theorem B6941497 : Blo 2281435 6941497 := bstep (se 2 (by rfl) ⟨2603061, by rfl⟩ : syracuseStep 6941497 = 5206123) B5206123
theorem B9255329 : Blo 2281435 9255329 := bstep (se 2 (by rfl) ⟨3470748, by rfl⟩ : syracuseStep 9255329 = 6941497) B6941497
theorem B6170219 : Blo 2281435 6170219 := bstep (se 1 (by rfl) ⟨4627664, by rfl⟩ : syracuseStep 6170219 = 9255329) B9255329
theorem B4113479 : Blo 2281435 4113479 := bstep (se 1 (by rfl) ⟨3085109, by rfl⟩ : syracuseStep 4113479 = 6170219) B6170219
theorem B2742319 : Blo 2281435 2742319 := bstep (se 1 (by rfl) ⟨2056739, by rfl⟩ : syracuseStep 2742319 = 4113479) B4113479
theorem B3656425 : Blo 2281435 3656425 := bstep (se 2 (by rfl) ⟨1371159, by rfl⟩ : syracuseStep 3656425 = 2742319) B2742319
theorem B4875233 : Blo 2281435 4875233 := bstep (se 2 (by rfl) ⟨1828212, by rfl⟩ : syracuseStep 4875233 = 3656425) B3656425
theorem B13000621 : Blo 2281435 13000621 := bstep (se 3 (by rfl) ⟨2437616, by rfl⟩ : syracuseStep 13000621 = 4875233) B4875233
theorem B17334161 : Blo 2281435 17334161 := bstep (se 2 (by rfl) ⟨6500310, by rfl⟩ : syracuseStep 17334161 = 13000621) B13000621
theorem B11556107 : Blo 2281435 11556107 := bstep (se 1 (by rfl) ⟨8667080, by rfl⟩ : syracuseStep 11556107 = 17334161) B17334161
theorem B7704071 : Blo 2281435 7704071 := bstep (se 1 (by rfl) ⟨5778053, by rfl⟩ : syracuseStep 7704071 = 11556107) B11556107
theorem B5136047 : Blo 2281435 5136047 := bstep (se 1 (by rfl) ⟨3852035, by rfl⟩ : syracuseStep 5136047 = 7704071) B7704071
theorem B3424031 : Blo 2281435 3424031 := bstep (se 1 (by rfl) ⟨2568023, by rfl⟩ : syracuseStep 3424031 = 5136047) B5136047
theorem B2282687 : Blo 2281435 2282687 := bstep (se 1 (by rfl) ⟨1712015, by rfl⟩ : syracuseStep 2282687 = 3424031) B3424031
theorem B3424037 : Blo 2281435 3424037 := bbase (se 4 (by rfl) ⟨321003, by rfl⟩ : syracuseStep 3424037 = 642007) (by norm_num)
theorem B2282691 : Blo 2281435 2282691 := bstep (se 1 (by rfl) ⟨1712018, by rfl⟩ : syracuseStep 2282691 = 3424037) B3424037
theorem B2889037 : Blo 2281435 2889037 := bbase (se 3 (by rfl) ⟨541694, by rfl⟩ : syracuseStep 2889037 = 1083389) (by norm_num)
theorem B3852049 : Blo 2281435 3852049 := bstep (se 2 (by rfl) ⟨1444518, by rfl⟩ : syracuseStep 3852049 = 2889037) B2889037
theorem B5136065 : Blo 2281435 5136065 := bstep (se 2 (by rfl) ⟨1926024, by rfl⟩ : syracuseStep 5136065 = 3852049) B3852049
theorem B3424043 : Blo 2281435 3424043 := bstep (se 1 (by rfl) ⟨2568032, by rfl⟩ : syracuseStep 3424043 = 5136065) B5136065
theorem B2282695 : Blo 2281435 2282695 := bstep (se 1 (by rfl) ⟨1712021, by rfl⟩ : syracuseStep 2282695 = 3424043) B3424043
theorem B2568037 : Blo 2281435 2568037 := bbase (se 4 (by rfl) ⟨240753, by rfl⟩ : syracuseStep 2568037 = 481507) (by norm_num)
theorem B3424049 : Blo 2281435 3424049 := bstep (se 2 (by rfl) ⟨1284018, by rfl⟩ : syracuseStep 3424049 = 2568037) B2568037
theorem B2282699 : Blo 2281435 2282699 := bstep (se 1 (by rfl) ⟨1712024, by rfl⟩ : syracuseStep 2282699 = 3424049) B3424049
theorem B6500357 : Blo 2281435 6500357 := bbase (se 4 (by rfl) ⟨609408, by rfl⟩ : syracuseStep 6500357 = 1218817) (by norm_num)
theorem B4333571 : Blo 2281435 4333571 := bstep (se 1 (by rfl) ⟨3250178, by rfl⟩ : syracuseStep 4333571 = 6500357) B6500357
theorem B2889047 : Blo 2281435 2889047 := bstep (se 1 (by rfl) ⟨2166785, by rfl⟩ : syracuseStep 2889047 = 4333571) B4333571
theorem B7704125 : Blo 2281435 7704125 := bstep (se 3 (by rfl) ⟨1444523, by rfl⟩ : syracuseStep 7704125 = 2889047) B2889047
theorem B5136083 : Blo 2281435 5136083 := bstep (se 1 (by rfl) ⟨3852062, by rfl⟩ : syracuseStep 5136083 = 7704125) B7704125
theorem B3424055 : Blo 2281435 3424055 := bstep (se 1 (by rfl) ⟨2568041, by rfl⟩ : syracuseStep 3424055 = 5136083) B5136083
theorem B2282703 : Blo 2281435 2282703 := bstep (se 1 (by rfl) ⟨1712027, by rfl⟩ : syracuseStep 2282703 = 3424055) B3424055
theorem B3424061 : Blo 2281435 3424061 := bbase (se 3 (by rfl) ⟨642011, by rfl⟩ : syracuseStep 3424061 = 1284023) (by norm_num)
theorem B2282707 : Blo 2281435 2282707 := bstep (se 1 (by rfl) ⟨1712030, by rfl⟩ : syracuseStep 2282707 = 3424061) B3424061
theorem B5136101 : Blo 2281435 5136101 := bbase (se 4 (by rfl) ⟨481509, by rfl⟩ : syracuseStep 5136101 = 963019) (by norm_num)
theorem B3424067 : Blo 2281435 3424067 := bstep (se 1 (by rfl) ⟨2568050, by rfl⟩ : syracuseStep 3424067 = 5136101) B5136101
theorem B2282711 : Blo 2281435 2282711 := bstep (se 1 (by rfl) ⟨1712033, by rfl⟩ : syracuseStep 2282711 = 3424067) B3424067
theorem B5778125 : Blo 2281435 5778125 := bbase (se 3 (by rfl) ⟨1083398, by rfl⟩ : syracuseStep 5778125 = 2166797) (by norm_num)
theorem B3852083 : Blo 2281435 3852083 := bstep (se 1 (by rfl) ⟨2889062, by rfl⟩ : syracuseStep 3852083 = 5778125) B5778125
theorem B2568055 : Blo 2281435 2568055 := bstep (se 1 (by rfl) ⟨1926041, by rfl⟩ : syracuseStep 2568055 = 3852083) B3852083
theorem B3424073 : Blo 2281435 3424073 := bstep (se 2 (by rfl) ⟨1284027, by rfl⟩ : syracuseStep 3424073 = 2568055) B2568055
theorem B2282715 : Blo 2281435 2282715 := bstep (se 1 (by rfl) ⟨1712036, by rfl⟩ : syracuseStep 2282715 = 3424073) B3424073
theorem B3656477 : Blo 2281435 3656477 := bbase (se 3 (by rfl) ⟨685589, by rfl⟩ : syracuseStep 3656477 = 1371179) (by norm_num)
theorem B2437651 : Blo 2281435 2437651 := bstep (se 1 (by rfl) ⟨1828238, by rfl⟩ : syracuseStep 2437651 = 3656477) B3656477
theorem B3250201 : Blo 2281435 3250201 := bstep (se 2 (by rfl) ⟨1218825, by rfl⟩ : syracuseStep 3250201 = 2437651) B2437651
theorem B4333601 : Blo 2281435 4333601 := bstep (se 2 (by rfl) ⟨1625100, by rfl⟩ : syracuseStep 4333601 = 3250201) B3250201
theorem B11556269 : Blo 2281435 11556269 := bstep (se 3 (by rfl) ⟨2166800, by rfl⟩ : syracuseStep 11556269 = 4333601) B4333601
theorem B7704179 : Blo 2281435 7704179 := bstep (se 1 (by rfl) ⟨5778134, by rfl⟩ : syracuseStep 7704179 = 11556269) B11556269
theorem B5136119 : Blo 2281435 5136119 := bstep (se 1 (by rfl) ⟨3852089, by rfl⟩ : syracuseStep 5136119 = 7704179) B7704179
theorem B3424079 : Blo 2281435 3424079 := bstep (se 1 (by rfl) ⟨2568059, by rfl⟩ : syracuseStep 3424079 = 5136119) B5136119
theorem B2282719 : Blo 2281435 2282719 := bstep (se 1 (by rfl) ⟨1712039, by rfl⟩ : syracuseStep 2282719 = 3424079) B3424079
theorem B3424085 : Blo 2281435 3424085 := bbase (se 9 (by rfl) ⟨10031, by rfl⟩ : syracuseStep 3424085 = 20063) (by norm_num)
theorem B2282723 : Blo 2281435 2282723 := bstep (se 1 (by rfl) ⟨1712042, by rfl⟩ : syracuseStep 2282723 = 3424085) B3424085
theorem B3904661 : Blo 2281435 3904661 := bbase (se 6 (by rfl) ⟨91515, by rfl⟩ : syracuseStep 3904661 = 183031) (by norm_num)
theorem B2603107 : Blo 2281435 2603107 := bstep (se 1 (by rfl) ⟨1952330, by rfl⟩ : syracuseStep 2603107 = 3904661) B3904661
theorem B13883237 : Blo 2281435 13883237 := bstep (se 4 (by rfl) ⟨1301553, by rfl⟩ : syracuseStep 13883237 = 2603107) B2603107
theorem B9255491 : Blo 2281435 9255491 := bstep (se 1 (by rfl) ⟨6941618, by rfl⟩ : syracuseStep 9255491 = 13883237) B13883237
theorem B6170327 : Blo 2281435 6170327 := bstep (se 1 (by rfl) ⟨4627745, by rfl⟩ : syracuseStep 6170327 = 9255491) B9255491
theorem B4113551 : Blo 2281435 4113551 := bstep (se 1 (by rfl) ⟨3085163, by rfl⟩ : syracuseStep 4113551 = 6170327) B6170327
theorem B10969469 : Blo 2281435 10969469 := bstep (se 3 (by rfl) ⟨2056775, by rfl⟩ : syracuseStep 10969469 = 4113551) B4113551
theorem B7312979 : Blo 2281435 7312979 := bstep (se 1 (by rfl) ⟨5484734, by rfl⟩ : syracuseStep 7312979 = 10969469) B10969469
theorem B4875319 : Blo 2281435 4875319 := bstep (se 1 (by rfl) ⟨3656489, by rfl⟩ : syracuseStep 4875319 = 7312979) B7312979
theorem B6500425 : Blo 2281435 6500425 := bstep (se 2 (by rfl) ⟨2437659, by rfl⟩ : syracuseStep 6500425 = 4875319) B4875319
theorem B8667233 : Blo 2281435 8667233 := bstep (se 2 (by rfl) ⟨3250212, by rfl⟩ : syracuseStep 8667233 = 6500425) B6500425
theorem B5778155 : Blo 2281435 5778155 := bstep (se 1 (by rfl) ⟨4333616, by rfl⟩ : syracuseStep 5778155 = 8667233) B8667233
theorem B3852103 : Blo 2281435 3852103 := bstep (se 1 (by rfl) ⟨2889077, by rfl⟩ : syracuseStep 3852103 = 5778155) B5778155
theorem B5136137 : Blo 2281435 5136137 := bstep (se 2 (by rfl) ⟨1926051, by rfl⟩ : syracuseStep 5136137 = 3852103) B3852103
theorem B3424091 : Blo 2281435 3424091 := bstep (se 1 (by rfl) ⟨2568068, by rfl⟩ : syracuseStep 3424091 = 5136137) B5136137
theorem B2282727 : Blo 2281435 2282727 := bstep (se 1 (by rfl) ⟨1712045, by rfl⟩ : syracuseStep 2282727 = 3424091) B3424091
theorem B2568073 : Blo 2281435 2568073 := bbase (se 2 (by rfl) ⟨963027, by rfl⟩ : syracuseStep 2568073 = 1926055) (by norm_num)
theorem B3424097 : Blo 2281435 3424097 := bstep (se 2 (by rfl) ⟨1284036, by rfl⟩ : syracuseStep 3424097 = 2568073) B2568073
theorem B2282731 : Blo 2281435 2282731 := bstep (se 1 (by rfl) ⟨1712048, by rfl⟩ : syracuseStep 2282731 = 3424097) B3424097
theorem B2928505 : Blo 2281435 2928505 := bbase (se 2 (by rfl) ⟨1098189, by rfl⟩ : syracuseStep 2928505 = 2196379) (by norm_num)
theorem B3904673 : Blo 2281435 3904673 := bstep (se 2 (by rfl) ⟨1464252, by rfl⟩ : syracuseStep 3904673 = 2928505) B2928505
theorem B10412461 : Blo 2281435 10412461 := bstep (se 3 (by rfl) ⟨1952336, by rfl⟩ : syracuseStep 10412461 = 3904673) B3904673
theorem B13883281 : Blo 2281435 13883281 := bstep (se 2 (by rfl) ⟨5206230, by rfl⟩ : syracuseStep 13883281 = 10412461) B10412461
theorem B74044165 : Blo 2281435 74044165 := bstep (se 4 (by rfl) ⟨6941640, by rfl⟩ : syracuseStep 74044165 = 13883281) B13883281
theorem B98725553 : Blo 2281435 98725553 := bstep (se 2 (by rfl) ⟨37022082, by rfl⟩ : syracuseStep 98725553 = 74044165) B74044165
theorem B65817035 : Blo 2281435 65817035 := bstep (se 1 (by rfl) ⟨49362776, by rfl⟩ : syracuseStep 65817035 = 98725553) B98725553
theorem B43878023 : Blo 2281435 43878023 := bstep (se 1 (by rfl) ⟨32908517, by rfl⟩ : syracuseStep 43878023 = 65817035) B65817035
theorem B29252015 : Blo 2281435 29252015 := bstep (se 1 (by rfl) ⟨21939011, by rfl⟩ : syracuseStep 29252015 = 43878023) B43878023
theorem B19501343 : Blo 2281435 19501343 := bstep (se 1 (by rfl) ⟨14626007, by rfl⟩ : syracuseStep 19501343 = 29252015) B29252015
theorem B13000895 : Blo 2281435 13000895 := bstep (se 1 (by rfl) ⟨9750671, by rfl⟩ : syracuseStep 13000895 = 19501343) B19501343
theorem B8667263 : Blo 2281435 8667263 := bstep (se 1 (by rfl) ⟨6500447, by rfl⟩ : syracuseStep 8667263 = 13000895) B13000895
theorem B5778175 : Blo 2281435 5778175 := bstep (se 1 (by rfl) ⟨4333631, by rfl⟩ : syracuseStep 5778175 = 8667263) B8667263
theorem B7704233 : Blo 2281435 7704233 := bstep (se 2 (by rfl) ⟨2889087, by rfl⟩ : syracuseStep 7704233 = 5778175) B5778175
theorem B5136155 : Blo 2281435 5136155 := bstep (se 1 (by rfl) ⟨3852116, by rfl⟩ : syracuseStep 5136155 = 7704233) B7704233
theorem B3424103 : Blo 2281435 3424103 := bstep (se 1 (by rfl) ⟨2568077, by rfl⟩ : syracuseStep 3424103 = 5136155) B5136155
theorem B2282735 : Blo 2281435 2282735 := bstep (se 1 (by rfl) ⟨1712051, by rfl⟩ : syracuseStep 2282735 = 3424103) B3424103
theorem B3424109 : Blo 2281435 3424109 := bbase (se 3 (by rfl) ⟨642020, by rfl⟩ : syracuseStep 3424109 = 1284041) (by norm_num)
theorem B2282739 : Blo 2281435 2282739 := bstep (se 1 (by rfl) ⟨1712054, by rfl⟩ : syracuseStep 2282739 = 3424109) B3424109
theorem B5136173 : Blo 2281435 5136173 := bbase (se 3 (by rfl) ⟨963032, by rfl⟩ : syracuseStep 5136173 = 1926065) (by norm_num)
theorem B3424115 : Blo 2281435 3424115 := bstep (se 1 (by rfl) ⟨2568086, by rfl⟩ : syracuseStep 3424115 = 5136173) B5136173
theorem B2282743 : Blo 2281435 2282743 := bstep (se 1 (by rfl) ⟨1712057, by rfl⟩ : syracuseStep 2282743 = 3424115) B3424115
theorem B9750725 : Blo 2281435 9750725 := bbase (se 4 (by rfl) ⟨914130, by rfl⟩ : syracuseStep 9750725 = 1828261) (by norm_num)
theorem B6500483 : Blo 2281435 6500483 := bstep (se 1 (by rfl) ⟨4875362, by rfl⟩ : syracuseStep 6500483 = 9750725) B9750725
theorem B4333655 : Blo 2281435 4333655 := bstep (se 1 (by rfl) ⟨3250241, by rfl⟩ : syracuseStep 4333655 = 6500483) B6500483
theorem B2889103 : Blo 2281435 2889103 := bstep (se 1 (by rfl) ⟨2166827, by rfl⟩ : syracuseStep 2889103 = 4333655) B4333655
theorem B3852137 : Blo 2281435 3852137 := bstep (se 2 (by rfl) ⟨1444551, by rfl⟩ : syracuseStep 3852137 = 2889103) B2889103
theorem B2568091 : Blo 2281435 2568091 := bstep (se 1 (by rfl) ⟨1926068, by rfl⟩ : syracuseStep 2568091 = 3852137) B3852137
theorem B3424121 : Blo 2281435 3424121 := bstep (se 2 (by rfl) ⟨1284045, by rfl⟩ : syracuseStep 3424121 = 2568091) B2568091
theorem B2282747 : Blo 2281435 2282747 := bstep (se 1 (by rfl) ⟨1712060, by rfl⟩ : syracuseStep 2282747 = 3424121) B3424121
theorem B3470845 : Blo 2281435 3470845 := bbase (se 3 (by rfl) ⟨650783, by rfl⟩ : syracuseStep 3470845 = 1301567) (by norm_num)
theorem B4627793 : Blo 2281435 4627793 := bstep (se 2 (by rfl) ⟨1735422, by rfl⟩ : syracuseStep 4627793 = 3470845) B3470845
theorem B12340781 : Blo 2281435 12340781 := bstep (se 3 (by rfl) ⟨2313896, by rfl⟩ : syracuseStep 12340781 = 4627793) B4627793
theorem B8227187 : Blo 2281435 8227187 := bstep (se 1 (by rfl) ⟨6170390, by rfl⟩ : syracuseStep 8227187 = 12340781) B12340781
theorem B5484791 : Blo 2281435 5484791 := bstep (se 1 (by rfl) ⟨4113593, by rfl⟩ : syracuseStep 5484791 = 8227187) B8227187
theorem B14626109 : Blo 2281435 14626109 := bstep (se 3 (by rfl) ⟨2742395, by rfl⟩ : syracuseStep 14626109 = 5484791) B5484791
theorem B39002957 : Blo 2281435 39002957 := bstep (se 3 (by rfl) ⟨7313054, by rfl⟩ : syracuseStep 39002957 = 14626109) B14626109
theorem B26001971 : Blo 2281435 26001971 := bstep (se 1 (by rfl) ⟨19501478, by rfl⟩ : syracuseStep 26001971 = 39002957) B39002957
theorem B17334647 : Blo 2281435 17334647 := bstep (se 1 (by rfl) ⟨13000985, by rfl⟩ : syracuseStep 17334647 = 26001971) B26001971
theorem B11556431 : Blo 2281435 11556431 := bstep (se 1 (by rfl) ⟨8667323, by rfl⟩ : syracuseStep 11556431 = 17334647) B17334647
theorem B7704287 : Blo 2281435 7704287 := bstep (se 1 (by rfl) ⟨5778215, by rfl⟩ : syracuseStep 7704287 = 11556431) B11556431
theorem B5136191 : Blo 2281435 5136191 := bstep (se 1 (by rfl) ⟨3852143, by rfl⟩ : syracuseStep 5136191 = 7704287) B7704287
theorem B3424127 : Blo 2281435 3424127 := bstep (se 1 (by rfl) ⟨2568095, by rfl⟩ : syracuseStep 3424127 = 5136191) B5136191
theorem B2282751 : Blo 2281435 2282751 := bstep (se 1 (by rfl) ⟨1712063, by rfl⟩ : syracuseStep 2282751 = 3424127) B3424127
theorem B3424133 : Blo 2281435 3424133 := bbase (se 4 (by rfl) ⟨321012, by rfl⟩ : syracuseStep 3424133 = 642025) (by norm_num)
theorem B2282755 : Blo 2281435 2282755 := bstep (se 1 (by rfl) ⟨1712066, by rfl⟩ : syracuseStep 2282755 = 3424133) B3424133
theorem B3852157 : Blo 2281435 3852157 := bbase (se 3 (by rfl) ⟨722279, by rfl⟩ : syracuseStep 3852157 = 1444559) (by norm_num)
theorem B5136209 : Blo 2281435 5136209 := bstep (se 2 (by rfl) ⟨1926078, by rfl⟩ : syracuseStep 5136209 = 3852157) B3852157
theorem B3424139 : Blo 2281435 3424139 := bstep (se 1 (by rfl) ⟨2568104, by rfl⟩ : syracuseStep 3424139 = 5136209) B5136209
theorem B2282759 : Blo 2281435 2282759 := bstep (se 1 (by rfl) ⟨1712069, by rfl⟩ : syracuseStep 2282759 = 3424139) B3424139
theorem B2568109 : Blo 2281435 2568109 := bbase (se 3 (by rfl) ⟨481520, by rfl⟩ : syracuseStep 2568109 = 963041) (by norm_num)
theorem B3424145 : Blo 2281435 3424145 := bstep (se 2 (by rfl) ⟨1284054, by rfl⟩ : syracuseStep 3424145 = 2568109) B2568109
theorem B2282763 : Blo 2281435 2282763 := bstep (se 1 (by rfl) ⟨1712072, by rfl⟩ : syracuseStep 2282763 = 3424145) B3424145
theorem B7704341 : Blo 2281435 7704341 := bbase (se 6 (by rfl) ⟨180570, by rfl⟩ : syracuseStep 7704341 = 361141) (by norm_num)
theorem B5136227 : Blo 2281435 5136227 := bstep (se 1 (by rfl) ⟨3852170, by rfl⟩ : syracuseStep 5136227 = 7704341) B7704341
theorem B3424151 : Blo 2281435 3424151 := bstep (se 1 (by rfl) ⟨2568113, by rfl⟩ : syracuseStep 3424151 = 5136227) B5136227
theorem B2282767 : Blo 2281435 2282767 := bstep (se 1 (by rfl) ⟨1712075, by rfl⟩ : syracuseStep 2282767 = 3424151) B3424151
theorem B3424157 : Blo 2281435 3424157 := bbase (se 3 (by rfl) ⟨642029, by rfl⟩ : syracuseStep 3424157 = 1284059) (by norm_num)
theorem B2282771 : Blo 2281435 2282771 := bstep (se 1 (by rfl) ⟨1712078, by rfl⟩ : syracuseStep 2282771 = 3424157) B3424157
theorem B5136245 : Blo 2281435 5136245 := bbase (se 5 (by rfl) ⟨240761, by rfl⟩ : syracuseStep 5136245 = 481523) (by norm_num)
theorem B3424163 : Blo 2281435 3424163 := bstep (se 1 (by rfl) ⟨2568122, by rfl⟩ : syracuseStep 3424163 = 5136245) B5136245
theorem B2282775 : Blo 2281435 2282775 := bstep (se 1 (by rfl) ⟨1712081, by rfl⟩ : syracuseStep 2282775 = 3424163) B3424163
theorem B9255701 : Blo 2281435 9255701 := bbase (se 6 (by rfl) ⟨216930, by rfl⟩ : syracuseStep 9255701 = 433861) (by norm_num)
theorem B6170467 : Blo 2281435 6170467 := bstep (se 1 (by rfl) ⟨4627850, by rfl⟩ : syracuseStep 6170467 = 9255701) B9255701
theorem B8227289 : Blo 2281435 8227289 := bstep (se 2 (by rfl) ⟨3085233, by rfl⟩ : syracuseStep 8227289 = 6170467) B6170467
theorem B21939437 : Blo 2281435 21939437 := bstep (se 3 (by rfl) ⟨4113644, by rfl⟩ : syracuseStep 21939437 = 8227289) B8227289
theorem B14626291 : Blo 2281435 14626291 := bstep (se 1 (by rfl) ⟨10969718, by rfl⟩ : syracuseStep 14626291 = 21939437) B21939437
theorem B19501721 : Blo 2281435 19501721 := bstep (se 2 (by rfl) ⟨7313145, by rfl⟩ : syracuseStep 19501721 = 14626291) B14626291
theorem B13001147 : Blo 2281435 13001147 := bstep (se 1 (by rfl) ⟨9750860, by rfl⟩ : syracuseStep 13001147 = 19501721) B19501721
theorem B8667431 : Blo 2281435 8667431 := bstep (se 1 (by rfl) ⟨6500573, by rfl⟩ : syracuseStep 8667431 = 13001147) B13001147
theorem B5778287 : Blo 2281435 5778287 := bstep (se 1 (by rfl) ⟨4333715, by rfl⟩ : syracuseStep 5778287 = 8667431) B8667431
theorem B3852191 : Blo 2281435 3852191 := bstep (se 1 (by rfl) ⟨2889143, by rfl⟩ : syracuseStep 3852191 = 5778287) B5778287
theorem B2568127 : Blo 2281435 2568127 := bstep (se 1 (by rfl) ⟨1926095, by rfl⟩ : syracuseStep 2568127 = 3852191) B3852191
theorem B3424169 : Blo 2281435 3424169 := bstep (se 2 (by rfl) ⟨1284063, by rfl⟩ : syracuseStep 3424169 = 2568127) B2568127
theorem B2282779 : Blo 2281435 2282779 := bstep (se 1 (by rfl) ⟨1712084, by rfl⟩ : syracuseStep 2282779 = 3424169) B3424169
theorem B8667445 : Blo 2281435 8667445 := bbase (se 5 (by rfl) ⟨406286, by rfl⟩ : syracuseStep 8667445 = 812573) (by norm_num)
theorem B11556593 : Blo 2281435 11556593 := bstep (se 2 (by rfl) ⟨4333722, by rfl⟩ : syracuseStep 11556593 = 8667445) B8667445
theorem B7704395 : Blo 2281435 7704395 := bstep (se 1 (by rfl) ⟨5778296, by rfl⟩ : syracuseStep 7704395 = 11556593) B11556593
theorem B5136263 : Blo 2281435 5136263 := bstep (se 1 (by rfl) ⟨3852197, by rfl⟩ : syracuseStep 5136263 = 7704395) B7704395
theorem B3424175 : Blo 2281435 3424175 := bstep (se 1 (by rfl) ⟨2568131, by rfl⟩ : syracuseStep 3424175 = 5136263) B5136263
theorem B2282783 : Blo 2281435 2282783 := bstep (se 1 (by rfl) ⟨1712087, by rfl⟩ : syracuseStep 2282783 = 3424175) B3424175
theorem B3424181 : Blo 2281435 3424181 := bbase (se 5 (by rfl) ⟨160508, by rfl⟩ : syracuseStep 3424181 = 321017) (by norm_num)
theorem B2282787 : Blo 2281435 2282787 := bstep (se 1 (by rfl) ⟨1712090, by rfl⟩ : syracuseStep 2282787 = 3424181) B3424181
theorem B5778317 : Blo 2281435 5778317 := bbase (se 3 (by rfl) ⟨1083434, by rfl⟩ : syracuseStep 5778317 = 2166869) (by norm_num)
theorem B3852211 : Blo 2281435 3852211 := bstep (se 1 (by rfl) ⟨2889158, by rfl⟩ : syracuseStep 3852211 = 5778317) B5778317
theorem B5136281 : Blo 2281435 5136281 := bstep (se 2 (by rfl) ⟨1926105, by rfl⟩ : syracuseStep 5136281 = 3852211) B3852211
theorem B3424187 : Blo 2281435 3424187 := bstep (se 1 (by rfl) ⟨2568140, by rfl⟩ : syracuseStep 3424187 = 5136281) B5136281
theorem B2282791 : Blo 2281435 2282791 := bstep (se 1 (by rfl) ⟨1712093, by rfl⟩ : syracuseStep 2282791 = 3424187) B3424187
theorem B2568145 : Blo 2281435 2568145 := bbase (se 2 (by rfl) ⟨963054, by rfl⟩ : syracuseStep 2568145 = 1926109) (by norm_num)
theorem B3424193 : Blo 2281435 3424193 := bstep (se 2 (by rfl) ⟨1284072, by rfl⟩ : syracuseStep 3424193 = 2568145) B2568145
theorem B2282795 : Blo 2281435 2282795 := bstep (se 1 (by rfl) ⟨1712096, by rfl⟩ : syracuseStep 2282795 = 3424193) B3424193
theorem B3656605 : Blo 2281435 3656605 := bbase (se 3 (by rfl) ⟨685613, by rfl⟩ : syracuseStep 3656605 = 1371227) (by norm_num)
theorem B4875473 : Blo 2281435 4875473 := bstep (se 2 (by rfl) ⟨1828302, by rfl⟩ : syracuseStep 4875473 = 3656605) B3656605
theorem B3250315 : Blo 2281435 3250315 := bstep (se 1 (by rfl) ⟨2437736, by rfl⟩ : syracuseStep 3250315 = 4875473) B4875473
theorem B4333753 : Blo 2281435 4333753 := bstep (se 2 (by rfl) ⟨1625157, by rfl⟩ : syracuseStep 4333753 = 3250315) B3250315
theorem B5778337 : Blo 2281435 5778337 := bstep (se 2 (by rfl) ⟨2166876, by rfl⟩ : syracuseStep 5778337 = 4333753) B4333753
theorem B7704449 : Blo 2281435 7704449 := bstep (se 2 (by rfl) ⟨2889168, by rfl⟩ : syracuseStep 7704449 = 5778337) B5778337
theorem B5136299 : Blo 2281435 5136299 := bstep (se 1 (by rfl) ⟨3852224, by rfl⟩ : syracuseStep 5136299 = 7704449) B7704449
theorem B3424199 : Blo 2281435 3424199 := bstep (se 1 (by rfl) ⟨2568149, by rfl⟩ : syracuseStep 3424199 = 5136299) B5136299
theorem B2282799 : Blo 2281435 2282799 := bstep (se 1 (by rfl) ⟨1712099, by rfl⟩ : syracuseStep 2282799 = 3424199) B3424199
theorem B3424205 : Blo 2281435 3424205 := bbase (se 3 (by rfl) ⟨642038, by rfl⟩ : syracuseStep 3424205 = 1284077) (by norm_num)
theorem B2282803 : Blo 2281435 2282803 := bstep (se 1 (by rfl) ⟨1712102, by rfl⟩ : syracuseStep 2282803 = 3424205) B3424205
theorem B5136317 : Blo 2281435 5136317 := bbase (se 3 (by rfl) ⟨963059, by rfl⟩ : syracuseStep 5136317 = 1926119) (by norm_num)
theorem B3424211 : Blo 2281435 3424211 := bstep (se 1 (by rfl) ⟨2568158, by rfl⟩ : syracuseStep 3424211 = 5136317) B5136317
theorem B2282807 : Blo 2281435 2282807 := bstep (se 1 (by rfl) ⟨1712105, by rfl⟩ : syracuseStep 2282807 = 3424211) B3424211
theorem B3852245 : Blo 2281435 3852245 := bbase (se 7 (by rfl) ⟨45143, by rfl⟩ : syracuseStep 3852245 = 90287) (by norm_num)
theorem B2568163 : Blo 2281435 2568163 := bstep (se 1 (by rfl) ⟨1926122, by rfl⟩ : syracuseStep 2568163 = 3852245) B3852245
theorem B3424217 : Blo 2281435 3424217 := bstep (se 2 (by rfl) ⟨1284081, by rfl⟩ : syracuseStep 3424217 = 2568163) B2568163
theorem B2282811 : Blo 2281435 2282811 := bstep (se 1 (by rfl) ⟨1712108, by rfl⟩ : syracuseStep 2282811 = 3424217) B3424217
theorem B9751013 : Blo 2281435 9751013 := bbase (se 4 (by rfl) ⟨914157, by rfl⟩ : syracuseStep 9751013 = 1828315) (by norm_num)
theorem B6500675 : Blo 2281435 6500675 := bstep (se 1 (by rfl) ⟨4875506, by rfl⟩ : syracuseStep 6500675 = 9751013) B9751013
theorem B17335133 : Blo 2281435 17335133 := bstep (se 3 (by rfl) ⟨3250337, by rfl⟩ : syracuseStep 17335133 = 6500675) B6500675
theorem B11556755 : Blo 2281435 11556755 := bstep (se 1 (by rfl) ⟨8667566, by rfl⟩ : syracuseStep 11556755 = 17335133) B17335133
theorem B7704503 : Blo 2281435 7704503 := bstep (se 1 (by rfl) ⟨5778377, by rfl⟩ : syracuseStep 7704503 = 11556755) B11556755
theorem B5136335 : Blo 2281435 5136335 := bstep (se 1 (by rfl) ⟨3852251, by rfl⟩ : syracuseStep 5136335 = 7704503) B7704503
theorem B3424223 : Blo 2281435 3424223 := bstep (se 1 (by rfl) ⟨2568167, by rfl⟩ : syracuseStep 3424223 = 5136335) B5136335
theorem B2282815 : Blo 2281435 2282815 := bstep (se 1 (by rfl) ⟨1712111, by rfl⟩ : syracuseStep 2282815 = 3424223) B3424223
theorem B3424229 : Blo 2281435 3424229 := bbase (se 4 (by rfl) ⟨321021, by rfl⟩ : syracuseStep 3424229 = 642043) (by norm_num)
theorem B2282819 : Blo 2281435 2282819 := bstep (se 1 (by rfl) ⟨1712114, by rfl⟩ : syracuseStep 2282819 = 3424229) B3424229
theorem B12341173 : Blo 2281435 12341173 := bbase (se 5 (by rfl) ⟨578492, by rfl⟩ : syracuseStep 12341173 = 1156985) (by norm_num)
theorem B16454897 : Blo 2281435 16454897 := bstep (se 2 (by rfl) ⟨6170586, by rfl⟩ : syracuseStep 16454897 = 12341173) B12341173
theorem B10969931 : Blo 2281435 10969931 := bstep (se 1 (by rfl) ⟨8227448, by rfl⟩ : syracuseStep 10969931 = 16454897) B16454897
theorem B7313287 : Blo 2281435 7313287 := bstep (se 1 (by rfl) ⟨5484965, by rfl⟩ : syracuseStep 7313287 = 10969931) B10969931
theorem B9751049 : Blo 2281435 9751049 := bstep (se 2 (by rfl) ⟨3656643, by rfl⟩ : syracuseStep 9751049 = 7313287) B7313287
theorem B6500699 : Blo 2281435 6500699 := bstep (se 1 (by rfl) ⟨4875524, by rfl⟩ : syracuseStep 6500699 = 9751049) B9751049
theorem B4333799 : Blo 2281435 4333799 := bstep (se 1 (by rfl) ⟨3250349, by rfl⟩ : syracuseStep 4333799 = 6500699) B6500699
theorem B2889199 : Blo 2281435 2889199 := bstep (se 1 (by rfl) ⟨2166899, by rfl⟩ : syracuseStep 2889199 = 4333799) B4333799
theorem B3852265 : Blo 2281435 3852265 := bstep (se 2 (by rfl) ⟨1444599, by rfl⟩ : syracuseStep 3852265 = 2889199) B2889199
theorem B5136353 : Blo 2281435 5136353 := bstep (se 2 (by rfl) ⟨1926132, by rfl⟩ : syracuseStep 5136353 = 3852265) B3852265
theorem B3424235 : Blo 2281435 3424235 := bstep (se 1 (by rfl) ⟨2568176, by rfl⟩ : syracuseStep 3424235 = 5136353) B5136353
theorem B2282823 : Blo 2281435 2282823 := bstep (se 1 (by rfl) ⟨1712117, by rfl⟩ : syracuseStep 2282823 = 3424235) B3424235
theorem B2568181 : Blo 2281435 2568181 := bbase (se 5 (by rfl) ⟨120383, by rfl⟩ : syracuseStep 2568181 = 240767) (by norm_num)
theorem B3424241 : Blo 2281435 3424241 := bstep (se 2 (by rfl) ⟨1284090, by rfl⟩ : syracuseStep 3424241 = 2568181) B2568181
theorem B2282827 : Blo 2281435 2282827 := bstep (se 1 (by rfl) ⟨1712120, by rfl⟩ : syracuseStep 2282827 = 3424241) B3424241
theorem B2889209 : Blo 2281435 2889209 := bbase (se 2 (by rfl) ⟨1083453, by rfl⟩ : syracuseStep 2889209 = 2166907) (by norm_num)
theorem B7704557 : Blo 2281435 7704557 := bstep (se 3 (by rfl) ⟨1444604, by rfl⟩ : syracuseStep 7704557 = 2889209) B2889209
theorem B5136371 : Blo 2281435 5136371 := bstep (se 1 (by rfl) ⟨3852278, by rfl⟩ : syracuseStep 5136371 = 7704557) B7704557
theorem B3424247 : Blo 2281435 3424247 := bstep (se 1 (by rfl) ⟨2568185, by rfl⟩ : syracuseStep 3424247 = 5136371) B5136371
theorem B2282831 : Blo 2281435 2282831 := bstep (se 1 (by rfl) ⟨1712123, by rfl⟩ : syracuseStep 2282831 = 3424247) B3424247
theorem B3424253 : Blo 2281435 3424253 := bbase (se 3 (by rfl) ⟨642047, by rfl⟩ : syracuseStep 3424253 = 1284095) (by norm_num)
theorem B2282835 : Blo 2281435 2282835 := bstep (se 1 (by rfl) ⟨1712126, by rfl⟩ : syracuseStep 2282835 = 3424253) B3424253
theorem B5136389 : Blo 2281435 5136389 := bbase (se 4 (by rfl) ⟨481536, by rfl⟩ : syracuseStep 5136389 = 963073) (by norm_num)
theorem B3424259 : Blo 2281435 3424259 := bstep (se 1 (by rfl) ⟨2568194, by rfl⟩ : syracuseStep 3424259 = 5136389) B5136389
theorem B2282839 : Blo 2281435 2282839 := bstep (se 1 (by rfl) ⟨1712129, by rfl⟩ : syracuseStep 2282839 = 3424259) B3424259
theorem B4333837 : Blo 2281435 4333837 := bbase (se 3 (by rfl) ⟨812594, by rfl⟩ : syracuseStep 4333837 = 1625189) (by norm_num)
theorem B5778449 : Blo 2281435 5778449 := bstep (se 2 (by rfl) ⟨2166918, by rfl⟩ : syracuseStep 5778449 = 4333837) B4333837
theorem B3852299 : Blo 2281435 3852299 := bstep (se 1 (by rfl) ⟨2889224, by rfl⟩ : syracuseStep 3852299 = 5778449) B5778449
theorem B2568199 : Blo 2281435 2568199 := bstep (se 1 (by rfl) ⟨1926149, by rfl⟩ : syracuseStep 2568199 = 3852299) B3852299
theorem B3424265 : Blo 2281435 3424265 := bstep (se 2 (by rfl) ⟨1284099, by rfl⟩ : syracuseStep 3424265 = 2568199) B2568199
theorem B2282843 : Blo 2281435 2282843 := bstep (se 1 (by rfl) ⟨1712132, by rfl⟩ : syracuseStep 2282843 = 3424265) B3424265
theorem B11556917 : Blo 2281435 11556917 := bbase (se 5 (by rfl) ⟨541730, by rfl⟩ : syracuseStep 11556917 = 1083461) (by norm_num)
theorem B7704611 : Blo 2281435 7704611 := bstep (se 1 (by rfl) ⟨5778458, by rfl⟩ : syracuseStep 7704611 = 11556917) B11556917
theorem B5136407 : Blo 2281435 5136407 := bstep (se 1 (by rfl) ⟨3852305, by rfl⟩ : syracuseStep 5136407 = 7704611) B7704611
theorem B3424271 : Blo 2281435 3424271 := bstep (se 1 (by rfl) ⟨2568203, by rfl⟩ : syracuseStep 3424271 = 5136407) B5136407
theorem B2282847 : Blo 2281435 2282847 := bstep (se 1 (by rfl) ⟨1712135, by rfl⟩ : syracuseStep 2282847 = 3424271) B3424271
theorem B3424277 : Blo 2281435 3424277 := bbase (se 6 (by rfl) ⟨80256, by rfl⟩ : syracuseStep 3424277 = 160513) (by norm_num)
theorem B2282851 : Blo 2281435 2282851 := bstep (se 1 (by rfl) ⟨1712138, by rfl⟩ : syracuseStep 2282851 = 3424277) B3424277
theorem B16455125 : Blo 2281435 16455125 := bbase (se 7 (by rfl) ⟨192833, by rfl⟩ : syracuseStep 16455125 = 385667) (by norm_num)
theorem B10970083 : Blo 2281435 10970083 := bstep (se 1 (by rfl) ⟨8227562, by rfl⟩ : syracuseStep 10970083 = 16455125) B16455125
theorem B14626777 : Blo 2281435 14626777 := bstep (se 2 (by rfl) ⟨5485041, by rfl⟩ : syracuseStep 14626777 = 10970083) B10970083
theorem B19502369 : Blo 2281435 19502369 := bstep (se 2 (by rfl) ⟨7313388, by rfl⟩ : syracuseStep 19502369 = 14626777) B14626777
theorem B13001579 : Blo 2281435 13001579 := bstep (se 1 (by rfl) ⟨9751184, by rfl⟩ : syracuseStep 13001579 = 19502369) B19502369
theorem B8667719 : Blo 2281435 8667719 := bstep (se 1 (by rfl) ⟨6500789, by rfl⟩ : syracuseStep 8667719 = 13001579) B13001579
theorem B5778479 : Blo 2281435 5778479 := bstep (se 1 (by rfl) ⟨4333859, by rfl⟩ : syracuseStep 5778479 = 8667719) B8667719
theorem B3852319 : Blo 2281435 3852319 := bstep (se 1 (by rfl) ⟨2889239, by rfl⟩ : syracuseStep 3852319 = 5778479) B5778479
theorem B5136425 : Blo 2281435 5136425 := bstep (se 2 (by rfl) ⟨1926159, by rfl⟩ : syracuseStep 5136425 = 3852319) B3852319
theorem B3424283 : Blo 2281435 3424283 := bstep (se 1 (by rfl) ⟨2568212, by rfl⟩ : syracuseStep 3424283 = 5136425) B5136425
theorem B2282855 : Blo 2281435 2282855 := bstep (se 1 (by rfl) ⟨1712141, by rfl⟩ : syracuseStep 2282855 = 3424283) B3424283
theorem B2568217 : Blo 2281435 2568217 := bbase (se 2 (by rfl) ⟨963081, by rfl⟩ : syracuseStep 2568217 = 1926163) (by norm_num)
theorem B3424289 : Blo 2281435 3424289 := bstep (se 2 (by rfl) ⟨1284108, by rfl⟩ : syracuseStep 3424289 = 2568217) B2568217
theorem B2282859 : Blo 2281435 2282859 := bstep (se 1 (by rfl) ⟨1712144, by rfl⟩ : syracuseStep 2282859 = 3424289) B3424289
theorem B8667749 : Blo 2281435 8667749 := bbase (se 4 (by rfl) ⟨812601, by rfl⟩ : syracuseStep 8667749 = 1625203) (by norm_num)
theorem B5778499 : Blo 2281435 5778499 := bstep (se 1 (by rfl) ⟨4333874, by rfl⟩ : syracuseStep 5778499 = 8667749) B8667749
theorem B7704665 : Blo 2281435 7704665 := bstep (se 2 (by rfl) ⟨2889249, by rfl⟩ : syracuseStep 7704665 = 5778499) B5778499
theorem B5136443 : Blo 2281435 5136443 := bstep (se 1 (by rfl) ⟨3852332, by rfl⟩ : syracuseStep 5136443 = 7704665) B7704665
theorem B3424295 : Blo 2281435 3424295 := bstep (se 1 (by rfl) ⟨2568221, by rfl⟩ : syracuseStep 3424295 = 5136443) B5136443
theorem B2282863 : Blo 2281435 2282863 := bstep (se 1 (by rfl) ⟨1712147, by rfl⟩ : syracuseStep 2282863 = 3424295) B3424295
theorem B3424301 : Blo 2281435 3424301 := bbase (se 3 (by rfl) ⟨642056, by rfl⟩ : syracuseStep 3424301 = 1284113) (by norm_num)
theorem B2282867 : Blo 2281435 2282867 := bstep (se 1 (by rfl) ⟨1712150, by rfl⟩ : syracuseStep 2282867 = 3424301) B3424301
theorem B5136461 : Blo 2281435 5136461 := bbase (se 3 (by rfl) ⟨963086, by rfl⟩ : syracuseStep 5136461 = 1926173) (by norm_num)
theorem B3424307 : Blo 2281435 3424307 := bstep (se 1 (by rfl) ⟨2568230, by rfl⟩ : syracuseStep 3424307 = 5136461) B5136461
theorem B2282871 : Blo 2281435 2282871 := bstep (se 1 (by rfl) ⟨1712153, by rfl⟩ : syracuseStep 2282871 = 3424307) B3424307
theorem B2889265 : Blo 2281435 2889265 := bbase (se 2 (by rfl) ⟨1083474, by rfl⟩ : syracuseStep 2889265 = 2166949) (by norm_num)
theorem B3852353 : Blo 2281435 3852353 := bstep (se 2 (by rfl) ⟨1444632, by rfl⟩ : syracuseStep 3852353 = 2889265) B2889265
theorem B2568235 : Blo 2281435 2568235 := bstep (se 1 (by rfl) ⟨1926176, by rfl⟩ : syracuseStep 2568235 = 3852353) B3852353
theorem B3424313 : Blo 2281435 3424313 := bstep (se 2 (by rfl) ⟨1284117, by rfl⟩ : syracuseStep 3424313 = 2568235) B2568235
theorem B2282875 : Blo 2281435 2282875 := bstep (se 1 (by rfl) ⟨1712156, by rfl⟩ : syracuseStep 2282875 = 3424313) B3424313
theorem B4628053 : Blo 2281435 4628053 := bbase (se 8 (by rfl) ⟨27117, by rfl⟩ : syracuseStep 4628053 = 54235) (by norm_num)
theorem B6170737 : Blo 2281435 6170737 := bstep (se 2 (by rfl) ⟨2314026, by rfl⟩ : syracuseStep 6170737 = 4628053) B4628053
theorem B8227649 : Blo 2281435 8227649 := bstep (se 2 (by rfl) ⟨3085368, by rfl⟩ : syracuseStep 8227649 = 6170737) B6170737
theorem B5485099 : Blo 2281435 5485099 := bstep (se 1 (by rfl) ⟨4113824, by rfl⟩ : syracuseStep 5485099 = 8227649) B8227649
theorem B7313465 : Blo 2281435 7313465 := bstep (se 2 (by rfl) ⟨2742549, by rfl⟩ : syracuseStep 7313465 = 5485099) B5485099
theorem B4875643 : Blo 2281435 4875643 := bstep (se 1 (by rfl) ⟨3656732, by rfl⟩ : syracuseStep 4875643 = 7313465) B7313465
theorem B26003429 : Blo 2281435 26003429 := bstep (se 4 (by rfl) ⟨2437821, by rfl⟩ : syracuseStep 26003429 = 4875643) B4875643
theorem B17335619 : Blo 2281435 17335619 := bstep (se 1 (by rfl) ⟨13001714, by rfl⟩ : syracuseStep 17335619 = 26003429) B26003429
theorem B11557079 : Blo 2281435 11557079 := bstep (se 1 (by rfl) ⟨8667809, by rfl⟩ : syracuseStep 11557079 = 17335619) B17335619
theorem B7704719 : Blo 2281435 7704719 := bstep (se 1 (by rfl) ⟨5778539, by rfl⟩ : syracuseStep 7704719 = 11557079) B11557079
theorem B5136479 : Blo 2281435 5136479 := bstep (se 1 (by rfl) ⟨3852359, by rfl⟩ : syracuseStep 5136479 = 7704719) B7704719
theorem B3424319 : Blo 2281435 3424319 := bstep (se 1 (by rfl) ⟨2568239, by rfl⟩ : syracuseStep 3424319 = 5136479) B5136479
theorem B2282879 : Blo 2281435 2282879 := bstep (se 1 (by rfl) ⟨1712159, by rfl⟩ : syracuseStep 2282879 = 3424319) B3424319
theorem B3424325 : Blo 2281435 3424325 := bbase (se 4 (by rfl) ⟨321030, by rfl⟩ : syracuseStep 3424325 = 642061) (by norm_num)
theorem B2282883 : Blo 2281435 2282883 := bstep (se 1 (by rfl) ⟨1712162, by rfl⟩ : syracuseStep 2282883 = 3424325) B3424325
theorem B3852373 : Blo 2281435 3852373 := bbase (se 8 (by rfl) ⟨22572, by rfl⟩ : syracuseStep 3852373 = 45145) (by norm_num)
theorem B5136497 : Blo 2281435 5136497 := bstep (se 2 (by rfl) ⟨1926186, by rfl⟩ : syracuseStep 5136497 = 3852373) B3852373
theorem B3424331 : Blo 2281435 3424331 := bstep (se 1 (by rfl) ⟨2568248, by rfl⟩ : syracuseStep 3424331 = 5136497) B5136497
theorem B2282887 : Blo 2281435 2282887 := bstep (se 1 (by rfl) ⟨1712165, by rfl⟩ : syracuseStep 2282887 = 3424331) B3424331
theorem B2568253 : Blo 2281435 2568253 := bbase (se 3 (by rfl) ⟨481547, by rfl⟩ : syracuseStep 2568253 = 963095) (by norm_num)
theorem B3424337 : Blo 2281435 3424337 := bstep (se 2 (by rfl) ⟨1284126, by rfl⟩ : syracuseStep 3424337 = 2568253) B2568253
theorem B2282891 : Blo 2281435 2282891 := bstep (se 1 (by rfl) ⟨1712168, by rfl⟩ : syracuseStep 2282891 = 3424337) B3424337
theorem B7704773 : Blo 2281435 7704773 := bbase (se 4 (by rfl) ⟨722322, by rfl⟩ : syracuseStep 7704773 = 1444645) (by norm_num)
theorem B5136515 : Blo 2281435 5136515 := bstep (se 1 (by rfl) ⟨3852386, by rfl⟩ : syracuseStep 5136515 = 7704773) B7704773
theorem B3424343 : Blo 2281435 3424343 := bstep (se 1 (by rfl) ⟨2568257, by rfl⟩ : syracuseStep 3424343 = 5136515) B5136515
theorem B2282895 : Blo 2281435 2282895 := bstep (se 1 (by rfl) ⟨1712171, by rfl⟩ : syracuseStep 2282895 = 3424343) B3424343
theorem B3424349 : Blo 2281435 3424349 := bbase (se 3 (by rfl) ⟨642065, by rfl⟩ : syracuseStep 3424349 = 1284131) (by norm_num)
theorem B2282899 : Blo 2281435 2282899 := bstep (se 1 (by rfl) ⟨1712174, by rfl⟩ : syracuseStep 2282899 = 3424349) B3424349
theorem B5136533 : Blo 2281435 5136533 := bbase (se 6 (by rfl) ⟨120387, by rfl⟩ : syracuseStep 5136533 = 240775) (by norm_num)
theorem B3424355 : Blo 2281435 3424355 := bstep (se 1 (by rfl) ⟨2568266, by rfl⟩ : syracuseStep 3424355 = 5136533) B5136533
theorem B2282903 : Blo 2281435 2282903 := bstep (se 1 (by rfl) ⟨1712177, by rfl⟩ : syracuseStep 2282903 = 3424355) B3424355
theorem B3250469 : Blo 2281435 3250469 := bbase (se 4 (by rfl) ⟨304731, by rfl⟩ : syracuseStep 3250469 = 609463) (by norm_num)
theorem B8667917 : Blo 2281435 8667917 := bstep (se 3 (by rfl) ⟨1625234, by rfl⟩ : syracuseStep 8667917 = 3250469) B3250469
theorem B5778611 : Blo 2281435 5778611 := bstep (se 1 (by rfl) ⟨4333958, by rfl⟩ : syracuseStep 5778611 = 8667917) B8667917
theorem B3852407 : Blo 2281435 3852407 := bstep (se 1 (by rfl) ⟨2889305, by rfl⟩ : syracuseStep 3852407 = 5778611) B5778611
theorem B2568271 : Blo 2281435 2568271 := bstep (se 1 (by rfl) ⟨1926203, by rfl⟩ : syracuseStep 2568271 = 3852407) B3852407
theorem B3424361 : Blo 2281435 3424361 := bstep (se 2 (by rfl) ⟨1284135, by rfl⟩ : syracuseStep 3424361 = 2568271) B2568271
theorem B2282907 : Blo 2281435 2282907 := bstep (se 1 (by rfl) ⟨1712180, by rfl⟩ : syracuseStep 2282907 = 3424361) B3424361
theorem B2674837 : Blo 2281435 2674837 := bbase (se 6 (by rfl) ⟨62691, by rfl⟩ : syracuseStep 2674837 = 125383) (by norm_num)
theorem B3566449 : Blo 2281435 3566449 := bstep (se 2 (by rfl) ⟨1337418, by rfl⟩ : syracuseStep 3566449 = 2674837) B2674837
theorem B19021061 : Blo 2281435 19021061 := bstep (se 4 (by rfl) ⟨1783224, by rfl⟩ : syracuseStep 19021061 = 3566449) B3566449
theorem B12680707 : Blo 2281435 12680707 := bstep (se 1 (by rfl) ⟨9510530, by rfl⟩ : syracuseStep 12680707 = 19021061) B19021061
theorem B16907609 : Blo 2281435 16907609 := bstep (se 2 (by rfl) ⟨6340353, by rfl⟩ : syracuseStep 16907609 = 12680707) B12680707
theorem B11271739 : Blo 2281435 11271739 := bstep (se 1 (by rfl) ⟨8453804, by rfl⟩ : syracuseStep 11271739 = 16907609) B16907609
theorem B15028985 : Blo 2281435 15028985 := bstep (se 2 (by rfl) ⟨5635869, by rfl⟩ : syracuseStep 15028985 = 11271739) B11271739
theorem B10019323 : Blo 2281435 10019323 := bstep (se 1 (by rfl) ⟨7514492, by rfl⟩ : syracuseStep 10019323 = 15028985) B15028985
theorem B13359097 : Blo 2281435 13359097 := bstep (se 2 (by rfl) ⟨5009661, by rfl⟩ : syracuseStep 13359097 = 10019323) B10019323
theorem B17812129 : Blo 2281435 17812129 := bstep (se 2 (by rfl) ⟨6679548, by rfl⟩ : syracuseStep 17812129 = 13359097) B13359097
theorem B23749505 : Blo 2281435 23749505 := bstep (se 2 (by rfl) ⟨8906064, by rfl⟩ : syracuseStep 23749505 = 17812129) B17812129
theorem B15833003 : Blo 2281435 15833003 := bstep (se 1 (by rfl) ⟨11874752, by rfl⟩ : syracuseStep 15833003 = 23749505) B23749505
theorem B42221341 : Blo 2281435 42221341 := bstep (se 3 (by rfl) ⟨7916501, by rfl⟩ : syracuseStep 42221341 = 15833003) B15833003
theorem B56295121 : Blo 2281435 56295121 := bstep (se 2 (by rfl) ⟨21110670, by rfl⟩ : syracuseStep 56295121 = 42221341) B42221341
theorem B75060161 : Blo 2281435 75060161 := bstep (se 2 (by rfl) ⟨28147560, by rfl⟩ : syracuseStep 75060161 = 56295121) B56295121
theorem B50040107 : Blo 2281435 50040107 := bstep (se 1 (by rfl) ⟨37530080, by rfl⟩ : syracuseStep 50040107 = 75060161) B75060161
theorem B33360071 : Blo 2281435 33360071 := bstep (se 1 (by rfl) ⟨25020053, by rfl⟩ : syracuseStep 33360071 = 50040107) B50040107
theorem B88960189 : Blo 2281435 88960189 := bstep (se 3 (by rfl) ⟨16680035, by rfl⟩ : syracuseStep 88960189 = 33360071) B33360071
theorem B118613585 : Blo 2281435 118613585 := bstep (se 2 (by rfl) ⟨44480094, by rfl⟩ : syracuseStep 118613585 = 88960189) B88960189
theorem B316302893 : Blo 2281435 316302893 := bstep (se 3 (by rfl) ⟨59306792, by rfl⟩ : syracuseStep 316302893 = 118613585) B118613585
theorem B210868595 : Blo 2281435 210868595 := bstep (se 1 (by rfl) ⟨158151446, by rfl⟩ : syracuseStep 210868595 = 316302893) B316302893
theorem B140579063 : Blo 2281435 140579063 := bstep (se 1 (by rfl) ⟨105434297, by rfl⟩ : syracuseStep 140579063 = 210868595) B210868595
theorem B93719375 : Blo 2281435 93719375 := bstep (se 1 (by rfl) ⟨70289531, by rfl⟩ : syracuseStep 93719375 = 140579063) B140579063
theorem B62479583 : Blo 2281435 62479583 := bstep (se 1 (by rfl) ⟨46859687, by rfl⟩ : syracuseStep 62479583 = 93719375) B93719375
theorem B41653055 : Blo 2281435 41653055 := bstep (se 1 (by rfl) ⟨31239791, by rfl⟩ : syracuseStep 41653055 = 62479583) B62479583
theorem B111074813 : Blo 2281435 111074813 := bstep (se 3 (by rfl) ⟨20826527, by rfl⟩ : syracuseStep 111074813 = 41653055) B41653055
theorem B74049875 : Blo 2281435 74049875 := bstep (se 1 (by rfl) ⟨55537406, by rfl⟩ : syracuseStep 74049875 = 111074813) B111074813
theorem B49366583 : Blo 2281435 49366583 := bstep (se 1 (by rfl) ⟨37024937, by rfl⟩ : syracuseStep 49366583 = 74049875) B74049875
theorem B32911055 : Blo 2281435 32911055 := bstep (se 1 (by rfl) ⟨24683291, by rfl⟩ : syracuseStep 32911055 = 49366583) B49366583
theorem B21940703 : Blo 2281435 21940703 := bstep (se 1 (by rfl) ⟨16455527, by rfl⟩ : syracuseStep 21940703 = 32911055) B32911055
theorem B14627135 : Blo 2281435 14627135 := bstep (se 1 (by rfl) ⟨10970351, by rfl⟩ : syracuseStep 14627135 = 21940703) B21940703
theorem B9751423 : Blo 2281435 9751423 := bstep (se 1 (by rfl) ⟨7313567, by rfl⟩ : syracuseStep 9751423 = 14627135) B14627135
theorem B13001897 : Blo 2281435 13001897 := bstep (se 2 (by rfl) ⟨4875711, by rfl⟩ : syracuseStep 13001897 = 9751423) B9751423
theorem B8667931 : Blo 2281435 8667931 := bstep (se 1 (by rfl) ⟨6500948, by rfl⟩ : syracuseStep 8667931 = 13001897) B13001897
theorem B11557241 : Blo 2281435 11557241 := bstep (se 2 (by rfl) ⟨4333965, by rfl⟩ : syracuseStep 11557241 = 8667931) B8667931
theorem B7704827 : Blo 2281435 7704827 := bstep (se 1 (by rfl) ⟨5778620, by rfl⟩ : syracuseStep 7704827 = 11557241) B11557241
theorem B5136551 : Blo 2281435 5136551 := bstep (se 1 (by rfl) ⟨3852413, by rfl⟩ : syracuseStep 5136551 = 7704827) B7704827
theorem B3424367 : Blo 2281435 3424367 := bstep (se 1 (by rfl) ⟨2568275, by rfl⟩ : syracuseStep 3424367 = 5136551) B5136551
theorem B2282911 : Blo 2281435 2282911 := bstep (se 1 (by rfl) ⟨1712183, by rfl⟩ : syracuseStep 2282911 = 3424367) B3424367
theorem B3424373 : Blo 2281435 3424373 := bbase (se 5 (by rfl) ⟨160517, by rfl⟩ : syracuseStep 3424373 = 321035) (by norm_num)
theorem B2282915 : Blo 2281435 2282915 := bstep (se 1 (by rfl) ⟨1712186, by rfl⟩ : syracuseStep 2282915 = 3424373) B3424373
theorem B4333981 : Blo 2281435 4333981 := bbase (se 3 (by rfl) ⟨812621, by rfl⟩ : syracuseStep 4333981 = 1625243) (by norm_num)
theorem B5778641 : Blo 2281435 5778641 := bstep (se 2 (by rfl) ⟨2166990, by rfl⟩ : syracuseStep 5778641 = 4333981) B4333981
theorem B3852427 : Blo 2281435 3852427 := bstep (se 1 (by rfl) ⟨2889320, by rfl⟩ : syracuseStep 3852427 = 5778641) B5778641
theorem B5136569 : Blo 2281435 5136569 := bstep (se 2 (by rfl) ⟨1926213, by rfl⟩ : syracuseStep 5136569 = 3852427) B3852427
theorem B3424379 : Blo 2281435 3424379 := bstep (se 1 (by rfl) ⟨2568284, by rfl⟩ : syracuseStep 3424379 = 5136569) B5136569
theorem B2282919 : Blo 2281435 2282919 := bstep (se 1 (by rfl) ⟨1712189, by rfl⟩ : syracuseStep 2282919 = 3424379) B3424379
theorem B2568289 : Blo 2281435 2568289 := bbase (se 2 (by rfl) ⟨963108, by rfl⟩ : syracuseStep 2568289 = 1926217) (by norm_num)
theorem B3424385 : Blo 2281435 3424385 := bstep (se 2 (by rfl) ⟨1284144, by rfl⟩ : syracuseStep 3424385 = 2568289) B2568289
theorem B2282923 : Blo 2281435 2282923 := bstep (se 1 (by rfl) ⟨1712192, by rfl⟩ : syracuseStep 2282923 = 3424385) B3424385
theorem B5778661 : Blo 2281435 5778661 := bbase (se 4 (by rfl) ⟨541749, by rfl⟩ : syracuseStep 5778661 = 1083499) (by norm_num)
theorem B7704881 : Blo 2281435 7704881 := bstep (se 2 (by rfl) ⟨2889330, by rfl⟩ : syracuseStep 7704881 = 5778661) B5778661
theorem B5136587 : Blo 2281435 5136587 := bstep (se 1 (by rfl) ⟨3852440, by rfl⟩ : syracuseStep 5136587 = 7704881) B7704881
theorem B3424391 : Blo 2281435 3424391 := bstep (se 1 (by rfl) ⟨2568293, by rfl⟩ : syracuseStep 3424391 = 5136587) B5136587
theorem B2282927 : Blo 2281435 2282927 := bstep (se 1 (by rfl) ⟨1712195, by rfl⟩ : syracuseStep 2282927 = 3424391) B3424391
theorem B3424397 : Blo 2281435 3424397 := bbase (se 3 (by rfl) ⟨642074, by rfl⟩ : syracuseStep 3424397 = 1284149) (by norm_num)
theorem B2282931 : Blo 2281435 2282931 := bstep (se 1 (by rfl) ⟨1712198, by rfl⟩ : syracuseStep 2282931 = 3424397) B3424397
theorem B5136605 : Blo 2281435 5136605 := bbase (se 3 (by rfl) ⟨963113, by rfl⟩ : syracuseStep 5136605 = 1926227) (by norm_num)
theorem B3424403 : Blo 2281435 3424403 := bstep (se 1 (by rfl) ⟨2568302, by rfl⟩ : syracuseStep 3424403 = 5136605) B5136605
theorem B2282935 : Blo 2281435 2282935 := bstep (se 1 (by rfl) ⟨1712201, by rfl⟩ : syracuseStep 2282935 = 3424403) B3424403
theorem B3852461 : Blo 2281435 3852461 := bbase (se 3 (by rfl) ⟨722336, by rfl⟩ : syracuseStep 3852461 = 1444673) (by norm_num)
theorem B2568307 : Blo 2281435 2568307 := bstep (se 1 (by rfl) ⟨1926230, by rfl⟩ : syracuseStep 2568307 = 3852461) B3852461
theorem B3424409 : Blo 2281435 3424409 := bstep (se 2 (by rfl) ⟨1284153, by rfl⟩ : syracuseStep 3424409 = 2568307) B2568307
theorem B2282939 : Blo 2281435 2282939 := bstep (se 1 (by rfl) ⟨1712204, by rfl⟩ : syracuseStep 2282939 = 3424409) B3424409
theorem B2603353 : Blo 2281435 2603353 := bbase (se 2 (by rfl) ⟨976257, by rfl⟩ : syracuseStep 2603353 = 1952515) (by norm_num)
theorem B3471137 : Blo 2281435 3471137 := bstep (se 2 (by rfl) ⟨1301676, by rfl⟩ : syracuseStep 3471137 = 2603353) B2603353
theorem B2314091 : Blo 2281435 2314091 := bstep (se 1 (by rfl) ⟨1735568, by rfl⟩ : syracuseStep 2314091 = 3471137) B3471137
theorem B6170909 : Blo 2281435 6170909 := bstep (se 3 (by rfl) ⟨1157045, by rfl⟩ : syracuseStep 6170909 = 2314091) B2314091
theorem B65823029 : Blo 2281435 65823029 := bstep (se 5 (by rfl) ⟨3085454, by rfl⟩ : syracuseStep 65823029 = 6170909) B6170909
theorem B43882019 : Blo 2281435 43882019 := bstep (se 1 (by rfl) ⟨32911514, by rfl⟩ : syracuseStep 43882019 = 65823029) B65823029
theorem B29254679 : Blo 2281435 29254679 := bstep (se 1 (by rfl) ⟨21941009, by rfl⟩ : syracuseStep 29254679 = 43882019) B43882019
theorem B19503119 : Blo 2281435 19503119 := bstep (se 1 (by rfl) ⟨14627339, by rfl⟩ : syracuseStep 19503119 = 29254679) B29254679
theorem B13002079 : Blo 2281435 13002079 := bstep (se 1 (by rfl) ⟨9751559, by rfl⟩ : syracuseStep 13002079 = 19503119) B19503119
theorem B17336105 : Blo 2281435 17336105 := bstep (se 2 (by rfl) ⟨6501039, by rfl⟩ : syracuseStep 17336105 = 13002079) B13002079
theorem B11557403 : Blo 2281435 11557403 := bstep (se 1 (by rfl) ⟨8668052, by rfl⟩ : syracuseStep 11557403 = 17336105) B17336105
theorem B7704935 : Blo 2281435 7704935 := bstep (se 1 (by rfl) ⟨5778701, by rfl⟩ : syracuseStep 7704935 = 11557403) B11557403
theorem B5136623 : Blo 2281435 5136623 := bstep (se 1 (by rfl) ⟨3852467, by rfl⟩ : syracuseStep 5136623 = 7704935) B7704935
theorem B3424415 : Blo 2281435 3424415 := bstep (se 1 (by rfl) ⟨2568311, by rfl⟩ : syracuseStep 3424415 = 5136623) B5136623
theorem B2282943 : Blo 2281435 2282943 := bstep (se 1 (by rfl) ⟨1712207, by rfl⟩ : syracuseStep 2282943 = 3424415) B3424415
theorem B3424421 : Blo 2281435 3424421 := bbase (se 4 (by rfl) ⟨321039, by rfl⟩ : syracuseStep 3424421 = 642079) (by norm_num)
theorem B2282947 : Blo 2281435 2282947 := bstep (se 1 (by rfl) ⟨1712210, by rfl⟩ : syracuseStep 2282947 = 3424421) B3424421
theorem B2889361 : Blo 2281435 2889361 := bbase (se 2 (by rfl) ⟨1083510, by rfl⟩ : syracuseStep 2889361 = 2167021) (by norm_num)
theorem B3852481 : Blo 2281435 3852481 := bstep (se 2 (by rfl) ⟨1444680, by rfl⟩ : syracuseStep 3852481 = 2889361) B2889361
theorem B5136641 : Blo 2281435 5136641 := bstep (se 2 (by rfl) ⟨1926240, by rfl⟩ : syracuseStep 5136641 = 3852481) B3852481
theorem B3424427 : Blo 2281435 3424427 := bstep (se 1 (by rfl) ⟨2568320, by rfl⟩ : syracuseStep 3424427 = 5136641) B5136641
theorem B2282951 : Blo 2281435 2282951 := bstep (se 1 (by rfl) ⟨1712213, by rfl⟩ : syracuseStep 2282951 = 3424427) B3424427
theorem B2568325 : Blo 2281435 2568325 := bbase (se 4 (by rfl) ⟨240780, by rfl⟩ : syracuseStep 2568325 = 481561) (by norm_num)
theorem B3424433 : Blo 2281435 3424433 := bstep (se 2 (by rfl) ⟨1284162, by rfl⟩ : syracuseStep 3424433 = 2568325) B2568325
theorem B2282955 : Blo 2281435 2282955 := bstep (se 1 (by rfl) ⟨1712216, by rfl⟩ : syracuseStep 2282955 = 3424433) B3424433
theorem B12341909 : Blo 2281435 12341909 := bbase (se 6 (by rfl) ⟨289263, by rfl⟩ : syracuseStep 12341909 = 578527) (by norm_num)
theorem B8227939 : Blo 2281435 8227939 := bstep (se 1 (by rfl) ⟨6170954, by rfl⟩ : syracuseStep 8227939 = 12341909) B12341909
theorem B10970585 : Blo 2281435 10970585 := bstep (se 2 (by rfl) ⟨4113969, by rfl⟩ : syracuseStep 10970585 = 8227939) B8227939
theorem B7313723 : Blo 2281435 7313723 := bstep (se 1 (by rfl) ⟨5485292, by rfl⟩ : syracuseStep 7313723 = 10970585) B10970585
theorem B4875815 : Blo 2281435 4875815 := bstep (se 1 (by rfl) ⟨3656861, by rfl⟩ : syracuseStep 4875815 = 7313723) B7313723
theorem B3250543 : Blo 2281435 3250543 := bstep (se 1 (by rfl) ⟨2437907, by rfl⟩ : syracuseStep 3250543 = 4875815) B4875815
theorem B4334057 : Blo 2281435 4334057 := bstep (se 2 (by rfl) ⟨1625271, by rfl⟩ : syracuseStep 4334057 = 3250543) B3250543
theorem B2889371 : Blo 2281435 2889371 := bstep (se 1 (by rfl) ⟨2167028, by rfl⟩ : syracuseStep 2889371 = 4334057) B4334057
theorem B7704989 : Blo 2281435 7704989 := bstep (se 3 (by rfl) ⟨1444685, by rfl⟩ : syracuseStep 7704989 = 2889371) B2889371
theorem B5136659 : Blo 2281435 5136659 := bstep (se 1 (by rfl) ⟨3852494, by rfl⟩ : syracuseStep 5136659 = 7704989) B7704989
theorem B3424439 : Blo 2281435 3424439 := bstep (se 1 (by rfl) ⟨2568329, by rfl⟩ : syracuseStep 3424439 = 5136659) B5136659
theorem B2282959 : Blo 2281435 2282959 := bstep (se 1 (by rfl) ⟨1712219, by rfl⟩ : syracuseStep 2282959 = 3424439) B3424439
theorem B3424445 : Blo 2281435 3424445 := bbase (se 3 (by rfl) ⟨642083, by rfl⟩ : syracuseStep 3424445 = 1284167) (by norm_num)
theorem B2282963 : Blo 2281435 2282963 := bstep (se 1 (by rfl) ⟨1712222, by rfl⟩ : syracuseStep 2282963 = 3424445) B3424445
theorem B5136677 : Blo 2281435 5136677 := bbase (se 4 (by rfl) ⟨481563, by rfl⟩ : syracuseStep 5136677 = 963127) (by norm_num)
theorem B3424451 : Blo 2281435 3424451 := bstep (se 1 (by rfl) ⟨2568338, by rfl⟩ : syracuseStep 3424451 = 5136677) B5136677
theorem B2282967 : Blo 2281435 2282967 := bstep (se 1 (by rfl) ⟨1712225, by rfl⟩ : syracuseStep 2282967 = 3424451) B3424451
theorem B5778773 : Blo 2281435 5778773 := bbase (se 11 (by rfl) ⟨4232, by rfl⟩ : syracuseStep 5778773 = 8465) (by norm_num)
theorem B3852515 : Blo 2281435 3852515 := bstep (se 1 (by rfl) ⟨2889386, by rfl⟩ : syracuseStep 3852515 = 5778773) B5778773
theorem B2568343 : Blo 2281435 2568343 := bstep (se 1 (by rfl) ⟨1926257, by rfl⟩ : syracuseStep 2568343 = 3852515) B3852515
theorem B3424457 : Blo 2281435 3424457 := bstep (se 2 (by rfl) ⟨1284171, by rfl⟩ : syracuseStep 3424457 = 2568343) B2568343
theorem B2282971 : Blo 2281435 2282971 := bstep (se 1 (by rfl) ⟨1712228, by rfl⟩ : syracuseStep 2282971 = 3424457) B3424457
theorem B2742665 : Blo 2281435 2742665 := bbase (se 2 (by rfl) ⟨1028499, by rfl⟩ : syracuseStep 2742665 = 2056999) (by norm_num)
theorem B7313773 : Blo 2281435 7313773 := bstep (se 3 (by rfl) ⟨1371332, by rfl⟩ : syracuseStep 7313773 = 2742665) B2742665
theorem B9751697 : Blo 2281435 9751697 := bstep (se 2 (by rfl) ⟨3656886, by rfl⟩ : syracuseStep 9751697 = 7313773) B7313773
theorem B6501131 : Blo 2281435 6501131 := bstep (se 1 (by rfl) ⟨4875848, by rfl⟩ : syracuseStep 6501131 = 9751697) B9751697
theorem B4334087 : Blo 2281435 4334087 := bstep (se 1 (by rfl) ⟨3250565, by rfl⟩ : syracuseStep 4334087 = 6501131) B6501131
theorem B11557565 : Blo 2281435 11557565 := bstep (se 3 (by rfl) ⟨2167043, by rfl⟩ : syracuseStep 11557565 = 4334087) B4334087
theorem B7705043 : Blo 2281435 7705043 := bstep (se 1 (by rfl) ⟨5778782, by rfl⟩ : syracuseStep 7705043 = 11557565) B11557565
theorem B5136695 : Blo 2281435 5136695 := bstep (se 1 (by rfl) ⟨3852521, by rfl⟩ : syracuseStep 5136695 = 7705043) B7705043
theorem B3424463 : Blo 2281435 3424463 := bstep (se 1 (by rfl) ⟨2568347, by rfl⟩ : syracuseStep 3424463 = 5136695) B5136695
theorem B2282975 : Blo 2281435 2282975 := bstep (se 1 (by rfl) ⟨1712231, by rfl⟩ : syracuseStep 2282975 = 3424463) B3424463
theorem B3424469 : Blo 2281435 3424469 := bbase (se 7 (by rfl) ⟨40130, by rfl⟩ : syracuseStep 3424469 = 80261) (by norm_num)
theorem B2282979 : Blo 2281435 2282979 := bstep (se 1 (by rfl) ⟨1712234, by rfl⟩ : syracuseStep 2282979 = 3424469) B3424469
theorem B2437933 : Blo 2281435 2437933 := bbase (se 3 (by rfl) ⟨457112, by rfl⟩ : syracuseStep 2437933 = 914225) (by norm_num)
theorem B3250577 : Blo 2281435 3250577 := bstep (se 2 (by rfl) ⟨1218966, by rfl⟩ : syracuseStep 3250577 = 2437933) B2437933
theorem B8668205 : Blo 2281435 8668205 := bstep (se 3 (by rfl) ⟨1625288, by rfl⟩ : syracuseStep 8668205 = 3250577) B3250577
theorem B5778803 : Blo 2281435 5778803 := bstep (se 1 (by rfl) ⟨4334102, by rfl⟩ : syracuseStep 5778803 = 8668205) B8668205
theorem B3852535 : Blo 2281435 3852535 := bstep (se 1 (by rfl) ⟨2889401, by rfl⟩ : syracuseStep 3852535 = 5778803) B5778803
theorem B5136713 : Blo 2281435 5136713 := bstep (se 2 (by rfl) ⟨1926267, by rfl⟩ : syracuseStep 5136713 = 3852535) B3852535
theorem B3424475 : Blo 2281435 3424475 := bstep (se 1 (by rfl) ⟨2568356, by rfl⟩ : syracuseStep 3424475 = 5136713) B5136713
theorem B2282983 : Blo 2281435 2282983 := bstep (se 1 (by rfl) ⟨1712237, by rfl⟩ : syracuseStep 2282983 = 3424475) B3424475
theorem B2568361 : Blo 2281435 2568361 := bbase (se 2 (by rfl) ⟨963135, by rfl⟩ : syracuseStep 2568361 = 1926271) (by norm_num)
theorem B3424481 : Blo 2281435 3424481 := bstep (se 2 (by rfl) ⟨1284180, by rfl⟩ : syracuseStep 3424481 = 2568361) B2568361
theorem B2282987 : Blo 2281435 2282987 := bstep (se 1 (by rfl) ⟨1712240, by rfl⟩ : syracuseStep 2282987 = 3424481) B3424481
theorem B9751765 : Blo 2281435 9751765 := bbase (se 7 (by rfl) ⟨114278, by rfl⟩ : syracuseStep 9751765 = 228557) (by norm_num)
theorem B13002353 : Blo 2281435 13002353 := bstep (se 2 (by rfl) ⟨4875882, by rfl⟩ : syracuseStep 13002353 = 9751765) B9751765
theorem B8668235 : Blo 2281435 8668235 := bstep (se 1 (by rfl) ⟨6501176, by rfl⟩ : syracuseStep 8668235 = 13002353) B13002353
theorem B5778823 : Blo 2281435 5778823 := bstep (se 1 (by rfl) ⟨4334117, by rfl⟩ : syracuseStep 5778823 = 8668235) B8668235
theorem B7705097 : Blo 2281435 7705097 := bstep (se 2 (by rfl) ⟨2889411, by rfl⟩ : syracuseStep 7705097 = 5778823) B5778823
theorem B5136731 : Blo 2281435 5136731 := bstep (se 1 (by rfl) ⟨3852548, by rfl⟩ : syracuseStep 5136731 = 7705097) B7705097
theorem B3424487 : Blo 2281435 3424487 := bstep (se 1 (by rfl) ⟨2568365, by rfl⟩ : syracuseStep 3424487 = 5136731) B5136731
theorem B2282991 : Blo 2281435 2282991 := bstep (se 1 (by rfl) ⟨1712243, by rfl⟩ : syracuseStep 2282991 = 3424487) B3424487
theorem B3424493 : Blo 2281435 3424493 := bbase (se 3 (by rfl) ⟨642092, by rfl⟩ : syracuseStep 3424493 = 1284185) (by norm_num)
theorem B2282995 : Blo 2281435 2282995 := bstep (se 1 (by rfl) ⟨1712246, by rfl⟩ : syracuseStep 2282995 = 3424493) B3424493
theorem B5136749 : Blo 2281435 5136749 := bbase (se 3 (by rfl) ⟨963140, by rfl⟩ : syracuseStep 5136749 = 1926281) (by norm_num)
theorem B3424499 : Blo 2281435 3424499 := bstep (se 1 (by rfl) ⟨2568374, by rfl⟩ : syracuseStep 3424499 = 5136749) B5136749
theorem B2282999 : Blo 2281435 2282999 := bstep (se 1 (by rfl) ⟨1712249, by rfl⟩ : syracuseStep 2282999 = 3424499) B3424499
theorem B4334141 : Blo 2281435 4334141 := bbase (se 3 (by rfl) ⟨812651, by rfl⟩ : syracuseStep 4334141 = 1625303) (by norm_num)
theorem B2889427 : Blo 2281435 2889427 := bstep (se 1 (by rfl) ⟨2167070, by rfl⟩ : syracuseStep 2889427 = 4334141) B4334141
theorem B3852569 : Blo 2281435 3852569 := bstep (se 2 (by rfl) ⟨1444713, by rfl⟩ : syracuseStep 3852569 = 2889427) B2889427
theorem B2568379 : Blo 2281435 2568379 := bstep (se 1 (by rfl) ⟨1926284, by rfl⟩ : syracuseStep 2568379 = 3852569) B3852569
theorem B3424505 : Blo 2281435 3424505 := bstep (se 2 (by rfl) ⟨1284189, by rfl⟩ : syracuseStep 3424505 = 2568379) B2568379
theorem B2283003 : Blo 2281435 2283003 := bstep (se 1 (by rfl) ⟨1712252, by rfl⟩ : syracuseStep 2283003 = 3424505) B3424505
theorem B6942469 : Blo 2281435 6942469 := bbase (se 4 (by rfl) ⟨650856, by rfl⟩ : syracuseStep 6942469 = 1301713) (by norm_num)
theorem B9256625 : Blo 2281435 9256625 := bstep (se 2 (by rfl) ⟨3471234, by rfl⟩ : syracuseStep 9256625 = 6942469) B6942469
theorem B6171083 : Blo 2281435 6171083 := bstep (se 1 (by rfl) ⟨4628312, by rfl⟩ : syracuseStep 6171083 = 9256625) B9256625
theorem B4114055 : Blo 2281435 4114055 := bstep (se 1 (by rfl) ⟨3085541, by rfl⟩ : syracuseStep 4114055 = 6171083) B6171083
theorem B2742703 : Blo 2281435 2742703 := bstep (se 1 (by rfl) ⟨2057027, by rfl⟩ : syracuseStep 2742703 = 4114055) B4114055
theorem B58510997 : Blo 2281435 58510997 := bstep (se 6 (by rfl) ⟨1371351, by rfl⟩ : syracuseStep 58510997 = 2742703) B2742703
theorem B39007331 : Blo 2281435 39007331 := bstep (se 1 (by rfl) ⟨29255498, by rfl⟩ : syracuseStep 39007331 = 58510997) B58510997
theorem B26004887 : Blo 2281435 26004887 := bstep (se 1 (by rfl) ⟨19503665, by rfl⟩ : syracuseStep 26004887 = 39007331) B39007331
theorem B17336591 : Blo 2281435 17336591 := bstep (se 1 (by rfl) ⟨13002443, by rfl⟩ : syracuseStep 17336591 = 26004887) B26004887
theorem B11557727 : Blo 2281435 11557727 := bstep (se 1 (by rfl) ⟨8668295, by rfl⟩ : syracuseStep 11557727 = 17336591) B17336591
theorem B7705151 : Blo 2281435 7705151 := bstep (se 1 (by rfl) ⟨5778863, by rfl⟩ : syracuseStep 7705151 = 11557727) B11557727
theorem B5136767 : Blo 2281435 5136767 := bstep (se 1 (by rfl) ⟨3852575, by rfl⟩ : syracuseStep 5136767 = 7705151) B7705151
theorem B3424511 : Blo 2281435 3424511 := bstep (se 1 (by rfl) ⟨2568383, by rfl⟩ : syracuseStep 3424511 = 5136767) B5136767
theorem B2283007 : Blo 2281435 2283007 := bstep (se 1 (by rfl) ⟨1712255, by rfl⟩ : syracuseStep 2283007 = 3424511) B3424511
theorem B3424517 : Blo 2281435 3424517 := bbase (se 4 (by rfl) ⟨321048, by rfl⟩ : syracuseStep 3424517 = 642097) (by norm_num)
theorem B2283011 : Blo 2281435 2283011 := bstep (se 1 (by rfl) ⟨1712258, by rfl⟩ : syracuseStep 2283011 = 3424517) B3424517
theorem B3852589 : Blo 2281435 3852589 := bbase (se 3 (by rfl) ⟨722360, by rfl⟩ : syracuseStep 3852589 = 1444721) (by norm_num)
theorem B5136785 : Blo 2281435 5136785 := bstep (se 2 (by rfl) ⟨1926294, by rfl⟩ : syracuseStep 5136785 = 3852589) B3852589
theorem B3424523 : Blo 2281435 3424523 := bstep (se 1 (by rfl) ⟨2568392, by rfl⟩ : syracuseStep 3424523 = 5136785) B5136785
theorem B2283015 : Blo 2281435 2283015 := bstep (se 1 (by rfl) ⟨1712261, by rfl⟩ : syracuseStep 2283015 = 3424523) B3424523
theorem B2568397 : Blo 2281435 2568397 := bbase (se 3 (by rfl) ⟨481574, by rfl⟩ : syracuseStep 2568397 = 963149) (by norm_num)
theorem B3424529 : Blo 2281435 3424529 := bstep (se 2 (by rfl) ⟨1284198, by rfl⟩ : syracuseStep 3424529 = 2568397) B2568397
theorem B2283019 : Blo 2281435 2283019 := bstep (se 1 (by rfl) ⟨1712264, by rfl⟩ : syracuseStep 2283019 = 3424529) B3424529
theorem B7705205 : Blo 2281435 7705205 := bbase (se 5 (by rfl) ⟨361181, by rfl⟩ : syracuseStep 7705205 = 722363) (by norm_num)
theorem B5136803 : Blo 2281435 5136803 := bstep (se 1 (by rfl) ⟨3852602, by rfl⟩ : syracuseStep 5136803 = 7705205) B7705205
theorem B3424535 : Blo 2281435 3424535 := bstep (se 1 (by rfl) ⟨2568401, by rfl⟩ : syracuseStep 3424535 = 5136803) B5136803
theorem B2283023 : Blo 2281435 2283023 := bstep (se 1 (by rfl) ⟨1712267, by rfl⟩ : syracuseStep 2283023 = 3424535) B3424535
theorem B3424541 : Blo 2281435 3424541 := bbase (se 3 (by rfl) ⟨642101, by rfl⟩ : syracuseStep 3424541 = 1284203) (by norm_num)
theorem B2283027 : Blo 2281435 2283027 := bstep (se 1 (by rfl) ⟨1712270, by rfl⟩ : syracuseStep 2283027 = 3424541) B3424541
theorem B5136821 : Blo 2281435 5136821 := bbase (se 5 (by rfl) ⟨240788, by rfl⟩ : syracuseStep 5136821 = 481577) (by norm_num)
theorem B3424547 : Blo 2281435 3424547 := bstep (se 1 (by rfl) ⟨2568410, by rfl⟩ : syracuseStep 3424547 = 5136821) B5136821
theorem B2283031 : Blo 2281435 2283031 := bstep (se 1 (by rfl) ⟨1712273, by rfl⟩ : syracuseStep 2283031 = 3424547) B3424547
theorem B8228213 : Blo 2281435 8228213 := bbase (se 5 (by rfl) ⟨385697, by rfl⟩ : syracuseStep 8228213 = 771395) (by norm_num)
theorem B5485475 : Blo 2281435 5485475 := bstep (se 1 (by rfl) ⟨4114106, by rfl⟩ : syracuseStep 5485475 = 8228213) B8228213
theorem B3656983 : Blo 2281435 3656983 := bstep (se 1 (by rfl) ⟨2742737, by rfl⟩ : syracuseStep 3656983 = 5485475) B5485475
theorem B4875977 : Blo 2281435 4875977 := bstep (se 2 (by rfl) ⟨1828491, by rfl⟩ : syracuseStep 4875977 = 3656983) B3656983
theorem B13002605 : Blo 2281435 13002605 := bstep (se 3 (by rfl) ⟨2437988, by rfl⟩ : syracuseStep 13002605 = 4875977) B4875977
theorem B8668403 : Blo 2281435 8668403 := bstep (se 1 (by rfl) ⟨6501302, by rfl⟩ : syracuseStep 8668403 = 13002605) B13002605
theorem B5778935 : Blo 2281435 5778935 := bstep (se 1 (by rfl) ⟨4334201, by rfl⟩ : syracuseStep 5778935 = 8668403) B8668403
theorem B3852623 : Blo 2281435 3852623 := bstep (se 1 (by rfl) ⟨2889467, by rfl⟩ : syracuseStep 3852623 = 5778935) B5778935
theorem B2568415 : Blo 2281435 2568415 := bstep (se 1 (by rfl) ⟨1926311, by rfl⟩ : syracuseStep 2568415 = 3852623) B3852623
theorem B3424553 : Blo 2281435 3424553 := bstep (se 2 (by rfl) ⟨1284207, by rfl⟩ : syracuseStep 3424553 = 2568415) B2568415
theorem B2283035 : Blo 2281435 2283035 := bstep (se 1 (by rfl) ⟨1712276, by rfl⟩ : syracuseStep 2283035 = 3424553) B3424553
theorem B3656989 : Blo 2281435 3656989 := bbase (se 3 (by rfl) ⟨685685, by rfl⟩ : syracuseStep 3656989 = 1371371) (by norm_num)
theorem B4875985 : Blo 2281435 4875985 := bstep (se 2 (by rfl) ⟨1828494, by rfl⟩ : syracuseStep 4875985 = 3656989) B3656989
theorem B6501313 : Blo 2281435 6501313 := bstep (se 2 (by rfl) ⟨2437992, by rfl⟩ : syracuseStep 6501313 = 4875985) B4875985
theorem B8668417 : Blo 2281435 8668417 := bstep (se 2 (by rfl) ⟨3250656, by rfl⟩ : syracuseStep 8668417 = 6501313) B6501313
theorem B11557889 : Blo 2281435 11557889 := bstep (se 2 (by rfl) ⟨4334208, by rfl⟩ : syracuseStep 11557889 = 8668417) B8668417
theorem B7705259 : Blo 2281435 7705259 := bstep (se 1 (by rfl) ⟨5778944, by rfl⟩ : syracuseStep 7705259 = 11557889) B11557889
theorem B5136839 : Blo 2281435 5136839 := bstep (se 1 (by rfl) ⟨3852629, by rfl⟩ : syracuseStep 5136839 = 7705259) B7705259
theorem B3424559 : Blo 2281435 3424559 := bstep (se 1 (by rfl) ⟨2568419, by rfl⟩ : syracuseStep 3424559 = 5136839) B5136839
theorem B2283039 : Blo 2281435 2283039 := bstep (se 1 (by rfl) ⟨1712279, by rfl⟩ : syracuseStep 2283039 = 3424559) B3424559
theorem B3424565 : Blo 2281435 3424565 := bbase (se 5 (by rfl) ⟨160526, by rfl⟩ : syracuseStep 3424565 = 321053) (by norm_num)
theorem B2283043 : Blo 2281435 2283043 := bstep (se 1 (by rfl) ⟨1712282, by rfl⟩ : syracuseStep 2283043 = 3424565) B3424565
theorem B5778965 : Blo 2281435 5778965 := bbase (se 6 (by rfl) ⟨135444, by rfl⟩ : syracuseStep 5778965 = 270889) (by norm_num)
theorem B3852643 : Blo 2281435 3852643 := bstep (se 1 (by rfl) ⟨2889482, by rfl⟩ : syracuseStep 3852643 = 5778965) B5778965
theorem B5136857 : Blo 2281435 5136857 := bstep (se 2 (by rfl) ⟨1926321, by rfl⟩ : syracuseStep 5136857 = 3852643) B3852643
theorem B3424571 : Blo 2281435 3424571 := bstep (se 1 (by rfl) ⟨2568428, by rfl⟩ : syracuseStep 3424571 = 5136857) B5136857
theorem B2283047 : Blo 2281435 2283047 := bstep (se 1 (by rfl) ⟨1712285, by rfl⟩ : syracuseStep 2283047 = 3424571) B3424571
theorem B2568433 : Blo 2281435 2568433 := bbase (se 2 (by rfl) ⟨963162, by rfl⟩ : syracuseStep 2568433 = 1926325) (by norm_num)
theorem B3424577 : Blo 2281435 3424577 := bstep (se 2 (by rfl) ⟨1284216, by rfl⟩ : syracuseStep 3424577 = 2568433) B2568433
theorem B2283051 : Blo 2281435 2283051 := bstep (se 1 (by rfl) ⟨1712288, by rfl⟩ : syracuseStep 2283051 = 3424577) B3424577
theorem B3905221 : Blo 2281435 3905221 := bbase (se 4 (by rfl) ⟨366114, by rfl⟩ : syracuseStep 3905221 = 732229) (by norm_num)
theorem B5206961 : Blo 2281435 5206961 := bstep (se 2 (by rfl) ⟨1952610, by rfl⟩ : syracuseStep 5206961 = 3905221) B3905221
theorem B13885229 : Blo 2281435 13885229 := bstep (se 3 (by rfl) ⟨2603480, by rfl⟩ : syracuseStep 13885229 = 5206961) B5206961
theorem B37027277 : Blo 2281435 37027277 := bstep (se 3 (by rfl) ⟨6942614, by rfl⟩ : syracuseStep 37027277 = 13885229) B13885229
theorem B24684851 : Blo 2281435 24684851 := bstep (se 1 (by rfl) ⟨18513638, by rfl⟩ : syracuseStep 24684851 = 37027277) B37027277
theorem B16456567 : Blo 2281435 16456567 := bstep (se 1 (by rfl) ⟨12342425, by rfl⟩ : syracuseStep 16456567 = 24684851) B24684851
theorem B21942089 : Blo 2281435 21942089 := bstep (se 2 (by rfl) ⟨8228283, by rfl⟩ : syracuseStep 21942089 = 16456567) B16456567
theorem B14628059 : Blo 2281435 14628059 := bstep (se 1 (by rfl) ⟨10971044, by rfl⟩ : syracuseStep 14628059 = 21942089) B21942089
theorem B9752039 : Blo 2281435 9752039 := bstep (se 1 (by rfl) ⟨7314029, by rfl⟩ : syracuseStep 9752039 = 14628059) B14628059
theorem B6501359 : Blo 2281435 6501359 := bstep (se 1 (by rfl) ⟨4876019, by rfl⟩ : syracuseStep 6501359 = 9752039) B9752039
theorem B4334239 : Blo 2281435 4334239 := bstep (se 1 (by rfl) ⟨3250679, by rfl⟩ : syracuseStep 4334239 = 6501359) B6501359
theorem B5778985 : Blo 2281435 5778985 := bstep (se 2 (by rfl) ⟨2167119, by rfl⟩ : syracuseStep 5778985 = 4334239) B4334239
theorem B7705313 : Blo 2281435 7705313 := bstep (se 2 (by rfl) ⟨2889492, by rfl⟩ : syracuseStep 7705313 = 5778985) B5778985
theorem B5136875 : Blo 2281435 5136875 := bstep (se 1 (by rfl) ⟨3852656, by rfl⟩ : syracuseStep 5136875 = 7705313) B7705313
theorem B3424583 : Blo 2281435 3424583 := bstep (se 1 (by rfl) ⟨2568437, by rfl⟩ : syracuseStep 3424583 = 5136875) B5136875
theorem B2283055 : Blo 2281435 2283055 := bstep (se 1 (by rfl) ⟨1712291, by rfl⟩ : syracuseStep 2283055 = 3424583) B3424583
theorem B3424589 : Blo 2281435 3424589 := bbase (se 3 (by rfl) ⟨642110, by rfl⟩ : syracuseStep 3424589 = 1284221) (by norm_num)
theorem B2283059 : Blo 2281435 2283059 := bstep (se 1 (by rfl) ⟨1712294, by rfl⟩ : syracuseStep 2283059 = 3424589) B3424589
theorem B5136893 : Blo 2281435 5136893 := bbase (se 3 (by rfl) ⟨963167, by rfl⟩ : syracuseStep 5136893 = 1926335) (by norm_num)
theorem B3424595 : Blo 2281435 3424595 := bstep (se 1 (by rfl) ⟨2568446, by rfl⟩ : syracuseStep 3424595 = 5136893) B5136893
theorem B2283063 : Blo 2281435 2283063 := bstep (se 1 (by rfl) ⟨1712297, by rfl⟩ : syracuseStep 2283063 = 3424595) B3424595
theorem B3852677 : Blo 2281435 3852677 := bbase (se 4 (by rfl) ⟨361188, by rfl⟩ : syracuseStep 3852677 = 722377) (by norm_num)
theorem B2568451 : Blo 2281435 2568451 := bstep (se 1 (by rfl) ⟨1926338, by rfl⟩ : syracuseStep 2568451 = 3852677) B3852677
theorem B3424601 : Blo 2281435 3424601 := bstep (se 2 (by rfl) ⟨1284225, by rfl⟩ : syracuseStep 3424601 = 2568451) B2568451
theorem B2283067 : Blo 2281435 2283067 := bstep (se 1 (by rfl) ⟨1712300, by rfl⟩ : syracuseStep 2283067 = 3424601) B3424601
theorem B17337077 : Blo 2281435 17337077 := bbase (se 5 (by rfl) ⟨812675, by rfl⟩ : syracuseStep 17337077 = 1625351) (by norm_num)
theorem B11558051 : Blo 2281435 11558051 := bstep (se 1 (by rfl) ⟨8668538, by rfl⟩ : syracuseStep 11558051 = 17337077) B17337077
theorem B7705367 : Blo 2281435 7705367 := bstep (se 1 (by rfl) ⟨5779025, by rfl⟩ : syracuseStep 7705367 = 11558051) B11558051
theorem B5136911 : Blo 2281435 5136911 := bstep (se 1 (by rfl) ⟨3852683, by rfl⟩ : syracuseStep 5136911 = 7705367) B7705367
theorem B3424607 : Blo 2281435 3424607 := bstep (se 1 (by rfl) ⟨2568455, by rfl⟩ : syracuseStep 3424607 = 5136911) B5136911
theorem B2283071 : Blo 2281435 2283071 := bstep (se 1 (by rfl) ⟨1712303, by rfl⟩ : syracuseStep 2283071 = 3424607) B3424607
theorem B3424613 : Blo 2281435 3424613 := bbase (se 4 (by rfl) ⟨321057, by rfl⟩ : syracuseStep 3424613 = 642115) (by norm_num)
theorem B2283075 : Blo 2281435 2283075 := bstep (se 1 (by rfl) ⟨1712306, by rfl⟩ : syracuseStep 2283075 = 3424613) B3424613
theorem B4334285 : Blo 2281435 4334285 := bbase (se 3 (by rfl) ⟨812678, by rfl⟩ : syracuseStep 4334285 = 1625357) (by norm_num)
theorem B2889523 : Blo 2281435 2889523 := bstep (se 1 (by rfl) ⟨2167142, by rfl⟩ : syracuseStep 2889523 = 4334285) B4334285
theorem B3852697 : Blo 2281435 3852697 := bstep (se 2 (by rfl) ⟨1444761, by rfl⟩ : syracuseStep 3852697 = 2889523) B2889523
theorem B5136929 : Blo 2281435 5136929 := bstep (se 2 (by rfl) ⟨1926348, by rfl⟩ : syracuseStep 5136929 = 3852697) B3852697
theorem B3424619 : Blo 2281435 3424619 := bstep (se 1 (by rfl) ⟨2568464, by rfl⟩ : syracuseStep 3424619 = 5136929) B5136929
theorem B2283079 : Blo 2281435 2283079 := bstep (se 1 (by rfl) ⟨1712309, by rfl⟩ : syracuseStep 2283079 = 3424619) B3424619
theorem B2568469 : Blo 2281435 2568469 := bbase (se 6 (by rfl) ⟨60198, by rfl⟩ : syracuseStep 2568469 = 120397) (by norm_num)
theorem B3424625 : Blo 2281435 3424625 := bstep (se 2 (by rfl) ⟨1284234, by rfl⟩ : syracuseStep 3424625 = 2568469) B2568469
theorem B2283083 : Blo 2281435 2283083 := bstep (se 1 (by rfl) ⟨1712312, by rfl⟩ : syracuseStep 2283083 = 3424625) B3424625
theorem B2889533 : Blo 2281435 2889533 := bbase (se 3 (by rfl) ⟨541787, by rfl⟩ : syracuseStep 2889533 = 1083575) (by norm_num)
theorem B7705421 : Blo 2281435 7705421 := bstep (se 3 (by rfl) ⟨1444766, by rfl⟩ : syracuseStep 7705421 = 2889533) B2889533
theorem B5136947 : Blo 2281435 5136947 := bstep (se 1 (by rfl) ⟨3852710, by rfl⟩ : syracuseStep 5136947 = 7705421) B7705421
theorem B3424631 : Blo 2281435 3424631 := bstep (se 1 (by rfl) ⟨2568473, by rfl⟩ : syracuseStep 3424631 = 5136947) B5136947
theorem B2283087 : Blo 2281435 2283087 := bstep (se 1 (by rfl) ⟨1712315, by rfl⟩ : syracuseStep 2283087 = 3424631) B3424631
theorem B3424637 : Blo 2281435 3424637 := bbase (se 3 (by rfl) ⟨642119, by rfl⟩ : syracuseStep 3424637 = 1284239) (by norm_num)
theorem B2283091 : Blo 2281435 2283091 := bstep (se 1 (by rfl) ⟨1712318, by rfl⟩ : syracuseStep 2283091 = 3424637) B3424637
theorem B5136965 : Blo 2281435 5136965 := bbase (se 4 (by rfl) ⟨481590, by rfl⟩ : syracuseStep 5136965 = 963181) (by norm_num)
theorem B3424643 : Blo 2281435 3424643 := bstep (se 1 (by rfl) ⟨2568482, by rfl⟩ : syracuseStep 3424643 = 5136965) B5136965
theorem B2283095 : Blo 2281435 2283095 := bstep (se 1 (by rfl) ⟨1712321, by rfl⟩ : syracuseStep 2283095 = 3424643) B3424643
theorem B2438057 : Blo 2281435 2438057 := bbase (se 2 (by rfl) ⟨914271, by rfl⟩ : syracuseStep 2438057 = 1828543) (by norm_num)
theorem B6501485 : Blo 2281435 6501485 := bstep (se 3 (by rfl) ⟨1219028, by rfl⟩ : syracuseStep 6501485 = 2438057) B2438057
theorem B4334323 : Blo 2281435 4334323 := bstep (se 1 (by rfl) ⟨3250742, by rfl⟩ : syracuseStep 4334323 = 6501485) B6501485
theorem B5779097 : Blo 2281435 5779097 := bstep (se 2 (by rfl) ⟨2167161, by rfl⟩ : syracuseStep 5779097 = 4334323) B4334323
theorem B3852731 : Blo 2281435 3852731 := bstep (se 1 (by rfl) ⟨2889548, by rfl⟩ : syracuseStep 3852731 = 5779097) B5779097
theorem B2568487 : Blo 2281435 2568487 := bstep (se 1 (by rfl) ⟨1926365, by rfl⟩ : syracuseStep 2568487 = 3852731) B3852731
theorem B3424649 : Blo 2281435 3424649 := bstep (se 2 (by rfl) ⟨1284243, by rfl⟩ : syracuseStep 3424649 = 2568487) B2568487
theorem B2283099 : Blo 2281435 2283099 := bstep (se 1 (by rfl) ⟨1712324, by rfl⟩ : syracuseStep 2283099 = 3424649) B3424649
theorem B11558213 : Blo 2281435 11558213 := bbase (se 4 (by rfl) ⟨1083582, by rfl⟩ : syracuseStep 11558213 = 2167165) (by norm_num)
theorem B7705475 : Blo 2281435 7705475 := bstep (se 1 (by rfl) ⟨5779106, by rfl⟩ : syracuseStep 7705475 = 11558213) B11558213
theorem B5136983 : Blo 2281435 5136983 := bstep (se 1 (by rfl) ⟨3852737, by rfl⟩ : syracuseStep 5136983 = 7705475) B7705475
theorem B3424655 : Blo 2281435 3424655 := bstep (se 1 (by rfl) ⟨2568491, by rfl⟩ : syracuseStep 3424655 = 5136983) B5136983
theorem B2283103 : Blo 2281435 2283103 := bstep (se 1 (by rfl) ⟨1712327, by rfl⟩ : syracuseStep 2283103 = 3424655) B3424655
theorem B3424661 : Blo 2281435 3424661 := bbase (se 6 (by rfl) ⟨80265, by rfl⟩ : syracuseStep 3424661 = 160531) (by norm_num)
theorem B2283107 : Blo 2281435 2283107 := bstep (se 1 (by rfl) ⟨1712330, by rfl⟩ : syracuseStep 2283107 = 3424661) B3424661
theorem B6171365 : Blo 2281435 6171365 := bbase (se 4 (by rfl) ⟨578565, by rfl⟩ : syracuseStep 6171365 = 1157131) (by norm_num)
theorem B4114243 : Blo 2281435 4114243 := bstep (se 1 (by rfl) ⟨3085682, by rfl⟩ : syracuseStep 4114243 = 6171365) B6171365
theorem B5485657 : Blo 2281435 5485657 := bstep (se 2 (by rfl) ⟨2057121, by rfl⟩ : syracuseStep 5485657 = 4114243) B4114243
theorem B7314209 : Blo 2281435 7314209 := bstep (se 2 (by rfl) ⟨2742828, by rfl⟩ : syracuseStep 7314209 = 5485657) B5485657
theorem B4876139 : Blo 2281435 4876139 := bstep (se 1 (by rfl) ⟨3657104, by rfl⟩ : syracuseStep 4876139 = 7314209) B7314209
theorem B13003037 : Blo 2281435 13003037 := bstep (se 3 (by rfl) ⟨2438069, by rfl⟩ : syracuseStep 13003037 = 4876139) B4876139
theorem B8668691 : Blo 2281435 8668691 := bstep (se 1 (by rfl) ⟨6501518, by rfl⟩ : syracuseStep 8668691 = 13003037) B13003037
theorem B5779127 : Blo 2281435 5779127 := bstep (se 1 (by rfl) ⟨4334345, by rfl⟩ : syracuseStep 5779127 = 8668691) B8668691
theorem B3852751 : Blo 2281435 3852751 := bstep (se 1 (by rfl) ⟨2889563, by rfl⟩ : syracuseStep 3852751 = 5779127) B5779127
theorem B5137001 : Blo 2281435 5137001 := bstep (se 2 (by rfl) ⟨1926375, by rfl⟩ : syracuseStep 5137001 = 3852751) B3852751
theorem B3424667 : Blo 2281435 3424667 := bstep (se 1 (by rfl) ⟨2568500, by rfl⟩ : syracuseStep 3424667 = 5137001) B5137001
theorem B2283111 : Blo 2281435 2283111 := bstep (se 1 (by rfl) ⟨1712333, by rfl⟩ : syracuseStep 2283111 = 3424667) B3424667
theorem B2568505 : Blo 2281435 2568505 := bbase (se 2 (by rfl) ⟨963189, by rfl⟩ : syracuseStep 2568505 = 1926379) (by norm_num)
theorem B3424673 : Blo 2281435 3424673 := bstep (se 2 (by rfl) ⟨1284252, by rfl⟩ : syracuseStep 3424673 = 2568505) B2568505
theorem B2283115 : Blo 2281435 2283115 := bstep (se 1 (by rfl) ⟨1712336, by rfl⟩ : syracuseStep 2283115 = 3424673) B3424673
theorem B6501541 : Blo 2281435 6501541 := bbase (se 4 (by rfl) ⟨609519, by rfl⟩ : syracuseStep 6501541 = 1219039) (by norm_num)
theorem B8668721 : Blo 2281435 8668721 := bstep (se 2 (by rfl) ⟨3250770, by rfl⟩ : syracuseStep 8668721 = 6501541) B6501541
theorem B5779147 : Blo 2281435 5779147 := bstep (se 1 (by rfl) ⟨4334360, by rfl⟩ : syracuseStep 5779147 = 8668721) B8668721
theorem B7705529 : Blo 2281435 7705529 := bstep (se 2 (by rfl) ⟨2889573, by rfl⟩ : syracuseStep 7705529 = 5779147) B5779147
theorem B5137019 : Blo 2281435 5137019 := bstep (se 1 (by rfl) ⟨3852764, by rfl⟩ : syracuseStep 5137019 = 7705529) B7705529
theorem B3424679 : Blo 2281435 3424679 := bstep (se 1 (by rfl) ⟨2568509, by rfl⟩ : syracuseStep 3424679 = 5137019) B5137019
theorem B2283119 : Blo 2281435 2283119 := bstep (se 1 (by rfl) ⟨1712339, by rfl⟩ : syracuseStep 2283119 = 3424679) B3424679
theorem B3424685 : Blo 2281435 3424685 := bbase (se 3 (by rfl) ⟨642128, by rfl⟩ : syracuseStep 3424685 = 1284257) (by norm_num)
theorem B2283123 : Blo 2281435 2283123 := bstep (se 1 (by rfl) ⟨1712342, by rfl⟩ : syracuseStep 2283123 = 3424685) B3424685
theorem B5137037 : Blo 2281435 5137037 := bbase (se 3 (by rfl) ⟨963194, by rfl⟩ : syracuseStep 5137037 = 1926389) (by norm_num)
theorem B3424691 : Blo 2281435 3424691 := bstep (se 1 (by rfl) ⟨2568518, by rfl⟩ : syracuseStep 3424691 = 5137037) B5137037
theorem B2283127 : Blo 2281435 2283127 := bstep (se 1 (by rfl) ⟨1712345, by rfl⟩ : syracuseStep 2283127 = 3424691) B3424691
theorem B2889589 : Blo 2281435 2889589 := bbase (se 5 (by rfl) ⟨135449, by rfl⟩ : syracuseStep 2889589 = 270899) (by norm_num)
theorem B3852785 : Blo 2281435 3852785 := bstep (se 2 (by rfl) ⟨1444794, by rfl⟩ : syracuseStep 3852785 = 2889589) B2889589
theorem B2568523 : Blo 2281435 2568523 := bstep (se 1 (by rfl) ⟨1926392, by rfl⟩ : syracuseStep 2568523 = 3852785) B3852785
theorem B3424697 : Blo 2281435 3424697 := bstep (se 2 (by rfl) ⟨1284261, by rfl⟩ : syracuseStep 3424697 = 2568523) B2568523
theorem B2283131 : Blo 2281435 2283131 := bstep (se 1 (by rfl) ⟨1712348, by rfl⟩ : syracuseStep 2283131 = 3424697) B3424697
theorem B16457141 : Blo 2281435 16457141 := bbase (se 5 (by rfl) ⟨771428, by rfl⟩ : syracuseStep 16457141 = 1542857) (by norm_num)
theorem B43885709 : Blo 2281435 43885709 := bstep (se 3 (by rfl) ⟨8228570, by rfl⟩ : syracuseStep 43885709 = 16457141) B16457141
theorem B29257139 : Blo 2281435 29257139 := bstep (se 1 (by rfl) ⟨21942854, by rfl⟩ : syracuseStep 29257139 = 43885709) B43885709
theorem B19504759 : Blo 2281435 19504759 := bstep (se 1 (by rfl) ⟨14628569, by rfl⟩ : syracuseStep 19504759 = 29257139) B29257139
theorem B26006345 : Blo 2281435 26006345 := bstep (se 2 (by rfl) ⟨9752379, by rfl⟩ : syracuseStep 26006345 = 19504759) B19504759
theorem B17337563 : Blo 2281435 17337563 := bstep (se 1 (by rfl) ⟨13003172, by rfl⟩ : syracuseStep 17337563 = 26006345) B26006345
theorem B11558375 : Blo 2281435 11558375 := bstep (se 1 (by rfl) ⟨8668781, by rfl⟩ : syracuseStep 11558375 = 17337563) B17337563
theorem B7705583 : Blo 2281435 7705583 := bstep (se 1 (by rfl) ⟨5779187, by rfl⟩ : syracuseStep 7705583 = 11558375) B11558375
theorem B5137055 : Blo 2281435 5137055 := bstep (se 1 (by rfl) ⟨3852791, by rfl⟩ : syracuseStep 5137055 = 7705583) B7705583
theorem B3424703 : Blo 2281435 3424703 := bstep (se 1 (by rfl) ⟨2568527, by rfl⟩ : syracuseStep 3424703 = 5137055) B5137055
theorem B2283135 : Blo 2281435 2283135 := bstep (se 1 (by rfl) ⟨1712351, by rfl⟩ : syracuseStep 2283135 = 3424703) B3424703
theorem B3424709 : Blo 2281435 3424709 := bbase (se 4 (by rfl) ⟨321066, by rfl⟩ : syracuseStep 3424709 = 642133) (by norm_num)
theorem B2283139 : Blo 2281435 2283139 := bstep (se 1 (by rfl) ⟨1712354, by rfl⟩ : syracuseStep 2283139 = 3424709) B3424709
theorem B3852805 : Blo 2281435 3852805 := bbase (se 4 (by rfl) ⟨361200, by rfl⟩ : syracuseStep 3852805 = 722401) (by norm_num)
theorem B5137073 : Blo 2281435 5137073 := bstep (se 2 (by rfl) ⟨1926402, by rfl⟩ : syracuseStep 5137073 = 3852805) B3852805
theorem B3424715 : Blo 2281435 3424715 := bstep (se 1 (by rfl) ⟨2568536, by rfl⟩ : syracuseStep 3424715 = 5137073) B5137073
theorem B2283143 : Blo 2281435 2283143 := bstep (se 1 (by rfl) ⟨1712357, by rfl⟩ : syracuseStep 2283143 = 3424715) B3424715
theorem B2568541 : Blo 2281435 2568541 := bbase (se 3 (by rfl) ⟨481601, by rfl⟩ : syracuseStep 2568541 = 963203) (by norm_num)
theorem B3424721 : Blo 2281435 3424721 := bstep (se 2 (by rfl) ⟨1284270, by rfl⟩ : syracuseStep 3424721 = 2568541) B2568541
theorem B2283147 : Blo 2281435 2283147 := bstep (se 1 (by rfl) ⟨1712360, by rfl⟩ : syracuseStep 2283147 = 3424721) B3424721
theorem B7705637 : Blo 2281435 7705637 := bbase (se 4 (by rfl) ⟨722403, by rfl⟩ : syracuseStep 7705637 = 1444807) (by norm_num)
theorem B5137091 : Blo 2281435 5137091 := bstep (se 1 (by rfl) ⟨3852818, by rfl⟩ : syracuseStep 5137091 = 7705637) B7705637
theorem B3424727 : Blo 2281435 3424727 := bstep (se 1 (by rfl) ⟨2568545, by rfl⟩ : syracuseStep 3424727 = 5137091) B5137091
theorem B2283151 : Blo 2281435 2283151 := bstep (se 1 (by rfl) ⟨1712363, by rfl⟩ : syracuseStep 2283151 = 3424727) B3424727
theorem B3424733 : Blo 2281435 3424733 := bbase (se 3 (by rfl) ⟨642137, by rfl⟩ : syracuseStep 3424733 = 1284275) (by norm_num)
theorem B2283155 : Blo 2281435 2283155 := bstep (se 1 (by rfl) ⟨1712366, by rfl⟩ : syracuseStep 2283155 = 3424733) B3424733
theorem B5137109 : Blo 2281435 5137109 := bbase (se 7 (by rfl) ⟨60200, by rfl⟩ : syracuseStep 5137109 = 120401) (by norm_num)
theorem B3424739 : Blo 2281435 3424739 := bstep (se 1 (by rfl) ⟨2568554, by rfl⟩ : syracuseStep 3424739 = 5137109) B5137109
theorem B2283159 : Blo 2281435 2283159 := bstep (se 1 (by rfl) ⟨1712369, by rfl⟩ : syracuseStep 2283159 = 3424739) B3424739
theorem B9752501 : Blo 2281435 9752501 := bbase (se 5 (by rfl) ⟨457148, by rfl⟩ : syracuseStep 9752501 = 914297) (by norm_num)
theorem B6501667 : Blo 2281435 6501667 := bstep (se 1 (by rfl) ⟨4876250, by rfl⟩ : syracuseStep 6501667 = 9752501) B9752501
theorem B8668889 : Blo 2281435 8668889 := bstep (se 2 (by rfl) ⟨3250833, by rfl⟩ : syracuseStep 8668889 = 6501667) B6501667
theorem B5779259 : Blo 2281435 5779259 := bstep (se 1 (by rfl) ⟨4334444, by rfl⟩ : syracuseStep 5779259 = 8668889) B8668889
theorem B3852839 : Blo 2281435 3852839 := bstep (se 1 (by rfl) ⟨2889629, by rfl⟩ : syracuseStep 3852839 = 5779259) B5779259
theorem B2568559 : Blo 2281435 2568559 := bstep (se 1 (by rfl) ⟨1926419, by rfl⟩ : syracuseStep 2568559 = 3852839) B3852839
theorem B3424745 : Blo 2281435 3424745 := bstep (se 2 (by rfl) ⟨1284279, by rfl⟩ : syracuseStep 3424745 = 2568559) B2568559
theorem B2283163 : Blo 2281435 2283163 := bstep (se 1 (by rfl) ⟨1712372, by rfl⟩ : syracuseStep 2283163 = 3424745) B3424745
theorem B3009529 : Blo 2281435 3009529 := bbase (se 2 (by rfl) ⟨1128573, by rfl⟩ : syracuseStep 3009529 = 2257147) (by norm_num)
theorem B4012705 : Blo 2281435 4012705 := bstep (se 2 (by rfl) ⟨1504764, by rfl⟩ : syracuseStep 4012705 = 3009529) B3009529
theorem B5350273 : Blo 2281435 5350273 := bstep (se 2 (by rfl) ⟨2006352, by rfl⟩ : syracuseStep 5350273 = 4012705) B4012705
theorem B28534789 : Blo 2281435 28534789 := bstep (se 4 (by rfl) ⟨2675136, by rfl⟩ : syracuseStep 28534789 = 5350273) B5350273
theorem B38046385 : Blo 2281435 38046385 := bstep (se 2 (by rfl) ⟨14267394, by rfl⟩ : syracuseStep 38046385 = 28534789) B28534789
theorem B50728513 : Blo 2281435 50728513 := bstep (se 2 (by rfl) ⟨19023192, by rfl⟩ : syracuseStep 50728513 = 38046385) B38046385
theorem B67638017 : Blo 2281435 67638017 := bstep (se 2 (by rfl) ⟨25364256, by rfl⟩ : syracuseStep 67638017 = 50728513) B50728513
theorem B45092011 : Blo 2281435 45092011 := bstep (se 1 (by rfl) ⟨33819008, by rfl⟩ : syracuseStep 45092011 = 67638017) B67638017
theorem B60122681 : Blo 2281435 60122681 := bstep (se 2 (by rfl) ⟨22546005, by rfl⟩ : syracuseStep 60122681 = 45092011) B45092011
theorem B40081787 : Blo 2281435 40081787 := bstep (se 1 (by rfl) ⟨30061340, by rfl⟩ : syracuseStep 40081787 = 60122681) B60122681
theorem B26721191 : Blo 2281435 26721191 := bstep (se 1 (by rfl) ⟨20040893, by rfl⟩ : syracuseStep 26721191 = 40081787) B40081787
theorem B17814127 : Blo 2281435 17814127 := bstep (se 1 (by rfl) ⟨13360595, by rfl⟩ : syracuseStep 17814127 = 26721191) B26721191
theorem B23752169 : Blo 2281435 23752169 := bstep (se 2 (by rfl) ⟨8907063, by rfl⟩ : syracuseStep 23752169 = 17814127) B17814127
theorem B15834779 : Blo 2281435 15834779 := bstep (se 1 (by rfl) ⟨11876084, by rfl⟩ : syracuseStep 15834779 = 23752169) B23752169
theorem B10556519 : Blo 2281435 10556519 := bstep (se 1 (by rfl) ⟨7917389, by rfl⟩ : syracuseStep 10556519 = 15834779) B15834779
theorem B112602869 : Blo 2281435 112602869 := bstep (se 5 (by rfl) ⟨5278259, by rfl⟩ : syracuseStep 112602869 = 10556519) B10556519
theorem B75068579 : Blo 2281435 75068579 := bstep (se 1 (by rfl) ⟨56301434, by rfl⟩ : syracuseStep 75068579 = 112602869) B112602869
theorem B200182877 : Blo 2281435 200182877 := bstep (se 3 (by rfl) ⟨37534289, by rfl⟩ : syracuseStep 200182877 = 75068579) B75068579
theorem B133455251 : Blo 2281435 133455251 := bstep (se 1 (by rfl) ⟨100091438, by rfl⟩ : syracuseStep 133455251 = 200182877) B200182877
theorem B88970167 : Blo 2281435 88970167 := bstep (se 1 (by rfl) ⟨66727625, by rfl⟩ : syracuseStep 88970167 = 133455251) B133455251
theorem B118626889 : Blo 2281435 118626889 := bstep (se 2 (by rfl) ⟨44485083, by rfl⟩ : syracuseStep 118626889 = 88970167) B88970167
theorem B158169185 : Blo 2281435 158169185 := bstep (se 2 (by rfl) ⟨59313444, by rfl⟩ : syracuseStep 158169185 = 118626889) B118626889
theorem B105446123 : Blo 2281435 105446123 := bstep (se 1 (by rfl) ⟨79084592, by rfl⟩ : syracuseStep 105446123 = 158169185) B158169185
theorem B70297415 : Blo 2281435 70297415 := bstep (se 1 (by rfl) ⟨52723061, by rfl⟩ : syracuseStep 70297415 = 105446123) B105446123
theorem B46864943 : Blo 2281435 46864943 := bstep (se 1 (by rfl) ⟨35148707, by rfl⟩ : syracuseStep 46864943 = 70297415) B70297415
theorem B31243295 : Blo 2281435 31243295 := bstep (se 1 (by rfl) ⟨23432471, by rfl⟩ : syracuseStep 31243295 = 46864943) B46864943
theorem B20828863 : Blo 2281435 20828863 := bstep (se 1 (by rfl) ⟨15621647, by rfl⟩ : syracuseStep 20828863 = 31243295) B31243295
theorem B27771817 : Blo 2281435 27771817 := bstep (se 2 (by rfl) ⟨10414431, by rfl⟩ : syracuseStep 27771817 = 20828863) B20828863
theorem B37029089 : Blo 2281435 37029089 := bstep (se 2 (by rfl) ⟨13885908, by rfl⟩ : syracuseStep 37029089 = 27771817) B27771817
theorem B24686059 : Blo 2281435 24686059 := bstep (se 1 (by rfl) ⟨18514544, by rfl⟩ : syracuseStep 24686059 = 37029089) B37029089
theorem B32914745 : Blo 2281435 32914745 := bstep (se 2 (by rfl) ⟨12343029, by rfl⟩ : syracuseStep 32914745 = 24686059) B24686059
theorem B21943163 : Blo 2281435 21943163 := bstep (se 1 (by rfl) ⟨16457372, by rfl⟩ : syracuseStep 21943163 = 32914745) B32914745
theorem B14628775 : Blo 2281435 14628775 := bstep (se 1 (by rfl) ⟨10971581, by rfl⟩ : syracuseStep 14628775 = 21943163) B21943163
theorem B19505033 : Blo 2281435 19505033 := bstep (se 2 (by rfl) ⟨7314387, by rfl⟩ : syracuseStep 19505033 = 14628775) B14628775
theorem B13003355 : Blo 2281435 13003355 := bstep (se 1 (by rfl) ⟨9752516, by rfl⟩ : syracuseStep 13003355 = 19505033) B19505033
theorem B8668903 : Blo 2281435 8668903 := bstep (se 1 (by rfl) ⟨6501677, by rfl⟩ : syracuseStep 8668903 = 13003355) B13003355
theorem B11558537 : Blo 2281435 11558537 := bstep (se 2 (by rfl) ⟨4334451, by rfl⟩ : syracuseStep 11558537 = 8668903) B8668903
theorem B7705691 : Blo 2281435 7705691 := bstep (se 1 (by rfl) ⟨5779268, by rfl⟩ : syracuseStep 7705691 = 11558537) B11558537
theorem B5137127 : Blo 2281435 5137127 := bstep (se 1 (by rfl) ⟨3852845, by rfl⟩ : syracuseStep 5137127 = 7705691) B7705691
theorem B3424751 : Blo 2281435 3424751 := bstep (se 1 (by rfl) ⟨2568563, by rfl⟩ : syracuseStep 3424751 = 5137127) B5137127
theorem B2283167 : Blo 2281435 2283167 := bstep (se 1 (by rfl) ⟨1712375, by rfl⟩ : syracuseStep 2283167 = 3424751) B3424751
theorem B3424757 : Blo 2281435 3424757 := bbase (se 5 (by rfl) ⟨160535, by rfl⟩ : syracuseStep 3424757 = 321071) (by norm_num)
theorem B2283171 : Blo 2281435 2283171 := bstep (se 1 (by rfl) ⟨1712378, by rfl⟩ : syracuseStep 2283171 = 3424757) B3424757
theorem B6501701 : Blo 2281435 6501701 := bbase (se 4 (by rfl) ⟨609534, by rfl⟩ : syracuseStep 6501701 = 1219069) (by norm_num)
theorem B4334467 : Blo 2281435 4334467 := bstep (se 1 (by rfl) ⟨3250850, by rfl⟩ : syracuseStep 4334467 = 6501701) B6501701
theorem B5779289 : Blo 2281435 5779289 := bstep (se 2 (by rfl) ⟨2167233, by rfl⟩ : syracuseStep 5779289 = 4334467) B4334467
theorem B3852859 : Blo 2281435 3852859 := bstep (se 1 (by rfl) ⟨2889644, by rfl⟩ : syracuseStep 3852859 = 5779289) B5779289
theorem B5137145 : Blo 2281435 5137145 := bstep (se 2 (by rfl) ⟨1926429, by rfl⟩ : syracuseStep 5137145 = 3852859) B3852859
theorem B3424763 : Blo 2281435 3424763 := bstep (se 1 (by rfl) ⟨2568572, by rfl⟩ : syracuseStep 3424763 = 5137145) B5137145
theorem B2283175 : Blo 2281435 2283175 := bstep (se 1 (by rfl) ⟨1712381, by rfl⟩ : syracuseStep 2283175 = 3424763) B3424763
theorem B2568577 : Blo 2281435 2568577 := bbase (se 2 (by rfl) ⟨963216, by rfl⟩ : syracuseStep 2568577 = 1926433) (by norm_num)
theorem B3424769 : Blo 2281435 3424769 := bstep (se 2 (by rfl) ⟨1284288, by rfl⟩ : syracuseStep 3424769 = 2568577) B2568577
theorem B2283179 : Blo 2281435 2283179 := bstep (se 1 (by rfl) ⟨1712384, by rfl⟩ : syracuseStep 2283179 = 3424769) B3424769
theorem B5779309 : Blo 2281435 5779309 := bbase (se 3 (by rfl) ⟨1083620, by rfl⟩ : syracuseStep 5779309 = 2167241) (by norm_num)
theorem B7705745 : Blo 2281435 7705745 := bstep (se 2 (by rfl) ⟨2889654, by rfl⟩ : syracuseStep 7705745 = 5779309) B5779309
theorem B5137163 : Blo 2281435 5137163 := bstep (se 1 (by rfl) ⟨3852872, by rfl⟩ : syracuseStep 5137163 = 7705745) B7705745
theorem B3424775 : Blo 2281435 3424775 := bstep (se 1 (by rfl) ⟨2568581, by rfl⟩ : syracuseStep 3424775 = 5137163) B5137163
theorem B2283183 : Blo 2281435 2283183 := bstep (se 1 (by rfl) ⟨1712387, by rfl⟩ : syracuseStep 2283183 = 3424775) B3424775
theorem B3424781 : Blo 2281435 3424781 := bbase (se 3 (by rfl) ⟨642146, by rfl⟩ : syracuseStep 3424781 = 1284293) (by norm_num)
theorem B2283187 : Blo 2281435 2283187 := bstep (se 1 (by rfl) ⟨1712390, by rfl⟩ : syracuseStep 2283187 = 3424781) B3424781
theorem B5137181 : Blo 2281435 5137181 := bbase (se 3 (by rfl) ⟨963221, by rfl⟩ : syracuseStep 5137181 = 1926443) (by norm_num)
theorem B3424787 : Blo 2281435 3424787 := bstep (se 1 (by rfl) ⟨2568590, by rfl⟩ : syracuseStep 3424787 = 5137181) B5137181
theorem B2283191 : Blo 2281435 2283191 := bstep (se 1 (by rfl) ⟨1712393, by rfl⟩ : syracuseStep 2283191 = 3424787) B3424787
theorem B3852893 : Blo 2281435 3852893 := bbase (se 3 (by rfl) ⟨722417, by rfl⟩ : syracuseStep 3852893 = 1444835) (by norm_num)
theorem B2568595 : Blo 2281435 2568595 := bstep (se 1 (by rfl) ⟨1926446, by rfl⟩ : syracuseStep 2568595 = 3852893) B3852893
theorem B3424793 : Blo 2281435 3424793 := bstep (se 2 (by rfl) ⟨1284297, by rfl⟩ : syracuseStep 3424793 = 2568595) B2568595
theorem B2283195 : Blo 2281435 2283195 := bstep (se 1 (by rfl) ⟨1712396, by rfl⟩ : syracuseStep 2283195 = 3424793) B3424793
theorem B3657245 : Blo 2281435 3657245 := bbase (se 3 (by rfl) ⟨685733, by rfl⟩ : syracuseStep 3657245 = 1371467) (by norm_num)
theorem B9752653 : Blo 2281435 9752653 := bstep (se 3 (by rfl) ⟨1828622, by rfl⟩ : syracuseStep 9752653 = 3657245) B3657245
theorem B13003537 : Blo 2281435 13003537 := bstep (se 2 (by rfl) ⟨4876326, by rfl⟩ : syracuseStep 13003537 = 9752653) B9752653
theorem B17338049 : Blo 2281435 17338049 := bstep (se 2 (by rfl) ⟨6501768, by rfl⟩ : syracuseStep 17338049 = 13003537) B13003537
theorem B11558699 : Blo 2281435 11558699 := bstep (se 1 (by rfl) ⟨8669024, by rfl⟩ : syracuseStep 11558699 = 17338049) B17338049
theorem B7705799 : Blo 2281435 7705799 := bstep (se 1 (by rfl) ⟨5779349, by rfl⟩ : syracuseStep 7705799 = 11558699) B11558699
theorem B5137199 : Blo 2281435 5137199 := bstep (se 1 (by rfl) ⟨3852899, by rfl⟩ : syracuseStep 5137199 = 7705799) B7705799
theorem B3424799 : Blo 2281435 3424799 := bstep (se 1 (by rfl) ⟨2568599, by rfl⟩ : syracuseStep 3424799 = 5137199) B5137199
theorem B2283199 : Blo 2281435 2283199 := bstep (se 1 (by rfl) ⟨1712399, by rfl⟩ : syracuseStep 2283199 = 3424799) B3424799
theorem B3424805 : Blo 2281435 3424805 := bbase (se 4 (by rfl) ⟨321075, by rfl⟩ : syracuseStep 3424805 = 642151) (by norm_num)
theorem B2283203 : Blo 2281435 2283203 := bstep (se 1 (by rfl) ⟨1712402, by rfl⟩ : syracuseStep 2283203 = 3424805) B3424805
theorem B2889685 : Blo 2281435 2889685 := bbase (se 7 (by rfl) ⟨33863, by rfl⟩ : syracuseStep 2889685 = 67727) (by norm_num)
theorem B3852913 : Blo 2281435 3852913 := bstep (se 2 (by rfl) ⟨1444842, by rfl⟩ : syracuseStep 3852913 = 2889685) B2889685
theorem B5137217 : Blo 2281435 5137217 := bstep (se 2 (by rfl) ⟨1926456, by rfl⟩ : syracuseStep 5137217 = 3852913) B3852913
theorem B3424811 : Blo 2281435 3424811 := bstep (se 1 (by rfl) ⟨2568608, by rfl⟩ : syracuseStep 3424811 = 5137217) B5137217
theorem B2283207 : Blo 2281435 2283207 := bstep (se 1 (by rfl) ⟨1712405, by rfl⟩ : syracuseStep 2283207 = 3424811) B3424811
theorem B2568613 : Blo 2281435 2568613 := bbase (se 4 (by rfl) ⟨240807, by rfl⟩ : syracuseStep 2568613 = 481615) (by norm_num)
theorem B3424817 : Blo 2281435 3424817 := bstep (se 2 (by rfl) ⟨1284306, by rfl⟩ : syracuseStep 3424817 = 2568613) B2568613
theorem B2283211 : Blo 2281435 2283211 := bstep (se 1 (by rfl) ⟨1712408, by rfl⟩ : syracuseStep 2283211 = 3424817) B3424817
theorem B79086293 : Blo 2281435 79086293 := bbase (se 7 (by rfl) ⟨926792, by rfl⟩ : syracuseStep 79086293 = 1853585) (by norm_num)
theorem B52724195 : Blo 2281435 52724195 := bstep (se 1 (by rfl) ⟨39543146, by rfl⟩ : syracuseStep 52724195 = 79086293) B79086293
theorem B35149463 : Blo 2281435 35149463 := bstep (se 1 (by rfl) ⟨26362097, by rfl⟩ : syracuseStep 35149463 = 52724195) B52724195
theorem B23432975 : Blo 2281435 23432975 := bstep (se 1 (by rfl) ⟨17574731, by rfl⟩ : syracuseStep 23432975 = 35149463) B35149463
theorem B15621983 : Blo 2281435 15621983 := bstep (se 1 (by rfl) ⟨11716487, by rfl⟩ : syracuseStep 15621983 = 23432975) B23432975
theorem B10414655 : Blo 2281435 10414655 := bstep (se 1 (by rfl) ⟨7810991, by rfl⟩ : syracuseStep 10414655 = 15621983) B15621983
theorem B6943103 : Blo 2281435 6943103 := bstep (se 1 (by rfl) ⟨5207327, by rfl⟩ : syracuseStep 6943103 = 10414655) B10414655
theorem B4628735 : Blo 2281435 4628735 := bstep (se 1 (by rfl) ⟨3471551, by rfl⟩ : syracuseStep 4628735 = 6943103) B6943103
theorem B3085823 : Blo 2281435 3085823 := bstep (se 1 (by rfl) ⟨2314367, by rfl⟩ : syracuseStep 3085823 = 4628735) B4628735
theorem B8228861 : Blo 2281435 8228861 := bstep (se 3 (by rfl) ⟨1542911, by rfl⟩ : syracuseStep 8228861 = 3085823) B3085823
theorem B5485907 : Blo 2281435 5485907 := bstep (se 1 (by rfl) ⟨4114430, by rfl⟩ : syracuseStep 5485907 = 8228861) B8228861
theorem B14629085 : Blo 2281435 14629085 := bstep (se 3 (by rfl) ⟨2742953, by rfl⟩ : syracuseStep 14629085 = 5485907) B5485907
theorem B9752723 : Blo 2281435 9752723 := bstep (se 1 (by rfl) ⟨7314542, by rfl⟩ : syracuseStep 9752723 = 14629085) B14629085
theorem B6501815 : Blo 2281435 6501815 := bstep (se 1 (by rfl) ⟨4876361, by rfl⟩ : syracuseStep 6501815 = 9752723) B9752723
theorem B4334543 : Blo 2281435 4334543 := bstep (se 1 (by rfl) ⟨3250907, by rfl⟩ : syracuseStep 4334543 = 6501815) B6501815
theorem B2889695 : Blo 2281435 2889695 := bstep (se 1 (by rfl) ⟨2167271, by rfl⟩ : syracuseStep 2889695 = 4334543) B4334543
theorem B7705853 : Blo 2281435 7705853 := bstep (se 3 (by rfl) ⟨1444847, by rfl⟩ : syracuseStep 7705853 = 2889695) B2889695
theorem B5137235 : Blo 2281435 5137235 := bstep (se 1 (by rfl) ⟨3852926, by rfl⟩ : syracuseStep 5137235 = 7705853) B7705853
theorem B3424823 : Blo 2281435 3424823 := bstep (se 1 (by rfl) ⟨2568617, by rfl⟩ : syracuseStep 3424823 = 5137235) B5137235
theorem B2283215 : Blo 2281435 2283215 := bstep (se 1 (by rfl) ⟨1712411, by rfl⟩ : syracuseStep 2283215 = 3424823) B3424823
theorem B3424829 : Blo 2281435 3424829 := bbase (se 3 (by rfl) ⟨642155, by rfl⟩ : syracuseStep 3424829 = 1284311) (by norm_num)
theorem B2283219 : Blo 2281435 2283219 := bstep (se 1 (by rfl) ⟨1712414, by rfl⟩ : syracuseStep 2283219 = 3424829) B3424829
theorem B5137253 : Blo 2281435 5137253 := bbase (se 4 (by rfl) ⟨481617, by rfl⟩ : syracuseStep 5137253 = 963235) (by norm_num)
theorem B3424835 : Blo 2281435 3424835 := bstep (se 1 (by rfl) ⟨2568626, by rfl⟩ : syracuseStep 3424835 = 5137253) B5137253
theorem B2283223 : Blo 2281435 2283223 := bstep (se 1 (by rfl) ⟨1712417, by rfl⟩ : syracuseStep 2283223 = 3424835) B3424835
theorem B5779421 : Blo 2281435 5779421 := bbase (se 3 (by rfl) ⟨1083641, by rfl⟩ : syracuseStep 5779421 = 2167283) (by norm_num)
theorem B3852947 : Blo 2281435 3852947 := bstep (se 1 (by rfl) ⟨2889710, by rfl⟩ : syracuseStep 3852947 = 5779421) B5779421
theorem B2568631 : Blo 2281435 2568631 := bstep (se 1 (by rfl) ⟨1926473, by rfl⟩ : syracuseStep 2568631 = 3852947) B3852947
theorem B3424841 : Blo 2281435 3424841 := bstep (se 2 (by rfl) ⟨1284315, by rfl⟩ : syracuseStep 3424841 = 2568631) B2568631
theorem B2283227 : Blo 2281435 2283227 := bstep (se 1 (by rfl) ⟨1712420, by rfl⟩ : syracuseStep 2283227 = 3424841) B3424841
theorem B4334573 : Blo 2281435 4334573 := bbase (se 3 (by rfl) ⟨812732, by rfl⟩ : syracuseStep 4334573 = 1625465) (by norm_num)
theorem B11558861 : Blo 2281435 11558861 := bstep (se 3 (by rfl) ⟨2167286, by rfl⟩ : syracuseStep 11558861 = 4334573) B4334573
theorem B7705907 : Blo 2281435 7705907 := bstep (se 1 (by rfl) ⟨5779430, by rfl⟩ : syracuseStep 7705907 = 11558861) B11558861
theorem B5137271 : Blo 2281435 5137271 := bstep (se 1 (by rfl) ⟨3852953, by rfl⟩ : syracuseStep 5137271 = 7705907) B7705907
theorem B3424847 : Blo 2281435 3424847 := bstep (se 1 (by rfl) ⟨2568635, by rfl⟩ : syracuseStep 3424847 = 5137271) B5137271
theorem B2283231 : Blo 2281435 2283231 := bstep (se 1 (by rfl) ⟨1712423, by rfl⟩ : syracuseStep 2283231 = 3424847) B3424847
theorem B3424853 : Blo 2281435 3424853 := bbase (se 8 (by rfl) ⟨20067, by rfl⟩ : syracuseStep 3424853 = 40135) (by norm_num)
theorem B2283235 : Blo 2281435 2283235 := bstep (se 1 (by rfl) ⟨1712426, by rfl⟩ : syracuseStep 2283235 = 3424853) B3424853
theorem B2345969 : Blo 2281435 2345969 := bbase (se 2 (by rfl) ⟨879738, by rfl⟩ : syracuseStep 2345969 = 1759477) (by norm_num)
theorem B6255917 : Blo 2281435 6255917 := bstep (se 3 (by rfl) ⟨1172984, by rfl⟩ : syracuseStep 6255917 = 2345969) B2345969
theorem B4170611 : Blo 2281435 4170611 := bstep (se 1 (by rfl) ⟨3127958, by rfl⟩ : syracuseStep 4170611 = 6255917) B6255917
theorem B2780407 : Blo 2281435 2780407 := bstep (se 1 (by rfl) ⟨2085305, by rfl⟩ : syracuseStep 2780407 = 4170611) B4170611
theorem B3707209 : Blo 2281435 3707209 := bstep (se 2 (by rfl) ⟨1390203, by rfl⟩ : syracuseStep 3707209 = 2780407) B2780407
theorem B4942945 : Blo 2281435 4942945 := bstep (se 2 (by rfl) ⟨1853604, by rfl⟩ : syracuseStep 4942945 = 3707209) B3707209
theorem B6590593 : Blo 2281435 6590593 := bstep (se 2 (by rfl) ⟨2471472, by rfl⟩ : syracuseStep 6590593 = 4942945) B4942945
theorem B8787457 : Blo 2281435 8787457 := bstep (se 2 (by rfl) ⟨3295296, by rfl⟩ : syracuseStep 8787457 = 6590593) B6590593
theorem B11716609 : Blo 2281435 11716609 := bstep (se 2 (by rfl) ⟨4393728, by rfl⟩ : syracuseStep 11716609 = 8787457) B8787457
theorem B15622145 : Blo 2281435 15622145 := bstep (se 2 (by rfl) ⟨5858304, by rfl⟩ : syracuseStep 15622145 = 11716609) B11716609
theorem B10414763 : Blo 2281435 10414763 := bstep (se 1 (by rfl) ⟨7811072, by rfl⟩ : syracuseStep 10414763 = 15622145) B15622145
theorem B6943175 : Blo 2281435 6943175 := bstep (se 1 (by rfl) ⟨5207381, by rfl⟩ : syracuseStep 6943175 = 10414763) B10414763
theorem B4628783 : Blo 2281435 4628783 := bstep (se 1 (by rfl) ⟨3471587, by rfl⟩ : syracuseStep 4628783 = 6943175) B6943175
theorem B12343421 : Blo 2281435 12343421 := bstep (se 3 (by rfl) ⟨2314391, by rfl⟩ : syracuseStep 12343421 = 4628783) B4628783
theorem B8228947 : Blo 2281435 8228947 := bstep (se 1 (by rfl) ⟨6171710, by rfl⟩ : syracuseStep 8228947 = 12343421) B12343421
theorem B10971929 : Blo 2281435 10971929 := bstep (se 2 (by rfl) ⟨4114473, by rfl⟩ : syracuseStep 10971929 = 8228947) B8228947
theorem B7314619 : Blo 2281435 7314619 := bstep (se 1 (by rfl) ⟨5485964, by rfl⟩ : syracuseStep 7314619 = 10971929) B10971929
theorem B9752825 : Blo 2281435 9752825 := bstep (se 2 (by rfl) ⟨3657309, by rfl⟩ : syracuseStep 9752825 = 7314619) B7314619
theorem B6501883 : Blo 2281435 6501883 := bstep (se 1 (by rfl) ⟨4876412, by rfl⟩ : syracuseStep 6501883 = 9752825) B9752825
theorem B8669177 : Blo 2281435 8669177 := bstep (se 2 (by rfl) ⟨3250941, by rfl⟩ : syracuseStep 8669177 = 6501883) B6501883
theorem B5779451 : Blo 2281435 5779451 := bstep (se 1 (by rfl) ⟨4334588, by rfl⟩ : syracuseStep 5779451 = 8669177) B8669177
theorem B3852967 : Blo 2281435 3852967 := bstep (se 1 (by rfl) ⟨2889725, by rfl⟩ : syracuseStep 3852967 = 5779451) B5779451
theorem B5137289 : Blo 2281435 5137289 := bstep (se 2 (by rfl) ⟨1926483, by rfl⟩ : syracuseStep 5137289 = 3852967) B3852967
theorem B3424859 : Blo 2281435 3424859 := bstep (se 1 (by rfl) ⟨2568644, by rfl⟩ : syracuseStep 3424859 = 5137289) B5137289
theorem B2283239 : Blo 2281435 2283239 := bstep (se 1 (by rfl) ⟨1712429, by rfl⟩ : syracuseStep 2283239 = 3424859) B3424859
theorem B2568649 : Blo 2281435 2568649 := bbase (se 2 (by rfl) ⟨963243, by rfl⟩ : syracuseStep 2568649 = 1926487) (by norm_num)
theorem B3424865 : Blo 2281435 3424865 := bstep (se 2 (by rfl) ⟨1284324, by rfl⟩ : syracuseStep 3424865 = 2568649) B2568649
theorem B2283243 : Blo 2281435 2283243 := bstep (se 1 (by rfl) ⟨1712432, by rfl⟩ : syracuseStep 2283243 = 3424865) B3424865
theorem B19505717 : Blo 2281435 19505717 := bbase (se 5 (by rfl) ⟨914330, by rfl⟩ : syracuseStep 19505717 = 1828661) (by norm_num)
theorem B13003811 : Blo 2281435 13003811 := bstep (se 1 (by rfl) ⟨9752858, by rfl⟩ : syracuseStep 13003811 = 19505717) B19505717
theorem B8669207 : Blo 2281435 8669207 := bstep (se 1 (by rfl) ⟨6501905, by rfl⟩ : syracuseStep 8669207 = 13003811) B13003811
theorem B5779471 : Blo 2281435 5779471 := bstep (se 1 (by rfl) ⟨4334603, by rfl⟩ : syracuseStep 5779471 = 8669207) B8669207
theorem B7705961 : Blo 2281435 7705961 := bstep (se 2 (by rfl) ⟨2889735, by rfl⟩ : syracuseStep 7705961 = 5779471) B5779471
theorem B5137307 : Blo 2281435 5137307 := bstep (se 1 (by rfl) ⟨3852980, by rfl⟩ : syracuseStep 5137307 = 7705961) B7705961
theorem B3424871 : Blo 2281435 3424871 := bstep (se 1 (by rfl) ⟨2568653, by rfl⟩ : syracuseStep 3424871 = 5137307) B5137307
theorem B2283247 : Blo 2281435 2283247 := bstep (se 1 (by rfl) ⟨1712435, by rfl⟩ : syracuseStep 2283247 = 3424871) B3424871
theorem B3424877 : Blo 2281435 3424877 := bbase (se 3 (by rfl) ⟨642164, by rfl⟩ : syracuseStep 3424877 = 1284329) (by norm_num)
theorem B2283251 : Blo 2281435 2283251 := bstep (se 1 (by rfl) ⟨1712438, by rfl⟩ : syracuseStep 2283251 = 3424877) B3424877
theorem B5137325 : Blo 2281435 5137325 := bbase (se 3 (by rfl) ⟨963248, by rfl⟩ : syracuseStep 5137325 = 1926497) (by norm_num)
theorem B3424883 : Blo 2281435 3424883 := bstep (se 1 (by rfl) ⟨2568662, by rfl⟩ : syracuseStep 3424883 = 5137325) B5137325
theorem B2283255 : Blo 2281435 2283255 := bstep (se 1 (by rfl) ⟨1712441, by rfl⟩ : syracuseStep 2283255 = 3424883) B3424883
theorem B6501941 : Blo 2281435 6501941 := bbase (se 5 (by rfl) ⟨304778, by rfl⟩ : syracuseStep 6501941 = 609557) (by norm_num)
theorem B4334627 : Blo 2281435 4334627 := bstep (se 1 (by rfl) ⟨3250970, by rfl⟩ : syracuseStep 4334627 = 6501941) B6501941
theorem B2889751 : Blo 2281435 2889751 := bstep (se 1 (by rfl) ⟨2167313, by rfl⟩ : syracuseStep 2889751 = 4334627) B4334627
theorem B3853001 : Blo 2281435 3853001 := bstep (se 2 (by rfl) ⟨1444875, by rfl⟩ : syracuseStep 3853001 = 2889751) B2889751
theorem B2568667 : Blo 2281435 2568667 := bstep (se 1 (by rfl) ⟨1926500, by rfl⟩ : syracuseStep 2568667 = 3853001) B3853001
theorem B3424889 : Blo 2281435 3424889 := bstep (se 2 (by rfl) ⟨1284333, by rfl⟩ : syracuseStep 3424889 = 2568667) B2568667
theorem B2283259 : Blo 2281435 2283259 := bstep (se 1 (by rfl) ⟨1712444, by rfl⟩ : syracuseStep 2283259 = 3424889) B3424889
theorem B15835445 : Blo 2281435 15835445 := bbase (se 5 (by rfl) ⟨742286, by rfl⟩ : syracuseStep 15835445 = 1484573) (by norm_num)
theorem B10556963 : Blo 2281435 10556963 := bstep (se 1 (by rfl) ⟨7917722, by rfl⟩ : syracuseStep 10556963 = 15835445) B15835445
theorem B7037975 : Blo 2281435 7037975 := bstep (se 1 (by rfl) ⟨5278481, by rfl⟩ : syracuseStep 7037975 = 10556963) B10556963
theorem B18767933 : Blo 2281435 18767933 := bstep (se 3 (by rfl) ⟨3518987, by rfl⟩ : syracuseStep 18767933 = 7037975) B7037975
theorem B12511955 : Blo 2281435 12511955 := bstep (se 1 (by rfl) ⟨9383966, by rfl⟩ : syracuseStep 12511955 = 18767933) B18767933
theorem B33365213 : Blo 2281435 33365213 := bstep (se 3 (by rfl) ⟨6255977, by rfl⟩ : syracuseStep 33365213 = 12511955) B12511955
theorem B22243475 : Blo 2281435 22243475 := bstep (se 1 (by rfl) ⟨16682606, by rfl⟩ : syracuseStep 22243475 = 33365213) B33365213
theorem B14828983 : Blo 2281435 14828983 := bstep (se 1 (by rfl) ⟨11121737, by rfl⟩ : syracuseStep 14828983 = 22243475) B22243475
theorem B79087909 : Blo 2281435 79087909 := bstep (se 4 (by rfl) ⟨7414491, by rfl⟩ : syracuseStep 79087909 = 14828983) B14828983
theorem B105450545 : Blo 2281435 105450545 := bstep (se 2 (by rfl) ⟨39543954, by rfl⟩ : syracuseStep 105450545 = 79087909) B79087909
theorem B281201453 : Blo 2281435 281201453 := bstep (se 3 (by rfl) ⟨52725272, by rfl⟩ : syracuseStep 281201453 = 105450545) B105450545
theorem B187467635 : Blo 2281435 187467635 := bstep (se 1 (by rfl) ⟨140600726, by rfl⟩ : syracuseStep 187467635 = 281201453) B281201453
theorem B124978423 : Blo 2281435 124978423 := bstep (se 1 (by rfl) ⟨93733817, by rfl⟩ : syracuseStep 124978423 = 187467635) B187467635
theorem B166637897 : Blo 2281435 166637897 := bstep (se 2 (by rfl) ⟨62489211, by rfl⟩ : syracuseStep 166637897 = 124978423) B124978423
theorem B111091931 : Blo 2281435 111091931 := bstep (se 1 (by rfl) ⟨83318948, by rfl⟩ : syracuseStep 111091931 = 166637897) B166637897
theorem B74061287 : Blo 2281435 74061287 := bstep (se 1 (by rfl) ⟨55545965, by rfl⟩ : syracuseStep 74061287 = 111091931) B111091931
theorem B49374191 : Blo 2281435 49374191 := bstep (se 1 (by rfl) ⟨37030643, by rfl⟩ : syracuseStep 49374191 = 74061287) B74061287
theorem B32916127 : Blo 2281435 32916127 := bstep (se 1 (by rfl) ⟨24687095, by rfl⟩ : syracuseStep 32916127 = 49374191) B49374191
theorem B43888169 : Blo 2281435 43888169 := bstep (se 2 (by rfl) ⟨16458063, by rfl⟩ : syracuseStep 43888169 = 32916127) B32916127
theorem B29258779 : Blo 2281435 29258779 := bstep (se 1 (by rfl) ⟨21944084, by rfl⟩ : syracuseStep 29258779 = 43888169) B43888169
theorem B39011705 : Blo 2281435 39011705 := bstep (se 2 (by rfl) ⟨14629389, by rfl⟩ : syracuseStep 39011705 = 29258779) B29258779
theorem B26007803 : Blo 2281435 26007803 := bstep (se 1 (by rfl) ⟨19505852, by rfl⟩ : syracuseStep 26007803 = 39011705) B39011705
theorem B17338535 : Blo 2281435 17338535 := bstep (se 1 (by rfl) ⟨13003901, by rfl⟩ : syracuseStep 17338535 = 26007803) B26007803
theorem B11559023 : Blo 2281435 11559023 := bstep (se 1 (by rfl) ⟨8669267, by rfl⟩ : syracuseStep 11559023 = 17338535) B17338535
theorem B7706015 : Blo 2281435 7706015 := bstep (se 1 (by rfl) ⟨5779511, by rfl⟩ : syracuseStep 7706015 = 11559023) B11559023
theorem B5137343 : Blo 2281435 5137343 := bstep (se 1 (by rfl) ⟨3853007, by rfl⟩ : syracuseStep 5137343 = 7706015) B7706015
theorem B3424895 : Blo 2281435 3424895 := bstep (se 1 (by rfl) ⟨2568671, by rfl⟩ : syracuseStep 3424895 = 5137343) B5137343
theorem B2283263 : Blo 2281435 2283263 := bstep (se 1 (by rfl) ⟨1712447, by rfl⟩ : syracuseStep 2283263 = 3424895) B3424895
theorem B3424901 : Blo 2281435 3424901 := bbase (se 4 (by rfl) ⟨321084, by rfl⟩ : syracuseStep 3424901 = 642169) (by norm_num)
theorem B2283267 : Blo 2281435 2283267 := bstep (se 1 (by rfl) ⟨1712450, by rfl⟩ : syracuseStep 2283267 = 3424901) B3424901
theorem B3853021 : Blo 2281435 3853021 := bbase (se 3 (by rfl) ⟨722441, by rfl⟩ : syracuseStep 3853021 = 1444883) (by norm_num)
theorem B5137361 : Blo 2281435 5137361 := bstep (se 2 (by rfl) ⟨1926510, by rfl⟩ : syracuseStep 5137361 = 3853021) B3853021
theorem B3424907 : Blo 2281435 3424907 := bstep (se 1 (by rfl) ⟨2568680, by rfl⟩ : syracuseStep 3424907 = 5137361) B5137361
theorem B2283271 : Blo 2281435 2283271 := bstep (se 1 (by rfl) ⟨1712453, by rfl⟩ : syracuseStep 2283271 = 3424907) B3424907
theorem B2568685 : Blo 2281435 2568685 := bbase (se 3 (by rfl) ⟨481628, by rfl⟩ : syracuseStep 2568685 = 963257) (by norm_num)
theorem B3424913 : Blo 2281435 3424913 := bstep (se 2 (by rfl) ⟨1284342, by rfl⟩ : syracuseStep 3424913 = 2568685) B2568685
theorem B2283275 : Blo 2281435 2283275 := bstep (se 1 (by rfl) ⟨1712456, by rfl⟩ : syracuseStep 2283275 = 3424913) B3424913
theorem B7706069 : Blo 2281435 7706069 := bbase (se 7 (by rfl) ⟨90305, by rfl⟩ : syracuseStep 7706069 = 180611) (by norm_num)
theorem B5137379 : Blo 2281435 5137379 := bstep (se 1 (by rfl) ⟨3853034, by rfl⟩ : syracuseStep 5137379 = 7706069) B7706069
theorem B3424919 : Blo 2281435 3424919 := bstep (se 1 (by rfl) ⟨2568689, by rfl⟩ : syracuseStep 3424919 = 5137379) B5137379
theorem B2283279 : Blo 2281435 2283279 := bstep (se 1 (by rfl) ⟨1712459, by rfl⟩ : syracuseStep 2283279 = 3424919) B3424919
theorem B3424925 : Blo 2281435 3424925 := bbase (se 3 (by rfl) ⟨642173, by rfl⟩ : syracuseStep 3424925 = 1284347) (by norm_num)
theorem B2283283 : Blo 2281435 2283283 := bstep (se 1 (by rfl) ⟨1712462, by rfl⟩ : syracuseStep 2283283 = 3424925) B3424925
theorem B5137397 : Blo 2281435 5137397 := bbase (se 5 (by rfl) ⟨240815, by rfl⟩ : syracuseStep 5137397 = 481631) (by norm_num)
theorem B3424931 : Blo 2281435 3424931 := bstep (se 1 (by rfl) ⟨2568698, by rfl⟩ : syracuseStep 3424931 = 5137397) B5137397
theorem B2283287 : Blo 2281435 2283287 := bstep (se 1 (by rfl) ⟨1712465, by rfl⟩ : syracuseStep 2283287 = 3424931) B3424931
theorem B49374805 : Blo 2281435 49374805 := bbase (se 8 (by rfl) ⟨289305, by rfl⟩ : syracuseStep 49374805 = 578611) (by norm_num)
theorem B65833073 : Blo 2281435 65833073 := bstep (se 2 (by rfl) ⟨24687402, by rfl⟩ : syracuseStep 65833073 = 49374805) B49374805
theorem B43888715 : Blo 2281435 43888715 := bstep (se 1 (by rfl) ⟨32916536, by rfl⟩ : syracuseStep 43888715 = 65833073) B65833073
theorem B29259143 : Blo 2281435 29259143 := bstep (se 1 (by rfl) ⟨21944357, by rfl⟩ : syracuseStep 29259143 = 43888715) B43888715
theorem B19506095 : Blo 2281435 19506095 := bstep (se 1 (by rfl) ⟨14629571, by rfl⟩ : syracuseStep 19506095 = 29259143) B29259143
theorem B13004063 : Blo 2281435 13004063 := bstep (se 1 (by rfl) ⟨9753047, by rfl⟩ : syracuseStep 13004063 = 19506095) B19506095
theorem B8669375 : Blo 2281435 8669375 := bstep (se 1 (by rfl) ⟨6502031, by rfl⟩ : syracuseStep 8669375 = 13004063) B13004063
theorem B5779583 : Blo 2281435 5779583 := bstep (se 1 (by rfl) ⟨4334687, by rfl⟩ : syracuseStep 5779583 = 8669375) B8669375
theorem B3853055 : Blo 2281435 3853055 := bstep (se 1 (by rfl) ⟨2889791, by rfl⟩ : syracuseStep 3853055 = 5779583) B5779583
theorem B2568703 : Blo 2281435 2568703 := bstep (se 1 (by rfl) ⟨1926527, by rfl⟩ : syracuseStep 2568703 = 3853055) B3853055
theorem B3424937 : Blo 2281435 3424937 := bstep (se 2 (by rfl) ⟨1284351, by rfl⟩ : syracuseStep 3424937 = 2568703) B2568703
theorem B2283291 : Blo 2281435 2283291 := bstep (se 1 (by rfl) ⟨1712468, by rfl⟩ : syracuseStep 2283291 = 3424937) B3424937
theorem B3251021 : Blo 2281435 3251021 := bbase (se 3 (by rfl) ⟨609566, by rfl⟩ : syracuseStep 3251021 = 1219133) (by norm_num)
theorem B8669389 : Blo 2281435 8669389 := bstep (se 3 (by rfl) ⟨1625510, by rfl⟩ : syracuseStep 8669389 = 3251021) B3251021
theorem B11559185 : Blo 2281435 11559185 := bstep (se 2 (by rfl) ⟨4334694, by rfl⟩ : syracuseStep 11559185 = 8669389) B8669389
theorem B7706123 : Blo 2281435 7706123 := bstep (se 1 (by rfl) ⟨5779592, by rfl⟩ : syracuseStep 7706123 = 11559185) B11559185
theorem B5137415 : Blo 2281435 5137415 := bstep (se 1 (by rfl) ⟨3853061, by rfl⟩ : syracuseStep 5137415 = 7706123) B7706123
theorem B3424943 : Blo 2281435 3424943 := bstep (se 1 (by rfl) ⟨2568707, by rfl⟩ : syracuseStep 3424943 = 5137415) B5137415
theorem B2283295 : Blo 2281435 2283295 := bstep (se 1 (by rfl) ⟨1712471, by rfl⟩ : syracuseStep 2283295 = 3424943) B3424943
theorem B3424949 : Blo 2281435 3424949 := bbase (se 5 (by rfl) ⟨160544, by rfl⟩ : syracuseStep 3424949 = 321089) (by norm_num)
theorem B2283299 : Blo 2281435 2283299 := bstep (se 1 (by rfl) ⟨1712474, by rfl⟩ : syracuseStep 2283299 = 3424949) B3424949
theorem B5779613 : Blo 2281435 5779613 := bbase (se 3 (by rfl) ⟨1083677, by rfl⟩ : syracuseStep 5779613 = 2167355) (by norm_num)
theorem B3853075 : Blo 2281435 3853075 := bstep (se 1 (by rfl) ⟨2889806, by rfl⟩ : syracuseStep 3853075 = 5779613) B5779613
theorem B5137433 : Blo 2281435 5137433 := bstep (se 2 (by rfl) ⟨1926537, by rfl⟩ : syracuseStep 5137433 = 3853075) B3853075
theorem B3424955 : Blo 2281435 3424955 := bstep (se 1 (by rfl) ⟨2568716, by rfl⟩ : syracuseStep 3424955 = 5137433) B5137433
theorem B2283303 : Blo 2281435 2283303 := bstep (se 1 (by rfl) ⟨1712477, by rfl⟩ : syracuseStep 2283303 = 3424955) B3424955
theorem B2568721 : Blo 2281435 2568721 := bbase (se 2 (by rfl) ⟨963270, by rfl⟩ : syracuseStep 2568721 = 1926541) (by norm_num)
theorem B3424961 : Blo 2281435 3424961 := bstep (se 2 (by rfl) ⟨1284360, by rfl⟩ : syracuseStep 3424961 = 2568721) B2568721
theorem B2283307 : Blo 2281435 2283307 := bstep (se 1 (by rfl) ⟨1712480, by rfl⟩ : syracuseStep 2283307 = 3424961) B3424961
theorem B4334725 : Blo 2281435 4334725 := bbase (se 4 (by rfl) ⟨406380, by rfl⟩ : syracuseStep 4334725 = 812761) (by norm_num)
theorem B5779633 : Blo 2281435 5779633 := bstep (se 2 (by rfl) ⟨2167362, by rfl⟩ : syracuseStep 5779633 = 4334725) B4334725
theorem B7706177 : Blo 2281435 7706177 := bstep (se 2 (by rfl) ⟨2889816, by rfl⟩ : syracuseStep 7706177 = 5779633) B5779633
theorem B5137451 : Blo 2281435 5137451 := bstep (se 1 (by rfl) ⟨3853088, by rfl⟩ : syracuseStep 5137451 = 7706177) B7706177
theorem B3424967 : Blo 2281435 3424967 := bstep (se 1 (by rfl) ⟨2568725, by rfl⟩ : syracuseStep 3424967 = 5137451) B5137451
theorem B2283311 : Blo 2281435 2283311 := bstep (se 1 (by rfl) ⟨1712483, by rfl⟩ : syracuseStep 2283311 = 3424967) B3424967
theorem B3424973 : Blo 2281435 3424973 := bbase (se 3 (by rfl) ⟨642182, by rfl⟩ : syracuseStep 3424973 = 1284365) (by norm_num)
theorem B2283315 : Blo 2281435 2283315 := bstep (se 1 (by rfl) ⟨1712486, by rfl⟩ : syracuseStep 2283315 = 3424973) B3424973
theorem B5137469 : Blo 2281435 5137469 := bbase (se 3 (by rfl) ⟨963275, by rfl⟩ : syracuseStep 5137469 = 1926551) (by norm_num)
theorem B3424979 : Blo 2281435 3424979 := bstep (se 1 (by rfl) ⟨2568734, by rfl⟩ : syracuseStep 3424979 = 5137469) B5137469
theorem B2283319 : Blo 2281435 2283319 := bstep (se 1 (by rfl) ⟨1712489, by rfl⟩ : syracuseStep 2283319 = 3424979) B3424979
theorem B3853109 : Blo 2281435 3853109 := bbase (se 5 (by rfl) ⟨180614, by rfl⟩ : syracuseStep 3853109 = 361229) (by norm_num)
theorem B2568739 : Blo 2281435 2568739 := bstep (se 1 (by rfl) ⟨1926554, by rfl⟩ : syracuseStep 2568739 = 3853109) B3853109
theorem B3424985 : Blo 2281435 3424985 := bstep (se 2 (by rfl) ⟨1284369, by rfl⟩ : syracuseStep 3424985 = 2568739) B2568739
theorem B2283323 : Blo 2281435 2283323 := bstep (se 1 (by rfl) ⟨1712492, by rfl⟩ : syracuseStep 2283323 = 3424985) B3424985
theorem B6502133 : Blo 2281435 6502133 := bbase (se 5 (by rfl) ⟨304787, by rfl⟩ : syracuseStep 6502133 = 609575) (by norm_num)
theorem B17339021 : Blo 2281435 17339021 := bstep (se 3 (by rfl) ⟨3251066, by rfl⟩ : syracuseStep 17339021 = 6502133) B6502133
theorem B11559347 : Blo 2281435 11559347 := bstep (se 1 (by rfl) ⟨8669510, by rfl⟩ : syracuseStep 11559347 = 17339021) B17339021
theorem B7706231 : Blo 2281435 7706231 := bstep (se 1 (by rfl) ⟨5779673, by rfl⟩ : syracuseStep 7706231 = 11559347) B11559347
theorem B5137487 : Blo 2281435 5137487 := bstep (se 1 (by rfl) ⟨3853115, by rfl⟩ : syracuseStep 5137487 = 7706231) B7706231
theorem B3424991 : Blo 2281435 3424991 := bstep (se 1 (by rfl) ⟨2568743, by rfl⟩ : syracuseStep 3424991 = 5137487) B5137487
theorem B2283327 : Blo 2281435 2283327 := bstep (se 1 (by rfl) ⟨1712495, by rfl⟩ : syracuseStep 2283327 = 3424991) B3424991
theorem B3424997 : Blo 2281435 3424997 := bbase (se 4 (by rfl) ⟨321093, by rfl⟩ : syracuseStep 3424997 = 642187) (by norm_num)
theorem B2283331 : Blo 2281435 2283331 := bstep (se 1 (by rfl) ⟨1712498, by rfl⟩ : syracuseStep 2283331 = 3424997) B3424997
theorem B2438309 : Blo 2281435 2438309 := bbase (se 4 (by rfl) ⟨228591, by rfl⟩ : syracuseStep 2438309 = 457183) (by norm_num)
theorem B6502157 : Blo 2281435 6502157 := bstep (se 3 (by rfl) ⟨1219154, by rfl⟩ : syracuseStep 6502157 = 2438309) B2438309
theorem B4334771 : Blo 2281435 4334771 := bstep (se 1 (by rfl) ⟨3251078, by rfl⟩ : syracuseStep 4334771 = 6502157) B6502157
theorem B2889847 : Blo 2281435 2889847 := bstep (se 1 (by rfl) ⟨2167385, by rfl⟩ : syracuseStep 2889847 = 4334771) B4334771
theorem B3853129 : Blo 2281435 3853129 := bstep (se 2 (by rfl) ⟨1444923, by rfl⟩ : syracuseStep 3853129 = 2889847) B2889847
theorem B5137505 : Blo 2281435 5137505 := bstep (se 2 (by rfl) ⟨1926564, by rfl⟩ : syracuseStep 5137505 = 3853129) B3853129
theorem B3425003 : Blo 2281435 3425003 := bstep (se 1 (by rfl) ⟨2568752, by rfl⟩ : syracuseStep 3425003 = 5137505) B5137505
theorem B2283335 : Blo 2281435 2283335 := bstep (se 1 (by rfl) ⟨1712501, by rfl⟩ : syracuseStep 2283335 = 3425003) B3425003
theorem B2568757 : Blo 2281435 2568757 := bbase (se 5 (by rfl) ⟨120410, by rfl⟩ : syracuseStep 2568757 = 240821) (by norm_num)
theorem B3425009 : Blo 2281435 3425009 := bstep (se 2 (by rfl) ⟨1284378, by rfl⟩ : syracuseStep 3425009 = 2568757) B2568757
theorem B2283339 : Blo 2281435 2283339 := bstep (se 1 (by rfl) ⟨1712504, by rfl⟩ : syracuseStep 2283339 = 3425009) B3425009
theorem B2889857 : Blo 2281435 2889857 := bbase (se 2 (by rfl) ⟨1083696, by rfl⟩ : syracuseStep 2889857 = 2167393) (by norm_num)
theorem B7706285 : Blo 2281435 7706285 := bstep (se 3 (by rfl) ⟨1444928, by rfl⟩ : syracuseStep 7706285 = 2889857) B2889857
theorem B5137523 : Blo 2281435 5137523 := bstep (se 1 (by rfl) ⟨3853142, by rfl⟩ : syracuseStep 5137523 = 7706285) B7706285
theorem B3425015 : Blo 2281435 3425015 := bstep (se 1 (by rfl) ⟨2568761, by rfl⟩ : syracuseStep 3425015 = 5137523) B5137523
theorem B2283343 : Blo 2281435 2283343 := bstep (se 1 (by rfl) ⟨1712507, by rfl⟩ : syracuseStep 2283343 = 3425015) B3425015
theorem B3425021 : Blo 2281435 3425021 := bbase (se 3 (by rfl) ⟨642191, by rfl⟩ : syracuseStep 3425021 = 1284383) (by norm_num)
theorem B2283347 : Blo 2281435 2283347 := bstep (se 1 (by rfl) ⟨1712510, by rfl⟩ : syracuseStep 2283347 = 3425021) B3425021
theorem B5137541 : Blo 2281435 5137541 := bbase (se 4 (by rfl) ⟨481644, by rfl⟩ : syracuseStep 5137541 = 963289) (by norm_num)
theorem B3425027 : Blo 2281435 3425027 := bstep (se 1 (by rfl) ⟨2568770, by rfl⟩ : syracuseStep 3425027 = 5137541) B5137541
theorem B2283351 : Blo 2281435 2283351 := bstep (se 1 (by rfl) ⟨1712513, by rfl⟩ : syracuseStep 2283351 = 3425027) B3425027
theorem B4876661 : Blo 2281435 4876661 := bbase (se 5 (by rfl) ⟨228593, by rfl⟩ : syracuseStep 4876661 = 457187) (by norm_num)
theorem B3251107 : Blo 2281435 3251107 := bstep (se 1 (by rfl) ⟨2438330, by rfl⟩ : syracuseStep 3251107 = 4876661) B4876661
theorem B4334809 : Blo 2281435 4334809 := bstep (se 2 (by rfl) ⟨1625553, by rfl⟩ : syracuseStep 4334809 = 3251107) B3251107
theorem B5779745 : Blo 2281435 5779745 := bstep (se 2 (by rfl) ⟨2167404, by rfl⟩ : syracuseStep 5779745 = 4334809) B4334809
theorem B3853163 : Blo 2281435 3853163 := bstep (se 1 (by rfl) ⟨2889872, by rfl⟩ : syracuseStep 3853163 = 5779745) B5779745
theorem B2568775 : Blo 2281435 2568775 := bstep (se 1 (by rfl) ⟨1926581, by rfl⟩ : syracuseStep 2568775 = 3853163) B3853163
theorem B3425033 : Blo 2281435 3425033 := bstep (se 2 (by rfl) ⟨1284387, by rfl⟩ : syracuseStep 3425033 = 2568775) B2568775
theorem B2283355 : Blo 2281435 2283355 := bstep (se 1 (by rfl) ⟨1712516, by rfl⟩ : syracuseStep 2283355 = 3425033) B3425033
theorem B11559509 : Blo 2281435 11559509 := bbase (se 8 (by rfl) ⟨67731, by rfl⟩ : syracuseStep 11559509 = 135463) (by norm_num)
theorem B7706339 : Blo 2281435 7706339 := bstep (se 1 (by rfl) ⟨5779754, by rfl⟩ : syracuseStep 7706339 = 11559509) B11559509
theorem B5137559 : Blo 2281435 5137559 := bstep (se 1 (by rfl) ⟨3853169, by rfl⟩ : syracuseStep 5137559 = 7706339) B7706339
theorem B3425039 : Blo 2281435 3425039 := bstep (se 1 (by rfl) ⟨2568779, by rfl⟩ : syracuseStep 3425039 = 5137559) B5137559
theorem B2283359 : Blo 2281435 2283359 := bstep (se 1 (by rfl) ⟨1712519, by rfl⟩ : syracuseStep 2283359 = 3425039) B3425039
theorem B3425045 : Blo 2281435 3425045 := bbase (se 6 (by rfl) ⟨80274, by rfl⟩ : syracuseStep 3425045 = 160549) (by norm_num)
theorem B2283363 : Blo 2281435 2283363 := bstep (se 1 (by rfl) ⟨1712522, by rfl⟩ : syracuseStep 2283363 = 3425045) B3425045
theorem B7918085 : Blo 2281435 7918085 := bbase (se 4 (by rfl) ⟨742320, by rfl⟩ : syracuseStep 7918085 = 1484641) (by norm_num)
theorem B21114893 : Blo 2281435 21114893 := bstep (se 3 (by rfl) ⟨3959042, by rfl⟩ : syracuseStep 21114893 = 7918085) B7918085
theorem B14076595 : Blo 2281435 14076595 := bstep (se 1 (by rfl) ⟨10557446, by rfl⟩ : syracuseStep 14076595 = 21114893) B21114893
theorem B18768793 : Blo 2281435 18768793 := bstep (se 2 (by rfl) ⟨7038297, by rfl⟩ : syracuseStep 18768793 = 14076595) B14076595
theorem B25025057 : Blo 2281435 25025057 := bstep (se 2 (by rfl) ⟨9384396, by rfl⟩ : syracuseStep 25025057 = 18768793) B18768793
theorem B16683371 : Blo 2281435 16683371 := bstep (se 1 (by rfl) ⟨12512528, by rfl⟩ : syracuseStep 16683371 = 25025057) B25025057
theorem B11122247 : Blo 2281435 11122247 := bstep (se 1 (by rfl) ⟨8341685, by rfl⟩ : syracuseStep 11122247 = 16683371) B16683371
theorem B7414831 : Blo 2281435 7414831 := bstep (se 1 (by rfl) ⟨5561123, by rfl⟩ : syracuseStep 7414831 = 11122247) B11122247
theorem B9886441 : Blo 2281435 9886441 := bstep (se 2 (by rfl) ⟨3707415, by rfl⟩ : syracuseStep 9886441 = 7414831) B7414831
theorem B13181921 : Blo 2281435 13181921 := bstep (se 2 (by rfl) ⟨4943220, by rfl⟩ : syracuseStep 13181921 = 9886441) B9886441
theorem B8787947 : Blo 2281435 8787947 := bstep (se 1 (by rfl) ⟨6590960, by rfl⟩ : syracuseStep 8787947 = 13181921) B13181921
theorem B23434525 : Blo 2281435 23434525 := bstep (se 3 (by rfl) ⟨4393973, by rfl⟩ : syracuseStep 23434525 = 8787947) B8787947
theorem B124984133 : Blo 2281435 124984133 := bstep (se 4 (by rfl) ⟨11717262, by rfl⟩ : syracuseStep 124984133 = 23434525) B23434525
theorem B83322755 : Blo 2281435 83322755 := bstep (se 1 (by rfl) ⟨62492066, by rfl⟩ : syracuseStep 83322755 = 124984133) B124984133
theorem B55548503 : Blo 2281435 55548503 := bstep (se 1 (by rfl) ⟨41661377, by rfl⟩ : syracuseStep 55548503 = 83322755) B83322755
theorem B37032335 : Blo 2281435 37032335 := bstep (se 1 (by rfl) ⟨27774251, by rfl⟩ : syracuseStep 37032335 = 55548503) B55548503
theorem B24688223 : Blo 2281435 24688223 := bstep (se 1 (by rfl) ⟨18516167, by rfl⟩ : syracuseStep 24688223 = 37032335) B37032335
theorem B16458815 : Blo 2281435 16458815 := bstep (se 1 (by rfl) ⟨12344111, by rfl⟩ : syracuseStep 16458815 = 24688223) B24688223
theorem B43890173 : Blo 2281435 43890173 := bstep (se 3 (by rfl) ⟨8229407, by rfl⟩ : syracuseStep 43890173 = 16458815) B16458815
theorem B29260115 : Blo 2281435 29260115 := bstep (se 1 (by rfl) ⟨21945086, by rfl⟩ : syracuseStep 29260115 = 43890173) B43890173
theorem B19506743 : Blo 2281435 19506743 := bstep (se 1 (by rfl) ⟨14630057, by rfl⟩ : syracuseStep 19506743 = 29260115) B29260115
theorem B13004495 : Blo 2281435 13004495 := bstep (se 1 (by rfl) ⟨9753371, by rfl⟩ : syracuseStep 13004495 = 19506743) B19506743
theorem B8669663 : Blo 2281435 8669663 := bstep (se 1 (by rfl) ⟨6502247, by rfl⟩ : syracuseStep 8669663 = 13004495) B13004495
theorem B5779775 : Blo 2281435 5779775 := bstep (se 1 (by rfl) ⟨4334831, by rfl⟩ : syracuseStep 5779775 = 8669663) B8669663
theorem B3853183 : Blo 2281435 3853183 := bstep (se 1 (by rfl) ⟨2889887, by rfl⟩ : syracuseStep 3853183 = 5779775) B5779775
theorem B5137577 : Blo 2281435 5137577 := bstep (se 2 (by rfl) ⟨1926591, by rfl⟩ : syracuseStep 5137577 = 3853183) B3853183
theorem B3425051 : Blo 2281435 3425051 := bstep (se 1 (by rfl) ⟨2568788, by rfl⟩ : syracuseStep 3425051 = 5137577) B5137577
theorem B2283367 : Blo 2281435 2283367 := bstep (se 1 (by rfl) ⟨1712525, by rfl⟩ : syracuseStep 2283367 = 3425051) B3425051
theorem B2568793 : Blo 2281435 2568793 := bbase (se 2 (by rfl) ⟨963297, by rfl⟩ : syracuseStep 2568793 = 1926595) (by norm_num)
theorem B3425057 : Blo 2281435 3425057 := bstep (se 2 (by rfl) ⟨1284396, by rfl⟩ : syracuseStep 3425057 = 2568793) B2568793
theorem B2283371 : Blo 2281435 2283371 := bstep (se 1 (by rfl) ⟨1712528, by rfl⟩ : syracuseStep 2283371 = 3425057) B3425057
theorem B5858653 : Blo 2281435 5858653 := bbase (se 3 (by rfl) ⟨1098497, by rfl⟩ : syracuseStep 5858653 = 2196995) (by norm_num)
theorem B7811537 : Blo 2281435 7811537 := bstep (se 2 (by rfl) ⟨2929326, by rfl⟩ : syracuseStep 7811537 = 5858653) B5858653
theorem B20830765 : Blo 2281435 20830765 := bstep (se 3 (by rfl) ⟨3905768, by rfl⟩ : syracuseStep 20830765 = 7811537) B7811537
theorem B27774353 : Blo 2281435 27774353 := bstep (se 2 (by rfl) ⟨10415382, by rfl⟩ : syracuseStep 27774353 = 20830765) B20830765
theorem B18516235 : Blo 2281435 18516235 := bstep (se 1 (by rfl) ⟨13887176, by rfl⟩ : syracuseStep 18516235 = 27774353) B27774353
theorem B24688313 : Blo 2281435 24688313 := bstep (se 2 (by rfl) ⟨9258117, by rfl⟩ : syracuseStep 24688313 = 18516235) B18516235
theorem B16458875 : Blo 2281435 16458875 := bstep (se 1 (by rfl) ⟨12344156, by rfl⟩ : syracuseStep 16458875 = 24688313) B24688313
theorem B10972583 : Blo 2281435 10972583 := bstep (se 1 (by rfl) ⟨8229437, by rfl⟩ : syracuseStep 10972583 = 16458875) B16458875
theorem B7315055 : Blo 2281435 7315055 := bstep (se 1 (by rfl) ⟨5486291, by rfl⟩ : syracuseStep 7315055 = 10972583) B10972583
theorem B4876703 : Blo 2281435 4876703 := bstep (se 1 (by rfl) ⟨3657527, by rfl⟩ : syracuseStep 4876703 = 7315055) B7315055
theorem B3251135 : Blo 2281435 3251135 := bstep (se 1 (by rfl) ⟨2438351, by rfl⟩ : syracuseStep 3251135 = 4876703) B4876703
theorem B8669693 : Blo 2281435 8669693 := bstep (se 3 (by rfl) ⟨1625567, by rfl⟩ : syracuseStep 8669693 = 3251135) B3251135
theorem B5779795 : Blo 2281435 5779795 := bstep (se 1 (by rfl) ⟨4334846, by rfl⟩ : syracuseStep 5779795 = 8669693) B8669693
theorem B7706393 : Blo 2281435 7706393 := bstep (se 2 (by rfl) ⟨2889897, by rfl⟩ : syracuseStep 7706393 = 5779795) B5779795
theorem B5137595 : Blo 2281435 5137595 := bstep (se 1 (by rfl) ⟨3853196, by rfl⟩ : syracuseStep 5137595 = 7706393) B7706393
theorem B3425063 : Blo 2281435 3425063 := bstep (se 1 (by rfl) ⟨2568797, by rfl⟩ : syracuseStep 3425063 = 5137595) B5137595
theorem B2283375 : Blo 2281435 2283375 := bstep (se 1 (by rfl) ⟨1712531, by rfl⟩ : syracuseStep 2283375 = 3425063) B3425063
theorem B3425069 : Blo 2281435 3425069 := bbase (se 3 (by rfl) ⟨642200, by rfl⟩ : syracuseStep 3425069 = 1284401) (by norm_num)
theorem B2283379 : Blo 2281435 2283379 := bstep (se 1 (by rfl) ⟨1712534, by rfl⟩ : syracuseStep 2283379 = 3425069) B3425069
theorem B5137613 : Blo 2281435 5137613 := bbase (se 3 (by rfl) ⟨963302, by rfl⟩ : syracuseStep 5137613 = 1926605) (by norm_num)
theorem B3425075 : Blo 2281435 3425075 := bstep (se 1 (by rfl) ⟨2568806, by rfl⟩ : syracuseStep 3425075 = 5137613) B5137613
theorem B2283383 : Blo 2281435 2283383 := bstep (se 1 (by rfl) ⟨1712537, by rfl⟩ : syracuseStep 2283383 = 3425075) B3425075
theorem B2889913 : Blo 2281435 2889913 := bbase (se 2 (by rfl) ⟨1083717, by rfl⟩ : syracuseStep 2889913 = 2167435) (by norm_num)
theorem B3853217 : Blo 2281435 3853217 := bstep (se 2 (by rfl) ⟨1444956, by rfl⟩ : syracuseStep 3853217 = 2889913) B2889913
theorem B2568811 : Blo 2281435 2568811 := bstep (se 1 (by rfl) ⟨1926608, by rfl⟩ : syracuseStep 2568811 = 3853217) B3853217
theorem B3425081 : Blo 2281435 3425081 := bstep (se 2 (by rfl) ⟨1284405, by rfl⟩ : syracuseStep 3425081 = 2568811) B2568811
theorem B2283387 : Blo 2281435 2283387 := bstep (se 1 (by rfl) ⟨1712540, by rfl⟩ : syracuseStep 2283387 = 3425081) B3425081
theorem B6943637 : Blo 2281435 6943637 := bbase (se 6 (by rfl) ⟨162741, by rfl⟩ : syracuseStep 6943637 = 325483) (by norm_num)
theorem B4629091 : Blo 2281435 4629091 := bstep (se 1 (by rfl) ⟨3471818, by rfl⟩ : syracuseStep 4629091 = 6943637) B6943637
theorem B6172121 : Blo 2281435 6172121 := bstep (se 2 (by rfl) ⟨2314545, by rfl⟩ : syracuseStep 6172121 = 4629091) B4629091
theorem B4114747 : Blo 2281435 4114747 := bstep (se 1 (by rfl) ⟨3086060, by rfl⟩ : syracuseStep 4114747 = 6172121) B6172121
theorem B5486329 : Blo 2281435 5486329 := bstep (se 2 (by rfl) ⟨2057373, by rfl⟩ : syracuseStep 5486329 = 4114747) B4114747
theorem B7315105 : Blo 2281435 7315105 := bstep (se 2 (by rfl) ⟨2743164, by rfl⟩ : syracuseStep 7315105 = 5486329) B5486329
theorem B9753473 : Blo 2281435 9753473 := bstep (se 2 (by rfl) ⟨3657552, by rfl⟩ : syracuseStep 9753473 = 7315105) B7315105
theorem B26009261 : Blo 2281435 26009261 := bstep (se 3 (by rfl) ⟨4876736, by rfl⟩ : syracuseStep 26009261 = 9753473) B9753473
theorem B17339507 : Blo 2281435 17339507 := bstep (se 1 (by rfl) ⟨13004630, by rfl⟩ : syracuseStep 17339507 = 26009261) B26009261
theorem B11559671 : Blo 2281435 11559671 := bstep (se 1 (by rfl) ⟨8669753, by rfl⟩ : syracuseStep 11559671 = 17339507) B17339507
theorem B7706447 : Blo 2281435 7706447 := bstep (se 1 (by rfl) ⟨5779835, by rfl⟩ : syracuseStep 7706447 = 11559671) B11559671
theorem B5137631 : Blo 2281435 5137631 := bstep (se 1 (by rfl) ⟨3853223, by rfl⟩ : syracuseStep 5137631 = 7706447) B7706447
theorem B3425087 : Blo 2281435 3425087 := bstep (se 1 (by rfl) ⟨2568815, by rfl⟩ : syracuseStep 3425087 = 5137631) B5137631
theorem B2283391 : Blo 2281435 2283391 := bstep (se 1 (by rfl) ⟨1712543, by rfl⟩ : syracuseStep 2283391 = 3425087) B3425087
theorem B3425093 : Blo 2281435 3425093 := bbase (se 4 (by rfl) ⟨321102, by rfl⟩ : syracuseStep 3425093 = 642205) (by norm_num)
theorem B2283395 : Blo 2281435 2283395 := bstep (se 1 (by rfl) ⟨1712546, by rfl⟩ : syracuseStep 2283395 = 3425093) B3425093
theorem B3853237 : Blo 2281435 3853237 := bbase (se 5 (by rfl) ⟨180620, by rfl⟩ : syracuseStep 3853237 = 361241) (by norm_num)
theorem B5137649 : Blo 2281435 5137649 := bstep (se 2 (by rfl) ⟨1926618, by rfl⟩ : syracuseStep 5137649 = 3853237) B3853237
theorem B3425099 : Blo 2281435 3425099 := bstep (se 1 (by rfl) ⟨2568824, by rfl⟩ : syracuseStep 3425099 = 5137649) B5137649
theorem B2283399 : Blo 2281435 2283399 := bstep (se 1 (by rfl) ⟨1712549, by rfl⟩ : syracuseStep 2283399 = 3425099) B3425099
theorem B2568829 : Blo 2281435 2568829 := bbase (se 3 (by rfl) ⟨481655, by rfl⟩ : syracuseStep 2568829 = 963311) (by norm_num)
theorem B3425105 : Blo 2281435 3425105 := bstep (se 2 (by rfl) ⟨1284414, by rfl⟩ : syracuseStep 3425105 = 2568829) B2568829
theorem B2283403 : Blo 2281435 2283403 := bstep (se 1 (by rfl) ⟨1712552, by rfl⟩ : syracuseStep 2283403 = 3425105) B3425105
theorem B7706501 : Blo 2281435 7706501 := bbase (se 4 (by rfl) ⟨722484, by rfl⟩ : syracuseStep 7706501 = 1444969) (by norm_num)
theorem B5137667 : Blo 2281435 5137667 := bstep (se 1 (by rfl) ⟨3853250, by rfl⟩ : syracuseStep 5137667 = 7706501) B7706501
theorem B3425111 : Blo 2281435 3425111 := bstep (se 1 (by rfl) ⟨2568833, by rfl⟩ : syracuseStep 3425111 = 5137667) B5137667
theorem B2283407 : Blo 2281435 2283407 := bstep (se 1 (by rfl) ⟨1712555, by rfl⟩ : syracuseStep 2283407 = 3425111) B3425111
theorem B3425117 : Blo 2281435 3425117 := bbase (se 3 (by rfl) ⟨642209, by rfl⟩ : syracuseStep 3425117 = 1284419) (by norm_num)
theorem B2283411 : Blo 2281435 2283411 := bstep (se 1 (by rfl) ⟨1712558, by rfl⟩ : syracuseStep 2283411 = 3425117) B3425117
theorem B5137685 : Blo 2281435 5137685 := bbase (se 6 (by rfl) ⟨120414, by rfl⟩ : syracuseStep 5137685 = 240829) (by norm_num)
theorem B3425123 : Blo 2281435 3425123 := bstep (se 1 (by rfl) ⟨2568842, by rfl⟩ : syracuseStep 3425123 = 5137685) B5137685
theorem B2283415 : Blo 2281435 2283415 := bstep (se 1 (by rfl) ⟨1712561, by rfl⟩ : syracuseStep 2283415 = 3425123) B3425123
theorem B8669861 : Blo 2281435 8669861 := bbase (se 4 (by rfl) ⟨812799, by rfl⟩ : syracuseStep 8669861 = 1625599) (by norm_num)
theorem B5779907 : Blo 2281435 5779907 := bstep (se 1 (by rfl) ⟨4334930, by rfl⟩ : syracuseStep 5779907 = 8669861) B8669861
theorem B3853271 : Blo 2281435 3853271 := bstep (se 1 (by rfl) ⟨2889953, by rfl⟩ : syracuseStep 3853271 = 5779907) B5779907
theorem B2568847 : Blo 2281435 2568847 := bstep (se 1 (by rfl) ⟨1926635, by rfl⟩ : syracuseStep 2568847 = 3853271) B3853271
theorem B3425129 : Blo 2281435 3425129 := bstep (se 2 (by rfl) ⟨1284423, by rfl⟩ : syracuseStep 3425129 = 2568847) B2568847
theorem B2283419 : Blo 2281435 2283419 := bstep (se 1 (by rfl) ⟨1712564, by rfl⟩ : syracuseStep 2283419 = 3425129) B3425129
theorem B4876805 : Blo 2281435 4876805 := bbase (se 4 (by rfl) ⟨457200, by rfl⟩ : syracuseStep 4876805 = 914401) (by norm_num)
theorem B13004813 : Blo 2281435 13004813 := bstep (se 3 (by rfl) ⟨2438402, by rfl⟩ : syracuseStep 13004813 = 4876805) B4876805
theorem B8669875 : Blo 2281435 8669875 := bstep (se 1 (by rfl) ⟨6502406, by rfl⟩ : syracuseStep 8669875 = 13004813) B13004813
theorem B11559833 : Blo 2281435 11559833 := bstep (se 2 (by rfl) ⟨4334937, by rfl⟩ : syracuseStep 11559833 = 8669875) B8669875
theorem B7706555 : Blo 2281435 7706555 := bstep (se 1 (by rfl) ⟨5779916, by rfl⟩ : syracuseStep 7706555 = 11559833) B11559833
theorem B5137703 : Blo 2281435 5137703 := bstep (se 1 (by rfl) ⟨3853277, by rfl⟩ : syracuseStep 5137703 = 7706555) B7706555
theorem B3425135 : Blo 2281435 3425135 := bstep (se 1 (by rfl) ⟨2568851, by rfl⟩ : syracuseStep 3425135 = 5137703) B5137703
theorem B2283423 : Blo 2281435 2283423 := bstep (se 1 (by rfl) ⟨1712567, by rfl⟩ : syracuseStep 2283423 = 3425135) B3425135
theorem B3425141 : Blo 2281435 3425141 := bbase (se 5 (by rfl) ⟨160553, by rfl⟩ : syracuseStep 3425141 = 321107) (by norm_num)
theorem B2283427 : Blo 2281435 2283427 := bstep (se 1 (by rfl) ⟨1712570, by rfl⟩ : syracuseStep 2283427 = 3425141) B3425141
theorem B10972853 : Blo 2281435 10972853 := bbase (se 5 (by rfl) ⟨514352, by rfl⟩ : syracuseStep 10972853 = 1028705) (by norm_num)
theorem B7315235 : Blo 2281435 7315235 := bstep (se 1 (by rfl) ⟨5486426, by rfl⟩ : syracuseStep 7315235 = 10972853) B10972853
theorem B4876823 : Blo 2281435 4876823 := bstep (se 1 (by rfl) ⟨3657617, by rfl⟩ : syracuseStep 4876823 = 7315235) B7315235
theorem B3251215 : Blo 2281435 3251215 := bstep (se 1 (by rfl) ⟨2438411, by rfl⟩ : syracuseStep 3251215 = 4876823) B4876823
theorem B4334953 : Blo 2281435 4334953 := bstep (se 2 (by rfl) ⟨1625607, by rfl⟩ : syracuseStep 4334953 = 3251215) B3251215
theorem B5779937 : Blo 2281435 5779937 := bstep (se 2 (by rfl) ⟨2167476, by rfl⟩ : syracuseStep 5779937 = 4334953) B4334953
theorem B3853291 : Blo 2281435 3853291 := bstep (se 1 (by rfl) ⟨2889968, by rfl⟩ : syracuseStep 3853291 = 5779937) B5779937
theorem B5137721 : Blo 2281435 5137721 := bstep (se 2 (by rfl) ⟨1926645, by rfl⟩ : syracuseStep 5137721 = 3853291) B3853291
theorem B3425147 : Blo 2281435 3425147 := bstep (se 1 (by rfl) ⟨2568860, by rfl⟩ : syracuseStep 3425147 = 5137721) B5137721
theorem B2283431 : Blo 2281435 2283431 := bstep (se 1 (by rfl) ⟨1712573, by rfl⟩ : syracuseStep 2283431 = 3425147) B3425147
theorem B2568865 : Blo 2281435 2568865 := bbase (se 2 (by rfl) ⟨963324, by rfl⟩ : syracuseStep 2568865 = 1926649) (by norm_num)
theorem B3425153 : Blo 2281435 3425153 := bstep (se 2 (by rfl) ⟨1284432, by rfl⟩ : syracuseStep 3425153 = 2568865) B2568865
theorem B2283435 : Blo 2281435 2283435 := bstep (se 1 (by rfl) ⟨1712576, by rfl⟩ : syracuseStep 2283435 = 3425153) B3425153
theorem C0 (j : ℕ) (h1 : 570358 ≤ j) (h2 : j ≤ 570858) : Blo 2281435 (4 * j + 3) := by
  interval_cases j
  · exact B2281435
  · exact B2281439
  · exact B2281443
  · exact B2281447
  · exact B2281451
  · exact B2281455
  · exact B2281459
  · exact B2281463
  · exact B2281467
  · exact B2281471
  · exact B2281475
  · exact B2281479
  · exact B2281483
  · exact B2281487
  · exact B2281491
  · exact B2281495
  · exact B2281499
  · exact B2281503
  · exact B2281507
  · exact B2281511
  · exact B2281515
  · exact B2281519
  · exact B2281523
  · exact B2281527
  · exact B2281531
  · exact B2281535
  · exact B2281539
  · exact B2281543
  · exact B2281547
  · exact B2281551
  · exact B2281555
  · exact B2281559
  · exact B2281563
  · exact B2281567
  · exact B2281571
  · exact B2281575
  · exact B2281579
  · exact B2281583
  · exact B2281587
  · exact B2281591
  · exact B2281595
  · exact B2281599
  · exact B2281603
  · exact B2281607
  · exact B2281611
  · exact B2281615
  · exact B2281619
  · exact B2281623
  · exact B2281627
  · exact B2281631
  · exact B2281635
  · exact B2281639
  · exact B2281643
  · exact B2281647
  · exact B2281651
  · exact B2281655
  · exact B2281659
  · exact B2281663
  · exact B2281667
  · exact B2281671
  · exact B2281675
  · exact B2281679
  · exact B2281683
  · exact B2281687
  · exact B2281691
  · exact B2281695
  · exact B2281699
  · exact B2281703
  · exact B2281707
  · exact B2281711
  · exact B2281715
  · exact B2281719
  · exact B2281723
  · exact B2281727
  · exact B2281731
  · exact B2281735
  · exact B2281739
  · exact B2281743
  · exact B2281747
  · exact B2281751
  · exact B2281755
  · exact B2281759
  · exact B2281763
  · exact B2281767
  · exact B2281771
  · exact B2281775
  · exact B2281779
  · exact B2281783
  · exact B2281787
  · exact B2281791
  · exact B2281795
  · exact B2281799
  · exact B2281803
  · exact B2281807
  · exact B2281811
  · exact B2281815
  · exact B2281819
  · exact B2281823
  · exact B2281827
  · exact B2281831
  · exact B2281835
  · exact B2281839
  · exact B2281843
  · exact B2281847
  · exact B2281851
  · exact B2281855
  · exact B2281859
  · exact B2281863
  · exact B2281867
  · exact B2281871
  · exact B2281875
  · exact B2281879
  · exact B2281883
  · exact B2281887
  · exact B2281891
  · exact B2281895
  · exact B2281899
  · exact B2281903
  · exact B2281907
  · exact B2281911
  · exact B2281915
  · exact B2281919
  · exact B2281923
  · exact B2281927
  · exact B2281931
  · exact B2281935
  · exact B2281939
  · exact B2281943
  · exact B2281947
  · exact B2281951
  · exact B2281955
  · exact B2281959
  · exact B2281963
  · exact B2281967
  · exact B2281971
  · exact B2281975
  · exact B2281979
  · exact B2281983
  · exact B2281987
  · exact B2281991
  · exact B2281995
  · exact B2281999
  · exact B2282003
  · exact B2282007
  · exact B2282011
  · exact B2282015
  · exact B2282019
  · exact B2282023
  · exact B2282027
  · exact B2282031
  · exact B2282035
  · exact B2282039
  · exact B2282043
  · exact B2282047
  · exact B2282051
  · exact B2282055
  · exact B2282059
  · exact B2282063
  · exact B2282067
  · exact B2282071
  · exact B2282075
  · exact B2282079
  · exact B2282083
  · exact B2282087
  · exact B2282091
  · exact B2282095
  · exact B2282099
  · exact B2282103
  · exact B2282107
  · exact B2282111
  · exact B2282115
  · exact B2282119
  · exact B2282123
  · exact B2282127
  · exact B2282131
  · exact B2282135
  · exact B2282139
  · exact B2282143
  · exact B2282147
  · exact B2282151
  · exact B2282155
  · exact B2282159
  · exact B2282163
  · exact B2282167
  · exact B2282171
  · exact B2282175
  · exact B2282179
  · exact B2282183
  · exact B2282187
  · exact B2282191
  · exact B2282195
  · exact B2282199
  · exact B2282203
  · exact B2282207
  · exact B2282211
  · exact B2282215
  · exact B2282219
  · exact B2282223
  · exact B2282227
  · exact B2282231
  · exact B2282235
  · exact B2282239
  · exact B2282243
  · exact B2282247
  · exact B2282251
  · exact B2282255
  · exact B2282259
  · exact B2282263
  · exact B2282267
  · exact B2282271
  · exact B2282275
  · exact B2282279
  · exact B2282283
  · exact B2282287
  · exact B2282291
  · exact B2282295
  · exact B2282299
  · exact B2282303
  · exact B2282307
  · exact B2282311
  · exact B2282315
  · exact B2282319
  · exact B2282323
  · exact B2282327
  · exact B2282331
  · exact B2282335
  · exact B2282339
  · exact B2282343
  · exact B2282347
  · exact B2282351
  · exact B2282355
  · exact B2282359
  · exact B2282363
  · exact B2282367
  · exact B2282371
  · exact B2282375
  · exact B2282379
  · exact B2282383
  · exact B2282387
  · exact B2282391
  · exact B2282395
  · exact B2282399
  · exact B2282403
  · exact B2282407
  · exact B2282411
  · exact B2282415
  · exact B2282419
  · exact B2282423
  · exact B2282427
  · exact B2282431
  · exact B2282435
  · exact B2282439
  · exact B2282443
  · exact B2282447
  · exact B2282451
  · exact B2282455
  · exact B2282459
  · exact B2282463
  · exact B2282467
  · exact B2282471
  · exact B2282475
  · exact B2282479
  · exact B2282483
  · exact B2282487
  · exact B2282491
  · exact B2282495
  · exact B2282499
  · exact B2282503
  · exact B2282507
  · exact B2282511
  · exact B2282515
  · exact B2282519
  · exact B2282523
  · exact B2282527
  · exact B2282531
  · exact B2282535
  · exact B2282539
  · exact B2282543
  · exact B2282547
  · exact B2282551
  · exact B2282555
  · exact B2282559
  · exact B2282563
  · exact B2282567
  · exact B2282571
  · exact B2282575
  · exact B2282579
  · exact B2282583
  · exact B2282587
  · exact B2282591
  · exact B2282595
  · exact B2282599
  · exact B2282603
  · exact B2282607
  · exact B2282611
  · exact B2282615
  · exact B2282619
  · exact B2282623
  · exact B2282627
  · exact B2282631
  · exact B2282635
  · exact B2282639
  · exact B2282643
  · exact B2282647
  · exact B2282651
  · exact B2282655
  · exact B2282659
  · exact B2282663
  · exact B2282667
  · exact B2282671
  · exact B2282675
  · exact B2282679
  · exact B2282683
  · exact B2282687
  · exact B2282691
  · exact B2282695
  · exact B2282699
  · exact B2282703
  · exact B2282707
  · exact B2282711
  · exact B2282715
  · exact B2282719
  · exact B2282723
  · exact B2282727
  · exact B2282731
  · exact B2282735
  · exact B2282739
  · exact B2282743
  · exact B2282747
  · exact B2282751
  · exact B2282755
  · exact B2282759
  · exact B2282763
  · exact B2282767
  · exact B2282771
  · exact B2282775
  · exact B2282779
  · exact B2282783
  · exact B2282787
  · exact B2282791
  · exact B2282795
  · exact B2282799
  · exact B2282803
  · exact B2282807
  · exact B2282811
  · exact B2282815
  · exact B2282819
  · exact B2282823
  · exact B2282827
  · exact B2282831
  · exact B2282835
  · exact B2282839
  · exact B2282843
  · exact B2282847
  · exact B2282851
  · exact B2282855
  · exact B2282859
  · exact B2282863
  · exact B2282867
  · exact B2282871
  · exact B2282875
  · exact B2282879
  · exact B2282883
  · exact B2282887
  · exact B2282891
  · exact B2282895
  · exact B2282899
  · exact B2282903
  · exact B2282907
  · exact B2282911
  · exact B2282915
  · exact B2282919
  · exact B2282923
  · exact B2282927
  · exact B2282931
  · exact B2282935
  · exact B2282939
  · exact B2282943
  · exact B2282947
  · exact B2282951
  · exact B2282955
  · exact B2282959
  · exact B2282963
  · exact B2282967
  · exact B2282971
  · exact B2282975
  · exact B2282979
  · exact B2282983
  · exact B2282987
  · exact B2282991
  · exact B2282995
  · exact B2282999
  · exact B2283003
  · exact B2283007
  · exact B2283011
  · exact B2283015
  · exact B2283019
  · exact B2283023
  · exact B2283027
  · exact B2283031
  · exact B2283035
  · exact B2283039
  · exact B2283043
  · exact B2283047
  · exact B2283051
  · exact B2283055
  · exact B2283059
  · exact B2283063
  · exact B2283067
  · exact B2283071
  · exact B2283075
  · exact B2283079
  · exact B2283083
  · exact B2283087
  · exact B2283091
  · exact B2283095
  · exact B2283099
  · exact B2283103
  · exact B2283107
  · exact B2283111
  · exact B2283115
  · exact B2283119
  · exact B2283123
  · exact B2283127
  · exact B2283131
  · exact B2283135
  · exact B2283139
  · exact B2283143
  · exact B2283147
  · exact B2283151
  · exact B2283155
  · exact B2283159
  · exact B2283163
  · exact B2283167
  · exact B2283171
  · exact B2283175
  · exact B2283179
  · exact B2283183
  · exact B2283187
  · exact B2283191
  · exact B2283195
  · exact B2283199
  · exact B2283203
  · exact B2283207
  · exact B2283211
  · exact B2283215
  · exact B2283219
  · exact B2283223
  · exact B2283227
  · exact B2283231
  · exact B2283235
  · exact B2283239
  · exact B2283243
  · exact B2283247
  · exact B2283251
  · exact B2283255
  · exact B2283259
  · exact B2283263
  · exact B2283267
  · exact B2283271
  · exact B2283275
  · exact B2283279
  · exact B2283283
  · exact B2283287
  · exact B2283291
  · exact B2283295
  · exact B2283299
  · exact B2283303
  · exact B2283307
  · exact B2283311
  · exact B2283315
  · exact B2283319
  · exact B2283323
  · exact B2283327
  · exact B2283331
  · exact B2283335
  · exact B2283339
  · exact B2283343
  · exact B2283347
  · exact B2283351
  · exact B2283355
  · exact B2283359
  · exact B2283363
  · exact B2283367
  · exact B2283371
  · exact B2283375
  · exact B2283379
  · exact B2283383
  · exact B2283387
  · exact B2283391
  · exact B2283395
  · exact B2283399
  · exact B2283403
  · exact B2283407
  · exact B2283411
  · exact B2283415
  · exact B2283419
  · exact B2283423
  · exact B2283427
  · exact B2283431
  · exact B2283435
theorem solution (m : ℕ) (hlo : 2281435 ≤ m) (hhi : m ≤ 2283435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 570358 ≤ j := by omega
    have hj2 : j ≤ 570858 := by omega
    have hb : Blo 2281435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
