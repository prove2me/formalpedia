-- Prove2me | solution 1 for syracuse_descends_range_2189435_2191435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:18:05.843482+00:00
-- url     : https://prove2.me/submissions/9f7e62ec-026f-4405-84c3-a5fde2cc2932

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

theorem B2771005 : Blo 2189435 2771005 := bbase (se 3 (by rfl) ⟨519563, by rfl⟩ : syracuseStep 2771005 = 1039127) (by norm_num)
theorem B3694673 : Blo 2189435 3694673 := bstep (se 2 (by rfl) ⟨1385502, by rfl⟩ : syracuseStep 3694673 = 2771005) B2771005
theorem B2463115 : Blo 2189435 2463115 := bstep (se 1 (by rfl) ⟨1847336, by rfl⟩ : syracuseStep 2463115 = 3694673) B3694673
theorem B3284153 : Blo 2189435 3284153 := bstep (se 2 (by rfl) ⟨1231557, by rfl⟩ : syracuseStep 3284153 = 2463115) B2463115
theorem B2189435 : Blo 2189435 2189435 := bstep (se 1 (by rfl) ⟨1642076, by rfl⟩ : syracuseStep 2189435 = 3284153) B3284153
theorem B10664725 : Blo 2189435 10664725 := bbase (se 6 (by rfl) ⟨249954, by rfl⟩ : syracuseStep 10664725 = 499909) (by norm_num)
theorem B14219633 : Blo 2189435 14219633 := bstep (se 2 (by rfl) ⟨5332362, by rfl⟩ : syracuseStep 14219633 = 10664725) B10664725
theorem B9479755 : Blo 2189435 9479755 := bstep (se 1 (by rfl) ⟨7109816, by rfl⟩ : syracuseStep 9479755 = 14219633) B14219633
theorem B12639673 : Blo 2189435 12639673 := bstep (se 2 (by rfl) ⟨4739877, by rfl⟩ : syracuseStep 12639673 = 9479755) B9479755
theorem B16852897 : Blo 2189435 16852897 := bstep (se 2 (by rfl) ⟨6319836, by rfl⟩ : syracuseStep 16852897 = 12639673) B12639673
theorem B22470529 : Blo 2189435 22470529 := bstep (se 2 (by rfl) ⟨8426448, by rfl⟩ : syracuseStep 22470529 = 16852897) B16852897
theorem B29960705 : Blo 2189435 29960705 := bstep (se 2 (by rfl) ⟨11235264, by rfl⟩ : syracuseStep 29960705 = 22470529) B22470529
theorem B19973803 : Blo 2189435 19973803 := bstep (se 1 (by rfl) ⟨14980352, by rfl⟩ : syracuseStep 19973803 = 29960705) B29960705
theorem B26631737 : Blo 2189435 26631737 := bstep (se 2 (by rfl) ⟨9986901, by rfl⟩ : syracuseStep 26631737 = 19973803) B19973803
theorem B17754491 : Blo 2189435 17754491 := bstep (se 1 (by rfl) ⟨13315868, by rfl⟩ : syracuseStep 17754491 = 26631737) B26631737
theorem B11836327 : Blo 2189435 11836327 := bstep (se 1 (by rfl) ⟨8877245, by rfl⟩ : syracuseStep 11836327 = 17754491) B17754491
theorem B15781769 : Blo 2189435 15781769 := bstep (se 2 (by rfl) ⟨5918163, by rfl⟩ : syracuseStep 15781769 = 11836327) B11836327
theorem B10521179 : Blo 2189435 10521179 := bstep (se 1 (by rfl) ⟨7890884, by rfl⟩ : syracuseStep 10521179 = 15781769) B15781769
theorem B7014119 : Blo 2189435 7014119 := bstep (se 1 (by rfl) ⟨5260589, by rfl⟩ : syracuseStep 7014119 = 10521179) B10521179
theorem B18704317 : Blo 2189435 18704317 := bstep (se 3 (by rfl) ⟨3507059, by rfl⟩ : syracuseStep 18704317 = 7014119) B7014119
theorem B24939089 : Blo 2189435 24939089 := bstep (se 2 (by rfl) ⟨9352158, by rfl⟩ : syracuseStep 24939089 = 18704317) B18704317
theorem B16626059 : Blo 2189435 16626059 := bstep (se 1 (by rfl) ⟨12469544, by rfl⟩ : syracuseStep 16626059 = 24939089) B24939089
theorem B11084039 : Blo 2189435 11084039 := bstep (se 1 (by rfl) ⟨8313029, by rfl⟩ : syracuseStep 11084039 = 16626059) B16626059
theorem B7389359 : Blo 2189435 7389359 := bstep (se 1 (by rfl) ⟨5542019, by rfl⟩ : syracuseStep 7389359 = 11084039) B11084039
theorem B4926239 : Blo 2189435 4926239 := bstep (se 1 (by rfl) ⟨3694679, by rfl⟩ : syracuseStep 4926239 = 7389359) B7389359
theorem B3284159 : Blo 2189435 3284159 := bstep (se 1 (by rfl) ⟨2463119, by rfl⟩ : syracuseStep 3284159 = 4926239) B4926239
theorem B2189439 : Blo 2189435 2189439 := bstep (se 1 (by rfl) ⟨1642079, by rfl⟩ : syracuseStep 2189439 = 3284159) B3284159
theorem B3284165 : Blo 2189435 3284165 := bbase (se 4 (by rfl) ⟨307890, by rfl⟩ : syracuseStep 3284165 = 615781) (by norm_num)
theorem B2189443 : Blo 2189435 2189443 := bstep (se 1 (by rfl) ⟨1642082, by rfl⟩ : syracuseStep 2189443 = 3284165) B3284165
theorem B3694693 : Blo 2189435 3694693 := bbase (se 4 (by rfl) ⟨346377, by rfl⟩ : syracuseStep 3694693 = 692755) (by norm_num)
theorem B4926257 : Blo 2189435 4926257 := bstep (se 2 (by rfl) ⟨1847346, by rfl⟩ : syracuseStep 4926257 = 3694693) B3694693
theorem B3284171 : Blo 2189435 3284171 := bstep (se 1 (by rfl) ⟨2463128, by rfl⟩ : syracuseStep 3284171 = 4926257) B4926257
theorem B2189447 : Blo 2189435 2189447 := bstep (se 1 (by rfl) ⟨1642085, by rfl⟩ : syracuseStep 2189447 = 3284171) B3284171
theorem B2463133 : Blo 2189435 2463133 := bbase (se 3 (by rfl) ⟨461837, by rfl⟩ : syracuseStep 2463133 = 923675) (by norm_num)
theorem B3284177 : Blo 2189435 3284177 := bstep (se 2 (by rfl) ⟨1231566, by rfl⟩ : syracuseStep 3284177 = 2463133) B2463133
theorem B2189451 : Blo 2189435 2189451 := bstep (se 1 (by rfl) ⟨1642088, by rfl⟩ : syracuseStep 2189451 = 3284177) B3284177
theorem B7389413 : Blo 2189435 7389413 := bbase (se 4 (by rfl) ⟨692757, by rfl⟩ : syracuseStep 7389413 = 1385515) (by norm_num)
theorem B4926275 : Blo 2189435 4926275 := bstep (se 1 (by rfl) ⟨3694706, by rfl⟩ : syracuseStep 4926275 = 7389413) B7389413
theorem B3284183 : Blo 2189435 3284183 := bstep (se 1 (by rfl) ⟨2463137, by rfl⟩ : syracuseStep 3284183 = 4926275) B4926275
theorem B2189455 : Blo 2189435 2189455 := bstep (se 1 (by rfl) ⟨1642091, by rfl⟩ : syracuseStep 2189455 = 3284183) B3284183
theorem B3284189 : Blo 2189435 3284189 := bbase (se 3 (by rfl) ⟨615785, by rfl⟩ : syracuseStep 3284189 = 1231571) (by norm_num)
theorem B2189459 : Blo 2189435 2189459 := bstep (se 1 (by rfl) ⟨1642094, by rfl⟩ : syracuseStep 2189459 = 3284189) B3284189
theorem B4926293 : Blo 2189435 4926293 := bbase (se 9 (by rfl) ⟨14432, by rfl⟩ : syracuseStep 4926293 = 28865) (by norm_num)
theorem B3284195 : Blo 2189435 3284195 := bstep (se 1 (by rfl) ⟨2463146, by rfl⟩ : syracuseStep 3284195 = 4926293) B4926293
theorem B2189463 : Blo 2189435 2189463 := bstep (se 1 (by rfl) ⟨1642097, by rfl⟩ : syracuseStep 2189463 = 3284195) B3284195
theorem B6234853 : Blo 2189435 6234853 := bbase (se 4 (by rfl) ⟨584517, by rfl⟩ : syracuseStep 6234853 = 1169035) (by norm_num)
theorem B8313137 : Blo 2189435 8313137 := bstep (se 2 (by rfl) ⟨3117426, by rfl⟩ : syracuseStep 8313137 = 6234853) B6234853
theorem B5542091 : Blo 2189435 5542091 := bstep (se 1 (by rfl) ⟨4156568, by rfl⟩ : syracuseStep 5542091 = 8313137) B8313137
theorem B3694727 : Blo 2189435 3694727 := bstep (se 1 (by rfl) ⟨2771045, by rfl⟩ : syracuseStep 3694727 = 5542091) B5542091
theorem B2463151 : Blo 2189435 2463151 := bstep (se 1 (by rfl) ⟨1847363, by rfl⟩ : syracuseStep 2463151 = 3694727) B3694727
theorem B3284201 : Blo 2189435 3284201 := bstep (se 2 (by rfl) ⟨1231575, by rfl⟩ : syracuseStep 3284201 = 2463151) B2463151
theorem B2189467 : Blo 2189435 2189467 := bstep (se 1 (by rfl) ⟨1642100, by rfl⟩ : syracuseStep 2189467 = 3284201) B3284201
theorem B26995477 : Blo 2189435 26995477 := bbase (se 6 (by rfl) ⟨632706, by rfl⟩ : syracuseStep 26995477 = 1265413) (by norm_num)
theorem B35993969 : Blo 2189435 35993969 := bstep (se 2 (by rfl) ⟨13497738, by rfl⟩ : syracuseStep 35993969 = 26995477) B26995477
theorem B23995979 : Blo 2189435 23995979 := bstep (se 1 (by rfl) ⟨17996984, by rfl⟩ : syracuseStep 23995979 = 35993969) B35993969
theorem B15997319 : Blo 2189435 15997319 := bstep (se 1 (by rfl) ⟨11997989, by rfl⟩ : syracuseStep 15997319 = 23995979) B23995979
theorem B10664879 : Blo 2189435 10664879 := bstep (se 1 (by rfl) ⟨7998659, by rfl⟩ : syracuseStep 10664879 = 15997319) B15997319
theorem B28439677 : Blo 2189435 28439677 := bstep (se 3 (by rfl) ⟨5332439, by rfl⟩ : syracuseStep 28439677 = 10664879) B10664879
theorem B151678277 : Blo 2189435 151678277 := bstep (se 4 (by rfl) ⟨14219838, by rfl⟩ : syracuseStep 151678277 = 28439677) B28439677
theorem B101118851 : Blo 2189435 101118851 := bstep (se 1 (by rfl) ⟨75839138, by rfl⟩ : syracuseStep 101118851 = 151678277) B151678277
theorem B67412567 : Blo 2189435 67412567 := bstep (se 1 (by rfl) ⟨50559425, by rfl⟩ : syracuseStep 67412567 = 101118851) B101118851
theorem B44941711 : Blo 2189435 44941711 := bstep (se 1 (by rfl) ⟨33706283, by rfl⟩ : syracuseStep 44941711 = 67412567) B67412567
theorem B59922281 : Blo 2189435 59922281 := bstep (se 2 (by rfl) ⟨22470855, by rfl⟩ : syracuseStep 59922281 = 44941711) B44941711
theorem B39948187 : Blo 2189435 39948187 := bstep (se 1 (by rfl) ⟨29961140, by rfl⟩ : syracuseStep 39948187 = 59922281) B59922281
theorem B53264249 : Blo 2189435 53264249 := bstep (se 2 (by rfl) ⟨19974093, by rfl⟩ : syracuseStep 53264249 = 39948187) B39948187
theorem B35509499 : Blo 2189435 35509499 := bstep (se 1 (by rfl) ⟨26632124, by rfl⟩ : syracuseStep 35509499 = 53264249) B53264249
theorem B23672999 : Blo 2189435 23672999 := bstep (se 1 (by rfl) ⟨17754749, by rfl⟩ : syracuseStep 23672999 = 35509499) B35509499
theorem B63127997 : Blo 2189435 63127997 := bstep (se 3 (by rfl) ⟨11836499, by rfl⟩ : syracuseStep 63127997 = 23672999) B23672999
theorem B42085331 : Blo 2189435 42085331 := bstep (se 1 (by rfl) ⟨31563998, by rfl⟩ : syracuseStep 42085331 = 63127997) B63127997
theorem B28056887 : Blo 2189435 28056887 := bstep (se 1 (by rfl) ⟨21042665, by rfl⟩ : syracuseStep 28056887 = 42085331) B42085331
theorem B18704591 : Blo 2189435 18704591 := bstep (se 1 (by rfl) ⟨14028443, by rfl⟩ : syracuseStep 18704591 = 28056887) B28056887
theorem B12469727 : Blo 2189435 12469727 := bstep (se 1 (by rfl) ⟨9352295, by rfl⟩ : syracuseStep 12469727 = 18704591) B18704591
theorem B8313151 : Blo 2189435 8313151 := bstep (se 1 (by rfl) ⟨6234863, by rfl⟩ : syracuseStep 8313151 = 12469727) B12469727
theorem B11084201 : Blo 2189435 11084201 := bstep (se 2 (by rfl) ⟨4156575, by rfl⟩ : syracuseStep 11084201 = 8313151) B8313151
theorem B7389467 : Blo 2189435 7389467 := bstep (se 1 (by rfl) ⟨5542100, by rfl⟩ : syracuseStep 7389467 = 11084201) B11084201
theorem B4926311 : Blo 2189435 4926311 := bstep (se 1 (by rfl) ⟨3694733, by rfl⟩ : syracuseStep 4926311 = 7389467) B7389467
theorem B3284207 : Blo 2189435 3284207 := bstep (se 1 (by rfl) ⟨2463155, by rfl⟩ : syracuseStep 3284207 = 4926311) B4926311
theorem B2189471 : Blo 2189435 2189471 := bstep (se 1 (by rfl) ⟨1642103, by rfl⟩ : syracuseStep 2189471 = 3284207) B3284207
theorem B3284213 : Blo 2189435 3284213 := bbase (se 5 (by rfl) ⟨153947, by rfl⟩ : syracuseStep 3284213 = 307895) (by norm_num)
theorem B2189475 : Blo 2189435 2189475 := bstep (se 1 (by rfl) ⟨1642106, by rfl⟩ : syracuseStep 2189475 = 3284213) B3284213
theorem B3329029 : Blo 2189435 3329029 := bbase (se 4 (by rfl) ⟨312096, by rfl⟩ : syracuseStep 3329029 = 624193) (by norm_num)
theorem B4438705 : Blo 2189435 4438705 := bstep (se 2 (by rfl) ⟨1664514, by rfl⟩ : syracuseStep 4438705 = 3329029) B3329029
theorem B5918273 : Blo 2189435 5918273 := bstep (se 2 (by rfl) ⟨2219352, by rfl⟩ : syracuseStep 5918273 = 4438705) B4438705
theorem B3945515 : Blo 2189435 3945515 := bstep (se 1 (by rfl) ⟨2959136, by rfl⟩ : syracuseStep 3945515 = 5918273) B5918273
theorem B10521373 : Blo 2189435 10521373 := bstep (se 3 (by rfl) ⟨1972757, by rfl⟩ : syracuseStep 10521373 = 3945515) B3945515
theorem B14028497 : Blo 2189435 14028497 := bstep (se 2 (by rfl) ⟨5260686, by rfl⟩ : syracuseStep 14028497 = 10521373) B10521373
theorem B9352331 : Blo 2189435 9352331 := bstep (se 1 (by rfl) ⟨7014248, by rfl⟩ : syracuseStep 9352331 = 14028497) B14028497
theorem B6234887 : Blo 2189435 6234887 := bstep (se 1 (by rfl) ⟨4676165, by rfl⟩ : syracuseStep 6234887 = 9352331) B9352331
theorem B4156591 : Blo 2189435 4156591 := bstep (se 1 (by rfl) ⟨3117443, by rfl⟩ : syracuseStep 4156591 = 6234887) B6234887
theorem B5542121 : Blo 2189435 5542121 := bstep (se 2 (by rfl) ⟨2078295, by rfl⟩ : syracuseStep 5542121 = 4156591) B4156591
theorem B3694747 : Blo 2189435 3694747 := bstep (se 1 (by rfl) ⟨2771060, by rfl⟩ : syracuseStep 3694747 = 5542121) B5542121
theorem B4926329 : Blo 2189435 4926329 := bstep (se 2 (by rfl) ⟨1847373, by rfl⟩ : syracuseStep 4926329 = 3694747) B3694747
theorem B3284219 : Blo 2189435 3284219 := bstep (se 1 (by rfl) ⟨2463164, by rfl⟩ : syracuseStep 3284219 = 4926329) B4926329
theorem B2189479 : Blo 2189435 2189479 := bstep (se 1 (by rfl) ⟨1642109, by rfl⟩ : syracuseStep 2189479 = 3284219) B3284219
theorem B2463169 : Blo 2189435 2463169 := bbase (se 2 (by rfl) ⟨923688, by rfl⟩ : syracuseStep 2463169 = 1847377) (by norm_num)
theorem B3284225 : Blo 2189435 3284225 := bstep (se 2 (by rfl) ⟨1231584, by rfl⟩ : syracuseStep 3284225 = 2463169) B2463169
theorem B2189483 : Blo 2189435 2189483 := bstep (se 1 (by rfl) ⟨1642112, by rfl⟩ : syracuseStep 2189483 = 3284225) B3284225
theorem B5542141 : Blo 2189435 5542141 := bbase (se 3 (by rfl) ⟨1039151, by rfl⟩ : syracuseStep 5542141 = 2078303) (by norm_num)
theorem B7389521 : Blo 2189435 7389521 := bstep (se 2 (by rfl) ⟨2771070, by rfl⟩ : syracuseStep 7389521 = 5542141) B5542141
theorem B4926347 : Blo 2189435 4926347 := bstep (se 1 (by rfl) ⟨3694760, by rfl⟩ : syracuseStep 4926347 = 7389521) B7389521
theorem B3284231 : Blo 2189435 3284231 := bstep (se 1 (by rfl) ⟨2463173, by rfl⟩ : syracuseStep 3284231 = 4926347) B4926347
theorem B2189487 : Blo 2189435 2189487 := bstep (se 1 (by rfl) ⟨1642115, by rfl⟩ : syracuseStep 2189487 = 3284231) B3284231
theorem B3284237 : Blo 2189435 3284237 := bbase (se 3 (by rfl) ⟨615794, by rfl⟩ : syracuseStep 3284237 = 1231589) (by norm_num)
theorem B2189491 : Blo 2189435 2189491 := bstep (se 1 (by rfl) ⟨1642118, by rfl⟩ : syracuseStep 2189491 = 3284237) B3284237
theorem B4926365 : Blo 2189435 4926365 := bbase (se 3 (by rfl) ⟨923693, by rfl⟩ : syracuseStep 4926365 = 1847387) (by norm_num)
theorem B3284243 : Blo 2189435 3284243 := bstep (se 1 (by rfl) ⟨2463182, by rfl⟩ : syracuseStep 3284243 = 4926365) B4926365
theorem B2189495 : Blo 2189435 2189495 := bstep (se 1 (by rfl) ⟨1642121, by rfl⟩ : syracuseStep 2189495 = 3284243) B3284243
theorem B3694781 : Blo 2189435 3694781 := bbase (se 3 (by rfl) ⟨692771, by rfl⟩ : syracuseStep 3694781 = 1385543) (by norm_num)
theorem B2463187 : Blo 2189435 2463187 := bstep (se 1 (by rfl) ⟨1847390, by rfl⟩ : syracuseStep 2463187 = 3694781) B3694781
theorem B3284249 : Blo 2189435 3284249 := bstep (se 2 (by rfl) ⟨1231593, by rfl⟩ : syracuseStep 3284249 = 2463187) B2463187
theorem B2189499 : Blo 2189435 2189499 := bstep (se 1 (by rfl) ⟨1642124, by rfl⟩ : syracuseStep 2189499 = 3284249) B3284249
theorem B12469909 : Blo 2189435 12469909 := bbase (se 6 (by rfl) ⟨292263, by rfl⟩ : syracuseStep 12469909 = 584527) (by norm_num)
theorem B16626545 : Blo 2189435 16626545 := bstep (se 2 (by rfl) ⟨6234954, by rfl⟩ : syracuseStep 16626545 = 12469909) B12469909
theorem B11084363 : Blo 2189435 11084363 := bstep (se 1 (by rfl) ⟨8313272, by rfl⟩ : syracuseStep 11084363 = 16626545) B16626545
theorem B7389575 : Blo 2189435 7389575 := bstep (se 1 (by rfl) ⟨5542181, by rfl⟩ : syracuseStep 7389575 = 11084363) B11084363
theorem B4926383 : Blo 2189435 4926383 := bstep (se 1 (by rfl) ⟨3694787, by rfl⟩ : syracuseStep 4926383 = 7389575) B7389575
theorem B3284255 : Blo 2189435 3284255 := bstep (se 1 (by rfl) ⟨2463191, by rfl⟩ : syracuseStep 3284255 = 4926383) B4926383
theorem B2189503 : Blo 2189435 2189503 := bstep (se 1 (by rfl) ⟨1642127, by rfl⟩ : syracuseStep 2189503 = 3284255) B3284255
theorem B3284261 : Blo 2189435 3284261 := bbase (se 4 (by rfl) ⟨307899, by rfl⟩ : syracuseStep 3284261 = 615799) (by norm_num)
theorem B2189507 : Blo 2189435 2189507 := bstep (se 1 (by rfl) ⟨1642130, by rfl⟩ : syracuseStep 2189507 = 3284261) B3284261
theorem B2771101 : Blo 2189435 2771101 := bbase (se 3 (by rfl) ⟨519581, by rfl⟩ : syracuseStep 2771101 = 1039163) (by norm_num)
theorem B3694801 : Blo 2189435 3694801 := bstep (se 2 (by rfl) ⟨1385550, by rfl⟩ : syracuseStep 3694801 = 2771101) B2771101
theorem B4926401 : Blo 2189435 4926401 := bstep (se 2 (by rfl) ⟨1847400, by rfl⟩ : syracuseStep 4926401 = 3694801) B3694801
theorem B3284267 : Blo 2189435 3284267 := bstep (se 1 (by rfl) ⟨2463200, by rfl⟩ : syracuseStep 3284267 = 4926401) B4926401
theorem B2189511 : Blo 2189435 2189511 := bstep (se 1 (by rfl) ⟨1642133, by rfl⟩ : syracuseStep 2189511 = 3284267) B3284267
theorem B2463205 : Blo 2189435 2463205 := bbase (se 4 (by rfl) ⟨230925, by rfl⟩ : syracuseStep 2463205 = 461851) (by norm_num)
theorem B3284273 : Blo 2189435 3284273 := bstep (se 2 (by rfl) ⟨1231602, by rfl⟩ : syracuseStep 3284273 = 2463205) B2463205
theorem B2189515 : Blo 2189435 2189515 := bstep (se 1 (by rfl) ⟨1642136, by rfl⟩ : syracuseStep 2189515 = 3284273) B3284273
theorem B3796325 : Blo 2189435 3796325 := bbase (se 4 (by rfl) ⟨355905, by rfl⟩ : syracuseStep 3796325 = 711811) (by norm_num)
theorem B2530883 : Blo 2189435 2530883 := bstep (se 1 (by rfl) ⟨1898162, by rfl⟩ : syracuseStep 2530883 = 3796325) B3796325
theorem B6749021 : Blo 2189435 6749021 := bstep (se 3 (by rfl) ⟨1265441, by rfl⟩ : syracuseStep 6749021 = 2530883) B2530883
theorem B17997389 : Blo 2189435 17997389 := bstep (se 3 (by rfl) ⟨3374510, by rfl⟩ : syracuseStep 17997389 = 6749021) B6749021
theorem B11998259 : Blo 2189435 11998259 := bstep (se 1 (by rfl) ⟨8998694, by rfl⟩ : syracuseStep 11998259 = 17997389) B17997389
theorem B7998839 : Blo 2189435 7998839 := bstep (se 1 (by rfl) ⟨5999129, by rfl⟩ : syracuseStep 7998839 = 11998259) B11998259
theorem B5332559 : Blo 2189435 5332559 := bstep (se 1 (by rfl) ⟨3999419, by rfl⟩ : syracuseStep 5332559 = 7998839) B7998839
theorem B14220157 : Blo 2189435 14220157 := bstep (se 3 (by rfl) ⟨2666279, by rfl⟩ : syracuseStep 14220157 = 5332559) B5332559
theorem B18960209 : Blo 2189435 18960209 := bstep (se 2 (by rfl) ⟨7110078, by rfl⟩ : syracuseStep 18960209 = 14220157) B14220157
theorem B12640139 : Blo 2189435 12640139 := bstep (se 1 (by rfl) ⟨9480104, by rfl⟩ : syracuseStep 12640139 = 18960209) B18960209
theorem B8426759 : Blo 2189435 8426759 := bstep (se 1 (by rfl) ⟨6320069, by rfl⟩ : syracuseStep 8426759 = 12640139) B12640139
theorem B22471357 : Blo 2189435 22471357 := bstep (se 3 (by rfl) ⟨4213379, by rfl⟩ : syracuseStep 22471357 = 8426759) B8426759
theorem B29961809 : Blo 2189435 29961809 := bstep (se 2 (by rfl) ⟨11235678, by rfl⟩ : syracuseStep 29961809 = 22471357) B22471357
theorem B19974539 : Blo 2189435 19974539 := bstep (se 1 (by rfl) ⟨14980904, by rfl⟩ : syracuseStep 19974539 = 29961809) B29961809
theorem B13316359 : Blo 2189435 13316359 := bstep (se 1 (by rfl) ⟨9987269, by rfl⟩ : syracuseStep 13316359 = 19974539) B19974539
theorem B17755145 : Blo 2189435 17755145 := bstep (se 2 (by rfl) ⟨6658179, by rfl⟩ : syracuseStep 17755145 = 13316359) B13316359
theorem B11836763 : Blo 2189435 11836763 := bstep (se 1 (by rfl) ⟨8877572, by rfl⟩ : syracuseStep 11836763 = 17755145) B17755145
theorem B7891175 : Blo 2189435 7891175 := bstep (se 1 (by rfl) ⟨5918381, by rfl⟩ : syracuseStep 7891175 = 11836763) B11836763
theorem B5260783 : Blo 2189435 5260783 := bstep (se 1 (by rfl) ⟨3945587, by rfl⟩ : syracuseStep 5260783 = 7891175) B7891175
theorem B7014377 : Blo 2189435 7014377 := bstep (se 2 (by rfl) ⟨2630391, by rfl⟩ : syracuseStep 7014377 = 5260783) B5260783
theorem B4676251 : Blo 2189435 4676251 := bstep (se 1 (by rfl) ⟨3507188, by rfl⟩ : syracuseStep 4676251 = 7014377) B7014377
theorem B6235001 : Blo 2189435 6235001 := bstep (se 2 (by rfl) ⟨2338125, by rfl⟩ : syracuseStep 6235001 = 4676251) B4676251
theorem B4156667 : Blo 2189435 4156667 := bstep (se 1 (by rfl) ⟨3117500, by rfl⟩ : syracuseStep 4156667 = 6235001) B6235001
theorem B2771111 : Blo 2189435 2771111 := bstep (se 1 (by rfl) ⟨2078333, by rfl⟩ : syracuseStep 2771111 = 4156667) B4156667
theorem B7389629 : Blo 2189435 7389629 := bstep (se 3 (by rfl) ⟨1385555, by rfl⟩ : syracuseStep 7389629 = 2771111) B2771111
theorem B4926419 : Blo 2189435 4926419 := bstep (se 1 (by rfl) ⟨3694814, by rfl⟩ : syracuseStep 4926419 = 7389629) B7389629
theorem B3284279 : Blo 2189435 3284279 := bstep (se 1 (by rfl) ⟨2463209, by rfl⟩ : syracuseStep 3284279 = 4926419) B4926419
theorem B2189519 : Blo 2189435 2189519 := bstep (se 1 (by rfl) ⟨1642139, by rfl⟩ : syracuseStep 2189519 = 3284279) B3284279
theorem B3284285 : Blo 2189435 3284285 := bbase (se 3 (by rfl) ⟨615803, by rfl⟩ : syracuseStep 3284285 = 1231607) (by norm_num)
theorem B2189523 : Blo 2189435 2189523 := bstep (se 1 (by rfl) ⟨1642142, by rfl⟩ : syracuseStep 2189523 = 3284285) B3284285
theorem B4926437 : Blo 2189435 4926437 := bbase (se 4 (by rfl) ⟨461853, by rfl⟩ : syracuseStep 4926437 = 923707) (by norm_num)
theorem B3284291 : Blo 2189435 3284291 := bstep (se 1 (by rfl) ⟨2463218, by rfl⟩ : syracuseStep 3284291 = 4926437) B4926437
theorem B2189527 : Blo 2189435 2189527 := bstep (se 1 (by rfl) ⟨1642145, by rfl⟩ : syracuseStep 2189527 = 3284291) B3284291
theorem B5542253 : Blo 2189435 5542253 := bbase (se 3 (by rfl) ⟨1039172, by rfl⟩ : syracuseStep 5542253 = 2078345) (by norm_num)
theorem B3694835 : Blo 2189435 3694835 := bstep (se 1 (by rfl) ⟨2771126, by rfl⟩ : syracuseStep 3694835 = 5542253) B5542253
theorem B2463223 : Blo 2189435 2463223 := bstep (se 1 (by rfl) ⟨1847417, by rfl⟩ : syracuseStep 2463223 = 3694835) B3694835
theorem B3284297 : Blo 2189435 3284297 := bstep (se 2 (by rfl) ⟨1231611, by rfl⟩ : syracuseStep 3284297 = 2463223) B2463223
theorem B2189531 : Blo 2189435 2189531 := bstep (se 1 (by rfl) ⟨1642148, by rfl⟩ : syracuseStep 2189531 = 3284297) B3284297
theorem B4676285 : Blo 2189435 4676285 := bbase (se 3 (by rfl) ⟨876803, by rfl⟩ : syracuseStep 4676285 = 1753607) (by norm_num)
theorem B3117523 : Blo 2189435 3117523 := bstep (se 1 (by rfl) ⟨2338142, by rfl⟩ : syracuseStep 3117523 = 4676285) B4676285
theorem B4156697 : Blo 2189435 4156697 := bstep (se 2 (by rfl) ⟨1558761, by rfl⟩ : syracuseStep 4156697 = 3117523) B3117523
theorem B11084525 : Blo 2189435 11084525 := bstep (se 3 (by rfl) ⟨2078348, by rfl⟩ : syracuseStep 11084525 = 4156697) B4156697
theorem B7389683 : Blo 2189435 7389683 := bstep (se 1 (by rfl) ⟨5542262, by rfl⟩ : syracuseStep 7389683 = 11084525) B11084525
theorem B4926455 : Blo 2189435 4926455 := bstep (se 1 (by rfl) ⟨3694841, by rfl⟩ : syracuseStep 4926455 = 7389683) B7389683
theorem B3284303 : Blo 2189435 3284303 := bstep (se 1 (by rfl) ⟨2463227, by rfl⟩ : syracuseStep 3284303 = 4926455) B4926455
theorem B2189535 : Blo 2189435 2189535 := bstep (se 1 (by rfl) ⟨1642151, by rfl⟩ : syracuseStep 2189535 = 3284303) B3284303
theorem B3284309 : Blo 2189435 3284309 := bbase (se 11 (by rfl) ⟨2405, by rfl⟩ : syracuseStep 3284309 = 4811) (by norm_num)
theorem B2189539 : Blo 2189435 2189539 := bstep (se 1 (by rfl) ⟨1642154, by rfl⟩ : syracuseStep 2189539 = 3284309) B3284309
theorem B2666309 : Blo 2189435 2666309 := bbase (se 4 (by rfl) ⟨249966, by rfl⟩ : syracuseStep 2666309 = 499933) (by norm_num)
theorem B28440629 : Blo 2189435 28440629 := bstep (se 5 (by rfl) ⟨1333154, by rfl⟩ : syracuseStep 28440629 = 2666309) B2666309
theorem B18960419 : Blo 2189435 18960419 := bstep (se 1 (by rfl) ⟨14220314, by rfl⟩ : syracuseStep 18960419 = 28440629) B28440629
theorem B50561117 : Blo 2189435 50561117 := bstep (se 3 (by rfl) ⟨9480209, by rfl⟩ : syracuseStep 50561117 = 18960419) B18960419
theorem B33707411 : Blo 2189435 33707411 := bstep (se 1 (by rfl) ⟨25280558, by rfl⟩ : syracuseStep 33707411 = 50561117) B50561117
theorem B22471607 : Blo 2189435 22471607 := bstep (se 1 (by rfl) ⟨16853705, by rfl⟩ : syracuseStep 22471607 = 33707411) B33707411
theorem B14981071 : Blo 2189435 14981071 := bstep (se 1 (by rfl) ⟨11235803, by rfl⟩ : syracuseStep 14981071 = 22471607) B22471607
theorem B19974761 : Blo 2189435 19974761 := bstep (se 2 (by rfl) ⟨7490535, by rfl⟩ : syracuseStep 19974761 = 14981071) B14981071
theorem B13316507 : Blo 2189435 13316507 := bstep (se 1 (by rfl) ⟨9987380, by rfl⟩ : syracuseStep 13316507 = 19974761) B19974761
theorem B8877671 : Blo 2189435 8877671 := bstep (se 1 (by rfl) ⟨6658253, by rfl⟩ : syracuseStep 8877671 = 13316507) B13316507
theorem B5918447 : Blo 2189435 5918447 := bstep (se 1 (by rfl) ⟨4438835, by rfl⟩ : syracuseStep 5918447 = 8877671) B8877671
theorem B3945631 : Blo 2189435 3945631 := bstep (se 1 (by rfl) ⟨2959223, by rfl⟩ : syracuseStep 3945631 = 5918447) B5918447
theorem B5260841 : Blo 2189435 5260841 := bstep (se 2 (by rfl) ⟨1972815, by rfl⟩ : syracuseStep 5260841 = 3945631) B3945631
theorem B3507227 : Blo 2189435 3507227 := bstep (se 1 (by rfl) ⟨2630420, by rfl⟩ : syracuseStep 3507227 = 5260841) B5260841
theorem B2338151 : Blo 2189435 2338151 := bstep (se 1 (by rfl) ⟨1753613, by rfl⟩ : syracuseStep 2338151 = 3507227) B3507227
theorem B6235069 : Blo 2189435 6235069 := bstep (se 3 (by rfl) ⟨1169075, by rfl⟩ : syracuseStep 6235069 = 2338151) B2338151
theorem B8313425 : Blo 2189435 8313425 := bstep (se 2 (by rfl) ⟨3117534, by rfl⟩ : syracuseStep 8313425 = 6235069) B6235069
theorem B5542283 : Blo 2189435 5542283 := bstep (se 1 (by rfl) ⟨4156712, by rfl⟩ : syracuseStep 5542283 = 8313425) B8313425
theorem B3694855 : Blo 2189435 3694855 := bstep (se 1 (by rfl) ⟨2771141, by rfl⟩ : syracuseStep 3694855 = 5542283) B5542283
theorem B4926473 : Blo 2189435 4926473 := bstep (se 2 (by rfl) ⟨1847427, by rfl⟩ : syracuseStep 4926473 = 3694855) B3694855
theorem B3284315 : Blo 2189435 3284315 := bstep (se 1 (by rfl) ⟨2463236, by rfl⟩ : syracuseStep 3284315 = 4926473) B4926473
theorem B2189543 : Blo 2189435 2189543 := bstep (se 1 (by rfl) ⟨1642157, by rfl⟩ : syracuseStep 2189543 = 3284315) B3284315
theorem B2463241 : Blo 2189435 2463241 := bbase (se 2 (by rfl) ⟨923715, by rfl⟩ : syracuseStep 2463241 = 1847431) (by norm_num)
theorem B3284321 : Blo 2189435 3284321 := bstep (se 2 (by rfl) ⟨1231620, by rfl⟩ : syracuseStep 3284321 = 2463241) B2463241
theorem B2189547 : Blo 2189435 2189547 := bstep (se 1 (by rfl) ⟨1642160, by rfl⟩ : syracuseStep 2189547 = 3284321) B3284321
theorem B15392693 : Blo 2189435 15392693 := bbase (se 5 (by rfl) ⟨721532, by rfl⟩ : syracuseStep 15392693 = 1443065) (by norm_num)
theorem B41047181 : Blo 2189435 41047181 := bstep (se 3 (by rfl) ⟨7696346, by rfl⟩ : syracuseStep 41047181 = 15392693) B15392693
theorem B27364787 : Blo 2189435 27364787 := bstep (se 1 (by rfl) ⟨20523590, by rfl⟩ : syracuseStep 27364787 = 41047181) B41047181
theorem B18243191 : Blo 2189435 18243191 := bstep (se 1 (by rfl) ⟨13682393, by rfl⟩ : syracuseStep 18243191 = 27364787) B27364787
theorem B48648509 : Blo 2189435 48648509 := bstep (se 3 (by rfl) ⟨9121595, by rfl⟩ : syracuseStep 48648509 = 18243191) B18243191
theorem B32432339 : Blo 2189435 32432339 := bstep (se 1 (by rfl) ⟨24324254, by rfl⟩ : syracuseStep 32432339 = 48648509) B48648509
theorem B86486237 : Blo 2189435 86486237 := bstep (se 3 (by rfl) ⟨16216169, by rfl⟩ : syracuseStep 86486237 = 32432339) B32432339
theorem B57657491 : Blo 2189435 57657491 := bstep (se 1 (by rfl) ⟨43243118, by rfl⟩ : syracuseStep 57657491 = 86486237) B86486237
theorem B38438327 : Blo 2189435 38438327 := bstep (se 1 (by rfl) ⟨28828745, by rfl⟩ : syracuseStep 38438327 = 57657491) B57657491
theorem B102502205 : Blo 2189435 102502205 := bstep (se 3 (by rfl) ⟨19219163, by rfl⟩ : syracuseStep 102502205 = 38438327) B38438327
theorem B68334803 : Blo 2189435 68334803 := bstep (se 1 (by rfl) ⟨51251102, by rfl⟩ : syracuseStep 68334803 = 102502205) B102502205
theorem B45556535 : Blo 2189435 45556535 := bstep (se 1 (by rfl) ⟨34167401, by rfl⟩ : syracuseStep 45556535 = 68334803) B68334803
theorem B30371023 : Blo 2189435 30371023 := bstep (se 1 (by rfl) ⟨22778267, by rfl⟩ : syracuseStep 30371023 = 45556535) B45556535
theorem B40494697 : Blo 2189435 40494697 := bstep (se 2 (by rfl) ⟨15185511, by rfl⟩ : syracuseStep 40494697 = 30371023) B30371023
theorem B215971717 : Blo 2189435 215971717 := bstep (se 4 (by rfl) ⟨20247348, by rfl⟩ : syracuseStep 215971717 = 40494697) B40494697
theorem B287962289 : Blo 2189435 287962289 := bstep (se 2 (by rfl) ⟨107985858, by rfl⟩ : syracuseStep 287962289 = 215971717) B215971717
theorem B191974859 : Blo 2189435 191974859 := bstep (se 1 (by rfl) ⟨143981144, by rfl⟩ : syracuseStep 191974859 = 287962289) B287962289
theorem B127983239 : Blo 2189435 127983239 := bstep (se 1 (by rfl) ⟨95987429, by rfl⟩ : syracuseStep 127983239 = 191974859) B191974859
theorem B85322159 : Blo 2189435 85322159 := bstep (se 1 (by rfl) ⟨63991619, by rfl⟩ : syracuseStep 85322159 = 127983239) B127983239
theorem B56881439 : Blo 2189435 56881439 := bstep (se 1 (by rfl) ⟨42661079, by rfl⟩ : syracuseStep 56881439 = 85322159) B85322159
theorem B37920959 : Blo 2189435 37920959 := bstep (se 1 (by rfl) ⟨28440719, by rfl⟩ : syracuseStep 37920959 = 56881439) B56881439
theorem B25280639 : Blo 2189435 25280639 := bstep (se 1 (by rfl) ⟨18960479, by rfl⟩ : syracuseStep 25280639 = 37920959) B37920959
theorem B16853759 : Blo 2189435 16853759 := bstep (se 1 (by rfl) ⟨12640319, by rfl⟩ : syracuseStep 16853759 = 25280639) B25280639
theorem B11235839 : Blo 2189435 11235839 := bstep (se 1 (by rfl) ⟨8426879, by rfl⟩ : syracuseStep 11235839 = 16853759) B16853759
theorem B29962237 : Blo 2189435 29962237 := bstep (se 3 (by rfl) ⟨5617919, by rfl⟩ : syracuseStep 29962237 = 11235839) B11235839
theorem B39949649 : Blo 2189435 39949649 := bstep (se 2 (by rfl) ⟨14981118, by rfl⟩ : syracuseStep 39949649 = 29962237) B29962237
theorem B26633099 : Blo 2189435 26633099 := bstep (se 1 (by rfl) ⟨19974824, by rfl⟩ : syracuseStep 26633099 = 39949649) B39949649
theorem B17755399 : Blo 2189435 17755399 := bstep (se 1 (by rfl) ⟨13316549, by rfl⟩ : syracuseStep 17755399 = 26633099) B26633099
theorem B23673865 : Blo 2189435 23673865 := bstep (se 2 (by rfl) ⟨8877699, by rfl⟩ : syracuseStep 23673865 = 17755399) B17755399
theorem B31565153 : Blo 2189435 31565153 := bstep (se 2 (by rfl) ⟨11836932, by rfl⟩ : syracuseStep 31565153 = 23673865) B23673865
theorem B21043435 : Blo 2189435 21043435 := bstep (se 1 (by rfl) ⟨15782576, by rfl⟩ : syracuseStep 21043435 = 31565153) B31565153
theorem B28057913 : Blo 2189435 28057913 := bstep (se 2 (by rfl) ⟨10521717, by rfl⟩ : syracuseStep 28057913 = 21043435) B21043435
theorem B18705275 : Blo 2189435 18705275 := bstep (se 1 (by rfl) ⟨14028956, by rfl⟩ : syracuseStep 18705275 = 28057913) B28057913
theorem B12470183 : Blo 2189435 12470183 := bstep (se 1 (by rfl) ⟨9352637, by rfl⟩ : syracuseStep 12470183 = 18705275) B18705275
theorem B8313455 : Blo 2189435 8313455 := bstep (se 1 (by rfl) ⟨6235091, by rfl⟩ : syracuseStep 8313455 = 12470183) B12470183
theorem B5542303 : Blo 2189435 5542303 := bstep (se 1 (by rfl) ⟨4156727, by rfl⟩ : syracuseStep 5542303 = 8313455) B8313455
theorem B7389737 : Blo 2189435 7389737 := bstep (se 2 (by rfl) ⟨2771151, by rfl⟩ : syracuseStep 7389737 = 5542303) B5542303
theorem B4926491 : Blo 2189435 4926491 := bstep (se 1 (by rfl) ⟨3694868, by rfl⟩ : syracuseStep 4926491 = 7389737) B7389737
theorem B3284327 : Blo 2189435 3284327 := bstep (se 1 (by rfl) ⟨2463245, by rfl⟩ : syracuseStep 3284327 = 4926491) B4926491
theorem B2189551 : Blo 2189435 2189551 := bstep (se 1 (by rfl) ⟨1642163, by rfl⟩ : syracuseStep 2189551 = 3284327) B3284327
theorem B3284333 : Blo 2189435 3284333 := bbase (se 3 (by rfl) ⟨615812, by rfl⟩ : syracuseStep 3284333 = 1231625) (by norm_num)
theorem B2189555 : Blo 2189435 2189555 := bstep (se 1 (by rfl) ⟨1642166, by rfl⟩ : syracuseStep 2189555 = 3284333) B3284333
theorem B4926509 : Blo 2189435 4926509 := bbase (se 3 (by rfl) ⟨923720, by rfl⟩ : syracuseStep 4926509 = 1847441) (by norm_num)
theorem B3284339 : Blo 2189435 3284339 := bstep (se 1 (by rfl) ⟨2463254, by rfl⟩ : syracuseStep 3284339 = 4926509) B4926509
theorem B2189559 : Blo 2189435 2189559 := bstep (se 1 (by rfl) ⟨1642169, by rfl⟩ : syracuseStep 2189559 = 3284339) B3284339
theorem B5918501 : Blo 2189435 5918501 := bbase (se 4 (by rfl) ⟨554859, by rfl⟩ : syracuseStep 5918501 = 1109719) (by norm_num)
theorem B3945667 : Blo 2189435 3945667 := bstep (se 1 (by rfl) ⟨2959250, by rfl⟩ : syracuseStep 3945667 = 5918501) B5918501
theorem B5260889 : Blo 2189435 5260889 := bstep (se 2 (by rfl) ⟨1972833, by rfl⟩ : syracuseStep 5260889 = 3945667) B3945667
theorem B14029037 : Blo 2189435 14029037 := bstep (se 3 (by rfl) ⟨2630444, by rfl⟩ : syracuseStep 14029037 = 5260889) B5260889
theorem B9352691 : Blo 2189435 9352691 := bstep (se 1 (by rfl) ⟨7014518, by rfl⟩ : syracuseStep 9352691 = 14029037) B14029037
theorem B6235127 : Blo 2189435 6235127 := bstep (se 1 (by rfl) ⟨4676345, by rfl⟩ : syracuseStep 6235127 = 9352691) B9352691
theorem B4156751 : Blo 2189435 4156751 := bstep (se 1 (by rfl) ⟨3117563, by rfl⟩ : syracuseStep 4156751 = 6235127) B6235127
theorem B2771167 : Blo 2189435 2771167 := bstep (se 1 (by rfl) ⟨2078375, by rfl⟩ : syracuseStep 2771167 = 4156751) B4156751
theorem B3694889 : Blo 2189435 3694889 := bstep (se 2 (by rfl) ⟨1385583, by rfl⟩ : syracuseStep 3694889 = 2771167) B2771167
theorem B2463259 : Blo 2189435 2463259 := bstep (se 1 (by rfl) ⟨1847444, by rfl⟩ : syracuseStep 2463259 = 3694889) B3694889
theorem B3284345 : Blo 2189435 3284345 := bstep (se 2 (by rfl) ⟨1231629, by rfl⟩ : syracuseStep 3284345 = 2463259) B2463259
theorem B2189563 : Blo 2189435 2189563 := bstep (se 1 (by rfl) ⟨1642172, by rfl⟩ : syracuseStep 2189563 = 3284345) B3284345
theorem B6658325 : Blo 2189435 6658325 := bbase (se 6 (by rfl) ⟨156054, by rfl⟩ : syracuseStep 6658325 = 312109) (by norm_num)
theorem B4438883 : Blo 2189435 4438883 := bstep (se 1 (by rfl) ⟨3329162, by rfl⟩ : syracuseStep 4438883 = 6658325) B6658325
theorem B2959255 : Blo 2189435 2959255 := bstep (se 1 (by rfl) ⟨2219441, by rfl⟩ : syracuseStep 2959255 = 4438883) B4438883
theorem B3945673 : Blo 2189435 3945673 := bstep (se 2 (by rfl) ⟨1479627, by rfl⟩ : syracuseStep 3945673 = 2959255) B2959255
theorem B5260897 : Blo 2189435 5260897 := bstep (se 2 (by rfl) ⟨1972836, by rfl⟩ : syracuseStep 5260897 = 3945673) B3945673
theorem B7014529 : Blo 2189435 7014529 := bstep (se 2 (by rfl) ⟨2630448, by rfl⟩ : syracuseStep 7014529 = 5260897) B5260897
theorem B37410821 : Blo 2189435 37410821 := bstep (se 4 (by rfl) ⟨3507264, by rfl⟩ : syracuseStep 37410821 = 7014529) B7014529
theorem B24940547 : Blo 2189435 24940547 := bstep (se 1 (by rfl) ⟨18705410, by rfl⟩ : syracuseStep 24940547 = 37410821) B37410821
theorem B16627031 : Blo 2189435 16627031 := bstep (se 1 (by rfl) ⟨12470273, by rfl⟩ : syracuseStep 16627031 = 24940547) B24940547
theorem B11084687 : Blo 2189435 11084687 := bstep (se 1 (by rfl) ⟨8313515, by rfl⟩ : syracuseStep 11084687 = 16627031) B16627031
theorem B7389791 : Blo 2189435 7389791 := bstep (se 1 (by rfl) ⟨5542343, by rfl⟩ : syracuseStep 7389791 = 11084687) B11084687
theorem B4926527 : Blo 2189435 4926527 := bstep (se 1 (by rfl) ⟨3694895, by rfl⟩ : syracuseStep 4926527 = 7389791) B7389791
theorem B3284351 : Blo 2189435 3284351 := bstep (se 1 (by rfl) ⟨2463263, by rfl⟩ : syracuseStep 3284351 = 4926527) B4926527
theorem B2189567 : Blo 2189435 2189567 := bstep (se 1 (by rfl) ⟨1642175, by rfl⟩ : syracuseStep 2189567 = 3284351) B3284351
theorem B3284357 : Blo 2189435 3284357 := bbase (se 4 (by rfl) ⟨307908, by rfl⟩ : syracuseStep 3284357 = 615817) (by norm_num)
theorem B2189571 : Blo 2189435 2189571 := bstep (se 1 (by rfl) ⟨1642178, by rfl⟩ : syracuseStep 2189571 = 3284357) B3284357
theorem B3694909 : Blo 2189435 3694909 := bbase (se 3 (by rfl) ⟨692795, by rfl⟩ : syracuseStep 3694909 = 1385591) (by norm_num)
theorem B4926545 : Blo 2189435 4926545 := bstep (se 2 (by rfl) ⟨1847454, by rfl⟩ : syracuseStep 4926545 = 3694909) B3694909
theorem B3284363 : Blo 2189435 3284363 := bstep (se 1 (by rfl) ⟨2463272, by rfl⟩ : syracuseStep 3284363 = 4926545) B4926545
theorem B2189575 : Blo 2189435 2189575 := bstep (se 1 (by rfl) ⟨1642181, by rfl⟩ : syracuseStep 2189575 = 3284363) B3284363
theorem B2463277 : Blo 2189435 2463277 := bbase (se 3 (by rfl) ⟨461864, by rfl⟩ : syracuseStep 2463277 = 923729) (by norm_num)
theorem B3284369 : Blo 2189435 3284369 := bstep (se 2 (by rfl) ⟨1231638, by rfl⟩ : syracuseStep 3284369 = 2463277) B2463277
theorem B2189579 : Blo 2189435 2189579 := bstep (se 1 (by rfl) ⟨1642184, by rfl⟩ : syracuseStep 2189579 = 3284369) B3284369
theorem B7389845 : Blo 2189435 7389845 := bbase (se 6 (by rfl) ⟨173199, by rfl⟩ : syracuseStep 7389845 = 346399) (by norm_num)
theorem B4926563 : Blo 2189435 4926563 := bstep (se 1 (by rfl) ⟨3694922, by rfl⟩ : syracuseStep 4926563 = 7389845) B7389845
theorem B3284375 : Blo 2189435 3284375 := bstep (se 1 (by rfl) ⟨2463281, by rfl⟩ : syracuseStep 3284375 = 4926563) B4926563
theorem B2189583 : Blo 2189435 2189583 := bstep (se 1 (by rfl) ⟨1642187, by rfl⟩ : syracuseStep 2189583 = 3284375) B3284375
theorem B3284381 : Blo 2189435 3284381 := bbase (se 3 (by rfl) ⟨615821, by rfl⟩ : syracuseStep 3284381 = 1231643) (by norm_num)
theorem B2189587 : Blo 2189435 2189587 := bstep (se 1 (by rfl) ⟨1642190, by rfl⟩ : syracuseStep 2189587 = 3284381) B3284381
theorem B4926581 : Blo 2189435 4926581 := bbase (se 5 (by rfl) ⟨230933, by rfl⟩ : syracuseStep 4926581 = 461867) (by norm_num)
theorem B3284387 : Blo 2189435 3284387 := bstep (se 1 (by rfl) ⟨2463290, by rfl⟩ : syracuseStep 3284387 = 4926581) B4926581
theorem B2189591 : Blo 2189435 2189591 := bstep (se 1 (by rfl) ⟨1642193, by rfl⟩ : syracuseStep 2189591 = 3284387) B3284387
theorem B18705653 : Blo 2189435 18705653 := bbase (se 5 (by rfl) ⟨876827, by rfl⟩ : syracuseStep 18705653 = 1753655) (by norm_num)
theorem B12470435 : Blo 2189435 12470435 := bstep (se 1 (by rfl) ⟨9352826, by rfl⟩ : syracuseStep 12470435 = 18705653) B18705653
theorem B8313623 : Blo 2189435 8313623 := bstep (se 1 (by rfl) ⟨6235217, by rfl⟩ : syracuseStep 8313623 = 12470435) B12470435
theorem B5542415 : Blo 2189435 5542415 := bstep (se 1 (by rfl) ⟨4156811, by rfl⟩ : syracuseStep 5542415 = 8313623) B8313623
theorem B3694943 : Blo 2189435 3694943 := bstep (se 1 (by rfl) ⟨2771207, by rfl⟩ : syracuseStep 3694943 = 5542415) B5542415
theorem B2463295 : Blo 2189435 2463295 := bstep (se 1 (by rfl) ⟨1847471, by rfl⟩ : syracuseStep 2463295 = 3694943) B3694943
theorem B3284393 : Blo 2189435 3284393 := bstep (se 2 (by rfl) ⟨1231647, by rfl⟩ : syracuseStep 3284393 = 2463295) B2463295
theorem B2189595 : Blo 2189435 2189595 := bstep (se 1 (by rfl) ⟨1642196, by rfl⟩ : syracuseStep 2189595 = 3284393) B3284393
theorem B8313637 : Blo 2189435 8313637 := bbase (se 4 (by rfl) ⟨779403, by rfl⟩ : syracuseStep 8313637 = 1558807) (by norm_num)
theorem B11084849 : Blo 2189435 11084849 := bstep (se 2 (by rfl) ⟨4156818, by rfl⟩ : syracuseStep 11084849 = 8313637) B8313637
theorem B7389899 : Blo 2189435 7389899 := bstep (se 1 (by rfl) ⟨5542424, by rfl⟩ : syracuseStep 7389899 = 11084849) B11084849
theorem B4926599 : Blo 2189435 4926599 := bstep (se 1 (by rfl) ⟨3694949, by rfl⟩ : syracuseStep 4926599 = 7389899) B7389899
theorem B3284399 : Blo 2189435 3284399 := bstep (se 1 (by rfl) ⟨2463299, by rfl⟩ : syracuseStep 3284399 = 4926599) B4926599
theorem B2189599 : Blo 2189435 2189599 := bstep (se 1 (by rfl) ⟨1642199, by rfl⟩ : syracuseStep 2189599 = 3284399) B3284399
theorem B3284405 : Blo 2189435 3284405 := bbase (se 5 (by rfl) ⟨153956, by rfl⟩ : syracuseStep 3284405 = 307913) (by norm_num)
theorem B2189603 : Blo 2189435 2189603 := bstep (se 1 (by rfl) ⟨1642202, by rfl⟩ : syracuseStep 2189603 = 3284405) B3284405
theorem B5542445 : Blo 2189435 5542445 := bbase (se 3 (by rfl) ⟨1039208, by rfl⟩ : syracuseStep 5542445 = 2078417) (by norm_num)
theorem B3694963 : Blo 2189435 3694963 := bstep (se 1 (by rfl) ⟨2771222, by rfl⟩ : syracuseStep 3694963 = 5542445) B5542445
theorem B4926617 : Blo 2189435 4926617 := bstep (se 2 (by rfl) ⟨1847481, by rfl⟩ : syracuseStep 4926617 = 3694963) B3694963
theorem B3284411 : Blo 2189435 3284411 := bstep (se 1 (by rfl) ⟨2463308, by rfl⟩ : syracuseStep 3284411 = 4926617) B4926617
theorem B2189607 : Blo 2189435 2189607 := bstep (se 1 (by rfl) ⟨1642205, by rfl⟩ : syracuseStep 2189607 = 3284411) B3284411
theorem B2463313 : Blo 2189435 2463313 := bbase (se 2 (by rfl) ⟨923742, by rfl⟩ : syracuseStep 2463313 = 1847485) (by norm_num)
theorem B3284417 : Blo 2189435 3284417 := bstep (se 2 (by rfl) ⟨1231656, by rfl⟩ : syracuseStep 3284417 = 2463313) B2463313
theorem B2189611 : Blo 2189435 2189611 := bstep (se 1 (by rfl) ⟨1642208, by rfl⟩ : syracuseStep 2189611 = 3284417) B3284417
theorem B3117637 : Blo 2189435 3117637 := bbase (se 4 (by rfl) ⟨292278, by rfl⟩ : syracuseStep 3117637 = 584557) (by norm_num)
theorem B4156849 : Blo 2189435 4156849 := bstep (se 2 (by rfl) ⟨1558818, by rfl⟩ : syracuseStep 4156849 = 3117637) B3117637
theorem B5542465 : Blo 2189435 5542465 := bstep (se 2 (by rfl) ⟨2078424, by rfl⟩ : syracuseStep 5542465 = 4156849) B4156849
theorem B7389953 : Blo 2189435 7389953 := bstep (se 2 (by rfl) ⟨2771232, by rfl⟩ : syracuseStep 7389953 = 5542465) B5542465
theorem B4926635 : Blo 2189435 4926635 := bstep (se 1 (by rfl) ⟨3694976, by rfl⟩ : syracuseStep 4926635 = 7389953) B7389953
theorem B3284423 : Blo 2189435 3284423 := bstep (se 1 (by rfl) ⟨2463317, by rfl⟩ : syracuseStep 3284423 = 4926635) B4926635
theorem B2189615 : Blo 2189435 2189615 := bstep (se 1 (by rfl) ⟨1642211, by rfl⟩ : syracuseStep 2189615 = 3284423) B3284423
theorem B3284429 : Blo 2189435 3284429 := bbase (se 3 (by rfl) ⟨615830, by rfl⟩ : syracuseStep 3284429 = 1231661) (by norm_num)
theorem B2189619 : Blo 2189435 2189619 := bstep (se 1 (by rfl) ⟨1642214, by rfl⟩ : syracuseStep 2189619 = 3284429) B3284429
theorem B4926653 : Blo 2189435 4926653 := bbase (se 3 (by rfl) ⟨923747, by rfl⟩ : syracuseStep 4926653 = 1847495) (by norm_num)
theorem B3284435 : Blo 2189435 3284435 := bstep (se 1 (by rfl) ⟨2463326, by rfl⟩ : syracuseStep 3284435 = 4926653) B4926653
theorem B2189623 : Blo 2189435 2189623 := bstep (se 1 (by rfl) ⟨1642217, by rfl⟩ : syracuseStep 2189623 = 3284435) B3284435
theorem B3694997 : Blo 2189435 3694997 := bbase (se 6 (by rfl) ⟨86601, by rfl⟩ : syracuseStep 3694997 = 173203) (by norm_num)
theorem B2463331 : Blo 2189435 2463331 := bstep (se 1 (by rfl) ⟨1847498, by rfl⟩ : syracuseStep 2463331 = 3694997) B3694997
theorem B3284441 : Blo 2189435 3284441 := bstep (se 2 (by rfl) ⟨1231665, by rfl⟩ : syracuseStep 3284441 = 2463331) B2463331
theorem B2189627 : Blo 2189435 2189627 := bstep (se 1 (by rfl) ⟨1642220, by rfl⟩ : syracuseStep 2189627 = 3284441) B3284441
theorem B2249789 : Blo 2189435 2249789 := bbase (se 3 (by rfl) ⟨421835, by rfl⟩ : syracuseStep 2249789 = 843671) (by norm_num)
theorem B5999437 : Blo 2189435 5999437 := bstep (se 3 (by rfl) ⟨1124894, by rfl⟩ : syracuseStep 5999437 = 2249789) B2249789
theorem B7999249 : Blo 2189435 7999249 := bstep (se 2 (by rfl) ⟨2999718, by rfl⟩ : syracuseStep 7999249 = 5999437) B5999437
theorem B10665665 : Blo 2189435 10665665 := bstep (se 2 (by rfl) ⟨3999624, by rfl⟩ : syracuseStep 10665665 = 7999249) B7999249
theorem B7110443 : Blo 2189435 7110443 := bstep (se 1 (by rfl) ⟨5332832, by rfl⟩ : syracuseStep 7110443 = 10665665) B10665665
theorem B4740295 : Blo 2189435 4740295 := bstep (se 1 (by rfl) ⟨3555221, by rfl⟩ : syracuseStep 4740295 = 7110443) B7110443
theorem B6320393 : Blo 2189435 6320393 := bstep (se 2 (by rfl) ⟨2370147, by rfl⟩ : syracuseStep 6320393 = 4740295) B4740295
theorem B4213595 : Blo 2189435 4213595 := bstep (se 1 (by rfl) ⟨3160196, by rfl⟩ : syracuseStep 4213595 = 6320393) B6320393
theorem B2809063 : Blo 2189435 2809063 := bstep (se 1 (by rfl) ⟨2106797, by rfl⟩ : syracuseStep 2809063 = 4213595) B4213595
theorem B14981669 : Blo 2189435 14981669 := bstep (se 4 (by rfl) ⟨1404531, by rfl⟩ : syracuseStep 14981669 = 2809063) B2809063
theorem B9987779 : Blo 2189435 9987779 := bstep (se 1 (by rfl) ⟨7490834, by rfl⟩ : syracuseStep 9987779 = 14981669) B14981669
theorem B6658519 : Blo 2189435 6658519 := bstep (se 1 (by rfl) ⟨4993889, by rfl⟩ : syracuseStep 6658519 = 9987779) B9987779
theorem B8878025 : Blo 2189435 8878025 := bstep (se 2 (by rfl) ⟨3329259, by rfl⟩ : syracuseStep 8878025 = 6658519) B6658519
theorem B5918683 : Blo 2189435 5918683 := bstep (se 1 (by rfl) ⟨4439012, by rfl⟩ : syracuseStep 5918683 = 8878025) B8878025
theorem B7891577 : Blo 2189435 7891577 := bstep (se 2 (by rfl) ⟨2959341, by rfl⟩ : syracuseStep 7891577 = 5918683) B5918683
theorem B5261051 : Blo 2189435 5261051 := bstep (se 1 (by rfl) ⟨3945788, by rfl⟩ : syracuseStep 5261051 = 7891577) B7891577
theorem B14029469 : Blo 2189435 14029469 := bstep (se 3 (by rfl) ⟨2630525, by rfl⟩ : syracuseStep 14029469 = 5261051) B5261051
theorem B9352979 : Blo 2189435 9352979 := bstep (se 1 (by rfl) ⟨7014734, by rfl⟩ : syracuseStep 9352979 = 14029469) B14029469
theorem B6235319 : Blo 2189435 6235319 := bstep (se 1 (by rfl) ⟨4676489, by rfl⟩ : syracuseStep 6235319 = 9352979) B9352979
theorem B16627517 : Blo 2189435 16627517 := bstep (se 3 (by rfl) ⟨3117659, by rfl⟩ : syracuseStep 16627517 = 6235319) B6235319
theorem B11085011 : Blo 2189435 11085011 := bstep (se 1 (by rfl) ⟨8313758, by rfl⟩ : syracuseStep 11085011 = 16627517) B16627517
theorem B7390007 : Blo 2189435 7390007 := bstep (se 1 (by rfl) ⟨5542505, by rfl⟩ : syracuseStep 7390007 = 11085011) B11085011
theorem B4926671 : Blo 2189435 4926671 := bstep (se 1 (by rfl) ⟨3695003, by rfl⟩ : syracuseStep 4926671 = 7390007) B7390007
theorem B3284447 : Blo 2189435 3284447 := bstep (se 1 (by rfl) ⟨2463335, by rfl⟩ : syracuseStep 3284447 = 4926671) B4926671
theorem B2189631 : Blo 2189435 2189631 := bstep (se 1 (by rfl) ⟨1642223, by rfl⟩ : syracuseStep 2189631 = 3284447) B3284447
theorem B3284453 : Blo 2189435 3284453 := bbase (se 4 (by rfl) ⟨307917, by rfl⟩ : syracuseStep 3284453 = 615835) (by norm_num)
theorem B2189635 : Blo 2189435 2189635 := bstep (se 1 (by rfl) ⟨1642226, by rfl⟩ : syracuseStep 2189635 = 3284453) B3284453
theorem B17756117 : Blo 2189435 17756117 := bbase (se 7 (by rfl) ⟨208079, by rfl⟩ : syracuseStep 17756117 = 416159) (by norm_num)
theorem B11837411 : Blo 2189435 11837411 := bstep (se 1 (by rfl) ⟨8878058, by rfl⟩ : syracuseStep 11837411 = 17756117) B17756117
theorem B7891607 : Blo 2189435 7891607 := bstep (se 1 (by rfl) ⟨5918705, by rfl⟩ : syracuseStep 7891607 = 11837411) B11837411
theorem B21044285 : Blo 2189435 21044285 := bstep (se 3 (by rfl) ⟨3945803, by rfl⟩ : syracuseStep 21044285 = 7891607) B7891607
theorem B14029523 : Blo 2189435 14029523 := bstep (se 1 (by rfl) ⟨10522142, by rfl⟩ : syracuseStep 14029523 = 21044285) B21044285
theorem B9353015 : Blo 2189435 9353015 := bstep (se 1 (by rfl) ⟨7014761, by rfl⟩ : syracuseStep 9353015 = 14029523) B14029523
theorem B6235343 : Blo 2189435 6235343 := bstep (se 1 (by rfl) ⟨4676507, by rfl⟩ : syracuseStep 6235343 = 9353015) B9353015
theorem B4156895 : Blo 2189435 4156895 := bstep (se 1 (by rfl) ⟨3117671, by rfl⟩ : syracuseStep 4156895 = 6235343) B6235343
theorem B2771263 : Blo 2189435 2771263 := bstep (se 1 (by rfl) ⟨2078447, by rfl⟩ : syracuseStep 2771263 = 4156895) B4156895
theorem B3695017 : Blo 2189435 3695017 := bstep (se 2 (by rfl) ⟨1385631, by rfl⟩ : syracuseStep 3695017 = 2771263) B2771263
theorem B4926689 : Blo 2189435 4926689 := bstep (se 2 (by rfl) ⟨1847508, by rfl⟩ : syracuseStep 4926689 = 3695017) B3695017
theorem B3284459 : Blo 2189435 3284459 := bstep (se 1 (by rfl) ⟨2463344, by rfl⟩ : syracuseStep 3284459 = 4926689) B4926689
theorem B2189639 : Blo 2189435 2189639 := bstep (se 1 (by rfl) ⟨1642229, by rfl⟩ : syracuseStep 2189639 = 3284459) B3284459
theorem B2463349 : Blo 2189435 2463349 := bbase (se 5 (by rfl) ⟨115469, by rfl⟩ : syracuseStep 2463349 = 230939) (by norm_num)
theorem B3284465 : Blo 2189435 3284465 := bstep (se 2 (by rfl) ⟨1231674, by rfl⟩ : syracuseStep 3284465 = 2463349) B2463349
theorem B2189643 : Blo 2189435 2189643 := bstep (se 1 (by rfl) ⟨1642232, by rfl⟩ : syracuseStep 2189643 = 3284465) B3284465
theorem B2771273 : Blo 2189435 2771273 := bbase (se 2 (by rfl) ⟨1039227, by rfl⟩ : syracuseStep 2771273 = 2078455) (by norm_num)
theorem B7390061 : Blo 2189435 7390061 := bstep (se 3 (by rfl) ⟨1385636, by rfl⟩ : syracuseStep 7390061 = 2771273) B2771273
theorem B4926707 : Blo 2189435 4926707 := bstep (se 1 (by rfl) ⟨3695030, by rfl⟩ : syracuseStep 4926707 = 7390061) B7390061
theorem B3284471 : Blo 2189435 3284471 := bstep (se 1 (by rfl) ⟨2463353, by rfl⟩ : syracuseStep 3284471 = 4926707) B4926707
theorem B2189647 : Blo 2189435 2189647 := bstep (se 1 (by rfl) ⟨1642235, by rfl⟩ : syracuseStep 2189647 = 3284471) B3284471
theorem B3284477 : Blo 2189435 3284477 := bbase (se 3 (by rfl) ⟨615839, by rfl⟩ : syracuseStep 3284477 = 1231679) (by norm_num)
theorem B2189651 : Blo 2189435 2189651 := bstep (se 1 (by rfl) ⟨1642238, by rfl⟩ : syracuseStep 2189651 = 3284477) B3284477
theorem B4926725 : Blo 2189435 4926725 := bbase (se 4 (by rfl) ⟨461880, by rfl⟩ : syracuseStep 4926725 = 923761) (by norm_num)
theorem B3284483 : Blo 2189435 3284483 := bstep (se 1 (by rfl) ⟨2463362, by rfl⟩ : syracuseStep 3284483 = 4926725) B4926725
theorem B2189655 : Blo 2189435 2189655 := bstep (se 1 (by rfl) ⟨1642241, by rfl⟩ : syracuseStep 2189655 = 3284483) B3284483
theorem B4156933 : Blo 2189435 4156933 := bbase (se 4 (by rfl) ⟨389712, by rfl⟩ : syracuseStep 4156933 = 779425) (by norm_num)
theorem B5542577 : Blo 2189435 5542577 := bstep (se 2 (by rfl) ⟨2078466, by rfl⟩ : syracuseStep 5542577 = 4156933) B4156933
theorem B3695051 : Blo 2189435 3695051 := bstep (se 1 (by rfl) ⟨2771288, by rfl⟩ : syracuseStep 3695051 = 5542577) B5542577
theorem B2463367 : Blo 2189435 2463367 := bstep (se 1 (by rfl) ⟨1847525, by rfl⟩ : syracuseStep 2463367 = 3695051) B3695051
theorem B3284489 : Blo 2189435 3284489 := bstep (se 2 (by rfl) ⟨1231683, by rfl⟩ : syracuseStep 3284489 = 2463367) B2463367
theorem B2189659 : Blo 2189435 2189659 := bstep (se 1 (by rfl) ⟨1642244, by rfl⟩ : syracuseStep 2189659 = 3284489) B3284489
theorem B11085173 : Blo 2189435 11085173 := bbase (se 5 (by rfl) ⟨519617, by rfl⟩ : syracuseStep 11085173 = 1039235) (by norm_num)
theorem B7390115 : Blo 2189435 7390115 := bstep (se 1 (by rfl) ⟨5542586, by rfl⟩ : syracuseStep 7390115 = 11085173) B11085173
theorem B4926743 : Blo 2189435 4926743 := bstep (se 1 (by rfl) ⟨3695057, by rfl⟩ : syracuseStep 4926743 = 7390115) B7390115
theorem B3284495 : Blo 2189435 3284495 := bstep (se 1 (by rfl) ⟨2463371, by rfl⟩ : syracuseStep 3284495 = 4926743) B4926743
theorem B2189663 : Blo 2189435 2189663 := bstep (se 1 (by rfl) ⟨1642247, by rfl⟩ : syracuseStep 2189663 = 3284495) B3284495
theorem B3284501 : Blo 2189435 3284501 := bbase (se 6 (by rfl) ⟨76980, by rfl⟩ : syracuseStep 3284501 = 153961) (by norm_num)
theorem B2189667 : Blo 2189435 2189667 := bstep (se 1 (by rfl) ⟨1642250, by rfl⟩ : syracuseStep 2189667 = 3284501) B3284501
theorem B5062117 : Blo 2189435 5062117 := bbase (se 4 (by rfl) ⟨474573, by rfl⟩ : syracuseStep 5062117 = 949147) (by norm_num)
theorem B6749489 : Blo 2189435 6749489 := bstep (se 2 (by rfl) ⟨2531058, by rfl⟩ : syracuseStep 6749489 = 5062117) B5062117
theorem B4499659 : Blo 2189435 4499659 := bstep (se 1 (by rfl) ⟨3374744, by rfl⟩ : syracuseStep 4499659 = 6749489) B6749489
theorem B5999545 : Blo 2189435 5999545 := bstep (se 2 (by rfl) ⟨2249829, by rfl⟩ : syracuseStep 5999545 = 4499659) B4499659
theorem B7999393 : Blo 2189435 7999393 := bstep (se 2 (by rfl) ⟨2999772, by rfl⟩ : syracuseStep 7999393 = 5999545) B5999545
theorem B10665857 : Blo 2189435 10665857 := bstep (se 2 (by rfl) ⟨3999696, by rfl⟩ : syracuseStep 10665857 = 7999393) B7999393
theorem B28442285 : Blo 2189435 28442285 := bstep (se 3 (by rfl) ⟨5332928, by rfl⟩ : syracuseStep 28442285 = 10665857) B10665857
theorem B18961523 : Blo 2189435 18961523 := bstep (se 1 (by rfl) ⟨14221142, by rfl⟩ : syracuseStep 18961523 = 28442285) B28442285
theorem B12641015 : Blo 2189435 12641015 := bstep (se 1 (by rfl) ⟨9480761, by rfl⟩ : syracuseStep 12641015 = 18961523) B18961523
theorem B8427343 : Blo 2189435 8427343 := bstep (se 1 (by rfl) ⟨6320507, by rfl⟩ : syracuseStep 8427343 = 12641015) B12641015
theorem B11236457 : Blo 2189435 11236457 := bstep (se 2 (by rfl) ⟨4213671, by rfl⟩ : syracuseStep 11236457 = 8427343) B8427343
theorem B7490971 : Blo 2189435 7490971 := bstep (se 1 (by rfl) ⟨5618228, by rfl⟩ : syracuseStep 7490971 = 11236457) B11236457
theorem B9987961 : Blo 2189435 9987961 := bstep (se 2 (by rfl) ⟨3745485, by rfl⟩ : syracuseStep 9987961 = 7490971) B7490971
theorem B13317281 : Blo 2189435 13317281 := bstep (se 2 (by rfl) ⟨4993980, by rfl⟩ : syracuseStep 13317281 = 9987961) B9987961
theorem B8878187 : Blo 2189435 8878187 := bstep (se 1 (by rfl) ⟨6658640, by rfl⟩ : syracuseStep 8878187 = 13317281) B13317281
theorem B23675165 : Blo 2189435 23675165 := bstep (se 3 (by rfl) ⟨4439093, by rfl⟩ : syracuseStep 23675165 = 8878187) B8878187
theorem B15783443 : Blo 2189435 15783443 := bstep (se 1 (by rfl) ⟨11837582, by rfl⟩ : syracuseStep 15783443 = 23675165) B23675165
theorem B10522295 : Blo 2189435 10522295 := bstep (se 1 (by rfl) ⟨7891721, by rfl⟩ : syracuseStep 10522295 = 15783443) B15783443
theorem B7014863 : Blo 2189435 7014863 := bstep (se 1 (by rfl) ⟨5261147, by rfl⟩ : syracuseStep 7014863 = 10522295) B10522295
theorem B18706301 : Blo 2189435 18706301 := bstep (se 3 (by rfl) ⟨3507431, by rfl⟩ : syracuseStep 18706301 = 7014863) B7014863
theorem B12470867 : Blo 2189435 12470867 := bstep (se 1 (by rfl) ⟨9353150, by rfl⟩ : syracuseStep 12470867 = 18706301) B18706301
theorem B8313911 : Blo 2189435 8313911 := bstep (se 1 (by rfl) ⟨6235433, by rfl⟩ : syracuseStep 8313911 = 12470867) B12470867
theorem B5542607 : Blo 2189435 5542607 := bstep (se 1 (by rfl) ⟨4156955, by rfl⟩ : syracuseStep 5542607 = 8313911) B8313911
theorem B3695071 : Blo 2189435 3695071 := bstep (se 1 (by rfl) ⟨2771303, by rfl⟩ : syracuseStep 3695071 = 5542607) B5542607
theorem B4926761 : Blo 2189435 4926761 := bstep (se 2 (by rfl) ⟨1847535, by rfl⟩ : syracuseStep 4926761 = 3695071) B3695071
theorem B3284507 : Blo 2189435 3284507 := bstep (se 1 (by rfl) ⟨2463380, by rfl⟩ : syracuseStep 3284507 = 4926761) B4926761
theorem B2189671 : Blo 2189435 2189671 := bstep (se 1 (by rfl) ⟨1642253, by rfl⟩ : syracuseStep 2189671 = 3284507) B3284507
theorem B2463385 : Blo 2189435 2463385 := bbase (se 2 (by rfl) ⟨923769, by rfl⟩ : syracuseStep 2463385 = 1847539) (by norm_num)
theorem B3284513 : Blo 2189435 3284513 := bstep (se 2 (by rfl) ⟨1231692, by rfl⟩ : syracuseStep 3284513 = 2463385) B2463385
theorem B2189675 : Blo 2189435 2189675 := bstep (se 1 (by rfl) ⟨1642256, by rfl⟩ : syracuseStep 2189675 = 3284513) B3284513
theorem B8313941 : Blo 2189435 8313941 := bbase (se 8 (by rfl) ⟨48714, by rfl⟩ : syracuseStep 8313941 = 97429) (by norm_num)
theorem B5542627 : Blo 2189435 5542627 := bstep (se 1 (by rfl) ⟨4156970, by rfl⟩ : syracuseStep 5542627 = 8313941) B8313941
theorem B7390169 : Blo 2189435 7390169 := bstep (se 2 (by rfl) ⟨2771313, by rfl⟩ : syracuseStep 7390169 = 5542627) B5542627
theorem B4926779 : Blo 2189435 4926779 := bstep (se 1 (by rfl) ⟨3695084, by rfl⟩ : syracuseStep 4926779 = 7390169) B7390169
theorem B3284519 : Blo 2189435 3284519 := bstep (se 1 (by rfl) ⟨2463389, by rfl⟩ : syracuseStep 3284519 = 4926779) B4926779
theorem B2189679 : Blo 2189435 2189679 := bstep (se 1 (by rfl) ⟨1642259, by rfl⟩ : syracuseStep 2189679 = 3284519) B3284519
theorem B3284525 : Blo 2189435 3284525 := bbase (se 3 (by rfl) ⟨615848, by rfl⟩ : syracuseStep 3284525 = 1231697) (by norm_num)
theorem B2189683 : Blo 2189435 2189683 := bstep (se 1 (by rfl) ⟨1642262, by rfl⟩ : syracuseStep 2189683 = 3284525) B3284525
theorem B4926797 : Blo 2189435 4926797 := bbase (se 3 (by rfl) ⟨923774, by rfl⟩ : syracuseStep 4926797 = 1847549) (by norm_num)
theorem B3284531 : Blo 2189435 3284531 := bstep (se 1 (by rfl) ⟨2463398, by rfl⟩ : syracuseStep 3284531 = 4926797) B4926797
theorem B2189687 : Blo 2189435 2189687 := bstep (se 1 (by rfl) ⟨1642265, by rfl⟩ : syracuseStep 2189687 = 3284531) B3284531
theorem B2771329 : Blo 2189435 2771329 := bbase (se 2 (by rfl) ⟨1039248, by rfl⟩ : syracuseStep 2771329 = 2078497) (by norm_num)
theorem B3695105 : Blo 2189435 3695105 := bstep (se 2 (by rfl) ⟨1385664, by rfl⟩ : syracuseStep 3695105 = 2771329) B2771329
theorem B2463403 : Blo 2189435 2463403 := bstep (se 1 (by rfl) ⟨1847552, by rfl⟩ : syracuseStep 2463403 = 3695105) B3695105
theorem B3284537 : Blo 2189435 3284537 := bstep (se 2 (by rfl) ⟨1231701, by rfl⟩ : syracuseStep 3284537 = 2463403) B2463403
theorem B2189691 : Blo 2189435 2189691 := bstep (se 1 (by rfl) ⟨1642268, by rfl⟩ : syracuseStep 2189691 = 3284537) B3284537
theorem B2338313 : Blo 2189435 2338313 := bbase (se 2 (by rfl) ⟨876867, by rfl⟩ : syracuseStep 2338313 = 1753735) (by norm_num)
theorem B24942005 : Blo 2189435 24942005 := bstep (se 5 (by rfl) ⟨1169156, by rfl⟩ : syracuseStep 24942005 = 2338313) B2338313
theorem B16628003 : Blo 2189435 16628003 := bstep (se 1 (by rfl) ⟨12471002, by rfl⟩ : syracuseStep 16628003 = 24942005) B24942005
theorem B11085335 : Blo 2189435 11085335 := bstep (se 1 (by rfl) ⟨8314001, by rfl⟩ : syracuseStep 11085335 = 16628003) B16628003
theorem B7390223 : Blo 2189435 7390223 := bstep (se 1 (by rfl) ⟨5542667, by rfl⟩ : syracuseStep 7390223 = 11085335) B11085335
theorem B4926815 : Blo 2189435 4926815 := bstep (se 1 (by rfl) ⟨3695111, by rfl⟩ : syracuseStep 4926815 = 7390223) B7390223
theorem B3284543 : Blo 2189435 3284543 := bstep (se 1 (by rfl) ⟨2463407, by rfl⟩ : syracuseStep 3284543 = 4926815) B4926815
theorem B2189695 : Blo 2189435 2189695 := bstep (se 1 (by rfl) ⟨1642271, by rfl⟩ : syracuseStep 2189695 = 3284543) B3284543
theorem B3284549 : Blo 2189435 3284549 := bbase (se 4 (by rfl) ⟨307926, by rfl⟩ : syracuseStep 3284549 = 615853) (by norm_num)
theorem B2189699 : Blo 2189435 2189699 := bstep (se 1 (by rfl) ⟨1642274, by rfl⟩ : syracuseStep 2189699 = 3284549) B3284549
theorem B3695125 : Blo 2189435 3695125 := bbase (se 6 (by rfl) ⟨86604, by rfl⟩ : syracuseStep 3695125 = 173209) (by norm_num)
theorem B4926833 : Blo 2189435 4926833 := bstep (se 2 (by rfl) ⟨1847562, by rfl⟩ : syracuseStep 4926833 = 3695125) B3695125
theorem B3284555 : Blo 2189435 3284555 := bstep (se 1 (by rfl) ⟨2463416, by rfl⟩ : syracuseStep 3284555 = 4926833) B4926833
theorem B2189703 : Blo 2189435 2189703 := bstep (se 1 (by rfl) ⟨1642277, by rfl⟩ : syracuseStep 2189703 = 3284555) B3284555
theorem B2463421 : Blo 2189435 2463421 := bbase (se 3 (by rfl) ⟨461891, by rfl⟩ : syracuseStep 2463421 = 923783) (by norm_num)
theorem B3284561 : Blo 2189435 3284561 := bstep (se 2 (by rfl) ⟨1231710, by rfl⟩ : syracuseStep 3284561 = 2463421) B2463421
theorem B2189707 : Blo 2189435 2189707 := bstep (se 1 (by rfl) ⟨1642280, by rfl⟩ : syracuseStep 2189707 = 3284561) B3284561
theorem B7390277 : Blo 2189435 7390277 := bbase (se 4 (by rfl) ⟨692838, by rfl⟩ : syracuseStep 7390277 = 1385677) (by norm_num)
theorem B4926851 : Blo 2189435 4926851 := bstep (se 1 (by rfl) ⟨3695138, by rfl⟩ : syracuseStep 4926851 = 7390277) B7390277
theorem B3284567 : Blo 2189435 3284567 := bstep (se 1 (by rfl) ⟨2463425, by rfl⟩ : syracuseStep 3284567 = 4926851) B4926851
theorem B2189711 : Blo 2189435 2189711 := bstep (se 1 (by rfl) ⟨1642283, by rfl⟩ : syracuseStep 2189711 = 3284567) B3284567
theorem B3284573 : Blo 2189435 3284573 := bbase (se 3 (by rfl) ⟨615857, by rfl⟩ : syracuseStep 3284573 = 1231715) (by norm_num)
theorem B2189715 : Blo 2189435 2189715 := bstep (se 1 (by rfl) ⟨1642286, by rfl⟩ : syracuseStep 2189715 = 3284573) B3284573
theorem B4926869 : Blo 2189435 4926869 := bbase (se 6 (by rfl) ⟨115473, by rfl⟩ : syracuseStep 4926869 = 230947) (by norm_num)
theorem B3284579 : Blo 2189435 3284579 := bstep (se 1 (by rfl) ⟨2463434, by rfl⟩ : syracuseStep 3284579 = 4926869) B4926869
theorem B2189719 : Blo 2189435 2189719 := bstep (se 1 (by rfl) ⟨1642289, by rfl⟩ : syracuseStep 2189719 = 3284579) B3284579
theorem B5918933 : Blo 2189435 5918933 := bbase (se 7 (by rfl) ⟨69362, by rfl⟩ : syracuseStep 5918933 = 138725) (by norm_num)
theorem B15783821 : Blo 2189435 15783821 := bstep (se 3 (by rfl) ⟨2959466, by rfl⟩ : syracuseStep 15783821 = 5918933) B5918933
theorem B10522547 : Blo 2189435 10522547 := bstep (se 1 (by rfl) ⟨7891910, by rfl⟩ : syracuseStep 10522547 = 15783821) B15783821
theorem B7015031 : Blo 2189435 7015031 := bstep (se 1 (by rfl) ⟨5261273, by rfl⟩ : syracuseStep 7015031 = 10522547) B10522547
theorem B4676687 : Blo 2189435 4676687 := bstep (se 1 (by rfl) ⟨3507515, by rfl⟩ : syracuseStep 4676687 = 7015031) B7015031
theorem B3117791 : Blo 2189435 3117791 := bstep (se 1 (by rfl) ⟨2338343, by rfl⟩ : syracuseStep 3117791 = 4676687) B4676687
theorem B8314109 : Blo 2189435 8314109 := bstep (se 3 (by rfl) ⟨1558895, by rfl⟩ : syracuseStep 8314109 = 3117791) B3117791
theorem B5542739 : Blo 2189435 5542739 := bstep (se 1 (by rfl) ⟨4157054, by rfl⟩ : syracuseStep 5542739 = 8314109) B8314109
theorem B3695159 : Blo 2189435 3695159 := bstep (se 1 (by rfl) ⟨2771369, by rfl⟩ : syracuseStep 3695159 = 5542739) B5542739
theorem B2463439 : Blo 2189435 2463439 := bstep (se 1 (by rfl) ⟨1847579, by rfl⟩ : syracuseStep 2463439 = 3695159) B3695159
theorem B3284585 : Blo 2189435 3284585 := bstep (se 2 (by rfl) ⟨1231719, by rfl⟩ : syracuseStep 3284585 = 2463439) B2463439
theorem B2189723 : Blo 2189435 2189723 := bstep (se 1 (by rfl) ⟨1642292, by rfl⟩ : syracuseStep 2189723 = 3284585) B3284585
theorem B2630641 : Blo 2189435 2630641 := bbase (se 2 (by rfl) ⟨986490, by rfl⟩ : syracuseStep 2630641 = 1972981) (by norm_num)
theorem B3507521 : Blo 2189435 3507521 := bstep (se 2 (by rfl) ⟨1315320, by rfl⟩ : syracuseStep 3507521 = 2630641) B2630641
theorem B9353389 : Blo 2189435 9353389 := bstep (se 3 (by rfl) ⟨1753760, by rfl⟩ : syracuseStep 9353389 = 3507521) B3507521
theorem B12471185 : Blo 2189435 12471185 := bstep (se 2 (by rfl) ⟨4676694, by rfl⟩ : syracuseStep 12471185 = 9353389) B9353389
theorem B8314123 : Blo 2189435 8314123 := bstep (se 1 (by rfl) ⟨6235592, by rfl⟩ : syracuseStep 8314123 = 12471185) B12471185
theorem B11085497 : Blo 2189435 11085497 := bstep (se 2 (by rfl) ⟨4157061, by rfl⟩ : syracuseStep 11085497 = 8314123) B8314123
theorem B7390331 : Blo 2189435 7390331 := bstep (se 1 (by rfl) ⟨5542748, by rfl⟩ : syracuseStep 7390331 = 11085497) B11085497
theorem B4926887 : Blo 2189435 4926887 := bstep (se 1 (by rfl) ⟨3695165, by rfl⟩ : syracuseStep 4926887 = 7390331) B7390331
theorem B3284591 : Blo 2189435 3284591 := bstep (se 1 (by rfl) ⟨2463443, by rfl⟩ : syracuseStep 3284591 = 4926887) B4926887
theorem B2189727 : Blo 2189435 2189727 := bstep (se 1 (by rfl) ⟨1642295, by rfl⟩ : syracuseStep 2189727 = 3284591) B3284591
theorem B3284597 : Blo 2189435 3284597 := bbase (se 5 (by rfl) ⟨153965, by rfl⟩ : syracuseStep 3284597 = 307931) (by norm_num)
theorem B2189731 : Blo 2189435 2189731 := bstep (se 1 (by rfl) ⟨1642298, by rfl⟩ : syracuseStep 2189731 = 3284597) B3284597
theorem B4157077 : Blo 2189435 4157077 := bbase (se 6 (by rfl) ⟨97431, by rfl⟩ : syracuseStep 4157077 = 194863) (by norm_num)
theorem B5542769 : Blo 2189435 5542769 := bstep (se 2 (by rfl) ⟨2078538, by rfl⟩ : syracuseStep 5542769 = 4157077) B4157077
theorem B3695179 : Blo 2189435 3695179 := bstep (se 1 (by rfl) ⟨2771384, by rfl⟩ : syracuseStep 3695179 = 5542769) B5542769
theorem B4926905 : Blo 2189435 4926905 := bstep (se 2 (by rfl) ⟨1847589, by rfl⟩ : syracuseStep 4926905 = 3695179) B3695179
theorem B3284603 : Blo 2189435 3284603 := bstep (se 1 (by rfl) ⟨2463452, by rfl⟩ : syracuseStep 3284603 = 4926905) B4926905
theorem B2189735 : Blo 2189435 2189735 := bstep (se 1 (by rfl) ⟨1642301, by rfl⟩ : syracuseStep 2189735 = 3284603) B3284603
theorem B2463457 : Blo 2189435 2463457 := bbase (se 2 (by rfl) ⟨923796, by rfl⟩ : syracuseStep 2463457 = 1847593) (by norm_num)
theorem B3284609 : Blo 2189435 3284609 := bstep (se 2 (by rfl) ⟨1231728, by rfl⟩ : syracuseStep 3284609 = 2463457) B2463457
theorem B2189739 : Blo 2189435 2189739 := bstep (se 1 (by rfl) ⟨1642304, by rfl⟩ : syracuseStep 2189739 = 3284609) B3284609
theorem B5542789 : Blo 2189435 5542789 := bbase (se 4 (by rfl) ⟨519636, by rfl⟩ : syracuseStep 5542789 = 1039273) (by norm_num)
theorem B7390385 : Blo 2189435 7390385 := bstep (se 2 (by rfl) ⟨2771394, by rfl⟩ : syracuseStep 7390385 = 5542789) B5542789
theorem B4926923 : Blo 2189435 4926923 := bstep (se 1 (by rfl) ⟨3695192, by rfl⟩ : syracuseStep 4926923 = 7390385) B7390385
theorem B3284615 : Blo 2189435 3284615 := bstep (se 1 (by rfl) ⟨2463461, by rfl⟩ : syracuseStep 3284615 = 4926923) B4926923
theorem B2189743 : Blo 2189435 2189743 := bstep (se 1 (by rfl) ⟨1642307, by rfl⟩ : syracuseStep 2189743 = 3284615) B3284615
theorem B3284621 : Blo 2189435 3284621 := bbase (se 3 (by rfl) ⟨615866, by rfl⟩ : syracuseStep 3284621 = 1231733) (by norm_num)
theorem B2189747 : Blo 2189435 2189747 := bstep (se 1 (by rfl) ⟨1642310, by rfl⟩ : syracuseStep 2189747 = 3284621) B3284621
theorem B4926941 : Blo 2189435 4926941 := bbase (se 3 (by rfl) ⟨923801, by rfl⟩ : syracuseStep 4926941 = 1847603) (by norm_num)
theorem B3284627 : Blo 2189435 3284627 := bstep (se 1 (by rfl) ⟨2463470, by rfl⟩ : syracuseStep 3284627 = 4926941) B4926941
theorem B2189751 : Blo 2189435 2189751 := bstep (se 1 (by rfl) ⟨1642313, by rfl⟩ : syracuseStep 2189751 = 3284627) B3284627
theorem B3695213 : Blo 2189435 3695213 := bbase (se 3 (by rfl) ⟨692852, by rfl⟩ : syracuseStep 3695213 = 1385705) (by norm_num)
theorem B2463475 : Blo 2189435 2463475 := bstep (se 1 (by rfl) ⟨1847606, by rfl⟩ : syracuseStep 2463475 = 3695213) B3695213
theorem B3284633 : Blo 2189435 3284633 := bstep (se 2 (by rfl) ⟨1231737, by rfl⟩ : syracuseStep 3284633 = 2463475) B2463475
theorem B2189755 : Blo 2189435 2189755 := bstep (se 1 (by rfl) ⟨1642316, by rfl⟩ : syracuseStep 2189755 = 3284633) B3284633
theorem B9481141 : Blo 2189435 9481141 := bbase (se 5 (by rfl) ⟨444428, by rfl⟩ : syracuseStep 9481141 = 888857) (by norm_num)
theorem B12641521 : Blo 2189435 12641521 := bstep (se 2 (by rfl) ⟨4740570, by rfl⟩ : syracuseStep 12641521 = 9481141) B9481141
theorem B16855361 : Blo 2189435 16855361 := bstep (se 2 (by rfl) ⟨6320760, by rfl⟩ : syracuseStep 16855361 = 12641521) B12641521
theorem B11236907 : Blo 2189435 11236907 := bstep (se 1 (by rfl) ⟨8427680, by rfl⟩ : syracuseStep 11236907 = 16855361) B16855361
theorem B7491271 : Blo 2189435 7491271 := bstep (se 1 (by rfl) ⟨5618453, by rfl⟩ : syracuseStep 7491271 = 11236907) B11236907
theorem B9988361 : Blo 2189435 9988361 := bstep (se 2 (by rfl) ⟨3745635, by rfl⟩ : syracuseStep 9988361 = 7491271) B7491271
theorem B6658907 : Blo 2189435 6658907 := bstep (se 1 (by rfl) ⟨4994180, by rfl⟩ : syracuseStep 6658907 = 9988361) B9988361
theorem B17757085 : Blo 2189435 17757085 := bstep (se 3 (by rfl) ⟨3329453, by rfl⟩ : syracuseStep 17757085 = 6658907) B6658907
theorem B23676113 : Blo 2189435 23676113 := bstep (se 2 (by rfl) ⟨8878542, by rfl⟩ : syracuseStep 23676113 = 17757085) B17757085
theorem B15784075 : Blo 2189435 15784075 := bstep (se 1 (by rfl) ⟨11838056, by rfl⟩ : syracuseStep 15784075 = 23676113) B23676113
theorem B21045433 : Blo 2189435 21045433 := bstep (se 2 (by rfl) ⟨7892037, by rfl⟩ : syracuseStep 21045433 = 15784075) B15784075
theorem B28060577 : Blo 2189435 28060577 := bstep (se 2 (by rfl) ⟨10522716, by rfl⟩ : syracuseStep 28060577 = 21045433) B21045433
theorem B18707051 : Blo 2189435 18707051 := bstep (se 1 (by rfl) ⟨14030288, by rfl⟩ : syracuseStep 18707051 = 28060577) B28060577
theorem B12471367 : Blo 2189435 12471367 := bstep (se 1 (by rfl) ⟨9353525, by rfl⟩ : syracuseStep 12471367 = 18707051) B18707051
theorem B16628489 : Blo 2189435 16628489 := bstep (se 2 (by rfl) ⟨6235683, by rfl⟩ : syracuseStep 16628489 = 12471367) B12471367
theorem B11085659 : Blo 2189435 11085659 := bstep (se 1 (by rfl) ⟨8314244, by rfl⟩ : syracuseStep 11085659 = 16628489) B16628489
theorem B7390439 : Blo 2189435 7390439 := bstep (se 1 (by rfl) ⟨5542829, by rfl⟩ : syracuseStep 7390439 = 11085659) B11085659
theorem B4926959 : Blo 2189435 4926959 := bstep (se 1 (by rfl) ⟨3695219, by rfl⟩ : syracuseStep 4926959 = 7390439) B7390439
theorem B3284639 : Blo 2189435 3284639 := bstep (se 1 (by rfl) ⟨2463479, by rfl⟩ : syracuseStep 3284639 = 4926959) B4926959
theorem B2189759 : Blo 2189435 2189759 := bstep (se 1 (by rfl) ⟨1642319, by rfl⟩ : syracuseStep 2189759 = 3284639) B3284639
theorem B3284645 : Blo 2189435 3284645 := bbase (se 4 (by rfl) ⟨307935, by rfl⟩ : syracuseStep 3284645 = 615871) (by norm_num)
theorem B2189763 : Blo 2189435 2189763 := bstep (se 1 (by rfl) ⟨1642322, by rfl⟩ : syracuseStep 2189763 = 3284645) B3284645
theorem B2771425 : Blo 2189435 2771425 := bbase (se 2 (by rfl) ⟨1039284, by rfl⟩ : syracuseStep 2771425 = 2078569) (by norm_num)
theorem B3695233 : Blo 2189435 3695233 := bstep (se 2 (by rfl) ⟨1385712, by rfl⟩ : syracuseStep 3695233 = 2771425) B2771425
theorem B4926977 : Blo 2189435 4926977 := bstep (se 2 (by rfl) ⟨1847616, by rfl⟩ : syracuseStep 4926977 = 3695233) B3695233
theorem B3284651 : Blo 2189435 3284651 := bstep (se 1 (by rfl) ⟨2463488, by rfl⟩ : syracuseStep 3284651 = 4926977) B4926977
theorem B2189767 : Blo 2189435 2189767 := bstep (se 1 (by rfl) ⟨1642325, by rfl⟩ : syracuseStep 2189767 = 3284651) B3284651
theorem B2463493 : Blo 2189435 2463493 := bbase (se 4 (by rfl) ⟨230952, by rfl⟩ : syracuseStep 2463493 = 461905) (by norm_num)
theorem B3284657 : Blo 2189435 3284657 := bstep (se 2 (by rfl) ⟨1231746, by rfl⟩ : syracuseStep 3284657 = 2463493) B2463493
theorem B2189771 : Blo 2189435 2189771 := bstep (se 1 (by rfl) ⟨1642328, by rfl⟩ : syracuseStep 2189771 = 3284657) B3284657
theorem B2219653 : Blo 2189435 2219653 := bbase (se 4 (by rfl) ⟨208092, by rfl⟩ : syracuseStep 2219653 = 416185) (by norm_num)
theorem B11838149 : Blo 2189435 11838149 := bstep (se 4 (by rfl) ⟨1109826, by rfl⟩ : syracuseStep 11838149 = 2219653) B2219653
theorem B7892099 : Blo 2189435 7892099 := bstep (se 1 (by rfl) ⟨5919074, by rfl⟩ : syracuseStep 7892099 = 11838149) B11838149
theorem B5261399 : Blo 2189435 5261399 := bstep (se 1 (by rfl) ⟨3946049, by rfl⟩ : syracuseStep 5261399 = 7892099) B7892099
theorem B3507599 : Blo 2189435 3507599 := bstep (se 1 (by rfl) ⟨2630699, by rfl⟩ : syracuseStep 3507599 = 5261399) B5261399
theorem B2338399 : Blo 2189435 2338399 := bstep (se 1 (by rfl) ⟨1753799, by rfl⟩ : syracuseStep 2338399 = 3507599) B3507599
theorem B3117865 : Blo 2189435 3117865 := bstep (se 2 (by rfl) ⟨1169199, by rfl⟩ : syracuseStep 3117865 = 2338399) B2338399
theorem B4157153 : Blo 2189435 4157153 := bstep (se 2 (by rfl) ⟨1558932, by rfl⟩ : syracuseStep 4157153 = 3117865) B3117865
theorem B2771435 : Blo 2189435 2771435 := bstep (se 1 (by rfl) ⟨2078576, by rfl⟩ : syracuseStep 2771435 = 4157153) B4157153
theorem B7390493 : Blo 2189435 7390493 := bstep (se 3 (by rfl) ⟨1385717, by rfl⟩ : syracuseStep 7390493 = 2771435) B2771435
theorem B4926995 : Blo 2189435 4926995 := bstep (se 1 (by rfl) ⟨3695246, by rfl⟩ : syracuseStep 4926995 = 7390493) B7390493
theorem B3284663 : Blo 2189435 3284663 := bstep (se 1 (by rfl) ⟨2463497, by rfl⟩ : syracuseStep 3284663 = 4926995) B4926995
theorem B2189775 : Blo 2189435 2189775 := bstep (se 1 (by rfl) ⟨1642331, by rfl⟩ : syracuseStep 2189775 = 3284663) B3284663
theorem B3284669 : Blo 2189435 3284669 := bbase (se 3 (by rfl) ⟨615875, by rfl⟩ : syracuseStep 3284669 = 1231751) (by norm_num)
theorem B2189779 : Blo 2189435 2189779 := bstep (se 1 (by rfl) ⟨1642334, by rfl⟩ : syracuseStep 2189779 = 3284669) B3284669
theorem B4927013 : Blo 2189435 4927013 := bbase (se 4 (by rfl) ⟨461907, by rfl⟩ : syracuseStep 4927013 = 923815) (by norm_num)
theorem B3284675 : Blo 2189435 3284675 := bstep (se 1 (by rfl) ⟨2463506, by rfl⟩ : syracuseStep 3284675 = 4927013) B4927013
theorem B2189783 : Blo 2189435 2189783 := bstep (se 1 (by rfl) ⟨1642337, by rfl⟩ : syracuseStep 2189783 = 3284675) B3284675
theorem B5542901 : Blo 2189435 5542901 := bbase (se 5 (by rfl) ⟨259823, by rfl⟩ : syracuseStep 5542901 = 519647) (by norm_num)
theorem B3695267 : Blo 2189435 3695267 := bstep (se 1 (by rfl) ⟨2771450, by rfl⟩ : syracuseStep 3695267 = 5542901) B5542901
theorem B2463511 : Blo 2189435 2463511 := bstep (se 1 (by rfl) ⟨1847633, by rfl⟩ : syracuseStep 2463511 = 3695267) B3695267
theorem B3284681 : Blo 2189435 3284681 := bstep (se 2 (by rfl) ⟨1231755, by rfl⟩ : syracuseStep 3284681 = 2463511) B2463511
theorem B2189787 : Blo 2189435 2189787 := bstep (se 1 (by rfl) ⟨1642340, by rfl⟩ : syracuseStep 2189787 = 3284681) B3284681
theorem B7593589 : Blo 2189435 7593589 := bbase (se 5 (by rfl) ⟨355949, by rfl⟩ : syracuseStep 7593589 = 711899) (by norm_num)
theorem B10124785 : Blo 2189435 10124785 := bstep (se 2 (by rfl) ⟨3796794, by rfl⟩ : syracuseStep 10124785 = 7593589) B7593589
theorem B13499713 : Blo 2189435 13499713 := bstep (se 2 (by rfl) ⟨5062392, by rfl⟩ : syracuseStep 13499713 = 10124785) B10124785
theorem B17999617 : Blo 2189435 17999617 := bstep (se 2 (by rfl) ⟨6749856, by rfl⟩ : syracuseStep 17999617 = 13499713) B13499713
theorem B23999489 : Blo 2189435 23999489 := bstep (se 2 (by rfl) ⟨8999808, by rfl⟩ : syracuseStep 23999489 = 17999617) B17999617
theorem B15999659 : Blo 2189435 15999659 := bstep (se 1 (by rfl) ⟨11999744, by rfl⟩ : syracuseStep 15999659 = 23999489) B23999489
theorem B10666439 : Blo 2189435 10666439 := bstep (se 1 (by rfl) ⟨7999829, by rfl⟩ : syracuseStep 10666439 = 15999659) B15999659
theorem B7110959 : Blo 2189435 7110959 := bstep (se 1 (by rfl) ⟨5333219, by rfl⟩ : syracuseStep 7110959 = 10666439) B10666439
theorem B75850229 : Blo 2189435 75850229 := bstep (se 5 (by rfl) ⟨3555479, by rfl⟩ : syracuseStep 75850229 = 7110959) B7110959
theorem B202267277 : Blo 2189435 202267277 := bstep (se 3 (by rfl) ⟨37925114, by rfl⟩ : syracuseStep 202267277 = 75850229) B75850229
theorem B134844851 : Blo 2189435 134844851 := bstep (se 1 (by rfl) ⟨101133638, by rfl⟩ : syracuseStep 134844851 = 202267277) B202267277
theorem B89896567 : Blo 2189435 89896567 := bstep (se 1 (by rfl) ⟨67422425, by rfl⟩ : syracuseStep 89896567 = 134844851) B134844851
theorem B119862089 : Blo 2189435 119862089 := bstep (se 2 (by rfl) ⟨44948283, by rfl⟩ : syracuseStep 119862089 = 89896567) B89896567
theorem B79908059 : Blo 2189435 79908059 := bstep (se 1 (by rfl) ⟨59931044, by rfl⟩ : syracuseStep 79908059 = 119862089) B119862089
theorem B53272039 : Blo 2189435 53272039 := bstep (se 1 (by rfl) ⟨39954029, by rfl⟩ : syracuseStep 53272039 = 79908059) B79908059
theorem B71029385 : Blo 2189435 71029385 := bstep (se 2 (by rfl) ⟨26636019, by rfl⟩ : syracuseStep 71029385 = 53272039) B53272039
theorem B47352923 : Blo 2189435 47352923 := bstep (se 1 (by rfl) ⟨35514692, by rfl⟩ : syracuseStep 47352923 = 71029385) B71029385
theorem B31568615 : Blo 2189435 31568615 := bstep (se 1 (by rfl) ⟨23676461, by rfl⟩ : syracuseStep 31568615 = 47352923) B47352923
theorem B21045743 : Blo 2189435 21045743 := bstep (se 1 (by rfl) ⟨15784307, by rfl⟩ : syracuseStep 21045743 = 31568615) B31568615
theorem B14030495 : Blo 2189435 14030495 := bstep (se 1 (by rfl) ⟨10522871, by rfl⟩ : syracuseStep 14030495 = 21045743) B21045743
theorem B9353663 : Blo 2189435 9353663 := bstep (se 1 (by rfl) ⟨7015247, by rfl⟩ : syracuseStep 9353663 = 14030495) B14030495
theorem B6235775 : Blo 2189435 6235775 := bstep (se 1 (by rfl) ⟨4676831, by rfl⟩ : syracuseStep 6235775 = 9353663) B9353663
theorem B4157183 : Blo 2189435 4157183 := bstep (se 1 (by rfl) ⟨3117887, by rfl⟩ : syracuseStep 4157183 = 6235775) B6235775
theorem B11085821 : Blo 2189435 11085821 := bstep (se 3 (by rfl) ⟨2078591, by rfl⟩ : syracuseStep 11085821 = 4157183) B4157183
theorem B7390547 : Blo 2189435 7390547 := bstep (se 1 (by rfl) ⟨5542910, by rfl⟩ : syracuseStep 7390547 = 11085821) B11085821
theorem B4927031 : Blo 2189435 4927031 := bstep (se 1 (by rfl) ⟨3695273, by rfl⟩ : syracuseStep 4927031 = 7390547) B7390547
theorem B3284687 : Blo 2189435 3284687 := bstep (se 1 (by rfl) ⟨2463515, by rfl⟩ : syracuseStep 3284687 = 4927031) B4927031
theorem B2189791 : Blo 2189435 2189791 := bstep (se 1 (by rfl) ⟨1642343, by rfl⟩ : syracuseStep 2189791 = 3284687) B3284687
theorem B3284693 : Blo 2189435 3284693 := bbase (se 7 (by rfl) ⟨38492, by rfl⟩ : syracuseStep 3284693 = 76985) (by norm_num)
theorem B2189795 : Blo 2189435 2189795 := bstep (se 1 (by rfl) ⟨1642346, by rfl⟩ : syracuseStep 2189795 = 3284693) B3284693
theorem B3507637 : Blo 2189435 3507637 := bbase (se 5 (by rfl) ⟨164420, by rfl⟩ : syracuseStep 3507637 = 328841) (by norm_num)
theorem B4676849 : Blo 2189435 4676849 := bstep (se 2 (by rfl) ⟨1753818, by rfl⟩ : syracuseStep 4676849 = 3507637) B3507637
theorem B3117899 : Blo 2189435 3117899 := bstep (se 1 (by rfl) ⟨2338424, by rfl⟩ : syracuseStep 3117899 = 4676849) B4676849
theorem B8314397 : Blo 2189435 8314397 := bstep (se 3 (by rfl) ⟨1558949, by rfl⟩ : syracuseStep 8314397 = 3117899) B3117899
theorem B5542931 : Blo 2189435 5542931 := bstep (se 1 (by rfl) ⟨4157198, by rfl⟩ : syracuseStep 5542931 = 8314397) B8314397
theorem B3695287 : Blo 2189435 3695287 := bstep (se 1 (by rfl) ⟨2771465, by rfl⟩ : syracuseStep 3695287 = 5542931) B5542931
theorem B4927049 : Blo 2189435 4927049 := bstep (se 2 (by rfl) ⟨1847643, by rfl⟩ : syracuseStep 4927049 = 3695287) B3695287
theorem B3284699 : Blo 2189435 3284699 := bstep (se 1 (by rfl) ⟨2463524, by rfl⟩ : syracuseStep 3284699 = 4927049) B4927049
theorem B2189799 : Blo 2189435 2189799 := bstep (se 1 (by rfl) ⟨1642349, by rfl⟩ : syracuseStep 2189799 = 3284699) B3284699
theorem B2463529 : Blo 2189435 2463529 := bbase (se 2 (by rfl) ⟨923823, by rfl⟩ : syracuseStep 2463529 = 1847647) (by norm_num)
theorem B3284705 : Blo 2189435 3284705 := bstep (se 2 (by rfl) ⟨1231764, by rfl⟩ : syracuseStep 3284705 = 2463529) B2463529
theorem B2189803 : Blo 2189435 2189803 := bstep (se 1 (by rfl) ⟨1642352, by rfl⟩ : syracuseStep 2189803 = 3284705) B3284705
theorem B2630737 : Blo 2189435 2630737 := bbase (se 2 (by rfl) ⟨986526, by rfl⟩ : syracuseStep 2630737 = 1973053) (by norm_num)
theorem B14030597 : Blo 2189435 14030597 := bstep (se 4 (by rfl) ⟨1315368, by rfl⟩ : syracuseStep 14030597 = 2630737) B2630737
theorem B9353731 : Blo 2189435 9353731 := bstep (se 1 (by rfl) ⟨7015298, by rfl⟩ : syracuseStep 9353731 = 14030597) B14030597
theorem B12471641 : Blo 2189435 12471641 := bstep (se 2 (by rfl) ⟨4676865, by rfl⟩ : syracuseStep 12471641 = 9353731) B9353731
theorem B8314427 : Blo 2189435 8314427 := bstep (se 1 (by rfl) ⟨6235820, by rfl⟩ : syracuseStep 8314427 = 12471641) B12471641
theorem B5542951 : Blo 2189435 5542951 := bstep (se 1 (by rfl) ⟨4157213, by rfl⟩ : syracuseStep 5542951 = 8314427) B8314427
theorem B7390601 : Blo 2189435 7390601 := bstep (se 2 (by rfl) ⟨2771475, by rfl⟩ : syracuseStep 7390601 = 5542951) B5542951
theorem B4927067 : Blo 2189435 4927067 := bstep (se 1 (by rfl) ⟨3695300, by rfl⟩ : syracuseStep 4927067 = 7390601) B7390601
theorem B3284711 : Blo 2189435 3284711 := bstep (se 1 (by rfl) ⟨2463533, by rfl⟩ : syracuseStep 3284711 = 4927067) B4927067
theorem B2189807 : Blo 2189435 2189807 := bstep (se 1 (by rfl) ⟨1642355, by rfl⟩ : syracuseStep 2189807 = 3284711) B3284711
theorem B3284717 : Blo 2189435 3284717 := bbase (se 3 (by rfl) ⟨615884, by rfl⟩ : syracuseStep 3284717 = 1231769) (by norm_num)
theorem B2189811 : Blo 2189435 2189811 := bstep (se 1 (by rfl) ⟨1642358, by rfl⟩ : syracuseStep 2189811 = 3284717) B3284717
theorem B4927085 : Blo 2189435 4927085 := bbase (se 3 (by rfl) ⟨923828, by rfl⟩ : syracuseStep 4927085 = 1847657) (by norm_num)
theorem B3284723 : Blo 2189435 3284723 := bstep (se 1 (by rfl) ⟨2463542, by rfl⟩ : syracuseStep 3284723 = 4927085) B4927085
theorem B2189815 : Blo 2189435 2189815 := bstep (se 1 (by rfl) ⟨1642361, by rfl⟩ : syracuseStep 2189815 = 3284723) B3284723
theorem B4157237 : Blo 2189435 4157237 := bbase (se 5 (by rfl) ⟨194870, by rfl⟩ : syracuseStep 4157237 = 389741) (by norm_num)
theorem B2771491 : Blo 2189435 2771491 := bstep (se 1 (by rfl) ⟨2078618, by rfl⟩ : syracuseStep 2771491 = 4157237) B4157237
theorem B3695321 : Blo 2189435 3695321 := bstep (se 2 (by rfl) ⟨1385745, by rfl⟩ : syracuseStep 3695321 = 2771491) B2771491
theorem B2463547 : Blo 2189435 2463547 := bstep (se 1 (by rfl) ⟨1847660, by rfl⟩ : syracuseStep 2463547 = 3695321) B3695321
theorem B3284729 : Blo 2189435 3284729 := bstep (se 2 (by rfl) ⟨1231773, by rfl⟩ : syracuseStep 3284729 = 2463547) B2463547
theorem B2189819 : Blo 2189435 2189819 := bstep (se 1 (by rfl) ⟨1642364, by rfl⟩ : syracuseStep 2189819 = 3284729) B3284729
theorem B8427925 : Blo 2189435 8427925 := bbase (se 6 (by rfl) ⟨197529, by rfl⟩ : syracuseStep 8427925 = 395059) (by norm_num)
theorem B44948933 : Blo 2189435 44948933 := bstep (se 4 (by rfl) ⟨4213962, by rfl⟩ : syracuseStep 44948933 = 8427925) B8427925
theorem B29965955 : Blo 2189435 29965955 := bstep (se 1 (by rfl) ⟨22474466, by rfl⟩ : syracuseStep 29965955 = 44948933) B44948933
theorem B319636853 : Blo 2189435 319636853 := bstep (se 5 (by rfl) ⟨14982977, by rfl⟩ : syracuseStep 319636853 = 29965955) B29965955
theorem B213091235 : Blo 2189435 213091235 := bstep (se 1 (by rfl) ⟨159818426, by rfl⟩ : syracuseStep 213091235 = 319636853) B319636853
theorem B142060823 : Blo 2189435 142060823 := bstep (se 1 (by rfl) ⟨106545617, by rfl⟩ : syracuseStep 142060823 = 213091235) B213091235
theorem B94707215 : Blo 2189435 94707215 := bstep (se 1 (by rfl) ⟨71030411, by rfl⟩ : syracuseStep 94707215 = 142060823) B142060823
theorem B63138143 : Blo 2189435 63138143 := bstep (se 1 (by rfl) ⟨47353607, by rfl⟩ : syracuseStep 63138143 = 94707215) B94707215
theorem B42092095 : Blo 2189435 42092095 := bstep (se 1 (by rfl) ⟨31569071, by rfl⟩ : syracuseStep 42092095 = 63138143) B63138143
theorem B56122793 : Blo 2189435 56122793 := bstep (se 2 (by rfl) ⟨21046047, by rfl⟩ : syracuseStep 56122793 = 42092095) B42092095
theorem B37415195 : Blo 2189435 37415195 := bstep (se 1 (by rfl) ⟨28061396, by rfl⟩ : syracuseStep 37415195 = 56122793) B56122793
theorem B24943463 : Blo 2189435 24943463 := bstep (se 1 (by rfl) ⟨18707597, by rfl⟩ : syracuseStep 24943463 = 37415195) B37415195
theorem B16628975 : Blo 2189435 16628975 := bstep (se 1 (by rfl) ⟨12471731, by rfl⟩ : syracuseStep 16628975 = 24943463) B24943463
theorem B11085983 : Blo 2189435 11085983 := bstep (se 1 (by rfl) ⟨8314487, by rfl⟩ : syracuseStep 11085983 = 16628975) B16628975
theorem B7390655 : Blo 2189435 7390655 := bstep (se 1 (by rfl) ⟨5542991, by rfl⟩ : syracuseStep 7390655 = 11085983) B11085983
theorem B4927103 : Blo 2189435 4927103 := bstep (se 1 (by rfl) ⟨3695327, by rfl⟩ : syracuseStep 4927103 = 7390655) B7390655
theorem B3284735 : Blo 2189435 3284735 := bstep (se 1 (by rfl) ⟨2463551, by rfl⟩ : syracuseStep 3284735 = 4927103) B4927103
theorem B2189823 : Blo 2189435 2189823 := bstep (se 1 (by rfl) ⟨1642367, by rfl⟩ : syracuseStep 2189823 = 3284735) B3284735
theorem B3284741 : Blo 2189435 3284741 := bbase (se 4 (by rfl) ⟨307944, by rfl⟩ : syracuseStep 3284741 = 615889) (by norm_num)
theorem B2189827 : Blo 2189435 2189827 := bstep (se 1 (by rfl) ⟨1642370, by rfl⟩ : syracuseStep 2189827 = 3284741) B3284741
theorem B3695341 : Blo 2189435 3695341 := bbase (se 3 (by rfl) ⟨692876, by rfl⟩ : syracuseStep 3695341 = 1385753) (by norm_num)
theorem B4927121 : Blo 2189435 4927121 := bstep (se 2 (by rfl) ⟨1847670, by rfl⟩ : syracuseStep 4927121 = 3695341) B3695341
theorem B3284747 : Blo 2189435 3284747 := bstep (se 1 (by rfl) ⟨2463560, by rfl⟩ : syracuseStep 3284747 = 4927121) B4927121
theorem B2189831 : Blo 2189435 2189831 := bstep (se 1 (by rfl) ⟨1642373, by rfl⟩ : syracuseStep 2189831 = 3284747) B3284747
theorem B2463565 : Blo 2189435 2463565 := bbase (se 3 (by rfl) ⟨461918, by rfl⟩ : syracuseStep 2463565 = 923837) (by norm_num)
theorem B3284753 : Blo 2189435 3284753 := bstep (se 2 (by rfl) ⟨1231782, by rfl⟩ : syracuseStep 3284753 = 2463565) B2463565
theorem B2189835 : Blo 2189435 2189835 := bstep (se 1 (by rfl) ⟨1642376, by rfl⟩ : syracuseStep 2189835 = 3284753) B3284753
theorem B7390709 : Blo 2189435 7390709 := bbase (se 5 (by rfl) ⟨346439, by rfl⟩ : syracuseStep 7390709 = 692879) (by norm_num)
theorem B4927139 : Blo 2189435 4927139 := bstep (se 1 (by rfl) ⟨3695354, by rfl⟩ : syracuseStep 4927139 = 7390709) B7390709
theorem B3284759 : Blo 2189435 3284759 := bstep (se 1 (by rfl) ⟨2463569, by rfl⟩ : syracuseStep 3284759 = 4927139) B4927139
theorem B2189839 : Blo 2189435 2189839 := bstep (se 1 (by rfl) ⟨1642379, by rfl⟩ : syracuseStep 2189839 = 3284759) B3284759
theorem B3284765 : Blo 2189435 3284765 := bbase (se 3 (by rfl) ⟨615893, by rfl⟩ : syracuseStep 3284765 = 1231787) (by norm_num)
theorem B2189843 : Blo 2189435 2189843 := bstep (se 1 (by rfl) ⟨1642382, by rfl⟩ : syracuseStep 2189843 = 3284765) B3284765
theorem B4927157 : Blo 2189435 4927157 := bbase (se 5 (by rfl) ⟨230960, by rfl⟩ : syracuseStep 4927157 = 461921) (by norm_num)
theorem B3284771 : Blo 2189435 3284771 := bstep (se 1 (by rfl) ⟨2463578, by rfl⟩ : syracuseStep 3284771 = 4927157) B4927157
theorem B2189847 : Blo 2189435 2189847 := bstep (se 1 (by rfl) ⟨1642385, by rfl⟩ : syracuseStep 2189847 = 3284771) B3284771
theorem B12471893 : Blo 2189435 12471893 := bbase (se 8 (by rfl) ⟨73077, by rfl⟩ : syracuseStep 12471893 = 146155) (by norm_num)
theorem B8314595 : Blo 2189435 8314595 := bstep (se 1 (by rfl) ⟨6235946, by rfl⟩ : syracuseStep 8314595 = 12471893) B12471893
theorem B5543063 : Blo 2189435 5543063 := bstep (se 1 (by rfl) ⟨4157297, by rfl⟩ : syracuseStep 5543063 = 8314595) B8314595
theorem B3695375 : Blo 2189435 3695375 := bstep (se 1 (by rfl) ⟨2771531, by rfl⟩ : syracuseStep 3695375 = 5543063) B5543063
theorem B2463583 : Blo 2189435 2463583 := bstep (se 1 (by rfl) ⟨1847687, by rfl⟩ : syracuseStep 2463583 = 3695375) B3695375
theorem B3284777 : Blo 2189435 3284777 := bstep (se 2 (by rfl) ⟨1231791, by rfl⟩ : syracuseStep 3284777 = 2463583) B2463583
theorem B2189851 : Blo 2189435 2189851 := bstep (se 1 (by rfl) ⟨1642388, by rfl⟩ : syracuseStep 2189851 = 3284777) B3284777
theorem B6235957 : Blo 2189435 6235957 := bbase (se 5 (by rfl) ⟨292310, by rfl⟩ : syracuseStep 6235957 = 584621) (by norm_num)
theorem B8314609 : Blo 2189435 8314609 := bstep (se 2 (by rfl) ⟨3117978, by rfl⟩ : syracuseStep 8314609 = 6235957) B6235957
theorem B11086145 : Blo 2189435 11086145 := bstep (se 2 (by rfl) ⟨4157304, by rfl⟩ : syracuseStep 11086145 = 8314609) B8314609
theorem B7390763 : Blo 2189435 7390763 := bstep (se 1 (by rfl) ⟨5543072, by rfl⟩ : syracuseStep 7390763 = 11086145) B11086145
theorem B4927175 : Blo 2189435 4927175 := bstep (se 1 (by rfl) ⟨3695381, by rfl⟩ : syracuseStep 4927175 = 7390763) B7390763
theorem B3284783 : Blo 2189435 3284783 := bstep (se 1 (by rfl) ⟨2463587, by rfl⟩ : syracuseStep 3284783 = 4927175) B4927175
theorem B2189855 : Blo 2189435 2189855 := bstep (se 1 (by rfl) ⟨1642391, by rfl⟩ : syracuseStep 2189855 = 3284783) B3284783
theorem B3284789 : Blo 2189435 3284789 := bbase (se 5 (by rfl) ⟨153974, by rfl⟩ : syracuseStep 3284789 = 307949) (by norm_num)
theorem B2189859 : Blo 2189435 2189859 := bstep (se 1 (by rfl) ⟨1642394, by rfl⟩ : syracuseStep 2189859 = 3284789) B3284789
theorem B5543093 : Blo 2189435 5543093 := bbase (se 5 (by rfl) ⟨259832, by rfl⟩ : syracuseStep 5543093 = 519665) (by norm_num)
theorem B3695395 : Blo 2189435 3695395 := bstep (se 1 (by rfl) ⟨2771546, by rfl⟩ : syracuseStep 3695395 = 5543093) B5543093
theorem B4927193 : Blo 2189435 4927193 := bstep (se 2 (by rfl) ⟨1847697, by rfl⟩ : syracuseStep 4927193 = 3695395) B3695395
theorem B3284795 : Blo 2189435 3284795 := bstep (se 1 (by rfl) ⟨2463596, by rfl⟩ : syracuseStep 3284795 = 4927193) B4927193
theorem B2189863 : Blo 2189435 2189863 := bstep (se 1 (by rfl) ⟨1642397, by rfl⟩ : syracuseStep 2189863 = 3284795) B3284795
theorem B2463601 : Blo 2189435 2463601 := bbase (se 2 (by rfl) ⟨923850, by rfl⟩ : syracuseStep 2463601 = 1847701) (by norm_num)
theorem B3284801 : Blo 2189435 3284801 := bstep (se 2 (by rfl) ⟨1231800, by rfl⟩ : syracuseStep 3284801 = 2463601) B2463601
theorem B2189867 : Blo 2189435 2189867 := bstep (se 1 (by rfl) ⟨1642400, by rfl⟩ : syracuseStep 2189867 = 3284801) B3284801
theorem B9354005 : Blo 2189435 9354005 := bbase (se 6 (by rfl) ⟨219234, by rfl⟩ : syracuseStep 9354005 = 438469) (by norm_num)
theorem B6236003 : Blo 2189435 6236003 := bstep (se 1 (by rfl) ⟨4677002, by rfl⟩ : syracuseStep 6236003 = 9354005) B9354005
theorem B4157335 : Blo 2189435 4157335 := bstep (se 1 (by rfl) ⟨3118001, by rfl⟩ : syracuseStep 4157335 = 6236003) B6236003
theorem B5543113 : Blo 2189435 5543113 := bstep (se 2 (by rfl) ⟨2078667, by rfl⟩ : syracuseStep 5543113 = 4157335) B4157335
theorem B7390817 : Blo 2189435 7390817 := bstep (se 2 (by rfl) ⟨2771556, by rfl⟩ : syracuseStep 7390817 = 5543113) B5543113
theorem B4927211 : Blo 2189435 4927211 := bstep (se 1 (by rfl) ⟨3695408, by rfl⟩ : syracuseStep 4927211 = 7390817) B7390817
theorem B3284807 : Blo 2189435 3284807 := bstep (se 1 (by rfl) ⟨2463605, by rfl⟩ : syracuseStep 3284807 = 4927211) B4927211
theorem B2189871 : Blo 2189435 2189871 := bstep (se 1 (by rfl) ⟨1642403, by rfl⟩ : syracuseStep 2189871 = 3284807) B3284807
theorem B3284813 : Blo 2189435 3284813 := bbase (se 3 (by rfl) ⟨615902, by rfl⟩ : syracuseStep 3284813 = 1231805) (by norm_num)
theorem B2189875 : Blo 2189435 2189875 := bstep (se 1 (by rfl) ⟨1642406, by rfl⟩ : syracuseStep 2189875 = 3284813) B3284813
theorem B4927229 : Blo 2189435 4927229 := bbase (se 3 (by rfl) ⟨923855, by rfl⟩ : syracuseStep 4927229 = 1847711) (by norm_num)
theorem B3284819 : Blo 2189435 3284819 := bstep (se 1 (by rfl) ⟨2463614, by rfl⟩ : syracuseStep 3284819 = 4927229) B4927229
theorem B2189879 : Blo 2189435 2189879 := bstep (se 1 (by rfl) ⟨1642409, by rfl⟩ : syracuseStep 2189879 = 3284819) B3284819
theorem B3695429 : Blo 2189435 3695429 := bbase (se 4 (by rfl) ⟨346446, by rfl⟩ : syracuseStep 3695429 = 692893) (by norm_num)
theorem B2463619 : Blo 2189435 2463619 := bstep (se 1 (by rfl) ⟨1847714, by rfl⟩ : syracuseStep 2463619 = 3695429) B3695429
theorem B3284825 : Blo 2189435 3284825 := bstep (se 2 (by rfl) ⟨1231809, by rfl⟩ : syracuseStep 3284825 = 2463619) B2463619
theorem B2189883 : Blo 2189435 2189883 := bstep (se 1 (by rfl) ⟨1642412, by rfl⟩ : syracuseStep 2189883 = 3284825) B3284825
theorem B16629461 : Blo 2189435 16629461 := bbase (se 7 (by rfl) ⟨194876, by rfl⟩ : syracuseStep 16629461 = 389753) (by norm_num)
theorem B11086307 : Blo 2189435 11086307 := bstep (se 1 (by rfl) ⟨8314730, by rfl⟩ : syracuseStep 11086307 = 16629461) B16629461
theorem B7390871 : Blo 2189435 7390871 := bstep (se 1 (by rfl) ⟨5543153, by rfl⟩ : syracuseStep 7390871 = 11086307) B11086307
theorem B4927247 : Blo 2189435 4927247 := bstep (se 1 (by rfl) ⟨3695435, by rfl⟩ : syracuseStep 4927247 = 7390871) B7390871
theorem B3284831 : Blo 2189435 3284831 := bstep (se 1 (by rfl) ⟨2463623, by rfl⟩ : syracuseStep 3284831 = 4927247) B4927247
theorem B2189887 : Blo 2189435 2189887 := bstep (se 1 (by rfl) ⟨1642415, by rfl⟩ : syracuseStep 2189887 = 3284831) B3284831
theorem B3284837 : Blo 2189435 3284837 := bbase (se 4 (by rfl) ⟨307953, by rfl⟩ : syracuseStep 3284837 = 615907) (by norm_num)
theorem B2189891 : Blo 2189435 2189891 := bstep (se 1 (by rfl) ⟨1642418, by rfl⟩ : syracuseStep 2189891 = 3284837) B3284837
theorem B4157381 : Blo 2189435 4157381 := bbase (se 4 (by rfl) ⟨389754, by rfl⟩ : syracuseStep 4157381 = 779509) (by norm_num)
theorem B2771587 : Blo 2189435 2771587 := bstep (se 1 (by rfl) ⟨2078690, by rfl⟩ : syracuseStep 2771587 = 4157381) B4157381
theorem B3695449 : Blo 2189435 3695449 := bstep (se 2 (by rfl) ⟨1385793, by rfl⟩ : syracuseStep 3695449 = 2771587) B2771587
theorem B4927265 : Blo 2189435 4927265 := bstep (se 2 (by rfl) ⟨1847724, by rfl⟩ : syracuseStep 4927265 = 3695449) B3695449
theorem B3284843 : Blo 2189435 3284843 := bstep (se 1 (by rfl) ⟨2463632, by rfl⟩ : syracuseStep 3284843 = 4927265) B4927265
theorem B2189895 : Blo 2189435 2189895 := bstep (se 1 (by rfl) ⟨1642421, by rfl⟩ : syracuseStep 2189895 = 3284843) B3284843
theorem B2463637 : Blo 2189435 2463637 := bbase (se 6 (by rfl) ⟨57741, by rfl⟩ : syracuseStep 2463637 = 115483) (by norm_num)
theorem B3284849 : Blo 2189435 3284849 := bstep (se 2 (by rfl) ⟨1231818, by rfl⟩ : syracuseStep 3284849 = 2463637) B2463637
theorem B2189899 : Blo 2189435 2189899 := bstep (se 1 (by rfl) ⟨1642424, by rfl⟩ : syracuseStep 2189899 = 3284849) B3284849
theorem B2771597 : Blo 2189435 2771597 := bbase (se 3 (by rfl) ⟨519674, by rfl⟩ : syracuseStep 2771597 = 1039349) (by norm_num)
theorem B7390925 : Blo 2189435 7390925 := bstep (se 3 (by rfl) ⟨1385798, by rfl⟩ : syracuseStep 7390925 = 2771597) B2771597
theorem B4927283 : Blo 2189435 4927283 := bstep (se 1 (by rfl) ⟨3695462, by rfl⟩ : syracuseStep 4927283 = 7390925) B7390925
theorem B3284855 : Blo 2189435 3284855 := bstep (se 1 (by rfl) ⟨2463641, by rfl⟩ : syracuseStep 3284855 = 4927283) B4927283
theorem B2189903 : Blo 2189435 2189903 := bstep (se 1 (by rfl) ⟨1642427, by rfl⟩ : syracuseStep 2189903 = 3284855) B3284855
theorem B3284861 : Blo 2189435 3284861 := bbase (se 3 (by rfl) ⟨615911, by rfl⟩ : syracuseStep 3284861 = 1231823) (by norm_num)
theorem B2189907 : Blo 2189435 2189907 := bstep (se 1 (by rfl) ⟨1642430, by rfl⟩ : syracuseStep 2189907 = 3284861) B3284861
theorem B4927301 : Blo 2189435 4927301 := bbase (se 4 (by rfl) ⟨461934, by rfl⟩ : syracuseStep 4927301 = 923869) (by norm_num)
theorem B3284867 : Blo 2189435 3284867 := bstep (se 1 (by rfl) ⟨2463650, by rfl⟩ : syracuseStep 3284867 = 4927301) B4927301
theorem B2189911 : Blo 2189435 2189911 := bstep (se 1 (by rfl) ⟨1642433, by rfl⟩ : syracuseStep 2189911 = 3284867) B3284867
theorem B9989077 : Blo 2189435 9989077 := bbase (se 7 (by rfl) ⟨117059, by rfl⟩ : syracuseStep 9989077 = 234119) (by norm_num)
theorem B13318769 : Blo 2189435 13318769 := bstep (se 2 (by rfl) ⟨4994538, by rfl⟩ : syracuseStep 13318769 = 9989077) B9989077
theorem B8879179 : Blo 2189435 8879179 := bstep (se 1 (by rfl) ⟨6659384, by rfl⟩ : syracuseStep 8879179 = 13318769) B13318769
theorem B11838905 : Blo 2189435 11838905 := bstep (se 2 (by rfl) ⟨4439589, by rfl⟩ : syracuseStep 11838905 = 8879179) B8879179
theorem B7892603 : Blo 2189435 7892603 := bstep (se 1 (by rfl) ⟨5919452, by rfl⟩ : syracuseStep 7892603 = 11838905) B11838905
theorem B5261735 : Blo 2189435 5261735 := bstep (se 1 (by rfl) ⟨3946301, by rfl⟩ : syracuseStep 5261735 = 7892603) B7892603
theorem B3507823 : Blo 2189435 3507823 := bstep (se 1 (by rfl) ⟨2630867, by rfl⟩ : syracuseStep 3507823 = 5261735) B5261735
theorem B4677097 : Blo 2189435 4677097 := bstep (se 2 (by rfl) ⟨1753911, by rfl⟩ : syracuseStep 4677097 = 3507823) B3507823
theorem B6236129 : Blo 2189435 6236129 := bstep (se 2 (by rfl) ⟨2338548, by rfl⟩ : syracuseStep 6236129 = 4677097) B4677097
theorem B4157419 : Blo 2189435 4157419 := bstep (se 1 (by rfl) ⟨3118064, by rfl⟩ : syracuseStep 4157419 = 6236129) B6236129
theorem B5543225 : Blo 2189435 5543225 := bstep (se 2 (by rfl) ⟨2078709, by rfl⟩ : syracuseStep 5543225 = 4157419) B4157419
theorem B3695483 : Blo 2189435 3695483 := bstep (se 1 (by rfl) ⟨2771612, by rfl⟩ : syracuseStep 3695483 = 5543225) B5543225
theorem B2463655 : Blo 2189435 2463655 := bstep (se 1 (by rfl) ⟨1847741, by rfl⟩ : syracuseStep 2463655 = 3695483) B3695483
theorem B3284873 : Blo 2189435 3284873 := bstep (se 2 (by rfl) ⟨1231827, by rfl⟩ : syracuseStep 3284873 = 2463655) B2463655
theorem B2189915 : Blo 2189435 2189915 := bstep (se 1 (by rfl) ⟨1642436, by rfl⟩ : syracuseStep 2189915 = 3284873) B3284873
theorem B11086469 : Blo 2189435 11086469 := bbase (se 4 (by rfl) ⟨1039356, by rfl⟩ : syracuseStep 11086469 = 2078713) (by norm_num)
theorem B7390979 : Blo 2189435 7390979 := bstep (se 1 (by rfl) ⟨5543234, by rfl⟩ : syracuseStep 7390979 = 11086469) B11086469
theorem B4927319 : Blo 2189435 4927319 := bstep (se 1 (by rfl) ⟨3695489, by rfl⟩ : syracuseStep 4927319 = 7390979) B7390979
theorem B3284879 : Blo 2189435 3284879 := bstep (se 1 (by rfl) ⟨2463659, by rfl⟩ : syracuseStep 3284879 = 4927319) B4927319
theorem B2189919 : Blo 2189435 2189919 := bstep (se 1 (by rfl) ⟨1642439, by rfl⟩ : syracuseStep 2189919 = 3284879) B3284879
theorem B3284885 : Blo 2189435 3284885 := bbase (se 6 (by rfl) ⟨76989, by rfl⟩ : syracuseStep 3284885 = 153979) (by norm_num)
theorem B2189923 : Blo 2189435 2189923 := bstep (se 1 (by rfl) ⟨1642442, by rfl⟩ : syracuseStep 2189923 = 3284885) B3284885
theorem B2338561 : Blo 2189435 2338561 := bbase (se 2 (by rfl) ⟨876960, by rfl⟩ : syracuseStep 2338561 = 1753921) (by norm_num)
theorem B12472325 : Blo 2189435 12472325 := bstep (se 4 (by rfl) ⟨1169280, by rfl⟩ : syracuseStep 12472325 = 2338561) B2338561
theorem B8314883 : Blo 2189435 8314883 := bstep (se 1 (by rfl) ⟨6236162, by rfl⟩ : syracuseStep 8314883 = 12472325) B12472325
theorem B5543255 : Blo 2189435 5543255 := bstep (se 1 (by rfl) ⟨4157441, by rfl⟩ : syracuseStep 5543255 = 8314883) B8314883
theorem B3695503 : Blo 2189435 3695503 := bstep (se 1 (by rfl) ⟨2771627, by rfl⟩ : syracuseStep 3695503 = 5543255) B5543255
theorem B4927337 : Blo 2189435 4927337 := bstep (se 2 (by rfl) ⟨1847751, by rfl⟩ : syracuseStep 4927337 = 3695503) B3695503
theorem B3284891 : Blo 2189435 3284891 := bstep (se 1 (by rfl) ⟨2463668, by rfl⟩ : syracuseStep 3284891 = 4927337) B4927337
theorem B2189927 : Blo 2189435 2189927 := bstep (se 1 (by rfl) ⟨1642445, by rfl⟩ : syracuseStep 2189927 = 3284891) B3284891
theorem B2463673 : Blo 2189435 2463673 := bbase (se 2 (by rfl) ⟨923877, by rfl⟩ : syracuseStep 2463673 = 1847755) (by norm_num)
theorem B3284897 : Blo 2189435 3284897 := bstep (se 2 (by rfl) ⟨1231836, by rfl⟩ : syracuseStep 3284897 = 2463673) B2463673
theorem B2189931 : Blo 2189435 2189931 := bstep (se 1 (by rfl) ⟨1642448, by rfl⟩ : syracuseStep 2189931 = 3284897) B3284897
theorem B5618909 : Blo 2189435 5618909 := bbase (se 3 (by rfl) ⟨1053545, by rfl⟩ : syracuseStep 5618909 = 2107091) (by norm_num)
theorem B3745939 : Blo 2189435 3745939 := bstep (se 1 (by rfl) ⟨2809454, by rfl⟩ : syracuseStep 3745939 = 5618909) B5618909
theorem B4994585 : Blo 2189435 4994585 := bstep (se 2 (by rfl) ⟨1872969, by rfl⟩ : syracuseStep 4994585 = 3745939) B3745939
theorem B3329723 : Blo 2189435 3329723 := bstep (se 1 (by rfl) ⟨2497292, by rfl⟩ : syracuseStep 3329723 = 4994585) B4994585
theorem B2219815 : Blo 2189435 2219815 := bstep (se 1 (by rfl) ⟨1664861, by rfl⟩ : syracuseStep 2219815 = 3329723) B3329723
theorem B2959753 : Blo 2189435 2959753 := bstep (se 2 (by rfl) ⟨1109907, by rfl⟩ : syracuseStep 2959753 = 2219815) B2219815
theorem B3946337 : Blo 2189435 3946337 := bstep (se 2 (by rfl) ⟨1479876, by rfl⟩ : syracuseStep 3946337 = 2959753) B2959753
theorem B2630891 : Blo 2189435 2630891 := bstep (se 1 (by rfl) ⟨1973168, by rfl⟩ : syracuseStep 2630891 = 3946337) B3946337
theorem B7015709 : Blo 2189435 7015709 := bstep (se 3 (by rfl) ⟨1315445, by rfl⟩ : syracuseStep 7015709 = 2630891) B2630891
theorem B4677139 : Blo 2189435 4677139 := bstep (se 1 (by rfl) ⟨3507854, by rfl⟩ : syracuseStep 4677139 = 7015709) B7015709
theorem B6236185 : Blo 2189435 6236185 := bstep (se 2 (by rfl) ⟨2338569, by rfl⟩ : syracuseStep 6236185 = 4677139) B4677139
theorem B8314913 : Blo 2189435 8314913 := bstep (se 2 (by rfl) ⟨3118092, by rfl⟩ : syracuseStep 8314913 = 6236185) B6236185
theorem B5543275 : Blo 2189435 5543275 := bstep (se 1 (by rfl) ⟨4157456, by rfl⟩ : syracuseStep 5543275 = 8314913) B8314913
theorem B7391033 : Blo 2189435 7391033 := bstep (se 2 (by rfl) ⟨2771637, by rfl⟩ : syracuseStep 7391033 = 5543275) B5543275
theorem B4927355 : Blo 2189435 4927355 := bstep (se 1 (by rfl) ⟨3695516, by rfl⟩ : syracuseStep 4927355 = 7391033) B7391033
theorem B3284903 : Blo 2189435 3284903 := bstep (se 1 (by rfl) ⟨2463677, by rfl⟩ : syracuseStep 3284903 = 4927355) B4927355
theorem B2189935 : Blo 2189435 2189935 := bstep (se 1 (by rfl) ⟨1642451, by rfl⟩ : syracuseStep 2189935 = 3284903) B3284903
theorem B3284909 : Blo 2189435 3284909 := bbase (se 3 (by rfl) ⟨615920, by rfl⟩ : syracuseStep 3284909 = 1231841) (by norm_num)
theorem B2189939 : Blo 2189435 2189939 := bstep (se 1 (by rfl) ⟨1642454, by rfl⟩ : syracuseStep 2189939 = 3284909) B3284909
theorem B4927373 : Blo 2189435 4927373 := bbase (se 3 (by rfl) ⟨923882, by rfl⟩ : syracuseStep 4927373 = 1847765) (by norm_num)
theorem B3284915 : Blo 2189435 3284915 := bstep (se 1 (by rfl) ⟨2463686, by rfl⟩ : syracuseStep 3284915 = 4927373) B4927373
theorem B2189943 : Blo 2189435 2189943 := bstep (se 1 (by rfl) ⟨1642457, by rfl⟩ : syracuseStep 2189943 = 3284915) B3284915
theorem B2771653 : Blo 2189435 2771653 := bbase (se 4 (by rfl) ⟨259842, by rfl⟩ : syracuseStep 2771653 = 519685) (by norm_num)
theorem B3695537 : Blo 2189435 3695537 := bstep (se 2 (by rfl) ⟨1385826, by rfl⟩ : syracuseStep 3695537 = 2771653) B2771653
theorem B2463691 : Blo 2189435 2463691 := bstep (se 1 (by rfl) ⟨1847768, by rfl⟩ : syracuseStep 2463691 = 3695537) B3695537
theorem B3284921 : Blo 2189435 3284921 := bstep (se 2 (by rfl) ⟨1231845, by rfl⟩ : syracuseStep 3284921 = 2463691) B2463691
theorem B2189947 : Blo 2189435 2189947 := bstep (se 1 (by rfl) ⟨1642460, by rfl⟩ : syracuseStep 2189947 = 3284921) B3284921
theorem B9989237 : Blo 2189435 9989237 := bbase (se 5 (by rfl) ⟨468245, by rfl⟩ : syracuseStep 9989237 = 936491) (by norm_num)
theorem B6659491 : Blo 2189435 6659491 := bstep (se 1 (by rfl) ⟨4994618, by rfl⟩ : syracuseStep 6659491 = 9989237) B9989237
theorem B8879321 : Blo 2189435 8879321 := bstep (se 2 (by rfl) ⟨3329745, by rfl⟩ : syracuseStep 8879321 = 6659491) B6659491
theorem B23678189 : Blo 2189435 23678189 := bstep (se 3 (by rfl) ⟨4439660, by rfl⟩ : syracuseStep 23678189 = 8879321) B8879321
theorem B15785459 : Blo 2189435 15785459 := bstep (se 1 (by rfl) ⟨11839094, by rfl⟩ : syracuseStep 15785459 = 23678189) B23678189
theorem B10523639 : Blo 2189435 10523639 := bstep (se 1 (by rfl) ⟨7892729, by rfl⟩ : syracuseStep 10523639 = 15785459) B15785459
theorem B28063037 : Blo 2189435 28063037 := bstep (se 3 (by rfl) ⟨5261819, by rfl⟩ : syracuseStep 28063037 = 10523639) B10523639
theorem B18708691 : Blo 2189435 18708691 := bstep (se 1 (by rfl) ⟨14031518, by rfl⟩ : syracuseStep 18708691 = 28063037) B28063037
theorem B24944921 : Blo 2189435 24944921 := bstep (se 2 (by rfl) ⟨9354345, by rfl⟩ : syracuseStep 24944921 = 18708691) B18708691
theorem B16629947 : Blo 2189435 16629947 := bstep (se 1 (by rfl) ⟨12472460, by rfl⟩ : syracuseStep 16629947 = 24944921) B24944921
theorem B11086631 : Blo 2189435 11086631 := bstep (se 1 (by rfl) ⟨8314973, by rfl⟩ : syracuseStep 11086631 = 16629947) B16629947
theorem B7391087 : Blo 2189435 7391087 := bstep (se 1 (by rfl) ⟨5543315, by rfl⟩ : syracuseStep 7391087 = 11086631) B11086631
theorem B4927391 : Blo 2189435 4927391 := bstep (se 1 (by rfl) ⟨3695543, by rfl⟩ : syracuseStep 4927391 = 7391087) B7391087
theorem B3284927 : Blo 2189435 3284927 := bstep (se 1 (by rfl) ⟨2463695, by rfl⟩ : syracuseStep 3284927 = 4927391) B4927391
theorem B2189951 : Blo 2189435 2189951 := bstep (se 1 (by rfl) ⟨1642463, by rfl⟩ : syracuseStep 2189951 = 3284927) B3284927
theorem B3284933 : Blo 2189435 3284933 := bbase (se 4 (by rfl) ⟨307962, by rfl⟩ : syracuseStep 3284933 = 615925) (by norm_num)
theorem B2189955 : Blo 2189435 2189955 := bstep (se 1 (by rfl) ⟨1642466, by rfl⟩ : syracuseStep 2189955 = 3284933) B3284933
theorem B3695557 : Blo 2189435 3695557 := bbase (se 4 (by rfl) ⟨346458, by rfl⟩ : syracuseStep 3695557 = 692917) (by norm_num)
theorem B4927409 : Blo 2189435 4927409 := bstep (se 2 (by rfl) ⟨1847778, by rfl⟩ : syracuseStep 4927409 = 3695557) B3695557
theorem B3284939 : Blo 2189435 3284939 := bstep (se 1 (by rfl) ⟨2463704, by rfl⟩ : syracuseStep 3284939 = 4927409) B4927409
theorem B2189959 : Blo 2189435 2189959 := bstep (se 1 (by rfl) ⟨1642469, by rfl⟩ : syracuseStep 2189959 = 3284939) B3284939
theorem B2463709 : Blo 2189435 2463709 := bbase (se 3 (by rfl) ⟨461945, by rfl⟩ : syracuseStep 2463709 = 923891) (by norm_num)
theorem B3284945 : Blo 2189435 3284945 := bstep (se 2 (by rfl) ⟨1231854, by rfl⟩ : syracuseStep 3284945 = 2463709) B2463709
theorem B2189963 : Blo 2189435 2189963 := bstep (se 1 (by rfl) ⟨1642472, by rfl⟩ : syracuseStep 2189963 = 3284945) B3284945
theorem B7391141 : Blo 2189435 7391141 := bbase (se 4 (by rfl) ⟨692919, by rfl⟩ : syracuseStep 7391141 = 1385839) (by norm_num)
theorem B4927427 : Blo 2189435 4927427 := bstep (se 1 (by rfl) ⟨3695570, by rfl⟩ : syracuseStep 4927427 = 7391141) B7391141
theorem B3284951 : Blo 2189435 3284951 := bstep (se 1 (by rfl) ⟨2463713, by rfl⟩ : syracuseStep 3284951 = 4927427) B4927427
theorem B2189967 : Blo 2189435 2189967 := bstep (se 1 (by rfl) ⟨1642475, by rfl⟩ : syracuseStep 2189967 = 3284951) B3284951
theorem B3284957 : Blo 2189435 3284957 := bbase (se 3 (by rfl) ⟨615929, by rfl⟩ : syracuseStep 3284957 = 1231859) (by norm_num)
theorem B2189971 : Blo 2189435 2189971 := bstep (se 1 (by rfl) ⟨1642478, by rfl⟩ : syracuseStep 2189971 = 3284957) B3284957
theorem B4927445 : Blo 2189435 4927445 := bbase (se 7 (by rfl) ⟨57743, by rfl⟩ : syracuseStep 4927445 = 115487) (by norm_num)
theorem B3284963 : Blo 2189435 3284963 := bstep (se 1 (by rfl) ⟨2463722, by rfl⟩ : syracuseStep 3284963 = 4927445) B4927445
theorem B2189975 : Blo 2189435 2189975 := bstep (se 1 (by rfl) ⟨1642481, by rfl⟩ : syracuseStep 2189975 = 3284963) B3284963
theorem B14031701 : Blo 2189435 14031701 := bbase (se 9 (by rfl) ⟨41108, by rfl⟩ : syracuseStep 14031701 = 82217) (by norm_num)
theorem B9354467 : Blo 2189435 9354467 := bstep (se 1 (by rfl) ⟨7015850, by rfl⟩ : syracuseStep 9354467 = 14031701) B14031701
theorem B6236311 : Blo 2189435 6236311 := bstep (se 1 (by rfl) ⟨4677233, by rfl⟩ : syracuseStep 6236311 = 9354467) B9354467
theorem B8315081 : Blo 2189435 8315081 := bstep (se 2 (by rfl) ⟨3118155, by rfl⟩ : syracuseStep 8315081 = 6236311) B6236311
theorem B5543387 : Blo 2189435 5543387 := bstep (se 1 (by rfl) ⟨4157540, by rfl⟩ : syracuseStep 5543387 = 8315081) B8315081
theorem B3695591 : Blo 2189435 3695591 := bstep (se 1 (by rfl) ⟨2771693, by rfl⟩ : syracuseStep 3695591 = 5543387) B5543387
theorem B2463727 : Blo 2189435 2463727 := bstep (se 1 (by rfl) ⟨1847795, by rfl⟩ : syracuseStep 2463727 = 3695591) B3695591
theorem B3284969 : Blo 2189435 3284969 := bstep (se 2 (by rfl) ⟨1231863, by rfl⟩ : syracuseStep 3284969 = 2463727) B2463727
theorem B2189979 : Blo 2189435 2189979 := bstep (se 1 (by rfl) ⟨1642484, by rfl⟩ : syracuseStep 2189979 = 3284969) B3284969
theorem B4994693 : Blo 2189435 4994693 := bbase (se 4 (by rfl) ⟨468252, by rfl⟩ : syracuseStep 4994693 = 936505) (by norm_num)
theorem B3329795 : Blo 2189435 3329795 := bstep (se 1 (by rfl) ⟨2497346, by rfl⟩ : syracuseStep 3329795 = 4994693) B4994693
theorem B8879453 : Blo 2189435 8879453 := bstep (se 3 (by rfl) ⟨1664897, by rfl⟩ : syracuseStep 8879453 = 3329795) B3329795
theorem B5919635 : Blo 2189435 5919635 := bstep (se 1 (by rfl) ⟨4439726, by rfl⟩ : syracuseStep 5919635 = 8879453) B8879453
theorem B3946423 : Blo 2189435 3946423 := bstep (se 1 (by rfl) ⟨2959817, by rfl⟩ : syracuseStep 3946423 = 5919635) B5919635
theorem B5261897 : Blo 2189435 5261897 := bstep (se 2 (by rfl) ⟨1973211, by rfl⟩ : syracuseStep 5261897 = 3946423) B3946423
theorem B3507931 : Blo 2189435 3507931 := bstep (se 1 (by rfl) ⟨2630948, by rfl⟩ : syracuseStep 3507931 = 5261897) B5261897
theorem B18708965 : Blo 2189435 18708965 := bstep (se 4 (by rfl) ⟨1753965, by rfl⟩ : syracuseStep 18708965 = 3507931) B3507931
theorem B12472643 : Blo 2189435 12472643 := bstep (se 1 (by rfl) ⟨9354482, by rfl⟩ : syracuseStep 12472643 = 18708965) B18708965
theorem B8315095 : Blo 2189435 8315095 := bstep (se 1 (by rfl) ⟨6236321, by rfl⟩ : syracuseStep 8315095 = 12472643) B12472643
theorem B11086793 : Blo 2189435 11086793 := bstep (se 2 (by rfl) ⟨4157547, by rfl⟩ : syracuseStep 11086793 = 8315095) B8315095
theorem B7391195 : Blo 2189435 7391195 := bstep (se 1 (by rfl) ⟨5543396, by rfl⟩ : syracuseStep 7391195 = 11086793) B11086793
theorem B4927463 : Blo 2189435 4927463 := bstep (se 1 (by rfl) ⟨3695597, by rfl⟩ : syracuseStep 4927463 = 7391195) B7391195
theorem B3284975 : Blo 2189435 3284975 := bstep (se 1 (by rfl) ⟨2463731, by rfl⟩ : syracuseStep 3284975 = 4927463) B4927463
theorem B2189983 : Blo 2189435 2189983 := bstep (se 1 (by rfl) ⟨1642487, by rfl⟩ : syracuseStep 2189983 = 3284975) B3284975
theorem B3284981 : Blo 2189435 3284981 := bbase (se 5 (by rfl) ⟨153983, by rfl⟩ : syracuseStep 3284981 = 307967) (by norm_num)
theorem B2189987 : Blo 2189435 2189987 := bstep (se 1 (by rfl) ⟨1642490, by rfl⟩ : syracuseStep 2189987 = 3284981) B3284981
theorem B5261917 : Blo 2189435 5261917 := bbase (se 3 (by rfl) ⟨986609, by rfl⟩ : syracuseStep 5261917 = 1973219) (by norm_num)
theorem B7015889 : Blo 2189435 7015889 := bstep (se 2 (by rfl) ⟨2630958, by rfl⟩ : syracuseStep 7015889 = 5261917) B5261917
theorem B4677259 : Blo 2189435 4677259 := bstep (se 1 (by rfl) ⟨3507944, by rfl⟩ : syracuseStep 4677259 = 7015889) B7015889
theorem B6236345 : Blo 2189435 6236345 := bstep (se 2 (by rfl) ⟨2338629, by rfl⟩ : syracuseStep 6236345 = 4677259) B4677259
theorem B4157563 : Blo 2189435 4157563 := bstep (se 1 (by rfl) ⟨3118172, by rfl⟩ : syracuseStep 4157563 = 6236345) B6236345
theorem B5543417 : Blo 2189435 5543417 := bstep (se 2 (by rfl) ⟨2078781, by rfl⟩ : syracuseStep 5543417 = 4157563) B4157563
theorem B3695611 : Blo 2189435 3695611 := bstep (se 1 (by rfl) ⟨2771708, by rfl⟩ : syracuseStep 3695611 = 5543417) B5543417
theorem B4927481 : Blo 2189435 4927481 := bstep (se 2 (by rfl) ⟨1847805, by rfl⟩ : syracuseStep 4927481 = 3695611) B3695611
theorem B3284987 : Blo 2189435 3284987 := bstep (se 1 (by rfl) ⟨2463740, by rfl⟩ : syracuseStep 3284987 = 4927481) B4927481
theorem B2189991 : Blo 2189435 2189991 := bstep (se 1 (by rfl) ⟨1642493, by rfl⟩ : syracuseStep 2189991 = 3284987) B3284987
theorem B2463745 : Blo 2189435 2463745 := bbase (se 2 (by rfl) ⟨923904, by rfl⟩ : syracuseStep 2463745 = 1847809) (by norm_num)
theorem B3284993 : Blo 2189435 3284993 := bstep (se 2 (by rfl) ⟨1231872, by rfl⟩ : syracuseStep 3284993 = 2463745) B2463745
theorem B2189995 : Blo 2189435 2189995 := bstep (se 1 (by rfl) ⟨1642496, by rfl⟩ : syracuseStep 2189995 = 3284993) B3284993
theorem B5543437 : Blo 2189435 5543437 := bbase (se 3 (by rfl) ⟨1039394, by rfl⟩ : syracuseStep 5543437 = 2078789) (by norm_num)
theorem B7391249 : Blo 2189435 7391249 := bstep (se 2 (by rfl) ⟨2771718, by rfl⟩ : syracuseStep 7391249 = 5543437) B5543437
theorem B4927499 : Blo 2189435 4927499 := bstep (se 1 (by rfl) ⟨3695624, by rfl⟩ : syracuseStep 4927499 = 7391249) B7391249
theorem B3284999 : Blo 2189435 3284999 := bstep (se 1 (by rfl) ⟨2463749, by rfl⟩ : syracuseStep 3284999 = 4927499) B4927499
theorem B2189999 : Blo 2189435 2189999 := bstep (se 1 (by rfl) ⟨1642499, by rfl⟩ : syracuseStep 2189999 = 3284999) B3284999
theorem B3285005 : Blo 2189435 3285005 := bbase (se 3 (by rfl) ⟨615938, by rfl⟩ : syracuseStep 3285005 = 1231877) (by norm_num)
theorem B2190003 : Blo 2189435 2190003 := bstep (se 1 (by rfl) ⟨1642502, by rfl⟩ : syracuseStep 2190003 = 3285005) B3285005
theorem B4927517 : Blo 2189435 4927517 := bbase (se 3 (by rfl) ⟨923909, by rfl⟩ : syracuseStep 4927517 = 1847819) (by norm_num)
theorem B3285011 : Blo 2189435 3285011 := bstep (se 1 (by rfl) ⟨2463758, by rfl⟩ : syracuseStep 3285011 = 4927517) B4927517
theorem B2190007 : Blo 2189435 2190007 := bstep (se 1 (by rfl) ⟨1642505, by rfl⟩ : syracuseStep 2190007 = 3285011) B3285011
theorem B3695645 : Blo 2189435 3695645 := bbase (se 3 (by rfl) ⟨692933, by rfl⟩ : syracuseStep 3695645 = 1385867) (by norm_num)
theorem B2463763 : Blo 2189435 2463763 := bstep (se 1 (by rfl) ⟨1847822, by rfl⟩ : syracuseStep 2463763 = 3695645) B3695645
theorem B3285017 : Blo 2189435 3285017 := bstep (se 2 (by rfl) ⟨1231881, by rfl⟩ : syracuseStep 3285017 = 2463763) B2463763
theorem B2190011 : Blo 2189435 2190011 := bstep (se 1 (by rfl) ⟨1642508, by rfl⟩ : syracuseStep 2190011 = 3285017) B3285017
theorem B4994765 : Blo 2189435 4994765 := bbase (se 3 (by rfl) ⟨936518, by rfl⟩ : syracuseStep 4994765 = 1873037) (by norm_num)
theorem B3329843 : Blo 2189435 3329843 := bstep (se 1 (by rfl) ⟨2497382, by rfl⟩ : syracuseStep 3329843 = 4994765) B4994765
theorem B8879581 : Blo 2189435 8879581 := bstep (se 3 (by rfl) ⟨1664921, by rfl⟩ : syracuseStep 8879581 = 3329843) B3329843
theorem B11839441 : Blo 2189435 11839441 := bstep (se 2 (by rfl) ⟨4439790, by rfl⟩ : syracuseStep 11839441 = 8879581) B8879581
theorem B15785921 : Blo 2189435 15785921 := bstep (se 2 (by rfl) ⟨5919720, by rfl⟩ : syracuseStep 15785921 = 11839441) B11839441
theorem B10523947 : Blo 2189435 10523947 := bstep (se 1 (by rfl) ⟨7892960, by rfl⟩ : syracuseStep 10523947 = 15785921) B15785921
theorem B14031929 : Blo 2189435 14031929 := bstep (se 2 (by rfl) ⟨5261973, by rfl⟩ : syracuseStep 14031929 = 10523947) B10523947
theorem B9354619 : Blo 2189435 9354619 := bstep (se 1 (by rfl) ⟨7015964, by rfl⟩ : syracuseStep 9354619 = 14031929) B14031929
theorem B12472825 : Blo 2189435 12472825 := bstep (se 2 (by rfl) ⟨4677309, by rfl⟩ : syracuseStep 12472825 = 9354619) B9354619
theorem B16630433 : Blo 2189435 16630433 := bstep (se 2 (by rfl) ⟨6236412, by rfl⟩ : syracuseStep 16630433 = 12472825) B12472825
theorem B11086955 : Blo 2189435 11086955 := bstep (se 1 (by rfl) ⟨8315216, by rfl⟩ : syracuseStep 11086955 = 16630433) B16630433
theorem B7391303 : Blo 2189435 7391303 := bstep (se 1 (by rfl) ⟨5543477, by rfl⟩ : syracuseStep 7391303 = 11086955) B11086955
theorem B4927535 : Blo 2189435 4927535 := bstep (se 1 (by rfl) ⟨3695651, by rfl⟩ : syracuseStep 4927535 = 7391303) B7391303
theorem B3285023 : Blo 2189435 3285023 := bstep (se 1 (by rfl) ⟨2463767, by rfl⟩ : syracuseStep 3285023 = 4927535) B4927535
theorem B2190015 : Blo 2189435 2190015 := bstep (se 1 (by rfl) ⟨1642511, by rfl⟩ : syracuseStep 2190015 = 3285023) B3285023
theorem B3285029 : Blo 2189435 3285029 := bbase (se 4 (by rfl) ⟨307971, by rfl⟩ : syracuseStep 3285029 = 615943) (by norm_num)
theorem B2190019 : Blo 2189435 2190019 := bstep (se 1 (by rfl) ⟨1642514, by rfl⟩ : syracuseStep 2190019 = 3285029) B3285029
theorem B2771749 : Blo 2189435 2771749 := bbase (se 4 (by rfl) ⟨259851, by rfl⟩ : syracuseStep 2771749 = 519703) (by norm_num)
theorem B3695665 : Blo 2189435 3695665 := bstep (se 2 (by rfl) ⟨1385874, by rfl⟩ : syracuseStep 3695665 = 2771749) B2771749
theorem B4927553 : Blo 2189435 4927553 := bstep (se 2 (by rfl) ⟨1847832, by rfl⟩ : syracuseStep 4927553 = 3695665) B3695665
theorem B3285035 : Blo 2189435 3285035 := bstep (se 1 (by rfl) ⟨2463776, by rfl⟩ : syracuseStep 3285035 = 4927553) B4927553
theorem B2190023 : Blo 2189435 2190023 := bstep (se 1 (by rfl) ⟨1642517, by rfl⟩ : syracuseStep 2190023 = 3285035) B3285035
theorem B2463781 : Blo 2189435 2463781 := bbase (se 4 (by rfl) ⟨230979, by rfl⟩ : syracuseStep 2463781 = 461959) (by norm_num)
theorem B3285041 : Blo 2189435 3285041 := bstep (se 2 (by rfl) ⟨1231890, by rfl⟩ : syracuseStep 3285041 = 2463781) B2463781
theorem B2190027 : Blo 2189435 2190027 := bstep (se 1 (by rfl) ⟨1642520, by rfl⟩ : syracuseStep 2190027 = 3285041) B3285041
theorem B5262013 : Blo 2189435 5262013 := bbase (se 3 (by rfl) ⟨986627, by rfl⟩ : syracuseStep 5262013 = 1973255) (by norm_num)
theorem B7016017 : Blo 2189435 7016017 := bstep (se 2 (by rfl) ⟨2631006, by rfl⟩ : syracuseStep 7016017 = 5262013) B5262013
theorem B9354689 : Blo 2189435 9354689 := bstep (se 2 (by rfl) ⟨3508008, by rfl⟩ : syracuseStep 9354689 = 7016017) B7016017
theorem B6236459 : Blo 2189435 6236459 := bstep (se 1 (by rfl) ⟨4677344, by rfl⟩ : syracuseStep 6236459 = 9354689) B9354689
theorem B4157639 : Blo 2189435 4157639 := bstep (se 1 (by rfl) ⟨3118229, by rfl⟩ : syracuseStep 4157639 = 6236459) B6236459
theorem B2771759 : Blo 2189435 2771759 := bstep (se 1 (by rfl) ⟨2078819, by rfl⟩ : syracuseStep 2771759 = 4157639) B4157639
theorem B7391357 : Blo 2189435 7391357 := bstep (se 3 (by rfl) ⟨1385879, by rfl⟩ : syracuseStep 7391357 = 2771759) B2771759
theorem B4927571 : Blo 2189435 4927571 := bstep (se 1 (by rfl) ⟨3695678, by rfl⟩ : syracuseStep 4927571 = 7391357) B7391357
theorem B3285047 : Blo 2189435 3285047 := bstep (se 1 (by rfl) ⟨2463785, by rfl⟩ : syracuseStep 3285047 = 4927571) B4927571
theorem B2190031 : Blo 2189435 2190031 := bstep (se 1 (by rfl) ⟨1642523, by rfl⟩ : syracuseStep 2190031 = 3285047) B3285047
theorem B3285053 : Blo 2189435 3285053 := bbase (se 3 (by rfl) ⟨615947, by rfl⟩ : syracuseStep 3285053 = 1231895) (by norm_num)
theorem B2190035 : Blo 2189435 2190035 := bstep (se 1 (by rfl) ⟨1642526, by rfl⟩ : syracuseStep 2190035 = 3285053) B3285053
theorem B4927589 : Blo 2189435 4927589 := bbase (se 4 (by rfl) ⟨461961, by rfl⟩ : syracuseStep 4927589 = 923923) (by norm_num)
theorem B3285059 : Blo 2189435 3285059 := bstep (se 1 (by rfl) ⟨2463794, by rfl⟩ : syracuseStep 3285059 = 4927589) B4927589
theorem B2190039 : Blo 2189435 2190039 := bstep (se 1 (by rfl) ⟨1642529, by rfl⟩ : syracuseStep 2190039 = 3285059) B3285059
theorem B5543549 : Blo 2189435 5543549 := bbase (se 3 (by rfl) ⟨1039415, by rfl⟩ : syracuseStep 5543549 = 2078831) (by norm_num)
theorem B3695699 : Blo 2189435 3695699 := bstep (se 1 (by rfl) ⟨2771774, by rfl⟩ : syracuseStep 3695699 = 5543549) B5543549
theorem B2463799 : Blo 2189435 2463799 := bstep (se 1 (by rfl) ⟨1847849, by rfl⟩ : syracuseStep 2463799 = 3695699) B3695699
theorem B3285065 : Blo 2189435 3285065 := bstep (se 2 (by rfl) ⟨1231899, by rfl⟩ : syracuseStep 3285065 = 2463799) B2463799
theorem B2190043 : Blo 2189435 2190043 := bstep (se 1 (by rfl) ⟨1642532, by rfl⟩ : syracuseStep 2190043 = 3285065) B3285065
theorem B4157669 : Blo 2189435 4157669 := bbase (se 4 (by rfl) ⟨389781, by rfl⟩ : syracuseStep 4157669 = 779563) (by norm_num)
theorem B11087117 : Blo 2189435 11087117 := bstep (se 3 (by rfl) ⟨2078834, by rfl⟩ : syracuseStep 11087117 = 4157669) B4157669
theorem B7391411 : Blo 2189435 7391411 := bstep (se 1 (by rfl) ⟨5543558, by rfl⟩ : syracuseStep 7391411 = 11087117) B11087117
theorem B4927607 : Blo 2189435 4927607 := bstep (se 1 (by rfl) ⟨3695705, by rfl⟩ : syracuseStep 4927607 = 7391411) B7391411
theorem B3285071 : Blo 2189435 3285071 := bstep (se 1 (by rfl) ⟨2463803, by rfl⟩ : syracuseStep 3285071 = 4927607) B4927607
theorem B2190047 : Blo 2189435 2190047 := bstep (se 1 (by rfl) ⟨1642535, by rfl⟩ : syracuseStep 2190047 = 3285071) B3285071
theorem B3285077 : Blo 2189435 3285077 := bbase (se 8 (by rfl) ⟨19248, by rfl⟩ : syracuseStep 3285077 = 38497) (by norm_num)
theorem B2190051 : Blo 2189435 2190051 := bstep (se 1 (by rfl) ⟨1642538, by rfl⟩ : syracuseStep 2190051 = 3285077) B3285077
theorem B23679317 : Blo 2189435 23679317 := bbase (se 10 (by rfl) ⟨34686, by rfl⟩ : syracuseStep 23679317 = 69373) (by norm_num)
theorem B15786211 : Blo 2189435 15786211 := bstep (se 1 (by rfl) ⟨11839658, by rfl⟩ : syracuseStep 15786211 = 23679317) B23679317
theorem B21048281 : Blo 2189435 21048281 := bstep (se 2 (by rfl) ⟨7893105, by rfl⟩ : syracuseStep 21048281 = 15786211) B15786211
theorem B14032187 : Blo 2189435 14032187 := bstep (se 1 (by rfl) ⟨10524140, by rfl⟩ : syracuseStep 14032187 = 21048281) B21048281
theorem B9354791 : Blo 2189435 9354791 := bstep (se 1 (by rfl) ⟨7016093, by rfl⟩ : syracuseStep 9354791 = 14032187) B14032187
theorem B6236527 : Blo 2189435 6236527 := bstep (se 1 (by rfl) ⟨4677395, by rfl⟩ : syracuseStep 6236527 = 9354791) B9354791
theorem B8315369 : Blo 2189435 8315369 := bstep (se 2 (by rfl) ⟨3118263, by rfl⟩ : syracuseStep 8315369 = 6236527) B6236527
theorem B5543579 : Blo 2189435 5543579 := bstep (se 1 (by rfl) ⟨4157684, by rfl⟩ : syracuseStep 5543579 = 8315369) B8315369
theorem B3695719 : Blo 2189435 3695719 := bstep (se 1 (by rfl) ⟨2771789, by rfl⟩ : syracuseStep 3695719 = 5543579) B5543579
theorem B4927625 : Blo 2189435 4927625 := bstep (se 2 (by rfl) ⟨1847859, by rfl⟩ : syracuseStep 4927625 = 3695719) B3695719
theorem B3285083 : Blo 2189435 3285083 := bstep (se 1 (by rfl) ⟨2463812, by rfl⟩ : syracuseStep 3285083 = 4927625) B4927625
theorem B2190055 : Blo 2189435 2190055 := bstep (se 1 (by rfl) ⟨1642541, by rfl⟩ : syracuseStep 2190055 = 3285083) B3285083
theorem B2463817 : Blo 2189435 2463817 := bbase (se 2 (by rfl) ⟨923931, by rfl⟩ : syracuseStep 2463817 = 1847863) (by norm_num)
theorem B3285089 : Blo 2189435 3285089 := bstep (se 2 (by rfl) ⟨1231908, by rfl⟩ : syracuseStep 3285089 = 2463817) B2463817
theorem B2190059 : Blo 2189435 2190059 := bstep (se 1 (by rfl) ⟨1642544, by rfl⟩ : syracuseStep 2190059 = 3285089) B3285089
theorem B8428853 : Blo 2189435 8428853 := bbase (se 5 (by rfl) ⟨395102, by rfl⟩ : syracuseStep 8428853 = 790205) (by norm_num)
theorem B5619235 : Blo 2189435 5619235 := bstep (se 1 (by rfl) ⟨4214426, by rfl⟩ : syracuseStep 5619235 = 8428853) B8428853
theorem B7492313 : Blo 2189435 7492313 := bstep (se 2 (by rfl) ⟨2809617, by rfl⟩ : syracuseStep 7492313 = 5619235) B5619235
theorem B4994875 : Blo 2189435 4994875 := bstep (se 1 (by rfl) ⟨3746156, by rfl⟩ : syracuseStep 4994875 = 7492313) B7492313
theorem B6659833 : Blo 2189435 6659833 := bstep (se 2 (by rfl) ⟨2497437, by rfl⟩ : syracuseStep 6659833 = 4994875) B4994875
theorem B8879777 : Blo 2189435 8879777 := bstep (se 2 (by rfl) ⟨3329916, by rfl⟩ : syracuseStep 8879777 = 6659833) B6659833
theorem B5919851 : Blo 2189435 5919851 := bstep (se 1 (by rfl) ⟨4439888, by rfl⟩ : syracuseStep 5919851 = 8879777) B8879777
theorem B3946567 : Blo 2189435 3946567 := bstep (se 1 (by rfl) ⟨2959925, by rfl⟩ : syracuseStep 3946567 = 5919851) B5919851
theorem B5262089 : Blo 2189435 5262089 := bstep (se 2 (by rfl) ⟨1973283, by rfl⟩ : syracuseStep 5262089 = 3946567) B3946567
theorem B14032237 : Blo 2189435 14032237 := bstep (se 3 (by rfl) ⟨2631044, by rfl⟩ : syracuseStep 14032237 = 5262089) B5262089
theorem B18709649 : Blo 2189435 18709649 := bstep (se 2 (by rfl) ⟨7016118, by rfl⟩ : syracuseStep 18709649 = 14032237) B14032237
theorem B12473099 : Blo 2189435 12473099 := bstep (se 1 (by rfl) ⟨9354824, by rfl⟩ : syracuseStep 12473099 = 18709649) B18709649
theorem B8315399 : Blo 2189435 8315399 := bstep (se 1 (by rfl) ⟨6236549, by rfl⟩ : syracuseStep 8315399 = 12473099) B12473099
theorem B5543599 : Blo 2189435 5543599 := bstep (se 1 (by rfl) ⟨4157699, by rfl⟩ : syracuseStep 5543599 = 8315399) B8315399
theorem B7391465 : Blo 2189435 7391465 := bstep (se 2 (by rfl) ⟨2771799, by rfl⟩ : syracuseStep 7391465 = 5543599) B5543599
theorem B4927643 : Blo 2189435 4927643 := bstep (se 1 (by rfl) ⟨3695732, by rfl⟩ : syracuseStep 4927643 = 7391465) B7391465
theorem B3285095 : Blo 2189435 3285095 := bstep (se 1 (by rfl) ⟨2463821, by rfl⟩ : syracuseStep 3285095 = 4927643) B4927643
theorem B2190063 : Blo 2189435 2190063 := bstep (se 1 (by rfl) ⟨1642547, by rfl⟩ : syracuseStep 2190063 = 3285095) B3285095
theorem B3285101 : Blo 2189435 3285101 := bbase (se 3 (by rfl) ⟨615956, by rfl⟩ : syracuseStep 3285101 = 1231913) (by norm_num)
theorem B2190067 : Blo 2189435 2190067 := bstep (se 1 (by rfl) ⟨1642550, by rfl⟩ : syracuseStep 2190067 = 3285101) B3285101
theorem B4927661 : Blo 2189435 4927661 := bbase (se 3 (by rfl) ⟨923936, by rfl⟩ : syracuseStep 4927661 = 1847873) (by norm_num)
theorem B3285107 : Blo 2189435 3285107 := bstep (se 1 (by rfl) ⟨2463830, by rfl⟩ : syracuseStep 3285107 = 4927661) B4927661
theorem B2190071 : Blo 2189435 2190071 := bstep (se 1 (by rfl) ⟨1642553, by rfl⟩ : syracuseStep 2190071 = 3285107) B3285107
theorem B11238533 : Blo 2189435 11238533 := bbase (se 4 (by rfl) ⟨1053612, by rfl⟩ : syracuseStep 11238533 = 2107225) (by norm_num)
theorem B7492355 : Blo 2189435 7492355 := bstep (se 1 (by rfl) ⟨5619266, by rfl⟩ : syracuseStep 7492355 = 11238533) B11238533
theorem B4994903 : Blo 2189435 4994903 := bstep (se 1 (by rfl) ⟨3746177, by rfl⟩ : syracuseStep 4994903 = 7492355) B7492355
theorem B13319741 : Blo 2189435 13319741 := bstep (se 3 (by rfl) ⟨2497451, by rfl⟩ : syracuseStep 13319741 = 4994903) B4994903
theorem B35519309 : Blo 2189435 35519309 := bstep (se 3 (by rfl) ⟨6659870, by rfl⟩ : syracuseStep 35519309 = 13319741) B13319741
theorem B23679539 : Blo 2189435 23679539 := bstep (se 1 (by rfl) ⟨17759654, by rfl⟩ : syracuseStep 23679539 = 35519309) B35519309
theorem B15786359 : Blo 2189435 15786359 := bstep (se 1 (by rfl) ⟨11839769, by rfl⟩ : syracuseStep 15786359 = 23679539) B23679539
theorem B10524239 : Blo 2189435 10524239 := bstep (se 1 (by rfl) ⟨7893179, by rfl⟩ : syracuseStep 10524239 = 15786359) B15786359
theorem B7016159 : Blo 2189435 7016159 := bstep (se 1 (by rfl) ⟨5262119, by rfl⟩ : syracuseStep 7016159 = 10524239) B10524239
theorem B4677439 : Blo 2189435 4677439 := bstep (se 1 (by rfl) ⟨3508079, by rfl⟩ : syracuseStep 4677439 = 7016159) B7016159
theorem B6236585 : Blo 2189435 6236585 := bstep (se 2 (by rfl) ⟨2338719, by rfl⟩ : syracuseStep 6236585 = 4677439) B4677439
theorem B4157723 : Blo 2189435 4157723 := bstep (se 1 (by rfl) ⟨3118292, by rfl⟩ : syracuseStep 4157723 = 6236585) B6236585
theorem B2771815 : Blo 2189435 2771815 := bstep (se 1 (by rfl) ⟨2078861, by rfl⟩ : syracuseStep 2771815 = 4157723) B4157723
theorem B3695753 : Blo 2189435 3695753 := bstep (se 2 (by rfl) ⟨1385907, by rfl⟩ : syracuseStep 3695753 = 2771815) B2771815
theorem B2463835 : Blo 2189435 2463835 := bstep (se 1 (by rfl) ⟨1847876, by rfl⟩ : syracuseStep 2463835 = 3695753) B3695753
theorem B3285113 : Blo 2189435 3285113 := bstep (se 2 (by rfl) ⟨1231917, by rfl⟩ : syracuseStep 3285113 = 2463835) B2463835
theorem B2190075 : Blo 2189435 2190075 := bstep (se 1 (by rfl) ⟨1642556, by rfl⟩ : syracuseStep 2190075 = 3285113) B3285113
theorem B6321685 : Blo 2189435 6321685 := bbase (se 6 (by rfl) ⟨148164, by rfl⟩ : syracuseStep 6321685 = 296329) (by norm_num)
theorem B8428913 : Blo 2189435 8428913 := bstep (se 2 (by rfl) ⟨3160842, by rfl⟩ : syracuseStep 8428913 = 6321685) B6321685
theorem B5619275 : Blo 2189435 5619275 := bstep (se 1 (by rfl) ⟨4214456, by rfl⟩ : syracuseStep 5619275 = 8428913) B8428913
theorem B3746183 : Blo 2189435 3746183 := bstep (se 1 (by rfl) ⟨2809637, by rfl⟩ : syracuseStep 3746183 = 5619275) B5619275
theorem B9989821 : Blo 2189435 9989821 := bstep (se 3 (by rfl) ⟨1873091, by rfl⟩ : syracuseStep 9989821 = 3746183) B3746183
theorem B13319761 : Blo 2189435 13319761 := bstep (se 2 (by rfl) ⟨4994910, by rfl⟩ : syracuseStep 13319761 = 9989821) B9989821
theorem B17759681 : Blo 2189435 17759681 := bstep (se 2 (by rfl) ⟨6659880, by rfl⟩ : syracuseStep 17759681 = 13319761) B13319761
theorem B11839787 : Blo 2189435 11839787 := bstep (se 1 (by rfl) ⟨8879840, by rfl⟩ : syracuseStep 11839787 = 17759681) B17759681
theorem B7893191 : Blo 2189435 7893191 := bstep (se 1 (by rfl) ⟨5919893, by rfl⟩ : syracuseStep 7893191 = 11839787) B11839787
theorem B5262127 : Blo 2189435 5262127 := bstep (se 1 (by rfl) ⟨3946595, by rfl⟩ : syracuseStep 5262127 = 7893191) B7893191
theorem B28064677 : Blo 2189435 28064677 := bstep (se 4 (by rfl) ⟨2631063, by rfl⟩ : syracuseStep 28064677 = 5262127) B5262127
theorem B37419569 : Blo 2189435 37419569 := bstep (se 2 (by rfl) ⟨14032338, by rfl⟩ : syracuseStep 37419569 = 28064677) B28064677
theorem B24946379 : Blo 2189435 24946379 := bstep (se 1 (by rfl) ⟨18709784, by rfl⟩ : syracuseStep 24946379 = 37419569) B37419569
theorem B16630919 : Blo 2189435 16630919 := bstep (se 1 (by rfl) ⟨12473189, by rfl⟩ : syracuseStep 16630919 = 24946379) B24946379
theorem B11087279 : Blo 2189435 11087279 := bstep (se 1 (by rfl) ⟨8315459, by rfl⟩ : syracuseStep 11087279 = 16630919) B16630919
theorem B7391519 : Blo 2189435 7391519 := bstep (se 1 (by rfl) ⟨5543639, by rfl⟩ : syracuseStep 7391519 = 11087279) B11087279
theorem B4927679 : Blo 2189435 4927679 := bstep (se 1 (by rfl) ⟨3695759, by rfl⟩ : syracuseStep 4927679 = 7391519) B7391519
theorem B3285119 : Blo 2189435 3285119 := bstep (se 1 (by rfl) ⟨2463839, by rfl⟩ : syracuseStep 3285119 = 4927679) B4927679
theorem B2190079 : Blo 2189435 2190079 := bstep (se 1 (by rfl) ⟨1642559, by rfl⟩ : syracuseStep 2190079 = 3285119) B3285119
theorem B3285125 : Blo 2189435 3285125 := bbase (se 4 (by rfl) ⟨307980, by rfl⟩ : syracuseStep 3285125 = 615961) (by norm_num)
theorem B2190083 : Blo 2189435 2190083 := bstep (se 1 (by rfl) ⟨1642562, by rfl⟩ : syracuseStep 2190083 = 3285125) B3285125
theorem B3695773 : Blo 2189435 3695773 := bbase (se 3 (by rfl) ⟨692957, by rfl⟩ : syracuseStep 3695773 = 1385915) (by norm_num)
theorem B4927697 : Blo 2189435 4927697 := bstep (se 2 (by rfl) ⟨1847886, by rfl⟩ : syracuseStep 4927697 = 3695773) B3695773
theorem B3285131 : Blo 2189435 3285131 := bstep (se 1 (by rfl) ⟨2463848, by rfl⟩ : syracuseStep 3285131 = 4927697) B4927697
theorem B2190087 : Blo 2189435 2190087 := bstep (se 1 (by rfl) ⟨1642565, by rfl⟩ : syracuseStep 2190087 = 3285131) B3285131
theorem B2463853 : Blo 2189435 2463853 := bbase (se 3 (by rfl) ⟨461972, by rfl⟩ : syracuseStep 2463853 = 923945) (by norm_num)
theorem B3285137 : Blo 2189435 3285137 := bstep (se 2 (by rfl) ⟨1231926, by rfl⟩ : syracuseStep 3285137 = 2463853) B2463853
theorem B2190091 : Blo 2189435 2190091 := bstep (se 1 (by rfl) ⟨1642568, by rfl⟩ : syracuseStep 2190091 = 3285137) B3285137
theorem B7391573 : Blo 2189435 7391573 := bbase (se 10 (by rfl) ⟨10827, by rfl⟩ : syracuseStep 7391573 = 21655) (by norm_num)
theorem B4927715 : Blo 2189435 4927715 := bstep (se 1 (by rfl) ⟨3695786, by rfl⟩ : syracuseStep 4927715 = 7391573) B7391573
theorem B3285143 : Blo 2189435 3285143 := bstep (se 1 (by rfl) ⟨2463857, by rfl⟩ : syracuseStep 3285143 = 4927715) B4927715
theorem B2190095 : Blo 2189435 2190095 := bstep (se 1 (by rfl) ⟨1642571, by rfl⟩ : syracuseStep 2190095 = 3285143) B3285143
theorem B3285149 : Blo 2189435 3285149 := bbase (se 3 (by rfl) ⟨615965, by rfl⟩ : syracuseStep 3285149 = 1231931) (by norm_num)
theorem B2190099 : Blo 2189435 2190099 := bstep (se 1 (by rfl) ⟨1642574, by rfl⟩ : syracuseStep 2190099 = 3285149) B3285149
theorem B4927733 : Blo 2189435 4927733 := bbase (se 5 (by rfl) ⟨230987, by rfl⟩ : syracuseStep 4927733 = 461975) (by norm_num)
theorem B3285155 : Blo 2189435 3285155 := bstep (se 1 (by rfl) ⟨2463866, by rfl⟩ : syracuseStep 3285155 = 4927733) B4927733
theorem B2190103 : Blo 2189435 2190103 := bstep (se 1 (by rfl) ⟨1642577, by rfl⟩ : syracuseStep 2190103 = 3285155) B3285155
theorem B2219989 : Blo 2189435 2219989 := bbase (se 7 (by rfl) ⟨26015, by rfl⟩ : syracuseStep 2219989 = 52031) (by norm_num)
theorem B2959985 : Blo 2189435 2959985 := bstep (se 2 (by rfl) ⟨1109994, by rfl⟩ : syracuseStep 2959985 = 2219989) B2219989
theorem B7893293 : Blo 2189435 7893293 := bstep (se 3 (by rfl) ⟨1479992, by rfl⟩ : syracuseStep 7893293 = 2959985) B2959985
theorem B21048781 : Blo 2189435 21048781 := bstep (se 3 (by rfl) ⟨3946646, by rfl⟩ : syracuseStep 21048781 = 7893293) B7893293
theorem B28065041 : Blo 2189435 28065041 := bstep (se 2 (by rfl) ⟨10524390, by rfl⟩ : syracuseStep 28065041 = 21048781) B21048781
theorem B18710027 : Blo 2189435 18710027 := bstep (se 1 (by rfl) ⟨14032520, by rfl⟩ : syracuseStep 18710027 = 28065041) B28065041
theorem B12473351 : Blo 2189435 12473351 := bstep (se 1 (by rfl) ⟨9355013, by rfl⟩ : syracuseStep 12473351 = 18710027) B18710027
theorem B8315567 : Blo 2189435 8315567 := bstep (se 1 (by rfl) ⟨6236675, by rfl⟩ : syracuseStep 8315567 = 12473351) B12473351
theorem B5543711 : Blo 2189435 5543711 := bstep (se 1 (by rfl) ⟨4157783, by rfl⟩ : syracuseStep 5543711 = 8315567) B8315567
theorem B3695807 : Blo 2189435 3695807 := bstep (se 1 (by rfl) ⟨2771855, by rfl⟩ : syracuseStep 3695807 = 5543711) B5543711
theorem B2463871 : Blo 2189435 2463871 := bstep (se 1 (by rfl) ⟨1847903, by rfl⟩ : syracuseStep 2463871 = 3695807) B3695807
theorem B3285161 : Blo 2189435 3285161 := bstep (se 2 (by rfl) ⟨1231935, by rfl⟩ : syracuseStep 3285161 = 2463871) B2463871
theorem B2190107 : Blo 2189435 2190107 := bstep (se 1 (by rfl) ⟨1642580, by rfl⟩ : syracuseStep 2190107 = 3285161) B3285161
theorem B5262205 : Blo 2189435 5262205 := bbase (se 3 (by rfl) ⟨986663, by rfl⟩ : syracuseStep 5262205 = 1973327) (by norm_num)
theorem B7016273 : Blo 2189435 7016273 := bstep (se 2 (by rfl) ⟨2631102, by rfl⟩ : syracuseStep 7016273 = 5262205) B5262205
theorem B4677515 : Blo 2189435 4677515 := bstep (se 1 (by rfl) ⟨3508136, by rfl⟩ : syracuseStep 4677515 = 7016273) B7016273
theorem B3118343 : Blo 2189435 3118343 := bstep (se 1 (by rfl) ⟨2338757, by rfl⟩ : syracuseStep 3118343 = 4677515) B4677515
theorem B8315581 : Blo 2189435 8315581 := bstep (se 3 (by rfl) ⟨1559171, by rfl⟩ : syracuseStep 8315581 = 3118343) B3118343
theorem B11087441 : Blo 2189435 11087441 := bstep (se 2 (by rfl) ⟨4157790, by rfl⟩ : syracuseStep 11087441 = 8315581) B8315581
theorem B7391627 : Blo 2189435 7391627 := bstep (se 1 (by rfl) ⟨5543720, by rfl⟩ : syracuseStep 7391627 = 11087441) B11087441
theorem B4927751 : Blo 2189435 4927751 := bstep (se 1 (by rfl) ⟨3695813, by rfl⟩ : syracuseStep 4927751 = 7391627) B7391627
theorem B3285167 : Blo 2189435 3285167 := bstep (se 1 (by rfl) ⟨2463875, by rfl⟩ : syracuseStep 3285167 = 4927751) B4927751
theorem B2190111 : Blo 2189435 2190111 := bstep (se 1 (by rfl) ⟨1642583, by rfl⟩ : syracuseStep 2190111 = 3285167) B3285167
theorem B3285173 : Blo 2189435 3285173 := bbase (se 5 (by rfl) ⟨153992, by rfl⟩ : syracuseStep 3285173 = 307985) (by norm_num)
theorem B2190115 : Blo 2189435 2190115 := bstep (se 1 (by rfl) ⟨1642586, by rfl⟩ : syracuseStep 2190115 = 3285173) B3285173
theorem B5543741 : Blo 2189435 5543741 := bbase (se 3 (by rfl) ⟨1039451, by rfl⟩ : syracuseStep 5543741 = 2078903) (by norm_num)
theorem B3695827 : Blo 2189435 3695827 := bstep (se 1 (by rfl) ⟨2771870, by rfl⟩ : syracuseStep 3695827 = 5543741) B5543741
theorem B4927769 : Blo 2189435 4927769 := bstep (se 2 (by rfl) ⟨1847913, by rfl⟩ : syracuseStep 4927769 = 3695827) B3695827
theorem B3285179 : Blo 2189435 3285179 := bstep (se 1 (by rfl) ⟨2463884, by rfl⟩ : syracuseStep 3285179 = 4927769) B4927769
theorem B2190119 : Blo 2189435 2190119 := bstep (se 1 (by rfl) ⟨1642589, by rfl⟩ : syracuseStep 2190119 = 3285179) B3285179
theorem B2463889 : Blo 2189435 2463889 := bbase (se 2 (by rfl) ⟨923958, by rfl⟩ : syracuseStep 2463889 = 1847917) (by norm_num)
theorem B3285185 : Blo 2189435 3285185 := bstep (se 2 (by rfl) ⟨1231944, by rfl⟩ : syracuseStep 3285185 = 2463889) B2463889
theorem B2190123 : Blo 2189435 2190123 := bstep (se 1 (by rfl) ⟨1642592, by rfl⟩ : syracuseStep 2190123 = 3285185) B3285185
theorem B4157821 : Blo 2189435 4157821 := bbase (se 3 (by rfl) ⟨779591, by rfl⟩ : syracuseStep 4157821 = 1559183) (by norm_num)
theorem B5543761 : Blo 2189435 5543761 := bstep (se 2 (by rfl) ⟨2078910, by rfl⟩ : syracuseStep 5543761 = 4157821) B4157821
theorem B7391681 : Blo 2189435 7391681 := bstep (se 2 (by rfl) ⟨2771880, by rfl⟩ : syracuseStep 7391681 = 5543761) B5543761
theorem B4927787 : Blo 2189435 4927787 := bstep (se 1 (by rfl) ⟨3695840, by rfl⟩ : syracuseStep 4927787 = 7391681) B7391681
theorem B3285191 : Blo 2189435 3285191 := bstep (se 1 (by rfl) ⟨2463893, by rfl⟩ : syracuseStep 3285191 = 4927787) B4927787
theorem B2190127 : Blo 2189435 2190127 := bstep (se 1 (by rfl) ⟨1642595, by rfl⟩ : syracuseStep 2190127 = 3285191) B3285191
theorem B3285197 : Blo 2189435 3285197 := bbase (se 3 (by rfl) ⟨615974, by rfl⟩ : syracuseStep 3285197 = 1231949) (by norm_num)
theorem B2190131 : Blo 2189435 2190131 := bstep (se 1 (by rfl) ⟨1642598, by rfl⟩ : syracuseStep 2190131 = 3285197) B3285197
theorem B4927805 : Blo 2189435 4927805 := bbase (se 3 (by rfl) ⟨923963, by rfl⟩ : syracuseStep 4927805 = 1847927) (by norm_num)
theorem B3285203 : Blo 2189435 3285203 := bstep (se 1 (by rfl) ⟨2463902, by rfl⟩ : syracuseStep 3285203 = 4927805) B4927805
theorem B2190135 : Blo 2189435 2190135 := bstep (se 1 (by rfl) ⟨1642601, by rfl⟩ : syracuseStep 2190135 = 3285203) B3285203
theorem B3695861 : Blo 2189435 3695861 := bbase (se 5 (by rfl) ⟨173243, by rfl⟩ : syracuseStep 3695861 = 346487) (by norm_num)
theorem B2463907 : Blo 2189435 2463907 := bstep (se 1 (by rfl) ⟨1847930, by rfl⟩ : syracuseStep 2463907 = 3695861) B3695861
theorem B3285209 : Blo 2189435 3285209 := bstep (se 2 (by rfl) ⟨1231953, by rfl⟩ : syracuseStep 3285209 = 2463907) B2463907
theorem B2190139 : Blo 2189435 2190139 := bstep (se 1 (by rfl) ⟨1642604, by rfl⟩ : syracuseStep 2190139 = 3285209) B3285209
theorem B8880101 : Blo 2189435 8880101 := bbase (se 4 (by rfl) ⟨832509, by rfl⟩ : syracuseStep 8880101 = 1665019) (by norm_num)
theorem B5920067 : Blo 2189435 5920067 := bstep (se 1 (by rfl) ⟨4440050, by rfl⟩ : syracuseStep 5920067 = 8880101) B8880101
theorem B15786845 : Blo 2189435 15786845 := bstep (se 3 (by rfl) ⟨2960033, by rfl⟩ : syracuseStep 15786845 = 5920067) B5920067
theorem B10524563 : Blo 2189435 10524563 := bstep (se 1 (by rfl) ⟨7893422, by rfl⟩ : syracuseStep 10524563 = 15786845) B15786845
theorem B7016375 : Blo 2189435 7016375 := bstep (se 1 (by rfl) ⟨5262281, by rfl⟩ : syracuseStep 7016375 = 10524563) B10524563
theorem B4677583 : Blo 2189435 4677583 := bstep (se 1 (by rfl) ⟨3508187, by rfl⟩ : syracuseStep 4677583 = 7016375) B7016375
theorem B6236777 : Blo 2189435 6236777 := bstep (se 2 (by rfl) ⟨2338791, by rfl⟩ : syracuseStep 6236777 = 4677583) B4677583
theorem B16631405 : Blo 2189435 16631405 := bstep (se 3 (by rfl) ⟨3118388, by rfl⟩ : syracuseStep 16631405 = 6236777) B6236777
theorem B11087603 : Blo 2189435 11087603 := bstep (se 1 (by rfl) ⟨8315702, by rfl⟩ : syracuseStep 11087603 = 16631405) B16631405
theorem B7391735 : Blo 2189435 7391735 := bstep (se 1 (by rfl) ⟨5543801, by rfl⟩ : syracuseStep 7391735 = 11087603) B11087603
theorem B4927823 : Blo 2189435 4927823 := bstep (se 1 (by rfl) ⟨3695867, by rfl⟩ : syracuseStep 4927823 = 7391735) B7391735
theorem B3285215 : Blo 2189435 3285215 := bstep (se 1 (by rfl) ⟨2463911, by rfl⟩ : syracuseStep 3285215 = 4927823) B4927823
theorem B2190143 : Blo 2189435 2190143 := bstep (se 1 (by rfl) ⟨1642607, by rfl⟩ : syracuseStep 2190143 = 3285215) B3285215
theorem B3285221 : Blo 2189435 3285221 := bbase (se 4 (by rfl) ⟨307989, by rfl⟩ : syracuseStep 3285221 = 615979) (by norm_num)
theorem B2190147 : Blo 2189435 2190147 := bstep (se 1 (by rfl) ⟨1642610, by rfl⟩ : syracuseStep 2190147 = 3285221) B3285221
theorem B4214597 : Blo 2189435 4214597 := bbase (se 4 (by rfl) ⟨395118, by rfl⟩ : syracuseStep 4214597 = 790237) (by norm_num)
theorem B11238925 : Blo 2189435 11238925 := bstep (se 3 (by rfl) ⟨2107298, by rfl⟩ : syracuseStep 11238925 = 4214597) B4214597
theorem B14985233 : Blo 2189435 14985233 := bstep (se 2 (by rfl) ⟨5619462, by rfl⟩ : syracuseStep 14985233 = 11238925) B11238925
theorem B9990155 : Blo 2189435 9990155 := bstep (se 1 (by rfl) ⟨7492616, by rfl⟩ : syracuseStep 9990155 = 14985233) B14985233
theorem B6660103 : Blo 2189435 6660103 := bstep (se 1 (by rfl) ⟨4995077, by rfl⟩ : syracuseStep 6660103 = 9990155) B9990155
theorem B8880137 : Blo 2189435 8880137 := bstep (se 2 (by rfl) ⟨3330051, by rfl⟩ : syracuseStep 8880137 = 6660103) B6660103
theorem B5920091 : Blo 2189435 5920091 := bstep (se 1 (by rfl) ⟨4440068, by rfl⟩ : syracuseStep 5920091 = 8880137) B8880137
theorem B3946727 : Blo 2189435 3946727 := bstep (se 1 (by rfl) ⟨2960045, by rfl⟩ : syracuseStep 3946727 = 5920091) B5920091
theorem B2631151 : Blo 2189435 2631151 := bstep (se 1 (by rfl) ⟨1973363, by rfl⟩ : syracuseStep 2631151 = 3946727) B3946727
theorem B3508201 : Blo 2189435 3508201 := bstep (se 2 (by rfl) ⟨1315575, by rfl⟩ : syracuseStep 3508201 = 2631151) B2631151
theorem B4677601 : Blo 2189435 4677601 := bstep (se 2 (by rfl) ⟨1754100, by rfl⟩ : syracuseStep 4677601 = 3508201) B3508201
theorem B6236801 : Blo 2189435 6236801 := bstep (se 2 (by rfl) ⟨2338800, by rfl⟩ : syracuseStep 6236801 = 4677601) B4677601
theorem B4157867 : Blo 2189435 4157867 := bstep (se 1 (by rfl) ⟨3118400, by rfl⟩ : syracuseStep 4157867 = 6236801) B6236801
theorem B2771911 : Blo 2189435 2771911 := bstep (se 1 (by rfl) ⟨2078933, by rfl⟩ : syracuseStep 2771911 = 4157867) B4157867
theorem B3695881 : Blo 2189435 3695881 := bstep (se 2 (by rfl) ⟨1385955, by rfl⟩ : syracuseStep 3695881 = 2771911) B2771911
theorem B4927841 : Blo 2189435 4927841 := bstep (se 2 (by rfl) ⟨1847940, by rfl⟩ : syracuseStep 4927841 = 3695881) B3695881
theorem B3285227 : Blo 2189435 3285227 := bstep (se 1 (by rfl) ⟨2463920, by rfl⟩ : syracuseStep 3285227 = 4927841) B4927841
theorem B2190151 : Blo 2189435 2190151 := bstep (se 1 (by rfl) ⟨1642613, by rfl⟩ : syracuseStep 2190151 = 3285227) B3285227
theorem B2463925 : Blo 2189435 2463925 := bbase (se 5 (by rfl) ⟨115496, by rfl⟩ : syracuseStep 2463925 = 230993) (by norm_num)
theorem B3285233 : Blo 2189435 3285233 := bstep (se 2 (by rfl) ⟨1231962, by rfl⟩ : syracuseStep 3285233 = 2463925) B2463925
theorem B2190155 : Blo 2189435 2190155 := bstep (se 1 (by rfl) ⟨1642616, by rfl⟩ : syracuseStep 2190155 = 3285233) B3285233
theorem B2771921 : Blo 2189435 2771921 := bbase (se 2 (by rfl) ⟨1039470, by rfl⟩ : syracuseStep 2771921 = 2078941) (by norm_num)
theorem B7391789 : Blo 2189435 7391789 := bstep (se 3 (by rfl) ⟨1385960, by rfl⟩ : syracuseStep 7391789 = 2771921) B2771921
theorem B4927859 : Blo 2189435 4927859 := bstep (se 1 (by rfl) ⟨3695894, by rfl⟩ : syracuseStep 4927859 = 7391789) B7391789
theorem B3285239 : Blo 2189435 3285239 := bstep (se 1 (by rfl) ⟨2463929, by rfl⟩ : syracuseStep 3285239 = 4927859) B4927859
theorem B2190159 : Blo 2189435 2190159 := bstep (se 1 (by rfl) ⟨1642619, by rfl⟩ : syracuseStep 2190159 = 3285239) B3285239
theorem B3285245 : Blo 2189435 3285245 := bbase (se 3 (by rfl) ⟨615983, by rfl⟩ : syracuseStep 3285245 = 1231967) (by norm_num)
theorem B2190163 : Blo 2189435 2190163 := bstep (se 1 (by rfl) ⟨1642622, by rfl⟩ : syracuseStep 2190163 = 3285245) B3285245
theorem B4927877 : Blo 2189435 4927877 := bbase (se 4 (by rfl) ⟨461988, by rfl⟩ : syracuseStep 4927877 = 923977) (by norm_num)
theorem B3285251 : Blo 2189435 3285251 := bstep (se 1 (by rfl) ⟨2463938, by rfl⟩ : syracuseStep 3285251 = 4927877) B4927877
theorem B2190167 : Blo 2189435 2190167 := bstep (se 1 (by rfl) ⟨1642625, by rfl⟩ : syracuseStep 2190167 = 3285251) B3285251
theorem B3118429 : Blo 2189435 3118429 := bbase (se 3 (by rfl) ⟨584705, by rfl⟩ : syracuseStep 3118429 = 1169411) (by norm_num)
theorem B4157905 : Blo 2189435 4157905 := bstep (se 2 (by rfl) ⟨1559214, by rfl⟩ : syracuseStep 4157905 = 3118429) B3118429
theorem B5543873 : Blo 2189435 5543873 := bstep (se 2 (by rfl) ⟨2078952, by rfl⟩ : syracuseStep 5543873 = 4157905) B4157905
theorem B3695915 : Blo 2189435 3695915 := bstep (se 1 (by rfl) ⟨2771936, by rfl⟩ : syracuseStep 3695915 = 5543873) B5543873
theorem B2463943 : Blo 2189435 2463943 := bstep (se 1 (by rfl) ⟨1847957, by rfl⟩ : syracuseStep 2463943 = 3695915) B3695915
theorem B3285257 : Blo 2189435 3285257 := bstep (se 2 (by rfl) ⟨1231971, by rfl⟩ : syracuseStep 3285257 = 2463943) B2463943
theorem B2190171 : Blo 2189435 2190171 := bstep (se 1 (by rfl) ⟨1642628, by rfl⟩ : syracuseStep 2190171 = 3285257) B3285257
theorem B11087765 : Blo 2189435 11087765 := bbase (se 6 (by rfl) ⟨259869, by rfl⟩ : syracuseStep 11087765 = 519739) (by norm_num)
theorem B7391843 : Blo 2189435 7391843 := bstep (se 1 (by rfl) ⟨5543882, by rfl⟩ : syracuseStep 7391843 = 11087765) B11087765
theorem B4927895 : Blo 2189435 4927895 := bstep (se 1 (by rfl) ⟨3695921, by rfl⟩ : syracuseStep 4927895 = 7391843) B7391843
theorem B3285263 : Blo 2189435 3285263 := bstep (se 1 (by rfl) ⟨2463947, by rfl⟩ : syracuseStep 3285263 = 4927895) B4927895
theorem B2190175 : Blo 2189435 2190175 := bstep (se 1 (by rfl) ⟨1642631, by rfl⟩ : syracuseStep 2190175 = 3285263) B3285263
theorem B3285269 : Blo 2189435 3285269 := bbase (se 6 (by rfl) ⟨76998, by rfl⟩ : syracuseStep 3285269 = 153997) (by norm_num)
theorem B2190179 : Blo 2189435 2190179 := bstep (se 1 (by rfl) ⟨1642634, by rfl⟩ : syracuseStep 2190179 = 3285269) B3285269
theorem B2370745 : Blo 2189435 2370745 := bbase (se 2 (by rfl) ⟨889029, by rfl⟩ : syracuseStep 2370745 = 1778059) (by norm_num)
theorem B3160993 : Blo 2189435 3160993 := bstep (se 2 (by rfl) ⟨1185372, by rfl⟩ : syracuseStep 3160993 = 2370745) B2370745
theorem B4214657 : Blo 2189435 4214657 := bstep (se 2 (by rfl) ⟨1580496, by rfl⟩ : syracuseStep 4214657 = 3160993) B3160993
theorem B2809771 : Blo 2189435 2809771 := bstep (se 1 (by rfl) ⟨2107328, by rfl⟩ : syracuseStep 2809771 = 4214657) B4214657
theorem B14985445 : Blo 2189435 14985445 := bstep (se 4 (by rfl) ⟨1404885, by rfl⟩ : syracuseStep 14985445 = 2809771) B2809771
theorem B19980593 : Blo 2189435 19980593 := bstep (se 2 (by rfl) ⟨7492722, by rfl⟩ : syracuseStep 19980593 = 14985445) B14985445
theorem B13320395 : Blo 2189435 13320395 := bstep (se 1 (by rfl) ⟨9990296, by rfl⟩ : syracuseStep 13320395 = 19980593) B19980593
theorem B8880263 : Blo 2189435 8880263 := bstep (se 1 (by rfl) ⟨6660197, by rfl⟩ : syracuseStep 8880263 = 13320395) B13320395
theorem B5920175 : Blo 2189435 5920175 := bstep (se 1 (by rfl) ⟨4440131, by rfl⟩ : syracuseStep 5920175 = 8880263) B8880263
theorem B15787133 : Blo 2189435 15787133 := bstep (se 3 (by rfl) ⟨2960087, by rfl⟩ : syracuseStep 15787133 = 5920175) B5920175
theorem B10524755 : Blo 2189435 10524755 := bstep (se 1 (by rfl) ⟨7893566, by rfl⟩ : syracuseStep 10524755 = 15787133) B15787133
theorem B28066013 : Blo 2189435 28066013 := bstep (se 3 (by rfl) ⟨5262377, by rfl⟩ : syracuseStep 28066013 = 10524755) B10524755
theorem B18710675 : Blo 2189435 18710675 := bstep (se 1 (by rfl) ⟨14033006, by rfl⟩ : syracuseStep 18710675 = 28066013) B28066013
theorem B12473783 : Blo 2189435 12473783 := bstep (se 1 (by rfl) ⟨9355337, by rfl⟩ : syracuseStep 12473783 = 18710675) B18710675
theorem B8315855 : Blo 2189435 8315855 := bstep (se 1 (by rfl) ⟨6236891, by rfl⟩ : syracuseStep 8315855 = 12473783) B12473783
theorem B5543903 : Blo 2189435 5543903 := bstep (se 1 (by rfl) ⟨4157927, by rfl⟩ : syracuseStep 5543903 = 8315855) B8315855
theorem B3695935 : Blo 2189435 3695935 := bstep (se 1 (by rfl) ⟨2771951, by rfl⟩ : syracuseStep 3695935 = 5543903) B5543903
theorem B4927913 : Blo 2189435 4927913 := bstep (se 2 (by rfl) ⟨1847967, by rfl⟩ : syracuseStep 4927913 = 3695935) B3695935
theorem B3285275 : Blo 2189435 3285275 := bstep (se 1 (by rfl) ⟨2463956, by rfl⟩ : syracuseStep 3285275 = 4927913) B4927913
theorem B2190183 : Blo 2189435 2190183 := bstep (se 1 (by rfl) ⟨1642637, by rfl⟩ : syracuseStep 2190183 = 3285275) B3285275
theorem B2463961 : Blo 2189435 2463961 := bbase (se 2 (by rfl) ⟨923985, by rfl⟩ : syracuseStep 2463961 = 1847971) (by norm_num)
theorem B3285281 : Blo 2189435 3285281 := bstep (se 2 (by rfl) ⟨1231980, by rfl⟩ : syracuseStep 3285281 = 2463961) B2463961
theorem B2190187 : Blo 2189435 2190187 := bstep (se 1 (by rfl) ⟨1642640, by rfl⟩ : syracuseStep 2190187 = 3285281) B3285281
theorem B5619565 : Blo 2189435 5619565 := bbase (se 3 (by rfl) ⟨1053668, by rfl⟩ : syracuseStep 5619565 = 2107337) (by norm_num)
theorem B7492753 : Blo 2189435 7492753 := bstep (se 2 (by rfl) ⟨2809782, by rfl⟩ : syracuseStep 7492753 = 5619565) B5619565
theorem B9990337 : Blo 2189435 9990337 := bstep (se 2 (by rfl) ⟨3746376, by rfl⟩ : syracuseStep 9990337 = 7492753) B7492753
theorem B13320449 : Blo 2189435 13320449 := bstep (se 2 (by rfl) ⟨4995168, by rfl⟩ : syracuseStep 13320449 = 9990337) B9990337
theorem B8880299 : Blo 2189435 8880299 := bstep (se 1 (by rfl) ⟨6660224, by rfl⟩ : syracuseStep 8880299 = 13320449) B13320449
theorem B5920199 : Blo 2189435 5920199 := bstep (se 1 (by rfl) ⟨4440149, by rfl⟩ : syracuseStep 5920199 = 8880299) B8880299
theorem B3946799 : Blo 2189435 3946799 := bstep (se 1 (by rfl) ⟨2960099, by rfl⟩ : syracuseStep 3946799 = 5920199) B5920199
theorem B2631199 : Blo 2189435 2631199 := bstep (se 1 (by rfl) ⟨1973399, by rfl⟩ : syracuseStep 2631199 = 3946799) B3946799
theorem B3508265 : Blo 2189435 3508265 := bstep (se 2 (by rfl) ⟨1315599, by rfl⟩ : syracuseStep 3508265 = 2631199) B2631199
theorem B2338843 : Blo 2189435 2338843 := bstep (se 1 (by rfl) ⟨1754132, by rfl⟩ : syracuseStep 2338843 = 3508265) B3508265
theorem B3118457 : Blo 2189435 3118457 := bstep (se 2 (by rfl) ⟨1169421, by rfl⟩ : syracuseStep 3118457 = 2338843) B2338843
theorem B8315885 : Blo 2189435 8315885 := bstep (se 3 (by rfl) ⟨1559228, by rfl⟩ : syracuseStep 8315885 = 3118457) B3118457
theorem B5543923 : Blo 2189435 5543923 := bstep (se 1 (by rfl) ⟨4157942, by rfl⟩ : syracuseStep 5543923 = 8315885) B8315885
theorem B7391897 : Blo 2189435 7391897 := bstep (se 2 (by rfl) ⟨2771961, by rfl⟩ : syracuseStep 7391897 = 5543923) B5543923
theorem B4927931 : Blo 2189435 4927931 := bstep (se 1 (by rfl) ⟨3695948, by rfl⟩ : syracuseStep 4927931 = 7391897) B7391897
theorem B3285287 : Blo 2189435 3285287 := bstep (se 1 (by rfl) ⟨2463965, by rfl⟩ : syracuseStep 3285287 = 4927931) B4927931
theorem B2190191 : Blo 2189435 2190191 := bstep (se 1 (by rfl) ⟨1642643, by rfl⟩ : syracuseStep 2190191 = 3285287) B3285287
theorem B3285293 : Blo 2189435 3285293 := bbase (se 3 (by rfl) ⟨615992, by rfl⟩ : syracuseStep 3285293 = 1231985) (by norm_num)
theorem B2190195 : Blo 2189435 2190195 := bstep (se 1 (by rfl) ⟨1642646, by rfl⟩ : syracuseStep 2190195 = 3285293) B3285293
theorem B4927949 : Blo 2189435 4927949 := bbase (se 3 (by rfl) ⟨923990, by rfl⟩ : syracuseStep 4927949 = 1847981) (by norm_num)
theorem B3285299 : Blo 2189435 3285299 := bstep (se 1 (by rfl) ⟨2463974, by rfl⟩ : syracuseStep 3285299 = 4927949) B4927949
theorem B2190199 : Blo 2189435 2190199 := bstep (se 1 (by rfl) ⟨1642649, by rfl⟩ : syracuseStep 2190199 = 3285299) B3285299
theorem B2771977 : Blo 2189435 2771977 := bbase (se 2 (by rfl) ⟨1039491, by rfl⟩ : syracuseStep 2771977 = 2078983) (by norm_num)
theorem B3695969 : Blo 2189435 3695969 := bstep (se 2 (by rfl) ⟨1385988, by rfl⟩ : syracuseStep 3695969 = 2771977) B2771977
theorem B2463979 : Blo 2189435 2463979 := bstep (se 1 (by rfl) ⟨1847984, by rfl⟩ : syracuseStep 2463979 = 3695969) B3695969
theorem B3285305 : Blo 2189435 3285305 := bstep (se 2 (by rfl) ⟨1231989, by rfl⟩ : syracuseStep 3285305 = 2463979) B2463979
theorem B2190203 : Blo 2189435 2190203 := bstep (se 1 (by rfl) ⟨1642652, by rfl⟩ : syracuseStep 2190203 = 3285305) B3285305
theorem B25288213 : Blo 2189435 25288213 := bbase (se 6 (by rfl) ⟨592692, by rfl⟩ : syracuseStep 25288213 = 1185385) (by norm_num)
theorem B33717617 : Blo 2189435 33717617 := bstep (se 2 (by rfl) ⟨12644106, by rfl⟩ : syracuseStep 33717617 = 25288213) B25288213
theorem B22478411 : Blo 2189435 22478411 := bstep (se 1 (by rfl) ⟨16858808, by rfl⟩ : syracuseStep 22478411 = 33717617) B33717617
theorem B14985607 : Blo 2189435 14985607 := bstep (se 1 (by rfl) ⟨11239205, by rfl⟩ : syracuseStep 14985607 = 22478411) B22478411
theorem B19980809 : Blo 2189435 19980809 := bstep (se 2 (by rfl) ⟨7492803, by rfl⟩ : syracuseStep 19980809 = 14985607) B14985607
theorem B13320539 : Blo 2189435 13320539 := bstep (se 1 (by rfl) ⟨9990404, by rfl⟩ : syracuseStep 13320539 = 19980809) B19980809
theorem B8880359 : Blo 2189435 8880359 := bstep (se 1 (by rfl) ⟨6660269, by rfl⟩ : syracuseStep 8880359 = 13320539) B13320539
theorem B23680957 : Blo 2189435 23680957 := bstep (se 3 (by rfl) ⟨4440179, by rfl⟩ : syracuseStep 23680957 = 8880359) B8880359
theorem B31574609 : Blo 2189435 31574609 := bstep (se 2 (by rfl) ⟨11840478, by rfl⟩ : syracuseStep 31574609 = 23680957) B23680957
theorem B21049739 : Blo 2189435 21049739 := bstep (se 1 (by rfl) ⟨15787304, by rfl⟩ : syracuseStep 21049739 = 31574609) B31574609
theorem B14033159 : Blo 2189435 14033159 := bstep (se 1 (by rfl) ⟨10524869, by rfl⟩ : syracuseStep 14033159 = 21049739) B21049739
theorem B9355439 : Blo 2189435 9355439 := bstep (se 1 (by rfl) ⟨7016579, by rfl⟩ : syracuseStep 9355439 = 14033159) B14033159
theorem B24947837 : Blo 2189435 24947837 := bstep (se 3 (by rfl) ⟨4677719, by rfl⟩ : syracuseStep 24947837 = 9355439) B9355439
theorem B16631891 : Blo 2189435 16631891 := bstep (se 1 (by rfl) ⟨12473918, by rfl⟩ : syracuseStep 16631891 = 24947837) B24947837
theorem B11087927 : Blo 2189435 11087927 := bstep (se 1 (by rfl) ⟨8315945, by rfl⟩ : syracuseStep 11087927 = 16631891) B16631891
theorem B7391951 : Blo 2189435 7391951 := bstep (se 1 (by rfl) ⟨5543963, by rfl⟩ : syracuseStep 7391951 = 11087927) B11087927
theorem B4927967 : Blo 2189435 4927967 := bstep (se 1 (by rfl) ⟨3695975, by rfl⟩ : syracuseStep 4927967 = 7391951) B7391951
theorem B3285311 : Blo 2189435 3285311 := bstep (se 1 (by rfl) ⟨2463983, by rfl⟩ : syracuseStep 3285311 = 4927967) B4927967
theorem B2190207 : Blo 2189435 2190207 := bstep (se 1 (by rfl) ⟨1642655, by rfl⟩ : syracuseStep 2190207 = 3285311) B3285311
theorem B3285317 : Blo 2189435 3285317 := bbase (se 4 (by rfl) ⟨307998, by rfl⟩ : syracuseStep 3285317 = 615997) (by norm_num)
theorem B2190211 : Blo 2189435 2190211 := bstep (se 1 (by rfl) ⟨1642658, by rfl⟩ : syracuseStep 2190211 = 3285317) B3285317
theorem B3695989 : Blo 2189435 3695989 := bbase (se 5 (by rfl) ⟨173249, by rfl⟩ : syracuseStep 3695989 = 346499) (by norm_num)
theorem B4927985 : Blo 2189435 4927985 := bstep (se 2 (by rfl) ⟨1847994, by rfl⟩ : syracuseStep 4927985 = 3695989) B3695989
theorem B3285323 : Blo 2189435 3285323 := bstep (se 1 (by rfl) ⟨2463992, by rfl⟩ : syracuseStep 3285323 = 4927985) B4927985
theorem B2190215 : Blo 2189435 2190215 := bstep (se 1 (by rfl) ⟨1642661, by rfl⟩ : syracuseStep 2190215 = 3285323) B3285323
theorem B2463997 : Blo 2189435 2463997 := bbase (se 3 (by rfl) ⟨461999, by rfl⟩ : syracuseStep 2463997 = 923999) (by norm_num)
theorem B3285329 : Blo 2189435 3285329 := bstep (se 2 (by rfl) ⟨1231998, by rfl⟩ : syracuseStep 3285329 = 2463997) B2463997
theorem B2190219 : Blo 2189435 2190219 := bstep (se 1 (by rfl) ⟨1642664, by rfl⟩ : syracuseStep 2190219 = 3285329) B3285329
theorem B7392005 : Blo 2189435 7392005 := bbase (se 4 (by rfl) ⟨693000, by rfl⟩ : syracuseStep 7392005 = 1386001) (by norm_num)
theorem B4928003 : Blo 2189435 4928003 := bstep (se 1 (by rfl) ⟨3696002, by rfl⟩ : syracuseStep 4928003 = 7392005) B7392005
theorem B3285335 : Blo 2189435 3285335 := bstep (se 1 (by rfl) ⟨2464001, by rfl⟩ : syracuseStep 3285335 = 4928003) B4928003
theorem B2190223 : Blo 2189435 2190223 := bstep (se 1 (by rfl) ⟨1642667, by rfl⟩ : syracuseStep 2190223 = 3285335) B3285335
theorem B3285341 : Blo 2189435 3285341 := bbase (se 3 (by rfl) ⟨616001, by rfl⟩ : syracuseStep 3285341 = 1232003) (by norm_num)
theorem B2190227 : Blo 2189435 2190227 := bstep (se 1 (by rfl) ⟨1642670, by rfl⟩ : syracuseStep 2190227 = 3285341) B3285341
theorem B4928021 : Blo 2189435 4928021 := bbase (se 6 (by rfl) ⟨115500, by rfl⟩ : syracuseStep 4928021 = 231001) (by norm_num)
theorem B3285347 : Blo 2189435 3285347 := bstep (se 1 (by rfl) ⟨2464010, by rfl⟩ : syracuseStep 3285347 = 4928021) B4928021
theorem B2190231 : Blo 2189435 2190231 := bstep (se 1 (by rfl) ⟨1642673, by rfl⟩ : syracuseStep 2190231 = 3285347) B3285347
theorem B8316053 : Blo 2189435 8316053 := bbase (se 6 (by rfl) ⟨194907, by rfl⟩ : syracuseStep 8316053 = 389815) (by norm_num)
theorem B5544035 : Blo 2189435 5544035 := bstep (se 1 (by rfl) ⟨4158026, by rfl⟩ : syracuseStep 5544035 = 8316053) B8316053
theorem B3696023 : Blo 2189435 3696023 := bstep (se 1 (by rfl) ⟨2772017, by rfl⟩ : syracuseStep 3696023 = 5544035) B5544035
theorem B2464015 : Blo 2189435 2464015 := bstep (se 1 (by rfl) ⟨1848011, by rfl⟩ : syracuseStep 2464015 = 3696023) B3696023
theorem B3285353 : Blo 2189435 3285353 := bstep (se 2 (by rfl) ⟨1232007, by rfl⟩ : syracuseStep 3285353 = 2464015) B2464015
theorem B2190235 : Blo 2189435 2190235 := bstep (se 1 (by rfl) ⟨1642676, by rfl⟩ : syracuseStep 2190235 = 3285353) B3285353
theorem B12474101 : Blo 2189435 12474101 := bbase (se 5 (by rfl) ⟨584723, by rfl⟩ : syracuseStep 12474101 = 1169447) (by norm_num)
theorem B8316067 : Blo 2189435 8316067 := bstep (se 1 (by rfl) ⟨6237050, by rfl⟩ : syracuseStep 8316067 = 12474101) B12474101
theorem B11088089 : Blo 2189435 11088089 := bstep (se 2 (by rfl) ⟨4158033, by rfl⟩ : syracuseStep 11088089 = 8316067) B8316067
theorem B7392059 : Blo 2189435 7392059 := bstep (se 1 (by rfl) ⟨5544044, by rfl⟩ : syracuseStep 7392059 = 11088089) B11088089
theorem B4928039 : Blo 2189435 4928039 := bstep (se 1 (by rfl) ⟨3696029, by rfl⟩ : syracuseStep 4928039 = 7392059) B7392059
theorem B3285359 : Blo 2189435 3285359 := bstep (se 1 (by rfl) ⟨2464019, by rfl⟩ : syracuseStep 3285359 = 4928039) B4928039
theorem B2190239 : Blo 2189435 2190239 := bstep (se 1 (by rfl) ⟨1642679, by rfl⟩ : syracuseStep 2190239 = 3285359) B3285359
theorem B3285365 : Blo 2189435 3285365 := bbase (se 5 (by rfl) ⟨154001, by rfl⟩ : syracuseStep 3285365 = 308003) (by norm_num)
theorem B2190243 : Blo 2189435 2190243 := bstep (se 1 (by rfl) ⟨1642682, by rfl⟩ : syracuseStep 2190243 = 3285365) B3285365
theorem B5262533 : Blo 2189435 5262533 := bbase (se 4 (by rfl) ⟨493362, by rfl⟩ : syracuseStep 5262533 = 986725) (by norm_num)
theorem B3508355 : Blo 2189435 3508355 := bstep (se 1 (by rfl) ⟨2631266, by rfl⟩ : syracuseStep 3508355 = 5262533) B5262533
theorem B2338903 : Blo 2189435 2338903 := bstep (se 1 (by rfl) ⟨1754177, by rfl⟩ : syracuseStep 2338903 = 3508355) B3508355
theorem B3118537 : Blo 2189435 3118537 := bstep (se 2 (by rfl) ⟨1169451, by rfl⟩ : syracuseStep 3118537 = 2338903) B2338903
theorem B4158049 : Blo 2189435 4158049 := bstep (se 2 (by rfl) ⟨1559268, by rfl⟩ : syracuseStep 4158049 = 3118537) B3118537
theorem B5544065 : Blo 2189435 5544065 := bstep (se 2 (by rfl) ⟨2079024, by rfl⟩ : syracuseStep 5544065 = 4158049) B4158049
theorem B3696043 : Blo 2189435 3696043 := bstep (se 1 (by rfl) ⟨2772032, by rfl⟩ : syracuseStep 3696043 = 5544065) B5544065
theorem B4928057 : Blo 2189435 4928057 := bstep (se 2 (by rfl) ⟨1848021, by rfl⟩ : syracuseStep 4928057 = 3696043) B3696043
theorem B3285371 : Blo 2189435 3285371 := bstep (se 1 (by rfl) ⟨2464028, by rfl⟩ : syracuseStep 3285371 = 4928057) B4928057
theorem B2190247 : Blo 2189435 2190247 := bstep (se 1 (by rfl) ⟨1642685, by rfl⟩ : syracuseStep 2190247 = 3285371) B3285371
theorem B2464033 : Blo 2189435 2464033 := bbase (se 2 (by rfl) ⟨924012, by rfl⟩ : syracuseStep 2464033 = 1848025) (by norm_num)
theorem B3285377 : Blo 2189435 3285377 := bstep (se 2 (by rfl) ⟨1232016, by rfl⟩ : syracuseStep 3285377 = 2464033) B2464033
theorem B2190251 : Blo 2189435 2190251 := bstep (se 1 (by rfl) ⟨1642688, by rfl⟩ : syracuseStep 2190251 = 3285377) B3285377
theorem B5544085 : Blo 2189435 5544085 := bbase (se 6 (by rfl) ⟨129939, by rfl⟩ : syracuseStep 5544085 = 259879) (by norm_num)
theorem B7392113 : Blo 2189435 7392113 := bstep (se 2 (by rfl) ⟨2772042, by rfl⟩ : syracuseStep 7392113 = 5544085) B5544085
theorem B4928075 : Blo 2189435 4928075 := bstep (se 1 (by rfl) ⟨3696056, by rfl⟩ : syracuseStep 4928075 = 7392113) B7392113
theorem B3285383 : Blo 2189435 3285383 := bstep (se 1 (by rfl) ⟨2464037, by rfl⟩ : syracuseStep 3285383 = 4928075) B4928075
theorem B2190255 : Blo 2189435 2190255 := bstep (se 1 (by rfl) ⟨1642691, by rfl⟩ : syracuseStep 2190255 = 3285383) B3285383
theorem B3285389 : Blo 2189435 3285389 := bbase (se 3 (by rfl) ⟨616010, by rfl⟩ : syracuseStep 3285389 = 1232021) (by norm_num)
theorem B2190259 : Blo 2189435 2190259 := bstep (se 1 (by rfl) ⟨1642694, by rfl⟩ : syracuseStep 2190259 = 3285389) B3285389
theorem B4928093 : Blo 2189435 4928093 := bbase (se 3 (by rfl) ⟨924017, by rfl⟩ : syracuseStep 4928093 = 1848035) (by norm_num)
theorem B3285395 : Blo 2189435 3285395 := bstep (se 1 (by rfl) ⟨2464046, by rfl⟩ : syracuseStep 3285395 = 4928093) B4928093
theorem B2190263 : Blo 2189435 2190263 := bstep (se 1 (by rfl) ⟨1642697, by rfl⟩ : syracuseStep 2190263 = 3285395) B3285395
theorem B3696077 : Blo 2189435 3696077 := bbase (se 3 (by rfl) ⟨693014, by rfl⟩ : syracuseStep 3696077 = 1386029) (by norm_num)
theorem B2464051 : Blo 2189435 2464051 := bstep (se 1 (by rfl) ⟨1848038, by rfl⟩ : syracuseStep 2464051 = 3696077) B3696077
theorem B3285401 : Blo 2189435 3285401 := bstep (se 2 (by rfl) ⟨1232025, by rfl⟩ : syracuseStep 3285401 = 2464051) B2464051
theorem B2190267 : Blo 2189435 2190267 := bstep (se 1 (by rfl) ⟨1642700, by rfl⟩ : syracuseStep 2190267 = 3285401) B3285401
theorem B9124597 : Blo 2189435 9124597 := bbase (se 5 (by rfl) ⟨427715, by rfl⟩ : syracuseStep 9124597 = 855431) (by norm_num)
theorem B12166129 : Blo 2189435 12166129 := bstep (se 2 (by rfl) ⟨4562298, by rfl⟩ : syracuseStep 12166129 = 9124597) B9124597
theorem B16221505 : Blo 2189435 16221505 := bstep (se 2 (by rfl) ⟨6083064, by rfl⟩ : syracuseStep 16221505 = 12166129) B12166129
theorem B21628673 : Blo 2189435 21628673 := bstep (se 2 (by rfl) ⟨8110752, by rfl⟩ : syracuseStep 21628673 = 16221505) B16221505
theorem B14419115 : Blo 2189435 14419115 := bstep (se 1 (by rfl) ⟨10814336, by rfl⟩ : syracuseStep 14419115 = 21628673) B21628673
theorem B9612743 : Blo 2189435 9612743 := bstep (se 1 (by rfl) ⟨7209557, by rfl⟩ : syracuseStep 9612743 = 14419115) B14419115
theorem B25633981 : Blo 2189435 25633981 := bstep (se 3 (by rfl) ⟨4806371, by rfl⟩ : syracuseStep 25633981 = 9612743) B9612743
theorem B34178641 : Blo 2189435 34178641 := bstep (se 2 (by rfl) ⟨12816990, by rfl⟩ : syracuseStep 34178641 = 25633981) B25633981
theorem B182286085 : Blo 2189435 182286085 := bstep (se 4 (by rfl) ⟨17089320, by rfl⟩ : syracuseStep 182286085 = 34178641) B34178641
theorem B243048113 : Blo 2189435 243048113 := bstep (se 2 (by rfl) ⟨91143042, by rfl⟩ : syracuseStep 243048113 = 182286085) B182286085
theorem B162032075 : Blo 2189435 162032075 := bstep (se 1 (by rfl) ⟨121524056, by rfl⟩ : syracuseStep 162032075 = 243048113) B243048113
theorem B108021383 : Blo 2189435 108021383 := bstep (se 1 (by rfl) ⟨81016037, by rfl⟩ : syracuseStep 108021383 = 162032075) B162032075
theorem B72014255 : Blo 2189435 72014255 := bstep (se 1 (by rfl) ⟨54010691, by rfl⟩ : syracuseStep 72014255 = 108021383) B108021383
theorem B48009503 : Blo 2189435 48009503 := bstep (se 1 (by rfl) ⟨36007127, by rfl⟩ : syracuseStep 48009503 = 72014255) B72014255
theorem B32006335 : Blo 2189435 32006335 := bstep (se 1 (by rfl) ⟨24004751, by rfl⟩ : syracuseStep 32006335 = 48009503) B48009503
theorem B42675113 : Blo 2189435 42675113 := bstep (se 2 (by rfl) ⟨16003167, by rfl⟩ : syracuseStep 42675113 = 32006335) B32006335
theorem B28450075 : Blo 2189435 28450075 := bstep (se 1 (by rfl) ⟨21337556, by rfl⟩ : syracuseStep 28450075 = 42675113) B42675113
theorem B37933433 : Blo 2189435 37933433 := bstep (se 2 (by rfl) ⟨14225037, by rfl⟩ : syracuseStep 37933433 = 28450075) B28450075
theorem B25288955 : Blo 2189435 25288955 := bstep (se 1 (by rfl) ⟨18966716, by rfl⟩ : syracuseStep 25288955 = 37933433) B37933433
theorem B16859303 : Blo 2189435 16859303 := bstep (se 1 (by rfl) ⟨12644477, by rfl⟩ : syracuseStep 16859303 = 25288955) B25288955
theorem B11239535 : Blo 2189435 11239535 := bstep (se 1 (by rfl) ⟨8429651, by rfl⟩ : syracuseStep 11239535 = 16859303) B16859303
theorem B7493023 : Blo 2189435 7493023 := bstep (se 1 (by rfl) ⟨5619767, by rfl⟩ : syracuseStep 7493023 = 11239535) B11239535
theorem B9990697 : Blo 2189435 9990697 := bstep (se 2 (by rfl) ⟨3746511, by rfl⟩ : syracuseStep 9990697 = 7493023) B7493023
theorem B13320929 : Blo 2189435 13320929 := bstep (se 2 (by rfl) ⟨4995348, by rfl⟩ : syracuseStep 13320929 = 9990697) B9990697
theorem B8880619 : Blo 2189435 8880619 := bstep (se 1 (by rfl) ⟨6660464, by rfl⟩ : syracuseStep 8880619 = 13320929) B13320929
theorem B11840825 : Blo 2189435 11840825 := bstep (se 2 (by rfl) ⟨4440309, by rfl⟩ : syracuseStep 11840825 = 8880619) B8880619
theorem B7893883 : Blo 2189435 7893883 := bstep (se 1 (by rfl) ⟨5920412, by rfl⟩ : syracuseStep 7893883 = 11840825) B11840825
theorem B10525177 : Blo 2189435 10525177 := bstep (se 2 (by rfl) ⟨3946941, by rfl⟩ : syracuseStep 10525177 = 7893883) B7893883
theorem B14033569 : Blo 2189435 14033569 := bstep (se 2 (by rfl) ⟨5262588, by rfl⟩ : syracuseStep 14033569 = 10525177) B10525177
theorem B18711425 : Blo 2189435 18711425 := bstep (se 2 (by rfl) ⟨7016784, by rfl⟩ : syracuseStep 18711425 = 14033569) B14033569
theorem B12474283 : Blo 2189435 12474283 := bstep (se 1 (by rfl) ⟨9355712, by rfl⟩ : syracuseStep 12474283 = 18711425) B18711425
theorem B16632377 : Blo 2189435 16632377 := bstep (se 2 (by rfl) ⟨6237141, by rfl⟩ : syracuseStep 16632377 = 12474283) B12474283
theorem B11088251 : Blo 2189435 11088251 := bstep (se 1 (by rfl) ⟨8316188, by rfl⟩ : syracuseStep 11088251 = 16632377) B16632377
theorem B7392167 : Blo 2189435 7392167 := bstep (se 1 (by rfl) ⟨5544125, by rfl⟩ : syracuseStep 7392167 = 11088251) B11088251
theorem B4928111 : Blo 2189435 4928111 := bstep (se 1 (by rfl) ⟨3696083, by rfl⟩ : syracuseStep 4928111 = 7392167) B7392167
theorem B3285407 : Blo 2189435 3285407 := bstep (se 1 (by rfl) ⟨2464055, by rfl⟩ : syracuseStep 3285407 = 4928111) B4928111
theorem B2190271 : Blo 2189435 2190271 := bstep (se 1 (by rfl) ⟨1642703, by rfl⟩ : syracuseStep 2190271 = 3285407) B3285407
theorem B3285413 : Blo 2189435 3285413 := bbase (se 4 (by rfl) ⟨308007, by rfl⟩ : syracuseStep 3285413 = 616015) (by norm_num)
theorem B2190275 : Blo 2189435 2190275 := bstep (se 1 (by rfl) ⟨1642706, by rfl⟩ : syracuseStep 2190275 = 3285413) B3285413
theorem B2772073 : Blo 2189435 2772073 := bbase (se 2 (by rfl) ⟨1039527, by rfl⟩ : syracuseStep 2772073 = 2079055) (by norm_num)
theorem B3696097 : Blo 2189435 3696097 := bstep (se 2 (by rfl) ⟨1386036, by rfl⟩ : syracuseStep 3696097 = 2772073) B2772073
theorem B4928129 : Blo 2189435 4928129 := bstep (se 2 (by rfl) ⟨1848048, by rfl⟩ : syracuseStep 4928129 = 3696097) B3696097
theorem B3285419 : Blo 2189435 3285419 := bstep (se 1 (by rfl) ⟨2464064, by rfl⟩ : syracuseStep 3285419 = 4928129) B4928129
theorem B2190279 : Blo 2189435 2190279 := bstep (se 1 (by rfl) ⟨1642709, by rfl⟩ : syracuseStep 2190279 = 3285419) B3285419
theorem B2464069 : Blo 2189435 2464069 := bbase (se 4 (by rfl) ⟨231006, by rfl⟩ : syracuseStep 2464069 = 462013) (by norm_num)
theorem B3285425 : Blo 2189435 3285425 := bstep (se 2 (by rfl) ⟨1232034, by rfl⟩ : syracuseStep 3285425 = 2464069) B2464069
theorem B2190283 : Blo 2189435 2190283 := bstep (se 1 (by rfl) ⟨1642712, by rfl⟩ : syracuseStep 2190283 = 3285425) B3285425
theorem B4158125 : Blo 2189435 4158125 := bbase (se 3 (by rfl) ⟨779648, by rfl⟩ : syracuseStep 4158125 = 1559297) (by norm_num)
theorem B2772083 : Blo 2189435 2772083 := bstep (se 1 (by rfl) ⟨2079062, by rfl⟩ : syracuseStep 2772083 = 4158125) B4158125
theorem B7392221 : Blo 2189435 7392221 := bstep (se 3 (by rfl) ⟨1386041, by rfl⟩ : syracuseStep 7392221 = 2772083) B2772083
theorem B4928147 : Blo 2189435 4928147 := bstep (se 1 (by rfl) ⟨3696110, by rfl⟩ : syracuseStep 4928147 = 7392221) B7392221
theorem B3285431 : Blo 2189435 3285431 := bstep (se 1 (by rfl) ⟨2464073, by rfl⟩ : syracuseStep 3285431 = 4928147) B4928147
theorem B2190287 : Blo 2189435 2190287 := bstep (se 1 (by rfl) ⟨1642715, by rfl⟩ : syracuseStep 2190287 = 3285431) B3285431
theorem B3285437 : Blo 2189435 3285437 := bbase (se 3 (by rfl) ⟨616019, by rfl⟩ : syracuseStep 3285437 = 1232039) (by norm_num)
theorem B2190291 : Blo 2189435 2190291 := bstep (se 1 (by rfl) ⟨1642718, by rfl⟩ : syracuseStep 2190291 = 3285437) B3285437
theorem B4928165 : Blo 2189435 4928165 := bbase (se 4 (by rfl) ⟨462015, by rfl⟩ : syracuseStep 4928165 = 924031) (by norm_num)
theorem B3285443 : Blo 2189435 3285443 := bstep (se 1 (by rfl) ⟨2464082, by rfl⟩ : syracuseStep 3285443 = 4928165) B4928165
theorem B2190295 : Blo 2189435 2190295 := bstep (se 1 (by rfl) ⟨1642721, by rfl⟩ : syracuseStep 2190295 = 3285443) B3285443
theorem B5544197 : Blo 2189435 5544197 := bbase (se 4 (by rfl) ⟨519768, by rfl⟩ : syracuseStep 5544197 = 1039537) (by norm_num)
theorem B3696131 : Blo 2189435 3696131 := bstep (se 1 (by rfl) ⟨2772098, by rfl⟩ : syracuseStep 3696131 = 5544197) B5544197
theorem B2464087 : Blo 2189435 2464087 := bstep (se 1 (by rfl) ⟨1848065, by rfl⟩ : syracuseStep 2464087 = 3696131) B3696131
theorem B3285449 : Blo 2189435 3285449 := bstep (se 2 (by rfl) ⟨1232043, by rfl⟩ : syracuseStep 3285449 = 2464087) B2464087
theorem B2190299 : Blo 2189435 2190299 := bstep (se 1 (by rfl) ⟨1642724, by rfl⟩ : syracuseStep 2190299 = 3285449) B3285449
theorem B4677925 : Blo 2189435 4677925 := bbase (se 4 (by rfl) ⟨438555, by rfl⟩ : syracuseStep 4677925 = 877111) (by norm_num)
theorem B6237233 : Blo 2189435 6237233 := bstep (se 2 (by rfl) ⟨2338962, by rfl⟩ : syracuseStep 6237233 = 4677925) B4677925
theorem B4158155 : Blo 2189435 4158155 := bstep (se 1 (by rfl) ⟨3118616, by rfl⟩ : syracuseStep 4158155 = 6237233) B6237233
theorem B11088413 : Blo 2189435 11088413 := bstep (se 3 (by rfl) ⟨2079077, by rfl⟩ : syracuseStep 11088413 = 4158155) B4158155
theorem B7392275 : Blo 2189435 7392275 := bstep (se 1 (by rfl) ⟨5544206, by rfl⟩ : syracuseStep 7392275 = 11088413) B11088413
theorem B4928183 : Blo 2189435 4928183 := bstep (se 1 (by rfl) ⟨3696137, by rfl⟩ : syracuseStep 4928183 = 7392275) B7392275
theorem B3285455 : Blo 2189435 3285455 := bstep (se 1 (by rfl) ⟨2464091, by rfl⟩ : syracuseStep 3285455 = 4928183) B4928183
theorem B2190303 : Blo 2189435 2190303 := bstep (se 1 (by rfl) ⟨1642727, by rfl⟩ : syracuseStep 2190303 = 3285455) B3285455
theorem B3285461 : Blo 2189435 3285461 := bbase (se 7 (by rfl) ⟨38501, by rfl⟩ : syracuseStep 3285461 = 77003) (by norm_num)
theorem B2190307 : Blo 2189435 2190307 := bstep (se 1 (by rfl) ⟨1642730, by rfl⟩ : syracuseStep 2190307 = 3285461) B3285461
theorem B8316341 : Blo 2189435 8316341 := bbase (se 5 (by rfl) ⟨389828, by rfl⟩ : syracuseStep 8316341 = 779657) (by norm_num)
theorem B5544227 : Blo 2189435 5544227 := bstep (se 1 (by rfl) ⟨4158170, by rfl⟩ : syracuseStep 5544227 = 8316341) B8316341
theorem B3696151 : Blo 2189435 3696151 := bstep (se 1 (by rfl) ⟨2772113, by rfl⟩ : syracuseStep 3696151 = 5544227) B5544227
theorem B4928201 : Blo 2189435 4928201 := bstep (se 2 (by rfl) ⟨1848075, by rfl⟩ : syracuseStep 4928201 = 3696151) B3696151
theorem B3285467 : Blo 2189435 3285467 := bstep (se 1 (by rfl) ⟨2464100, by rfl⟩ : syracuseStep 3285467 = 4928201) B4928201
theorem B2190311 : Blo 2189435 2190311 := bstep (se 1 (by rfl) ⟨1642733, by rfl⟩ : syracuseStep 2190311 = 3285467) B3285467
theorem B2464105 : Blo 2189435 2464105 := bbase (se 2 (by rfl) ⟨924039, by rfl⟩ : syracuseStep 2464105 = 1848079) (by norm_num)
theorem B3285473 : Blo 2189435 3285473 := bstep (se 2 (by rfl) ⟨1232052, by rfl⟩ : syracuseStep 3285473 = 2464105) B2464105
theorem B2190315 : Blo 2189435 2190315 := bstep (se 1 (by rfl) ⟨1642736, by rfl⟩ : syracuseStep 2190315 = 3285473) B3285473
theorem B3161189 : Blo 2189435 3161189 := bbase (se 4 (by rfl) ⟨296361, by rfl⟩ : syracuseStep 3161189 = 592723) (by norm_num)
theorem B8429837 : Blo 2189435 8429837 := bstep (se 3 (by rfl) ⟨1580594, by rfl⟩ : syracuseStep 8429837 = 3161189) B3161189
theorem B22479565 : Blo 2189435 22479565 := bstep (se 3 (by rfl) ⟨4214918, by rfl⟩ : syracuseStep 22479565 = 8429837) B8429837
theorem B29972753 : Blo 2189435 29972753 := bstep (se 2 (by rfl) ⟨11239782, by rfl⟩ : syracuseStep 29972753 = 22479565) B22479565
theorem B19981835 : Blo 2189435 19981835 := bstep (se 1 (by rfl) ⟨14986376, by rfl⟩ : syracuseStep 19981835 = 29972753) B29972753
theorem B13321223 : Blo 2189435 13321223 := bstep (se 1 (by rfl) ⟨9990917, by rfl⟩ : syracuseStep 13321223 = 19981835) B19981835
theorem B8880815 : Blo 2189435 8880815 := bstep (se 1 (by rfl) ⟨6660611, by rfl⟩ : syracuseStep 8880815 = 13321223) B13321223
theorem B5920543 : Blo 2189435 5920543 := bstep (se 1 (by rfl) ⟨4440407, by rfl⟩ : syracuseStep 5920543 = 8880815) B8880815
theorem B7894057 : Blo 2189435 7894057 := bstep (se 2 (by rfl) ⟨2960271, by rfl⟩ : syracuseStep 7894057 = 5920543) B5920543
theorem B10525409 : Blo 2189435 10525409 := bstep (se 2 (by rfl) ⟨3947028, by rfl⟩ : syracuseStep 10525409 = 7894057) B7894057
theorem B7016939 : Blo 2189435 7016939 := bstep (se 1 (by rfl) ⟨5262704, by rfl⟩ : syracuseStep 7016939 = 10525409) B10525409
theorem B4677959 : Blo 2189435 4677959 := bstep (se 1 (by rfl) ⟨3508469, by rfl⟩ : syracuseStep 4677959 = 7016939) B7016939
theorem B12474557 : Blo 2189435 12474557 := bstep (se 3 (by rfl) ⟨2338979, by rfl⟩ : syracuseStep 12474557 = 4677959) B4677959
theorem B8316371 : Blo 2189435 8316371 := bstep (se 1 (by rfl) ⟨6237278, by rfl⟩ : syracuseStep 8316371 = 12474557) B12474557
theorem B5544247 : Blo 2189435 5544247 := bstep (se 1 (by rfl) ⟨4158185, by rfl⟩ : syracuseStep 5544247 = 8316371) B8316371
theorem B7392329 : Blo 2189435 7392329 := bstep (se 2 (by rfl) ⟨2772123, by rfl⟩ : syracuseStep 7392329 = 5544247) B5544247
theorem B4928219 : Blo 2189435 4928219 := bstep (se 1 (by rfl) ⟨3696164, by rfl⟩ : syracuseStep 4928219 = 7392329) B7392329
theorem B3285479 : Blo 2189435 3285479 := bstep (se 1 (by rfl) ⟨2464109, by rfl⟩ : syracuseStep 3285479 = 4928219) B4928219
theorem B2190319 : Blo 2189435 2190319 := bstep (se 1 (by rfl) ⟨1642739, by rfl⟩ : syracuseStep 2190319 = 3285479) B3285479
theorem B3285485 : Blo 2189435 3285485 := bbase (se 3 (by rfl) ⟨616028, by rfl⟩ : syracuseStep 3285485 = 1232057) (by norm_num)
theorem B2190323 : Blo 2189435 2190323 := bstep (se 1 (by rfl) ⟨1642742, by rfl⟩ : syracuseStep 2190323 = 3285485) B3285485
theorem B4928237 : Blo 2189435 4928237 := bbase (se 3 (by rfl) ⟨924044, by rfl⟩ : syracuseStep 4928237 = 1848089) (by norm_num)
theorem B3285491 : Blo 2189435 3285491 := bstep (se 1 (by rfl) ⟨2464118, by rfl⟩ : syracuseStep 3285491 = 4928237) B4928237
theorem B2190327 : Blo 2189435 2190327 := bstep (se 1 (by rfl) ⟨1642745, by rfl⟩ : syracuseStep 2190327 = 3285491) B3285491
theorem B2338993 : Blo 2189435 2338993 := bbase (se 2 (by rfl) ⟨877122, by rfl⟩ : syracuseStep 2338993 = 1754245) (by norm_num)
theorem B3118657 : Blo 2189435 3118657 := bstep (se 2 (by rfl) ⟨1169496, by rfl⟩ : syracuseStep 3118657 = 2338993) B2338993
theorem B4158209 : Blo 2189435 4158209 := bstep (se 2 (by rfl) ⟨1559328, by rfl⟩ : syracuseStep 4158209 = 3118657) B3118657
theorem B2772139 : Blo 2189435 2772139 := bstep (se 1 (by rfl) ⟨2079104, by rfl⟩ : syracuseStep 2772139 = 4158209) B4158209
theorem B3696185 : Blo 2189435 3696185 := bstep (se 2 (by rfl) ⟨1386069, by rfl⟩ : syracuseStep 3696185 = 2772139) B2772139
theorem B2464123 : Blo 2189435 2464123 := bstep (se 1 (by rfl) ⟨1848092, by rfl⟩ : syracuseStep 2464123 = 3696185) B3696185
theorem B3285497 : Blo 2189435 3285497 := bstep (se 2 (by rfl) ⟨1232061, by rfl⟩ : syracuseStep 3285497 = 2464123) B2464123
theorem B2190331 : Blo 2189435 2190331 := bstep (se 1 (by rfl) ⟨1642748, by rfl⟩ : syracuseStep 2190331 = 3285497) B3285497
theorem B7407845 : Blo 2189435 7407845 := bbase (se 4 (by rfl) ⟨694485, by rfl⟩ : syracuseStep 7407845 = 1388971) (by norm_num)
theorem B4938563 : Blo 2189435 4938563 := bstep (se 1 (by rfl) ⟨3703922, by rfl⟩ : syracuseStep 4938563 = 7407845) B7407845
theorem B3292375 : Blo 2189435 3292375 := bstep (se 1 (by rfl) ⟨2469281, by rfl⟩ : syracuseStep 3292375 = 4938563) B4938563
theorem B4389833 : Blo 2189435 4389833 := bstep (se 2 (by rfl) ⟨1646187, by rfl⟩ : syracuseStep 4389833 = 3292375) B3292375
theorem B11706221 : Blo 2189435 11706221 := bstep (se 3 (by rfl) ⟨2194916, by rfl⟩ : syracuseStep 11706221 = 4389833) B4389833
theorem B7804147 : Blo 2189435 7804147 := bstep (se 1 (by rfl) ⟨5853110, by rfl⟩ : syracuseStep 7804147 = 11706221) B11706221
theorem B10405529 : Blo 2189435 10405529 := bstep (se 2 (by rfl) ⟨3902073, by rfl⟩ : syracuseStep 10405529 = 7804147) B7804147
theorem B6937019 : Blo 2189435 6937019 := bstep (se 1 (by rfl) ⟨5202764, by rfl⟩ : syracuseStep 6937019 = 10405529) B10405529
theorem B4624679 : Blo 2189435 4624679 := bstep (se 1 (by rfl) ⟨3468509, by rfl⟩ : syracuseStep 4624679 = 6937019) B6937019
theorem B3083119 : Blo 2189435 3083119 := bstep (se 1 (by rfl) ⟨2312339, by rfl⟩ : syracuseStep 3083119 = 4624679) B4624679
theorem B65773205 : Blo 2189435 65773205 := bstep (se 6 (by rfl) ⟨1541559, by rfl⟩ : syracuseStep 65773205 = 3083119) B3083119
theorem B43848803 : Blo 2189435 43848803 := bstep (se 1 (by rfl) ⟨32886602, by rfl⟩ : syracuseStep 43848803 = 65773205) B65773205
theorem B29232535 : Blo 2189435 29232535 := bstep (se 1 (by rfl) ⟨21924401, by rfl⟩ : syracuseStep 29232535 = 43848803) B43848803
theorem B38976713 : Blo 2189435 38976713 := bstep (se 2 (by rfl) ⟨14616267, by rfl⟩ : syracuseStep 38976713 = 29232535) B29232535
theorem B25984475 : Blo 2189435 25984475 := bstep (se 1 (by rfl) ⟨19488356, by rfl⟩ : syracuseStep 25984475 = 38976713) B38976713
theorem B17322983 : Blo 2189435 17322983 := bstep (se 1 (by rfl) ⟨12992237, by rfl⟩ : syracuseStep 17322983 = 25984475) B25984475
theorem B11548655 : Blo 2189435 11548655 := bstep (se 1 (by rfl) ⟨8661491, by rfl⟩ : syracuseStep 11548655 = 17322983) B17322983
theorem B7699103 : Blo 2189435 7699103 := bstep (se 1 (by rfl) ⟨5774327, by rfl⟩ : syracuseStep 7699103 = 11548655) B11548655
theorem B5132735 : Blo 2189435 5132735 := bstep (se 1 (by rfl) ⟨3849551, by rfl⟩ : syracuseStep 5132735 = 7699103) B7699103
theorem B3421823 : Blo 2189435 3421823 := bstep (se 1 (by rfl) ⟨2566367, by rfl⟩ : syracuseStep 3421823 = 5132735) B5132735
theorem B9124861 : Blo 2189435 9124861 := bstep (se 3 (by rfl) ⟨1710911, by rfl⟩ : syracuseStep 9124861 = 3421823) B3421823
theorem B12166481 : Blo 2189435 12166481 := bstep (se 2 (by rfl) ⟨4562430, by rfl⟩ : syracuseStep 12166481 = 9124861) B9124861
theorem B32443949 : Blo 2189435 32443949 := bstep (se 3 (by rfl) ⟨6083240, by rfl⟩ : syracuseStep 32443949 = 12166481) B12166481
theorem B86517197 : Blo 2189435 86517197 := bstep (se 3 (by rfl) ⟨16221974, by rfl⟩ : syracuseStep 86517197 = 32443949) B32443949
theorem B57678131 : Blo 2189435 57678131 := bstep (se 1 (by rfl) ⟨43258598, by rfl⟩ : syracuseStep 57678131 = 86517197) B86517197
theorem B38452087 : Blo 2189435 38452087 := bstep (se 1 (by rfl) ⟨28839065, by rfl⟩ : syracuseStep 38452087 = 57678131) B57678131
theorem B51269449 : Blo 2189435 51269449 := bstep (se 2 (by rfl) ⟨19226043, by rfl⟩ : syracuseStep 51269449 = 38452087) B38452087
theorem B68359265 : Blo 2189435 68359265 := bstep (se 2 (by rfl) ⟨25634724, by rfl⟩ : syracuseStep 68359265 = 51269449) B51269449
theorem B45572843 : Blo 2189435 45572843 := bstep (se 1 (by rfl) ⟨34179632, by rfl⟩ : syracuseStep 45572843 = 68359265) B68359265
theorem B30381895 : Blo 2189435 30381895 := bstep (se 1 (by rfl) ⟨22786421, by rfl⟩ : syracuseStep 30381895 = 45572843) B45572843
theorem B40509193 : Blo 2189435 40509193 := bstep (se 2 (by rfl) ⟨15190947, by rfl⟩ : syracuseStep 40509193 = 30381895) B30381895
theorem B54012257 : Blo 2189435 54012257 := bstep (se 2 (by rfl) ⟨20254596, by rfl⟩ : syracuseStep 54012257 = 40509193) B40509193
theorem B36008171 : Blo 2189435 36008171 := bstep (se 1 (by rfl) ⟨27006128, by rfl⟩ : syracuseStep 36008171 = 54012257) B54012257
theorem B24005447 : Blo 2189435 24005447 := bstep (se 1 (by rfl) ⟨18004085, by rfl⟩ : syracuseStep 24005447 = 36008171) B36008171
theorem B16003631 : Blo 2189435 16003631 := bstep (se 1 (by rfl) ⟨12002723, by rfl⟩ : syracuseStep 16003631 = 24005447) B24005447
theorem B10669087 : Blo 2189435 10669087 := bstep (se 1 (by rfl) ⟨8001815, by rfl⟩ : syracuseStep 10669087 = 16003631) B16003631
theorem B56901797 : Blo 2189435 56901797 := bstep (se 4 (by rfl) ⟨5334543, by rfl⟩ : syracuseStep 56901797 = 10669087) B10669087
theorem B37934531 : Blo 2189435 37934531 := bstep (se 1 (by rfl) ⟨28450898, by rfl⟩ : syracuseStep 37934531 = 56901797) B56901797
theorem B25289687 : Blo 2189435 25289687 := bstep (se 1 (by rfl) ⟨18967265, by rfl⟩ : syracuseStep 25289687 = 37934531) B37934531
theorem B16859791 : Blo 2189435 16859791 := bstep (se 1 (by rfl) ⟨12644843, by rfl⟩ : syracuseStep 16859791 = 25289687) B25289687
theorem B89918885 : Blo 2189435 89918885 := bstep (se 4 (by rfl) ⟨8429895, by rfl⟩ : syracuseStep 89918885 = 16859791) B16859791
theorem B59945923 : Blo 2189435 59945923 := bstep (se 1 (by rfl) ⟨44959442, by rfl⟩ : syracuseStep 59945923 = 89918885) B89918885
theorem B79927897 : Blo 2189435 79927897 := bstep (se 2 (by rfl) ⟨29972961, by rfl⟩ : syracuseStep 79927897 = 59945923) B59945923
theorem B106570529 : Blo 2189435 106570529 := bstep (se 2 (by rfl) ⟨39963948, by rfl⟩ : syracuseStep 106570529 = 79927897) B79927897
theorem B71047019 : Blo 2189435 71047019 := bstep (se 1 (by rfl) ⟨53285264, by rfl⟩ : syracuseStep 71047019 = 106570529) B106570529
theorem B47364679 : Blo 2189435 47364679 := bstep (se 1 (by rfl) ⟨35523509, by rfl⟩ : syracuseStep 47364679 = 71047019) B71047019
theorem B63152905 : Blo 2189435 63152905 := bstep (se 2 (by rfl) ⟨23682339, by rfl⟩ : syracuseStep 63152905 = 47364679) B47364679
theorem B84203873 : Blo 2189435 84203873 := bstep (se 2 (by rfl) ⟨31576452, by rfl⟩ : syracuseStep 84203873 = 63152905) B63152905
theorem B56135915 : Blo 2189435 56135915 := bstep (se 1 (by rfl) ⟨42101936, by rfl⟩ : syracuseStep 56135915 = 84203873) B84203873
theorem B37423943 : Blo 2189435 37423943 := bstep (se 1 (by rfl) ⟨28067957, by rfl⟩ : syracuseStep 37423943 = 56135915) B56135915
theorem B24949295 : Blo 2189435 24949295 := bstep (se 1 (by rfl) ⟨18711971, by rfl⟩ : syracuseStep 24949295 = 37423943) B37423943
theorem B16632863 : Blo 2189435 16632863 := bstep (se 1 (by rfl) ⟨12474647, by rfl⟩ : syracuseStep 16632863 = 24949295) B24949295
theorem B11088575 : Blo 2189435 11088575 := bstep (se 1 (by rfl) ⟨8316431, by rfl⟩ : syracuseStep 11088575 = 16632863) B16632863
theorem B7392383 : Blo 2189435 7392383 := bstep (se 1 (by rfl) ⟨5544287, by rfl⟩ : syracuseStep 7392383 = 11088575) B11088575
theorem B4928255 : Blo 2189435 4928255 := bstep (se 1 (by rfl) ⟨3696191, by rfl⟩ : syracuseStep 4928255 = 7392383) B7392383
theorem B3285503 : Blo 2189435 3285503 := bstep (se 1 (by rfl) ⟨2464127, by rfl⟩ : syracuseStep 3285503 = 4928255) B4928255
theorem B2190335 : Blo 2189435 2190335 := bstep (se 1 (by rfl) ⟨1642751, by rfl⟩ : syracuseStep 2190335 = 3285503) B3285503
theorem B3285509 : Blo 2189435 3285509 := bbase (se 4 (by rfl) ⟨308016, by rfl⟩ : syracuseStep 3285509 = 616033) (by norm_num)
theorem B2190339 : Blo 2189435 2190339 := bstep (se 1 (by rfl) ⟨1642754, by rfl⟩ : syracuseStep 2190339 = 3285509) B3285509
theorem B3696205 : Blo 2189435 3696205 := bbase (se 3 (by rfl) ⟨693038, by rfl⟩ : syracuseStep 3696205 = 1386077) (by norm_num)
theorem B4928273 : Blo 2189435 4928273 := bstep (se 2 (by rfl) ⟨1848102, by rfl⟩ : syracuseStep 4928273 = 3696205) B3696205
theorem B3285515 : Blo 2189435 3285515 := bstep (se 1 (by rfl) ⟨2464136, by rfl⟩ : syracuseStep 3285515 = 4928273) B4928273
theorem B2190343 : Blo 2189435 2190343 := bstep (se 1 (by rfl) ⟨1642757, by rfl⟩ : syracuseStep 2190343 = 3285515) B3285515
theorem B2464141 : Blo 2189435 2464141 := bbase (se 3 (by rfl) ⟨462026, by rfl⟩ : syracuseStep 2464141 = 924053) (by norm_num)
theorem B3285521 : Blo 2189435 3285521 := bstep (se 2 (by rfl) ⟨1232070, by rfl⟩ : syracuseStep 3285521 = 2464141) B2464141
theorem B2190347 : Blo 2189435 2190347 := bstep (se 1 (by rfl) ⟨1642760, by rfl⟩ : syracuseStep 2190347 = 3285521) B3285521
theorem B7392437 : Blo 2189435 7392437 := bbase (se 5 (by rfl) ⟨346520, by rfl⟩ : syracuseStep 7392437 = 693041) (by norm_num)
theorem B4928291 : Blo 2189435 4928291 := bstep (se 1 (by rfl) ⟨3696218, by rfl⟩ : syracuseStep 4928291 = 7392437) B7392437
theorem B3285527 : Blo 2189435 3285527 := bstep (se 1 (by rfl) ⟨2464145, by rfl⟩ : syracuseStep 3285527 = 4928291) B4928291
theorem B2190351 : Blo 2189435 2190351 := bstep (se 1 (by rfl) ⟨1642763, by rfl⟩ : syracuseStep 2190351 = 3285527) B3285527
theorem B3285533 : Blo 2189435 3285533 := bbase (se 3 (by rfl) ⟨616037, by rfl⟩ : syracuseStep 3285533 = 1232075) (by norm_num)
theorem B2190355 : Blo 2189435 2190355 := bstep (se 1 (by rfl) ⟨1642766, by rfl⟩ : syracuseStep 2190355 = 3285533) B3285533
theorem B4928309 : Blo 2189435 4928309 := bbase (se 5 (by rfl) ⟨231014, by rfl⟩ : syracuseStep 4928309 = 462029) (by norm_num)
theorem B3285539 : Blo 2189435 3285539 := bstep (se 1 (by rfl) ⟨2464154, by rfl⟩ : syracuseStep 3285539 = 4928309) B4928309
theorem B2190359 : Blo 2189435 2190359 := bstep (se 1 (by rfl) ⟨1642769, by rfl⟩ : syracuseStep 2190359 = 3285539) B3285539
theorem B10525621 : Blo 2189435 10525621 := bbase (se 5 (by rfl) ⟨493388, by rfl⟩ : syracuseStep 10525621 = 986777) (by norm_num)
theorem B14034161 : Blo 2189435 14034161 := bstep (se 2 (by rfl) ⟨5262810, by rfl⟩ : syracuseStep 14034161 = 10525621) B10525621
theorem B9356107 : Blo 2189435 9356107 := bstep (se 1 (by rfl) ⟨7017080, by rfl⟩ : syracuseStep 9356107 = 14034161) B14034161
theorem B12474809 : Blo 2189435 12474809 := bstep (se 2 (by rfl) ⟨4678053, by rfl⟩ : syracuseStep 12474809 = 9356107) B9356107
theorem B8316539 : Blo 2189435 8316539 := bstep (se 1 (by rfl) ⟨6237404, by rfl⟩ : syracuseStep 8316539 = 12474809) B12474809
theorem B5544359 : Blo 2189435 5544359 := bstep (se 1 (by rfl) ⟨4158269, by rfl⟩ : syracuseStep 5544359 = 8316539) B8316539
theorem B3696239 : Blo 2189435 3696239 := bstep (se 1 (by rfl) ⟨2772179, by rfl⟩ : syracuseStep 3696239 = 5544359) B5544359
theorem B2464159 : Blo 2189435 2464159 := bstep (se 1 (by rfl) ⟨1848119, by rfl⟩ : syracuseStep 2464159 = 3696239) B3696239
theorem B3285545 : Blo 2189435 3285545 := bstep (se 2 (by rfl) ⟨1232079, by rfl⟩ : syracuseStep 3285545 = 2464159) B2464159
theorem B2190363 : Blo 2189435 2190363 := bstep (se 1 (by rfl) ⟨1642772, by rfl⟩ : syracuseStep 2190363 = 3285545) B3285545
theorem B2848345 : Blo 2189435 2848345 := bbase (se 2 (by rfl) ⟨1068129, by rfl⟩ : syracuseStep 2848345 = 2136259) (by norm_num)
theorem B15191173 : Blo 2189435 15191173 := bstep (se 4 (by rfl) ⟨1424172, by rfl⟩ : syracuseStep 15191173 = 2848345) B2848345
theorem B20254897 : Blo 2189435 20254897 := bstep (se 2 (by rfl) ⟨7595586, by rfl⟩ : syracuseStep 20254897 = 15191173) B15191173
theorem B27006529 : Blo 2189435 27006529 := bstep (se 2 (by rfl) ⟨10127448, by rfl⟩ : syracuseStep 27006529 = 20254897) B20254897
theorem B36008705 : Blo 2189435 36008705 := bstep (se 2 (by rfl) ⟨13503264, by rfl⟩ : syracuseStep 36008705 = 27006529) B27006529
theorem B24005803 : Blo 2189435 24005803 := bstep (se 1 (by rfl) ⟨18004352, by rfl⟩ : syracuseStep 24005803 = 36008705) B36008705
theorem B32007737 : Blo 2189435 32007737 := bstep (se 2 (by rfl) ⟨12002901, by rfl⟩ : syracuseStep 32007737 = 24005803) B24005803
theorem B21338491 : Blo 2189435 21338491 := bstep (se 1 (by rfl) ⟨16003868, by rfl⟩ : syracuseStep 21338491 = 32007737) B32007737
theorem B28451321 : Blo 2189435 28451321 := bstep (se 2 (by rfl) ⟨10669245, by rfl⟩ : syracuseStep 28451321 = 21338491) B21338491
theorem B18967547 : Blo 2189435 18967547 := bstep (se 1 (by rfl) ⟨14225660, by rfl⟩ : syracuseStep 18967547 = 28451321) B28451321
theorem B50580125 : Blo 2189435 50580125 := bstep (se 3 (by rfl) ⟨9483773, by rfl⟩ : syracuseStep 50580125 = 18967547) B18967547
theorem B33720083 : Blo 2189435 33720083 := bstep (se 1 (by rfl) ⟨25290062, by rfl⟩ : syracuseStep 33720083 = 50580125) B50580125
theorem B22480055 : Blo 2189435 22480055 := bstep (se 1 (by rfl) ⟨16860041, by rfl⟩ : syracuseStep 22480055 = 33720083) B33720083
theorem B14986703 : Blo 2189435 14986703 := bstep (se 1 (by rfl) ⟨11240027, by rfl⟩ : syracuseStep 14986703 = 22480055) B22480055
theorem B9991135 : Blo 2189435 9991135 := bstep (se 1 (by rfl) ⟨7493351, by rfl⟩ : syracuseStep 9991135 = 14986703) B14986703
theorem B13321513 : Blo 2189435 13321513 := bstep (se 2 (by rfl) ⟨4995567, by rfl⟩ : syracuseStep 13321513 = 9991135) B9991135
theorem B17762017 : Blo 2189435 17762017 := bstep (se 2 (by rfl) ⟨6660756, by rfl⟩ : syracuseStep 17762017 = 13321513) B13321513
theorem B23682689 : Blo 2189435 23682689 := bstep (se 2 (by rfl) ⟨8881008, by rfl⟩ : syracuseStep 23682689 = 17762017) B17762017
theorem B15788459 : Blo 2189435 15788459 := bstep (se 1 (by rfl) ⟨11841344, by rfl⟩ : syracuseStep 15788459 = 23682689) B23682689
theorem B10525639 : Blo 2189435 10525639 := bstep (se 1 (by rfl) ⟨7894229, by rfl⟩ : syracuseStep 10525639 = 15788459) B15788459
theorem B14034185 : Blo 2189435 14034185 := bstep (se 2 (by rfl) ⟨5262819, by rfl⟩ : syracuseStep 14034185 = 10525639) B10525639
theorem B9356123 : Blo 2189435 9356123 := bstep (se 1 (by rfl) ⟨7017092, by rfl⟩ : syracuseStep 9356123 = 14034185) B14034185
theorem B6237415 : Blo 2189435 6237415 := bstep (se 1 (by rfl) ⟨4678061, by rfl⟩ : syracuseStep 6237415 = 9356123) B9356123
theorem B8316553 : Blo 2189435 8316553 := bstep (se 2 (by rfl) ⟨3118707, by rfl⟩ : syracuseStep 8316553 = 6237415) B6237415
theorem B11088737 : Blo 2189435 11088737 := bstep (se 2 (by rfl) ⟨4158276, by rfl⟩ : syracuseStep 11088737 = 8316553) B8316553
theorem B7392491 : Blo 2189435 7392491 := bstep (se 1 (by rfl) ⟨5544368, by rfl⟩ : syracuseStep 7392491 = 11088737) B11088737
theorem B4928327 : Blo 2189435 4928327 := bstep (se 1 (by rfl) ⟨3696245, by rfl⟩ : syracuseStep 4928327 = 7392491) B7392491
theorem B3285551 : Blo 2189435 3285551 := bstep (se 1 (by rfl) ⟨2464163, by rfl⟩ : syracuseStep 3285551 = 4928327) B4928327
theorem B2190367 : Blo 2189435 2190367 := bstep (se 1 (by rfl) ⟨1642775, by rfl⟩ : syracuseStep 2190367 = 3285551) B3285551
theorem B3285557 : Blo 2189435 3285557 := bbase (se 5 (by rfl) ⟨154010, by rfl⟩ : syracuseStep 3285557 = 308021) (by norm_num)
theorem B2190371 : Blo 2189435 2190371 := bstep (se 1 (by rfl) ⟨1642778, by rfl⟩ : syracuseStep 2190371 = 3285557) B3285557
theorem B5544389 : Blo 2189435 5544389 := bbase (se 4 (by rfl) ⟨519786, by rfl⟩ : syracuseStep 5544389 = 1039573) (by norm_num)
theorem B3696259 : Blo 2189435 3696259 := bstep (se 1 (by rfl) ⟨2772194, by rfl⟩ : syracuseStep 3696259 = 5544389) B5544389
theorem B4928345 : Blo 2189435 4928345 := bstep (se 2 (by rfl) ⟨1848129, by rfl⟩ : syracuseStep 4928345 = 3696259) B3696259
theorem B3285563 : Blo 2189435 3285563 := bstep (se 1 (by rfl) ⟨2464172, by rfl⟩ : syracuseStep 3285563 = 4928345) B4928345
theorem B2190375 : Blo 2189435 2190375 := bstep (se 1 (by rfl) ⟨1642781, by rfl⟩ : syracuseStep 2190375 = 3285563) B3285563
theorem B2464177 : Blo 2189435 2464177 := bbase (se 2 (by rfl) ⟨924066, by rfl⟩ : syracuseStep 2464177 = 1848133) (by norm_num)
theorem B3285569 : Blo 2189435 3285569 := bstep (se 2 (by rfl) ⟨1232088, by rfl⟩ : syracuseStep 3285569 = 2464177) B2464177
theorem B2190379 : Blo 2189435 2190379 := bstep (se 1 (by rfl) ⟨1642784, by rfl⟩ : syracuseStep 2190379 = 3285569) B3285569
theorem B6237461 : Blo 2189435 6237461 := bbase (se 6 (by rfl) ⟨146190, by rfl⟩ : syracuseStep 6237461 = 292381) (by norm_num)
theorem B4158307 : Blo 2189435 4158307 := bstep (se 1 (by rfl) ⟨3118730, by rfl⟩ : syracuseStep 4158307 = 6237461) B6237461
theorem B5544409 : Blo 2189435 5544409 := bstep (se 2 (by rfl) ⟨2079153, by rfl⟩ : syracuseStep 5544409 = 4158307) B4158307
theorem B7392545 : Blo 2189435 7392545 := bstep (se 2 (by rfl) ⟨2772204, by rfl⟩ : syracuseStep 7392545 = 5544409) B5544409
theorem B4928363 : Blo 2189435 4928363 := bstep (se 1 (by rfl) ⟨3696272, by rfl⟩ : syracuseStep 4928363 = 7392545) B7392545
theorem B3285575 : Blo 2189435 3285575 := bstep (se 1 (by rfl) ⟨2464181, by rfl⟩ : syracuseStep 3285575 = 4928363) B4928363
theorem B2190383 : Blo 2189435 2190383 := bstep (se 1 (by rfl) ⟨1642787, by rfl⟩ : syracuseStep 2190383 = 3285575) B3285575
theorem B3285581 : Blo 2189435 3285581 := bbase (se 3 (by rfl) ⟨616046, by rfl⟩ : syracuseStep 3285581 = 1232093) (by norm_num)
theorem B2190387 : Blo 2189435 2190387 := bstep (se 1 (by rfl) ⟨1642790, by rfl⟩ : syracuseStep 2190387 = 3285581) B3285581
theorem B4928381 : Blo 2189435 4928381 := bbase (se 3 (by rfl) ⟨924071, by rfl⟩ : syracuseStep 4928381 = 1848143) (by norm_num)
theorem B3285587 : Blo 2189435 3285587 := bstep (se 1 (by rfl) ⟨2464190, by rfl⟩ : syracuseStep 3285587 = 4928381) B4928381
theorem B2190391 : Blo 2189435 2190391 := bstep (se 1 (by rfl) ⟨1642793, by rfl⟩ : syracuseStep 2190391 = 3285587) B3285587
theorem B3696293 : Blo 2189435 3696293 := bbase (se 4 (by rfl) ⟨346527, by rfl⟩ : syracuseStep 3696293 = 693055) (by norm_num)
theorem B2464195 : Blo 2189435 2464195 := bstep (se 1 (by rfl) ⟨1848146, by rfl⟩ : syracuseStep 2464195 = 3696293) B3696293
theorem B3285593 : Blo 2189435 3285593 := bstep (se 2 (by rfl) ⟨1232097, by rfl⟩ : syracuseStep 3285593 = 2464195) B2464195
theorem B2190395 : Blo 2189435 2190395 := bstep (se 1 (by rfl) ⟨1642796, by rfl⟩ : syracuseStep 2190395 = 3285593) B3285593
theorem B2339065 : Blo 2189435 2339065 := bbase (se 2 (by rfl) ⟨877149, by rfl⟩ : syracuseStep 2339065 = 1754299) (by norm_num)
theorem B3118753 : Blo 2189435 3118753 := bstep (se 2 (by rfl) ⟨1169532, by rfl⟩ : syracuseStep 3118753 = 2339065) B2339065
theorem B16633349 : Blo 2189435 16633349 := bstep (se 4 (by rfl) ⟨1559376, by rfl⟩ : syracuseStep 16633349 = 3118753) B3118753
theorem B11088899 : Blo 2189435 11088899 := bstep (se 1 (by rfl) ⟨8316674, by rfl⟩ : syracuseStep 11088899 = 16633349) B16633349
theorem B7392599 : Blo 2189435 7392599 := bstep (se 1 (by rfl) ⟨5544449, by rfl⟩ : syracuseStep 7392599 = 11088899) B11088899
theorem B4928399 : Blo 2189435 4928399 := bstep (se 1 (by rfl) ⟨3696299, by rfl⟩ : syracuseStep 4928399 = 7392599) B7392599
theorem B3285599 : Blo 2189435 3285599 := bstep (se 1 (by rfl) ⟨2464199, by rfl⟩ : syracuseStep 3285599 = 4928399) B4928399
theorem B2190399 : Blo 2189435 2190399 := bstep (se 1 (by rfl) ⟨1642799, by rfl⟩ : syracuseStep 2190399 = 3285599) B3285599
theorem B3285605 : Blo 2189435 3285605 := bbase (se 4 (by rfl) ⟨308025, by rfl⟩ : syracuseStep 3285605 = 616051) (by norm_num)
theorem B2190403 : Blo 2189435 2190403 := bstep (se 1 (by rfl) ⟨1642802, by rfl⟩ : syracuseStep 2190403 = 3285605) B3285605
theorem B3118765 : Blo 2189435 3118765 := bbase (se 3 (by rfl) ⟨584768, by rfl⟩ : syracuseStep 3118765 = 1169537) (by norm_num)
theorem B4158353 : Blo 2189435 4158353 := bstep (se 2 (by rfl) ⟨1559382, by rfl⟩ : syracuseStep 4158353 = 3118765) B3118765
theorem B2772235 : Blo 2189435 2772235 := bstep (se 1 (by rfl) ⟨2079176, by rfl⟩ : syracuseStep 2772235 = 4158353) B4158353
theorem B3696313 : Blo 2189435 3696313 := bstep (se 2 (by rfl) ⟨1386117, by rfl⟩ : syracuseStep 3696313 = 2772235) B2772235
theorem B4928417 : Blo 2189435 4928417 := bstep (se 2 (by rfl) ⟨1848156, by rfl⟩ : syracuseStep 4928417 = 3696313) B3696313
theorem B3285611 : Blo 2189435 3285611 := bstep (se 1 (by rfl) ⟨2464208, by rfl⟩ : syracuseStep 3285611 = 4928417) B4928417
theorem B2190407 : Blo 2189435 2190407 := bstep (se 1 (by rfl) ⟨1642805, by rfl⟩ : syracuseStep 2190407 = 3285611) B3285611
theorem B2464213 : Blo 2189435 2464213 := bbase (se 7 (by rfl) ⟨28877, by rfl⟩ : syracuseStep 2464213 = 57755) (by norm_num)
theorem B3285617 : Blo 2189435 3285617 := bstep (se 2 (by rfl) ⟨1232106, by rfl⟩ : syracuseStep 3285617 = 2464213) B2464213
theorem B2190411 : Blo 2189435 2190411 := bstep (se 1 (by rfl) ⟨1642808, by rfl⟩ : syracuseStep 2190411 = 3285617) B3285617
theorem B2772245 : Blo 2189435 2772245 := bbase (se 6 (by rfl) ⟨64974, by rfl⟩ : syracuseStep 2772245 = 129949) (by norm_num)
theorem B7392653 : Blo 2189435 7392653 := bstep (se 3 (by rfl) ⟨1386122, by rfl⟩ : syracuseStep 7392653 = 2772245) B2772245
theorem B4928435 : Blo 2189435 4928435 := bstep (se 1 (by rfl) ⟨3696326, by rfl⟩ : syracuseStep 4928435 = 7392653) B7392653
theorem B3285623 : Blo 2189435 3285623 := bstep (se 1 (by rfl) ⟨2464217, by rfl⟩ : syracuseStep 3285623 = 4928435) B4928435
theorem B2190415 : Blo 2189435 2190415 := bstep (se 1 (by rfl) ⟨1642811, by rfl⟩ : syracuseStep 2190415 = 3285623) B3285623
theorem B3285629 : Blo 2189435 3285629 := bbase (se 3 (by rfl) ⟨616055, by rfl⟩ : syracuseStep 3285629 = 1232111) (by norm_num)
theorem B2190419 : Blo 2189435 2190419 := bstep (se 1 (by rfl) ⟨1642814, by rfl⟩ : syracuseStep 2190419 = 3285629) B3285629
theorem B4928453 : Blo 2189435 4928453 := bbase (se 4 (by rfl) ⟨462042, by rfl⟩ : syracuseStep 4928453 = 924085) (by norm_num)
theorem B3285635 : Blo 2189435 3285635 := bstep (se 1 (by rfl) ⟨2464226, by rfl⟩ : syracuseStep 3285635 = 4928453) B4928453
theorem B2190423 : Blo 2189435 2190423 := bstep (se 1 (by rfl) ⟨1642817, by rfl⟩ : syracuseStep 2190423 = 3285635) B3285635
theorem B5262965 : Blo 2189435 5262965 := bbase (se 5 (by rfl) ⟨246701, by rfl⟩ : syracuseStep 5262965 = 493403) (by norm_num)
theorem B3508643 : Blo 2189435 3508643 := bstep (se 1 (by rfl) ⟨2631482, by rfl⟩ : syracuseStep 3508643 = 5262965) B5262965
theorem B9356381 : Blo 2189435 9356381 := bstep (se 3 (by rfl) ⟨1754321, by rfl⟩ : syracuseStep 9356381 = 3508643) B3508643
theorem B6237587 : Blo 2189435 6237587 := bstep (se 1 (by rfl) ⟨4678190, by rfl⟩ : syracuseStep 6237587 = 9356381) B9356381
theorem B4158391 : Blo 2189435 4158391 := bstep (se 1 (by rfl) ⟨3118793, by rfl⟩ : syracuseStep 4158391 = 6237587) B6237587
theorem B5544521 : Blo 2189435 5544521 := bstep (se 2 (by rfl) ⟨2079195, by rfl⟩ : syracuseStep 5544521 = 4158391) B4158391
theorem B3696347 : Blo 2189435 3696347 := bstep (se 1 (by rfl) ⟨2772260, by rfl⟩ : syracuseStep 3696347 = 5544521) B5544521
theorem B2464231 : Blo 2189435 2464231 := bstep (se 1 (by rfl) ⟨1848173, by rfl⟩ : syracuseStep 2464231 = 3696347) B3696347
theorem B3285641 : Blo 2189435 3285641 := bstep (se 2 (by rfl) ⟨1232115, by rfl⟩ : syracuseStep 3285641 = 2464231) B2464231
theorem B2190427 : Blo 2189435 2190427 := bstep (se 1 (by rfl) ⟨1642820, by rfl⟩ : syracuseStep 2190427 = 3285641) B3285641
theorem B11089061 : Blo 2189435 11089061 := bbase (se 4 (by rfl) ⟨1039599, by rfl⟩ : syracuseStep 11089061 = 2079199) (by norm_num)
theorem B7392707 : Blo 2189435 7392707 := bstep (se 1 (by rfl) ⟨5544530, by rfl⟩ : syracuseStep 7392707 = 11089061) B11089061
theorem B4928471 : Blo 2189435 4928471 := bstep (se 1 (by rfl) ⟨3696353, by rfl⟩ : syracuseStep 4928471 = 7392707) B7392707
theorem B3285647 : Blo 2189435 3285647 := bstep (se 1 (by rfl) ⟨2464235, by rfl⟩ : syracuseStep 3285647 = 4928471) B4928471
theorem B2190431 : Blo 2189435 2190431 := bstep (se 1 (by rfl) ⟨1642823, by rfl⟩ : syracuseStep 2190431 = 3285647) B3285647
theorem B3285653 : Blo 2189435 3285653 := bbase (se 6 (by rfl) ⟨77007, by rfl⟩ : syracuseStep 3285653 = 154015) (by norm_num)
theorem B2190435 : Blo 2189435 2190435 := bstep (se 1 (by rfl) ⟨1642826, by rfl⟩ : syracuseStep 2190435 = 3285653) B3285653
theorem B8881301 : Blo 2189435 8881301 := bbase (se 6 (by rfl) ⟨208155, by rfl⟩ : syracuseStep 8881301 = 416311) (by norm_num)
theorem B5920867 : Blo 2189435 5920867 := bstep (se 1 (by rfl) ⟨4440650, by rfl⟩ : syracuseStep 5920867 = 8881301) B8881301
theorem B31577957 : Blo 2189435 31577957 := bstep (se 4 (by rfl) ⟨2960433, by rfl⟩ : syracuseStep 31577957 = 5920867) B5920867
theorem B21051971 : Blo 2189435 21051971 := bstep (se 1 (by rfl) ⟨15788978, by rfl⟩ : syracuseStep 21051971 = 31577957) B31577957
theorem B14034647 : Blo 2189435 14034647 := bstep (se 1 (by rfl) ⟨10525985, by rfl⟩ : syracuseStep 14034647 = 21051971) B21051971
theorem B9356431 : Blo 2189435 9356431 := bstep (se 1 (by rfl) ⟨7017323, by rfl⟩ : syracuseStep 9356431 = 14034647) B14034647
theorem B12475241 : Blo 2189435 12475241 := bstep (se 2 (by rfl) ⟨4678215, by rfl⟩ : syracuseStep 12475241 = 9356431) B9356431
theorem B8316827 : Blo 2189435 8316827 := bstep (se 1 (by rfl) ⟨6237620, by rfl⟩ : syracuseStep 8316827 = 12475241) B12475241
theorem B5544551 : Blo 2189435 5544551 := bstep (se 1 (by rfl) ⟨4158413, by rfl⟩ : syracuseStep 5544551 = 8316827) B8316827
theorem B3696367 : Blo 2189435 3696367 := bstep (se 1 (by rfl) ⟨2772275, by rfl⟩ : syracuseStep 3696367 = 5544551) B5544551
theorem B4928489 : Blo 2189435 4928489 := bstep (se 2 (by rfl) ⟨1848183, by rfl⟩ : syracuseStep 4928489 = 3696367) B3696367
theorem B3285659 : Blo 2189435 3285659 := bstep (se 1 (by rfl) ⟨2464244, by rfl⟩ : syracuseStep 3285659 = 4928489) B4928489
theorem B2190439 : Blo 2189435 2190439 := bstep (se 1 (by rfl) ⟨1642829, by rfl⟩ : syracuseStep 2190439 = 3285659) B3285659
theorem B2464249 : Blo 2189435 2464249 := bbase (se 2 (by rfl) ⟨924093, by rfl⟩ : syracuseStep 2464249 = 1848187) (by norm_num)
theorem B3285665 : Blo 2189435 3285665 := bstep (se 2 (by rfl) ⟨1232124, by rfl⟩ : syracuseStep 3285665 = 2464249) B2464249
theorem B2190443 : Blo 2189435 2190443 := bstep (se 1 (by rfl) ⟨1642832, by rfl⟩ : syracuseStep 2190443 = 3285665) B3285665
theorem B7017349 : Blo 2189435 7017349 := bbase (se 4 (by rfl) ⟨657876, by rfl⟩ : syracuseStep 7017349 = 1315753) (by norm_num)
theorem B9356465 : Blo 2189435 9356465 := bstep (se 2 (by rfl) ⟨3508674, by rfl⟩ : syracuseStep 9356465 = 7017349) B7017349
theorem B6237643 : Blo 2189435 6237643 := bstep (se 1 (by rfl) ⟨4678232, by rfl⟩ : syracuseStep 6237643 = 9356465) B9356465
theorem B8316857 : Blo 2189435 8316857 := bstep (se 2 (by rfl) ⟨3118821, by rfl⟩ : syracuseStep 8316857 = 6237643) B6237643
theorem B5544571 : Blo 2189435 5544571 := bstep (se 1 (by rfl) ⟨4158428, by rfl⟩ : syracuseStep 5544571 = 8316857) B8316857
theorem B7392761 : Blo 2189435 7392761 := bstep (se 2 (by rfl) ⟨2772285, by rfl⟩ : syracuseStep 7392761 = 5544571) B5544571
theorem B4928507 : Blo 2189435 4928507 := bstep (se 1 (by rfl) ⟨3696380, by rfl⟩ : syracuseStep 4928507 = 7392761) B7392761
theorem B3285671 : Blo 2189435 3285671 := bstep (se 1 (by rfl) ⟨2464253, by rfl⟩ : syracuseStep 3285671 = 4928507) B4928507
theorem B2190447 : Blo 2189435 2190447 := bstep (se 1 (by rfl) ⟨1642835, by rfl⟩ : syracuseStep 2190447 = 3285671) B3285671
theorem B3285677 : Blo 2189435 3285677 := bbase (se 3 (by rfl) ⟨616064, by rfl⟩ : syracuseStep 3285677 = 1232129) (by norm_num)
theorem B2190451 : Blo 2189435 2190451 := bstep (se 1 (by rfl) ⟨1642838, by rfl⟩ : syracuseStep 2190451 = 3285677) B3285677
theorem B4928525 : Blo 2189435 4928525 := bbase (se 3 (by rfl) ⟨924098, by rfl⟩ : syracuseStep 4928525 = 1848197) (by norm_num)
theorem B3285683 : Blo 2189435 3285683 := bstep (se 1 (by rfl) ⟨2464262, by rfl⟩ : syracuseStep 3285683 = 4928525) B4928525
theorem B2190455 : Blo 2189435 2190455 := bstep (se 1 (by rfl) ⟨1642841, by rfl⟩ : syracuseStep 2190455 = 3285683) B3285683
theorem B2772301 : Blo 2189435 2772301 := bbase (se 3 (by rfl) ⟨519806, by rfl⟩ : syracuseStep 2772301 = 1039613) (by norm_num)
theorem B3696401 : Blo 2189435 3696401 := bstep (se 2 (by rfl) ⟨1386150, by rfl⟩ : syracuseStep 3696401 = 2772301) B2772301
theorem B2464267 : Blo 2189435 2464267 := bstep (se 1 (by rfl) ⟨1848200, by rfl⟩ : syracuseStep 2464267 = 3696401) B3696401
theorem B3285689 : Blo 2189435 3285689 := bstep (se 2 (by rfl) ⟨1232133, by rfl⟩ : syracuseStep 3285689 = 2464267) B2464267
theorem B2190459 : Blo 2189435 2190459 := bstep (se 1 (by rfl) ⟨1642844, by rfl⟩ : syracuseStep 2190459 = 3285689) B3285689
theorem B20532149 : Blo 2189435 20532149 := bbase (se 5 (by rfl) ⟨962444, by rfl⟩ : syracuseStep 20532149 = 1924889) (by norm_num)
theorem B13688099 : Blo 2189435 13688099 := bstep (se 1 (by rfl) ⟨10266074, by rfl⟩ : syracuseStep 13688099 = 20532149) B20532149
theorem B9125399 : Blo 2189435 9125399 := bstep (se 1 (by rfl) ⟨6844049, by rfl⟩ : syracuseStep 9125399 = 13688099) B13688099
theorem B6083599 : Blo 2189435 6083599 := bstep (se 1 (by rfl) ⟨4562699, by rfl⟩ : syracuseStep 6083599 = 9125399) B9125399
theorem B8111465 : Blo 2189435 8111465 := bstep (se 2 (by rfl) ⟨3041799, by rfl⟩ : syracuseStep 8111465 = 6083599) B6083599
theorem B5407643 : Blo 2189435 5407643 := bstep (se 1 (by rfl) ⟨4055732, by rfl⟩ : syracuseStep 5407643 = 8111465) B8111465
theorem B3605095 : Blo 2189435 3605095 := bstep (se 1 (by rfl) ⟨2703821, by rfl⟩ : syracuseStep 3605095 = 5407643) B5407643
theorem B4806793 : Blo 2189435 4806793 := bstep (se 2 (by rfl) ⟨1802547, by rfl⟩ : syracuseStep 4806793 = 3605095) B3605095
theorem B6409057 : Blo 2189435 6409057 := bstep (se 2 (by rfl) ⟨2403396, by rfl⟩ : syracuseStep 6409057 = 4806793) B4806793
theorem B8545409 : Blo 2189435 8545409 := bstep (se 2 (by rfl) ⟨3204528, by rfl⟩ : syracuseStep 8545409 = 6409057) B6409057
theorem B5696939 : Blo 2189435 5696939 := bstep (se 1 (by rfl) ⟨4272704, by rfl⟩ : syracuseStep 5696939 = 8545409) B8545409
theorem B15191837 : Blo 2189435 15191837 := bstep (se 3 (by rfl) ⟨2848469, by rfl⟩ : syracuseStep 15191837 = 5696939) B5696939
theorem B10127891 : Blo 2189435 10127891 := bstep (se 1 (by rfl) ⟨7595918, by rfl⟩ : syracuseStep 10127891 = 15191837) B15191837
theorem B6751927 : Blo 2189435 6751927 := bstep (se 1 (by rfl) ⟨5063945, by rfl⟩ : syracuseStep 6751927 = 10127891) B10127891
theorem B36010277 : Blo 2189435 36010277 := bstep (se 4 (by rfl) ⟨3375963, by rfl⟩ : syracuseStep 36010277 = 6751927) B6751927
theorem B24006851 : Blo 2189435 24006851 := bstep (se 1 (by rfl) ⟨18005138, by rfl⟩ : syracuseStep 24006851 = 36010277) B36010277
theorem B16004567 : Blo 2189435 16004567 := bstep (se 1 (by rfl) ⟨12003425, by rfl⟩ : syracuseStep 16004567 = 24006851) B24006851
theorem B42678845 : Blo 2189435 42678845 := bstep (se 3 (by rfl) ⟨8002283, by rfl⟩ : syracuseStep 42678845 = 16004567) B16004567
theorem B28452563 : Blo 2189435 28452563 := bstep (se 1 (by rfl) ⟨21339422, by rfl⟩ : syracuseStep 28452563 = 42678845) B42678845
theorem B18968375 : Blo 2189435 18968375 := bstep (se 1 (by rfl) ⟨14226281, by rfl⟩ : syracuseStep 18968375 = 28452563) B28452563
theorem B50582333 : Blo 2189435 50582333 := bstep (se 3 (by rfl) ⟨9484187, by rfl⟩ : syracuseStep 50582333 = 18968375) B18968375
theorem B33721555 : Blo 2189435 33721555 := bstep (se 1 (by rfl) ⟨25291166, by rfl⟩ : syracuseStep 33721555 = 50582333) B50582333
theorem B44962073 : Blo 2189435 44962073 := bstep (se 2 (by rfl) ⟨16860777, by rfl⟩ : syracuseStep 44962073 = 33721555) B33721555
theorem B29974715 : Blo 2189435 29974715 := bstep (se 1 (by rfl) ⟨22481036, by rfl⟩ : syracuseStep 29974715 = 44962073) B44962073
theorem B19983143 : Blo 2189435 19983143 := bstep (se 1 (by rfl) ⟨14987357, by rfl⟩ : syracuseStep 19983143 = 29974715) B29974715
theorem B53288381 : Blo 2189435 53288381 := bstep (se 3 (by rfl) ⟨9991571, by rfl⟩ : syracuseStep 53288381 = 19983143) B19983143
theorem B35525587 : Blo 2189435 35525587 := bstep (se 1 (by rfl) ⟨26644190, by rfl⟩ : syracuseStep 35525587 = 53288381) B53288381
theorem B47367449 : Blo 2189435 47367449 := bstep (se 2 (by rfl) ⟨17762793, by rfl⟩ : syracuseStep 47367449 = 35525587) B35525587
theorem B31578299 : Blo 2189435 31578299 := bstep (se 1 (by rfl) ⟨23683724, by rfl⟩ : syracuseStep 31578299 = 47367449) B47367449
theorem B21052199 : Blo 2189435 21052199 := bstep (se 1 (by rfl) ⟨15789149, by rfl⟩ : syracuseStep 21052199 = 31578299) B31578299
theorem B14034799 : Blo 2189435 14034799 := bstep (se 1 (by rfl) ⟨10526099, by rfl⟩ : syracuseStep 14034799 = 21052199) B21052199
theorem B18713065 : Blo 2189435 18713065 := bstep (se 2 (by rfl) ⟨7017399, by rfl⟩ : syracuseStep 18713065 = 14034799) B14034799
theorem B24950753 : Blo 2189435 24950753 := bstep (se 2 (by rfl) ⟨9356532, by rfl⟩ : syracuseStep 24950753 = 18713065) B18713065
theorem B16633835 : Blo 2189435 16633835 := bstep (se 1 (by rfl) ⟨12475376, by rfl⟩ : syracuseStep 16633835 = 24950753) B24950753
theorem B11089223 : Blo 2189435 11089223 := bstep (se 1 (by rfl) ⟨8316917, by rfl⟩ : syracuseStep 11089223 = 16633835) B16633835
theorem B7392815 : Blo 2189435 7392815 := bstep (se 1 (by rfl) ⟨5544611, by rfl⟩ : syracuseStep 7392815 = 11089223) B11089223
theorem B4928543 : Blo 2189435 4928543 := bstep (se 1 (by rfl) ⟨3696407, by rfl⟩ : syracuseStep 4928543 = 7392815) B7392815
theorem B3285695 : Blo 2189435 3285695 := bstep (se 1 (by rfl) ⟨2464271, by rfl⟩ : syracuseStep 3285695 = 4928543) B4928543
theorem B2190463 : Blo 2189435 2190463 := bstep (se 1 (by rfl) ⟨1642847, by rfl⟩ : syracuseStep 2190463 = 3285695) B3285695
theorem B3285701 : Blo 2189435 3285701 := bbase (se 4 (by rfl) ⟨308034, by rfl⟩ : syracuseStep 3285701 = 616069) (by norm_num)
theorem B2190467 : Blo 2189435 2190467 := bstep (se 1 (by rfl) ⟨1642850, by rfl⟩ : syracuseStep 2190467 = 3285701) B3285701
theorem B3696421 : Blo 2189435 3696421 := bbase (se 4 (by rfl) ⟨346539, by rfl⟩ : syracuseStep 3696421 = 693079) (by norm_num)
theorem B4928561 : Blo 2189435 4928561 := bstep (se 2 (by rfl) ⟨1848210, by rfl⟩ : syracuseStep 4928561 = 3696421) B3696421
theorem B3285707 : Blo 2189435 3285707 := bstep (se 1 (by rfl) ⟨2464280, by rfl⟩ : syracuseStep 3285707 = 4928561) B4928561
theorem B2190471 : Blo 2189435 2190471 := bstep (se 1 (by rfl) ⟨1642853, by rfl⟩ : syracuseStep 2190471 = 3285707) B3285707
theorem B2464285 : Blo 2189435 2464285 := bbase (se 3 (by rfl) ⟨462053, by rfl⟩ : syracuseStep 2464285 = 924107) (by norm_num)
theorem B3285713 : Blo 2189435 3285713 := bstep (se 2 (by rfl) ⟨1232142, by rfl⟩ : syracuseStep 3285713 = 2464285) B2464285
theorem B2190475 : Blo 2189435 2190475 := bstep (se 1 (by rfl) ⟨1642856, by rfl⟩ : syracuseStep 2190475 = 3285713) B3285713
theorem B7392869 : Blo 2189435 7392869 := bbase (se 4 (by rfl) ⟨693081, by rfl⟩ : syracuseStep 7392869 = 1386163) (by norm_num)
theorem B4928579 : Blo 2189435 4928579 := bstep (se 1 (by rfl) ⟨3696434, by rfl⟩ : syracuseStep 4928579 = 7392869) B7392869
theorem B3285719 : Blo 2189435 3285719 := bstep (se 1 (by rfl) ⟨2464289, by rfl⟩ : syracuseStep 3285719 = 4928579) B4928579
theorem B2190479 : Blo 2189435 2190479 := bstep (se 1 (by rfl) ⟨1642859, by rfl⟩ : syracuseStep 2190479 = 3285719) B3285719
theorem B3285725 : Blo 2189435 3285725 := bbase (se 3 (by rfl) ⟨616073, by rfl⟩ : syracuseStep 3285725 = 1232147) (by norm_num)
theorem B2190483 : Blo 2189435 2190483 := bstep (se 1 (by rfl) ⟨1642862, by rfl⟩ : syracuseStep 2190483 = 3285725) B3285725
theorem B4928597 : Blo 2189435 4928597 := bbase (se 8 (by rfl) ⟨28878, by rfl⟩ : syracuseStep 4928597 = 57757) (by norm_num)
theorem B3285731 : Blo 2189435 3285731 := bstep (se 1 (by rfl) ⟨2464298, by rfl⟩ : syracuseStep 3285731 = 4928597) B4928597
theorem B2190487 : Blo 2189435 2190487 := bstep (se 1 (by rfl) ⟨1642865, by rfl⟩ : syracuseStep 2190487 = 3285731) B3285731
theorem B4440757 : Blo 2189435 4440757 := bbase (se 5 (by rfl) ⟨208160, by rfl⟩ : syracuseStep 4440757 = 416321) (by norm_num)
theorem B5921009 : Blo 2189435 5921009 := bstep (se 2 (by rfl) ⟨2220378, by rfl⟩ : syracuseStep 5921009 = 4440757) B4440757
theorem B3947339 : Blo 2189435 3947339 := bstep (se 1 (by rfl) ⟨2960504, by rfl⟩ : syracuseStep 3947339 = 5921009) B5921009
theorem B10526237 : Blo 2189435 10526237 := bstep (se 3 (by rfl) ⟨1973669, by rfl⟩ : syracuseStep 10526237 = 3947339) B3947339
theorem B7017491 : Blo 2189435 7017491 := bstep (se 1 (by rfl) ⟨5263118, by rfl⟩ : syracuseStep 7017491 = 10526237) B10526237
theorem B4678327 : Blo 2189435 4678327 := bstep (se 1 (by rfl) ⟨3508745, by rfl⟩ : syracuseStep 4678327 = 7017491) B7017491
theorem B6237769 : Blo 2189435 6237769 := bstep (se 2 (by rfl) ⟨2339163, by rfl⟩ : syracuseStep 6237769 = 4678327) B4678327
theorem B8317025 : Blo 2189435 8317025 := bstep (se 2 (by rfl) ⟨3118884, by rfl⟩ : syracuseStep 8317025 = 6237769) B6237769
theorem B5544683 : Blo 2189435 5544683 := bstep (se 1 (by rfl) ⟨4158512, by rfl⟩ : syracuseStep 5544683 = 8317025) B8317025
theorem B3696455 : Blo 2189435 3696455 := bstep (se 1 (by rfl) ⟨2772341, by rfl⟩ : syracuseStep 3696455 = 5544683) B5544683
theorem B2464303 : Blo 2189435 2464303 := bstep (se 1 (by rfl) ⟨1848227, by rfl⟩ : syracuseStep 2464303 = 3696455) B3696455
theorem B3285737 : Blo 2189435 3285737 := bstep (se 2 (by rfl) ⟨1232151, by rfl⟩ : syracuseStep 3285737 = 2464303) B2464303
theorem B2190491 : Blo 2189435 2190491 := bstep (se 1 (by rfl) ⟨1642868, by rfl⟩ : syracuseStep 2190491 = 3285737) B3285737
theorem B89925461 : Blo 2189435 89925461 := bbase (se 9 (by rfl) ⟨263453, by rfl⟩ : syracuseStep 89925461 = 526907) (by norm_num)
theorem B59950307 : Blo 2189435 59950307 := bstep (se 1 (by rfl) ⟨44962730, by rfl⟩ : syracuseStep 59950307 = 89925461) B89925461
theorem B39966871 : Blo 2189435 39966871 := bstep (se 1 (by rfl) ⟨29975153, by rfl⟩ : syracuseStep 39966871 = 59950307) B59950307
theorem B53289161 : Blo 2189435 53289161 := bstep (se 2 (by rfl) ⟨19983435, by rfl⟩ : syracuseStep 53289161 = 39966871) B39966871
theorem B35526107 : Blo 2189435 35526107 := bstep (se 1 (by rfl) ⟨26644580, by rfl⟩ : syracuseStep 35526107 = 53289161) B53289161
theorem B23684071 : Blo 2189435 23684071 := bstep (se 1 (by rfl) ⟨17763053, by rfl⟩ : syracuseStep 23684071 = 35526107) B35526107
theorem B31578761 : Blo 2189435 31578761 := bstep (se 2 (by rfl) ⟨11842035, by rfl⟩ : syracuseStep 31578761 = 23684071) B23684071
theorem B21052507 : Blo 2189435 21052507 := bstep (se 1 (by rfl) ⟨15789380, by rfl⟩ : syracuseStep 21052507 = 31578761) B31578761
theorem B28070009 : Blo 2189435 28070009 := bstep (se 2 (by rfl) ⟨10526253, by rfl⟩ : syracuseStep 28070009 = 21052507) B21052507
theorem B18713339 : Blo 2189435 18713339 := bstep (se 1 (by rfl) ⟨14035004, by rfl⟩ : syracuseStep 18713339 = 28070009) B28070009
theorem B12475559 : Blo 2189435 12475559 := bstep (se 1 (by rfl) ⟨9356669, by rfl⟩ : syracuseStep 12475559 = 18713339) B18713339
theorem B8317039 : Blo 2189435 8317039 := bstep (se 1 (by rfl) ⟨6237779, by rfl⟩ : syracuseStep 8317039 = 12475559) B12475559
theorem B11089385 : Blo 2189435 11089385 := bstep (se 2 (by rfl) ⟨4158519, by rfl⟩ : syracuseStep 11089385 = 8317039) B8317039
theorem B7392923 : Blo 2189435 7392923 := bstep (se 1 (by rfl) ⟨5544692, by rfl⟩ : syracuseStep 7392923 = 11089385) B11089385
theorem B4928615 : Blo 2189435 4928615 := bstep (se 1 (by rfl) ⟨3696461, by rfl⟩ : syracuseStep 4928615 = 7392923) B7392923
theorem B3285743 : Blo 2189435 3285743 := bstep (se 1 (by rfl) ⟨2464307, by rfl⟩ : syracuseStep 3285743 = 4928615) B4928615
theorem B2190495 : Blo 2189435 2190495 := bstep (se 1 (by rfl) ⟨1642871, by rfl⟩ : syracuseStep 2190495 = 3285743) B3285743
theorem B3285749 : Blo 2189435 3285749 := bbase (se 5 (by rfl) ⟨154019, by rfl⟩ : syracuseStep 3285749 = 308039) (by norm_num)
theorem B2190499 : Blo 2189435 2190499 := bstep (se 1 (by rfl) ⟨1642874, by rfl⟩ : syracuseStep 2190499 = 3285749) B3285749
theorem B4440781 : Blo 2189435 4440781 := bbase (se 3 (by rfl) ⟨832646, by rfl⟩ : syracuseStep 4440781 = 1665293) (by norm_num)
theorem B5921041 : Blo 2189435 5921041 := bstep (se 2 (by rfl) ⟨2220390, by rfl⟩ : syracuseStep 5921041 = 4440781) B4440781
theorem B7894721 : Blo 2189435 7894721 := bstep (se 2 (by rfl) ⟨2960520, by rfl⟩ : syracuseStep 7894721 = 5921041) B5921041
theorem B5263147 : Blo 2189435 5263147 := bstep (se 1 (by rfl) ⟨3947360, by rfl⟩ : syracuseStep 5263147 = 7894721) B7894721
theorem B7017529 : Blo 2189435 7017529 := bstep (se 2 (by rfl) ⟨2631573, by rfl⟩ : syracuseStep 7017529 = 5263147) B5263147
theorem B9356705 : Blo 2189435 9356705 := bstep (se 2 (by rfl) ⟨3508764, by rfl⟩ : syracuseStep 9356705 = 7017529) B7017529
theorem B6237803 : Blo 2189435 6237803 := bstep (se 1 (by rfl) ⟨4678352, by rfl⟩ : syracuseStep 6237803 = 9356705) B9356705
theorem B4158535 : Blo 2189435 4158535 := bstep (se 1 (by rfl) ⟨3118901, by rfl⟩ : syracuseStep 4158535 = 6237803) B6237803
theorem B5544713 : Blo 2189435 5544713 := bstep (se 2 (by rfl) ⟨2079267, by rfl⟩ : syracuseStep 5544713 = 4158535) B4158535
theorem B3696475 : Blo 2189435 3696475 := bstep (se 1 (by rfl) ⟨2772356, by rfl⟩ : syracuseStep 3696475 = 5544713) B5544713
theorem B4928633 : Blo 2189435 4928633 := bstep (se 2 (by rfl) ⟨1848237, by rfl⟩ : syracuseStep 4928633 = 3696475) B3696475
theorem B3285755 : Blo 2189435 3285755 := bstep (se 1 (by rfl) ⟨2464316, by rfl⟩ : syracuseStep 3285755 = 4928633) B4928633
theorem B2190503 : Blo 2189435 2190503 := bstep (se 1 (by rfl) ⟨1642877, by rfl⟩ : syracuseStep 2190503 = 3285755) B3285755
theorem B2464321 : Blo 2189435 2464321 := bbase (se 2 (by rfl) ⟨924120, by rfl⟩ : syracuseStep 2464321 = 1848241) (by norm_num)
theorem B3285761 : Blo 2189435 3285761 := bstep (se 2 (by rfl) ⟨1232160, by rfl⟩ : syracuseStep 3285761 = 2464321) B2464321
theorem B2190507 : Blo 2189435 2190507 := bstep (se 1 (by rfl) ⟨1642880, by rfl⟩ : syracuseStep 2190507 = 3285761) B3285761
theorem B5544733 : Blo 2189435 5544733 := bbase (se 3 (by rfl) ⟨1039637, by rfl⟩ : syracuseStep 5544733 = 2079275) (by norm_num)
theorem B7392977 : Blo 2189435 7392977 := bstep (se 2 (by rfl) ⟨2772366, by rfl⟩ : syracuseStep 7392977 = 5544733) B5544733
theorem B4928651 : Blo 2189435 4928651 := bstep (se 1 (by rfl) ⟨3696488, by rfl⟩ : syracuseStep 4928651 = 7392977) B7392977
theorem B3285767 : Blo 2189435 3285767 := bstep (se 1 (by rfl) ⟨2464325, by rfl⟩ : syracuseStep 3285767 = 4928651) B4928651
theorem B2190511 : Blo 2189435 2190511 := bstep (se 1 (by rfl) ⟨1642883, by rfl⟩ : syracuseStep 2190511 = 3285767) B3285767
theorem B3285773 : Blo 2189435 3285773 := bbase (se 3 (by rfl) ⟨616082, by rfl⟩ : syracuseStep 3285773 = 1232165) (by norm_num)
theorem B2190515 : Blo 2189435 2190515 := bstep (se 1 (by rfl) ⟨1642886, by rfl⟩ : syracuseStep 2190515 = 3285773) B3285773
theorem B4928669 : Blo 2189435 4928669 := bbase (se 3 (by rfl) ⟨924125, by rfl⟩ : syracuseStep 4928669 = 1848251) (by norm_num)
theorem B3285779 : Blo 2189435 3285779 := bstep (se 1 (by rfl) ⟨2464334, by rfl⟩ : syracuseStep 3285779 = 4928669) B4928669
theorem B2190519 : Blo 2189435 2190519 := bstep (se 1 (by rfl) ⟨1642889, by rfl⟩ : syracuseStep 2190519 = 3285779) B3285779
theorem B3696509 : Blo 2189435 3696509 := bbase (se 3 (by rfl) ⟨693095, by rfl⟩ : syracuseStep 3696509 = 1386191) (by norm_num)
theorem B2464339 : Blo 2189435 2464339 := bstep (se 1 (by rfl) ⟨1848254, by rfl⟩ : syracuseStep 2464339 = 3696509) B3696509
theorem B3285785 : Blo 2189435 3285785 := bstep (se 2 (by rfl) ⟨1232169, by rfl⟩ : syracuseStep 3285785 = 2464339) B2464339
theorem B2190523 : Blo 2189435 2190523 := bstep (se 1 (by rfl) ⟨1642892, by rfl⟩ : syracuseStep 2190523 = 3285785) B3285785
theorem B7017605 : Blo 2189435 7017605 := bbase (se 4 (by rfl) ⟨657900, by rfl⟩ : syracuseStep 7017605 = 1315801) (by norm_num)
theorem B4678403 : Blo 2189435 4678403 := bstep (se 1 (by rfl) ⟨3508802, by rfl⟩ : syracuseStep 4678403 = 7017605) B7017605
theorem B12475741 : Blo 2189435 12475741 := bstep (se 3 (by rfl) ⟨2339201, by rfl⟩ : syracuseStep 12475741 = 4678403) B4678403
theorem B16634321 : Blo 2189435 16634321 := bstep (se 2 (by rfl) ⟨6237870, by rfl⟩ : syracuseStep 16634321 = 12475741) B12475741
theorem B11089547 : Blo 2189435 11089547 := bstep (se 1 (by rfl) ⟨8317160, by rfl⟩ : syracuseStep 11089547 = 16634321) B16634321
theorem B7393031 : Blo 2189435 7393031 := bstep (se 1 (by rfl) ⟨5544773, by rfl⟩ : syracuseStep 7393031 = 11089547) B11089547
theorem B4928687 : Blo 2189435 4928687 := bstep (se 1 (by rfl) ⟨3696515, by rfl⟩ : syracuseStep 4928687 = 7393031) B7393031
theorem B3285791 : Blo 2189435 3285791 := bstep (se 1 (by rfl) ⟨2464343, by rfl⟩ : syracuseStep 3285791 = 4928687) B4928687
theorem B2190527 : Blo 2189435 2190527 := bstep (se 1 (by rfl) ⟨1642895, by rfl⟩ : syracuseStep 2190527 = 3285791) B3285791
theorem B3285797 : Blo 2189435 3285797 := bbase (se 4 (by rfl) ⟨308043, by rfl⟩ : syracuseStep 3285797 = 616087) (by norm_num)
theorem B2190531 : Blo 2189435 2190531 := bstep (se 1 (by rfl) ⟨1642898, by rfl⟩ : syracuseStep 2190531 = 3285797) B3285797
theorem B2772397 : Blo 2189435 2772397 := bbase (se 3 (by rfl) ⟨519824, by rfl⟩ : syracuseStep 2772397 = 1039649) (by norm_num)
theorem B3696529 : Blo 2189435 3696529 := bstep (se 2 (by rfl) ⟨1386198, by rfl⟩ : syracuseStep 3696529 = 2772397) B2772397
theorem B4928705 : Blo 2189435 4928705 := bstep (se 2 (by rfl) ⟨1848264, by rfl⟩ : syracuseStep 4928705 = 3696529) B3696529
theorem B3285803 : Blo 2189435 3285803 := bstep (se 1 (by rfl) ⟨2464352, by rfl⟩ : syracuseStep 3285803 = 4928705) B4928705
theorem B2190535 : Blo 2189435 2190535 := bstep (se 1 (by rfl) ⟨1642901, by rfl⟩ : syracuseStep 2190535 = 3285803) B3285803
theorem B2464357 : Blo 2189435 2464357 := bbase (se 4 (by rfl) ⟨231033, by rfl⟩ : syracuseStep 2464357 = 462067) (by norm_num)
theorem B3285809 : Blo 2189435 3285809 := bstep (se 2 (by rfl) ⟨1232178, by rfl⟩ : syracuseStep 3285809 = 2464357) B2464357
theorem B2190539 : Blo 2189435 2190539 := bstep (se 1 (by rfl) ⟨1642904, by rfl⟩ : syracuseStep 2190539 = 3285809) B3285809
theorem B3508829 : Blo 2189435 3508829 := bbase (se 3 (by rfl) ⟨657905, by rfl⟩ : syracuseStep 3508829 = 1315811) (by norm_num)
theorem B2339219 : Blo 2189435 2339219 := bstep (se 1 (by rfl) ⟨1754414, by rfl⟩ : syracuseStep 2339219 = 3508829) B3508829
theorem B6237917 : Blo 2189435 6237917 := bstep (se 3 (by rfl) ⟨1169609, by rfl⟩ : syracuseStep 6237917 = 2339219) B2339219
theorem B4158611 : Blo 2189435 4158611 := bstep (se 1 (by rfl) ⟨3118958, by rfl⟩ : syracuseStep 4158611 = 6237917) B6237917
theorem B2772407 : Blo 2189435 2772407 := bstep (se 1 (by rfl) ⟨2079305, by rfl⟩ : syracuseStep 2772407 = 4158611) B4158611
theorem B7393085 : Blo 2189435 7393085 := bstep (se 3 (by rfl) ⟨1386203, by rfl⟩ : syracuseStep 7393085 = 2772407) B2772407
theorem B4928723 : Blo 2189435 4928723 := bstep (se 1 (by rfl) ⟨3696542, by rfl⟩ : syracuseStep 4928723 = 7393085) B7393085
theorem B3285815 : Blo 2189435 3285815 := bstep (se 1 (by rfl) ⟨2464361, by rfl⟩ : syracuseStep 3285815 = 4928723) B4928723
theorem B2190543 : Blo 2189435 2190543 := bstep (se 1 (by rfl) ⟨1642907, by rfl⟩ : syracuseStep 2190543 = 3285815) B3285815
theorem B3285821 : Blo 2189435 3285821 := bbase (se 3 (by rfl) ⟨616091, by rfl⟩ : syracuseStep 3285821 = 1232183) (by norm_num)
theorem B2190547 : Blo 2189435 2190547 := bstep (se 1 (by rfl) ⟨1642910, by rfl⟩ : syracuseStep 2190547 = 3285821) B3285821
theorem B4928741 : Blo 2189435 4928741 := bbase (se 4 (by rfl) ⟨462069, by rfl⟩ : syracuseStep 4928741 = 924139) (by norm_num)
theorem B3285827 : Blo 2189435 3285827 := bstep (se 1 (by rfl) ⟨2464370, by rfl⟩ : syracuseStep 3285827 = 4928741) B4928741
theorem B2190551 : Blo 2189435 2190551 := bstep (se 1 (by rfl) ⟨1642913, by rfl⟩ : syracuseStep 2190551 = 3285827) B3285827
theorem B5544845 : Blo 2189435 5544845 := bbase (se 3 (by rfl) ⟨1039658, by rfl⟩ : syracuseStep 5544845 = 2079317) (by norm_num)
theorem B3696563 : Blo 2189435 3696563 := bstep (se 1 (by rfl) ⟨2772422, by rfl⟩ : syracuseStep 3696563 = 5544845) B5544845
theorem B2464375 : Blo 2189435 2464375 := bstep (se 1 (by rfl) ⟨1848281, by rfl⟩ : syracuseStep 2464375 = 3696563) B3696563
theorem B3285833 : Blo 2189435 3285833 := bstep (se 2 (by rfl) ⟨1232187, by rfl⟩ : syracuseStep 3285833 = 2464375) B2464375
theorem B2190555 : Blo 2189435 2190555 := bstep (se 1 (by rfl) ⟨1642916, by rfl⟩ : syracuseStep 2190555 = 3285833) B3285833
theorem B3118981 : Blo 2189435 3118981 := bbase (se 4 (by rfl) ⟨292404, by rfl⟩ : syracuseStep 3118981 = 584809) (by norm_num)
theorem B4158641 : Blo 2189435 4158641 := bstep (se 2 (by rfl) ⟨1559490, by rfl⟩ : syracuseStep 4158641 = 3118981) B3118981
theorem B11089709 : Blo 2189435 11089709 := bstep (se 3 (by rfl) ⟨2079320, by rfl⟩ : syracuseStep 11089709 = 4158641) B4158641
theorem B7393139 : Blo 2189435 7393139 := bstep (se 1 (by rfl) ⟨5544854, by rfl⟩ : syracuseStep 7393139 = 11089709) B11089709
theorem B4928759 : Blo 2189435 4928759 := bstep (se 1 (by rfl) ⟨3696569, by rfl⟩ : syracuseStep 4928759 = 7393139) B7393139
theorem B3285839 : Blo 2189435 3285839 := bstep (se 1 (by rfl) ⟨2464379, by rfl⟩ : syracuseStep 3285839 = 4928759) B4928759
theorem B2190559 : Blo 2189435 2190559 := bstep (se 1 (by rfl) ⟨1642919, by rfl⟩ : syracuseStep 2190559 = 3285839) B3285839
theorem B3285845 : Blo 2189435 3285845 := bbase (se 9 (by rfl) ⟨9626, by rfl⟩ : syracuseStep 3285845 = 19253) (by norm_num)
theorem B2190563 : Blo 2189435 2190563 := bstep (se 1 (by rfl) ⟨1642922, by rfl⟩ : syracuseStep 2190563 = 3285845) B3285845
theorem B5263301 : Blo 2189435 5263301 := bbase (se 4 (by rfl) ⟨493434, by rfl⟩ : syracuseStep 5263301 = 986869) (by norm_num)
theorem B3508867 : Blo 2189435 3508867 := bstep (se 1 (by rfl) ⟨2631650, by rfl⟩ : syracuseStep 3508867 = 5263301) B5263301
theorem B4678489 : Blo 2189435 4678489 := bstep (se 2 (by rfl) ⟨1754433, by rfl⟩ : syracuseStep 4678489 = 3508867) B3508867
theorem B6237985 : Blo 2189435 6237985 := bstep (se 2 (by rfl) ⟨2339244, by rfl⟩ : syracuseStep 6237985 = 4678489) B4678489
theorem B8317313 : Blo 2189435 8317313 := bstep (se 2 (by rfl) ⟨3118992, by rfl⟩ : syracuseStep 8317313 = 6237985) B6237985
theorem B5544875 : Blo 2189435 5544875 := bstep (se 1 (by rfl) ⟨4158656, by rfl⟩ : syracuseStep 5544875 = 8317313) B8317313
theorem B3696583 : Blo 2189435 3696583 := bstep (se 1 (by rfl) ⟨2772437, by rfl⟩ : syracuseStep 3696583 = 5544875) B5544875
theorem B4928777 : Blo 2189435 4928777 := bstep (se 2 (by rfl) ⟨1848291, by rfl⟩ : syracuseStep 4928777 = 3696583) B3696583
theorem B3285851 : Blo 2189435 3285851 := bstep (se 1 (by rfl) ⟨2464388, by rfl⟩ : syracuseStep 3285851 = 4928777) B4928777
theorem B2190567 : Blo 2189435 2190567 := bstep (se 1 (by rfl) ⟨1642925, by rfl⟩ : syracuseStep 2190567 = 3285851) B3285851
theorem B2464393 : Blo 2189435 2464393 := bbase (se 2 (by rfl) ⟨924147, by rfl⟩ : syracuseStep 2464393 = 1848295) (by norm_num)
theorem B3285857 : Blo 2189435 3285857 := bstep (se 2 (by rfl) ⟨1232196, by rfl⟩ : syracuseStep 3285857 = 2464393) B2464393
theorem B2190571 : Blo 2189435 2190571 := bstep (se 1 (by rfl) ⟨1642928, by rfl⟩ : syracuseStep 2190571 = 3285857) B3285857
theorem B8430821 : Blo 2189435 8430821 := bbase (se 4 (by rfl) ⟨790389, by rfl⟩ : syracuseStep 8430821 = 1580779) (by norm_num)
theorem B5620547 : Blo 2189435 5620547 := bstep (se 1 (by rfl) ⟨4215410, by rfl⟩ : syracuseStep 5620547 = 8430821) B8430821
theorem B14988125 : Blo 2189435 14988125 := bstep (se 3 (by rfl) ⟨2810273, by rfl⟩ : syracuseStep 14988125 = 5620547) B5620547
theorem B9992083 : Blo 2189435 9992083 := bstep (se 1 (by rfl) ⟨7494062, by rfl⟩ : syracuseStep 9992083 = 14988125) B14988125
theorem B13322777 : Blo 2189435 13322777 := bstep (se 2 (by rfl) ⟨4996041, by rfl⟩ : syracuseStep 13322777 = 9992083) B9992083
theorem B35527405 : Blo 2189435 35527405 := bstep (se 3 (by rfl) ⟨6661388, by rfl⟩ : syracuseStep 35527405 = 13322777) B13322777
theorem B47369873 : Blo 2189435 47369873 := bstep (se 2 (by rfl) ⟨17763702, by rfl⟩ : syracuseStep 47369873 = 35527405) B35527405
theorem B31579915 : Blo 2189435 31579915 := bstep (se 1 (by rfl) ⟨23684936, by rfl⟩ : syracuseStep 31579915 = 47369873) B47369873
theorem B42106553 : Blo 2189435 42106553 := bstep (se 2 (by rfl) ⟨15789957, by rfl⟩ : syracuseStep 42106553 = 31579915) B31579915
theorem B28071035 : Blo 2189435 28071035 := bstep (se 1 (by rfl) ⟨21053276, by rfl⟩ : syracuseStep 28071035 = 42106553) B42106553
theorem B18714023 : Blo 2189435 18714023 := bstep (se 1 (by rfl) ⟨14035517, by rfl⟩ : syracuseStep 18714023 = 28071035) B28071035
theorem B12476015 : Blo 2189435 12476015 := bstep (se 1 (by rfl) ⟨9357011, by rfl⟩ : syracuseStep 12476015 = 18714023) B18714023
theorem B8317343 : Blo 2189435 8317343 := bstep (se 1 (by rfl) ⟨6238007, by rfl⟩ : syracuseStep 8317343 = 12476015) B12476015
theorem B5544895 : Blo 2189435 5544895 := bstep (se 1 (by rfl) ⟨4158671, by rfl⟩ : syracuseStep 5544895 = 8317343) B8317343
theorem B7393193 : Blo 2189435 7393193 := bstep (se 2 (by rfl) ⟨2772447, by rfl⟩ : syracuseStep 7393193 = 5544895) B5544895
theorem B4928795 : Blo 2189435 4928795 := bstep (se 1 (by rfl) ⟨3696596, by rfl⟩ : syracuseStep 4928795 = 7393193) B7393193
theorem B3285863 : Blo 2189435 3285863 := bstep (se 1 (by rfl) ⟨2464397, by rfl⟩ : syracuseStep 3285863 = 4928795) B4928795
theorem B2190575 : Blo 2189435 2190575 := bstep (se 1 (by rfl) ⟨1642931, by rfl⟩ : syracuseStep 2190575 = 3285863) B3285863
theorem B3285869 : Blo 2189435 3285869 := bbase (se 3 (by rfl) ⟨616100, by rfl⟩ : syracuseStep 3285869 = 1232201) (by norm_num)
theorem B2190579 : Blo 2189435 2190579 := bstep (se 1 (by rfl) ⟨1642934, by rfl⟩ : syracuseStep 2190579 = 3285869) B3285869
theorem B4928813 : Blo 2189435 4928813 := bbase (se 3 (by rfl) ⟨924152, by rfl⟩ : syracuseStep 4928813 = 1848305) (by norm_num)
theorem B3285875 : Blo 2189435 3285875 := bstep (se 1 (by rfl) ⟨2464406, by rfl⟩ : syracuseStep 3285875 = 4928813) B4928813
theorem B2190583 : Blo 2189435 2190583 := bstep (se 1 (by rfl) ⟨1642937, by rfl⟩ : syracuseStep 2190583 = 3285875) B3285875
theorem B14227093 : Blo 2189435 14227093 := bbase (se 6 (by rfl) ⟨333447, by rfl⟩ : syracuseStep 14227093 = 666895) (by norm_num)
theorem B75877829 : Blo 2189435 75877829 := bstep (se 4 (by rfl) ⟨7113546, by rfl⟩ : syracuseStep 75877829 = 14227093) B14227093
theorem B50585219 : Blo 2189435 50585219 := bstep (se 1 (by rfl) ⟨37938914, by rfl⟩ : syracuseStep 50585219 = 75877829) B75877829
theorem B33723479 : Blo 2189435 33723479 := bstep (se 1 (by rfl) ⟨25292609, by rfl⟩ : syracuseStep 33723479 = 50585219) B50585219
theorem B22482319 : Blo 2189435 22482319 := bstep (se 1 (by rfl) ⟨16861739, by rfl⟩ : syracuseStep 22482319 = 33723479) B33723479
theorem B29976425 : Blo 2189435 29976425 := bstep (se 2 (by rfl) ⟨11241159, by rfl⟩ : syracuseStep 29976425 = 22482319) B22482319
theorem B19984283 : Blo 2189435 19984283 := bstep (se 1 (by rfl) ⟨14988212, by rfl⟩ : syracuseStep 19984283 = 29976425) B29976425
theorem B13322855 : Blo 2189435 13322855 := bstep (se 1 (by rfl) ⟨9992141, by rfl⟩ : syracuseStep 13322855 = 19984283) B19984283
theorem B8881903 : Blo 2189435 8881903 := bstep (se 1 (by rfl) ⟨6661427, by rfl⟩ : syracuseStep 8881903 = 13322855) B13322855
theorem B11842537 : Blo 2189435 11842537 := bstep (se 2 (by rfl) ⟨4440951, by rfl⟩ : syracuseStep 11842537 = 8881903) B8881903
theorem B15790049 : Blo 2189435 15790049 := bstep (se 2 (by rfl) ⟨5921268, by rfl⟩ : syracuseStep 15790049 = 11842537) B11842537
theorem B10526699 : Blo 2189435 10526699 := bstep (se 1 (by rfl) ⟨7895024, by rfl⟩ : syracuseStep 10526699 = 15790049) B15790049
theorem B7017799 : Blo 2189435 7017799 := bstep (se 1 (by rfl) ⟨5263349, by rfl⟩ : syracuseStep 7017799 = 10526699) B10526699
theorem B9357065 : Blo 2189435 9357065 := bstep (se 2 (by rfl) ⟨3508899, by rfl⟩ : syracuseStep 9357065 = 7017799) B7017799
theorem B6238043 : Blo 2189435 6238043 := bstep (se 1 (by rfl) ⟨4678532, by rfl⟩ : syracuseStep 6238043 = 9357065) B9357065
theorem B4158695 : Blo 2189435 4158695 := bstep (se 1 (by rfl) ⟨3119021, by rfl⟩ : syracuseStep 4158695 = 6238043) B6238043
theorem B2772463 : Blo 2189435 2772463 := bstep (se 1 (by rfl) ⟨2079347, by rfl⟩ : syracuseStep 2772463 = 4158695) B4158695
theorem B3696617 : Blo 2189435 3696617 := bstep (se 2 (by rfl) ⟨1386231, by rfl⟩ : syracuseStep 3696617 = 2772463) B2772463
theorem B2464411 : Blo 2189435 2464411 := bstep (se 1 (by rfl) ⟨1848308, by rfl⟩ : syracuseStep 2464411 = 3696617) B3696617
theorem B3285881 : Blo 2189435 3285881 := bstep (se 2 (by rfl) ⟨1232205, by rfl⟩ : syracuseStep 3285881 = 2464411) B2464411
theorem B2190587 : Blo 2189435 2190587 := bstep (se 1 (by rfl) ⟨1642940, by rfl⟩ : syracuseStep 2190587 = 3285881) B3285881
theorem B21053429 : Blo 2189435 21053429 := bbase (se 5 (by rfl) ⟨986879, by rfl⟩ : syracuseStep 21053429 = 1973759) (by norm_num)
theorem B14035619 : Blo 2189435 14035619 := bstep (se 1 (by rfl) ⟨10526714, by rfl⟩ : syracuseStep 14035619 = 21053429) B21053429
theorem B37428317 : Blo 2189435 37428317 := bstep (se 3 (by rfl) ⟨7017809, by rfl⟩ : syracuseStep 37428317 = 14035619) B14035619
theorem B24952211 : Blo 2189435 24952211 := bstep (se 1 (by rfl) ⟨18714158, by rfl⟩ : syracuseStep 24952211 = 37428317) B37428317
theorem B16634807 : Blo 2189435 16634807 := bstep (se 1 (by rfl) ⟨12476105, by rfl⟩ : syracuseStep 16634807 = 24952211) B24952211
theorem B11089871 : Blo 2189435 11089871 := bstep (se 1 (by rfl) ⟨8317403, by rfl⟩ : syracuseStep 11089871 = 16634807) B16634807
theorem B7393247 : Blo 2189435 7393247 := bstep (se 1 (by rfl) ⟨5544935, by rfl⟩ : syracuseStep 7393247 = 11089871) B11089871
theorem B4928831 : Blo 2189435 4928831 := bstep (se 1 (by rfl) ⟨3696623, by rfl⟩ : syracuseStep 4928831 = 7393247) B7393247
theorem B3285887 : Blo 2189435 3285887 := bstep (se 1 (by rfl) ⟨2464415, by rfl⟩ : syracuseStep 3285887 = 4928831) B4928831
theorem B2190591 : Blo 2189435 2190591 := bstep (se 1 (by rfl) ⟨1642943, by rfl⟩ : syracuseStep 2190591 = 3285887) B3285887
theorem B3285893 : Blo 2189435 3285893 := bbase (se 4 (by rfl) ⟨308052, by rfl⟩ : syracuseStep 3285893 = 616105) (by norm_num)
theorem B2190595 : Blo 2189435 2190595 := bstep (se 1 (by rfl) ⟨1642946, by rfl⟩ : syracuseStep 2190595 = 3285893) B3285893
theorem B3696637 : Blo 2189435 3696637 := bbase (se 3 (by rfl) ⟨693119, by rfl⟩ : syracuseStep 3696637 = 1386239) (by norm_num)
theorem B4928849 : Blo 2189435 4928849 := bstep (se 2 (by rfl) ⟨1848318, by rfl⟩ : syracuseStep 4928849 = 3696637) B3696637
theorem B3285899 : Blo 2189435 3285899 := bstep (se 1 (by rfl) ⟨2464424, by rfl⟩ : syracuseStep 3285899 = 4928849) B4928849
theorem B2190599 : Blo 2189435 2190599 := bstep (se 1 (by rfl) ⟨1642949, by rfl⟩ : syracuseStep 2190599 = 3285899) B3285899
theorem B2464429 : Blo 2189435 2464429 := bbase (se 3 (by rfl) ⟨462080, by rfl⟩ : syracuseStep 2464429 = 924161) (by norm_num)
theorem B3285905 : Blo 2189435 3285905 := bstep (se 2 (by rfl) ⟨1232214, by rfl⟩ : syracuseStep 3285905 = 2464429) B2464429
theorem B2190603 : Blo 2189435 2190603 := bstep (se 1 (by rfl) ⟨1642952, by rfl⟩ : syracuseStep 2190603 = 3285905) B3285905
theorem B7393301 : Blo 2189435 7393301 := bbase (se 6 (by rfl) ⟨173280, by rfl⟩ : syracuseStep 7393301 = 346561) (by norm_num)
theorem B4928867 : Blo 2189435 4928867 := bstep (se 1 (by rfl) ⟨3696650, by rfl⟩ : syracuseStep 4928867 = 7393301) B7393301
theorem B3285911 : Blo 2189435 3285911 := bstep (se 1 (by rfl) ⟨2464433, by rfl⟩ : syracuseStep 3285911 = 4928867) B4928867
theorem B2190607 : Blo 2189435 2190607 := bstep (se 1 (by rfl) ⟨1642955, by rfl⟩ : syracuseStep 2190607 = 3285911) B3285911
theorem B3285917 : Blo 2189435 3285917 := bbase (se 3 (by rfl) ⟨616109, by rfl⟩ : syracuseStep 3285917 = 1232219) (by norm_num)
theorem B2190611 : Blo 2189435 2190611 := bstep (se 1 (by rfl) ⟨1642958, by rfl⟩ : syracuseStep 2190611 = 3285917) B3285917
theorem B4928885 : Blo 2189435 4928885 := bbase (se 5 (by rfl) ⟨231041, by rfl⟩ : syracuseStep 4928885 = 462083) (by norm_num)
theorem B3285923 : Blo 2189435 3285923 := bstep (se 1 (by rfl) ⟨2464442, by rfl⟩ : syracuseStep 3285923 = 4928885) B4928885
theorem B2190615 : Blo 2189435 2190615 := bstep (se 1 (by rfl) ⟨1642961, by rfl⟩ : syracuseStep 2190615 = 3285923) B3285923
theorem B2960677 : Blo 2189435 2960677 := bbase (se 4 (by rfl) ⟨277563, by rfl⟩ : syracuseStep 2960677 = 555127) (by norm_num)
theorem B15790277 : Blo 2189435 15790277 := bstep (se 4 (by rfl) ⟨1480338, by rfl⟩ : syracuseStep 15790277 = 2960677) B2960677
theorem B10526851 : Blo 2189435 10526851 := bstep (se 1 (by rfl) ⟨7895138, by rfl⟩ : syracuseStep 10526851 = 15790277) B15790277
theorem B14035801 : Blo 2189435 14035801 := bstep (se 2 (by rfl) ⟨5263425, by rfl⟩ : syracuseStep 14035801 = 10526851) B10526851
theorem B18714401 : Blo 2189435 18714401 := bstep (se 2 (by rfl) ⟨7017900, by rfl⟩ : syracuseStep 18714401 = 14035801) B14035801
theorem B12476267 : Blo 2189435 12476267 := bstep (se 1 (by rfl) ⟨9357200, by rfl⟩ : syracuseStep 12476267 = 18714401) B18714401
theorem B8317511 : Blo 2189435 8317511 := bstep (se 1 (by rfl) ⟨6238133, by rfl⟩ : syracuseStep 8317511 = 12476267) B12476267
theorem B5545007 : Blo 2189435 5545007 := bstep (se 1 (by rfl) ⟨4158755, by rfl⟩ : syracuseStep 5545007 = 8317511) B8317511
theorem B3696671 : Blo 2189435 3696671 := bstep (se 1 (by rfl) ⟨2772503, by rfl⟩ : syracuseStep 3696671 = 5545007) B5545007
theorem B2464447 : Blo 2189435 2464447 := bstep (se 1 (by rfl) ⟨1848335, by rfl⟩ : syracuseStep 2464447 = 3696671) B3696671
theorem B3285929 : Blo 2189435 3285929 := bstep (se 2 (by rfl) ⟨1232223, by rfl⟩ : syracuseStep 3285929 = 2464447) B2464447
theorem B2190619 : Blo 2189435 2190619 := bstep (se 1 (by rfl) ⟨1642964, by rfl⟩ : syracuseStep 2190619 = 3285929) B3285929
theorem B8317525 : Blo 2189435 8317525 := bbase (se 8 (by rfl) ⟨48735, by rfl⟩ : syracuseStep 8317525 = 97471) (by norm_num)
theorem B11090033 : Blo 2189435 11090033 := bstep (se 2 (by rfl) ⟨4158762, by rfl⟩ : syracuseStep 11090033 = 8317525) B8317525
theorem B7393355 : Blo 2189435 7393355 := bstep (se 1 (by rfl) ⟨5545016, by rfl⟩ : syracuseStep 7393355 = 11090033) B11090033
theorem B4928903 : Blo 2189435 4928903 := bstep (se 1 (by rfl) ⟨3696677, by rfl⟩ : syracuseStep 4928903 = 7393355) B7393355
theorem B3285935 : Blo 2189435 3285935 := bstep (se 1 (by rfl) ⟨2464451, by rfl⟩ : syracuseStep 3285935 = 4928903) B4928903
theorem B2190623 : Blo 2189435 2190623 := bstep (se 1 (by rfl) ⟨1642967, by rfl⟩ : syracuseStep 2190623 = 3285935) B3285935
theorem B3285941 : Blo 2189435 3285941 := bbase (se 5 (by rfl) ⟨154028, by rfl⟩ : syracuseStep 3285941 = 308057) (by norm_num)
theorem B2190627 : Blo 2189435 2190627 := bstep (se 1 (by rfl) ⟨1642970, by rfl⟩ : syracuseStep 2190627 = 3285941) B3285941
theorem B5545037 : Blo 2189435 5545037 := bbase (se 3 (by rfl) ⟨1039694, by rfl⟩ : syracuseStep 5545037 = 2079389) (by norm_num)
theorem B3696691 : Blo 2189435 3696691 := bstep (se 1 (by rfl) ⟨2772518, by rfl⟩ : syracuseStep 3696691 = 5545037) B5545037
theorem B4928921 : Blo 2189435 4928921 := bstep (se 2 (by rfl) ⟨1848345, by rfl⟩ : syracuseStep 4928921 = 3696691) B3696691
theorem B3285947 : Blo 2189435 3285947 := bstep (se 1 (by rfl) ⟨2464460, by rfl⟩ : syracuseStep 3285947 = 4928921) B4928921
theorem B2190631 : Blo 2189435 2190631 := bstep (se 1 (by rfl) ⟨1642973, by rfl⟩ : syracuseStep 2190631 = 3285947) B3285947
theorem B2464465 : Blo 2189435 2464465 := bbase (se 2 (by rfl) ⟨924174, by rfl⟩ : syracuseStep 2464465 = 1848349) (by norm_num)
theorem B3285953 : Blo 2189435 3285953 := bstep (se 2 (by rfl) ⟨1232232, by rfl⟩ : syracuseStep 3285953 = 2464465) B2464465
theorem B2190635 : Blo 2189435 2190635 := bstep (se 1 (by rfl) ⟨1642976, by rfl⟩ : syracuseStep 2190635 = 3285953) B3285953
theorem B2631737 : Blo 2189435 2631737 := bbase (se 2 (by rfl) ⟨986901, by rfl⟩ : syracuseStep 2631737 = 1973803) (by norm_num)
theorem B7017965 : Blo 2189435 7017965 := bstep (se 3 (by rfl) ⟨1315868, by rfl⟩ : syracuseStep 7017965 = 2631737) B2631737
theorem B4678643 : Blo 2189435 4678643 := bstep (se 1 (by rfl) ⟨3508982, by rfl⟩ : syracuseStep 4678643 = 7017965) B7017965
theorem B3119095 : Blo 2189435 3119095 := bstep (se 1 (by rfl) ⟨2339321, by rfl⟩ : syracuseStep 3119095 = 4678643) B4678643
theorem B4158793 : Blo 2189435 4158793 := bstep (se 2 (by rfl) ⟨1559547, by rfl⟩ : syracuseStep 4158793 = 3119095) B3119095
theorem B5545057 : Blo 2189435 5545057 := bstep (se 2 (by rfl) ⟨2079396, by rfl⟩ : syracuseStep 5545057 = 4158793) B4158793
theorem B7393409 : Blo 2189435 7393409 := bstep (se 2 (by rfl) ⟨2772528, by rfl⟩ : syracuseStep 7393409 = 5545057) B5545057
theorem B4928939 : Blo 2189435 4928939 := bstep (se 1 (by rfl) ⟨3696704, by rfl⟩ : syracuseStep 4928939 = 7393409) B7393409
theorem B3285959 : Blo 2189435 3285959 := bstep (se 1 (by rfl) ⟨2464469, by rfl⟩ : syracuseStep 3285959 = 4928939) B4928939
theorem B2190639 : Blo 2189435 2190639 := bstep (se 1 (by rfl) ⟨1642979, by rfl⟩ : syracuseStep 2190639 = 3285959) B3285959
theorem B3285965 : Blo 2189435 3285965 := bbase (se 3 (by rfl) ⟨616118, by rfl⟩ : syracuseStep 3285965 = 1232237) (by norm_num)
theorem B2190643 : Blo 2189435 2190643 := bstep (se 1 (by rfl) ⟨1642982, by rfl⟩ : syracuseStep 2190643 = 3285965) B3285965
theorem B4928957 : Blo 2189435 4928957 := bbase (se 3 (by rfl) ⟨924179, by rfl⟩ : syracuseStep 4928957 = 1848359) (by norm_num)
theorem B3285971 : Blo 2189435 3285971 := bstep (se 1 (by rfl) ⟨2464478, by rfl⟩ : syracuseStep 3285971 = 4928957) B4928957
theorem B2190647 : Blo 2189435 2190647 := bstep (se 1 (by rfl) ⟨1642985, by rfl⟩ : syracuseStep 2190647 = 3285971) B3285971
theorem B3696725 : Blo 2189435 3696725 := bbase (se 8 (by rfl) ⟨21660, by rfl⟩ : syracuseStep 3696725 = 43321) (by norm_num)
theorem B2464483 : Blo 2189435 2464483 := bstep (se 1 (by rfl) ⟨1848362, by rfl⟩ : syracuseStep 2464483 = 3696725) B3696725
theorem B3285977 : Blo 2189435 3285977 := bstep (se 2 (by rfl) ⟨1232241, by rfl⟩ : syracuseStep 3285977 = 2464483) B2464483
theorem B2190651 : Blo 2189435 2190651 := bstep (se 1 (by rfl) ⟨1642988, by rfl⟩ : syracuseStep 2190651 = 3285977) B3285977
theorem B5335325 : Blo 2189435 5335325 := bbase (se 3 (by rfl) ⟨1000373, by rfl⟩ : syracuseStep 5335325 = 2000747) (by norm_num)
theorem B3556883 : Blo 2189435 3556883 := bstep (se 1 (by rfl) ⟨2667662, by rfl⟩ : syracuseStep 3556883 = 5335325) B5335325
theorem B9485021 : Blo 2189435 9485021 := bstep (se 3 (by rfl) ⟨1778441, by rfl⟩ : syracuseStep 9485021 = 3556883) B3556883
theorem B6323347 : Blo 2189435 6323347 := bstep (se 1 (by rfl) ⟨4742510, by rfl⟩ : syracuseStep 6323347 = 9485021) B9485021
theorem B8431129 : Blo 2189435 8431129 := bstep (se 2 (by rfl) ⟨3161673, by rfl⟩ : syracuseStep 8431129 = 6323347) B6323347
theorem B11241505 : Blo 2189435 11241505 := bstep (se 2 (by rfl) ⟨4215564, by rfl⟩ : syracuseStep 11241505 = 8431129) B8431129
theorem B14988673 : Blo 2189435 14988673 := bstep (se 2 (by rfl) ⟨5620752, by rfl⟩ : syracuseStep 14988673 = 11241505) B11241505
theorem B19984897 : Blo 2189435 19984897 := bstep (se 2 (by rfl) ⟨7494336, by rfl⟩ : syracuseStep 19984897 = 14988673) B14988673
theorem B26646529 : Blo 2189435 26646529 := bstep (se 2 (by rfl) ⟨9992448, by rfl⟩ : syracuseStep 26646529 = 19984897) B19984897
theorem B35528705 : Blo 2189435 35528705 := bstep (se 2 (by rfl) ⟨13323264, by rfl⟩ : syracuseStep 35528705 = 26646529) B26646529
theorem B23685803 : Blo 2189435 23685803 := bstep (se 1 (by rfl) ⟨17764352, by rfl⟩ : syracuseStep 23685803 = 35528705) B35528705
theorem B15790535 : Blo 2189435 15790535 := bstep (se 1 (by rfl) ⟨11842901, by rfl⟩ : syracuseStep 15790535 = 23685803) B23685803
theorem B10527023 : Blo 2189435 10527023 := bstep (se 1 (by rfl) ⟨7895267, by rfl⟩ : syracuseStep 10527023 = 15790535) B15790535
theorem B7018015 : Blo 2189435 7018015 := bstep (se 1 (by rfl) ⟨5263511, by rfl⟩ : syracuseStep 7018015 = 10527023) B10527023
theorem B9357353 : Blo 2189435 9357353 := bstep (se 2 (by rfl) ⟨3509007, by rfl⟩ : syracuseStep 9357353 = 7018015) B7018015
theorem B6238235 : Blo 2189435 6238235 := bstep (se 1 (by rfl) ⟨4678676, by rfl⟩ : syracuseStep 6238235 = 9357353) B9357353
theorem B16635293 : Blo 2189435 16635293 := bstep (se 3 (by rfl) ⟨3119117, by rfl⟩ : syracuseStep 16635293 = 6238235) B6238235
theorem B11090195 : Blo 2189435 11090195 := bstep (se 1 (by rfl) ⟨8317646, by rfl⟩ : syracuseStep 11090195 = 16635293) B16635293
theorem B7393463 : Blo 2189435 7393463 := bstep (se 1 (by rfl) ⟨5545097, by rfl⟩ : syracuseStep 7393463 = 11090195) B11090195
theorem B4928975 : Blo 2189435 4928975 := bstep (se 1 (by rfl) ⟨3696731, by rfl⟩ : syracuseStep 4928975 = 7393463) B7393463
theorem B3285983 : Blo 2189435 3285983 := bstep (se 1 (by rfl) ⟨2464487, by rfl⟩ : syracuseStep 3285983 = 4928975) B4928975
theorem B2190655 : Blo 2189435 2190655 := bstep (se 1 (by rfl) ⟨1642991, by rfl⟩ : syracuseStep 2190655 = 3285983) B3285983
theorem B3285989 : Blo 2189435 3285989 := bbase (se 4 (by rfl) ⟨308061, by rfl⟩ : syracuseStep 3285989 = 616123) (by norm_num)
theorem B2190659 : Blo 2189435 2190659 := bstep (se 1 (by rfl) ⟨1642994, by rfl⟩ : syracuseStep 2190659 = 3285989) B3285989
theorem B3509021 : Blo 2189435 3509021 := bbase (se 3 (by rfl) ⟨657941, by rfl⟩ : syracuseStep 3509021 = 1315883) (by norm_num)
theorem B9357389 : Blo 2189435 9357389 := bstep (se 3 (by rfl) ⟨1754510, by rfl⟩ : syracuseStep 9357389 = 3509021) B3509021
theorem B6238259 : Blo 2189435 6238259 := bstep (se 1 (by rfl) ⟨4678694, by rfl⟩ : syracuseStep 6238259 = 9357389) B9357389
theorem B4158839 : Blo 2189435 4158839 := bstep (se 1 (by rfl) ⟨3119129, by rfl⟩ : syracuseStep 4158839 = 6238259) B6238259
theorem B2772559 : Blo 2189435 2772559 := bstep (se 1 (by rfl) ⟨2079419, by rfl⟩ : syracuseStep 2772559 = 4158839) B4158839
theorem B3696745 : Blo 2189435 3696745 := bstep (se 2 (by rfl) ⟨1386279, by rfl⟩ : syracuseStep 3696745 = 2772559) B2772559
theorem B4928993 : Blo 2189435 4928993 := bstep (se 2 (by rfl) ⟨1848372, by rfl⟩ : syracuseStep 4928993 = 3696745) B3696745
theorem B3285995 : Blo 2189435 3285995 := bstep (se 1 (by rfl) ⟨2464496, by rfl⟩ : syracuseStep 3285995 = 4928993) B4928993
theorem B2190663 : Blo 2189435 2190663 := bstep (se 1 (by rfl) ⟨1642997, by rfl⟩ : syracuseStep 2190663 = 3285995) B3285995
theorem B2464501 : Blo 2189435 2464501 := bbase (se 5 (by rfl) ⟨115523, by rfl⟩ : syracuseStep 2464501 = 231047) (by norm_num)
theorem B3286001 : Blo 2189435 3286001 := bstep (se 2 (by rfl) ⟨1232250, by rfl⟩ : syracuseStep 3286001 = 2464501) B2464501
theorem B2190667 : Blo 2189435 2190667 := bstep (se 1 (by rfl) ⟨1643000, by rfl⟩ : syracuseStep 2190667 = 3286001) B3286001
theorem B2772569 : Blo 2189435 2772569 := bbase (se 2 (by rfl) ⟨1039713, by rfl⟩ : syracuseStep 2772569 = 2079427) (by norm_num)
theorem B7393517 : Blo 2189435 7393517 := bstep (se 3 (by rfl) ⟨1386284, by rfl⟩ : syracuseStep 7393517 = 2772569) B2772569
theorem B4929011 : Blo 2189435 4929011 := bstep (se 1 (by rfl) ⟨3696758, by rfl⟩ : syracuseStep 4929011 = 7393517) B7393517
theorem B3286007 : Blo 2189435 3286007 := bstep (se 1 (by rfl) ⟨2464505, by rfl⟩ : syracuseStep 3286007 = 4929011) B4929011
theorem B2190671 : Blo 2189435 2190671 := bstep (se 1 (by rfl) ⟨1643003, by rfl⟩ : syracuseStep 2190671 = 3286007) B3286007
theorem B3286013 : Blo 2189435 3286013 := bbase (se 3 (by rfl) ⟨616127, by rfl⟩ : syracuseStep 3286013 = 1232255) (by norm_num)
theorem B2190675 : Blo 2189435 2190675 := bstep (se 1 (by rfl) ⟨1643006, by rfl⟩ : syracuseStep 2190675 = 3286013) B3286013
theorem B4929029 : Blo 2189435 4929029 := bbase (se 4 (by rfl) ⟨462096, by rfl⟩ : syracuseStep 4929029 = 924193) (by norm_num)
theorem B3286019 : Blo 2189435 3286019 := bstep (se 1 (by rfl) ⟨2464514, by rfl⟩ : syracuseStep 3286019 = 4929029) B4929029
theorem B2190679 : Blo 2189435 2190679 := bstep (se 1 (by rfl) ⟨1643009, by rfl⟩ : syracuseStep 2190679 = 3286019) B3286019
theorem B4158877 : Blo 2189435 4158877 := bbase (se 3 (by rfl) ⟨779789, by rfl⟩ : syracuseStep 4158877 = 1559579) (by norm_num)
theorem B5545169 : Blo 2189435 5545169 := bstep (se 2 (by rfl) ⟨2079438, by rfl⟩ : syracuseStep 5545169 = 4158877) B4158877
theorem B3696779 : Blo 2189435 3696779 := bstep (se 1 (by rfl) ⟨2772584, by rfl⟩ : syracuseStep 3696779 = 5545169) B5545169
theorem B2464519 : Blo 2189435 2464519 := bstep (se 1 (by rfl) ⟨1848389, by rfl⟩ : syracuseStep 2464519 = 3696779) B3696779
theorem B3286025 : Blo 2189435 3286025 := bstep (se 2 (by rfl) ⟨1232259, by rfl⟩ : syracuseStep 3286025 = 2464519) B2464519
theorem B2190683 : Blo 2189435 2190683 := bstep (se 1 (by rfl) ⟨1643012, by rfl⟩ : syracuseStep 2190683 = 3286025) B3286025
theorem B11090357 : Blo 2189435 11090357 := bbase (se 5 (by rfl) ⟨519860, by rfl⟩ : syracuseStep 11090357 = 1039721) (by norm_num)
theorem B7393571 : Blo 2189435 7393571 := bstep (se 1 (by rfl) ⟨5545178, by rfl⟩ : syracuseStep 7393571 = 11090357) B11090357
theorem B4929047 : Blo 2189435 4929047 := bstep (se 1 (by rfl) ⟨3696785, by rfl⟩ : syracuseStep 4929047 = 7393571) B7393571
theorem B3286031 : Blo 2189435 3286031 := bstep (se 1 (by rfl) ⟨2464523, by rfl⟩ : syracuseStep 3286031 = 4929047) B4929047
theorem B2190687 : Blo 2189435 2190687 := bstep (se 1 (by rfl) ⟨1643015, by rfl⟩ : syracuseStep 2190687 = 3286031) B3286031
theorem B3286037 : Blo 2189435 3286037 := bbase (se 6 (by rfl) ⟨77016, by rfl⟩ : syracuseStep 3286037 = 154033) (by norm_num)
theorem B2190691 : Blo 2189435 2190691 := bstep (se 1 (by rfl) ⟨1643018, by rfl⟩ : syracuseStep 2190691 = 3286037) B3286037
theorem B5335421 : Blo 2189435 5335421 := bbase (se 3 (by rfl) ⟨1000391, by rfl⟩ : syracuseStep 5335421 = 2000783) (by norm_num)
theorem B56911157 : Blo 2189435 56911157 := bstep (se 5 (by rfl) ⟨2667710, by rfl⟩ : syracuseStep 56911157 = 5335421) B5335421
theorem B37940771 : Blo 2189435 37940771 := bstep (se 1 (by rfl) ⟨28455578, by rfl⟩ : syracuseStep 37940771 = 56911157) B56911157
theorem B101175389 : Blo 2189435 101175389 := bstep (se 3 (by rfl) ⟨18970385, by rfl⟩ : syracuseStep 101175389 = 37940771) B37940771
theorem B67450259 : Blo 2189435 67450259 := bstep (se 1 (by rfl) ⟨50587694, by rfl⟩ : syracuseStep 67450259 = 101175389) B101175389
theorem B44966839 : Blo 2189435 44966839 := bstep (se 1 (by rfl) ⟨33725129, by rfl⟩ : syracuseStep 44966839 = 67450259) B67450259
theorem B59955785 : Blo 2189435 59955785 := bstep (se 2 (by rfl) ⟨22483419, by rfl⟩ : syracuseStep 59955785 = 44966839) B44966839
theorem B39970523 : Blo 2189435 39970523 := bstep (se 1 (by rfl) ⟨29977892, by rfl⟩ : syracuseStep 39970523 = 59955785) B59955785
theorem B106588061 : Blo 2189435 106588061 := bstep (se 3 (by rfl) ⟨19985261, by rfl⟩ : syracuseStep 106588061 = 39970523) B39970523
theorem B71058707 : Blo 2189435 71058707 := bstep (se 1 (by rfl) ⟨53294030, by rfl⟩ : syracuseStep 71058707 = 106588061) B106588061
theorem B47372471 : Blo 2189435 47372471 := bstep (se 1 (by rfl) ⟨35529353, by rfl⟩ : syracuseStep 47372471 = 71058707) B71058707
theorem B31581647 : Blo 2189435 31581647 := bstep (se 1 (by rfl) ⟨23686235, by rfl⟩ : syracuseStep 31581647 = 47372471) B47372471
theorem B21054431 : Blo 2189435 21054431 := bstep (se 1 (by rfl) ⟨15790823, by rfl⟩ : syracuseStep 21054431 = 31581647) B31581647
theorem B14036287 : Blo 2189435 14036287 := bstep (se 1 (by rfl) ⟨10527215, by rfl⟩ : syracuseStep 14036287 = 21054431) B21054431
theorem B18715049 : Blo 2189435 18715049 := bstep (se 2 (by rfl) ⟨7018143, by rfl⟩ : syracuseStep 18715049 = 14036287) B14036287
theorem B12476699 : Blo 2189435 12476699 := bstep (se 1 (by rfl) ⟨9357524, by rfl⟩ : syracuseStep 12476699 = 18715049) B18715049
theorem B8317799 : Blo 2189435 8317799 := bstep (se 1 (by rfl) ⟨6238349, by rfl⟩ : syracuseStep 8317799 = 12476699) B12476699
theorem B5545199 : Blo 2189435 5545199 := bstep (se 1 (by rfl) ⟨4158899, by rfl⟩ : syracuseStep 5545199 = 8317799) B8317799
theorem B3696799 : Blo 2189435 3696799 := bstep (se 1 (by rfl) ⟨2772599, by rfl⟩ : syracuseStep 3696799 = 5545199) B5545199
theorem B4929065 : Blo 2189435 4929065 := bstep (se 2 (by rfl) ⟨1848399, by rfl⟩ : syracuseStep 4929065 = 3696799) B3696799
theorem B3286043 : Blo 2189435 3286043 := bstep (se 1 (by rfl) ⟨2464532, by rfl⟩ : syracuseStep 3286043 = 4929065) B4929065
theorem B2190695 : Blo 2189435 2190695 := bstep (se 1 (by rfl) ⟨1643021, by rfl⟩ : syracuseStep 2190695 = 3286043) B3286043
theorem B2464537 : Blo 2189435 2464537 := bbase (se 2 (by rfl) ⟨924201, by rfl⟩ : syracuseStep 2464537 = 1848403) (by norm_num)
theorem B3286049 : Blo 2189435 3286049 := bstep (se 2 (by rfl) ⟨1232268, by rfl⟩ : syracuseStep 3286049 = 2464537) B2464537
theorem B2190699 : Blo 2189435 2190699 := bstep (se 1 (by rfl) ⟨1643024, by rfl⟩ : syracuseStep 2190699 = 3286049) B3286049
theorem B8317829 : Blo 2189435 8317829 := bbase (se 4 (by rfl) ⟨779796, by rfl⟩ : syracuseStep 8317829 = 1559593) (by norm_num)
theorem B5545219 : Blo 2189435 5545219 := bstep (se 1 (by rfl) ⟨4158914, by rfl⟩ : syracuseStep 5545219 = 8317829) B8317829
theorem B7393625 : Blo 2189435 7393625 := bstep (se 2 (by rfl) ⟨2772609, by rfl⟩ : syracuseStep 7393625 = 5545219) B5545219
theorem B4929083 : Blo 2189435 4929083 := bstep (se 1 (by rfl) ⟨3696812, by rfl⟩ : syracuseStep 4929083 = 7393625) B7393625
theorem B3286055 : Blo 2189435 3286055 := bstep (se 1 (by rfl) ⟨2464541, by rfl⟩ : syracuseStep 3286055 = 4929083) B4929083
theorem B2190703 : Blo 2189435 2190703 := bstep (se 1 (by rfl) ⟨1643027, by rfl⟩ : syracuseStep 2190703 = 3286055) B3286055
theorem B3286061 : Blo 2189435 3286061 := bbase (se 3 (by rfl) ⟨616136, by rfl⟩ : syracuseStep 3286061 = 1232273) (by norm_num)
theorem B2190707 : Blo 2189435 2190707 := bstep (se 1 (by rfl) ⟨1643030, by rfl⟩ : syracuseStep 2190707 = 3286061) B3286061
theorem B4929101 : Blo 2189435 4929101 := bbase (se 3 (by rfl) ⟨924206, by rfl⟩ : syracuseStep 4929101 = 1848413) (by norm_num)
theorem B3286067 : Blo 2189435 3286067 := bstep (se 1 (by rfl) ⟨2464550, by rfl⟩ : syracuseStep 3286067 = 4929101) B4929101
theorem B2190711 : Blo 2189435 2190711 := bstep (se 1 (by rfl) ⟨1643033, by rfl⟩ : syracuseStep 2190711 = 3286067) B3286067
theorem B2772625 : Blo 2189435 2772625 := bbase (se 2 (by rfl) ⟨1039734, by rfl⟩ : syracuseStep 2772625 = 2079469) (by norm_num)
theorem B3696833 : Blo 2189435 3696833 := bstep (se 2 (by rfl) ⟨1386312, by rfl⟩ : syracuseStep 3696833 = 2772625) B2772625
theorem B2464555 : Blo 2189435 2464555 := bstep (se 1 (by rfl) ⟨1848416, by rfl⟩ : syracuseStep 2464555 = 3696833) B3696833
theorem B3286073 : Blo 2189435 3286073 := bstep (se 2 (by rfl) ⟨1232277, by rfl⟩ : syracuseStep 3286073 = 2464555) B2464555
theorem B2190715 : Blo 2189435 2190715 := bstep (se 1 (by rfl) ⟨1643036, by rfl⟩ : syracuseStep 2190715 = 3286073) B3286073
theorem B4678813 : Blo 2189435 4678813 := bbase (se 3 (by rfl) ⟨877277, by rfl⟩ : syracuseStep 4678813 = 1754555) (by norm_num)
theorem B24953669 : Blo 2189435 24953669 := bstep (se 4 (by rfl) ⟨2339406, by rfl⟩ : syracuseStep 24953669 = 4678813) B4678813
theorem B16635779 : Blo 2189435 16635779 := bstep (se 1 (by rfl) ⟨12476834, by rfl⟩ : syracuseStep 16635779 = 24953669) B24953669
theorem B11090519 : Blo 2189435 11090519 := bstep (se 1 (by rfl) ⟨8317889, by rfl⟩ : syracuseStep 11090519 = 16635779) B16635779
theorem B7393679 : Blo 2189435 7393679 := bstep (se 1 (by rfl) ⟨5545259, by rfl⟩ : syracuseStep 7393679 = 11090519) B11090519
theorem B4929119 : Blo 2189435 4929119 := bstep (se 1 (by rfl) ⟨3696839, by rfl⟩ : syracuseStep 4929119 = 7393679) B7393679
theorem B3286079 : Blo 2189435 3286079 := bstep (se 1 (by rfl) ⟨2464559, by rfl⟩ : syracuseStep 3286079 = 4929119) B4929119
theorem B2190719 : Blo 2189435 2190719 := bstep (se 1 (by rfl) ⟨1643039, by rfl⟩ : syracuseStep 2190719 = 3286079) B3286079
theorem B3286085 : Blo 2189435 3286085 := bbase (se 4 (by rfl) ⟨308070, by rfl⟩ : syracuseStep 3286085 = 616141) (by norm_num)
theorem B2190723 : Blo 2189435 2190723 := bstep (se 1 (by rfl) ⟨1643042, by rfl⟩ : syracuseStep 2190723 = 3286085) B3286085
theorem B3696853 : Blo 2189435 3696853 := bbase (se 7 (by rfl) ⟨43322, by rfl⟩ : syracuseStep 3696853 = 86645) (by norm_num)
theorem B4929137 : Blo 2189435 4929137 := bstep (se 2 (by rfl) ⟨1848426, by rfl⟩ : syracuseStep 4929137 = 3696853) B3696853
theorem B3286091 : Blo 2189435 3286091 := bstep (se 1 (by rfl) ⟨2464568, by rfl⟩ : syracuseStep 3286091 = 4929137) B4929137
theorem B2190727 : Blo 2189435 2190727 := bstep (se 1 (by rfl) ⟨1643045, by rfl⟩ : syracuseStep 2190727 = 3286091) B3286091
theorem B2464573 : Blo 2189435 2464573 := bbase (se 3 (by rfl) ⟨462107, by rfl⟩ : syracuseStep 2464573 = 924215) (by norm_num)
theorem B3286097 : Blo 2189435 3286097 := bstep (se 2 (by rfl) ⟨1232286, by rfl⟩ : syracuseStep 3286097 = 2464573) B2464573
theorem B2190731 : Blo 2189435 2190731 := bstep (se 1 (by rfl) ⟨1643048, by rfl⟩ : syracuseStep 2190731 = 3286097) B3286097
theorem B7393733 : Blo 2189435 7393733 := bbase (se 4 (by rfl) ⟨693162, by rfl⟩ : syracuseStep 7393733 = 1386325) (by norm_num)
theorem B4929155 : Blo 2189435 4929155 := bstep (se 1 (by rfl) ⟨3696866, by rfl⟩ : syracuseStep 4929155 = 7393733) B7393733
theorem B3286103 : Blo 2189435 3286103 := bstep (se 1 (by rfl) ⟨2464577, by rfl⟩ : syracuseStep 3286103 = 4929155) B4929155
theorem B2190735 : Blo 2189435 2190735 := bstep (se 1 (by rfl) ⟨1643051, by rfl⟩ : syracuseStep 2190735 = 3286103) B3286103
theorem B3286109 : Blo 2189435 3286109 := bbase (se 3 (by rfl) ⟨616145, by rfl⟩ : syracuseStep 3286109 = 1232291) (by norm_num)
theorem B2190739 : Blo 2189435 2190739 := bstep (se 1 (by rfl) ⟨1643054, by rfl⟩ : syracuseStep 2190739 = 3286109) B3286109
theorem B4929173 : Blo 2189435 4929173 := bbase (se 6 (by rfl) ⟨115527, by rfl⟩ : syracuseStep 4929173 = 231055) (by norm_num)
theorem B3286115 : Blo 2189435 3286115 := bstep (se 1 (by rfl) ⟨2464586, by rfl⟩ : syracuseStep 3286115 = 4929173) B4929173
theorem B2190743 : Blo 2189435 2190743 := bstep (se 1 (by rfl) ⟨1643057, by rfl⟩ : syracuseStep 2190743 = 3286115) B3286115
theorem B2339437 : Blo 2189435 2339437 := bbase (se 3 (by rfl) ⟨438644, by rfl⟩ : syracuseStep 2339437 = 877289) (by norm_num)
theorem B3119249 : Blo 2189435 3119249 := bstep (se 2 (by rfl) ⟨1169718, by rfl⟩ : syracuseStep 3119249 = 2339437) B2339437
theorem B8317997 : Blo 2189435 8317997 := bstep (se 3 (by rfl) ⟨1559624, by rfl⟩ : syracuseStep 8317997 = 3119249) B3119249
theorem B5545331 : Blo 2189435 5545331 := bstep (se 1 (by rfl) ⟨4158998, by rfl⟩ : syracuseStep 5545331 = 8317997) B8317997
theorem B3696887 : Blo 2189435 3696887 := bstep (se 1 (by rfl) ⟨2772665, by rfl⟩ : syracuseStep 3696887 = 5545331) B5545331
theorem B2464591 : Blo 2189435 2464591 := bstep (se 1 (by rfl) ⟨1848443, by rfl⟩ : syracuseStep 2464591 = 3696887) B3696887
theorem B3286121 : Blo 2189435 3286121 := bstep (se 2 (by rfl) ⟨1232295, by rfl⟩ : syracuseStep 3286121 = 2464591) B2464591
theorem B2190747 : Blo 2189435 2190747 := bstep (se 1 (by rfl) ⟨1643060, by rfl⟩ : syracuseStep 2190747 = 3286121) B3286121
theorem B14989333 : Blo 2189435 14989333 := bbase (se 6 (by rfl) ⟨351312, by rfl⟩ : syracuseStep 14989333 = 702625) (by norm_num)
theorem B19985777 : Blo 2189435 19985777 := bstep (se 2 (by rfl) ⟨7494666, by rfl⟩ : syracuseStep 19985777 = 14989333) B14989333
theorem B13323851 : Blo 2189435 13323851 := bstep (se 1 (by rfl) ⟨9992888, by rfl⟩ : syracuseStep 13323851 = 19985777) B19985777
theorem B8882567 : Blo 2189435 8882567 := bstep (se 1 (by rfl) ⟨6661925, by rfl⟩ : syracuseStep 8882567 = 13323851) B13323851
theorem B5921711 : Blo 2189435 5921711 := bstep (se 1 (by rfl) ⟨4441283, by rfl⟩ : syracuseStep 5921711 = 8882567) B8882567
theorem B3947807 : Blo 2189435 3947807 := bstep (se 1 (by rfl) ⟨2960855, by rfl⟩ : syracuseStep 3947807 = 5921711) B5921711
theorem B2631871 : Blo 2189435 2631871 := bstep (se 1 (by rfl) ⟨1973903, by rfl⟩ : syracuseStep 2631871 = 3947807) B3947807
theorem B14036645 : Blo 2189435 14036645 := bstep (se 4 (by rfl) ⟨1315935, by rfl⟩ : syracuseStep 14036645 = 2631871) B2631871
theorem B9357763 : Blo 2189435 9357763 := bstep (se 1 (by rfl) ⟨7018322, by rfl⟩ : syracuseStep 9357763 = 14036645) B14036645
theorem B12477017 : Blo 2189435 12477017 := bstep (se 2 (by rfl) ⟨4678881, by rfl⟩ : syracuseStep 12477017 = 9357763) B9357763
theorem B8318011 : Blo 2189435 8318011 := bstep (se 1 (by rfl) ⟨6238508, by rfl⟩ : syracuseStep 8318011 = 12477017) B12477017
theorem B11090681 : Blo 2189435 11090681 := bstep (se 2 (by rfl) ⟨4159005, by rfl⟩ : syracuseStep 11090681 = 8318011) B8318011
theorem B7393787 : Blo 2189435 7393787 := bstep (se 1 (by rfl) ⟨5545340, by rfl⟩ : syracuseStep 7393787 = 11090681) B11090681
theorem B4929191 : Blo 2189435 4929191 := bstep (se 1 (by rfl) ⟨3696893, by rfl⟩ : syracuseStep 4929191 = 7393787) B7393787
theorem B3286127 : Blo 2189435 3286127 := bstep (se 1 (by rfl) ⟨2464595, by rfl⟩ : syracuseStep 3286127 = 4929191) B4929191
theorem B2190751 : Blo 2189435 2190751 := bstep (se 1 (by rfl) ⟨1643063, by rfl⟩ : syracuseStep 2190751 = 3286127) B3286127
theorem B3286133 : Blo 2189435 3286133 := bbase (se 5 (by rfl) ⟨154037, by rfl⟩ : syracuseStep 3286133 = 308075) (by norm_num)
theorem B2190755 : Blo 2189435 2190755 := bstep (se 1 (by rfl) ⟨1643066, by rfl⟩ : syracuseStep 2190755 = 3286133) B3286133
theorem B4159021 : Blo 2189435 4159021 := bbase (se 3 (by rfl) ⟨779816, by rfl⟩ : syracuseStep 4159021 = 1559633) (by norm_num)
theorem B5545361 : Blo 2189435 5545361 := bstep (se 2 (by rfl) ⟨2079510, by rfl⟩ : syracuseStep 5545361 = 4159021) B4159021
theorem B3696907 : Blo 2189435 3696907 := bstep (se 1 (by rfl) ⟨2772680, by rfl⟩ : syracuseStep 3696907 = 5545361) B5545361
theorem B4929209 : Blo 2189435 4929209 := bstep (se 2 (by rfl) ⟨1848453, by rfl⟩ : syracuseStep 4929209 = 3696907) B3696907
theorem B3286139 : Blo 2189435 3286139 := bstep (se 1 (by rfl) ⟨2464604, by rfl⟩ : syracuseStep 3286139 = 4929209) B4929209
theorem B2190759 : Blo 2189435 2190759 := bstep (se 1 (by rfl) ⟨1643069, by rfl⟩ : syracuseStep 2190759 = 3286139) B3286139
theorem B2464609 : Blo 2189435 2464609 := bbase (se 2 (by rfl) ⟨924228, by rfl⟩ : syracuseStep 2464609 = 1848457) (by norm_num)
theorem B3286145 : Blo 2189435 3286145 := bstep (se 2 (by rfl) ⟨1232304, by rfl⟩ : syracuseStep 3286145 = 2464609) B2464609
theorem B2190763 : Blo 2189435 2190763 := bstep (se 1 (by rfl) ⟨1643072, by rfl⟩ : syracuseStep 2190763 = 3286145) B3286145
theorem B5545381 : Blo 2189435 5545381 := bbase (se 4 (by rfl) ⟨519879, by rfl⟩ : syracuseStep 5545381 = 1039759) (by norm_num)
theorem B7393841 : Blo 2189435 7393841 := bstep (se 2 (by rfl) ⟨2772690, by rfl⟩ : syracuseStep 7393841 = 5545381) B5545381
theorem B4929227 : Blo 2189435 4929227 := bstep (se 1 (by rfl) ⟨3696920, by rfl⟩ : syracuseStep 4929227 = 7393841) B7393841
theorem B3286151 : Blo 2189435 3286151 := bstep (se 1 (by rfl) ⟨2464613, by rfl⟩ : syracuseStep 3286151 = 4929227) B4929227
theorem B2190767 : Blo 2189435 2190767 := bstep (se 1 (by rfl) ⟨1643075, by rfl⟩ : syracuseStep 2190767 = 3286151) B3286151
theorem B3286157 : Blo 2189435 3286157 := bbase (se 3 (by rfl) ⟨616154, by rfl⟩ : syracuseStep 3286157 = 1232309) (by norm_num)
theorem B2190771 : Blo 2189435 2190771 := bstep (se 1 (by rfl) ⟨1643078, by rfl⟩ : syracuseStep 2190771 = 3286157) B3286157
theorem B4929245 : Blo 2189435 4929245 := bbase (se 3 (by rfl) ⟨924233, by rfl⟩ : syracuseStep 4929245 = 1848467) (by norm_num)
theorem B3286163 : Blo 2189435 3286163 := bstep (se 1 (by rfl) ⟨2464622, by rfl⟩ : syracuseStep 3286163 = 4929245) B4929245
theorem B2190775 : Blo 2189435 2190775 := bstep (se 1 (by rfl) ⟨1643081, by rfl⟩ : syracuseStep 2190775 = 3286163) B3286163
theorem B3696941 : Blo 2189435 3696941 := bbase (se 3 (by rfl) ⟨693176, by rfl⟩ : syracuseStep 3696941 = 1386353) (by norm_num)
theorem B2464627 : Blo 2189435 2464627 := bstep (se 1 (by rfl) ⟨1848470, by rfl⟩ : syracuseStep 2464627 = 3696941) B3696941
theorem B3286169 : Blo 2189435 3286169 := bstep (se 2 (by rfl) ⟨1232313, by rfl⟩ : syracuseStep 3286169 = 2464627) B2464627
theorem B2190779 : Blo 2189435 2190779 := bstep (se 1 (by rfl) ⟨1643084, by rfl⟩ : syracuseStep 2190779 = 3286169) B3286169
theorem B42110549 : Blo 2189435 42110549 := bbase (se 8 (by rfl) ⟨246741, by rfl⟩ : syracuseStep 42110549 = 493483) (by norm_num)
theorem B28073699 : Blo 2189435 28073699 := bstep (se 1 (by rfl) ⟨21055274, by rfl⟩ : syracuseStep 28073699 = 42110549) B42110549
theorem B18715799 : Blo 2189435 18715799 := bstep (se 1 (by rfl) ⟨14036849, by rfl⟩ : syracuseStep 18715799 = 28073699) B28073699
theorem B12477199 : Blo 2189435 12477199 := bstep (se 1 (by rfl) ⟨9357899, by rfl⟩ : syracuseStep 12477199 = 18715799) B18715799
theorem B16636265 : Blo 2189435 16636265 := bstep (se 2 (by rfl) ⟨6238599, by rfl⟩ : syracuseStep 16636265 = 12477199) B12477199
theorem B11090843 : Blo 2189435 11090843 := bstep (se 1 (by rfl) ⟨8318132, by rfl⟩ : syracuseStep 11090843 = 16636265) B16636265
theorem B7393895 : Blo 2189435 7393895 := bstep (se 1 (by rfl) ⟨5545421, by rfl⟩ : syracuseStep 7393895 = 11090843) B11090843
theorem B4929263 : Blo 2189435 4929263 := bstep (se 1 (by rfl) ⟨3696947, by rfl⟩ : syracuseStep 4929263 = 7393895) B7393895
theorem B3286175 : Blo 2189435 3286175 := bstep (se 1 (by rfl) ⟨2464631, by rfl⟩ : syracuseStep 3286175 = 4929263) B4929263
theorem B2190783 : Blo 2189435 2190783 := bstep (se 1 (by rfl) ⟨1643087, by rfl⟩ : syracuseStep 2190783 = 3286175) B3286175
theorem B3286181 : Blo 2189435 3286181 := bbase (se 4 (by rfl) ⟨308079, by rfl⟩ : syracuseStep 3286181 = 616159) (by norm_num)
theorem B2190787 : Blo 2189435 2190787 := bstep (se 1 (by rfl) ⟨1643090, by rfl⟩ : syracuseStep 2190787 = 3286181) B3286181
theorem B2772721 : Blo 2189435 2772721 := bbase (se 2 (by rfl) ⟨1039770, by rfl⟩ : syracuseStep 2772721 = 2079541) (by norm_num)
theorem B3696961 : Blo 2189435 3696961 := bstep (se 2 (by rfl) ⟨1386360, by rfl⟩ : syracuseStep 3696961 = 2772721) B2772721
theorem B4929281 : Blo 2189435 4929281 := bstep (se 2 (by rfl) ⟨1848480, by rfl⟩ : syracuseStep 4929281 = 3696961) B3696961
theorem B3286187 : Blo 2189435 3286187 := bstep (se 1 (by rfl) ⟨2464640, by rfl⟩ : syracuseStep 3286187 = 4929281) B4929281
theorem B2190791 : Blo 2189435 2190791 := bstep (se 1 (by rfl) ⟨1643093, by rfl⟩ : syracuseStep 2190791 = 3286187) B3286187
theorem B2464645 : Blo 2189435 2464645 := bbase (se 4 (by rfl) ⟨231060, by rfl⟩ : syracuseStep 2464645 = 462121) (by norm_num)
theorem B3286193 : Blo 2189435 3286193 := bstep (se 2 (by rfl) ⟨1232322, by rfl⟩ : syracuseStep 3286193 = 2464645) B2464645
theorem B2190795 : Blo 2189435 2190795 := bstep (se 1 (by rfl) ⟨1643096, by rfl⟩ : syracuseStep 2190795 = 3286193) B3286193
theorem B3331037 : Blo 2189435 3331037 := bbase (se 3 (by rfl) ⟨624569, by rfl⟩ : syracuseStep 3331037 = 1249139) (by norm_num)
theorem B2220691 : Blo 2189435 2220691 := bstep (se 1 (by rfl) ⟨1665518, by rfl⟩ : syracuseStep 2220691 = 3331037) B3331037
theorem B2960921 : Blo 2189435 2960921 := bstep (se 2 (by rfl) ⟨1110345, by rfl⟩ : syracuseStep 2960921 = 2220691) B2220691
theorem B7895789 : Blo 2189435 7895789 := bstep (se 3 (by rfl) ⟨1480460, by rfl⟩ : syracuseStep 7895789 = 2960921) B2960921
theorem B5263859 : Blo 2189435 5263859 := bstep (se 1 (by rfl) ⟨3947894, by rfl⟩ : syracuseStep 5263859 = 7895789) B7895789
theorem B3509239 : Blo 2189435 3509239 := bstep (se 1 (by rfl) ⟨2631929, by rfl⟩ : syracuseStep 3509239 = 5263859) B5263859
theorem B4678985 : Blo 2189435 4678985 := bstep (se 2 (by rfl) ⟨1754619, by rfl⟩ : syracuseStep 4678985 = 3509239) B3509239
theorem B3119323 : Blo 2189435 3119323 := bstep (se 1 (by rfl) ⟨2339492, by rfl⟩ : syracuseStep 3119323 = 4678985) B4678985
theorem B4159097 : Blo 2189435 4159097 := bstep (se 2 (by rfl) ⟨1559661, by rfl⟩ : syracuseStep 4159097 = 3119323) B3119323
theorem B2772731 : Blo 2189435 2772731 := bstep (se 1 (by rfl) ⟨2079548, by rfl⟩ : syracuseStep 2772731 = 4159097) B4159097
theorem B7393949 : Blo 2189435 7393949 := bstep (se 3 (by rfl) ⟨1386365, by rfl⟩ : syracuseStep 7393949 = 2772731) B2772731
theorem B4929299 : Blo 2189435 4929299 := bstep (se 1 (by rfl) ⟨3696974, by rfl⟩ : syracuseStep 4929299 = 7393949) B7393949
theorem B3286199 : Blo 2189435 3286199 := bstep (se 1 (by rfl) ⟨2464649, by rfl⟩ : syracuseStep 3286199 = 4929299) B4929299
theorem B2190799 : Blo 2189435 2190799 := bstep (se 1 (by rfl) ⟨1643099, by rfl⟩ : syracuseStep 2190799 = 3286199) B3286199
theorem B3286205 : Blo 2189435 3286205 := bbase (se 3 (by rfl) ⟨616163, by rfl⟩ : syracuseStep 3286205 = 1232327) (by norm_num)
theorem B2190803 : Blo 2189435 2190803 := bstep (se 1 (by rfl) ⟨1643102, by rfl⟩ : syracuseStep 2190803 = 3286205) B3286205
theorem B4929317 : Blo 2189435 4929317 := bbase (se 4 (by rfl) ⟨462123, by rfl⟩ : syracuseStep 4929317 = 924247) (by norm_num)
theorem B3286211 : Blo 2189435 3286211 := bstep (se 1 (by rfl) ⟨2464658, by rfl⟩ : syracuseStep 3286211 = 4929317) B4929317
theorem B2190807 : Blo 2189435 2190807 := bstep (se 1 (by rfl) ⟨1643105, by rfl⟩ : syracuseStep 2190807 = 3286211) B3286211
theorem B5545493 : Blo 2189435 5545493 := bbase (se 6 (by rfl) ⟨129972, by rfl⟩ : syracuseStep 5545493 = 259945) (by norm_num)
theorem B3696995 : Blo 2189435 3696995 := bstep (se 1 (by rfl) ⟨2772746, by rfl⟩ : syracuseStep 3696995 = 5545493) B5545493
theorem B2464663 : Blo 2189435 2464663 := bstep (se 1 (by rfl) ⟨1848497, by rfl⟩ : syracuseStep 2464663 = 3696995) B3696995
theorem B3286217 : Blo 2189435 3286217 := bstep (se 2 (by rfl) ⟨1232331, by rfl⟩ : syracuseStep 3286217 = 2464663) B2464663
theorem B2190811 : Blo 2189435 2190811 := bstep (se 1 (by rfl) ⟨1643108, by rfl⟩ : syracuseStep 2190811 = 3286217) B3286217
theorem B9358037 : Blo 2189435 9358037 := bbase (se 7 (by rfl) ⟨109664, by rfl⟩ : syracuseStep 9358037 = 219329) (by norm_num)
theorem B6238691 : Blo 2189435 6238691 := bstep (se 1 (by rfl) ⟨4679018, by rfl⟩ : syracuseStep 6238691 = 9358037) B9358037
theorem B4159127 : Blo 2189435 4159127 := bstep (se 1 (by rfl) ⟨3119345, by rfl⟩ : syracuseStep 4159127 = 6238691) B6238691
theorem B11091005 : Blo 2189435 11091005 := bstep (se 3 (by rfl) ⟨2079563, by rfl⟩ : syracuseStep 11091005 = 4159127) B4159127
theorem B7394003 : Blo 2189435 7394003 := bstep (se 1 (by rfl) ⟨5545502, by rfl⟩ : syracuseStep 7394003 = 11091005) B11091005
theorem B4929335 : Blo 2189435 4929335 := bstep (se 1 (by rfl) ⟨3697001, by rfl⟩ : syracuseStep 4929335 = 7394003) B7394003
theorem B3286223 : Blo 2189435 3286223 := bstep (se 1 (by rfl) ⟨2464667, by rfl⟩ : syracuseStep 3286223 = 4929335) B4929335
theorem B2190815 : Blo 2189435 2190815 := bstep (se 1 (by rfl) ⟨1643111, by rfl⟩ : syracuseStep 2190815 = 3286223) B3286223
theorem B3286229 : Blo 2189435 3286229 := bbase (se 7 (by rfl) ⟨38510, by rfl⟩ : syracuseStep 3286229 = 77021) (by norm_num)
theorem B2190819 : Blo 2189435 2190819 := bstep (se 1 (by rfl) ⟨1643114, by rfl⟩ : syracuseStep 2190819 = 3286229) B3286229
theorem B3119357 : Blo 2189435 3119357 := bbase (se 3 (by rfl) ⟨584879, by rfl⟩ : syracuseStep 3119357 = 1169759) (by norm_num)
theorem B8318285 : Blo 2189435 8318285 := bstep (se 3 (by rfl) ⟨1559678, by rfl⟩ : syracuseStep 8318285 = 3119357) B3119357
theorem B5545523 : Blo 2189435 5545523 := bstep (se 1 (by rfl) ⟨4159142, by rfl⟩ : syracuseStep 5545523 = 8318285) B8318285
theorem B3697015 : Blo 2189435 3697015 := bstep (se 1 (by rfl) ⟨2772761, by rfl⟩ : syracuseStep 3697015 = 5545523) B5545523
theorem B4929353 : Blo 2189435 4929353 := bstep (se 2 (by rfl) ⟨1848507, by rfl⟩ : syracuseStep 4929353 = 3697015) B3697015
theorem B3286235 : Blo 2189435 3286235 := bstep (se 1 (by rfl) ⟨2464676, by rfl⟩ : syracuseStep 3286235 = 4929353) B4929353
theorem B2190823 : Blo 2189435 2190823 := bstep (se 1 (by rfl) ⟨1643117, by rfl⟩ : syracuseStep 2190823 = 3286235) B3286235
theorem B2464681 : Blo 2189435 2464681 := bbase (se 2 (by rfl) ⟨924255, by rfl⟩ : syracuseStep 2464681 = 1848511) (by norm_num)
theorem B3286241 : Blo 2189435 3286241 := bstep (se 2 (by rfl) ⟨1232340, by rfl⟩ : syracuseStep 3286241 = 2464681) B2464681
theorem B2190827 : Blo 2189435 2190827 := bstep (se 1 (by rfl) ⟨1643120, by rfl⟩ : syracuseStep 2190827 = 3286241) B3286241
theorem B9993253 : Blo 2189435 9993253 := bbase (se 4 (by rfl) ⟨936867, by rfl⟩ : syracuseStep 9993253 = 1873735) (by norm_num)
theorem B13324337 : Blo 2189435 13324337 := bstep (se 2 (by rfl) ⟨4996626, by rfl⟩ : syracuseStep 13324337 = 9993253) B9993253
theorem B8882891 : Blo 2189435 8882891 := bstep (se 1 (by rfl) ⟨6662168, by rfl⟩ : syracuseStep 8882891 = 13324337) B13324337
theorem B5921927 : Blo 2189435 5921927 := bstep (se 1 (by rfl) ⟨4441445, by rfl⟩ : syracuseStep 5921927 = 8882891) B8882891
theorem B3947951 : Blo 2189435 3947951 := bstep (se 1 (by rfl) ⟨2960963, by rfl⟩ : syracuseStep 3947951 = 5921927) B5921927
theorem B10527869 : Blo 2189435 10527869 := bstep (se 3 (by rfl) ⟨1973975, by rfl⟩ : syracuseStep 10527869 = 3947951) B3947951
theorem B7018579 : Blo 2189435 7018579 := bstep (se 1 (by rfl) ⟨5263934, by rfl⟩ : syracuseStep 7018579 = 10527869) B10527869
theorem B9358105 : Blo 2189435 9358105 := bstep (se 2 (by rfl) ⟨3509289, by rfl⟩ : syracuseStep 9358105 = 7018579) B7018579
theorem B12477473 : Blo 2189435 12477473 := bstep (se 2 (by rfl) ⟨4679052, by rfl⟩ : syracuseStep 12477473 = 9358105) B9358105
theorem B8318315 : Blo 2189435 8318315 := bstep (se 1 (by rfl) ⟨6238736, by rfl⟩ : syracuseStep 8318315 = 12477473) B12477473
theorem B5545543 : Blo 2189435 5545543 := bstep (se 1 (by rfl) ⟨4159157, by rfl⟩ : syracuseStep 5545543 = 8318315) B8318315
theorem B7394057 : Blo 2189435 7394057 := bstep (se 2 (by rfl) ⟨2772771, by rfl⟩ : syracuseStep 7394057 = 5545543) B5545543
theorem B4929371 : Blo 2189435 4929371 := bstep (se 1 (by rfl) ⟨3697028, by rfl⟩ : syracuseStep 4929371 = 7394057) B7394057
theorem B3286247 : Blo 2189435 3286247 := bstep (se 1 (by rfl) ⟨2464685, by rfl⟩ : syracuseStep 3286247 = 4929371) B4929371
theorem B2190831 : Blo 2189435 2190831 := bstep (se 1 (by rfl) ⟨1643123, by rfl⟩ : syracuseStep 2190831 = 3286247) B3286247
theorem B3286253 : Blo 2189435 3286253 := bbase (se 3 (by rfl) ⟨616172, by rfl⟩ : syracuseStep 3286253 = 1232345) (by norm_num)
theorem B2190835 : Blo 2189435 2190835 := bstep (se 1 (by rfl) ⟨1643126, by rfl⟩ : syracuseStep 2190835 = 3286253) B3286253
theorem B4929389 : Blo 2189435 4929389 := bbase (se 3 (by rfl) ⟨924260, by rfl⟩ : syracuseStep 4929389 = 1848521) (by norm_num)
theorem B3286259 : Blo 2189435 3286259 := bstep (se 1 (by rfl) ⟨2464694, by rfl⟩ : syracuseStep 3286259 = 4929389) B4929389
theorem B2190839 : Blo 2189435 2190839 := bstep (se 1 (by rfl) ⟨1643129, by rfl⟩ : syracuseStep 2190839 = 3286259) B3286259
theorem B4159181 : Blo 2189435 4159181 := bbase (se 3 (by rfl) ⟨779846, by rfl⟩ : syracuseStep 4159181 = 1559693) (by norm_num)
theorem B2772787 : Blo 2189435 2772787 := bstep (se 1 (by rfl) ⟨2079590, by rfl⟩ : syracuseStep 2772787 = 4159181) B4159181
theorem B3697049 : Blo 2189435 3697049 := bstep (se 2 (by rfl) ⟨1386393, by rfl⟩ : syracuseStep 3697049 = 2772787) B2772787
theorem B2464699 : Blo 2189435 2464699 := bstep (se 1 (by rfl) ⟨1848524, by rfl⟩ : syracuseStep 2464699 = 3697049) B3697049
theorem B3286265 : Blo 2189435 3286265 := bstep (se 2 (by rfl) ⟨1232349, by rfl⟩ : syracuseStep 3286265 = 2464699) B2464699
theorem B2190843 : Blo 2189435 2190843 := bstep (se 1 (by rfl) ⟨1643132, by rfl⟩ : syracuseStep 2190843 = 3286265) B3286265
theorem B4441477 : Blo 2189435 4441477 := bbase (se 4 (by rfl) ⟨416388, by rfl⟩ : syracuseStep 4441477 = 832777) (by norm_num)
theorem B5921969 : Blo 2189435 5921969 := bstep (se 2 (by rfl) ⟨2220738, by rfl⟩ : syracuseStep 5921969 = 4441477) B4441477
theorem B15791917 : Blo 2189435 15791917 := bstep (se 3 (by rfl) ⟨2960984, by rfl⟩ : syracuseStep 15791917 = 5921969) B5921969
theorem B21055889 : Blo 2189435 21055889 := bstep (se 2 (by rfl) ⟨7895958, by rfl⟩ : syracuseStep 21055889 = 15791917) B15791917
theorem B56149037 : Blo 2189435 56149037 := bstep (se 3 (by rfl) ⟨10527944, by rfl⟩ : syracuseStep 56149037 = 21055889) B21055889
theorem B37432691 : Blo 2189435 37432691 := bstep (se 1 (by rfl) ⟨28074518, by rfl⟩ : syracuseStep 37432691 = 56149037) B56149037
theorem B24955127 : Blo 2189435 24955127 := bstep (se 1 (by rfl) ⟨18716345, by rfl⟩ : syracuseStep 24955127 = 37432691) B37432691
theorem B16636751 : Blo 2189435 16636751 := bstep (se 1 (by rfl) ⟨12477563, by rfl⟩ : syracuseStep 16636751 = 24955127) B24955127
theorem B11091167 : Blo 2189435 11091167 := bstep (se 1 (by rfl) ⟨8318375, by rfl⟩ : syracuseStep 11091167 = 16636751) B16636751
theorem B7394111 : Blo 2189435 7394111 := bstep (se 1 (by rfl) ⟨5545583, by rfl⟩ : syracuseStep 7394111 = 11091167) B11091167
theorem B4929407 : Blo 2189435 4929407 := bstep (se 1 (by rfl) ⟨3697055, by rfl⟩ : syracuseStep 4929407 = 7394111) B7394111
theorem B3286271 : Blo 2189435 3286271 := bstep (se 1 (by rfl) ⟨2464703, by rfl⟩ : syracuseStep 3286271 = 4929407) B4929407
theorem B2190847 : Blo 2189435 2190847 := bstep (se 1 (by rfl) ⟨1643135, by rfl⟩ : syracuseStep 2190847 = 3286271) B3286271
theorem B3286277 : Blo 2189435 3286277 := bbase (se 4 (by rfl) ⟨308088, by rfl⟩ : syracuseStep 3286277 = 616177) (by norm_num)
theorem B2190851 : Blo 2189435 2190851 := bstep (se 1 (by rfl) ⟨1643138, by rfl⟩ : syracuseStep 2190851 = 3286277) B3286277
theorem B3697069 : Blo 2189435 3697069 := bbase (se 3 (by rfl) ⟨693200, by rfl⟩ : syracuseStep 3697069 = 1386401) (by norm_num)
theorem B4929425 : Blo 2189435 4929425 := bstep (se 2 (by rfl) ⟨1848534, by rfl⟩ : syracuseStep 4929425 = 3697069) B3697069
theorem B3286283 : Blo 2189435 3286283 := bstep (se 1 (by rfl) ⟨2464712, by rfl⟩ : syracuseStep 3286283 = 4929425) B4929425
theorem B2190855 : Blo 2189435 2190855 := bstep (se 1 (by rfl) ⟨1643141, by rfl⟩ : syracuseStep 2190855 = 3286283) B3286283
theorem B2464717 : Blo 2189435 2464717 := bbase (se 3 (by rfl) ⟨462134, by rfl⟩ : syracuseStep 2464717 = 924269) (by norm_num)
theorem B3286289 : Blo 2189435 3286289 := bstep (se 2 (by rfl) ⟨1232358, by rfl⟩ : syracuseStep 3286289 = 2464717) B2464717
theorem B2190859 : Blo 2189435 2190859 := bstep (se 1 (by rfl) ⟨1643144, by rfl⟩ : syracuseStep 2190859 = 3286289) B3286289
theorem B7394165 : Blo 2189435 7394165 := bbase (se 5 (by rfl) ⟨346601, by rfl⟩ : syracuseStep 7394165 = 693203) (by norm_num)
theorem B4929443 : Blo 2189435 4929443 := bstep (se 1 (by rfl) ⟨3697082, by rfl⟩ : syracuseStep 4929443 = 7394165) B7394165
theorem B3286295 : Blo 2189435 3286295 := bstep (se 1 (by rfl) ⟨2464721, by rfl⟩ : syracuseStep 3286295 = 4929443) B4929443
theorem B2190863 : Blo 2189435 2190863 := bstep (se 1 (by rfl) ⟨1643147, by rfl⟩ : syracuseStep 2190863 = 3286295) B3286295
theorem B3286301 : Blo 2189435 3286301 := bbase (se 3 (by rfl) ⟨616181, by rfl⟩ : syracuseStep 3286301 = 1232363) (by norm_num)
theorem B2190867 : Blo 2189435 2190867 := bstep (se 1 (by rfl) ⟨1643150, by rfl⟩ : syracuseStep 2190867 = 3286301) B3286301
theorem B4929461 : Blo 2189435 4929461 := bbase (se 5 (by rfl) ⟨231068, by rfl⟩ : syracuseStep 4929461 = 462137) (by norm_num)
theorem B3286307 : Blo 2189435 3286307 := bstep (se 1 (by rfl) ⟨2464730, by rfl⟩ : syracuseStep 3286307 = 4929461) B4929461
theorem B2190871 : Blo 2189435 2190871 := bstep (se 1 (by rfl) ⟨1643153, by rfl⟩ : syracuseStep 2190871 = 3286307) B3286307
theorem B10268005 : Blo 2189435 10268005 := bbase (se 4 (by rfl) ⟨962625, by rfl⟩ : syracuseStep 10268005 = 1925251) (by norm_num)
theorem B13690673 : Blo 2189435 13690673 := bstep (se 2 (by rfl) ⟨5134002, by rfl⟩ : syracuseStep 13690673 = 10268005) B10268005
theorem B9127115 : Blo 2189435 9127115 := bstep (se 1 (by rfl) ⟨6845336, by rfl⟩ : syracuseStep 9127115 = 13690673) B13690673
theorem B6084743 : Blo 2189435 6084743 := bstep (se 1 (by rfl) ⟨4563557, by rfl⟩ : syracuseStep 6084743 = 9127115) B9127115
theorem B16225981 : Blo 2189435 16225981 := bstep (se 3 (by rfl) ⟨3042371, by rfl⟩ : syracuseStep 16225981 = 6084743) B6084743
theorem B86538565 : Blo 2189435 86538565 := bstep (se 4 (by rfl) ⟨8112990, by rfl⟩ : syracuseStep 86538565 = 16225981) B16225981
theorem B115384753 : Blo 2189435 115384753 := bstep (se 2 (by rfl) ⟨43269282, by rfl⟩ : syracuseStep 115384753 = 86538565) B86538565
theorem B153846337 : Blo 2189435 153846337 := bstep (se 2 (by rfl) ⟨57692376, by rfl⟩ : syracuseStep 153846337 = 115384753) B115384753
theorem B205128449 : Blo 2189435 205128449 := bstep (se 2 (by rfl) ⟨76923168, by rfl⟩ : syracuseStep 205128449 = 153846337) B153846337
theorem B136752299 : Blo 2189435 136752299 := bstep (se 1 (by rfl) ⟨102564224, by rfl⟩ : syracuseStep 136752299 = 205128449) B205128449
theorem B91168199 : Blo 2189435 91168199 := bstep (se 1 (by rfl) ⟨68376149, by rfl⟩ : syracuseStep 91168199 = 136752299) B136752299
theorem B60778799 : Blo 2189435 60778799 := bstep (se 1 (by rfl) ⟨45584099, by rfl⟩ : syracuseStep 60778799 = 91168199) B91168199
theorem B40519199 : Blo 2189435 40519199 := bstep (se 1 (by rfl) ⟨30389399, by rfl⟩ : syracuseStep 40519199 = 60778799) B60778799
theorem B27012799 : Blo 2189435 27012799 := bstep (se 1 (by rfl) ⟨20259599, by rfl⟩ : syracuseStep 27012799 = 40519199) B40519199
theorem B36017065 : Blo 2189435 36017065 := bstep (se 2 (by rfl) ⟨13506399, by rfl⟩ : syracuseStep 36017065 = 27012799) B27012799
theorem B192091013 : Blo 2189435 192091013 := bstep (se 4 (by rfl) ⟨18008532, by rfl⟩ : syracuseStep 192091013 = 36017065) B36017065
theorem B128060675 : Blo 2189435 128060675 := bstep (se 1 (by rfl) ⟨96045506, by rfl⟩ : syracuseStep 128060675 = 192091013) B192091013
theorem B85373783 : Blo 2189435 85373783 := bstep (se 1 (by rfl) ⟨64030337, by rfl⟩ : syracuseStep 85373783 = 128060675) B128060675
theorem B56915855 : Blo 2189435 56915855 := bstep (se 1 (by rfl) ⟨42686891, by rfl⟩ : syracuseStep 56915855 = 85373783) B85373783
theorem B37943903 : Blo 2189435 37943903 := bstep (se 1 (by rfl) ⟨28457927, by rfl⟩ : syracuseStep 37943903 = 56915855) B56915855
theorem B101183741 : Blo 2189435 101183741 := bstep (se 3 (by rfl) ⟨18971951, by rfl⟩ : syracuseStep 101183741 = 37943903) B37943903
theorem B67455827 : Blo 2189435 67455827 := bstep (se 1 (by rfl) ⟨50591870, by rfl⟩ : syracuseStep 67455827 = 101183741) B101183741
theorem B44970551 : Blo 2189435 44970551 := bstep (se 1 (by rfl) ⟨33727913, by rfl⟩ : syracuseStep 44970551 = 67455827) B67455827
theorem B29980367 : Blo 2189435 29980367 := bstep (se 1 (by rfl) ⟨22485275, by rfl⟩ : syracuseStep 29980367 = 44970551) B44970551
theorem B19986911 : Blo 2189435 19986911 := bstep (se 1 (by rfl) ⟨14990183, by rfl⟩ : syracuseStep 19986911 = 29980367) B29980367
theorem B13324607 : Blo 2189435 13324607 := bstep (se 1 (by rfl) ⟨9993455, by rfl⟩ : syracuseStep 13324607 = 19986911) B19986911
theorem B8883071 : Blo 2189435 8883071 := bstep (se 1 (by rfl) ⟨6662303, by rfl⟩ : syracuseStep 8883071 = 13324607) B13324607
theorem B5922047 : Blo 2189435 5922047 := bstep (se 1 (by rfl) ⟨4441535, by rfl⟩ : syracuseStep 5922047 = 8883071) B8883071
theorem B3948031 : Blo 2189435 3948031 := bstep (se 1 (by rfl) ⟨2961023, by rfl⟩ : syracuseStep 3948031 = 5922047) B5922047
theorem B5264041 : Blo 2189435 5264041 := bstep (se 2 (by rfl) ⟨1974015, by rfl⟩ : syracuseStep 5264041 = 3948031) B3948031
theorem B7018721 : Blo 2189435 7018721 := bstep (se 2 (by rfl) ⟨2632020, by rfl⟩ : syracuseStep 7018721 = 5264041) B5264041
theorem B4679147 : Blo 2189435 4679147 := bstep (se 1 (by rfl) ⟨3509360, by rfl⟩ : syracuseStep 4679147 = 7018721) B7018721
theorem B12477725 : Blo 2189435 12477725 := bstep (se 3 (by rfl) ⟨2339573, by rfl⟩ : syracuseStep 12477725 = 4679147) B4679147
theorem B8318483 : Blo 2189435 8318483 := bstep (se 1 (by rfl) ⟨6238862, by rfl⟩ : syracuseStep 8318483 = 12477725) B12477725
theorem B5545655 : Blo 2189435 5545655 := bstep (se 1 (by rfl) ⟨4159241, by rfl⟩ : syracuseStep 5545655 = 8318483) B8318483
theorem B3697103 : Blo 2189435 3697103 := bstep (se 1 (by rfl) ⟨2772827, by rfl⟩ : syracuseStep 3697103 = 5545655) B5545655
theorem B2464735 : Blo 2189435 2464735 := bstep (se 1 (by rfl) ⟨1848551, by rfl⟩ : syracuseStep 2464735 = 3697103) B3697103
theorem B3286313 : Blo 2189435 3286313 := bstep (se 2 (by rfl) ⟨1232367, by rfl⟩ : syracuseStep 3286313 = 2464735) B2464735
theorem B2190875 : Blo 2189435 2190875 := bstep (se 1 (by rfl) ⟨1643156, by rfl⟩ : syracuseStep 2190875 = 3286313) B3286313
theorem B2632025 : Blo 2189435 2632025 := bbase (se 2 (by rfl) ⟨987009, by rfl⟩ : syracuseStep 2632025 = 1974019) (by norm_num)
theorem B7018733 : Blo 2189435 7018733 := bstep (se 3 (by rfl) ⟨1316012, by rfl⟩ : syracuseStep 7018733 = 2632025) B2632025
theorem B4679155 : Blo 2189435 4679155 := bstep (se 1 (by rfl) ⟨3509366, by rfl⟩ : syracuseStep 4679155 = 7018733) B7018733
theorem B6238873 : Blo 2189435 6238873 := bstep (se 2 (by rfl) ⟨2339577, by rfl⟩ : syracuseStep 6238873 = 4679155) B4679155
theorem B8318497 : Blo 2189435 8318497 := bstep (se 2 (by rfl) ⟨3119436, by rfl⟩ : syracuseStep 8318497 = 6238873) B6238873
theorem B11091329 : Blo 2189435 11091329 := bstep (se 2 (by rfl) ⟨4159248, by rfl⟩ : syracuseStep 11091329 = 8318497) B8318497
theorem B7394219 : Blo 2189435 7394219 := bstep (se 1 (by rfl) ⟨5545664, by rfl⟩ : syracuseStep 7394219 = 11091329) B11091329
theorem B4929479 : Blo 2189435 4929479 := bstep (se 1 (by rfl) ⟨3697109, by rfl⟩ : syracuseStep 4929479 = 7394219) B7394219
theorem B3286319 : Blo 2189435 3286319 := bstep (se 1 (by rfl) ⟨2464739, by rfl⟩ : syracuseStep 3286319 = 4929479) B4929479
theorem B2190879 : Blo 2189435 2190879 := bstep (se 1 (by rfl) ⟨1643159, by rfl⟩ : syracuseStep 2190879 = 3286319) B3286319
theorem B3286325 : Blo 2189435 3286325 := bbase (se 5 (by rfl) ⟨154046, by rfl⟩ : syracuseStep 3286325 = 308093) (by norm_num)
theorem B2190883 : Blo 2189435 2190883 := bstep (se 1 (by rfl) ⟨1643162, by rfl⟩ : syracuseStep 2190883 = 3286325) B3286325
theorem B5545685 : Blo 2189435 5545685 := bbase (se 7 (by rfl) ⟨64988, by rfl⟩ : syracuseStep 5545685 = 129977) (by norm_num)
theorem B3697123 : Blo 2189435 3697123 := bstep (se 1 (by rfl) ⟨2772842, by rfl⟩ : syracuseStep 3697123 = 5545685) B5545685
theorem B4929497 : Blo 2189435 4929497 := bstep (se 2 (by rfl) ⟨1848561, by rfl⟩ : syracuseStep 4929497 = 3697123) B3697123
theorem B3286331 : Blo 2189435 3286331 := bstep (se 1 (by rfl) ⟨2464748, by rfl⟩ : syracuseStep 3286331 = 4929497) B4929497
theorem B2190887 : Blo 2189435 2190887 := bstep (se 1 (by rfl) ⟨1643165, by rfl⟩ : syracuseStep 2190887 = 3286331) B3286331
theorem B2464753 : Blo 2189435 2464753 := bbase (se 2 (by rfl) ⟨924282, by rfl⟩ : syracuseStep 2464753 = 1848565) (by norm_num)
theorem B3286337 : Blo 2189435 3286337 := bstep (se 2 (by rfl) ⟨1232376, by rfl⟩ : syracuseStep 3286337 = 2464753) B2464753
theorem B2190891 : Blo 2189435 2190891 := bstep (se 1 (by rfl) ⟨1643168, by rfl⟩ : syracuseStep 2190891 = 3286337) B3286337
theorem B7896133 : Blo 2189435 7896133 := bbase (se 4 (by rfl) ⟨740262, by rfl⟩ : syracuseStep 7896133 = 1480525) (by norm_num)
theorem B10528177 : Blo 2189435 10528177 := bstep (se 2 (by rfl) ⟨3948066, by rfl⟩ : syracuseStep 10528177 = 7896133) B7896133
theorem B14037569 : Blo 2189435 14037569 := bstep (se 2 (by rfl) ⟨5264088, by rfl⟩ : syracuseStep 14037569 = 10528177) B10528177
theorem B9358379 : Blo 2189435 9358379 := bstep (se 1 (by rfl) ⟨7018784, by rfl⟩ : syracuseStep 9358379 = 14037569) B14037569
theorem B6238919 : Blo 2189435 6238919 := bstep (se 1 (by rfl) ⟨4679189, by rfl⟩ : syracuseStep 6238919 = 9358379) B9358379
theorem B4159279 : Blo 2189435 4159279 := bstep (se 1 (by rfl) ⟨3119459, by rfl⟩ : syracuseStep 4159279 = 6238919) B6238919
theorem B5545705 : Blo 2189435 5545705 := bstep (se 2 (by rfl) ⟨2079639, by rfl⟩ : syracuseStep 5545705 = 4159279) B4159279
theorem B7394273 : Blo 2189435 7394273 := bstep (se 2 (by rfl) ⟨2772852, by rfl⟩ : syracuseStep 7394273 = 5545705) B5545705
theorem B4929515 : Blo 2189435 4929515 := bstep (se 1 (by rfl) ⟨3697136, by rfl⟩ : syracuseStep 4929515 = 7394273) B7394273
theorem B3286343 : Blo 2189435 3286343 := bstep (se 1 (by rfl) ⟨2464757, by rfl⟩ : syracuseStep 3286343 = 4929515) B4929515
theorem B2190895 : Blo 2189435 2190895 := bstep (se 1 (by rfl) ⟨1643171, by rfl⟩ : syracuseStep 2190895 = 3286343) B3286343
theorem B3286349 : Blo 2189435 3286349 := bbase (se 3 (by rfl) ⟨616190, by rfl⟩ : syracuseStep 3286349 = 1232381) (by norm_num)
theorem B2190899 : Blo 2189435 2190899 := bstep (se 1 (by rfl) ⟨1643174, by rfl⟩ : syracuseStep 2190899 = 3286349) B3286349
theorem B4929533 : Blo 2189435 4929533 := bbase (se 3 (by rfl) ⟨924287, by rfl⟩ : syracuseStep 4929533 = 1848575) (by norm_num)
theorem B3286355 : Blo 2189435 3286355 := bstep (se 1 (by rfl) ⟨2464766, by rfl⟩ : syracuseStep 3286355 = 4929533) B4929533
theorem B2190903 : Blo 2189435 2190903 := bstep (se 1 (by rfl) ⟨1643177, by rfl⟩ : syracuseStep 2190903 = 3286355) B3286355
theorem B3697157 : Blo 2189435 3697157 := bbase (se 4 (by rfl) ⟨346608, by rfl⟩ : syracuseStep 3697157 = 693217) (by norm_num)
theorem B2464771 : Blo 2189435 2464771 := bstep (se 1 (by rfl) ⟨1848578, by rfl⟩ : syracuseStep 2464771 = 3697157) B3697157
theorem B3286361 : Blo 2189435 3286361 := bstep (se 2 (by rfl) ⟨1232385, by rfl⟩ : syracuseStep 3286361 = 2464771) B2464771
theorem B2190907 : Blo 2189435 2190907 := bstep (se 1 (by rfl) ⟨1643180, by rfl⟩ : syracuseStep 2190907 = 3286361) B3286361
theorem B16637237 : Blo 2189435 16637237 := bbase (se 5 (by rfl) ⟨779870, by rfl⟩ : syracuseStep 16637237 = 1559741) (by norm_num)
theorem B11091491 : Blo 2189435 11091491 := bstep (se 1 (by rfl) ⟨8318618, by rfl⟩ : syracuseStep 11091491 = 16637237) B16637237
theorem B7394327 : Blo 2189435 7394327 := bstep (se 1 (by rfl) ⟨5545745, by rfl⟩ : syracuseStep 7394327 = 11091491) B11091491
theorem B4929551 : Blo 2189435 4929551 := bstep (se 1 (by rfl) ⟨3697163, by rfl⟩ : syracuseStep 4929551 = 7394327) B7394327
theorem B3286367 : Blo 2189435 3286367 := bstep (se 1 (by rfl) ⟨2464775, by rfl⟩ : syracuseStep 3286367 = 4929551) B4929551
theorem B2190911 : Blo 2189435 2190911 := bstep (se 1 (by rfl) ⟨1643183, by rfl⟩ : syracuseStep 2190911 = 3286367) B3286367
theorem B3286373 : Blo 2189435 3286373 := bbase (se 4 (by rfl) ⟨308097, by rfl⟩ : syracuseStep 3286373 = 616195) (by norm_num)
theorem B2190915 : Blo 2189435 2190915 := bstep (se 1 (by rfl) ⟨1643186, by rfl⟩ : syracuseStep 2190915 = 3286373) B3286373
theorem B4159325 : Blo 2189435 4159325 := bbase (se 3 (by rfl) ⟨779873, by rfl⟩ : syracuseStep 4159325 = 1559747) (by norm_num)
theorem B2772883 : Blo 2189435 2772883 := bstep (se 1 (by rfl) ⟨2079662, by rfl⟩ : syracuseStep 2772883 = 4159325) B4159325
theorem B3697177 : Blo 2189435 3697177 := bstep (se 2 (by rfl) ⟨1386441, by rfl⟩ : syracuseStep 3697177 = 2772883) B2772883
theorem B4929569 : Blo 2189435 4929569 := bstep (se 2 (by rfl) ⟨1848588, by rfl⟩ : syracuseStep 4929569 = 3697177) B3697177
theorem B3286379 : Blo 2189435 3286379 := bstep (se 1 (by rfl) ⟨2464784, by rfl⟩ : syracuseStep 3286379 = 4929569) B4929569
theorem B2190919 : Blo 2189435 2190919 := bstep (se 1 (by rfl) ⟨1643189, by rfl⟩ : syracuseStep 2190919 = 3286379) B3286379
theorem B2464789 : Blo 2189435 2464789 := bbase (se 6 (by rfl) ⟨57768, by rfl⟩ : syracuseStep 2464789 = 115537) (by norm_num)
theorem B3286385 : Blo 2189435 3286385 := bstep (se 2 (by rfl) ⟨1232394, by rfl⟩ : syracuseStep 3286385 = 2464789) B2464789
theorem B2190923 : Blo 2189435 2190923 := bstep (se 1 (by rfl) ⟨1643192, by rfl⟩ : syracuseStep 2190923 = 3286385) B3286385
theorem B2772893 : Blo 2189435 2772893 := bbase (se 3 (by rfl) ⟨519917, by rfl⟩ : syracuseStep 2772893 = 1039835) (by norm_num)
theorem B7394381 : Blo 2189435 7394381 := bstep (se 3 (by rfl) ⟨1386446, by rfl⟩ : syracuseStep 7394381 = 2772893) B2772893
theorem B4929587 : Blo 2189435 4929587 := bstep (se 1 (by rfl) ⟨3697190, by rfl⟩ : syracuseStep 4929587 = 7394381) B7394381
theorem B3286391 : Blo 2189435 3286391 := bstep (se 1 (by rfl) ⟨2464793, by rfl⟩ : syracuseStep 3286391 = 4929587) B4929587
theorem B2190927 : Blo 2189435 2190927 := bstep (se 1 (by rfl) ⟨1643195, by rfl⟩ : syracuseStep 2190927 = 3286391) B3286391
theorem B3286397 : Blo 2189435 3286397 := bbase (se 3 (by rfl) ⟨616199, by rfl⟩ : syracuseStep 3286397 = 1232399) (by norm_num)
theorem B2190931 : Blo 2189435 2190931 := bstep (se 1 (by rfl) ⟨1643198, by rfl⟩ : syracuseStep 2190931 = 3286397) B3286397
theorem B4929605 : Blo 2189435 4929605 := bbase (se 4 (by rfl) ⟨462150, by rfl⟩ : syracuseStep 4929605 = 924301) (by norm_num)
theorem B3286403 : Blo 2189435 3286403 := bstep (se 1 (by rfl) ⟨2464802, by rfl⟩ : syracuseStep 3286403 = 4929605) B4929605
theorem B2190935 : Blo 2189435 2190935 := bstep (se 1 (by rfl) ⟨1643201, by rfl⟩ : syracuseStep 2190935 = 3286403) B3286403
theorem B6239045 : Blo 2189435 6239045 := bbase (se 4 (by rfl) ⟨584910, by rfl⟩ : syracuseStep 6239045 = 1169821) (by norm_num)
theorem B4159363 : Blo 2189435 4159363 := bstep (se 1 (by rfl) ⟨3119522, by rfl⟩ : syracuseStep 4159363 = 6239045) B6239045
theorem B5545817 : Blo 2189435 5545817 := bstep (se 2 (by rfl) ⟨2079681, by rfl⟩ : syracuseStep 5545817 = 4159363) B4159363
theorem B3697211 : Blo 2189435 3697211 := bstep (se 1 (by rfl) ⟨2772908, by rfl⟩ : syracuseStep 3697211 = 5545817) B5545817
theorem B2464807 : Blo 2189435 2464807 := bstep (se 1 (by rfl) ⟨1848605, by rfl⟩ : syracuseStep 2464807 = 3697211) B3697211
theorem B3286409 : Blo 2189435 3286409 := bstep (se 2 (by rfl) ⟨1232403, by rfl⟩ : syracuseStep 3286409 = 2464807) B2464807
theorem B2190939 : Blo 2189435 2190939 := bstep (se 1 (by rfl) ⟨1643204, by rfl⟩ : syracuseStep 2190939 = 3286409) B3286409
theorem B11091653 : Blo 2189435 11091653 := bbase (se 4 (by rfl) ⟨1039842, by rfl⟩ : syracuseStep 11091653 = 2079685) (by norm_num)
theorem B7394435 : Blo 2189435 7394435 := bstep (se 1 (by rfl) ⟨5545826, by rfl⟩ : syracuseStep 7394435 = 11091653) B11091653
theorem B4929623 : Blo 2189435 4929623 := bstep (se 1 (by rfl) ⟨3697217, by rfl⟩ : syracuseStep 4929623 = 7394435) B7394435
theorem B3286415 : Blo 2189435 3286415 := bstep (se 1 (by rfl) ⟨2464811, by rfl⟩ : syracuseStep 3286415 = 4929623) B4929623
theorem B2190943 : Blo 2189435 2190943 := bstep (se 1 (by rfl) ⟨1643207, by rfl⟩ : syracuseStep 2190943 = 3286415) B3286415
theorem B3286421 : Blo 2189435 3286421 := bbase (se 6 (by rfl) ⟨77025, by rfl⟩ : syracuseStep 3286421 = 154051) (by norm_num)
theorem B2190947 : Blo 2189435 2190947 := bstep (se 1 (by rfl) ⟨1643210, by rfl⟩ : syracuseStep 2190947 = 3286421) B3286421
theorem B4679309 : Blo 2189435 4679309 := bbase (se 3 (by rfl) ⟨877370, by rfl⟩ : syracuseStep 4679309 = 1754741) (by norm_num)
theorem B12478157 : Blo 2189435 12478157 := bstep (se 3 (by rfl) ⟨2339654, by rfl⟩ : syracuseStep 12478157 = 4679309) B4679309
theorem B8318771 : Blo 2189435 8318771 := bstep (se 1 (by rfl) ⟨6239078, by rfl⟩ : syracuseStep 8318771 = 12478157) B12478157
theorem B5545847 : Blo 2189435 5545847 := bstep (se 1 (by rfl) ⟨4159385, by rfl⟩ : syracuseStep 5545847 = 8318771) B8318771
theorem B3697231 : Blo 2189435 3697231 := bstep (se 1 (by rfl) ⟨2772923, by rfl⟩ : syracuseStep 3697231 = 5545847) B5545847
theorem B4929641 : Blo 2189435 4929641 := bstep (se 2 (by rfl) ⟨1848615, by rfl⟩ : syracuseStep 4929641 = 3697231) B3697231
theorem B3286427 : Blo 2189435 3286427 := bstep (se 1 (by rfl) ⟨2464820, by rfl⟩ : syracuseStep 3286427 = 4929641) B4929641
theorem B2190951 : Blo 2189435 2190951 := bstep (se 1 (by rfl) ⟨1643213, by rfl⟩ : syracuseStep 2190951 = 3286427) B3286427
theorem B2464825 : Blo 2189435 2464825 := bbase (se 2 (by rfl) ⟨924309, by rfl⟩ : syracuseStep 2464825 = 1848619) (by norm_num)
theorem B3286433 : Blo 2189435 3286433 := bstep (se 2 (by rfl) ⟨1232412, by rfl⟩ : syracuseStep 3286433 = 2464825) B2464825
theorem B2190955 : Blo 2189435 2190955 := bstep (se 1 (by rfl) ⟨1643216, by rfl⟩ : syracuseStep 2190955 = 3286433) B3286433
theorem B2220853 : Blo 2189435 2220853 := bbase (se 5 (by rfl) ⟨104102, by rfl⟩ : syracuseStep 2220853 = 208205) (by norm_num)
theorem B2961137 : Blo 2189435 2961137 := bstep (se 2 (by rfl) ⟨1110426, by rfl⟩ : syracuseStep 2961137 = 2220853) B2220853
theorem B7896365 : Blo 2189435 7896365 := bstep (se 3 (by rfl) ⟨1480568, by rfl⟩ : syracuseStep 7896365 = 2961137) B2961137
theorem B5264243 : Blo 2189435 5264243 := bstep (se 1 (by rfl) ⟨3948182, by rfl⟩ : syracuseStep 5264243 = 7896365) B7896365
theorem B3509495 : Blo 2189435 3509495 := bstep (se 1 (by rfl) ⟨2632121, by rfl⟩ : syracuseStep 3509495 = 5264243) B5264243
theorem B2339663 : Blo 2189435 2339663 := bstep (se 1 (by rfl) ⟨1754747, by rfl⟩ : syracuseStep 2339663 = 3509495) B3509495
theorem B6239101 : Blo 2189435 6239101 := bstep (se 3 (by rfl) ⟨1169831, by rfl⟩ : syracuseStep 6239101 = 2339663) B2339663
theorem B8318801 : Blo 2189435 8318801 := bstep (se 2 (by rfl) ⟨3119550, by rfl⟩ : syracuseStep 8318801 = 6239101) B6239101
theorem B5545867 : Blo 2189435 5545867 := bstep (se 1 (by rfl) ⟨4159400, by rfl⟩ : syracuseStep 5545867 = 8318801) B8318801
theorem B7394489 : Blo 2189435 7394489 := bstep (se 2 (by rfl) ⟨2772933, by rfl⟩ : syracuseStep 7394489 = 5545867) B5545867
theorem B4929659 : Blo 2189435 4929659 := bstep (se 1 (by rfl) ⟨3697244, by rfl⟩ : syracuseStep 4929659 = 7394489) B7394489
theorem B3286439 : Blo 2189435 3286439 := bstep (se 1 (by rfl) ⟨2464829, by rfl⟩ : syracuseStep 3286439 = 4929659) B4929659
theorem B2190959 : Blo 2189435 2190959 := bstep (se 1 (by rfl) ⟨1643219, by rfl⟩ : syracuseStep 2190959 = 3286439) B3286439
theorem B3286445 : Blo 2189435 3286445 := bbase (se 3 (by rfl) ⟨616208, by rfl⟩ : syracuseStep 3286445 = 1232417) (by norm_num)
theorem B2190963 : Blo 2189435 2190963 := bstep (se 1 (by rfl) ⟨1643222, by rfl⟩ : syracuseStep 2190963 = 3286445) B3286445
theorem B4929677 : Blo 2189435 4929677 := bbase (se 3 (by rfl) ⟨924314, by rfl⟩ : syracuseStep 4929677 = 1848629) (by norm_num)
theorem B3286451 : Blo 2189435 3286451 := bstep (se 1 (by rfl) ⟨2464838, by rfl⟩ : syracuseStep 3286451 = 4929677) B4929677
theorem B2190967 : Blo 2189435 2190967 := bstep (se 1 (by rfl) ⟨1643225, by rfl⟩ : syracuseStep 2190967 = 3286451) B3286451
theorem B2772949 : Blo 2189435 2772949 := bbase (se 7 (by rfl) ⟨32495, by rfl⟩ : syracuseStep 2772949 = 64991) (by norm_num)
theorem B3697265 : Blo 2189435 3697265 := bstep (se 2 (by rfl) ⟨1386474, by rfl⟩ : syracuseStep 3697265 = 2772949) B2772949
theorem B2464843 : Blo 2189435 2464843 := bstep (se 1 (by rfl) ⟨1848632, by rfl⟩ : syracuseStep 2464843 = 3697265) B3697265
theorem B3286457 : Blo 2189435 3286457 := bstep (se 2 (by rfl) ⟨1232421, by rfl⟩ : syracuseStep 3286457 = 2464843) B2464843
theorem B2190971 : Blo 2189435 2190971 := bstep (se 1 (by rfl) ⟨1643228, by rfl⟩ : syracuseStep 2190971 = 3286457) B3286457
theorem B3705005 : Blo 2189435 3705005 := bbase (se 3 (by rfl) ⟨694688, by rfl⟩ : syracuseStep 3705005 = 1389377) (by norm_num)
theorem B2470003 : Blo 2189435 2470003 := bstep (se 1 (by rfl) ⟨1852502, by rfl⟩ : syracuseStep 2470003 = 3705005) B3705005
theorem B13173349 : Blo 2189435 13173349 := bstep (se 4 (by rfl) ⟨1235001, by rfl⟩ : syracuseStep 13173349 = 2470003) B2470003
theorem B17564465 : Blo 2189435 17564465 := bstep (se 2 (by rfl) ⟨6586674, by rfl⟩ : syracuseStep 17564465 = 13173349) B13173349
theorem B11709643 : Blo 2189435 11709643 := bstep (se 1 (by rfl) ⟨8782232, by rfl⟩ : syracuseStep 11709643 = 17564465) B17564465
theorem B15612857 : Blo 2189435 15612857 := bstep (se 2 (by rfl) ⟨5854821, by rfl⟩ : syracuseStep 15612857 = 11709643) B11709643
theorem B10408571 : Blo 2189435 10408571 := bstep (se 1 (by rfl) ⟨7806428, by rfl⟩ : syracuseStep 10408571 = 15612857) B15612857
theorem B6939047 : Blo 2189435 6939047 := bstep (se 1 (by rfl) ⟨5204285, by rfl⟩ : syracuseStep 6939047 = 10408571) B10408571
theorem B18504125 : Blo 2189435 18504125 := bstep (se 3 (by rfl) ⟨3469523, by rfl⟩ : syracuseStep 18504125 = 6939047) B6939047
theorem B12336083 : Blo 2189435 12336083 := bstep (se 1 (by rfl) ⟨9252062, by rfl⟩ : syracuseStep 12336083 = 18504125) B18504125
theorem B8224055 : Blo 2189435 8224055 := bstep (se 1 (by rfl) ⟨6168041, by rfl⟩ : syracuseStep 8224055 = 12336083) B12336083
theorem B5482703 : Blo 2189435 5482703 := bstep (se 1 (by rfl) ⟨4112027, by rfl⟩ : syracuseStep 5482703 = 8224055) B8224055
theorem B3655135 : Blo 2189435 3655135 := bstep (se 1 (by rfl) ⟨2741351, by rfl⟩ : syracuseStep 3655135 = 5482703) B5482703
theorem B19494053 : Blo 2189435 19494053 := bstep (se 4 (by rfl) ⟨1827567, by rfl⟩ : syracuseStep 19494053 = 3655135) B3655135
theorem B12996035 : Blo 2189435 12996035 := bstep (se 1 (by rfl) ⟨9747026, by rfl⟩ : syracuseStep 12996035 = 19494053) B19494053
theorem B8664023 : Blo 2189435 8664023 := bstep (se 1 (by rfl) ⟨6498017, by rfl⟩ : syracuseStep 8664023 = 12996035) B12996035
theorem B23104061 : Blo 2189435 23104061 := bstep (se 3 (by rfl) ⟨4332011, by rfl⟩ : syracuseStep 23104061 = 8664023) B8664023
theorem B15402707 : Blo 2189435 15402707 := bstep (se 1 (by rfl) ⟨11552030, by rfl⟩ : syracuseStep 15402707 = 23104061) B23104061
theorem B10268471 : Blo 2189435 10268471 := bstep (se 1 (by rfl) ⟨7701353, by rfl⟩ : syracuseStep 10268471 = 15402707) B15402707
theorem B6845647 : Blo 2189435 6845647 := bstep (se 1 (by rfl) ⟨5134235, by rfl⟩ : syracuseStep 6845647 = 10268471) B10268471
theorem B9127529 : Blo 2189435 9127529 := bstep (se 2 (by rfl) ⟨3422823, by rfl⟩ : syracuseStep 9127529 = 6845647) B6845647
theorem B6085019 : Blo 2189435 6085019 := bstep (se 1 (by rfl) ⟨4563764, by rfl⟩ : syracuseStep 6085019 = 9127529) B9127529
theorem B4056679 : Blo 2189435 4056679 := bstep (se 1 (by rfl) ⟨3042509, by rfl⟩ : syracuseStep 4056679 = 6085019) B6085019
theorem B5408905 : Blo 2189435 5408905 := bstep (se 2 (by rfl) ⟨2028339, by rfl⟩ : syracuseStep 5408905 = 4056679) B4056679
theorem B7211873 : Blo 2189435 7211873 := bstep (se 2 (by rfl) ⟨2704452, by rfl⟩ : syracuseStep 7211873 = 5408905) B5408905
theorem B19231661 : Blo 2189435 19231661 := bstep (se 3 (by rfl) ⟨3605936, by rfl⟩ : syracuseStep 19231661 = 7211873) B7211873
theorem B12821107 : Blo 2189435 12821107 := bstep (se 1 (by rfl) ⟨9615830, by rfl⟩ : syracuseStep 12821107 = 19231661) B19231661
theorem B17094809 : Blo 2189435 17094809 := bstep (se 2 (by rfl) ⟨6410553, by rfl⟩ : syracuseStep 17094809 = 12821107) B12821107
theorem B11396539 : Blo 2189435 11396539 := bstep (se 1 (by rfl) ⟨8547404, by rfl⟩ : syracuseStep 11396539 = 17094809) B17094809
theorem B15195385 : Blo 2189435 15195385 := bstep (se 2 (by rfl) ⟨5698269, by rfl⟩ : syracuseStep 15195385 = 11396539) B11396539
theorem B20260513 : Blo 2189435 20260513 := bstep (se 2 (by rfl) ⟨7597692, by rfl⟩ : syracuseStep 20260513 = 15195385) B15195385
theorem B27014017 : Blo 2189435 27014017 := bstep (se 2 (by rfl) ⟨10130256, by rfl⟩ : syracuseStep 27014017 = 20260513) B20260513
theorem B36018689 : Blo 2189435 36018689 := bstep (se 2 (by rfl) ⟨13507008, by rfl⟩ : syracuseStep 36018689 = 27014017) B27014017
theorem B96049837 : Blo 2189435 96049837 := bstep (se 3 (by rfl) ⟨18009344, by rfl⟩ : syracuseStep 96049837 = 36018689) B36018689
theorem B128066449 : Blo 2189435 128066449 := bstep (se 2 (by rfl) ⟨48024918, by rfl⟩ : syracuseStep 128066449 = 96049837) B96049837
theorem B170755265 : Blo 2189435 170755265 := bstep (se 2 (by rfl) ⟨64033224, by rfl⟩ : syracuseStep 170755265 = 128066449) B128066449
theorem B113836843 : Blo 2189435 113836843 := bstep (se 1 (by rfl) ⟨85377632, by rfl⟩ : syracuseStep 113836843 = 170755265) B170755265
theorem B151782457 : Blo 2189435 151782457 := bstep (se 2 (by rfl) ⟨56918421, by rfl⟩ : syracuseStep 151782457 = 113836843) B113836843
theorem B202376609 : Blo 2189435 202376609 := bstep (se 2 (by rfl) ⟨75891228, by rfl⟩ : syracuseStep 202376609 = 151782457) B151782457
theorem B134917739 : Blo 2189435 134917739 := bstep (se 1 (by rfl) ⟨101188304, by rfl⟩ : syracuseStep 134917739 = 202376609) B202376609
theorem B89945159 : Blo 2189435 89945159 := bstep (se 1 (by rfl) ⟨67458869, by rfl⟩ : syracuseStep 89945159 = 134917739) B134917739
theorem B239853757 : Blo 2189435 239853757 := bstep (se 3 (by rfl) ⟨44972579, by rfl⟩ : syracuseStep 239853757 = 89945159) B89945159
theorem B319805009 : Blo 2189435 319805009 := bstep (se 2 (by rfl) ⟨119926878, by rfl⟩ : syracuseStep 319805009 = 239853757) B239853757
theorem B213203339 : Blo 2189435 213203339 := bstep (se 1 (by rfl) ⟨159902504, by rfl⟩ : syracuseStep 213203339 = 319805009) B319805009
theorem B142135559 : Blo 2189435 142135559 := bstep (se 1 (by rfl) ⟨106601669, by rfl⟩ : syracuseStep 142135559 = 213203339) B213203339
theorem B94757039 : Blo 2189435 94757039 := bstep (se 1 (by rfl) ⟨71067779, by rfl⟩ : syracuseStep 94757039 = 142135559) B142135559
theorem B63171359 : Blo 2189435 63171359 := bstep (se 1 (by rfl) ⟨47378519, by rfl⟩ : syracuseStep 63171359 = 94757039) B94757039
theorem B42114239 : Blo 2189435 42114239 := bstep (se 1 (by rfl) ⟨31585679, by rfl⟩ : syracuseStep 42114239 = 63171359) B63171359
theorem B28076159 : Blo 2189435 28076159 := bstep (se 1 (by rfl) ⟨21057119, by rfl⟩ : syracuseStep 28076159 = 42114239) B42114239
theorem B18717439 : Blo 2189435 18717439 := bstep (se 1 (by rfl) ⟨14038079, by rfl⟩ : syracuseStep 18717439 = 28076159) B28076159
theorem B24956585 : Blo 2189435 24956585 := bstep (se 2 (by rfl) ⟨9358719, by rfl⟩ : syracuseStep 24956585 = 18717439) B18717439
theorem B16637723 : Blo 2189435 16637723 := bstep (se 1 (by rfl) ⟨12478292, by rfl⟩ : syracuseStep 16637723 = 24956585) B24956585
theorem B11091815 : Blo 2189435 11091815 := bstep (se 1 (by rfl) ⟨8318861, by rfl⟩ : syracuseStep 11091815 = 16637723) B16637723
theorem B7394543 : Blo 2189435 7394543 := bstep (se 1 (by rfl) ⟨5545907, by rfl⟩ : syracuseStep 7394543 = 11091815) B11091815
theorem B4929695 : Blo 2189435 4929695 := bstep (se 1 (by rfl) ⟨3697271, by rfl⟩ : syracuseStep 4929695 = 7394543) B7394543
theorem B3286463 : Blo 2189435 3286463 := bstep (se 1 (by rfl) ⟨2464847, by rfl⟩ : syracuseStep 3286463 = 4929695) B4929695
theorem B2190975 : Blo 2189435 2190975 := bstep (se 1 (by rfl) ⟨1643231, by rfl⟩ : syracuseStep 2190975 = 3286463) B3286463
theorem B3286469 : Blo 2189435 3286469 := bbase (se 4 (by rfl) ⟨308106, by rfl⟩ : syracuseStep 3286469 = 616213) (by norm_num)
theorem B2190979 : Blo 2189435 2190979 := bstep (se 1 (by rfl) ⟨1643234, by rfl⟩ : syracuseStep 2190979 = 3286469) B3286469
theorem B3697285 : Blo 2189435 3697285 := bbase (se 4 (by rfl) ⟨346620, by rfl⟩ : syracuseStep 3697285 = 693241) (by norm_num)
theorem B4929713 : Blo 2189435 4929713 := bstep (se 2 (by rfl) ⟨1848642, by rfl⟩ : syracuseStep 4929713 = 3697285) B3697285
theorem B3286475 : Blo 2189435 3286475 := bstep (se 1 (by rfl) ⟨2464856, by rfl⟩ : syracuseStep 3286475 = 4929713) B4929713
theorem B2190983 : Blo 2189435 2190983 := bstep (se 1 (by rfl) ⟨1643237, by rfl⟩ : syracuseStep 2190983 = 3286475) B3286475
theorem B2464861 : Blo 2189435 2464861 := bbase (se 3 (by rfl) ⟨462161, by rfl⟩ : syracuseStep 2464861 = 924323) (by norm_num)
theorem B3286481 : Blo 2189435 3286481 := bstep (se 2 (by rfl) ⟨1232430, by rfl⟩ : syracuseStep 3286481 = 2464861) B2464861
theorem B2190987 : Blo 2189435 2190987 := bstep (se 1 (by rfl) ⟨1643240, by rfl⟩ : syracuseStep 2190987 = 3286481) B3286481
theorem B7394597 : Blo 2189435 7394597 := bbase (se 4 (by rfl) ⟨693243, by rfl⟩ : syracuseStep 7394597 = 1386487) (by norm_num)
theorem B4929731 : Blo 2189435 4929731 := bstep (se 1 (by rfl) ⟨3697298, by rfl⟩ : syracuseStep 4929731 = 7394597) B7394597
theorem B3286487 : Blo 2189435 3286487 := bstep (se 1 (by rfl) ⟨2464865, by rfl⟩ : syracuseStep 3286487 = 4929731) B4929731
theorem B2190991 : Blo 2189435 2190991 := bstep (se 1 (by rfl) ⟨1643243, by rfl⟩ : syracuseStep 2190991 = 3286487) B3286487
theorem B3286493 : Blo 2189435 3286493 := bbase (se 3 (by rfl) ⟨616217, by rfl⟩ : syracuseStep 3286493 = 1232435) (by norm_num)
theorem B2190995 : Blo 2189435 2190995 := bstep (se 1 (by rfl) ⟨1643246, by rfl⟩ : syracuseStep 2190995 = 3286493) B3286493
theorem B4929749 : Blo 2189435 4929749 := bbase (se 7 (by rfl) ⟨57770, by rfl⟩ : syracuseStep 4929749 = 115541) (by norm_num)
theorem B3286499 : Blo 2189435 3286499 := bstep (se 1 (by rfl) ⟨2464874, by rfl⟩ : syracuseStep 3286499 = 4929749) B4929749
theorem B2190999 : Blo 2189435 2190999 := bstep (se 1 (by rfl) ⟨1643249, by rfl⟩ : syracuseStep 2190999 = 3286499) B3286499
theorem B8883589 : Blo 2189435 8883589 := bbase (se 4 (by rfl) ⟨832836, by rfl⟩ : syracuseStep 8883589 = 1665673) (by norm_num)
theorem B11844785 : Blo 2189435 11844785 := bstep (se 2 (by rfl) ⟨4441794, by rfl⟩ : syracuseStep 11844785 = 8883589) B8883589
theorem B7896523 : Blo 2189435 7896523 := bstep (se 1 (by rfl) ⟨5922392, by rfl⟩ : syracuseStep 7896523 = 11844785) B11844785
theorem B10528697 : Blo 2189435 10528697 := bstep (se 2 (by rfl) ⟨3948261, by rfl⟩ : syracuseStep 10528697 = 7896523) B7896523
theorem B7019131 : Blo 2189435 7019131 := bstep (se 1 (by rfl) ⟨5264348, by rfl⟩ : syracuseStep 7019131 = 10528697) B10528697
theorem B9358841 : Blo 2189435 9358841 := bstep (se 2 (by rfl) ⟨3509565, by rfl⟩ : syracuseStep 9358841 = 7019131) B7019131
theorem B6239227 : Blo 2189435 6239227 := bstep (se 1 (by rfl) ⟨4679420, by rfl⟩ : syracuseStep 6239227 = 9358841) B9358841
theorem B8318969 : Blo 2189435 8318969 := bstep (se 2 (by rfl) ⟨3119613, by rfl⟩ : syracuseStep 8318969 = 6239227) B6239227
theorem B5545979 : Blo 2189435 5545979 := bstep (se 1 (by rfl) ⟨4159484, by rfl⟩ : syracuseStep 5545979 = 8318969) B8318969
theorem B3697319 : Blo 2189435 3697319 := bstep (se 1 (by rfl) ⟨2772989, by rfl⟩ : syracuseStep 3697319 = 5545979) B5545979
theorem B2464879 : Blo 2189435 2464879 := bstep (se 1 (by rfl) ⟨1848659, by rfl⟩ : syracuseStep 2464879 = 3697319) B3697319
theorem B3286505 : Blo 2189435 3286505 := bstep (se 2 (by rfl) ⟨1232439, by rfl⟩ : syracuseStep 3286505 = 2464879) B2464879
theorem B2191003 : Blo 2189435 2191003 := bstep (se 1 (by rfl) ⟨1643252, by rfl⟩ : syracuseStep 2191003 = 3286505) B3286505
theorem B5264357 : Blo 2189435 5264357 := bbase (se 4 (by rfl) ⟨493533, by rfl⟩ : syracuseStep 5264357 = 987067) (by norm_num)
theorem B14038285 : Blo 2189435 14038285 := bstep (se 3 (by rfl) ⟨2632178, by rfl⟩ : syracuseStep 14038285 = 5264357) B5264357
theorem B18717713 : Blo 2189435 18717713 := bstep (se 2 (by rfl) ⟨7019142, by rfl⟩ : syracuseStep 18717713 = 14038285) B14038285
theorem B12478475 : Blo 2189435 12478475 := bstep (se 1 (by rfl) ⟨9358856, by rfl⟩ : syracuseStep 12478475 = 18717713) B18717713
theorem B8318983 : Blo 2189435 8318983 := bstep (se 1 (by rfl) ⟨6239237, by rfl⟩ : syracuseStep 8318983 = 12478475) B12478475
theorem B11091977 : Blo 2189435 11091977 := bstep (se 2 (by rfl) ⟨4159491, by rfl⟩ : syracuseStep 11091977 = 8318983) B8318983
theorem B7394651 : Blo 2189435 7394651 := bstep (se 1 (by rfl) ⟨5545988, by rfl⟩ : syracuseStep 7394651 = 11091977) B11091977
theorem B4929767 : Blo 2189435 4929767 := bstep (se 1 (by rfl) ⟨3697325, by rfl⟩ : syracuseStep 4929767 = 7394651) B7394651
theorem B3286511 : Blo 2189435 3286511 := bstep (se 1 (by rfl) ⟨2464883, by rfl⟩ : syracuseStep 3286511 = 4929767) B4929767
theorem B2191007 : Blo 2189435 2191007 := bstep (se 1 (by rfl) ⟨1643255, by rfl⟩ : syracuseStep 2191007 = 3286511) B3286511
theorem B3286517 : Blo 2189435 3286517 := bbase (se 5 (by rfl) ⟨154055, by rfl⟩ : syracuseStep 3286517 = 308111) (by norm_num)
theorem B2191011 : Blo 2189435 2191011 := bstep (se 1 (by rfl) ⟨1643258, by rfl⟩ : syracuseStep 2191011 = 3286517) B3286517
theorem B2632189 : Blo 2189435 2632189 := bbase (se 3 (by rfl) ⟨493535, by rfl⟩ : syracuseStep 2632189 = 987071) (by norm_num)
theorem B3509585 : Blo 2189435 3509585 := bstep (se 2 (by rfl) ⟨1316094, by rfl⟩ : syracuseStep 3509585 = 2632189) B2632189
theorem B2339723 : Blo 2189435 2339723 := bstep (se 1 (by rfl) ⟨1754792, by rfl⟩ : syracuseStep 2339723 = 3509585) B3509585
theorem B6239261 : Blo 2189435 6239261 := bstep (se 3 (by rfl) ⟨1169861, by rfl⟩ : syracuseStep 6239261 = 2339723) B2339723
theorem B4159507 : Blo 2189435 4159507 := bstep (se 1 (by rfl) ⟨3119630, by rfl⟩ : syracuseStep 4159507 = 6239261) B6239261
theorem B5546009 : Blo 2189435 5546009 := bstep (se 2 (by rfl) ⟨2079753, by rfl⟩ : syracuseStep 5546009 = 4159507) B4159507
theorem B3697339 : Blo 2189435 3697339 := bstep (se 1 (by rfl) ⟨2773004, by rfl⟩ : syracuseStep 3697339 = 5546009) B5546009
theorem B4929785 : Blo 2189435 4929785 := bstep (se 2 (by rfl) ⟨1848669, by rfl⟩ : syracuseStep 4929785 = 3697339) B3697339
theorem B3286523 : Blo 2189435 3286523 := bstep (se 1 (by rfl) ⟨2464892, by rfl⟩ : syracuseStep 3286523 = 4929785) B4929785
theorem B2191015 : Blo 2189435 2191015 := bstep (se 1 (by rfl) ⟨1643261, by rfl⟩ : syracuseStep 2191015 = 3286523) B3286523
theorem B2464897 : Blo 2189435 2464897 := bbase (se 2 (by rfl) ⟨924336, by rfl⟩ : syracuseStep 2464897 = 1848673) (by norm_num)
theorem B3286529 : Blo 2189435 3286529 := bstep (se 2 (by rfl) ⟨1232448, by rfl⟩ : syracuseStep 3286529 = 2464897) B2464897
theorem B2191019 : Blo 2189435 2191019 := bstep (se 1 (by rfl) ⟨1643264, by rfl⟩ : syracuseStep 2191019 = 3286529) B3286529
theorem B5546029 : Blo 2189435 5546029 := bbase (se 3 (by rfl) ⟨1039880, by rfl⟩ : syracuseStep 5546029 = 2079761) (by norm_num)
theorem B7394705 : Blo 2189435 7394705 := bstep (se 2 (by rfl) ⟨2773014, by rfl⟩ : syracuseStep 7394705 = 5546029) B5546029
theorem B4929803 : Blo 2189435 4929803 := bstep (se 1 (by rfl) ⟨3697352, by rfl⟩ : syracuseStep 4929803 = 7394705) B7394705
theorem B3286535 : Blo 2189435 3286535 := bstep (se 1 (by rfl) ⟨2464901, by rfl⟩ : syracuseStep 3286535 = 4929803) B4929803
theorem B2191023 : Blo 2189435 2191023 := bstep (se 1 (by rfl) ⟨1643267, by rfl⟩ : syracuseStep 2191023 = 3286535) B3286535
theorem B3286541 : Blo 2189435 3286541 := bbase (se 3 (by rfl) ⟨616226, by rfl⟩ : syracuseStep 3286541 = 1232453) (by norm_num)
theorem B2191027 : Blo 2189435 2191027 := bstep (se 1 (by rfl) ⟨1643270, by rfl⟩ : syracuseStep 2191027 = 3286541) B3286541
theorem B4929821 : Blo 2189435 4929821 := bbase (se 3 (by rfl) ⟨924341, by rfl⟩ : syracuseStep 4929821 = 1848683) (by norm_num)
theorem B3286547 : Blo 2189435 3286547 := bstep (se 1 (by rfl) ⟨2464910, by rfl⟩ : syracuseStep 3286547 = 4929821) B4929821
theorem B2191031 : Blo 2189435 2191031 := bstep (se 1 (by rfl) ⟨1643273, by rfl⟩ : syracuseStep 2191031 = 3286547) B3286547
theorem B3697373 : Blo 2189435 3697373 := bbase (se 3 (by rfl) ⟨693257, by rfl⟩ : syracuseStep 3697373 = 1386515) (by norm_num)
theorem B2464915 : Blo 2189435 2464915 := bstep (se 1 (by rfl) ⟨1848686, by rfl⟩ : syracuseStep 2464915 = 3697373) B3697373
theorem B3286553 : Blo 2189435 3286553 := bstep (se 2 (by rfl) ⟨1232457, by rfl⟩ : syracuseStep 3286553 = 2464915) B2464915
theorem B2191035 : Blo 2189435 2191035 := bstep (se 1 (by rfl) ⟨1643276, by rfl⟩ : syracuseStep 2191035 = 3286553) B3286553
theorem B2632217 : Blo 2189435 2632217 := bbase (se 2 (by rfl) ⟨987081, by rfl⟩ : syracuseStep 2632217 = 1974163) (by norm_num)
theorem B7019245 : Blo 2189435 7019245 := bstep (se 3 (by rfl) ⟨1316108, by rfl⟩ : syracuseStep 7019245 = 2632217) B2632217
theorem B9358993 : Blo 2189435 9358993 := bstep (se 2 (by rfl) ⟨3509622, by rfl⟩ : syracuseStep 9358993 = 7019245) B7019245
theorem B12478657 : Blo 2189435 12478657 := bstep (se 2 (by rfl) ⟨4679496, by rfl⟩ : syracuseStep 12478657 = 9358993) B9358993
theorem B16638209 : Blo 2189435 16638209 := bstep (se 2 (by rfl) ⟨6239328, by rfl⟩ : syracuseStep 16638209 = 12478657) B12478657
theorem B11092139 : Blo 2189435 11092139 := bstep (se 1 (by rfl) ⟨8319104, by rfl⟩ : syracuseStep 11092139 = 16638209) B16638209
theorem B7394759 : Blo 2189435 7394759 := bstep (se 1 (by rfl) ⟨5546069, by rfl⟩ : syracuseStep 7394759 = 11092139) B11092139
theorem B4929839 : Blo 2189435 4929839 := bstep (se 1 (by rfl) ⟨3697379, by rfl⟩ : syracuseStep 4929839 = 7394759) B7394759
theorem B3286559 : Blo 2189435 3286559 := bstep (se 1 (by rfl) ⟨2464919, by rfl⟩ : syracuseStep 3286559 = 4929839) B4929839
theorem B2191039 : Blo 2189435 2191039 := bstep (se 1 (by rfl) ⟨1643279, by rfl⟩ : syracuseStep 2191039 = 3286559) B3286559
theorem B3286565 : Blo 2189435 3286565 := bbase (se 4 (by rfl) ⟨308115, by rfl⟩ : syracuseStep 3286565 = 616231) (by norm_num)
theorem B2191043 : Blo 2189435 2191043 := bstep (se 1 (by rfl) ⟨1643282, by rfl⟩ : syracuseStep 2191043 = 3286565) B3286565
theorem B2773045 : Blo 2189435 2773045 := bbase (se 5 (by rfl) ⟨129986, by rfl⟩ : syracuseStep 2773045 = 259973) (by norm_num)
theorem B3697393 : Blo 2189435 3697393 := bstep (se 2 (by rfl) ⟨1386522, by rfl⟩ : syracuseStep 3697393 = 2773045) B2773045
theorem B4929857 : Blo 2189435 4929857 := bstep (se 2 (by rfl) ⟨1848696, by rfl⟩ : syracuseStep 4929857 = 3697393) B3697393
theorem B3286571 : Blo 2189435 3286571 := bstep (se 1 (by rfl) ⟨2464928, by rfl⟩ : syracuseStep 3286571 = 4929857) B4929857
theorem B2191047 : Blo 2189435 2191047 := bstep (se 1 (by rfl) ⟨1643285, by rfl⟩ : syracuseStep 2191047 = 3286571) B3286571
theorem B2464933 : Blo 2189435 2464933 := bbase (se 4 (by rfl) ⟨231087, by rfl⟩ : syracuseStep 2464933 = 462175) (by norm_num)
theorem B3286577 : Blo 2189435 3286577 := bstep (se 2 (by rfl) ⟨1232466, by rfl⟩ : syracuseStep 3286577 = 2464933) B2464933
theorem B2191051 : Blo 2189435 2191051 := bstep (se 1 (by rfl) ⟨1643288, by rfl⟩ : syracuseStep 2191051 = 3286577) B3286577
theorem B5922533 : Blo 2189435 5922533 := bbase (se 4 (by rfl) ⟨555237, by rfl⟩ : syracuseStep 5922533 = 1110475) (by norm_num)
theorem B3948355 : Blo 2189435 3948355 := bstep (se 1 (by rfl) ⟨2961266, by rfl⟩ : syracuseStep 3948355 = 5922533) B5922533
theorem B21057893 : Blo 2189435 21057893 := bstep (se 4 (by rfl) ⟨1974177, by rfl⟩ : syracuseStep 21057893 = 3948355) B3948355
theorem B14038595 : Blo 2189435 14038595 := bstep (se 1 (by rfl) ⟨10528946, by rfl⟩ : syracuseStep 14038595 = 21057893) B21057893
theorem B9359063 : Blo 2189435 9359063 := bstep (se 1 (by rfl) ⟨7019297, by rfl⟩ : syracuseStep 9359063 = 14038595) B14038595
theorem B6239375 : Blo 2189435 6239375 := bstep (se 1 (by rfl) ⟨4679531, by rfl⟩ : syracuseStep 6239375 = 9359063) B9359063
theorem B4159583 : Blo 2189435 4159583 := bstep (se 1 (by rfl) ⟨3119687, by rfl⟩ : syracuseStep 4159583 = 6239375) B6239375
theorem B2773055 : Blo 2189435 2773055 := bstep (se 1 (by rfl) ⟨2079791, by rfl⟩ : syracuseStep 2773055 = 4159583) B4159583
theorem B7394813 : Blo 2189435 7394813 := bstep (se 3 (by rfl) ⟨1386527, by rfl⟩ : syracuseStep 7394813 = 2773055) B2773055
theorem B4929875 : Blo 2189435 4929875 := bstep (se 1 (by rfl) ⟨3697406, by rfl⟩ : syracuseStep 4929875 = 7394813) B7394813
theorem B3286583 : Blo 2189435 3286583 := bstep (se 1 (by rfl) ⟨2464937, by rfl⟩ : syracuseStep 3286583 = 4929875) B4929875
theorem B2191055 : Blo 2189435 2191055 := bstep (se 1 (by rfl) ⟨1643291, by rfl⟩ : syracuseStep 2191055 = 3286583) B3286583
theorem B3286589 : Blo 2189435 3286589 := bbase (se 3 (by rfl) ⟨616235, by rfl⟩ : syracuseStep 3286589 = 1232471) (by norm_num)
theorem B2191059 : Blo 2189435 2191059 := bstep (se 1 (by rfl) ⟨1643294, by rfl⟩ : syracuseStep 2191059 = 3286589) B3286589
theorem B4929893 : Blo 2189435 4929893 := bbase (se 4 (by rfl) ⟨462177, by rfl⟩ : syracuseStep 4929893 = 924355) (by norm_num)
theorem B3286595 : Blo 2189435 3286595 := bstep (se 1 (by rfl) ⟨2464946, by rfl⟩ : syracuseStep 3286595 = 4929893) B4929893
theorem B2191063 : Blo 2189435 2191063 := bstep (se 1 (by rfl) ⟨1643297, by rfl⟩ : syracuseStep 2191063 = 3286595) B3286595
theorem B5546141 : Blo 2189435 5546141 := bbase (se 3 (by rfl) ⟨1039901, by rfl⟩ : syracuseStep 5546141 = 2079803) (by norm_num)
theorem B3697427 : Blo 2189435 3697427 := bstep (se 1 (by rfl) ⟨2773070, by rfl⟩ : syracuseStep 3697427 = 5546141) B5546141
theorem B2464951 : Blo 2189435 2464951 := bstep (se 1 (by rfl) ⟨1848713, by rfl⟩ : syracuseStep 2464951 = 3697427) B3697427
theorem B3286601 : Blo 2189435 3286601 := bstep (se 2 (by rfl) ⟨1232475, by rfl⟩ : syracuseStep 3286601 = 2464951) B2464951
theorem B2191067 : Blo 2189435 2191067 := bstep (se 1 (by rfl) ⟨1643300, by rfl⟩ : syracuseStep 2191067 = 3286601) B3286601
theorem B4159613 : Blo 2189435 4159613 := bbase (se 3 (by rfl) ⟨779927, by rfl⟩ : syracuseStep 4159613 = 1559855) (by norm_num)
theorem B11092301 : Blo 2189435 11092301 := bstep (se 3 (by rfl) ⟨2079806, by rfl⟩ : syracuseStep 11092301 = 4159613) B4159613
theorem B7394867 : Blo 2189435 7394867 := bstep (se 1 (by rfl) ⟨5546150, by rfl⟩ : syracuseStep 7394867 = 11092301) B11092301
theorem B4929911 : Blo 2189435 4929911 := bstep (se 1 (by rfl) ⟨3697433, by rfl⟩ : syracuseStep 4929911 = 7394867) B7394867
theorem B3286607 : Blo 2189435 3286607 := bstep (se 1 (by rfl) ⟨2464955, by rfl⟩ : syracuseStep 3286607 = 4929911) B4929911
theorem B2191071 : Blo 2189435 2191071 := bstep (se 1 (by rfl) ⟨1643303, by rfl⟩ : syracuseStep 2191071 = 3286607) B3286607
theorem B3286613 : Blo 2189435 3286613 := bbase (se 8 (by rfl) ⟨19257, by rfl⟩ : syracuseStep 3286613 = 38515) (by norm_num)
theorem B2191075 : Blo 2189435 2191075 := bstep (se 1 (by rfl) ⟨1643306, by rfl⟩ : syracuseStep 2191075 = 3286613) B3286613
theorem B4441949 : Blo 2189435 4441949 := bbase (se 3 (by rfl) ⟨832865, by rfl⟩ : syracuseStep 4441949 = 1665731) (by norm_num)
theorem B2961299 : Blo 2189435 2961299 := bstep (se 1 (by rfl) ⟨2220974, by rfl⟩ : syracuseStep 2961299 = 4441949) B4441949
theorem B7896797 : Blo 2189435 7896797 := bstep (se 3 (by rfl) ⟨1480649, by rfl⟩ : syracuseStep 7896797 = 2961299) B2961299
theorem B5264531 : Blo 2189435 5264531 := bstep (se 1 (by rfl) ⟨3948398, by rfl⟩ : syracuseStep 5264531 = 7896797) B7896797
theorem B3509687 : Blo 2189435 3509687 := bstep (se 1 (by rfl) ⟨2632265, by rfl⟩ : syracuseStep 3509687 = 5264531) B5264531
theorem B9359165 : Blo 2189435 9359165 := bstep (se 3 (by rfl) ⟨1754843, by rfl⟩ : syracuseStep 9359165 = 3509687) B3509687
theorem B6239443 : Blo 2189435 6239443 := bstep (se 1 (by rfl) ⟨4679582, by rfl⟩ : syracuseStep 6239443 = 9359165) B9359165
theorem B8319257 : Blo 2189435 8319257 := bstep (se 2 (by rfl) ⟨3119721, by rfl⟩ : syracuseStep 8319257 = 6239443) B6239443
theorem B5546171 : Blo 2189435 5546171 := bstep (se 1 (by rfl) ⟨4159628, by rfl⟩ : syracuseStep 5546171 = 8319257) B8319257
theorem B3697447 : Blo 2189435 3697447 := bstep (se 1 (by rfl) ⟨2773085, by rfl⟩ : syracuseStep 3697447 = 5546171) B5546171
theorem B4929929 : Blo 2189435 4929929 := bstep (se 2 (by rfl) ⟨1848723, by rfl⟩ : syracuseStep 4929929 = 3697447) B3697447
theorem B3286619 : Blo 2189435 3286619 := bstep (se 1 (by rfl) ⟨2464964, by rfl⟩ : syracuseStep 3286619 = 4929929) B4929929
theorem B2191079 : Blo 2189435 2191079 := bstep (se 1 (by rfl) ⟨1643309, by rfl⟩ : syracuseStep 2191079 = 3286619) B3286619
theorem B2464969 : Blo 2189435 2464969 := bbase (se 2 (by rfl) ⟨924363, by rfl⟩ : syracuseStep 2464969 = 1848727) (by norm_num)
theorem B3286625 : Blo 2189435 3286625 := bstep (se 2 (by rfl) ⟨1232484, by rfl⟩ : syracuseStep 3286625 = 2464969) B2464969
theorem B2191083 : Blo 2189435 2191083 := bstep (se 1 (by rfl) ⟨1643312, by rfl⟩ : syracuseStep 2191083 = 3286625) B3286625
theorem B11845237 : Blo 2189435 11845237 := bbase (se 5 (by rfl) ⟨555245, by rfl⟩ : syracuseStep 11845237 = 1110491) (by norm_num)
theorem B15793649 : Blo 2189435 15793649 := bstep (se 2 (by rfl) ⟨5922618, by rfl⟩ : syracuseStep 15793649 = 11845237) B11845237
theorem B10529099 : Blo 2189435 10529099 := bstep (se 1 (by rfl) ⟨7896824, by rfl⟩ : syracuseStep 10529099 = 15793649) B15793649
theorem B7019399 : Blo 2189435 7019399 := bstep (se 1 (by rfl) ⟨5264549, by rfl⟩ : syracuseStep 7019399 = 10529099) B10529099
theorem B18718397 : Blo 2189435 18718397 := bstep (se 3 (by rfl) ⟨3509699, by rfl⟩ : syracuseStep 18718397 = 7019399) B7019399
theorem B12478931 : Blo 2189435 12478931 := bstep (se 1 (by rfl) ⟨9359198, by rfl⟩ : syracuseStep 12478931 = 18718397) B18718397
theorem B8319287 : Blo 2189435 8319287 := bstep (se 1 (by rfl) ⟨6239465, by rfl⟩ : syracuseStep 8319287 = 12478931) B12478931
theorem B5546191 : Blo 2189435 5546191 := bstep (se 1 (by rfl) ⟨4159643, by rfl⟩ : syracuseStep 5546191 = 8319287) B8319287
theorem B7394921 : Blo 2189435 7394921 := bstep (se 2 (by rfl) ⟨2773095, by rfl⟩ : syracuseStep 7394921 = 5546191) B5546191
theorem B4929947 : Blo 2189435 4929947 := bstep (se 1 (by rfl) ⟨3697460, by rfl⟩ : syracuseStep 4929947 = 7394921) B7394921
theorem B3286631 : Blo 2189435 3286631 := bstep (se 1 (by rfl) ⟨2464973, by rfl⟩ : syracuseStep 3286631 = 4929947) B4929947
theorem B2191087 : Blo 2189435 2191087 := bstep (se 1 (by rfl) ⟨1643315, by rfl⟩ : syracuseStep 2191087 = 3286631) B3286631
theorem B3286637 : Blo 2189435 3286637 := bbase (se 3 (by rfl) ⟨616244, by rfl⟩ : syracuseStep 3286637 = 1232489) (by norm_num)
theorem B2191091 : Blo 2189435 2191091 := bstep (se 1 (by rfl) ⟨1643318, by rfl⟩ : syracuseStep 2191091 = 3286637) B3286637
theorem B4929965 : Blo 2189435 4929965 := bbase (se 3 (by rfl) ⟨924368, by rfl⟩ : syracuseStep 4929965 = 1848737) (by norm_num)
theorem B3286643 : Blo 2189435 3286643 := bstep (se 1 (by rfl) ⟨2464982, by rfl⟩ : syracuseStep 3286643 = 4929965) B4929965
theorem B2191095 : Blo 2189435 2191095 := bstep (se 1 (by rfl) ⟨1643321, by rfl⟩ : syracuseStep 2191095 = 3286643) B3286643
theorem B2339813 : Blo 2189435 2339813 := bbase (se 4 (by rfl) ⟨219357, by rfl⟩ : syracuseStep 2339813 = 438715) (by norm_num)
theorem B6239501 : Blo 2189435 6239501 := bstep (se 3 (by rfl) ⟨1169906, by rfl⟩ : syracuseStep 6239501 = 2339813) B2339813
theorem B4159667 : Blo 2189435 4159667 := bstep (se 1 (by rfl) ⟨3119750, by rfl⟩ : syracuseStep 4159667 = 6239501) B6239501
theorem B2773111 : Blo 2189435 2773111 := bstep (se 1 (by rfl) ⟨2079833, by rfl⟩ : syracuseStep 2773111 = 4159667) B4159667
theorem B3697481 : Blo 2189435 3697481 := bstep (se 2 (by rfl) ⟨1386555, by rfl⟩ : syracuseStep 3697481 = 2773111) B2773111
theorem B2464987 : Blo 2189435 2464987 := bstep (se 1 (by rfl) ⟨1848740, by rfl⟩ : syracuseStep 2464987 = 3697481) B3697481
theorem B3286649 : Blo 2189435 3286649 := bstep (se 2 (by rfl) ⟨1232493, by rfl⟩ : syracuseStep 3286649 = 2464987) B2464987
theorem B2191099 : Blo 2189435 2191099 := bstep (se 1 (by rfl) ⟨1643324, by rfl⟩ : syracuseStep 2191099 = 3286649) B3286649
theorem B4940293 : Blo 2189435 4940293 := bbase (se 4 (by rfl) ⟨463152, by rfl⟩ : syracuseStep 4940293 = 926305) (by norm_num)
theorem B6587057 : Blo 2189435 6587057 := bstep (se 2 (by rfl) ⟨2470146, by rfl⟩ : syracuseStep 6587057 = 4940293) B4940293
theorem B4391371 : Blo 2189435 4391371 := bstep (se 1 (by rfl) ⟨3293528, by rfl⟩ : syracuseStep 4391371 = 6587057) B6587057
theorem B5855161 : Blo 2189435 5855161 := bstep (se 2 (by rfl) ⟨2195685, by rfl⟩ : syracuseStep 5855161 = 4391371) B4391371
theorem B7806881 : Blo 2189435 7806881 := bstep (se 2 (by rfl) ⟨2927580, by rfl⟩ : syracuseStep 7806881 = 5855161) B5855161
theorem B5204587 : Blo 2189435 5204587 := bstep (se 1 (by rfl) ⟨3903440, by rfl⟩ : syracuseStep 5204587 = 7806881) B7806881
theorem B6939449 : Blo 2189435 6939449 := bstep (se 2 (by rfl) ⟨2602293, by rfl⟩ : syracuseStep 6939449 = 5204587) B5204587
theorem B4626299 : Blo 2189435 4626299 := bstep (se 1 (by rfl) ⟨3469724, by rfl⟩ : syracuseStep 4626299 = 6939449) B6939449
theorem B3084199 : Blo 2189435 3084199 := bstep (se 1 (by rfl) ⟨2313149, by rfl⟩ : syracuseStep 3084199 = 4626299) B4626299
theorem B65796245 : Blo 2189435 65796245 := bstep (se 6 (by rfl) ⟨1542099, by rfl⟩ : syracuseStep 65796245 = 3084199) B3084199
theorem B43864163 : Blo 2189435 43864163 := bstep (se 1 (by rfl) ⟨32898122, by rfl⟩ : syracuseStep 43864163 = 65796245) B65796245
theorem B29242775 : Blo 2189435 29242775 := bstep (se 1 (by rfl) ⟨21932081, by rfl⟩ : syracuseStep 29242775 = 43864163) B43864163
theorem B19495183 : Blo 2189435 19495183 := bstep (se 1 (by rfl) ⟨14621387, by rfl⟩ : syracuseStep 19495183 = 29242775) B29242775
theorem B25993577 : Blo 2189435 25993577 := bstep (se 2 (by rfl) ⟨9747591, by rfl⟩ : syracuseStep 25993577 = 19495183) B19495183
theorem B17329051 : Blo 2189435 17329051 := bstep (se 1 (by rfl) ⟨12996788, by rfl⟩ : syracuseStep 17329051 = 25993577) B25993577
theorem B23105401 : Blo 2189435 23105401 := bstep (se 2 (by rfl) ⟨8664525, by rfl⟩ : syracuseStep 23105401 = 17329051) B17329051
theorem B123228805 : Blo 2189435 123228805 := bstep (se 4 (by rfl) ⟨11552700, by rfl⟩ : syracuseStep 123228805 = 23105401) B23105401
theorem B164305073 : Blo 2189435 164305073 := bstep (se 2 (by rfl) ⟨61614402, by rfl⟩ : syracuseStep 164305073 = 123228805) B123228805
theorem B109536715 : Blo 2189435 109536715 := bstep (se 1 (by rfl) ⟨82152536, by rfl⟩ : syracuseStep 109536715 = 164305073) B164305073
theorem B146048953 : Blo 2189435 146048953 := bstep (se 2 (by rfl) ⟨54768357, by rfl⟩ : syracuseStep 146048953 = 109536715) B109536715
theorem B194731937 : Blo 2189435 194731937 := bstep (se 2 (by rfl) ⟨73024476, by rfl⟩ : syracuseStep 194731937 = 146048953) B146048953
theorem B129821291 : Blo 2189435 129821291 := bstep (se 1 (by rfl) ⟨97365968, by rfl⟩ : syracuseStep 129821291 = 194731937) B194731937
theorem B86547527 : Blo 2189435 86547527 := bstep (se 1 (by rfl) ⟨64910645, by rfl⟩ : syracuseStep 86547527 = 129821291) B129821291
theorem B57698351 : Blo 2189435 57698351 := bstep (se 1 (by rfl) ⟨43273763, by rfl⟩ : syracuseStep 57698351 = 86547527) B86547527
theorem B38465567 : Blo 2189435 38465567 := bstep (se 1 (by rfl) ⟨28849175, by rfl⟩ : syracuseStep 38465567 = 57698351) B57698351
theorem B25643711 : Blo 2189435 25643711 := bstep (se 1 (by rfl) ⟨19232783, by rfl⟩ : syracuseStep 25643711 = 38465567) B38465567
theorem B17095807 : Blo 2189435 17095807 := bstep (se 1 (by rfl) ⟨12821855, by rfl⟩ : syracuseStep 17095807 = 25643711) B25643711
theorem B22794409 : Blo 2189435 22794409 := bstep (se 2 (by rfl) ⟨8547903, by rfl⟩ : syracuseStep 22794409 = 17095807) B17095807
theorem B30392545 : Blo 2189435 30392545 := bstep (se 2 (by rfl) ⟨11397204, by rfl⟩ : syracuseStep 30392545 = 22794409) B22794409
theorem B40523393 : Blo 2189435 40523393 := bstep (se 2 (by rfl) ⟨15196272, by rfl⟩ : syracuseStep 40523393 = 30392545) B30392545
theorem B108062381 : Blo 2189435 108062381 := bstep (se 3 (by rfl) ⟨20261696, by rfl⟩ : syracuseStep 108062381 = 40523393) B40523393
theorem B288166349 : Blo 2189435 288166349 := bstep (se 3 (by rfl) ⟨54031190, by rfl⟩ : syracuseStep 288166349 = 108062381) B108062381
theorem B192110899 : Blo 2189435 192110899 := bstep (se 1 (by rfl) ⟨144083174, by rfl⟩ : syracuseStep 192110899 = 288166349) B288166349
theorem B256147865 : Blo 2189435 256147865 := bstep (se 2 (by rfl) ⟨96055449, by rfl⟩ : syracuseStep 256147865 = 192110899) B192110899
theorem B170765243 : Blo 2189435 170765243 := bstep (se 1 (by rfl) ⟨128073932, by rfl⟩ : syracuseStep 170765243 = 256147865) B256147865
theorem B113843495 : Blo 2189435 113843495 := bstep (se 1 (by rfl) ⟨85382621, by rfl⟩ : syracuseStep 113843495 = 170765243) B170765243
theorem B75895663 : Blo 2189435 75895663 := bstep (se 1 (by rfl) ⟨56921747, by rfl⟩ : syracuseStep 75895663 = 113843495) B113843495
theorem B101194217 : Blo 2189435 101194217 := bstep (se 2 (by rfl) ⟨37947831, by rfl⟩ : syracuseStep 101194217 = 75895663) B75895663
theorem B67462811 : Blo 2189435 67462811 := bstep (se 1 (by rfl) ⟨50597108, by rfl⟩ : syracuseStep 67462811 = 101194217) B101194217
theorem B44975207 : Blo 2189435 44975207 := bstep (se 1 (by rfl) ⟨33731405, by rfl⟩ : syracuseStep 44975207 = 67462811) B67462811
theorem B119933885 : Blo 2189435 119933885 := bstep (se 3 (by rfl) ⟨22487603, by rfl⟩ : syracuseStep 119933885 = 44975207) B44975207
theorem B79955923 : Blo 2189435 79955923 := bstep (se 1 (by rfl) ⟨59966942, by rfl⟩ : syracuseStep 79955923 = 119933885) B119933885
theorem B106607897 : Blo 2189435 106607897 := bstep (se 2 (by rfl) ⟨39977961, by rfl⟩ : syracuseStep 106607897 = 79955923) B79955923
theorem B71071931 : Blo 2189435 71071931 := bstep (se 1 (by rfl) ⟨53303948, by rfl⟩ : syracuseStep 71071931 = 106607897) B106607897
theorem B47381287 : Blo 2189435 47381287 := bstep (se 1 (by rfl) ⟨35535965, by rfl⟩ : syracuseStep 47381287 = 71071931) B71071931
theorem B63175049 : Blo 2189435 63175049 := bstep (se 2 (by rfl) ⟨23690643, by rfl⟩ : syracuseStep 63175049 = 47381287) B47381287
theorem B42116699 : Blo 2189435 42116699 := bstep (se 1 (by rfl) ⟨31587524, by rfl⟩ : syracuseStep 42116699 = 63175049) B63175049
theorem B28077799 : Blo 2189435 28077799 := bstep (se 1 (by rfl) ⟨21058349, by rfl⟩ : syracuseStep 28077799 = 42116699) B42116699
theorem B37437065 : Blo 2189435 37437065 := bstep (se 2 (by rfl) ⟨14038899, by rfl⟩ : syracuseStep 37437065 = 28077799) B28077799
theorem B24958043 : Blo 2189435 24958043 := bstep (se 1 (by rfl) ⟨18718532, by rfl⟩ : syracuseStep 24958043 = 37437065) B37437065
theorem B16638695 : Blo 2189435 16638695 := bstep (se 1 (by rfl) ⟨12479021, by rfl⟩ : syracuseStep 16638695 = 24958043) B24958043
theorem B11092463 : Blo 2189435 11092463 := bstep (se 1 (by rfl) ⟨8319347, by rfl⟩ : syracuseStep 11092463 = 16638695) B16638695
theorem B7394975 : Blo 2189435 7394975 := bstep (se 1 (by rfl) ⟨5546231, by rfl⟩ : syracuseStep 7394975 = 11092463) B11092463
theorem B4929983 : Blo 2189435 4929983 := bstep (se 1 (by rfl) ⟨3697487, by rfl⟩ : syracuseStep 4929983 = 7394975) B7394975
theorem B3286655 : Blo 2189435 3286655 := bstep (se 1 (by rfl) ⟨2464991, by rfl⟩ : syracuseStep 3286655 = 4929983) B4929983
theorem B2191103 : Blo 2189435 2191103 := bstep (se 1 (by rfl) ⟨1643327, by rfl⟩ : syracuseStep 2191103 = 3286655) B3286655
theorem B3286661 : Blo 2189435 3286661 := bbase (se 4 (by rfl) ⟨308124, by rfl⟩ : syracuseStep 3286661 = 616249) (by norm_num)
theorem B2191107 : Blo 2189435 2191107 := bstep (se 1 (by rfl) ⟨1643330, by rfl⟩ : syracuseStep 2191107 = 3286661) B3286661
theorem B3697501 : Blo 2189435 3697501 := bbase (se 3 (by rfl) ⟨693281, by rfl⟩ : syracuseStep 3697501 = 1386563) (by norm_num)
theorem B4930001 : Blo 2189435 4930001 := bstep (se 2 (by rfl) ⟨1848750, by rfl⟩ : syracuseStep 4930001 = 3697501) B3697501
theorem B3286667 : Blo 2189435 3286667 := bstep (se 1 (by rfl) ⟨2465000, by rfl⟩ : syracuseStep 3286667 = 4930001) B4930001
theorem B2191111 : Blo 2189435 2191111 := bstep (se 1 (by rfl) ⟨1643333, by rfl⟩ : syracuseStep 2191111 = 3286667) B3286667
theorem B2465005 : Blo 2189435 2465005 := bbase (se 3 (by rfl) ⟨462188, by rfl⟩ : syracuseStep 2465005 = 924377) (by norm_num)
theorem B3286673 : Blo 2189435 3286673 := bstep (se 2 (by rfl) ⟨1232502, by rfl⟩ : syracuseStep 3286673 = 2465005) B2465005
theorem B2191115 : Blo 2189435 2191115 := bstep (se 1 (by rfl) ⟨1643336, by rfl⟩ : syracuseStep 2191115 = 3286673) B3286673
theorem B7395029 : Blo 2189435 7395029 := bbase (se 7 (by rfl) ⟨86660, by rfl⟩ : syracuseStep 7395029 = 173321) (by norm_num)
theorem B4930019 : Blo 2189435 4930019 := bstep (se 1 (by rfl) ⟨3697514, by rfl⟩ : syracuseStep 4930019 = 7395029) B7395029
theorem B3286679 : Blo 2189435 3286679 := bstep (se 1 (by rfl) ⟨2465009, by rfl⟩ : syracuseStep 3286679 = 4930019) B4930019
theorem B2191119 : Blo 2189435 2191119 := bstep (se 1 (by rfl) ⟨1643339, by rfl⟩ : syracuseStep 2191119 = 3286679) B3286679
theorem B3286685 : Blo 2189435 3286685 := bbase (se 3 (by rfl) ⟨616253, by rfl⟩ : syracuseStep 3286685 = 1232507) (by norm_num)
theorem B2191123 : Blo 2189435 2191123 := bstep (se 1 (by rfl) ⟨1643342, by rfl⟩ : syracuseStep 2191123 = 3286685) B3286685
theorem B4930037 : Blo 2189435 4930037 := bbase (se 5 (by rfl) ⟨231095, by rfl⟩ : syracuseStep 4930037 = 462191) (by norm_num)
theorem B3286691 : Blo 2189435 3286691 := bstep (se 1 (by rfl) ⟨2465018, by rfl⟩ : syracuseStep 3286691 = 4930037) B4930037
theorem B2191127 : Blo 2189435 2191127 := bstep (se 1 (by rfl) ⟨1643345, by rfl⟩ : syracuseStep 2191127 = 3286691) B3286691
theorem B4002365 : Blo 2189435 4002365 := bbase (se 3 (by rfl) ⟨750443, by rfl⟩ : syracuseStep 4002365 = 1500887) (by norm_num)
theorem B2668243 : Blo 2189435 2668243 := bstep (se 1 (by rfl) ⟨2001182, by rfl⟩ : syracuseStep 2668243 = 4002365) B4002365
theorem B3557657 : Blo 2189435 3557657 := bstep (se 2 (by rfl) ⟨1334121, by rfl⟩ : syracuseStep 3557657 = 2668243) B2668243
theorem B2371771 : Blo 2189435 2371771 := bstep (se 1 (by rfl) ⟨1778828, by rfl⟩ : syracuseStep 2371771 = 3557657) B3557657
theorem B3162361 : Blo 2189435 3162361 := bstep (se 2 (by rfl) ⟨1185885, by rfl⟩ : syracuseStep 3162361 = 2371771) B2371771
theorem B4216481 : Blo 2189435 4216481 := bstep (se 2 (by rfl) ⟨1581180, by rfl⟩ : syracuseStep 4216481 = 3162361) B3162361
theorem B2810987 : Blo 2189435 2810987 := bstep (se 1 (by rfl) ⟨2108240, by rfl⟩ : syracuseStep 2810987 = 4216481) B4216481
theorem B29983861 : Blo 2189435 29983861 := bstep (se 5 (by rfl) ⟨1405493, by rfl⟩ : syracuseStep 29983861 = 2810987) B2810987
theorem B39978481 : Blo 2189435 39978481 := bstep (se 2 (by rfl) ⟨14991930, by rfl⟩ : syracuseStep 39978481 = 29983861) B29983861
theorem B53304641 : Blo 2189435 53304641 := bstep (se 2 (by rfl) ⟨19989240, by rfl⟩ : syracuseStep 53304641 = 39978481) B39978481
theorem B35536427 : Blo 2189435 35536427 := bstep (se 1 (by rfl) ⟨26652320, by rfl⟩ : syracuseStep 35536427 = 53304641) B53304641
theorem B23690951 : Blo 2189435 23690951 := bstep (se 1 (by rfl) ⟨17768213, by rfl⟩ : syracuseStep 23690951 = 35536427) B35536427
theorem B15793967 : Blo 2189435 15793967 := bstep (se 1 (by rfl) ⟨11845475, by rfl⟩ : syracuseStep 15793967 = 23690951) B23690951
theorem B42117245 : Blo 2189435 42117245 := bstep (se 3 (by rfl) ⟨7896983, by rfl⟩ : syracuseStep 42117245 = 15793967) B15793967
theorem B28078163 : Blo 2189435 28078163 := bstep (se 1 (by rfl) ⟨21058622, by rfl⟩ : syracuseStep 28078163 = 42117245) B42117245
theorem B18718775 : Blo 2189435 18718775 := bstep (se 1 (by rfl) ⟨14039081, by rfl⟩ : syracuseStep 18718775 = 28078163) B28078163
theorem B12479183 : Blo 2189435 12479183 := bstep (se 1 (by rfl) ⟨9359387, by rfl⟩ : syracuseStep 12479183 = 18718775) B18718775
theorem B8319455 : Blo 2189435 8319455 := bstep (se 1 (by rfl) ⟨6239591, by rfl⟩ : syracuseStep 8319455 = 12479183) B12479183
theorem B5546303 : Blo 2189435 5546303 := bstep (se 1 (by rfl) ⟨4159727, by rfl⟩ : syracuseStep 5546303 = 8319455) B8319455
theorem B3697535 : Blo 2189435 3697535 := bstep (se 1 (by rfl) ⟨2773151, by rfl⟩ : syracuseStep 3697535 = 5546303) B5546303
theorem B2465023 : Blo 2189435 2465023 := bstep (se 1 (by rfl) ⟨1848767, by rfl⟩ : syracuseStep 2465023 = 3697535) B3697535
theorem B3286697 : Blo 2189435 3286697 := bstep (se 2 (by rfl) ⟨1232511, by rfl⟩ : syracuseStep 3286697 = 2465023) B2465023
theorem B2191131 : Blo 2189435 2191131 := bstep (se 1 (by rfl) ⟨1643348, by rfl⟩ : syracuseStep 2191131 = 3286697) B3286697
theorem B2632333 : Blo 2189435 2632333 := bbase (se 3 (by rfl) ⟨493562, by rfl⟩ : syracuseStep 2632333 = 987125) (by norm_num)
theorem B3509777 : Blo 2189435 3509777 := bstep (se 2 (by rfl) ⟨1316166, by rfl⟩ : syracuseStep 3509777 = 2632333) B2632333
theorem B2339851 : Blo 2189435 2339851 := bstep (se 1 (by rfl) ⟨1754888, by rfl⟩ : syracuseStep 2339851 = 3509777) B3509777
theorem B3119801 : Blo 2189435 3119801 := bstep (se 2 (by rfl) ⟨1169925, by rfl⟩ : syracuseStep 3119801 = 2339851) B2339851
theorem B8319469 : Blo 2189435 8319469 := bstep (se 3 (by rfl) ⟨1559900, by rfl⟩ : syracuseStep 8319469 = 3119801) B3119801
theorem B11092625 : Blo 2189435 11092625 := bstep (se 2 (by rfl) ⟨4159734, by rfl⟩ : syracuseStep 11092625 = 8319469) B8319469
theorem B7395083 : Blo 2189435 7395083 := bstep (se 1 (by rfl) ⟨5546312, by rfl⟩ : syracuseStep 7395083 = 11092625) B11092625
theorem B4930055 : Blo 2189435 4930055 := bstep (se 1 (by rfl) ⟨3697541, by rfl⟩ : syracuseStep 4930055 = 7395083) B7395083
theorem B3286703 : Blo 2189435 3286703 := bstep (se 1 (by rfl) ⟨2465027, by rfl⟩ : syracuseStep 3286703 = 4930055) B4930055
theorem B2191135 : Blo 2189435 2191135 := bstep (se 1 (by rfl) ⟨1643351, by rfl⟩ : syracuseStep 2191135 = 3286703) B3286703
theorem B3286709 : Blo 2189435 3286709 := bbase (se 5 (by rfl) ⟨154064, by rfl⟩ : syracuseStep 3286709 = 308129) (by norm_num)
theorem B2191139 : Blo 2189435 2191139 := bstep (se 1 (by rfl) ⟨1643354, by rfl⟩ : syracuseStep 2191139 = 3286709) B3286709
theorem B5546333 : Blo 2189435 5546333 := bbase (se 3 (by rfl) ⟨1039937, by rfl⟩ : syracuseStep 5546333 = 2079875) (by norm_num)
theorem B3697555 : Blo 2189435 3697555 := bstep (se 1 (by rfl) ⟨2773166, by rfl⟩ : syracuseStep 3697555 = 5546333) B5546333
theorem B4930073 : Blo 2189435 4930073 := bstep (se 2 (by rfl) ⟨1848777, by rfl⟩ : syracuseStep 4930073 = 3697555) B3697555
theorem B3286715 : Blo 2189435 3286715 := bstep (se 1 (by rfl) ⟨2465036, by rfl⟩ : syracuseStep 3286715 = 4930073) B4930073
theorem B2191143 : Blo 2189435 2191143 := bstep (se 1 (by rfl) ⟨1643357, by rfl⟩ : syracuseStep 2191143 = 3286715) B3286715
theorem B2465041 : Blo 2189435 2465041 := bbase (se 2 (by rfl) ⟨924390, by rfl⟩ : syracuseStep 2465041 = 1848781) (by norm_num)
theorem B3286721 : Blo 2189435 3286721 := bstep (se 2 (by rfl) ⟨1232520, by rfl⟩ : syracuseStep 3286721 = 2465041) B2465041
theorem B2191147 : Blo 2189435 2191147 := bstep (se 1 (by rfl) ⟨1643360, by rfl⟩ : syracuseStep 2191147 = 3286721) B3286721
theorem B4159765 : Blo 2189435 4159765 := bbase (se 6 (by rfl) ⟨97494, by rfl⟩ : syracuseStep 4159765 = 194989) (by norm_num)
theorem B5546353 : Blo 2189435 5546353 := bstep (se 2 (by rfl) ⟨2079882, by rfl⟩ : syracuseStep 5546353 = 4159765) B4159765
theorem B7395137 : Blo 2189435 7395137 := bstep (se 2 (by rfl) ⟨2773176, by rfl⟩ : syracuseStep 7395137 = 5546353) B5546353
theorem B4930091 : Blo 2189435 4930091 := bstep (se 1 (by rfl) ⟨3697568, by rfl⟩ : syracuseStep 4930091 = 7395137) B7395137
theorem B3286727 : Blo 2189435 3286727 := bstep (se 1 (by rfl) ⟨2465045, by rfl⟩ : syracuseStep 3286727 = 4930091) B4930091
theorem B2191151 : Blo 2189435 2191151 := bstep (se 1 (by rfl) ⟨1643363, by rfl⟩ : syracuseStep 2191151 = 3286727) B3286727
theorem B3286733 : Blo 2189435 3286733 := bbase (se 3 (by rfl) ⟨616262, by rfl⟩ : syracuseStep 3286733 = 1232525) (by norm_num)
theorem B2191155 : Blo 2189435 2191155 := bstep (se 1 (by rfl) ⟨1643366, by rfl⟩ : syracuseStep 2191155 = 3286733) B3286733
theorem B4930109 : Blo 2189435 4930109 := bbase (se 3 (by rfl) ⟨924395, by rfl⟩ : syracuseStep 4930109 = 1848791) (by norm_num)
theorem B3286739 : Blo 2189435 3286739 := bstep (se 1 (by rfl) ⟨2465054, by rfl⟩ : syracuseStep 3286739 = 4930109) B4930109
theorem B2191159 : Blo 2189435 2191159 := bstep (se 1 (by rfl) ⟨1643369, by rfl⟩ : syracuseStep 2191159 = 3286739) B3286739
theorem B3697589 : Blo 2189435 3697589 := bbase (se 5 (by rfl) ⟨173324, by rfl⟩ : syracuseStep 3697589 = 346649) (by norm_num)
theorem B2465059 : Blo 2189435 2465059 := bstep (se 1 (by rfl) ⟨1848794, by rfl⟩ : syracuseStep 2465059 = 3697589) B3697589
theorem B3286745 : Blo 2189435 3286745 := bstep (se 2 (by rfl) ⟨1232529, by rfl⟩ : syracuseStep 3286745 = 2465059) B2465059
theorem B2191163 : Blo 2189435 2191163 := bstep (se 1 (by rfl) ⟨1643372, by rfl⟩ : syracuseStep 2191163 = 3286745) B3286745
theorem B2339885 : Blo 2189435 2339885 := bbase (se 3 (by rfl) ⟨438728, by rfl⟩ : syracuseStep 2339885 = 877457) (by norm_num)
theorem B6239693 : Blo 2189435 6239693 := bstep (se 3 (by rfl) ⟨1169942, by rfl⟩ : syracuseStep 6239693 = 2339885) B2339885
theorem B16639181 : Blo 2189435 16639181 := bstep (se 3 (by rfl) ⟨3119846, by rfl⟩ : syracuseStep 16639181 = 6239693) B6239693
theorem B11092787 : Blo 2189435 11092787 := bstep (se 1 (by rfl) ⟨8319590, by rfl⟩ : syracuseStep 11092787 = 16639181) B16639181
theorem B7395191 : Blo 2189435 7395191 := bstep (se 1 (by rfl) ⟨5546393, by rfl⟩ : syracuseStep 7395191 = 11092787) B11092787
theorem B4930127 : Blo 2189435 4930127 := bstep (se 1 (by rfl) ⟨3697595, by rfl⟩ : syracuseStep 4930127 = 7395191) B7395191
theorem B3286751 : Blo 2189435 3286751 := bstep (se 1 (by rfl) ⟨2465063, by rfl⟩ : syracuseStep 3286751 = 4930127) B4930127
theorem B2191167 : Blo 2189435 2191167 := bstep (se 1 (by rfl) ⟨1643375, by rfl⟩ : syracuseStep 2191167 = 3286751) B3286751
theorem B3286757 : Blo 2189435 3286757 := bbase (se 4 (by rfl) ⟨308133, by rfl⟩ : syracuseStep 3286757 = 616267) (by norm_num)
theorem B2191171 : Blo 2189435 2191171 := bstep (se 1 (by rfl) ⟨1643378, by rfl⟩ : syracuseStep 2191171 = 3286757) B3286757
theorem B6239717 : Blo 2189435 6239717 := bbase (se 4 (by rfl) ⟨584973, by rfl⟩ : syracuseStep 6239717 = 1169947) (by norm_num)
theorem B4159811 : Blo 2189435 4159811 := bstep (se 1 (by rfl) ⟨3119858, by rfl⟩ : syracuseStep 4159811 = 6239717) B6239717
theorem B2773207 : Blo 2189435 2773207 := bstep (se 1 (by rfl) ⟨2079905, by rfl⟩ : syracuseStep 2773207 = 4159811) B4159811
theorem B3697609 : Blo 2189435 3697609 := bstep (se 2 (by rfl) ⟨1386603, by rfl⟩ : syracuseStep 3697609 = 2773207) B2773207
theorem B4930145 : Blo 2189435 4930145 := bstep (se 2 (by rfl) ⟨1848804, by rfl⟩ : syracuseStep 4930145 = 3697609) B3697609
theorem B3286763 : Blo 2189435 3286763 := bstep (se 1 (by rfl) ⟨2465072, by rfl⟩ : syracuseStep 3286763 = 4930145) B4930145
theorem B2191175 : Blo 2189435 2191175 := bstep (se 1 (by rfl) ⟨1643381, by rfl⟩ : syracuseStep 2191175 = 3286763) B3286763
theorem B2465077 : Blo 2189435 2465077 := bbase (se 5 (by rfl) ⟨115550, by rfl⟩ : syracuseStep 2465077 = 231101) (by norm_num)
theorem B3286769 : Blo 2189435 3286769 := bstep (se 2 (by rfl) ⟨1232538, by rfl⟩ : syracuseStep 3286769 = 2465077) B2465077
theorem B2191179 : Blo 2189435 2191179 := bstep (se 1 (by rfl) ⟨1643384, by rfl⟩ : syracuseStep 2191179 = 3286769) B3286769
theorem B2773217 : Blo 2189435 2773217 := bbase (se 2 (by rfl) ⟨1039956, by rfl⟩ : syracuseStep 2773217 = 2079913) (by norm_num)
theorem B7395245 : Blo 2189435 7395245 := bstep (se 3 (by rfl) ⟨1386608, by rfl⟩ : syracuseStep 7395245 = 2773217) B2773217
theorem B4930163 : Blo 2189435 4930163 := bstep (se 1 (by rfl) ⟨3697622, by rfl⟩ : syracuseStep 4930163 = 7395245) B7395245
theorem B3286775 : Blo 2189435 3286775 := bstep (se 1 (by rfl) ⟨2465081, by rfl⟩ : syracuseStep 3286775 = 4930163) B4930163
theorem B2191183 : Blo 2189435 2191183 := bstep (se 1 (by rfl) ⟨1643387, by rfl⟩ : syracuseStep 2191183 = 3286775) B3286775
theorem B3286781 : Blo 2189435 3286781 := bbase (se 3 (by rfl) ⟨616271, by rfl⟩ : syracuseStep 3286781 = 1232543) (by norm_num)
theorem B2191187 : Blo 2189435 2191187 := bstep (se 1 (by rfl) ⟨1643390, by rfl⟩ : syracuseStep 2191187 = 3286781) B3286781
theorem B4930181 : Blo 2189435 4930181 := bbase (se 4 (by rfl) ⟨462204, by rfl⟩ : syracuseStep 4930181 = 924409) (by norm_num)
theorem B3286787 : Blo 2189435 3286787 := bstep (se 1 (by rfl) ⟨2465090, by rfl⟩ : syracuseStep 3286787 = 4930181) B4930181
theorem B2191191 : Blo 2189435 2191191 := bstep (se 1 (by rfl) ⟨1643393, by rfl⟩ : syracuseStep 2191191 = 3286787) B3286787
theorem B10529621 : Blo 2189435 10529621 := bbase (se 9 (by rfl) ⟨30848, by rfl⟩ : syracuseStep 10529621 = 61697) (by norm_num)
theorem B7019747 : Blo 2189435 7019747 := bstep (se 1 (by rfl) ⟨5264810, by rfl⟩ : syracuseStep 7019747 = 10529621) B10529621
theorem B4679831 : Blo 2189435 4679831 := bstep (se 1 (by rfl) ⟨3509873, by rfl⟩ : syracuseStep 4679831 = 7019747) B7019747
theorem B3119887 : Blo 2189435 3119887 := bstep (se 1 (by rfl) ⟨2339915, by rfl⟩ : syracuseStep 3119887 = 4679831) B4679831
theorem B4159849 : Blo 2189435 4159849 := bstep (se 2 (by rfl) ⟨1559943, by rfl⟩ : syracuseStep 4159849 = 3119887) B3119887
theorem B5546465 : Blo 2189435 5546465 := bstep (se 2 (by rfl) ⟨2079924, by rfl⟩ : syracuseStep 5546465 = 4159849) B4159849
theorem B3697643 : Blo 2189435 3697643 := bstep (se 1 (by rfl) ⟨2773232, by rfl⟩ : syracuseStep 3697643 = 5546465) B5546465
theorem B2465095 : Blo 2189435 2465095 := bstep (se 1 (by rfl) ⟨1848821, by rfl⟩ : syracuseStep 2465095 = 3697643) B3697643
theorem B3286793 : Blo 2189435 3286793 := bstep (se 2 (by rfl) ⟨1232547, by rfl⟩ : syracuseStep 3286793 = 2465095) B2465095
theorem B2191195 : Blo 2189435 2191195 := bstep (se 1 (by rfl) ⟨1643396, by rfl⟩ : syracuseStep 2191195 = 3286793) B3286793
theorem B11092949 : Blo 2189435 11092949 := bbase (se 7 (by rfl) ⟨129995, by rfl⟩ : syracuseStep 11092949 = 259991) (by norm_num)
theorem B7395299 : Blo 2189435 7395299 := bstep (se 1 (by rfl) ⟨5546474, by rfl⟩ : syracuseStep 7395299 = 11092949) B11092949
theorem B4930199 : Blo 2189435 4930199 := bstep (se 1 (by rfl) ⟨3697649, by rfl⟩ : syracuseStep 4930199 = 7395299) B7395299
theorem B3286799 : Blo 2189435 3286799 := bstep (se 1 (by rfl) ⟨2465099, by rfl⟩ : syracuseStep 3286799 = 4930199) B4930199
theorem B2191199 : Blo 2189435 2191199 := bstep (se 1 (by rfl) ⟨1643399, by rfl⟩ : syracuseStep 2191199 = 3286799) B3286799
theorem B3286805 : Blo 2189435 3286805 := bbase (se 6 (by rfl) ⟨77034, by rfl⟩ : syracuseStep 3286805 = 154069) (by norm_num)
theorem B2191203 : Blo 2189435 2191203 := bstep (se 1 (by rfl) ⟨1643402, by rfl⟩ : syracuseStep 2191203 = 3286805) B3286805
theorem B4057109 : Blo 2189435 4057109 := bbase (se 6 (by rfl) ⟨95088, by rfl⟩ : syracuseStep 4057109 = 190177) (by norm_num)
theorem B2704739 : Blo 2189435 2704739 := bstep (se 1 (by rfl) ⟨2028554, by rfl⟩ : syracuseStep 2704739 = 4057109) B4057109
theorem B7212637 : Blo 2189435 7212637 := bstep (se 3 (by rfl) ⟨1352369, by rfl⟩ : syracuseStep 7212637 = 2704739) B2704739
theorem B9616849 : Blo 2189435 9616849 := bstep (se 2 (by rfl) ⟨3606318, by rfl⟩ : syracuseStep 9616849 = 7212637) B7212637
theorem B51289861 : Blo 2189435 51289861 := bstep (se 4 (by rfl) ⟨4808424, by rfl⟩ : syracuseStep 51289861 = 9616849) B9616849
theorem B68386481 : Blo 2189435 68386481 := bstep (se 2 (by rfl) ⟨25644930, by rfl⟩ : syracuseStep 68386481 = 51289861) B51289861
theorem B45590987 : Blo 2189435 45590987 := bstep (se 1 (by rfl) ⟨34193240, by rfl⟩ : syracuseStep 45590987 = 68386481) B68386481
theorem B30393991 : Blo 2189435 30393991 := bstep (se 1 (by rfl) ⟨22795493, by rfl⟩ : syracuseStep 30393991 = 45590987) B45590987
theorem B40525321 : Blo 2189435 40525321 := bstep (se 2 (by rfl) ⟨15196995, by rfl⟩ : syracuseStep 40525321 = 30393991) B30393991
theorem B54033761 : Blo 2189435 54033761 := bstep (se 2 (by rfl) ⟨20262660, by rfl⟩ : syracuseStep 54033761 = 40525321) B40525321
theorem B144090029 : Blo 2189435 144090029 := bstep (se 3 (by rfl) ⟨27016880, by rfl⟩ : syracuseStep 144090029 = 54033761) B54033761
theorem B96060019 : Blo 2189435 96060019 := bstep (se 1 (by rfl) ⟨72045014, by rfl⟩ : syracuseStep 96060019 = 144090029) B144090029
theorem B128080025 : Blo 2189435 128080025 := bstep (se 2 (by rfl) ⟨48030009, by rfl⟩ : syracuseStep 128080025 = 96060019) B96060019
theorem B85386683 : Blo 2189435 85386683 := bstep (se 1 (by rfl) ⟨64040012, by rfl⟩ : syracuseStep 85386683 = 128080025) B128080025
theorem B56924455 : Blo 2189435 56924455 := bstep (se 1 (by rfl) ⟨42693341, by rfl⟩ : syracuseStep 56924455 = 85386683) B85386683
theorem B75899273 : Blo 2189435 75899273 := bstep (se 2 (by rfl) ⟨28462227, by rfl⟩ : syracuseStep 75899273 = 56924455) B56924455
theorem B202398061 : Blo 2189435 202398061 := bstep (se 3 (by rfl) ⟨37949636, by rfl⟩ : syracuseStep 202398061 = 75899273) B75899273
theorem B269864081 : Blo 2189435 269864081 := bstep (se 2 (by rfl) ⟨101199030, by rfl⟩ : syracuseStep 269864081 = 202398061) B202398061
theorem B179909387 : Blo 2189435 179909387 := bstep (se 1 (by rfl) ⟨134932040, by rfl⟩ : syracuseStep 179909387 = 269864081) B269864081
theorem B119939591 : Blo 2189435 119939591 := bstep (se 1 (by rfl) ⟨89954693, by rfl⟩ : syracuseStep 119939591 = 179909387) B179909387
theorem B79959727 : Blo 2189435 79959727 := bstep (se 1 (by rfl) ⟨59969795, by rfl⟩ : syracuseStep 79959727 = 119939591) B119939591
theorem B106612969 : Blo 2189435 106612969 := bstep (se 2 (by rfl) ⟨39979863, by rfl⟩ : syracuseStep 106612969 = 79959727) B79959727
theorem B142150625 : Blo 2189435 142150625 := bstep (se 2 (by rfl) ⟨53306484, by rfl⟩ : syracuseStep 142150625 = 106612969) B106612969
theorem B94767083 : Blo 2189435 94767083 := bstep (se 1 (by rfl) ⟨71075312, by rfl⟩ : syracuseStep 94767083 = 142150625) B142150625
theorem B63178055 : Blo 2189435 63178055 := bstep (se 1 (by rfl) ⟨47383541, by rfl⟩ : syracuseStep 63178055 = 94767083) B94767083
theorem B42118703 : Blo 2189435 42118703 := bstep (se 1 (by rfl) ⟨31589027, by rfl⟩ : syracuseStep 42118703 = 63178055) B63178055
theorem B28079135 : Blo 2189435 28079135 := bstep (se 1 (by rfl) ⟨21059351, by rfl⟩ : syracuseStep 28079135 = 42118703) B42118703
theorem B18719423 : Blo 2189435 18719423 := bstep (se 1 (by rfl) ⟨14039567, by rfl⟩ : syracuseStep 18719423 = 28079135) B28079135
theorem B12479615 : Blo 2189435 12479615 := bstep (se 1 (by rfl) ⟨9359711, by rfl⟩ : syracuseStep 12479615 = 18719423) B18719423
theorem B8319743 : Blo 2189435 8319743 := bstep (se 1 (by rfl) ⟨6239807, by rfl⟩ : syracuseStep 8319743 = 12479615) B12479615
theorem B5546495 : Blo 2189435 5546495 := bstep (se 1 (by rfl) ⟨4159871, by rfl⟩ : syracuseStep 5546495 = 8319743) B8319743
theorem B3697663 : Blo 2189435 3697663 := bstep (se 1 (by rfl) ⟨2773247, by rfl⟩ : syracuseStep 3697663 = 5546495) B5546495
theorem B4930217 : Blo 2189435 4930217 := bstep (se 2 (by rfl) ⟨1848831, by rfl⟩ : syracuseStep 4930217 = 3697663) B3697663
theorem B3286811 : Blo 2189435 3286811 := bstep (se 1 (by rfl) ⟨2465108, by rfl⟩ : syracuseStep 3286811 = 4930217) B4930217
theorem B2191207 : Blo 2189435 2191207 := bstep (se 1 (by rfl) ⟨1643405, by rfl⟩ : syracuseStep 2191207 = 3286811) B3286811
theorem B2465113 : Blo 2189435 2465113 := bbase (se 2 (by rfl) ⟨924417, by rfl⟩ : syracuseStep 2465113 = 1848835) (by norm_num)
theorem B3286817 : Blo 2189435 3286817 := bstep (se 2 (by rfl) ⟨1232556, by rfl⟩ : syracuseStep 3286817 = 2465113) B2465113
theorem B2191211 : Blo 2189435 2191211 := bstep (se 1 (by rfl) ⟨1643408, by rfl⟩ : syracuseStep 2191211 = 3286817) B3286817
theorem B2632429 : Blo 2189435 2632429 := bbase (se 3 (by rfl) ⟨493580, by rfl⟩ : syracuseStep 2632429 = 987161) (by norm_num)
theorem B3509905 : Blo 2189435 3509905 := bstep (se 2 (by rfl) ⟨1316214, by rfl⟩ : syracuseStep 3509905 = 2632429) B2632429
theorem B4679873 : Blo 2189435 4679873 := bstep (se 2 (by rfl) ⟨1754952, by rfl⟩ : syracuseStep 4679873 = 3509905) B3509905
theorem B3119915 : Blo 2189435 3119915 := bstep (se 1 (by rfl) ⟨2339936, by rfl⟩ : syracuseStep 3119915 = 4679873) B4679873
theorem B8319773 : Blo 2189435 8319773 := bstep (se 3 (by rfl) ⟨1559957, by rfl⟩ : syracuseStep 8319773 = 3119915) B3119915
theorem B5546515 : Blo 2189435 5546515 := bstep (se 1 (by rfl) ⟨4159886, by rfl⟩ : syracuseStep 5546515 = 8319773) B8319773
theorem B7395353 : Blo 2189435 7395353 := bstep (se 2 (by rfl) ⟨2773257, by rfl⟩ : syracuseStep 7395353 = 5546515) B5546515
theorem B4930235 : Blo 2189435 4930235 := bstep (se 1 (by rfl) ⟨3697676, by rfl⟩ : syracuseStep 4930235 = 7395353) B7395353
theorem B3286823 : Blo 2189435 3286823 := bstep (se 1 (by rfl) ⟨2465117, by rfl⟩ : syracuseStep 3286823 = 4930235) B4930235
theorem B2191215 : Blo 2189435 2191215 := bstep (se 1 (by rfl) ⟨1643411, by rfl⟩ : syracuseStep 2191215 = 3286823) B3286823
theorem B3286829 : Blo 2189435 3286829 := bbase (se 3 (by rfl) ⟨616280, by rfl⟩ : syracuseStep 3286829 = 1232561) (by norm_num)
theorem B2191219 : Blo 2189435 2191219 := bstep (se 1 (by rfl) ⟨1643414, by rfl⟩ : syracuseStep 2191219 = 3286829) B3286829
theorem B4930253 : Blo 2189435 4930253 := bbase (se 3 (by rfl) ⟨924422, by rfl⟩ : syracuseStep 4930253 = 1848845) (by norm_num)
theorem B3286835 : Blo 2189435 3286835 := bstep (se 1 (by rfl) ⟨2465126, by rfl⟩ : syracuseStep 3286835 = 4930253) B4930253
theorem B2191223 : Blo 2189435 2191223 := bstep (se 1 (by rfl) ⟨1643417, by rfl⟩ : syracuseStep 2191223 = 3286835) B3286835
theorem B2773273 : Blo 2189435 2773273 := bbase (se 2 (by rfl) ⟨1039977, by rfl⟩ : syracuseStep 2773273 = 2079955) (by norm_num)
theorem B3697697 : Blo 2189435 3697697 := bstep (se 2 (by rfl) ⟨1386636, by rfl⟩ : syracuseStep 3697697 = 2773273) B2773273
theorem B2465131 : Blo 2189435 2465131 := bstep (se 1 (by rfl) ⟨1848848, by rfl⟩ : syracuseStep 2465131 = 3697697) B3697697
theorem B3286841 : Blo 2189435 3286841 := bstep (se 2 (by rfl) ⟨1232565, by rfl⟩ : syracuseStep 3286841 = 2465131) B2465131
theorem B2191227 : Blo 2189435 2191227 := bstep (se 1 (by rfl) ⟨1643420, by rfl⟩ : syracuseStep 2191227 = 3286841) B3286841
theorem B9359813 : Blo 2189435 9359813 := bbase (se 4 (by rfl) ⟨877482, by rfl⟩ : syracuseStep 9359813 = 1754965) (by norm_num)
theorem B24959501 : Blo 2189435 24959501 := bstep (se 3 (by rfl) ⟨4679906, by rfl⟩ : syracuseStep 24959501 = 9359813) B9359813
theorem B16639667 : Blo 2189435 16639667 := bstep (se 1 (by rfl) ⟨12479750, by rfl⟩ : syracuseStep 16639667 = 24959501) B24959501
theorem B11093111 : Blo 2189435 11093111 := bstep (se 1 (by rfl) ⟨8319833, by rfl⟩ : syracuseStep 11093111 = 16639667) B16639667
theorem B7395407 : Blo 2189435 7395407 := bstep (se 1 (by rfl) ⟨5546555, by rfl⟩ : syracuseStep 7395407 = 11093111) B11093111
theorem B4930271 : Blo 2189435 4930271 := bstep (se 1 (by rfl) ⟨3697703, by rfl⟩ : syracuseStep 4930271 = 7395407) B7395407
theorem B3286847 : Blo 2189435 3286847 := bstep (se 1 (by rfl) ⟨2465135, by rfl⟩ : syracuseStep 3286847 = 4930271) B4930271
theorem B2191231 : Blo 2189435 2191231 := bstep (se 1 (by rfl) ⟨1643423, by rfl⟩ : syracuseStep 2191231 = 3286847) B3286847
theorem B3286853 : Blo 2189435 3286853 := bbase (se 4 (by rfl) ⟨308142, by rfl⟩ : syracuseStep 3286853 = 616285) (by norm_num)
theorem B2191235 : Blo 2189435 2191235 := bstep (se 1 (by rfl) ⟨1643426, by rfl⟩ : syracuseStep 2191235 = 3286853) B3286853
theorem B3697717 : Blo 2189435 3697717 := bbase (se 5 (by rfl) ⟨173330, by rfl⟩ : syracuseStep 3697717 = 346661) (by norm_num)
theorem B4930289 : Blo 2189435 4930289 := bstep (se 2 (by rfl) ⟨1848858, by rfl⟩ : syracuseStep 4930289 = 3697717) B3697717
theorem B3286859 : Blo 2189435 3286859 := bstep (se 1 (by rfl) ⟨2465144, by rfl⟩ : syracuseStep 3286859 = 4930289) B4930289
theorem B2191239 : Blo 2189435 2191239 := bstep (se 1 (by rfl) ⟨1643429, by rfl⟩ : syracuseStep 2191239 = 3286859) B3286859
theorem B2465149 : Blo 2189435 2465149 := bbase (se 3 (by rfl) ⟨462215, by rfl⟩ : syracuseStep 2465149 = 924431) (by norm_num)
theorem B3286865 : Blo 2189435 3286865 := bstep (se 2 (by rfl) ⟨1232574, by rfl⟩ : syracuseStep 3286865 = 2465149) B2465149
theorem B2191243 : Blo 2189435 2191243 := bstep (se 1 (by rfl) ⟨1643432, by rfl⟩ : syracuseStep 2191243 = 3286865) B3286865
theorem B7395461 : Blo 2189435 7395461 := bbase (se 4 (by rfl) ⟨693324, by rfl⟩ : syracuseStep 7395461 = 1386649) (by norm_num)
theorem B4930307 : Blo 2189435 4930307 := bstep (se 1 (by rfl) ⟨3697730, by rfl⟩ : syracuseStep 4930307 = 7395461) B7395461
theorem B3286871 : Blo 2189435 3286871 := bstep (se 1 (by rfl) ⟨2465153, by rfl⟩ : syracuseStep 3286871 = 4930307) B4930307
theorem B2191247 : Blo 2189435 2191247 := bstep (se 1 (by rfl) ⟨1643435, by rfl⟩ : syracuseStep 2191247 = 3286871) B3286871
theorem B3286877 : Blo 2189435 3286877 := bbase (se 3 (by rfl) ⟨616289, by rfl⟩ : syracuseStep 3286877 = 1232579) (by norm_num)
theorem B2191251 : Blo 2189435 2191251 := bstep (se 1 (by rfl) ⟨1643438, by rfl⟩ : syracuseStep 2191251 = 3286877) B3286877
theorem B4930325 : Blo 2189435 4930325 := bbase (se 6 (by rfl) ⟨115554, by rfl⟩ : syracuseStep 4930325 = 231109) (by norm_num)
theorem B3286883 : Blo 2189435 3286883 := bstep (se 1 (by rfl) ⟨2465162, by rfl⟩ : syracuseStep 3286883 = 4930325) B4930325
theorem B2191255 : Blo 2189435 2191255 := bstep (se 1 (by rfl) ⟨1643441, by rfl⟩ : syracuseStep 2191255 = 3286883) B3286883
theorem B8319941 : Blo 2189435 8319941 := bbase (se 4 (by rfl) ⟨779994, by rfl⟩ : syracuseStep 8319941 = 1559989) (by norm_num)
theorem B5546627 : Blo 2189435 5546627 := bstep (se 1 (by rfl) ⟨4159970, by rfl⟩ : syracuseStep 5546627 = 8319941) B8319941
theorem B3697751 : Blo 2189435 3697751 := bstep (se 1 (by rfl) ⟨2773313, by rfl⟩ : syracuseStep 3697751 = 5546627) B5546627
theorem B2465167 : Blo 2189435 2465167 := bstep (se 1 (by rfl) ⟨1848875, by rfl⟩ : syracuseStep 2465167 = 3697751) B3697751
theorem B3286889 : Blo 2189435 3286889 := bstep (se 2 (by rfl) ⟨1232583, by rfl⟩ : syracuseStep 3286889 = 2465167) B2465167
theorem B2191259 : Blo 2189435 2191259 := bstep (se 1 (by rfl) ⟨1643444, by rfl⟩ : syracuseStep 2191259 = 3286889) B3286889
theorem B3331741 : Blo 2189435 3331741 := bbase (se 3 (by rfl) ⟨624701, by rfl⟩ : syracuseStep 3331741 = 1249403) (by norm_num)
theorem B4442321 : Blo 2189435 4442321 := bstep (se 2 (by rfl) ⟨1665870, by rfl⟩ : syracuseStep 4442321 = 3331741) B3331741
theorem B11846189 : Blo 2189435 11846189 := bstep (se 3 (by rfl) ⟨2221160, by rfl⟩ : syracuseStep 11846189 = 4442321) B4442321
theorem B7897459 : Blo 2189435 7897459 := bstep (se 1 (by rfl) ⟨5923094, by rfl⟩ : syracuseStep 7897459 = 11846189) B11846189
theorem B10529945 : Blo 2189435 10529945 := bstep (se 2 (by rfl) ⟨3948729, by rfl⟩ : syracuseStep 10529945 = 7897459) B7897459
theorem B7019963 : Blo 2189435 7019963 := bstep (se 1 (by rfl) ⟨5264972, by rfl⟩ : syracuseStep 7019963 = 10529945) B10529945
theorem B4679975 : Blo 2189435 4679975 := bstep (se 1 (by rfl) ⟨3509981, by rfl⟩ : syracuseStep 4679975 = 7019963) B7019963
theorem B12479933 : Blo 2189435 12479933 := bstep (se 3 (by rfl) ⟨2339987, by rfl⟩ : syracuseStep 12479933 = 4679975) B4679975
theorem B8319955 : Blo 2189435 8319955 := bstep (se 1 (by rfl) ⟨6239966, by rfl⟩ : syracuseStep 8319955 = 12479933) B12479933
theorem B11093273 : Blo 2189435 11093273 := bstep (se 2 (by rfl) ⟨4159977, by rfl⟩ : syracuseStep 11093273 = 8319955) B8319955
theorem B7395515 : Blo 2189435 7395515 := bstep (se 1 (by rfl) ⟨5546636, by rfl⟩ : syracuseStep 7395515 = 11093273) B11093273
theorem B4930343 : Blo 2189435 4930343 := bstep (se 1 (by rfl) ⟨3697757, by rfl⟩ : syracuseStep 4930343 = 7395515) B7395515
theorem B3286895 : Blo 2189435 3286895 := bstep (se 1 (by rfl) ⟨2465171, by rfl⟩ : syracuseStep 3286895 = 4930343) B4930343
theorem B2191263 : Blo 2189435 2191263 := bstep (se 1 (by rfl) ⟨1643447, by rfl⟩ : syracuseStep 2191263 = 3286895) B3286895
theorem B3286901 : Blo 2189435 3286901 := bbase (se 5 (by rfl) ⟨154073, by rfl⟩ : syracuseStep 3286901 = 308147) (by norm_num)
theorem B2191267 : Blo 2189435 2191267 := bstep (se 1 (by rfl) ⟨1643450, by rfl⟩ : syracuseStep 2191267 = 3286901) B3286901
theorem B6663509 : Blo 2189435 6663509 := bbase (se 11 (by rfl) ⟨4880, by rfl⟩ : syracuseStep 6663509 = 9761) (by norm_num)
theorem B4442339 : Blo 2189435 4442339 := bstep (se 1 (by rfl) ⟨3331754, by rfl⟩ : syracuseStep 4442339 = 6663509) B6663509
theorem B2961559 : Blo 2189435 2961559 := bstep (se 1 (by rfl) ⟨2221169, by rfl⟩ : syracuseStep 2961559 = 4442339) B4442339
theorem B3948745 : Blo 2189435 3948745 := bstep (se 2 (by rfl) ⟨1480779, by rfl⟩ : syracuseStep 3948745 = 2961559) B2961559
theorem B5264993 : Blo 2189435 5264993 := bstep (se 2 (by rfl) ⟨1974372, by rfl⟩ : syracuseStep 5264993 = 3948745) B3948745
theorem B3509995 : Blo 2189435 3509995 := bstep (se 1 (by rfl) ⟨2632496, by rfl⟩ : syracuseStep 3509995 = 5264993) B5264993
theorem B4679993 : Blo 2189435 4679993 := bstep (se 2 (by rfl) ⟨1754997, by rfl⟩ : syracuseStep 4679993 = 3509995) B3509995
theorem B3119995 : Blo 2189435 3119995 := bstep (se 1 (by rfl) ⟨2339996, by rfl⟩ : syracuseStep 3119995 = 4679993) B4679993
theorem B4159993 : Blo 2189435 4159993 := bstep (se 2 (by rfl) ⟨1559997, by rfl⟩ : syracuseStep 4159993 = 3119995) B3119995
theorem B5546657 : Blo 2189435 5546657 := bstep (se 2 (by rfl) ⟨2079996, by rfl⟩ : syracuseStep 5546657 = 4159993) B4159993
theorem B3697771 : Blo 2189435 3697771 := bstep (se 1 (by rfl) ⟨2773328, by rfl⟩ : syracuseStep 3697771 = 5546657) B5546657
theorem B4930361 : Blo 2189435 4930361 := bstep (se 2 (by rfl) ⟨1848885, by rfl⟩ : syracuseStep 4930361 = 3697771) B3697771
theorem B3286907 : Blo 2189435 3286907 := bstep (se 1 (by rfl) ⟨2465180, by rfl⟩ : syracuseStep 3286907 = 4930361) B4930361
theorem B2191271 : Blo 2189435 2191271 := bstep (se 1 (by rfl) ⟨1643453, by rfl⟩ : syracuseStep 2191271 = 3286907) B3286907
theorem B2465185 : Blo 2189435 2465185 := bbase (se 2 (by rfl) ⟨924444, by rfl⟩ : syracuseStep 2465185 = 1848889) (by norm_num)
theorem B3286913 : Blo 2189435 3286913 := bstep (se 2 (by rfl) ⟨1232592, by rfl⟩ : syracuseStep 3286913 = 2465185) B2465185
theorem B2191275 : Blo 2189435 2191275 := bstep (se 1 (by rfl) ⟨1643456, by rfl⟩ : syracuseStep 2191275 = 3286913) B3286913
theorem B5546677 : Blo 2189435 5546677 := bbase (se 5 (by rfl) ⟨260000, by rfl⟩ : syracuseStep 5546677 = 520001) (by norm_num)
theorem B7395569 : Blo 2189435 7395569 := bstep (se 2 (by rfl) ⟨2773338, by rfl⟩ : syracuseStep 7395569 = 5546677) B5546677
theorem B4930379 : Blo 2189435 4930379 := bstep (se 1 (by rfl) ⟨3697784, by rfl⟩ : syracuseStep 4930379 = 7395569) B7395569
theorem B3286919 : Blo 2189435 3286919 := bstep (se 1 (by rfl) ⟨2465189, by rfl⟩ : syracuseStep 3286919 = 4930379) B4930379
theorem B2191279 : Blo 2189435 2191279 := bstep (se 1 (by rfl) ⟨1643459, by rfl⟩ : syracuseStep 2191279 = 3286919) B3286919
theorem B3286925 : Blo 2189435 3286925 := bbase (se 3 (by rfl) ⟨616298, by rfl⟩ : syracuseStep 3286925 = 1232597) (by norm_num)
theorem B2191283 : Blo 2189435 2191283 := bstep (se 1 (by rfl) ⟨1643462, by rfl⟩ : syracuseStep 2191283 = 3286925) B3286925
theorem B4930397 : Blo 2189435 4930397 := bbase (se 3 (by rfl) ⟨924449, by rfl⟩ : syracuseStep 4930397 = 1848899) (by norm_num)
theorem B3286931 : Blo 2189435 3286931 := bstep (se 1 (by rfl) ⟨2465198, by rfl⟩ : syracuseStep 3286931 = 4930397) B4930397
theorem B2191287 : Blo 2189435 2191287 := bstep (se 1 (by rfl) ⟨1643465, by rfl⟩ : syracuseStep 2191287 = 3286931) B3286931
theorem B3697805 : Blo 2189435 3697805 := bbase (se 3 (by rfl) ⟨693338, by rfl⟩ : syracuseStep 3697805 = 1386677) (by norm_num)
theorem B2465203 : Blo 2189435 2465203 := bstep (se 1 (by rfl) ⟨1848902, by rfl⟩ : syracuseStep 2465203 = 3697805) B3697805
theorem B3286937 : Blo 2189435 3286937 := bstep (se 2 (by rfl) ⟨1232601, by rfl⟩ : syracuseStep 3286937 = 2465203) B2465203
theorem B2191291 : Blo 2189435 2191291 := bstep (se 1 (by rfl) ⟨1643468, by rfl⟩ : syracuseStep 2191291 = 3286937) B3286937
theorem B2221193 : Blo 2189435 2221193 := bbase (se 2 (by rfl) ⟨832947, by rfl⟩ : syracuseStep 2221193 = 1665895) (by norm_num)
theorem B5923181 : Blo 2189435 5923181 := bstep (se 3 (by rfl) ⟨1110596, by rfl⟩ : syracuseStep 5923181 = 2221193) B2221193
theorem B3948787 : Blo 2189435 3948787 := bstep (se 1 (by rfl) ⟨2961590, by rfl⟩ : syracuseStep 3948787 = 5923181) B5923181
theorem B5265049 : Blo 2189435 5265049 := bstep (se 2 (by rfl) ⟨1974393, by rfl⟩ : syracuseStep 5265049 = 3948787) B3948787
theorem B7020065 : Blo 2189435 7020065 := bstep (se 2 (by rfl) ⟨2632524, by rfl⟩ : syracuseStep 7020065 = 5265049) B5265049
theorem B18720173 : Blo 2189435 18720173 := bstep (se 3 (by rfl) ⟨3510032, by rfl⟩ : syracuseStep 18720173 = 7020065) B7020065
theorem B12480115 : Blo 2189435 12480115 := bstep (se 1 (by rfl) ⟨9360086, by rfl⟩ : syracuseStep 12480115 = 18720173) B18720173
theorem B16640153 : Blo 2189435 16640153 := bstep (se 2 (by rfl) ⟨6240057, by rfl⟩ : syracuseStep 16640153 = 12480115) B12480115
theorem B11093435 : Blo 2189435 11093435 := bstep (se 1 (by rfl) ⟨8320076, by rfl⟩ : syracuseStep 11093435 = 16640153) B16640153
theorem B7395623 : Blo 2189435 7395623 := bstep (se 1 (by rfl) ⟨5546717, by rfl⟩ : syracuseStep 7395623 = 11093435) B11093435
theorem B4930415 : Blo 2189435 4930415 := bstep (se 1 (by rfl) ⟨3697811, by rfl⟩ : syracuseStep 4930415 = 7395623) B7395623
theorem B3286943 : Blo 2189435 3286943 := bstep (se 1 (by rfl) ⟨2465207, by rfl⟩ : syracuseStep 3286943 = 4930415) B4930415
theorem B2191295 : Blo 2189435 2191295 := bstep (se 1 (by rfl) ⟨1643471, by rfl⟩ : syracuseStep 2191295 = 3286943) B3286943
theorem B3286949 : Blo 2189435 3286949 := bbase (se 4 (by rfl) ⟨308151, by rfl⟩ : syracuseStep 3286949 = 616303) (by norm_num)
theorem B2191299 : Blo 2189435 2191299 := bstep (se 1 (by rfl) ⟨1643474, by rfl⟩ : syracuseStep 2191299 = 3286949) B3286949
theorem B2773369 : Blo 2189435 2773369 := bbase (se 2 (by rfl) ⟨1040013, by rfl⟩ : syracuseStep 2773369 = 2080027) (by norm_num)
theorem B3697825 : Blo 2189435 3697825 := bstep (se 2 (by rfl) ⟨1386684, by rfl⟩ : syracuseStep 3697825 = 2773369) B2773369
theorem B4930433 : Blo 2189435 4930433 := bstep (se 2 (by rfl) ⟨1848912, by rfl⟩ : syracuseStep 4930433 = 3697825) B3697825
theorem B3286955 : Blo 2189435 3286955 := bstep (se 1 (by rfl) ⟨2465216, by rfl⟩ : syracuseStep 3286955 = 4930433) B4930433
theorem B2191303 : Blo 2189435 2191303 := bstep (se 1 (by rfl) ⟨1643477, by rfl⟩ : syracuseStep 2191303 = 3286955) B3286955
theorem B2465221 : Blo 2189435 2465221 := bbase (se 4 (by rfl) ⟨231114, by rfl⟩ : syracuseStep 2465221 = 462229) (by norm_num)
theorem B3286961 : Blo 2189435 3286961 := bstep (se 2 (by rfl) ⟨1232610, by rfl⟩ : syracuseStep 3286961 = 2465221) B2465221
theorem B2191307 : Blo 2189435 2191307 := bstep (se 1 (by rfl) ⟨1643480, by rfl⟩ : syracuseStep 2191307 = 3286961) B3286961
theorem B4160069 : Blo 2189435 4160069 := bbase (se 4 (by rfl) ⟨390006, by rfl⟩ : syracuseStep 4160069 = 780013) (by norm_num)
theorem B2773379 : Blo 2189435 2773379 := bstep (se 1 (by rfl) ⟨2080034, by rfl⟩ : syracuseStep 2773379 = 4160069) B4160069
theorem B7395677 : Blo 2189435 7395677 := bstep (se 3 (by rfl) ⟨1386689, by rfl⟩ : syracuseStep 7395677 = 2773379) B2773379
theorem B4930451 : Blo 2189435 4930451 := bstep (se 1 (by rfl) ⟨3697838, by rfl⟩ : syracuseStep 4930451 = 7395677) B7395677
theorem B3286967 : Blo 2189435 3286967 := bstep (se 1 (by rfl) ⟨2465225, by rfl⟩ : syracuseStep 3286967 = 4930451) B4930451
theorem B2191311 : Blo 2189435 2191311 := bstep (se 1 (by rfl) ⟨1643483, by rfl⟩ : syracuseStep 2191311 = 3286967) B3286967
theorem B3286973 : Blo 2189435 3286973 := bbase (se 3 (by rfl) ⟨616307, by rfl⟩ : syracuseStep 3286973 = 1232615) (by norm_num)
theorem B2191315 : Blo 2189435 2191315 := bstep (se 1 (by rfl) ⟨1643486, by rfl⟩ : syracuseStep 2191315 = 3286973) B3286973
theorem B4930469 : Blo 2189435 4930469 := bbase (se 4 (by rfl) ⟨462231, by rfl⟩ : syracuseStep 4930469 = 924463) (by norm_num)
theorem B3286979 : Blo 2189435 3286979 := bstep (se 1 (by rfl) ⟨2465234, by rfl⟩ : syracuseStep 3286979 = 4930469) B4930469
theorem B2191319 : Blo 2189435 2191319 := bstep (se 1 (by rfl) ⟨1643489, by rfl⟩ : syracuseStep 2191319 = 3286979) B3286979
theorem B5546789 : Blo 2189435 5546789 := bbase (se 4 (by rfl) ⟨520011, by rfl⟩ : syracuseStep 5546789 = 1040023) (by norm_num)
theorem B3697859 : Blo 2189435 3697859 := bstep (se 1 (by rfl) ⟨2773394, by rfl⟩ : syracuseStep 3697859 = 5546789) B5546789
theorem B2465239 : Blo 2189435 2465239 := bstep (se 1 (by rfl) ⟨1848929, by rfl⟩ : syracuseStep 2465239 = 3697859) B3697859
theorem B3286985 : Blo 2189435 3286985 := bstep (se 2 (by rfl) ⟨1232619, by rfl⟩ : syracuseStep 3286985 = 2465239) B2465239
theorem B2191323 : Blo 2189435 2191323 := bstep (se 1 (by rfl) ⟨1643492, by rfl⟩ : syracuseStep 2191323 = 3286985) B3286985
theorem B6240149 : Blo 2189435 6240149 := bbase (se 6 (by rfl) ⟨146253, by rfl⟩ : syracuseStep 6240149 = 292507) (by norm_num)
theorem B4160099 : Blo 2189435 4160099 := bstep (se 1 (by rfl) ⟨3120074, by rfl⟩ : syracuseStep 4160099 = 6240149) B6240149
theorem B11093597 : Blo 2189435 11093597 := bstep (se 3 (by rfl) ⟨2080049, by rfl⟩ : syracuseStep 11093597 = 4160099) B4160099
theorem B7395731 : Blo 2189435 7395731 := bstep (se 1 (by rfl) ⟨5546798, by rfl⟩ : syracuseStep 7395731 = 11093597) B11093597
theorem B4930487 : Blo 2189435 4930487 := bstep (se 1 (by rfl) ⟨3697865, by rfl⟩ : syracuseStep 4930487 = 7395731) B7395731
theorem B3286991 : Blo 2189435 3286991 := bstep (se 1 (by rfl) ⟨2465243, by rfl⟩ : syracuseStep 3286991 = 4930487) B4930487
theorem B2191327 : Blo 2189435 2191327 := bstep (se 1 (by rfl) ⟨1643495, by rfl⟩ : syracuseStep 2191327 = 3286991) B3286991
theorem B3286997 : Blo 2189435 3286997 := bbase (se 7 (by rfl) ⟨38519, by rfl⟩ : syracuseStep 3286997 = 77039) (by norm_num)
theorem B2191331 : Blo 2189435 2191331 := bstep (se 1 (by rfl) ⟨1643498, by rfl⟩ : syracuseStep 2191331 = 3286997) B3286997
theorem B8320229 : Blo 2189435 8320229 := bbase (se 4 (by rfl) ⟨780021, by rfl⟩ : syracuseStep 8320229 = 1560043) (by norm_num)
theorem B5546819 : Blo 2189435 5546819 := bstep (se 1 (by rfl) ⟨4160114, by rfl⟩ : syracuseStep 5546819 = 8320229) B8320229
theorem B3697879 : Blo 2189435 3697879 := bstep (se 1 (by rfl) ⟨2773409, by rfl⟩ : syracuseStep 3697879 = 5546819) B5546819
theorem B4930505 : Blo 2189435 4930505 := bstep (se 2 (by rfl) ⟨1848939, by rfl⟩ : syracuseStep 4930505 = 3697879) B3697879
theorem B3287003 : Blo 2189435 3287003 := bstep (se 1 (by rfl) ⟨2465252, by rfl⟩ : syracuseStep 3287003 = 4930505) B4930505
theorem B2191335 : Blo 2189435 2191335 := bstep (se 1 (by rfl) ⟨1643501, by rfl⟩ : syracuseStep 2191335 = 3287003) B3287003
theorem B2465257 : Blo 2189435 2465257 := bbase (se 2 (by rfl) ⟨924471, by rfl⟩ : syracuseStep 2465257 = 1848943) (by norm_num)
theorem B3287009 : Blo 2189435 3287009 := bstep (se 2 (by rfl) ⟨1232628, by rfl⟩ : syracuseStep 3287009 = 2465257) B2465257
theorem B2191339 : Blo 2189435 2191339 := bstep (se 1 (by rfl) ⟨1643504, by rfl⟩ : syracuseStep 2191339 = 3287009) B3287009
theorem B2340073 : Blo 2189435 2340073 := bbase (se 2 (by rfl) ⟨877527, by rfl⟩ : syracuseStep 2340073 = 1755055) (by norm_num)
theorem B12480389 : Blo 2189435 12480389 := bstep (se 4 (by rfl) ⟨1170036, by rfl⟩ : syracuseStep 12480389 = 2340073) B2340073
theorem B8320259 : Blo 2189435 8320259 := bstep (se 1 (by rfl) ⟨6240194, by rfl⟩ : syracuseStep 8320259 = 12480389) B12480389
theorem B5546839 : Blo 2189435 5546839 := bstep (se 1 (by rfl) ⟨4160129, by rfl⟩ : syracuseStep 5546839 = 8320259) B8320259
theorem B7395785 : Blo 2189435 7395785 := bstep (se 2 (by rfl) ⟨2773419, by rfl⟩ : syracuseStep 7395785 = 5546839) B5546839
theorem B4930523 : Blo 2189435 4930523 := bstep (se 1 (by rfl) ⟨3697892, by rfl⟩ : syracuseStep 4930523 = 7395785) B7395785
theorem B3287015 : Blo 2189435 3287015 := bstep (se 1 (by rfl) ⟨2465261, by rfl⟩ : syracuseStep 3287015 = 4930523) B4930523
theorem B2191343 : Blo 2189435 2191343 := bstep (se 1 (by rfl) ⟨1643507, by rfl⟩ : syracuseStep 2191343 = 3287015) B3287015
theorem B3287021 : Blo 2189435 3287021 := bbase (se 3 (by rfl) ⟨616316, by rfl⟩ : syracuseStep 3287021 = 1232633) (by norm_num)
theorem B2191347 : Blo 2189435 2191347 := bstep (se 1 (by rfl) ⟨1643510, by rfl⟩ : syracuseStep 2191347 = 3287021) B3287021
theorem B4930541 : Blo 2189435 4930541 := bbase (se 3 (by rfl) ⟨924476, by rfl⟩ : syracuseStep 4930541 = 1848953) (by norm_num)
theorem B3287027 : Blo 2189435 3287027 := bstep (se 1 (by rfl) ⟨2465270, by rfl⟩ : syracuseStep 3287027 = 4930541) B4930541
theorem B2191351 : Blo 2189435 2191351 := bstep (se 1 (by rfl) ⟨1643513, by rfl⟩ : syracuseStep 2191351 = 3287027) B3287027
theorem B4680173 : Blo 2189435 4680173 := bbase (se 3 (by rfl) ⟨877532, by rfl⟩ : syracuseStep 4680173 = 1755065) (by norm_num)
theorem B3120115 : Blo 2189435 3120115 := bstep (se 1 (by rfl) ⟨2340086, by rfl⟩ : syracuseStep 3120115 = 4680173) B4680173
theorem B4160153 : Blo 2189435 4160153 := bstep (se 2 (by rfl) ⟨1560057, by rfl⟩ : syracuseStep 4160153 = 3120115) B3120115
theorem B2773435 : Blo 2189435 2773435 := bstep (se 1 (by rfl) ⟨2080076, by rfl⟩ : syracuseStep 2773435 = 4160153) B4160153
theorem B3697913 : Blo 2189435 3697913 := bstep (se 2 (by rfl) ⟨1386717, by rfl⟩ : syracuseStep 3697913 = 2773435) B2773435
theorem B2465275 : Blo 2189435 2465275 := bstep (se 1 (by rfl) ⟨1848956, by rfl⟩ : syracuseStep 2465275 = 3697913) B3697913
theorem B3287033 : Blo 2189435 3287033 := bstep (se 2 (by rfl) ⟨1232637, by rfl⟩ : syracuseStep 3287033 = 2465275) B2465275
theorem B2191355 : Blo 2189435 2191355 := bstep (se 1 (by rfl) ⟨1643516, by rfl⟩ : syracuseStep 2191355 = 3287033) B3287033
theorem B10132037 : Blo 2189435 10132037 := bbase (se 4 (by rfl) ⟨949878, by rfl⟩ : syracuseStep 10132037 = 1899757) (by norm_num)
theorem B6754691 : Blo 2189435 6754691 := bstep (se 1 (by rfl) ⟨5066018, by rfl⟩ : syracuseStep 6754691 = 10132037) B10132037
theorem B4503127 : Blo 2189435 4503127 := bstep (se 1 (by rfl) ⟨3377345, by rfl⟩ : syracuseStep 4503127 = 6754691) B6754691
theorem B6004169 : Blo 2189435 6004169 := bstep (se 2 (by rfl) ⟨2251563, by rfl⟩ : syracuseStep 6004169 = 4503127) B4503127
theorem B4002779 : Blo 2189435 4002779 := bstep (se 1 (by rfl) ⟨3002084, by rfl⟩ : syracuseStep 4002779 = 6004169) B6004169
theorem B2668519 : Blo 2189435 2668519 := bstep (se 1 (by rfl) ⟨2001389, by rfl⟩ : syracuseStep 2668519 = 4002779) B4002779
theorem B3558025 : Blo 2189435 3558025 := bstep (se 2 (by rfl) ⟨1334259, by rfl⟩ : syracuseStep 3558025 = 2668519) B2668519
theorem B4744033 : Blo 2189435 4744033 := bstep (se 2 (by rfl) ⟨1779012, by rfl⟩ : syracuseStep 4744033 = 3558025) B3558025
theorem B101206037 : Blo 2189435 101206037 := bstep (se 6 (by rfl) ⟨2372016, by rfl⟩ : syracuseStep 101206037 = 4744033) B4744033
theorem B269882765 : Blo 2189435 269882765 := bstep (se 3 (by rfl) ⟨50603018, by rfl⟩ : syracuseStep 269882765 = 101206037) B101206037
theorem B179921843 : Blo 2189435 179921843 := bstep (se 1 (by rfl) ⟨134941382, by rfl⟩ : syracuseStep 179921843 = 269882765) B269882765
theorem B119947895 : Blo 2189435 119947895 := bstep (se 1 (by rfl) ⟨89960921, by rfl⟩ : syracuseStep 119947895 = 179921843) B179921843
theorem B79965263 : Blo 2189435 79965263 := bstep (se 1 (by rfl) ⟨59973947, by rfl⟩ : syracuseStep 79965263 = 119947895) B119947895
theorem B213240701 : Blo 2189435 213240701 := bstep (se 3 (by rfl) ⟨39982631, by rfl⟩ : syracuseStep 213240701 = 79965263) B79965263
theorem B142160467 : Blo 2189435 142160467 := bstep (se 1 (by rfl) ⟨106620350, by rfl⟩ : syracuseStep 142160467 = 213240701) B213240701
theorem B189547289 : Blo 2189435 189547289 := bstep (se 2 (by rfl) ⟨71080233, by rfl⟩ : syracuseStep 189547289 = 142160467) B142160467
theorem B126364859 : Blo 2189435 126364859 := bstep (se 1 (by rfl) ⟨94773644, by rfl⟩ : syracuseStep 126364859 = 189547289) B189547289
theorem B84243239 : Blo 2189435 84243239 := bstep (se 1 (by rfl) ⟨63182429, by rfl⟩ : syracuseStep 84243239 = 126364859) B126364859
theorem B56162159 : Blo 2189435 56162159 := bstep (se 1 (by rfl) ⟨42121619, by rfl⟩ : syracuseStep 56162159 = 84243239) B84243239
theorem B37441439 : Blo 2189435 37441439 := bstep (se 1 (by rfl) ⟨28081079, by rfl⟩ : syracuseStep 37441439 = 56162159) B56162159
theorem B24960959 : Blo 2189435 24960959 := bstep (se 1 (by rfl) ⟨18720719, by rfl⟩ : syracuseStep 24960959 = 37441439) B37441439
theorem B16640639 : Blo 2189435 16640639 := bstep (se 1 (by rfl) ⟨12480479, by rfl⟩ : syracuseStep 16640639 = 24960959) B24960959
theorem B11093759 : Blo 2189435 11093759 := bstep (se 1 (by rfl) ⟨8320319, by rfl⟩ : syracuseStep 11093759 = 16640639) B16640639
theorem B7395839 : Blo 2189435 7395839 := bstep (se 1 (by rfl) ⟨5546879, by rfl⟩ : syracuseStep 7395839 = 11093759) B11093759
theorem B4930559 : Blo 2189435 4930559 := bstep (se 1 (by rfl) ⟨3697919, by rfl⟩ : syracuseStep 4930559 = 7395839) B7395839
theorem B3287039 : Blo 2189435 3287039 := bstep (se 1 (by rfl) ⟨2465279, by rfl⟩ : syracuseStep 3287039 = 4930559) B4930559
theorem B2191359 : Blo 2189435 2191359 := bstep (se 1 (by rfl) ⟨1643519, by rfl⟩ : syracuseStep 2191359 = 3287039) B3287039
theorem B3287045 : Blo 2189435 3287045 := bbase (se 4 (by rfl) ⟨308160, by rfl⟩ : syracuseStep 3287045 = 616321) (by norm_num)
theorem B2191363 : Blo 2189435 2191363 := bstep (se 1 (by rfl) ⟨1643522, by rfl⟩ : syracuseStep 2191363 = 3287045) B3287045
theorem B3697933 : Blo 2189435 3697933 := bbase (se 3 (by rfl) ⟨693362, by rfl⟩ : syracuseStep 3697933 = 1386725) (by norm_num)
theorem B4930577 : Blo 2189435 4930577 := bstep (se 2 (by rfl) ⟨1848966, by rfl⟩ : syracuseStep 4930577 = 3697933) B3697933
theorem B3287051 : Blo 2189435 3287051 := bstep (se 1 (by rfl) ⟨2465288, by rfl⟩ : syracuseStep 3287051 = 4930577) B4930577
theorem B2191367 : Blo 2189435 2191367 := bstep (se 1 (by rfl) ⟨1643525, by rfl⟩ : syracuseStep 2191367 = 3287051) B3287051
theorem B2465293 : Blo 2189435 2465293 := bbase (se 3 (by rfl) ⟨462242, by rfl⟩ : syracuseStep 2465293 = 924485) (by norm_num)
theorem B3287057 : Blo 2189435 3287057 := bstep (se 2 (by rfl) ⟨1232646, by rfl⟩ : syracuseStep 3287057 = 2465293) B2465293
theorem B2191371 : Blo 2189435 2191371 := bstep (se 1 (by rfl) ⟨1643528, by rfl⟩ : syracuseStep 2191371 = 3287057) B3287057
theorem B7395893 : Blo 2189435 7395893 := bbase (se 5 (by rfl) ⟨346682, by rfl⟩ : syracuseStep 7395893 = 693365) (by norm_num)
theorem B4930595 : Blo 2189435 4930595 := bstep (se 1 (by rfl) ⟨3697946, by rfl⟩ : syracuseStep 4930595 = 7395893) B7395893
theorem B3287063 : Blo 2189435 3287063 := bstep (se 1 (by rfl) ⟨2465297, by rfl⟩ : syracuseStep 3287063 = 4930595) B4930595
theorem B2191375 : Blo 2189435 2191375 := bstep (se 1 (by rfl) ⟨1643531, by rfl⟩ : syracuseStep 2191375 = 3287063) B3287063
theorem B3287069 : Blo 2189435 3287069 := bbase (se 3 (by rfl) ⟨616325, by rfl⟩ : syracuseStep 3287069 = 1232651) (by norm_num)
theorem B2191379 : Blo 2189435 2191379 := bstep (se 1 (by rfl) ⟨1643534, by rfl⟩ : syracuseStep 2191379 = 3287069) B3287069
theorem B4930613 : Blo 2189435 4930613 := bbase (se 5 (by rfl) ⟨231122, by rfl⟩ : syracuseStep 4930613 = 462245) (by norm_num)
theorem B3287075 : Blo 2189435 3287075 := bstep (se 1 (by rfl) ⟨2465306, by rfl⟩ : syracuseStep 3287075 = 4930613) B4930613
theorem B2191383 : Blo 2189435 2191383 := bstep (se 1 (by rfl) ⟨1643537, by rfl⟩ : syracuseStep 2191383 = 3287075) B3287075
theorem B4442573 : Blo 2189435 4442573 := bbase (se 3 (by rfl) ⟨832982, by rfl⟩ : syracuseStep 4442573 = 1665965) (by norm_num)
theorem B11846861 : Blo 2189435 11846861 := bstep (se 3 (by rfl) ⟨2221286, by rfl⟩ : syracuseStep 11846861 = 4442573) B4442573
theorem B7897907 : Blo 2189435 7897907 := bstep (se 1 (by rfl) ⟨5923430, by rfl⟩ : syracuseStep 7897907 = 11846861) B11846861
theorem B5265271 : Blo 2189435 5265271 := bstep (se 1 (by rfl) ⟨3948953, by rfl⟩ : syracuseStep 5265271 = 7897907) B7897907
theorem B7020361 : Blo 2189435 7020361 := bstep (se 2 (by rfl) ⟨2632635, by rfl⟩ : syracuseStep 7020361 = 5265271) B5265271
theorem B9360481 : Blo 2189435 9360481 := bstep (se 2 (by rfl) ⟨3510180, by rfl⟩ : syracuseStep 9360481 = 7020361) B7020361
theorem B12480641 : Blo 2189435 12480641 := bstep (se 2 (by rfl) ⟨4680240, by rfl⟩ : syracuseStep 12480641 = 9360481) B9360481
theorem B8320427 : Blo 2189435 8320427 := bstep (se 1 (by rfl) ⟨6240320, by rfl⟩ : syracuseStep 8320427 = 12480641) B12480641
theorem B5546951 : Blo 2189435 5546951 := bstep (se 1 (by rfl) ⟨4160213, by rfl⟩ : syracuseStep 5546951 = 8320427) B8320427
theorem B3697967 : Blo 2189435 3697967 := bstep (se 1 (by rfl) ⟨2773475, by rfl⟩ : syracuseStep 3697967 = 5546951) B5546951
theorem B2465311 : Blo 2189435 2465311 := bstep (se 1 (by rfl) ⟨1848983, by rfl⟩ : syracuseStep 2465311 = 3697967) B3697967
theorem B3287081 : Blo 2189435 3287081 := bstep (se 2 (by rfl) ⟨1232655, by rfl⟩ : syracuseStep 3287081 = 2465311) B2465311
theorem B2191387 : Blo 2189435 2191387 := bstep (se 1 (by rfl) ⟨1643540, by rfl⟩ : syracuseStep 2191387 = 3287081) B3287081
theorem B7020373 : Blo 2189435 7020373 := bbase (se 9 (by rfl) ⟨20567, by rfl⟩ : syracuseStep 7020373 = 41135) (by norm_num)
theorem B9360497 : Blo 2189435 9360497 := bstep (se 2 (by rfl) ⟨3510186, by rfl⟩ : syracuseStep 9360497 = 7020373) B7020373
theorem B6240331 : Blo 2189435 6240331 := bstep (se 1 (by rfl) ⟨4680248, by rfl⟩ : syracuseStep 6240331 = 9360497) B9360497
theorem B8320441 : Blo 2189435 8320441 := bstep (se 2 (by rfl) ⟨3120165, by rfl⟩ : syracuseStep 8320441 = 6240331) B6240331
theorem B11093921 : Blo 2189435 11093921 := bstep (se 2 (by rfl) ⟨4160220, by rfl⟩ : syracuseStep 11093921 = 8320441) B8320441
theorem B7395947 : Blo 2189435 7395947 := bstep (se 1 (by rfl) ⟨5546960, by rfl⟩ : syracuseStep 7395947 = 11093921) B11093921
theorem B4930631 : Blo 2189435 4930631 := bstep (se 1 (by rfl) ⟨3697973, by rfl⟩ : syracuseStep 4930631 = 7395947) B7395947
theorem B3287087 : Blo 2189435 3287087 := bstep (se 1 (by rfl) ⟨2465315, by rfl⟩ : syracuseStep 3287087 = 4930631) B4930631
theorem B2191391 : Blo 2189435 2191391 := bstep (se 1 (by rfl) ⟨1643543, by rfl⟩ : syracuseStep 2191391 = 3287087) B3287087
theorem B3287093 : Blo 2189435 3287093 := bbase (se 5 (by rfl) ⟨154082, by rfl⟩ : syracuseStep 3287093 = 308165) (by norm_num)
theorem B2191395 : Blo 2189435 2191395 := bstep (se 1 (by rfl) ⟨1643546, by rfl⟩ : syracuseStep 2191395 = 3287093) B3287093
theorem B5546981 : Blo 2189435 5546981 := bbase (se 4 (by rfl) ⟨520029, by rfl⟩ : syracuseStep 5546981 = 1040059) (by norm_num)
theorem B3697987 : Blo 2189435 3697987 := bstep (se 1 (by rfl) ⟨2773490, by rfl⟩ : syracuseStep 3697987 = 5546981) B5546981
theorem B4930649 : Blo 2189435 4930649 := bstep (se 2 (by rfl) ⟨1848993, by rfl⟩ : syracuseStep 4930649 = 3697987) B3697987
theorem B3287099 : Blo 2189435 3287099 := bstep (se 1 (by rfl) ⟨2465324, by rfl⟩ : syracuseStep 3287099 = 4930649) B4930649
theorem B2191399 : Blo 2189435 2191399 := bstep (se 1 (by rfl) ⟨1643549, by rfl⟩ : syracuseStep 2191399 = 3287099) B3287099
theorem B2465329 : Blo 2189435 2465329 := bbase (se 2 (by rfl) ⟨924498, by rfl⟩ : syracuseStep 2465329 = 1848997) (by norm_num)
theorem B3287105 : Blo 2189435 3287105 := bstep (se 2 (by rfl) ⟨1232664, by rfl⟩ : syracuseStep 3287105 = 2465329) B2465329
theorem B2191403 : Blo 2189435 2191403 := bstep (se 1 (by rfl) ⟨1643552, by rfl⟩ : syracuseStep 2191403 = 3287105) B3287105
theorem B21348629 : Blo 2189435 21348629 := bbase (se 6 (by rfl) ⟨500358, by rfl⟩ : syracuseStep 21348629 = 1000717) (by norm_num)
theorem B14232419 : Blo 2189435 14232419 := bstep (se 1 (by rfl) ⟨10674314, by rfl⟩ : syracuseStep 14232419 = 21348629) B21348629
theorem B9488279 : Blo 2189435 9488279 := bstep (se 1 (by rfl) ⟨7116209, by rfl⟩ : syracuseStep 9488279 = 14232419) B14232419
theorem B25302077 : Blo 2189435 25302077 := bstep (se 3 (by rfl) ⟨4744139, by rfl⟩ : syracuseStep 25302077 = 9488279) B9488279
theorem B16868051 : Blo 2189435 16868051 := bstep (se 1 (by rfl) ⟨12651038, by rfl⟩ : syracuseStep 16868051 = 25302077) B25302077
theorem B11245367 : Blo 2189435 11245367 := bstep (se 1 (by rfl) ⟨8434025, by rfl⟩ : syracuseStep 11245367 = 16868051) B16868051
theorem B7496911 : Blo 2189435 7496911 := bstep (se 1 (by rfl) ⟨5622683, by rfl⟩ : syracuseStep 7496911 = 11245367) B11245367
theorem B9995881 : Blo 2189435 9995881 := bstep (se 2 (by rfl) ⟨3748455, by rfl⟩ : syracuseStep 9995881 = 7496911) B7496911
theorem B13327841 : Blo 2189435 13327841 := bstep (se 2 (by rfl) ⟨4997940, by rfl⟩ : syracuseStep 13327841 = 9995881) B9995881
theorem B8885227 : Blo 2189435 8885227 := bstep (se 1 (by rfl) ⟨6663920, by rfl⟩ : syracuseStep 8885227 = 13327841) B13327841
theorem B11846969 : Blo 2189435 11846969 := bstep (se 2 (by rfl) ⟨4442613, by rfl⟩ : syracuseStep 11846969 = 8885227) B8885227
theorem B7897979 : Blo 2189435 7897979 := bstep (se 1 (by rfl) ⟨5923484, by rfl⟩ : syracuseStep 7897979 = 11846969) B11846969
theorem B5265319 : Blo 2189435 5265319 := bstep (se 1 (by rfl) ⟨3948989, by rfl⟩ : syracuseStep 5265319 = 7897979) B7897979
theorem B7020425 : Blo 2189435 7020425 := bstep (se 2 (by rfl) ⟨2632659, by rfl⟩ : syracuseStep 7020425 = 5265319) B5265319
theorem B4680283 : Blo 2189435 4680283 := bstep (se 1 (by rfl) ⟨3510212, by rfl⟩ : syracuseStep 4680283 = 7020425) B7020425
theorem B6240377 : Blo 2189435 6240377 := bstep (se 2 (by rfl) ⟨2340141, by rfl⟩ : syracuseStep 6240377 = 4680283) B4680283
theorem B4160251 : Blo 2189435 4160251 := bstep (se 1 (by rfl) ⟨3120188, by rfl⟩ : syracuseStep 4160251 = 6240377) B6240377
theorem B5547001 : Blo 2189435 5547001 := bstep (se 2 (by rfl) ⟨2080125, by rfl⟩ : syracuseStep 5547001 = 4160251) B4160251
theorem B7396001 : Blo 2189435 7396001 := bstep (se 2 (by rfl) ⟨2773500, by rfl⟩ : syracuseStep 7396001 = 5547001) B5547001
theorem B4930667 : Blo 2189435 4930667 := bstep (se 1 (by rfl) ⟨3698000, by rfl⟩ : syracuseStep 4930667 = 7396001) B7396001
theorem B3287111 : Blo 2189435 3287111 := bstep (se 1 (by rfl) ⟨2465333, by rfl⟩ : syracuseStep 3287111 = 4930667) B4930667
theorem B2191407 : Blo 2189435 2191407 := bstep (se 1 (by rfl) ⟨1643555, by rfl⟩ : syracuseStep 2191407 = 3287111) B3287111
theorem B3287117 : Blo 2189435 3287117 := bbase (se 3 (by rfl) ⟨616334, by rfl⟩ : syracuseStep 3287117 = 1232669) (by norm_num)
theorem B2191411 : Blo 2189435 2191411 := bstep (se 1 (by rfl) ⟨1643558, by rfl⟩ : syracuseStep 2191411 = 3287117) B3287117
theorem B4930685 : Blo 2189435 4930685 := bbase (se 3 (by rfl) ⟨924503, by rfl⟩ : syracuseStep 4930685 = 1849007) (by norm_num)
theorem B3287123 : Blo 2189435 3287123 := bstep (se 1 (by rfl) ⟨2465342, by rfl⟩ : syracuseStep 3287123 = 4930685) B4930685
theorem B2191415 : Blo 2189435 2191415 := bstep (se 1 (by rfl) ⟨1643561, by rfl⟩ : syracuseStep 2191415 = 3287123) B3287123
theorem B3698021 : Blo 2189435 3698021 := bbase (se 4 (by rfl) ⟨346689, by rfl⟩ : syracuseStep 3698021 = 693379) (by norm_num)
theorem B2465347 : Blo 2189435 2465347 := bstep (se 1 (by rfl) ⟨1849010, by rfl⟩ : syracuseStep 2465347 = 3698021) B3698021
theorem B3287129 : Blo 2189435 3287129 := bstep (se 2 (by rfl) ⟨1232673, by rfl⟩ : syracuseStep 3287129 = 2465347) B2465347
theorem B2191419 : Blo 2189435 2191419 := bstep (se 1 (by rfl) ⟨1643564, by rfl⟩ : syracuseStep 2191419 = 3287129) B3287129
theorem B4680317 : Blo 2189435 4680317 := bbase (se 3 (by rfl) ⟨877559, by rfl⟩ : syracuseStep 4680317 = 1755119) (by norm_num)
theorem B3120211 : Blo 2189435 3120211 := bstep (se 1 (by rfl) ⟨2340158, by rfl⟩ : syracuseStep 3120211 = 4680317) B4680317
theorem B16641125 : Blo 2189435 16641125 := bstep (se 4 (by rfl) ⟨1560105, by rfl⟩ : syracuseStep 16641125 = 3120211) B3120211
theorem B11094083 : Blo 2189435 11094083 := bstep (se 1 (by rfl) ⟨8320562, by rfl⟩ : syracuseStep 11094083 = 16641125) B16641125
theorem B7396055 : Blo 2189435 7396055 := bstep (se 1 (by rfl) ⟨5547041, by rfl⟩ : syracuseStep 7396055 = 11094083) B11094083
theorem B4930703 : Blo 2189435 4930703 := bstep (se 1 (by rfl) ⟨3698027, by rfl⟩ : syracuseStep 4930703 = 7396055) B7396055
theorem B3287135 : Blo 2189435 3287135 := bstep (se 1 (by rfl) ⟨2465351, by rfl⟩ : syracuseStep 3287135 = 4930703) B4930703
theorem B2191423 : Blo 2189435 2191423 := bstep (se 1 (by rfl) ⟨1643567, by rfl⟩ : syracuseStep 2191423 = 3287135) B3287135
theorem B3287141 : Blo 2189435 3287141 := bbase (se 4 (by rfl) ⟨308169, by rfl⟩ : syracuseStep 3287141 = 616339) (by norm_num)
theorem B2191427 : Blo 2189435 2191427 := bstep (se 1 (by rfl) ⟨1643570, by rfl⟩ : syracuseStep 2191427 = 3287141) B3287141
theorem B11245493 : Blo 2189435 11245493 := bbase (se 5 (by rfl) ⟨527132, by rfl⟩ : syracuseStep 11245493 = 1054265) (by norm_num)
theorem B7496995 : Blo 2189435 7496995 := bstep (se 1 (by rfl) ⟨5622746, by rfl⟩ : syracuseStep 7496995 = 11245493) B11245493
theorem B9995993 : Blo 2189435 9995993 := bstep (se 2 (by rfl) ⟨3748497, by rfl⟩ : syracuseStep 9995993 = 7496995) B7496995
theorem B6663995 : Blo 2189435 6663995 := bstep (se 1 (by rfl) ⟨4997996, by rfl⟩ : syracuseStep 6663995 = 9995993) B9995993
theorem B4442663 : Blo 2189435 4442663 := bstep (se 1 (by rfl) ⟨3331997, by rfl⟩ : syracuseStep 4442663 = 6663995) B6663995
theorem B2961775 : Blo 2189435 2961775 := bstep (se 1 (by rfl) ⟨2221331, by rfl⟩ : syracuseStep 2961775 = 4442663) B4442663
theorem B15796133 : Blo 2189435 15796133 := bstep (se 4 (by rfl) ⟨1480887, by rfl⟩ : syracuseStep 15796133 = 2961775) B2961775
theorem B10530755 : Blo 2189435 10530755 := bstep (se 1 (by rfl) ⟨7898066, by rfl⟩ : syracuseStep 10530755 = 15796133) B15796133
theorem B7020503 : Blo 2189435 7020503 := bstep (se 1 (by rfl) ⟨5265377, by rfl⟩ : syracuseStep 7020503 = 10530755) B10530755
theorem B4680335 : Blo 2189435 4680335 := bstep (se 1 (by rfl) ⟨3510251, by rfl⟩ : syracuseStep 4680335 = 7020503) B7020503
theorem B3120223 : Blo 2189435 3120223 := bstep (se 1 (by rfl) ⟨2340167, by rfl⟩ : syracuseStep 3120223 = 4680335) B4680335
theorem B4160297 : Blo 2189435 4160297 := bstep (se 2 (by rfl) ⟨1560111, by rfl⟩ : syracuseStep 4160297 = 3120223) B3120223
theorem B2773531 : Blo 2189435 2773531 := bstep (se 1 (by rfl) ⟨2080148, by rfl⟩ : syracuseStep 2773531 = 4160297) B4160297
theorem B3698041 : Blo 2189435 3698041 := bstep (se 2 (by rfl) ⟨1386765, by rfl⟩ : syracuseStep 3698041 = 2773531) B2773531
theorem B4930721 : Blo 2189435 4930721 := bstep (se 2 (by rfl) ⟨1849020, by rfl⟩ : syracuseStep 4930721 = 3698041) B3698041
theorem B3287147 : Blo 2189435 3287147 := bstep (se 1 (by rfl) ⟨2465360, by rfl⟩ : syracuseStep 3287147 = 4930721) B4930721
theorem B2191431 : Blo 2189435 2191431 := bstep (se 1 (by rfl) ⟨1643573, by rfl⟩ : syracuseStep 2191431 = 3287147) B3287147
theorem B2465365 : Blo 2189435 2465365 := bbase (se 8 (by rfl) ⟨14445, by rfl⟩ : syracuseStep 2465365 = 28891) (by norm_num)
theorem B3287153 : Blo 2189435 3287153 := bstep (se 2 (by rfl) ⟨1232682, by rfl⟩ : syracuseStep 3287153 = 2465365) B2465365
theorem B2191435 : Blo 2189435 2191435 := bstep (se 1 (by rfl) ⟨1643576, by rfl⟩ : syracuseStep 2191435 = 3287153) B3287153
theorem C0 (j : ℕ) (h1 : 547358 ≤ j) (h2 : j ≤ 547858) : Blo 2189435 (4 * j + 3) := by
  interval_cases j
  · exact B2189435
  · exact B2189439
  · exact B2189443
  · exact B2189447
  · exact B2189451
  · exact B2189455
  · exact B2189459
  · exact B2189463
  · exact B2189467
  · exact B2189471
  · exact B2189475
  · exact B2189479
  · exact B2189483
  · exact B2189487
  · exact B2189491
  · exact B2189495
  · exact B2189499
  · exact B2189503
  · exact B2189507
  · exact B2189511
  · exact B2189515
  · exact B2189519
  · exact B2189523
  · exact B2189527
  · exact B2189531
  · exact B2189535
  · exact B2189539
  · exact B2189543
  · exact B2189547
  · exact B2189551
  · exact B2189555
  · exact B2189559
  · exact B2189563
  · exact B2189567
  · exact B2189571
  · exact B2189575
  · exact B2189579
  · exact B2189583
  · exact B2189587
  · exact B2189591
  · exact B2189595
  · exact B2189599
  · exact B2189603
  · exact B2189607
  · exact B2189611
  · exact B2189615
  · exact B2189619
  · exact B2189623
  · exact B2189627
  · exact B2189631
  · exact B2189635
  · exact B2189639
  · exact B2189643
  · exact B2189647
  · exact B2189651
  · exact B2189655
  · exact B2189659
  · exact B2189663
  · exact B2189667
  · exact B2189671
  · exact B2189675
  · exact B2189679
  · exact B2189683
  · exact B2189687
  · exact B2189691
  · exact B2189695
  · exact B2189699
  · exact B2189703
  · exact B2189707
  · exact B2189711
  · exact B2189715
  · exact B2189719
  · exact B2189723
  · exact B2189727
  · exact B2189731
  · exact B2189735
  · exact B2189739
  · exact B2189743
  · exact B2189747
  · exact B2189751
  · exact B2189755
  · exact B2189759
  · exact B2189763
  · exact B2189767
  · exact B2189771
  · exact B2189775
  · exact B2189779
  · exact B2189783
  · exact B2189787
  · exact B2189791
  · exact B2189795
  · exact B2189799
  · exact B2189803
  · exact B2189807
  · exact B2189811
  · exact B2189815
  · exact B2189819
  · exact B2189823
  · exact B2189827
  · exact B2189831
  · exact B2189835
  · exact B2189839
  · exact B2189843
  · exact B2189847
  · exact B2189851
  · exact B2189855
  · exact B2189859
  · exact B2189863
  · exact B2189867
  · exact B2189871
  · exact B2189875
  · exact B2189879
  · exact B2189883
  · exact B2189887
  · exact B2189891
  · exact B2189895
  · exact B2189899
  · exact B2189903
  · exact B2189907
  · exact B2189911
  · exact B2189915
  · exact B2189919
  · exact B2189923
  · exact B2189927
  · exact B2189931
  · exact B2189935
  · exact B2189939
  · exact B2189943
  · exact B2189947
  · exact B2189951
  · exact B2189955
  · exact B2189959
  · exact B2189963
  · exact B2189967
  · exact B2189971
  · exact B2189975
  · exact B2189979
  · exact B2189983
  · exact B2189987
  · exact B2189991
  · exact B2189995
  · exact B2189999
  · exact B2190003
  · exact B2190007
  · exact B2190011
  · exact B2190015
  · exact B2190019
  · exact B2190023
  · exact B2190027
  · exact B2190031
  · exact B2190035
  · exact B2190039
  · exact B2190043
  · exact B2190047
  · exact B2190051
  · exact B2190055
  · exact B2190059
  · exact B2190063
  · exact B2190067
  · exact B2190071
  · exact B2190075
  · exact B2190079
  · exact B2190083
  · exact B2190087
  · exact B2190091
  · exact B2190095
  · exact B2190099
  · exact B2190103
  · exact B2190107
  · exact B2190111
  · exact B2190115
  · exact B2190119
  · exact B2190123
  · exact B2190127
  · exact B2190131
  · exact B2190135
  · exact B2190139
  · exact B2190143
  · exact B2190147
  · exact B2190151
  · exact B2190155
  · exact B2190159
  · exact B2190163
  · exact B2190167
  · exact B2190171
  · exact B2190175
  · exact B2190179
  · exact B2190183
  · exact B2190187
  · exact B2190191
  · exact B2190195
  · exact B2190199
  · exact B2190203
  · exact B2190207
  · exact B2190211
  · exact B2190215
  · exact B2190219
  · exact B2190223
  · exact B2190227
  · exact B2190231
  · exact B2190235
  · exact B2190239
  · exact B2190243
  · exact B2190247
  · exact B2190251
  · exact B2190255
  · exact B2190259
  · exact B2190263
  · exact B2190267
  · exact B2190271
  · exact B2190275
  · exact B2190279
  · exact B2190283
  · exact B2190287
  · exact B2190291
  · exact B2190295
  · exact B2190299
  · exact B2190303
  · exact B2190307
  · exact B2190311
  · exact B2190315
  · exact B2190319
  · exact B2190323
  · exact B2190327
  · exact B2190331
  · exact B2190335
  · exact B2190339
  · exact B2190343
  · exact B2190347
  · exact B2190351
  · exact B2190355
  · exact B2190359
  · exact B2190363
  · exact B2190367
  · exact B2190371
  · exact B2190375
  · exact B2190379
  · exact B2190383
  · exact B2190387
  · exact B2190391
  · exact B2190395
  · exact B2190399
  · exact B2190403
  · exact B2190407
  · exact B2190411
  · exact B2190415
  · exact B2190419
  · exact B2190423
  · exact B2190427
  · exact B2190431
  · exact B2190435
  · exact B2190439
  · exact B2190443
  · exact B2190447
  · exact B2190451
  · exact B2190455
  · exact B2190459
  · exact B2190463
  · exact B2190467
  · exact B2190471
  · exact B2190475
  · exact B2190479
  · exact B2190483
  · exact B2190487
  · exact B2190491
  · exact B2190495
  · exact B2190499
  · exact B2190503
  · exact B2190507
  · exact B2190511
  · exact B2190515
  · exact B2190519
  · exact B2190523
  · exact B2190527
  · exact B2190531
  · exact B2190535
  · exact B2190539
  · exact B2190543
  · exact B2190547
  · exact B2190551
  · exact B2190555
  · exact B2190559
  · exact B2190563
  · exact B2190567
  · exact B2190571
  · exact B2190575
  · exact B2190579
  · exact B2190583
  · exact B2190587
  · exact B2190591
  · exact B2190595
  · exact B2190599
  · exact B2190603
  · exact B2190607
  · exact B2190611
  · exact B2190615
  · exact B2190619
  · exact B2190623
  · exact B2190627
  · exact B2190631
  · exact B2190635
  · exact B2190639
  · exact B2190643
  · exact B2190647
  · exact B2190651
  · exact B2190655
  · exact B2190659
  · exact B2190663
  · exact B2190667
  · exact B2190671
  · exact B2190675
  · exact B2190679
  · exact B2190683
  · exact B2190687
  · exact B2190691
  · exact B2190695
  · exact B2190699
  · exact B2190703
  · exact B2190707
  · exact B2190711
  · exact B2190715
  · exact B2190719
  · exact B2190723
  · exact B2190727
  · exact B2190731
  · exact B2190735
  · exact B2190739
  · exact B2190743
  · exact B2190747
  · exact B2190751
  · exact B2190755
  · exact B2190759
  · exact B2190763
  · exact B2190767
  · exact B2190771
  · exact B2190775
  · exact B2190779
  · exact B2190783
  · exact B2190787
  · exact B2190791
  · exact B2190795
  · exact B2190799
  · exact B2190803
  · exact B2190807
  · exact B2190811
  · exact B2190815
  · exact B2190819
  · exact B2190823
  · exact B2190827
  · exact B2190831
  · exact B2190835
  · exact B2190839
  · exact B2190843
  · exact B2190847
  · exact B2190851
  · exact B2190855
  · exact B2190859
  · exact B2190863
  · exact B2190867
  · exact B2190871
  · exact B2190875
  · exact B2190879
  · exact B2190883
  · exact B2190887
  · exact B2190891
  · exact B2190895
  · exact B2190899
  · exact B2190903
  · exact B2190907
  · exact B2190911
  · exact B2190915
  · exact B2190919
  · exact B2190923
  · exact B2190927
  · exact B2190931
  · exact B2190935
  · exact B2190939
  · exact B2190943
  · exact B2190947
  · exact B2190951
  · exact B2190955
  · exact B2190959
  · exact B2190963
  · exact B2190967
  · exact B2190971
  · exact B2190975
  · exact B2190979
  · exact B2190983
  · exact B2190987
  · exact B2190991
  · exact B2190995
  · exact B2190999
  · exact B2191003
  · exact B2191007
  · exact B2191011
  · exact B2191015
  · exact B2191019
  · exact B2191023
  · exact B2191027
  · exact B2191031
  · exact B2191035
  · exact B2191039
  · exact B2191043
  · exact B2191047
  · exact B2191051
  · exact B2191055
  · exact B2191059
  · exact B2191063
  · exact B2191067
  · exact B2191071
  · exact B2191075
  · exact B2191079
  · exact B2191083
  · exact B2191087
  · exact B2191091
  · exact B2191095
  · exact B2191099
  · exact B2191103
  · exact B2191107
  · exact B2191111
  · exact B2191115
  · exact B2191119
  · exact B2191123
  · exact B2191127
  · exact B2191131
  · exact B2191135
  · exact B2191139
  · exact B2191143
  · exact B2191147
  · exact B2191151
  · exact B2191155
  · exact B2191159
  · exact B2191163
  · exact B2191167
  · exact B2191171
  · exact B2191175
  · exact B2191179
  · exact B2191183
  · exact B2191187
  · exact B2191191
  · exact B2191195
  · exact B2191199
  · exact B2191203
  · exact B2191207
  · exact B2191211
  · exact B2191215
  · exact B2191219
  · exact B2191223
  · exact B2191227
  · exact B2191231
  · exact B2191235
  · exact B2191239
  · exact B2191243
  · exact B2191247
  · exact B2191251
  · exact B2191255
  · exact B2191259
  · exact B2191263
  · exact B2191267
  · exact B2191271
  · exact B2191275
  · exact B2191279
  · exact B2191283
  · exact B2191287
  · exact B2191291
  · exact B2191295
  · exact B2191299
  · exact B2191303
  · exact B2191307
  · exact B2191311
  · exact B2191315
  · exact B2191319
  · exact B2191323
  · exact B2191327
  · exact B2191331
  · exact B2191335
  · exact B2191339
  · exact B2191343
  · exact B2191347
  · exact B2191351
  · exact B2191355
  · exact B2191359
  · exact B2191363
  · exact B2191367
  · exact B2191371
  · exact B2191375
  · exact B2191379
  · exact B2191383
  · exact B2191387
  · exact B2191391
  · exact B2191395
  · exact B2191399
  · exact B2191403
  · exact B2191407
  · exact B2191411
  · exact B2191415
  · exact B2191419
  · exact B2191423
  · exact B2191427
  · exact B2191431
  · exact B2191435
theorem solution (m : ℕ) (hlo : 2189435 ≤ m) (hhi : m ≤ 2191435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 547358 ≤ j := by omega
    have hj2 : j ≤ 547858 := by omega
    have hb : Blo 2189435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
