-- Prove2me | solution 1 for syracuse_descends_range_2141435_2143435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:17:17.189642+00:00
-- url     : https://prove2.me/submissions/6b9804ac-fb9e-4ff0-baa7-5acf5d4dd564

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

theorem B12362549 : Blo 2141435 12362549 := bbase (se 5 (by rfl) ⟨579494, by rfl⟩ : syracuseStep 12362549 = 1158989) (by norm_num)
theorem B32966797 : Blo 2141435 32966797 := bstep (se 3 (by rfl) ⟨6181274, by rfl⟩ : syracuseStep 32966797 = 12362549) B12362549
theorem B43955729 : Blo 2141435 43955729 := bstep (se 2 (by rfl) ⟨16483398, by rfl⟩ : syracuseStep 43955729 = 32966797) B32966797
theorem B29303819 : Blo 2141435 29303819 := bstep (se 1 (by rfl) ⟨21977864, by rfl⟩ : syracuseStep 29303819 = 43955729) B43955729
theorem B19535879 : Blo 2141435 19535879 := bstep (se 1 (by rfl) ⟨14651909, by rfl⟩ : syracuseStep 19535879 = 29303819) B29303819
theorem B13023919 : Blo 2141435 13023919 := bstep (se 1 (by rfl) ⟨9767939, by rfl⟩ : syracuseStep 13023919 = 19535879) B19535879
theorem B17365225 : Blo 2141435 17365225 := bstep (se 2 (by rfl) ⟨6511959, by rfl⟩ : syracuseStep 17365225 = 13023919) B13023919
theorem B23153633 : Blo 2141435 23153633 := bstep (se 2 (by rfl) ⟨8682612, by rfl⟩ : syracuseStep 23153633 = 17365225) B17365225
theorem B15435755 : Blo 2141435 15435755 := bstep (se 1 (by rfl) ⟨11576816, by rfl⟩ : syracuseStep 15435755 = 23153633) B23153633
theorem B10290503 : Blo 2141435 10290503 := bstep (se 1 (by rfl) ⟨7717877, by rfl⟩ : syracuseStep 10290503 = 15435755) B15435755
theorem B6860335 : Blo 2141435 6860335 := bstep (se 1 (by rfl) ⟨5145251, by rfl⟩ : syracuseStep 6860335 = 10290503) B10290503
theorem B9147113 : Blo 2141435 9147113 := bstep (se 2 (by rfl) ⟨3430167, by rfl⟩ : syracuseStep 9147113 = 6860335) B6860335
theorem B6098075 : Blo 2141435 6098075 := bstep (se 1 (by rfl) ⟨4573556, by rfl⟩ : syracuseStep 6098075 = 9147113) B9147113
theorem B4065383 : Blo 2141435 4065383 := bstep (se 1 (by rfl) ⟨3049037, by rfl⟩ : syracuseStep 4065383 = 6098075) B6098075
theorem B2710255 : Blo 2141435 2710255 := bstep (se 1 (by rfl) ⟨2032691, by rfl⟩ : syracuseStep 2710255 = 4065383) B4065383
theorem B3613673 : Blo 2141435 3613673 := bstep (se 2 (by rfl) ⟨1355127, by rfl⟩ : syracuseStep 3613673 = 2710255) B2710255
theorem B2409115 : Blo 2141435 2409115 := bstep (se 1 (by rfl) ⟨1806836, by rfl⟩ : syracuseStep 2409115 = 3613673) B3613673
theorem B3212153 : Blo 2141435 3212153 := bstep (se 2 (by rfl) ⟨1204557, by rfl⟩ : syracuseStep 3212153 = 2409115) B2409115
theorem B2141435 : Blo 2141435 2141435 := bstep (se 1 (by rfl) ⟨1606076, by rfl⟩ : syracuseStep 2141435 = 3212153) B3212153
theorem B2441989 : Blo 2141435 2441989 := bbase (se 4 (by rfl) ⟨228936, by rfl⟩ : syracuseStep 2441989 = 457873) (by norm_num)
theorem B3255985 : Blo 2141435 3255985 := bstep (se 2 (by rfl) ⟨1220994, by rfl⟩ : syracuseStep 3255985 = 2441989) B2441989
theorem B4341313 : Blo 2141435 4341313 := bstep (se 2 (by rfl) ⟨1627992, by rfl⟩ : syracuseStep 4341313 = 3255985) B3255985
theorem B5788417 : Blo 2141435 5788417 := bstep (se 2 (by rfl) ⟨2170656, by rfl⟩ : syracuseStep 5788417 = 4341313) B4341313
theorem B7717889 : Blo 2141435 7717889 := bstep (se 2 (by rfl) ⟨2894208, by rfl⟩ : syracuseStep 7717889 = 5788417) B5788417
theorem B20581037 : Blo 2141435 20581037 := bstep (se 3 (by rfl) ⟨3858944, by rfl⟩ : syracuseStep 20581037 = 7717889) B7717889
theorem B13720691 : Blo 2141435 13720691 := bstep (se 1 (by rfl) ⟨10290518, by rfl⟩ : syracuseStep 13720691 = 20581037) B20581037
theorem B36588509 : Blo 2141435 36588509 := bstep (se 3 (by rfl) ⟨6860345, by rfl⟩ : syracuseStep 36588509 = 13720691) B13720691
theorem B24392339 : Blo 2141435 24392339 := bstep (se 1 (by rfl) ⟨18294254, by rfl⟩ : syracuseStep 24392339 = 36588509) B36588509
theorem B16261559 : Blo 2141435 16261559 := bstep (se 1 (by rfl) ⟨12196169, by rfl⟩ : syracuseStep 16261559 = 24392339) B24392339
theorem B10841039 : Blo 2141435 10841039 := bstep (se 1 (by rfl) ⟨8130779, by rfl⟩ : syracuseStep 10841039 = 16261559) B16261559
theorem B7227359 : Blo 2141435 7227359 := bstep (se 1 (by rfl) ⟨5420519, by rfl⟩ : syracuseStep 7227359 = 10841039) B10841039
theorem B4818239 : Blo 2141435 4818239 := bstep (se 1 (by rfl) ⟨3613679, by rfl⟩ : syracuseStep 4818239 = 7227359) B7227359
theorem B3212159 : Blo 2141435 3212159 := bstep (se 1 (by rfl) ⟨2409119, by rfl⟩ : syracuseStep 3212159 = 4818239) B4818239
theorem B2141439 : Blo 2141435 2141439 := bstep (se 1 (by rfl) ⟨1606079, by rfl⟩ : syracuseStep 2141439 = 3212159) B3212159
theorem B3212165 : Blo 2141435 3212165 := bbase (se 4 (by rfl) ⟨301140, by rfl⟩ : syracuseStep 3212165 = 602281) (by norm_num)
theorem B2141443 : Blo 2141435 2141443 := bstep (se 1 (by rfl) ⟨1606082, by rfl⟩ : syracuseStep 2141443 = 3212165) B3212165
theorem B3613693 : Blo 2141435 3613693 := bbase (se 3 (by rfl) ⟨677567, by rfl⟩ : syracuseStep 3613693 = 1355135) (by norm_num)
theorem B4818257 : Blo 2141435 4818257 := bstep (se 2 (by rfl) ⟨1806846, by rfl⟩ : syracuseStep 4818257 = 3613693) B3613693
theorem B3212171 : Blo 2141435 3212171 := bstep (se 1 (by rfl) ⟨2409128, by rfl⟩ : syracuseStep 3212171 = 4818257) B4818257
theorem B2141447 : Blo 2141435 2141447 := bstep (se 1 (by rfl) ⟨1606085, by rfl⟩ : syracuseStep 2141447 = 3212171) B3212171
theorem B2409133 : Blo 2141435 2409133 := bbase (se 3 (by rfl) ⟨451712, by rfl⟩ : syracuseStep 2409133 = 903425) (by norm_num)
theorem B3212177 : Blo 2141435 3212177 := bstep (se 2 (by rfl) ⟨1204566, by rfl⟩ : syracuseStep 3212177 = 2409133) B2409133
theorem B2141451 : Blo 2141435 2141451 := bstep (se 1 (by rfl) ⟨1606088, by rfl⟩ : syracuseStep 2141451 = 3212177) B3212177
theorem B7227413 : Blo 2141435 7227413 := bbase (se 6 (by rfl) ⟨169392, by rfl⟩ : syracuseStep 7227413 = 338785) (by norm_num)
theorem B4818275 : Blo 2141435 4818275 := bstep (se 1 (by rfl) ⟨3613706, by rfl⟩ : syracuseStep 4818275 = 7227413) B7227413
theorem B3212183 : Blo 2141435 3212183 := bstep (se 1 (by rfl) ⟨2409137, by rfl⟩ : syracuseStep 3212183 = 4818275) B4818275
theorem B2141455 : Blo 2141435 2141455 := bstep (se 1 (by rfl) ⟨1606091, by rfl⟩ : syracuseStep 2141455 = 3212183) B3212183
theorem B3212189 : Blo 2141435 3212189 := bbase (se 3 (by rfl) ⟨602285, by rfl⟩ : syracuseStep 3212189 = 1204571) (by norm_num)
theorem B2141459 : Blo 2141435 2141459 := bstep (se 1 (by rfl) ⟨1606094, by rfl⟩ : syracuseStep 2141459 = 3212189) B3212189
theorem B4818293 : Blo 2141435 4818293 := bbase (se 5 (by rfl) ⟨225857, by rfl⟩ : syracuseStep 4818293 = 451715) (by norm_num)
theorem B3212195 : Blo 2141435 3212195 := bstep (se 1 (by rfl) ⟨2409146, by rfl⟩ : syracuseStep 3212195 = 4818293) B4818293
theorem B2141463 : Blo 2141435 2141463 := bstep (se 1 (by rfl) ⟨1606097, by rfl⟩ : syracuseStep 2141463 = 3212195) B3212195
theorem B4950677 : Blo 2141435 4950677 := bbase (se 6 (by rfl) ⟨116031, by rfl⟩ : syracuseStep 4950677 = 232063) (by norm_num)
theorem B13201805 : Blo 2141435 13201805 := bstep (se 3 (by rfl) ⟨2475338, by rfl⟩ : syracuseStep 13201805 = 4950677) B4950677
theorem B35204813 : Blo 2141435 35204813 := bstep (se 3 (by rfl) ⟨6600902, by rfl⟩ : syracuseStep 35204813 = 13201805) B13201805
theorem B23469875 : Blo 2141435 23469875 := bstep (se 1 (by rfl) ⟨17602406, by rfl⟩ : syracuseStep 23469875 = 35204813) B35204813
theorem B15646583 : Blo 2141435 15646583 := bstep (se 1 (by rfl) ⟨11734937, by rfl⟩ : syracuseStep 15646583 = 23469875) B23469875
theorem B10431055 : Blo 2141435 10431055 := bstep (se 1 (by rfl) ⟨7823291, by rfl⟩ : syracuseStep 10431055 = 15646583) B15646583
theorem B13908073 : Blo 2141435 13908073 := bstep (se 2 (by rfl) ⟨5215527, by rfl⟩ : syracuseStep 13908073 = 10431055) B10431055
theorem B18544097 : Blo 2141435 18544097 := bstep (se 2 (by rfl) ⟨6954036, by rfl⟩ : syracuseStep 18544097 = 13908073) B13908073
theorem B49450925 : Blo 2141435 49450925 := bstep (se 3 (by rfl) ⟨9272048, by rfl⟩ : syracuseStep 49450925 = 18544097) B18544097
theorem B32967283 : Blo 2141435 32967283 := bstep (se 1 (by rfl) ⟨24725462, by rfl⟩ : syracuseStep 32967283 = 49450925) B49450925
theorem B43956377 : Blo 2141435 43956377 := bstep (se 2 (by rfl) ⟨16483641, by rfl⟩ : syracuseStep 43956377 = 32967283) B32967283
theorem B29304251 : Blo 2141435 29304251 := bstep (se 1 (by rfl) ⟨21978188, by rfl⟩ : syracuseStep 29304251 = 43956377) B43956377
theorem B19536167 : Blo 2141435 19536167 := bstep (se 1 (by rfl) ⟨14652125, by rfl⟩ : syracuseStep 19536167 = 29304251) B29304251
theorem B52096445 : Blo 2141435 52096445 := bstep (se 3 (by rfl) ⟨9768083, by rfl⟩ : syracuseStep 52096445 = 19536167) B19536167
theorem B34730963 : Blo 2141435 34730963 := bstep (se 1 (by rfl) ⟨26048222, by rfl⟩ : syracuseStep 34730963 = 52096445) B52096445
theorem B23153975 : Blo 2141435 23153975 := bstep (se 1 (by rfl) ⟨17365481, by rfl⟩ : syracuseStep 23153975 = 34730963) B34730963
theorem B15435983 : Blo 2141435 15435983 := bstep (se 1 (by rfl) ⟨11576987, by rfl⟩ : syracuseStep 15435983 = 23153975) B23153975
theorem B10290655 : Blo 2141435 10290655 := bstep (se 1 (by rfl) ⟨7717991, by rfl⟩ : syracuseStep 10290655 = 15435983) B15435983
theorem B13720873 : Blo 2141435 13720873 := bstep (se 2 (by rfl) ⟨5145327, by rfl⟩ : syracuseStep 13720873 = 10290655) B10290655
theorem B18294497 : Blo 2141435 18294497 := bstep (se 2 (by rfl) ⟨6860436, by rfl⟩ : syracuseStep 18294497 = 13720873) B13720873
theorem B12196331 : Blo 2141435 12196331 := bstep (se 1 (by rfl) ⟨9147248, by rfl⟩ : syracuseStep 12196331 = 18294497) B18294497
theorem B8130887 : Blo 2141435 8130887 := bstep (se 1 (by rfl) ⟨6098165, by rfl⟩ : syracuseStep 8130887 = 12196331) B12196331
theorem B5420591 : Blo 2141435 5420591 := bstep (se 1 (by rfl) ⟨4065443, by rfl⟩ : syracuseStep 5420591 = 8130887) B8130887
theorem B3613727 : Blo 2141435 3613727 := bstep (se 1 (by rfl) ⟨2710295, by rfl⟩ : syracuseStep 3613727 = 5420591) B5420591
theorem B2409151 : Blo 2141435 2409151 := bstep (se 1 (by rfl) ⟨1806863, by rfl⟩ : syracuseStep 2409151 = 3613727) B3613727
theorem B3212201 : Blo 2141435 3212201 := bstep (se 2 (by rfl) ⟨1204575, by rfl⟩ : syracuseStep 3212201 = 2409151) B2409151
theorem B2141467 : Blo 2141435 2141467 := bstep (se 1 (by rfl) ⟨1606100, by rfl⟩ : syracuseStep 2141467 = 3212201) B3212201
theorem B8130901 : Blo 2141435 8130901 := bbase (se 10 (by rfl) ⟨11910, by rfl⟩ : syracuseStep 8130901 = 23821) (by norm_num)
theorem B10841201 : Blo 2141435 10841201 := bstep (se 2 (by rfl) ⟨4065450, by rfl⟩ : syracuseStep 10841201 = 8130901) B8130901
theorem B7227467 : Blo 2141435 7227467 := bstep (se 1 (by rfl) ⟨5420600, by rfl⟩ : syracuseStep 7227467 = 10841201) B10841201
theorem B4818311 : Blo 2141435 4818311 := bstep (se 1 (by rfl) ⟨3613733, by rfl⟩ : syracuseStep 4818311 = 7227467) B7227467
theorem B3212207 : Blo 2141435 3212207 := bstep (se 1 (by rfl) ⟨2409155, by rfl⟩ : syracuseStep 3212207 = 4818311) B4818311
theorem B2141471 : Blo 2141435 2141471 := bstep (se 1 (by rfl) ⟨1606103, by rfl⟩ : syracuseStep 2141471 = 3212207) B3212207
theorem B3212213 : Blo 2141435 3212213 := bbase (se 5 (by rfl) ⟨150572, by rfl⟩ : syracuseStep 3212213 = 301145) (by norm_num)
theorem B2141475 : Blo 2141435 2141475 := bstep (se 1 (by rfl) ⟨1606106, by rfl⟩ : syracuseStep 2141475 = 3212213) B3212213
theorem B5420621 : Blo 2141435 5420621 := bbase (se 3 (by rfl) ⟨1016366, by rfl⟩ : syracuseStep 5420621 = 2032733) (by norm_num)
theorem B3613747 : Blo 2141435 3613747 := bstep (se 1 (by rfl) ⟨2710310, by rfl⟩ : syracuseStep 3613747 = 5420621) B5420621
theorem B4818329 : Blo 2141435 4818329 := bstep (se 2 (by rfl) ⟨1806873, by rfl⟩ : syracuseStep 4818329 = 3613747) B3613747
theorem B3212219 : Blo 2141435 3212219 := bstep (se 1 (by rfl) ⟨2409164, by rfl⟩ : syracuseStep 3212219 = 4818329) B4818329
theorem B2141479 : Blo 2141435 2141479 := bstep (se 1 (by rfl) ⟨1606109, by rfl⟩ : syracuseStep 2141479 = 3212219) B3212219
theorem B2409169 : Blo 2141435 2409169 := bbase (se 2 (by rfl) ⟨903438, by rfl⟩ : syracuseStep 2409169 = 1806877) (by norm_num)
theorem B3212225 : Blo 2141435 3212225 := bstep (se 2 (by rfl) ⟨1204584, by rfl⟩ : syracuseStep 3212225 = 2409169) B2409169
theorem B2141483 : Blo 2141435 2141483 := bstep (se 1 (by rfl) ⟨1606112, by rfl⟩ : syracuseStep 2141483 = 3212225) B3212225
theorem B6860501 : Blo 2141435 6860501 := bbase (se 7 (by rfl) ⟨80396, by rfl⟩ : syracuseStep 6860501 = 160793) (by norm_num)
theorem B4573667 : Blo 2141435 4573667 := bstep (se 1 (by rfl) ⟨3430250, by rfl⟩ : syracuseStep 4573667 = 6860501) B6860501
theorem B3049111 : Blo 2141435 3049111 := bstep (se 1 (by rfl) ⟨2286833, by rfl⟩ : syracuseStep 3049111 = 4573667) B4573667
theorem B4065481 : Blo 2141435 4065481 := bstep (se 2 (by rfl) ⟨1524555, by rfl⟩ : syracuseStep 4065481 = 3049111) B3049111
theorem B5420641 : Blo 2141435 5420641 := bstep (se 2 (by rfl) ⟨2032740, by rfl⟩ : syracuseStep 5420641 = 4065481) B4065481
theorem B7227521 : Blo 2141435 7227521 := bstep (se 2 (by rfl) ⟨2710320, by rfl⟩ : syracuseStep 7227521 = 5420641) B5420641
theorem B4818347 : Blo 2141435 4818347 := bstep (se 1 (by rfl) ⟨3613760, by rfl⟩ : syracuseStep 4818347 = 7227521) B7227521
theorem B3212231 : Blo 2141435 3212231 := bstep (se 1 (by rfl) ⟨2409173, by rfl⟩ : syracuseStep 3212231 = 4818347) B4818347
theorem B2141487 : Blo 2141435 2141487 := bstep (se 1 (by rfl) ⟨1606115, by rfl⟩ : syracuseStep 2141487 = 3212231) B3212231
theorem B3212237 : Blo 2141435 3212237 := bbase (se 3 (by rfl) ⟨602294, by rfl⟩ : syracuseStep 3212237 = 1204589) (by norm_num)
theorem B2141491 : Blo 2141435 2141491 := bstep (se 1 (by rfl) ⟨1606118, by rfl⟩ : syracuseStep 2141491 = 3212237) B3212237
theorem B4818365 : Blo 2141435 4818365 := bbase (se 3 (by rfl) ⟨903443, by rfl⟩ : syracuseStep 4818365 = 1806887) (by norm_num)
theorem B3212243 : Blo 2141435 3212243 := bstep (se 1 (by rfl) ⟨2409182, by rfl⟩ : syracuseStep 3212243 = 4818365) B4818365
theorem B2141495 : Blo 2141435 2141495 := bstep (se 1 (by rfl) ⟨1606121, by rfl⟩ : syracuseStep 2141495 = 3212243) B3212243
theorem B3613781 : Blo 2141435 3613781 := bbase (se 8 (by rfl) ⟨21174, by rfl⟩ : syracuseStep 3613781 = 42349) (by norm_num)
theorem B2409187 : Blo 2141435 2409187 := bstep (se 1 (by rfl) ⟨1806890, by rfl⟩ : syracuseStep 2409187 = 3613781) B3613781
theorem B3212249 : Blo 2141435 3212249 := bstep (se 2 (by rfl) ⟨1204593, by rfl⟩ : syracuseStep 3212249 = 2409187) B2409187
theorem B2141499 : Blo 2141435 2141499 := bstep (se 1 (by rfl) ⟨1606124, by rfl⟩ : syracuseStep 2141499 = 3212249) B3212249
theorem B6512165 : Blo 2141435 6512165 := bbase (se 4 (by rfl) ⟨610515, by rfl⟩ : syracuseStep 6512165 = 1221031) (by norm_num)
theorem B4341443 : Blo 2141435 4341443 := bstep (se 1 (by rfl) ⟨3256082, by rfl⟩ : syracuseStep 4341443 = 6512165) B6512165
theorem B11577181 : Blo 2141435 11577181 := bstep (se 3 (by rfl) ⟨2170721, by rfl⟩ : syracuseStep 11577181 = 4341443) B4341443
theorem B15436241 : Blo 2141435 15436241 := bstep (se 2 (by rfl) ⟨5788590, by rfl⟩ : syracuseStep 15436241 = 11577181) B11577181
theorem B10290827 : Blo 2141435 10290827 := bstep (se 1 (by rfl) ⟨7718120, by rfl⟩ : syracuseStep 10290827 = 15436241) B15436241
theorem B6860551 : Blo 2141435 6860551 := bstep (se 1 (by rfl) ⟨5145413, by rfl⟩ : syracuseStep 6860551 = 10290827) B10290827
theorem B9147401 : Blo 2141435 9147401 := bstep (se 2 (by rfl) ⟨3430275, by rfl⟩ : syracuseStep 9147401 = 6860551) B6860551
theorem B6098267 : Blo 2141435 6098267 := bstep (se 1 (by rfl) ⟨4573700, by rfl⟩ : syracuseStep 6098267 = 9147401) B9147401
theorem B16262045 : Blo 2141435 16262045 := bstep (se 3 (by rfl) ⟨3049133, by rfl⟩ : syracuseStep 16262045 = 6098267) B6098267
theorem B10841363 : Blo 2141435 10841363 := bstep (se 1 (by rfl) ⟨8131022, by rfl⟩ : syracuseStep 10841363 = 16262045) B16262045
theorem B7227575 : Blo 2141435 7227575 := bstep (se 1 (by rfl) ⟨5420681, by rfl⟩ : syracuseStep 7227575 = 10841363) B10841363
theorem B4818383 : Blo 2141435 4818383 := bstep (se 1 (by rfl) ⟨3613787, by rfl⟩ : syracuseStep 4818383 = 7227575) B7227575
theorem B3212255 : Blo 2141435 3212255 := bstep (se 1 (by rfl) ⟨2409191, by rfl⟩ : syracuseStep 3212255 = 4818383) B4818383
theorem B2141503 : Blo 2141435 2141503 := bstep (se 1 (by rfl) ⟨1606127, by rfl⟩ : syracuseStep 2141503 = 3212255) B3212255
theorem B3212261 : Blo 2141435 3212261 := bbase (se 4 (by rfl) ⟨301149, by rfl⟩ : syracuseStep 3212261 = 602299) (by norm_num)
theorem B2141507 : Blo 2141435 2141507 := bstep (se 1 (by rfl) ⟨1606130, by rfl⟩ : syracuseStep 2141507 = 3212261) B3212261
theorem B2572717 : Blo 2141435 2572717 := bbase (se 3 (by rfl) ⟨482384, by rfl⟩ : syracuseStep 2572717 = 964769) (by norm_num)
theorem B3430289 : Blo 2141435 3430289 := bstep (se 2 (by rfl) ⟨1286358, by rfl⟩ : syracuseStep 3430289 = 2572717) B2572717
theorem B9147437 : Blo 2141435 9147437 := bstep (se 3 (by rfl) ⟨1715144, by rfl⟩ : syracuseStep 9147437 = 3430289) B3430289
theorem B6098291 : Blo 2141435 6098291 := bstep (se 1 (by rfl) ⟨4573718, by rfl⟩ : syracuseStep 6098291 = 9147437) B9147437
theorem B4065527 : Blo 2141435 4065527 := bstep (se 1 (by rfl) ⟨3049145, by rfl⟩ : syracuseStep 4065527 = 6098291) B6098291
theorem B2710351 : Blo 2141435 2710351 := bstep (se 1 (by rfl) ⟨2032763, by rfl⟩ : syracuseStep 2710351 = 4065527) B4065527
theorem B3613801 : Blo 2141435 3613801 := bstep (se 2 (by rfl) ⟨1355175, by rfl⟩ : syracuseStep 3613801 = 2710351) B2710351
theorem B4818401 : Blo 2141435 4818401 := bstep (se 2 (by rfl) ⟨1806900, by rfl⟩ : syracuseStep 4818401 = 3613801) B3613801
theorem B3212267 : Blo 2141435 3212267 := bstep (se 1 (by rfl) ⟨2409200, by rfl⟩ : syracuseStep 3212267 = 4818401) B4818401
theorem B2141511 : Blo 2141435 2141511 := bstep (se 1 (by rfl) ⟨1606133, by rfl⟩ : syracuseStep 2141511 = 3212267) B3212267
theorem B2409205 : Blo 2141435 2409205 := bbase (se 5 (by rfl) ⟨112931, by rfl⟩ : syracuseStep 2409205 = 225863) (by norm_num)
theorem B3212273 : Blo 2141435 3212273 := bstep (se 2 (by rfl) ⟨1204602, by rfl⟩ : syracuseStep 3212273 = 2409205) B2409205
theorem B2141515 : Blo 2141435 2141515 := bstep (se 1 (by rfl) ⟨1606136, by rfl⟩ : syracuseStep 2141515 = 3212273) B3212273
theorem B2710361 : Blo 2141435 2710361 := bbase (se 2 (by rfl) ⟨1016385, by rfl⟩ : syracuseStep 2710361 = 2032771) (by norm_num)
theorem B7227629 : Blo 2141435 7227629 := bstep (se 3 (by rfl) ⟨1355180, by rfl⟩ : syracuseStep 7227629 = 2710361) B2710361
theorem B4818419 : Blo 2141435 4818419 := bstep (se 1 (by rfl) ⟨3613814, by rfl⟩ : syracuseStep 4818419 = 7227629) B7227629
theorem B3212279 : Blo 2141435 3212279 := bstep (se 1 (by rfl) ⟨2409209, by rfl⟩ : syracuseStep 3212279 = 4818419) B4818419
theorem B2141519 : Blo 2141435 2141519 := bstep (se 1 (by rfl) ⟨1606139, by rfl⟩ : syracuseStep 2141519 = 3212279) B3212279
theorem B3212285 : Blo 2141435 3212285 := bbase (se 3 (by rfl) ⟨602303, by rfl⟩ : syracuseStep 3212285 = 1204607) (by norm_num)
theorem B2141523 : Blo 2141435 2141523 := bstep (se 1 (by rfl) ⟨1606142, by rfl⟩ : syracuseStep 2141523 = 3212285) B3212285
theorem B4818437 : Blo 2141435 4818437 := bbase (se 4 (by rfl) ⟨451728, by rfl⟩ : syracuseStep 4818437 = 903457) (by norm_num)
theorem B3212291 : Blo 2141435 3212291 := bstep (se 1 (by rfl) ⟨2409218, by rfl⟩ : syracuseStep 3212291 = 4818437) B4818437
theorem B2141527 : Blo 2141435 2141527 := bstep (se 1 (by rfl) ⟨1606145, by rfl⟩ : syracuseStep 2141527 = 3212291) B3212291
theorem B4065565 : Blo 2141435 4065565 := bbase (se 3 (by rfl) ⟨762293, by rfl⟩ : syracuseStep 4065565 = 1524587) (by norm_num)
theorem B5420753 : Blo 2141435 5420753 := bstep (se 2 (by rfl) ⟨2032782, by rfl⟩ : syracuseStep 5420753 = 4065565) B4065565
theorem B3613835 : Blo 2141435 3613835 := bstep (se 1 (by rfl) ⟨2710376, by rfl⟩ : syracuseStep 3613835 = 5420753) B5420753
theorem B2409223 : Blo 2141435 2409223 := bstep (se 1 (by rfl) ⟨1806917, by rfl⟩ : syracuseStep 2409223 = 3613835) B3613835
theorem B3212297 : Blo 2141435 3212297 := bstep (se 2 (by rfl) ⟨1204611, by rfl⟩ : syracuseStep 3212297 = 2409223) B2409223
theorem B2141531 : Blo 2141435 2141531 := bstep (se 1 (by rfl) ⟨1606148, by rfl⟩ : syracuseStep 2141531 = 3212297) B3212297
theorem B10841525 : Blo 2141435 10841525 := bbase (se 5 (by rfl) ⟨508196, by rfl⟩ : syracuseStep 10841525 = 1016393) (by norm_num)
theorem B7227683 : Blo 2141435 7227683 := bstep (se 1 (by rfl) ⟨5420762, by rfl⟩ : syracuseStep 7227683 = 10841525) B10841525
theorem B4818455 : Blo 2141435 4818455 := bstep (se 1 (by rfl) ⟨3613841, by rfl⟩ : syracuseStep 4818455 = 7227683) B7227683
theorem B3212303 : Blo 2141435 3212303 := bstep (se 1 (by rfl) ⟨2409227, by rfl⟩ : syracuseStep 3212303 = 4818455) B4818455
theorem B2141535 : Blo 2141435 2141535 := bstep (se 1 (by rfl) ⟨1606151, by rfl⟩ : syracuseStep 2141535 = 3212303) B3212303
theorem B3212309 : Blo 2141435 3212309 := bbase (se 6 (by rfl) ⟨75288, by rfl⟩ : syracuseStep 3212309 = 150577) (by norm_num)
theorem B2141539 : Blo 2141435 2141539 := bstep (se 1 (by rfl) ⟨1606154, by rfl⟩ : syracuseStep 2141539 = 3212309) B3212309
theorem B46309589 : Blo 2141435 46309589 := bbase (se 7 (by rfl) ⟨542690, by rfl⟩ : syracuseStep 46309589 = 1085381) (by norm_num)
theorem B30873059 : Blo 2141435 30873059 := bstep (se 1 (by rfl) ⟨23154794, by rfl⟩ : syracuseStep 30873059 = 46309589) B46309589
theorem B20582039 : Blo 2141435 20582039 := bstep (se 1 (by rfl) ⟨15436529, by rfl⟩ : syracuseStep 20582039 = 30873059) B30873059
theorem B13721359 : Blo 2141435 13721359 := bstep (se 1 (by rfl) ⟨10291019, by rfl⟩ : syracuseStep 13721359 = 20582039) B20582039
theorem B18295145 : Blo 2141435 18295145 := bstep (se 2 (by rfl) ⟨6860679, by rfl⟩ : syracuseStep 18295145 = 13721359) B13721359
theorem B12196763 : Blo 2141435 12196763 := bstep (se 1 (by rfl) ⟨9147572, by rfl⟩ : syracuseStep 12196763 = 18295145) B18295145
theorem B8131175 : Blo 2141435 8131175 := bstep (se 1 (by rfl) ⟨6098381, by rfl⟩ : syracuseStep 8131175 = 12196763) B12196763
theorem B5420783 : Blo 2141435 5420783 := bstep (se 1 (by rfl) ⟨4065587, by rfl⟩ : syracuseStep 5420783 = 8131175) B8131175
theorem B3613855 : Blo 2141435 3613855 := bstep (se 1 (by rfl) ⟨2710391, by rfl⟩ : syracuseStep 3613855 = 5420783) B5420783
theorem B4818473 : Blo 2141435 4818473 := bstep (se 2 (by rfl) ⟨1806927, by rfl⟩ : syracuseStep 4818473 = 3613855) B3613855
theorem B3212315 : Blo 2141435 3212315 := bstep (se 1 (by rfl) ⟨2409236, by rfl⟩ : syracuseStep 3212315 = 4818473) B4818473
theorem B2141543 : Blo 2141435 2141543 := bstep (se 1 (by rfl) ⟨1606157, by rfl⟩ : syracuseStep 2141543 = 3212315) B3212315
theorem B2409241 : Blo 2141435 2409241 := bbase (se 2 (by rfl) ⟨903465, by rfl⟩ : syracuseStep 2409241 = 1806931) (by norm_num)
theorem B3212321 : Blo 2141435 3212321 := bstep (se 2 (by rfl) ⟨1204620, by rfl⟩ : syracuseStep 3212321 = 2409241) B2409241
theorem B2141547 : Blo 2141435 2141547 := bstep (se 1 (by rfl) ⟨1606160, by rfl⟩ : syracuseStep 2141547 = 3212321) B3212321
theorem B8131205 : Blo 2141435 8131205 := bbase (se 4 (by rfl) ⟨762300, by rfl⟩ : syracuseStep 8131205 = 1524601) (by norm_num)
theorem B5420803 : Blo 2141435 5420803 := bstep (se 1 (by rfl) ⟨4065602, by rfl⟩ : syracuseStep 5420803 = 8131205) B8131205
theorem B7227737 : Blo 2141435 7227737 := bstep (se 2 (by rfl) ⟨2710401, by rfl⟩ : syracuseStep 7227737 = 5420803) B5420803
theorem B4818491 : Blo 2141435 4818491 := bstep (se 1 (by rfl) ⟨3613868, by rfl⟩ : syracuseStep 4818491 = 7227737) B7227737
theorem B3212327 : Blo 2141435 3212327 := bstep (se 1 (by rfl) ⟨2409245, by rfl⟩ : syracuseStep 3212327 = 4818491) B4818491
theorem B2141551 : Blo 2141435 2141551 := bstep (se 1 (by rfl) ⟨1606163, by rfl⟩ : syracuseStep 2141551 = 3212327) B3212327
theorem B3212333 : Blo 2141435 3212333 := bbase (se 3 (by rfl) ⟨602312, by rfl⟩ : syracuseStep 3212333 = 1204625) (by norm_num)
theorem B2141555 : Blo 2141435 2141555 := bstep (se 1 (by rfl) ⟨1606166, by rfl⟩ : syracuseStep 2141555 = 3212333) B3212333
theorem B4818509 : Blo 2141435 4818509 := bbase (se 3 (by rfl) ⟨903470, by rfl⟩ : syracuseStep 4818509 = 1806941) (by norm_num)
theorem B3212339 : Blo 2141435 3212339 := bstep (se 1 (by rfl) ⟨2409254, by rfl⟩ : syracuseStep 3212339 = 4818509) B4818509
theorem B2141559 : Blo 2141435 2141559 := bstep (se 1 (by rfl) ⟨1606169, by rfl⟩ : syracuseStep 2141559 = 3212339) B3212339
theorem B2710417 : Blo 2141435 2710417 := bbase (se 2 (by rfl) ⟨1016406, by rfl⟩ : syracuseStep 2710417 = 2032813) (by norm_num)
theorem B3613889 : Blo 2141435 3613889 := bstep (se 2 (by rfl) ⟨1355208, by rfl⟩ : syracuseStep 3613889 = 2710417) B2710417
theorem B2409259 : Blo 2141435 2409259 := bstep (se 1 (by rfl) ⟨1806944, by rfl⟩ : syracuseStep 2409259 = 3613889) B3613889
theorem B3212345 : Blo 2141435 3212345 := bstep (se 2 (by rfl) ⟨1204629, by rfl⟩ : syracuseStep 3212345 = 2409259) B2409259
theorem B2141563 : Blo 2141435 2141563 := bstep (se 1 (by rfl) ⟨1606172, by rfl⟩ : syracuseStep 2141563 = 3212345) B3212345
theorem B4573837 : Blo 2141435 4573837 := bbase (se 3 (by rfl) ⟨857594, by rfl⟩ : syracuseStep 4573837 = 1715189) (by norm_num)
theorem B24393797 : Blo 2141435 24393797 := bstep (se 4 (by rfl) ⟨2286918, by rfl⟩ : syracuseStep 24393797 = 4573837) B4573837
theorem B16262531 : Blo 2141435 16262531 := bstep (se 1 (by rfl) ⟨12196898, by rfl⟩ : syracuseStep 16262531 = 24393797) B24393797
theorem B10841687 : Blo 2141435 10841687 := bstep (se 1 (by rfl) ⟨8131265, by rfl⟩ : syracuseStep 10841687 = 16262531) B16262531
theorem B7227791 : Blo 2141435 7227791 := bstep (se 1 (by rfl) ⟨5420843, by rfl⟩ : syracuseStep 7227791 = 10841687) B10841687
theorem B4818527 : Blo 2141435 4818527 := bstep (se 1 (by rfl) ⟨3613895, by rfl⟩ : syracuseStep 4818527 = 7227791) B7227791
theorem B3212351 : Blo 2141435 3212351 := bstep (se 1 (by rfl) ⟨2409263, by rfl⟩ : syracuseStep 3212351 = 4818527) B4818527
theorem B2141567 : Blo 2141435 2141567 := bstep (se 1 (by rfl) ⟨1606175, by rfl⟩ : syracuseStep 2141567 = 3212351) B3212351
theorem B3212357 : Blo 2141435 3212357 := bbase (se 4 (by rfl) ⟨301158, by rfl⟩ : syracuseStep 3212357 = 602317) (by norm_num)
theorem B2141571 : Blo 2141435 2141571 := bstep (se 1 (by rfl) ⟨1606178, by rfl⟩ : syracuseStep 2141571 = 3212357) B3212357
theorem B3613909 : Blo 2141435 3613909 := bbase (se 7 (by rfl) ⟨42350, by rfl⟩ : syracuseStep 3613909 = 84701) (by norm_num)
theorem B4818545 : Blo 2141435 4818545 := bstep (se 2 (by rfl) ⟨1806954, by rfl⟩ : syracuseStep 4818545 = 3613909) B3613909
theorem B3212363 : Blo 2141435 3212363 := bstep (se 1 (by rfl) ⟨2409272, by rfl⟩ : syracuseStep 3212363 = 4818545) B4818545
theorem B2141575 : Blo 2141435 2141575 := bstep (se 1 (by rfl) ⟨1606181, by rfl⟩ : syracuseStep 2141575 = 3212363) B3212363
theorem B2409277 : Blo 2141435 2409277 := bbase (se 3 (by rfl) ⟨451739, by rfl⟩ : syracuseStep 2409277 = 903479) (by norm_num)
theorem B3212369 : Blo 2141435 3212369 := bstep (se 2 (by rfl) ⟨1204638, by rfl⟩ : syracuseStep 3212369 = 2409277) B2409277
theorem B2141579 : Blo 2141435 2141579 := bstep (se 1 (by rfl) ⟨1606184, by rfl⟩ : syracuseStep 2141579 = 3212369) B3212369
theorem B7227845 : Blo 2141435 7227845 := bbase (se 4 (by rfl) ⟨677610, by rfl⟩ : syracuseStep 7227845 = 1355221) (by norm_num)
theorem B4818563 : Blo 2141435 4818563 := bstep (se 1 (by rfl) ⟨3613922, by rfl⟩ : syracuseStep 4818563 = 7227845) B7227845
theorem B3212375 : Blo 2141435 3212375 := bstep (se 1 (by rfl) ⟨2409281, by rfl⟩ : syracuseStep 3212375 = 4818563) B4818563
theorem B2141583 : Blo 2141435 2141583 := bstep (se 1 (by rfl) ⟨1606187, by rfl⟩ : syracuseStep 2141583 = 3212375) B3212375
theorem B3212381 : Blo 2141435 3212381 := bbase (se 3 (by rfl) ⟨602321, by rfl⟩ : syracuseStep 3212381 = 1204643) (by norm_num)
theorem B2141587 : Blo 2141435 2141587 := bstep (se 1 (by rfl) ⟨1606190, by rfl⟩ : syracuseStep 2141587 = 3212381) B3212381
theorem B4818581 : Blo 2141435 4818581 := bbase (se 6 (by rfl) ⟨112935, by rfl⟩ : syracuseStep 4818581 = 225871) (by norm_num)
theorem B3212387 : Blo 2141435 3212387 := bstep (se 1 (by rfl) ⟨2409290, by rfl⟩ : syracuseStep 3212387 = 4818581) B4818581
theorem B2141591 : Blo 2141435 2141591 := bstep (se 1 (by rfl) ⟨1606193, by rfl⟩ : syracuseStep 2141591 = 3212387) B3212387
theorem B2286949 : Blo 2141435 2286949 := bbase (se 4 (by rfl) ⟨214401, by rfl⟩ : syracuseStep 2286949 = 428803) (by norm_num)
theorem B3049265 : Blo 2141435 3049265 := bstep (se 2 (by rfl) ⟨1143474, by rfl⟩ : syracuseStep 3049265 = 2286949) B2286949
theorem B8131373 : Blo 2141435 8131373 := bstep (se 3 (by rfl) ⟨1524632, by rfl⟩ : syracuseStep 8131373 = 3049265) B3049265
theorem B5420915 : Blo 2141435 5420915 := bstep (se 1 (by rfl) ⟨4065686, by rfl⟩ : syracuseStep 5420915 = 8131373) B8131373
theorem B3613943 : Blo 2141435 3613943 := bstep (se 1 (by rfl) ⟨2710457, by rfl⟩ : syracuseStep 3613943 = 5420915) B5420915
theorem B2409295 : Blo 2141435 2409295 := bstep (se 1 (by rfl) ⟨1806971, by rfl⟩ : syracuseStep 2409295 = 3613943) B3613943
theorem B3212393 : Blo 2141435 3212393 := bstep (se 2 (by rfl) ⟨1204647, by rfl⟩ : syracuseStep 3212393 = 2409295) B2409295
theorem B2141595 : Blo 2141435 2141595 := bstep (se 1 (by rfl) ⟨1606196, by rfl⟩ : syracuseStep 2141595 = 3212393) B3212393
theorem B13721717 : Blo 2141435 13721717 := bbase (se 5 (by rfl) ⟨643205, by rfl⟩ : syracuseStep 13721717 = 1286411) (by norm_num)
theorem B9147811 : Blo 2141435 9147811 := bstep (se 1 (by rfl) ⟨6860858, by rfl⟩ : syracuseStep 9147811 = 13721717) B13721717
theorem B12197081 : Blo 2141435 12197081 := bstep (se 2 (by rfl) ⟨4573905, by rfl⟩ : syracuseStep 12197081 = 9147811) B9147811
theorem B8131387 : Blo 2141435 8131387 := bstep (se 1 (by rfl) ⟨6098540, by rfl⟩ : syracuseStep 8131387 = 12197081) B12197081
theorem B10841849 : Blo 2141435 10841849 := bstep (se 2 (by rfl) ⟨4065693, by rfl⟩ : syracuseStep 10841849 = 8131387) B8131387
theorem B7227899 : Blo 2141435 7227899 := bstep (se 1 (by rfl) ⟨5420924, by rfl⟩ : syracuseStep 7227899 = 10841849) B10841849
theorem B4818599 : Blo 2141435 4818599 := bstep (se 1 (by rfl) ⟨3613949, by rfl⟩ : syracuseStep 4818599 = 7227899) B7227899
theorem B3212399 : Blo 2141435 3212399 := bstep (se 1 (by rfl) ⟨2409299, by rfl⟩ : syracuseStep 3212399 = 4818599) B4818599
theorem B2141599 : Blo 2141435 2141599 := bstep (se 1 (by rfl) ⟨1606199, by rfl⟩ : syracuseStep 2141599 = 3212399) B3212399
theorem B3212405 : Blo 2141435 3212405 := bbase (se 5 (by rfl) ⟨150581, by rfl⟩ : syracuseStep 3212405 = 301163) (by norm_num)
theorem B2141603 : Blo 2141435 2141603 := bstep (se 1 (by rfl) ⟨1606202, by rfl⟩ : syracuseStep 2141603 = 3212405) B3212405
theorem B4065709 : Blo 2141435 4065709 := bbase (se 3 (by rfl) ⟨762320, by rfl⟩ : syracuseStep 4065709 = 1524641) (by norm_num)
theorem B5420945 : Blo 2141435 5420945 := bstep (se 2 (by rfl) ⟨2032854, by rfl⟩ : syracuseStep 5420945 = 4065709) B4065709
theorem B3613963 : Blo 2141435 3613963 := bstep (se 1 (by rfl) ⟨2710472, by rfl⟩ : syracuseStep 3613963 = 5420945) B5420945
theorem B4818617 : Blo 2141435 4818617 := bstep (se 2 (by rfl) ⟨1806981, by rfl⟩ : syracuseStep 4818617 = 3613963) B3613963
theorem B3212411 : Blo 2141435 3212411 := bstep (se 1 (by rfl) ⟨2409308, by rfl⟩ : syracuseStep 3212411 = 4818617) B4818617
theorem B2141607 : Blo 2141435 2141607 := bstep (se 1 (by rfl) ⟨1606205, by rfl⟩ : syracuseStep 2141607 = 3212411) B3212411
theorem B2409313 : Blo 2141435 2409313 := bbase (se 2 (by rfl) ⟨903492, by rfl⟩ : syracuseStep 2409313 = 1806985) (by norm_num)
theorem B3212417 : Blo 2141435 3212417 := bstep (se 2 (by rfl) ⟨1204656, by rfl⟩ : syracuseStep 3212417 = 2409313) B2409313
theorem B2141611 : Blo 2141435 2141611 := bstep (se 1 (by rfl) ⟨1606208, by rfl⟩ : syracuseStep 2141611 = 3212417) B3212417
theorem B5420965 : Blo 2141435 5420965 := bbase (se 4 (by rfl) ⟨508215, by rfl⟩ : syracuseStep 5420965 = 1016431) (by norm_num)
theorem B7227953 : Blo 2141435 7227953 := bstep (se 2 (by rfl) ⟨2710482, by rfl⟩ : syracuseStep 7227953 = 5420965) B5420965
theorem B4818635 : Blo 2141435 4818635 := bstep (se 1 (by rfl) ⟨3613976, by rfl⟩ : syracuseStep 4818635 = 7227953) B7227953
theorem B3212423 : Blo 2141435 3212423 := bstep (se 1 (by rfl) ⟨2409317, by rfl⟩ : syracuseStep 3212423 = 4818635) B4818635
theorem B2141615 : Blo 2141435 2141615 := bstep (se 1 (by rfl) ⟨1606211, by rfl⟩ : syracuseStep 2141615 = 3212423) B3212423
theorem B3212429 : Blo 2141435 3212429 := bbase (se 3 (by rfl) ⟨602330, by rfl⟩ : syracuseStep 3212429 = 1204661) (by norm_num)
theorem B2141619 : Blo 2141435 2141619 := bstep (se 1 (by rfl) ⟨1606214, by rfl⟩ : syracuseStep 2141619 = 3212429) B3212429
theorem B4818653 : Blo 2141435 4818653 := bbase (se 3 (by rfl) ⟨903497, by rfl⟩ : syracuseStep 4818653 = 1806995) (by norm_num)
theorem B3212435 : Blo 2141435 3212435 := bstep (se 1 (by rfl) ⟨2409326, by rfl⟩ : syracuseStep 3212435 = 4818653) B4818653
theorem B2141623 : Blo 2141435 2141623 := bstep (se 1 (by rfl) ⟨1606217, by rfl⟩ : syracuseStep 2141623 = 3212435) B3212435
theorem B3613997 : Blo 2141435 3613997 := bbase (se 3 (by rfl) ⟨677624, by rfl⟩ : syracuseStep 3613997 = 1355249) (by norm_num)
theorem B2409331 : Blo 2141435 2409331 := bstep (se 1 (by rfl) ⟨1806998, by rfl⟩ : syracuseStep 2409331 = 3613997) B3613997
theorem B3212441 : Blo 2141435 3212441 := bstep (se 2 (by rfl) ⟨1204665, by rfl⟩ : syracuseStep 3212441 = 2409331) B2409331
theorem B2141627 : Blo 2141435 2141627 := bstep (se 1 (by rfl) ⟨1606220, by rfl⟩ : syracuseStep 2141627 = 3212441) B3212441
theorem B7718581 : Blo 2141435 7718581 := bbase (se 5 (by rfl) ⟨361808, by rfl⟩ : syracuseStep 7718581 = 723617) (by norm_num)
theorem B41165765 : Blo 2141435 41165765 := bstep (se 4 (by rfl) ⟨3859290, by rfl⟩ : syracuseStep 41165765 = 7718581) B7718581
theorem B27443843 : Blo 2141435 27443843 := bstep (se 1 (by rfl) ⟨20582882, by rfl⟩ : syracuseStep 27443843 = 41165765) B41165765
theorem B18295895 : Blo 2141435 18295895 := bstep (se 1 (by rfl) ⟨13721921, by rfl⟩ : syracuseStep 18295895 = 27443843) B27443843
theorem B12197263 : Blo 2141435 12197263 := bstep (se 1 (by rfl) ⟨9147947, by rfl⟩ : syracuseStep 12197263 = 18295895) B18295895
theorem B16263017 : Blo 2141435 16263017 := bstep (se 2 (by rfl) ⟨6098631, by rfl⟩ : syracuseStep 16263017 = 12197263) B12197263
theorem B10842011 : Blo 2141435 10842011 := bstep (se 1 (by rfl) ⟨8131508, by rfl⟩ : syracuseStep 10842011 = 16263017) B16263017
theorem B7228007 : Blo 2141435 7228007 := bstep (se 1 (by rfl) ⟨5421005, by rfl⟩ : syracuseStep 7228007 = 10842011) B10842011
theorem B4818671 : Blo 2141435 4818671 := bstep (se 1 (by rfl) ⟨3614003, by rfl⟩ : syracuseStep 4818671 = 7228007) B7228007
theorem B3212447 : Blo 2141435 3212447 := bstep (se 1 (by rfl) ⟨2409335, by rfl⟩ : syracuseStep 3212447 = 4818671) B4818671
theorem B2141631 : Blo 2141435 2141631 := bstep (se 1 (by rfl) ⟨1606223, by rfl⟩ : syracuseStep 2141631 = 3212447) B3212447
theorem B3212453 : Blo 2141435 3212453 := bbase (se 4 (by rfl) ⟨301167, by rfl⟩ : syracuseStep 3212453 = 602335) (by norm_num)
theorem B2141635 : Blo 2141435 2141635 := bstep (se 1 (by rfl) ⟨1606226, by rfl⟩ : syracuseStep 2141635 = 3212453) B3212453
theorem B2710513 : Blo 2141435 2710513 := bbase (se 2 (by rfl) ⟨1016442, by rfl⟩ : syracuseStep 2710513 = 2032885) (by norm_num)
theorem B3614017 : Blo 2141435 3614017 := bstep (se 2 (by rfl) ⟨1355256, by rfl⟩ : syracuseStep 3614017 = 2710513) B2710513
theorem B4818689 : Blo 2141435 4818689 := bstep (se 2 (by rfl) ⟨1807008, by rfl⟩ : syracuseStep 4818689 = 3614017) B3614017
theorem B3212459 : Blo 2141435 3212459 := bstep (se 1 (by rfl) ⟨2409344, by rfl⟩ : syracuseStep 3212459 = 4818689) B4818689
theorem B2141639 : Blo 2141435 2141639 := bstep (se 1 (by rfl) ⟨1606229, by rfl⟩ : syracuseStep 2141639 = 3212459) B3212459
theorem B2409349 : Blo 2141435 2409349 := bbase (se 4 (by rfl) ⟨225876, by rfl⟩ : syracuseStep 2409349 = 451753) (by norm_num)
theorem B3212465 : Blo 2141435 3212465 := bstep (se 2 (by rfl) ⟨1204674, by rfl⟩ : syracuseStep 3212465 = 2409349) B2409349
theorem B2141643 : Blo 2141435 2141643 := bstep (se 1 (by rfl) ⟨1606232, by rfl⟩ : syracuseStep 2141643 = 3212465) B3212465
theorem B2607985 : Blo 2141435 2607985 := bbase (se 2 (by rfl) ⟨977994, by rfl⟩ : syracuseStep 2607985 = 1955989) (by norm_num)
theorem B3477313 : Blo 2141435 3477313 := bstep (se 2 (by rfl) ⟨1303992, by rfl⟩ : syracuseStep 3477313 = 2607985) B2607985
theorem B18545669 : Blo 2141435 18545669 := bstep (se 4 (by rfl) ⟨1738656, by rfl⟩ : syracuseStep 18545669 = 3477313) B3477313
theorem B12363779 : Blo 2141435 12363779 := bstep (se 1 (by rfl) ⟨9272834, by rfl⟩ : syracuseStep 12363779 = 18545669) B18545669
theorem B8242519 : Blo 2141435 8242519 := bstep (se 1 (by rfl) ⟨6181889, by rfl⟩ : syracuseStep 8242519 = 12363779) B12363779
theorem B10990025 : Blo 2141435 10990025 := bstep (se 2 (by rfl) ⟨4121259, by rfl⟩ : syracuseStep 10990025 = 8242519) B8242519
theorem B7326683 : Blo 2141435 7326683 := bstep (se 1 (by rfl) ⟨5495012, by rfl⟩ : syracuseStep 7326683 = 10990025) B10990025
theorem B4884455 : Blo 2141435 4884455 := bstep (se 1 (by rfl) ⟨3663341, by rfl⟩ : syracuseStep 4884455 = 7326683) B7326683
theorem B3256303 : Blo 2141435 3256303 := bstep (se 1 (by rfl) ⟨2442227, by rfl⟩ : syracuseStep 3256303 = 4884455) B4884455
theorem B4341737 : Blo 2141435 4341737 := bstep (se 2 (by rfl) ⟨1628151, by rfl⟩ : syracuseStep 4341737 = 3256303) B3256303
theorem B2894491 : Blo 2141435 2894491 := bstep (se 1 (by rfl) ⟨2170868, by rfl⟩ : syracuseStep 2894491 = 4341737) B4341737
theorem B3859321 : Blo 2141435 3859321 := bstep (se 2 (by rfl) ⟨1447245, by rfl⟩ : syracuseStep 3859321 = 2894491) B2894491
theorem B5145761 : Blo 2141435 5145761 := bstep (se 2 (by rfl) ⟨1929660, by rfl⟩ : syracuseStep 5145761 = 3859321) B3859321
theorem B3430507 : Blo 2141435 3430507 := bstep (se 1 (by rfl) ⟨2572880, by rfl⟩ : syracuseStep 3430507 = 5145761) B5145761
theorem B4574009 : Blo 2141435 4574009 := bstep (se 2 (by rfl) ⟨1715253, by rfl⟩ : syracuseStep 4574009 = 3430507) B3430507
theorem B3049339 : Blo 2141435 3049339 := bstep (se 1 (by rfl) ⟨2287004, by rfl⟩ : syracuseStep 3049339 = 4574009) B4574009
theorem B4065785 : Blo 2141435 4065785 := bstep (se 2 (by rfl) ⟨1524669, by rfl⟩ : syracuseStep 4065785 = 3049339) B3049339
theorem B2710523 : Blo 2141435 2710523 := bstep (se 1 (by rfl) ⟨2032892, by rfl⟩ : syracuseStep 2710523 = 4065785) B4065785
theorem B7228061 : Blo 2141435 7228061 := bstep (se 3 (by rfl) ⟨1355261, by rfl⟩ : syracuseStep 7228061 = 2710523) B2710523
theorem B4818707 : Blo 2141435 4818707 := bstep (se 1 (by rfl) ⟨3614030, by rfl⟩ : syracuseStep 4818707 = 7228061) B7228061
theorem B3212471 : Blo 2141435 3212471 := bstep (se 1 (by rfl) ⟨2409353, by rfl⟩ : syracuseStep 3212471 = 4818707) B4818707
theorem B2141647 : Blo 2141435 2141647 := bstep (se 1 (by rfl) ⟨1606235, by rfl⟩ : syracuseStep 2141647 = 3212471) B3212471
theorem B3212477 : Blo 2141435 3212477 := bbase (se 3 (by rfl) ⟨602339, by rfl⟩ : syracuseStep 3212477 = 1204679) (by norm_num)
theorem B2141651 : Blo 2141435 2141651 := bstep (se 1 (by rfl) ⟨1606238, by rfl⟩ : syracuseStep 2141651 = 3212477) B3212477
theorem B4818725 : Blo 2141435 4818725 := bbase (se 4 (by rfl) ⟨451755, by rfl⟩ : syracuseStep 4818725 = 903511) (by norm_num)
theorem B3212483 : Blo 2141435 3212483 := bstep (se 1 (by rfl) ⟨2409362, by rfl⟩ : syracuseStep 3212483 = 4818725) B4818725
theorem B2141655 : Blo 2141435 2141655 := bstep (se 1 (by rfl) ⟨1606241, by rfl⟩ : syracuseStep 2141655 = 3212483) B3212483
theorem B5421077 : Blo 2141435 5421077 := bbase (se 6 (by rfl) ⟨127056, by rfl⟩ : syracuseStep 5421077 = 254113) (by norm_num)
theorem B3614051 : Blo 2141435 3614051 := bstep (se 1 (by rfl) ⟨2710538, by rfl⟩ : syracuseStep 3614051 = 5421077) B5421077
theorem B2409367 : Blo 2141435 2409367 := bstep (se 1 (by rfl) ⟨1807025, by rfl⟩ : syracuseStep 2409367 = 3614051) B3614051
theorem B3212489 : Blo 2141435 3212489 := bstep (se 2 (by rfl) ⟨1204683, by rfl⟩ : syracuseStep 3212489 = 2409367) B2409367
theorem B2141659 : Blo 2141435 2141659 := bstep (se 1 (by rfl) ⟨1606244, by rfl⟩ : syracuseStep 2141659 = 3212489) B3212489
theorem B9148085 : Blo 2141435 9148085 := bbase (se 5 (by rfl) ⟨428816, by rfl⟩ : syracuseStep 9148085 = 857633) (by norm_num)
theorem B6098723 : Blo 2141435 6098723 := bstep (se 1 (by rfl) ⟨4574042, by rfl⟩ : syracuseStep 6098723 = 9148085) B9148085
theorem B4065815 : Blo 2141435 4065815 := bstep (se 1 (by rfl) ⟨3049361, by rfl⟩ : syracuseStep 4065815 = 6098723) B6098723
theorem B10842173 : Blo 2141435 10842173 := bstep (se 3 (by rfl) ⟨2032907, by rfl⟩ : syracuseStep 10842173 = 4065815) B4065815
theorem B7228115 : Blo 2141435 7228115 := bstep (se 1 (by rfl) ⟨5421086, by rfl⟩ : syracuseStep 7228115 = 10842173) B10842173
theorem B4818743 : Blo 2141435 4818743 := bstep (se 1 (by rfl) ⟨3614057, by rfl⟩ : syracuseStep 4818743 = 7228115) B7228115
theorem B3212495 : Blo 2141435 3212495 := bstep (se 1 (by rfl) ⟨2409371, by rfl⟩ : syracuseStep 3212495 = 4818743) B4818743
theorem B2141663 : Blo 2141435 2141663 := bstep (se 1 (by rfl) ⟨1606247, by rfl⟩ : syracuseStep 2141663 = 3212495) B3212495
theorem B3212501 : Blo 2141435 3212501 := bbase (se 7 (by rfl) ⟨37646, by rfl⟩ : syracuseStep 3212501 = 75293) (by norm_num)
theorem B2141667 : Blo 2141435 2141667 := bstep (se 1 (by rfl) ⟨1606250, by rfl⟩ : syracuseStep 2141667 = 3212501) B3212501
theorem B3049373 : Blo 2141435 3049373 := bbase (se 3 (by rfl) ⟨571757, by rfl⟩ : syracuseStep 3049373 = 1143515) (by norm_num)
theorem B8131661 : Blo 2141435 8131661 := bstep (se 3 (by rfl) ⟨1524686, by rfl⟩ : syracuseStep 8131661 = 3049373) B3049373
theorem B5421107 : Blo 2141435 5421107 := bstep (se 1 (by rfl) ⟨4065830, by rfl⟩ : syracuseStep 5421107 = 8131661) B8131661
theorem B3614071 : Blo 2141435 3614071 := bstep (se 1 (by rfl) ⟨2710553, by rfl⟩ : syracuseStep 3614071 = 5421107) B5421107
theorem B4818761 : Blo 2141435 4818761 := bstep (se 2 (by rfl) ⟨1807035, by rfl⟩ : syracuseStep 4818761 = 3614071) B3614071
theorem B3212507 : Blo 2141435 3212507 := bstep (se 1 (by rfl) ⟨2409380, by rfl⟩ : syracuseStep 3212507 = 4818761) B4818761
theorem B2141671 : Blo 2141435 2141671 := bstep (se 1 (by rfl) ⟨1606253, by rfl⟩ : syracuseStep 2141671 = 3212507) B3212507
theorem B2409385 : Blo 2141435 2409385 := bbase (se 2 (by rfl) ⟨903519, by rfl⟩ : syracuseStep 2409385 = 1807039) (by norm_num)
theorem B3212513 : Blo 2141435 3212513 := bstep (se 2 (by rfl) ⟨1204692, by rfl⟩ : syracuseStep 3212513 = 2409385) B2409385
theorem B2141675 : Blo 2141435 2141675 := bstep (se 1 (by rfl) ⟨1606256, by rfl⟩ : syracuseStep 2141675 = 3212513) B3212513
theorem B11578133 : Blo 2141435 11578133 := bbase (se 6 (by rfl) ⟨271362, by rfl⟩ : syracuseStep 11578133 = 542725) (by norm_num)
theorem B7718755 : Blo 2141435 7718755 := bstep (se 1 (by rfl) ⟨5789066, by rfl⟩ : syracuseStep 7718755 = 11578133) B11578133
theorem B10291673 : Blo 2141435 10291673 := bstep (se 2 (by rfl) ⟨3859377, by rfl⟩ : syracuseStep 10291673 = 7718755) B7718755
theorem B6861115 : Blo 2141435 6861115 := bstep (se 1 (by rfl) ⟨5145836, by rfl⟩ : syracuseStep 6861115 = 10291673) B10291673
theorem B9148153 : Blo 2141435 9148153 := bstep (se 2 (by rfl) ⟨3430557, by rfl⟩ : syracuseStep 9148153 = 6861115) B6861115
theorem B12197537 : Blo 2141435 12197537 := bstep (se 2 (by rfl) ⟨4574076, by rfl⟩ : syracuseStep 12197537 = 9148153) B9148153
theorem B8131691 : Blo 2141435 8131691 := bstep (se 1 (by rfl) ⟨6098768, by rfl⟩ : syracuseStep 8131691 = 12197537) B12197537
theorem B5421127 : Blo 2141435 5421127 := bstep (se 1 (by rfl) ⟨4065845, by rfl⟩ : syracuseStep 5421127 = 8131691) B8131691
theorem B7228169 : Blo 2141435 7228169 := bstep (se 2 (by rfl) ⟨2710563, by rfl⟩ : syracuseStep 7228169 = 5421127) B5421127
theorem B4818779 : Blo 2141435 4818779 := bstep (se 1 (by rfl) ⟨3614084, by rfl⟩ : syracuseStep 4818779 = 7228169) B7228169
theorem B3212519 : Blo 2141435 3212519 := bstep (se 1 (by rfl) ⟨2409389, by rfl⟩ : syracuseStep 3212519 = 4818779) B4818779
theorem B2141679 : Blo 2141435 2141679 := bstep (se 1 (by rfl) ⟨1606259, by rfl⟩ : syracuseStep 2141679 = 3212519) B3212519
theorem B3212525 : Blo 2141435 3212525 := bbase (se 3 (by rfl) ⟨602348, by rfl⟩ : syracuseStep 3212525 = 1204697) (by norm_num)
theorem B2141683 : Blo 2141435 2141683 := bstep (se 1 (by rfl) ⟨1606262, by rfl⟩ : syracuseStep 2141683 = 3212525) B3212525
theorem B4818797 : Blo 2141435 4818797 := bbase (se 3 (by rfl) ⟨903524, by rfl⟩ : syracuseStep 4818797 = 1807049) (by norm_num)
theorem B3212531 : Blo 2141435 3212531 := bstep (se 1 (by rfl) ⟨2409398, by rfl⟩ : syracuseStep 3212531 = 4818797) B4818797
theorem B2141687 : Blo 2141435 2141687 := bstep (se 1 (by rfl) ⟨1606265, by rfl⟩ : syracuseStep 2141687 = 3212531) B3212531
theorem B4065869 : Blo 2141435 4065869 := bbase (se 3 (by rfl) ⟨762350, by rfl⟩ : syracuseStep 4065869 = 1524701) (by norm_num)
theorem B2710579 : Blo 2141435 2710579 := bstep (se 1 (by rfl) ⟨2032934, by rfl⟩ : syracuseStep 2710579 = 4065869) B4065869
theorem B3614105 : Blo 2141435 3614105 := bstep (se 2 (by rfl) ⟨1355289, by rfl⟩ : syracuseStep 3614105 = 2710579) B2710579
theorem B2409403 : Blo 2141435 2409403 := bstep (se 1 (by rfl) ⟨1807052, by rfl⟩ : syracuseStep 2409403 = 3614105) B3614105
theorem B3212537 : Blo 2141435 3212537 := bstep (se 2 (by rfl) ⟨1204701, by rfl⟩ : syracuseStep 3212537 = 2409403) B2409403
theorem B2141691 : Blo 2141435 2141691 := bstep (se 1 (by rfl) ⟨1606268, by rfl⟩ : syracuseStep 2141691 = 3212537) B3212537
theorem B10432165 : Blo 2141435 10432165 := bbase (se 4 (by rfl) ⟨978015, by rfl⟩ : syracuseStep 10432165 = 1956031) (by norm_num)
theorem B13909553 : Blo 2141435 13909553 := bstep (se 2 (by rfl) ⟨5216082, by rfl⟩ : syracuseStep 13909553 = 10432165) B10432165
theorem B9273035 : Blo 2141435 9273035 := bstep (se 1 (by rfl) ⟨6954776, by rfl⟩ : syracuseStep 9273035 = 13909553) B13909553
theorem B6182023 : Blo 2141435 6182023 := bstep (se 1 (by rfl) ⟨4636517, by rfl⟩ : syracuseStep 6182023 = 9273035) B9273035
theorem B8242697 : Blo 2141435 8242697 := bstep (se 2 (by rfl) ⟨3091011, by rfl⟩ : syracuseStep 8242697 = 6182023) B6182023
theorem B5495131 : Blo 2141435 5495131 := bstep (se 1 (by rfl) ⟨4121348, by rfl⟩ : syracuseStep 5495131 = 8242697) B8242697
theorem B29307365 : Blo 2141435 29307365 := bstep (se 4 (by rfl) ⟨2747565, by rfl⟩ : syracuseStep 29307365 = 5495131) B5495131
theorem B19538243 : Blo 2141435 19538243 := bstep (se 1 (by rfl) ⟨14653682, by rfl⟩ : syracuseStep 19538243 = 29307365) B29307365
theorem B13025495 : Blo 2141435 13025495 := bstep (se 1 (by rfl) ⟨9769121, by rfl⟩ : syracuseStep 13025495 = 19538243) B19538243
theorem B34734653 : Blo 2141435 34734653 := bstep (se 3 (by rfl) ⟨6512747, by rfl⟩ : syracuseStep 34734653 = 13025495) B13025495
theorem B23156435 : Blo 2141435 23156435 := bstep (se 1 (by rfl) ⟨17367326, by rfl⟩ : syracuseStep 23156435 = 34734653) B34734653
theorem B15437623 : Blo 2141435 15437623 := bstep (se 1 (by rfl) ⟨11578217, by rfl⟩ : syracuseStep 15437623 = 23156435) B23156435
theorem B20583497 : Blo 2141435 20583497 := bstep (se 2 (by rfl) ⟨7718811, by rfl⟩ : syracuseStep 20583497 = 15437623) B15437623
theorem B54889325 : Blo 2141435 54889325 := bstep (se 3 (by rfl) ⟨10291748, by rfl⟩ : syracuseStep 54889325 = 20583497) B20583497
theorem B36592883 : Blo 2141435 36592883 := bstep (se 1 (by rfl) ⟨27444662, by rfl⟩ : syracuseStep 36592883 = 54889325) B54889325
theorem B24395255 : Blo 2141435 24395255 := bstep (se 1 (by rfl) ⟨18296441, by rfl⟩ : syracuseStep 24395255 = 36592883) B36592883
theorem B16263503 : Blo 2141435 16263503 := bstep (se 1 (by rfl) ⟨12197627, by rfl⟩ : syracuseStep 16263503 = 24395255) B24395255
theorem B10842335 : Blo 2141435 10842335 := bstep (se 1 (by rfl) ⟨8131751, by rfl⟩ : syracuseStep 10842335 = 16263503) B16263503
theorem B7228223 : Blo 2141435 7228223 := bstep (se 1 (by rfl) ⟨5421167, by rfl⟩ : syracuseStep 7228223 = 10842335) B10842335
theorem B4818815 : Blo 2141435 4818815 := bstep (se 1 (by rfl) ⟨3614111, by rfl⟩ : syracuseStep 4818815 = 7228223) B7228223
theorem B3212543 : Blo 2141435 3212543 := bstep (se 1 (by rfl) ⟨2409407, by rfl⟩ : syracuseStep 3212543 = 4818815) B4818815
theorem B2141695 : Blo 2141435 2141695 := bstep (se 1 (by rfl) ⟨1606271, by rfl⟩ : syracuseStep 2141695 = 3212543) B3212543
theorem B3212549 : Blo 2141435 3212549 := bbase (se 4 (by rfl) ⟨301176, by rfl⟩ : syracuseStep 3212549 = 602353) (by norm_num)
theorem B2141699 : Blo 2141435 2141699 := bstep (se 1 (by rfl) ⟨1606274, by rfl⟩ : syracuseStep 2141699 = 3212549) B3212549
theorem B3614125 : Blo 2141435 3614125 := bbase (se 3 (by rfl) ⟨677648, by rfl⟩ : syracuseStep 3614125 = 1355297) (by norm_num)
theorem B4818833 : Blo 2141435 4818833 := bstep (se 2 (by rfl) ⟨1807062, by rfl⟩ : syracuseStep 4818833 = 3614125) B3614125
theorem B3212555 : Blo 2141435 3212555 := bstep (se 1 (by rfl) ⟨2409416, by rfl⟩ : syracuseStep 3212555 = 4818833) B4818833
theorem B2141703 : Blo 2141435 2141703 := bstep (se 1 (by rfl) ⟨1606277, by rfl⟩ : syracuseStep 2141703 = 3212555) B3212555
theorem B2409421 : Blo 2141435 2409421 := bbase (se 3 (by rfl) ⟨451766, by rfl⟩ : syracuseStep 2409421 = 903533) (by norm_num)
theorem B3212561 : Blo 2141435 3212561 := bstep (se 2 (by rfl) ⟨1204710, by rfl⟩ : syracuseStep 3212561 = 2409421) B2409421
theorem B2141707 : Blo 2141435 2141707 := bstep (se 1 (by rfl) ⟨1606280, by rfl⟩ : syracuseStep 2141707 = 3212561) B3212561
theorem B7228277 : Blo 2141435 7228277 := bbase (se 5 (by rfl) ⟨338825, by rfl⟩ : syracuseStep 7228277 = 677651) (by norm_num)
theorem B4818851 : Blo 2141435 4818851 := bstep (se 1 (by rfl) ⟨3614138, by rfl⟩ : syracuseStep 4818851 = 7228277) B7228277
theorem B3212567 : Blo 2141435 3212567 := bstep (se 1 (by rfl) ⟨2409425, by rfl⟩ : syracuseStep 3212567 = 4818851) B4818851
theorem B2141711 : Blo 2141435 2141711 := bstep (se 1 (by rfl) ⟨1606283, by rfl⟩ : syracuseStep 2141711 = 3212567) B3212567
theorem B3212573 : Blo 2141435 3212573 := bbase (se 3 (by rfl) ⟨602357, by rfl⟩ : syracuseStep 3212573 = 1204715) (by norm_num)
theorem B2141715 : Blo 2141435 2141715 := bstep (se 1 (by rfl) ⟨1606286, by rfl⟩ : syracuseStep 2141715 = 3212573) B3212573
theorem B4818869 : Blo 2141435 4818869 := bbase (se 5 (by rfl) ⟨225884, by rfl⟩ : syracuseStep 4818869 = 451769) (by norm_num)
theorem B3212579 : Blo 2141435 3212579 := bstep (se 1 (by rfl) ⟨2409434, by rfl⟩ : syracuseStep 3212579 = 4818869) B4818869
theorem B2141719 : Blo 2141435 2141719 := bstep (se 1 (by rfl) ⟨1606289, by rfl⟩ : syracuseStep 2141719 = 3212579) B3212579
theorem B2170945 : Blo 2141435 2170945 := bbase (se 2 (by rfl) ⟨814104, by rfl⟩ : syracuseStep 2170945 = 1628209) (by norm_num)
theorem B11578373 : Blo 2141435 11578373 := bstep (se 4 (by rfl) ⟨1085472, by rfl⟩ : syracuseStep 11578373 = 2170945) B2170945
theorem B7718915 : Blo 2141435 7718915 := bstep (se 1 (by rfl) ⟨5789186, by rfl⟩ : syracuseStep 7718915 = 11578373) B11578373
theorem B5145943 : Blo 2141435 5145943 := bstep (se 1 (by rfl) ⟨3859457, by rfl⟩ : syracuseStep 5145943 = 7718915) B7718915
theorem B6861257 : Blo 2141435 6861257 := bstep (se 2 (by rfl) ⟨2572971, by rfl⟩ : syracuseStep 6861257 = 5145943) B5145943
theorem B4574171 : Blo 2141435 4574171 := bstep (se 1 (by rfl) ⟨3430628, by rfl⟩ : syracuseStep 4574171 = 6861257) B6861257
theorem B12197789 : Blo 2141435 12197789 := bstep (se 3 (by rfl) ⟨2287085, by rfl⟩ : syracuseStep 12197789 = 4574171) B4574171
theorem B8131859 : Blo 2141435 8131859 := bstep (se 1 (by rfl) ⟨6098894, by rfl⟩ : syracuseStep 8131859 = 12197789) B12197789
theorem B5421239 : Blo 2141435 5421239 := bstep (se 1 (by rfl) ⟨4065929, by rfl⟩ : syracuseStep 5421239 = 8131859) B8131859
theorem B3614159 : Blo 2141435 3614159 := bstep (se 1 (by rfl) ⟨2710619, by rfl⟩ : syracuseStep 3614159 = 5421239) B5421239
theorem B2409439 : Blo 2141435 2409439 := bstep (se 1 (by rfl) ⟨1807079, by rfl⟩ : syracuseStep 2409439 = 3614159) B3614159
theorem B3212585 : Blo 2141435 3212585 := bstep (se 2 (by rfl) ⟨1204719, by rfl⟩ : syracuseStep 3212585 = 2409439) B2409439
theorem B2141723 : Blo 2141435 2141723 := bstep (se 1 (by rfl) ⟨1606292, by rfl⟩ : syracuseStep 2141723 = 3212585) B3212585
theorem B6861269 : Blo 2141435 6861269 := bbase (se 7 (by rfl) ⟨80405, by rfl⟩ : syracuseStep 6861269 = 160811) (by norm_num)
theorem B4574179 : Blo 2141435 4574179 := bstep (se 1 (by rfl) ⟨3430634, by rfl⟩ : syracuseStep 4574179 = 6861269) B6861269
theorem B6098905 : Blo 2141435 6098905 := bstep (se 2 (by rfl) ⟨2287089, by rfl⟩ : syracuseStep 6098905 = 4574179) B4574179
theorem B8131873 : Blo 2141435 8131873 := bstep (se 2 (by rfl) ⟨3049452, by rfl⟩ : syracuseStep 8131873 = 6098905) B6098905
theorem B10842497 : Blo 2141435 10842497 := bstep (se 2 (by rfl) ⟨4065936, by rfl⟩ : syracuseStep 10842497 = 8131873) B8131873
theorem B7228331 : Blo 2141435 7228331 := bstep (se 1 (by rfl) ⟨5421248, by rfl⟩ : syracuseStep 7228331 = 10842497) B10842497
theorem B4818887 : Blo 2141435 4818887 := bstep (se 1 (by rfl) ⟨3614165, by rfl⟩ : syracuseStep 4818887 = 7228331) B7228331
theorem B3212591 : Blo 2141435 3212591 := bstep (se 1 (by rfl) ⟨2409443, by rfl⟩ : syracuseStep 3212591 = 4818887) B4818887
theorem B2141727 : Blo 2141435 2141727 := bstep (se 1 (by rfl) ⟨1606295, by rfl⟩ : syracuseStep 2141727 = 3212591) B3212591
theorem B3212597 : Blo 2141435 3212597 := bbase (se 5 (by rfl) ⟨150590, by rfl⟩ : syracuseStep 3212597 = 301181) (by norm_num)
theorem B2141731 : Blo 2141435 2141731 := bstep (se 1 (by rfl) ⟨1606298, by rfl⟩ : syracuseStep 2141731 = 3212597) B3212597
theorem B5421269 : Blo 2141435 5421269 := bbase (se 7 (by rfl) ⟨63530, by rfl⟩ : syracuseStep 5421269 = 127061) (by norm_num)
theorem B3614179 : Blo 2141435 3614179 := bstep (se 1 (by rfl) ⟨2710634, by rfl⟩ : syracuseStep 3614179 = 5421269) B5421269
theorem B4818905 : Blo 2141435 4818905 := bstep (se 2 (by rfl) ⟨1807089, by rfl⟩ : syracuseStep 4818905 = 3614179) B3614179
theorem B3212603 : Blo 2141435 3212603 := bstep (se 1 (by rfl) ⟨2409452, by rfl⟩ : syracuseStep 3212603 = 4818905) B4818905
theorem B2141735 : Blo 2141435 2141735 := bstep (se 1 (by rfl) ⟨1606301, by rfl⟩ : syracuseStep 2141735 = 3212603) B3212603
theorem B2409457 : Blo 2141435 2409457 := bbase (se 2 (by rfl) ⟨903546, by rfl⟩ : syracuseStep 2409457 = 1807093) (by norm_num)
theorem B3212609 : Blo 2141435 3212609 := bstep (se 2 (by rfl) ⟨1204728, by rfl⟩ : syracuseStep 3212609 = 2409457) B2409457
theorem B2141739 : Blo 2141435 2141739 := bstep (se 1 (by rfl) ⟨1606304, by rfl⟩ : syracuseStep 2141739 = 3212609) B3212609
theorem B3859493 : Blo 2141435 3859493 := bbase (se 4 (by rfl) ⟨361827, by rfl⟩ : syracuseStep 3859493 = 723655) (by norm_num)
theorem B10291981 : Blo 2141435 10291981 := bstep (se 3 (by rfl) ⟨1929746, by rfl⟩ : syracuseStep 10291981 = 3859493) B3859493
theorem B13722641 : Blo 2141435 13722641 := bstep (se 2 (by rfl) ⟨5145990, by rfl⟩ : syracuseStep 13722641 = 10291981) B10291981
theorem B9148427 : Blo 2141435 9148427 := bstep (se 1 (by rfl) ⟨6861320, by rfl⟩ : syracuseStep 9148427 = 13722641) B13722641
theorem B6098951 : Blo 2141435 6098951 := bstep (se 1 (by rfl) ⟨4574213, by rfl⟩ : syracuseStep 6098951 = 9148427) B9148427
theorem B4065967 : Blo 2141435 4065967 := bstep (se 1 (by rfl) ⟨3049475, by rfl⟩ : syracuseStep 4065967 = 6098951) B6098951
theorem B5421289 : Blo 2141435 5421289 := bstep (se 2 (by rfl) ⟨2032983, by rfl⟩ : syracuseStep 5421289 = 4065967) B4065967
theorem B7228385 : Blo 2141435 7228385 := bstep (se 2 (by rfl) ⟨2710644, by rfl⟩ : syracuseStep 7228385 = 5421289) B5421289
theorem B4818923 : Blo 2141435 4818923 := bstep (se 1 (by rfl) ⟨3614192, by rfl⟩ : syracuseStep 4818923 = 7228385) B7228385
theorem B3212615 : Blo 2141435 3212615 := bstep (se 1 (by rfl) ⟨2409461, by rfl⟩ : syracuseStep 3212615 = 4818923) B4818923
theorem B2141743 : Blo 2141435 2141743 := bstep (se 1 (by rfl) ⟨1606307, by rfl⟩ : syracuseStep 2141743 = 3212615) B3212615
theorem B3212621 : Blo 2141435 3212621 := bbase (se 3 (by rfl) ⟨602366, by rfl⟩ : syracuseStep 3212621 = 1204733) (by norm_num)
theorem B2141747 : Blo 2141435 2141747 := bstep (se 1 (by rfl) ⟨1606310, by rfl⟩ : syracuseStep 2141747 = 3212621) B3212621
theorem B4818941 : Blo 2141435 4818941 := bbase (se 3 (by rfl) ⟨903551, by rfl⟩ : syracuseStep 4818941 = 1807103) (by norm_num)
theorem B3212627 : Blo 2141435 3212627 := bstep (se 1 (by rfl) ⟨2409470, by rfl⟩ : syracuseStep 3212627 = 4818941) B4818941
theorem B2141751 : Blo 2141435 2141751 := bstep (se 1 (by rfl) ⟨1606313, by rfl⟩ : syracuseStep 2141751 = 3212627) B3212627
theorem B3614213 : Blo 2141435 3614213 := bbase (se 4 (by rfl) ⟨338832, by rfl⟩ : syracuseStep 3614213 = 677665) (by norm_num)
theorem B2409475 : Blo 2141435 2409475 := bstep (se 1 (by rfl) ⟨1807106, by rfl⟩ : syracuseStep 2409475 = 3614213) B3614213
theorem B3212633 : Blo 2141435 3212633 := bstep (se 2 (by rfl) ⟨1204737, by rfl⟩ : syracuseStep 3212633 = 2409475) B2409475
theorem B2141755 : Blo 2141435 2141755 := bstep (se 1 (by rfl) ⟨1606316, by rfl⟩ : syracuseStep 2141755 = 3212633) B3212633
theorem B16263989 : Blo 2141435 16263989 := bbase (se 5 (by rfl) ⟨762374, by rfl⟩ : syracuseStep 16263989 = 1524749) (by norm_num)
theorem B10842659 : Blo 2141435 10842659 := bstep (se 1 (by rfl) ⟨8131994, by rfl⟩ : syracuseStep 10842659 = 16263989) B16263989
theorem B7228439 : Blo 2141435 7228439 := bstep (se 1 (by rfl) ⟨5421329, by rfl⟩ : syracuseStep 7228439 = 10842659) B10842659
theorem B4818959 : Blo 2141435 4818959 := bstep (se 1 (by rfl) ⟨3614219, by rfl⟩ : syracuseStep 4818959 = 7228439) B7228439
theorem B3212639 : Blo 2141435 3212639 := bstep (se 1 (by rfl) ⟨2409479, by rfl⟩ : syracuseStep 3212639 = 4818959) B4818959
theorem B2141759 : Blo 2141435 2141759 := bstep (se 1 (by rfl) ⟨1606319, by rfl⟩ : syracuseStep 2141759 = 3212639) B3212639
theorem B3212645 : Blo 2141435 3212645 := bbase (se 4 (by rfl) ⟨301185, by rfl⟩ : syracuseStep 3212645 = 602371) (by norm_num)
theorem B2141763 : Blo 2141435 2141763 := bstep (se 1 (by rfl) ⟨1606322, by rfl⟩ : syracuseStep 2141763 = 3212645) B3212645
theorem B4066013 : Blo 2141435 4066013 := bbase (se 3 (by rfl) ⟨762377, by rfl⟩ : syracuseStep 4066013 = 1524755) (by norm_num)
theorem B2710675 : Blo 2141435 2710675 := bstep (se 1 (by rfl) ⟨2033006, by rfl⟩ : syracuseStep 2710675 = 4066013) B4066013
theorem B3614233 : Blo 2141435 3614233 := bstep (se 2 (by rfl) ⟨1355337, by rfl⟩ : syracuseStep 3614233 = 2710675) B2710675
theorem B4818977 : Blo 2141435 4818977 := bstep (se 2 (by rfl) ⟨1807116, by rfl⟩ : syracuseStep 4818977 = 3614233) B3614233
theorem B3212651 : Blo 2141435 3212651 := bstep (se 1 (by rfl) ⟨2409488, by rfl⟩ : syracuseStep 3212651 = 4818977) B4818977
theorem B2141767 : Blo 2141435 2141767 := bstep (se 1 (by rfl) ⟨1606325, by rfl⟩ : syracuseStep 2141767 = 3212651) B3212651
theorem B2409493 : Blo 2141435 2409493 := bbase (se 6 (by rfl) ⟨56472, by rfl⟩ : syracuseStep 2409493 = 112945) (by norm_num)
theorem B3212657 : Blo 2141435 3212657 := bstep (se 2 (by rfl) ⟨1204746, by rfl⟩ : syracuseStep 3212657 = 2409493) B2409493
theorem B2141771 : Blo 2141435 2141771 := bstep (se 1 (by rfl) ⟨1606328, by rfl⟩ : syracuseStep 2141771 = 3212657) B3212657
theorem B2710685 : Blo 2141435 2710685 := bbase (se 3 (by rfl) ⟨508253, by rfl⟩ : syracuseStep 2710685 = 1016507) (by norm_num)
theorem B7228493 : Blo 2141435 7228493 := bstep (se 3 (by rfl) ⟨1355342, by rfl⟩ : syracuseStep 7228493 = 2710685) B2710685
theorem B4818995 : Blo 2141435 4818995 := bstep (se 1 (by rfl) ⟨3614246, by rfl⟩ : syracuseStep 4818995 = 7228493) B7228493
theorem B3212663 : Blo 2141435 3212663 := bstep (se 1 (by rfl) ⟨2409497, by rfl⟩ : syracuseStep 3212663 = 4818995) B4818995
theorem B2141775 : Blo 2141435 2141775 := bstep (se 1 (by rfl) ⟨1606331, by rfl⟩ : syracuseStep 2141775 = 3212663) B3212663
theorem B3212669 : Blo 2141435 3212669 := bbase (se 3 (by rfl) ⟨602375, by rfl⟩ : syracuseStep 3212669 = 1204751) (by norm_num)
theorem B2141779 : Blo 2141435 2141779 := bstep (se 1 (by rfl) ⟨1606334, by rfl⟩ : syracuseStep 2141779 = 3212669) B3212669
theorem B4819013 : Blo 2141435 4819013 := bbase (se 4 (by rfl) ⟨451782, by rfl⟩ : syracuseStep 4819013 = 903565) (by norm_num)
theorem B3212675 : Blo 2141435 3212675 := bstep (se 1 (by rfl) ⟨2409506, by rfl⟩ : syracuseStep 3212675 = 4819013) B4819013
theorem B2141783 : Blo 2141435 2141783 := bstep (se 1 (by rfl) ⟨1606337, by rfl⟩ : syracuseStep 2141783 = 3212675) B3212675
theorem B6099077 : Blo 2141435 6099077 := bbase (se 4 (by rfl) ⟨571788, by rfl⟩ : syracuseStep 6099077 = 1143577) (by norm_num)
theorem B4066051 : Blo 2141435 4066051 := bstep (se 1 (by rfl) ⟨3049538, by rfl⟩ : syracuseStep 4066051 = 6099077) B6099077
theorem B5421401 : Blo 2141435 5421401 := bstep (se 2 (by rfl) ⟨2033025, by rfl⟩ : syracuseStep 5421401 = 4066051) B4066051
theorem B3614267 : Blo 2141435 3614267 := bstep (se 1 (by rfl) ⟨2710700, by rfl⟩ : syracuseStep 3614267 = 5421401) B5421401
theorem B2409511 : Blo 2141435 2409511 := bstep (se 1 (by rfl) ⟨1807133, by rfl⟩ : syracuseStep 2409511 = 3614267) B3614267
theorem B3212681 : Blo 2141435 3212681 := bstep (se 2 (by rfl) ⟨1204755, by rfl⟩ : syracuseStep 3212681 = 2409511) B2409511
theorem B2141787 : Blo 2141435 2141787 := bstep (se 1 (by rfl) ⟨1606340, by rfl⟩ : syracuseStep 2141787 = 3212681) B3212681
theorem B10842821 : Blo 2141435 10842821 := bbase (se 4 (by rfl) ⟨1016514, by rfl⟩ : syracuseStep 10842821 = 2033029) (by norm_num)
theorem B7228547 : Blo 2141435 7228547 := bstep (se 1 (by rfl) ⟨5421410, by rfl⟩ : syracuseStep 7228547 = 10842821) B10842821
theorem B4819031 : Blo 2141435 4819031 := bstep (se 1 (by rfl) ⟨3614273, by rfl⟩ : syracuseStep 4819031 = 7228547) B7228547
theorem B3212687 : Blo 2141435 3212687 := bstep (se 1 (by rfl) ⟨2409515, by rfl⟩ : syracuseStep 3212687 = 4819031) B4819031
theorem B2141791 : Blo 2141435 2141791 := bstep (se 1 (by rfl) ⟨1606343, by rfl⟩ : syracuseStep 2141791 = 3212687) B3212687
theorem B3212693 : Blo 2141435 3212693 := bbase (se 6 (by rfl) ⟨75297, by rfl⟩ : syracuseStep 3212693 = 150595) (by norm_num)
theorem B2141795 : Blo 2141435 2141795 := bstep (se 1 (by rfl) ⟨1606346, by rfl⟩ : syracuseStep 2141795 = 3212693) B3212693
theorem B4574333 : Blo 2141435 4574333 := bbase (se 3 (by rfl) ⟨857687, by rfl⟩ : syracuseStep 4574333 = 1715375) (by norm_num)
theorem B12198221 : Blo 2141435 12198221 := bstep (se 3 (by rfl) ⟨2287166, by rfl⟩ : syracuseStep 12198221 = 4574333) B4574333
theorem B8132147 : Blo 2141435 8132147 := bstep (se 1 (by rfl) ⟨6099110, by rfl⟩ : syracuseStep 8132147 = 12198221) B12198221
theorem B5421431 : Blo 2141435 5421431 := bstep (se 1 (by rfl) ⟨4066073, by rfl⟩ : syracuseStep 5421431 = 8132147) B8132147
theorem B3614287 : Blo 2141435 3614287 := bstep (se 1 (by rfl) ⟨2710715, by rfl⟩ : syracuseStep 3614287 = 5421431) B5421431
theorem B4819049 : Blo 2141435 4819049 := bstep (se 2 (by rfl) ⟨1807143, by rfl⟩ : syracuseStep 4819049 = 3614287) B3614287
theorem B3212699 : Blo 2141435 3212699 := bstep (se 1 (by rfl) ⟨2409524, by rfl⟩ : syracuseStep 3212699 = 4819049) B4819049
theorem B2141799 : Blo 2141435 2141799 := bstep (se 1 (by rfl) ⟨1606349, by rfl⟩ : syracuseStep 2141799 = 3212699) B3212699
theorem B2409529 : Blo 2141435 2409529 := bbase (se 2 (by rfl) ⟨903573, by rfl⟩ : syracuseStep 2409529 = 1807147) (by norm_num)
theorem B3212705 : Blo 2141435 3212705 := bstep (se 2 (by rfl) ⟨1204764, by rfl⟩ : syracuseStep 3212705 = 2409529) B2409529
theorem B2141803 : Blo 2141435 2141803 := bstep (se 1 (by rfl) ⟨1606352, by rfl⟩ : syracuseStep 2141803 = 3212705) B3212705
theorem B4342061 : Blo 2141435 4342061 := bbase (se 3 (by rfl) ⟨814136, by rfl⟩ : syracuseStep 4342061 = 1628273) (by norm_num)
theorem B2894707 : Blo 2141435 2894707 := bstep (se 1 (by rfl) ⟨2171030, by rfl⟩ : syracuseStep 2894707 = 4342061) B4342061
theorem B3859609 : Blo 2141435 3859609 := bstep (se 2 (by rfl) ⟨1447353, by rfl⟩ : syracuseStep 3859609 = 2894707) B2894707
theorem B5146145 : Blo 2141435 5146145 := bstep (se 2 (by rfl) ⟨1929804, by rfl⟩ : syracuseStep 5146145 = 3859609) B3859609
theorem B3430763 : Blo 2141435 3430763 := bstep (se 1 (by rfl) ⟨2573072, by rfl⟩ : syracuseStep 3430763 = 5146145) B5146145
theorem B2287175 : Blo 2141435 2287175 := bstep (se 1 (by rfl) ⟨1715381, by rfl⟩ : syracuseStep 2287175 = 3430763) B3430763
theorem B6099133 : Blo 2141435 6099133 := bstep (se 3 (by rfl) ⟨1143587, by rfl⟩ : syracuseStep 6099133 = 2287175) B2287175
theorem B8132177 : Blo 2141435 8132177 := bstep (se 2 (by rfl) ⟨3049566, by rfl⟩ : syracuseStep 8132177 = 6099133) B6099133
theorem B5421451 : Blo 2141435 5421451 := bstep (se 1 (by rfl) ⟨4066088, by rfl⟩ : syracuseStep 5421451 = 8132177) B8132177
theorem B7228601 : Blo 2141435 7228601 := bstep (se 2 (by rfl) ⟨2710725, by rfl⟩ : syracuseStep 7228601 = 5421451) B5421451
theorem B4819067 : Blo 2141435 4819067 := bstep (se 1 (by rfl) ⟨3614300, by rfl⟩ : syracuseStep 4819067 = 7228601) B7228601
theorem B3212711 : Blo 2141435 3212711 := bstep (se 1 (by rfl) ⟨2409533, by rfl⟩ : syracuseStep 3212711 = 4819067) B4819067
theorem B2141807 : Blo 2141435 2141807 := bstep (se 1 (by rfl) ⟨1606355, by rfl⟩ : syracuseStep 2141807 = 3212711) B3212711
theorem B3212717 : Blo 2141435 3212717 := bbase (se 3 (by rfl) ⟨602384, by rfl⟩ : syracuseStep 3212717 = 1204769) (by norm_num)
theorem B2141811 : Blo 2141435 2141811 := bstep (se 1 (by rfl) ⟨1606358, by rfl⟩ : syracuseStep 2141811 = 3212717) B3212717
theorem B4819085 : Blo 2141435 4819085 := bbase (se 3 (by rfl) ⟨903578, by rfl⟩ : syracuseStep 4819085 = 1807157) (by norm_num)
theorem B3212723 : Blo 2141435 3212723 := bstep (se 1 (by rfl) ⟨2409542, by rfl⟩ : syracuseStep 3212723 = 4819085) B4819085
theorem B2141815 : Blo 2141435 2141815 := bstep (se 1 (by rfl) ⟨1606361, by rfl⟩ : syracuseStep 2141815 = 3212723) B3212723
theorem B2710741 : Blo 2141435 2710741 := bbase (se 7 (by rfl) ⟨31766, by rfl⟩ : syracuseStep 2710741 = 63533) (by norm_num)
theorem B3614321 : Blo 2141435 3614321 := bstep (se 2 (by rfl) ⟨1355370, by rfl⟩ : syracuseStep 3614321 = 2710741) B2710741
theorem B2409547 : Blo 2141435 2409547 := bstep (se 1 (by rfl) ⟨1807160, by rfl⟩ : syracuseStep 2409547 = 3614321) B3614321
theorem B3212729 : Blo 2141435 3212729 := bstep (se 2 (by rfl) ⟨1204773, by rfl⟩ : syracuseStep 3212729 = 2409547) B2409547
theorem B2141819 : Blo 2141435 2141819 := bstep (se 1 (by rfl) ⟨1606364, by rfl⟩ : syracuseStep 2141819 = 3212729) B3212729
theorem B2934221 : Blo 2141435 2934221 := bbase (se 3 (by rfl) ⟨550166, by rfl⟩ : syracuseStep 2934221 = 1100333) (by norm_num)
theorem B31298357 : Blo 2141435 31298357 := bstep (se 5 (by rfl) ⟨1467110, by rfl⟩ : syracuseStep 31298357 = 2934221) B2934221
theorem B83462285 : Blo 2141435 83462285 := bstep (se 3 (by rfl) ⟨15649178, by rfl⟩ : syracuseStep 83462285 = 31298357) B31298357
theorem B222566093 : Blo 2141435 222566093 := bstep (se 3 (by rfl) ⟨41731142, by rfl⟩ : syracuseStep 222566093 = 83462285) B83462285
theorem B148377395 : Blo 2141435 148377395 := bstep (se 1 (by rfl) ⟨111283046, by rfl⟩ : syracuseStep 148377395 = 222566093) B222566093
theorem B98918263 : Blo 2141435 98918263 := bstep (se 1 (by rfl) ⟨74188697, by rfl⟩ : syracuseStep 98918263 = 148377395) B148377395
theorem B131891017 : Blo 2141435 131891017 := bstep (se 2 (by rfl) ⟨49459131, by rfl⟩ : syracuseStep 131891017 = 98918263) B98918263
theorem B175854689 : Blo 2141435 175854689 := bstep (se 2 (by rfl) ⟨65945508, by rfl⟩ : syracuseStep 175854689 = 131891017) B131891017
theorem B117236459 : Blo 2141435 117236459 := bstep (se 1 (by rfl) ⟨87927344, by rfl⟩ : syracuseStep 117236459 = 175854689) B175854689
theorem B78157639 : Blo 2141435 78157639 := bstep (se 1 (by rfl) ⟨58618229, by rfl⟩ : syracuseStep 78157639 = 117236459) B117236459
theorem B104210185 : Blo 2141435 104210185 := bstep (se 2 (by rfl) ⟨39078819, by rfl⟩ : syracuseStep 104210185 = 78157639) B78157639
theorem B138946913 : Blo 2141435 138946913 := bstep (se 2 (by rfl) ⟨52105092, by rfl⟩ : syracuseStep 138946913 = 104210185) B104210185
theorem B92631275 : Blo 2141435 92631275 := bstep (se 1 (by rfl) ⟨69473456, by rfl⟩ : syracuseStep 92631275 = 138946913) B138946913
theorem B61754183 : Blo 2141435 61754183 := bstep (se 1 (by rfl) ⟨46315637, by rfl⟩ : syracuseStep 61754183 = 92631275) B92631275
theorem B41169455 : Blo 2141435 41169455 := bstep (se 1 (by rfl) ⟨30877091, by rfl⟩ : syracuseStep 41169455 = 61754183) B61754183
theorem B27446303 : Blo 2141435 27446303 := bstep (se 1 (by rfl) ⟨20584727, by rfl⟩ : syracuseStep 27446303 = 41169455) B41169455
theorem B18297535 : Blo 2141435 18297535 := bstep (se 1 (by rfl) ⟨13723151, by rfl⟩ : syracuseStep 18297535 = 27446303) B27446303
theorem B24396713 : Blo 2141435 24396713 := bstep (se 2 (by rfl) ⟨9148767, by rfl⟩ : syracuseStep 24396713 = 18297535) B18297535
theorem B16264475 : Blo 2141435 16264475 := bstep (se 1 (by rfl) ⟨12198356, by rfl⟩ : syracuseStep 16264475 = 24396713) B24396713
theorem B10842983 : Blo 2141435 10842983 := bstep (se 1 (by rfl) ⟨8132237, by rfl⟩ : syracuseStep 10842983 = 16264475) B16264475
theorem B7228655 : Blo 2141435 7228655 := bstep (se 1 (by rfl) ⟨5421491, by rfl⟩ : syracuseStep 7228655 = 10842983) B10842983
theorem B4819103 : Blo 2141435 4819103 := bstep (se 1 (by rfl) ⟨3614327, by rfl⟩ : syracuseStep 4819103 = 7228655) B7228655
theorem B3212735 : Blo 2141435 3212735 := bstep (se 1 (by rfl) ⟨2409551, by rfl⟩ : syracuseStep 3212735 = 4819103) B4819103
theorem B2141823 : Blo 2141435 2141823 := bstep (se 1 (by rfl) ⟨1606367, by rfl⟩ : syracuseStep 2141823 = 3212735) B3212735
theorem B3212741 : Blo 2141435 3212741 := bbase (se 4 (by rfl) ⟨301194, by rfl⟩ : syracuseStep 3212741 = 602389) (by norm_num)
theorem B2141827 : Blo 2141435 2141827 := bstep (se 1 (by rfl) ⟨1606370, by rfl⟩ : syracuseStep 2141827 = 3212741) B3212741
theorem B3614341 : Blo 2141435 3614341 := bbase (se 4 (by rfl) ⟨338844, by rfl⟩ : syracuseStep 3614341 = 677689) (by norm_num)
theorem B4819121 : Blo 2141435 4819121 := bstep (se 2 (by rfl) ⟨1807170, by rfl⟩ : syracuseStep 4819121 = 3614341) B3614341
theorem B3212747 : Blo 2141435 3212747 := bstep (se 1 (by rfl) ⟨2409560, by rfl⟩ : syracuseStep 3212747 = 4819121) B4819121
theorem B2141831 : Blo 2141435 2141831 := bstep (se 1 (by rfl) ⟨1606373, by rfl⟩ : syracuseStep 2141831 = 3212747) B3212747
theorem B2409565 : Blo 2141435 2409565 := bbase (se 3 (by rfl) ⟨451793, by rfl⟩ : syracuseStep 2409565 = 903587) (by norm_num)
theorem B3212753 : Blo 2141435 3212753 := bstep (se 2 (by rfl) ⟨1204782, by rfl⟩ : syracuseStep 3212753 = 2409565) B2409565
theorem B2141835 : Blo 2141435 2141835 := bstep (se 1 (by rfl) ⟨1606376, by rfl⟩ : syracuseStep 2141835 = 3212753) B3212753
theorem B7228709 : Blo 2141435 7228709 := bbase (se 4 (by rfl) ⟨677691, by rfl⟩ : syracuseStep 7228709 = 1355383) (by norm_num)
theorem B4819139 : Blo 2141435 4819139 := bstep (se 1 (by rfl) ⟨3614354, by rfl⟩ : syracuseStep 4819139 = 7228709) B7228709
theorem B3212759 : Blo 2141435 3212759 := bstep (se 1 (by rfl) ⟨2409569, by rfl⟩ : syracuseStep 3212759 = 4819139) B4819139
theorem B2141839 : Blo 2141435 2141839 := bstep (se 1 (by rfl) ⟨1606379, by rfl⟩ : syracuseStep 2141839 = 3212759) B3212759
theorem B3212765 : Blo 2141435 3212765 := bbase (se 3 (by rfl) ⟨602393, by rfl⟩ : syracuseStep 3212765 = 1204787) (by norm_num)
theorem B2141843 : Blo 2141435 2141843 := bstep (se 1 (by rfl) ⟨1606382, by rfl⟩ : syracuseStep 2141843 = 3212765) B3212765
theorem B4819157 : Blo 2141435 4819157 := bbase (se 7 (by rfl) ⟨56474, by rfl⟩ : syracuseStep 4819157 = 112949) (by norm_num)
theorem B3212771 : Blo 2141435 3212771 := bstep (se 1 (by rfl) ⟨2409578, by rfl⟩ : syracuseStep 3212771 = 4819157) B4819157
theorem B2141847 : Blo 2141435 2141847 := bstep (se 1 (by rfl) ⟨1606385, by rfl⟩ : syracuseStep 2141847 = 3212771) B3212771
theorem B10292501 : Blo 2141435 10292501 := bbase (se 6 (by rfl) ⟨241230, by rfl⟩ : syracuseStep 10292501 = 482461) (by norm_num)
theorem B6861667 : Blo 2141435 6861667 := bstep (se 1 (by rfl) ⟨5146250, by rfl⟩ : syracuseStep 6861667 = 10292501) B10292501
theorem B9148889 : Blo 2141435 9148889 := bstep (se 2 (by rfl) ⟨3430833, by rfl⟩ : syracuseStep 9148889 = 6861667) B6861667
theorem B6099259 : Blo 2141435 6099259 := bstep (se 1 (by rfl) ⟨4574444, by rfl⟩ : syracuseStep 6099259 = 9148889) B9148889
theorem B8132345 : Blo 2141435 8132345 := bstep (se 2 (by rfl) ⟨3049629, by rfl⟩ : syracuseStep 8132345 = 6099259) B6099259
theorem B5421563 : Blo 2141435 5421563 := bstep (se 1 (by rfl) ⟨4066172, by rfl⟩ : syracuseStep 5421563 = 8132345) B8132345
theorem B3614375 : Blo 2141435 3614375 := bstep (se 1 (by rfl) ⟨2710781, by rfl⟩ : syracuseStep 3614375 = 5421563) B5421563
theorem B2409583 : Blo 2141435 2409583 := bstep (se 1 (by rfl) ⟨1807187, by rfl⟩ : syracuseStep 2409583 = 3614375) B3614375
theorem B3212777 : Blo 2141435 3212777 := bstep (se 2 (by rfl) ⟨1204791, by rfl⟩ : syracuseStep 3212777 = 2409583) B2409583
theorem B2141851 : Blo 2141435 2141851 := bstep (se 1 (by rfl) ⟨1606388, by rfl⟩ : syracuseStep 2141851 = 3212777) B3212777
theorem B4342157 : Blo 2141435 4342157 := bbase (se 3 (by rfl) ⟨814154, by rfl⟩ : syracuseStep 4342157 = 1628309) (by norm_num)
theorem B2894771 : Blo 2141435 2894771 := bstep (se 1 (by rfl) ⟨2171078, by rfl⟩ : syracuseStep 2894771 = 4342157) B4342157
theorem B7719389 : Blo 2141435 7719389 := bstep (se 3 (by rfl) ⟨1447385, by rfl⟩ : syracuseStep 7719389 = 2894771) B2894771
theorem B5146259 : Blo 2141435 5146259 := bstep (se 1 (by rfl) ⟨3859694, by rfl⟩ : syracuseStep 5146259 = 7719389) B7719389
theorem B13723357 : Blo 2141435 13723357 := bstep (se 3 (by rfl) ⟨2573129, by rfl⟩ : syracuseStep 13723357 = 5146259) B5146259
theorem B18297809 : Blo 2141435 18297809 := bstep (se 2 (by rfl) ⟨6861678, by rfl⟩ : syracuseStep 18297809 = 13723357) B13723357
theorem B12198539 : Blo 2141435 12198539 := bstep (se 1 (by rfl) ⟨9148904, by rfl⟩ : syracuseStep 12198539 = 18297809) B18297809
theorem B8132359 : Blo 2141435 8132359 := bstep (se 1 (by rfl) ⟨6099269, by rfl⟩ : syracuseStep 8132359 = 12198539) B12198539
theorem B10843145 : Blo 2141435 10843145 := bstep (se 2 (by rfl) ⟨4066179, by rfl⟩ : syracuseStep 10843145 = 8132359) B8132359
theorem B7228763 : Blo 2141435 7228763 := bstep (se 1 (by rfl) ⟨5421572, by rfl⟩ : syracuseStep 7228763 = 10843145) B10843145
theorem B4819175 : Blo 2141435 4819175 := bstep (se 1 (by rfl) ⟨3614381, by rfl⟩ : syracuseStep 4819175 = 7228763) B7228763
theorem B3212783 : Blo 2141435 3212783 := bstep (se 1 (by rfl) ⟨2409587, by rfl⟩ : syracuseStep 3212783 = 4819175) B4819175
theorem B2141855 : Blo 2141435 2141855 := bstep (se 1 (by rfl) ⟨1606391, by rfl⟩ : syracuseStep 2141855 = 3212783) B3212783
theorem B3212789 : Blo 2141435 3212789 := bbase (se 5 (by rfl) ⟨150599, by rfl⟩ : syracuseStep 3212789 = 301199) (by norm_num)
theorem B2141859 : Blo 2141435 2141859 := bstep (se 1 (by rfl) ⟨1606394, by rfl⟩ : syracuseStep 2141859 = 3212789) B3212789
theorem B3430853 : Blo 2141435 3430853 := bbase (se 4 (by rfl) ⟨321642, by rfl⟩ : syracuseStep 3430853 = 643285) (by norm_num)
theorem B2287235 : Blo 2141435 2287235 := bstep (se 1 (by rfl) ⟨1715426, by rfl⟩ : syracuseStep 2287235 = 3430853) B3430853
theorem B6099293 : Blo 2141435 6099293 := bstep (se 3 (by rfl) ⟨1143617, by rfl⟩ : syracuseStep 6099293 = 2287235) B2287235
theorem B4066195 : Blo 2141435 4066195 := bstep (se 1 (by rfl) ⟨3049646, by rfl⟩ : syracuseStep 4066195 = 6099293) B6099293
theorem B5421593 : Blo 2141435 5421593 := bstep (se 2 (by rfl) ⟨2033097, by rfl⟩ : syracuseStep 5421593 = 4066195) B4066195
theorem B3614395 : Blo 2141435 3614395 := bstep (se 1 (by rfl) ⟨2710796, by rfl⟩ : syracuseStep 3614395 = 5421593) B5421593
theorem B4819193 : Blo 2141435 4819193 := bstep (se 2 (by rfl) ⟨1807197, by rfl⟩ : syracuseStep 4819193 = 3614395) B3614395
theorem B3212795 : Blo 2141435 3212795 := bstep (se 1 (by rfl) ⟨2409596, by rfl⟩ : syracuseStep 3212795 = 4819193) B4819193
theorem B2141863 : Blo 2141435 2141863 := bstep (se 1 (by rfl) ⟨1606397, by rfl⟩ : syracuseStep 2141863 = 3212795) B3212795
theorem B2409601 : Blo 2141435 2409601 := bbase (se 2 (by rfl) ⟨903600, by rfl⟩ : syracuseStep 2409601 = 1807201) (by norm_num)
theorem B3212801 : Blo 2141435 3212801 := bstep (se 2 (by rfl) ⟨1204800, by rfl⟩ : syracuseStep 3212801 = 2409601) B2409601
theorem B2141867 : Blo 2141435 2141867 := bstep (se 1 (by rfl) ⟨1606400, by rfl⟩ : syracuseStep 2141867 = 3212801) B3212801
theorem B5421613 : Blo 2141435 5421613 := bbase (se 3 (by rfl) ⟨1016552, by rfl⟩ : syracuseStep 5421613 = 2033105) (by norm_num)
theorem B7228817 : Blo 2141435 7228817 := bstep (se 2 (by rfl) ⟨2710806, by rfl⟩ : syracuseStep 7228817 = 5421613) B5421613
theorem B4819211 : Blo 2141435 4819211 := bstep (se 1 (by rfl) ⟨3614408, by rfl⟩ : syracuseStep 4819211 = 7228817) B7228817
theorem B3212807 : Blo 2141435 3212807 := bstep (se 1 (by rfl) ⟨2409605, by rfl⟩ : syracuseStep 3212807 = 4819211) B4819211
theorem B2141871 : Blo 2141435 2141871 := bstep (se 1 (by rfl) ⟨1606403, by rfl⟩ : syracuseStep 2141871 = 3212807) B3212807
theorem B3212813 : Blo 2141435 3212813 := bbase (se 3 (by rfl) ⟨602402, by rfl⟩ : syracuseStep 3212813 = 1204805) (by norm_num)
theorem B2141875 : Blo 2141435 2141875 := bstep (se 1 (by rfl) ⟨1606406, by rfl⟩ : syracuseStep 2141875 = 3212813) B3212813
theorem B4819229 : Blo 2141435 4819229 := bbase (se 3 (by rfl) ⟨903605, by rfl⟩ : syracuseStep 4819229 = 1807211) (by norm_num)
theorem B3212819 : Blo 2141435 3212819 := bstep (se 1 (by rfl) ⟨2409614, by rfl⟩ : syracuseStep 3212819 = 4819229) B4819229
theorem B2141879 : Blo 2141435 2141879 := bstep (se 1 (by rfl) ⟨1606409, by rfl⟩ : syracuseStep 2141879 = 3212819) B3212819
theorem B3614429 : Blo 2141435 3614429 := bbase (se 3 (by rfl) ⟨677705, by rfl⟩ : syracuseStep 3614429 = 1355411) (by norm_num)
theorem B2409619 : Blo 2141435 2409619 := bstep (se 1 (by rfl) ⟨1807214, by rfl⟩ : syracuseStep 2409619 = 3614429) B3614429
theorem B3212825 : Blo 2141435 3212825 := bstep (se 2 (by rfl) ⟨1204809, by rfl⟩ : syracuseStep 3212825 = 2409619) B2409619
theorem B2141883 : Blo 2141435 2141883 := bstep (se 1 (by rfl) ⟨1606412, by rfl⟩ : syracuseStep 2141883 = 3212825) B3212825
theorem B6861781 : Blo 2141435 6861781 := bbase (se 7 (by rfl) ⟨80411, by rfl⟩ : syracuseStep 6861781 = 160823) (by norm_num)
theorem B9149041 : Blo 2141435 9149041 := bstep (se 2 (by rfl) ⟨3430890, by rfl⟩ : syracuseStep 9149041 = 6861781) B6861781
theorem B12198721 : Blo 2141435 12198721 := bstep (se 2 (by rfl) ⟨4574520, by rfl⟩ : syracuseStep 12198721 = 9149041) B9149041
theorem B16264961 : Blo 2141435 16264961 := bstep (se 2 (by rfl) ⟨6099360, by rfl⟩ : syracuseStep 16264961 = 12198721) B12198721
theorem B10843307 : Blo 2141435 10843307 := bstep (se 1 (by rfl) ⟨8132480, by rfl⟩ : syracuseStep 10843307 = 16264961) B16264961
theorem B7228871 : Blo 2141435 7228871 := bstep (se 1 (by rfl) ⟨5421653, by rfl⟩ : syracuseStep 7228871 = 10843307) B10843307
theorem B4819247 : Blo 2141435 4819247 := bstep (se 1 (by rfl) ⟨3614435, by rfl⟩ : syracuseStep 4819247 = 7228871) B7228871
theorem B3212831 : Blo 2141435 3212831 := bstep (se 1 (by rfl) ⟨2409623, by rfl⟩ : syracuseStep 3212831 = 4819247) B4819247
theorem B2141887 : Blo 2141435 2141887 := bstep (se 1 (by rfl) ⟨1606415, by rfl⟩ : syracuseStep 2141887 = 3212831) B3212831
theorem B3212837 : Blo 2141435 3212837 := bbase (se 4 (by rfl) ⟨301203, by rfl⟩ : syracuseStep 3212837 = 602407) (by norm_num)
theorem B2141891 : Blo 2141435 2141891 := bstep (se 1 (by rfl) ⟨1606418, by rfl⟩ : syracuseStep 2141891 = 3212837) B3212837
theorem B2710837 : Blo 2141435 2710837 := bbase (se 5 (by rfl) ⟨127070, by rfl⟩ : syracuseStep 2710837 = 254141) (by norm_num)
theorem B3614449 : Blo 2141435 3614449 := bstep (se 2 (by rfl) ⟨1355418, by rfl⟩ : syracuseStep 3614449 = 2710837) B2710837
theorem B4819265 : Blo 2141435 4819265 := bstep (se 2 (by rfl) ⟨1807224, by rfl⟩ : syracuseStep 4819265 = 3614449) B3614449
theorem B3212843 : Blo 2141435 3212843 := bstep (se 1 (by rfl) ⟨2409632, by rfl⟩ : syracuseStep 3212843 = 4819265) B4819265
theorem B2141895 : Blo 2141435 2141895 := bstep (se 1 (by rfl) ⟨1606421, by rfl⟩ : syracuseStep 2141895 = 3212843) B3212843
theorem B2409637 : Blo 2141435 2409637 := bbase (se 4 (by rfl) ⟨225903, by rfl⟩ : syracuseStep 2409637 = 451807) (by norm_num)
theorem B3212849 : Blo 2141435 3212849 := bstep (se 2 (by rfl) ⟨1204818, by rfl⟩ : syracuseStep 3212849 = 2409637) B2409637
theorem B2141899 : Blo 2141435 2141899 := bstep (se 1 (by rfl) ⟨1606424, by rfl⟩ : syracuseStep 2141899 = 3212849) B3212849
theorem B4885037 : Blo 2141435 4885037 := bbase (se 3 (by rfl) ⟨915944, by rfl⟩ : syracuseStep 4885037 = 1831889) (by norm_num)
theorem B3256691 : Blo 2141435 3256691 := bstep (se 1 (by rfl) ⟨2442518, by rfl⟩ : syracuseStep 3256691 = 4885037) B4885037
theorem B8684509 : Blo 2141435 8684509 := bstep (se 3 (by rfl) ⟨1628345, by rfl⟩ : syracuseStep 8684509 = 3256691) B3256691
theorem B11579345 : Blo 2141435 11579345 := bstep (se 2 (by rfl) ⟨4342254, by rfl⟩ : syracuseStep 11579345 = 8684509) B8684509
theorem B7719563 : Blo 2141435 7719563 := bstep (se 1 (by rfl) ⟨5789672, by rfl⟩ : syracuseStep 7719563 = 11579345) B11579345
theorem B20585501 : Blo 2141435 20585501 := bstep (se 3 (by rfl) ⟨3859781, by rfl⟩ : syracuseStep 20585501 = 7719563) B7719563
theorem B13723667 : Blo 2141435 13723667 := bstep (se 1 (by rfl) ⟨10292750, by rfl⟩ : syracuseStep 13723667 = 20585501) B20585501
theorem B9149111 : Blo 2141435 9149111 := bstep (se 1 (by rfl) ⟨6861833, by rfl⟩ : syracuseStep 9149111 = 13723667) B13723667
theorem B6099407 : Blo 2141435 6099407 := bstep (se 1 (by rfl) ⟨4574555, by rfl⟩ : syracuseStep 6099407 = 9149111) B9149111
theorem B4066271 : Blo 2141435 4066271 := bstep (se 1 (by rfl) ⟨3049703, by rfl⟩ : syracuseStep 4066271 = 6099407) B6099407
theorem B2710847 : Blo 2141435 2710847 := bstep (se 1 (by rfl) ⟨2033135, by rfl⟩ : syracuseStep 2710847 = 4066271) B4066271
theorem B7228925 : Blo 2141435 7228925 := bstep (se 3 (by rfl) ⟨1355423, by rfl⟩ : syracuseStep 7228925 = 2710847) B2710847
theorem B4819283 : Blo 2141435 4819283 := bstep (se 1 (by rfl) ⟨3614462, by rfl⟩ : syracuseStep 4819283 = 7228925) B7228925
theorem B3212855 : Blo 2141435 3212855 := bstep (se 1 (by rfl) ⟨2409641, by rfl⟩ : syracuseStep 3212855 = 4819283) B4819283
theorem B2141903 : Blo 2141435 2141903 := bstep (se 1 (by rfl) ⟨1606427, by rfl⟩ : syracuseStep 2141903 = 3212855) B3212855
theorem B3212861 : Blo 2141435 3212861 := bbase (se 3 (by rfl) ⟨602411, by rfl⟩ : syracuseStep 3212861 = 1204823) (by norm_num)
theorem B2141907 : Blo 2141435 2141907 := bstep (se 1 (by rfl) ⟨1606430, by rfl⟩ : syracuseStep 2141907 = 3212861) B3212861
theorem B4819301 : Blo 2141435 4819301 := bbase (se 4 (by rfl) ⟨451809, by rfl⟩ : syracuseStep 4819301 = 903619) (by norm_num)
theorem B3212867 : Blo 2141435 3212867 := bstep (se 1 (by rfl) ⟨2409650, by rfl⟩ : syracuseStep 3212867 = 4819301) B4819301
theorem B2141911 : Blo 2141435 2141911 := bstep (se 1 (by rfl) ⟨1606433, by rfl⟩ : syracuseStep 2141911 = 3212867) B3212867
theorem B5421725 : Blo 2141435 5421725 := bbase (se 3 (by rfl) ⟨1016573, by rfl⟩ : syracuseStep 5421725 = 2033147) (by norm_num)
theorem B3614483 : Blo 2141435 3614483 := bstep (se 1 (by rfl) ⟨2710862, by rfl⟩ : syracuseStep 3614483 = 5421725) B5421725
theorem B2409655 : Blo 2141435 2409655 := bstep (se 1 (by rfl) ⟨1807241, by rfl⟩ : syracuseStep 2409655 = 3614483) B3614483
theorem B3212873 : Blo 2141435 3212873 := bstep (se 2 (by rfl) ⟨1204827, by rfl⟩ : syracuseStep 3212873 = 2409655) B2409655
theorem B2141915 : Blo 2141435 2141915 := bstep (se 1 (by rfl) ⟨1606436, by rfl⟩ : syracuseStep 2141915 = 3212873) B3212873
theorem B4066301 : Blo 2141435 4066301 := bbase (se 3 (by rfl) ⟨762431, by rfl⟩ : syracuseStep 4066301 = 1524863) (by norm_num)
theorem B10843469 : Blo 2141435 10843469 := bstep (se 3 (by rfl) ⟨2033150, by rfl⟩ : syracuseStep 10843469 = 4066301) B4066301
theorem B7228979 : Blo 2141435 7228979 := bstep (se 1 (by rfl) ⟨5421734, by rfl⟩ : syracuseStep 7228979 = 10843469) B10843469
theorem B4819319 : Blo 2141435 4819319 := bstep (se 1 (by rfl) ⟨3614489, by rfl⟩ : syracuseStep 4819319 = 7228979) B7228979
theorem B3212879 : Blo 2141435 3212879 := bstep (se 1 (by rfl) ⟨2409659, by rfl⟩ : syracuseStep 3212879 = 4819319) B4819319
theorem B2141919 : Blo 2141435 2141919 := bstep (se 1 (by rfl) ⟨1606439, by rfl⟩ : syracuseStep 2141919 = 3212879) B3212879
theorem B3212885 : Blo 2141435 3212885 := bbase (se 8 (by rfl) ⟨18825, by rfl⟩ : syracuseStep 3212885 = 37651) (by norm_num)
theorem B2141923 : Blo 2141435 2141923 := bstep (se 1 (by rfl) ⟨1606442, by rfl⟩ : syracuseStep 2141923 = 3212885) B3212885
theorem B2894869 : Blo 2141435 2894869 := bbase (se 6 (by rfl) ⟨67848, by rfl⟩ : syracuseStep 2894869 = 135697) (by norm_num)
theorem B3859825 : Blo 2141435 3859825 := bstep (se 2 (by rfl) ⟨1447434, by rfl⟩ : syracuseStep 3859825 = 2894869) B2894869
theorem B5146433 : Blo 2141435 5146433 := bstep (se 2 (by rfl) ⟨1929912, by rfl⟩ : syracuseStep 5146433 = 3859825) B3859825
theorem B3430955 : Blo 2141435 3430955 := bstep (se 1 (by rfl) ⟨2573216, by rfl⟩ : syracuseStep 3430955 = 5146433) B5146433
theorem B9149213 : Blo 2141435 9149213 := bstep (se 3 (by rfl) ⟨1715477, by rfl⟩ : syracuseStep 9149213 = 3430955) B3430955
theorem B6099475 : Blo 2141435 6099475 := bstep (se 1 (by rfl) ⟨4574606, by rfl⟩ : syracuseStep 6099475 = 9149213) B9149213
theorem B8132633 : Blo 2141435 8132633 := bstep (se 2 (by rfl) ⟨3049737, by rfl⟩ : syracuseStep 8132633 = 6099475) B6099475
theorem B5421755 : Blo 2141435 5421755 := bstep (se 1 (by rfl) ⟨4066316, by rfl⟩ : syracuseStep 5421755 = 8132633) B8132633
theorem B3614503 : Blo 2141435 3614503 := bstep (se 1 (by rfl) ⟨2710877, by rfl⟩ : syracuseStep 3614503 = 5421755) B5421755
theorem B4819337 : Blo 2141435 4819337 := bstep (se 2 (by rfl) ⟨1807251, by rfl⟩ : syracuseStep 4819337 = 3614503) B3614503
theorem B3212891 : Blo 2141435 3212891 := bstep (se 1 (by rfl) ⟨2409668, by rfl⟩ : syracuseStep 3212891 = 4819337) B4819337
theorem B2141927 : Blo 2141435 2141927 := bstep (se 1 (by rfl) ⟨1606445, by rfl⟩ : syracuseStep 2141927 = 3212891) B3212891
theorem B2409673 : Blo 2141435 2409673 := bbase (se 2 (by rfl) ⟨903627, by rfl⟩ : syracuseStep 2409673 = 1807255) (by norm_num)
theorem B3212897 : Blo 2141435 3212897 := bstep (se 2 (by rfl) ⟨1204836, by rfl⟩ : syracuseStep 3212897 = 2409673) B2409673
theorem B2141931 : Blo 2141435 2141931 := bstep (se 1 (by rfl) ⟨1606448, by rfl⟩ : syracuseStep 2141931 = 3212897) B3212897
theorem B18548149 : Blo 2141435 18548149 := bbase (se 5 (by rfl) ⟨869444, by rfl⟩ : syracuseStep 18548149 = 1738889) (by norm_num)
theorem B24730865 : Blo 2141435 24730865 := bstep (se 2 (by rfl) ⟨9274074, by rfl⟩ : syracuseStep 24730865 = 18548149) B18548149
theorem B16487243 : Blo 2141435 16487243 := bstep (se 1 (by rfl) ⟨12365432, by rfl⟩ : syracuseStep 16487243 = 24730865) B24730865
theorem B10991495 : Blo 2141435 10991495 := bstep (se 1 (by rfl) ⟨8243621, by rfl⟩ : syracuseStep 10991495 = 16487243) B16487243
theorem B29310653 : Blo 2141435 29310653 := bstep (se 3 (by rfl) ⟨5495747, by rfl⟩ : syracuseStep 29310653 = 10991495) B10991495
theorem B19540435 : Blo 2141435 19540435 := bstep (se 1 (by rfl) ⟨14655326, by rfl⟩ : syracuseStep 19540435 = 29310653) B29310653
theorem B26053913 : Blo 2141435 26053913 := bstep (se 2 (by rfl) ⟨9770217, by rfl⟩ : syracuseStep 26053913 = 19540435) B19540435
theorem B17369275 : Blo 2141435 17369275 := bstep (se 1 (by rfl) ⟨13026956, by rfl⟩ : syracuseStep 17369275 = 26053913) B26053913
theorem B23159033 : Blo 2141435 23159033 := bstep (se 2 (by rfl) ⟨8684637, by rfl⟩ : syracuseStep 23159033 = 17369275) B17369275
theorem B15439355 : Blo 2141435 15439355 := bstep (se 1 (by rfl) ⟨11579516, by rfl⟩ : syracuseStep 15439355 = 23159033) B23159033
theorem B10292903 : Blo 2141435 10292903 := bstep (se 1 (by rfl) ⟨7719677, by rfl⟩ : syracuseStep 10292903 = 15439355) B15439355
theorem B6861935 : Blo 2141435 6861935 := bstep (se 1 (by rfl) ⟨5146451, by rfl⟩ : syracuseStep 6861935 = 10292903) B10292903
theorem B18298493 : Blo 2141435 18298493 := bstep (se 3 (by rfl) ⟨3430967, by rfl⟩ : syracuseStep 18298493 = 6861935) B6861935
theorem B12198995 : Blo 2141435 12198995 := bstep (se 1 (by rfl) ⟨9149246, by rfl⟩ : syracuseStep 12198995 = 18298493) B18298493
theorem B8132663 : Blo 2141435 8132663 := bstep (se 1 (by rfl) ⟨6099497, by rfl⟩ : syracuseStep 8132663 = 12198995) B12198995
theorem B5421775 : Blo 2141435 5421775 := bstep (se 1 (by rfl) ⟨4066331, by rfl⟩ : syracuseStep 5421775 = 8132663) B8132663
theorem B7229033 : Blo 2141435 7229033 := bstep (se 2 (by rfl) ⟨2710887, by rfl⟩ : syracuseStep 7229033 = 5421775) B5421775
theorem B4819355 : Blo 2141435 4819355 := bstep (se 1 (by rfl) ⟨3614516, by rfl⟩ : syracuseStep 4819355 = 7229033) B7229033
theorem B3212903 : Blo 2141435 3212903 := bstep (se 1 (by rfl) ⟨2409677, by rfl⟩ : syracuseStep 3212903 = 4819355) B4819355
theorem B2141935 : Blo 2141435 2141935 := bstep (se 1 (by rfl) ⟨1606451, by rfl⟩ : syracuseStep 2141935 = 3212903) B3212903
theorem B3212909 : Blo 2141435 3212909 := bbase (se 3 (by rfl) ⟨602420, by rfl⟩ : syracuseStep 3212909 = 1204841) (by norm_num)
theorem B2141939 : Blo 2141435 2141939 := bstep (se 1 (by rfl) ⟨1606454, by rfl⟩ : syracuseStep 2141939 = 3212909) B3212909
theorem B4819373 : Blo 2141435 4819373 := bbase (se 3 (by rfl) ⟨903632, by rfl⟩ : syracuseStep 4819373 = 1807265) (by norm_num)
theorem B3212915 : Blo 2141435 3212915 := bstep (se 1 (by rfl) ⟨2409686, by rfl⟩ : syracuseStep 3212915 = 4819373) B4819373
theorem B2141943 : Blo 2141435 2141943 := bstep (se 1 (by rfl) ⟨1606457, by rfl⟩ : syracuseStep 2141943 = 3212915) B3212915
theorem B2287325 : Blo 2141435 2287325 := bbase (se 3 (by rfl) ⟨428873, by rfl⟩ : syracuseStep 2287325 = 857747) (by norm_num)
theorem B6099533 : Blo 2141435 6099533 := bstep (se 3 (by rfl) ⟨1143662, by rfl⟩ : syracuseStep 6099533 = 2287325) B2287325
theorem B4066355 : Blo 2141435 4066355 := bstep (se 1 (by rfl) ⟨3049766, by rfl⟩ : syracuseStep 4066355 = 6099533) B6099533
theorem B2710903 : Blo 2141435 2710903 := bstep (se 1 (by rfl) ⟨2033177, by rfl⟩ : syracuseStep 2710903 = 4066355) B4066355
theorem B3614537 : Blo 2141435 3614537 := bstep (se 2 (by rfl) ⟨1355451, by rfl⟩ : syracuseStep 3614537 = 2710903) B2710903
theorem B2409691 : Blo 2141435 2409691 := bstep (se 1 (by rfl) ⟨1807268, by rfl⟩ : syracuseStep 2409691 = 3614537) B3614537
theorem B3212921 : Blo 2141435 3212921 := bstep (se 2 (by rfl) ⟨1204845, by rfl⟩ : syracuseStep 3212921 = 2409691) B2409691
theorem B2141947 : Blo 2141435 2141947 := bstep (se 1 (by rfl) ⟨1606460, by rfl⟩ : syracuseStep 2141947 = 3212921) B3212921
theorem B5495789 : Blo 2141435 5495789 := bbase (se 3 (by rfl) ⟨1030460, by rfl⟩ : syracuseStep 5495789 = 2060921) (by norm_num)
theorem B3663859 : Blo 2141435 3663859 := bstep (se 1 (by rfl) ⟨2747894, by rfl⟩ : syracuseStep 3663859 = 5495789) B5495789
theorem B4885145 : Blo 2141435 4885145 := bstep (se 2 (by rfl) ⟨1831929, by rfl⟩ : syracuseStep 4885145 = 3663859) B3663859
theorem B3256763 : Blo 2141435 3256763 := bstep (se 1 (by rfl) ⟨2442572, by rfl⟩ : syracuseStep 3256763 = 4885145) B4885145
theorem B8684701 : Blo 2141435 8684701 := bstep (se 3 (by rfl) ⟨1628381, by rfl⟩ : syracuseStep 8684701 = 3256763) B3256763
theorem B46318405 : Blo 2141435 46318405 := bstep (se 4 (by rfl) ⟨4342350, by rfl⟩ : syracuseStep 46318405 = 8684701) B8684701
theorem B61757873 : Blo 2141435 61757873 := bstep (se 2 (by rfl) ⟨23159202, by rfl⟩ : syracuseStep 61757873 = 46318405) B46318405
theorem B41171915 : Blo 2141435 41171915 := bstep (se 1 (by rfl) ⟨30878936, by rfl⟩ : syracuseStep 41171915 = 61757873) B61757873
theorem B27447943 : Blo 2141435 27447943 := bstep (se 1 (by rfl) ⟨20585957, by rfl⟩ : syracuseStep 27447943 = 41171915) B41171915
theorem B36597257 : Blo 2141435 36597257 := bstep (se 2 (by rfl) ⟨13723971, by rfl⟩ : syracuseStep 36597257 = 27447943) B27447943
theorem B24398171 : Blo 2141435 24398171 := bstep (se 1 (by rfl) ⟨18298628, by rfl⟩ : syracuseStep 24398171 = 36597257) B36597257
theorem B16265447 : Blo 2141435 16265447 := bstep (se 1 (by rfl) ⟨12199085, by rfl⟩ : syracuseStep 16265447 = 24398171) B24398171
theorem B10843631 : Blo 2141435 10843631 := bstep (se 1 (by rfl) ⟨8132723, by rfl⟩ : syracuseStep 10843631 = 16265447) B16265447
theorem B7229087 : Blo 2141435 7229087 := bstep (se 1 (by rfl) ⟨5421815, by rfl⟩ : syracuseStep 7229087 = 10843631) B10843631
theorem B4819391 : Blo 2141435 4819391 := bstep (se 1 (by rfl) ⟨3614543, by rfl⟩ : syracuseStep 4819391 = 7229087) B7229087
theorem B3212927 : Blo 2141435 3212927 := bstep (se 1 (by rfl) ⟨2409695, by rfl⟩ : syracuseStep 3212927 = 4819391) B4819391
theorem B2141951 : Blo 2141435 2141951 := bstep (se 1 (by rfl) ⟨1606463, by rfl⟩ : syracuseStep 2141951 = 3212927) B3212927
theorem B3212933 : Blo 2141435 3212933 := bbase (se 4 (by rfl) ⟨301212, by rfl⟩ : syracuseStep 3212933 = 602425) (by norm_num)
theorem B2141955 : Blo 2141435 2141955 := bstep (se 1 (by rfl) ⟨1606466, by rfl⟩ : syracuseStep 2141955 = 3212933) B3212933
theorem B3614557 : Blo 2141435 3614557 := bbase (se 3 (by rfl) ⟨677729, by rfl⟩ : syracuseStep 3614557 = 1355459) (by norm_num)
theorem B4819409 : Blo 2141435 4819409 := bstep (se 2 (by rfl) ⟨1807278, by rfl⟩ : syracuseStep 4819409 = 3614557) B3614557
theorem B3212939 : Blo 2141435 3212939 := bstep (se 1 (by rfl) ⟨2409704, by rfl⟩ : syracuseStep 3212939 = 4819409) B4819409
theorem B2141959 : Blo 2141435 2141959 := bstep (se 1 (by rfl) ⟨1606469, by rfl⟩ : syracuseStep 2141959 = 3212939) B3212939
theorem B2409709 : Blo 2141435 2409709 := bbase (se 3 (by rfl) ⟨451820, by rfl⟩ : syracuseStep 2409709 = 903641) (by norm_num)
theorem B3212945 : Blo 2141435 3212945 := bstep (se 2 (by rfl) ⟨1204854, by rfl⟩ : syracuseStep 3212945 = 2409709) B2409709
theorem B2141963 : Blo 2141435 2141963 := bstep (se 1 (by rfl) ⟨1606472, by rfl⟩ : syracuseStep 2141963 = 3212945) B3212945
theorem B7229141 : Blo 2141435 7229141 := bbase (se 7 (by rfl) ⟨84716, by rfl⟩ : syracuseStep 7229141 = 169433) (by norm_num)
theorem B4819427 : Blo 2141435 4819427 := bstep (se 1 (by rfl) ⟨3614570, by rfl⟩ : syracuseStep 4819427 = 7229141) B7229141
theorem B3212951 : Blo 2141435 3212951 := bstep (se 1 (by rfl) ⟨2409713, by rfl⟩ : syracuseStep 3212951 = 4819427) B4819427
theorem B2141967 : Blo 2141435 2141967 := bstep (se 1 (by rfl) ⟨1606475, by rfl⟩ : syracuseStep 2141967 = 3212951) B3212951
theorem B3212957 : Blo 2141435 3212957 := bbase (se 3 (by rfl) ⟨602429, by rfl⟩ : syracuseStep 3212957 = 1204859) (by norm_num)
theorem B2141971 : Blo 2141435 2141971 := bstep (se 1 (by rfl) ⟨1606478, by rfl⟩ : syracuseStep 2141971 = 3212957) B3212957
theorem B4819445 : Blo 2141435 4819445 := bbase (se 5 (by rfl) ⟨225911, by rfl⟩ : syracuseStep 4819445 = 451823) (by norm_num)
theorem B3212963 : Blo 2141435 3212963 := bstep (se 1 (by rfl) ⟨2409722, by rfl⟩ : syracuseStep 3212963 = 4819445) B4819445
theorem B2141975 : Blo 2141435 2141975 := bstep (se 1 (by rfl) ⟨1606481, by rfl⟩ : syracuseStep 2141975 = 3212963) B3212963
theorem B5495861 : Blo 2141435 5495861 := bbase (se 5 (by rfl) ⟨257618, by rfl⟩ : syracuseStep 5495861 = 515237) (by norm_num)
theorem B14655629 : Blo 2141435 14655629 := bstep (se 3 (by rfl) ⟨2747930, by rfl⟩ : syracuseStep 14655629 = 5495861) B5495861
theorem B9770419 : Blo 2141435 9770419 := bstep (se 1 (by rfl) ⟨7327814, by rfl⟩ : syracuseStep 9770419 = 14655629) B14655629
theorem B13027225 : Blo 2141435 13027225 := bstep (se 2 (by rfl) ⟨4885209, by rfl⟩ : syracuseStep 13027225 = 9770419) B9770419
theorem B17369633 : Blo 2141435 17369633 := bstep (se 2 (by rfl) ⟨6513612, by rfl⟩ : syracuseStep 17369633 = 13027225) B13027225
theorem B11579755 : Blo 2141435 11579755 := bstep (se 1 (by rfl) ⟨8684816, by rfl⟩ : syracuseStep 11579755 = 17369633) B17369633
theorem B15439673 : Blo 2141435 15439673 := bstep (se 2 (by rfl) ⟨5789877, by rfl⟩ : syracuseStep 15439673 = 11579755) B11579755
theorem B41172461 : Blo 2141435 41172461 := bstep (se 3 (by rfl) ⟨7719836, by rfl⟩ : syracuseStep 41172461 = 15439673) B15439673
theorem B27448307 : Blo 2141435 27448307 := bstep (se 1 (by rfl) ⟨20586230, by rfl⟩ : syracuseStep 27448307 = 41172461) B41172461
theorem B18298871 : Blo 2141435 18298871 := bstep (se 1 (by rfl) ⟨13724153, by rfl⟩ : syracuseStep 18298871 = 27448307) B27448307
theorem B12199247 : Blo 2141435 12199247 := bstep (se 1 (by rfl) ⟨9149435, by rfl⟩ : syracuseStep 12199247 = 18298871) B18298871
theorem B8132831 : Blo 2141435 8132831 := bstep (se 1 (by rfl) ⟨6099623, by rfl⟩ : syracuseStep 8132831 = 12199247) B12199247
theorem B5421887 : Blo 2141435 5421887 := bstep (se 1 (by rfl) ⟨4066415, by rfl⟩ : syracuseStep 5421887 = 8132831) B8132831
theorem B3614591 : Blo 2141435 3614591 := bstep (se 1 (by rfl) ⟨2710943, by rfl⟩ : syracuseStep 3614591 = 5421887) B5421887
theorem B2409727 : Blo 2141435 2409727 := bstep (se 1 (by rfl) ⟨1807295, by rfl⟩ : syracuseStep 2409727 = 3614591) B3614591
theorem B3212969 : Blo 2141435 3212969 := bstep (se 2 (by rfl) ⟨1204863, by rfl⟩ : syracuseStep 3212969 = 2409727) B2409727
theorem B2141979 : Blo 2141435 2141979 := bstep (se 1 (by rfl) ⟨1606484, by rfl⟩ : syracuseStep 2141979 = 3212969) B3212969
theorem B3431045 : Blo 2141435 3431045 := bbase (se 4 (by rfl) ⟨321660, by rfl⟩ : syracuseStep 3431045 = 643321) (by norm_num)
theorem B2287363 : Blo 2141435 2287363 := bstep (se 1 (by rfl) ⟨1715522, by rfl⟩ : syracuseStep 2287363 = 3431045) B3431045
theorem B3049817 : Blo 2141435 3049817 := bstep (se 2 (by rfl) ⟨1143681, by rfl⟩ : syracuseStep 3049817 = 2287363) B2287363
theorem B8132845 : Blo 2141435 8132845 := bstep (se 3 (by rfl) ⟨1524908, by rfl⟩ : syracuseStep 8132845 = 3049817) B3049817
theorem B10843793 : Blo 2141435 10843793 := bstep (se 2 (by rfl) ⟨4066422, by rfl⟩ : syracuseStep 10843793 = 8132845) B8132845
theorem B7229195 : Blo 2141435 7229195 := bstep (se 1 (by rfl) ⟨5421896, by rfl⟩ : syracuseStep 7229195 = 10843793) B10843793
theorem B4819463 : Blo 2141435 4819463 := bstep (se 1 (by rfl) ⟨3614597, by rfl⟩ : syracuseStep 4819463 = 7229195) B7229195
theorem B3212975 : Blo 2141435 3212975 := bstep (se 1 (by rfl) ⟨2409731, by rfl⟩ : syracuseStep 3212975 = 4819463) B4819463
theorem B2141983 : Blo 2141435 2141983 := bstep (se 1 (by rfl) ⟨1606487, by rfl⟩ : syracuseStep 2141983 = 3212975) B3212975
theorem B3212981 : Blo 2141435 3212981 := bbase (se 5 (by rfl) ⟨150608, by rfl⟩ : syracuseStep 3212981 = 301217) (by norm_num)
theorem B2141987 : Blo 2141435 2141987 := bstep (se 1 (by rfl) ⟨1606490, by rfl⟩ : syracuseStep 2141987 = 3212981) B3212981
theorem B5421917 : Blo 2141435 5421917 := bbase (se 3 (by rfl) ⟨1016609, by rfl⟩ : syracuseStep 5421917 = 2033219) (by norm_num)
theorem B3614611 : Blo 2141435 3614611 := bstep (se 1 (by rfl) ⟨2710958, by rfl⟩ : syracuseStep 3614611 = 5421917) B5421917
theorem B4819481 : Blo 2141435 4819481 := bstep (se 2 (by rfl) ⟨1807305, by rfl⟩ : syracuseStep 4819481 = 3614611) B3614611
theorem B3212987 : Blo 2141435 3212987 := bstep (se 1 (by rfl) ⟨2409740, by rfl⟩ : syracuseStep 3212987 = 4819481) B4819481
theorem B2141991 : Blo 2141435 2141991 := bstep (se 1 (by rfl) ⟨1606493, by rfl⟩ : syracuseStep 2141991 = 3212987) B3212987
theorem B2409745 : Blo 2141435 2409745 := bbase (se 2 (by rfl) ⟨903654, by rfl⟩ : syracuseStep 2409745 = 1807309) (by norm_num)
theorem B3212993 : Blo 2141435 3212993 := bstep (se 2 (by rfl) ⟨1204872, by rfl⟩ : syracuseStep 3212993 = 2409745) B2409745
theorem B2141995 : Blo 2141435 2141995 := bstep (se 1 (by rfl) ⟨1606496, by rfl⟩ : syracuseStep 2141995 = 3212993) B3212993
theorem B4066453 : Blo 2141435 4066453 := bbase (se 6 (by rfl) ⟨95307, by rfl⟩ : syracuseStep 4066453 = 190615) (by norm_num)
theorem B5421937 : Blo 2141435 5421937 := bstep (se 2 (by rfl) ⟨2033226, by rfl⟩ : syracuseStep 5421937 = 4066453) B4066453
theorem B7229249 : Blo 2141435 7229249 := bstep (se 2 (by rfl) ⟨2710968, by rfl⟩ : syracuseStep 7229249 = 5421937) B5421937
theorem B4819499 : Blo 2141435 4819499 := bstep (se 1 (by rfl) ⟨3614624, by rfl⟩ : syracuseStep 4819499 = 7229249) B7229249
theorem B3212999 : Blo 2141435 3212999 := bstep (se 1 (by rfl) ⟨2409749, by rfl⟩ : syracuseStep 3212999 = 4819499) B4819499
theorem B2141999 : Blo 2141435 2141999 := bstep (se 1 (by rfl) ⟨1606499, by rfl⟩ : syracuseStep 2141999 = 3212999) B3212999
theorem B3213005 : Blo 2141435 3213005 := bbase (se 3 (by rfl) ⟨602438, by rfl⟩ : syracuseStep 3213005 = 1204877) (by norm_num)
theorem B2142003 : Blo 2141435 2142003 := bstep (se 1 (by rfl) ⟨1606502, by rfl⟩ : syracuseStep 2142003 = 3213005) B3213005
theorem B4819517 : Blo 2141435 4819517 := bbase (se 3 (by rfl) ⟨903659, by rfl⟩ : syracuseStep 4819517 = 1807319) (by norm_num)
theorem B3213011 : Blo 2141435 3213011 := bstep (se 1 (by rfl) ⟨2409758, by rfl⟩ : syracuseStep 3213011 = 4819517) B4819517
theorem B2142007 : Blo 2141435 2142007 := bstep (se 1 (by rfl) ⟨1606505, by rfl⟩ : syracuseStep 2142007 = 3213011) B3213011
theorem B3614645 : Blo 2141435 3614645 := bbase (se 5 (by rfl) ⟨169436, by rfl⟩ : syracuseStep 3614645 = 338873) (by norm_num)
theorem B2409763 : Blo 2141435 2409763 := bstep (se 1 (by rfl) ⟨1807322, by rfl⟩ : syracuseStep 2409763 = 3614645) B3614645
theorem B3213017 : Blo 2141435 3213017 := bstep (se 2 (by rfl) ⟨1204881, by rfl⟩ : syracuseStep 3213017 = 2409763) B2409763
theorem B2142011 : Blo 2141435 2142011 := bstep (se 1 (by rfl) ⟨1606508, by rfl⟩ : syracuseStep 2142011 = 3213017) B3213017
theorem B2287397 : Blo 2141435 2287397 := bbase (se 4 (by rfl) ⟨214443, by rfl⟩ : syracuseStep 2287397 = 428887) (by norm_num)
theorem B6099725 : Blo 2141435 6099725 := bstep (se 3 (by rfl) ⟨1143698, by rfl⟩ : syracuseStep 6099725 = 2287397) B2287397
theorem B16265933 : Blo 2141435 16265933 := bstep (se 3 (by rfl) ⟨3049862, by rfl⟩ : syracuseStep 16265933 = 6099725) B6099725
theorem B10843955 : Blo 2141435 10843955 := bstep (se 1 (by rfl) ⟨8132966, by rfl⟩ : syracuseStep 10843955 = 16265933) B16265933
theorem B7229303 : Blo 2141435 7229303 := bstep (se 1 (by rfl) ⟨5421977, by rfl⟩ : syracuseStep 7229303 = 10843955) B10843955
theorem B4819535 : Blo 2141435 4819535 := bstep (se 1 (by rfl) ⟨3614651, by rfl⟩ : syracuseStep 4819535 = 7229303) B7229303
theorem B3213023 : Blo 2141435 3213023 := bstep (se 1 (by rfl) ⟨2409767, by rfl⟩ : syracuseStep 3213023 = 4819535) B4819535
theorem B2142015 : Blo 2141435 2142015 := bstep (se 1 (by rfl) ⟨1606511, by rfl⟩ : syracuseStep 2142015 = 3213023) B3213023
theorem B3213029 : Blo 2141435 3213029 := bbase (se 4 (by rfl) ⟨301221, by rfl⟩ : syracuseStep 3213029 = 602443) (by norm_num)
theorem B2142019 : Blo 2141435 2142019 := bstep (se 1 (by rfl) ⟨1606514, by rfl⟩ : syracuseStep 2142019 = 3213029) B3213029
theorem B6099749 : Blo 2141435 6099749 := bbase (se 4 (by rfl) ⟨571851, by rfl⟩ : syracuseStep 6099749 = 1143703) (by norm_num)
theorem B4066499 : Blo 2141435 4066499 := bstep (se 1 (by rfl) ⟨3049874, by rfl⟩ : syracuseStep 4066499 = 6099749) B6099749
theorem B2710999 : Blo 2141435 2710999 := bstep (se 1 (by rfl) ⟨2033249, by rfl⟩ : syracuseStep 2710999 = 4066499) B4066499
theorem B3614665 : Blo 2141435 3614665 := bstep (se 2 (by rfl) ⟨1355499, by rfl⟩ : syracuseStep 3614665 = 2710999) B2710999
theorem B4819553 : Blo 2141435 4819553 := bstep (se 2 (by rfl) ⟨1807332, by rfl⟩ : syracuseStep 4819553 = 3614665) B3614665
theorem B3213035 : Blo 2141435 3213035 := bstep (se 1 (by rfl) ⟨2409776, by rfl⟩ : syracuseStep 3213035 = 4819553) B4819553
theorem B2142023 : Blo 2141435 2142023 := bstep (se 1 (by rfl) ⟨1606517, by rfl⟩ : syracuseStep 2142023 = 3213035) B3213035
theorem B2409781 : Blo 2141435 2409781 := bbase (se 5 (by rfl) ⟨112958, by rfl⟩ : syracuseStep 2409781 = 225917) (by norm_num)
theorem B3213041 : Blo 2141435 3213041 := bstep (se 2 (by rfl) ⟨1204890, by rfl⟩ : syracuseStep 3213041 = 2409781) B2409781
theorem B2142027 : Blo 2141435 2142027 := bstep (se 1 (by rfl) ⟨1606520, by rfl⟩ : syracuseStep 2142027 = 3213041) B3213041
theorem B2711009 : Blo 2141435 2711009 := bbase (se 2 (by rfl) ⟨1016628, by rfl⟩ : syracuseStep 2711009 = 2033257) (by norm_num)
theorem B7229357 : Blo 2141435 7229357 := bstep (se 3 (by rfl) ⟨1355504, by rfl⟩ : syracuseStep 7229357 = 2711009) B2711009
theorem B4819571 : Blo 2141435 4819571 := bstep (se 1 (by rfl) ⟨3614678, by rfl⟩ : syracuseStep 4819571 = 7229357) B7229357
theorem B3213047 : Blo 2141435 3213047 := bstep (se 1 (by rfl) ⟨2409785, by rfl⟩ : syracuseStep 3213047 = 4819571) B4819571
theorem B2142031 : Blo 2141435 2142031 := bstep (se 1 (by rfl) ⟨1606523, by rfl⟩ : syracuseStep 2142031 = 3213047) B3213047
theorem B3213053 : Blo 2141435 3213053 := bbase (se 3 (by rfl) ⟨602447, by rfl⟩ : syracuseStep 3213053 = 1204895) (by norm_num)
theorem B2142035 : Blo 2141435 2142035 := bstep (se 1 (by rfl) ⟨1606526, by rfl⟩ : syracuseStep 2142035 = 3213053) B3213053
theorem B4819589 : Blo 2141435 4819589 := bbase (se 4 (by rfl) ⟨451836, by rfl⟩ : syracuseStep 4819589 = 903673) (by norm_num)
theorem B3213059 : Blo 2141435 3213059 := bstep (se 1 (by rfl) ⟨2409794, by rfl⟩ : syracuseStep 3213059 = 4819589) B4819589
theorem B2142039 : Blo 2141435 2142039 := bstep (se 1 (by rfl) ⟨1606529, by rfl⟩ : syracuseStep 2142039 = 3213059) B3213059
theorem B7720069 : Blo 2141435 7720069 := bbase (se 4 (by rfl) ⟨723756, by rfl⟩ : syracuseStep 7720069 = 1447513) (by norm_num)
theorem B10293425 : Blo 2141435 10293425 := bstep (se 2 (by rfl) ⟨3860034, by rfl⟩ : syracuseStep 10293425 = 7720069) B7720069
theorem B6862283 : Blo 2141435 6862283 := bstep (se 1 (by rfl) ⟨5146712, by rfl⟩ : syracuseStep 6862283 = 10293425) B10293425
theorem B4574855 : Blo 2141435 4574855 := bstep (se 1 (by rfl) ⟨3431141, by rfl⟩ : syracuseStep 4574855 = 6862283) B6862283
theorem B3049903 : Blo 2141435 3049903 := bstep (se 1 (by rfl) ⟨2287427, by rfl⟩ : syracuseStep 3049903 = 4574855) B4574855
theorem B4066537 : Blo 2141435 4066537 := bstep (se 2 (by rfl) ⟨1524951, by rfl⟩ : syracuseStep 4066537 = 3049903) B3049903
theorem B5422049 : Blo 2141435 5422049 := bstep (se 2 (by rfl) ⟨2033268, by rfl⟩ : syracuseStep 5422049 = 4066537) B4066537
theorem B3614699 : Blo 2141435 3614699 := bstep (se 1 (by rfl) ⟨2711024, by rfl⟩ : syracuseStep 3614699 = 5422049) B5422049
theorem B2409799 : Blo 2141435 2409799 := bstep (se 1 (by rfl) ⟨1807349, by rfl⟩ : syracuseStep 2409799 = 3614699) B3614699
theorem B3213065 : Blo 2141435 3213065 := bstep (se 2 (by rfl) ⟨1204899, by rfl⟩ : syracuseStep 3213065 = 2409799) B2409799
theorem B2142043 : Blo 2141435 2142043 := bstep (se 1 (by rfl) ⟨1606532, by rfl⟩ : syracuseStep 2142043 = 3213065) B3213065
theorem B10844117 : Blo 2141435 10844117 := bbase (se 7 (by rfl) ⟨127079, by rfl⟩ : syracuseStep 10844117 = 254159) (by norm_num)
theorem B7229411 : Blo 2141435 7229411 := bstep (se 1 (by rfl) ⟨5422058, by rfl⟩ : syracuseStep 7229411 = 10844117) B10844117
theorem B4819607 : Blo 2141435 4819607 := bstep (se 1 (by rfl) ⟨3614705, by rfl⟩ : syracuseStep 4819607 = 7229411) B7229411
theorem B3213071 : Blo 2141435 3213071 := bstep (se 1 (by rfl) ⟨2409803, by rfl⟩ : syracuseStep 3213071 = 4819607) B4819607
theorem B2142047 : Blo 2141435 2142047 := bstep (se 1 (by rfl) ⟨1606535, by rfl⟩ : syracuseStep 2142047 = 3213071) B3213071
theorem B3213077 : Blo 2141435 3213077 := bbase (se 6 (by rfl) ⟨75306, by rfl⟩ : syracuseStep 3213077 = 150613) (by norm_num)
theorem B2142051 : Blo 2141435 2142051 := bstep (se 1 (by rfl) ⟨1606538, by rfl⟩ : syracuseStep 2142051 = 3213077) B3213077
theorem B13205429 : Blo 2141435 13205429 := bbase (se 5 (by rfl) ⟨619004, by rfl⟩ : syracuseStep 13205429 = 1238009) (by norm_num)
theorem B8803619 : Blo 2141435 8803619 := bstep (se 1 (by rfl) ⟨6602714, by rfl⟩ : syracuseStep 8803619 = 13205429) B13205429
theorem B5869079 : Blo 2141435 5869079 := bstep (se 1 (by rfl) ⟨4401809, by rfl⟩ : syracuseStep 5869079 = 8803619) B8803619
theorem B3912719 : Blo 2141435 3912719 := bstep (se 1 (by rfl) ⟨2934539, by rfl⟩ : syracuseStep 3912719 = 5869079) B5869079
theorem B10433917 : Blo 2141435 10433917 := bstep (se 3 (by rfl) ⟨1956359, by rfl⟩ : syracuseStep 10433917 = 3912719) B3912719
theorem B55647557 : Blo 2141435 55647557 := bstep (se 4 (by rfl) ⟨5216958, by rfl⟩ : syracuseStep 55647557 = 10433917) B10433917
theorem B37098371 : Blo 2141435 37098371 := bstep (se 1 (by rfl) ⟨27823778, by rfl⟩ : syracuseStep 37098371 = 55647557) B55647557
theorem B98928989 : Blo 2141435 98928989 := bstep (se 3 (by rfl) ⟨18549185, by rfl⟩ : syracuseStep 98928989 = 37098371) B37098371
theorem B65952659 : Blo 2141435 65952659 := bstep (se 1 (by rfl) ⟨49464494, by rfl⟩ : syracuseStep 65952659 = 98928989) B98928989
theorem B43968439 : Blo 2141435 43968439 := bstep (se 1 (by rfl) ⟨32976329, by rfl⟩ : syracuseStep 43968439 = 65952659) B65952659
theorem B234498341 : Blo 2141435 234498341 := bstep (se 4 (by rfl) ⟨21984219, by rfl⟩ : syracuseStep 234498341 = 43968439) B43968439
theorem B156332227 : Blo 2141435 156332227 := bstep (se 1 (by rfl) ⟨117249170, by rfl⟩ : syracuseStep 156332227 = 234498341) B234498341
theorem B208442969 : Blo 2141435 208442969 := bstep (se 2 (by rfl) ⟨78166113, by rfl⟩ : syracuseStep 208442969 = 156332227) B156332227
theorem B138961979 : Blo 2141435 138961979 := bstep (se 1 (by rfl) ⟨104221484, by rfl⟩ : syracuseStep 138961979 = 208442969) B208442969
theorem B92641319 : Blo 2141435 92641319 := bstep (se 1 (by rfl) ⟨69480989, by rfl⟩ : syracuseStep 92641319 = 138961979) B138961979
theorem B61760879 : Blo 2141435 61760879 := bstep (se 1 (by rfl) ⟨46320659, by rfl⟩ : syracuseStep 61760879 = 92641319) B92641319
theorem B41173919 : Blo 2141435 41173919 := bstep (se 1 (by rfl) ⟨30880439, by rfl⟩ : syracuseStep 41173919 = 61760879) B61760879
theorem B27449279 : Blo 2141435 27449279 := bstep (se 1 (by rfl) ⟨20586959, by rfl⟩ : syracuseStep 27449279 = 41173919) B41173919
theorem B18299519 : Blo 2141435 18299519 := bstep (se 1 (by rfl) ⟨13724639, by rfl⟩ : syracuseStep 18299519 = 27449279) B27449279
theorem B12199679 : Blo 2141435 12199679 := bstep (se 1 (by rfl) ⟨9149759, by rfl⟩ : syracuseStep 12199679 = 18299519) B18299519
theorem B8133119 : Blo 2141435 8133119 := bstep (se 1 (by rfl) ⟨6099839, by rfl⟩ : syracuseStep 8133119 = 12199679) B12199679
theorem B5422079 : Blo 2141435 5422079 := bstep (se 1 (by rfl) ⟨4066559, by rfl⟩ : syracuseStep 5422079 = 8133119) B8133119
theorem B3614719 : Blo 2141435 3614719 := bstep (se 1 (by rfl) ⟨2711039, by rfl⟩ : syracuseStep 3614719 = 5422079) B5422079
theorem B4819625 : Blo 2141435 4819625 := bstep (se 2 (by rfl) ⟨1807359, by rfl⟩ : syracuseStep 4819625 = 3614719) B3614719
theorem B3213083 : Blo 2141435 3213083 := bstep (se 1 (by rfl) ⟨2409812, by rfl⟩ : syracuseStep 3213083 = 4819625) B4819625
theorem B2142055 : Blo 2141435 2142055 := bstep (se 1 (by rfl) ⟨1606541, by rfl⟩ : syracuseStep 2142055 = 3213083) B3213083
theorem B2409817 : Blo 2141435 2409817 := bbase (se 2 (by rfl) ⟨903681, by rfl⟩ : syracuseStep 2409817 = 1807363) (by norm_num)
theorem B3213089 : Blo 2141435 3213089 := bstep (se 2 (by rfl) ⟨1204908, by rfl⟩ : syracuseStep 3213089 = 2409817) B2409817
theorem B2142059 : Blo 2141435 2142059 := bstep (se 1 (by rfl) ⟨1606544, by rfl⟩ : syracuseStep 2142059 = 3213089) B3213089
theorem B3431173 : Blo 2141435 3431173 := bbase (se 4 (by rfl) ⟨321672, by rfl⟩ : syracuseStep 3431173 = 643345) (by norm_num)
theorem B4574897 : Blo 2141435 4574897 := bstep (se 2 (by rfl) ⟨1715586, by rfl⟩ : syracuseStep 4574897 = 3431173) B3431173
theorem B3049931 : Blo 2141435 3049931 := bstep (se 1 (by rfl) ⟨2287448, by rfl⟩ : syracuseStep 3049931 = 4574897) B4574897
theorem B8133149 : Blo 2141435 8133149 := bstep (se 3 (by rfl) ⟨1524965, by rfl⟩ : syracuseStep 8133149 = 3049931) B3049931
theorem B5422099 : Blo 2141435 5422099 := bstep (se 1 (by rfl) ⟨4066574, by rfl⟩ : syracuseStep 5422099 = 8133149) B8133149
theorem B7229465 : Blo 2141435 7229465 := bstep (se 2 (by rfl) ⟨2711049, by rfl⟩ : syracuseStep 7229465 = 5422099) B5422099
theorem B4819643 : Blo 2141435 4819643 := bstep (se 1 (by rfl) ⟨3614732, by rfl⟩ : syracuseStep 4819643 = 7229465) B7229465
theorem B3213095 : Blo 2141435 3213095 := bstep (se 1 (by rfl) ⟨2409821, by rfl⟩ : syracuseStep 3213095 = 4819643) B4819643
theorem B2142063 : Blo 2141435 2142063 := bstep (se 1 (by rfl) ⟨1606547, by rfl⟩ : syracuseStep 2142063 = 3213095) B3213095
theorem B3213101 : Blo 2141435 3213101 := bbase (se 3 (by rfl) ⟨602456, by rfl⟩ : syracuseStep 3213101 = 1204913) (by norm_num)
theorem B2142067 : Blo 2141435 2142067 := bstep (se 1 (by rfl) ⟨1606550, by rfl⟩ : syracuseStep 2142067 = 3213101) B3213101
theorem B4819661 : Blo 2141435 4819661 := bbase (se 3 (by rfl) ⟨903686, by rfl⟩ : syracuseStep 4819661 = 1807373) (by norm_num)
theorem B3213107 : Blo 2141435 3213107 := bstep (se 1 (by rfl) ⟨2409830, by rfl⟩ : syracuseStep 3213107 = 4819661) B4819661
theorem B2142071 : Blo 2141435 2142071 := bstep (se 1 (by rfl) ⟨1606553, by rfl⟩ : syracuseStep 2142071 = 3213107) B3213107
theorem B2711065 : Blo 2141435 2711065 := bbase (se 2 (by rfl) ⟨1016649, by rfl⟩ : syracuseStep 2711065 = 2033299) (by norm_num)
theorem B3614753 : Blo 2141435 3614753 := bstep (se 2 (by rfl) ⟨1355532, by rfl⟩ : syracuseStep 3614753 = 2711065) B2711065
theorem B2409835 : Blo 2141435 2409835 := bstep (se 1 (by rfl) ⟨1807376, by rfl⟩ : syracuseStep 2409835 = 3614753) B3614753
theorem B3213113 : Blo 2141435 3213113 := bstep (se 2 (by rfl) ⟨1204917, by rfl⟩ : syracuseStep 3213113 = 2409835) B2409835
theorem B2142075 : Blo 2141435 2142075 := bstep (se 1 (by rfl) ⟨1606556, by rfl⟩ : syracuseStep 2142075 = 3213113) B3213113
theorem B9149861 : Blo 2141435 9149861 := bbase (se 4 (by rfl) ⟨857799, by rfl⟩ : syracuseStep 9149861 = 1715599) (by norm_num)
theorem B24399629 : Blo 2141435 24399629 := bstep (se 3 (by rfl) ⟨4574930, by rfl⟩ : syracuseStep 24399629 = 9149861) B9149861
theorem B16266419 : Blo 2141435 16266419 := bstep (se 1 (by rfl) ⟨12199814, by rfl⟩ : syracuseStep 16266419 = 24399629) B24399629
theorem B10844279 : Blo 2141435 10844279 := bstep (se 1 (by rfl) ⟨8133209, by rfl⟩ : syracuseStep 10844279 = 16266419) B16266419
theorem B7229519 : Blo 2141435 7229519 := bstep (se 1 (by rfl) ⟨5422139, by rfl⟩ : syracuseStep 7229519 = 10844279) B10844279
theorem B4819679 : Blo 2141435 4819679 := bstep (se 1 (by rfl) ⟨3614759, by rfl⟩ : syracuseStep 4819679 = 7229519) B7229519
theorem B3213119 : Blo 2141435 3213119 := bstep (se 1 (by rfl) ⟨2409839, by rfl⟩ : syracuseStep 3213119 = 4819679) B4819679
theorem B2142079 : Blo 2141435 2142079 := bstep (se 1 (by rfl) ⟨1606559, by rfl⟩ : syracuseStep 2142079 = 3213119) B3213119
theorem B3213125 : Blo 2141435 3213125 := bbase (se 4 (by rfl) ⟨301230, by rfl⟩ : syracuseStep 3213125 = 602461) (by norm_num)
theorem B2142083 : Blo 2141435 2142083 := bstep (se 1 (by rfl) ⟨1606562, by rfl⟩ : syracuseStep 2142083 = 3213125) B3213125
theorem B3614773 : Blo 2141435 3614773 := bbase (se 5 (by rfl) ⟨169442, by rfl⟩ : syracuseStep 3614773 = 338885) (by norm_num)
theorem B4819697 : Blo 2141435 4819697 := bstep (se 2 (by rfl) ⟨1807386, by rfl⟩ : syracuseStep 4819697 = 3614773) B3614773
theorem B3213131 : Blo 2141435 3213131 := bstep (se 1 (by rfl) ⟨2409848, by rfl⟩ : syracuseStep 3213131 = 4819697) B4819697
theorem B2142087 : Blo 2141435 2142087 := bstep (se 1 (by rfl) ⟨1606565, by rfl⟩ : syracuseStep 2142087 = 3213131) B3213131
theorem B2409853 : Blo 2141435 2409853 := bbase (se 3 (by rfl) ⟨451847, by rfl⟩ : syracuseStep 2409853 = 903695) (by norm_num)
theorem B3213137 : Blo 2141435 3213137 := bstep (se 2 (by rfl) ⟨1204926, by rfl⟩ : syracuseStep 3213137 = 2409853) B2409853
theorem B2142091 : Blo 2141435 2142091 := bstep (se 1 (by rfl) ⟨1606568, by rfl⟩ : syracuseStep 2142091 = 3213137) B3213137
theorem B7229573 : Blo 2141435 7229573 := bbase (se 4 (by rfl) ⟨677772, by rfl⟩ : syracuseStep 7229573 = 1355545) (by norm_num)
theorem B4819715 : Blo 2141435 4819715 := bstep (se 1 (by rfl) ⟨3614786, by rfl⟩ : syracuseStep 4819715 = 7229573) B7229573
theorem B3213143 : Blo 2141435 3213143 := bstep (se 1 (by rfl) ⟨2409857, by rfl⟩ : syracuseStep 3213143 = 4819715) B4819715
theorem B2142095 : Blo 2141435 2142095 := bstep (se 1 (by rfl) ⟨1606571, by rfl⟩ : syracuseStep 2142095 = 3213143) B3213143
theorem B3213149 : Blo 2141435 3213149 := bbase (se 3 (by rfl) ⟨602465, by rfl⟩ : syracuseStep 3213149 = 1204931) (by norm_num)
theorem B2142099 : Blo 2141435 2142099 := bstep (se 1 (by rfl) ⟨1606574, by rfl⟩ : syracuseStep 2142099 = 3213149) B3213149
theorem B4819733 : Blo 2141435 4819733 := bbase (se 6 (by rfl) ⟨112962, by rfl⟩ : syracuseStep 4819733 = 225925) (by norm_num)
theorem B3213155 : Blo 2141435 3213155 := bstep (se 1 (by rfl) ⟨2409866, by rfl⟩ : syracuseStep 3213155 = 4819733) B4819733
theorem B2142103 : Blo 2141435 2142103 := bstep (se 1 (by rfl) ⟨1606577, by rfl⟩ : syracuseStep 2142103 = 3213155) B3213155
theorem B8133317 : Blo 2141435 8133317 := bbase (se 4 (by rfl) ⟨762498, by rfl⟩ : syracuseStep 8133317 = 1524997) (by norm_num)
theorem B5422211 : Blo 2141435 5422211 := bstep (se 1 (by rfl) ⟨4066658, by rfl⟩ : syracuseStep 5422211 = 8133317) B8133317
theorem B3614807 : Blo 2141435 3614807 := bstep (se 1 (by rfl) ⟨2711105, by rfl⟩ : syracuseStep 3614807 = 5422211) B5422211
theorem B2409871 : Blo 2141435 2409871 := bstep (se 1 (by rfl) ⟨1807403, by rfl⟩ : syracuseStep 2409871 = 3614807) B3614807
theorem B3213161 : Blo 2141435 3213161 := bstep (se 2 (by rfl) ⟨1204935, by rfl⟩ : syracuseStep 3213161 = 2409871) B2409871
theorem B2142107 : Blo 2141435 2142107 := bstep (se 1 (by rfl) ⟨1606580, by rfl⟩ : syracuseStep 2142107 = 3213161) B3213161
theorem B10293749 : Blo 2141435 10293749 := bbase (se 5 (by rfl) ⟨482519, by rfl⟩ : syracuseStep 10293749 = 965039) (by norm_num)
theorem B6862499 : Blo 2141435 6862499 := bstep (se 1 (by rfl) ⟨5146874, by rfl⟩ : syracuseStep 6862499 = 10293749) B10293749
theorem B4574999 : Blo 2141435 4574999 := bstep (se 1 (by rfl) ⟨3431249, by rfl⟩ : syracuseStep 4574999 = 6862499) B6862499
theorem B12199997 : Blo 2141435 12199997 := bstep (se 3 (by rfl) ⟨2287499, by rfl⟩ : syracuseStep 12199997 = 4574999) B4574999
theorem B8133331 : Blo 2141435 8133331 := bstep (se 1 (by rfl) ⟨6099998, by rfl⟩ : syracuseStep 8133331 = 12199997) B12199997
theorem B10844441 : Blo 2141435 10844441 := bstep (se 2 (by rfl) ⟨4066665, by rfl⟩ : syracuseStep 10844441 = 8133331) B8133331
theorem B7229627 : Blo 2141435 7229627 := bstep (se 1 (by rfl) ⟨5422220, by rfl⟩ : syracuseStep 7229627 = 10844441) B10844441
theorem B4819751 : Blo 2141435 4819751 := bstep (se 1 (by rfl) ⟨3614813, by rfl⟩ : syracuseStep 4819751 = 7229627) B7229627
theorem B3213167 : Blo 2141435 3213167 := bstep (se 1 (by rfl) ⟨2409875, by rfl⟩ : syracuseStep 3213167 = 4819751) B4819751
theorem B2142111 : Blo 2141435 2142111 := bstep (se 1 (by rfl) ⟨1606583, by rfl⟩ : syracuseStep 2142111 = 3213167) B3213167
theorem B3213173 : Blo 2141435 3213173 := bbase (se 5 (by rfl) ⟨150617, by rfl⟩ : syracuseStep 3213173 = 301235) (by norm_num)
theorem B2142115 : Blo 2141435 2142115 := bstep (se 1 (by rfl) ⟨1606586, by rfl⟩ : syracuseStep 2142115 = 3213173) B3213173
theorem B17370773 : Blo 2141435 17370773 := bbase (se 6 (by rfl) ⟨407127, by rfl⟩ : syracuseStep 17370773 = 814255) (by norm_num)
theorem B11580515 : Blo 2141435 11580515 := bstep (se 1 (by rfl) ⟨8685386, by rfl⟩ : syracuseStep 11580515 = 17370773) B17370773
theorem B7720343 : Blo 2141435 7720343 := bstep (se 1 (by rfl) ⟨5790257, by rfl⟩ : syracuseStep 7720343 = 11580515) B11580515
theorem B5146895 : Blo 2141435 5146895 := bstep (se 1 (by rfl) ⟨3860171, by rfl⟩ : syracuseStep 5146895 = 7720343) B7720343
theorem B3431263 : Blo 2141435 3431263 := bstep (se 1 (by rfl) ⟨2573447, by rfl⟩ : syracuseStep 3431263 = 5146895) B5146895
theorem B4575017 : Blo 2141435 4575017 := bstep (se 2 (by rfl) ⟨1715631, by rfl⟩ : syracuseStep 4575017 = 3431263) B3431263
theorem B3050011 : Blo 2141435 3050011 := bstep (se 1 (by rfl) ⟨2287508, by rfl⟩ : syracuseStep 3050011 = 4575017) B4575017
theorem B4066681 : Blo 2141435 4066681 := bstep (se 2 (by rfl) ⟨1525005, by rfl⟩ : syracuseStep 4066681 = 3050011) B3050011
theorem B5422241 : Blo 2141435 5422241 := bstep (se 2 (by rfl) ⟨2033340, by rfl⟩ : syracuseStep 5422241 = 4066681) B4066681
theorem B3614827 : Blo 2141435 3614827 := bstep (se 1 (by rfl) ⟨2711120, by rfl⟩ : syracuseStep 3614827 = 5422241) B5422241
theorem B4819769 : Blo 2141435 4819769 := bstep (se 2 (by rfl) ⟨1807413, by rfl⟩ : syracuseStep 4819769 = 3614827) B3614827
theorem B3213179 : Blo 2141435 3213179 := bstep (se 1 (by rfl) ⟨2409884, by rfl⟩ : syracuseStep 3213179 = 4819769) B4819769
theorem B2142119 : Blo 2141435 2142119 := bstep (se 1 (by rfl) ⟨1606589, by rfl⟩ : syracuseStep 2142119 = 3213179) B3213179
theorem B2409889 : Blo 2141435 2409889 := bbase (se 2 (by rfl) ⟨903708, by rfl⟩ : syracuseStep 2409889 = 1807417) (by norm_num)
theorem B3213185 : Blo 2141435 3213185 := bstep (se 2 (by rfl) ⟨1204944, by rfl⟩ : syracuseStep 3213185 = 2409889) B2409889
theorem B2142123 : Blo 2141435 2142123 := bstep (se 1 (by rfl) ⟨1606592, by rfl⟩ : syracuseStep 2142123 = 3213185) B3213185
theorem B5422261 : Blo 2141435 5422261 := bbase (se 5 (by rfl) ⟨254168, by rfl⟩ : syracuseStep 5422261 = 508337) (by norm_num)
theorem B7229681 : Blo 2141435 7229681 := bstep (se 2 (by rfl) ⟨2711130, by rfl⟩ : syracuseStep 7229681 = 5422261) B5422261
theorem B4819787 : Blo 2141435 4819787 := bstep (se 1 (by rfl) ⟨3614840, by rfl⟩ : syracuseStep 4819787 = 7229681) B7229681
theorem B3213191 : Blo 2141435 3213191 := bstep (se 1 (by rfl) ⟨2409893, by rfl⟩ : syracuseStep 3213191 = 4819787) B4819787
theorem B2142127 : Blo 2141435 2142127 := bstep (se 1 (by rfl) ⟨1606595, by rfl⟩ : syracuseStep 2142127 = 3213191) B3213191
theorem B3213197 : Blo 2141435 3213197 := bbase (se 3 (by rfl) ⟨602474, by rfl⟩ : syracuseStep 3213197 = 1204949) (by norm_num)
theorem B2142131 : Blo 2141435 2142131 := bstep (se 1 (by rfl) ⟨1606598, by rfl⟩ : syracuseStep 2142131 = 3213197) B3213197
theorem B4819805 : Blo 2141435 4819805 := bbase (se 3 (by rfl) ⟨903713, by rfl⟩ : syracuseStep 4819805 = 1807427) (by norm_num)
theorem B3213203 : Blo 2141435 3213203 := bstep (se 1 (by rfl) ⟨2409902, by rfl⟩ : syracuseStep 3213203 = 4819805) B4819805
theorem B2142135 : Blo 2141435 2142135 := bstep (se 1 (by rfl) ⟨1606601, by rfl⟩ : syracuseStep 2142135 = 3213203) B3213203
theorem B3614861 : Blo 2141435 3614861 := bbase (se 3 (by rfl) ⟨677786, by rfl⟩ : syracuseStep 3614861 = 1355573) (by norm_num)
theorem B2409907 : Blo 2141435 2409907 := bstep (se 1 (by rfl) ⟨1807430, by rfl⟩ : syracuseStep 2409907 = 3614861) B3614861
theorem B3213209 : Blo 2141435 3213209 := bstep (se 2 (by rfl) ⟨1204953, by rfl⟩ : syracuseStep 3213209 = 2409907) B2409907
theorem B2142139 : Blo 2141435 2142139 := bstep (se 1 (by rfl) ⟨1606604, by rfl⟩ : syracuseStep 2142139 = 3213209) B3213209
theorem B2644177 : Blo 2141435 2644177 := bbase (se 2 (by rfl) ⟨991566, by rfl⟩ : syracuseStep 2644177 = 1983133) (by norm_num)
theorem B3525569 : Blo 2141435 3525569 := bstep (se 2 (by rfl) ⟨1322088, by rfl⟩ : syracuseStep 3525569 = 2644177) B2644177
theorem B37606069 : Blo 2141435 37606069 := bstep (se 5 (by rfl) ⟨1762784, by rfl⟩ : syracuseStep 37606069 = 3525569) B3525569
theorem B50141425 : Blo 2141435 50141425 := bstep (se 2 (by rfl) ⟨18803034, by rfl⟩ : syracuseStep 50141425 = 37606069) B37606069
theorem B66855233 : Blo 2141435 66855233 := bstep (se 2 (by rfl) ⟨25070712, by rfl⟩ : syracuseStep 66855233 = 50141425) B50141425
theorem B44570155 : Blo 2141435 44570155 := bstep (se 1 (by rfl) ⟨33427616, by rfl⟩ : syracuseStep 44570155 = 66855233) B66855233
theorem B59426873 : Blo 2141435 59426873 := bstep (se 2 (by rfl) ⟨22285077, by rfl⟩ : syracuseStep 59426873 = 44570155) B44570155
theorem B39617915 : Blo 2141435 39617915 := bstep (se 1 (by rfl) ⟨29713436, by rfl⟩ : syracuseStep 39617915 = 59426873) B59426873
theorem B422591093 : Blo 2141435 422591093 := bstep (se 5 (by rfl) ⟨19808957, by rfl⟩ : syracuseStep 422591093 = 39617915) B39617915
theorem B281727395 : Blo 2141435 281727395 := bstep (se 1 (by rfl) ⟨211295546, by rfl⟩ : syracuseStep 281727395 = 422591093) B422591093
theorem B187818263 : Blo 2141435 187818263 := bstep (se 1 (by rfl) ⟨140863697, by rfl⟩ : syracuseStep 187818263 = 281727395) B281727395
theorem B125212175 : Blo 2141435 125212175 := bstep (se 1 (by rfl) ⟨93909131, by rfl⟩ : syracuseStep 125212175 = 187818263) B187818263
theorem B83474783 : Blo 2141435 83474783 := bstep (se 1 (by rfl) ⟨62606087, by rfl⟩ : syracuseStep 83474783 = 125212175) B125212175
theorem B55649855 : Blo 2141435 55649855 := bstep (se 1 (by rfl) ⟨41737391, by rfl⟩ : syracuseStep 55649855 = 83474783) B83474783
theorem B37099903 : Blo 2141435 37099903 := bstep (se 1 (by rfl) ⟨27824927, by rfl⟩ : syracuseStep 37099903 = 55649855) B55649855
theorem B49466537 : Blo 2141435 49466537 := bstep (se 2 (by rfl) ⟨18549951, by rfl⟩ : syracuseStep 49466537 = 37099903) B37099903
theorem B32977691 : Blo 2141435 32977691 := bstep (se 1 (by rfl) ⟨24733268, by rfl⟩ : syracuseStep 32977691 = 49466537) B49466537
theorem B21985127 : Blo 2141435 21985127 := bstep (se 1 (by rfl) ⟨16488845, by rfl⟩ : syracuseStep 21985127 = 32977691) B32977691
theorem B14656751 : Blo 2141435 14656751 := bstep (se 1 (by rfl) ⟨10992563, by rfl⟩ : syracuseStep 14656751 = 21985127) B21985127
theorem B9771167 : Blo 2141435 9771167 := bstep (se 1 (by rfl) ⟨7328375, by rfl⟩ : syracuseStep 9771167 = 14656751) B14656751
theorem B6514111 : Blo 2141435 6514111 := bstep (se 1 (by rfl) ⟨4885583, by rfl⟩ : syracuseStep 6514111 = 9771167) B9771167
theorem B8685481 : Blo 2141435 8685481 := bstep (se 2 (by rfl) ⟨3257055, by rfl⟩ : syracuseStep 8685481 = 6514111) B6514111
theorem B11580641 : Blo 2141435 11580641 := bstep (se 2 (by rfl) ⟨4342740, by rfl⟩ : syracuseStep 11580641 = 8685481) B8685481
theorem B7720427 : Blo 2141435 7720427 := bstep (se 1 (by rfl) ⟨5790320, by rfl⟩ : syracuseStep 7720427 = 11580641) B11580641
theorem B5146951 : Blo 2141435 5146951 := bstep (se 1 (by rfl) ⟨3860213, by rfl⟩ : syracuseStep 5146951 = 7720427) B7720427
theorem B6862601 : Blo 2141435 6862601 := bstep (se 2 (by rfl) ⟨2573475, by rfl⟩ : syracuseStep 6862601 = 5146951) B5146951
theorem B18300269 : Blo 2141435 18300269 := bstep (se 3 (by rfl) ⟨3431300, by rfl⟩ : syracuseStep 18300269 = 6862601) B6862601
theorem B12200179 : Blo 2141435 12200179 := bstep (se 1 (by rfl) ⟨9150134, by rfl⟩ : syracuseStep 12200179 = 18300269) B18300269
theorem B16266905 : Blo 2141435 16266905 := bstep (se 2 (by rfl) ⟨6100089, by rfl⟩ : syracuseStep 16266905 = 12200179) B12200179
theorem B10844603 : Blo 2141435 10844603 := bstep (se 1 (by rfl) ⟨8133452, by rfl⟩ : syracuseStep 10844603 = 16266905) B16266905
theorem B7229735 : Blo 2141435 7229735 := bstep (se 1 (by rfl) ⟨5422301, by rfl⟩ : syracuseStep 7229735 = 10844603) B10844603
theorem B4819823 : Blo 2141435 4819823 := bstep (se 1 (by rfl) ⟨3614867, by rfl⟩ : syracuseStep 4819823 = 7229735) B7229735
theorem B3213215 : Blo 2141435 3213215 := bstep (se 1 (by rfl) ⟨2409911, by rfl⟩ : syracuseStep 3213215 = 4819823) B4819823
theorem B2142143 : Blo 2141435 2142143 := bstep (se 1 (by rfl) ⟨1606607, by rfl⟩ : syracuseStep 2142143 = 3213215) B3213215
theorem B3213221 : Blo 2141435 3213221 := bbase (se 4 (by rfl) ⟨301239, by rfl⟩ : syracuseStep 3213221 = 602479) (by norm_num)
theorem B2142147 : Blo 2141435 2142147 := bstep (se 1 (by rfl) ⟨1606610, by rfl⟩ : syracuseStep 2142147 = 3213221) B3213221
theorem B2711161 : Blo 2141435 2711161 := bbase (se 2 (by rfl) ⟨1016685, by rfl⟩ : syracuseStep 2711161 = 2033371) (by norm_num)
theorem B3614881 : Blo 2141435 3614881 := bstep (se 2 (by rfl) ⟨1355580, by rfl⟩ : syracuseStep 3614881 = 2711161) B2711161
theorem B4819841 : Blo 2141435 4819841 := bstep (se 2 (by rfl) ⟨1807440, by rfl⟩ : syracuseStep 4819841 = 3614881) B3614881
theorem B3213227 : Blo 2141435 3213227 := bstep (se 1 (by rfl) ⟨2409920, by rfl⟩ : syracuseStep 3213227 = 4819841) B4819841
theorem B2142151 : Blo 2141435 2142151 := bstep (se 1 (by rfl) ⟨1606613, by rfl⟩ : syracuseStep 2142151 = 3213227) B3213227
theorem B2409925 : Blo 2141435 2409925 := bbase (se 4 (by rfl) ⟨225930, by rfl⟩ : syracuseStep 2409925 = 451861) (by norm_num)
theorem B3213233 : Blo 2141435 3213233 := bstep (se 2 (by rfl) ⟨1204962, by rfl⟩ : syracuseStep 3213233 = 2409925) B2409925
theorem B2142155 : Blo 2141435 2142155 := bstep (se 1 (by rfl) ⟨1606616, by rfl⟩ : syracuseStep 2142155 = 3213233) B3213233
theorem B4066757 : Blo 2141435 4066757 := bbase (se 4 (by rfl) ⟨381258, by rfl⟩ : syracuseStep 4066757 = 762517) (by norm_num)
theorem B2711171 : Blo 2141435 2711171 := bstep (se 1 (by rfl) ⟨2033378, by rfl⟩ : syracuseStep 2711171 = 4066757) B4066757
theorem B7229789 : Blo 2141435 7229789 := bstep (se 3 (by rfl) ⟨1355585, by rfl⟩ : syracuseStep 7229789 = 2711171) B2711171
theorem B4819859 : Blo 2141435 4819859 := bstep (se 1 (by rfl) ⟨3614894, by rfl⟩ : syracuseStep 4819859 = 7229789) B7229789
theorem B3213239 : Blo 2141435 3213239 := bstep (se 1 (by rfl) ⟨2409929, by rfl⟩ : syracuseStep 3213239 = 4819859) B4819859
theorem B2142159 : Blo 2141435 2142159 := bstep (se 1 (by rfl) ⟨1606619, by rfl⟩ : syracuseStep 2142159 = 3213239) B3213239
theorem B3213245 : Blo 2141435 3213245 := bbase (se 3 (by rfl) ⟨602483, by rfl⟩ : syracuseStep 3213245 = 1204967) (by norm_num)
theorem B2142163 : Blo 2141435 2142163 := bstep (se 1 (by rfl) ⟨1606622, by rfl⟩ : syracuseStep 2142163 = 3213245) B3213245
theorem B4819877 : Blo 2141435 4819877 := bbase (se 4 (by rfl) ⟨451863, by rfl⟩ : syracuseStep 4819877 = 903727) (by norm_num)
theorem B3213251 : Blo 2141435 3213251 := bstep (se 1 (by rfl) ⟨2409938, by rfl⟩ : syracuseStep 3213251 = 4819877) B4819877
theorem B2142167 : Blo 2141435 2142167 := bstep (se 1 (by rfl) ⟨1606625, by rfl⟩ : syracuseStep 2142167 = 3213251) B3213251
theorem B5422373 : Blo 2141435 5422373 := bbase (se 4 (by rfl) ⟨508347, by rfl⟩ : syracuseStep 5422373 = 1016695) (by norm_num)
theorem B3614915 : Blo 2141435 3614915 := bstep (se 1 (by rfl) ⟨2711186, by rfl⟩ : syracuseStep 3614915 = 5422373) B5422373
theorem B2409943 : Blo 2141435 2409943 := bstep (se 1 (by rfl) ⟨1807457, by rfl⟩ : syracuseStep 2409943 = 3614915) B3614915
theorem B3213257 : Blo 2141435 3213257 := bstep (se 2 (by rfl) ⟨1204971, by rfl⟩ : syracuseStep 3213257 = 2409943) B2409943
theorem B2142171 : Blo 2141435 2142171 := bstep (se 1 (by rfl) ⟨1606628, by rfl⟩ : syracuseStep 2142171 = 3213257) B3213257
theorem B6100181 : Blo 2141435 6100181 := bbase (se 7 (by rfl) ⟨71486, by rfl⟩ : syracuseStep 6100181 = 142973) (by norm_num)
theorem B4066787 : Blo 2141435 4066787 := bstep (se 1 (by rfl) ⟨3050090, by rfl⟩ : syracuseStep 4066787 = 6100181) B6100181
theorem B10844765 : Blo 2141435 10844765 := bstep (se 3 (by rfl) ⟨2033393, by rfl⟩ : syracuseStep 10844765 = 4066787) B4066787
theorem B7229843 : Blo 2141435 7229843 := bstep (se 1 (by rfl) ⟨5422382, by rfl⟩ : syracuseStep 7229843 = 10844765) B10844765
theorem B4819895 : Blo 2141435 4819895 := bstep (se 1 (by rfl) ⟨3614921, by rfl⟩ : syracuseStep 4819895 = 7229843) B7229843
theorem B3213263 : Blo 2141435 3213263 := bstep (se 1 (by rfl) ⟨2409947, by rfl⟩ : syracuseStep 3213263 = 4819895) B4819895
theorem B2142175 : Blo 2141435 2142175 := bstep (se 1 (by rfl) ⟨1606631, by rfl⟩ : syracuseStep 2142175 = 3213263) B3213263
theorem B3213269 : Blo 2141435 3213269 := bbase (se 7 (by rfl) ⟨37655, by rfl⟩ : syracuseStep 3213269 = 75311) (by norm_num)
theorem B2142179 : Blo 2141435 2142179 := bstep (se 1 (by rfl) ⟨1606634, by rfl⟩ : syracuseStep 2142179 = 3213269) B3213269
theorem B8133605 : Blo 2141435 8133605 := bbase (se 4 (by rfl) ⟨762525, by rfl⟩ : syracuseStep 8133605 = 1525051) (by norm_num)
theorem B5422403 : Blo 2141435 5422403 := bstep (se 1 (by rfl) ⟨4066802, by rfl⟩ : syracuseStep 5422403 = 8133605) B8133605
theorem B3614935 : Blo 2141435 3614935 := bstep (se 1 (by rfl) ⟨2711201, by rfl⟩ : syracuseStep 3614935 = 5422403) B5422403
theorem B4819913 : Blo 2141435 4819913 := bstep (se 2 (by rfl) ⟨1807467, by rfl⟩ : syracuseStep 4819913 = 3614935) B3614935
theorem B3213275 : Blo 2141435 3213275 := bstep (se 1 (by rfl) ⟨2409956, by rfl⟩ : syracuseStep 3213275 = 4819913) B4819913
theorem B2142183 : Blo 2141435 2142183 := bstep (se 1 (by rfl) ⟨1606637, by rfl⟩ : syracuseStep 2142183 = 3213275) B3213275
theorem B2409961 : Blo 2141435 2409961 := bbase (se 2 (by rfl) ⟨903735, by rfl⟩ : syracuseStep 2409961 = 1807471) (by norm_num)
theorem B3213281 : Blo 2141435 3213281 := bstep (se 2 (by rfl) ⟨1204980, by rfl⟩ : syracuseStep 3213281 = 2409961) B2409961
theorem B2142187 : Blo 2141435 2142187 := bstep (se 1 (by rfl) ⟨1606640, by rfl⟩ : syracuseStep 2142187 = 3213281) B3213281
theorem B2287585 : Blo 2141435 2287585 := bbase (se 2 (by rfl) ⟨857844, by rfl⟩ : syracuseStep 2287585 = 1715689) (by norm_num)
theorem B12200453 : Blo 2141435 12200453 := bstep (se 4 (by rfl) ⟨1143792, by rfl⟩ : syracuseStep 12200453 = 2287585) B2287585
theorem B8133635 : Blo 2141435 8133635 := bstep (se 1 (by rfl) ⟨6100226, by rfl⟩ : syracuseStep 8133635 = 12200453) B12200453
theorem B5422423 : Blo 2141435 5422423 := bstep (se 1 (by rfl) ⟨4066817, by rfl⟩ : syracuseStep 5422423 = 8133635) B8133635
theorem B7229897 : Blo 2141435 7229897 := bstep (se 2 (by rfl) ⟨2711211, by rfl⟩ : syracuseStep 7229897 = 5422423) B5422423
theorem B4819931 : Blo 2141435 4819931 := bstep (se 1 (by rfl) ⟨3614948, by rfl⟩ : syracuseStep 4819931 = 7229897) B7229897
theorem B3213287 : Blo 2141435 3213287 := bstep (se 1 (by rfl) ⟨2409965, by rfl⟩ : syracuseStep 3213287 = 4819931) B4819931
theorem B2142191 : Blo 2141435 2142191 := bstep (se 1 (by rfl) ⟨1606643, by rfl⟩ : syracuseStep 2142191 = 3213287) B3213287
theorem B3213293 : Blo 2141435 3213293 := bbase (se 3 (by rfl) ⟨602492, by rfl⟩ : syracuseStep 3213293 = 1204985) (by norm_num)
theorem B2142195 : Blo 2141435 2142195 := bstep (se 1 (by rfl) ⟨1606646, by rfl⟩ : syracuseStep 2142195 = 3213293) B3213293
theorem B4819949 : Blo 2141435 4819949 := bbase (se 3 (by rfl) ⟨903740, by rfl⟩ : syracuseStep 4819949 = 1807481) (by norm_num)
theorem B3213299 : Blo 2141435 3213299 := bstep (se 1 (by rfl) ⟨2409974, by rfl⟩ : syracuseStep 3213299 = 4819949) B4819949
theorem B2142199 : Blo 2141435 2142199 := bstep (se 1 (by rfl) ⟨1606649, by rfl⟩ : syracuseStep 2142199 = 3213299) B3213299
theorem B4575197 : Blo 2141435 4575197 := bbase (se 3 (by rfl) ⟨857849, by rfl⟩ : syracuseStep 4575197 = 1715699) (by norm_num)
theorem B3050131 : Blo 2141435 3050131 := bstep (se 1 (by rfl) ⟨2287598, by rfl⟩ : syracuseStep 3050131 = 4575197) B4575197
theorem B4066841 : Blo 2141435 4066841 := bstep (se 2 (by rfl) ⟨1525065, by rfl⟩ : syracuseStep 4066841 = 3050131) B3050131
theorem B2711227 : Blo 2141435 2711227 := bstep (se 1 (by rfl) ⟨2033420, by rfl⟩ : syracuseStep 2711227 = 4066841) B4066841
theorem B3614969 : Blo 2141435 3614969 := bstep (se 2 (by rfl) ⟨1355613, by rfl⟩ : syracuseStep 3614969 = 2711227) B2711227
theorem B2409979 : Blo 2141435 2409979 := bstep (se 1 (by rfl) ⟨1807484, by rfl⟩ : syracuseStep 2409979 = 3614969) B3614969
theorem B3213305 : Blo 2141435 3213305 := bstep (se 2 (by rfl) ⟨1204989, by rfl⟩ : syracuseStep 3213305 = 2409979) B2409979
theorem B2142203 : Blo 2141435 2142203 := bstep (se 1 (by rfl) ⟨1606652, by rfl⟩ : syracuseStep 2142203 = 3213305) B3213305
theorem B16489333 : Blo 2141435 16489333 := bbase (se 5 (by rfl) ⟨772937, by rfl⟩ : syracuseStep 16489333 = 1545875) (by norm_num)
theorem B21985777 : Blo 2141435 21985777 := bstep (se 2 (by rfl) ⟨8244666, by rfl⟩ : syracuseStep 21985777 = 16489333) B16489333
theorem B29314369 : Blo 2141435 29314369 := bstep (se 2 (by rfl) ⟨10992888, by rfl⟩ : syracuseStep 29314369 = 21985777) B21985777
theorem B39085825 : Blo 2141435 39085825 := bstep (se 2 (by rfl) ⟨14657184, by rfl⟩ : syracuseStep 39085825 = 29314369) B29314369
theorem B52114433 : Blo 2141435 52114433 := bstep (se 2 (by rfl) ⟨19542912, by rfl⟩ : syracuseStep 52114433 = 39085825) B39085825
theorem B138971821 : Blo 2141435 138971821 := bstep (se 3 (by rfl) ⟨26057216, by rfl⟩ : syracuseStep 138971821 = 52114433) B52114433
theorem B185295761 : Blo 2141435 185295761 := bstep (se 2 (by rfl) ⟨69485910, by rfl⟩ : syracuseStep 185295761 = 138971821) B138971821
theorem B123530507 : Blo 2141435 123530507 := bstep (se 1 (by rfl) ⟨92647880, by rfl⟩ : syracuseStep 123530507 = 185295761) B185295761
theorem B82353671 : Blo 2141435 82353671 := bstep (se 1 (by rfl) ⟨61765253, by rfl⟩ : syracuseStep 82353671 = 123530507) B123530507
theorem B54902447 : Blo 2141435 54902447 := bstep (se 1 (by rfl) ⟨41176835, by rfl⟩ : syracuseStep 54902447 = 82353671) B82353671
theorem B36601631 : Blo 2141435 36601631 := bstep (se 1 (by rfl) ⟨27451223, by rfl⟩ : syracuseStep 36601631 = 54902447) B54902447
theorem B24401087 : Blo 2141435 24401087 := bstep (se 1 (by rfl) ⟨18300815, by rfl⟩ : syracuseStep 24401087 = 36601631) B36601631
theorem B16267391 : Blo 2141435 16267391 := bstep (se 1 (by rfl) ⟨12200543, by rfl⟩ : syracuseStep 16267391 = 24401087) B24401087
theorem B10844927 : Blo 2141435 10844927 := bstep (se 1 (by rfl) ⟨8133695, by rfl⟩ : syracuseStep 10844927 = 16267391) B16267391
theorem B7229951 : Blo 2141435 7229951 := bstep (se 1 (by rfl) ⟨5422463, by rfl⟩ : syracuseStep 7229951 = 10844927) B10844927
theorem B4819967 : Blo 2141435 4819967 := bstep (se 1 (by rfl) ⟨3614975, by rfl⟩ : syracuseStep 4819967 = 7229951) B7229951
theorem B3213311 : Blo 2141435 3213311 := bstep (se 1 (by rfl) ⟨2409983, by rfl⟩ : syracuseStep 3213311 = 4819967) B4819967
theorem B2142207 : Blo 2141435 2142207 := bstep (se 1 (by rfl) ⟨1606655, by rfl⟩ : syracuseStep 2142207 = 3213311) B3213311
theorem B3213317 : Blo 2141435 3213317 := bbase (se 4 (by rfl) ⟨301248, by rfl⟩ : syracuseStep 3213317 = 602497) (by norm_num)
theorem B2142211 : Blo 2141435 2142211 := bstep (se 1 (by rfl) ⟨1606658, by rfl⟩ : syracuseStep 2142211 = 3213317) B3213317
theorem B3614989 : Blo 2141435 3614989 := bbase (se 3 (by rfl) ⟨677810, by rfl⟩ : syracuseStep 3614989 = 1355621) (by norm_num)
theorem B4819985 : Blo 2141435 4819985 := bstep (se 2 (by rfl) ⟨1807494, by rfl⟩ : syracuseStep 4819985 = 3614989) B3614989
theorem B3213323 : Blo 2141435 3213323 := bstep (se 1 (by rfl) ⟨2409992, by rfl⟩ : syracuseStep 3213323 = 4819985) B4819985
theorem B2142215 : Blo 2141435 2142215 := bstep (se 1 (by rfl) ⟨1606661, by rfl⟩ : syracuseStep 2142215 = 3213323) B3213323
theorem B2409997 : Blo 2141435 2409997 := bbase (se 3 (by rfl) ⟨451874, by rfl⟩ : syracuseStep 2409997 = 903749) (by norm_num)
theorem B3213329 : Blo 2141435 3213329 := bstep (se 2 (by rfl) ⟨1204998, by rfl⟩ : syracuseStep 3213329 = 2409997) B2409997
theorem B2142219 : Blo 2141435 2142219 := bstep (se 1 (by rfl) ⟨1606664, by rfl⟩ : syracuseStep 2142219 = 3213329) B3213329
theorem B7230005 : Blo 2141435 7230005 := bbase (se 5 (by rfl) ⟨338906, by rfl⟩ : syracuseStep 7230005 = 677813) (by norm_num)
theorem B4820003 : Blo 2141435 4820003 := bstep (se 1 (by rfl) ⟨3615002, by rfl⟩ : syracuseStep 4820003 = 7230005) B7230005
theorem B3213335 : Blo 2141435 3213335 := bstep (se 1 (by rfl) ⟨2410001, by rfl⟩ : syracuseStep 3213335 = 4820003) B4820003
theorem B2142223 : Blo 2141435 2142223 := bstep (se 1 (by rfl) ⟨1606667, by rfl⟩ : syracuseStep 2142223 = 3213335) B3213335
theorem B3213341 : Blo 2141435 3213341 := bbase (se 3 (by rfl) ⟨602501, by rfl⟩ : syracuseStep 3213341 = 1205003) (by norm_num)
theorem B2142227 : Blo 2141435 2142227 := bstep (se 1 (by rfl) ⟨1606670, by rfl⟩ : syracuseStep 2142227 = 3213341) B3213341
theorem B4820021 : Blo 2141435 4820021 := bbase (se 5 (by rfl) ⟨225938, by rfl⟩ : syracuseStep 4820021 = 451877) (by norm_num)
theorem B3213347 : Blo 2141435 3213347 := bstep (se 1 (by rfl) ⟨2410010, by rfl⟩ : syracuseStep 3213347 = 4820021) B4820021
theorem B2142231 : Blo 2141435 2142231 := bstep (se 1 (by rfl) ⟨1606673, by rfl⟩ : syracuseStep 2142231 = 3213347) B3213347
theorem B5147173 : Blo 2141435 5147173 := bbase (se 4 (by rfl) ⟨482547, by rfl⟩ : syracuseStep 5147173 = 965095) (by norm_num)
theorem B6862897 : Blo 2141435 6862897 := bstep (se 2 (by rfl) ⟨2573586, by rfl⟩ : syracuseStep 6862897 = 5147173) B5147173
theorem B9150529 : Blo 2141435 9150529 := bstep (se 2 (by rfl) ⟨3431448, by rfl⟩ : syracuseStep 9150529 = 6862897) B6862897
theorem B12200705 : Blo 2141435 12200705 := bstep (se 2 (by rfl) ⟨4575264, by rfl⟩ : syracuseStep 12200705 = 9150529) B9150529
theorem B8133803 : Blo 2141435 8133803 := bstep (se 1 (by rfl) ⟨6100352, by rfl⟩ : syracuseStep 8133803 = 12200705) B12200705
theorem B5422535 : Blo 2141435 5422535 := bstep (se 1 (by rfl) ⟨4066901, by rfl⟩ : syracuseStep 5422535 = 8133803) B8133803
theorem B3615023 : Blo 2141435 3615023 := bstep (se 1 (by rfl) ⟨2711267, by rfl⟩ : syracuseStep 3615023 = 5422535) B5422535
theorem B2410015 : Blo 2141435 2410015 := bstep (se 1 (by rfl) ⟨1807511, by rfl⟩ : syracuseStep 2410015 = 3615023) B3615023
theorem B3213353 : Blo 2141435 3213353 := bstep (se 2 (by rfl) ⟨1205007, by rfl⟩ : syracuseStep 3213353 = 2410015) B2410015
theorem B2142235 : Blo 2141435 2142235 := bstep (se 1 (by rfl) ⟨1606676, by rfl⟩ : syracuseStep 2142235 = 3213353) B3213353
theorem B5790581 : Blo 2141435 5790581 := bbase (se 5 (by rfl) ⟨271433, by rfl⟩ : syracuseStep 5790581 = 542867) (by norm_num)
theorem B3860387 : Blo 2141435 3860387 := bstep (se 1 (by rfl) ⟨2895290, by rfl⟩ : syracuseStep 3860387 = 5790581) B5790581
theorem B2573591 : Blo 2141435 2573591 := bstep (se 1 (by rfl) ⟨1930193, by rfl⟩ : syracuseStep 2573591 = 3860387) B3860387
theorem B6862909 : Blo 2141435 6862909 := bstep (se 3 (by rfl) ⟨1286795, by rfl⟩ : syracuseStep 6862909 = 2573591) B2573591
theorem B9150545 : Blo 2141435 9150545 := bstep (se 2 (by rfl) ⟨3431454, by rfl⟩ : syracuseStep 9150545 = 6862909) B6862909
theorem B6100363 : Blo 2141435 6100363 := bstep (se 1 (by rfl) ⟨4575272, by rfl⟩ : syracuseStep 6100363 = 9150545) B9150545
theorem B8133817 : Blo 2141435 8133817 := bstep (se 2 (by rfl) ⟨3050181, by rfl⟩ : syracuseStep 8133817 = 6100363) B6100363
theorem B10845089 : Blo 2141435 10845089 := bstep (se 2 (by rfl) ⟨4066908, by rfl⟩ : syracuseStep 10845089 = 8133817) B8133817
theorem B7230059 : Blo 2141435 7230059 := bstep (se 1 (by rfl) ⟨5422544, by rfl⟩ : syracuseStep 7230059 = 10845089) B10845089
theorem B4820039 : Blo 2141435 4820039 := bstep (se 1 (by rfl) ⟨3615029, by rfl⟩ : syracuseStep 4820039 = 7230059) B7230059
theorem B3213359 : Blo 2141435 3213359 := bstep (se 1 (by rfl) ⟨2410019, by rfl⟩ : syracuseStep 3213359 = 4820039) B4820039
theorem B2142239 : Blo 2141435 2142239 := bstep (se 1 (by rfl) ⟨1606679, by rfl⟩ : syracuseStep 2142239 = 3213359) B3213359
theorem B3213365 : Blo 2141435 3213365 := bbase (se 5 (by rfl) ⟨150626, by rfl⟩ : syracuseStep 3213365 = 301253) (by norm_num)
theorem B2142243 : Blo 2141435 2142243 := bstep (se 1 (by rfl) ⟨1606682, by rfl⟩ : syracuseStep 2142243 = 3213365) B3213365
theorem B5422565 : Blo 2141435 5422565 := bbase (se 4 (by rfl) ⟨508365, by rfl⟩ : syracuseStep 5422565 = 1016731) (by norm_num)
theorem B3615043 : Blo 2141435 3615043 := bstep (se 1 (by rfl) ⟨2711282, by rfl⟩ : syracuseStep 3615043 = 5422565) B5422565
theorem B4820057 : Blo 2141435 4820057 := bstep (se 2 (by rfl) ⟨1807521, by rfl⟩ : syracuseStep 4820057 = 3615043) B3615043
theorem B3213371 : Blo 2141435 3213371 := bstep (se 1 (by rfl) ⟨2410028, by rfl⟩ : syracuseStep 3213371 = 4820057) B4820057
theorem B2142247 : Blo 2141435 2142247 := bstep (se 1 (by rfl) ⟨1606685, by rfl⟩ : syracuseStep 2142247 = 3213371) B3213371
theorem B2410033 : Blo 2141435 2410033 := bbase (se 2 (by rfl) ⟨903762, by rfl⟩ : syracuseStep 2410033 = 1807525) (by norm_num)
theorem B3213377 : Blo 2141435 3213377 := bstep (se 2 (by rfl) ⟨1205016, by rfl⟩ : syracuseStep 3213377 = 2410033) B2410033
theorem B2142251 : Blo 2141435 2142251 := bstep (se 1 (by rfl) ⟨1606688, by rfl⟩ : syracuseStep 2142251 = 3213377) B3213377
theorem B5147221 : Blo 2141435 5147221 := bbase (se 8 (by rfl) ⟨30159, by rfl⟩ : syracuseStep 5147221 = 60319) (by norm_num)
theorem B6862961 : Blo 2141435 6862961 := bstep (se 2 (by rfl) ⟨2573610, by rfl⟩ : syracuseStep 6862961 = 5147221) B5147221
theorem B4575307 : Blo 2141435 4575307 := bstep (se 1 (by rfl) ⟨3431480, by rfl⟩ : syracuseStep 4575307 = 6862961) B6862961
theorem B6100409 : Blo 2141435 6100409 := bstep (se 2 (by rfl) ⟨2287653, by rfl⟩ : syracuseStep 6100409 = 4575307) B4575307
theorem B4066939 : Blo 2141435 4066939 := bstep (se 1 (by rfl) ⟨3050204, by rfl⟩ : syracuseStep 4066939 = 6100409) B6100409
theorem B5422585 : Blo 2141435 5422585 := bstep (se 2 (by rfl) ⟨2033469, by rfl⟩ : syracuseStep 5422585 = 4066939) B4066939
theorem B7230113 : Blo 2141435 7230113 := bstep (se 2 (by rfl) ⟨2711292, by rfl⟩ : syracuseStep 7230113 = 5422585) B5422585
theorem B4820075 : Blo 2141435 4820075 := bstep (se 1 (by rfl) ⟨3615056, by rfl⟩ : syracuseStep 4820075 = 7230113) B7230113
theorem B3213383 : Blo 2141435 3213383 := bstep (se 1 (by rfl) ⟨2410037, by rfl⟩ : syracuseStep 3213383 = 4820075) B4820075
theorem B2142255 : Blo 2141435 2142255 := bstep (se 1 (by rfl) ⟨1606691, by rfl⟩ : syracuseStep 2142255 = 3213383) B3213383
theorem B3213389 : Blo 2141435 3213389 := bbase (se 3 (by rfl) ⟨602510, by rfl⟩ : syracuseStep 3213389 = 1205021) (by norm_num)
theorem B2142259 : Blo 2141435 2142259 := bstep (se 1 (by rfl) ⟨1606694, by rfl⟩ : syracuseStep 2142259 = 3213389) B3213389
theorem B4820093 : Blo 2141435 4820093 := bbase (se 3 (by rfl) ⟨903767, by rfl⟩ : syracuseStep 4820093 = 1807535) (by norm_num)
theorem B3213395 : Blo 2141435 3213395 := bstep (se 1 (by rfl) ⟨2410046, by rfl⟩ : syracuseStep 3213395 = 4820093) B4820093
theorem B2142263 : Blo 2141435 2142263 := bstep (se 1 (by rfl) ⟨1606697, by rfl⟩ : syracuseStep 2142263 = 3213395) B3213395
theorem B3615077 : Blo 2141435 3615077 := bbase (se 4 (by rfl) ⟨338913, by rfl⟩ : syracuseStep 3615077 = 677827) (by norm_num)
theorem B2410051 : Blo 2141435 2410051 := bstep (se 1 (by rfl) ⟨1807538, by rfl⟩ : syracuseStep 2410051 = 3615077) B3615077
theorem B3213401 : Blo 2141435 3213401 := bstep (se 2 (by rfl) ⟨1205025, by rfl⟩ : syracuseStep 3213401 = 2410051) B2410051
theorem B2142267 : Blo 2141435 2142267 := bstep (se 1 (by rfl) ⟨1606700, by rfl⟩ : syracuseStep 2142267 = 3213401) B3213401
theorem B4575341 : Blo 2141435 4575341 := bbase (se 3 (by rfl) ⟨857876, by rfl⟩ : syracuseStep 4575341 = 1715753) (by norm_num)
theorem B3050227 : Blo 2141435 3050227 := bstep (se 1 (by rfl) ⟨2287670, by rfl⟩ : syracuseStep 3050227 = 4575341) B4575341
theorem B16267877 : Blo 2141435 16267877 := bstep (se 4 (by rfl) ⟨1525113, by rfl⟩ : syracuseStep 16267877 = 3050227) B3050227
theorem B10845251 : Blo 2141435 10845251 := bstep (se 1 (by rfl) ⟨8133938, by rfl⟩ : syracuseStep 10845251 = 16267877) B16267877
theorem B7230167 : Blo 2141435 7230167 := bstep (se 1 (by rfl) ⟨5422625, by rfl⟩ : syracuseStep 7230167 = 10845251) B10845251
theorem B4820111 : Blo 2141435 4820111 := bstep (se 1 (by rfl) ⟨3615083, by rfl⟩ : syracuseStep 4820111 = 7230167) B7230167
theorem B3213407 : Blo 2141435 3213407 := bstep (se 1 (by rfl) ⟨2410055, by rfl⟩ : syracuseStep 3213407 = 4820111) B4820111
theorem B2142271 : Blo 2141435 2142271 := bstep (se 1 (by rfl) ⟨1606703, by rfl⟩ : syracuseStep 2142271 = 3213407) B3213407
theorem B3213413 : Blo 2141435 3213413 := bbase (se 4 (by rfl) ⟨301257, by rfl⟩ : syracuseStep 3213413 = 602515) (by norm_num)
theorem B2142275 : Blo 2141435 2142275 := bstep (se 1 (by rfl) ⟨1606706, by rfl⟩ : syracuseStep 2142275 = 3213413) B3213413
theorem B3664421 : Blo 2141435 3664421 := bbase (se 4 (by rfl) ⟨343539, by rfl⟩ : syracuseStep 3664421 = 687079) (by norm_num)
theorem B39087157 : Blo 2141435 39087157 := bstep (se 5 (by rfl) ⟨1832210, by rfl⟩ : syracuseStep 39087157 = 3664421) B3664421
theorem B52116209 : Blo 2141435 52116209 := bstep (se 2 (by rfl) ⟨19543578, by rfl⟩ : syracuseStep 52116209 = 39087157) B39087157
theorem B34744139 : Blo 2141435 34744139 := bstep (se 1 (by rfl) ⟨26058104, by rfl⟩ : syracuseStep 34744139 = 52116209) B52116209
theorem B23162759 : Blo 2141435 23162759 := bstep (se 1 (by rfl) ⟨17372069, by rfl⟩ : syracuseStep 23162759 = 34744139) B34744139
theorem B15441839 : Blo 2141435 15441839 := bstep (se 1 (by rfl) ⟨11581379, by rfl⟩ : syracuseStep 15441839 = 23162759) B23162759
theorem B10294559 : Blo 2141435 10294559 := bstep (se 1 (by rfl) ⟨7720919, by rfl⟩ : syracuseStep 10294559 = 15441839) B15441839
theorem B6863039 : Blo 2141435 6863039 := bstep (se 1 (by rfl) ⟨5147279, by rfl⟩ : syracuseStep 6863039 = 10294559) B10294559
theorem B4575359 : Blo 2141435 4575359 := bstep (se 1 (by rfl) ⟨3431519, by rfl⟩ : syracuseStep 4575359 = 6863039) B6863039
theorem B3050239 : Blo 2141435 3050239 := bstep (se 1 (by rfl) ⟨2287679, by rfl⟩ : syracuseStep 3050239 = 4575359) B4575359
theorem B4066985 : Blo 2141435 4066985 := bstep (se 2 (by rfl) ⟨1525119, by rfl⟩ : syracuseStep 4066985 = 3050239) B3050239
theorem B2711323 : Blo 2141435 2711323 := bstep (se 1 (by rfl) ⟨2033492, by rfl⟩ : syracuseStep 2711323 = 4066985) B4066985
theorem B3615097 : Blo 2141435 3615097 := bstep (se 2 (by rfl) ⟨1355661, by rfl⟩ : syracuseStep 3615097 = 2711323) B2711323
theorem B4820129 : Blo 2141435 4820129 := bstep (se 2 (by rfl) ⟨1807548, by rfl⟩ : syracuseStep 4820129 = 3615097) B3615097
theorem B3213419 : Blo 2141435 3213419 := bstep (se 1 (by rfl) ⟨2410064, by rfl⟩ : syracuseStep 3213419 = 4820129) B4820129
theorem B2142279 : Blo 2141435 2142279 := bstep (se 1 (by rfl) ⟨1606709, by rfl⟩ : syracuseStep 2142279 = 3213419) B3213419
theorem B2410069 : Blo 2141435 2410069 := bbase (se 8 (by rfl) ⟨14121, by rfl⟩ : syracuseStep 2410069 = 28243) (by norm_num)
theorem B3213425 : Blo 2141435 3213425 := bstep (se 2 (by rfl) ⟨1205034, by rfl⟩ : syracuseStep 3213425 = 2410069) B2410069
theorem B2142283 : Blo 2141435 2142283 := bstep (se 1 (by rfl) ⟨1606712, by rfl⟩ : syracuseStep 2142283 = 3213425) B3213425
theorem B2711333 : Blo 2141435 2711333 := bbase (se 4 (by rfl) ⟨254187, by rfl⟩ : syracuseStep 2711333 = 508375) (by norm_num)
theorem B7230221 : Blo 2141435 7230221 := bstep (se 3 (by rfl) ⟨1355666, by rfl⟩ : syracuseStep 7230221 = 2711333) B2711333
theorem B4820147 : Blo 2141435 4820147 := bstep (se 1 (by rfl) ⟨3615110, by rfl⟩ : syracuseStep 4820147 = 7230221) B7230221
theorem B3213431 : Blo 2141435 3213431 := bstep (se 1 (by rfl) ⟨2410073, by rfl⟩ : syracuseStep 3213431 = 4820147) B4820147
theorem B2142287 : Blo 2141435 2142287 := bstep (se 1 (by rfl) ⟨1606715, by rfl⟩ : syracuseStep 2142287 = 3213431) B3213431
theorem B3213437 : Blo 2141435 3213437 := bbase (se 3 (by rfl) ⟨602519, by rfl⟩ : syracuseStep 3213437 = 1205039) (by norm_num)
theorem B2142291 : Blo 2141435 2142291 := bstep (se 1 (by rfl) ⟨1606718, by rfl⟩ : syracuseStep 2142291 = 3213437) B3213437
theorem B4820165 : Blo 2141435 4820165 := bbase (se 4 (by rfl) ⟨451890, by rfl⟩ : syracuseStep 4820165 = 903781) (by norm_num)
theorem B3213443 : Blo 2141435 3213443 := bstep (se 1 (by rfl) ⟨2410082, by rfl⟩ : syracuseStep 3213443 = 4820165) B4820165
theorem B2142295 : Blo 2141435 2142295 := bstep (se 1 (by rfl) ⟨1606721, by rfl⟩ : syracuseStep 2142295 = 3213443) B3213443
theorem B23478997 : Blo 2141435 23478997 := bbase (se 7 (by rfl) ⟨275144, by rfl⟩ : syracuseStep 23478997 = 550289) (by norm_num)
theorem B31305329 : Blo 2141435 31305329 := bstep (se 2 (by rfl) ⟨11739498, by rfl⟩ : syracuseStep 31305329 = 23478997) B23478997
theorem B20870219 : Blo 2141435 20870219 := bstep (se 1 (by rfl) ⟨15652664, by rfl⟩ : syracuseStep 20870219 = 31305329) B31305329
theorem B13913479 : Blo 2141435 13913479 := bstep (se 1 (by rfl) ⟨10435109, by rfl⟩ : syracuseStep 13913479 = 20870219) B20870219
theorem B18551305 : Blo 2141435 18551305 := bstep (se 2 (by rfl) ⟨6956739, by rfl⟩ : syracuseStep 18551305 = 13913479) B13913479
theorem B24735073 : Blo 2141435 24735073 := bstep (se 2 (by rfl) ⟨9275652, by rfl⟩ : syracuseStep 24735073 = 18551305) B18551305
theorem B32980097 : Blo 2141435 32980097 := bstep (se 2 (by rfl) ⟨12367536, by rfl⟩ : syracuseStep 32980097 = 24735073) B24735073
theorem B21986731 : Blo 2141435 21986731 := bstep (se 1 (by rfl) ⟨16490048, by rfl⟩ : syracuseStep 21986731 = 32980097) B32980097
theorem B29315641 : Blo 2141435 29315641 := bstep (se 2 (by rfl) ⟨10993365, by rfl⟩ : syracuseStep 29315641 = 21986731) B21986731
theorem B39087521 : Blo 2141435 39087521 := bstep (se 2 (by rfl) ⟨14657820, by rfl⟩ : syracuseStep 39087521 = 29315641) B29315641
theorem B26058347 : Blo 2141435 26058347 := bstep (se 1 (by rfl) ⟨19543760, by rfl⟩ : syracuseStep 26058347 = 39087521) B39087521
theorem B17372231 : Blo 2141435 17372231 := bstep (se 1 (by rfl) ⟨13029173, by rfl⟩ : syracuseStep 17372231 = 26058347) B26058347
theorem B11581487 : Blo 2141435 11581487 := bstep (se 1 (by rfl) ⟨8686115, by rfl⟩ : syracuseStep 11581487 = 17372231) B17372231
theorem B7720991 : Blo 2141435 7720991 := bstep (se 1 (by rfl) ⟨5790743, by rfl⟩ : syracuseStep 7720991 = 11581487) B11581487
theorem B5147327 : Blo 2141435 5147327 := bstep (se 1 (by rfl) ⟨3860495, by rfl⟩ : syracuseStep 5147327 = 7720991) B7720991
theorem B13726205 : Blo 2141435 13726205 := bstep (se 3 (by rfl) ⟨2573663, by rfl⟩ : syracuseStep 13726205 = 5147327) B5147327
theorem B9150803 : Blo 2141435 9150803 := bstep (se 1 (by rfl) ⟨6863102, by rfl⟩ : syracuseStep 9150803 = 13726205) B13726205
theorem B6100535 : Blo 2141435 6100535 := bstep (se 1 (by rfl) ⟨4575401, by rfl⟩ : syracuseStep 6100535 = 9150803) B9150803
theorem B4067023 : Blo 2141435 4067023 := bstep (se 1 (by rfl) ⟨3050267, by rfl⟩ : syracuseStep 4067023 = 6100535) B6100535
theorem B5422697 : Blo 2141435 5422697 := bstep (se 2 (by rfl) ⟨2033511, by rfl⟩ : syracuseStep 5422697 = 4067023) B4067023
theorem B3615131 : Blo 2141435 3615131 := bstep (se 1 (by rfl) ⟨2711348, by rfl⟩ : syracuseStep 3615131 = 5422697) B5422697
theorem B2410087 : Blo 2141435 2410087 := bstep (se 1 (by rfl) ⟨1807565, by rfl⟩ : syracuseStep 2410087 = 3615131) B3615131
theorem B3213449 : Blo 2141435 3213449 := bstep (se 2 (by rfl) ⟨1205043, by rfl⟩ : syracuseStep 3213449 = 2410087) B2410087
theorem B2142299 : Blo 2141435 2142299 := bstep (se 1 (by rfl) ⟨1606724, by rfl⟩ : syracuseStep 2142299 = 3213449) B3213449
theorem B10845413 : Blo 2141435 10845413 := bbase (se 4 (by rfl) ⟨1016757, by rfl⟩ : syracuseStep 10845413 = 2033515) (by norm_num)
theorem B7230275 : Blo 2141435 7230275 := bstep (se 1 (by rfl) ⟨5422706, by rfl⟩ : syracuseStep 7230275 = 10845413) B10845413
theorem B4820183 : Blo 2141435 4820183 := bstep (se 1 (by rfl) ⟨3615137, by rfl⟩ : syracuseStep 4820183 = 7230275) B7230275
theorem B3213455 : Blo 2141435 3213455 := bstep (se 1 (by rfl) ⟨2410091, by rfl⟩ : syracuseStep 3213455 = 4820183) B4820183
theorem B2142303 : Blo 2141435 2142303 := bstep (se 1 (by rfl) ⟨1606727, by rfl⟩ : syracuseStep 2142303 = 3213455) B3213455
theorem B3213461 : Blo 2141435 3213461 := bbase (se 6 (by rfl) ⟨75315, by rfl⟩ : syracuseStep 3213461 = 150631) (by norm_num)
theorem B2142307 : Blo 2141435 2142307 := bstep (se 1 (by rfl) ⟨1606730, by rfl⟩ : syracuseStep 2142307 = 3213461) B3213461
theorem B9150853 : Blo 2141435 9150853 := bbase (se 4 (by rfl) ⟨857892, by rfl⟩ : syracuseStep 9150853 = 1715785) (by norm_num)
theorem B12201137 : Blo 2141435 12201137 := bstep (se 2 (by rfl) ⟨4575426, by rfl⟩ : syracuseStep 12201137 = 9150853) B9150853
theorem B8134091 : Blo 2141435 8134091 := bstep (se 1 (by rfl) ⟨6100568, by rfl⟩ : syracuseStep 8134091 = 12201137) B12201137
theorem B5422727 : Blo 2141435 5422727 := bstep (se 1 (by rfl) ⟨4067045, by rfl⟩ : syracuseStep 5422727 = 8134091) B8134091
theorem B3615151 : Blo 2141435 3615151 := bstep (se 1 (by rfl) ⟨2711363, by rfl⟩ : syracuseStep 3615151 = 5422727) B5422727
theorem B4820201 : Blo 2141435 4820201 := bstep (se 2 (by rfl) ⟨1807575, by rfl⟩ : syracuseStep 4820201 = 3615151) B3615151
theorem B3213467 : Blo 2141435 3213467 := bstep (se 1 (by rfl) ⟨2410100, by rfl⟩ : syracuseStep 3213467 = 4820201) B4820201
theorem B2142311 : Blo 2141435 2142311 := bstep (se 1 (by rfl) ⟨1606733, by rfl⟩ : syracuseStep 2142311 = 3213467) B3213467
theorem B2410105 : Blo 2141435 2410105 := bbase (se 2 (by rfl) ⟨903789, by rfl⟩ : syracuseStep 2410105 = 1807579) (by norm_num)
theorem B3213473 : Blo 2141435 3213473 := bstep (se 2 (by rfl) ⟨1205052, by rfl⟩ : syracuseStep 3213473 = 2410105) B2410105
theorem B2142315 : Blo 2141435 2142315 := bstep (se 1 (by rfl) ⟨1606736, by rfl⟩ : syracuseStep 2142315 = 3213473) B3213473
theorem B5217605 : Blo 2141435 5217605 := bbase (se 4 (by rfl) ⟨489150, by rfl⟩ : syracuseStep 5217605 = 978301) (by norm_num)
theorem B3478403 : Blo 2141435 3478403 := bstep (se 1 (by rfl) ⟨2608802, by rfl⟩ : syracuseStep 3478403 = 5217605) B5217605
theorem B9275741 : Blo 2141435 9275741 := bstep (se 3 (by rfl) ⟨1739201, by rfl⟩ : syracuseStep 9275741 = 3478403) B3478403
theorem B6183827 : Blo 2141435 6183827 := bstep (se 1 (by rfl) ⟨4637870, by rfl⟩ : syracuseStep 6183827 = 9275741) B9275741
theorem B4122551 : Blo 2141435 4122551 := bstep (se 1 (by rfl) ⟨3091913, by rfl⟩ : syracuseStep 4122551 = 6183827) B6183827
theorem B2748367 : Blo 2141435 2748367 := bstep (se 1 (by rfl) ⟨2061275, by rfl⟩ : syracuseStep 2748367 = 4122551) B4122551
theorem B3664489 : Blo 2141435 3664489 := bstep (se 2 (by rfl) ⟨1374183, by rfl⟩ : syracuseStep 3664489 = 2748367) B2748367
theorem B4885985 : Blo 2141435 4885985 := bstep (se 2 (by rfl) ⟨1832244, by rfl⟩ : syracuseStep 4885985 = 3664489) B3664489
theorem B3257323 : Blo 2141435 3257323 := bstep (se 1 (by rfl) ⟨2442992, by rfl⟩ : syracuseStep 3257323 = 4885985) B4885985
theorem B17372389 : Blo 2141435 17372389 := bstep (se 4 (by rfl) ⟨1628661, by rfl⟩ : syracuseStep 17372389 = 3257323) B3257323
theorem B23163185 : Blo 2141435 23163185 := bstep (se 2 (by rfl) ⟨8686194, by rfl⟩ : syracuseStep 23163185 = 17372389) B17372389
theorem B15442123 : Blo 2141435 15442123 := bstep (se 1 (by rfl) ⟨11581592, by rfl⟩ : syracuseStep 15442123 = 23163185) B23163185
theorem B20589497 : Blo 2141435 20589497 := bstep (se 2 (by rfl) ⟨7721061, by rfl⟩ : syracuseStep 20589497 = 15442123) B15442123
theorem B13726331 : Blo 2141435 13726331 := bstep (se 1 (by rfl) ⟨10294748, by rfl⟩ : syracuseStep 13726331 = 20589497) B20589497
theorem B9150887 : Blo 2141435 9150887 := bstep (se 1 (by rfl) ⟨6863165, by rfl⟩ : syracuseStep 9150887 = 13726331) B13726331
theorem B6100591 : Blo 2141435 6100591 := bstep (se 1 (by rfl) ⟨4575443, by rfl⟩ : syracuseStep 6100591 = 9150887) B9150887
theorem B8134121 : Blo 2141435 8134121 := bstep (se 2 (by rfl) ⟨3050295, by rfl⟩ : syracuseStep 8134121 = 6100591) B6100591
theorem B5422747 : Blo 2141435 5422747 := bstep (se 1 (by rfl) ⟨4067060, by rfl⟩ : syracuseStep 5422747 = 8134121) B8134121
theorem B7230329 : Blo 2141435 7230329 := bstep (se 2 (by rfl) ⟨2711373, by rfl⟩ : syracuseStep 7230329 = 5422747) B5422747
theorem B4820219 : Blo 2141435 4820219 := bstep (se 1 (by rfl) ⟨3615164, by rfl⟩ : syracuseStep 4820219 = 7230329) B7230329
theorem B3213479 : Blo 2141435 3213479 := bstep (se 1 (by rfl) ⟨2410109, by rfl⟩ : syracuseStep 3213479 = 4820219) B4820219
theorem B2142319 : Blo 2141435 2142319 := bstep (se 1 (by rfl) ⟨1606739, by rfl⟩ : syracuseStep 2142319 = 3213479) B3213479
theorem B3213485 : Blo 2141435 3213485 := bbase (se 3 (by rfl) ⟨602528, by rfl⟩ : syracuseStep 3213485 = 1205057) (by norm_num)
theorem B2142323 : Blo 2141435 2142323 := bstep (se 1 (by rfl) ⟨1606742, by rfl⟩ : syracuseStep 2142323 = 3213485) B3213485
theorem B4820237 : Blo 2141435 4820237 := bbase (se 3 (by rfl) ⟨903794, by rfl⟩ : syracuseStep 4820237 = 1807589) (by norm_num)
theorem B3213491 : Blo 2141435 3213491 := bstep (se 1 (by rfl) ⟨2410118, by rfl⟩ : syracuseStep 3213491 = 4820237) B4820237
theorem B2142327 : Blo 2141435 2142327 := bstep (se 1 (by rfl) ⟨1606745, by rfl⟩ : syracuseStep 2142327 = 3213491) B3213491
theorem B2711389 : Blo 2141435 2711389 := bbase (se 3 (by rfl) ⟨508385, by rfl⟩ : syracuseStep 2711389 = 1016771) (by norm_num)
theorem B3615185 : Blo 2141435 3615185 := bstep (se 2 (by rfl) ⟨1355694, by rfl⟩ : syracuseStep 3615185 = 2711389) B2711389
theorem B2410123 : Blo 2141435 2410123 := bstep (se 1 (by rfl) ⟨1807592, by rfl⟩ : syracuseStep 2410123 = 3615185) B3615185
theorem B3213497 : Blo 2141435 3213497 := bstep (se 2 (by rfl) ⟨1205061, by rfl⟩ : syracuseStep 3213497 = 2410123) B2410123
theorem B2142331 : Blo 2141435 2142331 := bstep (se 1 (by rfl) ⟨1606748, by rfl⟩ : syracuseStep 2142331 = 3213497) B3213497
theorem B18301909 : Blo 2141435 18301909 := bbase (se 7 (by rfl) ⟨214475, by rfl⟩ : syracuseStep 18301909 = 428951) (by norm_num)
theorem B24402545 : Blo 2141435 24402545 := bstep (se 2 (by rfl) ⟨9150954, by rfl⟩ : syracuseStep 24402545 = 18301909) B18301909
theorem B16268363 : Blo 2141435 16268363 := bstep (se 1 (by rfl) ⟨12201272, by rfl⟩ : syracuseStep 16268363 = 24402545) B24402545
theorem B10845575 : Blo 2141435 10845575 := bstep (se 1 (by rfl) ⟨8134181, by rfl⟩ : syracuseStep 10845575 = 16268363) B16268363
theorem B7230383 : Blo 2141435 7230383 := bstep (se 1 (by rfl) ⟨5422787, by rfl⟩ : syracuseStep 7230383 = 10845575) B10845575
theorem B4820255 : Blo 2141435 4820255 := bstep (se 1 (by rfl) ⟨3615191, by rfl⟩ : syracuseStep 4820255 = 7230383) B7230383
theorem B3213503 : Blo 2141435 3213503 := bstep (se 1 (by rfl) ⟨2410127, by rfl⟩ : syracuseStep 3213503 = 4820255) B4820255
theorem B2142335 : Blo 2141435 2142335 := bstep (se 1 (by rfl) ⟨1606751, by rfl⟩ : syracuseStep 2142335 = 3213503) B3213503
theorem B3213509 : Blo 2141435 3213509 := bbase (se 4 (by rfl) ⟨301266, by rfl⟩ : syracuseStep 3213509 = 602533) (by norm_num)
theorem B2142339 : Blo 2141435 2142339 := bstep (se 1 (by rfl) ⟨1606754, by rfl⟩ : syracuseStep 2142339 = 3213509) B3213509
theorem B3615205 : Blo 2141435 3615205 := bbase (se 4 (by rfl) ⟨338925, by rfl⟩ : syracuseStep 3615205 = 677851) (by norm_num)
theorem B4820273 : Blo 2141435 4820273 := bstep (se 2 (by rfl) ⟨1807602, by rfl⟩ : syracuseStep 4820273 = 3615205) B3615205
theorem B3213515 : Blo 2141435 3213515 := bstep (se 1 (by rfl) ⟨2410136, by rfl⟩ : syracuseStep 3213515 = 4820273) B4820273
theorem B2142343 : Blo 2141435 2142343 := bstep (se 1 (by rfl) ⟨1606757, by rfl⟩ : syracuseStep 2142343 = 3213515) B3213515
theorem B2410141 : Blo 2141435 2410141 := bbase (se 3 (by rfl) ⟨451901, by rfl⟩ : syracuseStep 2410141 = 903803) (by norm_num)
theorem B3213521 : Blo 2141435 3213521 := bstep (se 2 (by rfl) ⟨1205070, by rfl⟩ : syracuseStep 3213521 = 2410141) B2410141
theorem B2142347 : Blo 2141435 2142347 := bstep (se 1 (by rfl) ⟨1606760, by rfl⟩ : syracuseStep 2142347 = 3213521) B3213521
theorem B7230437 : Blo 2141435 7230437 := bbase (se 4 (by rfl) ⟨677853, by rfl⟩ : syracuseStep 7230437 = 1355707) (by norm_num)
theorem B4820291 : Blo 2141435 4820291 := bstep (se 1 (by rfl) ⟨3615218, by rfl⟩ : syracuseStep 4820291 = 7230437) B7230437
theorem B3213527 : Blo 2141435 3213527 := bstep (se 1 (by rfl) ⟨2410145, by rfl⟩ : syracuseStep 3213527 = 4820291) B4820291
theorem B2142351 : Blo 2141435 2142351 := bstep (se 1 (by rfl) ⟨1606763, by rfl⟩ : syracuseStep 2142351 = 3213527) B3213527
theorem B3213533 : Blo 2141435 3213533 := bbase (se 3 (by rfl) ⟨602537, by rfl⟩ : syracuseStep 3213533 = 1205075) (by norm_num)
theorem B2142355 : Blo 2141435 2142355 := bstep (se 1 (by rfl) ⟨1606766, by rfl⟩ : syracuseStep 2142355 = 3213533) B3213533
theorem B4820309 : Blo 2141435 4820309 := bbase (se 11 (by rfl) ⟨3530, by rfl⟩ : syracuseStep 4820309 = 7061) (by norm_num)
theorem B3213539 : Blo 2141435 3213539 := bstep (se 1 (by rfl) ⟨2410154, by rfl⟩ : syracuseStep 3213539 = 4820309) B4820309
theorem B2142359 : Blo 2141435 2142359 := bstep (se 1 (by rfl) ⟨1606769, by rfl⟩ : syracuseStep 2142359 = 3213539) B3213539
theorem B2287769 : Blo 2141435 2287769 := bbase (se 2 (by rfl) ⟨857913, by rfl⟩ : syracuseStep 2287769 = 1715827) (by norm_num)
theorem B6100717 : Blo 2141435 6100717 := bstep (se 3 (by rfl) ⟨1143884, by rfl⟩ : syracuseStep 6100717 = 2287769) B2287769
theorem B8134289 : Blo 2141435 8134289 := bstep (se 2 (by rfl) ⟨3050358, by rfl⟩ : syracuseStep 8134289 = 6100717) B6100717
theorem B5422859 : Blo 2141435 5422859 := bstep (se 1 (by rfl) ⟨4067144, by rfl⟩ : syracuseStep 5422859 = 8134289) B8134289
theorem B3615239 : Blo 2141435 3615239 := bstep (se 1 (by rfl) ⟨2711429, by rfl⟩ : syracuseStep 3615239 = 5422859) B5422859
theorem B2410159 : Blo 2141435 2410159 := bstep (se 1 (by rfl) ⟨1807619, by rfl⟩ : syracuseStep 2410159 = 3615239) B3615239
theorem B3213545 : Blo 2141435 3213545 := bstep (se 2 (by rfl) ⟨1205079, by rfl⟩ : syracuseStep 3213545 = 2410159) B2410159
theorem B2142363 : Blo 2141435 2142363 := bstep (se 1 (by rfl) ⟨1606772, by rfl⟩ : syracuseStep 2142363 = 3213545) B3213545
theorem B2201225 : Blo 2141435 2201225 := bbase (se 2 (by rfl) ⟨825459, by rfl⟩ : syracuseStep 2201225 = 1650919) (by norm_num)
theorem B23479733 : Blo 2141435 23479733 := bstep (se 5 (by rfl) ⟨1100612, by rfl⟩ : syracuseStep 23479733 = 2201225) B2201225
theorem B15653155 : Blo 2141435 15653155 := bstep (se 1 (by rfl) ⟨11739866, by rfl⟩ : syracuseStep 15653155 = 23479733) B23479733
theorem B20870873 : Blo 2141435 20870873 := bstep (se 2 (by rfl) ⟨7826577, by rfl⟩ : syracuseStep 20870873 = 15653155) B15653155
theorem B13913915 : Blo 2141435 13913915 := bstep (se 1 (by rfl) ⟨10435436, by rfl⟩ : syracuseStep 13913915 = 20870873) B20870873
theorem B37103773 : Blo 2141435 37103773 := bstep (se 3 (by rfl) ⟨6956957, by rfl⟩ : syracuseStep 37103773 = 13913915) B13913915
theorem B49471697 : Blo 2141435 49471697 := bstep (se 2 (by rfl) ⟨18551886, by rfl⟩ : syracuseStep 49471697 = 37103773) B37103773
theorem B32981131 : Blo 2141435 32981131 := bstep (se 1 (by rfl) ⟨24735848, by rfl⟩ : syracuseStep 32981131 = 49471697) B49471697
theorem B43974841 : Blo 2141435 43974841 := bstep (se 2 (by rfl) ⟨16490565, by rfl⟩ : syracuseStep 43974841 = 32981131) B32981131
theorem B58633121 : Blo 2141435 58633121 := bstep (se 2 (by rfl) ⟨21987420, by rfl⟩ : syracuseStep 58633121 = 43974841) B43974841
theorem B39088747 : Blo 2141435 39088747 := bstep (se 1 (by rfl) ⟨29316560, by rfl⟩ : syracuseStep 39088747 = 58633121) B58633121
theorem B52118329 : Blo 2141435 52118329 := bstep (se 2 (by rfl) ⟨19544373, by rfl⟩ : syracuseStep 52118329 = 39088747) B39088747
theorem B69491105 : Blo 2141435 69491105 := bstep (se 2 (by rfl) ⟨26059164, by rfl⟩ : syracuseStep 69491105 = 52118329) B52118329
theorem B46327403 : Blo 2141435 46327403 := bstep (se 1 (by rfl) ⟨34745552, by rfl⟩ : syracuseStep 46327403 = 69491105) B69491105
theorem B30884935 : Blo 2141435 30884935 := bstep (se 1 (by rfl) ⟨23163701, by rfl⟩ : syracuseStep 30884935 = 46327403) B46327403
theorem B41179913 : Blo 2141435 41179913 := bstep (se 2 (by rfl) ⟨15442467, by rfl⟩ : syracuseStep 41179913 = 30884935) B30884935
theorem B27453275 : Blo 2141435 27453275 := bstep (se 1 (by rfl) ⟨20589956, by rfl⟩ : syracuseStep 27453275 = 41179913) B41179913
theorem B18302183 : Blo 2141435 18302183 := bstep (se 1 (by rfl) ⟨13726637, by rfl⟩ : syracuseStep 18302183 = 27453275) B27453275
theorem B12201455 : Blo 2141435 12201455 := bstep (se 1 (by rfl) ⟨9151091, by rfl⟩ : syracuseStep 12201455 = 18302183) B18302183
theorem B8134303 : Blo 2141435 8134303 := bstep (se 1 (by rfl) ⟨6100727, by rfl⟩ : syracuseStep 8134303 = 12201455) B12201455
theorem B10845737 : Blo 2141435 10845737 := bstep (se 2 (by rfl) ⟨4067151, by rfl⟩ : syracuseStep 10845737 = 8134303) B8134303
theorem B7230491 : Blo 2141435 7230491 := bstep (se 1 (by rfl) ⟨5422868, by rfl⟩ : syracuseStep 7230491 = 10845737) B10845737
theorem B4820327 : Blo 2141435 4820327 := bstep (se 1 (by rfl) ⟨3615245, by rfl⟩ : syracuseStep 4820327 = 7230491) B7230491
theorem B3213551 : Blo 2141435 3213551 := bstep (se 1 (by rfl) ⟨2410163, by rfl⟩ : syracuseStep 3213551 = 4820327) B4820327
theorem B2142367 : Blo 2141435 2142367 := bstep (se 1 (by rfl) ⟨1606775, by rfl⟩ : syracuseStep 2142367 = 3213551) B3213551
theorem B3213557 : Blo 2141435 3213557 := bbase (se 5 (by rfl) ⟨150635, by rfl⟩ : syracuseStep 3213557 = 301271) (by norm_num)
theorem B2142371 : Blo 2141435 2142371 := bstep (se 1 (by rfl) ⟨1606778, by rfl⟩ : syracuseStep 2142371 = 3213557) B3213557
theorem B20590037 : Blo 2141435 20590037 := bbase (se 7 (by rfl) ⟨241289, by rfl⟩ : syracuseStep 20590037 = 482579) (by norm_num)
theorem B13726691 : Blo 2141435 13726691 := bstep (se 1 (by rfl) ⟨10295018, by rfl⟩ : syracuseStep 13726691 = 20590037) B20590037
theorem B9151127 : Blo 2141435 9151127 := bstep (se 1 (by rfl) ⟨6863345, by rfl⟩ : syracuseStep 9151127 = 13726691) B13726691
theorem B6100751 : Blo 2141435 6100751 := bstep (se 1 (by rfl) ⟨4575563, by rfl⟩ : syracuseStep 6100751 = 9151127) B9151127
theorem B4067167 : Blo 2141435 4067167 := bstep (se 1 (by rfl) ⟨3050375, by rfl⟩ : syracuseStep 4067167 = 6100751) B6100751
theorem B5422889 : Blo 2141435 5422889 := bstep (se 2 (by rfl) ⟨2033583, by rfl⟩ : syracuseStep 5422889 = 4067167) B4067167
theorem B3615259 : Blo 2141435 3615259 := bstep (se 1 (by rfl) ⟨2711444, by rfl⟩ : syracuseStep 3615259 = 5422889) B5422889
theorem B4820345 : Blo 2141435 4820345 := bstep (se 2 (by rfl) ⟨1807629, by rfl⟩ : syracuseStep 4820345 = 3615259) B3615259
theorem B3213563 : Blo 2141435 3213563 := bstep (se 1 (by rfl) ⟨2410172, by rfl⟩ : syracuseStep 3213563 = 4820345) B4820345
theorem B2142375 : Blo 2141435 2142375 := bstep (se 1 (by rfl) ⟨1606781, by rfl⟩ : syracuseStep 2142375 = 3213563) B3213563
theorem B2410177 : Blo 2141435 2410177 := bbase (se 2 (by rfl) ⟨903816, by rfl⟩ : syracuseStep 2410177 = 1807633) (by norm_num)
theorem B3213569 : Blo 2141435 3213569 := bstep (se 2 (by rfl) ⟨1205088, by rfl⟩ : syracuseStep 3213569 = 2410177) B2410177
theorem B2142379 : Blo 2141435 2142379 := bstep (se 1 (by rfl) ⟨1606784, by rfl⟩ : syracuseStep 2142379 = 3213569) B3213569
theorem B5422909 : Blo 2141435 5422909 := bbase (se 3 (by rfl) ⟨1016795, by rfl⟩ : syracuseStep 5422909 = 2033591) (by norm_num)
theorem B7230545 : Blo 2141435 7230545 := bstep (se 2 (by rfl) ⟨2711454, by rfl⟩ : syracuseStep 7230545 = 5422909) B5422909
theorem B4820363 : Blo 2141435 4820363 := bstep (se 1 (by rfl) ⟨3615272, by rfl⟩ : syracuseStep 4820363 = 7230545) B7230545
theorem B3213575 : Blo 2141435 3213575 := bstep (se 1 (by rfl) ⟨2410181, by rfl⟩ : syracuseStep 3213575 = 4820363) B4820363
theorem B2142383 : Blo 2141435 2142383 := bstep (se 1 (by rfl) ⟨1606787, by rfl⟩ : syracuseStep 2142383 = 3213575) B3213575
theorem B3213581 : Blo 2141435 3213581 := bbase (se 3 (by rfl) ⟨602546, by rfl⟩ : syracuseStep 3213581 = 1205093) (by norm_num)
theorem B2142387 : Blo 2141435 2142387 := bstep (se 1 (by rfl) ⟨1606790, by rfl⟩ : syracuseStep 2142387 = 3213581) B3213581
theorem B4820381 : Blo 2141435 4820381 := bbase (se 3 (by rfl) ⟨903821, by rfl⟩ : syracuseStep 4820381 = 1807643) (by norm_num)
theorem B3213587 : Blo 2141435 3213587 := bstep (se 1 (by rfl) ⟨2410190, by rfl⟩ : syracuseStep 3213587 = 4820381) B4820381
theorem B2142391 : Blo 2141435 2142391 := bstep (se 1 (by rfl) ⟨1606793, by rfl⟩ : syracuseStep 2142391 = 3213587) B3213587
theorem B3615293 : Blo 2141435 3615293 := bbase (se 3 (by rfl) ⟨677867, by rfl⟩ : syracuseStep 3615293 = 1355735) (by norm_num)
theorem B2410195 : Blo 2141435 2410195 := bstep (se 1 (by rfl) ⟨1807646, by rfl⟩ : syracuseStep 2410195 = 3615293) B3615293
theorem B3213593 : Blo 2141435 3213593 := bstep (se 2 (by rfl) ⟨1205097, by rfl⟩ : syracuseStep 3213593 = 2410195) B2410195
theorem B2142395 : Blo 2141435 2142395 := bstep (se 1 (by rfl) ⟨1606796, by rfl⟩ : syracuseStep 2142395 = 3213593) B3213593
theorem B13029781 : Blo 2141435 13029781 := bbase (se 6 (by rfl) ⟨305385, by rfl⟩ : syracuseStep 13029781 = 610771) (by norm_num)
theorem B17373041 : Blo 2141435 17373041 := bstep (se 2 (by rfl) ⟨6514890, by rfl⟩ : syracuseStep 17373041 = 13029781) B13029781
theorem B11582027 : Blo 2141435 11582027 := bstep (se 1 (by rfl) ⟨8686520, by rfl⟩ : syracuseStep 11582027 = 17373041) B17373041
theorem B7721351 : Blo 2141435 7721351 := bstep (se 1 (by rfl) ⟨5791013, by rfl⟩ : syracuseStep 7721351 = 11582027) B11582027
theorem B5147567 : Blo 2141435 5147567 := bstep (se 1 (by rfl) ⟨3860675, by rfl⟩ : syracuseStep 5147567 = 7721351) B7721351
theorem B3431711 : Blo 2141435 3431711 := bstep (se 1 (by rfl) ⟨2573783, by rfl⟩ : syracuseStep 3431711 = 5147567) B5147567
theorem B2287807 : Blo 2141435 2287807 := bstep (se 1 (by rfl) ⟨1715855, by rfl⟩ : syracuseStep 2287807 = 3431711) B3431711
theorem B12201637 : Blo 2141435 12201637 := bstep (se 4 (by rfl) ⟨1143903, by rfl⟩ : syracuseStep 12201637 = 2287807) B2287807
theorem B16268849 : Blo 2141435 16268849 := bstep (se 2 (by rfl) ⟨6100818, by rfl⟩ : syracuseStep 16268849 = 12201637) B12201637
theorem B10845899 : Blo 2141435 10845899 := bstep (se 1 (by rfl) ⟨8134424, by rfl⟩ : syracuseStep 10845899 = 16268849) B16268849
theorem B7230599 : Blo 2141435 7230599 := bstep (se 1 (by rfl) ⟨5422949, by rfl⟩ : syracuseStep 7230599 = 10845899) B10845899
theorem B4820399 : Blo 2141435 4820399 := bstep (se 1 (by rfl) ⟨3615299, by rfl⟩ : syracuseStep 4820399 = 7230599) B7230599
theorem B3213599 : Blo 2141435 3213599 := bstep (se 1 (by rfl) ⟨2410199, by rfl⟩ : syracuseStep 3213599 = 4820399) B4820399
theorem B2142399 : Blo 2141435 2142399 := bstep (se 1 (by rfl) ⟨1606799, by rfl⟩ : syracuseStep 2142399 = 3213599) B3213599
theorem B3213605 : Blo 2141435 3213605 := bbase (se 4 (by rfl) ⟨301275, by rfl⟩ : syracuseStep 3213605 = 602551) (by norm_num)
theorem B2142403 : Blo 2141435 2142403 := bstep (se 1 (by rfl) ⟨1606802, by rfl⟩ : syracuseStep 2142403 = 3213605) B3213605
theorem B2711485 : Blo 2141435 2711485 := bbase (se 3 (by rfl) ⟨508403, by rfl⟩ : syracuseStep 2711485 = 1016807) (by norm_num)
theorem B3615313 : Blo 2141435 3615313 := bstep (se 2 (by rfl) ⟨1355742, by rfl⟩ : syracuseStep 3615313 = 2711485) B2711485
theorem B4820417 : Blo 2141435 4820417 := bstep (se 2 (by rfl) ⟨1807656, by rfl⟩ : syracuseStep 4820417 = 3615313) B3615313
theorem B3213611 : Blo 2141435 3213611 := bstep (se 1 (by rfl) ⟨2410208, by rfl⟩ : syracuseStep 3213611 = 4820417) B4820417
theorem B2142407 : Blo 2141435 2142407 := bstep (se 1 (by rfl) ⟨1606805, by rfl⟩ : syracuseStep 2142407 = 3213611) B3213611
theorem B2410213 : Blo 2141435 2410213 := bbase (se 4 (by rfl) ⟨225957, by rfl⟩ : syracuseStep 2410213 = 451915) (by norm_num)
theorem B3213617 : Blo 2141435 3213617 := bstep (se 2 (by rfl) ⟨1205106, by rfl⟩ : syracuseStep 3213617 = 2410213) B2410213
theorem B2142411 : Blo 2141435 2142411 := bstep (se 1 (by rfl) ⟨1606808, by rfl⟩ : syracuseStep 2142411 = 3213617) B3213617
theorem B3526021 : Blo 2141435 3526021 := bbase (se 4 (by rfl) ⟨330564, by rfl⟩ : syracuseStep 3526021 = 661129) (by norm_num)
theorem B18805445 : Blo 2141435 18805445 := bstep (se 4 (by rfl) ⟨1763010, by rfl⟩ : syracuseStep 18805445 = 3526021) B3526021
theorem B12536963 : Blo 2141435 12536963 := bstep (se 1 (by rfl) ⟨9402722, by rfl⟩ : syracuseStep 12536963 = 18805445) B18805445
theorem B8357975 : Blo 2141435 8357975 := bstep (se 1 (by rfl) ⟨6268481, by rfl⟩ : syracuseStep 8357975 = 12536963) B12536963
theorem B5571983 : Blo 2141435 5571983 := bstep (se 1 (by rfl) ⟨4178987, by rfl⟩ : syracuseStep 5571983 = 8357975) B8357975
theorem B3714655 : Blo 2141435 3714655 := bstep (se 1 (by rfl) ⟨2785991, by rfl⟩ : syracuseStep 3714655 = 5571983) B5571983
theorem B4952873 : Blo 2141435 4952873 := bstep (se 2 (by rfl) ⟨1857327, by rfl⟩ : syracuseStep 4952873 = 3714655) B3714655
theorem B3301915 : Blo 2141435 3301915 := bstep (se 1 (by rfl) ⟨2476436, by rfl⟩ : syracuseStep 3301915 = 4952873) B4952873
theorem B4402553 : Blo 2141435 4402553 := bstep (se 2 (by rfl) ⟨1650957, by rfl⟩ : syracuseStep 4402553 = 3301915) B3301915
theorem B11740141 : Blo 2141435 11740141 := bstep (se 3 (by rfl) ⟨2201276, by rfl⟩ : syracuseStep 11740141 = 4402553) B4402553
theorem B15653521 : Blo 2141435 15653521 := bstep (se 2 (by rfl) ⟨5870070, by rfl⟩ : syracuseStep 15653521 = 11740141) B11740141
theorem B20871361 : Blo 2141435 20871361 := bstep (se 2 (by rfl) ⟨7826760, by rfl⟩ : syracuseStep 20871361 = 15653521) B15653521
theorem B27828481 : Blo 2141435 27828481 := bstep (se 2 (by rfl) ⟨10435680, by rfl⟩ : syracuseStep 27828481 = 20871361) B20871361
theorem B37104641 : Blo 2141435 37104641 := bstep (se 2 (by rfl) ⟨13914240, by rfl⟩ : syracuseStep 37104641 = 27828481) B27828481
theorem B24736427 : Blo 2141435 24736427 := bstep (se 1 (by rfl) ⟨18552320, by rfl⟩ : syracuseStep 24736427 = 37104641) B37104641
theorem B16490951 : Blo 2141435 16490951 := bstep (se 1 (by rfl) ⟨12368213, by rfl⟩ : syracuseStep 16490951 = 24736427) B24736427
theorem B10993967 : Blo 2141435 10993967 := bstep (se 1 (by rfl) ⟨8245475, by rfl⟩ : syracuseStep 10993967 = 16490951) B16490951
theorem B7329311 : Blo 2141435 7329311 := bstep (se 1 (by rfl) ⟨5496983, by rfl⟩ : syracuseStep 7329311 = 10993967) B10993967
theorem B4886207 : Blo 2141435 4886207 := bstep (se 1 (by rfl) ⟨3664655, by rfl⟩ : syracuseStep 4886207 = 7329311) B7329311
theorem B3257471 : Blo 2141435 3257471 := bstep (se 1 (by rfl) ⟨2443103, by rfl⟩ : syracuseStep 3257471 = 4886207) B4886207
theorem B2171647 : Blo 2141435 2171647 := bstep (se 1 (by rfl) ⟨1628735, by rfl⟩ : syracuseStep 2171647 = 3257471) B3257471
theorem B2895529 : Blo 2141435 2895529 := bstep (se 2 (by rfl) ⟨1085823, by rfl⟩ : syracuseStep 2895529 = 2171647) B2171647
theorem B3860705 : Blo 2141435 3860705 := bstep (se 2 (by rfl) ⟨1447764, by rfl⟩ : syracuseStep 3860705 = 2895529) B2895529
theorem B2573803 : Blo 2141435 2573803 := bstep (se 1 (by rfl) ⟨1930352, by rfl⟩ : syracuseStep 2573803 = 3860705) B3860705
theorem B3431737 : Blo 2141435 3431737 := bstep (se 2 (by rfl) ⟨1286901, by rfl⟩ : syracuseStep 3431737 = 2573803) B2573803
theorem B4575649 : Blo 2141435 4575649 := bstep (se 2 (by rfl) ⟨1715868, by rfl⟩ : syracuseStep 4575649 = 3431737) B3431737
theorem B6100865 : Blo 2141435 6100865 := bstep (se 2 (by rfl) ⟨2287824, by rfl⟩ : syracuseStep 6100865 = 4575649) B4575649
theorem B4067243 : Blo 2141435 4067243 := bstep (se 1 (by rfl) ⟨3050432, by rfl⟩ : syracuseStep 4067243 = 6100865) B6100865
theorem B2711495 : Blo 2141435 2711495 := bstep (se 1 (by rfl) ⟨2033621, by rfl⟩ : syracuseStep 2711495 = 4067243) B4067243
theorem B7230653 : Blo 2141435 7230653 := bstep (se 3 (by rfl) ⟨1355747, by rfl⟩ : syracuseStep 7230653 = 2711495) B2711495
theorem B4820435 : Blo 2141435 4820435 := bstep (se 1 (by rfl) ⟨3615326, by rfl⟩ : syracuseStep 4820435 = 7230653) B7230653
theorem B3213623 : Blo 2141435 3213623 := bstep (se 1 (by rfl) ⟨2410217, by rfl⟩ : syracuseStep 3213623 = 4820435) B4820435
theorem B2142415 : Blo 2141435 2142415 := bstep (se 1 (by rfl) ⟨1606811, by rfl⟩ : syracuseStep 2142415 = 3213623) B3213623
theorem B3213629 : Blo 2141435 3213629 := bbase (se 3 (by rfl) ⟨602555, by rfl⟩ : syracuseStep 3213629 = 1205111) (by norm_num)
theorem B2142419 : Blo 2141435 2142419 := bstep (se 1 (by rfl) ⟨1606814, by rfl⟩ : syracuseStep 2142419 = 3213629) B3213629
theorem B4820453 : Blo 2141435 4820453 := bbase (se 4 (by rfl) ⟨451917, by rfl⟩ : syracuseStep 4820453 = 903835) (by norm_num)
theorem B3213635 : Blo 2141435 3213635 := bstep (se 1 (by rfl) ⟨2410226, by rfl⟩ : syracuseStep 3213635 = 4820453) B4820453
theorem B2142423 : Blo 2141435 2142423 := bstep (se 1 (by rfl) ⟨1606817, by rfl⟩ : syracuseStep 2142423 = 3213635) B3213635
theorem B5423021 : Blo 2141435 5423021 := bbase (se 3 (by rfl) ⟨1016816, by rfl⟩ : syracuseStep 5423021 = 2033633) (by norm_num)
theorem B3615347 : Blo 2141435 3615347 := bstep (se 1 (by rfl) ⟨2711510, by rfl⟩ : syracuseStep 3615347 = 5423021) B5423021
theorem B2410231 : Blo 2141435 2410231 := bstep (se 1 (by rfl) ⟨1807673, by rfl⟩ : syracuseStep 2410231 = 3615347) B3615347
theorem B3213641 : Blo 2141435 3213641 := bstep (se 2 (by rfl) ⟨1205115, by rfl⟩ : syracuseStep 3213641 = 2410231) B2410231
theorem B2142427 : Blo 2141435 2142427 := bstep (se 1 (by rfl) ⟨1606820, by rfl⟩ : syracuseStep 2142427 = 3213641) B3213641
theorem B6863525 : Blo 2141435 6863525 := bbase (se 4 (by rfl) ⟨643455, by rfl⟩ : syracuseStep 6863525 = 1286911) (by norm_num)
theorem B4575683 : Blo 2141435 4575683 := bstep (se 1 (by rfl) ⟨3431762, by rfl⟩ : syracuseStep 4575683 = 6863525) B6863525
theorem B3050455 : Blo 2141435 3050455 := bstep (se 1 (by rfl) ⟨2287841, by rfl⟩ : syracuseStep 3050455 = 4575683) B4575683
theorem B4067273 : Blo 2141435 4067273 := bstep (se 2 (by rfl) ⟨1525227, by rfl⟩ : syracuseStep 4067273 = 3050455) B3050455
theorem B10846061 : Blo 2141435 10846061 := bstep (se 3 (by rfl) ⟨2033636, by rfl⟩ : syracuseStep 10846061 = 4067273) B4067273
theorem B7230707 : Blo 2141435 7230707 := bstep (se 1 (by rfl) ⟨5423030, by rfl⟩ : syracuseStep 7230707 = 10846061) B10846061
theorem B4820471 : Blo 2141435 4820471 := bstep (se 1 (by rfl) ⟨3615353, by rfl⟩ : syracuseStep 4820471 = 7230707) B7230707
theorem B3213647 : Blo 2141435 3213647 := bstep (se 1 (by rfl) ⟨2410235, by rfl⟩ : syracuseStep 3213647 = 4820471) B4820471
theorem B2142431 : Blo 2141435 2142431 := bstep (se 1 (by rfl) ⟨1606823, by rfl⟩ : syracuseStep 2142431 = 3213647) B3213647
theorem B3213653 : Blo 2141435 3213653 := bbase (se 10 (by rfl) ⟨4707, by rfl⟩ : syracuseStep 3213653 = 9415) (by norm_num)
theorem B2142435 : Blo 2141435 2142435 := bstep (se 1 (by rfl) ⟨1606826, by rfl⟩ : syracuseStep 2142435 = 3213653) B3213653
theorem B6100933 : Blo 2141435 6100933 := bbase (se 4 (by rfl) ⟨571962, by rfl⟩ : syracuseStep 6100933 = 1143925) (by norm_num)
theorem B8134577 : Blo 2141435 8134577 := bstep (se 2 (by rfl) ⟨3050466, by rfl⟩ : syracuseStep 8134577 = 6100933) B6100933
theorem B5423051 : Blo 2141435 5423051 := bstep (se 1 (by rfl) ⟨4067288, by rfl⟩ : syracuseStep 5423051 = 8134577) B8134577
theorem B3615367 : Blo 2141435 3615367 := bstep (se 1 (by rfl) ⟨2711525, by rfl⟩ : syracuseStep 3615367 = 5423051) B5423051
theorem B4820489 : Blo 2141435 4820489 := bstep (se 2 (by rfl) ⟨1807683, by rfl⟩ : syracuseStep 4820489 = 3615367) B3615367
theorem B3213659 : Blo 2141435 3213659 := bstep (se 1 (by rfl) ⟨2410244, by rfl⟩ : syracuseStep 3213659 = 4820489) B4820489
theorem B2142439 : Blo 2141435 2142439 := bstep (se 1 (by rfl) ⟨1606829, by rfl⟩ : syracuseStep 2142439 = 3213659) B3213659
theorem B2410249 : Blo 2141435 2410249 := bbase (se 2 (by rfl) ⟨903843, by rfl⟩ : syracuseStep 2410249 = 1807687) (by norm_num)
theorem B3213665 : Blo 2141435 3213665 := bstep (se 2 (by rfl) ⟨1205124, by rfl⟩ : syracuseStep 3213665 = 2410249) B2410249
theorem B2142443 : Blo 2141435 2142443 := bstep (se 1 (by rfl) ⟨1606832, by rfl⟩ : syracuseStep 2142443 = 3213665) B3213665
theorem B4343357 : Blo 2141435 4343357 := bbase (se 3 (by rfl) ⟨814379, by rfl⟩ : syracuseStep 4343357 = 1628759) (by norm_num)
theorem B2895571 : Blo 2141435 2895571 := bstep (se 1 (by rfl) ⟨2171678, by rfl⟩ : syracuseStep 2895571 = 4343357) B4343357
theorem B15443045 : Blo 2141435 15443045 := bstep (se 4 (by rfl) ⟨1447785, by rfl⟩ : syracuseStep 15443045 = 2895571) B2895571
theorem B10295363 : Blo 2141435 10295363 := bstep (se 1 (by rfl) ⟨7721522, by rfl⟩ : syracuseStep 10295363 = 15443045) B15443045
theorem B27454301 : Blo 2141435 27454301 := bstep (se 3 (by rfl) ⟨5147681, by rfl⟩ : syracuseStep 27454301 = 10295363) B10295363
theorem B18302867 : Blo 2141435 18302867 := bstep (se 1 (by rfl) ⟨13727150, by rfl⟩ : syracuseStep 18302867 = 27454301) B27454301
theorem B12201911 : Blo 2141435 12201911 := bstep (se 1 (by rfl) ⟨9151433, by rfl⟩ : syracuseStep 12201911 = 18302867) B18302867
theorem B8134607 : Blo 2141435 8134607 := bstep (se 1 (by rfl) ⟨6100955, by rfl⟩ : syracuseStep 8134607 = 12201911) B12201911
theorem B5423071 : Blo 2141435 5423071 := bstep (se 1 (by rfl) ⟨4067303, by rfl⟩ : syracuseStep 5423071 = 8134607) B8134607
theorem B7230761 : Blo 2141435 7230761 := bstep (se 2 (by rfl) ⟨2711535, by rfl⟩ : syracuseStep 7230761 = 5423071) B5423071
theorem B4820507 : Blo 2141435 4820507 := bstep (se 1 (by rfl) ⟨3615380, by rfl⟩ : syracuseStep 4820507 = 7230761) B7230761
theorem B3213671 : Blo 2141435 3213671 := bstep (se 1 (by rfl) ⟨2410253, by rfl⟩ : syracuseStep 3213671 = 4820507) B4820507
theorem B2142447 : Blo 2141435 2142447 := bstep (se 1 (by rfl) ⟨1606835, by rfl⟩ : syracuseStep 2142447 = 3213671) B3213671
theorem B3213677 : Blo 2141435 3213677 := bbase (se 3 (by rfl) ⟨602564, by rfl⟩ : syracuseStep 3213677 = 1205129) (by norm_num)
theorem B2142451 : Blo 2141435 2142451 := bstep (se 1 (by rfl) ⟨1606838, by rfl⟩ : syracuseStep 2142451 = 3213677) B3213677
theorem B4820525 : Blo 2141435 4820525 := bbase (se 3 (by rfl) ⟨903848, by rfl⟩ : syracuseStep 4820525 = 1807697) (by norm_num)
theorem B3213683 : Blo 2141435 3213683 := bstep (se 1 (by rfl) ⟨2410262, by rfl⟩ : syracuseStep 3213683 = 4820525) B4820525
theorem B2142455 : Blo 2141435 2142455 := bstep (se 1 (by rfl) ⟨1606841, by rfl⟩ : syracuseStep 2142455 = 3213683) B3213683
theorem B13914517 : Blo 2141435 13914517 := bbase (se 6 (by rfl) ⟨326121, by rfl⟩ : syracuseStep 13914517 = 652243) (by norm_num)
theorem B18552689 : Blo 2141435 18552689 := bstep (se 2 (by rfl) ⟨6957258, by rfl⟩ : syracuseStep 18552689 = 13914517) B13914517
theorem B12368459 : Blo 2141435 12368459 := bstep (se 1 (by rfl) ⟨9276344, by rfl⟩ : syracuseStep 12368459 = 18552689) B18552689
theorem B32982557 : Blo 2141435 32982557 := bstep (se 3 (by rfl) ⟨6184229, by rfl⟩ : syracuseStep 32982557 = 12368459) B12368459
theorem B351813941 : Blo 2141435 351813941 := bstep (se 5 (by rfl) ⟨16491278, by rfl⟩ : syracuseStep 351813941 = 32982557) B32982557
theorem B234542627 : Blo 2141435 234542627 := bstep (se 1 (by rfl) ⟨175906970, by rfl⟩ : syracuseStep 234542627 = 351813941) B351813941
theorem B156361751 : Blo 2141435 156361751 := bstep (se 1 (by rfl) ⟨117271313, by rfl⟩ : syracuseStep 156361751 = 234542627) B234542627
theorem B104241167 : Blo 2141435 104241167 := bstep (se 1 (by rfl) ⟨78180875, by rfl⟩ : syracuseStep 104241167 = 156361751) B156361751
theorem B69494111 : Blo 2141435 69494111 := bstep (se 1 (by rfl) ⟨52120583, by rfl⟩ : syracuseStep 69494111 = 104241167) B104241167
theorem B46329407 : Blo 2141435 46329407 := bstep (se 1 (by rfl) ⟨34747055, by rfl⟩ : syracuseStep 46329407 = 69494111) B69494111
theorem B30886271 : Blo 2141435 30886271 := bstep (se 1 (by rfl) ⟨23164703, by rfl⟩ : syracuseStep 30886271 = 46329407) B46329407
theorem B20590847 : Blo 2141435 20590847 := bstep (se 1 (by rfl) ⟨15443135, by rfl⟩ : syracuseStep 20590847 = 30886271) B30886271
theorem B13727231 : Blo 2141435 13727231 := bstep (se 1 (by rfl) ⟨10295423, by rfl⟩ : syracuseStep 13727231 = 20590847) B20590847
theorem B9151487 : Blo 2141435 9151487 := bstep (se 1 (by rfl) ⟨6863615, by rfl⟩ : syracuseStep 9151487 = 13727231) B13727231
theorem B6100991 : Blo 2141435 6100991 := bstep (se 1 (by rfl) ⟨4575743, by rfl⟩ : syracuseStep 6100991 = 9151487) B9151487
theorem B4067327 : Blo 2141435 4067327 := bstep (se 1 (by rfl) ⟨3050495, by rfl⟩ : syracuseStep 4067327 = 6100991) B6100991
theorem B2711551 : Blo 2141435 2711551 := bstep (se 1 (by rfl) ⟨2033663, by rfl⟩ : syracuseStep 2711551 = 4067327) B4067327
theorem B3615401 : Blo 2141435 3615401 := bstep (se 2 (by rfl) ⟨1355775, by rfl⟩ : syracuseStep 3615401 = 2711551) B2711551
theorem B2410267 : Blo 2141435 2410267 := bstep (se 1 (by rfl) ⟨1807700, by rfl⟩ : syracuseStep 2410267 = 3615401) B3615401
theorem B3213689 : Blo 2141435 3213689 := bstep (se 2 (by rfl) ⟨1205133, by rfl⟩ : syracuseStep 3213689 = 2410267) B2410267
theorem B2142459 : Blo 2141435 2142459 := bstep (se 1 (by rfl) ⟨1606844, by rfl⟩ : syracuseStep 2142459 = 3213689) B3213689
theorem B3431813 : Blo 2141435 3431813 := bbase (se 4 (by rfl) ⟨321732, by rfl⟩ : syracuseStep 3431813 = 643465) (by norm_num)
theorem B36606005 : Blo 2141435 36606005 := bstep (se 5 (by rfl) ⟨1715906, by rfl⟩ : syracuseStep 36606005 = 3431813) B3431813
theorem B24404003 : Blo 2141435 24404003 := bstep (se 1 (by rfl) ⟨18303002, by rfl⟩ : syracuseStep 24404003 = 36606005) B36606005
theorem B16269335 : Blo 2141435 16269335 := bstep (se 1 (by rfl) ⟨12202001, by rfl⟩ : syracuseStep 16269335 = 24404003) B24404003
theorem B10846223 : Blo 2141435 10846223 := bstep (se 1 (by rfl) ⟨8134667, by rfl⟩ : syracuseStep 10846223 = 16269335) B16269335
theorem B7230815 : Blo 2141435 7230815 := bstep (se 1 (by rfl) ⟨5423111, by rfl⟩ : syracuseStep 7230815 = 10846223) B10846223
theorem B4820543 : Blo 2141435 4820543 := bstep (se 1 (by rfl) ⟨3615407, by rfl⟩ : syracuseStep 4820543 = 7230815) B7230815
theorem B3213695 : Blo 2141435 3213695 := bstep (se 1 (by rfl) ⟨2410271, by rfl⟩ : syracuseStep 3213695 = 4820543) B4820543
theorem B2142463 : Blo 2141435 2142463 := bstep (se 1 (by rfl) ⟨1606847, by rfl⟩ : syracuseStep 2142463 = 3213695) B3213695
theorem B3213701 : Blo 2141435 3213701 := bbase (se 4 (by rfl) ⟨301284, by rfl⟩ : syracuseStep 3213701 = 602569) (by norm_num)
theorem B2142467 : Blo 2141435 2142467 := bstep (se 1 (by rfl) ⟨1606850, by rfl⟩ : syracuseStep 2142467 = 3213701) B3213701
theorem B3615421 : Blo 2141435 3615421 := bbase (se 3 (by rfl) ⟨677891, by rfl⟩ : syracuseStep 3615421 = 1355783) (by norm_num)
theorem B4820561 : Blo 2141435 4820561 := bstep (se 2 (by rfl) ⟨1807710, by rfl⟩ : syracuseStep 4820561 = 3615421) B3615421
theorem B3213707 : Blo 2141435 3213707 := bstep (se 1 (by rfl) ⟨2410280, by rfl⟩ : syracuseStep 3213707 = 4820561) B4820561
theorem B2142471 : Blo 2141435 2142471 := bstep (se 1 (by rfl) ⟨1606853, by rfl⟩ : syracuseStep 2142471 = 3213707) B3213707
theorem B2410285 : Blo 2141435 2410285 := bbase (se 3 (by rfl) ⟨451928, by rfl⟩ : syracuseStep 2410285 = 903857) (by norm_num)
theorem B3213713 : Blo 2141435 3213713 := bstep (se 2 (by rfl) ⟨1205142, by rfl⟩ : syracuseStep 3213713 = 2410285) B2410285
theorem B2142475 : Blo 2141435 2142475 := bstep (se 1 (by rfl) ⟨1606856, by rfl⟩ : syracuseStep 2142475 = 3213713) B3213713
theorem B7230869 : Blo 2141435 7230869 := bbase (se 6 (by rfl) ⟨169473, by rfl⟩ : syracuseStep 7230869 = 338947) (by norm_num)
theorem B4820579 : Blo 2141435 4820579 := bstep (se 1 (by rfl) ⟨3615434, by rfl⟩ : syracuseStep 4820579 = 7230869) B7230869
theorem B3213719 : Blo 2141435 3213719 := bstep (se 1 (by rfl) ⟨2410289, by rfl⟩ : syracuseStep 3213719 = 4820579) B4820579
theorem B2142479 : Blo 2141435 2142479 := bstep (se 1 (by rfl) ⟨1606859, by rfl⟩ : syracuseStep 2142479 = 3213719) B3213719
theorem B3213725 : Blo 2141435 3213725 := bbase (se 3 (by rfl) ⟨602573, by rfl⟩ : syracuseStep 3213725 = 1205147) (by norm_num)
theorem B2142483 : Blo 2141435 2142483 := bstep (se 1 (by rfl) ⟨1606862, by rfl⟩ : syracuseStep 2142483 = 3213725) B3213725
theorem B4820597 : Blo 2141435 4820597 := bbase (se 5 (by rfl) ⟨225965, by rfl⟩ : syracuseStep 4820597 = 451931) (by norm_num)
theorem B3213731 : Blo 2141435 3213731 := bstep (se 1 (by rfl) ⟨2410298, by rfl⟩ : syracuseStep 3213731 = 4820597) B4820597
theorem B2142487 : Blo 2141435 2142487 := bstep (se 1 (by rfl) ⟨1606865, by rfl⟩ : syracuseStep 2142487 = 3213731) B3213731
theorem B6863717 : Blo 2141435 6863717 := bbase (se 4 (by rfl) ⟨643473, by rfl⟩ : syracuseStep 6863717 = 1286947) (by norm_num)
theorem B18303245 : Blo 2141435 18303245 := bstep (se 3 (by rfl) ⟨3431858, by rfl⟩ : syracuseStep 18303245 = 6863717) B6863717
theorem B12202163 : Blo 2141435 12202163 := bstep (se 1 (by rfl) ⟨9151622, by rfl⟩ : syracuseStep 12202163 = 18303245) B18303245
theorem B8134775 : Blo 2141435 8134775 := bstep (se 1 (by rfl) ⟨6101081, by rfl⟩ : syracuseStep 8134775 = 12202163) B12202163
theorem B5423183 : Blo 2141435 5423183 := bstep (se 1 (by rfl) ⟨4067387, by rfl⟩ : syracuseStep 5423183 = 8134775) B8134775
theorem B3615455 : Blo 2141435 3615455 := bstep (se 1 (by rfl) ⟨2711591, by rfl⟩ : syracuseStep 3615455 = 5423183) B5423183
theorem B2410303 : Blo 2141435 2410303 := bstep (se 1 (by rfl) ⟨1807727, by rfl⟩ : syracuseStep 2410303 = 3615455) B3615455
theorem B3213737 : Blo 2141435 3213737 := bstep (se 2 (by rfl) ⟨1205151, by rfl⟩ : syracuseStep 3213737 = 2410303) B2410303
theorem B2142491 : Blo 2141435 2142491 := bstep (se 1 (by rfl) ⟨1606868, by rfl⟩ : syracuseStep 2142491 = 3213737) B3213737
theorem B8134789 : Blo 2141435 8134789 := bbase (se 4 (by rfl) ⟨762636, by rfl⟩ : syracuseStep 8134789 = 1525273) (by norm_num)
theorem B10846385 : Blo 2141435 10846385 := bstep (se 2 (by rfl) ⟨4067394, by rfl⟩ : syracuseStep 10846385 = 8134789) B8134789
theorem B7230923 : Blo 2141435 7230923 := bstep (se 1 (by rfl) ⟨5423192, by rfl⟩ : syracuseStep 7230923 = 10846385) B10846385
theorem B4820615 : Blo 2141435 4820615 := bstep (se 1 (by rfl) ⟨3615461, by rfl⟩ : syracuseStep 4820615 = 7230923) B7230923
theorem B3213743 : Blo 2141435 3213743 := bstep (se 1 (by rfl) ⟨2410307, by rfl⟩ : syracuseStep 3213743 = 4820615) B4820615
theorem B2142495 : Blo 2141435 2142495 := bstep (se 1 (by rfl) ⟨1606871, by rfl⟩ : syracuseStep 2142495 = 3213743) B3213743
theorem B3213749 : Blo 2141435 3213749 := bbase (se 5 (by rfl) ⟨150644, by rfl⟩ : syracuseStep 3213749 = 301289) (by norm_num)
theorem B2142499 : Blo 2141435 2142499 := bstep (se 1 (by rfl) ⟨1606874, by rfl⟩ : syracuseStep 2142499 = 3213749) B3213749
theorem B5423213 : Blo 2141435 5423213 := bbase (se 3 (by rfl) ⟨1016852, by rfl⟩ : syracuseStep 5423213 = 2033705) (by norm_num)
theorem B3615475 : Blo 2141435 3615475 := bstep (se 1 (by rfl) ⟨2711606, by rfl⟩ : syracuseStep 3615475 = 5423213) B5423213
theorem B4820633 : Blo 2141435 4820633 := bstep (se 2 (by rfl) ⟨1807737, by rfl⟩ : syracuseStep 4820633 = 3615475) B3615475
theorem B3213755 : Blo 2141435 3213755 := bstep (se 1 (by rfl) ⟨2410316, by rfl⟩ : syracuseStep 3213755 = 4820633) B4820633
theorem B2142503 : Blo 2141435 2142503 := bstep (se 1 (by rfl) ⟨1606877, by rfl⟩ : syracuseStep 2142503 = 3213755) B3213755
theorem B2410321 : Blo 2141435 2410321 := bbase (se 2 (by rfl) ⟨903870, by rfl⟩ : syracuseStep 2410321 = 1807741) (by norm_num)
theorem B3213761 : Blo 2141435 3213761 := bstep (se 2 (by rfl) ⟨1205160, by rfl⟩ : syracuseStep 3213761 = 2410321) B2410321
theorem B2142507 : Blo 2141435 2142507 := bstep (se 1 (by rfl) ⟨1606880, by rfl⟩ : syracuseStep 2142507 = 3213761) B3213761
theorem B5147837 : Blo 2141435 5147837 := bbase (se 3 (by rfl) ⟨965219, by rfl⟩ : syracuseStep 5147837 = 1930439) (by norm_num)
theorem B3431891 : Blo 2141435 3431891 := bstep (se 1 (by rfl) ⟨2573918, by rfl⟩ : syracuseStep 3431891 = 5147837) B5147837
theorem B2287927 : Blo 2141435 2287927 := bstep (se 1 (by rfl) ⟨1715945, by rfl⟩ : syracuseStep 2287927 = 3431891) B3431891
theorem B3050569 : Blo 2141435 3050569 := bstep (se 2 (by rfl) ⟨1143963, by rfl⟩ : syracuseStep 3050569 = 2287927) B2287927
theorem B4067425 : Blo 2141435 4067425 := bstep (se 2 (by rfl) ⟨1525284, by rfl⟩ : syracuseStep 4067425 = 3050569) B3050569
theorem B5423233 : Blo 2141435 5423233 := bstep (se 2 (by rfl) ⟨2033712, by rfl⟩ : syracuseStep 5423233 = 4067425) B4067425
theorem B7230977 : Blo 2141435 7230977 := bstep (se 2 (by rfl) ⟨2711616, by rfl⟩ : syracuseStep 7230977 = 5423233) B5423233
theorem B4820651 : Blo 2141435 4820651 := bstep (se 1 (by rfl) ⟨3615488, by rfl⟩ : syracuseStep 4820651 = 7230977) B7230977
theorem B3213767 : Blo 2141435 3213767 := bstep (se 1 (by rfl) ⟨2410325, by rfl⟩ : syracuseStep 3213767 = 4820651) B4820651
theorem B2142511 : Blo 2141435 2142511 := bstep (se 1 (by rfl) ⟨1606883, by rfl⟩ : syracuseStep 2142511 = 3213767) B3213767
theorem B3213773 : Blo 2141435 3213773 := bbase (se 3 (by rfl) ⟨602582, by rfl⟩ : syracuseStep 3213773 = 1205165) (by norm_num)
theorem B2142515 : Blo 2141435 2142515 := bstep (se 1 (by rfl) ⟨1606886, by rfl⟩ : syracuseStep 2142515 = 3213773) B3213773
theorem B4820669 : Blo 2141435 4820669 := bbase (se 3 (by rfl) ⟨903875, by rfl⟩ : syracuseStep 4820669 = 1807751) (by norm_num)
theorem B3213779 : Blo 2141435 3213779 := bstep (se 1 (by rfl) ⟨2410334, by rfl⟩ : syracuseStep 3213779 = 4820669) B4820669
theorem B2142519 : Blo 2141435 2142519 := bstep (se 1 (by rfl) ⟨1606889, by rfl⟩ : syracuseStep 2142519 = 3213779) B3213779
theorem B3615509 : Blo 2141435 3615509 := bbase (se 6 (by rfl) ⟨84738, by rfl⟩ : syracuseStep 3615509 = 169477) (by norm_num)
theorem B2410339 : Blo 2141435 2410339 := bstep (se 1 (by rfl) ⟨1807754, by rfl⟩ : syracuseStep 2410339 = 3615509) B3615509
theorem B3213785 : Blo 2141435 3213785 := bstep (se 2 (by rfl) ⟨1205169, by rfl⟩ : syracuseStep 3213785 = 2410339) B2410339
theorem B2142523 : Blo 2141435 2142523 := bstep (se 1 (by rfl) ⟨1606892, by rfl⟩ : syracuseStep 2142523 = 3213785) B3213785
theorem B3092213 : Blo 2141435 3092213 := bbase (se 5 (by rfl) ⟨144947, by rfl⟩ : syracuseStep 3092213 = 289895) (by norm_num)
theorem B8245901 : Blo 2141435 8245901 := bstep (se 3 (by rfl) ⟨1546106, by rfl⟩ : syracuseStep 8245901 = 3092213) B3092213
theorem B5497267 : Blo 2141435 5497267 := bstep (se 1 (by rfl) ⟨4122950, by rfl⟩ : syracuseStep 5497267 = 8245901) B8245901
theorem B7329689 : Blo 2141435 7329689 := bstep (se 2 (by rfl) ⟨2748633, by rfl⟩ : syracuseStep 7329689 = 5497267) B5497267
theorem B4886459 : Blo 2141435 4886459 := bstep (se 1 (by rfl) ⟨3664844, by rfl⟩ : syracuseStep 4886459 = 7329689) B7329689
theorem B3257639 : Blo 2141435 3257639 := bstep (se 1 (by rfl) ⟨2443229, by rfl⟩ : syracuseStep 3257639 = 4886459) B4886459
theorem B34748149 : Blo 2141435 34748149 := bstep (se 5 (by rfl) ⟨1628819, by rfl⟩ : syracuseStep 34748149 = 3257639) B3257639
theorem B46330865 : Blo 2141435 46330865 := bstep (se 2 (by rfl) ⟨17374074, by rfl⟩ : syracuseStep 46330865 = 34748149) B34748149
theorem B30887243 : Blo 2141435 30887243 := bstep (se 1 (by rfl) ⟨23165432, by rfl⟩ : syracuseStep 30887243 = 46330865) B46330865
theorem B20591495 : Blo 2141435 20591495 := bstep (se 1 (by rfl) ⟨15443621, by rfl⟩ : syracuseStep 20591495 = 30887243) B30887243
theorem B13727663 : Blo 2141435 13727663 := bstep (se 1 (by rfl) ⟨10295747, by rfl⟩ : syracuseStep 13727663 = 20591495) B20591495
theorem B9151775 : Blo 2141435 9151775 := bstep (se 1 (by rfl) ⟨6863831, by rfl⟩ : syracuseStep 9151775 = 13727663) B13727663
theorem B6101183 : Blo 2141435 6101183 := bstep (se 1 (by rfl) ⟨4575887, by rfl⟩ : syracuseStep 6101183 = 9151775) B9151775
theorem B16269821 : Blo 2141435 16269821 := bstep (se 3 (by rfl) ⟨3050591, by rfl⟩ : syracuseStep 16269821 = 6101183) B6101183
theorem B10846547 : Blo 2141435 10846547 := bstep (se 1 (by rfl) ⟨8134910, by rfl⟩ : syracuseStep 10846547 = 16269821) B16269821
theorem B7231031 : Blo 2141435 7231031 := bstep (se 1 (by rfl) ⟨5423273, by rfl⟩ : syracuseStep 7231031 = 10846547) B10846547
theorem B4820687 : Blo 2141435 4820687 := bstep (se 1 (by rfl) ⟨3615515, by rfl⟩ : syracuseStep 4820687 = 7231031) B7231031
theorem B3213791 : Blo 2141435 3213791 := bstep (se 1 (by rfl) ⟨2410343, by rfl⟩ : syracuseStep 3213791 = 4820687) B4820687
theorem B2142527 : Blo 2141435 2142527 := bstep (se 1 (by rfl) ⟨1606895, by rfl⟩ : syracuseStep 2142527 = 3213791) B3213791
theorem B3213797 : Blo 2141435 3213797 := bbase (se 4 (by rfl) ⟨301293, by rfl⟩ : syracuseStep 3213797 = 602587) (by norm_num)
theorem B2142531 : Blo 2141435 2142531 := bstep (se 1 (by rfl) ⟨1606898, by rfl⟩ : syracuseStep 2142531 = 3213797) B3213797
theorem B3257653 : Blo 2141435 3257653 := bbase (se 5 (by rfl) ⟨152702, by rfl⟩ : syracuseStep 3257653 = 305405) (by norm_num)
theorem B4343537 : Blo 2141435 4343537 := bstep (se 2 (by rfl) ⟨1628826, by rfl⟩ : syracuseStep 4343537 = 3257653) B3257653
theorem B2895691 : Blo 2141435 2895691 := bstep (se 1 (by rfl) ⟨2171768, by rfl⟩ : syracuseStep 2895691 = 4343537) B4343537
theorem B3860921 : Blo 2141435 3860921 := bstep (se 2 (by rfl) ⟨1447845, by rfl⟩ : syracuseStep 3860921 = 2895691) B2895691
theorem B2573947 : Blo 2141435 2573947 := bstep (se 1 (by rfl) ⟨1930460, by rfl⟩ : syracuseStep 2573947 = 3860921) B3860921
theorem B13727717 : Blo 2141435 13727717 := bstep (se 4 (by rfl) ⟨1286973, by rfl⟩ : syracuseStep 13727717 = 2573947) B2573947
theorem B9151811 : Blo 2141435 9151811 := bstep (se 1 (by rfl) ⟨6863858, by rfl⟩ : syracuseStep 9151811 = 13727717) B13727717
theorem B6101207 : Blo 2141435 6101207 := bstep (se 1 (by rfl) ⟨4575905, by rfl⟩ : syracuseStep 6101207 = 9151811) B9151811
theorem B4067471 : Blo 2141435 4067471 := bstep (se 1 (by rfl) ⟨3050603, by rfl⟩ : syracuseStep 4067471 = 6101207) B6101207
theorem B2711647 : Blo 2141435 2711647 := bstep (se 1 (by rfl) ⟨2033735, by rfl⟩ : syracuseStep 2711647 = 4067471) B4067471
theorem B3615529 : Blo 2141435 3615529 := bstep (se 2 (by rfl) ⟨1355823, by rfl⟩ : syracuseStep 3615529 = 2711647) B2711647
theorem B4820705 : Blo 2141435 4820705 := bstep (se 2 (by rfl) ⟨1807764, by rfl⟩ : syracuseStep 4820705 = 3615529) B3615529
theorem B3213803 : Blo 2141435 3213803 := bstep (se 1 (by rfl) ⟨2410352, by rfl⟩ : syracuseStep 3213803 = 4820705) B4820705
theorem B2142535 : Blo 2141435 2142535 := bstep (se 1 (by rfl) ⟨1606901, by rfl⟩ : syracuseStep 2142535 = 3213803) B3213803
theorem B2410357 : Blo 2141435 2410357 := bbase (se 5 (by rfl) ⟨112985, by rfl⟩ : syracuseStep 2410357 = 225971) (by norm_num)
theorem B3213809 : Blo 2141435 3213809 := bstep (se 2 (by rfl) ⟨1205178, by rfl⟩ : syracuseStep 3213809 = 2410357) B2410357
theorem B2142539 : Blo 2141435 2142539 := bstep (se 1 (by rfl) ⟨1606904, by rfl⟩ : syracuseStep 2142539 = 3213809) B3213809
theorem B2711657 : Blo 2141435 2711657 := bbase (se 2 (by rfl) ⟨1016871, by rfl⟩ : syracuseStep 2711657 = 2033743) (by norm_num)
theorem B7231085 : Blo 2141435 7231085 := bstep (se 3 (by rfl) ⟨1355828, by rfl⟩ : syracuseStep 7231085 = 2711657) B2711657
theorem B4820723 : Blo 2141435 4820723 := bstep (se 1 (by rfl) ⟨3615542, by rfl⟩ : syracuseStep 4820723 = 7231085) B7231085
theorem B3213815 : Blo 2141435 3213815 := bstep (se 1 (by rfl) ⟨2410361, by rfl⟩ : syracuseStep 3213815 = 4820723) B4820723
theorem B2142543 : Blo 2141435 2142543 := bstep (se 1 (by rfl) ⟨1606907, by rfl⟩ : syracuseStep 2142543 = 3213815) B3213815
theorem B3213821 : Blo 2141435 3213821 := bbase (se 3 (by rfl) ⟨602591, by rfl⟩ : syracuseStep 3213821 = 1205183) (by norm_num)
theorem B2142547 : Blo 2141435 2142547 := bstep (se 1 (by rfl) ⟨1606910, by rfl⟩ : syracuseStep 2142547 = 3213821) B3213821
theorem B4820741 : Blo 2141435 4820741 := bbase (se 4 (by rfl) ⟨451944, by rfl⟩ : syracuseStep 4820741 = 903889) (by norm_num)
theorem B3213827 : Blo 2141435 3213827 := bstep (se 1 (by rfl) ⟨2410370, by rfl⟩ : syracuseStep 3213827 = 4820741) B4820741
theorem B2142551 : Blo 2141435 2142551 := bstep (se 1 (by rfl) ⟨1606913, by rfl⟩ : syracuseStep 2142551 = 3213827) B3213827
theorem B4067509 : Blo 2141435 4067509 := bbase (se 5 (by rfl) ⟨190664, by rfl⟩ : syracuseStep 4067509 = 381329) (by norm_num)
theorem B5423345 : Blo 2141435 5423345 := bstep (se 2 (by rfl) ⟨2033754, by rfl⟩ : syracuseStep 5423345 = 4067509) B4067509
theorem B3615563 : Blo 2141435 3615563 := bstep (se 1 (by rfl) ⟨2711672, by rfl⟩ : syracuseStep 3615563 = 5423345) B5423345
theorem B2410375 : Blo 2141435 2410375 := bstep (se 1 (by rfl) ⟨1807781, by rfl⟩ : syracuseStep 2410375 = 3615563) B3615563
theorem B3213833 : Blo 2141435 3213833 := bstep (se 2 (by rfl) ⟨1205187, by rfl⟩ : syracuseStep 3213833 = 2410375) B2410375
theorem B2142555 : Blo 2141435 2142555 := bstep (se 1 (by rfl) ⟨1606916, by rfl⟩ : syracuseStep 2142555 = 3213833) B3213833
theorem B10846709 : Blo 2141435 10846709 := bbase (se 5 (by rfl) ⟨508439, by rfl⟩ : syracuseStep 10846709 = 1016879) (by norm_num)
theorem B7231139 : Blo 2141435 7231139 := bstep (se 1 (by rfl) ⟨5423354, by rfl⟩ : syracuseStep 7231139 = 10846709) B10846709
theorem B4820759 : Blo 2141435 4820759 := bstep (se 1 (by rfl) ⟨3615569, by rfl⟩ : syracuseStep 4820759 = 7231139) B7231139
theorem B3213839 : Blo 2141435 3213839 := bstep (se 1 (by rfl) ⟨2410379, by rfl⟩ : syracuseStep 3213839 = 4820759) B4820759
theorem B2142559 : Blo 2141435 2142559 := bstep (se 1 (by rfl) ⟨1606919, by rfl⟩ : syracuseStep 2142559 = 3213839) B3213839
theorem B3213845 : Blo 2141435 3213845 := bbase (se 6 (by rfl) ⟨75324, by rfl⟩ : syracuseStep 3213845 = 150649) (by norm_num)
theorem B2142563 : Blo 2141435 2142563 := bstep (se 1 (by rfl) ⟨1606922, by rfl⟩ : syracuseStep 2142563 = 3213845) B3213845
theorem B18303893 : Blo 2141435 18303893 := bbase (se 6 (by rfl) ⟨428997, by rfl⟩ : syracuseStep 18303893 = 857995) (by norm_num)
theorem B12202595 : Blo 2141435 12202595 := bstep (se 1 (by rfl) ⟨9151946, by rfl⟩ : syracuseStep 12202595 = 18303893) B18303893
theorem B8135063 : Blo 2141435 8135063 := bstep (se 1 (by rfl) ⟨6101297, by rfl⟩ : syracuseStep 8135063 = 12202595) B12202595
theorem B5423375 : Blo 2141435 5423375 := bstep (se 1 (by rfl) ⟨4067531, by rfl⟩ : syracuseStep 5423375 = 8135063) B8135063
theorem B3615583 : Blo 2141435 3615583 := bstep (se 1 (by rfl) ⟨2711687, by rfl⟩ : syracuseStep 3615583 = 5423375) B5423375
theorem B4820777 : Blo 2141435 4820777 := bstep (se 2 (by rfl) ⟨1807791, by rfl⟩ : syracuseStep 4820777 = 3615583) B3615583
theorem B3213851 : Blo 2141435 3213851 := bstep (se 1 (by rfl) ⟨2410388, by rfl⟩ : syracuseStep 3213851 = 4820777) B4820777
theorem B2142567 : Blo 2141435 2142567 := bstep (se 1 (by rfl) ⟨1606925, by rfl⟩ : syracuseStep 2142567 = 3213851) B3213851
theorem B2410393 : Blo 2141435 2410393 := bbase (se 2 (by rfl) ⟨903897, by rfl⟩ : syracuseStep 2410393 = 1807795) (by norm_num)
theorem B3213857 : Blo 2141435 3213857 := bstep (se 2 (by rfl) ⟨1205196, by rfl⟩ : syracuseStep 3213857 = 2410393) B2410393
theorem B2142571 : Blo 2141435 2142571 := bstep (se 1 (by rfl) ⟨1606928, by rfl⟩ : syracuseStep 2142571 = 3213857) B3213857
theorem B8135093 : Blo 2141435 8135093 := bbase (se 5 (by rfl) ⟨381332, by rfl⟩ : syracuseStep 8135093 = 762665) (by norm_num)
theorem B5423395 : Blo 2141435 5423395 := bstep (se 1 (by rfl) ⟨4067546, by rfl⟩ : syracuseStep 5423395 = 8135093) B8135093
theorem B7231193 : Blo 2141435 7231193 := bstep (se 2 (by rfl) ⟨2711697, by rfl⟩ : syracuseStep 7231193 = 5423395) B5423395
theorem B4820795 : Blo 2141435 4820795 := bstep (se 1 (by rfl) ⟨3615596, by rfl⟩ : syracuseStep 4820795 = 7231193) B7231193
theorem B3213863 : Blo 2141435 3213863 := bstep (se 1 (by rfl) ⟨2410397, by rfl⟩ : syracuseStep 3213863 = 4820795) B4820795
theorem B2142575 : Blo 2141435 2142575 := bstep (se 1 (by rfl) ⟨1606931, by rfl⟩ : syracuseStep 2142575 = 3213863) B3213863
theorem B3213869 : Blo 2141435 3213869 := bbase (se 3 (by rfl) ⟨602600, by rfl⟩ : syracuseStep 3213869 = 1205201) (by norm_num)
theorem B2142579 : Blo 2141435 2142579 := bstep (se 1 (by rfl) ⟨1606934, by rfl⟩ : syracuseStep 2142579 = 3213869) B3213869
theorem B4820813 : Blo 2141435 4820813 := bbase (se 3 (by rfl) ⟨903902, by rfl⟩ : syracuseStep 4820813 = 1807805) (by norm_num)
theorem B3213875 : Blo 2141435 3213875 := bstep (se 1 (by rfl) ⟨2410406, by rfl⟩ : syracuseStep 3213875 = 4820813) B4820813
theorem B2142583 : Blo 2141435 2142583 := bstep (se 1 (by rfl) ⟨1606937, by rfl⟩ : syracuseStep 2142583 = 3213875) B3213875
theorem B2711713 : Blo 2141435 2711713 := bbase (se 2 (by rfl) ⟨1016892, by rfl⟩ : syracuseStep 2711713 = 2033785) (by norm_num)
theorem B3615617 : Blo 2141435 3615617 := bstep (se 2 (by rfl) ⟨1355856, by rfl⟩ : syracuseStep 3615617 = 2711713) B2711713
theorem B2410411 : Blo 2141435 2410411 := bstep (se 1 (by rfl) ⟨1807808, by rfl⟩ : syracuseStep 2410411 = 3615617) B3615617
theorem B3213881 : Blo 2141435 3213881 := bstep (se 2 (by rfl) ⟨1205205, by rfl⟩ : syracuseStep 3213881 = 2410411) B2410411
theorem B2142587 : Blo 2141435 2142587 := bstep (se 1 (by rfl) ⟨1606940, by rfl⟩ : syracuseStep 2142587 = 3213881) B3213881
theorem B24405461 : Blo 2141435 24405461 := bbase (se 7 (by rfl) ⟨286001, by rfl⟩ : syracuseStep 24405461 = 572003) (by norm_num)
theorem B16270307 : Blo 2141435 16270307 := bstep (se 1 (by rfl) ⟨12202730, by rfl⟩ : syracuseStep 16270307 = 24405461) B24405461
theorem B10846871 : Blo 2141435 10846871 := bstep (se 1 (by rfl) ⟨8135153, by rfl⟩ : syracuseStep 10846871 = 16270307) B16270307
theorem B7231247 : Blo 2141435 7231247 := bstep (se 1 (by rfl) ⟨5423435, by rfl⟩ : syracuseStep 7231247 = 10846871) B10846871
theorem B4820831 : Blo 2141435 4820831 := bstep (se 1 (by rfl) ⟨3615623, by rfl⟩ : syracuseStep 4820831 = 7231247) B7231247
theorem B3213887 : Blo 2141435 3213887 := bstep (se 1 (by rfl) ⟨2410415, by rfl⟩ : syracuseStep 3213887 = 4820831) B4820831
theorem B2142591 : Blo 2141435 2142591 := bstep (se 1 (by rfl) ⟨1606943, by rfl⟩ : syracuseStep 2142591 = 3213887) B3213887
theorem B3213893 : Blo 2141435 3213893 := bbase (se 4 (by rfl) ⟨301302, by rfl⟩ : syracuseStep 3213893 = 602605) (by norm_num)
theorem B2142595 : Blo 2141435 2142595 := bstep (se 1 (by rfl) ⟨1606946, by rfl⟩ : syracuseStep 2142595 = 3213893) B3213893
theorem B3615637 : Blo 2141435 3615637 := bbase (se 6 (by rfl) ⟨84741, by rfl⟩ : syracuseStep 3615637 = 169483) (by norm_num)
theorem B4820849 : Blo 2141435 4820849 := bstep (se 2 (by rfl) ⟨1807818, by rfl⟩ : syracuseStep 4820849 = 3615637) B3615637
theorem B3213899 : Blo 2141435 3213899 := bstep (se 1 (by rfl) ⟨2410424, by rfl⟩ : syracuseStep 3213899 = 4820849) B4820849
theorem B2142599 : Blo 2141435 2142599 := bstep (se 1 (by rfl) ⟨1606949, by rfl⟩ : syracuseStep 2142599 = 3213899) B3213899
theorem B2410429 : Blo 2141435 2410429 := bbase (se 3 (by rfl) ⟨451955, by rfl⟩ : syracuseStep 2410429 = 903911) (by norm_num)
theorem B3213905 : Blo 2141435 3213905 := bstep (se 2 (by rfl) ⟨1205214, by rfl⟩ : syracuseStep 3213905 = 2410429) B2410429
theorem B2142603 : Blo 2141435 2142603 := bstep (se 1 (by rfl) ⟨1606952, by rfl⟩ : syracuseStep 2142603 = 3213905) B3213905
theorem B7231301 : Blo 2141435 7231301 := bbase (se 4 (by rfl) ⟨677934, by rfl⟩ : syracuseStep 7231301 = 1355869) (by norm_num)
theorem B4820867 : Blo 2141435 4820867 := bstep (se 1 (by rfl) ⟨3615650, by rfl⟩ : syracuseStep 4820867 = 7231301) B7231301
theorem B3213911 : Blo 2141435 3213911 := bstep (se 1 (by rfl) ⟨2410433, by rfl⟩ : syracuseStep 3213911 = 4820867) B4820867
theorem B2142607 : Blo 2141435 2142607 := bstep (se 1 (by rfl) ⟨1606955, by rfl⟩ : syracuseStep 2142607 = 3213911) B3213911
theorem B3213917 : Blo 2141435 3213917 := bbase (se 3 (by rfl) ⟨602609, by rfl⟩ : syracuseStep 3213917 = 1205219) (by norm_num)
theorem B2142611 : Blo 2141435 2142611 := bstep (se 1 (by rfl) ⟨1606958, by rfl⟩ : syracuseStep 2142611 = 3213917) B3213917
theorem B4820885 : Blo 2141435 4820885 := bbase (se 6 (by rfl) ⟨112989, by rfl⟩ : syracuseStep 4820885 = 225979) (by norm_num)
theorem B3213923 : Blo 2141435 3213923 := bstep (se 1 (by rfl) ⟨2410442, by rfl⟩ : syracuseStep 3213923 = 4820885) B4820885
theorem B2142615 : Blo 2141435 2142615 := bstep (se 1 (by rfl) ⟨1606961, by rfl⟩ : syracuseStep 2142615 = 3213923) B3213923
theorem B4576085 : Blo 2141435 4576085 := bbase (se 9 (by rfl) ⟨13406, by rfl⟩ : syracuseStep 4576085 = 26813) (by norm_num)
theorem B3050723 : Blo 2141435 3050723 := bstep (se 1 (by rfl) ⟨2288042, by rfl⟩ : syracuseStep 3050723 = 4576085) B4576085
theorem B8135261 : Blo 2141435 8135261 := bstep (se 3 (by rfl) ⟨1525361, by rfl⟩ : syracuseStep 8135261 = 3050723) B3050723
theorem B5423507 : Blo 2141435 5423507 := bstep (se 1 (by rfl) ⟨4067630, by rfl⟩ : syracuseStep 5423507 = 8135261) B8135261
theorem B3615671 : Blo 2141435 3615671 := bstep (se 1 (by rfl) ⟨2711753, by rfl⟩ : syracuseStep 3615671 = 5423507) B5423507
theorem B2410447 : Blo 2141435 2410447 := bstep (se 1 (by rfl) ⟨1807835, by rfl⟩ : syracuseStep 2410447 = 3615671) B3615671
theorem B3213929 : Blo 2141435 3213929 := bstep (se 2 (by rfl) ⟨1205223, by rfl⟩ : syracuseStep 3213929 = 2410447) B2410447
theorem B2142619 : Blo 2141435 2142619 := bstep (se 1 (by rfl) ⟨1606964, by rfl⟩ : syracuseStep 2142619 = 3213929) B3213929
theorem B2171857 : Blo 2141435 2171857 := bbase (se 2 (by rfl) ⟨814446, by rfl⟩ : syracuseStep 2171857 = 1628893) (by norm_num)
theorem B2895809 : Blo 2141435 2895809 := bstep (se 2 (by rfl) ⟨1085928, by rfl⟩ : syracuseStep 2895809 = 2171857) B2171857
theorem B7722157 : Blo 2141435 7722157 := bstep (se 3 (by rfl) ⟨1447904, by rfl⟩ : syracuseStep 7722157 = 2895809) B2895809
theorem B10296209 : Blo 2141435 10296209 := bstep (se 2 (by rfl) ⟨3861078, by rfl⟩ : syracuseStep 10296209 = 7722157) B7722157
theorem B6864139 : Blo 2141435 6864139 := bstep (se 1 (by rfl) ⟨5148104, by rfl⟩ : syracuseStep 6864139 = 10296209) B10296209
theorem B9152185 : Blo 2141435 9152185 := bstep (se 2 (by rfl) ⟨3432069, by rfl⟩ : syracuseStep 9152185 = 6864139) B6864139
theorem B12202913 : Blo 2141435 12202913 := bstep (se 2 (by rfl) ⟨4576092, by rfl⟩ : syracuseStep 12202913 = 9152185) B9152185
theorem B8135275 : Blo 2141435 8135275 := bstep (se 1 (by rfl) ⟨6101456, by rfl⟩ : syracuseStep 8135275 = 12202913) B12202913
theorem B10847033 : Blo 2141435 10847033 := bstep (se 2 (by rfl) ⟨4067637, by rfl⟩ : syracuseStep 10847033 = 8135275) B8135275
theorem B7231355 : Blo 2141435 7231355 := bstep (se 1 (by rfl) ⟨5423516, by rfl⟩ : syracuseStep 7231355 = 10847033) B10847033
theorem B4820903 : Blo 2141435 4820903 := bstep (se 1 (by rfl) ⟨3615677, by rfl⟩ : syracuseStep 4820903 = 7231355) B7231355
theorem B3213935 : Blo 2141435 3213935 := bstep (se 1 (by rfl) ⟨2410451, by rfl⟩ : syracuseStep 3213935 = 4820903) B4820903
theorem B2142623 : Blo 2141435 2142623 := bstep (se 1 (by rfl) ⟨1606967, by rfl⟩ : syracuseStep 2142623 = 3213935) B3213935
theorem B3213941 : Blo 2141435 3213941 := bbase (se 5 (by rfl) ⟨150653, by rfl⟩ : syracuseStep 3213941 = 301307) (by norm_num)
theorem B2142627 : Blo 2141435 2142627 := bstep (se 1 (by rfl) ⟨1606970, by rfl⟩ : syracuseStep 2142627 = 3213941) B3213941
theorem B4067653 : Blo 2141435 4067653 := bbase (se 4 (by rfl) ⟨381342, by rfl⟩ : syracuseStep 4067653 = 762685) (by norm_num)
theorem B5423537 : Blo 2141435 5423537 := bstep (se 2 (by rfl) ⟨2033826, by rfl⟩ : syracuseStep 5423537 = 4067653) B4067653
theorem B3615691 : Blo 2141435 3615691 := bstep (se 1 (by rfl) ⟨2711768, by rfl⟩ : syracuseStep 3615691 = 5423537) B5423537
theorem B4820921 : Blo 2141435 4820921 := bstep (se 2 (by rfl) ⟨1807845, by rfl⟩ : syracuseStep 4820921 = 3615691) B3615691
theorem B3213947 : Blo 2141435 3213947 := bstep (se 1 (by rfl) ⟨2410460, by rfl⟩ : syracuseStep 3213947 = 4820921) B4820921
theorem B2142631 : Blo 2141435 2142631 := bstep (se 1 (by rfl) ⟨1606973, by rfl⟩ : syracuseStep 2142631 = 3213947) B3213947
theorem B2410465 : Blo 2141435 2410465 := bbase (se 2 (by rfl) ⟨903924, by rfl⟩ : syracuseStep 2410465 = 1807849) (by norm_num)
theorem B3213953 : Blo 2141435 3213953 := bstep (se 2 (by rfl) ⟨1205232, by rfl⟩ : syracuseStep 3213953 = 2410465) B2410465
theorem B2142635 : Blo 2141435 2142635 := bstep (se 1 (by rfl) ⟨1606976, by rfl⟩ : syracuseStep 2142635 = 3213953) B3213953
theorem B5423557 : Blo 2141435 5423557 := bbase (se 4 (by rfl) ⟨508458, by rfl⟩ : syracuseStep 5423557 = 1016917) (by norm_num)
theorem B7231409 : Blo 2141435 7231409 := bstep (se 2 (by rfl) ⟨2711778, by rfl⟩ : syracuseStep 7231409 = 5423557) B5423557
theorem B4820939 : Blo 2141435 4820939 := bstep (se 1 (by rfl) ⟨3615704, by rfl⟩ : syracuseStep 4820939 = 7231409) B7231409
theorem B3213959 : Blo 2141435 3213959 := bstep (se 1 (by rfl) ⟨2410469, by rfl⟩ : syracuseStep 3213959 = 4820939) B4820939
theorem B2142639 : Blo 2141435 2142639 := bstep (se 1 (by rfl) ⟨1606979, by rfl⟩ : syracuseStep 2142639 = 3213959) B3213959
theorem B3213965 : Blo 2141435 3213965 := bbase (se 3 (by rfl) ⟨602618, by rfl⟩ : syracuseStep 3213965 = 1205237) (by norm_num)
theorem B2142643 : Blo 2141435 2142643 := bstep (se 1 (by rfl) ⟨1606982, by rfl⟩ : syracuseStep 2142643 = 3213965) B3213965
theorem B4820957 : Blo 2141435 4820957 := bbase (se 3 (by rfl) ⟨903929, by rfl⟩ : syracuseStep 4820957 = 1807859) (by norm_num)
theorem B3213971 : Blo 2141435 3213971 := bstep (se 1 (by rfl) ⟨2410478, by rfl⟩ : syracuseStep 3213971 = 4820957) B4820957
theorem B2142647 : Blo 2141435 2142647 := bstep (se 1 (by rfl) ⟨1606985, by rfl⟩ : syracuseStep 2142647 = 3213971) B3213971
theorem B3615725 : Blo 2141435 3615725 := bbase (se 3 (by rfl) ⟨677948, by rfl⟩ : syracuseStep 3615725 = 1355897) (by norm_num)
theorem B2410483 : Blo 2141435 2410483 := bstep (se 1 (by rfl) ⟨1807862, by rfl⟩ : syracuseStep 2410483 = 3615725) B3615725
theorem B3213977 : Blo 2141435 3213977 := bstep (se 2 (by rfl) ⟨1205241, by rfl⟩ : syracuseStep 3213977 = 2410483) B2410483
theorem B2142651 : Blo 2141435 2142651 := bstep (se 1 (by rfl) ⟨1606988, by rfl⟩ : syracuseStep 2142651 = 3213977) B3213977
theorem B5148181 : Blo 2141435 5148181 := bbase (se 6 (by rfl) ⟨120660, by rfl⟩ : syracuseStep 5148181 = 241321) (by norm_num)
theorem B27456965 : Blo 2141435 27456965 := bstep (se 4 (by rfl) ⟨2574090, by rfl⟩ : syracuseStep 27456965 = 5148181) B5148181
theorem B18304643 : Blo 2141435 18304643 := bstep (se 1 (by rfl) ⟨13728482, by rfl⟩ : syracuseStep 18304643 = 27456965) B27456965
theorem B12203095 : Blo 2141435 12203095 := bstep (se 1 (by rfl) ⟨9152321, by rfl⟩ : syracuseStep 12203095 = 18304643) B18304643
theorem B16270793 : Blo 2141435 16270793 := bstep (se 2 (by rfl) ⟨6101547, by rfl⟩ : syracuseStep 16270793 = 12203095) B12203095
theorem B10847195 : Blo 2141435 10847195 := bstep (se 1 (by rfl) ⟨8135396, by rfl⟩ : syracuseStep 10847195 = 16270793) B16270793
theorem B7231463 : Blo 2141435 7231463 := bstep (se 1 (by rfl) ⟨5423597, by rfl⟩ : syracuseStep 7231463 = 10847195) B10847195
theorem B4820975 : Blo 2141435 4820975 := bstep (se 1 (by rfl) ⟨3615731, by rfl⟩ : syracuseStep 4820975 = 7231463) B7231463
theorem B3213983 : Blo 2141435 3213983 := bstep (se 1 (by rfl) ⟨2410487, by rfl⟩ : syracuseStep 3213983 = 4820975) B4820975
theorem B2142655 : Blo 2141435 2142655 := bstep (se 1 (by rfl) ⟨1606991, by rfl⟩ : syracuseStep 2142655 = 3213983) B3213983
theorem B3213989 : Blo 2141435 3213989 := bbase (se 4 (by rfl) ⟨301311, by rfl⟩ : syracuseStep 3213989 = 602623) (by norm_num)
theorem B2142659 : Blo 2141435 2142659 := bstep (se 1 (by rfl) ⟨1606994, by rfl⟩ : syracuseStep 2142659 = 3213989) B3213989
theorem B2711809 : Blo 2141435 2711809 := bbase (se 2 (by rfl) ⟨1016928, by rfl⟩ : syracuseStep 2711809 = 2033857) (by norm_num)
theorem B3615745 : Blo 2141435 3615745 := bstep (se 2 (by rfl) ⟨1355904, by rfl⟩ : syracuseStep 3615745 = 2711809) B2711809
theorem B4820993 : Blo 2141435 4820993 := bstep (se 2 (by rfl) ⟨1807872, by rfl⟩ : syracuseStep 4820993 = 3615745) B3615745
theorem B3213995 : Blo 2141435 3213995 := bstep (se 1 (by rfl) ⟨2410496, by rfl⟩ : syracuseStep 3213995 = 4820993) B4820993
theorem B2142663 : Blo 2141435 2142663 := bstep (se 1 (by rfl) ⟨1606997, by rfl⟩ : syracuseStep 2142663 = 3213995) B3213995
theorem B2410501 : Blo 2141435 2410501 := bbase (se 4 (by rfl) ⟨225984, by rfl⟩ : syracuseStep 2410501 = 451969) (by norm_num)
theorem B3214001 : Blo 2141435 3214001 := bstep (se 2 (by rfl) ⟨1205250, by rfl⟩ : syracuseStep 3214001 = 2410501) B2410501
theorem B2142667 : Blo 2141435 2142667 := bstep (se 1 (by rfl) ⟨1607000, by rfl⟩ : syracuseStep 2142667 = 3214001) B3214001
theorem B3050797 : Blo 2141435 3050797 := bbase (se 3 (by rfl) ⟨572024, by rfl⟩ : syracuseStep 3050797 = 1144049) (by norm_num)
theorem B4067729 : Blo 2141435 4067729 := bstep (se 2 (by rfl) ⟨1525398, by rfl⟩ : syracuseStep 4067729 = 3050797) B3050797
theorem B2711819 : Blo 2141435 2711819 := bstep (se 1 (by rfl) ⟨2033864, by rfl⟩ : syracuseStep 2711819 = 4067729) B4067729
theorem B7231517 : Blo 2141435 7231517 := bstep (se 3 (by rfl) ⟨1355909, by rfl⟩ : syracuseStep 7231517 = 2711819) B2711819
theorem B4821011 : Blo 2141435 4821011 := bstep (se 1 (by rfl) ⟨3615758, by rfl⟩ : syracuseStep 4821011 = 7231517) B7231517
theorem B3214007 : Blo 2141435 3214007 := bstep (se 1 (by rfl) ⟨2410505, by rfl⟩ : syracuseStep 3214007 = 4821011) B4821011
theorem B2142671 : Blo 2141435 2142671 := bstep (se 1 (by rfl) ⟨1607003, by rfl⟩ : syracuseStep 2142671 = 3214007) B3214007
theorem B3214013 : Blo 2141435 3214013 := bbase (se 3 (by rfl) ⟨602627, by rfl⟩ : syracuseStep 3214013 = 1205255) (by norm_num)
theorem B2142675 : Blo 2141435 2142675 := bstep (se 1 (by rfl) ⟨1607006, by rfl⟩ : syracuseStep 2142675 = 3214013) B3214013
theorem B4821029 : Blo 2141435 4821029 := bbase (se 4 (by rfl) ⟨451971, by rfl⟩ : syracuseStep 4821029 = 903943) (by norm_num)
theorem B3214019 : Blo 2141435 3214019 := bstep (se 1 (by rfl) ⟨2410514, by rfl⟩ : syracuseStep 3214019 = 4821029) B4821029
theorem B2142679 : Blo 2141435 2142679 := bstep (se 1 (by rfl) ⟨1607009, by rfl⟩ : syracuseStep 2142679 = 3214019) B3214019
theorem B5423669 : Blo 2141435 5423669 := bbase (se 5 (by rfl) ⟨254234, by rfl⟩ : syracuseStep 5423669 = 508469) (by norm_num)
theorem B3615779 : Blo 2141435 3615779 := bstep (se 1 (by rfl) ⟨2711834, by rfl⟩ : syracuseStep 3615779 = 5423669) B5423669
theorem B2410519 : Blo 2141435 2410519 := bstep (se 1 (by rfl) ⟨1807889, by rfl⟩ : syracuseStep 2410519 = 3615779) B3615779
theorem B3214025 : Blo 2141435 3214025 := bstep (se 2 (by rfl) ⟨1205259, by rfl⟩ : syracuseStep 3214025 = 2410519) B2410519
theorem B2142683 : Blo 2141435 2142683 := bstep (se 1 (by rfl) ⟨1607012, by rfl⟩ : syracuseStep 2142683 = 3214025) B3214025
theorem B10296517 : Blo 2141435 10296517 := bbase (se 4 (by rfl) ⟨965298, by rfl⟩ : syracuseStep 10296517 = 1930597) (by norm_num)
theorem B13728689 : Blo 2141435 13728689 := bstep (se 2 (by rfl) ⟨5148258, by rfl⟩ : syracuseStep 13728689 = 10296517) B10296517
theorem B9152459 : Blo 2141435 9152459 := bstep (se 1 (by rfl) ⟨6864344, by rfl⟩ : syracuseStep 9152459 = 13728689) B13728689
theorem B6101639 : Blo 2141435 6101639 := bstep (se 1 (by rfl) ⟨4576229, by rfl⟩ : syracuseStep 6101639 = 9152459) B9152459
theorem B4067759 : Blo 2141435 4067759 := bstep (se 1 (by rfl) ⟨3050819, by rfl⟩ : syracuseStep 4067759 = 6101639) B6101639
theorem B10847357 : Blo 2141435 10847357 := bstep (se 3 (by rfl) ⟨2033879, by rfl⟩ : syracuseStep 10847357 = 4067759) B4067759
theorem B7231571 : Blo 2141435 7231571 := bstep (se 1 (by rfl) ⟨5423678, by rfl⟩ : syracuseStep 7231571 = 10847357) B10847357
theorem B4821047 : Blo 2141435 4821047 := bstep (se 1 (by rfl) ⟨3615785, by rfl⟩ : syracuseStep 4821047 = 7231571) B7231571
theorem B3214031 : Blo 2141435 3214031 := bstep (se 1 (by rfl) ⟨2410523, by rfl⟩ : syracuseStep 3214031 = 4821047) B4821047
theorem B2142687 : Blo 2141435 2142687 := bstep (se 1 (by rfl) ⟨1607015, by rfl⟩ : syracuseStep 2142687 = 3214031) B3214031
theorem B3214037 : Blo 2141435 3214037 := bbase (se 7 (by rfl) ⟨37664, by rfl⟩ : syracuseStep 3214037 = 75329) (by norm_num)
theorem B2142691 : Blo 2141435 2142691 := bstep (se 1 (by rfl) ⟨1607018, by rfl⟩ : syracuseStep 2142691 = 3214037) B3214037
theorem B4343861 : Blo 2141435 4343861 := bbase (se 5 (by rfl) ⟨203618, by rfl⟩ : syracuseStep 4343861 = 407237) (by norm_num)
theorem B2895907 : Blo 2141435 2895907 := bstep (se 1 (by rfl) ⟨2171930, by rfl⟩ : syracuseStep 2895907 = 4343861) B4343861
theorem B3861209 : Blo 2141435 3861209 := bstep (se 2 (by rfl) ⟨1447953, by rfl⟩ : syracuseStep 3861209 = 2895907) B2895907
theorem B10296557 : Blo 2141435 10296557 := bstep (se 3 (by rfl) ⟨1930604, by rfl⟩ : syracuseStep 10296557 = 3861209) B3861209
theorem B6864371 : Blo 2141435 6864371 := bstep (se 1 (by rfl) ⟨5148278, by rfl⟩ : syracuseStep 6864371 = 10296557) B10296557
theorem B4576247 : Blo 2141435 4576247 := bstep (se 1 (by rfl) ⟨3432185, by rfl⟩ : syracuseStep 4576247 = 6864371) B6864371
theorem B3050831 : Blo 2141435 3050831 := bstep (se 1 (by rfl) ⟨2288123, by rfl⟩ : syracuseStep 3050831 = 4576247) B4576247
theorem B8135549 : Blo 2141435 8135549 := bstep (se 3 (by rfl) ⟨1525415, by rfl⟩ : syracuseStep 8135549 = 3050831) B3050831
theorem B5423699 : Blo 2141435 5423699 := bstep (se 1 (by rfl) ⟨4067774, by rfl⟩ : syracuseStep 5423699 = 8135549) B8135549
theorem B3615799 : Blo 2141435 3615799 := bstep (se 1 (by rfl) ⟨2711849, by rfl⟩ : syracuseStep 3615799 = 5423699) B5423699
theorem B4821065 : Blo 2141435 4821065 := bstep (se 2 (by rfl) ⟨1807899, by rfl⟩ : syracuseStep 4821065 = 3615799) B3615799
theorem B3214043 : Blo 2141435 3214043 := bstep (se 1 (by rfl) ⟨2410532, by rfl⟩ : syracuseStep 3214043 = 4821065) B4821065
theorem B2142695 : Blo 2141435 2142695 := bstep (se 1 (by rfl) ⟨1607021, by rfl⟩ : syracuseStep 2142695 = 3214043) B3214043
theorem B2410537 : Blo 2141435 2410537 := bbase (se 2 (by rfl) ⟨903951, by rfl⟩ : syracuseStep 2410537 = 1807903) (by norm_num)
theorem B3214049 : Blo 2141435 3214049 := bstep (se 2 (by rfl) ⟨1205268, by rfl⟩ : syracuseStep 3214049 = 2410537) B2410537
theorem B2142699 : Blo 2141435 2142699 := bstep (se 1 (by rfl) ⟨1607024, by rfl⟩ : syracuseStep 2142699 = 3214049) B3214049
theorem B2895917 : Blo 2141435 2895917 := bbase (se 3 (by rfl) ⟨542984, by rfl⟩ : syracuseStep 2895917 = 1085969) (by norm_num)
theorem B30889781 : Blo 2141435 30889781 := bstep (se 5 (by rfl) ⟨1447958, by rfl⟩ : syracuseStep 30889781 = 2895917) B2895917
theorem B20593187 : Blo 2141435 20593187 := bstep (se 1 (by rfl) ⟨15444890, by rfl⟩ : syracuseStep 20593187 = 30889781) B30889781
theorem B13728791 : Blo 2141435 13728791 := bstep (se 1 (by rfl) ⟨10296593, by rfl⟩ : syracuseStep 13728791 = 20593187) B20593187
theorem B9152527 : Blo 2141435 9152527 := bstep (se 1 (by rfl) ⟨6864395, by rfl⟩ : syracuseStep 9152527 = 13728791) B13728791
theorem B12203369 : Blo 2141435 12203369 := bstep (se 2 (by rfl) ⟨4576263, by rfl⟩ : syracuseStep 12203369 = 9152527) B9152527
theorem B8135579 : Blo 2141435 8135579 := bstep (se 1 (by rfl) ⟨6101684, by rfl⟩ : syracuseStep 8135579 = 12203369) B12203369
theorem B5423719 : Blo 2141435 5423719 := bstep (se 1 (by rfl) ⟨4067789, by rfl⟩ : syracuseStep 5423719 = 8135579) B8135579
theorem B7231625 : Blo 2141435 7231625 := bstep (se 2 (by rfl) ⟨2711859, by rfl⟩ : syracuseStep 7231625 = 5423719) B5423719
theorem B4821083 : Blo 2141435 4821083 := bstep (se 1 (by rfl) ⟨3615812, by rfl⟩ : syracuseStep 4821083 = 7231625) B7231625
theorem B3214055 : Blo 2141435 3214055 := bstep (se 1 (by rfl) ⟨2410541, by rfl⟩ : syracuseStep 3214055 = 4821083) B4821083
theorem B2142703 : Blo 2141435 2142703 := bstep (se 1 (by rfl) ⟨1607027, by rfl⟩ : syracuseStep 2142703 = 3214055) B3214055
theorem B3214061 : Blo 2141435 3214061 := bbase (se 3 (by rfl) ⟨602636, by rfl⟩ : syracuseStep 3214061 = 1205273) (by norm_num)
theorem B2142707 : Blo 2141435 2142707 := bstep (se 1 (by rfl) ⟨1607030, by rfl⟩ : syracuseStep 2142707 = 3214061) B3214061
theorem B4821101 : Blo 2141435 4821101 := bbase (se 3 (by rfl) ⟨903956, by rfl⟩ : syracuseStep 4821101 = 1807913) (by norm_num)
theorem B3214067 : Blo 2141435 3214067 := bstep (se 1 (by rfl) ⟨2410550, by rfl⟩ : syracuseStep 3214067 = 4821101) B4821101
theorem B2142711 : Blo 2141435 2142711 := bstep (se 1 (by rfl) ⟨1607033, by rfl⟩ : syracuseStep 2142711 = 3214067) B3214067
theorem B4067813 : Blo 2141435 4067813 := bbase (se 4 (by rfl) ⟨381357, by rfl⟩ : syracuseStep 4067813 = 762715) (by norm_num)
theorem B2711875 : Blo 2141435 2711875 := bstep (se 1 (by rfl) ⟨2033906, by rfl⟩ : syracuseStep 2711875 = 4067813) B4067813
theorem B3615833 : Blo 2141435 3615833 := bstep (se 2 (by rfl) ⟨1355937, by rfl⟩ : syracuseStep 3615833 = 2711875) B2711875
theorem B2410555 : Blo 2141435 2410555 := bstep (se 1 (by rfl) ⟨1807916, by rfl⟩ : syracuseStep 2410555 = 3615833) B3615833
theorem B3214073 : Blo 2141435 3214073 := bstep (se 2 (by rfl) ⟨1205277, by rfl⟩ : syracuseStep 3214073 = 2410555) B2410555
theorem B2142715 : Blo 2141435 2142715 := bstep (se 1 (by rfl) ⟨1607036, by rfl⟩ : syracuseStep 2142715 = 3214073) B3214073
theorem B5791877 : Blo 2141435 5791877 := bbase (se 4 (by rfl) ⟨542988, by rfl⟩ : syracuseStep 5791877 = 1085977) (by norm_num)
theorem B3861251 : Blo 2141435 3861251 := bstep (se 1 (by rfl) ⟨2895938, by rfl⟩ : syracuseStep 3861251 = 5791877) B5791877
theorem B41186677 : Blo 2141435 41186677 := bstep (se 5 (by rfl) ⟨1930625, by rfl⟩ : syracuseStep 41186677 = 3861251) B3861251
theorem B54915569 : Blo 2141435 54915569 := bstep (se 2 (by rfl) ⟨20593338, by rfl⟩ : syracuseStep 54915569 = 41186677) B41186677
theorem B36610379 : Blo 2141435 36610379 := bstep (se 1 (by rfl) ⟨27457784, by rfl⟩ : syracuseStep 36610379 = 54915569) B54915569
theorem B24406919 : Blo 2141435 24406919 := bstep (se 1 (by rfl) ⟨18305189, by rfl⟩ : syracuseStep 24406919 = 36610379) B36610379
theorem B16271279 : Blo 2141435 16271279 := bstep (se 1 (by rfl) ⟨12203459, by rfl⟩ : syracuseStep 16271279 = 24406919) B24406919
theorem B10847519 : Blo 2141435 10847519 := bstep (se 1 (by rfl) ⟨8135639, by rfl⟩ : syracuseStep 10847519 = 16271279) B16271279
theorem B7231679 : Blo 2141435 7231679 := bstep (se 1 (by rfl) ⟨5423759, by rfl⟩ : syracuseStep 7231679 = 10847519) B10847519
theorem B4821119 : Blo 2141435 4821119 := bstep (se 1 (by rfl) ⟨3615839, by rfl⟩ : syracuseStep 4821119 = 7231679) B7231679
theorem B3214079 : Blo 2141435 3214079 := bstep (se 1 (by rfl) ⟨2410559, by rfl⟩ : syracuseStep 3214079 = 4821119) B4821119
theorem B2142719 : Blo 2141435 2142719 := bstep (se 1 (by rfl) ⟨1607039, by rfl⟩ : syracuseStep 2142719 = 3214079) B3214079
theorem B3214085 : Blo 2141435 3214085 := bbase (se 4 (by rfl) ⟨301320, by rfl⟩ : syracuseStep 3214085 = 602641) (by norm_num)
theorem B2142723 : Blo 2141435 2142723 := bstep (se 1 (by rfl) ⟨1607042, by rfl⟩ : syracuseStep 2142723 = 3214085) B3214085
theorem B3615853 : Blo 2141435 3615853 := bbase (se 3 (by rfl) ⟨677972, by rfl⟩ : syracuseStep 3615853 = 1355945) (by norm_num)
theorem B4821137 : Blo 2141435 4821137 := bstep (se 2 (by rfl) ⟨1807926, by rfl⟩ : syracuseStep 4821137 = 3615853) B3615853
theorem B3214091 : Blo 2141435 3214091 := bstep (se 1 (by rfl) ⟨2410568, by rfl⟩ : syracuseStep 3214091 = 4821137) B4821137
theorem B2142727 : Blo 2141435 2142727 := bstep (se 1 (by rfl) ⟨1607045, by rfl⟩ : syracuseStep 2142727 = 3214091) B3214091
theorem B2410573 : Blo 2141435 2410573 := bbase (se 3 (by rfl) ⟨451982, by rfl⟩ : syracuseStep 2410573 = 903965) (by norm_num)
theorem B3214097 : Blo 2141435 3214097 := bstep (se 2 (by rfl) ⟨1205286, by rfl⟩ : syracuseStep 3214097 = 2410573) B2410573
theorem B2142731 : Blo 2141435 2142731 := bstep (se 1 (by rfl) ⟨1607048, by rfl⟩ : syracuseStep 2142731 = 3214097) B3214097
theorem B7231733 : Blo 2141435 7231733 := bbase (se 5 (by rfl) ⟨338987, by rfl⟩ : syracuseStep 7231733 = 677975) (by norm_num)
theorem B4821155 : Blo 2141435 4821155 := bstep (se 1 (by rfl) ⟨3615866, by rfl⟩ : syracuseStep 4821155 = 7231733) B7231733
theorem B3214103 : Blo 2141435 3214103 := bstep (se 1 (by rfl) ⟨2410577, by rfl⟩ : syracuseStep 3214103 = 4821155) B4821155
theorem B2142735 : Blo 2141435 2142735 := bstep (se 1 (by rfl) ⟨1607051, by rfl⟩ : syracuseStep 2142735 = 3214103) B3214103
theorem B3214109 : Blo 2141435 3214109 := bbase (se 3 (by rfl) ⟨602645, by rfl⟩ : syracuseStep 3214109 = 1205291) (by norm_num)
theorem B2142739 : Blo 2141435 2142739 := bstep (se 1 (by rfl) ⟨1607054, by rfl⟩ : syracuseStep 2142739 = 3214109) B3214109
theorem B4821173 : Blo 2141435 4821173 := bbase (se 5 (by rfl) ⟨225992, by rfl⟩ : syracuseStep 4821173 = 451985) (by norm_num)
theorem B3214115 : Blo 2141435 3214115 := bstep (se 1 (by rfl) ⟨2410586, by rfl⟩ : syracuseStep 3214115 = 4821173) B4821173
theorem B2142743 : Blo 2141435 2142743 := bstep (se 1 (by rfl) ⟨1607057, by rfl⟩ : syracuseStep 2142743 = 3214115) B3214115
theorem B3432269 : Blo 2141435 3432269 := bbase (se 3 (by rfl) ⟨643550, by rfl⟩ : syracuseStep 3432269 = 1287101) (by norm_num)
theorem B2288179 : Blo 2141435 2288179 := bstep (se 1 (by rfl) ⟨1716134, by rfl⟩ : syracuseStep 2288179 = 3432269) B3432269
theorem B12203621 : Blo 2141435 12203621 := bstep (se 4 (by rfl) ⟨1144089, by rfl⟩ : syracuseStep 12203621 = 2288179) B2288179
theorem B8135747 : Blo 2141435 8135747 := bstep (se 1 (by rfl) ⟨6101810, by rfl⟩ : syracuseStep 8135747 = 12203621) B12203621
theorem B5423831 : Blo 2141435 5423831 := bstep (se 1 (by rfl) ⟨4067873, by rfl⟩ : syracuseStep 5423831 = 8135747) B8135747
theorem B3615887 : Blo 2141435 3615887 := bstep (se 1 (by rfl) ⟨2711915, by rfl⟩ : syracuseStep 3615887 = 5423831) B5423831
theorem B2410591 : Blo 2141435 2410591 := bstep (se 1 (by rfl) ⟨1807943, by rfl⟩ : syracuseStep 2410591 = 3615887) B3615887
theorem B3214121 : Blo 2141435 3214121 := bstep (se 2 (by rfl) ⟨1205295, by rfl⟩ : syracuseStep 3214121 = 2410591) B2410591
theorem B2142747 : Blo 2141435 2142747 := bstep (se 1 (by rfl) ⟨1607060, by rfl⟩ : syracuseStep 2142747 = 3214121) B3214121
theorem B5148413 : Blo 2141435 5148413 := bbase (se 3 (by rfl) ⟨965327, by rfl⟩ : syracuseStep 5148413 = 1930655) (by norm_num)
theorem B3432275 : Blo 2141435 3432275 := bstep (se 1 (by rfl) ⟨2574206, by rfl⟩ : syracuseStep 3432275 = 5148413) B5148413
theorem B2288183 : Blo 2141435 2288183 := bstep (se 1 (by rfl) ⟨1716137, by rfl⟩ : syracuseStep 2288183 = 3432275) B3432275
theorem B6101821 : Blo 2141435 6101821 := bstep (se 3 (by rfl) ⟨1144091, by rfl⟩ : syracuseStep 6101821 = 2288183) B2288183
theorem B8135761 : Blo 2141435 8135761 := bstep (se 2 (by rfl) ⟨3050910, by rfl⟩ : syracuseStep 8135761 = 6101821) B6101821
theorem B10847681 : Blo 2141435 10847681 := bstep (se 2 (by rfl) ⟨4067880, by rfl⟩ : syracuseStep 10847681 = 8135761) B8135761
theorem B7231787 : Blo 2141435 7231787 := bstep (se 1 (by rfl) ⟨5423840, by rfl⟩ : syracuseStep 7231787 = 10847681) B10847681
theorem B4821191 : Blo 2141435 4821191 := bstep (se 1 (by rfl) ⟨3615893, by rfl⟩ : syracuseStep 4821191 = 7231787) B7231787
theorem B3214127 : Blo 2141435 3214127 := bstep (se 1 (by rfl) ⟨2410595, by rfl⟩ : syracuseStep 3214127 = 4821191) B4821191
theorem B2142751 : Blo 2141435 2142751 := bstep (se 1 (by rfl) ⟨1607063, by rfl⟩ : syracuseStep 2142751 = 3214127) B3214127
theorem B3214133 : Blo 2141435 3214133 := bbase (se 5 (by rfl) ⟨150662, by rfl⟩ : syracuseStep 3214133 = 301325) (by norm_num)
theorem B2142755 : Blo 2141435 2142755 := bstep (se 1 (by rfl) ⟨1607066, by rfl⟩ : syracuseStep 2142755 = 3214133) B3214133
theorem B5423861 : Blo 2141435 5423861 := bbase (se 5 (by rfl) ⟨254243, by rfl⟩ : syracuseStep 5423861 = 508487) (by norm_num)
theorem B3615907 : Blo 2141435 3615907 := bstep (se 1 (by rfl) ⟨2711930, by rfl⟩ : syracuseStep 3615907 = 5423861) B5423861
theorem B4821209 : Blo 2141435 4821209 := bstep (se 2 (by rfl) ⟨1807953, by rfl⟩ : syracuseStep 4821209 = 3615907) B3615907
theorem B3214139 : Blo 2141435 3214139 := bstep (se 1 (by rfl) ⟨2410604, by rfl⟩ : syracuseStep 3214139 = 4821209) B4821209
theorem B2142759 : Blo 2141435 2142759 := bstep (se 1 (by rfl) ⟨1607069, by rfl⟩ : syracuseStep 2142759 = 3214139) B3214139
theorem B2410609 : Blo 2141435 2410609 := bbase (se 2 (by rfl) ⟨903978, by rfl⟩ : syracuseStep 2410609 = 1807957) (by norm_num)
theorem B3214145 : Blo 2141435 3214145 := bstep (se 2 (by rfl) ⟨1205304, by rfl⟩ : syracuseStep 3214145 = 2410609) B2410609
theorem B2142763 : Blo 2141435 2142763 := bstep (se 1 (by rfl) ⟨1607072, by rfl⟩ : syracuseStep 2142763 = 3214145) B3214145
theorem B7722677 : Blo 2141435 7722677 := bbase (se 5 (by rfl) ⟨362000, by rfl⟩ : syracuseStep 7722677 = 724001) (by norm_num)
theorem B5148451 : Blo 2141435 5148451 := bstep (se 1 (by rfl) ⟨3861338, by rfl⟩ : syracuseStep 5148451 = 7722677) B7722677
theorem B6864601 : Blo 2141435 6864601 := bstep (se 2 (by rfl) ⟨2574225, by rfl⟩ : syracuseStep 6864601 = 5148451) B5148451
theorem B9152801 : Blo 2141435 9152801 := bstep (se 2 (by rfl) ⟨3432300, by rfl⟩ : syracuseStep 9152801 = 6864601) B6864601
theorem B6101867 : Blo 2141435 6101867 := bstep (se 1 (by rfl) ⟨4576400, by rfl⟩ : syracuseStep 6101867 = 9152801) B9152801
theorem B4067911 : Blo 2141435 4067911 := bstep (se 1 (by rfl) ⟨3050933, by rfl⟩ : syracuseStep 4067911 = 6101867) B6101867
theorem B5423881 : Blo 2141435 5423881 := bstep (se 2 (by rfl) ⟨2033955, by rfl⟩ : syracuseStep 5423881 = 4067911) B4067911
theorem B7231841 : Blo 2141435 7231841 := bstep (se 2 (by rfl) ⟨2711940, by rfl⟩ : syracuseStep 7231841 = 5423881) B5423881
theorem B4821227 : Blo 2141435 4821227 := bstep (se 1 (by rfl) ⟨3615920, by rfl⟩ : syracuseStep 4821227 = 7231841) B7231841
theorem B3214151 : Blo 2141435 3214151 := bstep (se 1 (by rfl) ⟨2410613, by rfl⟩ : syracuseStep 3214151 = 4821227) B4821227
theorem B2142767 : Blo 2141435 2142767 := bstep (se 1 (by rfl) ⟨1607075, by rfl⟩ : syracuseStep 2142767 = 3214151) B3214151
theorem B3214157 : Blo 2141435 3214157 := bbase (se 3 (by rfl) ⟨602654, by rfl⟩ : syracuseStep 3214157 = 1205309) (by norm_num)
theorem B2142771 : Blo 2141435 2142771 := bstep (se 1 (by rfl) ⟨1607078, by rfl⟩ : syracuseStep 2142771 = 3214157) B3214157
theorem B4821245 : Blo 2141435 4821245 := bbase (se 3 (by rfl) ⟨903983, by rfl⟩ : syracuseStep 4821245 = 1807967) (by norm_num)
theorem B3214163 : Blo 2141435 3214163 := bstep (se 1 (by rfl) ⟨2410622, by rfl⟩ : syracuseStep 3214163 = 4821245) B4821245
theorem B2142775 : Blo 2141435 2142775 := bstep (se 1 (by rfl) ⟨1607081, by rfl⟩ : syracuseStep 2142775 = 3214163) B3214163
theorem B3615941 : Blo 2141435 3615941 := bbase (se 4 (by rfl) ⟨338994, by rfl⟩ : syracuseStep 3615941 = 677989) (by norm_num)
theorem B2410627 : Blo 2141435 2410627 := bstep (se 1 (by rfl) ⟨1807970, by rfl⟩ : syracuseStep 2410627 = 3615941) B3615941
theorem B3214169 : Blo 2141435 3214169 := bstep (se 2 (by rfl) ⟨1205313, by rfl⟩ : syracuseStep 3214169 = 2410627) B2410627
theorem B2142779 : Blo 2141435 2142779 := bstep (se 1 (by rfl) ⟨1607084, by rfl⟩ : syracuseStep 2142779 = 3214169) B3214169
theorem B16271765 : Blo 2141435 16271765 := bbase (se 6 (by rfl) ⟨381369, by rfl⟩ : syracuseStep 16271765 = 762739) (by norm_num)
theorem B10847843 : Blo 2141435 10847843 := bstep (se 1 (by rfl) ⟨8135882, by rfl⟩ : syracuseStep 10847843 = 16271765) B16271765
theorem B7231895 : Blo 2141435 7231895 := bstep (se 1 (by rfl) ⟨5423921, by rfl⟩ : syracuseStep 7231895 = 10847843) B10847843
theorem B4821263 : Blo 2141435 4821263 := bstep (se 1 (by rfl) ⟨3615947, by rfl⟩ : syracuseStep 4821263 = 7231895) B7231895
theorem B3214175 : Blo 2141435 3214175 := bstep (se 1 (by rfl) ⟨2410631, by rfl⟩ : syracuseStep 3214175 = 4821263) B4821263
theorem B2142783 : Blo 2141435 2142783 := bstep (se 1 (by rfl) ⟨1607087, by rfl⟩ : syracuseStep 2142783 = 3214175) B3214175
theorem B3214181 : Blo 2141435 3214181 := bbase (se 4 (by rfl) ⟨301329, by rfl⟩ : syracuseStep 3214181 = 602659) (by norm_num)
theorem B2142787 : Blo 2141435 2142787 := bstep (se 1 (by rfl) ⟨1607090, by rfl⟩ : syracuseStep 2142787 = 3214181) B3214181
theorem B4067957 : Blo 2141435 4067957 := bbase (se 5 (by rfl) ⟨190685, by rfl⟩ : syracuseStep 4067957 = 381371) (by norm_num)
theorem B2711971 : Blo 2141435 2711971 := bstep (se 1 (by rfl) ⟨2033978, by rfl⟩ : syracuseStep 2711971 = 4067957) B4067957
theorem B3615961 : Blo 2141435 3615961 := bstep (se 2 (by rfl) ⟨1355985, by rfl⟩ : syracuseStep 3615961 = 2711971) B2711971
theorem B4821281 : Blo 2141435 4821281 := bstep (se 2 (by rfl) ⟨1807980, by rfl⟩ : syracuseStep 4821281 = 3615961) B3615961
theorem B3214187 : Blo 2141435 3214187 := bstep (se 1 (by rfl) ⟨2410640, by rfl⟩ : syracuseStep 3214187 = 4821281) B4821281
theorem B2142791 : Blo 2141435 2142791 := bstep (se 1 (by rfl) ⟨1607093, by rfl⟩ : syracuseStep 2142791 = 3214187) B3214187
theorem B2410645 : Blo 2141435 2410645 := bbase (se 6 (by rfl) ⟨56499, by rfl⟩ : syracuseStep 2410645 = 112999) (by norm_num)
theorem B3214193 : Blo 2141435 3214193 := bstep (se 2 (by rfl) ⟨1205322, by rfl⟩ : syracuseStep 3214193 = 2410645) B2410645
theorem B2142795 : Blo 2141435 2142795 := bstep (se 1 (by rfl) ⟨1607096, by rfl⟩ : syracuseStep 2142795 = 3214193) B3214193
theorem B2711981 : Blo 2141435 2711981 := bbase (se 3 (by rfl) ⟨508496, by rfl⟩ : syracuseStep 2711981 = 1016993) (by norm_num)
theorem B7231949 : Blo 2141435 7231949 := bstep (se 3 (by rfl) ⟨1355990, by rfl⟩ : syracuseStep 7231949 = 2711981) B2711981
theorem B4821299 : Blo 2141435 4821299 := bstep (se 1 (by rfl) ⟨3615974, by rfl⟩ : syracuseStep 4821299 = 7231949) B7231949
theorem B3214199 : Blo 2141435 3214199 := bstep (se 1 (by rfl) ⟨2410649, by rfl⟩ : syracuseStep 3214199 = 4821299) B4821299
theorem B2142799 : Blo 2141435 2142799 := bstep (se 1 (by rfl) ⟨1607099, by rfl⟩ : syracuseStep 2142799 = 3214199) B3214199
theorem B3214205 : Blo 2141435 3214205 := bbase (se 3 (by rfl) ⟨602663, by rfl⟩ : syracuseStep 3214205 = 1205327) (by norm_num)
theorem B2142803 : Blo 2141435 2142803 := bstep (se 1 (by rfl) ⟨1607102, by rfl⟩ : syracuseStep 2142803 = 3214205) B3214205
theorem B4821317 : Blo 2141435 4821317 := bbase (se 4 (by rfl) ⟨451998, by rfl⟩ : syracuseStep 4821317 = 903997) (by norm_num)
theorem B3214211 : Blo 2141435 3214211 := bstep (se 1 (by rfl) ⟨2410658, by rfl⟩ : syracuseStep 3214211 = 4821317) B4821317
theorem B2142807 : Blo 2141435 2142807 := bstep (se 1 (by rfl) ⟨1607105, by rfl⟩ : syracuseStep 2142807 = 3214211) B3214211
theorem B4766381 : Blo 2141435 4766381 := bbase (se 3 (by rfl) ⟨893696, by rfl⟩ : syracuseStep 4766381 = 1787393) (by norm_num)
theorem B3177587 : Blo 2141435 3177587 := bstep (se 1 (by rfl) ⟨2383190, by rfl⟩ : syracuseStep 3177587 = 4766381) B4766381
theorem B8473565 : Blo 2141435 8473565 := bstep (se 3 (by rfl) ⟨1588793, by rfl⟩ : syracuseStep 8473565 = 3177587) B3177587
theorem B5649043 : Blo 2141435 5649043 := bstep (se 1 (by rfl) ⟨4236782, by rfl⟩ : syracuseStep 5649043 = 8473565) B8473565
theorem B7532057 : Blo 2141435 7532057 := bstep (se 2 (by rfl) ⟨2824521, by rfl⟩ : syracuseStep 7532057 = 5649043) B5649043
theorem B5021371 : Blo 2141435 5021371 := bstep (se 1 (by rfl) ⟨3766028, by rfl⟩ : syracuseStep 5021371 = 7532057) B7532057
theorem B26780645 : Blo 2141435 26780645 := bstep (se 4 (by rfl) ⟨2510685, by rfl⟩ : syracuseStep 26780645 = 5021371) B5021371
theorem B17853763 : Blo 2141435 17853763 := bstep (se 1 (by rfl) ⟨13390322, by rfl⟩ : syracuseStep 17853763 = 26780645) B26780645
theorem B23805017 : Blo 2141435 23805017 := bstep (se 2 (by rfl) ⟨8926881, by rfl⟩ : syracuseStep 23805017 = 17853763) B17853763
theorem B15870011 : Blo 2141435 15870011 := bstep (se 1 (by rfl) ⟨11902508, by rfl⟩ : syracuseStep 15870011 = 23805017) B23805017
theorem B42320029 : Blo 2141435 42320029 := bstep (se 3 (by rfl) ⟨7935005, by rfl⟩ : syracuseStep 42320029 = 15870011) B15870011
theorem B56426705 : Blo 2141435 56426705 := bstep (se 2 (by rfl) ⟨21160014, by rfl⟩ : syracuseStep 56426705 = 42320029) B42320029
theorem B37617803 : Blo 2141435 37617803 := bstep (se 1 (by rfl) ⟨28213352, by rfl⟩ : syracuseStep 37617803 = 56426705) B56426705
theorem B25078535 : Blo 2141435 25078535 := bstep (se 1 (by rfl) ⟨18808901, by rfl⟩ : syracuseStep 25078535 = 37617803) B37617803
theorem B16719023 : Blo 2141435 16719023 := bstep (se 1 (by rfl) ⟨12539267, by rfl⟩ : syracuseStep 16719023 = 25078535) B25078535
theorem B11146015 : Blo 2141435 11146015 := bstep (se 1 (by rfl) ⟨8359511, by rfl⟩ : syracuseStep 11146015 = 16719023) B16719023
theorem B59445413 : Blo 2141435 59445413 := bstep (se 4 (by rfl) ⟨5573007, by rfl⟩ : syracuseStep 59445413 = 11146015) B11146015
theorem B39630275 : Blo 2141435 39630275 := bstep (se 1 (by rfl) ⟨29722706, by rfl⟩ : syracuseStep 39630275 = 59445413) B59445413
theorem B26420183 : Blo 2141435 26420183 := bstep (se 1 (by rfl) ⟨19815137, by rfl⟩ : syracuseStep 26420183 = 39630275) B39630275
theorem B17613455 : Blo 2141435 17613455 := bstep (se 1 (by rfl) ⟨13210091, by rfl⟩ : syracuseStep 17613455 = 26420183) B26420183
theorem B46969213 : Blo 2141435 46969213 := bstep (se 3 (by rfl) ⟨8806727, by rfl⟩ : syracuseStep 46969213 = 17613455) B17613455
theorem B62625617 : Blo 2141435 62625617 := bstep (se 2 (by rfl) ⟨23484606, by rfl⟩ : syracuseStep 62625617 = 46969213) B46969213
theorem B41750411 : Blo 2141435 41750411 := bstep (se 1 (by rfl) ⟨31312808, by rfl⟩ : syracuseStep 41750411 = 62625617) B62625617
theorem B111334429 : Blo 2141435 111334429 := bstep (se 3 (by rfl) ⟨20875205, by rfl⟩ : syracuseStep 111334429 = 41750411) B41750411
theorem B148445905 : Blo 2141435 148445905 := bstep (se 2 (by rfl) ⟨55667214, by rfl⟩ : syracuseStep 148445905 = 111334429) B111334429
theorem B197927873 : Blo 2141435 197927873 := bstep (se 2 (by rfl) ⟨74222952, by rfl⟩ : syracuseStep 197927873 = 148445905) B148445905
theorem B131951915 : Blo 2141435 131951915 := bstep (se 1 (by rfl) ⟨98963936, by rfl⟩ : syracuseStep 131951915 = 197927873) B197927873
theorem B87967943 : Blo 2141435 87967943 := bstep (se 1 (by rfl) ⟨65975957, by rfl⟩ : syracuseStep 87967943 = 131951915) B131951915
theorem B58645295 : Blo 2141435 58645295 := bstep (se 1 (by rfl) ⟨43983971, by rfl⟩ : syracuseStep 58645295 = 87967943) B87967943
theorem B39096863 : Blo 2141435 39096863 := bstep (se 1 (by rfl) ⟨29322647, by rfl⟩ : syracuseStep 39096863 = 58645295) B58645295
theorem B26064575 : Blo 2141435 26064575 := bstep (se 1 (by rfl) ⟨19548431, by rfl⟩ : syracuseStep 26064575 = 39096863) B39096863
theorem B17376383 : Blo 2141435 17376383 := bstep (se 1 (by rfl) ⟨13032287, by rfl⟩ : syracuseStep 17376383 = 26064575) B26064575
theorem B11584255 : Blo 2141435 11584255 := bstep (se 1 (by rfl) ⟨8688191, by rfl⟩ : syracuseStep 11584255 = 17376383) B17376383
theorem B15445673 : Blo 2141435 15445673 := bstep (se 2 (by rfl) ⟨5792127, by rfl⟩ : syracuseStep 15445673 = 11584255) B11584255
theorem B10297115 : Blo 2141435 10297115 := bstep (se 1 (by rfl) ⟨7722836, by rfl⟩ : syracuseStep 10297115 = 15445673) B15445673
theorem B6864743 : Blo 2141435 6864743 := bstep (se 1 (by rfl) ⟨5148557, by rfl⟩ : syracuseStep 6864743 = 10297115) B10297115
theorem B4576495 : Blo 2141435 4576495 := bstep (se 1 (by rfl) ⟨3432371, by rfl⟩ : syracuseStep 4576495 = 6864743) B6864743
theorem B6101993 : Blo 2141435 6101993 := bstep (se 2 (by rfl) ⟨2288247, by rfl⟩ : syracuseStep 6101993 = 4576495) B4576495
theorem B4067995 : Blo 2141435 4067995 := bstep (se 1 (by rfl) ⟨3050996, by rfl⟩ : syracuseStep 4067995 = 6101993) B6101993
theorem B5423993 : Blo 2141435 5423993 := bstep (se 2 (by rfl) ⟨2033997, by rfl⟩ : syracuseStep 5423993 = 4067995) B4067995
theorem B3615995 : Blo 2141435 3615995 := bstep (se 1 (by rfl) ⟨2711996, by rfl⟩ : syracuseStep 3615995 = 5423993) B5423993
theorem B2410663 : Blo 2141435 2410663 := bstep (se 1 (by rfl) ⟨1807997, by rfl⟩ : syracuseStep 2410663 = 3615995) B3615995
theorem B3214217 : Blo 2141435 3214217 := bstep (se 2 (by rfl) ⟨1205331, by rfl⟩ : syracuseStep 3214217 = 2410663) B2410663
theorem B2142811 : Blo 2141435 2142811 := bstep (se 1 (by rfl) ⟨1607108, by rfl⟩ : syracuseStep 2142811 = 3214217) B3214217
theorem B10848005 : Blo 2141435 10848005 := bbase (se 4 (by rfl) ⟨1017000, by rfl⟩ : syracuseStep 10848005 = 2034001) (by norm_num)
theorem B7232003 : Blo 2141435 7232003 := bstep (se 1 (by rfl) ⟨5424002, by rfl⟩ : syracuseStep 7232003 = 10848005) B10848005
theorem B4821335 : Blo 2141435 4821335 := bstep (se 1 (by rfl) ⟨3616001, by rfl⟩ : syracuseStep 4821335 = 7232003) B7232003
theorem B3214223 : Blo 2141435 3214223 := bstep (se 1 (by rfl) ⟨2410667, by rfl⟩ : syracuseStep 3214223 = 4821335) B4821335
theorem B2142815 : Blo 2141435 2142815 := bstep (se 1 (by rfl) ⟨1607111, by rfl⟩ : syracuseStep 2142815 = 3214223) B3214223
theorem B3214229 : Blo 2141435 3214229 := bbase (se 6 (by rfl) ⟨75333, by rfl⟩ : syracuseStep 3214229 = 150667) (by norm_num)
theorem B2142819 : Blo 2141435 2142819 := bstep (se 1 (by rfl) ⟨1607114, by rfl⟩ : syracuseStep 2142819 = 3214229) B3214229
theorem B12204053 : Blo 2141435 12204053 := bbase (se 6 (by rfl) ⟨286032, by rfl⟩ : syracuseStep 12204053 = 572065) (by norm_num)
theorem B8136035 : Blo 2141435 8136035 := bstep (se 1 (by rfl) ⟨6102026, by rfl⟩ : syracuseStep 8136035 = 12204053) B12204053
theorem B5424023 : Blo 2141435 5424023 := bstep (se 1 (by rfl) ⟨4068017, by rfl⟩ : syracuseStep 5424023 = 8136035) B8136035
theorem B3616015 : Blo 2141435 3616015 := bstep (se 1 (by rfl) ⟨2712011, by rfl⟩ : syracuseStep 3616015 = 5424023) B5424023
theorem B4821353 : Blo 2141435 4821353 := bstep (se 2 (by rfl) ⟨1808007, by rfl⟩ : syracuseStep 4821353 = 3616015) B3616015
theorem B3214235 : Blo 2141435 3214235 := bstep (se 1 (by rfl) ⟨2410676, by rfl⟩ : syracuseStep 3214235 = 4821353) B4821353
theorem B2142823 : Blo 2141435 2142823 := bstep (se 1 (by rfl) ⟨1607117, by rfl⟩ : syracuseStep 2142823 = 3214235) B3214235
theorem B2410681 : Blo 2141435 2410681 := bbase (se 2 (by rfl) ⟨904005, by rfl⟩ : syracuseStep 2410681 = 1808011) (by norm_num)
theorem B3214241 : Blo 2141435 3214241 := bstep (se 2 (by rfl) ⟨1205340, by rfl⟩ : syracuseStep 3214241 = 2410681) B2410681
theorem B2142827 : Blo 2141435 2142827 := bstep (se 1 (by rfl) ⟨1607120, by rfl⟩ : syracuseStep 2142827 = 3214241) B3214241
theorem B5148605 : Blo 2141435 5148605 := bbase (se 3 (by rfl) ⟨965363, by rfl⟩ : syracuseStep 5148605 = 1930727) (by norm_num)
theorem B3432403 : Blo 2141435 3432403 := bstep (se 1 (by rfl) ⟨2574302, by rfl⟩ : syracuseStep 3432403 = 5148605) B5148605
theorem B4576537 : Blo 2141435 4576537 := bstep (se 2 (by rfl) ⟨1716201, by rfl⟩ : syracuseStep 4576537 = 3432403) B3432403
theorem B6102049 : Blo 2141435 6102049 := bstep (se 2 (by rfl) ⟨2288268, by rfl⟩ : syracuseStep 6102049 = 4576537) B4576537
theorem B8136065 : Blo 2141435 8136065 := bstep (se 2 (by rfl) ⟨3051024, by rfl⟩ : syracuseStep 8136065 = 6102049) B6102049
theorem B5424043 : Blo 2141435 5424043 := bstep (se 1 (by rfl) ⟨4068032, by rfl⟩ : syracuseStep 5424043 = 8136065) B8136065
theorem B7232057 : Blo 2141435 7232057 := bstep (se 2 (by rfl) ⟨2712021, by rfl⟩ : syracuseStep 7232057 = 5424043) B5424043
theorem B4821371 : Blo 2141435 4821371 := bstep (se 1 (by rfl) ⟨3616028, by rfl⟩ : syracuseStep 4821371 = 7232057) B7232057
theorem B3214247 : Blo 2141435 3214247 := bstep (se 1 (by rfl) ⟨2410685, by rfl⟩ : syracuseStep 3214247 = 4821371) B4821371
theorem B2142831 : Blo 2141435 2142831 := bstep (se 1 (by rfl) ⟨1607123, by rfl⟩ : syracuseStep 2142831 = 3214247) B3214247
theorem B3214253 : Blo 2141435 3214253 := bbase (se 3 (by rfl) ⟨602672, by rfl⟩ : syracuseStep 3214253 = 1205345) (by norm_num)
theorem B2142835 : Blo 2141435 2142835 := bstep (se 1 (by rfl) ⟨1607126, by rfl⟩ : syracuseStep 2142835 = 3214253) B3214253
theorem B4821389 : Blo 2141435 4821389 := bbase (se 3 (by rfl) ⟨904010, by rfl⟩ : syracuseStep 4821389 = 1808021) (by norm_num)
theorem B3214259 : Blo 2141435 3214259 := bstep (se 1 (by rfl) ⟨2410694, by rfl⟩ : syracuseStep 3214259 = 4821389) B4821389
theorem B2142839 : Blo 2141435 2142839 := bstep (se 1 (by rfl) ⟨1607129, by rfl⟩ : syracuseStep 2142839 = 3214259) B3214259
theorem B2712037 : Blo 2141435 2712037 := bbase (se 4 (by rfl) ⟨254253, by rfl⟩ : syracuseStep 2712037 = 508507) (by norm_num)
theorem B3616049 : Blo 2141435 3616049 := bstep (se 2 (by rfl) ⟨1356018, by rfl⟩ : syracuseStep 3616049 = 2712037) B2712037
theorem B2410699 : Blo 2141435 2410699 := bstep (se 1 (by rfl) ⟨1808024, by rfl⟩ : syracuseStep 2410699 = 3616049) B3616049
theorem B3214265 : Blo 2141435 3214265 := bstep (se 2 (by rfl) ⟨1205349, by rfl⟩ : syracuseStep 3214265 = 2410699) B2410699
theorem B2142843 : Blo 2141435 2142843 := bstep (se 1 (by rfl) ⟨1607132, by rfl⟩ : syracuseStep 2142843 = 3214265) B3214265
theorem B9907733 : Blo 2141435 9907733 := bbase (se 6 (by rfl) ⟨232212, by rfl⟩ : syracuseStep 9907733 = 464425) (by norm_num)
theorem B6605155 : Blo 2141435 6605155 := bstep (se 1 (by rfl) ⟨4953866, by rfl⟩ : syracuseStep 6605155 = 9907733) B9907733
theorem B8806873 : Blo 2141435 8806873 := bstep (se 2 (by rfl) ⟨3302577, by rfl⟩ : syracuseStep 8806873 = 6605155) B6605155
theorem B11742497 : Blo 2141435 11742497 := bstep (se 2 (by rfl) ⟨4403436, by rfl⟩ : syracuseStep 11742497 = 8806873) B8806873
theorem B7828331 : Blo 2141435 7828331 := bstep (se 1 (by rfl) ⟨5871248, by rfl⟩ : syracuseStep 7828331 = 11742497) B11742497
theorem B83502197 : Blo 2141435 83502197 := bstep (se 5 (by rfl) ⟨3914165, by rfl⟩ : syracuseStep 83502197 = 7828331) B7828331
theorem B55668131 : Blo 2141435 55668131 := bstep (se 1 (by rfl) ⟨41751098, by rfl⟩ : syracuseStep 55668131 = 83502197) B83502197
theorem B37112087 : Blo 2141435 37112087 := bstep (se 1 (by rfl) ⟨27834065, by rfl⟩ : syracuseStep 37112087 = 55668131) B55668131
theorem B24741391 : Blo 2141435 24741391 := bstep (se 1 (by rfl) ⟨18556043, by rfl⟩ : syracuseStep 24741391 = 37112087) B37112087
theorem B32988521 : Blo 2141435 32988521 := bstep (se 2 (by rfl) ⟨12370695, by rfl⟩ : syracuseStep 32988521 = 24741391) B24741391
theorem B21992347 : Blo 2141435 21992347 := bstep (se 1 (by rfl) ⟨16494260, by rfl⟩ : syracuseStep 21992347 = 32988521) B32988521
theorem B29323129 : Blo 2141435 29323129 := bstep (se 2 (by rfl) ⟨10996173, by rfl⟩ : syracuseStep 29323129 = 21992347) B21992347
theorem B39097505 : Blo 2141435 39097505 := bstep (se 2 (by rfl) ⟨14661564, by rfl⟩ : syracuseStep 39097505 = 29323129) B29323129
theorem B26065003 : Blo 2141435 26065003 := bstep (se 1 (by rfl) ⟨19548752, by rfl⟩ : syracuseStep 26065003 = 39097505) B39097505
theorem B34753337 : Blo 2141435 34753337 := bstep (se 2 (by rfl) ⟨13032501, by rfl⟩ : syracuseStep 34753337 = 26065003) B26065003
theorem B23168891 : Blo 2141435 23168891 := bstep (se 1 (by rfl) ⟨17376668, by rfl⟩ : syracuseStep 23168891 = 34753337) B34753337
theorem B15445927 : Blo 2141435 15445927 := bstep (se 1 (by rfl) ⟨11584445, by rfl⟩ : syracuseStep 15445927 = 23168891) B23168891
theorem B20594569 : Blo 2141435 20594569 := bstep (se 2 (by rfl) ⟨7722963, by rfl⟩ : syracuseStep 20594569 = 15445927) B15445927
theorem B27459425 : Blo 2141435 27459425 := bstep (se 2 (by rfl) ⟨10297284, by rfl⟩ : syracuseStep 27459425 = 20594569) B20594569
theorem B18306283 : Blo 2141435 18306283 := bstep (se 1 (by rfl) ⟨13729712, by rfl⟩ : syracuseStep 18306283 = 27459425) B27459425
theorem B24408377 : Blo 2141435 24408377 := bstep (se 2 (by rfl) ⟨9153141, by rfl⟩ : syracuseStep 24408377 = 18306283) B18306283
theorem B16272251 : Blo 2141435 16272251 := bstep (se 1 (by rfl) ⟨12204188, by rfl⟩ : syracuseStep 16272251 = 24408377) B24408377
theorem B10848167 : Blo 2141435 10848167 := bstep (se 1 (by rfl) ⟨8136125, by rfl⟩ : syracuseStep 10848167 = 16272251) B16272251
theorem B7232111 : Blo 2141435 7232111 := bstep (se 1 (by rfl) ⟨5424083, by rfl⟩ : syracuseStep 7232111 = 10848167) B10848167
theorem B4821407 : Blo 2141435 4821407 := bstep (se 1 (by rfl) ⟨3616055, by rfl⟩ : syracuseStep 4821407 = 7232111) B7232111
theorem B3214271 : Blo 2141435 3214271 := bstep (se 1 (by rfl) ⟨2410703, by rfl⟩ : syracuseStep 3214271 = 4821407) B4821407
theorem B2142847 : Blo 2141435 2142847 := bstep (se 1 (by rfl) ⟨1607135, by rfl⟩ : syracuseStep 2142847 = 3214271) B3214271
theorem B3214277 : Blo 2141435 3214277 := bbase (se 4 (by rfl) ⟨301338, by rfl⟩ : syracuseStep 3214277 = 602677) (by norm_num)
theorem B2142851 : Blo 2141435 2142851 := bstep (se 1 (by rfl) ⟨1607138, by rfl⟩ : syracuseStep 2142851 = 3214277) B3214277
theorem B3616069 : Blo 2141435 3616069 := bbase (se 4 (by rfl) ⟨339006, by rfl⟩ : syracuseStep 3616069 = 678013) (by norm_num)
theorem B4821425 : Blo 2141435 4821425 := bstep (se 2 (by rfl) ⟨1808034, by rfl⟩ : syracuseStep 4821425 = 3616069) B3616069
theorem B3214283 : Blo 2141435 3214283 := bstep (se 1 (by rfl) ⟨2410712, by rfl⟩ : syracuseStep 3214283 = 4821425) B4821425
theorem B2142855 : Blo 2141435 2142855 := bstep (se 1 (by rfl) ⟨1607141, by rfl⟩ : syracuseStep 2142855 = 3214283) B3214283
theorem B2410717 : Blo 2141435 2410717 := bbase (se 3 (by rfl) ⟨452009, by rfl⟩ : syracuseStep 2410717 = 904019) (by norm_num)
theorem B3214289 : Blo 2141435 3214289 := bstep (se 2 (by rfl) ⟨1205358, by rfl⟩ : syracuseStep 3214289 = 2410717) B2410717
theorem B2142859 : Blo 2141435 2142859 := bstep (se 1 (by rfl) ⟨1607144, by rfl⟩ : syracuseStep 2142859 = 3214289) B3214289
theorem B7232165 : Blo 2141435 7232165 := bbase (se 4 (by rfl) ⟨678015, by rfl⟩ : syracuseStep 7232165 = 1356031) (by norm_num)
theorem B4821443 : Blo 2141435 4821443 := bstep (se 1 (by rfl) ⟨3616082, by rfl⟩ : syracuseStep 4821443 = 7232165) B7232165
theorem B3214295 : Blo 2141435 3214295 := bstep (se 1 (by rfl) ⟨2410721, by rfl⟩ : syracuseStep 3214295 = 4821443) B4821443
theorem B2142863 : Blo 2141435 2142863 := bstep (se 1 (by rfl) ⟨1607147, by rfl⟩ : syracuseStep 2142863 = 3214295) B3214295
theorem B3214301 : Blo 2141435 3214301 := bbase (se 3 (by rfl) ⟨602681, by rfl⟩ : syracuseStep 3214301 = 1205363) (by norm_num)
theorem B2142867 : Blo 2141435 2142867 := bstep (se 1 (by rfl) ⟨1607150, by rfl⟩ : syracuseStep 2142867 = 3214301) B3214301
theorem B4821461 : Blo 2141435 4821461 := bbase (se 7 (by rfl) ⟨56501, by rfl⟩ : syracuseStep 4821461 = 113003) (by norm_num)
theorem B3214307 : Blo 2141435 3214307 := bstep (se 1 (by rfl) ⟨2410730, by rfl⟩ : syracuseStep 3214307 = 4821461) B4821461
theorem B2142871 : Blo 2141435 2142871 := bstep (se 1 (by rfl) ⟨1607153, by rfl⟩ : syracuseStep 2142871 = 3214307) B3214307
theorem B3302621 : Blo 2141435 3302621 := bbase (se 3 (by rfl) ⟨619241, by rfl⟩ : syracuseStep 3302621 = 1238483) (by norm_num)
theorem B35227957 : Blo 2141435 35227957 := bstep (se 5 (by rfl) ⟨1651310, by rfl⟩ : syracuseStep 35227957 = 3302621) B3302621
theorem B46970609 : Blo 2141435 46970609 := bstep (se 2 (by rfl) ⟨17613978, by rfl⟩ : syracuseStep 46970609 = 35227957) B35227957
theorem B125254957 : Blo 2141435 125254957 := bstep (se 3 (by rfl) ⟨23485304, by rfl⟩ : syracuseStep 125254957 = 46970609) B46970609
theorem B167006609 : Blo 2141435 167006609 := bstep (se 2 (by rfl) ⟨62627478, by rfl⟩ : syracuseStep 167006609 = 125254957) B125254957
theorem B111337739 : Blo 2141435 111337739 := bstep (se 1 (by rfl) ⟨83503304, by rfl⟩ : syracuseStep 111337739 = 167006609) B167006609
theorem B74225159 : Blo 2141435 74225159 := bstep (se 1 (by rfl) ⟨55668869, by rfl⟩ : syracuseStep 74225159 = 111337739) B111337739
theorem B49483439 : Blo 2141435 49483439 := bstep (se 1 (by rfl) ⟨37112579, by rfl⟩ : syracuseStep 49483439 = 74225159) B74225159
theorem B32988959 : Blo 2141435 32988959 := bstep (se 1 (by rfl) ⟨24741719, by rfl⟩ : syracuseStep 32988959 = 49483439) B49483439
theorem B21992639 : Blo 2141435 21992639 := bstep (se 1 (by rfl) ⟨16494479, by rfl⟩ : syracuseStep 21992639 = 32988959) B32988959
theorem B58647037 : Blo 2141435 58647037 := bstep (se 3 (by rfl) ⟨10996319, by rfl⟩ : syracuseStep 58647037 = 21992639) B21992639
theorem B78196049 : Blo 2141435 78196049 := bstep (se 2 (by rfl) ⟨29323518, by rfl⟩ : syracuseStep 78196049 = 58647037) B58647037
theorem B52130699 : Blo 2141435 52130699 := bstep (se 1 (by rfl) ⟨39098024, by rfl⟩ : syracuseStep 52130699 = 78196049) B78196049
theorem B34753799 : Blo 2141435 34753799 := bstep (se 1 (by rfl) ⟨26065349, by rfl⟩ : syracuseStep 34753799 = 52130699) B52130699
theorem B23169199 : Blo 2141435 23169199 := bstep (se 1 (by rfl) ⟨17376899, by rfl⟩ : syracuseStep 23169199 = 34753799) B34753799
theorem B30892265 : Blo 2141435 30892265 := bstep (se 2 (by rfl) ⟨11584599, by rfl⟩ : syracuseStep 30892265 = 23169199) B23169199
theorem B20594843 : Blo 2141435 20594843 := bstep (se 1 (by rfl) ⟨15446132, by rfl⟩ : syracuseStep 20594843 = 30892265) B30892265
theorem B13729895 : Blo 2141435 13729895 := bstep (se 1 (by rfl) ⟨10297421, by rfl⟩ : syracuseStep 13729895 = 20594843) B20594843
theorem B9153263 : Blo 2141435 9153263 := bstep (se 1 (by rfl) ⟨6864947, by rfl⟩ : syracuseStep 9153263 = 13729895) B13729895
theorem B6102175 : Blo 2141435 6102175 := bstep (se 1 (by rfl) ⟨4576631, by rfl⟩ : syracuseStep 6102175 = 9153263) B9153263
theorem B8136233 : Blo 2141435 8136233 := bstep (se 2 (by rfl) ⟨3051087, by rfl⟩ : syracuseStep 8136233 = 6102175) B6102175
theorem B5424155 : Blo 2141435 5424155 := bstep (se 1 (by rfl) ⟨4068116, by rfl⟩ : syracuseStep 5424155 = 8136233) B8136233
theorem B3616103 : Blo 2141435 3616103 := bstep (se 1 (by rfl) ⟨2712077, by rfl⟩ : syracuseStep 3616103 = 5424155) B5424155
theorem B2410735 : Blo 2141435 2410735 := bstep (se 1 (by rfl) ⟨1808051, by rfl⟩ : syracuseStep 2410735 = 3616103) B3616103
theorem B3214313 : Blo 2141435 3214313 := bstep (se 2 (by rfl) ⟨1205367, by rfl⟩ : syracuseStep 3214313 = 2410735) B2410735
theorem B2142875 : Blo 2141435 2142875 := bstep (se 1 (by rfl) ⟨1607156, by rfl⟩ : syracuseStep 2142875 = 3214313) B3214313
theorem B11742677 : Blo 2141435 11742677 := bbase (se 7 (by rfl) ⟨137609, by rfl⟩ : syracuseStep 11742677 = 275219) (by norm_num)
theorem B7828451 : Blo 2141435 7828451 := bstep (se 1 (by rfl) ⟨5871338, by rfl⟩ : syracuseStep 7828451 = 11742677) B11742677
theorem B5218967 : Blo 2141435 5218967 := bstep (se 1 (by rfl) ⟨3914225, by rfl⟩ : syracuseStep 5218967 = 7828451) B7828451
theorem B3479311 : Blo 2141435 3479311 := bstep (se 1 (by rfl) ⟨2609483, by rfl⟩ : syracuseStep 3479311 = 5218967) B5218967
theorem B4639081 : Blo 2141435 4639081 := bstep (se 2 (by rfl) ⟨1739655, by rfl⟩ : syracuseStep 4639081 = 3479311) B3479311
theorem B6185441 : Blo 2141435 6185441 := bstep (se 2 (by rfl) ⟨2319540, by rfl⟩ : syracuseStep 6185441 = 4639081) B4639081
theorem B16494509 : Blo 2141435 16494509 := bstep (se 3 (by rfl) ⟨3092720, by rfl⟩ : syracuseStep 16494509 = 6185441) B6185441
theorem B10996339 : Blo 2141435 10996339 := bstep (se 1 (by rfl) ⟨8247254, by rfl⟩ : syracuseStep 10996339 = 16494509) B16494509
theorem B14661785 : Blo 2141435 14661785 := bstep (se 2 (by rfl) ⟨5498169, by rfl⟩ : syracuseStep 14661785 = 10996339) B10996339
theorem B9774523 : Blo 2141435 9774523 := bstep (se 1 (by rfl) ⟨7330892, by rfl⟩ : syracuseStep 9774523 = 14661785) B14661785
theorem B52130789 : Blo 2141435 52130789 := bstep (se 4 (by rfl) ⟨4887261, by rfl⟩ : syracuseStep 52130789 = 9774523) B9774523
theorem B34753859 : Blo 2141435 34753859 := bstep (se 1 (by rfl) ⟨26065394, by rfl⟩ : syracuseStep 34753859 = 52130789) B52130789
theorem B23169239 : Blo 2141435 23169239 := bstep (se 1 (by rfl) ⟨17376929, by rfl⟩ : syracuseStep 23169239 = 34753859) B34753859
theorem B15446159 : Blo 2141435 15446159 := bstep (se 1 (by rfl) ⟨11584619, by rfl⟩ : syracuseStep 15446159 = 23169239) B23169239
theorem B10297439 : Blo 2141435 10297439 := bstep (se 1 (by rfl) ⟨7723079, by rfl⟩ : syracuseStep 10297439 = 15446159) B15446159
theorem B6864959 : Blo 2141435 6864959 := bstep (se 1 (by rfl) ⟨5148719, by rfl⟩ : syracuseStep 6864959 = 10297439) B10297439
theorem B18306557 : Blo 2141435 18306557 := bstep (se 3 (by rfl) ⟨3432479, by rfl⟩ : syracuseStep 18306557 = 6864959) B6864959
theorem B12204371 : Blo 2141435 12204371 := bstep (se 1 (by rfl) ⟨9153278, by rfl⟩ : syracuseStep 12204371 = 18306557) B18306557
theorem B8136247 : Blo 2141435 8136247 := bstep (se 1 (by rfl) ⟨6102185, by rfl⟩ : syracuseStep 8136247 = 12204371) B12204371
theorem B10848329 : Blo 2141435 10848329 := bstep (se 2 (by rfl) ⟨4068123, by rfl⟩ : syracuseStep 10848329 = 8136247) B8136247
theorem B7232219 : Blo 2141435 7232219 := bstep (se 1 (by rfl) ⟨5424164, by rfl⟩ : syracuseStep 7232219 = 10848329) B10848329
theorem B4821479 : Blo 2141435 4821479 := bstep (se 1 (by rfl) ⟨3616109, by rfl⟩ : syracuseStep 4821479 = 7232219) B7232219
theorem B3214319 : Blo 2141435 3214319 := bstep (se 1 (by rfl) ⟨2410739, by rfl⟩ : syracuseStep 3214319 = 4821479) B4821479
theorem B2142879 : Blo 2141435 2142879 := bstep (se 1 (by rfl) ⟨1607159, by rfl⟩ : syracuseStep 2142879 = 3214319) B3214319
theorem B3214325 : Blo 2141435 3214325 := bbase (se 5 (by rfl) ⟨150671, by rfl⟩ : syracuseStep 3214325 = 301343) (by norm_num)
theorem B2142883 : Blo 2141435 2142883 := bstep (se 1 (by rfl) ⟨1607162, by rfl⟩ : syracuseStep 2142883 = 3214325) B3214325
theorem B3432493 : Blo 2141435 3432493 := bbase (se 3 (by rfl) ⟨643592, by rfl⟩ : syracuseStep 3432493 = 1287185) (by norm_num)
theorem B4576657 : Blo 2141435 4576657 := bstep (se 2 (by rfl) ⟨1716246, by rfl⟩ : syracuseStep 4576657 = 3432493) B3432493
theorem B6102209 : Blo 2141435 6102209 := bstep (se 2 (by rfl) ⟨2288328, by rfl⟩ : syracuseStep 6102209 = 4576657) B4576657
theorem B4068139 : Blo 2141435 4068139 := bstep (se 1 (by rfl) ⟨3051104, by rfl⟩ : syracuseStep 4068139 = 6102209) B6102209
theorem B5424185 : Blo 2141435 5424185 := bstep (se 2 (by rfl) ⟨2034069, by rfl⟩ : syracuseStep 5424185 = 4068139) B4068139
theorem B3616123 : Blo 2141435 3616123 := bstep (se 1 (by rfl) ⟨2712092, by rfl⟩ : syracuseStep 3616123 = 5424185) B5424185
theorem B4821497 : Blo 2141435 4821497 := bstep (se 2 (by rfl) ⟨1808061, by rfl⟩ : syracuseStep 4821497 = 3616123) B3616123
theorem B3214331 : Blo 2141435 3214331 := bstep (se 1 (by rfl) ⟨2410748, by rfl⟩ : syracuseStep 3214331 = 4821497) B4821497
theorem B2142887 : Blo 2141435 2142887 := bstep (se 1 (by rfl) ⟨1607165, by rfl⟩ : syracuseStep 2142887 = 3214331) B3214331
theorem B2410753 : Blo 2141435 2410753 := bbase (se 2 (by rfl) ⟨904032, by rfl⟩ : syracuseStep 2410753 = 1808065) (by norm_num)
theorem B3214337 : Blo 2141435 3214337 := bstep (se 2 (by rfl) ⟨1205376, by rfl⟩ : syracuseStep 3214337 = 2410753) B2410753
theorem B2142891 : Blo 2141435 2142891 := bstep (se 1 (by rfl) ⟨1607168, by rfl⟩ : syracuseStep 2142891 = 3214337) B3214337
theorem B5424205 : Blo 2141435 5424205 := bbase (se 3 (by rfl) ⟨1017038, by rfl⟩ : syracuseStep 5424205 = 2034077) (by norm_num)
theorem B7232273 : Blo 2141435 7232273 := bstep (se 2 (by rfl) ⟨2712102, by rfl⟩ : syracuseStep 7232273 = 5424205) B5424205
theorem B4821515 : Blo 2141435 4821515 := bstep (se 1 (by rfl) ⟨3616136, by rfl⟩ : syracuseStep 4821515 = 7232273) B7232273
theorem B3214343 : Blo 2141435 3214343 := bstep (se 1 (by rfl) ⟨2410757, by rfl⟩ : syracuseStep 3214343 = 4821515) B4821515
theorem B2142895 : Blo 2141435 2142895 := bstep (se 1 (by rfl) ⟨1607171, by rfl⟩ : syracuseStep 2142895 = 3214343) B3214343
theorem B3214349 : Blo 2141435 3214349 := bbase (se 3 (by rfl) ⟨602690, by rfl⟩ : syracuseStep 3214349 = 1205381) (by norm_num)
theorem B2142899 : Blo 2141435 2142899 := bstep (se 1 (by rfl) ⟨1607174, by rfl⟩ : syracuseStep 2142899 = 3214349) B3214349
theorem B4821533 : Blo 2141435 4821533 := bbase (se 3 (by rfl) ⟨904037, by rfl⟩ : syracuseStep 4821533 = 1808075) (by norm_num)
theorem B3214355 : Blo 2141435 3214355 := bstep (se 1 (by rfl) ⟨2410766, by rfl⟩ : syracuseStep 3214355 = 4821533) B4821533
theorem B2142903 : Blo 2141435 2142903 := bstep (se 1 (by rfl) ⟨1607177, by rfl⟩ : syracuseStep 2142903 = 3214355) B3214355
theorem B3616157 : Blo 2141435 3616157 := bbase (se 3 (by rfl) ⟨678029, by rfl⟩ : syracuseStep 3616157 = 1356059) (by norm_num)
theorem B2410771 : Blo 2141435 2410771 := bstep (se 1 (by rfl) ⟨1808078, by rfl⟩ : syracuseStep 2410771 = 3616157) B3616157
theorem B3214361 : Blo 2141435 3214361 := bstep (se 2 (by rfl) ⟨1205385, by rfl⟩ : syracuseStep 3214361 = 2410771) B2410771
theorem B2142907 : Blo 2141435 2142907 := bstep (se 1 (by rfl) ⟨1607180, by rfl⟩ : syracuseStep 2142907 = 3214361) B3214361
theorem B15446389 : Blo 2141435 15446389 := bbase (se 5 (by rfl) ⟨724049, by rfl⟩ : syracuseStep 15446389 = 1448099) (by norm_num)
theorem B20595185 : Blo 2141435 20595185 := bstep (se 2 (by rfl) ⟨7723194, by rfl⟩ : syracuseStep 20595185 = 15446389) B15446389
theorem B13730123 : Blo 2141435 13730123 := bstep (se 1 (by rfl) ⟨10297592, by rfl⟩ : syracuseStep 13730123 = 20595185) B20595185
theorem B9153415 : Blo 2141435 9153415 := bstep (se 1 (by rfl) ⟨6865061, by rfl⟩ : syracuseStep 9153415 = 13730123) B13730123
theorem B12204553 : Blo 2141435 12204553 := bstep (se 2 (by rfl) ⟨4576707, by rfl⟩ : syracuseStep 12204553 = 9153415) B9153415
theorem B16272737 : Blo 2141435 16272737 := bstep (se 2 (by rfl) ⟨6102276, by rfl⟩ : syracuseStep 16272737 = 12204553) B12204553
theorem B10848491 : Blo 2141435 10848491 := bstep (se 1 (by rfl) ⟨8136368, by rfl⟩ : syracuseStep 10848491 = 16272737) B16272737
theorem B7232327 : Blo 2141435 7232327 := bstep (se 1 (by rfl) ⟨5424245, by rfl⟩ : syracuseStep 7232327 = 10848491) B10848491
theorem B4821551 : Blo 2141435 4821551 := bstep (se 1 (by rfl) ⟨3616163, by rfl⟩ : syracuseStep 4821551 = 7232327) B7232327
theorem B3214367 : Blo 2141435 3214367 := bstep (se 1 (by rfl) ⟨2410775, by rfl⟩ : syracuseStep 3214367 = 4821551) B4821551
theorem B2142911 : Blo 2141435 2142911 := bstep (se 1 (by rfl) ⟨1607183, by rfl⟩ : syracuseStep 2142911 = 3214367) B3214367
theorem B3214373 : Blo 2141435 3214373 := bbase (se 4 (by rfl) ⟨301347, by rfl⟩ : syracuseStep 3214373 = 602695) (by norm_num)
theorem B2142915 : Blo 2141435 2142915 := bstep (se 1 (by rfl) ⟨1607186, by rfl⟩ : syracuseStep 2142915 = 3214373) B3214373
theorem B2712133 : Blo 2141435 2712133 := bbase (se 4 (by rfl) ⟨254262, by rfl⟩ : syracuseStep 2712133 = 508525) (by norm_num)
theorem B3616177 : Blo 2141435 3616177 := bstep (se 2 (by rfl) ⟨1356066, by rfl⟩ : syracuseStep 3616177 = 2712133) B2712133
theorem B4821569 : Blo 2141435 4821569 := bstep (se 2 (by rfl) ⟨1808088, by rfl⟩ : syracuseStep 4821569 = 3616177) B3616177
theorem B3214379 : Blo 2141435 3214379 := bstep (se 1 (by rfl) ⟨2410784, by rfl⟩ : syracuseStep 3214379 = 4821569) B4821569
theorem B2142919 : Blo 2141435 2142919 := bstep (se 1 (by rfl) ⟨1607189, by rfl⟩ : syracuseStep 2142919 = 3214379) B3214379
theorem B2410789 : Blo 2141435 2410789 := bbase (se 4 (by rfl) ⟨226011, by rfl⟩ : syracuseStep 2410789 = 452023) (by norm_num)
theorem B3214385 : Blo 2141435 3214385 := bstep (se 2 (by rfl) ⟨1205394, by rfl⟩ : syracuseStep 3214385 = 2410789) B2410789
theorem B2142923 : Blo 2141435 2142923 := bstep (se 1 (by rfl) ⟨1607192, by rfl⟩ : syracuseStep 2142923 = 3214385) B3214385
theorem B3432557 : Blo 2141435 3432557 := bbase (se 3 (by rfl) ⟨643604, by rfl⟩ : syracuseStep 3432557 = 1287209) (by norm_num)
theorem B9153485 : Blo 2141435 9153485 := bstep (se 3 (by rfl) ⟨1716278, by rfl⟩ : syracuseStep 9153485 = 3432557) B3432557
theorem B6102323 : Blo 2141435 6102323 := bstep (se 1 (by rfl) ⟨4576742, by rfl⟩ : syracuseStep 6102323 = 9153485) B9153485
theorem B4068215 : Blo 2141435 4068215 := bstep (se 1 (by rfl) ⟨3051161, by rfl⟩ : syracuseStep 4068215 = 6102323) B6102323
theorem B2712143 : Blo 2141435 2712143 := bstep (se 1 (by rfl) ⟨2034107, by rfl⟩ : syracuseStep 2712143 = 4068215) B4068215
theorem B7232381 : Blo 2141435 7232381 := bstep (se 3 (by rfl) ⟨1356071, by rfl⟩ : syracuseStep 7232381 = 2712143) B2712143
theorem B4821587 : Blo 2141435 4821587 := bstep (se 1 (by rfl) ⟨3616190, by rfl⟩ : syracuseStep 4821587 = 7232381) B7232381
theorem B3214391 : Blo 2141435 3214391 := bstep (se 1 (by rfl) ⟨2410793, by rfl⟩ : syracuseStep 3214391 = 4821587) B4821587
theorem B2142927 : Blo 2141435 2142927 := bstep (se 1 (by rfl) ⟨1607195, by rfl⟩ : syracuseStep 2142927 = 3214391) B3214391
theorem B3214397 : Blo 2141435 3214397 := bbase (se 3 (by rfl) ⟨602699, by rfl⟩ : syracuseStep 3214397 = 1205399) (by norm_num)
theorem B2142931 : Blo 2141435 2142931 := bstep (se 1 (by rfl) ⟨1607198, by rfl⟩ : syracuseStep 2142931 = 3214397) B3214397
theorem B4821605 : Blo 2141435 4821605 := bbase (se 4 (by rfl) ⟨452025, by rfl⟩ : syracuseStep 4821605 = 904051) (by norm_num)
theorem B3214403 : Blo 2141435 3214403 := bstep (se 1 (by rfl) ⟨2410802, by rfl⟩ : syracuseStep 3214403 = 4821605) B4821605
theorem B2142935 : Blo 2141435 2142935 := bstep (se 1 (by rfl) ⟨1607201, by rfl⟩ : syracuseStep 2142935 = 3214403) B3214403
theorem B5424317 : Blo 2141435 5424317 := bbase (se 3 (by rfl) ⟨1017059, by rfl⟩ : syracuseStep 5424317 = 2034119) (by norm_num)
theorem B3616211 : Blo 2141435 3616211 := bstep (se 1 (by rfl) ⟨2712158, by rfl⟩ : syracuseStep 3616211 = 5424317) B5424317
theorem B2410807 : Blo 2141435 2410807 := bstep (se 1 (by rfl) ⟨1808105, by rfl⟩ : syracuseStep 2410807 = 3616211) B3616211
theorem B3214409 : Blo 2141435 3214409 := bstep (se 2 (by rfl) ⟨1205403, by rfl⟩ : syracuseStep 3214409 = 2410807) B2410807
theorem B2142939 : Blo 2141435 2142939 := bstep (se 1 (by rfl) ⟨1607204, by rfl⟩ : syracuseStep 2142939 = 3214409) B3214409
theorem B4068245 : Blo 2141435 4068245 := bbase (se 6 (by rfl) ⟨95349, by rfl⟩ : syracuseStep 4068245 = 190699) (by norm_num)
theorem B10848653 : Blo 2141435 10848653 := bstep (se 3 (by rfl) ⟨2034122, by rfl⟩ : syracuseStep 10848653 = 4068245) B4068245
theorem B7232435 : Blo 2141435 7232435 := bstep (se 1 (by rfl) ⟨5424326, by rfl⟩ : syracuseStep 7232435 = 10848653) B10848653
theorem B4821623 : Blo 2141435 4821623 := bstep (se 1 (by rfl) ⟨3616217, by rfl⟩ : syracuseStep 4821623 = 7232435) B7232435
theorem B3214415 : Blo 2141435 3214415 := bstep (se 1 (by rfl) ⟨2410811, by rfl⟩ : syracuseStep 3214415 = 4821623) B4821623
theorem B2142943 : Blo 2141435 2142943 := bstep (se 1 (by rfl) ⟨1607207, by rfl⟩ : syracuseStep 2142943 = 3214415) B3214415
theorem B3214421 : Blo 2141435 3214421 := bbase (se 8 (by rfl) ⟨18834, by rfl⟩ : syracuseStep 3214421 = 37669) (by norm_num)
theorem B2142947 : Blo 2141435 2142947 := bstep (se 1 (by rfl) ⟨1607210, by rfl⟩ : syracuseStep 2142947 = 3214421) B3214421
theorem B5148893 : Blo 2141435 5148893 := bbase (se 3 (by rfl) ⟨965417, by rfl⟩ : syracuseStep 5148893 = 1930835) (by norm_num)
theorem B13730381 : Blo 2141435 13730381 := bstep (se 3 (by rfl) ⟨2574446, by rfl⟩ : syracuseStep 13730381 = 5148893) B5148893
theorem B9153587 : Blo 2141435 9153587 := bstep (se 1 (by rfl) ⟨6865190, by rfl⟩ : syracuseStep 9153587 = 13730381) B13730381
theorem B6102391 : Blo 2141435 6102391 := bstep (se 1 (by rfl) ⟨4576793, by rfl⟩ : syracuseStep 6102391 = 9153587) B9153587
theorem B8136521 : Blo 2141435 8136521 := bstep (se 2 (by rfl) ⟨3051195, by rfl⟩ : syracuseStep 8136521 = 6102391) B6102391
theorem B5424347 : Blo 2141435 5424347 := bstep (se 1 (by rfl) ⟨4068260, by rfl⟩ : syracuseStep 5424347 = 8136521) B8136521
theorem B3616231 : Blo 2141435 3616231 := bstep (se 1 (by rfl) ⟨2712173, by rfl⟩ : syracuseStep 3616231 = 5424347) B5424347
theorem B4821641 : Blo 2141435 4821641 := bstep (se 2 (by rfl) ⟨1808115, by rfl⟩ : syracuseStep 4821641 = 3616231) B3616231
theorem B3214427 : Blo 2141435 3214427 := bstep (se 1 (by rfl) ⟨2410820, by rfl⟩ : syracuseStep 3214427 = 4821641) B4821641
theorem B2142951 : Blo 2141435 2142951 := bstep (se 1 (by rfl) ⟨1607213, by rfl⟩ : syracuseStep 2142951 = 3214427) B3214427
theorem B2410825 : Blo 2141435 2410825 := bbase (se 2 (by rfl) ⟨904059, by rfl⟩ : syracuseStep 2410825 = 1808119) (by norm_num)
theorem B3214433 : Blo 2141435 3214433 := bstep (se 2 (by rfl) ⟨1205412, by rfl⟩ : syracuseStep 3214433 = 2410825) B2410825
theorem B2142955 : Blo 2141435 2142955 := bstep (se 1 (by rfl) ⟨1607216, by rfl⟩ : syracuseStep 2142955 = 3214433) B3214433
theorem B296912213 : Blo 2141435 296912213 := bbase (se 12 (by rfl) ⟨108732, by rfl⟩ : syracuseStep 296912213 = 217465) (by norm_num)
theorem B197941475 : Blo 2141435 197941475 := bstep (se 1 (by rfl) ⟨148456106, by rfl⟩ : syracuseStep 197941475 = 296912213) B296912213
theorem B131960983 : Blo 2141435 131960983 := bstep (se 1 (by rfl) ⟨98970737, by rfl⟩ : syracuseStep 131960983 = 197941475) B197941475
theorem B175947977 : Blo 2141435 175947977 := bstep (se 2 (by rfl) ⟨65980491, by rfl⟩ : syracuseStep 175947977 = 131960983) B131960983
theorem B117298651 : Blo 2141435 117298651 := bstep (se 1 (by rfl) ⟨87973988, by rfl⟩ : syracuseStep 117298651 = 175947977) B175947977
theorem B156398201 : Blo 2141435 156398201 := bstep (se 2 (by rfl) ⟨58649325, by rfl⟩ : syracuseStep 156398201 = 117298651) B117298651
theorem B104265467 : Blo 2141435 104265467 := bstep (se 1 (by rfl) ⟨78199100, by rfl⟩ : syracuseStep 104265467 = 156398201) B156398201
theorem B69510311 : Blo 2141435 69510311 := bstep (se 1 (by rfl) ⟨52132733, by rfl⟩ : syracuseStep 69510311 = 104265467) B104265467
theorem B46340207 : Blo 2141435 46340207 := bstep (se 1 (by rfl) ⟨34755155, by rfl⟩ : syracuseStep 46340207 = 69510311) B69510311
theorem B30893471 : Blo 2141435 30893471 := bstep (se 1 (by rfl) ⟨23170103, by rfl⟩ : syracuseStep 30893471 = 46340207) B46340207
theorem B20595647 : Blo 2141435 20595647 := bstep (se 1 (by rfl) ⟨15446735, by rfl⟩ : syracuseStep 20595647 = 30893471) B30893471
theorem B13730431 : Blo 2141435 13730431 := bstep (se 1 (by rfl) ⟨10297823, by rfl⟩ : syracuseStep 13730431 = 20595647) B20595647
theorem B18307241 : Blo 2141435 18307241 := bstep (se 2 (by rfl) ⟨6865215, by rfl⟩ : syracuseStep 18307241 = 13730431) B13730431
theorem B12204827 : Blo 2141435 12204827 := bstep (se 1 (by rfl) ⟨9153620, by rfl⟩ : syracuseStep 12204827 = 18307241) B18307241
theorem B8136551 : Blo 2141435 8136551 := bstep (se 1 (by rfl) ⟨6102413, by rfl⟩ : syracuseStep 8136551 = 12204827) B12204827
theorem B5424367 : Blo 2141435 5424367 := bstep (se 1 (by rfl) ⟨4068275, by rfl⟩ : syracuseStep 5424367 = 8136551) B8136551
theorem B7232489 : Blo 2141435 7232489 := bstep (se 2 (by rfl) ⟨2712183, by rfl⟩ : syracuseStep 7232489 = 5424367) B5424367
theorem B4821659 : Blo 2141435 4821659 := bstep (se 1 (by rfl) ⟨3616244, by rfl⟩ : syracuseStep 4821659 = 7232489) B7232489
theorem B3214439 : Blo 2141435 3214439 := bstep (se 1 (by rfl) ⟨2410829, by rfl⟩ : syracuseStep 3214439 = 4821659) B4821659
theorem B2142959 : Blo 2141435 2142959 := bstep (se 1 (by rfl) ⟨1607219, by rfl⟩ : syracuseStep 2142959 = 3214439) B3214439
theorem B3214445 : Blo 2141435 3214445 := bbase (se 3 (by rfl) ⟨602708, by rfl⟩ : syracuseStep 3214445 = 1205417) (by norm_num)
theorem B2142963 : Blo 2141435 2142963 := bstep (se 1 (by rfl) ⟨1607222, by rfl⟩ : syracuseStep 2142963 = 3214445) B3214445
theorem B4821677 : Blo 2141435 4821677 := bbase (se 3 (by rfl) ⟨904064, by rfl⟩ : syracuseStep 4821677 = 1808129) (by norm_num)
theorem B3214451 : Blo 2141435 3214451 := bstep (se 1 (by rfl) ⟨2410838, by rfl⟩ : syracuseStep 3214451 = 4821677) B4821677
theorem B2142967 : Blo 2141435 2142967 := bstep (se 1 (by rfl) ⟨1607225, by rfl⟩ : syracuseStep 2142967 = 3214451) B3214451
theorem B4576837 : Blo 2141435 4576837 := bbase (se 4 (by rfl) ⟨429078, by rfl⟩ : syracuseStep 4576837 = 858157) (by norm_num)
theorem B6102449 : Blo 2141435 6102449 := bstep (se 2 (by rfl) ⟨2288418, by rfl⟩ : syracuseStep 6102449 = 4576837) B4576837
theorem B4068299 : Blo 2141435 4068299 := bstep (se 1 (by rfl) ⟨3051224, by rfl⟩ : syracuseStep 4068299 = 6102449) B6102449
theorem B2712199 : Blo 2141435 2712199 := bstep (se 1 (by rfl) ⟨2034149, by rfl⟩ : syracuseStep 2712199 = 4068299) B4068299
theorem B3616265 : Blo 2141435 3616265 := bstep (se 2 (by rfl) ⟨1356099, by rfl⟩ : syracuseStep 3616265 = 2712199) B2712199
theorem B2410843 : Blo 2141435 2410843 := bstep (se 1 (by rfl) ⟨1808132, by rfl⟩ : syracuseStep 2410843 = 3616265) B3616265
theorem B3214457 : Blo 2141435 3214457 := bstep (se 2 (by rfl) ⟨1205421, by rfl⟩ : syracuseStep 3214457 = 2410843) B2410843
theorem B2142971 : Blo 2141435 2142971 := bstep (se 1 (by rfl) ⟨1607228, by rfl⟩ : syracuseStep 2142971 = 3214457) B3214457
theorem B8688853 : Blo 2141435 8688853 := bbase (se 7 (by rfl) ⟨101822, by rfl⟩ : syracuseStep 8688853 = 203645) (by norm_num)
theorem B46340549 : Blo 2141435 46340549 := bstep (se 4 (by rfl) ⟨4344426, by rfl⟩ : syracuseStep 46340549 = 8688853) B8688853
theorem B30893699 : Blo 2141435 30893699 := bstep (se 1 (by rfl) ⟨23170274, by rfl⟩ : syracuseStep 30893699 = 46340549) B46340549
theorem B20595799 : Blo 2141435 20595799 := bstep (se 1 (by rfl) ⟨15446849, by rfl⟩ : syracuseStep 20595799 = 30893699) B30893699
theorem B27461065 : Blo 2141435 27461065 := bstep (se 2 (by rfl) ⟨10297899, by rfl⟩ : syracuseStep 27461065 = 20595799) B20595799
theorem B36614753 : Blo 2141435 36614753 := bstep (se 2 (by rfl) ⟨13730532, by rfl⟩ : syracuseStep 36614753 = 27461065) B27461065
theorem B24409835 : Blo 2141435 24409835 := bstep (se 1 (by rfl) ⟨18307376, by rfl⟩ : syracuseStep 24409835 = 36614753) B36614753
theorem B16273223 : Blo 2141435 16273223 := bstep (se 1 (by rfl) ⟨12204917, by rfl⟩ : syracuseStep 16273223 = 24409835) B24409835
theorem B10848815 : Blo 2141435 10848815 := bstep (se 1 (by rfl) ⟨8136611, by rfl⟩ : syracuseStep 10848815 = 16273223) B16273223
theorem B7232543 : Blo 2141435 7232543 := bstep (se 1 (by rfl) ⟨5424407, by rfl⟩ : syracuseStep 7232543 = 10848815) B10848815
theorem B4821695 : Blo 2141435 4821695 := bstep (se 1 (by rfl) ⟨3616271, by rfl⟩ : syracuseStep 4821695 = 7232543) B7232543
theorem B3214463 : Blo 2141435 3214463 := bstep (se 1 (by rfl) ⟨2410847, by rfl⟩ : syracuseStep 3214463 = 4821695) B4821695
theorem B2142975 : Blo 2141435 2142975 := bstep (se 1 (by rfl) ⟨1607231, by rfl⟩ : syracuseStep 2142975 = 3214463) B3214463
theorem B3214469 : Blo 2141435 3214469 := bbase (se 4 (by rfl) ⟨301356, by rfl⟩ : syracuseStep 3214469 = 602713) (by norm_num)
theorem B2142979 : Blo 2141435 2142979 := bstep (se 1 (by rfl) ⟨1607234, by rfl⟩ : syracuseStep 2142979 = 3214469) B3214469
theorem B3616285 : Blo 2141435 3616285 := bbase (se 3 (by rfl) ⟨678053, by rfl⟩ : syracuseStep 3616285 = 1356107) (by norm_num)
theorem B4821713 : Blo 2141435 4821713 := bstep (se 2 (by rfl) ⟨1808142, by rfl⟩ : syracuseStep 4821713 = 3616285) B3616285
theorem B3214475 : Blo 2141435 3214475 := bstep (se 1 (by rfl) ⟨2410856, by rfl⟩ : syracuseStep 3214475 = 4821713) B4821713
theorem B2142983 : Blo 2141435 2142983 := bstep (se 1 (by rfl) ⟨1607237, by rfl⟩ : syracuseStep 2142983 = 3214475) B3214475
theorem B2410861 : Blo 2141435 2410861 := bbase (se 3 (by rfl) ⟨452036, by rfl⟩ : syracuseStep 2410861 = 904073) (by norm_num)
theorem B3214481 : Blo 2141435 3214481 := bstep (se 2 (by rfl) ⟨1205430, by rfl⟩ : syracuseStep 3214481 = 2410861) B2410861
theorem B2142987 : Blo 2141435 2142987 := bstep (se 1 (by rfl) ⟨1607240, by rfl⟩ : syracuseStep 2142987 = 3214481) B3214481
theorem B7232597 : Blo 2141435 7232597 := bbase (se 8 (by rfl) ⟨42378, by rfl⟩ : syracuseStep 7232597 = 84757) (by norm_num)
theorem B4821731 : Blo 2141435 4821731 := bstep (se 1 (by rfl) ⟨3616298, by rfl⟩ : syracuseStep 4821731 = 7232597) B7232597
theorem B3214487 : Blo 2141435 3214487 := bstep (se 1 (by rfl) ⟨2410865, by rfl⟩ : syracuseStep 3214487 = 4821731) B4821731
theorem B2142991 : Blo 2141435 2142991 := bstep (se 1 (by rfl) ⟨1607243, by rfl⟩ : syracuseStep 2142991 = 3214487) B3214487
theorem B3214493 : Blo 2141435 3214493 := bbase (se 3 (by rfl) ⟨602717, by rfl⟩ : syracuseStep 3214493 = 1205435) (by norm_num)
theorem B2142995 : Blo 2141435 2142995 := bstep (se 1 (by rfl) ⟨1607246, by rfl⟩ : syracuseStep 2142995 = 3214493) B3214493
theorem B4821749 : Blo 2141435 4821749 := bbase (se 5 (by rfl) ⟨226019, by rfl⟩ : syracuseStep 4821749 = 452039) (by norm_num)
theorem B3214499 : Blo 2141435 3214499 := bstep (se 1 (by rfl) ⟨2410874, by rfl⟩ : syracuseStep 3214499 = 4821749) B4821749
theorem B2142999 : Blo 2141435 2142999 := bstep (se 1 (by rfl) ⟨1607249, by rfl⟩ : syracuseStep 2142999 = 3214499) B3214499
theorem B2574509 : Blo 2141435 2574509 := bbase (se 3 (by rfl) ⟨482720, by rfl⟩ : syracuseStep 2574509 = 965441) (by norm_num)
theorem B27461429 : Blo 2141435 27461429 := bstep (se 5 (by rfl) ⟨1287254, by rfl⟩ : syracuseStep 27461429 = 2574509) B2574509
theorem B18307619 : Blo 2141435 18307619 := bstep (se 1 (by rfl) ⟨13730714, by rfl⟩ : syracuseStep 18307619 = 27461429) B27461429
theorem B12205079 : Blo 2141435 12205079 := bstep (se 1 (by rfl) ⟨9153809, by rfl⟩ : syracuseStep 12205079 = 18307619) B18307619
theorem B8136719 : Blo 2141435 8136719 := bstep (se 1 (by rfl) ⟨6102539, by rfl⟩ : syracuseStep 8136719 = 12205079) B12205079
theorem B5424479 : Blo 2141435 5424479 := bstep (se 1 (by rfl) ⟨4068359, by rfl⟩ : syracuseStep 5424479 = 8136719) B8136719
theorem B3616319 : Blo 2141435 3616319 := bstep (se 1 (by rfl) ⟨2712239, by rfl⟩ : syracuseStep 3616319 = 5424479) B5424479
theorem B2410879 : Blo 2141435 2410879 := bstep (se 1 (by rfl) ⟨1808159, by rfl⟩ : syracuseStep 2410879 = 3616319) B3616319
theorem B3214505 : Blo 2141435 3214505 := bstep (se 2 (by rfl) ⟨1205439, by rfl⟩ : syracuseStep 3214505 = 2410879) B2410879
theorem B2143003 : Blo 2141435 2143003 := bstep (se 1 (by rfl) ⟨1607252, by rfl⟩ : syracuseStep 2143003 = 3214505) B3214505
theorem B3432685 : Blo 2141435 3432685 := bbase (se 3 (by rfl) ⟨643628, by rfl⟩ : syracuseStep 3432685 = 1287257) (by norm_num)
theorem B4576913 : Blo 2141435 4576913 := bstep (se 2 (by rfl) ⟨1716342, by rfl⟩ : syracuseStep 4576913 = 3432685) B3432685
theorem B3051275 : Blo 2141435 3051275 := bstep (se 1 (by rfl) ⟨2288456, by rfl⟩ : syracuseStep 3051275 = 4576913) B4576913
theorem B8136733 : Blo 2141435 8136733 := bstep (se 3 (by rfl) ⟨1525637, by rfl⟩ : syracuseStep 8136733 = 3051275) B3051275
theorem B10848977 : Blo 2141435 10848977 := bstep (se 2 (by rfl) ⟨4068366, by rfl⟩ : syracuseStep 10848977 = 8136733) B8136733
theorem B7232651 : Blo 2141435 7232651 := bstep (se 1 (by rfl) ⟨5424488, by rfl⟩ : syracuseStep 7232651 = 10848977) B10848977
theorem B4821767 : Blo 2141435 4821767 := bstep (se 1 (by rfl) ⟨3616325, by rfl⟩ : syracuseStep 4821767 = 7232651) B7232651
theorem B3214511 : Blo 2141435 3214511 := bstep (se 1 (by rfl) ⟨2410883, by rfl⟩ : syracuseStep 3214511 = 4821767) B4821767
theorem B2143007 : Blo 2141435 2143007 := bstep (se 1 (by rfl) ⟨1607255, by rfl⟩ : syracuseStep 2143007 = 3214511) B3214511
theorem B3214517 : Blo 2141435 3214517 := bbase (se 5 (by rfl) ⟨150680, by rfl⟩ : syracuseStep 3214517 = 301361) (by norm_num)
theorem B2143011 : Blo 2141435 2143011 := bstep (se 1 (by rfl) ⟨1607258, by rfl⟩ : syracuseStep 2143011 = 3214517) B3214517
theorem B5424509 : Blo 2141435 5424509 := bbase (se 3 (by rfl) ⟨1017095, by rfl⟩ : syracuseStep 5424509 = 2034191) (by norm_num)
theorem B3616339 : Blo 2141435 3616339 := bstep (se 1 (by rfl) ⟨2712254, by rfl⟩ : syracuseStep 3616339 = 5424509) B5424509
theorem B4821785 : Blo 2141435 4821785 := bstep (se 2 (by rfl) ⟨1808169, by rfl⟩ : syracuseStep 4821785 = 3616339) B3616339
theorem B3214523 : Blo 2141435 3214523 := bstep (se 1 (by rfl) ⟨2410892, by rfl⟩ : syracuseStep 3214523 = 4821785) B4821785
theorem B2143015 : Blo 2141435 2143015 := bstep (se 1 (by rfl) ⟨1607261, by rfl⟩ : syracuseStep 2143015 = 3214523) B3214523
theorem B2410897 : Blo 2141435 2410897 := bbase (se 2 (by rfl) ⟨904086, by rfl⟩ : syracuseStep 2410897 = 1808173) (by norm_num)
theorem B3214529 : Blo 2141435 3214529 := bstep (se 2 (by rfl) ⟨1205448, by rfl⟩ : syracuseStep 3214529 = 2410897) B2410897
theorem B2143019 : Blo 2141435 2143019 := bstep (se 1 (by rfl) ⟨1607264, by rfl⟩ : syracuseStep 2143019 = 3214529) B3214529
theorem B4068397 : Blo 2141435 4068397 := bbase (se 3 (by rfl) ⟨762824, by rfl⟩ : syracuseStep 4068397 = 1525649) (by norm_num)
theorem B5424529 : Blo 2141435 5424529 := bstep (se 2 (by rfl) ⟨2034198, by rfl⟩ : syracuseStep 5424529 = 4068397) B4068397
theorem B7232705 : Blo 2141435 7232705 := bstep (se 2 (by rfl) ⟨2712264, by rfl⟩ : syracuseStep 7232705 = 5424529) B5424529
theorem B4821803 : Blo 2141435 4821803 := bstep (se 1 (by rfl) ⟨3616352, by rfl⟩ : syracuseStep 4821803 = 7232705) B7232705
theorem B3214535 : Blo 2141435 3214535 := bstep (se 1 (by rfl) ⟨2410901, by rfl⟩ : syracuseStep 3214535 = 4821803) B4821803
theorem B2143023 : Blo 2141435 2143023 := bstep (se 1 (by rfl) ⟨1607267, by rfl⟩ : syracuseStep 2143023 = 3214535) B3214535
theorem B3214541 : Blo 2141435 3214541 := bbase (se 3 (by rfl) ⟨602726, by rfl⟩ : syracuseStep 3214541 = 1205453) (by norm_num)
theorem B2143027 : Blo 2141435 2143027 := bstep (se 1 (by rfl) ⟨1607270, by rfl⟩ : syracuseStep 2143027 = 3214541) B3214541
theorem B4821821 : Blo 2141435 4821821 := bbase (se 3 (by rfl) ⟨904091, by rfl⟩ : syracuseStep 4821821 = 1808183) (by norm_num)
theorem B3214547 : Blo 2141435 3214547 := bstep (se 1 (by rfl) ⟨2410910, by rfl⟩ : syracuseStep 3214547 = 4821821) B4821821
theorem B2143031 : Blo 2141435 2143031 := bstep (se 1 (by rfl) ⟨1607273, by rfl⟩ : syracuseStep 2143031 = 3214547) B3214547
theorem B3616373 : Blo 2141435 3616373 := bbase (se 5 (by rfl) ⟨169517, by rfl⟩ : syracuseStep 3616373 = 339035) (by norm_num)
theorem B2410915 : Blo 2141435 2410915 := bstep (se 1 (by rfl) ⟨1808186, by rfl⟩ : syracuseStep 2410915 = 3616373) B3616373
theorem B3214553 : Blo 2141435 3214553 := bstep (se 2 (by rfl) ⟨1205457, by rfl⟩ : syracuseStep 3214553 = 2410915) B2410915
theorem B2143035 : Blo 2141435 2143035 := bstep (se 1 (by rfl) ⟨1607276, by rfl⟩ : syracuseStep 2143035 = 3214553) B3214553
theorem B4576981 : Blo 2141435 4576981 := bbase (se 7 (by rfl) ⟨53636, by rfl⟩ : syracuseStep 4576981 = 107273) (by norm_num)
theorem B6102641 : Blo 2141435 6102641 := bstep (se 2 (by rfl) ⟨2288490, by rfl⟩ : syracuseStep 6102641 = 4576981) B4576981
theorem B16273709 : Blo 2141435 16273709 := bstep (se 3 (by rfl) ⟨3051320, by rfl⟩ : syracuseStep 16273709 = 6102641) B6102641
theorem B10849139 : Blo 2141435 10849139 := bstep (se 1 (by rfl) ⟨8136854, by rfl⟩ : syracuseStep 10849139 = 16273709) B16273709
theorem B7232759 : Blo 2141435 7232759 := bstep (se 1 (by rfl) ⟨5424569, by rfl⟩ : syracuseStep 7232759 = 10849139) B10849139
theorem B4821839 : Blo 2141435 4821839 := bstep (se 1 (by rfl) ⟨3616379, by rfl⟩ : syracuseStep 4821839 = 7232759) B7232759
theorem B3214559 : Blo 2141435 3214559 := bstep (se 1 (by rfl) ⟨2410919, by rfl⟩ : syracuseStep 3214559 = 4821839) B4821839
theorem B2143039 : Blo 2141435 2143039 := bstep (se 1 (by rfl) ⟨1607279, by rfl⟩ : syracuseStep 2143039 = 3214559) B3214559
theorem B3214565 : Blo 2141435 3214565 := bbase (se 4 (by rfl) ⟨301365, by rfl⟩ : syracuseStep 3214565 = 602731) (by norm_num)
theorem B2143043 : Blo 2141435 2143043 := bstep (se 1 (by rfl) ⟨1607282, by rfl⟩ : syracuseStep 2143043 = 3214565) B3214565
theorem B2383453 : Blo 2141435 2383453 := bbase (se 3 (by rfl) ⟨446897, by rfl⟩ : syracuseStep 2383453 = 893795) (by norm_num)
theorem B3177937 : Blo 2141435 3177937 := bstep (se 2 (by rfl) ⟨1191726, by rfl⟩ : syracuseStep 3177937 = 2383453) B2383453
theorem B16948997 : Blo 2141435 16948997 := bstep (se 4 (by rfl) ⟨1588968, by rfl⟩ : syracuseStep 16948997 = 3177937) B3177937
theorem B11299331 : Blo 2141435 11299331 := bstep (se 1 (by rfl) ⟨8474498, by rfl⟩ : syracuseStep 11299331 = 16948997) B16948997
theorem B7532887 : Blo 2141435 7532887 := bstep (se 1 (by rfl) ⟨5649665, by rfl⟩ : syracuseStep 7532887 = 11299331) B11299331
theorem B10043849 : Blo 2141435 10043849 := bstep (se 2 (by rfl) ⟨3766443, by rfl⟩ : syracuseStep 10043849 = 7532887) B7532887
theorem B26783597 : Blo 2141435 26783597 := bstep (se 3 (by rfl) ⟨5021924, by rfl⟩ : syracuseStep 26783597 = 10043849) B10043849
theorem B17855731 : Blo 2141435 17855731 := bstep (se 1 (by rfl) ⟨13391798, by rfl⟩ : syracuseStep 17855731 = 26783597) B26783597
theorem B23807641 : Blo 2141435 23807641 := bstep (se 2 (by rfl) ⟨8927865, by rfl⟩ : syracuseStep 23807641 = 17855731) B17855731
theorem B31743521 : Blo 2141435 31743521 := bstep (se 2 (by rfl) ⟨11903820, by rfl⟩ : syracuseStep 31743521 = 23807641) B23807641
theorem B21162347 : Blo 2141435 21162347 := bstep (se 1 (by rfl) ⟨15871760, by rfl⟩ : syracuseStep 21162347 = 31743521) B31743521
theorem B14108231 : Blo 2141435 14108231 := bstep (se 1 (by rfl) ⟨10581173, by rfl⟩ : syracuseStep 14108231 = 21162347) B21162347
theorem B9405487 : Blo 2141435 9405487 := bstep (se 1 (by rfl) ⟨7054115, by rfl⟩ : syracuseStep 9405487 = 14108231) B14108231
theorem B50162597 : Blo 2141435 50162597 := bstep (se 4 (by rfl) ⟨4702743, by rfl⟩ : syracuseStep 50162597 = 9405487) B9405487
theorem B33441731 : Blo 2141435 33441731 := bstep (se 1 (by rfl) ⟨25081298, by rfl⟩ : syracuseStep 33441731 = 50162597) B50162597
theorem B22294487 : Blo 2141435 22294487 := bstep (se 1 (by rfl) ⟨16720865, by rfl⟩ : syracuseStep 22294487 = 33441731) B33441731
theorem B59451965 : Blo 2141435 59451965 := bstep (se 3 (by rfl) ⟨11147243, by rfl⟩ : syracuseStep 59451965 = 22294487) B22294487
theorem B39634643 : Blo 2141435 39634643 := bstep (se 1 (by rfl) ⟨29725982, by rfl⟩ : syracuseStep 39634643 = 59451965) B59451965
theorem B26423095 : Blo 2141435 26423095 := bstep (se 1 (by rfl) ⟨19817321, by rfl⟩ : syracuseStep 26423095 = 39634643) B39634643
theorem B35230793 : Blo 2141435 35230793 := bstep (se 2 (by rfl) ⟨13211547, by rfl⟩ : syracuseStep 35230793 = 26423095) B26423095
theorem B93948781 : Blo 2141435 93948781 := bstep (se 3 (by rfl) ⟨17615396, by rfl⟩ : syracuseStep 93948781 = 35230793) B35230793
theorem B125265041 : Blo 2141435 125265041 := bstep (se 2 (by rfl) ⟨46974390, by rfl⟩ : syracuseStep 125265041 = 93948781) B93948781
theorem B83510027 : Blo 2141435 83510027 := bstep (se 1 (by rfl) ⟨62632520, by rfl⟩ : syracuseStep 83510027 = 125265041) B125265041
theorem B55673351 : Blo 2141435 55673351 := bstep (se 1 (by rfl) ⟨41755013, by rfl⟩ : syracuseStep 55673351 = 83510027) B83510027
theorem B37115567 : Blo 2141435 37115567 := bstep (se 1 (by rfl) ⟨27836675, by rfl⟩ : syracuseStep 37115567 = 55673351) B55673351
theorem B24743711 : Blo 2141435 24743711 := bstep (se 1 (by rfl) ⟨18557783, by rfl⟩ : syracuseStep 24743711 = 37115567) B37115567
theorem B16495807 : Blo 2141435 16495807 := bstep (se 1 (by rfl) ⟨12371855, by rfl⟩ : syracuseStep 16495807 = 24743711) B24743711
theorem B21994409 : Blo 2141435 21994409 := bstep (se 2 (by rfl) ⟨8247903, by rfl⟩ : syracuseStep 21994409 = 16495807) B16495807
theorem B14662939 : Blo 2141435 14662939 := bstep (se 1 (by rfl) ⟨10997204, by rfl⟩ : syracuseStep 14662939 = 21994409) B21994409
theorem B19550585 : Blo 2141435 19550585 := bstep (se 2 (by rfl) ⟨7331469, by rfl⟩ : syracuseStep 19550585 = 14662939) B14662939
theorem B13033723 : Blo 2141435 13033723 := bstep (se 1 (by rfl) ⟨9775292, by rfl⟩ : syracuseStep 13033723 = 19550585) B19550585
theorem B17378297 : Blo 2141435 17378297 := bstep (se 2 (by rfl) ⟨6516861, by rfl⟩ : syracuseStep 17378297 = 13033723) B13033723
theorem B11585531 : Blo 2141435 11585531 := bstep (se 1 (by rfl) ⟨8689148, by rfl⟩ : syracuseStep 11585531 = 17378297) B17378297
theorem B7723687 : Blo 2141435 7723687 := bstep (se 1 (by rfl) ⟨5792765, by rfl⟩ : syracuseStep 7723687 = 11585531) B11585531
theorem B10298249 : Blo 2141435 10298249 := bstep (se 2 (by rfl) ⟨3861843, by rfl⟩ : syracuseStep 10298249 = 7723687) B7723687
theorem B6865499 : Blo 2141435 6865499 := bstep (se 1 (by rfl) ⟨5149124, by rfl⟩ : syracuseStep 6865499 = 10298249) B10298249
theorem B4576999 : Blo 2141435 4576999 := bstep (se 1 (by rfl) ⟨3432749, by rfl⟩ : syracuseStep 4576999 = 6865499) B6865499
theorem B6102665 : Blo 2141435 6102665 := bstep (se 2 (by rfl) ⟨2288499, by rfl⟩ : syracuseStep 6102665 = 4576999) B4576999
theorem B4068443 : Blo 2141435 4068443 := bstep (se 1 (by rfl) ⟨3051332, by rfl⟩ : syracuseStep 4068443 = 6102665) B6102665
theorem B2712295 : Blo 2141435 2712295 := bstep (se 1 (by rfl) ⟨2034221, by rfl⟩ : syracuseStep 2712295 = 4068443) B4068443
theorem B3616393 : Blo 2141435 3616393 := bstep (se 2 (by rfl) ⟨1356147, by rfl⟩ : syracuseStep 3616393 = 2712295) B2712295
theorem B4821857 : Blo 2141435 4821857 := bstep (se 2 (by rfl) ⟨1808196, by rfl⟩ : syracuseStep 4821857 = 3616393) B3616393
theorem B3214571 : Blo 2141435 3214571 := bstep (se 1 (by rfl) ⟨2410928, by rfl⟩ : syracuseStep 3214571 = 4821857) B4821857
theorem B2143047 : Blo 2141435 2143047 := bstep (se 1 (by rfl) ⟨1607285, by rfl⟩ : syracuseStep 2143047 = 3214571) B3214571
theorem B2410933 : Blo 2141435 2410933 := bbase (se 5 (by rfl) ⟨113012, by rfl⟩ : syracuseStep 2410933 = 226025) (by norm_num)
theorem B3214577 : Blo 2141435 3214577 := bstep (se 2 (by rfl) ⟨1205466, by rfl⟩ : syracuseStep 3214577 = 2410933) B2410933
theorem B2143051 : Blo 2141435 2143051 := bstep (se 1 (by rfl) ⟨1607288, by rfl⟩ : syracuseStep 2143051 = 3214577) B3214577
theorem B2712305 : Blo 2141435 2712305 := bbase (se 2 (by rfl) ⟨1017114, by rfl⟩ : syracuseStep 2712305 = 2034229) (by norm_num)
theorem B7232813 : Blo 2141435 7232813 := bstep (se 3 (by rfl) ⟨1356152, by rfl⟩ : syracuseStep 7232813 = 2712305) B2712305
theorem B4821875 : Blo 2141435 4821875 := bstep (se 1 (by rfl) ⟨3616406, by rfl⟩ : syracuseStep 4821875 = 7232813) B7232813
theorem B3214583 : Blo 2141435 3214583 := bstep (se 1 (by rfl) ⟨2410937, by rfl⟩ : syracuseStep 3214583 = 4821875) B4821875
theorem B2143055 : Blo 2141435 2143055 := bstep (se 1 (by rfl) ⟨1607291, by rfl⟩ : syracuseStep 2143055 = 3214583) B3214583
theorem B3214589 : Blo 2141435 3214589 := bbase (se 3 (by rfl) ⟨602735, by rfl⟩ : syracuseStep 3214589 = 1205471) (by norm_num)
theorem B2143059 : Blo 2141435 2143059 := bstep (se 1 (by rfl) ⟨1607294, by rfl⟩ : syracuseStep 2143059 = 3214589) B3214589
theorem B4821893 : Blo 2141435 4821893 := bbase (se 4 (by rfl) ⟨452052, by rfl⟩ : syracuseStep 4821893 = 904105) (by norm_num)
theorem B3214595 : Blo 2141435 3214595 := bstep (se 1 (by rfl) ⟨2410946, by rfl⟩ : syracuseStep 3214595 = 4821893) B4821893
theorem B2143063 : Blo 2141435 2143063 := bstep (se 1 (by rfl) ⟨1607297, by rfl⟩ : syracuseStep 2143063 = 3214595) B3214595
theorem B2288521 : Blo 2141435 2288521 := bbase (se 2 (by rfl) ⟨858195, by rfl⟩ : syracuseStep 2288521 = 1716391) (by norm_num)
theorem B3051361 : Blo 2141435 3051361 := bstep (se 2 (by rfl) ⟨1144260, by rfl⟩ : syracuseStep 3051361 = 2288521) B2288521
theorem B4068481 : Blo 2141435 4068481 := bstep (se 2 (by rfl) ⟨1525680, by rfl⟩ : syracuseStep 4068481 = 3051361) B3051361
theorem B5424641 : Blo 2141435 5424641 := bstep (se 2 (by rfl) ⟨2034240, by rfl⟩ : syracuseStep 5424641 = 4068481) B4068481
theorem B3616427 : Blo 2141435 3616427 := bstep (se 1 (by rfl) ⟨2712320, by rfl⟩ : syracuseStep 3616427 = 5424641) B5424641
theorem B2410951 : Blo 2141435 2410951 := bstep (se 1 (by rfl) ⟨1808213, by rfl⟩ : syracuseStep 2410951 = 3616427) B3616427
theorem B3214601 : Blo 2141435 3214601 := bstep (se 2 (by rfl) ⟨1205475, by rfl⟩ : syracuseStep 3214601 = 2410951) B2410951
theorem B2143067 : Blo 2141435 2143067 := bstep (se 1 (by rfl) ⟨1607300, by rfl⟩ : syracuseStep 2143067 = 3214601) B3214601
theorem B10849301 : Blo 2141435 10849301 := bbase (se 6 (by rfl) ⟨254280, by rfl⟩ : syracuseStep 10849301 = 508561) (by norm_num)
theorem B7232867 : Blo 2141435 7232867 := bstep (se 1 (by rfl) ⟨5424650, by rfl⟩ : syracuseStep 7232867 = 10849301) B10849301
theorem B4821911 : Blo 2141435 4821911 := bstep (se 1 (by rfl) ⟨3616433, by rfl⟩ : syracuseStep 4821911 = 7232867) B7232867
theorem B3214607 : Blo 2141435 3214607 := bstep (se 1 (by rfl) ⟨2410955, by rfl⟩ : syracuseStep 3214607 = 4821911) B4821911
theorem B2143071 : Blo 2141435 2143071 := bstep (se 1 (by rfl) ⟨1607303, by rfl⟩ : syracuseStep 2143071 = 3214607) B3214607
theorem B3214613 : Blo 2141435 3214613 := bbase (se 6 (by rfl) ⟨75342, by rfl⟩ : syracuseStep 3214613 = 150685) (by norm_num)
theorem B2143075 : Blo 2141435 2143075 := bstep (se 1 (by rfl) ⟨1607306, by rfl⟩ : syracuseStep 2143075 = 3214613) B3214613
theorem B2383489 : Blo 2141435 2383489 := bbase (se 2 (by rfl) ⟨893808, by rfl⟩ : syracuseStep 2383489 = 1787617) (by norm_num)
theorem B12711941 : Blo 2141435 12711941 := bstep (se 4 (by rfl) ⟨1191744, by rfl⟩ : syracuseStep 12711941 = 2383489) B2383489
theorem B8474627 : Blo 2141435 8474627 := bstep (se 1 (by rfl) ⟨6355970, by rfl⟩ : syracuseStep 8474627 = 12711941) B12711941
theorem B5649751 : Blo 2141435 5649751 := bstep (se 1 (by rfl) ⟨4237313, by rfl⟩ : syracuseStep 5649751 = 8474627) B8474627
theorem B7533001 : Blo 2141435 7533001 := bstep (se 2 (by rfl) ⟨2824875, by rfl⟩ : syracuseStep 7533001 = 5649751) B5649751
theorem B10044001 : Blo 2141435 10044001 := bstep (se 2 (by rfl) ⟨3766500, by rfl⟩ : syracuseStep 10044001 = 7533001) B7533001
theorem B13392001 : Blo 2141435 13392001 := bstep (se 2 (by rfl) ⟨5022000, by rfl⟩ : syracuseStep 13392001 = 10044001) B10044001
theorem B17856001 : Blo 2141435 17856001 := bstep (se 2 (by rfl) ⟨6696000, by rfl⟩ : syracuseStep 17856001 = 13392001) B13392001
theorem B23808001 : Blo 2141435 23808001 := bstep (se 2 (by rfl) ⟨8928000, by rfl⟩ : syracuseStep 23808001 = 17856001) B17856001
theorem B31744001 : Blo 2141435 31744001 := bstep (se 2 (by rfl) ⟨11904000, by rfl⟩ : syracuseStep 31744001 = 23808001) B23808001
theorem B21162667 : Blo 2141435 21162667 := bstep (se 1 (by rfl) ⟨15872000, by rfl⟩ : syracuseStep 21162667 = 31744001) B31744001
theorem B28216889 : Blo 2141435 28216889 := bstep (se 2 (by rfl) ⟨10581333, by rfl⟩ : syracuseStep 28216889 = 21162667) B21162667
theorem B18811259 : Blo 2141435 18811259 := bstep (se 1 (by rfl) ⟨14108444, by rfl⟩ : syracuseStep 18811259 = 28216889) B28216889
theorem B12540839 : Blo 2141435 12540839 := bstep (se 1 (by rfl) ⟨9405629, by rfl⟩ : syracuseStep 12540839 = 18811259) B18811259
theorem B33442237 : Blo 2141435 33442237 := bstep (se 3 (by rfl) ⟨6270419, by rfl⟩ : syracuseStep 33442237 = 12540839) B12540839
theorem B44589649 : Blo 2141435 44589649 := bstep (se 2 (by rfl) ⟨16721118, by rfl⟩ : syracuseStep 44589649 = 33442237) B33442237
theorem B59452865 : Blo 2141435 59452865 := bstep (se 2 (by rfl) ⟨22294824, by rfl⟩ : syracuseStep 59452865 = 44589649) B44589649
theorem B39635243 : Blo 2141435 39635243 := bstep (se 1 (by rfl) ⟨29726432, by rfl⟩ : syracuseStep 39635243 = 59452865) B59452865
theorem B26423495 : Blo 2141435 26423495 := bstep (se 1 (by rfl) ⟨19817621, by rfl⟩ : syracuseStep 26423495 = 39635243) B39635243
theorem B17615663 : Blo 2141435 17615663 := bstep (se 1 (by rfl) ⟨13211747, by rfl⟩ : syracuseStep 17615663 = 26423495) B26423495
theorem B11743775 : Blo 2141435 11743775 := bstep (se 1 (by rfl) ⟨8807831, by rfl⟩ : syracuseStep 11743775 = 17615663) B17615663
theorem B7829183 : Blo 2141435 7829183 := bstep (se 1 (by rfl) ⟨5871887, by rfl⟩ : syracuseStep 7829183 = 11743775) B11743775
theorem B20877821 : Blo 2141435 20877821 := bstep (se 3 (by rfl) ⟨3914591, by rfl⟩ : syracuseStep 20877821 = 7829183) B7829183
theorem B13918547 : Blo 2141435 13918547 := bstep (se 1 (by rfl) ⟨10438910, by rfl⟩ : syracuseStep 13918547 = 20877821) B20877821
theorem B9279031 : Blo 2141435 9279031 := bstep (se 1 (by rfl) ⟨6959273, by rfl⟩ : syracuseStep 9279031 = 13918547) B13918547
theorem B12372041 : Blo 2141435 12372041 := bstep (se 2 (by rfl) ⟨4639515, by rfl⟩ : syracuseStep 12372041 = 9279031) B9279031
theorem B8248027 : Blo 2141435 8248027 := bstep (se 1 (by rfl) ⟨6186020, by rfl⟩ : syracuseStep 8248027 = 12372041) B12372041
theorem B10997369 : Blo 2141435 10997369 := bstep (se 2 (by rfl) ⟨4124013, by rfl⟩ : syracuseStep 10997369 = 8248027) B8248027
theorem B7331579 : Blo 2141435 7331579 := bstep (se 1 (by rfl) ⟨5498684, by rfl⟩ : syracuseStep 7331579 = 10997369) B10997369
theorem B4887719 : Blo 2141435 4887719 := bstep (se 1 (by rfl) ⟨3665789, by rfl⟩ : syracuseStep 4887719 = 7331579) B7331579
theorem B3258479 : Blo 2141435 3258479 := bstep (se 1 (by rfl) ⟨2443859, by rfl⟩ : syracuseStep 3258479 = 4887719) B4887719
theorem B2172319 : Blo 2141435 2172319 := bstep (se 1 (by rfl) ⟨1629239, by rfl⟩ : syracuseStep 2172319 = 3258479) B3258479
theorem B11585701 : Blo 2141435 11585701 := bstep (se 4 (by rfl) ⟨1086159, by rfl⟩ : syracuseStep 11585701 = 2172319) B2172319
theorem B15447601 : Blo 2141435 15447601 := bstep (se 2 (by rfl) ⟨5792850, by rfl⟩ : syracuseStep 15447601 = 11585701) B11585701
theorem B20596801 : Blo 2141435 20596801 := bstep (se 2 (by rfl) ⟨7723800, by rfl⟩ : syracuseStep 20596801 = 15447601) B15447601
theorem B27462401 : Blo 2141435 27462401 := bstep (se 2 (by rfl) ⟨10298400, by rfl⟩ : syracuseStep 27462401 = 20596801) B20596801
theorem B18308267 : Blo 2141435 18308267 := bstep (se 1 (by rfl) ⟨13731200, by rfl⟩ : syracuseStep 18308267 = 27462401) B27462401
theorem B12205511 : Blo 2141435 12205511 := bstep (se 1 (by rfl) ⟨9154133, by rfl⟩ : syracuseStep 12205511 = 18308267) B18308267
theorem B8137007 : Blo 2141435 8137007 := bstep (se 1 (by rfl) ⟨6102755, by rfl⟩ : syracuseStep 8137007 = 12205511) B12205511
theorem B5424671 : Blo 2141435 5424671 := bstep (se 1 (by rfl) ⟨4068503, by rfl⟩ : syracuseStep 5424671 = 8137007) B8137007
theorem B3616447 : Blo 2141435 3616447 := bstep (se 1 (by rfl) ⟨2712335, by rfl⟩ : syracuseStep 3616447 = 5424671) B5424671
theorem B4821929 : Blo 2141435 4821929 := bstep (se 2 (by rfl) ⟨1808223, by rfl⟩ : syracuseStep 4821929 = 3616447) B3616447
theorem B3214619 : Blo 2141435 3214619 := bstep (se 1 (by rfl) ⟨2410964, by rfl⟩ : syracuseStep 3214619 = 4821929) B4821929
theorem B2143079 : Blo 2141435 2143079 := bstep (se 1 (by rfl) ⟨1607309, by rfl⟩ : syracuseStep 2143079 = 3214619) B3214619
theorem B2410969 : Blo 2141435 2410969 := bbase (se 2 (by rfl) ⟨904113, by rfl⟩ : syracuseStep 2410969 = 1808227) (by norm_num)
theorem B3214625 : Blo 2141435 3214625 := bstep (se 2 (by rfl) ⟨1205484, by rfl⟩ : syracuseStep 3214625 = 2410969) B2410969
theorem B2143083 : Blo 2141435 2143083 := bstep (se 1 (by rfl) ⟨1607312, by rfl⟩ : syracuseStep 2143083 = 3214625) B3214625
theorem B3051389 : Blo 2141435 3051389 := bbase (se 3 (by rfl) ⟨572135, by rfl⟩ : syracuseStep 3051389 = 1144271) (by norm_num)
theorem B8137037 : Blo 2141435 8137037 := bstep (se 3 (by rfl) ⟨1525694, by rfl⟩ : syracuseStep 8137037 = 3051389) B3051389
theorem B5424691 : Blo 2141435 5424691 := bstep (se 1 (by rfl) ⟨4068518, by rfl⟩ : syracuseStep 5424691 = 8137037) B8137037
theorem B7232921 : Blo 2141435 7232921 := bstep (se 2 (by rfl) ⟨2712345, by rfl⟩ : syracuseStep 7232921 = 5424691) B5424691
theorem B4821947 : Blo 2141435 4821947 := bstep (se 1 (by rfl) ⟨3616460, by rfl⟩ : syracuseStep 4821947 = 7232921) B7232921
theorem B3214631 : Blo 2141435 3214631 := bstep (se 1 (by rfl) ⟨2410973, by rfl⟩ : syracuseStep 3214631 = 4821947) B4821947
theorem B2143087 : Blo 2141435 2143087 := bstep (se 1 (by rfl) ⟨1607315, by rfl⟩ : syracuseStep 2143087 = 3214631) B3214631
theorem B3214637 : Blo 2141435 3214637 := bbase (se 3 (by rfl) ⟨602744, by rfl⟩ : syracuseStep 3214637 = 1205489) (by norm_num)
theorem B2143091 : Blo 2141435 2143091 := bstep (se 1 (by rfl) ⟨1607318, by rfl⟩ : syracuseStep 2143091 = 3214637) B3214637
theorem B4821965 : Blo 2141435 4821965 := bbase (se 3 (by rfl) ⟨904118, by rfl⟩ : syracuseStep 4821965 = 1808237) (by norm_num)
theorem B3214643 : Blo 2141435 3214643 := bstep (se 1 (by rfl) ⟨2410982, by rfl⟩ : syracuseStep 3214643 = 4821965) B4821965
theorem B2143095 : Blo 2141435 2143095 := bstep (se 1 (by rfl) ⟨1607321, by rfl⟩ : syracuseStep 2143095 = 3214643) B3214643
theorem B2712361 : Blo 2141435 2712361 := bbase (se 2 (by rfl) ⟨1017135, by rfl⟩ : syracuseStep 2712361 = 2034271) (by norm_num)
theorem B3616481 : Blo 2141435 3616481 := bstep (se 2 (by rfl) ⟨1356180, by rfl⟩ : syracuseStep 3616481 = 2712361) B2712361
theorem B2410987 : Blo 2141435 2410987 := bstep (se 1 (by rfl) ⟨1808240, by rfl⟩ : syracuseStep 2410987 = 3616481) B3616481
theorem B3214649 : Blo 2141435 3214649 := bstep (se 2 (by rfl) ⟨1205493, by rfl⟩ : syracuseStep 3214649 = 2410987) B2410987
theorem B2143099 : Blo 2141435 2143099 := bstep (se 1 (by rfl) ⟨1607324, by rfl⟩ : syracuseStep 2143099 = 3214649) B3214649
theorem B4887773 : Blo 2141435 4887773 := bbase (se 3 (by rfl) ⟨916457, by rfl⟩ : syracuseStep 4887773 = 1832915) (by norm_num)
theorem B3258515 : Blo 2141435 3258515 := bstep (se 1 (by rfl) ⟨2443886, by rfl⟩ : syracuseStep 3258515 = 4887773) B4887773
theorem B8689373 : Blo 2141435 8689373 := bstep (se 3 (by rfl) ⟨1629257, by rfl⟩ : syracuseStep 8689373 = 3258515) B3258515
theorem B5792915 : Blo 2141435 5792915 := bstep (se 1 (by rfl) ⟨4344686, by rfl⟩ : syracuseStep 5792915 = 8689373) B8689373
theorem B15447773 : Blo 2141435 15447773 := bstep (se 3 (by rfl) ⟨2896457, by rfl⟩ : syracuseStep 15447773 = 5792915) B5792915
theorem B10298515 : Blo 2141435 10298515 := bstep (se 1 (by rfl) ⟨7723886, by rfl⟩ : syracuseStep 10298515 = 15447773) B15447773
theorem B13731353 : Blo 2141435 13731353 := bstep (se 2 (by rfl) ⟨5149257, by rfl⟩ : syracuseStep 13731353 = 10298515) B10298515
theorem B9154235 : Blo 2141435 9154235 := bstep (se 1 (by rfl) ⟨6865676, by rfl⟩ : syracuseStep 9154235 = 13731353) B13731353
theorem B24411293 : Blo 2141435 24411293 := bstep (se 3 (by rfl) ⟨4577117, by rfl⟩ : syracuseStep 24411293 = 9154235) B9154235
theorem B16274195 : Blo 2141435 16274195 := bstep (se 1 (by rfl) ⟨12205646, by rfl⟩ : syracuseStep 16274195 = 24411293) B24411293
theorem B10849463 : Blo 2141435 10849463 := bstep (se 1 (by rfl) ⟨8137097, by rfl⟩ : syracuseStep 10849463 = 16274195) B16274195
theorem B7232975 : Blo 2141435 7232975 := bstep (se 1 (by rfl) ⟨5424731, by rfl⟩ : syracuseStep 7232975 = 10849463) B10849463
theorem B4821983 : Blo 2141435 4821983 := bstep (se 1 (by rfl) ⟨3616487, by rfl⟩ : syracuseStep 4821983 = 7232975) B7232975
theorem B3214655 : Blo 2141435 3214655 := bstep (se 1 (by rfl) ⟨2410991, by rfl⟩ : syracuseStep 3214655 = 4821983) B4821983
theorem B2143103 : Blo 2141435 2143103 := bstep (se 1 (by rfl) ⟨1607327, by rfl⟩ : syracuseStep 2143103 = 3214655) B3214655
theorem B3214661 : Blo 2141435 3214661 := bbase (se 4 (by rfl) ⟨301374, by rfl⟩ : syracuseStep 3214661 = 602749) (by norm_num)
theorem B2143107 : Blo 2141435 2143107 := bstep (se 1 (by rfl) ⟨1607330, by rfl⟩ : syracuseStep 2143107 = 3214661) B3214661
theorem B3616501 : Blo 2141435 3616501 := bbase (se 5 (by rfl) ⟨169523, by rfl⟩ : syracuseStep 3616501 = 339047) (by norm_num)
theorem B4822001 : Blo 2141435 4822001 := bstep (se 2 (by rfl) ⟨1808250, by rfl⟩ : syracuseStep 4822001 = 3616501) B3616501
theorem B3214667 : Blo 2141435 3214667 := bstep (se 1 (by rfl) ⟨2411000, by rfl⟩ : syracuseStep 3214667 = 4822001) B4822001
theorem B2143111 : Blo 2141435 2143111 := bstep (se 1 (by rfl) ⟨1607333, by rfl⟩ : syracuseStep 2143111 = 3214667) B3214667
theorem B2411005 : Blo 2141435 2411005 := bbase (se 3 (by rfl) ⟨452063, by rfl⟩ : syracuseStep 2411005 = 904127) (by norm_num)
theorem B3214673 : Blo 2141435 3214673 := bstep (se 2 (by rfl) ⟨1205502, by rfl⟩ : syracuseStep 3214673 = 2411005) B2411005
theorem B2143115 : Blo 2141435 2143115 := bstep (se 1 (by rfl) ⟨1607336, by rfl⟩ : syracuseStep 2143115 = 3214673) B3214673
theorem B7233029 : Blo 2141435 7233029 := bbase (se 4 (by rfl) ⟨678096, by rfl⟩ : syracuseStep 7233029 = 1356193) (by norm_num)
theorem B4822019 : Blo 2141435 4822019 := bstep (se 1 (by rfl) ⟨3616514, by rfl⟩ : syracuseStep 4822019 = 7233029) B7233029
theorem B3214679 : Blo 2141435 3214679 := bstep (se 1 (by rfl) ⟨2411009, by rfl⟩ : syracuseStep 3214679 = 4822019) B4822019
theorem B2143119 : Blo 2141435 2143119 := bstep (se 1 (by rfl) ⟨1607339, by rfl⟩ : syracuseStep 2143119 = 3214679) B3214679
theorem B3214685 : Blo 2141435 3214685 := bbase (se 3 (by rfl) ⟨602753, by rfl⟩ : syracuseStep 3214685 = 1205507) (by norm_num)
theorem B2143123 : Blo 2141435 2143123 := bstep (se 1 (by rfl) ⟨1607342, by rfl⟩ : syracuseStep 2143123 = 3214685) B3214685
theorem B4822037 : Blo 2141435 4822037 := bbase (se 6 (by rfl) ⟨113016, by rfl⟩ : syracuseStep 4822037 = 226033) (by norm_num)
theorem B3214691 : Blo 2141435 3214691 := bstep (se 1 (by rfl) ⟨2411018, by rfl⟩ : syracuseStep 3214691 = 4822037) B4822037
theorem B2143127 : Blo 2141435 2143127 := bstep (se 1 (by rfl) ⟨1607345, by rfl⟩ : syracuseStep 2143127 = 3214691) B3214691
theorem B8137205 : Blo 2141435 8137205 := bbase (se 5 (by rfl) ⟨381431, by rfl⟩ : syracuseStep 8137205 = 762863) (by norm_num)
theorem B5424803 : Blo 2141435 5424803 := bstep (se 1 (by rfl) ⟨4068602, by rfl⟩ : syracuseStep 5424803 = 8137205) B8137205
theorem B3616535 : Blo 2141435 3616535 := bstep (se 1 (by rfl) ⟨2712401, by rfl⟩ : syracuseStep 3616535 = 5424803) B5424803
theorem B2411023 : Blo 2141435 2411023 := bstep (se 1 (by rfl) ⟨1808267, by rfl⟩ : syracuseStep 2411023 = 3616535) B3616535
theorem B3214697 : Blo 2141435 3214697 := bstep (se 2 (by rfl) ⟨1205511, by rfl⟩ : syracuseStep 3214697 = 2411023) B2411023
theorem B2143131 : Blo 2141435 2143131 := bstep (se 1 (by rfl) ⟨1607348, by rfl⟩ : syracuseStep 2143131 = 3214697) B3214697
theorem B2288593 : Blo 2141435 2288593 := bbase (se 2 (by rfl) ⟨858222, by rfl⟩ : syracuseStep 2288593 = 1716445) (by norm_num)
theorem B12205829 : Blo 2141435 12205829 := bstep (se 4 (by rfl) ⟨1144296, by rfl⟩ : syracuseStep 12205829 = 2288593) B2288593
theorem B8137219 : Blo 2141435 8137219 := bstep (se 1 (by rfl) ⟨6102914, by rfl⟩ : syracuseStep 8137219 = 12205829) B12205829
theorem B10849625 : Blo 2141435 10849625 := bstep (se 2 (by rfl) ⟨4068609, by rfl⟩ : syracuseStep 10849625 = 8137219) B8137219
theorem B7233083 : Blo 2141435 7233083 := bstep (se 1 (by rfl) ⟨5424812, by rfl⟩ : syracuseStep 7233083 = 10849625) B10849625
theorem B4822055 : Blo 2141435 4822055 := bstep (se 1 (by rfl) ⟨3616541, by rfl⟩ : syracuseStep 4822055 = 7233083) B7233083
theorem B3214703 : Blo 2141435 3214703 := bstep (se 1 (by rfl) ⟨2411027, by rfl⟩ : syracuseStep 3214703 = 4822055) B4822055
theorem B2143135 : Blo 2141435 2143135 := bstep (se 1 (by rfl) ⟨1607351, by rfl⟩ : syracuseStep 2143135 = 3214703) B3214703
theorem B3214709 : Blo 2141435 3214709 := bbase (se 5 (by rfl) ⟨150689, by rfl⟩ : syracuseStep 3214709 = 301379) (by norm_num)
theorem B2143139 : Blo 2141435 2143139 := bstep (se 1 (by rfl) ⟨1607354, by rfl⟩ : syracuseStep 2143139 = 3214709) B3214709
theorem B3051469 : Blo 2141435 3051469 := bbase (se 3 (by rfl) ⟨572150, by rfl⟩ : syracuseStep 3051469 = 1144301) (by norm_num)
theorem B4068625 : Blo 2141435 4068625 := bstep (se 2 (by rfl) ⟨1525734, by rfl⟩ : syracuseStep 4068625 = 3051469) B3051469
theorem B5424833 : Blo 2141435 5424833 := bstep (se 2 (by rfl) ⟨2034312, by rfl⟩ : syracuseStep 5424833 = 4068625) B4068625
theorem B3616555 : Blo 2141435 3616555 := bstep (se 1 (by rfl) ⟨2712416, by rfl⟩ : syracuseStep 3616555 = 5424833) B5424833
theorem B4822073 : Blo 2141435 4822073 := bstep (se 2 (by rfl) ⟨1808277, by rfl⟩ : syracuseStep 4822073 = 3616555) B3616555
theorem B3214715 : Blo 2141435 3214715 := bstep (se 1 (by rfl) ⟨2411036, by rfl⟩ : syracuseStep 3214715 = 4822073) B4822073
theorem B2143143 : Blo 2141435 2143143 := bstep (se 1 (by rfl) ⟨1607357, by rfl⟩ : syracuseStep 2143143 = 3214715) B3214715
theorem B2411041 : Blo 2141435 2411041 := bbase (se 2 (by rfl) ⟨904140, by rfl⟩ : syracuseStep 2411041 = 1808281) (by norm_num)
theorem B3214721 : Blo 2141435 3214721 := bstep (se 2 (by rfl) ⟨1205520, by rfl⟩ : syracuseStep 3214721 = 2411041) B2411041
theorem B2143147 : Blo 2141435 2143147 := bstep (se 1 (by rfl) ⟨1607360, by rfl⟩ : syracuseStep 2143147 = 3214721) B3214721
theorem B5424853 : Blo 2141435 5424853 := bbase (se 7 (by rfl) ⟨63572, by rfl⟩ : syracuseStep 5424853 = 127145) (by norm_num)
theorem B7233137 : Blo 2141435 7233137 := bstep (se 2 (by rfl) ⟨2712426, by rfl⟩ : syracuseStep 7233137 = 5424853) B5424853
theorem B4822091 : Blo 2141435 4822091 := bstep (se 1 (by rfl) ⟨3616568, by rfl⟩ : syracuseStep 4822091 = 7233137) B7233137
theorem B3214727 : Blo 2141435 3214727 := bstep (se 1 (by rfl) ⟨2411045, by rfl⟩ : syracuseStep 3214727 = 4822091) B4822091
theorem B2143151 : Blo 2141435 2143151 := bstep (se 1 (by rfl) ⟨1607363, by rfl⟩ : syracuseStep 2143151 = 3214727) B3214727
theorem B3214733 : Blo 2141435 3214733 := bbase (se 3 (by rfl) ⟨602762, by rfl⟩ : syracuseStep 3214733 = 1205525) (by norm_num)
theorem B2143155 : Blo 2141435 2143155 := bstep (se 1 (by rfl) ⟨1607366, by rfl⟩ : syracuseStep 2143155 = 3214733) B3214733
theorem B4822109 : Blo 2141435 4822109 := bbase (se 3 (by rfl) ⟨904145, by rfl⟩ : syracuseStep 4822109 = 1808291) (by norm_num)
theorem B3214739 : Blo 2141435 3214739 := bstep (se 1 (by rfl) ⟨2411054, by rfl⟩ : syracuseStep 3214739 = 4822109) B4822109
theorem B2143159 : Blo 2141435 2143159 := bstep (se 1 (by rfl) ⟨1607369, by rfl⟩ : syracuseStep 2143159 = 3214739) B3214739
theorem B3616589 : Blo 2141435 3616589 := bbase (se 3 (by rfl) ⟨678110, by rfl⟩ : syracuseStep 3616589 = 1356221) (by norm_num)
theorem B2411059 : Blo 2141435 2411059 := bstep (se 1 (by rfl) ⟨1808294, by rfl⟩ : syracuseStep 2411059 = 3616589) B3616589
theorem B3214745 : Blo 2141435 3214745 := bstep (se 2 (by rfl) ⟨1205529, by rfl⟩ : syracuseStep 3214745 = 2411059) B2411059
theorem B2143163 : Blo 2141435 2143163 := bstep (se 1 (by rfl) ⟨1607372, by rfl⟩ : syracuseStep 2143163 = 3214745) B3214745
theorem B7724117 : Blo 2141435 7724117 := bbase (se 8 (by rfl) ⟨45258, by rfl⟩ : syracuseStep 7724117 = 90517) (by norm_num)
theorem B20597645 : Blo 2141435 20597645 := bstep (se 3 (by rfl) ⟨3862058, by rfl⟩ : syracuseStep 20597645 = 7724117) B7724117
theorem B13731763 : Blo 2141435 13731763 := bstep (se 1 (by rfl) ⟨10298822, by rfl⟩ : syracuseStep 13731763 = 20597645) B20597645
theorem B18309017 : Blo 2141435 18309017 := bstep (se 2 (by rfl) ⟨6865881, by rfl⟩ : syracuseStep 18309017 = 13731763) B13731763
theorem B12206011 : Blo 2141435 12206011 := bstep (se 1 (by rfl) ⟨9154508, by rfl⟩ : syracuseStep 12206011 = 18309017) B18309017
theorem B16274681 : Blo 2141435 16274681 := bstep (se 2 (by rfl) ⟨6103005, by rfl⟩ : syracuseStep 16274681 = 12206011) B12206011
theorem B10849787 : Blo 2141435 10849787 := bstep (se 1 (by rfl) ⟨8137340, by rfl⟩ : syracuseStep 10849787 = 16274681) B16274681
theorem B7233191 : Blo 2141435 7233191 := bstep (se 1 (by rfl) ⟨5424893, by rfl⟩ : syracuseStep 7233191 = 10849787) B10849787
theorem B4822127 : Blo 2141435 4822127 := bstep (se 1 (by rfl) ⟨3616595, by rfl⟩ : syracuseStep 4822127 = 7233191) B7233191
theorem B3214751 : Blo 2141435 3214751 := bstep (se 1 (by rfl) ⟨2411063, by rfl⟩ : syracuseStep 3214751 = 4822127) B4822127
theorem B2143167 : Blo 2141435 2143167 := bstep (se 1 (by rfl) ⟨1607375, by rfl⟩ : syracuseStep 2143167 = 3214751) B3214751
theorem B3214757 : Blo 2141435 3214757 := bbase (se 4 (by rfl) ⟨301383, by rfl⟩ : syracuseStep 3214757 = 602767) (by norm_num)
theorem B2143171 : Blo 2141435 2143171 := bstep (se 1 (by rfl) ⟨1607378, by rfl⟩ : syracuseStep 2143171 = 3214757) B3214757
theorem B2712457 : Blo 2141435 2712457 := bbase (se 2 (by rfl) ⟨1017171, by rfl⟩ : syracuseStep 2712457 = 2034343) (by norm_num)
theorem B3616609 : Blo 2141435 3616609 := bstep (se 2 (by rfl) ⟨1356228, by rfl⟩ : syracuseStep 3616609 = 2712457) B2712457
theorem B4822145 : Blo 2141435 4822145 := bstep (se 2 (by rfl) ⟨1808304, by rfl⟩ : syracuseStep 4822145 = 3616609) B3616609
theorem B3214763 : Blo 2141435 3214763 := bstep (se 1 (by rfl) ⟨2411072, by rfl⟩ : syracuseStep 3214763 = 4822145) B4822145
theorem B2143175 : Blo 2141435 2143175 := bstep (se 1 (by rfl) ⟨1607381, by rfl⟩ : syracuseStep 2143175 = 3214763) B3214763
theorem B2411077 : Blo 2141435 2411077 := bbase (se 4 (by rfl) ⟨226038, by rfl⟩ : syracuseStep 2411077 = 452077) (by norm_num)
theorem B3214769 : Blo 2141435 3214769 := bstep (se 2 (by rfl) ⟨1205538, by rfl⟩ : syracuseStep 3214769 = 2411077) B2411077
theorem B2143179 : Blo 2141435 2143179 := bstep (se 1 (by rfl) ⟨1607384, by rfl⟩ : syracuseStep 2143179 = 3214769) B3214769
theorem B4068701 : Blo 2141435 4068701 := bbase (se 3 (by rfl) ⟨762881, by rfl⟩ : syracuseStep 4068701 = 1525763) (by norm_num)
theorem B2712467 : Blo 2141435 2712467 := bstep (se 1 (by rfl) ⟨2034350, by rfl⟩ : syracuseStep 2712467 = 4068701) B4068701
theorem B7233245 : Blo 2141435 7233245 := bstep (se 3 (by rfl) ⟨1356233, by rfl⟩ : syracuseStep 7233245 = 2712467) B2712467
theorem B4822163 : Blo 2141435 4822163 := bstep (se 1 (by rfl) ⟨3616622, by rfl⟩ : syracuseStep 4822163 = 7233245) B7233245
theorem B3214775 : Blo 2141435 3214775 := bstep (se 1 (by rfl) ⟨2411081, by rfl⟩ : syracuseStep 3214775 = 4822163) B4822163
theorem B2143183 : Blo 2141435 2143183 := bstep (se 1 (by rfl) ⟨1607387, by rfl⟩ : syracuseStep 2143183 = 3214775) B3214775
theorem B3214781 : Blo 2141435 3214781 := bbase (se 3 (by rfl) ⟨602771, by rfl⟩ : syracuseStep 3214781 = 1205543) (by norm_num)
theorem B2143187 : Blo 2141435 2143187 := bstep (se 1 (by rfl) ⟨1607390, by rfl⟩ : syracuseStep 2143187 = 3214781) B3214781
theorem B4822181 : Blo 2141435 4822181 := bbase (se 4 (by rfl) ⟨452079, by rfl⟩ : syracuseStep 4822181 = 904159) (by norm_num)
theorem B3214787 : Blo 2141435 3214787 := bstep (se 1 (by rfl) ⟨2411090, by rfl⟩ : syracuseStep 3214787 = 4822181) B4822181
theorem B2143191 : Blo 2141435 2143191 := bstep (se 1 (by rfl) ⟨1607393, by rfl⟩ : syracuseStep 2143191 = 3214787) B3214787
theorem B5424965 : Blo 2141435 5424965 := bbase (se 4 (by rfl) ⟨508590, by rfl⟩ : syracuseStep 5424965 = 1017181) (by norm_num)
theorem B3616643 : Blo 2141435 3616643 := bstep (se 1 (by rfl) ⟨2712482, by rfl⟩ : syracuseStep 3616643 = 5424965) B5424965
theorem B2411095 : Blo 2141435 2411095 := bstep (se 1 (by rfl) ⟨1808321, by rfl⟩ : syracuseStep 2411095 = 3616643) B3616643
theorem B3214793 : Blo 2141435 3214793 := bstep (se 2 (by rfl) ⟨1205547, by rfl⟩ : syracuseStep 3214793 = 2411095) B2411095
theorem B2143195 : Blo 2141435 2143195 := bstep (se 1 (by rfl) ⟨1607396, by rfl⟩ : syracuseStep 2143195 = 3214793) B3214793
theorem B3862117 : Blo 2141435 3862117 := bbase (se 4 (by rfl) ⟨362073, by rfl⟩ : syracuseStep 3862117 = 724147) (by norm_num)
theorem B5149489 : Blo 2141435 5149489 := bstep (se 2 (by rfl) ⟨1931058, by rfl⟩ : syracuseStep 5149489 = 3862117) B3862117
theorem B6865985 : Blo 2141435 6865985 := bstep (se 2 (by rfl) ⟨2574744, by rfl⟩ : syracuseStep 6865985 = 5149489) B5149489
theorem B4577323 : Blo 2141435 4577323 := bstep (se 1 (by rfl) ⟨3432992, by rfl⟩ : syracuseStep 4577323 = 6865985) B6865985
theorem B6103097 : Blo 2141435 6103097 := bstep (se 2 (by rfl) ⟨2288661, by rfl⟩ : syracuseStep 6103097 = 4577323) B4577323
theorem B4068731 : Blo 2141435 4068731 := bstep (se 1 (by rfl) ⟨3051548, by rfl⟩ : syracuseStep 4068731 = 6103097) B6103097
theorem B10849949 : Blo 2141435 10849949 := bstep (se 3 (by rfl) ⟨2034365, by rfl⟩ : syracuseStep 10849949 = 4068731) B4068731
theorem B7233299 : Blo 2141435 7233299 := bstep (se 1 (by rfl) ⟨5424974, by rfl⟩ : syracuseStep 7233299 = 10849949) B10849949
theorem B4822199 : Blo 2141435 4822199 := bstep (se 1 (by rfl) ⟨3616649, by rfl⟩ : syracuseStep 4822199 = 7233299) B7233299
theorem B3214799 : Blo 2141435 3214799 := bstep (se 1 (by rfl) ⟨2411099, by rfl⟩ : syracuseStep 3214799 = 4822199) B4822199
theorem B2143199 : Blo 2141435 2143199 := bstep (se 1 (by rfl) ⟨1607399, by rfl⟩ : syracuseStep 2143199 = 3214799) B3214799
theorem B3214805 : Blo 2141435 3214805 := bbase (se 7 (by rfl) ⟨37673, by rfl⟩ : syracuseStep 3214805 = 75347) (by norm_num)
theorem B2143203 : Blo 2141435 2143203 := bstep (se 1 (by rfl) ⟨1607402, by rfl⟩ : syracuseStep 2143203 = 3214805) B3214805
theorem B8137493 : Blo 2141435 8137493 := bbase (se 6 (by rfl) ⟨190722, by rfl⟩ : syracuseStep 8137493 = 381445) (by norm_num)
theorem B5424995 : Blo 2141435 5424995 := bstep (se 1 (by rfl) ⟨4068746, by rfl⟩ : syracuseStep 5424995 = 8137493) B8137493
theorem B3616663 : Blo 2141435 3616663 := bstep (se 1 (by rfl) ⟨2712497, by rfl⟩ : syracuseStep 3616663 = 5424995) B5424995
theorem B4822217 : Blo 2141435 4822217 := bstep (se 2 (by rfl) ⟨1808331, by rfl⟩ : syracuseStep 4822217 = 3616663) B3616663
theorem B3214811 : Blo 2141435 3214811 := bstep (se 1 (by rfl) ⟨2411108, by rfl⟩ : syracuseStep 3214811 = 4822217) B4822217
theorem B2143207 : Blo 2141435 2143207 := bstep (se 1 (by rfl) ⟨1607405, by rfl⟩ : syracuseStep 2143207 = 3214811) B3214811
theorem B2411113 : Blo 2141435 2411113 := bbase (se 2 (by rfl) ⟨904167, by rfl⟩ : syracuseStep 2411113 = 1808335) (by norm_num)
theorem B3214817 : Blo 2141435 3214817 := bstep (se 2 (by rfl) ⟨1205556, by rfl⟩ : syracuseStep 3214817 = 2411113) B2411113
theorem B2143211 : Blo 2141435 2143211 := bstep (se 1 (by rfl) ⟨1607408, by rfl⟩ : syracuseStep 2143211 = 3214817) B3214817
theorem B4577357 : Blo 2141435 4577357 := bbase (se 3 (by rfl) ⟨858254, by rfl⟩ : syracuseStep 4577357 = 1716509) (by norm_num)
theorem B12206285 : Blo 2141435 12206285 := bstep (se 3 (by rfl) ⟨2288678, by rfl⟩ : syracuseStep 12206285 = 4577357) B4577357
theorem B8137523 : Blo 2141435 8137523 := bstep (se 1 (by rfl) ⟨6103142, by rfl⟩ : syracuseStep 8137523 = 12206285) B12206285
theorem B5425015 : Blo 2141435 5425015 := bstep (se 1 (by rfl) ⟨4068761, by rfl⟩ : syracuseStep 5425015 = 8137523) B8137523
theorem B7233353 : Blo 2141435 7233353 := bstep (se 2 (by rfl) ⟨2712507, by rfl⟩ : syracuseStep 7233353 = 5425015) B5425015
theorem B4822235 : Blo 2141435 4822235 := bstep (se 1 (by rfl) ⟨3616676, by rfl⟩ : syracuseStep 4822235 = 7233353) B7233353
theorem B3214823 : Blo 2141435 3214823 := bstep (se 1 (by rfl) ⟨2411117, by rfl⟩ : syracuseStep 3214823 = 4822235) B4822235
theorem B2143215 : Blo 2141435 2143215 := bstep (se 1 (by rfl) ⟨1607411, by rfl⟩ : syracuseStep 2143215 = 3214823) B3214823
theorem B3214829 : Blo 2141435 3214829 := bbase (se 3 (by rfl) ⟨602780, by rfl⟩ : syracuseStep 3214829 = 1205561) (by norm_num)
theorem B2143219 : Blo 2141435 2143219 := bstep (se 1 (by rfl) ⟨1607414, by rfl⟩ : syracuseStep 2143219 = 3214829) B3214829
theorem B4822253 : Blo 2141435 4822253 := bbase (se 3 (by rfl) ⟨904172, by rfl⟩ : syracuseStep 4822253 = 1808345) (by norm_num)
theorem B3214835 : Blo 2141435 3214835 := bstep (se 1 (by rfl) ⟨2411126, by rfl⟩ : syracuseStep 3214835 = 4822253) B4822253
theorem B2143223 : Blo 2141435 2143223 := bstep (se 1 (by rfl) ⟨1607417, by rfl⟩ : syracuseStep 2143223 = 3214835) B3214835
theorem B3051589 : Blo 2141435 3051589 := bbase (se 4 (by rfl) ⟨286086, by rfl⟩ : syracuseStep 3051589 = 572173) (by norm_num)
theorem B4068785 : Blo 2141435 4068785 := bstep (se 2 (by rfl) ⟨1525794, by rfl⟩ : syracuseStep 4068785 = 3051589) B3051589
theorem B2712523 : Blo 2141435 2712523 := bstep (se 1 (by rfl) ⟨2034392, by rfl⟩ : syracuseStep 2712523 = 4068785) B4068785
theorem B3616697 : Blo 2141435 3616697 := bstep (se 2 (by rfl) ⟨1356261, by rfl⟩ : syracuseStep 3616697 = 2712523) B2712523
theorem B2411131 : Blo 2141435 2411131 := bstep (se 1 (by rfl) ⟨1808348, by rfl⟩ : syracuseStep 2411131 = 3616697) B3616697
theorem B3214841 : Blo 2141435 3214841 := bstep (se 2 (by rfl) ⟨1205565, by rfl⟩ : syracuseStep 3214841 = 2411131) B2411131
theorem B2143227 : Blo 2141435 2143227 := bstep (se 1 (by rfl) ⟨1607420, by rfl⟩ : syracuseStep 2143227 = 3214841) B3214841
theorem B13034837 : Blo 2141435 13034837 := bbase (se 12 (by rfl) ⟨4773, by rfl⟩ : syracuseStep 13034837 = 9547) (by norm_num)
theorem B8689891 : Blo 2141435 8689891 := bstep (se 1 (by rfl) ⟨6517418, by rfl⟩ : syracuseStep 8689891 = 13034837) B13034837
theorem B11586521 : Blo 2141435 11586521 := bstep (se 2 (by rfl) ⟨4344945, by rfl⟩ : syracuseStep 11586521 = 8689891) B8689891
theorem B30897389 : Blo 2141435 30897389 := bstep (se 3 (by rfl) ⟨5793260, by rfl⟩ : syracuseStep 30897389 = 11586521) B11586521
theorem B82393037 : Blo 2141435 82393037 := bstep (se 3 (by rfl) ⟨15448694, by rfl⟩ : syracuseStep 82393037 = 30897389) B30897389
theorem B54928691 : Blo 2141435 54928691 := bstep (se 1 (by rfl) ⟨41196518, by rfl⟩ : syracuseStep 54928691 = 82393037) B82393037
theorem B36619127 : Blo 2141435 36619127 := bstep (se 1 (by rfl) ⟨27464345, by rfl⟩ : syracuseStep 36619127 = 54928691) B54928691
theorem B24412751 : Blo 2141435 24412751 := bstep (se 1 (by rfl) ⟨18309563, by rfl⟩ : syracuseStep 24412751 = 36619127) B36619127
theorem B16275167 : Blo 2141435 16275167 := bstep (se 1 (by rfl) ⟨12206375, by rfl⟩ : syracuseStep 16275167 = 24412751) B24412751
theorem B10850111 : Blo 2141435 10850111 := bstep (se 1 (by rfl) ⟨8137583, by rfl⟩ : syracuseStep 10850111 = 16275167) B16275167
theorem B7233407 : Blo 2141435 7233407 := bstep (se 1 (by rfl) ⟨5425055, by rfl⟩ : syracuseStep 7233407 = 10850111) B10850111
theorem B4822271 : Blo 2141435 4822271 := bstep (se 1 (by rfl) ⟨3616703, by rfl⟩ : syracuseStep 4822271 = 7233407) B7233407
theorem B3214847 : Blo 2141435 3214847 := bstep (se 1 (by rfl) ⟨2411135, by rfl⟩ : syracuseStep 3214847 = 4822271) B4822271
theorem B2143231 : Blo 2141435 2143231 := bstep (se 1 (by rfl) ⟨1607423, by rfl⟩ : syracuseStep 2143231 = 3214847) B3214847
theorem B3214853 : Blo 2141435 3214853 := bbase (se 4 (by rfl) ⟨301392, by rfl⟩ : syracuseStep 3214853 = 602785) (by norm_num)
theorem B2143235 : Blo 2141435 2143235 := bstep (se 1 (by rfl) ⟨1607426, by rfl⟩ : syracuseStep 2143235 = 3214853) B3214853
theorem B3616717 : Blo 2141435 3616717 := bbase (se 3 (by rfl) ⟨678134, by rfl⟩ : syracuseStep 3616717 = 1356269) (by norm_num)
theorem B4822289 : Blo 2141435 4822289 := bstep (se 2 (by rfl) ⟨1808358, by rfl⟩ : syracuseStep 4822289 = 3616717) B3616717
theorem B3214859 : Blo 2141435 3214859 := bstep (se 1 (by rfl) ⟨2411144, by rfl⟩ : syracuseStep 3214859 = 4822289) B4822289
theorem B2143239 : Blo 2141435 2143239 := bstep (se 1 (by rfl) ⟨1607429, by rfl⟩ : syracuseStep 2143239 = 3214859) B3214859
theorem B2411149 : Blo 2141435 2411149 := bbase (se 3 (by rfl) ⟨452090, by rfl⟩ : syracuseStep 2411149 = 904181) (by norm_num)
theorem B3214865 : Blo 2141435 3214865 := bstep (se 2 (by rfl) ⟨1205574, by rfl⟩ : syracuseStep 3214865 = 2411149) B2411149
theorem B2143243 : Blo 2141435 2143243 := bstep (se 1 (by rfl) ⟨1607432, by rfl⟩ : syracuseStep 2143243 = 3214865) B3214865
theorem B7233461 : Blo 2141435 7233461 := bbase (se 5 (by rfl) ⟨339068, by rfl⟩ : syracuseStep 7233461 = 678137) (by norm_num)
theorem B4822307 : Blo 2141435 4822307 := bstep (se 1 (by rfl) ⟨3616730, by rfl⟩ : syracuseStep 4822307 = 7233461) B7233461
theorem B3214871 : Blo 2141435 3214871 := bstep (se 1 (by rfl) ⟨2411153, by rfl⟩ : syracuseStep 3214871 = 4822307) B4822307
theorem B2143247 : Blo 2141435 2143247 := bstep (se 1 (by rfl) ⟨1607435, by rfl⟩ : syracuseStep 2143247 = 3214871) B3214871
theorem B3214877 : Blo 2141435 3214877 := bbase (se 3 (by rfl) ⟨602789, by rfl⟩ : syracuseStep 3214877 = 1205579) (by norm_num)
theorem B2143251 : Blo 2141435 2143251 := bstep (se 1 (by rfl) ⟨1607438, by rfl⟩ : syracuseStep 2143251 = 3214877) B3214877
theorem B4822325 : Blo 2141435 4822325 := bbase (se 5 (by rfl) ⟨226046, by rfl⟩ : syracuseStep 4822325 = 452093) (by norm_num)
theorem B3214883 : Blo 2141435 3214883 := bstep (se 1 (by rfl) ⟨2411162, by rfl⟩ : syracuseStep 3214883 = 4822325) B4822325
theorem B2143255 : Blo 2141435 2143255 := bstep (se 1 (by rfl) ⟨1607441, by rfl⟩ : syracuseStep 2143255 = 3214883) B3214883
theorem B2896669 : Blo 2141435 2896669 := bbase (se 3 (by rfl) ⟨543125, by rfl⟩ : syracuseStep 2896669 = 1086251) (by norm_num)
theorem B3862225 : Blo 2141435 3862225 := bstep (se 2 (by rfl) ⟨1448334, by rfl⟩ : syracuseStep 3862225 = 2896669) B2896669
theorem B20598533 : Blo 2141435 20598533 := bstep (se 4 (by rfl) ⟨1931112, by rfl⟩ : syracuseStep 20598533 = 3862225) B3862225
theorem B13732355 : Blo 2141435 13732355 := bstep (se 1 (by rfl) ⟨10299266, by rfl⟩ : syracuseStep 13732355 = 20598533) B20598533
theorem B9154903 : Blo 2141435 9154903 := bstep (se 1 (by rfl) ⟨6866177, by rfl⟩ : syracuseStep 9154903 = 13732355) B13732355
theorem B12206537 : Blo 2141435 12206537 := bstep (se 2 (by rfl) ⟨4577451, by rfl⟩ : syracuseStep 12206537 = 9154903) B9154903
theorem B8137691 : Blo 2141435 8137691 := bstep (se 1 (by rfl) ⟨6103268, by rfl⟩ : syracuseStep 8137691 = 12206537) B12206537
theorem B5425127 : Blo 2141435 5425127 := bstep (se 1 (by rfl) ⟨4068845, by rfl⟩ : syracuseStep 5425127 = 8137691) B8137691
theorem B3616751 : Blo 2141435 3616751 := bstep (se 1 (by rfl) ⟨2712563, by rfl⟩ : syracuseStep 3616751 = 5425127) B5425127
theorem B2411167 : Blo 2141435 2411167 := bstep (se 1 (by rfl) ⟨1808375, by rfl⟩ : syracuseStep 2411167 = 3616751) B3616751
theorem B3214889 : Blo 2141435 3214889 := bstep (se 2 (by rfl) ⟨1205583, by rfl⟩ : syracuseStep 3214889 = 2411167) B2411167
theorem B2143259 : Blo 2141435 2143259 := bstep (se 1 (by rfl) ⟨1607444, by rfl⟩ : syracuseStep 2143259 = 3214889) B3214889
theorem B16089941 : Blo 2141435 16089941 := bbase (se 9 (by rfl) ⟨47138, by rfl⟩ : syracuseStep 16089941 = 94277) (by norm_num)
theorem B10726627 : Blo 2141435 10726627 := bstep (se 1 (by rfl) ⟨8044970, by rfl⟩ : syracuseStep 10726627 = 16089941) B16089941
theorem B14302169 : Blo 2141435 14302169 := bstep (se 2 (by rfl) ⟨5363313, by rfl⟩ : syracuseStep 14302169 = 10726627) B10726627
theorem B9534779 : Blo 2141435 9534779 := bstep (se 1 (by rfl) ⟨7151084, by rfl⟩ : syracuseStep 9534779 = 14302169) B14302169
theorem B6356519 : Blo 2141435 6356519 := bstep (se 1 (by rfl) ⟨4767389, by rfl⟩ : syracuseStep 6356519 = 9534779) B9534779
theorem B4237679 : Blo 2141435 4237679 := bstep (se 1 (by rfl) ⟨3178259, by rfl⟩ : syracuseStep 4237679 = 6356519) B6356519
theorem B2825119 : Blo 2141435 2825119 := bstep (se 1 (by rfl) ⟨2118839, by rfl⟩ : syracuseStep 2825119 = 4237679) B4237679
theorem B3766825 : Blo 2141435 3766825 := bstep (se 2 (by rfl) ⟨1412559, by rfl⟩ : syracuseStep 3766825 = 2825119) B2825119
theorem B5022433 : Blo 2141435 5022433 := bstep (se 2 (by rfl) ⟨1883412, by rfl⟩ : syracuseStep 5022433 = 3766825) B3766825
theorem B6696577 : Blo 2141435 6696577 := bstep (se 2 (by rfl) ⟨2511216, by rfl⟩ : syracuseStep 6696577 = 5022433) B5022433
theorem B35715077 : Blo 2141435 35715077 := bstep (se 4 (by rfl) ⟨3348288, by rfl⟩ : syracuseStep 35715077 = 6696577) B6696577
theorem B23810051 : Blo 2141435 23810051 := bstep (se 1 (by rfl) ⟨17857538, by rfl⟩ : syracuseStep 23810051 = 35715077) B35715077
theorem B15873367 : Blo 2141435 15873367 := bstep (se 1 (by rfl) ⟨11905025, by rfl⟩ : syracuseStep 15873367 = 23810051) B23810051
theorem B21164489 : Blo 2141435 21164489 := bstep (se 2 (by rfl) ⟨7936683, by rfl⟩ : syracuseStep 21164489 = 15873367) B15873367
theorem B14109659 : Blo 2141435 14109659 := bstep (se 1 (by rfl) ⟨10582244, by rfl⟩ : syracuseStep 14109659 = 21164489) B21164489
theorem B9406439 : Blo 2141435 9406439 := bstep (se 1 (by rfl) ⟨7054829, by rfl⟩ : syracuseStep 9406439 = 14109659) B14109659
theorem B6270959 : Blo 2141435 6270959 := bstep (se 1 (by rfl) ⟨4703219, by rfl⟩ : syracuseStep 6270959 = 9406439) B9406439
theorem B4180639 : Blo 2141435 4180639 := bstep (se 1 (by rfl) ⟨3135479, by rfl⟩ : syracuseStep 4180639 = 6270959) B6270959
theorem B5574185 : Blo 2141435 5574185 := bstep (se 2 (by rfl) ⟨2090319, by rfl⟩ : syracuseStep 5574185 = 4180639) B4180639
theorem B3716123 : Blo 2141435 3716123 := bstep (se 1 (by rfl) ⟨2787092, by rfl⟩ : syracuseStep 3716123 = 5574185) B5574185
theorem B39638645 : Blo 2141435 39638645 := bstep (se 5 (by rfl) ⟨1858061, by rfl⟩ : syracuseStep 39638645 = 3716123) B3716123
theorem B26425763 : Blo 2141435 26425763 := bstep (se 1 (by rfl) ⟨19819322, by rfl⟩ : syracuseStep 26425763 = 39638645) B39638645
theorem B17617175 : Blo 2141435 17617175 := bstep (se 1 (by rfl) ⟨13212881, by rfl⟩ : syracuseStep 17617175 = 26425763) B26425763
theorem B11744783 : Blo 2141435 11744783 := bstep (se 1 (by rfl) ⟨8808587, by rfl⟩ : syracuseStep 11744783 = 17617175) B17617175
theorem B7829855 : Blo 2141435 7829855 := bstep (se 1 (by rfl) ⟨5872391, by rfl⟩ : syracuseStep 7829855 = 11744783) B11744783
theorem B5219903 : Blo 2141435 5219903 := bstep (se 1 (by rfl) ⟨3914927, by rfl⟩ : syracuseStep 5219903 = 7829855) B7829855
theorem B3479935 : Blo 2141435 3479935 := bstep (se 1 (by rfl) ⟨2609951, by rfl⟩ : syracuseStep 3479935 = 5219903) B5219903
theorem B4639913 : Blo 2141435 4639913 := bstep (se 2 (by rfl) ⟨1739967, by rfl⟩ : syracuseStep 4639913 = 3479935) B3479935
theorem B3093275 : Blo 2141435 3093275 := bstep (se 1 (by rfl) ⟨2319956, by rfl⟩ : syracuseStep 3093275 = 4639913) B4639913
theorem B8248733 : Blo 2141435 8248733 := bstep (se 3 (by rfl) ⟨1546637, by rfl⟩ : syracuseStep 8248733 = 3093275) B3093275
theorem B5499155 : Blo 2141435 5499155 := bstep (se 1 (by rfl) ⟨4124366, by rfl⟩ : syracuseStep 5499155 = 8248733) B8248733
theorem B3666103 : Blo 2141435 3666103 := bstep (se 1 (by rfl) ⟨2749577, by rfl⟩ : syracuseStep 3666103 = 5499155) B5499155
theorem B78210197 : Blo 2141435 78210197 := bstep (se 6 (by rfl) ⟨1833051, by rfl⟩ : syracuseStep 78210197 = 3666103) B3666103
theorem B52140131 : Blo 2141435 52140131 := bstep (se 1 (by rfl) ⟨39105098, by rfl⟩ : syracuseStep 52140131 = 78210197) B78210197
theorem B34760087 : Blo 2141435 34760087 := bstep (se 1 (by rfl) ⟨26070065, by rfl⟩ : syracuseStep 34760087 = 52140131) B52140131
theorem B23173391 : Blo 2141435 23173391 := bstep (se 1 (by rfl) ⟨17380043, by rfl⟩ : syracuseStep 23173391 = 34760087) B34760087
theorem B15448927 : Blo 2141435 15448927 := bstep (se 1 (by rfl) ⟨11586695, by rfl⟩ : syracuseStep 15448927 = 23173391) B23173391
theorem B20598569 : Blo 2141435 20598569 := bstep (se 2 (by rfl) ⟨7724463, by rfl⟩ : syracuseStep 20598569 = 15448927) B15448927
theorem B13732379 : Blo 2141435 13732379 := bstep (se 1 (by rfl) ⟨10299284, by rfl⟩ : syracuseStep 13732379 = 20598569) B20598569
theorem B9154919 : Blo 2141435 9154919 := bstep (se 1 (by rfl) ⟨6866189, by rfl⟩ : syracuseStep 9154919 = 13732379) B13732379
theorem B6103279 : Blo 2141435 6103279 := bstep (se 1 (by rfl) ⟨4577459, by rfl⟩ : syracuseStep 6103279 = 9154919) B9154919
theorem B8137705 : Blo 2141435 8137705 := bstep (se 2 (by rfl) ⟨3051639, by rfl⟩ : syracuseStep 8137705 = 6103279) B6103279
theorem B10850273 : Blo 2141435 10850273 := bstep (se 2 (by rfl) ⟨4068852, by rfl⟩ : syracuseStep 10850273 = 8137705) B8137705
theorem B7233515 : Blo 2141435 7233515 := bstep (se 1 (by rfl) ⟨5425136, by rfl⟩ : syracuseStep 7233515 = 10850273) B10850273
theorem B4822343 : Blo 2141435 4822343 := bstep (se 1 (by rfl) ⟨3616757, by rfl⟩ : syracuseStep 4822343 = 7233515) B7233515
theorem B3214895 : Blo 2141435 3214895 := bstep (se 1 (by rfl) ⟨2411171, by rfl⟩ : syracuseStep 3214895 = 4822343) B4822343
theorem B2143263 : Blo 2141435 2143263 := bstep (se 1 (by rfl) ⟨1607447, by rfl⟩ : syracuseStep 2143263 = 3214895) B3214895
theorem B3214901 : Blo 2141435 3214901 := bbase (se 5 (by rfl) ⟨150698, by rfl⟩ : syracuseStep 3214901 = 301397) (by norm_num)
theorem B2143267 : Blo 2141435 2143267 := bstep (se 1 (by rfl) ⟨1607450, by rfl⟩ : syracuseStep 2143267 = 3214901) B3214901
theorem B5425157 : Blo 2141435 5425157 := bbase (se 4 (by rfl) ⟨508608, by rfl⟩ : syracuseStep 5425157 = 1017217) (by norm_num)
theorem B3616771 : Blo 2141435 3616771 := bstep (se 1 (by rfl) ⟨2712578, by rfl⟩ : syracuseStep 3616771 = 5425157) B5425157
theorem B4822361 : Blo 2141435 4822361 := bstep (se 2 (by rfl) ⟨1808385, by rfl⟩ : syracuseStep 4822361 = 3616771) B3616771
theorem B3214907 : Blo 2141435 3214907 := bstep (se 1 (by rfl) ⟨2411180, by rfl⟩ : syracuseStep 3214907 = 4822361) B4822361
theorem B2143271 : Blo 2141435 2143271 := bstep (se 1 (by rfl) ⟨1607453, by rfl⟩ : syracuseStep 2143271 = 3214907) B3214907
theorem B2411185 : Blo 2141435 2411185 := bbase (se 2 (by rfl) ⟨904194, by rfl⟩ : syracuseStep 2411185 = 1808389) (by norm_num)
theorem B3214913 : Blo 2141435 3214913 := bstep (se 2 (by rfl) ⟨1205592, by rfl⟩ : syracuseStep 3214913 = 2411185) B2411185
theorem B2143275 : Blo 2141435 2143275 := bstep (se 1 (by rfl) ⟨1607456, by rfl⟩ : syracuseStep 2143275 = 3214913) B3214913
theorem B2574841 : Blo 2141435 2574841 := bbase (se 2 (by rfl) ⟨965565, by rfl⟩ : syracuseStep 2574841 = 1931131) (by norm_num)
theorem B3433121 : Blo 2141435 3433121 := bstep (se 2 (by rfl) ⟨1287420, by rfl⟩ : syracuseStep 3433121 = 2574841) B2574841
theorem B2288747 : Blo 2141435 2288747 := bstep (se 1 (by rfl) ⟨1716560, by rfl⟩ : syracuseStep 2288747 = 3433121) B3433121
theorem B6103325 : Blo 2141435 6103325 := bstep (se 3 (by rfl) ⟨1144373, by rfl⟩ : syracuseStep 6103325 = 2288747) B2288747
theorem B4068883 : Blo 2141435 4068883 := bstep (se 1 (by rfl) ⟨3051662, by rfl⟩ : syracuseStep 4068883 = 6103325) B6103325
theorem B5425177 : Blo 2141435 5425177 := bstep (se 2 (by rfl) ⟨2034441, by rfl⟩ : syracuseStep 5425177 = 4068883) B4068883
theorem B7233569 : Blo 2141435 7233569 := bstep (se 2 (by rfl) ⟨2712588, by rfl⟩ : syracuseStep 7233569 = 5425177) B5425177
theorem B4822379 : Blo 2141435 4822379 := bstep (se 1 (by rfl) ⟨3616784, by rfl⟩ : syracuseStep 4822379 = 7233569) B7233569
theorem B3214919 : Blo 2141435 3214919 := bstep (se 1 (by rfl) ⟨2411189, by rfl⟩ : syracuseStep 3214919 = 4822379) B4822379
theorem B2143279 : Blo 2141435 2143279 := bstep (se 1 (by rfl) ⟨1607459, by rfl⟩ : syracuseStep 2143279 = 3214919) B3214919
theorem B3214925 : Blo 2141435 3214925 := bbase (se 3 (by rfl) ⟨602798, by rfl⟩ : syracuseStep 3214925 = 1205597) (by norm_num)
theorem B2143283 : Blo 2141435 2143283 := bstep (se 1 (by rfl) ⟨1607462, by rfl⟩ : syracuseStep 2143283 = 3214925) B3214925
theorem B4822397 : Blo 2141435 4822397 := bbase (se 3 (by rfl) ⟨904199, by rfl⟩ : syracuseStep 4822397 = 1808399) (by norm_num)
theorem B3214931 : Blo 2141435 3214931 := bstep (se 1 (by rfl) ⟨2411198, by rfl⟩ : syracuseStep 3214931 = 4822397) B4822397
theorem B2143287 : Blo 2141435 2143287 := bstep (se 1 (by rfl) ⟨1607465, by rfl⟩ : syracuseStep 2143287 = 3214931) B3214931
theorem B3616805 : Blo 2141435 3616805 := bbase (se 4 (by rfl) ⟨339075, by rfl⟩ : syracuseStep 3616805 = 678151) (by norm_num)
theorem B2411203 : Blo 2141435 2411203 := bstep (se 1 (by rfl) ⟨1808402, by rfl⟩ : syracuseStep 2411203 = 3616805) B3616805
theorem B3214937 : Blo 2141435 3214937 := bstep (se 2 (by rfl) ⟨1205601, by rfl⟩ : syracuseStep 3214937 = 2411203) B2411203
theorem B2143291 : Blo 2141435 2143291 := bstep (se 1 (by rfl) ⟨1607468, by rfl⟩ : syracuseStep 2143291 = 3214937) B3214937
theorem B3051685 : Blo 2141435 3051685 := bbase (se 4 (by rfl) ⟨286095, by rfl⟩ : syracuseStep 3051685 = 572191) (by norm_num)
theorem B16275653 : Blo 2141435 16275653 := bstep (se 4 (by rfl) ⟨1525842, by rfl⟩ : syracuseStep 16275653 = 3051685) B3051685
theorem B10850435 : Blo 2141435 10850435 := bstep (se 1 (by rfl) ⟨8137826, by rfl⟩ : syracuseStep 10850435 = 16275653) B16275653
theorem B7233623 : Blo 2141435 7233623 := bstep (se 1 (by rfl) ⟨5425217, by rfl⟩ : syracuseStep 7233623 = 10850435) B10850435
theorem B4822415 : Blo 2141435 4822415 := bstep (se 1 (by rfl) ⟨3616811, by rfl⟩ : syracuseStep 4822415 = 7233623) B7233623
theorem B3214943 : Blo 2141435 3214943 := bstep (se 1 (by rfl) ⟨2411207, by rfl⟩ : syracuseStep 3214943 = 4822415) B4822415
theorem B2143295 : Blo 2141435 2143295 := bstep (se 1 (by rfl) ⟨1607471, by rfl⟩ : syracuseStep 2143295 = 3214943) B3214943
theorem B3214949 : Blo 2141435 3214949 := bbase (se 4 (by rfl) ⟨301401, by rfl⟩ : syracuseStep 3214949 = 602803) (by norm_num)
theorem B2143299 : Blo 2141435 2143299 := bstep (se 1 (by rfl) ⟨1607474, by rfl⟩ : syracuseStep 2143299 = 3214949) B3214949
theorem B2288773 : Blo 2141435 2288773 := bbase (se 4 (by rfl) ⟨214572, by rfl⟩ : syracuseStep 2288773 = 429145) (by norm_num)
theorem B3051697 : Blo 2141435 3051697 := bstep (se 2 (by rfl) ⟨1144386, by rfl⟩ : syracuseStep 3051697 = 2288773) B2288773
theorem B4068929 : Blo 2141435 4068929 := bstep (se 2 (by rfl) ⟨1525848, by rfl⟩ : syracuseStep 4068929 = 3051697) B3051697
theorem B2712619 : Blo 2141435 2712619 := bstep (se 1 (by rfl) ⟨2034464, by rfl⟩ : syracuseStep 2712619 = 4068929) B4068929
theorem B3616825 : Blo 2141435 3616825 := bstep (se 2 (by rfl) ⟨1356309, by rfl⟩ : syracuseStep 3616825 = 2712619) B2712619
theorem B4822433 : Blo 2141435 4822433 := bstep (se 2 (by rfl) ⟨1808412, by rfl⟩ : syracuseStep 4822433 = 3616825) B3616825
theorem B3214955 : Blo 2141435 3214955 := bstep (se 1 (by rfl) ⟨2411216, by rfl⟩ : syracuseStep 3214955 = 4822433) B4822433
theorem B2143303 : Blo 2141435 2143303 := bstep (se 1 (by rfl) ⟨1607477, by rfl⟩ : syracuseStep 2143303 = 3214955) B3214955
theorem B2411221 : Blo 2141435 2411221 := bbase (se 7 (by rfl) ⟨28256, by rfl⟩ : syracuseStep 2411221 = 56513) (by norm_num)
theorem B3214961 : Blo 2141435 3214961 := bstep (se 2 (by rfl) ⟨1205610, by rfl⟩ : syracuseStep 3214961 = 2411221) B2411221
theorem B2143307 : Blo 2141435 2143307 := bstep (se 1 (by rfl) ⟨1607480, by rfl⟩ : syracuseStep 2143307 = 3214961) B3214961
theorem B2712629 : Blo 2141435 2712629 := bbase (se 5 (by rfl) ⟨127154, by rfl⟩ : syracuseStep 2712629 = 254309) (by norm_num)
theorem B7233677 : Blo 2141435 7233677 := bstep (se 3 (by rfl) ⟨1356314, by rfl⟩ : syracuseStep 7233677 = 2712629) B2712629
theorem B4822451 : Blo 2141435 4822451 := bstep (se 1 (by rfl) ⟨3616838, by rfl⟩ : syracuseStep 4822451 = 7233677) B7233677
theorem B3214967 : Blo 2141435 3214967 := bstep (se 1 (by rfl) ⟨2411225, by rfl⟩ : syracuseStep 3214967 = 4822451) B4822451
theorem B2143311 : Blo 2141435 2143311 := bstep (se 1 (by rfl) ⟨1607483, by rfl⟩ : syracuseStep 2143311 = 3214967) B3214967
theorem B3214973 : Blo 2141435 3214973 := bbase (se 3 (by rfl) ⟨602807, by rfl⟩ : syracuseStep 3214973 = 1205615) (by norm_num)
theorem B2143315 : Blo 2141435 2143315 := bstep (se 1 (by rfl) ⟨1607486, by rfl⟩ : syracuseStep 2143315 = 3214973) B3214973
theorem B4822469 : Blo 2141435 4822469 := bbase (se 4 (by rfl) ⟨452106, by rfl⟩ : syracuseStep 4822469 = 904213) (by norm_num)
theorem B3214979 : Blo 2141435 3214979 := bstep (se 1 (by rfl) ⟨2411234, by rfl⟩ : syracuseStep 3214979 = 4822469) B4822469
theorem B2143319 : Blo 2141435 2143319 := bstep (se 1 (by rfl) ⟨1607489, by rfl⟩ : syracuseStep 2143319 = 3214979) B3214979
theorem B3915037 : Blo 2141435 3915037 := bbase (se 3 (by rfl) ⟨734069, by rfl⟩ : syracuseStep 3915037 = 1468139) (by norm_num)
theorem B5220049 : Blo 2141435 5220049 := bstep (se 2 (by rfl) ⟨1957518, by rfl⟩ : syracuseStep 5220049 = 3915037) B3915037
theorem B6960065 : Blo 2141435 6960065 := bstep (se 2 (by rfl) ⟨2610024, by rfl⟩ : syracuseStep 6960065 = 5220049) B5220049
theorem B18560173 : Blo 2141435 18560173 := bstep (se 3 (by rfl) ⟨3480032, by rfl⟩ : syracuseStep 18560173 = 6960065) B6960065
theorem B24746897 : Blo 2141435 24746897 := bstep (se 2 (by rfl) ⟨9280086, by rfl⟩ : syracuseStep 24746897 = 18560173) B18560173
theorem B16497931 : Blo 2141435 16497931 := bstep (se 1 (by rfl) ⟨12373448, by rfl⟩ : syracuseStep 16497931 = 24746897) B24746897
theorem B21997241 : Blo 2141435 21997241 := bstep (se 2 (by rfl) ⟨8248965, by rfl⟩ : syracuseStep 21997241 = 16497931) B16497931
theorem B14664827 : Blo 2141435 14664827 := bstep (se 1 (by rfl) ⟨10998620, by rfl⟩ : syracuseStep 14664827 = 21997241) B21997241
theorem B9776551 : Blo 2141435 9776551 := bstep (se 1 (by rfl) ⟨7332413, by rfl⟩ : syracuseStep 9776551 = 14664827) B14664827
theorem B13035401 : Blo 2141435 13035401 := bstep (se 2 (by rfl) ⟨4888275, by rfl⟩ : syracuseStep 13035401 = 9776551) B9776551
theorem B8690267 : Blo 2141435 8690267 := bstep (se 1 (by rfl) ⟨6517700, by rfl⟩ : syracuseStep 8690267 = 13035401) B13035401
theorem B23174045 : Blo 2141435 23174045 := bstep (se 3 (by rfl) ⟨4345133, by rfl⟩ : syracuseStep 23174045 = 8690267) B8690267
theorem B15449363 : Blo 2141435 15449363 := bstep (se 1 (by rfl) ⟨11587022, by rfl⟩ : syracuseStep 15449363 = 23174045) B23174045
theorem B10299575 : Blo 2141435 10299575 := bstep (se 1 (by rfl) ⟨7724681, by rfl⟩ : syracuseStep 10299575 = 15449363) B15449363
theorem B6866383 : Blo 2141435 6866383 := bstep (se 1 (by rfl) ⟨5149787, by rfl⟩ : syracuseStep 6866383 = 10299575) B10299575
theorem B9155177 : Blo 2141435 9155177 := bstep (se 2 (by rfl) ⟨3433191, by rfl⟩ : syracuseStep 9155177 = 6866383) B6866383
theorem B6103451 : Blo 2141435 6103451 := bstep (se 1 (by rfl) ⟨4577588, by rfl⟩ : syracuseStep 6103451 = 9155177) B9155177
theorem B4068967 : Blo 2141435 4068967 := bstep (se 1 (by rfl) ⟨3051725, by rfl⟩ : syracuseStep 4068967 = 6103451) B6103451
theorem B5425289 : Blo 2141435 5425289 := bstep (se 2 (by rfl) ⟨2034483, by rfl⟩ : syracuseStep 5425289 = 4068967) B4068967
theorem B3616859 : Blo 2141435 3616859 := bstep (se 1 (by rfl) ⟨2712644, by rfl⟩ : syracuseStep 3616859 = 5425289) B5425289
theorem B2411239 : Blo 2141435 2411239 := bstep (se 1 (by rfl) ⟨1808429, by rfl⟩ : syracuseStep 2411239 = 3616859) B3616859
theorem B3214985 : Blo 2141435 3214985 := bstep (se 2 (by rfl) ⟨1205619, by rfl⟩ : syracuseStep 3214985 = 2411239) B2411239
theorem B2143323 : Blo 2141435 2143323 := bstep (se 1 (by rfl) ⟨1607492, by rfl⟩ : syracuseStep 2143323 = 3214985) B3214985
theorem B10850597 : Blo 2141435 10850597 := bbase (se 4 (by rfl) ⟨1017243, by rfl⟩ : syracuseStep 10850597 = 2034487) (by norm_num)
theorem B7233731 : Blo 2141435 7233731 := bstep (se 1 (by rfl) ⟨5425298, by rfl⟩ : syracuseStep 7233731 = 10850597) B10850597
theorem B4822487 : Blo 2141435 4822487 := bstep (se 1 (by rfl) ⟨3616865, by rfl⟩ : syracuseStep 4822487 = 7233731) B7233731
theorem B3214991 : Blo 2141435 3214991 := bstep (se 1 (by rfl) ⟨2411243, by rfl⟩ : syracuseStep 3214991 = 4822487) B4822487
theorem B2143327 : Blo 2141435 2143327 := bstep (se 1 (by rfl) ⟨1607495, by rfl⟩ : syracuseStep 2143327 = 3214991) B3214991
theorem B3214997 : Blo 2141435 3214997 := bbase (se 6 (by rfl) ⟨75351, by rfl⟩ : syracuseStep 3214997 = 150703) (by norm_num)
theorem B2143331 : Blo 2141435 2143331 := bstep (se 1 (by rfl) ⟨1607498, by rfl⟩ : syracuseStep 2143331 = 3214997) B3214997
theorem B9909989 : Blo 2141435 9909989 := bbase (se 4 (by rfl) ⟨929061, by rfl⟩ : syracuseStep 9909989 = 1858123) (by norm_num)
theorem B105706549 : Blo 2141435 105706549 := bstep (se 5 (by rfl) ⟨4954994, by rfl⟩ : syracuseStep 105706549 = 9909989) B9909989
theorem B140942065 : Blo 2141435 140942065 := bstep (se 2 (by rfl) ⟨52853274, by rfl⟩ : syracuseStep 140942065 = 105706549) B105706549
theorem B187922753 : Blo 2141435 187922753 := bstep (se 2 (by rfl) ⟨70471032, by rfl⟩ : syracuseStep 187922753 = 140942065) B140942065
theorem B125281835 : Blo 2141435 125281835 := bstep (se 1 (by rfl) ⟨93961376, by rfl⟩ : syracuseStep 125281835 = 187922753) B187922753
theorem B83521223 : Blo 2141435 83521223 := bstep (se 1 (by rfl) ⟨62640917, by rfl⟩ : syracuseStep 83521223 = 125281835) B125281835
theorem B55680815 : Blo 2141435 55680815 := bstep (se 1 (by rfl) ⟨41760611, by rfl⟩ : syracuseStep 55680815 = 83521223) B83521223
theorem B148482173 : Blo 2141435 148482173 := bstep (se 3 (by rfl) ⟨27840407, by rfl⟩ : syracuseStep 148482173 = 55680815) B55680815
theorem B98988115 : Blo 2141435 98988115 := bstep (se 1 (by rfl) ⟨74241086, by rfl⟩ : syracuseStep 98988115 = 148482173) B148482173
theorem B131984153 : Blo 2141435 131984153 := bstep (se 2 (by rfl) ⟨49494057, by rfl⟩ : syracuseStep 131984153 = 98988115) B98988115
theorem B87989435 : Blo 2141435 87989435 := bstep (se 1 (by rfl) ⟨65992076, by rfl⟩ : syracuseStep 87989435 = 131984153) B131984153
theorem B58659623 : Blo 2141435 58659623 := bstep (se 1 (by rfl) ⟨43994717, by rfl⟩ : syracuseStep 58659623 = 87989435) B87989435
theorem B39106415 : Blo 2141435 39106415 := bstep (se 1 (by rfl) ⟨29329811, by rfl⟩ : syracuseStep 39106415 = 58659623) B58659623
theorem B26070943 : Blo 2141435 26070943 := bstep (se 1 (by rfl) ⟨19553207, by rfl⟩ : syracuseStep 26070943 = 39106415) B39106415
theorem B34761257 : Blo 2141435 34761257 := bstep (se 2 (by rfl) ⟨13035471, by rfl⟩ : syracuseStep 34761257 = 26070943) B26070943
theorem B23174171 : Blo 2141435 23174171 := bstep (se 1 (by rfl) ⟨17380628, by rfl⟩ : syracuseStep 23174171 = 34761257) B34761257
theorem B15449447 : Blo 2141435 15449447 := bstep (se 1 (by rfl) ⟨11587085, by rfl⟩ : syracuseStep 15449447 = 23174171) B23174171
theorem B10299631 : Blo 2141435 10299631 := bstep (se 1 (by rfl) ⟨7724723, by rfl⟩ : syracuseStep 10299631 = 15449447) B15449447
theorem B13732841 : Blo 2141435 13732841 := bstep (se 2 (by rfl) ⟨5149815, by rfl⟩ : syracuseStep 13732841 = 10299631) B10299631
theorem B9155227 : Blo 2141435 9155227 := bstep (se 1 (by rfl) ⟨6866420, by rfl⟩ : syracuseStep 9155227 = 13732841) B13732841
theorem B12206969 : Blo 2141435 12206969 := bstep (se 2 (by rfl) ⟨4577613, by rfl⟩ : syracuseStep 12206969 = 9155227) B9155227
theorem B8137979 : Blo 2141435 8137979 := bstep (se 1 (by rfl) ⟨6103484, by rfl⟩ : syracuseStep 8137979 = 12206969) B12206969
theorem B5425319 : Blo 2141435 5425319 := bstep (se 1 (by rfl) ⟨4068989, by rfl⟩ : syracuseStep 5425319 = 8137979) B8137979
theorem B3616879 : Blo 2141435 3616879 := bstep (se 1 (by rfl) ⟨2712659, by rfl⟩ : syracuseStep 3616879 = 5425319) B5425319
theorem B4822505 : Blo 2141435 4822505 := bstep (se 2 (by rfl) ⟨1808439, by rfl⟩ : syracuseStep 4822505 = 3616879) B3616879
theorem B3215003 : Blo 2141435 3215003 := bstep (se 1 (by rfl) ⟨2411252, by rfl⟩ : syracuseStep 3215003 = 4822505) B4822505
theorem B2143335 : Blo 2141435 2143335 := bstep (se 1 (by rfl) ⟨1607501, by rfl⟩ : syracuseStep 2143335 = 3215003) B3215003
theorem B2411257 : Blo 2141435 2411257 := bbase (se 2 (by rfl) ⟨904221, by rfl⟩ : syracuseStep 2411257 = 1808443) (by norm_num)
theorem B3215009 : Blo 2141435 3215009 := bstep (se 2 (by rfl) ⟨1205628, by rfl⟩ : syracuseStep 3215009 = 2411257) B2411257
theorem B2143339 : Blo 2141435 2143339 := bstep (se 1 (by rfl) ⟨1607504, by rfl⟩ : syracuseStep 2143339 = 3215009) B3215009
theorem B2444161 : Blo 2141435 2444161 := bbase (se 2 (by rfl) ⟨916560, by rfl⟩ : syracuseStep 2444161 = 1833121) (by norm_num)
theorem B3258881 : Blo 2141435 3258881 := bstep (se 2 (by rfl) ⟨1222080, by rfl⟩ : syracuseStep 3258881 = 2444161) B2444161
theorem B2172587 : Blo 2141435 2172587 := bstep (se 1 (by rfl) ⟨1629440, by rfl⟩ : syracuseStep 2172587 = 3258881) B3258881
theorem B5793565 : Blo 2141435 5793565 := bstep (se 3 (by rfl) ⟨1086293, by rfl⟩ : syracuseStep 5793565 = 2172587) B2172587
theorem B7724753 : Blo 2141435 7724753 := bstep (se 2 (by rfl) ⟨2896782, by rfl⟩ : syracuseStep 7724753 = 5793565) B5793565
theorem B5149835 : Blo 2141435 5149835 := bstep (se 1 (by rfl) ⟨3862376, by rfl⟩ : syracuseStep 5149835 = 7724753) B7724753
theorem B3433223 : Blo 2141435 3433223 := bstep (se 1 (by rfl) ⟨2574917, by rfl⟩ : syracuseStep 3433223 = 5149835) B5149835
theorem B9155261 : Blo 2141435 9155261 := bstep (se 3 (by rfl) ⟨1716611, by rfl⟩ : syracuseStep 9155261 = 3433223) B3433223
theorem B6103507 : Blo 2141435 6103507 := bstep (se 1 (by rfl) ⟨4577630, by rfl⟩ : syracuseStep 6103507 = 9155261) B9155261
theorem B8138009 : Blo 2141435 8138009 := bstep (se 2 (by rfl) ⟨3051753, by rfl⟩ : syracuseStep 8138009 = 6103507) B6103507
theorem B5425339 : Blo 2141435 5425339 := bstep (se 1 (by rfl) ⟨4069004, by rfl⟩ : syracuseStep 5425339 = 8138009) B8138009
theorem B7233785 : Blo 2141435 7233785 := bstep (se 2 (by rfl) ⟨2712669, by rfl⟩ : syracuseStep 7233785 = 5425339) B5425339
theorem B4822523 : Blo 2141435 4822523 := bstep (se 1 (by rfl) ⟨3616892, by rfl⟩ : syracuseStep 4822523 = 7233785) B7233785
theorem B3215015 : Blo 2141435 3215015 := bstep (se 1 (by rfl) ⟨2411261, by rfl⟩ : syracuseStep 3215015 = 4822523) B4822523
theorem B2143343 : Blo 2141435 2143343 := bstep (se 1 (by rfl) ⟨1607507, by rfl⟩ : syracuseStep 2143343 = 3215015) B3215015
theorem B3215021 : Blo 2141435 3215021 := bbase (se 3 (by rfl) ⟨602816, by rfl⟩ : syracuseStep 3215021 = 1205633) (by norm_num)
theorem B2143347 : Blo 2141435 2143347 := bstep (se 1 (by rfl) ⟨1607510, by rfl⟩ : syracuseStep 2143347 = 3215021) B3215021
theorem B4822541 : Blo 2141435 4822541 := bbase (se 3 (by rfl) ⟨904226, by rfl⟩ : syracuseStep 4822541 = 1808453) (by norm_num)
theorem B3215027 : Blo 2141435 3215027 := bstep (se 1 (by rfl) ⟨2411270, by rfl⟩ : syracuseStep 3215027 = 4822541) B4822541
theorem B2143351 : Blo 2141435 2143351 := bstep (se 1 (by rfl) ⟨1607513, by rfl⟩ : syracuseStep 2143351 = 3215027) B3215027
theorem B2712685 : Blo 2141435 2712685 := bbase (se 3 (by rfl) ⟨508628, by rfl⟩ : syracuseStep 2712685 = 1017257) (by norm_num)
theorem B3616913 : Blo 2141435 3616913 := bstep (se 2 (by rfl) ⟨1356342, by rfl⟩ : syracuseStep 3616913 = 2712685) B2712685
theorem B2411275 : Blo 2141435 2411275 := bstep (se 1 (by rfl) ⟨1808456, by rfl⟩ : syracuseStep 2411275 = 3616913) B3616913
theorem B3215033 : Blo 2141435 3215033 := bstep (se 2 (by rfl) ⟨1205637, by rfl⟩ : syracuseStep 3215033 = 2411275) B2411275
theorem B2143355 : Blo 2141435 2143355 := bstep (se 1 (by rfl) ⟨1607516, by rfl⟩ : syracuseStep 2143355 = 3215033) B3215033
theorem B6960181 : Blo 2141435 6960181 := bbase (se 5 (by rfl) ⟨326258, by rfl⟩ : syracuseStep 6960181 = 652517) (by norm_num)
theorem B9280241 : Blo 2141435 9280241 := bstep (se 2 (by rfl) ⟨3480090, by rfl⟩ : syracuseStep 9280241 = 6960181) B6960181
theorem B6186827 : Blo 2141435 6186827 := bstep (se 1 (by rfl) ⟨4640120, by rfl⟩ : syracuseStep 6186827 = 9280241) B9280241
theorem B16498205 : Blo 2141435 16498205 := bstep (se 3 (by rfl) ⟨3093413, by rfl⟩ : syracuseStep 16498205 = 6186827) B6186827
theorem B10998803 : Blo 2141435 10998803 := bstep (se 1 (by rfl) ⟨8249102, by rfl⟩ : syracuseStep 10998803 = 16498205) B16498205
theorem B7332535 : Blo 2141435 7332535 := bstep (se 1 (by rfl) ⟨5499401, by rfl⟩ : syracuseStep 7332535 = 10998803) B10998803
theorem B9776713 : Blo 2141435 9776713 := bstep (se 2 (by rfl) ⟨3666267, by rfl⟩ : syracuseStep 9776713 = 7332535) B7332535
theorem B13035617 : Blo 2141435 13035617 := bstep (se 2 (by rfl) ⟨4888356, by rfl⟩ : syracuseStep 13035617 = 9776713) B9776713
theorem B8690411 : Blo 2141435 8690411 := bstep (se 1 (by rfl) ⟨6517808, by rfl⟩ : syracuseStep 8690411 = 13035617) B13035617
theorem B5793607 : Blo 2141435 5793607 := bstep (se 1 (by rfl) ⟨4345205, by rfl⟩ : syracuseStep 5793607 = 8690411) B8690411
theorem B7724809 : Blo 2141435 7724809 := bstep (se 2 (by rfl) ⟨2896803, by rfl⟩ : syracuseStep 7724809 = 5793607) B5793607
theorem B10299745 : Blo 2141435 10299745 := bstep (se 2 (by rfl) ⟨3862404, by rfl⟩ : syracuseStep 10299745 = 7724809) B7724809
theorem B13732993 : Blo 2141435 13732993 := bstep (se 2 (by rfl) ⟨5149872, by rfl⟩ : syracuseStep 13732993 = 10299745) B10299745
theorem B18310657 : Blo 2141435 18310657 := bstep (se 2 (by rfl) ⟨6866496, by rfl⟩ : syracuseStep 18310657 = 13732993) B13732993
theorem B24414209 : Blo 2141435 24414209 := bstep (se 2 (by rfl) ⟨9155328, by rfl⟩ : syracuseStep 24414209 = 18310657) B18310657
theorem B16276139 : Blo 2141435 16276139 := bstep (se 1 (by rfl) ⟨12207104, by rfl⟩ : syracuseStep 16276139 = 24414209) B24414209
theorem B10850759 : Blo 2141435 10850759 := bstep (se 1 (by rfl) ⟨8138069, by rfl⟩ : syracuseStep 10850759 = 16276139) B16276139
theorem B7233839 : Blo 2141435 7233839 := bstep (se 1 (by rfl) ⟨5425379, by rfl⟩ : syracuseStep 7233839 = 10850759) B10850759
theorem B4822559 : Blo 2141435 4822559 := bstep (se 1 (by rfl) ⟨3616919, by rfl⟩ : syracuseStep 4822559 = 7233839) B7233839
theorem B3215039 : Blo 2141435 3215039 := bstep (se 1 (by rfl) ⟨2411279, by rfl⟩ : syracuseStep 3215039 = 4822559) B4822559
theorem B2143359 : Blo 2141435 2143359 := bstep (se 1 (by rfl) ⟨1607519, by rfl⟩ : syracuseStep 2143359 = 3215039) B3215039
theorem B3215045 : Blo 2141435 3215045 := bbase (se 4 (by rfl) ⟨301410, by rfl⟩ : syracuseStep 3215045 = 602821) (by norm_num)
theorem B2143363 : Blo 2141435 2143363 := bstep (se 1 (by rfl) ⟨1607522, by rfl⟩ : syracuseStep 2143363 = 3215045) B3215045
theorem B3616933 : Blo 2141435 3616933 := bbase (se 4 (by rfl) ⟨339087, by rfl⟩ : syracuseStep 3616933 = 678175) (by norm_num)
theorem B4822577 : Blo 2141435 4822577 := bstep (se 2 (by rfl) ⟨1808466, by rfl⟩ : syracuseStep 4822577 = 3616933) B3616933
theorem B3215051 : Blo 2141435 3215051 := bstep (se 1 (by rfl) ⟨2411288, by rfl⟩ : syracuseStep 3215051 = 4822577) B4822577
theorem B2143367 : Blo 2141435 2143367 := bstep (se 1 (by rfl) ⟨1607525, by rfl⟩ : syracuseStep 2143367 = 3215051) B3215051
theorem B2411293 : Blo 2141435 2411293 := bbase (se 3 (by rfl) ⟨452117, by rfl⟩ : syracuseStep 2411293 = 904235) (by norm_num)
theorem B3215057 : Blo 2141435 3215057 := bstep (se 2 (by rfl) ⟨1205646, by rfl⟩ : syracuseStep 3215057 = 2411293) B2411293
theorem B2143371 : Blo 2141435 2143371 := bstep (se 1 (by rfl) ⟨1607528, by rfl⟩ : syracuseStep 2143371 = 3215057) B3215057
theorem B7233893 : Blo 2141435 7233893 := bbase (se 4 (by rfl) ⟨678177, by rfl⟩ : syracuseStep 7233893 = 1356355) (by norm_num)
theorem B4822595 : Blo 2141435 4822595 := bstep (se 1 (by rfl) ⟨3616946, by rfl⟩ : syracuseStep 4822595 = 7233893) B7233893
theorem B3215063 : Blo 2141435 3215063 := bstep (se 1 (by rfl) ⟨2411297, by rfl⟩ : syracuseStep 3215063 = 4822595) B4822595
theorem B2143375 : Blo 2141435 2143375 := bstep (se 1 (by rfl) ⟨1607531, by rfl⟩ : syracuseStep 2143375 = 3215063) B3215063
theorem B3215069 : Blo 2141435 3215069 := bbase (se 3 (by rfl) ⟨602825, by rfl⟩ : syracuseStep 3215069 = 1205651) (by norm_num)
theorem B2143379 : Blo 2141435 2143379 := bstep (se 1 (by rfl) ⟨1607534, by rfl⟩ : syracuseStep 2143379 = 3215069) B3215069
theorem B4822613 : Blo 2141435 4822613 := bbase (se 8 (by rfl) ⟨28257, by rfl⟩ : syracuseStep 4822613 = 56515) (by norm_num)
theorem B3215075 : Blo 2141435 3215075 := bstep (se 1 (by rfl) ⟨2411306, by rfl⟩ : syracuseStep 3215075 = 4822613) B4822613
theorem B2143383 : Blo 2141435 2143383 := bstep (se 1 (by rfl) ⟨1607537, by rfl⟩ : syracuseStep 2143383 = 3215075) B3215075
theorem B4577725 : Blo 2141435 4577725 := bbase (se 3 (by rfl) ⟨858323, by rfl⟩ : syracuseStep 4577725 = 1716647) (by norm_num)
theorem B6103633 : Blo 2141435 6103633 := bstep (se 2 (by rfl) ⟨2288862, by rfl⟩ : syracuseStep 6103633 = 4577725) B4577725
theorem B8138177 : Blo 2141435 8138177 := bstep (se 2 (by rfl) ⟨3051816, by rfl⟩ : syracuseStep 8138177 = 6103633) B6103633
theorem B5425451 : Blo 2141435 5425451 := bstep (se 1 (by rfl) ⟨4069088, by rfl⟩ : syracuseStep 5425451 = 8138177) B8138177
theorem B3616967 : Blo 2141435 3616967 := bstep (se 1 (by rfl) ⟨2712725, by rfl⟩ : syracuseStep 3616967 = 5425451) B5425451
theorem B2411311 : Blo 2141435 2411311 := bstep (se 1 (by rfl) ⟨1808483, by rfl⟩ : syracuseStep 2411311 = 3616967) B3616967
theorem B3215081 : Blo 2141435 3215081 := bstep (se 2 (by rfl) ⟨1205655, by rfl⟩ : syracuseStep 3215081 = 2411311) B2411311
theorem B2143387 : Blo 2141435 2143387 := bstep (se 1 (by rfl) ⟨1607540, by rfl⟩ : syracuseStep 2143387 = 3215081) B3215081
theorem B19553717 : Blo 2141435 19553717 := bbase (se 5 (by rfl) ⟨916580, by rfl⟩ : syracuseStep 19553717 = 1833161) (by norm_num)
theorem B13035811 : Blo 2141435 13035811 := bstep (se 1 (by rfl) ⟨9776858, by rfl⟩ : syracuseStep 13035811 = 19553717) B19553717
theorem B17381081 : Blo 2141435 17381081 := bstep (se 2 (by rfl) ⟨6517905, by rfl⟩ : syracuseStep 17381081 = 13035811) B13035811
theorem B11587387 : Blo 2141435 11587387 := bstep (se 1 (by rfl) ⟨8690540, by rfl⟩ : syracuseStep 11587387 = 17381081) B17381081
theorem B15449849 : Blo 2141435 15449849 := bstep (se 2 (by rfl) ⟨5793693, by rfl⟩ : syracuseStep 15449849 = 11587387) B11587387
theorem B10299899 : Blo 2141435 10299899 := bstep (se 1 (by rfl) ⟨7724924, by rfl⟩ : syracuseStep 10299899 = 15449849) B15449849
theorem B27466397 : Blo 2141435 27466397 := bstep (se 3 (by rfl) ⟨5149949, by rfl⟩ : syracuseStep 27466397 = 10299899) B10299899
theorem B18310931 : Blo 2141435 18310931 := bstep (se 1 (by rfl) ⟨13733198, by rfl⟩ : syracuseStep 18310931 = 27466397) B27466397
theorem B12207287 : Blo 2141435 12207287 := bstep (se 1 (by rfl) ⟨9155465, by rfl⟩ : syracuseStep 12207287 = 18310931) B18310931
theorem B8138191 : Blo 2141435 8138191 := bstep (se 1 (by rfl) ⟨6103643, by rfl⟩ : syracuseStep 8138191 = 12207287) B12207287
theorem B10850921 : Blo 2141435 10850921 := bstep (se 2 (by rfl) ⟨4069095, by rfl⟩ : syracuseStep 10850921 = 8138191) B8138191
theorem B7233947 : Blo 2141435 7233947 := bstep (se 1 (by rfl) ⟨5425460, by rfl⟩ : syracuseStep 7233947 = 10850921) B10850921
theorem B4822631 : Blo 2141435 4822631 := bstep (se 1 (by rfl) ⟨3616973, by rfl⟩ : syracuseStep 4822631 = 7233947) B7233947
theorem B3215087 : Blo 2141435 3215087 := bstep (se 1 (by rfl) ⟨2411315, by rfl⟩ : syracuseStep 3215087 = 4822631) B4822631
theorem B2143391 : Blo 2141435 2143391 := bstep (se 1 (by rfl) ⟨1607543, by rfl⟩ : syracuseStep 2143391 = 3215087) B3215087
theorem B3215093 : Blo 2141435 3215093 := bbase (se 5 (by rfl) ⟨150707, by rfl⟩ : syracuseStep 3215093 = 301415) (by norm_num)
theorem B2143395 : Blo 2141435 2143395 := bstep (se 1 (by rfl) ⟨1607546, by rfl⟩ : syracuseStep 2143395 = 3215093) B3215093
theorem B2574985 : Blo 2141435 2574985 := bbase (se 2 (by rfl) ⟨965619, by rfl⟩ : syracuseStep 2574985 = 1931239) (by norm_num)
theorem B3433313 : Blo 2141435 3433313 := bstep (se 2 (by rfl) ⟨1287492, by rfl⟩ : syracuseStep 3433313 = 2574985) B2574985
theorem B9155501 : Blo 2141435 9155501 := bstep (se 3 (by rfl) ⟨1716656, by rfl⟩ : syracuseStep 9155501 = 3433313) B3433313
theorem B6103667 : Blo 2141435 6103667 := bstep (se 1 (by rfl) ⟨4577750, by rfl⟩ : syracuseStep 6103667 = 9155501) B9155501
theorem B4069111 : Blo 2141435 4069111 := bstep (se 1 (by rfl) ⟨3051833, by rfl⟩ : syracuseStep 4069111 = 6103667) B6103667
theorem B5425481 : Blo 2141435 5425481 := bstep (se 2 (by rfl) ⟨2034555, by rfl⟩ : syracuseStep 5425481 = 4069111) B4069111
theorem B3616987 : Blo 2141435 3616987 := bstep (se 1 (by rfl) ⟨2712740, by rfl⟩ : syracuseStep 3616987 = 5425481) B5425481
theorem B4822649 : Blo 2141435 4822649 := bstep (se 2 (by rfl) ⟨1808493, by rfl⟩ : syracuseStep 4822649 = 3616987) B3616987
theorem B3215099 : Blo 2141435 3215099 := bstep (se 1 (by rfl) ⟨2411324, by rfl⟩ : syracuseStep 3215099 = 4822649) B4822649
theorem B2143399 : Blo 2141435 2143399 := bstep (se 1 (by rfl) ⟨1607549, by rfl⟩ : syracuseStep 2143399 = 3215099) B3215099
theorem B2411329 : Blo 2141435 2411329 := bbase (se 2 (by rfl) ⟨904248, by rfl⟩ : syracuseStep 2411329 = 1808497) (by norm_num)
theorem B3215105 : Blo 2141435 3215105 := bstep (se 2 (by rfl) ⟨1205664, by rfl⟩ : syracuseStep 3215105 = 2411329) B2411329
theorem B2143403 : Blo 2141435 2143403 := bstep (se 1 (by rfl) ⟨1607552, by rfl⟩ : syracuseStep 2143403 = 3215105) B3215105
theorem B5425501 : Blo 2141435 5425501 := bbase (se 3 (by rfl) ⟨1017281, by rfl⟩ : syracuseStep 5425501 = 2034563) (by norm_num)
theorem B7234001 : Blo 2141435 7234001 := bstep (se 2 (by rfl) ⟨2712750, by rfl⟩ : syracuseStep 7234001 = 5425501) B5425501
theorem B4822667 : Blo 2141435 4822667 := bstep (se 1 (by rfl) ⟨3617000, by rfl⟩ : syracuseStep 4822667 = 7234001) B7234001
theorem B3215111 : Blo 2141435 3215111 := bstep (se 1 (by rfl) ⟨2411333, by rfl⟩ : syracuseStep 3215111 = 4822667) B4822667
theorem B2143407 : Blo 2141435 2143407 := bstep (se 1 (by rfl) ⟨1607555, by rfl⟩ : syracuseStep 2143407 = 3215111) B3215111
theorem B3215117 : Blo 2141435 3215117 := bbase (se 3 (by rfl) ⟨602834, by rfl⟩ : syracuseStep 3215117 = 1205669) (by norm_num)
theorem B2143411 : Blo 2141435 2143411 := bstep (se 1 (by rfl) ⟨1607558, by rfl⟩ : syracuseStep 2143411 = 3215117) B3215117
theorem B4822685 : Blo 2141435 4822685 := bbase (se 3 (by rfl) ⟨904253, by rfl⟩ : syracuseStep 4822685 = 1808507) (by norm_num)
theorem B3215123 : Blo 2141435 3215123 := bstep (se 1 (by rfl) ⟨2411342, by rfl⟩ : syracuseStep 3215123 = 4822685) B4822685
theorem B2143415 : Blo 2141435 2143415 := bstep (se 1 (by rfl) ⟨1607561, by rfl⟩ : syracuseStep 2143415 = 3215123) B3215123
theorem B3617021 : Blo 2141435 3617021 := bbase (se 3 (by rfl) ⟨678191, by rfl⟩ : syracuseStep 3617021 = 1356383) (by norm_num)
theorem B2411347 : Blo 2141435 2411347 := bstep (se 1 (by rfl) ⟨1808510, by rfl⟩ : syracuseStep 2411347 = 3617021) B3617021
theorem B3215129 : Blo 2141435 3215129 := bstep (se 2 (by rfl) ⟨1205673, by rfl⟩ : syracuseStep 3215129 = 2411347) B2411347
theorem B2143419 : Blo 2141435 2143419 := bstep (se 1 (by rfl) ⟨1607564, by rfl⟩ : syracuseStep 2143419 = 3215129) B3215129
theorem B5793781 : Blo 2141435 5793781 := bbase (se 5 (by rfl) ⟨271583, by rfl⟩ : syracuseStep 5793781 = 543167) (by norm_num)
theorem B7725041 : Blo 2141435 7725041 := bstep (se 2 (by rfl) ⟨2896890, by rfl⟩ : syracuseStep 7725041 = 5793781) B5793781
theorem B5150027 : Blo 2141435 5150027 := bstep (se 1 (by rfl) ⟨3862520, by rfl⟩ : syracuseStep 5150027 = 7725041) B7725041
theorem B3433351 : Blo 2141435 3433351 := bstep (se 1 (by rfl) ⟨2575013, by rfl⟩ : syracuseStep 3433351 = 5150027) B5150027
theorem B4577801 : Blo 2141435 4577801 := bstep (se 2 (by rfl) ⟨1716675, by rfl⟩ : syracuseStep 4577801 = 3433351) B3433351
theorem B12207469 : Blo 2141435 12207469 := bstep (se 3 (by rfl) ⟨2288900, by rfl⟩ : syracuseStep 12207469 = 4577801) B4577801
theorem B16276625 : Blo 2141435 16276625 := bstep (se 2 (by rfl) ⟨6103734, by rfl⟩ : syracuseStep 16276625 = 12207469) B12207469
theorem B10851083 : Blo 2141435 10851083 := bstep (se 1 (by rfl) ⟨8138312, by rfl⟩ : syracuseStep 10851083 = 16276625) B16276625
theorem B7234055 : Blo 2141435 7234055 := bstep (se 1 (by rfl) ⟨5425541, by rfl⟩ : syracuseStep 7234055 = 10851083) B10851083
theorem B4822703 : Blo 2141435 4822703 := bstep (se 1 (by rfl) ⟨3617027, by rfl⟩ : syracuseStep 4822703 = 7234055) B7234055
theorem B3215135 : Blo 2141435 3215135 := bstep (se 1 (by rfl) ⟨2411351, by rfl⟩ : syracuseStep 3215135 = 4822703) B4822703
theorem B2143423 : Blo 2141435 2143423 := bstep (se 1 (by rfl) ⟨1607567, by rfl⟩ : syracuseStep 2143423 = 3215135) B3215135
theorem B3215141 : Blo 2141435 3215141 := bbase (se 4 (by rfl) ⟨301419, by rfl⟩ : syracuseStep 3215141 = 602839) (by norm_num)
theorem B2143427 : Blo 2141435 2143427 := bstep (se 1 (by rfl) ⟨1607570, by rfl⟩ : syracuseStep 2143427 = 3215141) B3215141
theorem B2712781 : Blo 2141435 2712781 := bbase (se 3 (by rfl) ⟨508646, by rfl⟩ : syracuseStep 2712781 = 1017293) (by norm_num)
theorem B3617041 : Blo 2141435 3617041 := bstep (se 2 (by rfl) ⟨1356390, by rfl⟩ : syracuseStep 3617041 = 2712781) B2712781
theorem B4822721 : Blo 2141435 4822721 := bstep (se 2 (by rfl) ⟨1808520, by rfl⟩ : syracuseStep 4822721 = 3617041) B3617041
theorem B3215147 : Blo 2141435 3215147 := bstep (se 1 (by rfl) ⟨2411360, by rfl⟩ : syracuseStep 3215147 = 4822721) B4822721
theorem B2143431 : Blo 2141435 2143431 := bstep (se 1 (by rfl) ⟨1607573, by rfl⟩ : syracuseStep 2143431 = 3215147) B3215147
theorem B2411365 : Blo 2141435 2411365 := bbase (se 4 (by rfl) ⟨226065, by rfl⟩ : syracuseStep 2411365 = 452131) (by norm_num)
theorem B3215153 : Blo 2141435 3215153 := bstep (se 2 (by rfl) ⟨1205682, by rfl⟩ : syracuseStep 3215153 = 2411365) B2411365
theorem B2143435 : Blo 2141435 2143435 := bstep (se 1 (by rfl) ⟨1607576, by rfl⟩ : syracuseStep 2143435 = 3215153) B3215153
theorem C0 (j : ℕ) (h1 : 535358 ≤ j) (h2 : j ≤ 535858) : Blo 2141435 (4 * j + 3) := by
  interval_cases j
  · exact B2141435
  · exact B2141439
  · exact B2141443
  · exact B2141447
  · exact B2141451
  · exact B2141455
  · exact B2141459
  · exact B2141463
  · exact B2141467
  · exact B2141471
  · exact B2141475
  · exact B2141479
  · exact B2141483
  · exact B2141487
  · exact B2141491
  · exact B2141495
  · exact B2141499
  · exact B2141503
  · exact B2141507
  · exact B2141511
  · exact B2141515
  · exact B2141519
  · exact B2141523
  · exact B2141527
  · exact B2141531
  · exact B2141535
  · exact B2141539
  · exact B2141543
  · exact B2141547
  · exact B2141551
  · exact B2141555
  · exact B2141559
  · exact B2141563
  · exact B2141567
  · exact B2141571
  · exact B2141575
  · exact B2141579
  · exact B2141583
  · exact B2141587
  · exact B2141591
  · exact B2141595
  · exact B2141599
  · exact B2141603
  · exact B2141607
  · exact B2141611
  · exact B2141615
  · exact B2141619
  · exact B2141623
  · exact B2141627
  · exact B2141631
  · exact B2141635
  · exact B2141639
  · exact B2141643
  · exact B2141647
  · exact B2141651
  · exact B2141655
  · exact B2141659
  · exact B2141663
  · exact B2141667
  · exact B2141671
  · exact B2141675
  · exact B2141679
  · exact B2141683
  · exact B2141687
  · exact B2141691
  · exact B2141695
  · exact B2141699
  · exact B2141703
  · exact B2141707
  · exact B2141711
  · exact B2141715
  · exact B2141719
  · exact B2141723
  · exact B2141727
  · exact B2141731
  · exact B2141735
  · exact B2141739
  · exact B2141743
  · exact B2141747
  · exact B2141751
  · exact B2141755
  · exact B2141759
  · exact B2141763
  · exact B2141767
  · exact B2141771
  · exact B2141775
  · exact B2141779
  · exact B2141783
  · exact B2141787
  · exact B2141791
  · exact B2141795
  · exact B2141799
  · exact B2141803
  · exact B2141807
  · exact B2141811
  · exact B2141815
  · exact B2141819
  · exact B2141823
  · exact B2141827
  · exact B2141831
  · exact B2141835
  · exact B2141839
  · exact B2141843
  · exact B2141847
  · exact B2141851
  · exact B2141855
  · exact B2141859
  · exact B2141863
  · exact B2141867
  · exact B2141871
  · exact B2141875
  · exact B2141879
  · exact B2141883
  · exact B2141887
  · exact B2141891
  · exact B2141895
  · exact B2141899
  · exact B2141903
  · exact B2141907
  · exact B2141911
  · exact B2141915
  · exact B2141919
  · exact B2141923
  · exact B2141927
  · exact B2141931
  · exact B2141935
  · exact B2141939
  · exact B2141943
  · exact B2141947
  · exact B2141951
  · exact B2141955
  · exact B2141959
  · exact B2141963
  · exact B2141967
  · exact B2141971
  · exact B2141975
  · exact B2141979
  · exact B2141983
  · exact B2141987
  · exact B2141991
  · exact B2141995
  · exact B2141999
  · exact B2142003
  · exact B2142007
  · exact B2142011
  · exact B2142015
  · exact B2142019
  · exact B2142023
  · exact B2142027
  · exact B2142031
  · exact B2142035
  · exact B2142039
  · exact B2142043
  · exact B2142047
  · exact B2142051
  · exact B2142055
  · exact B2142059
  · exact B2142063
  · exact B2142067
  · exact B2142071
  · exact B2142075
  · exact B2142079
  · exact B2142083
  · exact B2142087
  · exact B2142091
  · exact B2142095
  · exact B2142099
  · exact B2142103
  · exact B2142107
  · exact B2142111
  · exact B2142115
  · exact B2142119
  · exact B2142123
  · exact B2142127
  · exact B2142131
  · exact B2142135
  · exact B2142139
  · exact B2142143
  · exact B2142147
  · exact B2142151
  · exact B2142155
  · exact B2142159
  · exact B2142163
  · exact B2142167
  · exact B2142171
  · exact B2142175
  · exact B2142179
  · exact B2142183
  · exact B2142187
  · exact B2142191
  · exact B2142195
  · exact B2142199
  · exact B2142203
  · exact B2142207
  · exact B2142211
  · exact B2142215
  · exact B2142219
  · exact B2142223
  · exact B2142227
  · exact B2142231
  · exact B2142235
  · exact B2142239
  · exact B2142243
  · exact B2142247
  · exact B2142251
  · exact B2142255
  · exact B2142259
  · exact B2142263
  · exact B2142267
  · exact B2142271
  · exact B2142275
  · exact B2142279
  · exact B2142283
  · exact B2142287
  · exact B2142291
  · exact B2142295
  · exact B2142299
  · exact B2142303
  · exact B2142307
  · exact B2142311
  · exact B2142315
  · exact B2142319
  · exact B2142323
  · exact B2142327
  · exact B2142331
  · exact B2142335
  · exact B2142339
  · exact B2142343
  · exact B2142347
  · exact B2142351
  · exact B2142355
  · exact B2142359
  · exact B2142363
  · exact B2142367
  · exact B2142371
  · exact B2142375
  · exact B2142379
  · exact B2142383
  · exact B2142387
  · exact B2142391
  · exact B2142395
  · exact B2142399
  · exact B2142403
  · exact B2142407
  · exact B2142411
  · exact B2142415
  · exact B2142419
  · exact B2142423
  · exact B2142427
  · exact B2142431
  · exact B2142435
  · exact B2142439
  · exact B2142443
  · exact B2142447
  · exact B2142451
  · exact B2142455
  · exact B2142459
  · exact B2142463
  · exact B2142467
  · exact B2142471
  · exact B2142475
  · exact B2142479
  · exact B2142483
  · exact B2142487
  · exact B2142491
  · exact B2142495
  · exact B2142499
  · exact B2142503
  · exact B2142507
  · exact B2142511
  · exact B2142515
  · exact B2142519
  · exact B2142523
  · exact B2142527
  · exact B2142531
  · exact B2142535
  · exact B2142539
  · exact B2142543
  · exact B2142547
  · exact B2142551
  · exact B2142555
  · exact B2142559
  · exact B2142563
  · exact B2142567
  · exact B2142571
  · exact B2142575
  · exact B2142579
  · exact B2142583
  · exact B2142587
  · exact B2142591
  · exact B2142595
  · exact B2142599
  · exact B2142603
  · exact B2142607
  · exact B2142611
  · exact B2142615
  · exact B2142619
  · exact B2142623
  · exact B2142627
  · exact B2142631
  · exact B2142635
  · exact B2142639
  · exact B2142643
  · exact B2142647
  · exact B2142651
  · exact B2142655
  · exact B2142659
  · exact B2142663
  · exact B2142667
  · exact B2142671
  · exact B2142675
  · exact B2142679
  · exact B2142683
  · exact B2142687
  · exact B2142691
  · exact B2142695
  · exact B2142699
  · exact B2142703
  · exact B2142707
  · exact B2142711
  · exact B2142715
  · exact B2142719
  · exact B2142723
  · exact B2142727
  · exact B2142731
  · exact B2142735
  · exact B2142739
  · exact B2142743
  · exact B2142747
  · exact B2142751
  · exact B2142755
  · exact B2142759
  · exact B2142763
  · exact B2142767
  · exact B2142771
  · exact B2142775
  · exact B2142779
  · exact B2142783
  · exact B2142787
  · exact B2142791
  · exact B2142795
  · exact B2142799
  · exact B2142803
  · exact B2142807
  · exact B2142811
  · exact B2142815
  · exact B2142819
  · exact B2142823
  · exact B2142827
  · exact B2142831
  · exact B2142835
  · exact B2142839
  · exact B2142843
  · exact B2142847
  · exact B2142851
  · exact B2142855
  · exact B2142859
  · exact B2142863
  · exact B2142867
  · exact B2142871
  · exact B2142875
  · exact B2142879
  · exact B2142883
  · exact B2142887
  · exact B2142891
  · exact B2142895
  · exact B2142899
  · exact B2142903
  · exact B2142907
  · exact B2142911
  · exact B2142915
  · exact B2142919
  · exact B2142923
  · exact B2142927
  · exact B2142931
  · exact B2142935
  · exact B2142939
  · exact B2142943
  · exact B2142947
  · exact B2142951
  · exact B2142955
  · exact B2142959
  · exact B2142963
  · exact B2142967
  · exact B2142971
  · exact B2142975
  · exact B2142979
  · exact B2142983
  · exact B2142987
  · exact B2142991
  · exact B2142995
  · exact B2142999
  · exact B2143003
  · exact B2143007
  · exact B2143011
  · exact B2143015
  · exact B2143019
  · exact B2143023
  · exact B2143027
  · exact B2143031
  · exact B2143035
  · exact B2143039
  · exact B2143043
  · exact B2143047
  · exact B2143051
  · exact B2143055
  · exact B2143059
  · exact B2143063
  · exact B2143067
  · exact B2143071
  · exact B2143075
  · exact B2143079
  · exact B2143083
  · exact B2143087
  · exact B2143091
  · exact B2143095
  · exact B2143099
  · exact B2143103
  · exact B2143107
  · exact B2143111
  · exact B2143115
  · exact B2143119
  · exact B2143123
  · exact B2143127
  · exact B2143131
  · exact B2143135
  · exact B2143139
  · exact B2143143
  · exact B2143147
  · exact B2143151
  · exact B2143155
  · exact B2143159
  · exact B2143163
  · exact B2143167
  · exact B2143171
  · exact B2143175
  · exact B2143179
  · exact B2143183
  · exact B2143187
  · exact B2143191
  · exact B2143195
  · exact B2143199
  · exact B2143203
  · exact B2143207
  · exact B2143211
  · exact B2143215
  · exact B2143219
  · exact B2143223
  · exact B2143227
  · exact B2143231
  · exact B2143235
  · exact B2143239
  · exact B2143243
  · exact B2143247
  · exact B2143251
  · exact B2143255
  · exact B2143259
  · exact B2143263
  · exact B2143267
  · exact B2143271
  · exact B2143275
  · exact B2143279
  · exact B2143283
  · exact B2143287
  · exact B2143291
  · exact B2143295
  · exact B2143299
  · exact B2143303
  · exact B2143307
  · exact B2143311
  · exact B2143315
  · exact B2143319
  · exact B2143323
  · exact B2143327
  · exact B2143331
  · exact B2143335
  · exact B2143339
  · exact B2143343
  · exact B2143347
  · exact B2143351
  · exact B2143355
  · exact B2143359
  · exact B2143363
  · exact B2143367
  · exact B2143371
  · exact B2143375
  · exact B2143379
  · exact B2143383
  · exact B2143387
  · exact B2143391
  · exact B2143395
  · exact B2143399
  · exact B2143403
  · exact B2143407
  · exact B2143411
  · exact B2143415
  · exact B2143419
  · exact B2143423
  · exact B2143427
  · exact B2143431
  · exact B2143435
theorem solution (m : ℕ) (hlo : 2141435 ≤ m) (hhi : m ≤ 2143435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 535358 ≤ j := by omega
    have hj2 : j ≤ 535858 := by omega
    have hb : Blo 2141435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
