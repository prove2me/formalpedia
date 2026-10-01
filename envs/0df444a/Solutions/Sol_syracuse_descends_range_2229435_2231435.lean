-- Prove2me | solution 1 for syracuse_descends_range_2229435_2231435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:18:48.115954+00:00
-- url     : https://prove2.me/submissions/9c49c074-31ff-440e-9f1b-bf99958d79d3

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

theorem B3762173 : Blo 2229435 3762173 := bbase (se 3 (by rfl) ⟨705407, by rfl⟩ : syracuseStep 3762173 = 1410815) (by norm_num)
theorem B2508115 : Blo 2229435 2508115 := bstep (se 1 (by rfl) ⟨1881086, by rfl⟩ : syracuseStep 2508115 = 3762173) B3762173
theorem B3344153 : Blo 2229435 3344153 := bstep (se 2 (by rfl) ⟨1254057, by rfl⟩ : syracuseStep 3344153 = 2508115) B2508115
theorem B2229435 : Blo 2229435 2229435 := bstep (se 1 (by rfl) ⟨1672076, by rfl⟩ : syracuseStep 2229435 = 3344153) B3344153
theorem B4761509 : Blo 2229435 4761509 := bbase (se 4 (by rfl) ⟨446391, by rfl⟩ : syracuseStep 4761509 = 892783) (by norm_num)
theorem B12697357 : Blo 2229435 12697357 := bstep (se 3 (by rfl) ⟨2380754, by rfl⟩ : syracuseStep 12697357 = 4761509) B4761509
theorem B16929809 : Blo 2229435 16929809 := bstep (se 2 (by rfl) ⟨6348678, by rfl⟩ : syracuseStep 16929809 = 12697357) B12697357
theorem B11286539 : Blo 2229435 11286539 := bstep (se 1 (by rfl) ⟨8464904, by rfl⟩ : syracuseStep 11286539 = 16929809) B16929809
theorem B7524359 : Blo 2229435 7524359 := bstep (se 1 (by rfl) ⟨5643269, by rfl⟩ : syracuseStep 7524359 = 11286539) B11286539
theorem B5016239 : Blo 2229435 5016239 := bstep (se 1 (by rfl) ⟨3762179, by rfl⟩ : syracuseStep 5016239 = 7524359) B7524359
theorem B3344159 : Blo 2229435 3344159 := bstep (se 1 (by rfl) ⟨2508119, by rfl⟩ : syracuseStep 3344159 = 5016239) B5016239
theorem B2229439 : Blo 2229435 2229439 := bstep (se 1 (by rfl) ⟨1672079, by rfl⟩ : syracuseStep 2229439 = 3344159) B3344159
theorem B3344165 : Blo 2229435 3344165 := bbase (se 4 (by rfl) ⟨313515, by rfl⟩ : syracuseStep 3344165 = 627031) (by norm_num)
theorem B2229443 : Blo 2229435 2229443 := bstep (se 1 (by rfl) ⟨1672082, by rfl⟩ : syracuseStep 2229443 = 3344165) B3344165
theorem B2821645 : Blo 2229435 2821645 := bbase (se 3 (by rfl) ⟨529058, by rfl⟩ : syracuseStep 2821645 = 1058117) (by norm_num)
theorem B3762193 : Blo 2229435 3762193 := bstep (se 2 (by rfl) ⟨1410822, by rfl⟩ : syracuseStep 3762193 = 2821645) B2821645
theorem B5016257 : Blo 2229435 5016257 := bstep (se 2 (by rfl) ⟨1881096, by rfl⟩ : syracuseStep 5016257 = 3762193) B3762193
theorem B3344171 : Blo 2229435 3344171 := bstep (se 1 (by rfl) ⟨2508128, by rfl⟩ : syracuseStep 3344171 = 5016257) B5016257
theorem B2229447 : Blo 2229435 2229447 := bstep (se 1 (by rfl) ⟨1672085, by rfl⟩ : syracuseStep 2229447 = 3344171) B3344171
theorem B2508133 : Blo 2229435 2508133 := bbase (se 4 (by rfl) ⟨235137, by rfl⟩ : syracuseStep 2508133 = 470275) (by norm_num)
theorem B3344177 : Blo 2229435 3344177 := bstep (se 2 (by rfl) ⟨1254066, by rfl⟩ : syracuseStep 3344177 = 2508133) B2508133
theorem B2229451 : Blo 2229435 2229451 := bstep (se 1 (by rfl) ⟨1672088, by rfl⟩ : syracuseStep 2229451 = 3344177) B3344177
theorem B6348725 : Blo 2229435 6348725 := bbase (se 5 (by rfl) ⟨297596, by rfl⟩ : syracuseStep 6348725 = 595193) (by norm_num)
theorem B4232483 : Blo 2229435 4232483 := bstep (se 1 (by rfl) ⟨3174362, by rfl⟩ : syracuseStep 4232483 = 6348725) B6348725
theorem B2821655 : Blo 2229435 2821655 := bstep (se 1 (by rfl) ⟨2116241, by rfl⟩ : syracuseStep 2821655 = 4232483) B4232483
theorem B7524413 : Blo 2229435 7524413 := bstep (se 3 (by rfl) ⟨1410827, by rfl⟩ : syracuseStep 7524413 = 2821655) B2821655
theorem B5016275 : Blo 2229435 5016275 := bstep (se 1 (by rfl) ⟨3762206, by rfl⟩ : syracuseStep 5016275 = 7524413) B7524413
theorem B3344183 : Blo 2229435 3344183 := bstep (se 1 (by rfl) ⟨2508137, by rfl⟩ : syracuseStep 3344183 = 5016275) B5016275
theorem B2229455 : Blo 2229435 2229455 := bstep (se 1 (by rfl) ⟨1672091, by rfl⟩ : syracuseStep 2229455 = 3344183) B3344183
theorem B3344189 : Blo 2229435 3344189 := bbase (se 3 (by rfl) ⟨627035, by rfl⟩ : syracuseStep 3344189 = 1254071) (by norm_num)
theorem B2229459 : Blo 2229435 2229459 := bstep (se 1 (by rfl) ⟨1672094, by rfl⟩ : syracuseStep 2229459 = 3344189) B3344189
theorem B5016293 : Blo 2229435 5016293 := bbase (se 4 (by rfl) ⟨470277, by rfl⟩ : syracuseStep 5016293 = 940555) (by norm_num)
theorem B3344195 : Blo 2229435 3344195 := bstep (se 1 (by rfl) ⟨2508146, by rfl⟩ : syracuseStep 3344195 = 5016293) B5016293
theorem B2229463 : Blo 2229435 2229463 := bstep (se 1 (by rfl) ⟨1672097, by rfl⟩ : syracuseStep 2229463 = 3344195) B3344195
theorem B5643341 : Blo 2229435 5643341 := bbase (se 3 (by rfl) ⟨1058126, by rfl⟩ : syracuseStep 5643341 = 2116253) (by norm_num)
theorem B3762227 : Blo 2229435 3762227 := bstep (se 1 (by rfl) ⟨2821670, by rfl⟩ : syracuseStep 3762227 = 5643341) B5643341
theorem B2508151 : Blo 2229435 2508151 := bstep (se 1 (by rfl) ⟨1881113, by rfl⟩ : syracuseStep 2508151 = 3762227) B3762227
theorem B3344201 : Blo 2229435 3344201 := bstep (se 2 (by rfl) ⟨1254075, by rfl⟩ : syracuseStep 3344201 = 2508151) B2508151
theorem B2229467 : Blo 2229435 2229467 := bstep (se 1 (by rfl) ⟨1672100, by rfl⟩ : syracuseStep 2229467 = 3344201) B3344201
theorem B2380789 : Blo 2229435 2380789 := bbase (se 5 (by rfl) ⟨111599, by rfl⟩ : syracuseStep 2380789 = 223199) (by norm_num)
theorem B3174385 : Blo 2229435 3174385 := bstep (se 2 (by rfl) ⟨1190394, by rfl⟩ : syracuseStep 3174385 = 2380789) B2380789
theorem B4232513 : Blo 2229435 4232513 := bstep (se 2 (by rfl) ⟨1587192, by rfl⟩ : syracuseStep 4232513 = 3174385) B3174385
theorem B11286701 : Blo 2229435 11286701 := bstep (se 3 (by rfl) ⟨2116256, by rfl⟩ : syracuseStep 11286701 = 4232513) B4232513
theorem B7524467 : Blo 2229435 7524467 := bstep (se 1 (by rfl) ⟨5643350, by rfl⟩ : syracuseStep 7524467 = 11286701) B11286701
theorem B5016311 : Blo 2229435 5016311 := bstep (se 1 (by rfl) ⟨3762233, by rfl⟩ : syracuseStep 5016311 = 7524467) B7524467
theorem B3344207 : Blo 2229435 3344207 := bstep (se 1 (by rfl) ⟨2508155, by rfl⟩ : syracuseStep 3344207 = 5016311) B5016311
theorem B2229471 : Blo 2229435 2229471 := bstep (se 1 (by rfl) ⟨1672103, by rfl⟩ : syracuseStep 2229471 = 3344207) B3344207
theorem B3344213 : Blo 2229435 3344213 := bbase (se 9 (by rfl) ⟨9797, by rfl⟩ : syracuseStep 3344213 = 19595) (by norm_num)
theorem B2229475 : Blo 2229435 2229475 := bstep (se 1 (by rfl) ⟨1672106, by rfl⟩ : syracuseStep 2229475 = 3344213) B3344213
theorem B2714941 : Blo 2229435 2714941 := bbase (se 3 (by rfl) ⟨509051, by rfl⟩ : syracuseStep 2714941 = 1018103) (by norm_num)
theorem B3619921 : Blo 2229435 3619921 := bstep (se 2 (by rfl) ⟨1357470, by rfl⟩ : syracuseStep 3619921 = 2714941) B2714941
theorem B4826561 : Blo 2229435 4826561 := bstep (se 2 (by rfl) ⟨1809960, by rfl⟩ : syracuseStep 4826561 = 3619921) B3619921
theorem B12870829 : Blo 2229435 12870829 := bstep (se 3 (by rfl) ⟨2413280, by rfl⟩ : syracuseStep 12870829 = 4826561) B4826561
theorem B17161105 : Blo 2229435 17161105 := bstep (se 2 (by rfl) ⟨6435414, by rfl⟩ : syracuseStep 17161105 = 12870829) B12870829
theorem B22881473 : Blo 2229435 22881473 := bstep (se 2 (by rfl) ⟨8580552, by rfl⟩ : syracuseStep 22881473 = 17161105) B17161105
theorem B15254315 : Blo 2229435 15254315 := bstep (se 1 (by rfl) ⟨11440736, by rfl⟩ : syracuseStep 15254315 = 22881473) B22881473
theorem B10169543 : Blo 2229435 10169543 := bstep (se 1 (by rfl) ⟨7627157, by rfl⟩ : syracuseStep 10169543 = 15254315) B15254315
theorem B6779695 : Blo 2229435 6779695 := bstep (se 1 (by rfl) ⟨5084771, by rfl⟩ : syracuseStep 6779695 = 10169543) B10169543
theorem B9039593 : Blo 2229435 9039593 := bstep (se 2 (by rfl) ⟨3389847, by rfl⟩ : syracuseStep 9039593 = 6779695) B6779695
theorem B6026395 : Blo 2229435 6026395 := bstep (se 1 (by rfl) ⟨4519796, by rfl⟩ : syracuseStep 6026395 = 9039593) B9039593
theorem B8035193 : Blo 2229435 8035193 := bstep (se 2 (by rfl) ⟨3013197, by rfl⟩ : syracuseStep 8035193 = 6026395) B6026395
theorem B5356795 : Blo 2229435 5356795 := bstep (se 1 (by rfl) ⟨4017596, by rfl⟩ : syracuseStep 5356795 = 8035193) B8035193
theorem B7142393 : Blo 2229435 7142393 := bstep (se 2 (by rfl) ⟨2678397, by rfl⟩ : syracuseStep 7142393 = 5356795) B5356795
theorem B4761595 : Blo 2229435 4761595 := bstep (se 1 (by rfl) ⟨3571196, by rfl⟩ : syracuseStep 4761595 = 7142393) B7142393
theorem B6348793 : Blo 2229435 6348793 := bstep (se 2 (by rfl) ⟨2380797, by rfl⟩ : syracuseStep 6348793 = 4761595) B4761595
theorem B8465057 : Blo 2229435 8465057 := bstep (se 2 (by rfl) ⟨3174396, by rfl⟩ : syracuseStep 8465057 = 6348793) B6348793
theorem B5643371 : Blo 2229435 5643371 := bstep (se 1 (by rfl) ⟨4232528, by rfl⟩ : syracuseStep 5643371 = 8465057) B8465057
theorem B3762247 : Blo 2229435 3762247 := bstep (se 1 (by rfl) ⟨2821685, by rfl⟩ : syracuseStep 3762247 = 5643371) B5643371
theorem B5016329 : Blo 2229435 5016329 := bstep (se 2 (by rfl) ⟨1881123, by rfl⟩ : syracuseStep 5016329 = 3762247) B3762247
theorem B3344219 : Blo 2229435 3344219 := bstep (se 1 (by rfl) ⟨2508164, by rfl⟩ : syracuseStep 3344219 = 5016329) B5016329
theorem B2229479 : Blo 2229435 2229479 := bstep (se 1 (by rfl) ⟨1672109, by rfl⟩ : syracuseStep 2229479 = 3344219) B3344219
theorem B2508169 : Blo 2229435 2508169 := bbase (se 2 (by rfl) ⟨940563, by rfl⟩ : syracuseStep 2508169 = 1881127) (by norm_num)
theorem B3344225 : Blo 2229435 3344225 := bstep (se 2 (by rfl) ⟨1254084, by rfl⟩ : syracuseStep 3344225 = 2508169) B2508169
theorem B2229483 : Blo 2229435 2229483 := bstep (se 1 (by rfl) ⟨1672112, by rfl⟩ : syracuseStep 2229483 = 3344225) B3344225
theorem B15462485 : Blo 2229435 15462485 := bbase (se 8 (by rfl) ⟨90600, by rfl⟩ : syracuseStep 15462485 = 181201) (by norm_num)
theorem B10308323 : Blo 2229435 10308323 := bstep (se 1 (by rfl) ⟨7731242, by rfl⟩ : syracuseStep 10308323 = 15462485) B15462485
theorem B27488861 : Blo 2229435 27488861 := bstep (se 3 (by rfl) ⟨5154161, by rfl⟩ : syracuseStep 27488861 = 10308323) B10308323
theorem B18325907 : Blo 2229435 18325907 := bstep (se 1 (by rfl) ⟨13744430, by rfl⟩ : syracuseStep 18325907 = 27488861) B27488861
theorem B12217271 : Blo 2229435 12217271 := bstep (se 1 (by rfl) ⟨9162953, by rfl⟩ : syracuseStep 12217271 = 18325907) B18325907
theorem B32579389 : Blo 2229435 32579389 := bstep (se 3 (by rfl) ⟨6108635, by rfl⟩ : syracuseStep 32579389 = 12217271) B12217271
theorem B43439185 : Blo 2229435 43439185 := bstep (se 2 (by rfl) ⟨16289694, by rfl⟩ : syracuseStep 43439185 = 32579389) B32579389
theorem B231675653 : Blo 2229435 231675653 := bstep (se 4 (by rfl) ⟨21719592, by rfl⟩ : syracuseStep 231675653 = 43439185) B43439185
theorem B154450435 : Blo 2229435 154450435 := bstep (se 1 (by rfl) ⟨115837826, by rfl⟩ : syracuseStep 154450435 = 231675653) B231675653
theorem B205933913 : Blo 2229435 205933913 := bstep (se 2 (by rfl) ⟨77225217, by rfl⟩ : syracuseStep 205933913 = 154450435) B154450435
theorem B137289275 : Blo 2229435 137289275 := bstep (se 1 (by rfl) ⟨102966956, by rfl⟩ : syracuseStep 137289275 = 205933913) B205933913
theorem B91526183 : Blo 2229435 91526183 := bstep (se 1 (by rfl) ⟨68644637, by rfl⟩ : syracuseStep 91526183 = 137289275) B137289275
theorem B61017455 : Blo 2229435 61017455 := bstep (se 1 (by rfl) ⟨45763091, by rfl⟩ : syracuseStep 61017455 = 91526183) B91526183
theorem B40678303 : Blo 2229435 40678303 := bstep (se 1 (by rfl) ⟨30508727, by rfl⟩ : syracuseStep 40678303 = 61017455) B61017455
theorem B54237737 : Blo 2229435 54237737 := bstep (se 2 (by rfl) ⟨20339151, by rfl⟩ : syracuseStep 54237737 = 40678303) B40678303
theorem B36158491 : Blo 2229435 36158491 := bstep (se 1 (by rfl) ⟨27118868, by rfl⟩ : syracuseStep 36158491 = 54237737) B54237737
theorem B48211321 : Blo 2229435 48211321 := bstep (se 2 (by rfl) ⟨18079245, by rfl⟩ : syracuseStep 48211321 = 36158491) B36158491
theorem B64281761 : Blo 2229435 64281761 := bstep (se 2 (by rfl) ⟨24105660, by rfl⟩ : syracuseStep 64281761 = 48211321) B48211321
theorem B42854507 : Blo 2229435 42854507 := bstep (se 1 (by rfl) ⟨32140880, by rfl⟩ : syracuseStep 42854507 = 64281761) B64281761
theorem B28569671 : Blo 2229435 28569671 := bstep (se 1 (by rfl) ⟨21427253, by rfl⟩ : syracuseStep 28569671 = 42854507) B42854507
theorem B19046447 : Blo 2229435 19046447 := bstep (se 1 (by rfl) ⟨14284835, by rfl⟩ : syracuseStep 19046447 = 28569671) B28569671
theorem B12697631 : Blo 2229435 12697631 := bstep (se 1 (by rfl) ⟨9523223, by rfl⟩ : syracuseStep 12697631 = 19046447) B19046447
theorem B8465087 : Blo 2229435 8465087 := bstep (se 1 (by rfl) ⟨6348815, by rfl⟩ : syracuseStep 8465087 = 12697631) B12697631
theorem B5643391 : Blo 2229435 5643391 := bstep (se 1 (by rfl) ⟨4232543, by rfl⟩ : syracuseStep 5643391 = 8465087) B8465087
theorem B7524521 : Blo 2229435 7524521 := bstep (se 2 (by rfl) ⟨2821695, by rfl⟩ : syracuseStep 7524521 = 5643391) B5643391
theorem B5016347 : Blo 2229435 5016347 := bstep (se 1 (by rfl) ⟨3762260, by rfl⟩ : syracuseStep 5016347 = 7524521) B7524521
theorem B3344231 : Blo 2229435 3344231 := bstep (se 1 (by rfl) ⟨2508173, by rfl⟩ : syracuseStep 3344231 = 5016347) B5016347
theorem B2229487 : Blo 2229435 2229487 := bstep (se 1 (by rfl) ⟨1672115, by rfl⟩ : syracuseStep 2229487 = 3344231) B3344231
theorem B3344237 : Blo 2229435 3344237 := bbase (se 3 (by rfl) ⟨627044, by rfl⟩ : syracuseStep 3344237 = 1254089) (by norm_num)
theorem B2229491 : Blo 2229435 2229491 := bstep (se 1 (by rfl) ⟨1672118, by rfl⟩ : syracuseStep 2229491 = 3344237) B3344237
theorem B5016365 : Blo 2229435 5016365 := bbase (se 3 (by rfl) ⟨940568, by rfl⟩ : syracuseStep 5016365 = 1881137) (by norm_num)
theorem B3344243 : Blo 2229435 3344243 := bstep (se 1 (by rfl) ⟨2508182, by rfl⟩ : syracuseStep 3344243 = 5016365) B5016365
theorem B2229495 : Blo 2229435 2229495 := bstep (se 1 (by rfl) ⟨1672121, by rfl⟩ : syracuseStep 2229495 = 3344243) B3344243
theorem B3571229 : Blo 2229435 3571229 := bbase (se 3 (by rfl) ⟨669605, by rfl⟩ : syracuseStep 3571229 = 1339211) (by norm_num)
theorem B9523277 : Blo 2229435 9523277 := bstep (se 3 (by rfl) ⟨1785614, by rfl⟩ : syracuseStep 9523277 = 3571229) B3571229
theorem B6348851 : Blo 2229435 6348851 := bstep (se 1 (by rfl) ⟨4761638, by rfl⟩ : syracuseStep 6348851 = 9523277) B9523277
theorem B4232567 : Blo 2229435 4232567 := bstep (se 1 (by rfl) ⟨3174425, by rfl⟩ : syracuseStep 4232567 = 6348851) B6348851
theorem B2821711 : Blo 2229435 2821711 := bstep (se 1 (by rfl) ⟨2116283, by rfl⟩ : syracuseStep 2821711 = 4232567) B4232567
theorem B3762281 : Blo 2229435 3762281 := bstep (se 2 (by rfl) ⟨1410855, by rfl⟩ : syracuseStep 3762281 = 2821711) B2821711
theorem B2508187 : Blo 2229435 2508187 := bstep (se 1 (by rfl) ⟨1881140, by rfl⟩ : syracuseStep 2508187 = 3762281) B3762281
theorem B3344249 : Blo 2229435 3344249 := bstep (se 2 (by rfl) ⟨1254093, by rfl⟩ : syracuseStep 3344249 = 2508187) B2508187
theorem B2229499 : Blo 2229435 2229499 := bstep (se 1 (by rfl) ⟨1672124, by rfl⟩ : syracuseStep 2229499 = 3344249) B3344249
theorem B2714969 : Blo 2229435 2714969 := bbase (se 2 (by rfl) ⟨1018113, by rfl⟩ : syracuseStep 2714969 = 2036227) (by norm_num)
theorem B7239917 : Blo 2229435 7239917 := bstep (se 3 (by rfl) ⟨1357484, by rfl⟩ : syracuseStep 7239917 = 2714969) B2714969
theorem B4826611 : Blo 2229435 4826611 := bstep (se 1 (by rfl) ⟨3619958, by rfl⟩ : syracuseStep 4826611 = 7239917) B7239917
theorem B25741925 : Blo 2229435 25741925 := bstep (se 4 (by rfl) ⟨2413305, by rfl⟩ : syracuseStep 25741925 = 4826611) B4826611
theorem B17161283 : Blo 2229435 17161283 := bstep (se 1 (by rfl) ⟨12870962, by rfl⟩ : syracuseStep 17161283 = 25741925) B25741925
theorem B11440855 : Blo 2229435 11440855 := bstep (se 1 (by rfl) ⟨8580641, by rfl⟩ : syracuseStep 11440855 = 17161283) B17161283
theorem B61017893 : Blo 2229435 61017893 := bstep (se 4 (by rfl) ⟨5720427, by rfl⟩ : syracuseStep 61017893 = 11440855) B11440855
theorem B40678595 : Blo 2229435 40678595 := bstep (se 1 (by rfl) ⟨30508946, by rfl⟩ : syracuseStep 40678595 = 61017893) B61017893
theorem B27119063 : Blo 2229435 27119063 := bstep (se 1 (by rfl) ⟨20339297, by rfl⟩ : syracuseStep 27119063 = 40678595) B40678595
theorem B18079375 : Blo 2229435 18079375 := bstep (se 1 (by rfl) ⟨13559531, by rfl⟩ : syracuseStep 18079375 = 27119063) B27119063
theorem B24105833 : Blo 2229435 24105833 := bstep (se 2 (by rfl) ⟨9039687, by rfl⟩ : syracuseStep 24105833 = 18079375) B18079375
theorem B16070555 : Blo 2229435 16070555 := bstep (se 1 (by rfl) ⟨12052916, by rfl⟩ : syracuseStep 16070555 = 24105833) B24105833
theorem B10713703 : Blo 2229435 10713703 := bstep (se 1 (by rfl) ⟨8035277, by rfl⟩ : syracuseStep 10713703 = 16070555) B16070555
theorem B14284937 : Blo 2229435 14284937 := bstep (se 2 (by rfl) ⟨5356851, by rfl⟩ : syracuseStep 14284937 = 10713703) B10713703
theorem B38093165 : Blo 2229435 38093165 := bstep (se 3 (by rfl) ⟨7142468, by rfl⟩ : syracuseStep 38093165 = 14284937) B14284937
theorem B25395443 : Blo 2229435 25395443 := bstep (se 1 (by rfl) ⟨19046582, by rfl⟩ : syracuseStep 25395443 = 38093165) B38093165
theorem B16930295 : Blo 2229435 16930295 := bstep (se 1 (by rfl) ⟨12697721, by rfl⟩ : syracuseStep 16930295 = 25395443) B25395443
theorem B11286863 : Blo 2229435 11286863 := bstep (se 1 (by rfl) ⟨8465147, by rfl⟩ : syracuseStep 11286863 = 16930295) B16930295
theorem B7524575 : Blo 2229435 7524575 := bstep (se 1 (by rfl) ⟨5643431, by rfl⟩ : syracuseStep 7524575 = 11286863) B11286863
theorem B5016383 : Blo 2229435 5016383 := bstep (se 1 (by rfl) ⟨3762287, by rfl⟩ : syracuseStep 5016383 = 7524575) B7524575
theorem B3344255 : Blo 2229435 3344255 := bstep (se 1 (by rfl) ⟨2508191, by rfl⟩ : syracuseStep 3344255 = 5016383) B5016383
theorem B2229503 : Blo 2229435 2229503 := bstep (se 1 (by rfl) ⟨1672127, by rfl⟩ : syracuseStep 2229503 = 3344255) B3344255
theorem B3344261 : Blo 2229435 3344261 := bbase (se 4 (by rfl) ⟨313524, by rfl⟩ : syracuseStep 3344261 = 627049) (by norm_num)
theorem B2229507 : Blo 2229435 2229507 := bstep (se 1 (by rfl) ⟨1672130, by rfl⟩ : syracuseStep 2229507 = 3344261) B3344261
theorem B3762301 : Blo 2229435 3762301 := bbase (se 3 (by rfl) ⟨705431, by rfl⟩ : syracuseStep 3762301 = 1410863) (by norm_num)
theorem B5016401 : Blo 2229435 5016401 := bstep (se 2 (by rfl) ⟨1881150, by rfl⟩ : syracuseStep 5016401 = 3762301) B3762301
theorem B3344267 : Blo 2229435 3344267 := bstep (se 1 (by rfl) ⟨2508200, by rfl⟩ : syracuseStep 3344267 = 5016401) B5016401
theorem B2229511 : Blo 2229435 2229511 := bstep (se 1 (by rfl) ⟨1672133, by rfl⟩ : syracuseStep 2229511 = 3344267) B3344267
theorem B2508205 : Blo 2229435 2508205 := bbase (se 3 (by rfl) ⟨470288, by rfl⟩ : syracuseStep 2508205 = 940577) (by norm_num)
theorem B3344273 : Blo 2229435 3344273 := bstep (se 2 (by rfl) ⟨1254102, by rfl⟩ : syracuseStep 3344273 = 2508205) B2508205
theorem B2229515 : Blo 2229435 2229515 := bstep (se 1 (by rfl) ⟨1672136, by rfl⟩ : syracuseStep 2229515 = 3344273) B3344273
theorem B7524629 : Blo 2229435 7524629 := bbase (se 6 (by rfl) ⟨176358, by rfl⟩ : syracuseStep 7524629 = 352717) (by norm_num)
theorem B5016419 : Blo 2229435 5016419 := bstep (se 1 (by rfl) ⟨3762314, by rfl⟩ : syracuseStep 5016419 = 7524629) B7524629
theorem B3344279 : Blo 2229435 3344279 := bstep (se 1 (by rfl) ⟨2508209, by rfl⟩ : syracuseStep 3344279 = 5016419) B5016419
theorem B2229519 : Blo 2229435 2229519 := bstep (se 1 (by rfl) ⟨1672139, by rfl⟩ : syracuseStep 2229519 = 3344279) B3344279
theorem B3344285 : Blo 2229435 3344285 := bbase (se 3 (by rfl) ⟨627053, by rfl⟩ : syracuseStep 3344285 = 1254107) (by norm_num)
theorem B2229523 : Blo 2229435 2229523 := bstep (se 1 (by rfl) ⟨1672142, by rfl⟩ : syracuseStep 2229523 = 3344285) B3344285
theorem B5016437 : Blo 2229435 5016437 := bbase (se 5 (by rfl) ⟨235145, by rfl⟩ : syracuseStep 5016437 = 470291) (by norm_num)
theorem B3344291 : Blo 2229435 3344291 := bstep (se 1 (by rfl) ⟨2508218, by rfl⟩ : syracuseStep 3344291 = 5016437) B5016437
theorem B2229527 : Blo 2229435 2229527 := bstep (se 1 (by rfl) ⟨1672145, by rfl⟩ : syracuseStep 2229527 = 3344291) B3344291
theorem B51484501 : Blo 2229435 51484501 := bbase (se 9 (by rfl) ⟨150833, by rfl⟩ : syracuseStep 51484501 = 301667) (by norm_num)
theorem B68646001 : Blo 2229435 68646001 := bstep (se 2 (by rfl) ⟨25742250, by rfl⟩ : syracuseStep 68646001 = 51484501) B51484501
theorem B91528001 : Blo 2229435 91528001 := bstep (se 2 (by rfl) ⟨34323000, by rfl⟩ : syracuseStep 91528001 = 68646001) B68646001
theorem B61018667 : Blo 2229435 61018667 := bstep (se 1 (by rfl) ⟨45764000, by rfl⟩ : syracuseStep 61018667 = 91528001) B91528001
theorem B40679111 : Blo 2229435 40679111 := bstep (se 1 (by rfl) ⟨30509333, by rfl⟩ : syracuseStep 40679111 = 61018667) B61018667
theorem B108477629 : Blo 2229435 108477629 := bstep (se 3 (by rfl) ⟨20339555, by rfl⟩ : syracuseStep 108477629 = 40679111) B40679111
theorem B72318419 : Blo 2229435 72318419 := bstep (se 1 (by rfl) ⟨54238814, by rfl⟩ : syracuseStep 72318419 = 108477629) B108477629
theorem B48212279 : Blo 2229435 48212279 := bstep (se 1 (by rfl) ⟨36159209, by rfl⟩ : syracuseStep 48212279 = 72318419) B72318419
theorem B32141519 : Blo 2229435 32141519 := bstep (se 1 (by rfl) ⟨24106139, by rfl⟩ : syracuseStep 32141519 = 48212279) B48212279
theorem B21427679 : Blo 2229435 21427679 := bstep (se 1 (by rfl) ⟨16070759, by rfl⟩ : syracuseStep 21427679 = 32141519) B32141519
theorem B14285119 : Blo 2229435 14285119 := bstep (se 1 (by rfl) ⟨10713839, by rfl⟩ : syracuseStep 14285119 = 21427679) B21427679
theorem B19046825 : Blo 2229435 19046825 := bstep (se 2 (by rfl) ⟨7142559, by rfl⟩ : syracuseStep 19046825 = 14285119) B14285119
theorem B12697883 : Blo 2229435 12697883 := bstep (se 1 (by rfl) ⟨9523412, by rfl⟩ : syracuseStep 12697883 = 19046825) B19046825
theorem B8465255 : Blo 2229435 8465255 := bstep (se 1 (by rfl) ⟨6348941, by rfl⟩ : syracuseStep 8465255 = 12697883) B12697883
theorem B5643503 : Blo 2229435 5643503 := bstep (se 1 (by rfl) ⟨4232627, by rfl⟩ : syracuseStep 5643503 = 8465255) B8465255
theorem B3762335 : Blo 2229435 3762335 := bstep (se 1 (by rfl) ⟨2821751, by rfl⟩ : syracuseStep 3762335 = 5643503) B5643503
theorem B2508223 : Blo 2229435 2508223 := bstep (se 1 (by rfl) ⟨1881167, by rfl⟩ : syracuseStep 2508223 = 3762335) B3762335
theorem B3344297 : Blo 2229435 3344297 := bstep (se 2 (by rfl) ⟨1254111, by rfl⟩ : syracuseStep 3344297 = 2508223) B2508223
theorem B2229531 : Blo 2229435 2229531 := bstep (se 1 (by rfl) ⟨1672148, by rfl⟩ : syracuseStep 2229531 = 3344297) B3344297
theorem B8465269 : Blo 2229435 8465269 := bbase (se 5 (by rfl) ⟨396809, by rfl⟩ : syracuseStep 8465269 = 793619) (by norm_num)
theorem B11287025 : Blo 2229435 11287025 := bstep (se 2 (by rfl) ⟨4232634, by rfl⟩ : syracuseStep 11287025 = 8465269) B8465269
theorem B7524683 : Blo 2229435 7524683 := bstep (se 1 (by rfl) ⟨5643512, by rfl⟩ : syracuseStep 7524683 = 11287025) B11287025
theorem B5016455 : Blo 2229435 5016455 := bstep (se 1 (by rfl) ⟨3762341, by rfl⟩ : syracuseStep 5016455 = 7524683) B7524683
theorem B3344303 : Blo 2229435 3344303 := bstep (se 1 (by rfl) ⟨2508227, by rfl⟩ : syracuseStep 3344303 = 5016455) B5016455
theorem B2229535 : Blo 2229435 2229535 := bstep (se 1 (by rfl) ⟨1672151, by rfl⟩ : syracuseStep 2229535 = 3344303) B3344303
theorem B3344309 : Blo 2229435 3344309 := bbase (se 5 (by rfl) ⟨156764, by rfl⟩ : syracuseStep 3344309 = 313529) (by norm_num)
theorem B2229539 : Blo 2229435 2229539 := bstep (se 1 (by rfl) ⟨1672154, by rfl⟩ : syracuseStep 2229539 = 3344309) B3344309
theorem B5643533 : Blo 2229435 5643533 := bbase (se 3 (by rfl) ⟨1058162, by rfl⟩ : syracuseStep 5643533 = 2116325) (by norm_num)
theorem B3762355 : Blo 2229435 3762355 := bstep (se 1 (by rfl) ⟨2821766, by rfl⟩ : syracuseStep 3762355 = 5643533) B5643533
theorem B5016473 : Blo 2229435 5016473 := bstep (se 2 (by rfl) ⟨1881177, by rfl⟩ : syracuseStep 5016473 = 3762355) B3762355
theorem B3344315 : Blo 2229435 3344315 := bstep (se 1 (by rfl) ⟨2508236, by rfl⟩ : syracuseStep 3344315 = 5016473) B5016473
theorem B2229543 : Blo 2229435 2229543 := bstep (se 1 (by rfl) ⟨1672157, by rfl⟩ : syracuseStep 2229543 = 3344315) B3344315
theorem B2508241 : Blo 2229435 2508241 := bbase (se 2 (by rfl) ⟨940590, by rfl⟩ : syracuseStep 2508241 = 1881181) (by norm_num)
theorem B3344321 : Blo 2229435 3344321 := bstep (se 2 (by rfl) ⟨1254120, by rfl⟩ : syracuseStep 3344321 = 2508241) B2508241
theorem B2229547 : Blo 2229435 2229547 := bstep (se 1 (by rfl) ⟨1672160, by rfl⟩ : syracuseStep 2229547 = 3344321) B3344321
theorem B4761749 : Blo 2229435 4761749 := bbase (se 6 (by rfl) ⟨111603, by rfl⟩ : syracuseStep 4761749 = 223207) (by norm_num)
theorem B3174499 : Blo 2229435 3174499 := bstep (se 1 (by rfl) ⟨2380874, by rfl⟩ : syracuseStep 3174499 = 4761749) B4761749
theorem B4232665 : Blo 2229435 4232665 := bstep (se 2 (by rfl) ⟨1587249, by rfl⟩ : syracuseStep 4232665 = 3174499) B3174499
theorem B5643553 : Blo 2229435 5643553 := bstep (se 2 (by rfl) ⟨2116332, by rfl⟩ : syracuseStep 5643553 = 4232665) B4232665
theorem B7524737 : Blo 2229435 7524737 := bstep (se 2 (by rfl) ⟨2821776, by rfl⟩ : syracuseStep 7524737 = 5643553) B5643553
theorem B5016491 : Blo 2229435 5016491 := bstep (se 1 (by rfl) ⟨3762368, by rfl⟩ : syracuseStep 5016491 = 7524737) B7524737
theorem B3344327 : Blo 2229435 3344327 := bstep (se 1 (by rfl) ⟨2508245, by rfl⟩ : syracuseStep 3344327 = 5016491) B5016491
theorem B2229551 : Blo 2229435 2229551 := bstep (se 1 (by rfl) ⟨1672163, by rfl⟩ : syracuseStep 2229551 = 3344327) B3344327
theorem B3344333 : Blo 2229435 3344333 := bbase (se 3 (by rfl) ⟨627062, by rfl⟩ : syracuseStep 3344333 = 1254125) (by norm_num)
theorem B2229555 : Blo 2229435 2229555 := bstep (se 1 (by rfl) ⟨1672166, by rfl⟩ : syracuseStep 2229555 = 3344333) B3344333
theorem B5016509 : Blo 2229435 5016509 := bbase (se 3 (by rfl) ⟨940595, by rfl⟩ : syracuseStep 5016509 = 1881191) (by norm_num)
theorem B3344339 : Blo 2229435 3344339 := bstep (se 1 (by rfl) ⟨2508254, by rfl⟩ : syracuseStep 3344339 = 5016509) B5016509
theorem B2229559 : Blo 2229435 2229559 := bstep (se 1 (by rfl) ⟨1672169, by rfl⟩ : syracuseStep 2229559 = 3344339) B3344339
theorem B3762389 : Blo 2229435 3762389 := bbase (se 7 (by rfl) ⟨44090, by rfl⟩ : syracuseStep 3762389 = 88181) (by norm_num)
theorem B2508259 : Blo 2229435 2508259 := bstep (se 1 (by rfl) ⟨1881194, by rfl⟩ : syracuseStep 2508259 = 3762389) B3762389
theorem B3344345 : Blo 2229435 3344345 := bstep (se 2 (by rfl) ⟨1254129, by rfl⟩ : syracuseStep 3344345 = 2508259) B2508259
theorem B2229563 : Blo 2229435 2229563 := bstep (se 1 (by rfl) ⟨1672172, by rfl⟩ : syracuseStep 2229563 = 3344345) B3344345
theorem B11441189 : Blo 2229435 11441189 := bbase (se 4 (by rfl) ⟨1072611, by rfl⟩ : syracuseStep 11441189 = 2145223) (by norm_num)
theorem B7627459 : Blo 2229435 7627459 := bstep (se 1 (by rfl) ⟨5720594, by rfl⟩ : syracuseStep 7627459 = 11441189) B11441189
theorem B10169945 : Blo 2229435 10169945 := bstep (se 2 (by rfl) ⟨3813729, by rfl⟩ : syracuseStep 10169945 = 7627459) B7627459
theorem B6779963 : Blo 2229435 6779963 := bstep (se 1 (by rfl) ⟨5084972, by rfl⟩ : syracuseStep 6779963 = 10169945) B10169945
theorem B4519975 : Blo 2229435 4519975 := bstep (se 1 (by rfl) ⟨3389981, by rfl⟩ : syracuseStep 4519975 = 6779963) B6779963
theorem B6026633 : Blo 2229435 6026633 := bstep (se 2 (by rfl) ⟨2259987, by rfl⟩ : syracuseStep 6026633 = 4519975) B4519975
theorem B4017755 : Blo 2229435 4017755 := bstep (se 1 (by rfl) ⟨3013316, by rfl⟩ : syracuseStep 4017755 = 6026633) B6026633
theorem B2678503 : Blo 2229435 2678503 := bstep (se 1 (by rfl) ⟨2008877, by rfl⟩ : syracuseStep 2678503 = 4017755) B4017755
theorem B3571337 : Blo 2229435 3571337 := bstep (se 2 (by rfl) ⟨1339251, by rfl⟩ : syracuseStep 3571337 = 2678503) B2678503
theorem B9523565 : Blo 2229435 9523565 := bstep (se 3 (by rfl) ⟨1785668, by rfl⟩ : syracuseStep 9523565 = 3571337) B3571337
theorem B6349043 : Blo 2229435 6349043 := bstep (se 1 (by rfl) ⟨4761782, by rfl⟩ : syracuseStep 6349043 = 9523565) B9523565
theorem B16930781 : Blo 2229435 16930781 := bstep (se 3 (by rfl) ⟨3174521, by rfl⟩ : syracuseStep 16930781 = 6349043) B6349043
theorem B11287187 : Blo 2229435 11287187 := bstep (se 1 (by rfl) ⟨8465390, by rfl⟩ : syracuseStep 11287187 = 16930781) B16930781
theorem B7524791 : Blo 2229435 7524791 := bstep (se 1 (by rfl) ⟨5643593, by rfl⟩ : syracuseStep 7524791 = 11287187) B11287187
theorem B5016527 : Blo 2229435 5016527 := bstep (se 1 (by rfl) ⟨3762395, by rfl⟩ : syracuseStep 5016527 = 7524791) B7524791
theorem B3344351 : Blo 2229435 3344351 := bstep (se 1 (by rfl) ⟨2508263, by rfl⟩ : syracuseStep 3344351 = 5016527) B5016527
theorem B2229567 : Blo 2229435 2229567 := bstep (se 1 (by rfl) ⟨1672175, by rfl⟩ : syracuseStep 2229567 = 3344351) B3344351
theorem B3344357 : Blo 2229435 3344357 := bbase (se 4 (by rfl) ⟨313533, by rfl⟩ : syracuseStep 3344357 = 627067) (by norm_num)
theorem B2229571 : Blo 2229435 2229571 := bstep (se 1 (by rfl) ⟨1672178, by rfl⟩ : syracuseStep 2229571 = 3344357) B3344357
theorem B2678513 : Blo 2229435 2678513 := bbase (se 2 (by rfl) ⟨1004442, by rfl⟩ : syracuseStep 2678513 = 2008885) (by norm_num)
theorem B7142701 : Blo 2229435 7142701 := bstep (se 3 (by rfl) ⟨1339256, by rfl⟩ : syracuseStep 7142701 = 2678513) B2678513
theorem B9523601 : Blo 2229435 9523601 := bstep (se 2 (by rfl) ⟨3571350, by rfl⟩ : syracuseStep 9523601 = 7142701) B7142701
theorem B6349067 : Blo 2229435 6349067 := bstep (se 1 (by rfl) ⟨4761800, by rfl⟩ : syracuseStep 6349067 = 9523601) B9523601
theorem B4232711 : Blo 2229435 4232711 := bstep (se 1 (by rfl) ⟨3174533, by rfl⟩ : syracuseStep 4232711 = 6349067) B6349067
theorem B2821807 : Blo 2229435 2821807 := bstep (se 1 (by rfl) ⟨2116355, by rfl⟩ : syracuseStep 2821807 = 4232711) B4232711
theorem B3762409 : Blo 2229435 3762409 := bstep (se 2 (by rfl) ⟨1410903, by rfl⟩ : syracuseStep 3762409 = 2821807) B2821807
theorem B5016545 : Blo 2229435 5016545 := bstep (se 2 (by rfl) ⟨1881204, by rfl⟩ : syracuseStep 5016545 = 3762409) B3762409
theorem B3344363 : Blo 2229435 3344363 := bstep (se 1 (by rfl) ⟨2508272, by rfl⟩ : syracuseStep 3344363 = 5016545) B5016545
theorem B2229575 : Blo 2229435 2229575 := bstep (se 1 (by rfl) ⟨1672181, by rfl⟩ : syracuseStep 2229575 = 3344363) B3344363
theorem B2508277 : Blo 2229435 2508277 := bbase (se 5 (by rfl) ⟨117575, by rfl⟩ : syracuseStep 2508277 = 235151) (by norm_num)
theorem B3344369 : Blo 2229435 3344369 := bstep (se 2 (by rfl) ⟨1254138, by rfl⟩ : syracuseStep 3344369 = 2508277) B2508277
theorem B2229579 : Blo 2229435 2229579 := bstep (se 1 (by rfl) ⟨1672184, by rfl⟩ : syracuseStep 2229579 = 3344369) B3344369
theorem B2821817 : Blo 2229435 2821817 := bbase (se 2 (by rfl) ⟨1058181, by rfl⟩ : syracuseStep 2821817 = 2116363) (by norm_num)
theorem B7524845 : Blo 2229435 7524845 := bstep (se 3 (by rfl) ⟨1410908, by rfl⟩ : syracuseStep 7524845 = 2821817) B2821817
theorem B5016563 : Blo 2229435 5016563 := bstep (se 1 (by rfl) ⟨3762422, by rfl⟩ : syracuseStep 5016563 = 7524845) B7524845
theorem B3344375 : Blo 2229435 3344375 := bstep (se 1 (by rfl) ⟨2508281, by rfl⟩ : syracuseStep 3344375 = 5016563) B5016563
theorem B2229583 : Blo 2229435 2229583 := bstep (se 1 (by rfl) ⟨1672187, by rfl⟩ : syracuseStep 2229583 = 3344375) B3344375
theorem B3344381 : Blo 2229435 3344381 := bbase (se 3 (by rfl) ⟨627071, by rfl⟩ : syracuseStep 3344381 = 1254143) (by norm_num)
theorem B2229587 : Blo 2229435 2229587 := bstep (se 1 (by rfl) ⟨1672190, by rfl⟩ : syracuseStep 2229587 = 3344381) B3344381
theorem B5016581 : Blo 2229435 5016581 := bbase (se 4 (by rfl) ⟨470304, by rfl⟩ : syracuseStep 5016581 = 940609) (by norm_num)
theorem B3344387 : Blo 2229435 3344387 := bstep (se 1 (by rfl) ⟨2508290, by rfl⟩ : syracuseStep 3344387 = 5016581) B5016581
theorem B2229591 : Blo 2229435 2229591 := bstep (se 1 (by rfl) ⟨1672193, by rfl⟩ : syracuseStep 2229591 = 3344387) B3344387
theorem B4232749 : Blo 2229435 4232749 := bbase (se 3 (by rfl) ⟨793640, by rfl⟩ : syracuseStep 4232749 = 1587281) (by norm_num)
theorem B5643665 : Blo 2229435 5643665 := bstep (se 2 (by rfl) ⟨2116374, by rfl⟩ : syracuseStep 5643665 = 4232749) B4232749
theorem B3762443 : Blo 2229435 3762443 := bstep (se 1 (by rfl) ⟨2821832, by rfl⟩ : syracuseStep 3762443 = 5643665) B5643665
theorem B2508295 : Blo 2229435 2508295 := bstep (se 1 (by rfl) ⟨1881221, by rfl⟩ : syracuseStep 2508295 = 3762443) B3762443
theorem B3344393 : Blo 2229435 3344393 := bstep (se 2 (by rfl) ⟨1254147, by rfl⟩ : syracuseStep 3344393 = 2508295) B2508295
theorem B2229595 : Blo 2229435 2229595 := bstep (se 1 (by rfl) ⟨1672196, by rfl⟩ : syracuseStep 2229595 = 3344393) B3344393
theorem B11287349 : Blo 2229435 11287349 := bbase (se 5 (by rfl) ⟨529094, by rfl⟩ : syracuseStep 11287349 = 1058189) (by norm_num)
theorem B7524899 : Blo 2229435 7524899 := bstep (se 1 (by rfl) ⟨5643674, by rfl⟩ : syracuseStep 7524899 = 11287349) B11287349
theorem B5016599 : Blo 2229435 5016599 := bstep (se 1 (by rfl) ⟨3762449, by rfl⟩ : syracuseStep 5016599 = 7524899) B7524899
theorem B3344399 : Blo 2229435 3344399 := bstep (se 1 (by rfl) ⟨2508299, by rfl⟩ : syracuseStep 3344399 = 5016599) B5016599
theorem B2229599 : Blo 2229435 2229599 := bstep (se 1 (by rfl) ⟨1672199, by rfl⟩ : syracuseStep 2229599 = 3344399) B3344399
theorem B3344405 : Blo 2229435 3344405 := bbase (se 6 (by rfl) ⟨78384, by rfl⟩ : syracuseStep 3344405 = 156769) (by norm_num)
theorem B2229603 : Blo 2229435 2229603 := bstep (se 1 (by rfl) ⟨1672202, by rfl⟩ : syracuseStep 2229603 = 3344405) B3344405
theorem B6026741 : Blo 2229435 6026741 := bbase (se 5 (by rfl) ⟨282503, by rfl⟩ : syracuseStep 6026741 = 565007) (by norm_num)
theorem B4017827 : Blo 2229435 4017827 := bstep (se 1 (by rfl) ⟨3013370, by rfl⟩ : syracuseStep 4017827 = 6026741) B6026741
theorem B2678551 : Blo 2229435 2678551 := bstep (se 1 (by rfl) ⟨2008913, by rfl⟩ : syracuseStep 2678551 = 4017827) B4017827
theorem B14285605 : Blo 2229435 14285605 := bstep (se 4 (by rfl) ⟨1339275, by rfl⟩ : syracuseStep 14285605 = 2678551) B2678551
theorem B19047473 : Blo 2229435 19047473 := bstep (se 2 (by rfl) ⟨7142802, by rfl⟩ : syracuseStep 19047473 = 14285605) B14285605
theorem B12698315 : Blo 2229435 12698315 := bstep (se 1 (by rfl) ⟨9523736, by rfl⟩ : syracuseStep 12698315 = 19047473) B19047473
theorem B8465543 : Blo 2229435 8465543 := bstep (se 1 (by rfl) ⟨6349157, by rfl⟩ : syracuseStep 8465543 = 12698315) B12698315
theorem B5643695 : Blo 2229435 5643695 := bstep (se 1 (by rfl) ⟨4232771, by rfl⟩ : syracuseStep 5643695 = 8465543) B8465543
theorem B3762463 : Blo 2229435 3762463 := bstep (se 1 (by rfl) ⟨2821847, by rfl⟩ : syracuseStep 3762463 = 5643695) B5643695
theorem B5016617 : Blo 2229435 5016617 := bstep (se 2 (by rfl) ⟨1881231, by rfl⟩ : syracuseStep 5016617 = 3762463) B3762463
theorem B3344411 : Blo 2229435 3344411 := bstep (se 1 (by rfl) ⟨2508308, by rfl⟩ : syracuseStep 3344411 = 5016617) B5016617
theorem B2229607 : Blo 2229435 2229607 := bstep (se 1 (by rfl) ⟨1672205, by rfl⟩ : syracuseStep 2229607 = 3344411) B3344411
theorem B2508313 : Blo 2229435 2508313 := bbase (se 2 (by rfl) ⟨940617, by rfl⟩ : syracuseStep 2508313 = 1881235) (by norm_num)
theorem B3344417 : Blo 2229435 3344417 := bstep (se 2 (by rfl) ⟨1254156, by rfl⟩ : syracuseStep 3344417 = 2508313) B2508313
theorem B2229611 : Blo 2229435 2229611 := bstep (se 1 (by rfl) ⟨1672208, by rfl⟩ : syracuseStep 2229611 = 3344417) B3344417
theorem B8465573 : Blo 2229435 8465573 := bbase (se 4 (by rfl) ⟨793647, by rfl⟩ : syracuseStep 8465573 = 1587295) (by norm_num)
theorem B5643715 : Blo 2229435 5643715 := bstep (se 1 (by rfl) ⟨4232786, by rfl⟩ : syracuseStep 5643715 = 8465573) B8465573
theorem B7524953 : Blo 2229435 7524953 := bstep (se 2 (by rfl) ⟨2821857, by rfl⟩ : syracuseStep 7524953 = 5643715) B5643715
theorem B5016635 : Blo 2229435 5016635 := bstep (se 1 (by rfl) ⟨3762476, by rfl⟩ : syracuseStep 5016635 = 7524953) B7524953
theorem B3344423 : Blo 2229435 3344423 := bstep (se 1 (by rfl) ⟨2508317, by rfl⟩ : syracuseStep 3344423 = 5016635) B5016635
theorem B2229615 : Blo 2229435 2229615 := bstep (se 1 (by rfl) ⟨1672211, by rfl⟩ : syracuseStep 2229615 = 3344423) B3344423
theorem B3344429 : Blo 2229435 3344429 := bbase (se 3 (by rfl) ⟨627080, by rfl⟩ : syracuseStep 3344429 = 1254161) (by norm_num)
theorem B2229619 : Blo 2229435 2229619 := bstep (se 1 (by rfl) ⟨1672214, by rfl⟩ : syracuseStep 2229619 = 3344429) B3344429
theorem B5016653 : Blo 2229435 5016653 := bbase (se 3 (by rfl) ⟨940622, by rfl⟩ : syracuseStep 5016653 = 1881245) (by norm_num)
theorem B3344435 : Blo 2229435 3344435 := bstep (se 1 (by rfl) ⟨2508326, by rfl⟩ : syracuseStep 3344435 = 5016653) B5016653
theorem B2229623 : Blo 2229435 2229623 := bstep (se 1 (by rfl) ⟨1672217, by rfl⟩ : syracuseStep 2229623 = 3344435) B3344435
theorem B2821873 : Blo 2229435 2821873 := bbase (se 2 (by rfl) ⟨1058202, by rfl⟩ : syracuseStep 2821873 = 2116405) (by norm_num)
theorem B3762497 : Blo 2229435 3762497 := bstep (se 2 (by rfl) ⟨1410936, by rfl⟩ : syracuseStep 3762497 = 2821873) B2821873
theorem B2508331 : Blo 2229435 2508331 := bstep (se 1 (by rfl) ⟨1881248, by rfl⟩ : syracuseStep 2508331 = 3762497) B3762497
theorem B3344441 : Blo 2229435 3344441 := bstep (se 2 (by rfl) ⟨1254165, by rfl⟩ : syracuseStep 3344441 = 2508331) B2508331
theorem B2229627 : Blo 2229435 2229627 := bstep (se 1 (by rfl) ⟨1672220, by rfl⟩ : syracuseStep 2229627 = 3344441) B3344441
theorem B2715125 : Blo 2229435 2715125 := bbase (se 5 (by rfl) ⟨127271, by rfl⟩ : syracuseStep 2715125 = 254543) (by norm_num)
theorem B28961333 : Blo 2229435 28961333 := bstep (se 5 (by rfl) ⟨1357562, by rfl⟩ : syracuseStep 28961333 = 2715125) B2715125
theorem B19307555 : Blo 2229435 19307555 := bstep (se 1 (by rfl) ⟨14480666, by rfl⟩ : syracuseStep 19307555 = 28961333) B28961333
theorem B12871703 : Blo 2229435 12871703 := bstep (se 1 (by rfl) ⟨9653777, by rfl⟩ : syracuseStep 12871703 = 19307555) B19307555
theorem B8581135 : Blo 2229435 8581135 := bstep (se 1 (by rfl) ⟨6435851, by rfl⟩ : syracuseStep 8581135 = 12871703) B12871703
theorem B11441513 : Blo 2229435 11441513 := bstep (se 2 (by rfl) ⟨4290567, by rfl⟩ : syracuseStep 11441513 = 8581135) B8581135
theorem B30510701 : Blo 2229435 30510701 := bstep (se 3 (by rfl) ⟨5720756, by rfl⟩ : syracuseStep 30510701 = 11441513) B11441513
theorem B20340467 : Blo 2229435 20340467 := bstep (se 1 (by rfl) ⟨15255350, by rfl⟩ : syracuseStep 20340467 = 30510701) B30510701
theorem B13560311 : Blo 2229435 13560311 := bstep (se 1 (by rfl) ⟨10170233, by rfl⟩ : syracuseStep 13560311 = 20340467) B20340467
theorem B36160829 : Blo 2229435 36160829 := bstep (se 3 (by rfl) ⟨6780155, by rfl⟩ : syracuseStep 36160829 = 13560311) B13560311
theorem B24107219 : Blo 2229435 24107219 := bstep (se 1 (by rfl) ⟨18080414, by rfl⟩ : syracuseStep 24107219 = 36160829) B36160829
theorem B16071479 : Blo 2229435 16071479 := bstep (se 1 (by rfl) ⟨12053609, by rfl⟩ : syracuseStep 16071479 = 24107219) B24107219
theorem B10714319 : Blo 2229435 10714319 := bstep (se 1 (by rfl) ⟨8035739, by rfl⟩ : syracuseStep 10714319 = 16071479) B16071479
theorem B7142879 : Blo 2229435 7142879 := bstep (se 1 (by rfl) ⟨5357159, by rfl⟩ : syracuseStep 7142879 = 10714319) B10714319
theorem B4761919 : Blo 2229435 4761919 := bstep (se 1 (by rfl) ⟨3571439, by rfl⟩ : syracuseStep 4761919 = 7142879) B7142879
theorem B25396901 : Blo 2229435 25396901 := bstep (se 4 (by rfl) ⟨2380959, by rfl⟩ : syracuseStep 25396901 = 4761919) B4761919
theorem B16931267 : Blo 2229435 16931267 := bstep (se 1 (by rfl) ⟨12698450, by rfl⟩ : syracuseStep 16931267 = 25396901) B25396901
theorem B11287511 : Blo 2229435 11287511 := bstep (se 1 (by rfl) ⟨8465633, by rfl⟩ : syracuseStep 11287511 = 16931267) B16931267
theorem B7525007 : Blo 2229435 7525007 := bstep (se 1 (by rfl) ⟨5643755, by rfl⟩ : syracuseStep 7525007 = 11287511) B11287511
theorem B5016671 : Blo 2229435 5016671 := bstep (se 1 (by rfl) ⟨3762503, by rfl⟩ : syracuseStep 5016671 = 7525007) B7525007
theorem B3344447 : Blo 2229435 3344447 := bstep (se 1 (by rfl) ⟨2508335, by rfl⟩ : syracuseStep 3344447 = 5016671) B5016671
theorem B2229631 : Blo 2229435 2229631 := bstep (se 1 (by rfl) ⟨1672223, by rfl⟩ : syracuseStep 2229631 = 3344447) B3344447
theorem B3344453 : Blo 2229435 3344453 := bbase (se 4 (by rfl) ⟨313542, by rfl⟩ : syracuseStep 3344453 = 627085) (by norm_num)
theorem B2229635 : Blo 2229435 2229635 := bstep (se 1 (by rfl) ⟨1672226, by rfl⟩ : syracuseStep 2229635 = 3344453) B3344453
theorem B3762517 : Blo 2229435 3762517 := bbase (se 10 (by rfl) ⟨5511, by rfl⟩ : syracuseStep 3762517 = 11023) (by norm_num)
theorem B5016689 : Blo 2229435 5016689 := bstep (se 2 (by rfl) ⟨1881258, by rfl⟩ : syracuseStep 5016689 = 3762517) B3762517
theorem B3344459 : Blo 2229435 3344459 := bstep (se 1 (by rfl) ⟨2508344, by rfl⟩ : syracuseStep 3344459 = 5016689) B5016689
theorem B2229639 : Blo 2229435 2229639 := bstep (se 1 (by rfl) ⟨1672229, by rfl⟩ : syracuseStep 2229639 = 3344459) B3344459
theorem B2508349 : Blo 2229435 2508349 := bbase (se 3 (by rfl) ⟨470315, by rfl⟩ : syracuseStep 2508349 = 940631) (by norm_num)
theorem B3344465 : Blo 2229435 3344465 := bstep (se 2 (by rfl) ⟨1254174, by rfl⟩ : syracuseStep 3344465 = 2508349) B2508349
theorem B2229643 : Blo 2229435 2229643 := bstep (se 1 (by rfl) ⟨1672232, by rfl⟩ : syracuseStep 2229643 = 3344465) B3344465
theorem B7525061 : Blo 2229435 7525061 := bbase (se 4 (by rfl) ⟨705474, by rfl⟩ : syracuseStep 7525061 = 1410949) (by norm_num)
theorem B5016707 : Blo 2229435 5016707 := bstep (se 1 (by rfl) ⟨3762530, by rfl⟩ : syracuseStep 5016707 = 7525061) B7525061
theorem B3344471 : Blo 2229435 3344471 := bstep (se 1 (by rfl) ⟨2508353, by rfl⟩ : syracuseStep 3344471 = 5016707) B5016707
theorem B2229647 : Blo 2229435 2229647 := bstep (se 1 (by rfl) ⟨1672235, by rfl⟩ : syracuseStep 2229647 = 3344471) B3344471
theorem B3344477 : Blo 2229435 3344477 := bbase (se 3 (by rfl) ⟨627089, by rfl⟩ : syracuseStep 3344477 = 1254179) (by norm_num)
theorem B2229651 : Blo 2229435 2229651 := bstep (se 1 (by rfl) ⟨1672238, by rfl⟩ : syracuseStep 2229651 = 3344477) B3344477
theorem B5016725 : Blo 2229435 5016725 := bbase (se 6 (by rfl) ⟨117579, by rfl⟩ : syracuseStep 5016725 = 235159) (by norm_num)
theorem B3344483 : Blo 2229435 3344483 := bstep (se 1 (by rfl) ⟨2508362, by rfl⟩ : syracuseStep 3344483 = 5016725) B5016725
theorem B2229655 : Blo 2229435 2229655 := bstep (se 1 (by rfl) ⟨1672241, by rfl⟩ : syracuseStep 2229655 = 3344483) B3344483
theorem B3174653 : Blo 2229435 3174653 := bbase (se 3 (by rfl) ⟨595247, by rfl⟩ : syracuseStep 3174653 = 1190495) (by norm_num)
theorem B8465741 : Blo 2229435 8465741 := bstep (se 3 (by rfl) ⟨1587326, by rfl⟩ : syracuseStep 8465741 = 3174653) B3174653
theorem B5643827 : Blo 2229435 5643827 := bstep (se 1 (by rfl) ⟨4232870, by rfl⟩ : syracuseStep 5643827 = 8465741) B8465741
theorem B3762551 : Blo 2229435 3762551 := bstep (se 1 (by rfl) ⟨2821913, by rfl⟩ : syracuseStep 3762551 = 5643827) B5643827
theorem B2508367 : Blo 2229435 2508367 := bstep (se 1 (by rfl) ⟨1881275, by rfl⟩ : syracuseStep 2508367 = 3762551) B3762551
theorem B3344489 : Blo 2229435 3344489 := bstep (se 2 (by rfl) ⟨1254183, by rfl⟩ : syracuseStep 3344489 = 2508367) B2508367
theorem B2229659 : Blo 2229435 2229659 := bstep (se 1 (by rfl) ⟨1672244, by rfl⟩ : syracuseStep 2229659 = 3344489) B3344489
theorem B3813893 : Blo 2229435 3813893 := bbase (se 4 (by rfl) ⟨357552, by rfl⟩ : syracuseStep 3813893 = 715105) (by norm_num)
theorem B2542595 : Blo 2229435 2542595 := bstep (se 1 (by rfl) ⟨1906946, by rfl⟩ : syracuseStep 2542595 = 3813893) B3813893
theorem B6780253 : Blo 2229435 6780253 := bstep (se 3 (by rfl) ⟨1271297, by rfl⟩ : syracuseStep 6780253 = 2542595) B2542595
theorem B9040337 : Blo 2229435 9040337 := bstep (se 2 (by rfl) ⟨3390126, by rfl⟩ : syracuseStep 9040337 = 6780253) B6780253
theorem B6026891 : Blo 2229435 6026891 := bstep (se 1 (by rfl) ⟨4520168, by rfl⟩ : syracuseStep 6026891 = 9040337) B9040337
theorem B16071709 : Blo 2229435 16071709 := bstep (se 3 (by rfl) ⟨3013445, by rfl⟩ : syracuseStep 16071709 = 6026891) B6026891
theorem B21428945 : Blo 2229435 21428945 := bstep (se 2 (by rfl) ⟨8035854, by rfl⟩ : syracuseStep 21428945 = 16071709) B16071709
theorem B14285963 : Blo 2229435 14285963 := bstep (se 1 (by rfl) ⟨10714472, by rfl⟩ : syracuseStep 14285963 = 21428945) B21428945
theorem B9523975 : Blo 2229435 9523975 := bstep (se 1 (by rfl) ⟨7142981, by rfl⟩ : syracuseStep 9523975 = 14285963) B14285963
theorem B12698633 : Blo 2229435 12698633 := bstep (se 2 (by rfl) ⟨4761987, by rfl⟩ : syracuseStep 12698633 = 9523975) B9523975
theorem B8465755 : Blo 2229435 8465755 := bstep (se 1 (by rfl) ⟨6349316, by rfl⟩ : syracuseStep 8465755 = 12698633) B12698633
theorem B11287673 : Blo 2229435 11287673 := bstep (se 2 (by rfl) ⟨4232877, by rfl⟩ : syracuseStep 11287673 = 8465755) B8465755
theorem B7525115 : Blo 2229435 7525115 := bstep (se 1 (by rfl) ⟨5643836, by rfl⟩ : syracuseStep 7525115 = 11287673) B11287673
theorem B5016743 : Blo 2229435 5016743 := bstep (se 1 (by rfl) ⟨3762557, by rfl⟩ : syracuseStep 5016743 = 7525115) B7525115
theorem B3344495 : Blo 2229435 3344495 := bstep (se 1 (by rfl) ⟨2508371, by rfl⟩ : syracuseStep 3344495 = 5016743) B5016743
theorem B2229663 : Blo 2229435 2229663 := bstep (se 1 (by rfl) ⟨1672247, by rfl⟩ : syracuseStep 2229663 = 3344495) B3344495
theorem B3344501 : Blo 2229435 3344501 := bbase (se 5 (by rfl) ⟨156773, by rfl⟩ : syracuseStep 3344501 = 313547) (by norm_num)
theorem B2229667 : Blo 2229435 2229667 := bstep (se 1 (by rfl) ⟨1672250, by rfl⟩ : syracuseStep 2229667 = 3344501) B3344501
theorem B4232893 : Blo 2229435 4232893 := bbase (se 3 (by rfl) ⟨793667, by rfl⟩ : syracuseStep 4232893 = 1587335) (by norm_num)
theorem B5643857 : Blo 2229435 5643857 := bstep (se 2 (by rfl) ⟨2116446, by rfl⟩ : syracuseStep 5643857 = 4232893) B4232893
theorem B3762571 : Blo 2229435 3762571 := bstep (se 1 (by rfl) ⟨2821928, by rfl⟩ : syracuseStep 3762571 = 5643857) B5643857
theorem B5016761 : Blo 2229435 5016761 := bstep (se 2 (by rfl) ⟨1881285, by rfl⟩ : syracuseStep 5016761 = 3762571) B3762571
theorem B3344507 : Blo 2229435 3344507 := bstep (se 1 (by rfl) ⟨2508380, by rfl⟩ : syracuseStep 3344507 = 5016761) B5016761
theorem B2229671 : Blo 2229435 2229671 := bstep (se 1 (by rfl) ⟨1672253, by rfl⟩ : syracuseStep 2229671 = 3344507) B3344507
theorem B2508385 : Blo 2229435 2508385 := bbase (se 2 (by rfl) ⟨940644, by rfl⟩ : syracuseStep 2508385 = 1881289) (by norm_num)
theorem B3344513 : Blo 2229435 3344513 := bstep (se 2 (by rfl) ⟨1254192, by rfl⟩ : syracuseStep 3344513 = 2508385) B2508385
theorem B2229675 : Blo 2229435 2229675 := bstep (se 1 (by rfl) ⟨1672256, by rfl⟩ : syracuseStep 2229675 = 3344513) B3344513
theorem B5643877 : Blo 2229435 5643877 := bbase (se 4 (by rfl) ⟨529113, by rfl⟩ : syracuseStep 5643877 = 1058227) (by norm_num)
theorem B7525169 : Blo 2229435 7525169 := bstep (se 2 (by rfl) ⟨2821938, by rfl⟩ : syracuseStep 7525169 = 5643877) B5643877
theorem B5016779 : Blo 2229435 5016779 := bstep (se 1 (by rfl) ⟨3762584, by rfl⟩ : syracuseStep 5016779 = 7525169) B7525169
theorem B3344519 : Blo 2229435 3344519 := bstep (se 1 (by rfl) ⟨2508389, by rfl⟩ : syracuseStep 3344519 = 5016779) B5016779
theorem B2229679 : Blo 2229435 2229679 := bstep (se 1 (by rfl) ⟨1672259, by rfl⟩ : syracuseStep 2229679 = 3344519) B3344519
theorem B3344525 : Blo 2229435 3344525 := bbase (se 3 (by rfl) ⟨627098, by rfl⟩ : syracuseStep 3344525 = 1254197) (by norm_num)
theorem B2229683 : Blo 2229435 2229683 := bstep (se 1 (by rfl) ⟨1672262, by rfl⟩ : syracuseStep 2229683 = 3344525) B3344525
theorem B5016797 : Blo 2229435 5016797 := bbase (se 3 (by rfl) ⟨940649, by rfl⟩ : syracuseStep 5016797 = 1881299) (by norm_num)
theorem B3344531 : Blo 2229435 3344531 := bstep (se 1 (by rfl) ⟨2508398, by rfl⟩ : syracuseStep 3344531 = 5016797) B5016797
theorem B2229687 : Blo 2229435 2229687 := bstep (se 1 (by rfl) ⟨1672265, by rfl⟩ : syracuseStep 2229687 = 3344531) B3344531
theorem B3762605 : Blo 2229435 3762605 := bbase (se 3 (by rfl) ⟨705488, by rfl⟩ : syracuseStep 3762605 = 1410977) (by norm_num)
theorem B2508403 : Blo 2229435 2508403 := bstep (se 1 (by rfl) ⟨1881302, by rfl⟩ : syracuseStep 2508403 = 3762605) B3762605
theorem B3344537 : Blo 2229435 3344537 := bstep (se 2 (by rfl) ⟨1254201, by rfl⟩ : syracuseStep 3344537 = 2508403) B2508403
theorem B2229691 : Blo 2229435 2229691 := bstep (se 1 (by rfl) ⟨1672268, by rfl⟩ : syracuseStep 2229691 = 3344537) B3344537
theorem B6436037 : Blo 2229435 6436037 := bbase (se 4 (by rfl) ⟨603378, by rfl⟩ : syracuseStep 6436037 = 1206757) (by norm_num)
theorem B4290691 : Blo 2229435 4290691 := bstep (se 1 (by rfl) ⟨3218018, by rfl⟩ : syracuseStep 4290691 = 6436037) B6436037
theorem B5720921 : Blo 2229435 5720921 := bstep (se 2 (by rfl) ⟨2145345, by rfl⟩ : syracuseStep 5720921 = 4290691) B4290691
theorem B3813947 : Blo 2229435 3813947 := bstep (se 1 (by rfl) ⟨2860460, by rfl⟩ : syracuseStep 3813947 = 5720921) B5720921
theorem B2542631 : Blo 2229435 2542631 := bstep (se 1 (by rfl) ⟨1906973, by rfl⟩ : syracuseStep 2542631 = 3813947) B3813947
theorem B27121397 : Blo 2229435 27121397 := bstep (se 5 (by rfl) ⟨1271315, by rfl⟩ : syracuseStep 27121397 = 2542631) B2542631
theorem B72323725 : Blo 2229435 72323725 := bstep (se 3 (by rfl) ⟨13560698, by rfl⟩ : syracuseStep 72323725 = 27121397) B27121397
theorem B96431633 : Blo 2229435 96431633 := bstep (se 2 (by rfl) ⟨36161862, by rfl⟩ : syracuseStep 96431633 = 72323725) B72323725
theorem B64287755 : Blo 2229435 64287755 := bstep (se 1 (by rfl) ⟨48215816, by rfl⟩ : syracuseStep 64287755 = 96431633) B96431633
theorem B42858503 : Blo 2229435 42858503 := bstep (se 1 (by rfl) ⟨32143877, by rfl⟩ : syracuseStep 42858503 = 64287755) B64287755
theorem B28572335 : Blo 2229435 28572335 := bstep (se 1 (by rfl) ⟨21429251, by rfl⟩ : syracuseStep 28572335 = 42858503) B42858503
theorem B19048223 : Blo 2229435 19048223 := bstep (se 1 (by rfl) ⟨14286167, by rfl⟩ : syracuseStep 19048223 = 28572335) B28572335
theorem B12698815 : Blo 2229435 12698815 := bstep (se 1 (by rfl) ⟨9524111, by rfl⟩ : syracuseStep 12698815 = 19048223) B19048223
theorem B16931753 : Blo 2229435 16931753 := bstep (se 2 (by rfl) ⟨6349407, by rfl⟩ : syracuseStep 16931753 = 12698815) B12698815
theorem B11287835 : Blo 2229435 11287835 := bstep (se 1 (by rfl) ⟨8465876, by rfl⟩ : syracuseStep 11287835 = 16931753) B16931753
theorem B7525223 : Blo 2229435 7525223 := bstep (se 1 (by rfl) ⟨5643917, by rfl⟩ : syracuseStep 7525223 = 11287835) B11287835
theorem B5016815 : Blo 2229435 5016815 := bstep (se 1 (by rfl) ⟨3762611, by rfl⟩ : syracuseStep 5016815 = 7525223) B7525223
theorem B3344543 : Blo 2229435 3344543 := bstep (se 1 (by rfl) ⟨2508407, by rfl⟩ : syracuseStep 3344543 = 5016815) B5016815
theorem B2229695 : Blo 2229435 2229695 := bstep (se 1 (by rfl) ⟨1672271, by rfl⟩ : syracuseStep 2229695 = 3344543) B3344543
theorem B3344549 : Blo 2229435 3344549 := bbase (se 4 (by rfl) ⟨313551, by rfl⟩ : syracuseStep 3344549 = 627103) (by norm_num)
theorem B2229699 : Blo 2229435 2229699 := bstep (se 1 (by rfl) ⟨1672274, by rfl⟩ : syracuseStep 2229699 = 3344549) B3344549
theorem B2821969 : Blo 2229435 2821969 := bbase (se 2 (by rfl) ⟨1058238, by rfl⟩ : syracuseStep 2821969 = 2116477) (by norm_num)
theorem B3762625 : Blo 2229435 3762625 := bstep (se 2 (by rfl) ⟨1410984, by rfl⟩ : syracuseStep 3762625 = 2821969) B2821969
theorem B5016833 : Blo 2229435 5016833 := bstep (se 2 (by rfl) ⟨1881312, by rfl⟩ : syracuseStep 5016833 = 3762625) B3762625
theorem B3344555 : Blo 2229435 3344555 := bstep (se 1 (by rfl) ⟨2508416, by rfl⟩ : syracuseStep 3344555 = 5016833) B5016833
theorem B2229703 : Blo 2229435 2229703 := bstep (se 1 (by rfl) ⟨1672277, by rfl⟩ : syracuseStep 2229703 = 3344555) B3344555
theorem B2508421 : Blo 2229435 2508421 := bbase (se 4 (by rfl) ⟨235164, by rfl⟩ : syracuseStep 2508421 = 470329) (by norm_num)
theorem B3344561 : Blo 2229435 3344561 := bstep (se 2 (by rfl) ⟨1254210, by rfl⟩ : syracuseStep 3344561 = 2508421) B2508421
theorem B2229707 : Blo 2229435 2229707 := bstep (se 1 (by rfl) ⟨1672280, by rfl⟩ : syracuseStep 2229707 = 3344561) B3344561
theorem B20341205 : Blo 2229435 20341205 := bbase (se 7 (by rfl) ⟨238373, by rfl⟩ : syracuseStep 20341205 = 476747) (by norm_num)
theorem B13560803 : Blo 2229435 13560803 := bstep (se 1 (by rfl) ⟨10170602, by rfl⟩ : syracuseStep 13560803 = 20341205) B20341205
theorem B9040535 : Blo 2229435 9040535 := bstep (se 1 (by rfl) ⟨6780401, by rfl⟩ : syracuseStep 9040535 = 13560803) B13560803
theorem B6027023 : Blo 2229435 6027023 := bstep (se 1 (by rfl) ⟨4520267, by rfl⟩ : syracuseStep 6027023 = 9040535) B9040535
theorem B4018015 : Blo 2229435 4018015 := bstep (se 1 (by rfl) ⟨3013511, by rfl⟩ : syracuseStep 4018015 = 6027023) B6027023
theorem B5357353 : Blo 2229435 5357353 := bstep (se 2 (by rfl) ⟨2009007, by rfl⟩ : syracuseStep 5357353 = 4018015) B4018015
theorem B7143137 : Blo 2229435 7143137 := bstep (se 2 (by rfl) ⟨2678676, by rfl⟩ : syracuseStep 7143137 = 5357353) B5357353
theorem B4762091 : Blo 2229435 4762091 := bstep (se 1 (by rfl) ⟨3571568, by rfl⟩ : syracuseStep 4762091 = 7143137) B7143137
theorem B3174727 : Blo 2229435 3174727 := bstep (se 1 (by rfl) ⟨2381045, by rfl⟩ : syracuseStep 3174727 = 4762091) B4762091
theorem B4232969 : Blo 2229435 4232969 := bstep (se 2 (by rfl) ⟨1587363, by rfl⟩ : syracuseStep 4232969 = 3174727) B3174727
theorem B2821979 : Blo 2229435 2821979 := bstep (se 1 (by rfl) ⟨2116484, by rfl⟩ : syracuseStep 2821979 = 4232969) B4232969
theorem B7525277 : Blo 2229435 7525277 := bstep (se 3 (by rfl) ⟨1410989, by rfl⟩ : syracuseStep 7525277 = 2821979) B2821979
theorem B5016851 : Blo 2229435 5016851 := bstep (se 1 (by rfl) ⟨3762638, by rfl⟩ : syracuseStep 5016851 = 7525277) B7525277
theorem B3344567 : Blo 2229435 3344567 := bstep (se 1 (by rfl) ⟨2508425, by rfl⟩ : syracuseStep 3344567 = 5016851) B5016851
theorem B2229711 : Blo 2229435 2229711 := bstep (se 1 (by rfl) ⟨1672283, by rfl⟩ : syracuseStep 2229711 = 3344567) B3344567
theorem B3344573 : Blo 2229435 3344573 := bbase (se 3 (by rfl) ⟨627107, by rfl⟩ : syracuseStep 3344573 = 1254215) (by norm_num)
theorem B2229715 : Blo 2229435 2229715 := bstep (se 1 (by rfl) ⟨1672286, by rfl⟩ : syracuseStep 2229715 = 3344573) B3344573
theorem B5016869 : Blo 2229435 5016869 := bbase (se 4 (by rfl) ⟨470331, by rfl⟩ : syracuseStep 5016869 = 940663) (by norm_num)
theorem B3344579 : Blo 2229435 3344579 := bstep (se 1 (by rfl) ⟨2508434, by rfl⟩ : syracuseStep 3344579 = 5016869) B5016869
theorem B2229719 : Blo 2229435 2229719 := bstep (se 1 (by rfl) ⟨1672289, by rfl⟩ : syracuseStep 2229719 = 3344579) B3344579
theorem B5643989 : Blo 2229435 5643989 := bbase (se 7 (by rfl) ⟨66140, by rfl⟩ : syracuseStep 5643989 = 132281) (by norm_num)
theorem B3762659 : Blo 2229435 3762659 := bstep (se 1 (by rfl) ⟨2821994, by rfl⟩ : syracuseStep 3762659 = 5643989) B5643989
theorem B2508439 : Blo 2229435 2508439 := bstep (se 1 (by rfl) ⟨1881329, by rfl⟩ : syracuseStep 2508439 = 3762659) B3762659
theorem B3344585 : Blo 2229435 3344585 := bstep (se 2 (by rfl) ⟨1254219, by rfl⟩ : syracuseStep 3344585 = 2508439) B2508439
theorem B2229723 : Blo 2229435 2229723 := bstep (se 1 (by rfl) ⟨1672292, by rfl⟩ : syracuseStep 2229723 = 3344585) B3344585
theorem B5721005 : Blo 2229435 5721005 := bbase (se 3 (by rfl) ⟨1072688, by rfl⟩ : syracuseStep 5721005 = 2145377) (by norm_num)
theorem B3814003 : Blo 2229435 3814003 := bstep (se 1 (by rfl) ⟨2860502, by rfl⟩ : syracuseStep 3814003 = 5721005) B5721005
theorem B5085337 : Blo 2229435 5085337 := bstep (se 2 (by rfl) ⟨1907001, by rfl⟩ : syracuseStep 5085337 = 3814003) B3814003
theorem B6780449 : Blo 2229435 6780449 := bstep (se 2 (by rfl) ⟨2542668, by rfl⟩ : syracuseStep 6780449 = 5085337) B5085337
theorem B4520299 : Blo 2229435 4520299 := bstep (se 1 (by rfl) ⟨3390224, by rfl⟩ : syracuseStep 4520299 = 6780449) B6780449
theorem B6027065 : Blo 2229435 6027065 := bstep (se 2 (by rfl) ⟨2260149, by rfl⟩ : syracuseStep 6027065 = 4520299) B4520299
theorem B4018043 : Blo 2229435 4018043 := bstep (se 1 (by rfl) ⟨3013532, by rfl⟩ : syracuseStep 4018043 = 6027065) B6027065
theorem B10714781 : Blo 2229435 10714781 := bstep (se 3 (by rfl) ⟨2009021, by rfl⟩ : syracuseStep 10714781 = 4018043) B4018043
theorem B7143187 : Blo 2229435 7143187 := bstep (se 1 (by rfl) ⟨5357390, by rfl⟩ : syracuseStep 7143187 = 10714781) B10714781
theorem B9524249 : Blo 2229435 9524249 := bstep (se 2 (by rfl) ⟨3571593, by rfl⟩ : syracuseStep 9524249 = 7143187) B7143187
theorem B6349499 : Blo 2229435 6349499 := bstep (se 1 (by rfl) ⟨4762124, by rfl⟩ : syracuseStep 6349499 = 9524249) B9524249
theorem B4232999 : Blo 2229435 4232999 := bstep (se 1 (by rfl) ⟨3174749, by rfl⟩ : syracuseStep 4232999 = 6349499) B6349499
theorem B11287997 : Blo 2229435 11287997 := bstep (se 3 (by rfl) ⟨2116499, by rfl⟩ : syracuseStep 11287997 = 4232999) B4232999
theorem B7525331 : Blo 2229435 7525331 := bstep (se 1 (by rfl) ⟨5643998, by rfl⟩ : syracuseStep 7525331 = 11287997) B11287997
theorem B5016887 : Blo 2229435 5016887 := bstep (se 1 (by rfl) ⟨3762665, by rfl⟩ : syracuseStep 5016887 = 7525331) B7525331
theorem B3344591 : Blo 2229435 3344591 := bstep (se 1 (by rfl) ⟨2508443, by rfl⟩ : syracuseStep 3344591 = 5016887) B5016887
theorem B2229727 : Blo 2229435 2229727 := bstep (se 1 (by rfl) ⟨1672295, by rfl⟩ : syracuseStep 2229727 = 3344591) B3344591
theorem B3344597 : Blo 2229435 3344597 := bbase (se 7 (by rfl) ⟨39194, by rfl⟩ : syracuseStep 3344597 = 78389) (by norm_num)
theorem B2229731 : Blo 2229435 2229731 := bstep (se 1 (by rfl) ⟨1672298, by rfl⟩ : syracuseStep 2229731 = 3344597) B3344597
theorem B8036117 : Blo 2229435 8036117 := bbase (se 6 (by rfl) ⟨188346, by rfl⟩ : syracuseStep 8036117 = 376693) (by norm_num)
theorem B5357411 : Blo 2229435 5357411 := bstep (se 1 (by rfl) ⟨4018058, by rfl⟩ : syracuseStep 5357411 = 8036117) B8036117
theorem B3571607 : Blo 2229435 3571607 := bstep (se 1 (by rfl) ⟨2678705, by rfl⟩ : syracuseStep 3571607 = 5357411) B5357411
theorem B2381071 : Blo 2229435 2381071 := bstep (se 1 (by rfl) ⟨1785803, by rfl⟩ : syracuseStep 2381071 = 3571607) B3571607
theorem B3174761 : Blo 2229435 3174761 := bstep (se 2 (by rfl) ⟨1190535, by rfl⟩ : syracuseStep 3174761 = 2381071) B2381071
theorem B8466029 : Blo 2229435 8466029 := bstep (se 3 (by rfl) ⟨1587380, by rfl⟩ : syracuseStep 8466029 = 3174761) B3174761
theorem B5644019 : Blo 2229435 5644019 := bstep (se 1 (by rfl) ⟨4233014, by rfl⟩ : syracuseStep 5644019 = 8466029) B8466029
theorem B3762679 : Blo 2229435 3762679 := bstep (se 1 (by rfl) ⟨2822009, by rfl⟩ : syracuseStep 3762679 = 5644019) B5644019
theorem B5016905 : Blo 2229435 5016905 := bstep (se 2 (by rfl) ⟨1881339, by rfl⟩ : syracuseStep 5016905 = 3762679) B3762679
theorem B3344603 : Blo 2229435 3344603 := bstep (se 1 (by rfl) ⟨2508452, by rfl⟩ : syracuseStep 3344603 = 5016905) B5016905
theorem B2229735 : Blo 2229435 2229735 := bstep (se 1 (by rfl) ⟨1672301, by rfl⟩ : syracuseStep 2229735 = 3344603) B3344603
theorem B2508457 : Blo 2229435 2508457 := bbase (se 2 (by rfl) ⟨940671, by rfl⟩ : syracuseStep 2508457 = 1881343) (by norm_num)
theorem B3344609 : Blo 2229435 3344609 := bstep (se 2 (by rfl) ⟨1254228, by rfl⟩ : syracuseStep 3344609 = 2508457) B2508457
theorem B2229739 : Blo 2229435 2229739 := bstep (se 1 (by rfl) ⟨1672304, by rfl⟩ : syracuseStep 2229739 = 3344609) B3344609
theorem B5357429 : Blo 2229435 5357429 := bbase (se 5 (by rfl) ⟨251129, by rfl⟩ : syracuseStep 5357429 = 502259) (by norm_num)
theorem B3571619 : Blo 2229435 3571619 := bstep (se 1 (by rfl) ⟨2678714, by rfl⟩ : syracuseStep 3571619 = 5357429) B5357429
theorem B9524317 : Blo 2229435 9524317 := bstep (se 3 (by rfl) ⟨1785809, by rfl⟩ : syracuseStep 9524317 = 3571619) B3571619
theorem B12699089 : Blo 2229435 12699089 := bstep (se 2 (by rfl) ⟨4762158, by rfl⟩ : syracuseStep 12699089 = 9524317) B9524317
theorem B8466059 : Blo 2229435 8466059 := bstep (se 1 (by rfl) ⟨6349544, by rfl⟩ : syracuseStep 8466059 = 12699089) B12699089
theorem B5644039 : Blo 2229435 5644039 := bstep (se 1 (by rfl) ⟨4233029, by rfl⟩ : syracuseStep 5644039 = 8466059) B8466059
theorem B7525385 : Blo 2229435 7525385 := bstep (se 2 (by rfl) ⟨2822019, by rfl⟩ : syracuseStep 7525385 = 5644039) B5644039
theorem B5016923 : Blo 2229435 5016923 := bstep (se 1 (by rfl) ⟨3762692, by rfl⟩ : syracuseStep 5016923 = 7525385) B7525385
theorem B3344615 : Blo 2229435 3344615 := bstep (se 1 (by rfl) ⟨2508461, by rfl⟩ : syracuseStep 3344615 = 5016923) B5016923
theorem B2229743 : Blo 2229435 2229743 := bstep (se 1 (by rfl) ⟨1672307, by rfl⟩ : syracuseStep 2229743 = 3344615) B3344615
theorem B3344621 : Blo 2229435 3344621 := bbase (se 3 (by rfl) ⟨627116, by rfl⟩ : syracuseStep 3344621 = 1254233) (by norm_num)
theorem B2229747 : Blo 2229435 2229747 := bstep (se 1 (by rfl) ⟨1672310, by rfl⟩ : syracuseStep 2229747 = 3344621) B3344621
theorem B5016941 : Blo 2229435 5016941 := bbase (se 3 (by rfl) ⟨940676, by rfl⟩ : syracuseStep 5016941 = 1881353) (by norm_num)
theorem B3344627 : Blo 2229435 3344627 := bstep (se 1 (by rfl) ⟨2508470, by rfl⟩ : syracuseStep 3344627 = 5016941) B5016941
theorem B2229751 : Blo 2229435 2229751 := bstep (se 1 (by rfl) ⟨1672313, by rfl⟩ : syracuseStep 2229751 = 3344627) B3344627
theorem B4233053 : Blo 2229435 4233053 := bbase (se 3 (by rfl) ⟨793697, by rfl⟩ : syracuseStep 4233053 = 1587395) (by norm_num)
theorem B2822035 : Blo 2229435 2822035 := bstep (se 1 (by rfl) ⟨2116526, by rfl⟩ : syracuseStep 2822035 = 4233053) B4233053
theorem B3762713 : Blo 2229435 3762713 := bstep (se 2 (by rfl) ⟨1411017, by rfl⟩ : syracuseStep 3762713 = 2822035) B2822035
theorem B2508475 : Blo 2229435 2508475 := bstep (se 1 (by rfl) ⟨1881356, by rfl⟩ : syracuseStep 2508475 = 3762713) B3762713
theorem B3344633 : Blo 2229435 3344633 := bstep (se 2 (by rfl) ⟨1254237, by rfl⟩ : syracuseStep 3344633 = 2508475) B2508475
theorem B2229755 : Blo 2229435 2229755 := bstep (se 1 (by rfl) ⟨1672316, by rfl⟩ : syracuseStep 2229755 = 3344633) B3344633
theorem B10714933 : Blo 2229435 10714933 := bbase (se 5 (by rfl) ⟨502262, by rfl⟩ : syracuseStep 10714933 = 1004525) (by norm_num)
theorem B57146309 : Blo 2229435 57146309 := bstep (se 4 (by rfl) ⟨5357466, by rfl⟩ : syracuseStep 57146309 = 10714933) B10714933
theorem B38097539 : Blo 2229435 38097539 := bstep (se 1 (by rfl) ⟨28573154, by rfl⟩ : syracuseStep 38097539 = 57146309) B57146309
theorem B25398359 : Blo 2229435 25398359 := bstep (se 1 (by rfl) ⟨19048769, by rfl⟩ : syracuseStep 25398359 = 38097539) B38097539
theorem B16932239 : Blo 2229435 16932239 := bstep (se 1 (by rfl) ⟨12699179, by rfl⟩ : syracuseStep 16932239 = 25398359) B25398359
theorem B11288159 : Blo 2229435 11288159 := bstep (se 1 (by rfl) ⟨8466119, by rfl⟩ : syracuseStep 11288159 = 16932239) B16932239
theorem B7525439 : Blo 2229435 7525439 := bstep (se 1 (by rfl) ⟨5644079, by rfl⟩ : syracuseStep 7525439 = 11288159) B11288159
theorem B5016959 : Blo 2229435 5016959 := bstep (se 1 (by rfl) ⟨3762719, by rfl⟩ : syracuseStep 5016959 = 7525439) B7525439
theorem B3344639 : Blo 2229435 3344639 := bstep (se 1 (by rfl) ⟨2508479, by rfl⟩ : syracuseStep 3344639 = 5016959) B5016959
theorem B2229759 : Blo 2229435 2229759 := bstep (se 1 (by rfl) ⟨1672319, by rfl⟩ : syracuseStep 2229759 = 3344639) B3344639
theorem B3344645 : Blo 2229435 3344645 := bbase (se 4 (by rfl) ⟨313560, by rfl⟩ : syracuseStep 3344645 = 627121) (by norm_num)
theorem B2229763 : Blo 2229435 2229763 := bstep (se 1 (by rfl) ⟨1672322, by rfl⟩ : syracuseStep 2229763 = 3344645) B3344645
theorem B3762733 : Blo 2229435 3762733 := bbase (se 3 (by rfl) ⟨705512, by rfl⟩ : syracuseStep 3762733 = 1411025) (by norm_num)
theorem B5016977 : Blo 2229435 5016977 := bstep (se 2 (by rfl) ⟨1881366, by rfl⟩ : syracuseStep 5016977 = 3762733) B3762733
theorem B3344651 : Blo 2229435 3344651 := bstep (se 1 (by rfl) ⟨2508488, by rfl⟩ : syracuseStep 3344651 = 5016977) B5016977
theorem B2229767 : Blo 2229435 2229767 := bstep (se 1 (by rfl) ⟨1672325, by rfl⟩ : syracuseStep 2229767 = 3344651) B3344651
theorem B2508493 : Blo 2229435 2508493 := bbase (se 3 (by rfl) ⟨470342, by rfl⟩ : syracuseStep 2508493 = 940685) (by norm_num)
theorem B3344657 : Blo 2229435 3344657 := bstep (se 2 (by rfl) ⟨1254246, by rfl⟩ : syracuseStep 3344657 = 2508493) B2508493
theorem B2229771 : Blo 2229435 2229771 := bstep (se 1 (by rfl) ⟨1672328, by rfl⟩ : syracuseStep 2229771 = 3344657) B3344657
theorem B7525493 : Blo 2229435 7525493 := bbase (se 5 (by rfl) ⟨352757, by rfl⟩ : syracuseStep 7525493 = 705515) (by norm_num)
theorem B5016995 : Blo 2229435 5016995 := bstep (se 1 (by rfl) ⟨3762746, by rfl⟩ : syracuseStep 5016995 = 7525493) B7525493
theorem B3344663 : Blo 2229435 3344663 := bstep (se 1 (by rfl) ⟨2508497, by rfl⟩ : syracuseStep 3344663 = 5016995) B5016995
theorem B2229775 : Blo 2229435 2229775 := bstep (se 1 (by rfl) ⟨1672331, by rfl⟩ : syracuseStep 2229775 = 3344663) B3344663
theorem B3344669 : Blo 2229435 3344669 := bbase (se 3 (by rfl) ⟨627125, by rfl⟩ : syracuseStep 3344669 = 1254251) (by norm_num)
theorem B2229779 : Blo 2229435 2229779 := bstep (se 1 (by rfl) ⟨1672334, by rfl⟩ : syracuseStep 2229779 = 3344669) B3344669
theorem B5017013 : Blo 2229435 5017013 := bbase (se 5 (by rfl) ⟨235172, by rfl⟩ : syracuseStep 5017013 = 470345) (by norm_num)
theorem B3344675 : Blo 2229435 3344675 := bstep (se 1 (by rfl) ⟨2508506, by rfl⟩ : syracuseStep 3344675 = 5017013) B5017013
theorem B2229783 : Blo 2229435 2229783 := bstep (se 1 (by rfl) ⟨1672337, by rfl⟩ : syracuseStep 2229783 = 3344675) B3344675
theorem B4762253 : Blo 2229435 4762253 := bbase (se 3 (by rfl) ⟨892922, by rfl⟩ : syracuseStep 4762253 = 1785845) (by norm_num)
theorem B12699341 : Blo 2229435 12699341 := bstep (se 3 (by rfl) ⟨2381126, by rfl⟩ : syracuseStep 12699341 = 4762253) B4762253
theorem B8466227 : Blo 2229435 8466227 := bstep (se 1 (by rfl) ⟨6349670, by rfl⟩ : syracuseStep 8466227 = 12699341) B12699341
theorem B5644151 : Blo 2229435 5644151 := bstep (se 1 (by rfl) ⟨4233113, by rfl⟩ : syracuseStep 5644151 = 8466227) B8466227
theorem B3762767 : Blo 2229435 3762767 := bstep (se 1 (by rfl) ⟨2822075, by rfl⟩ : syracuseStep 3762767 = 5644151) B5644151
theorem B2508511 : Blo 2229435 2508511 := bstep (se 1 (by rfl) ⟨1881383, by rfl⟩ : syracuseStep 2508511 = 3762767) B3762767
theorem B3344681 : Blo 2229435 3344681 := bstep (se 2 (by rfl) ⟨1254255, by rfl⟩ : syracuseStep 3344681 = 2508511) B2508511
theorem B2229787 : Blo 2229435 2229787 := bstep (se 1 (by rfl) ⟨1672340, by rfl⟩ : syracuseStep 2229787 = 3344681) B3344681
theorem B4762261 : Blo 2229435 4762261 := bbase (se 6 (by rfl) ⟨111615, by rfl⟩ : syracuseStep 4762261 = 223231) (by norm_num)
theorem B6349681 : Blo 2229435 6349681 := bstep (se 2 (by rfl) ⟨2381130, by rfl⟩ : syracuseStep 6349681 = 4762261) B4762261
theorem B8466241 : Blo 2229435 8466241 := bstep (se 2 (by rfl) ⟨3174840, by rfl⟩ : syracuseStep 8466241 = 6349681) B6349681
theorem B11288321 : Blo 2229435 11288321 := bstep (se 2 (by rfl) ⟨4233120, by rfl⟩ : syracuseStep 11288321 = 8466241) B8466241
theorem B7525547 : Blo 2229435 7525547 := bstep (se 1 (by rfl) ⟨5644160, by rfl⟩ : syracuseStep 7525547 = 11288321) B11288321
theorem B5017031 : Blo 2229435 5017031 := bstep (se 1 (by rfl) ⟨3762773, by rfl⟩ : syracuseStep 5017031 = 7525547) B7525547
theorem B3344687 : Blo 2229435 3344687 := bstep (se 1 (by rfl) ⟨2508515, by rfl⟩ : syracuseStep 3344687 = 5017031) B5017031
theorem B2229791 : Blo 2229435 2229791 := bstep (se 1 (by rfl) ⟨1672343, by rfl⟩ : syracuseStep 2229791 = 3344687) B3344687
theorem B3344693 : Blo 2229435 3344693 := bbase (se 5 (by rfl) ⟨156782, by rfl⟩ : syracuseStep 3344693 = 313565) (by norm_num)
theorem B2229795 : Blo 2229435 2229795 := bstep (se 1 (by rfl) ⟨1672346, by rfl⟩ : syracuseStep 2229795 = 3344693) B3344693
theorem B5644181 : Blo 2229435 5644181 := bbase (se 6 (by rfl) ⟨132285, by rfl⟩ : syracuseStep 5644181 = 264571) (by norm_num)
theorem B3762787 : Blo 2229435 3762787 := bstep (se 1 (by rfl) ⟨2822090, by rfl⟩ : syracuseStep 3762787 = 5644181) B5644181
theorem B5017049 : Blo 2229435 5017049 := bstep (se 2 (by rfl) ⟨1881393, by rfl⟩ : syracuseStep 5017049 = 3762787) B3762787
theorem B3344699 : Blo 2229435 3344699 := bstep (se 1 (by rfl) ⟨2508524, by rfl⟩ : syracuseStep 3344699 = 5017049) B5017049
theorem B2229799 : Blo 2229435 2229799 := bstep (se 1 (by rfl) ⟨1672349, by rfl⟩ : syracuseStep 2229799 = 3344699) B3344699
theorem B2508529 : Blo 2229435 2508529 := bbase (se 2 (by rfl) ⟨940698, by rfl⟩ : syracuseStep 2508529 = 1881397) (by norm_num)
theorem B3344705 : Blo 2229435 3344705 := bstep (se 2 (by rfl) ⟨1254264, by rfl⟩ : syracuseStep 3344705 = 2508529) B2508529
theorem B2229803 : Blo 2229435 2229803 := bstep (se 1 (by rfl) ⟨1672352, by rfl⟩ : syracuseStep 2229803 = 3344705) B3344705
theorem B8146021 : Blo 2229435 8146021 := bbase (se 4 (by rfl) ⟨763689, by rfl⟩ : syracuseStep 8146021 = 1527379) (by norm_num)
theorem B10861361 : Blo 2229435 10861361 := bstep (se 2 (by rfl) ⟨4073010, by rfl⟩ : syracuseStep 10861361 = 8146021) B8146021
theorem B7240907 : Blo 2229435 7240907 := bstep (se 1 (by rfl) ⟨5430680, by rfl⟩ : syracuseStep 7240907 = 10861361) B10861361
theorem B4827271 : Blo 2229435 4827271 := bstep (se 1 (by rfl) ⟨3620453, by rfl⟩ : syracuseStep 4827271 = 7240907) B7240907
theorem B6436361 : Blo 2229435 6436361 := bstep (se 2 (by rfl) ⟨2413635, by rfl⟩ : syracuseStep 6436361 = 4827271) B4827271
theorem B4290907 : Blo 2229435 4290907 := bstep (se 1 (by rfl) ⟨3218180, by rfl⟩ : syracuseStep 4290907 = 6436361) B6436361
theorem B5721209 : Blo 2229435 5721209 := bstep (se 2 (by rfl) ⟨2145453, by rfl⟩ : syracuseStep 5721209 = 4290907) B4290907
theorem B3814139 : Blo 2229435 3814139 := bstep (se 1 (by rfl) ⟨2860604, by rfl⟩ : syracuseStep 3814139 = 5721209) B5721209
theorem B10171037 : Blo 2229435 10171037 := bstep (se 3 (by rfl) ⟨1907069, by rfl⟩ : syracuseStep 10171037 = 3814139) B3814139
theorem B6780691 : Blo 2229435 6780691 := bstep (se 1 (by rfl) ⟨5085518, by rfl⟩ : syracuseStep 6780691 = 10171037) B10171037
theorem B36163685 : Blo 2229435 36163685 := bstep (se 4 (by rfl) ⟨3390345, by rfl⟩ : syracuseStep 36163685 = 6780691) B6780691
theorem B24109123 : Blo 2229435 24109123 := bstep (se 1 (by rfl) ⟨18081842, by rfl⟩ : syracuseStep 24109123 = 36163685) B36163685
theorem B32145497 : Blo 2229435 32145497 := bstep (se 2 (by rfl) ⟨12054561, by rfl⟩ : syracuseStep 32145497 = 24109123) B24109123
theorem B21430331 : Blo 2229435 21430331 := bstep (se 1 (by rfl) ⟨16072748, by rfl⟩ : syracuseStep 21430331 = 32145497) B32145497
theorem B14286887 : Blo 2229435 14286887 := bstep (se 1 (by rfl) ⟨10715165, by rfl⟩ : syracuseStep 14286887 = 21430331) B21430331
theorem B9524591 : Blo 2229435 9524591 := bstep (se 1 (by rfl) ⟨7143443, by rfl⟩ : syracuseStep 9524591 = 14286887) B14286887
theorem B6349727 : Blo 2229435 6349727 := bstep (se 1 (by rfl) ⟨4762295, by rfl⟩ : syracuseStep 6349727 = 9524591) B9524591
theorem B4233151 : Blo 2229435 4233151 := bstep (se 1 (by rfl) ⟨3174863, by rfl⟩ : syracuseStep 4233151 = 6349727) B6349727
theorem B5644201 : Blo 2229435 5644201 := bstep (se 2 (by rfl) ⟨2116575, by rfl⟩ : syracuseStep 5644201 = 4233151) B4233151
theorem B7525601 : Blo 2229435 7525601 := bstep (se 2 (by rfl) ⟨2822100, by rfl⟩ : syracuseStep 7525601 = 5644201) B5644201
theorem B5017067 : Blo 2229435 5017067 := bstep (se 1 (by rfl) ⟨3762800, by rfl⟩ : syracuseStep 5017067 = 7525601) B7525601
theorem B3344711 : Blo 2229435 3344711 := bstep (se 1 (by rfl) ⟨2508533, by rfl⟩ : syracuseStep 3344711 = 5017067) B5017067
theorem B2229807 : Blo 2229435 2229807 := bstep (se 1 (by rfl) ⟨1672355, by rfl⟩ : syracuseStep 2229807 = 3344711) B3344711
theorem B3344717 : Blo 2229435 3344717 := bbase (se 3 (by rfl) ⟨627134, by rfl⟩ : syracuseStep 3344717 = 1254269) (by norm_num)
theorem B2229811 : Blo 2229435 2229811 := bstep (se 1 (by rfl) ⟨1672358, by rfl⟩ : syracuseStep 2229811 = 3344717) B3344717
theorem B5017085 : Blo 2229435 5017085 := bbase (se 3 (by rfl) ⟨940703, by rfl⟩ : syracuseStep 5017085 = 1881407) (by norm_num)
theorem B3344723 : Blo 2229435 3344723 := bstep (se 1 (by rfl) ⟨2508542, by rfl⟩ : syracuseStep 3344723 = 5017085) B5017085
theorem B2229815 : Blo 2229435 2229815 := bstep (se 1 (by rfl) ⟨1672361, by rfl⟩ : syracuseStep 2229815 = 3344723) B3344723
theorem B3762821 : Blo 2229435 3762821 := bbase (se 4 (by rfl) ⟨352764, by rfl⟩ : syracuseStep 3762821 = 705529) (by norm_num)
theorem B2508547 : Blo 2229435 2508547 := bstep (se 1 (by rfl) ⟨1881410, by rfl⟩ : syracuseStep 2508547 = 3762821) B3762821
theorem B3344729 : Blo 2229435 3344729 := bstep (se 2 (by rfl) ⟨1254273, by rfl⟩ : syracuseStep 3344729 = 2508547) B2508547
theorem B2229819 : Blo 2229435 2229819 := bstep (se 1 (by rfl) ⟨1672364, by rfl⟩ : syracuseStep 2229819 = 3344729) B3344729
theorem B16932725 : Blo 2229435 16932725 := bbase (se 5 (by rfl) ⟨793721, by rfl⟩ : syracuseStep 16932725 = 1587443) (by norm_num)
theorem B11288483 : Blo 2229435 11288483 := bstep (se 1 (by rfl) ⟨8466362, by rfl⟩ : syracuseStep 11288483 = 16932725) B16932725
theorem B7525655 : Blo 2229435 7525655 := bstep (se 1 (by rfl) ⟨5644241, by rfl⟩ : syracuseStep 7525655 = 11288483) B11288483
theorem B5017103 : Blo 2229435 5017103 := bstep (se 1 (by rfl) ⟨3762827, by rfl⟩ : syracuseStep 5017103 = 7525655) B7525655
theorem B3344735 : Blo 2229435 3344735 := bstep (se 1 (by rfl) ⟨2508551, by rfl⟩ : syracuseStep 3344735 = 5017103) B5017103
theorem B2229823 : Blo 2229435 2229823 := bstep (se 1 (by rfl) ⟨1672367, by rfl⟩ : syracuseStep 2229823 = 3344735) B3344735
theorem B3344741 : Blo 2229435 3344741 := bbase (se 4 (by rfl) ⟨313569, by rfl⟩ : syracuseStep 3344741 = 627139) (by norm_num)
theorem B2229827 : Blo 2229435 2229827 := bstep (se 1 (by rfl) ⟨1672370, by rfl⟩ : syracuseStep 2229827 = 3344741) B3344741
theorem B4233197 : Blo 2229435 4233197 := bbase (se 3 (by rfl) ⟨793724, by rfl⟩ : syracuseStep 4233197 = 1587449) (by norm_num)
theorem B2822131 : Blo 2229435 2822131 := bstep (se 1 (by rfl) ⟨2116598, by rfl⟩ : syracuseStep 2822131 = 4233197) B4233197
theorem B3762841 : Blo 2229435 3762841 := bstep (se 2 (by rfl) ⟨1411065, by rfl⟩ : syracuseStep 3762841 = 2822131) B2822131
theorem B5017121 : Blo 2229435 5017121 := bstep (se 2 (by rfl) ⟨1881420, by rfl⟩ : syracuseStep 5017121 = 3762841) B3762841
theorem B3344747 : Blo 2229435 3344747 := bstep (se 1 (by rfl) ⟨2508560, by rfl⟩ : syracuseStep 3344747 = 5017121) B5017121
theorem B2229831 : Blo 2229435 2229831 := bstep (se 1 (by rfl) ⟨1672373, by rfl⟩ : syracuseStep 2229831 = 3344747) B3344747
theorem B2508565 : Blo 2229435 2508565 := bbase (se 6 (by rfl) ⟨58794, by rfl⟩ : syracuseStep 2508565 = 117589) (by norm_num)
theorem B3344753 : Blo 2229435 3344753 := bstep (se 2 (by rfl) ⟨1254282, by rfl⟩ : syracuseStep 3344753 = 2508565) B2508565
theorem B2229835 : Blo 2229435 2229835 := bstep (se 1 (by rfl) ⟨1672376, by rfl⟩ : syracuseStep 2229835 = 3344753) B3344753
theorem B2822141 : Blo 2229435 2822141 := bbase (se 3 (by rfl) ⟨529151, by rfl⟩ : syracuseStep 2822141 = 1058303) (by norm_num)
theorem B7525709 : Blo 2229435 7525709 := bstep (se 3 (by rfl) ⟨1411070, by rfl⟩ : syracuseStep 7525709 = 2822141) B2822141
theorem B5017139 : Blo 2229435 5017139 := bstep (se 1 (by rfl) ⟨3762854, by rfl⟩ : syracuseStep 5017139 = 7525709) B7525709
theorem B3344759 : Blo 2229435 3344759 := bstep (se 1 (by rfl) ⟨2508569, by rfl⟩ : syracuseStep 3344759 = 5017139) B5017139
theorem B2229839 : Blo 2229435 2229839 := bstep (se 1 (by rfl) ⟨1672379, by rfl⟩ : syracuseStep 2229839 = 3344759) B3344759
theorem B3344765 : Blo 2229435 3344765 := bbase (se 3 (by rfl) ⟨627143, by rfl⟩ : syracuseStep 3344765 = 1254287) (by norm_num)
theorem B2229843 : Blo 2229435 2229843 := bstep (se 1 (by rfl) ⟨1672382, by rfl⟩ : syracuseStep 2229843 = 3344765) B3344765
theorem B5017157 : Blo 2229435 5017157 := bbase (se 4 (by rfl) ⟨470358, by rfl⟩ : syracuseStep 5017157 = 940717) (by norm_num)
theorem B3344771 : Blo 2229435 3344771 := bstep (se 1 (by rfl) ⟨2508578, by rfl⟩ : syracuseStep 3344771 = 5017157) B5017157
theorem B2229847 : Blo 2229435 2229847 := bstep (se 1 (by rfl) ⟨1672385, by rfl⟩ : syracuseStep 2229847 = 3344771) B3344771
theorem B2678845 : Blo 2229435 2678845 := bbase (se 3 (by rfl) ⟨502283, by rfl⟩ : syracuseStep 2678845 = 1004567) (by norm_num)
theorem B3571793 : Blo 2229435 3571793 := bstep (se 2 (by rfl) ⟨1339422, by rfl⟩ : syracuseStep 3571793 = 2678845) B2678845
theorem B2381195 : Blo 2229435 2381195 := bstep (se 1 (by rfl) ⟨1785896, by rfl⟩ : syracuseStep 2381195 = 3571793) B3571793
theorem B6349853 : Blo 2229435 6349853 := bstep (se 3 (by rfl) ⟨1190597, by rfl⟩ : syracuseStep 6349853 = 2381195) B2381195
theorem B4233235 : Blo 2229435 4233235 := bstep (se 1 (by rfl) ⟨3174926, by rfl⟩ : syracuseStep 4233235 = 6349853) B6349853
theorem B5644313 : Blo 2229435 5644313 := bstep (se 2 (by rfl) ⟨2116617, by rfl⟩ : syracuseStep 5644313 = 4233235) B4233235
theorem B3762875 : Blo 2229435 3762875 := bstep (se 1 (by rfl) ⟨2822156, by rfl⟩ : syracuseStep 3762875 = 5644313) B5644313
theorem B2508583 : Blo 2229435 2508583 := bstep (se 1 (by rfl) ⟨1881437, by rfl⟩ : syracuseStep 2508583 = 3762875) B3762875
theorem B3344777 : Blo 2229435 3344777 := bstep (se 2 (by rfl) ⟨1254291, by rfl⟩ : syracuseStep 3344777 = 2508583) B2508583
theorem B2229851 : Blo 2229435 2229851 := bstep (se 1 (by rfl) ⟨1672388, by rfl⟩ : syracuseStep 2229851 = 3344777) B3344777
theorem B11288645 : Blo 2229435 11288645 := bbase (se 4 (by rfl) ⟨1058310, by rfl⟩ : syracuseStep 11288645 = 2116621) (by norm_num)
theorem B7525763 : Blo 2229435 7525763 := bstep (se 1 (by rfl) ⟨5644322, by rfl⟩ : syracuseStep 7525763 = 11288645) B11288645
theorem B5017175 : Blo 2229435 5017175 := bstep (se 1 (by rfl) ⟨3762881, by rfl⟩ : syracuseStep 5017175 = 7525763) B7525763
theorem B3344783 : Blo 2229435 3344783 := bstep (se 1 (by rfl) ⟨2508587, by rfl⟩ : syracuseStep 3344783 = 5017175) B5017175
theorem B2229855 : Blo 2229435 2229855 := bstep (se 1 (by rfl) ⟨1672391, by rfl⟩ : syracuseStep 2229855 = 3344783) B3344783
theorem B3344789 : Blo 2229435 3344789 := bbase (se 6 (by rfl) ⟨78393, by rfl⟩ : syracuseStep 3344789 = 156787) (by norm_num)
theorem B2229859 : Blo 2229435 2229859 := bstep (se 1 (by rfl) ⟨1672394, by rfl⟩ : syracuseStep 2229859 = 3344789) B3344789
theorem B4582253 : Blo 2229435 4582253 := bbase (se 3 (by rfl) ⟨859172, by rfl⟩ : syracuseStep 4582253 = 1718345) (by norm_num)
theorem B3054835 : Blo 2229435 3054835 := bstep (se 1 (by rfl) ⟨2291126, by rfl⟩ : syracuseStep 3054835 = 4582253) B4582253
theorem B4073113 : Blo 2229435 4073113 := bstep (se 2 (by rfl) ⟨1527417, by rfl⟩ : syracuseStep 4073113 = 3054835) B3054835
theorem B5430817 : Blo 2229435 5430817 := bstep (se 2 (by rfl) ⟨2036556, by rfl⟩ : syracuseStep 5430817 = 4073113) B4073113
theorem B7241089 : Blo 2229435 7241089 := bstep (se 2 (by rfl) ⟨2715408, by rfl⟩ : syracuseStep 7241089 = 5430817) B5430817
theorem B9654785 : Blo 2229435 9654785 := bstep (se 2 (by rfl) ⟨3620544, by rfl⟩ : syracuseStep 9654785 = 7241089) B7241089
theorem B6436523 : Blo 2229435 6436523 := bstep (se 1 (by rfl) ⟨4827392, by rfl⟩ : syracuseStep 6436523 = 9654785) B9654785
theorem B17164061 : Blo 2229435 17164061 := bstep (se 3 (by rfl) ⟨3218261, by rfl⟩ : syracuseStep 17164061 = 6436523) B6436523
theorem B11442707 : Blo 2229435 11442707 := bstep (se 1 (by rfl) ⟨8582030, by rfl⟩ : syracuseStep 11442707 = 17164061) B17164061
theorem B7628471 : Blo 2229435 7628471 := bstep (se 1 (by rfl) ⟨5721353, by rfl⟩ : syracuseStep 7628471 = 11442707) B11442707
theorem B5085647 : Blo 2229435 5085647 := bstep (se 1 (by rfl) ⟨3814235, by rfl⟩ : syracuseStep 5085647 = 7628471) B7628471
theorem B3390431 : Blo 2229435 3390431 := bstep (se 1 (by rfl) ⟨2542823, by rfl⟩ : syracuseStep 3390431 = 5085647) B5085647
theorem B9041149 : Blo 2229435 9041149 := bstep (se 3 (by rfl) ⟨1695215, by rfl⟩ : syracuseStep 9041149 = 3390431) B3390431
theorem B12054865 : Blo 2229435 12054865 := bstep (se 2 (by rfl) ⟨4520574, by rfl⟩ : syracuseStep 12054865 = 9041149) B9041149
theorem B16073153 : Blo 2229435 16073153 := bstep (se 2 (by rfl) ⟨6027432, by rfl⟩ : syracuseStep 16073153 = 12054865) B12054865
theorem B10715435 : Blo 2229435 10715435 := bstep (se 1 (by rfl) ⟨8036576, by rfl⟩ : syracuseStep 10715435 = 16073153) B16073153
theorem B7143623 : Blo 2229435 7143623 := bstep (se 1 (by rfl) ⟨5357717, by rfl⟩ : syracuseStep 7143623 = 10715435) B10715435
theorem B4762415 : Blo 2229435 4762415 := bstep (se 1 (by rfl) ⟨3571811, by rfl⟩ : syracuseStep 4762415 = 7143623) B7143623
theorem B12699773 : Blo 2229435 12699773 := bstep (se 3 (by rfl) ⟨2381207, by rfl⟩ : syracuseStep 12699773 = 4762415) B4762415
theorem B8466515 : Blo 2229435 8466515 := bstep (se 1 (by rfl) ⟨6349886, by rfl⟩ : syracuseStep 8466515 = 12699773) B12699773
theorem B5644343 : Blo 2229435 5644343 := bstep (se 1 (by rfl) ⟨4233257, by rfl⟩ : syracuseStep 5644343 = 8466515) B8466515
theorem B3762895 : Blo 2229435 3762895 := bstep (se 1 (by rfl) ⟨2822171, by rfl⟩ : syracuseStep 3762895 = 5644343) B5644343
theorem B5017193 : Blo 2229435 5017193 := bstep (se 2 (by rfl) ⟨1881447, by rfl⟩ : syracuseStep 5017193 = 3762895) B3762895
theorem B3344795 : Blo 2229435 3344795 := bstep (se 1 (by rfl) ⟨2508596, by rfl⟩ : syracuseStep 3344795 = 5017193) B5017193
theorem B2229863 : Blo 2229435 2229863 := bstep (se 1 (by rfl) ⟨1672397, by rfl⟩ : syracuseStep 2229863 = 3344795) B3344795
theorem B2508601 : Blo 2229435 2508601 := bbase (se 2 (by rfl) ⟨940725, by rfl⟩ : syracuseStep 2508601 = 1881451) (by norm_num)
theorem B3344801 : Blo 2229435 3344801 := bstep (se 2 (by rfl) ⟨1254300, by rfl⟩ : syracuseStep 3344801 = 2508601) B2508601
theorem B2229867 : Blo 2229435 2229867 := bstep (se 1 (by rfl) ⟨1672400, by rfl⟩ : syracuseStep 2229867 = 3344801) B3344801
theorem B6349909 : Blo 2229435 6349909 := bbase (se 8 (by rfl) ⟨37206, by rfl⟩ : syracuseStep 6349909 = 74413) (by norm_num)
theorem B8466545 : Blo 2229435 8466545 := bstep (se 2 (by rfl) ⟨3174954, by rfl⟩ : syracuseStep 8466545 = 6349909) B6349909
theorem B5644363 : Blo 2229435 5644363 := bstep (se 1 (by rfl) ⟨4233272, by rfl⟩ : syracuseStep 5644363 = 8466545) B8466545
theorem B7525817 : Blo 2229435 7525817 := bstep (se 2 (by rfl) ⟨2822181, by rfl⟩ : syracuseStep 7525817 = 5644363) B5644363
theorem B5017211 : Blo 2229435 5017211 := bstep (se 1 (by rfl) ⟨3762908, by rfl⟩ : syracuseStep 5017211 = 7525817) B7525817
theorem B3344807 : Blo 2229435 3344807 := bstep (se 1 (by rfl) ⟨2508605, by rfl⟩ : syracuseStep 3344807 = 5017211) B5017211
theorem B2229871 : Blo 2229435 2229871 := bstep (se 1 (by rfl) ⟨1672403, by rfl⟩ : syracuseStep 2229871 = 3344807) B3344807
theorem B3344813 : Blo 2229435 3344813 := bbase (se 3 (by rfl) ⟨627152, by rfl⟩ : syracuseStep 3344813 = 1254305) (by norm_num)
theorem B2229875 : Blo 2229435 2229875 := bstep (se 1 (by rfl) ⟨1672406, by rfl⟩ : syracuseStep 2229875 = 3344813) B3344813
theorem B5017229 : Blo 2229435 5017229 := bbase (se 3 (by rfl) ⟨940730, by rfl⟩ : syracuseStep 5017229 = 1881461) (by norm_num)
theorem B3344819 : Blo 2229435 3344819 := bstep (se 1 (by rfl) ⟨2508614, by rfl⟩ : syracuseStep 3344819 = 5017229) B5017229
theorem B2229879 : Blo 2229435 2229879 := bstep (se 1 (by rfl) ⟨1672409, by rfl⟩ : syracuseStep 2229879 = 3344819) B3344819
theorem B2822197 : Blo 2229435 2822197 := bbase (se 5 (by rfl) ⟨132290, by rfl⟩ : syracuseStep 2822197 = 264581) (by norm_num)
theorem B3762929 : Blo 2229435 3762929 := bstep (se 2 (by rfl) ⟨1411098, by rfl⟩ : syracuseStep 3762929 = 2822197) B2822197
theorem B2508619 : Blo 2229435 2508619 := bstep (se 1 (by rfl) ⟨1881464, by rfl⟩ : syracuseStep 2508619 = 3762929) B3762929
theorem B3344825 : Blo 2229435 3344825 := bstep (se 2 (by rfl) ⟨1254309, by rfl⟩ : syracuseStep 3344825 = 2508619) B2508619
theorem B2229883 : Blo 2229435 2229883 := bstep (se 1 (by rfl) ⟨1672412, by rfl⟩ : syracuseStep 2229883 = 3344825) B3344825
theorem B32146645 : Blo 2229435 32146645 := bbase (se 7 (by rfl) ⟨376718, by rfl⟩ : syracuseStep 32146645 = 753437) (by norm_num)
theorem B42862193 : Blo 2229435 42862193 := bstep (se 2 (by rfl) ⟨16073322, by rfl⟩ : syracuseStep 42862193 = 32146645) B32146645
theorem B28574795 : Blo 2229435 28574795 := bstep (se 1 (by rfl) ⟨21431096, by rfl⟩ : syracuseStep 28574795 = 42862193) B42862193
theorem B19049863 : Blo 2229435 19049863 := bstep (se 1 (by rfl) ⟨14287397, by rfl⟩ : syracuseStep 19049863 = 28574795) B28574795
theorem B25399817 : Blo 2229435 25399817 := bstep (se 2 (by rfl) ⟨9524931, by rfl⟩ : syracuseStep 25399817 = 19049863) B19049863
theorem B16933211 : Blo 2229435 16933211 := bstep (se 1 (by rfl) ⟨12699908, by rfl⟩ : syracuseStep 16933211 = 25399817) B25399817
theorem B11288807 : Blo 2229435 11288807 := bstep (se 1 (by rfl) ⟨8466605, by rfl⟩ : syracuseStep 11288807 = 16933211) B16933211
theorem B7525871 : Blo 2229435 7525871 := bstep (se 1 (by rfl) ⟨5644403, by rfl⟩ : syracuseStep 7525871 = 11288807) B11288807
theorem B5017247 : Blo 2229435 5017247 := bstep (se 1 (by rfl) ⟨3762935, by rfl⟩ : syracuseStep 5017247 = 7525871) B7525871
theorem B3344831 : Blo 2229435 3344831 := bstep (se 1 (by rfl) ⟨2508623, by rfl⟩ : syracuseStep 3344831 = 5017247) B5017247
theorem B2229887 : Blo 2229435 2229887 := bstep (se 1 (by rfl) ⟨1672415, by rfl⟩ : syracuseStep 2229887 = 3344831) B3344831
theorem B3344837 : Blo 2229435 3344837 := bbase (se 4 (by rfl) ⟨313578, by rfl⟩ : syracuseStep 3344837 = 627157) (by norm_num)
theorem B2229891 : Blo 2229435 2229891 := bstep (se 1 (by rfl) ⟨1672418, by rfl⟩ : syracuseStep 2229891 = 3344837) B3344837
theorem B3762949 : Blo 2229435 3762949 := bbase (se 4 (by rfl) ⟨352776, by rfl⟩ : syracuseStep 3762949 = 705553) (by norm_num)
theorem B5017265 : Blo 2229435 5017265 := bstep (se 2 (by rfl) ⟨1881474, by rfl⟩ : syracuseStep 5017265 = 3762949) B3762949
theorem B3344843 : Blo 2229435 3344843 := bstep (se 1 (by rfl) ⟨2508632, by rfl⟩ : syracuseStep 3344843 = 5017265) B5017265
theorem B2229895 : Blo 2229435 2229895 := bstep (se 1 (by rfl) ⟨1672421, by rfl⟩ : syracuseStep 2229895 = 3344843) B3344843
theorem B2508637 : Blo 2229435 2508637 := bbase (se 3 (by rfl) ⟨470369, by rfl⟩ : syracuseStep 2508637 = 940739) (by norm_num)
theorem B3344849 : Blo 2229435 3344849 := bstep (se 2 (by rfl) ⟨1254318, by rfl⟩ : syracuseStep 3344849 = 2508637) B2508637
theorem B2229899 : Blo 2229435 2229899 := bstep (se 1 (by rfl) ⟨1672424, by rfl⟩ : syracuseStep 2229899 = 3344849) B3344849
theorem B7525925 : Blo 2229435 7525925 := bbase (se 4 (by rfl) ⟨705555, by rfl⟩ : syracuseStep 7525925 = 1411111) (by norm_num)
theorem B5017283 : Blo 2229435 5017283 := bstep (se 1 (by rfl) ⟨3762962, by rfl⟩ : syracuseStep 5017283 = 7525925) B7525925
theorem B3344855 : Blo 2229435 3344855 := bstep (se 1 (by rfl) ⟨2508641, by rfl⟩ : syracuseStep 3344855 = 5017283) B5017283
theorem B2229903 : Blo 2229435 2229903 := bstep (se 1 (by rfl) ⟨1672427, by rfl⟩ : syracuseStep 2229903 = 3344855) B3344855
theorem B3344861 : Blo 2229435 3344861 := bbase (se 3 (by rfl) ⟨627161, by rfl⟩ : syracuseStep 3344861 = 1254323) (by norm_num)
theorem B2229907 : Blo 2229435 2229907 := bstep (se 1 (by rfl) ⟨1672430, by rfl⟩ : syracuseStep 2229907 = 3344861) B3344861
theorem B5017301 : Blo 2229435 5017301 := bbase (se 7 (by rfl) ⟨58796, by rfl⟩ : syracuseStep 5017301 = 117593) (by norm_num)
theorem B3344867 : Blo 2229435 3344867 := bstep (se 1 (by rfl) ⟨2508650, by rfl⟩ : syracuseStep 3344867 = 5017301) B5017301
theorem B2229911 : Blo 2229435 2229911 := bstep (se 1 (by rfl) ⟨1672433, by rfl⟩ : syracuseStep 2229911 = 3344867) B3344867
theorem B9655013 : Blo 2229435 9655013 := bbase (se 4 (by rfl) ⟨905157, by rfl⟩ : syracuseStep 9655013 = 1810315) (by norm_num)
theorem B6436675 : Blo 2229435 6436675 := bstep (se 1 (by rfl) ⟨4827506, by rfl⟩ : syracuseStep 6436675 = 9655013) B9655013
theorem B8582233 : Blo 2229435 8582233 := bstep (se 2 (by rfl) ⟨3218337, by rfl⟩ : syracuseStep 8582233 = 6436675) B6436675
theorem B11442977 : Blo 2229435 11442977 := bstep (se 2 (by rfl) ⟨4291116, by rfl⟩ : syracuseStep 11442977 = 8582233) B8582233
theorem B7628651 : Blo 2229435 7628651 := bstep (se 1 (by rfl) ⟨5721488, by rfl⟩ : syracuseStep 7628651 = 11442977) B11442977
theorem B5085767 : Blo 2229435 5085767 := bstep (se 1 (by rfl) ⟨3814325, by rfl⟩ : syracuseStep 5085767 = 7628651) B7628651
theorem B3390511 : Blo 2229435 3390511 := bstep (se 1 (by rfl) ⟨2542883, by rfl⟩ : syracuseStep 3390511 = 5085767) B5085767
theorem B4520681 : Blo 2229435 4520681 := bstep (se 2 (by rfl) ⟨1695255, by rfl⟩ : syracuseStep 4520681 = 3390511) B3390511
theorem B3013787 : Blo 2229435 3013787 := bstep (se 1 (by rfl) ⟨2260340, by rfl⟩ : syracuseStep 3013787 = 4520681) B4520681
theorem B8036765 : Blo 2229435 8036765 := bstep (se 3 (by rfl) ⟨1506893, by rfl⟩ : syracuseStep 8036765 = 3013787) B3013787
theorem B5357843 : Blo 2229435 5357843 := bstep (se 1 (by rfl) ⟨4018382, by rfl⟩ : syracuseStep 5357843 = 8036765) B8036765
theorem B3571895 : Blo 2229435 3571895 := bstep (se 1 (by rfl) ⟨2678921, by rfl⟩ : syracuseStep 3571895 = 5357843) B5357843
theorem B9525053 : Blo 2229435 9525053 := bstep (se 3 (by rfl) ⟨1785947, by rfl⟩ : syracuseStep 9525053 = 3571895) B3571895
theorem B6350035 : Blo 2229435 6350035 := bstep (se 1 (by rfl) ⟨4762526, by rfl⟩ : syracuseStep 6350035 = 9525053) B9525053
theorem B8466713 : Blo 2229435 8466713 := bstep (se 2 (by rfl) ⟨3175017, by rfl⟩ : syracuseStep 8466713 = 6350035) B6350035
theorem B5644475 : Blo 2229435 5644475 := bstep (se 1 (by rfl) ⟨4233356, by rfl⟩ : syracuseStep 5644475 = 8466713) B8466713
theorem B3762983 : Blo 2229435 3762983 := bstep (se 1 (by rfl) ⟨2822237, by rfl⟩ : syracuseStep 3762983 = 5644475) B5644475
theorem B2508655 : Blo 2229435 2508655 := bstep (se 1 (by rfl) ⟨1881491, by rfl⟩ : syracuseStep 2508655 = 3762983) B3762983
theorem B3344873 : Blo 2229435 3344873 := bstep (se 2 (by rfl) ⟨1254327, by rfl⟩ : syracuseStep 3344873 = 2508655) B2508655
theorem B2229915 : Blo 2229435 2229915 := bstep (se 1 (by rfl) ⟨1672436, by rfl⟩ : syracuseStep 2229915 = 3344873) B3344873
theorem B5799557 : Blo 2229435 5799557 := bbase (se 4 (by rfl) ⟨543708, by rfl⟩ : syracuseStep 5799557 = 1087417) (by norm_num)
theorem B15465485 : Blo 2229435 15465485 := bstep (se 3 (by rfl) ⟨2899778, by rfl⟩ : syracuseStep 15465485 = 5799557) B5799557
theorem B10310323 : Blo 2229435 10310323 := bstep (se 1 (by rfl) ⟨7732742, by rfl⟩ : syracuseStep 10310323 = 15465485) B15465485
theorem B13747097 : Blo 2229435 13747097 := bstep (se 2 (by rfl) ⟨5155161, by rfl⟩ : syracuseStep 13747097 = 10310323) B10310323
theorem B9164731 : Blo 2229435 9164731 := bstep (se 1 (by rfl) ⟨6873548, by rfl⟩ : syracuseStep 9164731 = 13747097) B13747097
theorem B12219641 : Blo 2229435 12219641 := bstep (se 2 (by rfl) ⟨4582365, by rfl⟩ : syracuseStep 12219641 = 9164731) B9164731
theorem B8146427 : Blo 2229435 8146427 := bstep (se 1 (by rfl) ⟨6109820, by rfl⟩ : syracuseStep 8146427 = 12219641) B12219641
theorem B21723805 : Blo 2229435 21723805 := bstep (se 3 (by rfl) ⟨4073213, by rfl⟩ : syracuseStep 21723805 = 8146427) B8146427
theorem B28965073 : Blo 2229435 28965073 := bstep (se 2 (by rfl) ⟨10861902, by rfl⟩ : syracuseStep 28965073 = 21723805) B21723805
theorem B38620097 : Blo 2229435 38620097 := bstep (se 2 (by rfl) ⟨14482536, by rfl⟩ : syracuseStep 38620097 = 28965073) B28965073
theorem B25746731 : Blo 2229435 25746731 := bstep (se 1 (by rfl) ⟨19310048, by rfl⟩ : syracuseStep 25746731 = 38620097) B38620097
theorem B17164487 : Blo 2229435 17164487 := bstep (se 1 (by rfl) ⟨12873365, by rfl⟩ : syracuseStep 17164487 = 25746731) B25746731
theorem B45771965 : Blo 2229435 45771965 := bstep (se 3 (by rfl) ⟨8582243, by rfl⟩ : syracuseStep 45771965 = 17164487) B17164487
theorem B30514643 : Blo 2229435 30514643 := bstep (se 1 (by rfl) ⟨22885982, by rfl⟩ : syracuseStep 30514643 = 45771965) B45771965
theorem B20343095 : Blo 2229435 20343095 := bstep (se 1 (by rfl) ⟨15257321, by rfl⟩ : syracuseStep 20343095 = 30514643) B30514643
theorem B13562063 : Blo 2229435 13562063 := bstep (se 1 (by rfl) ⟨10171547, by rfl⟩ : syracuseStep 13562063 = 20343095) B20343095
theorem B9041375 : Blo 2229435 9041375 := bstep (se 1 (by rfl) ⟨6781031, by rfl⟩ : syracuseStep 9041375 = 13562063) B13562063
theorem B6027583 : Blo 2229435 6027583 := bstep (se 1 (by rfl) ⟨4520687, by rfl⟩ : syracuseStep 6027583 = 9041375) B9041375
theorem B8036777 : Blo 2229435 8036777 := bstep (se 2 (by rfl) ⟨3013791, by rfl⟩ : syracuseStep 8036777 = 6027583) B6027583
theorem B21431405 : Blo 2229435 21431405 := bstep (se 3 (by rfl) ⟨4018388, by rfl⟩ : syracuseStep 21431405 = 8036777) B8036777
theorem B14287603 : Blo 2229435 14287603 := bstep (se 1 (by rfl) ⟨10715702, by rfl⟩ : syracuseStep 14287603 = 21431405) B21431405
theorem B19050137 : Blo 2229435 19050137 := bstep (se 2 (by rfl) ⟨7143801, by rfl⟩ : syracuseStep 19050137 = 14287603) B14287603
theorem B12700091 : Blo 2229435 12700091 := bstep (se 1 (by rfl) ⟨9525068, by rfl⟩ : syracuseStep 12700091 = 19050137) B19050137
theorem B8466727 : Blo 2229435 8466727 := bstep (se 1 (by rfl) ⟨6350045, by rfl⟩ : syracuseStep 8466727 = 12700091) B12700091
theorem B11288969 : Blo 2229435 11288969 := bstep (se 2 (by rfl) ⟨4233363, by rfl⟩ : syracuseStep 11288969 = 8466727) B8466727
theorem B7525979 : Blo 2229435 7525979 := bstep (se 1 (by rfl) ⟨5644484, by rfl⟩ : syracuseStep 7525979 = 11288969) B11288969
theorem B5017319 : Blo 2229435 5017319 := bstep (se 1 (by rfl) ⟨3762989, by rfl⟩ : syracuseStep 5017319 = 7525979) B7525979
theorem B3344879 : Blo 2229435 3344879 := bstep (se 1 (by rfl) ⟨2508659, by rfl⟩ : syracuseStep 3344879 = 5017319) B5017319
theorem B2229919 : Blo 2229435 2229919 := bstep (se 1 (by rfl) ⟨1672439, by rfl⟩ : syracuseStep 2229919 = 3344879) B3344879
theorem B3344885 : Blo 2229435 3344885 := bbase (se 5 (by rfl) ⟨156791, by rfl⟩ : syracuseStep 3344885 = 313583) (by norm_num)
theorem B2229923 : Blo 2229435 2229923 := bstep (se 1 (by rfl) ⟨1672442, by rfl⟩ : syracuseStep 2229923 = 3344885) B3344885
theorem B6350069 : Blo 2229435 6350069 := bbase (se 5 (by rfl) ⟨297659, by rfl⟩ : syracuseStep 6350069 = 595319) (by norm_num)
theorem B4233379 : Blo 2229435 4233379 := bstep (se 1 (by rfl) ⟨3175034, by rfl⟩ : syracuseStep 4233379 = 6350069) B6350069
theorem B5644505 : Blo 2229435 5644505 := bstep (se 2 (by rfl) ⟨2116689, by rfl⟩ : syracuseStep 5644505 = 4233379) B4233379
theorem B3763003 : Blo 2229435 3763003 := bstep (se 1 (by rfl) ⟨2822252, by rfl⟩ : syracuseStep 3763003 = 5644505) B5644505
theorem B5017337 : Blo 2229435 5017337 := bstep (se 2 (by rfl) ⟨1881501, by rfl⟩ : syracuseStep 5017337 = 3763003) B3763003
theorem B3344891 : Blo 2229435 3344891 := bstep (se 1 (by rfl) ⟨2508668, by rfl⟩ : syracuseStep 3344891 = 5017337) B5017337
theorem B2229927 : Blo 2229435 2229927 := bstep (se 1 (by rfl) ⟨1672445, by rfl⟩ : syracuseStep 2229927 = 3344891) B3344891
theorem B2508673 : Blo 2229435 2508673 := bbase (se 2 (by rfl) ⟨940752, by rfl⟩ : syracuseStep 2508673 = 1881505) (by norm_num)
theorem B3344897 : Blo 2229435 3344897 := bstep (se 2 (by rfl) ⟨1254336, by rfl⟩ : syracuseStep 3344897 = 2508673) B2508673
theorem B2229931 : Blo 2229435 2229931 := bstep (se 1 (by rfl) ⟨1672448, by rfl⟩ : syracuseStep 2229931 = 3344897) B3344897
theorem B5644525 : Blo 2229435 5644525 := bbase (se 3 (by rfl) ⟨1058348, by rfl⟩ : syracuseStep 5644525 = 2116697) (by norm_num)
theorem B7526033 : Blo 2229435 7526033 := bstep (se 2 (by rfl) ⟨2822262, by rfl⟩ : syracuseStep 7526033 = 5644525) B5644525
theorem B5017355 : Blo 2229435 5017355 := bstep (se 1 (by rfl) ⟨3763016, by rfl⟩ : syracuseStep 5017355 = 7526033) B7526033
theorem B3344903 : Blo 2229435 3344903 := bstep (se 1 (by rfl) ⟨2508677, by rfl⟩ : syracuseStep 3344903 = 5017355) B5017355
theorem B2229935 : Blo 2229435 2229935 := bstep (se 1 (by rfl) ⟨1672451, by rfl⟩ : syracuseStep 2229935 = 3344903) B3344903
theorem B3344909 : Blo 2229435 3344909 := bbase (se 3 (by rfl) ⟨627170, by rfl⟩ : syracuseStep 3344909 = 1254341) (by norm_num)
theorem B2229939 : Blo 2229435 2229939 := bstep (se 1 (by rfl) ⟨1672454, by rfl⟩ : syracuseStep 2229939 = 3344909) B3344909
theorem B5017373 : Blo 2229435 5017373 := bbase (se 3 (by rfl) ⟨940757, by rfl⟩ : syracuseStep 5017373 = 1881515) (by norm_num)
theorem B3344915 : Blo 2229435 3344915 := bstep (se 1 (by rfl) ⟨2508686, by rfl⟩ : syracuseStep 3344915 = 5017373) B5017373
theorem B2229943 : Blo 2229435 2229943 := bstep (se 1 (by rfl) ⟨1672457, by rfl⟩ : syracuseStep 2229943 = 3344915) B3344915
theorem B3763037 : Blo 2229435 3763037 := bbase (se 3 (by rfl) ⟨705569, by rfl⟩ : syracuseStep 3763037 = 1411139) (by norm_num)
theorem B2508691 : Blo 2229435 2508691 := bstep (se 1 (by rfl) ⟨1881518, by rfl⟩ : syracuseStep 2508691 = 3763037) B3763037
theorem B3344921 : Blo 2229435 3344921 := bstep (se 2 (by rfl) ⟨1254345, by rfl⟩ : syracuseStep 3344921 = 2508691) B2508691
theorem B2229947 : Blo 2229435 2229947 := bstep (se 1 (by rfl) ⟨1672460, by rfl⟩ : syracuseStep 2229947 = 3344921) B3344921
theorem B9525205 : Blo 2229435 9525205 := bbase (se 7 (by rfl) ⟨111623, by rfl⟩ : syracuseStep 9525205 = 223247) (by norm_num)
theorem B12700273 : Blo 2229435 12700273 := bstep (se 2 (by rfl) ⟨4762602, by rfl⟩ : syracuseStep 12700273 = 9525205) B9525205
theorem B16933697 : Blo 2229435 16933697 := bstep (se 2 (by rfl) ⟨6350136, by rfl⟩ : syracuseStep 16933697 = 12700273) B12700273
theorem B11289131 : Blo 2229435 11289131 := bstep (se 1 (by rfl) ⟨8466848, by rfl⟩ : syracuseStep 11289131 = 16933697) B16933697
theorem B7526087 : Blo 2229435 7526087 := bstep (se 1 (by rfl) ⟨5644565, by rfl⟩ : syracuseStep 7526087 = 11289131) B11289131
theorem B5017391 : Blo 2229435 5017391 := bstep (se 1 (by rfl) ⟨3763043, by rfl⟩ : syracuseStep 5017391 = 7526087) B7526087
theorem B3344927 : Blo 2229435 3344927 := bstep (se 1 (by rfl) ⟨2508695, by rfl⟩ : syracuseStep 3344927 = 5017391) B5017391
theorem B2229951 : Blo 2229435 2229951 := bstep (se 1 (by rfl) ⟨1672463, by rfl⟩ : syracuseStep 2229951 = 3344927) B3344927
theorem B3344933 : Blo 2229435 3344933 := bbase (se 4 (by rfl) ⟨313587, by rfl⟩ : syracuseStep 3344933 = 627175) (by norm_num)
theorem B2229955 : Blo 2229435 2229955 := bstep (se 1 (by rfl) ⟨1672466, by rfl⟩ : syracuseStep 2229955 = 3344933) B3344933
theorem B2822293 : Blo 2229435 2822293 := bbase (se 6 (by rfl) ⟨66147, by rfl⟩ : syracuseStep 2822293 = 132295) (by norm_num)
theorem B3763057 : Blo 2229435 3763057 := bstep (se 2 (by rfl) ⟨1411146, by rfl⟩ : syracuseStep 3763057 = 2822293) B2822293
theorem B5017409 : Blo 2229435 5017409 := bstep (se 2 (by rfl) ⟨1881528, by rfl⟩ : syracuseStep 5017409 = 3763057) B3763057
theorem B3344939 : Blo 2229435 3344939 := bstep (se 1 (by rfl) ⟨2508704, by rfl⟩ : syracuseStep 3344939 = 5017409) B5017409
theorem B2229959 : Blo 2229435 2229959 := bstep (se 1 (by rfl) ⟨1672469, by rfl⟩ : syracuseStep 2229959 = 3344939) B3344939
theorem B2508709 : Blo 2229435 2508709 := bbase (se 4 (by rfl) ⟨235191, by rfl⟩ : syracuseStep 2508709 = 470383) (by norm_num)
theorem B3344945 : Blo 2229435 3344945 := bstep (se 2 (by rfl) ⟨1254354, by rfl⟩ : syracuseStep 3344945 = 2508709) B2508709
theorem B2229963 : Blo 2229435 2229963 := bstep (se 1 (by rfl) ⟨1672472, by rfl⟩ : syracuseStep 2229963 = 3344945) B3344945
theorem B9164933 : Blo 2229435 9164933 := bbase (se 4 (by rfl) ⟨859212, by rfl⟩ : syracuseStep 9164933 = 1718425) (by norm_num)
theorem B6109955 : Blo 2229435 6109955 := bstep (se 1 (by rfl) ⟨4582466, by rfl⟩ : syracuseStep 6109955 = 9164933) B9164933
theorem B4073303 : Blo 2229435 4073303 := bstep (se 1 (by rfl) ⟨3054977, by rfl⟩ : syracuseStep 4073303 = 6109955) B6109955
theorem B2715535 : Blo 2229435 2715535 := bstep (se 1 (by rfl) ⟨2036651, by rfl⟩ : syracuseStep 2715535 = 4073303) B4073303
theorem B3620713 : Blo 2229435 3620713 := bstep (se 2 (by rfl) ⟨1357767, by rfl⟩ : syracuseStep 3620713 = 2715535) B2715535
theorem B4827617 : Blo 2229435 4827617 := bstep (se 2 (by rfl) ⟨1810356, by rfl⟩ : syracuseStep 4827617 = 3620713) B3620713
theorem B3218411 : Blo 2229435 3218411 := bstep (se 1 (by rfl) ⟨2413808, by rfl⟩ : syracuseStep 3218411 = 4827617) B4827617
theorem B8582429 : Blo 2229435 8582429 := bstep (se 3 (by rfl) ⟨1609205, by rfl⟩ : syracuseStep 8582429 = 3218411) B3218411
theorem B22886477 : Blo 2229435 22886477 := bstep (se 3 (by rfl) ⟨4291214, by rfl⟩ : syracuseStep 22886477 = 8582429) B8582429
theorem B15257651 : Blo 2229435 15257651 := bstep (se 1 (by rfl) ⟨11443238, by rfl⟩ : syracuseStep 15257651 = 22886477) B22886477
theorem B40687069 : Blo 2229435 40687069 := bstep (se 3 (by rfl) ⟨7628825, by rfl⟩ : syracuseStep 40687069 = 15257651) B15257651
theorem B54249425 : Blo 2229435 54249425 := bstep (se 2 (by rfl) ⟨20343534, by rfl⟩ : syracuseStep 54249425 = 40687069) B40687069
theorem B36166283 : Blo 2229435 36166283 := bstep (se 1 (by rfl) ⟨27124712, by rfl⟩ : syracuseStep 36166283 = 54249425) B54249425
theorem B24110855 : Blo 2229435 24110855 := bstep (se 1 (by rfl) ⟨18083141, by rfl⟩ : syracuseStep 24110855 = 36166283) B36166283
theorem B16073903 : Blo 2229435 16073903 := bstep (se 1 (by rfl) ⟨12055427, by rfl⟩ : syracuseStep 16073903 = 24110855) B24110855
theorem B10715935 : Blo 2229435 10715935 := bstep (se 1 (by rfl) ⟨8036951, by rfl⟩ : syracuseStep 10715935 = 16073903) B16073903
theorem B14287913 : Blo 2229435 14287913 := bstep (se 2 (by rfl) ⟨5357967, by rfl⟩ : syracuseStep 14287913 = 10715935) B10715935
theorem B9525275 : Blo 2229435 9525275 := bstep (se 1 (by rfl) ⟨7143956, by rfl⟩ : syracuseStep 9525275 = 14287913) B14287913
theorem B6350183 : Blo 2229435 6350183 := bstep (se 1 (by rfl) ⟨4762637, by rfl⟩ : syracuseStep 6350183 = 9525275) B9525275
theorem B4233455 : Blo 2229435 4233455 := bstep (se 1 (by rfl) ⟨3175091, by rfl⟩ : syracuseStep 4233455 = 6350183) B6350183
theorem B2822303 : Blo 2229435 2822303 := bstep (se 1 (by rfl) ⟨2116727, by rfl⟩ : syracuseStep 2822303 = 4233455) B4233455
theorem B7526141 : Blo 2229435 7526141 := bstep (se 3 (by rfl) ⟨1411151, by rfl⟩ : syracuseStep 7526141 = 2822303) B2822303
theorem B5017427 : Blo 2229435 5017427 := bstep (se 1 (by rfl) ⟨3763070, by rfl⟩ : syracuseStep 5017427 = 7526141) B7526141
theorem B3344951 : Blo 2229435 3344951 := bstep (se 1 (by rfl) ⟨2508713, by rfl⟩ : syracuseStep 3344951 = 5017427) B5017427
theorem B2229967 : Blo 2229435 2229967 := bstep (se 1 (by rfl) ⟨1672475, by rfl⟩ : syracuseStep 2229967 = 3344951) B3344951
theorem B3344957 : Blo 2229435 3344957 := bbase (se 3 (by rfl) ⟨627179, by rfl⟩ : syracuseStep 3344957 = 1254359) (by norm_num)
theorem B2229971 : Blo 2229435 2229971 := bstep (se 1 (by rfl) ⟨1672478, by rfl⟩ : syracuseStep 2229971 = 3344957) B3344957
theorem B5017445 : Blo 2229435 5017445 := bbase (se 4 (by rfl) ⟨470385, by rfl⟩ : syracuseStep 5017445 = 940771) (by norm_num)
theorem B3344963 : Blo 2229435 3344963 := bstep (se 1 (by rfl) ⟨2508722, by rfl⟩ : syracuseStep 3344963 = 5017445) B5017445
theorem B2229975 : Blo 2229435 2229975 := bstep (se 1 (by rfl) ⟨1672481, by rfl⟩ : syracuseStep 2229975 = 3344963) B3344963
theorem B5644637 : Blo 2229435 5644637 := bbase (se 3 (by rfl) ⟨1058369, by rfl⟩ : syracuseStep 5644637 = 2116739) (by norm_num)
theorem B3763091 : Blo 2229435 3763091 := bstep (se 1 (by rfl) ⟨2822318, by rfl⟩ : syracuseStep 3763091 = 5644637) B5644637
theorem B2508727 : Blo 2229435 2508727 := bstep (se 1 (by rfl) ⟨1881545, by rfl⟩ : syracuseStep 2508727 = 3763091) B3763091
theorem B3344969 : Blo 2229435 3344969 := bstep (se 2 (by rfl) ⟨1254363, by rfl⟩ : syracuseStep 3344969 = 2508727) B2508727
theorem B2229979 : Blo 2229435 2229979 := bstep (se 1 (by rfl) ⟨1672484, by rfl⟩ : syracuseStep 2229979 = 3344969) B3344969
theorem B4233485 : Blo 2229435 4233485 := bbase (se 3 (by rfl) ⟨793778, by rfl⟩ : syracuseStep 4233485 = 1587557) (by norm_num)
theorem B11289293 : Blo 2229435 11289293 := bstep (se 3 (by rfl) ⟨2116742, by rfl⟩ : syracuseStep 11289293 = 4233485) B4233485
theorem B7526195 : Blo 2229435 7526195 := bstep (se 1 (by rfl) ⟨5644646, by rfl⟩ : syracuseStep 7526195 = 11289293) B11289293
theorem B5017463 : Blo 2229435 5017463 := bstep (se 1 (by rfl) ⟨3763097, by rfl⟩ : syracuseStep 5017463 = 7526195) B7526195
theorem B3344975 : Blo 2229435 3344975 := bstep (se 1 (by rfl) ⟨2508731, by rfl⟩ : syracuseStep 3344975 = 5017463) B5017463
theorem B2229983 : Blo 2229435 2229983 := bstep (se 1 (by rfl) ⟨1672487, by rfl⟩ : syracuseStep 2229983 = 3344975) B3344975
theorem B3344981 : Blo 2229435 3344981 := bbase (se 8 (by rfl) ⟨19599, by rfl⟩ : syracuseStep 3344981 = 39199) (by norm_num)
theorem B2229987 : Blo 2229435 2229987 := bstep (se 1 (by rfl) ⟨1672490, by rfl⟩ : syracuseStep 2229987 = 3344981) B3344981
theorem B9041669 : Blo 2229435 9041669 := bbase (se 4 (by rfl) ⟨847656, by rfl⟩ : syracuseStep 9041669 = 1695313) (by norm_num)
theorem B6027779 : Blo 2229435 6027779 := bstep (se 1 (by rfl) ⟨4520834, by rfl⟩ : syracuseStep 6027779 = 9041669) B9041669
theorem B4018519 : Blo 2229435 4018519 := bstep (se 1 (by rfl) ⟨3013889, by rfl⟩ : syracuseStep 4018519 = 6027779) B6027779
theorem B5358025 : Blo 2229435 5358025 := bstep (se 2 (by rfl) ⟨2009259, by rfl⟩ : syracuseStep 5358025 = 4018519) B4018519
theorem B7144033 : Blo 2229435 7144033 := bstep (se 2 (by rfl) ⟨2679012, by rfl⟩ : syracuseStep 7144033 = 5358025) B5358025
theorem B9525377 : Blo 2229435 9525377 := bstep (se 2 (by rfl) ⟨3572016, by rfl⟩ : syracuseStep 9525377 = 7144033) B7144033
theorem B6350251 : Blo 2229435 6350251 := bstep (se 1 (by rfl) ⟨4762688, by rfl⟩ : syracuseStep 6350251 = 9525377) B9525377
theorem B8467001 : Blo 2229435 8467001 := bstep (se 2 (by rfl) ⟨3175125, by rfl⟩ : syracuseStep 8467001 = 6350251) B6350251
theorem B5644667 : Blo 2229435 5644667 := bstep (se 1 (by rfl) ⟨4233500, by rfl⟩ : syracuseStep 5644667 = 8467001) B8467001
theorem B3763111 : Blo 2229435 3763111 := bstep (se 1 (by rfl) ⟨2822333, by rfl⟩ : syracuseStep 3763111 = 5644667) B5644667
theorem B5017481 : Blo 2229435 5017481 := bstep (se 2 (by rfl) ⟨1881555, by rfl⟩ : syracuseStep 5017481 = 3763111) B3763111
theorem B3344987 : Blo 2229435 3344987 := bstep (se 1 (by rfl) ⟨2508740, by rfl⟩ : syracuseStep 3344987 = 5017481) B5017481
theorem B2229991 : Blo 2229435 2229991 := bstep (se 1 (by rfl) ⟨1672493, by rfl⟩ : syracuseStep 2229991 = 3344987) B3344987
theorem B2508745 : Blo 2229435 2508745 := bbase (se 2 (by rfl) ⟨940779, by rfl⟩ : syracuseStep 2508745 = 1881559) (by norm_num)
theorem B3344993 : Blo 2229435 3344993 := bstep (se 2 (by rfl) ⟨1254372, by rfl⟩ : syracuseStep 3344993 = 2508745) B2508745
theorem B2229995 : Blo 2229435 2229995 := bstep (se 1 (by rfl) ⟨1672496, by rfl⟩ : syracuseStep 2229995 = 3344993) B3344993
theorem B3572029 : Blo 2229435 3572029 := bbase (se 3 (by rfl) ⟨669755, by rfl⟩ : syracuseStep 3572029 = 1339511) (by norm_num)
theorem B19050821 : Blo 2229435 19050821 := bstep (se 4 (by rfl) ⟨1786014, by rfl⟩ : syracuseStep 19050821 = 3572029) B3572029
theorem B12700547 : Blo 2229435 12700547 := bstep (se 1 (by rfl) ⟨9525410, by rfl⟩ : syracuseStep 12700547 = 19050821) B19050821
theorem B8467031 : Blo 2229435 8467031 := bstep (se 1 (by rfl) ⟨6350273, by rfl⟩ : syracuseStep 8467031 = 12700547) B12700547
theorem B5644687 : Blo 2229435 5644687 := bstep (se 1 (by rfl) ⟨4233515, by rfl⟩ : syracuseStep 5644687 = 8467031) B8467031
theorem B7526249 : Blo 2229435 7526249 := bstep (se 2 (by rfl) ⟨2822343, by rfl⟩ : syracuseStep 7526249 = 5644687) B5644687
theorem B5017499 : Blo 2229435 5017499 := bstep (se 1 (by rfl) ⟨3763124, by rfl⟩ : syracuseStep 5017499 = 7526249) B7526249
theorem B3344999 : Blo 2229435 3344999 := bstep (se 1 (by rfl) ⟨2508749, by rfl⟩ : syracuseStep 3344999 = 5017499) B5017499
theorem B2229999 : Blo 2229435 2229999 := bstep (se 1 (by rfl) ⟨1672499, by rfl⟩ : syracuseStep 2229999 = 3344999) B3344999
theorem B3345005 : Blo 2229435 3345005 := bbase (se 3 (by rfl) ⟨627188, by rfl⟩ : syracuseStep 3345005 = 1254377) (by norm_num)
theorem B2230003 : Blo 2229435 2230003 := bstep (se 1 (by rfl) ⟨1672502, by rfl⟩ : syracuseStep 2230003 = 3345005) B3345005
theorem B5017517 : Blo 2229435 5017517 := bbase (se 3 (by rfl) ⟨940784, by rfl⟩ : syracuseStep 5017517 = 1881569) (by norm_num)
theorem B3345011 : Blo 2229435 3345011 := bstep (se 1 (by rfl) ⟨2508758, by rfl⟩ : syracuseStep 3345011 = 5017517) B5017517
theorem B2230007 : Blo 2229435 2230007 := bstep (se 1 (by rfl) ⟨1672505, by rfl⟩ : syracuseStep 2230007 = 3345011) B3345011
theorem B6350309 : Blo 2229435 6350309 := bbase (se 4 (by rfl) ⟨595341, by rfl⟩ : syracuseStep 6350309 = 1190683) (by norm_num)
theorem B4233539 : Blo 2229435 4233539 := bstep (se 1 (by rfl) ⟨3175154, by rfl⟩ : syracuseStep 4233539 = 6350309) B6350309
theorem B2822359 : Blo 2229435 2822359 := bstep (se 1 (by rfl) ⟨2116769, by rfl⟩ : syracuseStep 2822359 = 4233539) B4233539
theorem B3763145 : Blo 2229435 3763145 := bstep (se 2 (by rfl) ⟨1411179, by rfl⟩ : syracuseStep 3763145 = 2822359) B2822359
theorem B2508763 : Blo 2229435 2508763 := bstep (se 1 (by rfl) ⟨1881572, by rfl⟩ : syracuseStep 2508763 = 3763145) B3763145
theorem B3345017 : Blo 2229435 3345017 := bstep (se 2 (by rfl) ⟨1254381, by rfl⟩ : syracuseStep 3345017 = 2508763) B2508763
theorem B2230011 : Blo 2229435 2230011 := bstep (se 1 (by rfl) ⟨1672508, by rfl⟩ : syracuseStep 2230011 = 3345017) B3345017
theorem B2260441 : Blo 2229435 2260441 := bbase (se 2 (by rfl) ⟨847665, by rfl⟩ : syracuseStep 2260441 = 1695331) (by norm_num)
theorem B3013921 : Blo 2229435 3013921 := bstep (se 2 (by rfl) ⟨1130220, by rfl⟩ : syracuseStep 3013921 = 2260441) B2260441
theorem B16074245 : Blo 2229435 16074245 := bstep (se 4 (by rfl) ⟨1506960, by rfl⟩ : syracuseStep 16074245 = 3013921) B3013921
theorem B42864653 : Blo 2229435 42864653 := bstep (se 3 (by rfl) ⟨8037122, by rfl⟩ : syracuseStep 42864653 = 16074245) B16074245
theorem B28576435 : Blo 2229435 28576435 := bstep (se 1 (by rfl) ⟨21432326, by rfl⟩ : syracuseStep 28576435 = 42864653) B42864653
theorem B38101913 : Blo 2229435 38101913 := bstep (se 2 (by rfl) ⟨14288217, by rfl⟩ : syracuseStep 38101913 = 28576435) B28576435
theorem B25401275 : Blo 2229435 25401275 := bstep (se 1 (by rfl) ⟨19050956, by rfl⟩ : syracuseStep 25401275 = 38101913) B38101913
theorem B16934183 : Blo 2229435 16934183 := bstep (se 1 (by rfl) ⟨12700637, by rfl⟩ : syracuseStep 16934183 = 25401275) B25401275
theorem B11289455 : Blo 2229435 11289455 := bstep (se 1 (by rfl) ⟨8467091, by rfl⟩ : syracuseStep 11289455 = 16934183) B16934183
theorem B7526303 : Blo 2229435 7526303 := bstep (se 1 (by rfl) ⟨5644727, by rfl⟩ : syracuseStep 7526303 = 11289455) B11289455
theorem B5017535 : Blo 2229435 5017535 := bstep (se 1 (by rfl) ⟨3763151, by rfl⟩ : syracuseStep 5017535 = 7526303) B7526303
theorem B3345023 : Blo 2229435 3345023 := bstep (se 1 (by rfl) ⟨2508767, by rfl⟩ : syracuseStep 3345023 = 5017535) B5017535
theorem B2230015 : Blo 2229435 2230015 := bstep (se 1 (by rfl) ⟨1672511, by rfl⟩ : syracuseStep 2230015 = 3345023) B3345023
theorem B3345029 : Blo 2229435 3345029 := bbase (se 4 (by rfl) ⟨313596, by rfl⟩ : syracuseStep 3345029 = 627193) (by norm_num)
theorem B2230019 : Blo 2229435 2230019 := bstep (se 1 (by rfl) ⟨1672514, by rfl⟩ : syracuseStep 2230019 = 3345029) B3345029
theorem B3763165 : Blo 2229435 3763165 := bbase (se 3 (by rfl) ⟨705593, by rfl⟩ : syracuseStep 3763165 = 1411187) (by norm_num)
theorem B5017553 : Blo 2229435 5017553 := bstep (se 2 (by rfl) ⟨1881582, by rfl⟩ : syracuseStep 5017553 = 3763165) B3763165
theorem B3345035 : Blo 2229435 3345035 := bstep (se 1 (by rfl) ⟨2508776, by rfl⟩ : syracuseStep 3345035 = 5017553) B5017553
theorem B2230023 : Blo 2229435 2230023 := bstep (se 1 (by rfl) ⟨1672517, by rfl⟩ : syracuseStep 2230023 = 3345035) B3345035
theorem B2508781 : Blo 2229435 2508781 := bbase (se 3 (by rfl) ⟨470396, by rfl⟩ : syracuseStep 2508781 = 940793) (by norm_num)
theorem B3345041 : Blo 2229435 3345041 := bstep (se 2 (by rfl) ⟨1254390, by rfl⟩ : syracuseStep 3345041 = 2508781) B2508781
theorem B2230027 : Blo 2229435 2230027 := bstep (se 1 (by rfl) ⟨1672520, by rfl⟩ : syracuseStep 2230027 = 3345041) B3345041
theorem B7526357 : Blo 2229435 7526357 := bbase (se 7 (by rfl) ⟨88199, by rfl⟩ : syracuseStep 7526357 = 176399) (by norm_num)
theorem B5017571 : Blo 2229435 5017571 := bstep (se 1 (by rfl) ⟨3763178, by rfl⟩ : syracuseStep 5017571 = 7526357) B7526357
theorem B3345047 : Blo 2229435 3345047 := bstep (se 1 (by rfl) ⟨2508785, by rfl⟩ : syracuseStep 3345047 = 5017571) B5017571
theorem B2230031 : Blo 2229435 2230031 := bstep (se 1 (by rfl) ⟨1672523, by rfl⟩ : syracuseStep 2230031 = 3345047) B3345047
theorem B3345053 : Blo 2229435 3345053 := bbase (se 3 (by rfl) ⟨627197, by rfl⟩ : syracuseStep 3345053 = 1254395) (by norm_num)
theorem B2230035 : Blo 2229435 2230035 := bstep (se 1 (by rfl) ⟨1672526, by rfl⟩ : syracuseStep 2230035 = 3345053) B3345053
theorem B5017589 : Blo 2229435 5017589 := bbase (se 5 (by rfl) ⟨235199, by rfl⟩ : syracuseStep 5017589 = 470399) (by norm_num)
theorem B3345059 : Blo 2229435 3345059 := bstep (se 1 (by rfl) ⟨2508794, by rfl⟩ : syracuseStep 3345059 = 5017589) B5017589
theorem B2230039 : Blo 2229435 2230039 := bstep (se 1 (by rfl) ⟨1672529, by rfl⟩ : syracuseStep 2230039 = 3345059) B3345059
theorem B5431253 : Blo 2229435 5431253 := bbase (se 7 (by rfl) ⟨63647, by rfl⟩ : syracuseStep 5431253 = 127295) (by norm_num)
theorem B14483341 : Blo 2229435 14483341 := bstep (se 3 (by rfl) ⟨2715626, by rfl⟩ : syracuseStep 14483341 = 5431253) B5431253
theorem B19311121 : Blo 2229435 19311121 := bstep (se 2 (by rfl) ⟨7241670, by rfl⟩ : syracuseStep 19311121 = 14483341) B14483341
theorem B25748161 : Blo 2229435 25748161 := bstep (se 2 (by rfl) ⟨9655560, by rfl⟩ : syracuseStep 25748161 = 19311121) B19311121
theorem B137323525 : Blo 2229435 137323525 := bstep (se 4 (by rfl) ⟨12874080, by rfl⟩ : syracuseStep 137323525 = 25748161) B25748161
theorem B183098033 : Blo 2229435 183098033 := bstep (se 2 (by rfl) ⟨68661762, by rfl⟩ : syracuseStep 183098033 = 137323525) B137323525
theorem B122065355 : Blo 2229435 122065355 := bstep (se 1 (by rfl) ⟨91549016, by rfl⟩ : syracuseStep 122065355 = 183098033) B183098033
theorem B81376903 : Blo 2229435 81376903 := bstep (se 1 (by rfl) ⟨61032677, by rfl⟩ : syracuseStep 81376903 = 122065355) B122065355
theorem B108502537 : Blo 2229435 108502537 := bstep (se 2 (by rfl) ⟨40688451, by rfl⟩ : syracuseStep 108502537 = 81376903) B81376903
theorem B144670049 : Blo 2229435 144670049 := bstep (se 2 (by rfl) ⟨54251268, by rfl⟩ : syracuseStep 144670049 = 108502537) B108502537
theorem B96446699 : Blo 2229435 96446699 := bstep (se 1 (by rfl) ⟨72335024, by rfl⟩ : syracuseStep 96446699 = 144670049) B144670049
theorem B64297799 : Blo 2229435 64297799 := bstep (se 1 (by rfl) ⟨48223349, by rfl⟩ : syracuseStep 64297799 = 96446699) B96446699
theorem B42865199 : Blo 2229435 42865199 := bstep (se 1 (by rfl) ⟨32148899, by rfl⟩ : syracuseStep 42865199 = 64297799) B64297799
theorem B28576799 : Blo 2229435 28576799 := bstep (se 1 (by rfl) ⟨21432599, by rfl⟩ : syracuseStep 28576799 = 42865199) B42865199
theorem B19051199 : Blo 2229435 19051199 := bstep (se 1 (by rfl) ⟨14288399, by rfl⟩ : syracuseStep 19051199 = 28576799) B28576799
theorem B12700799 : Blo 2229435 12700799 := bstep (se 1 (by rfl) ⟨9525599, by rfl⟩ : syracuseStep 12700799 = 19051199) B19051199
theorem B8467199 : Blo 2229435 8467199 := bstep (se 1 (by rfl) ⟨6350399, by rfl⟩ : syracuseStep 8467199 = 12700799) B12700799
theorem B5644799 : Blo 2229435 5644799 := bstep (se 1 (by rfl) ⟨4233599, by rfl⟩ : syracuseStep 5644799 = 8467199) B8467199
theorem B3763199 : Blo 2229435 3763199 := bstep (se 1 (by rfl) ⟨2822399, by rfl⟩ : syracuseStep 3763199 = 5644799) B5644799
theorem B2508799 : Blo 2229435 2508799 := bstep (se 1 (by rfl) ⟨1881599, by rfl⟩ : syracuseStep 2508799 = 3763199) B3763199
theorem B3345065 : Blo 2229435 3345065 := bstep (se 2 (by rfl) ⟨1254399, by rfl⟩ : syracuseStep 3345065 = 2508799) B2508799
theorem B2230043 : Blo 2229435 2230043 := bstep (se 1 (by rfl) ⟨1672532, by rfl⟩ : syracuseStep 2230043 = 3345065) B3345065
theorem B3175205 : Blo 2229435 3175205 := bbase (se 4 (by rfl) ⟨297675, by rfl⟩ : syracuseStep 3175205 = 595351) (by norm_num)
theorem B8467213 : Blo 2229435 8467213 := bstep (se 3 (by rfl) ⟨1587602, by rfl⟩ : syracuseStep 8467213 = 3175205) B3175205
theorem B11289617 : Blo 2229435 11289617 := bstep (se 2 (by rfl) ⟨4233606, by rfl⟩ : syracuseStep 11289617 = 8467213) B8467213
theorem B7526411 : Blo 2229435 7526411 := bstep (se 1 (by rfl) ⟨5644808, by rfl⟩ : syracuseStep 7526411 = 11289617) B11289617
theorem B5017607 : Blo 2229435 5017607 := bstep (se 1 (by rfl) ⟨3763205, by rfl⟩ : syracuseStep 5017607 = 7526411) B7526411
theorem B3345071 : Blo 2229435 3345071 := bstep (se 1 (by rfl) ⟨2508803, by rfl⟩ : syracuseStep 3345071 = 5017607) B5017607
theorem B2230047 : Blo 2229435 2230047 := bstep (se 1 (by rfl) ⟨1672535, by rfl⟩ : syracuseStep 2230047 = 3345071) B3345071
theorem B3345077 : Blo 2229435 3345077 := bbase (se 5 (by rfl) ⟨156800, by rfl⟩ : syracuseStep 3345077 = 313601) (by norm_num)
theorem B2230051 : Blo 2229435 2230051 := bstep (se 1 (by rfl) ⟨1672538, by rfl⟩ : syracuseStep 2230051 = 3345077) B3345077
theorem B5644829 : Blo 2229435 5644829 := bbase (se 3 (by rfl) ⟨1058405, by rfl⟩ : syracuseStep 5644829 = 2116811) (by norm_num)
theorem B3763219 : Blo 2229435 3763219 := bstep (se 1 (by rfl) ⟨2822414, by rfl⟩ : syracuseStep 3763219 = 5644829) B5644829
theorem B5017625 : Blo 2229435 5017625 := bstep (se 2 (by rfl) ⟨1881609, by rfl⟩ : syracuseStep 5017625 = 3763219) B3763219
theorem B3345083 : Blo 2229435 3345083 := bstep (se 1 (by rfl) ⟨2508812, by rfl⟩ : syracuseStep 3345083 = 5017625) B5017625
theorem B2230055 : Blo 2229435 2230055 := bstep (se 1 (by rfl) ⟨1672541, by rfl⟩ : syracuseStep 2230055 = 3345083) B3345083
theorem B2508817 : Blo 2229435 2508817 := bbase (se 2 (by rfl) ⟨940806, by rfl⟩ : syracuseStep 2508817 = 1881613) (by norm_num)
theorem B3345089 : Blo 2229435 3345089 := bstep (se 2 (by rfl) ⟨1254408, by rfl⟩ : syracuseStep 3345089 = 2508817) B2508817
theorem B2230059 : Blo 2229435 2230059 := bstep (se 1 (by rfl) ⟨1672544, by rfl⟩ : syracuseStep 2230059 = 3345089) B3345089
theorem B4233637 : Blo 2229435 4233637 := bbase (se 4 (by rfl) ⟨396903, by rfl⟩ : syracuseStep 4233637 = 793807) (by norm_num)
theorem B5644849 : Blo 2229435 5644849 := bstep (se 2 (by rfl) ⟨2116818, by rfl⟩ : syracuseStep 5644849 = 4233637) B4233637
theorem B7526465 : Blo 2229435 7526465 := bstep (se 2 (by rfl) ⟨2822424, by rfl⟩ : syracuseStep 7526465 = 5644849) B5644849
theorem B5017643 : Blo 2229435 5017643 := bstep (se 1 (by rfl) ⟨3763232, by rfl⟩ : syracuseStep 5017643 = 7526465) B7526465
theorem B3345095 : Blo 2229435 3345095 := bstep (se 1 (by rfl) ⟨2508821, by rfl⟩ : syracuseStep 3345095 = 5017643) B5017643
theorem B2230063 : Blo 2229435 2230063 := bstep (se 1 (by rfl) ⟨1672547, by rfl⟩ : syracuseStep 2230063 = 3345095) B3345095
theorem B3345101 : Blo 2229435 3345101 := bbase (se 3 (by rfl) ⟨627206, by rfl⟩ : syracuseStep 3345101 = 1254413) (by norm_num)
theorem B2230067 : Blo 2229435 2230067 := bstep (se 1 (by rfl) ⟨1672550, by rfl⟩ : syracuseStep 2230067 = 3345101) B3345101
theorem B5017661 : Blo 2229435 5017661 := bbase (se 3 (by rfl) ⟨940811, by rfl⟩ : syracuseStep 5017661 = 1881623) (by norm_num)
theorem B3345107 : Blo 2229435 3345107 := bstep (se 1 (by rfl) ⟨2508830, by rfl⟩ : syracuseStep 3345107 = 5017661) B5017661
theorem B2230071 : Blo 2229435 2230071 := bstep (se 1 (by rfl) ⟨1672553, by rfl⟩ : syracuseStep 2230071 = 3345107) B3345107
theorem B3763253 : Blo 2229435 3763253 := bbase (se 5 (by rfl) ⟨176402, by rfl⟩ : syracuseStep 3763253 = 352805) (by norm_num)
theorem B2508835 : Blo 2229435 2508835 := bstep (se 1 (by rfl) ⟨1881626, by rfl⟩ : syracuseStep 2508835 = 3763253) B3763253
theorem B3345113 : Blo 2229435 3345113 := bstep (se 2 (by rfl) ⟨1254417, by rfl⟩ : syracuseStep 3345113 = 2508835) B2508835
theorem B2230075 : Blo 2229435 2230075 := bstep (se 1 (by rfl) ⟨1672556, by rfl⟩ : syracuseStep 2230075 = 3345113) B3345113
theorem B6350501 : Blo 2229435 6350501 := bbase (se 4 (by rfl) ⟨595359, by rfl⟩ : syracuseStep 6350501 = 1190719) (by norm_num)
theorem B16934669 : Blo 2229435 16934669 := bstep (se 3 (by rfl) ⟨3175250, by rfl⟩ : syracuseStep 16934669 = 6350501) B6350501
theorem B11289779 : Blo 2229435 11289779 := bstep (se 1 (by rfl) ⟨8467334, by rfl⟩ : syracuseStep 11289779 = 16934669) B16934669
theorem B7526519 : Blo 2229435 7526519 := bstep (se 1 (by rfl) ⟨5644889, by rfl⟩ : syracuseStep 7526519 = 11289779) B11289779
theorem B5017679 : Blo 2229435 5017679 := bstep (se 1 (by rfl) ⟨3763259, by rfl⟩ : syracuseStep 5017679 = 7526519) B7526519
theorem B3345119 : Blo 2229435 3345119 := bstep (se 1 (by rfl) ⟨2508839, by rfl⟩ : syracuseStep 3345119 = 5017679) B5017679
theorem B2230079 : Blo 2229435 2230079 := bstep (se 1 (by rfl) ⟨1672559, by rfl⟩ : syracuseStep 2230079 = 3345119) B3345119
theorem B3345125 : Blo 2229435 3345125 := bbase (se 4 (by rfl) ⟨313605, by rfl⟩ : syracuseStep 3345125 = 627211) (by norm_num)
theorem B2230083 : Blo 2229435 2230083 := bstep (se 1 (by rfl) ⟨1672562, by rfl⟩ : syracuseStep 2230083 = 3345125) B3345125
theorem B4018693 : Blo 2229435 4018693 := bbase (se 4 (by rfl) ⟨376752, by rfl⟩ : syracuseStep 4018693 = 753505) (by norm_num)
theorem B5358257 : Blo 2229435 5358257 := bstep (se 2 (by rfl) ⟨2009346, by rfl⟩ : syracuseStep 5358257 = 4018693) B4018693
theorem B3572171 : Blo 2229435 3572171 := bstep (se 1 (by rfl) ⟨2679128, by rfl⟩ : syracuseStep 3572171 = 5358257) B5358257
theorem B2381447 : Blo 2229435 2381447 := bstep (se 1 (by rfl) ⟨1786085, by rfl⟩ : syracuseStep 2381447 = 3572171) B3572171
theorem B6350525 : Blo 2229435 6350525 := bstep (se 3 (by rfl) ⟨1190723, by rfl⟩ : syracuseStep 6350525 = 2381447) B2381447
theorem B4233683 : Blo 2229435 4233683 := bstep (se 1 (by rfl) ⟨3175262, by rfl⟩ : syracuseStep 4233683 = 6350525) B6350525
theorem B2822455 : Blo 2229435 2822455 := bstep (se 1 (by rfl) ⟨2116841, by rfl⟩ : syracuseStep 2822455 = 4233683) B4233683
theorem B3763273 : Blo 2229435 3763273 := bstep (se 2 (by rfl) ⟨1411227, by rfl⟩ : syracuseStep 3763273 = 2822455) B2822455
theorem B5017697 : Blo 2229435 5017697 := bstep (se 2 (by rfl) ⟨1881636, by rfl⟩ : syracuseStep 5017697 = 3763273) B3763273
theorem B3345131 : Blo 2229435 3345131 := bstep (se 1 (by rfl) ⟨2508848, by rfl⟩ : syracuseStep 3345131 = 5017697) B5017697
theorem B2230087 : Blo 2229435 2230087 := bstep (se 1 (by rfl) ⟨1672565, by rfl⟩ : syracuseStep 2230087 = 3345131) B3345131
theorem B2508853 : Blo 2229435 2508853 := bbase (se 5 (by rfl) ⟨117602, by rfl⟩ : syracuseStep 2508853 = 235205) (by norm_num)
theorem B3345137 : Blo 2229435 3345137 := bstep (se 2 (by rfl) ⟨1254426, by rfl⟩ : syracuseStep 3345137 = 2508853) B2508853
theorem B2230091 : Blo 2229435 2230091 := bstep (se 1 (by rfl) ⟨1672568, by rfl⟩ : syracuseStep 2230091 = 3345137) B3345137
theorem B2822465 : Blo 2229435 2822465 := bbase (se 2 (by rfl) ⟨1058424, by rfl⟩ : syracuseStep 2822465 = 2116849) (by norm_num)
theorem B7526573 : Blo 2229435 7526573 := bstep (se 3 (by rfl) ⟨1411232, by rfl⟩ : syracuseStep 7526573 = 2822465) B2822465
theorem B5017715 : Blo 2229435 5017715 := bstep (se 1 (by rfl) ⟨3763286, by rfl⟩ : syracuseStep 5017715 = 7526573) B7526573
theorem B3345143 : Blo 2229435 3345143 := bstep (se 1 (by rfl) ⟨2508857, by rfl⟩ : syracuseStep 3345143 = 5017715) B5017715
theorem B2230095 : Blo 2229435 2230095 := bstep (se 1 (by rfl) ⟨1672571, by rfl⟩ : syracuseStep 2230095 = 3345143) B3345143
theorem B3345149 : Blo 2229435 3345149 := bbase (se 3 (by rfl) ⟨627215, by rfl⟩ : syracuseStep 3345149 = 1254431) (by norm_num)
theorem B2230099 : Blo 2229435 2230099 := bstep (se 1 (by rfl) ⟨1672574, by rfl⟩ : syracuseStep 2230099 = 3345149) B3345149
theorem B5017733 : Blo 2229435 5017733 := bbase (se 4 (by rfl) ⟨470412, by rfl⟩ : syracuseStep 5017733 = 940825) (by norm_num)
theorem B3345155 : Blo 2229435 3345155 := bstep (se 1 (by rfl) ⟨2508866, by rfl⟩ : syracuseStep 3345155 = 5017733) B5017733
theorem B2230103 : Blo 2229435 2230103 := bstep (se 1 (by rfl) ⟨1672577, by rfl⟩ : syracuseStep 2230103 = 3345155) B3345155
theorem B17400149 : Blo 2229435 17400149 := bbase (se 10 (by rfl) ⟨25488, by rfl⟩ : syracuseStep 17400149 = 50977) (by norm_num)
theorem B11600099 : Blo 2229435 11600099 := bstep (se 1 (by rfl) ⟨8700074, by rfl⟩ : syracuseStep 11600099 = 17400149) B17400149
theorem B7733399 : Blo 2229435 7733399 := bstep (se 1 (by rfl) ⟨5800049, by rfl⟩ : syracuseStep 7733399 = 11600099) B11600099
theorem B20622397 : Blo 2229435 20622397 := bstep (se 3 (by rfl) ⟨3866699, by rfl⟩ : syracuseStep 20622397 = 7733399) B7733399
theorem B27496529 : Blo 2229435 27496529 := bstep (se 2 (by rfl) ⟨10311198, by rfl⟩ : syracuseStep 27496529 = 20622397) B20622397
theorem B18331019 : Blo 2229435 18331019 := bstep (se 1 (by rfl) ⟨13748264, by rfl⟩ : syracuseStep 18331019 = 27496529) B27496529
theorem B12220679 : Blo 2229435 12220679 := bstep (se 1 (by rfl) ⟨9165509, by rfl⟩ : syracuseStep 12220679 = 18331019) B18331019
theorem B32588477 : Blo 2229435 32588477 := bstep (se 3 (by rfl) ⟨6110339, by rfl⟩ : syracuseStep 32588477 = 12220679) B12220679
theorem B21725651 : Blo 2229435 21725651 := bstep (se 1 (by rfl) ⟨16294238, by rfl⟩ : syracuseStep 21725651 = 32588477) B32588477
theorem B14483767 : Blo 2229435 14483767 := bstep (se 1 (by rfl) ⟨10862825, by rfl⟩ : syracuseStep 14483767 = 21725651) B21725651
theorem B19311689 : Blo 2229435 19311689 := bstep (se 2 (by rfl) ⟨7241883, by rfl⟩ : syracuseStep 19311689 = 14483767) B14483767
theorem B12874459 : Blo 2229435 12874459 := bstep (se 1 (by rfl) ⟨9655844, by rfl⟩ : syracuseStep 12874459 = 19311689) B19311689
theorem B17165945 : Blo 2229435 17165945 := bstep (se 2 (by rfl) ⟨6437229, by rfl⟩ : syracuseStep 17165945 = 12874459) B12874459
theorem B11443963 : Blo 2229435 11443963 := bstep (se 1 (by rfl) ⟨8582972, by rfl⟩ : syracuseStep 11443963 = 17165945) B17165945
theorem B15258617 : Blo 2229435 15258617 := bstep (se 2 (by rfl) ⟨5721981, by rfl⟩ : syracuseStep 15258617 = 11443963) B11443963
theorem B10172411 : Blo 2229435 10172411 := bstep (se 1 (by rfl) ⟨7629308, by rfl⟩ : syracuseStep 10172411 = 15258617) B15258617
theorem B6781607 : Blo 2229435 6781607 := bstep (se 1 (by rfl) ⟨5086205, by rfl⟩ : syracuseStep 6781607 = 10172411) B10172411
theorem B4521071 : Blo 2229435 4521071 := bstep (se 1 (by rfl) ⟨3390803, by rfl⟩ : syracuseStep 4521071 = 6781607) B6781607
theorem B3014047 : Blo 2229435 3014047 := bstep (se 1 (by rfl) ⟨2260535, by rfl⟩ : syracuseStep 3014047 = 4521071) B4521071
theorem B4018729 : Blo 2229435 4018729 := bstep (se 2 (by rfl) ⟨1507023, by rfl⟩ : syracuseStep 4018729 = 3014047) B3014047
theorem B5358305 : Blo 2229435 5358305 := bstep (se 2 (by rfl) ⟨2009364, by rfl⟩ : syracuseStep 5358305 = 4018729) B4018729
theorem B3572203 : Blo 2229435 3572203 := bstep (se 1 (by rfl) ⟨2679152, by rfl⟩ : syracuseStep 3572203 = 5358305) B5358305
theorem B4762937 : Blo 2229435 4762937 := bstep (se 2 (by rfl) ⟨1786101, by rfl⟩ : syracuseStep 4762937 = 3572203) B3572203
theorem B3175291 : Blo 2229435 3175291 := bstep (se 1 (by rfl) ⟨2381468, by rfl⟩ : syracuseStep 3175291 = 4762937) B4762937
theorem B4233721 : Blo 2229435 4233721 := bstep (se 2 (by rfl) ⟨1587645, by rfl⟩ : syracuseStep 4233721 = 3175291) B3175291
theorem B5644961 : Blo 2229435 5644961 := bstep (se 2 (by rfl) ⟨2116860, by rfl⟩ : syracuseStep 5644961 = 4233721) B4233721
theorem B3763307 : Blo 2229435 3763307 := bstep (se 1 (by rfl) ⟨2822480, by rfl⟩ : syracuseStep 3763307 = 5644961) B5644961
theorem B2508871 : Blo 2229435 2508871 := bstep (se 1 (by rfl) ⟨1881653, by rfl⟩ : syracuseStep 2508871 = 3763307) B3763307
theorem B3345161 : Blo 2229435 3345161 := bstep (se 2 (by rfl) ⟨1254435, by rfl⟩ : syracuseStep 3345161 = 2508871) B2508871
theorem B2230107 : Blo 2229435 2230107 := bstep (se 1 (by rfl) ⟨1672580, by rfl⟩ : syracuseStep 2230107 = 3345161) B3345161
theorem B11289941 : Blo 2229435 11289941 := bbase (se 12 (by rfl) ⟨4134, by rfl⟩ : syracuseStep 11289941 = 8269) (by norm_num)
theorem B7526627 : Blo 2229435 7526627 := bstep (se 1 (by rfl) ⟨5644970, by rfl⟩ : syracuseStep 7526627 = 11289941) B11289941
theorem B5017751 : Blo 2229435 5017751 := bstep (se 1 (by rfl) ⟨3763313, by rfl⟩ : syracuseStep 5017751 = 7526627) B7526627
theorem B3345167 : Blo 2229435 3345167 := bstep (se 1 (by rfl) ⟨2508875, by rfl⟩ : syracuseStep 3345167 = 5017751) B5017751
theorem B2230111 : Blo 2229435 2230111 := bstep (se 1 (by rfl) ⟨1672583, by rfl⟩ : syracuseStep 2230111 = 3345167) B3345167
theorem B3345173 : Blo 2229435 3345173 := bbase (se 6 (by rfl) ⟨78402, by rfl⟩ : syracuseStep 3345173 = 156805) (by norm_num)
theorem B2230115 : Blo 2229435 2230115 := bstep (se 1 (by rfl) ⟨1672586, by rfl⟩ : syracuseStep 2230115 = 3345173) B3345173
theorem B6967957 : Blo 2229435 6967957 := bbase (se 6 (by rfl) ⟨163311, by rfl⟩ : syracuseStep 6967957 = 326623) (by norm_num)
theorem B9290609 : Blo 2229435 9290609 := bstep (se 2 (by rfl) ⟨3483978, by rfl⟩ : syracuseStep 9290609 = 6967957) B6967957
theorem B6193739 : Blo 2229435 6193739 := bstep (se 1 (by rfl) ⟨4645304, by rfl⟩ : syracuseStep 6193739 = 9290609) B9290609
theorem B4129159 : Blo 2229435 4129159 := bstep (se 1 (by rfl) ⟨3096869, by rfl⟩ : syracuseStep 4129159 = 6193739) B6193739
theorem B5505545 : Blo 2229435 5505545 := bstep (se 2 (by rfl) ⟨2064579, by rfl⟩ : syracuseStep 5505545 = 4129159) B4129159
theorem B3670363 : Blo 2229435 3670363 := bstep (se 1 (by rfl) ⟨2752772, by rfl⟩ : syracuseStep 3670363 = 5505545) B5505545
theorem B19575269 : Blo 2229435 19575269 := bstep (se 4 (by rfl) ⟨1835181, by rfl⟩ : syracuseStep 19575269 = 3670363) B3670363
theorem B13050179 : Blo 2229435 13050179 := bstep (se 1 (by rfl) ⟨9787634, by rfl⟩ : syracuseStep 13050179 = 19575269) B19575269
theorem B8700119 : Blo 2229435 8700119 := bstep (se 1 (by rfl) ⟨6525089, by rfl⟩ : syracuseStep 8700119 = 13050179) B13050179
theorem B5800079 : Blo 2229435 5800079 := bstep (se 1 (by rfl) ⟨4350059, by rfl⟩ : syracuseStep 5800079 = 8700119) B8700119
theorem B3866719 : Blo 2229435 3866719 := bstep (se 1 (by rfl) ⟨2900039, by rfl⟩ : syracuseStep 3866719 = 5800079) B5800079
theorem B5155625 : Blo 2229435 5155625 := bstep (se 2 (by rfl) ⟨1933359, by rfl⟩ : syracuseStep 5155625 = 3866719) B3866719
theorem B3437083 : Blo 2229435 3437083 := bstep (se 1 (by rfl) ⟨2577812, by rfl⟩ : syracuseStep 3437083 = 5155625) B5155625
theorem B4582777 : Blo 2229435 4582777 := bstep (se 2 (by rfl) ⟨1718541, by rfl⟩ : syracuseStep 4582777 = 3437083) B3437083
theorem B6110369 : Blo 2229435 6110369 := bstep (se 2 (by rfl) ⟨2291388, by rfl⟩ : syracuseStep 6110369 = 4582777) B4582777
theorem B4073579 : Blo 2229435 4073579 := bstep (se 1 (by rfl) ⟨3055184, by rfl⟩ : syracuseStep 4073579 = 6110369) B6110369
theorem B2715719 : Blo 2229435 2715719 := bstep (se 1 (by rfl) ⟨2036789, by rfl⟩ : syracuseStep 2715719 = 4073579) B4073579
theorem B28967669 : Blo 2229435 28967669 := bstep (se 5 (by rfl) ⟨1357859, by rfl⟩ : syracuseStep 28967669 = 2715719) B2715719
theorem B19311779 : Blo 2229435 19311779 := bstep (se 1 (by rfl) ⟨14483834, by rfl⟩ : syracuseStep 19311779 = 28967669) B28967669
theorem B12874519 : Blo 2229435 12874519 := bstep (se 1 (by rfl) ⟨9655889, by rfl⟩ : syracuseStep 12874519 = 19311779) B19311779
theorem B17166025 : Blo 2229435 17166025 := bstep (se 2 (by rfl) ⟨6437259, by rfl⟩ : syracuseStep 17166025 = 12874519) B12874519
theorem B91552133 : Blo 2229435 91552133 := bstep (se 4 (by rfl) ⟨8583012, by rfl⟩ : syracuseStep 91552133 = 17166025) B17166025
theorem B61034755 : Blo 2229435 61034755 := bstep (se 1 (by rfl) ⟨45776066, by rfl⟩ : syracuseStep 61034755 = 91552133) B91552133
theorem B81379673 : Blo 2229435 81379673 := bstep (se 2 (by rfl) ⟨30517377, by rfl⟩ : syracuseStep 81379673 = 61034755) B61034755
theorem B54253115 : Blo 2229435 54253115 := bstep (se 1 (by rfl) ⟨40689836, by rfl⟩ : syracuseStep 54253115 = 81379673) B81379673
theorem B36168743 : Blo 2229435 36168743 := bstep (se 1 (by rfl) ⟨27126557, by rfl⟩ : syracuseStep 36168743 = 54253115) B54253115
theorem B24112495 : Blo 2229435 24112495 := bstep (se 1 (by rfl) ⟨18084371, by rfl⟩ : syracuseStep 24112495 = 36168743) B36168743
theorem B32149993 : Blo 2229435 32149993 := bstep (se 2 (by rfl) ⟨12056247, by rfl⟩ : syracuseStep 32149993 = 24112495) B24112495
theorem B42866657 : Blo 2229435 42866657 := bstep (se 2 (by rfl) ⟨16074996, by rfl⟩ : syracuseStep 42866657 = 32149993) B32149993
theorem B28577771 : Blo 2229435 28577771 := bstep (se 1 (by rfl) ⟨21433328, by rfl⟩ : syracuseStep 28577771 = 42866657) B42866657
theorem B19051847 : Blo 2229435 19051847 := bstep (se 1 (by rfl) ⟨14288885, by rfl⟩ : syracuseStep 19051847 = 28577771) B28577771
theorem B12701231 : Blo 2229435 12701231 := bstep (se 1 (by rfl) ⟨9525923, by rfl⟩ : syracuseStep 12701231 = 19051847) B19051847
theorem B8467487 : Blo 2229435 8467487 := bstep (se 1 (by rfl) ⟨6350615, by rfl⟩ : syracuseStep 8467487 = 12701231) B12701231
theorem B5644991 : Blo 2229435 5644991 := bstep (se 1 (by rfl) ⟨4233743, by rfl⟩ : syracuseStep 5644991 = 8467487) B8467487
theorem B3763327 : Blo 2229435 3763327 := bstep (se 1 (by rfl) ⟨2822495, by rfl⟩ : syracuseStep 3763327 = 5644991) B5644991
theorem B5017769 : Blo 2229435 5017769 := bstep (se 2 (by rfl) ⟨1881663, by rfl⟩ : syracuseStep 5017769 = 3763327) B3763327
theorem B3345179 : Blo 2229435 3345179 := bstep (se 1 (by rfl) ⟨2508884, by rfl⟩ : syracuseStep 3345179 = 5017769) B5017769
theorem B2230119 : Blo 2229435 2230119 := bstep (se 1 (by rfl) ⟨1672589, by rfl⟩ : syracuseStep 2230119 = 3345179) B3345179
theorem B2508889 : Blo 2229435 2508889 := bbase (se 2 (by rfl) ⟨940833, by rfl⟩ : syracuseStep 2508889 = 1881667) (by norm_num)
theorem B3345185 : Blo 2229435 3345185 := bstep (se 2 (by rfl) ⟨1254444, by rfl⟩ : syracuseStep 3345185 = 2508889) B2508889
theorem B2230123 : Blo 2229435 2230123 := bstep (se 1 (by rfl) ⟨1672592, by rfl⟩ : syracuseStep 2230123 = 3345185) B3345185
theorem B7144469 : Blo 2229435 7144469 := bbase (se 6 (by rfl) ⟨167448, by rfl⟩ : syracuseStep 7144469 = 334897) (by norm_num)
theorem B4762979 : Blo 2229435 4762979 := bstep (se 1 (by rfl) ⟨3572234, by rfl⟩ : syracuseStep 4762979 = 7144469) B7144469
theorem B3175319 : Blo 2229435 3175319 := bstep (se 1 (by rfl) ⟨2381489, by rfl⟩ : syracuseStep 3175319 = 4762979) B4762979
theorem B8467517 : Blo 2229435 8467517 := bstep (se 3 (by rfl) ⟨1587659, by rfl⟩ : syracuseStep 8467517 = 3175319) B3175319
theorem B5645011 : Blo 2229435 5645011 := bstep (se 1 (by rfl) ⟨4233758, by rfl⟩ : syracuseStep 5645011 = 8467517) B8467517
theorem B7526681 : Blo 2229435 7526681 := bstep (se 2 (by rfl) ⟨2822505, by rfl⟩ : syracuseStep 7526681 = 5645011) B5645011
theorem B5017787 : Blo 2229435 5017787 := bstep (se 1 (by rfl) ⟨3763340, by rfl⟩ : syracuseStep 5017787 = 7526681) B7526681
theorem B3345191 : Blo 2229435 3345191 := bstep (se 1 (by rfl) ⟨2508893, by rfl⟩ : syracuseStep 3345191 = 5017787) B5017787
theorem B2230127 : Blo 2229435 2230127 := bstep (se 1 (by rfl) ⟨1672595, by rfl⟩ : syracuseStep 2230127 = 3345191) B3345191
theorem B3345197 : Blo 2229435 3345197 := bbase (se 3 (by rfl) ⟨627224, by rfl⟩ : syracuseStep 3345197 = 1254449) (by norm_num)
theorem B2230131 : Blo 2229435 2230131 := bstep (se 1 (by rfl) ⟨1672598, by rfl⟩ : syracuseStep 2230131 = 3345197) B3345197
theorem B5017805 : Blo 2229435 5017805 := bbase (se 3 (by rfl) ⟨940838, by rfl⟩ : syracuseStep 5017805 = 1881677) (by norm_num)
theorem B3345203 : Blo 2229435 3345203 := bstep (se 1 (by rfl) ⟨2508902, by rfl⟩ : syracuseStep 3345203 = 5017805) B5017805
theorem B2230135 : Blo 2229435 2230135 := bstep (se 1 (by rfl) ⟨1672601, by rfl⟩ : syracuseStep 2230135 = 3345203) B3345203
theorem B2822521 : Blo 2229435 2822521 := bbase (se 2 (by rfl) ⟨1058445, by rfl⟩ : syracuseStep 2822521 = 2116891) (by norm_num)
theorem B3763361 : Blo 2229435 3763361 := bstep (se 2 (by rfl) ⟨1411260, by rfl⟩ : syracuseStep 3763361 = 2822521) B2822521
theorem B2508907 : Blo 2229435 2508907 := bstep (se 1 (by rfl) ⟨1881680, by rfl⟩ : syracuseStep 2508907 = 3763361) B3763361
theorem B3345209 : Blo 2229435 3345209 := bstep (se 2 (by rfl) ⟨1254453, by rfl⟩ : syracuseStep 3345209 = 2508907) B2508907
theorem B2230139 : Blo 2229435 2230139 := bstep (se 1 (by rfl) ⟨1672604, by rfl⟩ : syracuseStep 2230139 = 3345209) B3345209
theorem B6110437 : Blo 2229435 6110437 := bbase (se 4 (by rfl) ⟨572853, by rfl⟩ : syracuseStep 6110437 = 1145707) (by norm_num)
theorem B8147249 : Blo 2229435 8147249 := bstep (se 2 (by rfl) ⟨3055218, by rfl⟩ : syracuseStep 8147249 = 6110437) B6110437
theorem B5431499 : Blo 2229435 5431499 := bstep (se 1 (by rfl) ⟨4073624, by rfl⟩ : syracuseStep 5431499 = 8147249) B8147249
theorem B3620999 : Blo 2229435 3620999 := bstep (se 1 (by rfl) ⟨2715749, by rfl⟩ : syracuseStep 3620999 = 5431499) B5431499
theorem B2413999 : Blo 2229435 2413999 := bstep (se 1 (by rfl) ⟨1810499, by rfl⟩ : syracuseStep 2413999 = 3620999) B3620999
theorem B3218665 : Blo 2229435 3218665 := bstep (se 2 (by rfl) ⟨1206999, by rfl⟩ : syracuseStep 3218665 = 2413999) B2413999
theorem B4291553 : Blo 2229435 4291553 := bstep (se 2 (by rfl) ⟨1609332, by rfl⟩ : syracuseStep 4291553 = 3218665) B3218665
theorem B11444141 : Blo 2229435 11444141 := bstep (se 3 (by rfl) ⟨2145776, by rfl⟩ : syracuseStep 11444141 = 4291553) B4291553
theorem B7629427 : Blo 2229435 7629427 := bstep (se 1 (by rfl) ⟨5722070, by rfl⟩ : syracuseStep 7629427 = 11444141) B11444141
theorem B10172569 : Blo 2229435 10172569 := bstep (se 2 (by rfl) ⟨3814713, by rfl⟩ : syracuseStep 10172569 = 7629427) B7629427
theorem B13563425 : Blo 2229435 13563425 := bstep (se 2 (by rfl) ⟨5086284, by rfl⟩ : syracuseStep 13563425 = 10172569) B10172569
theorem B9042283 : Blo 2229435 9042283 := bstep (se 1 (by rfl) ⟨6781712, by rfl⟩ : syracuseStep 9042283 = 13563425) B13563425
theorem B12056377 : Blo 2229435 12056377 := bstep (se 2 (by rfl) ⟨4521141, by rfl⟩ : syracuseStep 12056377 = 9042283) B9042283
theorem B16075169 : Blo 2229435 16075169 := bstep (se 2 (by rfl) ⟨6028188, by rfl⟩ : syracuseStep 16075169 = 12056377) B12056377
theorem B10716779 : Blo 2229435 10716779 := bstep (se 1 (by rfl) ⟨8037584, by rfl⟩ : syracuseStep 10716779 = 16075169) B16075169
theorem B7144519 : Blo 2229435 7144519 := bstep (se 1 (by rfl) ⟨5358389, by rfl⟩ : syracuseStep 7144519 = 10716779) B10716779
theorem B9526025 : Blo 2229435 9526025 := bstep (se 2 (by rfl) ⟨3572259, by rfl⟩ : syracuseStep 9526025 = 7144519) B7144519
theorem B25402733 : Blo 2229435 25402733 := bstep (se 3 (by rfl) ⟨4763012, by rfl⟩ : syracuseStep 25402733 = 9526025) B9526025
theorem B16935155 : Blo 2229435 16935155 := bstep (se 1 (by rfl) ⟨12701366, by rfl⟩ : syracuseStep 16935155 = 25402733) B25402733
theorem B11290103 : Blo 2229435 11290103 := bstep (se 1 (by rfl) ⟨8467577, by rfl⟩ : syracuseStep 11290103 = 16935155) B16935155
theorem B7526735 : Blo 2229435 7526735 := bstep (se 1 (by rfl) ⟨5645051, by rfl⟩ : syracuseStep 7526735 = 11290103) B11290103
theorem B5017823 : Blo 2229435 5017823 := bstep (se 1 (by rfl) ⟨3763367, by rfl⟩ : syracuseStep 5017823 = 7526735) B7526735
theorem B3345215 : Blo 2229435 3345215 := bstep (se 1 (by rfl) ⟨2508911, by rfl⟩ : syracuseStep 3345215 = 5017823) B5017823
theorem B2230143 : Blo 2229435 2230143 := bstep (se 1 (by rfl) ⟨1672607, by rfl⟩ : syracuseStep 2230143 = 3345215) B3345215
theorem B3345221 : Blo 2229435 3345221 := bbase (se 4 (by rfl) ⟨313614, by rfl⟩ : syracuseStep 3345221 = 627229) (by norm_num)
theorem B2230147 : Blo 2229435 2230147 := bstep (se 1 (by rfl) ⟨1672610, by rfl⟩ : syracuseStep 2230147 = 3345221) B3345221
theorem B3763381 : Blo 2229435 3763381 := bbase (se 5 (by rfl) ⟨176408, by rfl⟩ : syracuseStep 3763381 = 352817) (by norm_num)
theorem B5017841 : Blo 2229435 5017841 := bstep (se 2 (by rfl) ⟨1881690, by rfl⟩ : syracuseStep 5017841 = 3763381) B3763381
theorem B3345227 : Blo 2229435 3345227 := bstep (se 1 (by rfl) ⟨2508920, by rfl⟩ : syracuseStep 3345227 = 5017841) B5017841
theorem B2230151 : Blo 2229435 2230151 := bstep (se 1 (by rfl) ⟨1672613, by rfl⟩ : syracuseStep 2230151 = 3345227) B3345227
theorem B2508925 : Blo 2229435 2508925 := bbase (se 3 (by rfl) ⟨470423, by rfl⟩ : syracuseStep 2508925 = 940847) (by norm_num)
theorem B3345233 : Blo 2229435 3345233 := bstep (se 2 (by rfl) ⟨1254462, by rfl⟩ : syracuseStep 3345233 = 2508925) B2508925
theorem B2230155 : Blo 2229435 2230155 := bstep (se 1 (by rfl) ⟨1672616, by rfl⟩ : syracuseStep 2230155 = 3345233) B3345233
theorem B7526789 : Blo 2229435 7526789 := bbase (se 4 (by rfl) ⟨705636, by rfl⟩ : syracuseStep 7526789 = 1411273) (by norm_num)
theorem B5017859 : Blo 2229435 5017859 := bstep (se 1 (by rfl) ⟨3763394, by rfl⟩ : syracuseStep 5017859 = 7526789) B7526789
theorem B3345239 : Blo 2229435 3345239 := bstep (se 1 (by rfl) ⟨2508929, by rfl⟩ : syracuseStep 3345239 = 5017859) B5017859
theorem B2230159 : Blo 2229435 2230159 := bstep (se 1 (by rfl) ⟨1672619, by rfl⟩ : syracuseStep 2230159 = 3345239) B3345239
theorem B3345245 : Blo 2229435 3345245 := bbase (se 3 (by rfl) ⟨627233, by rfl⟩ : syracuseStep 3345245 = 1254467) (by norm_num)
theorem B2230163 : Blo 2229435 2230163 := bstep (se 1 (by rfl) ⟨1672622, by rfl⟩ : syracuseStep 2230163 = 3345245) B3345245
theorem B5017877 : Blo 2229435 5017877 := bbase (se 6 (by rfl) ⟨117606, by rfl⟩ : syracuseStep 5017877 = 235213) (by norm_num)
theorem B3345251 : Blo 2229435 3345251 := bstep (se 1 (by rfl) ⟨2508938, by rfl⟩ : syracuseStep 3345251 = 5017877) B5017877
theorem B2230167 : Blo 2229435 2230167 := bstep (se 1 (by rfl) ⟨1672625, by rfl⟩ : syracuseStep 2230167 = 3345251) B3345251
theorem B8467685 : Blo 2229435 8467685 := bbase (se 4 (by rfl) ⟨793845, by rfl⟩ : syracuseStep 8467685 = 1587691) (by norm_num)
theorem B5645123 : Blo 2229435 5645123 := bstep (se 1 (by rfl) ⟨4233842, by rfl⟩ : syracuseStep 5645123 = 8467685) B8467685
theorem B3763415 : Blo 2229435 3763415 := bstep (se 1 (by rfl) ⟨2822561, by rfl⟩ : syracuseStep 3763415 = 5645123) B5645123
theorem B2508943 : Blo 2229435 2508943 := bstep (se 1 (by rfl) ⟨1881707, by rfl⟩ : syracuseStep 2508943 = 3763415) B3763415
theorem B3345257 : Blo 2229435 3345257 := bstep (se 2 (by rfl) ⟨1254471, by rfl⟩ : syracuseStep 3345257 = 2508943) B2508943
theorem B2230171 : Blo 2229435 2230171 := bstep (se 1 (by rfl) ⟨1672628, by rfl⟩ : syracuseStep 2230171 = 3345257) B3345257
theorem B8037701 : Blo 2229435 8037701 := bbase (se 4 (by rfl) ⟨753534, by rfl⟩ : syracuseStep 8037701 = 1507069) (by norm_num)
theorem B5358467 : Blo 2229435 5358467 := bstep (se 1 (by rfl) ⟨4018850, by rfl⟩ : syracuseStep 5358467 = 8037701) B8037701
theorem B3572311 : Blo 2229435 3572311 := bstep (se 1 (by rfl) ⟨2679233, by rfl⟩ : syracuseStep 3572311 = 5358467) B5358467
theorem B4763081 : Blo 2229435 4763081 := bstep (se 2 (by rfl) ⟨1786155, by rfl⟩ : syracuseStep 4763081 = 3572311) B3572311
theorem B12701549 : Blo 2229435 12701549 := bstep (se 3 (by rfl) ⟨2381540, by rfl⟩ : syracuseStep 12701549 = 4763081) B4763081
theorem B8467699 : Blo 2229435 8467699 := bstep (se 1 (by rfl) ⟨6350774, by rfl⟩ : syracuseStep 8467699 = 12701549) B12701549
theorem B11290265 : Blo 2229435 11290265 := bstep (se 2 (by rfl) ⟨4233849, by rfl⟩ : syracuseStep 11290265 = 8467699) B8467699
theorem B7526843 : Blo 2229435 7526843 := bstep (se 1 (by rfl) ⟨5645132, by rfl⟩ : syracuseStep 7526843 = 11290265) B11290265
theorem B5017895 : Blo 2229435 5017895 := bstep (se 1 (by rfl) ⟨3763421, by rfl⟩ : syracuseStep 5017895 = 7526843) B7526843
theorem B3345263 : Blo 2229435 3345263 := bstep (se 1 (by rfl) ⟨2508947, by rfl⟩ : syracuseStep 3345263 = 5017895) B5017895
theorem B2230175 : Blo 2229435 2230175 := bstep (se 1 (by rfl) ⟨1672631, by rfl⟩ : syracuseStep 2230175 = 3345263) B3345263
theorem B3345269 : Blo 2229435 3345269 := bbase (se 5 (by rfl) ⟨156809, by rfl⟩ : syracuseStep 3345269 = 313619) (by norm_num)
theorem B2230179 : Blo 2229435 2230179 := bstep (se 1 (by rfl) ⟨1672634, by rfl⟩ : syracuseStep 2230179 = 3345269) B3345269
theorem B12056597 : Blo 2229435 12056597 := bbase (se 6 (by rfl) ⟨282576, by rfl⟩ : syracuseStep 12056597 = 565153) (by norm_num)
theorem B8037731 : Blo 2229435 8037731 := bstep (se 1 (by rfl) ⟨6028298, by rfl⟩ : syracuseStep 8037731 = 12056597) B12056597
theorem B5358487 : Blo 2229435 5358487 := bstep (se 1 (by rfl) ⟨4018865, by rfl⟩ : syracuseStep 5358487 = 8037731) B8037731
theorem B7144649 : Blo 2229435 7144649 := bstep (se 2 (by rfl) ⟨2679243, by rfl⟩ : syracuseStep 7144649 = 5358487) B5358487
theorem B4763099 : Blo 2229435 4763099 := bstep (se 1 (by rfl) ⟨3572324, by rfl⟩ : syracuseStep 4763099 = 7144649) B7144649
theorem B3175399 : Blo 2229435 3175399 := bstep (se 1 (by rfl) ⟨2381549, by rfl⟩ : syracuseStep 3175399 = 4763099) B4763099
theorem B4233865 : Blo 2229435 4233865 := bstep (se 2 (by rfl) ⟨1587699, by rfl⟩ : syracuseStep 4233865 = 3175399) B3175399
theorem B5645153 : Blo 2229435 5645153 := bstep (se 2 (by rfl) ⟨2116932, by rfl⟩ : syracuseStep 5645153 = 4233865) B4233865
theorem B3763435 : Blo 2229435 3763435 := bstep (se 1 (by rfl) ⟨2822576, by rfl⟩ : syracuseStep 3763435 = 5645153) B5645153
theorem B5017913 : Blo 2229435 5017913 := bstep (se 2 (by rfl) ⟨1881717, by rfl⟩ : syracuseStep 5017913 = 3763435) B3763435
theorem B3345275 : Blo 2229435 3345275 := bstep (se 1 (by rfl) ⟨2508956, by rfl⟩ : syracuseStep 3345275 = 5017913) B5017913
theorem B2230183 : Blo 2229435 2230183 := bstep (se 1 (by rfl) ⟨1672637, by rfl⟩ : syracuseStep 2230183 = 3345275) B3345275
theorem B2508961 : Blo 2229435 2508961 := bbase (se 2 (by rfl) ⟨940860, by rfl⟩ : syracuseStep 2508961 = 1881721) (by norm_num)
theorem B3345281 : Blo 2229435 3345281 := bstep (se 2 (by rfl) ⟨1254480, by rfl⟩ : syracuseStep 3345281 = 2508961) B2508961
theorem B2230187 : Blo 2229435 2230187 := bstep (se 1 (by rfl) ⟨1672640, by rfl⟩ : syracuseStep 2230187 = 3345281) B3345281
theorem B5645173 : Blo 2229435 5645173 := bbase (se 5 (by rfl) ⟨264617, by rfl⟩ : syracuseStep 5645173 = 529235) (by norm_num)
theorem B7526897 : Blo 2229435 7526897 := bstep (se 2 (by rfl) ⟨2822586, by rfl⟩ : syracuseStep 7526897 = 5645173) B5645173
theorem B5017931 : Blo 2229435 5017931 := bstep (se 1 (by rfl) ⟨3763448, by rfl⟩ : syracuseStep 5017931 = 7526897) B7526897
theorem B3345287 : Blo 2229435 3345287 := bstep (se 1 (by rfl) ⟨2508965, by rfl⟩ : syracuseStep 3345287 = 5017931) B5017931
theorem B2230191 : Blo 2229435 2230191 := bstep (se 1 (by rfl) ⟨1672643, by rfl⟩ : syracuseStep 2230191 = 3345287) B3345287
theorem B3345293 : Blo 2229435 3345293 := bbase (se 3 (by rfl) ⟨627242, by rfl⟩ : syracuseStep 3345293 = 1254485) (by norm_num)
theorem B2230195 : Blo 2229435 2230195 := bstep (se 1 (by rfl) ⟨1672646, by rfl⟩ : syracuseStep 2230195 = 3345293) B3345293
theorem B5017949 : Blo 2229435 5017949 := bbase (se 3 (by rfl) ⟨940865, by rfl⟩ : syracuseStep 5017949 = 1881731) (by norm_num)
theorem B3345299 : Blo 2229435 3345299 := bstep (se 1 (by rfl) ⟨2508974, by rfl⟩ : syracuseStep 3345299 = 5017949) B5017949
theorem B2230199 : Blo 2229435 2230199 := bstep (se 1 (by rfl) ⟨1672649, by rfl⟩ : syracuseStep 2230199 = 3345299) B3345299
theorem B3763469 : Blo 2229435 3763469 := bbase (se 3 (by rfl) ⟨705650, by rfl⟩ : syracuseStep 3763469 = 1411301) (by norm_num)
theorem B2508979 : Blo 2229435 2508979 := bstep (se 1 (by rfl) ⟨1881734, by rfl⟩ : syracuseStep 2508979 = 3763469) B3763469
theorem B3345305 : Blo 2229435 3345305 := bstep (se 2 (by rfl) ⟨1254489, by rfl⟩ : syracuseStep 3345305 = 2508979) B2508979
theorem B2230203 : Blo 2229435 2230203 := bstep (se 1 (by rfl) ⟨1672652, by rfl⟩ : syracuseStep 2230203 = 3345305) B3345305
theorem B19052597 : Blo 2229435 19052597 := bbase (se 5 (by rfl) ⟨893090, by rfl⟩ : syracuseStep 19052597 = 1786181) (by norm_num)
theorem B12701731 : Blo 2229435 12701731 := bstep (se 1 (by rfl) ⟨9526298, by rfl⟩ : syracuseStep 12701731 = 19052597) B19052597
theorem B16935641 : Blo 2229435 16935641 := bstep (se 2 (by rfl) ⟨6350865, by rfl⟩ : syracuseStep 16935641 = 12701731) B12701731
theorem B11290427 : Blo 2229435 11290427 := bstep (se 1 (by rfl) ⟨8467820, by rfl⟩ : syracuseStep 11290427 = 16935641) B16935641
theorem B7526951 : Blo 2229435 7526951 := bstep (se 1 (by rfl) ⟨5645213, by rfl⟩ : syracuseStep 7526951 = 11290427) B11290427
theorem B5017967 : Blo 2229435 5017967 := bstep (se 1 (by rfl) ⟨3763475, by rfl⟩ : syracuseStep 5017967 = 7526951) B7526951
theorem B3345311 : Blo 2229435 3345311 := bstep (se 1 (by rfl) ⟨2508983, by rfl⟩ : syracuseStep 3345311 = 5017967) B5017967
theorem B2230207 : Blo 2229435 2230207 := bstep (se 1 (by rfl) ⟨1672655, by rfl⟩ : syracuseStep 2230207 = 3345311) B3345311
theorem B3345317 : Blo 2229435 3345317 := bbase (se 4 (by rfl) ⟨313623, by rfl⟩ : syracuseStep 3345317 = 627247) (by norm_num)
theorem B2230211 : Blo 2229435 2230211 := bstep (se 1 (by rfl) ⟨1672658, by rfl⟩ : syracuseStep 2230211 = 3345317) B3345317
theorem B2822617 : Blo 2229435 2822617 := bbase (se 2 (by rfl) ⟨1058481, by rfl⟩ : syracuseStep 2822617 = 2116963) (by norm_num)
theorem B3763489 : Blo 2229435 3763489 := bstep (se 2 (by rfl) ⟨1411308, by rfl⟩ : syracuseStep 3763489 = 2822617) B2822617
theorem B5017985 : Blo 2229435 5017985 := bstep (se 2 (by rfl) ⟨1881744, by rfl⟩ : syracuseStep 5017985 = 3763489) B3763489
theorem B3345323 : Blo 2229435 3345323 := bstep (se 1 (by rfl) ⟨2508992, by rfl⟩ : syracuseStep 3345323 = 5017985) B5017985
theorem B2230215 : Blo 2229435 2230215 := bstep (se 1 (by rfl) ⟨1672661, by rfl⟩ : syracuseStep 2230215 = 3345323) B3345323
theorem B2508997 : Blo 2229435 2508997 := bbase (se 4 (by rfl) ⟨235218, by rfl⟩ : syracuseStep 2508997 = 470437) (by norm_num)
theorem B3345329 : Blo 2229435 3345329 := bstep (se 2 (by rfl) ⟨1254498, by rfl⟩ : syracuseStep 3345329 = 2508997) B2508997
theorem B2230219 : Blo 2229435 2230219 := bstep (se 1 (by rfl) ⟨1672664, by rfl⟩ : syracuseStep 2230219 = 3345329) B3345329
theorem B4233941 : Blo 2229435 4233941 := bbase (se 7 (by rfl) ⟨49616, by rfl⟩ : syracuseStep 4233941 = 99233) (by norm_num)
theorem B2822627 : Blo 2229435 2822627 := bstep (se 1 (by rfl) ⟨2116970, by rfl⟩ : syracuseStep 2822627 = 4233941) B4233941
theorem B7527005 : Blo 2229435 7527005 := bstep (se 3 (by rfl) ⟨1411313, by rfl⟩ : syracuseStep 7527005 = 2822627) B2822627
theorem B5018003 : Blo 2229435 5018003 := bstep (se 1 (by rfl) ⟨3763502, by rfl⟩ : syracuseStep 5018003 = 7527005) B7527005
theorem B3345335 : Blo 2229435 3345335 := bstep (se 1 (by rfl) ⟨2509001, by rfl⟩ : syracuseStep 3345335 = 5018003) B5018003
theorem B2230223 : Blo 2229435 2230223 := bstep (se 1 (by rfl) ⟨1672667, by rfl⟩ : syracuseStep 2230223 = 3345335) B3345335
theorem B3345341 : Blo 2229435 3345341 := bbase (se 3 (by rfl) ⟨627251, by rfl⟩ : syracuseStep 3345341 = 1254503) (by norm_num)
theorem B2230227 : Blo 2229435 2230227 := bstep (se 1 (by rfl) ⟨1672670, by rfl⟩ : syracuseStep 2230227 = 3345341) B3345341
theorem B5018021 : Blo 2229435 5018021 := bbase (se 4 (by rfl) ⟨470439, by rfl⟩ : syracuseStep 5018021 = 940879) (by norm_num)
theorem B3345347 : Blo 2229435 3345347 := bstep (se 1 (by rfl) ⟨2509010, by rfl⟩ : syracuseStep 3345347 = 5018021) B5018021
theorem B2230231 : Blo 2229435 2230231 := bstep (se 1 (by rfl) ⟨1672673, by rfl⟩ : syracuseStep 2230231 = 3345347) B3345347
theorem B5645285 : Blo 2229435 5645285 := bbase (se 4 (by rfl) ⟨529245, by rfl⟩ : syracuseStep 5645285 = 1058491) (by norm_num)
theorem B3763523 : Blo 2229435 3763523 := bstep (se 1 (by rfl) ⟨2822642, by rfl⟩ : syracuseStep 3763523 = 5645285) B5645285
theorem B2509015 : Blo 2229435 2509015 := bstep (se 1 (by rfl) ⟨1881761, by rfl⟩ : syracuseStep 2509015 = 3763523) B3763523
theorem B3345353 : Blo 2229435 3345353 := bstep (se 2 (by rfl) ⟨1254507, by rfl⟩ : syracuseStep 3345353 = 2509015) B2509015
theorem B2230235 : Blo 2229435 2230235 := bstep (se 1 (by rfl) ⟨1672676, by rfl⟩ : syracuseStep 2230235 = 3345353) B3345353
theorem B2381609 : Blo 2229435 2381609 := bbase (se 2 (by rfl) ⟨893103, by rfl⟩ : syracuseStep 2381609 = 1786207) (by norm_num)
theorem B6350957 : Blo 2229435 6350957 := bstep (se 3 (by rfl) ⟨1190804, by rfl⟩ : syracuseStep 6350957 = 2381609) B2381609
theorem B4233971 : Blo 2229435 4233971 := bstep (se 1 (by rfl) ⟨3175478, by rfl⟩ : syracuseStep 4233971 = 6350957) B6350957
theorem B11290589 : Blo 2229435 11290589 := bstep (se 3 (by rfl) ⟨2116985, by rfl⟩ : syracuseStep 11290589 = 4233971) B4233971
theorem B7527059 : Blo 2229435 7527059 := bstep (se 1 (by rfl) ⟨5645294, by rfl⟩ : syracuseStep 7527059 = 11290589) B11290589
theorem B5018039 : Blo 2229435 5018039 := bstep (se 1 (by rfl) ⟨3763529, by rfl⟩ : syracuseStep 5018039 = 7527059) B7527059
theorem B3345359 : Blo 2229435 3345359 := bstep (se 1 (by rfl) ⟨2509019, by rfl⟩ : syracuseStep 3345359 = 5018039) B5018039
theorem B2230239 : Blo 2229435 2230239 := bstep (se 1 (by rfl) ⟨1672679, by rfl⟩ : syracuseStep 2230239 = 3345359) B3345359
theorem B3345365 : Blo 2229435 3345365 := bbase (se 7 (by rfl) ⟨39203, by rfl⟩ : syracuseStep 3345365 = 78407) (by norm_num)
theorem B2230243 : Blo 2229435 2230243 := bstep (se 1 (by rfl) ⟨1672682, by rfl⟩ : syracuseStep 2230243 = 3345365) B3345365
theorem B8467973 : Blo 2229435 8467973 := bbase (se 4 (by rfl) ⟨793872, by rfl⟩ : syracuseStep 8467973 = 1587745) (by norm_num)
theorem B5645315 : Blo 2229435 5645315 := bstep (se 1 (by rfl) ⟨4233986, by rfl⟩ : syracuseStep 5645315 = 8467973) B8467973
theorem B3763543 : Blo 2229435 3763543 := bstep (se 1 (by rfl) ⟨2822657, by rfl⟩ : syracuseStep 3763543 = 5645315) B5645315
theorem B5018057 : Blo 2229435 5018057 := bstep (se 2 (by rfl) ⟨1881771, by rfl⟩ : syracuseStep 5018057 = 3763543) B3763543
theorem B3345371 : Blo 2229435 3345371 := bstep (se 1 (by rfl) ⟨2509028, by rfl⟩ : syracuseStep 3345371 = 5018057) B5018057
theorem B2230247 : Blo 2229435 2230247 := bstep (se 1 (by rfl) ⟨1672685, by rfl⟩ : syracuseStep 2230247 = 3345371) B3345371
theorem B2509033 : Blo 2229435 2509033 := bbase (se 2 (by rfl) ⟨940887, by rfl⟩ : syracuseStep 2509033 = 1881775) (by norm_num)
theorem B3345377 : Blo 2229435 3345377 := bstep (se 2 (by rfl) ⟨1254516, by rfl⟩ : syracuseStep 3345377 = 2509033) B2509033
theorem B2230251 : Blo 2229435 2230251 := bstep (se 1 (by rfl) ⟨1672688, by rfl⟩ : syracuseStep 2230251 = 3345377) B3345377
theorem B12702005 : Blo 2229435 12702005 := bbase (se 5 (by rfl) ⟨595406, by rfl⟩ : syracuseStep 12702005 = 1190813) (by norm_num)
theorem B8468003 : Blo 2229435 8468003 := bstep (se 1 (by rfl) ⟨6351002, by rfl⟩ : syracuseStep 8468003 = 12702005) B12702005
theorem B5645335 : Blo 2229435 5645335 := bstep (se 1 (by rfl) ⟨4234001, by rfl⟩ : syracuseStep 5645335 = 8468003) B8468003
theorem B7527113 : Blo 2229435 7527113 := bstep (se 2 (by rfl) ⟨2822667, by rfl⟩ : syracuseStep 7527113 = 5645335) B5645335
theorem B5018075 : Blo 2229435 5018075 := bstep (se 1 (by rfl) ⟨3763556, by rfl⟩ : syracuseStep 5018075 = 7527113) B7527113
theorem B3345383 : Blo 2229435 3345383 := bstep (se 1 (by rfl) ⟨2509037, by rfl⟩ : syracuseStep 3345383 = 5018075) B5018075
theorem B2230255 : Blo 2229435 2230255 := bstep (se 1 (by rfl) ⟨1672691, by rfl⟩ : syracuseStep 2230255 = 3345383) B3345383
theorem B3345389 : Blo 2229435 3345389 := bbase (se 3 (by rfl) ⟨627260, by rfl⟩ : syracuseStep 3345389 = 1254521) (by norm_num)
theorem B2230259 : Blo 2229435 2230259 := bstep (se 1 (by rfl) ⟨1672694, by rfl⟩ : syracuseStep 2230259 = 3345389) B3345389
theorem B5018093 : Blo 2229435 5018093 := bbase (se 3 (by rfl) ⟨940892, by rfl⟩ : syracuseStep 5018093 = 1881785) (by norm_num)
theorem B3345395 : Blo 2229435 3345395 := bstep (se 1 (by rfl) ⟨2509046, by rfl⟩ : syracuseStep 3345395 = 5018093) B5018093
theorem B2230263 : Blo 2229435 2230263 := bstep (se 1 (by rfl) ⟨1672697, by rfl⟩ : syracuseStep 2230263 = 3345395) B3345395
theorem B2543285 : Blo 2229435 2543285 := bbase (se 5 (by rfl) ⟨119216, by rfl⟩ : syracuseStep 2543285 = 238433) (by norm_num)
theorem B6782093 : Blo 2229435 6782093 := bstep (se 3 (by rfl) ⟨1271642, by rfl⟩ : syracuseStep 6782093 = 2543285) B2543285
theorem B4521395 : Blo 2229435 4521395 := bstep (se 1 (by rfl) ⟨3391046, by rfl⟩ : syracuseStep 4521395 = 6782093) B6782093
theorem B3014263 : Blo 2229435 3014263 := bstep (se 1 (by rfl) ⟨2260697, by rfl⟩ : syracuseStep 3014263 = 4521395) B4521395
theorem B16076069 : Blo 2229435 16076069 := bstep (se 4 (by rfl) ⟨1507131, by rfl⟩ : syracuseStep 16076069 = 3014263) B3014263
theorem B10717379 : Blo 2229435 10717379 := bstep (se 1 (by rfl) ⟨8038034, by rfl⟩ : syracuseStep 10717379 = 16076069) B16076069
theorem B7144919 : Blo 2229435 7144919 := bstep (se 1 (by rfl) ⟨5358689, by rfl⟩ : syracuseStep 7144919 = 10717379) B10717379
theorem B4763279 : Blo 2229435 4763279 := bstep (se 1 (by rfl) ⟨3572459, by rfl⟩ : syracuseStep 4763279 = 7144919) B7144919
theorem B3175519 : Blo 2229435 3175519 := bstep (se 1 (by rfl) ⟨2381639, by rfl⟩ : syracuseStep 3175519 = 4763279) B4763279
theorem B4234025 : Blo 2229435 4234025 := bstep (se 2 (by rfl) ⟨1587759, by rfl⟩ : syracuseStep 4234025 = 3175519) B3175519
theorem B2822683 : Blo 2229435 2822683 := bstep (se 1 (by rfl) ⟨2117012, by rfl⟩ : syracuseStep 2822683 = 4234025) B4234025
theorem B3763577 : Blo 2229435 3763577 := bstep (se 2 (by rfl) ⟨1411341, by rfl⟩ : syracuseStep 3763577 = 2822683) B2822683
theorem B2509051 : Blo 2229435 2509051 := bstep (se 1 (by rfl) ⟨1881788, by rfl⟩ : syracuseStep 2509051 = 3763577) B3763577
theorem B3345401 : Blo 2229435 3345401 := bstep (se 2 (by rfl) ⟨1254525, by rfl⟩ : syracuseStep 3345401 = 2509051) B2509051
theorem B2230267 : Blo 2229435 2230267 := bstep (se 1 (by rfl) ⟨1672700, by rfl⟩ : syracuseStep 2230267 = 3345401) B3345401
theorem B3621205 : Blo 2229435 3621205 := bbase (se 10 (by rfl) ⟨5304, by rfl⟩ : syracuseStep 3621205 = 10609) (by norm_num)
theorem B19313093 : Blo 2229435 19313093 := bstep (se 4 (by rfl) ⟨1810602, by rfl⟩ : syracuseStep 19313093 = 3621205) B3621205
theorem B51501581 : Blo 2229435 51501581 := bstep (se 3 (by rfl) ⟨9656546, by rfl⟩ : syracuseStep 51501581 = 19313093) B19313093
theorem B34334387 : Blo 2229435 34334387 := bstep (se 1 (by rfl) ⟨25750790, by rfl⟩ : syracuseStep 34334387 = 51501581) B51501581
theorem B22889591 : Blo 2229435 22889591 := bstep (se 1 (by rfl) ⟨17167193, by rfl⟩ : syracuseStep 22889591 = 34334387) B34334387
theorem B15259727 : Blo 2229435 15259727 := bstep (se 1 (by rfl) ⟨11444795, by rfl⟩ : syracuseStep 15259727 = 22889591) B22889591
theorem B10173151 : Blo 2229435 10173151 := bstep (se 1 (by rfl) ⟨7629863, by rfl⟩ : syracuseStep 10173151 = 15259727) B15259727
theorem B54256805 : Blo 2229435 54256805 := bstep (se 4 (by rfl) ⟨5086575, by rfl⟩ : syracuseStep 54256805 = 10173151) B10173151
theorem B36171203 : Blo 2229435 36171203 := bstep (se 1 (by rfl) ⟨27128402, by rfl⟩ : syracuseStep 36171203 = 54256805) B54256805
theorem B96456541 : Blo 2229435 96456541 := bstep (se 3 (by rfl) ⟨18085601, by rfl⟩ : syracuseStep 96456541 = 36171203) B36171203
theorem B128608721 : Blo 2229435 128608721 := bstep (se 2 (by rfl) ⟨48228270, by rfl⟩ : syracuseStep 128608721 = 96456541) B96456541
theorem B85739147 : Blo 2229435 85739147 := bstep (se 1 (by rfl) ⟨64304360, by rfl⟩ : syracuseStep 85739147 = 128608721) B128608721
theorem B57159431 : Blo 2229435 57159431 := bstep (se 1 (by rfl) ⟨42869573, by rfl⟩ : syracuseStep 57159431 = 85739147) B85739147
theorem B38106287 : Blo 2229435 38106287 := bstep (se 1 (by rfl) ⟨28579715, by rfl⟩ : syracuseStep 38106287 = 57159431) B57159431
theorem B25404191 : Blo 2229435 25404191 := bstep (se 1 (by rfl) ⟨19053143, by rfl⟩ : syracuseStep 25404191 = 38106287) B38106287
theorem B16936127 : Blo 2229435 16936127 := bstep (se 1 (by rfl) ⟨12702095, by rfl⟩ : syracuseStep 16936127 = 25404191) B25404191
theorem B11290751 : Blo 2229435 11290751 := bstep (se 1 (by rfl) ⟨8468063, by rfl⟩ : syracuseStep 11290751 = 16936127) B16936127
theorem B7527167 : Blo 2229435 7527167 := bstep (se 1 (by rfl) ⟨5645375, by rfl⟩ : syracuseStep 7527167 = 11290751) B11290751
theorem B5018111 : Blo 2229435 5018111 := bstep (se 1 (by rfl) ⟨3763583, by rfl⟩ : syracuseStep 5018111 = 7527167) B7527167
theorem B3345407 : Blo 2229435 3345407 := bstep (se 1 (by rfl) ⟨2509055, by rfl⟩ : syracuseStep 3345407 = 5018111) B5018111
theorem B2230271 : Blo 2229435 2230271 := bstep (se 1 (by rfl) ⟨1672703, by rfl⟩ : syracuseStep 2230271 = 3345407) B3345407
theorem B3345413 : Blo 2229435 3345413 := bbase (se 4 (by rfl) ⟨313632, by rfl⟩ : syracuseStep 3345413 = 627265) (by norm_num)
theorem B2230275 : Blo 2229435 2230275 := bstep (se 1 (by rfl) ⟨1672706, by rfl⟩ : syracuseStep 2230275 = 3345413) B3345413
theorem B3763597 : Blo 2229435 3763597 := bbase (se 3 (by rfl) ⟨705674, by rfl⟩ : syracuseStep 3763597 = 1411349) (by norm_num)
theorem B5018129 : Blo 2229435 5018129 := bstep (se 2 (by rfl) ⟨1881798, by rfl⟩ : syracuseStep 5018129 = 3763597) B3763597
theorem B3345419 : Blo 2229435 3345419 := bstep (se 1 (by rfl) ⟨2509064, by rfl⟩ : syracuseStep 3345419 = 5018129) B5018129
theorem B2230279 : Blo 2229435 2230279 := bstep (se 1 (by rfl) ⟨1672709, by rfl⟩ : syracuseStep 2230279 = 3345419) B3345419
theorem B2509069 : Blo 2229435 2509069 := bbase (se 3 (by rfl) ⟨470450, by rfl⟩ : syracuseStep 2509069 = 940901) (by norm_num)
theorem B3345425 : Blo 2229435 3345425 := bstep (se 2 (by rfl) ⟨1254534, by rfl⟩ : syracuseStep 3345425 = 2509069) B2509069
theorem B2230283 : Blo 2229435 2230283 := bstep (se 1 (by rfl) ⟨1672712, by rfl⟩ : syracuseStep 2230283 = 3345425) B3345425
theorem B7527221 : Blo 2229435 7527221 := bbase (se 5 (by rfl) ⟨352838, by rfl⟩ : syracuseStep 7527221 = 705677) (by norm_num)
theorem B5018147 : Blo 2229435 5018147 := bstep (se 1 (by rfl) ⟨3763610, by rfl⟩ : syracuseStep 5018147 = 7527221) B7527221
theorem B3345431 : Blo 2229435 3345431 := bstep (se 1 (by rfl) ⟨2509073, by rfl⟩ : syracuseStep 3345431 = 5018147) B5018147
theorem B2230287 : Blo 2229435 2230287 := bstep (se 1 (by rfl) ⟨1672715, by rfl⟩ : syracuseStep 2230287 = 3345431) B3345431
theorem B3345437 : Blo 2229435 3345437 := bbase (se 3 (by rfl) ⟨627269, by rfl⟩ : syracuseStep 3345437 = 1254539) (by norm_num)
theorem B2230291 : Blo 2229435 2230291 := bstep (se 1 (by rfl) ⟨1672718, by rfl⟩ : syracuseStep 2230291 = 3345437) B3345437
theorem B5018165 : Blo 2229435 5018165 := bbase (se 5 (by rfl) ⟨235226, by rfl⟩ : syracuseStep 5018165 = 470453) (by norm_num)
theorem B3345443 : Blo 2229435 3345443 := bstep (se 1 (by rfl) ⟨2509082, by rfl⟩ : syracuseStep 3345443 = 5018165) B5018165
theorem B2230295 : Blo 2229435 2230295 := bstep (se 1 (by rfl) ⟨1672721, by rfl⟩ : syracuseStep 2230295 = 3345443) B3345443
theorem B9526693 : Blo 2229435 9526693 := bbase (se 4 (by rfl) ⟨893127, by rfl⟩ : syracuseStep 9526693 = 1786255) (by norm_num)
theorem B12702257 : Blo 2229435 12702257 := bstep (se 2 (by rfl) ⟨4763346, by rfl⟩ : syracuseStep 12702257 = 9526693) B9526693
theorem B8468171 : Blo 2229435 8468171 := bstep (se 1 (by rfl) ⟨6351128, by rfl⟩ : syracuseStep 8468171 = 12702257) B12702257
theorem B5645447 : Blo 2229435 5645447 := bstep (se 1 (by rfl) ⟨4234085, by rfl⟩ : syracuseStep 5645447 = 8468171) B8468171
theorem B3763631 : Blo 2229435 3763631 := bstep (se 1 (by rfl) ⟨2822723, by rfl⟩ : syracuseStep 3763631 = 5645447) B5645447
theorem B2509087 : Blo 2229435 2509087 := bstep (se 1 (by rfl) ⟨1881815, by rfl⟩ : syracuseStep 2509087 = 3763631) B3763631
theorem B3345449 : Blo 2229435 3345449 := bstep (se 2 (by rfl) ⟨1254543, by rfl⟩ : syracuseStep 3345449 = 2509087) B2509087
theorem B2230299 : Blo 2229435 2230299 := bstep (se 1 (by rfl) ⟨1672724, by rfl⟩ : syracuseStep 2230299 = 3345449) B3345449
theorem B9526709 : Blo 2229435 9526709 := bbase (se 5 (by rfl) ⟨446564, by rfl⟩ : syracuseStep 9526709 = 893129) (by norm_num)
theorem B6351139 : Blo 2229435 6351139 := bstep (se 1 (by rfl) ⟨4763354, by rfl⟩ : syracuseStep 6351139 = 9526709) B9526709
theorem B8468185 : Blo 2229435 8468185 := bstep (se 2 (by rfl) ⟨3175569, by rfl⟩ : syracuseStep 8468185 = 6351139) B6351139
theorem B11290913 : Blo 2229435 11290913 := bstep (se 2 (by rfl) ⟨4234092, by rfl⟩ : syracuseStep 11290913 = 8468185) B8468185
theorem B7527275 : Blo 2229435 7527275 := bstep (se 1 (by rfl) ⟨5645456, by rfl⟩ : syracuseStep 7527275 = 11290913) B11290913
theorem B5018183 : Blo 2229435 5018183 := bstep (se 1 (by rfl) ⟨3763637, by rfl⟩ : syracuseStep 5018183 = 7527275) B7527275
theorem B3345455 : Blo 2229435 3345455 := bstep (se 1 (by rfl) ⟨2509091, by rfl⟩ : syracuseStep 3345455 = 5018183) B5018183
theorem B2230303 : Blo 2229435 2230303 := bstep (se 1 (by rfl) ⟨1672727, by rfl⟩ : syracuseStep 2230303 = 3345455) B3345455
theorem B3345461 : Blo 2229435 3345461 := bbase (se 5 (by rfl) ⟨156818, by rfl⟩ : syracuseStep 3345461 = 313637) (by norm_num)
theorem B2230307 : Blo 2229435 2230307 := bstep (se 1 (by rfl) ⟨1672730, by rfl⟩ : syracuseStep 2230307 = 3345461) B3345461
theorem B5645477 : Blo 2229435 5645477 := bbase (se 4 (by rfl) ⟨529263, by rfl⟩ : syracuseStep 5645477 = 1058527) (by norm_num)
theorem B3763651 : Blo 2229435 3763651 := bstep (se 1 (by rfl) ⟨2822738, by rfl⟩ : syracuseStep 3763651 = 5645477) B5645477
theorem B5018201 : Blo 2229435 5018201 := bstep (se 2 (by rfl) ⟨1881825, by rfl⟩ : syracuseStep 5018201 = 3763651) B3763651
theorem B3345467 : Blo 2229435 3345467 := bstep (se 1 (by rfl) ⟨2509100, by rfl⟩ : syracuseStep 3345467 = 5018201) B5018201
theorem B2230311 : Blo 2229435 2230311 := bstep (se 1 (by rfl) ⟨1672733, by rfl⟩ : syracuseStep 2230311 = 3345467) B3345467
theorem B2509105 : Blo 2229435 2509105 := bbase (se 2 (by rfl) ⟨940914, by rfl⟩ : syracuseStep 2509105 = 1881829) (by norm_num)
theorem B3345473 : Blo 2229435 3345473 := bstep (se 2 (by rfl) ⟨1254552, by rfl⟩ : syracuseStep 3345473 = 2509105) B2509105
theorem B2230315 : Blo 2229435 2230315 := bstep (se 1 (by rfl) ⟨1672736, by rfl⟩ : syracuseStep 2230315 = 3345473) B3345473
theorem B4763389 : Blo 2229435 4763389 := bbase (se 3 (by rfl) ⟨893135, by rfl⟩ : syracuseStep 4763389 = 1786271) (by norm_num)
theorem B6351185 : Blo 2229435 6351185 := bstep (se 2 (by rfl) ⟨2381694, by rfl⟩ : syracuseStep 6351185 = 4763389) B4763389
theorem B4234123 : Blo 2229435 4234123 := bstep (se 1 (by rfl) ⟨3175592, by rfl⟩ : syracuseStep 4234123 = 6351185) B6351185
theorem B5645497 : Blo 2229435 5645497 := bstep (se 2 (by rfl) ⟨2117061, by rfl⟩ : syracuseStep 5645497 = 4234123) B4234123
theorem B7527329 : Blo 2229435 7527329 := bstep (se 2 (by rfl) ⟨2822748, by rfl⟩ : syracuseStep 7527329 = 5645497) B5645497
theorem B5018219 : Blo 2229435 5018219 := bstep (se 1 (by rfl) ⟨3763664, by rfl⟩ : syracuseStep 5018219 = 7527329) B7527329
theorem B3345479 : Blo 2229435 3345479 := bstep (se 1 (by rfl) ⟨2509109, by rfl⟩ : syracuseStep 3345479 = 5018219) B5018219
theorem B2230319 : Blo 2229435 2230319 := bstep (se 1 (by rfl) ⟨1672739, by rfl⟩ : syracuseStep 2230319 = 3345479) B3345479
theorem B3345485 : Blo 2229435 3345485 := bbase (se 3 (by rfl) ⟨627278, by rfl⟩ : syracuseStep 3345485 = 1254557) (by norm_num)
theorem B2230323 : Blo 2229435 2230323 := bstep (se 1 (by rfl) ⟨1672742, by rfl⟩ : syracuseStep 2230323 = 3345485) B3345485
theorem B5018237 : Blo 2229435 5018237 := bbase (se 3 (by rfl) ⟨940919, by rfl⟩ : syracuseStep 5018237 = 1881839) (by norm_num)
theorem B3345491 : Blo 2229435 3345491 := bstep (se 1 (by rfl) ⟨2509118, by rfl⟩ : syracuseStep 3345491 = 5018237) B5018237
theorem B2230327 : Blo 2229435 2230327 := bstep (se 1 (by rfl) ⟨1672745, by rfl⟩ : syracuseStep 2230327 = 3345491) B3345491
theorem B3763685 : Blo 2229435 3763685 := bbase (se 4 (by rfl) ⟨352845, by rfl⟩ : syracuseStep 3763685 = 705691) (by norm_num)
theorem B2509123 : Blo 2229435 2509123 := bstep (se 1 (by rfl) ⟨1881842, by rfl⟩ : syracuseStep 2509123 = 3763685) B3763685
theorem B3345497 : Blo 2229435 3345497 := bstep (se 2 (by rfl) ⟨1254561, by rfl⟩ : syracuseStep 3345497 = 2509123) B2509123
theorem B2230331 : Blo 2229435 2230331 := bstep (se 1 (by rfl) ⟨1672748, by rfl⟩ : syracuseStep 2230331 = 3345497) B3345497
theorem B7630085 : Blo 2229435 7630085 := bbase (se 4 (by rfl) ⟨715320, by rfl⟩ : syracuseStep 7630085 = 1430641) (by norm_num)
theorem B5086723 : Blo 2229435 5086723 := bstep (se 1 (by rfl) ⟨3815042, by rfl⟩ : syracuseStep 5086723 = 7630085) B7630085
theorem B6782297 : Blo 2229435 6782297 := bstep (se 2 (by rfl) ⟨2543361, by rfl⟩ : syracuseStep 6782297 = 5086723) B5086723
theorem B18086125 : Blo 2229435 18086125 := bstep (se 3 (by rfl) ⟨3391148, by rfl⟩ : syracuseStep 18086125 = 6782297) B6782297
theorem B24114833 : Blo 2229435 24114833 := bstep (se 2 (by rfl) ⟨9043062, by rfl⟩ : syracuseStep 24114833 = 18086125) B18086125
theorem B16076555 : Blo 2229435 16076555 := bstep (se 1 (by rfl) ⟨12057416, by rfl⟩ : syracuseStep 16076555 = 24114833) B24114833
theorem B10717703 : Blo 2229435 10717703 := bstep (se 1 (by rfl) ⟨8038277, by rfl⟩ : syracuseStep 10717703 = 16076555) B16076555
theorem B7145135 : Blo 2229435 7145135 := bstep (se 1 (by rfl) ⟨5358851, by rfl⟩ : syracuseStep 7145135 = 10717703) B10717703
theorem B4763423 : Blo 2229435 4763423 := bstep (se 1 (by rfl) ⟨3572567, by rfl⟩ : syracuseStep 4763423 = 7145135) B7145135
theorem B3175615 : Blo 2229435 3175615 := bstep (se 1 (by rfl) ⟨2381711, by rfl⟩ : syracuseStep 3175615 = 4763423) B4763423
theorem B16936613 : Blo 2229435 16936613 := bstep (se 4 (by rfl) ⟨1587807, by rfl⟩ : syracuseStep 16936613 = 3175615) B3175615
theorem B11291075 : Blo 2229435 11291075 := bstep (se 1 (by rfl) ⟨8468306, by rfl⟩ : syracuseStep 11291075 = 16936613) B16936613
theorem B7527383 : Blo 2229435 7527383 := bstep (se 1 (by rfl) ⟨5645537, by rfl⟩ : syracuseStep 7527383 = 11291075) B11291075
theorem B5018255 : Blo 2229435 5018255 := bstep (se 1 (by rfl) ⟨3763691, by rfl⟩ : syracuseStep 5018255 = 7527383) B7527383
theorem B3345503 : Blo 2229435 3345503 := bstep (se 1 (by rfl) ⟨2509127, by rfl⟩ : syracuseStep 3345503 = 5018255) B5018255
theorem B2230335 : Blo 2229435 2230335 := bstep (se 1 (by rfl) ⟨1672751, by rfl⟩ : syracuseStep 2230335 = 3345503) B3345503
theorem B3345509 : Blo 2229435 3345509 := bbase (se 4 (by rfl) ⟨313641, by rfl⟩ : syracuseStep 3345509 = 627283) (by norm_num)
theorem B2230339 : Blo 2229435 2230339 := bstep (se 1 (by rfl) ⟨1672754, by rfl⟩ : syracuseStep 2230339 = 3345509) B3345509
theorem B3572581 : Blo 2229435 3572581 := bbase (se 4 (by rfl) ⟨334929, by rfl⟩ : syracuseStep 3572581 = 669859) (by norm_num)
theorem B4763441 : Blo 2229435 4763441 := bstep (se 2 (by rfl) ⟨1786290, by rfl⟩ : syracuseStep 4763441 = 3572581) B3572581
theorem B3175627 : Blo 2229435 3175627 := bstep (se 1 (by rfl) ⟨2381720, by rfl⟩ : syracuseStep 3175627 = 4763441) B4763441
theorem B4234169 : Blo 2229435 4234169 := bstep (se 2 (by rfl) ⟨1587813, by rfl⟩ : syracuseStep 4234169 = 3175627) B3175627
theorem B2822779 : Blo 2229435 2822779 := bstep (se 1 (by rfl) ⟨2117084, by rfl⟩ : syracuseStep 2822779 = 4234169) B4234169
theorem B3763705 : Blo 2229435 3763705 := bstep (se 2 (by rfl) ⟨1411389, by rfl⟩ : syracuseStep 3763705 = 2822779) B2822779
theorem B5018273 : Blo 2229435 5018273 := bstep (se 2 (by rfl) ⟨1881852, by rfl⟩ : syracuseStep 5018273 = 3763705) B3763705
theorem B3345515 : Blo 2229435 3345515 := bstep (se 1 (by rfl) ⟨2509136, by rfl⟩ : syracuseStep 3345515 = 5018273) B5018273
theorem B2230343 : Blo 2229435 2230343 := bstep (se 1 (by rfl) ⟨1672757, by rfl⟩ : syracuseStep 2230343 = 3345515) B3345515
theorem B2509141 : Blo 2229435 2509141 := bbase (se 10 (by rfl) ⟨3675, by rfl⟩ : syracuseStep 2509141 = 7351) (by norm_num)
theorem B3345521 : Blo 2229435 3345521 := bstep (se 2 (by rfl) ⟨1254570, by rfl⟩ : syracuseStep 3345521 = 2509141) B2509141
theorem B2230347 : Blo 2229435 2230347 := bstep (se 1 (by rfl) ⟨1672760, by rfl⟩ : syracuseStep 2230347 = 3345521) B3345521
theorem B2822789 : Blo 2229435 2822789 := bbase (se 4 (by rfl) ⟨264636, by rfl⟩ : syracuseStep 2822789 = 529273) (by norm_num)
theorem B7527437 : Blo 2229435 7527437 := bstep (se 3 (by rfl) ⟨1411394, by rfl⟩ : syracuseStep 7527437 = 2822789) B2822789
theorem B5018291 : Blo 2229435 5018291 := bstep (se 1 (by rfl) ⟨3763718, by rfl⟩ : syracuseStep 5018291 = 7527437) B7527437
theorem B3345527 : Blo 2229435 3345527 := bstep (se 1 (by rfl) ⟨2509145, by rfl⟩ : syracuseStep 3345527 = 5018291) B5018291
theorem B2230351 : Blo 2229435 2230351 := bstep (se 1 (by rfl) ⟨1672763, by rfl⟩ : syracuseStep 2230351 = 3345527) B3345527
theorem B3345533 : Blo 2229435 3345533 := bbase (se 3 (by rfl) ⟨627287, by rfl⟩ : syracuseStep 3345533 = 1254575) (by norm_num)
theorem B2230355 : Blo 2229435 2230355 := bstep (se 1 (by rfl) ⟨1672766, by rfl⟩ : syracuseStep 2230355 = 3345533) B3345533
theorem B5018309 : Blo 2229435 5018309 := bbase (se 4 (by rfl) ⟨470466, by rfl⟩ : syracuseStep 5018309 = 940933) (by norm_num)
theorem B3345539 : Blo 2229435 3345539 := bstep (se 1 (by rfl) ⟨2509154, by rfl⟩ : syracuseStep 3345539 = 5018309) B5018309
theorem B2230359 : Blo 2229435 2230359 := bstep (se 1 (by rfl) ⟨1672769, by rfl⟩ : syracuseStep 2230359 = 3345539) B3345539
theorem B8148053 : Blo 2229435 8148053 := bbase (se 8 (by rfl) ⟨47742, by rfl⟩ : syracuseStep 8148053 = 95485) (by norm_num)
theorem B5432035 : Blo 2229435 5432035 := bstep (se 1 (by rfl) ⟨4074026, by rfl⟩ : syracuseStep 5432035 = 8148053) B8148053
theorem B7242713 : Blo 2229435 7242713 := bstep (se 2 (by rfl) ⟨2716017, by rfl⟩ : syracuseStep 7242713 = 5432035) B5432035
theorem B4828475 : Blo 2229435 4828475 := bstep (se 1 (by rfl) ⟨3621356, by rfl⟩ : syracuseStep 4828475 = 7242713) B7242713
theorem B3218983 : Blo 2229435 3218983 := bstep (se 1 (by rfl) ⟨2414237, by rfl⟩ : syracuseStep 3218983 = 4828475) B4828475
theorem B17167909 : Blo 2229435 17167909 := bstep (se 4 (by rfl) ⟨1609491, by rfl⟩ : syracuseStep 17167909 = 3218983) B3218983
theorem B22890545 : Blo 2229435 22890545 := bstep (se 2 (by rfl) ⟨8583954, by rfl⟩ : syracuseStep 22890545 = 17167909) B17167909
theorem B15260363 : Blo 2229435 15260363 := bstep (se 1 (by rfl) ⟨11445272, by rfl⟩ : syracuseStep 15260363 = 22890545) B22890545
theorem B10173575 : Blo 2229435 10173575 := bstep (se 1 (by rfl) ⟨7630181, by rfl⟩ : syracuseStep 10173575 = 15260363) B15260363
theorem B6782383 : Blo 2229435 6782383 := bstep (se 1 (by rfl) ⟨5086787, by rfl⟩ : syracuseStep 6782383 = 10173575) B10173575
theorem B9043177 : Blo 2229435 9043177 := bstep (se 2 (by rfl) ⟨3391191, by rfl⟩ : syracuseStep 9043177 = 6782383) B6782383
theorem B12057569 : Blo 2229435 12057569 := bstep (se 2 (by rfl) ⟨4521588, by rfl⟩ : syracuseStep 12057569 = 9043177) B9043177
theorem B8038379 : Blo 2229435 8038379 := bstep (se 1 (by rfl) ⟨6028784, by rfl⟩ : syracuseStep 8038379 = 12057569) B12057569
theorem B21435677 : Blo 2229435 21435677 := bstep (se 3 (by rfl) ⟨4019189, by rfl⟩ : syracuseStep 21435677 = 8038379) B8038379
theorem B14290451 : Blo 2229435 14290451 := bstep (se 1 (by rfl) ⟨10717838, by rfl⟩ : syracuseStep 14290451 = 21435677) B21435677
theorem B9526967 : Blo 2229435 9526967 := bstep (se 1 (by rfl) ⟨7145225, by rfl⟩ : syracuseStep 9526967 = 14290451) B14290451
theorem B6351311 : Blo 2229435 6351311 := bstep (se 1 (by rfl) ⟨4763483, by rfl⟩ : syracuseStep 6351311 = 9526967) B9526967
theorem B4234207 : Blo 2229435 4234207 := bstep (se 1 (by rfl) ⟨3175655, by rfl⟩ : syracuseStep 4234207 = 6351311) B6351311
theorem B5645609 : Blo 2229435 5645609 := bstep (se 2 (by rfl) ⟨2117103, by rfl⟩ : syracuseStep 5645609 = 4234207) B4234207
theorem B3763739 : Blo 2229435 3763739 := bstep (se 1 (by rfl) ⟨2822804, by rfl⟩ : syracuseStep 3763739 = 5645609) B5645609
theorem B2509159 : Blo 2229435 2509159 := bstep (se 1 (by rfl) ⟨1881869, by rfl⟩ : syracuseStep 2509159 = 3763739) B3763739
theorem B3345545 : Blo 2229435 3345545 := bstep (se 2 (by rfl) ⟨1254579, by rfl⟩ : syracuseStep 3345545 = 2509159) B2509159
theorem B2230363 : Blo 2229435 2230363 := bstep (se 1 (by rfl) ⟨1672772, by rfl⟩ : syracuseStep 2230363 = 3345545) B3345545
theorem B11291237 : Blo 2229435 11291237 := bbase (se 4 (by rfl) ⟨1058553, by rfl⟩ : syracuseStep 11291237 = 2117107) (by norm_num)
theorem B7527491 : Blo 2229435 7527491 := bstep (se 1 (by rfl) ⟨5645618, by rfl⟩ : syracuseStep 7527491 = 11291237) B11291237
theorem B5018327 : Blo 2229435 5018327 := bstep (se 1 (by rfl) ⟨3763745, by rfl⟩ : syracuseStep 5018327 = 7527491) B7527491
theorem B3345551 : Blo 2229435 3345551 := bstep (se 1 (by rfl) ⟨2509163, by rfl⟩ : syracuseStep 3345551 = 5018327) B5018327
theorem B2230367 : Blo 2229435 2230367 := bstep (se 1 (by rfl) ⟨1672775, by rfl⟩ : syracuseStep 2230367 = 3345551) B3345551
theorem B3345557 : Blo 2229435 3345557 := bbase (se 6 (by rfl) ⟨78411, by rfl⟩ : syracuseStep 3345557 = 156823) (by norm_num)
theorem B2230371 : Blo 2229435 2230371 := bstep (se 1 (by rfl) ⟨1672778, by rfl⟩ : syracuseStep 2230371 = 3345557) B3345557
theorem B4828501 : Blo 2229435 4828501 := bbase (se 11 (by rfl) ⟨3536, by rfl⟩ : syracuseStep 4828501 = 7073) (by norm_num)
theorem B6438001 : Blo 2229435 6438001 := bstep (se 2 (by rfl) ⟨2414250, by rfl⟩ : syracuseStep 6438001 = 4828501) B4828501
theorem B8584001 : Blo 2229435 8584001 := bstep (se 2 (by rfl) ⟨3219000, by rfl⟩ : syracuseStep 8584001 = 6438001) B6438001
theorem B5722667 : Blo 2229435 5722667 := bstep (se 1 (by rfl) ⟨4292000, by rfl⟩ : syracuseStep 5722667 = 8584001) B8584001
theorem B3815111 : Blo 2229435 3815111 := bstep (se 1 (by rfl) ⟨2861333, by rfl⟩ : syracuseStep 3815111 = 5722667) B5722667
theorem B2543407 : Blo 2229435 2543407 := bstep (se 1 (by rfl) ⟨1907555, by rfl⟩ : syracuseStep 2543407 = 3815111) B3815111
theorem B13564837 : Blo 2229435 13564837 := bstep (se 4 (by rfl) ⟨1271703, by rfl⟩ : syracuseStep 13564837 = 2543407) B2543407
theorem B18086449 : Blo 2229435 18086449 := bstep (se 2 (by rfl) ⟨6782418, by rfl⟩ : syracuseStep 18086449 = 13564837) B13564837
theorem B24115265 : Blo 2229435 24115265 := bstep (se 2 (by rfl) ⟨9043224, by rfl⟩ : syracuseStep 24115265 = 18086449) B18086449
theorem B16076843 : Blo 2229435 16076843 := bstep (se 1 (by rfl) ⟨12057632, by rfl⟩ : syracuseStep 16076843 = 24115265) B24115265
theorem B10717895 : Blo 2229435 10717895 := bstep (se 1 (by rfl) ⟨8038421, by rfl⟩ : syracuseStep 10717895 = 16076843) B16076843
theorem B7145263 : Blo 2229435 7145263 := bstep (se 1 (by rfl) ⟨5358947, by rfl⟩ : syracuseStep 7145263 = 10717895) B10717895
theorem B9527017 : Blo 2229435 9527017 := bstep (se 2 (by rfl) ⟨3572631, by rfl⟩ : syracuseStep 9527017 = 7145263) B7145263
theorem B12702689 : Blo 2229435 12702689 := bstep (se 2 (by rfl) ⟨4763508, by rfl⟩ : syracuseStep 12702689 = 9527017) B9527017
theorem B8468459 : Blo 2229435 8468459 := bstep (se 1 (by rfl) ⟨6351344, by rfl⟩ : syracuseStep 8468459 = 12702689) B12702689
theorem B5645639 : Blo 2229435 5645639 := bstep (se 1 (by rfl) ⟨4234229, by rfl⟩ : syracuseStep 5645639 = 8468459) B8468459
theorem B3763759 : Blo 2229435 3763759 := bstep (se 1 (by rfl) ⟨2822819, by rfl⟩ : syracuseStep 3763759 = 5645639) B5645639
theorem B5018345 : Blo 2229435 5018345 := bstep (se 2 (by rfl) ⟨1881879, by rfl⟩ : syracuseStep 5018345 = 3763759) B3763759
theorem B3345563 : Blo 2229435 3345563 := bstep (se 1 (by rfl) ⟨2509172, by rfl⟩ : syracuseStep 3345563 = 5018345) B5018345
theorem B2230375 : Blo 2229435 2230375 := bstep (se 1 (by rfl) ⟨1672781, by rfl⟩ : syracuseStep 2230375 = 3345563) B3345563
theorem B2509177 : Blo 2229435 2509177 := bbase (se 2 (by rfl) ⟨940941, by rfl⟩ : syracuseStep 2509177 = 1881883) (by norm_num)
theorem B3345569 : Blo 2229435 3345569 := bstep (se 2 (by rfl) ⟨1254588, by rfl⟩ : syracuseStep 3345569 = 2509177) B2509177
theorem B2230379 : Blo 2229435 2230379 := bstep (se 1 (by rfl) ⟨1672784, by rfl⟩ : syracuseStep 2230379 = 3345569) B3345569
theorem B4521629 : Blo 2229435 4521629 := bbase (se 3 (by rfl) ⟨847805, by rfl⟩ : syracuseStep 4521629 = 1695611) (by norm_num)
theorem B3014419 : Blo 2229435 3014419 := bstep (se 1 (by rfl) ⟨2260814, by rfl⟩ : syracuseStep 3014419 = 4521629) B4521629
theorem B4019225 : Blo 2229435 4019225 := bstep (se 2 (by rfl) ⟨1507209, by rfl⟩ : syracuseStep 4019225 = 3014419) B3014419
theorem B10717933 : Blo 2229435 10717933 := bstep (se 3 (by rfl) ⟨2009612, by rfl⟩ : syracuseStep 10717933 = 4019225) B4019225
theorem B14290577 : Blo 2229435 14290577 := bstep (se 2 (by rfl) ⟨5358966, by rfl⟩ : syracuseStep 14290577 = 10717933) B10717933
theorem B9527051 : Blo 2229435 9527051 := bstep (se 1 (by rfl) ⟨7145288, by rfl⟩ : syracuseStep 9527051 = 14290577) B14290577
theorem B6351367 : Blo 2229435 6351367 := bstep (se 1 (by rfl) ⟨4763525, by rfl⟩ : syracuseStep 6351367 = 9527051) B9527051
theorem B8468489 : Blo 2229435 8468489 := bstep (se 2 (by rfl) ⟨3175683, by rfl⟩ : syracuseStep 8468489 = 6351367) B6351367
theorem B5645659 : Blo 2229435 5645659 := bstep (se 1 (by rfl) ⟨4234244, by rfl⟩ : syracuseStep 5645659 = 8468489) B8468489
theorem B7527545 : Blo 2229435 7527545 := bstep (se 2 (by rfl) ⟨2822829, by rfl⟩ : syracuseStep 7527545 = 5645659) B5645659
theorem B5018363 : Blo 2229435 5018363 := bstep (se 1 (by rfl) ⟨3763772, by rfl⟩ : syracuseStep 5018363 = 7527545) B7527545
theorem B3345575 : Blo 2229435 3345575 := bstep (se 1 (by rfl) ⟨2509181, by rfl⟩ : syracuseStep 3345575 = 5018363) B5018363
theorem B2230383 : Blo 2229435 2230383 := bstep (se 1 (by rfl) ⟨1672787, by rfl⟩ : syracuseStep 2230383 = 3345575) B3345575
theorem B3345581 : Blo 2229435 3345581 := bbase (se 3 (by rfl) ⟨627296, by rfl⟩ : syracuseStep 3345581 = 1254593) (by norm_num)
theorem B2230387 : Blo 2229435 2230387 := bstep (se 1 (by rfl) ⟨1672790, by rfl⟩ : syracuseStep 2230387 = 3345581) B3345581
theorem B5018381 : Blo 2229435 5018381 := bbase (se 3 (by rfl) ⟨940946, by rfl⟩ : syracuseStep 5018381 = 1881893) (by norm_num)
theorem B3345587 : Blo 2229435 3345587 := bstep (se 1 (by rfl) ⟨2509190, by rfl⟩ : syracuseStep 3345587 = 5018381) B5018381
theorem B2230391 : Blo 2229435 2230391 := bstep (se 1 (by rfl) ⟨1672793, by rfl⟩ : syracuseStep 2230391 = 3345587) B3345587
theorem B2822845 : Blo 2229435 2822845 := bbase (se 3 (by rfl) ⟨529283, by rfl⟩ : syracuseStep 2822845 = 1058567) (by norm_num)
theorem B3763793 : Blo 2229435 3763793 := bstep (se 2 (by rfl) ⟨1411422, by rfl⟩ : syracuseStep 3763793 = 2822845) B2822845
theorem B2509195 : Blo 2229435 2509195 := bstep (se 1 (by rfl) ⟨1881896, by rfl⟩ : syracuseStep 2509195 = 3763793) B3763793
theorem B3345593 : Blo 2229435 3345593 := bstep (se 2 (by rfl) ⟨1254597, by rfl⟩ : syracuseStep 3345593 = 2509195) B2509195
theorem B2230395 : Blo 2229435 2230395 := bstep (se 1 (by rfl) ⟨1672796, by rfl⟩ : syracuseStep 2230395 = 3345593) B3345593
theorem B32592725 : Blo 2229435 32592725 := bbase (se 9 (by rfl) ⟨95486, by rfl⟩ : syracuseStep 32592725 = 190973) (by norm_num)
theorem B21728483 : Blo 2229435 21728483 := bstep (se 1 (by rfl) ⟨16296362, by rfl⟩ : syracuseStep 21728483 = 32592725) B32592725
theorem B14485655 : Blo 2229435 14485655 := bstep (se 1 (by rfl) ⟨10864241, by rfl⟩ : syracuseStep 14485655 = 21728483) B21728483
theorem B38628413 : Blo 2229435 38628413 := bstep (se 3 (by rfl) ⟨7242827, by rfl⟩ : syracuseStep 38628413 = 14485655) B14485655
theorem B25752275 : Blo 2229435 25752275 := bstep (se 1 (by rfl) ⟨19314206, by rfl⟩ : syracuseStep 25752275 = 38628413) B38628413
theorem B17168183 : Blo 2229435 17168183 := bstep (se 1 (by rfl) ⟨12876137, by rfl⟩ : syracuseStep 17168183 = 25752275) B25752275
theorem B11445455 : Blo 2229435 11445455 := bstep (se 1 (by rfl) ⟨8584091, by rfl⟩ : syracuseStep 11445455 = 17168183) B17168183
theorem B7630303 : Blo 2229435 7630303 := bstep (se 1 (by rfl) ⟨5722727, by rfl⟩ : syracuseStep 7630303 = 11445455) B11445455
theorem B10173737 : Blo 2229435 10173737 := bstep (se 2 (by rfl) ⟨3815151, by rfl⟩ : syracuseStep 10173737 = 7630303) B7630303
theorem B6782491 : Blo 2229435 6782491 := bstep (se 1 (by rfl) ⟨5086868, by rfl⟩ : syracuseStep 6782491 = 10173737) B10173737
theorem B9043321 : Blo 2229435 9043321 := bstep (se 2 (by rfl) ⟨3391245, by rfl⟩ : syracuseStep 9043321 = 6782491) B6782491
theorem B12057761 : Blo 2229435 12057761 := bstep (se 2 (by rfl) ⟨4521660, by rfl⟩ : syracuseStep 12057761 = 9043321) B9043321
theorem B8038507 : Blo 2229435 8038507 := bstep (se 1 (by rfl) ⟨6028880, by rfl⟩ : syracuseStep 8038507 = 12057761) B12057761
theorem B10718009 : Blo 2229435 10718009 := bstep (se 2 (by rfl) ⟨4019253, by rfl⟩ : syracuseStep 10718009 = 8038507) B8038507
theorem B7145339 : Blo 2229435 7145339 := bstep (se 1 (by rfl) ⟨5359004, by rfl⟩ : syracuseStep 7145339 = 10718009) B10718009
theorem B19054237 : Blo 2229435 19054237 := bstep (se 3 (by rfl) ⟨3572669, by rfl⟩ : syracuseStep 19054237 = 7145339) B7145339
theorem B25405649 : Blo 2229435 25405649 := bstep (se 2 (by rfl) ⟨9527118, by rfl⟩ : syracuseStep 25405649 = 19054237) B19054237
theorem B16937099 : Blo 2229435 16937099 := bstep (se 1 (by rfl) ⟨12702824, by rfl⟩ : syracuseStep 16937099 = 25405649) B25405649
theorem B11291399 : Blo 2229435 11291399 := bstep (se 1 (by rfl) ⟨8468549, by rfl⟩ : syracuseStep 11291399 = 16937099) B16937099
theorem B7527599 : Blo 2229435 7527599 := bstep (se 1 (by rfl) ⟨5645699, by rfl⟩ : syracuseStep 7527599 = 11291399) B11291399
theorem B5018399 : Blo 2229435 5018399 := bstep (se 1 (by rfl) ⟨3763799, by rfl⟩ : syracuseStep 5018399 = 7527599) B7527599
theorem B3345599 : Blo 2229435 3345599 := bstep (se 1 (by rfl) ⟨2509199, by rfl⟩ : syracuseStep 3345599 = 5018399) B5018399
theorem B2230399 : Blo 2229435 2230399 := bstep (se 1 (by rfl) ⟨1672799, by rfl⟩ : syracuseStep 2230399 = 3345599) B3345599
theorem B3345605 : Blo 2229435 3345605 := bbase (se 4 (by rfl) ⟨313650, by rfl⟩ : syracuseStep 3345605 = 627301) (by norm_num)
theorem B2230403 : Blo 2229435 2230403 := bstep (se 1 (by rfl) ⟨1672802, by rfl⟩ : syracuseStep 2230403 = 3345605) B3345605
theorem B3763813 : Blo 2229435 3763813 := bbase (se 4 (by rfl) ⟨352857, by rfl⟩ : syracuseStep 3763813 = 705715) (by norm_num)
theorem B5018417 : Blo 2229435 5018417 := bstep (se 2 (by rfl) ⟨1881906, by rfl⟩ : syracuseStep 5018417 = 3763813) B3763813
theorem B3345611 : Blo 2229435 3345611 := bstep (se 1 (by rfl) ⟨2509208, by rfl⟩ : syracuseStep 3345611 = 5018417) B5018417
theorem B2230407 : Blo 2229435 2230407 := bstep (se 1 (by rfl) ⟨1672805, by rfl⟩ : syracuseStep 2230407 = 3345611) B3345611
theorem B2509213 : Blo 2229435 2509213 := bbase (se 3 (by rfl) ⟨470477, by rfl⟩ : syracuseStep 2509213 = 940955) (by norm_num)
theorem B3345617 : Blo 2229435 3345617 := bstep (se 2 (by rfl) ⟨1254606, by rfl⟩ : syracuseStep 3345617 = 2509213) B2509213
theorem B2230411 : Blo 2229435 2230411 := bstep (se 1 (by rfl) ⟨1672808, by rfl⟩ : syracuseStep 2230411 = 3345617) B3345617
theorem B7527653 : Blo 2229435 7527653 := bbase (se 4 (by rfl) ⟨705717, by rfl⟩ : syracuseStep 7527653 = 1411435) (by norm_num)
theorem B5018435 : Blo 2229435 5018435 := bstep (se 1 (by rfl) ⟨3763826, by rfl⟩ : syracuseStep 5018435 = 7527653) B7527653
theorem B3345623 : Blo 2229435 3345623 := bstep (se 1 (by rfl) ⟨2509217, by rfl⟩ : syracuseStep 3345623 = 5018435) B5018435
theorem B2230415 : Blo 2229435 2230415 := bstep (se 1 (by rfl) ⟨1672811, by rfl⟩ : syracuseStep 2230415 = 3345623) B3345623
theorem B3345629 : Blo 2229435 3345629 := bbase (se 3 (by rfl) ⟨627305, by rfl⟩ : syracuseStep 3345629 = 1254611) (by norm_num)
theorem B2230419 : Blo 2229435 2230419 := bstep (se 1 (by rfl) ⟨1672814, by rfl⟩ : syracuseStep 2230419 = 3345629) B3345629
theorem B5018453 : Blo 2229435 5018453 := bbase (se 9 (by rfl) ⟨14702, by rfl⟩ : syracuseStep 5018453 = 29405) (by norm_num)
theorem B3345635 : Blo 2229435 3345635 := bstep (se 1 (by rfl) ⟨2509226, by rfl⟩ : syracuseStep 3345635 = 5018453) B5018453
theorem B2230423 : Blo 2229435 2230423 := bstep (se 1 (by rfl) ⟨1672817, by rfl⟩ : syracuseStep 2230423 = 3345635) B3345635
theorem B6351493 : Blo 2229435 6351493 := bbase (se 4 (by rfl) ⟨595452, by rfl⟩ : syracuseStep 6351493 = 1190905) (by norm_num)
theorem B8468657 : Blo 2229435 8468657 := bstep (se 2 (by rfl) ⟨3175746, by rfl⟩ : syracuseStep 8468657 = 6351493) B6351493
theorem B5645771 : Blo 2229435 5645771 := bstep (se 1 (by rfl) ⟨4234328, by rfl⟩ : syracuseStep 5645771 = 8468657) B8468657
theorem B3763847 : Blo 2229435 3763847 := bstep (se 1 (by rfl) ⟨2822885, by rfl⟩ : syracuseStep 3763847 = 5645771) B5645771
theorem B2509231 : Blo 2229435 2509231 := bstep (se 1 (by rfl) ⟨1881923, by rfl⟩ : syracuseStep 2509231 = 3763847) B3763847
theorem B3345641 : Blo 2229435 3345641 := bstep (se 2 (by rfl) ⟨1254615, by rfl⟩ : syracuseStep 3345641 = 2509231) B2509231
theorem B2230427 : Blo 2229435 2230427 := bstep (se 1 (by rfl) ⟨1672820, by rfl⟩ : syracuseStep 2230427 = 3345641) B3345641
theorem B4521725 : Blo 2229435 4521725 := bbase (se 3 (by rfl) ⟨847823, by rfl⟩ : syracuseStep 4521725 = 1695647) (by norm_num)
theorem B48231733 : Blo 2229435 48231733 := bstep (se 5 (by rfl) ⟨2260862, by rfl⟩ : syracuseStep 48231733 = 4521725) B4521725
theorem B64308977 : Blo 2229435 64308977 := bstep (se 2 (by rfl) ⟨24115866, by rfl⟩ : syracuseStep 64308977 = 48231733) B48231733
theorem B42872651 : Blo 2229435 42872651 := bstep (se 1 (by rfl) ⟨32154488, by rfl⟩ : syracuseStep 42872651 = 64308977) B64308977
theorem B28581767 : Blo 2229435 28581767 := bstep (se 1 (by rfl) ⟨21436325, by rfl⟩ : syracuseStep 28581767 = 42872651) B42872651
theorem B19054511 : Blo 2229435 19054511 := bstep (se 1 (by rfl) ⟨14290883, by rfl⟩ : syracuseStep 19054511 = 28581767) B28581767
theorem B12703007 : Blo 2229435 12703007 := bstep (se 1 (by rfl) ⟨9527255, by rfl⟩ : syracuseStep 12703007 = 19054511) B19054511
theorem B8468671 : Blo 2229435 8468671 := bstep (se 1 (by rfl) ⟨6351503, by rfl⟩ : syracuseStep 8468671 = 12703007) B12703007
theorem B11291561 : Blo 2229435 11291561 := bstep (se 2 (by rfl) ⟨4234335, by rfl⟩ : syracuseStep 11291561 = 8468671) B8468671
theorem B7527707 : Blo 2229435 7527707 := bstep (se 1 (by rfl) ⟨5645780, by rfl⟩ : syracuseStep 7527707 = 11291561) B11291561
theorem B5018471 : Blo 2229435 5018471 := bstep (se 1 (by rfl) ⟨3763853, by rfl⟩ : syracuseStep 5018471 = 7527707) B7527707
theorem B3345647 : Blo 2229435 3345647 := bstep (se 1 (by rfl) ⟨2509235, by rfl⟩ : syracuseStep 3345647 = 5018471) B5018471
theorem B2230431 : Blo 2229435 2230431 := bstep (se 1 (by rfl) ⟨1672823, by rfl⟩ : syracuseStep 2230431 = 3345647) B3345647
theorem B3345653 : Blo 2229435 3345653 := bbase (se 5 (by rfl) ⟨156827, by rfl⟩ : syracuseStep 3345653 = 313655) (by norm_num)
theorem B2230435 : Blo 2229435 2230435 := bstep (se 1 (by rfl) ⟨1672826, by rfl⟩ : syracuseStep 2230435 = 3345653) B3345653
theorem B20625461 : Blo 2229435 20625461 := bbase (se 5 (by rfl) ⟨966818, by rfl⟩ : syracuseStep 20625461 = 1933637) (by norm_num)
theorem B13750307 : Blo 2229435 13750307 := bstep (se 1 (by rfl) ⟨10312730, by rfl⟩ : syracuseStep 13750307 = 20625461) B20625461
theorem B9166871 : Blo 2229435 9166871 := bstep (se 1 (by rfl) ⟨6875153, by rfl⟩ : syracuseStep 9166871 = 13750307) B13750307
theorem B24444989 : Blo 2229435 24444989 := bstep (se 3 (by rfl) ⟨4583435, by rfl⟩ : syracuseStep 24444989 = 9166871) B9166871
theorem B16296659 : Blo 2229435 16296659 := bstep (se 1 (by rfl) ⟨12222494, by rfl⟩ : syracuseStep 16296659 = 24444989) B24444989
theorem B10864439 : Blo 2229435 10864439 := bstep (se 1 (by rfl) ⟨8148329, by rfl⟩ : syracuseStep 10864439 = 16296659) B16296659
theorem B7242959 : Blo 2229435 7242959 := bstep (se 1 (by rfl) ⟨5432219, by rfl⟩ : syracuseStep 7242959 = 10864439) B10864439
theorem B4828639 : Blo 2229435 4828639 := bstep (se 1 (by rfl) ⟨3621479, by rfl⟩ : syracuseStep 4828639 = 7242959) B7242959
theorem B6438185 : Blo 2229435 6438185 := bstep (se 2 (by rfl) ⟨2414319, by rfl⟩ : syracuseStep 6438185 = 4828639) B4828639
theorem B4292123 : Blo 2229435 4292123 := bstep (se 1 (by rfl) ⟨3219092, by rfl⟩ : syracuseStep 4292123 = 6438185) B6438185
theorem B11445661 : Blo 2229435 11445661 := bstep (se 3 (by rfl) ⟨2146061, by rfl⟩ : syracuseStep 11445661 = 4292123) B4292123
theorem B15260881 : Blo 2229435 15260881 := bstep (se 2 (by rfl) ⟨5722830, by rfl⟩ : syracuseStep 15260881 = 11445661) B11445661
theorem B20347841 : Blo 2229435 20347841 := bstep (se 2 (by rfl) ⟨7630440, by rfl⟩ : syracuseStep 20347841 = 15260881) B15260881
theorem B13565227 : Blo 2229435 13565227 := bstep (se 1 (by rfl) ⟨10173920, by rfl⟩ : syracuseStep 13565227 = 20347841) B20347841
theorem B18086969 : Blo 2229435 18086969 := bstep (se 2 (by rfl) ⟨6782613, by rfl⟩ : syracuseStep 18086969 = 13565227) B13565227
theorem B12057979 : Blo 2229435 12057979 := bstep (se 1 (by rfl) ⟨9043484, by rfl⟩ : syracuseStep 12057979 = 18086969) B18086969
theorem B16077305 : Blo 2229435 16077305 := bstep (se 2 (by rfl) ⟨6028989, by rfl⟩ : syracuseStep 16077305 = 12057979) B12057979
theorem B10718203 : Blo 2229435 10718203 := bstep (se 1 (by rfl) ⟨8038652, by rfl⟩ : syracuseStep 10718203 = 16077305) B16077305
theorem B14290937 : Blo 2229435 14290937 := bstep (se 2 (by rfl) ⟨5359101, by rfl⟩ : syracuseStep 14290937 = 10718203) B10718203
theorem B9527291 : Blo 2229435 9527291 := bstep (se 1 (by rfl) ⟨7145468, by rfl⟩ : syracuseStep 9527291 = 14290937) B14290937
theorem B6351527 : Blo 2229435 6351527 := bstep (se 1 (by rfl) ⟨4763645, by rfl⟩ : syracuseStep 6351527 = 9527291) B9527291
theorem B4234351 : Blo 2229435 4234351 := bstep (se 1 (by rfl) ⟨3175763, by rfl⟩ : syracuseStep 4234351 = 6351527) B6351527
theorem B5645801 : Blo 2229435 5645801 := bstep (se 2 (by rfl) ⟨2117175, by rfl⟩ : syracuseStep 5645801 = 4234351) B4234351
theorem B3763867 : Blo 2229435 3763867 := bstep (se 1 (by rfl) ⟨2822900, by rfl⟩ : syracuseStep 3763867 = 5645801) B5645801
theorem B5018489 : Blo 2229435 5018489 := bstep (se 2 (by rfl) ⟨1881933, by rfl⟩ : syracuseStep 5018489 = 3763867) B3763867
theorem B3345659 : Blo 2229435 3345659 := bstep (se 1 (by rfl) ⟨2509244, by rfl⟩ : syracuseStep 3345659 = 5018489) B5018489
theorem B2230439 : Blo 2229435 2230439 := bstep (se 1 (by rfl) ⟨1672829, by rfl⟩ : syracuseStep 2230439 = 3345659) B3345659
theorem B2509249 : Blo 2229435 2509249 := bbase (se 2 (by rfl) ⟨940968, by rfl⟩ : syracuseStep 2509249 = 1881937) (by norm_num)
theorem B3345665 : Blo 2229435 3345665 := bstep (se 2 (by rfl) ⟨1254624, by rfl⟩ : syracuseStep 3345665 = 2509249) B2509249
theorem B2230443 : Blo 2229435 2230443 := bstep (se 1 (by rfl) ⟨1672832, by rfl⟩ : syracuseStep 2230443 = 3345665) B3345665
theorem B5645821 : Blo 2229435 5645821 := bbase (se 3 (by rfl) ⟨1058591, by rfl⟩ : syracuseStep 5645821 = 2117183) (by norm_num)
theorem B7527761 : Blo 2229435 7527761 := bstep (se 2 (by rfl) ⟨2822910, by rfl⟩ : syracuseStep 7527761 = 5645821) B5645821
theorem B5018507 : Blo 2229435 5018507 := bstep (se 1 (by rfl) ⟨3763880, by rfl⟩ : syracuseStep 5018507 = 7527761) B7527761
theorem B3345671 : Blo 2229435 3345671 := bstep (se 1 (by rfl) ⟨2509253, by rfl⟩ : syracuseStep 3345671 = 5018507) B5018507
theorem B2230447 : Blo 2229435 2230447 := bstep (se 1 (by rfl) ⟨1672835, by rfl⟩ : syracuseStep 2230447 = 3345671) B3345671
theorem B3345677 : Blo 2229435 3345677 := bbase (se 3 (by rfl) ⟨627314, by rfl⟩ : syracuseStep 3345677 = 1254629) (by norm_num)
theorem B2230451 : Blo 2229435 2230451 := bstep (se 1 (by rfl) ⟨1672838, by rfl⟩ : syracuseStep 2230451 = 3345677) B3345677
theorem B5018525 : Blo 2229435 5018525 := bbase (se 3 (by rfl) ⟨940973, by rfl⟩ : syracuseStep 5018525 = 1881947) (by norm_num)
theorem B3345683 : Blo 2229435 3345683 := bstep (se 1 (by rfl) ⟨2509262, by rfl⟩ : syracuseStep 3345683 = 5018525) B5018525
theorem B2230455 : Blo 2229435 2230455 := bstep (se 1 (by rfl) ⟨1672841, by rfl⟩ : syracuseStep 2230455 = 3345683) B3345683
theorem B3763901 : Blo 2229435 3763901 := bbase (se 3 (by rfl) ⟨705731, by rfl⟩ : syracuseStep 3763901 = 1411463) (by norm_num)
theorem B2509267 : Blo 2229435 2509267 := bstep (se 1 (by rfl) ⟨1881950, by rfl⟩ : syracuseStep 2509267 = 3763901) B3763901
theorem B3345689 : Blo 2229435 3345689 := bstep (se 2 (by rfl) ⟨1254633, by rfl⟩ : syracuseStep 3345689 = 2509267) B2509267
theorem B2230459 : Blo 2229435 2230459 := bstep (se 1 (by rfl) ⟨1672844, by rfl⟩ : syracuseStep 2230459 = 3345689) B3345689
theorem B12703189 : Blo 2229435 12703189 := bbase (se 7 (by rfl) ⟨148865, by rfl⟩ : syracuseStep 12703189 = 297731) (by norm_num)
theorem B16937585 : Blo 2229435 16937585 := bstep (se 2 (by rfl) ⟨6351594, by rfl⟩ : syracuseStep 16937585 = 12703189) B12703189
theorem B11291723 : Blo 2229435 11291723 := bstep (se 1 (by rfl) ⟨8468792, by rfl⟩ : syracuseStep 11291723 = 16937585) B16937585
theorem B7527815 : Blo 2229435 7527815 := bstep (se 1 (by rfl) ⟨5645861, by rfl⟩ : syracuseStep 7527815 = 11291723) B11291723
theorem B5018543 : Blo 2229435 5018543 := bstep (se 1 (by rfl) ⟨3763907, by rfl⟩ : syracuseStep 5018543 = 7527815) B7527815
theorem B3345695 : Blo 2229435 3345695 := bstep (se 1 (by rfl) ⟨2509271, by rfl⟩ : syracuseStep 3345695 = 5018543) B5018543
theorem B2230463 : Blo 2229435 2230463 := bstep (se 1 (by rfl) ⟨1672847, by rfl⟩ : syracuseStep 2230463 = 3345695) B3345695
theorem B3345701 : Blo 2229435 3345701 := bbase (se 4 (by rfl) ⟨313659, by rfl⟩ : syracuseStep 3345701 = 627319) (by norm_num)
theorem B2230467 : Blo 2229435 2230467 := bstep (se 1 (by rfl) ⟨1672850, by rfl⟩ : syracuseStep 2230467 = 3345701) B3345701
theorem B2822941 : Blo 2229435 2822941 := bbase (se 3 (by rfl) ⟨529301, by rfl⟩ : syracuseStep 2822941 = 1058603) (by norm_num)
theorem B3763921 : Blo 2229435 3763921 := bstep (se 2 (by rfl) ⟨1411470, by rfl⟩ : syracuseStep 3763921 = 2822941) B2822941
theorem B5018561 : Blo 2229435 5018561 := bstep (se 2 (by rfl) ⟨1881960, by rfl⟩ : syracuseStep 5018561 = 3763921) B3763921
theorem B3345707 : Blo 2229435 3345707 := bstep (se 1 (by rfl) ⟨2509280, by rfl⟩ : syracuseStep 3345707 = 5018561) B5018561
theorem B2230471 : Blo 2229435 2230471 := bstep (se 1 (by rfl) ⟨1672853, by rfl⟩ : syracuseStep 2230471 = 3345707) B3345707
theorem B2509285 : Blo 2229435 2509285 := bbase (se 4 (by rfl) ⟨235245, by rfl⟩ : syracuseStep 2509285 = 470491) (by norm_num)
theorem B3345713 : Blo 2229435 3345713 := bstep (se 2 (by rfl) ⟨1254642, by rfl⟩ : syracuseStep 3345713 = 2509285) B2509285
theorem B2230475 : Blo 2229435 2230475 := bstep (se 1 (by rfl) ⟨1672856, by rfl⟩ : syracuseStep 2230475 = 3345713) B3345713
theorem B5087053 : Blo 2229435 5087053 := bbase (se 3 (by rfl) ⟨953822, by rfl⟩ : syracuseStep 5087053 = 1907645) (by norm_num)
theorem B6782737 : Blo 2229435 6782737 := bstep (se 2 (by rfl) ⟨2543526, by rfl⟩ : syracuseStep 6782737 = 5087053) B5087053
theorem B9043649 : Blo 2229435 9043649 := bstep (se 2 (by rfl) ⟨3391368, by rfl⟩ : syracuseStep 9043649 = 6782737) B6782737
theorem B6029099 : Blo 2229435 6029099 := bstep (se 1 (by rfl) ⟨4521824, by rfl⟩ : syracuseStep 6029099 = 9043649) B9043649
theorem B4019399 : Blo 2229435 4019399 := bstep (se 1 (by rfl) ⟨3014549, by rfl⟩ : syracuseStep 4019399 = 6029099) B6029099
theorem B2679599 : Blo 2229435 2679599 := bstep (se 1 (by rfl) ⟨2009699, by rfl⟩ : syracuseStep 2679599 = 4019399) B4019399
theorem B7145597 : Blo 2229435 7145597 := bstep (se 3 (by rfl) ⟨1339799, by rfl⟩ : syracuseStep 7145597 = 2679599) B2679599
theorem B4763731 : Blo 2229435 4763731 := bstep (se 1 (by rfl) ⟨3572798, by rfl⟩ : syracuseStep 4763731 = 7145597) B7145597
theorem B6351641 : Blo 2229435 6351641 := bstep (se 2 (by rfl) ⟨2381865, by rfl⟩ : syracuseStep 6351641 = 4763731) B4763731
theorem B4234427 : Blo 2229435 4234427 := bstep (se 1 (by rfl) ⟨3175820, by rfl⟩ : syracuseStep 4234427 = 6351641) B6351641
theorem B2822951 : Blo 2229435 2822951 := bstep (se 1 (by rfl) ⟨2117213, by rfl⟩ : syracuseStep 2822951 = 4234427) B4234427
theorem B7527869 : Blo 2229435 7527869 := bstep (se 3 (by rfl) ⟨1411475, by rfl⟩ : syracuseStep 7527869 = 2822951) B2822951
theorem B5018579 : Blo 2229435 5018579 := bstep (se 1 (by rfl) ⟨3763934, by rfl⟩ : syracuseStep 5018579 = 7527869) B7527869
theorem B3345719 : Blo 2229435 3345719 := bstep (se 1 (by rfl) ⟨2509289, by rfl⟩ : syracuseStep 3345719 = 5018579) B5018579
theorem B2230479 : Blo 2229435 2230479 := bstep (se 1 (by rfl) ⟨1672859, by rfl⟩ : syracuseStep 2230479 = 3345719) B3345719
theorem B3345725 : Blo 2229435 3345725 := bbase (se 3 (by rfl) ⟨627323, by rfl⟩ : syracuseStep 3345725 = 1254647) (by norm_num)
theorem B2230483 : Blo 2229435 2230483 := bstep (se 1 (by rfl) ⟨1672862, by rfl⟩ : syracuseStep 2230483 = 3345725) B3345725
theorem B5018597 : Blo 2229435 5018597 := bbase (se 4 (by rfl) ⟨470493, by rfl⟩ : syracuseStep 5018597 = 940987) (by norm_num)
theorem B3345731 : Blo 2229435 3345731 := bstep (se 1 (by rfl) ⟨2509298, by rfl⟩ : syracuseStep 3345731 = 5018597) B5018597
theorem B2230487 : Blo 2229435 2230487 := bstep (se 1 (by rfl) ⟨1672865, by rfl⟩ : syracuseStep 2230487 = 3345731) B3345731
theorem B5645933 : Blo 2229435 5645933 := bbase (se 3 (by rfl) ⟨1058612, by rfl⟩ : syracuseStep 5645933 = 2117225) (by norm_num)
theorem B3763955 : Blo 2229435 3763955 := bstep (se 1 (by rfl) ⟨2822966, by rfl⟩ : syracuseStep 3763955 = 5645933) B5645933
theorem B2509303 : Blo 2229435 2509303 := bstep (se 1 (by rfl) ⟨1881977, by rfl⟩ : syracuseStep 2509303 = 3763955) B3763955
theorem B3345737 : Blo 2229435 3345737 := bstep (se 2 (by rfl) ⟨1254651, by rfl⟩ : syracuseStep 3345737 = 2509303) B2509303
theorem B2230491 : Blo 2229435 2230491 := bstep (se 1 (by rfl) ⟨1672868, by rfl⟩ : syracuseStep 2230491 = 3345737) B3345737
theorem B4763765 : Blo 2229435 4763765 := bbase (se 5 (by rfl) ⟨223301, by rfl⟩ : syracuseStep 4763765 = 446603) (by norm_num)
theorem B3175843 : Blo 2229435 3175843 := bstep (se 1 (by rfl) ⟨2381882, by rfl⟩ : syracuseStep 3175843 = 4763765) B4763765
theorem B4234457 : Blo 2229435 4234457 := bstep (se 2 (by rfl) ⟨1587921, by rfl⟩ : syracuseStep 4234457 = 3175843) B3175843
theorem B11291885 : Blo 2229435 11291885 := bstep (se 3 (by rfl) ⟨2117228, by rfl⟩ : syracuseStep 11291885 = 4234457) B4234457
theorem B7527923 : Blo 2229435 7527923 := bstep (se 1 (by rfl) ⟨5645942, by rfl⟩ : syracuseStep 7527923 = 11291885) B11291885
theorem B5018615 : Blo 2229435 5018615 := bstep (se 1 (by rfl) ⟨3763961, by rfl⟩ : syracuseStep 5018615 = 7527923) B7527923
theorem B3345743 : Blo 2229435 3345743 := bstep (se 1 (by rfl) ⟨2509307, by rfl⟩ : syracuseStep 3345743 = 5018615) B5018615
theorem B2230495 : Blo 2229435 2230495 := bstep (se 1 (by rfl) ⟨1672871, by rfl⟩ : syracuseStep 2230495 = 3345743) B3345743
theorem B3345749 : Blo 2229435 3345749 := bbase (se 11 (by rfl) ⟨2450, by rfl⟩ : syracuseStep 3345749 = 4901) (by norm_num)
theorem B2230499 : Blo 2229435 2230499 := bstep (se 1 (by rfl) ⟨1672874, by rfl⟩ : syracuseStep 2230499 = 3345749) B3345749
theorem B3572837 : Blo 2229435 3572837 := bbase (se 4 (by rfl) ⟨334953, by rfl⟩ : syracuseStep 3572837 = 669907) (by norm_num)
theorem B2381891 : Blo 2229435 2381891 := bstep (se 1 (by rfl) ⟨1786418, by rfl⟩ : syracuseStep 2381891 = 3572837) B3572837
theorem B6351709 : Blo 2229435 6351709 := bstep (se 3 (by rfl) ⟨1190945, by rfl⟩ : syracuseStep 6351709 = 2381891) B2381891
theorem B8468945 : Blo 2229435 8468945 := bstep (se 2 (by rfl) ⟨3175854, by rfl⟩ : syracuseStep 8468945 = 6351709) B6351709
theorem B5645963 : Blo 2229435 5645963 := bstep (se 1 (by rfl) ⟨4234472, by rfl⟩ : syracuseStep 5645963 = 8468945) B8468945
theorem B3763975 : Blo 2229435 3763975 := bstep (se 1 (by rfl) ⟨2822981, by rfl⟩ : syracuseStep 3763975 = 5645963) B5645963
theorem B5018633 : Blo 2229435 5018633 := bstep (se 2 (by rfl) ⟨1881987, by rfl⟩ : syracuseStep 5018633 = 3763975) B3763975
theorem B3345755 : Blo 2229435 3345755 := bstep (se 1 (by rfl) ⟨2509316, by rfl⟩ : syracuseStep 3345755 = 5018633) B5018633
theorem B2230503 : Blo 2229435 2230503 := bstep (se 1 (by rfl) ⟨1672877, by rfl⟩ : syracuseStep 2230503 = 3345755) B3345755
theorem B2509321 : Blo 2229435 2509321 := bbase (se 2 (by rfl) ⟨940995, by rfl⟩ : syracuseStep 2509321 = 1881991) (by norm_num)
theorem B3345761 : Blo 2229435 3345761 := bstep (se 2 (by rfl) ⟨1254660, by rfl⟩ : syracuseStep 3345761 = 2509321) B2509321
theorem B2230507 : Blo 2229435 2230507 := bstep (se 1 (by rfl) ⟨1672880, by rfl⟩ : syracuseStep 2230507 = 3345761) B3345761
theorem B4583581 : Blo 2229435 4583581 := bbase (se 3 (by rfl) ⟨859421, by rfl⟩ : syracuseStep 4583581 = 1718843) (by norm_num)
theorem B24445765 : Blo 2229435 24445765 := bstep (se 4 (by rfl) ⟨2291790, by rfl⟩ : syracuseStep 24445765 = 4583581) B4583581
theorem B130377413 : Blo 2229435 130377413 := bstep (se 4 (by rfl) ⟨12222882, by rfl⟩ : syracuseStep 130377413 = 24445765) B24445765
theorem B86918275 : Blo 2229435 86918275 := bstep (se 1 (by rfl) ⟨65188706, by rfl⟩ : syracuseStep 86918275 = 130377413) B130377413
theorem B115891033 : Blo 2229435 115891033 := bstep (se 2 (by rfl) ⟨43459137, by rfl⟩ : syracuseStep 115891033 = 86918275) B86918275
theorem B154521377 : Blo 2229435 154521377 := bstep (se 2 (by rfl) ⟨57945516, by rfl⟩ : syracuseStep 154521377 = 115891033) B115891033
theorem B103014251 : Blo 2229435 103014251 := bstep (se 1 (by rfl) ⟨77260688, by rfl⟩ : syracuseStep 103014251 = 154521377) B154521377
theorem B68676167 : Blo 2229435 68676167 := bstep (se 1 (by rfl) ⟨51507125, by rfl⟩ : syracuseStep 68676167 = 103014251) B103014251
theorem B45784111 : Blo 2229435 45784111 := bstep (se 1 (by rfl) ⟨34338083, by rfl⟩ : syracuseStep 45784111 = 68676167) B68676167
theorem B61045481 : Blo 2229435 61045481 := bstep (se 2 (by rfl) ⟨22892055, by rfl⟩ : syracuseStep 61045481 = 45784111) B45784111
theorem B40696987 : Blo 2229435 40696987 := bstep (se 1 (by rfl) ⟨30522740, by rfl⟩ : syracuseStep 40696987 = 61045481) B61045481
theorem B54262649 : Blo 2229435 54262649 := bstep (se 2 (by rfl) ⟨20348493, by rfl⟩ : syracuseStep 54262649 = 40696987) B40696987
theorem B36175099 : Blo 2229435 36175099 := bstep (se 1 (by rfl) ⟨27131324, by rfl⟩ : syracuseStep 36175099 = 54262649) B54262649
theorem B48233465 : Blo 2229435 48233465 := bstep (se 2 (by rfl) ⟨18087549, by rfl⟩ : syracuseStep 48233465 = 36175099) B36175099
theorem B32155643 : Blo 2229435 32155643 := bstep (se 1 (by rfl) ⟨24116732, by rfl⟩ : syracuseStep 32155643 = 48233465) B48233465
theorem B21437095 : Blo 2229435 21437095 := bstep (se 1 (by rfl) ⟨16077821, by rfl⟩ : syracuseStep 21437095 = 32155643) B32155643
theorem B28582793 : Blo 2229435 28582793 := bstep (se 2 (by rfl) ⟨10718547, by rfl⟩ : syracuseStep 28582793 = 21437095) B21437095
theorem B19055195 : Blo 2229435 19055195 := bstep (se 1 (by rfl) ⟨14291396, by rfl⟩ : syracuseStep 19055195 = 28582793) B28582793
theorem B12703463 : Blo 2229435 12703463 := bstep (se 1 (by rfl) ⟨9527597, by rfl⟩ : syracuseStep 12703463 = 19055195) B19055195
theorem B8468975 : Blo 2229435 8468975 := bstep (se 1 (by rfl) ⟨6351731, by rfl⟩ : syracuseStep 8468975 = 12703463) B12703463
theorem B5645983 : Blo 2229435 5645983 := bstep (se 1 (by rfl) ⟨4234487, by rfl⟩ : syracuseStep 5645983 = 8468975) B8468975
theorem B7527977 : Blo 2229435 7527977 := bstep (se 2 (by rfl) ⟨2822991, by rfl⟩ : syracuseStep 7527977 = 5645983) B5645983
theorem B5018651 : Blo 2229435 5018651 := bstep (se 1 (by rfl) ⟨3763988, by rfl⟩ : syracuseStep 5018651 = 7527977) B7527977
theorem B3345767 : Blo 2229435 3345767 := bstep (se 1 (by rfl) ⟨2509325, by rfl⟩ : syracuseStep 3345767 = 5018651) B5018651
theorem B2230511 : Blo 2229435 2230511 := bstep (se 1 (by rfl) ⟨1672883, by rfl⟩ : syracuseStep 2230511 = 3345767) B3345767
theorem B3345773 : Blo 2229435 3345773 := bbase (se 3 (by rfl) ⟨627332, by rfl⟩ : syracuseStep 3345773 = 1254665) (by norm_num)
theorem B2230515 : Blo 2229435 2230515 := bstep (se 1 (by rfl) ⟨1672886, by rfl⟩ : syracuseStep 2230515 = 3345773) B3345773
theorem B5018669 : Blo 2229435 5018669 := bbase (se 3 (by rfl) ⟨941000, by rfl⟩ : syracuseStep 5018669 = 1882001) (by norm_num)
theorem B3345779 : Blo 2229435 3345779 := bstep (se 1 (by rfl) ⟨2509334, by rfl⟩ : syracuseStep 3345779 = 5018669) B5018669
theorem B2230519 : Blo 2229435 2230519 := bstep (se 1 (by rfl) ⟨1672889, by rfl⟩ : syracuseStep 2230519 = 3345779) B3345779
theorem B14291477 : Blo 2229435 14291477 := bbase (se 6 (by rfl) ⟨334956, by rfl⟩ : syracuseStep 14291477 = 669913) (by norm_num)
theorem B9527651 : Blo 2229435 9527651 := bstep (se 1 (by rfl) ⟨7145738, by rfl⟩ : syracuseStep 9527651 = 14291477) B14291477
theorem B6351767 : Blo 2229435 6351767 := bstep (se 1 (by rfl) ⟨4763825, by rfl⟩ : syracuseStep 6351767 = 9527651) B9527651
theorem B4234511 : Blo 2229435 4234511 := bstep (se 1 (by rfl) ⟨3175883, by rfl⟩ : syracuseStep 4234511 = 6351767) B6351767
theorem B2823007 : Blo 2229435 2823007 := bstep (se 1 (by rfl) ⟨2117255, by rfl⟩ : syracuseStep 2823007 = 4234511) B4234511
theorem B3764009 : Blo 2229435 3764009 := bstep (se 2 (by rfl) ⟨1411503, by rfl⟩ : syracuseStep 3764009 = 2823007) B2823007
theorem B2509339 : Blo 2229435 2509339 := bstep (se 1 (by rfl) ⟨1882004, by rfl⟩ : syracuseStep 2509339 = 3764009) B3764009
theorem B3345785 : Blo 2229435 3345785 := bstep (se 2 (by rfl) ⟨1254669, by rfl⟩ : syracuseStep 3345785 = 2509339) B2509339
theorem B2230523 : Blo 2229435 2230523 := bstep (se 1 (by rfl) ⟨1672892, by rfl⟩ : syracuseStep 2230523 = 3345785) B3345785
theorem B7145749 : Blo 2229435 7145749 := bbase (se 6 (by rfl) ⟨167478, by rfl⟩ : syracuseStep 7145749 = 334957) (by norm_num)
theorem B38110661 : Blo 2229435 38110661 := bstep (se 4 (by rfl) ⟨3572874, by rfl⟩ : syracuseStep 38110661 = 7145749) B7145749
theorem B25407107 : Blo 2229435 25407107 := bstep (se 1 (by rfl) ⟨19055330, by rfl⟩ : syracuseStep 25407107 = 38110661) B38110661
theorem B16938071 : Blo 2229435 16938071 := bstep (se 1 (by rfl) ⟨12703553, by rfl⟩ : syracuseStep 16938071 = 25407107) B25407107
theorem B11292047 : Blo 2229435 11292047 := bstep (se 1 (by rfl) ⟨8469035, by rfl⟩ : syracuseStep 11292047 = 16938071) B16938071
theorem B7528031 : Blo 2229435 7528031 := bstep (se 1 (by rfl) ⟨5646023, by rfl⟩ : syracuseStep 7528031 = 11292047) B11292047
theorem B5018687 : Blo 2229435 5018687 := bstep (se 1 (by rfl) ⟨3764015, by rfl⟩ : syracuseStep 5018687 = 7528031) B7528031
theorem B3345791 : Blo 2229435 3345791 := bstep (se 1 (by rfl) ⟨2509343, by rfl⟩ : syracuseStep 3345791 = 5018687) B5018687
theorem B2230527 : Blo 2229435 2230527 := bstep (se 1 (by rfl) ⟨1672895, by rfl⟩ : syracuseStep 2230527 = 3345791) B3345791
theorem B3345797 : Blo 2229435 3345797 := bbase (se 4 (by rfl) ⟨313668, by rfl⟩ : syracuseStep 3345797 = 627337) (by norm_num)
theorem B2230531 : Blo 2229435 2230531 := bstep (se 1 (by rfl) ⟨1672898, by rfl⟩ : syracuseStep 2230531 = 3345797) B3345797
theorem B3764029 : Blo 2229435 3764029 := bbase (se 3 (by rfl) ⟨705755, by rfl⟩ : syracuseStep 3764029 = 1411511) (by norm_num)
theorem B5018705 : Blo 2229435 5018705 := bstep (se 2 (by rfl) ⟨1882014, by rfl⟩ : syracuseStep 5018705 = 3764029) B3764029
theorem B3345803 : Blo 2229435 3345803 := bstep (se 1 (by rfl) ⟨2509352, by rfl⟩ : syracuseStep 3345803 = 5018705) B5018705
theorem B2230535 : Blo 2229435 2230535 := bstep (se 1 (by rfl) ⟨1672901, by rfl⟩ : syracuseStep 2230535 = 3345803) B3345803
theorem B2509357 : Blo 2229435 2509357 := bbase (se 3 (by rfl) ⟨470504, by rfl⟩ : syracuseStep 2509357 = 941009) (by norm_num)
theorem B3345809 : Blo 2229435 3345809 := bstep (se 2 (by rfl) ⟨1254678, by rfl⟩ : syracuseStep 3345809 = 2509357) B2509357
theorem B2230539 : Blo 2229435 2230539 := bstep (se 1 (by rfl) ⟨1672904, by rfl⟩ : syracuseStep 2230539 = 3345809) B3345809
theorem B7528085 : Blo 2229435 7528085 := bbase (se 6 (by rfl) ⟨176439, by rfl⟩ : syracuseStep 7528085 = 352879) (by norm_num)
theorem B5018723 : Blo 2229435 5018723 := bstep (se 1 (by rfl) ⟨3764042, by rfl⟩ : syracuseStep 5018723 = 7528085) B7528085
theorem B3345815 : Blo 2229435 3345815 := bstep (se 1 (by rfl) ⟨2509361, by rfl⟩ : syracuseStep 3345815 = 5018723) B5018723
theorem B2230543 : Blo 2229435 2230543 := bstep (se 1 (by rfl) ⟨1672907, by rfl⟩ : syracuseStep 2230543 = 3345815) B3345815
theorem B3345821 : Blo 2229435 3345821 := bbase (se 3 (by rfl) ⟨627341, by rfl⟩ : syracuseStep 3345821 = 1254683) (by norm_num)
theorem B2230547 : Blo 2229435 2230547 := bstep (se 1 (by rfl) ⟨1672910, by rfl⟩ : syracuseStep 2230547 = 3345821) B3345821
theorem B5018741 : Blo 2229435 5018741 := bbase (se 5 (by rfl) ⟨235253, by rfl⟩ : syracuseStep 5018741 = 470507) (by norm_num)
theorem B3345827 : Blo 2229435 3345827 := bstep (se 1 (by rfl) ⟨2509370, by rfl⟩ : syracuseStep 3345827 = 5018741) B5018741
theorem B2230551 : Blo 2229435 2230551 := bstep (se 1 (by rfl) ⟨1672913, by rfl⟩ : syracuseStep 2230551 = 3345827) B3345827
theorem B19055573 : Blo 2229435 19055573 := bbase (se 7 (by rfl) ⟨223307, by rfl⟩ : syracuseStep 19055573 = 446615) (by norm_num)
theorem B12703715 : Blo 2229435 12703715 := bstep (se 1 (by rfl) ⟨9527786, by rfl⟩ : syracuseStep 12703715 = 19055573) B19055573
theorem B8469143 : Blo 2229435 8469143 := bstep (se 1 (by rfl) ⟨6351857, by rfl⟩ : syracuseStep 8469143 = 12703715) B12703715
theorem B5646095 : Blo 2229435 5646095 := bstep (se 1 (by rfl) ⟨4234571, by rfl⟩ : syracuseStep 5646095 = 8469143) B8469143
theorem B3764063 : Blo 2229435 3764063 := bstep (se 1 (by rfl) ⟨2823047, by rfl⟩ : syracuseStep 3764063 = 5646095) B5646095
theorem B2509375 : Blo 2229435 2509375 := bstep (se 1 (by rfl) ⟨1882031, by rfl⟩ : syracuseStep 2509375 = 3764063) B3764063
theorem B3345833 : Blo 2229435 3345833 := bstep (se 2 (by rfl) ⟨1254687, by rfl⟩ : syracuseStep 3345833 = 2509375) B2509375
theorem B2230555 : Blo 2229435 2230555 := bstep (se 1 (by rfl) ⟨1672916, by rfl⟩ : syracuseStep 2230555 = 3345833) B3345833
theorem B8469157 : Blo 2229435 8469157 := bbase (se 4 (by rfl) ⟨793983, by rfl⟩ : syracuseStep 8469157 = 1587967) (by norm_num)
theorem B11292209 : Blo 2229435 11292209 := bstep (se 2 (by rfl) ⟨4234578, by rfl⟩ : syracuseStep 11292209 = 8469157) B8469157
theorem B7528139 : Blo 2229435 7528139 := bstep (se 1 (by rfl) ⟨5646104, by rfl⟩ : syracuseStep 7528139 = 11292209) B11292209
theorem B5018759 : Blo 2229435 5018759 := bstep (se 1 (by rfl) ⟨3764069, by rfl⟩ : syracuseStep 5018759 = 7528139) B7528139
theorem B3345839 : Blo 2229435 3345839 := bstep (se 1 (by rfl) ⟨2509379, by rfl⟩ : syracuseStep 3345839 = 5018759) B5018759
theorem B2230559 : Blo 2229435 2230559 := bstep (se 1 (by rfl) ⟨1672919, by rfl⟩ : syracuseStep 2230559 = 3345839) B3345839
theorem B3345845 : Blo 2229435 3345845 := bbase (se 5 (by rfl) ⟨156836, by rfl⟩ : syracuseStep 3345845 = 313673) (by norm_num)
theorem B2230563 : Blo 2229435 2230563 := bstep (se 1 (by rfl) ⟨1672922, by rfl⟩ : syracuseStep 2230563 = 3345845) B3345845
theorem B5646125 : Blo 2229435 5646125 := bbase (se 3 (by rfl) ⟨1058648, by rfl⟩ : syracuseStep 5646125 = 2117297) (by norm_num)
theorem B3764083 : Blo 2229435 3764083 := bstep (se 1 (by rfl) ⟨2823062, by rfl⟩ : syracuseStep 3764083 = 5646125) B5646125
theorem B5018777 : Blo 2229435 5018777 := bstep (se 2 (by rfl) ⟨1882041, by rfl⟩ : syracuseStep 5018777 = 3764083) B3764083
theorem B3345851 : Blo 2229435 3345851 := bstep (se 1 (by rfl) ⟨2509388, by rfl⟩ : syracuseStep 3345851 = 5018777) B5018777
theorem B2230567 : Blo 2229435 2230567 := bstep (se 1 (by rfl) ⟨1672925, by rfl⟩ : syracuseStep 2230567 = 3345851) B3345851
theorem B2509393 : Blo 2229435 2509393 := bbase (se 2 (by rfl) ⟨941022, by rfl⟩ : syracuseStep 2509393 = 1882045) (by norm_num)
theorem B3345857 : Blo 2229435 3345857 := bstep (se 2 (by rfl) ⟨1254696, by rfl⟩ : syracuseStep 3345857 = 2509393) B2509393
theorem B2230571 : Blo 2229435 2230571 := bstep (se 1 (by rfl) ⟨1672928, by rfl⟩ : syracuseStep 2230571 = 3345857) B3345857
theorem B3175957 : Blo 2229435 3175957 := bbase (se 6 (by rfl) ⟨74436, by rfl⟩ : syracuseStep 3175957 = 148873) (by norm_num)
theorem B4234609 : Blo 2229435 4234609 := bstep (se 2 (by rfl) ⟨1587978, by rfl⟩ : syracuseStep 4234609 = 3175957) B3175957
theorem B5646145 : Blo 2229435 5646145 := bstep (se 2 (by rfl) ⟨2117304, by rfl⟩ : syracuseStep 5646145 = 4234609) B4234609
theorem B7528193 : Blo 2229435 7528193 := bstep (se 2 (by rfl) ⟨2823072, by rfl⟩ : syracuseStep 7528193 = 5646145) B5646145
theorem B5018795 : Blo 2229435 5018795 := bstep (se 1 (by rfl) ⟨3764096, by rfl⟩ : syracuseStep 5018795 = 7528193) B7528193
theorem B3345863 : Blo 2229435 3345863 := bstep (se 1 (by rfl) ⟨2509397, by rfl⟩ : syracuseStep 3345863 = 5018795) B5018795
theorem B2230575 : Blo 2229435 2230575 := bstep (se 1 (by rfl) ⟨1672931, by rfl⟩ : syracuseStep 2230575 = 3345863) B3345863
theorem B3345869 : Blo 2229435 3345869 := bbase (se 3 (by rfl) ⟨627350, by rfl⟩ : syracuseStep 3345869 = 1254701) (by norm_num)
theorem B2230579 : Blo 2229435 2230579 := bstep (se 1 (by rfl) ⟨1672934, by rfl⟩ : syracuseStep 2230579 = 3345869) B3345869
theorem B5018813 : Blo 2229435 5018813 := bbase (se 3 (by rfl) ⟨941027, by rfl⟩ : syracuseStep 5018813 = 1882055) (by norm_num)
theorem B3345875 : Blo 2229435 3345875 := bstep (se 1 (by rfl) ⟨2509406, by rfl⟩ : syracuseStep 3345875 = 5018813) B5018813
theorem B2230583 : Blo 2229435 2230583 := bstep (se 1 (by rfl) ⟨1672937, by rfl⟩ : syracuseStep 2230583 = 3345875) B3345875
theorem B3764117 : Blo 2229435 3764117 := bbase (se 6 (by rfl) ⟨88221, by rfl⟩ : syracuseStep 3764117 = 176443) (by norm_num)
theorem B2509411 : Blo 2229435 2509411 := bstep (se 1 (by rfl) ⟨1882058, by rfl⟩ : syracuseStep 2509411 = 3764117) B3764117
theorem B3345881 : Blo 2229435 3345881 := bstep (se 2 (by rfl) ⟨1254705, by rfl⟩ : syracuseStep 3345881 = 2509411) B2509411
theorem B2230587 : Blo 2229435 2230587 := bstep (se 1 (by rfl) ⟨1672940, by rfl⟩ : syracuseStep 2230587 = 3345881) B3345881
theorem B2679733 : Blo 2229435 2679733 := bbase (se 5 (by rfl) ⟨125612, by rfl⟩ : syracuseStep 2679733 = 251225) (by norm_num)
theorem B14291909 : Blo 2229435 14291909 := bstep (se 4 (by rfl) ⟨1339866, by rfl⟩ : syracuseStep 14291909 = 2679733) B2679733
theorem B9527939 : Blo 2229435 9527939 := bstep (se 1 (by rfl) ⟨7145954, by rfl⟩ : syracuseStep 9527939 = 14291909) B14291909
theorem B6351959 : Blo 2229435 6351959 := bstep (se 1 (by rfl) ⟨4763969, by rfl⟩ : syracuseStep 6351959 = 9527939) B9527939
theorem B16938557 : Blo 2229435 16938557 := bstep (se 3 (by rfl) ⟨3175979, by rfl⟩ : syracuseStep 16938557 = 6351959) B6351959
theorem B11292371 : Blo 2229435 11292371 := bstep (se 1 (by rfl) ⟨8469278, by rfl⟩ : syracuseStep 11292371 = 16938557) B16938557
theorem B7528247 : Blo 2229435 7528247 := bstep (se 1 (by rfl) ⟨5646185, by rfl⟩ : syracuseStep 7528247 = 11292371) B11292371
theorem B5018831 : Blo 2229435 5018831 := bstep (se 1 (by rfl) ⟨3764123, by rfl⟩ : syracuseStep 5018831 = 7528247) B7528247
theorem B3345887 : Blo 2229435 3345887 := bstep (se 1 (by rfl) ⟨2509415, by rfl⟩ : syracuseStep 3345887 = 5018831) B5018831
theorem B2230591 : Blo 2229435 2230591 := bstep (se 1 (by rfl) ⟨1672943, by rfl⟩ : syracuseStep 2230591 = 3345887) B3345887
theorem B3345893 : Blo 2229435 3345893 := bbase (se 4 (by rfl) ⟨313677, by rfl⟩ : syracuseStep 3345893 = 627355) (by norm_num)
theorem B2230595 : Blo 2229435 2230595 := bstep (se 1 (by rfl) ⟨1672946, by rfl⟩ : syracuseStep 2230595 = 3345893) B3345893
theorem B20349301 : Blo 2229435 20349301 := bbase (se 5 (by rfl) ⟨953873, by rfl⟩ : syracuseStep 20349301 = 1907747) (by norm_num)
theorem B27132401 : Blo 2229435 27132401 := bstep (se 2 (by rfl) ⟨10174650, by rfl⟩ : syracuseStep 27132401 = 20349301) B20349301
theorem B18088267 : Blo 2229435 18088267 := bstep (se 1 (by rfl) ⟨13566200, by rfl⟩ : syracuseStep 18088267 = 27132401) B27132401
theorem B24117689 : Blo 2229435 24117689 := bstep (se 2 (by rfl) ⟨9044133, by rfl⟩ : syracuseStep 24117689 = 18088267) B18088267
theorem B16078459 : Blo 2229435 16078459 := bstep (se 1 (by rfl) ⟨12058844, by rfl⟩ : syracuseStep 16078459 = 24117689) B24117689
theorem B21437945 : Blo 2229435 21437945 := bstep (se 2 (by rfl) ⟨8039229, by rfl⟩ : syracuseStep 21437945 = 16078459) B16078459
theorem B14291963 : Blo 2229435 14291963 := bstep (se 1 (by rfl) ⟨10718972, by rfl⟩ : syracuseStep 14291963 = 21437945) B21437945
theorem B9527975 : Blo 2229435 9527975 := bstep (se 1 (by rfl) ⟨7145981, by rfl⟩ : syracuseStep 9527975 = 14291963) B14291963
theorem B6351983 : Blo 2229435 6351983 := bstep (se 1 (by rfl) ⟨4763987, by rfl⟩ : syracuseStep 6351983 = 9527975) B9527975
theorem B4234655 : Blo 2229435 4234655 := bstep (se 1 (by rfl) ⟨3175991, by rfl⟩ : syracuseStep 4234655 = 6351983) B6351983
theorem B2823103 : Blo 2229435 2823103 := bstep (se 1 (by rfl) ⟨2117327, by rfl⟩ : syracuseStep 2823103 = 4234655) B4234655
theorem B3764137 : Blo 2229435 3764137 := bstep (se 2 (by rfl) ⟨1411551, by rfl⟩ : syracuseStep 3764137 = 2823103) B2823103
theorem B5018849 : Blo 2229435 5018849 := bstep (se 2 (by rfl) ⟨1882068, by rfl⟩ : syracuseStep 5018849 = 3764137) B3764137
theorem B3345899 : Blo 2229435 3345899 := bstep (se 1 (by rfl) ⟨2509424, by rfl⟩ : syracuseStep 3345899 = 5018849) B5018849
theorem B2230599 : Blo 2229435 2230599 := bstep (se 1 (by rfl) ⟨1672949, by rfl⟩ : syracuseStep 2230599 = 3345899) B3345899
theorem B2509429 : Blo 2229435 2509429 := bbase (se 5 (by rfl) ⟨117629, by rfl⟩ : syracuseStep 2509429 = 235259) (by norm_num)
theorem B3345905 : Blo 2229435 3345905 := bstep (se 2 (by rfl) ⟨1254714, by rfl⟩ : syracuseStep 3345905 = 2509429) B2509429
theorem B2230603 : Blo 2229435 2230603 := bstep (se 1 (by rfl) ⟨1672952, by rfl⟩ : syracuseStep 2230603 = 3345905) B3345905
theorem B2823113 : Blo 2229435 2823113 := bbase (se 2 (by rfl) ⟨1058667, by rfl⟩ : syracuseStep 2823113 = 2117335) (by norm_num)
theorem B7528301 : Blo 2229435 7528301 := bstep (se 3 (by rfl) ⟨1411556, by rfl⟩ : syracuseStep 7528301 = 2823113) B2823113
theorem B5018867 : Blo 2229435 5018867 := bstep (se 1 (by rfl) ⟨3764150, by rfl⟩ : syracuseStep 5018867 = 7528301) B7528301
theorem B3345911 : Blo 2229435 3345911 := bstep (se 1 (by rfl) ⟨2509433, by rfl⟩ : syracuseStep 3345911 = 5018867) B5018867
theorem B2230607 : Blo 2229435 2230607 := bstep (se 1 (by rfl) ⟨1672955, by rfl⟩ : syracuseStep 2230607 = 3345911) B3345911
theorem B3345917 : Blo 2229435 3345917 := bbase (se 3 (by rfl) ⟨627359, by rfl⟩ : syracuseStep 3345917 = 1254719) (by norm_num)
theorem B2230611 : Blo 2229435 2230611 := bstep (se 1 (by rfl) ⟨1672958, by rfl⟩ : syracuseStep 2230611 = 3345917) B3345917
theorem B5018885 : Blo 2229435 5018885 := bbase (se 4 (by rfl) ⟨470520, by rfl⟩ : syracuseStep 5018885 = 941041) (by norm_num)
theorem B3345923 : Blo 2229435 3345923 := bstep (se 1 (by rfl) ⟨2509442, by rfl⟩ : syracuseStep 3345923 = 5018885) B5018885
theorem B2230615 : Blo 2229435 2230615 := bstep (se 1 (by rfl) ⟨1672961, by rfl⟩ : syracuseStep 2230615 = 3345923) B3345923
theorem B4234693 : Blo 2229435 4234693 := bbase (se 4 (by rfl) ⟨397002, by rfl⟩ : syracuseStep 4234693 = 794005) (by norm_num)
theorem B5646257 : Blo 2229435 5646257 := bstep (se 2 (by rfl) ⟨2117346, by rfl⟩ : syracuseStep 5646257 = 4234693) B4234693
theorem B3764171 : Blo 2229435 3764171 := bstep (se 1 (by rfl) ⟨2823128, by rfl⟩ : syracuseStep 3764171 = 5646257) B5646257
theorem B2509447 : Blo 2229435 2509447 := bstep (se 1 (by rfl) ⟨1882085, by rfl⟩ : syracuseStep 2509447 = 3764171) B3764171
theorem B3345929 : Blo 2229435 3345929 := bstep (se 2 (by rfl) ⟨1254723, by rfl⟩ : syracuseStep 3345929 = 2509447) B2509447
theorem B2230619 : Blo 2229435 2230619 := bstep (se 1 (by rfl) ⟨1672964, by rfl⟩ : syracuseStep 2230619 = 3345929) B3345929
theorem B11292533 : Blo 2229435 11292533 := bbase (se 5 (by rfl) ⟨529337, by rfl⟩ : syracuseStep 11292533 = 1058675) (by norm_num)
theorem B7528355 : Blo 2229435 7528355 := bstep (se 1 (by rfl) ⟨5646266, by rfl⟩ : syracuseStep 7528355 = 11292533) B11292533
theorem B5018903 : Blo 2229435 5018903 := bstep (se 1 (by rfl) ⟨3764177, by rfl⟩ : syracuseStep 5018903 = 7528355) B7528355
theorem B3345935 : Blo 2229435 3345935 := bstep (se 1 (by rfl) ⟨2509451, by rfl⟩ : syracuseStep 3345935 = 5018903) B5018903
theorem B2230623 : Blo 2229435 2230623 := bstep (se 1 (by rfl) ⟨1672967, by rfl⟩ : syracuseStep 2230623 = 3345935) B3345935
theorem B3345941 : Blo 2229435 3345941 := bbase (se 6 (by rfl) ⟨78420, by rfl⟩ : syracuseStep 3345941 = 156841) (by norm_num)
theorem B2230627 : Blo 2229435 2230627 := bstep (se 1 (by rfl) ⟨1672970, by rfl⟩ : syracuseStep 2230627 = 3345941) B3345941
theorem B10719125 : Blo 2229435 10719125 := bbase (se 6 (by rfl) ⟨251229, by rfl⟩ : syracuseStep 10719125 = 502459) (by norm_num)
theorem B7146083 : Blo 2229435 7146083 := bstep (se 1 (by rfl) ⟨5359562, by rfl⟩ : syracuseStep 7146083 = 10719125) B10719125
theorem B19056221 : Blo 2229435 19056221 := bstep (se 3 (by rfl) ⟨3573041, by rfl⟩ : syracuseStep 19056221 = 7146083) B7146083
theorem B12704147 : Blo 2229435 12704147 := bstep (se 1 (by rfl) ⟨9528110, by rfl⟩ : syracuseStep 12704147 = 19056221) B19056221
theorem B8469431 : Blo 2229435 8469431 := bstep (se 1 (by rfl) ⟨6352073, by rfl⟩ : syracuseStep 8469431 = 12704147) B12704147
theorem B5646287 : Blo 2229435 5646287 := bstep (se 1 (by rfl) ⟨4234715, by rfl⟩ : syracuseStep 5646287 = 8469431) B8469431
theorem B3764191 : Blo 2229435 3764191 := bstep (se 1 (by rfl) ⟨2823143, by rfl⟩ : syracuseStep 3764191 = 5646287) B5646287
theorem B5018921 : Blo 2229435 5018921 := bstep (se 2 (by rfl) ⟨1882095, by rfl⟩ : syracuseStep 5018921 = 3764191) B3764191
theorem B3345947 : Blo 2229435 3345947 := bstep (se 1 (by rfl) ⟨2509460, by rfl⟩ : syracuseStep 3345947 = 5018921) B5018921
theorem B2230631 : Blo 2229435 2230631 := bstep (se 1 (by rfl) ⟨1672973, by rfl⟩ : syracuseStep 2230631 = 3345947) B3345947
theorem B2509465 : Blo 2229435 2509465 := bbase (se 2 (by rfl) ⟨941049, by rfl⟩ : syracuseStep 2509465 = 1882099) (by norm_num)
theorem B3345953 : Blo 2229435 3345953 := bstep (se 2 (by rfl) ⟨1254732, by rfl⟩ : syracuseStep 3345953 = 2509465) B2509465
theorem B2230635 : Blo 2229435 2230635 := bstep (se 1 (by rfl) ⟨1672976, by rfl⟩ : syracuseStep 2230635 = 3345953) B3345953
theorem B8469461 : Blo 2229435 8469461 := bbase (se 7 (by rfl) ⟨99251, by rfl⟩ : syracuseStep 8469461 = 198503) (by norm_num)
theorem B5646307 : Blo 2229435 5646307 := bstep (se 1 (by rfl) ⟨4234730, by rfl⟩ : syracuseStep 5646307 = 8469461) B8469461
theorem B7528409 : Blo 2229435 7528409 := bstep (se 2 (by rfl) ⟨2823153, by rfl⟩ : syracuseStep 7528409 = 5646307) B5646307
theorem B5018939 : Blo 2229435 5018939 := bstep (se 1 (by rfl) ⟨3764204, by rfl⟩ : syracuseStep 5018939 = 7528409) B7528409
theorem B3345959 : Blo 2229435 3345959 := bstep (se 1 (by rfl) ⟨2509469, by rfl⟩ : syracuseStep 3345959 = 5018939) B5018939
theorem B2230639 : Blo 2229435 2230639 := bstep (se 1 (by rfl) ⟨1672979, by rfl⟩ : syracuseStep 2230639 = 3345959) B3345959
theorem B3345965 : Blo 2229435 3345965 := bbase (se 3 (by rfl) ⟨627368, by rfl⟩ : syracuseStep 3345965 = 1254737) (by norm_num)
theorem B2230643 : Blo 2229435 2230643 := bstep (se 1 (by rfl) ⟨1672982, by rfl⟩ : syracuseStep 2230643 = 3345965) B3345965
theorem B5018957 : Blo 2229435 5018957 := bbase (se 3 (by rfl) ⟨941054, by rfl⟩ : syracuseStep 5018957 = 1882109) (by norm_num)
theorem B3345971 : Blo 2229435 3345971 := bstep (se 1 (by rfl) ⟨2509478, by rfl⟩ : syracuseStep 3345971 = 5018957) B5018957
theorem B2230647 : Blo 2229435 2230647 := bstep (se 1 (by rfl) ⟨1672985, by rfl⟩ : syracuseStep 2230647 = 3345971) B3345971
theorem B2823169 : Blo 2229435 2823169 := bbase (se 2 (by rfl) ⟨1058688, by rfl⟩ : syracuseStep 2823169 = 2117377) (by norm_num)
theorem B3764225 : Blo 2229435 3764225 := bstep (se 2 (by rfl) ⟨1411584, by rfl⟩ : syracuseStep 3764225 = 2823169) B2823169
theorem B2509483 : Blo 2229435 2509483 := bstep (se 1 (by rfl) ⟨1882112, by rfl⟩ : syracuseStep 2509483 = 3764225) B3764225
theorem B3345977 : Blo 2229435 3345977 := bstep (se 2 (by rfl) ⟨1254741, by rfl⟩ : syracuseStep 3345977 = 2509483) B2509483
theorem B2230651 : Blo 2229435 2230651 := bstep (se 1 (by rfl) ⟨1672988, by rfl⟩ : syracuseStep 2230651 = 3345977) B3345977
theorem B2382053 : Blo 2229435 2382053 := bbase (se 4 (by rfl) ⟨223317, by rfl⟩ : syracuseStep 2382053 = 446635) (by norm_num)
theorem B25408565 : Blo 2229435 25408565 := bstep (se 5 (by rfl) ⟨1191026, by rfl⟩ : syracuseStep 25408565 = 2382053) B2382053
theorem B16939043 : Blo 2229435 16939043 := bstep (se 1 (by rfl) ⟨12704282, by rfl⟩ : syracuseStep 16939043 = 25408565) B25408565
theorem B11292695 : Blo 2229435 11292695 := bstep (se 1 (by rfl) ⟨8469521, by rfl⟩ : syracuseStep 11292695 = 16939043) B16939043
theorem B7528463 : Blo 2229435 7528463 := bstep (se 1 (by rfl) ⟨5646347, by rfl⟩ : syracuseStep 7528463 = 11292695) B11292695
theorem B5018975 : Blo 2229435 5018975 := bstep (se 1 (by rfl) ⟨3764231, by rfl⟩ : syracuseStep 5018975 = 7528463) B7528463
theorem B3345983 : Blo 2229435 3345983 := bstep (se 1 (by rfl) ⟨2509487, by rfl⟩ : syracuseStep 3345983 = 5018975) B5018975
theorem B2230655 : Blo 2229435 2230655 := bstep (se 1 (by rfl) ⟨1672991, by rfl⟩ : syracuseStep 2230655 = 3345983) B3345983
theorem B3345989 : Blo 2229435 3345989 := bbase (se 4 (by rfl) ⟨313686, by rfl⟩ : syracuseStep 3345989 = 627373) (by norm_num)
theorem B2230659 : Blo 2229435 2230659 := bstep (se 1 (by rfl) ⟨1672994, by rfl⟩ : syracuseStep 2230659 = 3345989) B3345989
theorem B3764245 : Blo 2229435 3764245 := bbase (se 6 (by rfl) ⟨88224, by rfl⟩ : syracuseStep 3764245 = 176449) (by norm_num)
theorem B5018993 : Blo 2229435 5018993 := bstep (se 2 (by rfl) ⟨1882122, by rfl⟩ : syracuseStep 5018993 = 3764245) B3764245
theorem B3345995 : Blo 2229435 3345995 := bstep (se 1 (by rfl) ⟨2509496, by rfl⟩ : syracuseStep 3345995 = 5018993) B5018993
theorem B2230663 : Blo 2229435 2230663 := bstep (se 1 (by rfl) ⟨1672997, by rfl⟩ : syracuseStep 2230663 = 3345995) B3345995
theorem B2509501 : Blo 2229435 2509501 := bbase (se 3 (by rfl) ⟨470531, by rfl⟩ : syracuseStep 2509501 = 941063) (by norm_num)
theorem B3346001 : Blo 2229435 3346001 := bstep (se 2 (by rfl) ⟨1254750, by rfl⟩ : syracuseStep 3346001 = 2509501) B2509501
theorem B2230667 : Blo 2229435 2230667 := bstep (se 1 (by rfl) ⟨1673000, by rfl⟩ : syracuseStep 2230667 = 3346001) B3346001
theorem B7528517 : Blo 2229435 7528517 := bbase (se 4 (by rfl) ⟨705798, by rfl⟩ : syracuseStep 7528517 = 1411597) (by norm_num)
theorem B5019011 : Blo 2229435 5019011 := bstep (se 1 (by rfl) ⟨3764258, by rfl⟩ : syracuseStep 5019011 = 7528517) B7528517
theorem B3346007 : Blo 2229435 3346007 := bstep (se 1 (by rfl) ⟨2509505, by rfl⟩ : syracuseStep 3346007 = 5019011) B5019011
theorem B2230671 : Blo 2229435 2230671 := bstep (se 1 (by rfl) ⟨1673003, by rfl⟩ : syracuseStep 2230671 = 3346007) B3346007
theorem B3346013 : Blo 2229435 3346013 := bbase (se 3 (by rfl) ⟨627377, by rfl⟩ : syracuseStep 3346013 = 1254755) (by norm_num)
theorem B2230675 : Blo 2229435 2230675 := bstep (se 1 (by rfl) ⟨1673006, by rfl⟩ : syracuseStep 2230675 = 3346013) B3346013
theorem B5019029 : Blo 2229435 5019029 := bbase (se 6 (by rfl) ⟨117633, by rfl⟩ : syracuseStep 5019029 = 235267) (by norm_num)
theorem B3346019 : Blo 2229435 3346019 := bstep (se 1 (by rfl) ⟨2509514, by rfl⟩ : syracuseStep 3346019 = 5019029) B5019029
theorem B2230679 : Blo 2229435 2230679 := bstep (se 1 (by rfl) ⟨1673009, by rfl⟩ : syracuseStep 2230679 = 3346019) B3346019
theorem B3621877 : Blo 2229435 3621877 := bbase (se 5 (by rfl) ⟨169775, by rfl⟩ : syracuseStep 3621877 = 339551) (by norm_num)
theorem B19316677 : Blo 2229435 19316677 := bstep (se 4 (by rfl) ⟨1810938, by rfl⟩ : syracuseStep 19316677 = 3621877) B3621877
theorem B25755569 : Blo 2229435 25755569 := bstep (se 2 (by rfl) ⟨9658338, by rfl⟩ : syracuseStep 25755569 = 19316677) B19316677
theorem B17170379 : Blo 2229435 17170379 := bstep (se 1 (by rfl) ⟨12877784, by rfl⟩ : syracuseStep 17170379 = 25755569) B25755569
theorem B11446919 : Blo 2229435 11446919 := bstep (se 1 (by rfl) ⟨8585189, by rfl⟩ : syracuseStep 11446919 = 17170379) B17170379
theorem B7631279 : Blo 2229435 7631279 := bstep (se 1 (by rfl) ⟨5723459, by rfl⟩ : syracuseStep 7631279 = 11446919) B11446919
theorem B5087519 : Blo 2229435 5087519 := bstep (se 1 (by rfl) ⟨3815639, by rfl⟩ : syracuseStep 5087519 = 7631279) B7631279
theorem B3391679 : Blo 2229435 3391679 := bstep (se 1 (by rfl) ⟨2543759, by rfl⟩ : syracuseStep 3391679 = 5087519) B5087519
theorem B2261119 : Blo 2229435 2261119 := bstep (se 1 (by rfl) ⟨1695839, by rfl⟩ : syracuseStep 2261119 = 3391679) B3391679
theorem B3014825 : Blo 2229435 3014825 := bstep (se 2 (by rfl) ⟨1130559, by rfl⟩ : syracuseStep 3014825 = 2261119) B2261119
theorem B8039533 : Blo 2229435 8039533 := bstep (se 3 (by rfl) ⟨1507412, by rfl⟩ : syracuseStep 8039533 = 3014825) B3014825
theorem B10719377 : Blo 2229435 10719377 := bstep (se 2 (by rfl) ⟨4019766, by rfl⟩ : syracuseStep 10719377 = 8039533) B8039533
theorem B7146251 : Blo 2229435 7146251 := bstep (se 1 (by rfl) ⟨5359688, by rfl⟩ : syracuseStep 7146251 = 10719377) B10719377
theorem B4764167 : Blo 2229435 4764167 := bstep (se 1 (by rfl) ⟨3573125, by rfl⟩ : syracuseStep 4764167 = 7146251) B7146251
theorem B3176111 : Blo 2229435 3176111 := bstep (se 1 (by rfl) ⟨2382083, by rfl⟩ : syracuseStep 3176111 = 4764167) B4764167
theorem B8469629 : Blo 2229435 8469629 := bstep (se 3 (by rfl) ⟨1588055, by rfl⟩ : syracuseStep 8469629 = 3176111) B3176111
theorem B5646419 : Blo 2229435 5646419 := bstep (se 1 (by rfl) ⟨4234814, by rfl⟩ : syracuseStep 5646419 = 8469629) B8469629
theorem B3764279 : Blo 2229435 3764279 := bstep (se 1 (by rfl) ⟨2823209, by rfl⟩ : syracuseStep 3764279 = 5646419) B5646419
theorem B2509519 : Blo 2229435 2509519 := bstep (se 1 (by rfl) ⟨1882139, by rfl⟩ : syracuseStep 2509519 = 3764279) B3764279
theorem B3346025 : Blo 2229435 3346025 := bstep (se 2 (by rfl) ⟨1254759, by rfl⟩ : syracuseStep 3346025 = 2509519) B2509519
theorem B2230683 : Blo 2229435 2230683 := bstep (se 1 (by rfl) ⟨1673012, by rfl⟩ : syracuseStep 2230683 = 3346025) B3346025
theorem B4019773 : Blo 2229435 4019773 := bbase (se 3 (by rfl) ⟨753707, by rfl⟩ : syracuseStep 4019773 = 1507415) (by norm_num)
theorem B5359697 : Blo 2229435 5359697 := bstep (se 2 (by rfl) ⟨2009886, by rfl⟩ : syracuseStep 5359697 = 4019773) B4019773
theorem B3573131 : Blo 2229435 3573131 := bstep (se 1 (by rfl) ⟨2679848, by rfl⟩ : syracuseStep 3573131 = 5359697) B5359697
theorem B9528349 : Blo 2229435 9528349 := bstep (se 3 (by rfl) ⟨1786565, by rfl⟩ : syracuseStep 9528349 = 3573131) B3573131
theorem B12704465 : Blo 2229435 12704465 := bstep (se 2 (by rfl) ⟨4764174, by rfl⟩ : syracuseStep 12704465 = 9528349) B9528349
theorem B8469643 : Blo 2229435 8469643 := bstep (se 1 (by rfl) ⟨6352232, by rfl⟩ : syracuseStep 8469643 = 12704465) B12704465
theorem B11292857 : Blo 2229435 11292857 := bstep (se 2 (by rfl) ⟨4234821, by rfl⟩ : syracuseStep 11292857 = 8469643) B8469643
theorem B7528571 : Blo 2229435 7528571 := bstep (se 1 (by rfl) ⟨5646428, by rfl⟩ : syracuseStep 7528571 = 11292857) B11292857
theorem B5019047 : Blo 2229435 5019047 := bstep (se 1 (by rfl) ⟨3764285, by rfl⟩ : syracuseStep 5019047 = 7528571) B7528571
theorem B3346031 : Blo 2229435 3346031 := bstep (se 1 (by rfl) ⟨2509523, by rfl⟩ : syracuseStep 3346031 = 5019047) B5019047
theorem B2230687 : Blo 2229435 2230687 := bstep (se 1 (by rfl) ⟨1673015, by rfl⟩ : syracuseStep 2230687 = 3346031) B3346031
theorem B3346037 : Blo 2229435 3346037 := bbase (se 5 (by rfl) ⟨156845, by rfl⟩ : syracuseStep 3346037 = 313691) (by norm_num)
theorem B2230691 : Blo 2229435 2230691 := bstep (se 1 (by rfl) ⟨1673018, by rfl⟩ : syracuseStep 2230691 = 3346037) B3346037
theorem B4234837 : Blo 2229435 4234837 := bbase (se 8 (by rfl) ⟨24813, by rfl⟩ : syracuseStep 4234837 = 49627) (by norm_num)
theorem B5646449 : Blo 2229435 5646449 := bstep (se 2 (by rfl) ⟨2117418, by rfl⟩ : syracuseStep 5646449 = 4234837) B4234837
theorem B3764299 : Blo 2229435 3764299 := bstep (se 1 (by rfl) ⟨2823224, by rfl⟩ : syracuseStep 3764299 = 5646449) B5646449
theorem B5019065 : Blo 2229435 5019065 := bstep (se 2 (by rfl) ⟨1882149, by rfl⟩ : syracuseStep 5019065 = 3764299) B3764299
theorem B3346043 : Blo 2229435 3346043 := bstep (se 1 (by rfl) ⟨2509532, by rfl⟩ : syracuseStep 3346043 = 5019065) B5019065
theorem B2230695 : Blo 2229435 2230695 := bstep (se 1 (by rfl) ⟨1673021, by rfl⟩ : syracuseStep 2230695 = 3346043) B3346043
theorem B2509537 : Blo 2229435 2509537 := bbase (se 2 (by rfl) ⟨941076, by rfl⟩ : syracuseStep 2509537 = 1882153) (by norm_num)
theorem B3346049 : Blo 2229435 3346049 := bstep (se 2 (by rfl) ⟨1254768, by rfl⟩ : syracuseStep 3346049 = 2509537) B2509537
theorem B2230699 : Blo 2229435 2230699 := bstep (se 1 (by rfl) ⟨1673024, by rfl⟩ : syracuseStep 2230699 = 3346049) B3346049
theorem B5646469 : Blo 2229435 5646469 := bbase (se 4 (by rfl) ⟨529356, by rfl⟩ : syracuseStep 5646469 = 1058713) (by norm_num)
theorem B7528625 : Blo 2229435 7528625 := bstep (se 2 (by rfl) ⟨2823234, by rfl⟩ : syracuseStep 7528625 = 5646469) B5646469
theorem B5019083 : Blo 2229435 5019083 := bstep (se 1 (by rfl) ⟨3764312, by rfl⟩ : syracuseStep 5019083 = 7528625) B7528625
theorem B3346055 : Blo 2229435 3346055 := bstep (se 1 (by rfl) ⟨2509541, by rfl⟩ : syracuseStep 3346055 = 5019083) B5019083
theorem B2230703 : Blo 2229435 2230703 := bstep (se 1 (by rfl) ⟨1673027, by rfl⟩ : syracuseStep 2230703 = 3346055) B3346055
theorem B3346061 : Blo 2229435 3346061 := bbase (se 3 (by rfl) ⟨627386, by rfl⟩ : syracuseStep 3346061 = 1254773) (by norm_num)
theorem B2230707 : Blo 2229435 2230707 := bstep (se 1 (by rfl) ⟨1673030, by rfl⟩ : syracuseStep 2230707 = 3346061) B3346061
theorem B5019101 : Blo 2229435 5019101 := bbase (se 3 (by rfl) ⟨941081, by rfl⟩ : syracuseStep 5019101 = 1882163) (by norm_num)
theorem B3346067 : Blo 2229435 3346067 := bstep (se 1 (by rfl) ⟨2509550, by rfl⟩ : syracuseStep 3346067 = 5019101) B5019101
theorem B2230711 : Blo 2229435 2230711 := bstep (se 1 (by rfl) ⟨1673033, by rfl⟩ : syracuseStep 2230711 = 3346067) B3346067
theorem B3764333 : Blo 2229435 3764333 := bbase (se 3 (by rfl) ⟨705812, by rfl⟩ : syracuseStep 3764333 = 1411625) (by norm_num)
theorem B2509555 : Blo 2229435 2509555 := bstep (se 1 (by rfl) ⟨1882166, by rfl⟩ : syracuseStep 2509555 = 3764333) B3764333
theorem B3346073 : Blo 2229435 3346073 := bstep (se 2 (by rfl) ⟨1254777, by rfl⟩ : syracuseStep 3346073 = 2509555) B2509555
theorem B2230715 : Blo 2229435 2230715 := bstep (se 1 (by rfl) ⟨1673036, by rfl⟩ : syracuseStep 2230715 = 3346073) B3346073
theorem B21439093 : Blo 2229435 21439093 := bbase (se 5 (by rfl) ⟨1004957, by rfl⟩ : syracuseStep 21439093 = 2009915) (by norm_num)
theorem B28585457 : Blo 2229435 28585457 := bstep (se 2 (by rfl) ⟨10719546, by rfl⟩ : syracuseStep 28585457 = 21439093) B21439093
theorem B19056971 : Blo 2229435 19056971 := bstep (se 1 (by rfl) ⟨14292728, by rfl⟩ : syracuseStep 19056971 = 28585457) B28585457
theorem B12704647 : Blo 2229435 12704647 := bstep (se 1 (by rfl) ⟨9528485, by rfl⟩ : syracuseStep 12704647 = 19056971) B19056971
theorem B16939529 : Blo 2229435 16939529 := bstep (se 2 (by rfl) ⟨6352323, by rfl⟩ : syracuseStep 16939529 = 12704647) B12704647
theorem B11293019 : Blo 2229435 11293019 := bstep (se 1 (by rfl) ⟨8469764, by rfl⟩ : syracuseStep 11293019 = 16939529) B16939529
theorem B7528679 : Blo 2229435 7528679 := bstep (se 1 (by rfl) ⟨5646509, by rfl⟩ : syracuseStep 7528679 = 11293019) B11293019
theorem B5019119 : Blo 2229435 5019119 := bstep (se 1 (by rfl) ⟨3764339, by rfl⟩ : syracuseStep 5019119 = 7528679) B7528679
theorem B3346079 : Blo 2229435 3346079 := bstep (se 1 (by rfl) ⟨2509559, by rfl⟩ : syracuseStep 3346079 = 5019119) B5019119
theorem B2230719 : Blo 2229435 2230719 := bstep (se 1 (by rfl) ⟨1673039, by rfl⟩ : syracuseStep 2230719 = 3346079) B3346079
theorem B3346085 : Blo 2229435 3346085 := bbase (se 4 (by rfl) ⟨313695, by rfl⟩ : syracuseStep 3346085 = 627391) (by norm_num)
theorem B2230723 : Blo 2229435 2230723 := bstep (se 1 (by rfl) ⟨1673042, by rfl⟩ : syracuseStep 2230723 = 3346085) B3346085
theorem B2823265 : Blo 2229435 2823265 := bbase (se 2 (by rfl) ⟨1058724, by rfl⟩ : syracuseStep 2823265 = 2117449) (by norm_num)
theorem B3764353 : Blo 2229435 3764353 := bstep (se 2 (by rfl) ⟨1411632, by rfl⟩ : syracuseStep 3764353 = 2823265) B2823265
theorem B5019137 : Blo 2229435 5019137 := bstep (se 2 (by rfl) ⟨1882176, by rfl⟩ : syracuseStep 5019137 = 3764353) B3764353
theorem B3346091 : Blo 2229435 3346091 := bstep (se 1 (by rfl) ⟨2509568, by rfl⟩ : syracuseStep 3346091 = 5019137) B5019137
theorem B2230727 : Blo 2229435 2230727 := bstep (se 1 (by rfl) ⟨1673045, by rfl⟩ : syracuseStep 2230727 = 3346091) B3346091
theorem B2509573 : Blo 2229435 2509573 := bbase (se 4 (by rfl) ⟨235272, by rfl⟩ : syracuseStep 2509573 = 470545) (by norm_num)
theorem B3346097 : Blo 2229435 3346097 := bstep (se 2 (by rfl) ⟨1254786, by rfl⟩ : syracuseStep 3346097 = 2509573) B2509573
theorem B2230731 : Blo 2229435 2230731 := bstep (se 1 (by rfl) ⟨1673048, by rfl⟩ : syracuseStep 2230731 = 3346097) B3346097
theorem B4019861 : Blo 2229435 4019861 := bbase (se 6 (by rfl) ⟨94215, by rfl⟩ : syracuseStep 4019861 = 188431) (by norm_num)
theorem B2679907 : Blo 2229435 2679907 := bstep (se 1 (by rfl) ⟨2009930, by rfl⟩ : syracuseStep 2679907 = 4019861) B4019861
theorem B3573209 : Blo 2229435 3573209 := bstep (se 2 (by rfl) ⟨1339953, by rfl⟩ : syracuseStep 3573209 = 2679907) B2679907
theorem B2382139 : Blo 2229435 2382139 := bstep (se 1 (by rfl) ⟨1786604, by rfl⟩ : syracuseStep 2382139 = 3573209) B3573209
theorem B3176185 : Blo 2229435 3176185 := bstep (se 2 (by rfl) ⟨1191069, by rfl⟩ : syracuseStep 3176185 = 2382139) B2382139
theorem B4234913 : Blo 2229435 4234913 := bstep (se 2 (by rfl) ⟨1588092, by rfl⟩ : syracuseStep 4234913 = 3176185) B3176185
theorem B2823275 : Blo 2229435 2823275 := bstep (se 1 (by rfl) ⟨2117456, by rfl⟩ : syracuseStep 2823275 = 4234913) B4234913
theorem B7528733 : Blo 2229435 7528733 := bstep (se 3 (by rfl) ⟨1411637, by rfl⟩ : syracuseStep 7528733 = 2823275) B2823275
theorem B5019155 : Blo 2229435 5019155 := bstep (se 1 (by rfl) ⟨3764366, by rfl⟩ : syracuseStep 5019155 = 7528733) B7528733
theorem B3346103 : Blo 2229435 3346103 := bstep (se 1 (by rfl) ⟨2509577, by rfl⟩ : syracuseStep 3346103 = 5019155) B5019155
theorem B2230735 : Blo 2229435 2230735 := bstep (se 1 (by rfl) ⟨1673051, by rfl⟩ : syracuseStep 2230735 = 3346103) B3346103
theorem B3346109 : Blo 2229435 3346109 := bbase (se 3 (by rfl) ⟨627395, by rfl⟩ : syracuseStep 3346109 = 1254791) (by norm_num)
theorem B2230739 : Blo 2229435 2230739 := bstep (se 1 (by rfl) ⟨1673054, by rfl⟩ : syracuseStep 2230739 = 3346109) B3346109
theorem B5019173 : Blo 2229435 5019173 := bbase (se 4 (by rfl) ⟨470547, by rfl⟩ : syracuseStep 5019173 = 941095) (by norm_num)
theorem B3346115 : Blo 2229435 3346115 := bstep (se 1 (by rfl) ⟨2509586, by rfl⟩ : syracuseStep 3346115 = 5019173) B5019173
theorem B2230743 : Blo 2229435 2230743 := bstep (se 1 (by rfl) ⟨1673057, by rfl⟩ : syracuseStep 2230743 = 3346115) B3346115
theorem B5646581 : Blo 2229435 5646581 := bbase (se 5 (by rfl) ⟨264683, by rfl⟩ : syracuseStep 5646581 = 529367) (by norm_num)
theorem B3764387 : Blo 2229435 3764387 := bstep (se 1 (by rfl) ⟨2823290, by rfl⟩ : syracuseStep 3764387 = 5646581) B5646581
theorem B2509591 : Blo 2229435 2509591 := bstep (se 1 (by rfl) ⟨1882193, by rfl⟩ : syracuseStep 2509591 = 3764387) B3764387
theorem B3346121 : Blo 2229435 3346121 := bstep (se 2 (by rfl) ⟨1254795, by rfl⟩ : syracuseStep 3346121 = 2509591) B2509591
theorem B2230747 : Blo 2229435 2230747 := bstep (se 1 (by rfl) ⟨1673060, by rfl⟩ : syracuseStep 2230747 = 3346121) B3346121
theorem B2414657 : Blo 2229435 2414657 := bbase (se 2 (by rfl) ⟨905496, by rfl⟩ : syracuseStep 2414657 = 1810993) (by norm_num)
theorem B6439085 : Blo 2229435 6439085 := bstep (se 3 (by rfl) ⟨1207328, by rfl⟩ : syracuseStep 6439085 = 2414657) B2414657
theorem B4292723 : Blo 2229435 4292723 := bstep (se 1 (by rfl) ⟨3219542, by rfl⟩ : syracuseStep 4292723 = 6439085) B6439085
theorem B11447261 : Blo 2229435 11447261 := bstep (se 3 (by rfl) ⟨2146361, by rfl⟩ : syracuseStep 11447261 = 4292723) B4292723
theorem B7631507 : Blo 2229435 7631507 := bstep (se 1 (by rfl) ⟨5723630, by rfl⟩ : syracuseStep 7631507 = 11447261) B11447261
theorem B20350685 : Blo 2229435 20350685 := bstep (se 3 (by rfl) ⟨3815753, by rfl⟩ : syracuseStep 20350685 = 7631507) B7631507
theorem B13567123 : Blo 2229435 13567123 := bstep (se 1 (by rfl) ⟨10175342, by rfl⟩ : syracuseStep 13567123 = 20350685) B20350685
theorem B18089497 : Blo 2229435 18089497 := bstep (se 2 (by rfl) ⟨6783561, by rfl⟩ : syracuseStep 18089497 = 13567123) B13567123
theorem B24119329 : Blo 2229435 24119329 := bstep (se 2 (by rfl) ⟨9044748, by rfl⟩ : syracuseStep 24119329 = 18089497) B18089497
theorem B32159105 : Blo 2229435 32159105 := bstep (se 2 (by rfl) ⟨12059664, by rfl⟩ : syracuseStep 32159105 = 24119329) B24119329
theorem B21439403 : Blo 2229435 21439403 := bstep (se 1 (by rfl) ⟨16079552, by rfl⟩ : syracuseStep 21439403 = 32159105) B32159105
theorem B14292935 : Blo 2229435 14292935 := bstep (se 1 (by rfl) ⟨10719701, by rfl⟩ : syracuseStep 14292935 = 21439403) B21439403
theorem B9528623 : Blo 2229435 9528623 := bstep (se 1 (by rfl) ⟨7146467, by rfl⟩ : syracuseStep 9528623 = 14292935) B14292935
theorem B6352415 : Blo 2229435 6352415 := bstep (se 1 (by rfl) ⟨4764311, by rfl⟩ : syracuseStep 6352415 = 9528623) B9528623
theorem B4234943 : Blo 2229435 4234943 := bstep (se 1 (by rfl) ⟨3176207, by rfl⟩ : syracuseStep 4234943 = 6352415) B6352415
theorem B11293181 : Blo 2229435 11293181 := bstep (se 3 (by rfl) ⟨2117471, by rfl⟩ : syracuseStep 11293181 = 4234943) B4234943
theorem B7528787 : Blo 2229435 7528787 := bstep (se 1 (by rfl) ⟨5646590, by rfl⟩ : syracuseStep 7528787 = 11293181) B11293181
theorem B5019191 : Blo 2229435 5019191 := bstep (se 1 (by rfl) ⟨3764393, by rfl⟩ : syracuseStep 5019191 = 7528787) B7528787
theorem B3346127 : Blo 2229435 3346127 := bstep (se 1 (by rfl) ⟨2509595, by rfl⟩ : syracuseStep 3346127 = 5019191) B5019191
theorem B2230751 : Blo 2229435 2230751 := bstep (se 1 (by rfl) ⟨1673063, by rfl⟩ : syracuseStep 2230751 = 3346127) B3346127
theorem B3346133 : Blo 2229435 3346133 := bbase (se 7 (by rfl) ⟨39212, by rfl⟩ : syracuseStep 3346133 = 78425) (by norm_num)
theorem B2230755 : Blo 2229435 2230755 := bstep (se 1 (by rfl) ⟨1673066, by rfl⟩ : syracuseStep 2230755 = 3346133) B3346133
theorem B6439109 : Blo 2229435 6439109 := bbase (se 4 (by rfl) ⟨603666, by rfl⟩ : syracuseStep 6439109 = 1207333) (by norm_num)
theorem B17170957 : Blo 2229435 17170957 := bstep (se 3 (by rfl) ⟨3219554, by rfl⟩ : syracuseStep 17170957 = 6439109) B6439109
theorem B91578437 : Blo 2229435 91578437 := bstep (se 4 (by rfl) ⟨8585478, by rfl⟩ : syracuseStep 91578437 = 17170957) B17170957
theorem B61052291 : Blo 2229435 61052291 := bstep (se 1 (by rfl) ⟨45789218, by rfl⟩ : syracuseStep 61052291 = 91578437) B91578437
theorem B40701527 : Blo 2229435 40701527 := bstep (se 1 (by rfl) ⟨30526145, by rfl⟩ : syracuseStep 40701527 = 61052291) B61052291
theorem B27134351 : Blo 2229435 27134351 := bstep (se 1 (by rfl) ⟨20350763, by rfl⟩ : syracuseStep 27134351 = 40701527) B40701527
theorem B18089567 : Blo 2229435 18089567 := bstep (se 1 (by rfl) ⟨13567175, by rfl⟩ : syracuseStep 18089567 = 27134351) B27134351
theorem B12059711 : Blo 2229435 12059711 := bstep (se 1 (by rfl) ⟨9044783, by rfl⟩ : syracuseStep 12059711 = 18089567) B18089567
theorem B8039807 : Blo 2229435 8039807 := bstep (se 1 (by rfl) ⟨6029855, by rfl⟩ : syracuseStep 8039807 = 12059711) B12059711
theorem B5359871 : Blo 2229435 5359871 := bstep (se 1 (by rfl) ⟨4019903, by rfl⟩ : syracuseStep 5359871 = 8039807) B8039807
theorem B3573247 : Blo 2229435 3573247 := bstep (se 1 (by rfl) ⟨2679935, by rfl⟩ : syracuseStep 3573247 = 5359871) B5359871
theorem B4764329 : Blo 2229435 4764329 := bstep (se 2 (by rfl) ⟨1786623, by rfl⟩ : syracuseStep 4764329 = 3573247) B3573247
theorem B3176219 : Blo 2229435 3176219 := bstep (se 1 (by rfl) ⟨2382164, by rfl⟩ : syracuseStep 3176219 = 4764329) B4764329
theorem B8469917 : Blo 2229435 8469917 := bstep (se 3 (by rfl) ⟨1588109, by rfl⟩ : syracuseStep 8469917 = 3176219) B3176219
theorem B5646611 : Blo 2229435 5646611 := bstep (se 1 (by rfl) ⟨4234958, by rfl⟩ : syracuseStep 5646611 = 8469917) B8469917
theorem B3764407 : Blo 2229435 3764407 := bstep (se 1 (by rfl) ⟨2823305, by rfl⟩ : syracuseStep 3764407 = 5646611) B5646611
theorem B5019209 : Blo 2229435 5019209 := bstep (se 2 (by rfl) ⟨1882203, by rfl⟩ : syracuseStep 5019209 = 3764407) B3764407
theorem B3346139 : Blo 2229435 3346139 := bstep (se 1 (by rfl) ⟨2509604, by rfl⟩ : syracuseStep 3346139 = 5019209) B5019209
theorem B2230759 : Blo 2229435 2230759 := bstep (se 1 (by rfl) ⟨1673069, by rfl⟩ : syracuseStep 2230759 = 3346139) B3346139
theorem B2509609 : Blo 2229435 2509609 := bbase (se 2 (by rfl) ⟨941103, by rfl⟩ : syracuseStep 2509609 = 1882207) (by norm_num)
theorem B3346145 : Blo 2229435 3346145 := bstep (se 2 (by rfl) ⟨1254804, by rfl⟩ : syracuseStep 3346145 = 2509609) B2509609
theorem B2230763 : Blo 2229435 2230763 := bstep (se 1 (by rfl) ⟨1673072, by rfl⟩ : syracuseStep 2230763 = 3346145) B3346145
theorem B4019917 : Blo 2229435 4019917 := bbase (se 3 (by rfl) ⟨753734, by rfl⟩ : syracuseStep 4019917 = 1507469) (by norm_num)
theorem B5359889 : Blo 2229435 5359889 := bstep (se 2 (by rfl) ⟨2009958, by rfl⟩ : syracuseStep 5359889 = 4019917) B4019917
theorem B14293037 : Blo 2229435 14293037 := bstep (se 3 (by rfl) ⟨2679944, by rfl⟩ : syracuseStep 14293037 = 5359889) B5359889
theorem B9528691 : Blo 2229435 9528691 := bstep (se 1 (by rfl) ⟨7146518, by rfl⟩ : syracuseStep 9528691 = 14293037) B14293037
theorem B12704921 : Blo 2229435 12704921 := bstep (se 2 (by rfl) ⟨4764345, by rfl⟩ : syracuseStep 12704921 = 9528691) B9528691
theorem B8469947 : Blo 2229435 8469947 := bstep (se 1 (by rfl) ⟨6352460, by rfl⟩ : syracuseStep 8469947 = 12704921) B12704921
theorem B5646631 : Blo 2229435 5646631 := bstep (se 1 (by rfl) ⟨4234973, by rfl⟩ : syracuseStep 5646631 = 8469947) B8469947
theorem B7528841 : Blo 2229435 7528841 := bstep (se 2 (by rfl) ⟨2823315, by rfl⟩ : syracuseStep 7528841 = 5646631) B5646631
theorem B5019227 : Blo 2229435 5019227 := bstep (se 1 (by rfl) ⟨3764420, by rfl⟩ : syracuseStep 5019227 = 7528841) B7528841
theorem B3346151 : Blo 2229435 3346151 := bstep (se 1 (by rfl) ⟨2509613, by rfl⟩ : syracuseStep 3346151 = 5019227) B5019227
theorem B2230767 : Blo 2229435 2230767 := bstep (se 1 (by rfl) ⟨1673075, by rfl⟩ : syracuseStep 2230767 = 3346151) B3346151
theorem B3346157 : Blo 2229435 3346157 := bbase (se 3 (by rfl) ⟨627404, by rfl⟩ : syracuseStep 3346157 = 1254809) (by norm_num)
theorem B2230771 : Blo 2229435 2230771 := bstep (se 1 (by rfl) ⟨1673078, by rfl⟩ : syracuseStep 2230771 = 3346157) B3346157
theorem B5019245 : Blo 2229435 5019245 := bbase (se 3 (by rfl) ⟨941108, by rfl⟩ : syracuseStep 5019245 = 1882217) (by norm_num)
theorem B3346163 : Blo 2229435 3346163 := bstep (se 1 (by rfl) ⟨2509622, by rfl⟩ : syracuseStep 3346163 = 5019245) B5019245
theorem B2230775 : Blo 2229435 2230775 := bstep (se 1 (by rfl) ⟨1673081, by rfl⟩ : syracuseStep 2230775 = 3346163) B3346163
theorem B4234997 : Blo 2229435 4234997 := bbase (se 5 (by rfl) ⟨198515, by rfl⟩ : syracuseStep 4234997 = 397031) (by norm_num)
theorem B2823331 : Blo 2229435 2823331 := bstep (se 1 (by rfl) ⟨2117498, by rfl⟩ : syracuseStep 2823331 = 4234997) B4234997
theorem B3764441 : Blo 2229435 3764441 := bstep (se 2 (by rfl) ⟨1411665, by rfl⟩ : syracuseStep 3764441 = 2823331) B2823331
theorem B2509627 : Blo 2229435 2509627 := bstep (se 1 (by rfl) ⟨1882220, by rfl⟩ : syracuseStep 2509627 = 3764441) B3764441
theorem B3346169 : Blo 2229435 3346169 := bstep (se 2 (by rfl) ⟨1254813, by rfl⟩ : syracuseStep 3346169 = 2509627) B2509627
theorem B2230779 : Blo 2229435 2230779 := bstep (se 1 (by rfl) ⟨1673084, by rfl⟩ : syracuseStep 2230779 = 3346169) B3346169
theorem B9811013 : Blo 2229435 9811013 := bbase (se 4 (by rfl) ⟨919782, by rfl⟩ : syracuseStep 9811013 = 1839565) (by norm_num)
theorem B104650805 : Blo 2229435 104650805 := bstep (se 5 (by rfl) ⟨4905506, by rfl⟩ : syracuseStep 104650805 = 9811013) B9811013
theorem B69767203 : Blo 2229435 69767203 := bstep (se 1 (by rfl) ⟨52325402, by rfl⟩ : syracuseStep 69767203 = 104650805) B104650805
theorem B93022937 : Blo 2229435 93022937 := bstep (se 2 (by rfl) ⟨34883601, by rfl⟩ : syracuseStep 93022937 = 69767203) B69767203
theorem B62015291 : Blo 2229435 62015291 := bstep (se 1 (by rfl) ⟨46511468, by rfl⟩ : syracuseStep 62015291 = 93022937) B93022937
theorem B41343527 : Blo 2229435 41343527 := bstep (se 1 (by rfl) ⟨31007645, by rfl⟩ : syracuseStep 41343527 = 62015291) B62015291
theorem B27562351 : Blo 2229435 27562351 := bstep (se 1 (by rfl) ⟨20671763, by rfl⟩ : syracuseStep 27562351 = 41343527) B41343527
theorem B36749801 : Blo 2229435 36749801 := bstep (se 2 (by rfl) ⟨13781175, by rfl⟩ : syracuseStep 36749801 = 27562351) B27562351
theorem B24499867 : Blo 2229435 24499867 := bstep (se 1 (by rfl) ⟨18374900, by rfl⟩ : syracuseStep 24499867 = 36749801) B36749801
theorem B32666489 : Blo 2229435 32666489 := bstep (se 2 (by rfl) ⟨12249933, by rfl⟩ : syracuseStep 32666489 = 24499867) B24499867
theorem B21777659 : Blo 2229435 21777659 := bstep (se 1 (by rfl) ⟨16333244, by rfl⟩ : syracuseStep 21777659 = 32666489) B32666489
theorem B14518439 : Blo 2229435 14518439 := bstep (se 1 (by rfl) ⟨10888829, by rfl⟩ : syracuseStep 14518439 = 21777659) B21777659
theorem B9678959 : Blo 2229435 9678959 := bstep (se 1 (by rfl) ⟨7259219, by rfl⟩ : syracuseStep 9678959 = 14518439) B14518439
theorem B6452639 : Blo 2229435 6452639 := bstep (se 1 (by rfl) ⟨4839479, by rfl⟩ : syracuseStep 6452639 = 9678959) B9678959
theorem B4301759 : Blo 2229435 4301759 := bstep (se 1 (by rfl) ⟨3226319, by rfl⟩ : syracuseStep 4301759 = 6452639) B6452639
theorem B11471357 : Blo 2229435 11471357 := bstep (se 3 (by rfl) ⟨2150879, by rfl⟩ : syracuseStep 11471357 = 4301759) B4301759
theorem B7647571 : Blo 2229435 7647571 := bstep (se 1 (by rfl) ⟨5735678, by rfl⟩ : syracuseStep 7647571 = 11471357) B11471357
theorem B10196761 : Blo 2229435 10196761 := bstep (se 2 (by rfl) ⟨3823785, by rfl⟩ : syracuseStep 10196761 = 7647571) B7647571
theorem B13595681 : Blo 2229435 13595681 := bstep (se 2 (by rfl) ⟨5098380, by rfl⟩ : syracuseStep 13595681 = 10196761) B10196761
theorem B9063787 : Blo 2229435 9063787 := bstep (se 1 (by rfl) ⟨6797840, by rfl⟩ : syracuseStep 9063787 = 13595681) B13595681
theorem B12085049 : Blo 2229435 12085049 := bstep (se 2 (by rfl) ⟨4531893, by rfl⟩ : syracuseStep 12085049 = 9063787) B9063787
theorem B32226797 : Blo 2229435 32226797 := bstep (se 3 (by rfl) ⟨6042524, by rfl⟩ : syracuseStep 32226797 = 12085049) B12085049
theorem B21484531 : Blo 2229435 21484531 := bstep (se 1 (by rfl) ⟨16113398, by rfl⟩ : syracuseStep 21484531 = 32226797) B32226797
theorem B114584165 : Blo 2229435 114584165 := bstep (se 4 (by rfl) ⟨10742265, by rfl⟩ : syracuseStep 114584165 = 21484531) B21484531
theorem B76389443 : Blo 2229435 76389443 := bstep (se 1 (by rfl) ⟨57292082, by rfl⟩ : syracuseStep 76389443 = 114584165) B114584165
theorem B50926295 : Blo 2229435 50926295 := bstep (se 1 (by rfl) ⟨38194721, by rfl⟩ : syracuseStep 50926295 = 76389443) B76389443
theorem B33950863 : Blo 2229435 33950863 := bstep (se 1 (by rfl) ⟨25463147, by rfl⟩ : syracuseStep 33950863 = 50926295) B50926295
theorem B45267817 : Blo 2229435 45267817 := bstep (se 2 (by rfl) ⟨16975431, by rfl⟩ : syracuseStep 45267817 = 33950863) B33950863
theorem B60357089 : Blo 2229435 60357089 := bstep (se 2 (by rfl) ⟨22633908, by rfl⟩ : syracuseStep 60357089 = 45267817) B45267817
theorem B40238059 : Blo 2229435 40238059 := bstep (se 1 (by rfl) ⟨30178544, by rfl⟩ : syracuseStep 40238059 = 60357089) B60357089
theorem B53650745 : Blo 2229435 53650745 := bstep (se 2 (by rfl) ⟨20119029, by rfl⟩ : syracuseStep 53650745 = 40238059) B40238059
theorem B35767163 : Blo 2229435 35767163 := bstep (se 1 (by rfl) ⟨26825372, by rfl⟩ : syracuseStep 35767163 = 53650745) B53650745
theorem B23844775 : Blo 2229435 23844775 := bstep (se 1 (by rfl) ⟨17883581, by rfl⟩ : syracuseStep 23844775 = 35767163) B35767163
theorem B31793033 : Blo 2229435 31793033 := bstep (se 2 (by rfl) ⟨11922387, by rfl⟩ : syracuseStep 31793033 = 23844775) B23844775
theorem B21195355 : Blo 2229435 21195355 := bstep (se 1 (by rfl) ⟨15896516, by rfl⟩ : syracuseStep 21195355 = 31793033) B31793033
theorem B28260473 : Blo 2229435 28260473 := bstep (se 2 (by rfl) ⟨10597677, by rfl⟩ : syracuseStep 28260473 = 21195355) B21195355
theorem B75361261 : Blo 2229435 75361261 := bstep (se 3 (by rfl) ⟨14130236, by rfl⟩ : syracuseStep 75361261 = 28260473) B28260473
theorem B100481681 : Blo 2229435 100481681 := bstep (se 2 (by rfl) ⟨37680630, by rfl⟩ : syracuseStep 100481681 = 75361261) B75361261
theorem B267951149 : Blo 2229435 267951149 := bstep (se 3 (by rfl) ⟨50240840, by rfl⟩ : syracuseStep 267951149 = 100481681) B100481681
theorem B178634099 : Blo 2229435 178634099 := bstep (se 1 (by rfl) ⟨133975574, by rfl⟩ : syracuseStep 178634099 = 267951149) B267951149
theorem B119089399 : Blo 2229435 119089399 := bstep (se 1 (by rfl) ⟨89317049, by rfl⟩ : syracuseStep 119089399 = 178634099) B178634099
theorem B158785865 : Blo 2229435 158785865 := bstep (se 2 (by rfl) ⟨59544699, by rfl⟩ : syracuseStep 158785865 = 119089399) B119089399
theorem B105857243 : Blo 2229435 105857243 := bstep (se 1 (by rfl) ⟨79392932, by rfl⟩ : syracuseStep 105857243 = 158785865) B158785865
theorem B70571495 : Blo 2229435 70571495 := bstep (se 1 (by rfl) ⟨52928621, by rfl⟩ : syracuseStep 70571495 = 105857243) B105857243
theorem B47047663 : Blo 2229435 47047663 := bstep (se 1 (by rfl) ⟨35285747, by rfl⟩ : syracuseStep 47047663 = 70571495) B70571495
theorem B62730217 : Blo 2229435 62730217 := bstep (se 2 (by rfl) ⟨23523831, by rfl⟩ : syracuseStep 62730217 = 47047663) B47047663
theorem B83640289 : Blo 2229435 83640289 := bstep (se 2 (by rfl) ⟨31365108, by rfl⟩ : syracuseStep 83640289 = 62730217) B62730217
theorem B111520385 : Blo 2229435 111520385 := bstep (se 2 (by rfl) ⟨41820144, by rfl⟩ : syracuseStep 111520385 = 83640289) B83640289
theorem B74346923 : Blo 2229435 74346923 := bstep (se 1 (by rfl) ⟨55760192, by rfl⟩ : syracuseStep 74346923 = 111520385) B111520385
theorem B198258461 : Blo 2229435 198258461 := bstep (se 3 (by rfl) ⟨37173461, by rfl⟩ : syracuseStep 198258461 = 74346923) B74346923
theorem B132172307 : Blo 2229435 132172307 := bstep (se 1 (by rfl) ⟨99129230, by rfl⟩ : syracuseStep 132172307 = 198258461) B198258461
theorem B88114871 : Blo 2229435 88114871 := bstep (se 1 (by rfl) ⟨66086153, by rfl⟩ : syracuseStep 88114871 = 132172307) B132172307
theorem B234972989 : Blo 2229435 234972989 := bstep (se 3 (by rfl) ⟨44057435, by rfl⟩ : syracuseStep 234972989 = 88114871) B88114871
theorem B156648659 : Blo 2229435 156648659 := bstep (se 1 (by rfl) ⟨117486494, by rfl⟩ : syracuseStep 156648659 = 234972989) B234972989
theorem B417729757 : Blo 2229435 417729757 := bstep (se 3 (by rfl) ⟨78324329, by rfl⟩ : syracuseStep 417729757 = 156648659) B156648659
theorem B556973009 : Blo 2229435 556973009 := bstep (se 2 (by rfl) ⟨208864878, by rfl⟩ : syracuseStep 556973009 = 417729757) B417729757
theorem B371315339 : Blo 2229435 371315339 := bstep (se 1 (by rfl) ⟨278486504, by rfl⟩ : syracuseStep 371315339 = 556973009) B556973009
theorem B247543559 : Blo 2229435 247543559 := bstep (se 1 (by rfl) ⟨185657669, by rfl⟩ : syracuseStep 247543559 = 371315339) B371315339
theorem B165029039 : Blo 2229435 165029039 := bstep (se 1 (by rfl) ⟨123771779, by rfl⟩ : syracuseStep 165029039 = 247543559) B247543559
theorem B110019359 : Blo 2229435 110019359 := bstep (se 1 (by rfl) ⟨82514519, by rfl⟩ : syracuseStep 110019359 = 165029039) B165029039
theorem B73346239 : Blo 2229435 73346239 := bstep (se 1 (by rfl) ⟨55009679, by rfl⟩ : syracuseStep 73346239 = 110019359) B110019359
theorem B97794985 : Blo 2229435 97794985 := bstep (se 2 (by rfl) ⟨36673119, by rfl⟩ : syracuseStep 97794985 = 73346239) B73346239
theorem B130393313 : Blo 2229435 130393313 := bstep (se 2 (by rfl) ⟨48897492, by rfl⟩ : syracuseStep 130393313 = 97794985) B97794985
theorem B86928875 : Blo 2229435 86928875 := bstep (se 1 (by rfl) ⟨65196656, by rfl⟩ : syracuseStep 86928875 = 130393313) B130393313
theorem B57952583 : Blo 2229435 57952583 := bstep (se 1 (by rfl) ⟨43464437, by rfl⟩ : syracuseStep 57952583 = 86928875) B86928875
theorem B38635055 : Blo 2229435 38635055 := bstep (se 1 (by rfl) ⟨28976291, by rfl⟩ : syracuseStep 38635055 = 57952583) B57952583
theorem B25756703 : Blo 2229435 25756703 := bstep (se 1 (by rfl) ⟨19317527, by rfl⟩ : syracuseStep 25756703 = 38635055) B38635055
theorem B17171135 : Blo 2229435 17171135 := bstep (se 1 (by rfl) ⟨12878351, by rfl⟩ : syracuseStep 17171135 = 25756703) B25756703
theorem B11447423 : Blo 2229435 11447423 := bstep (se 1 (by rfl) ⟨8585567, by rfl⟩ : syracuseStep 11447423 = 17171135) B17171135
theorem B7631615 : Blo 2229435 7631615 := bstep (se 1 (by rfl) ⟨5723711, by rfl⟩ : syracuseStep 7631615 = 11447423) B11447423
theorem B20350973 : Blo 2229435 20350973 := bstep (se 3 (by rfl) ⟨3815807, by rfl⟩ : syracuseStep 20350973 = 7631615) B7631615
theorem B54269261 : Blo 2229435 54269261 := bstep (se 3 (by rfl) ⟨10175486, by rfl⟩ : syracuseStep 54269261 = 20350973) B20350973
theorem B36179507 : Blo 2229435 36179507 := bstep (se 1 (by rfl) ⟨27134630, by rfl⟩ : syracuseStep 36179507 = 54269261) B54269261
theorem B96478685 : Blo 2229435 96478685 := bstep (se 3 (by rfl) ⟨18089753, by rfl⟩ : syracuseStep 96478685 = 36179507) B36179507
theorem B64319123 : Blo 2229435 64319123 := bstep (se 1 (by rfl) ⟨48239342, by rfl⟩ : syracuseStep 64319123 = 96478685) B96478685
theorem B42879415 : Blo 2229435 42879415 := bstep (se 1 (by rfl) ⟨32159561, by rfl⟩ : syracuseStep 42879415 = 64319123) B64319123
theorem B57172553 : Blo 2229435 57172553 := bstep (se 2 (by rfl) ⟨21439707, by rfl⟩ : syracuseStep 57172553 = 42879415) B42879415
theorem B38115035 : Blo 2229435 38115035 := bstep (se 1 (by rfl) ⟨28586276, by rfl⟩ : syracuseStep 38115035 = 57172553) B57172553
theorem B25410023 : Blo 2229435 25410023 := bstep (se 1 (by rfl) ⟨19057517, by rfl⟩ : syracuseStep 25410023 = 38115035) B38115035
theorem B16940015 : Blo 2229435 16940015 := bstep (se 1 (by rfl) ⟨12705011, by rfl⟩ : syracuseStep 16940015 = 25410023) B25410023
theorem B11293343 : Blo 2229435 11293343 := bstep (se 1 (by rfl) ⟨8470007, by rfl⟩ : syracuseStep 11293343 = 16940015) B16940015
theorem B7528895 : Blo 2229435 7528895 := bstep (se 1 (by rfl) ⟨5646671, by rfl⟩ : syracuseStep 7528895 = 11293343) B11293343
theorem B5019263 : Blo 2229435 5019263 := bstep (se 1 (by rfl) ⟨3764447, by rfl⟩ : syracuseStep 5019263 = 7528895) B7528895
theorem B3346175 : Blo 2229435 3346175 := bstep (se 1 (by rfl) ⟨2509631, by rfl⟩ : syracuseStep 3346175 = 5019263) B5019263
theorem B2230783 : Blo 2229435 2230783 := bstep (se 1 (by rfl) ⟨1673087, by rfl⟩ : syracuseStep 2230783 = 3346175) B3346175
theorem B3346181 : Blo 2229435 3346181 := bbase (se 4 (by rfl) ⟨313704, by rfl⟩ : syracuseStep 3346181 = 627409) (by norm_num)
theorem B2230787 : Blo 2229435 2230787 := bstep (se 1 (by rfl) ⟨1673090, by rfl⟩ : syracuseStep 2230787 = 3346181) B3346181
theorem B3764461 : Blo 2229435 3764461 := bbase (se 3 (by rfl) ⟨705836, by rfl⟩ : syracuseStep 3764461 = 1411673) (by norm_num)
theorem B5019281 : Blo 2229435 5019281 := bstep (se 2 (by rfl) ⟨1882230, by rfl⟩ : syracuseStep 5019281 = 3764461) B3764461
theorem B3346187 : Blo 2229435 3346187 := bstep (se 1 (by rfl) ⟨2509640, by rfl⟩ : syracuseStep 3346187 = 5019281) B5019281
theorem B2230791 : Blo 2229435 2230791 := bstep (se 1 (by rfl) ⟨1673093, by rfl⟩ : syracuseStep 2230791 = 3346187) B3346187
theorem B2509645 : Blo 2229435 2509645 := bbase (se 3 (by rfl) ⟨470558, by rfl⟩ : syracuseStep 2509645 = 941117) (by norm_num)
theorem B3346193 : Blo 2229435 3346193 := bstep (se 2 (by rfl) ⟨1254822, by rfl⟩ : syracuseStep 3346193 = 2509645) B2509645
theorem B2230795 : Blo 2229435 2230795 := bstep (se 1 (by rfl) ⟨1673096, by rfl⟩ : syracuseStep 2230795 = 3346193) B3346193
theorem B7528949 : Blo 2229435 7528949 := bbase (se 5 (by rfl) ⟨352919, by rfl⟩ : syracuseStep 7528949 = 705839) (by norm_num)
theorem B5019299 : Blo 2229435 5019299 := bstep (se 1 (by rfl) ⟨3764474, by rfl⟩ : syracuseStep 5019299 = 7528949) B7528949
theorem B3346199 : Blo 2229435 3346199 := bstep (se 1 (by rfl) ⟨2509649, by rfl⟩ : syracuseStep 3346199 = 5019299) B5019299
theorem B2230799 : Blo 2229435 2230799 := bstep (se 1 (by rfl) ⟨1673099, by rfl⟩ : syracuseStep 2230799 = 3346199) B3346199
theorem B3346205 : Blo 2229435 3346205 := bbase (se 3 (by rfl) ⟨627413, by rfl⟩ : syracuseStep 3346205 = 1254827) (by norm_num)
theorem B2230803 : Blo 2229435 2230803 := bstep (se 1 (by rfl) ⟨1673102, by rfl⟩ : syracuseStep 2230803 = 3346205) B3346205
theorem B5019317 : Blo 2229435 5019317 := bbase (se 5 (by rfl) ⟨235280, by rfl⟩ : syracuseStep 5019317 = 470561) (by norm_num)
theorem B3346211 : Blo 2229435 3346211 := bstep (se 1 (by rfl) ⟨2509658, by rfl⟩ : syracuseStep 3346211 = 5019317) B5019317
theorem B2230807 : Blo 2229435 2230807 := bstep (se 1 (by rfl) ⟨1673105, by rfl⟩ : syracuseStep 2230807 = 3346211) B3346211
theorem B12705173 : Blo 2229435 12705173 := bbase (se 6 (by rfl) ⟨297777, by rfl⟩ : syracuseStep 12705173 = 595555) (by norm_num)
theorem B8470115 : Blo 2229435 8470115 := bstep (se 1 (by rfl) ⟨6352586, by rfl⟩ : syracuseStep 8470115 = 12705173) B12705173
theorem B5646743 : Blo 2229435 5646743 := bstep (se 1 (by rfl) ⟨4235057, by rfl⟩ : syracuseStep 5646743 = 8470115) B8470115
theorem B3764495 : Blo 2229435 3764495 := bstep (se 1 (by rfl) ⟨2823371, by rfl⟩ : syracuseStep 3764495 = 5646743) B5646743
theorem B2509663 : Blo 2229435 2509663 := bstep (se 1 (by rfl) ⟨1882247, by rfl⟩ : syracuseStep 2509663 = 3764495) B3764495
theorem B3346217 : Blo 2229435 3346217 := bstep (se 2 (by rfl) ⟨1254831, by rfl⟩ : syracuseStep 3346217 = 2509663) B2509663
theorem B2230811 : Blo 2229435 2230811 := bstep (se 1 (by rfl) ⟨1673108, by rfl⟩ : syracuseStep 2230811 = 3346217) B3346217
theorem B6352597 : Blo 2229435 6352597 := bbase (se 7 (by rfl) ⟨74444, by rfl⟩ : syracuseStep 6352597 = 148889) (by norm_num)
theorem B8470129 : Blo 2229435 8470129 := bstep (se 2 (by rfl) ⟨3176298, by rfl⟩ : syracuseStep 8470129 = 6352597) B6352597
theorem B11293505 : Blo 2229435 11293505 := bstep (se 2 (by rfl) ⟨4235064, by rfl⟩ : syracuseStep 11293505 = 8470129) B8470129
theorem B7529003 : Blo 2229435 7529003 := bstep (se 1 (by rfl) ⟨5646752, by rfl⟩ : syracuseStep 7529003 = 11293505) B11293505
theorem B5019335 : Blo 2229435 5019335 := bstep (se 1 (by rfl) ⟨3764501, by rfl⟩ : syracuseStep 5019335 = 7529003) B7529003
theorem B3346223 : Blo 2229435 3346223 := bstep (se 1 (by rfl) ⟨2509667, by rfl⟩ : syracuseStep 3346223 = 5019335) B5019335
theorem B2230815 : Blo 2229435 2230815 := bstep (se 1 (by rfl) ⟨1673111, by rfl⟩ : syracuseStep 2230815 = 3346223) B3346223
theorem B3346229 : Blo 2229435 3346229 := bbase (se 5 (by rfl) ⟨156854, by rfl⟩ : syracuseStep 3346229 = 313709) (by norm_num)
theorem B2230819 : Blo 2229435 2230819 := bstep (se 1 (by rfl) ⟨1673114, by rfl⟩ : syracuseStep 2230819 = 3346229) B3346229
theorem B5646773 : Blo 2229435 5646773 := bbase (se 5 (by rfl) ⟨264692, by rfl⟩ : syracuseStep 5646773 = 529385) (by norm_num)
theorem B3764515 : Blo 2229435 3764515 := bstep (se 1 (by rfl) ⟨2823386, by rfl⟩ : syracuseStep 3764515 = 5646773) B5646773
theorem B5019353 : Blo 2229435 5019353 := bstep (se 2 (by rfl) ⟨1882257, by rfl⟩ : syracuseStep 5019353 = 3764515) B3764515
theorem B3346235 : Blo 2229435 3346235 := bstep (se 1 (by rfl) ⟨2509676, by rfl⟩ : syracuseStep 3346235 = 5019353) B5019353
theorem B2230823 : Blo 2229435 2230823 := bstep (se 1 (by rfl) ⟨1673117, by rfl⟩ : syracuseStep 2230823 = 3346235) B3346235
theorem B2509681 : Blo 2229435 2509681 := bbase (se 2 (by rfl) ⟨941130, by rfl⟩ : syracuseStep 2509681 = 1882261) (by norm_num)
theorem B3346241 : Blo 2229435 3346241 := bstep (se 2 (by rfl) ⟨1254840, by rfl⟩ : syracuseStep 3346241 = 2509681) B2509681
theorem B2230827 : Blo 2229435 2230827 := bstep (se 1 (by rfl) ⟨1673120, by rfl⟩ : syracuseStep 2230827 = 3346241) B3346241
theorem B9528965 : Blo 2229435 9528965 := bbase (se 4 (by rfl) ⟨893340, by rfl⟩ : syracuseStep 9528965 = 1786681) (by norm_num)
theorem B6352643 : Blo 2229435 6352643 := bstep (se 1 (by rfl) ⟨4764482, by rfl⟩ : syracuseStep 6352643 = 9528965) B9528965
theorem B4235095 : Blo 2229435 4235095 := bstep (se 1 (by rfl) ⟨3176321, by rfl⟩ : syracuseStep 4235095 = 6352643) B6352643
theorem B5646793 : Blo 2229435 5646793 := bstep (se 2 (by rfl) ⟨2117547, by rfl⟩ : syracuseStep 5646793 = 4235095) B4235095
theorem B7529057 : Blo 2229435 7529057 := bstep (se 2 (by rfl) ⟨2823396, by rfl⟩ : syracuseStep 7529057 = 5646793) B5646793
theorem B5019371 : Blo 2229435 5019371 := bstep (se 1 (by rfl) ⟨3764528, by rfl⟩ : syracuseStep 5019371 = 7529057) B7529057
theorem B3346247 : Blo 2229435 3346247 := bstep (se 1 (by rfl) ⟨2509685, by rfl⟩ : syracuseStep 3346247 = 5019371) B5019371
theorem B2230831 : Blo 2229435 2230831 := bstep (se 1 (by rfl) ⟨1673123, by rfl⟩ : syracuseStep 2230831 = 3346247) B3346247
theorem B3346253 : Blo 2229435 3346253 := bbase (se 3 (by rfl) ⟨627422, by rfl⟩ : syracuseStep 3346253 = 1254845) (by norm_num)
theorem B2230835 : Blo 2229435 2230835 := bstep (se 1 (by rfl) ⟨1673126, by rfl⟩ : syracuseStep 2230835 = 3346253) B3346253
theorem B5019389 : Blo 2229435 5019389 := bbase (se 3 (by rfl) ⟨941135, by rfl⟩ : syracuseStep 5019389 = 1882271) (by norm_num)
theorem B3346259 : Blo 2229435 3346259 := bstep (se 1 (by rfl) ⟨2509694, by rfl⟩ : syracuseStep 3346259 = 5019389) B5019389
theorem B2230839 : Blo 2229435 2230839 := bstep (se 1 (by rfl) ⟨1673129, by rfl⟩ : syracuseStep 2230839 = 3346259) B3346259
theorem B3764549 : Blo 2229435 3764549 := bbase (se 4 (by rfl) ⟨352926, by rfl⟩ : syracuseStep 3764549 = 705853) (by norm_num)
theorem B2509699 : Blo 2229435 2509699 := bstep (se 1 (by rfl) ⟨1882274, by rfl⟩ : syracuseStep 2509699 = 3764549) B3764549
theorem B3346265 : Blo 2229435 3346265 := bstep (se 2 (by rfl) ⟨1254849, by rfl⟩ : syracuseStep 3346265 = 2509699) B2509699
theorem B2230843 : Blo 2229435 2230843 := bstep (se 1 (by rfl) ⟨1673132, by rfl⟩ : syracuseStep 2230843 = 3346265) B3346265
theorem B16940501 : Blo 2229435 16940501 := bbase (se 7 (by rfl) ⟨198521, by rfl⟩ : syracuseStep 16940501 = 397043) (by norm_num)
theorem B11293667 : Blo 2229435 11293667 := bstep (se 1 (by rfl) ⟨8470250, by rfl⟩ : syracuseStep 11293667 = 16940501) B16940501
theorem B7529111 : Blo 2229435 7529111 := bstep (se 1 (by rfl) ⟨5646833, by rfl⟩ : syracuseStep 7529111 = 11293667) B11293667
theorem B5019407 : Blo 2229435 5019407 := bstep (se 1 (by rfl) ⟨3764555, by rfl⟩ : syracuseStep 5019407 = 7529111) B7529111
theorem B3346271 : Blo 2229435 3346271 := bstep (se 1 (by rfl) ⟨2509703, by rfl⟩ : syracuseStep 3346271 = 5019407) B5019407
theorem B2230847 : Blo 2229435 2230847 := bstep (se 1 (by rfl) ⟨1673135, by rfl⟩ : syracuseStep 2230847 = 3346271) B3346271
theorem B3346277 : Blo 2229435 3346277 := bbase (se 4 (by rfl) ⟨313713, by rfl⟩ : syracuseStep 3346277 = 627427) (by norm_num)
theorem B2230851 : Blo 2229435 2230851 := bstep (se 1 (by rfl) ⟨1673138, by rfl⟩ : syracuseStep 2230851 = 3346277) B3346277
theorem B4235141 : Blo 2229435 4235141 := bbase (se 4 (by rfl) ⟨397044, by rfl⟩ : syracuseStep 4235141 = 794089) (by norm_num)
theorem B2823427 : Blo 2229435 2823427 := bstep (se 1 (by rfl) ⟨2117570, by rfl⟩ : syracuseStep 2823427 = 4235141) B4235141
theorem B3764569 : Blo 2229435 3764569 := bstep (se 2 (by rfl) ⟨1411713, by rfl⟩ : syracuseStep 3764569 = 2823427) B2823427
theorem B5019425 : Blo 2229435 5019425 := bstep (se 2 (by rfl) ⟨1882284, by rfl⟩ : syracuseStep 5019425 = 3764569) B3764569
theorem B3346283 : Blo 2229435 3346283 := bstep (se 1 (by rfl) ⟨2509712, by rfl⟩ : syracuseStep 3346283 = 5019425) B5019425
theorem B2230855 : Blo 2229435 2230855 := bstep (se 1 (by rfl) ⟨1673141, by rfl⟩ : syracuseStep 2230855 = 3346283) B3346283
theorem B2509717 : Blo 2229435 2509717 := bbase (se 6 (by rfl) ⟨58821, by rfl⟩ : syracuseStep 2509717 = 117643) (by norm_num)
theorem B3346289 : Blo 2229435 3346289 := bstep (se 2 (by rfl) ⟨1254858, by rfl⟩ : syracuseStep 3346289 = 2509717) B2509717
theorem B2230859 : Blo 2229435 2230859 := bstep (se 1 (by rfl) ⟨1673144, by rfl⟩ : syracuseStep 2230859 = 3346289) B3346289
theorem B2823437 : Blo 2229435 2823437 := bbase (se 3 (by rfl) ⟨529394, by rfl⟩ : syracuseStep 2823437 = 1058789) (by norm_num)
theorem B7529165 : Blo 2229435 7529165 := bstep (se 3 (by rfl) ⟨1411718, by rfl⟩ : syracuseStep 7529165 = 2823437) B2823437
theorem B5019443 : Blo 2229435 5019443 := bstep (se 1 (by rfl) ⟨3764582, by rfl⟩ : syracuseStep 5019443 = 7529165) B7529165
theorem B3346295 : Blo 2229435 3346295 := bstep (se 1 (by rfl) ⟨2509721, by rfl⟩ : syracuseStep 3346295 = 5019443) B5019443
theorem B2230863 : Blo 2229435 2230863 := bstep (se 1 (by rfl) ⟨1673147, by rfl⟩ : syracuseStep 2230863 = 3346295) B3346295
theorem B3346301 : Blo 2229435 3346301 := bbase (se 3 (by rfl) ⟨627431, by rfl⟩ : syracuseStep 3346301 = 1254863) (by norm_num)
theorem B2230867 : Blo 2229435 2230867 := bstep (se 1 (by rfl) ⟨1673150, by rfl⟩ : syracuseStep 2230867 = 3346301) B3346301
theorem B5019461 : Blo 2229435 5019461 := bbase (se 4 (by rfl) ⟨470574, by rfl⟩ : syracuseStep 5019461 = 941149) (by norm_num)
theorem B3346307 : Blo 2229435 3346307 := bstep (se 1 (by rfl) ⟨2509730, by rfl⟩ : syracuseStep 3346307 = 5019461) B5019461
theorem B2230871 : Blo 2229435 2230871 := bstep (se 1 (by rfl) ⟨1673153, by rfl⟩ : syracuseStep 2230871 = 3346307) B3346307
theorem B3015085 : Blo 2229435 3015085 := bbase (se 3 (by rfl) ⟨565328, by rfl⟩ : syracuseStep 3015085 = 1130657) (by norm_num)
theorem B4020113 : Blo 2229435 4020113 := bstep (se 2 (by rfl) ⟨1507542, by rfl⟩ : syracuseStep 4020113 = 3015085) B3015085
theorem B2680075 : Blo 2229435 2680075 := bstep (se 1 (by rfl) ⟨2010056, by rfl⟩ : syracuseStep 2680075 = 4020113) B4020113
theorem B3573433 : Blo 2229435 3573433 := bstep (se 2 (by rfl) ⟨1340037, by rfl⟩ : syracuseStep 3573433 = 2680075) B2680075
theorem B4764577 : Blo 2229435 4764577 := bstep (se 2 (by rfl) ⟨1786716, by rfl⟩ : syracuseStep 4764577 = 3573433) B3573433
theorem B6352769 : Blo 2229435 6352769 := bstep (se 2 (by rfl) ⟨2382288, by rfl⟩ : syracuseStep 6352769 = 4764577) B4764577
theorem B4235179 : Blo 2229435 4235179 := bstep (se 1 (by rfl) ⟨3176384, by rfl⟩ : syracuseStep 4235179 = 6352769) B6352769
theorem B5646905 : Blo 2229435 5646905 := bstep (se 2 (by rfl) ⟨2117589, by rfl⟩ : syracuseStep 5646905 = 4235179) B4235179
theorem B3764603 : Blo 2229435 3764603 := bstep (se 1 (by rfl) ⟨2823452, by rfl⟩ : syracuseStep 3764603 = 5646905) B5646905
theorem B2509735 : Blo 2229435 2509735 := bstep (se 1 (by rfl) ⟨1882301, by rfl⟩ : syracuseStep 2509735 = 3764603) B3764603
theorem B3346313 : Blo 2229435 3346313 := bstep (se 2 (by rfl) ⟨1254867, by rfl⟩ : syracuseStep 3346313 = 2509735) B2509735
theorem B2230875 : Blo 2229435 2230875 := bstep (se 1 (by rfl) ⟨1673156, by rfl⟩ : syracuseStep 2230875 = 3346313) B3346313
theorem B11293829 : Blo 2229435 11293829 := bbase (se 4 (by rfl) ⟨1058796, by rfl⟩ : syracuseStep 11293829 = 2117593) (by norm_num)
theorem B7529219 : Blo 2229435 7529219 := bstep (se 1 (by rfl) ⟨5646914, by rfl⟩ : syracuseStep 7529219 = 11293829) B11293829
theorem B5019479 : Blo 2229435 5019479 := bstep (se 1 (by rfl) ⟨3764609, by rfl⟩ : syracuseStep 5019479 = 7529219) B7529219
theorem B3346319 : Blo 2229435 3346319 := bstep (se 1 (by rfl) ⟨2509739, by rfl⟩ : syracuseStep 3346319 = 5019479) B5019479
theorem B2230879 : Blo 2229435 2230879 := bstep (se 1 (by rfl) ⟨1673159, by rfl⟩ : syracuseStep 2230879 = 3346319) B3346319
theorem B3346325 : Blo 2229435 3346325 := bbase (se 6 (by rfl) ⟨78429, by rfl⟩ : syracuseStep 3346325 = 156859) (by norm_num)
theorem B2230883 : Blo 2229435 2230883 := bstep (se 1 (by rfl) ⟨1673162, by rfl⟩ : syracuseStep 2230883 = 3346325) B3346325
theorem B2382301 : Blo 2229435 2382301 := bbase (se 3 (by rfl) ⟨446681, by rfl⟩ : syracuseStep 2382301 = 893363) (by norm_num)
theorem B12705605 : Blo 2229435 12705605 := bstep (se 4 (by rfl) ⟨1191150, by rfl⟩ : syracuseStep 12705605 = 2382301) B2382301
theorem B8470403 : Blo 2229435 8470403 := bstep (se 1 (by rfl) ⟨6352802, by rfl⟩ : syracuseStep 8470403 = 12705605) B12705605
theorem B5646935 : Blo 2229435 5646935 := bstep (se 1 (by rfl) ⟨4235201, by rfl⟩ : syracuseStep 5646935 = 8470403) B8470403
theorem B3764623 : Blo 2229435 3764623 := bstep (se 1 (by rfl) ⟨2823467, by rfl⟩ : syracuseStep 3764623 = 5646935) B5646935
theorem B5019497 : Blo 2229435 5019497 := bstep (se 2 (by rfl) ⟨1882311, by rfl⟩ : syracuseStep 5019497 = 3764623) B3764623
theorem B3346331 : Blo 2229435 3346331 := bstep (se 1 (by rfl) ⟨2509748, by rfl⟩ : syracuseStep 3346331 = 5019497) B5019497
theorem B2230887 : Blo 2229435 2230887 := bstep (se 1 (by rfl) ⟨1673165, by rfl⟩ : syracuseStep 2230887 = 3346331) B3346331
theorem B2509753 : Blo 2229435 2509753 := bbase (se 2 (by rfl) ⟨941157, by rfl⟩ : syracuseStep 2509753 = 1882315) (by norm_num)
theorem B3346337 : Blo 2229435 3346337 := bstep (se 2 (by rfl) ⟨1254876, by rfl⟩ : syracuseStep 3346337 = 2509753) B2509753
theorem B2230891 : Blo 2229435 2230891 := bstep (se 1 (by rfl) ⟨1673168, by rfl⟩ : syracuseStep 2230891 = 3346337) B3346337
theorem B5360197 : Blo 2229435 5360197 := bbase (se 4 (by rfl) ⟨502518, by rfl⟩ : syracuseStep 5360197 = 1005037) (by norm_num)
theorem B7146929 : Blo 2229435 7146929 := bstep (se 2 (by rfl) ⟨2680098, by rfl⟩ : syracuseStep 7146929 = 5360197) B5360197
theorem B4764619 : Blo 2229435 4764619 := bstep (se 1 (by rfl) ⟨3573464, by rfl⟩ : syracuseStep 4764619 = 7146929) B7146929
theorem B6352825 : Blo 2229435 6352825 := bstep (se 2 (by rfl) ⟨2382309, by rfl⟩ : syracuseStep 6352825 = 4764619) B4764619
theorem B8470433 : Blo 2229435 8470433 := bstep (se 2 (by rfl) ⟨3176412, by rfl⟩ : syracuseStep 8470433 = 6352825) B6352825
theorem B5646955 : Blo 2229435 5646955 := bstep (se 1 (by rfl) ⟨4235216, by rfl⟩ : syracuseStep 5646955 = 8470433) B8470433
theorem B7529273 : Blo 2229435 7529273 := bstep (se 2 (by rfl) ⟨2823477, by rfl⟩ : syracuseStep 7529273 = 5646955) B5646955
theorem B5019515 : Blo 2229435 5019515 := bstep (se 1 (by rfl) ⟨3764636, by rfl⟩ : syracuseStep 5019515 = 7529273) B7529273
theorem B3346343 : Blo 2229435 3346343 := bstep (se 1 (by rfl) ⟨2509757, by rfl⟩ : syracuseStep 3346343 = 5019515) B5019515
theorem B2230895 : Blo 2229435 2230895 := bstep (se 1 (by rfl) ⟨1673171, by rfl⟩ : syracuseStep 2230895 = 3346343) B3346343
theorem B3346349 : Blo 2229435 3346349 := bbase (se 3 (by rfl) ⟨627440, by rfl⟩ : syracuseStep 3346349 = 1254881) (by norm_num)
theorem B2230899 : Blo 2229435 2230899 := bstep (se 1 (by rfl) ⟨1673174, by rfl⟩ : syracuseStep 2230899 = 3346349) B3346349
theorem B5019533 : Blo 2229435 5019533 := bbase (se 3 (by rfl) ⟨941162, by rfl⟩ : syracuseStep 5019533 = 1882325) (by norm_num)
theorem B3346355 : Blo 2229435 3346355 := bstep (se 1 (by rfl) ⟨2509766, by rfl⟩ : syracuseStep 3346355 = 5019533) B5019533
theorem B2230903 : Blo 2229435 2230903 := bstep (se 1 (by rfl) ⟨1673177, by rfl⟩ : syracuseStep 2230903 = 3346355) B3346355
theorem B2823493 : Blo 2229435 2823493 := bbase (se 4 (by rfl) ⟨264702, by rfl⟩ : syracuseStep 2823493 = 529405) (by norm_num)
theorem B3764657 : Blo 2229435 3764657 := bstep (se 2 (by rfl) ⟨1411746, by rfl⟩ : syracuseStep 3764657 = 2823493) B2823493
theorem B2509771 : Blo 2229435 2509771 := bstep (se 1 (by rfl) ⟨1882328, by rfl⟩ : syracuseStep 2509771 = 3764657) B3764657
theorem B3346361 : Blo 2229435 3346361 := bstep (se 2 (by rfl) ⟨1254885, by rfl⟩ : syracuseStep 3346361 = 2509771) B2509771
theorem B2230907 : Blo 2229435 2230907 := bstep (se 1 (by rfl) ⟨1673180, by rfl⟩ : syracuseStep 2230907 = 3346361) B3346361
theorem B10720469 : Blo 2229435 10720469 := bbase (se 7 (by rfl) ⟨125630, by rfl⟩ : syracuseStep 10720469 = 251261) (by norm_num)
theorem B28587917 : Blo 2229435 28587917 := bstep (se 3 (by rfl) ⟨5360234, by rfl⟩ : syracuseStep 28587917 = 10720469) B10720469
theorem B19058611 : Blo 2229435 19058611 := bstep (se 1 (by rfl) ⟨14293958, by rfl⟩ : syracuseStep 19058611 = 28587917) B28587917
theorem B25411481 : Blo 2229435 25411481 := bstep (se 2 (by rfl) ⟨9529305, by rfl⟩ : syracuseStep 25411481 = 19058611) B19058611
theorem B16940987 : Blo 2229435 16940987 := bstep (se 1 (by rfl) ⟨12705740, by rfl⟩ : syracuseStep 16940987 = 25411481) B25411481
theorem B11293991 : Blo 2229435 11293991 := bstep (se 1 (by rfl) ⟨8470493, by rfl⟩ : syracuseStep 11293991 = 16940987) B16940987
theorem B7529327 : Blo 2229435 7529327 := bstep (se 1 (by rfl) ⟨5646995, by rfl⟩ : syracuseStep 7529327 = 11293991) B11293991
theorem B5019551 : Blo 2229435 5019551 := bstep (se 1 (by rfl) ⟨3764663, by rfl⟩ : syracuseStep 5019551 = 7529327) B7529327
theorem B3346367 : Blo 2229435 3346367 := bstep (se 1 (by rfl) ⟨2509775, by rfl⟩ : syracuseStep 3346367 = 5019551) B5019551
theorem B2230911 : Blo 2229435 2230911 := bstep (se 1 (by rfl) ⟨1673183, by rfl⟩ : syracuseStep 2230911 = 3346367) B3346367
theorem B3346373 : Blo 2229435 3346373 := bbase (se 4 (by rfl) ⟨313722, by rfl⟩ : syracuseStep 3346373 = 627445) (by norm_num)
theorem B2230915 : Blo 2229435 2230915 := bstep (se 1 (by rfl) ⟨1673186, by rfl⟩ : syracuseStep 2230915 = 3346373) B3346373
theorem B3764677 : Blo 2229435 3764677 := bbase (se 4 (by rfl) ⟨352938, by rfl⟩ : syracuseStep 3764677 = 705877) (by norm_num)
theorem B5019569 : Blo 2229435 5019569 := bstep (se 2 (by rfl) ⟨1882338, by rfl⟩ : syracuseStep 5019569 = 3764677) B3764677
theorem B3346379 : Blo 2229435 3346379 := bstep (se 1 (by rfl) ⟨2509784, by rfl⟩ : syracuseStep 3346379 = 5019569) B5019569
theorem B2230919 : Blo 2229435 2230919 := bstep (se 1 (by rfl) ⟨1673189, by rfl⟩ : syracuseStep 2230919 = 3346379) B3346379
theorem B2509789 : Blo 2229435 2509789 := bbase (se 3 (by rfl) ⟨470585, by rfl⟩ : syracuseStep 2509789 = 941171) (by norm_num)
theorem B3346385 : Blo 2229435 3346385 := bstep (se 2 (by rfl) ⟨1254894, by rfl⟩ : syracuseStep 3346385 = 2509789) B2509789
theorem B2230923 : Blo 2229435 2230923 := bstep (se 1 (by rfl) ⟨1673192, by rfl⟩ : syracuseStep 2230923 = 3346385) B3346385
theorem B7529381 : Blo 2229435 7529381 := bbase (se 4 (by rfl) ⟨705879, by rfl⟩ : syracuseStep 7529381 = 1411759) (by norm_num)
theorem B5019587 : Blo 2229435 5019587 := bstep (se 1 (by rfl) ⟨3764690, by rfl⟩ : syracuseStep 5019587 = 7529381) B7529381
theorem B3346391 : Blo 2229435 3346391 := bstep (se 1 (by rfl) ⟨2509793, by rfl⟩ : syracuseStep 3346391 = 5019587) B5019587
theorem B2230927 : Blo 2229435 2230927 := bstep (se 1 (by rfl) ⟨1673195, by rfl⟩ : syracuseStep 2230927 = 3346391) B3346391
theorem B3346397 : Blo 2229435 3346397 := bbase (se 3 (by rfl) ⟨627449, by rfl⟩ : syracuseStep 3346397 = 1254899) (by norm_num)
theorem B2230931 : Blo 2229435 2230931 := bstep (se 1 (by rfl) ⟨1673198, by rfl⟩ : syracuseStep 2230931 = 3346397) B3346397
theorem B5019605 : Blo 2229435 5019605 := bbase (se 7 (by rfl) ⟨58823, by rfl⟩ : syracuseStep 5019605 = 117647) (by norm_num)
theorem B3346403 : Blo 2229435 3346403 := bstep (se 1 (by rfl) ⟨2509802, by rfl⟩ : syracuseStep 3346403 = 5019605) B5019605
theorem B2230935 : Blo 2229435 2230935 := bstep (se 1 (by rfl) ⟨1673201, by rfl⟩ : syracuseStep 2230935 = 3346403) B3346403
theorem B5088101 : Blo 2229435 5088101 := bbase (se 4 (by rfl) ⟨477009, by rfl⟩ : syracuseStep 5088101 = 954019) (by norm_num)
theorem B13568269 : Blo 2229435 13568269 := bstep (se 3 (by rfl) ⟨2544050, by rfl⟩ : syracuseStep 13568269 = 5088101) B5088101
theorem B18091025 : Blo 2229435 18091025 := bstep (se 2 (by rfl) ⟨6784134, by rfl⟩ : syracuseStep 18091025 = 13568269) B13568269
theorem B12060683 : Blo 2229435 12060683 := bstep (se 1 (by rfl) ⟨9045512, by rfl⟩ : syracuseStep 12060683 = 18091025) B18091025
theorem B8040455 : Blo 2229435 8040455 := bstep (se 1 (by rfl) ⟨6030341, by rfl⟩ : syracuseStep 8040455 = 12060683) B12060683
theorem B5360303 : Blo 2229435 5360303 := bstep (se 1 (by rfl) ⟨4020227, by rfl⟩ : syracuseStep 5360303 = 8040455) B8040455
theorem B14294141 : Blo 2229435 14294141 := bstep (se 3 (by rfl) ⟨2680151, by rfl⟩ : syracuseStep 14294141 = 5360303) B5360303
theorem B9529427 : Blo 2229435 9529427 := bstep (se 1 (by rfl) ⟨7147070, by rfl⟩ : syracuseStep 9529427 = 14294141) B14294141
theorem B6352951 : Blo 2229435 6352951 := bstep (se 1 (by rfl) ⟨4764713, by rfl⟩ : syracuseStep 6352951 = 9529427) B9529427
theorem B8470601 : Blo 2229435 8470601 := bstep (se 2 (by rfl) ⟨3176475, by rfl⟩ : syracuseStep 8470601 = 6352951) B6352951
theorem B5647067 : Blo 2229435 5647067 := bstep (se 1 (by rfl) ⟨4235300, by rfl⟩ : syracuseStep 5647067 = 8470601) B8470601
theorem B3764711 : Blo 2229435 3764711 := bstep (se 1 (by rfl) ⟨2823533, by rfl⟩ : syracuseStep 3764711 = 5647067) B5647067
theorem B2509807 : Blo 2229435 2509807 := bstep (se 1 (by rfl) ⟨1882355, by rfl⟩ : syracuseStep 2509807 = 3764711) B3764711
theorem B3346409 : Blo 2229435 3346409 := bstep (se 2 (by rfl) ⟨1254903, by rfl⟩ : syracuseStep 3346409 = 2509807) B2509807
theorem B2230939 : Blo 2229435 2230939 := bstep (se 1 (by rfl) ⟨1673204, by rfl⟩ : syracuseStep 2230939 = 3346409) B3346409
theorem B3573541 : Blo 2229435 3573541 := bbase (se 4 (by rfl) ⟨335019, by rfl⟩ : syracuseStep 3573541 = 670039) (by norm_num)
theorem B19058885 : Blo 2229435 19058885 := bstep (se 4 (by rfl) ⟨1786770, by rfl⟩ : syracuseStep 19058885 = 3573541) B3573541
theorem B12705923 : Blo 2229435 12705923 := bstep (se 1 (by rfl) ⟨9529442, by rfl⟩ : syracuseStep 12705923 = 19058885) B19058885
theorem B8470615 : Blo 2229435 8470615 := bstep (se 1 (by rfl) ⟨6352961, by rfl⟩ : syracuseStep 8470615 = 12705923) B12705923
theorem B11294153 : Blo 2229435 11294153 := bstep (se 2 (by rfl) ⟨4235307, by rfl⟩ : syracuseStep 11294153 = 8470615) B8470615
theorem B7529435 : Blo 2229435 7529435 := bstep (se 1 (by rfl) ⟨5647076, by rfl⟩ : syracuseStep 7529435 = 11294153) B11294153
theorem B5019623 : Blo 2229435 5019623 := bstep (se 1 (by rfl) ⟨3764717, by rfl⟩ : syracuseStep 5019623 = 7529435) B7529435
theorem B3346415 : Blo 2229435 3346415 := bstep (se 1 (by rfl) ⟨2509811, by rfl⟩ : syracuseStep 3346415 = 5019623) B5019623
theorem B2230943 : Blo 2229435 2230943 := bstep (se 1 (by rfl) ⟨1673207, by rfl⟩ : syracuseStep 2230943 = 3346415) B3346415
theorem B3346421 : Blo 2229435 3346421 := bbase (se 5 (by rfl) ⟨156863, by rfl⟩ : syracuseStep 3346421 = 313727) (by norm_num)
theorem B2230947 : Blo 2229435 2230947 := bstep (se 1 (by rfl) ⟨1673210, by rfl⟩ : syracuseStep 2230947 = 3346421) B3346421
theorem B7147109 : Blo 2229435 7147109 := bbase (se 4 (by rfl) ⟨670041, by rfl⟩ : syracuseStep 7147109 = 1340083) (by norm_num)
theorem B4764739 : Blo 2229435 4764739 := bstep (se 1 (by rfl) ⟨3573554, by rfl⟩ : syracuseStep 4764739 = 7147109) B7147109
theorem B6352985 : Blo 2229435 6352985 := bstep (se 2 (by rfl) ⟨2382369, by rfl⟩ : syracuseStep 6352985 = 4764739) B4764739
theorem B4235323 : Blo 2229435 4235323 := bstep (se 1 (by rfl) ⟨3176492, by rfl⟩ : syracuseStep 4235323 = 6352985) B6352985
theorem B5647097 : Blo 2229435 5647097 := bstep (se 2 (by rfl) ⟨2117661, by rfl⟩ : syracuseStep 5647097 = 4235323) B4235323
theorem B3764731 : Blo 2229435 3764731 := bstep (se 1 (by rfl) ⟨2823548, by rfl⟩ : syracuseStep 3764731 = 5647097) B5647097
theorem B5019641 : Blo 2229435 5019641 := bstep (se 2 (by rfl) ⟨1882365, by rfl⟩ : syracuseStep 5019641 = 3764731) B3764731
theorem B3346427 : Blo 2229435 3346427 := bstep (se 1 (by rfl) ⟨2509820, by rfl⟩ : syracuseStep 3346427 = 5019641) B5019641
theorem B2230951 : Blo 2229435 2230951 := bstep (se 1 (by rfl) ⟨1673213, by rfl⟩ : syracuseStep 2230951 = 3346427) B3346427
theorem B2509825 : Blo 2229435 2509825 := bbase (se 2 (by rfl) ⟨941184, by rfl⟩ : syracuseStep 2509825 = 1882369) (by norm_num)
theorem B3346433 : Blo 2229435 3346433 := bstep (se 2 (by rfl) ⟨1254912, by rfl⟩ : syracuseStep 3346433 = 2509825) B2509825
theorem B2230955 : Blo 2229435 2230955 := bstep (se 1 (by rfl) ⟨1673216, by rfl⟩ : syracuseStep 2230955 = 3346433) B3346433
theorem B5647117 : Blo 2229435 5647117 := bbase (se 3 (by rfl) ⟨1058834, by rfl⟩ : syracuseStep 5647117 = 2117669) (by norm_num)
theorem B7529489 : Blo 2229435 7529489 := bstep (se 2 (by rfl) ⟨2823558, by rfl⟩ : syracuseStep 7529489 = 5647117) B5647117
theorem B5019659 : Blo 2229435 5019659 := bstep (se 1 (by rfl) ⟨3764744, by rfl⟩ : syracuseStep 5019659 = 7529489) B7529489
theorem B3346439 : Blo 2229435 3346439 := bstep (se 1 (by rfl) ⟨2509829, by rfl⟩ : syracuseStep 3346439 = 5019659) B5019659
theorem B2230959 : Blo 2229435 2230959 := bstep (se 1 (by rfl) ⟨1673219, by rfl⟩ : syracuseStep 2230959 = 3346439) B3346439
theorem B3346445 : Blo 2229435 3346445 := bbase (se 3 (by rfl) ⟨627458, by rfl⟩ : syracuseStep 3346445 = 1254917) (by norm_num)
theorem B2230963 : Blo 2229435 2230963 := bstep (se 1 (by rfl) ⟨1673222, by rfl⟩ : syracuseStep 2230963 = 3346445) B3346445
theorem B5019677 : Blo 2229435 5019677 := bbase (se 3 (by rfl) ⟨941189, by rfl⟩ : syracuseStep 5019677 = 1882379) (by norm_num)
theorem B3346451 : Blo 2229435 3346451 := bstep (se 1 (by rfl) ⟨2509838, by rfl⟩ : syracuseStep 3346451 = 5019677) B5019677
theorem B2230967 : Blo 2229435 2230967 := bstep (se 1 (by rfl) ⟨1673225, by rfl⟩ : syracuseStep 2230967 = 3346451) B3346451
theorem B3764765 : Blo 2229435 3764765 := bbase (se 3 (by rfl) ⟨705893, by rfl⟩ : syracuseStep 3764765 = 1411787) (by norm_num)
theorem B2509843 : Blo 2229435 2509843 := bstep (se 1 (by rfl) ⟨1882382, by rfl⟩ : syracuseStep 2509843 = 3764765) B3764765
theorem B3346457 : Blo 2229435 3346457 := bstep (se 2 (by rfl) ⟨1254921, by rfl⟩ : syracuseStep 3346457 = 2509843) B2509843
theorem B2230971 : Blo 2229435 2230971 := bstep (se 1 (by rfl) ⟨1673228, by rfl⟩ : syracuseStep 2230971 = 3346457) B3346457
theorem B6439733 : Blo 2229435 6439733 := bbase (se 5 (by rfl) ⟨301862, by rfl⟩ : syracuseStep 6439733 = 603725) (by norm_num)
theorem B4293155 : Blo 2229435 4293155 := bstep (se 1 (by rfl) ⟨3219866, by rfl⟩ : syracuseStep 4293155 = 6439733) B6439733
theorem B2862103 : Blo 2229435 2862103 := bstep (se 1 (by rfl) ⟨2146577, by rfl⟩ : syracuseStep 2862103 = 4293155) B4293155
theorem B3816137 : Blo 2229435 3816137 := bstep (se 2 (by rfl) ⟨1431051, by rfl⟩ : syracuseStep 3816137 = 2862103) B2862103
theorem B2544091 : Blo 2229435 2544091 := bstep (se 1 (by rfl) ⟨1908068, by rfl⟩ : syracuseStep 2544091 = 3816137) B3816137
theorem B13568485 : Blo 2229435 13568485 := bstep (se 4 (by rfl) ⟨1272045, by rfl⟩ : syracuseStep 13568485 = 2544091) B2544091
theorem B18091313 : Blo 2229435 18091313 := bstep (se 2 (by rfl) ⟨6784242, by rfl⟩ : syracuseStep 18091313 = 13568485) B13568485
theorem B12060875 : Blo 2229435 12060875 := bstep (se 1 (by rfl) ⟨9045656, by rfl⟩ : syracuseStep 12060875 = 18091313) B18091313
theorem B8040583 : Blo 2229435 8040583 := bstep (se 1 (by rfl) ⟨6030437, by rfl⟩ : syracuseStep 8040583 = 12060875) B12060875
theorem B10720777 : Blo 2229435 10720777 := bstep (se 2 (by rfl) ⟨4020291, by rfl⟩ : syracuseStep 10720777 = 8040583) B8040583
theorem B14294369 : Blo 2229435 14294369 := bstep (se 2 (by rfl) ⟨5360388, by rfl⟩ : syracuseStep 14294369 = 10720777) B10720777
theorem B9529579 : Blo 2229435 9529579 := bstep (se 1 (by rfl) ⟨7147184, by rfl⟩ : syracuseStep 9529579 = 14294369) B14294369
theorem B12706105 : Blo 2229435 12706105 := bstep (se 2 (by rfl) ⟨4764789, by rfl⟩ : syracuseStep 12706105 = 9529579) B9529579
theorem B16941473 : Blo 2229435 16941473 := bstep (se 2 (by rfl) ⟨6353052, by rfl⟩ : syracuseStep 16941473 = 12706105) B12706105
theorem B11294315 : Blo 2229435 11294315 := bstep (se 1 (by rfl) ⟨8470736, by rfl⟩ : syracuseStep 11294315 = 16941473) B16941473
theorem B7529543 : Blo 2229435 7529543 := bstep (se 1 (by rfl) ⟨5647157, by rfl⟩ : syracuseStep 7529543 = 11294315) B11294315
theorem B5019695 : Blo 2229435 5019695 := bstep (se 1 (by rfl) ⟨3764771, by rfl⟩ : syracuseStep 5019695 = 7529543) B7529543
theorem B3346463 : Blo 2229435 3346463 := bstep (se 1 (by rfl) ⟨2509847, by rfl⟩ : syracuseStep 3346463 = 5019695) B5019695
theorem B2230975 : Blo 2229435 2230975 := bstep (se 1 (by rfl) ⟨1673231, by rfl⟩ : syracuseStep 2230975 = 3346463) B3346463
theorem B3346469 : Blo 2229435 3346469 := bbase (se 4 (by rfl) ⟨313731, by rfl⟩ : syracuseStep 3346469 = 627463) (by norm_num)
theorem B2230979 : Blo 2229435 2230979 := bstep (se 1 (by rfl) ⟨1673234, by rfl⟩ : syracuseStep 2230979 = 3346469) B3346469
theorem B2823589 : Blo 2229435 2823589 := bbase (se 4 (by rfl) ⟨264711, by rfl⟩ : syracuseStep 2823589 = 529423) (by norm_num)
theorem B3764785 : Blo 2229435 3764785 := bstep (se 2 (by rfl) ⟨1411794, by rfl⟩ : syracuseStep 3764785 = 2823589) B2823589
theorem B5019713 : Blo 2229435 5019713 := bstep (se 2 (by rfl) ⟨1882392, by rfl⟩ : syracuseStep 5019713 = 3764785) B3764785
theorem B3346475 : Blo 2229435 3346475 := bstep (se 1 (by rfl) ⟨2509856, by rfl⟩ : syracuseStep 3346475 = 5019713) B5019713
theorem B2230983 : Blo 2229435 2230983 := bstep (se 1 (by rfl) ⟨1673237, by rfl⟩ : syracuseStep 2230983 = 3346475) B3346475
theorem B2509861 : Blo 2229435 2509861 := bbase (se 4 (by rfl) ⟨235299, by rfl⟩ : syracuseStep 2509861 = 470599) (by norm_num)
theorem B3346481 : Blo 2229435 3346481 := bstep (se 2 (by rfl) ⟨1254930, by rfl⟩ : syracuseStep 3346481 = 2509861) B2509861
theorem B2230987 : Blo 2229435 2230987 := bstep (se 1 (by rfl) ⟨1673240, by rfl⟩ : syracuseStep 2230987 = 3346481) B3346481
theorem B7147237 : Blo 2229435 7147237 := bbase (se 4 (by rfl) ⟨670053, by rfl⟩ : syracuseStep 7147237 = 1340107) (by norm_num)
theorem B9529649 : Blo 2229435 9529649 := bstep (se 2 (by rfl) ⟨3573618, by rfl⟩ : syracuseStep 9529649 = 7147237) B7147237
theorem B6353099 : Blo 2229435 6353099 := bstep (se 1 (by rfl) ⟨4764824, by rfl⟩ : syracuseStep 6353099 = 9529649) B9529649
theorem B4235399 : Blo 2229435 4235399 := bstep (se 1 (by rfl) ⟨3176549, by rfl⟩ : syracuseStep 4235399 = 6353099) B6353099
theorem B2823599 : Blo 2229435 2823599 := bstep (se 1 (by rfl) ⟨2117699, by rfl⟩ : syracuseStep 2823599 = 4235399) B4235399
theorem B7529597 : Blo 2229435 7529597 := bstep (se 3 (by rfl) ⟨1411799, by rfl⟩ : syracuseStep 7529597 = 2823599) B2823599
theorem B5019731 : Blo 2229435 5019731 := bstep (se 1 (by rfl) ⟨3764798, by rfl⟩ : syracuseStep 5019731 = 7529597) B7529597
theorem B3346487 : Blo 2229435 3346487 := bstep (se 1 (by rfl) ⟨2509865, by rfl⟩ : syracuseStep 3346487 = 5019731) B5019731
theorem B2230991 : Blo 2229435 2230991 := bstep (se 1 (by rfl) ⟨1673243, by rfl⟩ : syracuseStep 2230991 = 3346487) B3346487
theorem B3346493 : Blo 2229435 3346493 := bbase (se 3 (by rfl) ⟨627467, by rfl⟩ : syracuseStep 3346493 = 1254935) (by norm_num)
theorem B2230995 : Blo 2229435 2230995 := bstep (se 1 (by rfl) ⟨1673246, by rfl⟩ : syracuseStep 2230995 = 3346493) B3346493
theorem B5019749 : Blo 2229435 5019749 := bbase (se 4 (by rfl) ⟨470601, by rfl⟩ : syracuseStep 5019749 = 941203) (by norm_num)
theorem B3346499 : Blo 2229435 3346499 := bstep (se 1 (by rfl) ⟨2509874, by rfl⟩ : syracuseStep 3346499 = 5019749) B5019749
theorem B2230999 : Blo 2229435 2230999 := bstep (se 1 (by rfl) ⟨1673249, by rfl⟩ : syracuseStep 2230999 = 3346499) B3346499
theorem B5647229 : Blo 2229435 5647229 := bbase (se 3 (by rfl) ⟨1058855, by rfl⟩ : syracuseStep 5647229 = 2117711) (by norm_num)
theorem B3764819 : Blo 2229435 3764819 := bstep (se 1 (by rfl) ⟨2823614, by rfl⟩ : syracuseStep 3764819 = 5647229) B5647229
theorem B2509879 : Blo 2229435 2509879 := bstep (se 1 (by rfl) ⟨1882409, by rfl⟩ : syracuseStep 2509879 = 3764819) B3764819
theorem B3346505 : Blo 2229435 3346505 := bstep (se 2 (by rfl) ⟨1254939, by rfl⟩ : syracuseStep 3346505 = 2509879) B2509879
theorem B2231003 : Blo 2229435 2231003 := bstep (se 1 (by rfl) ⟨1673252, by rfl⟩ : syracuseStep 2231003 = 3346505) B3346505
theorem B4235429 : Blo 2229435 4235429 := bbase (se 4 (by rfl) ⟨397071, by rfl⟩ : syracuseStep 4235429 = 794143) (by norm_num)
theorem B11294477 : Blo 2229435 11294477 := bstep (se 3 (by rfl) ⟨2117714, by rfl⟩ : syracuseStep 11294477 = 4235429) B4235429
theorem B7529651 : Blo 2229435 7529651 := bstep (se 1 (by rfl) ⟨5647238, by rfl⟩ : syracuseStep 7529651 = 11294477) B11294477
theorem B5019767 : Blo 2229435 5019767 := bstep (se 1 (by rfl) ⟨3764825, by rfl⟩ : syracuseStep 5019767 = 7529651) B7529651
theorem B3346511 : Blo 2229435 3346511 := bstep (se 1 (by rfl) ⟨2509883, by rfl⟩ : syracuseStep 3346511 = 5019767) B5019767
theorem B2231007 : Blo 2229435 2231007 := bstep (se 1 (by rfl) ⟨1673255, by rfl⟩ : syracuseStep 2231007 = 3346511) B3346511
theorem B3346517 : Blo 2229435 3346517 := bbase (se 8 (by rfl) ⟨19608, by rfl⟩ : syracuseStep 3346517 = 39217) (by norm_num)
theorem B2231011 : Blo 2229435 2231011 := bstep (se 1 (by rfl) ⟨1673258, by rfl⟩ : syracuseStep 2231011 = 3346517) B3346517
theorem B21441941 : Blo 2229435 21441941 := bbase (se 6 (by rfl) ⟨502545, by rfl⟩ : syracuseStep 21441941 = 1005091) (by norm_num)
theorem B14294627 : Blo 2229435 14294627 := bstep (se 1 (by rfl) ⟨10720970, by rfl⟩ : syracuseStep 14294627 = 21441941) B21441941
theorem B9529751 : Blo 2229435 9529751 := bstep (se 1 (by rfl) ⟨7147313, by rfl⟩ : syracuseStep 9529751 = 14294627) B14294627
theorem B6353167 : Blo 2229435 6353167 := bstep (se 1 (by rfl) ⟨4764875, by rfl⟩ : syracuseStep 6353167 = 9529751) B9529751
theorem B8470889 : Blo 2229435 8470889 := bstep (se 2 (by rfl) ⟨3176583, by rfl⟩ : syracuseStep 8470889 = 6353167) B6353167
theorem B5647259 : Blo 2229435 5647259 := bstep (se 1 (by rfl) ⟨4235444, by rfl⟩ : syracuseStep 5647259 = 8470889) B8470889
theorem B3764839 : Blo 2229435 3764839 := bstep (se 1 (by rfl) ⟨2823629, by rfl⟩ : syracuseStep 3764839 = 5647259) B5647259
theorem B5019785 : Blo 2229435 5019785 := bstep (se 2 (by rfl) ⟨1882419, by rfl⟩ : syracuseStep 5019785 = 3764839) B3764839
theorem B3346523 : Blo 2229435 3346523 := bstep (se 1 (by rfl) ⟨2509892, by rfl⟩ : syracuseStep 3346523 = 5019785) B5019785
theorem B2231015 : Blo 2229435 2231015 := bstep (se 1 (by rfl) ⟨1673261, by rfl⟩ : syracuseStep 2231015 = 3346523) B3346523
theorem B2509897 : Blo 2229435 2509897 := bbase (se 2 (by rfl) ⟨941211, by rfl⟩ : syracuseStep 2509897 = 1882423) (by norm_num)
theorem B3346529 : Blo 2229435 3346529 := bstep (se 2 (by rfl) ⟨1254948, by rfl⟩ : syracuseStep 3346529 = 2509897) B2509897
theorem B2231019 : Blo 2229435 2231019 := bstep (se 1 (by rfl) ⟨1673264, by rfl⟩ : syracuseStep 2231019 = 3346529) B3346529
theorem B14294677 : Blo 2229435 14294677 := bbase (se 6 (by rfl) ⟨335031, by rfl⟩ : syracuseStep 14294677 = 670063) (by norm_num)
theorem B19059569 : Blo 2229435 19059569 := bstep (se 2 (by rfl) ⟨7147338, by rfl⟩ : syracuseStep 19059569 = 14294677) B14294677
theorem B12706379 : Blo 2229435 12706379 := bstep (se 1 (by rfl) ⟨9529784, by rfl⟩ : syracuseStep 12706379 = 19059569) B19059569
theorem B8470919 : Blo 2229435 8470919 := bstep (se 1 (by rfl) ⟨6353189, by rfl⟩ : syracuseStep 8470919 = 12706379) B12706379
theorem B5647279 : Blo 2229435 5647279 := bstep (se 1 (by rfl) ⟨4235459, by rfl⟩ : syracuseStep 5647279 = 8470919) B8470919
theorem B7529705 : Blo 2229435 7529705 := bstep (se 2 (by rfl) ⟨2823639, by rfl⟩ : syracuseStep 7529705 = 5647279) B5647279
theorem B5019803 : Blo 2229435 5019803 := bstep (se 1 (by rfl) ⟨3764852, by rfl⟩ : syracuseStep 5019803 = 7529705) B7529705
theorem B3346535 : Blo 2229435 3346535 := bstep (se 1 (by rfl) ⟨2509901, by rfl⟩ : syracuseStep 3346535 = 5019803) B5019803
theorem B2231023 : Blo 2229435 2231023 := bstep (se 1 (by rfl) ⟨1673267, by rfl⟩ : syracuseStep 2231023 = 3346535) B3346535
theorem B3346541 : Blo 2229435 3346541 := bbase (se 3 (by rfl) ⟨627476, by rfl⟩ : syracuseStep 3346541 = 1254953) (by norm_num)
theorem B2231027 : Blo 2229435 2231027 := bstep (se 1 (by rfl) ⟨1673270, by rfl⟩ : syracuseStep 2231027 = 3346541) B3346541
theorem B5019821 : Blo 2229435 5019821 := bbase (se 3 (by rfl) ⟨941216, by rfl⟩ : syracuseStep 5019821 = 1882433) (by norm_num)
theorem B3346547 : Blo 2229435 3346547 := bstep (se 1 (by rfl) ⟨2509910, by rfl⟩ : syracuseStep 3346547 = 5019821) B5019821
theorem B2231031 : Blo 2229435 2231031 := bstep (se 1 (by rfl) ⟨1673273, by rfl⟩ : syracuseStep 2231031 = 3346547) B3346547
theorem B3015301 : Blo 2229435 3015301 := bbase (se 4 (by rfl) ⟨282684, by rfl⟩ : syracuseStep 3015301 = 565369) (by norm_num)
theorem B4020401 : Blo 2229435 4020401 := bstep (se 2 (by rfl) ⟨1507650, by rfl⟩ : syracuseStep 4020401 = 3015301) B3015301
theorem B10721069 : Blo 2229435 10721069 := bstep (se 3 (by rfl) ⟨2010200, by rfl⟩ : syracuseStep 10721069 = 4020401) B4020401
theorem B7147379 : Blo 2229435 7147379 := bstep (se 1 (by rfl) ⟨5360534, by rfl⟩ : syracuseStep 7147379 = 10721069) B10721069
theorem B4764919 : Blo 2229435 4764919 := bstep (se 1 (by rfl) ⟨3573689, by rfl⟩ : syracuseStep 4764919 = 7147379) B7147379
theorem B6353225 : Blo 2229435 6353225 := bstep (se 2 (by rfl) ⟨2382459, by rfl⟩ : syracuseStep 6353225 = 4764919) B4764919
theorem B4235483 : Blo 2229435 4235483 := bstep (se 1 (by rfl) ⟨3176612, by rfl⟩ : syracuseStep 4235483 = 6353225) B6353225
theorem B2823655 : Blo 2229435 2823655 := bstep (se 1 (by rfl) ⟨2117741, by rfl⟩ : syracuseStep 2823655 = 4235483) B4235483
theorem B3764873 : Blo 2229435 3764873 := bstep (se 2 (by rfl) ⟨1411827, by rfl⟩ : syracuseStep 3764873 = 2823655) B2823655
theorem B2509915 : Blo 2229435 2509915 := bstep (se 1 (by rfl) ⟨1882436, by rfl⟩ : syracuseStep 2509915 = 3764873) B3764873
theorem B3346553 : Blo 2229435 3346553 := bstep (se 2 (by rfl) ⟨1254957, by rfl⟩ : syracuseStep 3346553 = 2509915) B2509915
theorem B2231035 : Blo 2229435 2231035 := bstep (se 1 (by rfl) ⟨1673276, by rfl⟩ : syracuseStep 2231035 = 3346553) B3346553
theorem B2716841 : Blo 2229435 2716841 := bbase (se 2 (by rfl) ⟨1018815, by rfl⟩ : syracuseStep 2716841 = 2037631) (by norm_num)
theorem B7244909 : Blo 2229435 7244909 := bstep (se 3 (by rfl) ⟨1358420, by rfl⟩ : syracuseStep 7244909 = 2716841) B2716841
theorem B4829939 : Blo 2229435 4829939 := bstep (se 1 (by rfl) ⟨3622454, by rfl⟩ : syracuseStep 4829939 = 7244909) B7244909
theorem B3219959 : Blo 2229435 3219959 := bstep (se 1 (by rfl) ⟨2414969, by rfl⟩ : syracuseStep 3219959 = 4829939) B4829939
theorem B8586557 : Blo 2229435 8586557 := bstep (se 3 (by rfl) ⟨1609979, by rfl⟩ : syracuseStep 8586557 = 3219959) B3219959
theorem B5724371 : Blo 2229435 5724371 := bstep (se 1 (by rfl) ⟨4293278, by rfl⟩ : syracuseStep 5724371 = 8586557) B8586557
theorem B3816247 : Blo 2229435 3816247 := bstep (se 1 (by rfl) ⟨2862185, by rfl⟩ : syracuseStep 3816247 = 5724371) B5724371
theorem B5088329 : Blo 2229435 5088329 := bstep (se 2 (by rfl) ⟨1908123, by rfl⟩ : syracuseStep 5088329 = 3816247) B3816247
theorem B3392219 : Blo 2229435 3392219 := bstep (se 1 (by rfl) ⟨2544164, by rfl⟩ : syracuseStep 3392219 = 5088329) B5088329
theorem B9045917 : Blo 2229435 9045917 := bstep (se 3 (by rfl) ⟨1696109, by rfl⟩ : syracuseStep 9045917 = 3392219) B3392219
theorem B6030611 : Blo 2229435 6030611 := bstep (se 1 (by rfl) ⟨4522958, by rfl⟩ : syracuseStep 6030611 = 9045917) B9045917
theorem B4020407 : Blo 2229435 4020407 := bstep (se 1 (by rfl) ⟨3015305, by rfl⟩ : syracuseStep 4020407 = 6030611) B6030611
theorem B2680271 : Blo 2229435 2680271 := bstep (se 1 (by rfl) ⟨2010203, by rfl⟩ : syracuseStep 2680271 = 4020407) B4020407
theorem B28589557 : Blo 2229435 28589557 := bstep (se 5 (by rfl) ⟨1340135, by rfl⟩ : syracuseStep 28589557 = 2680271) B2680271
theorem B38119409 : Blo 2229435 38119409 := bstep (se 2 (by rfl) ⟨14294778, by rfl⟩ : syracuseStep 38119409 = 28589557) B28589557
theorem B25412939 : Blo 2229435 25412939 := bstep (se 1 (by rfl) ⟨19059704, by rfl⟩ : syracuseStep 25412939 = 38119409) B38119409
theorem B16941959 : Blo 2229435 16941959 := bstep (se 1 (by rfl) ⟨12706469, by rfl⟩ : syracuseStep 16941959 = 25412939) B25412939
theorem B11294639 : Blo 2229435 11294639 := bstep (se 1 (by rfl) ⟨8470979, by rfl⟩ : syracuseStep 11294639 = 16941959) B16941959
theorem B7529759 : Blo 2229435 7529759 := bstep (se 1 (by rfl) ⟨5647319, by rfl⟩ : syracuseStep 7529759 = 11294639) B11294639
theorem B5019839 : Blo 2229435 5019839 := bstep (se 1 (by rfl) ⟨3764879, by rfl⟩ : syracuseStep 5019839 = 7529759) B7529759
theorem B3346559 : Blo 2229435 3346559 := bstep (se 1 (by rfl) ⟨2509919, by rfl⟩ : syracuseStep 3346559 = 5019839) B5019839
theorem B2231039 : Blo 2229435 2231039 := bstep (se 1 (by rfl) ⟨1673279, by rfl⟩ : syracuseStep 2231039 = 3346559) B3346559
theorem B3346565 : Blo 2229435 3346565 := bbase (se 4 (by rfl) ⟨313740, by rfl⟩ : syracuseStep 3346565 = 627481) (by norm_num)
theorem B2231043 : Blo 2229435 2231043 := bstep (se 1 (by rfl) ⟨1673282, by rfl⟩ : syracuseStep 2231043 = 3346565) B3346565
theorem B3764893 : Blo 2229435 3764893 := bbase (se 3 (by rfl) ⟨705917, by rfl⟩ : syracuseStep 3764893 = 1411835) (by norm_num)
theorem B5019857 : Blo 2229435 5019857 := bstep (se 2 (by rfl) ⟨1882446, by rfl⟩ : syracuseStep 5019857 = 3764893) B3764893
theorem B3346571 : Blo 2229435 3346571 := bstep (se 1 (by rfl) ⟨2509928, by rfl⟩ : syracuseStep 3346571 = 5019857) B5019857
theorem B2231047 : Blo 2229435 2231047 := bstep (se 1 (by rfl) ⟨1673285, by rfl⟩ : syracuseStep 2231047 = 3346571) B3346571
theorem B2509933 : Blo 2229435 2509933 := bbase (se 3 (by rfl) ⟨470612, by rfl⟩ : syracuseStep 2509933 = 941225) (by norm_num)
theorem B3346577 : Blo 2229435 3346577 := bstep (se 2 (by rfl) ⟨1254966, by rfl⟩ : syracuseStep 3346577 = 2509933) B2509933
theorem B2231051 : Blo 2229435 2231051 := bstep (se 1 (by rfl) ⟨1673288, by rfl⟩ : syracuseStep 2231051 = 3346577) B3346577
theorem B7529813 : Blo 2229435 7529813 := bbase (se 12 (by rfl) ⟨2757, by rfl⟩ : syracuseStep 7529813 = 5515) (by norm_num)
theorem B5019875 : Blo 2229435 5019875 := bstep (se 1 (by rfl) ⟨3764906, by rfl⟩ : syracuseStep 5019875 = 7529813) B7529813
theorem B3346583 : Blo 2229435 3346583 := bstep (se 1 (by rfl) ⟨2509937, by rfl⟩ : syracuseStep 3346583 = 5019875) B5019875
theorem B2231055 : Blo 2229435 2231055 := bstep (se 1 (by rfl) ⟨1673291, by rfl⟩ : syracuseStep 2231055 = 3346583) B3346583
theorem B3346589 : Blo 2229435 3346589 := bbase (se 3 (by rfl) ⟨627485, by rfl⟩ : syracuseStep 3346589 = 1254971) (by norm_num)
theorem B2231059 : Blo 2229435 2231059 := bstep (se 1 (by rfl) ⟨1673294, by rfl⟩ : syracuseStep 2231059 = 3346589) B3346589
theorem B5019893 : Blo 2229435 5019893 := bbase (se 5 (by rfl) ⟨235307, by rfl⟩ : syracuseStep 5019893 = 470615) (by norm_num)
theorem B3346595 : Blo 2229435 3346595 := bstep (se 1 (by rfl) ⟨2509946, by rfl⟩ : syracuseStep 3346595 = 5019893) B5019893
theorem B2231063 : Blo 2229435 2231063 := bstep (se 1 (by rfl) ⟨1673297, by rfl⟩ : syracuseStep 2231063 = 3346595) B3346595
theorem B5433749 : Blo 2229435 5433749 := bbase (se 6 (by rfl) ⟨127353, by rfl⟩ : syracuseStep 5433749 = 254707) (by norm_num)
theorem B3622499 : Blo 2229435 3622499 := bstep (se 1 (by rfl) ⟨2716874, by rfl⟩ : syracuseStep 3622499 = 5433749) B5433749
theorem B2414999 : Blo 2229435 2414999 := bstep (se 1 (by rfl) ⟨1811249, by rfl⟩ : syracuseStep 2414999 = 3622499) B3622499
theorem B6439997 : Blo 2229435 6439997 := bstep (se 3 (by rfl) ⟨1207499, by rfl⟩ : syracuseStep 6439997 = 2414999) B2414999
theorem B4293331 : Blo 2229435 4293331 := bstep (se 1 (by rfl) ⟨3219998, by rfl⟩ : syracuseStep 4293331 = 6439997) B6439997
theorem B22897765 : Blo 2229435 22897765 := bstep (se 4 (by rfl) ⟨2146665, by rfl⟩ : syracuseStep 22897765 = 4293331) B4293331
theorem B30530353 : Blo 2229435 30530353 := bstep (se 2 (by rfl) ⟨11448882, by rfl⟩ : syracuseStep 30530353 = 22897765) B22897765
theorem B40707137 : Blo 2229435 40707137 := bstep (se 2 (by rfl) ⟨15265176, by rfl⟩ : syracuseStep 40707137 = 30530353) B30530353
theorem B27138091 : Blo 2229435 27138091 := bstep (se 1 (by rfl) ⟨20353568, by rfl⟩ : syracuseStep 27138091 = 40707137) B40707137
theorem B36184121 : Blo 2229435 36184121 := bstep (se 2 (by rfl) ⟨13569045, by rfl⟩ : syracuseStep 36184121 = 27138091) B27138091
theorem B24122747 : Blo 2229435 24122747 := bstep (se 1 (by rfl) ⟨18092060, by rfl⟩ : syracuseStep 24122747 = 36184121) B36184121
theorem B16081831 : Blo 2229435 16081831 := bstep (se 1 (by rfl) ⟨12061373, by rfl⟩ : syracuseStep 16081831 = 24122747) B24122747
theorem B21442441 : Blo 2229435 21442441 := bstep (se 2 (by rfl) ⟨8040915, by rfl⟩ : syracuseStep 21442441 = 16081831) B16081831
theorem B28589921 : Blo 2229435 28589921 := bstep (se 2 (by rfl) ⟨10721220, by rfl⟩ : syracuseStep 28589921 = 21442441) B21442441
theorem B19059947 : Blo 2229435 19059947 := bstep (se 1 (by rfl) ⟨14294960, by rfl⟩ : syracuseStep 19059947 = 28589921) B28589921
theorem B12706631 : Blo 2229435 12706631 := bstep (se 1 (by rfl) ⟨9529973, by rfl⟩ : syracuseStep 12706631 = 19059947) B19059947
theorem B8471087 : Blo 2229435 8471087 := bstep (se 1 (by rfl) ⟨6353315, by rfl⟩ : syracuseStep 8471087 = 12706631) B12706631
theorem B5647391 : Blo 2229435 5647391 := bstep (se 1 (by rfl) ⟨4235543, by rfl⟩ : syracuseStep 5647391 = 8471087) B8471087
theorem B3764927 : Blo 2229435 3764927 := bstep (se 1 (by rfl) ⟨2823695, by rfl⟩ : syracuseStep 3764927 = 5647391) B5647391
theorem B2509951 : Blo 2229435 2509951 := bstep (se 1 (by rfl) ⟨1882463, by rfl⟩ : syracuseStep 2509951 = 3764927) B3764927
theorem B3346601 : Blo 2229435 3346601 := bstep (se 2 (by rfl) ⟨1254975, by rfl⟩ : syracuseStep 3346601 = 2509951) B2509951
theorem B2231067 : Blo 2229435 2231067 := bstep (se 1 (by rfl) ⟨1673300, by rfl⟩ : syracuseStep 2231067 = 3346601) B3346601
theorem B7147493 : Blo 2229435 7147493 := bbase (se 4 (by rfl) ⟨670077, by rfl⟩ : syracuseStep 7147493 = 1340155) (by norm_num)
theorem B4764995 : Blo 2229435 4764995 := bstep (se 1 (by rfl) ⟨3573746, by rfl⟩ : syracuseStep 4764995 = 7147493) B7147493
theorem B3176663 : Blo 2229435 3176663 := bstep (se 1 (by rfl) ⟨2382497, by rfl⟩ : syracuseStep 3176663 = 4764995) B4764995
theorem B8471101 : Blo 2229435 8471101 := bstep (se 3 (by rfl) ⟨1588331, by rfl⟩ : syracuseStep 8471101 = 3176663) B3176663
theorem B11294801 : Blo 2229435 11294801 := bstep (se 2 (by rfl) ⟨4235550, by rfl⟩ : syracuseStep 11294801 = 8471101) B8471101
theorem B7529867 : Blo 2229435 7529867 := bstep (se 1 (by rfl) ⟨5647400, by rfl⟩ : syracuseStep 7529867 = 11294801) B11294801
theorem B5019911 : Blo 2229435 5019911 := bstep (se 1 (by rfl) ⟨3764933, by rfl⟩ : syracuseStep 5019911 = 7529867) B7529867
theorem B3346607 : Blo 2229435 3346607 := bstep (se 1 (by rfl) ⟨2509955, by rfl⟩ : syracuseStep 3346607 = 5019911) B5019911
theorem B2231071 : Blo 2229435 2231071 := bstep (se 1 (by rfl) ⟨1673303, by rfl⟩ : syracuseStep 2231071 = 3346607) B3346607
theorem B3346613 : Blo 2229435 3346613 := bbase (se 5 (by rfl) ⟨156872, by rfl⟩ : syracuseStep 3346613 = 313745) (by norm_num)
theorem B2231075 : Blo 2229435 2231075 := bstep (se 1 (by rfl) ⟨1673306, by rfl⟩ : syracuseStep 2231075 = 3346613) B3346613
theorem B5647421 : Blo 2229435 5647421 := bbase (se 3 (by rfl) ⟨1058891, by rfl⟩ : syracuseStep 5647421 = 2117783) (by norm_num)
theorem B3764947 : Blo 2229435 3764947 := bstep (se 1 (by rfl) ⟨2823710, by rfl⟩ : syracuseStep 3764947 = 5647421) B5647421
theorem B5019929 : Blo 2229435 5019929 := bstep (se 2 (by rfl) ⟨1882473, by rfl⟩ : syracuseStep 5019929 = 3764947) B3764947
theorem B3346619 : Blo 2229435 3346619 := bstep (se 1 (by rfl) ⟨2509964, by rfl⟩ : syracuseStep 3346619 = 5019929) B5019929
theorem B2231079 : Blo 2229435 2231079 := bstep (se 1 (by rfl) ⟨1673309, by rfl⟩ : syracuseStep 2231079 = 3346619) B3346619
theorem B2509969 : Blo 2229435 2509969 := bbase (se 2 (by rfl) ⟨941238, by rfl⟩ : syracuseStep 2509969 = 1882477) (by norm_num)
theorem B3346625 : Blo 2229435 3346625 := bstep (se 2 (by rfl) ⟨1254984, by rfl⟩ : syracuseStep 3346625 = 2509969) B2509969
theorem B2231083 : Blo 2229435 2231083 := bstep (se 1 (by rfl) ⟨1673312, by rfl⟩ : syracuseStep 2231083 = 3346625) B3346625
theorem B4235581 : Blo 2229435 4235581 := bbase (se 3 (by rfl) ⟨794171, by rfl⟩ : syracuseStep 4235581 = 1588343) (by norm_num)
theorem B5647441 : Blo 2229435 5647441 := bstep (se 2 (by rfl) ⟨2117790, by rfl⟩ : syracuseStep 5647441 = 4235581) B4235581
theorem B7529921 : Blo 2229435 7529921 := bstep (se 2 (by rfl) ⟨2823720, by rfl⟩ : syracuseStep 7529921 = 5647441) B5647441
theorem B5019947 : Blo 2229435 5019947 := bstep (se 1 (by rfl) ⟨3764960, by rfl⟩ : syracuseStep 5019947 = 7529921) B7529921
theorem B3346631 : Blo 2229435 3346631 := bstep (se 1 (by rfl) ⟨2509973, by rfl⟩ : syracuseStep 3346631 = 5019947) B5019947
theorem B2231087 : Blo 2229435 2231087 := bstep (se 1 (by rfl) ⟨1673315, by rfl⟩ : syracuseStep 2231087 = 3346631) B3346631
theorem B3346637 : Blo 2229435 3346637 := bbase (se 3 (by rfl) ⟨627494, by rfl⟩ : syracuseStep 3346637 = 1254989) (by norm_num)
theorem B2231091 : Blo 2229435 2231091 := bstep (se 1 (by rfl) ⟨1673318, by rfl⟩ : syracuseStep 2231091 = 3346637) B3346637
theorem B5019965 : Blo 2229435 5019965 := bbase (se 3 (by rfl) ⟨941243, by rfl⟩ : syracuseStep 5019965 = 1882487) (by norm_num)
theorem B3346643 : Blo 2229435 3346643 := bstep (se 1 (by rfl) ⟨2509982, by rfl⟩ : syracuseStep 3346643 = 5019965) B5019965
theorem B2231095 : Blo 2229435 2231095 := bstep (se 1 (by rfl) ⟨1673321, by rfl⟩ : syracuseStep 2231095 = 3346643) B3346643
theorem B3764981 : Blo 2229435 3764981 := bbase (se 5 (by rfl) ⟨176483, by rfl⟩ : syracuseStep 3764981 = 352967) (by norm_num)
theorem B2509987 : Blo 2229435 2509987 := bstep (se 1 (by rfl) ⟨1882490, by rfl⟩ : syracuseStep 2509987 = 3764981) B3764981
theorem B3346649 : Blo 2229435 3346649 := bstep (se 2 (by rfl) ⟨1254993, by rfl⟩ : syracuseStep 3346649 = 2509987) B2509987
theorem B2231099 : Blo 2229435 2231099 := bstep (se 1 (by rfl) ⟨1673324, by rfl⟩ : syracuseStep 2231099 = 3346649) B3346649
theorem B8041045 : Blo 2229435 8041045 := bbase (se 8 (by rfl) ⟨47115, by rfl⟩ : syracuseStep 8041045 = 94231) (by norm_num)
theorem B10721393 : Blo 2229435 10721393 := bstep (se 2 (by rfl) ⟨4020522, by rfl⟩ : syracuseStep 10721393 = 8041045) B8041045
theorem B7147595 : Blo 2229435 7147595 := bstep (se 1 (by rfl) ⟨5360696, by rfl⟩ : syracuseStep 7147595 = 10721393) B10721393
theorem B4765063 : Blo 2229435 4765063 := bstep (se 1 (by rfl) ⟨3573797, by rfl⟩ : syracuseStep 4765063 = 7147595) B7147595
theorem B6353417 : Blo 2229435 6353417 := bstep (se 2 (by rfl) ⟨2382531, by rfl⟩ : syracuseStep 6353417 = 4765063) B4765063
theorem B16942445 : Blo 2229435 16942445 := bstep (se 3 (by rfl) ⟨3176708, by rfl⟩ : syracuseStep 16942445 = 6353417) B6353417
theorem B11294963 : Blo 2229435 11294963 := bstep (se 1 (by rfl) ⟨8471222, by rfl⟩ : syracuseStep 11294963 = 16942445) B16942445
theorem B7529975 : Blo 2229435 7529975 := bstep (se 1 (by rfl) ⟨5647481, by rfl⟩ : syracuseStep 7529975 = 11294963) B11294963
theorem B5019983 : Blo 2229435 5019983 := bstep (se 1 (by rfl) ⟨3764987, by rfl⟩ : syracuseStep 5019983 = 7529975) B7529975
theorem B3346655 : Blo 2229435 3346655 := bstep (se 1 (by rfl) ⟨2509991, by rfl⟩ : syracuseStep 3346655 = 5019983) B5019983
theorem B2231103 : Blo 2229435 2231103 := bstep (se 1 (by rfl) ⟨1673327, by rfl⟩ : syracuseStep 2231103 = 3346655) B3346655
theorem B3346661 : Blo 2229435 3346661 := bbase (se 4 (by rfl) ⟨313749, by rfl⟩ : syracuseStep 3346661 = 627499) (by norm_num)
theorem B2231107 : Blo 2229435 2231107 := bstep (se 1 (by rfl) ⟨1673330, by rfl⟩ : syracuseStep 2231107 = 3346661) B3346661
theorem B5360717 : Blo 2229435 5360717 := bbase (se 3 (by rfl) ⟨1005134, by rfl⟩ : syracuseStep 5360717 = 2010269) (by norm_num)
theorem B3573811 : Blo 2229435 3573811 := bstep (se 1 (by rfl) ⟨2680358, by rfl⟩ : syracuseStep 3573811 = 5360717) B5360717
theorem B4765081 : Blo 2229435 4765081 := bstep (se 2 (by rfl) ⟨1786905, by rfl⟩ : syracuseStep 4765081 = 3573811) B3573811
theorem B6353441 : Blo 2229435 6353441 := bstep (se 2 (by rfl) ⟨2382540, by rfl⟩ : syracuseStep 6353441 = 4765081) B4765081
theorem B4235627 : Blo 2229435 4235627 := bstep (se 1 (by rfl) ⟨3176720, by rfl⟩ : syracuseStep 4235627 = 6353441) B6353441
theorem B2823751 : Blo 2229435 2823751 := bstep (se 1 (by rfl) ⟨2117813, by rfl⟩ : syracuseStep 2823751 = 4235627) B4235627
theorem B3765001 : Blo 2229435 3765001 := bstep (se 2 (by rfl) ⟨1411875, by rfl⟩ : syracuseStep 3765001 = 2823751) B2823751
theorem B5020001 : Blo 2229435 5020001 := bstep (se 2 (by rfl) ⟨1882500, by rfl⟩ : syracuseStep 5020001 = 3765001) B3765001
theorem B3346667 : Blo 2229435 3346667 := bstep (se 1 (by rfl) ⟨2510000, by rfl⟩ : syracuseStep 3346667 = 5020001) B5020001
theorem B2231111 : Blo 2229435 2231111 := bstep (se 1 (by rfl) ⟨1673333, by rfl⟩ : syracuseStep 2231111 = 3346667) B3346667
theorem B2510005 : Blo 2229435 2510005 := bbase (se 5 (by rfl) ⟨117656, by rfl⟩ : syracuseStep 2510005 = 235313) (by norm_num)
theorem B3346673 : Blo 2229435 3346673 := bstep (se 2 (by rfl) ⟨1255002, by rfl⟩ : syracuseStep 3346673 = 2510005) B2510005
theorem B2231115 : Blo 2229435 2231115 := bstep (se 1 (by rfl) ⟨1673336, by rfl⟩ : syracuseStep 2231115 = 3346673) B3346673
theorem B2823761 : Blo 2229435 2823761 := bbase (se 2 (by rfl) ⟨1058910, by rfl⟩ : syracuseStep 2823761 = 2117821) (by norm_num)
theorem B7530029 : Blo 2229435 7530029 := bstep (se 3 (by rfl) ⟨1411880, by rfl⟩ : syracuseStep 7530029 = 2823761) B2823761
theorem B5020019 : Blo 2229435 5020019 := bstep (se 1 (by rfl) ⟨3765014, by rfl⟩ : syracuseStep 5020019 = 7530029) B7530029
theorem B3346679 : Blo 2229435 3346679 := bstep (se 1 (by rfl) ⟨2510009, by rfl⟩ : syracuseStep 3346679 = 5020019) B5020019
theorem B2231119 : Blo 2229435 2231119 := bstep (se 1 (by rfl) ⟨1673339, by rfl⟩ : syracuseStep 2231119 = 3346679) B3346679
theorem B3346685 : Blo 2229435 3346685 := bbase (se 3 (by rfl) ⟨627503, by rfl⟩ : syracuseStep 3346685 = 1255007) (by norm_num)
theorem B2231123 : Blo 2229435 2231123 := bstep (se 1 (by rfl) ⟨1673342, by rfl⟩ : syracuseStep 2231123 = 3346685) B3346685
theorem B5020037 : Blo 2229435 5020037 := bbase (se 4 (by rfl) ⟨470628, by rfl⟩ : syracuseStep 5020037 = 941257) (by norm_num)
theorem B3346691 : Blo 2229435 3346691 := bstep (se 1 (by rfl) ⟨2510018, by rfl⟩ : syracuseStep 3346691 = 5020037) B5020037
theorem B2231127 : Blo 2229435 2231127 := bstep (se 1 (by rfl) ⟨1673345, by rfl⟩ : syracuseStep 2231127 = 3346691) B3346691
theorem B3176749 : Blo 2229435 3176749 := bbase (se 3 (by rfl) ⟨595640, by rfl⟩ : syracuseStep 3176749 = 1191281) (by norm_num)
theorem B4235665 : Blo 2229435 4235665 := bstep (se 2 (by rfl) ⟨1588374, by rfl⟩ : syracuseStep 4235665 = 3176749) B3176749
theorem B5647553 : Blo 2229435 5647553 := bstep (se 2 (by rfl) ⟨2117832, by rfl⟩ : syracuseStep 5647553 = 4235665) B4235665
theorem B3765035 : Blo 2229435 3765035 := bstep (se 1 (by rfl) ⟨2823776, by rfl⟩ : syracuseStep 3765035 = 5647553) B5647553
theorem B2510023 : Blo 2229435 2510023 := bstep (se 1 (by rfl) ⟨1882517, by rfl⟩ : syracuseStep 2510023 = 3765035) B3765035
theorem B3346697 : Blo 2229435 3346697 := bstep (se 2 (by rfl) ⟨1255011, by rfl⟩ : syracuseStep 3346697 = 2510023) B2510023
theorem B2231131 : Blo 2229435 2231131 := bstep (se 1 (by rfl) ⟨1673348, by rfl⟩ : syracuseStep 2231131 = 3346697) B3346697
theorem B11295125 : Blo 2229435 11295125 := bbase (se 6 (by rfl) ⟨264729, by rfl⟩ : syracuseStep 11295125 = 529459) (by norm_num)
theorem B7530083 : Blo 2229435 7530083 := bstep (se 1 (by rfl) ⟨5647562, by rfl⟩ : syracuseStep 7530083 = 11295125) B11295125
theorem B5020055 : Blo 2229435 5020055 := bstep (se 1 (by rfl) ⟨3765041, by rfl⟩ : syracuseStep 5020055 = 7530083) B7530083
theorem B3346703 : Blo 2229435 3346703 := bstep (se 1 (by rfl) ⟨2510027, by rfl⟩ : syracuseStep 3346703 = 5020055) B5020055
theorem B2231135 : Blo 2229435 2231135 := bstep (se 1 (by rfl) ⟨1673351, by rfl⟩ : syracuseStep 2231135 = 3346703) B3346703
theorem B3346709 : Blo 2229435 3346709 := bbase (se 6 (by rfl) ⟨78438, by rfl⟩ : syracuseStep 3346709 = 156877) (by norm_num)
theorem B2231139 : Blo 2229435 2231139 := bstep (se 1 (by rfl) ⟨1673354, by rfl⟩ : syracuseStep 2231139 = 3346709) B3346709
theorem B8041189 : Blo 2229435 8041189 := bbase (se 4 (by rfl) ⟨753861, by rfl⟩ : syracuseStep 8041189 = 1507723) (by norm_num)
theorem B10721585 : Blo 2229435 10721585 := bstep (se 2 (by rfl) ⟨4020594, by rfl⟩ : syracuseStep 10721585 = 8041189) B8041189
theorem B28590893 : Blo 2229435 28590893 := bstep (se 3 (by rfl) ⟨5360792, by rfl⟩ : syracuseStep 28590893 = 10721585) B10721585
theorem B19060595 : Blo 2229435 19060595 := bstep (se 1 (by rfl) ⟨14295446, by rfl⟩ : syracuseStep 19060595 = 28590893) B28590893
theorem B12707063 : Blo 2229435 12707063 := bstep (se 1 (by rfl) ⟨9530297, by rfl⟩ : syracuseStep 12707063 = 19060595) B19060595
theorem B8471375 : Blo 2229435 8471375 := bstep (se 1 (by rfl) ⟨6353531, by rfl⟩ : syracuseStep 8471375 = 12707063) B12707063
theorem B5647583 : Blo 2229435 5647583 := bstep (se 1 (by rfl) ⟨4235687, by rfl⟩ : syracuseStep 5647583 = 8471375) B8471375
theorem B3765055 : Blo 2229435 3765055 := bstep (se 1 (by rfl) ⟨2823791, by rfl⟩ : syracuseStep 3765055 = 5647583) B5647583
theorem B5020073 : Blo 2229435 5020073 := bstep (se 2 (by rfl) ⟨1882527, by rfl⟩ : syracuseStep 5020073 = 3765055) B3765055
theorem B3346715 : Blo 2229435 3346715 := bstep (se 1 (by rfl) ⟨2510036, by rfl⟩ : syracuseStep 3346715 = 5020073) B5020073
theorem B2231143 : Blo 2229435 2231143 := bstep (se 1 (by rfl) ⟨1673357, by rfl⟩ : syracuseStep 2231143 = 3346715) B3346715
theorem B2510041 : Blo 2229435 2510041 := bbase (se 2 (by rfl) ⟨941265, by rfl⟩ : syracuseStep 2510041 = 1882531) (by norm_num)
theorem B3346721 : Blo 2229435 3346721 := bstep (se 2 (by rfl) ⟨1255020, by rfl⟩ : syracuseStep 3346721 = 2510041) B2510041
theorem B2231147 : Blo 2229435 2231147 := bstep (se 1 (by rfl) ⟨1673360, by rfl⟩ : syracuseStep 2231147 = 3346721) B3346721
theorem B5360813 : Blo 2229435 5360813 := bbase (se 3 (by rfl) ⟨1005152, by rfl⟩ : syracuseStep 5360813 = 2010305) (by norm_num)
theorem B3573875 : Blo 2229435 3573875 := bstep (se 1 (by rfl) ⟨2680406, by rfl⟩ : syracuseStep 3573875 = 5360813) B5360813
theorem B2382583 : Blo 2229435 2382583 := bstep (se 1 (by rfl) ⟨1786937, by rfl⟩ : syracuseStep 2382583 = 3573875) B3573875
theorem B3176777 : Blo 2229435 3176777 := bstep (se 2 (by rfl) ⟨1191291, by rfl⟩ : syracuseStep 3176777 = 2382583) B2382583
theorem B8471405 : Blo 2229435 8471405 := bstep (se 3 (by rfl) ⟨1588388, by rfl⟩ : syracuseStep 8471405 = 3176777) B3176777
theorem B5647603 : Blo 2229435 5647603 := bstep (se 1 (by rfl) ⟨4235702, by rfl⟩ : syracuseStep 5647603 = 8471405) B8471405
theorem B7530137 : Blo 2229435 7530137 := bstep (se 2 (by rfl) ⟨2823801, by rfl⟩ : syracuseStep 7530137 = 5647603) B5647603
theorem B5020091 : Blo 2229435 5020091 := bstep (se 1 (by rfl) ⟨3765068, by rfl⟩ : syracuseStep 5020091 = 7530137) B7530137
theorem B3346727 : Blo 2229435 3346727 := bstep (se 1 (by rfl) ⟨2510045, by rfl⟩ : syracuseStep 3346727 = 5020091) B5020091
theorem B2231151 : Blo 2229435 2231151 := bstep (se 1 (by rfl) ⟨1673363, by rfl⟩ : syracuseStep 2231151 = 3346727) B3346727
theorem B3346733 : Blo 2229435 3346733 := bbase (se 3 (by rfl) ⟨627512, by rfl⟩ : syracuseStep 3346733 = 1255025) (by norm_num)
theorem B2231155 : Blo 2229435 2231155 := bstep (se 1 (by rfl) ⟨1673366, by rfl⟩ : syracuseStep 2231155 = 3346733) B3346733
theorem B5020109 : Blo 2229435 5020109 := bbase (se 3 (by rfl) ⟨941270, by rfl⟩ : syracuseStep 5020109 = 1882541) (by norm_num)
theorem B3346739 : Blo 2229435 3346739 := bstep (se 1 (by rfl) ⟨2510054, by rfl⟩ : syracuseStep 3346739 = 5020109) B5020109
theorem B2231159 : Blo 2229435 2231159 := bstep (se 1 (by rfl) ⟨1673369, by rfl⟩ : syracuseStep 2231159 = 3346739) B3346739
theorem B2823817 : Blo 2229435 2823817 := bbase (se 2 (by rfl) ⟨1058931, by rfl⟩ : syracuseStep 2823817 = 2117863) (by norm_num)
theorem B3765089 : Blo 2229435 3765089 := bstep (se 2 (by rfl) ⟨1411908, by rfl⟩ : syracuseStep 3765089 = 2823817) B2823817
theorem B2510059 : Blo 2229435 2510059 := bstep (se 1 (by rfl) ⟨1882544, by rfl⟩ : syracuseStep 2510059 = 3765089) B3765089
theorem B3346745 : Blo 2229435 3346745 := bstep (se 2 (by rfl) ⟨1255029, by rfl⟩ : syracuseStep 3346745 = 2510059) B2510059
theorem B2231163 : Blo 2229435 2231163 := bstep (se 1 (by rfl) ⟨1673372, by rfl⟩ : syracuseStep 2231163 = 3346745) B3346745
theorem B3264077 : Blo 2229435 3264077 := bbase (se 3 (by rfl) ⟨612014, by rfl⟩ : syracuseStep 3264077 = 1224029) (by norm_num)
theorem B8704205 : Blo 2229435 8704205 := bstep (se 3 (by rfl) ⟨1632038, by rfl⟩ : syracuseStep 8704205 = 3264077) B3264077
theorem B5802803 : Blo 2229435 5802803 := bstep (se 1 (by rfl) ⟨4352102, by rfl⟩ : syracuseStep 5802803 = 8704205) B8704205
theorem B3868535 : Blo 2229435 3868535 := bstep (se 1 (by rfl) ⟨2901401, by rfl⟩ : syracuseStep 3868535 = 5802803) B5802803
theorem B2579023 : Blo 2229435 2579023 := bstep (se 1 (by rfl) ⟨1934267, by rfl⟩ : syracuseStep 2579023 = 3868535) B3868535
theorem B3438697 : Blo 2229435 3438697 := bstep (se 2 (by rfl) ⟨1289511, by rfl⟩ : syracuseStep 3438697 = 2579023) B2579023
theorem B4584929 : Blo 2229435 4584929 := bstep (se 2 (by rfl) ⟨1719348, by rfl⟩ : syracuseStep 4584929 = 3438697) B3438697
theorem B48905909 : Blo 2229435 48905909 := bstep (se 5 (by rfl) ⟨2292464, by rfl⟩ : syracuseStep 48905909 = 4584929) B4584929
theorem B32603939 : Blo 2229435 32603939 := bstep (se 1 (by rfl) ⟨24452954, by rfl⟩ : syracuseStep 32603939 = 48905909) B48905909
theorem B21735959 : Blo 2229435 21735959 := bstep (se 1 (by rfl) ⟨16301969, by rfl⟩ : syracuseStep 21735959 = 32603939) B32603939
theorem B57962557 : Blo 2229435 57962557 := bstep (se 3 (by rfl) ⟨10867979, by rfl⟩ : syracuseStep 57962557 = 21735959) B21735959
theorem B77283409 : Blo 2229435 77283409 := bstep (se 2 (by rfl) ⟨28981278, by rfl⟩ : syracuseStep 77283409 = 57962557) B57962557
theorem B103044545 : Blo 2229435 103044545 := bstep (se 2 (by rfl) ⟨38641704, by rfl⟩ : syracuseStep 103044545 = 77283409) B77283409
theorem B68696363 : Blo 2229435 68696363 := bstep (se 1 (by rfl) ⟨51522272, by rfl⟩ : syracuseStep 68696363 = 103044545) B103044545
theorem B45797575 : Blo 2229435 45797575 := bstep (se 1 (by rfl) ⟨34348181, by rfl⟩ : syracuseStep 45797575 = 68696363) B68696363
theorem B61063433 : Blo 2229435 61063433 := bstep (se 2 (by rfl) ⟨22898787, by rfl⟩ : syracuseStep 61063433 = 45797575) B45797575
theorem B40708955 : Blo 2229435 40708955 := bstep (se 1 (by rfl) ⟨30531716, by rfl⟩ : syracuseStep 40708955 = 61063433) B61063433
theorem B27139303 : Blo 2229435 27139303 := bstep (se 1 (by rfl) ⟨20354477, by rfl⟩ : syracuseStep 27139303 = 40708955) B40708955
theorem B36185737 : Blo 2229435 36185737 := bstep (se 2 (by rfl) ⟨13569651, by rfl⟩ : syracuseStep 36185737 = 27139303) B27139303
theorem B48247649 : Blo 2229435 48247649 := bstep (se 2 (by rfl) ⟨18092868, by rfl⟩ : syracuseStep 48247649 = 36185737) B36185737
theorem B32165099 : Blo 2229435 32165099 := bstep (se 1 (by rfl) ⟨24123824, by rfl⟩ : syracuseStep 32165099 = 48247649) B48247649
theorem B21443399 : Blo 2229435 21443399 := bstep (se 1 (by rfl) ⟨16082549, by rfl⟩ : syracuseStep 21443399 = 32165099) B32165099
theorem B14295599 : Blo 2229435 14295599 := bstep (se 1 (by rfl) ⟨10721699, by rfl⟩ : syracuseStep 14295599 = 21443399) B21443399
theorem B9530399 : Blo 2229435 9530399 := bstep (se 1 (by rfl) ⟨7147799, by rfl⟩ : syracuseStep 9530399 = 14295599) B14295599
theorem B25414397 : Blo 2229435 25414397 := bstep (se 3 (by rfl) ⟨4765199, by rfl⟩ : syracuseStep 25414397 = 9530399) B9530399
theorem B16942931 : Blo 2229435 16942931 := bstep (se 1 (by rfl) ⟨12707198, by rfl⟩ : syracuseStep 16942931 = 25414397) B25414397
theorem B11295287 : Blo 2229435 11295287 := bstep (se 1 (by rfl) ⟨8471465, by rfl⟩ : syracuseStep 11295287 = 16942931) B16942931
theorem B7530191 : Blo 2229435 7530191 := bstep (se 1 (by rfl) ⟨5647643, by rfl⟩ : syracuseStep 7530191 = 11295287) B11295287
theorem B5020127 : Blo 2229435 5020127 := bstep (se 1 (by rfl) ⟨3765095, by rfl⟩ : syracuseStep 5020127 = 7530191) B7530191
theorem B3346751 : Blo 2229435 3346751 := bstep (se 1 (by rfl) ⟨2510063, by rfl⟩ : syracuseStep 3346751 = 5020127) B5020127
theorem B2231167 : Blo 2229435 2231167 := bstep (se 1 (by rfl) ⟨1673375, by rfl⟩ : syracuseStep 2231167 = 3346751) B3346751
theorem B3346757 : Blo 2229435 3346757 := bbase (se 4 (by rfl) ⟨313758, by rfl⟩ : syracuseStep 3346757 = 627517) (by norm_num)
theorem B2231171 : Blo 2229435 2231171 := bstep (se 1 (by rfl) ⟨1673378, by rfl⟩ : syracuseStep 2231171 = 3346757) B3346757
theorem B3765109 : Blo 2229435 3765109 := bbase (se 5 (by rfl) ⟨176489, by rfl⟩ : syracuseStep 3765109 = 352979) (by norm_num)
theorem B5020145 : Blo 2229435 5020145 := bstep (se 2 (by rfl) ⟨1882554, by rfl⟩ : syracuseStep 5020145 = 3765109) B3765109
theorem B3346763 : Blo 2229435 3346763 := bstep (se 1 (by rfl) ⟨2510072, by rfl⟩ : syracuseStep 3346763 = 5020145) B5020145
theorem B2231175 : Blo 2229435 2231175 := bstep (se 1 (by rfl) ⟨1673381, by rfl⟩ : syracuseStep 2231175 = 3346763) B3346763
theorem B2510077 : Blo 2229435 2510077 := bbase (se 3 (by rfl) ⟨470639, by rfl⟩ : syracuseStep 2510077 = 941279) (by norm_num)
theorem B3346769 : Blo 2229435 3346769 := bstep (se 2 (by rfl) ⟨1255038, by rfl⟩ : syracuseStep 3346769 = 2510077) B2510077
theorem B2231179 : Blo 2229435 2231179 := bstep (se 1 (by rfl) ⟨1673384, by rfl⟩ : syracuseStep 2231179 = 3346769) B3346769
theorem B7530245 : Blo 2229435 7530245 := bbase (se 4 (by rfl) ⟨705960, by rfl⟩ : syracuseStep 7530245 = 1411921) (by norm_num)
theorem B5020163 : Blo 2229435 5020163 := bstep (se 1 (by rfl) ⟨3765122, by rfl⟩ : syracuseStep 5020163 = 7530245) B7530245
theorem B3346775 : Blo 2229435 3346775 := bstep (se 1 (by rfl) ⟨2510081, by rfl⟩ : syracuseStep 3346775 = 5020163) B5020163
theorem B2231183 : Blo 2229435 2231183 := bstep (se 1 (by rfl) ⟨1673387, by rfl⟩ : syracuseStep 2231183 = 3346775) B3346775
theorem B3346781 : Blo 2229435 3346781 := bbase (se 3 (by rfl) ⟨627521, by rfl⟩ : syracuseStep 3346781 = 1255043) (by norm_num)
theorem B2231187 : Blo 2229435 2231187 := bstep (se 1 (by rfl) ⟨1673390, by rfl⟩ : syracuseStep 2231187 = 3346781) B3346781
theorem B5020181 : Blo 2229435 5020181 := bbase (se 6 (by rfl) ⟨117660, by rfl⟩ : syracuseStep 5020181 = 235321) (by norm_num)
theorem B3346787 : Blo 2229435 3346787 := bstep (se 1 (by rfl) ⟨2510090, by rfl⟩ : syracuseStep 3346787 = 5020181) B5020181
theorem B2231191 : Blo 2229435 2231191 := bstep (se 1 (by rfl) ⟨1673393, by rfl⟩ : syracuseStep 2231191 = 3346787) B3346787
theorem B8471573 : Blo 2229435 8471573 := bbase (se 6 (by rfl) ⟨198552, by rfl⟩ : syracuseStep 8471573 = 397105) (by norm_num)
theorem B5647715 : Blo 2229435 5647715 := bstep (se 1 (by rfl) ⟨4235786, by rfl⟩ : syracuseStep 5647715 = 8471573) B8471573
theorem B3765143 : Blo 2229435 3765143 := bstep (se 1 (by rfl) ⟨2823857, by rfl⟩ : syracuseStep 3765143 = 5647715) B5647715
theorem B2510095 : Blo 2229435 2510095 := bstep (se 1 (by rfl) ⟨1882571, by rfl⟩ : syracuseStep 2510095 = 3765143) B3765143
theorem B3346793 : Blo 2229435 3346793 := bstep (se 2 (by rfl) ⟨1255047, by rfl⟩ : syracuseStep 3346793 = 2510095) B2510095
theorem B2231195 : Blo 2229435 2231195 := bstep (se 1 (by rfl) ⟨1673396, by rfl⟩ : syracuseStep 2231195 = 3346793) B3346793
theorem B12707381 : Blo 2229435 12707381 := bbase (se 5 (by rfl) ⟨595658, by rfl⟩ : syracuseStep 12707381 = 1191317) (by norm_num)
theorem B8471587 : Blo 2229435 8471587 := bstep (se 1 (by rfl) ⟨6353690, by rfl⟩ : syracuseStep 8471587 = 12707381) B12707381
theorem B11295449 : Blo 2229435 11295449 := bstep (se 2 (by rfl) ⟨4235793, by rfl⟩ : syracuseStep 11295449 = 8471587) B8471587
theorem B7530299 : Blo 2229435 7530299 := bstep (se 1 (by rfl) ⟨5647724, by rfl⟩ : syracuseStep 7530299 = 11295449) B11295449
theorem B5020199 : Blo 2229435 5020199 := bstep (se 1 (by rfl) ⟨3765149, by rfl⟩ : syracuseStep 5020199 = 7530299) B7530299
theorem B3346799 : Blo 2229435 3346799 := bstep (se 1 (by rfl) ⟨2510099, by rfl⟩ : syracuseStep 3346799 = 5020199) B5020199
theorem B2231199 : Blo 2229435 2231199 := bstep (se 1 (by rfl) ⟨1673399, by rfl⟩ : syracuseStep 2231199 = 3346799) B3346799
theorem B3346805 : Blo 2229435 3346805 := bbase (se 5 (by rfl) ⟨156881, by rfl⟩ : syracuseStep 3346805 = 313763) (by norm_num)
theorem B2231203 : Blo 2229435 2231203 := bstep (se 1 (by rfl) ⟨1673402, by rfl⟩ : syracuseStep 2231203 = 3346805) B3346805
theorem B3573965 : Blo 2229435 3573965 := bbase (se 3 (by rfl) ⟨670118, by rfl⟩ : syracuseStep 3573965 = 1340237) (by norm_num)
theorem B2382643 : Blo 2229435 2382643 := bstep (se 1 (by rfl) ⟨1786982, by rfl⟩ : syracuseStep 2382643 = 3573965) B3573965
theorem B3176857 : Blo 2229435 3176857 := bstep (se 2 (by rfl) ⟨1191321, by rfl⟩ : syracuseStep 3176857 = 2382643) B2382643
theorem B4235809 : Blo 2229435 4235809 := bstep (se 2 (by rfl) ⟨1588428, by rfl⟩ : syracuseStep 4235809 = 3176857) B3176857
theorem B5647745 : Blo 2229435 5647745 := bstep (se 2 (by rfl) ⟨2117904, by rfl⟩ : syracuseStep 5647745 = 4235809) B4235809
theorem B3765163 : Blo 2229435 3765163 := bstep (se 1 (by rfl) ⟨2823872, by rfl⟩ : syracuseStep 3765163 = 5647745) B5647745
theorem B5020217 : Blo 2229435 5020217 := bstep (se 2 (by rfl) ⟨1882581, by rfl⟩ : syracuseStep 5020217 = 3765163) B3765163
theorem B3346811 : Blo 2229435 3346811 := bstep (se 1 (by rfl) ⟨2510108, by rfl⟩ : syracuseStep 3346811 = 5020217) B5020217
theorem B2231207 : Blo 2229435 2231207 := bstep (se 1 (by rfl) ⟨1673405, by rfl⟩ : syracuseStep 2231207 = 3346811) B3346811
theorem B2510113 : Blo 2229435 2510113 := bbase (se 2 (by rfl) ⟨941292, by rfl⟩ : syracuseStep 2510113 = 1882585) (by norm_num)
theorem B3346817 : Blo 2229435 3346817 := bstep (se 2 (by rfl) ⟨1255056, by rfl⟩ : syracuseStep 3346817 = 2510113) B2510113
theorem B2231211 : Blo 2229435 2231211 := bstep (se 1 (by rfl) ⟨1673408, by rfl⟩ : syracuseStep 2231211 = 3346817) B3346817
theorem B5647765 : Blo 2229435 5647765 := bbase (se 6 (by rfl) ⟨132369, by rfl⟩ : syracuseStep 5647765 = 264739) (by norm_num)
theorem B7530353 : Blo 2229435 7530353 := bstep (se 2 (by rfl) ⟨2823882, by rfl⟩ : syracuseStep 7530353 = 5647765) B5647765
theorem B5020235 : Blo 2229435 5020235 := bstep (se 1 (by rfl) ⟨3765176, by rfl⟩ : syracuseStep 5020235 = 7530353) B7530353
theorem B3346823 : Blo 2229435 3346823 := bstep (se 1 (by rfl) ⟨2510117, by rfl⟩ : syracuseStep 3346823 = 5020235) B5020235
theorem B2231215 : Blo 2229435 2231215 := bstep (se 1 (by rfl) ⟨1673411, by rfl⟩ : syracuseStep 2231215 = 3346823) B3346823
theorem B3346829 : Blo 2229435 3346829 := bbase (se 3 (by rfl) ⟨627530, by rfl⟩ : syracuseStep 3346829 = 1255061) (by norm_num)
theorem B2231219 : Blo 2229435 2231219 := bstep (se 1 (by rfl) ⟨1673414, by rfl⟩ : syracuseStep 2231219 = 3346829) B3346829
theorem B5020253 : Blo 2229435 5020253 := bbase (se 3 (by rfl) ⟨941297, by rfl⟩ : syracuseStep 5020253 = 1882595) (by norm_num)
theorem B3346835 : Blo 2229435 3346835 := bstep (se 1 (by rfl) ⟨2510126, by rfl⟩ : syracuseStep 3346835 = 5020253) B5020253
theorem B2231223 : Blo 2229435 2231223 := bstep (se 1 (by rfl) ⟨1673417, by rfl⟩ : syracuseStep 2231223 = 3346835) B3346835
theorem B3765197 : Blo 2229435 3765197 := bbase (se 3 (by rfl) ⟨705974, by rfl⟩ : syracuseStep 3765197 = 1411949) (by norm_num)
theorem B2510131 : Blo 2229435 2510131 := bstep (se 1 (by rfl) ⟨1882598, by rfl⟩ : syracuseStep 2510131 = 3765197) B3765197
theorem B3346841 : Blo 2229435 3346841 := bstep (se 2 (by rfl) ⟨1255065, by rfl⟩ : syracuseStep 3346841 = 2510131) B2510131
theorem B2231227 : Blo 2229435 2231227 := bstep (se 1 (by rfl) ⟨1673420, by rfl⟩ : syracuseStep 2231227 = 3346841) B3346841
theorem B3438797 : Blo 2229435 3438797 := bbase (se 3 (by rfl) ⟨644774, by rfl⟩ : syracuseStep 3438797 = 1289549) (by norm_num)
theorem B36680501 : Blo 2229435 36680501 := bstep (se 5 (by rfl) ⟨1719398, by rfl⟩ : syracuseStep 36680501 = 3438797) B3438797
theorem B24453667 : Blo 2229435 24453667 := bstep (se 1 (by rfl) ⟨18340250, by rfl⟩ : syracuseStep 24453667 = 36680501) B36680501
theorem B32604889 : Blo 2229435 32604889 := bstep (se 2 (by rfl) ⟨12226833, by rfl⟩ : syracuseStep 32604889 = 24453667) B24453667
theorem B43473185 : Blo 2229435 43473185 := bstep (se 2 (by rfl) ⟨16302444, by rfl⟩ : syracuseStep 43473185 = 32604889) B32604889
theorem B28982123 : Blo 2229435 28982123 := bstep (se 1 (by rfl) ⟨21736592, by rfl⟩ : syracuseStep 28982123 = 43473185) B43473185
theorem B19321415 : Blo 2229435 19321415 := bstep (se 1 (by rfl) ⟨14491061, by rfl⟩ : syracuseStep 19321415 = 28982123) B28982123
theorem B12880943 : Blo 2229435 12880943 := bstep (se 1 (by rfl) ⟨9660707, by rfl⟩ : syracuseStep 12880943 = 19321415) B19321415
theorem B8587295 : Blo 2229435 8587295 := bstep (se 1 (by rfl) ⟨6440471, by rfl⟩ : syracuseStep 8587295 = 12880943) B12880943
theorem B5724863 : Blo 2229435 5724863 := bstep (se 1 (by rfl) ⟨4293647, by rfl⟩ : syracuseStep 5724863 = 8587295) B8587295
theorem B3816575 : Blo 2229435 3816575 := bstep (se 1 (by rfl) ⟨2862431, by rfl⟩ : syracuseStep 3816575 = 5724863) B5724863
theorem B2544383 : Blo 2229435 2544383 := bstep (se 1 (by rfl) ⟨1908287, by rfl⟩ : syracuseStep 2544383 = 3816575) B3816575
theorem B6785021 : Blo 2229435 6785021 := bstep (se 3 (by rfl) ⟨1272191, by rfl⟩ : syracuseStep 6785021 = 2544383) B2544383
theorem B4523347 : Blo 2229435 4523347 := bstep (se 1 (by rfl) ⟨3392510, by rfl⟩ : syracuseStep 4523347 = 6785021) B6785021
theorem B24124517 : Blo 2229435 24124517 := bstep (se 4 (by rfl) ⟨2261673, by rfl⟩ : syracuseStep 24124517 = 4523347) B4523347
theorem B16083011 : Blo 2229435 16083011 := bstep (se 1 (by rfl) ⟨12062258, by rfl⟩ : syracuseStep 16083011 = 24124517) B24124517
theorem B10722007 : Blo 2229435 10722007 := bstep (se 1 (by rfl) ⟨8041505, by rfl⟩ : syracuseStep 10722007 = 16083011) B16083011
theorem B14296009 : Blo 2229435 14296009 := bstep (se 2 (by rfl) ⟨5361003, by rfl⟩ : syracuseStep 14296009 = 10722007) B10722007
theorem B19061345 : Blo 2229435 19061345 := bstep (se 2 (by rfl) ⟨7148004, by rfl⟩ : syracuseStep 19061345 = 14296009) B14296009
theorem B12707563 : Blo 2229435 12707563 := bstep (se 1 (by rfl) ⟨9530672, by rfl⟩ : syracuseStep 12707563 = 19061345) B19061345
theorem B16943417 : Blo 2229435 16943417 := bstep (se 2 (by rfl) ⟨6353781, by rfl⟩ : syracuseStep 16943417 = 12707563) B12707563
theorem B11295611 : Blo 2229435 11295611 := bstep (se 1 (by rfl) ⟨8471708, by rfl⟩ : syracuseStep 11295611 = 16943417) B16943417
theorem B7530407 : Blo 2229435 7530407 := bstep (se 1 (by rfl) ⟨5647805, by rfl⟩ : syracuseStep 7530407 = 11295611) B11295611
theorem B5020271 : Blo 2229435 5020271 := bstep (se 1 (by rfl) ⟨3765203, by rfl⟩ : syracuseStep 5020271 = 7530407) B7530407
theorem B3346847 : Blo 2229435 3346847 := bstep (se 1 (by rfl) ⟨2510135, by rfl⟩ : syracuseStep 3346847 = 5020271) B5020271
theorem B2231231 : Blo 2229435 2231231 := bstep (se 1 (by rfl) ⟨1673423, by rfl⟩ : syracuseStep 2231231 = 3346847) B3346847
theorem B3346853 : Blo 2229435 3346853 := bbase (se 4 (by rfl) ⟨313767, by rfl⟩ : syracuseStep 3346853 = 627535) (by norm_num)
theorem B2231235 : Blo 2229435 2231235 := bstep (se 1 (by rfl) ⟨1673426, by rfl⟩ : syracuseStep 2231235 = 3346853) B3346853
theorem B2823913 : Blo 2229435 2823913 := bbase (se 2 (by rfl) ⟨1058967, by rfl⟩ : syracuseStep 2823913 = 2117935) (by norm_num)
theorem B3765217 : Blo 2229435 3765217 := bstep (se 2 (by rfl) ⟨1411956, by rfl⟩ : syracuseStep 3765217 = 2823913) B2823913
theorem B5020289 : Blo 2229435 5020289 := bstep (se 2 (by rfl) ⟨1882608, by rfl⟩ : syracuseStep 5020289 = 3765217) B3765217
theorem B3346859 : Blo 2229435 3346859 := bstep (se 1 (by rfl) ⟨2510144, by rfl⟩ : syracuseStep 3346859 = 5020289) B5020289
theorem B2231239 : Blo 2229435 2231239 := bstep (se 1 (by rfl) ⟨1673429, by rfl⟩ : syracuseStep 2231239 = 3346859) B3346859
theorem B2510149 : Blo 2229435 2510149 := bbase (se 4 (by rfl) ⟨235326, by rfl⟩ : syracuseStep 2510149 = 470653) (by norm_num)
theorem B3346865 : Blo 2229435 3346865 := bstep (se 2 (by rfl) ⟨1255074, by rfl⟩ : syracuseStep 3346865 = 2510149) B2510149
theorem B2231243 : Blo 2229435 2231243 := bstep (se 1 (by rfl) ⟨1673432, by rfl⟩ : syracuseStep 2231243 = 3346865) B3346865
theorem B4235885 : Blo 2229435 4235885 := bbase (se 3 (by rfl) ⟨794228, by rfl⟩ : syracuseStep 4235885 = 1588457) (by norm_num)
theorem B2823923 : Blo 2229435 2823923 := bstep (se 1 (by rfl) ⟨2117942, by rfl⟩ : syracuseStep 2823923 = 4235885) B4235885
theorem B7530461 : Blo 2229435 7530461 := bstep (se 3 (by rfl) ⟨1411961, by rfl⟩ : syracuseStep 7530461 = 2823923) B2823923
theorem B5020307 : Blo 2229435 5020307 := bstep (se 1 (by rfl) ⟨3765230, by rfl⟩ : syracuseStep 5020307 = 7530461) B7530461
theorem B3346871 : Blo 2229435 3346871 := bstep (se 1 (by rfl) ⟨2510153, by rfl⟩ : syracuseStep 3346871 = 5020307) B5020307
theorem B2231247 : Blo 2229435 2231247 := bstep (se 1 (by rfl) ⟨1673435, by rfl⟩ : syracuseStep 2231247 = 3346871) B3346871
theorem B3346877 : Blo 2229435 3346877 := bbase (se 3 (by rfl) ⟨627539, by rfl⟩ : syracuseStep 3346877 = 1255079) (by norm_num)
theorem B2231251 : Blo 2229435 2231251 := bstep (se 1 (by rfl) ⟨1673438, by rfl⟩ : syracuseStep 2231251 = 3346877) B3346877
theorem B5020325 : Blo 2229435 5020325 := bbase (se 4 (by rfl) ⟨470655, by rfl⟩ : syracuseStep 5020325 = 941311) (by norm_num)
theorem B3346883 : Blo 2229435 3346883 := bstep (se 1 (by rfl) ⟨2510162, by rfl⟩ : syracuseStep 3346883 = 5020325) B5020325
theorem B2231255 : Blo 2229435 2231255 := bstep (se 1 (by rfl) ⟨1673441, by rfl⟩ : syracuseStep 2231255 = 3346883) B3346883
theorem B5647877 : Blo 2229435 5647877 := bbase (se 4 (by rfl) ⟨529488, by rfl⟩ : syracuseStep 5647877 = 1058977) (by norm_num)
theorem B3765251 : Blo 2229435 3765251 := bstep (se 1 (by rfl) ⟨2823938, by rfl⟩ : syracuseStep 3765251 = 5647877) B5647877
theorem B2510167 : Blo 2229435 2510167 := bstep (se 1 (by rfl) ⟨1882625, by rfl⟩ : syracuseStep 2510167 = 3765251) B3765251
theorem B3346889 : Blo 2229435 3346889 := bstep (se 2 (by rfl) ⟨1255083, by rfl⟩ : syracuseStep 3346889 = 2510167) B2510167
theorem B2231259 : Blo 2229435 2231259 := bstep (se 1 (by rfl) ⟨1673444, by rfl⟩ : syracuseStep 2231259 = 3346889) B3346889
theorem B4765405 : Blo 2229435 4765405 := bbase (se 3 (by rfl) ⟨893513, by rfl⟩ : syracuseStep 4765405 = 1787027) (by norm_num)
theorem B6353873 : Blo 2229435 6353873 := bstep (se 2 (by rfl) ⟨2382702, by rfl⟩ : syracuseStep 6353873 = 4765405) B4765405
theorem B4235915 : Blo 2229435 4235915 := bstep (se 1 (by rfl) ⟨3176936, by rfl⟩ : syracuseStep 4235915 = 6353873) B6353873
theorem B11295773 : Blo 2229435 11295773 := bstep (se 3 (by rfl) ⟨2117957, by rfl⟩ : syracuseStep 11295773 = 4235915) B4235915
theorem B7530515 : Blo 2229435 7530515 := bstep (se 1 (by rfl) ⟨5647886, by rfl⟩ : syracuseStep 7530515 = 11295773) B11295773
theorem B5020343 : Blo 2229435 5020343 := bstep (se 1 (by rfl) ⟨3765257, by rfl⟩ : syracuseStep 5020343 = 7530515) B7530515
theorem B3346895 : Blo 2229435 3346895 := bstep (se 1 (by rfl) ⟨2510171, by rfl⟩ : syracuseStep 3346895 = 5020343) B5020343
theorem B2231263 : Blo 2229435 2231263 := bstep (se 1 (by rfl) ⟨1673447, by rfl⟩ : syracuseStep 2231263 = 3346895) B3346895
theorem B3346901 : Blo 2229435 3346901 := bbase (se 7 (by rfl) ⟨39221, by rfl⟩ : syracuseStep 3346901 = 78443) (by norm_num)
theorem B2231267 : Blo 2229435 2231267 := bstep (se 1 (by rfl) ⟨1673450, by rfl⟩ : syracuseStep 2231267 = 3346901) B3346901
theorem B8471861 : Blo 2229435 8471861 := bbase (se 5 (by rfl) ⟨397118, by rfl⟩ : syracuseStep 8471861 = 794237) (by norm_num)
theorem B5647907 : Blo 2229435 5647907 := bstep (se 1 (by rfl) ⟨4235930, by rfl⟩ : syracuseStep 5647907 = 8471861) B8471861
theorem B3765271 : Blo 2229435 3765271 := bstep (se 1 (by rfl) ⟨2823953, by rfl⟩ : syracuseStep 3765271 = 5647907) B5647907
theorem B5020361 : Blo 2229435 5020361 := bstep (se 2 (by rfl) ⟨1882635, by rfl⟩ : syracuseStep 5020361 = 3765271) B3765271
theorem B3346907 : Blo 2229435 3346907 := bstep (se 1 (by rfl) ⟨2510180, by rfl⟩ : syracuseStep 3346907 = 5020361) B5020361
theorem B2231271 : Blo 2229435 2231271 := bstep (se 1 (by rfl) ⟨1673453, by rfl⟩ : syracuseStep 2231271 = 3346907) B3346907
theorem B2510185 : Blo 2229435 2510185 := bbase (se 2 (by rfl) ⟨941319, by rfl⟩ : syracuseStep 2510185 = 1882639) (by norm_num)
theorem B3346913 : Blo 2229435 3346913 := bstep (se 2 (by rfl) ⟨1255092, by rfl⟩ : syracuseStep 3346913 = 2510185) B2510185
theorem B2231275 : Blo 2229435 2231275 := bstep (se 1 (by rfl) ⟨1673456, by rfl⟩ : syracuseStep 2231275 = 3346913) B3346913
theorem B2448181 : Blo 2229435 2448181 := bbase (se 5 (by rfl) ⟨114758, by rfl⟩ : syracuseStep 2448181 = 229517) (by norm_num)
theorem B3264241 : Blo 2229435 3264241 := bstep (se 2 (by rfl) ⟨1224090, by rfl⟩ : syracuseStep 3264241 = 2448181) B2448181
theorem B4352321 : Blo 2229435 4352321 := bstep (se 2 (by rfl) ⟨1632120, by rfl⟩ : syracuseStep 4352321 = 3264241) B3264241
theorem B2901547 : Blo 2229435 2901547 := bstep (se 1 (by rfl) ⟨2176160, by rfl⟩ : syracuseStep 2901547 = 4352321) B4352321
theorem B3868729 : Blo 2229435 3868729 := bstep (se 2 (by rfl) ⟨1450773, by rfl⟩ : syracuseStep 3868729 = 2901547) B2901547
theorem B20633221 : Blo 2229435 20633221 := bstep (se 4 (by rfl) ⟨1934364, by rfl⟩ : syracuseStep 20633221 = 3868729) B3868729
theorem B27510961 : Blo 2229435 27510961 := bstep (se 2 (by rfl) ⟨10316610, by rfl⟩ : syracuseStep 27510961 = 20633221) B20633221
theorem B36681281 : Blo 2229435 36681281 := bstep (se 2 (by rfl) ⟨13755480, by rfl⟩ : syracuseStep 36681281 = 27510961) B27510961
theorem B24454187 : Blo 2229435 24454187 := bstep (se 1 (by rfl) ⟨18340640, by rfl⟩ : syracuseStep 24454187 = 36681281) B36681281
theorem B16302791 : Blo 2229435 16302791 := bstep (se 1 (by rfl) ⟨12227093, by rfl⟩ : syracuseStep 16302791 = 24454187) B24454187
theorem B10868527 : Blo 2229435 10868527 := bstep (se 1 (by rfl) ⟨8151395, by rfl⟩ : syracuseStep 10868527 = 16302791) B16302791
theorem B14491369 : Blo 2229435 14491369 := bstep (se 2 (by rfl) ⟨5434263, by rfl⟩ : syracuseStep 14491369 = 10868527) B10868527
theorem B19321825 : Blo 2229435 19321825 := bstep (se 2 (by rfl) ⟨7245684, by rfl⟩ : syracuseStep 19321825 = 14491369) B14491369
theorem B25762433 : Blo 2229435 25762433 := bstep (se 2 (by rfl) ⟨9660912, by rfl⟩ : syracuseStep 25762433 = 19321825) B19321825
theorem B68699821 : Blo 2229435 68699821 := bstep (se 3 (by rfl) ⟨12881216, by rfl⟩ : syracuseStep 68699821 = 25762433) B25762433
theorem B91599761 : Blo 2229435 91599761 := bstep (se 2 (by rfl) ⟨34349910, by rfl⟩ : syracuseStep 91599761 = 68699821) B68699821
theorem B61066507 : Blo 2229435 61066507 := bstep (se 1 (by rfl) ⟨45799880, by rfl⟩ : syracuseStep 61066507 = 91599761) B91599761
theorem B81422009 : Blo 2229435 81422009 := bstep (se 2 (by rfl) ⟨30533253, by rfl⟩ : syracuseStep 81422009 = 61066507) B61066507
theorem B54281339 : Blo 2229435 54281339 := bstep (se 1 (by rfl) ⟨40711004, by rfl⟩ : syracuseStep 54281339 = 81422009) B81422009
theorem B36187559 : Blo 2229435 36187559 := bstep (se 1 (by rfl) ⟨27140669, by rfl⟩ : syracuseStep 36187559 = 54281339) B54281339
theorem B24125039 : Blo 2229435 24125039 := bstep (se 1 (by rfl) ⟨18093779, by rfl⟩ : syracuseStep 24125039 = 36187559) B36187559
theorem B16083359 : Blo 2229435 16083359 := bstep (se 1 (by rfl) ⟨12062519, by rfl⟩ : syracuseStep 16083359 = 24125039) B24125039
theorem B10722239 : Blo 2229435 10722239 := bstep (se 1 (by rfl) ⟨8041679, by rfl⟩ : syracuseStep 10722239 = 16083359) B16083359
theorem B7148159 : Blo 2229435 7148159 := bstep (se 1 (by rfl) ⟨5361119, by rfl⟩ : syracuseStep 7148159 = 10722239) B10722239
theorem B4765439 : Blo 2229435 4765439 := bstep (se 1 (by rfl) ⟨3574079, by rfl⟩ : syracuseStep 4765439 = 7148159) B7148159
theorem B12707837 : Blo 2229435 12707837 := bstep (se 3 (by rfl) ⟨2382719, by rfl⟩ : syracuseStep 12707837 = 4765439) B4765439
theorem B8471891 : Blo 2229435 8471891 := bstep (se 1 (by rfl) ⟨6353918, by rfl⟩ : syracuseStep 8471891 = 12707837) B12707837
theorem B5647927 : Blo 2229435 5647927 := bstep (se 1 (by rfl) ⟨4235945, by rfl⟩ : syracuseStep 5647927 = 8471891) B8471891
theorem B7530569 : Blo 2229435 7530569 := bstep (se 2 (by rfl) ⟨2823963, by rfl⟩ : syracuseStep 7530569 = 5647927) B5647927
theorem B5020379 : Blo 2229435 5020379 := bstep (se 1 (by rfl) ⟨3765284, by rfl⟩ : syracuseStep 5020379 = 7530569) B7530569
theorem B3346919 : Blo 2229435 3346919 := bstep (se 1 (by rfl) ⟨2510189, by rfl⟩ : syracuseStep 3346919 = 5020379) B5020379
theorem B2231279 : Blo 2229435 2231279 := bstep (se 1 (by rfl) ⟨1673459, by rfl⟩ : syracuseStep 2231279 = 3346919) B3346919
theorem B3346925 : Blo 2229435 3346925 := bbase (se 3 (by rfl) ⟨627548, by rfl⟩ : syracuseStep 3346925 = 1255097) (by norm_num)
theorem B2231283 : Blo 2229435 2231283 := bstep (se 1 (by rfl) ⟨1673462, by rfl⟩ : syracuseStep 2231283 = 3346925) B3346925
theorem B5020397 : Blo 2229435 5020397 := bbase (se 3 (by rfl) ⟨941324, by rfl⟩ : syracuseStep 5020397 = 1882649) (by norm_num)
theorem B3346931 : Blo 2229435 3346931 := bstep (se 1 (by rfl) ⟨2510198, by rfl⟩ : syracuseStep 3346931 = 5020397) B5020397
theorem B2231287 : Blo 2229435 2231287 := bstep (se 1 (by rfl) ⟨1673465, by rfl⟩ : syracuseStep 2231287 = 3346931) B3346931
theorem B2382733 : Blo 2229435 2382733 := bbase (se 3 (by rfl) ⟨446762, by rfl⟩ : syracuseStep 2382733 = 893525) (by norm_num)
theorem B3176977 : Blo 2229435 3176977 := bstep (se 2 (by rfl) ⟨1191366, by rfl⟩ : syracuseStep 3176977 = 2382733) B2382733
theorem B4235969 : Blo 2229435 4235969 := bstep (se 2 (by rfl) ⟨1588488, by rfl⟩ : syracuseStep 4235969 = 3176977) B3176977
theorem B2823979 : Blo 2229435 2823979 := bstep (se 1 (by rfl) ⟨2117984, by rfl⟩ : syracuseStep 2823979 = 4235969) B4235969
theorem B3765305 : Blo 2229435 3765305 := bstep (se 2 (by rfl) ⟨1411989, by rfl⟩ : syracuseStep 3765305 = 2823979) B2823979
theorem B2510203 : Blo 2229435 2510203 := bstep (se 1 (by rfl) ⟨1882652, by rfl⟩ : syracuseStep 2510203 = 3765305) B3765305
theorem B3346937 : Blo 2229435 3346937 := bstep (se 2 (by rfl) ⟨1255101, by rfl⟩ : syracuseStep 3346937 = 2510203) B2510203
theorem B2231291 : Blo 2229435 2231291 := bstep (se 1 (by rfl) ⟨1673468, by rfl⟩ : syracuseStep 2231291 = 3346937) B3346937
theorem B2614361 : Blo 2229435 2614361 := bbase (se 2 (by rfl) ⟨980385, by rfl⟩ : syracuseStep 2614361 = 1960771) (by norm_num)
theorem B6971629 : Blo 2229435 6971629 := bstep (se 3 (by rfl) ⟨1307180, by rfl⟩ : syracuseStep 6971629 = 2614361) B2614361
theorem B9295505 : Blo 2229435 9295505 := bstep (se 2 (by rfl) ⟨3485814, by rfl⟩ : syracuseStep 9295505 = 6971629) B6971629
theorem B6197003 : Blo 2229435 6197003 := bstep (se 1 (by rfl) ⟨4647752, by rfl⟩ : syracuseStep 6197003 = 9295505) B9295505
theorem B4131335 : Blo 2229435 4131335 := bstep (se 1 (by rfl) ⟨3098501, by rfl⟩ : syracuseStep 4131335 = 6197003) B6197003
theorem B2754223 : Blo 2229435 2754223 := bstep (se 1 (by rfl) ⟨2065667, by rfl⟩ : syracuseStep 2754223 = 4131335) B4131335
theorem B14689189 : Blo 2229435 14689189 := bstep (se 4 (by rfl) ⟨1377111, by rfl⟩ : syracuseStep 14689189 = 2754223) B2754223
theorem B19585585 : Blo 2229435 19585585 := bstep (se 2 (by rfl) ⟨7344594, by rfl⟩ : syracuseStep 19585585 = 14689189) B14689189
theorem B26114113 : Blo 2229435 26114113 := bstep (se 2 (by rfl) ⟨9792792, by rfl⟩ : syracuseStep 26114113 = 19585585) B19585585
theorem B34818817 : Blo 2229435 34818817 := bstep (se 2 (by rfl) ⟨13057056, by rfl⟩ : syracuseStep 34818817 = 26114113) B26114113
theorem B46425089 : Blo 2229435 46425089 := bstep (se 2 (by rfl) ⟨17409408, by rfl⟩ : syracuseStep 46425089 = 34818817) B34818817
theorem B30950059 : Blo 2229435 30950059 := bstep (se 1 (by rfl) ⟨23212544, by rfl⟩ : syracuseStep 30950059 = 46425089) B46425089
theorem B41266745 : Blo 2229435 41266745 := bstep (se 2 (by rfl) ⟨15475029, by rfl⟩ : syracuseStep 41266745 = 30950059) B30950059
theorem B27511163 : Blo 2229435 27511163 := bstep (se 1 (by rfl) ⟨20633372, by rfl⟩ : syracuseStep 27511163 = 41266745) B41266745
theorem B18340775 : Blo 2229435 18340775 := bstep (se 1 (by rfl) ⟨13755581, by rfl⟩ : syracuseStep 18340775 = 27511163) B27511163
theorem B12227183 : Blo 2229435 12227183 := bstep (se 1 (by rfl) ⟨9170387, by rfl⟩ : syracuseStep 12227183 = 18340775) B18340775
theorem B8151455 : Blo 2229435 8151455 := bstep (se 1 (by rfl) ⟨6113591, by rfl⟩ : syracuseStep 8151455 = 12227183) B12227183
theorem B5434303 : Blo 2229435 5434303 := bstep (se 1 (by rfl) ⟨4075727, by rfl⟩ : syracuseStep 5434303 = 8151455) B8151455
theorem B7245737 : Blo 2229435 7245737 := bstep (se 2 (by rfl) ⟨2717151, by rfl⟩ : syracuseStep 7245737 = 5434303) B5434303
theorem B4830491 : Blo 2229435 4830491 := bstep (se 1 (by rfl) ⟨3622868, by rfl⟩ : syracuseStep 4830491 = 7245737) B7245737
theorem B3220327 : Blo 2229435 3220327 := bstep (se 1 (by rfl) ⟨2415245, by rfl⟩ : syracuseStep 3220327 = 4830491) B4830491
theorem B17175077 : Blo 2229435 17175077 := bstep (se 4 (by rfl) ⟨1610163, by rfl⟩ : syracuseStep 17175077 = 3220327) B3220327
theorem B11450051 : Blo 2229435 11450051 := bstep (se 1 (by rfl) ⟨8587538, by rfl⟩ : syracuseStep 11450051 = 17175077) B17175077
theorem B7633367 : Blo 2229435 7633367 := bstep (se 1 (by rfl) ⟨5725025, by rfl⟩ : syracuseStep 7633367 = 11450051) B11450051
theorem B5088911 : Blo 2229435 5088911 := bstep (se 1 (by rfl) ⟨3816683, by rfl⟩ : syracuseStep 5088911 = 7633367) B7633367
theorem B54281717 : Blo 2229435 54281717 := bstep (se 5 (by rfl) ⟨2544455, by rfl⟩ : syracuseStep 54281717 = 5088911) B5088911
theorem B36187811 : Blo 2229435 36187811 := bstep (se 1 (by rfl) ⟨27140858, by rfl⟩ : syracuseStep 36187811 = 54281717) B54281717
theorem B24125207 : Blo 2229435 24125207 := bstep (se 1 (by rfl) ⟨18093905, by rfl⟩ : syracuseStep 24125207 = 36187811) B36187811
theorem B64333885 : Blo 2229435 64333885 := bstep (se 3 (by rfl) ⟨12062603, by rfl⟩ : syracuseStep 64333885 = 24125207) B24125207
theorem B85778513 : Blo 2229435 85778513 := bstep (se 2 (by rfl) ⟨32166942, by rfl⟩ : syracuseStep 85778513 = 64333885) B64333885
theorem B57185675 : Blo 2229435 57185675 := bstep (se 1 (by rfl) ⟨42889256, by rfl⟩ : syracuseStep 57185675 = 85778513) B85778513
theorem B38123783 : Blo 2229435 38123783 := bstep (se 1 (by rfl) ⟨28592837, by rfl⟩ : syracuseStep 38123783 = 57185675) B57185675
theorem B25415855 : Blo 2229435 25415855 := bstep (se 1 (by rfl) ⟨19061891, by rfl⟩ : syracuseStep 25415855 = 38123783) B38123783
theorem B16943903 : Blo 2229435 16943903 := bstep (se 1 (by rfl) ⟨12707927, by rfl⟩ : syracuseStep 16943903 = 25415855) B25415855
theorem B11295935 : Blo 2229435 11295935 := bstep (se 1 (by rfl) ⟨8471951, by rfl⟩ : syracuseStep 11295935 = 16943903) B16943903
theorem B7530623 : Blo 2229435 7530623 := bstep (se 1 (by rfl) ⟨5647967, by rfl⟩ : syracuseStep 7530623 = 11295935) B11295935
theorem B5020415 : Blo 2229435 5020415 := bstep (se 1 (by rfl) ⟨3765311, by rfl⟩ : syracuseStep 5020415 = 7530623) B7530623
theorem B3346943 : Blo 2229435 3346943 := bstep (se 1 (by rfl) ⟨2510207, by rfl⟩ : syracuseStep 3346943 = 5020415) B5020415
theorem B2231295 : Blo 2229435 2231295 := bstep (se 1 (by rfl) ⟨1673471, by rfl⟩ : syracuseStep 2231295 = 3346943) B3346943
theorem B3346949 : Blo 2229435 3346949 := bbase (se 4 (by rfl) ⟨313776, by rfl⟩ : syracuseStep 3346949 = 627553) (by norm_num)
theorem B2231299 : Blo 2229435 2231299 := bstep (se 1 (by rfl) ⟨1673474, by rfl⟩ : syracuseStep 2231299 = 3346949) B3346949
theorem B3765325 : Blo 2229435 3765325 := bbase (se 3 (by rfl) ⟨705998, by rfl⟩ : syracuseStep 3765325 = 1411997) (by norm_num)
theorem B5020433 : Blo 2229435 5020433 := bstep (se 2 (by rfl) ⟨1882662, by rfl⟩ : syracuseStep 5020433 = 3765325) B3765325
theorem B3346955 : Blo 2229435 3346955 := bstep (se 1 (by rfl) ⟨2510216, by rfl⟩ : syracuseStep 3346955 = 5020433) B5020433
theorem B2231303 : Blo 2229435 2231303 := bstep (se 1 (by rfl) ⟨1673477, by rfl⟩ : syracuseStep 2231303 = 3346955) B3346955
theorem B2510221 : Blo 2229435 2510221 := bbase (se 3 (by rfl) ⟨470666, by rfl⟩ : syracuseStep 2510221 = 941333) (by norm_num)
theorem B3346961 : Blo 2229435 3346961 := bstep (se 2 (by rfl) ⟨1255110, by rfl⟩ : syracuseStep 3346961 = 2510221) B2510221
theorem B2231307 : Blo 2229435 2231307 := bstep (se 1 (by rfl) ⟨1673480, by rfl⟩ : syracuseStep 2231307 = 3346961) B3346961
theorem B7530677 : Blo 2229435 7530677 := bbase (se 5 (by rfl) ⟨353000, by rfl⟩ : syracuseStep 7530677 = 706001) (by norm_num)
theorem B5020451 : Blo 2229435 5020451 := bstep (se 1 (by rfl) ⟨3765338, by rfl⟩ : syracuseStep 5020451 = 7530677) B7530677
theorem B3346967 : Blo 2229435 3346967 := bstep (se 1 (by rfl) ⟨2510225, by rfl⟩ : syracuseStep 3346967 = 5020451) B5020451
theorem B2231311 : Blo 2229435 2231311 := bstep (se 1 (by rfl) ⟨1673483, by rfl⟩ : syracuseStep 2231311 = 3346967) B3346967
theorem B3346973 : Blo 2229435 3346973 := bbase (se 3 (by rfl) ⟨627557, by rfl⟩ : syracuseStep 3346973 = 1255115) (by norm_num)
theorem B2231315 : Blo 2229435 2231315 := bstep (se 1 (by rfl) ⟨1673486, by rfl⟩ : syracuseStep 2231315 = 3346973) B3346973
theorem B5020469 : Blo 2229435 5020469 := bbase (se 5 (by rfl) ⟨235334, by rfl⟩ : syracuseStep 5020469 = 470669) (by norm_num)
theorem B3346979 : Blo 2229435 3346979 := bstep (se 1 (by rfl) ⟨2510234, by rfl⟩ : syracuseStep 3346979 = 5020469) B5020469
theorem B2231319 : Blo 2229435 2231319 := bstep (se 1 (by rfl) ⟨1673489, by rfl⟩ : syracuseStep 2231319 = 3346979) B3346979
theorem B3816733 : Blo 2229435 3816733 := bbase (se 3 (by rfl) ⟨715637, by rfl⟩ : syracuseStep 3816733 = 1431275) (by norm_num)
theorem B5088977 : Blo 2229435 5088977 := bstep (se 2 (by rfl) ⟨1908366, by rfl⟩ : syracuseStep 5088977 = 3816733) B3816733
theorem B3392651 : Blo 2229435 3392651 := bstep (se 1 (by rfl) ⟨2544488, by rfl⟩ : syracuseStep 3392651 = 5088977) B5088977
theorem B9047069 : Blo 2229435 9047069 := bstep (se 3 (by rfl) ⟨1696325, by rfl⟩ : syracuseStep 9047069 = 3392651) B3392651
theorem B6031379 : Blo 2229435 6031379 := bstep (se 1 (by rfl) ⟨4523534, by rfl⟩ : syracuseStep 6031379 = 9047069) B9047069
theorem B16083677 : Blo 2229435 16083677 := bstep (se 3 (by rfl) ⟨3015689, by rfl⟩ : syracuseStep 16083677 = 6031379) B6031379
theorem B10722451 : Blo 2229435 10722451 := bstep (se 1 (by rfl) ⟨8041838, by rfl⟩ : syracuseStep 10722451 = 16083677) B16083677
theorem B14296601 : Blo 2229435 14296601 := bstep (se 2 (by rfl) ⟨5361225, by rfl⟩ : syracuseStep 14296601 = 10722451) B10722451
theorem B9531067 : Blo 2229435 9531067 := bstep (se 1 (by rfl) ⟨7148300, by rfl⟩ : syracuseStep 9531067 = 14296601) B14296601
theorem B12708089 : Blo 2229435 12708089 := bstep (se 2 (by rfl) ⟨4765533, by rfl⟩ : syracuseStep 12708089 = 9531067) B9531067
theorem B8472059 : Blo 2229435 8472059 := bstep (se 1 (by rfl) ⟨6354044, by rfl⟩ : syracuseStep 8472059 = 12708089) B12708089
theorem B5648039 : Blo 2229435 5648039 := bstep (se 1 (by rfl) ⟨4236029, by rfl⟩ : syracuseStep 5648039 = 8472059) B8472059
theorem B3765359 : Blo 2229435 3765359 := bstep (se 1 (by rfl) ⟨2824019, by rfl⟩ : syracuseStep 3765359 = 5648039) B5648039
theorem B2510239 : Blo 2229435 2510239 := bstep (se 1 (by rfl) ⟨1882679, by rfl⟩ : syracuseStep 2510239 = 3765359) B3765359
theorem B3346985 : Blo 2229435 3346985 := bstep (se 2 (by rfl) ⟨1255119, by rfl⟩ : syracuseStep 3346985 = 2510239) B2510239
theorem B2231323 : Blo 2229435 2231323 := bstep (se 1 (by rfl) ⟨1673492, by rfl⟩ : syracuseStep 2231323 = 3346985) B3346985
theorem B10722469 : Blo 2229435 10722469 := bbase (se 4 (by rfl) ⟨1005231, by rfl⟩ : syracuseStep 10722469 = 2010463) (by norm_num)
theorem B14296625 : Blo 2229435 14296625 := bstep (se 2 (by rfl) ⟨5361234, by rfl⟩ : syracuseStep 14296625 = 10722469) B10722469
theorem B9531083 : Blo 2229435 9531083 := bstep (se 1 (by rfl) ⟨7148312, by rfl⟩ : syracuseStep 9531083 = 14296625) B14296625
theorem B6354055 : Blo 2229435 6354055 := bstep (se 1 (by rfl) ⟨4765541, by rfl⟩ : syracuseStep 6354055 = 9531083) B9531083
theorem B8472073 : Blo 2229435 8472073 := bstep (se 2 (by rfl) ⟨3177027, by rfl⟩ : syracuseStep 8472073 = 6354055) B6354055
theorem B11296097 : Blo 2229435 11296097 := bstep (se 2 (by rfl) ⟨4236036, by rfl⟩ : syracuseStep 11296097 = 8472073) B8472073
theorem B7530731 : Blo 2229435 7530731 := bstep (se 1 (by rfl) ⟨5648048, by rfl⟩ : syracuseStep 7530731 = 11296097) B11296097
theorem B5020487 : Blo 2229435 5020487 := bstep (se 1 (by rfl) ⟨3765365, by rfl⟩ : syracuseStep 5020487 = 7530731) B7530731
theorem B3346991 : Blo 2229435 3346991 := bstep (se 1 (by rfl) ⟨2510243, by rfl⟩ : syracuseStep 3346991 = 5020487) B5020487
theorem B2231327 : Blo 2229435 2231327 := bstep (se 1 (by rfl) ⟨1673495, by rfl⟩ : syracuseStep 2231327 = 3346991) B3346991
theorem B3346997 : Blo 2229435 3346997 := bbase (se 5 (by rfl) ⟨156890, by rfl⟩ : syracuseStep 3346997 = 313781) (by norm_num)
theorem B2231331 : Blo 2229435 2231331 := bstep (se 1 (by rfl) ⟨1673498, by rfl⟩ : syracuseStep 2231331 = 3346997) B3346997
theorem B5648069 : Blo 2229435 5648069 := bbase (se 4 (by rfl) ⟨529506, by rfl⟩ : syracuseStep 5648069 = 1059013) (by norm_num)
theorem B3765379 : Blo 2229435 3765379 := bstep (se 1 (by rfl) ⟨2824034, by rfl⟩ : syracuseStep 3765379 = 5648069) B5648069
theorem B5020505 : Blo 2229435 5020505 := bstep (se 2 (by rfl) ⟨1882689, by rfl⟩ : syracuseStep 5020505 = 3765379) B3765379
theorem B3347003 : Blo 2229435 3347003 := bstep (se 1 (by rfl) ⟨2510252, by rfl⟩ : syracuseStep 3347003 = 5020505) B5020505
theorem B2231335 : Blo 2229435 2231335 := bstep (se 1 (by rfl) ⟨1673501, by rfl⟩ : syracuseStep 2231335 = 3347003) B3347003
theorem B2510257 : Blo 2229435 2510257 := bbase (se 2 (by rfl) ⟨941346, by rfl⟩ : syracuseStep 2510257 = 1882693) (by norm_num)
theorem B3347009 : Blo 2229435 3347009 := bstep (se 2 (by rfl) ⟨1255128, by rfl⟩ : syracuseStep 3347009 = 2510257) B2510257
theorem B2231339 : Blo 2229435 2231339 := bstep (se 1 (by rfl) ⟨1673504, by rfl⟩ : syracuseStep 2231339 = 3347009) B3347009
theorem B6354101 : Blo 2229435 6354101 := bbase (se 5 (by rfl) ⟨297848, by rfl⟩ : syracuseStep 6354101 = 595697) (by norm_num)
theorem B4236067 : Blo 2229435 4236067 := bstep (se 1 (by rfl) ⟨3177050, by rfl⟩ : syracuseStep 4236067 = 6354101) B6354101
theorem B5648089 : Blo 2229435 5648089 := bstep (se 2 (by rfl) ⟨2118033, by rfl⟩ : syracuseStep 5648089 = 4236067) B4236067
theorem B7530785 : Blo 2229435 7530785 := bstep (se 2 (by rfl) ⟨2824044, by rfl⟩ : syracuseStep 7530785 = 5648089) B5648089
theorem B5020523 : Blo 2229435 5020523 := bstep (se 1 (by rfl) ⟨3765392, by rfl⟩ : syracuseStep 5020523 = 7530785) B7530785
theorem B3347015 : Blo 2229435 3347015 := bstep (se 1 (by rfl) ⟨2510261, by rfl⟩ : syracuseStep 3347015 = 5020523) B5020523
theorem B2231343 : Blo 2229435 2231343 := bstep (se 1 (by rfl) ⟨1673507, by rfl⟩ : syracuseStep 2231343 = 3347015) B3347015
theorem B3347021 : Blo 2229435 3347021 := bbase (se 3 (by rfl) ⟨627566, by rfl⟩ : syracuseStep 3347021 = 1255133) (by norm_num)
theorem B2231347 : Blo 2229435 2231347 := bstep (se 1 (by rfl) ⟨1673510, by rfl⟩ : syracuseStep 2231347 = 3347021) B3347021
theorem B5020541 : Blo 2229435 5020541 := bbase (se 3 (by rfl) ⟨941351, by rfl⟩ : syracuseStep 5020541 = 1882703) (by norm_num)
theorem B3347027 : Blo 2229435 3347027 := bstep (se 1 (by rfl) ⟨2510270, by rfl⟩ : syracuseStep 3347027 = 5020541) B5020541
theorem B2231351 : Blo 2229435 2231351 := bstep (se 1 (by rfl) ⟨1673513, by rfl⟩ : syracuseStep 2231351 = 3347027) B3347027
theorem B3765413 : Blo 2229435 3765413 := bbase (se 4 (by rfl) ⟨353007, by rfl⟩ : syracuseStep 3765413 = 706015) (by norm_num)
theorem B2510275 : Blo 2229435 2510275 := bstep (se 1 (by rfl) ⟨1882706, by rfl⟩ : syracuseStep 2510275 = 3765413) B3765413
theorem B3347033 : Blo 2229435 3347033 := bstep (se 2 (by rfl) ⟨1255137, by rfl⟩ : syracuseStep 3347033 = 2510275) B2510275
theorem B2231355 : Blo 2229435 2231355 := bstep (se 1 (by rfl) ⟨1673516, by rfl⟩ : syracuseStep 2231355 = 3347033) B3347033
theorem B2382805 : Blo 2229435 2382805 := bbase (se 7 (by rfl) ⟨27923, by rfl⟩ : syracuseStep 2382805 = 55847) (by norm_num)
theorem B3177073 : Blo 2229435 3177073 := bstep (se 2 (by rfl) ⟨1191402, by rfl⟩ : syracuseStep 3177073 = 2382805) B2382805
theorem B16944389 : Blo 2229435 16944389 := bstep (se 4 (by rfl) ⟨1588536, by rfl⟩ : syracuseStep 16944389 = 3177073) B3177073
theorem B11296259 : Blo 2229435 11296259 := bstep (se 1 (by rfl) ⟨8472194, by rfl⟩ : syracuseStep 11296259 = 16944389) B16944389
theorem B7530839 : Blo 2229435 7530839 := bstep (se 1 (by rfl) ⟨5648129, by rfl⟩ : syracuseStep 7530839 = 11296259) B11296259
theorem B5020559 : Blo 2229435 5020559 := bstep (se 1 (by rfl) ⟨3765419, by rfl⟩ : syracuseStep 5020559 = 7530839) B7530839
theorem B3347039 : Blo 2229435 3347039 := bstep (se 1 (by rfl) ⟨2510279, by rfl⟩ : syracuseStep 3347039 = 5020559) B5020559
theorem B2231359 : Blo 2229435 2231359 := bstep (se 1 (by rfl) ⟨1673519, by rfl⟩ : syracuseStep 2231359 = 3347039) B3347039
theorem B3347045 : Blo 2229435 3347045 := bbase (se 4 (by rfl) ⟨313785, by rfl⟩ : syracuseStep 3347045 = 627571) (by norm_num)
theorem B2231363 : Blo 2229435 2231363 := bstep (se 1 (by rfl) ⟨1673522, by rfl⟩ : syracuseStep 2231363 = 3347045) B3347045
theorem B3177085 : Blo 2229435 3177085 := bbase (se 3 (by rfl) ⟨595703, by rfl⟩ : syracuseStep 3177085 = 1191407) (by norm_num)
theorem B4236113 : Blo 2229435 4236113 := bstep (se 2 (by rfl) ⟨1588542, by rfl⟩ : syracuseStep 4236113 = 3177085) B3177085
theorem B2824075 : Blo 2229435 2824075 := bstep (se 1 (by rfl) ⟨2118056, by rfl⟩ : syracuseStep 2824075 = 4236113) B4236113
theorem B3765433 : Blo 2229435 3765433 := bstep (se 2 (by rfl) ⟨1412037, by rfl⟩ : syracuseStep 3765433 = 2824075) B2824075
theorem B5020577 : Blo 2229435 5020577 := bstep (se 2 (by rfl) ⟨1882716, by rfl⟩ : syracuseStep 5020577 = 3765433) B3765433
theorem B3347051 : Blo 2229435 3347051 := bstep (se 1 (by rfl) ⟨2510288, by rfl⟩ : syracuseStep 3347051 = 5020577) B5020577
theorem B2231367 : Blo 2229435 2231367 := bstep (se 1 (by rfl) ⟨1673525, by rfl⟩ : syracuseStep 2231367 = 3347051) B3347051
theorem B2510293 : Blo 2229435 2510293 := bbase (se 7 (by rfl) ⟨29417, by rfl⟩ : syracuseStep 2510293 = 58835) (by norm_num)
theorem B3347057 : Blo 2229435 3347057 := bstep (se 2 (by rfl) ⟨1255146, by rfl⟩ : syracuseStep 3347057 = 2510293) B2510293
theorem B2231371 : Blo 2229435 2231371 := bstep (se 1 (by rfl) ⟨1673528, by rfl⟩ : syracuseStep 2231371 = 3347057) B3347057
theorem B2824085 : Blo 2229435 2824085 := bbase (se 6 (by rfl) ⟨66189, by rfl⟩ : syracuseStep 2824085 = 132379) (by norm_num)
theorem B7530893 : Blo 2229435 7530893 := bstep (se 3 (by rfl) ⟨1412042, by rfl⟩ : syracuseStep 7530893 = 2824085) B2824085
theorem B5020595 : Blo 2229435 5020595 := bstep (se 1 (by rfl) ⟨3765446, by rfl⟩ : syracuseStep 5020595 = 7530893) B7530893
theorem B3347063 : Blo 2229435 3347063 := bstep (se 1 (by rfl) ⟨2510297, by rfl⟩ : syracuseStep 3347063 = 5020595) B5020595
theorem B2231375 : Blo 2229435 2231375 := bstep (se 1 (by rfl) ⟨1673531, by rfl⟩ : syracuseStep 2231375 = 3347063) B3347063
theorem B3347069 : Blo 2229435 3347069 := bbase (se 3 (by rfl) ⟨627575, by rfl⟩ : syracuseStep 3347069 = 1255151) (by norm_num)
theorem B2231379 : Blo 2229435 2231379 := bstep (se 1 (by rfl) ⟨1673534, by rfl⟩ : syracuseStep 2231379 = 3347069) B3347069
theorem B5020613 : Blo 2229435 5020613 := bbase (se 4 (by rfl) ⟨470682, by rfl⟩ : syracuseStep 5020613 = 941365) (by norm_num)
theorem B3347075 : Blo 2229435 3347075 := bstep (se 1 (by rfl) ⟨2510306, by rfl⟩ : syracuseStep 3347075 = 5020613) B5020613
theorem B2231383 : Blo 2229435 2231383 := bstep (se 1 (by rfl) ⟨1673537, by rfl⟩ : syracuseStep 2231383 = 3347075) B3347075
theorem B3574253 : Blo 2229435 3574253 := bbase (se 3 (by rfl) ⟨670172, by rfl⟩ : syracuseStep 3574253 = 1340345) (by norm_num)
theorem B9531341 : Blo 2229435 9531341 := bstep (se 3 (by rfl) ⟨1787126, by rfl⟩ : syracuseStep 9531341 = 3574253) B3574253
theorem B6354227 : Blo 2229435 6354227 := bstep (se 1 (by rfl) ⟨4765670, by rfl⟩ : syracuseStep 6354227 = 9531341) B9531341
theorem B4236151 : Blo 2229435 4236151 := bstep (se 1 (by rfl) ⟨3177113, by rfl⟩ : syracuseStep 4236151 = 6354227) B6354227
theorem B5648201 : Blo 2229435 5648201 := bstep (se 2 (by rfl) ⟨2118075, by rfl⟩ : syracuseStep 5648201 = 4236151) B4236151
theorem B3765467 : Blo 2229435 3765467 := bstep (se 1 (by rfl) ⟨2824100, by rfl⟩ : syracuseStep 3765467 = 5648201) B5648201
theorem B2510311 : Blo 2229435 2510311 := bstep (se 1 (by rfl) ⟨1882733, by rfl⟩ : syracuseStep 2510311 = 3765467) B3765467
theorem B3347081 : Blo 2229435 3347081 := bstep (se 2 (by rfl) ⟨1255155, by rfl⟩ : syracuseStep 3347081 = 2510311) B2510311
theorem B2231387 : Blo 2229435 2231387 := bstep (se 1 (by rfl) ⟨1673540, by rfl⟩ : syracuseStep 2231387 = 3347081) B3347081
theorem B11296421 : Blo 2229435 11296421 := bbase (se 4 (by rfl) ⟨1059039, by rfl⟩ : syracuseStep 11296421 = 2118079) (by norm_num)
theorem B7530947 : Blo 2229435 7530947 := bstep (se 1 (by rfl) ⟨5648210, by rfl⟩ : syracuseStep 7530947 = 11296421) B11296421
theorem B5020631 : Blo 2229435 5020631 := bstep (se 1 (by rfl) ⟨3765473, by rfl⟩ : syracuseStep 5020631 = 7530947) B7530947
theorem B3347087 : Blo 2229435 3347087 := bstep (se 1 (by rfl) ⟨2510315, by rfl⟩ : syracuseStep 3347087 = 5020631) B5020631
theorem B2231391 : Blo 2229435 2231391 := bstep (se 1 (by rfl) ⟨1673543, by rfl⟩ : syracuseStep 2231391 = 3347087) B3347087
theorem B3347093 : Blo 2229435 3347093 := bbase (se 6 (by rfl) ⟨78447, by rfl⟩ : syracuseStep 3347093 = 156895) (by norm_num)
theorem B2231395 : Blo 2229435 2231395 := bstep (se 1 (by rfl) ⟨1673546, by rfl⟩ : syracuseStep 2231395 = 3347093) B3347093
theorem B5372621 : Blo 2229435 5372621 := bbase (se 3 (by rfl) ⟨1007366, by rfl⟩ : syracuseStep 5372621 = 2014733) (by norm_num)
theorem B3581747 : Blo 2229435 3581747 := bstep (se 1 (by rfl) ⟨2686310, by rfl⟩ : syracuseStep 3581747 = 5372621) B5372621
theorem B2387831 : Blo 2229435 2387831 := bstep (se 1 (by rfl) ⟨1790873, by rfl⟩ : syracuseStep 2387831 = 3581747) B3581747
theorem B25470197 : Blo 2229435 25470197 := bstep (se 5 (by rfl) ⟨1193915, by rfl⟩ : syracuseStep 25470197 = 2387831) B2387831
theorem B16980131 : Blo 2229435 16980131 := bstep (se 1 (by rfl) ⟨12735098, by rfl⟩ : syracuseStep 16980131 = 25470197) B25470197
theorem B11320087 : Blo 2229435 11320087 := bstep (se 1 (by rfl) ⟨8490065, by rfl⟩ : syracuseStep 11320087 = 16980131) B16980131
theorem B15093449 : Blo 2229435 15093449 := bstep (se 2 (by rfl) ⟨5660043, by rfl⟩ : syracuseStep 15093449 = 11320087) B11320087
theorem B10062299 : Blo 2229435 10062299 := bstep (se 1 (by rfl) ⟨7546724, by rfl⟩ : syracuseStep 10062299 = 15093449) B15093449
theorem B6708199 : Blo 2229435 6708199 := bstep (se 1 (by rfl) ⟨5031149, by rfl⟩ : syracuseStep 6708199 = 10062299) B10062299
theorem B8944265 : Blo 2229435 8944265 := bstep (se 2 (by rfl) ⟨3354099, by rfl⟩ : syracuseStep 8944265 = 6708199) B6708199
theorem B5962843 : Blo 2229435 5962843 := bstep (se 1 (by rfl) ⟨4472132, by rfl⟩ : syracuseStep 5962843 = 8944265) B8944265
theorem B7950457 : Blo 2229435 7950457 := bstep (se 2 (by rfl) ⟨2981421, by rfl⟩ : syracuseStep 7950457 = 5962843) B5962843
theorem B42402437 : Blo 2229435 42402437 := bstep (se 4 (by rfl) ⟨3975228, by rfl⟩ : syracuseStep 42402437 = 7950457) B7950457
theorem B28268291 : Blo 2229435 28268291 := bstep (se 1 (by rfl) ⟨21201218, by rfl⟩ : syracuseStep 28268291 = 42402437) B42402437
theorem B75382109 : Blo 2229435 75382109 := bstep (se 3 (by rfl) ⟨14134145, by rfl⟩ : syracuseStep 75382109 = 28268291) B28268291
theorem B50254739 : Blo 2229435 50254739 := bstep (se 1 (by rfl) ⟨37691054, by rfl⟩ : syracuseStep 50254739 = 75382109) B75382109
theorem B33503159 : Blo 2229435 33503159 := bstep (se 1 (by rfl) ⟨25127369, by rfl⟩ : syracuseStep 33503159 = 50254739) B50254739
theorem B22335439 : Blo 2229435 22335439 := bstep (se 1 (by rfl) ⟨16751579, by rfl⟩ : syracuseStep 22335439 = 33503159) B33503159
theorem B29780585 : Blo 2229435 29780585 := bstep (se 2 (by rfl) ⟨11167719, by rfl⟩ : syracuseStep 29780585 = 22335439) B22335439
theorem B19853723 : Blo 2229435 19853723 := bstep (se 1 (by rfl) ⟨14890292, by rfl⟩ : syracuseStep 19853723 = 29780585) B29780585
theorem B13235815 : Blo 2229435 13235815 := bstep (se 1 (by rfl) ⟨9926861, by rfl⟩ : syracuseStep 13235815 = 19853723) B19853723
theorem B17647753 : Blo 2229435 17647753 := bstep (se 2 (by rfl) ⟨6617907, by rfl⟩ : syracuseStep 17647753 = 13235815) B13235815
theorem B23530337 : Blo 2229435 23530337 := bstep (se 2 (by rfl) ⟨8823876, by rfl⟩ : syracuseStep 23530337 = 17647753) B17647753
theorem B15686891 : Blo 2229435 15686891 := bstep (se 1 (by rfl) ⟨11765168, by rfl⟩ : syracuseStep 15686891 = 23530337) B23530337
theorem B10457927 : Blo 2229435 10457927 := bstep (se 1 (by rfl) ⟨7843445, by rfl⟩ : syracuseStep 10457927 = 15686891) B15686891
theorem B6971951 : Blo 2229435 6971951 := bstep (se 1 (by rfl) ⟨5228963, by rfl⟩ : syracuseStep 6971951 = 10457927) B10457927
theorem B18591869 : Blo 2229435 18591869 := bstep (se 3 (by rfl) ⟨3485975, by rfl⟩ : syracuseStep 18591869 = 6971951) B6971951
theorem B12394579 : Blo 2229435 12394579 := bstep (se 1 (by rfl) ⟨9295934, by rfl⟩ : syracuseStep 12394579 = 18591869) B18591869
theorem B16526105 : Blo 2229435 16526105 := bstep (se 2 (by rfl) ⟨6197289, by rfl⟩ : syracuseStep 16526105 = 12394579) B12394579
theorem B11017403 : Blo 2229435 11017403 := bstep (se 1 (by rfl) ⟨8263052, by rfl⟩ : syracuseStep 11017403 = 16526105) B16526105
theorem B7344935 : Blo 2229435 7344935 := bstep (se 1 (by rfl) ⟨5508701, by rfl⟩ : syracuseStep 7344935 = 11017403) B11017403
theorem B4896623 : Blo 2229435 4896623 := bstep (se 1 (by rfl) ⟨3672467, by rfl⟩ : syracuseStep 4896623 = 7344935) B7344935
theorem B13057661 : Blo 2229435 13057661 := bstep (se 3 (by rfl) ⟨2448311, by rfl⟩ : syracuseStep 13057661 = 4896623) B4896623
theorem B8705107 : Blo 2229435 8705107 := bstep (se 1 (by rfl) ⟨6528830, by rfl⟩ : syracuseStep 8705107 = 13057661) B13057661
theorem B11606809 : Blo 2229435 11606809 := bstep (se 2 (by rfl) ⟨4352553, by rfl⟩ : syracuseStep 11606809 = 8705107) B8705107
theorem B15475745 : Blo 2229435 15475745 := bstep (se 2 (by rfl) ⟨5803404, by rfl⟩ : syracuseStep 15475745 = 11606809) B11606809
theorem B41268653 : Blo 2229435 41268653 := bstep (se 3 (by rfl) ⟨7737872, by rfl⟩ : syracuseStep 41268653 = 15475745) B15475745
theorem B440198965 : Blo 2229435 440198965 := bstep (se 5 (by rfl) ⟨20634326, by rfl⟩ : syracuseStep 440198965 = 41268653) B41268653
theorem B586931953 : Blo 2229435 586931953 := bstep (se 2 (by rfl) ⟨220099482, by rfl⟩ : syracuseStep 586931953 = 440198965) B440198965
theorem B782575937 : Blo 2229435 782575937 := bstep (se 2 (by rfl) ⟨293465976, by rfl⟩ : syracuseStep 782575937 = 586931953) B586931953
theorem B521717291 : Blo 2229435 521717291 := bstep (se 1 (by rfl) ⟨391287968, by rfl⟩ : syracuseStep 521717291 = 782575937) B782575937
theorem B347811527 : Blo 2229435 347811527 := bstep (se 1 (by rfl) ⟨260858645, by rfl⟩ : syracuseStep 347811527 = 521717291) B521717291
theorem B927497405 : Blo 2229435 927497405 := bstep (se 3 (by rfl) ⟨173905763, by rfl⟩ : syracuseStep 927497405 = 347811527) B347811527
theorem B618331603 : Blo 2229435 618331603 := bstep (se 1 (by rfl) ⟨463748702, by rfl⟩ : syracuseStep 618331603 = 927497405) B927497405
theorem B824442137 : Blo 2229435 824442137 := bstep (se 2 (by rfl) ⟨309165801, by rfl⟩ : syracuseStep 824442137 = 618331603) B618331603
theorem B549628091 : Blo 2229435 549628091 := bstep (se 1 (by rfl) ⟨412221068, by rfl⟩ : syracuseStep 549628091 = 824442137) B824442137
theorem B366418727 : Blo 2229435 366418727 := bstep (se 1 (by rfl) ⟨274814045, by rfl⟩ : syracuseStep 366418727 = 549628091) B549628091
theorem B244279151 : Blo 2229435 244279151 := bstep (se 1 (by rfl) ⟨183209363, by rfl⟩ : syracuseStep 244279151 = 366418727) B366418727
theorem B162852767 : Blo 2229435 162852767 := bstep (se 1 (by rfl) ⟨122139575, by rfl⟩ : syracuseStep 162852767 = 244279151) B244279151
theorem B108568511 : Blo 2229435 108568511 := bstep (se 1 (by rfl) ⟨81426383, by rfl⟩ : syracuseStep 108568511 = 162852767) B162852767
theorem B72379007 : Blo 2229435 72379007 := bstep (se 1 (by rfl) ⟨54284255, by rfl⟩ : syracuseStep 72379007 = 108568511) B108568511
theorem B48252671 : Blo 2229435 48252671 := bstep (se 1 (by rfl) ⟨36189503, by rfl⟩ : syracuseStep 48252671 = 72379007) B72379007
theorem B32168447 : Blo 2229435 32168447 := bstep (se 1 (by rfl) ⟨24126335, by rfl⟩ : syracuseStep 32168447 = 48252671) B48252671
theorem B21445631 : Blo 2229435 21445631 := bstep (se 1 (by rfl) ⟨16084223, by rfl⟩ : syracuseStep 21445631 = 32168447) B32168447
theorem B14297087 : Blo 2229435 14297087 := bstep (se 1 (by rfl) ⟨10722815, by rfl⟩ : syracuseStep 14297087 = 21445631) B21445631
theorem B9531391 : Blo 2229435 9531391 := bstep (se 1 (by rfl) ⟨7148543, by rfl⟩ : syracuseStep 9531391 = 14297087) B14297087
theorem B12708521 : Blo 2229435 12708521 := bstep (se 2 (by rfl) ⟨4765695, by rfl⟩ : syracuseStep 12708521 = 9531391) B9531391
theorem B8472347 : Blo 2229435 8472347 := bstep (se 1 (by rfl) ⟨6354260, by rfl⟩ : syracuseStep 8472347 = 12708521) B12708521
theorem B5648231 : Blo 2229435 5648231 := bstep (se 1 (by rfl) ⟨4236173, by rfl⟩ : syracuseStep 5648231 = 8472347) B8472347
theorem B3765487 : Blo 2229435 3765487 := bstep (se 1 (by rfl) ⟨2824115, by rfl⟩ : syracuseStep 3765487 = 5648231) B5648231
theorem B5020649 : Blo 2229435 5020649 := bstep (se 2 (by rfl) ⟨1882743, by rfl⟩ : syracuseStep 5020649 = 3765487) B3765487
theorem B3347099 : Blo 2229435 3347099 := bstep (se 1 (by rfl) ⟨2510324, by rfl⟩ : syracuseStep 3347099 = 5020649) B5020649
theorem B2231399 : Blo 2229435 2231399 := bstep (se 1 (by rfl) ⟨1673549, by rfl⟩ : syracuseStep 2231399 = 3347099) B3347099
theorem B2510329 : Blo 2229435 2510329 := bbase (se 2 (by rfl) ⟨941373, by rfl⟩ : syracuseStep 2510329 = 1882747) (by norm_num)
theorem B3347105 : Blo 2229435 3347105 := bstep (se 2 (by rfl) ⟨1255164, by rfl⟩ : syracuseStep 3347105 = 2510329) B2510329
theorem B2231403 : Blo 2229435 2231403 := bstep (se 1 (by rfl) ⟨1673552, by rfl⟩ : syracuseStep 2231403 = 3347105) B3347105
theorem B3816877 : Blo 2229435 3816877 := bbase (se 3 (by rfl) ⟨715664, by rfl⟩ : syracuseStep 3816877 = 1431329) (by norm_num)
theorem B5089169 : Blo 2229435 5089169 := bstep (se 2 (by rfl) ⟨1908438, by rfl⟩ : syracuseStep 5089169 = 3816877) B3816877
theorem B3392779 : Blo 2229435 3392779 := bstep (se 1 (by rfl) ⟨2544584, by rfl⟩ : syracuseStep 3392779 = 5089169) B5089169
theorem B4523705 : Blo 2229435 4523705 := bstep (se 2 (by rfl) ⟨1696389, by rfl⟩ : syracuseStep 4523705 = 3392779) B3392779
theorem B3015803 : Blo 2229435 3015803 := bstep (se 1 (by rfl) ⟨2261852, by rfl⟩ : syracuseStep 3015803 = 4523705) B4523705
theorem B8042141 : Blo 2229435 8042141 := bstep (se 3 (by rfl) ⟨1507901, by rfl⟩ : syracuseStep 8042141 = 3015803) B3015803
theorem B5361427 : Blo 2229435 5361427 := bstep (se 1 (by rfl) ⟨4021070, by rfl⟩ : syracuseStep 5361427 = 8042141) B8042141
theorem B7148569 : Blo 2229435 7148569 := bstep (se 2 (by rfl) ⟨2680713, by rfl⟩ : syracuseStep 7148569 = 5361427) B5361427
theorem B9531425 : Blo 2229435 9531425 := bstep (se 2 (by rfl) ⟨3574284, by rfl⟩ : syracuseStep 9531425 = 7148569) B7148569
theorem B6354283 : Blo 2229435 6354283 := bstep (se 1 (by rfl) ⟨4765712, by rfl⟩ : syracuseStep 6354283 = 9531425) B9531425
theorem B8472377 : Blo 2229435 8472377 := bstep (se 2 (by rfl) ⟨3177141, by rfl⟩ : syracuseStep 8472377 = 6354283) B6354283
theorem B5648251 : Blo 2229435 5648251 := bstep (se 1 (by rfl) ⟨4236188, by rfl⟩ : syracuseStep 5648251 = 8472377) B8472377
theorem B7531001 : Blo 2229435 7531001 := bstep (se 2 (by rfl) ⟨2824125, by rfl⟩ : syracuseStep 7531001 = 5648251) B5648251
theorem B5020667 : Blo 2229435 5020667 := bstep (se 1 (by rfl) ⟨3765500, by rfl⟩ : syracuseStep 5020667 = 7531001) B7531001
theorem B3347111 : Blo 2229435 3347111 := bstep (se 1 (by rfl) ⟨2510333, by rfl⟩ : syracuseStep 3347111 = 5020667) B5020667
theorem B2231407 : Blo 2229435 2231407 := bstep (se 1 (by rfl) ⟨1673555, by rfl⟩ : syracuseStep 2231407 = 3347111) B3347111
theorem B3347117 : Blo 2229435 3347117 := bbase (se 3 (by rfl) ⟨627584, by rfl⟩ : syracuseStep 3347117 = 1255169) (by norm_num)
theorem B2231411 : Blo 2229435 2231411 := bstep (se 1 (by rfl) ⟨1673558, by rfl⟩ : syracuseStep 2231411 = 3347117) B3347117
theorem B5020685 : Blo 2229435 5020685 := bbase (se 3 (by rfl) ⟨941378, by rfl⟩ : syracuseStep 5020685 = 1882757) (by norm_num)
theorem B3347123 : Blo 2229435 3347123 := bstep (se 1 (by rfl) ⟨2510342, by rfl⟩ : syracuseStep 3347123 = 5020685) B5020685
theorem B2231415 : Blo 2229435 2231415 := bstep (se 1 (by rfl) ⟨1673561, by rfl⟩ : syracuseStep 2231415 = 3347123) B3347123
theorem B2824141 : Blo 2229435 2824141 := bbase (se 3 (by rfl) ⟨529526, by rfl⟩ : syracuseStep 2824141 = 1059053) (by norm_num)
theorem B3765521 : Blo 2229435 3765521 := bstep (se 2 (by rfl) ⟨1412070, by rfl⟩ : syracuseStep 3765521 = 2824141) B2824141
theorem B2510347 : Blo 2229435 2510347 := bstep (se 1 (by rfl) ⟨1882760, by rfl⟩ : syracuseStep 2510347 = 3765521) B3765521
theorem B3347129 : Blo 2229435 3347129 := bstep (se 2 (by rfl) ⟨1255173, by rfl⟩ : syracuseStep 3347129 = 2510347) B2510347
theorem B2231419 : Blo 2229435 2231419 := bstep (se 1 (by rfl) ⟨1673564, by rfl⟩ : syracuseStep 2231419 = 3347129) B3347129
theorem B32168789 : Blo 2229435 32168789 := bbase (se 9 (by rfl) ⟨94244, by rfl⟩ : syracuseStep 32168789 = 188489) (by norm_num)
theorem B21445859 : Blo 2229435 21445859 := bstep (se 1 (by rfl) ⟨16084394, by rfl⟩ : syracuseStep 21445859 = 32168789) B32168789
theorem B14297239 : Blo 2229435 14297239 := bstep (se 1 (by rfl) ⟨10722929, by rfl⟩ : syracuseStep 14297239 = 21445859) B21445859
theorem B19062985 : Blo 2229435 19062985 := bstep (se 2 (by rfl) ⟨7148619, by rfl⟩ : syracuseStep 19062985 = 14297239) B14297239
theorem B25417313 : Blo 2229435 25417313 := bstep (se 2 (by rfl) ⟨9531492, by rfl⟩ : syracuseStep 25417313 = 19062985) B19062985
theorem B16944875 : Blo 2229435 16944875 := bstep (se 1 (by rfl) ⟨12708656, by rfl⟩ : syracuseStep 16944875 = 25417313) B25417313
theorem B11296583 : Blo 2229435 11296583 := bstep (se 1 (by rfl) ⟨8472437, by rfl⟩ : syracuseStep 11296583 = 16944875) B16944875
theorem B7531055 : Blo 2229435 7531055 := bstep (se 1 (by rfl) ⟨5648291, by rfl⟩ : syracuseStep 7531055 = 11296583) B11296583
theorem B5020703 : Blo 2229435 5020703 := bstep (se 1 (by rfl) ⟨3765527, by rfl⟩ : syracuseStep 5020703 = 7531055) B7531055
theorem B3347135 : Blo 2229435 3347135 := bstep (se 1 (by rfl) ⟨2510351, by rfl⟩ : syracuseStep 3347135 = 5020703) B5020703
theorem B2231423 : Blo 2229435 2231423 := bstep (se 1 (by rfl) ⟨1673567, by rfl⟩ : syracuseStep 2231423 = 3347135) B3347135
theorem B3347141 : Blo 2229435 3347141 := bbase (se 4 (by rfl) ⟨313794, by rfl⟩ : syracuseStep 3347141 = 627589) (by norm_num)
theorem B2231427 : Blo 2229435 2231427 := bstep (se 1 (by rfl) ⟨1673570, by rfl⟩ : syracuseStep 2231427 = 3347141) B3347141
theorem B3765541 : Blo 2229435 3765541 := bbase (se 4 (by rfl) ⟨353019, by rfl⟩ : syracuseStep 3765541 = 706039) (by norm_num)
theorem B5020721 : Blo 2229435 5020721 := bstep (se 2 (by rfl) ⟨1882770, by rfl⟩ : syracuseStep 5020721 = 3765541) B3765541
theorem B3347147 : Blo 2229435 3347147 := bstep (se 1 (by rfl) ⟨2510360, by rfl⟩ : syracuseStep 3347147 = 5020721) B5020721
theorem B2231431 : Blo 2229435 2231431 := bstep (se 1 (by rfl) ⟨1673573, by rfl⟩ : syracuseStep 2231431 = 3347147) B3347147
theorem B2510365 : Blo 2229435 2510365 := bbase (se 3 (by rfl) ⟨470693, by rfl⟩ : syracuseStep 2510365 = 941387) (by norm_num)
theorem B3347153 : Blo 2229435 3347153 := bstep (se 2 (by rfl) ⟨1255182, by rfl⟩ : syracuseStep 3347153 = 2510365) B2510365
theorem B2231435 : Blo 2229435 2231435 := bstep (se 1 (by rfl) ⟨1673576, by rfl⟩ : syracuseStep 2231435 = 3347153) B3347153
theorem C0 (j : ℕ) (h1 : 557358 ≤ j) (h2 : j ≤ 557858) : Blo 2229435 (4 * j + 3) := by
  interval_cases j
  · exact B2229435
  · exact B2229439
  · exact B2229443
  · exact B2229447
  · exact B2229451
  · exact B2229455
  · exact B2229459
  · exact B2229463
  · exact B2229467
  · exact B2229471
  · exact B2229475
  · exact B2229479
  · exact B2229483
  · exact B2229487
  · exact B2229491
  · exact B2229495
  · exact B2229499
  · exact B2229503
  · exact B2229507
  · exact B2229511
  · exact B2229515
  · exact B2229519
  · exact B2229523
  · exact B2229527
  · exact B2229531
  · exact B2229535
  · exact B2229539
  · exact B2229543
  · exact B2229547
  · exact B2229551
  · exact B2229555
  · exact B2229559
  · exact B2229563
  · exact B2229567
  · exact B2229571
  · exact B2229575
  · exact B2229579
  · exact B2229583
  · exact B2229587
  · exact B2229591
  · exact B2229595
  · exact B2229599
  · exact B2229603
  · exact B2229607
  · exact B2229611
  · exact B2229615
  · exact B2229619
  · exact B2229623
  · exact B2229627
  · exact B2229631
  · exact B2229635
  · exact B2229639
  · exact B2229643
  · exact B2229647
  · exact B2229651
  · exact B2229655
  · exact B2229659
  · exact B2229663
  · exact B2229667
  · exact B2229671
  · exact B2229675
  · exact B2229679
  · exact B2229683
  · exact B2229687
  · exact B2229691
  · exact B2229695
  · exact B2229699
  · exact B2229703
  · exact B2229707
  · exact B2229711
  · exact B2229715
  · exact B2229719
  · exact B2229723
  · exact B2229727
  · exact B2229731
  · exact B2229735
  · exact B2229739
  · exact B2229743
  · exact B2229747
  · exact B2229751
  · exact B2229755
  · exact B2229759
  · exact B2229763
  · exact B2229767
  · exact B2229771
  · exact B2229775
  · exact B2229779
  · exact B2229783
  · exact B2229787
  · exact B2229791
  · exact B2229795
  · exact B2229799
  · exact B2229803
  · exact B2229807
  · exact B2229811
  · exact B2229815
  · exact B2229819
  · exact B2229823
  · exact B2229827
  · exact B2229831
  · exact B2229835
  · exact B2229839
  · exact B2229843
  · exact B2229847
  · exact B2229851
  · exact B2229855
  · exact B2229859
  · exact B2229863
  · exact B2229867
  · exact B2229871
  · exact B2229875
  · exact B2229879
  · exact B2229883
  · exact B2229887
  · exact B2229891
  · exact B2229895
  · exact B2229899
  · exact B2229903
  · exact B2229907
  · exact B2229911
  · exact B2229915
  · exact B2229919
  · exact B2229923
  · exact B2229927
  · exact B2229931
  · exact B2229935
  · exact B2229939
  · exact B2229943
  · exact B2229947
  · exact B2229951
  · exact B2229955
  · exact B2229959
  · exact B2229963
  · exact B2229967
  · exact B2229971
  · exact B2229975
  · exact B2229979
  · exact B2229983
  · exact B2229987
  · exact B2229991
  · exact B2229995
  · exact B2229999
  · exact B2230003
  · exact B2230007
  · exact B2230011
  · exact B2230015
  · exact B2230019
  · exact B2230023
  · exact B2230027
  · exact B2230031
  · exact B2230035
  · exact B2230039
  · exact B2230043
  · exact B2230047
  · exact B2230051
  · exact B2230055
  · exact B2230059
  · exact B2230063
  · exact B2230067
  · exact B2230071
  · exact B2230075
  · exact B2230079
  · exact B2230083
  · exact B2230087
  · exact B2230091
  · exact B2230095
  · exact B2230099
  · exact B2230103
  · exact B2230107
  · exact B2230111
  · exact B2230115
  · exact B2230119
  · exact B2230123
  · exact B2230127
  · exact B2230131
  · exact B2230135
  · exact B2230139
  · exact B2230143
  · exact B2230147
  · exact B2230151
  · exact B2230155
  · exact B2230159
  · exact B2230163
  · exact B2230167
  · exact B2230171
  · exact B2230175
  · exact B2230179
  · exact B2230183
  · exact B2230187
  · exact B2230191
  · exact B2230195
  · exact B2230199
  · exact B2230203
  · exact B2230207
  · exact B2230211
  · exact B2230215
  · exact B2230219
  · exact B2230223
  · exact B2230227
  · exact B2230231
  · exact B2230235
  · exact B2230239
  · exact B2230243
  · exact B2230247
  · exact B2230251
  · exact B2230255
  · exact B2230259
  · exact B2230263
  · exact B2230267
  · exact B2230271
  · exact B2230275
  · exact B2230279
  · exact B2230283
  · exact B2230287
  · exact B2230291
  · exact B2230295
  · exact B2230299
  · exact B2230303
  · exact B2230307
  · exact B2230311
  · exact B2230315
  · exact B2230319
  · exact B2230323
  · exact B2230327
  · exact B2230331
  · exact B2230335
  · exact B2230339
  · exact B2230343
  · exact B2230347
  · exact B2230351
  · exact B2230355
  · exact B2230359
  · exact B2230363
  · exact B2230367
  · exact B2230371
  · exact B2230375
  · exact B2230379
  · exact B2230383
  · exact B2230387
  · exact B2230391
  · exact B2230395
  · exact B2230399
  · exact B2230403
  · exact B2230407
  · exact B2230411
  · exact B2230415
  · exact B2230419
  · exact B2230423
  · exact B2230427
  · exact B2230431
  · exact B2230435
  · exact B2230439
  · exact B2230443
  · exact B2230447
  · exact B2230451
  · exact B2230455
  · exact B2230459
  · exact B2230463
  · exact B2230467
  · exact B2230471
  · exact B2230475
  · exact B2230479
  · exact B2230483
  · exact B2230487
  · exact B2230491
  · exact B2230495
  · exact B2230499
  · exact B2230503
  · exact B2230507
  · exact B2230511
  · exact B2230515
  · exact B2230519
  · exact B2230523
  · exact B2230527
  · exact B2230531
  · exact B2230535
  · exact B2230539
  · exact B2230543
  · exact B2230547
  · exact B2230551
  · exact B2230555
  · exact B2230559
  · exact B2230563
  · exact B2230567
  · exact B2230571
  · exact B2230575
  · exact B2230579
  · exact B2230583
  · exact B2230587
  · exact B2230591
  · exact B2230595
  · exact B2230599
  · exact B2230603
  · exact B2230607
  · exact B2230611
  · exact B2230615
  · exact B2230619
  · exact B2230623
  · exact B2230627
  · exact B2230631
  · exact B2230635
  · exact B2230639
  · exact B2230643
  · exact B2230647
  · exact B2230651
  · exact B2230655
  · exact B2230659
  · exact B2230663
  · exact B2230667
  · exact B2230671
  · exact B2230675
  · exact B2230679
  · exact B2230683
  · exact B2230687
  · exact B2230691
  · exact B2230695
  · exact B2230699
  · exact B2230703
  · exact B2230707
  · exact B2230711
  · exact B2230715
  · exact B2230719
  · exact B2230723
  · exact B2230727
  · exact B2230731
  · exact B2230735
  · exact B2230739
  · exact B2230743
  · exact B2230747
  · exact B2230751
  · exact B2230755
  · exact B2230759
  · exact B2230763
  · exact B2230767
  · exact B2230771
  · exact B2230775
  · exact B2230779
  · exact B2230783
  · exact B2230787
  · exact B2230791
  · exact B2230795
  · exact B2230799
  · exact B2230803
  · exact B2230807
  · exact B2230811
  · exact B2230815
  · exact B2230819
  · exact B2230823
  · exact B2230827
  · exact B2230831
  · exact B2230835
  · exact B2230839
  · exact B2230843
  · exact B2230847
  · exact B2230851
  · exact B2230855
  · exact B2230859
  · exact B2230863
  · exact B2230867
  · exact B2230871
  · exact B2230875
  · exact B2230879
  · exact B2230883
  · exact B2230887
  · exact B2230891
  · exact B2230895
  · exact B2230899
  · exact B2230903
  · exact B2230907
  · exact B2230911
  · exact B2230915
  · exact B2230919
  · exact B2230923
  · exact B2230927
  · exact B2230931
  · exact B2230935
  · exact B2230939
  · exact B2230943
  · exact B2230947
  · exact B2230951
  · exact B2230955
  · exact B2230959
  · exact B2230963
  · exact B2230967
  · exact B2230971
  · exact B2230975
  · exact B2230979
  · exact B2230983
  · exact B2230987
  · exact B2230991
  · exact B2230995
  · exact B2230999
  · exact B2231003
  · exact B2231007
  · exact B2231011
  · exact B2231015
  · exact B2231019
  · exact B2231023
  · exact B2231027
  · exact B2231031
  · exact B2231035
  · exact B2231039
  · exact B2231043
  · exact B2231047
  · exact B2231051
  · exact B2231055
  · exact B2231059
  · exact B2231063
  · exact B2231067
  · exact B2231071
  · exact B2231075
  · exact B2231079
  · exact B2231083
  · exact B2231087
  · exact B2231091
  · exact B2231095
  · exact B2231099
  · exact B2231103
  · exact B2231107
  · exact B2231111
  · exact B2231115
  · exact B2231119
  · exact B2231123
  · exact B2231127
  · exact B2231131
  · exact B2231135
  · exact B2231139
  · exact B2231143
  · exact B2231147
  · exact B2231151
  · exact B2231155
  · exact B2231159
  · exact B2231163
  · exact B2231167
  · exact B2231171
  · exact B2231175
  · exact B2231179
  · exact B2231183
  · exact B2231187
  · exact B2231191
  · exact B2231195
  · exact B2231199
  · exact B2231203
  · exact B2231207
  · exact B2231211
  · exact B2231215
  · exact B2231219
  · exact B2231223
  · exact B2231227
  · exact B2231231
  · exact B2231235
  · exact B2231239
  · exact B2231243
  · exact B2231247
  · exact B2231251
  · exact B2231255
  · exact B2231259
  · exact B2231263
  · exact B2231267
  · exact B2231271
  · exact B2231275
  · exact B2231279
  · exact B2231283
  · exact B2231287
  · exact B2231291
  · exact B2231295
  · exact B2231299
  · exact B2231303
  · exact B2231307
  · exact B2231311
  · exact B2231315
  · exact B2231319
  · exact B2231323
  · exact B2231327
  · exact B2231331
  · exact B2231335
  · exact B2231339
  · exact B2231343
  · exact B2231347
  · exact B2231351
  · exact B2231355
  · exact B2231359
  · exact B2231363
  · exact B2231367
  · exact B2231371
  · exact B2231375
  · exact B2231379
  · exact B2231383
  · exact B2231387
  · exact B2231391
  · exact B2231395
  · exact B2231399
  · exact B2231403
  · exact B2231407
  · exact B2231411
  · exact B2231415
  · exact B2231419
  · exact B2231423
  · exact B2231427
  · exact B2231431
  · exact B2231435
theorem solution (m : ℕ) (hlo : 2229435 ≤ m) (hhi : m ≤ 2231435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 557358 ≤ j := by omega
    have hj2 : j ≤ 557858 := by omega
    have hb : Blo 2229435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
