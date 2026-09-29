-- Prove2me | solution 1 for syracuse_descends_range_1648023_1649523
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:17:15.176576+00:00
-- url     : https://prove2.me/submissions/ed044b04-dba2-421b-9af5-0e8cb6b4febf

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


theorem B4694021 : Blo 1648023 4694021 := bbase (se 4 (by rfl) ⟨440064, by rfl⟩ : syracuseStep 4694021 = 880129) (by norm_num)
theorem B2473997 : Blo 1648023 2473997 := bbase (se 3 (by rfl) ⟨463874, by rfl⟩ : syracuseStep 2473997 = 927749) (by norm_num)
theorem B3711005 : Blo 1648023 3711005 := bbase (se 3 (by rfl) ⟨695813, by rfl⟩ : syracuseStep 3711005 = 1391627) (by norm_num)
theorem B2474021 : Blo 1648023 2474021 := bbase (se 4 (by rfl) ⟨231939, by rfl⟩ : syracuseStep 2474021 = 463879) (by norm_num)
theorem B3342397 : Blo 1648023 3342397 := bbase (se 3 (by rfl) ⟨626699, by rfl⟩ : syracuseStep 3342397 = 1253399) (by norm_num)
theorem B2474045 : Blo 1648023 2474045 := bbase (se 3 (by rfl) ⟨463883, by rfl⟩ : syracuseStep 2474045 = 927767) (by norm_num)
theorem B2474069 : Blo 1648023 2474069 := bbase (se 8 (by rfl) ⟨14496, by rfl⟩ : syracuseStep 2474069 = 28993) (by norm_num)
theorem B94027861 : Blo 1648023 94027861 := bbase (se 8 (by rfl) ⟨550944, by rfl⟩ : syracuseStep 94027861 = 1101889) (by norm_num)
theorem B3129445 : Blo 1648023 3129445 := bbase (se 4 (by rfl) ⟨293385, by rfl⟩ : syracuseStep 3129445 = 586771) (by norm_num)
theorem B3711077 : Blo 1648023 3711077 := bbase (se 4 (by rfl) ⟨347913, by rfl⟩ : syracuseStep 3711077 = 695827) (by norm_num)
theorem B2474093 : Blo 1648023 2474093 := bbase (se 3 (by rfl) ⟨463892, by rfl⟩ : syracuseStep 2474093 = 927785) (by norm_num)
theorem B5562485 : Blo 1648023 5562485 := bbase (se 5 (by rfl) ⟨260741, by rfl⟩ : syracuseStep 5562485 = 521483) (by norm_num)
theorem B2474117 : Blo 1648023 2474117 := bbase (se 4 (by rfl) ⟨231948, by rfl⟩ : syracuseStep 2474117 = 463897) (by norm_num)
theorem B2474141 : Blo 1648023 2474141 := bbase (se 3 (by rfl) ⟨463901, by rfl⟩ : syracuseStep 2474141 = 927803) (by norm_num)
theorem B3711149 : Blo 1648023 3711149 := bbase (se 3 (by rfl) ⟨695840, by rfl⟩ : syracuseStep 3711149 = 1391681) (by norm_num)
theorem B2228405 : Blo 1648023 2228405 := bbase (se 5 (by rfl) ⟨104456, by rfl⟩ : syracuseStep 2228405 = 208913) (by norm_num)
theorem B2474165 : Blo 1648023 2474165 := bbase (se 5 (by rfl) ⟨115976, by rfl⟩ : syracuseStep 2474165 = 231953) (by norm_num)
theorem B4694213 : Blo 1648023 4694213 := bbase (se 4 (by rfl) ⟨440082, by rfl⟩ : syracuseStep 4694213 = 880165) (by norm_num)
theorem B2474189 : Blo 1648023 2474189 := bbase (se 3 (by rfl) ⟨463910, by rfl⟩ : syracuseStep 2474189 = 927821) (by norm_num)
theorem B2859229 : Blo 1648023 2859229 := bbase (se 3 (by rfl) ⟨536105, by rfl⟩ : syracuseStep 2859229 = 1072211) (by norm_num)
theorem B2474213 : Blo 1648023 2474213 := bbase (se 4 (by rfl) ⟨231957, by rfl⟩ : syracuseStep 2474213 = 463915) (by norm_num)
theorem B3711221 : Blo 1648023 3711221 := bbase (se 5 (by rfl) ⟨173963, by rfl⟩ : syracuseStep 3711221 = 347927) (by norm_num)
theorem B2474237 : Blo 1648023 2474237 := bbase (se 3 (by rfl) ⟨463919, by rfl⟩ : syracuseStep 2474237 = 927839) (by norm_num)
theorem B2474261 : Blo 1648023 2474261 := bbase (se 6 (by rfl) ⟨57990, by rfl⟩ : syracuseStep 2474261 = 115981) (by norm_num)
theorem B2474285 : Blo 1648023 2474285 := bbase (se 3 (by rfl) ⟨463928, by rfl⟩ : syracuseStep 2474285 = 927857) (by norm_num)
theorem B3711293 : Blo 1648023 3711293 := bbase (se 3 (by rfl) ⟨695867, by rfl⟩ : syracuseStep 3711293 = 1391735) (by norm_num)
theorem B8348021 : Blo 1648023 8348021 := bbase (se 5 (by rfl) ⟨391313, by rfl⟩ : syracuseStep 8348021 = 782627) (by norm_num)
theorem B3711365 : Blo 1648023 3711365 := bbase (se 4 (by rfl) ⟨347940, by rfl⟩ : syracuseStep 3711365 = 695881) (by norm_num)
theorem B3129749 : Blo 1648023 3129749 := bbase (se 6 (by rfl) ⟨73353, by rfl⟩ : syracuseStep 3129749 = 146707) (by norm_num)
theorem B8028629 : Blo 1648023 8028629 := bbase (se 7 (by rfl) ⟨94085, by rfl⟩ : syracuseStep 8028629 = 188171) (by norm_num)
theorem B3760597 : Blo 1648023 3760597 := bbase (se 7 (by rfl) ⟨44069, by rfl⟩ : syracuseStep 3760597 = 88139) (by norm_num)
theorem B5562917 : Blo 1648023 5562917 := bbase (se 4 (by rfl) ⟨521523, by rfl⟩ : syracuseStep 5562917 = 1043047) (by norm_num)
theorem B6259301 : Blo 1648023 6259301 := bbase (se 4 (by rfl) ⟨586809, by rfl⟩ : syracuseStep 6259301 = 1173619) (by norm_num)
theorem B6259589 : Blo 1648023 6259589 := bbase (se 4 (by rfl) ⟨586836, by rfl⟩ : syracuseStep 6259589 = 1173673) (by norm_num)
theorem B15852469 : Blo 1648023 15852469 := bbase (se 5 (by rfl) ⟨743084, by rfl⟩ : syracuseStep 15852469 = 1486169) (by norm_num)
theorem B5563349 : Blo 1648023 5563349 := bbase (se 7 (by rfl) ⟨65195, by rfl⟩ : syracuseStep 5563349 = 130391) (by norm_num)
theorem B9520213 : Blo 1648023 9520213 := bbase (se 8 (by rfl) ⟨55782, by rfl⟩ : syracuseStep 9520213 = 111565) (by norm_num)
theorem B3130501 : Blo 1648023 3130501 := bbase (se 4 (by rfl) ⟨293484, by rfl⟩ : syracuseStep 3130501 = 586969) (by norm_num)
theorem B3343493 : Blo 1648023 3343493 := bbase (se 4 (by rfl) ⟨313452, by rfl⟩ : syracuseStep 3343493 = 626905) (by norm_num)
theorem B2507917 : Blo 1648023 2507917 := bbase (se 3 (by rfl) ⟨470234, by rfl⟩ : syracuseStep 2507917 = 940469) (by norm_num)
theorem B4695205 : Blo 1648023 4695205 := bbase (se 4 (by rfl) ⟨440175, by rfl⟩ : syracuseStep 4695205 = 880351) (by norm_num)
theorem B2507965 : Blo 1648023 2507965 := bbase (se 3 (by rfl) ⟨470243, by rfl⟩ : syracuseStep 2507965 = 940487) (by norm_num)
theorem B3130645 : Blo 1648023 3130645 := bbase (se 6 (by rfl) ⟨73374, by rfl⟩ : syracuseStep 3130645 = 146749) (by norm_num)
theorem B9389429 : Blo 1648023 9389429 := bbase (se 5 (by rfl) ⟨440129, by rfl⟩ : syracuseStep 9389429 = 880259) (by norm_num)
theorem B5563781 : Blo 1648023 5563781 := bbase (se 4 (by rfl) ⟨521604, by rfl⟩ : syracuseStep 5563781 = 1043209) (by norm_num)
theorem B3130805 : Blo 1648023 3130805 := bbase (se 5 (by rfl) ⟨146756, by rfl⟩ : syracuseStep 3130805 = 293513) (by norm_num)
theorem B6776261 : Blo 1648023 6776261 := bbase (se 4 (by rfl) ⟨635274, by rfl⟩ : syracuseStep 6776261 = 1270549) (by norm_num)
theorem B10298933 : Blo 1648023 10298933 := bbase (se 5 (by rfl) ⟨482762, by rfl⟩ : syracuseStep 10298933 = 965525) (by norm_num)
theorem B3130949 : Blo 1648023 3130949 := bbase (se 4 (by rfl) ⟨293526, by rfl⟩ : syracuseStep 3130949 = 587053) (by norm_num)
theorem B2115173 : Blo 1648023 2115173 := bbase (se 4 (by rfl) ⟨198297, by rfl⟩ : syracuseStep 2115173 = 396595) (by norm_num)
theorem B8349317 : Blo 1648023 8349317 := bbase (se 4 (by rfl) ⟨782748, by rfl⟩ : syracuseStep 8349317 = 1565497) (by norm_num)
theorem B14083733 : Blo 1648023 14083733 := bbase (se 6 (by rfl) ⟨330087, by rfl⟩ : syracuseStep 14083733 = 660175) (by norm_num)
theorem B4286189 : Blo 1648023 4286189 := bbase (se 3 (by rfl) ⟨803660, by rfl⟩ : syracuseStep 4286189 = 1607321) (by norm_num)
theorem B2115353 : Blo 1648023 2115353 := bbase (se 2 (by rfl) ⟨793257, by rfl⟩ : syracuseStep 2115353 = 1586515) (by norm_num)
theorem B5564213 : Blo 1648023 5564213 := bbase (se 5 (by rfl) ⟨260822, by rfl⟩ : syracuseStep 5564213 = 521645) (by norm_num)
theorem B4171621 : Blo 1648023 4171621 := bbase (se 4 (by rfl) ⟨391089, by rfl⟩ : syracuseStep 4171621 = 782179) (by norm_num)
theorem B3131237 : Blo 1648023 3131237 := bbase (se 4 (by rfl) ⟨293553, by rfl⟩ : syracuseStep 3131237 = 587107) (by norm_num)
theorem B2820037 : Blo 1648023 2820037 := bbase (se 4 (by rfl) ⟨264378, by rfl⟩ : syracuseStep 2820037 = 528757) (by norm_num)
theorem B4171733 : Blo 1648023 4171733 := bbase (se 7 (by rfl) ⟨48887, by rfl⟩ : syracuseStep 4171733 = 97775) (by norm_num)
theorem B5720053 : Blo 1648023 5720053 := bbase (se 5 (by rfl) ⟨268127, by rfl⟩ : syracuseStep 5720053 = 536255) (by norm_num)
theorem B3131389 : Blo 1648023 3131389 := bbase (se 3 (by rfl) ⟨587135, by rfl⟩ : syracuseStep 3131389 = 1174271) (by norm_num)
theorem B6260773 : Blo 1648023 6260773 := bbase (se 4 (by rfl) ⟨586947, by rfl⟩ : syracuseStep 6260773 = 1173895) (by norm_num)
theorem B2639957 : Blo 1648023 2639957 := bbase (se 8 (by rfl) ⟨15468, by rfl⟩ : syracuseStep 2639957 = 30937) (by norm_num)
theorem B4171925 : Blo 1648023 4171925 := bbase (se 6 (by rfl) ⟨97779, by rfl⟩ : syracuseStep 4171925 = 195559) (by norm_num)
theorem B5564645 : Blo 1648023 5564645 := bbase (se 4 (by rfl) ⟨521685, by rfl⟩ : syracuseStep 5564645 = 1043371) (by norm_num)
theorem B4696309 : Blo 1648023 4696309 := bbase (se 5 (by rfl) ⟨220139, by rfl⟩ : syracuseStep 4696309 = 440279) (by norm_num)
theorem B6261077 : Blo 1648023 6261077 := bbase (se 10 (by rfl) ⟨9171, by rfl⟩ : syracuseStep 6261077 = 18343) (by norm_num)
theorem B4172269 : Blo 1648023 4172269 := bbase (se 3 (by rfl) ⟨782300, by rfl⟩ : syracuseStep 4172269 = 1564601) (by norm_num)
theorem B9390613 : Blo 1648023 9390613 := bbase (se 6 (by rfl) ⟨220092, by rfl⟩ : syracuseStep 9390613 = 440185) (by norm_num)
theorem B4172381 : Blo 1648023 4172381 := bbase (se 3 (by rfl) ⟨782321, by rfl⟩ : syracuseStep 4172381 = 1564643) (by norm_num)
theorem B1854049 : Blo 1648023 1854049 := bbase (se 2 (by rfl) ⟨695268, by rfl⟩ : syracuseStep 1854049 = 1390537) (by norm_num)
theorem B2640509 : Blo 1648023 2640509 := bbase (se 3 (by rfl) ⟨495095, by rfl⟩ : syracuseStep 2640509 = 990191) (by norm_num)
theorem B1854085 : Blo 1648023 1854085 := bbase (se 4 (by rfl) ⟨173820, by rfl⟩ : syracuseStep 1854085 = 347641) (by norm_num)
theorem B5565077 : Blo 1648023 5565077 := bbase (se 6 (by rfl) ⟨130431, by rfl⟩ : syracuseStep 5565077 = 260863) (by norm_num)
theorem B2640541 : Blo 1648023 2640541 := bbase (se 3 (by rfl) ⟨495101, by rfl⟩ : syracuseStep 2640541 = 990203) (by norm_num)
theorem B1854121 : Blo 1648023 1854121 := bbase (se 2 (by rfl) ⟨695295, by rfl⟩ : syracuseStep 1854121 = 1390591) (by norm_num)
theorem B4229813 : Blo 1648023 4229813 := bbase (se 5 (by rfl) ⟨198272, by rfl⟩ : syracuseStep 4229813 = 396545) (by norm_num)
theorem B1854157 : Blo 1648023 1854157 := bbase (se 3 (by rfl) ⟨347654, by rfl⟩ : syracuseStep 1854157 = 695309) (by norm_num)
theorem B1854193 : Blo 1648023 1854193 := bbase (se 2 (by rfl) ⟨695322, by rfl⟩ : syracuseStep 1854193 = 1390645) (by norm_num)
theorem B1854229 : Blo 1648023 1854229 := bbase (se 6 (by rfl) ⟨43458, by rfl⟩ : syracuseStep 1854229 = 86917) (by norm_num)
theorem B4172573 : Blo 1648023 4172573 := bbase (se 3 (by rfl) ⟨782357, by rfl⟩ : syracuseStep 4172573 = 1564715) (by norm_num)
theorem B5942069 : Blo 1648023 5942069 := bbase (se 5 (by rfl) ⟨278534, by rfl⟩ : syracuseStep 5942069 = 557069) (by norm_num)
theorem B1854265 : Blo 1648023 1854265 := bbase (se 2 (by rfl) ⟨695349, by rfl⟩ : syracuseStep 1854265 = 1390699) (by norm_num)
theorem B1854301 : Blo 1648023 1854301 := bbase (se 3 (by rfl) ⟨347681, by rfl⟩ : syracuseStep 1854301 = 695363) (by norm_num)
theorem B1854337 : Blo 1648023 1854337 := bbase (se 2 (by rfl) ⟨695376, by rfl⟩ : syracuseStep 1854337 = 1390753) (by norm_num)
theorem B8350613 : Blo 1648023 8350613 := bbase (se 6 (by rfl) ⟨195717, by rfl⟩ : syracuseStep 8350613 = 391435) (by norm_num)
theorem B1854373 : Blo 1648023 1854373 := bbase (se 4 (by rfl) ⟨173847, by rfl⟩ : syracuseStep 1854373 = 347695) (by norm_num)
theorem B1854409 : Blo 1648023 1854409 := bbase (se 2 (by rfl) ⟨695403, by rfl⟩ : syracuseStep 1854409 = 1390807) (by norm_num)
theorem B1854445 : Blo 1648023 1854445 := bbase (se 3 (by rfl) ⟨347708, by rfl⟩ : syracuseStep 1854445 = 695417) (by norm_num)
theorem B1854481 : Blo 1648023 1854481 := bbase (se 2 (by rfl) ⟨695430, by rfl⟩ : syracuseStep 1854481 = 1390861) (by norm_num)
theorem B1854517 : Blo 1648023 1854517 := bbase (se 5 (by rfl) ⟨86930, by rfl⟩ : syracuseStep 1854517 = 173861) (by norm_num)
theorem B5565509 : Blo 1648023 5565509 := bbase (se 4 (by rfl) ⟨521766, by rfl⟩ : syracuseStep 5565509 = 1043533) (by norm_num)
theorem B1854553 : Blo 1648023 1854553 := bbase (se 2 (by rfl) ⟨695457, by rfl⟩ : syracuseStep 1854553 = 1390915) (by norm_num)
theorem B4172917 : Blo 1648023 4172917 := bbase (se 5 (by rfl) ⟨195605, by rfl⟩ : syracuseStep 4172917 = 391211) (by norm_num)
theorem B1854589 : Blo 1648023 1854589 := bbase (se 3 (by rfl) ⟨347735, by rfl⟩ : syracuseStep 1854589 = 695471) (by norm_num)
theorem B1854625 : Blo 1648023 1854625 := bbase (se 2 (by rfl) ⟨695484, by rfl⟩ : syracuseStep 1854625 = 1390969) (by norm_num)
theorem B1854661 : Blo 1648023 1854661 := bbase (se 4 (by rfl) ⟨173874, by rfl⟩ : syracuseStep 1854661 = 347749) (by norm_num)
theorem B4173029 : Blo 1648023 4173029 := bbase (se 4 (by rfl) ⟨391221, by rfl⟩ : syracuseStep 4173029 = 782443) (by norm_num)
theorem B1854697 : Blo 1648023 1854697 := bbase (se 2 (by rfl) ⟨695511, by rfl⟩ : syracuseStep 1854697 = 1391023) (by norm_num)
theorem B1854733 : Blo 1648023 1854733 := bbase (se 3 (by rfl) ⟨347762, by rfl⟩ : syracuseStep 1854733 = 695525) (by norm_num)
theorem B1854769 : Blo 1648023 1854769 := bbase (se 2 (by rfl) ⟨695538, by rfl⟩ : syracuseStep 1854769 = 1391077) (by norm_num)
theorem B1854805 : Blo 1648023 1854805 := bbase (se 11 (by rfl) ⟨1358, by rfl⟩ : syracuseStep 1854805 = 2717) (by norm_num)
theorem B5942645 : Blo 1648023 5942645 := bbase (se 5 (by rfl) ⟨278561, by rfl⟩ : syracuseStep 5942645 = 557123) (by norm_num)
theorem B1854841 : Blo 1648023 1854841 := bbase (se 2 (by rfl) ⟨695565, by rfl⟩ : syracuseStep 1854841 = 1391131) (by norm_num)
theorem B3960197 : Blo 1648023 3960197 := bbase (se 4 (by rfl) ⟨371268, by rfl⟩ : syracuseStep 3960197 = 742537) (by norm_num)
theorem B1854877 : Blo 1648023 1854877 := bbase (se 3 (by rfl) ⟨347789, by rfl⟩ : syracuseStep 1854877 = 695579) (by norm_num)
theorem B4173221 : Blo 1648023 4173221 := bbase (se 4 (by rfl) ⟨391239, by rfl⟩ : syracuseStep 4173221 = 782479) (by norm_num)
theorem B1854913 : Blo 1648023 1854913 := bbase (se 2 (by rfl) ⟨695592, by rfl⟩ : syracuseStep 1854913 = 1391185) (by norm_num)
theorem B1854949 : Blo 1648023 1854949 := bbase (se 4 (by rfl) ⟨173901, by rfl⟩ : syracuseStep 1854949 = 347803) (by norm_num)
theorem B5565941 : Blo 1648023 5565941 := bbase (se 5 (by rfl) ⟨260903, by rfl⟩ : syracuseStep 5565941 = 521807) (by norm_num)
theorem B1854985 : Blo 1648023 1854985 := bbase (se 2 (by rfl) ⟨695619, by rfl⟩ : syracuseStep 1854985 = 1391239) (by norm_num)
theorem B2346509 : Blo 1648023 2346509 := bbase (se 3 (by rfl) ⟨439970, by rfl⟩ : syracuseStep 2346509 = 879941) (by norm_num)
theorem B1855021 : Blo 1648023 1855021 := bbase (se 3 (by rfl) ⟨347816, by rfl⟩ : syracuseStep 1855021 = 695633) (by norm_num)
theorem B2641469 : Blo 1648023 2641469 := bbase (se 3 (by rfl) ⟨495275, by rfl⟩ : syracuseStep 2641469 = 990551) (by norm_num)
theorem B1855057 : Blo 1648023 1855057 := bbase (se 2 (by rfl) ⟨695646, by rfl⟩ : syracuseStep 1855057 = 1391293) (by norm_num)
theorem B1855093 : Blo 1648023 1855093 := bbase (se 5 (by rfl) ⟨86957, by rfl⟩ : syracuseStep 1855093 = 173915) (by norm_num)
theorem B1855129 : Blo 1648023 1855129 := bbase (se 2 (by rfl) ⟨695673, by rfl⟩ : syracuseStep 1855129 = 1391347) (by norm_num)
theorem B1879733 : Blo 1648023 1879733 := bbase (se 5 (by rfl) ⟨88112, by rfl⟩ : syracuseStep 1879733 = 176225) (by norm_num)
theorem B1855165 : Blo 1648023 1855165 := bbase (se 3 (by rfl) ⟨347843, by rfl⟩ : syracuseStep 1855165 = 695687) (by norm_num)
theorem B1879765 : Blo 1648023 1879765 := bbase (se 7 (by rfl) ⟨22028, by rfl⟩ : syracuseStep 1879765 = 44057) (by norm_num)
theorem B1855201 : Blo 1648023 1855201 := bbase (se 2 (by rfl) ⟨695700, by rfl⟩ : syracuseStep 1855201 = 1391401) (by norm_num)
theorem B4173565 : Blo 1648023 4173565 := bbase (se 3 (by rfl) ⟨782543, by rfl⟩ : syracuseStep 4173565 = 1565087) (by norm_num)
theorem B7040773 : Blo 1648023 7040773 := bbase (se 4 (by rfl) ⟨660072, by rfl⟩ : syracuseStep 7040773 = 1320145) (by norm_num)
theorem B1855237 : Blo 1648023 1855237 := bbase (se 4 (by rfl) ⟨173928, by rfl⟩ : syracuseStep 1855237 = 347857) (by norm_num)
theorem B5353253 : Blo 1648023 5353253 := bbase (se 4 (by rfl) ⟨501867, by rfl⟩ : syracuseStep 5353253 = 1003735) (by norm_num)
theorem B1855273 : Blo 1648023 1855273 := bbase (se 2 (by rfl) ⟨695727, by rfl⟩ : syracuseStep 1855273 = 1391455) (by norm_num)
theorem B1855309 : Blo 1648023 1855309 := bbase (se 3 (by rfl) ⟨347870, by rfl⟩ : syracuseStep 1855309 = 695741) (by norm_num)
theorem B4173677 : Blo 1648023 4173677 := bbase (se 3 (by rfl) ⟨782564, by rfl⟩ : syracuseStep 4173677 = 1565129) (by norm_num)
theorem B1855345 : Blo 1648023 1855345 := bbase (se 2 (by rfl) ⟨695754, by rfl⟩ : syracuseStep 1855345 = 1391509) (by norm_num)
theorem B1855381 : Blo 1648023 1855381 := bbase (se 6 (by rfl) ⟨43485, by rfl⟩ : syracuseStep 1855381 = 86971) (by norm_num)
theorem B5566373 : Blo 1648023 5566373 := bbase (se 4 (by rfl) ⟨521847, by rfl⟩ : syracuseStep 5566373 = 1043695) (by norm_num)
theorem B2781101 : Blo 1648023 2781101 := bbase (se 3 (by rfl) ⟨521456, by rfl⟩ : syracuseStep 2781101 = 1042913) (by norm_num)
theorem B1855417 : Blo 1648023 1855417 := bbase (se 2 (by rfl) ⟨695781, by rfl⟩ : syracuseStep 1855417 = 1391563) (by norm_num)
theorem B2379709 : Blo 1648023 2379709 := bbase (se 3 (by rfl) ⟨446195, by rfl⟩ : syracuseStep 2379709 = 892391) (by norm_num)
theorem B1855453 : Blo 1648023 1855453 := bbase (se 3 (by rfl) ⟨347897, by rfl⟩ : syracuseStep 1855453 = 695795) (by norm_num)
theorem B1855489 : Blo 1648023 1855489 := bbase (se 2 (by rfl) ⟨695808, by rfl⟩ : syracuseStep 1855489 = 1391617) (by norm_num)
theorem B1855525 : Blo 1648023 1855525 := bbase (se 4 (by rfl) ⟨173955, by rfl⟩ : syracuseStep 1855525 = 347911) (by norm_num)
theorem B2781229 : Blo 1648023 2781229 := bbase (se 3 (by rfl) ⟨521480, by rfl⟩ : syracuseStep 2781229 = 1042961) (by norm_num)
theorem B4173869 : Blo 1648023 4173869 := bbase (se 3 (by rfl) ⟨782600, by rfl⟩ : syracuseStep 4173869 = 1565201) (by norm_num)
theorem B2347061 : Blo 1648023 2347061 := bbase (se 5 (by rfl) ⟨110018, by rfl⟩ : syracuseStep 2347061 = 220037) (by norm_num)
theorem B5279813 : Blo 1648023 5279813 := bbase (se 4 (by rfl) ⟨494982, by rfl⟩ : syracuseStep 5279813 = 989965) (by norm_num)
theorem B1855561 : Blo 1648023 1855561 := bbase (se 2 (by rfl) ⟨695835, by rfl⟩ : syracuseStep 1855561 = 1391671) (by norm_num)
theorem B1855597 : Blo 1648023 1855597 := bbase (se 3 (by rfl) ⟨347924, by rfl⟩ : syracuseStep 1855597 = 695849) (by norm_num)
theorem B2781317 : Blo 1648023 2781317 := bbase (se 4 (by rfl) ⟨260748, by rfl⟩ : syracuseStep 2781317 = 521497) (by norm_num)
theorem B1855633 : Blo 1648023 1855633 := bbase (se 2 (by rfl) ⟨695862, by rfl⟩ : syracuseStep 1855633 = 1391725) (by norm_num)
theorem B1855669 : Blo 1648023 1855669 := bbase (se 5 (by rfl) ⟨86984, by rfl⟩ : syracuseStep 1855669 = 173969) (by norm_num)
theorem B1855705 : Blo 1648023 1855705 := bbase (se 2 (by rfl) ⟨695889, by rfl⟩ : syracuseStep 1855705 = 1391779) (by norm_num)
theorem B2642149 : Blo 1648023 2642149 := bbase (se 4 (by rfl) ⟨247701, by rfl⟩ : syracuseStep 2642149 = 495403) (by norm_num)
theorem B1880317 : Blo 1648023 1880317 := bbase (se 3 (by rfl) ⟨352559, by rfl⟩ : syracuseStep 1880317 = 705119) (by norm_num)
theorem B2781445 : Blo 1648023 2781445 := bbase (se 4 (by rfl) ⟨260760, by rfl⟩ : syracuseStep 2781445 = 521521) (by norm_num)
theorem B2642213 : Blo 1648023 2642213 := bbase (se 4 (by rfl) ⟨247707, by rfl⟩ : syracuseStep 2642213 = 495415) (by norm_num)
theorem B5566805 : Blo 1648023 5566805 := bbase (se 10 (by rfl) ⟨8154, by rfl⟩ : syracuseStep 5566805 = 16309) (by norm_num)
theorem B2781533 : Blo 1648023 2781533 := bbase (se 3 (by rfl) ⟨521537, by rfl⟩ : syracuseStep 2781533 = 1043075) (by norm_num)
theorem B4174213 : Blo 1648023 4174213 := bbase (se 4 (by rfl) ⟨391332, by rfl⟩ : syracuseStep 4174213 = 782665) (by norm_num)
theorem B9392597 : Blo 1648023 9392597 := bbase (se 7 (by rfl) ⟨110069, by rfl⟩ : syracuseStep 9392597 = 220139) (by norm_num)
theorem B2781661 : Blo 1648023 2781661 := bbase (se 3 (by rfl) ⟨521561, by rfl⟩ : syracuseStep 2781661 = 1043123) (by norm_num)
theorem B4174325 : Blo 1648023 4174325 := bbase (se 5 (by rfl) ⟨195671, by rfl⟩ : syracuseStep 4174325 = 391343) (by norm_num)
theorem B2781749 : Blo 1648023 2781749 := bbase (se 5 (by rfl) ⟨130394, by rfl⟩ : syracuseStep 2781749 = 260789) (by norm_num)
theorem B14086709 : Blo 1648023 14086709 := bbase (se 5 (by rfl) ⟨660314, by rfl⟩ : syracuseStep 14086709 = 1320629) (by norm_num)
theorem B8344133 : Blo 1648023 8344133 := bbase (se 4 (by rfl) ⟨782262, by rfl⟩ : syracuseStep 8344133 = 1564525) (by norm_num)
theorem B2781877 : Blo 1648023 2781877 := bbase (se 5 (by rfl) ⟨130400, by rfl⟩ : syracuseStep 2781877 = 260801) (by norm_num)
theorem B3388085 : Blo 1648023 3388085 := bbase (se 5 (by rfl) ⟨158816, by rfl⟩ : syracuseStep 3388085 = 317633) (by norm_num)
theorem B4174517 : Blo 1648023 4174517 := bbase (se 5 (by rfl) ⟨195680, by rfl⟩ : syracuseStep 4174517 = 391361) (by norm_num)
theorem B3568349 : Blo 1648023 3568349 := bbase (se 3 (by rfl) ⟨669065, by rfl⟩ : syracuseStep 3568349 = 1338131) (by norm_num)
theorem B2781965 : Blo 1648023 2781965 := bbase (se 3 (by rfl) ⟨521618, by rfl⟩ : syracuseStep 2781965 = 1043237) (by norm_num)
theorem B2347813 : Blo 1648023 2347813 := bbase (se 4 (by rfl) ⟨220107, by rfl⟩ : syracuseStep 2347813 = 440215) (by norm_num)
theorem B2782093 : Blo 1648023 2782093 := bbase (se 3 (by rfl) ⟨521642, by rfl⟩ : syracuseStep 2782093 = 1043285) (by norm_num)
theorem B6607781 : Blo 1648023 6607781 := bbase (se 4 (by rfl) ⟨619479, by rfl⟩ : syracuseStep 6607781 = 1238959) (by norm_num)
theorem B5944229 : Blo 1648023 5944229 := bbase (se 4 (by rfl) ⟨557271, by rfl⟩ : syracuseStep 5944229 = 1114543) (by norm_num)
theorem B5280709 : Blo 1648023 5280709 := bbase (se 4 (by rfl) ⟨495066, by rfl⟩ : syracuseStep 5280709 = 990133) (by norm_num)
theorem B2085841 : Blo 1648023 2085841 := bbase (se 2 (by rfl) ⟨782190, by rfl⟩ : syracuseStep 2085841 = 1564381) (by norm_num)
theorem B2782181 : Blo 1648023 2782181 := bbase (se 4 (by rfl) ⟨260829, by rfl⟩ : syracuseStep 2782181 = 521659) (by norm_num)
theorem B4174861 : Blo 1648023 4174861 := bbase (se 3 (by rfl) ⟨782786, by rfl⟩ : syracuseStep 4174861 = 1565573) (by norm_num)
theorem B8459333 : Blo 1648023 8459333 := bbase (se 4 (by rfl) ⟨793062, by rfl⟩ : syracuseStep 8459333 = 1586125) (by norm_num)
theorem B7140437 : Blo 1648023 7140437 := bbase (se 8 (by rfl) ⟨41838, by rfl⟩ : syracuseStep 7140437 = 83677) (by norm_num)
theorem B2782309 : Blo 1648023 2782309 := bbase (se 4 (by rfl) ⟨260841, by rfl⟩ : syracuseStep 2782309 = 521683) (by norm_num)
theorem B4289645 : Blo 1648023 4289645 := bbase (se 3 (by rfl) ⟨804308, by rfl⟩ : syracuseStep 4289645 = 1608617) (by norm_num)
theorem B8909941 : Blo 1648023 8909941 := bbase (se 5 (by rfl) ⟨417653, by rfl⟩ : syracuseStep 8909941 = 835307) (by norm_num)
theorem B3961973 : Blo 1648023 3961973 := bbase (se 5 (by rfl) ⟨185717, by rfl⟩ : syracuseStep 3961973 = 371435) (by norm_num)
theorem B2086013 : Blo 1648023 2086013 := bbase (se 3 (by rfl) ⟨391127, by rfl⟩ : syracuseStep 2086013 = 782255) (by norm_num)
theorem B4174973 : Blo 1648023 4174973 := bbase (se 3 (by rfl) ⟨782807, by rfl⟩ : syracuseStep 4174973 = 1565615) (by norm_num)
theorem B3708053 : Blo 1648023 3708053 := bbase (se 6 (by rfl) ⟨86907, by rfl⟩ : syracuseStep 3708053 = 173815) (by norm_num)
theorem B2086069 : Blo 1648023 2086069 := bbase (se 5 (by rfl) ⟨97784, by rfl⟩ : syracuseStep 2086069 = 195569) (by norm_num)
theorem B2782397 : Blo 1648023 2782397 := bbase (se 3 (by rfl) ⟨521699, by rfl⟩ : syracuseStep 2782397 = 1043399) (by norm_num)
theorem B5944517 : Blo 1648023 5944517 := bbase (se 4 (by rfl) ⟨557298, by rfl⟩ : syracuseStep 5944517 = 1114597) (by norm_num)
theorem B7042261 : Blo 1648023 7042261 := bbase (se 7 (by rfl) ⟨82526, by rfl⟩ : syracuseStep 7042261 = 165053) (by norm_num)
theorem B3708125 : Blo 1648023 3708125 := bbase (se 3 (by rfl) ⟨695273, by rfl⟩ : syracuseStep 3708125 = 1390547) (by norm_num)
theorem B7042277 : Blo 1648023 7042277 := bbase (se 4 (by rfl) ⟨660213, by rfl⟩ : syracuseStep 7042277 = 1320427) (by norm_num)
theorem B2086165 : Blo 1648023 2086165 := bbase (se 6 (by rfl) ⟨48894, by rfl⟩ : syracuseStep 2086165 = 97789) (by norm_num)
theorem B3708197 : Blo 1648023 3708197 := bbase (se 4 (by rfl) ⟨347643, by rfl⟩ : syracuseStep 3708197 = 695287) (by norm_num)
theorem B2782525 : Blo 1648023 2782525 := bbase (se 3 (by rfl) ⟨521723, by rfl⟩ : syracuseStep 2782525 = 1043447) (by norm_num)
theorem B4175165 : Blo 1648023 4175165 := bbase (se 3 (by rfl) ⟨782843, by rfl⟩ : syracuseStep 4175165 = 1565687) (by norm_num)
theorem B3708269 : Blo 1648023 3708269 := bbase (se 3 (by rfl) ⟨695300, by rfl⟩ : syracuseStep 3708269 = 1390601) (by norm_num)
theorem B2782613 : Blo 1648023 2782613 := bbase (se 6 (by rfl) ⟨65217, by rfl⟩ : syracuseStep 2782613 = 130435) (by norm_num)
theorem B15046037 : Blo 1648023 15046037 := bbase (se 6 (by rfl) ⟨352641, by rfl⟩ : syracuseStep 15046037 = 705283) (by norm_num)
theorem B3708341 : Blo 1648023 3708341 := bbase (se 5 (by rfl) ⟨173828, by rfl⟩ : syracuseStep 3708341 = 347657) (by norm_num)
theorem B2086337 : Blo 1648023 2086337 := bbase (se 2 (by rfl) ⟨782376, by rfl⟩ : syracuseStep 2086337 = 1564753) (by norm_num)
theorem B2086393 : Blo 1648023 2086393 := bbase (se 2 (by rfl) ⟨782397, by rfl⟩ : syracuseStep 2086393 = 1564795) (by norm_num)
theorem B3708413 : Blo 1648023 3708413 := bbase (se 3 (by rfl) ⟨695327, by rfl⟩ : syracuseStep 3708413 = 1390655) (by norm_num)
theorem B2782741 : Blo 1648023 2782741 := bbase (se 6 (by rfl) ⟨65220, by rfl⟩ : syracuseStep 2782741 = 130441) (by norm_num)
theorem B3520037 : Blo 1648023 3520037 := bbase (se 4 (by rfl) ⟨330003, by rfl⟩ : syracuseStep 3520037 = 660007) (by norm_num)
theorem B3520045 : Blo 1648023 3520045 := bbase (se 3 (by rfl) ⟨660008, by rfl⟩ : syracuseStep 3520045 = 1320017) (by norm_num)
theorem B2348605 : Blo 1648023 2348605 := bbase (se 3 (by rfl) ⟨440363, by rfl⟩ : syracuseStep 2348605 = 880727) (by norm_num)
theorem B3708485 : Blo 1648023 3708485 := bbase (se 4 (by rfl) ⟨347670, by rfl⟩ : syracuseStep 3708485 = 695341) (by norm_num)
theorem B2086489 : Blo 1648023 2086489 := bbase (se 2 (by rfl) ⟨782433, by rfl⟩ : syracuseStep 2086489 = 1564867) (by norm_num)
theorem B2782829 : Blo 1648023 2782829 := bbase (se 3 (by rfl) ⟨521780, by rfl⟩ : syracuseStep 2782829 = 1043561) (by norm_num)
theorem B3708557 : Blo 1648023 3708557 := bbase (se 3 (by rfl) ⟨695354, by rfl⟩ : syracuseStep 3708557 = 1390709) (by norm_num)
theorem B3708629 : Blo 1648023 3708629 := bbase (se 7 (by rfl) ⟨43460, by rfl⟩ : syracuseStep 3708629 = 86921) (by norm_num)
theorem B2782957 : Blo 1648023 2782957 := bbase (se 3 (by rfl) ⟨521804, by rfl⟩ : syracuseStep 2782957 = 1043609) (by norm_num)
theorem B2086661 : Blo 1648023 2086661 := bbase (se 4 (by rfl) ⟨195624, by rfl⟩ : syracuseStep 2086661 = 391249) (by norm_num)
theorem B12048149 : Blo 1648023 12048149 := bbase (se 6 (by rfl) ⟨282378, by rfl⟩ : syracuseStep 12048149 = 564757) (by norm_num)
theorem B3708701 : Blo 1648023 3708701 := bbase (se 3 (by rfl) ⟨695381, by rfl⟩ : syracuseStep 3708701 = 1390763) (by norm_num)
theorem B2086717 : Blo 1648023 2086717 := bbase (se 3 (by rfl) ⟨391259, by rfl⟩ : syracuseStep 2086717 = 782519) (by norm_num)
theorem B2783045 : Blo 1648023 2783045 := bbase (se 4 (by rfl) ⟨260910, by rfl⟩ : syracuseStep 2783045 = 521821) (by norm_num)
theorem B8345429 : Blo 1648023 8345429 := bbase (se 9 (by rfl) ⟨24449, by rfl⟩ : syracuseStep 8345429 = 48899) (by norm_num)
theorem B3708773 : Blo 1648023 3708773 := bbase (se 4 (by rfl) ⟨347697, by rfl⟩ : syracuseStep 3708773 = 695395) (by norm_num)
theorem B2062201 : Blo 1648023 2062201 := bbase (se 2 (by rfl) ⟨773325, by rfl⟩ : syracuseStep 2062201 = 1546651) (by norm_num)
theorem B2086813 : Blo 1648023 2086813 := bbase (se 3 (by rfl) ⟨391277, by rfl⟩ : syracuseStep 2086813 = 782555) (by norm_num)
theorem B3708845 : Blo 1648023 3708845 := bbase (se 3 (by rfl) ⟨695408, by rfl⟩ : syracuseStep 3708845 = 1390817) (by norm_num)
theorem B2783173 : Blo 1648023 2783173 := bbase (se 4 (by rfl) ⟨260922, by rfl⟩ : syracuseStep 2783173 = 521845) (by norm_num)
theorem B22566869 : Blo 1648023 22566869 := bbase (se 7 (by rfl) ⟨264455, by rfl⟩ : syracuseStep 22566869 = 528911) (by norm_num)
theorem B3708917 : Blo 1648023 3708917 := bbase (se 5 (by rfl) ⟨173855, by rfl⟩ : syracuseStep 3708917 = 347711) (by norm_num)
theorem B2783261 : Blo 1648023 2783261 := bbase (se 3 (by rfl) ⟨521861, by rfl⟩ : syracuseStep 2783261 = 1043723) (by norm_num)
theorem B3708989 : Blo 1648023 3708989 := bbase (se 3 (by rfl) ⟨695435, by rfl⟩ : syracuseStep 3708989 = 1390871) (by norm_num)
theorem B2086985 : Blo 1648023 2086985 := bbase (se 2 (by rfl) ⟨782619, by rfl⟩ : syracuseStep 2086985 = 1565239) (by norm_num)
theorem B1980497 : Blo 1648023 1980497 := bbase (se 2 (by rfl) ⟨742686, by rfl⟩ : syracuseStep 1980497 = 1485373) (by norm_num)
theorem B2971741 : Blo 1648023 2971741 := bbase (se 3 (by rfl) ⟨557201, by rfl⟩ : syracuseStep 2971741 = 1114403) (by norm_num)
theorem B2472053 : Blo 1648023 2472053 := bbase (se 5 (by rfl) ⟨115877, by rfl⟩ : syracuseStep 2472053 = 231755) (by norm_num)
theorem B2087041 : Blo 1648023 2087041 := bbase (se 2 (by rfl) ⟨782640, by rfl⟩ : syracuseStep 2087041 = 1565281) (by norm_num)
theorem B3709061 : Blo 1648023 3709061 := bbase (se 4 (by rfl) ⟨347724, by rfl⟩ : syracuseStep 3709061 = 695449) (by norm_num)
theorem B2472077 : Blo 1648023 2472077 := bbase (se 3 (by rfl) ⟨463514, by rfl⟩ : syracuseStep 2472077 = 927029) (by norm_num)
theorem B2783389 : Blo 1648023 2783389 := bbase (se 3 (by rfl) ⟨521885, by rfl⟩ : syracuseStep 2783389 = 1043771) (by norm_num)
theorem B2472101 : Blo 1648023 2472101 := bbase (se 4 (by rfl) ⟨231759, by rfl⟩ : syracuseStep 2472101 = 463519) (by norm_num)
theorem B5642405 : Blo 1648023 5642405 := bbase (se 4 (by rfl) ⟨528975, by rfl⟩ : syracuseStep 5642405 = 1057951) (by norm_num)
theorem B2472125 : Blo 1648023 2472125 := bbase (se 3 (by rfl) ⟨463523, by rfl⟩ : syracuseStep 2472125 = 927047) (by norm_num)
theorem B3709133 : Blo 1648023 3709133 := bbase (se 3 (by rfl) ⟨695462, by rfl⟩ : syracuseStep 3709133 = 1390925) (by norm_num)
theorem B2472149 : Blo 1648023 2472149 := bbase (se 7 (by rfl) ⟨28970, by rfl⟩ : syracuseStep 2472149 = 57941) (by norm_num)
theorem B12523733 : Blo 1648023 12523733 := bbase (se 7 (by rfl) ⟨146762, by rfl⟩ : syracuseStep 12523733 = 293525) (by norm_num)
theorem B1808605 : Blo 1648023 1808605 := bbase (se 3 (by rfl) ⟨339113, by rfl⟩ : syracuseStep 1808605 = 678227) (by norm_num)
theorem B2087137 : Blo 1648023 2087137 := bbase (se 2 (by rfl) ⟨782676, by rfl⟩ : syracuseStep 2087137 = 1565353) (by norm_num)
theorem B2472173 : Blo 1648023 2472173 := bbase (se 3 (by rfl) ⟨463532, by rfl⟩ : syracuseStep 2472173 = 927065) (by norm_num)
theorem B2783477 : Blo 1648023 2783477 := bbase (se 5 (by rfl) ⟨130475, by rfl⟩ : syracuseStep 2783477 = 260951) (by norm_num)
theorem B2472197 : Blo 1648023 2472197 := bbase (se 4 (by rfl) ⟨231768, by rfl⟩ : syracuseStep 2472197 = 463537) (by norm_num)
theorem B3709205 : Blo 1648023 3709205 := bbase (se 6 (by rfl) ⟨86934, by rfl⟩ : syracuseStep 3709205 = 173869) (by norm_num)
theorem B2472221 : Blo 1648023 2472221 := bbase (se 3 (by rfl) ⟨463541, by rfl⟩ : syracuseStep 2472221 = 927083) (by norm_num)
theorem B2472245 : Blo 1648023 2472245 := bbase (se 5 (by rfl) ⟨115886, by rfl⟩ : syracuseStep 2472245 = 231773) (by norm_num)
theorem B2472269 : Blo 1648023 2472269 := bbase (se 3 (by rfl) ⟨463550, by rfl⟩ : syracuseStep 2472269 = 927101) (by norm_num)
theorem B1694029 : Blo 1648023 1694029 := bbase (se 3 (by rfl) ⟨317630, by rfl⟩ : syracuseStep 1694029 = 635261) (by norm_num)
theorem B3709277 : Blo 1648023 3709277 := bbase (se 3 (by rfl) ⟨695489, by rfl⟩ : syracuseStep 3709277 = 1390979) (by norm_num)
theorem B2472293 : Blo 1648023 2472293 := bbase (se 4 (by rfl) ⟨231777, by rfl⟩ : syracuseStep 2472293 = 463555) (by norm_num)
theorem B2677093 : Blo 1648023 2677093 := bbase (se 4 (by rfl) ⟨250977, by rfl⟩ : syracuseStep 2677093 = 501955) (by norm_num)
theorem B2472317 : Blo 1648023 2472317 := bbase (se 3 (by rfl) ⟨463559, by rfl⟩ : syracuseStep 2472317 = 927119) (by norm_num)
theorem B2087309 : Blo 1648023 2087309 := bbase (se 3 (by rfl) ⟨391370, by rfl⟩ : syracuseStep 2087309 = 782741) (by norm_num)
theorem B2472341 : Blo 1648023 2472341 := bbase (se 6 (by rfl) ⟨57945, by rfl⟩ : syracuseStep 2472341 = 115891) (by norm_num)
theorem B3709349 : Blo 1648023 3709349 := bbase (se 4 (by rfl) ⟨347751, by rfl⟩ : syracuseStep 3709349 = 695503) (by norm_num)
theorem B2472365 : Blo 1648023 2472365 := bbase (se 3 (by rfl) ⟨463568, by rfl⟩ : syracuseStep 2472365 = 927137) (by norm_num)
theorem B2472389 : Blo 1648023 2472389 := bbase (se 4 (by rfl) ⟨231786, by rfl⟩ : syracuseStep 2472389 = 463573) (by norm_num)
theorem B2087365 : Blo 1648023 2087365 := bbase (se 4 (by rfl) ⟨195690, by rfl⟩ : syracuseStep 2087365 = 391381) (by norm_num)
theorem B5642693 : Blo 1648023 5642693 := bbase (se 4 (by rfl) ⟨529002, by rfl⟩ : syracuseStep 5642693 = 1058005) (by norm_num)
theorem B6683093 : Blo 1648023 6683093 := bbase (se 7 (by rfl) ⟨78317, by rfl⟩ : syracuseStep 6683093 = 156635) (by norm_num)
theorem B2472413 : Blo 1648023 2472413 := bbase (se 3 (by rfl) ⟨463577, by rfl⟩ : syracuseStep 2472413 = 927155) (by norm_num)
theorem B4454885 : Blo 1648023 4454885 := bbase (se 4 (by rfl) ⟨417645, by rfl⟩ : syracuseStep 4454885 = 835291) (by norm_num)
theorem B3709421 : Blo 1648023 3709421 := bbase (se 3 (by rfl) ⟨695516, by rfl⟩ : syracuseStep 3709421 = 1391033) (by norm_num)
theorem B2472437 : Blo 1648023 2472437 := bbase (se 5 (by rfl) ⟨115895, by rfl⟩ : syracuseStep 2472437 = 231791) (by norm_num)
theorem B2472461 : Blo 1648023 2472461 := bbase (se 3 (by rfl) ⟨463586, by rfl⟩ : syracuseStep 2472461 = 927173) (by norm_num)
theorem B2472485 : Blo 1648023 2472485 := bbase (se 4 (by rfl) ⟨231795, by rfl⟩ : syracuseStep 2472485 = 463591) (by norm_num)
theorem B2087461 : Blo 1648023 2087461 := bbase (se 4 (by rfl) ⟨195699, by rfl⟩ : syracuseStep 2087461 = 391399) (by norm_num)
theorem B3709493 : Blo 1648023 3709493 := bbase (se 5 (by rfl) ⟨173882, by rfl⟩ : syracuseStep 3709493 = 347765) (by norm_num)
theorem B2472509 : Blo 1648023 2472509 := bbase (se 3 (by rfl) ⟨463595, by rfl⟩ : syracuseStep 2472509 = 927191) (by norm_num)
theorem B2472533 : Blo 1648023 2472533 := bbase (se 8 (by rfl) ⟨14487, by rfl⟩ : syracuseStep 2472533 = 28975) (by norm_num)
theorem B2472557 : Blo 1648023 2472557 := bbase (se 3 (by rfl) ⟨463604, by rfl⟩ : syracuseStep 2472557 = 927209) (by norm_num)
theorem B12515957 : Blo 1648023 12515957 := bbase (se 5 (by rfl) ⟨586685, by rfl⟩ : syracuseStep 12515957 = 1173371) (by norm_num)
theorem B3709565 : Blo 1648023 3709565 := bbase (se 3 (by rfl) ⟨695543, by rfl⟩ : syracuseStep 3709565 = 1391087) (by norm_num)
theorem B2472581 : Blo 1648023 2472581 := bbase (se 4 (by rfl) ⟨231804, by rfl⟩ : syracuseStep 2472581 = 463609) (by norm_num)
theorem B3521173 : Blo 1648023 3521173 := bbase (se 6 (by rfl) ⟨82527, by rfl⟩ : syracuseStep 3521173 = 165055) (by norm_num)
theorem B2472605 : Blo 1648023 2472605 := bbase (se 3 (by rfl) ⟨463613, by rfl⟩ : syracuseStep 2472605 = 927227) (by norm_num)
theorem B2472629 : Blo 1648023 2472629 := bbase (se 5 (by rfl) ⟨115904, by rfl⟩ : syracuseStep 2472629 = 231809) (by norm_num)
theorem B3709637 : Blo 1648023 3709637 := bbase (se 4 (by rfl) ⟨347778, by rfl⟩ : syracuseStep 3709637 = 695557) (by norm_num)
theorem B2472653 : Blo 1648023 2472653 := bbase (se 3 (by rfl) ⟨463622, by rfl⟩ : syracuseStep 2472653 = 927245) (by norm_num)
theorem B2087633 : Blo 1648023 2087633 := bbase (se 2 (by rfl) ⟨782862, by rfl⟩ : syracuseStep 2087633 = 1565725) (by norm_num)
theorem B2472677 : Blo 1648023 2472677 := bbase (se 4 (by rfl) ⟨231813, by rfl⟩ : syracuseStep 2472677 = 463627) (by norm_num)
theorem B10566389 : Blo 1648023 10566389 := bbase (se 5 (by rfl) ⟨495299, by rfl⟩ : syracuseStep 10566389 = 990599) (by norm_num)
theorem B2472701 : Blo 1648023 2472701 := bbase (se 3 (by rfl) ⟨463631, by rfl⟩ : syracuseStep 2472701 = 927263) (by norm_num)
theorem B1981189 : Blo 1648023 1981189 := bbase (se 4 (by rfl) ⟨185736, by rfl⟩ : syracuseStep 1981189 = 371473) (by norm_num)
theorem B3709709 : Blo 1648023 3709709 := bbase (se 3 (by rfl) ⟨695570, by rfl⟩ : syracuseStep 3709709 = 1391141) (by norm_num)
theorem B2472725 : Blo 1648023 2472725 := bbase (se 6 (by rfl) ⟨57954, by rfl⟩ : syracuseStep 2472725 = 115909) (by norm_num)
theorem B2472749 : Blo 1648023 2472749 := bbase (se 3 (by rfl) ⟨463640, by rfl⟩ : syracuseStep 2472749 = 927281) (by norm_num)
theorem B2472773 : Blo 1648023 2472773 := bbase (se 4 (by rfl) ⟨231822, by rfl⟩ : syracuseStep 2472773 = 463645) (by norm_num)
theorem B4455253 : Blo 1648023 4455253 := bbase (se 9 (by rfl) ⟨13052, by rfl⟩ : syracuseStep 4455253 = 26105) (by norm_num)
theorem B3709781 : Blo 1648023 3709781 := bbase (se 9 (by rfl) ⟨10868, by rfl⟩ : syracuseStep 3709781 = 21737) (by norm_num)
theorem B2472797 : Blo 1648023 2472797 := bbase (se 3 (by rfl) ⟨463649, by rfl⟩ : syracuseStep 2472797 = 927299) (by norm_num)
theorem B2472821 : Blo 1648023 2472821 := bbase (se 5 (by rfl) ⟨115913, by rfl⟩ : syracuseStep 2472821 = 231827) (by norm_num)
theorem B2472845 : Blo 1648023 2472845 := bbase (se 3 (by rfl) ⟨463658, by rfl⟩ : syracuseStep 2472845 = 927317) (by norm_num)
theorem B3709853 : Blo 1648023 3709853 := bbase (se 3 (by rfl) ⟨695597, by rfl⟩ : syracuseStep 3709853 = 1391195) (by norm_num)
theorem B2472869 : Blo 1648023 2472869 := bbase (se 4 (by rfl) ⟨231831, by rfl⟩ : syracuseStep 2472869 = 463663) (by norm_num)
theorem B2472893 : Blo 1648023 2472893 := bbase (se 3 (by rfl) ⟨463667, by rfl⟩ : syracuseStep 2472893 = 927335) (by norm_num)
theorem B2472917 : Blo 1648023 2472917 := bbase (se 7 (by rfl) ⟨28979, by rfl⟩ : syracuseStep 2472917 = 57959) (by norm_num)
theorem B1981405 : Blo 1648023 1981405 := bbase (se 3 (by rfl) ⟨371513, by rfl⟩ : syracuseStep 1981405 = 743027) (by norm_num)
theorem B3709925 : Blo 1648023 3709925 := bbase (se 4 (by rfl) ⟨347805, by rfl⟩ : syracuseStep 3709925 = 695611) (by norm_num)
theorem B2472941 : Blo 1648023 2472941 := bbase (se 3 (by rfl) ⟨463676, by rfl⟩ : syracuseStep 2472941 = 927353) (by norm_num)
theorem B2472965 : Blo 1648023 2472965 := bbase (se 4 (by rfl) ⟨231840, by rfl⟩ : syracuseStep 2472965 = 463681) (by norm_num)
theorem B3521549 : Blo 1648023 3521549 := bbase (se 3 (by rfl) ⟨660290, by rfl⟩ : syracuseStep 3521549 = 1320581) (by norm_num)
theorem B2472989 : Blo 1648023 2472989 := bbase (se 3 (by rfl) ⟨463685, by rfl⟩ : syracuseStep 2472989 = 927371) (by norm_num)
theorem B3709997 : Blo 1648023 3709997 := bbase (se 3 (by rfl) ⟨695624, by rfl⟩ : syracuseStep 3709997 = 1391249) (by norm_num)
theorem B2473013 : Blo 1648023 2473013 := bbase (se 5 (by rfl) ⟨115922, by rfl⟩ : syracuseStep 2473013 = 231845) (by norm_num)
theorem B2473037 : Blo 1648023 2473037 := bbase (se 3 (by rfl) ⟨463694, by rfl⟩ : syracuseStep 2473037 = 927389) (by norm_num)
theorem B16055381 : Blo 1648023 16055381 := bbase (se 8 (by rfl) ⟨94074, by rfl⟩ : syracuseStep 16055381 = 188149) (by norm_num)
theorem B3570773 : Blo 1648023 3570773 := bbase (se 8 (by rfl) ⟨20922, by rfl⟩ : syracuseStep 3570773 = 41845) (by norm_num)
theorem B2473061 : Blo 1648023 2473061 := bbase (se 4 (by rfl) ⟨231849, by rfl⟩ : syracuseStep 2473061 = 463699) (by norm_num)
theorem B8346725 : Blo 1648023 8346725 := bbase (se 4 (by rfl) ⟨782505, by rfl⟩ : syracuseStep 8346725 = 1565011) (by norm_num)
theorem B3710069 : Blo 1648023 3710069 := bbase (se 5 (by rfl) ⟨173909, by rfl⟩ : syracuseStep 3710069 = 347819) (by norm_num)
theorem B2473085 : Blo 1648023 2473085 := bbase (se 3 (by rfl) ⟨463703, by rfl⟩ : syracuseStep 2473085 = 927407) (by norm_num)
theorem B2473109 : Blo 1648023 2473109 := bbase (se 6 (by rfl) ⟨57963, by rfl⟩ : syracuseStep 2473109 = 115927) (by norm_num)
theorem B2473133 : Blo 1648023 2473133 := bbase (se 3 (by rfl) ⟨463712, by rfl⟩ : syracuseStep 2473133 = 927425) (by norm_num)
theorem B3710141 : Blo 1648023 3710141 := bbase (se 3 (by rfl) ⟨695651, by rfl⟩ : syracuseStep 3710141 = 1391303) (by norm_num)
theorem B2473157 : Blo 1648023 2473157 := bbase (se 4 (by rfl) ⟨231858, by rfl⟩ : syracuseStep 2473157 = 463717) (by norm_num)
theorem B2473181 : Blo 1648023 2473181 := bbase (se 3 (by rfl) ⟨463721, by rfl⟩ : syracuseStep 2473181 = 927443) (by norm_num)
theorem B1760501 : Blo 1648023 1760501 := bbase (se 5 (by rfl) ⟨82523, by rfl⟩ : syracuseStep 1760501 = 165047) (by norm_num)
theorem B2473205 : Blo 1648023 2473205 := bbase (se 5 (by rfl) ⟨115931, by rfl⟩ : syracuseStep 2473205 = 231863) (by norm_num)
theorem B3710213 : Blo 1648023 3710213 := bbase (se 4 (by rfl) ⟨347832, by rfl⟩ : syracuseStep 3710213 = 695665) (by norm_num)
theorem B2473229 : Blo 1648023 2473229 := bbase (se 3 (by rfl) ⟨463730, by rfl⟩ : syracuseStep 2473229 = 927461) (by norm_num)
theorem B2473253 : Blo 1648023 2473253 := bbase (se 4 (by rfl) ⟨231867, by rfl⟩ : syracuseStep 2473253 = 463735) (by norm_num)
theorem B7920949 : Blo 1648023 7920949 := bbase (se 5 (by rfl) ⟨371294, by rfl⟩ : syracuseStep 7920949 = 742589) (by norm_num)
theorem B2473277 : Blo 1648023 2473277 := bbase (se 3 (by rfl) ⟨463739, by rfl⟩ : syracuseStep 2473277 = 927479) (by norm_num)
theorem B3710285 : Blo 1648023 3710285 := bbase (se 3 (by rfl) ⟨695678, by rfl⟩ : syracuseStep 3710285 = 1391357) (by norm_num)
theorem B2473301 : Blo 1648023 2473301 := bbase (se 11 (by rfl) ⟨1811, by rfl⟩ : syracuseStep 2473301 = 3623) (by norm_num)
theorem B2473325 : Blo 1648023 2473325 := bbase (se 3 (by rfl) ⟨463748, by rfl⟩ : syracuseStep 2473325 = 927497) (by norm_num)
theorem B3128701 : Blo 1648023 3128701 := bbase (se 3 (by rfl) ⟨586631, by rfl⟩ : syracuseStep 3128701 = 1173263) (by norm_num)
theorem B2473349 : Blo 1648023 2473349 := bbase (se 4 (by rfl) ⟨231876, by rfl⟩ : syracuseStep 2473349 = 463753) (by norm_num)
theorem B3710357 : Blo 1648023 3710357 := bbase (se 6 (by rfl) ⟨86961, by rfl⟩ : syracuseStep 3710357 = 173923) (by norm_num)
theorem B2473373 : Blo 1648023 2473373 := bbase (se 3 (by rfl) ⟨463757, by rfl⟩ : syracuseStep 2473373 = 927515) (by norm_num)
theorem B2473397 : Blo 1648023 2473397 := bbase (se 5 (by rfl) ⟨115940, by rfl⟩ : syracuseStep 2473397 = 231881) (by norm_num)
theorem B9649589 : Blo 1648023 9649589 := bbase (se 5 (by rfl) ⟨452324, by rfl⟩ : syracuseStep 9649589 = 904649) (by norm_num)
theorem B7044533 : Blo 1648023 7044533 := bbase (se 5 (by rfl) ⟨330212, by rfl⟩ : syracuseStep 7044533 = 660425) (by norm_num)
theorem B2473421 : Blo 1648023 2473421 := bbase (se 3 (by rfl) ⟨463766, by rfl⟩ : syracuseStep 2473421 = 927533) (by norm_num)
theorem B3710429 : Blo 1648023 3710429 := bbase (se 3 (by rfl) ⟨695705, by rfl⟩ : syracuseStep 3710429 = 1391411) (by norm_num)
theorem B2473445 : Blo 1648023 2473445 := bbase (se 4 (by rfl) ⟨231885, by rfl⟩ : syracuseStep 2473445 = 463771) (by norm_num)
theorem B1785317 : Blo 1648023 1785317 := bbase (se 4 (by rfl) ⟨167373, by rfl⟩ : syracuseStep 1785317 = 334747) (by norm_num)
theorem B2473469 : Blo 1648023 2473469 := bbase (se 3 (by rfl) ⟨463775, by rfl⟩ : syracuseStep 2473469 = 927551) (by norm_num)
theorem B2473493 : Blo 1648023 2473493 := bbase (se 6 (by rfl) ⟨57972, by rfl⟩ : syracuseStep 2473493 = 115945) (by norm_num)
theorem B3128861 : Blo 1648023 3128861 := bbase (se 3 (by rfl) ⟨586661, by rfl⟩ : syracuseStep 3128861 = 1173323) (by norm_num)
theorem B3710501 : Blo 1648023 3710501 := bbase (se 4 (by rfl) ⟨347859, by rfl⟩ : syracuseStep 3710501 = 695719) (by norm_num)
theorem B2473517 : Blo 1648023 2473517 := bbase (se 3 (by rfl) ⟨463784, by rfl⟩ : syracuseStep 2473517 = 927569) (by norm_num)
theorem B2473541 : Blo 1648023 2473541 := bbase (se 4 (by rfl) ⟨231894, by rfl⟩ : syracuseStep 2473541 = 463789) (by norm_num)
theorem B2473565 : Blo 1648023 2473565 := bbase (se 3 (by rfl) ⟨463793, by rfl⟩ : syracuseStep 2473565 = 927587) (by norm_num)
theorem B3710573 : Blo 1648023 3710573 := bbase (se 3 (by rfl) ⟨695732, by rfl⟩ : syracuseStep 3710573 = 1391465) (by norm_num)
theorem B4693621 : Blo 1648023 4693621 := bbase (se 5 (by rfl) ⟨220013, by rfl⟩ : syracuseStep 4693621 = 440027) (by norm_num)
theorem B2473589 : Blo 1648023 2473589 := bbase (se 5 (by rfl) ⟨115949, by rfl⟩ : syracuseStep 2473589 = 231899) (by norm_num)
theorem B2473613 : Blo 1648023 2473613 := bbase (se 3 (by rfl) ⟨463802, by rfl⟩ : syracuseStep 2473613 = 927605) (by norm_num)
theorem B2473637 : Blo 1648023 2473637 := bbase (se 4 (by rfl) ⟨231903, by rfl⟩ : syracuseStep 2473637 = 463807) (by norm_num)
theorem B3129005 : Blo 1648023 3129005 := bbase (se 3 (by rfl) ⟨586688, by rfl⟩ : syracuseStep 3129005 = 1173377) (by norm_num)
theorem B1760945 : Blo 1648023 1760945 := bbase (se 2 (by rfl) ⟨660354, by rfl⟩ : syracuseStep 1760945 = 1320709) (by norm_num)
theorem B3710645 : Blo 1648023 3710645 := bbase (se 5 (by rfl) ⟨173936, by rfl⟩ : syracuseStep 3710645 = 347873) (by norm_num)
theorem B2473661 : Blo 1648023 2473661 := bbase (se 3 (by rfl) ⟨463811, by rfl⟩ : syracuseStep 2473661 = 927623) (by norm_num)
theorem B2473685 : Blo 1648023 2473685 := bbase (se 7 (by rfl) ⟨28988, by rfl⟩ : syracuseStep 2473685 = 57977) (by norm_num)
theorem B2473709 : Blo 1648023 2473709 := bbase (se 3 (by rfl) ⟨463820, by rfl⟩ : syracuseStep 2473709 = 927641) (by norm_num)
theorem B3710717 : Blo 1648023 3710717 := bbase (se 3 (by rfl) ⟨695759, by rfl⟩ : syracuseStep 3710717 = 1391519) (by norm_num)
theorem B2473733 : Blo 1648023 2473733 := bbase (se 4 (by rfl) ⟨231912, by rfl⟩ : syracuseStep 2473733 = 463825) (by norm_num)
theorem B4693781 : Blo 1648023 4693781 := bbase (se 6 (by rfl) ⟨110010, by rfl⟩ : syracuseStep 4693781 = 220021) (by norm_num)
theorem B5283605 : Blo 1648023 5283605 := bbase (se 6 (by rfl) ⟨123834, by rfl⟩ : syracuseStep 5283605 = 247669) (by norm_num)
theorem B2473757 : Blo 1648023 2473757 := bbase (se 3 (by rfl) ⟨463829, by rfl⟩ : syracuseStep 2473757 = 927659) (by norm_num)
theorem B8912693 : Blo 1648023 8912693 := bbase (se 5 (by rfl) ⟨417782, by rfl⟩ : syracuseStep 8912693 = 835565) (by norm_num)
theorem B2473781 : Blo 1648023 2473781 := bbase (se 5 (by rfl) ⟨115958, by rfl⟩ : syracuseStep 2473781 = 231917) (by norm_num)
theorem B3710789 : Blo 1648023 3710789 := bbase (se 4 (by rfl) ⟨347886, by rfl⟩ : syracuseStep 3710789 = 695773) (by norm_num)
theorem B2473805 : Blo 1648023 2473805 := bbase (se 3 (by rfl) ⟨463838, by rfl⟩ : syracuseStep 2473805 = 927677) (by norm_num)
theorem B2473829 : Blo 1648023 2473829 := bbase (se 4 (by rfl) ⟨231921, by rfl⟩ : syracuseStep 2473829 = 463843) (by norm_num)
theorem B2473853 : Blo 1648023 2473853 := bbase (se 3 (by rfl) ⟨463847, by rfl⟩ : syracuseStep 2473853 = 927695) (by norm_num)
theorem B3710861 : Blo 1648023 3710861 := bbase (se 3 (by rfl) ⟨695786, by rfl⟩ : syracuseStep 3710861 = 1391573) (by norm_num)
theorem B2473877 : Blo 1648023 2473877 := bbase (se 6 (by rfl) ⟨57981, by rfl⟩ : syracuseStep 2473877 = 115963) (by norm_num)
theorem B1761193 : Blo 1648023 1761193 := bbase (se 2 (by rfl) ⟨660447, by rfl⟩ : syracuseStep 1761193 = 1320895) (by norm_num)
theorem B2473901 : Blo 1648023 2473901 := bbase (se 3 (by rfl) ⟨463856, by rfl⟩ : syracuseStep 2473901 = 927713) (by norm_num)
theorem B2473925 : Blo 1648023 2473925 := bbase (se 4 (by rfl) ⟨231930, by rfl⟩ : syracuseStep 2473925 = 463861) (by norm_num)
theorem B3129293 : Blo 1648023 3129293 := bbase (se 3 (by rfl) ⟨586742, by rfl⟩ : syracuseStep 3129293 = 1173485) (by norm_num)
theorem B3710933 : Blo 1648023 3710933 := bbase (se 7 (by rfl) ⟨43487, by rfl⟩ : syracuseStep 3710933 = 86975) (by norm_num)
theorem B2473949 : Blo 1648023 2473949 := bbase (se 3 (by rfl) ⟨463865, by rfl⟩ : syracuseStep 2473949 = 927731) (by norm_num)
theorem B2473973 : Blo 1648023 2473973 := bbase (se 5 (by rfl) ⟨115967, by rfl⟩ : syracuseStep 2473973 = 231935) (by norm_num)
theorem B2473985 : Blo 1648023 2473985 := bstep (se 2 (by rfl) ⟨927744, by rfl⟩ : syracuseStep 2473985 = 1855489) B1855489
theorem B3129347 : Blo 1648023 3129347 := bstep (se 1 (by rfl) ⟨2347010, by rfl⟩ : syracuseStep 3129347 = 4694021) B4694021
theorem B2474003 : Blo 1648023 2474003 := bstep (se 1 (by rfl) ⟨1855502, by rfl⟩ : syracuseStep 2474003 = 3711005) B3711005
theorem B8347697 : Blo 1648023 8347697 := bstep (se 2 (by rfl) ⟨3130386, by rfl⟩ : syracuseStep 8347697 = 6260773) B6260773
theorem B2474033 : Blo 1648023 2474033 := bstep (se 2 (by rfl) ⟨927762, by rfl⟩ : syracuseStep 2474033 = 1855525) B1855525
theorem B2474051 : Blo 1648023 2474051 := bstep (se 1 (by rfl) ⟨1855538, by rfl⟩ : syracuseStep 2474051 = 3711077) B3711077
theorem B4456529 : Blo 1648023 4456529 := bstep (se 2 (by rfl) ⟨1671198, by rfl⟩ : syracuseStep 4456529 = 3342397) B3342397
theorem B2474081 : Blo 1648023 2474081 := bstep (se 2 (by rfl) ⟨927780, by rfl⟩ : syracuseStep 2474081 = 1855561) B1855561
theorem B2474099 : Blo 1648023 2474099 := bstep (se 1 (by rfl) ⟨1855574, by rfl⟩ : syracuseStep 2474099 = 3711149) B3711149
theorem B6258829 : Blo 1648023 6258829 := bstep (se 3 (by rfl) ⟨1173530, by rfl⟩ : syracuseStep 6258829 = 2347061) B2347061
theorem B2474129 : Blo 1648023 2474129 := bstep (se 2 (by rfl) ⟨927798, by rfl⟩ : syracuseStep 2474129 = 1855597) B1855597
theorem B2474147 : Blo 1648023 2474147 := bstep (se 1 (by rfl) ⟨1855610, by rfl⟩ : syracuseStep 2474147 = 3711221) B3711221
theorem B2474177 : Blo 1648023 2474177 := bstep (se 2 (by rfl) ⟨927816, by rfl⟩ : syracuseStep 2474177 = 1855633) B1855633
theorem B1761475 : Blo 1648023 1761475 := bstep (se 1 (by rfl) ⟨1321106, by rfl⟩ : syracuseStep 1761475 = 2642213) B2642213
theorem B3711185 : Blo 1648023 3711185 := bstep (se 2 (by rfl) ⟨1391694, by rfl⟩ : syracuseStep 3711185 = 2783389) B2783389
theorem B2474195 : Blo 1648023 2474195 := bstep (se 1 (by rfl) ⟨1855646, by rfl⟩ : syracuseStep 2474195 = 3711293) B3711293
theorem B3711203 : Blo 1648023 3711203 := bstep (se 1 (by rfl) ⟨2783402, by rfl⟩ : syracuseStep 3711203 = 5566805) B5566805
theorem B2474225 : Blo 1648023 2474225 := bstep (se 2 (by rfl) ⟨927834, by rfl⟩ : syracuseStep 2474225 = 1855669) B1855669
theorem B2474243 : Blo 1648023 2474243 := bstep (se 1 (by rfl) ⟨1855682, by rfl⟩ : syracuseStep 2474243 = 3711365) B3711365
theorem B2474273 : Blo 1648023 2474273 := bstep (se 2 (by rfl) ⟨927852, by rfl⟩ : syracuseStep 2474273 = 1855705) B1855705
theorem B3522865 : Blo 1648023 3522865 := bstep (se 2 (by rfl) ⟨1321074, by rfl⟩ : syracuseStep 3522865 = 2642149) B2642149
theorem B5562701 : Blo 1648023 5562701 := bstep (se 3 (by rfl) ⟨1043006, by rfl⟩ : syracuseStep 5562701 = 2086013) B2086013
theorem B5562755 : Blo 1648023 5562755 := bstep (se 1 (by rfl) ⟨4172066, by rfl⟩ : syracuseStep 5562755 = 8344133) B8344133
theorem B501481925 : Blo 1648023 501481925 := bstep (se 4 (by rfl) ⟨47013930, by rfl⟩ : syracuseStep 501481925 = 94027861) B94027861
theorem B12517901 : Blo 1648023 12517901 := bstep (se 3 (by rfl) ⟨2347106, by rfl⟩ : syracuseStep 12517901 = 4694213) B4694213
theorem B4694669 : Blo 1648023 4694669 := bstep (se 3 (by rfl) ⟨880250, by rfl⟩ : syracuseStep 4694669 = 1760501) B1760501
theorem B5563025 : Blo 1648023 5563025 := bstep (se 2 (by rfl) ⟨2086134, by rfl⟩ : syracuseStep 5563025 = 4172269) B4172269
theorem B4760291 : Blo 1648023 4760291 := bstep (se 1 (by rfl) ⟨3570218, by rfl⟩ : syracuseStep 4760291 = 7140437) B7140437
theorem B2228995 : Blo 1648023 2228995 := bstep (se 1 (by rfl) ⟨1671746, by rfl⟩ : syracuseStep 2228995 = 3343493) B3343493
theorem B4694851 : Blo 1648023 4694851 := bstep (se 1 (by rfl) ⟨3521138, by rfl⟩ : syracuseStep 4694851 = 7042277) B7042277
theorem B4694897 : Blo 1648023 4694897 := bstep (se 2 (by rfl) ⟨1760586, by rfl⟩ : syracuseStep 4694897 = 3521173) B3521173
theorem B6259619 : Blo 1648023 6259619 := bstep (se 1 (by rfl) ⟨4694714, by rfl⟩ : syracuseStep 6259619 = 9389429) B9389429
theorem B6865955 : Blo 1648023 6865955 := bstep (se 1 (by rfl) ⟨5149466, by rfl⟩ : syracuseStep 6865955 = 10298933) B10298933
theorem B3130417 : Blo 1648023 3130417 := bstep (se 2 (by rfl) ⟨1173906, by rfl⟩ : syracuseStep 3130417 = 2347813) B2347813
theorem B9389155 : Blo 1648023 9389155 := bstep (se 1 (by rfl) ⟨7041866, by rfl⟩ : syracuseStep 9389155 = 14083733) B14083733
theorem B5940337 : Blo 1648023 5940337 := bstep (se 2 (by rfl) ⟨2227626, by rfl⟩ : syracuseStep 5940337 = 4455253) B4455253
theorem B25732237 : Blo 1648023 25732237 := bstep (se 3 (by rfl) ⟨4824794, by rfl⟩ : syracuseStep 25732237 = 9649589) B9649589
theorem B5563565 : Blo 1648023 5563565 := bstep (se 3 (by rfl) ⟨1043168, by rfl⟩ : syracuseStep 5563565 = 2086337) B2086337
theorem B5563619 : Blo 1648023 5563619 := bstep (se 1 (by rfl) ⟨4172714, by rfl⟩ : syracuseStep 5563619 = 8345429) B8345429
theorem B21136625 : Blo 1648023 21136625 := bstep (se 2 (by rfl) ⟨7926234, by rfl⟩ : syracuseStep 21136625 = 15852469) B15852469
theorem B11879693 : Blo 1648023 11879693 := bstep (se 3 (by rfl) ⟨2227442, by rfl⟩ : syracuseStep 11879693 = 4454885) B4454885
theorem B4760845 : Blo 1648023 4760845 := bstep (se 3 (by rfl) ⟨892658, by rfl⟩ : syracuseStep 4760845 = 1785317) B1785317
theorem B10028357 : Blo 1648023 10028357 := bstep (se 4 (by rfl) ⟨940158, by rfl⟩ : syracuseStep 10028357 = 1880317) B1880317
theorem B1648035 : Blo 1648023 1648035 := bstep (se 1 (by rfl) ⟨1236026, by rfl⟩ : syracuseStep 1648035 = 2472053) B2472053
theorem B1648051 : Blo 1648023 1648051 := bstep (se 1 (by rfl) ⟨1236038, by rfl⟩ : syracuseStep 1648051 = 2472077) B2472077
theorem B1648067 : Blo 1648023 1648067 := bstep (se 1 (by rfl) ⟨1236050, by rfl⟩ : syracuseStep 1648067 = 2472101) B2472101
theorem B3761603 : Blo 1648023 3761603 := bstep (se 1 (by rfl) ⟨2821202, by rfl⟩ : syracuseStep 3761603 = 5642405) B5642405
theorem B1648083 : Blo 1648023 1648083 := bstep (se 1 (by rfl) ⟨1236062, by rfl⟩ : syracuseStep 1648083 = 2472125) B2472125
theorem B1648099 : Blo 1648023 1648099 := bstep (se 1 (by rfl) ⟨1236074, by rfl⟩ : syracuseStep 1648099 = 2472149) B2472149
theorem B8349155 : Blo 1648023 8349155 := bstep (se 1 (by rfl) ⟨6261866, by rfl⟩ : syracuseStep 8349155 = 12523733) B12523733
theorem B11879921 : Blo 1648023 11879921 := bstep (se 2 (by rfl) ⟨4454970, by rfl⟩ : syracuseStep 11879921 = 8909941) B8909941
theorem B1648115 : Blo 1648023 1648115 := bstep (se 1 (by rfl) ⟨1236086, by rfl⟩ : syracuseStep 1648115 = 2472173) B2472173
theorem B5563889 : Blo 1648023 5563889 := bstep (se 2 (by rfl) ⟨2086458, by rfl⟩ : syracuseStep 5563889 = 4172917) B4172917
theorem B1648131 : Blo 1648023 1648131 := bstep (se 1 (by rfl) ⟨1236098, by rfl⟩ : syracuseStep 1648131 = 2472197) B2472197
theorem B1648147 : Blo 1648023 1648147 := bstep (se 1 (by rfl) ⟨1236110, by rfl⟩ : syracuseStep 1648147 = 2472221) B2472221
theorem B3343889 : Blo 1648023 3343889 := bstep (se 2 (by rfl) ⟨1253958, by rfl⟩ : syracuseStep 3343889 = 2507917) B2507917
theorem B1648163 : Blo 1648023 1648163 := bstep (se 1 (by rfl) ⟨1236122, by rfl⟩ : syracuseStep 1648163 = 2472245) B2472245
theorem B6260273 : Blo 1648023 6260273 := bstep (se 2 (by rfl) ⟨2347602, by rfl⟩ : syracuseStep 6260273 = 4695205) B4695205
theorem B1648179 : Blo 1648023 1648179 := bstep (se 1 (by rfl) ⟨1236134, by rfl⟩ : syracuseStep 1648179 = 2472269) B2472269
theorem B1648195 : Blo 1648023 1648195 := bstep (se 1 (by rfl) ⟨1236146, by rfl⟩ : syracuseStep 1648195 = 2472293) B2472293
theorem B1648211 : Blo 1648023 1648211 := bstep (se 1 (by rfl) ⟨1236158, by rfl⟩ : syracuseStep 1648211 = 2472317) B2472317
theorem B1648227 : Blo 1648023 1648227 := bstep (se 1 (by rfl) ⟨1236170, by rfl⟩ : syracuseStep 1648227 = 2472341) B2472341
theorem B9389681 : Blo 1648023 9389681 := bstep (se 2 (by rfl) ⟨3521130, by rfl⟩ : syracuseStep 9389681 = 7042261) B7042261
theorem B1648243 : Blo 1648023 1648243 := bstep (se 1 (by rfl) ⟨1236182, by rfl⟩ : syracuseStep 1648243 = 2472365) B2472365
theorem B1648259 : Blo 1648023 1648259 := bstep (se 1 (by rfl) ⟨1236194, by rfl⟩ : syracuseStep 1648259 = 2472389) B2472389
theorem B3761795 : Blo 1648023 3761795 := bstep (se 1 (by rfl) ⟨2821346, by rfl⟩ : syracuseStep 3761795 = 5642693) B5642693
theorem B1648275 : Blo 1648023 1648275 := bstep (se 1 (by rfl) ⟨1236206, by rfl⟩ : syracuseStep 1648275 = 2472413) B2472413
theorem B1648291 : Blo 1648023 1648291 := bstep (se 1 (by rfl) ⟨1236218, by rfl⟩ : syracuseStep 1648291 = 2472437) B2472437
theorem B1648307 : Blo 1648023 1648307 := bstep (se 1 (by rfl) ⟨1236230, by rfl⟩ : syracuseStep 1648307 = 2472461) B2472461
theorem B1648323 : Blo 1648023 1648323 := bstep (se 1 (by rfl) ⟨1236242, by rfl⟩ : syracuseStep 1648323 = 2472485) B2472485
theorem B1648339 : Blo 1648023 1648339 := bstep (se 1 (by rfl) ⟨1236254, by rfl⟩ : syracuseStep 1648339 = 2472509) B2472509
theorem B1648355 : Blo 1648023 1648355 := bstep (se 1 (by rfl) ⟨1236266, by rfl⟩ : syracuseStep 1648355 = 2472533) B2472533
theorem B10561265 : Blo 1648023 10561265 := bstep (se 2 (by rfl) ⟨3960474, by rfl⟩ : syracuseStep 10561265 = 7920949) B7920949
theorem B1648371 : Blo 1648023 1648371 := bstep (se 1 (by rfl) ⟨1236278, by rfl⟩ : syracuseStep 1648371 = 2472557) B2472557
theorem B1648387 : Blo 1648023 1648387 := bstep (se 1 (by rfl) ⟨1236290, by rfl⟩ : syracuseStep 1648387 = 2472581) B2472581
theorem B1648403 : Blo 1648023 1648403 := bstep (se 1 (by rfl) ⟨1236302, by rfl⟩ : syracuseStep 1648403 = 2472605) B2472605
theorem B1648419 : Blo 1648023 1648419 := bstep (se 1 (by rfl) ⟨1236314, by rfl⟩ : syracuseStep 1648419 = 2472629) B2472629
theorem B2819875 : Blo 1648023 2819875 := bstep (se 1 (by rfl) ⟨2114906, by rfl⟩ : syracuseStep 2819875 = 4229813) B4229813
theorem B1648435 : Blo 1648023 1648435 := bstep (se 1 (by rfl) ⟨1236326, by rfl⟩ : syracuseStep 1648435 = 2472653) B2472653
theorem B1648451 : Blo 1648023 1648451 := bstep (se 1 (by rfl) ⟨1236338, by rfl⟩ : syracuseStep 1648451 = 2472677) B2472677
theorem B4171601 : Blo 1648023 4171601 := bstep (se 2 (by rfl) ⟨1564350, by rfl⟩ : syracuseStep 4171601 = 3128701) B3128701
theorem B1648467 : Blo 1648023 1648467 := bstep (se 1 (by rfl) ⟨1236350, by rfl⟩ : syracuseStep 1648467 = 2472701) B2472701
theorem B1648483 : Blo 1648023 1648483 := bstep (se 1 (by rfl) ⟨1236362, by rfl⟩ : syracuseStep 1648483 = 2472725) B2472725
theorem B1648499 : Blo 1648023 1648499 := bstep (se 1 (by rfl) ⟨1236374, by rfl⟩ : syracuseStep 1648499 = 2472749) B2472749
theorem B1648515 : Blo 1648023 1648515 := bstep (se 1 (by rfl) ⟨1236386, by rfl⟩ : syracuseStep 1648515 = 2472773) B2472773
theorem B1648531 : Blo 1648023 1648531 := bstep (se 1 (by rfl) ⟨1236398, by rfl⟩ : syracuseStep 1648531 = 2472797) B2472797
theorem B1648547 : Blo 1648023 1648547 := bstep (se 1 (by rfl) ⟨1236410, by rfl⟩ : syracuseStep 1648547 = 2472821) B2472821
theorem B1648563 : Blo 1648023 1648563 := bstep (se 1 (by rfl) ⟨1236422, by rfl⟩ : syracuseStep 1648563 = 2472845) B2472845
theorem B1648579 : Blo 1648023 1648579 := bstep (se 1 (by rfl) ⟨1236434, by rfl⟩ : syracuseStep 1648579 = 2472869) B2472869
theorem B1648595 : Blo 1648023 1648595 := bstep (se 1 (by rfl) ⟨1236446, by rfl⟩ : syracuseStep 1648595 = 2472893) B2472893
theorem B1648611 : Blo 1648023 1648611 := bstep (se 1 (by rfl) ⟨1236458, by rfl⟩ : syracuseStep 1648611 = 2472917) B2472917
theorem B1648627 : Blo 1648023 1648627 := bstep (se 1 (by rfl) ⟨1236470, by rfl⟩ : syracuseStep 1648627 = 2472941) B2472941
theorem B1648643 : Blo 1648023 1648643 := bstep (se 1 (by rfl) ⟨1236482, by rfl⟩ : syracuseStep 1648643 = 2472965) B2472965
theorem B5564429 : Blo 1648023 5564429 := bstep (se 3 (by rfl) ⟨1043330, by rfl⟩ : syracuseStep 5564429 = 2086661) B2086661
theorem B1648659 : Blo 1648023 1648659 := bstep (se 1 (by rfl) ⟨1236494, by rfl⟩ : syracuseStep 1648659 = 2472989) B2472989
theorem B1648675 : Blo 1648023 1648675 := bstep (se 1 (by rfl) ⟨1236506, by rfl⟩ : syracuseStep 1648675 = 2473013) B2473013
theorem B1648691 : Blo 1648023 1648691 := bstep (se 1 (by rfl) ⟨1236518, by rfl⟩ : syracuseStep 1648691 = 2473037) B2473037
theorem B1648707 : Blo 1648023 1648707 := bstep (se 1 (by rfl) ⟨1236530, by rfl⟩ : syracuseStep 1648707 = 2473061) B2473061
theorem B5564483 : Blo 1648023 5564483 := bstep (se 1 (by rfl) ⟨4173362, by rfl⟩ : syracuseStep 5564483 = 8346725) B8346725
theorem B3131473 : Blo 1648023 3131473 := bstep (se 2 (by rfl) ⟨1174302, by rfl⟩ : syracuseStep 3131473 = 2348605) B2348605
theorem B1648723 : Blo 1648023 1648723 := bstep (se 1 (by rfl) ⟨1236542, by rfl⟩ : syracuseStep 1648723 = 2473085) B2473085
theorem B1648739 : Blo 1648023 1648739 := bstep (se 1 (by rfl) ⟨1236554, by rfl⟩ : syracuseStep 1648739 = 2473109) B2473109
theorem B1648755 : Blo 1648023 1648755 := bstep (se 1 (by rfl) ⟨1236566, by rfl⟩ : syracuseStep 1648755 = 2473133) B2473133
theorem B1648771 : Blo 1648023 1648771 := bstep (se 1 (by rfl) ⟨1236578, by rfl⟩ : syracuseStep 1648771 = 2473157) B2473157
theorem B1648787 : Blo 1648023 1648787 := bstep (se 1 (by rfl) ⟨1236590, by rfl⟩ : syracuseStep 1648787 = 2473181) B2473181
theorem B1648803 : Blo 1648023 1648803 := bstep (se 1 (by rfl) ⟨1236602, by rfl⟩ : syracuseStep 1648803 = 2473205) B2473205
theorem B1648819 : Blo 1648023 1648819 := bstep (se 1 (by rfl) ⟨1236614, by rfl⟩ : syracuseStep 1648819 = 2473229) B2473229
theorem B1648835 : Blo 1648023 1648835 := bstep (se 1 (by rfl) ⟨1236626, by rfl⟩ : syracuseStep 1648835 = 2473253) B2473253
theorem B1648851 : Blo 1648023 1648851 := bstep (se 1 (by rfl) ⟨1236638, by rfl⟩ : syracuseStep 1648851 = 2473277) B2473277
theorem B1648867 : Blo 1648023 1648867 := bstep (se 1 (by rfl) ⟨1236650, by rfl⟩ : syracuseStep 1648867 = 2473301) B2473301
theorem B1648883 : Blo 1648023 1648883 := bstep (se 1 (by rfl) ⟨1236662, by rfl⟩ : syracuseStep 1648883 = 2473325) B2473325
theorem B2640131 : Blo 1648023 2640131 := bstep (se 1 (by rfl) ⟨1980098, by rfl⟩ : syracuseStep 2640131 = 3960197) B3960197
theorem B1648899 : Blo 1648023 1648899 := bstep (se 1 (by rfl) ⟨1236674, by rfl⟩ : syracuseStep 1648899 = 2473349) B2473349
theorem B8349965 : Blo 1648023 8349965 := bstep (se 3 (by rfl) ⟨1565618, by rfl⟩ : syracuseStep 8349965 = 3131237) B3131237
theorem B1648915 : Blo 1648023 1648915 := bstep (se 1 (by rfl) ⟨1236686, by rfl⟩ : syracuseStep 1648915 = 2473373) B2473373
theorem B1648931 : Blo 1648023 1648931 := bstep (se 1 (by rfl) ⟨1236698, by rfl⟩ : syracuseStep 1648931 = 2473397) B2473397
theorem B4696355 : Blo 1648023 4696355 := bstep (se 1 (by rfl) ⟨3522266, by rfl⟩ : syracuseStep 4696355 = 7044533) B7044533
theorem B1648947 : Blo 1648023 1648947 := bstep (se 1 (by rfl) ⟨1236710, by rfl⟩ : syracuseStep 1648947 = 2473421) B2473421
theorem B1648963 : Blo 1648023 1648963 := bstep (se 1 (by rfl) ⟨1236722, by rfl⟩ : syracuseStep 1648963 = 2473445) B2473445
theorem B5564753 : Blo 1648023 5564753 := bstep (se 2 (by rfl) ⟨2086782, by rfl⟩ : syracuseStep 5564753 = 4173565) B4173565
theorem B1648979 : Blo 1648023 1648979 := bstep (se 1 (by rfl) ⟨1236734, by rfl⟩ : syracuseStep 1648979 = 2473469) B2473469
theorem B1648995 : Blo 1648023 1648995 := bstep (se 1 (by rfl) ⟨1236746, by rfl⟩ : syracuseStep 1648995 = 2473493) B2473493
theorem B1649011 : Blo 1648023 1649011 := bstep (se 1 (by rfl) ⟨1236758, by rfl⟩ : syracuseStep 1649011 = 2473517) B2473517
theorem B1649027 : Blo 1648023 1649027 := bstep (se 1 (by rfl) ⟨1236770, by rfl⟩ : syracuseStep 1649027 = 2473541) B2473541
theorem B1649043 : Blo 1648023 1649043 := bstep (se 1 (by rfl) ⟨1236782, by rfl⟩ : syracuseStep 1649043 = 2473565) B2473565
theorem B1649059 : Blo 1648023 1649059 := bstep (se 1 (by rfl) ⟨1236794, by rfl⟩ : syracuseStep 1649059 = 2473589) B2473589
theorem B1649075 : Blo 1648023 1649075 := bstep (se 1 (by rfl) ⟨1236806, by rfl⟩ : syracuseStep 1649075 = 2473613) B2473613
theorem B1649091 : Blo 1648023 1649091 := bstep (se 1 (by rfl) ⟨1236818, by rfl⟩ : syracuseStep 1649091 = 2473637) B2473637
theorem B20056517 : Blo 1648023 20056517 := bstep (se 4 (by rfl) ⟨1880298, by rfl⟩ : syracuseStep 20056517 = 3760597) B3760597
theorem B1649107 : Blo 1648023 1649107 := bstep (se 1 (by rfl) ⟨1236830, by rfl⟩ : syracuseStep 1649107 = 2473661) B2473661
theorem B1649123 : Blo 1648023 1649123 := bstep (se 1 (by rfl) ⟨1236842, by rfl⟩ : syracuseStep 1649123 = 2473685) B2473685
theorem B1649139 : Blo 1648023 1649139 := bstep (se 1 (by rfl) ⟨1236854, by rfl⟩ : syracuseStep 1649139 = 2473709) B2473709
theorem B1649155 : Blo 1648023 1649155 := bstep (se 1 (by rfl) ⟨1236866, by rfl⟩ : syracuseStep 1649155 = 2473733) B2473733
theorem B1649171 : Blo 1648023 1649171 := bstep (se 1 (by rfl) ⟨1236878, by rfl⟩ : syracuseStep 1649171 = 2473757) B2473757
theorem B5941795 : Blo 1648023 5941795 := bstep (se 1 (by rfl) ⟨4456346, by rfl⟩ : syracuseStep 5941795 = 8912693) B8912693
theorem B1649187 : Blo 1648023 1649187 := bstep (se 1 (by rfl) ⟨1236890, by rfl⟩ : syracuseStep 1649187 = 2473781) B2473781
theorem B1649203 : Blo 1648023 1649203 := bstep (se 1 (by rfl) ⟨1236902, by rfl⟩ : syracuseStep 1649203 = 2473805) B2473805
theorem B1649219 : Blo 1648023 1649219 := bstep (se 1 (by rfl) ⟨1236914, by rfl⟩ : syracuseStep 1649219 = 2473829) B2473829
theorem B3172945 : Blo 1648023 3172945 := bstep (se 2 (by rfl) ⟨1189854, by rfl⟩ : syracuseStep 3172945 = 2379709) B2379709
theorem B1649235 : Blo 1648023 1649235 := bstep (se 1 (by rfl) ⟨1236926, by rfl⟩ : syracuseStep 1649235 = 2473853) B2473853
theorem B1649251 : Blo 1648023 1649251 := bstep (se 1 (by rfl) ⟨1236938, by rfl⟩ : syracuseStep 1649251 = 2473877) B2473877
theorem B1854067 : Blo 1648023 1854067 := bstep (se 1 (by rfl) ⟨1390550, by rfl⟩ : syracuseStep 1854067 = 2781101) B2781101
theorem B1649267 : Blo 1648023 1649267 := bstep (se 1 (by rfl) ⟨1236950, by rfl⟩ : syracuseStep 1649267 = 2473901) B2473901
theorem B1649283 : Blo 1648023 1649283 := bstep (se 1 (by rfl) ⟨1236962, by rfl⟩ : syracuseStep 1649283 = 2473925) B2473925
theorem B1649299 : Blo 1648023 1649299 := bstep (se 1 (by rfl) ⟨1236974, by rfl⟩ : syracuseStep 1649299 = 2473949) B2473949
theorem B1649315 : Blo 1648023 1649315 := bstep (se 1 (by rfl) ⟨1236986, by rfl⟩ : syracuseStep 1649315 = 2473973) B2473973
theorem B1649331 : Blo 1648023 1649331 := bstep (se 1 (by rfl) ⟨1236998, by rfl⟩ : syracuseStep 1649331 = 2473997) B2473997
theorem B1649347 : Blo 1648023 1649347 := bstep (se 1 (by rfl) ⟨1237010, by rfl⟩ : syracuseStep 1649347 = 2474021) B2474021
theorem B1649363 : Blo 1648023 1649363 := bstep (se 1 (by rfl) ⟨1237022, by rfl⟩ : syracuseStep 1649363 = 2474045) B2474045
theorem B1649379 : Blo 1648023 1649379 := bstep (se 1 (by rfl) ⟨1237034, by rfl⟩ : syracuseStep 1649379 = 2474069) B2474069
theorem B1649395 : Blo 1648023 1649395 := bstep (se 1 (by rfl) ⟨1237046, by rfl⟩ : syracuseStep 1649395 = 2474093) B2474093
theorem B1854211 : Blo 1648023 1854211 := bstep (se 1 (by rfl) ⟨1390658, by rfl⟩ : syracuseStep 1854211 = 2781317) B2781317
theorem B1649411 : Blo 1648023 1649411 := bstep (se 1 (by rfl) ⟨1237058, by rfl⟩ : syracuseStep 1649411 = 2474117) B2474117
theorem B1649427 : Blo 1648023 1649427 := bstep (se 1 (by rfl) ⟨1237070, by rfl⟩ : syracuseStep 1649427 = 2474141) B2474141
theorem B1649443 : Blo 1648023 1649443 := bstep (se 1 (by rfl) ⟨1237082, by rfl⟩ : syracuseStep 1649443 = 2474165) B2474165
theorem B4172593 : Blo 1648023 4172593 := bstep (se 2 (by rfl) ⟨1564722, by rfl⟩ : syracuseStep 4172593 = 3129445) B3129445
theorem B1649459 : Blo 1648023 1649459 := bstep (se 1 (by rfl) ⟨1237094, by rfl⟩ : syracuseStep 1649459 = 2474189) B2474189
theorem B1649475 : Blo 1648023 1649475 := bstep (se 1 (by rfl) ⟨1237106, by rfl⟩ : syracuseStep 1649475 = 2474213) B2474213
theorem B1649491 : Blo 1648023 1649491 := bstep (se 1 (by rfl) ⟨1237118, by rfl⟩ : syracuseStep 1649491 = 2474237) B2474237
theorem B1649507 : Blo 1648023 1649507 := bstep (se 1 (by rfl) ⟨1237130, by rfl⟩ : syracuseStep 1649507 = 2474261) B2474261
theorem B5565293 : Blo 1648023 5565293 := bstep (se 3 (by rfl) ⟨1043492, by rfl⟩ : syracuseStep 5565293 = 2086985) B2086985
theorem B1649523 : Blo 1648023 1649523 := bstep (se 1 (by rfl) ⟨1237142, by rfl⟩ : syracuseStep 1649523 = 2474285) B2474285
theorem B7039885 : Blo 1648023 7039885 := bstep (se 3 (by rfl) ⟨1319978, by rfl⟩ : syracuseStep 7039885 = 2639957) B2639957
theorem B1854355 : Blo 1648023 1854355 := bstep (se 1 (by rfl) ⟨1390766, by rfl⟩ : syracuseStep 1854355 = 2781533) B2781533
theorem B5565347 : Blo 1648023 5565347 := bstep (se 1 (by rfl) ⟨4174010, by rfl⟩ : syracuseStep 5565347 = 8348021) B8348021
theorem B11439053 : Blo 1648023 11439053 := bstep (se 3 (by rfl) ⟨2144822, by rfl⟩ : syracuseStep 11439053 = 4289645) B4289645
theorem B2411473 : Blo 1648023 2411473 := bstep (se 2 (by rfl) ⟨904302, by rfl⟩ : syracuseStep 2411473 = 1808605) B1808605
theorem B5352419 : Blo 1648023 5352419 := bstep (se 1 (by rfl) ⟨4014314, by rfl⟩ : syracuseStep 5352419 = 8028629) B8028629
theorem B6261731 : Blo 1648023 6261731 := bstep (se 1 (by rfl) ⟨4696298, by rfl⟩ : syracuseStep 6261731 = 9392597) B9392597
theorem B6261745 : Blo 1648023 6261745 := bstep (se 2 (by rfl) ⟨2348154, by rfl⟩ : syracuseStep 6261745 = 4696309) B4696309
theorem B1854499 : Blo 1648023 1854499 := bstep (se 1 (by rfl) ⟨1390874, by rfl⟩ : syracuseStep 1854499 = 2781749) B2781749
theorem B9391139 : Blo 1648023 9391139 := bstep (se 1 (by rfl) ⟨7043354, by rfl⟩ : syracuseStep 9391139 = 14086709) B14086709
theorem B4172867 : Blo 1648023 4172867 := bstep (se 1 (by rfl) ⟨3129650, by rfl⟩ : syracuseStep 4172867 = 6259301) B6259301
theorem B5942413 : Blo 1648023 5942413 := bstep (se 3 (by rfl) ⟨1114202, by rfl⟩ : syracuseStep 5942413 = 2228405) B2228405
theorem B2378899 : Blo 1648023 2378899 := bstep (se 1 (by rfl) ⟨1784174, by rfl⟩ : syracuseStep 2378899 = 3568349) B3568349
theorem B5565617 : Blo 1648023 5565617 := bstep (se 2 (by rfl) ⟨2087106, by rfl⟩ : syracuseStep 5565617 = 4174213) B4174213
theorem B1854643 : Blo 1648023 1854643 := bstep (se 1 (by rfl) ⟨1390982, by rfl⟩ : syracuseStep 1854643 = 2781965) B2781965
theorem B4173059 : Blo 1648023 4173059 := bstep (se 1 (by rfl) ⟨3129794, by rfl⟩ : syracuseStep 4173059 = 6259589) B6259589
theorem B1854787 : Blo 1648023 1854787 := bstep (se 1 (by rfl) ⟨1391090, by rfl⟩ : syracuseStep 1854787 = 2782181) B2782181
theorem B12520817 : Blo 1648023 12520817 := bstep (se 2 (by rfl) ⟨4695306, by rfl⟩ : syracuseStep 12520817 = 9390613) B9390613
theorem B5639555 : Blo 1648023 5639555 := bstep (se 1 (by rfl) ⟨4229666, by rfl⟩ : syracuseStep 5639555 = 8459333) B8459333
theorem B1854931 : Blo 1648023 1854931 := bstep (se 1 (by rfl) ⟨1391198, by rfl⟩ : syracuseStep 1854931 = 2782397) B2782397
theorem B38088245 : Blo 1648023 38088245 := bstep (se 5 (by rfl) ⟨1785386, by rfl⟩ : syracuseStep 38088245 = 3570773) B3570773
theorem B1855075 : Blo 1648023 1855075 := bstep (se 1 (by rfl) ⟨1391306, by rfl⟩ : syracuseStep 1855075 = 2782613) B2782613
theorem B10030691 : Blo 1648023 10030691 := bstep (se 1 (by rfl) ⟨7523018, by rfl⟩ : syracuseStep 10030691 = 15046037) B15046037
theorem B4517507 : Blo 1648023 4517507 := bstep (se 1 (by rfl) ⟨3388130, by rfl⟩ : syracuseStep 4517507 = 6776261) B6776261
theorem B2641585 : Blo 1648023 2641585 := bstep (se 2 (by rfl) ⟨990594, by rfl⟩ : syracuseStep 2641585 = 1981189) B1981189
theorem B5566157 : Blo 1648023 5566157 := bstep (se 3 (by rfl) ⟨1043654, by rfl⟩ : syracuseStep 5566157 = 2087309) B2087309
theorem B1855219 : Blo 1648023 1855219 := bstep (se 1 (by rfl) ⟨1391414, by rfl⟩ : syracuseStep 1855219 = 2782829) B2782829
theorem B5566211 : Blo 1648023 5566211 := bstep (se 1 (by rfl) ⟨4174658, by rfl⟩ : syracuseStep 5566211 = 8349317) B8349317
theorem B15249221 : Blo 1648023 15249221 := bstep (se 4 (by rfl) ⟨1429614, by rfl⟩ : syracuseStep 15249221 = 2859229) B2859229
theorem B1855363 : Blo 1648023 1855363 := bstep (se 1 (by rfl) ⟨1391522, by rfl⟩ : syracuseStep 1855363 = 2783045) B2783045
theorem B7040945 : Blo 1648023 7040945 := bstep (se 2 (by rfl) ⟨2640354, by rfl⟩ : syracuseStep 7040945 = 5280709) B5280709
theorem B2781121 : Blo 1648023 2781121 := bstep (se 2 (by rfl) ⟨1042920, by rfl⟩ : syracuseStep 2781121 = 2085841) B2085841
theorem B2781155 : Blo 1648023 2781155 := bstep (se 1 (by rfl) ⟨2085866, by rfl⟩ : syracuseStep 2781155 = 4171733) B4171733
theorem B15044579 : Blo 1648023 15044579 := bstep (se 1 (by rfl) ⟨11283434, by rfl⟩ : syracuseStep 15044579 = 22566869) B22566869
theorem B5566481 : Blo 1648023 5566481 := bstep (se 2 (by rfl) ⟨2087430, by rfl⟩ : syracuseStep 5566481 = 4174861) B4174861
theorem B1855507 : Blo 1648023 1855507 := bstep (se 1 (by rfl) ⟨1391630, by rfl⟩ : syracuseStep 1855507 = 2783261) B2783261
theorem B2781283 : Blo 1648023 2781283 := bstep (se 1 (by rfl) ⟨2085962, by rfl⟩ : syracuseStep 2781283 = 4171925) B4171925
theorem B12693617 : Blo 1648023 12693617 := bstep (se 2 (by rfl) ⟨4760106, by rfl⟩ : syracuseStep 12693617 = 9520213) B9520213
theorem B1855651 : Blo 1648023 1855651 := bstep (se 1 (by rfl) ⟨1391738, by rfl⟩ : syracuseStep 1855651 = 2783477) B2783477
theorem B4174001 : Blo 1648023 4174001 := bstep (se 2 (by rfl) ⟨1565250, by rfl⟩ : syracuseStep 4174001 = 3130501) B3130501
theorem B4174051 : Blo 1648023 4174051 := bstep (se 1 (by rfl) ⟨3130538, by rfl⟩ : syracuseStep 4174051 = 6261077) B6261077
theorem B2781425 : Blo 1648023 2781425 := bstep (se 2 (by rfl) ⟨1043034, by rfl⟩ : syracuseStep 2781425 = 2086069) B2086069
theorem B5640461 : Blo 1648023 5640461 := bstep (se 3 (by rfl) ⟨1057586, by rfl⟩ : syracuseStep 5640461 = 2115173) B2115173
theorem B2781553 : Blo 1648023 2781553 := bstep (se 2 (by rfl) ⟨1043082, by rfl⟩ : syracuseStep 2781553 = 2086165) B2086165
theorem B4174193 : Blo 1648023 4174193 := bstep (se 2 (by rfl) ⟨1565322, by rfl⟩ : syracuseStep 4174193 = 3130645) B3130645
theorem B2781587 : Blo 1648023 2781587 := bstep (se 1 (by rfl) ⟨2086190, by rfl⟩ : syracuseStep 2781587 = 4172381) B4172381
theorem B8343971 : Blo 1648023 8343971 := bstep (se 1 (by rfl) ⟨6257978, by rfl⟩ : syracuseStep 8343971 = 12515957) B12515957
theorem B2781715 : Blo 1648023 2781715 := bstep (se 1 (by rfl) ⟨2086286, by rfl⟩ : syracuseStep 2781715 = 4172573) B4172573
theorem B3961379 : Blo 1648023 3961379 := bstep (se 1 (by rfl) ⟨2971034, by rfl⟩ : syracuseStep 3961379 = 5942069) B5942069
theorem B5567021 : Blo 1648023 5567021 := bstep (se 3 (by rfl) ⟨1043816, by rfl⟩ : syracuseStep 5567021 = 2087633) B2087633
theorem B5567075 : Blo 1648023 5567075 := bstep (se 1 (by rfl) ⟨4175306, by rfl⟩ : syracuseStep 5567075 = 8350613) B8350613
theorem B2781857 : Blo 1648023 2781857 := bstep (se 2 (by rfl) ⟨1043196, by rfl⟩ : syracuseStep 2781857 = 2086393) B2086393
theorem B2347699 : Blo 1648023 2347699 := bstep (se 1 (by rfl) ⟨1760774, by rfl⟩ : syracuseStep 2347699 = 3521549) B3521549
theorem B10703587 : Blo 1648023 10703587 := bstep (se 1 (by rfl) ⟨8027690, by rfl⟩ : syracuseStep 10703587 = 16055381) B16055381
theorem B5640941 : Blo 1648023 5640941 := bstep (se 3 (by rfl) ⟨1057676, by rfl⟩ : syracuseStep 5640941 = 2115353) B2115353
theorem B2781985 : Blo 1648023 2781985 := bstep (se 2 (by rfl) ⟨1043244, by rfl⟩ : syracuseStep 2781985 = 2086489) B2086489
theorem B2782019 : Blo 1648023 2782019 := bstep (se 1 (by rfl) ⟨2086514, by rfl⟩ : syracuseStep 2782019 = 4173029) B4173029
theorem B9393029 : Blo 1648023 9393029 := bstep (se 4 (by rfl) ⟨880596, by rfl⟩ : syracuseStep 9393029 = 1761193) B1761193
theorem B3961763 : Blo 1648023 3961763 := bstep (se 1 (by rfl) ⟨2971322, by rfl⟩ : syracuseStep 3961763 = 5942645) B5942645
theorem B2782147 : Blo 1648023 2782147 := bstep (se 1 (by rfl) ⟨2086610, by rfl⟩ : syracuseStep 2782147 = 4173221) B4173221
theorem B2085907 : Blo 1648023 2085907 := bstep (se 1 (by rfl) ⟨1564430, by rfl⟩ : syracuseStep 2085907 = 3128861) B3128861
theorem B2782289 : Blo 1648023 2782289 := bstep (se 2 (by rfl) ⟨1043358, by rfl⟩ : syracuseStep 2782289 = 2086717) B2086717
theorem B2086003 : Blo 1648023 2086003 := bstep (se 1 (by rfl) ⟨1564502, by rfl⟩ : syracuseStep 2086003 = 3129005) B3129005
theorem B2749601 : Blo 1648023 2749601 := bstep (se 2 (by rfl) ⟨1031100, by rfl⟩ : syracuseStep 2749601 = 2062201) B2062201
theorem B3568835 : Blo 1648023 3568835 := bstep (se 1 (by rfl) ⟨2676626, by rfl⟩ : syracuseStep 3568835 = 5353253) B5353253
theorem B8344781 : Blo 1648023 8344781 := bstep (se 3 (by rfl) ⟨1564646, by rfl⟩ : syracuseStep 8344781 = 3129293) B3129293
theorem B2782417 : Blo 1648023 2782417 := bstep (se 2 (by rfl) ⟨1043406, by rfl⟩ : syracuseStep 2782417 = 2086813) B2086813
theorem B2782451 : Blo 1648023 2782451 := bstep (se 1 (by rfl) ⟨2086838, by rfl⟩ : syracuseStep 2782451 = 4173677) B4173677
theorem B4175185 : Blo 1648023 4175185 := bstep (se 2 (by rfl) ⟨1565694, by rfl⟩ : syracuseStep 4175185 = 3131389) B3131389
theorem B2782579 : Blo 1648023 2782579 := bstep (se 1 (by rfl) ⟨2086934, by rfl⟩ : syracuseStep 2782579 = 4173869) B4173869
theorem B3519875 : Blo 1648023 3519875 := bstep (se 1 (by rfl) ⟨2639906, by rfl⟩ : syracuseStep 3519875 = 5279813) B5279813
theorem B3708305 : Blo 1648023 3708305 := bstep (se 2 (by rfl) ⟨1390614, by rfl⟩ : syracuseStep 3708305 = 2781229) B2781229
theorem B3708323 : Blo 1648023 3708323 := bstep (se 1 (by rfl) ⟨2781242, by rfl⟩ : syracuseStep 3708323 = 5562485) B5562485
theorem B3962321 : Blo 1648023 3962321 := bstep (se 2 (by rfl) ⟨1485870, by rfl⟩ : syracuseStep 3962321 = 2971741) B2971741
theorem B2782721 : Blo 1648023 2782721 := bstep (se 2 (by rfl) ⟨1043520, by rfl⟩ : syracuseStep 2782721 = 2087041) B2087041
theorem B5281325 : Blo 1648023 5281325 := bstep (se 3 (by rfl) ⟨990248, by rfl⟩ : syracuseStep 5281325 = 1980497) B1980497
theorem B2086499 : Blo 1648023 2086499 := bstep (se 1 (by rfl) ⟨1564874, by rfl⟩ : syracuseStep 2086499 = 3129749) B3129749
theorem B2782849 : Blo 1648023 2782849 := bstep (se 2 (by rfl) ⟨1043568, by rfl⟩ : syracuseStep 2782849 = 2087137) B2087137
theorem B10565261 : Blo 1648023 10565261 := bstep (se 3 (by rfl) ⟨1980986, by rfl⟩ : syracuseStep 10565261 = 3961973) B3961973
theorem B2782883 : Blo 1648023 2782883 := bstep (se 1 (by rfl) ⟨2087162, by rfl⟩ : syracuseStep 2782883 = 4174325) B4174325
theorem B3708593 : Blo 1648023 3708593 := bstep (se 2 (by rfl) ⟨1390722, by rfl⟩ : syracuseStep 3708593 = 2781445) B2781445
theorem B3708611 : Blo 1648023 3708611 := bstep (se 1 (by rfl) ⟨2781458, by rfl⟩ : syracuseStep 3708611 = 5562917) B5562917
theorem B2258705 : Blo 1648023 2258705 := bstep (se 2 (by rfl) ⟨847014, by rfl⟩ : syracuseStep 2258705 = 1694029) B1694029
theorem B2258723 : Blo 1648023 2258723 := bstep (se 1 (by rfl) ⟨1694042, by rfl⟩ : syracuseStep 2258723 = 3388085) B3388085
theorem B2783011 : Blo 1648023 2783011 := bstep (se 1 (by rfl) ⟨2087258, by rfl⟩ : syracuseStep 2783011 = 4174517) B4174517
theorem B2783153 : Blo 1648023 2783153 := bstep (se 2 (by rfl) ⟨1043682, by rfl⟩ : syracuseStep 2783153 = 2087365) B2087365
theorem B4405187 : Blo 1648023 4405187 := bstep (se 1 (by rfl) ⟨3303890, by rfl⟩ : syracuseStep 4405187 = 6607781) B6607781
theorem B3962819 : Blo 1648023 3962819 := bstep (se 1 (by rfl) ⟨2972114, by rfl⟩ : syracuseStep 3962819 = 5944229) B5944229
theorem B3708881 : Blo 1648023 3708881 := bstep (se 2 (by rfl) ⟨1390830, by rfl⟩ : syracuseStep 3708881 = 2781661) B2781661
theorem B3708899 : Blo 1648023 3708899 := bstep (se 1 (by rfl) ⟨2781674, by rfl⟩ : syracuseStep 3708899 = 5563349) B5563349
theorem B2783281 : Blo 1648023 2783281 := bstep (se 2 (by rfl) ⟨1043730, by rfl⟩ : syracuseStep 2783281 = 2087461) B2087461
theorem B2783315 : Blo 1648023 2783315 := bstep (se 1 (by rfl) ⟨2087486, by rfl⟩ : syracuseStep 2783315 = 4174973) B4174973
theorem B2472035 : Blo 1648023 2472035 := bstep (se 1 (by rfl) ⟨1854026, by rfl⟩ : syracuseStep 2472035 = 3708053) B3708053
theorem B2472065 : Blo 1648023 2472065 := bstep (se 2 (by rfl) ⟨927024, by rfl⟩ : syracuseStep 2472065 = 1854049) B1854049
theorem B3963011 : Blo 1648023 3963011 := bstep (se 1 (by rfl) ⟨2972258, by rfl⟩ : syracuseStep 3963011 = 5944517) B5944517
theorem B2472083 : Blo 1648023 2472083 := bstep (se 1 (by rfl) ⟨1854062, by rfl⟩ : syracuseStep 2472083 = 3708125) B3708125
theorem B2472113 : Blo 1648023 2472113 := bstep (se 2 (by rfl) ⟨927042, by rfl⟩ : syracuseStep 2472113 = 1854085) B1854085
theorem B2472131 : Blo 1648023 2472131 := bstep (se 1 (by rfl) ⟨1854098, by rfl⟩ : syracuseStep 2472131 = 3708197) B3708197
theorem B3520721 : Blo 1648023 3520721 := bstep (se 2 (by rfl) ⟨1320270, by rfl⟩ : syracuseStep 3520721 = 2640541) B2640541
theorem B2783443 : Blo 1648023 2783443 := bstep (se 1 (by rfl) ⟨2087582, by rfl⟩ : syracuseStep 2783443 = 4175165) B4175165
theorem B2472161 : Blo 1648023 2472161 := bstep (se 2 (by rfl) ⟨927060, by rfl⟩ : syracuseStep 2472161 = 1854121) B1854121
theorem B3709169 : Blo 1648023 3709169 := bstep (se 2 (by rfl) ⟨1390938, by rfl⟩ : syracuseStep 3709169 = 2781877) B2781877
theorem B2472179 : Blo 1648023 2472179 := bstep (se 1 (by rfl) ⟨1854134, by rfl⟩ : syracuseStep 2472179 = 3708269) B3708269
theorem B3709187 : Blo 1648023 3709187 := bstep (se 1 (by rfl) ⟨2781890, by rfl⟩ : syracuseStep 3709187 = 5563781) B5563781
theorem B2472209 : Blo 1648023 2472209 := bstep (se 2 (by rfl) ⟨927078, by rfl⟩ : syracuseStep 2472209 = 1854157) B1854157
theorem B2472227 : Blo 1648023 2472227 := bstep (se 1 (by rfl) ⟨1854170, by rfl⟩ : syracuseStep 2472227 = 3708341) B3708341
theorem B2087203 : Blo 1648023 2087203 := bstep (se 1 (by rfl) ⟨1565402, by rfl⟩ : syracuseStep 2087203 = 3130805) B3130805
theorem B2472257 : Blo 1648023 2472257 := bstep (se 2 (by rfl) ⟨927096, by rfl⟩ : syracuseStep 2472257 = 1854193) B1854193
theorem B13375813 : Blo 1648023 13375813 := bstep (se 4 (by rfl) ⟨1253982, by rfl⟩ : syracuseStep 13375813 = 2507965) B2507965
theorem B2472275 : Blo 1648023 2472275 := bstep (se 1 (by rfl) ⟨1854206, by rfl⟩ : syracuseStep 2472275 = 3708413) B3708413
theorem B2472305 : Blo 1648023 2472305 := bstep (se 2 (by rfl) ⟨927114, by rfl⟩ : syracuseStep 2472305 = 1854229) B1854229
theorem B2472323 : Blo 1648023 2472323 := bstep (se 1 (by rfl) ⟨1854242, by rfl⟩ : syracuseStep 2472323 = 3708485) B3708485
theorem B2087299 : Blo 1648023 2087299 := bstep (se 1 (by rfl) ⟨1565474, by rfl⟩ : syracuseStep 2087299 = 3130949) B3130949
theorem B2472353 : Blo 1648023 2472353 := bstep (se 2 (by rfl) ⟨927132, by rfl⟩ : syracuseStep 2472353 = 1854265) B1854265
theorem B2472371 : Blo 1648023 2472371 := bstep (se 1 (by rfl) ⟨1854278, by rfl⟩ : syracuseStep 2472371 = 3708557) B3708557
theorem B10025413 : Blo 1648023 10025413 := bstep (se 4 (by rfl) ⟨939882, by rfl⟩ : syracuseStep 10025413 = 1879765) B1879765
theorem B2472401 : Blo 1648023 2472401 := bstep (se 2 (by rfl) ⟨927150, by rfl⟩ : syracuseStep 2472401 = 1854301) B1854301
theorem B2472419 : Blo 1648023 2472419 := bstep (se 1 (by rfl) ⟨1854314, by rfl⟩ : syracuseStep 2472419 = 3708629) B3708629
theorem B2857459 : Blo 1648023 2857459 := bstep (se 1 (by rfl) ⟨2143094, by rfl⟩ : syracuseStep 2857459 = 4286189) B4286189
theorem B2472449 : Blo 1648023 2472449 := bstep (se 2 (by rfl) ⟨927168, by rfl⟩ : syracuseStep 2472449 = 1854337) B1854337
theorem B3709457 : Blo 1648023 3709457 := bstep (se 2 (by rfl) ⟨1391046, by rfl⟩ : syracuseStep 3709457 = 2782093) B2782093
theorem B2472467 : Blo 1648023 2472467 := bstep (se 1 (by rfl) ⟨1854350, by rfl⟩ : syracuseStep 2472467 = 3708701) B3708701
theorem B3709475 : Blo 1648023 3709475 := bstep (se 1 (by rfl) ⟨2782106, by rfl⟩ : syracuseStep 3709475 = 5564213) B5564213
theorem B2472497 : Blo 1648023 2472497 := bstep (se 2 (by rfl) ⟨927186, by rfl⟩ : syracuseStep 2472497 = 1854373) B1854373
theorem B2472515 : Blo 1648023 2472515 := bstep (se 1 (by rfl) ⟨1854386, by rfl⟩ : syracuseStep 2472515 = 3708773) B3708773
theorem B2472545 : Blo 1648023 2472545 := bstep (se 2 (by rfl) ⟨927204, by rfl⟩ : syracuseStep 2472545 = 1854409) B1854409
theorem B2472563 : Blo 1648023 2472563 := bstep (se 1 (by rfl) ⟨1854422, by rfl⟩ : syracuseStep 2472563 = 3708845) B3708845
theorem B2472593 : Blo 1648023 2472593 := bstep (se 2 (by rfl) ⟨927222, by rfl⟩ : syracuseStep 2472593 = 1854445) B1854445
theorem B2472611 : Blo 1648023 2472611 := bstep (se 1 (by rfl) ⟨1854458, by rfl⟩ : syracuseStep 2472611 = 3708917) B3708917
theorem B2472641 : Blo 1648023 2472641 := bstep (se 2 (by rfl) ⟨927240, by rfl⟩ : syracuseStep 2472641 = 1854481) B1854481
theorem B6257357 : Blo 1648023 6257357 := bstep (se 3 (by rfl) ⟨1173254, by rfl⟩ : syracuseStep 6257357 = 2346509) B2346509
theorem B2472659 : Blo 1648023 2472659 := bstep (se 1 (by rfl) ⟨1854494, by rfl⟩ : syracuseStep 2472659 = 3708989) B3708989
theorem B2472689 : Blo 1648023 2472689 := bstep (se 2 (by rfl) ⟨927258, by rfl⟩ : syracuseStep 2472689 = 1854517) B1854517
theorem B2472707 : Blo 1648023 2472707 := bstep (se 1 (by rfl) ⟨1854530, by rfl⟩ : syracuseStep 2472707 = 3709061) B3709061
theorem B9386765 : Blo 1648023 9386765 := bstep (se 3 (by rfl) ⟨1760018, by rfl⟩ : syracuseStep 9386765 = 3520037) B3520037
theorem B2472737 : Blo 1648023 2472737 := bstep (se 2 (by rfl) ⟨927276, by rfl⟩ : syracuseStep 2472737 = 1854553) B1854553
theorem B3709745 : Blo 1648023 3709745 := bstep (se 2 (by rfl) ⟨1391154, by rfl⟩ : syracuseStep 3709745 = 2782309) B2782309
theorem B2472755 : Blo 1648023 2472755 := bstep (se 1 (by rfl) ⟨1854566, by rfl⟩ : syracuseStep 2472755 = 3709133) B3709133
theorem B3709763 : Blo 1648023 3709763 := bstep (se 1 (by rfl) ⟨2782322, by rfl⟩ : syracuseStep 3709763 = 5564645) B5564645
theorem B7043917 : Blo 1648023 7043917 := bstep (se 3 (by rfl) ⟨1320734, by rfl⟩ : syracuseStep 7043917 = 2641469) B2641469
theorem B2472785 : Blo 1648023 2472785 := bstep (se 2 (by rfl) ⟨927294, by rfl⟩ : syracuseStep 2472785 = 1854589) B1854589
theorem B2472803 : Blo 1648023 2472803 := bstep (se 1 (by rfl) ⟨1854602, by rfl⟩ : syracuseStep 2472803 = 3709205) B3709205
theorem B2472833 : Blo 1648023 2472833 := bstep (se 2 (by rfl) ⟨927312, by rfl⟩ : syracuseStep 2472833 = 1854625) B1854625
theorem B2472851 : Blo 1648023 2472851 := bstep (se 1 (by rfl) ⟨1854638, by rfl⟩ : syracuseStep 2472851 = 3709277) B3709277
theorem B2472881 : Blo 1648023 2472881 := bstep (se 2 (by rfl) ⟨927330, by rfl⟩ : syracuseStep 2472881 = 1854661) B1854661
theorem B2472899 : Blo 1648023 2472899 := bstep (se 1 (by rfl) ⟨1854674, by rfl⟩ : syracuseStep 2472899 = 3709349) B3709349
theorem B2472929 : Blo 1648023 2472929 := bstep (se 2 (by rfl) ⟨927348, by rfl⟩ : syracuseStep 2472929 = 1854697) B1854697
theorem B4455395 : Blo 1648023 4455395 := bstep (se 1 (by rfl) ⟨3341546, by rfl⟩ : syracuseStep 4455395 = 6683093) B6683093
theorem B2472947 : Blo 1648023 2472947 := bstep (se 1 (by rfl) ⟨1854710, by rfl⟩ : syracuseStep 2472947 = 3709421) B3709421
theorem B2472977 : Blo 1648023 2472977 := bstep (se 2 (by rfl) ⟨927366, by rfl⟩ : syracuseStep 2472977 = 1854733) B1854733
theorem B2472995 : Blo 1648023 2472995 := bstep (se 1 (by rfl) ⟨1854746, by rfl⟩ : syracuseStep 2472995 = 3709493) B3709493
theorem B2473025 : Blo 1648023 2473025 := bstep (se 2 (by rfl) ⟨927384, by rfl⟩ : syracuseStep 2473025 = 1854769) B1854769
theorem B3710033 : Blo 1648023 3710033 := bstep (se 2 (by rfl) ⟨1391262, by rfl⟩ : syracuseStep 3710033 = 2782525) B2782525
theorem B1760339 : Blo 1648023 1760339 := bstep (se 1 (by rfl) ⟨1320254, by rfl⟩ : syracuseStep 1760339 = 2640509) B2640509
theorem B2473043 : Blo 1648023 2473043 := bstep (se 1 (by rfl) ⟨1854782, by rfl⟩ : syracuseStep 2473043 = 3709565) B3709565
theorem B3710051 : Blo 1648023 3710051 := bstep (se 1 (by rfl) ⟨2782538, by rfl⟩ : syracuseStep 3710051 = 5565077) B5565077
theorem B2473073 : Blo 1648023 2473073 := bstep (se 2 (by rfl) ⟨927402, by rfl⟩ : syracuseStep 2473073 = 1854805) B1854805
theorem B2473091 : Blo 1648023 2473091 := bstep (se 1 (by rfl) ⟨1854818, by rfl⟩ : syracuseStep 2473091 = 3709637) B3709637
theorem B5012621 : Blo 1648023 5012621 := bstep (se 3 (by rfl) ⟨939866, by rfl⟩ : syracuseStep 5012621 = 1879733) B1879733
theorem B2473121 : Blo 1648023 2473121 := bstep (se 2 (by rfl) ⟨927420, by rfl⟩ : syracuseStep 2473121 = 1854841) B1854841
theorem B7044259 : Blo 1648023 7044259 := bstep (se 1 (by rfl) ⟨5283194, by rfl⟩ : syracuseStep 7044259 = 10566389) B10566389
theorem B2473139 : Blo 1648023 2473139 := bstep (se 1 (by rfl) ⟨1854854, by rfl⟩ : syracuseStep 2473139 = 3709709) B3709709
theorem B18783413 : Blo 1648023 18783413 := bstep (se 5 (by rfl) ⟨880472, by rfl⟩ : syracuseStep 18783413 = 1760945) B1760945
theorem B14277829 : Blo 1648023 14277829 := bstep (se 4 (by rfl) ⟨1338546, by rfl⟩ : syracuseStep 14277829 = 2677093) B2677093
theorem B2473169 : Blo 1648023 2473169 := bstep (se 2 (by rfl) ⟨927438, by rfl⟩ : syracuseStep 2473169 = 1854877) B1854877
theorem B2473187 : Blo 1648023 2473187 := bstep (se 1 (by rfl) ⟨1854890, by rfl⟩ : syracuseStep 2473187 = 3709781) B3709781
theorem B2473217 : Blo 1648023 2473217 := bstep (se 2 (by rfl) ⟨927456, by rfl⟩ : syracuseStep 2473217 = 1854913) B1854913
theorem B2473235 : Blo 1648023 2473235 := bstep (se 1 (by rfl) ⟨1854926, by rfl⟩ : syracuseStep 2473235 = 3709853) B3709853
theorem B2473265 : Blo 1648023 2473265 := bstep (se 2 (by rfl) ⟨927474, by rfl⟩ : syracuseStep 2473265 = 1854949) B1854949
theorem B2473283 : Blo 1648023 2473283 := bstep (se 1 (by rfl) ⟨1854962, by rfl⟩ : syracuseStep 2473283 = 3709925) B3709925
theorem B2473313 : Blo 1648023 2473313 := bstep (se 2 (by rfl) ⟨927492, by rfl⟩ : syracuseStep 2473313 = 1854985) B1854985
theorem B3710321 : Blo 1648023 3710321 := bstep (se 2 (by rfl) ⟨1391370, by rfl⟩ : syracuseStep 3710321 = 2782741) B2782741
theorem B2473331 : Blo 1648023 2473331 := bstep (se 1 (by rfl) ⟨1854998, by rfl⟩ : syracuseStep 2473331 = 3709997) B3709997
theorem B3710339 : Blo 1648023 3710339 := bstep (se 1 (by rfl) ⟨2782754, by rfl⟩ : syracuseStep 3710339 = 5565509) B5565509
theorem B32128397 : Blo 1648023 32128397 := bstep (se 3 (by rfl) ⟨6024074, by rfl⟩ : syracuseStep 32128397 = 12048149) B12048149
theorem B4693393 : Blo 1648023 4693393 := bstep (se 2 (by rfl) ⟨1760022, by rfl⟩ : syracuseStep 4693393 = 3520045) B3520045
theorem B2473361 : Blo 1648023 2473361 := bstep (se 2 (by rfl) ⟨927510, by rfl⟩ : syracuseStep 2473361 = 1855021) B1855021
theorem B2473379 : Blo 1648023 2473379 := bstep (se 1 (by rfl) ⟨1855034, by rfl⟩ : syracuseStep 2473379 = 3710069) B3710069
theorem B2473409 : Blo 1648023 2473409 := bstep (se 2 (by rfl) ⟨927528, by rfl⟩ : syracuseStep 2473409 = 1855057) B1855057
theorem B2473427 : Blo 1648023 2473427 := bstep (se 1 (by rfl) ⟨1855070, by rfl⟩ : syracuseStep 2473427 = 3710141) B3710141
theorem B6258161 : Blo 1648023 6258161 := bstep (se 2 (by rfl) ⟨2346810, by rfl⟩ : syracuseStep 6258161 = 4693621) B4693621
theorem B2473457 : Blo 1648023 2473457 := bstep (se 2 (by rfl) ⟨927546, by rfl⟩ : syracuseStep 2473457 = 1855093) B1855093
theorem B2473475 : Blo 1648023 2473475 := bstep (se 1 (by rfl) ⟨1855106, by rfl⟩ : syracuseStep 2473475 = 3710213) B3710213
theorem B2473505 : Blo 1648023 2473505 := bstep (se 2 (by rfl) ⟨927564, by rfl⟩ : syracuseStep 2473505 = 1855129) B1855129
theorem B2473523 : Blo 1648023 2473523 := bstep (se 1 (by rfl) ⟨1855142, by rfl⟩ : syracuseStep 2473523 = 3710285) B3710285
theorem B2473553 : Blo 1648023 2473553 := bstep (se 2 (by rfl) ⟨927582, by rfl⟩ : syracuseStep 2473553 = 1855165) B1855165
theorem B2473571 : Blo 1648023 2473571 := bstep (se 1 (by rfl) ⟨1855178, by rfl⟩ : syracuseStep 2473571 = 3710357) B3710357
theorem B2473601 : Blo 1648023 2473601 := bstep (se 2 (by rfl) ⟨927600, by rfl⟩ : syracuseStep 2473601 = 1855201) B1855201
theorem B3710609 : Blo 1648023 3710609 := bstep (se 2 (by rfl) ⟨1391478, by rfl⟩ : syracuseStep 3710609 = 2782957) B2782957
theorem B2473619 : Blo 1648023 2473619 := bstep (se 1 (by rfl) ⟨1855214, by rfl⟩ : syracuseStep 2473619 = 3710429) B3710429
theorem B3710627 : Blo 1648023 3710627 := bstep (se 1 (by rfl) ⟨2782970, by rfl⟩ : syracuseStep 3710627 = 5565941) B5565941
theorem B9387697 : Blo 1648023 9387697 := bstep (se 2 (by rfl) ⟨3520386, by rfl⟩ : syracuseStep 9387697 = 7040773) B7040773
theorem B2473649 : Blo 1648023 2473649 := bstep (se 2 (by rfl) ⟨927618, by rfl⟩ : syracuseStep 2473649 = 1855237) B1855237
theorem B2473667 : Blo 1648023 2473667 := bstep (se 1 (by rfl) ⟨1855250, by rfl⟩ : syracuseStep 2473667 = 3710501) B3710501
theorem B2473697 : Blo 1648023 2473697 := bstep (se 2 (by rfl) ⟨927636, by rfl⟩ : syracuseStep 2473697 = 1855273) B1855273
theorem B2473715 : Blo 1648023 2473715 := bstep (se 1 (by rfl) ⟨1855286, by rfl⟩ : syracuseStep 2473715 = 3710573) B3710573
theorem B2473745 : Blo 1648023 2473745 := bstep (se 2 (by rfl) ⟨927654, by rfl⟩ : syracuseStep 2473745 = 1855309) B1855309
theorem B2473763 : Blo 1648023 2473763 := bstep (se 1 (by rfl) ⟨1855322, by rfl⟩ : syracuseStep 2473763 = 3710645) B3710645
theorem B5562161 : Blo 1648023 5562161 := bstep (se 2 (by rfl) ⟨2085810, by rfl⟩ : syracuseStep 5562161 = 4171621) B4171621
theorem B2473793 : Blo 1648023 2473793 := bstep (se 2 (by rfl) ⟨927672, by rfl⟩ : syracuseStep 2473793 = 1855345) B1855345
theorem B10567493 : Blo 1648023 10567493 := bstep (se 4 (by rfl) ⟨990702, by rfl⟩ : syracuseStep 10567493 = 1981405) B1981405
theorem B2473811 : Blo 1648023 2473811 := bstep (se 1 (by rfl) ⟨1855358, by rfl⟩ : syracuseStep 2473811 = 3710717) B3710717
theorem B3129187 : Blo 1648023 3129187 := bstep (se 1 (by rfl) ⟨2346890, by rfl⟩ : syracuseStep 3129187 = 4693781) B4693781
theorem B3522403 : Blo 1648023 3522403 := bstep (se 1 (by rfl) ⟨2641802, by rfl⟩ : syracuseStep 3522403 = 5283605) B5283605
theorem B2473841 : Blo 1648023 2473841 := bstep (se 2 (by rfl) ⟨927690, by rfl⟩ : syracuseStep 2473841 = 1855381) B1855381
theorem B2473859 : Blo 1648023 2473859 := bstep (se 1 (by rfl) ⟨1855394, by rfl⟩ : syracuseStep 2473859 = 3710789) B3710789
theorem B2473889 : Blo 1648023 2473889 := bstep (se 2 (by rfl) ⟨927708, by rfl⟩ : syracuseStep 2473889 = 1855417) B1855417
theorem B3760049 : Blo 1648023 3760049 := bstep (se 2 (by rfl) ⟨1410018, by rfl⟩ : syracuseStep 3760049 = 2820037) B2820037
theorem B3710897 : Blo 1648023 3710897 := bstep (se 2 (by rfl) ⟨1391586, by rfl⟩ : syracuseStep 3710897 = 2783173) B2783173
theorem B2473907 : Blo 1648023 2473907 := bstep (se 1 (by rfl) ⟨1855430, by rfl⟩ : syracuseStep 2473907 = 3710861) B3710861
theorem B3710915 : Blo 1648023 3710915 := bstep (se 1 (by rfl) ⟨2783186, by rfl⟩ : syracuseStep 3710915 = 5566373) B5566373
theorem B2473937 : Blo 1648023 2473937 := bstep (se 2 (by rfl) ⟨927726, by rfl⟩ : syracuseStep 2473937 = 1855453) B1855453
theorem B2473955 : Blo 1648023 2473955 := bstep (se 1 (by rfl) ⟨1855466, by rfl⟩ : syracuseStep 2473955 = 3710933) B3710933
theorem B7626737 : Blo 1648023 7626737 := bstep (se 2 (by rfl) ⟨2860026, by rfl⟩ : syracuseStep 7626737 = 5720053) B5720053
theorem B3710987 : Blo 1648023 3710987 := bstep (se 1 (by rfl) ⟨2783240, by rfl⟩ : syracuseStep 3710987 = 5566481) B5566481
theorem B2474009 : Blo 1648023 2474009 := bstep (se 2 (by rfl) ⟨927753, by rfl⟩ : syracuseStep 2474009 = 1855507) B1855507
theorem B3711041 : Blo 1648023 3711041 := bstep (se 2 (by rfl) ⟨1391640, by rfl⟩ : syracuseStep 3711041 = 2783281) B2783281
theorem B8462411 : Blo 1648023 8462411 := bstep (se 1 (by rfl) ⟨6346808, by rfl⟩ : syracuseStep 8462411 = 12693617) B12693617
theorem B2474123 : Blo 1648023 2474123 := bstep (se 1 (by rfl) ⟨1855592, by rfl⟩ : syracuseStep 2474123 = 3711185) B3711185
theorem B2474135 : Blo 1648023 2474135 := bstep (se 1 (by rfl) ⟨1855601, by rfl⟩ : syracuseStep 2474135 = 3711203) B3711203
theorem B3760307 : Blo 1648023 3760307 := bstep (se 1 (by rfl) ⟨2820230, by rfl⟩ : syracuseStep 3760307 = 5640461) B5640461
theorem B2474201 : Blo 1648023 2474201 := bstep (se 2 (by rfl) ⟨927825, by rfl⟩ : syracuseStep 2474201 = 1855651) B1855651
theorem B4694237 : Blo 1648023 4694237 := bstep (se 3 (by rfl) ⟨880169, by rfl⟩ : syracuseStep 4694237 = 1760339) B1760339
theorem B5562647 : Blo 1648023 5562647 := bstep (se 1 (by rfl) ⟨4171985, by rfl⟩ : syracuseStep 5562647 = 8343971) B8343971
theorem B3711257 : Blo 1648023 3711257 := bstep (se 2 (by rfl) ⟨1391721, by rfl⟩ : syracuseStep 3711257 = 2783443) B2783443
theorem B10568029 : Blo 1648023 10568029 := bstep (se 3 (by rfl) ⟨1981505, by rfl⟩ : syracuseStep 10568029 = 3963011) B3963011
theorem B3711347 : Blo 1648023 3711347 := bstep (se 1 (by rfl) ⟨2783510, by rfl⟩ : syracuseStep 3711347 = 5567021) B5567021
theorem B3711383 : Blo 1648023 3711383 := bstep (se 1 (by rfl) ⟨2783537, by rfl⟩ : syracuseStep 3711383 = 5567075) B5567075
theorem B17834417 : Blo 1648023 17834417 := bstep (se 2 (by rfl) ⟨6687906, by rfl⟩ : syracuseStep 17834417 = 13375813) B13375813
theorem B3129779 : Blo 1648023 3129779 := bstep (se 1 (by rfl) ⟨2347334, by rfl⟩ : syracuseStep 3129779 = 4694669) B4694669
theorem B3760627 : Blo 1648023 3760627 := bstep (se 1 (by rfl) ⟨2820470, by rfl⟩ : syracuseStep 3760627 = 5640941) B5640941
theorem B3129931 : Blo 1648023 3129931 := bstep (se 1 (by rfl) ⟨2347448, by rfl⟩ : syracuseStep 3129931 = 4694897) B4694897
theorem B3809945 : Blo 1648023 3809945 := bstep (se 2 (by rfl) ⟨1428729, by rfl⟩ : syracuseStep 3809945 = 2857459) B2857459
theorem B7922393 : Blo 1648023 7922393 := bstep (se 2 (by rfl) ⟨2970897, by rfl⟩ : syracuseStep 7922393 = 5941795) B5941795
theorem B5563187 : Blo 1648023 5563187 := bstep (se 1 (by rfl) ⟨4172390, by rfl⟩ : syracuseStep 5563187 = 8344781) B8344781
theorem B14091083 : Blo 1648023 14091083 := bstep (se 1 (by rfl) ⟨10568312, by rfl⟩ : syracuseStep 14091083 = 21136625) B21136625
theorem B6685571 : Blo 1648023 6685571 := bstep (se 1 (by rfl) ⟨5014178, by rfl⟩ : syracuseStep 6685571 = 10028357) B10028357
theorem B3130265 : Blo 1648023 3130265 := bstep (se 2 (by rfl) ⟨1173849, by rfl⟩ : syracuseStep 3130265 = 2347699) B2347699
theorem B2507735 : Blo 1648023 2507735 := bstep (se 1 (by rfl) ⟨1880801, by rfl⟩ : syracuseStep 2507735 = 3761603) B3761603
theorem B14271449 : Blo 1648023 14271449 := bstep (se 2 (by rfl) ⟨5351793, by rfl⟩ : syracuseStep 14271449 = 10703587) B10703587
theorem B5563457 : Blo 1648023 5563457 := bstep (se 2 (by rfl) ⟨2086296, by rfl⟩ : syracuseStep 5563457 = 4172593) B4172593
theorem B6259787 : Blo 1648023 6259787 := bstep (se 1 (by rfl) ⟨4694840, by rfl⟩ : syracuseStep 6259787 = 9389681) B9389681
theorem B2507863 : Blo 1648023 2507863 := bstep (se 1 (by rfl) ⟨1880897, by rfl⟩ : syracuseStep 2507863 = 3761795) B3761795
theorem B6259801 : Blo 1648023 6259801 := bstep (se 2 (by rfl) ⟨2347425, by rfl⟩ : syracuseStep 6259801 = 4694851) B4694851
theorem B8348993 : Blo 1648023 8348993 := bstep (se 2 (by rfl) ⟨3130872, by rfl⟩ : syracuseStep 8348993 = 6261745) B6261745
theorem B1648023 : Blo 1648023 1648023 := bstep (se 1 (by rfl) ⟨1236017, by rfl⟩ : syracuseStep 1648023 = 2472035) B2472035
theorem B1648043 : Blo 1648023 1648043 := bstep (se 1 (by rfl) ⟨1236032, by rfl⟩ : syracuseStep 1648043 = 2472065) B2472065
theorem B1648055 : Blo 1648023 1648055 := bstep (se 1 (by rfl) ⟨1236041, by rfl⟩ : syracuseStep 1648055 = 2472083) B2472083
theorem B1648075 : Blo 1648023 1648075 := bstep (se 1 (by rfl) ⟨1236056, by rfl⟩ : syracuseStep 1648075 = 2472113) B2472113
theorem B1648087 : Blo 1648023 1648087 := bstep (se 1 (by rfl) ⟨1236065, by rfl⟩ : syracuseStep 1648087 = 2472131) B2472131
theorem B12518873 : Blo 1648023 12518873 := bstep (se 2 (by rfl) ⟨4694577, by rfl⟩ : syracuseStep 12518873 = 9389155) B9389155
theorem B1648107 : Blo 1648023 1648107 := bstep (se 1 (by rfl) ⟨1236080, by rfl⟩ : syracuseStep 1648107 = 2472161) B2472161
theorem B1648119 : Blo 1648023 1648119 := bstep (se 1 (by rfl) ⟨1236089, by rfl⟩ : syracuseStep 1648119 = 2472179) B2472179
theorem B1648139 : Blo 1648023 1648139 := bstep (se 1 (by rfl) ⟨1236104, by rfl⟩ : syracuseStep 1648139 = 2472209) B2472209
theorem B7923217 : Blo 1648023 7923217 := bstep (se 2 (by rfl) ⟨2971206, by rfl⟩ : syracuseStep 7923217 = 5942413) B5942413
theorem B34309649 : Blo 1648023 34309649 := bstep (se 2 (by rfl) ⟨12866118, by rfl⟩ : syracuseStep 34309649 = 25732237) B25732237
theorem B1648151 : Blo 1648023 1648151 := bstep (se 1 (by rfl) ⟨1236113, by rfl⟩ : syracuseStep 1648151 = 2472227) B2472227
theorem B3130903 : Blo 1648023 3130903 := bstep (se 1 (by rfl) ⟨2348177, by rfl⟩ : syracuseStep 3130903 = 4696355) B4696355
theorem B1648171 : Blo 1648023 1648171 := bstep (se 1 (by rfl) ⟨1236128, by rfl⟩ : syracuseStep 1648171 = 2472257) B2472257
theorem B1648183 : Blo 1648023 1648183 := bstep (se 1 (by rfl) ⟨1236137, by rfl⟩ : syracuseStep 1648183 = 2472275) B2472275
theorem B1648203 : Blo 1648023 1648203 := bstep (se 1 (by rfl) ⟨1236152, by rfl⟩ : syracuseStep 1648203 = 2472305) B2472305
theorem B1648215 : Blo 1648023 1648215 := bstep (se 1 (by rfl) ⟨1236161, by rfl⟩ : syracuseStep 1648215 = 2472323) B2472323
theorem B5563997 : Blo 1648023 5563997 := bstep (se 3 (by rfl) ⟨1043249, by rfl⟩ : syracuseStep 5563997 = 2086499) B2086499
theorem B1648235 : Blo 1648023 1648235 := bstep (se 1 (by rfl) ⟨1236176, by rfl⟩ : syracuseStep 1648235 = 2472353) B2472353
theorem B1648247 : Blo 1648023 1648247 := bstep (se 1 (by rfl) ⟨1236185, by rfl⟩ : syracuseStep 1648247 = 2472371) B2472371
theorem B13371011 : Blo 1648023 13371011 := bstep (se 1 (by rfl) ⟨10028258, by rfl⟩ : syracuseStep 13371011 = 20056517) B20056517
theorem B1648267 : Blo 1648023 1648267 := bstep (se 1 (by rfl) ⟨1236200, by rfl⟩ : syracuseStep 1648267 = 2472401) B2472401
theorem B1648279 : Blo 1648023 1648279 := bstep (se 1 (by rfl) ⟨1236209, by rfl⟩ : syracuseStep 1648279 = 2472419) B2472419
theorem B1648299 : Blo 1648023 1648299 := bstep (se 1 (by rfl) ⟨1236224, by rfl⟩ : syracuseStep 1648299 = 2472449) B2472449
theorem B1648311 : Blo 1648023 1648311 := bstep (se 1 (by rfl) ⟨1236233, by rfl⟩ : syracuseStep 1648311 = 2472467) B2472467
theorem B1648331 : Blo 1648023 1648331 := bstep (se 1 (by rfl) ⟨1236248, by rfl⟩ : syracuseStep 1648331 = 2472497) B2472497
theorem B1648343 : Blo 1648023 1648343 := bstep (se 1 (by rfl) ⟨1236257, by rfl⟩ : syracuseStep 1648343 = 2472515) B2472515
theorem B1648363 : Blo 1648023 1648363 := bstep (se 1 (by rfl) ⟨1236272, by rfl⟩ : syracuseStep 1648363 = 2472545) B2472545
theorem B1648375 : Blo 1648023 1648375 := bstep (se 1 (by rfl) ⟨1236281, by rfl⟩ : syracuseStep 1648375 = 2472563) B2472563
theorem B1648395 : Blo 1648023 1648395 := bstep (se 1 (by rfl) ⟨1236296, by rfl⟩ : syracuseStep 1648395 = 2472593) B2472593
theorem B1648407 : Blo 1648023 1648407 := bstep (se 1 (by rfl) ⟨1236305, by rfl⟩ : syracuseStep 1648407 = 2472611) B2472611
theorem B1648427 : Blo 1648023 1648427 := bstep (se 1 (by rfl) ⟨1236320, by rfl⟩ : syracuseStep 1648427 = 2472641) B2472641
theorem B4171571 : Blo 1648023 4171571 := bstep (se 1 (by rfl) ⟨3128678, by rfl⟩ : syracuseStep 4171571 = 6257357) B6257357
theorem B1648439 : Blo 1648023 1648439 := bstep (se 1 (by rfl) ⟨1236329, by rfl⟩ : syracuseStep 1648439 = 2472659) B2472659
theorem B1648459 : Blo 1648023 1648459 := bstep (se 1 (by rfl) ⟨1236344, by rfl⟩ : syracuseStep 1648459 = 2472689) B2472689
theorem B1648471 : Blo 1648023 1648471 := bstep (se 1 (by rfl) ⟨1236353, by rfl⟩ : syracuseStep 1648471 = 2472707) B2472707
theorem B1648491 : Blo 1648023 1648491 := bstep (se 1 (by rfl) ⟨1236368, by rfl⟩ : syracuseStep 1648491 = 2472737) B2472737
theorem B1648503 : Blo 1648023 1648503 := bstep (se 1 (by rfl) ⟨1236377, by rfl⟩ : syracuseStep 1648503 = 2472755) B2472755
theorem B1648523 : Blo 1648023 1648523 := bstep (se 1 (by rfl) ⟨1236392, by rfl⟩ : syracuseStep 1648523 = 2472785) B2472785
theorem B1648535 : Blo 1648023 1648535 := bstep (se 1 (by rfl) ⟨1236401, by rfl⟩ : syracuseStep 1648535 = 2472803) B2472803
theorem B1648555 : Blo 1648023 1648555 := bstep (se 1 (by rfl) ⟨1236416, by rfl⟩ : syracuseStep 1648555 = 2472833) B2472833
theorem B1648567 : Blo 1648023 1648567 := bstep (se 1 (by rfl) ⟨1236425, by rfl⟩ : syracuseStep 1648567 = 2472851) B2472851
theorem B1648587 : Blo 1648023 1648587 := bstep (se 1 (by rfl) ⟨1236440, by rfl⟩ : syracuseStep 1648587 = 2472881) B2472881
theorem B1648599 : Blo 1648023 1648599 := bstep (se 1 (by rfl) ⟨1236449, by rfl⟩ : syracuseStep 1648599 = 2472899) B2472899
theorem B1648619 : Blo 1648023 1648619 := bstep (se 1 (by rfl) ⟨1236464, by rfl⟩ : syracuseStep 1648619 = 2472929) B2472929
theorem B1648631 : Blo 1648023 1648631 := bstep (se 1 (by rfl) ⟨1236473, by rfl⟩ : syracuseStep 1648631 = 2472947) B2472947
theorem B1648651 : Blo 1648023 1648651 := bstep (se 1 (by rfl) ⟨1236488, by rfl⟩ : syracuseStep 1648651 = 2472977) B2472977
theorem B1648663 : Blo 1648023 1648663 := bstep (se 1 (by rfl) ⟨1236497, by rfl⟩ : syracuseStep 1648663 = 2472995) B2472995
theorem B6260759 : Blo 1648023 6260759 := bstep (se 1 (by rfl) ⟨4695569, by rfl⟩ : syracuseStep 6260759 = 9391139) B9391139
theorem B1648683 : Blo 1648023 1648683 := bstep (se 1 (by rfl) ⟨1236512, by rfl⟩ : syracuseStep 1648683 = 2473025) B2473025
theorem B6023213 : Blo 1648023 6023213 := bstep (se 3 (by rfl) ⟨1129352, by rfl⟩ : syracuseStep 6023213 = 2258705) B2258705
theorem B1648695 : Blo 1648023 1648695 := bstep (se 1 (by rfl) ⟨1236521, by rfl⟩ : syracuseStep 1648695 = 2473043) B2473043
theorem B1648715 : Blo 1648023 1648715 := bstep (se 1 (by rfl) ⟨1236536, by rfl⟩ : syracuseStep 1648715 = 2473073) B2473073
theorem B1648727 : Blo 1648023 1648727 := bstep (se 1 (by rfl) ⟨1236545, by rfl⟩ : syracuseStep 1648727 = 2473091) B2473091
theorem B6023261 : Blo 1648023 6023261 := bstep (se 3 (by rfl) ⟨1129361, by rfl⟩ : syracuseStep 6023261 = 2258723) B2258723
theorem B1648747 : Blo 1648023 1648747 := bstep (se 1 (by rfl) ⟨1236560, by rfl⟩ : syracuseStep 1648747 = 2473121) B2473121
theorem B1648759 : Blo 1648023 1648759 := bstep (se 1 (by rfl) ⟨1236569, by rfl⟩ : syracuseStep 1648759 = 2473139) B2473139
theorem B1648779 : Blo 1648023 1648779 := bstep (se 1 (by rfl) ⟨1236584, by rfl⟩ : syracuseStep 1648779 = 2473169) B2473169
theorem B1648791 : Blo 1648023 1648791 := bstep (se 1 (by rfl) ⟨1236593, by rfl⟩ : syracuseStep 1648791 = 2473187) B2473187
theorem B1648811 : Blo 1648023 1648811 := bstep (se 1 (by rfl) ⟨1236608, by rfl⟩ : syracuseStep 1648811 = 2473217) B2473217
theorem B1648823 : Blo 1648023 1648823 := bstep (se 1 (by rfl) ⟨1236617, by rfl⟩ : syracuseStep 1648823 = 2473235) B2473235
theorem B1648843 : Blo 1648023 1648843 := bstep (se 1 (by rfl) ⟨1236632, by rfl⟩ : syracuseStep 1648843 = 2473265) B2473265
theorem B1648855 : Blo 1648023 1648855 := bstep (se 1 (by rfl) ⟨1236641, by rfl⟩ : syracuseStep 1648855 = 2473283) B2473283
theorem B1648875 : Blo 1648023 1648875 := bstep (se 1 (by rfl) ⟨1236656, by rfl⟩ : syracuseStep 1648875 = 2473313) B2473313
theorem B1648887 : Blo 1648023 1648887 := bstep (se 1 (by rfl) ⟨1236665, by rfl⟩ : syracuseStep 1648887 = 2473331) B2473331
theorem B1648907 : Blo 1648023 1648907 := bstep (se 1 (by rfl) ⟨1236680, by rfl⟩ : syracuseStep 1648907 = 2473361) B2473361
theorem B1648919 : Blo 1648023 1648919 := bstep (se 1 (by rfl) ⟨1236689, by rfl⟩ : syracuseStep 1648919 = 2473379) B2473379
theorem B1648939 : Blo 1648023 1648939 := bstep (se 1 (by rfl) ⟨1236704, by rfl⟩ : syracuseStep 1648939 = 2473409) B2473409
theorem B1648951 : Blo 1648023 1648951 := bstep (se 1 (by rfl) ⟨1236713, by rfl⟩ : syracuseStep 1648951 = 2473427) B2473427
theorem B4172107 : Blo 1648023 4172107 := bstep (se 1 (by rfl) ⟨3129080, by rfl⟩ : syracuseStep 4172107 = 6258161) B6258161
theorem B1648971 : Blo 1648023 1648971 := bstep (se 1 (by rfl) ⟨1236728, by rfl⟩ : syracuseStep 1648971 = 2473457) B2473457
theorem B1648983 : Blo 1648023 1648983 := bstep (se 1 (by rfl) ⟨1236737, by rfl⟩ : syracuseStep 1648983 = 2473475) B2473475
theorem B1649003 : Blo 1648023 1649003 := bstep (se 1 (by rfl) ⟨1236752, by rfl⟩ : syracuseStep 1649003 = 2473505) B2473505
theorem B1649015 : Blo 1648023 1649015 := bstep (se 1 (by rfl) ⟨1236761, by rfl⟩ : syracuseStep 1649015 = 2473523) B2473523
theorem B1649035 : Blo 1648023 1649035 := bstep (se 1 (by rfl) ⟨1236776, by rfl⟩ : syracuseStep 1649035 = 2473553) B2473553
theorem B1649047 : Blo 1648023 1649047 := bstep (se 1 (by rfl) ⟨1236785, by rfl⟩ : syracuseStep 1649047 = 2473571) B2473571
theorem B6687127 : Blo 1648023 6687127 := bstep (se 1 (by rfl) ⟨5015345, by rfl⟩ : syracuseStep 6687127 = 10030691) B10030691
theorem B1649067 : Blo 1648023 1649067 := bstep (se 1 (by rfl) ⟨1236800, by rfl⟩ : syracuseStep 1649067 = 2473601) B2473601
theorem B1649079 : Blo 1648023 1649079 := bstep (se 1 (by rfl) ⟨1236809, by rfl⟩ : syracuseStep 1649079 = 2473619) B2473619
theorem B1649099 : Blo 1648023 1649099 := bstep (se 1 (by rfl) ⟨1236824, by rfl⟩ : syracuseStep 1649099 = 2473649) B2473649
theorem B1649111 : Blo 1648023 1649111 := bstep (se 1 (by rfl) ⟨1236833, by rfl⟩ : syracuseStep 1649111 = 2473667) B2473667
theorem B4172249 : Blo 1648023 4172249 := bstep (se 2 (by rfl) ⟨1564593, by rfl⟩ : syracuseStep 4172249 = 3129187) B3129187
theorem B4696537 : Blo 1648023 4696537 := bstep (se 2 (by rfl) ⟨1761201, by rfl⟩ : syracuseStep 4696537 = 3522403) B3522403
theorem B1649131 : Blo 1648023 1649131 := bstep (se 1 (by rfl) ⟨1236848, by rfl⟩ : syracuseStep 1649131 = 2473697) B2473697
theorem B1649143 : Blo 1648023 1649143 := bstep (se 1 (by rfl) ⟨1236857, by rfl⟩ : syracuseStep 1649143 = 2473715) B2473715
theorem B1649163 : Blo 1648023 1649163 := bstep (se 1 (by rfl) ⟨1236872, by rfl⟩ : syracuseStep 1649163 = 2473745) B2473745
theorem B1649175 : Blo 1648023 1649175 := bstep (se 1 (by rfl) ⟨1236881, by rfl⟩ : syracuseStep 1649175 = 2473763) B2473763
theorem B1649195 : Blo 1648023 1649195 := bstep (se 1 (by rfl) ⟨1236896, by rfl⟩ : syracuseStep 1649195 = 2473793) B2473793
theorem B1649207 : Blo 1648023 1649207 := bstep (se 1 (by rfl) ⟨1236905, by rfl⟩ : syracuseStep 1649207 = 2473811) B2473811
theorem B1649227 : Blo 1648023 1649227 := bstep (se 1 (by rfl) ⟨1236920, by rfl⟩ : syracuseStep 1649227 = 2473841) B2473841
theorem B1649239 : Blo 1648023 1649239 := bstep (se 1 (by rfl) ⟨1236929, by rfl⟩ : syracuseStep 1649239 = 2473859) B2473859
theorem B1649259 : Blo 1648023 1649259 := bstep (se 1 (by rfl) ⟨1236944, by rfl⟩ : syracuseStep 1649259 = 2473889) B2473889
theorem B1649271 : Blo 1648023 1649271 := bstep (se 1 (by rfl) ⟨1236953, by rfl⟩ : syracuseStep 1649271 = 2473907) B2473907
theorem B1649291 : Blo 1648023 1649291 := bstep (se 1 (by rfl) ⟨1236968, by rfl⟩ : syracuseStep 1649291 = 2473937) B2473937
theorem B1854103 : Blo 1648023 1854103 := bstep (se 1 (by rfl) ⟨1390577, by rfl⟩ : syracuseStep 1854103 = 2781155) B2781155
theorem B10029719 : Blo 1648023 10029719 := bstep (se 1 (by rfl) ⟨7522289, by rfl⟩ : syracuseStep 10029719 = 15044579) B15044579
theorem B1649303 : Blo 1648023 1649303 := bstep (se 1 (by rfl) ⟨1236977, by rfl⟩ : syracuseStep 1649303 = 2473955) B2473955
theorem B1649323 : Blo 1648023 1649323 := bstep (se 1 (by rfl) ⟨1236992, by rfl⟩ : syracuseStep 1649323 = 2473985) B2473985
theorem B1649335 : Blo 1648023 1649335 := bstep (se 1 (by rfl) ⟨1237001, by rfl⟩ : syracuseStep 1649335 = 2474003) B2474003
theorem B5565131 : Blo 1648023 5565131 := bstep (se 1 (by rfl) ⟨4173848, by rfl⟩ : syracuseStep 5565131 = 8347697) B8347697
theorem B1649355 : Blo 1648023 1649355 := bstep (se 1 (by rfl) ⟨1237016, by rfl⟩ : syracuseStep 1649355 = 2474033) B2474033
theorem B1649367 : Blo 1648023 1649367 := bstep (se 1 (by rfl) ⟨1237025, by rfl⟩ : syracuseStep 1649367 = 2474051) B2474051
theorem B1649387 : Blo 1648023 1649387 := bstep (se 1 (by rfl) ⟨1237040, by rfl⟩ : syracuseStep 1649387 = 2474081) B2474081
theorem B1649399 : Blo 1648023 1649399 := bstep (se 1 (by rfl) ⟨1237049, by rfl⟩ : syracuseStep 1649399 = 2474099) B2474099
theorem B1649419 : Blo 1648023 1649419 := bstep (se 1 (by rfl) ⟨1237064, by rfl⟩ : syracuseStep 1649419 = 2474129) B2474129
theorem B1649431 : Blo 1648023 1649431 := bstep (se 1 (by rfl) ⟨1237073, by rfl⟩ : syracuseStep 1649431 = 2474147) B2474147
theorem B1649451 : Blo 1648023 1649451 := bstep (se 1 (by rfl) ⟨1237088, by rfl⟩ : syracuseStep 1649451 = 2474177) B2474177
theorem B1649463 : Blo 1648023 1649463 := bstep (se 1 (by rfl) ⟨1237097, by rfl⟩ : syracuseStep 1649463 = 2474195) B2474195
theorem B1854283 : Blo 1648023 1854283 := bstep (se 1 (by rfl) ⟨1390712, by rfl⟩ : syracuseStep 1854283 = 2781425) B2781425
theorem B1649483 : Blo 1648023 1649483 := bstep (se 1 (by rfl) ⟨1237112, by rfl⟩ : syracuseStep 1649483 = 2474225) B2474225
theorem B1649495 : Blo 1648023 1649495 := bstep (se 1 (by rfl) ⟨1237121, by rfl⟩ : syracuseStep 1649495 = 2474243) B2474243
theorem B1649515 : Blo 1648023 1649515 := bstep (se 1 (by rfl) ⟨1237136, by rfl⟩ : syracuseStep 1649515 = 2474273) B2474273
theorem B1854391 : Blo 1648023 1854391 := bstep (se 1 (by rfl) ⟨1390793, by rfl⟩ : syracuseStep 1854391 = 2781587) B2781587
theorem B5565401 : Blo 1648023 5565401 := bstep (se 2 (by rfl) ⟨2087025, by rfl⟩ : syracuseStep 5565401 = 4174051) B4174051
theorem B2640919 : Blo 1648023 2640919 := bstep (se 1 (by rfl) ⟨1980689, by rfl⟩ : syracuseStep 2640919 = 3961379) B3961379
theorem B4697153 : Blo 1648023 4697153 := bstep (se 2 (by rfl) ⟨1761432, by rfl⟩ : syracuseStep 4697153 = 3522865) B3522865
theorem B1854571 : Blo 1648023 1854571 := bstep (se 1 (by rfl) ⟨1390928, by rfl⟩ : syracuseStep 1854571 = 2781857) B2781857
theorem B3173527 : Blo 1648023 3173527 := bstep (se 1 (by rfl) ⟨2380145, by rfl⟩ : syracuseStep 3173527 = 4760291) B4760291
theorem B1854679 : Blo 1648023 1854679 := bstep (se 1 (by rfl) ⟨1391009, by rfl⟩ : syracuseStep 1854679 = 2782019) B2782019
theorem B6262019 : Blo 1648023 6262019 := bstep (se 1 (by rfl) ⟨4696514, by rfl⟩ : syracuseStep 6262019 = 9393029) B9393029
theorem B4173079 : Blo 1648023 4173079 := bstep (se 1 (by rfl) ⟨3129809, by rfl⟩ : syracuseStep 4173079 = 6259619) B6259619
theorem B2641175 : Blo 1648023 2641175 := bstep (se 1 (by rfl) ⟨1980881, by rfl⟩ : syracuseStep 2641175 = 3961763) B3961763
theorem B1854859 : Blo 1648023 1854859 := bstep (se 1 (by rfl) ⟨1391144, by rfl⟩ : syracuseStep 1854859 = 2782289) B2782289
theorem B4230593 : Blo 1648023 4230593 := bstep (se 2 (by rfl) ⟨1586472, by rfl⟩ : syracuseStep 4230593 = 3172945) B3172945
theorem B2379223 : Blo 1648023 2379223 := bstep (se 1 (by rfl) ⟨1784417, by rfl⟩ : syracuseStep 2379223 = 3568835) B3568835
theorem B1854967 : Blo 1648023 1854967 := bstep (se 1 (by rfl) ⟨1391225, by rfl⟩ : syracuseStep 1854967 = 2782451) B2782451
theorem B2346583 : Blo 1648023 2346583 := bstep (se 1 (by rfl) ⟨1759937, by rfl⟩ : syracuseStep 2346583 = 3519875) B3519875
theorem B2641547 : Blo 1648023 2641547 := bstep (se 1 (by rfl) ⟨1981160, by rfl⟩ : syracuseStep 2641547 = 3962321) B3962321
theorem B5566103 : Blo 1648023 5566103 := bstep (se 1 (by rfl) ⟨4174577, by rfl⟩ : syracuseStep 5566103 = 8349155) B8349155
theorem B1855147 : Blo 1648023 1855147 := bstep (se 1 (by rfl) ⟨1391360, by rfl⟩ : syracuseStep 1855147 = 2782721) B2782721
theorem B4173515 : Blo 1648023 4173515 := bstep (se 1 (by rfl) ⟨3130136, by rfl⟩ : syracuseStep 4173515 = 6260273) B6260273
theorem B9391889 : Blo 1648023 9391889 := bstep (se 2 (by rfl) ⟨3521958, by rfl⟩ : syracuseStep 9391889 = 7043917) B7043917
theorem B1855255 : Blo 1648023 1855255 := bstep (se 1 (by rfl) ⟨1391441, by rfl⟩ : syracuseStep 1855255 = 2782883) B2782883
theorem B7040843 : Blo 1648023 7040843 := bstep (se 1 (by rfl) ⟨5280632, by rfl⟩ : syracuseStep 7040843 = 10561265) B10561265
theorem B2781067 : Blo 1648023 2781067 := bstep (se 1 (by rfl) ⟨2085800, by rfl⟩ : syracuseStep 2781067 = 4171601) B4171601
theorem B3215297 : Blo 1648023 3215297 := bstep (se 2 (by rfl) ⟨1205736, by rfl⟩ : syracuseStep 3215297 = 2411473) B2411473
theorem B1855435 : Blo 1648023 1855435 := bstep (se 1 (by rfl) ⟨1391576, by rfl⟩ : syracuseStep 1855435 = 2783153) B2783153
theorem B2936791 : Blo 1648023 2936791 := bstep (se 1 (by rfl) ⟨2202593, by rfl⟩ : syracuseStep 2936791 = 4405187) B4405187
theorem B2641879 : Blo 1648023 2641879 := bstep (se 1 (by rfl) ⟨1981409, by rfl⟩ : syracuseStep 2641879 = 3962819) B3962819
theorem B2781209 : Blo 1648023 2781209 := bstep (se 2 (by rfl) ⟨1042953, by rfl⟩ : syracuseStep 2781209 = 2085907) B2085907
theorem B8917037 : Blo 1648023 8917037 := bstep (se 3 (by rfl) ⟨1671944, by rfl⟩ : syracuseStep 8917037 = 3343889) B3343889
theorem B1855543 : Blo 1648023 1855543 := bstep (se 1 (by rfl) ⟨1391657, by rfl⟩ : syracuseStep 1855543 = 2783315) B2783315
theorem B4173889 : Blo 1648023 4173889 := bstep (se 2 (by rfl) ⟨1565208, by rfl⟩ : syracuseStep 4173889 = 3130417) B3130417
theorem B25391173 : Blo 1648023 25391173 := bstep (se 4 (by rfl) ⟨2380422, by rfl⟩ : syracuseStep 25391173 = 4760845) B4760845
theorem B2347147 : Blo 1648023 2347147 := bstep (se 1 (by rfl) ⟨1760360, by rfl⟩ : syracuseStep 2347147 = 3520721) B3520721
theorem B2781337 : Blo 1648023 2781337 := bstep (se 2 (by rfl) ⟨1043001, by rfl⟩ : syracuseStep 2781337 = 2086003) B2086003
theorem B5566643 : Blo 1648023 5566643 := bstep (se 1 (by rfl) ⟨4174982, by rfl⟩ : syracuseStep 5566643 = 8349965) B8349965
theorem B9392345 : Blo 1648023 9392345 := bstep (se 2 (by rfl) ⟨3522129, by rfl⟩ : syracuseStep 9392345 = 7044259) B7044259
theorem B5566913 : Blo 1648023 5566913 := bstep (se 2 (by rfl) ⟨2087592, by rfl⟩ : syracuseStep 5566913 = 4175185) B4175185
theorem B3568279 : Blo 1648023 3568279 := bstep (se 1 (by rfl) ⟨2676209, by rfl⟩ : syracuseStep 3568279 = 5352419) B5352419
theorem B2970263 : Blo 1648023 2970263 := bstep (se 1 (by rfl) ⟨2227697, by rfl⟩ : syracuseStep 2970263 = 4455395) B4455395
theorem B4174487 : Blo 1648023 4174487 := bstep (se 1 (by rfl) ⟨3130865, by rfl⟩ : syracuseStep 4174487 = 6261731) B6261731
theorem B2781911 : Blo 1648023 2781911 := bstep (se 1 (by rfl) ⟨2086433, by rfl⟩ : syracuseStep 2781911 = 4172867) B4172867
theorem B12522275 : Blo 1648023 12522275 := bstep (se 1 (by rfl) ⟨9391706, by rfl⟩ : syracuseStep 12522275 = 18783413) B18783413
theorem B2782039 : Blo 1648023 2782039 := bstep (se 1 (by rfl) ⟨2086529, by rfl⟩ : syracuseStep 2782039 = 4173059) B4173059
theorem B21418931 : Blo 1648023 21418931 := bstep (se 1 (by rfl) ⟨16064198, by rfl⟩ : syracuseStep 21418931 = 32128397) B32128397
theorem B25392163 : Blo 1648023 25392163 := bstep (se 1 (by rfl) ⟨19044122, by rfl⟩ : syracuseStep 25392163 = 38088245) B38088245
theorem B3011671 : Blo 1648023 3011671 := bstep (se 1 (by rfl) ⟨2258753, by rfl⟩ : syracuseStep 3011671 = 4517507) B4517507
theorem B3708107 : Blo 1648023 3708107 := bstep (se 1 (by rfl) ⟨2781080, by rfl⟩ : syracuseStep 3708107 = 5562161) B5562161
theorem B3708161 : Blo 1648023 3708161 := bstep (se 2 (by rfl) ⟨1390560, by rfl⟩ : syracuseStep 3708161 = 2781121) B2781121
theorem B5084491 : Blo 1648023 5084491 := bstep (se 1 (by rfl) ⟨3813368, by rfl⟩ : syracuseStep 5084491 = 7626737) B7626737
theorem B2086231 : Blo 1648023 2086231 := bstep (se 1 (by rfl) ⟨1564673, by rfl⟩ : syracuseStep 2086231 = 3129347) B3129347
theorem B2971019 : Blo 1648023 2971019 := bstep (se 1 (by rfl) ⟨2228264, by rfl⟩ : syracuseStep 2971019 = 4456529) B4456529
theorem B4175297 : Blo 1648023 4175297 := bstep (se 2 (by rfl) ⟨1565736, by rfl⟩ : syracuseStep 4175297 = 3131473) B3131473
theorem B2782667 : Blo 1648023 2782667 := bstep (se 1 (by rfl) ⟨2087000, by rfl⟩ : syracuseStep 2782667 = 4174001) B4174001
theorem B3708377 : Blo 1648023 3708377 := bstep (se 2 (by rfl) ⟨1390641, by rfl⟩ : syracuseStep 3708377 = 2781283) B2781283
theorem B8345105 : Blo 1648023 8345105 := bstep (se 2 (by rfl) ⟨3129414, by rfl⟩ : syracuseStep 8345105 = 6258829) B6258829
theorem B3708467 : Blo 1648023 3708467 := bstep (se 1 (by rfl) ⟨2781350, by rfl⟩ : syracuseStep 3708467 = 5562701) B5562701
theorem B2782795 : Blo 1648023 2782795 := bstep (se 1 (by rfl) ⟨2087096, by rfl⟩ : syracuseStep 2782795 = 4174193) B4174193
theorem B3708503 : Blo 1648023 3708503 := bstep (se 1 (by rfl) ⟨2781377, by rfl⟩ : syracuseStep 3708503 = 5562755) B5562755
theorem B2348633 : Blo 1648023 2348633 := bstep (se 2 (by rfl) ⟨880737, by rfl⟩ : syracuseStep 2348633 = 1761475) B1761475
theorem B334321283 : Blo 1648023 334321283 := bstep (se 1 (by rfl) ⟨250740962, by rfl⟩ : syracuseStep 334321283 = 501481925) B501481925
theorem B8345267 : Blo 1648023 8345267 := bstep (se 1 (by rfl) ⟨6258950, by rfl⟩ : syracuseStep 8345267 = 12517901) B12517901
theorem B2782937 : Blo 1648023 2782937 := bstep (se 2 (by rfl) ⟨1043601, by rfl⟩ : syracuseStep 2782937 = 2087203) B2087203
theorem B3708683 : Blo 1648023 3708683 := bstep (se 1 (by rfl) ⟨2781512, by rfl⟩ : syracuseStep 3708683 = 5563025) B5563025
theorem B3708737 : Blo 1648023 3708737 := bstep (se 2 (by rfl) ⟨1390776, by rfl⟩ : syracuseStep 3708737 = 2781553) B2781553
theorem B2783065 : Blo 1648023 2783065 := bstep (se 2 (by rfl) ⟨1043649, by rfl⟩ : syracuseStep 2783065 = 2087299) B2087299
theorem B4577303 : Blo 1648023 4577303 := bstep (se 1 (by rfl) ⟨3432977, by rfl⟩ : syracuseStep 4577303 = 6865955) B6865955
theorem B3708953 : Blo 1648023 3708953 := bstep (se 2 (by rfl) ⟨1390857, by rfl⟩ : syracuseStep 3708953 = 2781715) B2781715
theorem B12687461 : Blo 1648023 12687461 := bstep (se 4 (by rfl) ⟨1189449, by rfl⟩ : syracuseStep 12687461 = 2378899) B2378899
theorem B1833067 : Blo 1648023 1833067 := bstep (se 1 (by rfl) ⟨1374800, by rfl⟩ : syracuseStep 1833067 = 2749601) B2749601
theorem B3709043 : Blo 1648023 3709043 := bstep (se 1 (by rfl) ⟨2781782, by rfl⟩ : syracuseStep 3709043 = 5563565) B5563565
theorem B3709079 : Blo 1648023 3709079 := bstep (se 1 (by rfl) ⟨2781809, by rfl⟩ : syracuseStep 3709079 = 5563619) B5563619
theorem B2472089 : Blo 1648023 2472089 := bstep (se 2 (by rfl) ⟨927033, by rfl⟩ : syracuseStep 2472089 = 1854067) B1854067
theorem B7919795 : Blo 1648023 7919795 := bstep (se 1 (by rfl) ⟨5939846, by rfl⟩ : syracuseStep 7919795 = 11879693) B11879693
theorem B2472203 : Blo 1648023 2472203 := bstep (se 1 (by rfl) ⟨1854152, by rfl⟩ : syracuseStep 2472203 = 3708305) B3708305
theorem B2472215 : Blo 1648023 2472215 := bstep (se 1 (by rfl) ⟨1854161, by rfl⟩ : syracuseStep 2472215 = 3708323) B3708323
theorem B7919947 : Blo 1648023 7919947 := bstep (se 1 (by rfl) ⟨5939960, by rfl⟩ : syracuseStep 7919947 = 11879921) B11879921
theorem B3709259 : Blo 1648023 3709259 := bstep (se 1 (by rfl) ⟨2781944, by rfl⟩ : syracuseStep 3709259 = 5563889) B5563889
theorem B2472281 : Blo 1648023 2472281 := bstep (se 2 (by rfl) ⟨927105, by rfl⟩ : syracuseStep 2472281 = 1854211) B1854211
theorem B2971993 : Blo 1648023 2971993 := bstep (se 2 (by rfl) ⟨1114497, by rfl⟩ : syracuseStep 2971993 = 2228995) B2228995
theorem B3520883 : Blo 1648023 3520883 := bstep (se 1 (by rfl) ⟨2640662, by rfl⟩ : syracuseStep 3520883 = 5281325) B5281325
theorem B3709313 : Blo 1648023 3709313 := bstep (se 2 (by rfl) ⟨1390992, by rfl⟩ : syracuseStep 3709313 = 2781985) B2781985
theorem B7043507 : Blo 1648023 7043507 := bstep (se 1 (by rfl) ⟨5282630, by rfl⟩ : syracuseStep 7043507 = 10565261) B10565261
theorem B2472395 : Blo 1648023 2472395 := bstep (se 1 (by rfl) ⟨1854296, by rfl⟩ : syracuseStep 2472395 = 3708593) B3708593
theorem B2472407 : Blo 1648023 2472407 := bstep (se 1 (by rfl) ⟨1854305, by rfl⟩ : syracuseStep 2472407 = 3708611) B3708611
theorem B9386513 : Blo 1648023 9386513 := bstep (se 2 (by rfl) ⟨3519942, by rfl⟩ : syracuseStep 9386513 = 7039885) B7039885
theorem B2472473 : Blo 1648023 2472473 := bstep (se 2 (by rfl) ⟨927177, by rfl⟩ : syracuseStep 2472473 = 1854355) B1854355
theorem B3709529 : Blo 1648023 3709529 := bstep (se 2 (by rfl) ⟨1391073, by rfl⟩ : syracuseStep 3709529 = 2782147) B2782147
theorem B2472587 : Blo 1648023 2472587 := bstep (se 1 (by rfl) ⟨1854440, by rfl⟩ : syracuseStep 2472587 = 3708881) B3708881
theorem B2472599 : Blo 1648023 2472599 := bstep (se 1 (by rfl) ⟨1854449, by rfl⟩ : syracuseStep 2472599 = 3708899) B3708899
theorem B3709619 : Blo 1648023 3709619 := bstep (se 1 (by rfl) ⟨2782214, by rfl⟩ : syracuseStep 3709619 = 5564429) B5564429
theorem B3709655 : Blo 1648023 3709655 := bstep (se 1 (by rfl) ⟨2782241, by rfl⟩ : syracuseStep 3709655 = 5564483) B5564483
theorem B2472665 : Blo 1648023 2472665 := bstep (se 2 (by rfl) ⟨927249, by rfl⟩ : syracuseStep 2472665 = 1854499) B1854499
theorem B7920449 : Blo 1648023 7920449 := bstep (se 2 (by rfl) ⟨2970168, by rfl⟩ : syracuseStep 7920449 = 5940337) B5940337
theorem B2472779 : Blo 1648023 2472779 := bstep (se 1 (by rfl) ⟨1854584, by rfl⟩ : syracuseStep 2472779 = 3709169) B3709169
theorem B1760087 : Blo 1648023 1760087 := bstep (se 1 (by rfl) ⟨1320065, by rfl⟩ : syracuseStep 1760087 = 2640131) B2640131
theorem B2472791 : Blo 1648023 2472791 := bstep (se 1 (by rfl) ⟨1854593, by rfl⟩ : syracuseStep 2472791 = 3709187) B3709187
theorem B3709835 : Blo 1648023 3709835 := bstep (se 1 (by rfl) ⟨2782376, by rfl⟩ : syracuseStep 3709835 = 5564753) B5564753
theorem B2472857 : Blo 1648023 2472857 := bstep (se 2 (by rfl) ⟨927321, by rfl⟩ : syracuseStep 2472857 = 1854643) B1854643
theorem B19037105 : Blo 1648023 19037105 := bstep (se 2 (by rfl) ⟨7138914, by rfl⟩ : syracuseStep 19037105 = 14277829) B14277829
theorem B3709889 : Blo 1648023 3709889 := bstep (se 2 (by rfl) ⟨1391208, by rfl⟩ : syracuseStep 3709889 = 2782417) B2782417
theorem B2472971 : Blo 1648023 2472971 := bstep (se 1 (by rfl) ⟨1854728, by rfl⟩ : syracuseStep 2472971 = 3709457) B3709457
theorem B2472983 : Blo 1648023 2472983 := bstep (se 1 (by rfl) ⟨1854737, by rfl⟩ : syracuseStep 2472983 = 3709475) B3709475
theorem B2473049 : Blo 1648023 2473049 := bstep (se 2 (by rfl) ⟨927393, by rfl⟩ : syracuseStep 2473049 = 1854787) B1854787
theorem B3710105 : Blo 1648023 3710105 := bstep (se 2 (by rfl) ⟨1391289, by rfl⟩ : syracuseStep 3710105 = 2782579) B2782579
theorem B6257843 : Blo 1648023 6257843 := bstep (se 1 (by rfl) ⟨4693382, by rfl⟩ : syracuseStep 6257843 = 9386765) B9386765
theorem B6257857 : Blo 1648023 6257857 := bstep (se 2 (by rfl) ⟨2346696, by rfl⟩ : syracuseStep 6257857 = 4693393) B4693393
theorem B2473163 : Blo 1648023 2473163 := bstep (se 1 (by rfl) ⟨1854872, by rfl⟩ : syracuseStep 2473163 = 3709745) B3709745
theorem B2473175 : Blo 1648023 2473175 := bstep (se 1 (by rfl) ⟨1854881, by rfl⟩ : syracuseStep 2473175 = 3709763) B3709763
theorem B3710195 : Blo 1648023 3710195 := bstep (se 1 (by rfl) ⟨2782646, by rfl⟩ : syracuseStep 3710195 = 5565293) B5565293
theorem B3710231 : Blo 1648023 3710231 := bstep (se 1 (by rfl) ⟨2782673, by rfl⟩ : syracuseStep 3710231 = 5565347) B5565347
theorem B2473241 : Blo 1648023 2473241 := bstep (se 2 (by rfl) ⟨927465, by rfl⟩ : syracuseStep 2473241 = 1854931) B1854931
theorem B7626035 : Blo 1648023 7626035 := bstep (se 1 (by rfl) ⟨5719526, by rfl⟩ : syracuseStep 7626035 = 11439053) B11439053
theorem B2473355 : Blo 1648023 2473355 := bstep (se 1 (by rfl) ⟨1855016, by rfl⟩ : syracuseStep 2473355 = 3710033) B3710033
theorem B2473367 : Blo 1648023 2473367 := bstep (se 1 (by rfl) ⟨1855025, by rfl⟩ : syracuseStep 2473367 = 3710051) B3710051
theorem B3341747 : Blo 1648023 3341747 := bstep (se 1 (by rfl) ⟨2506310, by rfl⟩ : syracuseStep 3341747 = 5012621) B5012621
theorem B3710411 : Blo 1648023 3710411 := bstep (se 1 (by rfl) ⟨2782808, by rfl⟩ : syracuseStep 3710411 = 5565617) B5565617
theorem B2473433 : Blo 1648023 2473433 := bstep (se 2 (by rfl) ⟨927537, by rfl⟩ : syracuseStep 2473433 = 1855075) B1855075
theorem B3710465 : Blo 1648023 3710465 := bstep (se 2 (by rfl) ⟨1391424, by rfl⟩ : syracuseStep 3710465 = 2782849) B2782849
theorem B12516929 : Blo 1648023 12516929 := bstep (se 2 (by rfl) ⟨4693848, by rfl⟩ : syracuseStep 12516929 = 9387697) B9387697
theorem B3522113 : Blo 1648023 3522113 := bstep (se 2 (by rfl) ⟨1320792, by rfl⟩ : syracuseStep 3522113 = 2641585) B2641585
theorem B8347211 : Blo 1648023 8347211 := bstep (se 1 (by rfl) ⟨6260408, by rfl⟩ : syracuseStep 8347211 = 12520817) B12520817
theorem B2473547 : Blo 1648023 2473547 := bstep (se 1 (by rfl) ⟨1855160, by rfl⟩ : syracuseStep 2473547 = 3710321) B3710321
theorem B3759703 : Blo 1648023 3759703 := bstep (se 1 (by rfl) ⟨2819777, by rfl⟩ : syracuseStep 3759703 = 5639555) B5639555
theorem B2473559 : Blo 1648023 2473559 := bstep (se 1 (by rfl) ⟨1855169, by rfl⟩ : syracuseStep 2473559 = 3710339) B3710339
theorem B2473625 : Blo 1648023 2473625 := bstep (se 2 (by rfl) ⟨927609, by rfl⟩ : syracuseStep 2473625 = 1855219) B1855219
theorem B53468869 : Blo 1648023 53468869 := bstep (se 4 (by rfl) ⟨5012706, by rfl⟩ : syracuseStep 53468869 = 10025413) B10025413
theorem B3759833 : Blo 1648023 3759833 := bstep (se 2 (by rfl) ⟨1409937, by rfl⟩ : syracuseStep 3759833 = 2819875) B2819875
theorem B3710681 : Blo 1648023 3710681 := bstep (se 2 (by rfl) ⟨1391505, by rfl⟩ : syracuseStep 3710681 = 2783011) B2783011
theorem B2473739 : Blo 1648023 2473739 := bstep (se 1 (by rfl) ⟨1855304, by rfl⟩ : syracuseStep 2473739 = 3710609) B3710609
theorem B2473751 : Blo 1648023 2473751 := bstep (se 1 (by rfl) ⟨1855313, by rfl⟩ : syracuseStep 2473751 = 3710627) B3710627
theorem B10026797 : Blo 1648023 10026797 := bstep (se 3 (by rfl) ⟨1880024, by rfl⟩ : syracuseStep 10026797 = 3760049) B3760049
theorem B3710771 : Blo 1648023 3710771 := bstep (se 1 (by rfl) ⟨2783078, by rfl⟩ : syracuseStep 3710771 = 5566157) B5566157
theorem B3710807 : Blo 1648023 3710807 := bstep (se 1 (by rfl) ⟨2783105, by rfl⟩ : syracuseStep 3710807 = 5566211) B5566211
theorem B2473817 : Blo 1648023 2473817 := bstep (se 2 (by rfl) ⟨927681, by rfl⟩ : syracuseStep 2473817 = 1855363) B1855363
theorem B10166147 : Blo 1648023 10166147 := bstep (se 1 (by rfl) ⟨7624610, by rfl⟩ : syracuseStep 10166147 = 15249221) B15249221
theorem B7044995 : Blo 1648023 7044995 := bstep (se 1 (by rfl) ⟨5283746, by rfl⟩ : syracuseStep 7044995 = 10567493) B10567493
theorem B4693963 : Blo 1648023 4693963 := bstep (se 1 (by rfl) ⟨3520472, by rfl⟩ : syracuseStep 4693963 = 7040945) B7040945
theorem B2473931 : Blo 1648023 2473931 := bstep (se 1 (by rfl) ⟨1855448, by rfl⟩ : syracuseStep 2473931 = 3710897) B3710897
theorem B2473943 : Blo 1648023 2473943 := bstep (se 1 (by rfl) ⟨1855457, by rfl⟩ : syracuseStep 2473943 = 3710915) B3710915
theorem B2473991 : Blo 1648023 2473991 := bstep (se 1 (by rfl) ⟨1855493, by rfl⟩ : syracuseStep 2473991 = 3710987) B3710987
theorem B2474027 : Blo 1648023 2474027 := bstep (se 1 (by rfl) ⟨1855520, by rfl⟩ : syracuseStep 2474027 = 3711041) B3711041
theorem B2474057 : Blo 1648023 2474057 := bstep (se 2 (by rfl) ⟨927771, by rfl⟩ : syracuseStep 2474057 = 1855543) B1855543
theorem B2506871 : Blo 1648023 2506871 := bstep (se 1 (by rfl) ⟨1880153, by rfl⟩ : syracuseStep 2506871 = 3760307) B3760307
theorem B3711095 : Blo 1648023 3711095 := bstep (se 1 (by rfl) ⟨2783321, by rfl⟩ : syracuseStep 3711095 = 5566643) B5566643
theorem B3129491 : Blo 1648023 3129491 := bstep (se 1 (by rfl) ⟨2347118, by rfl⟩ : syracuseStep 3129491 = 4694237) B4694237
theorem B3129529 : Blo 1648023 3129529 := bstep (se 2 (by rfl) ⟨1173573, by rfl⟩ : syracuseStep 3129529 = 2347147) B2347147
theorem B2474171 : Blo 1648023 2474171 := bstep (se 1 (by rfl) ⟨1855628, by rfl⟩ : syracuseStep 2474171 = 3711257) B3711257
theorem B2474231 : Blo 1648023 2474231 := bstep (se 1 (by rfl) ⟨1855673, by rfl⟩ : syracuseStep 2474231 = 3711347) B3711347
theorem B2474255 : Blo 1648023 2474255 := bstep (se 1 (by rfl) ⟨1855691, by rfl⟩ : syracuseStep 2474255 = 3711383) B3711383
theorem B3711275 : Blo 1648023 3711275 := bstep (se 1 (by rfl) ⟨2783456, by rfl⟩ : syracuseStep 3711275 = 5566913) B5566913
theorem B5562809 : Blo 1648023 5562809 := bstep (se 2 (by rfl) ⟨2086053, by rfl⟩ : syracuseStep 5562809 = 4172107) B4172107
theorem B2539963 : Blo 1648023 2539963 := bstep (se 1 (by rfl) ⟨1904972, by rfl⟩ : syracuseStep 2539963 = 3809945) B3809945
theorem B14090705 : Blo 1648023 14090705 := bstep (se 2 (by rfl) ⟨5284014, by rfl⟩ : syracuseStep 14090705 = 10568029) B10568029
theorem B8348183 : Blo 1648023 8348183 := bstep (se 1 (by rfl) ⟨6261137, by rfl⟩ : syracuseStep 8348183 = 12522275) B12522275
theorem B4457047 : Blo 1648023 4457047 := bstep (se 1 (by rfl) ⟨3342785, by rfl⟩ : syracuseStep 4457047 = 6685571) B6685571
theorem B1671823 : Blo 1648023 1671823 := bstep (se 1 (by rfl) ⟨1253867, by rfl⟩ : syracuseStep 1671823 = 2507735) B2507735
theorem B5014169 : Blo 1648023 5014169 := bstep (se 2 (by rfl) ⟨1880313, by rfl⟩ : syracuseStep 5014169 = 3760627) B3760627
theorem B5563403 : Blo 1648023 5563403 := bstep (se 1 (by rfl) ⟨4172552, by rfl⟩ : syracuseStep 5563403 = 8345105) B8345105
theorem B22873099 : Blo 1648023 22873099 := bstep (se 1 (by rfl) ⟨17154824, by rfl⟩ : syracuseStep 22873099 = 34309649) B34309649
theorem B7922717 : Blo 1648023 7922717 := bstep (se 3 (by rfl) ⟨1485509, by rfl⟩ : syracuseStep 7922717 = 2971019) B2971019
theorem B8914007 : Blo 1648023 8914007 := bstep (se 1 (by rfl) ⟨6685505, by rfl⟩ : syracuseStep 8914007 = 13371011) B13371011
theorem B5563511 : Blo 1648023 5563511 := bstep (se 1 (by rfl) ⟨4172633, by rfl⟩ : syracuseStep 5563511 = 8345267) B8345267
theorem B4015475 : Blo 1648023 4015475 := bstep (se 1 (by rfl) ⟨3011606, by rfl⟩ : syracuseStep 4015475 = 6023213) B6023213
theorem B4015507 : Blo 1648023 4015507 := bstep (se 1 (by rfl) ⟨3011630, by rfl⟩ : syracuseStep 4015507 = 6023261) B6023261
theorem B1648059 : Blo 1648023 1648059 := bstep (se 1 (by rfl) ⟨1236044, by rfl⟩ : syracuseStep 1648059 = 2472089) B2472089
theorem B3343817 : Blo 1648023 3343817 := bstep (se 2 (by rfl) ⟨1253931, by rfl⟩ : syracuseStep 3343817 = 2507863) B2507863
theorem B1648135 : Blo 1648023 1648135 := bstep (se 1 (by rfl) ⟨1236101, by rfl⟩ : syracuseStep 1648135 = 2472203) B2472203
theorem B1648143 : Blo 1648023 1648143 := bstep (se 1 (by rfl) ⟨1236107, by rfl⟩ : syracuseStep 1648143 = 2472215) B2472215
theorem B1648187 : Blo 1648023 1648187 := bstep (se 1 (by rfl) ⟨1236140, by rfl⟩ : syracuseStep 1648187 = 2472281) B2472281
theorem B4695671 : Blo 1648023 4695671 := bstep (se 1 (by rfl) ⟨3521753, by rfl⟩ : syracuseStep 4695671 = 7043507) B7043507
theorem B1648263 : Blo 1648023 1648263 := bstep (se 1 (by rfl) ⟨1236197, by rfl⟩ : syracuseStep 1648263 = 2472395) B2472395
theorem B1648271 : Blo 1648023 1648271 := bstep (se 1 (by rfl) ⟨1236203, by rfl⟩ : syracuseStep 1648271 = 2472407) B2472407
theorem B1648315 : Blo 1648023 1648315 := bstep (se 1 (by rfl) ⟨1236236, by rfl⟩ : syracuseStep 1648315 = 2472473) B2472473
theorem B5564105 : Blo 1648023 5564105 := bstep (se 2 (by rfl) ⟨2086539, by rfl⟩ : syracuseStep 5564105 = 4173079) B4173079
theorem B42239717 : Blo 1648023 42239717 := bstep (se 4 (by rfl) ⟨3959973, by rfl⟩ : syracuseStep 42239717 = 7919947) B7919947
theorem B1648391 : Blo 1648023 1648391 := bstep (se 1 (by rfl) ⟨1236293, by rfl⟩ : syracuseStep 1648391 = 2472587) B2472587
theorem B1648399 : Blo 1648023 1648399 := bstep (se 1 (by rfl) ⟨1236299, by rfl⟩ : syracuseStep 1648399 = 2472599) B2472599
theorem B6686479 : Blo 1648023 6686479 := bstep (se 1 (by rfl) ⟨5014859, by rfl⟩ : syracuseStep 6686479 = 10029719) B10029719
theorem B1648443 : Blo 1648023 1648443 := bstep (se 1 (by rfl) ⟨1236332, by rfl⟩ : syracuseStep 1648443 = 2472665) B2472665
theorem B1648519 : Blo 1648023 1648519 := bstep (se 1 (by rfl) ⟨1236389, by rfl⟩ : syracuseStep 1648519 = 2472779) B2472779
theorem B1648527 : Blo 1648023 1648527 := bstep (se 1 (by rfl) ⟨1236395, by rfl⟩ : syracuseStep 1648527 = 2472791) B2472791
theorem B1648571 : Blo 1648023 1648571 := bstep (se 1 (by rfl) ⟨1236428, by rfl⟩ : syracuseStep 1648571 = 2472857) B2472857
theorem B3172297 : Blo 1648023 3172297 := bstep (se 2 (by rfl) ⟨1189611, by rfl⟩ : syracuseStep 3172297 = 2379223) B2379223
theorem B12691403 : Blo 1648023 12691403 := bstep (se 1 (by rfl) ⟨9518552, by rfl⟩ : syracuseStep 12691403 = 19037105) B19037105
theorem B1648647 : Blo 1648023 1648647 := bstep (se 1 (by rfl) ⟨1236485, by rfl⟩ : syracuseStep 1648647 = 2472971) B2472971
theorem B1648655 : Blo 1648023 1648655 := bstep (se 1 (by rfl) ⟨1236491, by rfl⟩ : syracuseStep 1648655 = 2472983) B2472983
theorem B3131435 : Blo 1648023 3131435 := bstep (se 1 (by rfl) ⟨2348576, by rfl⟩ : syracuseStep 3131435 = 4697153) B4697153
theorem B1648699 : Blo 1648023 1648699 := bstep (se 1 (by rfl) ⟨1236524, by rfl⟩ : syracuseStep 1648699 = 2473049) B2473049
theorem B4171895 : Blo 1648023 4171895 := bstep (se 1 (by rfl) ⟨3128921, by rfl⟩ : syracuseStep 4171895 = 6257843) B6257843
theorem B1648775 : Blo 1648023 1648775 := bstep (se 1 (by rfl) ⟨1236581, by rfl⟩ : syracuseStep 1648775 = 2473163) B2473163
theorem B1648783 : Blo 1648023 1648783 := bstep (se 1 (by rfl) ⟨1236587, by rfl⟩ : syracuseStep 1648783 = 2473175) B2473175
theorem B1648827 : Blo 1648023 1648827 := bstep (se 1 (by rfl) ⟨1236620, by rfl⟩ : syracuseStep 1648827 = 2473241) B2473241
theorem B1648903 : Blo 1648023 1648903 := bstep (se 1 (by rfl) ⟨1236677, by rfl⟩ : syracuseStep 1648903 = 2473355) B2473355
theorem B1648911 : Blo 1648023 1648911 := bstep (se 1 (by rfl) ⟨1236683, by rfl⟩ : syracuseStep 1648911 = 2473367) B2473367
theorem B2820395 : Blo 1648023 2820395 := bstep (se 1 (by rfl) ⟨2115296, by rfl⟩ : syracuseStep 2820395 = 4230593) B4230593
theorem B1648955 : Blo 1648023 1648955 := bstep (se 1 (by rfl) ⟨1236716, by rfl⟩ : syracuseStep 1648955 = 2473433) B2473433
theorem B5564807 : Blo 1648023 5564807 := bstep (se 1 (by rfl) ⟨4173605, by rfl⟩ : syracuseStep 5564807 = 8347211) B8347211
theorem B1649031 : Blo 1648023 1649031 := bstep (se 1 (by rfl) ⟨1236773, by rfl⟩ : syracuseStep 1649031 = 2473547) B2473547
theorem B1649039 : Blo 1648023 1649039 := bstep (se 1 (by rfl) ⟨1236779, by rfl⟩ : syracuseStep 1649039 = 2473559) B2473559
theorem B1649083 : Blo 1648023 1649083 := bstep (se 1 (by rfl) ⟨1236812, by rfl⟩ : syracuseStep 1649083 = 2473625) B2473625
theorem B57117149 : Blo 1648023 57117149 := bstep (se 3 (by rfl) ⟨10709465, by rfl⟩ : syracuseStep 57117149 = 21418931) B21418931
theorem B1649159 : Blo 1648023 1649159 := bstep (se 1 (by rfl) ⟨1236869, by rfl⟩ : syracuseStep 1649159 = 2473739) B2473739
theorem B6261259 : Blo 1648023 6261259 := bstep (se 1 (by rfl) ⟨4695944, by rfl⟩ : syracuseStep 6261259 = 9391889) B9391889
theorem B1649167 : Blo 1648023 1649167 := bstep (se 1 (by rfl) ⟨1236875, by rfl⟩ : syracuseStep 1649167 = 2473751) B2473751
theorem B1649211 : Blo 1648023 1649211 := bstep (se 1 (by rfl) ⟨1236908, by rfl⟩ : syracuseStep 1649211 = 2473817) B2473817
theorem B6777431 : Blo 1648023 6777431 := bstep (se 1 (by rfl) ⟨5083073, by rfl⟩ : syracuseStep 6777431 = 10166147) B10166147
theorem B4696663 : Blo 1648023 4696663 := bstep (se 1 (by rfl) ⟨3522497, by rfl⟩ : syracuseStep 4696663 = 7044995) B7044995
theorem B1649287 : Blo 1648023 1649287 := bstep (se 1 (by rfl) ⟨1236965, by rfl⟩ : syracuseStep 1649287 = 2473931) B2473931
theorem B1649295 : Blo 1648023 1649295 := bstep (se 1 (by rfl) ⟨1236971, by rfl⟩ : syracuseStep 1649295 = 2473943) B2473943
theorem B1854139 : Blo 1648023 1854139 := bstep (se 1 (by rfl) ⟨1390604, by rfl⟩ : syracuseStep 1854139 = 2781209) B2781209
theorem B1649339 : Blo 1648023 1649339 := bstep (se 1 (by rfl) ⟨1237004, by rfl⟩ : syracuseStep 1649339 = 2474009) B2474009
theorem B5565185 : Blo 1648023 5565185 := bstep (se 2 (by rfl) ⟨2086944, by rfl⟩ : syracuseStep 5565185 = 4173889) B4173889
theorem B1649415 : Blo 1648023 1649415 := bstep (se 1 (by rfl) ⟨1237061, by rfl⟩ : syracuseStep 1649415 = 2474123) B2474123
theorem B1649423 : Blo 1648023 1649423 := bstep (se 1 (by rfl) ⟨1237067, by rfl⟩ : syracuseStep 1649423 = 2474135) B2474135
theorem B2444089 : Blo 1648023 2444089 := bstep (se 2 (by rfl) ⟨916533, by rfl⟩ : syracuseStep 2444089 = 1833067) B1833067
theorem B6261563 : Blo 1648023 6261563 := bstep (se 1 (by rfl) ⟨4696172, by rfl⟩ : syracuseStep 6261563 = 9392345) B9392345
theorem B1649467 : Blo 1648023 1649467 := bstep (se 1 (by rfl) ⟨1237100, by rfl⟩ : syracuseStep 1649467 = 2474201) B2474201
theorem B11889611 : Blo 1648023 11889611 := bstep (se 1 (by rfl) ⟨8917208, by rfl⟩ : syracuseStep 11889611 = 17834417) B17834417
theorem B1854607 : Blo 1648023 1854607 := bstep (se 1 (by rfl) ⟨1390955, by rfl⟩ : syracuseStep 1854607 = 2781911) B2781911
theorem B8916169 : Blo 1648023 8916169 := bstep (se 2 (by rfl) ⟨3343563, by rfl⟩ : syracuseStep 8916169 = 6687127) B6687127
theorem B6262049 : Blo 1648023 6262049 := bstep (se 2 (by rfl) ⟨2348268, by rfl⟩ : syracuseStep 6262049 = 4696537) B4696537
theorem B4173191 : Blo 1648023 4173191 := bstep (se 1 (by rfl) ⟨3129893, by rfl⟩ : syracuseStep 4173191 = 6259787) B6259787
theorem B4173241 : Blo 1648023 4173241 := bstep (se 2 (by rfl) ⟨1564965, by rfl⟩ : syracuseStep 4173241 = 3129931) B3129931
theorem B20336093 : Blo 1648023 20336093 := bstep (se 3 (by rfl) ⟨3813017, by rfl⟩ : syracuseStep 20336093 = 7626035) B7626035
theorem B5565995 : Blo 1648023 5565995 := bstep (se 1 (by rfl) ⟨4174496, by rfl⟩ : syracuseStep 5565995 = 8348993) B8348993
theorem B1855111 : Blo 1648023 1855111 := bstep (se 1 (by rfl) ⟨1391333, by rfl⟩ : syracuseStep 1855111 = 2782667) B2782667
theorem B1855291 : Blo 1648023 1855291 := bstep (se 1 (by rfl) ⟨1391468, by rfl⟩ : syracuseStep 1855291 = 2782937) B2782937
theorem B2781047 : Blo 1648023 2781047 := bstep (se 1 (by rfl) ⟨2085785, by rfl⟩ : syracuseStep 2781047 = 4171571) B4171571
theorem B3051535 : Blo 1648023 3051535 := bstep (se 1 (by rfl) ⟨2288651, by rfl⟩ : syracuseStep 3051535 = 4577303) B4577303
theorem B4173839 : Blo 1648023 4173839 := bstep (se 1 (by rfl) ⟨3130379, by rfl⟩ : syracuseStep 4173839 = 6260759) B6260759
theorem B8458307 : Blo 1648023 8458307 := bstep (se 1 (by rfl) ⟨6343730, by rfl⟩ : syracuseStep 8458307 = 12687461) B12687461
theorem B5279863 : Blo 1648023 5279863 := bstep (se 1 (by rfl) ⟨3959897, by rfl⟩ : syracuseStep 5279863 = 7919795) B7919795
theorem B4231369 : Blo 1648023 4231369 := bstep (se 2 (by rfl) ⟨1586763, by rfl⟩ : syracuseStep 4231369 = 3173527) B3173527
theorem B6263021 : Blo 1648023 6263021 := bstep (se 3 (by rfl) ⟨1174316, by rfl⟩ : syracuseStep 6263021 = 2348633) B2348633
theorem B2347255 : Blo 1648023 2347255 := bstep (se 1 (by rfl) ⟨1760441, by rfl⟩ : syracuseStep 2347255 = 3520883) B3520883
theorem B8343809 : Blo 1648023 8343809 := bstep (se 2 (by rfl) ⟨3128928, by rfl⟩ : syracuseStep 8343809 = 6257857) B6257857
theorem B2781499 : Blo 1648023 2781499 := bstep (se 1 (by rfl) ⟨2086124, by rfl⟩ : syracuseStep 2781499 = 4172249) B4172249
theorem B891523421 : Blo 1648023 891523421 := bstep (se 3 (by rfl) ⟨167160641, by rfl⟩ : syracuseStep 891523421 = 334321283) B334321283
theorem B6779321 : Blo 1648023 6779321 := bstep (se 2 (by rfl) ⟨2542245, by rfl⟩ : syracuseStep 6779321 = 5084491) B5084491
theorem B2781641 : Blo 1648023 2781641 := bstep (se 2 (by rfl) ⟨1043115, by rfl⟩ : syracuseStep 2781641 = 2086231) B2086231
theorem B5280299 : Blo 1648023 5280299 := bstep (se 1 (by rfl) ⟨3960224, by rfl⟩ : syracuseStep 5280299 = 7920449) B7920449
theorem B10564289 : Blo 1648023 10564289 := bstep (se 2 (by rfl) ⟨3961608, by rfl⟩ : syracuseStep 10564289 = 7923217) B7923217
theorem B4174537 : Blo 1648023 4174537 := bstep (se 2 (by rfl) ⟨1565451, by rfl⟩ : syracuseStep 4174537 = 3130903) B3130903
theorem B4174679 : Blo 1648023 4174679 := bstep (se 1 (by rfl) ⟨3131009, by rfl⟩ : syracuseStep 4174679 = 6262019) B6262019
theorem B71291825 : Blo 1648023 71291825 := bstep (se 2 (by rfl) ⟨26734434, by rfl⟩ : syracuseStep 71291825 = 53468869) B53468869
theorem B8344619 : Blo 1648023 8344619 := bstep (se 1 (by rfl) ⟨6258464, by rfl⟩ : syracuseStep 8344619 = 12516929) B12516929
theorem B2348075 : Blo 1648023 2348075 := bstep (se 1 (by rfl) ⟨1761056, by rfl⟩ : syracuseStep 2348075 = 3522113) B3522113
theorem B2782343 : Blo 1648023 2782343 := bstep (se 1 (by rfl) ⟨2086757, by rfl⟩ : syracuseStep 2782343 = 4173515) B4173515
theorem B8574125 : Blo 1648023 8574125 := bstep (se 3 (by rfl) ⟨1607648, by rfl⟩ : syracuseStep 8574125 = 3215297) B3215297
theorem B3708089 : Blo 1648023 3708089 := bstep (se 2 (by rfl) ⟨1390533, by rfl⟩ : syracuseStep 3708089 = 2781067) B2781067
theorem B38057197 : Blo 1648023 38057197 := bstep (se 3 (by rfl) ⟨7135724, by rfl⟩ : syracuseStep 38057197 = 14271449) B14271449
theorem B5944691 : Blo 1648023 5944691 := bstep (se 1 (by rfl) ⟨4458518, by rfl⟩ : syracuseStep 5944691 = 8917037) B8917037
theorem B5641607 : Blo 1648023 5641607 := bstep (se 1 (by rfl) ⟨4231205, by rfl⟩ : syracuseStep 5641607 = 8462411) B8462411
theorem B33854897 : Blo 1648023 33854897 := bstep (se 2 (by rfl) ⟨12695586, by rfl⟩ : syracuseStep 33854897 = 25391173) B25391173
theorem B3708431 : Blo 1648023 3708431 := bstep (se 1 (by rfl) ⟨2781323, by rfl⟩ : syracuseStep 3708431 = 5562647) B5562647
theorem B3708449 : Blo 1648023 3708449 := bstep (se 2 (by rfl) ⟨1390668, by rfl⟩ : syracuseStep 3708449 = 2781337) B2781337
theorem B1980175 : Blo 1648023 1980175 := bstep (se 1 (by rfl) ⟨1485131, by rfl⟩ : syracuseStep 1980175 = 2970263) B2970263
theorem B2782991 : Blo 1648023 2782991 := bstep (se 1 (by rfl) ⟨2087243, by rfl⟩ : syracuseStep 2782991 = 4174487) B4174487
theorem B3962657 : Blo 1648023 3962657 := bstep (se 2 (by rfl) ⟨1485996, by rfl⟩ : syracuseStep 3962657 = 2971993) B2971993
theorem B20051749 : Blo 1648023 20051749 := bstep (se 4 (by rfl) ⟨1879851, by rfl⟩ : syracuseStep 20051749 = 3759703) B3759703
theorem B16062245 : Blo 1648023 16062245 := bstep (se 4 (by rfl) ⟨1505835, by rfl⟩ : syracuseStep 16062245 = 3011671) B3011671
theorem B106952501 : Blo 1648023 106952501 := bstep (se 5 (by rfl) ⟨5013398, by rfl⟩ : syracuseStep 106952501 = 10026797) B10026797
theorem B5281595 : Blo 1648023 5281595 := bstep (se 1 (by rfl) ⟨3961196, by rfl⟩ : syracuseStep 5281595 = 7922393) B7922393
theorem B3708791 : Blo 1648023 3708791 := bstep (se 1 (by rfl) ⟨2781593, by rfl⟩ : syracuseStep 3708791 = 5563187) B5563187
theorem B9394055 : Blo 1648023 9394055 := bstep (se 1 (by rfl) ⟨7045541, by rfl⟩ : syracuseStep 9394055 = 14091083) B14091083
theorem B3708971 : Blo 1648023 3708971 := bstep (se 1 (by rfl) ⟨2781728, by rfl⟩ : syracuseStep 3708971 = 5563457) B5563457
theorem B2472071 : Blo 1648023 2472071 := bstep (se 1 (by rfl) ⟨1854053, by rfl⟩ : syracuseStep 2472071 = 3708107) B3708107
theorem B2472107 : Blo 1648023 2472107 := bstep (se 1 (by rfl) ⟨1854080, by rfl⟩ : syracuseStep 2472107 = 3708161) B3708161
theorem B2472137 : Blo 1648023 2472137 := bstep (se 2 (by rfl) ⟨927051, by rfl⟩ : syracuseStep 2472137 = 1854103) B1854103
theorem B4757705 : Blo 1648023 4757705 := bstep (se 2 (by rfl) ⟨1784139, by rfl⟩ : syracuseStep 4757705 = 3568279) B3568279
theorem B2783531 : Blo 1648023 2783531 := bstep (se 1 (by rfl) ⟨2087648, by rfl⟩ : syracuseStep 2783531 = 4175297) B4175297
theorem B2472251 : Blo 1648023 2472251 := bstep (se 1 (by rfl) ⟨1854188, by rfl⟩ : syracuseStep 2472251 = 3708377) B3708377
theorem B8345915 : Blo 1648023 8345915 := bstep (se 1 (by rfl) ⟨6259436, by rfl⟩ : syracuseStep 8345915 = 12518873) B12518873
theorem B2472311 : Blo 1648023 2472311 := bstep (se 1 (by rfl) ⟨1854233, by rfl⟩ : syracuseStep 2472311 = 3708467) B3708467
theorem B2472335 : Blo 1648023 2472335 := bstep (se 1 (by rfl) ⟨1854251, by rfl⟩ : syracuseStep 2472335 = 3708503) B3708503
theorem B3709331 : Blo 1648023 3709331 := bstep (se 1 (by rfl) ⟨2781998, by rfl⟩ : syracuseStep 3709331 = 5563997) B5563997
theorem B2472377 : Blo 1648023 2472377 := bstep (se 2 (by rfl) ⟨927141, by rfl⟩ : syracuseStep 2472377 = 1854283) B1854283
theorem B3709385 : Blo 1648023 3709385 := bstep (se 2 (by rfl) ⟨1391019, by rfl⟩ : syracuseStep 3709385 = 2782039) B2782039
theorem B8911325 : Blo 1648023 8911325 := bstep (se 3 (by rfl) ⟨1670873, by rfl⟩ : syracuseStep 8911325 = 3341747) B3341747
theorem B8346077 : Blo 1648023 8346077 := bstep (se 3 (by rfl) ⟨1564889, by rfl⟩ : syracuseStep 8346077 = 3129779) B3129779
theorem B2472455 : Blo 1648023 2472455 := bstep (se 1 (by rfl) ⟨1854341, by rfl⟩ : syracuseStep 2472455 = 3708683) B3708683
theorem B2472491 : Blo 1648023 2472491 := bstep (se 1 (by rfl) ⟨1854368, by rfl⟩ : syracuseStep 2472491 = 3708737) B3708737
theorem B2472521 : Blo 1648023 2472521 := bstep (se 2 (by rfl) ⟨927195, by rfl⟩ : syracuseStep 2472521 = 1854391) B1854391
theorem B2472635 : Blo 1648023 2472635 := bstep (se 1 (by rfl) ⟨1854476, by rfl⟩ : syracuseStep 2472635 = 3708953) B3708953
theorem B3521225 : Blo 1648023 3521225 := bstep (se 2 (by rfl) ⟨1320459, by rfl⟩ : syracuseStep 3521225 = 2640919) B2640919
theorem B33856217 : Blo 1648023 33856217 := bstep (se 2 (by rfl) ⟨12696081, by rfl⟩ : syracuseStep 33856217 = 25392163) B25392163
theorem B2472695 : Blo 1648023 2472695 := bstep (se 1 (by rfl) ⟨1854521, by rfl⟩ : syracuseStep 2472695 = 3709043) B3709043
theorem B2472719 : Blo 1648023 2472719 := bstep (se 1 (by rfl) ⟨1854539, by rfl⟩ : syracuseStep 2472719 = 3709079) B3709079
theorem B8346401 : Blo 1648023 8346401 := bstep (se 2 (by rfl) ⟨3129900, by rfl⟩ : syracuseStep 8346401 = 6259801) B6259801
theorem B2472761 : Blo 1648023 2472761 := bstep (se 2 (by rfl) ⟨927285, by rfl⟩ : syracuseStep 2472761 = 1854571) B1854571
theorem B2472839 : Blo 1648023 2472839 := bstep (se 1 (by rfl) ⟨1854629, by rfl⟩ : syracuseStep 2472839 = 3709259) B3709259
theorem B2472875 : Blo 1648023 2472875 := bstep (se 1 (by rfl) ⟨1854656, by rfl⟩ : syracuseStep 2472875 = 3709313) B3709313
theorem B2472905 : Blo 1648023 2472905 := bstep (se 2 (by rfl) ⟨927339, by rfl⟩ : syracuseStep 2472905 = 1854679) B1854679
theorem B6257675 : Blo 1648023 6257675 := bstep (se 1 (by rfl) ⟨4693256, by rfl⟩ : syracuseStep 6257675 = 9386513) B9386513
theorem B2473019 : Blo 1648023 2473019 := bstep (se 1 (by rfl) ⟨1854764, by rfl⟩ : syracuseStep 2473019 = 3709529) B3709529
theorem B2473079 : Blo 1648023 2473079 := bstep (se 1 (by rfl) ⟨1854809, by rfl⟩ : syracuseStep 2473079 = 3709619) B3709619
theorem B3710087 : Blo 1648023 3710087 := bstep (se 1 (by rfl) ⟨2782565, by rfl⟩ : syracuseStep 3710087 = 5565131) B5565131
theorem B2473103 : Blo 1648023 2473103 := bstep (se 1 (by rfl) ⟨1854827, by rfl⟩ : syracuseStep 2473103 = 3709655) B3709655
theorem B2473145 : Blo 1648023 2473145 := bstep (se 2 (by rfl) ⟨927429, by rfl⟩ : syracuseStep 2473145 = 1854859) B1854859
theorem B2473223 : Blo 1648023 2473223 := bstep (se 1 (by rfl) ⟨1854917, by rfl⟩ : syracuseStep 2473223 = 3709835) B3709835
theorem B2473259 : Blo 1648023 2473259 := bstep (se 1 (by rfl) ⟨1854944, by rfl⟩ : syracuseStep 2473259 = 3709889) B3709889
theorem B3710267 : Blo 1648023 3710267 := bstep (se 1 (by rfl) ⟨2782700, by rfl⟩ : syracuseStep 3710267 = 5565401) B5565401
theorem B2473289 : Blo 1648023 2473289 := bstep (se 2 (by rfl) ⟨927483, by rfl⟩ : syracuseStep 2473289 = 1854967) B1854967
theorem B3710393 : Blo 1648023 3710393 := bstep (se 2 (by rfl) ⟨1391397, by rfl⟩ : syracuseStep 3710393 = 2782795) B2782795
theorem B2473403 : Blo 1648023 2473403 := bstep (se 1 (by rfl) ⟨1855052, by rfl⟩ : syracuseStep 2473403 = 3710105) B3710105
theorem B3128777 : Blo 1648023 3128777 := bstep (se 2 (by rfl) ⟨1173291, by rfl⟩ : syracuseStep 3128777 = 2346583) B2346583
theorem B2473463 : Blo 1648023 2473463 := bstep (se 1 (by rfl) ⟨1855097, by rfl⟩ : syracuseStep 2473463 = 3710195) B3710195
theorem B1760783 : Blo 1648023 1760783 := bstep (se 1 (by rfl) ⟨1320587, by rfl⟩ : syracuseStep 1760783 = 2641175) B2641175
theorem B2473487 : Blo 1648023 2473487 := bstep (se 1 (by rfl) ⟨1855115, by rfl⟩ : syracuseStep 2473487 = 3710231) B3710231
theorem B2473529 : Blo 1648023 2473529 := bstep (se 2 (by rfl) ⟨927573, by rfl⟩ : syracuseStep 2473529 = 1855147) B1855147
theorem B4693565 : Blo 1648023 4693565 := bstep (se 3 (by rfl) ⟨880043, by rfl⟩ : syracuseStep 4693565 = 1760087) B1760087
theorem B2473607 : Blo 1648023 2473607 := bstep (se 1 (by rfl) ⟨1855205, by rfl⟩ : syracuseStep 2473607 = 3710411) B3710411
theorem B2473643 : Blo 1648023 2473643 := bstep (se 1 (by rfl) ⟨1855232, by rfl⟩ : syracuseStep 2473643 = 3710465) B3710465
theorem B2473673 : Blo 1648023 2473673 := bstep (se 2 (by rfl) ⟨927627, by rfl⟩ : syracuseStep 2473673 = 1855255) B1855255
theorem B8347373 : Blo 1648023 8347373 := bstep (se 3 (by rfl) ⟨1565132, by rfl⟩ : syracuseStep 8347373 = 3130265) B3130265
theorem B1761031 : Blo 1648023 1761031 := bstep (se 1 (by rfl) ⟨1320773, by rfl⟩ : syracuseStep 1761031 = 2641547) B2641547
theorem B3710735 : Blo 1648023 3710735 := bstep (se 1 (by rfl) ⟨2783051, by rfl⟩ : syracuseStep 3710735 = 5566103) B5566103
theorem B3710753 : Blo 1648023 3710753 := bstep (se 2 (by rfl) ⟨1391532, by rfl⟩ : syracuseStep 3710753 = 2783065) B2783065
theorem B14090021 : Blo 1648023 14090021 := bstep (se 4 (by rfl) ⟨1320939, by rfl⟩ : syracuseStep 14090021 = 2641879) B2641879
theorem B2506555 : Blo 1648023 2506555 := bstep (se 1 (by rfl) ⟨1879916, by rfl⟩ : syracuseStep 2506555 = 3759833) B3759833
theorem B2473787 : Blo 1648023 2473787 := bstep (se 1 (by rfl) ⟨1855340, by rfl⟩ : syracuseStep 2473787 = 3710681) B3710681
theorem B2473847 : Blo 1648023 2473847 := bstep (se 1 (by rfl) ⟨1855385, by rfl⟩ : syracuseStep 2473847 = 3710771) B3710771
theorem B4693895 : Blo 1648023 4693895 := bstep (se 1 (by rfl) ⟨3520421, by rfl⟩ : syracuseStep 4693895 = 7040843) B7040843
theorem B2473871 : Blo 1648023 2473871 := bstep (se 1 (by rfl) ⟨1855403, by rfl⟩ : syracuseStep 2473871 = 3710807) B3710807
theorem B6258617 : Blo 1648023 6258617 := bstep (se 2 (by rfl) ⟨2346981, by rfl⟩ : syracuseStep 6258617 = 4693963) B4693963
theorem B2473913 : Blo 1648023 2473913 := bstep (se 2 (by rfl) ⟨927717, by rfl⟩ : syracuseStep 2473913 = 1855435) B1855435
theorem B3915721 : Blo 1648023 3915721 := bstep (se 2 (by rfl) ⟨1468395, by rfl⟩ : syracuseStep 3915721 = 2936791) B2936791
theorem B1671247 : Blo 1648023 1671247 := bstep (se 1 (by rfl) ⟨1253435, by rfl⟩ : syracuseStep 1671247 = 2506871) B2506871
theorem B2474063 : Blo 1648023 2474063 := bstep (se 1 (by rfl) ⟨1855547, by rfl⟩ : syracuseStep 2474063 = 3711095) B3711095
theorem B5562539 : Blo 1648023 5562539 := bstep (se 1 (by rfl) ⟨4171904, by rfl⟩ : syracuseStep 5562539 = 8343809) B8343809
theorem B2474183 : Blo 1648023 2474183 := bstep (se 1 (by rfl) ⟨1855637, by rfl⟩ : syracuseStep 2474183 = 3711275) B3711275
theorem B3129673 : Blo 1648023 3129673 := bstep (se 2 (by rfl) ⟨1173627, by rfl⟩ : syracuseStep 3129673 = 2347255) B2347255
theorem B3342779 : Blo 1648023 3342779 := bstep (se 1 (by rfl) ⟨2507084, by rfl⟩ : syracuseStep 3342779 = 5014169) B5014169
theorem B8348345 : Blo 1648023 8348345 := bstep (se 2 (by rfl) ⟨3130629, by rfl⟩ : syracuseStep 8348345 = 6261259) B6261259
theorem B5563079 : Blo 1648023 5563079 := bstep (se 1 (by rfl) ⟨4172309, by rfl⟩ : syracuseStep 5563079 = 8344619) B8344619
theorem B22569931 : Blo 1648023 22569931 := bstep (se 1 (by rfl) ⟨16927448, by rfl⟩ : syracuseStep 22569931 = 33854897) B33854897
theorem B2229211 : Blo 1648023 2229211 := bstep (se 1 (by rfl) ⟨1671908, by rfl⟩ : syracuseStep 2229211 = 3343817) B3343817
theorem B10708163 : Blo 1648023 10708163 := bstep (se 1 (by rfl) ⟨8031122, by rfl⟩ : syracuseStep 10708163 = 16062245) B16062245
theorem B4695421 : Blo 1648023 4695421 := bstep (se 3 (by rfl) ⟨880391, by rfl⟩ : syracuseStep 4695421 = 1760783) B1760783
theorem B35661221 : Blo 1648023 35661221 := bstep (se 4 (by rfl) ⟨3343239, by rfl⟩ : syracuseStep 35661221 = 6686479) B6686479
theorem B1648047 : Blo 1648023 1648047 := bstep (se 1 (by rfl) ⟨1236035, by rfl⟩ : syracuseStep 1648047 = 2472071) B2472071
theorem B1648071 : Blo 1648023 1648071 := bstep (se 1 (by rfl) ⟨1236053, by rfl⟩ : syracuseStep 1648071 = 2472107) B2472107
theorem B1648091 : Blo 1648023 1648091 := bstep (se 1 (by rfl) ⟨1236068, by rfl⟩ : syracuseStep 1648091 = 2472137) B2472137
theorem B3171803 : Blo 1648023 3171803 := bstep (se 1 (by rfl) ⟨2378852, by rfl⟩ : syracuseStep 3171803 = 4757705) B4757705
theorem B1648167 : Blo 1648023 1648167 := bstep (se 1 (by rfl) ⟨1236125, by rfl⟩ : syracuseStep 1648167 = 2472251) B2472251
theorem B5563943 : Blo 1648023 5563943 := bstep (se 1 (by rfl) ⟨4172957, by rfl⟩ : syracuseStep 5563943 = 8345915) B8345915
theorem B1648207 : Blo 1648023 1648207 := bstep (se 1 (by rfl) ⟨1236155, by rfl⟩ : syracuseStep 1648207 = 2472311) B2472311
theorem B1648223 : Blo 1648023 1648223 := bstep (se 1 (by rfl) ⟨1236167, by rfl⟩ : syracuseStep 1648223 = 2472335) B2472335
theorem B11888225 : Blo 1648023 11888225 := bstep (se 2 (by rfl) ⟨4458084, by rfl⟩ : syracuseStep 11888225 = 8916169) B8916169
theorem B1648251 : Blo 1648023 1648251 := bstep (se 1 (by rfl) ⟨1236188, by rfl⟩ : syracuseStep 1648251 = 2472377) B2472377
theorem B50742929 : Blo 1648023 50742929 := bstep (se 2 (by rfl) ⟨19028598, by rfl⟩ : syracuseStep 50742929 = 38057197) B38057197
theorem B5940883 : Blo 1648023 5940883 := bstep (se 1 (by rfl) ⟨4455662, by rfl⟩ : syracuseStep 5940883 = 8911325) B8911325
theorem B5564051 : Blo 1648023 5564051 := bstep (se 1 (by rfl) ⟨4173038, by rfl⟩ : syracuseStep 5564051 = 8346077) B8346077
theorem B38078099 : Blo 1648023 38078099 := bstep (se 1 (by rfl) ⟨28558574, by rfl⟩ : syracuseStep 38078099 = 57117149) B57117149
theorem B1648303 : Blo 1648023 1648303 := bstep (se 1 (by rfl) ⟨1236227, by rfl⟩ : syracuseStep 1648303 = 2472455) B2472455
theorem B1648327 : Blo 1648023 1648327 := bstep (se 1 (by rfl) ⟨1236245, by rfl⟩ : syracuseStep 1648327 = 2472491) B2472491
theorem B1648347 : Blo 1648023 1648347 := bstep (se 1 (by rfl) ⟨1236260, by rfl⟩ : syracuseStep 1648347 = 2472521) B2472521
theorem B1648423 : Blo 1648023 1648423 := bstep (se 1 (by rfl) ⟨1236317, by rfl⟩ : syracuseStep 1648423 = 2472635) B2472635
theorem B91457333 : Blo 1648023 91457333 := bstep (se 5 (by rfl) ⟨4287062, by rfl⟩ : syracuseStep 91457333 = 8574125) B8574125
theorem B22570811 : Blo 1648023 22570811 := bstep (se 1 (by rfl) ⟨16928108, by rfl⟩ : syracuseStep 22570811 = 33856217) B33856217
theorem B1648463 : Blo 1648023 1648463 := bstep (se 1 (by rfl) ⟨1236347, by rfl⟩ : syracuseStep 1648463 = 2472695) B2472695
theorem B1648479 : Blo 1648023 1648479 := bstep (se 1 (by rfl) ⟨1236359, by rfl⟩ : syracuseStep 1648479 = 2472719) B2472719
theorem B5564267 : Blo 1648023 5564267 := bstep (se 1 (by rfl) ⟨4173200, by rfl⟩ : syracuseStep 5564267 = 8346401) B8346401
theorem B1648507 : Blo 1648023 1648507 := bstep (se 1 (by rfl) ⟨1236380, by rfl⟩ : syracuseStep 1648507 = 2472761) B2472761
theorem B5564321 : Blo 1648023 5564321 := bstep (se 2 (by rfl) ⟨2086620, by rfl⟩ : syracuseStep 5564321 = 4173241) B4173241
theorem B1648559 : Blo 1648023 1648559 := bstep (se 1 (by rfl) ⟨1236419, by rfl⟩ : syracuseStep 1648559 = 2472839) B2472839
theorem B1648583 : Blo 1648023 1648583 := bstep (se 1 (by rfl) ⟨1236437, by rfl⟩ : syracuseStep 1648583 = 2472875) B2472875
theorem B1648603 : Blo 1648023 1648603 := bstep (se 1 (by rfl) ⟨1236452, by rfl⟩ : syracuseStep 1648603 = 2472905) B2472905
theorem B4171783 : Blo 1648023 4171783 := bstep (se 1 (by rfl) ⟨3128837, by rfl⟩ : syracuseStep 4171783 = 6257675) B6257675
theorem B1648679 : Blo 1648023 1648679 := bstep (se 1 (by rfl) ⟨1236509, by rfl⟩ : syracuseStep 1648679 = 2473019) B2473019
theorem B1648719 : Blo 1648023 1648719 := bstep (se 1 (by rfl) ⟨1236539, by rfl⟩ : syracuseStep 1648719 = 2473079) B2473079
theorem B1648735 : Blo 1648023 1648735 := bstep (se 1 (by rfl) ⟨1236551, by rfl⟩ : syracuseStep 1648735 = 2473103) B2473103
theorem B1648763 : Blo 1648023 1648763 := bstep (se 1 (by rfl) ⟨1236572, by rfl⟩ : syracuseStep 1648763 = 2473145) B2473145
theorem B1648815 : Blo 1648023 1648815 := bstep (se 1 (by rfl) ⟨1236611, by rfl⟩ : syracuseStep 1648815 = 2473223) B2473223
theorem B1648839 : Blo 1648023 1648839 := bstep (se 1 (by rfl) ⟨1236629, by rfl⟩ : syracuseStep 1648839 = 2473259) B2473259
theorem B1648859 : Blo 1648023 1648859 := bstep (se 1 (by rfl) ⟨1236644, by rfl⟩ : syracuseStep 1648859 = 2473289) B2473289
theorem B1648935 : Blo 1648023 1648935 := bstep (se 1 (by rfl) ⟨1236701, by rfl⟩ : syracuseStep 1648935 = 2473403) B2473403
theorem B1648975 : Blo 1648023 1648975 := bstep (se 1 (by rfl) ⟨1236731, by rfl⟩ : syracuseStep 1648975 = 2473463) B2473463
theorem B1648991 : Blo 1648023 1648991 := bstep (se 1 (by rfl) ⟨1236743, by rfl⟩ : syracuseStep 1648991 = 2473487) B2473487
theorem B2640233 : Blo 1648023 2640233 := bstep (se 2 (by rfl) ⟨990087, by rfl⟩ : syracuseStep 2640233 = 1980175) B1980175
theorem B1649019 : Blo 1648023 1649019 := bstep (se 1 (by rfl) ⟨1236764, by rfl⟩ : syracuseStep 1649019 = 2473529) B2473529
theorem B20883845 : Blo 1648023 20883845 := bstep (se 4 (by rfl) ⟨1957860, by rfl⟩ : syracuseStep 20883845 = 3915721) B3915721
theorem B1649071 : Blo 1648023 1649071 := bstep (se 1 (by rfl) ⟨1236803, by rfl⟩ : syracuseStep 1649071 = 2473607) B2473607
theorem B1649095 : Blo 1648023 1649095 := bstep (se 1 (by rfl) ⟨1236821, by rfl⟩ : syracuseStep 1649095 = 2473643) B2473643
theorem B1649115 : Blo 1648023 1649115 := bstep (se 1 (by rfl) ⟨1236836, by rfl⟩ : syracuseStep 1649115 = 2473673) B2473673
theorem B5564915 : Blo 1648023 5564915 := bstep (se 1 (by rfl) ⟨4173686, by rfl⟩ : syracuseStep 5564915 = 8347373) B8347373
theorem B1649191 : Blo 1648023 1649191 := bstep (se 1 (by rfl) ⟨1236893, by rfl⟩ : syracuseStep 1649191 = 2473787) B2473787
theorem B1854031 : Blo 1648023 1854031 := bstep (se 1 (by rfl) ⟨1390523, by rfl⟩ : syracuseStep 1854031 = 2781047) B2781047
theorem B1649231 : Blo 1648023 1649231 := bstep (se 1 (by rfl) ⟨1236923, by rfl⟩ : syracuseStep 1649231 = 2473847) B2473847
theorem B1649247 : Blo 1648023 1649247 := bstep (se 1 (by rfl) ⟨1236935, by rfl⟩ : syracuseStep 1649247 = 2473871) B2473871
theorem B4229729 : Blo 1648023 4229729 := bstep (se 2 (by rfl) ⟨1586148, by rfl⟩ : syracuseStep 4229729 = 3172297) B3172297
theorem B4172411 : Blo 1648023 4172411 := bstep (se 1 (by rfl) ⟨3129308, by rfl⟩ : syracuseStep 4172411 = 6258617) B6258617
theorem B1649275 : Blo 1648023 1649275 := bstep (se 1 (by rfl) ⟨1236956, by rfl⟩ : syracuseStep 1649275 = 2473913) B2473913
theorem B1649327 : Blo 1648023 1649327 := bstep (se 1 (by rfl) ⟨1236995, by rfl⟩ : syracuseStep 1649327 = 2473991) B2473991
theorem B1649351 : Blo 1648023 1649351 := bstep (se 1 (by rfl) ⟨1237013, by rfl⟩ : syracuseStep 1649351 = 2474027) B2474027
theorem B5638871 : Blo 1648023 5638871 := bstep (se 1 (by rfl) ⟨4229153, by rfl⟩ : syracuseStep 5638871 = 8458307) B8458307
theorem B1649371 : Blo 1648023 1649371 := bstep (se 1 (by rfl) ⟨1237028, by rfl⟩ : syracuseStep 1649371 = 2474057) B2474057
theorem B6261533 : Blo 1648023 6261533 := bstep (se 3 (by rfl) ⟨1174037, by rfl⟩ : syracuseStep 6261533 = 2348075) B2348075
theorem B1649447 : Blo 1648023 1649447 := bstep (se 1 (by rfl) ⟨1237085, by rfl⟩ : syracuseStep 1649447 = 2474171) B2474171
theorem B7039817 : Blo 1648023 7039817 := bstep (se 2 (by rfl) ⟨2639931, by rfl⟩ : syracuseStep 7039817 = 5279863) B5279863
theorem B1649487 : Blo 1648023 1649487 := bstep (se 1 (by rfl) ⟨1237115, by rfl⟩ : syracuseStep 1649487 = 2474231) B2474231
theorem B1649503 : Blo 1648023 1649503 := bstep (se 1 (by rfl) ⟨1237127, by rfl⟩ : syracuseStep 1649503 = 2474255) B2474255
theorem B594348947 : Blo 1648023 594348947 := bstep (se 1 (by rfl) ⟨445761710, by rfl⟩ : syracuseStep 594348947 = 891523421) B891523421
theorem B4172705 : Blo 1648023 4172705 := bstep (se 2 (by rfl) ⟨1564764, by rfl⟩ : syracuseStep 4172705 = 3129529) B3129529
theorem B1854427 : Blo 1648023 1854427 := bstep (se 1 (by rfl) ⟨1390820, by rfl⟩ : syracuseStep 1854427 = 2781641) B2781641
theorem B5565455 : Blo 1648023 5565455 := bstep (se 1 (by rfl) ⟨4174091, by rfl⟩ : syracuseStep 5565455 = 8348183) B8348183
theorem B3386617 : Blo 1648023 3386617 := bstep (se 2 (by rfl) ⟨1269981, by rfl⟩ : syracuseStep 3386617 = 2539963) B2539963
theorem B8916389 : Blo 1648023 8916389 := bstep (se 4 (by rfl) ⟨835911, by rfl⟩ : syracuseStep 8916389 = 1671823) B1671823
theorem B1854895 : Blo 1648023 1854895 := bstep (se 1 (by rfl) ⟨1391171, by rfl⟩ : syracuseStep 1854895 = 2782343) B2782343
theorem B5942729 : Blo 1648023 5942729 := bstep (se 2 (by rfl) ⟨2228523, by rfl⟩ : syracuseStep 5942729 = 4457047) B4457047
theorem B6262217 : Blo 1648023 6262217 := bstep (se 2 (by rfl) ⟨2348331, by rfl⟩ : syracuseStep 6262217 = 4696663) B4696663
theorem B5566049 : Blo 1648023 5566049 := bstep (se 2 (by rfl) ⟨2087268, by rfl⟩ : syracuseStep 5566049 = 4174537) B4174537
theorem B15044285 : Blo 1648023 15044285 := bstep (se 3 (by rfl) ⟨2820803, by rfl⟩ : syracuseStep 15044285 = 5641607) B5641607
theorem B28159811 : Blo 1648023 28159811 := bstep (se 1 (by rfl) ⟨21119858, by rfl⟩ : syracuseStep 28159811 = 42239717) B42239717
theorem B1855327 : Blo 1648023 1855327 := bstep (se 1 (by rfl) ⟨1391495, by rfl⟩ : syracuseStep 1855327 = 2782991) B2782991
theorem B2641771 : Blo 1648023 2641771 := bstep (se 1 (by rfl) ⟨1981328, by rfl⟩ : syracuseStep 2641771 = 3962657) B3962657
theorem B6262703 : Blo 1648023 6262703 := bstep (se 1 (by rfl) ⟨4697027, by rfl⟩ : syracuseStep 6262703 = 9394055) B9394055
theorem B2781263 : Blo 1648023 2781263 := bstep (se 1 (by rfl) ⟨2085947, by rfl⟩ : syracuseStep 2781263 = 4171895) B4171895
theorem B1880263 : Blo 1648023 1880263 := bstep (se 1 (by rfl) ⟨1410197, by rfl⟩ : syracuseStep 1880263 = 2820395) B2820395
theorem B1855687 : Blo 1648023 1855687 := bstep (se 1 (by rfl) ⟨1391765, by rfl⟩ : syracuseStep 1855687 = 2783531) B2783531
theorem B12521789 : Blo 1648023 12521789 := bstep (se 3 (by rfl) ⟨2347835, by rfl⟩ : syracuseStep 12521789 = 4695671) B4695671
theorem B4518287 : Blo 1648023 4518287 := bstep (se 1 (by rfl) ⟨3388715, by rfl⟩ : syracuseStep 4518287 = 6777431) B6777431
theorem B2347483 : Blo 1648023 2347483 := bstep (se 1 (by rfl) ⟨1760612, by rfl⟩ : syracuseStep 2347483 = 3521225) B3521225
theorem B5354009 : Blo 1648023 5354009 := bstep (se 2 (by rfl) ⟨2007753, by rfl⟩ : syracuseStep 5354009 = 4015507) B4015507
theorem B4174375 : Blo 1648023 4174375 := bstep (se 1 (by rfl) ⟨3130781, by rfl⟩ : syracuseStep 4174375 = 6261563) B6261563
theorem B7926407 : Blo 1648023 7926407 := bstep (se 1 (by rfl) ⟨5944805, by rfl⟩ : syracuseStep 7926407 = 11889611) B11889611
theorem B4174699 : Blo 1648023 4174699 := bstep (se 1 (by rfl) ⟨3131024, by rfl⟩ : syracuseStep 4174699 = 6262049) B6262049
theorem B2782127 : Blo 1648023 2782127 := bstep (se 1 (by rfl) ⟨2086595, by rfl⟩ : syracuseStep 2782127 = 4173191) B4173191
theorem B2085851 : Blo 1648023 2085851 := bstep (se 1 (by rfl) ⟨1564388, by rfl⟩ : syracuseStep 2085851 = 3128777) B3128777
theorem B2348041 : Blo 1648023 2348041 := bstep (se 2 (by rfl) ⟨880515, by rfl⟩ : syracuseStep 2348041 = 1761031) B1761031
theorem B26735665 : Blo 1648023 26735665 := bstep (se 2 (by rfl) ⟨10025874, by rfl⟩ : syracuseStep 26735665 = 20051749) B20051749
theorem B9393347 : Blo 1648023 9393347 := bstep (se 1 (by rfl) ⟨7045010, by rfl⟩ : syracuseStep 9393347 = 14090021) B14090021
theorem B2782559 : Blo 1648023 2782559 := bstep (se 1 (by rfl) ⟨2086919, by rfl⟩ : syracuseStep 2782559 = 4173839) B4173839
theorem B4068713 : Blo 1648023 4068713 := bstep (se 2 (by rfl) ⟨1525767, by rfl⟩ : syracuseStep 4068713 = 3051535) B3051535
theorem B2086327 : Blo 1648023 2086327 := bstep (se 1 (by rfl) ⟨1564745, by rfl⟩ : syracuseStep 2086327 = 3129491) B3129491
theorem B4175347 : Blo 1648023 4175347 := bstep (se 1 (by rfl) ⟨3131510, by rfl⟩ : syracuseStep 4175347 = 6263021) B6263021
theorem B23770685 : Blo 1648023 23770685 := bstep (se 3 (by rfl) ⟨4457003, by rfl⟩ : syracuseStep 23770685 = 8914007) B8914007
theorem B3708539 : Blo 1648023 3708539 := bstep (se 1 (by rfl) ⟨2781404, by rfl⟩ : syracuseStep 3708539 = 5562809) B5562809
theorem B4519547 : Blo 1648023 4519547 := bstep (se 1 (by rfl) ⟨3389660, by rfl⟩ : syracuseStep 4519547 = 6779321) B6779321
theorem B9393803 : Blo 1648023 9393803 := bstep (se 1 (by rfl) ⟨7045352, by rfl⟩ : syracuseStep 9393803 = 14090705) B14090705
theorem B3520199 : Blo 1648023 3520199 := bstep (se 1 (by rfl) ⟨2640149, by rfl⟩ : syracuseStep 3520199 = 5280299) B5280299
theorem B3708665 : Blo 1648023 3708665 := bstep (se 2 (by rfl) ⟨1390749, by rfl⟩ : syracuseStep 3708665 = 2781499) B2781499
theorem B7042859 : Blo 1648023 7042859 := bstep (se 1 (by rfl) ⟨5282144, by rfl⟩ : syracuseStep 7042859 = 10564289) B10564289
theorem B2783119 : Blo 1648023 2783119 := bstep (se 1 (by rfl) ⟨2087339, by rfl⟩ : syracuseStep 2783119 = 4174679) B4174679
theorem B47527883 : Blo 1648023 47527883 := bstep (se 1 (by rfl) ⟨35645912, by rfl⟩ : syracuseStep 47527883 = 71291825) B71291825
theorem B3708935 : Blo 1648023 3708935 := bstep (se 1 (by rfl) ⟨2781701, by rfl⟩ : syracuseStep 3708935 = 5563403) B5563403
theorem B5281811 : Blo 1648023 5281811 := bstep (se 1 (by rfl) ⟨3961358, by rfl⟩ : syracuseStep 5281811 = 7922717) B7922717
theorem B3709007 : Blo 1648023 3709007 := bstep (se 1 (by rfl) ⟨2781755, by rfl⟩ : syracuseStep 3709007 = 5563511) B5563511
theorem B2472059 : Blo 1648023 2472059 := bstep (se 1 (by rfl) ⟨1854044, by rfl⟩ : syracuseStep 2472059 = 3708089) B3708089
theorem B2676983 : Blo 1648023 2676983 := bstep (se 1 (by rfl) ⟨2007737, by rfl⟩ : syracuseStep 2676983 = 4015475) B4015475
theorem B3963127 : Blo 1648023 3963127 := bstep (se 1 (by rfl) ⟨2972345, by rfl⟩ : syracuseStep 3963127 = 5944691) B5944691
theorem B2472185 : Blo 1648023 2472185 := bstep (se 2 (by rfl) ⟨927069, by rfl⟩ : syracuseStep 2472185 = 1854139) B1854139
theorem B2472287 : Blo 1648023 2472287 := bstep (se 1 (by rfl) ⟨1854215, by rfl⟩ : syracuseStep 2472287 = 3708431) B3708431
theorem B2472299 : Blo 1648023 2472299 := bstep (se 1 (by rfl) ⟨1854224, by rfl⟩ : syracuseStep 2472299 = 3708449) B3708449
theorem B22567301 : Blo 1648023 22567301 := bstep (se 4 (by rfl) ⟨2115684, by rfl⟩ : syracuseStep 22567301 = 4231369) B4231369
theorem B3258785 : Blo 1648023 3258785 := bstep (se 2 (by rfl) ⟨1222044, by rfl⟩ : syracuseStep 3258785 = 2444089) B2444089
theorem B3709403 : Blo 1648023 3709403 := bstep (se 1 (by rfl) ⟨2782052, by rfl⟩ : syracuseStep 3709403 = 5564105) B5564105
theorem B71301667 : Blo 1648023 71301667 := bstep (se 1 (by rfl) ⟨53476250, by rfl⟩ : syracuseStep 71301667 = 106952501) B106952501
theorem B3521063 : Blo 1648023 3521063 := bstep (se 1 (by rfl) ⟨2640797, by rfl⟩ : syracuseStep 3521063 = 5281595) B5281595
theorem B2472527 : Blo 1648023 2472527 := bstep (se 1 (by rfl) ⟨1854395, by rfl⟩ : syracuseStep 2472527 = 3708791) B3708791
theorem B8460935 : Blo 1648023 8460935 := bstep (se 1 (by rfl) ⟨6345701, by rfl⟩ : syracuseStep 8460935 = 12691403) B12691403
theorem B30497465 : Blo 1648023 30497465 := bstep (se 2 (by rfl) ⟨11436549, by rfl⟩ : syracuseStep 30497465 = 22873099) B22873099
theorem B2472647 : Blo 1648023 2472647 := bstep (se 1 (by rfl) ⟨1854485, by rfl⟩ : syracuseStep 2472647 = 3708971) B3708971
theorem B2087623 : Blo 1648023 2087623 := bstep (se 1 (by rfl) ⟨1565717, by rfl⟩ : syracuseStep 2087623 = 3131435) B3131435
theorem B2472809 : Blo 1648023 2472809 := bstep (se 2 (by rfl) ⟨927303, by rfl⟩ : syracuseStep 2472809 = 1854607) B1854607
theorem B3709871 : Blo 1648023 3709871 := bstep (se 1 (by rfl) ⟨2782403, by rfl⟩ : syracuseStep 3709871 = 5564807) B5564807
theorem B2472887 : Blo 1648023 2472887 := bstep (se 1 (by rfl) ⟨1854665, by rfl⟩ : syracuseStep 2472887 = 3709331) B3709331
theorem B2472923 : Blo 1648023 2472923 := bstep (se 1 (by rfl) ⟨1854692, by rfl⟩ : syracuseStep 2472923 = 3709385) B3709385
theorem B3710123 : Blo 1648023 3710123 := bstep (se 1 (by rfl) ⟨2782592, by rfl⟩ : syracuseStep 3710123 = 5565185) B5565185
theorem B2473391 : Blo 1648023 2473391 := bstep (se 1 (by rfl) ⟨1855043, by rfl⟩ : syracuseStep 2473391 = 3710087) B3710087
theorem B2473481 : Blo 1648023 2473481 := bstep (se 2 (by rfl) ⟨927555, by rfl⟩ : syracuseStep 2473481 = 1855111) B1855111
theorem B2473511 : Blo 1648023 2473511 := bstep (se 1 (by rfl) ⟨1855133, by rfl⟩ : syracuseStep 2473511 = 3710267) B3710267
theorem B2473595 : Blo 1648023 2473595 := bstep (se 1 (by rfl) ⟨1855196, by rfl⟩ : syracuseStep 2473595 = 3710393) B3710393
theorem B13557395 : Blo 1648023 13557395 := bstep (se 1 (by rfl) ⟨10168046, by rfl⟩ : syracuseStep 13557395 = 20336093) B20336093
theorem B3710663 : Blo 1648023 3710663 := bstep (se 1 (by rfl) ⟨2782997, by rfl⟩ : syracuseStep 3710663 = 5565995) B5565995
theorem B3129043 : Blo 1648023 3129043 := bstep (se 1 (by rfl) ⟨2346782, by rfl⟩ : syracuseStep 3129043 = 4693565) B4693565
theorem B3342073 : Blo 1648023 3342073 := bstep (se 2 (by rfl) ⟨1253277, by rfl⟩ : syracuseStep 3342073 = 2506555) B2506555
theorem B2473721 : Blo 1648023 2473721 := bstep (se 2 (by rfl) ⟨927645, by rfl⟩ : syracuseStep 2473721 = 1855291) B1855291
theorem B2473823 : Blo 1648023 2473823 := bstep (se 1 (by rfl) ⟨1855367, by rfl⟩ : syracuseStep 2473823 = 3710735) B3710735
theorem B2473835 : Blo 1648023 2473835 := bstep (se 1 (by rfl) ⟨1855376, by rfl⟩ : syracuseStep 2473835 = 3710753) B3710753
theorem B3129263 : Blo 1648023 3129263 := bstep (se 1 (by rfl) ⟨2346947, by rfl⟩ : syracuseStep 3129263 = 4693895) B4693895
theorem B5562377 : Blo 1648023 5562377 := bstep (se 2 (by rfl) ⟨2085891, by rfl⟩ : syracuseStep 5562377 = 4171783) B4171783
theorem B2228329 : Blo 1648023 2228329 := bstep (se 2 (by rfl) ⟨835623, by rfl⟩ : syracuseStep 2228329 = 1671247) B1671247
theorem B8347859 : Blo 1648023 8347859 := bstep (se 1 (by rfl) ⟨6260894, by rfl⟩ : syracuseStep 8347859 = 12521789) B12521789
theorem B2474249 : Blo 1648023 2474249 := bstep (se 2 (by rfl) ⟨927843, by rfl⟩ : syracuseStep 2474249 = 1855687) B1855687
theorem B2228519 : Blo 1648023 2228519 := bstep (se 1 (by rfl) ⟨1671389, by rfl⟩ : syracuseStep 2228519 = 3342779) B3342779
theorem B5284169 : Blo 1648023 5284169 := bstep (se 2 (by rfl) ⟨1981563, by rfl⟩ : syracuseStep 5284169 = 3963127) B3963127
theorem B5284271 : Blo 1648023 5284271 := bstep (se 1 (by rfl) ⟨3963203, by rfl⟩ : syracuseStep 5284271 = 7926407) B7926407
theorem B3129977 : Blo 1648023 3129977 := bstep (se 2 (by rfl) ⟨1173741, by rfl⟩ : syracuseStep 3129977 = 2347483) B2347483
theorem B95068889 : Blo 1648023 95068889 := bstep (se 2 (by rfl) ⟨35650833, by rfl⟩ : syracuseStep 95068889 = 71301667) B71301667
theorem B2712475 : Blo 1648023 2712475 := bstep (se 1 (by rfl) ⟨2034356, by rfl⟩ : syracuseStep 2712475 = 4068713) B4068713
theorem B23774147 : Blo 1648023 23774147 := bstep (se 1 (by rfl) ⟨17830610, by rfl⟩ : syracuseStep 23774147 = 35661221) B35661221
theorem B10028069 : Blo 1648023 10028069 := bstep (se 4 (by rfl) ⟨940131, by rfl⟩ : syracuseStep 10028069 = 1880263) B1880263
theorem B4695239 : Blo 1648023 4695239 := bstep (se 1 (by rfl) ⟨3521429, by rfl⟩ : syracuseStep 4695239 = 7042859) B7042859
theorem B3130721 : Blo 1648023 3130721 := bstep (se 2 (by rfl) ⟨1174020, by rfl⟩ : syracuseStep 3130721 = 2348041) B2348041
theorem B1648039 : Blo 1648023 1648039 := bstep (se 1 (by rfl) ⟨1236029, by rfl⟩ : syracuseStep 1648039 = 2472059) B2472059
theorem B1648123 : Blo 1648023 1648123 := bstep (se 1 (by rfl) ⟨1236092, by rfl⟩ : syracuseStep 1648123 = 2472185) B2472185
theorem B1648191 : Blo 1648023 1648191 := bstep (se 1 (by rfl) ⟨1236143, by rfl⟩ : syracuseStep 1648191 = 2472287) B2472287
theorem B1648199 : Blo 1648023 1648199 := bstep (se 1 (by rfl) ⟨1236149, by rfl⟩ : syracuseStep 1648199 = 2472299) B2472299
theorem B2172523 : Blo 1648023 2172523 := bstep (se 1 (by rfl) ⟨1629392, by rfl⟩ : syracuseStep 2172523 = 3258785) B3258785
theorem B1648351 : Blo 1648023 1648351 := bstep (se 1 (by rfl) ⟨1236263, by rfl⟩ : syracuseStep 1648351 = 2472527) B2472527
theorem B2819819 : Blo 1648023 2819819 := bstep (se 1 (by rfl) ⟨2114864, by rfl⟩ : syracuseStep 2819819 = 4229729) B4229729
theorem B1648431 : Blo 1648023 1648431 := bstep (se 1 (by rfl) ⟨1236323, by rfl⟩ : syracuseStep 1648431 = 2472647) B2472647
theorem B6260561 : Blo 1648023 6260561 := bstep (se 2 (by rfl) ⟨2347710, by rfl⟩ : syracuseStep 6260561 = 4695421) B4695421
theorem B1648539 : Blo 1648023 1648539 := bstep (se 1 (by rfl) ⟨1236404, by rfl⟩ : syracuseStep 1648539 = 2472809) B2472809
theorem B396232631 : Blo 1648023 396232631 := bstep (se 1 (by rfl) ⟨297174473, by rfl⟩ : syracuseStep 396232631 = 594348947) B594348947
theorem B1648591 : Blo 1648023 1648591 := bstep (se 1 (by rfl) ⟨1236443, by rfl⟩ : syracuseStep 1648591 = 2472887) B2472887
theorem B1648615 : Blo 1648023 1648615 := bstep (se 1 (by rfl) ⟨1236461, by rfl⟩ : syracuseStep 1648615 = 2472923) B2472923
theorem B4172057 : Blo 1648023 4172057 := bstep (se 2 (by rfl) ⟨1564521, by rfl⟩ : syracuseStep 4172057 = 3129043) B3129043
theorem B1648927 : Blo 1648023 1648927 := bstep (se 1 (by rfl) ⟨1236695, by rfl⟩ : syracuseStep 1648927 = 2473391) B2473391
theorem B1648987 : Blo 1648023 1648987 := bstep (se 1 (by rfl) ⟨1236740, by rfl⟩ : syracuseStep 1648987 = 2473481) B2473481
theorem B1649007 : Blo 1648023 1649007 := bstep (se 1 (by rfl) ⟨1236755, by rfl⟩ : syracuseStep 1649007 = 2473511) B2473511
theorem B1649063 : Blo 1648023 1649063 := bstep (se 1 (by rfl) ⟨1236797, by rfl⟩ : syracuseStep 1649063 = 2473595) B2473595
theorem B9038263 : Blo 1648023 9038263 := bstep (se 1 (by rfl) ⟨6778697, by rfl⟩ : syracuseStep 9038263 = 13557395) B13557395
theorem B10029523 : Blo 1648023 10029523 := bstep (se 1 (by rfl) ⟨7522142, by rfl⟩ : syracuseStep 10029523 = 15044285) B15044285
theorem B11889125 : Blo 1648023 11889125 := bstep (se 4 (by rfl) ⟨1114605, by rfl⟩ : syracuseStep 11889125 = 2229211) B2229211
theorem B1649147 : Blo 1648023 1649147 := bstep (se 1 (by rfl) ⟨1236860, by rfl⟩ : syracuseStep 1649147 = 2473721) B2473721
theorem B1649215 : Blo 1648023 1649215 := bstep (se 1 (by rfl) ⟨1236911, by rfl⟩ : syracuseStep 1649215 = 2473823) B2473823
theorem B1649223 : Blo 1648023 1649223 := bstep (se 1 (by rfl) ⟨1236917, by rfl⟩ : syracuseStep 1649223 = 2473835) B2473835
theorem B1854175 : Blo 1648023 1854175 := bstep (se 1 (by rfl) ⟨1390631, by rfl⟩ : syracuseStep 1854175 = 2781263) B2781263
theorem B1649375 : Blo 1648023 1649375 := bstep (se 1 (by rfl) ⟨1237031, by rfl⟩ : syracuseStep 1649375 = 2474063) B2474063
theorem B1649455 : Blo 1648023 1649455 := bstep (se 1 (by rfl) ⟨1237091, by rfl⟩ : syracuseStep 1649455 = 2474183) B2474183
theorem B4172897 : Blo 1648023 4172897 := bstep (se 2 (by rfl) ⟨1564836, by rfl⟩ : syracuseStep 4172897 = 3129673) B3129673
theorem B5565563 : Blo 1648023 5565563 := bstep (se 1 (by rfl) ⟨4174172, by rfl⟩ : syracuseStep 5565563 = 8348345) B8348345
theorem B1854751 : Blo 1648023 1854751 := bstep (se 1 (by rfl) ⟨1391063, by rfl⟩ : syracuseStep 1854751 = 2782127) B2782127
theorem B7138621 : Blo 1648023 7138621 := bstep (se 3 (by rfl) ⟨1338491, by rfl⟩ : syracuseStep 7138621 = 2676983) B2676983
theorem B5565833 : Blo 1648023 5565833 := bstep (se 2 (by rfl) ⟨2087187, by rfl⟩ : syracuseStep 5565833 = 4174375) B4174375
theorem B7138775 : Blo 1648023 7138775 := bstep (se 1 (by rfl) ⟨5354081, by rfl⟩ : syracuseStep 7138775 = 10708163) B10708163
theorem B6262231 : Blo 1648023 6262231 := bstep (se 1 (by rfl) ⟨4696673, by rfl⟩ : syracuseStep 6262231 = 9393347) B9393347
theorem B1855039 : Blo 1648023 1855039 := bstep (se 1 (by rfl) ⟨1391279, by rfl⟩ : syracuseStep 1855039 = 2782559) B2782559
theorem B7040621 : Blo 1648023 7040621 := bstep (se 3 (by rfl) ⟨1320116, by rfl⟩ : syracuseStep 7040621 = 2640233) B2640233
theorem B15847123 : Blo 1648023 15847123 := bstep (se 1 (by rfl) ⟨11885342, by rfl⟩ : syracuseStep 15847123 = 23770685) B23770685
theorem B7925483 : Blo 1648023 7925483 := bstep (se 1 (by rfl) ⟨5944112, by rfl⟩ : syracuseStep 7925483 = 11888225) B11888225
theorem B6262535 : Blo 1648023 6262535 := bstep (se 1 (by rfl) ⟨4696901, by rfl⟩ : syracuseStep 6262535 = 9393803) B9393803
theorem B33828619 : Blo 1648023 33828619 := bstep (se 1 (by rfl) ⟨25371464, by rfl⟩ : syracuseStep 33828619 = 50742929) B50742929
theorem B5566265 : Blo 1648023 5566265 := bstep (se 2 (by rfl) ⟨2087349, by rfl⟩ : syracuseStep 5566265 = 4174699) B4174699
theorem B8458141 : Blo 1648023 8458141 := bstep (se 3 (by rfl) ⟨1585901, by rfl⟩ : syracuseStep 8458141 = 3171803) B3171803
theorem B30093241 : Blo 1648023 30093241 := bstep (se 2 (by rfl) ⟨11284965, by rfl⟩ : syracuseStep 30093241 = 22569931) B22569931
theorem B35647553 : Blo 1648023 35647553 := bstep (se 2 (by rfl) ⟨13367832, by rfl⟩ : syracuseStep 35647553 = 26735665) B26735665
theorem B13922563 : Blo 1648023 13922563 := bstep (se 1 (by rfl) ⟨10441922, by rfl⟩ : syracuseStep 13922563 = 20883845) B20883845
theorem B15044867 : Blo 1648023 15044867 := bstep (se 1 (by rfl) ⟨11283650, by rfl⟩ : syracuseStep 15044867 = 22567301) B22567301
theorem B2347375 : Blo 1648023 2347375 := bstep (se 1 (by rfl) ⟨1760531, by rfl⟩ : syracuseStep 2347375 = 3521063) B3521063
theorem B2781607 : Blo 1648023 2781607 := bstep (se 1 (by rfl) ⟨2086205, by rfl⟩ : syracuseStep 2781607 = 4172411) B4172411
theorem B5640623 : Blo 1648023 5640623 := bstep (se 1 (by rfl) ⟨4230467, by rfl⟩ : syracuseStep 5640623 = 8460935) B8460935
theorem B4174355 : Blo 1648023 4174355 := bstep (se 1 (by rfl) ⟨3130766, by rfl⟩ : syracuseStep 4174355 = 6261533) B6261533
theorem B2781769 : Blo 1648023 2781769 := bstep (se 2 (by rfl) ⟨1043163, by rfl⟩ : syracuseStep 2781769 = 2086327) B2086327
theorem B2781803 : Blo 1648023 2781803 := bstep (se 1 (by rfl) ⟨2086352, by rfl⟩ : syracuseStep 2781803 = 4172705) B4172705
theorem B5567129 : Blo 1648023 5567129 := bstep (se 2 (by rfl) ⟨2087673, by rfl⟩ : syracuseStep 5567129 = 4175347) B4175347
theorem B5944259 : Blo 1648023 5944259 := bstep (se 1 (by rfl) ⟨4458194, by rfl⟩ : syracuseStep 5944259 = 8916389) B8916389
theorem B3961819 : Blo 1648023 3961819 := bstep (se 1 (by rfl) ⟨2971364, by rfl⟩ : syracuseStep 3961819 = 5942729) B5942729
theorem B4174811 : Blo 1648023 4174811 := bstep (se 1 (by rfl) ⟨3131108, by rfl⟩ : syracuseStep 4174811 = 6262217) B6262217
theorem B18773207 : Blo 1648023 18773207 := bstep (se 1 (by rfl) ⟨14079905, by rfl⟩ : syracuseStep 18773207 = 28159811) B28159811
theorem B2086175 : Blo 1648023 2086175 := bstep (se 1 (by rfl) ⟨1564631, by rfl⟩ : syracuseStep 2086175 = 3129263) B3129263
theorem B4175135 : Blo 1648023 4175135 := bstep (se 1 (by rfl) ⟨3131351, by rfl⟩ : syracuseStep 4175135 = 6262703) B6262703
theorem B3708359 : Blo 1648023 3708359 := bstep (se 1 (by rfl) ⟨2781269, by rfl⟩ : syracuseStep 3708359 = 5562539) B5562539
theorem B3012191 : Blo 1648023 3012191 := bstep (se 1 (by rfl) ⟨2259143, by rfl⟩ : syracuseStep 3012191 = 4518287) B4518287
theorem B3569339 : Blo 1648023 3569339 := bstep (se 1 (by rfl) ⟨2677004, by rfl⟩ : syracuseStep 3569339 = 5354009) B5354009
theorem B3708719 : Blo 1648023 3708719 := bstep (se 1 (by rfl) ⟨2781539, by rfl⟩ : syracuseStep 3708719 = 5563079) B5563079
theorem B31684709 : Blo 1648023 31684709 := bstep (se 4 (by rfl) ⟨2970441, by rfl⟩ : syracuseStep 31684709 = 5940883) B5940883
theorem B2472041 : Blo 1648023 2472041 := bstep (se 2 (by rfl) ⟨927015, by rfl⟩ : syracuseStep 2472041 = 1854031) B1854031
theorem B2783497 : Blo 1648023 2783497 := bstep (se 2 (by rfl) ⟨1043811, by rfl⟩ : syracuseStep 2783497 = 2087623) B2087623
theorem B3709295 : Blo 1648023 3709295 := bstep (se 1 (by rfl) ⟨2781971, by rfl⟩ : syracuseStep 3709295 = 5563943) B5563943
theorem B2472359 : Blo 1648023 2472359 := bstep (se 1 (by rfl) ⟨1854269, by rfl⟩ : syracuseStep 2472359 = 3708539) B3708539
theorem B3013031 : Blo 1648023 3013031 := bstep (se 1 (by rfl) ⟨2259773, by rfl⟩ : syracuseStep 3013031 = 4519547) B4519547
theorem B3709367 : Blo 1648023 3709367 := bstep (se 1 (by rfl) ⟨2782025, by rfl⟩ : syracuseStep 3709367 = 5564051) B5564051
theorem B25385399 : Blo 1648023 25385399 := bstep (se 1 (by rfl) ⟨19039049, by rfl⟩ : syracuseStep 25385399 = 38078099) B38078099
theorem B2472443 : Blo 1648023 2472443 := bstep (se 1 (by rfl) ⟨1854332, by rfl⟩ : syracuseStep 2472443 = 3708665) B3708665
theorem B60971555 : Blo 1648023 60971555 := bstep (se 1 (by rfl) ⟨45728666, by rfl⟩ : syracuseStep 60971555 = 91457333) B91457333
theorem B15047207 : Blo 1648023 15047207 := bstep (se 1 (by rfl) ⟨11285405, by rfl⟩ : syracuseStep 15047207 = 22570811) B22570811
theorem B3709511 : Blo 1648023 3709511 := bstep (se 1 (by rfl) ⟨2782133, by rfl⟩ : syracuseStep 3709511 = 5564267) B5564267
theorem B3709547 : Blo 1648023 3709547 := bstep (se 1 (by rfl) ⟨2782160, by rfl⟩ : syracuseStep 3709547 = 5564321) B5564321
theorem B2472569 : Blo 1648023 2472569 := bstep (se 2 (by rfl) ⟨927213, by rfl⟩ : syracuseStep 2472569 = 1854427) B1854427
theorem B18061957 : Blo 1648023 18061957 := bstep (se 4 (by rfl) ⟨1693308, by rfl⟩ : syracuseStep 18061957 = 3386617) B3386617
theorem B31685255 : Blo 1648023 31685255 := bstep (se 1 (by rfl) ⟨23763941, by rfl⟩ : syracuseStep 31685255 = 47527883) B47527883
theorem B2472623 : Blo 1648023 2472623 := bstep (se 1 (by rfl) ⟨1854467, by rfl⟩ : syracuseStep 2472623 = 3708935) B3708935
theorem B3521207 : Blo 1648023 3521207 := bstep (se 1 (by rfl) ⟨2640905, by rfl⟩ : syracuseStep 3521207 = 5281811) B5281811
theorem B2472671 : Blo 1648023 2472671 := bstep (se 1 (by rfl) ⟨1854503, by rfl⟩ : syracuseStep 2472671 = 3709007) B3709007
theorem B2472935 : Blo 1648023 2472935 := bstep (se 1 (by rfl) ⟨1854701, by rfl⟩ : syracuseStep 2472935 = 3709403) B3709403
theorem B3709943 : Blo 1648023 3709943 := bstep (se 1 (by rfl) ⟨2782457, by rfl⟩ : syracuseStep 3709943 = 5564915) B5564915
theorem B20331643 : Blo 1648023 20331643 := bstep (se 1 (by rfl) ⟨15248732, by rfl⟩ : syracuseStep 20331643 = 30497465) B30497465
theorem B3759247 : Blo 1648023 3759247 := bstep (se 1 (by rfl) ⟨2819435, by rfl⟩ : syracuseStep 3759247 = 5638871) B5638871
theorem B9387197 : Blo 1648023 9387197 := bstep (se 3 (by rfl) ⟨1760099, by rfl⟩ : syracuseStep 9387197 = 3520199) B3520199
theorem B4693211 : Blo 1648023 4693211 := bstep (se 1 (by rfl) ⟨3519908, by rfl⟩ : syracuseStep 4693211 = 7039817) B7039817
theorem B2473193 : Blo 1648023 2473193 := bstep (se 2 (by rfl) ⟨927447, by rfl⟩ : syracuseStep 2473193 = 1854895) B1854895
theorem B2473247 : Blo 1648023 2473247 := bstep (se 1 (by rfl) ⟨1854935, by rfl⟩ : syracuseStep 2473247 = 3709871) B3709871
theorem B3710303 : Blo 1648023 3710303 := bstep (se 1 (by rfl) ⟨2782727, by rfl⟩ : syracuseStep 3710303 = 5565455) B5565455
theorem B2473415 : Blo 1648023 2473415 := bstep (se 1 (by rfl) ⟨1855061, by rfl⟩ : syracuseStep 2473415 = 3710123) B3710123
theorem B4456097 : Blo 1648023 4456097 := bstep (se 2 (by rfl) ⟨1671036, by rfl⟩ : syracuseStep 4456097 = 3342073) B3342073
theorem B3710699 : Blo 1648023 3710699 := bstep (se 1 (by rfl) ⟨2783024, by rfl⟩ : syracuseStep 3710699 = 5566049) B5566049
theorem B2473769 : Blo 1648023 2473769 := bstep (se 2 (by rfl) ⟨927663, by rfl⟩ : syracuseStep 2473769 = 1855327) B1855327
theorem B2473775 : Blo 1648023 2473775 := bstep (se 1 (by rfl) ⟨1855331, by rfl⟩ : syracuseStep 2473775 = 3710663) B3710663
theorem B3522361 : Blo 1648023 3522361 := bstep (se 2 (by rfl) ⟨1320885, by rfl⟩ : syracuseStep 3522361 = 2641771) B2641771
theorem B3710825 : Blo 1648023 3710825 := bstep (se 2 (by rfl) ⟨1391559, by rfl⟩ : syracuseStep 3710825 = 2783119) B2783119
theorem B5562269 : Blo 1648023 5562269 := bstep (se 3 (by rfl) ⟨1042925, by rfl⟩ : syracuseStep 5562269 = 2085851) B2085851
theorem B23765035 : Blo 1648023 23765035 := bstep (se 1 (by rfl) ⟨17823776, by rfl⟩ : syracuseStep 23765035 = 35647553) B35647553
theorem B3522779 : Blo 1648023 3522779 := bstep (se 1 (by rfl) ⟨2642084, by rfl⟩ : syracuseStep 3522779 = 5284169) B5284169
theorem B3760415 : Blo 1648023 3760415 := bstep (se 1 (by rfl) ⟨2820311, by rfl⟩ : syracuseStep 3760415 = 5640623) B5640623
theorem B3522847 : Blo 1648023 3522847 := bstep (se 1 (by rfl) ⟨2642135, by rfl⟩ : syracuseStep 3522847 = 5284271) B5284271
theorem B18563417 : Blo 1648023 18563417 := bstep (se 2 (by rfl) ⟨6961281, by rfl⟩ : syracuseStep 18563417 = 13922563) B13922563
theorem B3711329 : Blo 1648023 3711329 := bstep (se 2 (by rfl) ⟨1391748, by rfl⟩ : syracuseStep 3711329 = 2783497) B2783497
theorem B3711419 : Blo 1648023 3711419 := bstep (se 1 (by rfl) ⟨2783564, by rfl⟩ : syracuseStep 3711419 = 5567129) B5567129
theorem B3129833 : Blo 1648023 3129833 := bstep (se 2 (by rfl) ⟨1173687, by rfl⟩ : syracuseStep 3129833 = 2347375) B2347375
theorem B12051017 : Blo 1648023 12051017 := bstep (se 2 (by rfl) ⟨4519131, by rfl⟩ : syracuseStep 12051017 = 9038263) B9038263
theorem B6685379 : Blo 1648023 6685379 := bstep (se 1 (by rfl) ⟨5014034, by rfl⟩ : syracuseStep 6685379 = 10028069) B10028069
theorem B5563133 : Blo 1648023 5563133 := bstep (se 3 (by rfl) ⟨1043087, by rfl⟩ : syracuseStep 5563133 = 2086175) B2086175
theorem B3130159 : Blo 1648023 3130159 := bstep (se 1 (by rfl) ⟨2347619, by rfl⟩ : syracuseStep 3130159 = 4695239) B4695239
theorem B2008127 : Blo 1648023 2008127 := bstep (se 1 (by rfl) ⟨1506095, by rfl⟩ : syracuseStep 2008127 = 3012191) B3012191
theorem B1648027 : Blo 1648023 1648027 := bstep (se 1 (by rfl) ⟨1236020, by rfl⟩ : syracuseStep 1648027 = 2472041) B2472041
theorem B27108857 : Blo 1648023 27108857 := bstep (se 2 (by rfl) ⟨10165821, by rfl⟩ : syracuseStep 27108857 = 20331643) B20331643
theorem B1648239 : Blo 1648023 1648239 := bstep (se 1 (by rfl) ⟨1236179, by rfl⟩ : syracuseStep 1648239 = 2472359) B2472359
theorem B2008687 : Blo 1648023 2008687 := bstep (se 1 (by rfl) ⟨1506515, by rfl⟩ : syracuseStep 2008687 = 3013031) B3013031
theorem B1648295 : Blo 1648023 1648295 := bstep (se 1 (by rfl) ⟨1236221, by rfl⟩ : syracuseStep 1648295 = 2472443) B2472443
theorem B1648379 : Blo 1648023 1648379 := bstep (se 1 (by rfl) ⟨1236284, by rfl⟩ : syracuseStep 1648379 = 2472569) B2472569
theorem B1648415 : Blo 1648023 1648415 := bstep (se 1 (by rfl) ⟨1236311, by rfl⟩ : syracuseStep 1648415 = 2472623) B2472623
theorem B1648447 : Blo 1648023 1648447 := bstep (se 1 (by rfl) ⟨1236335, by rfl⟩ : syracuseStep 1648447 = 2472671) B2472671
theorem B8349641 : Blo 1648023 8349641 := bstep (se 2 (by rfl) ⟨3131115, by rfl⟩ : syracuseStep 8349641 = 6262231) B6262231
theorem B1648623 : Blo 1648023 1648623 := bstep (se 1 (by rfl) ⟨1236467, by rfl⟩ : syracuseStep 1648623 = 2472935) B2472935
theorem B1648795 : Blo 1648023 1648795 := bstep (se 1 (by rfl) ⟨1236596, by rfl⟩ : syracuseStep 1648795 = 2473193) B2473193
theorem B1648831 : Blo 1648023 1648831 := bstep (se 1 (by rfl) ⟨1236623, by rfl⟩ : syracuseStep 1648831 = 2473247) B2473247
theorem B21129497 : Blo 1648023 21129497 := bstep (se 2 (by rfl) ⟨7923561, by rfl⟩ : syracuseStep 21129497 = 15847123) B15847123
theorem B1648943 : Blo 1648023 1648943 := bstep (se 1 (by rfl) ⟨1236707, by rfl⟩ : syracuseStep 1648943 = 2473415) B2473415
theorem B4696481 : Blo 1648023 4696481 := bstep (se 2 (by rfl) ⟨1761180, by rfl⟩ : syracuseStep 4696481 = 3522361) B3522361
theorem B1649179 : Blo 1648023 1649179 := bstep (se 1 (by rfl) ⟨1236884, by rfl⟩ : syracuseStep 1649179 = 2473769) B2473769
theorem B1649183 : Blo 1648023 1649183 := bstep (se 1 (by rfl) ⟨1236887, by rfl⟩ : syracuseStep 1649183 = 2473775) B2473775
theorem B5565239 : Blo 1648023 5565239 := bstep (se 1 (by rfl) ⟨4173929, by rfl⟩ : syracuseStep 5565239 = 8347859) B8347859
theorem B10029911 : Blo 1648023 10029911 := bstep (se 1 (by rfl) ⟨7522433, by rfl⟩ : syracuseStep 10029911 = 15044867) B15044867
theorem B1649499 : Blo 1648023 1649499 := bstep (se 1 (by rfl) ⟨1237124, by rfl⟩ : syracuseStep 1649499 = 2474249) B2474249
theorem B1854535 : Blo 1648023 1854535 := bstep (se 1 (by rfl) ⟨1390901, by rfl⟩ : syracuseStep 1854535 = 2781803) B2781803
theorem B13372697 : Blo 1648023 13372697 := bstep (se 2 (by rfl) ⟨5014761, by rfl⟩ : syracuseStep 13372697 = 10029523) B10029523
theorem B5942717 : Blo 1648023 5942717 := bstep (se 3 (by rfl) ⟨1114259, by rfl⟩ : syracuseStep 5942717 = 2228519) B2228519
theorem B2379559 : Blo 1648023 2379559 := bstep (se 1 (by rfl) ⟨1784669, by rfl⟩ : syracuseStep 2379559 = 3569339) B3569339
theorem B3616633 : Blo 1648023 3616633 := bstep (se 2 (by rfl) ⟨1356237, by rfl⟩ : syracuseStep 3616633 = 2712475) B2712475
theorem B4173707 : Blo 1648023 4173707 := bstep (se 1 (by rfl) ⟨3130280, by rfl⟩ : syracuseStep 4173707 = 6260561) B6260561
theorem B264155087 : Blo 1648023 264155087 := bstep (se 1 (by rfl) ⟨198116315, by rfl⟩ : syracuseStep 264155087 = 396232631) B396232631
theorem B21123139 : Blo 1648023 21123139 := bstep (se 1 (by rfl) ⟨15842354, by rfl⟩ : syracuseStep 21123139 = 31684709) B31684709
theorem B2781371 : Blo 1648023 2781371 := bstep (se 1 (by rfl) ⟨2086028, by rfl⟩ : syracuseStep 2781371 = 4172057) B4172057
theorem B7926083 : Blo 1648023 7926083 := bstep (se 1 (by rfl) ⟨5944562, by rfl⟩ : syracuseStep 7926083 = 11889125) B11889125
theorem B10031471 : Blo 1648023 10031471 := bstep (se 1 (by rfl) ⟨7523603, by rfl⟩ : syracuseStep 10031471 = 15047207) B15047207
theorem B21123503 : Blo 1648023 21123503 := bstep (se 1 (by rfl) ⟨15842627, by rfl⟩ : syracuseStep 21123503 = 31685255) B31685255
theorem B2347471 : Blo 1648023 2347471 := bstep (se 1 (by rfl) ⟨1760603, by rfl⟩ : syracuseStep 2347471 = 3521207) B3521207
theorem B2781931 : Blo 1648023 2781931 := bstep (se 1 (by rfl) ⟨2086448, by rfl⟩ : syracuseStep 2781931 = 4172897) B4172897
theorem B2896697 : Blo 1648023 2896697 := bstep (se 2 (by rfl) ⟨1086261, by rfl⟩ : syracuseStep 2896697 = 2172523) B2172523
theorem B2970731 : Blo 1648023 2970731 := bstep (se 1 (by rfl) ⟨2228048, by rfl⟩ : syracuseStep 2970731 = 4456097) B4456097
theorem B4175023 : Blo 1648023 4175023 := bstep (se 1 (by rfl) ⟨3131267, by rfl⟩ : syracuseStep 4175023 = 6262535) B6262535
theorem B11277521 : Blo 1648023 11277521 := bstep (se 2 (by rfl) ⟨4229070, by rfl⟩ : syracuseStep 11277521 = 8458141) B8458141
theorem B3708179 : Blo 1648023 3708179 := bstep (se 1 (by rfl) ⟨2781134, by rfl⟩ : syracuseStep 3708179 = 5562269) B5562269
theorem B3708251 : Blo 1648023 3708251 := bstep (se 1 (by rfl) ⟨2781188, by rfl⟩ : syracuseStep 3708251 = 5562377) B5562377
theorem B2782903 : Blo 1648023 2782903 := bstep (se 1 (by rfl) ⟨2087177, by rfl⟩ : syracuseStep 2782903 = 4174355) B4174355
theorem B2086651 : Blo 1648023 2086651 := bstep (se 1 (by rfl) ⟨1564988, by rfl⟩ : syracuseStep 2086651 = 3129977) B3129977
theorem B63379259 : Blo 1648023 63379259 := bstep (se 1 (by rfl) ⟨47534444, by rfl⟩ : syracuseStep 63379259 = 95068889) B95068889
theorem B11884421 : Blo 1648023 11884421 := bstep (se 4 (by rfl) ⟨1114164, by rfl⟩ : syracuseStep 11884421 = 2228329) B2228329
theorem B3708809 : Blo 1648023 3708809 := bstep (se 2 (by rfl) ⟨1390803, by rfl⟩ : syracuseStep 3708809 = 2781607) B2781607
theorem B15849431 : Blo 1648023 15849431 := bstep (se 1 (by rfl) ⟨11887073, by rfl⟩ : syracuseStep 15849431 = 23774147) B23774147
theorem B3962839 : Blo 1648023 3962839 := bstep (se 1 (by rfl) ⟨2972129, by rfl⟩ : syracuseStep 3962839 = 5944259) B5944259
theorem B2783207 : Blo 1648023 2783207 := bstep (se 1 (by rfl) ⟨2087405, by rfl⟩ : syracuseStep 2783207 = 4174811) B4174811
theorem B3709025 : Blo 1648023 3709025 := bstep (se 2 (by rfl) ⟨1390884, by rfl⟩ : syracuseStep 3709025 = 2781769) B2781769
theorem B12515471 : Blo 1648023 12515471 := bstep (se 1 (by rfl) ⟨9386603, by rfl⟩ : syracuseStep 12515471 = 18773207) B18773207
theorem B24082609 : Blo 1648023 24082609 := bstep (se 2 (by rfl) ⟨9030978, by rfl⟩ : syracuseStep 24082609 = 18061957) B18061957
theorem B2783423 : Blo 1648023 2783423 := bstep (se 1 (by rfl) ⟨2087567, by rfl⟩ : syracuseStep 2783423 = 4175135) B4175135
theorem B2087147 : Blo 1648023 2087147 := bstep (se 1 (by rfl) ⟨1565360, by rfl⟩ : syracuseStep 2087147 = 3130721) B3130721
theorem B2472233 : Blo 1648023 2472233 := bstep (se 2 (by rfl) ⟨927087, by rfl⟩ : syracuseStep 2472233 = 1854175) B1854175
theorem B2472239 : Blo 1648023 2472239 := bstep (se 1 (by rfl) ⟨1854179, by rfl⟩ : syracuseStep 2472239 = 3708359) B3708359
theorem B2472479 : Blo 1648023 2472479 := bstep (se 1 (by rfl) ⟨1854359, by rfl⟩ : syracuseStep 2472479 = 3708719) B3708719
theorem B5282425 : Blo 1648023 5282425 := bstep (se 2 (by rfl) ⟨1980909, by rfl⟩ : syracuseStep 5282425 = 3961819) B3961819
theorem B5012329 : Blo 1648023 5012329 := bstep (se 2 (by rfl) ⟨1879623, by rfl⟩ : syracuseStep 5012329 = 3759247) B3759247
theorem B2472863 : Blo 1648023 2472863 := bstep (se 1 (by rfl) ⟨1854647, by rfl⟩ : syracuseStep 2472863 = 3709295) B3709295
theorem B2472911 : Blo 1648023 2472911 := bstep (se 1 (by rfl) ⟨1854683, by rfl⟩ : syracuseStep 2472911 = 3709367) B3709367
theorem B16923599 : Blo 1648023 16923599 := bstep (se 1 (by rfl) ⟨12692699, by rfl⟩ : syracuseStep 16923599 = 25385399) B25385399
theorem B40647703 : Blo 1648023 40647703 := bstep (se 1 (by rfl) ⟨30485777, by rfl⟩ : syracuseStep 40647703 = 60971555) B60971555
theorem B2473001 : Blo 1648023 2473001 := bstep (se 2 (by rfl) ⟨927375, by rfl⟩ : syracuseStep 2473001 = 1854751) B1854751
theorem B2473007 : Blo 1648023 2473007 := bstep (se 1 (by rfl) ⟨1854755, by rfl⟩ : syracuseStep 2473007 = 3709511) B3709511
theorem B2473031 : Blo 1648023 2473031 := bstep (se 1 (by rfl) ⟨1854773, by rfl⟩ : syracuseStep 2473031 = 3709547) B3709547
theorem B9518161 : Blo 1648023 9518161 := bstep (se 2 (by rfl) ⟨3569310, by rfl⟩ : syracuseStep 9518161 = 7138621) B7138621
theorem B7519517 : Blo 1648023 7519517 := bstep (se 3 (by rfl) ⟨1409909, by rfl⟩ : syracuseStep 7519517 = 2819819) B2819819
theorem B21134621 : Blo 1648023 21134621 := bstep (se 3 (by rfl) ⟨3962741, by rfl⟩ : syracuseStep 21134621 = 7925483) B7925483
theorem B2473295 : Blo 1648023 2473295 := bstep (se 1 (by rfl) ⟨1854971, by rfl⟩ : syracuseStep 2473295 = 3709943) B3709943
theorem B3710375 : Blo 1648023 3710375 := bstep (se 1 (by rfl) ⟨2782781, by rfl⟩ : syracuseStep 3710375 = 5565563) B5565563
theorem B2473385 : Blo 1648023 2473385 := bstep (se 2 (by rfl) ⟨927519, by rfl⟩ : syracuseStep 2473385 = 1855039) B1855039
theorem B6258131 : Blo 1648023 6258131 := bstep (se 1 (by rfl) ⟨4693598, by rfl⟩ : syracuseStep 6258131 = 9387197) B9387197
theorem B3128807 : Blo 1648023 3128807 := bstep (se 1 (by rfl) ⟨2346605, by rfl⟩ : syracuseStep 3128807 = 4693211) B4693211
theorem B2473535 : Blo 1648023 2473535 := bstep (se 1 (by rfl) ⟨1855151, by rfl⟩ : syracuseStep 2473535 = 3710303) B3710303
theorem B3710555 : Blo 1648023 3710555 := bstep (se 1 (by rfl) ⟨2782916, by rfl⟩ : syracuseStep 3710555 = 5565833) B5565833
theorem B4759183 : Blo 1648023 4759183 := bstep (se 1 (by rfl) ⟨3569387, by rfl⟩ : syracuseStep 4759183 = 7138775) B7138775
theorem B45104825 : Blo 1648023 45104825 := bstep (se 2 (by rfl) ⟨16914309, by rfl⟩ : syracuseStep 45104825 = 33828619) B33828619
theorem B4693747 : Blo 1648023 4693747 := bstep (se 1 (by rfl) ⟨3520310, by rfl⟩ : syracuseStep 4693747 = 7040621) B7040621
theorem B2473799 : Blo 1648023 2473799 := bstep (se 1 (by rfl) ⟨1855349, by rfl⟩ : syracuseStep 2473799 = 3710699) B3710699
theorem B3710843 : Blo 1648023 3710843 := bstep (se 1 (by rfl) ⟨2783132, by rfl⟩ : syracuseStep 3710843 = 5566265) B5566265
theorem B2473883 : Blo 1648023 2473883 := bstep (se 1 (by rfl) ⟨1855412, by rfl⟩ : syracuseStep 2473883 = 3710825) B3710825
theorem B40124321 : Blo 1648023 40124321 := bstep (se 2 (by rfl) ⟨15046620, by rfl⟩ : syracuseStep 40124321 = 30093241) B30093241
theorem B31686713 : Blo 1648023 31686713 := bstep (se 2 (by rfl) ⟨11882517, by rfl⟩ : syracuseStep 31686713 = 23765035) B23765035
theorem B28164185 : Blo 1648023 28164185 := bstep (se 2 (by rfl) ⟨10561569, by rfl⟩ : syracuseStep 28164185 = 21123139) B21123139
theorem B2506943 : Blo 1648023 2506943 := bstep (se 1 (by rfl) ⟨1880207, by rfl⟩ : syracuseStep 2506943 = 3760415) B3760415
theorem B5284055 : Blo 1648023 5284055 := bstep (se 1 (by rfl) ⟨3963041, by rfl⟩ : syracuseStep 5284055 = 7926083) B7926083
theorem B2474219 : Blo 1648023 2474219 := bstep (se 1 (by rfl) ⟨1855664, by rfl⟩ : syracuseStep 2474219 = 3711329) B3711329
theorem B14082335 : Blo 1648023 14082335 := bstep (se 1 (by rfl) ⟨10561751, by rfl⟩ : syracuseStep 14082335 = 21123503) B21123503
theorem B2474279 : Blo 1648023 2474279 := bstep (se 1 (by rfl) ⟨1855709, by rfl⟩ : syracuseStep 2474279 = 3711419) B3711419
theorem B4456919 : Blo 1648023 4456919 := bstep (se 1 (by rfl) ⟨3342689, by rfl⟩ : syracuseStep 4456919 = 6685379) B6685379
theorem B28172933 : Blo 1648023 28172933 := bstep (se 4 (by rfl) ⟨2641212, by rfl⟩ : syracuseStep 28172933 = 5282425) B5282425
theorem B18072571 : Blo 1648023 18072571 := bstep (se 1 (by rfl) ⟨13554428, by rfl⟩ : syracuseStep 18072571 = 27108857) B27108857
theorem B7922947 : Blo 1648023 7922947 := bstep (se 1 (by rfl) ⟨5942210, by rfl⟩ : syracuseStep 7922947 = 11884421) B11884421
theorem B12690881 : Blo 1648023 12690881 := bstep (se 2 (by rfl) ⟨4759080, by rfl⟩ : syracuseStep 12690881 = 9518161) B9518161
theorem B1648155 : Blo 1648023 1648155 := bstep (se 1 (by rfl) ⟨1236116, by rfl⟩ : syracuseStep 1648155 = 2472233) B2472233
theorem B1648159 : Blo 1648023 1648159 := bstep (se 1 (by rfl) ⟨1236119, by rfl⟩ : syracuseStep 1648159 = 2472239) B2472239
theorem B3130987 : Blo 1648023 3130987 := bstep (se 1 (by rfl) ⟨2348240, by rfl⟩ : syracuseStep 3130987 = 4696481) B4696481
theorem B1648319 : Blo 1648023 1648319 := bstep (se 1 (by rfl) ⟨1236239, by rfl⟩ : syracuseStep 1648319 = 2472479) B2472479
theorem B1648575 : Blo 1648023 1648575 := bstep (se 1 (by rfl) ⟨1236431, by rfl⟩ : syracuseStep 1648575 = 2472863) B2472863
theorem B1648607 : Blo 1648023 1648607 := bstep (se 1 (by rfl) ⟨1236455, by rfl⟩ : syracuseStep 1648607 = 2472911) B2472911
theorem B11282399 : Blo 1648023 11282399 := bstep (se 1 (by rfl) ⟨8461799, by rfl⟩ : syracuseStep 11282399 = 16923599) B16923599
theorem B1648667 : Blo 1648023 1648667 := bstep (se 1 (by rfl) ⟨1236500, by rfl⟩ : syracuseStep 1648667 = 2473001) B2473001
theorem B1648671 : Blo 1648023 1648671 := bstep (se 1 (by rfl) ⟨1236503, by rfl⟩ : syracuseStep 1648671 = 2473007) B2473007
theorem B1648687 : Blo 1648023 1648687 := bstep (se 1 (by rfl) ⟨1236515, by rfl⟩ : syracuseStep 1648687 = 2473031) B2473031
theorem B8915131 : Blo 1648023 8915131 := bstep (se 1 (by rfl) ⟨6686348, by rfl⟩ : syracuseStep 8915131 = 13372697) B13372697
theorem B1648863 : Blo 1648023 1648863 := bstep (se 1 (by rfl) ⟨1236647, by rfl⟩ : syracuseStep 1648863 = 2473295) B2473295
theorem B1648923 : Blo 1648023 1648923 := bstep (se 1 (by rfl) ⟨1236692, by rfl⟩ : syracuseStep 1648923 = 2473385) B2473385
theorem B4172087 : Blo 1648023 4172087 := bstep (se 1 (by rfl) ⟨3129065, by rfl⟩ : syracuseStep 4172087 = 6258131) B6258131
theorem B1649023 : Blo 1648023 1649023 := bstep (se 1 (by rfl) ⟨1236767, by rfl⟩ : syracuseStep 1649023 = 2473535) B2473535
theorem B3172745 : Blo 1648023 3172745 := bstep (se 2 (by rfl) ⟨1189779, by rfl⟩ : syracuseStep 3172745 = 2379559) B2379559
theorem B12519845 : Blo 1648023 12519845 := bstep (se 4 (by rfl) ⟨1173735, by rfl⟩ : syracuseStep 12519845 = 2347471) B2347471
theorem B1649199 : Blo 1648023 1649199 := bstep (se 1 (by rfl) ⟨1236899, by rfl⟩ : syracuseStep 1649199 = 2473799) B2473799
theorem B1649255 : Blo 1648023 1649255 := bstep (se 1 (by rfl) ⟨1236941, by rfl⟩ : syracuseStep 1649255 = 2473883) B2473883
theorem B26749547 : Blo 1648023 26749547 := bstep (se 1 (by rfl) ⟨20062160, by rfl⟩ : syracuseStep 26749547 = 40124321) B40124321
theorem B1854247 : Blo 1648023 1854247 := bstep (se 1 (by rfl) ⟨1390685, by rfl⟩ : syracuseStep 1854247 = 2781371) B2781371
theorem B6687647 : Blo 1648023 6687647 := bstep (se 1 (by rfl) ⟨5015735, by rfl⟩ : syracuseStep 6687647 = 10031471) B10031471
theorem B4697129 : Blo 1648023 4697129 := bstep (se 2 (by rfl) ⟨1761423, by rfl⟩ : syracuseStep 4697129 = 3522847) B3522847
theorem B5565725 : Blo 1648023 5565725 := bstep (se 3 (by rfl) ⟨1043573, by rfl⟩ : syracuseStep 5565725 = 2087147) B2087147
theorem B4173545 : Blo 1648023 4173545 := bstep (se 2 (by rfl) ⟨1565079, by rfl⟩ : syracuseStep 4173545 = 3130159) B3130159
theorem B8343485 : Blo 1648023 8343485 := bstep (se 3 (by rfl) ⟨1564403, by rfl⟩ : syracuseStep 8343485 = 3128807) B3128807
theorem B5566427 : Blo 1648023 5566427 := bstep (se 1 (by rfl) ⟨4174820, by rfl⟩ : syracuseStep 5566427 = 8349641) B8349641
theorem B1855471 : Blo 1648023 1855471 := bstep (se 1 (by rfl) ⟨1391603, by rfl⟩ : syracuseStep 1855471 = 2783207) B2783207
theorem B8343647 : Blo 1648023 8343647 := bstep (se 1 (by rfl) ⟨6257735, by rfl⟩ : syracuseStep 8343647 = 12515471) B12515471
theorem B1855615 : Blo 1648023 1855615 := bstep (se 1 (by rfl) ⟨1391711, by rfl⟩ : syracuseStep 1855615 = 2783423) B2783423
theorem B14086331 : Blo 1648023 14086331 := bstep (se 1 (by rfl) ⟨10564748, by rfl⟩ : syracuseStep 14086331 = 21129497) B21129497
theorem B5566697 : Blo 1648023 5566697 := bstep (se 2 (by rfl) ⟨2087511, by rfl⟩ : syracuseStep 5566697 = 4175023) B4175023
theorem B19288709 : Blo 1648023 19288709 := bstep (se 4 (by rfl) ⟨1808316, by rfl⟩ : syracuseStep 19288709 = 3616633) B3616633
theorem B6345577 : Blo 1648023 6345577 := bstep (se 2 (by rfl) ⟨2379591, by rfl⟩ : syracuseStep 6345577 = 4759183) B4759183
theorem B3961811 : Blo 1648023 3961811 := bstep (se 1 (by rfl) ⟨2971358, by rfl⟩ : syracuseStep 3961811 = 5942717) B5942717
theorem B2782201 : Blo 1648023 2782201 := bstep (se 2 (by rfl) ⟨1043325, by rfl⟩ : syracuseStep 2782201 = 2086651) B2086651
theorem B30069883 : Blo 1648023 30069883 := bstep (se 1 (by rfl) ⟨22552412, by rfl⟩ : syracuseStep 30069883 = 45104825) B45104825
theorem B2782471 : Blo 1648023 2782471 := bstep (se 1 (by rfl) ⟨2086853, by rfl⟩ : syracuseStep 2782471 = 4173707) B4173707
theorem B2348519 : Blo 1648023 2348519 := bstep (se 1 (by rfl) ⟨1761389, by rfl⟩ : syracuseStep 2348519 = 3522779) B3522779
theorem B5355005 : Blo 1648023 5355005 := bstep (se 3 (by rfl) ⟨1004063, by rfl⟩ : syracuseStep 5355005 = 2008127) B2008127
theorem B12375611 : Blo 1648023 12375611 := bstep (se 1 (by rfl) ⟨9281708, by rfl⟩ : syracuseStep 12375611 = 18563417) B18563417
theorem B32110145 : Blo 1648023 32110145 := bstep (se 2 (by rfl) ⟨12041304, by rfl⟩ : syracuseStep 32110145 = 24082609) B24082609
theorem B2086555 : Blo 1648023 2086555 := bstep (se 1 (by rfl) ⟨1564916, by rfl⟩ : syracuseStep 2086555 = 3129833) B3129833
theorem B8034011 : Blo 1648023 8034011 := bstep (se 1 (by rfl) ⟨6025508, by rfl⟩ : syracuseStep 8034011 = 12051017) B12051017
theorem B3708755 : Blo 1648023 3708755 := bstep (se 1 (by rfl) ⟨2781566, by rfl⟩ : syracuseStep 3708755 = 5563133) B5563133
theorem B1931131 : Blo 1648023 1931131 := bstep (se 1 (by rfl) ⟨1448348, by rfl⟩ : syracuseStep 1931131 = 2896697) B2896697
theorem B1980487 : Blo 1648023 1980487 := bstep (se 1 (by rfl) ⟨1485365, by rfl⟩ : syracuseStep 1980487 = 2970731) B2970731
theorem B7518347 : Blo 1648023 7518347 := bstep (se 1 (by rfl) ⟨5638760, by rfl⟩ : syracuseStep 7518347 = 11277521) B11277521
theorem B2472119 : Blo 1648023 2472119 := bstep (se 1 (by rfl) ⟨1854089, by rfl⟩ : syracuseStep 2472119 = 3708179) B3708179
theorem B2472167 : Blo 1648023 2472167 := bstep (se 1 (by rfl) ⟨1854125, by rfl⟩ : syracuseStep 2472167 = 3708251) B3708251
theorem B106985717 : Blo 1648023 106985717 := bstep (se 5 (by rfl) ⟨5014955, by rfl⟩ : syracuseStep 106985717 = 10029911) B10029911
theorem B3709241 : Blo 1648023 3709241 := bstep (se 2 (by rfl) ⟨1390965, by rfl⟩ : syracuseStep 3709241 = 2781931) B2781931
theorem B6683105 : Blo 1648023 6683105 := bstep (se 2 (by rfl) ⟨2506164, by rfl⟩ : syracuseStep 6683105 = 5012329) B5012329
theorem B42252839 : Blo 1648023 42252839 := bstep (se 1 (by rfl) ⟨31689629, by rfl⟩ : syracuseStep 42252839 = 63379259) B63379259
theorem B2472539 : Blo 1648023 2472539 := bstep (se 1 (by rfl) ⟨1854404, by rfl⟩ : syracuseStep 2472539 = 3708809) B3708809
theorem B10566287 : Blo 1648023 10566287 := bstep (se 1 (by rfl) ⟨7924715, by rfl⟩ : syracuseStep 10566287 = 15849431) B15849431
theorem B54196937 : Blo 1648023 54196937 := bstep (se 2 (by rfl) ⟨20323851, by rfl⟩ : syracuseStep 54196937 = 40647703) B40647703
theorem B2472683 : Blo 1648023 2472683 := bstep (se 1 (by rfl) ⟨1854512, by rfl⟩ : syracuseStep 2472683 = 3709025) B3709025
theorem B2472713 : Blo 1648023 2472713 := bstep (se 2 (by rfl) ⟨927267, by rfl⟩ : syracuseStep 2472713 = 1854535) B1854535
theorem B3710159 : Blo 1648023 3710159 := bstep (se 1 (by rfl) ⟨2782619, by rfl⟩ : syracuseStep 3710159 = 5565239) B5565239
theorem B2678249 : Blo 1648023 2678249 := bstep (se 2 (by rfl) ⟨1004343, by rfl⟩ : syracuseStep 2678249 = 2008687) B2008687
theorem B5013011 : Blo 1648023 5013011 := bstep (se 1 (by rfl) ⟨3759758, by rfl⟩ : syracuseStep 5013011 = 7519517) B7519517
theorem B14089747 : Blo 1648023 14089747 := bstep (se 1 (by rfl) ⟨10567310, by rfl⟩ : syracuseStep 14089747 = 21134621) B21134621
theorem B3710537 : Blo 1648023 3710537 := bstep (se 2 (by rfl) ⟨1391451, by rfl⟩ : syracuseStep 3710537 = 2782903) B2782903
theorem B2473583 : Blo 1648023 2473583 := bstep (se 1 (by rfl) ⟨1855187, by rfl⟩ : syracuseStep 2473583 = 3710375) B3710375
theorem B6258329 : Blo 1648023 6258329 := bstep (se 2 (by rfl) ⟨2346873, by rfl⟩ : syracuseStep 6258329 = 4693747) B4693747
theorem B2473703 : Blo 1648023 2473703 := bstep (se 1 (by rfl) ⟨1855277, by rfl⟩ : syracuseStep 2473703 = 3710555) B3710555
theorem B2473895 : Blo 1648023 2473895 := bstep (se 1 (by rfl) ⟨1855421, by rfl⟩ : syracuseStep 2473895 = 3710843) B3710843
theorem B5283785 : Blo 1648023 5283785 := bstep (se 2 (by rfl) ⟨1981419, by rfl⟩ : syracuseStep 5283785 = 3962839) B3962839
theorem B176103391 : Blo 1648023 176103391 := bstep (se 1 (by rfl) ⟨132077543, by rfl⟩ : syracuseStep 176103391 = 264155087) B264155087
theorem B18776123 : Blo 1648023 18776123 := bstep (se 1 (by rfl) ⟨14082092, by rfl⟩ : syracuseStep 18776123 = 28164185) B28164185
theorem B5562431 : Blo 1648023 5562431 := bstep (se 1 (by rfl) ⟨4171823, by rfl⟩ : syracuseStep 5562431 = 8343647) B8343647
theorem B12525677 : Blo 1648023 12525677 := bstep (se 3 (by rfl) ⟨2348564, by rfl⟩ : syracuseStep 12525677 = 4697129) B4697129
theorem B3522703 : Blo 1648023 3522703 := bstep (se 1 (by rfl) ⟨2642027, by rfl⟩ : syracuseStep 3522703 = 5284055) B5284055
theorem B3711131 : Blo 1648023 3711131 := bstep (se 1 (by rfl) ⟨2783348, by rfl⟩ : syracuseStep 3711131 = 5566697) B5566697
theorem B2474153 : Blo 1648023 2474153 := bstep (se 2 (by rfl) ⟨927807, by rfl⟩ : syracuseStep 2474153 = 1855615) B1855615
theorem B9388223 : Blo 1648023 9388223 := bstep (se 1 (by rfl) ⟨7041167, by rfl⟩ : syracuseStep 9388223 = 14082335) B14082335
theorem B11886841 : Blo 1648023 11886841 := bstep (se 2 (by rfl) ⟨4457565, by rfl⟩ : syracuseStep 11886841 = 8915131) B8915131
theorem B6685181 : Blo 1648023 6685181 := bstep (se 3 (by rfl) ⟨1253471, by rfl⟩ : syracuseStep 6685181 = 2506943) B2506943
theorem B8250407 : Blo 1648023 8250407 := bstep (se 1 (by rfl) ⟨6187805, by rfl⟩ : syracuseStep 8250407 = 12375611) B12375611
theorem B21406763 : Blo 1648023 21406763 := bstep (se 1 (by rfl) ⟨16055072, by rfl⟩ : syracuseStep 21406763 = 32110145) B32110145
theorem B7521599 : Blo 1648023 7521599 := bstep (se 1 (by rfl) ⟨5641199, by rfl⟩ : syracuseStep 7521599 = 11282399) B11282399
theorem B14280013 : Blo 1648023 14280013 := bstep (se 3 (by rfl) ⟨2677502, by rfl⟩ : syracuseStep 14280013 = 5355005) B5355005
theorem B1648079 : Blo 1648023 1648079 := bstep (se 1 (by rfl) ⟨1236059, by rfl⟩ : syracuseStep 1648079 = 2472119) B2472119
theorem B1648111 : Blo 1648023 1648111 := bstep (se 1 (by rfl) ⟨1236083, by rfl⟩ : syracuseStep 1648111 = 2472167) B2472167
theorem B2115163 : Blo 1648023 2115163 := bstep (se 1 (by rfl) ⟨1586372, by rfl⟩ : syracuseStep 2115163 = 3172745) B3172745
theorem B1648359 : Blo 1648023 1648359 := bstep (se 1 (by rfl) ⟨1236269, by rfl⟩ : syracuseStep 1648359 = 2472539) B2472539
theorem B1648455 : Blo 1648023 1648455 := bstep (se 1 (by rfl) ⟨1236341, by rfl⟩ : syracuseStep 1648455 = 2472683) B2472683
theorem B1648475 : Blo 1648023 1648475 := bstep (se 1 (by rfl) ⟨1236356, by rfl⟩ : syracuseStep 1648475 = 2472713) B2472713
theorem B4458431 : Blo 1648023 4458431 := bstep (se 1 (by rfl) ⟨3343823, by rfl⟩ : syracuseStep 4458431 = 6687647) B6687647
theorem B10299365 : Blo 1648023 10299365 := bstep (se 4 (by rfl) ⟨965565, by rfl⟩ : syracuseStep 10299365 = 1931131) B1931131
theorem B18786329 : Blo 1648023 18786329 := bstep (se 2 (by rfl) ⟨7044873, by rfl⟩ : syracuseStep 18786329 = 14089747) B14089747
theorem B1649055 : Blo 1648023 1649055 := bstep (se 1 (by rfl) ⟨1236791, by rfl⟩ : syracuseStep 1649055 = 2473583) B2473583
theorem B4172219 : Blo 1648023 4172219 := bstep (se 1 (by rfl) ⟨3129164, by rfl⟩ : syracuseStep 4172219 = 6258329) B6258329
theorem B1649135 : Blo 1648023 1649135 := bstep (se 1 (by rfl) ⟨1236851, by rfl⟩ : syracuseStep 1649135 = 2473703) B2473703
theorem B1649263 : Blo 1648023 1649263 := bstep (se 1 (by rfl) ⟨1236947, by rfl⟩ : syracuseStep 1649263 = 2473895) B2473895
theorem B2640649 : Blo 1648023 2640649 := bstep (se 2 (by rfl) ⟨990243, by rfl⟩ : syracuseStep 2640649 = 1980487) B1980487
theorem B9390887 : Blo 1648023 9390887 := bstep (se 1 (by rfl) ⟨7043165, by rfl⟩ : syracuseStep 9390887 = 14086331) B14086331
theorem B1649479 : Blo 1648023 1649479 := bstep (se 1 (by rfl) ⟨1237109, by rfl⟩ : syracuseStep 1649479 = 2474219) B2474219
theorem B1649519 : Blo 1648023 1649519 := bstep (se 1 (by rfl) ⟨1237139, by rfl⟩ : syracuseStep 1649519 = 2474279) B2474279
theorem B17821613 : Blo 1648023 17821613 := bstep (se 3 (by rfl) ⟨3341552, by rfl⟩ : syracuseStep 17821613 = 6683105) B6683105
theorem B6262717 : Blo 1648023 6262717 := bstep (se 3 (by rfl) ⟨1174259, by rfl⟩ : syracuseStep 6262717 = 2348519) B2348519
theorem B24096761 : Blo 1648023 24096761 := bstep (se 2 (by rfl) ⟨9036285, by rfl⟩ : syracuseStep 24096761 = 18072571) B18072571
theorem B71323811 : Blo 1648023 71323811 := bstep (se 1 (by rfl) ⟨53492858, by rfl⟩ : syracuseStep 71323811 = 106985717) B106985717
theorem B2781391 : Blo 1648023 2781391 := bstep (se 1 (by rfl) ⟨2086043, by rfl⟩ : syracuseStep 2781391 = 4172087) B4172087
theorem B10563929 : Blo 1648023 10563929 := bstep (se 2 (by rfl) ⟨3961473, by rfl⟩ : syracuseStep 10563929 = 7922947) B7922947
theorem B28168559 : Blo 1648023 28168559 := bstep (se 1 (by rfl) ⟨21126419, by rfl⟩ : syracuseStep 28168559 = 42252839) B42252839
theorem B36131291 : Blo 1648023 36131291 := bstep (se 1 (by rfl) ⟨27098468, by rfl⟩ : syracuseStep 36131291 = 54196937) B54196937
theorem B4174649 : Blo 1648023 4174649 := bstep (se 2 (by rfl) ⟨1565493, by rfl⟩ : syracuseStep 4174649 = 3130987) B3130987
theorem B2782073 : Blo 1648023 2782073 := bstep (se 2 (by rfl) ⟨1043277, by rfl⟩ : syracuseStep 2782073 = 2086555) B2086555
theorem B2782363 : Blo 1648023 2782363 := bstep (se 1 (by rfl) ⟨2086772, by rfl⟩ : syracuseStep 2782363 = 4173545) B4173545
theorem B10564829 : Blo 1648023 10564829 := bstep (se 3 (by rfl) ⟨1980905, by rfl⟩ : syracuseStep 10564829 = 3961811) B3961811
theorem B234804521 : Blo 1648023 234804521 := bstep (se 2 (by rfl) ⟨88051695, by rfl⟩ : syracuseStep 234804521 = 176103391) B176103391
theorem B21124475 : Blo 1648023 21124475 := bstep (se 1 (by rfl) ⟨15843356, by rfl⟩ : syracuseStep 21124475 = 31686713) B31686713
theorem B2971279 : Blo 1648023 2971279 := bstep (se 1 (by rfl) ⟨2228459, by rfl⟩ : syracuseStep 2971279 = 4456919) B4456919
theorem B12859139 : Blo 1648023 12859139 := bstep (se 1 (by rfl) ⟨9644354, by rfl⟩ : syracuseStep 12859139 = 19288709) B19288709
theorem B18781955 : Blo 1648023 18781955 := bstep (se 1 (by rfl) ⟨14086466, by rfl⟩ : syracuseStep 18781955 = 28172933) B28172933
theorem B160372709 : Blo 1648023 160372709 := bstep (se 4 (by rfl) ⟨15034941, by rfl⟩ : syracuseStep 160372709 = 30069883) B30069883
theorem B8460587 : Blo 1648023 8460587 := bstep (se 1 (by rfl) ⟨6345440, by rfl⟩ : syracuseStep 8460587 = 12690881) B12690881
theorem B2472329 : Blo 1648023 2472329 := bstep (se 2 (by rfl) ⟨927123, by rfl⟩ : syracuseStep 2472329 = 1854247) B1854247
theorem B8460769 : Blo 1648023 8460769 := bstep (se 2 (by rfl) ⟨3172788, by rfl⟩ : syracuseStep 8460769 = 6345577) B6345577
theorem B5356007 : Blo 1648023 5356007 := bstep (se 1 (by rfl) ⟨4017005, by rfl⟩ : syracuseStep 5356007 = 8034011) B8034011
theorem B2472503 : Blo 1648023 2472503 := bstep (se 1 (by rfl) ⟨1854377, by rfl⟩ : syracuseStep 2472503 = 3708755) B3708755
theorem B3709601 : Blo 1648023 3709601 := bstep (se 2 (by rfl) ⟨1391100, by rfl⟩ : syracuseStep 3709601 = 2782201) B2782201
theorem B5012231 : Blo 1648023 5012231 := bstep (se 1 (by rfl) ⟨3759173, by rfl⟩ : syracuseStep 5012231 = 7518347) B7518347
theorem B2472827 : Blo 1648023 2472827 := bstep (se 1 (by rfl) ⟨1854620, by rfl⟩ : syracuseStep 2472827 = 3709241) B3709241
theorem B8346563 : Blo 1648023 8346563 := bstep (se 1 (by rfl) ⟨6259922, by rfl⟩ : syracuseStep 8346563 = 12519845) B12519845
theorem B3709961 : Blo 1648023 3709961 := bstep (se 2 (by rfl) ⟨1391235, by rfl⟩ : syracuseStep 3709961 = 2782471) B2782471
theorem B17833031 : Blo 1648023 17833031 := bstep (se 1 (by rfl) ⟨13374773, by rfl⟩ : syracuseStep 17833031 = 26749547) B26749547
theorem B7044191 : Blo 1648023 7044191 := bstep (se 1 (by rfl) ⟨5283143, by rfl⟩ : syracuseStep 7044191 = 10566287) B10566287
theorem B2473439 : Blo 1648023 2473439 := bstep (se 1 (by rfl) ⟨1855079, by rfl⟩ : syracuseStep 2473439 = 3710159) B3710159
theorem B3710483 : Blo 1648023 3710483 := bstep (se 1 (by rfl) ⟨2782862, by rfl⟩ : syracuseStep 3710483 = 5565725) B5565725
theorem B1785499 : Blo 1648023 1785499 := bstep (se 1 (by rfl) ⟨1339124, by rfl⟩ : syracuseStep 1785499 = 2678249) B2678249
theorem B3342007 : Blo 1648023 3342007 := bstep (se 1 (by rfl) ⟨2506505, by rfl⟩ : syracuseStep 3342007 = 5013011) B5013011
theorem B2473691 : Blo 1648023 2473691 := bstep (se 1 (by rfl) ⟨1855268, by rfl⟩ : syracuseStep 2473691 = 3710537) B3710537
theorem B5562323 : Blo 1648023 5562323 := bstep (se 1 (by rfl) ⟨4171742, by rfl⟩ : syracuseStep 5562323 = 8343485) B8343485
theorem B3522523 : Blo 1648023 3522523 := bstep (se 1 (by rfl) ⟨2641892, by rfl⟩ : syracuseStep 3522523 = 5283785) B5283785
theorem B3710951 : Blo 1648023 3710951 := bstep (se 1 (by rfl) ⟨2783213, by rfl⟩ : syracuseStep 3710951 = 5566427) B5566427
theorem B2473961 : Blo 1648023 2473961 := bstep (se 2 (by rfl) ⟨927735, by rfl⟩ : syracuseStep 2473961 = 1855471) B1855471
theorem B12517415 : Blo 1648023 12517415 := bstep (se 1 (by rfl) ⟨9388061, by rfl⟩ : syracuseStep 12517415 = 18776123) B18776123
theorem B2474087 : Blo 1648023 2474087 := bstep (se 1 (by rfl) ⟨1855565, by rfl⟩ : syracuseStep 2474087 = 3711131) B3711131
theorem B6258815 : Blo 1648023 6258815 := bstep (se 1 (by rfl) ⟨4694111, by rfl⟩ : syracuseStep 6258815 = 9388223) B9388223
theorem B4456787 : Blo 1648023 4456787 := bstep (se 1 (by rfl) ⟨3342590, by rfl⟩ : syracuseStep 4456787 = 6685181) B6685181
theorem B11281025 : Blo 1648023 11281025 := bstep (se 2 (by rfl) ⟨4230384, by rfl⟩ : syracuseStep 11281025 = 8460769) B8460769
theorem B14271175 : Blo 1648023 14271175 := bstep (se 1 (by rfl) ⟨10703381, by rfl⟩ : syracuseStep 14271175 = 21406763) B21406763
theorem B5014399 : Blo 1648023 5014399 := bstep (se 1 (by rfl) ⟨3760799, by rfl⟩ : syracuseStep 5014399 = 7521599) B7521599
theorem B14082983 : Blo 1648023 14082983 := bstep (se 1 (by rfl) ⟨10562237, by rfl⟩ : syracuseStep 14082983 = 21124475) B21124475
theorem B106915139 : Blo 1648023 106915139 := bstep (se 1 (by rfl) ⟨80186354, by rfl⟩ : syracuseStep 106915139 = 160372709) B160372709
theorem B6866243 : Blo 1648023 6866243 := bstep (se 1 (by rfl) ⟨5149682, by rfl⟩ : syracuseStep 6866243 = 10299365) B10299365
theorem B1648219 : Blo 1648023 1648219 := bstep (se 1 (by rfl) ⟨1236164, by rfl⟩ : syracuseStep 1648219 = 2472329) B2472329
theorem B1648335 : Blo 1648023 1648335 := bstep (se 1 (by rfl) ⟨1236251, by rfl⟩ : syracuseStep 1648335 = 2472503) B2472503
theorem B19040017 : Blo 1648023 19040017 := bstep (se 2 (by rfl) ⟨7140006, by rfl⟩ : syracuseStep 19040017 = 14280013) B14280013
theorem B6260591 : Blo 1648023 6260591 := bstep (se 1 (by rfl) ⟨4695443, by rfl⟩ : syracuseStep 6260591 = 9390887) B9390887
theorem B1648551 : Blo 1648023 1648551 := bstep (se 1 (by rfl) ⟨1236413, by rfl⟩ : syracuseStep 1648551 = 2472827) B2472827
theorem B5564375 : Blo 1648023 5564375 := bstep (se 1 (by rfl) ⟨4173281, by rfl⟩ : syracuseStep 5564375 = 8346563) B8346563
theorem B11888687 : Blo 1648023 11888687 := bstep (se 1 (by rfl) ⟨8916515, by rfl⟩ : syracuseStep 11888687 = 17833031) B17833031
theorem B4696127 : Blo 1648023 4696127 := bstep (se 1 (by rfl) ⟨3522095, by rfl⟩ : syracuseStep 4696127 = 7044191) B7044191
theorem B2820217 : Blo 1648023 2820217 := bstep (se 2 (by rfl) ⟨1057581, by rfl⟩ : syracuseStep 2820217 = 2115163) B2115163
theorem B1648959 : Blo 1648023 1648959 := bstep (se 1 (by rfl) ⟨1236719, by rfl⟩ : syracuseStep 1648959 = 2473439) B2473439
theorem B1649127 : Blo 1648023 1649127 := bstep (se 1 (by rfl) ⟨1236845, by rfl⟩ : syracuseStep 1649127 = 2473691) B2473691
theorem B8350289 : Blo 1648023 8350289 := bstep (se 2 (by rfl) ⟨3131358, by rfl⟩ : syracuseStep 8350289 = 6262717) B6262717
theorem B11881075 : Blo 1648023 11881075 := bstep (se 1 (by rfl) ⟨8910806, by rfl⟩ : syracuseStep 11881075 = 17821613) B17821613
theorem B4696697 : Blo 1648023 4696697 := bstep (se 2 (by rfl) ⟨1761261, by rfl⟩ : syracuseStep 4696697 = 3522523) B3522523
theorem B1649307 : Blo 1648023 1649307 := bstep (se 1 (by rfl) ⟨1236980, by rfl⟩ : syracuseStep 1649307 = 2473961) B2473961
theorem B8350451 : Blo 1648023 8350451 := bstep (se 1 (by rfl) ⟨6262838, by rfl⟩ : syracuseStep 8350451 = 12525677) B12525677
theorem B53463797 : Blo 1648023 53463797 := bstep (se 5 (by rfl) ⟨2506115, by rfl⟩ : syracuseStep 53463797 = 5012231) B5012231
theorem B47549207 : Blo 1648023 47549207 := bstep (se 1 (by rfl) ⟨35661905, by rfl⟩ : syracuseStep 47549207 = 71323811) B71323811
theorem B1649435 : Blo 1648023 1649435 := bstep (se 1 (by rfl) ⟨1237076, by rfl⟩ : syracuseStep 1649435 = 2474153) B2474153
theorem B4696937 : Blo 1648023 4696937 := bstep (se 2 (by rfl) ⟨1761351, by rfl⟩ : syracuseStep 4696937 = 3522703) B3522703
theorem B18779039 : Blo 1648023 18779039 := bstep (se 1 (by rfl) ⟨14084279, by rfl⟩ : syracuseStep 18779039 = 28168559) B28168559
theorem B24087527 : Blo 1648023 24087527 := bstep (se 1 (by rfl) ⟨18065645, by rfl⟩ : syracuseStep 24087527 = 36131291) B36131291
theorem B1854715 : Blo 1648023 1854715 := bstep (se 1 (by rfl) ⟨1391036, by rfl⟩ : syracuseStep 1854715 = 2782073) B2782073
theorem B5500271 : Blo 1648023 5500271 := bstep (se 1 (by rfl) ⟨4125203, by rfl⟩ : syracuseStep 5500271 = 8250407) B8250407
theorem B156536347 : Blo 1648023 156536347 := bstep (se 1 (by rfl) ⟨117402260, by rfl⟩ : syracuseStep 156536347 = 234804521) B234804521
theorem B8572759 : Blo 1648023 8572759 := bstep (se 1 (by rfl) ⟨6429569, by rfl⟩ : syracuseStep 8572759 = 12859139) B12859139
theorem B12521303 : Blo 1648023 12521303 := bstep (se 1 (by rfl) ⟨9390977, by rfl⟩ : syracuseStep 12521303 = 18781955) B18781955
theorem B5640391 : Blo 1648023 5640391 := bstep (se 1 (by rfl) ⟨4230293, by rfl⟩ : syracuseStep 5640391 = 8460587) B8460587
theorem B2781479 : Blo 1648023 2781479 := bstep (se 1 (by rfl) ⟨2086109, by rfl⟩ : syracuseStep 2781479 = 4172219) B4172219
theorem B3961705 : Blo 1648023 3961705 := bstep (se 2 (by rfl) ⟨1485639, by rfl⟩ : syracuseStep 3961705 = 2971279) B2971279
theorem B3708215 : Blo 1648023 3708215 := bstep (se 1 (by rfl) ⟨2781161, by rfl⟩ : syracuseStep 3708215 = 5562323) B5562323
theorem B3708287 : Blo 1648023 3708287 := bstep (se 1 (by rfl) ⟨2781215, by rfl⟩ : syracuseStep 3708287 = 5562431) B5562431
theorem B7042619 : Blo 1648023 7042619 := bstep (se 1 (by rfl) ⟨5281964, by rfl⟩ : syracuseStep 7042619 = 10563929) B10563929
theorem B3708521 : Blo 1648023 3708521 := bstep (se 2 (by rfl) ⟨1390695, by rfl⟩ : syracuseStep 3708521 = 2781391) B2781391
theorem B15849121 : Blo 1648023 15849121 := bstep (se 2 (by rfl) ⟨5943420, by rfl⟩ : syracuseStep 15849121 = 11886841) B11886841
theorem B2783099 : Blo 1648023 2783099 := bstep (se 1 (by rfl) ⟨2087324, by rfl⟩ : syracuseStep 2783099 = 4174649) B4174649
theorem B38090645 : Blo 1648023 38090645 := bstep (se 6 (by rfl) ⟨892749, by rfl⟩ : syracuseStep 38090645 = 1785499) B1785499
theorem B7043219 : Blo 1648023 7043219 := bstep (se 1 (by rfl) ⟨5282414, by rfl⟩ : syracuseStep 7043219 = 10564829) B10564829
theorem B3520865 : Blo 1648023 3520865 := bstep (se 2 (by rfl) ⟨1320324, by rfl⟩ : syracuseStep 3520865 = 2640649) B2640649
theorem B2972287 : Blo 1648023 2972287 := bstep (se 1 (by rfl) ⟨2229215, by rfl⟩ : syracuseStep 2972287 = 4458431) B4458431
theorem B12524219 : Blo 1648023 12524219 := bstep (se 1 (by rfl) ⟨9393164, by rfl⟩ : syracuseStep 12524219 = 18786329) B18786329
theorem B3709817 : Blo 1648023 3709817 := bstep (se 2 (by rfl) ⟨1391181, by rfl⟩ : syracuseStep 3709817 = 2782363) B2782363
theorem B3570671 : Blo 1648023 3570671 := bstep (se 1 (by rfl) ⟨2678003, by rfl⟩ : syracuseStep 3570671 = 5356007) B5356007
theorem B2473067 : Blo 1648023 2473067 := bstep (se 1 (by rfl) ⟨1854800, by rfl⟩ : syracuseStep 2473067 = 3709601) B3709601
theorem B2473307 : Blo 1648023 2473307 := bstep (se 1 (by rfl) ⟨1854980, by rfl⟩ : syracuseStep 2473307 = 3709961) B3709961
theorem B4456009 : Blo 1648023 4456009 := bstep (se 2 (by rfl) ⟨1671003, by rfl⟩ : syracuseStep 4456009 = 3342007) B3342007
theorem B2473655 : Blo 1648023 2473655 := bstep (se 1 (by rfl) ⟨1855241, by rfl⟩ : syracuseStep 2473655 = 3710483) B3710483
theorem B2473967 : Blo 1648023 2473967 := bstep (se 1 (by rfl) ⟨1855475, by rfl⟩ : syracuseStep 2473967 = 3710951) B3710951
theorem B16064507 : Blo 1648023 16064507 := bstep (se 1 (by rfl) ⟨12048380, by rfl⟩ : syracuseStep 16064507 = 24096761) B24096761
theorem B3760289 : Blo 1648023 3760289 := bstep (se 2 (by rfl) ⟨1410108, by rfl⟩ : syracuseStep 3760289 = 2820217) B2820217
theorem B7520521 : Blo 1648023 7520521 := bstep (se 2 (by rfl) ⟨2820195, by rfl⟩ : syracuseStep 7520521 = 5640391) B5640391
theorem B7520683 : Blo 1648023 7520683 := bstep (se 1 (by rfl) ⟨5640512, by rfl⟩ : syracuseStep 7520683 = 11281025) B11281025
theorem B9388655 : Blo 1648023 9388655 := bstep (se 1 (by rfl) ⟨7041491, by rfl⟩ : syracuseStep 9388655 = 14082983) B14082983
theorem B47539061 : Blo 1648023 47539061 := bstep (se 5 (by rfl) ⟨2228393, by rfl⟩ : syracuseStep 47539061 = 4456787) B4456787
theorem B9388973 : Blo 1648023 9388973 := bstep (se 3 (by rfl) ⟨1760432, by rfl⟩ : syracuseStep 9388973 = 3520865) B3520865
theorem B4695079 : Blo 1648023 4695079 := bstep (se 1 (by rfl) ⟨3521309, by rfl⟩ : syracuseStep 4695079 = 7042619) B7042619
theorem B6685865 : Blo 1648023 6685865 := bstep (se 2 (by rfl) ⟨2507199, by rfl⟩ : syracuseStep 6685865 = 5014399) B5014399
theorem B3130751 : Blo 1648023 3130751 := bstep (se 1 (by rfl) ⟨2348063, by rfl⟩ : syracuseStep 3130751 = 4696127) B4696127
theorem B4695479 : Blo 1648023 4695479 := bstep (se 1 (by rfl) ⟨3521609, by rfl⟩ : syracuseStep 4695479 = 7043219) B7043219
theorem B3131131 : Blo 1648023 3131131 := bstep (se 1 (by rfl) ⟨2348348, by rfl⟩ : syracuseStep 3131131 = 4696697) B4696697
theorem B45721381 : Blo 1648023 45721381 := bstep (se 4 (by rfl) ⟨4286379, by rfl⟩ : syracuseStep 45721381 = 8572759) B8572759
theorem B8349479 : Blo 1648023 8349479 := bstep (se 1 (by rfl) ⟨6262109, by rfl⟩ : syracuseStep 8349479 = 12524219) B12524219
theorem B3131291 : Blo 1648023 3131291 := bstep (se 1 (by rfl) ⟨2348468, by rfl⟩ : syracuseStep 3131291 = 4696937) B4696937
theorem B12519359 : Blo 1648023 12519359 := bstep (se 1 (by rfl) ⟨9389519, by rfl⟩ : syracuseStep 12519359 = 18779039) B18779039
theorem B16058351 : Blo 1648023 16058351 := bstep (se 1 (by rfl) ⟨12043763, by rfl⟩ : syracuseStep 16058351 = 24087527) B24087527
theorem B1648711 : Blo 1648023 1648711 := bstep (se 1 (by rfl) ⟨1236533, by rfl⟩ : syracuseStep 1648711 = 2473067) B2473067
theorem B5941345 : Blo 1648023 5941345 := bstep (se 2 (by rfl) ⟨2228004, by rfl⟩ : syracuseStep 5941345 = 4456009) B4456009
theorem B1648871 : Blo 1648023 1648871 := bstep (se 1 (by rfl) ⟨1236653, by rfl⟩ : syracuseStep 1648871 = 2473307) B2473307
theorem B1649103 : Blo 1648023 1649103 := bstep (se 1 (by rfl) ⟨1236827, by rfl⟩ : syracuseStep 1649103 = 2473655) B2473655
theorem B1649311 : Blo 1648023 1649311 := bstep (se 1 (by rfl) ⟨1236983, by rfl⟩ : syracuseStep 1649311 = 2473967) B2473967
theorem B10709671 : Blo 1648023 10709671 := bstep (se 1 (by rfl) ⟨8032253, by rfl⟩ : syracuseStep 10709671 = 16064507) B16064507
theorem B1649391 : Blo 1648023 1649391 := bstep (se 1 (by rfl) ⟨1237043, by rfl⟩ : syracuseStep 1649391 = 2474087) B2474087
theorem B4172543 : Blo 1648023 4172543 := bstep (se 1 (by rfl) ⟨3129407, by rfl⟩ : syracuseStep 4172543 = 6258815) B6258815
theorem B1854319 : Blo 1648023 1854319 := bstep (se 1 (by rfl) ⟨1390739, by rfl⟩ : syracuseStep 1854319 = 2781479) B2781479
theorem B14667389 : Blo 1648023 14667389 := bstep (se 3 (by rfl) ⟨2750135, by rfl⟩ : syracuseStep 14667389 = 5500271) B5500271
theorem B4173727 : Blo 1648023 4173727 := bstep (se 1 (by rfl) ⟨3130295, by rfl⟩ : syracuseStep 4173727 = 6260591) B6260591
theorem B1855399 : Blo 1648023 1855399 := bstep (se 1 (by rfl) ⟨1391549, by rfl⟩ : syracuseStep 1855399 = 2783099) B2783099
theorem B7925791 : Blo 1648023 7925791 := bstep (se 1 (by rfl) ⟨5944343, by rfl⟩ : syracuseStep 7925791 = 11888687) B11888687
theorem B5566859 : Blo 1648023 5566859 := bstep (se 1 (by rfl) ⟨4175144, by rfl⟩ : syracuseStep 5566859 = 8350289) B8350289
theorem B5566967 : Blo 1648023 5566967 := bstep (se 1 (by rfl) ⟨4175225, by rfl⟩ : syracuseStep 5566967 = 8350451) B8350451
theorem B31699471 : Blo 1648023 31699471 := bstep (se 1 (by rfl) ⟨23774603, by rfl⟩ : syracuseStep 31699471 = 47549207) B47549207
theorem B2380447 : Blo 1648023 2380447 := bstep (se 1 (by rfl) ⟨1785335, by rfl⟩ : syracuseStep 2380447 = 3570671) B3570671
theorem B21132161 : Blo 1648023 21132161 := bstep (se 2 (by rfl) ⟨7924560, by rfl⟩ : syracuseStep 21132161 = 15849121) B15849121
theorem B8344943 : Blo 1648023 8344943 := bstep (se 1 (by rfl) ⟨6258707, by rfl⟩ : syracuseStep 8344943 = 12517415) B12517415
theorem B15841433 : Blo 1648023 15841433 := bstep (se 2 (by rfl) ⟨5940537, by rfl⟩ : syracuseStep 15841433 = 11881075) B11881075
theorem B3963049 : Blo 1648023 3963049 := bstep (se 2 (by rfl) ⟨1486143, by rfl⟩ : syracuseStep 3963049 = 2972287) B2972287
theorem B2472143 : Blo 1648023 2472143 := bstep (se 1 (by rfl) ⟨1854107, by rfl⟩ : syracuseStep 2472143 = 3708215) B3708215
theorem B71276759 : Blo 1648023 71276759 := bstep (se 1 (by rfl) ⟨53457569, by rfl⟩ : syracuseStep 71276759 = 106915139) B106915139
theorem B4577495 : Blo 1648023 4577495 := bstep (se 1 (by rfl) ⟨3433121, by rfl⟩ : syracuseStep 4577495 = 6866243) B6866243
theorem B2472191 : Blo 1648023 2472191 := bstep (se 1 (by rfl) ⟨1854143, by rfl⟩ : syracuseStep 2472191 = 3708287) B3708287
theorem B19028233 : Blo 1648023 19028233 := bstep (se 2 (by rfl) ⟨7135587, by rfl⟩ : syracuseStep 19028233 = 14271175) B14271175
theorem B2472347 : Blo 1648023 2472347 := bstep (se 1 (by rfl) ⟨1854260, by rfl⟩ : syracuseStep 2472347 = 3708521) B3708521
theorem B5282273 : Blo 1648023 5282273 := bstep (se 2 (by rfl) ⟨1980852, by rfl⟩ : syracuseStep 5282273 = 3961705) B3961705
theorem B25393763 : Blo 1648023 25393763 := bstep (se 1 (by rfl) ⟨19045322, by rfl⟩ : syracuseStep 25393763 = 38090645) B38090645
theorem B3709583 : Blo 1648023 3709583 := bstep (se 1 (by rfl) ⟨2782187, by rfl⟩ : syracuseStep 3709583 = 5564375) B5564375
theorem B2472953 : Blo 1648023 2472953 := bstep (se 2 (by rfl) ⟨927357, by rfl⟩ : syracuseStep 2472953 = 1854715) B1854715
theorem B35642531 : Blo 1648023 35642531 := bstep (se 1 (by rfl) ⟨26731898, by rfl⟩ : syracuseStep 35642531 = 53463797) B53463797
theorem B2473211 : Blo 1648023 2473211 := bstep (se 1 (by rfl) ⟨1854908, by rfl⟩ : syracuseStep 2473211 = 3709817) B3709817
theorem B208715129 : Blo 1648023 208715129 := bstep (se 2 (by rfl) ⟨78268173, by rfl⟩ : syracuseStep 208715129 = 156536347) B156536347
theorem B25386689 : Blo 1648023 25386689 := bstep (se 2 (by rfl) ⟨9520008, by rfl⟩ : syracuseStep 25386689 = 19040017) B19040017
theorem B8347535 : Blo 1648023 8347535 := bstep (se 1 (by rfl) ⟨6260651, by rfl⟩ : syracuseStep 8347535 = 12521303) B12521303
theorem B10567721 : Blo 1648023 10567721 := bstep (se 2 (by rfl) ⟨3962895, by rfl⟩ : syracuseStep 10567721 = 7925791) B7925791
theorem B2506859 : Blo 1648023 2506859 := bstep (se 1 (by rfl) ⟨1880144, by rfl⟩ : syracuseStep 2506859 = 3760289) B3760289
theorem B7921793 : Blo 1648023 7921793 := bstep (se 2 (by rfl) ⟨2970672, by rfl⟩ : syracuseStep 7921793 = 5941345) B5941345
theorem B3711239 : Blo 1648023 3711239 := bstep (se 1 (by rfl) ⟨2783429, by rfl⟩ : syracuseStep 3711239 = 5566859) B5566859
theorem B3711311 : Blo 1648023 3711311 := bstep (se 1 (by rfl) ⟨2783483, by rfl⟩ : syracuseStep 3711311 = 5566967) B5566967
theorem B25370977 : Blo 1648023 25370977 := bstep (se 2 (by rfl) ⟨9514116, by rfl⟩ : syracuseStep 25370977 = 19028233) B19028233
theorem B10027361 : Blo 1648023 10027361 := bstep (se 2 (by rfl) ⟨3760260, by rfl⟩ : syracuseStep 10027361 = 7520521) B7520521
theorem B6259103 : Blo 1648023 6259103 := bstep (se 1 (by rfl) ⟨4694327, by rfl⟩ : syracuseStep 6259103 = 9388655) B9388655
theorem B10027577 : Blo 1648023 10027577 := bstep (se 2 (by rfl) ⟨3760341, by rfl⟩ : syracuseStep 10027577 = 7520683) B7520683
theorem B6259315 : Blo 1648023 6259315 := bstep (se 1 (by rfl) ⟨4694486, by rfl⟩ : syracuseStep 6259315 = 9388973) B9388973
theorem B4457243 : Blo 1648023 4457243 := bstep (se 1 (by rfl) ⟨3342932, by rfl⟩ : syracuseStep 4457243 = 6685865) B6685865
theorem B21136261 : Blo 1648023 21136261 := bstep (se 4 (by rfl) ⟨1981524, by rfl⟩ : syracuseStep 21136261 = 3963049) B3963049
theorem B14279561 : Blo 1648023 14279561 := bstep (se 2 (by rfl) ⟨5354835, by rfl⟩ : syracuseStep 14279561 = 10709671) B10709671
theorem B5563295 : Blo 1648023 5563295 := bstep (se 1 (by rfl) ⟨4172471, by rfl⟩ : syracuseStep 5563295 = 8344943) B8344943
theorem B3130319 : Blo 1648023 3130319 := bstep (se 1 (by rfl) ⟨2347739, by rfl⟩ : syracuseStep 3130319 = 4695479) B4695479
theorem B8348669 : Blo 1648023 8348669 := bstep (se 3 (by rfl) ⟨1565375, by rfl⟩ : syracuseStep 8348669 = 3130751) B3130751
theorem B6260105 : Blo 1648023 6260105 := bstep (se 2 (by rfl) ⟨2347539, by rfl⟩ : syracuseStep 6260105 = 4695079) B4695079
theorem B10560955 : Blo 1648023 10560955 := bstep (se 1 (by rfl) ⟨7920716, by rfl⟩ : syracuseStep 10560955 = 15841433) B15841433
theorem B1648095 : Blo 1648023 1648095 := bstep (se 1 (by rfl) ⟨1236071, by rfl⟩ : syracuseStep 1648095 = 2472143) B2472143
theorem B1648127 : Blo 1648023 1648127 := bstep (se 1 (by rfl) ⟨1236095, by rfl⟩ : syracuseStep 1648127 = 2472191) B2472191
theorem B1648231 : Blo 1648023 1648231 := bstep (se 1 (by rfl) ⟨1236173, by rfl⟩ : syracuseStep 1648231 = 2472347) B2472347
theorem B1648635 : Blo 1648023 1648635 := bstep (se 1 (by rfl) ⟨1236476, by rfl⟩ : syracuseStep 1648635 = 2472953) B2472953
theorem B1648807 : Blo 1648023 1648807 := bstep (se 1 (by rfl) ⟨1236605, by rfl⟩ : syracuseStep 1648807 = 2473211) B2473211
theorem B48826613 : Blo 1648023 48826613 := bstep (se 5 (by rfl) ⟨2288747, by rfl⟩ : syracuseStep 48826613 = 4577495) B4577495
theorem B139143419 : Blo 1648023 139143419 := bstep (se 1 (by rfl) ⟨104357564, by rfl⟩ : syracuseStep 139143419 = 208715129) B208715129
theorem B5564969 : Blo 1648023 5564969 := bstep (se 2 (by rfl) ⟨2086863, by rfl⟩ : syracuseStep 5564969 = 4173727) B4173727
theorem B5565023 : Blo 1648023 5565023 := bstep (se 1 (by rfl) ⟨4173767, by rfl⟩ : syracuseStep 5565023 = 8347535) B8347535
theorem B42265961 : Blo 1648023 42265961 := bstep (se 2 (by rfl) ⟨15849735, by rfl⟩ : syracuseStep 42265961 = 31699471) B31699471
theorem B5566319 : Blo 1648023 5566319 := bstep (se 1 (by rfl) ⟨4174739, by rfl⟩ : syracuseStep 5566319 = 8349479) B8349479
theorem B47517839 : Blo 1648023 47517839 := bstep (se 1 (by rfl) ⟨35638379, by rfl⟩ : syracuseStep 47517839 = 71276759) B71276759
theorem B16929175 : Blo 1648023 16929175 := bstep (se 1 (by rfl) ⟨12696881, by rfl⟩ : syracuseStep 16929175 = 25393763) B25393763
theorem B2781695 : Blo 1648023 2781695 := bstep (se 1 (by rfl) ⟨2086271, by rfl⟩ : syracuseStep 2781695 = 4172543) B4172543
theorem B23761687 : Blo 1648023 23761687 := bstep (se 1 (by rfl) ⟨17821265, by rfl⟩ : syracuseStep 23761687 = 35642531) B35642531
theorem B4174841 : Blo 1648023 4174841 := bstep (se 2 (by rfl) ⟨1565565, by rfl⟩ : syracuseStep 4174841 = 3131131) B3131131
theorem B60961841 : Blo 1648023 60961841 := bstep (se 2 (by rfl) ⟨22860690, by rfl⟩ : syracuseStep 60961841 = 45721381) B45721381
theorem B9778259 : Blo 1648023 9778259 := bstep (se 1 (by rfl) ⟨7333694, by rfl⟩ : syracuseStep 9778259 = 14667389) B14667389
theorem B31692707 : Blo 1648023 31692707 := bstep (se 1 (by rfl) ⟨23769530, by rfl⟩ : syracuseStep 31692707 = 47539061) B47539061
theorem B14088107 : Blo 1648023 14088107 := bstep (se 1 (by rfl) ⟨10566080, by rfl⟩ : syracuseStep 14088107 = 21132161) B21132161
theorem B12695717 : Blo 1648023 12695717 := bstep (se 4 (by rfl) ⟨1190223, by rfl⟩ : syracuseStep 12695717 = 2380447) B2380447
theorem B2472425 : Blo 1648023 2472425 := bstep (se 2 (by rfl) ⟨927159, by rfl⟩ : syracuseStep 2472425 = 1854319) B1854319
theorem B2087527 : Blo 1648023 2087527 := bstep (se 1 (by rfl) ⟨1565645, by rfl⟩ : syracuseStep 2087527 = 3131291) B3131291
theorem B8346239 : Blo 1648023 8346239 := bstep (se 1 (by rfl) ⟨6259679, by rfl⟩ : syracuseStep 8346239 = 12519359) B12519359
theorem B10705567 : Blo 1648023 10705567 := bstep (se 1 (by rfl) ⟨8029175, by rfl⟩ : syracuseStep 10705567 = 16058351) B16058351
theorem B3521515 : Blo 1648023 3521515 := bstep (se 1 (by rfl) ⟨2641136, by rfl⟩ : syracuseStep 3521515 = 5282273) B5282273
theorem B2473055 : Blo 1648023 2473055 := bstep (se 1 (by rfl) ⟨1854791, by rfl⟩ : syracuseStep 2473055 = 3709583) B3709583
theorem B16924459 : Blo 1648023 16924459 := bstep (se 1 (by rfl) ⟨12693344, by rfl⟩ : syracuseStep 16924459 = 25386689) B25386689
theorem B2473865 : Blo 1648023 2473865 := bstep (se 2 (by rfl) ⟨927699, by rfl⟩ : syracuseStep 2473865 = 1855399) B1855399
theorem B7045147 : Blo 1648023 7045147 := bstep (se 1 (by rfl) ⟨5283860, by rfl⟩ : syracuseStep 7045147 = 10567721) B10567721
theorem B1671239 : Blo 1648023 1671239 := bstep (se 1 (by rfl) ⟨1253429, by rfl⟩ : syracuseStep 1671239 = 2506859) B2506859
theorem B31678559 : Blo 1648023 31678559 := bstep (se 1 (by rfl) ⟨23758919, by rfl⟩ : syracuseStep 31678559 = 47517839) B47517839
theorem B2474159 : Blo 1648023 2474159 := bstep (se 1 (by rfl) ⟨1855619, by rfl⟩ : syracuseStep 2474159 = 3711239) B3711239
theorem B2474207 : Blo 1648023 2474207 := bstep (se 1 (by rfl) ⟨1855655, by rfl⟩ : syracuseStep 2474207 = 3711311) B3711311
theorem B9519707 : Blo 1648023 9519707 := bstep (se 1 (by rfl) ⟨7139780, by rfl⟩ : syracuseStep 9519707 = 14279561) B14279561
theorem B130204301 : Blo 1648023 130204301 := bstep (se 3 (by rfl) ⟨24413306, by rfl⟩ : syracuseStep 130204301 = 48826613) B48826613
theorem B40641227 : Blo 1648023 40641227 := bstep (se 1 (by rfl) ⟨30480920, by rfl⟩ : syracuseStep 40641227 = 60961841) B60961841
theorem B26739629 : Blo 1648023 26739629 := bstep (se 3 (by rfl) ⟨5013680, by rfl⟩ : syracuseStep 26739629 = 10027361) B10027361
theorem B28181681 : Blo 1648023 28181681 := bstep (se 2 (by rfl) ⟨10568130, by rfl⟩ : syracuseStep 28181681 = 21136261) B21136261
theorem B21128471 : Blo 1648023 21128471 := bstep (se 1 (by rfl) ⟨15846353, by rfl⟩ : syracuseStep 21128471 = 31692707) B31692707
theorem B4695353 : Blo 1648023 4695353 := bstep (se 2 (by rfl) ⟨1760757, by rfl⟩ : syracuseStep 4695353 = 3521515) B3521515
theorem B8463811 : Blo 1648023 8463811 := bstep (se 1 (by rfl) ⟨6347858, by rfl⟩ : syracuseStep 8463811 = 12695717) B12695717
theorem B26740205 : Blo 1648023 26740205 := bstep (se 3 (by rfl) ⟨5013788, by rfl⟩ : syracuseStep 26740205 = 10027577) B10027577
theorem B1648283 : Blo 1648023 1648283 := bstep (se 1 (by rfl) ⟨1236212, by rfl⟩ : syracuseStep 1648283 = 2472425) B2472425
theorem B5564159 : Blo 1648023 5564159 := bstep (se 1 (by rfl) ⟨4173119, by rfl⟩ : syracuseStep 5564159 = 8346239) B8346239
theorem B1648703 : Blo 1648023 1648703 := bstep (se 1 (by rfl) ⟨1236527, by rfl⟩ : syracuseStep 1648703 = 2473055) B2473055
theorem B1649243 : Blo 1648023 1649243 := bstep (se 1 (by rfl) ⟨1236932, by rfl⟩ : syracuseStep 1649243 = 2473865) B2473865
theorem B4172735 : Blo 1648023 4172735 := bstep (se 1 (by rfl) ⟨3129551, by rfl⟩ : syracuseStep 4172735 = 6259103) B6259103
theorem B1854463 : Blo 1648023 1854463 := bstep (se 1 (by rfl) ⟨1390847, by rfl⟩ : syracuseStep 1854463 = 2781695) B2781695
theorem B33827969 : Blo 1648023 33827969 := bstep (se 2 (by rfl) ⟨12685488, by rfl⟩ : syracuseStep 33827969 = 25370977) B25370977
theorem B22572233 : Blo 1648023 22572233 := bstep (se 2 (by rfl) ⟨8464587, by rfl⟩ : syracuseStep 22572233 = 16929175) B16929175
theorem B5565779 : Blo 1648023 5565779 := bstep (se 1 (by rfl) ⟨4174334, by rfl⟩ : syracuseStep 5565779 = 8348669) B8348669
theorem B14274089 : Blo 1648023 14274089 := bstep (se 2 (by rfl) ⟨5352783, by rfl⟩ : syracuseStep 14274089 = 10705567) B10705567
theorem B4173403 : Blo 1648023 4173403 := bstep (se 1 (by rfl) ⟨3130052, by rfl⟩ : syracuseStep 4173403 = 6260105) B6260105
theorem B31682249 : Blo 1648023 31682249 := bstep (se 2 (by rfl) ⟨11880843, by rfl⟩ : syracuseStep 31682249 = 23761687) B23761687
theorem B9392071 : Blo 1648023 9392071 := bstep (se 1 (by rfl) ⟨7044053, by rfl⟩ : syracuseStep 9392071 = 14088107) B14088107
theorem B92762279 : Blo 1648023 92762279 := bstep (se 1 (by rfl) ⟨69571709, by rfl⟩ : syracuseStep 92762279 = 139143419) B139143419
theorem B28177307 : Blo 1648023 28177307 := bstep (se 1 (by rfl) ⟨21132980, by rfl⟩ : syracuseStep 28177307 = 42265961) B42265961
theorem B22565945 : Blo 1648023 22565945 := bstep (se 2 (by rfl) ⟨8462229, by rfl⟩ : syracuseStep 22565945 = 16924459) B16924459
theorem B5281195 : Blo 1648023 5281195 := bstep (se 1 (by rfl) ⟨3960896, by rfl⟩ : syracuseStep 5281195 = 7921793) B7921793
theorem B2971495 : Blo 1648023 2971495 := bstep (se 1 (by rfl) ⟨2228621, by rfl⟩ : syracuseStep 2971495 = 4457243) B4457243
theorem B3708863 : Blo 1648023 3708863 := bstep (se 1 (by rfl) ⟨2781647, by rfl⟩ : syracuseStep 3708863 = 5563295) B5563295
theorem B2086879 : Blo 1648023 2086879 := bstep (se 1 (by rfl) ⟨1565159, by rfl⟩ : syracuseStep 2086879 = 3130319) B3130319
theorem B2783227 : Blo 1648023 2783227 := bstep (se 1 (by rfl) ⟨2087420, by rfl⟩ : syracuseStep 2783227 = 4174841) B4174841
theorem B6518839 : Blo 1648023 6518839 := bstep (se 1 (by rfl) ⟨4889129, by rfl⟩ : syracuseStep 6518839 = 9778259) B9778259
theorem B2783369 : Blo 1648023 2783369 := bstep (se 2 (by rfl) ⟨1043763, by rfl⟩ : syracuseStep 2783369 = 2087527) B2087527
theorem B8345753 : Blo 1648023 8345753 := bstep (se 2 (by rfl) ⟨3129657, by rfl⟩ : syracuseStep 8345753 = 6259315) B6259315
theorem B3709979 : Blo 1648023 3709979 := bstep (se 1 (by rfl) ⟨2782484, by rfl⟩ : syracuseStep 3709979 = 5564969) B5564969
theorem B3710015 : Blo 1648023 3710015 := bstep (se 1 (by rfl) ⟨2782511, by rfl⟩ : syracuseStep 3710015 = 5565023) B5565023
theorem B14081273 : Blo 1648023 14081273 := bstep (se 2 (by rfl) ⟨5280477, by rfl⟩ : syracuseStep 14081273 = 10560955) B10560955
theorem B3710879 : Blo 1648023 3710879 := bstep (se 1 (by rfl) ⟨2783159, by rfl⟩ : syracuseStep 3710879 = 5566319) B5566319
theorem B21119039 : Blo 1648023 21119039 := bstep (se 1 (by rfl) ⟨15839279, by rfl⟩ : syracuseStep 21119039 = 31678559) B31678559
theorem B8691785 : Blo 1648023 8691785 := bstep (se 2 (by rfl) ⟨3259419, by rfl⟩ : syracuseStep 8691785 = 6518839) B6518839
theorem B61841519 : Blo 1648023 61841519 := bstep (se 1 (by rfl) ⟨46381139, by rfl⟩ : syracuseStep 61841519 = 92762279) B92762279
theorem B4456637 : Blo 1648023 4456637 := bstep (se 3 (by rfl) ⟨835619, by rfl⟩ : syracuseStep 4456637 = 1671239) B1671239
theorem B18784871 : Blo 1648023 18784871 := bstep (se 1 (by rfl) ⟨14088653, by rfl⟩ : syracuseStep 18784871 = 28177307) B28177307
theorem B17826419 : Blo 1648023 17826419 := bstep (se 1 (by rfl) ⟨13369814, by rfl⟩ : syracuseStep 17826419 = 26739629) B26739629
theorem B3130235 : Blo 1648023 3130235 := bstep (se 1 (by rfl) ⟨2347676, by rfl⟩ : syracuseStep 3130235 = 4695353) B4695353
theorem B17826803 : Blo 1648023 17826803 := bstep (se 1 (by rfl) ⟨13370102, by rfl⟩ : syracuseStep 17826803 = 26740205) B26740205
theorem B5563835 : Blo 1648023 5563835 := bstep (se 1 (by rfl) ⟨4172876, by rfl⟩ : syracuseStep 5563835 = 8345753) B8345753
theorem B347211469 : Blo 1648023 347211469 := bstep (se 3 (by rfl) ⟨65102150, by rfl⟩ : syracuseStep 347211469 = 130204301) B130204301
theorem B5564537 : Blo 1648023 5564537 := bstep (se 2 (by rfl) ⟨2086701, by rfl⟩ : syracuseStep 5564537 = 4173403) B4173403
theorem B21121499 : Blo 1648023 21121499 := bstep (se 1 (by rfl) ⟨15841124, by rfl⟩ : syracuseStep 21121499 = 31682249) B31682249
theorem B1649439 : Blo 1648023 1649439 := bstep (se 1 (by rfl) ⟨1237079, by rfl⟩ : syracuseStep 1649439 = 2474159) B2474159
theorem B1649471 : Blo 1648023 1649471 := bstep (se 1 (by rfl) ⟨1237103, by rfl⟩ : syracuseStep 1649471 = 2474207) B2474207
theorem B27094151 : Blo 1648023 27094151 := bstep (se 1 (by rfl) ⟨20320613, by rfl⟩ : syracuseStep 27094151 = 40641227) B40641227
theorem B15043963 : Blo 1648023 15043963 := bstep (se 1 (by rfl) ⟨11282972, by rfl⟩ : syracuseStep 15043963 = 22565945) B22565945
theorem B18787787 : Blo 1648023 18787787 := bstep (se 1 (by rfl) ⟨14090840, by rfl⟩ : syracuseStep 18787787 = 28181681) B28181681
theorem B14085647 : Blo 1648023 14085647 := bstep (se 1 (by rfl) ⟨10564235, by rfl⟩ : syracuseStep 14085647 = 21128471) B21128471
theorem B1855579 : Blo 1648023 1855579 := bstep (se 1 (by rfl) ⟨1391684, by rfl⟩ : syracuseStep 1855579 = 2783369) B2783369
theorem B15847973 : Blo 1648023 15847973 := bstep (se 4 (by rfl) ⟨1485747, by rfl⟩ : syracuseStep 15847973 = 2971495) B2971495
theorem B7041593 : Blo 1648023 7041593 := bstep (se 2 (by rfl) ⟨2640597, by rfl⟩ : syracuseStep 7041593 = 5281195) B5281195
theorem B11285081 : Blo 1648023 11285081 := bstep (se 2 (by rfl) ⟨4231905, by rfl⟩ : syracuseStep 11285081 = 8463811) B8463811
theorem B2781823 : Blo 1648023 2781823 := bstep (se 1 (by rfl) ⟨2086367, by rfl⟩ : syracuseStep 2781823 = 4172735) B4172735
theorem B9516059 : Blo 1648023 9516059 := bstep (se 1 (by rfl) ⟨7137044, by rfl⟩ : syracuseStep 9516059 = 14274089) B14274089
theorem B12522761 : Blo 1648023 12522761 := bstep (se 2 (by rfl) ⟨4696035, by rfl⟩ : syracuseStep 12522761 = 9392071) B9392071
theorem B2782505 : Blo 1648023 2782505 := bstep (se 2 (by rfl) ⟨1043439, by rfl⟩ : syracuseStep 2782505 = 2086879) B2086879
theorem B9393529 : Blo 1648023 9393529 := bstep (se 2 (by rfl) ⟨3522573, by rfl⟩ : syracuseStep 9393529 = 7045147) B7045147
theorem B3709439 : Blo 1648023 3709439 := bstep (se 1 (by rfl) ⟨2782079, by rfl⟩ : syracuseStep 3709439 = 5564159) B5564159
theorem B2472575 : Blo 1648023 2472575 := bstep (se 1 (by rfl) ⟨1854431, by rfl⟩ : syracuseStep 2472575 = 3708863) B3708863
theorem B2472617 : Blo 1648023 2472617 := bstep (se 2 (by rfl) ⟨927231, by rfl⟩ : syracuseStep 2472617 = 1854463) B1854463
theorem B25385885 : Blo 1648023 25385885 := bstep (se 3 (by rfl) ⟨4759853, by rfl⟩ : syracuseStep 25385885 = 9519707) B9519707
theorem B2473319 : Blo 1648023 2473319 := bstep (se 1 (by rfl) ⟨1854989, by rfl⟩ : syracuseStep 2473319 = 3709979) B3709979
theorem B2473343 : Blo 1648023 2473343 := bstep (se 1 (by rfl) ⟨1855007, by rfl⟩ : syracuseStep 2473343 = 3710015) B3710015
theorem B22551979 : Blo 1648023 22551979 := bstep (se 1 (by rfl) ⟨16913984, by rfl⟩ : syracuseStep 22551979 = 33827969) B33827969
theorem B15048155 : Blo 1648023 15048155 := bstep (se 1 (by rfl) ⟨11286116, by rfl⟩ : syracuseStep 15048155 = 22572233) B22572233
theorem B9387515 : Blo 1648023 9387515 := bstep (se 1 (by rfl) ⟨7040636, by rfl⟩ : syracuseStep 9387515 = 14081273) B14081273
theorem B3710519 : Blo 1648023 3710519 := bstep (se 1 (by rfl) ⟨2782889, by rfl⟩ : syracuseStep 3710519 = 5565779) B5565779
theorem B2473919 : Blo 1648023 2473919 := bstep (se 1 (by rfl) ⟨1855439, by rfl⟩ : syracuseStep 2473919 = 3710879) B3710879
theorem B3710969 : Blo 1648023 3710969 := bstep (se 2 (by rfl) ⟨1391613, by rfl⟩ : syracuseStep 3710969 = 2783227) B2783227
theorem B2474105 : Blo 1648023 2474105 := bstep (se 2 (by rfl) ⟨927789, by rfl⟩ : syracuseStep 2474105 = 1855579) B1855579
theorem B8348507 : Blo 1648023 8348507 := bstep (se 1 (by rfl) ⟨6261380, by rfl⟩ : syracuseStep 8348507 = 12522761) B12522761
theorem B18777581 : Blo 1648023 18777581 := bstep (se 3 (by rfl) ⟨3520796, by rfl⟩ : syracuseStep 18777581 = 7041593) B7041593
theorem B1648383 : Blo 1648023 1648383 := bstep (se 1 (by rfl) ⟨1236287, by rfl⟩ : syracuseStep 1648383 = 2472575) B2472575
theorem B1648411 : Blo 1648023 1648411 := bstep (se 1 (by rfl) ⟨1236308, by rfl⟩ : syracuseStep 1648411 = 2472617) B2472617
theorem B1648879 : Blo 1648023 1648879 := bstep (se 1 (by rfl) ⟨1236659, by rfl⟩ : syracuseStep 1648879 = 2473319) B2473319
theorem B1648895 : Blo 1648023 1648895 := bstep (se 1 (by rfl) ⟨1236671, by rfl⟩ : syracuseStep 1648895 = 2473343) B2473343
theorem B462948625 : Blo 1648023 462948625 := bstep (se 2 (by rfl) ⟨173605734, by rfl⟩ : syracuseStep 462948625 = 347211469) B347211469
theorem B9390431 : Blo 1648023 9390431 := bstep (se 1 (by rfl) ⟨7042823, by rfl⟩ : syracuseStep 9390431 = 14085647) B14085647
theorem B1649279 : Blo 1648023 1649279 := bstep (se 1 (by rfl) ⟨1236959, by rfl⟩ : syracuseStep 1649279 = 2473919) B2473919
theorem B5794523 : Blo 1648023 5794523 := bstep (se 1 (by rfl) ⟨4345892, by rfl⟩ : syracuseStep 5794523 = 8691785) B8691785
theorem B7523387 : Blo 1648023 7523387 := bstep (se 1 (by rfl) ⟨5642540, by rfl⟩ : syracuseStep 7523387 = 11285081) B11285081
theorem B6344039 : Blo 1648023 6344039 := bstep (se 1 (by rfl) ⟨4758029, by rfl⟩ : syracuseStep 6344039 = 9516059) B9516059
theorem B2473979 : Blo 1648023 2473979 := bstep (se 1 (by rfl) ⟨1855484, by rfl⟩ : syracuseStep 2473979 = 3710969) B3710969
theorem B1855003 : Blo 1648023 1855003 := bstep (se 1 (by rfl) ⟨1391252, by rfl⟩ : syracuseStep 1855003 = 2782505) B2782505
theorem B20058617 : Blo 1648023 20058617 := bstep (se 2 (by rfl) ⟨7521981, by rfl⟩ : syracuseStep 20058617 = 15043963) B15043963
theorem B30069305 : Blo 1648023 30069305 := bstep (se 2 (by rfl) ⟨11275989, by rfl⟩ : syracuseStep 30069305 = 22551979) B22551979
theorem B10032103 : Blo 1648023 10032103 := bstep (se 1 (by rfl) ⟨7524077, by rfl⟩ : syracuseStep 10032103 = 15048155) B15048155
theorem B14079359 : Blo 1648023 14079359 := bstep (se 1 (by rfl) ⟨10559519, by rfl⟩ : syracuseStep 14079359 = 21119039) B21119039
theorem B41227679 : Blo 1648023 41227679 := bstep (se 1 (by rfl) ⟨30920759, by rfl⟩ : syracuseStep 41227679 = 61841519) B61841519
theorem B2971091 : Blo 1648023 2971091 := bstep (se 1 (by rfl) ⟨2228318, by rfl⟩ : syracuseStep 2971091 = 4456637) B4456637
theorem B10565315 : Blo 1648023 10565315 := bstep (se 1 (by rfl) ⟨7923986, by rfl⟩ : syracuseStep 10565315 = 15847973) B15847973
theorem B12523247 : Blo 1648023 12523247 := bstep (se 1 (by rfl) ⟨9392435, by rfl⟩ : syracuseStep 12523247 = 18784871) B18784871
theorem B11884279 : Blo 1648023 11884279 := bstep (se 1 (by rfl) ⟨8913209, by rfl⟩ : syracuseStep 11884279 = 17826419) B17826419
theorem B2086823 : Blo 1648023 2086823 := bstep (se 1 (by rfl) ⟨1565117, by rfl⟩ : syracuseStep 2086823 = 3130235) B3130235
theorem B11884535 : Blo 1648023 11884535 := bstep (se 1 (by rfl) ⟨8913401, by rfl⟩ : syracuseStep 11884535 = 17826803) B17826803
theorem B3709097 : Blo 1648023 3709097 := bstep (se 2 (by rfl) ⟨1390911, by rfl⟩ : syracuseStep 3709097 = 2781823) B2781823
theorem B3709223 : Blo 1648023 3709223 := bstep (se 1 (by rfl) ⟨2781917, by rfl⟩ : syracuseStep 3709223 = 5563835) B5563835
theorem B3709691 : Blo 1648023 3709691 := bstep (se 1 (by rfl) ⟨2782268, by rfl⟩ : syracuseStep 3709691 = 5564537) B5564537
theorem B14080999 : Blo 1648023 14080999 := bstep (se 1 (by rfl) ⟨10560749, by rfl⟩ : syracuseStep 14080999 = 21121499) B21121499
theorem B2472959 : Blo 1648023 2472959 := bstep (se 1 (by rfl) ⟨1854719, by rfl⟩ : syracuseStep 2472959 = 3709439) B3709439
theorem B12524705 : Blo 1648023 12524705 := bstep (se 2 (by rfl) ⟨4696764, by rfl⟩ : syracuseStep 12524705 = 9393529) B9393529
theorem B16923923 : Blo 1648023 16923923 := bstep (se 1 (by rfl) ⟨12692942, by rfl⟩ : syracuseStep 16923923 = 25385885) B25385885
theorem B18062767 : Blo 1648023 18062767 := bstep (se 1 (by rfl) ⟨13547075, by rfl⟩ : syracuseStep 18062767 = 27094151) B27094151
theorem B12525191 : Blo 1648023 12525191 := bstep (se 1 (by rfl) ⟨9393893, by rfl⟩ : syracuseStep 12525191 = 18787787) B18787787
theorem B6258343 : Blo 1648023 6258343 := bstep (se 1 (by rfl) ⟨4693757, by rfl⟩ : syracuseStep 6258343 = 9387515) B9387515
theorem B2473679 : Blo 1648023 2473679 := bstep (se 1 (by rfl) ⟨1855259, by rfl⟩ : syracuseStep 2473679 = 3710519) B3710519
theorem B20046203 : Blo 1648023 20046203 := bstep (se 1 (by rfl) ⟨15034652, by rfl⟩ : syracuseStep 20046203 = 30069305) B30069305
theorem B16917437 : Blo 1648023 16917437 := bstep (se 3 (by rfl) ⟨3172019, by rfl⟩ : syracuseStep 16917437 = 6344039) B6344039
theorem B27485119 : Blo 1648023 27485119 := bstep (se 1 (by rfl) ⟨20613839, by rfl⟩ : syracuseStep 27485119 = 41227679) B41227679
theorem B12518387 : Blo 1648023 12518387 := bstep (se 1 (by rfl) ⟨9388790, by rfl⟩ : syracuseStep 12518387 = 18777581) B18777581
theorem B8348831 : Blo 1648023 8348831 := bstep (se 1 (by rfl) ⟨6261623, by rfl⟩ : syracuseStep 8348831 = 12523247) B12523247
theorem B7922909 : Blo 1648023 7922909 := bstep (se 3 (by rfl) ⟨1485545, by rfl⟩ : syracuseStep 7922909 = 2971091) B2971091
theorem B7923023 : Blo 1648023 7923023 := bstep (se 1 (by rfl) ⟨5942267, by rfl⟩ : syracuseStep 7923023 = 11884535) B11884535
theorem B6260287 : Blo 1648023 6260287 := bstep (se 1 (by rfl) ⟨4695215, by rfl⟩ : syracuseStep 6260287 = 9390431) B9390431
theorem B1648639 : Blo 1648023 1648639 := bstep (se 1 (by rfl) ⟨1236479, by rfl⟩ : syracuseStep 1648639 = 2472959) B2472959
theorem B5015591 : Blo 1648023 5015591 := bstep (se 1 (by rfl) ⟨3761693, by rfl⟩ : syracuseStep 5015591 = 7523387) B7523387
theorem B8349803 : Blo 1648023 8349803 := bstep (se 1 (by rfl) ⟨6262352, by rfl⟩ : syracuseStep 8349803 = 12524705) B12524705
theorem B11282615 : Blo 1648023 11282615 := bstep (se 1 (by rfl) ⟨8461961, by rfl⟩ : syracuseStep 11282615 = 16923923) B16923923
theorem B15845705 : Blo 1648023 15845705 := bstep (se 2 (by rfl) ⟨5942139, by rfl⟩ : syracuseStep 15845705 = 11884279) B11884279
theorem B8350127 : Blo 1648023 8350127 := bstep (se 1 (by rfl) ⟨6262595, by rfl⟩ : syracuseStep 8350127 = 12525191) B12525191
theorem B5564861 : Blo 1648023 5564861 := bstep (se 3 (by rfl) ⟨1043411, by rfl⟩ : syracuseStep 5564861 = 2086823) B2086823
theorem B1649119 : Blo 1648023 1649119 := bstep (se 1 (by rfl) ⟨1236839, by rfl⟩ : syracuseStep 1649119 = 2473679) B2473679
theorem B1649319 : Blo 1648023 1649319 := bstep (se 1 (by rfl) ⟨1236989, by rfl⟩ : syracuseStep 1649319 = 2473979) B2473979
theorem B1649403 : Blo 1648023 1649403 := bstep (se 1 (by rfl) ⟨1237052, by rfl⟩ : syracuseStep 1649403 = 2474105) B2474105
theorem B13372411 : Blo 1648023 13372411 := bstep (se 1 (by rfl) ⟨10029308, by rfl⟩ : syracuseStep 13372411 = 20058617) B20058617
theorem B5565671 : Blo 1648023 5565671 := bstep (se 1 (by rfl) ⟨4174253, by rfl⟩ : syracuseStep 5565671 = 8348507) B8348507
theorem B3863015 : Blo 1648023 3863015 := bstep (se 1 (by rfl) ⟨2897261, by rfl⟩ : syracuseStep 3863015 = 5794523) B5794523
theorem B8344457 : Blo 1648023 8344457 := bstep (se 2 (by rfl) ⟨3129171, by rfl⟩ : syracuseStep 8344457 = 6258343) B6258343
theorem B617264833 : Blo 1648023 617264833 := bstep (se 2 (by rfl) ⟨231474312, by rfl⟩ : syracuseStep 617264833 = 462948625) B462948625
theorem B9386239 : Blo 1648023 9386239 := bstep (se 1 (by rfl) ⟨7039679, by rfl⟩ : syracuseStep 9386239 = 14079359) B14079359
theorem B7043543 : Blo 1648023 7043543 := bstep (se 1 (by rfl) ⟨5282657, by rfl⟩ : syracuseStep 7043543 = 10565315) B10565315
theorem B18774665 : Blo 1648023 18774665 := bstep (se 2 (by rfl) ⟨7040499, by rfl⟩ : syracuseStep 18774665 = 14080999) B14080999
theorem B13376137 : Blo 1648023 13376137 := bstep (se 2 (by rfl) ⟨5016051, by rfl⟩ : syracuseStep 13376137 = 10032103) B10032103
theorem B2472731 : Blo 1648023 2472731 := bstep (se 1 (by rfl) ⟨1854548, by rfl⟩ : syracuseStep 2472731 = 3709097) B3709097
theorem B2472815 : Blo 1648023 2472815 := bstep (se 1 (by rfl) ⟨1854611, by rfl⟩ : syracuseStep 2472815 = 3709223) B3709223
theorem B2473127 : Blo 1648023 2473127 := bstep (se 1 (by rfl) ⟨1854845, by rfl⟩ : syracuseStep 2473127 = 3709691) B3709691
theorem B24083689 : Blo 1648023 24083689 := bstep (se 2 (by rfl) ⟨9031383, by rfl⟩ : syracuseStep 24083689 = 18062767) B18062767
theorem B2473337 : Blo 1648023 2473337 := bstep (se 2 (by rfl) ⟨927501, by rfl⟩ : syracuseStep 2473337 = 1855003) B1855003
theorem B5562971 : Blo 1648023 5562971 := bstep (se 1 (by rfl) ⟨4172228, by rfl⟩ : syracuseStep 5562971 = 8344457) B8344457
theorem B17834849 : Blo 1648023 17834849 := bstep (se 2 (by rfl) ⟨6688068, by rfl⟩ : syracuseStep 17834849 = 13376137) B13376137
theorem B3343727 : Blo 1648023 3343727 := bstep (se 1 (by rfl) ⟨2507795, by rfl⟩ : syracuseStep 3343727 = 5015591) B5015591
theorem B7521743 : Blo 1648023 7521743 := bstep (se 1 (by rfl) ⟨5641307, by rfl⟩ : syracuseStep 7521743 = 11282615) B11282615
theorem B4695695 : Blo 1648023 4695695 := bstep (se 1 (by rfl) ⟨3521771, by rfl⟩ : syracuseStep 4695695 = 7043543) B7043543
theorem B1648487 : Blo 1648023 1648487 := bstep (se 1 (by rfl) ⟨1236365, by rfl⟩ : syracuseStep 1648487 = 2472731) B2472731
theorem B1648543 : Blo 1648023 1648543 := bstep (se 1 (by rfl) ⟨1236407, by rfl⟩ : syracuseStep 1648543 = 2472815) B2472815
theorem B1648751 : Blo 1648023 1648751 := bstep (se 1 (by rfl) ⟨1236563, by rfl⟩ : syracuseStep 1648751 = 2473127) B2473127
theorem B1648891 : Blo 1648023 1648891 := bstep (se 1 (by rfl) ⟨1236668, by rfl⟩ : syracuseStep 1648891 = 2473337) B2473337
theorem B823019777 : Blo 1648023 823019777 := bstep (se 2 (by rfl) ⟨308632416, by rfl⟩ : syracuseStep 823019777 = 617264833) B617264833
theorem B13364135 : Blo 1648023 13364135 := bstep (se 1 (by rfl) ⟨10023101, by rfl⟩ : syracuseStep 13364135 = 20046203) B20046203
theorem B2575343 : Blo 1648023 2575343 := bstep (se 1 (by rfl) ⟨1931507, by rfl⟩ : syracuseStep 2575343 = 3863015) B3863015
theorem B5565887 : Blo 1648023 5565887 := bstep (se 1 (by rfl) ⟨4174415, by rfl⟩ : syracuseStep 5565887 = 8348831) B8348831
theorem B36646825 : Blo 1648023 36646825 := bstep (se 2 (by rfl) ⟨13742559, by rfl⟩ : syracuseStep 36646825 = 27485119) B27485119
theorem B17829881 : Blo 1648023 17829881 := bstep (se 2 (by rfl) ⟨6686205, by rfl⟩ : syracuseStep 17829881 = 13372411) B13372411
theorem B5566535 : Blo 1648023 5566535 := bstep (se 1 (by rfl) ⟨4174901, by rfl⟩ : syracuseStep 5566535 = 8349803) B8349803
theorem B10563803 : Blo 1648023 10563803 := bstep (se 1 (by rfl) ⟨7922852, by rfl⟩ : syracuseStep 10563803 = 15845705) B15845705
theorem B5566751 : Blo 1648023 5566751 := bstep (se 1 (by rfl) ⟨4175063, by rfl⟩ : syracuseStep 5566751 = 8350127) B8350127
theorem B12514985 : Blo 1648023 12514985 := bstep (se 2 (by rfl) ⟨4693119, by rfl⟩ : syracuseStep 12514985 = 9386239) B9386239
theorem B11278291 : Blo 1648023 11278291 := bstep (se 1 (by rfl) ⟨8458718, by rfl⟩ : syracuseStep 11278291 = 16917437) B16917437
theorem B8345591 : Blo 1648023 8345591 := bstep (se 1 (by rfl) ⟨6259193, by rfl⟩ : syracuseStep 8345591 = 12518387) B12518387
theorem B5281939 : Blo 1648023 5281939 := bstep (se 1 (by rfl) ⟨3961454, by rfl⟩ : syracuseStep 5281939 = 7922909) B7922909
theorem B5282015 : Blo 1648023 5282015 := bstep (se 1 (by rfl) ⟨3961511, by rfl⟩ : syracuseStep 5282015 = 7923023) B7923023
theorem B3709907 : Blo 1648023 3709907 := bstep (se 1 (by rfl) ⟨2782430, by rfl⟩ : syracuseStep 3709907 = 5564861) B5564861
theorem B32111585 : Blo 1648023 32111585 := bstep (se 2 (by rfl) ⟨12041844, by rfl⟩ : syracuseStep 32111585 = 24083689) B24083689
theorem B12516443 : Blo 1648023 12516443 := bstep (se 1 (by rfl) ⟨9387332, by rfl⟩ : syracuseStep 12516443 = 18774665) B18774665
theorem B8347049 : Blo 1648023 8347049 := bstep (se 2 (by rfl) ⟨3130143, by rfl⟩ : syracuseStep 8347049 = 6260287) B6260287
theorem B3710447 : Blo 1648023 3710447 := bstep (se 1 (by rfl) ⟨2782835, by rfl⟩ : syracuseStep 3710447 = 5565671) B5565671
theorem B3711023 : Blo 1648023 3711023 := bstep (se 1 (by rfl) ⟨2783267, by rfl⟩ : syracuseStep 3711023 = 5566535) B5566535
theorem B3711167 : Blo 1648023 3711167 := bstep (se 1 (by rfl) ⟨2783375, by rfl⟩ : syracuseStep 3711167 = 5566751) B5566751
theorem B5014495 : Blo 1648023 5014495 := bstep (se 1 (by rfl) ⟨3760871, by rfl⟩ : syracuseStep 5014495 = 7521743) B7521743
theorem B3130463 : Blo 1648023 3130463 := bstep (se 1 (by rfl) ⟨2347847, by rfl⟩ : syracuseStep 3130463 = 4695695) B4695695
theorem B5563727 : Blo 1648023 5563727 := bstep (se 1 (by rfl) ⟨4172795, by rfl⟩ : syracuseStep 5563727 = 8345591) B8345591
theorem B21407723 : Blo 1648023 21407723 := bstep (se 1 (by rfl) ⟨16055792, by rfl⟩ : syracuseStep 21407723 = 32111585) B32111585
theorem B5564699 : Blo 1648023 5564699 := bstep (se 1 (by rfl) ⟨4173524, by rfl⟩ : syracuseStep 5564699 = 8347049) B8347049
theorem B11886587 : Blo 1648023 11886587 := bstep (se 1 (by rfl) ⟨8914940, by rfl⟩ : syracuseStep 11886587 = 17829881) B17829881
theorem B11889899 : Blo 1648023 11889899 := bstep (se 1 (by rfl) ⟨8917424, by rfl⟩ : syracuseStep 11889899 = 17834849) B17834849
theorem B14085373 : Blo 1648023 14085373 := bstep (se 3 (by rfl) ⟨2641007, by rfl⟩ : syracuseStep 14085373 = 5282015) B5282015
theorem B8916605 : Blo 1648023 8916605 := bstep (se 3 (by rfl) ⟨1671863, by rfl⟩ : syracuseStep 8916605 = 3343727) B3343727
theorem B8343323 : Blo 1648023 8343323 := bstep (se 1 (by rfl) ⟨6257492, by rfl⟩ : syracuseStep 8343323 = 12514985) B12514985
theorem B548679851 : Blo 1648023 548679851 := bstep (se 1 (by rfl) ⟨411509888, by rfl⟩ : syracuseStep 548679851 = 823019777) B823019777
theorem B8909423 : Blo 1648023 8909423 := bstep (se 1 (by rfl) ⟨6682067, by rfl⟩ : syracuseStep 8909423 = 13364135) B13364135
theorem B1716895 : Blo 1648023 1716895 := bstep (se 1 (by rfl) ⟨1287671, by rfl⟩ : syracuseStep 1716895 = 2575343) B2575343
theorem B8344295 : Blo 1648023 8344295 := bstep (se 1 (by rfl) ⟨6258221, by rfl⟩ : syracuseStep 8344295 = 12516443) B12516443
theorem B48862433 : Blo 1648023 48862433 := bstep (se 2 (by rfl) ⟨18323412, by rfl⟩ : syracuseStep 48862433 = 36646825) B36646825
theorem B15037721 : Blo 1648023 15037721 := bstep (se 2 (by rfl) ⟨5639145, by rfl⟩ : syracuseStep 15037721 = 11278291) B11278291
theorem B7042535 : Blo 1648023 7042535 := bstep (se 1 (by rfl) ⟨5281901, by rfl⟩ : syracuseStep 7042535 = 10563803) B10563803
theorem B7042585 : Blo 1648023 7042585 := bstep (se 2 (by rfl) ⟨2640969, by rfl⟩ : syracuseStep 7042585 = 5281939) B5281939
theorem B3708647 : Blo 1648023 3708647 := bstep (se 1 (by rfl) ⟨2781485, by rfl⟩ : syracuseStep 3708647 = 5562971) B5562971
theorem B2473271 : Blo 1648023 2473271 := bstep (se 1 (by rfl) ⟨1854953, by rfl⟩ : syracuseStep 2473271 = 3709907) B3709907
theorem B3710591 : Blo 1648023 3710591 := bstep (se 1 (by rfl) ⟨2782943, by rfl⟩ : syracuseStep 3710591 = 5565887) B5565887
theorem B2473631 : Blo 1648023 2473631 := bstep (se 1 (by rfl) ⟨1855223, by rfl⟩ : syracuseStep 2473631 = 3710447) B3710447
theorem B2474015 : Blo 1648023 2474015 := bstep (se 1 (by rfl) ⟨1855511, by rfl⟩ : syracuseStep 2474015 = 3711023) B3711023
theorem B2474111 : Blo 1648023 2474111 := bstep (se 1 (by rfl) ⟨1855583, by rfl⟩ : syracuseStep 2474111 = 3711167) B3711167
theorem B5939615 : Blo 1648023 5939615 := bstep (se 1 (by rfl) ⟨4454711, by rfl⟩ : syracuseStep 5939615 = 8909423) B8909423
theorem B5562863 : Blo 1648023 5562863 := bstep (se 1 (by rfl) ⟨4172147, by rfl⟩ : syracuseStep 5562863 = 8344295) B8344295
theorem B4695023 : Blo 1648023 4695023 := bstep (se 1 (by rfl) ⟨3521267, by rfl⟩ : syracuseStep 4695023 = 7042535) B7042535
theorem B6685993 : Blo 1648023 6685993 := bstep (se 2 (by rfl) ⟨2507247, by rfl⟩ : syracuseStep 6685993 = 5014495) B5014495
theorem B14271815 : Blo 1648023 14271815 := bstep (se 1 (by rfl) ⟨10703861, by rfl⟩ : syracuseStep 14271815 = 21407723) B21407723
theorem B9390113 : Blo 1648023 9390113 := bstep (se 2 (by rfl) ⟨3521292, by rfl⟩ : syracuseStep 9390113 = 7042585) B7042585
theorem B1648847 : Blo 1648023 1648847 := bstep (se 1 (by rfl) ⟨1236635, by rfl⟩ : syracuseStep 1648847 = 2473271) B2473271
theorem B1649087 : Blo 1648023 1649087 := bstep (se 1 (by rfl) ⟨1236815, by rfl⟩ : syracuseStep 1649087 = 2473631) B2473631
theorem B7924391 : Blo 1648023 7924391 := bstep (se 1 (by rfl) ⟨5943293, by rfl⟩ : syracuseStep 7924391 = 11886587) B11886587
theorem B32574955 : Blo 1648023 32574955 := bstep (se 1 (by rfl) ⟨24431216, by rfl⟩ : syracuseStep 32574955 = 48862433) B48862433
theorem B18780497 : Blo 1648023 18780497 := bstep (se 2 (by rfl) ⟨7042686, by rfl⟩ : syracuseStep 18780497 = 14085373) B14085373
theorem B7926599 : Blo 1648023 7926599 := bstep (se 1 (by rfl) ⟨5944949, by rfl⟩ : syracuseStep 7926599 = 11889899) B11889899
theorem B5944403 : Blo 1648023 5944403 := bstep (se 1 (by rfl) ⟨4458302, by rfl⟩ : syracuseStep 5944403 = 8916605) B8916605
theorem B365786567 : Blo 1648023 365786567 := bstep (se 1 (by rfl) ⟨274339925, by rfl⟩ : syracuseStep 365786567 = 548679851) B548679851
theorem B2086975 : Blo 1648023 2086975 := bstep (se 1 (by rfl) ⟨1565231, by rfl⟩ : syracuseStep 2086975 = 3130463) B3130463
theorem B9156773 : Blo 1648023 9156773 := bstep (se 4 (by rfl) ⟨858447, by rfl⟩ : syracuseStep 9156773 = 1716895) B1716895
theorem B10025147 : Blo 1648023 10025147 := bstep (se 1 (by rfl) ⟨7518860, by rfl⟩ : syracuseStep 10025147 = 15037721) B15037721
theorem B3709151 : Blo 1648023 3709151 := bstep (se 1 (by rfl) ⟨2781863, by rfl⟩ : syracuseStep 3709151 = 5563727) B5563727
theorem B2472431 : Blo 1648023 2472431 := bstep (se 1 (by rfl) ⟨1854323, by rfl⟩ : syracuseStep 2472431 = 3708647) B3708647
theorem B3709799 : Blo 1648023 3709799 := bstep (se 1 (by rfl) ⟨2782349, by rfl⟩ : syracuseStep 3709799 = 5564699) B5564699
theorem B2473727 : Blo 1648023 2473727 := bstep (se 1 (by rfl) ⟨1855295, by rfl⟩ : syracuseStep 2473727 = 3710591) B3710591
theorem B5562215 : Blo 1648023 5562215 := bstep (se 1 (by rfl) ⟨4171661, by rfl⟩ : syracuseStep 5562215 = 8343323) B8343323
theorem B3130015 : Blo 1648023 3130015 := bstep (se 1 (by rfl) ⟨2347511, by rfl⟩ : syracuseStep 3130015 = 4695023) B4695023
theorem B6260075 : Blo 1648023 6260075 := bstep (se 1 (by rfl) ⟨4695056, by rfl⟩ : syracuseStep 6260075 = 9390113) B9390113
theorem B1648287 : Blo 1648023 1648287 := bstep (se 1 (by rfl) ⟨1236215, by rfl⟩ : syracuseStep 1648287 = 2472431) B2472431
theorem B8914657 : Blo 1648023 8914657 := bstep (se 2 (by rfl) ⟨3342996, by rfl⟩ : syracuseStep 8914657 = 6685993) B6685993
theorem B21137597 : Blo 1648023 21137597 := bstep (se 3 (by rfl) ⟨3963299, by rfl⟩ : syracuseStep 21137597 = 7926599) B7926599
theorem B1649151 : Blo 1648023 1649151 := bstep (se 1 (by rfl) ⟨1236863, by rfl⟩ : syracuseStep 1649151 = 2473727) B2473727
theorem B1649343 : Blo 1648023 1649343 := bstep (se 1 (by rfl) ⟨1237007, by rfl⟩ : syracuseStep 1649343 = 2474015) B2474015
theorem B1649407 : Blo 1648023 1649407 := bstep (se 1 (by rfl) ⟨1237055, by rfl⟩ : syracuseStep 1649407 = 2474111) B2474111
theorem B12520331 : Blo 1648023 12520331 := bstep (se 1 (by rfl) ⟨9390248, by rfl⟩ : syracuseStep 12520331 = 18780497) B18780497
theorem B9514543 : Blo 1648023 9514543 := bstep (se 1 (by rfl) ⟨7135907, by rfl⟩ : syracuseStep 9514543 = 14271815) B14271815
theorem B15838973 : Blo 1648023 15838973 := bstep (se 3 (by rfl) ⟨2969807, by rfl⟩ : syracuseStep 15838973 = 5939615) B5939615
theorem B3708143 : Blo 1648023 3708143 := bstep (se 1 (by rfl) ⟨2781107, by rfl⟩ : syracuseStep 3708143 = 5562215) B5562215
theorem B2782633 : Blo 1648023 2782633 := bstep (se 2 (by rfl) ⟨1043487, by rfl⟩ : syracuseStep 2782633 = 2086975) B2086975
theorem B3708575 : Blo 1648023 3708575 := bstep (se 1 (by rfl) ⟨2781431, by rfl⟩ : syracuseStep 3708575 = 5562863) B5562863
theorem B24418061 : Blo 1648023 24418061 := bstep (se 3 (by rfl) ⟨4578386, by rfl⟩ : syracuseStep 24418061 = 9156773) B9156773
theorem B3962935 : Blo 1648023 3962935 := bstep (se 1 (by rfl) ⟨2972201, by rfl⟩ : syracuseStep 3962935 = 5944403) B5944403
theorem B243857711 : Blo 1648023 243857711 := bstep (se 1 (by rfl) ⟨182893283, by rfl⟩ : syracuseStep 243857711 = 365786567) B365786567
theorem B6683431 : Blo 1648023 6683431 := bstep (se 1 (by rfl) ⟨5012573, by rfl⟩ : syracuseStep 6683431 = 10025147) B10025147
theorem B2472767 : Blo 1648023 2472767 := bstep (se 1 (by rfl) ⟨1854575, by rfl⟩ : syracuseStep 2472767 = 3709151) B3709151
theorem B5282927 : Blo 1648023 5282927 := bstep (se 1 (by rfl) ⟨3962195, by rfl⟩ : syracuseStep 5282927 = 7924391) B7924391
theorem B2473199 : Blo 1648023 2473199 := bstep (se 1 (by rfl) ⟨1854899, by rfl⟩ : syracuseStep 2473199 = 3709799) B3709799
theorem B43433273 : Blo 1648023 43433273 := bstep (se 2 (by rfl) ⟨16287477, by rfl⟩ : syracuseStep 43433273 = 32574955) B32574955
theorem B5283913 : Blo 1648023 5283913 := bstep (se 2 (by rfl) ⟨1981467, by rfl⟩ : syracuseStep 5283913 = 3962935) B3962935
theorem B16278707 : Blo 1648023 16278707 := bstep (se 1 (by rfl) ⟨12209030, by rfl⟩ : syracuseStep 16278707 = 24418061) B24418061
theorem B14091731 : Blo 1648023 14091731 := bstep (se 1 (by rfl) ⟨10568798, by rfl⟩ : syracuseStep 14091731 = 21137597) B21137597
theorem B162571807 : Blo 1648023 162571807 := bstep (se 1 (by rfl) ⟨121928855, by rfl⟩ : syracuseStep 162571807 = 243857711) B243857711
theorem B1648511 : Blo 1648023 1648511 := bstep (se 1 (by rfl) ⟨1236383, by rfl⟩ : syracuseStep 1648511 = 2472767) B2472767
theorem B1648799 : Blo 1648023 1648799 := bstep (se 1 (by rfl) ⟨1236599, by rfl⟩ : syracuseStep 1648799 = 2473199) B2473199
theorem B4173353 : Blo 1648023 4173353 := bstep (se 2 (by rfl) ⟨1565007, by rfl⟩ : syracuseStep 4173353 = 3130015) B3130015
theorem B4173383 : Blo 1648023 4173383 := bstep (se 1 (by rfl) ⟨3130037, by rfl⟩ : syracuseStep 4173383 = 6260075) B6260075
theorem B12686057 : Blo 1648023 12686057 := bstep (se 2 (by rfl) ⟨4757271, by rfl⟩ : syracuseStep 12686057 = 9514543) B9514543
theorem B28955515 : Blo 1648023 28955515 := bstep (se 1 (by rfl) ⟨21716636, by rfl⟩ : syracuseStep 28955515 = 43433273) B43433273
theorem B2472095 : Blo 1648023 2472095 := bstep (se 1 (by rfl) ⟨1854071, by rfl⟩ : syracuseStep 2472095 = 3708143) B3708143
theorem B8911241 : Blo 1648023 8911241 := bstep (se 2 (by rfl) ⟨3341715, by rfl⟩ : syracuseStep 8911241 = 6683431) B6683431
theorem B2472383 : Blo 1648023 2472383 := bstep (se 1 (by rfl) ⟨1854287, by rfl⟩ : syracuseStep 2472383 = 3708575) B3708575
theorem B3710177 : Blo 1648023 3710177 := bstep (se 2 (by rfl) ⟨1391316, by rfl⟩ : syracuseStep 3710177 = 2782633) B2782633
theorem B8346887 : Blo 1648023 8346887 := bstep (se 1 (by rfl) ⟨6260165, by rfl⟩ : syracuseStep 8346887 = 12520331) B12520331
theorem B3521951 : Blo 1648023 3521951 := bstep (se 1 (by rfl) ⟨2641463, by rfl⟩ : syracuseStep 3521951 = 5282927) B5282927
theorem B11886209 : Blo 1648023 11886209 := bstep (se 2 (by rfl) ⟨4457328, by rfl⟩ : syracuseStep 11886209 = 8914657) B8914657
theorem B10559315 : Blo 1648023 10559315 := bstep (se 1 (by rfl) ⟨7919486, by rfl⟩ : syracuseStep 10559315 = 15838973) B15838973
theorem B7045217 : Blo 1648023 7045217 := bstep (se 2 (by rfl) ⟨2641956, by rfl⟩ : syracuseStep 7045217 = 5283913) B5283913
theorem B1648063 : Blo 1648023 1648063 := bstep (se 1 (by rfl) ⟨1236047, by rfl⟩ : syracuseStep 1648063 = 2472095) B2472095
theorem B5940827 : Blo 1648023 5940827 := bstep (se 1 (by rfl) ⟨4455620, by rfl⟩ : syracuseStep 5940827 = 8911241) B8911241
theorem B1648255 : Blo 1648023 1648255 := bstep (se 1 (by rfl) ⟨1236191, by rfl⟩ : syracuseStep 1648255 = 2472383) B2472383
theorem B216762409 : Blo 1648023 216762409 := bstep (se 2 (by rfl) ⟨81285903, by rfl⟩ : syracuseStep 216762409 = 162571807) B162571807
theorem B5564591 : Blo 1648023 5564591 := bstep (se 1 (by rfl) ⟨4173443, by rfl⟩ : syracuseStep 5564591 = 8346887) B8346887
theorem B7924139 : Blo 1648023 7924139 := bstep (se 1 (by rfl) ⟨5943104, by rfl⟩ : syracuseStep 7924139 = 11886209) B11886209
theorem B7039543 : Blo 1648023 7039543 := bstep (se 1 (by rfl) ⟨5279657, by rfl⟩ : syracuseStep 7039543 = 10559315) B10559315
theorem B8457371 : Blo 1648023 8457371 := bstep (se 1 (by rfl) ⟨6343028, by rfl⟩ : syracuseStep 8457371 = 12686057) B12686057
theorem B2347967 : Blo 1648023 2347967 := bstep (se 1 (by rfl) ⟨1760975, by rfl⟩ : syracuseStep 2347967 = 3521951) B3521951
theorem B2782235 : Blo 1648023 2782235 := bstep (se 1 (by rfl) ⟨2086676, by rfl⟩ : syracuseStep 2782235 = 4173353) B4173353
theorem B2782255 : Blo 1648023 2782255 := bstep (se 1 (by rfl) ⟨2086691, by rfl⟩ : syracuseStep 2782255 = 4173383) B4173383
theorem B10852471 : Blo 1648023 10852471 := bstep (se 1 (by rfl) ⟨8139353, by rfl⟩ : syracuseStep 10852471 = 16278707) B16278707
theorem B9394487 : Blo 1648023 9394487 := bstep (se 1 (by rfl) ⟨7045865, by rfl⟩ : syracuseStep 9394487 = 14091731) B14091731
theorem B38607353 : Blo 1648023 38607353 := bstep (se 2 (by rfl) ⟨14477757, by rfl⟩ : syracuseStep 38607353 = 28955515) B28955515
theorem B2473451 : Blo 1648023 2473451 := bstep (se 1 (by rfl) ⟨1855088, by rfl⟩ : syracuseStep 2473451 = 3710177) B3710177
theorem B5638247 : Blo 1648023 5638247 := bstep (se 1 (by rfl) ⟨4228685, by rfl⟩ : syracuseStep 5638247 = 8457371) B8457371
theorem B1648967 : Blo 1648023 1648967 := bstep (se 1 (by rfl) ⟨1236725, by rfl⟩ : syracuseStep 1648967 = 2473451) B2473451
theorem B6261245 : Blo 1648023 6261245 := bstep (se 3 (by rfl) ⟨1173983, by rfl⟩ : syracuseStep 6261245 = 2347967) B2347967
theorem B289016545 : Blo 1648023 289016545 := bstep (se 2 (by rfl) ⟨108381204, by rfl⟩ : syracuseStep 289016545 = 216762409) B216762409
theorem B4696811 : Blo 1648023 4696811 := bstep (se 1 (by rfl) ⟨3522608, by rfl⟩ : syracuseStep 4696811 = 7045217) B7045217
theorem B14469961 : Blo 1648023 14469961 := bstep (se 2 (by rfl) ⟨5426235, by rfl⟩ : syracuseStep 14469961 = 10852471) B10852471
theorem B1854823 : Blo 1648023 1854823 := bstep (se 1 (by rfl) ⟨1391117, by rfl⟩ : syracuseStep 1854823 = 2782235) B2782235
theorem B3960551 : Blo 1648023 3960551 := bstep (se 1 (by rfl) ⟨2970413, by rfl⟩ : syracuseStep 3960551 = 5940827) B5940827
theorem B6262991 : Blo 1648023 6262991 := bstep (se 1 (by rfl) ⟨4697243, by rfl⟩ : syracuseStep 6262991 = 9394487) B9394487
theorem B9386057 : Blo 1648023 9386057 := bstep (se 2 (by rfl) ⟨3519771, by rfl⟩ : syracuseStep 9386057 = 7039543) B7039543
theorem B3709673 : Blo 1648023 3709673 := bstep (se 2 (by rfl) ⟨1391127, by rfl⟩ : syracuseStep 3709673 = 2782255) B2782255
theorem B3709727 : Blo 1648023 3709727 := bstep (se 1 (by rfl) ⟨2782295, by rfl⟩ : syracuseStep 3709727 = 5564591) B5564591
theorem B5282759 : Blo 1648023 5282759 := bstep (se 1 (by rfl) ⟨3962069, by rfl⟩ : syracuseStep 5282759 = 7924139) B7924139
theorem B25738235 : Blo 1648023 25738235 := bstep (se 1 (by rfl) ⟨19303676, by rfl⟩ : syracuseStep 25738235 = 38607353) B38607353
theorem B19293281 : Blo 1648023 19293281 := bstep (se 2 (by rfl) ⟨7234980, by rfl⟩ : syracuseStep 19293281 = 14469961) B14469961
theorem B3131207 : Blo 1648023 3131207 := bstep (se 1 (by rfl) ⟨2348405, by rfl⟩ : syracuseStep 3131207 = 4696811) B4696811
theorem B2640367 : Blo 1648023 2640367 := bstep (se 1 (by rfl) ⟨1980275, by rfl⟩ : syracuseStep 2640367 = 3960551) B3960551
theorem B385355393 : Blo 1648023 385355393 := bstep (se 2 (by rfl) ⟨144508272, by rfl⟩ : syracuseStep 385355393 = 289016545) B289016545
theorem B4174163 : Blo 1648023 4174163 := bstep (se 1 (by rfl) ⟨3130622, by rfl⟩ : syracuseStep 4174163 = 6261245) B6261245
theorem B17158823 : Blo 1648023 17158823 := bstep (se 1 (by rfl) ⟨12869117, by rfl⟩ : syracuseStep 17158823 = 25738235) B25738235
theorem B14087357 : Blo 1648023 14087357 := bstep (se 3 (by rfl) ⟨2641379, by rfl⟩ : syracuseStep 14087357 = 5282759) B5282759
theorem B4175327 : Blo 1648023 4175327 := bstep (se 1 (by rfl) ⟨3131495, by rfl⟩ : syracuseStep 4175327 = 6262991) B6262991
theorem B6257371 : Blo 1648023 6257371 := bstep (se 1 (by rfl) ⟨4693028, by rfl⟩ : syracuseStep 6257371 = 9386057) B9386057
theorem B3758831 : Blo 1648023 3758831 := bstep (se 1 (by rfl) ⟨2819123, by rfl⟩ : syracuseStep 3758831 = 5638247) B5638247
theorem B2473097 : Blo 1648023 2473097 := bstep (se 2 (by rfl) ⟨927411, by rfl⟩ : syracuseStep 2473097 = 1854823) B1854823
theorem B2473115 : Blo 1648023 2473115 := bstep (se 1 (by rfl) ⟨1854836, by rfl⟩ : syracuseStep 2473115 = 3709673) B3709673
theorem B2473151 : Blo 1648023 2473151 := bstep (se 1 (by rfl) ⟨1854863, by rfl⟩ : syracuseStep 2473151 = 3709727) B3709727
theorem B12862187 : Blo 1648023 12862187 := bstep (se 1 (by rfl) ⟨9646640, by rfl⟩ : syracuseStep 12862187 = 19293281) B19293281
theorem B1648731 : Blo 1648023 1648731 := bstep (se 1 (by rfl) ⟨1236548, by rfl⟩ : syracuseStep 1648731 = 2473097) B2473097
theorem B1648743 : Blo 1648023 1648743 := bstep (se 1 (by rfl) ⟨1236557, by rfl⟩ : syracuseStep 1648743 = 2473115) B2473115
theorem B1648767 : Blo 1648023 1648767 := bstep (se 1 (by rfl) ⟨1236575, by rfl⟩ : syracuseStep 1648767 = 2473151) B2473151
theorem B256903595 : Blo 1648023 256903595 := bstep (se 1 (by rfl) ⟨192677696, by rfl⟩ : syracuseStep 256903595 = 385355393) B385355393
theorem B11439215 : Blo 1648023 11439215 := bstep (se 1 (by rfl) ⟨8579411, by rfl⟩ : syracuseStep 11439215 = 17158823) B17158823
theorem B9391571 : Blo 1648023 9391571 := bstep (se 1 (by rfl) ⟨7043678, by rfl⟩ : syracuseStep 9391571 = 14087357) B14087357
theorem B8343161 : Blo 1648023 8343161 := bstep (se 2 (by rfl) ⟨3128685, by rfl⟩ : syracuseStep 8343161 = 6257371) B6257371
theorem B2782775 : Blo 1648023 2782775 := bstep (se 1 (by rfl) ⟨2087081, by rfl⟩ : syracuseStep 2782775 = 4174163) B4174163
theorem B2783551 : Blo 1648023 2783551 := bstep (se 1 (by rfl) ⟨2087663, by rfl⟩ : syracuseStep 2783551 = 4175327) B4175327
theorem B2087471 : Blo 1648023 2087471 := bstep (se 1 (by rfl) ⟨1565603, by rfl⟩ : syracuseStep 2087471 = 3131207) B3131207
theorem B2505887 : Blo 1648023 2505887 := bstep (se 1 (by rfl) ⟨1879415, by rfl⟩ : syracuseStep 2505887 = 3758831) B3758831
theorem B14081957 : Blo 1648023 14081957 := bstep (se 4 (by rfl) ⟨1320183, by rfl⟩ : syracuseStep 14081957 = 2640367) B2640367
theorem B3711401 : Blo 1648023 3711401 := bstep (se 2 (by rfl) ⟨1391775, by rfl⟩ : syracuseStep 3711401 = 2783551) B2783551
theorem B6261047 : Blo 1648023 6261047 := bstep (se 1 (by rfl) ⟨4695785, by rfl⟩ : syracuseStep 6261047 = 9391571) B9391571
theorem B1855183 : Blo 1648023 1855183 := bstep (se 1 (by rfl) ⟨1391387, by rfl⟩ : syracuseStep 1855183 = 2782775) B2782775
theorem B5566589 : Blo 1648023 5566589 := bstep (se 3 (by rfl) ⟨1043735, by rfl⟩ : syracuseStep 5566589 = 2087471) B2087471
theorem B137196661 : Blo 1648023 137196661 := bstep (se 5 (by rfl) ⟨6431093, by rfl⟩ : syracuseStep 137196661 = 12862187) B12862187
theorem B171269063 : Blo 1648023 171269063 := bstep (se 1 (by rfl) ⟨128451797, by rfl⟩ : syracuseStep 171269063 = 256903595) B256903595
theorem B7626143 : Blo 1648023 7626143 := bstep (se 1 (by rfl) ⟨5719607, by rfl⟩ : syracuseStep 7626143 = 11439215) B11439215
theorem B1670591 : Blo 1648023 1670591 := bstep (se 1 (by rfl) ⟨1252943, by rfl⟩ : syracuseStep 1670591 = 2505887) B2505887
theorem B5562107 : Blo 1648023 5562107 := bstep (se 1 (by rfl) ⟨4171580, by rfl⟩ : syracuseStep 5562107 = 8343161) B8343161
theorem B9387971 : Blo 1648023 9387971 := bstep (se 1 (by rfl) ⟨7040978, by rfl⟩ : syracuseStep 9387971 = 14081957) B14081957
theorem B3711059 : Blo 1648023 3711059 := bstep (se 1 (by rfl) ⟨2783294, by rfl⟩ : syracuseStep 3711059 = 5566589) B5566589
theorem B2474267 : Blo 1648023 2474267 := bstep (se 1 (by rfl) ⟨1855700, by rfl⟩ : syracuseStep 2474267 = 3711401) B3711401
theorem B182928881 : Blo 1648023 182928881 := bstep (se 2 (by rfl) ⟨68598330, by rfl⟩ : syracuseStep 182928881 = 137196661) B137196661
theorem B4174031 : Blo 1648023 4174031 := bstep (se 1 (by rfl) ⟨3130523, by rfl⟩ : syracuseStep 4174031 = 6261047) B6261047
theorem B5084095 : Blo 1648023 5084095 := bstep (se 1 (by rfl) ⟨3813071, by rfl⟩ : syracuseStep 5084095 = 7626143) B7626143
theorem B3708071 : Blo 1648023 3708071 := bstep (se 1 (by rfl) ⟨2781053, by rfl⟩ : syracuseStep 3708071 = 5562107) B5562107
theorem B4454909 : Blo 1648023 4454909 := bstep (se 3 (by rfl) ⟨835295, by rfl⟩ : syracuseStep 4454909 = 1670591) B1670591
theorem B114179375 : Blo 1648023 114179375 := bstep (se 1 (by rfl) ⟨85634531, by rfl⟩ : syracuseStep 114179375 = 171269063) B171269063
theorem B2473577 : Blo 1648023 2473577 := bstep (se 2 (by rfl) ⟨927591, by rfl⟩ : syracuseStep 2473577 = 1855183) B1855183
theorem B6258647 : Blo 1648023 6258647 := bstep (se 1 (by rfl) ⟨4693985, by rfl⟩ : syracuseStep 6258647 = 9387971) B9387971
theorem B2474039 : Blo 1648023 2474039 := bstep (se 1 (by rfl) ⟨1855529, by rfl⟩ : syracuseStep 2474039 = 3711059) B3711059
theorem B1649051 : Blo 1648023 1649051 := bstep (se 1 (by rfl) ⟨1236788, by rfl⟩ : syracuseStep 1649051 = 2473577) B2473577
theorem B4172431 : Blo 1648023 4172431 := bstep (se 1 (by rfl) ⟨3129323, by rfl⟩ : syracuseStep 4172431 = 6258647) B6258647
theorem B1649511 : Blo 1648023 1649511 := bstep (se 1 (by rfl) ⟨1237133, by rfl⟩ : syracuseStep 1649511 = 2474267) B2474267
theorem B6778793 : Blo 1648023 6778793 := bstep (se 2 (by rfl) ⟨2542047, by rfl⟩ : syracuseStep 6778793 = 5084095) B5084095
theorem B2969939 : Blo 1648023 2969939 := bstep (se 1 (by rfl) ⟨2227454, by rfl⟩ : syracuseStep 2969939 = 4454909) B4454909
theorem B2782687 : Blo 1648023 2782687 := bstep (se 1 (by rfl) ⟨2087015, by rfl⟩ : syracuseStep 2782687 = 4174031) B4174031
theorem B2472047 : Blo 1648023 2472047 := bstep (se 1 (by rfl) ⟨1854035, by rfl⟩ : syracuseStep 2472047 = 3708071) B3708071
theorem B121952587 : Blo 1648023 121952587 := bstep (se 1 (by rfl) ⟨91464440, by rfl⟩ : syracuseStep 121952587 = 182928881) B182928881
theorem B76119583 : Blo 1648023 76119583 := bstep (se 1 (by rfl) ⟨57089687, by rfl⟩ : syracuseStep 76119583 = 114179375) B114179375
theorem B162603449 : Blo 1648023 162603449 := bstep (se 2 (by rfl) ⟨60976293, by rfl⟩ : syracuseStep 162603449 = 121952587) B121952587
theorem B5563241 : Blo 1648023 5563241 := bstep (se 2 (by rfl) ⟨2086215, by rfl⟩ : syracuseStep 5563241 = 4172431) B4172431
theorem B1648031 : Blo 1648023 1648031 := bstep (se 1 (by rfl) ⟨1236023, by rfl⟩ : syracuseStep 1648031 = 2472047) B2472047
theorem B101492777 : Blo 1648023 101492777 := bstep (se 2 (by rfl) ⟨38059791, by rfl⟩ : syracuseStep 101492777 = 76119583) B76119583
theorem B1649359 : Blo 1648023 1649359 := bstep (se 1 (by rfl) ⟨1237019, by rfl⟩ : syracuseStep 1649359 = 2474039) B2474039
theorem B4519195 : Blo 1648023 4519195 := bstep (se 1 (by rfl) ⟨3389396, by rfl⟩ : syracuseStep 4519195 = 6778793) B6778793
theorem B1979959 : Blo 1648023 1979959 := bstep (se 1 (by rfl) ⟨1484969, by rfl⟩ : syracuseStep 1979959 = 2969939) B2969939
theorem B3710249 : Blo 1648023 3710249 := bstep (se 2 (by rfl) ⟨1391343, by rfl⟩ : syracuseStep 3710249 = 2782687) B2782687
theorem B24102373 : Blo 1648023 24102373 := bstep (se 4 (by rfl) ⟨2259597, by rfl⟩ : syracuseStep 24102373 = 4519195) B4519195
theorem B2639945 : Blo 1648023 2639945 := bstep (se 2 (by rfl) ⟨989979, by rfl⟩ : syracuseStep 2639945 = 1979959) B1979959
theorem B67661851 : Blo 1648023 67661851 := bstep (se 1 (by rfl) ⟨50746388, by rfl⟩ : syracuseStep 67661851 = 101492777) B101492777
theorem B108402299 : Blo 1648023 108402299 := bstep (se 1 (by rfl) ⟨81301724, by rfl⟩ : syracuseStep 108402299 = 162603449) B162603449
theorem B3708827 : Blo 1648023 3708827 := bstep (se 1 (by rfl) ⟨2781620, by rfl⟩ : syracuseStep 3708827 = 5563241) B5563241
theorem B2473499 : Blo 1648023 2473499 := bstep (se 1 (by rfl) ⟨1855124, by rfl⟩ : syracuseStep 2473499 = 3710249) B3710249
theorem B1648999 : Blo 1648023 1648999 := bstep (se 1 (by rfl) ⟨1236749, by rfl⟩ : syracuseStep 1648999 = 2473499) B2473499
theorem B90215801 : Blo 1648023 90215801 := bstep (se 2 (by rfl) ⟨33830925, by rfl⟩ : syracuseStep 90215801 = 67661851) B67661851
theorem B72268199 : Blo 1648023 72268199 := bstep (se 1 (by rfl) ⟨54201149, by rfl⟩ : syracuseStep 72268199 = 108402299) B108402299
theorem B2472551 : Blo 1648023 2472551 := bstep (se 1 (by rfl) ⟨1854413, by rfl⟩ : syracuseStep 2472551 = 3708827) B3708827
theorem B1759963 : Blo 1648023 1759963 := bstep (se 1 (by rfl) ⟨1319972, by rfl⟩ : syracuseStep 1759963 = 2639945) B2639945
theorem B32136497 : Blo 1648023 32136497 := bstep (se 2 (by rfl) ⟨12051186, by rfl⟩ : syracuseStep 32136497 = 24102373) B24102373
theorem B48178799 : Blo 1648023 48178799 := bstep (se 1 (by rfl) ⟨36134099, by rfl⟩ : syracuseStep 48178799 = 72268199) B72268199
theorem B1648367 : Blo 1648023 1648367 := bstep (se 1 (by rfl) ⟨1236275, by rfl⟩ : syracuseStep 1648367 = 2472551) B2472551
theorem B21424331 : Blo 1648023 21424331 := bstep (se 1 (by rfl) ⟨16068248, by rfl⟩ : syracuseStep 21424331 = 32136497) B32136497
theorem B2346617 : Blo 1648023 2346617 := bstep (se 2 (by rfl) ⟨879981, by rfl⟩ : syracuseStep 2346617 = 1759963) B1759963
theorem B60143867 : Blo 1648023 60143867 := bstep (se 1 (by rfl) ⟨45107900, by rfl⟩ : syracuseStep 60143867 = 90215801) B90215801
theorem B14282887 : Blo 1648023 14282887 := bstep (se 1 (by rfl) ⟨10712165, by rfl⟩ : syracuseStep 14282887 = 21424331) B21424331
theorem B40095911 : Blo 1648023 40095911 := bstep (se 1 (by rfl) ⟨30071933, by rfl⟩ : syracuseStep 40095911 = 60143867) B60143867
theorem B32119199 : Blo 1648023 32119199 := bstep (se 1 (by rfl) ⟨24089399, by rfl⟩ : syracuseStep 32119199 = 48178799) B48178799
theorem B6257645 : Blo 1648023 6257645 := bstep (se 3 (by rfl) ⟨1173308, by rfl⟩ : syracuseStep 6257645 = 2346617) B2346617
theorem B26730607 : Blo 1648023 26730607 := bstep (se 1 (by rfl) ⟨20047955, by rfl⟩ : syracuseStep 26730607 = 40095911) B40095911
theorem B4171763 : Blo 1648023 4171763 := bstep (se 1 (by rfl) ⟨3128822, by rfl⟩ : syracuseStep 4171763 = 6257645) B6257645
theorem B19043849 : Blo 1648023 19043849 := bstep (se 2 (by rfl) ⟨7141443, by rfl⟩ : syracuseStep 19043849 = 14282887) B14282887
theorem B21412799 : Blo 1648023 21412799 := bstep (se 1 (by rfl) ⟨16059599, by rfl⟩ : syracuseStep 21412799 = 32119199) B32119199
theorem B2781175 : Blo 1648023 2781175 := bstep (se 1 (by rfl) ⟨2085881, by rfl⟩ : syracuseStep 2781175 = 4171763) B4171763
theorem B14275199 : Blo 1648023 14275199 := bstep (se 1 (by rfl) ⟨10706399, by rfl⟩ : syracuseStep 14275199 = 21412799) B21412799
theorem B35640809 : Blo 1648023 35640809 := bstep (se 2 (by rfl) ⟨13365303, by rfl⟩ : syracuseStep 35640809 = 26730607) B26730607
theorem B12695899 : Blo 1648023 12695899 := bstep (se 1 (by rfl) ⟨9521924, by rfl⟩ : syracuseStep 12695899 = 19043849) B19043849
theorem B16927865 : Blo 1648023 16927865 := bstep (se 2 (by rfl) ⟨6347949, by rfl⟩ : syracuseStep 16927865 = 12695899) B12695899
theorem B23760539 : Blo 1648023 23760539 := bstep (se 1 (by rfl) ⟨17820404, by rfl⟩ : syracuseStep 23760539 = 35640809) B35640809
theorem B3708233 : Blo 1648023 3708233 := bstep (se 2 (by rfl) ⟨1390587, by rfl⟩ : syracuseStep 3708233 = 2781175) B2781175
theorem B9516799 : Blo 1648023 9516799 := bstep (se 1 (by rfl) ⟨7137599, by rfl⟩ : syracuseStep 9516799 = 14275199) B14275199
theorem B11285243 : Blo 1648023 11285243 := bstep (se 1 (by rfl) ⟨8463932, by rfl⟩ : syracuseStep 11285243 = 16927865) B16927865
theorem B15840359 : Blo 1648023 15840359 := bstep (se 1 (by rfl) ⟨11880269, by rfl⟩ : syracuseStep 15840359 = 23760539) B23760539
theorem B2472155 : Blo 1648023 2472155 := bstep (se 1 (by rfl) ⟨1854116, by rfl⟩ : syracuseStep 2472155 = 3708233) B3708233
theorem B12689065 : Blo 1648023 12689065 := bstep (se 2 (by rfl) ⟨4758399, by rfl⟩ : syracuseStep 12689065 = 9516799) B9516799
theorem B10560239 : Blo 1648023 10560239 := bstep (se 1 (by rfl) ⟨7920179, by rfl⟩ : syracuseStep 10560239 = 15840359) B15840359
theorem B1648103 : Blo 1648023 1648103 := bstep (se 1 (by rfl) ⟨1236077, by rfl⟩ : syracuseStep 1648103 = 2472155) B2472155
theorem B16918753 : Blo 1648023 16918753 := bstep (se 2 (by rfl) ⟨6344532, by rfl⟩ : syracuseStep 16918753 = 12689065) B12689065
theorem B7523495 : Blo 1648023 7523495 := bstep (se 1 (by rfl) ⟨5642621, by rfl⟩ : syracuseStep 7523495 = 11285243) B11285243
theorem B5015663 : Blo 1648023 5015663 := bstep (se 1 (by rfl) ⟨3761747, by rfl⟩ : syracuseStep 5015663 = 7523495) B7523495
theorem B7040159 : Blo 1648023 7040159 := bstep (se 1 (by rfl) ⟨5280119, by rfl⟩ : syracuseStep 7040159 = 10560239) B10560239
theorem B22558337 : Blo 1648023 22558337 := bstep (se 2 (by rfl) ⟨8459376, by rfl⟩ : syracuseStep 22558337 = 16918753) B16918753
theorem B3343775 : Blo 1648023 3343775 := bstep (se 1 (by rfl) ⟨2507831, by rfl⟩ : syracuseStep 3343775 = 5015663) B5015663
theorem B15038891 : Blo 1648023 15038891 := bstep (se 1 (by rfl) ⟨11279168, by rfl⟩ : syracuseStep 15038891 = 22558337) B22558337
theorem B4693439 : Blo 1648023 4693439 := bstep (se 1 (by rfl) ⟨3520079, by rfl⟩ : syracuseStep 4693439 = 7040159) B7040159
theorem B8916733 : Blo 1648023 8916733 := bstep (se 3 (by rfl) ⟨1671887, by rfl⟩ : syracuseStep 8916733 = 3343775) B3343775
theorem B10025927 : Blo 1648023 10025927 := bstep (se 1 (by rfl) ⟨7519445, by rfl⟩ : syracuseStep 10025927 = 15038891) B15038891
theorem B3128959 : Blo 1648023 3128959 := bstep (se 1 (by rfl) ⟨2346719, by rfl⟩ : syracuseStep 3128959 = 4693439) B4693439
theorem B4171945 : Blo 1648023 4171945 := bstep (se 2 (by rfl) ⟨1564479, by rfl⟩ : syracuseStep 4171945 = 3128959) B3128959
theorem B11888977 : Blo 1648023 11888977 := bstep (se 2 (by rfl) ⟨4458366, by rfl⟩ : syracuseStep 11888977 = 8916733) B8916733
theorem B6683951 : Blo 1648023 6683951 := bstep (se 1 (by rfl) ⟨5012963, by rfl⟩ : syracuseStep 6683951 = 10025927) B10025927
theorem B5562593 : Blo 1648023 5562593 := bstep (se 2 (by rfl) ⟨2085972, by rfl⟩ : syracuseStep 5562593 = 4171945) B4171945
theorem B15851969 : Blo 1648023 15851969 := bstep (se 2 (by rfl) ⟨5944488, by rfl⟩ : syracuseStep 15851969 = 11888977) B11888977
theorem B4455967 : Blo 1648023 4455967 := bstep (se 1 (by rfl) ⟨3341975, by rfl⟩ : syracuseStep 4455967 = 6683951) B6683951
theorem B10567979 : Blo 1648023 10567979 := bstep (se 1 (by rfl) ⟨7925984, by rfl⟩ : syracuseStep 10567979 = 15851969) B15851969
theorem B5941289 : Blo 1648023 5941289 := bstep (se 2 (by rfl) ⟨2227983, by rfl⟩ : syracuseStep 5941289 = 4455967) B4455967
theorem B3708395 : Blo 1648023 3708395 := bstep (se 1 (by rfl) ⟨2781296, by rfl⟩ : syracuseStep 3708395 = 5562593) B5562593
theorem B7045319 : Blo 1648023 7045319 := bstep (se 1 (by rfl) ⟨5283989, by rfl⟩ : syracuseStep 7045319 = 10567979) B10567979
theorem B3960859 : Blo 1648023 3960859 := bstep (se 1 (by rfl) ⟨2970644, by rfl⟩ : syracuseStep 3960859 = 5941289) B5941289
theorem B2472263 : Blo 1648023 2472263 := bstep (se 1 (by rfl) ⟨1854197, by rfl⟩ : syracuseStep 2472263 = 3708395) B3708395
theorem B1648175 : Blo 1648023 1648175 := bstep (se 1 (by rfl) ⟨1236131, by rfl⟩ : syracuseStep 1648175 = 2472263) B2472263
theorem B4696879 : Blo 1648023 4696879 := bstep (se 1 (by rfl) ⟨3522659, by rfl⟩ : syracuseStep 4696879 = 7045319) B7045319
theorem B5281145 : Blo 1648023 5281145 := bstep (se 2 (by rfl) ⟨1980429, by rfl⟩ : syracuseStep 5281145 = 3960859) B3960859
theorem B6262505 : Blo 1648023 6262505 := bstep (se 2 (by rfl) ⟨2348439, by rfl⟩ : syracuseStep 6262505 = 4696879) B4696879
theorem B3520763 : Blo 1648023 3520763 := bstep (se 1 (by rfl) ⟨2640572, by rfl⟩ : syracuseStep 3520763 = 5281145) B5281145
theorem B2347175 : Blo 1648023 2347175 := bstep (se 1 (by rfl) ⟨1760381, by rfl⟩ : syracuseStep 2347175 = 3520763) B3520763
theorem B4175003 : Blo 1648023 4175003 := bstep (se 1 (by rfl) ⟨3131252, by rfl⟩ : syracuseStep 4175003 = 6262505) B6262505
theorem B6259133 : Blo 1648023 6259133 := bstep (se 3 (by rfl) ⟨1173587, by rfl⟩ : syracuseStep 6259133 = 2347175) B2347175
theorem B2783335 : Blo 1648023 2783335 := bstep (se 1 (by rfl) ⟨2087501, by rfl⟩ : syracuseStep 2783335 = 4175003) B4175003
theorem B3711113 : Blo 1648023 3711113 := bstep (se 2 (by rfl) ⟨1391667, by rfl⟩ : syracuseStep 3711113 = 2783335) B2783335
theorem B4172755 : Blo 1648023 4172755 := bstep (se 1 (by rfl) ⟨3129566, by rfl⟩ : syracuseStep 4172755 = 6259133) B6259133
theorem B2474075 : Blo 1648023 2474075 := bstep (se 1 (by rfl) ⟨1855556, by rfl⟩ : syracuseStep 2474075 = 3711113) B3711113
theorem B5563673 : Blo 1648023 5563673 := bstep (se 2 (by rfl) ⟨2086377, by rfl⟩ : syracuseStep 5563673 = 4172755) B4172755
theorem B1649383 : Blo 1648023 1649383 := bstep (se 1 (by rfl) ⟨1237037, by rfl⟩ : syracuseStep 1649383 = 2474075) B2474075
theorem B3709115 : Blo 1648023 3709115 := bstep (se 1 (by rfl) ⟨2781836, by rfl⟩ : syracuseStep 3709115 = 5563673) B5563673
theorem B2472743 : Blo 1648023 2472743 := bstep (se 1 (by rfl) ⟨1854557, by rfl⟩ : syracuseStep 2472743 = 3709115) B3709115
theorem B1648495 : Blo 1648023 1648495 := bstep (se 1 (by rfl) ⟨1236371, by rfl⟩ : syracuseStep 1648495 = 2472743) B2472743

theorem C0 (j : ℕ) (h1 : 412005 ≤ j) (h2 : j ≤ 412380) : Blo 1648023 (4 * j + 3) := by
  interval_cases j
  · exact B1648023
  · exact B1648027
  · exact B1648031
  · exact B1648035
  · exact B1648039
  · exact B1648043
  · exact B1648047
  · exact B1648051
  · exact B1648055
  · exact B1648059
  · exact B1648063
  · exact B1648067
  · exact B1648071
  · exact B1648075
  · exact B1648079
  · exact B1648083
  · exact B1648087
  · exact B1648091
  · exact B1648095
  · exact B1648099
  · exact B1648103
  · exact B1648107
  · exact B1648111
  · exact B1648115
  · exact B1648119
  · exact B1648123
  · exact B1648127
  · exact B1648131
  · exact B1648135
  · exact B1648139
  · exact B1648143
  · exact B1648147
  · exact B1648151
  · exact B1648155
  · exact B1648159
  · exact B1648163
  · exact B1648167
  · exact B1648171
  · exact B1648175
  · exact B1648179
  · exact B1648183
  · exact B1648187
  · exact B1648191
  · exact B1648195
  · exact B1648199
  · exact B1648203
  · exact B1648207
  · exact B1648211
  · exact B1648215
  · exact B1648219
  · exact B1648223
  · exact B1648227
  · exact B1648231
  · exact B1648235
  · exact B1648239
  · exact B1648243
  · exact B1648247
  · exact B1648251
  · exact B1648255
  · exact B1648259
  · exact B1648263
  · exact B1648267
  · exact B1648271
  · exact B1648275
  · exact B1648279
  · exact B1648283
  · exact B1648287
  · exact B1648291
  · exact B1648295
  · exact B1648299
  · exact B1648303
  · exact B1648307
  · exact B1648311
  · exact B1648315
  · exact B1648319
  · exact B1648323
  · exact B1648327
  · exact B1648331
  · exact B1648335
  · exact B1648339
  · exact B1648343
  · exact B1648347
  · exact B1648351
  · exact B1648355
  · exact B1648359
  · exact B1648363
  · exact B1648367
  · exact B1648371
  · exact B1648375
  · exact B1648379
  · exact B1648383
  · exact B1648387
  · exact B1648391
  · exact B1648395
  · exact B1648399
  · exact B1648403
  · exact B1648407
  · exact B1648411
  · exact B1648415
  · exact B1648419
  · exact B1648423
  · exact B1648427
  · exact B1648431
  · exact B1648435
  · exact B1648439
  · exact B1648443
  · exact B1648447
  · exact B1648451
  · exact B1648455
  · exact B1648459
  · exact B1648463
  · exact B1648467
  · exact B1648471
  · exact B1648475
  · exact B1648479
  · exact B1648483
  · exact B1648487
  · exact B1648491
  · exact B1648495
  · exact B1648499
  · exact B1648503
  · exact B1648507
  · exact B1648511
  · exact B1648515
  · exact B1648519
  · exact B1648523
  · exact B1648527
  · exact B1648531
  · exact B1648535
  · exact B1648539
  · exact B1648543
  · exact B1648547
  · exact B1648551
  · exact B1648555
  · exact B1648559
  · exact B1648563
  · exact B1648567
  · exact B1648571
  · exact B1648575
  · exact B1648579
  · exact B1648583
  · exact B1648587
  · exact B1648591
  · exact B1648595
  · exact B1648599
  · exact B1648603
  · exact B1648607
  · exact B1648611
  · exact B1648615
  · exact B1648619
  · exact B1648623
  · exact B1648627
  · exact B1648631
  · exact B1648635
  · exact B1648639
  · exact B1648643
  · exact B1648647
  · exact B1648651
  · exact B1648655
  · exact B1648659
  · exact B1648663
  · exact B1648667
  · exact B1648671
  · exact B1648675
  · exact B1648679
  · exact B1648683
  · exact B1648687
  · exact B1648691
  · exact B1648695
  · exact B1648699
  · exact B1648703
  · exact B1648707
  · exact B1648711
  · exact B1648715
  · exact B1648719
  · exact B1648723
  · exact B1648727
  · exact B1648731
  · exact B1648735
  · exact B1648739
  · exact B1648743
  · exact B1648747
  · exact B1648751
  · exact B1648755
  · exact B1648759
  · exact B1648763
  · exact B1648767
  · exact B1648771
  · exact B1648775
  · exact B1648779
  · exact B1648783
  · exact B1648787
  · exact B1648791
  · exact B1648795
  · exact B1648799
  · exact B1648803
  · exact B1648807
  · exact B1648811
  · exact B1648815
  · exact B1648819
  · exact B1648823
  · exact B1648827
  · exact B1648831
  · exact B1648835
  · exact B1648839
  · exact B1648843
  · exact B1648847
  · exact B1648851
  · exact B1648855
  · exact B1648859
  · exact B1648863
  · exact B1648867
  · exact B1648871
  · exact B1648875
  · exact B1648879
  · exact B1648883
  · exact B1648887
  · exact B1648891
  · exact B1648895
  · exact B1648899
  · exact B1648903
  · exact B1648907
  · exact B1648911
  · exact B1648915
  · exact B1648919
  · exact B1648923
  · exact B1648927
  · exact B1648931
  · exact B1648935
  · exact B1648939
  · exact B1648943
  · exact B1648947
  · exact B1648951
  · exact B1648955
  · exact B1648959
  · exact B1648963
  · exact B1648967
  · exact B1648971
  · exact B1648975
  · exact B1648979
  · exact B1648983
  · exact B1648987
  · exact B1648991
  · exact B1648995
  · exact B1648999
  · exact B1649003
  · exact B1649007
  · exact B1649011
  · exact B1649015
  · exact B1649019
  · exact B1649023
  · exact B1649027
  · exact B1649031
  · exact B1649035
  · exact B1649039
  · exact B1649043
  · exact B1649047
  · exact B1649051
  · exact B1649055
  · exact B1649059
  · exact B1649063
  · exact B1649067
  · exact B1649071
  · exact B1649075
  · exact B1649079
  · exact B1649083
  · exact B1649087
  · exact B1649091
  · exact B1649095
  · exact B1649099
  · exact B1649103
  · exact B1649107
  · exact B1649111
  · exact B1649115
  · exact B1649119
  · exact B1649123
  · exact B1649127
  · exact B1649131
  · exact B1649135
  · exact B1649139
  · exact B1649143
  · exact B1649147
  · exact B1649151
  · exact B1649155
  · exact B1649159
  · exact B1649163
  · exact B1649167
  · exact B1649171
  · exact B1649175
  · exact B1649179
  · exact B1649183
  · exact B1649187
  · exact B1649191
  · exact B1649195
  · exact B1649199
  · exact B1649203
  · exact B1649207
  · exact B1649211
  · exact B1649215
  · exact B1649219
  · exact B1649223
  · exact B1649227
  · exact B1649231
  · exact B1649235
  · exact B1649239
  · exact B1649243
  · exact B1649247
  · exact B1649251
  · exact B1649255
  · exact B1649259
  · exact B1649263
  · exact B1649267
  · exact B1649271
  · exact B1649275
  · exact B1649279
  · exact B1649283
  · exact B1649287
  · exact B1649291
  · exact B1649295
  · exact B1649299
  · exact B1649303
  · exact B1649307
  · exact B1649311
  · exact B1649315
  · exact B1649319
  · exact B1649323
  · exact B1649327
  · exact B1649331
  · exact B1649335
  · exact B1649339
  · exact B1649343
  · exact B1649347
  · exact B1649351
  · exact B1649355
  · exact B1649359
  · exact B1649363
  · exact B1649367
  · exact B1649371
  · exact B1649375
  · exact B1649379
  · exact B1649383
  · exact B1649387
  · exact B1649391
  · exact B1649395
  · exact B1649399
  · exact B1649403
  · exact B1649407
  · exact B1649411
  · exact B1649415
  · exact B1649419
  · exact B1649423
  · exact B1649427
  · exact B1649431
  · exact B1649435
  · exact B1649439
  · exact B1649443
  · exact B1649447
  · exact B1649451
  · exact B1649455
  · exact B1649459
  · exact B1649463
  · exact B1649467
  · exact B1649471
  · exact B1649475
  · exact B1649479
  · exact B1649483
  · exact B1649487
  · exact B1649491
  · exact B1649495
  · exact B1649499
  · exact B1649503
  · exact B1649507
  · exact B1649511
  · exact B1649515
  · exact B1649519
  · exact B1649523

theorem solution (m : ℕ) (hlo : 1648023 ≤ m) (hhi : m ≤ 1649523) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 412005 ≤ j := by omega
    have hj2 : j ≤ 412380 := by omega
    have hb : Blo 1648023 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
