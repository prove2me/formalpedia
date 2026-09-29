-- Prove2me | solution 1 for syracuse_descends_range_358757_362757
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T17:47:38.340562+00:00
-- url     : https://prove2.me/submissions/2ffe7f90-2e5e-4a18-bdcd-841f3a2bab59

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


theorem B1376261 : Blo 358757 1376261 := bbase (se 4 (by rfl) ⟨129024, by rfl⟩ : syracuseStep 1376261 = 258049) (by norm_num)
theorem B819229 : Blo 358757 819229 := bbase (se 3 (by rfl) ⟨153605, by rfl⟩ : syracuseStep 819229 = 307211) (by norm_num)
theorem B2064437 : Blo 358757 2064437 := bbase (se 5 (by rfl) ⟨96770, by rfl⟩ : syracuseStep 2064437 = 193541) (by norm_num)
theorem B983125 : Blo 358757 983125 := bbase (se 8 (by rfl) ⟨5760, by rfl⟩ : syracuseStep 983125 = 11521) (by norm_num)
theorem B458885 : Blo 358757 458885 := bbase (se 4 (by rfl) ⟨43020, by rfl⟩ : syracuseStep 458885 = 86041) (by norm_num)
theorem B917669 : Blo 358757 917669 := bbase (se 4 (by rfl) ⟨86031, by rfl⟩ : syracuseStep 917669 = 172063) (by norm_num)
theorem B458941 : Blo 358757 458941 := bbase (se 3 (by rfl) ⟨86051, by rfl⟩ : syracuseStep 458941 = 172103) (by norm_num)
theorem B1212677 : Blo 358757 1212677 := bbase (se 4 (by rfl) ⟨113688, by rfl⟩ : syracuseStep 1212677 = 227377) (by norm_num)
theorem B459037 : Blo 358757 459037 := bbase (se 3 (by rfl) ⟨86069, by rfl⟩ : syracuseStep 459037 = 172139) (by norm_num)
theorem B3277205 : Blo 358757 3277205 := bbase (se 6 (by rfl) ⟨76809, by rfl⟩ : syracuseStep 3277205 = 153619) (by norm_num)
theorem B918013 : Blo 358757 918013 := bbase (se 3 (by rfl) ⟨172127, by rfl⟩ : syracuseStep 918013 = 344255) (by norm_num)
theorem B819733 : Blo 358757 819733 := bbase (se 6 (by rfl) ⟨19212, by rfl⟩ : syracuseStep 819733 = 38425) (by norm_num)
theorem B1835621 : Blo 358757 1835621 := bbase (se 4 (by rfl) ⟨172089, by rfl⟩ : syracuseStep 1835621 = 344179) (by norm_num)
theorem B918125 : Blo 358757 918125 := bbase (se 3 (by rfl) ⟨172148, by rfl⟩ : syracuseStep 918125 = 344297) (by norm_num)
theorem B1213109 : Blo 358757 1213109 := bbase (se 5 (by rfl) ⟨56864, by rfl⟩ : syracuseStep 1213109 = 113729) (by norm_num)
theorem B1213541 : Blo 358757 1213541 := bbase (se 4 (by rfl) ⟨113769, by rfl⟩ : syracuseStep 1213541 = 227539) (by norm_num)
theorem B787573 : Blo 358757 787573 := bbase (se 5 (by rfl) ⟨36917, by rfl⟩ : syracuseStep 787573 = 73835) (by norm_num)
theorem B2065621 : Blo 358757 2065621 := bbase (se 7 (by rfl) ⟨24206, by rfl⟩ : syracuseStep 2065621 = 48413) (by norm_num)
theorem B820469 : Blo 358757 820469 := bbase (se 5 (by rfl) ⟨38459, by rfl⟩ : syracuseStep 820469 = 76919) (by norm_num)
theorem B1213973 : Blo 358757 1213973 := bbase (se 6 (by rfl) ⟨28452, by rfl⟩ : syracuseStep 1213973 = 56905) (by norm_num)
theorem B1640245 : Blo 358757 1640245 := bbase (se 5 (by rfl) ⟨76886, by rfl⟩ : syracuseStep 1640245 = 153773) (by norm_num)
theorem B1214405 : Blo 358757 1214405 := bbase (se 4 (by rfl) ⟨113850, by rfl⟩ : syracuseStep 1214405 = 227701) (by norm_num)
theorem B821381 : Blo 358757 821381 := bbase (se 4 (by rfl) ⟨77004, by rfl⟩ : syracuseStep 821381 = 154009) (by norm_num)
theorem B1214837 : Blo 358757 1214837 := bbase (se 5 (by rfl) ⟨56945, by rfl⟩ : syracuseStep 1214837 = 113891) (by norm_num)
theorem B6162965 : Blo 358757 6162965 := bbase (se 6 (by rfl) ⟨144444, by rfl⟩ : syracuseStep 6162965 = 288889) (by norm_num)
theorem B1542725 : Blo 358757 1542725 := bbase (se 4 (by rfl) ⟨144630, by rfl⟩ : syracuseStep 1542725 = 289261) (by norm_num)
theorem B1739333 : Blo 358757 1739333 := bbase (se 4 (by rfl) ⟨163062, by rfl⟩ : syracuseStep 1739333 = 326125) (by norm_num)
theorem B1215269 : Blo 358757 1215269 := bbase (se 4 (by rfl) ⟨113931, by rfl⟩ : syracuseStep 1215269 = 227863) (by norm_num)
theorem B494717 : Blo 358757 494717 := bbase (se 3 (by rfl) ⟨92759, by rfl⟩ : syracuseStep 494717 = 185519) (by norm_num)
theorem B1215701 : Blo 358757 1215701 := bbase (se 7 (by rfl) ⟨14246, by rfl⟩ : syracuseStep 1215701 = 28493) (by norm_num)
theorem B462397 : Blo 358757 462397 := bbase (se 3 (by rfl) ⟨86699, by rfl⟩ : syracuseStep 462397 = 173399) (by norm_num)
theorem B1216133 : Blo 358757 1216133 := bbase (se 4 (by rfl) ⟨114012, by rfl⟩ : syracuseStep 1216133 = 228025) (by norm_num)
theorem B1216565 : Blo 358757 1216565 := bbase (se 5 (by rfl) ⟨57026, by rfl⟩ : syracuseStep 1216565 = 114053) (by norm_num)
theorem B1544501 : Blo 358757 1544501 := bbase (se 5 (by rfl) ⟨72398, by rfl⟩ : syracuseStep 1544501 = 144797) (by norm_num)
theorem B1216997 : Blo 358757 1216997 := bbase (se 4 (by rfl) ⟨114093, by rfl⟩ : syracuseStep 1216997 = 228187) (by norm_num)
theorem B1544741 : Blo 358757 1544741 := bbase (se 4 (by rfl) ⟨144819, by rfl⟩ : syracuseStep 1544741 = 289639) (by norm_num)
theorem B1217429 : Blo 358757 1217429 := bbase (se 6 (by rfl) ⟨28533, by rfl⟩ : syracuseStep 1217429 = 57067) (by norm_num)
theorem B1151957 : Blo 358757 1151957 := bbase (se 7 (by rfl) ⟨13499, by rfl⟩ : syracuseStep 1151957 = 26999) (by norm_num)
theorem B463849 : Blo 358757 463849 := bbase (se 2 (by rfl) ⟨173943, by rfl⟩ : syracuseStep 463849 = 347887) (by norm_num)
theorem B431245 : Blo 358757 431245 := bbase (se 3 (by rfl) ⟨80858, by rfl⟩ : syracuseStep 431245 = 161717) (by norm_num)
theorem B365869 : Blo 358757 365869 := bbase (se 3 (by rfl) ⟨68600, by rfl⟩ : syracuseStep 365869 = 137201) (by norm_num)
theorem B1217861 : Blo 358757 1217861 := bbase (se 4 (by rfl) ⟨114174, by rfl⟩ : syracuseStep 1217861 = 228349) (by norm_num)
theorem B693749 : Blo 358757 693749 := bbase (se 5 (by rfl) ⟨32519, by rfl⟩ : syracuseStep 693749 = 65039) (by norm_num)
theorem B1742485 : Blo 358757 1742485 := bbase (se 6 (by rfl) ⟨40839, by rfl⟩ : syracuseStep 1742485 = 81679) (by norm_num)
theorem B431777 : Blo 358757 431777 := bbase (se 2 (by rfl) ⟨161916, by rfl⟩ : syracuseStep 431777 = 323833) (by norm_num)
theorem B1218293 : Blo 358757 1218293 := bbase (se 5 (by rfl) ⟨57107, by rfl⟩ : syracuseStep 1218293 = 114215) (by norm_num)
theorem B1153045 : Blo 358757 1153045 := bbase (se 6 (by rfl) ⟨27024, by rfl⟩ : syracuseStep 1153045 = 54049) (by norm_num)
theorem B2725973 : Blo 358757 2725973 := bbase (se 8 (by rfl) ⟨15972, by rfl⟩ : syracuseStep 2725973 = 31945) (by norm_num)
theorem B1218725 : Blo 358757 1218725 := bbase (se 4 (by rfl) ⟨114255, by rfl⟩ : syracuseStep 1218725 = 228511) (by norm_num)
theorem B1022149 : Blo 358757 1022149 := bbase (se 4 (by rfl) ⟨95826, by rfl⟩ : syracuseStep 1022149 = 191653) (by norm_num)
theorem B432373 : Blo 358757 432373 := bbase (se 5 (by rfl) ⟨20267, by rfl⟩ : syracuseStep 432373 = 40535) (by norm_num)
theorem B432469 : Blo 358757 432469 := bbase (se 10 (by rfl) ⟨633, by rfl⟩ : syracuseStep 432469 = 1267) (by norm_num)
theorem B825869 : Blo 358757 825869 := bbase (se 3 (by rfl) ⟨154850, by rfl⟩ : syracuseStep 825869 = 309701) (by norm_num)
theorem B1219157 : Blo 358757 1219157 := bbase (se 8 (by rfl) ⟨7143, by rfl⟩ : syracuseStep 1219157 = 14287) (by norm_num)
theorem B727717 : Blo 358757 727717 := bbase (se 4 (by rfl) ⟨68223, by rfl⟩ : syracuseStep 727717 = 136447) (by norm_num)
theorem B367345 : Blo 358757 367345 := bbase (se 2 (by rfl) ⟨137754, by rfl⟩ : syracuseStep 367345 = 275509) (by norm_num)
theorem B1547029 : Blo 358757 1547029 := bbase (se 6 (by rfl) ⟨36258, by rfl⟩ : syracuseStep 1547029 = 72517) (by norm_num)
theorem B1219589 : Blo 358757 1219589 := bbase (se 4 (by rfl) ⟨114336, by rfl⟩ : syracuseStep 1219589 = 228673) (by norm_num)
theorem B662581 : Blo 358757 662581 := bbase (se 5 (by rfl) ⟨31058, by rfl⟩ : syracuseStep 662581 = 62117) (by norm_num)
theorem B826453 : Blo 358757 826453 := bbase (se 8 (by rfl) ⟨4842, by rfl⟩ : syracuseStep 826453 = 9685) (by norm_num)
theorem B1154213 : Blo 358757 1154213 := bbase (se 4 (by rfl) ⟨108207, by rfl⟩ : syracuseStep 1154213 = 216415) (by norm_num)
theorem B2202805 : Blo 358757 2202805 := bbase (se 5 (by rfl) ⟨103256, by rfl⟩ : syracuseStep 2202805 = 206513) (by norm_num)
theorem B1220021 : Blo 358757 1220021 := bbase (se 5 (by rfl) ⟨57188, by rfl⟩ : syracuseStep 1220021 = 114377) (by norm_num)
theorem B433613 : Blo 358757 433613 := bbase (se 3 (by rfl) ⟨81302, by rfl⟩ : syracuseStep 433613 = 162605) (by norm_num)
theorem B1383925 : Blo 358757 1383925 := bbase (se 5 (by rfl) ⟨64871, by rfl⟩ : syracuseStep 1383925 = 129743) (by norm_num)
theorem B2367029 : Blo 358757 2367029 := bbase (se 5 (by rfl) ⟨110954, by rfl⟩ : syracuseStep 2367029 = 221909) (by norm_num)
theorem B1023653 : Blo 358757 1023653 := bbase (se 4 (by rfl) ⟨95967, by rfl⟩ : syracuseStep 1023653 = 191935) (by norm_num)
theorem B499469 : Blo 358757 499469 := bbase (se 3 (by rfl) ⟨93650, by rfl⟩ : syracuseStep 499469 = 187301) (by norm_num)
theorem B2629397 : Blo 358757 2629397 := bbase (se 6 (by rfl) ⟨61626, by rfl⟩ : syracuseStep 2629397 = 123253) (by norm_num)
theorem B433945 : Blo 358757 433945 := bbase (se 2 (by rfl) ⟨162729, by rfl⟩ : syracuseStep 433945 = 325459) (by norm_num)
theorem B1220453 : Blo 358757 1220453 := bbase (se 4 (by rfl) ⟨114417, by rfl⟩ : syracuseStep 1220453 = 228835) (by norm_num)
theorem B696397 : Blo 358757 696397 := bbase (se 3 (by rfl) ⟨130574, by rfl⟩ : syracuseStep 696397 = 261149) (by norm_num)
theorem B1548517 : Blo 358757 1548517 := bbase (se 4 (by rfl) ⟨145173, by rfl⟩ : syracuseStep 1548517 = 290347) (by norm_num)
theorem B1548533 : Blo 358757 1548533 := bbase (se 5 (by rfl) ⟨72587, by rfl⟩ : syracuseStep 1548533 = 145175) (by norm_num)
theorem B1220885 : Blo 358757 1220885 := bbase (se 6 (by rfl) ⟨28614, by rfl⟩ : syracuseStep 1220885 = 57229) (by norm_num)
theorem B3449141 : Blo 358757 3449141 := bbase (se 5 (by rfl) ⟨161678, by rfl⟩ : syracuseStep 3449141 = 323357) (by norm_num)
theorem B2662741 : Blo 358757 2662741 := bbase (se 10 (by rfl) ⟨3900, by rfl⟩ : syracuseStep 2662741 = 7801) (by norm_num)
theorem B434641 : Blo 358757 434641 := bbase (se 2 (by rfl) ⟨162990, by rfl⟩ : syracuseStep 434641 = 325981) (by norm_num)
theorem B434689 : Blo 358757 434689 := bbase (se 2 (by rfl) ⟨163008, by rfl⟩ : syracuseStep 434689 = 326017) (by norm_num)
theorem B1221317 : Blo 358757 1221317 := bbase (se 4 (by rfl) ⟨114498, by rfl⟩ : syracuseStep 1221317 = 228997) (by norm_num)
theorem B1156069 : Blo 358757 1156069 := bbase (se 4 (by rfl) ⟨108381, by rfl⟩ : syracuseStep 1156069 = 216763) (by norm_num)
theorem B926765 : Blo 358757 926765 := bbase (se 3 (by rfl) ⟨173768, by rfl⟩ : syracuseStep 926765 = 347537) (by norm_num)
theorem B730181 : Blo 358757 730181 := bbase (se 4 (by rfl) ⟨68454, by rfl⟩ : syracuseStep 730181 = 136909) (by norm_num)
theorem B2303093 : Blo 358757 2303093 := bbase (se 5 (by rfl) ⟨107957, by rfl⟩ : syracuseStep 2303093 = 215915) (by norm_num)
theorem B1221749 : Blo 358757 1221749 := bbase (se 5 (by rfl) ⟨57269, by rfl⟩ : syracuseStep 1221749 = 114539) (by norm_num)
theorem B1025237 : Blo 358757 1025237 := bbase (se 7 (by rfl) ⟨12014, by rfl⟩ : syracuseStep 1025237 = 24029) (by norm_num)
theorem B1811909 : Blo 358757 1811909 := bbase (se 4 (by rfl) ⟨169866, by rfl⟩ : syracuseStep 1811909 = 339733) (by norm_num)
theorem B2598389 : Blo 358757 2598389 := bbase (se 5 (by rfl) ⟨121799, by rfl⟩ : syracuseStep 2598389 = 243599) (by norm_num)
theorem B435737 : Blo 358757 435737 := bbase (se 2 (by rfl) ⟨163401, by rfl⟩ : syracuseStep 435737 = 326803) (by norm_num)
theorem B1222181 : Blo 358757 1222181 := bbase (se 4 (by rfl) ⟨114579, by rfl⟩ : syracuseStep 1222181 = 229159) (by norm_num)
theorem B468725 : Blo 358757 468725 := bbase (se 5 (by rfl) ⟨21971, by rfl⟩ : syracuseStep 468725 = 43943) (by norm_num)
theorem B1189621 : Blo 358757 1189621 := bbase (se 5 (by rfl) ⟨55763, by rfl⟩ : syracuseStep 1189621 = 111527) (by norm_num)
theorem B861997 : Blo 358757 861997 := bbase (se 3 (by rfl) ⟨161624, by rfl⟩ : syracuseStep 861997 = 323249) (by norm_num)
theorem B1025909 : Blo 358757 1025909 := bbase (se 5 (by rfl) ⟨48089, by rfl⟩ : syracuseStep 1025909 = 96179) (by norm_num)
theorem B1222613 : Blo 358757 1222613 := bbase (se 7 (by rfl) ⟨14327, by rfl⟩ : syracuseStep 1222613 = 28655) (by norm_num)
theorem B403609 : Blo 358757 403609 := bbase (se 2 (by rfl) ⟨151353, by rfl⟩ : syracuseStep 403609 = 302707) (by norm_num)
theorem B403645 : Blo 358757 403645 := bbase (se 3 (by rfl) ⟨75683, by rfl⟩ : syracuseStep 403645 = 151367) (by norm_num)
theorem B403681 : Blo 358757 403681 := bbase (se 2 (by rfl) ⟨151380, by rfl⟩ : syracuseStep 403681 = 302761) (by norm_num)
theorem B403717 : Blo 358757 403717 := bbase (se 4 (by rfl) ⟨37848, by rfl⟩ : syracuseStep 403717 = 75697) (by norm_num)
theorem B1026341 : Blo 358757 1026341 := bbase (se 4 (by rfl) ⟨96219, by rfl⟩ : syracuseStep 1026341 = 192439) (by norm_num)
theorem B403753 : Blo 358757 403753 := bbase (se 2 (by rfl) ⟨151407, by rfl⟩ : syracuseStep 403753 = 302815) (by norm_num)
theorem B1157429 : Blo 358757 1157429 := bbase (se 5 (by rfl) ⟨54254, by rfl⟩ : syracuseStep 1157429 = 108509) (by norm_num)
theorem B403789 : Blo 358757 403789 := bbase (se 3 (by rfl) ⟨75710, by rfl⟩ : syracuseStep 403789 = 151421) (by norm_num)
theorem B403825 : Blo 358757 403825 := bbase (se 2 (by rfl) ⟨151434, by rfl⟩ : syracuseStep 403825 = 302869) (by norm_num)
theorem B2107765 : Blo 358757 2107765 := bbase (se 5 (by rfl) ⟨98801, by rfl⟩ : syracuseStep 2107765 = 197603) (by norm_num)
theorem B1223045 : Blo 358757 1223045 := bbase (se 4 (by rfl) ⟨114660, by rfl⟩ : syracuseStep 1223045 = 229321) (by norm_num)
theorem B403861 : Blo 358757 403861 := bbase (se 6 (by rfl) ⟨9465, by rfl⟩ : syracuseStep 403861 = 18931) (by norm_num)
theorem B862613 : Blo 358757 862613 := bbase (se 6 (by rfl) ⟨20217, by rfl⟩ : syracuseStep 862613 = 40435) (by norm_num)
theorem B1321397 : Blo 358757 1321397 := bbase (se 5 (by rfl) ⟨61940, by rfl⟩ : syracuseStep 1321397 = 123881) (by norm_num)
theorem B403897 : Blo 358757 403897 := bbase (se 2 (by rfl) ⟨151461, by rfl⟩ : syracuseStep 403897 = 302923) (by norm_num)
theorem B862669 : Blo 358757 862669 := bbase (se 3 (by rfl) ⟨161750, by rfl⟩ : syracuseStep 862669 = 323501) (by norm_num)
theorem B403933 : Blo 358757 403933 := bbase (se 3 (by rfl) ⟨75737, by rfl⟩ : syracuseStep 403933 = 151475) (by norm_num)
theorem B403969 : Blo 358757 403969 := bbase (se 2 (by rfl) ⟨151488, by rfl⟩ : syracuseStep 403969 = 302977) (by norm_num)
theorem B404005 : Blo 358757 404005 := bbase (se 4 (by rfl) ⟨37875, by rfl⟩ : syracuseStep 404005 = 75751) (by norm_num)
theorem B371237 : Blo 358757 371237 := bbase (se 4 (by rfl) ⟨34803, by rfl⟩ : syracuseStep 371237 = 69607) (by norm_num)
theorem B404041 : Blo 358757 404041 := bbase (se 2 (by rfl) ⟨151515, by rfl⟩ : syracuseStep 404041 = 303031) (by norm_num)
theorem B1092197 : Blo 358757 1092197 := bbase (se 4 (by rfl) ⟨102393, by rfl⟩ : syracuseStep 1092197 = 204787) (by norm_num)
theorem B404077 : Blo 358757 404077 := bbase (se 3 (by rfl) ⟨75764, by rfl⟩ : syracuseStep 404077 = 151529) (by norm_num)
theorem B404113 : Blo 358757 404113 := bbase (se 2 (by rfl) ⟨151542, by rfl⟩ : syracuseStep 404113 = 303085) (by norm_num)
theorem B404149 : Blo 358757 404149 := bbase (se 5 (by rfl) ⟨18944, by rfl⟩ : syracuseStep 404149 = 37889) (by norm_num)
theorem B404185 : Blo 358757 404185 := bbase (se 2 (by rfl) ⟨151569, by rfl⟩ : syracuseStep 404185 = 303139) (by norm_num)
theorem B404221 : Blo 358757 404221 := bbase (se 3 (by rfl) ⟨75791, by rfl⟩ : syracuseStep 404221 = 151583) (by norm_num)
theorem B404257 : Blo 358757 404257 := bbase (se 2 (by rfl) ⟨151596, by rfl⟩ : syracuseStep 404257 = 303193) (by norm_num)
theorem B1223477 : Blo 358757 1223477 := bbase (se 5 (by rfl) ⟨57350, by rfl⟩ : syracuseStep 1223477 = 114701) (by norm_num)
theorem B404293 : Blo 358757 404293 := bbase (se 4 (by rfl) ⟨37902, by rfl⟩ : syracuseStep 404293 = 75805) (by norm_num)
theorem B404329 : Blo 358757 404329 := bbase (se 2 (by rfl) ⟨151623, by rfl⟩ : syracuseStep 404329 = 303247) (by norm_num)
theorem B732029 : Blo 358757 732029 := bbase (se 3 (by rfl) ⟨137255, by rfl⟩ : syracuseStep 732029 = 274511) (by norm_num)
theorem B404365 : Blo 358757 404365 := bbase (se 3 (by rfl) ⟨75818, by rfl⟩ : syracuseStep 404365 = 151637) (by norm_num)
theorem B404401 : Blo 358757 404401 := bbase (se 2 (by rfl) ⟨151650, by rfl⟩ : syracuseStep 404401 = 303301) (by norm_num)
theorem B404437 : Blo 358757 404437 := bbase (se 7 (by rfl) ⟨4739, by rfl⟩ : syracuseStep 404437 = 9479) (by norm_num)
theorem B404473 : Blo 358757 404473 := bbase (se 2 (by rfl) ⟨151677, by rfl⟩ : syracuseStep 404473 = 303355) (by norm_num)
theorem B1027093 : Blo 358757 1027093 := bbase (se 6 (by rfl) ⟨24072, by rfl⟩ : syracuseStep 1027093 = 48145) (by norm_num)
theorem B404509 : Blo 358757 404509 := bbase (se 3 (by rfl) ⟨75845, by rfl⟩ : syracuseStep 404509 = 151691) (by norm_num)
theorem B404545 : Blo 358757 404545 := bbase (se 2 (by rfl) ⟨151704, by rfl⟩ : syracuseStep 404545 = 303409) (by norm_num)
theorem B404581 : Blo 358757 404581 := bbase (se 4 (by rfl) ⟨37929, by rfl⟩ : syracuseStep 404581 = 75859) (by norm_num)
theorem B404617 : Blo 358757 404617 := bbase (se 2 (by rfl) ⟨151731, by rfl⟩ : syracuseStep 404617 = 303463) (by norm_num)
theorem B404653 : Blo 358757 404653 := bbase (se 3 (by rfl) ⟨75872, by rfl⟩ : syracuseStep 404653 = 151745) (by norm_num)
theorem B404689 : Blo 358757 404689 := bbase (se 2 (by rfl) ⟨151758, by rfl⟩ : syracuseStep 404689 = 303517) (by norm_num)
theorem B1223909 : Blo 358757 1223909 := bbase (se 4 (by rfl) ⟨114741, by rfl⟩ : syracuseStep 1223909 = 229483) (by norm_num)
theorem B404725 : Blo 358757 404725 := bbase (se 5 (by rfl) ⟨18971, by rfl⟩ : syracuseStep 404725 = 37943) (by norm_num)
theorem B404761 : Blo 358757 404761 := bbase (se 2 (by rfl) ⟨151785, by rfl⟩ : syracuseStep 404761 = 303571) (by norm_num)
theorem B404797 : Blo 358757 404797 := bbase (se 3 (by rfl) ⟨75899, by rfl⟩ : syracuseStep 404797 = 151799) (by norm_num)
theorem B5680469 : Blo 358757 5680469 := bbase (se 11 (by rfl) ⟨4160, by rfl⟩ : syracuseStep 5680469 = 8321) (by norm_num)
theorem B6663509 : Blo 358757 6663509 := bbase (se 11 (by rfl) ⟨4880, by rfl⟩ : syracuseStep 6663509 = 9761) (by norm_num)
theorem B404833 : Blo 358757 404833 := bbase (se 2 (by rfl) ⟨151812, by rfl⟩ : syracuseStep 404833 = 303625) (by norm_num)
theorem B404869 : Blo 358757 404869 := bbase (se 4 (by rfl) ⟨37956, by rfl⟩ : syracuseStep 404869 = 75913) (by norm_num)
theorem B404905 : Blo 358757 404905 := bbase (se 2 (by rfl) ⟨151839, by rfl⟩ : syracuseStep 404905 = 303679) (by norm_num)
theorem B863669 : Blo 358757 863669 := bbase (se 5 (by rfl) ⟨40484, by rfl⟩ : syracuseStep 863669 = 80969) (by norm_num)
theorem B404941 : Blo 358757 404941 := bbase (se 3 (by rfl) ⟨75926, by rfl⟩ : syracuseStep 404941 = 151853) (by norm_num)
theorem B404977 : Blo 358757 404977 := bbase (se 2 (by rfl) ⟨151866, by rfl⟩ : syracuseStep 404977 = 303733) (by norm_num)
theorem B405013 : Blo 358757 405013 := bbase (se 6 (by rfl) ⟨9492, by rfl⟩ : syracuseStep 405013 = 18985) (by norm_num)
theorem B405049 : Blo 358757 405049 := bbase (se 2 (by rfl) ⟨151893, by rfl⟩ : syracuseStep 405049 = 303787) (by norm_num)
theorem B405085 : Blo 358757 405085 := bbase (se 3 (by rfl) ⟨75953, by rfl⟩ : syracuseStep 405085 = 151907) (by norm_num)
theorem B470641 : Blo 358757 470641 := bbase (se 2 (by rfl) ⟨176490, by rfl⟩ : syracuseStep 470641 = 352981) (by norm_num)
theorem B405121 : Blo 358757 405121 := bbase (se 2 (by rfl) ⟨151920, by rfl⟩ : syracuseStep 405121 = 303841) (by norm_num)
theorem B405157 : Blo 358757 405157 := bbase (se 4 (by rfl) ⟨37983, by rfl⟩ : syracuseStep 405157 = 75967) (by norm_num)
theorem B405193 : Blo 358757 405193 := bbase (se 2 (by rfl) ⟨151947, by rfl⟩ : syracuseStep 405193 = 303895) (by norm_num)
theorem B437981 : Blo 358757 437981 := bbase (se 3 (by rfl) ⟨82121, by rfl⟩ : syracuseStep 437981 = 164243) (by norm_num)
theorem B405229 : Blo 358757 405229 := bbase (se 3 (by rfl) ⟨75980, by rfl⟩ : syracuseStep 405229 = 151961) (by norm_num)
theorem B405265 : Blo 358757 405265 := bbase (se 2 (by rfl) ⟨151974, by rfl⟩ : syracuseStep 405265 = 303949) (by norm_num)
theorem B405301 : Blo 358757 405301 := bbase (se 5 (by rfl) ⟨18998, by rfl⟩ : syracuseStep 405301 = 37997) (by norm_num)
theorem B405337 : Blo 358757 405337 := bbase (se 2 (by rfl) ⟨152001, by rfl⟩ : syracuseStep 405337 = 304003) (by norm_num)
theorem B405373 : Blo 358757 405373 := bbase (se 3 (by rfl) ⟨76007, by rfl⟩ : syracuseStep 405373 = 152015) (by norm_num)
theorem B405409 : Blo 358757 405409 := bbase (se 2 (by rfl) ⟨152028, by rfl⟩ : syracuseStep 405409 = 304057) (by norm_num)
theorem B405445 : Blo 358757 405445 := bbase (se 4 (by rfl) ⟨38010, by rfl⟩ : syracuseStep 405445 = 76021) (by norm_num)
theorem B733133 : Blo 358757 733133 := bbase (se 3 (by rfl) ⟨137462, by rfl⟩ : syracuseStep 733133 = 274925) (by norm_num)
theorem B405481 : Blo 358757 405481 := bbase (se 2 (by rfl) ⟨152055, by rfl⟩ : syracuseStep 405481 = 304111) (by norm_num)
theorem B405517 : Blo 358757 405517 := bbase (se 3 (by rfl) ⟨76034, by rfl⟩ : syracuseStep 405517 = 152069) (by norm_num)
theorem B405553 : Blo 358757 405553 := bbase (se 2 (by rfl) ⟨152082, by rfl⟩ : syracuseStep 405553 = 304165) (by norm_num)
theorem B405589 : Blo 358757 405589 := bbase (se 8 (by rfl) ⟨2376, by rfl⟩ : syracuseStep 405589 = 4753) (by norm_num)
theorem B405625 : Blo 358757 405625 := bbase (se 2 (by rfl) ⟨152109, by rfl⟩ : syracuseStep 405625 = 304219) (by norm_num)
theorem B405661 : Blo 358757 405661 := bbase (se 3 (by rfl) ⟨76061, by rfl⟩ : syracuseStep 405661 = 152123) (by norm_num)
theorem B405697 : Blo 358757 405697 := bbase (se 2 (by rfl) ⟨152136, by rfl⟩ : syracuseStep 405697 = 304273) (by norm_num)
theorem B405733 : Blo 358757 405733 := bbase (se 4 (by rfl) ⟨38037, by rfl⟩ : syracuseStep 405733 = 76075) (by norm_num)
theorem B1061093 : Blo 358757 1061093 := bbase (se 4 (by rfl) ⟨99477, by rfl⟩ : syracuseStep 1061093 = 198955) (by norm_num)
theorem B405769 : Blo 358757 405769 := bbase (se 2 (by rfl) ⟨152163, by rfl⟩ : syracuseStep 405769 = 304327) (by norm_num)
theorem B405805 : Blo 358757 405805 := bbase (se 3 (by rfl) ⟨76088, by rfl⟩ : syracuseStep 405805 = 152177) (by norm_num)
theorem B405841 : Blo 358757 405841 := bbase (se 2 (by rfl) ⟨152190, by rfl⟩ : syracuseStep 405841 = 304381) (by norm_num)
theorem B2044277 : Blo 358757 2044277 := bbase (se 5 (by rfl) ⟨95825, by rfl⟩ : syracuseStep 2044277 = 191651) (by norm_num)
theorem B405877 : Blo 358757 405877 := bbase (se 5 (by rfl) ⟨19025, by rfl⟩ : syracuseStep 405877 = 38051) (by norm_num)
theorem B405913 : Blo 358757 405913 := bbase (se 2 (by rfl) ⟨152217, by rfl⟩ : syracuseStep 405913 = 304435) (by norm_num)
theorem B405949 : Blo 358757 405949 := bbase (se 3 (by rfl) ⟨76115, by rfl⟩ : syracuseStep 405949 = 152231) (by norm_num)
theorem B930253 : Blo 358757 930253 := bbase (se 3 (by rfl) ⟨174422, by rfl⟩ : syracuseStep 930253 = 348845) (by norm_num)
theorem B405985 : Blo 358757 405985 := bbase (se 2 (by rfl) ⟨152244, by rfl⟩ : syracuseStep 405985 = 304489) (by norm_num)
theorem B1749509 : Blo 358757 1749509 := bbase (se 4 (by rfl) ⟨164016, by rfl⟩ : syracuseStep 1749509 = 328033) (by norm_num)
theorem B406021 : Blo 358757 406021 := bbase (se 4 (by rfl) ⟨38064, by rfl⟩ : syracuseStep 406021 = 76129) (by norm_num)
theorem B766493 : Blo 358757 766493 := bbase (se 3 (by rfl) ⟨143717, by rfl⟩ : syracuseStep 766493 = 287435) (by norm_num)
theorem B406057 : Blo 358757 406057 := bbase (se 2 (by rfl) ⟨152271, by rfl⟩ : syracuseStep 406057 = 304543) (by norm_num)
theorem B2142773 : Blo 358757 2142773 := bbase (se 5 (by rfl) ⟨100442, by rfl⟩ : syracuseStep 2142773 = 200885) (by norm_num)
theorem B406093 : Blo 358757 406093 := bbase (se 3 (by rfl) ⟨76142, by rfl⟩ : syracuseStep 406093 = 152285) (by norm_num)
theorem B406129 : Blo 358757 406129 := bbase (se 2 (by rfl) ⟨152298, by rfl⟩ : syracuseStep 406129 = 304597) (by norm_num)
theorem B406165 : Blo 358757 406165 := bbase (se 6 (by rfl) ⟨9519, by rfl⟩ : syracuseStep 406165 = 19039) (by norm_num)
theorem B1389221 : Blo 358757 1389221 := bbase (se 4 (by rfl) ⟨130239, by rfl⟩ : syracuseStep 1389221 = 260479) (by norm_num)
theorem B406201 : Blo 358757 406201 := bbase (se 2 (by rfl) ⟨152325, by rfl⟩ : syracuseStep 406201 = 304651) (by norm_num)
theorem B406237 : Blo 358757 406237 := bbase (se 3 (by rfl) ⟨76169, by rfl⟩ : syracuseStep 406237 = 152339) (by norm_num)
theorem B406273 : Blo 358757 406273 := bbase (se 2 (by rfl) ⟨152352, by rfl⟩ : syracuseStep 406273 = 304705) (by norm_num)
theorem B766741 : Blo 358757 766741 := bbase (se 6 (by rfl) ⟨17970, by rfl⟩ : syracuseStep 766741 = 35941) (by norm_num)
theorem B406309 : Blo 358757 406309 := bbase (se 4 (by rfl) ⟨38091, by rfl⟩ : syracuseStep 406309 = 76183) (by norm_num)
theorem B406345 : Blo 358757 406345 := bbase (se 2 (by rfl) ⟨152379, by rfl⟩ : syracuseStep 406345 = 304759) (by norm_num)
theorem B406381 : Blo 358757 406381 := bbase (se 3 (by rfl) ⟨76196, by rfl⟩ : syracuseStep 406381 = 152393) (by norm_num)
theorem B406417 : Blo 358757 406417 := bbase (se 2 (by rfl) ⟨152406, by rfl⟩ : syracuseStep 406417 = 304813) (by norm_num)
theorem B406453 : Blo 358757 406453 := bbase (se 5 (by rfl) ⟨19052, by rfl⟩ : syracuseStep 406453 = 38105) (by norm_num)
theorem B406489 : Blo 358757 406489 := bbase (se 2 (by rfl) ⟨152433, by rfl⟩ : syracuseStep 406489 = 304867) (by norm_num)
theorem B406525 : Blo 358757 406525 := bbase (se 3 (by rfl) ⟨76223, by rfl⟩ : syracuseStep 406525 = 152447) (by norm_num)
theorem B406561 : Blo 358757 406561 := bbase (se 2 (by rfl) ⟨152460, by rfl⟩ : syracuseStep 406561 = 304921) (by norm_num)
theorem B406597 : Blo 358757 406597 := bbase (se 4 (by rfl) ⟨38118, by rfl⟩ : syracuseStep 406597 = 76237) (by norm_num)
theorem B406633 : Blo 358757 406633 := bbase (se 2 (by rfl) ⟨152487, by rfl⟩ : syracuseStep 406633 = 304975) (by norm_num)
theorem B406669 : Blo 358757 406669 := bbase (se 3 (by rfl) ⟨76250, by rfl⟩ : syracuseStep 406669 = 152501) (by norm_num)
theorem B406705 : Blo 358757 406705 := bbase (se 2 (by rfl) ⟨152514, by rfl⟩ : syracuseStep 406705 = 305029) (by norm_num)
theorem B406741 : Blo 358757 406741 := bbase (se 7 (by rfl) ⟨4766, by rfl⟩ : syracuseStep 406741 = 9533) (by norm_num)
theorem B406777 : Blo 358757 406777 := bbase (se 2 (by rfl) ⟨152541, by rfl⟩ : syracuseStep 406777 = 305083) (by norm_num)
theorem B767245 : Blo 358757 767245 := bbase (se 3 (by rfl) ⟨143858, by rfl⟩ : syracuseStep 767245 = 287717) (by norm_num)
theorem B406813 : Blo 358757 406813 := bbase (se 3 (by rfl) ⟨76277, by rfl⟩ : syracuseStep 406813 = 152555) (by norm_num)
theorem B406849 : Blo 358757 406849 := bbase (se 2 (by rfl) ⟨152568, by rfl⟩ : syracuseStep 406849 = 305137) (by norm_num)
theorem B406885 : Blo 358757 406885 := bbase (se 4 (by rfl) ⟨38145, by rfl⟩ : syracuseStep 406885 = 76291) (by norm_num)
theorem B1095029 : Blo 358757 1095029 := bbase (se 5 (by rfl) ⟨51329, by rfl⟩ : syracuseStep 1095029 = 102659) (by norm_num)
theorem B406921 : Blo 358757 406921 := bbase (se 2 (by rfl) ⟨152595, by rfl⟩ : syracuseStep 406921 = 305191) (by norm_num)
theorem B406957 : Blo 358757 406957 := bbase (se 3 (by rfl) ⟨76304, by rfl⟩ : syracuseStep 406957 = 152609) (by norm_num)
theorem B406993 : Blo 358757 406993 := bbase (se 2 (by rfl) ⟨152622, by rfl⟩ : syracuseStep 406993 = 305245) (by norm_num)
theorem B1095125 : Blo 358757 1095125 := bbase (se 7 (by rfl) ⟨12833, by rfl⟩ : syracuseStep 1095125 = 25667) (by norm_num)
theorem B2635253 : Blo 358757 2635253 := bbase (se 5 (by rfl) ⟨123527, by rfl⟩ : syracuseStep 2635253 = 247055) (by norm_num)
theorem B407029 : Blo 358757 407029 := bbase (se 5 (by rfl) ⟨19079, by rfl⟩ : syracuseStep 407029 = 38159) (by norm_num)
theorem B407065 : Blo 358757 407065 := bbase (se 2 (by rfl) ⟨152649, by rfl⟩ : syracuseStep 407065 = 305299) (by norm_num)
theorem B538157 : Blo 358757 538157 := bbase (se 3 (by rfl) ⟨100904, by rfl⟩ : syracuseStep 538157 = 201809) (by norm_num)
theorem B407101 : Blo 358757 407101 := bbase (se 3 (by rfl) ⟨76331, by rfl⟩ : syracuseStep 407101 = 152663) (by norm_num)
theorem B538181 : Blo 358757 538181 := bbase (se 4 (by rfl) ⟨50454, by rfl⟩ : syracuseStep 538181 = 100909) (by norm_num)
theorem B538205 : Blo 358757 538205 := bbase (se 3 (by rfl) ⟨100913, by rfl⟩ : syracuseStep 538205 = 201827) (by norm_num)
theorem B407137 : Blo 358757 407137 := bbase (se 2 (by rfl) ⟨152676, by rfl⟩ : syracuseStep 407137 = 305353) (by norm_num)
theorem B538229 : Blo 358757 538229 := bbase (se 5 (by rfl) ⟨25229, by rfl⟩ : syracuseStep 538229 = 50459) (by norm_num)
theorem B407173 : Blo 358757 407173 := bbase (se 4 (by rfl) ⟨38172, by rfl⟩ : syracuseStep 407173 = 76345) (by norm_num)
theorem B1160837 : Blo 358757 1160837 := bbase (se 4 (by rfl) ⟨108828, by rfl⟩ : syracuseStep 1160837 = 217657) (by norm_num)
theorem B538253 : Blo 358757 538253 := bbase (se 3 (by rfl) ⟨100922, by rfl⟩ : syracuseStep 538253 = 201845) (by norm_num)
theorem B538277 : Blo 358757 538277 := bbase (se 4 (by rfl) ⟨50463, by rfl⟩ : syracuseStep 538277 = 100927) (by norm_num)
theorem B407209 : Blo 358757 407209 := bbase (se 2 (by rfl) ⟨152703, by rfl⟩ : syracuseStep 407209 = 305407) (by norm_num)
theorem B2733749 : Blo 358757 2733749 := bbase (se 5 (by rfl) ⟨128144, by rfl⟩ : syracuseStep 2733749 = 256289) (by norm_num)
theorem B538301 : Blo 358757 538301 := bbase (se 3 (by rfl) ⟨100931, by rfl⟩ : syracuseStep 538301 = 201863) (by norm_num)
theorem B407245 : Blo 358757 407245 := bbase (se 3 (by rfl) ⟨76358, by rfl⟩ : syracuseStep 407245 = 152717) (by norm_num)
theorem B538325 : Blo 358757 538325 := bbase (se 7 (by rfl) ⟨6308, by rfl⟩ : syracuseStep 538325 = 12617) (by norm_num)
theorem B538349 : Blo 358757 538349 := bbase (se 3 (by rfl) ⟨100940, by rfl⟩ : syracuseStep 538349 = 201881) (by norm_num)
theorem B407281 : Blo 358757 407281 := bbase (se 2 (by rfl) ⟨152730, by rfl⟩ : syracuseStep 407281 = 305461) (by norm_num)
theorem B866045 : Blo 358757 866045 := bbase (se 3 (by rfl) ⟨162383, by rfl⟩ : syracuseStep 866045 = 324767) (by norm_num)
theorem B538373 : Blo 358757 538373 := bbase (se 4 (by rfl) ⟨50472, by rfl⟩ : syracuseStep 538373 = 100945) (by norm_num)
theorem B4110101 : Blo 358757 4110101 := bbase (se 6 (by rfl) ⟨96330, by rfl⟩ : syracuseStep 4110101 = 192661) (by norm_num)
theorem B407317 : Blo 358757 407317 := bbase (se 6 (by rfl) ⟨9546, by rfl⟩ : syracuseStep 407317 = 19093) (by norm_num)
theorem B538397 : Blo 358757 538397 := bbase (se 3 (by rfl) ⟨100949, by rfl⟩ : syracuseStep 538397 = 201899) (by norm_num)
theorem B538421 : Blo 358757 538421 := bbase (se 5 (by rfl) ⟨25238, by rfl⟩ : syracuseStep 538421 = 50477) (by norm_num)
theorem B1029941 : Blo 358757 1029941 := bbase (se 5 (by rfl) ⟨48278, by rfl⟩ : syracuseStep 1029941 = 96557) (by norm_num)
theorem B407353 : Blo 358757 407353 := bbase (se 2 (by rfl) ⟨152757, by rfl⟩ : syracuseStep 407353 = 305515) (by norm_num)
theorem B538445 : Blo 358757 538445 := bbase (se 3 (by rfl) ⟨100958, by rfl⟩ : syracuseStep 538445 = 201917) (by norm_num)
theorem B407389 : Blo 358757 407389 := bbase (se 3 (by rfl) ⟨76385, by rfl⟩ : syracuseStep 407389 = 152771) (by norm_num)
theorem B538469 : Blo 358757 538469 := bbase (se 4 (by rfl) ⟨50481, by rfl⟩ : syracuseStep 538469 = 100963) (by norm_num)
theorem B538493 : Blo 358757 538493 := bbase (se 3 (by rfl) ⟨100967, by rfl⟩ : syracuseStep 538493 = 201935) (by norm_num)
theorem B407425 : Blo 358757 407425 := bbase (se 2 (by rfl) ⟨152784, by rfl⟩ : syracuseStep 407425 = 305569) (by norm_num)
theorem B538517 : Blo 358757 538517 := bbase (se 6 (by rfl) ⟨12621, by rfl⟩ : syracuseStep 538517 = 25243) (by norm_num)
theorem B407461 : Blo 358757 407461 := bbase (se 4 (by rfl) ⟨38199, by rfl⟩ : syracuseStep 407461 = 76399) (by norm_num)
theorem B538541 : Blo 358757 538541 := bbase (se 3 (by rfl) ⟨100976, by rfl⟩ : syracuseStep 538541 = 201953) (by norm_num)
theorem B538565 : Blo 358757 538565 := bbase (se 4 (by rfl) ⟨50490, by rfl⟩ : syracuseStep 538565 = 100981) (by norm_num)
theorem B407497 : Blo 358757 407497 := bbase (se 2 (by rfl) ⟨152811, by rfl⟩ : syracuseStep 407497 = 305623) (by norm_num)
theorem B538589 : Blo 358757 538589 := bbase (se 3 (by rfl) ⟨100985, by rfl⟩ : syracuseStep 538589 = 201971) (by norm_num)
theorem B407533 : Blo 358757 407533 := bbase (se 3 (by rfl) ⟨76412, by rfl⟩ : syracuseStep 407533 = 152825) (by norm_num)
theorem B538613 : Blo 358757 538613 := bbase (se 5 (by rfl) ⟨25247, by rfl⟩ : syracuseStep 538613 = 50495) (by norm_num)
theorem B538637 : Blo 358757 538637 := bbase (se 3 (by rfl) ⟨100994, by rfl⟩ : syracuseStep 538637 = 201989) (by norm_num)
theorem B407569 : Blo 358757 407569 := bbase (se 2 (by rfl) ⟨152838, by rfl⟩ : syracuseStep 407569 = 305677) (by norm_num)
theorem B538661 : Blo 358757 538661 := bbase (se 4 (by rfl) ⟨50499, by rfl⟩ : syracuseStep 538661 = 100999) (by norm_num)
theorem B407605 : Blo 358757 407605 := bbase (se 5 (by rfl) ⟨19106, by rfl⟩ : syracuseStep 407605 = 38213) (by norm_num)
theorem B538685 : Blo 358757 538685 := bbase (se 3 (by rfl) ⟨101003, by rfl⟩ : syracuseStep 538685 = 202007) (by norm_num)
theorem B538709 : Blo 358757 538709 := bbase (se 8 (by rfl) ⟨3156, by rfl⟩ : syracuseStep 538709 = 6313) (by norm_num)
theorem B407641 : Blo 358757 407641 := bbase (se 2 (by rfl) ⟨152865, by rfl⟩ : syracuseStep 407641 = 305731) (by norm_num)
theorem B538733 : Blo 358757 538733 := bbase (se 3 (by rfl) ⟨101012, by rfl⟩ : syracuseStep 538733 = 202025) (by norm_num)
theorem B866429 : Blo 358757 866429 := bbase (se 3 (by rfl) ⟨162455, by rfl⟩ : syracuseStep 866429 = 324911) (by norm_num)
theorem B407677 : Blo 358757 407677 := bbase (se 3 (by rfl) ⟨76439, by rfl⟩ : syracuseStep 407677 = 152879) (by norm_num)
theorem B538757 : Blo 358757 538757 := bbase (se 4 (by rfl) ⟨50508, by rfl⟩ : syracuseStep 538757 = 101017) (by norm_num)
theorem B768133 : Blo 358757 768133 := bbase (se 4 (by rfl) ⟨72012, by rfl⟩ : syracuseStep 768133 = 144025) (by norm_num)
theorem B538781 : Blo 358757 538781 := bbase (se 3 (by rfl) ⟨101021, by rfl⟩ : syracuseStep 538781 = 202043) (by norm_num)
theorem B407713 : Blo 358757 407713 := bbase (se 2 (by rfl) ⟨152892, by rfl⟩ : syracuseStep 407713 = 305785) (by norm_num)
theorem B538805 : Blo 358757 538805 := bbase (se 5 (by rfl) ⟨25256, by rfl⟩ : syracuseStep 538805 = 50513) (by norm_num)
theorem B407749 : Blo 358757 407749 := bbase (se 4 (by rfl) ⟨38226, by rfl⟩ : syracuseStep 407749 = 76453) (by norm_num)
theorem B538829 : Blo 358757 538829 := bbase (se 3 (by rfl) ⟨101030, by rfl⟩ : syracuseStep 538829 = 202061) (by norm_num)
theorem B538853 : Blo 358757 538853 := bbase (se 4 (by rfl) ⟨50517, by rfl⟩ : syracuseStep 538853 = 101035) (by norm_num)
theorem B407785 : Blo 358757 407785 := bbase (se 2 (by rfl) ⟨152919, by rfl⟩ : syracuseStep 407785 = 305839) (by norm_num)
theorem B538877 : Blo 358757 538877 := bbase (se 3 (by rfl) ⟨101039, by rfl⟩ : syracuseStep 538877 = 202079) (by norm_num)
theorem B407821 : Blo 358757 407821 := bbase (se 3 (by rfl) ⟨76466, by rfl⟩ : syracuseStep 407821 = 152933) (by norm_num)
theorem B538901 : Blo 358757 538901 := bbase (se 6 (by rfl) ⟨12630, by rfl⟩ : syracuseStep 538901 = 25261) (by norm_num)
theorem B538925 : Blo 358757 538925 := bbase (se 3 (by rfl) ⟨101048, by rfl⟩ : syracuseStep 538925 = 202097) (by norm_num)
theorem B407857 : Blo 358757 407857 := bbase (se 2 (by rfl) ⟨152946, by rfl⟩ : syracuseStep 407857 = 305893) (by norm_num)
theorem B538949 : Blo 358757 538949 := bbase (se 4 (by rfl) ⟨50526, by rfl⟩ : syracuseStep 538949 = 101053) (by norm_num)
theorem B866629 : Blo 358757 866629 := bbase (se 4 (by rfl) ⟨81246, by rfl⟩ : syracuseStep 866629 = 162493) (by norm_num)
theorem B407893 : Blo 358757 407893 := bbase (se 10 (by rfl) ⟨597, by rfl⟩ : syracuseStep 407893 = 1195) (by norm_num)
theorem B538973 : Blo 358757 538973 := bbase (se 3 (by rfl) ⟨101057, by rfl⟩ : syracuseStep 538973 = 202115) (by norm_num)
theorem B538997 : Blo 358757 538997 := bbase (se 5 (by rfl) ⟨25265, by rfl⟩ : syracuseStep 538997 = 50531) (by norm_num)
theorem B407929 : Blo 358757 407929 := bbase (se 2 (by rfl) ⟨152973, by rfl⟩ : syracuseStep 407929 = 305947) (by norm_num)
theorem B539021 : Blo 358757 539021 := bbase (se 3 (by rfl) ⟨101066, by rfl⟩ : syracuseStep 539021 = 202133) (by norm_num)
theorem B407965 : Blo 358757 407965 := bbase (se 3 (by rfl) ⟨76493, by rfl⟩ : syracuseStep 407965 = 152987) (by norm_num)
theorem B539045 : Blo 358757 539045 := bbase (se 4 (by rfl) ⟨50535, by rfl⟩ : syracuseStep 539045 = 101071) (by norm_num)
theorem B539069 : Blo 358757 539069 := bbase (se 3 (by rfl) ⟨101075, by rfl⟩ : syracuseStep 539069 = 202151) (by norm_num)
theorem B408001 : Blo 358757 408001 := bbase (se 2 (by rfl) ⟨153000, by rfl⟩ : syracuseStep 408001 = 306001) (by norm_num)
theorem B539093 : Blo 358757 539093 := bbase (se 7 (by rfl) ⟨6317, by rfl⟩ : syracuseStep 539093 = 12635) (by norm_num)
theorem B408037 : Blo 358757 408037 := bbase (se 4 (by rfl) ⟨38253, by rfl⟩ : syracuseStep 408037 = 76507) (by norm_num)
theorem B539117 : Blo 358757 539117 := bbase (se 3 (by rfl) ⟨101084, by rfl⟩ : syracuseStep 539117 = 202169) (by norm_num)
theorem B539141 : Blo 358757 539141 := bbase (se 4 (by rfl) ⟨50544, by rfl⟩ : syracuseStep 539141 = 101089) (by norm_num)
theorem B408073 : Blo 358757 408073 := bbase (se 2 (by rfl) ⟨153027, by rfl⟩ : syracuseStep 408073 = 306055) (by norm_num)
theorem B2046485 : Blo 358757 2046485 := bbase (se 6 (by rfl) ⟨47964, by rfl⟩ : syracuseStep 2046485 = 95929) (by norm_num)
theorem B539165 : Blo 358757 539165 := bbase (se 3 (by rfl) ⟨101093, by rfl⟩ : syracuseStep 539165 = 202187) (by norm_num)
theorem B539189 : Blo 358757 539189 := bbase (se 5 (by rfl) ⟨25274, by rfl⟩ : syracuseStep 539189 = 50549) (by norm_num)
theorem B539213 : Blo 358757 539213 := bbase (se 3 (by rfl) ⟨101102, by rfl⟩ : syracuseStep 539213 = 202205) (by norm_num)
theorem B539237 : Blo 358757 539237 := bbase (se 4 (by rfl) ⟨50553, by rfl⟩ : syracuseStep 539237 = 101107) (by norm_num)
theorem B768629 : Blo 358757 768629 := bbase (se 5 (by rfl) ⟨36029, by rfl⟩ : syracuseStep 768629 = 72059) (by norm_num)
theorem B539261 : Blo 358757 539261 := bbase (se 3 (by rfl) ⟨101111, by rfl⟩ : syracuseStep 539261 = 202223) (by norm_num)
theorem B539285 : Blo 358757 539285 := bbase (se 6 (by rfl) ⟨12639, by rfl⟩ : syracuseStep 539285 = 25279) (by norm_num)
theorem B539309 : Blo 358757 539309 := bbase (se 3 (by rfl) ⟨101120, by rfl⟩ : syracuseStep 539309 = 202241) (by norm_num)
theorem B539333 : Blo 358757 539333 := bbase (se 4 (by rfl) ⟨50562, by rfl⟩ : syracuseStep 539333 = 101125) (by norm_num)
theorem B539357 : Blo 358757 539357 := bbase (se 3 (by rfl) ⟨101129, by rfl⟩ : syracuseStep 539357 = 202259) (by norm_num)
theorem B539381 : Blo 358757 539381 := bbase (se 5 (by rfl) ⟨25283, by rfl⟩ : syracuseStep 539381 = 50567) (by norm_num)
theorem B539405 : Blo 358757 539405 := bbase (se 3 (by rfl) ⟨101138, by rfl⟩ : syracuseStep 539405 = 202277) (by norm_num)
theorem B539429 : Blo 358757 539429 := bbase (se 4 (by rfl) ⟨50571, by rfl⟩ : syracuseStep 539429 = 101143) (by norm_num)
theorem B539453 : Blo 358757 539453 := bbase (se 3 (by rfl) ⟨101147, by rfl⟩ : syracuseStep 539453 = 202295) (by norm_num)
theorem B539477 : Blo 358757 539477 := bbase (se 9 (by rfl) ⟨1580, by rfl⟩ : syracuseStep 539477 = 3161) (by norm_num)
theorem B539501 : Blo 358757 539501 := bbase (se 3 (by rfl) ⟨101156, by rfl⟩ : syracuseStep 539501 = 202313) (by norm_num)
theorem B1817477 : Blo 358757 1817477 := bbase (se 4 (by rfl) ⟨170388, by rfl⟩ : syracuseStep 1817477 = 340777) (by norm_num)
theorem B539525 : Blo 358757 539525 := bbase (se 4 (by rfl) ⟨50580, by rfl⟩ : syracuseStep 539525 = 101161) (by norm_num)
theorem B1162117 : Blo 358757 1162117 := bbase (se 4 (by rfl) ⟨108948, by rfl⟩ : syracuseStep 1162117 = 217897) (by norm_num)
theorem B539549 : Blo 358757 539549 := bbase (se 3 (by rfl) ⟨101165, by rfl⟩ : syracuseStep 539549 = 202331) (by norm_num)
theorem B539573 : Blo 358757 539573 := bbase (se 5 (by rfl) ⟨25292, by rfl⟩ : syracuseStep 539573 = 50585) (by norm_num)
theorem B539597 : Blo 358757 539597 := bbase (se 3 (by rfl) ⟨101174, by rfl⟩ : syracuseStep 539597 = 202349) (by norm_num)
theorem B1031125 : Blo 358757 1031125 := bbase (se 7 (by rfl) ⟨12083, by rfl⟩ : syracuseStep 1031125 = 24167) (by norm_num)
theorem B539621 : Blo 358757 539621 := bbase (se 4 (by rfl) ⟨50589, by rfl⟩ : syracuseStep 539621 = 101179) (by norm_num)
theorem B539645 : Blo 358757 539645 := bbase (se 3 (by rfl) ⟨101183, by rfl⟩ : syracuseStep 539645 = 202367) (by norm_num)
theorem B539669 : Blo 358757 539669 := bbase (se 6 (by rfl) ⟨12648, by rfl⟩ : syracuseStep 539669 = 25297) (by norm_num)
theorem B539693 : Blo 358757 539693 := bbase (se 3 (by rfl) ⟨101192, by rfl⟩ : syracuseStep 539693 = 202385) (by norm_num)
theorem B539717 : Blo 358757 539717 := bbase (se 4 (by rfl) ⟨50598, by rfl⟩ : syracuseStep 539717 = 101197) (by norm_num)
theorem B539741 : Blo 358757 539741 := bbase (se 3 (by rfl) ⟨101201, by rfl⟩ : syracuseStep 539741 = 202403) (by norm_num)
theorem B539765 : Blo 358757 539765 := bbase (se 5 (by rfl) ⟨25301, by rfl⟩ : syracuseStep 539765 = 50603) (by norm_num)
theorem B1031285 : Blo 358757 1031285 := bbase (se 5 (by rfl) ⟨48341, by rfl⟩ : syracuseStep 1031285 = 96683) (by norm_num)
theorem B539789 : Blo 358757 539789 := bbase (se 3 (by rfl) ⟨101210, by rfl⟩ : syracuseStep 539789 = 202421) (by norm_num)
theorem B539813 : Blo 358757 539813 := bbase (se 4 (by rfl) ⟨50607, by rfl⟩ : syracuseStep 539813 = 101215) (by norm_num)
theorem B539837 : Blo 358757 539837 := bbase (se 3 (by rfl) ⟨101219, by rfl⟩ : syracuseStep 539837 = 202439) (by norm_num)
theorem B539861 : Blo 358757 539861 := bbase (se 7 (by rfl) ⟨6326, by rfl⟩ : syracuseStep 539861 = 12653) (by norm_num)
theorem B539885 : Blo 358757 539885 := bbase (se 3 (by rfl) ⟨101228, by rfl⟩ : syracuseStep 539885 = 202457) (by norm_num)
theorem B933125 : Blo 358757 933125 := bbase (se 4 (by rfl) ⟨87480, by rfl⟩ : syracuseStep 933125 = 174961) (by norm_num)
theorem B539909 : Blo 358757 539909 := bbase (se 4 (by rfl) ⟨50616, by rfl⟩ : syracuseStep 539909 = 101233) (by norm_num)
theorem B605461 : Blo 358757 605461 := bbase (se 6 (by rfl) ⟨14190, by rfl⟩ : syracuseStep 605461 = 28381) (by norm_num)
theorem B539933 : Blo 358757 539933 := bbase (se 3 (by rfl) ⟨101237, by rfl⟩ : syracuseStep 539933 = 202475) (by norm_num)
theorem B539957 : Blo 358757 539957 := bbase (se 5 (by rfl) ⟨25310, by rfl⟩ : syracuseStep 539957 = 50621) (by norm_num)
theorem B539981 : Blo 358757 539981 := bbase (se 3 (by rfl) ⟨101246, by rfl⟩ : syracuseStep 539981 = 202493) (by norm_num)
theorem B540005 : Blo 358757 540005 := bbase (se 4 (by rfl) ⟨50625, by rfl⟩ : syracuseStep 540005 = 101251) (by norm_num)
theorem B1031525 : Blo 358757 1031525 := bbase (se 4 (by rfl) ⟨96705, by rfl⟩ : syracuseStep 1031525 = 193411) (by norm_num)
theorem B605549 : Blo 358757 605549 := bbase (se 3 (by rfl) ⟨113540, by rfl⟩ : syracuseStep 605549 = 227081) (by norm_num)
theorem B540029 : Blo 358757 540029 := bbase (se 3 (by rfl) ⟨101255, by rfl⟩ : syracuseStep 540029 = 202511) (by norm_num)
theorem B540053 : Blo 358757 540053 := bbase (se 6 (by rfl) ⟨12657, by rfl⟩ : syracuseStep 540053 = 25315) (by norm_num)
theorem B540077 : Blo 358757 540077 := bbase (se 3 (by rfl) ⟨101264, by rfl⟩ : syracuseStep 540077 = 202529) (by norm_num)
theorem B540101 : Blo 358757 540101 := bbase (se 4 (by rfl) ⟨50634, by rfl⟩ : syracuseStep 540101 = 101269) (by norm_num)
theorem B540125 : Blo 358757 540125 := bbase (se 3 (by rfl) ⟨101273, by rfl⟩ : syracuseStep 540125 = 202547) (by norm_num)
theorem B605677 : Blo 358757 605677 := bbase (se 3 (by rfl) ⟨113564, by rfl⟩ : syracuseStep 605677 = 227129) (by norm_num)
theorem B769517 : Blo 358757 769517 := bbase (se 3 (by rfl) ⟨144284, by rfl⟩ : syracuseStep 769517 = 288569) (by norm_num)
theorem B540149 : Blo 358757 540149 := bbase (se 5 (by rfl) ⟨25319, by rfl⟩ : syracuseStep 540149 = 50639) (by norm_num)
theorem B540173 : Blo 358757 540173 := bbase (se 3 (by rfl) ⟨101282, by rfl⟩ : syracuseStep 540173 = 202565) (by norm_num)
theorem B540197 : Blo 358757 540197 := bbase (se 4 (by rfl) ⟨50643, by rfl⟩ : syracuseStep 540197 = 101287) (by norm_num)
theorem B1031717 : Blo 358757 1031717 := bbase (se 4 (by rfl) ⟨96723, by rfl⟩ : syracuseStep 1031717 = 193447) (by norm_num)
theorem B540221 : Blo 358757 540221 := bbase (se 3 (by rfl) ⟨101291, by rfl⟩ : syracuseStep 540221 = 202583) (by norm_num)
theorem B605765 : Blo 358757 605765 := bbase (se 4 (by rfl) ⟨56790, by rfl⟩ : syracuseStep 605765 = 113581) (by norm_num)
theorem B540245 : Blo 358757 540245 := bbase (se 8 (by rfl) ⟨3165, by rfl⟩ : syracuseStep 540245 = 6331) (by norm_num)
theorem B769637 : Blo 358757 769637 := bbase (se 4 (by rfl) ⟨72153, by rfl⟩ : syracuseStep 769637 = 144307) (by norm_num)
theorem B540269 : Blo 358757 540269 := bbase (se 3 (by rfl) ⟨101300, by rfl⟩ : syracuseStep 540269 = 202601) (by norm_num)
theorem B540293 : Blo 358757 540293 := bbase (se 4 (by rfl) ⟨50652, by rfl⟩ : syracuseStep 540293 = 101305) (by norm_num)
theorem B540317 : Blo 358757 540317 := bbase (se 3 (by rfl) ⟨101309, by rfl⟩ : syracuseStep 540317 = 202619) (by norm_num)
theorem B540341 : Blo 358757 540341 := bbase (se 5 (by rfl) ⟨25328, by rfl⟩ : syracuseStep 540341 = 50657) (by norm_num)
theorem B3096245 : Blo 358757 3096245 := bbase (se 5 (by rfl) ⟨145136, by rfl⟩ : syracuseStep 3096245 = 290273) (by norm_num)
theorem B409285 : Blo 358757 409285 := bbase (se 4 (by rfl) ⟨38370, by rfl⟩ : syracuseStep 409285 = 76741) (by norm_num)
theorem B605893 : Blo 358757 605893 := bbase (se 4 (by rfl) ⟨56802, by rfl⟩ : syracuseStep 605893 = 113605) (by norm_num)
theorem B540365 : Blo 358757 540365 := bbase (se 3 (by rfl) ⟨101318, by rfl⟩ : syracuseStep 540365 = 202637) (by norm_num)
theorem B540389 : Blo 358757 540389 := bbase (se 4 (by rfl) ⟨50661, by rfl⟩ : syracuseStep 540389 = 101323) (by norm_num)
theorem B540413 : Blo 358757 540413 := bbase (se 3 (by rfl) ⟨101327, by rfl⟩ : syracuseStep 540413 = 202655) (by norm_num)
theorem B540437 : Blo 358757 540437 := bbase (se 6 (by rfl) ⟨12666, by rfl⟩ : syracuseStep 540437 = 25333) (by norm_num)
theorem B605981 : Blo 358757 605981 := bbase (se 3 (by rfl) ⟨113621, by rfl⟩ : syracuseStep 605981 = 227243) (by norm_num)
theorem B540461 : Blo 358757 540461 := bbase (se 3 (by rfl) ⟨101336, by rfl⟩ : syracuseStep 540461 = 202673) (by norm_num)
theorem B540485 : Blo 358757 540485 := bbase (se 4 (by rfl) ⟨50670, by rfl⟩ : syracuseStep 540485 = 101341) (by norm_num)
theorem B540509 : Blo 358757 540509 := bbase (se 3 (by rfl) ⟨101345, by rfl⟩ : syracuseStep 540509 = 202691) (by norm_num)
theorem B868205 : Blo 358757 868205 := bbase (se 3 (by rfl) ⟨162788, by rfl⟩ : syracuseStep 868205 = 325577) (by norm_num)
theorem B540533 : Blo 358757 540533 := bbase (se 5 (by rfl) ⟨25337, by rfl⟩ : syracuseStep 540533 = 50675) (by norm_num)
theorem B540557 : Blo 358757 540557 := bbase (se 3 (by rfl) ⟨101354, by rfl⟩ : syracuseStep 540557 = 202709) (by norm_num)
theorem B606109 : Blo 358757 606109 := bbase (se 3 (by rfl) ⟨113645, by rfl⟩ : syracuseStep 606109 = 227291) (by norm_num)
theorem B540581 : Blo 358757 540581 := bbase (se 4 (by rfl) ⟨50679, by rfl⟩ : syracuseStep 540581 = 101359) (by norm_num)
theorem B540605 : Blo 358757 540605 := bbase (se 3 (by rfl) ⟨101363, by rfl⟩ : syracuseStep 540605 = 202727) (by norm_num)
theorem B540629 : Blo 358757 540629 := bbase (se 7 (by rfl) ⟨6335, by rfl⟩ : syracuseStep 540629 = 12671) (by norm_num)
theorem B540653 : Blo 358757 540653 := bbase (se 3 (by rfl) ⟨101372, by rfl⟩ : syracuseStep 540653 = 202745) (by norm_num)
theorem B606197 : Blo 358757 606197 := bbase (se 5 (by rfl) ⟨28415, by rfl⟩ : syracuseStep 606197 = 56831) (by norm_num)
theorem B540677 : Blo 358757 540677 := bbase (se 4 (by rfl) ⟨50688, by rfl⟩ : syracuseStep 540677 = 101377) (by norm_num)
theorem B540701 : Blo 358757 540701 := bbase (se 3 (by rfl) ⟨101381, by rfl⟩ : syracuseStep 540701 = 202763) (by norm_num)
theorem B540725 : Blo 358757 540725 := bbase (se 5 (by rfl) ⟨25346, by rfl⟩ : syracuseStep 540725 = 50693) (by norm_num)
theorem B540749 : Blo 358757 540749 := bbase (se 3 (by rfl) ⟨101390, by rfl⟩ : syracuseStep 540749 = 202781) (by norm_num)
theorem B3686485 : Blo 358757 3686485 := bbase (se 8 (by rfl) ⟨21600, by rfl⟩ : syracuseStep 3686485 = 43201) (by norm_num)
theorem B540773 : Blo 358757 540773 := bbase (se 4 (by rfl) ⟨50697, by rfl⟩ : syracuseStep 540773 = 101395) (by norm_num)
theorem B606325 : Blo 358757 606325 := bbase (se 5 (by rfl) ⟨28421, by rfl⟩ : syracuseStep 606325 = 56843) (by norm_num)
theorem B540797 : Blo 358757 540797 := bbase (se 3 (by rfl) ⟨101399, by rfl⟩ : syracuseStep 540797 = 202799) (by norm_num)
theorem B1818773 : Blo 358757 1818773 := bbase (se 6 (by rfl) ⟨42627, by rfl⟩ : syracuseStep 1818773 = 85255) (by norm_num)
theorem B540821 : Blo 358757 540821 := bbase (se 6 (by rfl) ⟨12675, by rfl⟩ : syracuseStep 540821 = 25351) (by norm_num)
theorem B540845 : Blo 358757 540845 := bbase (se 3 (by rfl) ⟨101408, by rfl⟩ : syracuseStep 540845 = 202817) (by norm_num)
theorem B540869 : Blo 358757 540869 := bbase (se 4 (by rfl) ⟨50706, by rfl⟩ : syracuseStep 540869 = 101413) (by norm_num)
theorem B606413 : Blo 358757 606413 := bbase (se 3 (by rfl) ⟨113702, by rfl⟩ : syracuseStep 606413 = 227405) (by norm_num)
theorem B540893 : Blo 358757 540893 := bbase (se 3 (by rfl) ⟨101417, by rfl⟩ : syracuseStep 540893 = 202835) (by norm_num)
theorem B770269 : Blo 358757 770269 := bbase (se 3 (by rfl) ⟨144425, by rfl⟩ : syracuseStep 770269 = 288851) (by norm_num)
theorem B540917 : Blo 358757 540917 := bbase (se 5 (by rfl) ⟨25355, by rfl⟩ : syracuseStep 540917 = 50711) (by norm_num)
theorem B540941 : Blo 358757 540941 := bbase (se 3 (by rfl) ⟨101426, by rfl⟩ : syracuseStep 540941 = 202853) (by norm_num)
theorem B540965 : Blo 358757 540965 := bbase (se 4 (by rfl) ⟨50715, by rfl⟩ : syracuseStep 540965 = 101431) (by norm_num)
theorem B540989 : Blo 358757 540989 := bbase (se 3 (by rfl) ⟨101435, by rfl⟩ : syracuseStep 540989 = 202871) (by norm_num)
theorem B606541 : Blo 358757 606541 := bbase (se 3 (by rfl) ⟨113726, by rfl⟩ : syracuseStep 606541 = 227453) (by norm_num)
theorem B541013 : Blo 358757 541013 := bbase (se 10 (by rfl) ⟨792, by rfl⟩ : syracuseStep 541013 = 1585) (by norm_num)
theorem B541037 : Blo 358757 541037 := bbase (se 3 (by rfl) ⟨101444, by rfl⟩ : syracuseStep 541037 = 202889) (by norm_num)
theorem B541061 : Blo 358757 541061 := bbase (se 4 (by rfl) ⟨50724, by rfl⟩ : syracuseStep 541061 = 101449) (by norm_num)
theorem B541085 : Blo 358757 541085 := bbase (se 3 (by rfl) ⟨101453, by rfl⟩ : syracuseStep 541085 = 202907) (by norm_num)
theorem B606629 : Blo 358757 606629 := bbase (se 4 (by rfl) ⟨56871, by rfl⟩ : syracuseStep 606629 = 113743) (by norm_num)
theorem B541109 : Blo 358757 541109 := bbase (se 5 (by rfl) ⟨25364, by rfl⟩ : syracuseStep 541109 = 50729) (by norm_num)
theorem B541133 : Blo 358757 541133 := bbase (se 3 (by rfl) ⟨101462, by rfl⟩ : syracuseStep 541133 = 202925) (by norm_num)
theorem B541157 : Blo 358757 541157 := bbase (se 4 (by rfl) ⟨50733, by rfl⟩ : syracuseStep 541157 = 101467) (by norm_num)
theorem B541181 : Blo 358757 541181 := bbase (se 3 (by rfl) ⟨101471, by rfl⟩ : syracuseStep 541181 = 202943) (by norm_num)
theorem B1032709 : Blo 358757 1032709 := bbase (se 4 (by rfl) ⟨96816, by rfl⟩ : syracuseStep 1032709 = 193633) (by norm_num)
theorem B541205 : Blo 358757 541205 := bbase (se 6 (by rfl) ⟨12684, by rfl⟩ : syracuseStep 541205 = 25369) (by norm_num)
theorem B606757 : Blo 358757 606757 := bbase (se 4 (by rfl) ⟨56883, by rfl⟩ : syracuseStep 606757 = 113767) (by norm_num)
theorem B541229 : Blo 358757 541229 := bbase (se 3 (by rfl) ⟨101480, by rfl⟩ : syracuseStep 541229 = 202961) (by norm_num)
theorem B410161 : Blo 358757 410161 := bbase (se 2 (by rfl) ⟨153810, by rfl⟩ : syracuseStep 410161 = 307621) (by norm_num)
theorem B541253 : Blo 358757 541253 := bbase (se 4 (by rfl) ⟨50742, by rfl⟩ : syracuseStep 541253 = 101485) (by norm_num)
theorem B1458773 : Blo 358757 1458773 := bbase (se 8 (by rfl) ⟨8547, by rfl⟩ : syracuseStep 1458773 = 17095) (by norm_num)
theorem B541277 : Blo 358757 541277 := bbase (se 3 (by rfl) ⟨101489, by rfl⟩ : syracuseStep 541277 = 202979) (by norm_num)
theorem B541301 : Blo 358757 541301 := bbase (se 5 (by rfl) ⟨25373, by rfl⟩ : syracuseStep 541301 = 50747) (by norm_num)
theorem B606845 : Blo 358757 606845 := bbase (se 3 (by rfl) ⟨113783, by rfl⟩ : syracuseStep 606845 = 227567) (by norm_num)
theorem B541325 : Blo 358757 541325 := bbase (se 3 (by rfl) ⟨101498, by rfl⟩ : syracuseStep 541325 = 202997) (by norm_num)
theorem B541349 : Blo 358757 541349 := bbase (se 4 (by rfl) ⟨50751, by rfl⟩ : syracuseStep 541349 = 101503) (by norm_num)
theorem B541373 : Blo 358757 541373 := bbase (se 3 (by rfl) ⟨101507, by rfl⟩ : syracuseStep 541373 = 203015) (by norm_num)
theorem B541397 : Blo 358757 541397 := bbase (se 7 (by rfl) ⟨6344, by rfl⟩ : syracuseStep 541397 = 12689) (by norm_num)
theorem B541421 : Blo 358757 541421 := bbase (se 3 (by rfl) ⟨101516, by rfl⟩ : syracuseStep 541421 = 203033) (by norm_num)
theorem B606973 : Blo 358757 606973 := bbase (se 3 (by rfl) ⟨113807, by rfl⟩ : syracuseStep 606973 = 227615) (by norm_num)
theorem B541445 : Blo 358757 541445 := bbase (se 4 (by rfl) ⟨50760, by rfl⟩ : syracuseStep 541445 = 101521) (by norm_num)
theorem B541469 : Blo 358757 541469 := bbase (se 3 (by rfl) ⟨101525, by rfl⟩ : syracuseStep 541469 = 203051) (by norm_num)
theorem B541493 : Blo 358757 541493 := bbase (se 5 (by rfl) ⟨25382, by rfl⟩ : syracuseStep 541493 = 50765) (by norm_num)
theorem B541517 : Blo 358757 541517 := bbase (se 3 (by rfl) ⟨101534, by rfl⟩ : syracuseStep 541517 = 203069) (by norm_num)
theorem B607061 : Blo 358757 607061 := bbase (se 9 (by rfl) ⟨1778, by rfl⟩ : syracuseStep 607061 = 3557) (by norm_num)
theorem B541541 : Blo 358757 541541 := bbase (se 4 (by rfl) ⟨50769, by rfl⟩ : syracuseStep 541541 = 101539) (by norm_num)
theorem B2474869 : Blo 358757 2474869 := bbase (se 5 (by rfl) ⟨116009, by rfl⟩ : syracuseStep 2474869 = 232019) (by norm_num)
theorem B541565 : Blo 358757 541565 := bbase (se 3 (by rfl) ⟨101543, by rfl⟩ : syracuseStep 541565 = 203087) (by norm_num)
theorem B934789 : Blo 358757 934789 := bbase (se 4 (by rfl) ⟨87636, by rfl⟩ : syracuseStep 934789 = 175273) (by norm_num)
theorem B541589 : Blo 358757 541589 := bbase (se 6 (by rfl) ⟨12693, by rfl⟩ : syracuseStep 541589 = 25387) (by norm_num)
theorem B541613 : Blo 358757 541613 := bbase (se 3 (by rfl) ⟨101552, by rfl⟩ : syracuseStep 541613 = 203105) (by norm_num)
theorem B541637 : Blo 358757 541637 := bbase (se 4 (by rfl) ⟨50778, by rfl⟩ : syracuseStep 541637 = 101557) (by norm_num)
theorem B607189 : Blo 358757 607189 := bbase (se 7 (by rfl) ⟨7115, by rfl⟩ : syracuseStep 607189 = 14231) (by norm_num)
theorem B541661 : Blo 358757 541661 := bbase (se 3 (by rfl) ⟨101561, by rfl⟩ : syracuseStep 541661 = 203123) (by norm_num)
theorem B541685 : Blo 358757 541685 := bbase (se 5 (by rfl) ⟨25391, by rfl⟩ : syracuseStep 541685 = 50783) (by norm_num)
theorem B541709 : Blo 358757 541709 := bbase (se 3 (by rfl) ⟨101570, by rfl⟩ : syracuseStep 541709 = 203141) (by norm_num)
theorem B541733 : Blo 358757 541733 := bbase (se 4 (by rfl) ⟨50787, by rfl⟩ : syracuseStep 541733 = 101575) (by norm_num)
theorem B607277 : Blo 358757 607277 := bbase (se 3 (by rfl) ⟨113864, by rfl⟩ : syracuseStep 607277 = 227729) (by norm_num)
theorem B541757 : Blo 358757 541757 := bbase (se 3 (by rfl) ⟨101579, by rfl⟩ : syracuseStep 541757 = 203159) (by norm_num)
theorem B771157 : Blo 358757 771157 := bbase (se 8 (by rfl) ⟨4518, by rfl⟩ : syracuseStep 771157 = 9037) (by norm_num)
theorem B541781 : Blo 358757 541781 := bbase (se 8 (by rfl) ⟨3174, by rfl⟩ : syracuseStep 541781 = 6349) (by norm_num)
theorem B541805 : Blo 358757 541805 := bbase (se 3 (by rfl) ⟨101588, by rfl⟩ : syracuseStep 541805 = 203177) (by norm_num)
theorem B541829 : Blo 358757 541829 := bbase (se 4 (by rfl) ⟨50796, by rfl⟩ : syracuseStep 541829 = 101593) (by norm_num)
theorem B541853 : Blo 358757 541853 := bbase (se 3 (by rfl) ⟨101597, by rfl⟩ : syracuseStep 541853 = 203195) (by norm_num)
theorem B607405 : Blo 358757 607405 := bbase (se 3 (by rfl) ⟨113888, by rfl⟩ : syracuseStep 607405 = 227777) (by norm_num)
theorem B541877 : Blo 358757 541877 := bbase (se 5 (by rfl) ⟨25400, by rfl⟩ : syracuseStep 541877 = 50801) (by norm_num)
theorem B771277 : Blo 358757 771277 := bbase (se 3 (by rfl) ⟨144614, by rfl⟩ : syracuseStep 771277 = 289229) (by norm_num)
theorem B541901 : Blo 358757 541901 := bbase (se 3 (by rfl) ⟨101606, by rfl⟩ : syracuseStep 541901 = 203213) (by norm_num)
theorem B541925 : Blo 358757 541925 := bbase (se 4 (by rfl) ⟨50805, by rfl⟩ : syracuseStep 541925 = 101611) (by norm_num)
theorem B541949 : Blo 358757 541949 := bbase (se 3 (by rfl) ⟨101615, by rfl⟩ : syracuseStep 541949 = 203231) (by norm_num)
theorem B869629 : Blo 358757 869629 := bbase (se 3 (by rfl) ⟨163055, by rfl⟩ : syracuseStep 869629 = 326111) (by norm_num)
theorem B1295621 : Blo 358757 1295621 := bbase (se 4 (by rfl) ⟨121464, by rfl⟩ : syracuseStep 1295621 = 242929) (by norm_num)
theorem B607493 : Blo 358757 607493 := bbase (se 4 (by rfl) ⟨56952, by rfl⟩ : syracuseStep 607493 = 113905) (by norm_num)
theorem B541973 : Blo 358757 541973 := bbase (se 6 (by rfl) ⟨12702, by rfl⟩ : syracuseStep 541973 = 25405) (by norm_num)
theorem B4179221 : Blo 358757 4179221 := bbase (se 6 (by rfl) ⟨97950, by rfl⟩ : syracuseStep 4179221 = 195901) (by norm_num)
theorem B541997 : Blo 358757 541997 := bbase (se 3 (by rfl) ⟨101624, by rfl⟩ : syracuseStep 541997 = 203249) (by norm_num)
theorem B542021 : Blo 358757 542021 := bbase (se 4 (by rfl) ⟨50814, by rfl⟩ : syracuseStep 542021 = 101629) (by norm_num)
theorem B542045 : Blo 358757 542045 := bbase (se 3 (by rfl) ⟨101633, by rfl⟩ : syracuseStep 542045 = 203267) (by norm_num)
theorem B542069 : Blo 358757 542069 := bbase (se 5 (by rfl) ⟨25409, by rfl⟩ : syracuseStep 542069 = 50819) (by norm_num)
theorem B607621 : Blo 358757 607621 := bbase (se 4 (by rfl) ⟨56964, by rfl⟩ : syracuseStep 607621 = 113929) (by norm_num)
theorem B542093 : Blo 358757 542093 := bbase (se 3 (by rfl) ⟨101642, by rfl⟩ : syracuseStep 542093 = 203285) (by norm_num)
theorem B1820069 : Blo 358757 1820069 := bbase (se 4 (by rfl) ⟨170631, by rfl⟩ : syracuseStep 1820069 = 341263) (by norm_num)
theorem B542117 : Blo 358757 542117 := bbase (se 4 (by rfl) ⟨50823, by rfl⟩ : syracuseStep 542117 = 101647) (by norm_num)
theorem B542141 : Blo 358757 542141 := bbase (se 3 (by rfl) ⟨101651, by rfl⟩ : syracuseStep 542141 = 203303) (by norm_num)
theorem B476609 : Blo 358757 476609 := bbase (se 2 (by rfl) ⟨178728, by rfl⟩ : syracuseStep 476609 = 357457) (by norm_num)
theorem B771533 : Blo 358757 771533 := bbase (se 3 (by rfl) ⟨144662, by rfl⟩ : syracuseStep 771533 = 289325) (by norm_num)
theorem B542165 : Blo 358757 542165 := bbase (se 7 (by rfl) ⟨6353, by rfl⟩ : syracuseStep 542165 = 12707) (by norm_num)
theorem B607709 : Blo 358757 607709 := bbase (se 3 (by rfl) ⟨113945, by rfl⟩ : syracuseStep 607709 = 227891) (by norm_num)
theorem B542189 : Blo 358757 542189 := bbase (se 3 (by rfl) ⟨101660, by rfl⟩ : syracuseStep 542189 = 203321) (by norm_num)
theorem B542213 : Blo 358757 542213 := bbase (se 4 (by rfl) ⟨50832, by rfl⟩ : syracuseStep 542213 = 101665) (by norm_num)
theorem B738829 : Blo 358757 738829 := bbase (se 3 (by rfl) ⟨138530, by rfl⟩ : syracuseStep 738829 = 277061) (by norm_num)
theorem B542237 : Blo 358757 542237 := bbase (se 3 (by rfl) ⟨101669, by rfl⟩ : syracuseStep 542237 = 203339) (by norm_num)
theorem B542261 : Blo 358757 542261 := bbase (se 5 (by rfl) ⟨25418, by rfl⟩ : syracuseStep 542261 = 50837) (by norm_num)
theorem B542285 : Blo 358757 542285 := bbase (se 3 (by rfl) ⟨101678, by rfl⟩ : syracuseStep 542285 = 203357) (by norm_num)
theorem B607837 : Blo 358757 607837 := bbase (se 3 (by rfl) ⟨113969, by rfl⟩ : syracuseStep 607837 = 227939) (by norm_num)
theorem B542309 : Blo 358757 542309 := bbase (se 4 (by rfl) ⟨50841, by rfl⟩ : syracuseStep 542309 = 101683) (by norm_num)
theorem B542333 : Blo 358757 542333 := bbase (se 3 (by rfl) ⟨101687, by rfl⟩ : syracuseStep 542333 = 203375) (by norm_num)
theorem B542357 : Blo 358757 542357 := bbase (se 6 (by rfl) ⟨12711, by rfl⟩ : syracuseStep 542357 = 25423) (by norm_num)
theorem B542381 : Blo 358757 542381 := bbase (se 3 (by rfl) ⟨101696, by rfl⟩ : syracuseStep 542381 = 203393) (by norm_num)
theorem B607925 : Blo 358757 607925 := bbase (se 5 (by rfl) ⟨28496, by rfl⟩ : syracuseStep 607925 = 56993) (by norm_num)
theorem B542405 : Blo 358757 542405 := bbase (se 4 (by rfl) ⟨50850, by rfl⟩ : syracuseStep 542405 = 101701) (by norm_num)
theorem B4703957 : Blo 358757 4703957 := bbase (se 7 (by rfl) ⟨55124, by rfl⟩ : syracuseStep 4703957 = 110249) (by norm_num)
theorem B542429 : Blo 358757 542429 := bbase (se 3 (by rfl) ⟨101705, by rfl⟩ : syracuseStep 542429 = 203411) (by norm_num)
theorem B411361 : Blo 358757 411361 := bbase (se 2 (by rfl) ⟨154260, by rfl⟩ : syracuseStep 411361 = 308521) (by norm_num)
theorem B542453 : Blo 358757 542453 := bbase (se 5 (by rfl) ⟨25427, by rfl⟩ : syracuseStep 542453 = 50855) (by norm_num)
theorem B542477 : Blo 358757 542477 := bbase (se 3 (by rfl) ⟨101714, by rfl⟩ : syracuseStep 542477 = 203429) (by norm_num)
theorem B542501 : Blo 358757 542501 := bbase (se 4 (by rfl) ⟨50859, by rfl⟩ : syracuseStep 542501 = 101719) (by norm_num)
theorem B608053 : Blo 358757 608053 := bbase (se 5 (by rfl) ⟨28502, by rfl⟩ : syracuseStep 608053 = 57005) (by norm_num)
theorem B542525 : Blo 358757 542525 := bbase (se 3 (by rfl) ⟨101723, by rfl⟩ : syracuseStep 542525 = 203447) (by norm_num)
theorem B542549 : Blo 358757 542549 := bbase (se 9 (by rfl) ⟨1589, by rfl⟩ : syracuseStep 542549 = 3179) (by norm_num)
theorem B542573 : Blo 358757 542573 := bbase (se 3 (by rfl) ⟨101732, by rfl⟩ : syracuseStep 542573 = 203465) (by norm_num)
theorem B542597 : Blo 358757 542597 := bbase (se 4 (by rfl) ⟨50868, by rfl⟩ : syracuseStep 542597 = 101737) (by norm_num)
theorem B608141 : Blo 358757 608141 := bbase (se 3 (by rfl) ⟨114026, by rfl⟩ : syracuseStep 608141 = 228053) (by norm_num)
theorem B542621 : Blo 358757 542621 := bbase (se 3 (by rfl) ⟨101741, by rfl⟩ : syracuseStep 542621 = 203483) (by norm_num)
theorem B870301 : Blo 358757 870301 := bbase (se 3 (by rfl) ⟨163181, by rfl⟩ : syracuseStep 870301 = 326363) (by norm_num)
theorem B542645 : Blo 358757 542645 := bbase (se 5 (by rfl) ⟨25436, by rfl⟩ : syracuseStep 542645 = 50873) (by norm_num)
theorem B542669 : Blo 358757 542669 := bbase (se 3 (by rfl) ⟨101750, by rfl⟩ : syracuseStep 542669 = 203501) (by norm_num)
theorem B542693 : Blo 358757 542693 := bbase (se 4 (by rfl) ⟨50877, by rfl⟩ : syracuseStep 542693 = 101755) (by norm_num)
theorem B542717 : Blo 358757 542717 := bbase (se 3 (by rfl) ⟨101759, by rfl⟩ : syracuseStep 542717 = 203519) (by norm_num)
theorem B608269 : Blo 358757 608269 := bbase (se 3 (by rfl) ⟨114050, by rfl⟩ : syracuseStep 608269 = 228101) (by norm_num)
theorem B542741 : Blo 358757 542741 := bbase (se 6 (by rfl) ⟨12720, by rfl⟩ : syracuseStep 542741 = 25441) (by norm_num)
theorem B4769813 : Blo 358757 4769813 := bbase (se 6 (by rfl) ⟨111792, by rfl⟩ : syracuseStep 4769813 = 223585) (by norm_num)
theorem B542765 : Blo 358757 542765 := bbase (se 3 (by rfl) ⟨101768, by rfl⟩ : syracuseStep 542765 = 203537) (by norm_num)
theorem B542789 : Blo 358757 542789 := bbase (se 4 (by rfl) ⟨50886, by rfl⟩ : syracuseStep 542789 = 101773) (by norm_num)
theorem B542813 : Blo 358757 542813 := bbase (se 3 (by rfl) ⟨101777, by rfl⟩ : syracuseStep 542813 = 203555) (by norm_num)
theorem B608357 : Blo 358757 608357 := bbase (se 4 (by rfl) ⟨57033, by rfl⟩ : syracuseStep 608357 = 114067) (by norm_num)
theorem B542837 : Blo 358757 542837 := bbase (se 5 (by rfl) ⟨25445, by rfl⟩ : syracuseStep 542837 = 50891) (by norm_num)
theorem B870533 : Blo 358757 870533 := bbase (se 4 (by rfl) ⟨81612, by rfl⟩ : syracuseStep 870533 = 163225) (by norm_num)
theorem B542861 : Blo 358757 542861 := bbase (se 3 (by rfl) ⟨101786, by rfl⟩ : syracuseStep 542861 = 203573) (by norm_num)
theorem B542885 : Blo 358757 542885 := bbase (se 4 (by rfl) ⟨50895, by rfl⟩ : syracuseStep 542885 = 101791) (by norm_num)
theorem B870581 : Blo 358757 870581 := bbase (se 5 (by rfl) ⟨40808, by rfl⟩ : syracuseStep 870581 = 81617) (by norm_num)
theorem B575677 : Blo 358757 575677 := bbase (se 3 (by rfl) ⟨107939, by rfl⟩ : syracuseStep 575677 = 215879) (by norm_num)
theorem B542909 : Blo 358757 542909 := bbase (se 3 (by rfl) ⟨101795, by rfl⟩ : syracuseStep 542909 = 203591) (by norm_num)
theorem B542933 : Blo 358757 542933 := bbase (se 7 (by rfl) ⟨6362, by rfl⟩ : syracuseStep 542933 = 12725) (by norm_num)
theorem B608485 : Blo 358757 608485 := bbase (se 4 (by rfl) ⟨57045, by rfl⟩ : syracuseStep 608485 = 114091) (by norm_num)
theorem B542957 : Blo 358757 542957 := bbase (se 3 (by rfl) ⟨101804, by rfl⟩ : syracuseStep 542957 = 203609) (by norm_num)
theorem B542981 : Blo 358757 542981 := bbase (se 4 (by rfl) ⟨50904, by rfl⟩ : syracuseStep 542981 = 101809) (by norm_num)
theorem B411913 : Blo 358757 411913 := bbase (se 2 (by rfl) ⟨154467, by rfl⟩ : syracuseStep 411913 = 308935) (by norm_num)
theorem B1362197 : Blo 358757 1362197 := bbase (se 6 (by rfl) ⟨31926, by rfl⟩ : syracuseStep 1362197 = 63853) (by norm_num)
theorem B543005 : Blo 358757 543005 := bbase (se 3 (by rfl) ⟨101813, by rfl⟩ : syracuseStep 543005 = 203627) (by norm_num)
theorem B543029 : Blo 358757 543029 := bbase (se 5 (by rfl) ⟨25454, by rfl⟩ : syracuseStep 543029 = 50909) (by norm_num)
theorem B608573 : Blo 358757 608573 := bbase (se 3 (by rfl) ⟨114107, by rfl⟩ : syracuseStep 608573 = 228215) (by norm_num)
theorem B772421 : Blo 358757 772421 := bbase (se 4 (by rfl) ⟨72414, by rfl⟩ : syracuseStep 772421 = 144829) (by norm_num)
theorem B543053 : Blo 358757 543053 := bbase (se 3 (by rfl) ⟨101822, by rfl⟩ : syracuseStep 543053 = 203645) (by norm_num)
theorem B543077 : Blo 358757 543077 := bbase (se 4 (by rfl) ⟨50913, by rfl⟩ : syracuseStep 543077 = 101827) (by norm_num)
theorem B543101 : Blo 358757 543101 := bbase (se 3 (by rfl) ⟨101831, by rfl⟩ : syracuseStep 543101 = 203663) (by norm_num)
theorem B1296773 : Blo 358757 1296773 := bbase (se 4 (by rfl) ⟨121572, by rfl⟩ : syracuseStep 1296773 = 243145) (by norm_num)
theorem B543125 : Blo 358757 543125 := bbase (se 6 (by rfl) ⟨12729, by rfl⟩ : syracuseStep 543125 = 25459) (by norm_num)
theorem B543149 : Blo 358757 543149 := bbase (se 3 (by rfl) ⟨101840, by rfl⟩ : syracuseStep 543149 = 203681) (by norm_num)
theorem B2574773 : Blo 358757 2574773 := bbase (se 5 (by rfl) ⟨120692, by rfl⟩ : syracuseStep 2574773 = 241385) (by norm_num)
theorem B1100213 : Blo 358757 1100213 := bbase (se 5 (by rfl) ⟨51572, by rfl⟩ : syracuseStep 1100213 = 103145) (by norm_num)
theorem B608701 : Blo 358757 608701 := bbase (se 3 (by rfl) ⟨114131, by rfl⟩ : syracuseStep 608701 = 228263) (by norm_num)
theorem B543173 : Blo 358757 543173 := bbase (se 4 (by rfl) ⟨50922, by rfl⟩ : syracuseStep 543173 = 101845) (by norm_num)
theorem B1558997 : Blo 358757 1558997 := bbase (se 7 (by rfl) ⟨18269, by rfl⟩ : syracuseStep 1558997 = 36539) (by norm_num)
theorem B543197 : Blo 358757 543197 := bbase (se 3 (by rfl) ⟨101849, by rfl⟩ : syracuseStep 543197 = 203699) (by norm_num)
theorem B543221 : Blo 358757 543221 := bbase (se 5 (by rfl) ⟨25463, by rfl⟩ : syracuseStep 543221 = 50927) (by norm_num)
theorem B543245 : Blo 358757 543245 := bbase (se 3 (by rfl) ⟨101858, by rfl⟩ : syracuseStep 543245 = 203717) (by norm_num)
theorem B608789 : Blo 358757 608789 := bbase (se 6 (by rfl) ⟨14268, by rfl⟩ : syracuseStep 608789 = 28537) (by norm_num)
theorem B543269 : Blo 358757 543269 := bbase (se 4 (by rfl) ⟨50931, by rfl⟩ : syracuseStep 543269 = 101863) (by norm_num)
theorem B772661 : Blo 358757 772661 := bbase (se 5 (by rfl) ⟨36218, by rfl⟩ : syracuseStep 772661 = 72437) (by norm_num)
theorem B543293 : Blo 358757 543293 := bbase (se 3 (by rfl) ⟨101867, by rfl⟩ : syracuseStep 543293 = 203735) (by norm_num)
theorem B412237 : Blo 358757 412237 := bbase (se 3 (by rfl) ⟨77294, by rfl⟩ : syracuseStep 412237 = 154589) (by norm_num)
theorem B412241 : Blo 358757 412241 := bbase (se 2 (by rfl) ⟨154590, by rfl⟩ : syracuseStep 412241 = 309181) (by norm_num)
theorem B543317 : Blo 358757 543317 := bbase (se 8 (by rfl) ⟨3183, by rfl⟩ : syracuseStep 543317 = 6367) (by norm_num)
theorem B543341 : Blo 358757 543341 := bbase (se 3 (by rfl) ⟨101876, by rfl⟩ : syracuseStep 543341 = 203753) (by norm_num)
theorem B543365 : Blo 358757 543365 := bbase (se 4 (by rfl) ⟨50940, by rfl⟩ : syracuseStep 543365 = 101881) (by norm_num)
theorem B608917 : Blo 358757 608917 := bbase (se 6 (by rfl) ⟨14271, by rfl⟩ : syracuseStep 608917 = 28543) (by norm_num)
theorem B543389 : Blo 358757 543389 := bbase (se 3 (by rfl) ⟨101885, by rfl⟩ : syracuseStep 543389 = 203771) (by norm_num)
theorem B1821365 : Blo 358757 1821365 := bbase (se 5 (by rfl) ⟨85376, by rfl⟩ : syracuseStep 1821365 = 170753) (by norm_num)
theorem B543413 : Blo 358757 543413 := bbase (se 5 (by rfl) ⟨25472, by rfl⟩ : syracuseStep 543413 = 50945) (by norm_num)
theorem B543437 : Blo 358757 543437 := bbase (se 3 (by rfl) ⟨101894, by rfl⟩ : syracuseStep 543437 = 203789) (by norm_num)
theorem B543461 : Blo 358757 543461 := bbase (se 4 (by rfl) ⟨50949, by rfl⟩ : syracuseStep 543461 = 101899) (by norm_num)
theorem B609005 : Blo 358757 609005 := bbase (se 3 (by rfl) ⟨114188, by rfl⟩ : syracuseStep 609005 = 228377) (by norm_num)
theorem B543485 : Blo 358757 543485 := bbase (se 3 (by rfl) ⟨101903, by rfl⟩ : syracuseStep 543485 = 203807) (by norm_num)
theorem B543509 : Blo 358757 543509 := bbase (se 6 (by rfl) ⟨12738, by rfl⟩ : syracuseStep 543509 = 25477) (by norm_num)
theorem B543533 : Blo 358757 543533 := bbase (se 3 (by rfl) ⟨101912, by rfl⟩ : syracuseStep 543533 = 203825) (by norm_num)
theorem B543557 : Blo 358757 543557 := bbase (se 4 (by rfl) ⟨50958, by rfl⟩ : syracuseStep 543557 = 101917) (by norm_num)
theorem B1461077 : Blo 358757 1461077 := bbase (se 9 (by rfl) ⟨4280, by rfl⟩ : syracuseStep 1461077 = 8561) (by norm_num)
theorem B543581 : Blo 358757 543581 := bbase (se 3 (by rfl) ⟨101921, by rfl⟩ : syracuseStep 543581 = 203843) (by norm_num)
theorem B609133 : Blo 358757 609133 := bbase (se 3 (by rfl) ⟨114212, by rfl⟩ : syracuseStep 609133 = 228425) (by norm_num)
theorem B543605 : Blo 358757 543605 := bbase (se 5 (by rfl) ⟨25481, by rfl⟩ : syracuseStep 543605 = 50963) (by norm_num)
theorem B576389 : Blo 358757 576389 := bbase (se 4 (by rfl) ⟨54036, by rfl⟩ : syracuseStep 576389 = 108073) (by norm_num)
theorem B543629 : Blo 358757 543629 := bbase (se 3 (by rfl) ⟨101930, by rfl⟩ : syracuseStep 543629 = 203861) (by norm_num)
theorem B543653 : Blo 358757 543653 := bbase (se 4 (by rfl) ⟨50967, by rfl⟩ : syracuseStep 543653 = 101935) (by norm_num)
theorem B543677 : Blo 358757 543677 := bbase (se 3 (by rfl) ⟨101939, by rfl⟩ : syracuseStep 543677 = 203879) (by norm_num)
theorem B609221 : Blo 358757 609221 := bbase (se 4 (by rfl) ⟨57114, by rfl⟩ : syracuseStep 609221 = 114229) (by norm_num)
theorem B543701 : Blo 358757 543701 := bbase (se 7 (by rfl) ⟨6371, by rfl⟩ : syracuseStep 543701 = 12743) (by norm_num)
theorem B543725 : Blo 358757 543725 := bbase (se 3 (by rfl) ⟨101948, by rfl⟩ : syracuseStep 543725 = 203897) (by norm_num)
theorem B543749 : Blo 358757 543749 := bbase (se 4 (by rfl) ⟨50976, by rfl⟩ : syracuseStep 543749 = 101953) (by norm_num)
theorem B543773 : Blo 358757 543773 := bbase (se 3 (by rfl) ⟨101957, by rfl⟩ : syracuseStep 543773 = 203915) (by norm_num)
theorem B773165 : Blo 358757 773165 := bbase (se 3 (by rfl) ⟨144968, by rfl⟩ : syracuseStep 773165 = 289937) (by norm_num)
theorem B773173 : Blo 358757 773173 := bbase (se 5 (by rfl) ⟨36242, by rfl⟩ : syracuseStep 773173 = 72485) (by norm_num)
theorem B543797 : Blo 358757 543797 := bbase (se 5 (by rfl) ⟨25490, by rfl⟩ : syracuseStep 543797 = 50981) (by norm_num)
theorem B609349 : Blo 358757 609349 := bbase (se 4 (by rfl) ⟨57126, by rfl⟩ : syracuseStep 609349 = 114253) (by norm_num)
theorem B543821 : Blo 358757 543821 := bbase (se 3 (by rfl) ⟨101966, by rfl⟩ : syracuseStep 543821 = 203933) (by norm_num)
theorem B543845 : Blo 358757 543845 := bbase (se 4 (by rfl) ⟨50985, by rfl⟩ : syracuseStep 543845 = 101971) (by norm_num)
theorem B1559669 : Blo 358757 1559669 := bbase (se 5 (by rfl) ⟨73109, by rfl⟩ : syracuseStep 1559669 = 146219) (by norm_num)
theorem B412789 : Blo 358757 412789 := bbase (se 5 (by rfl) ⟨19349, by rfl⟩ : syracuseStep 412789 = 38699) (by norm_num)
theorem B543869 : Blo 358757 543869 := bbase (se 3 (by rfl) ⟨101975, by rfl⟩ : syracuseStep 543869 = 203951) (by norm_num)
theorem B543893 : Blo 358757 543893 := bbase (se 6 (by rfl) ⟨12747, by rfl⟩ : syracuseStep 543893 = 25495) (by norm_num)
theorem B609437 : Blo 358757 609437 := bbase (se 3 (by rfl) ⟨114269, by rfl⟩ : syracuseStep 609437 = 228539) (by norm_num)
theorem B543917 : Blo 358757 543917 := bbase (se 3 (by rfl) ⟨101984, by rfl⟩ : syracuseStep 543917 = 203969) (by norm_num)
theorem B543941 : Blo 358757 543941 := bbase (se 4 (by rfl) ⟨50994, by rfl⟩ : syracuseStep 543941 = 101989) (by norm_num)
theorem B543965 : Blo 358757 543965 := bbase (se 3 (by rfl) ⟨101993, by rfl⟩ : syracuseStep 543965 = 203987) (by norm_num)
theorem B543989 : Blo 358757 543989 := bbase (se 5 (by rfl) ⟨25499, by rfl⟩ : syracuseStep 543989 = 50999) (by norm_num)
theorem B544013 : Blo 358757 544013 := bbase (se 3 (by rfl) ⟨102002, by rfl⟩ : syracuseStep 544013 = 204005) (by norm_num)
theorem B642325 : Blo 358757 642325 := bbase (se 6 (by rfl) ⟨15054, by rfl⟩ : syracuseStep 642325 = 30109) (by norm_num)
theorem B609565 : Blo 358757 609565 := bbase (se 3 (by rfl) ⟨114293, by rfl⟩ : syracuseStep 609565 = 228587) (by norm_num)
theorem B544037 : Blo 358757 544037 := bbase (se 4 (by rfl) ⟨51003, by rfl⟩ : syracuseStep 544037 = 102007) (by norm_num)
theorem B544061 : Blo 358757 544061 := bbase (se 3 (by rfl) ⟨102011, by rfl⟩ : syracuseStep 544061 = 204023) (by norm_num)
theorem B544085 : Blo 358757 544085 := bbase (se 11 (by rfl) ⟨398, by rfl⟩ : syracuseStep 544085 = 797) (by norm_num)
theorem B544109 : Blo 358757 544109 := bbase (se 3 (by rfl) ⟨102020, by rfl⟩ : syracuseStep 544109 = 204041) (by norm_num)
theorem B609653 : Blo 358757 609653 := bbase (se 5 (by rfl) ⟨28577, by rfl⟩ : syracuseStep 609653 = 57155) (by norm_num)
theorem B544133 : Blo 358757 544133 := bbase (se 4 (by rfl) ⟨51012, by rfl⟩ : syracuseStep 544133 = 102025) (by norm_num)
theorem B609781 : Blo 358757 609781 := bbase (se 5 (by rfl) ⟨28583, by rfl⟩ : syracuseStep 609781 = 57167) (by norm_num)
theorem B511525 : Blo 358757 511525 := bbase (se 4 (by rfl) ⟨47955, by rfl⟩ : syracuseStep 511525 = 95911) (by norm_num)
theorem B577061 : Blo 358757 577061 := bbase (se 4 (by rfl) ⟨54099, by rfl⟩ : syracuseStep 577061 = 108199) (by norm_num)
theorem B609869 : Blo 358757 609869 := bbase (se 3 (by rfl) ⟨114350, by rfl⟩ : syracuseStep 609869 = 228701) (by norm_num)
theorem B413273 : Blo 358757 413273 := bbase (se 2 (by rfl) ⟨154977, by rfl⟩ : syracuseStep 413273 = 309955) (by norm_num)
theorem B3067541 : Blo 358757 3067541 := bbase (se 6 (by rfl) ⟨71895, by rfl⟩ : syracuseStep 3067541 = 143791) (by norm_num)
theorem B609997 : Blo 358757 609997 := bbase (se 3 (by rfl) ⟨114374, by rfl⟩ : syracuseStep 609997 = 228749) (by norm_num)
theorem B610085 : Blo 358757 610085 := bbase (se 4 (by rfl) ⟨57195, by rfl⟩ : syracuseStep 610085 = 114391) (by norm_num)
theorem B970613 : Blo 358757 970613 := bbase (se 5 (by rfl) ⟨45497, by rfl⟩ : syracuseStep 970613 = 90995) (by norm_num)
theorem B511861 : Blo 358757 511861 := bbase (se 5 (by rfl) ⟨23993, by rfl⟩ : syracuseStep 511861 = 47987) (by norm_num)
theorem B610213 : Blo 358757 610213 := bbase (se 4 (by rfl) ⟨57207, by rfl⟩ : syracuseStep 610213 = 114415) (by norm_num)
theorem B1822661 : Blo 358757 1822661 := bbase (se 4 (by rfl) ⟨170874, by rfl⟩ : syracuseStep 1822661 = 341749) (by norm_num)
theorem B610301 : Blo 358757 610301 := bbase (se 3 (by rfl) ⟨114431, by rfl⟩ : syracuseStep 610301 = 228863) (by norm_num)
theorem B577573 : Blo 358757 577573 := bbase (se 4 (by rfl) ⟨54147, by rfl⟩ : syracuseStep 577573 = 108295) (by norm_num)
theorem B512077 : Blo 358757 512077 := bbase (se 3 (by rfl) ⟨96014, by rfl⟩ : syracuseStep 512077 = 192029) (by norm_num)
theorem B610429 : Blo 358757 610429 := bbase (se 3 (by rfl) ⟨114455, by rfl⟩ : syracuseStep 610429 = 228911) (by norm_num)
theorem B774301 : Blo 358757 774301 := bbase (se 3 (by rfl) ⟨145181, by rfl⟩ : syracuseStep 774301 = 290363) (by norm_num)
theorem B610517 : Blo 358757 610517 := bbase (se 7 (by rfl) ⟨7154, by rfl⟩ : syracuseStep 610517 = 14309) (by norm_num)
theorem B807245 : Blo 358757 807245 := bbase (se 3 (by rfl) ⟨151358, by rfl⟩ : syracuseStep 807245 = 302717) (by norm_num)
theorem B1364309 : Blo 358757 1364309 := bbase (se 10 (by rfl) ⟨1998, by rfl⟩ : syracuseStep 1364309 = 3997) (by norm_num)
theorem B610645 : Blo 358757 610645 := bbase (se 10 (by rfl) ⟨894, by rfl⟩ : syracuseStep 610645 = 1789) (by norm_num)
theorem B807317 : Blo 358757 807317 := bbase (se 6 (by rfl) ⟨18921, by rfl⟩ : syracuseStep 807317 = 37843) (by norm_num)
theorem B610733 : Blo 358757 610733 := bbase (se 3 (by rfl) ⟨114512, by rfl⟩ : syracuseStep 610733 = 229025) (by norm_num)
theorem B512453 : Blo 358757 512453 := bbase (se 4 (by rfl) ⟨48042, by rfl⟩ : syracuseStep 512453 = 96085) (by norm_num)
theorem B807389 : Blo 358757 807389 := bbase (se 3 (by rfl) ⟨151385, by rfl⟩ : syracuseStep 807389 = 302771) (by norm_num)
theorem B578029 : Blo 358757 578029 := bbase (se 3 (by rfl) ⟨108380, by rfl⟩ : syracuseStep 578029 = 216761) (by norm_num)
theorem B1102325 : Blo 358757 1102325 := bbase (se 5 (by rfl) ⟨51671, by rfl⟩ : syracuseStep 1102325 = 103343) (by norm_num)
theorem B2347541 : Blo 358757 2347541 := bbase (se 6 (by rfl) ⟨55020, by rfl⟩ : syracuseStep 2347541 = 110041) (by norm_num)
theorem B774677 : Blo 358757 774677 := bbase (se 6 (by rfl) ⟨18156, by rfl⟩ : syracuseStep 774677 = 36313) (by norm_num)
theorem B807461 : Blo 358757 807461 := bbase (se 4 (by rfl) ⟨75699, by rfl⟩ : syracuseStep 807461 = 151399) (by norm_num)
theorem B610861 : Blo 358757 610861 := bbase (se 3 (by rfl) ⟨114536, by rfl⟩ : syracuseStep 610861 = 229073) (by norm_num)
theorem B1561141 : Blo 358757 1561141 := bbase (se 5 (by rfl) ⟨73178, by rfl⟩ : syracuseStep 1561141 = 146357) (by norm_num)
theorem B807533 : Blo 358757 807533 := bbase (se 3 (by rfl) ⟨151412, by rfl⟩ : syracuseStep 807533 = 302825) (by norm_num)
theorem B1364597 : Blo 358757 1364597 := bbase (se 5 (by rfl) ⟨63965, by rfl⟩ : syracuseStep 1364597 = 127931) (by norm_num)
theorem B610949 : Blo 358757 610949 := bbase (se 4 (by rfl) ⟨57276, by rfl⟩ : syracuseStep 610949 = 114553) (by norm_num)
theorem B807605 : Blo 358757 807605 := bbase (se 5 (by rfl) ⟨37856, by rfl⟩ : syracuseStep 807605 = 75713) (by norm_num)
theorem B742085 : Blo 358757 742085 := bbase (se 4 (by rfl) ⟨69570, by rfl⟩ : syracuseStep 742085 = 139141) (by norm_num)
theorem B1037045 : Blo 358757 1037045 := bbase (se 5 (by rfl) ⟨48611, by rfl⟩ : syracuseStep 1037045 = 97223) (by norm_num)
theorem B807677 : Blo 358757 807677 := bbase (se 3 (by rfl) ⟨151439, by rfl⟩ : syracuseStep 807677 = 302879) (by norm_num)
theorem B611077 : Blo 358757 611077 := bbase (se 4 (by rfl) ⟨57288, by rfl⟩ : syracuseStep 611077 = 114577) (by norm_num)
theorem B1299253 : Blo 358757 1299253 := bbase (se 5 (by rfl) ⟨60902, by rfl⟩ : syracuseStep 1299253 = 121805) (by norm_num)
theorem B807749 : Blo 358757 807749 := bbase (se 4 (by rfl) ⟨75726, by rfl⟩ : syracuseStep 807749 = 151453) (by norm_num)
theorem B611165 : Blo 358757 611165 := bbase (se 3 (by rfl) ⟨114593, by rfl⟩ : syracuseStep 611165 = 229187) (by norm_num)
theorem B709517 : Blo 358757 709517 := bbase (se 3 (by rfl) ⟨133034, by rfl⟩ : syracuseStep 709517 = 266069) (by norm_num)
theorem B807821 : Blo 358757 807821 := bbase (se 3 (by rfl) ⟨151466, by rfl⟩ : syracuseStep 807821 = 302933) (by norm_num)
theorem B5198741 : Blo 358757 5198741 := bbase (se 6 (by rfl) ⟨121845, by rfl⟩ : syracuseStep 5198741 = 243691) (by norm_num)
theorem B807893 : Blo 358757 807893 := bbase (se 7 (by rfl) ⟨9467, by rfl⟩ : syracuseStep 807893 = 18935) (by norm_num)
theorem B611293 : Blo 358757 611293 := bbase (se 3 (by rfl) ⟨114617, by rfl⟩ : syracuseStep 611293 = 229235) (by norm_num)
theorem B807965 : Blo 358757 807965 := bbase (se 3 (by rfl) ⟨151493, by rfl⟩ : syracuseStep 807965 = 302987) (by norm_num)
theorem B611381 : Blo 358757 611381 := bbase (se 5 (by rfl) ⟨28658, by rfl⟩ : syracuseStep 611381 = 57317) (by norm_num)
theorem B808037 : Blo 358757 808037 := bbase (se 4 (by rfl) ⟨75753, by rfl⟩ : syracuseStep 808037 = 151507) (by norm_num)
theorem B578701 : Blo 358757 578701 := bbase (se 3 (by rfl) ⟨108506, by rfl⟩ : syracuseStep 578701 = 217013) (by norm_num)
theorem B808109 : Blo 358757 808109 := bbase (se 3 (by rfl) ⟨151520, by rfl⟩ : syracuseStep 808109 = 303041) (by norm_num)
theorem B611509 : Blo 358757 611509 := bbase (se 5 (by rfl) ⟨28664, by rfl⟩ : syracuseStep 611509 = 57329) (by norm_num)
theorem B1823957 : Blo 358757 1823957 := bbase (se 7 (by rfl) ⟨21374, by rfl⟩ : syracuseStep 1823957 = 42749) (by norm_num)
theorem B808181 : Blo 358757 808181 := bbase (se 5 (by rfl) ⟨37883, by rfl⟩ : syracuseStep 808181 = 75767) (by norm_num)
theorem B611597 : Blo 358757 611597 := bbase (se 3 (by rfl) ⟨114674, by rfl⟩ : syracuseStep 611597 = 229349) (by norm_num)
theorem B2741525 : Blo 358757 2741525 := bbase (se 6 (by rfl) ⟨64254, by rfl⟩ : syracuseStep 2741525 = 128509) (by norm_num)
theorem B808253 : Blo 358757 808253 := bbase (se 3 (by rfl) ⟨151547, by rfl⟩ : syracuseStep 808253 = 303095) (by norm_num)
theorem B808325 : Blo 358757 808325 := bbase (se 4 (by rfl) ⟨75780, by rfl⟩ : syracuseStep 808325 = 151561) (by norm_num)
theorem B611725 : Blo 358757 611725 := bbase (se 3 (by rfl) ⟨114698, by rfl⟩ : syracuseStep 611725 = 229397) (by norm_num)
theorem B1725877 : Blo 358757 1725877 := bbase (se 5 (by rfl) ⟨80900, by rfl⟩ : syracuseStep 1725877 = 161801) (by norm_num)
theorem B808397 : Blo 358757 808397 := bbase (se 3 (by rfl) ⟨151574, by rfl⟩ : syracuseStep 808397 = 303149) (by norm_num)
theorem B611813 : Blo 358757 611813 := bbase (se 4 (by rfl) ⟨57357, by rfl⟩ : syracuseStep 611813 = 114715) (by norm_num)
theorem B808469 : Blo 358757 808469 := bbase (se 6 (by rfl) ⟨18948, by rfl⟩ : syracuseStep 808469 = 37897) (by norm_num)
theorem B1299989 : Blo 358757 1299989 := bbase (se 6 (by rfl) ⟨30468, by rfl⟩ : syracuseStep 1299989 = 60937) (by norm_num)
theorem B579125 : Blo 358757 579125 := bbase (se 5 (by rfl) ⟨27146, by rfl⟩ : syracuseStep 579125 = 54293) (by norm_num)
theorem B808541 : Blo 358757 808541 := bbase (se 3 (by rfl) ⟨151601, by rfl⟩ : syracuseStep 808541 = 303203) (by norm_num)
theorem B611941 : Blo 358757 611941 := bbase (se 4 (by rfl) ⟨57369, by rfl⟩ : syracuseStep 611941 = 114739) (by norm_num)
theorem B808613 : Blo 358757 808613 := bbase (se 4 (by rfl) ⟨75807, by rfl⟩ : syracuseStep 808613 = 151615) (by norm_num)
theorem B612029 : Blo 358757 612029 := bbase (se 3 (by rfl) ⟨114755, by rfl⟩ : syracuseStep 612029 = 229511) (by norm_num)
theorem B1038037 : Blo 358757 1038037 := bbase (se 7 (by rfl) ⟨12164, by rfl⟩ : syracuseStep 1038037 = 24329) (by norm_num)
theorem B808685 : Blo 358757 808685 := bbase (se 3 (by rfl) ⟨151628, by rfl⟩ : syracuseStep 808685 = 303257) (by norm_num)
theorem B1365781 : Blo 358757 1365781 := bbase (se 6 (by rfl) ⟨32010, by rfl⟩ : syracuseStep 1365781 = 64021) (by norm_num)
theorem B808757 : Blo 358757 808757 := bbase (se 5 (by rfl) ⟨37910, by rfl⟩ : syracuseStep 808757 = 75821) (by norm_num)
theorem B513877 : Blo 358757 513877 := bbase (se 9 (by rfl) ⟨1505, by rfl⟩ : syracuseStep 513877 = 3011) (by norm_num)
theorem B579413 : Blo 358757 579413 := bbase (se 9 (by rfl) ⟨1697, by rfl⟩ : syracuseStep 579413 = 3395) (by norm_num)
theorem B808829 : Blo 358757 808829 := bbase (se 3 (by rfl) ⟨151655, by rfl⟩ : syracuseStep 808829 = 303311) (by norm_num)
theorem B808901 : Blo 358757 808901 := bbase (se 4 (by rfl) ⟨75834, by rfl⟩ : syracuseStep 808901 = 151669) (by norm_num)
theorem B808973 : Blo 358757 808973 := bbase (se 3 (by rfl) ⟨151682, by rfl⟩ : syracuseStep 808973 = 303365) (by norm_num)
theorem B1366085 : Blo 358757 1366085 := bbase (se 4 (by rfl) ⟨128070, by rfl⟩ : syracuseStep 1366085 = 256141) (by norm_num)
theorem B809045 : Blo 358757 809045 := bbase (se 8 (by rfl) ⟨4740, by rfl⟩ : syracuseStep 809045 = 9481) (by norm_num)
theorem B2480213 : Blo 358757 2480213 := bbase (se 8 (by rfl) ⟨14532, by rfl⟩ : syracuseStep 2480213 = 29065) (by norm_num)
theorem B546925 : Blo 358757 546925 := bbase (se 3 (by rfl) ⟨102548, by rfl⟩ : syracuseStep 546925 = 205097) (by norm_num)
theorem B809117 : Blo 358757 809117 := bbase (se 3 (by rfl) ⟨151709, by rfl⟩ : syracuseStep 809117 = 303419) (by norm_num)
theorem B1300693 : Blo 358757 1300693 := bbase (se 7 (by rfl) ⟨15242, by rfl⟩ : syracuseStep 1300693 = 30485) (by norm_num)
theorem B809189 : Blo 358757 809189 := bbase (se 4 (by rfl) ⟨75861, by rfl⟩ : syracuseStep 809189 = 151723) (by norm_num)
theorem B383221 : Blo 358757 383221 := bbase (se 5 (by rfl) ⟨17963, by rfl⟩ : syracuseStep 383221 = 35927) (by norm_num)
theorem B809261 : Blo 358757 809261 := bbase (se 3 (by rfl) ⟨151736, by rfl⟩ : syracuseStep 809261 = 303473) (by norm_num)
theorem B809333 : Blo 358757 809333 := bbase (se 5 (by rfl) ⟨37937, by rfl⟩ : syracuseStep 809333 = 75875) (by norm_num)
theorem B514469 : Blo 358757 514469 := bbase (se 4 (by rfl) ⟨48231, by rfl⟩ : syracuseStep 514469 = 96463) (by norm_num)
theorem B809405 : Blo 358757 809405 := bbase (se 3 (by rfl) ⟨151763, by rfl⟩ : syracuseStep 809405 = 303527) (by norm_num)
theorem B1825253 : Blo 358757 1825253 := bbase (se 4 (by rfl) ⟨171117, by rfl⟩ : syracuseStep 1825253 = 342235) (by norm_num)
theorem B514549 : Blo 358757 514549 := bbase (se 5 (by rfl) ⟨24119, by rfl⟩ : syracuseStep 514549 = 48239) (by norm_num)
theorem B809477 : Blo 358757 809477 := bbase (se 4 (by rfl) ⟨75888, by rfl⟩ : syracuseStep 809477 = 151777) (by norm_num)
theorem B973349 : Blo 358757 973349 := bbase (se 4 (by rfl) ⟨91251, by rfl⟩ : syracuseStep 973349 = 182503) (by norm_num)
theorem B1858085 : Blo 358757 1858085 := bbase (se 4 (by rfl) ⟨174195, by rfl⟩ : syracuseStep 1858085 = 348391) (by norm_num)
theorem B2316853 : Blo 358757 2316853 := bbase (se 5 (by rfl) ⟨108602, by rfl⟩ : syracuseStep 2316853 = 217205) (by norm_num)
theorem B809549 : Blo 358757 809549 := bbase (se 3 (by rfl) ⟨151790, by rfl⟩ : syracuseStep 809549 = 303581) (by norm_num)
theorem B514669 : Blo 358757 514669 := bbase (se 3 (by rfl) ⟨96500, by rfl⟩ : syracuseStep 514669 = 193001) (by norm_num)
theorem B580213 : Blo 358757 580213 := bbase (se 5 (by rfl) ⟨27197, by rfl⟩ : syracuseStep 580213 = 54395) (by norm_num)
theorem B809621 : Blo 358757 809621 := bbase (se 6 (by rfl) ⟨18975, by rfl⟩ : syracuseStep 809621 = 37951) (by norm_num)
theorem B383665 : Blo 358757 383665 := bbase (se 2 (by rfl) ⟨143874, by rfl⟩ : syracuseStep 383665 = 287749) (by norm_num)
theorem B514765 : Blo 358757 514765 := bbase (se 3 (by rfl) ⟨96518, by rfl⟩ : syracuseStep 514765 = 193037) (by norm_num)
theorem B809693 : Blo 358757 809693 := bbase (se 3 (by rfl) ⟨151817, by rfl⟩ : syracuseStep 809693 = 303635) (by norm_num)
theorem B383725 : Blo 358757 383725 := bbase (se 3 (by rfl) ⟨71948, by rfl⟩ : syracuseStep 383725 = 143897) (by norm_num)
theorem B809765 : Blo 358757 809765 := bbase (se 4 (by rfl) ⟨75915, by rfl⟩ : syracuseStep 809765 = 151831) (by norm_num)
theorem B809837 : Blo 358757 809837 := bbase (se 3 (by rfl) ⟨151844, by rfl⟩ : syracuseStep 809837 = 303689) (by norm_num)
theorem B809909 : Blo 358757 809909 := bbase (se 5 (by rfl) ⟨37964, by rfl⟩ : syracuseStep 809909 = 75929) (by norm_num)
theorem B809981 : Blo 358757 809981 := bbase (se 3 (by rfl) ⟨151871, by rfl⟩ : syracuseStep 809981 = 303743) (by norm_num)
theorem B908293 : Blo 358757 908293 := bbase (se 4 (by rfl) ⟨85152, by rfl⟩ : syracuseStep 908293 = 170305) (by norm_num)
theorem B384041 : Blo 358757 384041 := bbase (se 2 (by rfl) ⟨144015, by rfl⟩ : syracuseStep 384041 = 288031) (by norm_num)
theorem B810053 : Blo 358757 810053 := bbase (se 4 (by rfl) ⟨75942, by rfl⟩ : syracuseStep 810053 = 151885) (by norm_num)
theorem B908405 : Blo 358757 908405 := bbase (se 5 (by rfl) ⟨42581, by rfl⟩ : syracuseStep 908405 = 85163) (by norm_num)
theorem B810125 : Blo 358757 810125 := bbase (se 3 (by rfl) ⟨151898, by rfl⟩ : syracuseStep 810125 = 303797) (by norm_num)
theorem B580765 : Blo 358757 580765 := bbase (se 3 (by rfl) ⟨108893, by rfl⟩ : syracuseStep 580765 = 217787) (by norm_num)
theorem B515261 : Blo 358757 515261 := bbase (se 3 (by rfl) ⟨96611, by rfl⟩ : syracuseStep 515261 = 193223) (by norm_num)
theorem B810197 : Blo 358757 810197 := bbase (se 7 (by rfl) ⟨9494, by rfl⟩ : syracuseStep 810197 = 18989) (by norm_num)
theorem B548093 : Blo 358757 548093 := bbase (se 3 (by rfl) ⟨102767, by rfl⟩ : syracuseStep 548093 = 205535) (by norm_num)
theorem B810269 : Blo 358757 810269 := bbase (se 3 (by rfl) ⟨151925, by rfl⟩ : syracuseStep 810269 = 303851) (by norm_num)
theorem B908597 : Blo 358757 908597 := bbase (se 5 (by rfl) ⟨42590, by rfl⟩ : syracuseStep 908597 = 85181) (by norm_num)
theorem B810341 : Blo 358757 810341 := bbase (se 4 (by rfl) ⟨75969, by rfl⟩ : syracuseStep 810341 = 151939) (by norm_num)
theorem B581021 : Blo 358757 581021 := bbase (se 3 (by rfl) ⟨108941, by rfl⟩ : syracuseStep 581021 = 217883) (by norm_num)
theorem B810413 : Blo 358757 810413 := bbase (se 3 (by rfl) ⟨151952, by rfl⟩ : syracuseStep 810413 = 303905) (by norm_num)
theorem B384485 : Blo 358757 384485 := bbase (se 4 (by rfl) ⟨36045, by rfl⟩ : syracuseStep 384485 = 72091) (by norm_num)
theorem B810485 : Blo 358757 810485 := bbase (se 5 (by rfl) ⟨37991, by rfl⟩ : syracuseStep 810485 = 75983) (by norm_num)
theorem B384545 : Blo 358757 384545 := bbase (se 2 (by rfl) ⟨144204, by rfl⟩ : syracuseStep 384545 = 288409) (by norm_num)
theorem B810557 : Blo 358757 810557 := bbase (se 3 (by rfl) ⟨151979, by rfl⟩ : syracuseStep 810557 = 303959) (by norm_num)
theorem B810629 : Blo 358757 810629 := bbase (se 4 (by rfl) ⟨75996, by rfl⟩ : syracuseStep 810629 = 151993) (by norm_num)
theorem B908941 : Blo 358757 908941 := bbase (se 3 (by rfl) ⟨170426, by rfl⟩ : syracuseStep 908941 = 340853) (by norm_num)
theorem B384673 : Blo 358757 384673 := bbase (se 2 (by rfl) ⟨144252, by rfl⟩ : syracuseStep 384673 = 288505) (by norm_num)
theorem B548549 : Blo 358757 548549 := bbase (se 4 (by rfl) ⟨51426, by rfl⟩ : syracuseStep 548549 = 102853) (by norm_num)
theorem B810701 : Blo 358757 810701 := bbase (se 3 (by rfl) ⟨152006, by rfl⟩ : syracuseStep 810701 = 304013) (by norm_num)
theorem B515813 : Blo 358757 515813 := bbase (se 4 (by rfl) ⟨48357, by rfl⟩ : syracuseStep 515813 = 96715) (by norm_num)
theorem B1826549 : Blo 358757 1826549 := bbase (se 5 (by rfl) ⟨85619, by rfl⟩ : syracuseStep 1826549 = 171239) (by norm_num)
theorem B909053 : Blo 358757 909053 := bbase (se 3 (by rfl) ⟨170447, by rfl⟩ : syracuseStep 909053 = 340895) (by norm_num)
theorem B810773 : Blo 358757 810773 := bbase (se 6 (by rfl) ⟨19002, by rfl⟩ : syracuseStep 810773 = 38005) (by norm_num)
theorem B810845 : Blo 358757 810845 := bbase (se 3 (by rfl) ⟨152033, by rfl⟩ : syracuseStep 810845 = 304067) (by norm_num)
theorem B810917 : Blo 358757 810917 := bbase (se 4 (by rfl) ⟨76023, by rfl⟩ : syracuseStep 810917 = 152047) (by norm_num)
theorem B909245 : Blo 358757 909245 := bbase (se 3 (by rfl) ⟨170483, by rfl⟩ : syracuseStep 909245 = 340967) (by norm_num)
theorem B810989 : Blo 358757 810989 := bbase (se 3 (by rfl) ⟨152060, by rfl⟩ : syracuseStep 810989 = 304121) (by norm_num)
theorem B417793 : Blo 358757 417793 := bbase (se 2 (by rfl) ⟨156672, by rfl⟩ : syracuseStep 417793 = 313345) (by norm_num)
theorem B811061 : Blo 358757 811061 := bbase (se 5 (by rfl) ⟨38018, by rfl⟩ : syracuseStep 811061 = 76037) (by norm_num)
theorem B385117 : Blo 358757 385117 := bbase (se 3 (by rfl) ⟨72209, by rfl⟩ : syracuseStep 385117 = 144419) (by norm_num)
theorem B811133 : Blo 358757 811133 := bbase (se 3 (by rfl) ⟨152087, by rfl⟩ : syracuseStep 811133 = 304175) (by norm_num)
theorem B1368197 : Blo 358757 1368197 := bbase (se 4 (by rfl) ⟨128268, by rfl⟩ : syracuseStep 1368197 = 256537) (by norm_num)
theorem B876701 : Blo 358757 876701 := bbase (se 3 (by rfl) ⟨164381, by rfl⟩ : syracuseStep 876701 = 328763) (by norm_num)
theorem B2056373 : Blo 358757 2056373 := bbase (se 5 (by rfl) ⟨96392, by rfl⟩ : syracuseStep 2056373 = 192785) (by norm_num)
theorem B811205 : Blo 358757 811205 := bbase (se 4 (by rfl) ⟨76050, by rfl⟩ : syracuseStep 811205 = 152101) (by norm_num)
theorem B385237 : Blo 358757 385237 := bbase (se 7 (by rfl) ⟨4514, by rfl⟩ : syracuseStep 385237 = 9029) (by norm_num)
theorem B811277 : Blo 358757 811277 := bbase (se 3 (by rfl) ⟨152114, by rfl⟩ : syracuseStep 811277 = 304229) (by norm_num)
theorem B909589 : Blo 358757 909589 := bbase (se 6 (by rfl) ⟨21318, by rfl⟩ : syracuseStep 909589 = 42637) (by norm_num)
theorem B549181 : Blo 358757 549181 := bbase (se 3 (by rfl) ⟨102971, by rfl⟩ : syracuseStep 549181 = 205943) (by norm_num)
theorem B811349 : Blo 358757 811349 := bbase (se 10 (by rfl) ⟨1188, by rfl⟩ : syracuseStep 811349 = 2377) (by norm_num)
theorem B909701 : Blo 358757 909701 := bbase (se 4 (by rfl) ⟨85284, by rfl⟩ : syracuseStep 909701 = 170569) (by norm_num)
theorem B3498389 : Blo 358757 3498389 := bbase (se 6 (by rfl) ⟨81993, by rfl⟩ : syracuseStep 3498389 = 163987) (by norm_num)
theorem B811421 : Blo 358757 811421 := bbase (se 3 (by rfl) ⟨152141, by rfl⟩ : syracuseStep 811421 = 304283) (by norm_num)
theorem B1368485 : Blo 358757 1368485 := bbase (se 4 (by rfl) ⟨128295, by rfl⟩ : syracuseStep 1368485 = 256591) (by norm_num)
theorem B385489 : Blo 358757 385489 := bbase (se 2 (by rfl) ⟨144558, by rfl⟩ : syracuseStep 385489 = 289117) (by norm_num)
theorem B385493 : Blo 358757 385493 := bbase (se 7 (by rfl) ⟨4517, by rfl⟩ : syracuseStep 385493 = 9035) (by norm_num)
theorem B811493 : Blo 358757 811493 := bbase (se 4 (by rfl) ⟨76077, by rfl⟩ : syracuseStep 811493 = 152155) (by norm_num)
theorem B811565 : Blo 358757 811565 := bbase (se 3 (by rfl) ⟨152168, by rfl⟩ : syracuseStep 811565 = 304337) (by norm_num)
theorem B909893 : Blo 358757 909893 := bbase (se 4 (by rfl) ⟨85302, by rfl⟩ : syracuseStep 909893 = 170605) (by norm_num)
theorem B549461 : Blo 358757 549461 := bbase (se 8 (by rfl) ⟨3219, by rfl⟩ : syracuseStep 549461 = 6439) (by norm_num)
theorem B811637 : Blo 358757 811637 := bbase (se 5 (by rfl) ⟨38045, by rfl⟩ : syracuseStep 811637 = 76091) (by norm_num)
theorem B811709 : Blo 358757 811709 := bbase (se 3 (by rfl) ⟨152195, by rfl⟩ : syracuseStep 811709 = 304391) (by norm_num)
theorem B1532677 : Blo 358757 1532677 := bbase (se 4 (by rfl) ⟨143688, by rfl⟩ : syracuseStep 1532677 = 287377) (by norm_num)
theorem B811781 : Blo 358757 811781 := bbase (se 4 (by rfl) ⟨76104, by rfl⟩ : syracuseStep 811781 = 152209) (by norm_num)
theorem B3498773 : Blo 358757 3498773 := bbase (se 6 (by rfl) ⟨82002, by rfl⟩ : syracuseStep 3498773 = 164005) (by norm_num)
theorem B1467173 : Blo 358757 1467173 := bbase (se 4 (by rfl) ⟨137547, by rfl⟩ : syracuseStep 1467173 = 275095) (by norm_num)
theorem B811853 : Blo 358757 811853 := bbase (se 3 (by rfl) ⟨152222, by rfl⟩ : syracuseStep 811853 = 304445) (by norm_num)
theorem B2614133 : Blo 358757 2614133 := bbase (se 5 (by rfl) ⟨122537, by rfl⟩ : syracuseStep 2614133 = 245075) (by norm_num)
theorem B811925 : Blo 358757 811925 := bbase (se 6 (by rfl) ⟨19029, by rfl⟩ : syracuseStep 811925 = 38059) (by norm_num)
theorem B910237 : Blo 358757 910237 := bbase (se 3 (by rfl) ⟨170669, by rfl⟩ : syracuseStep 910237 = 341339) (by norm_num)
theorem B615325 : Blo 358757 615325 := bbase (se 3 (by rfl) ⟨115373, by rfl⟩ : syracuseStep 615325 = 230747) (by norm_num)
theorem B549845 : Blo 358757 549845 := bbase (se 7 (by rfl) ⟨6443, by rfl⟩ : syracuseStep 549845 = 12887) (by norm_num)
theorem B811997 : Blo 358757 811997 := bbase (se 3 (by rfl) ⟨152249, by rfl⟩ : syracuseStep 811997 = 304499) (by norm_num)
theorem B1827845 : Blo 358757 1827845 := bbase (se 4 (by rfl) ⟨171360, by rfl⟩ : syracuseStep 1827845 = 342721) (by norm_num)
theorem B386057 : Blo 358757 386057 := bbase (se 2 (by rfl) ⟨144771, by rfl⟩ : syracuseStep 386057 = 289543) (by norm_num)
theorem B910349 : Blo 358757 910349 := bbase (se 3 (by rfl) ⟨170690, by rfl⟩ : syracuseStep 910349 = 341381) (by norm_num)
theorem B812069 : Blo 358757 812069 := bbase (se 4 (by rfl) ⟨76131, by rfl⟩ : syracuseStep 812069 = 152263) (by norm_num)
theorem B812141 : Blo 358757 812141 := bbase (se 3 (by rfl) ⟨152276, by rfl⟩ : syracuseStep 812141 = 304553) (by norm_num)
theorem B812213 : Blo 358757 812213 := bbase (se 5 (by rfl) ⟨38072, by rfl⟩ : syracuseStep 812213 = 76145) (by norm_num)
theorem B386245 : Blo 358757 386245 := bbase (se 4 (by rfl) ⟨36210, by rfl⟩ : syracuseStep 386245 = 72421) (by norm_num)
theorem B910541 : Blo 358757 910541 := bbase (se 3 (by rfl) ⟨170726, by rfl⟩ : syracuseStep 910541 = 341453) (by norm_num)
theorem B681205 : Blo 358757 681205 := bbase (se 5 (by rfl) ⟨31931, by rfl⟩ : syracuseStep 681205 = 63863) (by norm_num)
theorem B1729781 : Blo 358757 1729781 := bbase (se 5 (by rfl) ⟨81083, by rfl⟩ : syracuseStep 1729781 = 162167) (by norm_num)
theorem B812285 : Blo 358757 812285 := bbase (se 3 (by rfl) ⟨152303, by rfl⟩ : syracuseStep 812285 = 304607) (by norm_num)
theorem B812357 : Blo 358757 812357 := bbase (se 4 (by rfl) ⟨76158, by rfl⟩ : syracuseStep 812357 = 152317) (by norm_num)
theorem B419161 : Blo 358757 419161 := bbase (se 2 (by rfl) ⟨157185, by rfl⟩ : syracuseStep 419161 = 314371) (by norm_num)
theorem B812429 : Blo 358757 812429 := bbase (se 3 (by rfl) ⟨152330, by rfl⟩ : syracuseStep 812429 = 304661) (by norm_num)
theorem B681365 : Blo 358757 681365 := bbase (se 6 (by rfl) ⟨15969, by rfl⟩ : syracuseStep 681365 = 31939) (by norm_num)
theorem B812501 : Blo 358757 812501 := bbase (se 7 (by rfl) ⟨9521, by rfl⟩ : syracuseStep 812501 = 19043) (by norm_num)
theorem B812573 : Blo 358757 812573 := bbase (se 3 (by rfl) ⟨152357, by rfl⟩ : syracuseStep 812573 = 304715) (by norm_num)
theorem B681509 : Blo 358757 681509 := bbase (se 4 (by rfl) ⟨63891, by rfl⟩ : syracuseStep 681509 = 127783) (by norm_num)
theorem B910885 : Blo 358757 910885 := bbase (se 4 (by rfl) ⟨85395, by rfl⟩ : syracuseStep 910885 = 170791) (by norm_num)
theorem B1369669 : Blo 358757 1369669 := bbase (se 4 (by rfl) ⟨128406, by rfl⟩ : syracuseStep 1369669 = 256813) (by norm_num)
theorem B648805 : Blo 358757 648805 := bbase (se 4 (by rfl) ⟨60825, by rfl⟩ : syracuseStep 648805 = 121651) (by norm_num)
theorem B812645 : Blo 358757 812645 := bbase (se 4 (by rfl) ⟨76185, by rfl⟩ : syracuseStep 812645 = 152371) (by norm_num)
theorem B910997 : Blo 358757 910997 := bbase (se 6 (by rfl) ⟨21351, by rfl⟩ : syracuseStep 910997 = 42703) (by norm_num)
theorem B812717 : Blo 358757 812717 := bbase (se 3 (by rfl) ⟨152384, by rfl⟩ : syracuseStep 812717 = 304769) (by norm_num)
theorem B812789 : Blo 358757 812789 := bbase (se 5 (by rfl) ⟨38099, by rfl⟩ : syracuseStep 812789 = 76199) (by norm_num)
theorem B812861 : Blo 358757 812861 := bbase (se 3 (by rfl) ⟨152411, by rfl⟩ : syracuseStep 812861 = 304823) (by norm_num)
theorem B681797 : Blo 358757 681797 := bbase (se 4 (by rfl) ⟨63918, by rfl⟩ : syracuseStep 681797 = 127837) (by norm_num)
theorem B911189 : Blo 358757 911189 := bbase (se 9 (by rfl) ⟨2669, by rfl⟩ : syracuseStep 911189 = 5339) (by norm_num)
theorem B1369973 : Blo 358757 1369973 := bbase (se 5 (by rfl) ⟨64217, by rfl⟩ : syracuseStep 1369973 = 128435) (by norm_num)
theorem B812933 : Blo 358757 812933 := bbase (se 4 (by rfl) ⟨76212, by rfl⟩ : syracuseStep 812933 = 152425) (by norm_num)
theorem B813005 : Blo 358757 813005 := bbase (se 3 (by rfl) ⟨152438, by rfl⟩ : syracuseStep 813005 = 304877) (by norm_num)
theorem B681949 : Blo 358757 681949 := bbase (se 3 (by rfl) ⟨127865, by rfl⟩ : syracuseStep 681949 = 255731) (by norm_num)
theorem B387065 : Blo 358757 387065 := bbase (se 2 (by rfl) ⟨145149, by rfl⟩ : syracuseStep 387065 = 290299) (by norm_num)
theorem B3467285 : Blo 358757 3467285 := bbase (se 6 (by rfl) ⟨81264, by rfl⟩ : syracuseStep 3467285 = 162529) (by norm_num)
theorem B813077 : Blo 358757 813077 := bbase (se 6 (by rfl) ⟨19056, by rfl⟩ : syracuseStep 813077 = 38113) (by norm_num)
theorem B649309 : Blo 358757 649309 := bbase (se 3 (by rfl) ⟨121745, by rfl⟩ : syracuseStep 649309 = 243491) (by norm_num)
theorem B813149 : Blo 358757 813149 := bbase (se 3 (by rfl) ⟨152465, by rfl⟩ : syracuseStep 813149 = 304931) (by norm_num)
theorem B813221 : Blo 358757 813221 := bbase (se 4 (by rfl) ⟨76239, by rfl⟩ : syracuseStep 813221 = 152479) (by norm_num)
theorem B911533 : Blo 358757 911533 := bbase (se 3 (by rfl) ⟨170912, by rfl⟩ : syracuseStep 911533 = 341825) (by norm_num)
theorem B2091221 : Blo 358757 2091221 := bbase (se 7 (by rfl) ⟨24506, by rfl⟩ : syracuseStep 2091221 = 49013) (by norm_num)
theorem B813293 : Blo 358757 813293 := bbase (se 3 (by rfl) ⟨152492, by rfl⟩ : syracuseStep 813293 = 304985) (by norm_num)
theorem B682253 : Blo 358757 682253 := bbase (se 3 (by rfl) ⟨127922, by rfl⟩ : syracuseStep 682253 = 255845) (by norm_num)
theorem B1829141 : Blo 358757 1829141 := bbase (se 6 (by rfl) ⟨42870, by rfl⟩ : syracuseStep 1829141 = 85741) (by norm_num)
theorem B911645 : Blo 358757 911645 := bbase (se 3 (by rfl) ⟨170933, by rfl⟩ : syracuseStep 911645 = 341867) (by norm_num)
theorem B813365 : Blo 358757 813365 := bbase (se 5 (by rfl) ⟨38126, by rfl⟩ : syracuseStep 813365 = 76253) (by norm_num)
theorem B616829 : Blo 358757 616829 := bbase (se 3 (by rfl) ⟨115655, by rfl⟩ : syracuseStep 616829 = 231311) (by norm_num)
theorem B813437 : Blo 358757 813437 := bbase (se 3 (by rfl) ⟨152519, by rfl⟩ : syracuseStep 813437 = 305039) (by norm_num)
theorem B518557 : Blo 358757 518557 := bbase (se 3 (by rfl) ⟨97229, by rfl⟩ : syracuseStep 518557 = 194459) (by norm_num)
theorem B813509 : Blo 358757 813509 := bbase (se 4 (by rfl) ⟨76266, by rfl⟩ : syracuseStep 813509 = 152533) (by norm_num)
theorem B911837 : Blo 358757 911837 := bbase (se 3 (by rfl) ⟨170969, by rfl⟩ : syracuseStep 911837 = 341939) (by norm_num)
theorem B813581 : Blo 358757 813581 := bbase (se 3 (by rfl) ⟨152546, by rfl⟩ : syracuseStep 813581 = 305093) (by norm_num)
theorem B813653 : Blo 358757 813653 := bbase (se 8 (by rfl) ⟨4767, by rfl⟩ : syracuseStep 813653 = 9535) (by norm_num)
theorem B813725 : Blo 358757 813725 := bbase (se 3 (by rfl) ⟨152573, by rfl⟩ : syracuseStep 813725 = 305147) (by norm_num)
theorem B813797 : Blo 358757 813797 := bbase (se 4 (by rfl) ⟨76293, by rfl⟩ : syracuseStep 813797 = 152587) (by norm_num)
theorem B813869 : Blo 358757 813869 := bbase (se 3 (by rfl) ⟨152600, by rfl⟩ : syracuseStep 813869 = 305201) (by norm_num)
theorem B912181 : Blo 358757 912181 := bbase (se 5 (by rfl) ⟨42758, by rfl⟩ : syracuseStep 912181 = 85517) (by norm_num)
theorem B813941 : Blo 358757 813941 := bbase (se 5 (by rfl) ⟨38153, by rfl⟩ : syracuseStep 813941 = 76307) (by norm_num)
theorem B912293 : Blo 358757 912293 := bbase (se 4 (by rfl) ⟨85527, by rfl⟩ : syracuseStep 912293 = 171055) (by norm_num)
theorem B814013 : Blo 358757 814013 := bbase (se 3 (by rfl) ⟨152627, by rfl⟩ : syracuseStep 814013 = 305255) (by norm_num)
theorem B650189 : Blo 358757 650189 := bbase (se 3 (by rfl) ⟨121910, by rfl⟩ : syracuseStep 650189 = 243821) (by norm_num)
theorem B683005 : Blo 358757 683005 := bbase (se 3 (by rfl) ⟨128063, by rfl⟩ : syracuseStep 683005 = 256127) (by norm_num)
theorem B814085 : Blo 358757 814085 := bbase (se 4 (by rfl) ⟨76320, by rfl⟩ : syracuseStep 814085 = 152641) (by norm_num)
theorem B814157 : Blo 358757 814157 := bbase (se 3 (by rfl) ⟨152654, by rfl⟩ : syracuseStep 814157 = 305309) (by norm_num)
theorem B912485 : Blo 358757 912485 := bbase (se 4 (by rfl) ⟨85545, by rfl⟩ : syracuseStep 912485 = 171091) (by norm_num)
theorem B683149 : Blo 358757 683149 := bbase (se 3 (by rfl) ⟨128090, by rfl⟩ : syracuseStep 683149 = 256181) (by norm_num)
theorem B814229 : Blo 358757 814229 := bbase (se 6 (by rfl) ⟨19083, by rfl⟩ : syracuseStep 814229 = 38167) (by norm_num)
theorem B650405 : Blo 358757 650405 := bbase (se 4 (by rfl) ⟨60975, by rfl⟩ : syracuseStep 650405 = 121951) (by norm_num)
theorem B519341 : Blo 358757 519341 := bbase (se 3 (by rfl) ⟨97376, by rfl⟩ : syracuseStep 519341 = 194753) (by norm_num)
theorem B1731797 : Blo 358757 1731797 := bbase (se 7 (by rfl) ⟨20294, by rfl⟩ : syracuseStep 1731797 = 40589) (by norm_num)
theorem B814301 : Blo 358757 814301 := bbase (se 3 (by rfl) ⟨152681, by rfl⟩ : syracuseStep 814301 = 305363) (by norm_num)
theorem B814373 : Blo 358757 814373 := bbase (se 4 (by rfl) ⟨76347, by rfl⟩ : syracuseStep 814373 = 152695) (by norm_num)
theorem B683309 : Blo 358757 683309 := bbase (se 3 (by rfl) ⟨128120, by rfl⟩ : syracuseStep 683309 = 256241) (by norm_num)
theorem B650549 : Blo 358757 650549 := bbase (se 5 (by rfl) ⟨30494, by rfl⟩ : syracuseStep 650549 = 60989) (by norm_num)
theorem B814445 : Blo 358757 814445 := bbase (se 3 (by rfl) ⟨152708, by rfl⟩ : syracuseStep 814445 = 305417) (by norm_num)
theorem B650629 : Blo 358757 650629 := bbase (se 4 (by rfl) ⟨60996, by rfl⟩ : syracuseStep 650629 = 121993) (by norm_num)
theorem B486805 : Blo 358757 486805 := bbase (se 6 (by rfl) ⟨11409, by rfl⟩ : syracuseStep 486805 = 22819) (by norm_num)
theorem B814517 : Blo 358757 814517 := bbase (se 5 (by rfl) ⟨38180, by rfl⟩ : syracuseStep 814517 = 76361) (by norm_num)
theorem B683453 : Blo 358757 683453 := bbase (se 3 (by rfl) ⟨128147, by rfl⟩ : syracuseStep 683453 = 256295) (by norm_num)
theorem B912829 : Blo 358757 912829 := bbase (se 3 (by rfl) ⟨171155, by rfl⟩ : syracuseStep 912829 = 342311) (by norm_num)
theorem B454081 : Blo 358757 454081 := bbase (se 2 (by rfl) ⟨170280, by rfl⟩ : syracuseStep 454081 = 340561) (by norm_num)
theorem B814589 : Blo 358757 814589 := bbase (se 3 (by rfl) ⟨152735, by rfl⟩ : syracuseStep 814589 = 305471) (by norm_num)
theorem B454177 : Blo 358757 454177 := bbase (se 2 (by rfl) ⟨170316, by rfl⟩ : syracuseStep 454177 = 340633) (by norm_num)
theorem B1830437 : Blo 358757 1830437 := bbase (se 4 (by rfl) ⟨171603, by rfl⟩ : syracuseStep 1830437 = 343207) (by norm_num)
theorem B912941 : Blo 358757 912941 := bbase (se 3 (by rfl) ⟨171176, by rfl⟩ : syracuseStep 912941 = 342353) (by norm_num)
theorem B814661 : Blo 358757 814661 := bbase (se 4 (by rfl) ⟨76374, by rfl⟩ : syracuseStep 814661 = 152749) (by norm_num)
theorem B814733 : Blo 358757 814733 := bbase (se 3 (by rfl) ⟨152762, by rfl⟩ : syracuseStep 814733 = 305525) (by norm_num)
theorem B1535669 : Blo 358757 1535669 := bbase (se 5 (by rfl) ⟨71984, by rfl⟩ : syracuseStep 1535669 = 143969) (by norm_num)
theorem B454349 : Blo 358757 454349 := bbase (se 3 (by rfl) ⟨85190, by rfl⟩ : syracuseStep 454349 = 170381) (by norm_num)
theorem B814805 : Blo 358757 814805 := bbase (se 7 (by rfl) ⟨9548, by rfl⟩ : syracuseStep 814805 = 19097) (by norm_num)
theorem B683741 : Blo 358757 683741 := bbase (se 3 (by rfl) ⟨128201, by rfl⟩ : syracuseStep 683741 = 256403) (by norm_num)
theorem B913133 : Blo 358757 913133 := bbase (se 3 (by rfl) ⟨171212, by rfl⟩ : syracuseStep 913133 = 342425) (by norm_num)
theorem B454405 : Blo 358757 454405 := bbase (se 4 (by rfl) ⟨42600, by rfl⟩ : syracuseStep 454405 = 85201) (by norm_num)
theorem B814877 : Blo 358757 814877 := bbase (se 3 (by rfl) ⟨152789, by rfl⟩ : syracuseStep 814877 = 305579) (by norm_num)
theorem B487253 : Blo 358757 487253 := bbase (se 9 (by rfl) ⟨1427, by rfl⟩ : syracuseStep 487253 = 2855) (by norm_num)
theorem B454501 : Blo 358757 454501 := bbase (se 4 (by rfl) ⟨42609, by rfl⟩ : syracuseStep 454501 = 85219) (by norm_num)
theorem B814949 : Blo 358757 814949 := bbase (se 4 (by rfl) ⟨76401, by rfl⟩ : syracuseStep 814949 = 152803) (by norm_num)
theorem B683893 : Blo 358757 683893 := bbase (se 5 (by rfl) ⟨32057, by rfl⟩ : syracuseStep 683893 = 64115) (by norm_num)
theorem B815021 : Blo 358757 815021 := bbase (se 3 (by rfl) ⟨152816, by rfl⟩ : syracuseStep 815021 = 305633) (by norm_num)
theorem B1372085 : Blo 358757 1372085 := bbase (se 5 (by rfl) ⟨64316, by rfl⟩ : syracuseStep 1372085 = 128633) (by norm_num)
theorem B1732549 : Blo 358757 1732549 := bbase (se 4 (by rfl) ⟨162426, by rfl⟩ : syracuseStep 1732549 = 324853) (by norm_num)
theorem B815093 : Blo 358757 815093 := bbase (se 5 (by rfl) ⟨38207, by rfl⟩ : syracuseStep 815093 = 76415) (by norm_num)
theorem B454673 : Blo 358757 454673 := bbase (se 2 (by rfl) ⟨170502, by rfl⟩ : syracuseStep 454673 = 341005) (by norm_num)
theorem B815165 : Blo 358757 815165 := bbase (se 3 (by rfl) ⟨152843, by rfl⟩ : syracuseStep 815165 = 305687) (by norm_num)
theorem B913477 : Blo 358757 913477 := bbase (se 4 (by rfl) ⟨85638, by rfl⟩ : syracuseStep 913477 = 171277) (by norm_num)
theorem B454729 : Blo 358757 454729 := bbase (se 2 (by rfl) ⟨170523, by rfl⟩ : syracuseStep 454729 = 341047) (by norm_num)
theorem B815237 : Blo 358757 815237 := bbase (se 4 (by rfl) ⟨76428, by rfl⟩ : syracuseStep 815237 = 152857) (by norm_num)
theorem B684197 : Blo 358757 684197 := bbase (se 4 (by rfl) ⟨64143, by rfl⟩ : syracuseStep 684197 = 128287) (by norm_num)
theorem B454825 : Blo 358757 454825 := bbase (se 2 (by rfl) ⟨170559, by rfl⟩ : syracuseStep 454825 = 341119) (by norm_num)
theorem B913589 : Blo 358757 913589 := bbase (se 5 (by rfl) ⟨42824, by rfl⟩ : syracuseStep 913589 = 85649) (by norm_num)
theorem B815309 : Blo 358757 815309 := bbase (se 3 (by rfl) ⟨152870, by rfl⟩ : syracuseStep 815309 = 305741) (by norm_num)
theorem B1372373 : Blo 358757 1372373 := bbase (se 7 (by rfl) ⟨16082, by rfl⟩ : syracuseStep 1372373 = 32165) (by norm_num)
theorem B815381 : Blo 358757 815381 := bbase (se 6 (by rfl) ⟨19110, by rfl⟩ : syracuseStep 815381 = 38221) (by norm_num)
theorem B454997 : Blo 358757 454997 := bbase (se 10 (by rfl) ⟨666, by rfl⟩ : syracuseStep 454997 = 1333) (by norm_num)
theorem B815453 : Blo 358757 815453 := bbase (se 3 (by rfl) ⟨152897, by rfl⟩ : syracuseStep 815453 = 305795) (by norm_num)
theorem B913781 : Blo 358757 913781 := bbase (se 5 (by rfl) ⟨42833, by rfl⟩ : syracuseStep 913781 = 85667) (by norm_num)
theorem B455053 : Blo 358757 455053 := bbase (se 3 (by rfl) ⟨85322, by rfl⟩ : syracuseStep 455053 = 170645) (by norm_num)
theorem B815525 : Blo 358757 815525 := bbase (se 4 (by rfl) ⟨76455, by rfl⟩ : syracuseStep 815525 = 152911) (by norm_num)
theorem B455149 : Blo 358757 455149 := bbase (se 3 (by rfl) ⟨85340, by rfl⟩ : syracuseStep 455149 = 170681) (by norm_num)
theorem B815597 : Blo 358757 815597 := bbase (se 3 (by rfl) ⟨152924, by rfl⟩ : syracuseStep 815597 = 305849) (by norm_num)
theorem B815669 : Blo 358757 815669 := bbase (se 5 (by rfl) ⟨38234, by rfl⟩ : syracuseStep 815669 = 76469) (by norm_num)
theorem B815741 : Blo 358757 815741 := bbase (se 3 (by rfl) ⟨152951, by rfl⟩ : syracuseStep 815741 = 305903) (by norm_num)
theorem B619157 : Blo 358757 619157 := bbase (se 6 (by rfl) ⟨14511, by rfl⟩ : syracuseStep 619157 = 29023) (by norm_num)
theorem B455321 : Blo 358757 455321 := bbase (se 2 (by rfl) ⟨170745, by rfl⟩ : syracuseStep 455321 = 341491) (by norm_num)
theorem B1536677 : Blo 358757 1536677 := bbase (se 4 (by rfl) ⟨144063, by rfl⟩ : syracuseStep 1536677 = 288127) (by norm_num)
theorem B815813 : Blo 358757 815813 := bbase (se 4 (by rfl) ⟨76482, by rfl⟩ : syracuseStep 815813 = 152965) (by norm_num)
theorem B914125 : Blo 358757 914125 := bbase (se 3 (by rfl) ⟨171398, by rfl⟩ : syracuseStep 914125 = 342797) (by norm_num)
theorem B455377 : Blo 358757 455377 := bbase (se 2 (by rfl) ⟨170766, by rfl⟩ : syracuseStep 455377 = 341533) (by norm_num)
theorem B783101 : Blo 358757 783101 := bbase (se 3 (by rfl) ⟨146831, by rfl⟩ : syracuseStep 783101 = 293663) (by norm_num)
theorem B815885 : Blo 358757 815885 := bbase (se 3 (by rfl) ⟨152978, by rfl⟩ : syracuseStep 815885 = 305957) (by norm_num)
theorem B1766165 : Blo 358757 1766165 := bbase (se 6 (by rfl) ⟨41394, by rfl⟩ : syracuseStep 1766165 = 82789) (by norm_num)
theorem B455473 : Blo 358757 455473 := bbase (se 2 (by rfl) ⟨170802, by rfl⟩ : syracuseStep 455473 = 341605) (by norm_num)
theorem B1831733 : Blo 358757 1831733 := bbase (se 5 (by rfl) ⟨85862, by rfl⟩ : syracuseStep 1831733 = 171725) (by norm_num)
theorem B914237 : Blo 358757 914237 := bbase (se 3 (by rfl) ⟨171419, by rfl⟩ : syracuseStep 914237 = 342839) (by norm_num)
theorem B1045333 : Blo 358757 1045333 := bbase (se 9 (by rfl) ⟨3062, by rfl⟩ : syracuseStep 1045333 = 6125) (by norm_num)
theorem B815957 : Blo 358757 815957 := bbase (se 9 (by rfl) ⟨2390, by rfl⟩ : syracuseStep 815957 = 4781) (by norm_num)
theorem B2749301 : Blo 358757 2749301 := bbase (se 5 (by rfl) ⟨128873, by rfl⟩ : syracuseStep 2749301 = 257747) (by norm_num)
theorem B553853 : Blo 358757 553853 := bbase (se 3 (by rfl) ⟨103847, by rfl⟩ : syracuseStep 553853 = 207695) (by norm_num)
theorem B684949 : Blo 358757 684949 := bbase (se 6 (by rfl) ⟨16053, by rfl⟩ : syracuseStep 684949 = 32107) (by norm_num)
theorem B816029 : Blo 358757 816029 := bbase (se 3 (by rfl) ⟨153005, by rfl⟩ : syracuseStep 816029 = 306011) (by norm_num)
theorem B455645 : Blo 358757 455645 := bbase (se 3 (by rfl) ⟨85433, by rfl⟩ : syracuseStep 455645 = 170867) (by norm_num)
theorem B816101 : Blo 358757 816101 := bbase (se 4 (by rfl) ⟨76509, by rfl⟩ : syracuseStep 816101 = 153019) (by norm_num)
theorem B914429 : Blo 358757 914429 := bbase (se 3 (by rfl) ⟨171455, by rfl⟩ : syracuseStep 914429 = 342911) (by norm_num)
theorem B455701 : Blo 358757 455701 := bbase (se 6 (by rfl) ⟨10680, by rfl⟩ : syracuseStep 455701 = 21361) (by norm_num)
theorem B685093 : Blo 358757 685093 := bbase (se 4 (by rfl) ⟨64227, by rfl⟩ : syracuseStep 685093 = 128455) (by norm_num)
theorem B816173 : Blo 358757 816173 := bbase (se 3 (by rfl) ⟨153032, by rfl⟩ : syracuseStep 816173 = 306065) (by norm_num)
theorem B455797 : Blo 358757 455797 := bbase (se 5 (by rfl) ⟨21365, by rfl⟩ : syracuseStep 455797 = 42731) (by norm_num)
theorem B685253 : Blo 358757 685253 := bbase (se 4 (by rfl) ⟨64242, by rfl⟩ : syracuseStep 685253 = 128485) (by norm_num)
theorem B455969 : Blo 358757 455969 := bbase (se 2 (by rfl) ⟨170988, by rfl⟩ : syracuseStep 455969 = 341977) (by norm_num)
theorem B685397 : Blo 358757 685397 := bbase (se 13 (by rfl) ⟨125, by rfl⟩ : syracuseStep 685397 = 251) (by norm_num)
theorem B914773 : Blo 358757 914773 := bbase (se 13 (by rfl) ⟨167, by rfl⟩ : syracuseStep 914773 = 335) (by norm_num)
theorem B456025 : Blo 358757 456025 := bbase (se 2 (by rfl) ⟨171009, by rfl⟩ : syracuseStep 456025 = 342019) (by norm_num)
theorem B1373557 : Blo 358757 1373557 := bbase (se 5 (by rfl) ⟨64385, by rfl⟩ : syracuseStep 1373557 = 128771) (by norm_num)
theorem B456121 : Blo 358757 456121 := bbase (se 2 (by rfl) ⟨171045, by rfl⟩ : syracuseStep 456121 = 342091) (by norm_num)
theorem B914885 : Blo 358757 914885 := bbase (se 4 (by rfl) ⟨85770, by rfl⟩ : syracuseStep 914885 = 171541) (by norm_num)
theorem B456293 : Blo 358757 456293 := bbase (se 4 (by rfl) ⟨42777, by rfl⟩ : syracuseStep 456293 = 85555) (by norm_num)
theorem B685685 : Blo 358757 685685 := bbase (se 5 (by rfl) ⟨32141, by rfl⟩ : syracuseStep 685685 = 64283) (by norm_num)
theorem B915077 : Blo 358757 915077 := bbase (se 4 (by rfl) ⟨85788, by rfl⟩ : syracuseStep 915077 = 171577) (by norm_num)
theorem B456349 : Blo 358757 456349 := bbase (se 3 (by rfl) ⟨85565, by rfl⟩ : syracuseStep 456349 = 171131) (by norm_num)
theorem B1373861 : Blo 358757 1373861 := bbase (se 4 (by rfl) ⟨128799, by rfl⟩ : syracuseStep 1373861 = 257599) (by norm_num)
theorem B2324213 : Blo 358757 2324213 := bbase (se 5 (by rfl) ⟨108947, by rfl⟩ : syracuseStep 2324213 = 217895) (by norm_num)
theorem B456445 : Blo 358757 456445 := bbase (se 3 (by rfl) ⟨85583, by rfl⟩ : syracuseStep 456445 = 171167) (by norm_num)
theorem B685837 : Blo 358757 685837 := bbase (se 3 (by rfl) ⟨128594, by rfl⟩ : syracuseStep 685837 = 257189) (by norm_num)
theorem B456617 : Blo 358757 456617 := bbase (se 2 (by rfl) ⟨171231, by rfl⟩ : syracuseStep 456617 = 342463) (by norm_num)
theorem B653261 : Blo 358757 653261 := bbase (se 3 (by rfl) ⟨122486, by rfl⟩ : syracuseStep 653261 = 244973) (by norm_num)
theorem B915421 : Blo 358757 915421 := bbase (se 3 (by rfl) ⟨171641, by rfl⟩ : syracuseStep 915421 = 343283) (by norm_num)
theorem B456673 : Blo 358757 456673 := bbase (se 2 (by rfl) ⟨171252, by rfl⟩ : syracuseStep 456673 = 342505) (by norm_num)
theorem B686141 : Blo 358757 686141 := bbase (se 3 (by rfl) ⟨128651, by rfl⟩ : syracuseStep 686141 = 257303) (by norm_num)
theorem B456769 : Blo 358757 456769 := bbase (se 2 (by rfl) ⟨171288, by rfl⟩ : syracuseStep 456769 = 342577) (by norm_num)
theorem B1833029 : Blo 358757 1833029 := bbase (se 4 (by rfl) ⟨171846, by rfl⟩ : syracuseStep 1833029 = 343693) (by norm_num)
theorem B915533 : Blo 358757 915533 := bbase (se 3 (by rfl) ⟨171662, by rfl⟩ : syracuseStep 915533 = 343325) (by norm_num)
theorem B587893 : Blo 358757 587893 := bbase (se 5 (by rfl) ⟨27557, by rfl⟩ : syracuseStep 587893 = 55115) (by norm_num)
theorem B456941 : Blo 358757 456941 := bbase (se 3 (by rfl) ⟨85676, by rfl⟩ : syracuseStep 456941 = 171353) (by norm_num)
theorem B915725 : Blo 358757 915725 := bbase (se 3 (by rfl) ⟨171698, by rfl⟩ : syracuseStep 915725 = 343397) (by norm_num)
theorem B456997 : Blo 358757 456997 := bbase (se 4 (by rfl) ⟨42843, by rfl⟩ : syracuseStep 456997 = 85687) (by norm_num)
theorem B457093 : Blo 358757 457093 := bbase (se 4 (by rfl) ⟨42852, by rfl⟩ : syracuseStep 457093 = 85705) (by norm_num)
theorem B1538453 : Blo 358757 1538453 := bbase (se 6 (by rfl) ⟨36057, by rfl⟩ : syracuseStep 1538453 = 72115) (by norm_num)
theorem B4946453 : Blo 358757 4946453 := bbase (se 6 (by rfl) ⟨115932, by rfl⟩ : syracuseStep 4946453 = 231865) (by norm_num)
theorem B457265 : Blo 358757 457265 := bbase (se 2 (by rfl) ⟨171474, by rfl⟩ : syracuseStep 457265 = 342949) (by norm_num)
theorem B1210949 : Blo 358757 1210949 := bbase (se 4 (by rfl) ⟨113526, by rfl⟩ : syracuseStep 1210949 = 227053) (by norm_num)
theorem B916069 : Blo 358757 916069 := bbase (se 4 (by rfl) ⟨85881, by rfl⟩ : syracuseStep 916069 = 171763) (by norm_num)
theorem B457321 : Blo 358757 457321 := bbase (se 2 (by rfl) ⟨171495, by rfl⟩ : syracuseStep 457321 = 342991) (by norm_num)
theorem B948893 : Blo 358757 948893 := bbase (se 3 (by rfl) ⟨177917, by rfl⟩ : syracuseStep 948893 = 355835) (by norm_num)
theorem B457417 : Blo 358757 457417 := bbase (se 2 (by rfl) ⟨171531, by rfl⟩ : syracuseStep 457417 = 343063) (by norm_num)
theorem B916181 : Blo 358757 916181 := bbase (se 7 (by rfl) ⟨10736, by rfl⟩ : syracuseStep 916181 = 21473) (by norm_num)
theorem B686893 : Blo 358757 686893 := bbase (se 3 (by rfl) ⟨128792, by rfl⟩ : syracuseStep 686893 = 257585) (by norm_num)
theorem B457589 : Blo 358757 457589 := bbase (se 5 (by rfl) ⟨21449, by rfl⟩ : syracuseStep 457589 = 42899) (by norm_num)
theorem B916373 : Blo 358757 916373 := bbase (se 6 (by rfl) ⟨21477, by rfl⟩ : syracuseStep 916373 = 42955) (by norm_num)
theorem B457645 : Blo 358757 457645 := bbase (se 3 (by rfl) ⟨85808, by rfl⟩ : syracuseStep 457645 = 171617) (by norm_num)
theorem B687037 : Blo 358757 687037 := bbase (se 3 (by rfl) ⟨128819, by rfl⟩ : syracuseStep 687037 = 257639) (by norm_num)
theorem B1211381 : Blo 358757 1211381 := bbase (se 5 (by rfl) ⟨56783, by rfl⟩ : syracuseStep 1211381 = 113567) (by norm_num)
theorem B457741 : Blo 358757 457741 := bbase (se 3 (by rfl) ⟨85826, by rfl⟩ : syracuseStep 457741 = 171653) (by norm_num)
theorem B523325 : Blo 358757 523325 := bbase (se 3 (by rfl) ⟨98123, by rfl⟩ : syracuseStep 523325 = 196247) (by norm_num)
theorem B687197 : Blo 358757 687197 := bbase (se 3 (by rfl) ⟨128849, by rfl⟩ : syracuseStep 687197 = 257699) (by norm_num)
theorem B457913 : Blo 358757 457913 := bbase (se 2 (by rfl) ⟨171717, by rfl⟩ : syracuseStep 457913 = 343435) (by norm_num)
theorem B687341 : Blo 358757 687341 := bbase (se 3 (by rfl) ⟨128876, by rfl⟩ : syracuseStep 687341 = 257753) (by norm_num)
theorem B916717 : Blo 358757 916717 := bbase (se 3 (by rfl) ⟨171884, by rfl⟩ : syracuseStep 916717 = 343769) (by norm_num)
theorem B457969 : Blo 358757 457969 := bbase (se 2 (by rfl) ⟨171738, by rfl⟩ : syracuseStep 457969 = 343477) (by norm_num)
theorem B1637653 : Blo 358757 1637653 := bbase (se 6 (by rfl) ⟨38382, by rfl⟩ : syracuseStep 1637653 = 76765) (by norm_num)
theorem B458065 : Blo 358757 458065 := bbase (se 2 (by rfl) ⟨171774, by rfl⟩ : syracuseStep 458065 = 343549) (by norm_num)
theorem B1834325 : Blo 358757 1834325 := bbase (se 11 (by rfl) ⟨1343, by rfl⟩ : syracuseStep 1834325 = 2687) (by norm_num)
theorem B916829 : Blo 358757 916829 := bbase (se 3 (by rfl) ⟨171905, by rfl⟩ : syracuseStep 916829 = 343811) (by norm_num)
theorem B1211813 : Blo 358757 1211813 := bbase (se 4 (by rfl) ⟨113607, by rfl⟩ : syracuseStep 1211813 = 227215) (by norm_num)
theorem B458237 : Blo 358757 458237 := bbase (se 3 (by rfl) ⟨85919, by rfl⟩ : syracuseStep 458237 = 171839) (by norm_num)
theorem B687629 : Blo 358757 687629 := bbase (se 3 (by rfl) ⟨128930, by rfl⟩ : syracuseStep 687629 = 257861) (by norm_num)
theorem B917021 : Blo 358757 917021 := bbase (se 3 (by rfl) ⟨171941, by rfl⟩ : syracuseStep 917021 = 343883) (by norm_num)
theorem B2588213 : Blo 358757 2588213 := bbase (se 5 (by rfl) ⟨121322, by rfl⟩ : syracuseStep 2588213 = 242645) (by norm_num)
theorem B458293 : Blo 358757 458293 := bbase (se 5 (by rfl) ⟨21482, by rfl⟩ : syracuseStep 458293 = 42965) (by norm_num)
theorem B458389 : Blo 358757 458389 := bbase (se 6 (by rfl) ⟨10743, by rfl⟩ : syracuseStep 458389 = 21487) (by norm_num)
theorem B687781 : Blo 358757 687781 := bbase (se 4 (by rfl) ⟨64479, by rfl⟩ : syracuseStep 687781 = 128959) (by norm_num)
theorem B1375973 : Blo 358757 1375973 := bbase (se 4 (by rfl) ⟨128997, by rfl⟩ : syracuseStep 1375973 = 257995) (by norm_num)
theorem B2817845 : Blo 358757 2817845 := bbase (se 5 (by rfl) ⟨132086, by rfl⟩ : syracuseStep 2817845 = 264173) (by norm_num)
theorem B458561 : Blo 358757 458561 := bbase (se 2 (by rfl) ⟨171960, by rfl⟩ : syracuseStep 458561 = 343921) (by norm_num)
theorem B1212245 : Blo 358757 1212245 := bbase (se 9 (by rfl) ⟨3551, by rfl⟩ : syracuseStep 1212245 = 7103) (by norm_num)
theorem B917365 : Blo 358757 917365 := bbase (se 5 (by rfl) ⟨43001, by rfl⟩ : syracuseStep 917365 = 86003) (by norm_num)
theorem B458617 : Blo 358757 458617 := bbase (se 2 (by rfl) ⟨171981, by rfl⟩ : syracuseStep 458617 = 343963) (by norm_num)
theorem B688085 : Blo 358757 688085 := bbase (se 7 (by rfl) ⟨8063, by rfl⟩ : syracuseStep 688085 = 16127) (by norm_num)
theorem B458713 : Blo 358757 458713 := bbase (se 2 (by rfl) ⟨172017, by rfl⟩ : syracuseStep 458713 = 344035) (by norm_num)
theorem B917477 : Blo 358757 917477 := bbase (se 4 (by rfl) ⟨86013, by rfl⟩ : syracuseStep 917477 = 172027) (by norm_num)
theorem B557057 : Blo 358757 557057 := bstep (se 2 (by rfl) ⟨208896, by rfl⟩ : syracuseStep 557057 = 417793) B417793
theorem B360451 : Blo 358757 360451 := bstep (se 1 (by rfl) ⟨270338, by rfl⟩ : syracuseStep 360451 = 540677) B540677
theorem B917507 : Blo 358757 917507 := bstep (se 1 (by rfl) ⟨688130, by rfl⟩ : syracuseStep 917507 = 1376261) B1376261
theorem B360467 : Blo 358757 360467 := bstep (se 1 (by rfl) ⟨270350, by rfl⟩ : syracuseStep 360467 = 540701) B540701
theorem B360483 : Blo 358757 360483 := bstep (se 1 (by rfl) ⟨270362, by rfl⟩ : syracuseStep 360483 = 540725) B540725
theorem B1376291 : Blo 358757 1376291 := bstep (se 1 (by rfl) ⟨1032218, by rfl⟩ : syracuseStep 1376291 = 2064437) B2064437
theorem B1212461 : Blo 358757 1212461 := bstep (se 3 (by rfl) ⟨227336, by rfl⟩ : syracuseStep 1212461 = 454673) B454673
theorem B360499 : Blo 358757 360499 := bstep (se 1 (by rfl) ⟨270374, by rfl⟩ : syracuseStep 360499 = 540749) B540749
theorem B360515 : Blo 358757 360515 := bstep (se 1 (by rfl) ⟨270386, by rfl⟩ : syracuseStep 360515 = 540773) B540773
theorem B360531 : Blo 358757 360531 := bstep (se 1 (by rfl) ⟨270398, by rfl⟩ : syracuseStep 360531 = 540797) B540797
theorem B1212515 : Blo 358757 1212515 := bstep (se 1 (by rfl) ⟨909386, by rfl⟩ : syracuseStep 1212515 = 1818773) B1818773
theorem B360547 : Blo 358757 360547 := bstep (se 1 (by rfl) ⟨270410, by rfl⟩ : syracuseStep 360547 = 540821) B540821
theorem B1310833 : Blo 358757 1310833 := bstep (se 2 (by rfl) ⟨491562, by rfl⟩ : syracuseStep 1310833 = 983125) B983125
theorem B4915313 : Blo 358757 4915313 := bstep (se 2 (by rfl) ⟨1843242, by rfl⟩ : syracuseStep 4915313 = 3686485) B3686485
theorem B360563 : Blo 358757 360563 := bstep (se 1 (by rfl) ⟨270422, by rfl⟩ : syracuseStep 360563 = 540845) B540845
theorem B360579 : Blo 358757 360579 := bstep (se 1 (by rfl) ⟨270434, by rfl⟩ : syracuseStep 360579 = 540869) B540869
theorem B360595 : Blo 358757 360595 := bstep (se 1 (by rfl) ⟨270446, by rfl⟩ : syracuseStep 360595 = 540893) B540893
theorem B360611 : Blo 358757 360611 := bstep (se 1 (by rfl) ⟨270458, by rfl⟩ : syracuseStep 360611 = 540917) B540917
theorem B360627 : Blo 358757 360627 := bstep (se 1 (by rfl) ⟨270470, by rfl⟩ : syracuseStep 360627 = 540941) B540941
theorem B360643 : Blo 358757 360643 := bstep (se 1 (by rfl) ⟨270482, by rfl⟩ : syracuseStep 360643 = 540965) B540965
theorem B3080389 : Blo 358757 3080389 := bstep (se 4 (by rfl) ⟨288786, by rfl⟩ : syracuseStep 3080389 = 577573) B577573
theorem B360659 : Blo 358757 360659 := bstep (se 1 (by rfl) ⟨270494, by rfl⟩ : syracuseStep 360659 = 540989) B540989
theorem B360675 : Blo 358757 360675 := bstep (se 1 (by rfl) ⟨270506, by rfl⟩ : syracuseStep 360675 = 541013) B541013
theorem B360691 : Blo 358757 360691 := bstep (se 1 (by rfl) ⟨270518, by rfl⟩ : syracuseStep 360691 = 541037) B541037
theorem B360707 : Blo 358757 360707 := bstep (se 1 (by rfl) ⟨270530, by rfl⟩ : syracuseStep 360707 = 541061) B541061
theorem B360723 : Blo 358757 360723 := bstep (se 1 (by rfl) ⟨270542, by rfl⟩ : syracuseStep 360723 = 541085) B541085
theorem B360739 : Blo 358757 360739 := bstep (se 1 (by rfl) ⟨270554, by rfl⟩ : syracuseStep 360739 = 541109) B541109
theorem B2064689 : Blo 358757 2064689 := bstep (se 2 (by rfl) ⟨774258, by rfl⟩ : syracuseStep 2064689 = 1548517) B1548517
theorem B360755 : Blo 358757 360755 := bstep (se 1 (by rfl) ⟨270566, by rfl⟩ : syracuseStep 360755 = 541133) B541133
theorem B360771 : Blo 358757 360771 := bstep (se 1 (by rfl) ⟨270578, by rfl⟩ : syracuseStep 360771 = 541157) B541157
theorem B360787 : Blo 358757 360787 := bstep (se 1 (by rfl) ⟨270590, by rfl⟩ : syracuseStep 360787 = 541181) B541181
theorem B360803 : Blo 358757 360803 := bstep (se 1 (by rfl) ⟨270602, by rfl⟩ : syracuseStep 360803 = 541205) B541205
theorem B1212785 : Blo 358757 1212785 := bstep (se 2 (by rfl) ⟨454794, by rfl⟩ : syracuseStep 1212785 = 909589) B909589
theorem B360819 : Blo 358757 360819 := bstep (se 1 (by rfl) ⟨270614, by rfl⟩ : syracuseStep 360819 = 541229) B541229
theorem B360835 : Blo 358757 360835 := bstep (se 1 (by rfl) ⟨270626, by rfl⟩ : syracuseStep 360835 = 541253) B541253
theorem B360851 : Blo 358757 360851 := bstep (se 1 (by rfl) ⟨270638, by rfl⟩ : syracuseStep 360851 = 541277) B541277
theorem B360867 : Blo 358757 360867 := bstep (se 1 (by rfl) ⟨270650, by rfl⟩ : syracuseStep 360867 = 541301) B541301
theorem B360883 : Blo 358757 360883 := bstep (se 1 (by rfl) ⟨270662, by rfl⟩ : syracuseStep 360883 = 541325) B541325
theorem B360899 : Blo 358757 360899 := bstep (se 1 (by rfl) ⟨270674, by rfl⟩ : syracuseStep 360899 = 541349) B541349
theorem B360915 : Blo 358757 360915 := bstep (se 1 (by rfl) ⟨270686, by rfl⟩ : syracuseStep 360915 = 541373) B541373
theorem B360931 : Blo 358757 360931 := bstep (se 1 (by rfl) ⟨270698, by rfl⟩ : syracuseStep 360931 = 541397) B541397
theorem B360947 : Blo 358757 360947 := bstep (se 1 (by rfl) ⟨270710, by rfl⟩ : syracuseStep 360947 = 541421) B541421
theorem B360963 : Blo 358757 360963 := bstep (se 1 (by rfl) ⟨270722, by rfl⟩ : syracuseStep 360963 = 541445) B541445
theorem B360979 : Blo 358757 360979 := bstep (se 1 (by rfl) ⟨270734, by rfl⟩ : syracuseStep 360979 = 541469) B541469
theorem B360995 : Blo 358757 360995 := bstep (se 1 (by rfl) ⟨270746, by rfl⟩ : syracuseStep 360995 = 541493) B541493
theorem B361011 : Blo 358757 361011 := bstep (se 1 (by rfl) ⟨270758, by rfl⟩ : syracuseStep 361011 = 541517) B541517
theorem B361027 : Blo 358757 361027 := bstep (se 1 (by rfl) ⟨270770, by rfl⟩ : syracuseStep 361027 = 541541) B541541
theorem B361043 : Blo 358757 361043 := bstep (se 1 (by rfl) ⟨270782, by rfl⟩ : syracuseStep 361043 = 541565) B541565
theorem B361059 : Blo 358757 361059 := bstep (se 1 (by rfl) ⟨270794, by rfl⟩ : syracuseStep 361059 = 541589) B541589
theorem B361075 : Blo 358757 361075 := bstep (se 1 (by rfl) ⟨270806, by rfl⟩ : syracuseStep 361075 = 541613) B541613
theorem B361091 : Blo 358757 361091 := bstep (se 1 (by rfl) ⟨270818, by rfl⟩ : syracuseStep 361091 = 541637) B541637
theorem B361107 : Blo 358757 361107 := bstep (se 1 (by rfl) ⟨270830, by rfl⟩ : syracuseStep 361107 = 541661) B541661
theorem B361123 : Blo 358757 361123 := bstep (se 1 (by rfl) ⟨270842, by rfl⟩ : syracuseStep 361123 = 541685) B541685
theorem B1376945 : Blo 358757 1376945 := bstep (se 2 (by rfl) ⟨516354, by rfl⟩ : syracuseStep 1376945 = 1032709) B1032709
theorem B361139 : Blo 358757 361139 := bstep (se 1 (by rfl) ⟨270854, by rfl⟩ : syracuseStep 361139 = 541709) B541709
theorem B361155 : Blo 358757 361155 := bstep (se 1 (by rfl) ⟨270866, by rfl⟩ : syracuseStep 361155 = 541733) B541733
theorem B361171 : Blo 358757 361171 := bstep (se 1 (by rfl) ⟨270878, by rfl⟩ : syracuseStep 361171 = 541757) B541757
theorem B361187 : Blo 358757 361187 := bstep (se 1 (by rfl) ⟨270890, by rfl⟩ : syracuseStep 361187 = 541781) B541781
theorem B361203 : Blo 358757 361203 := bstep (se 1 (by rfl) ⟨270902, by rfl⟩ : syracuseStep 361203 = 541805) B541805
theorem B361219 : Blo 358757 361219 := bstep (se 1 (by rfl) ⟨270914, by rfl⟩ : syracuseStep 361219 = 541829) B541829
theorem B361235 : Blo 358757 361235 := bstep (se 1 (by rfl) ⟨270926, by rfl⟩ : syracuseStep 361235 = 541853) B541853
theorem B361251 : Blo 358757 361251 := bstep (se 1 (by rfl) ⟨270938, by rfl⟩ : syracuseStep 361251 = 541877) B541877
theorem B361267 : Blo 358757 361267 := bstep (se 1 (by rfl) ⟨270950, by rfl⟩ : syracuseStep 361267 = 541901) B541901
theorem B361283 : Blo 358757 361283 := bstep (se 1 (by rfl) ⟨270962, by rfl⟩ : syracuseStep 361283 = 541925) B541925
theorem B361299 : Blo 358757 361299 := bstep (se 1 (by rfl) ⟨270974, by rfl⟩ : syracuseStep 361299 = 541949) B541949
theorem B361315 : Blo 358757 361315 := bstep (se 1 (by rfl) ⟨270986, by rfl⟩ : syracuseStep 361315 = 541973) B541973
theorem B2786147 : Blo 358757 2786147 := bstep (se 1 (by rfl) ⟨2089610, by rfl⟩ : syracuseStep 2786147 = 4179221) B4179221
theorem B361331 : Blo 358757 361331 := bstep (se 1 (by rfl) ⟨270998, by rfl⟩ : syracuseStep 361331 = 541997) B541997
theorem B361347 : Blo 358757 361347 := bstep (se 1 (by rfl) ⟨271010, by rfl⟩ : syracuseStep 361347 = 542021) B542021
theorem B1213325 : Blo 358757 1213325 := bstep (se 3 (by rfl) ⟨227498, by rfl⟩ : syracuseStep 1213325 = 454997) B454997
theorem B361363 : Blo 358757 361363 := bstep (se 1 (by rfl) ⟨271022, by rfl⟩ : syracuseStep 361363 = 542045) B542045
theorem B361379 : Blo 358757 361379 := bstep (se 1 (by rfl) ⟨271034, by rfl⟩ : syracuseStep 361379 = 542069) B542069
theorem B361395 : Blo 358757 361395 := bstep (se 1 (by rfl) ⟨271046, by rfl⟩ : syracuseStep 361395 = 542093) B542093
theorem B1213379 : Blo 358757 1213379 := bstep (se 1 (by rfl) ⟨910034, by rfl⟩ : syracuseStep 1213379 = 1820069) B1820069
theorem B361411 : Blo 358757 361411 := bstep (se 1 (by rfl) ⟨271058, by rfl⟩ : syracuseStep 361411 = 542117) B542117
theorem B361427 : Blo 358757 361427 := bstep (se 1 (by rfl) ⟨271070, by rfl⟩ : syracuseStep 361427 = 542141) B542141
theorem B361443 : Blo 358757 361443 := bstep (se 1 (by rfl) ⟨271082, by rfl⟩ : syracuseStep 361443 = 542165) B542165
theorem B361459 : Blo 358757 361459 := bstep (se 1 (by rfl) ⟨271094, by rfl⟩ : syracuseStep 361459 = 542189) B542189
theorem B361475 : Blo 358757 361475 := bstep (se 1 (by rfl) ⟨271106, by rfl⟩ : syracuseStep 361475 = 542213) B542213
theorem B361491 : Blo 358757 361491 := bstep (se 1 (by rfl) ⟨271118, by rfl⟩ : syracuseStep 361491 = 542237) B542237
theorem B361507 : Blo 358757 361507 := bstep (se 1 (by rfl) ⟨271130, by rfl⟩ : syracuseStep 361507 = 542261) B542261
theorem B361523 : Blo 358757 361523 := bstep (se 1 (by rfl) ⟨271142, by rfl⟩ : syracuseStep 361523 = 542285) B542285
theorem B361539 : Blo 358757 361539 := bstep (se 1 (by rfl) ⟨271154, by rfl⟩ : syracuseStep 361539 = 542309) B542309
theorem B361555 : Blo 358757 361555 := bstep (se 1 (by rfl) ⟨271166, by rfl⟩ : syracuseStep 361555 = 542333) B542333
theorem B361571 : Blo 358757 361571 := bstep (se 1 (by rfl) ⟨271178, by rfl⟩ : syracuseStep 361571 = 542357) B542357
theorem B361587 : Blo 358757 361587 := bstep (se 1 (by rfl) ⟨271190, by rfl⟩ : syracuseStep 361587 = 542381) B542381
theorem B361603 : Blo 358757 361603 := bstep (se 1 (by rfl) ⟨271202, by rfl⟩ : syracuseStep 361603 = 542405) B542405
theorem B361619 : Blo 358757 361619 := bstep (se 1 (by rfl) ⟨271214, by rfl⟩ : syracuseStep 361619 = 542429) B542429
theorem B361635 : Blo 358757 361635 := bstep (se 1 (by rfl) ⟨271226, by rfl⟩ : syracuseStep 361635 = 542453) B542453
theorem B1246385 : Blo 358757 1246385 := bstep (se 2 (by rfl) ⟨467394, by rfl⟩ : syracuseStep 1246385 = 934789) B934789
theorem B361651 : Blo 358757 361651 := bstep (se 1 (by rfl) ⟨271238, by rfl⟩ : syracuseStep 361651 = 542477) B542477
theorem B361667 : Blo 358757 361667 := bstep (se 1 (by rfl) ⟨271250, by rfl⟩ : syracuseStep 361667 = 542501) B542501
theorem B1213649 : Blo 358757 1213649 := bstep (se 2 (by rfl) ⟨455118, by rfl⟩ : syracuseStep 1213649 = 910237) B910237
theorem B820433 : Blo 358757 820433 := bstep (se 2 (by rfl) ⟨307662, by rfl⟩ : syracuseStep 820433 = 615325) B615325
theorem B361683 : Blo 358757 361683 := bstep (se 1 (by rfl) ⟨271262, by rfl⟩ : syracuseStep 361683 = 542525) B542525
theorem B361699 : Blo 358757 361699 := bstep (se 1 (by rfl) ⟨271274, by rfl⟩ : syracuseStep 361699 = 542549) B542549
theorem B361715 : Blo 358757 361715 := bstep (se 1 (by rfl) ⟨271286, by rfl⟩ : syracuseStep 361715 = 542573) B542573
theorem B361731 : Blo 358757 361731 := bstep (se 1 (by rfl) ⟨271298, by rfl⟩ : syracuseStep 361731 = 542597) B542597
theorem B361747 : Blo 358757 361747 := bstep (se 1 (by rfl) ⟨271310, by rfl⟩ : syracuseStep 361747 = 542621) B542621
theorem B361763 : Blo 358757 361763 := bstep (se 1 (by rfl) ⟨271322, by rfl⟩ : syracuseStep 361763 = 542645) B542645
theorem B1541425 : Blo 358757 1541425 := bstep (se 2 (by rfl) ⟨578034, by rfl⟩ : syracuseStep 1541425 = 1156069) B1156069
theorem B361779 : Blo 358757 361779 := bstep (se 1 (by rfl) ⟨271334, by rfl⟩ : syracuseStep 361779 = 542669) B542669
theorem B5276981 : Blo 358757 5276981 := bstep (se 5 (by rfl) ⟨247358, by rfl⟩ : syracuseStep 5276981 = 494717) B494717
theorem B361795 : Blo 358757 361795 := bstep (se 1 (by rfl) ⟨271346, by rfl⟩ : syracuseStep 361795 = 542693) B542693
theorem B361811 : Blo 358757 361811 := bstep (se 1 (by rfl) ⟨271358, by rfl⟩ : syracuseStep 361811 = 542717) B542717
theorem B361827 : Blo 358757 361827 := bstep (se 1 (by rfl) ⟨271370, by rfl⟩ : syracuseStep 361827 = 542741) B542741
theorem B361843 : Blo 358757 361843 := bstep (se 1 (by rfl) ⟨271382, by rfl⟩ : syracuseStep 361843 = 542765) B542765
theorem B361859 : Blo 358757 361859 := bstep (se 1 (by rfl) ⟨271394, by rfl⟩ : syracuseStep 361859 = 542789) B542789
theorem B361875 : Blo 358757 361875 := bstep (se 1 (by rfl) ⟨271406, by rfl⟩ : syracuseStep 361875 = 542813) B542813
theorem B361891 : Blo 358757 361891 := bstep (se 1 (by rfl) ⟨271418, by rfl⟩ : syracuseStep 361891 = 542837) B542837
theorem B361907 : Blo 358757 361907 := bstep (se 1 (by rfl) ⟨271430, by rfl⟩ : syracuseStep 361907 = 542861) B542861
theorem B361923 : Blo 358757 361923 := bstep (se 1 (by rfl) ⟨271442, by rfl⟩ : syracuseStep 361923 = 542885) B542885
theorem B361939 : Blo 358757 361939 := bstep (se 1 (by rfl) ⟨271454, by rfl⟩ : syracuseStep 361939 = 542909) B542909
theorem B361955 : Blo 358757 361955 := bstep (se 1 (by rfl) ⟨271466, by rfl⟩ : syracuseStep 361955 = 542933) B542933
theorem B1050097 : Blo 358757 1050097 := bstep (se 2 (by rfl) ⟨393786, by rfl⟩ : syracuseStep 1050097 = 787573) B787573
theorem B361971 : Blo 358757 361971 := bstep (se 1 (by rfl) ⟨271478, by rfl⟩ : syracuseStep 361971 = 542957) B542957
theorem B361987 : Blo 358757 361987 := bstep (se 1 (by rfl) ⟨271490, by rfl⟩ : syracuseStep 361987 = 542981) B542981
theorem B362003 : Blo 358757 362003 := bstep (se 1 (by rfl) ⟨271502, by rfl⟩ : syracuseStep 362003 = 543005) B543005
theorem B362019 : Blo 358757 362019 := bstep (se 1 (by rfl) ⟨271514, by rfl⟩ : syracuseStep 362019 = 543029) B543029
theorem B362035 : Blo 358757 362035 := bstep (se 1 (by rfl) ⟨271526, by rfl⟩ : syracuseStep 362035 = 543053) B543053
theorem B362051 : Blo 358757 362051 := bstep (se 1 (by rfl) ⟨271538, by rfl⟩ : syracuseStep 362051 = 543077) B543077
theorem B362067 : Blo 358757 362067 := bstep (se 1 (by rfl) ⟨271550, by rfl⟩ : syracuseStep 362067 = 543101) B543101
theorem B362083 : Blo 358757 362083 := bstep (se 1 (by rfl) ⟨271562, by rfl⟩ : syracuseStep 362083 = 543125) B543125
theorem B2754161 : Blo 358757 2754161 := bstep (se 2 (by rfl) ⟨1032810, by rfl⟩ : syracuseStep 2754161 = 2065621) B2065621
theorem B362099 : Blo 358757 362099 := bstep (se 1 (by rfl) ⟨271574, by rfl⟩ : syracuseStep 362099 = 543149) B543149
theorem B362115 : Blo 358757 362115 := bstep (se 1 (by rfl) ⟨271586, by rfl⟩ : syracuseStep 362115 = 543173) B543173
theorem B362131 : Blo 358757 362131 := bstep (se 1 (by rfl) ⟨271598, by rfl⟩ : syracuseStep 362131 = 543197) B543197
theorem B362147 : Blo 358757 362147 := bstep (se 1 (by rfl) ⟨271610, by rfl⟩ : syracuseStep 362147 = 543221) B543221
theorem B362163 : Blo 358757 362163 := bstep (se 1 (by rfl) ⟨271622, by rfl⟩ : syracuseStep 362163 = 543245) B543245
theorem B362179 : Blo 358757 362179 := bstep (se 1 (by rfl) ⟨271634, by rfl⟩ : syracuseStep 362179 = 543269) B543269
theorem B4622021 : Blo 358757 4622021 := bstep (se 4 (by rfl) ⟨433314, by rfl⟩ : syracuseStep 4622021 = 866629) B866629
theorem B362195 : Blo 358757 362195 := bstep (se 1 (by rfl) ⟨271646, by rfl⟩ : syracuseStep 362195 = 543293) B543293
theorem B362211 : Blo 358757 362211 := bstep (se 1 (by rfl) ⟨271658, by rfl⟩ : syracuseStep 362211 = 543317) B543317
theorem B1214189 : Blo 358757 1214189 := bstep (se 3 (by rfl) ⟨227660, by rfl⟩ : syracuseStep 1214189 = 455321) B455321
theorem B362227 : Blo 358757 362227 := bstep (se 1 (by rfl) ⟨271670, by rfl⟩ : syracuseStep 362227 = 543341) B543341
theorem B362243 : Blo 358757 362243 := bstep (se 1 (by rfl) ⟨271682, by rfl⟩ : syracuseStep 362243 = 543365) B543365
theorem B362259 : Blo 358757 362259 := bstep (se 1 (by rfl) ⟨271694, by rfl⟩ : syracuseStep 362259 = 543389) B543389
theorem B558881 : Blo 358757 558881 := bstep (se 2 (by rfl) ⟨209580, by rfl⟩ : syracuseStep 558881 = 419161) B419161
theorem B1214243 : Blo 358757 1214243 := bstep (se 1 (by rfl) ⟨910682, by rfl⟩ : syracuseStep 1214243 = 1821365) B1821365
theorem B362275 : Blo 358757 362275 := bstep (se 1 (by rfl) ⟨271706, by rfl⟩ : syracuseStep 362275 = 543413) B543413
theorem B362291 : Blo 358757 362291 := bstep (se 1 (by rfl) ⟨271718, by rfl⟩ : syracuseStep 362291 = 543437) B543437
theorem B5539637 : Blo 358757 5539637 := bstep (se 5 (by rfl) ⟨259670, by rfl⟩ : syracuseStep 5539637 = 519341) B519341
theorem B362307 : Blo 358757 362307 := bstep (se 1 (by rfl) ⟨271730, by rfl⟩ : syracuseStep 362307 = 543461) B543461
theorem B362323 : Blo 358757 362323 := bstep (se 1 (by rfl) ⟨271742, by rfl⟩ : syracuseStep 362323 = 543485) B543485
theorem B362339 : Blo 358757 362339 := bstep (se 1 (by rfl) ⟨271754, by rfl⟩ : syracuseStep 362339 = 543509) B543509
theorem B362355 : Blo 358757 362355 := bstep (se 1 (by rfl) ⟨271766, by rfl⟩ : syracuseStep 362355 = 543533) B543533
theorem B362371 : Blo 358757 362371 := bstep (se 1 (by rfl) ⟨271778, by rfl⟩ : syracuseStep 362371 = 543557) B543557
theorem B362387 : Blo 358757 362387 := bstep (se 1 (by rfl) ⟨271790, by rfl⟩ : syracuseStep 362387 = 543581) B543581
theorem B362403 : Blo 358757 362403 := bstep (se 1 (by rfl) ⟨271802, by rfl⟩ : syracuseStep 362403 = 543605) B543605
theorem B362419 : Blo 358757 362419 := bstep (se 1 (by rfl) ⟨271814, by rfl⟩ : syracuseStep 362419 = 543629) B543629
theorem B362435 : Blo 358757 362435 := bstep (se 1 (by rfl) ⟨271826, by rfl⟩ : syracuseStep 362435 = 543653) B543653
theorem B11241413 : Blo 358757 11241413 := bstep (se 4 (by rfl) ⟨1053882, by rfl⟩ : syracuseStep 11241413 = 2107765) B2107765
theorem B362451 : Blo 358757 362451 := bstep (se 1 (by rfl) ⟨271838, by rfl⟩ : syracuseStep 362451 = 543677) B543677
theorem B362467 : Blo 358757 362467 := bstep (se 1 (by rfl) ⟨271850, by rfl⟩ : syracuseStep 362467 = 543701) B543701
theorem B362483 : Blo 358757 362483 := bstep (se 1 (by rfl) ⟨271862, by rfl⟩ : syracuseStep 362483 = 543725) B543725
theorem B362499 : Blo 358757 362499 := bstep (se 1 (by rfl) ⟨271874, by rfl⟩ : syracuseStep 362499 = 543749) B543749
theorem B985105 : Blo 358757 985105 := bstep (se 2 (by rfl) ⟨369414, by rfl⟩ : syracuseStep 985105 = 738829) B738829
theorem B362515 : Blo 358757 362515 := bstep (se 1 (by rfl) ⟨271886, by rfl⟩ : syracuseStep 362515 = 543773) B543773
theorem B362531 : Blo 358757 362531 := bstep (se 1 (by rfl) ⟨271898, by rfl⟩ : syracuseStep 362531 = 543797) B543797
theorem B1214513 : Blo 358757 1214513 := bstep (se 2 (by rfl) ⟨455442, by rfl⟩ : syracuseStep 1214513 = 910885) B910885
theorem B362547 : Blo 358757 362547 := bstep (se 1 (by rfl) ⟨271910, by rfl⟩ : syracuseStep 362547 = 543821) B543821
theorem B362563 : Blo 358757 362563 := bstep (se 1 (by rfl) ⟨271922, by rfl⟩ : syracuseStep 362563 = 543845) B543845
theorem B362579 : Blo 358757 362579 := bstep (se 1 (by rfl) ⟨271934, by rfl⟩ : syracuseStep 362579 = 543869) B543869
theorem B362595 : Blo 358757 362595 := bstep (se 1 (by rfl) ⟨271946, by rfl⟩ : syracuseStep 362595 = 543893) B543893
theorem B362611 : Blo 358757 362611 := bstep (se 1 (by rfl) ⟨271958, by rfl⟩ : syracuseStep 362611 = 543917) B543917
theorem B362627 : Blo 358757 362627 := bstep (se 1 (by rfl) ⟨271970, by rfl⟩ : syracuseStep 362627 = 543941) B543941
theorem B362643 : Blo 358757 362643 := bstep (se 1 (by rfl) ⟨271982, by rfl⟩ : syracuseStep 362643 = 543965) B543965
theorem B362659 : Blo 358757 362659 := bstep (se 1 (by rfl) ⟨271994, by rfl⟩ : syracuseStep 362659 = 543989) B543989
theorem B362675 : Blo 358757 362675 := bstep (se 1 (by rfl) ⟨272006, by rfl⟩ : syracuseStep 362675 = 544013) B544013
theorem B362691 : Blo 358757 362691 := bstep (se 1 (by rfl) ⟨272018, by rfl⟩ : syracuseStep 362691 = 544037) B544037
theorem B362707 : Blo 358757 362707 := bstep (se 1 (by rfl) ⟨272030, by rfl⟩ : syracuseStep 362707 = 544061) B544061
theorem B362723 : Blo 358757 362723 := bstep (se 1 (by rfl) ⟨272042, by rfl⟩ : syracuseStep 362723 = 544085) B544085
theorem B362739 : Blo 358757 362739 := bstep (se 1 (by rfl) ⟨272054, by rfl⟩ : syracuseStep 362739 = 544109) B544109
theorem B362755 : Blo 358757 362755 := bstep (se 1 (by rfl) ⟨272066, by rfl⟩ : syracuseStep 362755 = 544133) B544133
theorem B1149329 : Blo 358757 1149329 := bstep (se 2 (by rfl) ⟨430998, by rfl⟩ : syracuseStep 1149329 = 861997) B861997
theorem B1215053 : Blo 358757 1215053 := bstep (se 3 (by rfl) ⟨227822, by rfl⟩ : syracuseStep 1215053 = 455645) B455645
theorem B1215107 : Blo 358757 1215107 := bstep (se 1 (by rfl) ⟨911330, by rfl⟩ : syracuseStep 1215107 = 1822661) B1822661
theorem B1215377 : Blo 358757 1215377 := bstep (se 2 (by rfl) ⟨455766, by rfl⟩ : syracuseStep 1215377 = 911533) B911533
theorem B494723 : Blo 358757 494723 := bstep (se 1 (by rfl) ⟨371042, by rfl⟩ : syracuseStep 494723 = 742085) B742085
theorem B691363 : Blo 358757 691363 := bstep (se 1 (by rfl) ⟨518522, by rfl⟩ : syracuseStep 691363 = 1037045) B1037045
theorem B691409 : Blo 358757 691409 := bstep (se 2 (by rfl) ⟨259278, by rfl⟩ : syracuseStep 691409 = 518557) B518557
theorem B1215917 : Blo 358757 1215917 := bstep (se 3 (by rfl) ⟨227984, by rfl⟩ : syracuseStep 1215917 = 455969) B455969
theorem B1215971 : Blo 358757 1215971 := bstep (se 1 (by rfl) ⟨911978, by rfl⟩ : syracuseStep 1215971 = 1823957) B1823957
theorem B1216241 : Blo 358757 1216241 := bstep (se 2 (by rfl) ⟨456090, by rfl⟩ : syracuseStep 1216241 = 912181) B912181
theorem B2920333 : Blo 358757 2920333 := bstep (se 3 (by rfl) ⟨547562, by rfl⟩ : syracuseStep 2920333 = 1095125) B1095125
theorem B1216781 : Blo 358757 1216781 := bstep (se 3 (by rfl) ⟨228146, by rfl⟩ : syracuseStep 1216781 = 456293) B456293
theorem B1216835 : Blo 358757 1216835 := bstep (se 1 (by rfl) ⟨912626, by rfl⟩ : syracuseStep 1216835 = 1825253) B1825253
theorem B856433 : Blo 358757 856433 := bstep (se 2 (by rfl) ⟨321162, by rfl⟩ : syracuseStep 856433 = 642325) B642325
theorem B1151405 : Blo 358757 1151405 := bstep (se 3 (by rfl) ⟨215888, by rfl⟩ : syracuseStep 1151405 = 431777) B431777
theorem B1217105 : Blo 358757 1217105 := bstep (se 2 (by rfl) ⟨456414, by rfl⟩ : syracuseStep 1217105 = 912829) B912829
theorem B1249933 : Blo 358757 1249933 := bstep (se 3 (by rfl) ⟨234362, by rfl⟩ : syracuseStep 1249933 = 468725) B468725
theorem B5083829 : Blo 358757 5083829 := bstep (se 5 (by rfl) ⟨238304, by rfl⟩ : syracuseStep 5083829 = 476609) B476609
theorem B6197957 : Blo 358757 6197957 := bstep (se 4 (by rfl) ⟨581058, by rfl⟩ : syracuseStep 6197957 = 1162117) B1162117
theorem B627521 : Blo 358757 627521 := bstep (se 2 (by rfl) ⟨235320, by rfl⟩ : syracuseStep 627521 = 470641) B470641
theorem B365395 : Blo 358757 365395 := bstep (se 1 (by rfl) ⟨274046, by rfl⟩ : syracuseStep 365395 = 548093) B548093
theorem B1545101 : Blo 358757 1545101 := bstep (se 3 (by rfl) ⟨289706, by rfl⟩ : syracuseStep 1545101 = 579413) B579413
theorem B1217645 : Blo 358757 1217645 := bstep (se 3 (by rfl) ⟨228308, by rfl⟩ : syracuseStep 1217645 = 456617) B456617
theorem B365699 : Blo 358757 365699 := bstep (se 1 (by rfl) ⟨274274, by rfl⟩ : syracuseStep 365699 = 548549) B548549
theorem B1217699 : Blo 358757 1217699 := bstep (se 1 (by rfl) ⟨913274, by rfl⟩ : syracuseStep 1217699 = 1826549) B1826549
theorem B1742029 : Blo 358757 1742029 := bstep (se 3 (by rfl) ⟨326630, by rfl⟩ : syracuseStep 1742029 = 653261) B653261
theorem B12719501 : Blo 358757 12719501 := bstep (se 3 (by rfl) ⟨2384906, by rfl⟩ : syracuseStep 12719501 = 4769813) B4769813
theorem B1217969 : Blo 358757 1217969 := bstep (se 2 (by rfl) ⟨456738, by rfl⟩ : syracuseStep 1217969 = 913477) B913477
theorem B2299427 : Blo 358757 2299427 := bstep (se 1 (by rfl) ⟨1724570, by rfl⟩ : syracuseStep 2299427 = 3449141) B3449141
theorem B2332259 : Blo 358757 2332259 := bstep (se 1 (by rfl) ⟨1749194, by rfl⟩ : syracuseStep 2332259 = 3498389) B3498389
theorem B1742755 : Blo 358757 1742755 := bstep (se 1 (by rfl) ⟨1307066, by rfl⟩ : syracuseStep 1742755 = 2614133) B2614133
theorem B1218509 : Blo 358757 1218509 := bstep (se 3 (by rfl) ⟨228470, by rfl⟩ : syracuseStep 1218509 = 456941) B456941
theorem B366563 : Blo 358757 366563 := bstep (se 1 (by rfl) ⟨274922, by rfl⟩ : syracuseStep 366563 = 549845) B549845
theorem B1218563 : Blo 358757 1218563 := bstep (se 1 (by rfl) ⟨913922, by rfl⟩ : syracuseStep 1218563 = 1827845) B1827845
theorem B1153187 : Blo 358757 1153187 := bstep (se 1 (by rfl) ⟨864890, by rfl⟩ : syracuseStep 1153187 = 1729781) B1729781
theorem B4397237 : Blo 358757 4397237 := bstep (se 5 (by rfl) ⟨206120, by rfl⟩ : syracuseStep 4397237 = 412241) B412241
theorem B1218833 : Blo 358757 1218833 := bstep (se 2 (by rfl) ⟨457062, by rfl⟩ : syracuseStep 1218833 = 914125) B914125
theorem B1644877 : Blo 358757 1644877 := bstep (se 3 (by rfl) ⟨308414, by rfl⟩ : syracuseStep 1644877 = 616829) B616829
theorem B1022321 : Blo 358757 1022321 := bstep (se 2 (by rfl) ⟨383370, by rfl⟩ : syracuseStep 1022321 = 766741) B766741
theorem B989965 : Blo 358757 989965 := bstep (se 3 (by rfl) ⟨185618, by rfl⟩ : syracuseStep 989965 = 371237) B371237
theorem B1219373 : Blo 358757 1219373 := bstep (se 3 (by rfl) ⟨228632, by rfl⟩ : syracuseStep 1219373 = 457265) B457265
theorem B1219427 : Blo 358757 1219427 := bstep (se 1 (by rfl) ⟨914570, by rfl⟩ : syracuseStep 1219427 = 1829141) B1829141
theorem B1022993 : Blo 358757 1022993 := bstep (se 2 (by rfl) ⟨383622, by rfl⟩ : syracuseStep 1022993 = 767245) B767245
theorem B728131 : Blo 358757 728131 := bstep (se 1 (by rfl) ⟨546098, by rfl⟩ : syracuseStep 728131 = 1092197) B1092197
theorem B2530381 : Blo 358757 2530381 := bstep (se 3 (by rfl) ⟨474446, by rfl⟩ : syracuseStep 2530381 = 948893) B948893
theorem B1219697 : Blo 358757 1219697 := bstep (se 2 (by rfl) ⟨457386, by rfl⟩ : syracuseStep 1219697 = 914773) B914773
theorem B2301169 : Blo 358757 2301169 := bstep (se 2 (by rfl) ⟨862938, by rfl⟩ : syracuseStep 2301169 = 1725877) B1725877
theorem B433459 : Blo 358757 433459 := bstep (se 1 (by rfl) ⟨325094, by rfl⟩ : syracuseStep 433459 = 650189) B650189
theorem B433603 : Blo 358757 433603 := bstep (se 1 (by rfl) ⟨325202, by rfl⟩ : syracuseStep 433603 = 650405) B650405
theorem B1154531 : Blo 358757 1154531 := bstep (se 1 (by rfl) ⟨865898, by rfl⟩ : syracuseStep 1154531 = 1731797) B1731797
theorem B1384049 : Blo 358757 1384049 := bstep (se 2 (by rfl) ⟨519018, by rfl⟩ : syracuseStep 1384049 = 1038037) B1038037
theorem B1220237 : Blo 358757 1220237 := bstep (se 3 (by rfl) ⟨228794, by rfl⟩ : syracuseStep 1220237 = 457589) B457589
theorem B1220291 : Blo 358757 1220291 := bstep (se 1 (by rfl) ⟨915218, by rfl⟩ : syracuseStep 1220291 = 1830437) B1830437
theorem B1023779 : Blo 358757 1023779 := bstep (se 1 (by rfl) ⟨767834, by rfl⟩ : syracuseStep 1023779 = 1535669) B1535669
theorem B1220561 : Blo 358757 1220561 := bstep (se 2 (by rfl) ⟨457710, by rfl⟩ : syracuseStep 1220561 = 915421) B915421
theorem B1024109 : Blo 358757 1024109 := bstep (se 3 (by rfl) ⟨192020, by rfl⟩ : syracuseStep 1024109 = 384041) B384041
theorem B729233 : Blo 358757 729233 := bstep (se 2 (by rfl) ⟨273462, by rfl⟩ : syracuseStep 729233 = 546925) B546925
theorem B1024177 : Blo 358757 1024177 := bstep (se 2 (by rfl) ⟨384066, by rfl⟩ : syracuseStep 1024177 = 768133) B768133
theorem B1024451 : Blo 358757 1024451 := bstep (se 1 (by rfl) ⟨768338, by rfl⟩ : syracuseStep 1024451 = 1536677) B1536677
theorem B926147 : Blo 358757 926147 := bstep (se 1 (by rfl) ⟨694610, by rfl⟩ : syracuseStep 926147 = 1389221) B1389221
theorem B1221101 : Blo 358757 1221101 := bstep (se 3 (by rfl) ⟨228956, by rfl⟩ : syracuseStep 1221101 = 457913) B457913
theorem B1221155 : Blo 358757 1221155 := bstep (se 1 (by rfl) ⟨915866, by rfl⟩ : syracuseStep 1221155 = 1831733) B1831733
theorem B369235 : Blo 358757 369235 := bstep (se 1 (by rfl) ⟨276926, by rfl⟩ : syracuseStep 369235 = 553853) B553853
theorem B3089137 : Blo 358757 3089137 := bstep (se 2 (by rfl) ⟨1158426, by rfl⟩ : syracuseStep 3089137 = 2316853) B2316853
theorem B1221425 : Blo 358757 1221425 := bstep (se 2 (by rfl) ⟨458034, by rfl⟩ : syracuseStep 1221425 = 916069) B916069
theorem B730019 : Blo 358757 730019 := bstep (se 1 (by rfl) ⟨547514, by rfl⟩ : syracuseStep 730019 = 1095029) B1095029
theorem B2303117 : Blo 358757 2303117 := bstep (se 3 (by rfl) ⟨431834, by rfl⟩ : syracuseStep 2303117 = 863669) B863669
theorem B1549475 : Blo 358757 1549475 := bstep (se 1 (by rfl) ⟨1162106, by rfl⟩ : syracuseStep 1549475 = 2324213) B2324213
theorem B1156301 : Blo 358757 1156301 := bstep (se 3 (by rfl) ⟨216806, by rfl⟩ : syracuseStep 1156301 = 433613) B433613
theorem B1025293 : Blo 358757 1025293 := bstep (se 3 (by rfl) ⟨192242, by rfl⟩ : syracuseStep 1025293 = 384485) B384485
theorem B7808309 : Blo 358757 7808309 := bstep (se 5 (by rfl) ⟨366014, by rfl⟩ : syracuseStep 7808309 = 732029) B732029
theorem B1221965 : Blo 358757 1221965 := bstep (se 3 (by rfl) ⟨229118, by rfl⟩ : syracuseStep 1221965 = 458237) B458237
theorem B1222019 : Blo 358757 1222019 := bstep (se 1 (by rfl) ⟨916514, by rfl⟩ : syracuseStep 1222019 = 1833029) B1833029
theorem B1025453 : Blo 358757 1025453 := bstep (se 3 (by rfl) ⟨192272, by rfl⟩ : syracuseStep 1025453 = 384545) B384545
theorem B1025635 : Blo 358757 1025635 := bstep (se 1 (by rfl) ⟨769226, by rfl⟩ : syracuseStep 1025635 = 1538453) B1538453
theorem B1222289 : Blo 358757 1222289 := bstep (se 2 (by rfl) ⟨458358, by rfl⟩ : syracuseStep 1222289 = 916717) B916717
theorem B1845233 : Blo 358757 1845233 := bstep (se 2 (by rfl) ⟨691962, by rfl⟩ : syracuseStep 1845233 = 1383925) B1383925
theorem B1222829 : Blo 358757 1222829 := bstep (se 3 (by rfl) ⟨229280, by rfl⟩ : syracuseStep 1222829 = 458561) B458561
theorem B1222883 : Blo 358757 1222883 := bstep (se 1 (by rfl) ⟨917162, by rfl⟩ : syracuseStep 1222883 = 1834325) B1834325
theorem B403699 : Blo 358757 403699 := bstep (se 1 (by rfl) ⟨302774, by rfl⟩ : syracuseStep 403699 = 605549) B605549
theorem B403843 : Blo 358757 403843 := bstep (se 1 (by rfl) ⟨302882, by rfl⟩ : syracuseStep 403843 = 605765) B605765
theorem B1223153 : Blo 358757 1223153 := bstep (se 2 (by rfl) ⟨458682, by rfl⟩ : syracuseStep 1223153 = 917365) B917365
theorem B403987 : Blo 358757 403987 := bstep (se 1 (by rfl) ⟨302990, by rfl⟩ : syracuseStep 403987 = 605981) B605981
theorem B1878563 : Blo 358757 1878563 := bstep (se 1 (by rfl) ⟨1408922, by rfl⟩ : syracuseStep 1878563 = 2817845) B2817845
theorem B404131 : Blo 358757 404131 := bstep (se 1 (by rfl) ⟨303098, by rfl⟩ : syracuseStep 404131 = 606197) B606197
theorem B1092305 : Blo 358757 1092305 := bstep (se 2 (by rfl) ⟨409614, by rfl⟩ : syracuseStep 1092305 = 819229) B819229
theorem B928529 : Blo 358757 928529 := bstep (se 2 (by rfl) ⟨348198, by rfl⟩ : syracuseStep 928529 = 696397) B696397
theorem B404275 : Blo 358757 404275 := bstep (se 1 (by rfl) ⟨303206, by rfl⟩ : syracuseStep 404275 = 606413) B606413
theorem B404419 : Blo 358757 404419 := bstep (se 1 (by rfl) ⟨303314, by rfl⟩ : syracuseStep 404419 = 606629) B606629
theorem B1027025 : Blo 358757 1027025 := bstep (se 2 (by rfl) ⟨385134, by rfl⟩ : syracuseStep 1027025 = 770269) B770269
theorem B1223693 : Blo 358757 1223693 := bstep (se 3 (by rfl) ⟨229442, by rfl⟩ : syracuseStep 1223693 = 458885) B458885
theorem B1223747 : Blo 358757 1223747 := bstep (se 1 (by rfl) ⟨917810, by rfl⟩ : syracuseStep 1223747 = 1835621) B1835621
theorem B2337869 : Blo 358757 2337869 := bstep (se 3 (by rfl) ⟨438350, by rfl⟩ : syracuseStep 2337869 = 876701) B876701
theorem B732241 : Blo 358757 732241 := bstep (se 2 (by rfl) ⟨274590, by rfl⟩ : syracuseStep 732241 = 549181) B549181
theorem B404563 : Blo 358757 404563 := bstep (se 1 (by rfl) ⟨303422, by rfl⟩ : syracuseStep 404563 = 606845) B606845
theorem B3550321 : Blo 358757 3550321 := bstep (se 2 (by rfl) ⟨1331370, by rfl⟩ : syracuseStep 3550321 = 2662741) B2662741
theorem B404707 : Blo 358757 404707 := bstep (se 1 (by rfl) ⟨303530, by rfl⟩ : syracuseStep 404707 = 607061) B607061
theorem B1224017 : Blo 358757 1224017 := bstep (se 2 (by rfl) ⟨459006, by rfl⟩ : syracuseStep 1224017 = 918013) B918013
theorem B1092977 : Blo 358757 1092977 := bstep (se 2 (by rfl) ⟨409866, by rfl⟩ : syracuseStep 1092977 = 819733) B819733
theorem B404851 : Blo 358757 404851 := bstep (se 1 (by rfl) ⟨303638, by rfl⟩ : syracuseStep 404851 = 607277) B607277
theorem B863747 : Blo 358757 863747 := bstep (se 1 (by rfl) ⟨647810, by rfl⟩ : syracuseStep 863747 = 1295621) B1295621
theorem B404995 : Blo 358757 404995 := bstep (se 1 (by rfl) ⟨303746, by rfl⟩ : syracuseStep 404995 = 607493) B607493
theorem B405139 : Blo 358757 405139 := bstep (se 1 (by rfl) ⟨303854, by rfl⟩ : syracuseStep 405139 = 607709) B607709
theorem B2043569 : Blo 358757 2043569 := bstep (se 2 (by rfl) ⟨766338, by rfl⟩ : syracuseStep 2043569 = 1532677) B1532677
theorem B405283 : Blo 358757 405283 := bstep (se 1 (by rfl) ⟨303962, by rfl⟩ : syracuseStep 405283 = 607925) B607925
theorem B1027981 : Blo 358757 1027981 := bstep (se 3 (by rfl) ⟨192746, by rfl⟩ : syracuseStep 1027981 = 385493) B385493
theorem B405427 : Blo 358757 405427 := bstep (se 1 (by rfl) ⟨304070, by rfl⟩ : syracuseStep 405427 = 608141) B608141
theorem B405571 : Blo 358757 405571 := bstep (se 1 (by rfl) ⟨304178, by rfl⟩ : syracuseStep 405571 = 608357) B608357
theorem B1028209 : Blo 358757 1028209 := bstep (se 2 (by rfl) ⟨385578, by rfl⟩ : syracuseStep 1028209 = 771157) B771157
theorem B405715 : Blo 358757 405715 := bstep (se 1 (by rfl) ⟨304286, by rfl⟩ : syracuseStep 405715 = 608573) B608573
theorem B864515 : Blo 358757 864515 := bstep (se 1 (by rfl) ⟨648386, by rfl⟩ : syracuseStep 864515 = 1296773) B1296773
theorem B1028369 : Blo 358757 1028369 := bstep (se 2 (by rfl) ⟨385638, by rfl⟩ : syracuseStep 1028369 = 771277) B771277
theorem B1716515 : Blo 358757 1716515 := bstep (se 1 (by rfl) ⟨1287386, by rfl⟩ : syracuseStep 1716515 = 2574773) B2574773
theorem B733475 : Blo 358757 733475 := bstep (se 1 (by rfl) ⟨550106, by rfl⟩ : syracuseStep 733475 = 1100213) B1100213
theorem B1159505 : Blo 358757 1159505 := bstep (se 2 (by rfl) ⟨434814, by rfl⟩ : syracuseStep 1159505 = 869629) B869629
theorem B4108643 : Blo 358757 4108643 := bstep (se 1 (by rfl) ⟨3081482, by rfl⟩ : syracuseStep 4108643 = 6162965) B6162965
theorem B405859 : Blo 358757 405859 := bstep (se 1 (by rfl) ⟨304394, by rfl⟩ : syracuseStep 405859 = 608789) B608789
theorem B1028483 : Blo 358757 1028483 := bstep (se 1 (by rfl) ⟨771362, by rfl⟩ : syracuseStep 1028483 = 1542725) B1542725
theorem B1159555 : Blo 358757 1159555 := bstep (se 1 (by rfl) ⟨869666, by rfl⟩ : syracuseStep 1159555 = 1739333) B1739333
theorem B2306501 : Blo 358757 2306501 := bstep (se 4 (by rfl) ⟨216234, by rfl⟩ : syracuseStep 2306501 = 432469) B432469
theorem B406003 : Blo 358757 406003 := bstep (se 1 (by rfl) ⟨304502, by rfl⟩ : syracuseStep 406003 = 609005) B609005
theorem B406147 : Blo 358757 406147 := bstep (se 1 (by rfl) ⟨304610, by rfl⟩ : syracuseStep 406147 = 609221) B609221
theorem B3912461 : Blo 358757 3912461 := bstep (se 3 (by rfl) ⟨733586, by rfl⟩ : syracuseStep 3912461 = 1467173) B1467173
theorem B406291 : Blo 358757 406291 := bstep (se 1 (by rfl) ⟨304718, by rfl⟩ : syracuseStep 406291 = 609437) B609437
theorem B865073 : Blo 358757 865073 := bstep (se 2 (by rfl) ⟨324402, by rfl⟩ : syracuseStep 865073 = 648805) B648805
theorem B406435 : Blo 358757 406435 := bstep (se 1 (by rfl) ⟨304826, by rfl⟩ : syracuseStep 406435 = 609653) B609653
theorem B1586161 : Blo 358757 1586161 := bstep (se 2 (by rfl) ⟨594810, by rfl⟩ : syracuseStep 1586161 = 1189621) B1189621
theorem B406579 : Blo 358757 406579 := bstep (se 1 (by rfl) ⟨304934, by rfl⟩ : syracuseStep 406579 = 609869) B609869
theorem B4600901 : Blo 358757 4600901 := bstep (se 4 (by rfl) ⟨431334, by rfl⟩ : syracuseStep 4600901 = 862669) B862669
theorem B2045027 : Blo 358757 2045027 := bstep (se 1 (by rfl) ⟨1533770, by rfl⟩ : syracuseStep 2045027 = 3067541) B3067541
theorem B406723 : Blo 358757 406723 := bstep (se 1 (by rfl) ⟨305042, by rfl⟩ : syracuseStep 406723 = 610085) B610085
theorem B1160401 : Blo 358757 1160401 := bstep (se 2 (by rfl) ⟨435150, by rfl⟩ : syracuseStep 1160401 = 870301) B870301
theorem B406867 : Blo 358757 406867 := bstep (se 1 (by rfl) ⟨305150, by rfl⟩ : syracuseStep 406867 = 610301) B610301
theorem B1029485 : Blo 358757 1029485 := bstep (se 3 (by rfl) ⟨193028, by rfl⟩ : syracuseStep 1029485 = 386057) B386057
theorem B865745 : Blo 358757 865745 := bstep (se 2 (by rfl) ⟨324654, by rfl⟩ : syracuseStep 865745 = 649309) B649309
theorem B407011 : Blo 358757 407011 := bstep (se 1 (by rfl) ⟨305258, by rfl⟩ : syracuseStep 407011 = 610517) B610517
theorem B1947149 : Blo 358757 1947149 := bstep (se 3 (by rfl) ⟨365090, by rfl⟩ : syracuseStep 1947149 = 730181) B730181
theorem B538145 : Blo 358757 538145 := bstep (se 2 (by rfl) ⟨201804, by rfl⟩ : syracuseStep 538145 = 403609) B403609
theorem B1029667 : Blo 358757 1029667 := bstep (se 1 (by rfl) ⟨772250, by rfl⟩ : syracuseStep 1029667 = 1544501) B1544501
theorem B538163 : Blo 358757 538163 := bstep (se 1 (by rfl) ⟨403622, by rfl⟩ : syracuseStep 538163 = 807245) B807245
theorem B538193 : Blo 358757 538193 := bstep (se 2 (by rfl) ⟨201822, by rfl⟩ : syracuseStep 538193 = 403645) B403645
theorem B767569 : Blo 358757 767569 := bstep (se 2 (by rfl) ⟨287838, by rfl⟩ : syracuseStep 767569 = 575677) B575677
theorem B538211 : Blo 358757 538211 := bstep (se 1 (by rfl) ⟨403658, by rfl⟩ : syracuseStep 538211 = 807317) B807317
theorem B407155 : Blo 358757 407155 := bstep (se 1 (by rfl) ⟨305366, by rfl⟩ : syracuseStep 407155 = 610733) B610733
theorem B538241 : Blo 358757 538241 := bstep (se 2 (by rfl) ⟨201840, by rfl⟩ : syracuseStep 538241 = 403681) B403681
theorem B538259 : Blo 358757 538259 := bstep (se 1 (by rfl) ⟨403694, by rfl⟩ : syracuseStep 538259 = 807389) B807389
theorem B538289 : Blo 358757 538289 := bstep (se 2 (by rfl) ⟨201858, by rfl⟩ : syracuseStep 538289 = 403717) B403717
theorem B538307 : Blo 358757 538307 := bstep (se 1 (by rfl) ⟨403730, by rfl⟩ : syracuseStep 538307 = 807461) B807461
theorem B1029827 : Blo 358757 1029827 := bstep (se 1 (by rfl) ⟨772370, by rfl⟩ : syracuseStep 1029827 = 1544741) B1544741
theorem B538337 : Blo 358757 538337 := bstep (se 2 (by rfl) ⟨201876, by rfl⟩ : syracuseStep 538337 = 403753) B403753
theorem B538355 : Blo 358757 538355 := bstep (se 1 (by rfl) ⟨403766, by rfl⟩ : syracuseStep 538355 = 807533) B807533
theorem B407299 : Blo 358757 407299 := bstep (se 1 (by rfl) ⟨305474, by rfl⟩ : syracuseStep 407299 = 610949) B610949
theorem B538385 : Blo 358757 538385 := bstep (se 2 (by rfl) ⟨201894, by rfl⟩ : syracuseStep 538385 = 403789) B403789
theorem B538403 : Blo 358757 538403 := bstep (se 1 (by rfl) ⟨403802, by rfl⟩ : syracuseStep 538403 = 807605) B807605
theorem B538433 : Blo 358757 538433 := bstep (se 2 (by rfl) ⟨201912, by rfl⟩ : syracuseStep 538433 = 403825) B403825
theorem B538451 : Blo 358757 538451 := bstep (se 1 (by rfl) ⟨403838, by rfl⟩ : syracuseStep 538451 = 807677) B807677
theorem B538481 : Blo 358757 538481 := bstep (se 2 (by rfl) ⟨201930, by rfl⟩ : syracuseStep 538481 = 403861) B403861
theorem B538499 : Blo 358757 538499 := bstep (se 1 (by rfl) ⟨403874, by rfl⟩ : syracuseStep 538499 = 807749) B807749
theorem B407443 : Blo 358757 407443 := bstep (se 1 (by rfl) ⟨305582, by rfl⟩ : syracuseStep 407443 = 611165) B611165
theorem B538529 : Blo 358757 538529 := bstep (se 2 (by rfl) ⟨201948, by rfl⟩ : syracuseStep 538529 = 403897) B403897
theorem B538547 : Blo 358757 538547 := bstep (se 1 (by rfl) ⟨403910, by rfl⟩ : syracuseStep 538547 = 807821) B807821
theorem B3094469 : Blo 358757 3094469 := bstep (se 4 (by rfl) ⟨290106, by rfl⟩ : syracuseStep 3094469 = 580213) B580213
theorem B538577 : Blo 358757 538577 := bstep (se 2 (by rfl) ⟨201966, by rfl⟩ : syracuseStep 538577 = 403933) B403933
theorem B538595 : Blo 358757 538595 := bstep (se 1 (by rfl) ⟨403946, by rfl⟩ : syracuseStep 538595 = 807893) B807893
theorem B767971 : Blo 358757 767971 := bstep (se 1 (by rfl) ⟨575978, by rfl⟩ : syracuseStep 767971 = 1151957) B1151957
theorem B538625 : Blo 358757 538625 := bstep (se 2 (by rfl) ⟨201984, by rfl⟩ : syracuseStep 538625 = 403969) B403969
theorem B538643 : Blo 358757 538643 := bstep (se 1 (by rfl) ⟨403982, by rfl⟩ : syracuseStep 538643 = 807965) B807965
theorem B407587 : Blo 358757 407587 := bstep (se 1 (by rfl) ⟨305690, by rfl⟩ : syracuseStep 407587 = 611381) B611381
theorem B538673 : Blo 358757 538673 := bstep (se 2 (by rfl) ⟨202002, by rfl⟩ : syracuseStep 538673 = 404005) B404005
theorem B538691 : Blo 358757 538691 := bstep (se 1 (by rfl) ⟨404018, by rfl⟩ : syracuseStep 538691 = 808037) B808037
theorem B538721 : Blo 358757 538721 := bstep (se 2 (by rfl) ⟨202020, by rfl⟩ : syracuseStep 538721 = 404041) B404041
theorem B538739 : Blo 358757 538739 := bstep (se 1 (by rfl) ⟨404054, by rfl⟩ : syracuseStep 538739 = 808109) B808109
theorem B538769 : Blo 358757 538769 := bstep (se 2 (by rfl) ⟨202038, by rfl⟩ : syracuseStep 538769 = 404077) B404077
theorem B538787 : Blo 358757 538787 := bstep (se 1 (by rfl) ⟨404090, by rfl⟩ : syracuseStep 538787 = 808181) B808181
theorem B407731 : Blo 358757 407731 := bstep (se 1 (by rfl) ⟨305798, by rfl⟩ : syracuseStep 407731 = 611597) B611597
theorem B538817 : Blo 358757 538817 := bstep (se 2 (by rfl) ⟨202056, by rfl⟩ : syracuseStep 538817 = 404113) B404113
theorem B538835 : Blo 358757 538835 := bstep (se 1 (by rfl) ⟨404126, by rfl⟩ : syracuseStep 538835 = 808253) B808253
theorem B538865 : Blo 358757 538865 := bstep (se 2 (by rfl) ⟨202074, by rfl⟩ : syracuseStep 538865 = 404149) B404149
theorem B538883 : Blo 358757 538883 := bstep (se 1 (by rfl) ⟨404162, by rfl⟩ : syracuseStep 538883 = 808325) B808325
theorem B538913 : Blo 358757 538913 := bstep (se 2 (by rfl) ⟨202092, by rfl⟩ : syracuseStep 538913 = 404185) B404185
theorem B538931 : Blo 358757 538931 := bstep (se 1 (by rfl) ⟨404198, by rfl⟩ : syracuseStep 538931 = 808397) B808397
theorem B407875 : Blo 358757 407875 := bstep (se 1 (by rfl) ⟨305906, by rfl⟩ : syracuseStep 407875 = 611813) B611813
theorem B538961 : Blo 358757 538961 := bstep (se 2 (by rfl) ⟨202110, by rfl⟩ : syracuseStep 538961 = 404221) B404221
theorem B538979 : Blo 358757 538979 := bstep (se 1 (by rfl) ⟨404234, by rfl⟩ : syracuseStep 538979 = 808469) B808469
theorem B539009 : Blo 358757 539009 := bstep (se 2 (by rfl) ⟨202128, by rfl⟩ : syracuseStep 539009 = 404257) B404257
theorem B539027 : Blo 358757 539027 := bstep (se 1 (by rfl) ⟨404270, by rfl⟩ : syracuseStep 539027 = 808541) B808541
theorem B539057 : Blo 358757 539057 := bstep (se 2 (by rfl) ⟨202146, by rfl⟩ : syracuseStep 539057 = 404293) B404293
theorem B539075 : Blo 358757 539075 := bstep (se 1 (by rfl) ⟨404306, by rfl⟩ : syracuseStep 539075 = 808613) B808613
theorem B408019 : Blo 358757 408019 := bstep (se 1 (by rfl) ⟨306014, by rfl⟩ : syracuseStep 408019 = 612029) B612029
theorem B539105 : Blo 358757 539105 := bstep (se 2 (by rfl) ⟨202164, by rfl⟩ : syracuseStep 539105 = 404329) B404329
theorem B539123 : Blo 358757 539123 := bstep (se 1 (by rfl) ⟨404342, by rfl⟩ : syracuseStep 539123 = 808685) B808685
theorem B4831757 : Blo 358757 4831757 := bstep (se 3 (by rfl) ⟨905954, by rfl⟩ : syracuseStep 4831757 = 1811909) B1811909
theorem B539153 : Blo 358757 539153 := bstep (se 2 (by rfl) ⟨202182, by rfl⟩ : syracuseStep 539153 = 404365) B404365
theorem B539171 : Blo 358757 539171 := bstep (se 1 (by rfl) ⟨404378, by rfl⟩ : syracuseStep 539171 = 808757) B808757
theorem B539201 : Blo 358757 539201 := bstep (se 2 (by rfl) ⟨202200, by rfl⟩ : syracuseStep 539201 = 404401) B404401
theorem B539219 : Blo 358757 539219 := bstep (se 1 (by rfl) ⟨404414, by rfl⟩ : syracuseStep 539219 = 808829) B808829
theorem B539249 : Blo 358757 539249 := bstep (se 2 (by rfl) ⟨202218, by rfl⟩ : syracuseStep 539249 = 404437) B404437
theorem B539267 : Blo 358757 539267 := bstep (se 1 (by rfl) ⟨404450, by rfl⟩ : syracuseStep 539267 = 808901) B808901
theorem B1849997 : Blo 358757 1849997 := bstep (se 3 (by rfl) ⟨346874, by rfl⟩ : syracuseStep 1849997 = 693749) B693749
theorem B539297 : Blo 358757 539297 := bstep (se 2 (by rfl) ⟨202236, by rfl⟩ : syracuseStep 539297 = 404473) B404473
theorem B539315 : Blo 358757 539315 := bstep (se 1 (by rfl) ⟨404486, by rfl⟩ : syracuseStep 539315 = 808973) B808973
theorem B539345 : Blo 358757 539345 := bstep (se 2 (by rfl) ⟨202254, by rfl⟩ : syracuseStep 539345 = 404509) B404509
theorem B1817315 : Blo 358757 1817315 := bstep (se 1 (by rfl) ⟨1362986, by rfl⟩ : syracuseStep 1817315 = 2725973) B2725973
theorem B539363 : Blo 358757 539363 := bstep (se 1 (by rfl) ⟨404522, by rfl⟩ : syracuseStep 539363 = 809045) B809045
theorem B1653475 : Blo 358757 1653475 := bstep (se 1 (by rfl) ⟨1240106, by rfl⟩ : syracuseStep 1653475 = 2480213) B2480213
theorem B1161965 : Blo 358757 1161965 := bstep (se 3 (by rfl) ⟨217868, by rfl⟩ : syracuseStep 1161965 = 435737) B435737
theorem B1030897 : Blo 358757 1030897 := bstep (se 2 (by rfl) ⟨386586, by rfl⟩ : syracuseStep 1030897 = 773173) B773173
theorem B539393 : Blo 358757 539393 := bstep (se 2 (by rfl) ⟨202272, by rfl⟩ : syracuseStep 539393 = 404545) B404545
theorem B539411 : Blo 358757 539411 := bstep (se 1 (by rfl) ⟨404558, by rfl⟩ : syracuseStep 539411 = 809117) B809117
theorem B539441 : Blo 358757 539441 := bstep (se 2 (by rfl) ⟨202290, by rfl⟩ : syracuseStep 539441 = 404581) B404581
theorem B539459 : Blo 358757 539459 := bstep (se 1 (by rfl) ⟨404594, by rfl⟩ : syracuseStep 539459 = 809189) B809189
theorem B539489 : Blo 358757 539489 := bstep (se 2 (by rfl) ⟨202308, by rfl⟩ : syracuseStep 539489 = 404617) B404617
theorem B539507 : Blo 358757 539507 := bstep (se 1 (by rfl) ⟨404630, by rfl⟩ : syracuseStep 539507 = 809261) B809261
theorem B539537 : Blo 358757 539537 := bstep (se 2 (by rfl) ⟨202326, by rfl⟩ : syracuseStep 539537 = 404653) B404653
theorem B539555 : Blo 358757 539555 := bstep (se 1 (by rfl) ⟨404666, by rfl⟩ : syracuseStep 539555 = 809333) B809333
theorem B539585 : Blo 358757 539585 := bstep (se 2 (by rfl) ⟨202344, by rfl⟩ : syracuseStep 539585 = 404689) B404689
theorem B539603 : Blo 358757 539603 := bstep (se 1 (by rfl) ⟨404702, by rfl⟩ : syracuseStep 539603 = 809405) B809405
theorem B539633 : Blo 358757 539633 := bstep (se 2 (by rfl) ⟨202362, by rfl⟩ : syracuseStep 539633 = 404725) B404725
theorem B539651 : Blo 358757 539651 := bstep (se 1 (by rfl) ⟨404738, by rfl⟩ : syracuseStep 539651 = 809477) B809477
theorem B539681 : Blo 358757 539681 := bstep (se 2 (by rfl) ⟨202380, by rfl⟩ : syracuseStep 539681 = 404761) B404761
theorem B539699 : Blo 358757 539699 := bstep (se 1 (by rfl) ⟨404774, by rfl⟩ : syracuseStep 539699 = 809549) B809549
theorem B539729 : Blo 358757 539729 := bstep (se 2 (by rfl) ⟨202398, by rfl⟩ : syracuseStep 539729 = 404797) B404797
theorem B539747 : Blo 358757 539747 := bstep (se 1 (by rfl) ⟨404810, by rfl⟩ : syracuseStep 539747 = 809621) B809621
theorem B539777 : Blo 358757 539777 := bstep (se 2 (by rfl) ⟨202416, by rfl⟩ : syracuseStep 539777 = 404833) B404833
theorem B539795 : Blo 358757 539795 := bstep (se 1 (by rfl) ⟨404846, by rfl⟩ : syracuseStep 539795 = 809693) B809693
theorem B539825 : Blo 358757 539825 := bstep (se 2 (by rfl) ⟨202434, by rfl⟩ : syracuseStep 539825 = 404869) B404869
theorem B867505 : Blo 358757 867505 := bstep (se 2 (by rfl) ⟨325314, by rfl⟩ : syracuseStep 867505 = 650629) B650629
theorem B539843 : Blo 358757 539843 := bstep (se 1 (by rfl) ⟨404882, by rfl⟩ : syracuseStep 539843 = 809765) B809765
theorem B539873 : Blo 358757 539873 := bstep (se 2 (by rfl) ⟨202452, by rfl⟩ : syracuseStep 539873 = 404905) B404905
theorem B539891 : Blo 358757 539891 := bstep (se 1 (by rfl) ⟨404918, by rfl⟩ : syracuseStep 539891 = 809837) B809837
theorem B605441 : Blo 358757 605441 := bstep (se 2 (by rfl) ⟨227040, by rfl⟩ : syracuseStep 605441 = 454081) B454081
theorem B539921 : Blo 358757 539921 := bstep (se 2 (by rfl) ⟨202470, by rfl⟩ : syracuseStep 539921 = 404941) B404941
theorem B539939 : Blo 358757 539939 := bstep (se 1 (by rfl) ⟨404954, by rfl⟩ : syracuseStep 539939 = 809909) B809909
theorem B539969 : Blo 358757 539969 := bstep (se 2 (by rfl) ⟨202488, by rfl⟩ : syracuseStep 539969 = 404977) B404977
theorem B539987 : Blo 358757 539987 := bstep (se 1 (by rfl) ⟨404990, by rfl⟩ : syracuseStep 539987 = 809981) B809981
theorem B540017 : Blo 358757 540017 := bstep (se 2 (by rfl) ⟨202506, by rfl⟩ : syracuseStep 540017 = 405013) B405013
theorem B605569 : Blo 358757 605569 := bstep (se 2 (by rfl) ⟨227088, by rfl⟩ : syracuseStep 605569 = 454177) B454177
theorem B540035 : Blo 358757 540035 := bstep (se 1 (by rfl) ⟨405026, by rfl⟩ : syracuseStep 540035 = 810053) B810053
theorem B540065 : Blo 358757 540065 := bstep (se 2 (by rfl) ⟨202524, by rfl⟩ : syracuseStep 540065 = 405049) B405049
theorem B605603 : Blo 358757 605603 := bstep (se 1 (by rfl) ⟨454202, by rfl⟩ : syracuseStep 605603 = 908405) B908405
theorem B540083 : Blo 358757 540083 := bstep (se 1 (by rfl) ⟨405062, by rfl⟩ : syracuseStep 540083 = 810125) B810125
theorem B769475 : Blo 358757 769475 := bstep (se 1 (by rfl) ⟨577106, by rfl⟩ : syracuseStep 769475 = 1154213) B1154213
theorem B540113 : Blo 358757 540113 := bstep (se 2 (by rfl) ⟨202542, by rfl⟩ : syracuseStep 540113 = 405085) B405085
theorem B540131 : Blo 358757 540131 := bstep (se 1 (by rfl) ⟨405098, by rfl⟩ : syracuseStep 540131 = 810197) B810197
theorem B540161 : Blo 358757 540161 := bstep (se 2 (by rfl) ⟨202560, by rfl⟩ : syracuseStep 540161 = 405121) B405121
theorem B1818125 : Blo 358757 1818125 := bstep (se 3 (by rfl) ⟨340898, by rfl⟩ : syracuseStep 1818125 = 681797) B681797
theorem B540179 : Blo 358757 540179 := bstep (se 1 (by rfl) ⟨405134, by rfl⟩ : syracuseStep 540179 = 810269) B810269
theorem B605731 : Blo 358757 605731 := bstep (se 1 (by rfl) ⟨454298, by rfl⟩ : syracuseStep 605731 = 908597) B908597
theorem B540209 : Blo 358757 540209 := bstep (se 2 (by rfl) ⟨202578, by rfl⟩ : syracuseStep 540209 = 405157) B405157
theorem B540227 : Blo 358757 540227 := bstep (se 1 (by rfl) ⟨405170, by rfl⟩ : syracuseStep 540227 = 810341) B810341
theorem B540257 : Blo 358757 540257 := bstep (se 2 (by rfl) ⟨202596, by rfl⟩ : syracuseStep 540257 = 405193) B405193
theorem B540275 : Blo 358757 540275 := bstep (se 1 (by rfl) ⟨405206, by rfl⟩ : syracuseStep 540275 = 810413) B810413
theorem B540305 : Blo 358757 540305 := bstep (se 2 (by rfl) ⟨202614, by rfl⟩ : syracuseStep 540305 = 405229) B405229
theorem B540323 : Blo 358757 540323 := bstep (se 1 (by rfl) ⟨405242, by rfl⟩ : syracuseStep 540323 = 810485) B810485
theorem B605873 : Blo 358757 605873 := bstep (se 2 (by rfl) ⟨227202, by rfl⟩ : syracuseStep 605873 = 454405) B454405
theorem B540353 : Blo 358757 540353 := bstep (se 2 (by rfl) ⟨202632, by rfl⟩ : syracuseStep 540353 = 405265) B405265
theorem B540371 : Blo 358757 540371 := bstep (se 1 (by rfl) ⟨405278, by rfl⟩ : syracuseStep 540371 = 810557) B810557
theorem B540401 : Blo 358757 540401 := bstep (se 2 (by rfl) ⟨202650, by rfl⟩ : syracuseStep 540401 = 405301) B405301
theorem B540419 : Blo 358757 540419 := bstep (se 1 (by rfl) ⟨405314, by rfl⟩ : syracuseStep 540419 = 810629) B810629
theorem B540449 : Blo 358757 540449 := bstep (se 2 (by rfl) ⟨202668, by rfl⟩ : syracuseStep 540449 = 405337) B405337
theorem B606001 : Blo 358757 606001 := bstep (se 2 (by rfl) ⟨227250, by rfl⟩ : syracuseStep 606001 = 454501) B454501
theorem B540467 : Blo 358757 540467 := bstep (se 1 (by rfl) ⟨405350, by rfl⟩ : syracuseStep 540467 = 810701) B810701
theorem B540497 : Blo 358757 540497 := bstep (se 2 (by rfl) ⟨202686, by rfl⟩ : syracuseStep 540497 = 405373) B405373
theorem B606035 : Blo 358757 606035 := bstep (se 1 (by rfl) ⟨454526, by rfl⟩ : syracuseStep 606035 = 909053) B909053
theorem B1752931 : Blo 358757 1752931 := bstep (se 1 (by rfl) ⟨1314698, by rfl⟩ : syracuseStep 1752931 = 2629397) B2629397
theorem B540515 : Blo 358757 540515 := bstep (se 1 (by rfl) ⟨405386, by rfl⟩ : syracuseStep 540515 = 810773) B810773
theorem B540545 : Blo 358757 540545 := bstep (se 2 (by rfl) ⟨202704, by rfl⟩ : syracuseStep 540545 = 405409) B405409
theorem B540563 : Blo 358757 540563 := bstep (se 1 (by rfl) ⟨405422, by rfl⟩ : syracuseStep 540563 = 810845) B810845
theorem B540593 : Blo 358757 540593 := bstep (se 2 (by rfl) ⟨202722, by rfl⟩ : syracuseStep 540593 = 405445) B405445
theorem B2310065 : Blo 358757 2310065 := bstep (se 2 (by rfl) ⟨866274, by rfl⟩ : syracuseStep 2310065 = 1732549) B1732549
theorem B540611 : Blo 358757 540611 := bstep (se 1 (by rfl) ⟨405458, by rfl⟩ : syracuseStep 540611 = 810917) B810917
theorem B606163 : Blo 358757 606163 := bstep (se 1 (by rfl) ⟨454622, by rfl⟩ : syracuseStep 606163 = 909245) B909245
theorem B540641 : Blo 358757 540641 := bstep (se 2 (by rfl) ⟨202740, by rfl⟩ : syracuseStep 540641 = 405481) B405481
theorem B1032173 : Blo 358757 1032173 := bstep (se 3 (by rfl) ⟨193532, by rfl⟩ : syracuseStep 1032173 = 387065) B387065
theorem B540659 : Blo 358757 540659 := bstep (se 1 (by rfl) ⟨405494, by rfl⟩ : syracuseStep 540659 = 810989) B810989
theorem B540689 : Blo 358757 540689 := bstep (se 2 (by rfl) ⟨202758, by rfl⟩ : syracuseStep 540689 = 405517) B405517
theorem B540707 : Blo 358757 540707 := bstep (se 1 (by rfl) ⟨405530, by rfl⟩ : syracuseStep 540707 = 811061) B811061
theorem B540737 : Blo 358757 540737 := bstep (se 2 (by rfl) ⟨202776, by rfl⟩ : syracuseStep 540737 = 405553) B405553
theorem B540755 : Blo 358757 540755 := bstep (se 1 (by rfl) ⟨405566, by rfl⟩ : syracuseStep 540755 = 811133) B811133
theorem B606305 : Blo 358757 606305 := bstep (se 2 (by rfl) ⟨227364, by rfl⟩ : syracuseStep 606305 = 454729) B454729
theorem B540785 : Blo 358757 540785 := bstep (se 2 (by rfl) ⟨202794, by rfl⟩ : syracuseStep 540785 = 405589) B405589
theorem B540803 : Blo 358757 540803 := bstep (se 1 (by rfl) ⟨405602, by rfl⟩ : syracuseStep 540803 = 811205) B811205
theorem B540833 : Blo 358757 540833 := bstep (se 2 (by rfl) ⟨202812, by rfl⟩ : syracuseStep 540833 = 405625) B405625
theorem B1032355 : Blo 358757 1032355 := bstep (se 1 (by rfl) ⟨774266, by rfl⟩ : syracuseStep 1032355 = 1548533) B1548533
theorem B540851 : Blo 358757 540851 := bstep (se 1 (by rfl) ⟨405638, by rfl⟩ : syracuseStep 540851 = 811277) B811277
theorem B540881 : Blo 358757 540881 := bstep (se 2 (by rfl) ⟨202830, by rfl⟩ : syracuseStep 540881 = 405661) B405661
theorem B1032401 : Blo 358757 1032401 := bstep (se 2 (by rfl) ⟨387150, by rfl⟩ : syracuseStep 1032401 = 774301) B774301
theorem B606433 : Blo 358757 606433 := bstep (se 2 (by rfl) ⟨227412, by rfl⟩ : syracuseStep 606433 = 454825) B454825
theorem B540899 : Blo 358757 540899 := bstep (se 1 (by rfl) ⟨405674, by rfl⟩ : syracuseStep 540899 = 811349) B811349
theorem B540929 : Blo 358757 540929 := bstep (se 2 (by rfl) ⟨202848, by rfl⟩ : syracuseStep 540929 = 405697) B405697
theorem B606467 : Blo 358757 606467 := bstep (se 1 (by rfl) ⟨454850, by rfl⟩ : syracuseStep 606467 = 909701) B909701
theorem B540947 : Blo 358757 540947 := bstep (se 1 (by rfl) ⟨405710, by rfl⟩ : syracuseStep 540947 = 811421) B811421
theorem B540977 : Blo 358757 540977 := bstep (se 2 (by rfl) ⟨202866, by rfl⟩ : syracuseStep 540977 = 405733) B405733
theorem B540995 : Blo 358757 540995 := bstep (se 1 (by rfl) ⟨405746, by rfl⟩ : syracuseStep 540995 = 811493) B811493
theorem B541025 : Blo 358757 541025 := bstep (se 2 (by rfl) ⟨202884, by rfl⟩ : syracuseStep 541025 = 405769) B405769
theorem B541043 : Blo 358757 541043 := bstep (se 1 (by rfl) ⟨405782, by rfl⟩ : syracuseStep 541043 = 811565) B811565
theorem B606595 : Blo 358757 606595 := bstep (se 1 (by rfl) ⟨454946, by rfl⟩ : syracuseStep 606595 = 909893) B909893
theorem B541073 : Blo 358757 541073 := bstep (se 2 (by rfl) ⟨202902, by rfl⟩ : syracuseStep 541073 = 405805) B405805
theorem B541091 : Blo 358757 541091 := bstep (se 1 (by rfl) ⟨405818, by rfl⟩ : syracuseStep 541091 = 811637) B811637
theorem B541121 : Blo 358757 541121 := bstep (se 2 (by rfl) ⟨202920, by rfl⟩ : syracuseStep 541121 = 405841) B405841
theorem B541139 : Blo 358757 541139 := bstep (se 1 (by rfl) ⟨405854, by rfl⟩ : syracuseStep 541139 = 811709) B811709
theorem B541169 : Blo 358757 541169 := bstep (se 2 (by rfl) ⟨202938, by rfl⟩ : syracuseStep 541169 = 405877) B405877
theorem B541187 : Blo 358757 541187 := bstep (se 1 (by rfl) ⟨405890, by rfl⟩ : syracuseStep 541187 = 811781) B811781
theorem B606737 : Blo 358757 606737 := bstep (se 2 (by rfl) ⟨227526, by rfl⟩ : syracuseStep 606737 = 455053) B455053
theorem B541217 : Blo 358757 541217 := bstep (se 2 (by rfl) ⟨202956, by rfl⟩ : syracuseStep 541217 = 405913) B405913
theorem B541235 : Blo 358757 541235 := bstep (se 1 (by rfl) ⟨405926, by rfl⟩ : syracuseStep 541235 = 811853) B811853
theorem B541265 : Blo 358757 541265 := bstep (se 2 (by rfl) ⟨202974, by rfl⟩ : syracuseStep 541265 = 405949) B405949
theorem B541283 : Blo 358757 541283 := bstep (se 1 (by rfl) ⟨405962, by rfl⟩ : syracuseStep 541283 = 811925) B811925
theorem B541313 : Blo 358757 541313 := bstep (se 2 (by rfl) ⟨202992, by rfl⟩ : syracuseStep 541313 = 405985) B405985
theorem B606865 : Blo 358757 606865 := bstep (se 2 (by rfl) ⟨227574, by rfl⟩ : syracuseStep 606865 = 455149) B455149
theorem B770705 : Blo 358757 770705 := bstep (se 2 (by rfl) ⟨289014, by rfl⟩ : syracuseStep 770705 = 578029) B578029
theorem B541331 : Blo 358757 541331 := bstep (se 1 (by rfl) ⟨405998, by rfl⟩ : syracuseStep 541331 = 811997) B811997
theorem B541361 : Blo 358757 541361 := bstep (se 2 (by rfl) ⟨203010, by rfl⟩ : syracuseStep 541361 = 406021) B406021
theorem B606899 : Blo 358757 606899 := bstep (se 1 (by rfl) ⟨455174, by rfl⟩ : syracuseStep 606899 = 910349) B910349
theorem B541379 : Blo 358757 541379 := bstep (se 1 (by rfl) ⟨406034, by rfl⟩ : syracuseStep 541379 = 812069) B812069
theorem B541409 : Blo 358757 541409 := bstep (se 2 (by rfl) ⟨203028, by rfl⟩ : syracuseStep 541409 = 406057) B406057
theorem B2081521 : Blo 358757 2081521 := bstep (se 2 (by rfl) ⟨780570, by rfl⟩ : syracuseStep 2081521 = 1561141) B1561141
theorem B541427 : Blo 358757 541427 := bstep (se 1 (by rfl) ⟨406070, by rfl⟩ : syracuseStep 541427 = 812141) B812141
theorem B541457 : Blo 358757 541457 := bstep (se 2 (by rfl) ⟨203046, by rfl⟩ : syracuseStep 541457 = 406093) B406093
theorem B541475 : Blo 358757 541475 := bstep (se 1 (by rfl) ⟨406106, by rfl⟩ : syracuseStep 541475 = 812213) B812213
theorem B607027 : Blo 358757 607027 := bstep (se 1 (by rfl) ⟨455270, by rfl⟩ : syracuseStep 607027 = 910541) B910541
theorem B541505 : Blo 358757 541505 := bstep (se 2 (by rfl) ⟨203064, by rfl⟩ : syracuseStep 541505 = 406129) B406129
theorem B541523 : Blo 358757 541523 := bstep (se 1 (by rfl) ⟨406142, by rfl⟩ : syracuseStep 541523 = 812285) B812285
theorem B541553 : Blo 358757 541553 := bstep (se 2 (by rfl) ⟨203082, by rfl⟩ : syracuseStep 541553 = 406165) B406165
theorem B541571 : Blo 358757 541571 := bstep (se 1 (by rfl) ⟨406178, by rfl⟩ : syracuseStep 541571 = 812357) B812357
theorem B541601 : Blo 358757 541601 := bstep (se 2 (by rfl) ⟨203100, by rfl⟩ : syracuseStep 541601 = 406201) B406201
theorem B541619 : Blo 358757 541619 := bstep (se 1 (by rfl) ⟨406214, by rfl⟩ : syracuseStep 541619 = 812429) B812429
theorem B607169 : Blo 358757 607169 := bstep (se 2 (by rfl) ⟨227688, by rfl⟩ : syracuseStep 607169 = 455377) B455377
theorem B541649 : Blo 358757 541649 := bstep (se 2 (by rfl) ⟨203118, by rfl⟩ : syracuseStep 541649 = 406237) B406237
theorem B541667 : Blo 358757 541667 := bstep (se 1 (by rfl) ⟨406250, by rfl⟩ : syracuseStep 541667 = 812501) B812501
theorem B541697 : Blo 358757 541697 := bstep (se 2 (by rfl) ⟨203136, by rfl⟩ : syracuseStep 541697 = 406273) B406273
theorem B541715 : Blo 358757 541715 := bstep (se 1 (by rfl) ⟨406286, by rfl⟩ : syracuseStep 541715 = 812573) B812573
theorem B541745 : Blo 358757 541745 := bstep (se 2 (by rfl) ⟨203154, by rfl⟩ : syracuseStep 541745 = 406309) B406309
theorem B607297 : Blo 358757 607297 := bstep (se 2 (by rfl) ⟨227736, by rfl⟩ : syracuseStep 607297 = 455473) B455473
theorem B541763 : Blo 358757 541763 := bstep (se 1 (by rfl) ⟨406322, by rfl⟩ : syracuseStep 541763 = 812645) B812645
theorem B541793 : Blo 358757 541793 := bstep (se 2 (by rfl) ⟨203172, by rfl⟩ : syracuseStep 541793 = 406345) B406345
theorem B607331 : Blo 358757 607331 := bstep (se 1 (by rfl) ⟨455498, by rfl⟩ : syracuseStep 607331 = 910997) B910997
theorem B1393777 : Blo 358757 1393777 := bstep (se 2 (by rfl) ⟨522666, by rfl⟩ : syracuseStep 1393777 = 1045333) B1045333
theorem B541811 : Blo 358757 541811 := bstep (se 1 (by rfl) ⟨406358, by rfl⟩ : syracuseStep 541811 = 812717) B812717
theorem B541841 : Blo 358757 541841 := bstep (se 2 (by rfl) ⟨203190, by rfl⟩ : syracuseStep 541841 = 406381) B406381
theorem B541859 : Blo 358757 541859 := bstep (se 1 (by rfl) ⟨406394, by rfl⟩ : syracuseStep 541859 = 812789) B812789
theorem B541889 : Blo 358757 541889 := bstep (se 2 (by rfl) ⟨203208, by rfl⟩ : syracuseStep 541889 = 406417) B406417
theorem B541907 : Blo 358757 541907 := bstep (se 1 (by rfl) ⟨406430, by rfl⟩ : syracuseStep 541907 = 812861) B812861
theorem B607459 : Blo 358757 607459 := bstep (se 1 (by rfl) ⟨455594, by rfl⟩ : syracuseStep 607459 = 911189) B911189
theorem B541937 : Blo 358757 541937 := bstep (se 2 (by rfl) ⟨203226, by rfl⟩ : syracuseStep 541937 = 406453) B406453
theorem B541955 : Blo 358757 541955 := bstep (se 1 (by rfl) ⟨406466, by rfl⟩ : syracuseStep 541955 = 812933) B812933
theorem B541985 : Blo 358757 541985 := bstep (se 2 (by rfl) ⟨203244, by rfl⟩ : syracuseStep 541985 = 406489) B406489
theorem B542003 : Blo 358757 542003 := bstep (se 1 (by rfl) ⟨406502, by rfl⟩ : syracuseStep 542003 = 813005) B813005
theorem B542033 : Blo 358757 542033 := bstep (se 2 (by rfl) ⟨203262, by rfl⟩ : syracuseStep 542033 = 406525) B406525
theorem B2311523 : Blo 358757 2311523 := bstep (se 1 (by rfl) ⟨1733642, by rfl⟩ : syracuseStep 2311523 = 3467285) B3467285
theorem B542051 : Blo 358757 542051 := bstep (se 1 (by rfl) ⟨406538, by rfl⟩ : syracuseStep 542051 = 813077) B813077
theorem B607601 : Blo 358757 607601 := bstep (se 2 (by rfl) ⟨227850, by rfl⟩ : syracuseStep 607601 = 455701) B455701
theorem B542081 : Blo 358757 542081 := bstep (se 2 (by rfl) ⟨203280, by rfl⟩ : syracuseStep 542081 = 406561) B406561
theorem B542099 : Blo 358757 542099 := bstep (se 1 (by rfl) ⟨406574, by rfl⟩ : syracuseStep 542099 = 813149) B813149
theorem B542129 : Blo 358757 542129 := bstep (se 2 (by rfl) ⟨203298, by rfl⟩ : syracuseStep 542129 = 406597) B406597
theorem B542147 : Blo 358757 542147 := bstep (se 1 (by rfl) ⟨406610, by rfl⟩ : syracuseStep 542147 = 813221) B813221
theorem B542177 : Blo 358757 542177 := bstep (se 2 (by rfl) ⟨203316, by rfl⟩ : syracuseStep 542177 = 406633) B406633
theorem B1394147 : Blo 358757 1394147 := bstep (se 1 (by rfl) ⟨1045610, by rfl⟩ : syracuseStep 1394147 = 2091221) B2091221
theorem B607729 : Blo 358757 607729 := bstep (se 2 (by rfl) ⟨227898, by rfl⟩ : syracuseStep 607729 = 455797) B455797
theorem B542195 : Blo 358757 542195 := bstep (se 1 (by rfl) ⟨406646, by rfl⟩ : syracuseStep 542195 = 813293) B813293
theorem B771601 : Blo 358757 771601 := bstep (se 2 (by rfl) ⟨289350, by rfl⟩ : syracuseStep 771601 = 578701) B578701
theorem B542225 : Blo 358757 542225 := bstep (se 2 (by rfl) ⟨203334, by rfl⟩ : syracuseStep 542225 = 406669) B406669
theorem B607763 : Blo 358757 607763 := bstep (se 1 (by rfl) ⟨455822, by rfl⟩ : syracuseStep 607763 = 911645) B911645
theorem B574993 : Blo 358757 574993 := bstep (se 2 (by rfl) ⟨215622, by rfl⟩ : syracuseStep 574993 = 431245) B431245
theorem B771619 : Blo 358757 771619 := bstep (se 1 (by rfl) ⟨578714, by rfl⟩ : syracuseStep 771619 = 1157429) B1157429
theorem B542243 : Blo 358757 542243 := bstep (se 1 (by rfl) ⟨406682, by rfl⟩ : syracuseStep 542243 = 813365) B813365
theorem B542273 : Blo 358757 542273 := bstep (se 2 (by rfl) ⟨203352, by rfl⟩ : syracuseStep 542273 = 406705) B406705
theorem B542291 : Blo 358757 542291 := bstep (se 1 (by rfl) ⟨406718, by rfl⟩ : syracuseStep 542291 = 813437) B813437
theorem B575075 : Blo 358757 575075 := bstep (se 1 (by rfl) ⟨431306, by rfl⟩ : syracuseStep 575075 = 862613) B862613
theorem B542321 : Blo 358757 542321 := bstep (se 2 (by rfl) ⟨203370, by rfl⟩ : syracuseStep 542321 = 406741) B406741
theorem B542339 : Blo 358757 542339 := bstep (se 1 (by rfl) ⟨406754, by rfl⟩ : syracuseStep 542339 = 813509) B813509
theorem B607891 : Blo 358757 607891 := bstep (se 1 (by rfl) ⟨455918, by rfl⟩ : syracuseStep 607891 = 911837) B911837
theorem B542369 : Blo 358757 542369 := bstep (se 2 (by rfl) ⟨203388, by rfl⟩ : syracuseStep 542369 = 406777) B406777
theorem B542387 : Blo 358757 542387 := bstep (se 1 (by rfl) ⟨406790, by rfl⟩ : syracuseStep 542387 = 813581) B813581
theorem B542417 : Blo 358757 542417 := bstep (se 2 (by rfl) ⟨203406, by rfl⟩ : syracuseStep 542417 = 406813) B406813
theorem B542435 : Blo 358757 542435 := bstep (se 1 (by rfl) ⟨406826, by rfl⟩ : syracuseStep 542435 = 813653) B813653
theorem B542465 : Blo 358757 542465 := bstep (se 2 (by rfl) ⟨203424, by rfl⟩ : syracuseStep 542465 = 406849) B406849
theorem B542483 : Blo 358757 542483 := bstep (se 1 (by rfl) ⟨406862, by rfl⟩ : syracuseStep 542483 = 813725) B813725
theorem B608033 : Blo 358757 608033 := bstep (se 2 (by rfl) ⟨228012, by rfl⟩ : syracuseStep 608033 = 456025) B456025
theorem B542513 : Blo 358757 542513 := bstep (se 2 (by rfl) ⟨203442, by rfl⟩ : syracuseStep 542513 = 406885) B406885
theorem B542531 : Blo 358757 542531 := bstep (se 1 (by rfl) ⟨406898, by rfl⟩ : syracuseStep 542531 = 813797) B813797
theorem B542561 : Blo 358757 542561 := bstep (se 2 (by rfl) ⟨203460, by rfl⟩ : syracuseStep 542561 = 406921) B406921
theorem B542579 : Blo 358757 542579 := bstep (se 1 (by rfl) ⟨406934, by rfl⟩ : syracuseStep 542579 = 813869) B813869
theorem B542609 : Blo 358757 542609 := bstep (se 2 (by rfl) ⟨203478, by rfl⟩ : syracuseStep 542609 = 406957) B406957
theorem B608161 : Blo 358757 608161 := bstep (se 2 (by rfl) ⟨228060, by rfl⟩ : syracuseStep 608161 = 456121) B456121
theorem B542627 : Blo 358757 542627 := bstep (se 1 (by rfl) ⟨406970, by rfl⟩ : syracuseStep 542627 = 813941) B813941
theorem B542657 : Blo 358757 542657 := bstep (se 2 (by rfl) ⟨203496, by rfl⟩ : syracuseStep 542657 = 406993) B406993
theorem B608195 : Blo 358757 608195 := bstep (se 1 (by rfl) ⟨456146, by rfl⟩ : syracuseStep 608195 = 912293) B912293
theorem B542675 : Blo 358757 542675 := bstep (se 1 (by rfl) ⟨407006, by rfl⟩ : syracuseStep 542675 = 814013) B814013
theorem B542705 : Blo 358757 542705 := bstep (se 2 (by rfl) ⟨203514, by rfl⟩ : syracuseStep 542705 = 407029) B407029
theorem B542723 : Blo 358757 542723 := bstep (se 1 (by rfl) ⟨407042, by rfl⟩ : syracuseStep 542723 = 814085) B814085
theorem B542753 : Blo 358757 542753 := bstep (se 2 (by rfl) ⟨203532, by rfl⟩ : syracuseStep 542753 = 407065) B407065
theorem B542771 : Blo 358757 542771 := bstep (se 1 (by rfl) ⟨407078, by rfl⟩ : syracuseStep 542771 = 814157) B814157
theorem B608323 : Blo 358757 608323 := bstep (se 1 (by rfl) ⟨456242, by rfl⟩ : syracuseStep 608323 = 912485) B912485
theorem B542801 : Blo 358757 542801 := bstep (se 2 (by rfl) ⟨203550, by rfl⟩ : syracuseStep 542801 = 407101) B407101
theorem B542819 : Blo 358757 542819 := bstep (se 1 (by rfl) ⟨407114, by rfl⟩ : syracuseStep 542819 = 814229) B814229
theorem B542849 : Blo 358757 542849 := bstep (se 2 (by rfl) ⟨203568, by rfl⟩ : syracuseStep 542849 = 407137) B407137
theorem B542867 : Blo 358757 542867 := bstep (se 1 (by rfl) ⟨407150, by rfl⟩ : syracuseStep 542867 = 814301) B814301
theorem B542897 : Blo 358757 542897 := bstep (se 2 (by rfl) ⟨203586, by rfl⟩ : syracuseStep 542897 = 407173) B407173
theorem B542915 : Blo 358757 542915 := bstep (se 1 (by rfl) ⟨407186, by rfl⟩ : syracuseStep 542915 = 814373) B814373
theorem B608465 : Blo 358757 608465 := bstep (se 2 (by rfl) ⟨228174, by rfl⟩ : syracuseStep 608465 = 456349) B456349
theorem B542945 : Blo 358757 542945 := bstep (se 2 (by rfl) ⟨203604, by rfl⟩ : syracuseStep 542945 = 407209) B407209
theorem B3786979 : Blo 358757 3786979 := bstep (se 1 (by rfl) ⟨2840234, by rfl⟩ : syracuseStep 3786979 = 5680469) B5680469
theorem B4442339 : Blo 358757 4442339 := bstep (se 1 (by rfl) ⟨3331754, by rfl⟩ : syracuseStep 4442339 = 6663509) B6663509
theorem B542963 : Blo 358757 542963 := bstep (se 1 (by rfl) ⟨407222, by rfl⟩ : syracuseStep 542963 = 814445) B814445
theorem B542993 : Blo 358757 542993 := bstep (se 2 (by rfl) ⟨203622, by rfl⟩ : syracuseStep 542993 = 407245) B407245
theorem B543011 : Blo 358757 543011 := bstep (se 1 (by rfl) ⟨407258, by rfl⟩ : syracuseStep 543011 = 814517) B814517
theorem B543041 : Blo 358757 543041 := bstep (se 2 (by rfl) ⟨203640, by rfl⟩ : syracuseStep 543041 = 407281) B407281
theorem B608593 : Blo 358757 608593 := bstep (se 2 (by rfl) ⟨228222, by rfl⟩ : syracuseStep 608593 = 456445) B456445
theorem B543059 : Blo 358757 543059 := bstep (se 1 (by rfl) ⟨407294, by rfl⟩ : syracuseStep 543059 = 814589) B814589
theorem B1821041 : Blo 358757 1821041 := bstep (se 2 (by rfl) ⟨682890, by rfl⟩ : syracuseStep 1821041 = 1365781) B1365781
theorem B543089 : Blo 358757 543089 := bstep (se 2 (by rfl) ⟨203658, by rfl⟩ : syracuseStep 543089 = 407317) B407317
theorem B608627 : Blo 358757 608627 := bstep (se 1 (by rfl) ⟨456470, by rfl⟩ : syracuseStep 608627 = 912941) B912941
theorem B543107 : Blo 358757 543107 := bstep (se 1 (by rfl) ⟨407330, by rfl⟩ : syracuseStep 543107 = 814661) B814661
theorem B543137 : Blo 358757 543137 := bstep (se 2 (by rfl) ⟨203676, by rfl⟩ : syracuseStep 543137 = 407353) B407353
theorem B543155 : Blo 358757 543155 := bstep (se 1 (by rfl) ⟨407366, by rfl⟩ : syracuseStep 543155 = 814733) B814733
theorem B543185 : Blo 358757 543185 := bstep (se 2 (by rfl) ⟨203694, by rfl⟩ : syracuseStep 543185 = 407389) B407389
theorem B543203 : Blo 358757 543203 := bstep (se 1 (by rfl) ⟨407402, by rfl⟩ : syracuseStep 543203 = 814805) B814805
theorem B608755 : Blo 358757 608755 := bstep (se 1 (by rfl) ⟨456566, by rfl⟩ : syracuseStep 608755 = 913133) B913133
theorem B543233 : Blo 358757 543233 := bstep (se 2 (by rfl) ⟨203712, by rfl⟩ : syracuseStep 543233 = 407425) B407425
theorem B543251 : Blo 358757 543251 := bstep (se 1 (by rfl) ⟨407438, by rfl⟩ : syracuseStep 543251 = 814877) B814877
theorem B543281 : Blo 358757 543281 := bstep (se 2 (by rfl) ⟨203730, by rfl⟩ : syracuseStep 543281 = 407461) B407461
theorem B543299 : Blo 358757 543299 := bstep (se 1 (by rfl) ⟨407474, by rfl⟩ : syracuseStep 543299 = 814949) B814949
theorem B543329 : Blo 358757 543329 := bstep (se 2 (by rfl) ⟨203748, by rfl⟩ : syracuseStep 543329 = 407497) B407497
theorem B543347 : Blo 358757 543347 := bstep (se 1 (by rfl) ⟨407510, by rfl⟩ : syracuseStep 543347 = 815021) B815021
theorem B608897 : Blo 358757 608897 := bstep (se 2 (by rfl) ⟨228336, by rfl⟩ : syracuseStep 608897 = 456673) B456673
theorem B543377 : Blo 358757 543377 := bstep (se 2 (by rfl) ⟨203766, by rfl⟩ : syracuseStep 543377 = 407533) B407533
theorem B543395 : Blo 358757 543395 := bstep (se 1 (by rfl) ⟨407546, by rfl⟩ : syracuseStep 543395 = 815093) B815093
theorem B543425 : Blo 358757 543425 := bstep (se 2 (by rfl) ⟨203784, by rfl⟩ : syracuseStep 543425 = 407569) B407569
theorem B543443 : Blo 358757 543443 := bstep (se 1 (by rfl) ⟨407582, by rfl⟩ : syracuseStep 543443 = 815165) B815165
theorem B543473 : Blo 358757 543473 := bstep (se 2 (by rfl) ⟨203802, by rfl⟩ : syracuseStep 543473 = 407605) B407605
theorem B609025 : Blo 358757 609025 := bstep (se 2 (by rfl) ⟨228384, by rfl⟩ : syracuseStep 609025 = 456769) B456769
theorem B543491 : Blo 358757 543491 := bstep (se 1 (by rfl) ⟨407618, by rfl⟩ : syracuseStep 543491 = 815237) B815237
theorem B543521 : Blo 358757 543521 := bstep (se 2 (by rfl) ⟨203820, by rfl⟩ : syracuseStep 543521 = 407641) B407641
theorem B609059 : Blo 358757 609059 := bstep (se 1 (by rfl) ⟨456794, by rfl⟩ : syracuseStep 609059 = 913589) B913589
theorem B543539 : Blo 358757 543539 := bstep (se 1 (by rfl) ⟨407654, by rfl⟩ : syracuseStep 543539 = 815309) B815309
theorem B5327669 : Blo 358757 5327669 := bstep (se 5 (by rfl) ⟨249734, by rfl⟩ : syracuseStep 5327669 = 499469) B499469
theorem B707395 : Blo 358757 707395 := bstep (se 1 (by rfl) ⟨530546, by rfl⟩ : syracuseStep 707395 = 1061093) B1061093
theorem B1395533 : Blo 358757 1395533 := bstep (se 3 (by rfl) ⟨261662, by rfl⟩ : syracuseStep 1395533 = 523325) B523325
theorem B543569 : Blo 358757 543569 := bstep (se 2 (by rfl) ⟨203838, by rfl⟩ : syracuseStep 543569 = 407677) B407677
theorem B543587 : Blo 358757 543587 := bstep (se 1 (by rfl) ⟨407690, by rfl⟩ : syracuseStep 543587 = 815381) B815381
theorem B543617 : Blo 358757 543617 := bstep (se 2 (by rfl) ⟨203856, by rfl⟩ : syracuseStep 543617 = 407713) B407713
theorem B543635 : Blo 358757 543635 := bstep (se 1 (by rfl) ⟨407726, by rfl⟩ : syracuseStep 543635 = 815453) B815453
theorem B1362851 : Blo 358757 1362851 := bstep (se 1 (by rfl) ⟨1022138, by rfl⟩ : syracuseStep 1362851 = 2044277) B2044277
theorem B609187 : Blo 358757 609187 := bstep (se 1 (by rfl) ⟨456890, by rfl⟩ : syracuseStep 609187 = 913781) B913781
theorem B1362865 : Blo 358757 1362865 := bstep (se 2 (by rfl) ⟨511074, by rfl⟩ : syracuseStep 1362865 = 1022149) B1022149
theorem B543665 : Blo 358757 543665 := bstep (se 2 (by rfl) ⟨203874, by rfl⟩ : syracuseStep 543665 = 407749) B407749
theorem B543683 : Blo 358757 543683 := bstep (se 1 (by rfl) ⟨407762, by rfl⟩ : syracuseStep 543683 = 815525) B815525
theorem B543713 : Blo 358757 543713 := bstep (se 2 (by rfl) ⟨203892, by rfl⟩ : syracuseStep 543713 = 407785) B407785
theorem B510961 : Blo 358757 510961 := bstep (se 2 (by rfl) ⟨191610, by rfl⟩ : syracuseStep 510961 = 383221) B383221
theorem B576497 : Blo 358757 576497 := bstep (se 2 (by rfl) ⟨216186, by rfl⟩ : syracuseStep 576497 = 432373) B432373
theorem B543731 : Blo 358757 543731 := bstep (se 1 (by rfl) ⟨407798, by rfl⟩ : syracuseStep 543731 = 815597) B815597
theorem B1166339 : Blo 358757 1166339 := bstep (se 1 (by rfl) ⟨874754, by rfl⟩ : syracuseStep 1166339 = 1749509) B1749509
theorem B543761 : Blo 358757 543761 := bstep (se 2 (by rfl) ⟨203910, by rfl⟩ : syracuseStep 543761 = 407821) B407821
theorem B510995 : Blo 358757 510995 := bstep (se 1 (by rfl) ⟨383246, by rfl⟩ : syracuseStep 510995 = 766493) B766493
theorem B1428515 : Blo 358757 1428515 := bstep (se 1 (by rfl) ⟨1071386, by rfl⟩ : syracuseStep 1428515 = 2142773) B2142773
theorem B543779 : Blo 358757 543779 := bstep (se 1 (by rfl) ⟨407834, by rfl⟩ : syracuseStep 543779 = 815669) B815669
theorem B609329 : Blo 358757 609329 := bstep (se 2 (by rfl) ⟨228498, by rfl⟩ : syracuseStep 609329 = 456997) B456997
theorem B543809 : Blo 358757 543809 := bstep (se 2 (by rfl) ⟨203928, by rfl⟩ : syracuseStep 543809 = 407857) B407857
theorem B543827 : Blo 358757 543827 := bstep (se 1 (by rfl) ⟨407870, by rfl⟩ : syracuseStep 543827 = 815741) B815741
theorem B412771 : Blo 358757 412771 := bstep (se 1 (by rfl) ⟨309578, by rfl⟩ : syracuseStep 412771 = 619157) B619157
theorem B543857 : Blo 358757 543857 := bstep (se 2 (by rfl) ⟨203946, by rfl⟩ : syracuseStep 543857 = 407893) B407893
theorem B543875 : Blo 358757 543875 := bstep (se 1 (by rfl) ⟨407906, by rfl⟩ : syracuseStep 543875 = 815813) B815813
theorem B543905 : Blo 358757 543905 := bstep (se 2 (by rfl) ⟨203964, by rfl⟩ : syracuseStep 543905 = 407929) B407929
theorem B609457 : Blo 358757 609457 := bstep (se 2 (by rfl) ⟨228546, by rfl⟩ : syracuseStep 609457 = 457093) B457093
theorem B543923 : Blo 358757 543923 := bstep (se 1 (by rfl) ⟨407942, by rfl⟩ : syracuseStep 543923 = 815885) B815885
theorem B543953 : Blo 358757 543953 := bstep (se 2 (by rfl) ⟨203982, by rfl⟩ : syracuseStep 543953 = 407965) B407965
theorem B609491 : Blo 358757 609491 := bstep (se 1 (by rfl) ⟨457118, by rfl⟩ : syracuseStep 609491 = 914237) B914237
theorem B543971 : Blo 358757 543971 := bstep (se 1 (by rfl) ⟨407978, by rfl⟩ : syracuseStep 543971 = 815957) B815957
theorem B544001 : Blo 358757 544001 := bstep (se 2 (by rfl) ⟨204000, by rfl⟩ : syracuseStep 544001 = 408001) B408001
theorem B544019 : Blo 358757 544019 := bstep (se 1 (by rfl) ⟨408014, by rfl⟩ : syracuseStep 544019 = 816029) B816029
theorem B544049 : Blo 358757 544049 := bstep (se 2 (by rfl) ⟨204018, by rfl⟩ : syracuseStep 544049 = 408037) B408037
theorem B544067 : Blo 358757 544067 := bstep (se 1 (by rfl) ⟨408050, by rfl⟩ : syracuseStep 544067 = 816101) B816101
theorem B609619 : Blo 358757 609619 := bstep (se 1 (by rfl) ⟨457214, by rfl⟩ : syracuseStep 609619 = 914429) B914429
theorem B544097 : Blo 358757 544097 := bstep (se 2 (by rfl) ⟨204036, by rfl⟩ : syracuseStep 544097 = 408073) B408073
theorem B544115 : Blo 358757 544115 := bstep (se 1 (by rfl) ⟨408086, by rfl⟩ : syracuseStep 544115 = 816173) B816173
theorem B609761 : Blo 358757 609761 := bstep (se 2 (by rfl) ⟨228660, by rfl⟩ : syracuseStep 609761 = 457321) B457321
theorem B970289 : Blo 358757 970289 := bstep (se 2 (by rfl) ⟨363858, by rfl⟩ : syracuseStep 970289 = 727717) B727717
theorem B511553 : Blo 358757 511553 := bstep (se 2 (by rfl) ⟨191832, by rfl⟩ : syracuseStep 511553 = 383665) B383665
theorem B609889 : Blo 358757 609889 := bstep (se 2 (by rfl) ⟨228708, by rfl⟩ : syracuseStep 609889 = 457417) B457417
theorem B609923 : Blo 358757 609923 := bstep (se 1 (by rfl) ⟨457442, by rfl⟩ : syracuseStep 609923 = 914885) B914885
theorem B511633 : Blo 358757 511633 := bstep (se 2 (by rfl) ⟨191862, by rfl⟩ : syracuseStep 511633 = 383725) B383725
theorem B1756835 : Blo 358757 1756835 := bstep (se 1 (by rfl) ⟨1317626, by rfl⟩ : syracuseStep 1756835 = 2635253) B2635253
theorem B2182853 : Blo 358757 2182853 := bstep (se 4 (by rfl) ⟨204642, by rfl⟩ : syracuseStep 2182853 = 409285) B409285
theorem B610051 : Blo 358757 610051 := bstep (se 1 (by rfl) ⟨457538, by rfl⟩ : syracuseStep 610051 = 915077) B915077
theorem B773891 : Blo 358757 773891 := bstep (se 1 (by rfl) ⟨580418, by rfl⟩ : syracuseStep 773891 = 1160837) B1160837
theorem B1822499 : Blo 358757 1822499 := bstep (se 1 (by rfl) ⟨1366874, by rfl⟩ : syracuseStep 1822499 = 2733749) B2733749
theorem B577363 : Blo 358757 577363 := bstep (se 1 (by rfl) ⟨433022, by rfl⟩ : syracuseStep 577363 = 866045) B866045
theorem B2740067 : Blo 358757 2740067 := bstep (se 1 (by rfl) ⟨2055050, by rfl⟩ : syracuseStep 2740067 = 4110101) B4110101
theorem B610193 : Blo 358757 610193 := bstep (se 2 (by rfl) ⟨228822, by rfl⟩ : syracuseStep 610193 = 457645) B457645
theorem B610321 : Blo 358757 610321 := bstep (se 2 (by rfl) ⟨228870, by rfl⟩ : syracuseStep 610321 = 457741) B457741
theorem B610355 : Blo 358757 610355 := bstep (se 1 (by rfl) ⟨457766, by rfl⟩ : syracuseStep 610355 = 915533) B915533
theorem B577619 : Blo 358757 577619 := bstep (se 1 (by rfl) ⟨433214, by rfl⟩ : syracuseStep 577619 = 866429) B866429
theorem B1101937 : Blo 358757 1101937 := bstep (se 2 (by rfl) ⟨413226, by rfl⟩ : syracuseStep 1101937 = 826453) B826453
theorem B6312077 : Blo 358757 6312077 := bstep (se 3 (by rfl) ⟨1183514, by rfl⟩ : syracuseStep 6312077 = 2367029) B2367029
theorem B610483 : Blo 358757 610483 := bstep (se 1 (by rfl) ⟨457862, by rfl⟩ : syracuseStep 610483 = 915725) B915725
theorem B774353 : Blo 358757 774353 := bstep (se 2 (by rfl) ⟨290382, by rfl⟩ : syracuseStep 774353 = 580765) B580765
theorem B1102061 : Blo 358757 1102061 := bstep (se 3 (by rfl) ⟨206636, by rfl⟩ : syracuseStep 1102061 = 413273) B413273
theorem B2937073 : Blo 358757 2937073 := bstep (se 2 (by rfl) ⟨1101402, by rfl⟩ : syracuseStep 2937073 = 2202805) B2202805
theorem B610625 : Blo 358757 610625 := bstep (se 2 (by rfl) ⟨228984, by rfl⟩ : syracuseStep 610625 = 457969) B457969
theorem B1364323 : Blo 358757 1364323 := bstep (se 1 (by rfl) ⟨1023242, by rfl⟩ : syracuseStep 1364323 = 2046485) B2046485
theorem B3297635 : Blo 358757 3297635 := bstep (se 1 (by rfl) ⟨2473226, by rfl⟩ : syracuseStep 3297635 = 4946453) B4946453
theorem B807281 : Blo 358757 807281 := bstep (se 2 (by rfl) ⟨302730, by rfl⟩ : syracuseStep 807281 = 605461) B605461
theorem B2183537 : Blo 358757 2183537 := bstep (se 2 (by rfl) ⟨818826, by rfl⟩ : syracuseStep 2183537 = 1637653) B1637653
theorem B807299 : Blo 358757 807299 := bstep (se 1 (by rfl) ⟨605474, by rfl⟩ : syracuseStep 807299 = 1210949) B1210949
theorem B512419 : Blo 358757 512419 := bstep (se 1 (by rfl) ⟨384314, by rfl⟩ : syracuseStep 512419 = 768629) B768629
theorem B610753 : Blo 358757 610753 := bstep (se 2 (by rfl) ⟨229032, by rfl⟩ : syracuseStep 610753 = 458065) B458065
theorem B610787 : Blo 358757 610787 := bstep (se 1 (by rfl) ⟨458090, by rfl⟩ : syracuseStep 610787 = 916181) B916181
theorem B1167949 : Blo 358757 1167949 := bstep (se 3 (by rfl) ⟨218990, by rfl⟩ : syracuseStep 1167949 = 437981) B437981
theorem B1823309 : Blo 358757 1823309 := bstep (se 3 (by rfl) ⟨341870, by rfl⟩ : syracuseStep 1823309 = 683741) B683741
theorem B610915 : Blo 358757 610915 := bstep (se 1 (by rfl) ⟨458186, by rfl⟩ : syracuseStep 610915 = 916373) B916373
theorem B807569 : Blo 358757 807569 := bstep (se 2 (by rfl) ⟨302838, by rfl⟩ : syracuseStep 807569 = 605677) B605677
theorem B807587 : Blo 358757 807587 := bstep (se 1 (by rfl) ⟨605690, by rfl⟩ : syracuseStep 807587 = 1211381) B1211381
theorem B611057 : Blo 358757 611057 := bstep (se 2 (by rfl) ⟨229146, by rfl⟩ : syracuseStep 611057 = 458293) B458293
theorem B611185 : Blo 358757 611185 := bstep (se 2 (by rfl) ⟨229194, by rfl⟩ : syracuseStep 611185 = 458389) B458389
theorem B512897 : Blo 358757 512897 := bstep (se 2 (by rfl) ⟨192336, by rfl⟩ : syracuseStep 512897 = 384673) B384673
theorem B1299341 : Blo 358757 1299341 := bstep (se 3 (by rfl) ⟨243626, by rfl⟩ : syracuseStep 1299341 = 487253) B487253
theorem B611219 : Blo 358757 611219 := bstep (se 1 (by rfl) ⟨458414, by rfl⟩ : syracuseStep 611219 = 916829) B916829
theorem B807857 : Blo 358757 807857 := bstep (se 2 (by rfl) ⟨302946, by rfl⟩ : syracuseStep 807857 = 605893) B605893
theorem B807875 : Blo 358757 807875 := bstep (se 1 (by rfl) ⟨605906, by rfl⟩ : syracuseStep 807875 = 1211813) B1211813
theorem B2315213 : Blo 358757 2315213 := bstep (se 3 (by rfl) ⟨434102, by rfl⟩ : syracuseStep 2315213 = 868205) B868205
theorem B513011 : Blo 358757 513011 := bstep (se 1 (by rfl) ⟨384758, by rfl⟩ : syracuseStep 513011 = 769517) B769517
theorem B611347 : Blo 358757 611347 := bstep (se 1 (by rfl) ⟨458510, by rfl⟩ : syracuseStep 611347 = 917021) B917021
theorem B578593 : Blo 358757 578593 := bstep (se 2 (by rfl) ⟨216972, by rfl⟩ : syracuseStep 578593 = 433945) B433945
theorem B1725475 : Blo 358757 1725475 := bstep (se 1 (by rfl) ⟨1294106, by rfl⟩ : syracuseStep 1725475 = 2588213) B2588213
theorem B513091 : Blo 358757 513091 := bstep (se 1 (by rfl) ⟨384818, by rfl⟩ : syracuseStep 513091 = 769637) B769637
theorem B611489 : Blo 358757 611489 := bstep (se 2 (by rfl) ⟨229308, by rfl⟩ : syracuseStep 611489 = 458617) B458617
theorem B808145 : Blo 358757 808145 := bstep (se 2 (by rfl) ⟨303054, by rfl⟩ : syracuseStep 808145 = 606109) B606109
theorem B808163 : Blo 358757 808163 := bstep (se 1 (by rfl) ⟨606122, by rfl⟩ : syracuseStep 808163 = 1212245) B1212245
theorem B611617 : Blo 358757 611617 := bstep (se 2 (by rfl) ⟨229356, by rfl⟩ : syracuseStep 611617 = 458713) B458713
theorem B611651 : Blo 358757 611651 := bstep (se 1 (by rfl) ⟨458738, by rfl⟩ : syracuseStep 611651 = 917477) B917477
theorem B611779 : Blo 358757 611779 := bstep (se 1 (by rfl) ⟨458834, by rfl⟩ : syracuseStep 611779 = 917669) B917669
theorem B808433 : Blo 358757 808433 := bstep (se 2 (by rfl) ⟨303162, by rfl⟩ : syracuseStep 808433 = 606325) B606325
theorem B808451 : Blo 358757 808451 := bstep (se 1 (by rfl) ⟨606338, by rfl⟩ : syracuseStep 808451 = 1212677) B1212677
theorem B611921 : Blo 358757 611921 := bstep (se 2 (by rfl) ⟨229470, by rfl⟩ : syracuseStep 611921 = 458941) B458941
theorem B2184803 : Blo 358757 2184803 := bstep (se 1 (by rfl) ⟨1638602, by rfl⟩ : syracuseStep 2184803 = 3277205) B3277205
theorem B513649 : Blo 358757 513649 := bstep (se 2 (by rfl) ⟨192618, by rfl⟩ : syracuseStep 513649 = 385237) B385237
theorem B612049 : Blo 358757 612049 := bstep (se 2 (by rfl) ⟨229518, by rfl⟩ : syracuseStep 612049 = 459037) B459037
theorem B972515 : Blo 358757 972515 := bstep (se 1 (by rfl) ⟨729386, by rfl⟩ : syracuseStep 972515 = 1458773) B1458773
theorem B612083 : Blo 358757 612083 := bstep (se 1 (by rfl) ⟨459062, by rfl⟩ : syracuseStep 612083 = 918125) B918125
theorem B808721 : Blo 358757 808721 := bstep (se 2 (by rfl) ⟨303270, by rfl⟩ : syracuseStep 808721 = 606541) B606541
theorem B808739 : Blo 358757 808739 := bstep (se 1 (by rfl) ⟨606554, by rfl⟩ : syracuseStep 808739 = 1213109) B1213109
theorem B2053957 : Blo 358757 2053957 := bstep (se 4 (by rfl) ⟨192558, by rfl⟩ : syracuseStep 2053957 = 385117) B385117
theorem B579521 : Blo 358757 579521 := bstep (se 2 (by rfl) ⟨217320, by rfl⟩ : syracuseStep 579521 = 434641) B434641
theorem B809009 : Blo 358757 809009 := bstep (se 2 (by rfl) ⟨303378, by rfl⟩ : syracuseStep 809009 = 606757) B606757
theorem B546881 : Blo 358757 546881 := bstep (se 2 (by rfl) ⟨205080, by rfl⟩ : syracuseStep 546881 = 410161) B410161
theorem B809027 : Blo 358757 809027 := bstep (se 1 (by rfl) ⟨606770, by rfl⟩ : syracuseStep 809027 = 1213541) B1213541
theorem B514355 : Blo 358757 514355 := bstep (se 1 (by rfl) ⟨385766, by rfl⟩ : syracuseStep 514355 = 771533) B771533
theorem B809297 : Blo 358757 809297 := bstep (se 2 (by rfl) ⟨303486, by rfl⟩ : syracuseStep 809297 = 606973) B606973
theorem B809315 : Blo 358757 809315 := bstep (se 1 (by rfl) ⟨606986, by rfl⟩ : syracuseStep 809315 = 1213973) B1213973
theorem B3135971 : Blo 358757 3135971 := bstep (se 1 (by rfl) ⟨2351978, by rfl⟩ : syracuseStep 3135971 = 4703957) B4703957
theorem B3299825 : Blo 358757 3299825 := bstep (se 2 (by rfl) ⟨1237434, by rfl⟩ : syracuseStep 3299825 = 2474869) B2474869
theorem B1366541 : Blo 358757 1366541 := bstep (se 3 (by rfl) ⟨256226, by rfl⟩ : syracuseStep 1366541 = 512453) B512453
theorem B809585 : Blo 358757 809585 := bstep (se 2 (by rfl) ⟨303594, by rfl⟩ : syracuseStep 809585 = 607189) B607189
theorem B809603 : Blo 358757 809603 := bstep (se 1 (by rfl) ⟨607202, by rfl⟩ : syracuseStep 809603 = 1214405) B1214405
theorem B2939533 : Blo 358757 2939533 := bstep (se 3 (by rfl) ⟨551162, by rfl⟩ : syracuseStep 2939533 = 1102325) B1102325
theorem B580355 : Blo 358757 580355 := bstep (se 1 (by rfl) ⟨435266, by rfl⟩ : syracuseStep 580355 = 870533) B870533
theorem B580387 : Blo 358757 580387 := bstep (se 1 (by rfl) ⟨435290, by rfl⟩ : syracuseStep 580387 = 870581) B870581
theorem B908131 : Blo 358757 908131 := bstep (se 1 (by rfl) ⟨681098, by rfl⟩ : syracuseStep 908131 = 1362197) B1362197
theorem B1465229 : Blo 358757 1465229 := bstep (se 3 (by rfl) ⟨274730, by rfl⟩ : syracuseStep 1465229 = 549461) B549461
theorem B809873 : Blo 358757 809873 := bstep (se 2 (by rfl) ⟨303702, by rfl⟩ : syracuseStep 809873 = 607405) B607405
theorem B809891 : Blo 358757 809891 := bstep (se 1 (by rfl) ⟨607418, by rfl⟩ : syracuseStep 809891 = 1214837) B1214837
theorem B514993 : Blo 358757 514993 := bstep (se 2 (by rfl) ⟨193122, by rfl⟩ : syracuseStep 514993 = 386245) B386245
theorem B1039331 : Blo 358757 1039331 := bstep (se 1 (by rfl) ⟨779498, by rfl⟩ : syracuseStep 1039331 = 1558997) B1558997
theorem B908273 : Blo 358757 908273 := bstep (se 2 (by rfl) ⟨340602, by rfl⟩ : syracuseStep 908273 = 681205) B681205
theorem B515107 : Blo 358757 515107 := bstep (se 1 (by rfl) ⟨386330, by rfl⟩ : syracuseStep 515107 = 772661) B772661
theorem B810161 : Blo 358757 810161 := bstep (se 2 (by rfl) ⟨303810, by rfl⟩ : syracuseStep 810161 = 607621) B607621
theorem B810179 : Blo 358757 810179 := bstep (se 1 (by rfl) ⟨607634, by rfl⟩ : syracuseStep 810179 = 1215269) B1215269
theorem B974051 : Blo 358757 974051 := bstep (se 1 (by rfl) ⟨730538, by rfl⟩ : syracuseStep 974051 = 1461077) B1461077
theorem B384259 : Blo 358757 384259 := bstep (se 1 (by rfl) ⟨288194, by rfl⟩ : syracuseStep 384259 = 576389) B576389
theorem B9330061 : Blo 358757 9330061 := bstep (se 3 (by rfl) ⟨1749386, by rfl⟩ : syracuseStep 9330061 = 3498773) B3498773
theorem B4709773 : Blo 358757 4709773 := bstep (se 3 (by rfl) ⟨883082, by rfl⟩ : syracuseStep 4709773 = 1766165) B1766165
theorem B1826225 : Blo 358757 1826225 := bstep (se 2 (by rfl) ⟨684834, by rfl⟩ : syracuseStep 1826225 = 1369669) B1369669
theorem B810449 : Blo 358757 810449 := bstep (se 2 (by rfl) ⟨303918, by rfl⟩ : syracuseStep 810449 = 607837) B607837
theorem B810467 : Blo 358757 810467 := bstep (se 1 (by rfl) ⟨607850, by rfl⟩ : syracuseStep 810467 = 1215701) B1215701
theorem B384707 : Blo 358757 384707 := bstep (se 1 (by rfl) ⟨288530, by rfl⟩ : syracuseStep 384707 = 577061) B577061
theorem B1892045 : Blo 358757 1892045 := bstep (se 3 (by rfl) ⟨354758, by rfl⟩ : syracuseStep 1892045 = 709517) B709517
theorem B2186993 : Blo 358757 2186993 := bstep (se 2 (by rfl) ⟨820122, by rfl⟩ : syracuseStep 2186993 = 1640245) B1640245
theorem B810737 : Blo 358757 810737 := bstep (se 2 (by rfl) ⟨304026, by rfl⟩ : syracuseStep 810737 = 608053) B608053
theorem B810755 : Blo 358757 810755 := bstep (se 1 (by rfl) ⟨608066, by rfl⟩ : syracuseStep 810755 = 1216133) B1216133
theorem B2055941 : Blo 358757 2055941 := bstep (se 4 (by rfl) ⟨192744, by rfl⟩ : syracuseStep 2055941 = 385489) B385489
theorem B647075 : Blo 358757 647075 := bstep (se 1 (by rfl) ⟨485306, by rfl⟩ : syracuseStep 647075 = 970613) B970613
theorem B909265 : Blo 358757 909265 := bstep (se 2 (by rfl) ⟨340974, by rfl⟩ : syracuseStep 909265 = 681949) B681949
theorem B2318341 : Blo 358757 2318341 := bstep (se 4 (by rfl) ⟨217344, by rfl⟩ : syracuseStep 2318341 = 434689) B434689
theorem B811025 : Blo 358757 811025 := bstep (se 2 (by rfl) ⟨304134, by rfl⟩ : syracuseStep 811025 = 608269) B608269
theorem B811043 : Blo 358757 811043 := bstep (se 1 (by rfl) ⟨608282, by rfl⟩ : syracuseStep 811043 = 1216565) B1216565
theorem B909539 : Blo 358757 909539 := bstep (se 1 (by rfl) ⟨682154, by rfl⟩ : syracuseStep 909539 = 1364309) B1364309
theorem B811313 : Blo 358757 811313 := bstep (se 2 (by rfl) ⟨304242, by rfl⟩ : syracuseStep 811313 = 608485) B608485
theorem B811331 : Blo 358757 811331 := bstep (se 1 (by rfl) ⟨608498, by rfl⟩ : syracuseStep 811331 = 1216997) B1216997
theorem B549217 : Blo 358757 549217 := bstep (se 2 (by rfl) ⟨205956, by rfl⟩ : syracuseStep 549217 = 411913) B411913
theorem B1565027 : Blo 358757 1565027 := bstep (se 1 (by rfl) ⟨1173770, by rfl⟩ : syracuseStep 1565027 = 2347541) B2347541
theorem B516451 : Blo 358757 516451 := bstep (se 1 (by rfl) ⟨387338, by rfl⟩ : syracuseStep 516451 = 774677) B774677
theorem B909731 : Blo 358757 909731 := bstep (se 1 (by rfl) ⟨682298, by rfl⟩ : syracuseStep 909731 = 1364597) B1364597
theorem B811601 : Blo 358757 811601 := bstep (se 2 (by rfl) ⟨304350, by rfl⟩ : syracuseStep 811601 = 608701) B608701
theorem B3465827 : Blo 358757 3465827 := bstep (se 1 (by rfl) ⟨2599370, by rfl⟩ : syracuseStep 3465827 = 5198741) B5198741
theorem B811619 : Blo 358757 811619 := bstep (se 1 (by rfl) ⟨608714, by rfl⟩ : syracuseStep 811619 = 1217429) B1217429
theorem B2187917 : Blo 358757 2187917 := bstep (se 3 (by rfl) ⟨410234, by rfl⟩ : syracuseStep 2187917 = 820469) B820469
theorem B549649 : Blo 358757 549649 := bstep (se 2 (by rfl) ⟨206118, by rfl⟩ : syracuseStep 549649 = 412237) B412237
theorem B1827683 : Blo 358757 1827683 := bstep (se 1 (by rfl) ⟨1370762, by rfl⟩ : syracuseStep 1827683 = 2741525) B2741525
theorem B811889 : Blo 358757 811889 := bstep (se 2 (by rfl) ⟨304458, by rfl⟩ : syracuseStep 811889 = 608917) B608917
theorem B811907 : Blo 358757 811907 := bstep (se 1 (by rfl) ⟨608930, by rfl⟩ : syracuseStep 811907 = 1217861) B1217861
theorem B386083 : Blo 358757 386083 := bstep (se 1 (by rfl) ⟨289562, by rfl⟩ : syracuseStep 386083 = 579125) B579125
theorem B2745413 : Blo 358757 2745413 := bstep (se 4 (by rfl) ⟨257382, by rfl⟩ : syracuseStep 2745413 = 514765) B514765
theorem B812177 : Blo 358757 812177 := bstep (se 2 (by rfl) ⟨304566, by rfl⟩ : syracuseStep 812177 = 609133) B609133
theorem B812195 : Blo 358757 812195 := bstep (se 1 (by rfl) ⟨609146, by rfl⟩ : syracuseStep 812195 = 1218293) B1218293
theorem B1959173 : Blo 358757 1959173 := bstep (se 4 (by rfl) ⟨183672, by rfl⟩ : syracuseStep 1959173 = 367345) B367345
theorem B910673 : Blo 358757 910673 := bstep (se 2 (by rfl) ⟨341502, by rfl⟩ : syracuseStep 910673 = 683005) B683005
theorem B1369457 : Blo 358757 1369457 := bstep (se 2 (by rfl) ⟨513546, by rfl⟩ : syracuseStep 1369457 = 1027093) B1027093
theorem B910723 : Blo 358757 910723 := bstep (se 1 (by rfl) ⟨683042, by rfl⟩ : syracuseStep 910723 = 1366085) B1366085
theorem B3466637 : Blo 358757 3466637 := bstep (se 3 (by rfl) ⟨649994, by rfl⟩ : syracuseStep 3466637 = 1299989) B1299989
theorem B812465 : Blo 358757 812465 := bstep (se 2 (by rfl) ⟨304674, by rfl⟩ : syracuseStep 812465 = 609349) B609349
theorem B812483 : Blo 358757 812483 := bstep (se 1 (by rfl) ⟨609362, by rfl⟩ : syracuseStep 812483 = 1218725) B1218725
theorem B550385 : Blo 358757 550385 := bstep (se 2 (by rfl) ⟨206394, by rfl⟩ : syracuseStep 550385 = 412789) B412789
theorem B910865 : Blo 358757 910865 := bstep (se 2 (by rfl) ⟨341574, by rfl⟩ : syracuseStep 910865 = 683149) B683149
theorem B1828493 : Blo 358757 1828493 := bstep (se 3 (by rfl) ⟨342842, by rfl⟩ : syracuseStep 1828493 = 685685) B685685
theorem B550579 : Blo 358757 550579 := bstep (se 1 (by rfl) ⟨412934, by rfl⟩ : syracuseStep 550579 = 825869) B825869
theorem B648899 : Blo 358757 648899 := bstep (se 1 (by rfl) ⟨486674, by rfl⟩ : syracuseStep 648899 = 973349) B973349
theorem B1238723 : Blo 358757 1238723 := bstep (se 1 (by rfl) ⟨929042, by rfl⟩ : syracuseStep 1238723 = 1858085) B1858085
theorem B812753 : Blo 358757 812753 := bstep (se 2 (by rfl) ⟨304782, by rfl⟩ : syracuseStep 812753 = 609565) B609565
theorem B812771 : Blo 358757 812771 := bstep (se 1 (by rfl) ⟨609578, by rfl⟩ : syracuseStep 812771 = 1219157) B1219157
theorem B649073 : Blo 358757 649073 := bstep (se 2 (by rfl) ⟨243402, by rfl⟩ : syracuseStep 649073 = 486805) B486805
theorem B813041 : Blo 358757 813041 := bstep (se 2 (by rfl) ⟨304890, by rfl⟩ : syracuseStep 813041 = 609781) B609781
theorem B813059 : Blo 358757 813059 := bstep (se 1 (by rfl) ⟨609794, by rfl⟩ : syracuseStep 813059 = 1219589) B1219589
theorem B8775701 : Blo 358757 8775701 := bstep (se 6 (by rfl) ⟨205680, by rfl⟩ : syracuseStep 8775701 = 411361) B411361
theorem B682033 : Blo 358757 682033 := bstep (se 2 (by rfl) ⟨255762, by rfl⟩ : syracuseStep 682033 = 511525) B511525
theorem B616529 : Blo 358757 616529 := bstep (se 2 (by rfl) ⟨231198, by rfl⟩ : syracuseStep 616529 = 462397) B462397
theorem B813329 : Blo 358757 813329 := bstep (se 2 (by rfl) ⟨304998, by rfl⟩ : syracuseStep 813329 = 609997) B609997
theorem B387347 : Blo 358757 387347 := bstep (se 1 (by rfl) ⟨290510, by rfl⟩ : syracuseStep 387347 = 581021) B581021
theorem B813347 : Blo 358757 813347 := bstep (se 1 (by rfl) ⟨610010, by rfl⟩ : syracuseStep 813347 = 1220021) B1220021
theorem B682435 : Blo 358757 682435 := bstep (se 1 (by rfl) ⟨511826, by rfl⟩ : syracuseStep 682435 = 1023653) B1023653
theorem B682481 : Blo 358757 682481 := bstep (se 2 (by rfl) ⟨255930, by rfl⟩ : syracuseStep 682481 = 511861) B511861
theorem B911857 : Blo 358757 911857 := bstep (se 2 (by rfl) ⟨341946, by rfl⟩ : syracuseStep 911857 = 683893) B683893
theorem B813617 : Blo 358757 813617 := bstep (se 2 (by rfl) ⟨305106, by rfl⟩ : syracuseStep 813617 = 610213) B610213
theorem B813635 : Blo 358757 813635 := bstep (se 1 (by rfl) ⟨610226, by rfl⟩ : syracuseStep 813635 = 1220453) B1220453
theorem B912131 : Blo 358757 912131 := bstep (se 1 (by rfl) ⟨684098, by rfl⟩ : syracuseStep 912131 = 1368197) B1368197
theorem B682769 : Blo 358757 682769 := bstep (se 2 (by rfl) ⟨256038, by rfl⟩ : syracuseStep 682769 = 512077) B512077
theorem B1370915 : Blo 358757 1370915 := bstep (se 1 (by rfl) ⟨1028186, by rfl⟩ : syracuseStep 1370915 = 2056373) B2056373
theorem B813905 : Blo 358757 813905 := bstep (se 2 (by rfl) ⟨305214, by rfl⟩ : syracuseStep 813905 = 610429) B610429
theorem B813923 : Blo 358757 813923 := bstep (se 1 (by rfl) ⟨610442, by rfl⟩ : syracuseStep 813923 = 1220885) B1220885
theorem B912323 : Blo 358757 912323 := bstep (se 1 (by rfl) ⟨684242, by rfl⟩ : syracuseStep 912323 = 1368485) B1368485
theorem B3533765 : Blo 358757 3533765 := bstep (se 4 (by rfl) ⟨331290, by rfl⟩ : syracuseStep 3533765 = 662581) B662581
theorem B2190349 : Blo 358757 2190349 := bstep (se 3 (by rfl) ⟨410690, by rfl⟩ : syracuseStep 2190349 = 821381) B821381
theorem B814193 : Blo 358757 814193 := bstep (se 2 (by rfl) ⟨305322, by rfl⟩ : syracuseStep 814193 = 610645) B610645
theorem B814211 : Blo 358757 814211 := bstep (se 1 (by rfl) ⟨610658, by rfl⟩ : syracuseStep 814211 = 1221317) B1221317
theorem B1240337 : Blo 358757 1240337 := bstep (se 2 (by rfl) ⟨465126, by rfl⟩ : syracuseStep 1240337 = 930253) B930253
theorem B617843 : Blo 358757 617843 := bstep (se 1 (by rfl) ⟨463382, by rfl⟩ : syracuseStep 617843 = 926765) B926765
theorem B814481 : Blo 358757 814481 := bstep (se 2 (by rfl) ⟨305430, by rfl⟩ : syracuseStep 814481 = 610861) B610861
theorem B1535395 : Blo 358757 1535395 := bstep (se 1 (by rfl) ⟨1151546, by rfl⟩ : syracuseStep 1535395 = 2303093) B2303093
theorem B814499 : Blo 358757 814499 := bstep (se 1 (by rfl) ⟨610874, by rfl⟩ : syracuseStep 814499 = 1221749) B1221749
theorem B683491 : Blo 358757 683491 := bstep (se 1 (by rfl) ⟨512618, by rfl⟩ : syracuseStep 683491 = 1025237) B1025237
theorem B2059789 : Blo 358757 2059789 := bstep (se 3 (by rfl) ⟨386210, by rfl⟩ : syracuseStep 2059789 = 772421) B772421
theorem B454243 : Blo 358757 454243 := bstep (se 1 (by rfl) ⟨340682, by rfl⟩ : syracuseStep 454243 = 681365) B681365
theorem B1732259 : Blo 358757 1732259 := bstep (se 1 (by rfl) ⟨1299194, by rfl⟩ : syracuseStep 1732259 = 2598389) B2598389
theorem B814769 : Blo 358757 814769 := bstep (se 2 (by rfl) ⟨305538, by rfl⟩ : syracuseStep 814769 = 611077) B611077
theorem B454339 : Blo 358757 454339 := bstep (se 1 (by rfl) ⟨340754, by rfl⟩ : syracuseStep 454339 = 681509) B681509
theorem B814787 : Blo 358757 814787 := bstep (se 1 (by rfl) ⟨611090, by rfl⟩ : syracuseStep 814787 = 1222181) B1222181
theorem B1732337 : Blo 358757 1732337 := bstep (se 2 (by rfl) ⟨649626, by rfl⟩ : syracuseStep 1732337 = 1299253) B1299253
theorem B1371917 : Blo 358757 1371917 := bstep (se 3 (by rfl) ⟨257234, by rfl⟩ : syracuseStep 1371917 = 514469) B514469
theorem B913265 : Blo 358757 913265 := bstep (se 2 (by rfl) ⟨342474, by rfl⟩ : syracuseStep 913265 = 684949) B684949
theorem B683939 : Blo 358757 683939 := bstep (se 1 (by rfl) ⟨512954, by rfl⟩ : syracuseStep 683939 = 1025909) B1025909
theorem B913315 : Blo 358757 913315 := bstep (se 1 (by rfl) ⟨684986, by rfl⟩ : syracuseStep 913315 = 1369973) B1369973
theorem B815057 : Blo 358757 815057 := bstep (se 2 (by rfl) ⟨305646, by rfl⟩ : syracuseStep 815057 = 611293) B611293
theorem B815075 : Blo 358757 815075 := bstep (se 1 (by rfl) ⟨611306, by rfl⟩ : syracuseStep 815075 = 1222613) B1222613
theorem B913457 : Blo 358757 913457 := bstep (se 2 (by rfl) ⟨342546, by rfl⟩ : syracuseStep 913457 = 685093) B685093
theorem B454835 : Blo 358757 454835 := bstep (se 1 (by rfl) ⟨341126, by rfl⟩ : syracuseStep 454835 = 682253) B682253
theorem B684227 : Blo 358757 684227 := bstep (se 1 (by rfl) ⟨513170, by rfl⟩ : syracuseStep 684227 = 1026341) B1026341
theorem B815345 : Blo 358757 815345 := bstep (se 2 (by rfl) ⟨305754, by rfl⟩ : syracuseStep 815345 = 611509) B611509
theorem B815363 : Blo 358757 815363 := bstep (se 1 (by rfl) ⟨611522, by rfl⟩ : syracuseStep 815363 = 1223045) B1223045
theorem B880931 : Blo 358757 880931 := bstep (se 1 (by rfl) ⟨660698, by rfl⟩ : syracuseStep 880931 = 1321397) B1321397
theorem B487825 : Blo 358757 487825 := bstep (se 2 (by rfl) ⟨182934, by rfl⟩ : syracuseStep 487825 = 365869) B365869
theorem B1831409 : Blo 358757 1831409 := bstep (se 2 (by rfl) ⟨686778, by rfl⟩ : syracuseStep 1831409 = 1373557) B1373557
theorem B815633 : Blo 358757 815633 := bstep (se 2 (by rfl) ⟨305862, by rfl⟩ : syracuseStep 815633 = 611725) B611725
theorem B815651 : Blo 358757 815651 := bstep (se 1 (by rfl) ⟨611738, by rfl⟩ : syracuseStep 815651 = 1223477) B1223477
theorem B815921 : Blo 358757 815921 := bstep (se 2 (by rfl) ⟨305970, by rfl⟩ : syracuseStep 815921 = 611941) B611941
theorem B815939 : Blo 358757 815939 := bstep (se 1 (by rfl) ⟨611954, by rfl⟩ : syracuseStep 815939 = 1223909) B1223909
theorem B2323313 : Blo 358757 2323313 := bstep (se 2 (by rfl) ⟨871242, by rfl⟩ : syracuseStep 2323313 = 1742485) B1742485
theorem B455539 : Blo 358757 455539 := bstep (se 1 (by rfl) ⟨341654, by rfl⟩ : syracuseStep 455539 = 683309) B683309
theorem B455635 : Blo 358757 455635 := bstep (se 1 (by rfl) ⟨341726, by rfl⟩ : syracuseStep 455635 = 683453) B683453
theorem B914449 : Blo 358757 914449 := bstep (se 2 (by rfl) ⟨342918, by rfl⟩ : syracuseStep 914449 = 685837) B685837
theorem B685169 : Blo 358757 685169 := bstep (se 2 (by rfl) ⟨256938, by rfl⟩ : syracuseStep 685169 = 513877) B513877
theorem B914723 : Blo 358757 914723 := bstep (se 1 (by rfl) ⟨686042, by rfl⟩ : syracuseStep 914723 = 1372085) B1372085
theorem B488755 : Blo 358757 488755 := bstep (se 1 (by rfl) ⟨366566, by rfl⟩ : syracuseStep 488755 = 733133) B733133
theorem B1537393 : Blo 358757 1537393 := bstep (se 2 (by rfl) ⟨576522, by rfl⟩ : syracuseStep 1537393 = 1153045) B1153045
theorem B456131 : Blo 358757 456131 := bstep (se 1 (by rfl) ⟨342098, by rfl⟩ : syracuseStep 456131 = 684197) B684197
theorem B2061773 : Blo 358757 2061773 := bstep (se 3 (by rfl) ⟨386582, by rfl⟩ : syracuseStep 2061773 = 773165) B773165
theorem B914915 : Blo 358757 914915 := bstep (se 1 (by rfl) ⟨686186, by rfl⟩ : syracuseStep 914915 = 1372373) B1372373
theorem B783857 : Blo 358757 783857 := bstep (se 2 (by rfl) ⟨293946, by rfl⟩ : syracuseStep 783857 = 587893) B587893
theorem B1734257 : Blo 358757 1734257 := bstep (se 2 (by rfl) ⟨650346, by rfl⟩ : syracuseStep 1734257 = 1300693) B1300693
theorem B4159117 : Blo 358757 4159117 := bstep (se 3 (by rfl) ⟨779834, by rfl⟩ : syracuseStep 4159117 = 1559669) B1559669
theorem B1374029 : Blo 358757 1374029 := bstep (se 3 (by rfl) ⟨257630, by rfl⟩ : syracuseStep 1374029 = 515261) B515261
theorem B522067 : Blo 358757 522067 := bstep (se 1 (by rfl) ⟨391550, by rfl⟩ : syracuseStep 522067 = 783101) B783101
theorem B1832867 : Blo 358757 1832867 := bstep (se 1 (by rfl) ⟨1374650, by rfl⟩ : syracuseStep 1832867 = 2749301) B2749301
theorem B686065 : Blo 358757 686065 := bstep (se 2 (by rfl) ⟨257274, by rfl⟩ : syracuseStep 686065 = 514549) B514549
theorem B2488333 : Blo 358757 2488333 := bstep (se 3 (by rfl) ⟨466562, by rfl⟩ : syracuseStep 2488333 = 933125) B933125
theorem B456835 : Blo 358757 456835 := bstep (se 1 (by rfl) ⟨342626, by rfl⟩ : syracuseStep 456835 = 685253) B685253
theorem B1734797 : Blo 358757 1734797 := bstep (se 3 (by rfl) ⟨325274, by rfl⟩ : syracuseStep 1734797 = 650549) B650549
theorem B686225 : Blo 358757 686225 := bstep (se 2 (by rfl) ⟨257334, by rfl⟩ : syracuseStep 686225 = 514669) B514669
theorem B456931 : Blo 358757 456931 := bstep (se 1 (by rfl) ⟨342698, by rfl⟩ : syracuseStep 456931 = 685397) B685397
theorem B2062705 : Blo 358757 2062705 := bstep (se 2 (by rfl) ⟨773514, by rfl⟩ : syracuseStep 2062705 = 1547029) B1547029
theorem B358771 : Blo 358757 358771 := bstep (se 1 (by rfl) ⟨269078, by rfl⟩ : syracuseStep 358771 = 538157) B538157
theorem B358787 : Blo 358757 358787 := bstep (se 1 (by rfl) ⟨269090, by rfl⟩ : syracuseStep 358787 = 538181) B538181
theorem B915857 : Blo 358757 915857 := bstep (se 2 (by rfl) ⟨343446, by rfl⟩ : syracuseStep 915857 = 686893) B686893
theorem B358803 : Blo 358757 358803 := bstep (se 1 (by rfl) ⟨269102, by rfl⟩ : syracuseStep 358803 = 538205) B538205
theorem B358819 : Blo 358757 358819 := bstep (se 1 (by rfl) ⟨269114, by rfl⟩ : syracuseStep 358819 = 538229) B538229
theorem B358835 : Blo 358757 358835 := bstep (se 1 (by rfl) ⟨269126, by rfl⟩ : syracuseStep 358835 = 538253) B538253
theorem B358851 : Blo 358757 358851 := bstep (se 1 (by rfl) ⟨269138, by rfl⟩ : syracuseStep 358851 = 538277) B538277
theorem B915907 : Blo 358757 915907 := bstep (se 1 (by rfl) ⟨686930, by rfl⟩ : syracuseStep 915907 = 1373861) B1373861
theorem B358867 : Blo 358757 358867 := bstep (se 1 (by rfl) ⟨269150, by rfl⟩ : syracuseStep 358867 = 538301) B538301
theorem B358883 : Blo 358757 358883 := bstep (se 1 (by rfl) ⟨269162, by rfl⟩ : syracuseStep 358883 = 538325) B538325
theorem B358899 : Blo 358757 358899 := bstep (se 1 (by rfl) ⟨269174, by rfl⟩ : syracuseStep 358899 = 538349) B538349
theorem B358915 : Blo 358757 358915 := bstep (se 1 (by rfl) ⟨269186, by rfl⟩ : syracuseStep 358915 = 538373) B538373
theorem B358931 : Blo 358757 358931 := bstep (se 1 (by rfl) ⟨269198, by rfl⟩ : syracuseStep 358931 = 538397) B538397
theorem B358947 : Blo 358757 358947 := bstep (se 1 (by rfl) ⟨269210, by rfl⟩ : syracuseStep 358947 = 538421) B538421
theorem B686627 : Blo 358757 686627 := bstep (se 1 (by rfl) ⟨514970, by rfl⟩ : syracuseStep 686627 = 1029941) B1029941
theorem B358963 : Blo 358757 358963 := bstep (se 1 (by rfl) ⟨269222, by rfl⟩ : syracuseStep 358963 = 538445) B538445
theorem B358979 : Blo 358757 358979 := bstep (se 1 (by rfl) ⟨269234, by rfl⟩ : syracuseStep 358979 = 538469) B538469
theorem B916049 : Blo 358757 916049 := bstep (se 2 (by rfl) ⟨343518, by rfl⟩ : syracuseStep 916049 = 687037) B687037
theorem B358995 : Blo 358757 358995 := bstep (se 1 (by rfl) ⟨269246, by rfl⟩ : syracuseStep 358995 = 538493) B538493
theorem B359011 : Blo 358757 359011 := bstep (se 1 (by rfl) ⟨269258, by rfl⟩ : syracuseStep 359011 = 538517) B538517
theorem B1374833 : Blo 358757 1374833 := bstep (se 2 (by rfl) ⟨515562, by rfl⟩ : syracuseStep 1374833 = 1031125) B1031125
theorem B359027 : Blo 358757 359027 := bstep (se 1 (by rfl) ⟨269270, by rfl⟩ : syracuseStep 359027 = 538541) B538541
theorem B359043 : Blo 358757 359043 := bstep (se 1 (by rfl) ⟨269282, by rfl⟩ : syracuseStep 359043 = 538565) B538565
theorem B359059 : Blo 358757 359059 := bstep (se 1 (by rfl) ⟨269294, by rfl⟩ : syracuseStep 359059 = 538589) B538589
theorem B359075 : Blo 358757 359075 := bstep (se 1 (by rfl) ⟨269306, by rfl⟩ : syracuseStep 359075 = 538613) B538613
theorem B1211057 : Blo 358757 1211057 := bstep (se 2 (by rfl) ⟨454146, by rfl⟩ : syracuseStep 1211057 = 908293) B908293
theorem B359091 : Blo 358757 359091 := bstep (se 1 (by rfl) ⟨269318, by rfl⟩ : syracuseStep 359091 = 538637) B538637
theorem B359107 : Blo 358757 359107 := bstep (se 1 (by rfl) ⟨269330, by rfl⟩ : syracuseStep 359107 = 538661) B538661
theorem B1833677 : Blo 358757 1833677 := bstep (se 3 (by rfl) ⟨343814, by rfl⟩ : syracuseStep 1833677 = 687629) B687629
theorem B359123 : Blo 358757 359123 := bstep (se 1 (by rfl) ⟨269342, by rfl⟩ : syracuseStep 359123 = 538685) B538685
theorem B457427 : Blo 358757 457427 := bstep (se 1 (by rfl) ⟨343070, by rfl⟩ : syracuseStep 457427 = 686141) B686141
theorem B359139 : Blo 358757 359139 := bstep (se 1 (by rfl) ⟨269354, by rfl⟩ : syracuseStep 359139 = 538709) B538709
theorem B359155 : Blo 358757 359155 := bstep (se 1 (by rfl) ⟨269366, by rfl⟩ : syracuseStep 359155 = 538733) B538733
theorem B359171 : Blo 358757 359171 := bstep (se 1 (by rfl) ⟨269378, by rfl⟩ : syracuseStep 359171 = 538757) B538757
theorem B2751245 : Blo 358757 2751245 := bstep (se 3 (by rfl) ⟨515858, by rfl⟩ : syracuseStep 2751245 = 1031717) B1031717
theorem B359187 : Blo 358757 359187 := bstep (se 1 (by rfl) ⟨269390, by rfl⟩ : syracuseStep 359187 = 538781) B538781
theorem B359203 : Blo 358757 359203 := bstep (se 1 (by rfl) ⟨269402, by rfl⟩ : syracuseStep 359203 = 538805) B538805
theorem B359219 : Blo 358757 359219 := bstep (se 1 (by rfl) ⟨269414, by rfl⟩ : syracuseStep 359219 = 538829) B538829
theorem B359235 : Blo 358757 359235 := bstep (se 1 (by rfl) ⟨269426, by rfl⟩ : syracuseStep 359235 = 538853) B538853
theorem B359251 : Blo 358757 359251 := bstep (se 1 (by rfl) ⟨269438, by rfl⟩ : syracuseStep 359251 = 538877) B538877
theorem B359267 : Blo 358757 359267 := bstep (se 1 (by rfl) ⟨269450, by rfl⟩ : syracuseStep 359267 = 538901) B538901
theorem B359283 : Blo 358757 359283 := bstep (se 1 (by rfl) ⟨269462, by rfl⟩ : syracuseStep 359283 = 538925) B538925
theorem B359299 : Blo 358757 359299 := bstep (se 1 (by rfl) ⟨269474, by rfl⟩ : syracuseStep 359299 = 538949) B538949
theorem B359315 : Blo 358757 359315 := bstep (se 1 (by rfl) ⟨269486, by rfl⟩ : syracuseStep 359315 = 538973) B538973
theorem B359331 : Blo 358757 359331 := bstep (se 1 (by rfl) ⟨269498, by rfl⟩ : syracuseStep 359331 = 538997) B538997
theorem B359347 : Blo 358757 359347 := bstep (se 1 (by rfl) ⟨269510, by rfl⟩ : syracuseStep 359347 = 539021) B539021
theorem B359363 : Blo 358757 359363 := bstep (se 1 (by rfl) ⟨269522, by rfl⟩ : syracuseStep 359363 = 539045) B539045
theorem B359379 : Blo 358757 359379 := bstep (se 1 (by rfl) ⟨269534, by rfl⟩ : syracuseStep 359379 = 539069) B539069
theorem B359395 : Blo 358757 359395 := bstep (se 1 (by rfl) ⟨269546, by rfl⟩ : syracuseStep 359395 = 539093) B539093
theorem B359411 : Blo 358757 359411 := bstep (se 1 (by rfl) ⟨269558, by rfl⟩ : syracuseStep 359411 = 539117) B539117
theorem B359427 : Blo 358757 359427 := bstep (se 1 (by rfl) ⟨269570, by rfl⟩ : syracuseStep 359427 = 539141) B539141
theorem B359443 : Blo 358757 359443 := bstep (se 1 (by rfl) ⟨269582, by rfl⟩ : syracuseStep 359443 = 539165) B539165
theorem B359459 : Blo 358757 359459 := bstep (se 1 (by rfl) ⟨269594, by rfl⟩ : syracuseStep 359459 = 539189) B539189
theorem B359475 : Blo 358757 359475 := bstep (se 1 (by rfl) ⟨269606, by rfl⟩ : syracuseStep 359475 = 539213) B539213
theorem B359491 : Blo 358757 359491 := bstep (se 1 (by rfl) ⟨269618, by rfl⟩ : syracuseStep 359491 = 539237) B539237
theorem B359507 : Blo 358757 359507 := bstep (se 1 (by rfl) ⟨269630, by rfl⟩ : syracuseStep 359507 = 539261) B539261
theorem B359523 : Blo 358757 359523 := bstep (se 1 (by rfl) ⟨269642, by rfl⟩ : syracuseStep 359523 = 539285) B539285
theorem B359539 : Blo 358757 359539 := bstep (se 1 (by rfl) ⟨269654, by rfl⟩ : syracuseStep 359539 = 539309) B539309
theorem B359555 : Blo 358757 359555 := bstep (se 1 (by rfl) ⟨269666, by rfl⟩ : syracuseStep 359555 = 539333) B539333
theorem B359571 : Blo 358757 359571 := bstep (se 1 (by rfl) ⟨269678, by rfl⟩ : syracuseStep 359571 = 539357) B539357
theorem B359587 : Blo 358757 359587 := bstep (se 1 (by rfl) ⟨269690, by rfl⟩ : syracuseStep 359587 = 539381) B539381
theorem B359603 : Blo 358757 359603 := bstep (se 1 (by rfl) ⟨269702, by rfl⟩ : syracuseStep 359603 = 539405) B539405
theorem B359619 : Blo 358757 359619 := bstep (se 1 (by rfl) ⟨269714, by rfl⟩ : syracuseStep 359619 = 539429) B539429
theorem B1211597 : Blo 358757 1211597 := bstep (se 3 (by rfl) ⟨227174, by rfl⟩ : syracuseStep 1211597 = 454349) B454349
theorem B359635 : Blo 358757 359635 := bstep (se 1 (by rfl) ⟨269726, by rfl⟩ : syracuseStep 359635 = 539453) B539453
theorem B359651 : Blo 358757 359651 := bstep (se 1 (by rfl) ⟨269738, by rfl⟩ : syracuseStep 359651 = 539477) B539477
theorem B359667 : Blo 358757 359667 := bstep (se 1 (by rfl) ⟨269750, by rfl⟩ : syracuseStep 359667 = 539501) B539501
theorem B1211651 : Blo 358757 1211651 := bstep (se 1 (by rfl) ⟨908738, by rfl⟩ : syracuseStep 1211651 = 1817477) B1817477
theorem B359683 : Blo 358757 359683 := bstep (se 1 (by rfl) ⟨269762, by rfl⟩ : syracuseStep 359683 = 539525) B539525
theorem B1375501 : Blo 358757 1375501 := bstep (se 3 (by rfl) ⟨257906, by rfl⟩ : syracuseStep 1375501 = 515813) B515813
theorem B359699 : Blo 358757 359699 := bstep (se 1 (by rfl) ⟨269774, by rfl⟩ : syracuseStep 359699 = 539549) B539549
theorem B359715 : Blo 358757 359715 := bstep (se 1 (by rfl) ⟨269786, by rfl⟩ : syracuseStep 359715 = 539573) B539573
theorem B359731 : Blo 358757 359731 := bstep (se 1 (by rfl) ⟨269798, by rfl⟩ : syracuseStep 359731 = 539597) B539597
theorem B359747 : Blo 358757 359747 := bstep (se 1 (by rfl) ⟨269810, by rfl⟩ : syracuseStep 359747 = 539621) B539621
theorem B359763 : Blo 358757 359763 := bstep (se 1 (by rfl) ⟨269822, by rfl⟩ : syracuseStep 359763 = 539645) B539645
theorem B359779 : Blo 358757 359779 := bstep (se 1 (by rfl) ⟨269834, by rfl⟩ : syracuseStep 359779 = 539669) B539669
theorem B359795 : Blo 358757 359795 := bstep (se 1 (by rfl) ⟨269846, by rfl⟩ : syracuseStep 359795 = 539693) B539693
theorem B359811 : Blo 358757 359811 := bstep (se 1 (by rfl) ⟨269858, by rfl⟩ : syracuseStep 359811 = 539717) B539717
theorem B359827 : Blo 358757 359827 := bstep (se 1 (by rfl) ⟨269870, by rfl⟩ : syracuseStep 359827 = 539741) B539741
theorem B458131 : Blo 358757 458131 := bstep (se 1 (by rfl) ⟨343598, by rfl⟩ : syracuseStep 458131 = 687197) B687197
theorem B359843 : Blo 358757 359843 := bstep (se 1 (by rfl) ⟨269882, by rfl⟩ : syracuseStep 359843 = 539765) B539765
theorem B687523 : Blo 358757 687523 := bstep (se 1 (by rfl) ⟨515642, by rfl⟩ : syracuseStep 687523 = 1031285) B1031285
theorem B359859 : Blo 358757 359859 := bstep (se 1 (by rfl) ⟨269894, by rfl⟩ : syracuseStep 359859 = 539789) B539789
theorem B359875 : Blo 358757 359875 := bstep (se 1 (by rfl) ⟨269906, by rfl⟩ : syracuseStep 359875 = 539813) B539813
theorem B359891 : Blo 358757 359891 := bstep (se 1 (by rfl) ⟨269918, by rfl⟩ : syracuseStep 359891 = 539837) B539837
theorem B359907 : Blo 358757 359907 := bstep (se 1 (by rfl) ⟨269930, by rfl⟩ : syracuseStep 359907 = 539861) B539861
theorem B359923 : Blo 358757 359923 := bstep (se 1 (by rfl) ⟨269942, by rfl⟩ : syracuseStep 359923 = 539885) B539885
theorem B458227 : Blo 358757 458227 := bstep (se 1 (by rfl) ⟨343670, by rfl⟩ : syracuseStep 458227 = 687341) B687341
theorem B359939 : Blo 358757 359939 := bstep (se 1 (by rfl) ⟨269954, by rfl⟩ : syracuseStep 359939 = 539909) B539909
theorem B1211921 : Blo 358757 1211921 := bstep (se 2 (by rfl) ⟨454470, by rfl⟩ : syracuseStep 1211921 = 908941) B908941
theorem B359955 : Blo 358757 359955 := bstep (se 1 (by rfl) ⟨269966, by rfl⟩ : syracuseStep 359955 = 539933) B539933
theorem B9895445 : Blo 358757 9895445 := bstep (se 6 (by rfl) ⟨231924, by rfl⟩ : syracuseStep 9895445 = 463849) B463849
theorem B359971 : Blo 358757 359971 := bstep (se 1 (by rfl) ⟨269978, by rfl⟩ : syracuseStep 359971 = 539957) B539957
theorem B917041 : Blo 358757 917041 := bstep (se 2 (by rfl) ⟨343890, by rfl⟩ : syracuseStep 917041 = 687781) B687781
theorem B359987 : Blo 358757 359987 := bstep (se 1 (by rfl) ⟨269990, by rfl⟩ : syracuseStep 359987 = 539981) B539981
theorem B360003 : Blo 358757 360003 := bstep (se 1 (by rfl) ⟨270002, by rfl⟩ : syracuseStep 360003 = 540005) B540005
theorem B687683 : Blo 358757 687683 := bstep (se 1 (by rfl) ⟨515762, by rfl⟩ : syracuseStep 687683 = 1031525) B1031525
theorem B360019 : Blo 358757 360019 := bstep (se 1 (by rfl) ⟨270014, by rfl⟩ : syracuseStep 360019 = 540029) B540029
theorem B360035 : Blo 358757 360035 := bstep (se 1 (by rfl) ⟨270026, by rfl⟩ : syracuseStep 360035 = 540053) B540053
theorem B360051 : Blo 358757 360051 := bstep (se 1 (by rfl) ⟨270038, by rfl⟩ : syracuseStep 360051 = 540077) B540077
theorem B360067 : Blo 358757 360067 := bstep (se 1 (by rfl) ⟨270050, by rfl⟩ : syracuseStep 360067 = 540101) B540101
theorem B360083 : Blo 358757 360083 := bstep (se 1 (by rfl) ⟨270062, by rfl⟩ : syracuseStep 360083 = 540125) B540125
theorem B360099 : Blo 358757 360099 := bstep (se 1 (by rfl) ⟨270074, by rfl⟩ : syracuseStep 360099 = 540149) B540149
theorem B360115 : Blo 358757 360115 := bstep (se 1 (by rfl) ⟨270086, by rfl⟩ : syracuseStep 360115 = 540173) B540173
theorem B360131 : Blo 358757 360131 := bstep (se 1 (by rfl) ⟨270098, by rfl⟩ : syracuseStep 360131 = 540197) B540197
theorem B360147 : Blo 358757 360147 := bstep (se 1 (by rfl) ⟨270110, by rfl⟩ : syracuseStep 360147 = 540221) B540221
theorem B360163 : Blo 358757 360163 := bstep (se 1 (by rfl) ⟨270122, by rfl⟩ : syracuseStep 360163 = 540245) B540245
theorem B360179 : Blo 358757 360179 := bstep (se 1 (by rfl) ⟨270134, by rfl⟩ : syracuseStep 360179 = 540269) B540269
theorem B360195 : Blo 358757 360195 := bstep (se 1 (by rfl) ⟨270146, by rfl⟩ : syracuseStep 360195 = 540293) B540293
theorem B360211 : Blo 358757 360211 := bstep (se 1 (by rfl) ⟨270158, by rfl⟩ : syracuseStep 360211 = 540317) B540317
theorem B360227 : Blo 358757 360227 := bstep (se 1 (by rfl) ⟨270170, by rfl⟩ : syracuseStep 360227 = 540341) B540341
theorem B2064163 : Blo 358757 2064163 := bstep (se 1 (by rfl) ⟨1548122, by rfl⟩ : syracuseStep 2064163 = 3096245) B3096245
theorem B360243 : Blo 358757 360243 := bstep (se 1 (by rfl) ⟨270182, by rfl⟩ : syracuseStep 360243 = 540365) B540365
theorem B360259 : Blo 358757 360259 := bstep (se 1 (by rfl) ⟨270194, by rfl⟩ : syracuseStep 360259 = 540389) B540389
theorem B917315 : Blo 358757 917315 := bstep (se 1 (by rfl) ⟨687986, by rfl⟩ : syracuseStep 917315 = 1375973) B1375973
theorem B360275 : Blo 358757 360275 := bstep (se 1 (by rfl) ⟨270206, by rfl⟩ : syracuseStep 360275 = 540413) B540413
theorem B360291 : Blo 358757 360291 := bstep (se 1 (by rfl) ⟨270218, by rfl⟩ : syracuseStep 360291 = 540437) B540437
theorem B360307 : Blo 358757 360307 := bstep (se 1 (by rfl) ⟨270230, by rfl⟩ : syracuseStep 360307 = 540461) B540461
theorem B360323 : Blo 358757 360323 := bstep (se 1 (by rfl) ⟨270242, by rfl⟩ : syracuseStep 360323 = 540485) B540485
theorem B360339 : Blo 358757 360339 := bstep (se 1 (by rfl) ⟨270254, by rfl⟩ : syracuseStep 360339 = 540509) B540509
theorem B360355 : Blo 358757 360355 := bstep (se 1 (by rfl) ⟨270266, by rfl⟩ : syracuseStep 360355 = 540533) B540533
theorem B360371 : Blo 358757 360371 := bstep (se 1 (by rfl) ⟨270278, by rfl⟩ : syracuseStep 360371 = 540557) B540557
theorem B360387 : Blo 358757 360387 := bstep (se 1 (by rfl) ⟨270290, by rfl⟩ : syracuseStep 360387 = 540581) B540581
theorem B360403 : Blo 358757 360403 := bstep (se 1 (by rfl) ⟨270302, by rfl⟩ : syracuseStep 360403 = 540605) B540605
theorem B360419 : Blo 358757 360419 := bstep (se 1 (by rfl) ⟨270314, by rfl⟩ : syracuseStep 360419 = 540629) B540629
theorem B458723 : Blo 358757 458723 := bstep (se 1 (by rfl) ⟨344042, by rfl⟩ : syracuseStep 458723 = 688085) B688085
theorem B360435 : Blo 358757 360435 := bstep (se 1 (by rfl) ⟨270326, by rfl⟩ : syracuseStep 360435 = 540653) B540653
theorem B360459 : Blo 358757 360459 := bstep (se 1 (by rfl) ⟨270344, by rfl⟩ : syracuseStep 360459 = 540689) B540689
theorem B360471 : Blo 358757 360471 := bstep (se 1 (by rfl) ⟨270353, by rfl⟩ : syracuseStep 360471 = 540707) B540707
theorem B917527 : Blo 358757 917527 := bstep (se 1 (by rfl) ⟨688145, by rfl⟩ : syracuseStep 917527 = 1376291) B1376291
theorem B360491 : Blo 358757 360491 := bstep (se 1 (by rfl) ⟨270368, by rfl⟩ : syracuseStep 360491 = 540737) B540737
theorem B360503 : Blo 358757 360503 := bstep (se 1 (by rfl) ⟨270377, by rfl⟩ : syracuseStep 360503 = 540755) B540755
theorem B3276875 : Blo 358757 3276875 := bstep (se 1 (by rfl) ⟨2457656, by rfl⟩ : syracuseStep 3276875 = 4915313) B4915313
theorem B360523 : Blo 358757 360523 := bstep (se 1 (by rfl) ⟨270392, by rfl⟩ : syracuseStep 360523 = 540785) B540785
theorem B360535 : Blo 358757 360535 := bstep (se 1 (by rfl) ⟨270401, by rfl⟩ : syracuseStep 360535 = 540803) B540803
theorem B360555 : Blo 358757 360555 := bstep (se 1 (by rfl) ⟨270416, by rfl⟩ : syracuseStep 360555 = 540833) B540833
theorem B360567 : Blo 358757 360567 := bstep (se 1 (by rfl) ⟨270425, by rfl⟩ : syracuseStep 360567 = 540851) B540851
theorem B360587 : Blo 358757 360587 := bstep (se 1 (by rfl) ⟨270440, by rfl⟩ : syracuseStep 360587 = 540881) B540881
theorem B688267 : Blo 358757 688267 := bstep (se 1 (by rfl) ⟨516200, by rfl⟩ : syracuseStep 688267 = 1032401) B1032401
theorem B360599 : Blo 358757 360599 := bstep (se 1 (by rfl) ⟨270449, by rfl⟩ : syracuseStep 360599 = 540899) B540899
theorem B360619 : Blo 358757 360619 := bstep (se 1 (by rfl) ⟨270464, by rfl⟩ : syracuseStep 360619 = 540929) B540929
theorem B360631 : Blo 358757 360631 := bstep (se 1 (by rfl) ⟨270473, by rfl⟩ : syracuseStep 360631 = 540947) B540947
theorem B360651 : Blo 358757 360651 := bstep (se 1 (by rfl) ⟨270488, by rfl⟩ : syracuseStep 360651 = 540977) B540977
theorem B1376459 : Blo 358757 1376459 := bstep (se 1 (by rfl) ⟨1032344, by rfl⟩ : syracuseStep 1376459 = 2064689) B2064689
theorem B360663 : Blo 358757 360663 := bstep (se 1 (by rfl) ⟨270497, by rfl⟩ : syracuseStep 360663 = 540995) B540995
theorem B1376473 : Blo 358757 1376473 := bstep (se 2 (by rfl) ⟨516177, by rfl⟩ : syracuseStep 1376473 = 1032355) B1032355
theorem B360683 : Blo 358757 360683 := bstep (se 1 (by rfl) ⟨270512, by rfl⟩ : syracuseStep 360683 = 541025) B541025
theorem B360695 : Blo 358757 360695 := bstep (se 1 (by rfl) ⟨270521, by rfl⟩ : syracuseStep 360695 = 541043) B541043
theorem B360715 : Blo 358757 360715 := bstep (se 1 (by rfl) ⟨270536, by rfl⟩ : syracuseStep 360715 = 541073) B541073
theorem B360727 : Blo 358757 360727 := bstep (se 1 (by rfl) ⟨270545, by rfl⟩ : syracuseStep 360727 = 541091) B541091
theorem B360747 : Blo 358757 360747 := bstep (se 1 (by rfl) ⟨270560, by rfl⟩ : syracuseStep 360747 = 541121) B541121
theorem B360759 : Blo 358757 360759 := bstep (se 1 (by rfl) ⟨270569, by rfl⟩ : syracuseStep 360759 = 541139) B541139
theorem B360779 : Blo 358757 360779 := bstep (se 1 (by rfl) ⟨270584, by rfl⟩ : syracuseStep 360779 = 541169) B541169
theorem B360791 : Blo 358757 360791 := bstep (se 1 (by rfl) ⟨270593, by rfl⟩ : syracuseStep 360791 = 541187) B541187
theorem B360811 : Blo 358757 360811 := bstep (se 1 (by rfl) ⟨270608, by rfl⟩ : syracuseStep 360811 = 541217) B541217
theorem B360823 : Blo 358757 360823 := bstep (se 1 (by rfl) ⟨270617, by rfl⟩ : syracuseStep 360823 = 541235) B541235
theorem B360843 : Blo 358757 360843 := bstep (se 1 (by rfl) ⟨270632, by rfl⟩ : syracuseStep 360843 = 541265) B541265
theorem B360855 : Blo 358757 360855 := bstep (se 1 (by rfl) ⟨270641, by rfl⟩ : syracuseStep 360855 = 541283) B541283
theorem B360875 : Blo 358757 360875 := bstep (se 1 (by rfl) ⟨270656, by rfl⟩ : syracuseStep 360875 = 541313) B541313
theorem B360887 : Blo 358757 360887 := bstep (se 1 (by rfl) ⟨270665, by rfl⟩ : syracuseStep 360887 = 541331) B541331
theorem B360907 : Blo 358757 360907 := bstep (se 1 (by rfl) ⟨270680, by rfl⟩ : syracuseStep 360907 = 541361) B541361
theorem B917963 : Blo 358757 917963 := bstep (se 1 (by rfl) ⟨688472, by rfl⟩ : syracuseStep 917963 = 1376945) B1376945
theorem B360919 : Blo 358757 360919 := bstep (se 1 (by rfl) ⟨270689, by rfl⟩ : syracuseStep 360919 = 541379) B541379
theorem B688601 : Blo 358757 688601 := bstep (se 2 (by rfl) ⟨258225, by rfl⟩ : syracuseStep 688601 = 516451) B516451
theorem B1212893 : Blo 358757 1212893 := bstep (se 3 (by rfl) ⟨227417, by rfl⟩ : syracuseStep 1212893 = 454835) B454835
theorem B360939 : Blo 358757 360939 := bstep (se 1 (by rfl) ⟨270704, by rfl⟩ : syracuseStep 360939 = 541409) B541409
theorem B360951 : Blo 358757 360951 := bstep (se 1 (by rfl) ⟨270713, by rfl⟩ : syracuseStep 360951 = 541427) B541427
theorem B360971 : Blo 358757 360971 := bstep (se 1 (by rfl) ⟨270728, by rfl⟩ : syracuseStep 360971 = 541457) B541457
theorem B360983 : Blo 358757 360983 := bstep (se 1 (by rfl) ⟨270737, by rfl⟩ : syracuseStep 360983 = 541475) B541475
theorem B361003 : Blo 358757 361003 := bstep (se 1 (by rfl) ⟨270752, by rfl⟩ : syracuseStep 361003 = 541505) B541505
theorem B361015 : Blo 358757 361015 := bstep (se 1 (by rfl) ⟨270761, by rfl⟩ : syracuseStep 361015 = 541523) B541523
theorem B361035 : Blo 358757 361035 := bstep (se 1 (by rfl) ⟨270776, by rfl⟩ : syracuseStep 361035 = 541553) B541553
theorem B361047 : Blo 358757 361047 := bstep (se 1 (by rfl) ⟨270785, by rfl⟩ : syracuseStep 361047 = 541571) B541571
theorem B361067 : Blo 358757 361067 := bstep (se 1 (by rfl) ⟨270800, by rfl⟩ : syracuseStep 361067 = 541601) B541601
theorem B361079 : Blo 358757 361079 := bstep (se 1 (by rfl) ⟨270809, by rfl⟩ : syracuseStep 361079 = 541619) B541619
theorem B361099 : Blo 358757 361099 := bstep (se 1 (by rfl) ⟨270824, by rfl⟩ : syracuseStep 361099 = 541649) B541649
theorem B361111 : Blo 358757 361111 := bstep (se 1 (by rfl) ⟨270833, by rfl⟩ : syracuseStep 361111 = 541667) B541667
theorem B361131 : Blo 358757 361131 := bstep (se 1 (by rfl) ⟨270848, by rfl⟩ : syracuseStep 361131 = 541697) B541697
theorem B5833397 : Blo 358757 5833397 := bstep (se 5 (by rfl) ⟨273440, by rfl⟩ : syracuseStep 5833397 = 546881) B546881
theorem B361143 : Blo 358757 361143 := bstep (se 1 (by rfl) ⟨270857, by rfl⟩ : syracuseStep 361143 = 541715) B541715
theorem B361163 : Blo 358757 361163 := bstep (se 1 (by rfl) ⟨270872, by rfl⟩ : syracuseStep 361163 = 541745) B541745
theorem B361175 : Blo 358757 361175 := bstep (se 1 (by rfl) ⟨270881, by rfl⟩ : syracuseStep 361175 = 541763) B541763
theorem B361195 : Blo 358757 361195 := bstep (se 1 (by rfl) ⟨270896, by rfl⟩ : syracuseStep 361195 = 541793) B541793
theorem B361207 : Blo 358757 361207 := bstep (se 1 (by rfl) ⟨270905, by rfl⟩ : syracuseStep 361207 = 541811) B541811
theorem B361227 : Blo 358757 361227 := bstep (se 1 (by rfl) ⟨270920, by rfl⟩ : syracuseStep 361227 = 541841) B541841
theorem B361239 : Blo 358757 361239 := bstep (se 1 (by rfl) ⟨270929, by rfl⟩ : syracuseStep 361239 = 541859) B541859
theorem B492313 : Blo 358757 492313 := bstep (se 2 (by rfl) ⟨184617, by rfl⟩ : syracuseStep 492313 = 369235) B369235
theorem B361259 : Blo 358757 361259 := bstep (se 1 (by rfl) ⟨270944, by rfl⟩ : syracuseStep 361259 = 541889) B541889
theorem B361271 : Blo 358757 361271 := bstep (se 1 (by rfl) ⟨270953, by rfl⟩ : syracuseStep 361271 = 541907) B541907
theorem B361291 : Blo 358757 361291 := bstep (se 1 (by rfl) ⟨270968, by rfl⟩ : syracuseStep 361291 = 541937) B541937
theorem B361303 : Blo 358757 361303 := bstep (se 1 (by rfl) ⟨270977, by rfl⟩ : syracuseStep 361303 = 541955) B541955
theorem B361323 : Blo 358757 361323 := bstep (se 1 (by rfl) ⟨270992, by rfl⟩ : syracuseStep 361323 = 541985) B541985
theorem B361335 : Blo 358757 361335 := bstep (se 1 (by rfl) ⟨271001, by rfl⟩ : syracuseStep 361335 = 542003) B542003
theorem B361355 : Blo 358757 361355 := bstep (se 1 (by rfl) ⟨271016, by rfl⟩ : syracuseStep 361355 = 542033) B542033
theorem B1541015 : Blo 358757 1541015 := bstep (se 1 (by rfl) ⟨1155761, by rfl⟩ : syracuseStep 1541015 = 2311523) B2311523
theorem B361367 : Blo 358757 361367 := bstep (se 1 (by rfl) ⟨271025, by rfl⟩ : syracuseStep 361367 = 542051) B542051
theorem B361387 : Blo 358757 361387 := bstep (se 1 (by rfl) ⟨271040, by rfl⟩ : syracuseStep 361387 = 542081) B542081
theorem B361399 : Blo 358757 361399 := bstep (se 1 (by rfl) ⟨271049, by rfl⟩ : syracuseStep 361399 = 542099) B542099
theorem B361419 : Blo 358757 361419 := bstep (se 1 (by rfl) ⟨271064, by rfl⟩ : syracuseStep 361419 = 542129) B542129
theorem B361431 : Blo 358757 361431 := bstep (se 1 (by rfl) ⟨271073, by rfl⟩ : syracuseStep 361431 = 542147) B542147
theorem B361451 : Blo 358757 361451 := bstep (se 1 (by rfl) ⟨271088, by rfl⟩ : syracuseStep 361451 = 542177) B542177
theorem B361463 : Blo 358757 361463 := bstep (se 1 (by rfl) ⟨271097, by rfl⟩ : syracuseStep 361463 = 542195) B542195
theorem B361483 : Blo 358757 361483 := bstep (se 1 (by rfl) ⟨271112, by rfl⟩ : syracuseStep 361483 = 542225) B542225
theorem B361495 : Blo 358757 361495 := bstep (se 1 (by rfl) ⟨271121, by rfl⟩ : syracuseStep 361495 = 542243) B542243
theorem B361515 : Blo 358757 361515 := bstep (se 1 (by rfl) ⟨271136, by rfl⟩ : syracuseStep 361515 = 542273) B542273
theorem B361527 : Blo 358757 361527 := bstep (se 1 (by rfl) ⟨271145, by rfl⟩ : syracuseStep 361527 = 542291) B542291
theorem B361547 : Blo 358757 361547 := bstep (se 1 (by rfl) ⟨271160, by rfl⟩ : syracuseStep 361547 = 542321) B542321
theorem B1836107 : Blo 358757 1836107 := bstep (se 1 (by rfl) ⟨1377080, by rfl⟩ : syracuseStep 1836107 = 2754161) B2754161
theorem B361559 : Blo 358757 361559 := bstep (se 1 (by rfl) ⟨271169, by rfl⟩ : syracuseStep 361559 = 542339) B542339
theorem B361579 : Blo 358757 361579 := bstep (se 1 (by rfl) ⟨271184, by rfl⟩ : syracuseStep 361579 = 542369) B542369
theorem B361591 : Blo 358757 361591 := bstep (se 1 (by rfl) ⟨271193, by rfl⟩ : syracuseStep 361591 = 542387) B542387
theorem B3081347 : Blo 358757 3081347 := bstep (se 1 (by rfl) ⟨2311010, by rfl⟩ : syracuseStep 3081347 = 4622021) B4622021
theorem B361611 : Blo 358757 361611 := bstep (se 1 (by rfl) ⟨271208, by rfl⟩ : syracuseStep 361611 = 542417) B542417
theorem B361623 : Blo 358757 361623 := bstep (se 1 (by rfl) ⟨271217, by rfl⟩ : syracuseStep 361623 = 542435) B542435
theorem B361643 : Blo 358757 361643 := bstep (se 1 (by rfl) ⟨271232, by rfl⟩ : syracuseStep 361643 = 542465) B542465
theorem B361655 : Blo 358757 361655 := bstep (se 1 (by rfl) ⟨271241, by rfl⟩ : syracuseStep 361655 = 542483) B542483
theorem B361675 : Blo 358757 361675 := bstep (se 1 (by rfl) ⟨271256, by rfl⟩ : syracuseStep 361675 = 542513) B542513
theorem B361687 : Blo 358757 361687 := bstep (se 1 (by rfl) ⟨271265, by rfl⟩ : syracuseStep 361687 = 542531) B542531
theorem B361707 : Blo 358757 361707 := bstep (se 1 (by rfl) ⟨271280, by rfl⟩ : syracuseStep 361707 = 542561) B542561
theorem B361719 : Blo 358757 361719 := bstep (se 1 (by rfl) ⟨271289, by rfl⟩ : syracuseStep 361719 = 542579) B542579
theorem B361739 : Blo 358757 361739 := bstep (se 1 (by rfl) ⟨271304, by rfl⟩ : syracuseStep 361739 = 542609) B542609
theorem B361751 : Blo 358757 361751 := bstep (se 1 (by rfl) ⟨271313, by rfl⟩ : syracuseStep 361751 = 542627) B542627
theorem B361771 : Blo 358757 361771 := bstep (se 1 (by rfl) ⟨271328, by rfl⟩ : syracuseStep 361771 = 542657) B542657
theorem B361783 : Blo 358757 361783 := bstep (se 1 (by rfl) ⟨271337, by rfl⟩ : syracuseStep 361783 = 542675) B542675
theorem B361803 : Blo 358757 361803 := bstep (se 1 (by rfl) ⟨271352, by rfl⟩ : syracuseStep 361803 = 542705) B542705
theorem B361815 : Blo 358757 361815 := bstep (se 1 (by rfl) ⟨271361, by rfl⟩ : syracuseStep 361815 = 542723) B542723
theorem B361835 : Blo 358757 361835 := bstep (se 1 (by rfl) ⟨271376, by rfl⟩ : syracuseStep 361835 = 542753) B542753
theorem B361847 : Blo 358757 361847 := bstep (se 1 (by rfl) ⟨271385, by rfl⟩ : syracuseStep 361847 = 542771) B542771
theorem B361867 : Blo 358757 361867 := bstep (se 1 (by rfl) ⟨271400, by rfl⟩ : syracuseStep 361867 = 542801) B542801
theorem B361879 : Blo 358757 361879 := bstep (se 1 (by rfl) ⟨271409, by rfl⟩ : syracuseStep 361879 = 542819) B542819
theorem B361899 : Blo 358757 361899 := bstep (se 1 (by rfl) ⟨271424, by rfl⟩ : syracuseStep 361899 = 542849) B542849
theorem B361911 : Blo 358757 361911 := bstep (se 1 (by rfl) ⟨271433, by rfl⟩ : syracuseStep 361911 = 542867) B542867
theorem B361931 : Blo 358757 361931 := bstep (se 1 (by rfl) ⟨271448, by rfl⟩ : syracuseStep 361931 = 542897) B542897
theorem B361943 : Blo 358757 361943 := bstep (se 1 (by rfl) ⟨271457, by rfl⟩ : syracuseStep 361943 = 542915) B542915
theorem B361963 : Blo 358757 361963 := bstep (se 1 (by rfl) ⟨271472, by rfl⟩ : syracuseStep 361963 = 542945) B542945
theorem B361975 : Blo 358757 361975 := bstep (se 1 (by rfl) ⟨271481, by rfl⟩ : syracuseStep 361975 = 542963) B542963
theorem B361995 : Blo 358757 361995 := bstep (se 1 (by rfl) ⟨271496, by rfl⟩ : syracuseStep 361995 = 542993) B542993
theorem B362007 : Blo 358757 362007 := bstep (se 1 (by rfl) ⟨271505, by rfl⟩ : syracuseStep 362007 = 543011) B543011
theorem B362027 : Blo 358757 362027 := bstep (se 1 (by rfl) ⟨271520, by rfl⟩ : syracuseStep 362027 = 543041) B543041
theorem B362039 : Blo 358757 362039 := bstep (se 1 (by rfl) ⟨271529, by rfl⟩ : syracuseStep 362039 = 543059) B543059
theorem B1214027 : Blo 358757 1214027 := bstep (se 1 (by rfl) ⟨910520, by rfl⟩ : syracuseStep 1214027 = 1821041) B1821041
theorem B362059 : Blo 358757 362059 := bstep (se 1 (by rfl) ⟨271544, by rfl⟩ : syracuseStep 362059 = 543089) B543089
theorem B362071 : Blo 358757 362071 := bstep (se 1 (by rfl) ⟨271553, by rfl⟩ : syracuseStep 362071 = 543107) B543107
theorem B362091 : Blo 358757 362091 := bstep (se 1 (by rfl) ⟨271568, by rfl⟩ : syracuseStep 362091 = 543137) B543137
theorem B362103 : Blo 358757 362103 := bstep (se 1 (by rfl) ⟨271577, by rfl⟩ : syracuseStep 362103 = 543155) B543155
theorem B362123 : Blo 358757 362123 := bstep (se 1 (by rfl) ⟨271592, by rfl⟩ : syracuseStep 362123 = 543185) B543185
theorem B362135 : Blo 358757 362135 := bstep (se 1 (by rfl) ⟨271601, by rfl⟩ : syracuseStep 362135 = 543203) B543203
theorem B362155 : Blo 358757 362155 := bstep (se 1 (by rfl) ⟨271616, by rfl⟩ : syracuseStep 362155 = 543233) B543233
theorem B362167 : Blo 358757 362167 := bstep (se 1 (by rfl) ⟨271625, by rfl⟩ : syracuseStep 362167 = 543251) B543251
theorem B362187 : Blo 358757 362187 := bstep (se 1 (by rfl) ⟨271640, by rfl⟩ : syracuseStep 362187 = 543281) B543281
theorem B362199 : Blo 358757 362199 := bstep (se 1 (by rfl) ⟨271649, by rfl⟩ : syracuseStep 362199 = 543299) B543299
theorem B362219 : Blo 358757 362219 := bstep (se 1 (by rfl) ⟨271664, by rfl⟩ : syracuseStep 362219 = 543329) B543329
theorem B362231 : Blo 358757 362231 := bstep (se 1 (by rfl) ⟨271673, by rfl⟩ : syracuseStep 362231 = 543347) B543347
theorem B362251 : Blo 358757 362251 := bstep (se 1 (by rfl) ⟨271688, by rfl⟩ : syracuseStep 362251 = 543377) B543377
theorem B362263 : Blo 358757 362263 := bstep (se 1 (by rfl) ⟨271697, by rfl⟩ : syracuseStep 362263 = 543395) B543395
theorem B362283 : Blo 358757 362283 := bstep (se 1 (by rfl) ⟨271712, by rfl⟩ : syracuseStep 362283 = 543425) B543425
theorem B362295 : Blo 358757 362295 := bstep (se 1 (by rfl) ⟨271721, by rfl⟩ : syracuseStep 362295 = 543443) B543443
theorem B362315 : Blo 358757 362315 := bstep (se 1 (by rfl) ⟨271736, by rfl⟩ : syracuseStep 362315 = 543473) B543473
theorem B362327 : Blo 358757 362327 := bstep (se 1 (by rfl) ⟨271745, by rfl⟩ : syracuseStep 362327 = 543491) B543491
theorem B1214297 : Blo 358757 1214297 := bstep (se 2 (by rfl) ⟨455361, by rfl⟩ : syracuseStep 1214297 = 910723) B910723
theorem B362347 : Blo 358757 362347 := bstep (se 1 (by rfl) ⟨271760, by rfl⟩ : syracuseStep 362347 = 543521) B543521
theorem B362359 : Blo 358757 362359 := bstep (se 1 (by rfl) ⟨271769, by rfl⟩ : syracuseStep 362359 = 543539) B543539
theorem B362379 : Blo 358757 362379 := bstep (se 1 (by rfl) ⟨271784, by rfl⟩ : syracuseStep 362379 = 543569) B543569
theorem B362391 : Blo 358757 362391 := bstep (se 1 (by rfl) ⟨271793, by rfl⟩ : syracuseStep 362391 = 543587) B543587
theorem B362411 : Blo 358757 362411 := bstep (se 1 (by rfl) ⟨271808, by rfl⟩ : syracuseStep 362411 = 543617) B543617
theorem B362423 : Blo 358757 362423 := bstep (se 1 (by rfl) ⟨271817, by rfl⟩ : syracuseStep 362423 = 543635) B543635
theorem B362443 : Blo 358757 362443 := bstep (se 1 (by rfl) ⟨271832, by rfl⟩ : syracuseStep 362443 = 543665) B543665
theorem B362455 : Blo 358757 362455 := bstep (se 1 (by rfl) ⟨271841, by rfl⟩ : syracuseStep 362455 = 543683) B543683
theorem B362475 : Blo 358757 362475 := bstep (se 1 (by rfl) ⟨271856, by rfl⟩ : syracuseStep 362475 = 543713) B543713
theorem B362487 : Blo 358757 362487 := bstep (se 1 (by rfl) ⟨271865, by rfl⟩ : syracuseStep 362487 = 543731) B543731
theorem B362507 : Blo 358757 362507 := bstep (se 1 (by rfl) ⟨271880, by rfl⟩ : syracuseStep 362507 = 543761) B543761
theorem B952343 : Blo 358757 952343 := bstep (se 1 (by rfl) ⟨714257, by rfl⟩ : syracuseStep 952343 = 1428515) B1428515
theorem B362519 : Blo 358757 362519 := bstep (se 1 (by rfl) ⟨271889, by rfl⟩ : syracuseStep 362519 = 543779) B543779
theorem B362539 : Blo 358757 362539 := bstep (se 1 (by rfl) ⟨271904, by rfl⟩ : syracuseStep 362539 = 543809) B543809
theorem B362551 : Blo 358757 362551 := bstep (se 1 (by rfl) ⟨271913, by rfl⟩ : syracuseStep 362551 = 543827) B543827
theorem B362571 : Blo 358757 362571 := bstep (se 1 (by rfl) ⟨271928, by rfl⟩ : syracuseStep 362571 = 543857) B543857
theorem B362583 : Blo 358757 362583 := bstep (se 1 (by rfl) ⟨271937, by rfl⟩ : syracuseStep 362583 = 543875) B543875
theorem B362603 : Blo 358757 362603 := bstep (se 1 (by rfl) ⟨271952, by rfl⟩ : syracuseStep 362603 = 543905) B543905
theorem B362615 : Blo 358757 362615 := bstep (se 1 (by rfl) ⟨271961, by rfl⟩ : syracuseStep 362615 = 543923) B543923
theorem B460939 : Blo 358757 460939 := bstep (se 1 (by rfl) ⟨345704, by rfl⟩ : syracuseStep 460939 = 691409) B691409
theorem B362635 : Blo 358757 362635 := bstep (se 1 (by rfl) ⟨271976, by rfl⟩ : syracuseStep 362635 = 543953) B543953
theorem B362647 : Blo 358757 362647 := bstep (se 1 (by rfl) ⟨271985, by rfl⟩ : syracuseStep 362647 = 543971) B543971
theorem B362667 : Blo 358757 362667 := bstep (se 1 (by rfl) ⟨272000, by rfl⟩ : syracuseStep 362667 = 544001) B544001
theorem B1673389 : Blo 358757 1673389 := bstep (se 3 (by rfl) ⟨313760, by rfl⟩ : syracuseStep 1673389 = 627521) B627521
theorem B362679 : Blo 358757 362679 := bstep (se 1 (by rfl) ⟨272009, by rfl⟩ : syracuseStep 362679 = 544019) B544019
theorem B362699 : Blo 358757 362699 := bstep (se 1 (by rfl) ⟨272024, by rfl⟩ : syracuseStep 362699 = 544049) B544049
theorem B362711 : Blo 358757 362711 := bstep (se 1 (by rfl) ⟨272033, by rfl⟩ : syracuseStep 362711 = 544067) B544067
theorem B362731 : Blo 358757 362731 := bstep (se 1 (by rfl) ⟨272048, by rfl⟩ : syracuseStep 362731 = 544097) B544097
theorem B362743 : Blo 358757 362743 := bstep (se 1 (by rfl) ⟨272057, by rfl⟩ : syracuseStep 362743 = 544115) B544115
theorem B1214999 : Blo 358757 1214999 := bstep (se 1 (by rfl) ⟨911249, by rfl⟩ : syracuseStep 1214999 = 1822499) B1822499
theorem B2198423 : Blo 358757 2198423 := bstep (se 1 (by rfl) ⟨1648817, by rfl⟩ : syracuseStep 2198423 = 3297635) B3297635
theorem B5049305 : Blo 358757 5049305 := bstep (se 2 (by rfl) ⟨1893489, by rfl⟩ : syracuseStep 5049305 = 3786979) B3786979
theorem B1215539 : Blo 358757 1215539 := bstep (se 1 (by rfl) ⟨911654, by rfl⟩ : syracuseStep 1215539 = 1823309) B1823309
theorem B4131971 : Blo 358757 4131971 := bstep (se 1 (by rfl) ⟨3098978, by rfl⟩ : syracuseStep 4131971 = 6197957) B6197957
theorem B1543475 : Blo 358757 1543475 := bstep (se 1 (by rfl) ⟨1157606, by rfl⟩ : syracuseStep 1543475 = 2315213) B2315213
theorem B1215809 : Blo 358757 1215809 := bstep (se 2 (by rfl) ⟨455928, by rfl⟩ : syracuseStep 1215809 = 911857) B911857
theorem B1216349 : Blo 358757 1216349 := bstep (se 3 (by rfl) ⟨228065, by rfl⟩ : syracuseStep 1216349 = 456131) B456131
theorem B2920465 : Blo 358757 2920465 := bstep (se 2 (by rfl) ⟨1095174, by rfl⟩ : syracuseStep 2920465 = 2190349) B2190349
theorem B5279813 : Blo 358757 5279813 := bstep (se 4 (by rfl) ⟨494982, by rfl⟩ : syracuseStep 5279813 = 989965) B989965
theorem B921817 : Blo 358757 921817 := bstep (se 2 (by rfl) ⟨345681, by rfl⟩ : syracuseStep 921817 = 691363) B691363
theorem B4624685 : Blo 358757 4624685 := bstep (se 3 (by rfl) ⟨867128, by rfl⟩ : syracuseStep 4624685 = 1734257) B1734257
theorem B2199883 : Blo 358757 2199883 := bstep (se 1 (by rfl) ⟨1649912, by rfl⟩ : syracuseStep 2199883 = 3299825) B3299825
theorem B692887 : Blo 358757 692887 := bstep (se 1 (by rfl) ⟨519665, by rfl⟩ : syracuseStep 692887 = 1039331) B1039331
theorem B1217483 : Blo 358757 1217483 := bstep (se 1 (by rfl) ⟨913112, by rfl⟩ : syracuseStep 1217483 = 1826225) B1826225
theorem B922699 : Blo 358757 922699 := bstep (se 1 (by rfl) ⟨692024, by rfl⟩ : syracuseStep 922699 = 1384049) B1384049
theorem B1545389 : Blo 358757 1545389 := bstep (se 3 (by rfl) ⟨289760, by rfl⟩ : syracuseStep 1545389 = 579521) B579521
theorem B1217753 : Blo 358757 1217753 := bstep (se 2 (by rfl) ⟨456657, by rfl⟩ : syracuseStep 1217753 = 913315) B913315
theorem B1644077 : Blo 358757 1644077 := bstep (se 3 (by rfl) ⟨308264, by rfl⟩ : syracuseStep 1644077 = 616529) B616529
theorem B1546073 : Blo 358757 1546073 := bstep (se 2 (by rfl) ⟨579777, by rfl⟩ : syracuseStep 1546073 = 1159555) B1159555
theorem B1218455 : Blo 358757 1218455 := bstep (se 1 (by rfl) ⟨913841, by rfl⟩ : syracuseStep 1218455 = 1827683) B1827683
theorem B366923 : Blo 358757 366923 := bstep (se 1 (by rfl) ⟨275192, by rfl⟩ : syracuseStep 366923 = 550385) B550385
theorem B1218995 : Blo 358757 1218995 := bstep (se 1 (by rfl) ⟨914246, by rfl⟩ : syracuseStep 1218995 = 1828493) B1828493
theorem B432599 : Blo 358757 432599 := bstep (se 1 (by rfl) ⟨324449, by rfl⟩ : syracuseStep 432599 = 648899) B648899
theorem B825815 : Blo 358757 825815 := bstep (se 1 (by rfl) ⟨619361, by rfl⟩ : syracuseStep 825815 = 1238723) B1238723
theorem B432715 : Blo 358757 432715 := bstep (se 1 (by rfl) ⟨324536, by rfl⟩ : syracuseStep 432715 = 649073) B649073
theorem B1219265 : Blo 358757 1219265 := bstep (se 2 (by rfl) ⟨457224, by rfl⟩ : syracuseStep 1219265 = 914449) B914449
theorem B2300633 : Blo 358757 2300633 := bstep (se 2 (by rfl) ⟨862737, by rfl⟩ : syracuseStep 2300633 = 1725475) B1725475
theorem B1547201 : Blo 358757 1547201 := bstep (se 2 (by rfl) ⟨580200, by rfl⟩ : syracuseStep 1547201 = 1160401) B1160401
theorem B728203 : Blo 358757 728203 := bstep (se 1 (by rfl) ⟨546152, by rfl⟩ : syracuseStep 728203 = 1092305) B1092305
theorem B1219805 : Blo 358757 1219805 := bstep (se 3 (by rfl) ⟨228713, by rfl⟩ : syracuseStep 1219805 = 457427) B457427
theorem B1023425 : Blo 358757 1023425 := bstep (se 2 (by rfl) ⟨383784, by rfl⟩ : syracuseStep 1023425 = 767569) B767569
theorem B826891 : Blo 358757 826891 := bstep (se 1 (by rfl) ⟨620168, by rfl⟩ : syracuseStep 826891 = 1240337) B1240337
theorem B728651 : Blo 358757 728651 := bstep (se 1 (by rfl) ⟨546488, by rfl⟩ : syracuseStep 728651 = 1092977) B1092977
theorem B1154839 : Blo 358757 1154839 := bstep (se 1 (by rfl) ⟨866129, by rfl⟩ : syracuseStep 1154839 = 1732259) B1732259
theorem B696089 : Blo 358757 696089 := bstep (se 2 (by rfl) ⟨261033, by rfl⟩ : syracuseStep 696089 = 522067) B522067
theorem B1154891 : Blo 358757 1154891 := bstep (se 1 (by rfl) ⟨866168, by rfl⟩ : syracuseStep 1154891 = 1732337) B1732337
theorem B1023961 : Blo 358757 1023961 := bstep (se 2 (by rfl) ⟨383985, by rfl⟩ : syracuseStep 1023961 = 767971) B767971
theorem B3317777 : Blo 358757 3317777 := bstep (se 2 (by rfl) ⟨1244166, by rfl⟩ : syracuseStep 3317777 = 2488333) B2488333
theorem B6234317 : Blo 358757 6234317 := bstep (se 3 (by rfl) ⟨1168934, by rfl⟩ : syracuseStep 6234317 = 2337869) B2337869
theorem B1220939 : Blo 358757 1220939 := bstep (se 1 (by rfl) ⟨915704, by rfl⟩ : syracuseStep 1220939 = 1831409) B1831409
theorem B1319261 : Blo 358757 1319261 := bstep (se 3 (by rfl) ⟨247361, by rfl⟩ : syracuseStep 1319261 = 494723) B494723
theorem B1548875 : Blo 358757 1548875 := bstep (se 1 (by rfl) ⟨1161656, by rfl⟩ : syracuseStep 1548875 = 2323313) B2323313
theorem B1221209 : Blo 358757 1221209 := bstep (se 2 (by rfl) ⟨457953, by rfl⟩ : syracuseStep 1221209 = 915907) B915907
theorem B2204633 : Blo 358757 2204633 := bstep (se 2 (by rfl) ⟨826737, by rfl⟩ : syracuseStep 2204633 = 1653475) B1653475
theorem B1221911 : Blo 358757 1221911 := bstep (se 1 (by rfl) ⟨916433, by rfl⟩ : syracuseStep 1221911 = 1832867) B1832867
theorem B1156531 : Blo 358757 1156531 := bstep (se 1 (by rfl) ⟨867398, by rfl⟩ : syracuseStep 1156531 = 1734797) B1734797
theorem B1156673 : Blo 358757 1156673 := bstep (se 2 (by rfl) ⟨433752, by rfl⟩ : syracuseStep 1156673 = 867505) B867505
theorem B3221171 : Blo 358757 3221171 := bstep (se 1 (by rfl) ⟨2415878, by rfl⟩ : syracuseStep 3221171 = 4831757) B4831757
theorem B1222451 : Blo 358757 1222451 := bstep (se 1 (by rfl) ⟨916838, by rfl⟩ : syracuseStep 1222451 = 1833677) B1833677
theorem B1025885 : Blo 358757 1025885 := bstep (se 3 (by rfl) ⟨192353, by rfl⟩ : syracuseStep 1025885 = 384707) B384707
theorem B9348965 : Blo 358757 9348965 := bstep (se 4 (by rfl) ⟨876465, by rfl⟩ : syracuseStep 9348965 = 1752931) B1752931
theorem B1222721 : Blo 358757 1222721 := bstep (se 2 (by rfl) ⟨458520, by rfl⟩ : syracuseStep 1222721 = 917041) B917041
theorem B403627 : Blo 358757 403627 := bstep (se 1 (by rfl) ⟨302720, by rfl⟩ : syracuseStep 403627 = 605441) B605441
theorem B403735 : Blo 358757 403735 := bstep (se 1 (by rfl) ⟨302801, by rfl⟩ : syracuseStep 403735 = 605603) B605603
theorem B6596963 : Blo 358757 6596963 := bstep (se 1 (by rfl) ⟨4947722, by rfl⟩ : syracuseStep 6596963 = 9895445) B9895445
theorem B403915 : Blo 358757 403915 := bstep (se 1 (by rfl) ⟨302936, by rfl⟩ : syracuseStep 403915 = 605873) B605873
theorem B404023 : Blo 358757 404023 := bstep (se 1 (by rfl) ⟨303017, by rfl⟩ : syracuseStep 404023 = 606035) B606035
theorem B1223261 : Blo 358757 1223261 := bstep (se 3 (by rfl) ⟨229361, by rfl⟩ : syracuseStep 1223261 = 458723) B458723
theorem B1485485 : Blo 358757 1485485 := bstep (se 3 (by rfl) ⟨278528, by rfl⟩ : syracuseStep 1485485 = 557057) B557057
theorem B3091121 : Blo 358757 3091121 := bstep (se 2 (by rfl) ⟨1159170, by rfl⟩ : syracuseStep 3091121 = 2318341) B2318341
theorem B404203 : Blo 358757 404203 := bstep (se 1 (by rfl) ⟨303152, by rfl⟩ : syracuseStep 404203 = 606305) B606305
theorem B5253893 : Blo 358757 5253893 := bstep (se 4 (by rfl) ⟨492552, by rfl⟩ : syracuseStep 5253893 = 985105) B985105
theorem B404311 : Blo 358757 404311 := bstep (se 1 (by rfl) ⟨303233, by rfl⟩ : syracuseStep 404311 = 606467) B606467
theorem B4107185 : Blo 358757 4107185 := bstep (se 2 (by rfl) ⟨1540194, by rfl⟩ : syracuseStep 4107185 = 3080389) B3080389
theorem B404491 : Blo 358757 404491 := bstep (se 1 (by rfl) ⟨303368, by rfl⟩ : syracuseStep 404491 = 606737) B606737
theorem B404599 : Blo 358757 404599 := bstep (se 1 (by rfl) ⟨303449, by rfl⟩ : syracuseStep 404599 = 606899) B606899
theorem B732289 : Blo 358757 732289 := bstep (se 2 (by rfl) ⟨274608, by rfl⟩ : syracuseStep 732289 = 549217) B549217
theorem B6991109 : Blo 358757 6991109 := bstep (se 4 (by rfl) ⟨655416, by rfl⟩ : syracuseStep 6991109 = 1310833) B1310833
theorem B404779 : Blo 358757 404779 := bstep (se 1 (by rfl) ⟨303584, by rfl⟩ : syracuseStep 404779 = 607169) B607169
theorem B404887 : Blo 358757 404887 := bstep (se 1 (by rfl) ⟨303665, by rfl⟩ : syracuseStep 404887 = 607331) B607331
theorem B3517987 : Blo 358757 3517987 := bstep (se 1 (by rfl) ⟨2638490, by rfl⟩ : syracuseStep 3517987 = 5276981) B5276981
theorem B405067 : Blo 358757 405067 := bstep (se 1 (by rfl) ⟨303800, by rfl⟩ : syracuseStep 405067 = 607601) B607601
theorem B929431 : Blo 358757 929431 := bstep (se 1 (by rfl) ⟨697073, by rfl⟩ : syracuseStep 929431 = 1394147) B1394147
theorem B405175 : Blo 358757 405175 := bstep (se 1 (by rfl) ⟨303881, by rfl⟩ : syracuseStep 405175 = 607763) B607763
theorem B405355 : Blo 358757 405355 := bstep (se 1 (by rfl) ⟨304016, by rfl⟩ : syracuseStep 405355 = 608033) B608033
theorem B405463 : Blo 358757 405463 := bstep (se 1 (by rfl) ⟨304097, by rfl⟩ : syracuseStep 405463 = 608195) B608195
theorem B405643 : Blo 358757 405643 := bstep (se 1 (by rfl) ⟨304232, by rfl⟩ : syracuseStep 405643 = 608465) B608465
theorem B2961559 : Blo 358757 2961559 := bstep (se 1 (by rfl) ⟨2221169, by rfl⟩ : syracuseStep 2961559 = 4442339) B4442339
theorem B405751 : Blo 358757 405751 := bstep (se 1 (by rfl) ⟨304313, by rfl⟩ : syracuseStep 405751 = 608627) B608627
theorem B405931 : Blo 358757 405931 := bstep (se 1 (by rfl) ⟨304448, by rfl⟩ : syracuseStep 405931 = 608897) B608897
theorem B406039 : Blo 358757 406039 := bstep (se 1 (by rfl) ⟨304529, by rfl⟩ : syracuseStep 406039 = 609059) B609059
theorem B3551779 : Blo 358757 3551779 := bstep (se 1 (by rfl) ⟨2663834, by rfl⟩ : syracuseStep 3551779 = 5327669) B5327669
theorem B930355 : Blo 358757 930355 := bstep (se 1 (by rfl) ⟨697766, by rfl⟩ : syracuseStep 930355 = 1395533) B1395533
theorem B1028801 : Blo 358757 1028801 := bstep (se 2 (by rfl) ⟨385800, by rfl⟩ : syracuseStep 1028801 = 771601) B771601
theorem B766657 : Blo 358757 766657 := bstep (se 2 (by rfl) ⟨287496, by rfl⟩ : syracuseStep 766657 = 574993) B574993
theorem B406219 : Blo 358757 406219 := bstep (se 1 (by rfl) ⟨304664, by rfl⟩ : syracuseStep 406219 = 609329) B609329
theorem B1028825 : Blo 358757 1028825 := bstep (se 2 (by rfl) ⟨385809, by rfl⟩ : syracuseStep 1028825 = 771619) B771619
theorem B2601733 : Blo 358757 2601733 := bstep (se 4 (by rfl) ⟨243912, by rfl⟩ : syracuseStep 2601733 = 487825) B487825
theorem B406327 : Blo 358757 406327 := bstep (se 1 (by rfl) ⟨304745, by rfl⟩ : syracuseStep 406327 = 609491) B609491
theorem B734105 : Blo 358757 734105 := bstep (se 2 (by rfl) ⟨275289, by rfl⟩ : syracuseStep 734105 = 550579) B550579
theorem B406507 : Blo 358757 406507 := bstep (se 1 (by rfl) ⟨304880, by rfl⟩ : syracuseStep 406507 = 609761) B609761
theorem B406615 : Blo 358757 406615 := bstep (se 1 (by rfl) ⟨304961, by rfl⟩ : syracuseStep 406615 = 609923) B609923
theorem B1455235 : Blo 358757 1455235 := bstep (se 1 (by rfl) ⟨1091426, by rfl⟩ : syracuseStep 1455235 = 2182853) B2182853
theorem B406795 : Blo 358757 406795 := bstep (se 1 (by rfl) ⟨305096, by rfl⟩ : syracuseStep 406795 = 610193) B610193
theorem B406903 : Blo 358757 406903 := bstep (se 1 (by rfl) ⟨305177, by rfl⟩ : syracuseStep 406903 = 610355) B610355
theorem B4208051 : Blo 358757 4208051 := bstep (se 1 (by rfl) ⟨3156038, by rfl⟩ : syracuseStep 4208051 = 6312077) B6312077
theorem B734707 : Blo 358757 734707 := bstep (se 1 (by rfl) ⟨551030, by rfl⟩ : syracuseStep 734707 = 1102061) B1102061
theorem B407083 : Blo 358757 407083 := bstep (se 1 (by rfl) ⟨305312, by rfl⟩ : syracuseStep 407083 = 610625) B610625
theorem B538187 : Blo 358757 538187 := bstep (se 1 (by rfl) ⟨403640, by rfl⟩ : syracuseStep 538187 = 807281) B807281
theorem B538199 : Blo 358757 538199 := bstep (se 1 (by rfl) ⟨403649, by rfl⟩ : syracuseStep 538199 = 807299) B807299
theorem B767603 : Blo 358757 767603 := bstep (se 1 (by rfl) ⟨575702, by rfl⟩ : syracuseStep 767603 = 1151405) B1151405
theorem B407191 : Blo 358757 407191 := bstep (se 1 (by rfl) ⟨305393, by rfl⟩ : syracuseStep 407191 = 610787) B610787
theorem B538265 : Blo 358757 538265 := bstep (se 2 (by rfl) ⟨201849, by rfl⟩ : syracuseStep 538265 = 403699) B403699
theorem B538379 : Blo 358757 538379 := bstep (se 1 (by rfl) ⟨403784, by rfl⟩ : syracuseStep 538379 = 807569) B807569
theorem B538391 : Blo 358757 538391 := bstep (se 1 (by rfl) ⟨403793, by rfl⟩ : syracuseStep 538391 = 807587) B807587
theorem B3389219 : Blo 358757 3389219 := bstep (se 1 (by rfl) ⟨2541914, by rfl⟩ : syracuseStep 3389219 = 5083829) B5083829
theorem B3323693 : Blo 358757 3323693 := bstep (se 3 (by rfl) ⟨623192, by rfl⟩ : syracuseStep 3323693 = 1246385) B1246385
theorem B407371 : Blo 358757 407371 := bstep (se 1 (by rfl) ⟨305528, by rfl⟩ : syracuseStep 407371 = 611057) B611057
theorem B538457 : Blo 358757 538457 := bstep (se 2 (by rfl) ⟨201921, by rfl⟩ : syracuseStep 538457 = 403843) B403843
theorem B866227 : Blo 358757 866227 := bstep (se 1 (by rfl) ⟨649670, by rfl⟩ : syracuseStep 866227 = 1299341) B1299341
theorem B1030067 : Blo 358757 1030067 := bstep (se 1 (by rfl) ⟨772550, by rfl⟩ : syracuseStep 1030067 = 1545101) B1545101
theorem B407479 : Blo 358757 407479 := bstep (se 1 (by rfl) ⟨305609, by rfl⟩ : syracuseStep 407479 = 611219) B611219
theorem B538571 : Blo 358757 538571 := bstep (se 1 (by rfl) ⟨403928, by rfl⟩ : syracuseStep 538571 = 807857) B807857
theorem B538583 : Blo 358757 538583 := bstep (se 1 (by rfl) ⟨403937, by rfl⟩ : syracuseStep 538583 = 807875) B807875
theorem B538649 : Blo 358757 538649 := bstep (se 2 (by rfl) ⟨201993, by rfl⟩ : syracuseStep 538649 = 403987) B403987
theorem B15677509 : Blo 358757 15677509 := bstep (se 4 (by rfl) ⟨1469766, by rfl⟩ : syracuseStep 15677509 = 2939533) B2939533
theorem B407659 : Blo 358757 407659 := bstep (se 1 (by rfl) ⟨305744, by rfl⟩ : syracuseStep 407659 = 611489) B611489
theorem B538763 : Blo 358757 538763 := bstep (se 1 (by rfl) ⟨404072, by rfl⟩ : syracuseStep 538763 = 808145) B808145
theorem B538775 : Blo 358757 538775 := bstep (se 1 (by rfl) ⟨404081, by rfl⟩ : syracuseStep 538775 = 808163) B808163
theorem B407767 : Blo 358757 407767 := bstep (se 1 (by rfl) ⟨305825, by rfl⟩ : syracuseStep 407767 = 611651) B611651
theorem B538841 : Blo 358757 538841 := bstep (se 2 (by rfl) ⟨202065, by rfl⟩ : syracuseStep 538841 = 404131) B404131
theorem B538955 : Blo 358757 538955 := bstep (se 1 (by rfl) ⟨404216, by rfl⟩ : syracuseStep 538955 = 808433) B808433
theorem B538967 : Blo 358757 538967 := bstep (se 1 (by rfl) ⟨404225, by rfl⟩ : syracuseStep 538967 = 808451) B808451
theorem B407947 : Blo 358757 407947 := bstep (se 1 (by rfl) ⟨305960, by rfl⟩ : syracuseStep 407947 = 611921) B611921
theorem B1554839 : Blo 358757 1554839 := bstep (se 1 (by rfl) ⟨1166129, by rfl⟩ : syracuseStep 1554839 = 2332259) B2332259
theorem B1456535 : Blo 358757 1456535 := bstep (se 1 (by rfl) ⟨1092401, by rfl⟩ : syracuseStep 1456535 = 2184803) B2184803
theorem B539033 : Blo 358757 539033 := bstep (se 2 (by rfl) ⟨202137, by rfl⟩ : syracuseStep 539033 = 404275) B404275
theorem B408055 : Blo 358757 408055 := bstep (se 1 (by rfl) ⟨306041, by rfl⟩ : syracuseStep 408055 = 612083) B612083
theorem B539147 : Blo 358757 539147 := bstep (se 1 (by rfl) ⟨404360, by rfl⟩ : syracuseStep 539147 = 808721) B808721
theorem B539159 : Blo 358757 539159 := bstep (se 1 (by rfl) ⟨404369, by rfl⟩ : syracuseStep 539159 = 808739) B808739
theorem B1817153 : Blo 358757 1817153 := bstep (se 2 (by rfl) ⟨681432, by rfl⟩ : syracuseStep 1817153 = 1362865) B1362865
theorem B539225 : Blo 358757 539225 := bstep (se 2 (by rfl) ⟨202209, by rfl⟩ : syracuseStep 539225 = 404419) B404419
theorem B539339 : Blo 358757 539339 := bstep (se 1 (by rfl) ⟨404504, by rfl⟩ : syracuseStep 539339 = 809009) B809009
theorem B539351 : Blo 358757 539351 := bstep (se 1 (by rfl) ⟨404513, by rfl⟩ : syracuseStep 539351 = 809027) B809027
theorem B2931461 : Blo 358757 2931461 := bstep (se 4 (by rfl) ⟨274824, by rfl⟩ : syracuseStep 2931461 = 549649) B549649
theorem B768791 : Blo 358757 768791 := bstep (se 1 (by rfl) ⟨576593, by rfl⟩ : syracuseStep 768791 = 1153187) B1153187
theorem B539417 : Blo 358757 539417 := bstep (se 2 (by rfl) ⟨202281, by rfl⟩ : syracuseStep 539417 = 404563) B404563
theorem B2931491 : Blo 358757 2931491 := bstep (se 1 (by rfl) ⟨2198618, by rfl⟩ : syracuseStep 2931491 = 4397237) B4397237
theorem B4733761 : Blo 358757 4733761 := bstep (se 2 (by rfl) ⟨1775160, by rfl⟩ : syracuseStep 4733761 = 3550321) B3550321
theorem B539531 : Blo 358757 539531 := bstep (se 1 (by rfl) ⟨404648, by rfl⟩ : syracuseStep 539531 = 809297) B809297
theorem B539543 : Blo 358757 539543 := bstep (se 1 (by rfl) ⟨404657, by rfl⟩ : syracuseStep 539543 = 809315) B809315
theorem B539609 : Blo 358757 539609 := bstep (se 2 (by rfl) ⟨202353, by rfl⟩ : syracuseStep 539609 = 404707) B404707
theorem B539723 : Blo 358757 539723 := bstep (se 1 (by rfl) ⟨404792, by rfl⟩ : syracuseStep 539723 = 809585) B809585
theorem B539735 : Blo 358757 539735 := bstep (se 1 (by rfl) ⟨404801, by rfl⟩ : syracuseStep 539735 = 809603) B809603
theorem B539801 : Blo 358757 539801 := bstep (se 2 (by rfl) ⟨202425, by rfl⟩ : syracuseStep 539801 = 404851) B404851
theorem B2047193 : Blo 358757 2047193 := bstep (se 2 (by rfl) ⟨767697, by rfl⟩ : syracuseStep 2047193 = 1535395) B1535395
theorem B539915 : Blo 358757 539915 := bstep (se 1 (by rfl) ⟨404936, by rfl⟩ : syracuseStep 539915 = 809873) B809873
theorem B539927 : Blo 358757 539927 := bstep (se 1 (by rfl) ⟨404945, by rfl⟩ : syracuseStep 539927 = 809891) B809891
theorem B605515 : Blo 358757 605515 := bstep (se 1 (by rfl) ⟨454136, by rfl⟩ : syracuseStep 605515 = 908273) B908273
theorem B539993 : Blo 358757 539993 := bstep (se 2 (by rfl) ⟨202497, by rfl⟩ : syracuseStep 539993 = 404995) B404995
theorem B540107 : Blo 358757 540107 := bstep (se 1 (by rfl) ⟨405080, by rfl⟩ : syracuseStep 540107 = 810161) B810161
theorem B540119 : Blo 358757 540119 := bstep (se 1 (by rfl) ⟨405089, by rfl⟩ : syracuseStep 540119 = 810179) B810179
theorem B605657 : Blo 358757 605657 := bstep (se 2 (by rfl) ⟨227121, by rfl⟩ : syracuseStep 605657 = 454243) B454243
theorem B540185 : Blo 358757 540185 := bstep (se 2 (by rfl) ⟨202569, by rfl⟩ : syracuseStep 540185 = 405139) B405139
theorem B605785 : Blo 358757 605785 := bstep (se 2 (by rfl) ⟨227169, by rfl⟩ : syracuseStep 605785 = 454339) B454339
theorem B540299 : Blo 358757 540299 := bstep (se 1 (by rfl) ⟨405224, by rfl⟩ : syracuseStep 540299 = 810449) B810449
theorem B540311 : Blo 358757 540311 := bstep (se 1 (by rfl) ⟨405233, by rfl⟩ : syracuseStep 540311 = 810467) B810467
theorem B540377 : Blo 358757 540377 := bstep (se 2 (by rfl) ⟨202641, by rfl⟩ : syracuseStep 540377 = 405283) B405283
theorem B769817 : Blo 358757 769817 := bstep (se 2 (by rfl) ⟨288681, by rfl⟩ : syracuseStep 769817 = 577363) B577363
theorem B1261363 : Blo 358757 1261363 := bstep (se 1 (by rfl) ⟨946022, by rfl⟩ : syracuseStep 1261363 = 1892045) B1892045
theorem B1457995 : Blo 358757 1457995 := bstep (se 1 (by rfl) ⟨1093496, by rfl⟩ : syracuseStep 1457995 = 2186993) B2186993
theorem B540491 : Blo 358757 540491 := bstep (se 1 (by rfl) ⟨405368, by rfl⟩ : syracuseStep 540491 = 810737) B810737
theorem B540503 : Blo 358757 540503 := bstep (se 1 (by rfl) ⟨405377, by rfl⟩ : syracuseStep 540503 = 810755) B810755
theorem B540569 : Blo 358757 540569 := bstep (se 2 (by rfl) ⟨202713, by rfl⟩ : syracuseStep 540569 = 405427) B405427
theorem B540683 : Blo 358757 540683 := bstep (se 1 (by rfl) ⟨405512, by rfl⟩ : syracuseStep 540683 = 811025) B811025
theorem B540695 : Blo 358757 540695 := bstep (se 1 (by rfl) ⟨405521, by rfl⟩ : syracuseStep 540695 = 811043) B811043
theorem B540761 : Blo 358757 540761 := bstep (se 2 (by rfl) ⟨202785, by rfl⟩ : syracuseStep 540761 = 405571) B405571
theorem B606359 : Blo 358757 606359 := bstep (se 1 (by rfl) ⟨454769, by rfl⟩ : syracuseStep 606359 = 909539) B909539
theorem B540875 : Blo 358757 540875 := bstep (se 1 (by rfl) ⟨405656, by rfl⟩ : syracuseStep 540875 = 811313) B811313
theorem B540887 : Blo 358757 540887 := bstep (se 1 (by rfl) ⟨405665, by rfl⟩ : syracuseStep 540887 = 811331) B811331
theorem B606487 : Blo 358757 606487 := bstep (se 1 (by rfl) ⟨454865, by rfl⟩ : syracuseStep 606487 = 909731) B909731
theorem B540953 : Blo 358757 540953 := bstep (se 2 (by rfl) ⟨202857, by rfl⟩ : syracuseStep 540953 = 405715) B405715
theorem B3916097 : Blo 358757 3916097 := bstep (se 2 (by rfl) ⟨1468536, by rfl⟩ : syracuseStep 3916097 = 2937073) B2937073
theorem B541067 : Blo 358757 541067 := bstep (se 1 (by rfl) ⟨405800, by rfl⟩ : syracuseStep 541067 = 811601) B811601
theorem B2310551 : Blo 358757 2310551 := bstep (se 1 (by rfl) ⟨1732913, by rfl⟩ : syracuseStep 2310551 = 3465827) B3465827
theorem B541079 : Blo 358757 541079 := bstep (se 1 (by rfl) ⟨405809, by rfl⟩ : syracuseStep 541079 = 811619) B811619
theorem B1458611 : Blo 358757 1458611 := bstep (se 1 (by rfl) ⟨1093958, by rfl⟩ : syracuseStep 1458611 = 2187917) B2187917
theorem B1819097 : Blo 358757 1819097 := bstep (se 2 (by rfl) ⟨682161, by rfl⟩ : syracuseStep 1819097 = 1364323) B1364323
theorem B541145 : Blo 358757 541145 := bstep (se 2 (by rfl) ⟨202929, by rfl⟩ : syracuseStep 541145 = 405859) B405859
theorem B541259 : Blo 358757 541259 := bstep (se 1 (by rfl) ⟨405944, by rfl⟩ : syracuseStep 541259 = 811889) B811889
theorem B541271 : Blo 358757 541271 := bstep (se 1 (by rfl) ⟨405953, by rfl⟩ : syracuseStep 541271 = 811907) B811907
theorem B541337 : Blo 358757 541337 := bstep (se 2 (by rfl) ⟨203001, by rfl⟩ : syracuseStep 541337 = 406003) B406003
theorem B1032925 : Blo 358757 1032925 := bstep (se 3 (by rfl) ⟨193673, by rfl⟩ : syracuseStep 1032925 = 387347) B387347
theorem B541451 : Blo 358757 541451 := bstep (se 1 (by rfl) ⟨406088, by rfl⟩ : syracuseStep 541451 = 812177) B812177
theorem B1557265 : Blo 358757 1557265 := bstep (se 2 (by rfl) ⟨583974, by rfl⟩ : syracuseStep 1557265 = 1167949) B1167949
theorem B541463 : Blo 358757 541463 := bstep (se 1 (by rfl) ⟨406097, by rfl⟩ : syracuseStep 541463 = 812195) B812195
theorem B1032983 : Blo 358757 1032983 := bstep (se 1 (by rfl) ⟨774737, by rfl⟩ : syracuseStep 1032983 = 1549475) B1549475
theorem B770867 : Blo 358757 770867 := bstep (se 1 (by rfl) ⟨578150, by rfl⟩ : syracuseStep 770867 = 1156301) B1156301
theorem B541529 : Blo 358757 541529 := bstep (se 2 (by rfl) ⟨203073, by rfl⟩ : syracuseStep 541529 = 406147) B406147
theorem B607115 : Blo 358757 607115 := bstep (se 1 (by rfl) ⟨455336, by rfl⟩ : syracuseStep 607115 = 910673) B910673
theorem B2311091 : Blo 358757 2311091 := bstep (se 1 (by rfl) ⟨1733318, by rfl⟩ : syracuseStep 2311091 = 3466637) B3466637
theorem B541643 : Blo 358757 541643 := bstep (se 1 (by rfl) ⟨406232, by rfl⟩ : syracuseStep 541643 = 812465) B812465
theorem B541655 : Blo 358757 541655 := bstep (se 1 (by rfl) ⟨406241, by rfl⟩ : syracuseStep 541655 = 812483) B812483
theorem B607243 : Blo 358757 607243 := bstep (se 1 (by rfl) ⟨455432, by rfl⟩ : syracuseStep 607243 = 910865) B910865
theorem B541721 : Blo 358757 541721 := bstep (se 2 (by rfl) ⟨203145, by rfl⟩ : syracuseStep 541721 = 406291) B406291
theorem B3064877 : Blo 358757 3064877 := bstep (se 3 (by rfl) ⟨574664, by rfl⟩ : syracuseStep 3064877 = 1149329) B1149329
theorem B9290821 : Blo 358757 9290821 := bstep (se 4 (by rfl) ⟨871014, by rfl⟩ : syracuseStep 9290821 = 1742029) B1742029
theorem B541835 : Blo 358757 541835 := bstep (se 1 (by rfl) ⟨406376, by rfl⟩ : syracuseStep 541835 = 812753) B812753
theorem B541847 : Blo 358757 541847 := bstep (se 1 (by rfl) ⟨406385, by rfl⟩ : syracuseStep 541847 = 812771) B812771
theorem B607385 : Blo 358757 607385 := bstep (se 2 (by rfl) ⟨227769, by rfl⟩ : syracuseStep 607385 = 455539) B455539
theorem B541913 : Blo 358757 541913 := bstep (se 2 (by rfl) ⟨203217, by rfl⟩ : syracuseStep 541913 = 406435) B406435
theorem B607513 : Blo 358757 607513 := bstep (se 2 (by rfl) ⟨227817, by rfl⟩ : syracuseStep 607513 = 455635) B455635
theorem B2114881 : Blo 358757 2114881 := bstep (se 2 (by rfl) ⟨793080, by rfl⟩ : syracuseStep 2114881 = 1586161) B1586161
theorem B1230155 : Blo 358757 1230155 := bstep (se 1 (by rfl) ⟨922616, by rfl⟩ : syracuseStep 1230155 = 1845233) B1845233
theorem B542027 : Blo 358757 542027 := bstep (se 1 (by rfl) ⟨406520, by rfl⟩ : syracuseStep 542027 = 813041) B813041
theorem B542039 : Blo 358757 542039 := bstep (se 1 (by rfl) ⟨406529, by rfl⟩ : syracuseStep 542039 = 813059) B813059
theorem B5850467 : Blo 358757 5850467 := bstep (se 1 (by rfl) ⟨4387850, by rfl⟩ : syracuseStep 5850467 = 8775701) B8775701
theorem B771457 : Blo 358757 771457 := bstep (se 2 (by rfl) ⟨289296, by rfl⟩ : syracuseStep 771457 = 578593) B578593
theorem B542105 : Blo 358757 542105 := bstep (se 2 (by rfl) ⟨203289, by rfl⟩ : syracuseStep 542105 = 406579) B406579
theorem B542219 : Blo 358757 542219 := bstep (se 1 (by rfl) ⟨406664, by rfl⟩ : syracuseStep 542219 = 813329) B813329
theorem B542231 : Blo 358757 542231 := bstep (se 1 (by rfl) ⟨406673, by rfl⟩ : syracuseStep 542231 = 813347) B813347
theorem B542297 : Blo 358757 542297 := bstep (se 2 (by rfl) ⟨203361, by rfl⟩ : syracuseStep 542297 = 406723) B406723
theorem B542411 : Blo 358757 542411 := bstep (se 1 (by rfl) ⟨406808, by rfl⟩ : syracuseStep 542411 = 813617) B813617
theorem B4933325 : Blo 358757 4933325 := bstep (se 3 (by rfl) ⟨924998, by rfl⟩ : syracuseStep 4933325 = 1849997) B1849997
theorem B542423 : Blo 358757 542423 := bstep (se 1 (by rfl) ⟨406817, by rfl⟩ : syracuseStep 542423 = 813635) B813635
theorem B542489 : Blo 358757 542489 := bstep (se 2 (by rfl) ⟨203433, by rfl⟩ : syracuseStep 542489 = 406867) B406867
theorem B2049857 : Blo 358757 2049857 := bstep (se 2 (by rfl) ⟨768696, by rfl⟩ : syracuseStep 2049857 = 1537393) B1537393
theorem B608087 : Blo 358757 608087 := bstep (se 1 (by rfl) ⟨456065, by rfl⟩ : syracuseStep 608087 = 912131) B912131
theorem B542603 : Blo 358757 542603 := bstep (se 1 (by rfl) ⟨406952, by rfl⟩ : syracuseStep 542603 = 813905) B813905
theorem B542615 : Blo 358757 542615 := bstep (se 1 (by rfl) ⟨406961, by rfl⟩ : syracuseStep 542615 = 813923) B813923
theorem B608215 : Blo 358757 608215 := bstep (se 1 (by rfl) ⟨456161, by rfl⟩ : syracuseStep 608215 = 912323) B912323
theorem B542681 : Blo 358757 542681 := bstep (se 2 (by rfl) ⟨203505, by rfl⟩ : syracuseStep 542681 = 407011) B407011
theorem B1820717 : Blo 358757 1820717 := bstep (se 3 (by rfl) ⟨341384, by rfl⟩ : syracuseStep 1820717 = 682769) B682769
theorem B542795 : Blo 358757 542795 := bstep (se 1 (by rfl) ⟨407096, by rfl⟩ : syracuseStep 542795 = 814193) B814193
theorem B542807 : Blo 358757 542807 := bstep (se 1 (by rfl) ⟨407105, by rfl⟩ : syracuseStep 542807 = 814211) B814211
theorem B542873 : Blo 358757 542873 := bstep (se 2 (by rfl) ⟨203577, by rfl⟩ : syracuseStep 542873 = 407155) B407155
theorem B411895 : Blo 358757 411895 := bstep (se 1 (by rfl) ⟨308921, by rfl⟩ : syracuseStep 411895 = 617843) B617843
theorem B542987 : Blo 358757 542987 := bstep (se 1 (by rfl) ⟨407240, by rfl⟩ : syracuseStep 542987 = 814481) B814481
theorem B542999 : Blo 358757 542999 := bstep (se 1 (by rfl) ⟨407249, by rfl⟩ : syracuseStep 542999 = 814499) B814499
theorem B575831 : Blo 358757 575831 := bstep (se 1 (by rfl) ⟨431873, by rfl⟩ : syracuseStep 575831 = 863747) B863747
theorem B543065 : Blo 358757 543065 := bstep (se 2 (by rfl) ⟨203649, by rfl⟩ : syracuseStep 543065 = 407299) B407299
theorem B2312549 : Blo 358757 2312549 := bstep (se 4 (by rfl) ⟨216801, by rfl⟩ : syracuseStep 2312549 = 433603) B433603
theorem B2738609 : Blo 358757 2738609 := bstep (se 2 (by rfl) ⟨1026978, by rfl⟩ : syracuseStep 2738609 = 2053957) B2053957
theorem B1362379 : Blo 358757 1362379 := bstep (se 1 (by rfl) ⟨1021784, by rfl⟩ : syracuseStep 1362379 = 2043569) B2043569
theorem B543179 : Blo 358757 543179 := bstep (se 1 (by rfl) ⟨407384, by rfl⟩ : syracuseStep 543179 = 814769) B814769
theorem B543191 : Blo 358757 543191 := bstep (se 1 (by rfl) ⟨407393, by rfl⟩ : syracuseStep 543191 = 814787) B814787
theorem B9423373 : Blo 358757 9423373 := bstep (se 3 (by rfl) ⟨1766882, by rfl⟩ : syracuseStep 9423373 = 3533765) B3533765
theorem B543257 : Blo 358757 543257 := bstep (se 2 (by rfl) ⟨203721, by rfl⟩ : syracuseStep 543257 = 407443) B407443
theorem B608843 : Blo 358757 608843 := bstep (se 1 (by rfl) ⟨456632, by rfl⟩ : syracuseStep 608843 = 913265) B913265
theorem B543371 : Blo 358757 543371 := bstep (se 1 (by rfl) ⟨407528, by rfl⟩ : syracuseStep 543371 = 815057) B815057
theorem B543383 : Blo 358757 543383 := bstep (se 1 (by rfl) ⟨407537, by rfl⟩ : syracuseStep 543383 = 815075) B815075
theorem B608971 : Blo 358757 608971 := bstep (se 1 (by rfl) ⟨456728, by rfl⟩ : syracuseStep 608971 = 913457) B913457
theorem B543449 : Blo 358757 543449 := bstep (se 2 (by rfl) ⟨203793, by rfl⟩ : syracuseStep 543449 = 407587) B407587
theorem B1362653 : Blo 358757 1362653 := bstep (se 3 (by rfl) ⟨255497, by rfl⟩ : syracuseStep 1362653 = 510995) B510995
theorem B543563 : Blo 358757 543563 := bstep (se 1 (by rfl) ⟨407672, by rfl⟩ : syracuseStep 543563 = 815345) B815345
theorem B576343 : Blo 358757 576343 := bstep (se 1 (by rfl) ⟨432257, by rfl⟩ : syracuseStep 576343 = 864515) B864515
theorem B609113 : Blo 358757 609113 := bstep (se 2 (by rfl) ⟨228417, by rfl⟩ : syracuseStep 609113 = 456835) B456835
theorem B543575 : Blo 358757 543575 := bstep (se 1 (by rfl) ⟨407681, by rfl⟩ : syracuseStep 543575 = 815363) B815363
theorem B773003 : Blo 358757 773003 := bstep (se 1 (by rfl) ⟨579752, by rfl⟩ : syracuseStep 773003 = 1159505) B1159505
theorem B2739095 : Blo 358757 2739095 := bstep (se 1 (by rfl) ⟨2054321, by rfl⟩ : syracuseStep 2739095 = 4108643) B4108643
theorem B543641 : Blo 358757 543641 := bstep (se 2 (by rfl) ⟨203865, by rfl⟩ : syracuseStep 543641 = 407731) B407731
theorem B609241 : Blo 358757 609241 := bstep (se 2 (by rfl) ⟨228465, by rfl⟩ : syracuseStep 609241 = 456931) B456931
theorem B543755 : Blo 358757 543755 := bstep (se 1 (by rfl) ⟨407816, by rfl⟩ : syracuseStep 543755 = 815633) B815633
theorem B543767 : Blo 358757 543767 := bstep (se 1 (by rfl) ⟨407825, by rfl⟩ : syracuseStep 543767 = 815651) B815651
theorem B543833 : Blo 358757 543833 := bstep (se 2 (by rfl) ⟨203937, by rfl⟩ : syracuseStep 543833 = 407875) B407875
theorem B2608307 : Blo 358757 2608307 := bstep (se 1 (by rfl) ⟨1956230, by rfl⟩ : syracuseStep 2608307 = 3912461) B3912461
theorem B576715 : Blo 358757 576715 := bstep (se 1 (by rfl) ⟨432536, by rfl⟩ : syracuseStep 576715 = 865073) B865073
theorem B543947 : Blo 358757 543947 := bstep (se 1 (by rfl) ⟨407960, by rfl⟩ : syracuseStep 543947 = 815921) B815921
theorem B543959 : Blo 358757 543959 := bstep (se 1 (by rfl) ⟨407969, by rfl⟩ : syracuseStep 543959 = 815939) B815939
theorem B544025 : Blo 358757 544025 := bstep (se 2 (by rfl) ⟨204009, by rfl⟩ : syracuseStep 544025 = 408019) B408019
theorem B3067267 : Blo 358757 3067267 := bstep (se 1 (by rfl) ⟨2300450, by rfl⟩ : syracuseStep 3067267 = 4600901) B4600901
theorem B1363351 : Blo 358757 1363351 := bstep (se 1 (by rfl) ⟨1022513, by rfl⟩ : syracuseStep 1363351 = 2045027) B2045027
theorem B609815 : Blo 358757 609815 := bstep (se 1 (by rfl) ⟨457361, by rfl⟩ : syracuseStep 609815 = 914723) B914723
theorem B577163 : Blo 358757 577163 := bstep (se 1 (by rfl) ⟨432872, by rfl⟩ : syracuseStep 577163 = 865745) B865745
theorem B609943 : Blo 358757 609943 := bstep (se 1 (by rfl) ⟨457457, by rfl⟩ : syracuseStep 609943 = 914915) B914915
theorem B1298099 : Blo 358757 1298099 := bstep (se 1 (by rfl) ⟨973574, by rfl⟩ : syracuseStep 1298099 = 1947149) B1947149
theorem B773849 : Blo 358757 773849 := bstep (se 2 (by rfl) ⟨290193, by rfl⟩ : syracuseStep 773849 = 580387) B580387
theorem B970841 : Blo 358757 970841 := bstep (se 2 (by rfl) ⟨364065, by rfl⟩ : syracuseStep 970841 = 728131) B728131
theorem B1364141 : Blo 358757 1364141 := bstep (se 3 (by rfl) ⟨255776, by rfl⟩ : syracuseStep 1364141 = 511553) B511553
theorem B610571 : Blo 358757 610571 := bstep (se 1 (by rfl) ⟨457928, by rfl⟩ : syracuseStep 610571 = 915857) B915857
theorem B3068225 : Blo 358757 3068225 := bstep (se 2 (by rfl) ⟨1150584, by rfl⟩ : syracuseStep 3068225 = 2301169) B2301169
theorem B512345 : Blo 358757 512345 := bstep (se 2 (by rfl) ⟨192129, by rfl⟩ : syracuseStep 512345 = 384259) B384259
theorem B610699 : Blo 358757 610699 := bstep (se 1 (by rfl) ⟨458024, by rfl⟩ : syracuseStep 610699 = 916049) B916049
theorem B577945 : Blo 358757 577945 := bstep (se 2 (by rfl) ⟨216729, by rfl⟩ : syracuseStep 577945 = 433459) B433459
theorem B807371 : Blo 358757 807371 := bstep (se 1 (by rfl) ⟨605528, by rfl⟩ : syracuseStep 807371 = 1211057) B1211057
theorem B774643 : Blo 358757 774643 := bstep (se 1 (by rfl) ⟨580982, by rfl⟩ : syracuseStep 774643 = 1161965) B1161965
theorem B807425 : Blo 358757 807425 := bstep (se 2 (by rfl) ⟨302784, by rfl⟩ : syracuseStep 807425 = 605569) B605569
theorem B12440081 : Blo 358757 12440081 := bstep (se 2 (by rfl) ⟨4665030, by rfl⟩ : syracuseStep 12440081 = 9330061) B9330061
theorem B6279697 : Blo 358757 6279697 := bstep (se 2 (by rfl) ⟨2354886, by rfl⟩ : syracuseStep 6279697 = 4709773) B4709773
theorem B610841 : Blo 358757 610841 := bstep (se 2 (by rfl) ⟨229065, by rfl⟩ : syracuseStep 610841 = 458131) B458131
theorem B610969 : Blo 358757 610969 := bstep (se 2 (by rfl) ⟨229113, by rfl⟩ : syracuseStep 610969 = 458227) B458227
theorem B807641 : Blo 358757 807641 := bstep (se 2 (by rfl) ⟨302865, by rfl⟩ : syracuseStep 807641 = 605731) B605731
theorem B807731 : Blo 358757 807731 := bstep (se 1 (by rfl) ⟨605798, by rfl⟩ : syracuseStep 807731 = 1211597) B1211597
theorem B807767 : Blo 358757 807767 := bstep (se 1 (by rfl) ⟨605825, by rfl⟩ : syracuseStep 807767 = 1211651) B1211651
theorem B512983 : Blo 358757 512983 := bstep (se 1 (by rfl) ⟨384737, by rfl⟩ : syracuseStep 512983 = 769475) B769475
theorem B807947 : Blo 358757 807947 := bstep (se 1 (by rfl) ⟨605960, by rfl⟩ : syracuseStep 807947 = 1211921) B1211921
theorem B808001 : Blo 358757 808001 := bstep (se 2 (by rfl) ⟨303000, by rfl⟩ : syracuseStep 808001 = 606001) B606001
theorem B1725533 : Blo 358757 1725533 := bstep (se 3 (by rfl) ⟨323537, by rfl⟩ : syracuseStep 1725533 = 647075) B647075
theorem B611543 : Blo 358757 611543 := bstep (se 1 (by rfl) ⟨458657, by rfl⟩ : syracuseStep 611543 = 917315) B917315
theorem B808217 : Blo 358757 808217 := bstep (se 2 (by rfl) ⟨303081, by rfl⟩ : syracuseStep 808217 = 606163) B606163
theorem B611671 : Blo 358757 611671 := bstep (se 1 (by rfl) ⟨458753, by rfl⟩ : syracuseStep 611671 = 917507) B917507
theorem B808307 : Blo 358757 808307 := bstep (se 1 (by rfl) ⟨606230, by rfl⟩ : syracuseStep 808307 = 1212461) B1212461
theorem B808343 : Blo 358757 808343 := bstep (se 1 (by rfl) ⟨606257, by rfl⟩ : syracuseStep 808343 = 1212515) B1212515
theorem B1365569 : Blo 358757 1365569 := bstep (se 2 (by rfl) ⟨512088, by rfl⟩ : syracuseStep 1365569 = 1024177) B1024177
theorem B808523 : Blo 358757 808523 := bstep (se 1 (by rfl) ⟨606392, by rfl⟩ : syracuseStep 808523 = 1212785) B1212785
theorem B808577 : Blo 358757 808577 := bstep (se 2 (by rfl) ⟨303216, by rfl⟩ : syracuseStep 808577 = 606433) B606433
theorem B513803 : Blo 358757 513803 := bstep (se 1 (by rfl) ⟨385352, by rfl⟩ : syracuseStep 513803 = 770705) B770705
theorem B808793 : Blo 358757 808793 := bstep (se 2 (by rfl) ⟨303297, by rfl⟩ : syracuseStep 808793 = 606595) B606595
theorem B1824605 : Blo 358757 1824605 := bstep (se 3 (by rfl) ⟨342113, by rfl⟩ : syracuseStep 1824605 = 684227) B684227
theorem B1857431 : Blo 358757 1857431 := bstep (se 1 (by rfl) ⟨1393073, by rfl⟩ : syracuseStep 1857431 = 2786147) B2786147
theorem B808883 : Blo 358757 808883 := bstep (se 1 (by rfl) ⟨606662, by rfl⟩ : syracuseStep 808883 = 1213325) B1213325
theorem B808919 : Blo 358757 808919 := bstep (se 1 (by rfl) ⟨606689, by rfl⟩ : syracuseStep 808919 = 1213379) B1213379
theorem B809099 : Blo 358757 809099 := bstep (se 1 (by rfl) ⟨606824, by rfl⟩ : syracuseStep 809099 = 1213649) B1213649
theorem B546955 : Blo 358757 546955 := bstep (se 1 (by rfl) ⟨410216, by rfl⟩ : syracuseStep 546955 = 820433) B820433
theorem B809153 : Blo 358757 809153 := bstep (se 2 (by rfl) ⟨303432, by rfl⟩ : syracuseStep 809153 = 606865) B606865
theorem B5822765 : Blo 358757 5822765 := bstep (se 3 (by rfl) ⟨1091768, by rfl⟩ : syracuseStep 5822765 = 2183537) B2183537
theorem B2283821 : Blo 358757 2283821 := bstep (se 3 (by rfl) ⟨428216, by rfl⟩ : syracuseStep 2283821 = 856433) B856433
theorem B4118849 : Blo 358757 4118849 := bstep (se 2 (by rfl) ⟨1544568, by rfl⟩ : syracuseStep 4118849 = 3089137) B3089137
theorem B383383 : Blo 358757 383383 := bstep (se 1 (by rfl) ⟨287537, by rfl⟩ : syracuseStep 383383 = 575075) B575075
theorem B809369 : Blo 358757 809369 := bstep (se 2 (by rfl) ⟨303513, by rfl⟩ : syracuseStep 809369 = 607027) B607027
theorem B809459 : Blo 358757 809459 := bstep (se 1 (by rfl) ⟨607094, by rfl⟩ : syracuseStep 809459 = 1214189) B1214189
theorem B809495 : Blo 358757 809495 := bstep (se 1 (by rfl) ⟨607121, by rfl⟩ : syracuseStep 809495 = 1214243) B1214243
theorem B7494275 : Blo 358757 7494275 := bstep (se 1 (by rfl) ⟨5620706, by rfl⟩ : syracuseStep 7494275 = 11241413) B11241413
theorem B809675 : Blo 358757 809675 := bstep (se 1 (by rfl) ⟨607256, by rfl⟩ : syracuseStep 809675 = 1214513) B1214513
theorem B514777 : Blo 358757 514777 := bstep (se 2 (by rfl) ⟨193041, by rfl⟩ : syracuseStep 514777 = 386083) B386083
theorem B809729 : Blo 358757 809729 := bstep (se 2 (by rfl) ⟨303648, by rfl⟩ : syracuseStep 809729 = 607297) B607297
theorem B809945 : Blo 358757 809945 := bstep (se 2 (by rfl) ⟨303729, by rfl⟩ : syracuseStep 809945 = 607459) B607459
theorem B1367057 : Blo 358757 1367057 := bstep (se 2 (by rfl) ⟨512646, by rfl⟩ : syracuseStep 1367057 = 1025293) B1025293
theorem B810035 : Blo 358757 810035 := bstep (se 1 (by rfl) ⟨607526, by rfl⟩ : syracuseStep 810035 = 1215053) B1215053
theorem B2055233 : Blo 358757 2055233 := bstep (se 2 (by rfl) ⟨770712, by rfl⟩ : syracuseStep 2055233 = 1541425) B1541425
theorem B810071 : Blo 358757 810071 := bstep (se 1 (by rfl) ⟨607553, by rfl⟩ : syracuseStep 810071 = 1215107) B1215107
theorem B810251 : Blo 358757 810251 := bstep (se 1 (by rfl) ⟨607688, by rfl⟩ : syracuseStep 810251 = 1215377) B1215377
theorem B908567 : Blo 358757 908567 := bstep (se 1 (by rfl) ⟨681425, by rfl⟩ : syracuseStep 908567 = 1362851) B1362851
theorem B1400129 : Blo 358757 1400129 := bstep (se 2 (by rfl) ⟨525048, by rfl⟩ : syracuseStep 1400129 = 1050097) B1050097
theorem B810305 : Blo 358757 810305 := bstep (se 2 (by rfl) ⟨303864, by rfl⟩ : syracuseStep 810305 = 607729) B607729
theorem B777559 : Blo 358757 777559 := bstep (se 1 (by rfl) ⟨583169, by rfl⟩ : syracuseStep 777559 = 1166339) B1166339
theorem B1367513 : Blo 358757 1367513 := bstep (se 2 (by rfl) ⟨512817, by rfl⟩ : syracuseStep 1367513 = 1025635) B1025635
theorem B810521 : Blo 358757 810521 := bstep (se 2 (by rfl) ⟨303945, by rfl⟩ : syracuseStep 810521 = 607891) B607891
theorem B810611 : Blo 358757 810611 := bstep (se 1 (by rfl) ⟨607958, by rfl⟩ : syracuseStep 810611 = 1215917) B1215917
theorem B810647 : Blo 358757 810647 := bstep (se 1 (by rfl) ⟨607985, by rfl⟩ : syracuseStep 810647 = 1215971) B1215971
theorem B1367725 : Blo 358757 1367725 := bstep (se 3 (by rfl) ⟨256448, by rfl⟩ : syracuseStep 1367725 = 512897) B512897
theorem B646859 : Blo 358757 646859 := bstep (se 1 (by rfl) ⟨485144, by rfl⟩ : syracuseStep 646859 = 970289) B970289
theorem B1171223 : Blo 358757 1171223 := bstep (se 1 (by rfl) ⟨878417, by rfl⟩ : syracuseStep 1171223 = 1756835) B1756835
theorem B810827 : Blo 358757 810827 := bstep (se 1 (by rfl) ⟨608120, by rfl⟩ : syracuseStep 810827 = 1216241) B1216241
theorem B515927 : Blo 358757 515927 := bstep (se 1 (by rfl) ⟨386945, by rfl⟩ : syracuseStep 515927 = 773891) B773891
theorem B810881 : Blo 358757 810881 := bstep (se 2 (by rfl) ⟨304080, by rfl⟩ : syracuseStep 810881 = 608161) B608161
theorem B1826711 : Blo 358757 1826711 := bstep (se 1 (by rfl) ⟨1370033, by rfl⟩ : syracuseStep 1826711 = 2740067) B2740067
theorem B1368029 : Blo 358757 1368029 := bstep (se 3 (by rfl) ⟨256505, by rfl⟩ : syracuseStep 1368029 = 513011) B513011
theorem B385079 : Blo 358757 385079 := bstep (se 1 (by rfl) ⟨288809, by rfl⟩ : syracuseStep 385079 = 577619) B577619
theorem B909377 : Blo 358757 909377 := bstep (se 2 (by rfl) ⟨341016, by rfl⟩ : syracuseStep 909377 = 682033) B682033
theorem B811097 : Blo 358757 811097 := bstep (se 2 (by rfl) ⟨304161, by rfl⟩ : syracuseStep 811097 = 608323) B608323
theorem B516235 : Blo 358757 516235 := bstep (se 1 (by rfl) ⟨387176, by rfl⟩ : syracuseStep 516235 = 774353) B774353
theorem B811187 : Blo 358757 811187 := bstep (se 1 (by rfl) ⟨608390, by rfl⟩ : syracuseStep 811187 = 1216781) B1216781
theorem B811223 : Blo 358757 811223 := bstep (se 1 (by rfl) ⟨608417, by rfl⟩ : syracuseStep 811223 = 1216835) B1216835
theorem B26665237 : Blo 358757 26665237 := bstep (se 6 (by rfl) ⟨624966, by rfl⟩ : syracuseStep 26665237 = 1249933) B1249933
theorem B975197 : Blo 358757 975197 := bstep (se 3 (by rfl) ⟨182849, by rfl⟩ : syracuseStep 975197 = 365699) B365699
theorem B811403 : Blo 358757 811403 := bstep (se 1 (by rfl) ⟨608552, by rfl⟩ : syracuseStep 811403 = 1217105) B1217105
theorem B811457 : Blo 358757 811457 := bstep (se 2 (by rfl) ⟨304296, by rfl⟩ : syracuseStep 811457 = 608593) B608593
theorem B909913 : Blo 358757 909913 := bstep (se 2 (by rfl) ⟨341217, by rfl⟩ : syracuseStep 909913 = 682435) B682435
theorem B811673 : Blo 358757 811673 := bstep (se 2 (by rfl) ⟨304377, by rfl⟩ : syracuseStep 811673 = 608755) B608755
theorem B811763 : Blo 358757 811763 := bstep (se 1 (by rfl) ⟨608822, by rfl⟩ : syracuseStep 811763 = 1217645) B1217645
theorem B811799 : Blo 358757 811799 := bstep (se 1 (by rfl) ⟨608849, by rfl⟩ : syracuseStep 811799 = 1217699) B1217699
theorem B8479667 : Blo 358757 8479667 := bstep (se 1 (by rfl) ⟨6359750, by rfl⟩ : syracuseStep 8479667 = 12719501) B12719501
theorem B811979 : Blo 358757 811979 := bstep (se 1 (by rfl) ⟨608984, by rfl⟩ : syracuseStep 811979 = 1217969) B1217969
theorem B812033 : Blo 358757 812033 := bstep (se 2 (by rfl) ⟨304512, by rfl⟩ : syracuseStep 812033 = 609025) B609025
theorem B1532951 : Blo 358757 1532951 := bstep (se 1 (by rfl) ⟨1149713, by rfl⟩ : syracuseStep 1532951 = 2299427) B2299427
theorem B943193 : Blo 358757 943193 := bstep (se 2 (by rfl) ⟨353697, by rfl⟩ : syracuseStep 943193 = 707395) B707395
theorem B648343 : Blo 358757 648343 := bstep (se 1 (by rfl) ⟨486257, by rfl⟩ : syracuseStep 648343 = 972515) B972515
theorem B812249 : Blo 358757 812249 := bstep (se 2 (by rfl) ⟨304593, by rfl⟩ : syracuseStep 812249 = 609187) B609187
theorem B11101445 : Blo 358757 11101445 := bstep (se 4 (by rfl) ⟨1040760, by rfl⟩ : syracuseStep 11101445 = 2081521) B2081521
theorem B2090285 : Blo 358757 2090285 := bstep (se 3 (by rfl) ⟨391928, by rfl⟩ : syracuseStep 2090285 = 783857) B783857
theorem B812339 : Blo 358757 812339 := bstep (se 1 (by rfl) ⟨609254, by rfl⟩ : syracuseStep 812339 = 1218509) B1218509
theorem B681281 : Blo 358757 681281 := bstep (se 2 (by rfl) ⟨255480, by rfl⟩ : syracuseStep 681281 = 510961) B510961
theorem B812375 : Blo 358757 812375 := bstep (se 1 (by rfl) ⟨609281, by rfl⟩ : syracuseStep 812375 = 1218563) B1218563
theorem B976321 : Blo 358757 976321 := bstep (se 2 (by rfl) ⟨366120, by rfl⟩ : syracuseStep 976321 = 732241) B732241
theorem B550361 : Blo 358757 550361 := bstep (se 2 (by rfl) ⟨206385, by rfl⟩ : syracuseStep 550361 = 412771) B412771
theorem B812555 : Blo 358757 812555 := bstep (se 1 (by rfl) ⟨609416, by rfl⟩ : syracuseStep 812555 = 1218833) B1218833
theorem B812609 : Blo 358757 812609 := bstep (se 2 (by rfl) ⟨304728, by rfl⟩ : syracuseStep 812609 = 609457) B609457
theorem B681547 : Blo 358757 681547 := bstep (se 1 (by rfl) ⟨511160, by rfl⟩ : syracuseStep 681547 = 1022321) B1022321
theorem B2090647 : Blo 358757 2090647 := bstep (se 1 (by rfl) ⟨1567985, by rfl⟩ : syracuseStep 2090647 = 3135971) B3135971
theorem B911027 : Blo 358757 911027 := bstep (se 1 (by rfl) ⟨683270, by rfl⟩ : syracuseStep 911027 = 1366541) B1366541
theorem B812825 : Blo 358757 812825 := bstep (se 2 (by rfl) ⟨304809, by rfl⟩ : syracuseStep 812825 = 609619) B609619
theorem B386903 : Blo 358757 386903 := bstep (se 1 (by rfl) ⟨290177, by rfl⟩ : syracuseStep 386903 = 580355) B580355
theorem B812915 : Blo 358757 812915 := bstep (se 1 (by rfl) ⟨609686, by rfl⟩ : syracuseStep 812915 = 1219373) B1219373
theorem B812951 : Blo 358757 812951 := bstep (se 1 (by rfl) ⟨609713, by rfl⟩ : syracuseStep 812951 = 1219427) B1219427
theorem B976819 : Blo 358757 976819 := bstep (se 1 (by rfl) ⟨732614, by rfl⟩ : syracuseStep 976819 = 1465229) B1465229
theorem B911321 : Blo 358757 911321 := bstep (se 2 (by rfl) ⟨341745, by rfl⟩ : syracuseStep 911321 = 683491) B683491
theorem B681995 : Blo 358757 681995 := bstep (se 1 (by rfl) ⟨511496, by rfl⟩ : syracuseStep 681995 = 1022993) B1022993
theorem B2746385 : Blo 358757 2746385 := bstep (se 2 (by rfl) ⟨1029894, by rfl⟩ : syracuseStep 2746385 = 2059789) B2059789
theorem B813131 : Blo 358757 813131 := bstep (se 1 (by rfl) ⟨609848, by rfl⟩ : syracuseStep 813131 = 1219697) B1219697
theorem B813185 : Blo 358757 813185 := bstep (se 2 (by rfl) ⟨304944, by rfl⟩ : syracuseStep 813185 = 609889) B609889
theorem B14772365 : Blo 358757 14772365 := bstep (se 3 (by rfl) ⟨2769818, by rfl⟩ : syracuseStep 14772365 = 5539637) B5539637
theorem B649367 : Blo 358757 649367 := bstep (se 1 (by rfl) ⟨487025, by rfl⟩ : syracuseStep 649367 = 974051) B974051
theorem B682177 : Blo 358757 682177 := bstep (se 2 (by rfl) ⟨255816, by rfl⟩ : syracuseStep 682177 = 511633) B511633
theorem B813401 : Blo 358757 813401 := bstep (se 2 (by rfl) ⟨305025, by rfl⟩ : syracuseStep 813401 = 610051) B610051
theorem B813491 : Blo 358757 813491 := bstep (se 1 (by rfl) ⟨610118, by rfl⟩ : syracuseStep 813491 = 1220237) B1220237
theorem B813527 : Blo 358757 813527 := bstep (se 1 (by rfl) ⟨610145, by rfl⟩ : syracuseStep 813527 = 1220291) B1220291
theorem B1370627 : Blo 358757 1370627 := bstep (se 1 (by rfl) ⟨1027970, by rfl⟩ : syracuseStep 1370627 = 2055941) B2055941
theorem B3893777 : Blo 358757 3893777 := bstep (se 2 (by rfl) ⟨1460166, by rfl⟩ : syracuseStep 3893777 = 2920333) B2920333
theorem B1370641 : Blo 358757 1370641 := bstep (se 2 (by rfl) ⟨513990, by rfl⟩ : syracuseStep 1370641 = 1027981) B1027981
theorem B682519 : Blo 358757 682519 := bstep (se 1 (by rfl) ⟨511889, by rfl⟩ : syracuseStep 682519 = 1023779) B1023779
theorem B977501 : Blo 358757 977501 := bstep (se 3 (by rfl) ⟨183281, by rfl⟩ : syracuseStep 977501 = 366563) B366563
theorem B813707 : Blo 358757 813707 := bstep (se 1 (by rfl) ⟨610280, by rfl⟩ : syracuseStep 813707 = 1220561) B1220561
theorem B813761 : Blo 358757 813761 := bstep (se 2 (by rfl) ⟨305160, by rfl⟩ : syracuseStep 813761 = 610321) B610321
theorem B682739 : Blo 358757 682739 := bstep (se 1 (by rfl) ⟨512054, by rfl⟩ : syracuseStep 682739 = 1024109) B1024109
theorem B486155 : Blo 358757 486155 := bstep (se 1 (by rfl) ⟨364616, by rfl⟩ : syracuseStep 486155 = 729233) B729233
theorem B1370945 : Blo 358757 1370945 := bstep (se 2 (by rfl) ⟨514104, by rfl⟩ : syracuseStep 1370945 = 1028209) B1028209
theorem B1469249 : Blo 358757 1469249 := bstep (se 2 (by rfl) ⟨550968, by rfl⟩ : syracuseStep 1469249 = 1101937) B1101937
theorem B1043351 : Blo 358757 1043351 := bstep (se 1 (by rfl) ⟨782513, by rfl⟩ : syracuseStep 1043351 = 1565027) B1565027
theorem B813977 : Blo 358757 813977 := bstep (se 2 (by rfl) ⟨305241, by rfl⟩ : syracuseStep 813977 = 610483) B610483
theorem B682967 : Blo 358757 682967 := bstep (se 1 (by rfl) ⟨512225, by rfl⟩ : syracuseStep 682967 = 1024451) B1024451
theorem B617431 : Blo 358757 617431 := bstep (se 1 (by rfl) ⟨463073, by rfl⟩ : syracuseStep 617431 = 926147) B926147
theorem B814067 : Blo 358757 814067 := bstep (se 1 (by rfl) ⟨610550, by rfl⟩ : syracuseStep 814067 = 1221101) B1221101
theorem B814103 : Blo 358757 814103 := bstep (se 1 (by rfl) ⟨610577, by rfl⟩ : syracuseStep 814103 = 1221155) B1221155
theorem B814283 : Blo 358757 814283 := bstep (se 1 (by rfl) ⟨610712, by rfl⟩ : syracuseStep 814283 = 1221425) B1221425
theorem B683225 : Blo 358757 683225 := bstep (se 2 (by rfl) ⟨256209, by rfl⟩ : syracuseStep 683225 = 512419) B512419
theorem B814337 : Blo 358757 814337 := bstep (se 2 (by rfl) ⟨305376, by rfl⟩ : syracuseStep 814337 = 610753) B610753
theorem B7433477 : Blo 358757 7433477 := bstep (se 4 (by rfl) ⟨696888, by rfl⟩ : syracuseStep 7433477 = 1393777) B1393777
theorem B486679 : Blo 358757 486679 := bstep (se 1 (by rfl) ⟨365009, by rfl⟩ : syracuseStep 486679 = 730019) B730019
theorem B1830275 : Blo 358757 1830275 := bstep (se 1 (by rfl) ⟨1372706, by rfl⟩ : syracuseStep 1830275 = 2745413) B2745413
theorem B1535411 : Blo 358757 1535411 := bstep (se 1 (by rfl) ⟨1151558, by rfl⟩ : syracuseStep 1535411 = 2303117) B2303117
theorem B814553 : Blo 358757 814553 := bstep (se 2 (by rfl) ⟨305457, by rfl⟩ : syracuseStep 814553 = 610915) B610915
theorem B1371613 : Blo 358757 1371613 := bstep (se 3 (by rfl) ⟨257177, by rfl⟩ : syracuseStep 1371613 = 514355) B514355
theorem B1306115 : Blo 358757 1306115 := bstep (se 1 (by rfl) ⟨979586, by rfl⟩ : syracuseStep 1306115 = 1959173) B1959173
theorem B5205539 : Blo 358757 5205539 := bstep (se 1 (by rfl) ⟨3904154, by rfl⟩ : syracuseStep 5205539 = 7808309) B7808309
theorem B814643 : Blo 358757 814643 := bstep (se 1 (by rfl) ⟨610982, by rfl⟩ : syracuseStep 814643 = 1221965) B1221965
theorem B912971 : Blo 358757 912971 := bstep (se 1 (by rfl) ⟨684728, by rfl⟩ : syracuseStep 912971 = 1369457) B1369457
theorem B814679 : Blo 358757 814679 := bstep (se 1 (by rfl) ⟨611009, by rfl⟩ : syracuseStep 814679 = 1222019) B1222019
theorem B683635 : Blo 358757 683635 := bstep (se 1 (by rfl) ⟨512726, by rfl⟩ : syracuseStep 683635 = 1025453) B1025453
theorem B814859 : Blo 358757 814859 := bstep (se 1 (by rfl) ⟨611144, by rfl⟩ : syracuseStep 814859 = 1222289) B1222289
theorem B487193 : Blo 358757 487193 := bstep (se 2 (by rfl) ⟨182697, by rfl⟩ : syracuseStep 487193 = 365395) B365395
theorem B814913 : Blo 358757 814913 := bstep (se 2 (by rfl) ⟨305592, by rfl⟩ : syracuseStep 814913 = 611185) B611185
theorem B815129 : Blo 358757 815129 := bstep (se 2 (by rfl) ⟨305673, by rfl⟩ : syracuseStep 815129 = 611347) B611347
theorem B684121 : Blo 358757 684121 := bstep (se 2 (by rfl) ⟨256545, by rfl⟩ : syracuseStep 684121 = 513091) B513091
theorem B5009501 : Blo 358757 5009501 := bstep (se 3 (by rfl) ⟨939281, by rfl⟩ : syracuseStep 5009501 = 1878563) B1878563
theorem B815219 : Blo 358757 815219 := bstep (se 1 (by rfl) ⟨611414, by rfl⟩ : syracuseStep 815219 = 1222829) B1222829
theorem B815255 : Blo 358757 815255 := bstep (se 1 (by rfl) ⟨611441, by rfl⟩ : syracuseStep 815255 = 1222883) B1222883
theorem B454987 : Blo 358757 454987 := bstep (se 1 (by rfl) ⟨341240, by rfl⟩ : syracuseStep 454987 = 682481) B682481
theorem B815435 : Blo 358757 815435 := bstep (se 1 (by rfl) ⟨611576, by rfl⟩ : syracuseStep 815435 = 1223153) B1223153
theorem B815489 : Blo 358757 815489 := bstep (se 2 (by rfl) ⟨305808, by rfl⟩ : syracuseStep 815489 = 611617) B611617
theorem B651673 : Blo 358757 651673 := bstep (se 2 (by rfl) ⟨244377, by rfl⟩ : syracuseStep 651673 = 488755) B488755
theorem B619019 : Blo 358757 619019 := bstep (se 1 (by rfl) ⟨464264, by rfl⟩ : syracuseStep 619019 = 928529) B928529
theorem B913943 : Blo 358757 913943 := bstep (se 1 (by rfl) ⟨685457, by rfl⟩ : syracuseStep 913943 = 1370915) B1370915
theorem B815705 : Blo 358757 815705 := bstep (se 2 (by rfl) ⟨305889, by rfl⟩ : syracuseStep 815705 = 611779) B611779
theorem B684683 : Blo 358757 684683 := bstep (se 1 (by rfl) ⟨513512, by rfl⟩ : syracuseStep 684683 = 1027025) B1027025
theorem B815795 : Blo 358757 815795 := bstep (se 1 (by rfl) ⟨611846, by rfl⟩ : syracuseStep 815795 = 1223693) B1223693
theorem B815831 : Blo 358757 815831 := bstep (se 1 (by rfl) ⟨611873, by rfl⟩ : syracuseStep 815831 = 1223747) B1223747
theorem B1372889 : Blo 358757 1372889 := bstep (se 2 (by rfl) ⟨514833, by rfl⟩ : syracuseStep 1372889 = 1029667) B1029667
theorem B684865 : Blo 358757 684865 := bstep (se 2 (by rfl) ⟨256824, by rfl⟩ : syracuseStep 684865 = 513649) B513649
theorem B816011 : Blo 358757 816011 := bstep (se 1 (by rfl) ⟨612008, by rfl⟩ : syracuseStep 816011 = 1224017) B1224017
theorem B816065 : Blo 358757 816065 := bstep (se 2 (by rfl) ⟨306024, by rfl⟩ : syracuseStep 816065 = 612049) B612049
theorem B914611 : Blo 358757 914611 := bstep (se 1 (by rfl) ⟨685958, by rfl⟩ : syracuseStep 914611 = 1371917) B1371917
theorem B2323673 : Blo 358757 2323673 := bstep (se 2 (by rfl) ⟨871377, by rfl⟩ : syracuseStep 2323673 = 1742755) B1742755
theorem B455959 : Blo 358757 455959 := bstep (se 1 (by rfl) ⟨341969, by rfl⟩ : syracuseStep 455959 = 683939) B683939
theorem B1537325 : Blo 358757 1537325 := bstep (se 3 (by rfl) ⟨288248, by rfl⟩ : syracuseStep 1537325 = 576497) B576497
theorem B914753 : Blo 358757 914753 := bstep (se 2 (by rfl) ⟨343032, by rfl⟩ : syracuseStep 914753 = 686065) B686065
theorem B685579 : Blo 358757 685579 := bstep (se 1 (by rfl) ⟨514184, by rfl⟩ : syracuseStep 685579 = 1028369) B1028369
theorem B1144343 : Blo 358757 1144343 := bstep (se 1 (by rfl) ⟨858257, by rfl⟩ : syracuseStep 1144343 = 1716515) B1716515
theorem B587287 : Blo 358757 587287 := bstep (se 1 (by rfl) ⟨440465, by rfl⟩ : syracuseStep 587287 = 880931) B880931
theorem B488983 : Blo 358757 488983 := bstep (se 1 (by rfl) ⟨366737, by rfl⟩ : syracuseStep 488983 = 733475) B733475
theorem B685655 : Blo 358757 685655 := bstep (se 1 (by rfl) ⟨514241, by rfl⟩ : syracuseStep 685655 = 1028483) B1028483
theorem B1537667 : Blo 358757 1537667 := bstep (se 1 (by rfl) ⟨1153250, by rfl⟩ : syracuseStep 1537667 = 2306501) B2306501
theorem B5961397 : Blo 358757 5961397 := bstep (se 5 (by rfl) ⟨279440, by rfl⟩ : syracuseStep 5961397 = 558881) B558881
theorem B2193169 : Blo 358757 2193169 := bstep (se 2 (by rfl) ⟨822438, by rfl⟩ : syracuseStep 2193169 = 1644877) B1644877
theorem B2750273 : Blo 358757 2750273 := bstep (se 2 (by rfl) ⟨1031352, by rfl⟩ : syracuseStep 2750273 = 2062705) B2062705
theorem B22181957 : Blo 358757 22181957 := bstep (se 4 (by rfl) ⟨2079558, by rfl⟩ : syracuseStep 22181957 = 4159117) B4159117
theorem B456779 : Blo 358757 456779 := bstep (se 1 (by rfl) ⟨342584, by rfl⟩ : syracuseStep 456779 = 685169) B685169
theorem B686323 : Blo 358757 686323 := bstep (se 1 (by rfl) ⟨514742, by rfl⟩ : syracuseStep 686323 = 1029485) B1029485
theorem B1374515 : Blo 358757 1374515 := bstep (se 1 (by rfl) ⟨1030886, by rfl⟩ : syracuseStep 1374515 = 2061773) B2061773
theorem B1374529 : Blo 358757 1374529 := bstep (se 2 (by rfl) ⟨515448, by rfl⟩ : syracuseStep 1374529 = 1030897) B1030897
theorem B358763 : Blo 358757 358763 := bstep (se 1 (by rfl) ⟨269072, by rfl⟩ : syracuseStep 358763 = 538145) B538145
theorem B358775 : Blo 358757 358775 := bstep (se 1 (by rfl) ⟨269081, by rfl⟩ : syracuseStep 358775 = 538163) B538163
theorem B358795 : Blo 358757 358795 := bstep (se 1 (by rfl) ⟨269096, by rfl⟩ : syracuseStep 358795 = 538193) B538193
theorem B358807 : Blo 358757 358807 := bstep (se 1 (by rfl) ⟨269105, by rfl⟩ : syracuseStep 358807 = 538211) B538211
theorem B358827 : Blo 358757 358827 := bstep (se 1 (by rfl) ⟨269120, by rfl⟩ : syracuseStep 358827 = 538241) B538241
theorem B358839 : Blo 358757 358839 := bstep (se 1 (by rfl) ⟨269129, by rfl⟩ : syracuseStep 358839 = 538259) B538259
theorem B358859 : Blo 358757 358859 := bstep (se 1 (by rfl) ⟨269144, by rfl⟩ : syracuseStep 358859 = 538289) B538289
theorem B358871 : Blo 358757 358871 := bstep (se 1 (by rfl) ⟨269153, by rfl⟩ : syracuseStep 358871 = 538307) B538307
theorem B686551 : Blo 358757 686551 := bstep (se 1 (by rfl) ⟨514913, by rfl⟩ : syracuseStep 686551 = 1029827) B1029827
theorem B1210841 : Blo 358757 1210841 := bstep (se 2 (by rfl) ⟨454065, by rfl⟩ : syracuseStep 1210841 = 908131) B908131
theorem B358891 : Blo 358757 358891 := bstep (se 1 (by rfl) ⟨269168, by rfl⟩ : syracuseStep 358891 = 538337) B538337
theorem B358903 : Blo 358757 358903 := bstep (se 1 (by rfl) ⟨269177, by rfl⟩ : syracuseStep 358903 = 538355) B538355
theorem B358923 : Blo 358757 358923 := bstep (se 1 (by rfl) ⟨269192, by rfl⟩ : syracuseStep 358923 = 538385) B538385
theorem B358935 : Blo 358757 358935 := bstep (se 1 (by rfl) ⟨269201, by rfl⟩ : syracuseStep 358935 = 538403) B538403
theorem B358955 : Blo 358757 358955 := bstep (se 1 (by rfl) ⟨269216, by rfl⟩ : syracuseStep 358955 = 538433) B538433
theorem B916019 : Blo 358757 916019 := bstep (se 1 (by rfl) ⟨687014, by rfl⟩ : syracuseStep 916019 = 1374029) B1374029
theorem B358967 : Blo 358757 358967 := bstep (se 1 (by rfl) ⟨269225, by rfl⟩ : syracuseStep 358967 = 538451) B538451
theorem B686657 : Blo 358757 686657 := bstep (se 2 (by rfl) ⟨257496, by rfl⟩ : syracuseStep 686657 = 514993) B514993
theorem B358987 : Blo 358757 358987 := bstep (se 1 (by rfl) ⟨269240, by rfl⟩ : syracuseStep 358987 = 538481) B538481
theorem B358999 : Blo 358757 358999 := bstep (se 1 (by rfl) ⟨269249, by rfl⟩ : syracuseStep 358999 = 538499) B538499
theorem B3078749 : Blo 358757 3078749 := bstep (se 3 (by rfl) ⟨577265, by rfl⟩ : syracuseStep 3078749 = 1154531) B1154531
theorem B359019 : Blo 358757 359019 := bstep (se 1 (by rfl) ⟨269264, by rfl⟩ : syracuseStep 359019 = 538529) B538529
theorem B359031 : Blo 358757 359031 := bstep (se 1 (by rfl) ⟨269273, by rfl⟩ : syracuseStep 359031 = 538547) B538547
theorem B2062979 : Blo 358757 2062979 := bstep (se 1 (by rfl) ⟨1547234, by rfl⟩ : syracuseStep 2062979 = 3094469) B3094469
theorem B359051 : Blo 358757 359051 := bstep (se 1 (by rfl) ⟨269288, by rfl⟩ : syracuseStep 359051 = 538577) B538577
theorem B359063 : Blo 358757 359063 := bstep (se 1 (by rfl) ⟨269297, by rfl⟩ : syracuseStep 359063 = 538595) B538595
theorem B359083 : Blo 358757 359083 := bstep (se 1 (by rfl) ⟨269312, by rfl⟩ : syracuseStep 359083 = 538625) B538625
theorem B359095 : Blo 358757 359095 := bstep (se 1 (by rfl) ⟨269321, by rfl⟩ : syracuseStep 359095 = 538643) B538643
theorem B359115 : Blo 358757 359115 := bstep (se 1 (by rfl) ⟨269336, by rfl⟩ : syracuseStep 359115 = 538673) B538673
theorem B359127 : Blo 358757 359127 := bstep (se 1 (by rfl) ⟨269345, by rfl⟩ : syracuseStep 359127 = 538691) B538691
theorem B686809 : Blo 358757 686809 := bstep (se 2 (by rfl) ⟨257553, by rfl⟩ : syracuseStep 686809 = 515107) B515107
theorem B359147 : Blo 358757 359147 := bstep (se 1 (by rfl) ⟨269360, by rfl⟩ : syracuseStep 359147 = 538721) B538721
theorem B359159 : Blo 358757 359159 := bstep (se 1 (by rfl) ⟨269369, by rfl⟩ : syracuseStep 359159 = 538739) B538739
theorem B359179 : Blo 358757 359179 := bstep (se 1 (by rfl) ⟨269384, by rfl⟩ : syracuseStep 359179 = 538769) B538769
theorem B457483 : Blo 358757 457483 := bstep (se 1 (by rfl) ⟨343112, by rfl⟩ : syracuseStep 457483 = 686225) B686225
theorem B3373841 : Blo 358757 3373841 := bstep (se 2 (by rfl) ⟨1265190, by rfl⟩ : syracuseStep 3373841 = 2530381) B2530381
theorem B359191 : Blo 358757 359191 := bstep (se 1 (by rfl) ⟨269393, by rfl⟩ : syracuseStep 359191 = 538787) B538787
theorem B359211 : Blo 358757 359211 := bstep (se 1 (by rfl) ⟨269408, by rfl⟩ : syracuseStep 359211 = 538817) B538817
theorem B359223 : Blo 358757 359223 := bstep (se 1 (by rfl) ⟨269417, by rfl⟩ : syracuseStep 359223 = 538835) B538835
theorem B359243 : Blo 358757 359243 := bstep (se 1 (by rfl) ⟨269432, by rfl⟩ : syracuseStep 359243 = 538865) B538865
theorem B359255 : Blo 358757 359255 := bstep (se 1 (by rfl) ⟨269441, by rfl⟩ : syracuseStep 359255 = 538883) B538883
theorem B359275 : Blo 358757 359275 := bstep (se 1 (by rfl) ⟨269456, by rfl⟩ : syracuseStep 359275 = 538913) B538913
theorem B359287 : Blo 358757 359287 := bstep (se 1 (by rfl) ⟨269465, by rfl⟩ : syracuseStep 359287 = 538931) B538931
theorem B359307 : Blo 358757 359307 := bstep (se 1 (by rfl) ⟨269480, by rfl⟩ : syracuseStep 359307 = 538961) B538961
theorem B359319 : Blo 358757 359319 := bstep (se 1 (by rfl) ⟨269489, by rfl⟩ : syracuseStep 359319 = 538979) B538979
theorem B359339 : Blo 358757 359339 := bstep (se 1 (by rfl) ⟨269504, by rfl⟩ : syracuseStep 359339 = 539009) B539009
theorem B359351 : Blo 358757 359351 := bstep (se 1 (by rfl) ⟨269513, by rfl⟩ : syracuseStep 359351 = 539027) B539027
theorem B359371 : Blo 358757 359371 := bstep (se 1 (by rfl) ⟨269528, by rfl⟩ : syracuseStep 359371 = 539057) B539057
theorem B359383 : Blo 358757 359383 := bstep (se 1 (by rfl) ⟨269537, by rfl⟩ : syracuseStep 359383 = 539075) B539075
theorem B359403 : Blo 358757 359403 := bstep (se 1 (by rfl) ⟨269552, by rfl⟩ : syracuseStep 359403 = 539105) B539105
theorem B359415 : Blo 358757 359415 := bstep (se 1 (by rfl) ⟨269561, by rfl⟩ : syracuseStep 359415 = 539123) B539123
theorem B359435 : Blo 358757 359435 := bstep (se 1 (by rfl) ⟨269576, by rfl⟩ : syracuseStep 359435 = 539153) B539153
theorem B1834001 : Blo 358757 1834001 := bstep (se 2 (by rfl) ⟨687750, by rfl⟩ : syracuseStep 1834001 = 1375501) B1375501
theorem B359447 : Blo 358757 359447 := bstep (se 1 (by rfl) ⟨269585, by rfl⟩ : syracuseStep 359447 = 539171) B539171
theorem B457751 : Blo 358757 457751 := bstep (se 1 (by rfl) ⟨343313, by rfl⟩ : syracuseStep 457751 = 686627) B686627
theorem B359467 : Blo 358757 359467 := bstep (se 1 (by rfl) ⟨269600, by rfl⟩ : syracuseStep 359467 = 539201) B539201
theorem B359479 : Blo 358757 359479 := bstep (se 1 (by rfl) ⟨269609, by rfl⟩ : syracuseStep 359479 = 539219) B539219
theorem B359499 : Blo 358757 359499 := bstep (se 1 (by rfl) ⟨269624, by rfl⟩ : syracuseStep 359499 = 539249) B539249
theorem B916555 : Blo 358757 916555 := bstep (se 1 (by rfl) ⟨687416, by rfl⟩ : syracuseStep 916555 = 1374833) B1374833
theorem B359511 : Blo 358757 359511 := bstep (se 1 (by rfl) ⟨269633, by rfl⟩ : syracuseStep 359511 = 539267) B539267
theorem B359531 : Blo 358757 359531 := bstep (se 1 (by rfl) ⟨269648, by rfl⟩ : syracuseStep 359531 = 539297) B539297
theorem B359543 : Blo 358757 359543 := bstep (se 1 (by rfl) ⟨269657, by rfl⟩ : syracuseStep 359543 = 539315) B539315
theorem B359563 : Blo 358757 359563 := bstep (se 1 (by rfl) ⟨269672, by rfl⟩ : syracuseStep 359563 = 539345) B539345
theorem B1211543 : Blo 358757 1211543 := bstep (se 1 (by rfl) ⟨908657, by rfl⟩ : syracuseStep 1211543 = 1817315) B1817315
theorem B359575 : Blo 358757 359575 := bstep (se 1 (by rfl) ⟨269681, by rfl⟩ : syracuseStep 359575 = 539363) B539363
theorem B359595 : Blo 358757 359595 := bstep (se 1 (by rfl) ⟨269696, by rfl⟩ : syracuseStep 359595 = 539393) B539393
theorem B1834163 : Blo 358757 1834163 := bstep (se 1 (by rfl) ⟨1375622, by rfl⟩ : syracuseStep 1834163 = 2751245) B2751245
theorem B359607 : Blo 358757 359607 := bstep (se 1 (by rfl) ⟨269705, by rfl⟩ : syracuseStep 359607 = 539411) B539411
theorem B359627 : Blo 358757 359627 := bstep (se 1 (by rfl) ⟨269720, by rfl⟩ : syracuseStep 359627 = 539441) B539441
theorem B359639 : Blo 358757 359639 := bstep (se 1 (by rfl) ⟨269729, by rfl⟩ : syracuseStep 359639 = 539459) B539459
theorem B916697 : Blo 358757 916697 := bstep (se 2 (by rfl) ⟨343761, by rfl⟩ : syracuseStep 916697 = 687523) B687523
theorem B359659 : Blo 358757 359659 := bstep (se 1 (by rfl) ⟨269744, by rfl⟩ : syracuseStep 359659 = 539489) B539489
theorem B359671 : Blo 358757 359671 := bstep (se 1 (by rfl) ⟨269753, by rfl⟩ : syracuseStep 359671 = 539507) B539507
theorem B359691 : Blo 358757 359691 := bstep (se 1 (by rfl) ⟨269768, by rfl⟩ : syracuseStep 359691 = 539537) B539537
theorem B359703 : Blo 358757 359703 := bstep (se 1 (by rfl) ⟨269777, by rfl⟩ : syracuseStep 359703 = 539555) B539555
theorem B359723 : Blo 358757 359723 := bstep (se 1 (by rfl) ⟨269792, by rfl⟩ : syracuseStep 359723 = 539585) B539585
theorem B359735 : Blo 358757 359735 := bstep (se 1 (by rfl) ⟨269801, by rfl⟩ : syracuseStep 359735 = 539603) B539603
theorem B359755 : Blo 358757 359755 := bstep (se 1 (by rfl) ⟨269816, by rfl⟩ : syracuseStep 359755 = 539633) B539633
theorem B359767 : Blo 358757 359767 := bstep (se 1 (by rfl) ⟨269825, by rfl⟩ : syracuseStep 359767 = 539651) B539651
theorem B359787 : Blo 358757 359787 := bstep (se 1 (by rfl) ⟨269840, by rfl⟩ : syracuseStep 359787 = 539681) B539681
theorem B359799 : Blo 358757 359799 := bstep (se 1 (by rfl) ⟨269849, by rfl⟩ : syracuseStep 359799 = 539699) B539699
theorem B359819 : Blo 358757 359819 := bstep (se 1 (by rfl) ⟨269864, by rfl⟩ : syracuseStep 359819 = 539729) B539729
theorem B359831 : Blo 358757 359831 := bstep (se 1 (by rfl) ⟨269873, by rfl⟩ : syracuseStep 359831 = 539747) B539747
theorem B359851 : Blo 358757 359851 := bstep (se 1 (by rfl) ⟨269888, by rfl⟩ : syracuseStep 359851 = 539777) B539777
theorem B359863 : Blo 358757 359863 := bstep (se 1 (by rfl) ⟨269897, by rfl⟩ : syracuseStep 359863 = 539795) B539795
theorem B359883 : Blo 358757 359883 := bstep (se 1 (by rfl) ⟨269912, by rfl⟩ : syracuseStep 359883 = 539825) B539825
theorem B359895 : Blo 358757 359895 := bstep (se 1 (by rfl) ⟨269921, by rfl⟩ : syracuseStep 359895 = 539843) B539843
theorem B359915 : Blo 358757 359915 := bstep (se 1 (by rfl) ⟨269936, by rfl⟩ : syracuseStep 359915 = 539873) B539873
theorem B359927 : Blo 358757 359927 := bstep (se 1 (by rfl) ⟨269945, by rfl⟩ : syracuseStep 359927 = 539891) B539891
theorem B359947 : Blo 358757 359947 := bstep (se 1 (by rfl) ⟨269960, by rfl⟩ : syracuseStep 359947 = 539921) B539921
theorem B359959 : Blo 358757 359959 := bstep (se 1 (by rfl) ⟨269969, by rfl⟩ : syracuseStep 359959 = 539939) B539939
theorem B359979 : Blo 358757 359979 := bstep (se 1 (by rfl) ⟨269984, by rfl⟩ : syracuseStep 359979 = 539969) B539969
theorem B359991 : Blo 358757 359991 := bstep (se 1 (by rfl) ⟨269993, by rfl⟩ : syracuseStep 359991 = 539987) B539987
theorem B360011 : Blo 358757 360011 := bstep (se 1 (by rfl) ⟨270008, by rfl⟩ : syracuseStep 360011 = 540017) B540017
theorem B360023 : Blo 358757 360023 := bstep (se 1 (by rfl) ⟨270017, by rfl⟩ : syracuseStep 360023 = 540035) B540035
theorem B360043 : Blo 358757 360043 := bstep (se 1 (by rfl) ⟨270032, by rfl⟩ : syracuseStep 360043 = 540065) B540065
theorem B360055 : Blo 358757 360055 := bstep (se 1 (by rfl) ⟨270041, by rfl⟩ : syracuseStep 360055 = 540083) B540083
theorem B360075 : Blo 358757 360075 := bstep (se 1 (by rfl) ⟨270056, by rfl⟩ : syracuseStep 360075 = 540113) B540113
theorem B360087 : Blo 358757 360087 := bstep (se 1 (by rfl) ⟨270065, by rfl⟩ : syracuseStep 360087 = 540131) B540131
theorem B360107 : Blo 358757 360107 := bstep (se 1 (by rfl) ⟨270080, by rfl⟩ : syracuseStep 360107 = 540161) B540161
theorem B1212083 : Blo 358757 1212083 := bstep (se 1 (by rfl) ⟨909062, by rfl⟩ : syracuseStep 1212083 = 1818125) B1818125
theorem B360119 : Blo 358757 360119 := bstep (se 1 (by rfl) ⟨270089, by rfl⟩ : syracuseStep 360119 = 540179) B540179
theorem B360139 : Blo 358757 360139 := bstep (se 1 (by rfl) ⟨270104, by rfl⟩ : syracuseStep 360139 = 540209) B540209
theorem B360151 : Blo 358757 360151 := bstep (se 1 (by rfl) ⟨270113, by rfl⟩ : syracuseStep 360151 = 540227) B540227
theorem B458455 : Blo 358757 458455 := bstep (se 1 (by rfl) ⟨343841, by rfl⟩ : syracuseStep 458455 = 687683) B687683
theorem B2752217 : Blo 358757 2752217 := bstep (se 2 (by rfl) ⟨1032081, by rfl⟩ : syracuseStep 2752217 = 2064163) B2064163
theorem B360171 : Blo 358757 360171 := bstep (se 1 (by rfl) ⟨270128, by rfl⟩ : syracuseStep 360171 = 540257) B540257
theorem B360183 : Blo 358757 360183 := bstep (se 1 (by rfl) ⟨270137, by rfl⟩ : syracuseStep 360183 = 540275) B540275
theorem B360203 : Blo 358757 360203 := bstep (se 1 (by rfl) ⟨270152, by rfl⟩ : syracuseStep 360203 = 540305) B540305
theorem B360215 : Blo 358757 360215 := bstep (se 1 (by rfl) ⟨270161, by rfl⟩ : syracuseStep 360215 = 540323) B540323
theorem B360235 : Blo 358757 360235 := bstep (se 1 (by rfl) ⟨270176, by rfl⟩ : syracuseStep 360235 = 540353) B540353
theorem B360247 : Blo 358757 360247 := bstep (se 1 (by rfl) ⟨270185, by rfl⟩ : syracuseStep 360247 = 540371) B540371
theorem B360267 : Blo 358757 360267 := bstep (se 1 (by rfl) ⟨270200, by rfl⟩ : syracuseStep 360267 = 540401) B540401
theorem B360279 : Blo 358757 360279 := bstep (se 1 (by rfl) ⟨270209, by rfl⟩ : syracuseStep 360279 = 540419) B540419
theorem B360299 : Blo 358757 360299 := bstep (se 1 (by rfl) ⟨270224, by rfl⟩ : syracuseStep 360299 = 540449) B540449
theorem B360311 : Blo 358757 360311 := bstep (se 1 (by rfl) ⟨270233, by rfl⟩ : syracuseStep 360311 = 540467) B540467
theorem B360331 : Blo 358757 360331 := bstep (se 1 (by rfl) ⟨270248, by rfl⟩ : syracuseStep 360331 = 540497) B540497
theorem B360343 : Blo 358757 360343 := bstep (se 1 (by rfl) ⟨270257, by rfl⟩ : syracuseStep 360343 = 540515) B540515
theorem B360363 : Blo 358757 360363 := bstep (se 1 (by rfl) ⟨270272, by rfl⟩ : syracuseStep 360363 = 540545) B540545
theorem B360375 : Blo 358757 360375 := bstep (se 1 (by rfl) ⟨270281, by rfl⟩ : syracuseStep 360375 = 540563) B540563
theorem B1212353 : Blo 358757 1212353 := bstep (se 2 (by rfl) ⟨454632, by rfl⟩ : syracuseStep 1212353 = 909265) B909265
theorem B360395 : Blo 358757 360395 := bstep (se 1 (by rfl) ⟨270296, by rfl⟩ : syracuseStep 360395 = 540593) B540593
theorem B1540043 : Blo 358757 1540043 := bstep (se 1 (by rfl) ⟨1155032, by rfl⟩ : syracuseStep 1540043 = 2310065) B2310065
theorem B360407 : Blo 358757 360407 := bstep (se 1 (by rfl) ⟨270305, by rfl⟩ : syracuseStep 360407 = 540611) B540611
theorem B360427 : Blo 358757 360427 := bstep (se 1 (by rfl) ⟨270320, by rfl⟩ : syracuseStep 360427 = 540641) B540641
theorem B688115 : Blo 358757 688115 := bstep (se 1 (by rfl) ⟨516086, by rfl⟩ : syracuseStep 688115 = 1032173) B1032173
theorem B360439 : Blo 358757 360439 := bstep (se 1 (by rfl) ⟨270329, by rfl⟩ : syracuseStep 360439 = 540659) B540659
theorem B360455 : Blo 358757 360455 := bstep (se 1 (by rfl) ⟨270341, by rfl⟩ : syracuseStep 360455 = 540683) B540683
theorem B360463 : Blo 358757 360463 := bstep (se 1 (by rfl) ⟨270347, by rfl⟩ : syracuseStep 360463 = 540695) B540695
theorem B360507 : Blo 358757 360507 := bstep (se 1 (by rfl) ⟨270380, by rfl⟩ : syracuseStep 360507 = 540761) B540761
theorem B360583 : Blo 358757 360583 := bstep (se 1 (by rfl) ⟨270437, by rfl⟩ : syracuseStep 360583 = 540875) B540875
theorem B917639 : Blo 358757 917639 := bstep (se 1 (by rfl) ⟨688229, by rfl⟩ : syracuseStep 917639 = 1376459) B1376459
theorem B360591 : Blo 358757 360591 := bstep (se 1 (by rfl) ⟨270443, by rfl⟩ : syracuseStep 360591 = 540887) B540887
theorem B917689 : Blo 358757 917689 := bstep (se 2 (by rfl) ⟨344133, by rfl⟩ : syracuseStep 917689 = 688267) B688267
theorem B688313 : Blo 358757 688313 := bstep (se 2 (by rfl) ⟨258117, by rfl⟩ : syracuseStep 688313 = 516235) B516235
theorem B360635 : Blo 358757 360635 := bstep (se 1 (by rfl) ⟨270476, by rfl⟩ : syracuseStep 360635 = 540953) B540953
theorem B360711 : Blo 358757 360711 := bstep (se 1 (by rfl) ⟨270533, by rfl⟩ : syracuseStep 360711 = 541067) B541067
theorem B1540367 : Blo 358757 1540367 := bstep (se 1 (by rfl) ⟨1155275, by rfl⟩ : syracuseStep 1540367 = 2310551) B2310551
theorem B360719 : Blo 358757 360719 := bstep (se 1 (by rfl) ⟨270539, by rfl⟩ : syracuseStep 360719 = 541079) B541079
theorem B1835297 : Blo 358757 1835297 := bstep (se 2 (by rfl) ⟨688236, by rfl⟩ : syracuseStep 1835297 = 1376473) B1376473
theorem B1212731 : Blo 358757 1212731 := bstep (se 1 (by rfl) ⟨909548, by rfl⟩ : syracuseStep 1212731 = 1819097) B1819097
theorem B360763 : Blo 358757 360763 := bstep (se 1 (by rfl) ⟨270572, by rfl⟩ : syracuseStep 360763 = 541145) B541145
theorem B35553649 : Blo 358757 35553649 := bstep (se 2 (by rfl) ⟨13332618, by rfl⟩ : syracuseStep 35553649 = 26665237) B26665237
theorem B360839 : Blo 358757 360839 := bstep (se 1 (by rfl) ⟨270629, by rfl⟩ : syracuseStep 360839 = 541259) B541259
theorem B360847 : Blo 358757 360847 := bstep (se 1 (by rfl) ⟨270635, by rfl⟩ : syracuseStep 360847 = 541271) B541271
theorem B360891 : Blo 358757 360891 := bstep (se 1 (by rfl) ⟨270668, by rfl⟩ : syracuseStep 360891 = 541337) B541337
theorem B360967 : Blo 358757 360967 := bstep (se 1 (by rfl) ⟨270725, by rfl⟩ : syracuseStep 360967 = 541451) B541451
theorem B360975 : Blo 358757 360975 := bstep (se 1 (by rfl) ⟨270731, by rfl⟩ : syracuseStep 360975 = 541463) B541463
theorem B688655 : Blo 358757 688655 := bstep (se 1 (by rfl) ⟨516491, by rfl⟩ : syracuseStep 688655 = 1032983) B1032983
theorem B361019 : Blo 358757 361019 := bstep (se 1 (by rfl) ⟨270764, by rfl⟩ : syracuseStep 361019 = 541529) B541529
theorem B1540727 : Blo 358757 1540727 := bstep (se 1 (by rfl) ⟨1155545, by rfl⟩ : syracuseStep 1540727 = 2311091) B2311091
theorem B361095 : Blo 358757 361095 := bstep (se 1 (by rfl) ⟨270821, by rfl⟩ : syracuseStep 361095 = 541643) B541643
theorem B361103 : Blo 358757 361103 := bstep (se 1 (by rfl) ⟨270827, by rfl⟩ : syracuseStep 361103 = 541655) B541655
theorem B361147 : Blo 358757 361147 := bstep (se 1 (by rfl) ⟨270860, by rfl⟩ : syracuseStep 361147 = 541721) B541721
theorem B2917093 : Blo 358757 2917093 := bstep (se 4 (by rfl) ⟨273477, by rfl⟩ : syracuseStep 2917093 = 546955) B546955
theorem B361223 : Blo 358757 361223 := bstep (se 1 (by rfl) ⟨270917, by rfl⟩ : syracuseStep 361223 = 541835) B541835
theorem B361231 : Blo 358757 361231 := bstep (se 1 (by rfl) ⟨270923, by rfl⟩ : syracuseStep 361231 = 541847) B541847
theorem B1213217 : Blo 358757 1213217 := bstep (se 2 (by rfl) ⟨454956, by rfl⟩ : syracuseStep 1213217 = 909913) B909913
theorem B361275 : Blo 358757 361275 := bstep (se 1 (by rfl) ⟨270956, by rfl⟩ : syracuseStep 361275 = 541913) B541913
theorem B820103 : Blo 358757 820103 := bstep (se 1 (by rfl) ⟨615077, by rfl⟩ : syracuseStep 820103 = 1230155) B1230155
theorem B361351 : Blo 358757 361351 := bstep (se 1 (by rfl) ⟨271013, by rfl⟩ : syracuseStep 361351 = 542027) B542027
theorem B361359 : Blo 358757 361359 := bstep (se 1 (by rfl) ⟨271019, by rfl⟩ : syracuseStep 361359 = 542039) B542039
theorem B3900311 : Blo 358757 3900311 := bstep (se 1 (by rfl) ⟨2925233, by rfl⟩ : syracuseStep 3900311 = 5850467) B5850467
theorem B361403 : Blo 358757 361403 := bstep (se 1 (by rfl) ⟨271052, by rfl⟩ : syracuseStep 361403 = 542105) B542105
theorem B1377233 : Blo 358757 1377233 := bstep (se 2 (by rfl) ⟨516462, by rfl⟩ : syracuseStep 1377233 = 1032925) B1032925
theorem B361479 : Blo 358757 361479 := bstep (se 1 (by rfl) ⟨271109, by rfl⟩ : syracuseStep 361479 = 542219) B542219
theorem B361487 : Blo 358757 361487 := bstep (se 1 (by rfl) ⟨271115, by rfl⟩ : syracuseStep 361487 = 542231) B542231
theorem B656417 : Blo 358757 656417 := bstep (se 2 (by rfl) ⟨246156, by rfl⟩ : syracuseStep 656417 = 492313) B492313
theorem B361531 : Blo 358757 361531 := bstep (se 1 (by rfl) ⟨271148, by rfl⟩ : syracuseStep 361531 = 542297) B542297
theorem B361607 : Blo 358757 361607 := bstep (se 1 (by rfl) ⟨271205, by rfl⟩ : syracuseStep 361607 = 542411) B542411
theorem B361615 : Blo 358757 361615 := bstep (se 1 (by rfl) ⟨271211, by rfl⟩ : syracuseStep 361615 = 542423) B542423
theorem B361659 : Blo 358757 361659 := bstep (se 1 (by rfl) ⟨271244, by rfl⟩ : syracuseStep 361659 = 542489) B542489
theorem B1836269 : Blo 358757 1836269 := bstep (se 3 (by rfl) ⟨344300, by rfl⟩ : syracuseStep 1836269 = 688601) B688601
theorem B361735 : Blo 358757 361735 := bstep (se 1 (by rfl) ⟨271301, by rfl⟩ : syracuseStep 361735 = 542603) B542603
theorem B361743 : Blo 358757 361743 := bstep (se 1 (by rfl) ⟨271307, by rfl⟩ : syracuseStep 361743 = 542615) B542615
theorem B361787 : Blo 358757 361787 := bstep (se 1 (by rfl) ⟨271340, by rfl⟩ : syracuseStep 361787 = 542681) B542681
theorem B1213811 : Blo 358757 1213811 := bstep (se 1 (by rfl) ⟨910358, by rfl⟩ : syracuseStep 1213811 = 1820717) B1820717
theorem B361863 : Blo 358757 361863 := bstep (se 1 (by rfl) ⟨271397, by rfl⟩ : syracuseStep 361863 = 542795) B542795
theorem B361871 : Blo 358757 361871 := bstep (se 1 (by rfl) ⟨271403, by rfl⟩ : syracuseStep 361871 = 542807) B542807
theorem B12387761 : Blo 358757 12387761 := bstep (se 2 (by rfl) ⟨4645410, by rfl⟩ : syracuseStep 12387761 = 9290821) B9290821
theorem B361915 : Blo 358757 361915 := bstep (se 1 (by rfl) ⟨271436, by rfl⟩ : syracuseStep 361915 = 542873) B542873
theorem B361991 : Blo 358757 361991 := bstep (se 1 (by rfl) ⟨271493, by rfl⟩ : syracuseStep 361991 = 542987) B542987
theorem B361999 : Blo 358757 361999 := bstep (se 1 (by rfl) ⟨271499, by rfl⟩ : syracuseStep 361999 = 542999) B542999
theorem B362043 : Blo 358757 362043 := bstep (se 1 (by rfl) ⟨271532, by rfl⟩ : syracuseStep 362043 = 543065) B543065
theorem B1541699 : Blo 358757 1541699 := bstep (se 1 (by rfl) ⟨1156274, by rfl⟩ : syracuseStep 1541699 = 2312549) B2312549
theorem B362119 : Blo 358757 362119 := bstep (se 1 (by rfl) ⟨271589, by rfl⟩ : syracuseStep 362119 = 543179) B543179
theorem B362127 : Blo 358757 362127 := bstep (se 1 (by rfl) ⟨271595, by rfl⟩ : syracuseStep 362127 = 543191) B543191
theorem B362171 : Blo 358757 362171 := bstep (se 1 (by rfl) ⟨271628, by rfl⟩ : syracuseStep 362171 = 543257) B543257
theorem B362247 : Blo 358757 362247 := bstep (se 1 (by rfl) ⟨271685, by rfl⟩ : syracuseStep 362247 = 543371) B543371
theorem B362255 : Blo 358757 362255 := bstep (se 1 (by rfl) ⟨271691, by rfl⟩ : syracuseStep 362255 = 543383) B543383
theorem B362299 : Blo 358757 362299 := bstep (se 1 (by rfl) ⟨271724, by rfl⟩ : syracuseStep 362299 = 543449) B543449
theorem B362375 : Blo 358757 362375 := bstep (se 1 (by rfl) ⟨271781, by rfl⟩ : syracuseStep 362375 = 543563) B543563
theorem B362383 : Blo 358757 362383 := bstep (se 1 (by rfl) ⟨271787, by rfl⟩ : syracuseStep 362383 = 543575) B543575
theorem B1542041 : Blo 358757 1542041 := bstep (se 2 (by rfl) ⟨578265, by rfl⟩ : syracuseStep 1542041 = 1156531) B1156531
theorem B362427 : Blo 358757 362427 := bstep (se 1 (by rfl) ⟨271820, by rfl⟩ : syracuseStep 362427 = 543641) B543641
theorem B362503 : Blo 358757 362503 := bstep (se 1 (by rfl) ⟨271877, by rfl⟩ : syracuseStep 362503 = 543755) B543755
theorem B362511 : Blo 358757 362511 := bstep (se 1 (by rfl) ⟨271883, by rfl⟩ : syracuseStep 362511 = 543767) B543767
theorem B362555 : Blo 358757 362555 := bstep (se 1 (by rfl) ⟨271916, by rfl⟩ : syracuseStep 362555 = 543833) B543833
theorem B2754647 : Blo 358757 2754647 := bstep (se 1 (by rfl) ⟨2065985, by rfl⟩ : syracuseStep 2754647 = 4131971) B4131971
theorem B1738871 : Blo 358757 1738871 := bstep (se 1 (by rfl) ⟨1304153, by rfl⟩ : syracuseStep 1738871 = 2608307) B2608307
theorem B3082373 : Blo 358757 3082373 := bstep (se 4 (by rfl) ⟨288972, by rfl⟩ : syracuseStep 3082373 = 577945) B577945
theorem B362631 : Blo 358757 362631 := bstep (se 1 (by rfl) ⟨271973, by rfl⟩ : syracuseStep 362631 = 543947) B543947
theorem B362639 : Blo 358757 362639 := bstep (se 1 (by rfl) ⟨271979, by rfl⟩ : syracuseStep 362639 = 543959) B543959
theorem B362683 : Blo 358757 362683 := bstep (se 1 (by rfl) ⟨272012, by rfl⟩ : syracuseStep 362683 = 544025) B544025
theorem B2787529 : Blo 358757 2787529 := bstep (se 2 (by rfl) ⟨1045323, by rfl⟩ : syracuseStep 2787529 = 2090647) B2090647
theorem B3083123 : Blo 358757 3083123 := bstep (se 1 (by rfl) ⟨2312342, by rfl⟩ : syracuseStep 3083123 = 4624685) B4624685
theorem B2231185 : Blo 358757 2231185 := bstep (se 2 (by rfl) ⟨836694, by rfl⟩ : syracuseStep 2231185 = 1673389) B1673389
theorem B8293387 : Blo 358757 8293387 := bstep (se 1 (by rfl) ⟨6220040, by rfl⟩ : syracuseStep 8293387 = 12440081) B12440081
theorem B1150355 : Blo 358757 1150355 := bstep (se 1 (by rfl) ⟨862766, by rfl⟩ : syracuseStep 1150355 = 1725533) B1725533
theorem B1216403 : Blo 358757 1216403 := bstep (se 1 (by rfl) ⟨912302, by rfl⟩ : syracuseStep 1216403 = 1824605) B1824605
theorem B823241 : Blo 358757 823241 := bstep (se 2 (by rfl) ⟨308715, by rfl⟩ : syracuseStep 823241 = 617431) B617431
theorem B4690649 : Blo 358757 4690649 := bstep (se 2 (by rfl) ⟨1758993, by rfl⟩ : syracuseStep 4690649 = 3517987) B3517987
theorem B431239 : Blo 358757 431239 := bstep (se 1 (by rfl) ⟨323429, by rfl⟩ : syracuseStep 431239 = 646859) B646859
theorem B464059 : Blo 358757 464059 := bstep (se 1 (by rfl) ⟨348044, by rfl⟩ : syracuseStep 464059 = 696089) B696089
theorem B1217807 : Blo 358757 1217807 := bstep (se 1 (by rfl) ⟨913355, by rfl⟩ : syracuseStep 1217807 = 1826711) B1826711
theorem B1218077 : Blo 358757 1218077 := bstep (se 3 (by rfl) ⟨228389, by rfl⟩ : syracuseStep 1218077 = 456779) B456779
theorem B1021967 : Blo 358757 1021967 := bstep (se 1 (by rfl) ⟨766475, by rfl⟩ : syracuseStep 1021967 = 1532951) B1532951
theorem B923849 : Blo 358757 923849 := bstep (se 2 (by rfl) ⟨346443, by rfl⟩ : syracuseStep 923849 = 692887) B692887
theorem B1022209 : Blo 358757 1022209 := bstep (se 2 (by rfl) ⟨383328, by rfl⟩ : syracuseStep 1022209 = 766657) B766657
theorem B1153597 : Blo 358757 1153597 := bstep (se 3 (by rfl) ⟨216299, by rfl⟩ : syracuseStep 1153597 = 432599) B432599
theorem B2202173 : Blo 358757 2202173 := bstep (se 3 (by rfl) ⟨412907, by rfl⟩ : syracuseStep 2202173 = 825815) B825815
theorem B6232643 : Blo 358757 6232643 := bstep (se 1 (by rfl) ⟨4674482, by rfl⟩ : syracuseStep 6232643 = 9348965) B9348965
theorem B432911 : Blo 358757 432911 := bstep (se 1 (by rfl) ⟨324683, by rfl⟩ : syracuseStep 432911 = 649367) B649367
theorem B4397975 : Blo 358757 4397975 := bstep (se 1 (by rfl) ⟨3298481, by rfl⟩ : syracuseStep 4397975 = 6596963) B6596963
theorem B1219481 : Blo 358757 1219481 := bstep (se 2 (by rfl) ⟨457305, by rfl⟩ : syracuseStep 1219481 = 914611) B914611
theorem B2595851 : Blo 358757 2595851 := bstep (se 1 (by rfl) ⟨1946888, by rfl⟩ : syracuseStep 2595851 = 3893777) B3893777
theorem B990323 : Blo 358757 990323 := bstep (se 1 (by rfl) ⟨742742, by rfl⟩ : syracuseStep 990323 = 1485485) B1485485
theorem B695567 : Blo 358757 695567 := bstep (se 1 (by rfl) ⟨521675, by rfl⟩ : syracuseStep 695567 = 1043351) B1043351
theorem B4660739 : Blo 358757 4660739 := bstep (se 1 (by rfl) ⟨3495554, by rfl⟩ : syracuseStep 4660739 = 6991109) B6991109
theorem B4955651 : Blo 358757 4955651 := bstep (se 1 (by rfl) ⟨3716738, by rfl⟩ : syracuseStep 4955651 = 7433477) B7433477
theorem B1220183 : Blo 358757 1220183 := bstep (se 1 (by rfl) ⟨915137, by rfl⟩ : syracuseStep 1220183 = 1830275) B1830275
theorem B1023607 : Blo 358757 1023607 := bstep (se 1 (by rfl) ⟨767705, by rfl⟩ : syracuseStep 1023607 = 1535411) B1535411
theorem B2924225 : Blo 358757 2924225 := bstep (se 2 (by rfl) ⟨1096584, by rfl⟩ : syracuseStep 2924225 = 2193169) B2193169
theorem B1154969 : Blo 358757 1154969 := bstep (se 2 (by rfl) ⟨433113, by rfl⟩ : syracuseStep 1154969 = 866227) B866227
theorem B1220669 : Blo 358757 1220669 := bstep (se 3 (by rfl) ⟨228875, by rfl⟩ : syracuseStep 1220669 = 457751) B457751
theorem B1549115 : Blo 358757 1549115 := bstep (se 1 (by rfl) ⟨1161836, by rfl⟩ : syracuseStep 1549115 = 2323673) B2323673
theorem B1024883 : Blo 358757 1024883 := bstep (se 1 (by rfl) ⟨768662, by rfl⟩ : syracuseStep 1024883 = 1537325) B1537325
theorem B762895 : Blo 358757 762895 := bstep (se 1 (by rfl) ⟨572171, by rfl⟩ : syracuseStep 762895 = 1144343) B1144343
theorem B1025111 : Blo 358757 1025111 := bstep (se 1 (by rfl) ⟨768833, by rfl⟩ : syracuseStep 1025111 = 1537667) B1537667
theorem B14787971 : Blo 358757 14787971 := bstep (se 1 (by rfl) ⟨11090978, by rfl⟩ : syracuseStep 14787971 = 22181957) B22181957
theorem B1222073 : Blo 358757 1222073 := bstep (se 2 (by rfl) ⟨458277, by rfl⟩ : syracuseStep 1222073 = 916555) B916555
theorem B1222667 : Blo 358757 1222667 := bstep (se 1 (by rfl) ⟨917000, by rfl⟩ : syracuseStep 1222667 = 1834001) B1834001
theorem B1222775 : Blo 358757 1222775 := bstep (se 1 (by rfl) ⟨917081, by rfl⟩ : syracuseStep 1222775 = 1834163) B1834163
theorem B403771 : Blo 358757 403771 := bstep (se 1 (by rfl) ⟨302828, by rfl⟩ : syracuseStep 403771 = 605657) B605657
theorem B1681817 : Blo 358757 1681817 := bstep (se 2 (by rfl) ⟨630681, by rfl⟩ : syracuseStep 1681817 = 1261363) B1261363
theorem B1943993 : Blo 358757 1943993 := bstep (se 2 (by rfl) ⟨728997, by rfl⟩ : syracuseStep 1943993 = 1457995) B1457995
theorem B1026695 : Blo 358757 1026695 := bstep (se 1 (by rfl) ⟨770021, by rfl⟩ : syracuseStep 1026695 = 1540043) B1540043
theorem B1223369 : Blo 358757 1223369 := bstep (se 2 (by rfl) ⟨458763, by rfl⟩ : syracuseStep 1223369 = 917527) B917527
theorem B404239 : Blo 358757 404239 := bstep (se 1 (by rfl) ⟨303179, by rfl⟩ : syracuseStep 404239 = 606359) B606359
theorem B1026877 : Blo 358757 1026877 := bstep (se 3 (by rfl) ⟨192539, by rfl⟩ : syracuseStep 1026877 = 385079) B385079
theorem B404743 : Blo 358757 404743 := bstep (se 1 (by rfl) ⟨303557, by rfl⟩ : syracuseStep 404743 = 607115) B607115
theorem B1027343 : Blo 358757 1027343 := bstep (se 1 (by rfl) ⟨770507, by rfl⟩ : syracuseStep 1027343 = 1541015) B1541015
theorem B2043251 : Blo 358757 2043251 := bstep (se 1 (by rfl) ⟨1532438, by rfl⟩ : syracuseStep 2043251 = 3064877) B3064877
theorem B1224071 : Blo 358757 1224071 := bstep (se 1 (by rfl) ⟨918053, by rfl⟩ : syracuseStep 1224071 = 1836107) B1836107
theorem B404923 : Blo 358757 404923 := bstep (se 1 (by rfl) ⟨303692, by rfl⟩ : syracuseStep 404923 = 607385) B607385
theorem B2600525 : Blo 358757 2600525 := bstep (se 3 (by rfl) ⟨487598, by rfl⟩ : syracuseStep 2600525 = 975197) B975197
theorem B3518029 : Blo 358757 3518029 := bstep (se 3 (by rfl) ⟨659630, by rfl⟩ : syracuseStep 3518029 = 1319261) B1319261
theorem B2076353 : Blo 358757 2076353 := bstep (se 2 (by rfl) ⟨778632, by rfl⟩ : syracuseStep 2076353 = 1557265) B1557265
theorem B3288883 : Blo 358757 3288883 := bstep (se 1 (by rfl) ⟨2466662, by rfl⟩ : syracuseStep 3288883 = 4933325) B4933325
theorem B405391 : Blo 358757 405391 := bstep (se 1 (by rfl) ⟨304043, by rfl⟩ : syracuseStep 405391 = 608087) B608087
theorem B634895 : Blo 358757 634895 := bstep (se 1 (by rfl) ⟨476171, by rfl⟩ : syracuseStep 634895 = 952343) B952343
theorem B405895 : Blo 358757 405895 := bstep (se 1 (by rfl) ⟨304421, by rfl⟩ : syracuseStep 405895 = 608843) B608843
theorem B1028609 : Blo 358757 1028609 := bstep (se 2 (by rfl) ⟨385728, by rfl⟩ : syracuseStep 1028609 = 771457) B771457
theorem B406075 : Blo 358757 406075 := bstep (se 1 (by rfl) ⟨304556, by rfl⟩ : syracuseStep 406075 = 609113) B609113
theorem B2044709 : Blo 358757 2044709 := bstep (se 4 (by rfl) ⟨191691, by rfl⟩ : syracuseStep 2044709 = 383383) B383383
theorem B406543 : Blo 358757 406543 := bstep (se 1 (by rfl) ⟨304907, by rfl⟩ : syracuseStep 406543 = 609815) B609815
theorem B865399 : Blo 358757 865399 := bstep (se 1 (by rfl) ⟨649049, by rfl⟩ : syracuseStep 865399 = 1298099) B1298099
theorem B3519875 : Blo 358757 3519875 := bstep (se 1 (by rfl) ⟨2639906, by rfl⟩ : syracuseStep 3519875 = 5279813) B5279813
theorem B407047 : Blo 358757 407047 := bstep (se 1 (by rfl) ⟨305285, by rfl⟩ : syracuseStep 407047 = 610571) B610571
theorem B2045483 : Blo 358757 2045483 := bstep (se 1 (by rfl) ⟨1534112, by rfl⟩ : syracuseStep 2045483 = 3068225) B3068225
theorem B538169 : Blo 358757 538169 := bstep (se 2 (by rfl) ⟨201813, by rfl⟩ : syracuseStep 538169 = 403627) B403627
theorem B4961893 : Blo 358757 4961893 := bstep (se 4 (by rfl) ⟨465177, by rfl⟩ : syracuseStep 4961893 = 930355) B930355
theorem B538247 : Blo 358757 538247 := bstep (se 1 (by rfl) ⟨403685, by rfl⟩ : syracuseStep 538247 = 807371) B807371
theorem B538283 : Blo 358757 538283 := bstep (se 1 (by rfl) ⟨403712, by rfl⟩ : syracuseStep 538283 = 807425) B807425
theorem B407227 : Blo 358757 407227 := bstep (se 1 (by rfl) ⟨305420, by rfl⟩ : syracuseStep 407227 = 610841) B610841
theorem B538313 : Blo 358757 538313 := bstep (se 2 (by rfl) ⟨201867, by rfl⟩ : syracuseStep 538313 = 403735) B403735
theorem B538427 : Blo 358757 538427 := bstep (se 1 (by rfl) ⟨403820, by rfl⟩ : syracuseStep 538427 = 807641) B807641
theorem B538487 : Blo 358757 538487 := bstep (se 1 (by rfl) ⟨403865, by rfl⟩ : syracuseStep 538487 = 807731) B807731
theorem B538511 : Blo 358757 538511 := bstep (se 1 (by rfl) ⟨403883, by rfl⟩ : syracuseStep 538511 = 807767) B807767
theorem B1816505 : Blo 358757 1816505 := bstep (se 2 (by rfl) ⟨681189, by rfl⟩ : syracuseStep 1816505 = 1362379) B1362379
theorem B538553 : Blo 358757 538553 := bstep (se 2 (by rfl) ⟨201957, by rfl⟩ : syracuseStep 538553 = 403915) B403915
theorem B538631 : Blo 358757 538631 := bstep (se 1 (by rfl) ⟨403973, by rfl⟩ : syracuseStep 538631 = 807947) B807947
theorem B12564497 : Blo 358757 12564497 := bstep (se 2 (by rfl) ⟨4711686, by rfl⟩ : syracuseStep 12564497 = 9423373) B9423373
theorem B538667 : Blo 358757 538667 := bstep (se 1 (by rfl) ⟨404000, by rfl⟩ : syracuseStep 538667 = 808001) B808001
theorem B538697 : Blo 358757 538697 := bstep (se 2 (by rfl) ⟨202011, by rfl⟩ : syracuseStep 538697 = 404023) B404023
theorem B1030259 : Blo 358757 1030259 := bstep (se 1 (by rfl) ⟨772694, by rfl⟩ : syracuseStep 1030259 = 1545389) B1545389
theorem B407695 : Blo 358757 407695 := bstep (se 1 (by rfl) ⟨305771, by rfl⟩ : syracuseStep 407695 = 611543) B611543
theorem B538811 : Blo 358757 538811 := bstep (se 1 (by rfl) ⟨404108, by rfl⟩ : syracuseStep 538811 = 808217) B808217
theorem B538871 : Blo 358757 538871 := bstep (se 1 (by rfl) ⟨404153, by rfl⟩ : syracuseStep 538871 = 808307) B808307
theorem B538895 : Blo 358757 538895 := bstep (se 1 (by rfl) ⟨404171, by rfl⟩ : syracuseStep 538895 = 808343) B808343
theorem B538937 : Blo 358757 538937 := bstep (se 2 (by rfl) ⟨202101, by rfl⟩ : syracuseStep 538937 = 404203) B404203
theorem B539015 : Blo 358757 539015 := bstep (se 1 (by rfl) ⟨404261, by rfl⟩ : syracuseStep 539015 = 808523) B808523
theorem B539051 : Blo 358757 539051 := bstep (se 1 (by rfl) ⟨404288, by rfl⟩ : syracuseStep 539051 = 808577) B808577
theorem B539081 : Blo 358757 539081 := bstep (se 2 (by rfl) ⟨202155, by rfl⟩ : syracuseStep 539081 = 404311) B404311
theorem B768457 : Blo 358757 768457 := bstep (se 2 (by rfl) ⟨288171, by rfl⟩ : syracuseStep 768457 = 576343) B576343
theorem B1030715 : Blo 358757 1030715 := bstep (se 1 (by rfl) ⟨773036, by rfl⟩ : syracuseStep 1030715 = 1546073) B1546073
theorem B539195 : Blo 358757 539195 := bstep (se 1 (by rfl) ⟨404396, by rfl⟩ : syracuseStep 539195 = 808793) B808793
theorem B539255 : Blo 358757 539255 := bstep (se 1 (by rfl) ⟨404441, by rfl⟩ : syracuseStep 539255 = 808883) B808883
theorem B539279 : Blo 358757 539279 := bstep (se 1 (by rfl) ⟨404459, by rfl⟩ : syracuseStep 539279 = 808919) B808919
theorem B539321 : Blo 358757 539321 := bstep (se 2 (by rfl) ⟨202245, by rfl⟩ : syracuseStep 539321 = 404491) B404491
theorem B539399 : Blo 358757 539399 := bstep (se 1 (by rfl) ⟨404549, by rfl⟩ : syracuseStep 539399 = 809099) B809099
theorem B539435 : Blo 358757 539435 := bstep (se 1 (by rfl) ⟨404576, by rfl⟩ : syracuseStep 539435 = 809153) B809153
theorem B539465 : Blo 358757 539465 := bstep (se 2 (by rfl) ⟨202299, by rfl⟩ : syracuseStep 539465 = 404599) B404599
theorem B3881843 : Blo 358757 3881843 := bstep (se 1 (by rfl) ⟨2911382, by rfl⟩ : syracuseStep 3881843 = 5822765) B5822765
theorem B1522547 : Blo 358757 1522547 := bstep (se 1 (by rfl) ⟨1141910, by rfl⟩ : syracuseStep 1522547 = 2283821) B2283821
theorem B768953 : Blo 358757 768953 := bstep (se 2 (by rfl) ⟨288357, by rfl⟩ : syracuseStep 768953 = 576715) B576715
theorem B539579 : Blo 358757 539579 := bstep (se 1 (by rfl) ⟨404684, by rfl⟩ : syracuseStep 539579 = 809369) B809369
theorem B2046941 : Blo 358757 2046941 := bstep (se 3 (by rfl) ⟨383801, by rfl⟩ : syracuseStep 2046941 = 767603) B767603
theorem B539639 : Blo 358757 539639 := bstep (se 1 (by rfl) ⟨404729, by rfl⟩ : syracuseStep 539639 = 809459) B809459
theorem B539663 : Blo 358757 539663 := bstep (se 1 (by rfl) ⟨404747, by rfl⟩ : syracuseStep 539663 = 809495) B809495
theorem B539705 : Blo 358757 539705 := bstep (se 2 (by rfl) ⟨202389, by rfl⟩ : syracuseStep 539705 = 404779) B404779
theorem B4996183 : Blo 358757 4996183 := bstep (se 1 (by rfl) ⟨3747137, by rfl⟩ : syracuseStep 4996183 = 7494275) B7494275
theorem B539783 : Blo 358757 539783 := bstep (se 1 (by rfl) ⟨404837, by rfl⟩ : syracuseStep 539783 = 809675) B809675
theorem B539819 : Blo 358757 539819 := bstep (se 1 (by rfl) ⟨404864, by rfl⟩ : syracuseStep 539819 = 809729) B809729
theorem B1817801 : Blo 358757 1817801 := bstep (se 2 (by rfl) ⟨681675, by rfl⟩ : syracuseStep 1817801 = 1363351) B1363351
theorem B539849 : Blo 358757 539849 := bstep (se 2 (by rfl) ⟨202443, by rfl⟩ : syracuseStep 539849 = 404887) B404887
theorem B1031467 : Blo 358757 1031467 := bstep (se 1 (by rfl) ⟨773600, by rfl⟩ : syracuseStep 1031467 = 1547201) B1547201
theorem B539963 : Blo 358757 539963 := bstep (se 1 (by rfl) ⟨404972, by rfl⟩ : syracuseStep 539963 = 809945) B809945
theorem B540023 : Blo 358757 540023 := bstep (se 1 (by rfl) ⟨405017, by rfl⟩ : syracuseStep 540023 = 810035) B810035
theorem B540047 : Blo 358757 540047 := bstep (se 1 (by rfl) ⟨405035, by rfl⟩ : syracuseStep 540047 = 810071) B810071
theorem B540089 : Blo 358757 540089 := bstep (se 2 (by rfl) ⟨202533, by rfl⟩ : syracuseStep 540089 = 405067) B405067
theorem B540167 : Blo 358757 540167 := bstep (se 1 (by rfl) ⟨405125, by rfl⟩ : syracuseStep 540167 = 810251) B810251
theorem B605711 : Blo 358757 605711 := bstep (se 1 (by rfl) ⟨454283, by rfl⟩ : syracuseStep 605711 = 908567) B908567
theorem B933419 : Blo 358757 933419 := bstep (se 1 (by rfl) ⟨700064, by rfl⟩ : syracuseStep 933419 = 1400129) B1400129
theorem B540203 : Blo 358757 540203 := bstep (se 1 (by rfl) ⟨405152, by rfl⟩ : syracuseStep 540203 = 810305) B810305
theorem B1031741 : Blo 358757 1031741 := bstep (se 3 (by rfl) ⟨193451, by rfl⟩ : syracuseStep 1031741 = 386903) B386903
theorem B540233 : Blo 358757 540233 := bstep (se 2 (by rfl) ⟨202587, by rfl⟩ : syracuseStep 540233 = 405175) B405175
theorem B2735693 : Blo 358757 2735693 := bstep (se 3 (by rfl) ⟨512942, by rfl⟩ : syracuseStep 2735693 = 1025885) B1025885
theorem B540347 : Blo 358757 540347 := bstep (se 1 (by rfl) ⟨405260, by rfl⟩ : syracuseStep 540347 = 810521) B810521
theorem B540407 : Blo 358757 540407 := bstep (se 1 (by rfl) ⟨405305, by rfl⟩ : syracuseStep 540407 = 810611) B810611
theorem B540431 : Blo 358757 540431 := bstep (se 1 (by rfl) ⟨405323, by rfl⟩ : syracuseStep 540431 = 810647) B810647
theorem B540473 : Blo 358757 540473 := bstep (se 2 (by rfl) ⟨202677, by rfl⟩ : syracuseStep 540473 = 405355) B405355
theorem B540551 : Blo 358757 540551 := bstep (se 1 (by rfl) ⟨405413, by rfl⟩ : syracuseStep 540551 = 810827) B810827
theorem B769927 : Blo 358757 769927 := bstep (se 1 (by rfl) ⟨577445, by rfl⟩ : syracuseStep 769927 = 1154891) B1154891
theorem B540587 : Blo 358757 540587 := bstep (se 1 (by rfl) ⟨405440, by rfl⟩ : syracuseStep 540587 = 810881) B810881
theorem B540617 : Blo 358757 540617 := bstep (se 2 (by rfl) ⟨202731, by rfl⟩ : syracuseStep 540617 = 405463) B405463
theorem B2211851 : Blo 358757 2211851 := bstep (se 1 (by rfl) ⟨1658888, by rfl⟩ : syracuseStep 2211851 = 3317777) B3317777
theorem B606251 : Blo 358757 606251 := bstep (se 1 (by rfl) ⟨454688, by rfl⟩ : syracuseStep 606251 = 909377) B909377
theorem B540731 : Blo 358757 540731 := bstep (se 1 (by rfl) ⟨405548, by rfl⟩ : syracuseStep 540731 = 811097) B811097
theorem B540791 : Blo 358757 540791 := bstep (se 1 (by rfl) ⟨405593, by rfl⟩ : syracuseStep 540791 = 811187) B811187
theorem B540815 : Blo 358757 540815 := bstep (se 1 (by rfl) ⟨405611, by rfl⟩ : syracuseStep 540815 = 811223) B811223
theorem B540857 : Blo 358757 540857 := bstep (se 2 (by rfl) ⟨202821, by rfl⟩ : syracuseStep 540857 = 405643) B405643
theorem B3948745 : Blo 358757 3948745 := bstep (se 2 (by rfl) ⟨1480779, by rfl⟩ : syracuseStep 3948745 = 2961559) B2961559
theorem B540935 : Blo 358757 540935 := bstep (se 1 (by rfl) ⟨405701, by rfl⟩ : syracuseStep 540935 = 811403) B811403
theorem B1229089 : Blo 358757 1229089 := bstep (se 2 (by rfl) ⟨460908, by rfl⟩ : syracuseStep 1229089 = 921817) B921817
theorem B540971 : Blo 358757 540971 := bstep (se 1 (by rfl) ⟨405728, by rfl⟩ : syracuseStep 540971 = 811457) B811457
theorem B541001 : Blo 358757 541001 := bstep (se 2 (by rfl) ⟨202875, by rfl⟩ : syracuseStep 541001 = 405751) B405751
theorem B1032583 : Blo 358757 1032583 := bstep (se 1 (by rfl) ⟨774437, by rfl⟩ : syracuseStep 1032583 = 1548875) B1548875
theorem B606649 : Blo 358757 606649 := bstep (se 2 (by rfl) ⟨227493, by rfl⟩ : syracuseStep 606649 = 454987) B454987
theorem B2933177 : Blo 358757 2933177 := bstep (se 2 (by rfl) ⟨1099941, by rfl⟩ : syracuseStep 2933177 = 2199883) B2199883
theorem B541115 : Blo 358757 541115 := bstep (se 1 (by rfl) ⟨405836, by rfl⟩ : syracuseStep 541115 = 811673) B811673
theorem B541175 : Blo 358757 541175 := bstep (se 1 (by rfl) ⟨405881, by rfl⟩ : syracuseStep 541175 = 811763) B811763
theorem B541199 : Blo 358757 541199 := bstep (se 1 (by rfl) ⟨405899, by rfl⟩ : syracuseStep 541199 = 811799) B811799
theorem B868897 : Blo 358757 868897 := bstep (se 2 (by rfl) ⟨325836, by rfl⟩ : syracuseStep 868897 = 651673) B651673
theorem B541241 : Blo 358757 541241 := bstep (se 2 (by rfl) ⟨202965, by rfl⟩ : syracuseStep 541241 = 405931) B405931
theorem B5653111 : Blo 358757 5653111 := bstep (se 1 (by rfl) ⟨4239833, by rfl⟩ : syracuseStep 5653111 = 8479667) B8479667
theorem B541319 : Blo 358757 541319 := bstep (se 1 (by rfl) ⟨405989, by rfl⟩ : syracuseStep 541319 = 811979) B811979
theorem B1032857 : Blo 358757 1032857 := bstep (se 2 (by rfl) ⟨387321, by rfl⟩ : syracuseStep 1032857 = 774643) B774643
theorem B541355 : Blo 358757 541355 := bstep (se 1 (by rfl) ⟨406016, by rfl⟩ : syracuseStep 541355 = 812033) B812033
theorem B8372929 : Blo 358757 8372929 := bstep (se 2 (by rfl) ⟨3139848, by rfl⟩ : syracuseStep 8372929 = 6279697) B6279697
theorem B541385 : Blo 358757 541385 := bstep (se 2 (by rfl) ⟨203019, by rfl⟩ : syracuseStep 541385 = 406039) B406039
theorem B4735705 : Blo 358757 4735705 := bstep (se 2 (by rfl) ⟨1775889, by rfl⟩ : syracuseStep 4735705 = 3551779) B3551779
theorem B3457829 : Blo 358757 3457829 := bstep (se 4 (by rfl) ⟨324171, by rfl⟩ : syracuseStep 3457829 = 648343) B648343
theorem B541499 : Blo 358757 541499 := bstep (se 1 (by rfl) ⟨406124, by rfl⟩ : syracuseStep 541499 = 812249) B812249
theorem B1393523 : Blo 358757 1393523 := bstep (se 1 (by rfl) ⟨1045142, by rfl⟩ : syracuseStep 1393523 = 2090285) B2090285
theorem B541559 : Blo 358757 541559 := bstep (se 1 (by rfl) ⟨406169, by rfl⟩ : syracuseStep 541559 = 812339) B812339
theorem B541583 : Blo 358757 541583 := bstep (se 1 (by rfl) ⟨406187, by rfl⟩ : syracuseStep 541583 = 812375) B812375
theorem B541625 : Blo 358757 541625 := bstep (se 2 (by rfl) ⟨203109, by rfl⟩ : syracuseStep 541625 = 406219) B406219
theorem B541703 : Blo 358757 541703 := bstep (se 1 (by rfl) ⟨406277, by rfl⟩ : syracuseStep 541703 = 812555) B812555
theorem B771115 : Blo 358757 771115 := bstep (se 1 (by rfl) ⟨578336, by rfl⟩ : syracuseStep 771115 = 1156673) B1156673
theorem B541739 : Blo 358757 541739 := bstep (se 1 (by rfl) ⟨406304, by rfl⟩ : syracuseStep 541739 = 812609) B812609
theorem B541769 : Blo 358757 541769 := bstep (se 2 (by rfl) ⟨203163, by rfl⟩ : syracuseStep 541769 = 406327) B406327
theorem B607351 : Blo 358757 607351 := bstep (se 1 (by rfl) ⟨455513, by rfl⟩ : syracuseStep 607351 = 911027) B911027
theorem B2147447 : Blo 358757 2147447 := bstep (se 1 (by rfl) ⟨1610585, by rfl⟩ : syracuseStep 2147447 = 3221171) B3221171
theorem B541883 : Blo 358757 541883 := bstep (se 1 (by rfl) ⟨406412, by rfl⟩ : syracuseStep 541883 = 812825) B812825
theorem B541943 : Blo 358757 541943 := bstep (se 1 (by rfl) ⟨406457, by rfl⟩ : syracuseStep 541943 = 812915) B812915
theorem B541967 : Blo 358757 541967 := bstep (se 1 (by rfl) ⟨406475, by rfl⟩ : syracuseStep 541967 = 812951) B812951
theorem B542009 : Blo 358757 542009 := bstep (se 2 (by rfl) ⟨203253, by rfl⟩ : syracuseStep 542009 = 406507) B406507
theorem B607547 : Blo 358757 607547 := bstep (se 1 (by rfl) ⟨455660, by rfl⟩ : syracuseStep 607547 = 911321) B911321
theorem B542087 : Blo 358757 542087 := bstep (se 1 (by rfl) ⟨406565, by rfl⟩ : syracuseStep 542087 = 813131) B813131
theorem B542123 : Blo 358757 542123 := bstep (se 1 (by rfl) ⟨406592, by rfl⟩ : syracuseStep 542123 = 813185) B813185
theorem B9848243 : Blo 358757 9848243 := bstep (se 1 (by rfl) ⟨7386182, by rfl⟩ : syracuseStep 9848243 = 14772365) B14772365
theorem B1230265 : Blo 358757 1230265 := bstep (se 2 (by rfl) ⟨461349, by rfl⟩ : syracuseStep 1230265 = 922699) B922699
theorem B542153 : Blo 358757 542153 := bstep (se 2 (by rfl) ⟨203307, by rfl⟩ : syracuseStep 542153 = 406615) B406615
theorem B542267 : Blo 358757 542267 := bstep (se 1 (by rfl) ⟨406700, by rfl⟩ : syracuseStep 542267 = 813401) B813401
theorem B542327 : Blo 358757 542327 := bstep (se 1 (by rfl) ⟨406745, by rfl⟩ : syracuseStep 542327 = 813491) B813491
theorem B542351 : Blo 358757 542351 := bstep (se 1 (by rfl) ⟨406763, by rfl⟩ : syracuseStep 542351 = 813527) B813527
theorem B542393 : Blo 358757 542393 := bstep (se 2 (by rfl) ⟨203397, by rfl⟩ : syracuseStep 542393 = 406795) B406795
theorem B607945 : Blo 358757 607945 := bstep (se 2 (by rfl) ⟨227979, by rfl⟩ : syracuseStep 607945 = 455959) B455959
theorem B542471 : Blo 358757 542471 := bstep (se 1 (by rfl) ⟨406853, by rfl⟩ : syracuseStep 542471 = 813707) B813707
theorem B542507 : Blo 358757 542507 := bstep (se 1 (by rfl) ⟨406880, by rfl⟩ : syracuseStep 542507 = 813761) B813761
theorem B542537 : Blo 358757 542537 := bstep (se 2 (by rfl) ⟨203451, by rfl⟩ : syracuseStep 542537 = 406903) B406903
theorem B542651 : Blo 358757 542651 := bstep (se 1 (by rfl) ⟨406988, by rfl⟩ : syracuseStep 542651 = 813977) B813977
theorem B2738123 : Blo 358757 2738123 := bstep (se 1 (by rfl) ⟨2053592, by rfl⟩ : syracuseStep 2738123 = 4107185) B4107185
theorem B542711 : Blo 358757 542711 := bstep (se 1 (by rfl) ⟨407033, by rfl⟩ : syracuseStep 542711 = 814067) B814067
theorem B542735 : Blo 358757 542735 := bstep (se 1 (by rfl) ⟨407051, by rfl⟩ : syracuseStep 542735 = 814103) B814103
theorem B1296413 : Blo 358757 1296413 := bstep (se 3 (by rfl) ⟨243077, by rfl⟩ : syracuseStep 1296413 = 486155) B486155
theorem B542777 : Blo 358757 542777 := bstep (se 2 (by rfl) ⟨203541, by rfl⟩ : syracuseStep 542777 = 407083) B407083
theorem B2050109 : Blo 358757 2050109 := bstep (se 3 (by rfl) ⟨384395, by rfl⟩ : syracuseStep 2050109 = 768791) B768791
theorem B7817309 : Blo 358757 7817309 := bstep (se 3 (by rfl) ⟨1465745, by rfl⟩ : syracuseStep 7817309 = 2931491) B2931491
theorem B542855 : Blo 358757 542855 := bstep (se 1 (by rfl) ⟨407141, by rfl⟩ : syracuseStep 542855 = 814283) B814283
theorem B542891 : Blo 358757 542891 := bstep (se 1 (by rfl) ⟨407168, by rfl⟩ : syracuseStep 542891 = 814337) B814337
theorem B542921 : Blo 358757 542921 := bstep (se 2 (by rfl) ⟨203595, by rfl⟩ : syracuseStep 542921 = 407191) B407191
theorem B7948529 : Blo 358757 7948529 := bstep (se 2 (by rfl) ⟨2980698, by rfl⟩ : syracuseStep 7948529 = 5961397) B5961397
theorem B543035 : Blo 358757 543035 := bstep (se 1 (by rfl) ⟨407276, by rfl⟩ : syracuseStep 543035 = 814553) B814553
theorem B870743 : Blo 358757 870743 := bstep (se 1 (by rfl) ⟨653057, by rfl⟩ : syracuseStep 870743 = 1306115) B1306115
theorem B543095 : Blo 358757 543095 := bstep (se 1 (by rfl) ⟨407321, by rfl⟩ : syracuseStep 543095 = 814643) B814643
theorem B608647 : Blo 358757 608647 := bstep (se 1 (by rfl) ⟨456485, by rfl⟩ : syracuseStep 608647 = 912971) B912971
theorem B543119 : Blo 358757 543119 := bstep (se 1 (by rfl) ⟨407339, by rfl⟩ : syracuseStep 543119 = 814679) B814679
theorem B543161 : Blo 358757 543161 := bstep (se 2 (by rfl) ⟨203685, by rfl⟩ : syracuseStep 543161 = 407371) B407371
theorem B543239 : Blo 358757 543239 := bstep (se 1 (by rfl) ⟨407429, by rfl⟩ : syracuseStep 543239 = 814859) B814859
theorem B543275 : Blo 358757 543275 := bstep (se 1 (by rfl) ⟨407456, by rfl⟩ : syracuseStep 543275 = 814913) B814913
theorem B543305 : Blo 358757 543305 := bstep (se 2 (by rfl) ⟨203739, by rfl⟩ : syracuseStep 543305 = 407479) B407479
theorem B543419 : Blo 358757 543419 := bstep (se 1 (by rfl) ⟨407564, by rfl⟩ : syracuseStep 543419 = 815129) B815129
theorem B4410085 : Blo 358757 4410085 := bstep (se 4 (by rfl) ⟨413445, by rfl⟩ : syracuseStep 4410085 = 826891) B826891
theorem B543479 : Blo 358757 543479 := bstep (se 1 (by rfl) ⟨407609, by rfl⟩ : syracuseStep 543479 = 815219) B815219
theorem B543503 : Blo 358757 543503 := bstep (se 1 (by rfl) ⟨407627, by rfl⟩ : syracuseStep 543503 = 815255) B815255
theorem B543545 : Blo 358757 543545 := bstep (se 2 (by rfl) ⟨203829, by rfl⟩ : syracuseStep 543545 = 407659) B407659
theorem B543623 : Blo 358757 543623 := bstep (se 1 (by rfl) ⟨407717, by rfl⟩ : syracuseStep 543623 = 815435) B815435
theorem B543659 : Blo 358757 543659 := bstep (se 1 (by rfl) ⟨407744, by rfl⟩ : syracuseStep 543659 = 815489) B815489
theorem B543689 : Blo 358757 543689 := bstep (se 2 (by rfl) ⟨203883, by rfl⟩ : syracuseStep 543689 = 407767) B407767
theorem B412679 : Blo 358757 412679 := bstep (se 1 (by rfl) ⟨309509, by rfl⟩ : syracuseStep 412679 = 619019) B619019
theorem B609295 : Blo 358757 609295 := bstep (se 1 (by rfl) ⟨456971, by rfl⟩ : syracuseStep 609295 = 913943) B913943
theorem B543803 : Blo 358757 543803 := bstep (se 1 (by rfl) ⟨407852, by rfl⟩ : syracuseStep 543803 = 815705) B815705
theorem B543863 : Blo 358757 543863 := bstep (se 1 (by rfl) ⟨407897, by rfl⟩ : syracuseStep 543863 = 815795) B815795
theorem B543887 : Blo 358757 543887 := bstep (se 1 (by rfl) ⟨407915, by rfl⟩ : syracuseStep 543887 = 815831) B815831
theorem B543929 : Blo 358757 543929 := bstep (se 2 (by rfl) ⟨203973, by rfl⟩ : syracuseStep 543929 = 407947) B407947
theorem B544007 : Blo 358757 544007 := bstep (se 1 (by rfl) ⟨408005, by rfl⟩ : syracuseStep 544007 = 816011) B816011
theorem B544043 : Blo 358757 544043 := bstep (se 1 (by rfl) ⟨408032, by rfl⟩ : syracuseStep 544043 = 816065) B816065
theorem B544073 : Blo 358757 544073 := bstep (se 2 (by rfl) ⟨204027, by rfl⟩ : syracuseStep 544073 = 408055) B408055
theorem B576953 : Blo 358757 576953 := bstep (se 2 (by rfl) ⟨216357, by rfl⟩ : syracuseStep 576953 = 432715) B432715
theorem B4115933 : Blo 358757 4115933 := bstep (se 3 (by rfl) ⟨771737, by rfl⟩ : syracuseStep 4115933 = 1543475) B1543475
theorem B609835 : Blo 358757 609835 := bstep (se 1 (by rfl) ⟨457376, by rfl⟩ : syracuseStep 609835 = 914753) B914753
theorem B2805367 : Blo 358757 2805367 := bstep (se 1 (by rfl) ⟨2104025, by rfl⟩ : syracuseStep 2805367 = 4208051) B4208051
theorem B609977 : Blo 358757 609977 := bstep (se 2 (by rfl) ⟨228741, by rfl⟩ : syracuseStep 609977 = 457483) B457483
theorem B6311681 : Blo 358757 6311681 := bstep (se 2 (by rfl) ⟨2366880, by rfl⟩ : syracuseStep 6311681 = 4733761) B4733761
theorem B2215795 : Blo 358757 2215795 := bstep (se 1 (by rfl) ⟨1661846, by rfl⟩ : syracuseStep 2215795 = 3323693) B3323693
theorem B970937 : Blo 358757 970937 := bstep (se 2 (by rfl) ⟨364101, by rfl⟩ : syracuseStep 970937 = 728203) B728203
theorem B1036559 : Blo 358757 1036559 := bstep (se 1 (by rfl) ⟨777419, by rfl⟩ : syracuseStep 1036559 = 1554839) B1554839
theorem B971023 : Blo 358757 971023 := bstep (se 1 (by rfl) ⟨728267, by rfl⟩ : syracuseStep 971023 = 1456535) B1456535
theorem B807227 : Blo 358757 807227 := bstep (se 1 (by rfl) ⟨605420, by rfl⟩ : syracuseStep 807227 = 1210841) B1210841
theorem B610679 : Blo 358757 610679 := bstep (se 1 (by rfl) ⟨458009, by rfl⟩ : syracuseStep 610679 = 916019) B916019
theorem B2052499 : Blo 358757 2052499 := bstep (se 1 (by rfl) ⟨1539374, by rfl⟩ : syracuseStep 2052499 = 3078749) B3078749
theorem B807353 : Blo 358757 807353 := bstep (se 2 (by rfl) ⟨302757, by rfl⟩ : syracuseStep 807353 = 605515) B605515
theorem B1036745 : Blo 358757 1036745 := bstep (se 2 (by rfl) ⟨388779, by rfl⟩ : syracuseStep 1036745 = 777559) B777559
theorem B1954307 : Blo 358757 1954307 := bstep (se 1 (by rfl) ⟨1465730, by rfl⟩ : syracuseStep 1954307 = 2931461) B2931461
theorem B2249227 : Blo 358757 2249227 := bstep (se 1 (by rfl) ⟨1686920, by rfl⟩ : syracuseStep 2249227 = 3373841) B3373841
theorem B1299181 : Blo 358757 1299181 := bstep (se 3 (by rfl) ⟨243596, by rfl⟩ : syracuseStep 1299181 = 487193) B487193
theorem B807695 : Blo 358757 807695 := bstep (se 1 (by rfl) ⟨605771, by rfl⟩ : syracuseStep 807695 = 1211543) B1211543
theorem B807713 : Blo 358757 807713 := bstep (se 2 (by rfl) ⟨302892, by rfl⟩ : syracuseStep 807713 = 605785) B605785
theorem B1364795 : Blo 358757 1364795 := bstep (se 1 (by rfl) ⟨1023596, by rfl⟩ : syracuseStep 1364795 = 2047193) B2047193
theorem B611131 : Blo 358757 611131 := bstep (se 1 (by rfl) ⟨458348, by rfl⟩ : syracuseStep 611131 = 916697) B916697
theorem B1823633 : Blo 358757 1823633 := bstep (se 2 (by rfl) ⟨683862, by rfl⟩ : syracuseStep 1823633 = 1367725) B1367725
theorem B611273 : Blo 358757 611273 := bstep (se 2 (by rfl) ⟨229227, by rfl⟩ : syracuseStep 611273 = 458455) B458455
theorem B808055 : Blo 358757 808055 := bstep (se 1 (by rfl) ⟨606041, by rfl⟩ : syracuseStep 808055 = 1212083) B1212083
theorem B513211 : Blo 358757 513211 := bstep (se 1 (by rfl) ⟨384908, by rfl⟩ : syracuseStep 513211 = 769817) B769817
theorem B1365281 : Blo 358757 1365281 := bstep (se 2 (by rfl) ⟨511980, by rfl⟩ : syracuseStep 1365281 = 1023961) B1023961
theorem B808235 : Blo 358757 808235 := bstep (se 1 (by rfl) ⟨606176, by rfl⟩ : syracuseStep 808235 = 1212353) B1212353
theorem B2184583 : Blo 358757 2184583 := bstep (se 1 (by rfl) ⟨1638437, by rfl⟩ : syracuseStep 2184583 = 3276875) B3276875
theorem B2610731 : Blo 358757 2610731 := bstep (se 1 (by rfl) ⟨1958048, by rfl⟩ : syracuseStep 2610731 = 3916097) B3916097
theorem B972407 : Blo 358757 972407 := bstep (se 1 (by rfl) ⟨729305, by rfl⟩ : syracuseStep 972407 = 1458611) B1458611
theorem B611975 : Blo 358757 611975 := bstep (se 1 (by rfl) ⟨458981, by rfl⟩ : syracuseStep 611975 = 917963) B917963
theorem B808595 : Blo 358757 808595 := bstep (se 1 (by rfl) ⟨606446, by rfl⟩ : syracuseStep 808595 = 1212893) B1212893
theorem B808649 : Blo 358757 808649 := bstep (se 2 (by rfl) ⟨303243, by rfl⟩ : syracuseStep 808649 = 606487) B606487
theorem B3888931 : Blo 358757 3888931 := bstep (se 1 (by rfl) ⟨2916698, by rfl⟩ : syracuseStep 3888931 = 5833397) B5833397
theorem B513911 : Blo 358757 513911 := bstep (se 1 (by rfl) ⟨385433, by rfl⟩ : syracuseStep 513911 = 770867) B770867
theorem B2054231 : Blo 358757 2054231 := bstep (se 1 (by rfl) ⟨1540673, by rfl⟩ : syracuseStep 2054231 = 3081347) B3081347
theorem B1366253 : Blo 358757 1366253 := bstep (se 3 (by rfl) ⟨256172, by rfl⟩ : syracuseStep 1366253 = 512345) B512345
theorem B809351 : Blo 358757 809351 := bstep (se 1 (by rfl) ⟨607013, by rfl⟩ : syracuseStep 809351 = 1214027) B1214027
theorem B1366571 : Blo 358757 1366571 := bstep (se 1 (by rfl) ⟨1024928, by rfl⟩ : syracuseStep 1366571 = 2049857) B2049857
theorem B809531 : Blo 358757 809531 := bstep (se 1 (by rfl) ⟨607148, by rfl⟩ : syracuseStep 809531 = 1214297) B1214297
theorem B809657 : Blo 358757 809657 := bstep (se 2 (by rfl) ⟨303621, by rfl⟩ : syracuseStep 809657 = 607243) B607243
theorem B383887 : Blo 358757 383887 := bstep (se 1 (by rfl) ⟨287915, by rfl⟩ : syracuseStep 383887 = 575831) B575831
theorem B1825739 : Blo 358757 1825739 := bstep (se 1 (by rfl) ⟨1369304, by rfl⟩ : syracuseStep 1825739 = 2738609) B2738609
theorem B809999 : Blo 358757 809999 := bstep (se 1 (by rfl) ⟨607499, by rfl⟩ : syracuseStep 809999 = 1214999) B1214999
theorem B810017 : Blo 358757 810017 := bstep (se 2 (by rfl) ⟨303756, by rfl⟩ : syracuseStep 810017 = 607513) B607513
theorem B908435 : Blo 358757 908435 := bstep (se 1 (by rfl) ⟨681326, by rfl⟩ : syracuseStep 908435 = 1362653) B1362653
theorem B2743469 : Blo 358757 2743469 := bstep (se 3 (by rfl) ⟨514400, by rfl⟩ : syracuseStep 2743469 = 1028801) B1028801
theorem B1301761 : Blo 358757 1301761 := bstep (se 2 (by rfl) ⟨488160, by rfl⟩ : syracuseStep 1301761 = 976321) B976321
theorem B515335 : Blo 358757 515335 := bstep (se 1 (by rfl) ⟨386501, by rfl⟩ : syracuseStep 515335 = 773003) B773003
theorem B1465615 : Blo 358757 1465615 := bstep (se 1 (by rfl) ⟨1099211, by rfl⟩ : syracuseStep 1465615 = 2198423) B2198423
theorem B1826063 : Blo 358757 1826063 := bstep (se 1 (by rfl) ⟨1369547, by rfl⟩ : syracuseStep 1826063 = 2739095) B2739095
theorem B3366203 : Blo 358757 3366203 := bstep (se 1 (by rfl) ⟨2524652, by rfl⟩ : syracuseStep 3366203 = 5049305) B5049305
theorem B810359 : Blo 358757 810359 := bstep (se 1 (by rfl) ⟨607769, by rfl⟩ : syracuseStep 810359 = 1215539) B1215539
theorem B908729 : Blo 358757 908729 := bstep (se 2 (by rfl) ⟨340773, by rfl⟩ : syracuseStep 908729 = 681547) B681547
theorem B810539 : Blo 358757 810539 := bstep (se 1 (by rfl) ⟨607904, by rfl⟩ : syracuseStep 810539 = 1215809) B1215809
theorem B1957613 : Blo 358757 1957613 := bstep (se 3 (by rfl) ⟨367052, by rfl⟩ : syracuseStep 1957613 = 734105) B734105
theorem B515899 : Blo 358757 515899 := bstep (se 1 (by rfl) ⟨386924, by rfl⟩ : syracuseStep 515899 = 773849) B773849
theorem B810899 : Blo 358757 810899 := bstep (se 1 (by rfl) ⟨608174, by rfl⟩ : syracuseStep 810899 = 1216349) B1216349
theorem B1302425 : Blo 358757 1302425 := bstep (se 2 (by rfl) ⟨488409, by rfl⟩ : syracuseStep 1302425 = 976819) B976819
theorem B810953 : Blo 358757 810953 := bstep (se 2 (by rfl) ⟨304107, by rfl⟩ : syracuseStep 810953 = 608215) B608215
theorem B647227 : Blo 358757 647227 := bstep (se 1 (by rfl) ⟨485420, by rfl⟩ : syracuseStep 647227 = 970841) B970841
theorem B909427 : Blo 358757 909427 := bstep (se 1 (by rfl) ⟨682070, by rfl⟩ : syracuseStep 909427 = 1364141) B1364141
theorem B614585 : Blo 358757 614585 := bstep (se 2 (by rfl) ⟨230469, by rfl⟩ : syracuseStep 614585 = 460939) B460939
theorem B2515181 : Blo 358757 2515181 := bstep (se 3 (by rfl) ⟨471596, by rfl⟩ : syracuseStep 2515181 = 943193) B943193
theorem B909569 : Blo 358757 909569 := bstep (se 2 (by rfl) ⟨341088, by rfl⟩ : syracuseStep 909569 = 682177) B682177
theorem B549193 : Blo 358757 549193 := bstep (se 2 (by rfl) ⟨205947, by rfl⟩ : syracuseStep 549193 = 411895) B411895
theorem B811655 : Blo 358757 811655 := bstep (se 1 (by rfl) ⟨608741, by rfl⟩ : syracuseStep 811655 = 1217483) B1217483
theorem B1827521 : Blo 358757 1827521 := bstep (se 2 (by rfl) ⟨685320, by rfl⟩ : syracuseStep 1827521 = 1370641) B1370641
theorem B910025 : Blo 358757 910025 := bstep (se 2 (by rfl) ⟨341259, by rfl⟩ : syracuseStep 910025 = 682519) B682519
theorem B811835 : Blo 358757 811835 := bstep (se 1 (by rfl) ⟨608876, by rfl⟩ : syracuseStep 811835 = 1217753) B1217753
theorem B811961 : Blo 358757 811961 := bstep (se 2 (by rfl) ⟨304485, by rfl⟩ : syracuseStep 811961 = 608971) B608971
theorem B910379 : Blo 358757 910379 := bstep (se 1 (by rfl) ⟨682784, by rfl⟩ : syracuseStep 910379 = 1365569) B1365569
theorem B1467629 : Blo 358757 1467629 := bstep (se 3 (by rfl) ⟨275180, by rfl⟩ : syracuseStep 1467629 = 550361) B550361
theorem B812303 : Blo 358757 812303 := bstep (se 1 (by rfl) ⟨609227, by rfl⟩ : syracuseStep 812303 = 1218455) B1218455
theorem B1238287 : Blo 358757 1238287 := bstep (se 1 (by rfl) ⟨928715, by rfl⟩ : syracuseStep 1238287 = 1857431) B1857431
theorem B812321 : Blo 358757 812321 := bstep (se 2 (by rfl) ⟨304620, by rfl⟩ : syracuseStep 812321 = 609241) B609241
theorem B4384205 : Blo 358757 4384205 := bstep (se 3 (by rfl) ⟨822038, by rfl⟩ : syracuseStep 4384205 = 1644077) B1644077
theorem B976385 : Blo 358757 976385 := bstep (se 2 (by rfl) ⟨366144, by rfl⟩ : syracuseStep 976385 = 732289) B732289
theorem B2745899 : Blo 358757 2745899 := bstep (se 1 (by rfl) ⟨2059424, by rfl⟩ : syracuseStep 2745899 = 4118849) B4118849
theorem B812663 : Blo 358757 812663 := bstep (se 1 (by rfl) ⟨609497, by rfl⟩ : syracuseStep 812663 = 1218995) B1218995
theorem B648905 : Blo 358757 648905 := bstep (se 2 (by rfl) ⟨243339, by rfl⟩ : syracuseStep 648905 = 486679) B486679
theorem B812843 : Blo 358757 812843 := bstep (se 1 (by rfl) ⟨609632, by rfl⟩ : syracuseStep 812843 = 1219265) B1219265
theorem B1533755 : Blo 358757 1533755 := bstep (se 1 (by rfl) ⟨1150316, by rfl⟩ : syracuseStep 1533755 = 2300633) B2300633
theorem B4089689 : Blo 358757 4089689 := bstep (se 2 (by rfl) ⟨1533633, by rfl⟩ : syracuseStep 4089689 = 3067267) B3067267
theorem B1828817 : Blo 358757 1828817 := bstep (se 2 (by rfl) ⟨685806, by rfl⟩ : syracuseStep 1828817 = 1371613) B1371613
theorem B911371 : Blo 358757 911371 := bstep (se 1 (by rfl) ⟨683528, by rfl⟩ : syracuseStep 911371 = 1367057) B1367057
theorem B1370141 : Blo 358757 1370141 := bstep (se 3 (by rfl) ⟨256901, by rfl⟩ : syracuseStep 1370141 = 513803) B513803
theorem B1370155 : Blo 358757 1370155 := bstep (se 1 (by rfl) ⟨1027616, by rfl⟩ : syracuseStep 1370155 = 2055233) B2055233
theorem B813203 : Blo 358757 813203 := bstep (se 1 (by rfl) ⟨609902, by rfl⟩ : syracuseStep 813203 = 1219805) B1219805
theorem B911513 : Blo 358757 911513 := bstep (se 2 (by rfl) ⟨341817, by rfl⟩ : syracuseStep 911513 = 683635) B683635
theorem B813257 : Blo 358757 813257 := bstep (se 2 (by rfl) ⟨304971, by rfl⟩ : syracuseStep 813257 = 609943) B609943
theorem B1239241 : Blo 358757 1239241 := bstep (se 2 (by rfl) ⟨464715, by rfl⟩ : syracuseStep 1239241 = 929431) B929431
theorem B682283 : Blo 358757 682283 := bstep (se 1 (by rfl) ⟨511712, by rfl⟩ : syracuseStep 682283 = 1023425) B1023425
theorem B911675 : Blo 358757 911675 := bstep (se 1 (by rfl) ⟨683756, by rfl⟩ : syracuseStep 911675 = 1367513) B1367513
theorem B485767 : Blo 358757 485767 := bstep (se 1 (by rfl) ⟨364325, by rfl⟩ : syracuseStep 485767 = 728651) B728651
theorem B780815 : Blo 358757 780815 := bstep (se 1 (by rfl) ⟨585611, by rfl⟩ : syracuseStep 780815 = 1171223) B1171223
theorem B912019 : Blo 358757 912019 := bstep (se 1 (by rfl) ⟨684014, by rfl⟩ : syracuseStep 912019 = 1368029) B1368029
theorem B3893953 : Blo 358757 3893953 := bstep (se 2 (by rfl) ⟨1460232, by rfl⟩ : syracuseStep 3893953 = 2920465) B2920465
theorem B912161 : Blo 358757 912161 := bstep (se 2 (by rfl) ⟨342060, by rfl⟩ : syracuseStep 912161 = 684121) B684121
theorem B4156211 : Blo 358757 4156211 := bstep (se 1 (by rfl) ⟨3117158, by rfl⟩ : syracuseStep 4156211 = 6234317) B6234317
theorem B813959 : Blo 358757 813959 := bstep (se 1 (by rfl) ⟨610469, by rfl⟩ : syracuseStep 813959 = 1220939) B1220939
theorem B814139 : Blo 358757 814139 := bstep (se 1 (by rfl) ⟨610604, by rfl⟩ : syracuseStep 814139 = 1221209) B1221209
theorem B814265 : Blo 358757 814265 := bstep (se 2 (by rfl) ⟨305349, by rfl⟩ : syracuseStep 814265 = 610699) B610699
theorem B1469755 : Blo 358757 1469755 := bstep (se 1 (by rfl) ⟨1102316, by rfl⟩ : syracuseStep 1469755 = 2204633) B2204633
theorem B7761253 : Blo 358757 7761253 := bstep (se 4 (by rfl) ⟨727617, by rfl⟩ : syracuseStep 7761253 = 1455235) B1455235
theorem B7400963 : Blo 358757 7400963 := bstep (se 1 (by rfl) ⟨5550722, by rfl⟩ : syracuseStep 7400963 = 11101445) B11101445
theorem B814607 : Blo 358757 814607 := bstep (se 1 (by rfl) ⟨610955, by rfl⟩ : syracuseStep 814607 = 1221911) B1221911
theorem B978461 : Blo 358757 978461 := bstep (se 3 (by rfl) ⟨183461, by rfl⟩ : syracuseStep 978461 = 366923) B366923
theorem B814625 : Blo 358757 814625 := bstep (se 2 (by rfl) ⟨305484, by rfl⟩ : syracuseStep 814625 = 610969) B610969
theorem B454187 : Blo 358757 454187 := bstep (se 1 (by rfl) ⟨340640, by rfl⟩ : syracuseStep 454187 = 681281) B681281
theorem B3468977 : Blo 358757 3468977 := bstep (se 2 (by rfl) ⟨1300866, by rfl⟩ : syracuseStep 3468977 = 2601733) B2601733
theorem B913153 : Blo 358757 913153 := bstep (se 2 (by rfl) ⟨342432, by rfl⟩ : syracuseStep 913153 = 684865) B684865
theorem B814967 : Blo 358757 814967 := bstep (se 1 (by rfl) ⟨611225, by rfl⟩ : syracuseStep 814967 = 1222451) B1222451
theorem B683977 : Blo 358757 683977 := bstep (se 2 (by rfl) ⟨256491, by rfl⟩ : syracuseStep 683977 = 512983) B512983
theorem B454663 : Blo 358757 454663 := bstep (se 1 (by rfl) ⟨340997, by rfl⟩ : syracuseStep 454663 = 681995) B681995
theorem B1830923 : Blo 358757 1830923 := bstep (se 1 (by rfl) ⟨1373192, by rfl⟩ : syracuseStep 1830923 = 2746385) B2746385
theorem B45117461 : Blo 358757 45117461 := bstep (se 6 (by rfl) ⟨1057440, by rfl⟩ : syracuseStep 45117461 = 2114881) B2114881
theorem B815147 : Blo 358757 815147 := bstep (se 1 (by rfl) ⟨611360, by rfl⟩ : syracuseStep 815147 = 1222721) B1222721
theorem B1831085 : Blo 358757 1831085 := bstep (se 3 (by rfl) ⟨343328, by rfl⟩ : syracuseStep 1831085 = 686657) B686657
theorem B913751 : Blo 358757 913751 := bstep (se 1 (by rfl) ⟨685313, by rfl⟩ : syracuseStep 913751 = 1370627) B1370627
theorem B651667 : Blo 358757 651667 := bstep (se 1 (by rfl) ⟨488750, by rfl⟩ : syracuseStep 651667 = 977501) B977501
theorem B815507 : Blo 358757 815507 := bstep (se 1 (by rfl) ⟨611630, by rfl⟩ : syracuseStep 815507 = 1223261) B1223261
theorem B815561 : Blo 358757 815561 := bstep (se 2 (by rfl) ⟨305835, by rfl⟩ : syracuseStep 815561 = 611671) B611671
theorem B2060747 : Blo 358757 2060747 := bstep (se 1 (by rfl) ⟨1545560, by rfl⟩ : syracuseStep 2060747 = 3091121) B3091121
theorem B455159 : Blo 358757 455159 := bstep (se 1 (by rfl) ⟨341369, by rfl⟩ : syracuseStep 455159 = 682739) B682739
theorem B3502595 : Blo 358757 3502595 := bstep (se 1 (by rfl) ⟨2626946, by rfl⟩ : syracuseStep 3502595 = 5253893) B5253893
theorem B913963 : Blo 358757 913963 := bstep (se 1 (by rfl) ⟨685472, by rfl⟩ : syracuseStep 913963 = 1370945) B1370945
theorem B979499 : Blo 358757 979499 := bstep (se 1 (by rfl) ⟨734624, by rfl⟩ : syracuseStep 979499 = 1469249) B1469249
theorem B455311 : Blo 358757 455311 := bstep (se 1 (by rfl) ⟨341483, by rfl⟩ : syracuseStep 455311 = 682967) B682967
theorem B979609 : Blo 358757 979609 := bstep (se 2 (by rfl) ⟨367353, by rfl⟩ : syracuseStep 979609 = 734707) B734707
theorem B914105 : Blo 358757 914105 := bstep (se 2 (by rfl) ⟨342789, by rfl⟩ : syracuseStep 914105 = 685579) B685579
theorem B783049 : Blo 358757 783049 := bstep (se 2 (by rfl) ⟨293643, by rfl⟩ : syracuseStep 783049 = 587287) B587287
theorem B651977 : Blo 358757 651977 := bstep (se 2 (by rfl) ⟨244491, by rfl⟩ : syracuseStep 651977 = 488983) B488983
theorem B455483 : Blo 358757 455483 := bstep (se 1 (by rfl) ⟨341612, by rfl⟩ : syracuseStep 455483 = 683225) B683225
theorem B3470359 : Blo 358757 3470359 := bstep (se 1 (by rfl) ⟨2602769, by rfl⟩ : syracuseStep 3470359 = 5205539) B5205539
theorem B3339667 : Blo 358757 3339667 := bstep (se 1 (by rfl) ⟨2504750, by rfl⟩ : syracuseStep 3339667 = 5009501) B5009501
theorem B20903345 : Blo 358757 20903345 := bstep (se 2 (by rfl) ⟨7838754, by rfl⟩ : syracuseStep 20903345 = 15677509) B15677509
theorem B915097 : Blo 358757 915097 := bstep (se 2 (by rfl) ⟨343161, by rfl⟩ : syracuseStep 915097 = 686323) B686323
theorem B1832705 : Blo 358757 1832705 := bstep (se 2 (by rfl) ⟨687264, by rfl⟩ : syracuseStep 1832705 = 1374529) B1374529
theorem B456455 : Blo 358757 456455 := bstep (se 1 (by rfl) ⟨342341, by rfl⟩ : syracuseStep 456455 = 684683) B684683
theorem B685883 : Blo 358757 685883 := bstep (se 1 (by rfl) ⟨514412, by rfl⟩ : syracuseStep 685883 = 1028825) B1028825
theorem B915259 : Blo 358757 915259 := bstep (se 1 (by rfl) ⟨686444, by rfl⟩ : syracuseStep 915259 = 1372889) B1372889
theorem B915401 : Blo 358757 915401 := bstep (se 2 (by rfl) ⟨343275, by rfl⟩ : syracuseStep 915401 = 686551) B686551
theorem B686369 : Blo 358757 686369 := bstep (se 2 (by rfl) ⟨257388, by rfl⟩ : syracuseStep 686369 = 514777) B514777
theorem B915745 : Blo 358757 915745 := bstep (se 2 (by rfl) ⟨343404, by rfl⟩ : syracuseStep 915745 = 686809) B686809
theorem B358791 : Blo 358757 358791 := bstep (se 1 (by rfl) ⟨269093, by rfl⟩ : syracuseStep 358791 = 538187) B538187
theorem B358799 : Blo 358757 358799 := bstep (se 1 (by rfl) ⟨269099, by rfl⟩ : syracuseStep 358799 = 538199) B538199
theorem B457103 : Blo 358757 457103 := bstep (se 1 (by rfl) ⟨342827, by rfl⟩ : syracuseStep 457103 = 685655) B685655
theorem B358843 : Blo 358757 358843 := bstep (se 1 (by rfl) ⟨269132, by rfl⟩ : syracuseStep 358843 = 538265) B538265
theorem B358919 : Blo 358757 358919 := bstep (se 1 (by rfl) ⟨269189, by rfl⟩ : syracuseStep 358919 = 538379) B538379
theorem B358927 : Blo 358757 358927 := bstep (se 1 (by rfl) ⟨269195, by rfl⟩ : syracuseStep 358927 = 538391) B538391
theorem B2259479 : Blo 358757 2259479 := bstep (se 1 (by rfl) ⟨1694609, by rfl⟩ : syracuseStep 2259479 = 3389219) B3389219
theorem B1833515 : Blo 358757 1833515 := bstep (se 1 (by rfl) ⟨1375136, by rfl⟩ : syracuseStep 1833515 = 2750273) B2750273
theorem B358971 : Blo 358757 358971 := bstep (se 1 (by rfl) ⟨269228, by rfl⟩ : syracuseStep 358971 = 538457) B538457
theorem B686711 : Blo 358757 686711 := bstep (se 1 (by rfl) ⟨515033, by rfl⟩ : syracuseStep 686711 = 1030067) B1030067
theorem B359047 : Blo 358757 359047 := bstep (se 1 (by rfl) ⟨269285, by rfl⟩ : syracuseStep 359047 = 538571) B538571
theorem B359055 : Blo 358757 359055 := bstep (se 1 (by rfl) ⟨269291, by rfl⟩ : syracuseStep 359055 = 538583) B538583
theorem B359099 : Blo 358757 359099 := bstep (se 1 (by rfl) ⟨269324, by rfl⟩ : syracuseStep 359099 = 538649) B538649
theorem B359175 : Blo 358757 359175 := bstep (se 1 (by rfl) ⟨269381, by rfl⟩ : syracuseStep 359175 = 538763) B538763
theorem B359183 : Blo 358757 359183 := bstep (se 1 (by rfl) ⟨269387, by rfl⟩ : syracuseStep 359183 = 538775) B538775
theorem B359227 : Blo 358757 359227 := bstep (se 1 (by rfl) ⟨269420, by rfl⟩ : syracuseStep 359227 = 538841) B538841
theorem B916343 : Blo 358757 916343 := bstep (se 1 (by rfl) ⟨687257, by rfl⟩ : syracuseStep 916343 = 1374515) B1374515
theorem B359303 : Blo 358757 359303 := bstep (se 1 (by rfl) ⟨269477, by rfl⟩ : syracuseStep 359303 = 538955) B538955
theorem B359311 : Blo 358757 359311 := bstep (se 1 (by rfl) ⟨269483, by rfl⟩ : syracuseStep 359311 = 538967) B538967
theorem B359355 : Blo 358757 359355 := bstep (se 1 (by rfl) ⟨269516, by rfl⟩ : syracuseStep 359355 = 539033) B539033
theorem B359431 : Blo 358757 359431 := bstep (se 1 (by rfl) ⟨269573, by rfl⟩ : syracuseStep 359431 = 539147) B539147
theorem B359439 : Blo 358757 359439 := bstep (se 1 (by rfl) ⟨269579, by rfl⟩ : syracuseStep 359439 = 539159) B539159
theorem B1539101 : Blo 358757 1539101 := bstep (se 3 (by rfl) ⟨288581, by rfl⟩ : syracuseStep 1539101 = 577163) B577163
theorem B1211435 : Blo 358757 1211435 := bstep (se 1 (by rfl) ⟨908576, by rfl⟩ : syracuseStep 1211435 = 1817153) B1817153
theorem B359483 : Blo 358757 359483 := bstep (se 1 (by rfl) ⟨269612, by rfl⟩ : syracuseStep 359483 = 539225) B539225
theorem B1375319 : Blo 358757 1375319 := bstep (se 1 (by rfl) ⟨1031489, by rfl⟩ : syracuseStep 1375319 = 2062979) B2062979
theorem B359559 : Blo 358757 359559 := bstep (se 1 (by rfl) ⟨269669, by rfl⟩ : syracuseStep 359559 = 539339) B539339
theorem B359567 : Blo 358757 359567 := bstep (se 1 (by rfl) ⟨269675, by rfl⟩ : syracuseStep 359567 = 539351) B539351
theorem B359611 : Blo 358757 359611 := bstep (se 1 (by rfl) ⟨269708, by rfl⟩ : syracuseStep 359611 = 539417) B539417
theorem B359687 : Blo 358757 359687 := bstep (se 1 (by rfl) ⟨269765, by rfl⟩ : syracuseStep 359687 = 539531) B539531
theorem B359695 : Blo 358757 359695 := bstep (se 1 (by rfl) ⟨269771, by rfl⟩ : syracuseStep 359695 = 539543) B539543
theorem B359739 : Blo 358757 359739 := bstep (se 1 (by rfl) ⟨269804, by rfl⟩ : syracuseStep 359739 = 539609) B539609
theorem B359815 : Blo 358757 359815 := bstep (se 1 (by rfl) ⟨269861, by rfl⟩ : syracuseStep 359815 = 539723) B539723
theorem B359823 : Blo 358757 359823 := bstep (se 1 (by rfl) ⟨269867, by rfl⟩ : syracuseStep 359823 = 539735) B539735
theorem B359867 : Blo 358757 359867 := bstep (se 1 (by rfl) ⟨269900, by rfl⟩ : syracuseStep 359867 = 539801) B539801
theorem B359943 : Blo 358757 359943 := bstep (se 1 (by rfl) ⟨269957, by rfl⟩ : syracuseStep 359943 = 539915) B539915
theorem B359951 : Blo 358757 359951 := bstep (se 1 (by rfl) ⟨269963, by rfl⟩ : syracuseStep 359951 = 539927) B539927
theorem B359995 : Blo 358757 359995 := bstep (se 1 (by rfl) ⟨269996, by rfl⟩ : syracuseStep 359995 = 539993) B539993
theorem B1375805 : Blo 358757 1375805 := bstep (se 3 (by rfl) ⟨257963, by rfl⟩ : syracuseStep 1375805 = 515927) B515927
theorem B360071 : Blo 358757 360071 := bstep (se 1 (by rfl) ⟨270053, by rfl⟩ : syracuseStep 360071 = 540107) B540107
theorem B360079 : Blo 358757 360079 := bstep (se 1 (by rfl) ⟨270059, by rfl⟩ : syracuseStep 360079 = 540119) B540119
theorem B360123 : Blo 358757 360123 := bstep (se 1 (by rfl) ⟨270092, by rfl⟩ : syracuseStep 360123 = 540185) B540185
theorem B1539785 : Blo 358757 1539785 := bstep (se 2 (by rfl) ⟨577419, by rfl⟩ : syracuseStep 1539785 = 1154839) B1154839
theorem B360199 : Blo 358757 360199 := bstep (se 1 (by rfl) ⟨270149, by rfl⟩ : syracuseStep 360199 = 540299) B540299
theorem B360207 : Blo 358757 360207 := bstep (se 1 (by rfl) ⟨270155, by rfl⟩ : syracuseStep 360207 = 540311) B540311
theorem B360251 : Blo 358757 360251 := bstep (se 1 (by rfl) ⟨270188, by rfl⟩ : syracuseStep 360251 = 540377) B540377
theorem B1834811 : Blo 358757 1834811 := bstep (se 1 (by rfl) ⟨1376108, by rfl⟩ : syracuseStep 1834811 = 2752217) B2752217
theorem B360327 : Blo 358757 360327 := bstep (se 1 (by rfl) ⟨270245, by rfl⟩ : syracuseStep 360327 = 540491) B540491
theorem B360335 : Blo 358757 360335 := bstep (se 1 (by rfl) ⟨270251, by rfl⟩ : syracuseStep 360335 = 540503) B540503
theorem B360379 : Blo 358757 360379 := bstep (se 1 (by rfl) ⟨270284, by rfl⟩ : syracuseStep 360379 = 540569) B540569
theorem B1834973 : Blo 358757 1834973 := bstep (se 3 (by rfl) ⟨344057, by rfl⟩ : syracuseStep 1834973 = 688115) B688115
theorem B5898269 : Blo 358757 5898269 := bstep (se 3 (by rfl) ⟨1105925, by rfl⟩ : syracuseStep 5898269 = 2211851) B2211851
theorem B360487 : Blo 358757 360487 := bstep (se 1 (by rfl) ⟨270365, by rfl⟩ : syracuseStep 360487 = 540731) B540731
theorem B360527 : Blo 358757 360527 := bstep (se 1 (by rfl) ⟨270395, by rfl⟩ : syracuseStep 360527 = 540791) B540791
theorem B360543 : Blo 358757 360543 := bstep (se 1 (by rfl) ⟨270407, by rfl⟩ : syracuseStep 360543 = 540815) B540815
theorem B360571 : Blo 358757 360571 := bstep (se 1 (by rfl) ⟨270428, by rfl⟩ : syracuseStep 360571 = 540857) B540857
theorem B458875 : Blo 358757 458875 := bstep (se 1 (by rfl) ⟨344156, by rfl⟩ : syracuseStep 458875 = 688313) B688313
theorem B1212569 : Blo 358757 1212569 := bstep (se 2 (by rfl) ⟨454713, by rfl⟩ : syracuseStep 1212569 = 909427) B909427
theorem B360623 : Blo 358757 360623 := bstep (se 1 (by rfl) ⟨270467, by rfl⟩ : syracuseStep 360623 = 540935) B540935
theorem B360647 : Blo 358757 360647 := bstep (se 1 (by rfl) ⟨270485, by rfl⟩ : syracuseStep 360647 = 540971) B540971
theorem B360667 : Blo 358757 360667 := bstep (se 1 (by rfl) ⟨270500, by rfl⟩ : syracuseStep 360667 = 541001) B541001
theorem B360743 : Blo 358757 360743 := bstep (se 1 (by rfl) ⟨270557, by rfl⟩ : syracuseStep 360743 = 541115) B541115
theorem B360783 : Blo 358757 360783 := bstep (se 1 (by rfl) ⟨270587, by rfl⟩ : syracuseStep 360783 = 541175) B541175
theorem B360799 : Blo 358757 360799 := bstep (se 1 (by rfl) ⟨270599, by rfl⟩ : syracuseStep 360799 = 541199) B541199
theorem B459103 : Blo 358757 459103 := bstep (se 1 (by rfl) ⟨344327, by rfl⟩ : syracuseStep 459103 = 688655) B688655
theorem B360827 : Blo 358757 360827 := bstep (se 1 (by rfl) ⟨270620, by rfl⟩ : syracuseStep 360827 = 541241) B541241
theorem B1638785 : Blo 358757 1638785 := bstep (se 2 (by rfl) ⟨614544, by rfl⟩ : syracuseStep 1638785 = 1229089) B1229089
theorem B360879 : Blo 358757 360879 := bstep (se 1 (by rfl) ⟨270659, by rfl⟩ : syracuseStep 360879 = 541319) B541319
theorem B688571 : Blo 358757 688571 := bstep (se 1 (by rfl) ⟨516428, by rfl⟩ : syracuseStep 688571 = 1032857) B1032857
theorem B360903 : Blo 358757 360903 := bstep (se 1 (by rfl) ⟨270677, by rfl⟩ : syracuseStep 360903 = 541355) B541355
theorem B360923 : Blo 358757 360923 := bstep (se 1 (by rfl) ⟨270692, by rfl⟩ : syracuseStep 360923 = 541385) B541385
theorem B1638893 : Blo 358757 1638893 := bstep (se 3 (by rfl) ⟨307292, by rfl⟩ : syracuseStep 1638893 = 614585) B614585
theorem B1376777 : Blo 358757 1376777 := bstep (se 2 (by rfl) ⟨516291, by rfl⟩ : syracuseStep 1376777 = 1032583) B1032583
theorem B360999 : Blo 358757 360999 := bstep (se 1 (by rfl) ⟨270749, by rfl⟩ : syracuseStep 360999 = 541499) B541499
theorem B361039 : Blo 358757 361039 := bstep (se 1 (by rfl) ⟨270779, by rfl⟩ : syracuseStep 361039 = 541559) B541559
theorem B361055 : Blo 358757 361055 := bstep (se 1 (by rfl) ⟨270791, by rfl⟩ : syracuseStep 361055 = 541583) B541583
theorem B361083 : Blo 358757 361083 := bstep (se 1 (by rfl) ⟨270812, by rfl⟩ : syracuseStep 361083 = 541625) B541625
theorem B918155 : Blo 358757 918155 := bstep (se 1 (by rfl) ⟨688616, by rfl⟩ : syracuseStep 918155 = 1377233) B1377233
theorem B361135 : Blo 358757 361135 := bstep (se 1 (by rfl) ⟨270851, by rfl⟩ : syracuseStep 361135 = 541703) B541703
theorem B361159 : Blo 358757 361159 := bstep (se 1 (by rfl) ⟨270869, by rfl⟩ : syracuseStep 361159 = 541739) B541739
theorem B361179 : Blo 358757 361179 := bstep (se 1 (by rfl) ⟨270884, by rfl⟩ : syracuseStep 361179 = 541769) B541769
theorem B361255 : Blo 358757 361255 := bstep (se 1 (by rfl) ⟨270941, by rfl⟩ : syracuseStep 361255 = 541883) B541883
theorem B7537481 : Blo 358757 7537481 := bstep (se 2 (by rfl) ⟨2826555, by rfl⟩ : syracuseStep 7537481 = 5653111) B5653111
theorem B361295 : Blo 358757 361295 := bstep (se 1 (by rfl) ⟨270971, by rfl⟩ : syracuseStep 361295 = 541943) B541943
theorem B361311 : Blo 358757 361311 := bstep (se 1 (by rfl) ⟨270983, by rfl⟩ : syracuseStep 361311 = 541967) B541967
theorem B361339 : Blo 358757 361339 := bstep (se 1 (by rfl) ⟨271004, by rfl⟩ : syracuseStep 361339 = 542009) B542009
theorem B361391 : Blo 358757 361391 := bstep (se 1 (by rfl) ⟨271043, by rfl⟩ : syracuseStep 361391 = 542087) B542087
theorem B361415 : Blo 358757 361415 := bstep (se 1 (by rfl) ⟨271061, by rfl⟩ : syracuseStep 361415 = 542123) B542123
theorem B8258507 : Blo 358757 8258507 := bstep (se 1 (by rfl) ⟨6193880, by rfl⟩ : syracuseStep 8258507 = 12387761) B12387761
theorem B361435 : Blo 358757 361435 := bstep (se 1 (by rfl) ⟨271076, by rfl⟩ : syracuseStep 361435 = 542153) B542153
theorem B361511 : Blo 358757 361511 := bstep (se 1 (by rfl) ⟨271133, by rfl⟩ : syracuseStep 361511 = 542267) B542267
theorem B361551 : Blo 358757 361551 := bstep (se 1 (by rfl) ⟨271163, by rfl⟩ : syracuseStep 361551 = 542327) B542327
theorem B361567 : Blo 358757 361567 := bstep (se 1 (by rfl) ⟨271175, by rfl⟩ : syracuseStep 361567 = 542351) B542351
theorem B361595 : Blo 358757 361595 := bstep (se 1 (by rfl) ⟨271196, by rfl⟩ : syracuseStep 361595 = 542393) B542393
theorem B361647 : Blo 358757 361647 := bstep (se 1 (by rfl) ⟨271235, by rfl⟩ : syracuseStep 361647 = 542471) B542471
theorem B361671 : Blo 358757 361671 := bstep (se 1 (by rfl) ⟨271253, by rfl⟩ : syracuseStep 361671 = 542507) B542507
theorem B361691 : Blo 358757 361691 := bstep (se 1 (by rfl) ⟨271268, by rfl⟩ : syracuseStep 361691 = 542537) B542537
theorem B361767 : Blo 358757 361767 := bstep (se 1 (by rfl) ⟨271325, by rfl⟩ : syracuseStep 361767 = 542651) B542651
theorem B1213757 : Blo 358757 1213757 := bstep (se 3 (by rfl) ⟨227579, by rfl⟩ : syracuseStep 1213757 = 455159) B455159
theorem B361807 : Blo 358757 361807 := bstep (se 1 (by rfl) ⟨271355, by rfl⟩ : syracuseStep 361807 = 542711) B542711
theorem B5211485 : Blo 358757 5211485 := bstep (se 3 (by rfl) ⟨977153, by rfl⟩ : syracuseStep 5211485 = 1954307) B1954307
theorem B361823 : Blo 358757 361823 := bstep (se 1 (by rfl) ⟨271367, by rfl⟩ : syracuseStep 361823 = 542735) B542735
theorem B1017193 : Blo 358757 1017193 := bstep (se 2 (by rfl) ⟨381447, by rfl⟩ : syracuseStep 1017193 = 762895) B762895
theorem B361851 : Blo 358757 361851 := bstep (se 1 (by rfl) ⟨271388, by rfl⟩ : syracuseStep 361851 = 542777) B542777
theorem B1836431 : Blo 358757 1836431 := bstep (se 1 (by rfl) ⟨1377323, by rfl⟩ : syracuseStep 1836431 = 2754647) B2754647
theorem B5211539 : Blo 358757 5211539 := bstep (se 1 (by rfl) ⟨3908654, by rfl⟩ : syracuseStep 5211539 = 7817309) B7817309
theorem B361903 : Blo 358757 361903 := bstep (se 1 (by rfl) ⟨271427, by rfl⟩ : syracuseStep 361903 = 542855) B542855
theorem B361927 : Blo 358757 361927 := bstep (se 1 (by rfl) ⟨271445, by rfl⟩ : syracuseStep 361927 = 542891) B542891
theorem B361947 : Blo 358757 361947 := bstep (se 1 (by rfl) ⟨271460, by rfl⟩ : syracuseStep 361947 = 542921) B542921
theorem B362023 : Blo 358757 362023 := bstep (se 1 (by rfl) ⟨271517, by rfl⟩ : syracuseStep 362023 = 543035) B543035
theorem B362063 : Blo 358757 362063 := bstep (se 1 (by rfl) ⟨271547, by rfl⟩ : syracuseStep 362063 = 543095) B543095
theorem B362079 : Blo 358757 362079 := bstep (se 1 (by rfl) ⟨271559, by rfl⟩ : syracuseStep 362079 = 543119) B543119
theorem B362107 : Blo 358757 362107 := bstep (se 1 (by rfl) ⟨271580, by rfl⟩ : syracuseStep 362107 = 543161) B543161
theorem B362159 : Blo 358757 362159 := bstep (se 1 (by rfl) ⟨271619, by rfl⟩ : syracuseStep 362159 = 543239) B543239
theorem B362183 : Blo 358757 362183 := bstep (se 1 (by rfl) ⟨271637, by rfl⟩ : syracuseStep 362183 = 543275) B543275
theorem B362203 : Blo 358757 362203 := bstep (se 1 (by rfl) ⟨271652, by rfl⟩ : syracuseStep 362203 = 543305) B543305
theorem B362279 : Blo 358757 362279 := bstep (se 1 (by rfl) ⟨271709, by rfl⟩ : syracuseStep 362279 = 543419) B543419
theorem B362319 : Blo 358757 362319 := bstep (se 1 (by rfl) ⟨271739, by rfl⟩ : syracuseStep 362319 = 543479) B543479
theorem B362335 : Blo 358757 362335 := bstep (se 1 (by rfl) ⟨271751, by rfl⟩ : syracuseStep 362335 = 543503) B543503
theorem B362363 : Blo 358757 362363 := bstep (se 1 (by rfl) ⟨271772, by rfl⟩ : syracuseStep 362363 = 543545) B543545
theorem B1640353 : Blo 358757 1640353 := bstep (se 2 (by rfl) ⟨615132, by rfl⟩ : syracuseStep 1640353 = 1230265) B1230265
theorem B362415 : Blo 358757 362415 := bstep (se 1 (by rfl) ⟨271811, by rfl⟩ : syracuseStep 362415 = 543623) B543623
theorem B362439 : Blo 358757 362439 := bstep (se 1 (by rfl) ⟨271829, by rfl⟩ : syracuseStep 362439 = 543659) B543659
theorem B362459 : Blo 358757 362459 := bstep (se 1 (by rfl) ⟨271844, by rfl⟩ : syracuseStep 362459 = 543689) B543689
theorem B362535 : Blo 358757 362535 := bstep (se 1 (by rfl) ⟨271901, by rfl⟩ : syracuseStep 362535 = 543803) B543803
theorem B362575 : Blo 358757 362575 := bstep (se 1 (by rfl) ⟨271931, by rfl⟩ : syracuseStep 362575 = 543863) B543863
theorem B362591 : Blo 358757 362591 := bstep (se 1 (by rfl) ⟨271943, by rfl⟩ : syracuseStep 362591 = 543887) B543887
theorem B362619 : Blo 358757 362619 := bstep (se 1 (by rfl) ⟨271964, by rfl⟩ : syracuseStep 362619 = 543929) B543929
theorem B1214621 : Blo 358757 1214621 := bstep (se 3 (by rfl) ⟨227741, by rfl⟩ : syracuseStep 1214621 = 455483) B455483
theorem B362671 : Blo 358757 362671 := bstep (se 1 (by rfl) ⟨272003, by rfl⟩ : syracuseStep 362671 = 544007) B544007
theorem B362695 : Blo 358757 362695 := bstep (se 1 (by rfl) ⟨272021, by rfl⟩ : syracuseStep 362695 = 544043) B544043
theorem B362715 : Blo 358757 362715 := bstep (se 1 (by rfl) ⟨272036, by rfl⟩ : syracuseStep 362715 = 544073) B544073
theorem B4098437 : Blo 358757 4098437 := bstep (se 4 (by rfl) ⟨384228, by rfl⟩ : syracuseStep 4098437 = 768457) B768457
theorem B1215161 : Blo 358757 1215161 := bstep (se 2 (by rfl) ⟨455685, by rfl⟩ : syracuseStep 1215161 = 911371) B911371
theorem B11995877 : Blo 358757 11995877 := bstep (se 4 (by rfl) ⟨1124613, by rfl⟩ : syracuseStep 11995877 = 2249227) B2249227
theorem B691039 : Blo 358757 691039 := bstep (se 1 (by rfl) ⟨518279, by rfl⟩ : syracuseStep 691039 = 1036559) B1036559
theorem B691163 : Blo 358757 691163 := bstep (se 1 (by rfl) ⟨518372, by rfl⟩ : syracuseStep 691163 = 1036745) B1036745
theorem B1215755 : Blo 358757 1215755 := bstep (se 1 (by rfl) ⟨911816, by rfl⟩ : syracuseStep 1215755 = 1823633) B1823633
theorem B1216025 : Blo 358757 1216025 := bstep (se 2 (by rfl) ⟨456009, by rfl⟩ : syracuseStep 1216025 = 912019) B912019
theorem B1740487 : Blo 358757 1740487 := bstep (se 1 (by rfl) ⟨1305365, by rfl⟩ : syracuseStep 1740487 = 2610731) B2610731
theorem B1217159 : Blo 358757 1217159 := bstep (se 1 (by rfl) ⟨912869, by rfl⟩ : syracuseStep 1217159 = 1825739) B1825739
theorem B1217213 : Blo 358757 1217213 := bstep (se 3 (by rfl) ⟨228227, by rfl⟩ : syracuseStep 1217213 = 456455) B456455
theorem B660215 : Blo 358757 660215 := bstep (se 1 (by rfl) ⟨495161, by rfl⟩ : syracuseStep 660215 = 990323) B990323
theorem B4690705 : Blo 358757 4690705 := bstep (se 2 (by rfl) ⟨1759014, by rfl⟩ : syracuseStep 4690705 = 3518029) B3518029
theorem B3740489 : Blo 358757 3740489 := bstep (se 2 (by rfl) ⟨1402683, by rfl⟩ : syracuseStep 3740489 = 2805367) B2805367
theorem B1217375 : Blo 358757 1217375 := bstep (se 1 (by rfl) ⟨913031, by rfl⟩ : syracuseStep 1217375 = 1826063) B1826063
theorem B463711 : Blo 358757 463711 := bstep (se 1 (by rfl) ⟨347783, by rfl⟩ : syracuseStep 463711 = 695567) B695567
theorem B1217537 : Blo 358757 1217537 := bstep (se 2 (by rfl) ⟨456576, by rfl⟩ : syracuseStep 1217537 = 913153) B913153
theorem B2954393 : Blo 358757 2954393 := bstep (se 2 (by rfl) ⟨1107897, by rfl⟩ : syracuseStep 2954393 = 2215795) B2215795
theorem B1218347 : Blo 358757 1218347 := bstep (se 1 (by rfl) ⟨913760, by rfl⟩ : syracuseStep 1218347 = 1827521) B1827521
theorem B1218617 : Blo 358757 1218617 := bstep (se 2 (by rfl) ⟨456981, by rfl⟩ : syracuseStep 1218617 = 913963) B913963
theorem B2922803 : Blo 358757 2922803 := bstep (se 1 (by rfl) ⟨2192102, by rfl⟩ : syracuseStep 2922803 = 4384205) B4384205
theorem B1218941 : Blo 358757 1218941 := bstep (se 3 (by rfl) ⟨228551, by rfl⟩ : syracuseStep 1218941 = 457103) B457103
theorem B1022503 : Blo 358757 1022503 := bstep (se 1 (by rfl) ⟨766877, by rfl⟩ : syracuseStep 1022503 = 1533755) B1533755
theorem B2726459 : Blo 358757 2726459 := bstep (se 1 (by rfl) ⟨2044844, by rfl⟩ : syracuseStep 2726459 = 4089689) B4089689
theorem B1219211 : Blo 358757 1219211 := bstep (se 1 (by rfl) ⟨914408, by rfl⟩ : syracuseStep 1219211 = 1828817) B1828817
theorem B4627145 : Blo 358757 4627145 := bstep (se 2 (by rfl) ⟨1735179, by rfl⟩ : syracuseStep 4627145 = 3470359) B3470359
theorem B1153865 : Blo 358757 1153865 := bstep (se 2 (by rfl) ⟨432699, by rfl⟩ : syracuseStep 1153865 = 865399) B865399
theorem B1154429 : Blo 358757 1154429 := bstep (se 3 (by rfl) ⟨216455, by rfl⟩ : syracuseStep 1154429 = 432911) B432911
theorem B1220129 : Blo 358757 1220129 := bstep (se 2 (by rfl) ⟨457548, by rfl⟩ : syracuseStep 1220129 = 915097) B915097
theorem B5185241 : Blo 358757 5185241 := bstep (se 2 (by rfl) ⟨1944465, by rfl⟩ : syracuseStep 5185241 = 3888931) B3888931
theorem B1220345 : Blo 358757 1220345 := bstep (se 2 (by rfl) ⟨457629, by rfl⟩ : syracuseStep 1220345 = 915259) B915259
theorem B1384235 : Blo 358757 1384235 := bstep (se 1 (by rfl) ⟨1038176, by rfl⟩ : syracuseStep 1384235 = 2076353) B2076353
theorem B1220615 : Blo 358757 1220615 := bstep (se 1 (by rfl) ⟨915461, by rfl⟩ : syracuseStep 1220615 = 1830923) B1830923
theorem B4104269 : Blo 358757 4104269 := bstep (se 3 (by rfl) ⟨769550, by rfl⟩ : syracuseStep 4104269 = 1539101) B1539101
theorem B1220723 : Blo 358757 1220723 := bstep (se 1 (by rfl) ⟨915542, by rfl⟩ : syracuseStep 1220723 = 1831085) B1831085
theorem B2335063 : Blo 358757 2335063 := bstep (se 1 (by rfl) ⟨1751297, by rfl⟩ : syracuseStep 2335063 = 3502595) B3502595
theorem B1220993 : Blo 358757 1220993 := bstep (se 2 (by rfl) ⟨457872, by rfl⟩ : syracuseStep 1220993 = 915745) B915745
theorem B434651 : Blo 358757 434651 := bstep (se 1 (by rfl) ⟨325988, by rfl⟩ : syracuseStep 434651 = 651977) B651977
theorem B13935563 : Blo 358757 13935563 := bstep (se 1 (by rfl) ⟨10451672, by rfl⟩ : syracuseStep 13935563 = 20903345) B20903345
theorem B1221803 : Blo 358757 1221803 := bstep (se 1 (by rfl) ⟨916352, by rfl⟩ : syracuseStep 1221803 = 1832705) B1832705
theorem B6661577 : Blo 358757 6661577 := bstep (se 2 (by rfl) ⟨2498091, by rfl⟩ : syracuseStep 6661577 = 4996183) B4996183
theorem B1222343 : Blo 358757 1222343 := bstep (se 1 (by rfl) ⟨916757, by rfl⟩ : syracuseStep 1222343 = 1833515) B1833515
theorem B5220301 : Blo 358757 5220301 := bstep (se 3 (by rfl) ⟨978806, by rfl⟩ : syracuseStep 5220301 = 1957613) B1957613
theorem B403807 : Blo 358757 403807 := bstep (se 1 (by rfl) ⟨302855, by rfl⟩ : syracuseStep 403807 = 605711) B605711
theorem B1026523 : Blo 358757 1026523 := bstep (se 1 (by rfl) ⟨769892, by rfl⟩ : syracuseStep 1026523 = 1539785) B1539785
theorem B1026569 : Blo 358757 1026569 := bstep (se 2 (by rfl) ⟨384963, by rfl⟩ : syracuseStep 1026569 = 769927) B769927
theorem B1223207 : Blo 358757 1223207 := bstep (se 1 (by rfl) ⟨917405, by rfl⟩ : syracuseStep 1223207 = 1834811) B1834811
theorem B1223315 : Blo 358757 1223315 := bstep (se 1 (by rfl) ⟨917486, by rfl⟩ : syracuseStep 1223315 = 1834973) B1834973
theorem B404167 : Blo 358757 404167 := bstep (se 1 (by rfl) ⟨303125, by rfl⟩ : syracuseStep 404167 = 606251) B606251
theorem B862969 : Blo 358757 862969 := bstep (se 2 (by rfl) ⟨323613, by rfl⟩ : syracuseStep 862969 = 647227) B647227
theorem B1026911 : Blo 358757 1026911 := bstep (se 1 (by rfl) ⟨770183, by rfl⟩ : syracuseStep 1026911 = 1540367) B1540367
theorem B1223531 : Blo 358757 1223531 := bstep (se 1 (by rfl) ⟨917648, by rfl⟩ : syracuseStep 1223531 = 1835297) B1835297
theorem B1223585 : Blo 358757 1223585 := bstep (se 2 (by rfl) ⟨458844, by rfl⟩ : syracuseStep 1223585 = 917689) B917689
theorem B1027151 : Blo 358757 1027151 := bstep (se 1 (by rfl) ⟨770363, by rfl⟩ : syracuseStep 1027151 = 1540727) B1540727
theorem B732257 : Blo 358757 732257 := bstep (se 2 (by rfl) ⟨274596, by rfl⟩ : syracuseStep 732257 = 549193) B549193
theorem B2305219 : Blo 358757 2305219 := bstep (se 1 (by rfl) ⟨1728914, by rfl⟩ : syracuseStep 2305219 = 3457829) B3457829
theorem B929015 : Blo 358757 929015 := bstep (se 1 (by rfl) ⟨696761, by rfl⟩ : syracuseStep 929015 = 1393523) B1393523
theorem B2600207 : Blo 358757 2600207 := bstep (se 1 (by rfl) ⟨1950155, by rfl⟩ : syracuseStep 2600207 = 3900311) B3900311
theorem B437611 : Blo 358757 437611 := bstep (se 1 (by rfl) ⟨328208, by rfl⟩ : syracuseStep 437611 = 656417) B656417
theorem B1224179 : Blo 358757 1224179 := bstep (se 1 (by rfl) ⟨918134, by rfl⟩ : syracuseStep 1224179 = 1836269) B1836269
theorem B405031 : Blo 358757 405031 := bstep (se 1 (by rfl) ⟨303773, by rfl⟩ : syracuseStep 405031 = 607547) B607547
theorem B6565495 : Blo 358757 6565495 := bstep (se 1 (by rfl) ⟨4924121, by rfl⟩ : syracuseStep 6565495 = 9848243) B9848243
theorem B1027799 : Blo 358757 1027799 := bstep (se 1 (by rfl) ⟨770849, by rfl⟩ : syracuseStep 1027799 = 1541699) B1541699
theorem B1028027 : Blo 358757 1028027 := bstep (se 1 (by rfl) ⟨771020, by rfl⟩ : syracuseStep 1028027 = 1542041) B1542041
theorem B5451781 : Blo 358757 5451781 := bstep (se 4 (by rfl) ⟨511104, by rfl⟩ : syracuseStep 5451781 = 1022209) B1022209
theorem B864275 : Blo 358757 864275 := bstep (se 1 (by rfl) ⟨648206, by rfl⟩ : syracuseStep 864275 = 1296413) B1296413
theorem B1028153 : Blo 358757 1028153 := bstep (se 2 (by rfl) ⟨385557, by rfl⟩ : syracuseStep 1028153 = 771115) B771115
theorem B1159247 : Blo 358757 1159247 := bstep (se 1 (by rfl) ⟨869435, by rfl⟩ : syracuseStep 1159247 = 1738871) B1738871
theorem B1651049 : Blo 358757 1651049 := bstep (se 2 (by rfl) ⟨619143, by rfl⟩ : syracuseStep 1651049 = 1238287) B1238287
theorem B766903 : Blo 358757 766903 := bstep (se 1 (by rfl) ⟨575177, by rfl⟩ : syracuseStep 766903 = 1150355) B1150355
theorem B406651 : Blo 358757 406651 := bstep (se 1 (by rfl) ⟨304988, by rfl⟩ : syracuseStep 406651 = 609977) B609977
theorem B4207787 : Blo 358757 4207787 := bstep (se 1 (by rfl) ⟨3155840, by rfl⟩ : syracuseStep 4207787 = 6311681) B6311681
theorem B4634117 : Blo 358757 4634117 := bstep (se 4 (by rfl) ⟨434448, by rfl⟩ : syracuseStep 4634117 = 868897) B868897
theorem B538151 : Blo 358757 538151 := bstep (se 1 (by rfl) ⟨403613, by rfl⟩ : syracuseStep 538151 = 807227) B807227
theorem B407119 : Blo 358757 407119 := bstep (se 1 (by rfl) ⟨305339, by rfl⟩ : syracuseStep 407119 = 610679) B610679
theorem B3716705 : Blo 358757 3716705 := bstep (se 2 (by rfl) ⟨1393764, by rfl⟩ : syracuseStep 3716705 = 2787529) B2787529
theorem B1652321 : Blo 358757 1652321 := bstep (se 2 (by rfl) ⟨619620, by rfl⟩ : syracuseStep 1652321 = 1239241) B1239241
theorem B538235 : Blo 358757 538235 := bstep (se 1 (by rfl) ⟨403676, by rfl⟩ : syracuseStep 538235 = 807353) B807353
theorem B538361 : Blo 358757 538361 := bstep (se 2 (by rfl) ⟨201885, by rfl⟩ : syracuseStep 538361 = 403771) B403771
theorem B3127099 : Blo 358757 3127099 := bstep (se 1 (by rfl) ⟨2345324, by rfl⟩ : syracuseStep 3127099 = 4690649) B4690649
theorem B538463 : Blo 358757 538463 := bstep (se 1 (by rfl) ⟨403847, by rfl⟩ : syracuseStep 538463 = 807695) B807695
theorem B538475 : Blo 358757 538475 := bstep (se 1 (by rfl) ⟨403856, by rfl⟩ : syracuseStep 538475 = 807713) B807713
theorem B407515 : Blo 358757 407515 := bstep (se 1 (by rfl) ⟨305636, by rfl⟩ : syracuseStep 407515 = 611273) B611273
theorem B538703 : Blo 358757 538703 := bstep (se 1 (by rfl) ⟨404027, by rfl⟩ : syracuseStep 538703 = 808055) B808055
theorem B538823 : Blo 358757 538823 := bstep (se 1 (by rfl) ⟨404117, by rfl⟩ : syracuseStep 538823 = 808235) B808235
theorem B5191937 : Blo 358757 5191937 := bstep (se 2 (by rfl) ⟨1946976, by rfl⟩ : syracuseStep 5191937 = 3893953) B3893953
theorem B5880113 : Blo 358757 5880113 := bstep (se 2 (by rfl) ⟨2205042, by rfl⟩ : syracuseStep 5880113 = 4410085) B4410085
theorem B538985 : Blo 358757 538985 := bstep (se 2 (by rfl) ⟨202119, by rfl⟩ : syracuseStep 538985 = 404239) B404239
theorem B407983 : Blo 358757 407983 := bstep (se 1 (by rfl) ⟨305987, by rfl⟩ : syracuseStep 407983 = 611975) B611975
theorem B539063 : Blo 358757 539063 := bstep (se 1 (by rfl) ⟨404297, by rfl⟩ : syracuseStep 539063 = 808595) B808595
theorem B539099 : Blo 358757 539099 := bstep (se 1 (by rfl) ⟨404324, by rfl⟩ : syracuseStep 539099 = 808649) B808649
theorem B11057849 : Blo 358757 11057849 := bstep (se 2 (by rfl) ⟨4146693, by rfl⟩ : syracuseStep 11057849 = 8293387) B8293387
theorem B539567 : Blo 358757 539567 := bstep (se 1 (by rfl) ⟨404675, by rfl⟩ : syracuseStep 539567 = 809351) B809351
theorem B539657 : Blo 358757 539657 := bstep (se 2 (by rfl) ⟨202371, by rfl⟩ : syracuseStep 539657 = 404743) B404743
theorem B539687 : Blo 358757 539687 := bstep (se 1 (by rfl) ⟨404765, by rfl⟩ : syracuseStep 539687 = 809531) B809531
theorem B539771 : Blo 358757 539771 := bstep (se 1 (by rfl) ⟨404828, by rfl⟩ : syracuseStep 539771 = 809657) B809657
theorem B539897 : Blo 358757 539897 := bstep (se 2 (by rfl) ⟨202461, by rfl⟩ : syracuseStep 539897 = 404923) B404923
theorem B2931983 : Blo 358757 2931983 := bstep (se 1 (by rfl) ⟨2198987, by rfl⟩ : syracuseStep 2931983 = 4397975) B4397975
theorem B539999 : Blo 358757 539999 := bstep (se 1 (by rfl) ⟨404999, by rfl⟩ : syracuseStep 539999 = 809999) B809999
theorem B540011 : Blo 358757 540011 := bstep (se 1 (by rfl) ⟨405008, by rfl⟩ : syracuseStep 540011 = 810017) B810017
theorem B605623 : Blo 358757 605623 := bstep (se 1 (by rfl) ⟨454217, by rfl⟩ : syracuseStep 605623 = 908435) B908435
theorem B540239 : Blo 358757 540239 := bstep (se 1 (by rfl) ⟨405179, by rfl⟩ : syracuseStep 540239 = 810359) B810359
theorem B605819 : Blo 358757 605819 := bstep (se 1 (by rfl) ⟨454364, by rfl⟩ : syracuseStep 605819 = 908729) B908729
theorem B540359 : Blo 358757 540359 := bstep (se 1 (by rfl) ⟨405269, by rfl⟩ : syracuseStep 540359 = 810539) B810539
theorem B1949483 : Blo 358757 1949483 := bstep (se 1 (by rfl) ⟨1462112, by rfl⟩ : syracuseStep 1949483 = 2924225) B2924225
theorem B540521 : Blo 358757 540521 := bstep (se 2 (by rfl) ⟨202695, by rfl⟩ : syracuseStep 540521 = 405391) B405391
theorem B540599 : Blo 358757 540599 := bstep (se 1 (by rfl) ⟨405449, by rfl⟩ : syracuseStep 540599 = 810899) B810899
theorem B868283 : Blo 358757 868283 := bstep (se 1 (by rfl) ⟨651212, by rfl⟩ : syracuseStep 868283 = 1302425) B1302425
theorem B769979 : Blo 358757 769979 := bstep (se 1 (by rfl) ⟨577484, by rfl⟩ : syracuseStep 769979 = 1154969) B1154969
theorem B540635 : Blo 358757 540635 := bstep (se 1 (by rfl) ⟨405476, by rfl⟩ : syracuseStep 540635 = 810953) B810953
theorem B606217 : Blo 358757 606217 := bstep (se 2 (by rfl) ⟨227331, by rfl⟩ : syracuseStep 606217 = 454663) B454663
theorem B606379 : Blo 358757 606379 := bstep (se 1 (by rfl) ⟨454784, by rfl⟩ : syracuseStep 606379 = 909569) B909569
theorem B1294697 : Blo 358757 1294697 := bstep (se 2 (by rfl) ⟨485511, by rfl⟩ : syracuseStep 1294697 = 971023) B971023
theorem B541103 : Blo 358757 541103 := bstep (se 1 (by rfl) ⟨405827, by rfl⟩ : syracuseStep 541103 = 811655) B811655
theorem B606683 : Blo 358757 606683 := bstep (se 1 (by rfl) ⟨455012, by rfl⟩ : syracuseStep 606683 = 910025) B910025
theorem B541193 : Blo 358757 541193 := bstep (se 2 (by rfl) ⟨202947, by rfl⟩ : syracuseStep 541193 = 405895) B405895
theorem B2736665 : Blo 358757 2736665 := bstep (se 2 (by rfl) ⟨1026249, by rfl⟩ : syracuseStep 2736665 = 2052499) B2052499
theorem B868889 : Blo 358757 868889 := bstep (se 2 (by rfl) ⟨325833, by rfl⟩ : syracuseStep 868889 = 651667) B651667
theorem B541223 : Blo 358757 541223 := bstep (se 1 (by rfl) ⟨405917, by rfl⟩ : syracuseStep 541223 = 811835) B811835
theorem B1032743 : Blo 358757 1032743 := bstep (se 1 (by rfl) ⟨774557, by rfl⟩ : syracuseStep 1032743 = 1549115) B1549115
theorem B541307 : Blo 358757 541307 := bstep (se 1 (by rfl) ⟨405980, by rfl⟩ : syracuseStep 541307 = 811961) B811961
theorem B606919 : Blo 358757 606919 := bstep (se 1 (by rfl) ⟨455189, by rfl⟩ : syracuseStep 606919 = 910379) B910379
theorem B541433 : Blo 358757 541433 := bstep (se 2 (by rfl) ⟨203037, by rfl⟩ : syracuseStep 541433 = 406075) B406075
theorem B1819421 : Blo 358757 1819421 := bstep (se 3 (by rfl) ⟨341141, by rfl⟩ : syracuseStep 1819421 = 682283) B682283
theorem B541535 : Blo 358757 541535 := bstep (se 1 (by rfl) ⟨406151, by rfl⟩ : syracuseStep 541535 = 812303) B812303
theorem B607081 : Blo 358757 607081 := bstep (se 2 (by rfl) ⟨227655, by rfl⟩ : syracuseStep 607081 = 455311) B455311
theorem B541547 : Blo 358757 541547 := bstep (se 1 (by rfl) ⟨406160, by rfl⟩ : syracuseStep 541547 = 812321) B812321
theorem B541775 : Blo 358757 541775 := bstep (se 1 (by rfl) ⟨406331, by rfl⟩ : syracuseStep 541775 = 812663) B812663
theorem B541895 : Blo 358757 541895 := bstep (se 1 (by rfl) ⟨406421, by rfl⟩ : syracuseStep 541895 = 812843) B812843
theorem B542057 : Blo 358757 542057 := bstep (se 2 (by rfl) ⟨203271, by rfl⟩ : syracuseStep 542057 = 406543) B406543
theorem B542135 : Blo 358757 542135 := bstep (se 1 (by rfl) ⟨406601, by rfl⟩ : syracuseStep 542135 = 813203) B813203
theorem B607675 : Blo 358757 607675 := bstep (se 1 (by rfl) ⟨455756, by rfl⟩ : syracuseStep 607675 = 911513) B911513
theorem B542171 : Blo 358757 542171 := bstep (se 1 (by rfl) ⟨406628, by rfl⟩ : syracuseStep 542171 = 813257) B813257
theorem B574985 : Blo 358757 574985 := bstep (se 2 (by rfl) ⟨215619, by rfl⟩ : syracuseStep 574985 = 431239) B431239
theorem B607783 : Blo 358757 607783 := bstep (se 1 (by rfl) ⟨455837, by rfl⟩ : syracuseStep 607783 = 911675) B911675
theorem B1295995 : Blo 358757 1295995 := bstep (se 1 (by rfl) ⟨971996, by rfl⟩ : syracuseStep 1295995 = 1943993) B1943993
theorem B608107 : Blo 358757 608107 := bstep (se 1 (by rfl) ⟨456080, by rfl⟩ : syracuseStep 608107 = 912161) B912161
theorem B2770807 : Blo 358757 2770807 := bstep (se 1 (by rfl) ⟨2078105, by rfl⟩ : syracuseStep 2770807 = 4156211) B4156211
theorem B542639 : Blo 358757 542639 := bstep (se 1 (by rfl) ⟨406979, by rfl⟩ : syracuseStep 542639 = 813959) B813959
theorem B542729 : Blo 358757 542729 := bstep (se 2 (by rfl) ⟨203523, by rfl⟩ : syracuseStep 542729 = 407047) B407047
theorem B542759 : Blo 358757 542759 := bstep (se 1 (by rfl) ⟨407069, by rfl⟩ : syracuseStep 542759 = 814139) B814139
theorem B542843 : Blo 358757 542843 := bstep (se 1 (by rfl) ⟨407132, by rfl⟩ : syracuseStep 542843 = 814265) B814265
theorem B1362167 : Blo 358757 1362167 := bstep (se 1 (by rfl) ⟨1021625, by rfl⟩ : syracuseStep 1362167 = 2043251) B2043251
theorem B542969 : Blo 358757 542969 := bstep (se 2 (by rfl) ⟨203613, by rfl⟩ : syracuseStep 542969 = 407227) B407227
theorem B4933975 : Blo 358757 4933975 := bstep (se 1 (by rfl) ⟨3700481, by rfl⟩ : syracuseStep 4933975 = 7400963) B7400963
theorem B543071 : Blo 358757 543071 := bstep (se 1 (by rfl) ⟨407303, by rfl⟩ : syracuseStep 543071 = 814607) B814607
theorem B543083 : Blo 358757 543083 := bstep (se 1 (by rfl) ⟨407312, by rfl⟩ : syracuseStep 543083 = 814625) B814625
theorem B2312651 : Blo 358757 2312651 := bstep (se 1 (by rfl) ⟨1734488, by rfl⟩ : syracuseStep 2312651 = 3468977) B3468977
theorem B2050541 : Blo 358757 2050541 := bstep (se 3 (by rfl) ⟨384476, by rfl⟩ : syracuseStep 2050541 = 768953) B768953
theorem B543311 : Blo 358757 543311 := bstep (se 1 (by rfl) ⟨407483, by rfl⟩ : syracuseStep 543311 = 814967) B814967
theorem B1100477 : Blo 358757 1100477 := bstep (se 3 (by rfl) ⟨206339, by rfl⟩ : syracuseStep 1100477 = 412679) B412679
theorem B543431 : Blo 358757 543431 := bstep (se 1 (by rfl) ⟨407573, by rfl⟩ : syracuseStep 543431 = 815147) B815147
theorem B543593 : Blo 358757 543593 := bstep (se 2 (by rfl) ⟨203847, by rfl⟩ : syracuseStep 543593 = 407695) B407695
theorem B609167 : Blo 358757 609167 := bstep (se 1 (by rfl) ⟨456875, by rfl⟩ : syracuseStep 609167 = 913751) B913751
theorem B543671 : Blo 358757 543671 := bstep (se 1 (by rfl) ⟨407753, by rfl⟩ : syracuseStep 543671 = 815507) B815507
theorem B543707 : Blo 358757 543707 := bstep (se 1 (by rfl) ⟨407780, by rfl⟩ : syracuseStep 543707 = 815561) B815561
theorem B609403 : Blo 358757 609403 := bstep (se 1 (by rfl) ⟨457052, by rfl⟩ : syracuseStep 609403 = 914105) B914105
theorem B1363139 : Blo 358757 1363139 := bstep (se 1 (by rfl) ⟨1022354, by rfl⟩ : syracuseStep 1363139 = 2044709) B2044709
theorem B2739581 : Blo 358757 2739581 := bstep (se 3 (by rfl) ⟨513671, by rfl⟩ : syracuseStep 2739581 = 1027343) B1027343
theorem B2346583 : Blo 358757 2346583 := bstep (se 1 (by rfl) ⟨1759937, by rfl⟩ : syracuseStep 2346583 = 3519875) B3519875
theorem B1363655 : Blo 358757 1363655 := bstep (se 1 (by rfl) ⟨1022741, by rfl⟩ : syracuseStep 1363655 = 2045483) B2045483
theorem B511849 : Blo 358757 511849 := bstep (se 2 (by rfl) ⟨191943, by rfl⟩ : syracuseStep 511849 = 383887) B383887
theorem B610267 : Blo 358757 610267 := bstep (se 1 (by rfl) ⟨457700, by rfl⟩ : syracuseStep 610267 = 915401) B915401
theorem B8376331 : Blo 358757 8376331 := bstep (se 1 (by rfl) ⟨6282248, by rfl⟩ : syracuseStep 8376331 = 12564497) B12564497
theorem B1954153 : Blo 358757 1954153 := bstep (se 2 (by rfl) ⟨732807, by rfl⟩ : syracuseStep 1954153 = 1465615) B1465615
theorem B610895 : Blo 358757 610895 := bstep (se 1 (by rfl) ⟨458171, by rfl⟩ : syracuseStep 610895 = 916343) B916343
theorem B1364627 : Blo 358757 1364627 := bstep (se 1 (by rfl) ⟨1023470, by rfl⟩ : syracuseStep 1364627 = 2046941) B2046941
theorem B807623 : Blo 358757 807623 := bstep (se 1 (by rfl) ⟨605717, by rfl⟩ : syracuseStep 807623 = 1211435) B1211435
theorem B1364809 : Blo 358757 1364809 := bstep (se 2 (by rfl) ⟨511803, by rfl⟩ : syracuseStep 1364809 = 1023607) B1023607
theorem B1823795 : Blo 358757 1823795 := bstep (se 1 (by rfl) ⟨1367846, by rfl⟩ : syracuseStep 1823795 = 2735693) B2735693
theorem B611759 : Blo 358757 611759 := bstep (se 1 (by rfl) ⟨458819, by rfl⟩ : syracuseStep 611759 = 917639) B917639
theorem B808487 : Blo 358757 808487 := bstep (se 1 (by rfl) ⟨606365, by rfl⟩ : syracuseStep 808487 = 1212731) B1212731
theorem B5264993 : Blo 358757 5264993 := bstep (se 2 (by rfl) ⟨1974372, by rfl⟩ : syracuseStep 5264993 = 3948745) B3948745
theorem B47404865 : Blo 358757 47404865 := bstep (se 2 (by rfl) ⟨17776824, by rfl⟩ : syracuseStep 47404865 = 35553649) B35553649
theorem B808811 : Blo 358757 808811 := bstep (se 1 (by rfl) ⟨606608, by rfl⟩ : syracuseStep 808811 = 1213217) B1213217
theorem B808865 : Blo 358757 808865 := bstep (se 2 (by rfl) ⟨303324, by rfl⟩ : syracuseStep 808865 = 606649) B606649
theorem B1431631 : Blo 358757 1431631 := bstep (se 1 (by rfl) ⟨1073723, by rfl⟩ : syracuseStep 1431631 = 2147447) B2147447
theorem B809207 : Blo 358757 809207 := bstep (se 1 (by rfl) ⟨606905, by rfl⟩ : syracuseStep 809207 = 1213811) B1213811
theorem B11163905 : Blo 358757 11163905 := bstep (se 2 (by rfl) ⟨4186464, by rfl⟩ : syracuseStep 11163905 = 8372929) B8372929
theorem B6314273 : Blo 358757 6314273 := bstep (se 2 (by rfl) ⟨2367852, by rfl⟩ : syracuseStep 6314273 = 4735705) B4735705
theorem B3889457 : Blo 358757 3889457 := bstep (se 2 (by rfl) ⟨1458546, by rfl⟩ : syracuseStep 3889457 = 2917093) B2917093
theorem B7821805 : Blo 358757 7821805 := bstep (se 3 (by rfl) ⟨1466588, by rfl⟩ : syracuseStep 7821805 = 2933177) B2933177
theorem B1825415 : Blo 358757 1825415 := bstep (se 1 (by rfl) ⟨1369061, by rfl⟩ : syracuseStep 1825415 = 2738123) B2738123
theorem B1366739 : Blo 358757 1366739 := bstep (se 1 (by rfl) ⟨1025054, by rfl⟩ : syracuseStep 1366739 = 2050109) B2050109
theorem B2054915 : Blo 358757 2054915 := bstep (se 1 (by rfl) ⟨1541186, by rfl⟩ : syracuseStep 2054915 = 3082373) B3082373
theorem B2611997 : Blo 358757 2611997 := bstep (se 3 (by rfl) ⟨489749, by rfl⟩ : syracuseStep 2611997 = 979499) B979499
theorem B809801 : Blo 358757 809801 := bstep (se 2 (by rfl) ⟨303675, by rfl⟩ : syracuseStep 809801 = 607351) B607351
theorem B5299019 : Blo 358757 5299019 := bstep (se 1 (by rfl) ⟨3974264, by rfl⟩ : syracuseStep 5299019 = 7948529) B7948529
theorem B580495 : Blo 358757 580495 := bstep (se 1 (by rfl) ⟨435371, by rfl⟩ : syracuseStep 580495 = 870743) B870743
theorem B2055415 : Blo 358757 2055415 := bstep (se 1 (by rfl) ⟨1541561, by rfl⟩ : syracuseStep 2055415 = 3083123) B3083123
theorem B810593 : Blo 358757 810593 := bstep (se 2 (by rfl) ⟨303972, by rfl⟩ : syracuseStep 810593 = 607945) B607945
theorem B384635 : Blo 358757 384635 := bstep (se 1 (by rfl) ⟨288476, by rfl⟩ : syracuseStep 384635 = 576953) B576953
theorem B2743955 : Blo 358757 2743955 := bstep (se 1 (by rfl) ⟨2057966, by rfl⟩ : syracuseStep 2743955 = 4115933) B4115933
theorem B2186941 : Blo 358757 2186941 := bstep (se 3 (by rfl) ⟨410051, by rfl⟩ : syracuseStep 2186941 = 820103) B820103
theorem B26828597 : Blo 358757 26828597 := bstep (se 5 (by rfl) ⟨1257590, by rfl⟩ : syracuseStep 26828597 = 2515181) B2515181
theorem B810935 : Blo 358757 810935 := bstep (se 1 (by rfl) ⟨608201, by rfl⟩ : syracuseStep 810935 = 1216403) B1216403
theorem B1826873 : Blo 358757 1826873 := bstep (se 2 (by rfl) ⟨685077, by rfl⟩ : syracuseStep 1826873 = 1370155) B1370155
theorem B647291 : Blo 358757 647291 := bstep (se 1 (by rfl) ⟨485468, by rfl⟩ : syracuseStep 647291 = 970937) B970937
theorem B647689 : Blo 358757 647689 := bstep (se 2 (by rfl) ⟨242883, by rfl⟩ : syracuseStep 647689 = 485767) B485767
theorem B811529 : Blo 358757 811529 := bstep (se 2 (by rfl) ⟨304323, by rfl⟩ : syracuseStep 811529 = 608647) B608647
theorem B909863 : Blo 358757 909863 := bstep (se 1 (by rfl) ⟨682397, by rfl⟩ : syracuseStep 909863 = 1364795) B1364795
theorem B811871 : Blo 358757 811871 := bstep (se 1 (by rfl) ⟨608903, by rfl⟩ : syracuseStep 811871 = 1217807) B1217807
theorem B910187 : Blo 358757 910187 := bstep (se 1 (by rfl) ⟨682640, by rfl⟩ : syracuseStep 910187 = 1365281) B1365281
theorem B812051 : Blo 358757 812051 := bstep (se 1 (by rfl) ⟨609038, by rfl⟩ : syracuseStep 812051 = 1218077) B1218077
theorem B648271 : Blo 358757 648271 := bstep (se 1 (by rfl) ⟨486203, by rfl⟩ : syracuseStep 648271 = 972407) B972407
theorem B1369169 : Blo 358757 1369169 := bstep (se 2 (by rfl) ⟨513438, by rfl⟩ : syracuseStep 1369169 = 1026877) B1026877
theorem B2974913 : Blo 358757 2974913 := bstep (se 2 (by rfl) ⟨1115592, by rfl⟩ : syracuseStep 2974913 = 2231185) B2231185
theorem B681311 : Blo 358757 681311 := bstep (se 1 (by rfl) ⟨510983, by rfl⟩ : syracuseStep 681311 = 1021967) B1021967
theorem B812393 : Blo 358757 812393 := bstep (se 2 (by rfl) ⟨304647, by rfl⟩ : syracuseStep 812393 = 609295) B609295
theorem B1369487 : Blo 358757 1369487 := bstep (se 1 (by rfl) ⟨1027115, by rfl⟩ : syracuseStep 1369487 = 2054231) B2054231
theorem B615899 : Blo 358757 615899 := bstep (se 1 (by rfl) ⟨461924, by rfl⟩ : syracuseStep 615899 = 923849) B923849
theorem B910835 : Blo 358757 910835 := bstep (se 1 (by rfl) ⟨683126, by rfl⟩ : syracuseStep 910835 = 1366253) B1366253
theorem B911047 : Blo 358757 911047 := bstep (se 1 (by rfl) ⟨683285, by rfl⟩ : syracuseStep 911047 = 1366571) B1366571
theorem B1468115 : Blo 358757 1468115 := bstep (se 1 (by rfl) ⟨1101086, by rfl⟩ : syracuseStep 1468115 = 2202173) B2202173
theorem B4155095 : Blo 358757 4155095 := bstep (se 1 (by rfl) ⟨3116321, by rfl⟩ : syracuseStep 4155095 = 6232643) B6232643
theorem B1959673 : Blo 358757 1959673 := bstep (se 2 (by rfl) ⟨734877, by rfl⟩ : syracuseStep 1959673 = 1469755) B1469755
theorem B10348337 : Blo 358757 10348337 := bstep (se 2 (by rfl) ⟨3880626, by rfl⟩ : syracuseStep 10348337 = 7761253) B7761253
theorem B1730413 : Blo 358757 1730413 := bstep (se 3 (by rfl) ⟨324452, by rfl⟩ : syracuseStep 1730413 = 648905) B648905
theorem B812987 : Blo 358757 812987 := bstep (se 1 (by rfl) ⟨609740, by rfl⟩ : syracuseStep 812987 = 1219481) B1219481
theorem B1730567 : Blo 358757 1730567 := bstep (se 1 (by rfl) ⟨1297925, by rfl⟩ : syracuseStep 1730567 = 2595851) B2595851
theorem B813113 : Blo 358757 813113 := bstep (se 2 (by rfl) ⟨304917, by rfl⟩ : syracuseStep 813113 = 609835) B609835
theorem B1828979 : Blo 358757 1828979 := bstep (se 1 (by rfl) ⟨1371734, by rfl⟩ : syracuseStep 1828979 = 2743469) B2743469
theorem B1370429 : Blo 358757 1370429 := bstep (se 3 (by rfl) ⟨256955, by rfl⟩ : syracuseStep 1370429 = 513911) B513911
theorem B3107159 : Blo 358757 3107159 := bstep (se 1 (by rfl) ⟨2330369, by rfl⟩ : syracuseStep 3107159 = 4660739) B4660739
theorem B3303767 : Blo 358757 3303767 := bstep (se 1 (by rfl) ⟨2477825, by rfl⟩ : syracuseStep 3303767 = 4955651) B4955651
theorem B813455 : Blo 358757 813455 := bstep (se 1 (by rfl) ⟨610091, by rfl⟩ : syracuseStep 813455 = 1220183) B1220183
theorem B4385177 : Blo 358757 4385177 := bstep (se 2 (by rfl) ⟨1644441, by rfl⟩ : syracuseStep 4385177 = 3288883) B3288883
theorem B911969 : Blo 358757 911969 := bstep (se 2 (by rfl) ⟨341988, by rfl⟩ : syracuseStep 911969 = 683977) B683977
theorem B813779 : Blo 358757 813779 := bstep (se 1 (by rfl) ⟨610334, by rfl⟩ : syracuseStep 813779 = 1220669) B1220669
theorem B2747357 : Blo 358757 2747357 := bstep (se 3 (by rfl) ⟨515129, by rfl⟩ : syracuseStep 2747357 = 1030259) B1030259
theorem B683255 : Blo 358757 683255 := bstep (se 1 (by rfl) ⟨512441, by rfl⟩ : syracuseStep 683255 = 1024883) B1024883
theorem B683407 : Blo 358757 683407 := bstep (se 1 (by rfl) ⟨512555, by rfl⟩ : syracuseStep 683407 = 1025111) B1025111
theorem B978419 : Blo 358757 978419 := bstep (se 1 (by rfl) ⟨733814, by rfl⟩ : syracuseStep 978419 = 1467629) B1467629
theorem B1306145 : Blo 358757 1306145 := bstep (se 2 (by rfl) ⟨489804, by rfl⟩ : syracuseStep 1306145 = 979609) B979609
theorem B9858647 : Blo 358757 9858647 := bstep (se 1 (by rfl) ⟨7393985, by rfl⟩ : syracuseStep 9858647 = 14787971) B14787971
theorem B1044065 : Blo 358757 1044065 := bstep (se 2 (by rfl) ⟨391524, by rfl⟩ : syracuseStep 1044065 = 783049) B783049
theorem B814715 : Blo 358757 814715 := bstep (se 1 (by rfl) ⟨611036, by rfl⟩ : syracuseStep 814715 = 1222073) B1222073
theorem B1732241 : Blo 358757 1732241 := bstep (se 2 (by rfl) ⟨649590, by rfl⟩ : syracuseStep 1732241 = 1299181) B1299181
theorem B650923 : Blo 358757 650923 := bstep (se 1 (by rfl) ⟨488192, by rfl⟩ : syracuseStep 650923 = 976385) B976385
theorem B1830599 : Blo 358757 1830599 := bstep (se 1 (by rfl) ⟨1372949, by rfl⟩ : syracuseStep 1830599 = 2745899) B2745899
theorem B4484845 : Blo 358757 4484845 := bstep (se 3 (by rfl) ⟨840908, by rfl⟩ : syracuseStep 4484845 = 1681817) B1681817
theorem B814841 : Blo 358757 814841 := bstep (se 2 (by rfl) ⟨305565, by rfl⟩ : syracuseStep 814841 = 611131) B611131
theorem B815111 : Blo 358757 815111 := bstep (se 1 (by rfl) ⟨611333, by rfl⟩ : syracuseStep 815111 = 1222667) B1222667
theorem B913427 : Blo 358757 913427 := bstep (se 1 (by rfl) ⟨685070, by rfl⟩ : syracuseStep 913427 = 1370141) B1370141
theorem B815183 : Blo 358757 815183 := bstep (se 1 (by rfl) ⟨611387, by rfl⟩ : syracuseStep 815183 = 1222775) B1222775
theorem B684281 : Blo 358757 684281 := bstep (se 2 (by rfl) ⟨256605, by rfl⟩ : syracuseStep 684281 = 513211) B513211
theorem B618745 : Blo 358757 618745 := bstep (se 2 (by rfl) ⟨232029, by rfl⟩ : syracuseStep 618745 = 464059) B464059
theorem B520543 : Blo 358757 520543 := bstep (se 1 (by rfl) ⟨390407, by rfl⟩ : syracuseStep 520543 = 780815) B780815
theorem B684463 : Blo 358757 684463 := bstep (se 1 (by rfl) ⟨513347, by rfl⟩ : syracuseStep 684463 = 1026695) B1026695
theorem B815579 : Blo 358757 815579 := bstep (se 1 (by rfl) ⟨611684, by rfl⟩ : syracuseStep 815579 = 1223369) B1223369
theorem B2912777 : Blo 358757 2912777 := bstep (se 2 (by rfl) ⟨1092291, by rfl⟩ : syracuseStep 2912777 = 2184583) B2184583
theorem B4452889 : Blo 358757 4452889 := bstep (se 2 (by rfl) ⟨1669833, by rfl⟩ : syracuseStep 4452889 = 3339667) B3339667
theorem B6615857 : Blo 358757 6615857 := bstep (se 2 (by rfl) ⟨2480946, by rfl⟩ : syracuseStep 6615857 = 4961893) B4961893
theorem B816047 : Blo 358757 816047 := bstep (se 1 (by rfl) ⟨612035, by rfl⟩ : syracuseStep 816047 = 1224071) B1224071
theorem B652307 : Blo 358757 652307 := bstep (se 1 (by rfl) ⟨489230, by rfl⟩ : syracuseStep 652307 = 978461) B978461
theorem B1733683 : Blo 358757 1733683 := bstep (se 1 (by rfl) ⟨1300262, by rfl⟩ : syracuseStep 1733683 = 2600525) B2600525
theorem B423263 : Blo 358757 423263 := bstep (se 1 (by rfl) ⟨317447, by rfl⟩ : syracuseStep 423263 = 634895) B634895
theorem B30078307 : Blo 358757 30078307 := bstep (se 1 (by rfl) ⟨22558730, by rfl⟩ : syracuseStep 30078307 = 45117461) B45117461
theorem B1373831 : Blo 358757 1373831 := bstep (se 1 (by rfl) ⟨1030373, by rfl⟩ : syracuseStep 1373831 = 2060747) B2060747
theorem B685739 : Blo 358757 685739 := bstep (se 1 (by rfl) ⟨514304, by rfl⟩ : syracuseStep 685739 = 1028609) B1028609
theorem B1538129 : Blo 358757 1538129 := bstep (se 2 (by rfl) ⟨576798, by rfl⟩ : syracuseStep 1538129 = 1153597) B1153597
theorem B8976541 : Blo 358757 8976541 := bstep (se 3 (by rfl) ⟨1683101, by rfl⟩ : syracuseStep 8976541 = 3366203) B3366203
theorem B358779 : Blo 358757 358779 := bstep (se 1 (by rfl) ⟨269084, by rfl⟩ : syracuseStep 358779 = 538169) B538169
theorem B358831 : Blo 358757 358831 := bstep (se 1 (by rfl) ⟨269123, by rfl⟩ : syracuseStep 358831 = 538247) B538247
theorem B358855 : Blo 358757 358855 := bstep (se 1 (by rfl) ⟨269141, by rfl⟩ : syracuseStep 358855 = 538283) B538283
theorem B358875 : Blo 358757 358875 := bstep (se 1 (by rfl) ⟨269156, by rfl⟩ : syracuseStep 358875 = 538313) B538313
theorem B358951 : Blo 358757 358951 := bstep (se 1 (by rfl) ⟨269213, by rfl⟩ : syracuseStep 358951 = 538427) B538427
theorem B457255 : Blo 358757 457255 := bstep (se 1 (by rfl) ⟨342941, by rfl⟩ : syracuseStep 457255 = 685883) B685883
theorem B358991 : Blo 358757 358991 := bstep (se 1 (by rfl) ⟨269243, by rfl⟩ : syracuseStep 358991 = 538487) B538487
theorem B359007 : Blo 358757 359007 := bstep (se 1 (by rfl) ⟨269255, by rfl⟩ : syracuseStep 359007 = 538511) B538511
theorem B1211003 : Blo 358757 1211003 := bstep (se 1 (by rfl) ⟨908252, by rfl⟩ : syracuseStep 1211003 = 1816505) B1816505
theorem B359035 : Blo 358757 359035 := bstep (se 1 (by rfl) ⟨269276, by rfl⟩ : syracuseStep 359035 = 538553) B538553
theorem B359087 : Blo 358757 359087 := bstep (se 1 (by rfl) ⟨269315, by rfl⟩ : syracuseStep 359087 = 538631) B538631
theorem B359111 : Blo 358757 359111 := bstep (se 1 (by rfl) ⟨269333, by rfl⟩ : syracuseStep 359111 = 538667) B538667
theorem B359131 : Blo 358757 359131 := bstep (se 1 (by rfl) ⟨269348, by rfl⟩ : syracuseStep 359131 = 538697) B538697
theorem B1211165 : Blo 358757 1211165 := bstep (se 3 (by rfl) ⟨227093, by rfl⟩ : syracuseStep 1211165 = 454187) B454187
theorem B359207 : Blo 358757 359207 := bstep (se 1 (by rfl) ⟨269405, by rfl⟩ : syracuseStep 359207 = 538811) B538811
theorem B359247 : Blo 358757 359247 := bstep (se 1 (by rfl) ⟨269435, by rfl⟩ : syracuseStep 359247 = 538871) B538871
theorem B359263 : Blo 358757 359263 := bstep (se 1 (by rfl) ⟨269447, by rfl⟩ : syracuseStep 359263 = 538895) B538895
theorem B457579 : Blo 358757 457579 := bstep (se 1 (by rfl) ⟨343184, by rfl⟩ : syracuseStep 457579 = 686369) B686369
theorem B359291 : Blo 358757 359291 := bstep (se 1 (by rfl) ⟨269468, by rfl⟩ : syracuseStep 359291 = 538937) B538937
theorem B359343 : Blo 358757 359343 := bstep (se 1 (by rfl) ⟨269507, by rfl⟩ : syracuseStep 359343 = 539015) B539015
theorem B359367 : Blo 358757 359367 := bstep (se 1 (by rfl) ⟨269525, by rfl⟩ : syracuseStep 359367 = 539051) B539051
theorem B359387 : Blo 358757 359387 := bstep (se 1 (by rfl) ⟨269540, by rfl⟩ : syracuseStep 359387 = 539081) B539081
theorem B1735681 : Blo 358757 1735681 := bstep (se 2 (by rfl) ⟨650880, by rfl⟩ : syracuseStep 1735681 = 1301761) B1301761
theorem B687113 : Blo 358757 687113 := bstep (se 2 (by rfl) ⟨257667, by rfl⟩ : syracuseStep 687113 = 515335) B515335
theorem B1506319 : Blo 358757 1506319 := bstep (se 1 (by rfl) ⟨1129739, by rfl⟩ : syracuseStep 1506319 = 2259479) B2259479
theorem B359463 : Blo 358757 359463 := bstep (se 1 (by rfl) ⟨269597, by rfl⟩ : syracuseStep 359463 = 539195) B539195
theorem B687143 : Blo 358757 687143 := bstep (se 1 (by rfl) ⟨515357, by rfl⟩ : syracuseStep 687143 = 1030715) B1030715
theorem B1375289 : Blo 358757 1375289 := bstep (se 2 (by rfl) ⟨515733, by rfl⟩ : syracuseStep 1375289 = 1031467) B1031467
theorem B359503 : Blo 358757 359503 := bstep (se 1 (by rfl) ⟨269627, by rfl⟩ : syracuseStep 359503 = 539255) B539255
theorem B457807 : Blo 358757 457807 := bstep (se 1 (by rfl) ⟨343355, by rfl⟩ : syracuseStep 457807 = 686711) B686711
theorem B359519 : Blo 358757 359519 := bstep (se 1 (by rfl) ⟨269639, by rfl⟩ : syracuseStep 359519 = 539279) B539279
theorem B359547 : Blo 358757 359547 := bstep (se 1 (by rfl) ⟨269660, by rfl⟩ : syracuseStep 359547 = 539321) B539321
theorem B359599 : Blo 358757 359599 := bstep (se 1 (by rfl) ⟨269699, by rfl⟩ : syracuseStep 359599 = 539399) B539399
theorem B359623 : Blo 358757 359623 := bstep (se 1 (by rfl) ⟨269717, by rfl⟩ : syracuseStep 359623 = 539435) B539435
theorem B359643 : Blo 358757 359643 := bstep (se 1 (by rfl) ⟨269732, by rfl⟩ : syracuseStep 359643 = 539465) B539465
theorem B2587895 : Blo 358757 2587895 := bstep (se 1 (by rfl) ⟨1940921, by rfl⟩ : syracuseStep 2587895 = 3881843) B3881843
theorem B1015031 : Blo 358757 1015031 := bstep (se 1 (by rfl) ⟨761273, by rfl⟩ : syracuseStep 1015031 = 1522547) B1522547
theorem B359719 : Blo 358757 359719 := bstep (se 1 (by rfl) ⟨269789, by rfl⟩ : syracuseStep 359719 = 539579) B539579
theorem B359759 : Blo 358757 359759 := bstep (se 1 (by rfl) ⟨269819, by rfl⟩ : syracuseStep 359759 = 539639) B539639
theorem B359775 : Blo 358757 359775 := bstep (se 1 (by rfl) ⟨269831, by rfl⟩ : syracuseStep 359775 = 539663) B539663
theorem B359803 : Blo 358757 359803 := bstep (se 1 (by rfl) ⟨269852, by rfl⟩ : syracuseStep 359803 = 539705) B539705
theorem B916879 : Blo 358757 916879 := bstep (se 1 (by rfl) ⟨687659, by rfl⟩ : syracuseStep 916879 = 1375319) B1375319
theorem B359855 : Blo 358757 359855 := bstep (se 1 (by rfl) ⟨269891, by rfl⟩ : syracuseStep 359855 = 539783) B539783
theorem B359879 : Blo 358757 359879 := bstep (se 1 (by rfl) ⟨269909, by rfl⟩ : syracuseStep 359879 = 539819) B539819
theorem B1211867 : Blo 358757 1211867 := bstep (se 1 (by rfl) ⟨908900, by rfl⟩ : syracuseStep 1211867 = 1817801) B1817801
theorem B359899 : Blo 358757 359899 := bstep (se 1 (by rfl) ⟨269924, by rfl⟩ : syracuseStep 359899 = 539849) B539849
theorem B359975 : Blo 358757 359975 := bstep (se 1 (by rfl) ⟨269981, by rfl⟩ : syracuseStep 359975 = 539963) B539963
theorem B360015 : Blo 358757 360015 := bstep (se 1 (by rfl) ⟨270011, by rfl⟩ : syracuseStep 360015 = 540023) B540023
theorem B360031 : Blo 358757 360031 := bstep (se 1 (by rfl) ⟨270023, by rfl⟩ : syracuseStep 360031 = 540047) B540047
theorem B360059 : Blo 358757 360059 := bstep (se 1 (by rfl) ⟨270044, by rfl⟩ : syracuseStep 360059 = 540089) B540089
theorem B360111 : Blo 358757 360111 := bstep (se 1 (by rfl) ⟨270083, by rfl⟩ : syracuseStep 360111 = 540167) B540167
theorem B622279 : Blo 358757 622279 := bstep (se 1 (by rfl) ⟨466709, by rfl⟩ : syracuseStep 622279 = 933419) B933419
theorem B360135 : Blo 358757 360135 := bstep (se 1 (by rfl) ⟨270101, by rfl⟩ : syracuseStep 360135 = 540203) B540203
theorem B687827 : Blo 358757 687827 := bstep (se 1 (by rfl) ⟨515870, by rfl⟩ : syracuseStep 687827 = 1031741) B1031741
theorem B917203 : Blo 358757 917203 := bstep (se 1 (by rfl) ⟨687902, by rfl⟩ : syracuseStep 917203 = 1375805) B1375805
theorem B360155 : Blo 358757 360155 := bstep (se 1 (by rfl) ⟨270116, by rfl⟩ : syracuseStep 360155 = 540233) B540233
theorem B687865 : Blo 358757 687865 := bstep (se 2 (by rfl) ⟨257949, by rfl⟩ : syracuseStep 687865 = 515899) B515899
theorem B360231 : Blo 358757 360231 := bstep (se 1 (by rfl) ⟨270173, by rfl⟩ : syracuseStep 360231 = 540347) B540347
theorem B360271 : Blo 358757 360271 := bstep (se 1 (by rfl) ⟨270203, by rfl⟩ : syracuseStep 360271 = 540407) B540407
theorem B360287 : Blo 358757 360287 := bstep (se 1 (by rfl) ⟨270215, by rfl⟩ : syracuseStep 360287 = 540431) B540431
theorem B2195309 : Blo 358757 2195309 := bstep (se 3 (by rfl) ⟨411620, by rfl⟩ : syracuseStep 2195309 = 823241) B823241
theorem B360315 : Blo 358757 360315 := bstep (se 1 (by rfl) ⟨270236, by rfl⟩ : syracuseStep 360315 = 540473) B540473
theorem B360367 : Blo 358757 360367 := bstep (se 1 (by rfl) ⟨270275, by rfl⟩ : syracuseStep 360367 = 540551) B540551
theorem B360391 : Blo 358757 360391 := bstep (se 1 (by rfl) ⟨270293, by rfl⟩ : syracuseStep 360391 = 540587) B540587
theorem B360411 : Blo 358757 360411 := bstep (se 1 (by rfl) ⟨270308, by rfl⟩ : syracuseStep 360411 = 540617) B540617
theorem B15728717 : Blo 358757 15728717 := bstep (se 3 (by rfl) ⟨2949134, by rfl⟩ : syracuseStep 15728717 = 5898269) B5898269
theorem B360735 : Blo 358757 360735 := bstep (se 1 (by rfl) ⟨270551, by rfl⟩ : syracuseStep 360735 = 541103) B541103
theorem B459047 : Blo 358757 459047 := bstep (se 1 (by rfl) ⟨344285, by rfl⟩ : syracuseStep 459047 = 688571) B688571
theorem B360795 : Blo 358757 360795 := bstep (se 1 (by rfl) ⟨270596, by rfl⟩ : syracuseStep 360795 = 541193) B541193
theorem B917851 : Blo 358757 917851 := bstep (se 1 (by rfl) ⟨688388, by rfl⟩ : syracuseStep 917851 = 1376777) B1376777
theorem B360815 : Blo 358757 360815 := bstep (se 1 (by rfl) ⟨270611, by rfl⟩ : syracuseStep 360815 = 541223) B541223
theorem B688495 : Blo 358757 688495 := bstep (se 1 (by rfl) ⟨516371, by rfl⟩ : syracuseStep 688495 = 1032743) B1032743
theorem B360871 : Blo 358757 360871 := bstep (se 1 (by rfl) ⟨270653, by rfl⟩ : syracuseStep 360871 = 541307) B541307
theorem B3113417 : Blo 358757 3113417 := bstep (se 2 (by rfl) ⟨1167531, by rfl⟩ : syracuseStep 3113417 = 2335063) B2335063
theorem B360955 : Blo 358757 360955 := bstep (se 1 (by rfl) ⟨270716, by rfl⟩ : syracuseStep 360955 = 541433) B541433
theorem B1212947 : Blo 358757 1212947 := bstep (se 1 (by rfl) ⟨909710, by rfl⟩ : syracuseStep 1212947 = 1819421) B1819421
theorem B361023 : Blo 358757 361023 := bstep (se 1 (by rfl) ⟨270767, by rfl⟩ : syracuseStep 361023 = 541535) B541535
theorem B361031 : Blo 358757 361031 := bstep (se 1 (by rfl) ⟨270773, by rfl⟩ : syracuseStep 361031 = 541547) B541547
theorem B5505671 : Blo 358757 5505671 := bstep (se 1 (by rfl) ⟨4129253, by rfl⟩ : syracuseStep 5505671 = 8258507) B8258507
theorem B361183 : Blo 358757 361183 := bstep (se 1 (by rfl) ⟨270887, by rfl⟩ : syracuseStep 361183 = 541775) B541775
theorem B361263 : Blo 358757 361263 := bstep (se 1 (by rfl) ⟨270947, by rfl⟩ : syracuseStep 361263 = 541895) B541895
theorem B3474323 : Blo 358757 3474323 := bstep (se 1 (by rfl) ⟨2605742, by rfl⟩ : syracuseStep 3474323 = 5211485) B5211485
theorem B361371 : Blo 358757 361371 := bstep (se 1 (by rfl) ⟨271028, by rfl⟩ : syracuseStep 361371 = 542057) B542057
theorem B3474359 : Blo 358757 3474359 := bstep (se 1 (by rfl) ⟨2605769, by rfl⟩ : syracuseStep 3474359 = 5211539) B5211539
theorem B361423 : Blo 358757 361423 := bstep (se 1 (by rfl) ⟨271067, by rfl⟩ : syracuseStep 361423 = 542135) B542135
theorem B361447 : Blo 358757 361447 := bstep (se 1 (by rfl) ⟨271085, by rfl⟩ : syracuseStep 361447 = 542171) B542171
theorem B361759 : Blo 358757 361759 := bstep (se 1 (by rfl) ⟨271319, by rfl⟩ : syracuseStep 361759 = 542639) B542639
theorem B361819 : Blo 358757 361819 := bstep (se 1 (by rfl) ⟨271364, by rfl⟩ : syracuseStep 361819 = 542729) B542729
theorem B361839 : Blo 358757 361839 := bstep (se 1 (by rfl) ⟨271379, by rfl⟩ : syracuseStep 361839 = 542759) B542759
theorem B361895 : Blo 358757 361895 := bstep (se 1 (by rfl) ⟨271421, by rfl⟩ : syracuseStep 361895 = 542843) B542843
theorem B361979 : Blo 358757 361979 := bstep (se 1 (by rfl) ⟨271484, by rfl⟩ : syracuseStep 361979 = 542969) B542969
theorem B362047 : Blo 358757 362047 := bstep (se 1 (by rfl) ⟨271535, by rfl⟩ : syracuseStep 362047 = 543071) B543071
theorem B362055 : Blo 358757 362055 := bstep (se 1 (by rfl) ⟨271541, by rfl⟩ : syracuseStep 362055 = 543083) B543083
theorem B1541767 : Blo 358757 1541767 := bstep (se 1 (by rfl) ⟨1156325, by rfl⟩ : syracuseStep 1541767 = 2312651) B2312651
theorem B362207 : Blo 358757 362207 := bstep (se 1 (by rfl) ⟨271655, by rfl⟩ : syracuseStep 362207 = 543311) B543311
theorem B362287 : Blo 358757 362287 := bstep (se 1 (by rfl) ⟨271715, by rfl⟩ : syracuseStep 362287 = 543431) B543431
theorem B7997251 : Blo 358757 7997251 := bstep (se 1 (by rfl) ⟨5997938, by rfl⟩ : syracuseStep 7997251 = 11995877) B11995877
theorem B362395 : Blo 358757 362395 := bstep (se 1 (by rfl) ⟨271796, by rfl⟩ : syracuseStep 362395 = 543593) B543593
theorem B362447 : Blo 358757 362447 := bstep (se 1 (by rfl) ⟨271835, by rfl⟩ : syracuseStep 362447 = 543671) B543671
theorem B460775 : Blo 358757 460775 := bstep (se 1 (by rfl) ⟨345581, by rfl⟩ : syracuseStep 460775 = 691163) B691163
theorem B362471 : Blo 358757 362471 := bstep (se 1 (by rfl) ⟨271853, by rfl⟩ : syracuseStep 362471 = 543707) B543707
theorem B1214729 : Blo 358757 1214729 := bstep (se 2 (by rfl) ⟨455523, by rfl⟩ : syracuseStep 1214729 = 911047) B911047
theorem B1739485 : Blo 358757 1739485 := bstep (se 3 (by rfl) ⟨326153, by rfl⟩ : syracuseStep 1739485 = 652307) B652307
theorem B2493659 : Blo 358757 2493659 := bstep (se 1 (by rfl) ⟨1870244, by rfl⟩ : syracuseStep 2493659 = 3740489) B3740489
theorem B1215863 : Blo 358757 1215863 := bstep (se 1 (by rfl) ⟨911897, by rfl⟩ : syracuseStep 1215863 = 1823795) B1823795
theorem B1969595 : Blo 358757 1969595 := bstep (se 1 (by rfl) ⟨1477196, by rfl⟩ : syracuseStep 1969595 = 2954393) B2954393
theorem B1150625 : Blo 358757 1150625 := bstep (se 2 (by rfl) ⟨431484, by rfl⟩ : syracuseStep 1150625 = 862969) B862969
theorem B3509995 : Blo 358757 3509995 := bstep (se 1 (by rfl) ⟨2632496, by rfl⟩ : syracuseStep 3509995 = 5264993) B5264993
theorem B921385 : Blo 358757 921385 := bstep (se 2 (by rfl) ⟨345519, by rfl⟩ : syracuseStep 921385 = 691039) B691039
theorem B7442603 : Blo 358757 7442603 := bstep (se 1 (by rfl) ⟨5581952, by rfl⟩ : syracuseStep 7442603 = 11163905) B11163905
theorem B2592971 : Blo 358757 2592971 := bstep (se 1 (by rfl) ⟨1944728, by rfl⟩ : syracuseStep 2592971 = 3889457) B3889457
theorem B1216943 : Blo 358757 1216943 := bstep (se 1 (by rfl) ⟨912707, by rfl⟩ : syracuseStep 1216943 = 1825415) B1825415
theorem B3084763 : Blo 358757 3084763 := bstep (se 1 (by rfl) ⟨2313572, by rfl⟩ : syracuseStep 3084763 = 4627145) B4627145
theorem B1741331 : Blo 358757 1741331 := bstep (se 1 (by rfl) ⟨1305998, by rfl⟩ : syracuseStep 1741331 = 2611997) B2611997
theorem B11080253 : Blo 358757 11080253 := bstep (se 3 (by rfl) ⟨2077547, by rfl⟩ : syracuseStep 11080253 = 4155095) B4155095
theorem B8753993 : Blo 358757 8753993 := bstep (se 2 (by rfl) ⟨3282747, by rfl⟩ : syracuseStep 8753993 = 6565495) B6565495
theorem B922823 : Blo 358757 922823 := bstep (se 1 (by rfl) ⟨692117, by rfl⟩ : syracuseStep 922823 = 1384235) B1384235
theorem B1217915 : Blo 358757 1217915 := bstep (se 1 (by rfl) ⟨913436, by rfl⟩ : syracuseStep 1217915 = 1826873) B1826873
theorem B8033701 : Blo 358757 8033701 := bstep (se 4 (by rfl) ⟨753159, by rfl⟩ : syracuseStep 8033701 = 1506319) B1506319
theorem B824993 : Blo 358757 824993 := bstep (se 2 (by rfl) ⟨309372, by rfl⟩ : syracuseStep 824993 = 618745) B618745
theorem B694057 : Blo 358757 694057 := bstep (se 2 (by rfl) ⟨260271, by rfl⟩ : syracuseStep 694057 = 520543) B520543
theorem B5937185 : Blo 358757 5937185 := bstep (se 2 (by rfl) ⟨2226444, by rfl⟩ : syracuseStep 5937185 = 4452889) B4452889
theorem B1022537 : Blo 358757 1022537 := bstep (se 2 (by rfl) ⟨383451, by rfl⟩ : syracuseStep 1022537 = 766903) B766903
theorem B1153711 : Blo 358757 1153711 := bstep (se 1 (by rfl) ⟨865283, by rfl⟩ : syracuseStep 1153711 = 1730567) B1730567
theorem B1219319 : Blo 358757 1219319 := bstep (se 1 (by rfl) ⟨914489, by rfl⟩ : syracuseStep 1219319 = 1828979) B1828979
theorem B2071439 : Blo 358757 2071439 := bstep (se 1 (by rfl) ⟨1553579, by rfl⟩ : syracuseStep 2071439 = 3107159) B3107159
theorem B2202511 : Blo 358757 2202511 := bstep (se 1 (by rfl) ⟨1651883, by rfl⟩ : syracuseStep 2202511 = 3303767) B3303767
theorem B2923451 : Blo 358757 2923451 := bstep (se 1 (by rfl) ⟨2192588, by rfl⟩ : syracuseStep 2923451 = 4385177) B4385177
theorem B696043 : Blo 358757 696043 := bstep (se 1 (by rfl) ⟨522032, by rfl⟩ : syracuseStep 696043 = 1044065) B1044065
theorem B4169465 : Blo 358757 4169465 := bstep (se 2 (by rfl) ⟨1563549, by rfl⟩ : syracuseStep 4169465 = 3127099) B3127099
theorem B1154827 : Blo 358757 1154827 := bstep (se 1 (by rfl) ⟨866120, by rfl⟩ : syracuseStep 1154827 = 1732241) B1732241
theorem B1220399 : Blo 358757 1220399 := bstep (se 1 (by rfl) ⟨915299, by rfl⟩ : syracuseStep 1220399 = 1830599) B1830599
theorem B1908841 : Blo 358757 1908841 := bstep (se 2 (by rfl) ⟨715815, by rfl⟩ : syracuseStep 1908841 = 1431631) B1431631
theorem B11968721 : Blo 358757 11968721 := bstep (se 2 (by rfl) ⟨4488270, by rfl⟩ : syracuseStep 11968721 = 8976541) B8976541
theorem B1941851 : Blo 358757 1941851 := bstep (se 1 (by rfl) ⟨1456388, by rfl⟩ : syracuseStep 1941851 = 2912777) B2912777
theorem B10429073 : Blo 358757 10429073 := bstep (se 2 (by rfl) ⟨3910902, by rfl⟩ : syracuseStep 10429073 = 7821805) B7821805
theorem B3089411 : Blo 358757 3089411 := bstep (se 1 (by rfl) ⟨2317058, by rfl⟩ : syracuseStep 3089411 = 4634117) B4634117
theorem B1025419 : Blo 358757 1025419 := bstep (se 1 (by rfl) ⟨769064, by rfl⟩ : syracuseStep 1025419 = 1538129) B1538129
theorem B1025693 : Blo 358757 1025693 := bstep (se 3 (by rfl) ⟨192317, by rfl⟩ : syracuseStep 1025693 = 384635) B384635
theorem B1222505 : Blo 358757 1222505 := bstep (se 2 (by rfl) ⟨458439, by rfl⟩ : syracuseStep 1222505 = 916879) B916879
theorem B2729861 : Blo 358757 2729861 := bstep (se 4 (by rfl) ⟨255924, by rfl⟩ : syracuseStep 2729861 = 511849) B511849
theorem B829705 : Blo 358757 829705 := bstep (se 2 (by rfl) ⟨311139, by rfl⟩ : syracuseStep 829705 = 622279) B622279
theorem B1222937 : Blo 358757 1222937 := bstep (se 2 (by rfl) ⟨458601, by rfl⟩ : syracuseStep 1222937 = 917203) B917203
theorem B403879 : Blo 358757 403879 := bstep (se 1 (by rfl) ⟨302909, by rfl⟩ : syracuseStep 403879 = 605819) B605819
theorem B2304733 : Blo 358757 2304733 := bstep (se 3 (by rfl) ⟨432137, by rfl⟩ : syracuseStep 2304733 = 864275) B864275
theorem B863131 : Blo 358757 863131 := bstep (se 1 (by rfl) ⟨647348, by rfl⟩ : syracuseStep 863131 = 1294697) B1294697
theorem B1092523 : Blo 358757 1092523 := bstep (se 1 (by rfl) ⟨819392, by rfl⟩ : syracuseStep 1092523 = 1638785) B1638785
theorem B404455 : Blo 358757 404455 := bstep (se 1 (by rfl) ⟨303341, by rfl⟩ : syracuseStep 404455 = 606683) B606683
theorem B1092595 : Blo 358757 1092595 := bstep (se 1 (by rfl) ⟨819446, by rfl⟩ : syracuseStep 1092595 = 1638893) B1638893
theorem B5024987 : Blo 358757 5024987 := bstep (se 1 (by rfl) ⟨3768740, by rfl⟩ : syracuseStep 5024987 = 7537481) B7537481
theorem B863585 : Blo 358757 863585 := bstep (se 2 (by rfl) ⟨323844, by rfl⟩ : syracuseStep 863585 = 647689) B647689
theorem B1224287 : Blo 358757 1224287 := bstep (se 1 (by rfl) ⟨918215, by rfl⟩ : syracuseStep 1224287 = 1836431) B1836431
theorem B1159069 : Blo 358757 1159069 := bstep (se 3 (by rfl) ⟨217325, by rfl⟩ : syracuseStep 1159069 = 434651) B434651
theorem B864361 : Blo 358757 864361 := bstep (se 2 (by rfl) ⟨324135, by rfl⟩ : syracuseStep 864361 = 648271) B648271
theorem B2732291 : Blo 358757 2732291 := bstep (se 1 (by rfl) ⟨2049218, by rfl⟩ : syracuseStep 2732291 = 4098437) B4098437
theorem B1356257 : Blo 358757 1356257 := bstep (se 2 (by rfl) ⟨508596, by rfl⟩ : syracuseStep 1356257 = 1017193) B1017193
theorem B406111 : Blo 358757 406111 := bstep (se 1 (by rfl) ⟨304583, by rfl⟩ : syracuseStep 406111 = 609167) B609167
theorem B2307217 : Blo 358757 2307217 := bstep (se 2 (by rfl) ⟨865206, by rfl⟩ : syracuseStep 2307217 = 1730413) B1730413
theorem B6960401 : Blo 358757 6960401 := bstep (se 2 (by rfl) ⟨2610150, by rfl⟩ : syracuseStep 6960401 = 5220301) B5220301
theorem B407263 : Blo 358757 407263 := bstep (se 1 (by rfl) ⟨305447, by rfl⟩ : syracuseStep 407263 = 610895) B610895
theorem B538409 : Blo 358757 538409 := bstep (se 2 (by rfl) ⟨201903, by rfl⟩ : syracuseStep 538409 = 403807) B403807
theorem B538415 : Blo 358757 538415 := bstep (se 1 (by rfl) ⟨403811, by rfl⟩ : syracuseStep 538415 = 807623) B807623
theorem B440143 : Blo 358757 440143 := bstep (se 1 (by rfl) ⟨330107, by rfl⟩ : syracuseStep 440143 = 660215) B660215
theorem B1816829 : Blo 358757 1816829 := bstep (se 3 (by rfl) ⟨340655, by rfl⟩ : syracuseStep 1816829 = 681311) B681311
theorem B1128701 : Blo 358757 1128701 := bstep (se 3 (by rfl) ⟨211631, by rfl⟩ : syracuseStep 1128701 = 423263) B423263
theorem B538889 : Blo 358757 538889 := bstep (se 2 (by rfl) ⟨202083, by rfl⟩ : syracuseStep 538889 = 404167) B404167
theorem B407839 : Blo 358757 407839 := bstep (se 1 (by rfl) ⟨305879, by rfl⟩ : syracuseStep 407839 = 611759) B611759
theorem B538991 : Blo 358757 538991 := bstep (se 1 (by rfl) ⟨404243, by rfl⟩ : syracuseStep 538991 = 808487) B808487
theorem B539207 : Blo 358757 539207 := bstep (se 1 (by rfl) ⟨404405, by rfl⟩ : syracuseStep 539207 = 808811) B808811
theorem B539243 : Blo 358757 539243 := bstep (se 1 (by rfl) ⟨404432, by rfl⟩ : syracuseStep 539243 = 808865) B808865
theorem B539471 : Blo 358757 539471 := bstep (se 1 (by rfl) ⟨404603, by rfl⟩ : syracuseStep 539471 = 809207) B809207
theorem B4209515 : Blo 358757 4209515 := bstep (se 1 (by rfl) ⟨3157136, by rfl⟩ : syracuseStep 4209515 = 6314273) B6314273
theorem B1948535 : Blo 358757 1948535 := bstep (se 1 (by rfl) ⟨1461401, by rfl⟩ : syracuseStep 1948535 = 2922803) B2922803
theorem B1817639 : Blo 358757 1817639 := bstep (se 1 (by rfl) ⟨1363229, by rfl⟩ : syracuseStep 1817639 = 2726459) B2726459
theorem B539867 : Blo 358757 539867 := bstep (se 1 (by rfl) ⟨404900, by rfl⟩ : syracuseStep 539867 = 809801) B809801
theorem B540041 : Blo 358757 540041 := bstep (se 2 (by rfl) ⟨202515, by rfl⟩ : syracuseStep 540041 = 405031) B405031
theorem B3128777 : Blo 358757 3128777 := bstep (se 2 (by rfl) ⟨1173291, by rfl⟩ : syracuseStep 3128777 = 2346583) B2346583
theorem B769619 : Blo 358757 769619 := bstep (se 1 (by rfl) ⟨577214, by rfl⟩ : syracuseStep 769619 = 1154429) B1154429
theorem B5979793 : Blo 358757 5979793 := bstep (se 2 (by rfl) ⟨2242422, by rfl⟩ : syracuseStep 5979793 = 4484845) B4484845
theorem B540395 : Blo 358757 540395 := bstep (se 1 (by rfl) ⟨405296, by rfl⟩ : syracuseStep 540395 = 810593) B810593
theorem B3456827 : Blo 358757 3456827 := bstep (se 1 (by rfl) ⟨2592620, by rfl⟩ : syracuseStep 3456827 = 5185241) B5185241
theorem B540623 : Blo 358757 540623 := bstep (se 1 (by rfl) ⟨405467, by rfl⟩ : syracuseStep 540623 = 810935) B810935
theorem B2736179 : Blo 358757 2736179 := bstep (se 1 (by rfl) ⟨2052134, by rfl⟩ : syracuseStep 2736179 = 4104269) B4104269
theorem B541019 : Blo 358757 541019 := bstep (se 1 (by rfl) ⟨405764, by rfl⟩ : syracuseStep 541019 = 811529) B811529
theorem B606575 : Blo 358757 606575 := bstep (se 1 (by rfl) ⟨454931, by rfl⟩ : syracuseStep 606575 = 909863) B909863
theorem B2605537 : Blo 358757 2605537 := bstep (se 2 (by rfl) ⟨977076, by rfl⟩ : syracuseStep 2605537 = 1954153) B1954153
theorem B541247 : Blo 358757 541247 := bstep (se 1 (by rfl) ⟨405935, by rfl⟩ : syracuseStep 541247 = 811871) B811871
theorem B606791 : Blo 358757 606791 := bstep (se 1 (by rfl) ⟨455093, by rfl⟩ : syracuseStep 606791 = 910187) B910187
theorem B9290375 : Blo 358757 9290375 := bstep (se 1 (by rfl) ⟨6967781, by rfl⟩ : syracuseStep 9290375 = 13935563) B13935563
theorem B541367 : Blo 358757 541367 := bstep (se 1 (by rfl) ⟨406025, by rfl⟩ : syracuseStep 541367 = 812051) B812051
theorem B1983275 : Blo 358757 1983275 := bstep (se 1 (by rfl) ⟨1487456, by rfl⟩ : syracuseStep 1983275 = 2974913) B2974913
theorem B541595 : Blo 358757 541595 := bstep (se 1 (by rfl) ⟨406196, by rfl⟩ : syracuseStep 541595 = 812393) B812393
theorem B4441051 : Blo 358757 4441051 := bstep (se 1 (by rfl) ⟨3330788, by rfl⟩ : syracuseStep 4441051 = 6661577) B6661577
theorem B410599 : Blo 358757 410599 := bstep (se 1 (by rfl) ⟨307949, by rfl⟩ : syracuseStep 410599 = 615899) B615899
theorem B607223 : Blo 358757 607223 := bstep (se 1 (by rfl) ⟨455417, by rfl⟩ : syracuseStep 607223 = 910835) B910835
theorem B1819745 : Blo 358757 1819745 := bstep (se 2 (by rfl) ⟨682404, by rfl⟩ : syracuseStep 1819745 = 1364809) B1364809
theorem B6898891 : Blo 358757 6898891 := bstep (se 1 (by rfl) ⟨5174168, by rfl⟩ : syracuseStep 6898891 = 10348337) B10348337
theorem B541991 : Blo 358757 541991 := bstep (se 1 (by rfl) ⟨406493, by rfl⟩ : syracuseStep 541991 = 812987) B812987
theorem B542075 : Blo 358757 542075 := bstep (se 1 (by rfl) ⟨406556, by rfl⟩ : syracuseStep 542075 = 813113) B813113
theorem B2311577 : Blo 358757 2311577 := bstep (se 2 (by rfl) ⟨866841, by rfl⟩ : syracuseStep 2311577 = 1733683) B1733683
theorem B542201 : Blo 358757 542201 := bstep (se 2 (by rfl) ⟨203325, by rfl⟩ : syracuseStep 542201 = 406651) B406651
theorem B542303 : Blo 358757 542303 := bstep (se 1 (by rfl) ⟨406727, by rfl⟩ : syracuseStep 542303 = 813455) B813455
theorem B607979 : Blo 358757 607979 := bstep (se 1 (by rfl) ⟨455984, by rfl⟩ : syracuseStep 607979 = 911969) B911969
theorem B542519 : Blo 358757 542519 := bstep (se 1 (by rfl) ⟨406889, by rfl⟩ : syracuseStep 542519 = 813779) B813779
theorem B2934605 : Blo 358757 2934605 := bstep (se 3 (by rfl) ⟨550238, by rfl⟩ : syracuseStep 2934605 = 1100477) B1100477
theorem B542825 : Blo 358757 542825 := bstep (se 2 (by rfl) ⟨203559, by rfl⟩ : syracuseStep 542825 = 407119) B407119
theorem B870763 : Blo 358757 870763 := bstep (se 1 (by rfl) ⟨653072, by rfl⟩ : syracuseStep 870763 = 1306145) B1306145
theorem B6572431 : Blo 358757 6572431 := bstep (se 1 (by rfl) ⟨4929323, by rfl⟩ : syracuseStep 6572431 = 9858647) B9858647
theorem B543143 : Blo 358757 543143 := bstep (se 1 (by rfl) ⟨407357, by rfl⟩ : syracuseStep 543143 = 814715) B814715
theorem B543227 : Blo 358757 543227 := bstep (se 1 (by rfl) ⟨407420, by rfl⟩ : syracuseStep 543227 = 814841) B814841
theorem B543353 : Blo 358757 543353 := bstep (se 2 (by rfl) ⟨203757, by rfl⟩ : syracuseStep 543353 = 407515) B407515
theorem B543407 : Blo 358757 543407 := bstep (se 1 (by rfl) ⟨407555, by rfl⟩ : syracuseStep 543407 = 815111) B815111
theorem B608951 : Blo 358757 608951 := bstep (se 1 (by rfl) ⟨456713, by rfl⟩ : syracuseStep 608951 = 913427) B913427
theorem B772831 : Blo 358757 772831 := bstep (se 1 (by rfl) ⟨579623, by rfl⟩ : syracuseStep 772831 = 1159247) B1159247
theorem B543455 : Blo 358757 543455 := bstep (se 1 (by rfl) ⟨407591, by rfl⟩ : syracuseStep 543455 = 815183) B815183
theorem B1100699 : Blo 358757 1100699 := bstep (se 1 (by rfl) ⟨825524, by rfl⟩ : syracuseStep 1100699 = 1651049) B1651049
theorem B543719 : Blo 358757 543719 := bstep (se 1 (by rfl) ⟨407789, by rfl⟩ : syracuseStep 543719 = 815579) B815579
theorem B4410571 : Blo 358757 4410571 := bstep (se 1 (by rfl) ⟨3307928, by rfl⟩ : syracuseStep 4410571 = 6615857) B6615857
theorem B543977 : Blo 358757 543977 := bstep (se 2 (by rfl) ⟨203991, by rfl⟩ : syracuseStep 543977 = 407983) B407983
theorem B544031 : Blo 358757 544031 := bstep (se 1 (by rfl) ⟨408023, by rfl⟩ : syracuseStep 544031 = 816047) B816047
theorem B1822013 : Blo 358757 1822013 := bstep (se 3 (by rfl) ⟨341627, by rfl⟩ : syracuseStep 1822013 = 683255) B683255
theorem B1363337 : Blo 358757 1363337 := bstep (se 2 (by rfl) ⟨511251, by rfl⟩ : syracuseStep 1363337 = 1022503) B1022503
theorem B609673 : Blo 358757 609673 := bstep (se 2 (by rfl) ⟨228627, by rfl⟩ : syracuseStep 609673 = 457255) B457255
theorem B2805191 : Blo 358757 2805191 := bstep (se 1 (by rfl) ⟨2103893, by rfl⟩ : syracuseStep 2805191 = 4207787) B4207787
theorem B2477803 : Blo 358757 2477803 := bstep (se 1 (by rfl) ⟨1858352, by rfl⟩ : syracuseStep 2477803 = 3716705) B3716705
theorem B1101547 : Blo 358757 1101547 := bstep (se 1 (by rfl) ⟨826160, by rfl⟩ : syracuseStep 1101547 = 1652321) B1652321
theorem B610105 : Blo 358757 610105 := bstep (se 2 (by rfl) ⟨228789, by rfl⟩ : syracuseStep 610105 = 457579) B457579
theorem B773993 : Blo 358757 773993 := bstep (se 2 (by rfl) ⟨290247, by rfl⟩ : syracuseStep 773993 = 580495) B580495
theorem B2314241 : Blo 358757 2314241 := bstep (se 2 (by rfl) ⟨867840, by rfl⟩ : syracuseStep 2314241 = 1735681) B1735681
theorem B610409 : Blo 358757 610409 := bstep (se 2 (by rfl) ⟨228903, by rfl⟩ : syracuseStep 610409 = 457807) B457807
theorem B3461291 : Blo 358757 3461291 := bstep (se 1 (by rfl) ⟨2595968, by rfl⟩ : syracuseStep 3461291 = 5191937) B5191937
theorem B3920075 : Blo 358757 3920075 := bstep (se 1 (by rfl) ⟨2940056, by rfl⟩ : syracuseStep 3920075 = 5880113) B5880113
theorem B2740553 : Blo 358757 2740553 := bstep (se 2 (by rfl) ⟨1027707, by rfl⟩ : syracuseStep 2740553 = 2055415) B2055415
theorem B807335 : Blo 358757 807335 := bstep (se 1 (by rfl) ⟨605501, by rfl⟩ : syracuseStep 807335 = 1211003) B1211003
theorem B807443 : Blo 358757 807443 := bstep (se 1 (by rfl) ⟨605582, by rfl⟩ : syracuseStep 807443 = 1211165) B1211165
theorem B807497 : Blo 358757 807497 := bstep (se 2 (by rfl) ⟨302811, by rfl⟩ : syracuseStep 807497 = 605623) B605623
theorem B1725263 : Blo 358757 1725263 := bstep (se 1 (by rfl) ⟨1293947, by rfl⟩ : syracuseStep 1725263 = 2587895) B2587895
theorem B676687 : Blo 358757 676687 := bstep (se 1 (by rfl) ⟨507515, by rfl⟩ : syracuseStep 676687 = 1015031) B1015031
theorem B1954655 : Blo 358757 1954655 := bstep (se 1 (by rfl) ⟨1465991, by rfl⟩ : syracuseStep 1954655 = 2931983) B2931983
theorem B807911 : Blo 358757 807911 := bstep (se 1 (by rfl) ⟨605933, by rfl⟩ : syracuseStep 807911 = 1211867) B1211867
theorem B1299655 : Blo 358757 1299655 := bstep (se 1 (by rfl) ⟨974741, by rfl⟩ : syracuseStep 1299655 = 1949483) B1949483
theorem B1463539 : Blo 358757 1463539 := bstep (se 1 (by rfl) ⟨1097654, by rfl⟩ : syracuseStep 1463539 = 2195309) B2195309
theorem B513319 : Blo 358757 513319 := bstep (se 1 (by rfl) ⟨384989, by rfl⟩ : syracuseStep 513319 = 769979) B769979
theorem B578855 : Blo 358757 578855 := bstep (se 1 (by rfl) ⟨434141, by rfl⟩ : syracuseStep 578855 = 868283) B868283
theorem B808289 : Blo 358757 808289 := bstep (se 2 (by rfl) ⟨303108, by rfl⟩ : syracuseStep 808289 = 606217) B606217
theorem B808379 : Blo 358757 808379 := bstep (se 1 (by rfl) ⟨606284, by rfl⟩ : syracuseStep 808379 = 1212569) B1212569
theorem B611833 : Blo 358757 611833 := bstep (se 2 (by rfl) ⟨229437, by rfl⟩ : syracuseStep 611833 = 458875) B458875
theorem B808505 : Blo 358757 808505 := bstep (se 2 (by rfl) ⟨303189, by rfl⟩ : syracuseStep 808505 = 606379) B606379
theorem B1726109 : Blo 358757 1726109 := bstep (se 3 (by rfl) ⟨323645, by rfl⟩ : syracuseStep 1726109 = 647291) B647291
theorem B1824443 : Blo 358757 1824443 := bstep (se 1 (by rfl) ⟨1368332, by rfl⟩ : syracuseStep 1824443 = 2736665) B2736665
theorem B579259 : Blo 358757 579259 := bstep (se 1 (by rfl) ⟨434444, by rfl⟩ : syracuseStep 579259 = 868889) B868889
theorem B612103 : Blo 358757 612103 := bstep (se 1 (by rfl) ⟨459077, by rfl⟩ : syracuseStep 612103 = 918155) B918155
theorem B612137 : Blo 358757 612137 := bstep (se 2 (by rfl) ⟨229551, by rfl⟩ : syracuseStep 612137 = 459103) B459103
theorem B809171 : Blo 358757 809171 := bstep (se 1 (by rfl) ⟨606878, by rfl⟩ : syracuseStep 809171 = 1213757) B1213757
theorem B809225 : Blo 358757 809225 := bstep (se 2 (by rfl) ⟨303459, by rfl⟩ : syracuseStep 809225 = 606919) B606919
theorem B809441 : Blo 358757 809441 := bstep (se 2 (by rfl) ⟨303540, by rfl⟩ : syracuseStep 809441 = 607081) B607081
theorem B809747 : Blo 358757 809747 := bstep (se 1 (by rfl) ⟨607310, by rfl⟩ : syracuseStep 809747 = 1214621) B1214621
theorem B908111 : Blo 358757 908111 := bstep (se 1 (by rfl) ⟨681083, by rfl⟩ : syracuseStep 908111 = 1362167) B1362167
theorem B1367027 : Blo 358757 1367027 := bstep (se 1 (by rfl) ⟨1025270, by rfl⟩ : syracuseStep 1367027 = 2050541) B2050541
theorem B810107 : Blo 358757 810107 := bstep (se 1 (by rfl) ⟨607580, by rfl⟩ : syracuseStep 810107 = 1215161) B1215161
theorem B810233 : Blo 358757 810233 := bstep (se 2 (by rfl) ⟨303837, by rfl⟩ : syracuseStep 810233 = 607675) B607675
theorem B810377 : Blo 358757 810377 := bstep (se 2 (by rfl) ⟨303891, by rfl⟩ : syracuseStep 810377 = 607783) B607783
theorem B908759 : Blo 358757 908759 := bstep (se 1 (by rfl) ⟨681569, by rfl⟩ : syracuseStep 908759 = 1363139) B1363139
theorem B1727993 : Blo 358757 1727993 := bstep (se 2 (by rfl) ⟨647997, by rfl⟩ : syracuseStep 1727993 = 1295995) B1295995
theorem B810503 : Blo 358757 810503 := bstep (se 1 (by rfl) ⟨607877, by rfl⟩ : syracuseStep 810503 = 1215755) B1215755
theorem B1826387 : Blo 358757 1826387 := bstep (se 1 (by rfl) ⟨1369790, by rfl⟩ : syracuseStep 1826387 = 2739581) B2739581
theorem B2612897 : Blo 358757 2612897 := bstep (se 2 (by rfl) ⟨979836, by rfl⟩ : syracuseStep 2612897 = 1959673) B1959673
theorem B810683 : Blo 358757 810683 := bstep (se 1 (by rfl) ⟨608012, by rfl⟩ : syracuseStep 810683 = 1216025) B1216025
theorem B909103 : Blo 358757 909103 := bstep (se 1 (by rfl) ⟨681827, by rfl⟩ : syracuseStep 909103 = 1363655) B1363655
theorem B810809 : Blo 358757 810809 := bstep (se 2 (by rfl) ⟨304053, by rfl⟩ : syracuseStep 810809 = 608107) B608107
theorem B3694409 : Blo 358757 3694409 := bstep (se 2 (by rfl) ⟨1385403, by rfl⟩ : syracuseStep 3694409 = 2770807) B2770807
theorem B2187137 : Blo 358757 2187137 := bstep (se 2 (by rfl) ⟨820176, by rfl⟩ : syracuseStep 2187137 = 1640353) B1640353
theorem B811439 : Blo 358757 811439 := bstep (se 1 (by rfl) ⟨608579, by rfl⟩ : syracuseStep 811439 = 1217159) B1217159
theorem B909751 : Blo 358757 909751 := bstep (se 1 (by rfl) ⟨682313, by rfl⟩ : syracuseStep 909751 = 1364627) B1364627
theorem B6578633 : Blo 358757 6578633 := bstep (se 2 (by rfl) ⟨2466987, by rfl⟩ : syracuseStep 6578633 = 4933975) B4933975
theorem B811475 : Blo 358757 811475 := bstep (se 1 (by rfl) ⟨608606, by rfl⟩ : syracuseStep 811475 = 1217213) B1217213
theorem B811583 : Blo 358757 811583 := bstep (se 1 (by rfl) ⟨608687, by rfl⟩ : syracuseStep 811583 = 1217375) B1217375
theorem B1368697 : Blo 358757 1368697 := bstep (se 2 (by rfl) ⟨513261, by rfl⟩ : syracuseStep 1368697 = 1026523) B1026523
theorem B811691 : Blo 358757 811691 := bstep (se 1 (by rfl) ⟨608768, by rfl⟩ : syracuseStep 811691 = 1217537) B1217537
theorem B812231 : Blo 358757 812231 := bstep (se 1 (by rfl) ⟨609173, by rfl⟩ : syracuseStep 812231 = 1218347) B1218347
theorem B1533293 : Blo 358757 1533293 := bstep (se 3 (by rfl) ⟨287492, by rfl⟩ : syracuseStep 1533293 = 574985) B574985
theorem B812411 : Blo 358757 812411 := bstep (se 1 (by rfl) ⟨609308, by rfl⟩ : syracuseStep 812411 = 1218617) B1218617
theorem B812537 : Blo 358757 812537 := bstep (se 2 (by rfl) ⟨304701, by rfl⟩ : syracuseStep 812537 = 609403) B609403
theorem B812627 : Blo 358757 812627 := bstep (se 1 (by rfl) ⟨609470, by rfl⟩ : syracuseStep 812627 = 1218941) B1218941
theorem B3073625 : Blo 358757 3073625 := bstep (se 2 (by rfl) ⟨1152609, by rfl⟩ : syracuseStep 3073625 = 2305219) B2305219
theorem B812807 : Blo 358757 812807 := bstep (se 1 (by rfl) ⟨609605, by rfl⟩ : syracuseStep 812807 = 1219211) B1219211
theorem B911159 : Blo 358757 911159 := bstep (se 1 (by rfl) ⟨683369, by rfl⟩ : syracuseStep 911159 = 1366739) B1366739
theorem B583481 : Blo 358757 583481 := bstep (se 2 (by rfl) ⟨218805, by rfl⟩ : syracuseStep 583481 = 437611) B437611
theorem B1369943 : Blo 358757 1369943 := bstep (se 1 (by rfl) ⟨1027457, by rfl⟩ : syracuseStep 1369943 = 2054915) B2054915
theorem B911209 : Blo 358757 911209 := bstep (se 2 (by rfl) ⟨341703, by rfl⟩ : syracuseStep 911209 = 683407) B683407
theorem B3532679 : Blo 358757 3532679 := bstep (se 1 (by rfl) ⟨2649509, by rfl⟩ : syracuseStep 3532679 = 5299019) B5299019
theorem B126412973 : Blo 358757 126412973 := bstep (se 3 (by rfl) ⟨23702432, by rfl⟩ : syracuseStep 126412973 = 47404865) B47404865
theorem B2320649 : Blo 358757 2320649 := bstep (se 2 (by rfl) ⟨870243, by rfl⟩ : syracuseStep 2320649 = 1740487) B1740487
theorem B813419 : Blo 358757 813419 := bstep (se 1 (by rfl) ⟨610064, by rfl⟩ : syracuseStep 813419 = 1220129) B1220129
theorem B1829303 : Blo 358757 1829303 := bstep (se 1 (by rfl) ⟨1371977, by rfl⟩ : syracuseStep 1829303 = 2743955) B2743955
theorem B813563 : Blo 358757 813563 := bstep (se 1 (by rfl) ⟨610172, by rfl⟩ : syracuseStep 813563 = 1220345) B1220345
theorem B17885731 : Blo 358757 17885731 := bstep (se 1 (by rfl) ⟨13414298, by rfl⟩ : syracuseStep 17885731 = 26828597) B26828597
theorem B813689 : Blo 358757 813689 := bstep (se 2 (by rfl) ⟨305133, by rfl⟩ : syracuseStep 813689 = 610267) B610267
theorem B813743 : Blo 358757 813743 := bstep (se 1 (by rfl) ⟨610307, by rfl⟩ : syracuseStep 813743 = 1220615) B1220615
theorem B7269041 : Blo 358757 7269041 := bstep (se 2 (by rfl) ⟨2725890, by rfl⟩ : syracuseStep 7269041 = 5451781) B5451781
theorem B11168441 : Blo 358757 11168441 := bstep (se 2 (by rfl) ⟨4188165, by rfl⟩ : syracuseStep 11168441 = 8376331) B8376331
theorem B813815 : Blo 358757 813815 := bstep (se 1 (by rfl) ⟨610361, by rfl⟩ : syracuseStep 813815 = 1220723) B1220723
theorem B813995 : Blo 358757 813995 := bstep (se 1 (by rfl) ⟨610496, by rfl⟩ : syracuseStep 813995 = 1220993) B1220993
theorem B912617 : Blo 358757 912617 := bstep (se 2 (by rfl) ⟨342231, by rfl⟩ : syracuseStep 912617 = 684463) B684463
theorem B912779 : Blo 358757 912779 := bstep (se 1 (by rfl) ⟨684584, by rfl⟩ : syracuseStep 912779 = 1369169) B1369169
theorem B814535 : Blo 358757 814535 := bstep (se 1 (by rfl) ⟨610901, by rfl⟩ : syracuseStep 814535 = 1221803) B1221803
theorem B912991 : Blo 358757 912991 := bstep (se 1 (by rfl) ⟨684743, by rfl⟩ : syracuseStep 912991 = 1369487) B1369487
theorem B6254273 : Blo 358757 6254273 := bstep (se 2 (by rfl) ⟨2345352, by rfl⟩ : syracuseStep 6254273 = 4690705) B4690705
theorem B618281 : Blo 358757 618281 := bstep (se 2 (by rfl) ⟨231855, by rfl⟩ : syracuseStep 618281 = 463711) B463711
theorem B814895 : Blo 358757 814895 := bstep (se 1 (by rfl) ⟨611171, by rfl⟩ : syracuseStep 814895 = 1222343) B1222343
theorem B978743 : Blo 358757 978743 := bstep (se 1 (by rfl) ⟨734057, by rfl⟩ : syracuseStep 978743 = 1468115) B1468115
theorem B913619 : Blo 358757 913619 := bstep (se 1 (by rfl) ⟨685214, by rfl⟩ : syracuseStep 913619 = 1370429) B1370429
theorem B684379 : Blo 358757 684379 := bstep (se 1 (by rfl) ⟨513284, by rfl⟩ : syracuseStep 684379 = 1026569) B1026569
theorem B815471 : Blo 358757 815471 := bstep (se 1 (by rfl) ⟨611603, by rfl⟩ : syracuseStep 815471 = 1223207) B1223207
theorem B815543 : Blo 358757 815543 := bstep (se 1 (by rfl) ⟨611657, by rfl⟩ : syracuseStep 815543 = 1223315) B1223315
theorem B40104409 : Blo 358757 40104409 := bstep (se 2 (by rfl) ⟨15039153, by rfl⟩ : syracuseStep 40104409 = 30078307) B30078307
theorem B684607 : Blo 358757 684607 := bstep (se 1 (by rfl) ⟨513455, by rfl⟩ : syracuseStep 684607 = 1026911) B1026911
theorem B815687 : Blo 358757 815687 := bstep (se 1 (by rfl) ⟨611765, by rfl⟩ : syracuseStep 815687 = 1223531) B1223531
theorem B815723 : Blo 358757 815723 := bstep (se 1 (by rfl) ⟨611792, by rfl⟩ : syracuseStep 815723 = 1223585) B1223585
theorem B1831571 : Blo 358757 1831571 := bstep (se 1 (by rfl) ⟨1373678, by rfl⟩ : syracuseStep 1831571 = 2747357) B2747357
theorem B684767 : Blo 358757 684767 := bstep (se 1 (by rfl) ⟨513575, by rfl⟩ : syracuseStep 684767 = 1027151) B1027151
theorem B488171 : Blo 358757 488171 := bstep (se 1 (by rfl) ⟨366128, by rfl⟩ : syracuseStep 488171 = 732257) B732257
theorem B619343 : Blo 358757 619343 := bstep (se 1 (by rfl) ⟨464507, by rfl⟩ : syracuseStep 619343 = 929015) B929015
theorem B1733471 : Blo 358757 1733471 := bstep (se 1 (by rfl) ⟨1300103, by rfl⟩ : syracuseStep 1733471 = 2600207) B2600207
theorem B3076973 : Blo 358757 3076973 := bstep (se 3 (by rfl) ⟨576932, by rfl⟩ : syracuseStep 3076973 = 1153865) B1153865
theorem B652279 : Blo 358757 652279 := bstep (se 1 (by rfl) ⟨489209, by rfl⟩ : syracuseStep 652279 = 978419) B978419
theorem B816119 : Blo 358757 816119 := bstep (se 1 (by rfl) ⟨612089, by rfl⟩ : syracuseStep 816119 = 1224179) B1224179
theorem B685199 : Blo 358757 685199 := bstep (se 1 (by rfl) ⟨513899, by rfl⟩ : syracuseStep 685199 = 1027799) B1027799
theorem B685351 : Blo 358757 685351 := bstep (se 1 (by rfl) ⟨514013, by rfl⟩ : syracuseStep 685351 = 1028027) B1028027
theorem B685435 : Blo 358757 685435 := bstep (se 1 (by rfl) ⟨514076, by rfl⟩ : syracuseStep 685435 = 1028153) B1028153
theorem B1832381 : Blo 358757 1832381 := bstep (se 3 (by rfl) ⟨343571, by rfl⟩ : syracuseStep 1832381 = 687143) B687143
theorem B456187 : Blo 358757 456187 := bstep (se 1 (by rfl) ⟨342140, by rfl⟩ : syracuseStep 456187 = 684281) B684281
theorem B3471589 : Blo 358757 3471589 := bstep (se 4 (by rfl) ⟨325461, by rfl⟩ : syracuseStep 3471589 = 650923) B650923
theorem B358767 : Blo 358757 358767 := bstep (se 1 (by rfl) ⟨269075, by rfl⟩ : syracuseStep 358767 = 538151) B538151
theorem B358823 : Blo 358757 358823 := bstep (se 1 (by rfl) ⟨269117, by rfl⟩ : syracuseStep 358823 = 538235) B538235
theorem B915887 : Blo 358757 915887 := bstep (se 1 (by rfl) ⟨686915, by rfl⟩ : syracuseStep 915887 = 1373831) B1373831
theorem B457159 : Blo 358757 457159 := bstep (se 1 (by rfl) ⟨342869, by rfl⟩ : syracuseStep 457159 = 685739) B685739
theorem B358907 : Blo 358757 358907 := bstep (se 1 (by rfl) ⟨269180, by rfl⟩ : syracuseStep 358907 = 538361) B538361
theorem B358975 : Blo 358757 358975 := bstep (se 1 (by rfl) ⟨269231, by rfl⟩ : syracuseStep 358975 = 538463) B538463
theorem B358983 : Blo 358757 358983 := bstep (se 1 (by rfl) ⟨269237, by rfl⟩ : syracuseStep 358983 = 538475) B538475
theorem B359135 : Blo 358757 359135 := bstep (se 1 (by rfl) ⟨269351, by rfl⟩ : syracuseStep 359135 = 538703) B538703
theorem B359215 : Blo 358757 359215 := bstep (se 1 (by rfl) ⟨269411, by rfl⟩ : syracuseStep 359215 = 538823) B538823
theorem B359323 : Blo 358757 359323 := bstep (se 1 (by rfl) ⟨269492, by rfl⟩ : syracuseStep 359323 = 538985) B538985
theorem B359375 : Blo 358757 359375 := bstep (se 1 (by rfl) ⟨269531, by rfl⟩ : syracuseStep 359375 = 539063) B539063
theorem B359399 : Blo 358757 359399 := bstep (se 1 (by rfl) ⟨269549, by rfl⟩ : syracuseStep 359399 = 539099) B539099
theorem B7371899 : Blo 358757 7371899 := bstep (se 1 (by rfl) ⟨5528924, by rfl⟩ : syracuseStep 7371899 = 11057849) B11057849
theorem B359711 : Blo 358757 359711 := bstep (se 1 (by rfl) ⟨269783, by rfl⟩ : syracuseStep 359711 = 539567) B539567
theorem B359771 : Blo 358757 359771 := bstep (se 1 (by rfl) ⟨269828, by rfl⟩ : syracuseStep 359771 = 539657) B539657
theorem B458075 : Blo 358757 458075 := bstep (se 1 (by rfl) ⟨343556, by rfl⟩ : syracuseStep 458075 = 687113) B687113
theorem B359791 : Blo 358757 359791 := bstep (se 1 (by rfl) ⟨269843, by rfl⟩ : syracuseStep 359791 = 539687) B539687
theorem B916859 : Blo 358757 916859 := bstep (se 1 (by rfl) ⟨687644, by rfl⟩ : syracuseStep 916859 = 1375289) B1375289
theorem B359847 : Blo 358757 359847 := bstep (se 1 (by rfl) ⟨269885, by rfl⟩ : syracuseStep 359847 = 539771) B539771
theorem B359931 : Blo 358757 359931 := bstep (se 1 (by rfl) ⟨269948, by rfl⟩ : syracuseStep 359931 = 539897) B539897
theorem B359999 : Blo 358757 359999 := bstep (se 1 (by rfl) ⟨269999, by rfl⟩ : syracuseStep 359999 = 539999) B539999
theorem B360007 : Blo 358757 360007 := bstep (se 1 (by rfl) ⟨270005, by rfl⟩ : syracuseStep 360007 = 540011) B540011
theorem B2915921 : Blo 358757 2915921 := bstep (se 2 (by rfl) ⟨1093470, by rfl⟩ : syracuseStep 2915921 = 2186941) B2186941
theorem B917153 : Blo 358757 917153 := bstep (se 2 (by rfl) ⟨343932, by rfl⟩ : syracuseStep 917153 = 687865) B687865
theorem B360159 : Blo 358757 360159 := bstep (se 1 (by rfl) ⟨270119, by rfl⟩ : syracuseStep 360159 = 540239) B540239
theorem B360239 : Blo 358757 360239 := bstep (se 1 (by rfl) ⟨270179, by rfl⟩ : syracuseStep 360239 = 540359) B540359
theorem B458551 : Blo 358757 458551 := bstep (se 1 (by rfl) ⟨343913, by rfl⟩ : syracuseStep 458551 = 687827) B687827
theorem B360347 : Blo 358757 360347 := bstep (se 1 (by rfl) ⟨270260, by rfl⟩ : syracuseStep 360347 = 540521) B540521
theorem B360399 : Blo 358757 360399 := bstep (se 1 (by rfl) ⟨270299, by rfl⟩ : syracuseStep 360399 = 540599) B540599
theorem B360423 : Blo 358757 360423 := bstep (se 1 (by rfl) ⟨270317, by rfl⟩ : syracuseStep 360423 = 540635) B540635
theorem B10485811 : Blo 358757 10485811 := bstep (se 1 (by rfl) ⟨7864358, by rfl⟩ : syracuseStep 10485811 = 15728717) B15728717
theorem B360679 : Blo 358757 360679 := bstep (se 1 (by rfl) ⟨270509, by rfl⟩ : syracuseStep 360679 = 541019) B541019
theorem B360831 : Blo 358757 360831 := bstep (se 1 (by rfl) ⟨270623, by rfl⟩ : syracuseStep 360831 = 541247) B541247
theorem B3670447 : Blo 358757 3670447 := bstep (se 1 (by rfl) ⟨2752835, by rfl⟩ : syracuseStep 3670447 = 5505671) B5505671
theorem B6193583 : Blo 358757 6193583 := bstep (se 1 (by rfl) ⟨4645187, by rfl⟩ : syracuseStep 6193583 = 9290375) B9290375
theorem B360911 : Blo 358757 360911 := bstep (se 1 (by rfl) ⟨270683, by rfl⟩ : syracuseStep 360911 = 541367) B541367
theorem B917993 : Blo 358757 917993 := bstep (se 2 (by rfl) ⟨344247, by rfl⟩ : syracuseStep 917993 = 688495) B688495
theorem B1213001 : Blo 358757 1213001 := bstep (se 2 (by rfl) ⟨454875, by rfl⟩ : syracuseStep 1213001 = 909751) B909751
theorem B361063 : Blo 358757 361063 := bstep (se 1 (by rfl) ⟨270797, by rfl⟩ : syracuseStep 361063 = 541595) B541595
theorem B1213163 : Blo 358757 1213163 := bstep (se 1 (by rfl) ⟨909872, by rfl⟩ : syracuseStep 1213163 = 1819745) B1819745
theorem B361327 : Blo 358757 361327 := bstep (se 1 (by rfl) ⟨270995, by rfl⟩ : syracuseStep 361327 = 541991) B541991
theorem B5178269 : Blo 358757 5178269 := bstep (se 3 (by rfl) ⟨970925, by rfl⟩ : syracuseStep 5178269 = 1941851) B1941851
theorem B361383 : Blo 358757 361383 := bstep (se 1 (by rfl) ⟨271037, by rfl⟩ : syracuseStep 361383 = 542075) B542075
theorem B1541051 : Blo 358757 1541051 := bstep (se 1 (by rfl) ⟨1155788, by rfl⟩ : syracuseStep 1541051 = 2311577) B2311577
theorem B361467 : Blo 358757 361467 := bstep (se 1 (by rfl) ⟨271100, by rfl⟩ : syracuseStep 361467 = 542201) B542201
theorem B361535 : Blo 358757 361535 := bstep (se 1 (by rfl) ⟨271151, by rfl⟩ : syracuseStep 361535 = 542303) B542303
theorem B361679 : Blo 358757 361679 := bstep (se 1 (by rfl) ⟨271259, by rfl⟩ : syracuseStep 361679 = 542519) B542519
theorem B361883 : Blo 358757 361883 := bstep (se 1 (by rfl) ⟨271412, by rfl⟩ : syracuseStep 361883 = 542825) B542825
theorem B362095 : Blo 358757 362095 := bstep (se 1 (by rfl) ⟨271571, by rfl⟩ : syracuseStep 362095 = 543143) B543143
theorem B362151 : Blo 358757 362151 := bstep (se 1 (by rfl) ⟨271613, by rfl⟩ : syracuseStep 362151 = 543227) B543227
theorem B362235 : Blo 358757 362235 := bstep (se 1 (by rfl) ⟨271676, by rfl⟩ : syracuseStep 362235 = 543353) B543353
theorem B362271 : Blo 358757 362271 := bstep (se 1 (by rfl) ⟨271703, by rfl⟩ : syracuseStep 362271 = 543407) B543407
theorem B362303 : Blo 358757 362303 := bstep (se 1 (by rfl) ⟨271727, by rfl⟩ : syracuseStep 362303 = 543455) B543455
theorem B362479 : Blo 358757 362479 := bstep (se 1 (by rfl) ⟨271859, by rfl⟩ : syracuseStep 362479 = 543719) B543719
theorem B362651 : Blo 358757 362651 := bstep (se 1 (by rfl) ⟨271988, by rfl⟩ : syracuseStep 362651 = 543977) B543977
theorem B362687 : Blo 358757 362687 := bstep (se 1 (by rfl) ⟨272015, by rfl⟩ : syracuseStep 362687 = 544031) B544031
theorem B1214675 : Blo 358757 1214675 := bstep (se 1 (by rfl) ⟨911006, by rfl⟩ : syracuseStep 1214675 = 1822013) B1822013
theorem B1313063 : Blo 358757 1313063 := bstep (se 1 (by rfl) ⟨984797, by rfl⟩ : syracuseStep 1313063 = 1969595) B1969595
theorem B1870127 : Blo 358757 1870127 := bstep (se 1 (by rfl) ⟨1402595, by rfl⟩ : syracuseStep 1870127 = 2805191) B2805191
theorem B1214945 : Blo 358757 1214945 := bstep (se 2 (by rfl) ⟨455604, by rfl⟩ : syracuseStep 1214945 = 911209) B911209
theorem B13896197 : Blo 358757 13896197 := bstep (se 4 (by rfl) ⟨1302768, by rfl⟩ : syracuseStep 13896197 = 2605537) B2605537
theorem B1542827 : Blo 358757 1542827 := bstep (se 1 (by rfl) ⟨1157120, by rfl⟩ : syracuseStep 1542827 = 2314241) B2314241
theorem B5835995 : Blo 358757 5835995 := bstep (se 1 (by rfl) ⟨4376996, by rfl⟩ : syracuseStep 5835995 = 8753993) B8753993
theorem B1150175 : Blo 358757 1150175 := bstep (se 1 (by rfl) ⟨862631, by rfl⟩ : syracuseStep 1150175 = 1725263) B1725263
theorem B1150739 : Blo 358757 1150739 := bstep (se 1 (by rfl) ⟨863054, by rfl⟩ : syracuseStep 1150739 = 1726109) B1726109
theorem B1216295 : Blo 358757 1216295 := bstep (se 1 (by rfl) ⟨912221, by rfl⟩ : syracuseStep 1216295 = 1824443) B1824443
theorem B9277253 : Blo 358757 9277253 := bstep (se 4 (by rfl) ⟨869742, by rfl⟩ : syracuseStep 9277253 = 1739485) B1739485
theorem B1150841 : Blo 358757 1150841 := bstep (se 2 (by rfl) ⟨431565, by rfl⟩ : syracuseStep 1150841 = 863131) B863131
theorem B1380959 : Blo 358757 1380959 := bstep (se 1 (by rfl) ⟨1035719, by rfl⟩ : syracuseStep 1380959 = 2071439) B2071439
theorem B1217321 : Blo 358757 1217321 := bstep (se 2 (by rfl) ⟨456495, by rfl⟩ : syracuseStep 1217321 = 912991) B912991
theorem B1151995 : Blo 358757 1151995 := bstep (se 1 (by rfl) ⟨863996, by rfl⟩ : syracuseStep 1151995 = 1727993) B1727993
theorem B1217591 : Blo 358757 1217591 := bstep (se 1 (by rfl) ⟨913193, by rfl⟩ : syracuseStep 1217591 = 1826387) B1826387
theorem B1741931 : Blo 358757 1741931 := bstep (se 1 (by rfl) ⟨1306448, by rfl⟩ : syracuseStep 1741931 = 2612897) B2612897
theorem B1545425 : Blo 358757 1545425 := bstep (se 2 (by rfl) ⟨579534, by rfl⟩ : syracuseStep 1545425 = 1159069) B1159069
theorem B2462939 : Blo 358757 2462939 := bstep (se 1 (by rfl) ⟨1847204, by rfl⟩ : syracuseStep 2462939 = 3694409) B3694409
theorem B15832493 : Blo 358757 15832493 := bstep (se 3 (by rfl) ⟨2968592, by rfl⟩ : syracuseStep 15832493 = 5937185) B5937185
theorem B1152481 : Blo 358757 1152481 := bstep (se 2 (by rfl) ⟨432180, by rfl⟩ : syracuseStep 1152481 = 864361) B864361
theorem B6952715 : Blo 358757 6952715 := bstep (se 1 (by rfl) ⟨5214536, by rfl⟩ : syracuseStep 6952715 = 10429073) B10429073
theorem B1022195 : Blo 358757 1022195 := bstep (se 1 (by rfl) ⟨766646, by rfl⟩ : syracuseStep 1022195 = 1533293) B1533293
theorem B1547099 : Blo 358757 1547099 := bstep (se 1 (by rfl) ⟨1160324, by rfl⟩ : syracuseStep 1547099 = 2320649) B2320649
theorem B1219535 : Blo 358757 1219535 := bstep (se 1 (by rfl) ⟨914651, by rfl⟩ : syracuseStep 1219535 = 1829303) B1829303
theorem B7445627 : Blo 358757 7445627 := bstep (se 1 (by rfl) ⟨5584220, by rfl⟩ : syracuseStep 7445627 = 11168441) B11168441
theorem B3349991 : Blo 358757 3349991 := bstep (se 1 (by rfl) ⟨2512493, by rfl⟩ : syracuseStep 3349991 = 5024987) B5024987
theorem B925409 : Blo 358757 925409 := bstep (se 2 (by rfl) ⟨347028, by rfl⟩ : syracuseStep 925409 = 694057) B694057
theorem B4169515 : Blo 358757 4169515 := bstep (se 1 (by rfl) ⟨3127136, by rfl⟩ : syracuseStep 4169515 = 6254273) B6254273
theorem B4628785 : Blo 358757 4628785 := bstep (se 2 (by rfl) ⟨1735794, by rfl⟩ : syracuseStep 4628785 = 3471589) B3471589
theorem B1221047 : Blo 358757 1221047 := bstep (se 1 (by rfl) ⟨915785, by rfl⟩ : syracuseStep 1221047 = 1831571) B1831571
theorem B1155647 : Blo 358757 1155647 := bstep (se 1 (by rfl) ⟨866735, by rfl⟩ : syracuseStep 1155647 = 1733471) B1733471
theorem B1221533 : Blo 358757 1221533 := bstep (se 3 (by rfl) ⟨229037, by rfl⟩ : syracuseStep 1221533 = 458075) B458075
theorem B1221587 : Blo 358757 1221587 := bstep (se 1 (by rfl) ⟨916190, by rfl⟩ : syracuseStep 1221587 = 1832381) B1832381
theorem B3712229 : Blo 358757 3712229 := bstep (se 4 (by rfl) ⟨348021, by rfl⟩ : syracuseStep 3712229 = 696043) B696043
theorem B7973057 : Blo 358757 7973057 := bstep (se 2 (by rfl) ⟨2989896, by rfl⟩ : syracuseStep 7973057 = 5979793) B5979793
theorem B1943947 : Blo 358757 1943947 := bstep (se 1 (by rfl) ⟨1457960, by rfl⟩ : syracuseStep 1943947 = 2915921) B2915921
theorem B2304551 : Blo 358757 2304551 := bstep (se 1 (by rfl) ⟨1728413, by rfl⟩ : syracuseStep 2304551 = 3456827) B3456827
theorem B404383 : Blo 358757 404383 := bstep (se 1 (by rfl) ⟨303287, by rfl⟩ : syracuseStep 404383 = 606575) B606575
theorem B404527 : Blo 358757 404527 := bstep (se 1 (by rfl) ⟨303395, by rfl⟩ : syracuseStep 404527 = 606791) B606791
theorem B1223801 : Blo 358757 1223801 := bstep (se 2 (by rfl) ⟨458925, by rfl⟩ : syracuseStep 1223801 = 917851) B917851
theorem B1322183 : Blo 358757 1322183 := bstep (se 1 (by rfl) ⟨991637, by rfl⟩ : syracuseStep 1322183 = 1983275) B1983275
theorem B404815 : Blo 358757 404815 := bstep (se 1 (by rfl) ⟨303611, by rfl⟩ : syracuseStep 404815 = 607223) B607223
theorem B1224125 : Blo 358757 1224125 := bstep (se 3 (by rfl) ⟨229523, by rfl⟩ : syracuseStep 1224125 = 459047) B459047
theorem B405319 : Blo 358757 405319 := bstep (se 1 (by rfl) ⟨303989, by rfl⟩ : syracuseStep 405319 = 607979) B607979
theorem B8302445 : Blo 358757 8302445 := bstep (se 3 (by rfl) ⟨1556708, by rfl⟩ : syracuseStep 8302445 = 3113417) B3113417
theorem B405967 : Blo 358757 405967 := bstep (se 1 (by rfl) ⟨304475, by rfl⟩ : syracuseStep 405967 = 608951) B608951
theorem B733799 : Blo 358757 733799 := bstep (se 1 (by rfl) ⟨550349, by rfl⟩ : syracuseStep 733799 = 1100699) B1100699
theorem B10663001 : Blo 358757 10663001 := bstep (se 2 (by rfl) ⟨3998625, by rfl⟩ : syracuseStep 10663001 = 7997251) B7997251
theorem B767083 : Blo 358757 767083 := bstep (se 1 (by rfl) ⟨575312, by rfl⟩ : syracuseStep 767083 = 1150625) B1150625
theorem B406939 : Blo 358757 406939 := bstep (se 1 (by rfl) ⟨305204, by rfl⟩ : syracuseStep 406939 = 610409) B610409
theorem B2307527 : Blo 358757 2307527 := bstep (se 1 (by rfl) ⟨1730645, by rfl⟩ : syracuseStep 2307527 = 3461291) B3461291
theorem B4961735 : Blo 358757 4961735 := bstep (se 1 (by rfl) ⟨3721301, by rfl⟩ : syracuseStep 4961735 = 7442603) B7442603
theorem B538223 : Blo 358757 538223 := bstep (se 1 (by rfl) ⟨403667, by rfl⟩ : syracuseStep 538223 = 807335) B807335
theorem B538295 : Blo 358757 538295 := bstep (se 1 (by rfl) ⟨403721, by rfl⟩ : syracuseStep 538295 = 807443) B807443
theorem B1160887 : Blo 358757 1160887 := bstep (se 1 (by rfl) ⟨870665, by rfl⟩ : syracuseStep 1160887 = 1741331) B1741331
theorem B538331 : Blo 358757 538331 := bstep (se 1 (by rfl) ⟨403748, by rfl⟩ : syracuseStep 538331 = 807497) B807497
theorem B1161017 : Blo 358757 1161017 := bstep (se 2 (by rfl) ⟨435381, by rfl⟩ : syracuseStep 1161017 = 870763) B870763
theorem B8763241 : Blo 358757 8763241 := bstep (se 2 (by rfl) ⟨3286215, by rfl⟩ : syracuseStep 8763241 = 6572431) B6572431
theorem B538505 : Blo 358757 538505 := bstep (se 2 (by rfl) ⟨201939, by rfl⟩ : syracuseStep 538505 = 403879) B403879
theorem B538607 : Blo 358757 538607 := bstep (se 1 (by rfl) ⟨403955, by rfl⟩ : syracuseStep 538607 = 807911) B807911
theorem B538859 : Blo 358757 538859 := bstep (se 1 (by rfl) ⟨404144, by rfl⟩ : syracuseStep 538859 = 808289) B808289
theorem B538919 : Blo 358757 538919 := bstep (se 1 (by rfl) ⟨404189, by rfl⟩ : syracuseStep 538919 = 808379) B808379
theorem B539003 : Blo 358757 539003 := bstep (se 1 (by rfl) ⟨404252, by rfl⟩ : syracuseStep 539003 = 808505) B808505
theorem B408091 : Blo 358757 408091 := bstep (se 1 (by rfl) ⟨306068, by rfl⟩ : syracuseStep 408091 = 612137) B612137
theorem B1456697 : Blo 358757 1456697 := bstep (se 2 (by rfl) ⟨546261, by rfl⟩ : syracuseStep 1456697 = 1092523) B1092523
theorem B539273 : Blo 358757 539273 := bstep (se 2 (by rfl) ⟨202227, by rfl⟩ : syracuseStep 539273 = 404455) B404455
theorem B1456793 : Blo 358757 1456793 := bstep (se 2 (by rfl) ⟨546297, by rfl⟩ : syracuseStep 1456793 = 1092595) B1092595
theorem B539447 : Blo 358757 539447 := bstep (se 1 (by rfl) ⟨404585, by rfl⟩ : syracuseStep 539447 = 809171) B809171
theorem B539483 : Blo 358757 539483 := bstep (se 1 (by rfl) ⟨404612, by rfl⟩ : syracuseStep 539483 = 809225) B809225
theorem B5880761 : Blo 358757 5880761 := bstep (se 2 (by rfl) ⟨2205285, by rfl⟩ : syracuseStep 5880761 = 4410571) B4410571
theorem B539627 : Blo 358757 539627 := bstep (se 1 (by rfl) ⟨404720, by rfl⟩ : syracuseStep 539627 = 809441) B809441
theorem B539831 : Blo 358757 539831 := bstep (se 1 (by rfl) ⟨404873, by rfl⟩ : syracuseStep 539831 = 809747) B809747
theorem B605407 : Blo 358757 605407 := bstep (se 1 (by rfl) ⟨454055, by rfl⟩ : syracuseStep 605407 = 908111) B908111
theorem B1948967 : Blo 358757 1948967 := bstep (se 1 (by rfl) ⟨1461725, by rfl⟩ : syracuseStep 1948967 = 2923451) B2923451
theorem B540071 : Blo 358757 540071 := bstep (se 1 (by rfl) ⟨405053, by rfl⟩ : syracuseStep 540071 = 810107) B810107
theorem B1555949 : Blo 358757 1555949 := bstep (se 3 (by rfl) ⟨291740, by rfl⟩ : syracuseStep 1555949 = 583481) B583481
theorem B540155 : Blo 358757 540155 := bstep (se 1 (by rfl) ⟨405116, by rfl⟩ : syracuseStep 540155 = 810233) B810233
theorem B540251 : Blo 358757 540251 := bstep (se 1 (by rfl) ⟨405188, by rfl⟩ : syracuseStep 540251 = 810377) B810377
theorem B605839 : Blo 358757 605839 := bstep (se 1 (by rfl) ⟨454379, by rfl⟩ : syracuseStep 605839 = 908759) B908759
theorem B540335 : Blo 358757 540335 := bstep (se 1 (by rfl) ⟨405251, by rfl⟩ : syracuseStep 540335 = 810503) B810503
theorem B540455 : Blo 358757 540455 := bstep (se 1 (by rfl) ⟨405341, by rfl⟩ : syracuseStep 540455 = 810683) B810683
theorem B540539 : Blo 358757 540539 := bstep (se 1 (by rfl) ⟨405404, by rfl⟩ : syracuseStep 540539 = 810809) B810809
theorem B1458091 : Blo 358757 1458091 := bstep (se 1 (by rfl) ⟨1093568, by rfl⟩ : syracuseStep 1458091 = 2187137) B2187137
theorem B1228733 : Blo 358757 1228733 := bstep (se 3 (by rfl) ⟨230387, by rfl⟩ : syracuseStep 1228733 = 460775) B460775
theorem B7979147 : Blo 358757 7979147 := bstep (se 1 (by rfl) ⟨5984360, by rfl⟩ : syracuseStep 7979147 = 11968721) B11968721
theorem B540959 : Blo 358757 540959 := bstep (se 1 (by rfl) ⟨405719, by rfl⟩ : syracuseStep 540959 = 811439) B811439
theorem B540983 : Blo 358757 540983 := bstep (se 1 (by rfl) ⟨405737, by rfl⟩ : syracuseStep 540983 = 811475) B811475
theorem B541055 : Blo 358757 541055 := bstep (se 1 (by rfl) ⟨405791, by rfl⟩ : syracuseStep 541055 = 811583) B811583
theorem B541127 : Blo 358757 541127 := bstep (se 1 (by rfl) ⟨405845, by rfl⟩ : syracuseStep 541127 = 811691) B811691
theorem B4113017 : Blo 358757 4113017 := bstep (se 2 (by rfl) ⟨1542381, by rfl⟩ : syracuseStep 4113017 = 3084763) B3084763
theorem B541481 : Blo 358757 541481 := bstep (se 2 (by rfl) ⟨203055, by rfl⟩ : syracuseStep 541481 = 406111) B406111
theorem B541487 : Blo 358757 541487 := bstep (se 1 (by rfl) ⟨406115, by rfl⟩ : syracuseStep 541487 = 812231) B812231
theorem B541607 : Blo 358757 541607 := bstep (se 1 (by rfl) ⟨406205, by rfl⟩ : syracuseStep 541607 = 812411) B812411
theorem B541691 : Blo 358757 541691 := bstep (se 1 (by rfl) ⟨406268, by rfl⟩ : syracuseStep 541691 = 812537) B812537
theorem B6931493 : Blo 358757 6931493 := bstep (se 4 (by rfl) ⟨649827, by rfl⟩ : syracuseStep 6931493 = 1299655) B1299655
theorem B541751 : Blo 358757 541751 := bstep (se 1 (by rfl) ⟨406313, by rfl⟩ : syracuseStep 541751 = 812627) B812627
theorem B2049083 : Blo 358757 2049083 := bstep (se 1 (by rfl) ⟨1536812, by rfl⟩ : syracuseStep 2049083 = 3073625) B3073625
theorem B902249 : Blo 358757 902249 := bstep (se 2 (by rfl) ⟨338343, by rfl⟩ : syracuseStep 902249 = 676687) B676687
theorem B541871 : Blo 358757 541871 := bstep (se 1 (by rfl) ⟨406403, by rfl⟩ : syracuseStep 541871 = 812807) B812807
theorem B607439 : Blo 358757 607439 := bstep (se 1 (by rfl) ⟨455579, by rfl⟩ : syracuseStep 607439 = 911159) B911159
theorem B1819907 : Blo 358757 1819907 := bstep (se 1 (by rfl) ⟨1364930, by rfl⟩ : syracuseStep 1819907 = 2729861) B2729861
theorem B869705 : Blo 358757 869705 := bstep (se 2 (by rfl) ⟨326139, by rfl⟩ : syracuseStep 869705 = 652279) B652279
theorem B542279 : Blo 358757 542279 := bstep (se 1 (by rfl) ⟨406709, by rfl⟩ : syracuseStep 542279 = 813419) B813419
theorem B1951385 : Blo 358757 1951385 := bstep (se 2 (by rfl) ⟨731769, by rfl⟩ : syracuseStep 1951385 = 1463539) B1463539
theorem B542375 : Blo 358757 542375 := bstep (se 1 (by rfl) ⟨406781, by rfl⟩ : syracuseStep 542375 = 813563) B813563
theorem B542459 : Blo 358757 542459 := bstep (se 1 (by rfl) ⟨406844, by rfl⟩ : syracuseStep 542459 = 813689) B813689
theorem B542495 : Blo 358757 542495 := bstep (se 1 (by rfl) ⟨406871, by rfl⟩ : syracuseStep 542495 = 813743) B813743
theorem B19384109 : Blo 358757 19384109 := bstep (se 3 (by rfl) ⟨3634520, by rfl⟩ : syracuseStep 19384109 = 7269041) B7269041
theorem B542543 : Blo 358757 542543 := bstep (se 1 (by rfl) ⟨406907, by rfl⟩ : syracuseStep 542543 = 813815) B813815
theorem B542663 : Blo 358757 542663 := bstep (se 1 (by rfl) ⟨406997, by rfl⟩ : syracuseStep 542663 = 813995) B813995
theorem B608249 : Blo 358757 608249 := bstep (se 2 (by rfl) ⟨228093, by rfl⟩ : syracuseStep 608249 = 456187) B456187
theorem B608411 : Blo 358757 608411 := bstep (se 1 (by rfl) ⟨456308, by rfl⟩ : syracuseStep 608411 = 912617) B912617
theorem B575723 : Blo 358757 575723 := bstep (se 1 (by rfl) ⟨431792, by rfl⟩ : syracuseStep 575723 = 863585) B863585
theorem B772345 : Blo 358757 772345 := bstep (se 2 (by rfl) ⟨289629, by rfl⟩ : syracuseStep 772345 = 579259) B579259
theorem B608519 : Blo 358757 608519 := bstep (se 1 (by rfl) ⟨456389, by rfl⟩ : syracuseStep 608519 = 912779) B912779
theorem B543017 : Blo 358757 543017 := bstep (se 2 (by rfl) ⟨203631, by rfl⟩ : syracuseStep 543017 = 407263) B407263
theorem B543023 : Blo 358757 543023 := bstep (se 1 (by rfl) ⟨407267, by rfl⟩ : syracuseStep 543023 = 814535) B814535
theorem B412187 : Blo 358757 412187 := bstep (se 1 (by rfl) ⟨309140, by rfl⟩ : syracuseStep 412187 = 618281) B618281
theorem B543263 : Blo 358757 543263 := bstep (se 1 (by rfl) ⟨407447, by rfl⟩ : syracuseStep 543263 = 814895) B814895
theorem B609079 : Blo 358757 609079 := bstep (se 1 (by rfl) ⟨456809, by rfl⟩ : syracuseStep 609079 = 913619) B913619
theorem B1821527 : Blo 358757 1821527 := bstep (se 1 (by rfl) ⟨1366145, by rfl⟩ : syracuseStep 1821527 = 2732291) B2732291
theorem B543647 : Blo 358757 543647 := bstep (se 1 (by rfl) ⟨407735, by rfl⟩ : syracuseStep 543647 = 815471) B815471
theorem B543695 : Blo 358757 543695 := bstep (se 1 (by rfl) ⟨407771, by rfl⟩ : syracuseStep 543695 = 815543) B815543
theorem B904171 : Blo 358757 904171 := bstep (se 1 (by rfl) ⟨678128, by rfl⟩ : syracuseStep 904171 = 1356257) B1356257
theorem B543785 : Blo 358757 543785 := bstep (se 2 (by rfl) ⟨203919, by rfl⟩ : syracuseStep 543785 = 407839) B407839
theorem B543791 : Blo 358757 543791 := bstep (se 1 (by rfl) ⟨407843, by rfl⟩ : syracuseStep 543791 = 815687) B815687
theorem B543815 : Blo 358757 543815 := bstep (se 1 (by rfl) ⟨407861, by rfl⟩ : syracuseStep 543815 = 815723) B815723
theorem B412895 : Blo 358757 412895 := bstep (se 1 (by rfl) ⟨309671, by rfl⟩ : syracuseStep 412895 = 619343) B619343
theorem B2051315 : Blo 358757 2051315 := bstep (se 1 (by rfl) ⟨1538486, by rfl⟩ : syracuseStep 2051315 = 3076973) B3076973
theorem B609545 : Blo 358757 609545 := bstep (se 2 (by rfl) ⟨228579, by rfl⟩ : syracuseStep 609545 = 457159) B457159
theorem B544079 : Blo 358757 544079 := bstep (se 1 (by rfl) ⟨408059, by rfl⟩ : syracuseStep 544079 = 816119) B816119
theorem B4640267 : Blo 358757 4640267 := bstep (se 1 (by rfl) ⟨3480200, by rfl⟩ : syracuseStep 4640267 = 6960401) B6960401
theorem B2936681 : Blo 358757 2936681 := bstep (se 2 (by rfl) ⟨1101255, by rfl⟩ : syracuseStep 2936681 = 2202511) B2202511
theorem B2052317 : Blo 358757 2052317 := bstep (se 3 (by rfl) ⟨384809, by rfl⟩ : syracuseStep 2052317 = 769619) B769619
theorem B610591 : Blo 358757 610591 := bstep (se 1 (by rfl) ⟨457943, by rfl⟩ : syracuseStep 610591 = 915887) B915887
theorem B2347429 : Blo 358757 2347429 := bstep (se 4 (by rfl) ⟨220071, by rfl⟩ : syracuseStep 2347429 = 440143) B440143
theorem B2806343 : Blo 358757 2806343 := bstep (se 1 (by rfl) ⟨2104757, by rfl⟩ : syracuseStep 2806343 = 4209515) B4209515
theorem B1299023 : Blo 358757 1299023 := bstep (se 1 (by rfl) ⟨974267, by rfl⟩ : syracuseStep 1299023 = 1948535) B1948535
theorem B2609981 : Blo 358757 2609981 := bstep (se 3 (by rfl) ⟨489371, by rfl⟩ : syracuseStep 2609981 = 978743) B978743
theorem B611239 : Blo 358757 611239 := bstep (se 1 (by rfl) ⟨458429, by rfl⟩ : syracuseStep 611239 = 916859) B916859
theorem B2085851 : Blo 358757 2085851 := bstep (se 1 (by rfl) ⟨1564388, by rfl⟩ : syracuseStep 2085851 = 3128777) B3128777
theorem B611401 : Blo 358757 611401 := bstep (se 2 (by rfl) ⟨229275, by rfl⟩ : syracuseStep 611401 = 458551) B458551
theorem B611435 : Blo 358757 611435 := bstep (se 1 (by rfl) ⟨458576, by rfl⟩ : syracuseStep 611435 = 917153) B917153
theorem B1824119 : Blo 358757 1824119 := bstep (se 1 (by rfl) ⟨1368089, by rfl⟩ : syracuseStep 1824119 = 2736179) B2736179
theorem B2545121 : Blo 358757 2545121 := bstep (se 2 (by rfl) ⟨954420, by rfl⟩ : syracuseStep 2545121 = 1908841) B1908841
theorem B808631 : Blo 358757 808631 := bstep (se 1 (by rfl) ⟨606473, by rfl⟩ : syracuseStep 808631 = 1212947) B1212947
theorem B2316215 : Blo 358757 2316215 := bstep (se 1 (by rfl) ⟨1737161, by rfl⟩ : syracuseStep 2316215 = 3474323) B3474323
theorem B2316239 : Blo 358757 2316239 := bstep (se 1 (by rfl) ⟨1737179, by rfl⟩ : syracuseStep 2316239 = 3474359) B3474359
theorem B1824929 : Blo 358757 1824929 := bstep (se 2 (by rfl) ⟨684348, by rfl⟩ : syracuseStep 1824929 = 1368697) B1368697
theorem B1956403 : Blo 358757 1956403 := bstep (se 1 (by rfl) ⟨1467302, by rfl⟩ : syracuseStep 1956403 = 2934605) B2934605
theorem B547465 : Blo 358757 547465 := bstep (se 2 (by rfl) ⟨205299, by rfl⟩ : syracuseStep 547465 = 410599) B410599
theorem B29547341 : Blo 358757 29547341 := bstep (se 3 (by rfl) ⟨5540126, by rfl⟩ : syracuseStep 29547341 = 11080253) B11080253
theorem B809819 : Blo 358757 809819 := bstep (se 1 (by rfl) ⟨607364, by rfl⟩ : syracuseStep 809819 = 1214729) B1214729
theorem B9198521 : Blo 358757 9198521 := bstep (se 2 (by rfl) ⟨3449445, by rfl⟩ : syracuseStep 9198521 = 6898891) B6898891
theorem B1367225 : Blo 358757 1367225 := bstep (se 2 (by rfl) ⟨512709, by rfl⟩ : syracuseStep 1367225 = 1025419) B1025419
theorem B1301789 : Blo 358757 1301789 := bstep (se 3 (by rfl) ⟨244085, by rfl⟩ : syracuseStep 1301789 = 488171) B488171
theorem B1662439 : Blo 358757 1662439 := bstep (se 1 (by rfl) ⟨1246829, by rfl⟩ : syracuseStep 1662439 = 2493659) B2493659
theorem B2055689 : Blo 358757 2055689 := bstep (se 2 (by rfl) ⟨770883, by rfl⟩ : syracuseStep 2055689 = 1541767) B1541767
theorem B810575 : Blo 358757 810575 := bstep (se 1 (by rfl) ⟨607931, by rfl⟩ : syracuseStep 810575 = 1215863) B1215863
theorem B908891 : Blo 358757 908891 := bstep (se 1 (by rfl) ⟨681668, by rfl⟩ : syracuseStep 908891 = 1363337) B1363337
theorem B1728647 : Blo 358757 1728647 := bstep (se 1 (by rfl) ⟨1296485, by rfl⟩ : syracuseStep 1728647 = 2592971) B2592971
theorem B2613383 : Blo 358757 2613383 := bstep (se 1 (by rfl) ⟨1960037, by rfl⟩ : syracuseStep 2613383 = 3920075) B3920075
theorem B1827035 : Blo 358757 1827035 := bstep (se 1 (by rfl) ⟨1370276, by rfl⟩ : syracuseStep 1827035 = 2740553) B2740553
theorem B811295 : Blo 358757 811295 := bstep (se 1 (by rfl) ⟨608471, by rfl⟩ : syracuseStep 811295 = 1216943) B1216943
theorem B1106273 : Blo 358757 1106273 := bstep (se 2 (by rfl) ⟨414852, by rfl⟩ : syracuseStep 1106273 = 829705) B829705
theorem B1827197 : Blo 358757 1827197 := bstep (se 3 (by rfl) ⟨342599, by rfl⟩ : syracuseStep 1827197 = 685199) B685199
theorem B1303103 : Blo 358757 1303103 := bstep (se 1 (by rfl) ⟨977327, by rfl⟩ : syracuseStep 1303103 = 1954655) B1954655
theorem B23847641 : Blo 358757 23847641 := bstep (se 2 (by rfl) ⟨8942865, by rfl⟩ : syracuseStep 23847641 = 17885731) B17885731
theorem B615215 : Blo 358757 615215 := bstep (se 1 (by rfl) ⟨461411, by rfl⟩ : syracuseStep 615215 = 922823) B922823
theorem B385903 : Blo 358757 385903 := bstep (se 1 (by rfl) ⟨289427, by rfl⟩ : syracuseStep 385903 = 578855) B578855
theorem B811943 : Blo 358757 811943 := bstep (se 1 (by rfl) ⟨608957, by rfl⟩ : syracuseStep 811943 = 1217915) B1217915
theorem B3072977 : Blo 358757 3072977 := bstep (se 2 (by rfl) ⟨1152366, by rfl⟩ : syracuseStep 3072977 = 2304733) B2304733
theorem B549995 : Blo 358757 549995 := bstep (se 1 (by rfl) ⟨412496, by rfl⟩ : syracuseStep 549995 = 824993) B824993
theorem B4121765 : Blo 358757 4121765 := bstep (se 4 (by rfl) ⟨386415, by rfl⟩ : syracuseStep 4121765 = 772831) B772831
theorem B681691 : Blo 358757 681691 := bstep (se 1 (by rfl) ⟨511268, by rfl⟩ : syracuseStep 681691 = 1022537) B1022537
theorem B812879 : Blo 358757 812879 := bstep (se 1 (by rfl) ⟨609659, by rfl⟩ : syracuseStep 812879 = 1219319) B1219319
theorem B812897 : Blo 358757 812897 := bstep (se 2 (by rfl) ⟨304836, by rfl⟩ : syracuseStep 812897 = 609673) B609673
theorem B911351 : Blo 358757 911351 := bstep (se 1 (by rfl) ⟨683513, by rfl⟩ : syracuseStep 911351 = 1367027) B1367027
theorem B4679993 : Blo 358757 4679993 := bstep (se 2 (by rfl) ⟨1754997, by rfl⟩ : syracuseStep 4679993 = 3509995) B3509995
theorem B3303737 : Blo 358757 3303737 := bstep (se 2 (by rfl) ⟨1238901, by rfl⟩ : syracuseStep 3303737 = 2477803) B2477803
theorem B1468729 : Blo 358757 1468729 := bstep (se 2 (by rfl) ⟨550773, by rfl⟩ : syracuseStep 1468729 = 1101547) B1101547
theorem B813473 : Blo 358757 813473 := bstep (se 2 (by rfl) ⟨305052, by rfl⟩ : syracuseStep 813473 = 610105) B610105
theorem B23685605 : Blo 358757 23685605 := bstep (se 4 (by rfl) ⟨2220525, by rfl⟩ : syracuseStep 23685605 = 4441051) B4441051
theorem B2779643 : Blo 358757 2779643 := bstep (se 1 (by rfl) ⟨2084732, by rfl⟩ : syracuseStep 2779643 = 4169465) B4169465
theorem B813599 : Blo 358757 813599 := bstep (se 1 (by rfl) ⟨610199, by rfl⟩ : syracuseStep 813599 = 1220399) B1220399
theorem B4385755 : Blo 358757 4385755 := bstep (se 1 (by rfl) ⟨3289316, by rfl⟩ : syracuseStep 4385755 = 6578633) B6578633
theorem B912505 : Blo 358757 912505 := bstep (se 2 (by rfl) ⟨342189, by rfl⟩ : syracuseStep 912505 = 684379) B684379
theorem B53472545 : Blo 358757 53472545 := bstep (se 2 (by rfl) ⟨20052204, by rfl⟩ : syracuseStep 53472545 = 40104409) B40104409
theorem B3009869 : Blo 358757 3009869 := bstep (se 3 (by rfl) ⟨564350, by rfl⟩ : syracuseStep 3009869 = 1128701) B1128701
theorem B2059607 : Blo 358757 2059607 := bstep (se 1 (by rfl) ⟨1544705, by rfl⟩ : syracuseStep 2059607 = 3089411) B3089411
theorem B912809 : Blo 358757 912809 := bstep (se 2 (by rfl) ⟨342303, by rfl⟩ : syracuseStep 912809 = 684607) B684607
theorem B683795 : Blo 358757 683795 := bstep (se 1 (by rfl) ⟨512846, by rfl⟩ : syracuseStep 683795 = 1025693) B1025693
theorem B913295 : Blo 358757 913295 := bstep (se 1 (by rfl) ⟨684971, by rfl⟩ : syracuseStep 913295 = 1369943) B1369943
theorem B815003 : Blo 358757 815003 := bstep (se 1 (by rfl) ⟨611252, by rfl⟩ : syracuseStep 815003 = 1222505) B1222505
theorem B2355119 : Blo 358757 2355119 := bstep (se 1 (by rfl) ⟨1766339, by rfl⟩ : syracuseStep 2355119 = 3532679) B3532679
theorem B84275315 : Blo 358757 84275315 := bstep (se 1 (by rfl) ⟨63206486, by rfl⟩ : syracuseStep 84275315 = 126412973) B126412973
theorem B815291 : Blo 358757 815291 := bstep (se 1 (by rfl) ⟨611468, by rfl⟩ : syracuseStep 815291 = 1222937) B1222937
theorem B3076289 : Blo 358757 3076289 := bstep (se 2 (by rfl) ⟨1153608, by rfl⟩ : syracuseStep 3076289 = 2307217) B2307217
theorem B684425 : Blo 358757 684425 := bstep (se 2 (by rfl) ⟨256659, by rfl⟩ : syracuseStep 684425 = 513319) B513319
theorem B913801 : Blo 358757 913801 := bstep (se 2 (by rfl) ⟨342675, by rfl⟩ : syracuseStep 913801 = 685351) B685351
theorem B913913 : Blo 358757 913913 := bstep (se 2 (by rfl) ⟨342717, by rfl⟩ : syracuseStep 913913 = 685435) B685435
theorem B10711601 : Blo 358757 10711601 := bstep (se 2 (by rfl) ⟨4016850, by rfl⟩ : syracuseStep 10711601 = 8033701) B8033701
theorem B815777 : Blo 358757 815777 := bstep (se 2 (by rfl) ⟨305916, by rfl⟩ : syracuseStep 815777 = 611833) B611833
theorem B816137 : Blo 358757 816137 := bstep (se 2 (by rfl) ⟨306051, by rfl⟩ : syracuseStep 816137 = 612103) B612103
theorem B816191 : Blo 358757 816191 := bstep (se 1 (by rfl) ⟨612143, by rfl⟩ : syracuseStep 816191 = 1224287) B1224287
theorem B456511 : Blo 358757 456511 := bstep (se 1 (by rfl) ⟨342383, by rfl⟩ : syracuseStep 456511 = 684767) B684767
theorem B1538281 : Blo 358757 1538281 := bstep (se 2 (by rfl) ⟨576855, by rfl⟩ : syracuseStep 1538281 = 1153711) B1153711
theorem B358939 : Blo 358757 358939 := bstep (se 1 (by rfl) ⟨269204, by rfl⟩ : syracuseStep 358939 = 538409) B538409
theorem B358943 : Blo 358757 358943 := bstep (se 1 (by rfl) ⟨269207, by rfl⟩ : syracuseStep 358943 = 538415) B538415
theorem B1211219 : Blo 358757 1211219 := bstep (se 1 (by rfl) ⟨908414, by rfl⟩ : syracuseStep 1211219 = 1816829) B1816829
theorem B359259 : Blo 358757 359259 := bstep (se 1 (by rfl) ⟨269444, by rfl⟩ : syracuseStep 359259 = 538889) B538889
theorem B4914053 : Blo 358757 4914053 := bstep (se 4 (by rfl) ⟨460692, by rfl⟩ : syracuseStep 4914053 = 921385) B921385
theorem B359327 : Blo 358757 359327 := bstep (se 1 (by rfl) ⟨269495, by rfl⟩ : syracuseStep 359327 = 538991) B538991
theorem B359471 : Blo 358757 359471 := bstep (se 1 (by rfl) ⟨269603, by rfl⟩ : syracuseStep 359471 = 539207) B539207
theorem B359495 : Blo 358757 359495 := bstep (se 1 (by rfl) ⟨269621, by rfl⟩ : syracuseStep 359495 = 539243) B539243
theorem B359647 : Blo 358757 359647 := bstep (se 1 (by rfl) ⟨269735, by rfl⟩ : syracuseStep 359647 = 539471) B539471
theorem B1211759 : Blo 358757 1211759 := bstep (se 1 (by rfl) ⟨908819, by rfl⟩ : syracuseStep 1211759 = 1817639) B1817639
theorem B4914599 : Blo 358757 4914599 := bstep (se 1 (by rfl) ⟨3685949, by rfl⟩ : syracuseStep 4914599 = 7371899) B7371899
theorem B359911 : Blo 358757 359911 := bstep (se 1 (by rfl) ⟨269933, by rfl⟩ : syracuseStep 359911 = 539867) B539867
theorem B360027 : Blo 358757 360027 := bstep (se 1 (by rfl) ⟨270020, by rfl⟩ : syracuseStep 360027 = 540041) B540041
theorem B2063981 : Blo 358757 2063981 := bstep (se 3 (by rfl) ⟨386996, by rfl⟩ : syracuseStep 2063981 = 773993) B773993
theorem B1539769 : Blo 358757 1539769 := bstep (se 2 (by rfl) ⟨577413, by rfl⟩ : syracuseStep 1539769 = 1154827) B1154827
theorem B1212137 : Blo 358757 1212137 := bstep (se 2 (by rfl) ⟨454551, by rfl⟩ : syracuseStep 1212137 = 909103) B909103
theorem B360263 : Blo 358757 360263 := bstep (se 1 (by rfl) ⟨270197, by rfl⟩ : syracuseStep 360263 = 540395) B540395
theorem B360415 : Blo 358757 360415 := bstep (se 1 (by rfl) ⟨270311, by rfl⟩ : syracuseStep 360415 = 540623) B540623
theorem B360639 : Blo 358757 360639 := bstep (se 1 (by rfl) ⟨270479, by rfl⟩ : syracuseStep 360639 = 540959) B540959
theorem B360655 : Blo 358757 360655 := bstep (se 1 (by rfl) ⟨270491, by rfl⟩ : syracuseStep 360655 = 540983) B540983
theorem B360703 : Blo 358757 360703 := bstep (se 1 (by rfl) ⟨270527, by rfl⟩ : syracuseStep 360703 = 541055) B541055
theorem B4129055 : Blo 358757 4129055 := bstep (se 1 (by rfl) ⟨3096791, by rfl⟩ : syracuseStep 4129055 = 6193583) B6193583
theorem B360751 : Blo 358757 360751 := bstep (se 1 (by rfl) ⟨270563, by rfl⟩ : syracuseStep 360751 = 541127) B541127
theorem B360987 : Blo 358757 360987 := bstep (se 1 (by rfl) ⟨270740, by rfl⟩ : syracuseStep 360987 = 541481) B541481
theorem B360991 : Blo 358757 360991 := bstep (se 1 (by rfl) ⟨270743, by rfl⟩ : syracuseStep 360991 = 541487) B541487
theorem B361071 : Blo 358757 361071 := bstep (se 1 (by rfl) ⟨270803, by rfl⟩ : syracuseStep 361071 = 541607) B541607
theorem B361127 : Blo 358757 361127 := bstep (se 1 (by rfl) ⟨270845, by rfl⟩ : syracuseStep 361127 = 541691) B541691
theorem B4620995 : Blo 358757 4620995 := bstep (se 1 (by rfl) ⟨3465746, by rfl⟩ : syracuseStep 4620995 = 6931493) B6931493
theorem B361167 : Blo 358757 361167 := bstep (se 1 (by rfl) ⟨270875, by rfl⟩ : syracuseStep 361167 = 541751) B541751
theorem B361247 : Blo 358757 361247 := bstep (se 1 (by rfl) ⟨270935, by rfl⟩ : syracuseStep 361247 = 541871) B541871
theorem B1213271 : Blo 358757 1213271 := bstep (se 1 (by rfl) ⟨909953, by rfl⟩ : syracuseStep 1213271 = 1819907) B1819907
theorem B361519 : Blo 358757 361519 := bstep (se 1 (by rfl) ⟨271139, by rfl⟩ : syracuseStep 361519 = 542279) B542279
theorem B361583 : Blo 358757 361583 := bstep (se 1 (by rfl) ⟨271187, by rfl⟩ : syracuseStep 361583 = 542375) B542375
theorem B5866613 : Blo 358757 5866613 := bstep (se 5 (by rfl) ⟨274997, by rfl⟩ : syracuseStep 5866613 = 549995) B549995
theorem B361639 : Blo 358757 361639 := bstep (se 1 (by rfl) ⟨271229, by rfl⟩ : syracuseStep 361639 = 542459) B542459
theorem B361663 : Blo 358757 361663 := bstep (se 1 (by rfl) ⟨271247, by rfl⟩ : syracuseStep 361663 = 542495) B542495
theorem B361695 : Blo 358757 361695 := bstep (se 1 (by rfl) ⟨271271, by rfl⟩ : syracuseStep 361695 = 542543) B542543
theorem B361775 : Blo 358757 361775 := bstep (se 1 (by rfl) ⟨271331, by rfl⟩ : syracuseStep 361775 = 542663) B542663
theorem B3081725 : Blo 358757 3081725 := bstep (se 3 (by rfl) ⟨577823, by rfl⟩ : syracuseStep 3081725 = 1155647) B1155647
theorem B362011 : Blo 358757 362011 := bstep (se 1 (by rfl) ⟨271508, by rfl⟩ : syracuseStep 362011 = 543017) B543017
theorem B1246751 : Blo 358757 1246751 := bstep (se 1 (by rfl) ⟨935063, by rfl⟩ : syracuseStep 1246751 = 1870127) B1870127
theorem B362015 : Blo 358757 362015 := bstep (se 1 (by rfl) ⟨271511, by rfl⟩ : syracuseStep 362015 = 543023) B543023
theorem B362175 : Blo 358757 362175 := bstep (se 1 (by rfl) ⟨271631, by rfl⟩ : syracuseStep 362175 = 543263) B543263
theorem B1214351 : Blo 358757 1214351 := bstep (se 1 (by rfl) ⟨910763, by rfl⟩ : syracuseStep 1214351 = 1821527) B1821527
theorem B362431 : Blo 358757 362431 := bstep (se 1 (by rfl) ⟨271823, by rfl⟩ : syracuseStep 362431 = 543647) B543647
theorem B362463 : Blo 358757 362463 := bstep (se 1 (by rfl) ⟨271847, by rfl⟩ : syracuseStep 362463 = 543695) B543695
theorem B362523 : Blo 358757 362523 := bstep (se 1 (by rfl) ⟨271892, by rfl⟩ : syracuseStep 362523 = 543785) B543785
theorem B362527 : Blo 358757 362527 := bstep (se 1 (by rfl) ⟨271895, by rfl⟩ : syracuseStep 362527 = 543791) B543791
theorem B362543 : Blo 358757 362543 := bstep (se 1 (by rfl) ⟨271907, by rfl⟩ : syracuseStep 362543 = 543815) B543815
theorem B1640573 : Blo 358757 1640573 := bstep (se 3 (by rfl) ⟨307607, by rfl⟩ : syracuseStep 1640573 = 615215) B615215
theorem B362719 : Blo 358757 362719 := bstep (se 1 (by rfl) ⟨272039, by rfl⟩ : syracuseStep 362719 = 544079) B544079
theorem B1870895 : Blo 358757 1870895 := bstep (se 1 (by rfl) ⟨1403171, by rfl⟩ : syracuseStep 1870895 = 2806343) B2806343
theorem B920639 : Blo 358757 920639 := bstep (se 1 (by rfl) ⟨690479, by rfl⟩ : syracuseStep 920639 = 1380959) B1380959
theorem B2591929 : Blo 358757 2591929 := bstep (se 2 (by rfl) ⟨971973, by rfl⟩ : syracuseStep 2591929 = 1943947) B1943947
theorem B1739987 : Blo 358757 1739987 := bstep (se 1 (by rfl) ⟨1304990, by rfl⟩ : syracuseStep 1739987 = 2609981) B2609981
theorem B1641959 : Blo 358757 1641959 := bstep (se 1 (by rfl) ⟨1231469, by rfl⟩ : syracuseStep 1641959 = 2462939) B2462939
theorem B1216079 : Blo 358757 1216079 := bstep (se 1 (by rfl) ⟨912059, by rfl⟩ : syracuseStep 1216079 = 1824119) B1824119
theorem B10554995 : Blo 358757 10554995 := bstep (se 1 (by rfl) ⟨7916246, by rfl⟩ : syracuseStep 10554995 = 15832493) B15832493
theorem B1544143 : Blo 358757 1544143 := bstep (se 1 (by rfl) ⟨1158107, by rfl⟩ : syracuseStep 1544143 = 2316215) B2316215
theorem B1544159 : Blo 358757 1544159 := bstep (se 1 (by rfl) ⟨1158119, by rfl⟩ : syracuseStep 1544159 = 2316239) B2316239
theorem B1216619 : Blo 358757 1216619 := bstep (se 1 (by rfl) ⟨912464, by rfl⟩ : syracuseStep 1216619 = 1824929) B1824929
theorem B1216673 : Blo 358757 1216673 := bstep (se 2 (by rfl) ⟨456252, by rfl⟩ : syracuseStep 1216673 = 912505) B912505
theorem B19698227 : Blo 358757 19698227 := bstep (se 1 (by rfl) ⟨14773670, by rfl⟩ : syracuseStep 19698227 = 29547341) B29547341
theorem B6132347 : Blo 358757 6132347 := bstep (se 1 (by rfl) ⟨4599260, by rfl⟩ : syracuseStep 6132347 = 9198521) B9198521
theorem B2233327 : Blo 358757 2233327 := bstep (se 1 (by rfl) ⟨1674995, by rfl⟩ : syracuseStep 2233327 = 3349991) B3349991
theorem B1152431 : Blo 358757 1152431 := bstep (se 1 (by rfl) ⟨864323, by rfl⟩ : syracuseStep 1152431 = 1728647) B1728647
theorem B1742255 : Blo 358757 1742255 := bstep (se 1 (by rfl) ⟨1306691, by rfl⟩ : syracuseStep 1742255 = 2613383) B2613383
theorem B1218023 : Blo 358757 1218023 := bstep (se 1 (by rfl) ⟨913517, by rfl⟩ : syracuseStep 1218023 = 1827035) B1827035
theorem B1218131 : Blo 358757 1218131 := bstep (se 1 (by rfl) ⟨913598, by rfl⟩ : syracuseStep 1218131 = 1827197) B1827197
theorem B15898427 : Blo 358757 15898427 := bstep (se 1 (by rfl) ⟨11923820, by rfl⟩ : syracuseStep 15898427 = 23847641) B23847641
theorem B1218401 : Blo 358757 1218401 := bstep (se 2 (by rfl) ⟨456900, by rfl⟩ : syracuseStep 1218401 = 913801) B913801
theorem B7412381 : Blo 358757 7412381 := bstep (se 3 (by rfl) ⟨1389821, by rfl⟩ : syracuseStep 7412381 = 2779643) B2779643
theorem B5315371 : Blo 358757 5315371 := bstep (se 1 (by rfl) ⟨3986528, by rfl⟩ : syracuseStep 5315371 = 7973057) B7973057
theorem B1022777 : Blo 358757 1022777 := bstep (se 2 (by rfl) ⟨383541, by rfl⟩ : syracuseStep 1022777 = 767083) B767083
theorem B3119995 : Blo 358757 3119995 := bstep (se 1 (by rfl) ⟨2339996, by rfl⟩ : syracuseStep 3119995 = 4679993) B4679993
theorem B2202491 : Blo 358757 2202491 := bstep (se 1 (by rfl) ⟨1651868, by rfl⟩ : syracuseStep 2202491 = 3303737) B3303737
theorem B2006579 : Blo 358757 2006579 := bstep (se 1 (by rfl) ⟨1504934, by rfl⟩ : syracuseStep 2006579 = 3009869) B3009869
theorem B1547849 : Blo 358757 1547849 := bstep (se 2 (by rfl) ⟨580443, by rfl⟩ : syracuseStep 1547849 = 1160887) B1160887
theorem B729953 : Blo 358757 729953 := bstep (se 2 (by rfl) ⟨273732, by rfl⟩ : syracuseStep 729953 = 547465) B547465
theorem B1944121 : Blo 358757 1944121 := bstep (se 2 (by rfl) ⟨729045, by rfl⟩ : syracuseStep 1944121 = 1458091) B1458091
theorem B5319431 : Blo 358757 5319431 := bstep (se 1 (by rfl) ⟨3989573, by rfl⟩ : syracuseStep 5319431 = 7979147) B7979147
theorem B6171713 : Blo 358757 6171713 := bstep (se 2 (by rfl) ⟨2314392, by rfl⟩ : syracuseStep 6171713 = 4628785) B4628785
theorem B4893929 : Blo 358757 4893929 := bstep (se 2 (by rfl) ⟨1835223, by rfl⟩ : syracuseStep 4893929 = 3670447) B3670447
theorem B3452179 : Blo 358757 3452179 := bstep (se 1 (by rfl) ⟨2589134, by rfl⟩ : syracuseStep 3452179 = 5178269) B5178269
theorem B1027367 : Blo 358757 1027367 := bstep (se 1 (by rfl) ⟨770525, by rfl⟩ : syracuseStep 1027367 = 1541051) B1541051
theorem B601499 : Blo 358757 601499 := bstep (se 1 (by rfl) ⟨451124, by rfl⟩ : syracuseStep 601499 = 902249) B902249
theorem B404959 : Blo 358757 404959 := bstep (se 1 (by rfl) ⟨303719, by rfl⟩ : syracuseStep 404959 = 607439) B607439
theorem B12922739 : Blo 358757 12922739 := bstep (se 1 (by rfl) ⟨9692054, by rfl⟩ : syracuseStep 12922739 = 19384109) B19384109
theorem B405499 : Blo 358757 405499 := bstep (se 1 (by rfl) ⟨304124, by rfl⟩ : syracuseStep 405499 = 608249) B608249
theorem B405607 : Blo 358757 405607 := bstep (se 1 (by rfl) ⟨304205, by rfl⟩ : syracuseStep 405607 = 608411) B608411
theorem B405679 : Blo 358757 405679 := bstep (se 1 (by rfl) ⟨304259, by rfl⟩ : syracuseStep 405679 = 608519) B608519
theorem B1028551 : Blo 358757 1028551 := bstep (se 1 (by rfl) ⟨771413, by rfl⟩ : syracuseStep 1028551 = 1542827) B1542827
theorem B766783 : Blo 358757 766783 := bstep (se 1 (by rfl) ⟨575087, by rfl⟩ : syracuseStep 766783 = 1150175) B1150175
theorem B406363 : Blo 358757 406363 := bstep (se 1 (by rfl) ⟨304772, by rfl⟩ : syracuseStep 406363 = 609545) B609545
theorem B3093511 : Blo 358757 3093511 := bstep (se 1 (by rfl) ⟨2320133, by rfl⟩ : syracuseStep 3093511 = 4640267) B4640267
theorem B767159 : Blo 358757 767159 := bstep (se 1 (by rfl) ⟨575369, by rfl⟩ : syracuseStep 767159 = 1150739) B1150739
theorem B767227 : Blo 358757 767227 := bstep (se 1 (by rfl) ⟨575420, by rfl⟩ : syracuseStep 767227 = 1150841) B1150841
theorem B1029793 : Blo 358757 1029793 := bstep (se 2 (by rfl) ⟨386172, by rfl⟩ : syracuseStep 1029793 = 772345) B772345
theorem B866015 : Blo 358757 866015 := bstep (se 1 (by rfl) ⟨649511, by rfl⟩ : syracuseStep 866015 = 1299023) B1299023
theorem B1390567 : Blo 358757 1390567 := bstep (se 1 (by rfl) ⟨1042925, by rfl⟩ : syracuseStep 1390567 = 2085851) B2085851
theorem B407623 : Blo 358757 407623 := bstep (se 1 (by rfl) ⟨305717, by rfl⟩ : syracuseStep 407623 = 611435) B611435
theorem B1161287 : Blo 358757 1161287 := bstep (se 1 (by rfl) ⟨870965, by rfl⟩ : syracuseStep 1161287 = 1741931) B1741931
theorem B1030283 : Blo 358757 1030283 := bstep (se 1 (by rfl) ⟨772712, by rfl⟩ : syracuseStep 1030283 = 1545425) B1545425
theorem B539087 : Blo 358757 539087 := bstep (se 1 (by rfl) ⟨404315, by rfl⟩ : syracuseStep 539087 = 808631) B808631
theorem B4635143 : Blo 358757 4635143 := bstep (se 1 (by rfl) ⟨3476357, by rfl⟩ : syracuseStep 4635143 = 6952715) B6952715
theorem B539177 : Blo 358757 539177 := bstep (se 2 (by rfl) ⟨202191, by rfl⟩ : syracuseStep 539177 = 404383) B404383
theorem B5847673 : Blo 358757 5847673 := bstep (se 2 (by rfl) ⟨2192877, by rfl⟩ : syracuseStep 5847673 = 4385755) B4385755
theorem B539369 : Blo 358757 539369 := bstep (se 2 (by rfl) ⟨202263, by rfl⟩ : syracuseStep 539369 = 404527) B404527
theorem B539753 : Blo 358757 539753 := bstep (se 2 (by rfl) ⟨202407, by rfl⟩ : syracuseStep 539753 = 404815) B404815
theorem B539879 : Blo 358757 539879 := bstep (se 1 (by rfl) ⟨404909, by rfl⟩ : syracuseStep 539879 = 809819) B809819
theorem B1031399 : Blo 358757 1031399 := bstep (se 1 (by rfl) ⟨773549, by rfl⟩ : syracuseStep 1031399 = 1547099) B1547099
theorem B4963751 : Blo 358757 4963751 := bstep (se 1 (by rfl) ⟨3722813, by rfl⟩ : syracuseStep 4963751 = 7445627) B7445627
theorem B540383 : Blo 358757 540383 := bstep (se 1 (by rfl) ⟨405287, by rfl⟩ : syracuseStep 540383 = 810575) B810575
theorem B605927 : Blo 358757 605927 := bstep (se 1 (by rfl) ⟨454445, by rfl⟩ : syracuseStep 605927 = 908891) B908891
theorem B540425 : Blo 358757 540425 := bstep (se 2 (by rfl) ⟨202659, by rfl⟩ : syracuseStep 540425 = 405319) B405319
theorem B540863 : Blo 358757 540863 := bstep (se 1 (by rfl) ⟨405647, by rfl⟩ : syracuseStep 540863 = 811295) B811295
theorem B737515 : Blo 358757 737515 := bstep (se 1 (by rfl) ⟨553136, by rfl⟩ : syracuseStep 737515 = 1106273) B1106273
theorem B868735 : Blo 358757 868735 := bstep (se 1 (by rfl) ⟨651551, by rfl⟩ : syracuseStep 868735 = 1303103) B1303103
theorem B3129905 : Blo 358757 3129905 := bstep (se 2 (by rfl) ⟨1173714, by rfl⟩ : syracuseStep 3129905 = 2347429) B2347429
theorem B541289 : Blo 358757 541289 := bstep (se 2 (by rfl) ⟨202983, by rfl⟩ : syracuseStep 541289 = 405967) B405967
theorem B541295 : Blo 358757 541295 := bstep (se 1 (by rfl) ⟨405971, by rfl⟩ : syracuseStep 541295 = 811943) B811943
theorem B2048651 : Blo 358757 2048651 := bstep (se 1 (by rfl) ⟨1536488, by rfl⟩ : syracuseStep 2048651 = 3072977) B3072977
theorem B2474819 : Blo 358757 2474819 := bstep (se 1 (by rfl) ⟨1856114, by rfl⟩ : syracuseStep 2474819 = 3712229) B3712229
theorem B541919 : Blo 358757 541919 := bstep (se 1 (by rfl) ⟨406439, by rfl⟩ : syracuseStep 541919 = 812879) B812879
theorem B541931 : Blo 358757 541931 := bstep (se 1 (by rfl) ⟨406448, by rfl⟩ : syracuseStep 541931 = 812897) B812897
theorem B607567 : Blo 358757 607567 := bstep (se 1 (by rfl) ⟨455675, by rfl⟩ : syracuseStep 607567 = 911351) B911351
theorem B1099165 : Blo 358757 1099165 := bstep (se 3 (by rfl) ⟨206093, by rfl⟩ : syracuseStep 1099165 = 412187) B412187
theorem B6145469 : Blo 358757 6145469 := bstep (se 3 (by rfl) ⟨1152275, by rfl⟩ : syracuseStep 6145469 = 2304551) B2304551
theorem B542315 : Blo 358757 542315 := bstep (se 1 (by rfl) ⟨406736, by rfl⟩ : syracuseStep 542315 = 813473) B813473
theorem B542399 : Blo 358757 542399 := bstep (se 1 (by rfl) ⟨406799, by rfl⟩ : syracuseStep 542399 = 813599) B813599
theorem B542585 : Blo 358757 542585 := bstep (se 2 (by rfl) ⟨203469, by rfl⟩ : syracuseStep 542585 = 406939) B406939
theorem B608539 : Blo 358757 608539 := bstep (se 1 (by rfl) ⟨456404, by rfl⟩ : syracuseStep 608539 = 912809) B912809
theorem B608681 : Blo 358757 608681 := bstep (se 2 (by rfl) ⟨228255, by rfl⟩ : syracuseStep 608681 = 456511) B456511
theorem B11684321 : Blo 358757 11684321 := bstep (se 2 (by rfl) ⟨4381620, by rfl⟩ : syracuseStep 11684321 = 8763241) B8763241
theorem B608863 : Blo 358757 608863 := bstep (se 1 (by rfl) ⟨456647, by rfl⟩ : syracuseStep 608863 = 913295) B913295
theorem B543335 : Blo 358757 543335 := bstep (se 1 (by rfl) ⟨407501, by rfl⟩ : syracuseStep 543335 = 815003) B815003
theorem B56183543 : Blo 358757 56183543 := bstep (se 1 (by rfl) ⟨42137657, by rfl⟩ : syracuseStep 56183543 = 84275315) B84275315
theorem B543527 : Blo 358757 543527 := bstep (se 1 (by rfl) ⟨407645, by rfl⟩ : syracuseStep 543527 = 815291) B815291
theorem B2050859 : Blo 358757 2050859 := bstep (se 1 (by rfl) ⟨1538144, by rfl⟩ : syracuseStep 2050859 = 3076289) B3076289
theorem B2051041 : Blo 358757 2051041 := bstep (se 2 (by rfl) ⟨769140, by rfl⟩ : syracuseStep 2051041 = 1538281) B1538281
theorem B609275 : Blo 358757 609275 := bstep (se 1 (by rfl) ⟨456956, by rfl⟩ : syracuseStep 609275 = 913913) B913913
theorem B543851 : Blo 358757 543851 := bstep (se 1 (by rfl) ⟨407888, by rfl⟩ : syracuseStep 543851 = 815777) B815777
theorem B1101053 : Blo 358757 1101053 := bstep (se 3 (by rfl) ⟨206447, by rfl⟩ : syracuseStep 1101053 = 412895) B412895
theorem B544091 : Blo 358757 544091 := bstep (se 1 (by rfl) ⟨408068, by rfl⟩ : syracuseStep 544091 = 816137) B816137
theorem B544121 : Blo 358757 544121 := bstep (se 2 (by rfl) ⟨204045, by rfl⟩ : syracuseStep 544121 = 408091) B408091
theorem B544127 : Blo 358757 544127 := bstep (se 1 (by rfl) ⟨408095, by rfl⟩ : syracuseStep 544127 = 816191) B816191
theorem B2608537 : Blo 358757 2608537 := bstep (se 2 (by rfl) ⟨978201, by rfl⟩ : syracuseStep 2608537 = 1956403) B1956403
theorem B774011 : Blo 358757 774011 := bstep (se 1 (by rfl) ⟨580508, by rfl⟩ : syracuseStep 774011 = 1161017) B1161017
theorem B807209 : Blo 358757 807209 := bstep (se 2 (by rfl) ⟨302703, by rfl⟩ : syracuseStep 807209 = 605407) B605407
theorem B971131 : Blo 358757 971131 := bstep (se 1 (by rfl) ⟨728348, by rfl⟩ : syracuseStep 971131 = 1456697) B1456697
theorem B971195 : Blo 358757 971195 := bstep (se 1 (by rfl) ⟨728396, by rfl⟩ : syracuseStep 971195 = 1456793) B1456793
theorem B807479 : Blo 358757 807479 := bstep (se 1 (by rfl) ⟨605609, by rfl⟩ : syracuseStep 807479 = 1211219) B1211219
theorem B3920507 : Blo 358757 3920507 := bstep (se 1 (by rfl) ⟨2940380, by rfl⟩ : syracuseStep 3920507 = 5880761) B5880761
theorem B2216585 : Blo 358757 2216585 := bstep (se 2 (by rfl) ⟨831219, by rfl⟩ : syracuseStep 2216585 = 1662439) B1662439
theorem B807785 : Blo 358757 807785 := bstep (se 2 (by rfl) ⟨302919, by rfl⟩ : syracuseStep 807785 = 605839) B605839
theorem B1299311 : Blo 358757 1299311 := bstep (se 1 (by rfl) ⟨974483, by rfl⟩ : syracuseStep 1299311 = 1948967) B1948967
theorem B807839 : Blo 358757 807839 := bstep (se 1 (by rfl) ⟨605879, by rfl⟩ : syracuseStep 807839 = 1211759) B1211759
theorem B2053025 : Blo 358757 2053025 := bstep (se 2 (by rfl) ⟨769884, by rfl⟩ : syracuseStep 2053025 = 1539769) B1539769
theorem B1037299 : Blo 358757 1037299 := bstep (se 1 (by rfl) ⟨777974, by rfl⟩ : syracuseStep 1037299 = 1555949) B1555949
theorem B5559353 : Blo 358757 5559353 := bstep (se 2 (by rfl) ⟨2084757, by rfl⟩ : syracuseStep 5559353 = 4169515) B4169515
theorem B808091 : Blo 358757 808091 := bstep (se 1 (by rfl) ⟨606068, by rfl⟩ : syracuseStep 808091 = 1212137) B1212137
theorem B13981081 : Blo 358757 13981081 := bstep (se 2 (by rfl) ⟨5242905, by rfl⟩ : syracuseStep 13981081 = 10485811) B10485811
theorem B611995 : Blo 358757 611995 := bstep (se 1 (by rfl) ⟨458996, by rfl⟩ : syracuseStep 611995 = 917993) B917993
theorem B808667 : Blo 358757 808667 := bstep (se 1 (by rfl) ⟨606500, by rfl⟩ : syracuseStep 808667 = 1213001) B1213001
theorem B2742011 : Blo 358757 2742011 := bstep (se 1 (by rfl) ⟨2056508, by rfl⟩ : syracuseStep 2742011 = 4113017) B4113017
theorem B808775 : Blo 358757 808775 := bstep (se 1 (by rfl) ⟨606581, by rfl⟩ : syracuseStep 808775 = 1213163) B1213163
theorem B1366055 : Blo 358757 1366055 := bstep (se 1 (by rfl) ⟨1024541, by rfl⟩ : syracuseStep 1366055 = 2049083) B2049083
theorem B579803 : Blo 358757 579803 := bstep (se 1 (by rfl) ⟨434852, by rfl⟩ : syracuseStep 579803 = 869705) B869705
theorem B809783 : Blo 358757 809783 := bstep (se 1 (by rfl) ⟨607337, by rfl⟩ : syracuseStep 809783 = 1214675) B1214675
theorem B383815 : Blo 358757 383815 := bstep (se 1 (by rfl) ⟨287861, by rfl⟩ : syracuseStep 383815 = 575723) B575723
theorem B875375 : Blo 358757 875375 := bstep (se 1 (by rfl) ⟨656531, by rfl⟩ : syracuseStep 875375 = 1313063) B1313063
theorem B1956797 : Blo 358757 1956797 := bstep (se 3 (by rfl) ⟨366899, by rfl⟩ : syracuseStep 1956797 = 733799) B733799
theorem B809963 : Blo 358757 809963 := bstep (se 1 (by rfl) ⟨607472, by rfl⟩ : syracuseStep 809963 = 1214945) B1214945
theorem B9264131 : Blo 358757 9264131 := bstep (se 1 (by rfl) ⟨6948098, by rfl⟩ : syracuseStep 9264131 = 13896197) B13896197
theorem B3890663 : Blo 358757 3890663 := bstep (se 1 (by rfl) ⟨2917997, by rfl⟩ : syracuseStep 3890663 = 5835995) B5835995
theorem B1367543 : Blo 358757 1367543 := bstep (se 1 (by rfl) ⟨1025657, by rfl⟩ : syracuseStep 1367543 = 2051315) B2051315
theorem B908921 : Blo 358757 908921 := bstep (se 2 (by rfl) ⟨340845, by rfl⟩ : syracuseStep 908921 = 681691) B681691
theorem B810863 : Blo 358757 810863 := bstep (se 1 (by rfl) ⟨608147, by rfl⟩ : syracuseStep 810863 = 1216295) B1216295
theorem B6184835 : Blo 358757 6184835 := bstep (se 1 (by rfl) ⟨4638626, by rfl⟩ : syracuseStep 6184835 = 9277253) B9277253
theorem B1957787 : Blo 358757 1957787 := bstep (se 1 (by rfl) ⟨1468340, by rfl⟩ : syracuseStep 1957787 = 2936681) B2936681
theorem B1368211 : Blo 358757 1368211 := bstep (se 1 (by rfl) ⟨1026158, by rfl⟩ : syracuseStep 1368211 = 2052317) B2052317
theorem B1958305 : Blo 358757 1958305 := bstep (se 2 (by rfl) ⟨734364, by rfl⟩ : syracuseStep 1958305 = 1468729) B1468729
theorem B811547 : Blo 358757 811547 := bstep (se 1 (by rfl) ⟨608660, by rfl⟩ : syracuseStep 811547 = 1217321) B1217321
theorem B811727 : Blo 358757 811727 := bstep (se 1 (by rfl) ⟨608795, by rfl⟩ : syracuseStep 811727 = 1217591) B1217591
theorem B1696747 : Blo 358757 1696747 := bstep (se 1 (by rfl) ⟨1272560, by rfl⟩ : syracuseStep 1696747 = 2545121) B2545121
theorem B812105 : Blo 358757 812105 := bstep (se 2 (by rfl) ⟨304539, by rfl⟩ : syracuseStep 812105 = 609079) B609079
theorem B1205561 : Blo 358757 1205561 := bstep (se 2 (by rfl) ⟨452085, by rfl⟩ : syracuseStep 1205561 = 904171) B904171
theorem B681463 : Blo 358757 681463 := bstep (se 1 (by rfl) ⟨511097, by rfl⟩ : syracuseStep 681463 = 1022195) B1022195
theorem B5203693 : Blo 358757 5203693 := bstep (se 3 (by rfl) ⟨975692, by rfl⟩ : syracuseStep 5203693 = 1951385) B1951385
theorem B2058149 : Blo 358757 2058149 := bstep (se 4 (by rfl) ⟨192951, by rfl⟩ : syracuseStep 2058149 = 385903) B385903
theorem B813023 : Blo 358757 813023 := bstep (se 1 (by rfl) ⟨609767, by rfl⟩ : syracuseStep 813023 = 1219535) B1219535
theorem B911483 : Blo 358757 911483 := bstep (se 1 (by rfl) ⟨683612, by rfl⟩ : syracuseStep 911483 = 1367225) B1367225
theorem B1370459 : Blo 358757 1370459 := bstep (se 1 (by rfl) ⟨1027844, by rfl⟩ : syracuseStep 1370459 = 2055689) B2055689
theorem B616939 : Blo 358757 616939 := bstep (se 1 (by rfl) ⟨462704, by rfl⟩ : syracuseStep 616939 = 925409) B925409
theorem B814031 : Blo 358757 814031 := bstep (se 1 (by rfl) ⟨610523, by rfl⟩ : syracuseStep 814031 = 1221047) B1221047
theorem B814121 : Blo 358757 814121 := bstep (se 2 (by rfl) ⟨305295, by rfl⟩ : syracuseStep 814121 = 610591) B610591
theorem B814355 : Blo 358757 814355 := bstep (se 1 (by rfl) ⟨610766, by rfl⟩ : syracuseStep 814355 = 1221533) B1221533
theorem B814391 : Blo 358757 814391 := bstep (se 1 (by rfl) ⟨610793, by rfl⟩ : syracuseStep 814391 = 1221587) B1221587
theorem B2747843 : Blo 358757 2747843 := bstep (se 1 (by rfl) ⟨2060882, by rfl⟩ : syracuseStep 2747843 = 4121765) B4121765
theorem B814985 : Blo 358757 814985 := bstep (se 2 (by rfl) ⟨305619, by rfl⟩ : syracuseStep 814985 = 611239) B611239
theorem B1535993 : Blo 358757 1535993 := bstep (se 2 (by rfl) ⟨575997, by rfl⟩ : syracuseStep 1535993 = 1151995) B1151995
theorem B815201 : Blo 358757 815201 := bstep (se 2 (by rfl) ⟨305700, by rfl⟩ : syracuseStep 815201 = 611401) B611401
theorem B15790403 : Blo 358757 15790403 := bstep (se 1 (by rfl) ⟨11842802, by rfl⟩ : syracuseStep 15790403 = 23685605) B23685605
theorem B1536641 : Blo 358757 1536641 := bstep (se 2 (by rfl) ⟨576240, by rfl⟩ : syracuseStep 1536641 = 1152481) B1152481
theorem B815867 : Blo 358757 815867 := bstep (se 1 (by rfl) ⟨611900, by rfl⟩ : syracuseStep 815867 = 1223801) B1223801
theorem B881455 : Blo 358757 881455 := bstep (se 1 (by rfl) ⟨661091, by rfl⟩ : syracuseStep 881455 = 1322183) B1322183
theorem B35648363 : Blo 358757 35648363 := bstep (se 1 (by rfl) ⟨26736272, by rfl⟩ : syracuseStep 35648363 = 53472545) B53472545
theorem B1373071 : Blo 358757 1373071 := bstep (se 1 (by rfl) ⟨1029803, by rfl⟩ : syracuseStep 1373071 = 2059607) B2059607
theorem B816083 : Blo 358757 816083 := bstep (se 1 (by rfl) ⟨612062, by rfl⟩ : syracuseStep 816083 = 1224125) B1224125
theorem B455863 : Blo 358757 455863 := bstep (se 1 (by rfl) ⟨341897, by rfl⟩ : syracuseStep 455863 = 683795) B683795
theorem B5534963 : Blo 358757 5534963 := bstep (se 1 (by rfl) ⟨4151222, by rfl⟩ : syracuseStep 5534963 = 8302445) B8302445
theorem B1570079 : Blo 358757 1570079 := bstep (se 1 (by rfl) ⟨1177559, by rfl⟩ : syracuseStep 1570079 = 2355119) B2355119
theorem B456283 : Blo 358757 456283 := bstep (se 1 (by rfl) ⟨342212, by rfl⟩ : syracuseStep 456283 = 684425) B684425
theorem B7141067 : Blo 358757 7141067 := bstep (se 1 (by rfl) ⟨5355800, by rfl⟩ : syracuseStep 7141067 = 10711601) B10711601
theorem B7108667 : Blo 358757 7108667 := bstep (se 1 (by rfl) ⟨5331500, by rfl⟩ : syracuseStep 7108667 = 10663001) B10663001
theorem B3471437 : Blo 358757 3471437 := bstep (se 3 (by rfl) ⟨650894, by rfl⟩ : syracuseStep 3471437 = 1301789) B1301789
theorem B1538351 : Blo 358757 1538351 := bstep (se 1 (by rfl) ⟨1153763, by rfl⟩ : syracuseStep 1538351 = 2307527) B2307527
theorem B3307823 : Blo 358757 3307823 := bstep (se 1 (by rfl) ⟨2480867, by rfl⟩ : syracuseStep 3307823 = 4961735) B4961735
theorem B358815 : Blo 358757 358815 := bstep (se 1 (by rfl) ⟨269111, by rfl⟩ : syracuseStep 358815 = 538223) B538223
theorem B13105597 : Blo 358757 13105597 := bstep (se 3 (by rfl) ⟨2457299, by rfl⟩ : syracuseStep 13105597 = 4914599) B4914599
theorem B358863 : Blo 358757 358863 := bstep (se 1 (by rfl) ⟨269147, by rfl⟩ : syracuseStep 358863 = 538295) B538295
theorem B358887 : Blo 358757 358887 := bstep (se 1 (by rfl) ⟨269165, by rfl⟩ : syracuseStep 358887 = 538331) B538331
theorem B359003 : Blo 358757 359003 := bstep (se 1 (by rfl) ⟨269252, by rfl⟩ : syracuseStep 359003 = 538505) B538505
theorem B359071 : Blo 358757 359071 := bstep (se 1 (by rfl) ⟨269303, by rfl⟩ : syracuseStep 359071 = 538607) B538607
theorem B359239 : Blo 358757 359239 := bstep (se 1 (by rfl) ⟨269429, by rfl⟩ : syracuseStep 359239 = 538859) B538859
theorem B359279 : Blo 358757 359279 := bstep (se 1 (by rfl) ⟨269459, by rfl⟩ : syracuseStep 359279 = 538919) B538919
theorem B359335 : Blo 358757 359335 := bstep (se 1 (by rfl) ⟨269501, by rfl⟩ : syracuseStep 359335 = 539003) B539003
theorem B359515 : Blo 358757 359515 := bstep (se 1 (by rfl) ⟨269636, by rfl⟩ : syracuseStep 359515 = 539273) B539273
theorem B359631 : Blo 358757 359631 := bstep (se 1 (by rfl) ⟨269723, by rfl⟩ : syracuseStep 359631 = 539447) B539447
theorem B359655 : Blo 358757 359655 := bstep (se 1 (by rfl) ⟨269741, by rfl⟩ : syracuseStep 359655 = 539483) B539483
theorem B3276035 : Blo 358757 3276035 := bstep (se 1 (by rfl) ⟨2457026, by rfl⟩ : syracuseStep 3276035 = 4914053) B4914053
theorem B359751 : Blo 358757 359751 := bstep (se 1 (by rfl) ⟨269813, by rfl⟩ : syracuseStep 359751 = 539627) B539627
theorem B359887 : Blo 358757 359887 := bstep (se 1 (by rfl) ⟨269915, by rfl⟩ : syracuseStep 359887 = 539831) B539831
theorem B360047 : Blo 358757 360047 := bstep (se 1 (by rfl) ⟨270035, by rfl⟩ : syracuseStep 360047 = 540071) B540071
theorem B360103 : Blo 358757 360103 := bstep (se 1 (by rfl) ⟨270077, by rfl⟩ : syracuseStep 360103 = 540155) B540155
theorem B360167 : Blo 358757 360167 := bstep (se 1 (by rfl) ⟨270125, by rfl⟩ : syracuseStep 360167 = 540251) B540251
theorem B1375987 : Blo 358757 1375987 := bstep (se 1 (by rfl) ⟨1031990, by rfl⟩ : syracuseStep 1375987 = 2063981) B2063981
theorem B360223 : Blo 358757 360223 := bstep (se 1 (by rfl) ⟨270167, by rfl⟩ : syracuseStep 360223 = 540335) B540335
theorem B360303 : Blo 358757 360303 := bstep (se 1 (by rfl) ⟨270227, by rfl⟩ : syracuseStep 360303 = 540455) B540455
theorem B360359 : Blo 358757 360359 := bstep (se 1 (by rfl) ⟨270269, by rfl⟩ : syracuseStep 360359 = 540539) B540539
theorem B819155 : Blo 358757 819155 := bstep (se 1 (by rfl) ⟨614366, by rfl⟩ : syracuseStep 819155 = 1228733) B1228733
theorem B360575 : Blo 358757 360575 := bstep (se 1 (by rfl) ⟨270431, by rfl⟩ : syracuseStep 360575 = 540863) B540863
theorem B2752703 : Blo 358757 2752703 := bstep (se 1 (by rfl) ⟨2064527, by rfl⟩ : syracuseStep 2752703 = 4129055) B4129055
theorem B983353 : Blo 358757 983353 := bstep (se 2 (by rfl) ⟨368757, by rfl⟩ : syracuseStep 983353 = 737515) B737515
theorem B360859 : Blo 358757 360859 := bstep (se 1 (by rfl) ⟨270644, by rfl⟩ : syracuseStep 360859 = 541289) B541289
theorem B360863 : Blo 358757 360863 := bstep (se 1 (by rfl) ⟨270647, by rfl⟩ : syracuseStep 360863 = 541295) B541295
theorem B3080663 : Blo 358757 3080663 := bstep (se 1 (by rfl) ⟨2310497, by rfl⟩ : syracuseStep 3080663 = 4620995) B4620995
theorem B361279 : Blo 358757 361279 := bstep (se 1 (by rfl) ⟨270959, by rfl⟩ : syracuseStep 361279 = 541919) B541919
theorem B361287 : Blo 358757 361287 := bstep (se 1 (by rfl) ⟨270965, by rfl⟩ : syracuseStep 361287 = 541931) B541931
theorem B4096979 : Blo 358757 4096979 := bstep (se 1 (by rfl) ⟨3072734, by rfl⟩ : syracuseStep 4096979 = 6145469) B6145469
theorem B361543 : Blo 358757 361543 := bstep (se 1 (by rfl) ⟨271157, by rfl⟩ : syracuseStep 361543 = 542315) B542315
theorem B361599 : Blo 358757 361599 := bstep (se 1 (by rfl) ⟨271199, by rfl⟩ : syracuseStep 361599 = 542399) B542399
theorem B2589853 : Blo 358757 2589853 := bstep (se 3 (by rfl) ⟨485597, by rfl⟩ : syracuseStep 2589853 = 971195) B971195
theorem B361723 : Blo 358757 361723 := bstep (se 1 (by rfl) ⟨271292, by rfl⟩ : syracuseStep 361723 = 542585) B542585
theorem B2262329 : Blo 358757 2262329 := bstep (se 2 (by rfl) ⟨848373, by rfl⟩ : syracuseStep 2262329 = 1696747) B1696747
theorem B362223 : Blo 358757 362223 := bstep (se 1 (by rfl) ⟨271667, by rfl⟩ : syracuseStep 362223 = 543335) B543335
theorem B37455695 : Blo 358757 37455695 := bstep (se 1 (by rfl) ⟨28091771, by rfl⟩ : syracuseStep 37455695 = 56183543) B56183543
theorem B362351 : Blo 358757 362351 := bstep (se 1 (by rfl) ⟨271763, by rfl⟩ : syracuseStep 362351 = 543527) B543527
theorem B362567 : Blo 358757 362567 := bstep (se 1 (by rfl) ⟨271925, by rfl⟩ : syracuseStep 362567 = 543851) B543851
theorem B362727 : Blo 358757 362727 := bstep (se 1 (by rfl) ⟨272045, by rfl⟩ : syracuseStep 362727 = 544091) B544091
theorem B362747 : Blo 358757 362747 := bstep (se 1 (by rfl) ⟨272060, by rfl⟩ : syracuseStep 362747 = 544121) B544121
theorem B362751 : Blo 358757 362751 := bstep (se 1 (by rfl) ⟨272063, by rfl⟩ : syracuseStep 362751 = 544127) B544127
theorem B3706235 : Blo 358757 3706235 := bstep (se 1 (by rfl) ⟨2779676, by rfl⟩ : syracuseStep 3706235 = 5559353) B5559353
theorem B2592161 : Blo 358757 2592161 := bstep (se 2 (by rfl) ⟨972060, by rfl⟩ : syracuseStep 2592161 = 1944121) B1944121
theorem B3214829 : Blo 358757 3214829 := bstep (se 3 (by rfl) ⟨602780, by rfl⟩ : syracuseStep 3214829 = 1205561) B1205561
theorem B28348645 : Blo 358757 28348645 := bstep (se 4 (by rfl) ⟨2657685, by rfl⟩ : syracuseStep 28348645 = 5315371) B5315371
theorem B3478049 : Blo 358757 3478049 := bstep (se 2 (by rfl) ⟨1304268, by rfl⟩ : syracuseStep 3478049 = 2608537) B2608537
theorem B2593775 : Blo 358757 2593775 := bstep (se 1 (by rfl) ⟨1945331, by rfl⟩ : syracuseStep 2593775 = 3890663) B3890663
theorem B1546141 : Blo 358757 1546141 := bstep (se 3 (by rfl) ⟨289901, by rfl⟩ : syracuseStep 1546141 = 579803) B579803
theorem B1022377 : Blo 358757 1022377 := bstep (se 2 (by rfl) ⟨383391, by rfl⟩ : syracuseStep 1022377 = 766783) B766783
theorem B1383065 : Blo 358757 1383065 := bstep (se 2 (by rfl) ⟨518649, by rfl⟩ : syracuseStep 1383065 = 1037299) B1037299
theorem B1022969 : Blo 358757 1022969 := bstep (se 2 (by rfl) ⟨383613, by rfl⟩ : syracuseStep 1022969 = 767227) B767227
theorem B3546287 : Blo 358757 3546287 := bstep (se 1 (by rfl) ⟨2659715, by rfl⟩ : syracuseStep 3546287 = 5319431) B5319431
theorem B1023995 : Blo 358757 1023995 := bstep (se 1 (by rfl) ⟨767996, by rfl⟩ : syracuseStep 1023995 = 1535993) B1535993
theorem B4989053 : Blo 358757 4989053 := bstep (se 3 (by rfl) ⟨935447, by rfl⟩ : syracuseStep 4989053 = 1870895) B1870895
theorem B10526935 : Blo 358757 10526935 := bstep (se 1 (by rfl) ⟨7895201, by rfl⟩ : syracuseStep 10526935 = 15790403) B15790403
theorem B1024427 : Blo 358757 1024427 := bstep (se 1 (by rfl) ⟨768320, by rfl⟩ : syracuseStep 1024427 = 1536641) B1536641
theorem B23765575 : Blo 358757 23765575 := bstep (se 1 (by rfl) ⟨17824181, by rfl⟩ : syracuseStep 23765575 = 35648363) B35648363
theorem B17474129 : Blo 358757 17474129 := bstep (se 2 (by rfl) ⟨6552798, by rfl⟩ : syracuseStep 17474129 = 13105597) B13105597
theorem B4760711 : Blo 358757 4760711 := bstep (se 1 (by rfl) ⟨3570533, by rfl⟩ : syracuseStep 4760711 = 7141067) B7141067
theorem B1025567 : Blo 358757 1025567 := bstep (se 1 (by rfl) ⟨769175, by rfl⟩ : syracuseStep 1025567 = 1538351) B1538351
theorem B2205215 : Blo 358757 2205215 := bstep (se 1 (by rfl) ⟨1653911, by rfl⟩ : syracuseStep 2205215 = 3307823) B3307823
theorem B3090095 : Blo 358757 3090095 := bstep (se 1 (by rfl) ⟨2317571, by rfl⟩ : syracuseStep 3090095 = 4635143) B4635143
theorem B403951 : Blo 358757 403951 := bstep (se 1 (by rfl) ⟨302963, by rfl⟩ : syracuseStep 403951 = 605927) B605927
theorem B1158313 : Blo 358757 1158313 := bstep (se 2 (by rfl) ⟨434367, by rfl⟩ : syracuseStep 1158313 = 868735) B868735
theorem B1649879 : Blo 358757 1649879 := bstep (se 1 (by rfl) ⟨1237409, by rfl⟩ : syracuseStep 1649879 = 2474819) B2474819
theorem B3911075 : Blo 358757 3911075 := bstep (se 1 (by rfl) ⟨2933306, by rfl⟩ : syracuseStep 3911075 = 5866613) B5866613
theorem B831167 : Blo 358757 831167 := bstep (se 1 (by rfl) ⟨623375, by rfl⟩ : syracuseStep 831167 = 1246751) B1246751
theorem B1093715 : Blo 358757 1093715 := bstep (se 1 (by rfl) ⟨820286, by rfl⟩ : syracuseStep 1093715 = 1640573) B1640573
theorem B405787 : Blo 358757 405787 := bstep (se 1 (by rfl) ⟨304340, by rfl⟩ : syracuseStep 405787 = 608681) B608681
theorem B5910893 : Blo 358757 5910893 := bstep (se 3 (by rfl) ⟨1108292, by rfl⟩ : syracuseStep 5910893 = 2216585) B2216585
theorem B406183 : Blo 358757 406183 := bstep (se 1 (by rfl) ⟨304637, by rfl⟩ : syracuseStep 406183 = 609275) B609275
theorem B1159991 : Blo 358757 1159991 := bstep (se 1 (by rfl) ⟨869993, by rfl⟩ : syracuseStep 1159991 = 1739987) B1739987
theorem B734035 : Blo 358757 734035 := bstep (se 1 (by rfl) ⟨550526, by rfl⟩ : syracuseStep 734035 = 1101053) B1101053
theorem B1094639 : Blo 358757 1094639 := bstep (se 1 (by rfl) ⟨820979, by rfl⟩ : syracuseStep 1094639 = 1641959) B1641959
theorem B1029439 : Blo 358757 1029439 := bstep (se 1 (by rfl) ⟨772079, by rfl⟩ : syracuseStep 1029439 = 1544159) B1544159
theorem B538139 : Blo 358757 538139 := bstep (se 1 (by rfl) ⟨403604, by rfl⟩ : syracuseStep 538139 = 807209) B807209
theorem B538319 : Blo 358757 538319 := bstep (se 1 (by rfl) ⟨403739, by rfl⟩ : syracuseStep 538319 = 807479) B807479
theorem B538523 : Blo 358757 538523 := bstep (se 1 (by rfl) ⟨403892, by rfl⟩ : syracuseStep 538523 = 807785) B807785
theorem B866207 : Blo 358757 866207 := bstep (se 1 (by rfl) ⟨649655, by rfl⟩ : syracuseStep 866207 = 1299311) B1299311
theorem B538559 : Blo 358757 538559 := bstep (se 1 (by rfl) ⟨403919, by rfl⟩ : syracuseStep 538559 = 807839) B807839
theorem B538727 : Blo 358757 538727 := bstep (se 1 (by rfl) ⟨404045, by rfl⟩ : syracuseStep 538727 = 808091) B808091
theorem B768287 : Blo 358757 768287 := bstep (se 1 (by rfl) ⟨576215, by rfl⟩ : syracuseStep 768287 = 1152431) B1152431
theorem B1161503 : Blo 358757 1161503 := bstep (se 1 (by rfl) ⟨871127, by rfl⟩ : syracuseStep 1161503 = 1742255) B1742255
theorem B539111 : Blo 358757 539111 := bstep (se 1 (by rfl) ⟨404333, by rfl⟩ : syracuseStep 539111 = 808667) B808667
theorem B10598951 : Blo 358757 10598951 := bstep (se 1 (by rfl) ⟨7949213, by rfl⟩ : syracuseStep 10598951 = 15898427) B15898427
theorem B539183 : Blo 358757 539183 := bstep (se 1 (by rfl) ⟨404387, by rfl⟩ : syracuseStep 539183 = 808775) B808775
theorem B2734721 : Blo 358757 2734721 := bstep (se 2 (by rfl) ⟨1025520, by rfl⟩ : syracuseStep 2734721 = 2051041) B2051041
theorem B3455905 : Blo 358757 3455905 := bstep (se 2 (by rfl) ⟨1295964, by rfl⟩ : syracuseStep 3455905 = 2591929) B2591929
theorem B4602905 : Blo 358757 4602905 := bstep (se 2 (by rfl) ⟨1726089, by rfl⟩ : syracuseStep 4602905 = 3452179) B3452179
theorem B539855 : Blo 358757 539855 := bstep (se 1 (by rfl) ⟨404891, by rfl⟩ : syracuseStep 539855 = 809783) B809783
theorem B539945 : Blo 358757 539945 := bstep (se 2 (by rfl) ⟨202479, by rfl⟩ : syracuseStep 539945 = 404959) B404959
theorem B539975 : Blo 358757 539975 := bstep (se 1 (by rfl) ⟨404981, by rfl⟩ : syracuseStep 539975 = 809963) B809963
theorem B6176087 : Blo 358757 6176087 := bstep (se 1 (by rfl) ⟨4632065, by rfl⟩ : syracuseStep 6176087 = 9264131) B9264131
theorem B605947 : Blo 358757 605947 := bstep (se 1 (by rfl) ⟨454460, by rfl⟩ : syracuseStep 605947 = 908921) B908921
theorem B540575 : Blo 358757 540575 := bstep (se 1 (by rfl) ⟨405431, by rfl⟩ : syracuseStep 540575 = 810863) B810863
theorem B540665 : Blo 358757 540665 := bstep (se 2 (by rfl) ⟨202749, by rfl⟩ : syracuseStep 540665 = 405499) B405499
theorem B540809 : Blo 358757 540809 := bstep (se 2 (by rfl) ⟨202803, by rfl⟩ : syracuseStep 540809 = 405607) B405607
theorem B540905 : Blo 358757 540905 := bstep (se 2 (by rfl) ⟨202839, by rfl⟩ : syracuseStep 540905 = 405679) B405679
theorem B541031 : Blo 358757 541031 := bstep (se 1 (by rfl) ⟨405773, by rfl⟩ : syracuseStep 541031 = 811547) B811547
theorem B541151 : Blo 358757 541151 := bstep (se 1 (by rfl) ⟨405863, by rfl⟩ : syracuseStep 541151 = 811727) B811727
theorem B1294841 : Blo 358757 1294841 := bstep (se 2 (by rfl) ⟨485565, by rfl⟩ : syracuseStep 1294841 = 971131) B971131
theorem B541403 : Blo 358757 541403 := bstep (se 1 (by rfl) ⟨406052, by rfl⟩ : syracuseStep 541403 = 812105) B812105
theorem B541817 : Blo 358757 541817 := bstep (se 2 (by rfl) ⟨203181, by rfl⟩ : syracuseStep 541817 = 406363) B406363
theorem B542015 : Blo 358757 542015 := bstep (se 1 (by rfl) ⟨406511, by rfl⟩ : syracuseStep 542015 = 813023) B813023
theorem B607655 : Blo 358757 607655 := bstep (se 1 (by rfl) ⟨455741, by rfl⟩ : syracuseStep 607655 = 911483) B911483
theorem B607817 : Blo 358757 607817 := bstep (se 2 (by rfl) ⟨227931, by rfl⟩ : syracuseStep 607817 = 455863) B455863
theorem B542687 : Blo 358757 542687 := bstep (se 1 (by rfl) ⟨407015, by rfl⟩ : syracuseStep 542687 = 814031) B814031
theorem B542747 : Blo 358757 542747 := bstep (se 1 (by rfl) ⟨407060, by rfl⟩ : syracuseStep 542747 = 814121) B814121
theorem B4114475 : Blo 358757 4114475 := bstep (se 1 (by rfl) ⟨3085856, by rfl⟩ : syracuseStep 4114475 = 6171713) B6171713
theorem B608377 : Blo 358757 608377 := bstep (se 2 (by rfl) ⟨228141, by rfl⟩ : syracuseStep 608377 = 456283) B456283
theorem B3262619 : Blo 358757 3262619 := bstep (se 1 (by rfl) ⟨2446964, by rfl⟩ : syracuseStep 3262619 = 4893929) B4893929
theorem B542903 : Blo 358757 542903 := bstep (se 1 (by rfl) ⟨407177, by rfl⟩ : syracuseStep 542903 = 814355) B814355
theorem B542927 : Blo 358757 542927 := bstep (se 1 (by rfl) ⟨407195, by rfl⟩ : syracuseStep 542927 = 814391) B814391
theorem B543323 : Blo 358757 543323 := bstep (se 1 (by rfl) ⟨407492, by rfl⟩ : syracuseStep 543323 = 814985) B814985
theorem B1854089 : Blo 358757 1854089 := bstep (se 2 (by rfl) ⟨695283, by rfl⟩ : syracuseStep 1854089 = 1390567) B1390567
theorem B543467 : Blo 358757 543467 := bstep (se 1 (by rfl) ⟨407600, by rfl⟩ : syracuseStep 543467 = 815201) B815201
theorem B543497 : Blo 358757 543497 := bstep (se 2 (by rfl) ⟨203811, by rfl⟩ : syracuseStep 543497 = 407623) B407623
theorem B543911 : Blo 358757 543911 := bstep (se 1 (by rfl) ⟨407933, by rfl⟩ : syracuseStep 543911 = 815867) B815867
theorem B544055 : Blo 358757 544055 := bstep (se 1 (by rfl) ⟨408041, by rfl⟩ : syracuseStep 544055 = 816083) B816083
theorem B511439 : Blo 358757 511439 := bstep (se 1 (by rfl) ⟨383579, by rfl⟩ : syracuseStep 511439 = 767159) B767159
theorem B3689975 : Blo 358757 3689975 := bstep (se 1 (by rfl) ⟨2767481, by rfl⟩ : syracuseStep 3689975 = 5534963) B5534963
theorem B7786165 : Blo 358757 7786165 := bstep (se 5 (by rfl) ⟨364976, by rfl⟩ : syracuseStep 7786165 = 729953) B729953
theorem B511753 : Blo 358757 511753 := bstep (se 2 (by rfl) ⟨191907, by rfl⟩ : syracuseStep 511753 = 383815) B383815
theorem B577343 : Blo 358757 577343 := bstep (se 1 (by rfl) ⟨433007, by rfl⟩ : syracuseStep 577343 = 866015) B866015
theorem B4739111 : Blo 358757 4739111 := bstep (se 1 (by rfl) ⟨3554333, by rfl⟩ : syracuseStep 4739111 = 7108667) B7108667
theorem B774191 : Blo 358757 774191 := bstep (se 1 (by rfl) ⟨580643, by rfl⟩ : syracuseStep 774191 = 1161287) B1161287
theorem B2314291 : Blo 358757 2314291 := bstep (se 1 (by rfl) ⟨1735718, by rfl⟩ : syracuseStep 2314291 = 3471437) B3471437
theorem B2184023 : Blo 358757 2184023 := bstep (se 1 (by rfl) ⟨1638017, by rfl⟩ : syracuseStep 2184023 = 3276035) B3276035
theorem B13161365 : Blo 358757 13161365 := bstep (se 6 (by rfl) ⟨308469, by rfl⟩ : syracuseStep 13161365 = 616939) B616939
theorem B546103 : Blo 358757 546103 := bstep (se 1 (by rfl) ⟨409577, by rfl⟩ : syracuseStep 546103 = 819155) B819155
theorem B1824281 : Blo 358757 1824281 := bstep (se 2 (by rfl) ⟨684105, by rfl⟩ : syracuseStep 1824281 = 1368211) B1368211
theorem B2086603 : Blo 358757 2086603 := bstep (se 1 (by rfl) ⟨1564952, by rfl⟩ : syracuseStep 2086603 = 3129905) B3129905
theorem B1365767 : Blo 358757 1365767 := bstep (se 1 (by rfl) ⟨1024325, by rfl⟩ : syracuseStep 1365767 = 2048651) B2048651
theorem B2611073 : Blo 358757 2611073 := bstep (se 2 (by rfl) ⟨979152, by rfl⟩ : syracuseStep 2611073 = 1958305) B1958305
theorem B808847 : Blo 358757 808847 := bstep (se 1 (by rfl) ⟨606635, by rfl⟩ : syracuseStep 808847 = 1213271) B1213271
theorem B2054483 : Blo 358757 2054483 := bstep (se 1 (by rfl) ⟨1540862, by rfl⟩ : syracuseStep 2054483 = 3081725) B3081725
theorem B809567 : Blo 358757 809567 := bstep (se 1 (by rfl) ⟨607175, by rfl⟩ : syracuseStep 809567 = 1214351) B1214351
theorem B7789547 : Blo 358757 7789547 := bstep (se 1 (by rfl) ⟨5842160, by rfl⟩ : syracuseStep 7789547 = 11684321) B11684321
theorem B810089 : Blo 358757 810089 := bstep (se 2 (by rfl) ⟨303783, by rfl⟩ : syracuseStep 810089 = 607567) B607567
theorem B1367239 : Blo 358757 1367239 := bstep (se 1 (by rfl) ⟨1025429, by rfl⟩ : syracuseStep 1367239 = 2050859) B2050859
theorem B1465553 : Blo 358757 1465553 := bstep (se 2 (by rfl) ⟨549582, by rfl⟩ : syracuseStep 1465553 = 1099165) B1099165
theorem B908617 : Blo 358757 908617 := bstep (se 2 (by rfl) ⟨340731, by rfl⟩ : syracuseStep 908617 = 681463) B681463
theorem B613759 : Blo 358757 613759 := bstep (se 1 (by rfl) ⟨460319, by rfl⟩ : syracuseStep 613759 = 920639) B920639
theorem B6938257 : Blo 358757 6938257 := bstep (se 2 (by rfl) ⟨2601846, by rfl⟩ : syracuseStep 6938257 = 5203693) B5203693
theorem B810719 : Blo 358757 810719 := bstep (se 1 (by rfl) ⟨608039, by rfl⟩ : syracuseStep 810719 = 1216079) B1216079
theorem B516007 : Blo 358757 516007 := bstep (se 1 (by rfl) ⟨387005, by rfl⟩ : syracuseStep 516007 = 774011) B774011
theorem B811079 : Blo 358757 811079 := bstep (se 1 (by rfl) ⟨608309, by rfl⟩ : syracuseStep 811079 = 1216619) B1216619
theorem B811115 : Blo 358757 811115 := bstep (se 1 (by rfl) ⟨608336, by rfl⟩ : syracuseStep 811115 = 1216673) B1216673
theorem B13132151 : Blo 358757 13132151 := bstep (se 1 (by rfl) ⟨9849113, by rfl⟩ : syracuseStep 13132151 = 19698227) B19698227
theorem B811385 : Blo 358757 811385 := bstep (se 2 (by rfl) ⟨304269, by rfl⟩ : syracuseStep 811385 = 608539) B608539
theorem B4088231 : Blo 358757 4088231 := bstep (se 1 (by rfl) ⟨3066173, by rfl⟩ : syracuseStep 4088231 = 6132347) B6132347
theorem B2613671 : Blo 358757 2613671 := bstep (se 1 (by rfl) ⟨1960253, by rfl⟩ : syracuseStep 2613671 = 3920507) B3920507
theorem B1368683 : Blo 358757 1368683 := bstep (se 1 (by rfl) ⟨1026512, by rfl⟩ : syracuseStep 1368683 = 2053025) B2053025
theorem B811817 : Blo 358757 811817 := bstep (se 2 (by rfl) ⟨304431, by rfl⟩ : syracuseStep 811817 = 608863) B608863
theorem B812015 : Blo 358757 812015 := bstep (se 1 (by rfl) ⟨609011, by rfl⟩ : syracuseStep 812015 = 1218023) B1218023
theorem B812087 : Blo 358757 812087 := bstep (se 1 (by rfl) ⟨609065, by rfl⟩ : syracuseStep 812087 = 1218131) B1218131
theorem B1828007 : Blo 358757 1828007 := bstep (se 1 (by rfl) ⟨1371005, by rfl⟩ : syracuseStep 1828007 = 2742011) B2742011
theorem B812267 : Blo 358757 812267 := bstep (se 1 (by rfl) ⟨609200, by rfl⟩ : syracuseStep 812267 = 1218401) B1218401
theorem B910703 : Blo 358757 910703 := bstep (se 1 (by rfl) ⟨683027, by rfl⟩ : syracuseStep 910703 = 1366055) B1366055
theorem B4941587 : Blo 358757 4941587 := bstep (se 1 (by rfl) ⟨3706190, by rfl⟩ : syracuseStep 4941587 = 7412381) B7412381
theorem B681851 : Blo 358757 681851 := bstep (se 1 (by rfl) ⟨511388, by rfl⟩ : syracuseStep 681851 = 1022777) B1022777
theorem B583583 : Blo 358757 583583 := bstep (se 1 (by rfl) ⟨437687, by rfl⟩ : syracuseStep 583583 = 875375) B875375
theorem B1468327 : Blo 358757 1468327 := bstep (se 1 (by rfl) ⟨1101245, by rfl⟩ : syracuseStep 1468327 = 2202491) B2202491
theorem B1304531 : Blo 358757 1304531 := bstep (se 1 (by rfl) ⟨978398, by rfl⟩ : syracuseStep 1304531 = 1956797) B1956797
theorem B911695 : Blo 358757 911695 := bstep (se 1 (by rfl) ⟨683771, by rfl⟩ : syracuseStep 911695 = 1367543) B1367543
theorem B1337719 : Blo 358757 1337719 := bstep (se 1 (by rfl) ⟨1003289, by rfl⟩ : syracuseStep 1337719 = 2006579) B2006579
theorem B4123223 : Blo 358757 4123223 := bstep (se 1 (by rfl) ⟨3092417, by rfl⟩ : syracuseStep 4123223 = 6184835) B6184835
theorem B1305191 : Blo 358757 1305191 := bstep (se 1 (by rfl) ⟨978893, by rfl⟩ : syracuseStep 1305191 = 1957787) B1957787
theorem B2058857 : Blo 358757 2058857 := bstep (se 2 (by rfl) ⟨772071, by rfl⟩ : syracuseStep 2058857 = 1544143) B1544143
theorem B1371401 : Blo 358757 1371401 := bstep (se 2 (by rfl) ⟨514275, by rfl⟩ : syracuseStep 1371401 = 1028551) B1028551
theorem B1175273 : Blo 358757 1175273 := bstep (se 2 (by rfl) ⟨440727, by rfl⟩ : syracuseStep 1175273 = 881455) B881455
theorem B1830761 : Blo 358757 1830761 := bstep (se 2 (by rfl) ⟨686535, by rfl⟩ : syracuseStep 1830761 = 1373071) B1373071
theorem B1372099 : Blo 358757 1372099 := bstep (se 1 (by rfl) ⟨1029074, by rfl⟩ : syracuseStep 1372099 = 2058149) B2058149
theorem B2977769 : Blo 358757 2977769 := bstep (se 2 (by rfl) ⟨1116663, by rfl⟩ : syracuseStep 2977769 = 2233327) B2233327
theorem B4124681 : Blo 358757 4124681 := bstep (se 2 (by rfl) ⟨1546755, by rfl⟩ : syracuseStep 4124681 = 3093511) B3093511
theorem B913639 : Blo 358757 913639 := bstep (se 1 (by rfl) ⟨685229, by rfl⟩ : syracuseStep 913639 = 1370459) B1370459
theorem B18641441 : Blo 358757 18641441 := bstep (se 2 (by rfl) ⟨6990540, by rfl⟩ : syracuseStep 18641441 = 13981081) B13981081
theorem B684911 : Blo 358757 684911 := bstep (se 1 (by rfl) ⟨513683, by rfl⟩ : syracuseStep 684911 = 1027367) B1027367
theorem B815993 : Blo 358757 815993 := bstep (se 2 (by rfl) ⟨305997, by rfl⟩ : syracuseStep 815993 = 611995) B611995
theorem B1373057 : Blo 358757 1373057 := bstep (se 2 (by rfl) ⟨514896, by rfl⟩ : syracuseStep 1373057 = 1029793) B1029793
theorem B1831895 : Blo 358757 1831895 := bstep (se 1 (by rfl) ⟨1373921, by rfl⟩ : syracuseStep 1831895 = 2747843) B2747843
theorem B8615159 : Blo 358757 8615159 := bstep (se 1 (by rfl) ⟨6461369, by rfl⟩ : syracuseStep 8615159 = 12922739) B12922739
theorem B7796897 : Blo 358757 7796897 := bstep (se 2 (by rfl) ⟨2923836, by rfl⟩ : syracuseStep 7796897 = 5847673) B5847673
theorem B1046719 : Blo 358757 1046719 := bstep (se 1 (by rfl) ⟨785039, by rfl⟩ : syracuseStep 1046719 = 1570079) B1570079
theorem B1603997 : Blo 358757 1603997 := bstep (se 3 (by rfl) ⟨300749, by rfl⟩ : syracuseStep 1603997 = 601499) B601499
theorem B4159993 : Blo 358757 4159993 := bstep (se 2 (by rfl) ⟨1559997, by rfl⟩ : syracuseStep 4159993 = 3119995) B3119995
theorem B686855 : Blo 358757 686855 := bstep (se 1 (by rfl) ⟨515141, by rfl⟩ : syracuseStep 686855 = 1030283) B1030283
theorem B4127597 : Blo 358757 4127597 := bstep (se 3 (by rfl) ⟨773924, by rfl⟩ : syracuseStep 4127597 = 1547849) B1547849
theorem B28146653 : Blo 358757 28146653 := bstep (se 3 (by rfl) ⟨5277497, by rfl⟩ : syracuseStep 28146653 = 10554995) B10554995
theorem B359391 : Blo 358757 359391 := bstep (se 1 (by rfl) ⟨269543, by rfl⟩ : syracuseStep 359391 = 539087) B539087
theorem B359451 : Blo 358757 359451 := bstep (se 1 (by rfl) ⟨269588, by rfl⟩ : syracuseStep 359451 = 539177) B539177
theorem B359579 : Blo 358757 359579 := bstep (se 1 (by rfl) ⟨269684, by rfl⟩ : syracuseStep 359579 = 539369) B539369
theorem B359835 : Blo 358757 359835 := bstep (se 1 (by rfl) ⟨269876, by rfl⟩ : syracuseStep 359835 = 539753) B539753
theorem B359919 : Blo 358757 359919 := bstep (se 1 (by rfl) ⟨269939, by rfl⟩ : syracuseStep 359919 = 539879) B539879
theorem B687599 : Blo 358757 687599 := bstep (se 1 (by rfl) ⟨515699, by rfl⟩ : syracuseStep 687599 = 1031399) B1031399
theorem B3309167 : Blo 358757 3309167 := bstep (se 1 (by rfl) ⟨2481875, by rfl⟩ : syracuseStep 3309167 = 4963751) B4963751
theorem B1834649 : Blo 358757 1834649 := bstep (se 2 (by rfl) ⟨687993, by rfl⟩ : syracuseStep 1834649 = 1375987) B1375987
theorem B360255 : Blo 358757 360255 := bstep (se 1 (by rfl) ⟨270191, by rfl⟩ : syracuseStep 360255 = 540383) B540383
theorem B360283 : Blo 358757 360283 := bstep (se 1 (by rfl) ⟨270212, by rfl⟩ : syracuseStep 360283 = 540425) B540425
theorem B360539 : Blo 358757 360539 := bstep (se 1 (by rfl) ⟨270404, by rfl⟩ : syracuseStep 360539 = 540809) B540809
theorem B1835135 : Blo 358757 1835135 := bstep (se 1 (by rfl) ⟨1376351, by rfl⟩ : syracuseStep 1835135 = 2752703) B2752703
theorem B360603 : Blo 358757 360603 := bstep (se 1 (by rfl) ⟨270452, by rfl⟩ : syracuseStep 360603 = 540905) B540905
theorem B360687 : Blo 358757 360687 := bstep (se 1 (by rfl) ⟨270515, by rfl⟩ : syracuseStep 360687 = 541031) B541031
theorem B360767 : Blo 358757 360767 := bstep (se 1 (by rfl) ⟨270575, by rfl⟩ : syracuseStep 360767 = 541151) B541151
theorem B1311137 : Blo 358757 1311137 := bstep (se 2 (by rfl) ⟨491676, by rfl⟩ : syracuseStep 1311137 = 983353) B983353
theorem B360935 : Blo 358757 360935 := bstep (se 1 (by rfl) ⟨270701, by rfl⟩ : syracuseStep 360935 = 541403) B541403
theorem B361211 : Blo 358757 361211 := bstep (se 1 (by rfl) ⟨270908, by rfl⟩ : syracuseStep 361211 = 541817) B541817
theorem B31687433 : Blo 358757 31687433 := bstep (se 2 (by rfl) ⟨11882787, by rfl⟩ : syracuseStep 31687433 = 23765575) B23765575
theorem B1508219 : Blo 358757 1508219 := bstep (se 1 (by rfl) ⟨1131164, by rfl⟩ : syracuseStep 1508219 = 2262329) B2262329
theorem B361343 : Blo 358757 361343 := bstep (se 1 (by rfl) ⟨271007, by rfl⟩ : syracuseStep 361343 = 542015) B542015
theorem B24970463 : Blo 358757 24970463 := bstep (se 1 (by rfl) ⟨18727847, by rfl⟩ : syracuseStep 24970463 = 37455695) B37455695
theorem B361791 : Blo 358757 361791 := bstep (se 1 (by rfl) ⟨271343, by rfl⟩ : syracuseStep 361791 = 542687) B542687
theorem B361831 : Blo 358757 361831 := bstep (se 1 (by rfl) ⟨271373, by rfl⟩ : syracuseStep 361831 = 542747) B542747
theorem B361935 : Blo 358757 361935 := bstep (se 1 (by rfl) ⟨271451, by rfl⟩ : syracuseStep 361935 = 542903) B542903
theorem B361951 : Blo 358757 361951 := bstep (se 1 (by rfl) ⟨271463, by rfl⟩ : syracuseStep 361951 = 542927) B542927
theorem B362215 : Blo 358757 362215 := bstep (se 1 (by rfl) ⟨271661, by rfl⟩ : syracuseStep 362215 = 543323) B543323
theorem B362311 : Blo 358757 362311 := bstep (se 1 (by rfl) ⟨271733, by rfl⟩ : syracuseStep 362311 = 543467) B543467
theorem B362331 : Blo 358757 362331 := bstep (se 1 (by rfl) ⟨271748, by rfl⟩ : syracuseStep 362331 = 543497) B543497
theorem B362607 : Blo 358757 362607 := bstep (se 1 (by rfl) ⟨271955, by rfl⟩ : syracuseStep 362607 = 543911) B543911
theorem B362703 : Blo 358757 362703 := bstep (se 1 (by rfl) ⟨272027, by rfl⟩ : syracuseStep 362703 = 544055) B544055
theorem B2459983 : Blo 358757 2459983 := bstep (se 1 (by rfl) ⟨1844987, by rfl⟩ : syracuseStep 2459983 = 3689975) B3689975
theorem B2919037 : Blo 358757 2919037 := bstep (se 3 (by rfl) ⟨547319, by rfl⟩ : syracuseStep 2919037 = 1094639) B1094639
theorem B1215593 : Blo 358757 1215593 := bstep (se 2 (by rfl) ⟨455847, by rfl⟩ : syracuseStep 1215593 = 911695) B911695
theorem B1216187 : Blo 358757 1216187 := bstep (se 1 (by rfl) ⟨912140, by rfl⟩ : syracuseStep 1216187 = 1824281) B1824281
theorem B1544417 : Blo 358757 1544417 := bstep (se 2 (by rfl) ⟨579156, by rfl⟩ : syracuseStep 1544417 = 1158313) B1158313
theorem B922043 : Blo 358757 922043 := bstep (se 1 (by rfl) ⟨691532, by rfl⟩ : syracuseStep 922043 = 1383065) B1383065
theorem B13177565 : Blo 358757 13177565 := bstep (se 3 (by rfl) ⟨2470793, by rfl⟩ : syracuseStep 13177565 = 4941587) B4941587
theorem B604771093 : Blo 358757 604771093 := bstep (se 6 (by rfl) ⟨14174322, by rfl⟩ : syracuseStep 604771093 = 28348645) B28348645
theorem B2364191 : Blo 358757 2364191 := bstep (se 1 (by rfl) ⟨1773143, by rfl⟩ : syracuseStep 2364191 = 3546287) B3546287
theorem B3085721 : Blo 358757 3085721 := bstep (se 2 (by rfl) ⟨1157145, by rfl⟩ : syracuseStep 3085721 = 2314291) B2314291
theorem B8754767 : Blo 358757 8754767 := bstep (se 1 (by rfl) ⟨6566075, by rfl⟩ : syracuseStep 8754767 = 13132151) B13132151
theorem B2725487 : Blo 358757 2725487 := bstep (se 1 (by rfl) ⟨2044115, by rfl⟩ : syracuseStep 2725487 = 4088231) B4088231
theorem B1742447 : Blo 358757 1742447 := bstep (se 1 (by rfl) ⟨1306835, by rfl⟩ : syracuseStep 1742447 = 2613671) B2613671
theorem B1218185 : Blo 358757 1218185 := bstep (se 2 (by rfl) ⟨456819, by rfl⟩ : syracuseStep 1218185 = 913639) B913639
theorem B1218671 : Blo 358757 1218671 := bstep (se 1 (by rfl) ⟨914003, by rfl⟩ : syracuseStep 1218671 = 1828007) B1828007
theorem B3480509 : Blo 358757 3480509 := bstep (se 3 (by rfl) ⟨652595, by rfl⟩ : syracuseStep 3480509 = 1305191) B1305191
theorem B728137 : Blo 358757 728137 := bstep (se 2 (by rfl) ⟨273051, by rfl⟩ : syracuseStep 728137 = 546103) B546103
theorem B1220507 : Blo 358757 1220507 := bstep (se 1 (by rfl) ⟨915380, by rfl⟩ : syracuseStep 1220507 = 1830761) B1830761
theorem B2727917 : Blo 358757 2727917 := bstep (se 3 (by rfl) ⟨511484, by rfl⟩ : syracuseStep 2727917 = 1022969) B1022969
theorem B729143 : Blo 358757 729143 := bstep (se 1 (by rfl) ⟨546857, by rfl⟩ : syracuseStep 729143 = 1093715) B1093715
theorem B3940595 : Blo 358757 3940595 := bstep (se 1 (by rfl) ⟨2955446, by rfl⟩ : syracuseStep 3940595 = 5910893) B5910893
theorem B12427627 : Blo 358757 12427627 := bstep (se 1 (by rfl) ⟨9320720, by rfl⟩ : syracuseStep 12427627 = 18641441) B18641441
theorem B1221263 : Blo 358757 1221263 := bstep (se 1 (by rfl) ⟨915947, by rfl⟩ : syracuseStep 1221263 = 1831895) B1831895
theorem B5546657 : Blo 358757 5546657 := bstep (se 2 (by rfl) ⟨2079996, by rfl⟩ : syracuseStep 5546657 = 4159993) B4159993
theorem B5743439 : Blo 358757 5743439 := bstep (se 1 (by rfl) ⟨4307579, by rfl⟩ : syracuseStep 5743439 = 8615159) B8615159
theorem B9251009 : Blo 358757 9251009 := bstep (se 2 (by rfl) ⟨3469128, by rfl⟩ : syracuseStep 9251009 = 6938257) B6938257
theorem B2206111 : Blo 358757 2206111 := bstep (se 1 (by rfl) ⟨1654583, by rfl⟩ : syracuseStep 2206111 = 3309167) B3309167
theorem B1223099 : Blo 358757 1223099 := bstep (se 1 (by rfl) ⟨917324, by rfl⟩ : syracuseStep 1223099 = 1834649) B1834649
theorem B7940717 : Blo 358757 7940717 := bstep (se 3 (by rfl) ⟨1488884, by rfl⟩ : syracuseStep 7940717 = 2977769) B2977769
theorem B14035913 : Blo 358757 14035913 := bstep (se 2 (by rfl) ⟨5263467, by rfl⟩ : syracuseStep 14035913 = 10526935) B10526935
theorem B863227 : Blo 358757 863227 := bstep (se 1 (by rfl) ⟨647420, by rfl⟩ : syracuseStep 863227 = 1294841) B1294841
theorem B2731319 : Blo 358757 2731319 := bstep (se 1 (by rfl) ⟨2048489, by rfl⟩ : syracuseStep 2731319 = 4096979) B4096979
theorem B405103 : Blo 358757 405103 := bstep (se 1 (by rfl) ⟨303827, by rfl⟩ : syracuseStep 405103 = 607655) B607655
theorem B405211 : Blo 358757 405211 := bstep (se 1 (by rfl) ⟨303908, by rfl⟩ : syracuseStep 405211 = 607817) B607817
theorem B2731805 : Blo 358757 2731805 := bstep (se 3 (by rfl) ⟨512213, by rfl⟩ : syracuseStep 2731805 = 1024427) B1024427
theorem B3453137 : Blo 358757 3453137 := bstep (se 2 (by rfl) ⟨1294926, by rfl⟩ : syracuseStep 3453137 = 2589853) B2589853
theorem B2470823 : Blo 358757 2470823 := bstep (se 1 (by rfl) ⟨1853117, by rfl⟩ : syracuseStep 2470823 = 3706235) B3706235
theorem B2143219 : Blo 358757 2143219 := bstep (se 1 (by rfl) ⟨1607414, by rfl⟩ : syracuseStep 2143219 = 3214829) B3214829
theorem B3159407 : Blo 358757 3159407 := bstep (se 1 (by rfl) ⟨2369555, by rfl⟩ : syracuseStep 3159407 = 4739111) B4739111
theorem B1783625 : Blo 358757 1783625 := bstep (se 2 (by rfl) ⟨668859, by rfl⟩ : syracuseStep 1783625 = 1337719) B1337719
theorem B1456015 : Blo 358757 1456015 := bstep (se 1 (by rfl) ⟨1092011, by rfl⟩ : syracuseStep 1456015 = 2184023) B2184023
theorem B538601 : Blo 358757 538601 := bstep (se 2 (by rfl) ⟨201975, by rfl⟩ : syracuseStep 538601 = 403951) B403951
theorem B539231 : Blo 358757 539231 := bstep (se 1 (by rfl) ⟨404423, by rfl⟩ : syracuseStep 539231 = 808847) B808847
theorem B539711 : Blo 358757 539711 := bstep (se 1 (by rfl) ⟨404783, by rfl⟩ : syracuseStep 539711 = 809567) B809567
theorem B5193031 : Blo 358757 5193031 := bstep (se 1 (by rfl) ⟨3894773, by rfl⟩ : syracuseStep 5193031 = 7789547) B7789547
theorem B540059 : Blo 358757 540059 := bstep (se 1 (by rfl) ⟨405044, by rfl⟩ : syracuseStep 540059 = 810089) B810089
theorem B6962861 : Blo 358757 6962861 := bstep (se 3 (by rfl) ⟨1305536, by rfl⟩ : syracuseStep 6962861 = 2611073) B2611073
theorem B1556221 : Blo 358757 1556221 := bstep (se 3 (by rfl) ⟨291791, by rfl⟩ : syracuseStep 1556221 = 583583) B583583
theorem B540479 : Blo 358757 540479 := bstep (se 1 (by rfl) ⟨405359, by rfl⟩ : syracuseStep 540479 = 810719) B810719
theorem B540719 : Blo 358757 540719 := bstep (se 1 (by rfl) ⟨405539, by rfl⟩ : syracuseStep 540719 = 811079) B811079
theorem B540743 : Blo 358757 540743 := bstep (se 1 (by rfl) ⟨405557, by rfl⟩ : syracuseStep 540743 = 811115) B811115
theorem B3326035 : Blo 358757 3326035 := bstep (se 1 (by rfl) ⟨2494526, by rfl⟩ : syracuseStep 3326035 = 4989053) B4989053
theorem B540923 : Blo 358757 540923 := bstep (se 1 (by rfl) ⟨405692, by rfl⟩ : syracuseStep 540923 = 811385) B811385
theorem B541049 : Blo 358757 541049 := bstep (se 2 (by rfl) ⟨202893, by rfl⟩ : syracuseStep 541049 = 405787) B405787
theorem B11649419 : Blo 358757 11649419 := bstep (se 1 (by rfl) ⟨8737064, by rfl⟩ : syracuseStep 11649419 = 17474129) B17474129
theorem B8700317 : Blo 358757 8700317 := bstep (se 3 (by rfl) ⟨1631309, by rfl⟩ : syracuseStep 8700317 = 3262619) B3262619
theorem B541211 : Blo 358757 541211 := bstep (se 1 (by rfl) ⟨405908, by rfl⟩ : syracuseStep 541211 = 811817) B811817
theorem B541343 : Blo 358757 541343 := bstep (se 1 (by rfl) ⟨406007, by rfl⟩ : syracuseStep 541343 = 812015) B812015
theorem B541391 : Blo 358757 541391 := bstep (se 1 (by rfl) ⟨406043, by rfl⟩ : syracuseStep 541391 = 812087) B812087
theorem B541511 : Blo 358757 541511 := bstep (se 1 (by rfl) ⟨406133, by rfl⟩ : syracuseStep 541511 = 812267) B812267
theorem B541577 : Blo 358757 541577 := bstep (se 2 (by rfl) ⟨203091, by rfl⟩ : syracuseStep 541577 = 406183) B406183
theorem B607135 : Blo 358757 607135 := bstep (se 1 (by rfl) ⟨455351, by rfl⟩ : syracuseStep 607135 = 910703) B910703
theorem B869687 : Blo 358757 869687 := bstep (se 1 (by rfl) ⟨652265, by rfl⟩ : syracuseStep 869687 = 1304531) B1304531
theorem B1099919 : Blo 358757 1099919 := bstep (se 1 (by rfl) ⟨824939, by rfl⟩ : syracuseStep 1099919 = 1649879) B1649879
theorem B2607383 : Blo 358757 2607383 := bstep (se 1 (by rfl) ⟨1955537, by rfl⟩ : syracuseStep 2607383 = 3911075) B3911075
theorem B1395625 : Blo 358757 1395625 := bstep (se 2 (by rfl) ⟨523359, by rfl⟩ : syracuseStep 1395625 = 1046719) B1046719
theorem B773327 : Blo 358757 773327 := bstep (se 1 (by rfl) ⟨579995, by rfl⟩ : syracuseStep 773327 = 1159991) B1159991
theorem B1363169 : Blo 358757 1363169 := bstep (se 2 (by rfl) ⟨511188, by rfl⟩ : syracuseStep 1363169 = 1022377) B1022377
theorem B543995 : Blo 358757 543995 := bstep (se 1 (by rfl) ⟨407996, by rfl⟩ : syracuseStep 543995 = 815993) B815993
theorem B11128549 : Blo 358757 11128549 := bstep (se 4 (by rfl) ⟨1043301, by rfl⟩ : syracuseStep 11128549 = 2086603) B2086603
theorem B1363837 : Blo 358757 1363837 := bstep (se 3 (by rfl) ⟨255719, by rfl⟩ : syracuseStep 1363837 = 511439) B511439
theorem B4607873 : Blo 358757 4607873 := bstep (se 2 (by rfl) ⟨1727952, by rfl⟩ : syracuseStep 4607873 = 3455905) B3455905
theorem B577471 : Blo 358757 577471 := bstep (se 1 (by rfl) ⟨433103, by rfl⟩ : syracuseStep 577471 = 866207) B866207
theorem B5197931 : Blo 358757 5197931 := bstep (se 1 (by rfl) ⟨3898448, by rfl⟩ : syracuseStep 5197931 = 7796897) B7796897
theorem B512191 : Blo 358757 512191 := bstep (se 1 (by rfl) ⟨384143, by rfl⟩ : syracuseStep 512191 = 768287) B768287
theorem B774335 : Blo 358757 774335 := bstep (se 1 (by rfl) ⟨580751, by rfl⟩ : syracuseStep 774335 = 1161503) B1161503
theorem B1822985 : Blo 358757 1822985 := bstep (se 2 (by rfl) ⟨683619, by rfl⟩ : syracuseStep 1822985 = 1367239) B1367239
theorem B1069331 : Blo 358757 1069331 := bstep (se 1 (by rfl) ⟨801998, by rfl⟩ : syracuseStep 1069331 = 1603997) B1603997
theorem B7065967 : Blo 358757 7065967 := bstep (se 1 (by rfl) ⟨5299475, by rfl⟩ : syracuseStep 7065967 = 10598951) B10598951
theorem B1823147 : Blo 358757 1823147 := bstep (se 1 (by rfl) ⟨1367360, by rfl⟩ : syracuseStep 1823147 = 2734721) B2734721
theorem B18764435 : Blo 358757 18764435 := bstep (se 1 (by rfl) ⟨14073326, by rfl⟩ : syracuseStep 18764435 = 28146653) B28146653
theorem B3068603 : Blo 358757 3068603 := bstep (se 1 (by rfl) ⟨2301452, by rfl⟩ : syracuseStep 3068603 = 4602905) B4602905
theorem B4117391 : Blo 358757 4117391 := bstep (se 1 (by rfl) ⟨3088043, by rfl⟩ : syracuseStep 4117391 = 6176087) B6176087
theorem B807929 : Blo 358757 807929 := bstep (se 2 (by rfl) ⟨302973, by rfl⟩ : syracuseStep 807929 = 605947) B605947
theorem B2053775 : Blo 358757 2053775 := bstep (se 1 (by rfl) ⟨1540331, by rfl⟩ : syracuseStep 2053775 = 3080663) B3080663
theorem B2742983 : Blo 358757 2742983 := bstep (se 1 (by rfl) ⟨2057237, by rfl⟩ : syracuseStep 2742983 = 4114475) B4114475
theorem B1236059 : Blo 358757 1236059 := bstep (se 1 (by rfl) ⟨927044, by rfl⟩ : syracuseStep 1236059 = 1854089) B1854089
theorem B1728107 : Blo 358757 1728107 := bstep (se 1 (by rfl) ⟨1296080, by rfl⟩ : syracuseStep 1728107 = 2592161) B2592161
theorem B384895 : Blo 358757 384895 := bstep (se 1 (by rfl) ⟨288671, by rfl⟩ : syracuseStep 384895 = 577343) B577343
theorem B1957769 : Blo 358757 1957769 := bstep (se 2 (by rfl) ⟨734163, by rfl⟩ : syracuseStep 1957769 = 1468327) B1468327
theorem B516127 : Blo 358757 516127 := bstep (se 1 (by rfl) ⟨387095, by rfl⟩ : syracuseStep 516127 = 774191) B774191
theorem B811169 : Blo 358757 811169 := bstep (se 2 (by rfl) ⟨304188, by rfl⟩ : syracuseStep 811169 = 608377) B608377
theorem B2318699 : Blo 358757 2318699 := bstep (se 1 (by rfl) ⟨1739024, by rfl⟩ : syracuseStep 2318699 = 3478049) B3478049
theorem B8774243 : Blo 358757 8774243 := bstep (se 1 (by rfl) ⟨6580682, by rfl⟩ : syracuseStep 8774243 = 13161365) B13161365
theorem B1729183 : Blo 358757 1729183 := bstep (se 1 (by rfl) ⟨1296887, by rfl⟩ : syracuseStep 1729183 = 2593775) B2593775
theorem B910511 : Blo 358757 910511 := bstep (se 1 (by rfl) ⟨682883, by rfl⟩ : syracuseStep 910511 = 1365767) B1365767
theorem B1369655 : Blo 358757 1369655 := bstep (se 1 (by rfl) ⟨1027241, by rfl⟩ : syracuseStep 1369655 = 2054483) B2054483
theorem B977035 : Blo 358757 977035 := bstep (se 1 (by rfl) ⟨732776, by rfl⟩ : syracuseStep 977035 = 1465553) B1465553
theorem B10381553 : Blo 358757 10381553 := bstep (se 2 (by rfl) ⟨3893082, by rfl⟩ : syracuseStep 10381553 = 7786165) B7786165
theorem B682337 : Blo 358757 682337 := bstep (se 2 (by rfl) ⟨255876, by rfl⟩ : syracuseStep 682337 = 511753) B511753
theorem B1829465 : Blo 358757 1829465 := bstep (se 2 (by rfl) ⟨686049, by rfl⟩ : syracuseStep 1829465 = 1372099) B1372099
theorem B682663 : Blo 358757 682663 := bstep (se 1 (by rfl) ⟨511997, by rfl⟩ : syracuseStep 682663 = 1023995) B1023995
theorem B912455 : Blo 358757 912455 := bstep (se 1 (by rfl) ⟨684341, by rfl⟩ : syracuseStep 912455 = 1368683) B1368683
theorem B3173807 : Blo 358757 3173807 := bstep (se 1 (by rfl) ⟨2380355, by rfl⟩ : syracuseStep 3173807 = 4760711) B4760711
theorem B683711 : Blo 358757 683711 := bstep (se 1 (by rfl) ⟨512783, by rfl⟩ : syracuseStep 683711 = 1025567) B1025567
theorem B1470143 : Blo 358757 1470143 := bstep (se 1 (by rfl) ⟨1102607, by rfl⟩ : syracuseStep 1470143 = 2205215) B2205215
theorem B978713 : Blo 358757 978713 := bstep (se 2 (by rfl) ⟨367017, by rfl⟩ : syracuseStep 978713 = 734035) B734035
theorem B2060063 : Blo 358757 2060063 := bstep (se 1 (by rfl) ⟨1545047, by rfl⟩ : syracuseStep 2060063 = 3090095) B3090095
theorem B454567 : Blo 358757 454567 := bstep (se 1 (by rfl) ⟨340925, by rfl⟩ : syracuseStep 454567 = 681851) B681851
theorem B2748815 : Blo 358757 2748815 := bstep (se 1 (by rfl) ⟨2061611, by rfl⟩ : syracuseStep 2748815 = 4123223) B4123223
theorem B1372571 : Blo 358757 1372571 := bstep (se 1 (by rfl) ⟨1029428, by rfl⟩ : syracuseStep 1372571 = 2058857) B2058857
theorem B1372585 : Blo 358757 1372585 := bstep (se 2 (by rfl) ⟨514719, by rfl⟩ : syracuseStep 1372585 = 1029439) B1029439
theorem B914267 : Blo 358757 914267 := bstep (se 1 (by rfl) ⟨685700, by rfl⟩ : syracuseStep 914267 = 1371401) B1371401
theorem B554111 : Blo 358757 554111 := bstep (se 1 (by rfl) ⟨415583, by rfl⟩ : syracuseStep 554111 = 831167) B831167
theorem B783515 : Blo 358757 783515 := bstep (se 1 (by rfl) ⟨587636, by rfl⟩ : syracuseStep 783515 = 1175273) B1175273
theorem B2061521 : Blo 358757 2061521 := bstep (se 2 (by rfl) ⟨773070, by rfl⟩ : syracuseStep 2061521 = 1546141) B1546141
theorem B2749787 : Blo 358757 2749787 := bstep (se 1 (by rfl) ⟨2062340, by rfl⟩ : syracuseStep 2749787 = 4124681) B4124681
theorem B456607 : Blo 358757 456607 := bstep (se 1 (by rfl) ⟨342455, by rfl⟩ : syracuseStep 456607 = 684911) B684911
theorem B915371 : Blo 358757 915371 := bstep (se 1 (by rfl) ⟨686528, by rfl⟩ : syracuseStep 915371 = 1373057) B1373057
theorem B358759 : Blo 358757 358759 := bstep (se 1 (by rfl) ⟨269069, by rfl⟩ : syracuseStep 358759 = 538139) B538139
theorem B358879 : Blo 358757 358879 := bstep (se 1 (by rfl) ⟨269159, by rfl⟩ : syracuseStep 358879 = 538319) B538319
theorem B359015 : Blo 358757 359015 := bstep (se 1 (by rfl) ⟨269261, by rfl⟩ : syracuseStep 359015 = 538523) B538523
theorem B359039 : Blo 358757 359039 := bstep (se 1 (by rfl) ⟨269279, by rfl⟩ : syracuseStep 359039 = 538559) B538559
theorem B359151 : Blo 358757 359151 := bstep (se 1 (by rfl) ⟨269363, by rfl⟩ : syracuseStep 359151 = 538727) B538727
theorem B359407 : Blo 358757 359407 := bstep (se 1 (by rfl) ⟨269555, by rfl⟩ : syracuseStep 359407 = 539111) B539111
theorem B359455 : Blo 358757 359455 := bstep (se 1 (by rfl) ⟨269591, by rfl⟩ : syracuseStep 359455 = 539183) B539183
theorem B1211489 : Blo 358757 1211489 := bstep (se 2 (by rfl) ⟨454308, by rfl⟩ : syracuseStep 1211489 = 908617) B908617
theorem B818345 : Blo 358757 818345 := bstep (se 2 (by rfl) ⟨306879, by rfl⟩ : syracuseStep 818345 = 613759) B613759
theorem B457903 : Blo 358757 457903 := bstep (se 1 (by rfl) ⟨343427, by rfl⟩ : syracuseStep 457903 = 686855) B686855
theorem B2751731 : Blo 358757 2751731 := bstep (se 1 (by rfl) ⟨2063798, by rfl⟩ : syracuseStep 2751731 = 4127597) B4127597
theorem B359903 : Blo 358757 359903 := bstep (se 1 (by rfl) ⟨269927, by rfl⟩ : syracuseStep 359903 = 539855) B539855
theorem B359963 : Blo 358757 359963 := bstep (se 1 (by rfl) ⟨269972, by rfl⟩ : syracuseStep 359963 = 539945) B539945
theorem B359983 : Blo 358757 359983 := bstep (se 1 (by rfl) ⟨269987, by rfl⟩ : syracuseStep 359983 = 539975) B539975
theorem B458399 : Blo 358757 458399 := bstep (se 1 (by rfl) ⟨343799, by rfl⟩ : syracuseStep 458399 = 687599) B687599
theorem B688009 : Blo 358757 688009 := bstep (se 2 (by rfl) ⟨258003, by rfl⟩ : syracuseStep 688009 = 516007) B516007
theorem B360383 : Blo 358757 360383 := bstep (se 1 (by rfl) ⟨270287, by rfl⟩ : syracuseStep 360383 = 540575) B540575
theorem B360443 : Blo 358757 360443 := bstep (se 1 (by rfl) ⟨270332, by rfl⟩ : syracuseStep 360443 = 540665) B540665
theorem B360479 : Blo 358757 360479 := bstep (se 1 (by rfl) ⟨270359, by rfl⟩ : syracuseStep 360479 = 540719) B540719
theorem B688169 : Blo 358757 688169 := bstep (se 2 (by rfl) ⟨258063, by rfl⟩ : syracuseStep 688169 = 516127) B516127
theorem B360495 : Blo 358757 360495 := bstep (se 1 (by rfl) ⟨270371, by rfl⟩ : syracuseStep 360495 = 540743) B540743
theorem B360615 : Blo 358757 360615 := bstep (se 1 (by rfl) ⟨270461, by rfl⟩ : syracuseStep 360615 = 540923) B540923
theorem B360699 : Blo 358757 360699 := bstep (se 1 (by rfl) ⟨270524, by rfl⟩ : syracuseStep 360699 = 541049) B541049
theorem B7766279 : Blo 358757 7766279 := bstep (se 1 (by rfl) ⟨5824709, by rfl⟩ : syracuseStep 7766279 = 11649419) B11649419
theorem B5800211 : Blo 358757 5800211 := bstep (se 1 (by rfl) ⟨4350158, by rfl⟩ : syracuseStep 5800211 = 8700317) B8700317
theorem B360807 : Blo 358757 360807 := bstep (se 1 (by rfl) ⟨270605, by rfl⟩ : syracuseStep 360807 = 541211) B541211
theorem B360895 : Blo 358757 360895 := bstep (se 1 (by rfl) ⟨270671, by rfl⟩ : syracuseStep 360895 = 541343) B541343
theorem B360927 : Blo 358757 360927 := bstep (se 1 (by rfl) ⟨270695, by rfl⟩ : syracuseStep 360927 = 541391) B541391
theorem B361007 : Blo 358757 361007 := bstep (se 1 (by rfl) ⟨270755, by rfl⟩ : syracuseStep 361007 = 541511) B541511
theorem B361051 : Blo 358757 361051 := bstep (se 1 (by rfl) ⟨270788, by rfl⟩ : syracuseStep 361051 = 541577) B541577
theorem B2851549 : Blo 358757 2851549 := bstep (se 3 (by rfl) ⟨534665, by rfl⟩ : syracuseStep 2851549 = 1069331) B1069331
theorem B16646975 : Blo 358757 16646975 := bstep (se 1 (by rfl) ⟨12485231, by rfl⟩ : syracuseStep 16646975 = 24970463) B24970463
theorem B2458781 : Blo 358757 2458781 := bstep (se 3 (by rfl) ⟨461021, by rfl⟩ : syracuseStep 2458781 = 922043) B922043
theorem B1738255 : Blo 358757 1738255 := bstep (se 1 (by rfl) ⟨1303691, by rfl⟩ : syracuseStep 1738255 = 2607383) B2607383
theorem B362663 : Blo 358757 362663 := bstep (se 1 (by rfl) ⟨271997, by rfl⟩ : syracuseStep 362663 = 543995) B543995
theorem B1215323 : Blo 358757 1215323 := bstep (se 1 (by rfl) ⟨911492, by rfl⟩ : syracuseStep 1215323 = 1822985) B1822985
theorem B1215431 : Blo 358757 1215431 := bstep (se 1 (by rfl) ⟨911573, by rfl⟩ : syracuseStep 1215431 = 1823147) B1823147
theorem B3279977 : Blo 358757 3279977 := bstep (se 2 (by rfl) ⟨1229991, by rfl⟩ : syracuseStep 3279977 = 2459983) B2459983
theorem B8785043 : Blo 358757 8785043 := bstep (se 1 (by rfl) ⟨6588782, by rfl⟩ : syracuseStep 8785043 = 13177565) B13177565
theorem B1576127 : Blo 358757 1576127 := bstep (se 1 (by rfl) ⟨1182095, by rfl⟩ : syracuseStep 1576127 = 2364191) B2364191
theorem B5836511 : Blo 358757 5836511 := bstep (se 1 (by rfl) ⟨4377383, by rfl⟩ : syracuseStep 5836511 = 8754767) B8754767
theorem B824039 : Blo 358757 824039 := bstep (se 1 (by rfl) ⟨618029, by rfl⟩ : syracuseStep 824039 = 1236059) B1236059
theorem B4756333 : Blo 358757 4756333 := bstep (se 3 (by rfl) ⟨891812, by rfl⟩ : syracuseStep 4756333 = 1783625) B1783625
theorem B1152071 : Blo 358757 1152071 := bstep (se 1 (by rfl) ⟨864053, by rfl⟩ : syracuseStep 1152071 = 1728107) B1728107
theorem B2627063 : Blo 358757 2627063 := bstep (se 1 (by rfl) ⟨1970297, by rfl⟩ : syracuseStep 2627063 = 3940595) B3940595
theorem B1545799 : Blo 358757 1545799 := bstep (se 1 (by rfl) ⟨1159349, by rfl⟩ : syracuseStep 1545799 = 2318699) B2318699
theorem B2857625 : Blo 358757 2857625 := bstep (se 2 (by rfl) ⟨1071609, by rfl⟩ : syracuseStep 2857625 = 2143219) B2143219
theorem B6167339 : Blo 358757 6167339 := bstep (se 1 (by rfl) ⟨4625504, by rfl⟩ : syracuseStep 6167339 = 9251009) B9251009
theorem B6921035 : Blo 358757 6921035 := bstep (se 1 (by rfl) ⟨5190776, by rfl⟩ : syracuseStep 6921035 = 10381553) B10381553
theorem B1219643 : Blo 358757 1219643 := bstep (se 1 (by rfl) ⟨914732, by rfl⟩ : syracuseStep 1219643 = 1829465) B1829465
theorem B1941353 : Blo 358757 1941353 := bstep (se 2 (by rfl) ⟨728007, by rfl⟩ : syracuseStep 1941353 = 1456015) B1456015
theorem B2302091 : Blo 358757 2302091 := bstep (se 1 (by rfl) ⟨1726568, by rfl⟩ : syracuseStep 2302091 = 3453137) B3453137
theorem B1647215 : Blo 358757 1647215 := bstep (se 1 (by rfl) ⟨1235411, by rfl⟩ : syracuseStep 1647215 = 2470823) B2470823
theorem B369407 : Blo 358757 369407 := bstep (se 1 (by rfl) ⟨277055, by rfl⟩ : syracuseStep 369407 = 554111) B554111
theorem B2106271 : Blo 358757 2106271 := bstep (se 1 (by rfl) ⟨1579703, by rfl⟩ : syracuseStep 2106271 = 3159407) B3159407
theorem B8463485 : Blo 358757 8463485 := bstep (se 3 (by rfl) ⟨1586903, by rfl⟩ : syracuseStep 8463485 = 3173807) B3173807
theorem B1222397 : Blo 358757 1222397 := bstep (se 3 (by rfl) ⟨229199, by rfl⟩ : syracuseStep 1222397 = 458399) B458399
theorem B6924041 : Blo 358757 6924041 := bstep (se 2 (by rfl) ⟨2596515, by rfl⟩ : syracuseStep 6924041 = 5193031) B5193031
theorem B2074961 : Blo 358757 2074961 := bstep (se 2 (by rfl) ⟨778110, by rfl⟩ : syracuseStep 2074961 = 1556221) B1556221
theorem B1223423 : Blo 358757 1223423 := bstep (se 1 (by rfl) ⟨917567, by rfl⟩ : syracuseStep 1223423 = 1835135) B1835135
theorem B4434713 : Blo 358757 4434713 := bstep (se 2 (by rfl) ⟨1663017, by rfl⟩ : syracuseStep 4434713 = 3326035) B3326035
theorem B2305577 : Blo 358757 2305577 := bstep (se 2 (by rfl) ⟨864591, by rfl⟩ : syracuseStep 2305577 = 1729183) B1729183
theorem B14791085 : Blo 358757 14791085 := bstep (se 3 (by rfl) ⟨2773328, by rfl⟩ : syracuseStep 14791085 = 5546657) B5546657
theorem B1029611 : Blo 358757 1029611 := bstep (se 1 (by rfl) ⟨772208, by rfl⟩ : syracuseStep 1029611 = 1544417) B1544417
theorem B2045735 : Blo 358757 2045735 := bstep (se 1 (by rfl) ⟨1534301, by rfl⟩ : syracuseStep 2045735 = 3068603) B3068603
theorem B538619 : Blo 358757 538619 := bstep (se 1 (by rfl) ⟨403964, by rfl⟩ : syracuseStep 538619 = 807929) B807929
theorem B1816991 : Blo 358757 1816991 := bstep (se 1 (by rfl) ⟨1362743, by rfl⟩ : syracuseStep 1816991 = 2725487) B2725487
theorem B1161631 : Blo 358757 1161631 := bstep (se 1 (by rfl) ⟨871223, by rfl⟩ : syracuseStep 1161631 = 1742447) B1742447
theorem B540137 : Blo 358757 540137 := bstep (se 2 (by rfl) ⟨202551, by rfl⟩ : syracuseStep 540137 = 405103) B405103
theorem B540281 : Blo 358757 540281 := bstep (se 2 (by rfl) ⟨202605, by rfl⟩ : syracuseStep 540281 = 405211) B405211
theorem B1818449 : Blo 358757 1818449 := bstep (se 2 (by rfl) ⟨681918, by rfl⟩ : syracuseStep 1818449 = 1363837) B1363837
theorem B606089 : Blo 358757 606089 := bstep (se 2 (by rfl) ⟨227283, by rfl⟩ : syracuseStep 606089 = 454567) B454567
theorem B769961 : Blo 358757 769961 := bstep (se 2 (by rfl) ⟨288735, by rfl⟩ : syracuseStep 769961 = 577471) B577471
theorem B4603877 : Blo 358757 4603877 := bstep (se 4 (by rfl) ⟨431613, by rfl⟩ : syracuseStep 4603877 = 863227) B863227
theorem B1818611 : Blo 358757 1818611 := bstep (se 1 (by rfl) ⟨1363958, by rfl⟩ : syracuseStep 1818611 = 2727917) B2727917
theorem B540779 : Blo 358757 540779 := bstep (se 1 (by rfl) ⟨405584, by rfl⟩ : syracuseStep 540779 = 811169) B811169
theorem B2933117 : Blo 358757 2933117 := bstep (se 3 (by rfl) ⟨549959, by rfl⟩ : syracuseStep 2933117 = 1099919) B1099919
theorem B5849495 : Blo 358757 5849495 := bstep (se 1 (by rfl) ⟨4387121, by rfl⟩ : syracuseStep 5849495 = 8774243) B8774243
theorem B9421289 : Blo 358757 9421289 := bstep (se 2 (by rfl) ⟨3532983, by rfl⟩ : syracuseStep 9421289 = 7065967) B7065967
theorem B607007 : Blo 358757 607007 := bstep (se 1 (by rfl) ⟨455255, by rfl⟩ : syracuseStep 607007 = 910511) B910511
theorem B5293811 : Blo 358757 5293811 := bstep (se 1 (by rfl) ⟨3970358, by rfl⟩ : syracuseStep 5293811 = 7940717) B7940717
theorem B9357275 : Blo 358757 9357275 := bstep (se 1 (by rfl) ⟨7017956, by rfl⟩ : syracuseStep 9357275 = 14035913) B14035913
theorem B608303 : Blo 358757 608303 := bstep (se 1 (by rfl) ⟨456227, by rfl⟩ : syracuseStep 608303 = 912455) B912455
theorem B1820879 : Blo 358757 1820879 := bstep (se 1 (by rfl) ⟨1365659, by rfl⟩ : syracuseStep 1820879 = 2731319) B2731319
theorem B1821203 : Blo 358757 1821203 := bstep (se 1 (by rfl) ⟨1365902, by rfl⟩ : syracuseStep 1821203 = 2731805) B2731805
theorem B608809 : Blo 358757 608809 := bstep (se 2 (by rfl) ⟨228303, by rfl⟩ : syracuseStep 608809 = 456607) B456607
theorem B609511 : Blo 358757 609511 := bstep (se 1 (by rfl) ⟨457133, by rfl⟩ : syracuseStep 609511 = 914267) B914267
theorem B610247 : Blo 358757 610247 := bstep (se 1 (by rfl) ⟨457685, by rfl⟩ : syracuseStep 610247 = 915371) B915371
theorem B970849 : Blo 358757 970849 := bstep (se 2 (by rfl) ⟨364068, by rfl⟩ : syracuseStep 970849 = 728137) B728137
theorem B610537 : Blo 358757 610537 := bstep (se 2 (by rfl) ⟨228951, by rfl⟩ : syracuseStep 610537 = 457903) B457903
theorem B2052773 : Blo 358757 2052773 := bstep (se 4 (by rfl) ⟨192447, by rfl⟩ : syracuseStep 2052773 = 384895) B384895
theorem B807659 : Blo 358757 807659 := bstep (se 1 (by rfl) ⟨605744, by rfl⟩ : syracuseStep 807659 = 1211489) B1211489
theorem B545563 : Blo 358757 545563 := bstep (se 1 (by rfl) ⟨409172, by rfl⟩ : syracuseStep 545563 = 818345) B818345
theorem B4641907 : Blo 358757 4641907 := bstep (se 1 (by rfl) ⟨3481430, by rfl⟩ : syracuseStep 4641907 = 6962861) B6962861
theorem B874091 : Blo 358757 874091 := bstep (se 1 (by rfl) ⟨655568, by rfl⟩ : syracuseStep 874091 = 1311137) B1311137
theorem B16570169 : Blo 358757 16570169 := bstep (se 2 (by rfl) ⟨6213813, by rfl⟩ : syracuseStep 16570169 = 12427627) B12427627
theorem B21124955 : Blo 358757 21124955 := bstep (se 1 (by rfl) ⟨15843716, by rfl⟩ : syracuseStep 21124955 = 31687433) B31687433
theorem B1005479 : Blo 358757 1005479 := bstep (se 1 (by rfl) ⟨754109, by rfl⟩ : syracuseStep 1005479 = 1508219) B1508219
theorem B579791 : Blo 358757 579791 := bstep (se 1 (by rfl) ⟨434843, by rfl⟩ : syracuseStep 579791 = 869687) B869687
theorem B809513 : Blo 358757 809513 := bstep (se 2 (by rfl) ⟨303567, by rfl⟩ : syracuseStep 809513 = 607135) B607135
theorem B810395 : Blo 358757 810395 := bstep (se 1 (by rfl) ⟨607796, by rfl⟩ : syracuseStep 810395 = 1215593) B1215593
theorem B908779 : Blo 358757 908779 := bstep (se 1 (by rfl) ⟨681584, by rfl⟩ : syracuseStep 908779 = 1363169) B1363169
theorem B810791 : Blo 358757 810791 := bstep (se 1 (by rfl) ⟨608093, by rfl⟩ : syracuseStep 810791 = 1216187) B1216187
theorem B3071915 : Blo 358757 3071915 := bstep (se 1 (by rfl) ⟨2303936, by rfl⟩ : syracuseStep 3071915 = 4607873) B4607873
theorem B3465287 : Blo 358757 3465287 := bstep (se 1 (by rfl) ⟨2598965, by rfl⟩ : syracuseStep 3465287 = 5197931) B5197931
theorem B516223 : Blo 358757 516223 := bstep (se 1 (by rfl) ⟨387167, by rfl⟩ : syracuseStep 516223 = 774335) B774335
theorem B1302713 : Blo 358757 1302713 := bstep (se 2 (by rfl) ⟨488517, by rfl⟩ : syracuseStep 1302713 = 977035) B977035
theorem B12509623 : Blo 358757 12509623 := bstep (se 1 (by rfl) ⟨9382217, by rfl⟩ : syracuseStep 12509623 = 18764435) B18764435
theorem B2941481 : Blo 358757 2941481 := bstep (se 2 (by rfl) ⟨1103055, by rfl⟩ : syracuseStep 2941481 = 2206111) B2206111
theorem B2744927 : Blo 358757 2744927 := bstep (se 1 (by rfl) ⟨2058695, by rfl⟩ : syracuseStep 2744927 = 4117391) B4117391
theorem B3892049 : Blo 358757 3892049 := bstep (se 2 (by rfl) ⟨1459518, by rfl⟩ : syracuseStep 3892049 = 2919037) B2919037
theorem B910217 : Blo 358757 910217 := bstep (se 2 (by rfl) ⟨341331, by rfl⟩ : syracuseStep 910217 = 682663) B682663
theorem B2057147 : Blo 358757 2057147 := bstep (se 1 (by rfl) ⟨1542860, by rfl⟩ : syracuseStep 2057147 = 3085721) B3085721
theorem B812123 : Blo 358757 812123 := bstep (se 1 (by rfl) ⟨609092, by rfl⟩ : syracuseStep 812123 = 1218185) B1218185
theorem B1369183 : Blo 358757 1369183 := bstep (se 1 (by rfl) ⟨1026887, by rfl⟩ : syracuseStep 1369183 = 2053775) B2053775
theorem B1860833 : Blo 358757 1860833 := bstep (se 2 (by rfl) ⟨697812, by rfl⟩ : syracuseStep 1860833 = 1395625) B1395625
theorem B812447 : Blo 358757 812447 := bstep (se 1 (by rfl) ⟨609335, by rfl⟩ : syracuseStep 812447 = 1218671) B1218671
theorem B3225445829 : Blo 358757 3225445829 := bstep (se 4 (by rfl) ⟨302385546, by rfl⟩ : syracuseStep 3225445829 = 604771093) B604771093
theorem B1828655 : Blo 358757 1828655 := bstep (se 1 (by rfl) ⟨1371491, by rfl⟩ : syracuseStep 1828655 = 2742983) B2742983
theorem B2320339 : Blo 358757 2320339 := bstep (se 1 (by rfl) ⟨1740254, by rfl⟩ : syracuseStep 2320339 = 3480509) B3480509
theorem B14838065 : Blo 358757 14838065 := bstep (se 2 (by rfl) ⟨5564274, by rfl⟩ : syracuseStep 14838065 = 11128549) B11128549
theorem B1305179 : Blo 358757 1305179 := bstep (se 1 (by rfl) ⟨978884, by rfl⟩ : syracuseStep 1305179 = 1957769) B1957769
theorem B813671 : Blo 358757 813671 := bstep (se 1 (by rfl) ⟨610253, by rfl⟩ : syracuseStep 813671 = 1220507) B1220507
theorem B486095 : Blo 358757 486095 := bstep (se 1 (by rfl) ⟨364571, by rfl⟩ : syracuseStep 486095 = 729143) B729143
theorem B682921 : Blo 358757 682921 := bstep (se 2 (by rfl) ⟨256095, by rfl⟩ : syracuseStep 682921 = 512191) B512191
theorem B814175 : Blo 358757 814175 := bstep (se 1 (by rfl) ⟨610631, by rfl⟩ : syracuseStep 814175 = 1221263) B1221263
theorem B3828959 : Blo 358757 3828959 := bstep (se 1 (by rfl) ⟨2871719, by rfl⟩ : syracuseStep 3828959 = 5743439) B5743439
theorem B1830113 : Blo 358757 1830113 := bstep (se 2 (by rfl) ⟨686292, by rfl⟩ : syracuseStep 1830113 = 1372585) B1372585
theorem B913103 : Blo 358757 913103 := bstep (se 1 (by rfl) ⟨684827, by rfl⟩ : syracuseStep 913103 = 1369655) B1369655
theorem B454891 : Blo 358757 454891 := bstep (se 1 (by rfl) ⟨341168, by rfl⟩ : syracuseStep 454891 = 682337) B682337
theorem B815399 : Blo 358757 815399 := bstep (se 1 (by rfl) ⟨611549, by rfl⟩ : syracuseStep 815399 = 1223099) B1223099
theorem B455807 : Blo 358757 455807 := bstep (se 1 (by rfl) ⟨341855, by rfl⟩ : syracuseStep 455807 = 683711) B683711
theorem B980095 : Blo 358757 980095 := bstep (se 1 (by rfl) ⟨735071, by rfl⟩ : syracuseStep 980095 = 1470143) B1470143
theorem B652475 : Blo 358757 652475 := bstep (se 1 (by rfl) ⟨489356, by rfl⟩ : syracuseStep 652475 = 978713) B978713
theorem B1373375 : Blo 358757 1373375 := bstep (se 1 (by rfl) ⟨1030031, by rfl⟩ : syracuseStep 1373375 = 2060063) B2060063
theorem B1832543 : Blo 358757 1832543 := bstep (se 1 (by rfl) ⟨1374407, by rfl⟩ : syracuseStep 1832543 = 2748815) B2748815
theorem B915047 : Blo 358757 915047 := bstep (se 1 (by rfl) ⟨686285, by rfl⟩ : syracuseStep 915047 = 1372571) B1372571
theorem B2062205 : Blo 358757 2062205 := bstep (se 3 (by rfl) ⟨386663, by rfl⟩ : syracuseStep 2062205 = 773327) B773327
theorem B522343 : Blo 358757 522343 := bstep (se 1 (by rfl) ⟨391757, by rfl⟩ : syracuseStep 522343 = 783515) B783515
theorem B1374347 : Blo 358757 1374347 := bstep (se 1 (by rfl) ⟨1030760, by rfl⟩ : syracuseStep 1374347 = 2061521) B2061521
theorem B1833191 : Blo 358757 1833191 := bstep (se 1 (by rfl) ⟨1374893, by rfl⟩ : syracuseStep 1833191 = 2749787) B2749787
theorem B359067 : Blo 358757 359067 := bstep (se 1 (by rfl) ⟨269300, by rfl⟩ : syracuseStep 359067 = 538601) B538601
theorem B359487 : Blo 358757 359487 := bstep (se 1 (by rfl) ⟨269615, by rfl⟩ : syracuseStep 359487 = 539231) B539231
theorem B359807 : Blo 358757 359807 := bstep (se 1 (by rfl) ⟨269855, by rfl⟩ : syracuseStep 359807 = 539711) B539711
theorem B1834487 : Blo 358757 1834487 := bstep (se 1 (by rfl) ⟨1375865, by rfl⟩ : syracuseStep 1834487 = 2751731) B2751731
theorem B360039 : Blo 358757 360039 := bstep (se 1 (by rfl) ⟨270029, by rfl⟩ : syracuseStep 360039 = 540059) B540059
theorem B917345 : Blo 358757 917345 := bstep (se 2 (by rfl) ⟨344004, by rfl⟩ : syracuseStep 917345 = 688009) B688009
theorem B360319 : Blo 358757 360319 := bstep (se 1 (by rfl) ⟨270239, by rfl⟩ : syracuseStep 360319 = 540479) B540479
theorem B458779 : Blo 358757 458779 := bstep (se 1 (by rfl) ⟨344084, by rfl⟩ : syracuseStep 458779 = 688169) B688169
theorem B360519 : Blo 358757 360519 := bstep (se 1 (by rfl) ⟨270389, by rfl⟩ : syracuseStep 360519 = 540779) B540779
theorem B5177519 : Blo 358757 5177519 := bstep (se 1 (by rfl) ⟨3883139, by rfl⟩ : syracuseStep 5177519 = 7766279) B7766279
theorem B3866807 : Blo 358757 3866807 := bstep (se 1 (by rfl) ⟨2900105, by rfl⟩ : syracuseStep 3866807 = 5800211) B5800211
theorem B3899663 : Blo 358757 3899663 := bstep (se 1 (by rfl) ⟨2924747, by rfl⟩ : syracuseStep 3899663 = 5849495) B5849495
theorem B2753189 : Blo 358757 2753189 := bstep (se 4 (by rfl) ⟨258111, by rfl⟩ : syracuseStep 2753189 = 516223) B516223
theorem B1639187 : Blo 358757 1639187 := bstep (se 1 (by rfl) ⟨1229390, by rfl⟩ : syracuseStep 1639187 = 2458781) B2458781
theorem B1213919 : Blo 358757 1213919 := bstep (se 1 (by rfl) ⟨910439, by rfl⟩ : syracuseStep 1213919 = 1820879) B1820879
theorem B1214135 : Blo 358757 1214135 := bstep (se 1 (by rfl) ⟨910601, by rfl⟩ : syracuseStep 1214135 = 1821203) B1821203
theorem B985085 : Blo 358757 985085 := bstep (se 3 (by rfl) ⟨184703, by rfl⟩ : syracuseStep 985085 = 369407) B369407
theorem B1050751 : Blo 358757 1050751 := bstep (se 1 (by rfl) ⟨788063, by rfl⟩ : syracuseStep 1050751 = 1576127) B1576127
theorem B66717989 : Blo 358757 66717989 := bstep (se 4 (by rfl) ⟨6254811, by rfl⟩ : syracuseStep 66717989 = 12509623) B12509623
theorem B1215485 : Blo 358757 1215485 := bstep (se 3 (by rfl) ⟨227903, by rfl⟩ : syracuseStep 1215485 = 455807) B455807
theorem B11046779 : Blo 358757 11046779 := bstep (se 1 (by rfl) ⟨8285084, by rfl⟩ : syracuseStep 11046779 = 16570169) B16570169
theorem B1905083 : Blo 358757 1905083 := bstep (se 1 (by rfl) ⟨1428812, by rfl⟩ : syracuseStep 1905083 = 2857625) B2857625
theorem B1212407 : Blo 358757 1212407 := bstep (se 1 (by rfl) ⟨909305, by rfl⟩ : syracuseStep 1212407 = 1818611) B1818611
theorem B2594699 : Blo 358757 2594699 := bstep (se 1 (by rfl) ⟨1946024, by rfl⟩ : syracuseStep 2594699 = 3892049) B3892049
theorem B727417 : Blo 358757 727417 := bstep (se 2 (by rfl) ⟨272781, by rfl⟩ : syracuseStep 727417 = 545563) B545563
theorem B1219103 : Blo 358757 1219103 := bstep (se 1 (by rfl) ⟨914327, by rfl⟩ : syracuseStep 1219103 = 1828655) B1828655
theorem B1383307 : Blo 358757 1383307 := bstep (se 1 (by rfl) ⟨1037480, by rfl⟩ : syracuseStep 1383307 = 2074961) B2074961
theorem B2956475 : Blo 358757 2956475 := bstep (se 1 (by rfl) ⟨2217356, by rfl⟩ : syracuseStep 2956475 = 4434713) B4434713
theorem B1220075 : Blo 358757 1220075 := bstep (se 1 (by rfl) ⟨915056, by rfl⟩ : syracuseStep 1220075 = 1830113) B1830113
theorem B696457 : Blo 358757 696457 := bstep (se 2 (by rfl) ⟨261171, by rfl⟩ : syracuseStep 696457 = 522343) B522343
theorem B1548841 : Blo 358757 1548841 := bstep (se 2 (by rfl) ⟨580815, by rfl⟩ : syracuseStep 1548841 = 1161631) B1161631
theorem B434983 : Blo 358757 434983 := bstep (se 1 (by rfl) ⟨326237, by rfl⟩ : syracuseStep 434983 = 652475) B652475
theorem B1221695 : Blo 358757 1221695 := bstep (se 1 (by rfl) ⟨916271, by rfl⟩ : syracuseStep 1221695 = 1832543) B1832543
theorem B1222127 : Blo 358757 1222127 := bstep (se 1 (by rfl) ⟨916595, by rfl⟩ : syracuseStep 1222127 = 1833191) B1833191
theorem B1222991 : Blo 358757 1222991 := bstep (se 1 (by rfl) ⟨917243, by rfl⟩ : syracuseStep 1222991 = 1834487) B1834487
theorem B404059 : Blo 358757 404059 := bstep (se 1 (by rfl) ⟨303044, by rfl⟩ : syracuseStep 404059 = 606089) B606089
theorem B404671 : Blo 358757 404671 := bstep (se 1 (by rfl) ⟨303503, by rfl⟩ : syracuseStep 404671 = 607007) B607007
theorem B6238183 : Blo 358757 6238183 := bstep (se 1 (by rfl) ⟨4678637, by rfl⟩ : syracuseStep 6238183 = 9357275) B9357275
theorem B405535 : Blo 358757 405535 := bstep (se 1 (by rfl) ⟨304151, by rfl⟩ : syracuseStep 405535 = 608303) B608303
theorem B7843949 : Blo 358757 7843949 := bstep (se 3 (by rfl) ⟨1470740, by rfl⟩ : syracuseStep 7843949 = 2941481) B2941481
theorem B3093785 : Blo 358757 3093785 := bstep (se 2 (by rfl) ⟨1160169, by rfl⟩ : syracuseStep 3093785 = 2320339) B2320339
theorem B406831 : Blo 358757 406831 := bstep (se 1 (by rfl) ⟨305123, by rfl⟩ : syracuseStep 406831 = 610247) B610247
theorem B538439 : Blo 358757 538439 := bstep (se 1 (by rfl) ⟨403829, by rfl⟩ : syracuseStep 538439 = 807659) B807659
theorem B4962221 : Blo 358757 4962221 := bstep (se 3 (by rfl) ⟨930416, by rfl⟩ : syracuseStep 4962221 = 1860833) B1860833
theorem B768047 : Blo 358757 768047 := bstep (se 1 (by rfl) ⟨576035, by rfl⟩ : syracuseStep 768047 = 1152071) B1152071
theorem B1751375 : Blo 358757 1751375 := bstep (se 1 (by rfl) ⟨1313531, by rfl⟩ : syracuseStep 1751375 = 2627063) B2627063
theorem B670319 : Blo 358757 670319 := bstep (se 1 (by rfl) ⟨502739, by rfl⟩ : syracuseStep 670319 = 1005479) B1005479
theorem B539675 : Blo 358757 539675 := bstep (se 1 (by rfl) ⟨404756, by rfl⟩ : syracuseStep 539675 = 809513) B809513
theorem B4111559 : Blo 358757 4111559 := bstep (se 1 (by rfl) ⟨3083669, by rfl⟩ : syracuseStep 4111559 = 6167339) B6167339
theorem B60833045 : Blo 358757 60833045 := bstep (se 6 (by rfl) ⟨1425774, by rfl⟩ : syracuseStep 60833045 = 2851549) B2851549
theorem B540263 : Blo 358757 540263 := bstep (se 1 (by rfl) ⟨405197, by rfl⟩ : syracuseStep 540263 = 810395) B810395
theorem B540527 : Blo 358757 540527 := bstep (se 1 (by rfl) ⟨405395, by rfl⟩ : syracuseStep 540527 = 810791) B810791
theorem B1294235 : Blo 358757 1294235 := bstep (se 1 (by rfl) ⟨970676, by rfl⟩ : syracuseStep 1294235 = 1941353) B1941353
theorem B2047943 : Blo 358757 2047943 := bstep (se 1 (by rfl) ⟨1535957, by rfl⟩ : syracuseStep 2047943 = 3071915) B3071915
theorem B2310191 : Blo 358757 2310191 := bstep (se 1 (by rfl) ⟨1732643, by rfl⟩ : syracuseStep 2310191 = 3465287) B3465287
theorem B868475 : Blo 358757 868475 := bstep (se 1 (by rfl) ⟨651356, by rfl⟩ : syracuseStep 868475 = 1302713) B1302713
theorem B1294465 : Blo 358757 1294465 := bstep (se 2 (by rfl) ⟨485424, by rfl⟩ : syracuseStep 1294465 = 970849) B970849
theorem B606521 : Blo 358757 606521 := bstep (se 2 (by rfl) ⟨227445, by rfl⟩ : syracuseStep 606521 = 454891) B454891
theorem B1098143 : Blo 358757 1098143 := bstep (se 1 (by rfl) ⟨823607, by rfl⟩ : syracuseStep 1098143 = 1647215) B1647215
theorem B606811 : Blo 358757 606811 := bstep (se 1 (by rfl) ⟨455108, by rfl⟩ : syracuseStep 606811 = 910217) B910217
theorem B541415 : Blo 358757 541415 := bstep (se 1 (by rfl) ⟨406061, by rfl⟩ : syracuseStep 541415 = 812123) B812123
theorem B541631 : Blo 358757 541631 := bstep (se 1 (by rfl) ⟨406223, by rfl⟩ : syracuseStep 541631 = 812447) B812447
theorem B6341777 : Blo 358757 6341777 := bstep (se 2 (by rfl) ⟨2378166, by rfl⟩ : syracuseStep 6341777 = 4756333) B4756333
theorem B870119 : Blo 358757 870119 := bstep (se 1 (by rfl) ⟨652589, by rfl⟩ : syracuseStep 870119 = 1305179) B1305179
theorem B542447 : Blo 358757 542447 := bstep (se 1 (by rfl) ⟨406835, by rfl⟩ : syracuseStep 542447 = 813671) B813671
theorem B1296253 : Blo 358757 1296253 := bstep (se 3 (by rfl) ⟨243047, by rfl⟩ : syracuseStep 1296253 = 486095) B486095
theorem B542783 : Blo 358757 542783 := bstep (se 1 (by rfl) ⟨407087, by rfl⟩ : syracuseStep 542783 = 814175) B814175
theorem B608735 : Blo 358757 608735 := bstep (se 1 (by rfl) ⟨456551, by rfl⟩ : syracuseStep 608735 = 913103) B913103
theorem B543599 : Blo 358757 543599 := bstep (se 1 (by rfl) ⟨407699, by rfl⟩ : syracuseStep 543599 = 815399) B815399
theorem B610031 : Blo 358757 610031 := bstep (se 1 (by rfl) ⟨457523, by rfl⟩ : syracuseStep 610031 = 915047) B915047
theorem B1363823 : Blo 358757 1363823 := bstep (se 1 (by rfl) ⟨1022867, by rfl⟩ : syracuseStep 1363823 = 2045735) B2045735
theorem B611563 : Blo 358757 611563 := bstep (se 1 (by rfl) ⟨458672, by rfl⟩ : syracuseStep 611563 = 917345) B917345
theorem B513307 : Blo 358757 513307 := bstep (se 1 (by rfl) ⟨384980, by rfl⟩ : syracuseStep 513307 = 769961) B769961
theorem B3069251 : Blo 358757 3069251 := bstep (se 1 (by rfl) ⟨2301938, by rfl⟩ : syracuseStep 3069251 = 4603877) B4603877
theorem B1955411 : Blo 358757 1955411 := bstep (se 1 (by rfl) ⟨1466558, by rfl⟩ : syracuseStep 1955411 = 2933117) B2933117
theorem B6280859 : Blo 358757 6280859 := bstep (se 1 (by rfl) ⟨4710644, by rfl⟩ : syracuseStep 6280859 = 9421289) B9421289
theorem B11097983 : Blo 358757 11097983 := bstep (se 1 (by rfl) ⟨8323487, by rfl⟩ : syracuseStep 11097983 = 16646975) B16646975
theorem B3529207 : Blo 358757 3529207 := bstep (se 1 (by rfl) ⟨2646905, by rfl⟩ : syracuseStep 3529207 = 5293811) B5293811
theorem B2808361 : Blo 358757 2808361 := bstep (se 2 (by rfl) ⟨1053135, by rfl⟩ : syracuseStep 2808361 = 2106271) B2106271
theorem B1825577 : Blo 358757 1825577 := bstep (se 2 (by rfl) ⟨684591, by rfl⟩ : syracuseStep 1825577 = 1369183) B1369183
theorem B810215 : Blo 358757 810215 := bstep (se 1 (by rfl) ⟨607661, by rfl⟩ : syracuseStep 810215 = 1215323) B1215323
theorem B810287 : Blo 358757 810287 := bstep (se 1 (by rfl) ⟨607715, by rfl⟩ : syracuseStep 810287 = 1215431) B1215431
theorem B2317673 : Blo 358757 2317673 := bstep (se 2 (by rfl) ⟨869127, by rfl⟩ : syracuseStep 2317673 = 1738255) B1738255
theorem B2186651 : Blo 358757 2186651 := bstep (se 1 (by rfl) ⟨1639988, by rfl⟩ : syracuseStep 2186651 = 3279977) B3279977
theorem B5856695 : Blo 358757 5856695 := bstep (se 1 (by rfl) ⟨4392521, by rfl⟩ : syracuseStep 5856695 = 8785043) B8785043
theorem B3891007 : Blo 358757 3891007 := bstep (se 1 (by rfl) ⟨2918255, by rfl⟩ : syracuseStep 3891007 = 5836511) B5836511
theorem B22569293 : Blo 358757 22569293 := bstep (se 3 (by rfl) ⟨4231742, by rfl⟩ : syracuseStep 22569293 = 8463485) B8463485
theorem B1368515 : Blo 358757 1368515 := bstep (se 1 (by rfl) ⟨1026386, by rfl⟩ : syracuseStep 1368515 = 2052773) B2052773
theorem B549359 : Blo 358757 549359 := bstep (se 1 (by rfl) ⟨412019, by rfl⟩ : syracuseStep 549359 = 824039) B824039
theorem B811745 : Blo 358757 811745 := bstep (se 2 (by rfl) ⟨304404, by rfl⟩ : syracuseStep 811745 = 608809) B608809
theorem B582727 : Blo 358757 582727 := bstep (se 1 (by rfl) ⟨437045, by rfl⟩ : syracuseStep 582727 = 874091) B874091
theorem B910561 : Blo 358757 910561 := bstep (se 2 (by rfl) ⟨341460, by rfl⟩ : syracuseStep 910561 = 682921) B682921
theorem B14083303 : Blo 358757 14083303 := bstep (se 1 (by rfl) ⟨10562477, by rfl⟩ : syracuseStep 14083303 = 21124955) B21124955
theorem B386527 : Blo 358757 386527 := bstep (se 1 (by rfl) ⟨289895, by rfl⟩ : syracuseStep 386527 = 579791) B579791
theorem B812681 : Blo 358757 812681 := bstep (se 2 (by rfl) ⟨304755, by rfl⟩ : syracuseStep 812681 = 609511) B609511
theorem B4614023 : Blo 358757 4614023 := bstep (se 1 (by rfl) ⟨3460517, by rfl⟩ : syracuseStep 4614023 = 6921035) B6921035
theorem B813095 : Blo 358757 813095 := bstep (se 1 (by rfl) ⟨609821, by rfl⟩ : syracuseStep 813095 = 1219643) B1219643
theorem B1534727 : Blo 358757 1534727 := bstep (se 1 (by rfl) ⟨1151045, by rfl⟩ : syracuseStep 1534727 = 2302091) B2302091
theorem B814049 : Blo 358757 814049 := bstep (se 2 (by rfl) ⟨305268, by rfl⟩ : syracuseStep 814049 = 610537) B610537
theorem B1829951 : Blo 358757 1829951 := bstep (se 1 (by rfl) ⟨1372463, by rfl⟩ : syracuseStep 1829951 = 2744927) B2744927
theorem B1371431 : Blo 358757 1371431 := bstep (se 1 (by rfl) ⟨1028573, by rfl⟩ : syracuseStep 1371431 = 2057147) B2057147
theorem B2150297219 : Blo 358757 2150297219 := bstep (se 1 (by rfl) ⟨1612722914, by rfl⟩ : syracuseStep 2150297219 = 3225445829) B3225445829
theorem B814931 : Blo 358757 814931 := bstep (se 1 (by rfl) ⟨611198, by rfl⟩ : syracuseStep 814931 = 1222397) B1222397
theorem B4616027 : Blo 358757 4616027 := bstep (se 1 (by rfl) ⟨3462020, by rfl⟩ : syracuseStep 4616027 = 6924041) B6924041
theorem B6189209 : Blo 358757 6189209 := bstep (se 2 (by rfl) ⟨2320953, by rfl⟩ : syracuseStep 6189209 = 4641907) B4641907
theorem B1306793 : Blo 358757 1306793 := bstep (se 2 (by rfl) ⟨490047, by rfl⟩ : syracuseStep 1306793 = 980095) B980095
theorem B9892043 : Blo 358757 9892043 := bstep (se 1 (by rfl) ⟨7419032, by rfl⟩ : syracuseStep 9892043 = 14838065) B14838065
theorem B815615 : Blo 358757 815615 := bstep (se 1 (by rfl) ⟨611711, by rfl⟩ : syracuseStep 815615 = 1223423) B1223423
theorem B2061065 : Blo 358757 2061065 := bstep (se 2 (by rfl) ⟨772899, by rfl⟩ : syracuseStep 2061065 = 1545799) B1545799
theorem B2552639 : Blo 358757 2552639 := bstep (se 1 (by rfl) ⟨1914479, by rfl⟩ : syracuseStep 2552639 = 3828959) B3828959
theorem B1537051 : Blo 358757 1537051 := bstep (se 1 (by rfl) ⟨1152788, by rfl⟩ : syracuseStep 1537051 = 2305577) B2305577
theorem B9860723 : Blo 358757 9860723 := bstep (se 1 (by rfl) ⟨7395542, by rfl⟩ : syracuseStep 9860723 = 14791085) B14791085
theorem B915583 : Blo 358757 915583 := bstep (se 1 (by rfl) ⟨686687, by rfl⟩ : syracuseStep 915583 = 1373375) B1373375
theorem B686407 : Blo 358757 686407 := bstep (se 1 (by rfl) ⟨514805, by rfl⟩ : syracuseStep 686407 = 1029611) B1029611
theorem B1374803 : Blo 358757 1374803 := bstep (se 1 (by rfl) ⟨1031102, by rfl⟩ : syracuseStep 1374803 = 2062205) B2062205
theorem B359079 : Blo 358757 359079 := bstep (se 1 (by rfl) ⟨269309, by rfl⟩ : syracuseStep 359079 = 538619) B538619
theorem B916231 : Blo 358757 916231 := bstep (se 1 (by rfl) ⟨687173, by rfl⟩ : syracuseStep 916231 = 1374347) B1374347
theorem B1211327 : Blo 358757 1211327 := bstep (se 1 (by rfl) ⟨908495, by rfl⟩ : syracuseStep 1211327 = 1816991) B1816991
theorem B1211705 : Blo 358757 1211705 := bstep (se 2 (by rfl) ⟨454389, by rfl⟩ : syracuseStep 1211705 = 908779) B908779
theorem B360091 : Blo 358757 360091 := bstep (se 1 (by rfl) ⟨270068, by rfl⟩ : syracuseStep 360091 = 540137) B540137
theorem B360187 : Blo 358757 360187 := bstep (se 1 (by rfl) ⟨270140, by rfl⟩ : syracuseStep 360187 = 540281) B540281
theorem B1212299 : Blo 358757 1212299 := bstep (se 1 (by rfl) ⟨909224, by rfl⟩ : syracuseStep 1212299 = 1818449) B1818449
theorem B1540127 : Blo 358757 1540127 := bstep (se 1 (by rfl) ⟨1155095, by rfl⟩ : syracuseStep 1540127 = 2310191) B2310191
theorem B1835459 : Blo 358757 1835459 := bstep (se 1 (by rfl) ⟨1376594, by rfl⟩ : syracuseStep 1835459 = 2753189) B2753189
theorem B360943 : Blo 358757 360943 := bstep (se 1 (by rfl) ⟨270707, by rfl⟩ : syracuseStep 360943 = 541415) B541415
theorem B361087 : Blo 358757 361087 := bstep (se 1 (by rfl) ⟨270815, by rfl⟩ : syracuseStep 361087 = 541631) B541631
theorem B2065121 : Blo 358757 2065121 := bstep (se 2 (by rfl) ⟨774420, by rfl⟩ : syracuseStep 2065121 = 1548841) B1548841
theorem B4227851 : Blo 358757 4227851 := bstep (se 1 (by rfl) ⟨3170888, by rfl⟩ : syracuseStep 4227851 = 6341777) B6341777
theorem B361631 : Blo 358757 361631 := bstep (se 1 (by rfl) ⟨271223, by rfl⟩ : syracuseStep 361631 = 542447) B542447
theorem B656723 : Blo 358757 656723 := bstep (se 1 (by rfl) ⟨492542, by rfl⟩ : syracuseStep 656723 = 985085) B985085
theorem B361855 : Blo 358757 361855 := bstep (se 1 (by rfl) ⟨271391, by rfl⟩ : syracuseStep 361855 = 542783) B542783
theorem B1214081 : Blo 358757 1214081 := bstep (se 2 (by rfl) ⟨455280, by rfl⟩ : syracuseStep 1214081 = 910561) B910561
theorem B18777737 : Blo 358757 18777737 := bstep (se 2 (by rfl) ⟨7041651, by rfl⟩ : syracuseStep 18777737 = 14083303) B14083303
theorem B362399 : Blo 358757 362399 := bstep (se 1 (by rfl) ⟨271799, by rfl⟩ : syracuseStep 362399 = 543599) B543599
theorem B16748957 : Blo 358757 16748957 := bstep (se 3 (by rfl) ⟨3140429, by rfl⟩ : syracuseStep 16748957 = 6280859) B6280859
theorem B1217051 : Blo 358757 1217051 := bstep (se 1 (by rfl) ⟨912788, by rfl⟩ : syracuseStep 1217051 = 1825577) B1825577
theorem B7377637 : Blo 358757 7377637 := bstep (se 4 (by rfl) ⟨691653, by rfl⟩ : syracuseStep 7377637 = 1383307) B1383307
theorem B1970983 : Blo 358757 1970983 := bstep (se 1 (by rfl) ⟨1478237, by rfl⟩ : syracuseStep 1970983 = 2956475) B2956475
theorem B3904463 : Blo 358757 3904463 := bstep (se 1 (by rfl) ⟨2928347, by rfl⟩ : syracuseStep 3904463 = 5856695) B5856695
theorem B29594621 : Blo 358757 29594621 := bstep (se 3 (by rfl) ⟨5548991, by rfl⟩ : syracuseStep 29594621 = 11097983) B11097983
theorem B15046195 : Blo 358757 15046195 := bstep (se 1 (by rfl) ⟨11284646, by rfl⟩ : syracuseStep 15046195 = 22569293) B22569293
theorem B366239 : Blo 358757 366239 := bstep (se 1 (by rfl) ⟨274679, by rfl⟩ : syracuseStep 366239 = 549359) B549359
theorem B1219967 : Blo 358757 1219967 := bstep (se 1 (by rfl) ⟨914975, by rfl⟩ : syracuseStep 1219967 = 1829951) B1829951
theorem B6594695 : Blo 358757 6594695 := bstep (se 1 (by rfl) ⟨4946021, by rfl⟩ : syracuseStep 6594695 = 9892043) B9892043
theorem B1220777 : Blo 358757 1220777 := bstep (se 2 (by rfl) ⟨457791, by rfl⟩ : syracuseStep 1220777 = 915583) B915583
theorem B3744481 : Blo 358757 3744481 := bstep (se 2 (by rfl) ⟨1404180, by rfl⟩ : syracuseStep 3744481 = 2808361) B2808361
theorem B1221641 : Blo 358757 1221641 := bstep (se 2 (by rfl) ⟨458115, by rfl⟩ : syracuseStep 1221641 = 916231) B916231
theorem B5188009 : Blo 358757 5188009 := bstep (se 2 (by rfl) ⟨1945503, by rfl⟩ : syracuseStep 5188009 = 3891007) B3891007
theorem B862823 : Blo 358757 862823 := bstep (se 1 (by rfl) ⟨647117, by rfl⟩ : syracuseStep 862823 = 1294235) B1294235
theorem B3451679 : Blo 358757 3451679 := bstep (se 1 (by rfl) ⟨2588759, by rfl⟩ : syracuseStep 3451679 = 5177519) B5177519
theorem B2599775 : Blo 358757 2599775 := bstep (se 1 (by rfl) ⟨1949831, by rfl⟩ : syracuseStep 2599775 = 3899663) B3899663
theorem B928609 : Blo 358757 928609 := bstep (se 2 (by rfl) ⟨348228, by rfl⟩ : syracuseStep 928609 = 696457) B696457
theorem B404347 : Blo 358757 404347 := bstep (se 1 (by rfl) ⟨303260, by rfl⟩ : syracuseStep 404347 = 606521) B606521
theorem B732095 : Blo 358757 732095 := bstep (se 1 (by rfl) ⟨549071, by rfl⟩ : syracuseStep 732095 = 1098143) B1098143
theorem B3484781 : Blo 358757 3484781 := bstep (se 3 (by rfl) ⟨653396, by rfl⟩ : syracuseStep 3484781 = 1306793) B1306793
theorem B1092791 : Blo 358757 1092791 := bstep (se 1 (by rfl) ⟨819593, by rfl⟩ : syracuseStep 1092791 = 1639187) B1639187
theorem B44478659 : Blo 358757 44478659 := bstep (se 1 (by rfl) ⟨33358994, by rfl⟩ : syracuseStep 44478659 = 66717989) B66717989
theorem B405823 : Blo 358757 405823 := bstep (se 1 (by rfl) ⟨304367, by rfl⟩ : syracuseStep 405823 = 608735) B608735
theorem B406687 : Blo 358757 406687 := bstep (se 1 (by rfl) ⟨305015, by rfl⟩ : syracuseStep 406687 = 610031) B610031
theorem B538745 : Blo 358757 538745 := bstep (se 2 (by rfl) ⟨202029, by rfl⟩ : syracuseStep 538745 = 404059) B404059
theorem B2046167 : Blo 358757 2046167 := bstep (se 1 (by rfl) ⟨1534625, by rfl⟩ : syracuseStep 2046167 = 3069251) B3069251
theorem B539561 : Blo 358757 539561 := bstep (se 2 (by rfl) ⟨202335, by rfl⟩ : syracuseStep 539561 = 404671) B404671
theorem B540143 : Blo 358757 540143 := bstep (se 1 (by rfl) ⟨405107, by rfl⟩ : syracuseStep 540143 = 810215) B810215
theorem B540191 : Blo 358757 540191 := bstep (se 1 (by rfl) ⟨405143, by rfl⟩ : syracuseStep 540191 = 810287) B810287
theorem B1457767 : Blo 358757 1457767 := bstep (se 1 (by rfl) ⟨1093325, by rfl⟩ : syracuseStep 1457767 = 2186651) B2186651
theorem B540713 : Blo 358757 540713 := bstep (se 2 (by rfl) ⟨202767, by rfl⟩ : syracuseStep 540713 = 405535) B405535
theorem B2048125 : Blo 358757 2048125 := bstep (se 3 (by rfl) ⟨384023, by rfl⟩ : syracuseStep 2048125 = 768047) B768047
theorem B541163 : Blo 358757 541163 := bstep (se 1 (by rfl) ⟨405872, by rfl⟩ : syracuseStep 541163 = 811745) B811745
theorem B541787 : Blo 358757 541787 := bstep (se 1 (by rfl) ⟨406340, by rfl⟩ : syracuseStep 541787 = 812681) B812681
theorem B542063 : Blo 358757 542063 := bstep (se 1 (by rfl) ⟨406547, by rfl⟩ : syracuseStep 542063 = 813095) B813095
theorem B2049401 : Blo 358757 2049401 := bstep (se 2 (by rfl) ⟨768525, by rfl⟩ : syracuseStep 2049401 = 1537051) B1537051
theorem B2737637 : Blo 358757 2737637 := bstep (se 4 (by rfl) ⟨256653, by rfl⟩ : syracuseStep 2737637 = 513307) B513307
theorem B542441 : Blo 358757 542441 := bstep (se 2 (by rfl) ⟨203415, by rfl⟩ : syracuseStep 542441 = 406831) B406831
theorem B542699 : Blo 358757 542699 := bstep (se 1 (by rfl) ⟨407024, by rfl⟩ : syracuseStep 542699 = 814049) B814049
theorem B543287 : Blo 358757 543287 := bstep (se 1 (by rfl) ⟨407465, by rfl⟩ : syracuseStep 543287 = 814931) B814931
theorem B5229299 : Blo 358757 5229299 := bstep (se 1 (by rfl) ⟨3921974, by rfl⟩ : syracuseStep 5229299 = 7843949) B7843949
theorem B543743 : Blo 358757 543743 := bstep (se 1 (by rfl) ⟨407807, by rfl⟩ : syracuseStep 543743 = 815615) B815615
theorem B969889 : Blo 358757 969889 := bstep (se 2 (by rfl) ⟨363708, by rfl⟩ : syracuseStep 969889 = 727417) B727417
theorem B4705609 : Blo 358757 4705609 := bstep (se 2 (by rfl) ⟨1764603, by rfl⟩ : syracuseStep 4705609 = 3529207) B3529207
theorem B6180461 : Blo 358757 6180461 := bstep (se 3 (by rfl) ⟨1158836, by rfl⟩ : syracuseStep 6180461 = 2317673) B2317673
theorem B6573815 : Blo 358757 6573815 := bstep (se 1 (by rfl) ⟨4930361, by rfl⟩ : syracuseStep 6573815 = 9860723) B9860723
theorem B1167583 : Blo 358757 1167583 := bstep (se 1 (by rfl) ⟨875687, by rfl⟩ : syracuseStep 1167583 = 1751375) B1751375
theorem B5734125917 : Blo 358757 5734125917 := bstep (se 3 (by rfl) ⟨1075148609, by rfl⟩ : syracuseStep 5734125917 = 2150297219) B2150297219
theorem B446879 : Blo 358757 446879 := bstep (se 1 (by rfl) ⟨335159, by rfl⟩ : syracuseStep 446879 = 670319) B670319
theorem B807551 : Blo 358757 807551 := bstep (se 1 (by rfl) ⟨605663, by rfl⟩ : syracuseStep 807551 = 1211327) B1211327
theorem B2741039 : Blo 358757 2741039 := bstep (se 1 (by rfl) ⟨2055779, by rfl⟩ : syracuseStep 2741039 = 4111559) B4111559
theorem B40555363 : Blo 358757 40555363 := bstep (se 1 (by rfl) ⟨30416522, by rfl⟩ : syracuseStep 40555363 = 60833045) B60833045
theorem B807803 : Blo 358757 807803 := bstep (se 1 (by rfl) ⟨605852, by rfl⟩ : syracuseStep 807803 = 1211705) B1211705
theorem B808199 : Blo 358757 808199 := bstep (se 1 (by rfl) ⟨606149, by rfl⟩ : syracuseStep 808199 = 1212299) B1212299
theorem B1365295 : Blo 358757 1365295 := bstep (se 1 (by rfl) ⟨1023971, by rfl⟩ : syracuseStep 1365295 = 2047943) B2047943
theorem B808271 : Blo 358757 808271 := bstep (se 1 (by rfl) ⟨606203, by rfl⟩ : syracuseStep 808271 = 1212407) B1212407
theorem B611705 : Blo 358757 611705 := bstep (se 2 (by rfl) ⟨229389, by rfl⟩ : syracuseStep 611705 = 458779) B458779
theorem B578983 : Blo 358757 578983 := bstep (se 1 (by rfl) ⟨434237, by rfl⟩ : syracuseStep 578983 = 868475) B868475
theorem B2577871 : Blo 358757 2577871 := bstep (se 1 (by rfl) ⟨1933403, by rfl⟩ : syracuseStep 2577871 = 3866807) B3866807
theorem B1725953 : Blo 358757 1725953 := bstep (se 2 (by rfl) ⟨647232, by rfl⟩ : syracuseStep 1725953 = 1294465) B1294465
theorem B809081 : Blo 358757 809081 := bstep (se 2 (by rfl) ⟨303405, by rfl⟩ : syracuseStep 809081 = 606811) B606811
theorem B809279 : Blo 358757 809279 := bstep (se 1 (by rfl) ⟨606959, by rfl⟩ : syracuseStep 809279 = 1213919) B1213919
theorem B579977 : Blo 358757 579977 := bstep (se 2 (by rfl) ⟨217491, by rfl⟩ : syracuseStep 579977 = 434983) B434983
theorem B809423 : Blo 358757 809423 := bstep (se 1 (by rfl) ⟨607067, by rfl⟩ : syracuseStep 809423 = 1214135) B1214135
theorem B580079 : Blo 358757 580079 := bstep (se 1 (by rfl) ⟨435059, by rfl⟩ : syracuseStep 580079 = 870119) B870119
theorem B776969 : Blo 358757 776969 := bstep (se 2 (by rfl) ⟨291363, by rfl⟩ : syracuseStep 776969 = 582727) B582727
theorem B515369 : Blo 358757 515369 := bstep (se 2 (by rfl) ⟨193263, by rfl⟩ : syracuseStep 515369 = 386527) B386527
theorem B810323 : Blo 358757 810323 := bstep (se 1 (by rfl) ⟨607742, by rfl⟩ : syracuseStep 810323 = 1215485) B1215485
theorem B909215 : Blo 358757 909215 := bstep (se 1 (by rfl) ⟨681911, by rfl⟩ : syracuseStep 909215 = 1363823) B1363823
theorem B7364519 : Blo 358757 7364519 := bstep (se 1 (by rfl) ⟨5523389, by rfl⟩ : syracuseStep 7364519 = 11046779) B11046779
theorem B1401001 : Blo 358757 1401001 := bstep (se 2 (by rfl) ⟨525375, by rfl⟩ : syracuseStep 1401001 = 1050751) B1050751
theorem B1270055 : Blo 358757 1270055 := bstep (se 1 (by rfl) ⟨952541, by rfl⟩ : syracuseStep 1270055 = 1905083) B1905083
theorem B1303607 : Blo 358757 1303607 := bstep (se 1 (by rfl) ⟨977705, by rfl⟩ : syracuseStep 1303607 = 1955411) B1955411
theorem B1729799 : Blo 358757 1729799 := bstep (se 1 (by rfl) ⟨1297349, by rfl⟩ : syracuseStep 1729799 = 2594699) B2594699
theorem B812735 : Blo 358757 812735 := bstep (se 1 (by rfl) ⟨609551, by rfl⟩ : syracuseStep 812735 = 1219103) B1219103
theorem B813383 : Blo 358757 813383 := bstep (se 1 (by rfl) ⟨610037, by rfl⟩ : syracuseStep 813383 = 1220075) B1220075
theorem B8317577 : Blo 358757 8317577 := bstep (se 2 (by rfl) ⟨3119091, by rfl⟩ : syracuseStep 8317577 = 6238183) B6238183
theorem B912343 : Blo 358757 912343 := bstep (se 1 (by rfl) ⟨684257, by rfl⟩ : syracuseStep 912343 = 1368515) B1368515
theorem B814463 : Blo 358757 814463 := bstep (se 1 (by rfl) ⟨610847, by rfl⟩ : syracuseStep 814463 = 1221695) B1221695
theorem B814751 : Blo 358757 814751 := bstep (se 1 (by rfl) ⟨611063, by rfl⟩ : syracuseStep 814751 = 1222127) B1222127
theorem B3076015 : Blo 358757 3076015 := bstep (se 1 (by rfl) ⟨2307011, by rfl⟩ : syracuseStep 3076015 = 4614023) B4614023
theorem B815327 : Blo 358757 815327 := bstep (se 1 (by rfl) ⟨611495, by rfl⟩ : syracuseStep 815327 = 1222991) B1222991
theorem B815417 : Blo 358757 815417 := bstep (se 2 (by rfl) ⟨305781, by rfl⟩ : syracuseStep 815417 = 611563) B611563
theorem B4092605 : Blo 358757 4092605 := bstep (se 3 (by rfl) ⟨767363, by rfl⟩ : syracuseStep 4092605 = 1534727) B1534727
theorem B914287 : Blo 358757 914287 := bstep (se 1 (by rfl) ⟨685715, by rfl⟩ : syracuseStep 914287 = 1371431) B1371431
theorem B3077351 : Blo 358757 3077351 := bstep (se 1 (by rfl) ⟨2308013, by rfl⟩ : syracuseStep 3077351 = 4616027) B4616027
theorem B4126139 : Blo 358757 4126139 := bstep (se 1 (by rfl) ⟨3094604, by rfl⟩ : syracuseStep 4126139 = 6189209) B6189209
theorem B915209 : Blo 358757 915209 := bstep (se 2 (by rfl) ⟨343203, by rfl⟩ : syracuseStep 915209 = 686407) B686407
theorem B1374043 : Blo 358757 1374043 := bstep (se 1 (by rfl) ⟨1030532, by rfl⟩ : syracuseStep 1374043 = 2061065) B2061065
theorem B27228149 : Blo 358757 27228149 := bstep (se 5 (by rfl) ⟨1276319, by rfl⟩ : syracuseStep 27228149 = 2552639) B2552639
theorem B2062523 : Blo 358757 2062523 := bstep (se 1 (by rfl) ⟨1546892, by rfl⟩ : syracuseStep 2062523 = 3093785) B3093785
theorem B358959 : Blo 358757 358959 := bstep (se 1 (by rfl) ⟨269219, by rfl⟩ : syracuseStep 358959 = 538439) B538439
theorem B3308147 : Blo 358757 3308147 := bstep (se 1 (by rfl) ⟨2481110, by rfl⟩ : syracuseStep 3308147 = 4962221) B4962221
theorem B916535 : Blo 358757 916535 := bstep (se 1 (by rfl) ⟨687401, by rfl⟩ : syracuseStep 916535 = 1374803) B1374803
theorem B6913349 : Blo 358757 6913349 := bstep (se 4 (by rfl) ⟨648126, by rfl⟩ : syracuseStep 6913349 = 1296253) B1296253
theorem B359783 : Blo 358757 359783 := bstep (se 1 (by rfl) ⟨269837, by rfl⟩ : syracuseStep 359783 = 539675) B539675
theorem B360175 : Blo 358757 360175 := bstep (se 1 (by rfl) ⟨270131, by rfl⟩ : syracuseStep 360175 = 540263) B540263
theorem B360351 : Blo 358757 360351 := bstep (se 1 (by rfl) ⟨270263, by rfl⟩ : syracuseStep 360351 = 540527) B540527
theorem B360475 : Blo 358757 360475 := bstep (se 1 (by rfl) ⟨270356, by rfl⟩ : syracuseStep 360475 = 540713) B540713
theorem B360775 : Blo 358757 360775 := bstep (se 1 (by rfl) ⟨270581, by rfl⟩ : syracuseStep 360775 = 541163) B541163
theorem B1376747 : Blo 358757 1376747 := bstep (se 1 (by rfl) ⟨1032560, by rfl⟩ : syracuseStep 1376747 = 2065121) B2065121
theorem B2818567 : Blo 358757 2818567 := bstep (se 1 (by rfl) ⟨2113925, by rfl⟩ : syracuseStep 2818567 = 4227851) B4227851
theorem B361191 : Blo 358757 361191 := bstep (se 1 (by rfl) ⟨270893, by rfl⟩ : syracuseStep 361191 = 541787) B541787
theorem B361375 : Blo 358757 361375 := bstep (se 1 (by rfl) ⟨271031, by rfl⟩ : syracuseStep 361375 = 542063) B542063
theorem B44663885 : Blo 358757 44663885 := bstep (se 3 (by rfl) ⟨8374478, by rfl⟩ : syracuseStep 44663885 = 16748957) B16748957
theorem B12518491 : Blo 358757 12518491 := bstep (se 1 (by rfl) ⟨9388868, by rfl⟩ : syracuseStep 12518491 = 18777737) B18777737
theorem B361627 : Blo 358757 361627 := bstep (se 1 (by rfl) ⟨271220, by rfl⟩ : syracuseStep 361627 = 542441) B542441
theorem B361799 : Blo 358757 361799 := bstep (se 1 (by rfl) ⟨271349, by rfl⟩ : syracuseStep 361799 = 542699) B542699
theorem B362191 : Blo 358757 362191 := bstep (se 1 (by rfl) ⟨271643, by rfl⟩ : syracuseStep 362191 = 543287) B543287
theorem B362495 : Blo 358757 362495 := bstep (se 1 (by rfl) ⟨271871, by rfl⟩ : syracuseStep 362495 = 543743) B543743
theorem B3822750611 : Blo 358757 3822750611 := bstep (se 1 (by rfl) ⟨2867062958, by rfl⟩ : syracuseStep 3822750611 = 5734125917) B5734125917
theorem B6917345 : Blo 358757 6917345 := bstep (se 2 (by rfl) ⟨2594004, by rfl⟩ : syracuseStep 6917345 = 5188009) B5188009
theorem B19729747 : Blo 358757 19729747 := bstep (se 1 (by rfl) ⟨14797310, by rfl⟩ : syracuseStep 19729747 = 29594621) B29594621
theorem B29888021 : Blo 358757 29888021 := bstep (se 6 (by rfl) ⟨700500, by rfl⟩ : syracuseStep 29888021 = 1401001) B1401001
theorem B1216457 : Blo 358757 1216457 := bstep (se 2 (by rfl) ⟨456171, by rfl⟩ : syracuseStep 1216457 = 912343) B912343
theorem B4101353 : Blo 358757 4101353 := bstep (se 2 (by rfl) ⟨1538007, by rfl⟩ : syracuseStep 4101353 = 3076015) B3076015
theorem B4396463 : Blo 358757 4396463 := bstep (se 1 (by rfl) ⟨3297347, by rfl⟩ : syracuseStep 4396463 = 6594695) B6594695
theorem B1153199 : Blo 358757 1153199 := bstep (se 1 (by rfl) ⟨864899, by rfl⟩ : syracuseStep 1153199 = 1729799) B1729799
theorem B9836849 : Blo 358757 9836849 := bstep (se 2 (by rfl) ⟨3688818, by rfl⟩ : syracuseStep 9836849 = 7377637) B7377637
theorem B2627977 : Blo 358757 2627977 := bstep (se 2 (by rfl) ⟨985491, by rfl⟩ : syracuseStep 2627977 = 1970983) B1970983
theorem B54073817 : Blo 358757 54073817 := bstep (se 2 (by rfl) ⟨20277681, by rfl⟩ : syracuseStep 54073817 = 40555363) B40555363
theorem B1219049 : Blo 358757 1219049 := bstep (se 2 (by rfl) ⟨457143, by rfl⟩ : syracuseStep 1219049 = 914287) B914287
theorem B1546877 : Blo 358757 1546877 := bstep (se 3 (by rfl) ⟨290039, by rfl⟩ : syracuseStep 1546877 = 580079) B580079
theorem B2300861 : Blo 358757 2300861 := bstep (se 3 (by rfl) ⟨431411, by rfl⟩ : syracuseStep 2300861 = 862823) B862823
theorem B2301119 : Blo 358757 2301119 := bstep (se 1 (by rfl) ⟨1725839, by rfl⟩ : syracuseStep 2301119 = 3451679) B3451679
theorem B20061593 : Blo 358757 20061593 := bstep (se 2 (by rfl) ⟨7523097, by rfl⟩ : syracuseStep 20061593 = 15046195) B15046195
theorem B728527 : Blo 358757 728527 := bstep (se 1 (by rfl) ⟨546395, by rfl⟩ : syracuseStep 728527 = 1092791) B1092791
theorem B2728403 : Blo 358757 2728403 := bstep (se 1 (by rfl) ⟨2046302, by rfl⟩ : syracuseStep 2728403 = 4092605) B4092605
theorem B2205431 : Blo 358757 2205431 := bstep (se 1 (by rfl) ⟨1654073, by rfl⟩ : syracuseStep 2205431 = 3308147) B3308147
theorem B1943689 : Blo 358757 1943689 := bstep (se 2 (by rfl) ⟨728883, by rfl⟩ : syracuseStep 1943689 = 1457767) B1457767
theorem B1026751 : Blo 358757 1026751 := bstep (se 1 (by rfl) ⟨770063, by rfl⟩ : syracuseStep 1026751 = 1540127) B1540127
theorem B2730833 : Blo 358757 2730833 := bstep (se 2 (by rfl) ⟨1024062, by rfl⟩ : syracuseStep 2730833 = 2048125) B2048125
theorem B1223639 : Blo 358757 1223639 := bstep (se 1 (by rfl) ⟨917729, by rfl⟩ : syracuseStep 1223639 = 1835459) B1835459
theorem B437815 : Blo 358757 437815 := bstep (se 1 (by rfl) ⟨328361, by rfl⟩ : syracuseStep 437815 = 656723) B656723
theorem B4992641 : Blo 358757 4992641 := bstep (se 2 (by rfl) ⟨1872240, by rfl⟩ : syracuseStep 4992641 = 3744481) B3744481
theorem B1191677 : Blo 358757 1191677 := bstep (se 3 (by rfl) ⟨223439, by rfl⟩ : syracuseStep 1191677 = 446879) B446879
theorem B3486199 : Blo 358757 3486199 := bstep (se 1 (by rfl) ⟨2614649, by rfl⟩ : syracuseStep 3486199 = 5229299) B5229299
theorem B538367 : Blo 358757 538367 := bstep (se 1 (by rfl) ⟨403775, by rfl⟩ : syracuseStep 538367 = 807551) B807551
theorem B538535 : Blo 358757 538535 := bstep (se 1 (by rfl) ⟨403901, by rfl⟩ : syracuseStep 538535 = 807803) B807803
theorem B2602975 : Blo 358757 2602975 := bstep (se 1 (by rfl) ⟨1952231, by rfl⟩ : syracuseStep 2602975 = 3904463) B3904463
theorem B538799 : Blo 358757 538799 := bstep (se 1 (by rfl) ⟨404099, by rfl⟩ : syracuseStep 538799 = 808199) B808199
theorem B538847 : Blo 358757 538847 := bstep (se 1 (by rfl) ⟨404135, by rfl⟩ : syracuseStep 538847 = 808271) B808271
theorem B407803 : Blo 358757 407803 := bstep (se 1 (by rfl) ⟨305852, by rfl⟩ : syracuseStep 407803 = 611705) B611705
theorem B539129 : Blo 358757 539129 := bstep (se 2 (by rfl) ⟨202173, by rfl⟩ : syracuseStep 539129 = 404347) B404347
theorem B4602541 : Blo 358757 4602541 := bstep (se 3 (by rfl) ⟨862976, by rfl⟩ : syracuseStep 4602541 = 1725953) B1725953
theorem B539387 : Blo 358757 539387 := bstep (se 1 (by rfl) ⟨404540, by rfl⟩ : syracuseStep 539387 = 809081) B809081
theorem B539519 : Blo 358757 539519 := bstep (se 1 (by rfl) ⟨404639, by rfl⟩ : syracuseStep 539519 = 809279) B809279
theorem B1293185 : Blo 358757 1293185 := bstep (se 2 (by rfl) ⟨484944, by rfl⟩ : syracuseStep 1293185 = 969889) B969889
theorem B539615 : Blo 358757 539615 := bstep (se 1 (by rfl) ⟨404711, by rfl⟩ : syracuseStep 539615 = 809423) B809423
theorem B6274145 : Blo 358757 6274145 := bstep (se 2 (by rfl) ⟨2352804, by rfl⟩ : syracuseStep 6274145 = 4705609) B4705609
theorem B540215 : Blo 358757 540215 := bstep (se 1 (by rfl) ⟨405161, by rfl⟩ : syracuseStep 540215 = 810323) B810323
theorem B606143 : Blo 358757 606143 := bstep (se 1 (by rfl) ⟨454607, by rfl⟩ : syracuseStep 606143 = 909215) B909215
theorem B1556777 : Blo 358757 1556777 := bstep (se 2 (by rfl) ⟨583791, by rfl⟩ : syracuseStep 1556777 = 1167583) B1167583
theorem B541097 : Blo 358757 541097 := bstep (se 2 (by rfl) ⟨202911, by rfl⟩ : syracuseStep 541097 = 405823) B405823
theorem B869071 : Blo 358757 869071 := bstep (se 1 (by rfl) ⟨651803, by rfl⟩ : syracuseStep 869071 = 1303607) B1303607
theorem B541823 : Blo 358757 541823 := bstep (se 1 (by rfl) ⟨406367, by rfl⟩ : syracuseStep 541823 = 812735) B812735
theorem B542249 : Blo 358757 542249 := bstep (se 2 (by rfl) ⟨203343, by rfl⟩ : syracuseStep 542249 = 406687) B406687
theorem B542255 : Blo 358757 542255 := bstep (se 1 (by rfl) ⟨406691, by rfl⟩ : syracuseStep 542255 = 813383) B813383
theorem B1820393 : Blo 358757 1820393 := bstep (se 2 (by rfl) ⟨682647, by rfl⟩ : syracuseStep 1820393 = 1365295) B1365295
theorem B771977 : Blo 358757 771977 := bstep (se 2 (by rfl) ⟨289491, by rfl⟩ : syracuseStep 771977 = 578983) B578983
theorem B19810325 : Blo 358757 19810325 := bstep (se 6 (by rfl) ⟨464304, by rfl⟩ : syracuseStep 19810325 = 928609) B928609
theorem B542975 : Blo 358757 542975 := bstep (se 1 (by rfl) ⟨407231, by rfl⟩ : syracuseStep 542975 = 814463) B814463
theorem B543167 : Blo 358757 543167 := bstep (se 1 (by rfl) ⟨407375, by rfl⟩ : syracuseStep 543167 = 814751) B814751
theorem B543551 : Blo 358757 543551 := bstep (se 1 (by rfl) ⟨407663, by rfl⟩ : syracuseStep 543551 = 815327) B815327
theorem B543611 : Blo 358757 543611 := bstep (se 1 (by rfl) ⟨407708, by rfl⟩ : syracuseStep 543611 = 815417) B815417
theorem B2051567 : Blo 358757 2051567 := bstep (se 1 (by rfl) ⟨1538675, by rfl⟩ : syracuseStep 2051567 = 3077351) B3077351
theorem B610139 : Blo 358757 610139 := bstep (se 1 (by rfl) ⟨457604, by rfl⟩ : syracuseStep 610139 = 915209) B915209
theorem B1364111 : Blo 358757 1364111 := bstep (se 1 (by rfl) ⟨1023083, by rfl⟩ : syracuseStep 1364111 = 2046167) B2046167
theorem B611023 : Blo 358757 611023 := bstep (se 1 (by rfl) ⟨458267, by rfl⟩ : syracuseStep 611023 = 916535) B916535
theorem B4608899 : Blo 358757 4608899 := bstep (se 1 (by rfl) ⟨3456674, by rfl⟩ : syracuseStep 4608899 = 6913349) B6913349
theorem B1366267 : Blo 358757 1366267 := bstep (se 1 (by rfl) ⟨1024700, by rfl⟩ : syracuseStep 1366267 = 2049401) B2049401
theorem B1825091 : Blo 358757 1825091 := bstep (se 1 (by rfl) ⟨1368818, by rfl⟩ : syracuseStep 1825091 = 2737637) B2737637
theorem B809387 : Blo 358757 809387 := bstep (se 1 (by rfl) ⟨607040, by rfl⟩ : syracuseStep 809387 = 1214081) B1214081
theorem B4120307 : Blo 358757 4120307 := bstep (se 1 (by rfl) ⟨3090230, by rfl⟩ : syracuseStep 4120307 = 6180461) B6180461
theorem B4382543 : Blo 358757 4382543 := bstep (se 1 (by rfl) ⟨3286907, by rfl⟩ : syracuseStep 4382543 = 6573815) B6573815
theorem B811367 : Blo 358757 811367 := bstep (se 1 (by rfl) ⟨608525, by rfl⟩ : syracuseStep 811367 = 1217051) B1217051
theorem B1827359 : Blo 358757 1827359 := bstep (se 1 (by rfl) ⟨1370519, by rfl⟩ : syracuseStep 1827359 = 2741039) B2741039
theorem B386651 : Blo 358757 386651 := bstep (se 1 (by rfl) ⟨289988, by rfl⟩ : syracuseStep 386651 = 579977) B579977
theorem B976637 : Blo 358757 976637 := bstep (se 3 (by rfl) ⟨183119, by rfl⟩ : syracuseStep 976637 = 366239) B366239
theorem B517979 : Blo 358757 517979 := bstep (se 1 (by rfl) ⟨388484, by rfl⟩ : syracuseStep 517979 = 776969) B776969
theorem B813311 : Blo 358757 813311 := bstep (se 1 (by rfl) ⟨609983, by rfl⟩ : syracuseStep 813311 = 1219967) B1219967
theorem B4909679 : Blo 358757 4909679 := bstep (se 1 (by rfl) ⟨3682259, by rfl⟩ : syracuseStep 4909679 = 7364519) B7364519
theorem B813851 : Blo 358757 813851 := bstep (se 1 (by rfl) ⟨610388, by rfl⟩ : syracuseStep 813851 = 1220777) B1220777
theorem B846703 : Blo 358757 846703 := bstep (se 1 (by rfl) ⟨635027, by rfl⟩ : syracuseStep 846703 = 1270055) B1270055
theorem B814427 : Blo 358757 814427 := bstep (se 1 (by rfl) ⟨610820, by rfl⟩ : syracuseStep 814427 = 1221641) B1221641
theorem B22180205 : Blo 358757 22180205 := bstep (se 3 (by rfl) ⟨4158788, by rfl⟩ : syracuseStep 22180205 = 8317577) B8317577
theorem B1733183 : Blo 358757 1733183 := bstep (se 1 (by rfl) ⟨1299887, by rfl⟩ : syracuseStep 1733183 = 2599775) B2599775
theorem B3437161 : Blo 358757 3437161 := bstep (se 2 (by rfl) ⟨1288935, by rfl⟩ : syracuseStep 3437161 = 2577871) B2577871
theorem B488063 : Blo 358757 488063 := bstep (se 1 (by rfl) ⟨366047, by rfl⟩ : syracuseStep 488063 = 732095) B732095
theorem B2323187 : Blo 358757 2323187 := bstep (se 1 (by rfl) ⟨1742390, by rfl⟩ : syracuseStep 2323187 = 3484781) B3484781
theorem B1832057 : Blo 358757 1832057 := bstep (se 2 (by rfl) ⟨687021, by rfl⟩ : syracuseStep 1832057 = 1374043) B1374043
theorem B29652439 : Blo 358757 29652439 := bstep (se 1 (by rfl) ⟨22239329, by rfl⟩ : syracuseStep 29652439 = 44478659) B44478659
theorem B1374317 : Blo 358757 1374317 := bstep (se 3 (by rfl) ⟨257684, by rfl⟩ : syracuseStep 1374317 = 515369) B515369
theorem B2750759 : Blo 358757 2750759 := bstep (se 1 (by rfl) ⟨2063069, by rfl⟩ : syracuseStep 2750759 = 4126139) B4126139
theorem B18152099 : Blo 358757 18152099 := bstep (se 1 (by rfl) ⟨13614074, by rfl⟩ : syracuseStep 18152099 = 27228149) B27228149
theorem B359163 : Blo 358757 359163 := bstep (se 1 (by rfl) ⟨269372, by rfl⟩ : syracuseStep 359163 = 538745) B538745
theorem B1375015 : Blo 358757 1375015 := bstep (se 1 (by rfl) ⟨1031261, by rfl⟩ : syracuseStep 1375015 = 2062523) B2062523
theorem B359707 : Blo 358757 359707 := bstep (se 1 (by rfl) ⟨269780, by rfl⟩ : syracuseStep 359707 = 539561) B539561
theorem B360095 : Blo 358757 360095 := bstep (se 1 (by rfl) ⟨270071, by rfl⟩ : syracuseStep 360095 = 540143) B540143
theorem B360127 : Blo 358757 360127 := bstep (se 1 (by rfl) ⟨270095, by rfl⟩ : syracuseStep 360127 = 540191) B540191
theorem B360731 : Blo 358757 360731 := bstep (se 1 (by rfl) ⟨270548, by rfl⟩ : syracuseStep 360731 = 541097) B541097
theorem B917831 : Blo 358757 917831 := bstep (se 1 (by rfl) ⟨688373, by rfl⟩ : syracuseStep 917831 = 1376747) B1376747
theorem B361215 : Blo 358757 361215 := bstep (se 1 (by rfl) ⟨270911, by rfl⟩ : syracuseStep 361215 = 541823) B541823
theorem B361499 : Blo 358757 361499 := bstep (se 1 (by rfl) ⟨271124, by rfl⟩ : syracuseStep 361499 = 542249) B542249
theorem B361503 : Blo 358757 361503 := bstep (se 1 (by rfl) ⟨271127, by rfl⟩ : syracuseStep 361503 = 542255) B542255
theorem B1213595 : Blo 358757 1213595 := bstep (se 1 (by rfl) ⟨910196, by rfl⟩ : syracuseStep 1213595 = 1820393) B1820393
theorem B13206883 : Blo 358757 13206883 := bstep (se 1 (by rfl) ⟨9905162, by rfl⟩ : syracuseStep 13206883 = 19810325) B19810325
theorem B361983 : Blo 358757 361983 := bstep (se 1 (by rfl) ⟨271487, by rfl⟩ : syracuseStep 361983 = 542975) B542975
theorem B362111 : Blo 358757 362111 := bstep (se 1 (by rfl) ⟨271583, by rfl⟩ : syracuseStep 362111 = 543167) B543167
theorem B362367 : Blo 358757 362367 := bstep (se 1 (by rfl) ⟨271775, by rfl⟩ : syracuseStep 362367 = 543551) B543551
theorem B362407 : Blo 358757 362407 := bstep (se 1 (by rfl) ⟨271805, by rfl⟩ : syracuseStep 362407 = 543611) B543611
theorem B2548500407 : Blo 358757 2548500407 := bstep (se 1 (by rfl) ⟨1911375305, by rfl⟩ : syracuseStep 2548500407 = 3822750611) B3822750611
theorem B19925347 : Blo 358757 19925347 := bstep (se 1 (by rfl) ⟨14944010, by rfl⟩ : syracuseStep 19925347 = 29888021) B29888021
theorem B2591585 : Blo 358757 2591585 := bstep (se 2 (by rfl) ⟨971844, by rfl⟩ : syracuseStep 2591585 = 1943689) B1943689
theorem B1216727 : Blo 358757 1216727 := bstep (se 1 (by rfl) ⟨912545, by rfl⟩ : syracuseStep 1216727 = 1825091) B1825091
theorem B36049211 : Blo 358757 36049211 := bstep (se 1 (by rfl) ⟨27036908, by rfl⟩ : syracuseStep 36049211 = 54073817) B54073817
theorem B1381277 : Blo 358757 1381277 := bstep (se 3 (by rfl) ⟨258989, by rfl⟩ : syracuseStep 1381277 = 517979) B517979
theorem B13374395 : Blo 358757 13374395 := bstep (se 1 (by rfl) ⟨10030796, by rfl⟩ : syracuseStep 13374395 = 20061593) B20061593
theorem B1218239 : Blo 358757 1218239 := bstep (se 1 (by rfl) ⟨913679, by rfl⟩ : syracuseStep 1218239 = 1827359) B1827359
theorem B105225317 : Blo 358757 105225317 := bstep (se 4 (by rfl) ⟨9864873, by rfl⟩ : syracuseStep 105225317 = 19729747) B19729747
theorem B14786803 : Blo 358757 14786803 := bstep (se 1 (by rfl) ⟨11090102, by rfl⟩ : syracuseStep 14786803 = 22180205) B22180205
theorem B1155455 : Blo 358757 1155455 := bstep (se 1 (by rfl) ⟨866591, by rfl⟩ : syracuseStep 1155455 = 1733183) B1733183
theorem B1548791 : Blo 358757 1548791 := bstep (se 1 (by rfl) ⟨1161593, by rfl⟩ : syracuseStep 1548791 = 2323187) B2323187
theorem B1221371 : Blo 358757 1221371 := bstep (se 1 (by rfl) ⟨916028, by rfl⟩ : syracuseStep 1221371 = 1832057) B1832057
theorem B6136721 : Blo 358757 6136721 := bstep (se 2 (by rfl) ⟨2301270, by rfl⟩ : syracuseStep 6136721 = 4602541) B4602541
theorem B12101399 : Blo 358757 12101399 := bstep (se 1 (by rfl) ⟨9076049, by rfl⟩ : syracuseStep 12101399 = 18152099) B18152099
theorem B862123 : Blo 358757 862123 := bstep (se 1 (by rfl) ⟨646592, by rfl⟩ : syracuseStep 862123 = 1293185) B1293185
theorem B404095 : Blo 358757 404095 := bstep (se 1 (by rfl) ⟨303071, by rfl⟩ : syracuseStep 404095 = 606143) B606143
theorem B1158761 : Blo 358757 1158761 := bstep (se 2 (by rfl) ⟨434535, by rfl⟩ : syracuseStep 1158761 = 869071) B869071
theorem B16691321 : Blo 358757 16691321 := bstep (se 2 (by rfl) ⟨6259245, by rfl⟩ : syracuseStep 16691321 = 12518491) B12518491
theorem B406759 : Blo 358757 406759 := bstep (se 1 (by rfl) ⟨305069, by rfl⟩ : syracuseStep 406759 = 610139) B610139
theorem B18331525 : Blo 358757 18331525 := bstep (se 4 (by rfl) ⟨1718580, by rfl⟩ : syracuseStep 18331525 = 3437161) B3437161
theorem B2734235 : Blo 358757 2734235 := bstep (se 1 (by rfl) ⟨2050676, by rfl⟩ : syracuseStep 2734235 = 4101353) B4101353
theorem B2930975 : Blo 358757 2930975 := bstep (se 1 (by rfl) ⟨2198231, by rfl⟩ : syracuseStep 2930975 = 4396463) B4396463
theorem B768799 : Blo 358757 768799 := bstep (se 1 (by rfl) ⟨576599, by rfl⟩ : syracuseStep 768799 = 1153199) B1153199
theorem B1031069 : Blo 358757 1031069 := bstep (se 3 (by rfl) ⟨193325, by rfl⟩ : syracuseStep 1031069 = 386651) B386651
theorem B539591 : Blo 358757 539591 := bstep (se 1 (by rfl) ⟨404693, by rfl⟩ : syracuseStep 539591 = 809387) B809387
theorem B1031251 : Blo 358757 1031251 := bstep (se 1 (by rfl) ⟨773438, by rfl⟩ : syracuseStep 1031251 = 1546877) B1546877
theorem B540911 : Blo 358757 540911 := bstep (se 1 (by rfl) ⟨405683, by rfl⟩ : syracuseStep 540911 = 811367) B811367
theorem B1818935 : Blo 358757 1818935 := bstep (se 1 (by rfl) ⟨1364201, by rfl⟩ : syracuseStep 1818935 = 2728403) B2728403
theorem B26231597 : Blo 358757 26231597 := bstep (se 3 (by rfl) ⟨4918424, by rfl⟩ : syracuseStep 26231597 = 9836849) B9836849
theorem B542207 : Blo 358757 542207 := bstep (se 1 (by rfl) ⟨406655, by rfl⟩ : syracuseStep 542207 = 813311) B813311
theorem B542567 : Blo 358757 542567 := bstep (se 1 (by rfl) ⟨406925, by rfl⟩ : syracuseStep 542567 = 813851) B813851
theorem B1820555 : Blo 358757 1820555 := bstep (se 1 (by rfl) ⟨1365416, by rfl⟩ : syracuseStep 1820555 = 2730833) B2730833
theorem B39536585 : Blo 358757 39536585 := bstep (se 2 (by rfl) ⟨14826219, by rfl⟩ : syracuseStep 39536585 = 29652439) B29652439
theorem B542951 : Blo 358757 542951 := bstep (se 1 (by rfl) ⟨407213, by rfl⟩ : syracuseStep 542951 = 814427) B814427
theorem B3328427 : Blo 358757 3328427 := bstep (se 1 (by rfl) ⟨2496320, by rfl⟩ : syracuseStep 3328427 = 4992641) B4992641
theorem B1821689 : Blo 358757 1821689 := bstep (se 2 (by rfl) ⟨683133, by rfl⟩ : syracuseStep 1821689 = 1366267) B1366267
theorem B543737 : Blo 358757 543737 := bstep (se 2 (by rfl) ⟨203901, by rfl⟩ : syracuseStep 543737 = 407803) B407803
theorem B971369 : Blo 358757 971369 := bstep (se 2 (by rfl) ⟨364263, by rfl⟩ : syracuseStep 971369 = 728527) B728527
theorem B4182763 : Blo 358757 4182763 := bstep (se 1 (by rfl) ⟨3137072, by rfl⟩ : syracuseStep 4182763 = 6274145) B6274145
theorem B11686781 : Blo 358757 11686781 := bstep (se 3 (by rfl) ⟨2191271, by rfl⟩ : syracuseStep 11686781 = 4382543) B4382543
theorem B3758089 : Blo 358757 3758089 := bstep (se 2 (by rfl) ⟨1409283, by rfl⟩ : syracuseStep 3758089 = 2818567) B2818567
theorem B29775923 : Blo 358757 29775923 := bstep (se 1 (by rfl) ⟨22331942, by rfl⟩ : syracuseStep 29775923 = 44663885) B44663885
theorem B4151405 : Blo 358757 4151405 := bstep (se 3 (by rfl) ⟨778388, by rfl⟩ : syracuseStep 4151405 = 1556777) B1556777
theorem B1301501 : Blo 358757 1301501 := bstep (se 3 (by rfl) ⟨244031, by rfl⟩ : syracuseStep 1301501 = 488063) B488063
theorem B4611563 : Blo 358757 4611563 := bstep (se 1 (by rfl) ⟨3458672, by rfl⟩ : syracuseStep 4611563 = 6917345) B6917345
theorem B1367711 : Blo 358757 1367711 := bstep (se 1 (by rfl) ⟨1025783, by rfl⟩ : syracuseStep 1367711 = 2051567) B2051567
theorem B810971 : Blo 358757 810971 := bstep (se 1 (by rfl) ⟨608228, by rfl⟩ : syracuseStep 810971 = 1216457) B1216457
theorem B909407 : Blo 358757 909407 := bstep (se 1 (by rfl) ⟨682055, by rfl⟩ : syracuseStep 909407 = 1364111) B1364111
theorem B3072599 : Blo 358757 3072599 := bstep (se 1 (by rfl) ⟨2304449, by rfl⟩ : syracuseStep 3072599 = 4608899) B4608899
theorem B1369001 : Blo 358757 1369001 := bstep (se 2 (by rfl) ⟨513375, by rfl⟩ : syracuseStep 1369001 = 1026751) B1026751
theorem B812699 : Blo 358757 812699 := bstep (se 1 (by rfl) ⟨609524, by rfl⟩ : syracuseStep 812699 = 1219049) B1219049
theorem B4515749 : Blo 358757 4515749 := bstep (se 4 (by rfl) ⟨423351, by rfl⟩ : syracuseStep 4515749 = 846703) B846703
theorem B1533907 : Blo 358757 1533907 := bstep (se 1 (by rfl) ⟨1150430, by rfl⟩ : syracuseStep 1533907 = 2300861) B2300861
theorem B583753 : Blo 358757 583753 := bstep (se 2 (by rfl) ⟨218907, by rfl⟩ : syracuseStep 583753 = 437815) B437815
theorem B1534079 : Blo 358757 1534079 := bstep (se 1 (by rfl) ⟨1150559, by rfl⟩ : syracuseStep 1534079 = 2301119) B2301119
theorem B2058605 : Blo 358757 2058605 := bstep (se 3 (by rfl) ⟨385988, by rfl⟩ : syracuseStep 2058605 = 771977) B771977
theorem B2746871 : Blo 358757 2746871 := bstep (se 1 (by rfl) ⟨2060153, by rfl⟩ : syracuseStep 2746871 = 4120307) B4120307
theorem B4648265 : Blo 358757 4648265 := bstep (se 2 (by rfl) ⟨1743099, by rfl⟩ : syracuseStep 4648265 = 3486199) B3486199
theorem B814697 : Blo 358757 814697 := bstep (se 2 (by rfl) ⟨305511, by rfl⟩ : syracuseStep 814697 = 611023) B611023
theorem B1470287 : Blo 358757 1470287 := bstep (se 1 (by rfl) ⟨1102715, by rfl⟩ : syracuseStep 1470287 = 2205431) B2205431
theorem B651091 : Blo 358757 651091 := bstep (se 1 (by rfl) ⟨488318, by rfl⟩ : syracuseStep 651091 = 976637) B976637
theorem B3273119 : Blo 358757 3273119 := bstep (se 1 (by rfl) ⟨2454839, by rfl⟩ : syracuseStep 3273119 = 4909679) B4909679
theorem B815759 : Blo 358757 815759 := bstep (se 1 (by rfl) ⟨611819, by rfl⟩ : syracuseStep 815759 = 1223639) B1223639
theorem B3470633 : Blo 358757 3470633 := bstep (se 2 (by rfl) ⟨1301487, by rfl⟩ : syracuseStep 3470633 = 2602975) B2602975
theorem B12711221 : Blo 358757 12711221 := bstep (se 5 (by rfl) ⟨595838, by rfl⟩ : syracuseStep 12711221 = 1191677) B1191677
theorem B3503969 : Blo 358757 3503969 := bstep (se 2 (by rfl) ⟨1313988, by rfl⟩ : syracuseStep 3503969 = 2627977) B2627977
theorem B1833353 : Blo 358757 1833353 := bstep (se 2 (by rfl) ⟨687507, by rfl⟩ : syracuseStep 1833353 = 1375015) B1375015
theorem B358911 : Blo 358757 358911 := bstep (se 1 (by rfl) ⟨269183, by rfl⟩ : syracuseStep 358911 = 538367) B538367
theorem B359023 : Blo 358757 359023 := bstep (se 1 (by rfl) ⟨269267, by rfl⟩ : syracuseStep 359023 = 538535) B538535
theorem B916211 : Blo 358757 916211 := bstep (se 1 (by rfl) ⟨687158, by rfl⟩ : syracuseStep 916211 = 1374317) B1374317
theorem B359199 : Blo 358757 359199 := bstep (se 1 (by rfl) ⟨269399, by rfl⟩ : syracuseStep 359199 = 538799) B538799
theorem B359231 : Blo 358757 359231 := bstep (se 1 (by rfl) ⟨269423, by rfl⟩ : syracuseStep 359231 = 538847) B538847
theorem B1833839 : Blo 358757 1833839 := bstep (se 1 (by rfl) ⟨1375379, by rfl⟩ : syracuseStep 1833839 = 2750759) B2750759
theorem B359419 : Blo 358757 359419 := bstep (se 1 (by rfl) ⟨269564, by rfl⟩ : syracuseStep 359419 = 539129) B539129
theorem B359591 : Blo 358757 359591 := bstep (se 1 (by rfl) ⟨269693, by rfl⟩ : syracuseStep 359591 = 539387) B539387
theorem B359679 : Blo 358757 359679 := bstep (se 1 (by rfl) ⟨269759, by rfl⟩ : syracuseStep 359679 = 539519) B539519
theorem B359743 : Blo 358757 359743 := bstep (se 1 (by rfl) ⟨269807, by rfl⟩ : syracuseStep 359743 = 539615) B539615
theorem B360143 : Blo 358757 360143 := bstep (se 1 (by rfl) ⟨270107, by rfl⟩ : syracuseStep 360143 = 540215) B540215
theorem B360607 : Blo 358757 360607 := bstep (se 1 (by rfl) ⟨270455, by rfl⟩ : syracuseStep 360607 = 540911) B540911
theorem B1212623 : Blo 358757 1212623 := bstep (se 1 (by rfl) ⟨909467, by rfl⟩ : syracuseStep 1212623 = 1818935) B1818935
theorem B361471 : Blo 358757 361471 := bstep (se 1 (by rfl) ⟨271103, by rfl⟩ : syracuseStep 361471 = 542207) B542207
theorem B361711 : Blo 358757 361711 := bstep (se 1 (by rfl) ⟨271283, by rfl⟩ : syracuseStep 361711 = 542567) B542567
theorem B1213703 : Blo 358757 1213703 := bstep (se 1 (by rfl) ⟨910277, by rfl⟩ : syracuseStep 1213703 = 1820555) B1820555
theorem B361967 : Blo 358757 361967 := bstep (se 1 (by rfl) ⟨271475, by rfl⟩ : syracuseStep 361967 = 542951) B542951
theorem B1214459 : Blo 358757 1214459 := bstep (se 1 (by rfl) ⟨910844, by rfl⟩ : syracuseStep 1214459 = 1821689) B1821689
theorem B362491 : Blo 358757 362491 := bstep (se 1 (by rfl) ⟨271868, by rfl⟩ : syracuseStep 362491 = 543737) B543737
theorem B1149497 : Blo 358757 1149497 := bstep (se 2 (by rfl) ⟨431061, by rfl⟩ : syracuseStep 1149497 = 862123) B862123
theorem B920851 : Blo 358757 920851 := bstep (se 1 (by rfl) ⟨690638, by rfl⟩ : syracuseStep 920851 = 1381277) B1381277
theorem B8916263 : Blo 358757 8916263 := bstep (se 1 (by rfl) ⟨6687197, by rfl⟩ : syracuseStep 8916263 = 13374395) B13374395
theorem B5577017 : Blo 358757 5577017 := bstep (se 2 (by rfl) ⟨2091381, by rfl⟩ : syracuseStep 5577017 = 4182763) B4182763
theorem B8067599 : Blo 358757 8067599 := bstep (se 1 (by rfl) ⟨6050699, by rfl⟩ : syracuseStep 8067599 = 12101399) B12101399
theorem B1022719 : Blo 358757 1022719 := bstep (se 1 (by rfl) ⟨767039, by rfl⟩ : syracuseStep 1022719 = 1534079) B1534079
theorem B1025065 : Blo 358757 1025065 := bstep (se 2 (by rfl) ⟨384399, by rfl⟩ : syracuseStep 1025065 = 768799) B768799
theorem B2335979 : Blo 358757 2335979 := bstep (se 1 (by rfl) ⟨1751984, by rfl⟩ : syracuseStep 2335979 = 3503969) B3503969
theorem B1222235 : Blo 358757 1222235 := bstep (se 1 (by rfl) ⟨916676, by rfl⟩ : syracuseStep 1222235 = 1833353) B1833353
theorem B1222559 : Blo 358757 1222559 := bstep (se 1 (by rfl) ⟨916919, by rfl⟩ : syracuseStep 1222559 = 1833839) B1833839
theorem B1699000271 : Blo 358757 1699000271 := bstep (se 1 (by rfl) ⟨1274250203, by rfl⟩ : syracuseStep 1699000271 = 2548500407) B2548500407
theorem B26357723 : Blo 358757 26357723 := bstep (se 1 (by rfl) ⟨19768292, by rfl⟩ : syracuseStep 26357723 = 39536585) B39536585
theorem B17609177 : Blo 358757 17609177 := bstep (se 2 (by rfl) ⟨6603441, by rfl⟩ : syracuseStep 17609177 = 13206883) B13206883
theorem B2045209 : Blo 358757 2045209 := bstep (se 2 (by rfl) ⟨766953, by rfl⟩ : syracuseStep 2045209 = 1533907) B1533907
theorem B24032807 : Blo 358757 24032807 := bstep (se 1 (by rfl) ⟨18024605, by rfl⟩ : syracuseStep 24032807 = 36049211) B36049211
theorem B538793 : Blo 358757 538793 := bstep (se 2 (by rfl) ⟨202047, by rfl⟩ : syracuseStep 538793 = 404095) B404095
theorem B2767603 : Blo 358757 2767603 := bstep (se 1 (by rfl) ⟨2075702, by rfl⟩ : syracuseStep 2767603 = 4151405) B4151405
theorem B867667 : Blo 358757 867667 := bstep (se 1 (by rfl) ⟨650750, by rfl⟩ : syracuseStep 867667 = 1301501) B1301501
theorem B868121 : Blo 358757 868121 := bstep (se 2 (by rfl) ⟨325545, by rfl⟩ : syracuseStep 868121 = 651091) B651091
theorem B540647 : Blo 358757 540647 := bstep (se 1 (by rfl) ⟨405485, by rfl⟩ : syracuseStep 540647 = 810971) B810971
theorem B606271 : Blo 358757 606271 := bstep (se 1 (by rfl) ⟨454703, by rfl⟩ : syracuseStep 606271 = 909407) B909407
theorem B770303 : Blo 358757 770303 := bstep (se 1 (by rfl) ⟨577727, by rfl⟩ : syracuseStep 770303 = 1155455) B1155455
theorem B1032527 : Blo 358757 1032527 := bstep (se 1 (by rfl) ⟨774395, by rfl⟩ : syracuseStep 1032527 = 1548791) B1548791
theorem B2048399 : Blo 358757 2048399 := bstep (se 1 (by rfl) ⟨1536299, by rfl⟩ : syracuseStep 2048399 = 3072599) B3072599
theorem B541799 : Blo 358757 541799 := bstep (se 1 (by rfl) ⟨406349, by rfl⟩ : syracuseStep 541799 = 812699) B812699
theorem B542345 : Blo 358757 542345 := bstep (se 2 (by rfl) ⟨203379, by rfl⟩ : syracuseStep 542345 = 406759) B406759
theorem B3098843 : Blo 358757 3098843 := bstep (se 1 (by rfl) ⟨2324132, by rfl⟩ : syracuseStep 3098843 = 4648265) B4648265
theorem B772507 : Blo 358757 772507 := bstep (se 1 (by rfl) ⟨579380, by rfl⟩ : syracuseStep 772507 = 1158761) B1158761
theorem B543131 : Blo 358757 543131 := bstep (se 1 (by rfl) ⟨407348, by rfl⟩ : syracuseStep 543131 = 814697) B814697
theorem B11127547 : Blo 358757 11127547 := bstep (se 1 (by rfl) ⟨8345660, by rfl⟩ : syracuseStep 11127547 = 16691321) B16691321
theorem B2182079 : Blo 358757 2182079 := bstep (se 1 (by rfl) ⟨1636559, by rfl⟩ : syracuseStep 2182079 = 3273119) B3273119
theorem B543839 : Blo 358757 543839 := bstep (se 1 (by rfl) ⟨407879, by rfl⟩ : syracuseStep 543839 = 815759) B815759
theorem B2313755 : Blo 358757 2313755 := bstep (se 1 (by rfl) ⟨1735316, by rfl⟩ : syracuseStep 2313755 = 3470633) B3470633
theorem B8474147 : Blo 358757 8474147 := bstep (se 1 (by rfl) ⟨6355610, by rfl⟩ : syracuseStep 8474147 = 12711221) B12711221
theorem B1822823 : Blo 358757 1822823 := bstep (se 1 (by rfl) ⟨1367117, by rfl⟩ : syracuseStep 1822823 = 2734235) B2734235
theorem B1953983 : Blo 358757 1953983 := bstep (se 1 (by rfl) ⟨1465487, by rfl⟩ : syracuseStep 1953983 = 2930975) B2930975
theorem B610807 : Blo 358757 610807 := bstep (se 1 (by rfl) ⟨458105, by rfl⟩ : syracuseStep 610807 = 916211) B916211
theorem B611887 : Blo 358757 611887 := bstep (se 1 (by rfl) ⟨458915, by rfl⟩ : syracuseStep 611887 = 917831) B917831
theorem B19715737 : Blo 358757 19715737 := bstep (se 2 (by rfl) ⟨7393401, by rfl⟩ : syracuseStep 19715737 = 14786803) B14786803
theorem B17487731 : Blo 358757 17487731 := bstep (se 1 (by rfl) ⟨13115798, by rfl⟩ : syracuseStep 17487731 = 26231597) B26231597
theorem B809063 : Blo 358757 809063 := bstep (se 1 (by rfl) ⟨606797, by rfl⟩ : syracuseStep 809063 = 1213595) B1213595
theorem B2218951 : Blo 358757 2218951 := bstep (se 1 (by rfl) ⟨1664213, by rfl⟩ : syracuseStep 2218951 = 3328427) B3328427
theorem B1727723 : Blo 358757 1727723 := bstep (se 1 (by rfl) ⟨1295792, by rfl⟩ : syracuseStep 1727723 = 2591585) B2591585
theorem B778337 : Blo 358757 778337 := bstep (se 2 (by rfl) ⟨291876, by rfl⟩ : syracuseStep 778337 = 583753) B583753
theorem B811151 : Blo 358757 811151 := bstep (se 1 (by rfl) ⟨608363, by rfl⟩ : syracuseStep 811151 = 1216727) B1216727
theorem B647579 : Blo 358757 647579 := bstep (se 1 (by rfl) ⟨485684, by rfl⟩ : syracuseStep 647579 = 971369) B971369
theorem B26567129 : Blo 358757 26567129 := bstep (se 2 (by rfl) ⟨9962673, by rfl⟩ : syracuseStep 26567129 = 19925347) B19925347
theorem B7791187 : Blo 358757 7791187 := bstep (se 1 (by rfl) ⟨5843390, by rfl⟩ : syracuseStep 7791187 = 11686781) B11686781
theorem B812159 : Blo 358757 812159 := bstep (se 1 (by rfl) ⟨609119, by rfl⟩ : syracuseStep 812159 = 1218239) B1218239
theorem B19850615 : Blo 358757 19850615 := bstep (se 1 (by rfl) ⟨14887961, by rfl⟩ : syracuseStep 19850615 = 29775923) B29775923
theorem B70150211 : Blo 358757 70150211 := bstep (se 1 (by rfl) ⟨52612658, by rfl⟩ : syracuseStep 70150211 = 105225317) B105225317
theorem B3074375 : Blo 358757 3074375 := bstep (se 1 (by rfl) ⟨2305781, by rfl⟩ : syracuseStep 3074375 = 4611563) B4611563
theorem B911807 : Blo 358757 911807 := bstep (se 1 (by rfl) ⟨683855, by rfl⟩ : syracuseStep 911807 = 1367711) B1367711
theorem B814247 : Blo 358757 814247 := bstep (se 1 (by rfl) ⟨610685, by rfl⟩ : syracuseStep 814247 = 1221371) B1221371
theorem B4091147 : Blo 358757 4091147 := bstep (se 1 (by rfl) ⟨3068360, by rfl⟩ : syracuseStep 4091147 = 6136721) B6136721
theorem B912667 : Blo 358757 912667 := bstep (se 1 (by rfl) ⟨684500, by rfl⟩ : syracuseStep 912667 = 1369001) B1369001
theorem B3010499 : Blo 358757 3010499 := bstep (se 1 (by rfl) ⟨2257874, by rfl⟩ : syracuseStep 3010499 = 4515749) B4515749
theorem B1372403 : Blo 358757 1372403 := bstep (se 1 (by rfl) ⟨1029302, by rfl⟩ : syracuseStep 1372403 = 2058605) B2058605
theorem B1831247 : Blo 358757 1831247 := bstep (se 1 (by rfl) ⟨1373435, by rfl⟩ : syracuseStep 1831247 = 2746871) B2746871
theorem B24442033 : Blo 358757 24442033 := bstep (se 2 (by rfl) ⟨9165762, by rfl⟩ : syracuseStep 24442033 = 18331525) B18331525
theorem B980191 : Blo 358757 980191 := bstep (se 1 (by rfl) ⟨735143, by rfl⟩ : syracuseStep 980191 = 1470287) B1470287
theorem B5010785 : Blo 358757 5010785 := bstep (se 2 (by rfl) ⟨1879044, by rfl⟩ : syracuseStep 5010785 = 3758089) B3758089
theorem B1375001 : Blo 358757 1375001 := bstep (se 2 (by rfl) ⟨515625, by rfl⟩ : syracuseStep 1375001 = 1031251) B1031251
theorem B687379 : Blo 358757 687379 := bstep (se 1 (by rfl) ⟨515534, by rfl⟩ : syracuseStep 687379 = 1031069) B1031069
theorem B359727 : Blo 358757 359727 := bstep (se 1 (by rfl) ⟨269795, by rfl⟩ : syracuseStep 359727 = 539591) B539591
theorem B688351 : Blo 358757 688351 := bstep (se 1 (by rfl) ⟨516263, by rfl⟩ : syracuseStep 688351 = 1032527) B1032527
theorem B361199 : Blo 358757 361199 := bstep (se 1 (by rfl) ⟨270899, by rfl⟩ : syracuseStep 361199 = 541799) B541799
theorem B10388249 : Blo 358757 10388249 := bstep (se 2 (by rfl) ⟨3895593, by rfl⟩ : syracuseStep 10388249 = 7791187) B7791187
theorem B361563 : Blo 358757 361563 := bstep (se 1 (by rfl) ⟨271172, by rfl⟩ : syracuseStep 361563 = 542345) B542345
theorem B2065895 : Blo 358757 2065895 := bstep (se 1 (by rfl) ⟨1549421, by rfl⟩ : syracuseStep 2065895 = 3098843) B3098843
theorem B362087 : Blo 358757 362087 := bstep (se 1 (by rfl) ⟨271565, by rfl⟩ : syracuseStep 362087 = 543131) B543131
theorem B362559 : Blo 358757 362559 := bstep (se 1 (by rfl) ⟨271919, by rfl⟩ : syracuseStep 362559 = 543839) B543839
theorem B1542503 : Blo 358757 1542503 := bstep (se 1 (by rfl) ⟨1156877, by rfl⟩ : syracuseStep 1542503 = 2313755) B2313755
theorem B1215215 : Blo 358757 1215215 := bstep (se 1 (by rfl) ⟨911411, by rfl⟩ : syracuseStep 1215215 = 1822823) B1822823
theorem B5378399 : Blo 358757 5378399 := bstep (se 1 (by rfl) ⟨4033799, by rfl⟩ : syracuseStep 5378399 = 8067599) B8067599
theorem B1216889 : Blo 358757 1216889 := bstep (se 2 (by rfl) ⟨456333, by rfl⟩ : syracuseStep 1216889 = 912667) B912667
theorem B1151815 : Blo 358757 1151815 := bstep (se 1 (by rfl) ⟨863861, by rfl⟩ : syracuseStep 1151815 = 1727723) B1727723
theorem B431719 : Blo 358757 431719 := bstep (se 1 (by rfl) ⟨323789, by rfl⟩ : syracuseStep 431719 = 647579) B647579
theorem B46766807 : Blo 358757 46766807 := bstep (se 1 (by rfl) ⟨35075105, by rfl⟩ : syracuseStep 46766807 = 70150211) B70150211
theorem B2726945 : Blo 358757 2726945 := bstep (se 2 (by rfl) ⟨1022604, by rfl⟩ : syracuseStep 2726945 = 2045209) B2045209
theorem B2727431 : Blo 358757 2727431 := bstep (se 1 (by rfl) ⟨2045573, by rfl⟩ : syracuseStep 2727431 = 4091147) B4091147
theorem B26287649 : Blo 358757 26287649 := bstep (se 2 (by rfl) ⟨9857868, by rfl⟩ : syracuseStep 26287649 = 19715737) B19715737
theorem B2006999 : Blo 358757 2006999 := bstep (se 1 (by rfl) ⟨1505249, by rfl⟩ : syracuseStep 2006999 = 3010499) B3010499
theorem B1132666847 : Blo 358757 1132666847 := bstep (se 1 (by rfl) ⟨849500135, by rfl⟩ : syracuseStep 1132666847 = 1699000271) B1699000271
theorem B17571815 : Blo 358757 17571815 := bstep (se 1 (by rfl) ⟨13178861, by rfl⟩ : syracuseStep 17571815 = 26357723) B26357723
theorem B1220831 : Blo 358757 1220831 := bstep (se 1 (by rfl) ⟨915623, by rfl⟩ : syracuseStep 1220831 = 1831247) B1831247
theorem B11739451 : Blo 358757 11739451 := bstep (se 1 (by rfl) ⟨8804588, by rfl⟩ : syracuseStep 11739451 = 17609177) B17609177
theorem B2958601 : Blo 358757 2958601 := bstep (se 2 (by rfl) ⟨1109475, by rfl⟩ : syracuseStep 2958601 = 2218951) B2218951
theorem B1156889 : Blo 358757 1156889 := bstep (se 2 (by rfl) ⟨433833, by rfl⟩ : syracuseStep 1156889 = 867667) B867667
theorem B766331 : Blo 358757 766331 := bstep (se 1 (by rfl) ⟨574748, by rfl⟩ : syracuseStep 766331 = 1149497) B1149497
theorem B1454719 : Blo 358757 1454719 := bstep (se 1 (by rfl) ⟨1091039, by rfl⟩ : syracuseStep 1454719 = 2182079) B2182079
theorem B5944175 : Blo 358757 5944175 := bstep (se 1 (by rfl) ⟨4458131, by rfl⟩ : syracuseStep 5944175 = 8916263) B8916263
theorem B5649431 : Blo 358757 5649431 := bstep (se 1 (by rfl) ⟨4237073, by rfl⟩ : syracuseStep 5649431 = 8474147) B8474147
theorem B1030009 : Blo 358757 1030009 := bstep (se 2 (by rfl) ⟨386253, by rfl⟩ : syracuseStep 1030009 = 772507) B772507
theorem B539375 : Blo 358757 539375 := bstep (se 1 (by rfl) ⟨404531, by rfl⟩ : syracuseStep 539375 = 809063) B809063
theorem B540767 : Blo 358757 540767 := bstep (se 1 (by rfl) ⟨405575, by rfl⟩ : syracuseStep 540767 = 811151) B811151
theorem B17711419 : Blo 358757 17711419 := bstep (se 1 (by rfl) ⟨13283564, by rfl⟩ : syracuseStep 17711419 = 26567129) B26567129
theorem B541439 : Blo 358757 541439 := bstep (se 1 (by rfl) ⟨406079, by rfl⟩ : syracuseStep 541439 = 812159) B812159
theorem B1557319 : Blo 358757 1557319 := bstep (se 1 (by rfl) ⟨1167989, by rfl⟩ : syracuseStep 1557319 = 2335979) B2335979
theorem B2049583 : Blo 358757 2049583 := bstep (se 1 (by rfl) ⟨1537187, by rfl⟩ : syracuseStep 2049583 = 3074375) B3074375
theorem B32589377 : Blo 358757 32589377 := bstep (se 2 (by rfl) ⟨12221016, by rfl⟩ : syracuseStep 32589377 = 24442033) B24442033
theorem B607871 : Blo 358757 607871 := bstep (se 1 (by rfl) ⟨455903, by rfl⟩ : syracuseStep 607871 = 911807) B911807
theorem B542831 : Blo 358757 542831 := bstep (se 1 (by rfl) ⟨407123, by rfl⟩ : syracuseStep 542831 = 814247) B814247
theorem B3690137 : Blo 358757 3690137 := bstep (se 2 (by rfl) ⟨1383801, by rfl⟩ : syracuseStep 3690137 = 2767603) B2767603
theorem B1363625 : Blo 358757 1363625 := bstep (se 2 (by rfl) ⟨511359, by rfl⟩ : syracuseStep 1363625 = 1022719) B1022719
theorem B578747 : Blo 358757 578747 := bstep (se 1 (by rfl) ⟨434060, by rfl⟩ : syracuseStep 578747 = 868121) B868121
theorem B808361 : Blo 358757 808361 := bstep (se 2 (by rfl) ⟨303135, by rfl⟩ : syracuseStep 808361 = 606271) B606271
theorem B808415 : Blo 358757 808415 := bstep (se 1 (by rfl) ⟨606311, by rfl⟩ : syracuseStep 808415 = 1212623) B1212623
theorem B513535 : Blo 358757 513535 := bstep (se 1 (by rfl) ⟨385151, by rfl⟩ : syracuseStep 513535 = 770303) B770303
theorem B1365599 : Blo 358757 1365599 := bstep (se 1 (by rfl) ⟨1024199, by rfl⟩ : syracuseStep 1365599 = 2048399) B2048399
theorem B809135 : Blo 358757 809135 := bstep (se 1 (by rfl) ⟨606851, by rfl⟩ : syracuseStep 809135 = 1213703) B1213703
theorem B809639 : Blo 358757 809639 := bstep (se 1 (by rfl) ⟨607229, by rfl⟩ : syracuseStep 809639 = 1214459) B1214459
theorem B1366753 : Blo 358757 1366753 := bstep (se 2 (by rfl) ⟨512532, by rfl⟩ : syracuseStep 1366753 = 1025065) B1025065
theorem B1302655 : Blo 358757 1302655 := bstep (se 1 (by rfl) ⟨976991, by rfl⟩ : syracuseStep 1302655 = 1953983) B1953983
theorem B14836729 : Blo 358757 14836729 := bstep (se 2 (by rfl) ⟨5563773, by rfl⟩ : syracuseStep 14836729 = 11127547) B11127547
theorem B11658487 : Blo 358757 11658487 := bstep (se 1 (by rfl) ⟨8743865, by rfl⟩ : syracuseStep 11658487 = 17487731) B17487731
theorem B518891 : Blo 358757 518891 := bstep (se 1 (by rfl) ⟨389168, by rfl⟩ : syracuseStep 518891 = 778337) B778337
theorem B814409 : Blo 358757 814409 := bstep (se 2 (by rfl) ⟨305403, by rfl⟩ : syracuseStep 814409 = 610807) B610807
theorem B14872045 : Blo 358757 14872045 := bstep (se 3 (by rfl) ⟨2788508, by rfl⟩ : syracuseStep 14872045 = 5577017) B5577017
theorem B13233743 : Blo 358757 13233743 := bstep (se 1 (by rfl) ⟨9925307, by rfl⟩ : syracuseStep 13233743 = 19850615) B19850615
theorem B814823 : Blo 358757 814823 := bstep (se 1 (by rfl) ⟨611117, by rfl⟩ : syracuseStep 814823 = 1222235) B1222235
theorem B815039 : Blo 358757 815039 := bstep (se 1 (by rfl) ⟨611279, by rfl⟩ : syracuseStep 815039 = 1222559) B1222559
theorem B4911205 : Blo 358757 4911205 := bstep (se 4 (by rfl) ⟨460425, by rfl⟩ : syracuseStep 4911205 = 920851) B920851
theorem B1306921 : Blo 358757 1306921 := bstep (se 2 (by rfl) ⟨490095, by rfl⟩ : syracuseStep 1306921 = 980191) B980191
theorem B815849 : Blo 358757 815849 := bstep (se 2 (by rfl) ⟨305943, by rfl⟩ : syracuseStep 815849 = 611887) B611887
theorem B914935 : Blo 358757 914935 := bstep (se 1 (by rfl) ⟨686201, by rfl⟩ : syracuseStep 914935 = 1372403) B1372403
theorem B3340523 : Blo 358757 3340523 := bstep (se 1 (by rfl) ⟨2505392, by rfl⟩ : syracuseStep 3340523 = 5010785) B5010785
theorem B16021871 : Blo 358757 16021871 := bstep (se 1 (by rfl) ⟨12016403, by rfl⟩ : syracuseStep 16021871 = 24032807) B24032807
theorem B359195 : Blo 358757 359195 := bstep (se 1 (by rfl) ⟨269396, by rfl⟩ : syracuseStep 359195 = 538793) B538793
theorem B916505 : Blo 358757 916505 := bstep (se 2 (by rfl) ⟨343689, by rfl⟩ : syracuseStep 916505 = 687379) B687379
theorem B916667 : Blo 358757 916667 := bstep (se 1 (by rfl) ⟨687500, by rfl⟩ : syracuseStep 916667 = 1375001) B1375001
theorem B360431 : Blo 358757 360431 := bstep (se 1 (by rfl) ⟨270323, by rfl⟩ : syracuseStep 360431 = 540647) B540647
theorem B360511 : Blo 358757 360511 := bstep (se 1 (by rfl) ⟨270383, by rfl⟩ : syracuseStep 360511 = 540767) B540767
theorem B1736873 : Blo 358757 1736873 := bstep (se 2 (by rfl) ⟨651327, by rfl⟩ : syracuseStep 1736873 = 1302655) B1302655
theorem B917801 : Blo 358757 917801 := bstep (se 2 (by rfl) ⟨344175, by rfl⟩ : syracuseStep 917801 = 688351) B688351
theorem B360959 : Blo 358757 360959 := bstep (se 1 (by rfl) ⟨270719, by rfl⟩ : syracuseStep 360959 = 541439) B541439
theorem B1377263 : Blo 358757 1377263 := bstep (se 1 (by rfl) ⟨1032947, by rfl⟩ : syracuseStep 1377263 = 2065895) B2065895
theorem B21726251 : Blo 358757 21726251 := bstep (se 1 (by rfl) ⟨16294688, by rfl⟩ : syracuseStep 21726251 = 32589377) B32589377
theorem B361887 : Blo 358757 361887 := bstep (se 1 (by rfl) ⟨271415, by rfl⟩ : syracuseStep 361887 = 542831) B542831
theorem B2460091 : Blo 358757 2460091 := bstep (se 1 (by rfl) ⟨1845068, by rfl⟩ : syracuseStep 2460091 = 3690137) B3690137
theorem B19829393 : Blo 358757 19829393 := bstep (se 2 (by rfl) ⟨7436022, by rfl⟩ : syracuseStep 19829393 = 14872045) B14872045
theorem B3085037 : Blo 358757 3085037 := bstep (se 3 (by rfl) ⟨578444, by rfl⟩ : syracuseStep 3085037 = 1156889) B1156889
theorem B755111231 : Blo 358757 755111231 := bstep (se 1 (by rfl) ⟨566333423, by rfl⟩ : syracuseStep 755111231 = 1132666847) B1132666847
theorem B1742561 : Blo 358757 1742561 := bstep (se 2 (by rfl) ⟨653460, by rfl⟩ : syracuseStep 1742561 = 1306921) B1306921
theorem B1939625 : Blo 358757 1939625 := bstep (se 2 (by rfl) ⟨727359, by rfl⟩ : syracuseStep 1939625 = 1454719) B1454719
theorem B1219913 : Blo 358757 1219913 := bstep (se 2 (by rfl) ⟨457467, by rfl⟩ : syracuseStep 1219913 = 914935) B914935
theorem B8822495 : Blo 358757 8822495 := bstep (se 1 (by rfl) ⟨6616871, by rfl⟩ : syracuseStep 8822495 = 13233743) B13233743
theorem B2302501 : Blo 358757 2302501 := bstep (se 4 (by rfl) ⟨215859, by rfl⟩ : syracuseStep 2302501 = 431719) B431719
theorem B6925499 : Blo 358757 6925499 := bstep (se 1 (by rfl) ⟨5194124, by rfl⟩ : syracuseStep 6925499 = 10388249) B10388249
theorem B405247 : Blo 358757 405247 := bstep (se 1 (by rfl) ⟨303935, by rfl⟩ : syracuseStep 405247 = 607871) B607871
theorem B2076425 : Blo 358757 2076425 := bstep (se 2 (by rfl) ⟨778659, by rfl⟩ : syracuseStep 2076425 = 1557319) B1557319
theorem B1028335 : Blo 358757 1028335 := bstep (se 1 (by rfl) ⟨771251, by rfl⟩ : syracuseStep 1028335 = 1542503) B1542503
theorem B15544649 : Blo 358757 15544649 := bstep (se 2 (by rfl) ⟨5829243, by rfl⟩ : syracuseStep 15544649 = 11658487) B11658487
theorem B3944801 : Blo 358757 3944801 := bstep (se 2 (by rfl) ⟨1479300, by rfl⟩ : syracuseStep 3944801 = 2958601) B2958601
theorem B2732777 : Blo 358757 2732777 := bstep (se 2 (by rfl) ⟨1024791, by rfl⟩ : syracuseStep 2732777 = 2049583) B2049583
theorem B3585599 : Blo 358757 3585599 := bstep (se 1 (by rfl) ⟨2689199, by rfl⟩ : syracuseStep 3585599 = 5378399) B5378399
theorem B538907 : Blo 358757 538907 := bstep (se 1 (by rfl) ⟨404180, by rfl⟩ : syracuseStep 538907 = 808361) B808361
theorem B538943 : Blo 358757 538943 := bstep (se 1 (by rfl) ⟨404207, by rfl⟩ : syracuseStep 538943 = 808415) B808415
theorem B539423 : Blo 358757 539423 := bstep (se 1 (by rfl) ⟨404567, by rfl⟩ : syracuseStep 539423 = 809135) B809135
theorem B539759 : Blo 358757 539759 := bstep (se 1 (by rfl) ⟨404819, by rfl⟩ : syracuseStep 539759 = 809639) B809639
theorem B31177871 : Blo 358757 31177871 := bstep (se 1 (by rfl) ⟨23383403, by rfl⟩ : syracuseStep 31177871 = 46766807) B46766807
theorem B1817963 : Blo 358757 1817963 := bstep (se 1 (by rfl) ⟨1363472, by rfl⟩ : syracuseStep 1817963 = 2726945) B2726945
theorem B1818287 : Blo 358757 1818287 := bstep (se 1 (by rfl) ⟨1363715, by rfl⟩ : syracuseStep 1818287 = 2727431) B2727431
theorem B11714543 : Blo 358757 11714543 := bstep (se 1 (by rfl) ⟨8785907, by rfl⟩ : syracuseStep 11714543 = 17571815) B17571815
theorem B542939 : Blo 358757 542939 := bstep (se 1 (by rfl) ⟨407204, by rfl⟩ : syracuseStep 542939 = 814409) B814409
theorem B543215 : Blo 358757 543215 := bstep (se 1 (by rfl) ⟨407411, by rfl⟩ : syracuseStep 543215 = 814823) B814823
theorem B543359 : Blo 358757 543359 := bstep (se 1 (by rfl) ⟨407519, by rfl⟩ : syracuseStep 543359 = 815039) B815039
theorem B510887 : Blo 358757 510887 := bstep (se 1 (by rfl) ⟨383165, by rfl⟩ : syracuseStep 510887 = 766331) B766331
theorem B543899 : Blo 358757 543899 := bstep (se 1 (by rfl) ⟨407924, by rfl⟩ : syracuseStep 543899 = 815849) B815849
theorem B1822337 : Blo 358757 1822337 := bstep (se 2 (by rfl) ⟨683376, by rfl⟩ : syracuseStep 1822337 = 1366753) B1366753
theorem B611003 : Blo 358757 611003 := bstep (se 1 (by rfl) ⟨458252, by rfl⟩ : syracuseStep 611003 = 916505) B916505
theorem B611111 : Blo 358757 611111 := bstep (se 1 (by rfl) ⟨458333, by rfl⟩ : syracuseStep 611111 = 916667) B916667
theorem B23615225 : Blo 358757 23615225 := bstep (se 2 (by rfl) ⟨8855709, by rfl⟩ : syracuseStep 23615225 = 17711419) B17711419
theorem B15652601 : Blo 358757 15652601 := bstep (se 2 (by rfl) ⟨5869725, by rfl⟩ : syracuseStep 15652601 = 11739451) B11739451
theorem B19782305 : Blo 358757 19782305 := bstep (se 2 (by rfl) ⟨7418364, by rfl⟩ : syracuseStep 19782305 = 14836729) B14836729
theorem B810143 : Blo 358757 810143 := bstep (se 1 (by rfl) ⟨607607, by rfl⟩ : syracuseStep 810143 = 1215215) B1215215
theorem B909083 : Blo 358757 909083 := bstep (se 1 (by rfl) ⟨681812, by rfl⟩ : syracuseStep 909083 = 1363625) B1363625
theorem B15065149 : Blo 358757 15065149 := bstep (se 3 (by rfl) ⟨2824715, by rfl⟩ : syracuseStep 15065149 = 5649431) B5649431
theorem B811259 : Blo 358757 811259 := bstep (se 1 (by rfl) ⟨608444, by rfl⟩ : syracuseStep 811259 = 1216889) B1216889
theorem B385831 : Blo 358757 385831 := bstep (se 1 (by rfl) ⟨289373, by rfl⟩ : syracuseStep 385831 = 578747) B578747
theorem B910399 : Blo 358757 910399 := bstep (se 1 (by rfl) ⟨682799, by rfl⟩ : syracuseStep 910399 = 1365599) B1365599
theorem B17525099 : Blo 358757 17525099 := bstep (se 1 (by rfl) ⟨13143824, by rfl⟩ : syracuseStep 17525099 = 26287649) B26287649
theorem B1337999 : Blo 358757 1337999 := bstep (se 1 (by rfl) ⟨1003499, by rfl⟩ : syracuseStep 1337999 = 2006999) B2006999
theorem B6548273 : Blo 358757 6548273 := bstep (se 2 (by rfl) ⟨2455602, by rfl⟩ : syracuseStep 6548273 = 4911205) B4911205
theorem B813887 : Blo 358757 813887 := bstep (se 1 (by rfl) ⟨610415, by rfl⟩ : syracuseStep 813887 = 1220831) B1220831
theorem B8908061 : Blo 358757 8908061 := bstep (se 3 (by rfl) ⟨1670261, by rfl⟩ : syracuseStep 8908061 = 3340523) B3340523
theorem B1535753 : Blo 358757 1535753 := bstep (se 2 (by rfl) ⟨575907, by rfl⟩ : syracuseStep 1535753 = 1151815) B1151815
theorem B684713 : Blo 358757 684713 := bstep (se 2 (by rfl) ⟨256767, by rfl⟩ : syracuseStep 684713 = 513535) B513535
theorem B5534837 : Blo 358757 5534837 := bstep (se 5 (by rfl) ⟨259445, by rfl⟩ : syracuseStep 5534837 = 518891) B518891
theorem B1373345 : Blo 358757 1373345 := bstep (se 2 (by rfl) ⟨515004, by rfl⟩ : syracuseStep 1373345 = 1030009) B1030009
theorem B3962783 : Blo 358757 3962783 := bstep (se 1 (by rfl) ⟨2972087, by rfl⟩ : syracuseStep 3962783 = 5944175) B5944175
theorem B10681247 : Blo 358757 10681247 := bstep (se 1 (by rfl) ⟨8010935, by rfl⟩ : syracuseStep 10681247 = 16021871) B16021871
theorem B359583 : Blo 358757 359583 := bstep (se 1 (by rfl) ⟨269687, by rfl⟩ : syracuseStep 359583 = 539375) B539375
theorem B20086865 : Blo 358757 20086865 := bstep (se 2 (by rfl) ⟨7532574, by rfl⟩ : syracuseStep 20086865 = 15065149) B15065149
theorem B918175 : Blo 358757 918175 := bstep (se 1 (by rfl) ⟨688631, by rfl⟩ : syracuseStep 918175 = 1377263) B1377263
theorem B14484167 : Blo 358757 14484167 := bstep (se 1 (by rfl) ⟨10863125, by rfl⟩ : syracuseStep 14484167 = 21726251) B21726251
theorem B10519469 : Blo 358757 10519469 := bstep (se 3 (by rfl) ⟨1972400, by rfl⟩ : syracuseStep 10519469 = 3944801) B3944801
theorem B1213865 : Blo 358757 1213865 := bstep (se 2 (by rfl) ⟨455199, by rfl⟩ : syracuseStep 1213865 = 910399) B910399
theorem B361959 : Blo 358757 361959 := bstep (se 1 (by rfl) ⟨271469, by rfl⟩ : syracuseStep 361959 = 542939) B542939
theorem B362143 : Blo 358757 362143 := bstep (se 1 (by rfl) ⟨271607, by rfl⟩ : syracuseStep 362143 = 543215) B543215
theorem B362239 : Blo 358757 362239 := bstep (se 1 (by rfl) ⟨271679, by rfl⟩ : syracuseStep 362239 = 543359) B543359
theorem B362599 : Blo 358757 362599 := bstep (se 1 (by rfl) ⟨271949, by rfl⟩ : syracuseStep 362599 = 543899) B543899
theorem B1214891 : Blo 358757 1214891 := bstep (se 1 (by rfl) ⟨911168, by rfl⟩ : syracuseStep 1214891 = 1822337) B1822337
theorem B3280121 : Blo 358757 3280121 := bstep (se 2 (by rfl) ⟨1230045, by rfl⟩ : syracuseStep 3280121 = 2460091) B2460091
theorem B4365515 : Blo 358757 4365515 := bstep (se 1 (by rfl) ⟨3274136, by rfl⟩ : syracuseStep 4365515 = 6548273) B6548273
theorem B1023835 : Blo 358757 1023835 := bstep (se 1 (by rfl) ⟨767876, by rfl⟩ : syracuseStep 1023835 = 1535753) B1535753
theorem B1384283 : Blo 358757 1384283 := bstep (se 1 (by rfl) ⟨1038212, by rfl⟩ : syracuseStep 1384283 = 2076425) B2076425
theorem B10363099 : Blo 358757 10363099 := bstep (se 1 (by rfl) ⟨7772324, by rfl⟩ : syracuseStep 10363099 = 15544649) B15544649
theorem B7120831 : Blo 358757 7120831 := bstep (se 1 (by rfl) ⟨5340623, by rfl⟩ : syracuseStep 7120831 = 10681247) B10681247
theorem B20785247 : Blo 358757 20785247 := bstep (se 1 (by rfl) ⟨15588935, by rfl⟩ : syracuseStep 20785247 = 31177871) B31177871
theorem B7809695 : Blo 358757 7809695 := bstep (se 1 (by rfl) ⟨5857271, by rfl⟩ : syracuseStep 7809695 = 11714543) B11714543
theorem B1157915 : Blo 358757 1157915 := bstep (se 1 (by rfl) ⟨868436, by rfl⟩ : syracuseStep 1157915 = 1736873) B1736873
theorem B13219595 : Blo 358757 13219595 := bstep (se 1 (by rfl) ⟨9914696, by rfl⟩ : syracuseStep 13219595 = 19829393) B19829393
theorem B407335 : Blo 358757 407335 := bstep (se 1 (by rfl) ⟨305501, by rfl⟩ : syracuseStep 407335 = 611003) B611003
theorem B407407 : Blo 358757 407407 := bstep (se 1 (by rfl) ⟨305555, by rfl⟩ : syracuseStep 407407 = 611111) B611111
theorem B1161707 : Blo 358757 1161707 := bstep (se 1 (by rfl) ⟨871280, by rfl⟩ : syracuseStep 1161707 = 1742561) B1742561
theorem B15743483 : Blo 358757 15743483 := bstep (se 1 (by rfl) ⟨11807612, by rfl⟩ : syracuseStep 15743483 = 23615225) B23615225
theorem B10435067 : Blo 358757 10435067 := bstep (se 1 (by rfl) ⟨7826300, by rfl⟩ : syracuseStep 10435067 = 15652601) B15652601
theorem B1293083 : Blo 358757 1293083 := bstep (se 1 (by rfl) ⟨969812, by rfl⟩ : syracuseStep 1293083 = 1939625) B1939625
theorem B13188203 : Blo 358757 13188203 := bstep (se 1 (by rfl) ⟨9891152, by rfl⟩ : syracuseStep 13188203 = 19782305) B19782305
theorem B540095 : Blo 358757 540095 := bstep (se 1 (by rfl) ⟨405071, by rfl⟩ : syracuseStep 540095 = 810143) B810143
theorem B540329 : Blo 358757 540329 := bstep (se 2 (by rfl) ⟨202623, by rfl⟩ : syracuseStep 540329 = 405247) B405247
theorem B5881663 : Blo 358757 5881663 := bstep (se 1 (by rfl) ⟨4411247, by rfl⟩ : syracuseStep 5881663 = 8822495) B8822495
theorem B606055 : Blo 358757 606055 := bstep (se 1 (by rfl) ⟨454541, by rfl⟩ : syracuseStep 606055 = 909083) B909083
theorem B540839 : Blo 358757 540839 := bstep (se 1 (by rfl) ⟨405629, by rfl⟩ : syracuseStep 540839 = 811259) B811259
theorem B11683399 : Blo 358757 11683399 := bstep (se 1 (by rfl) ⟨8762549, by rfl⟩ : syracuseStep 11683399 = 17525099) B17525099
theorem B542591 : Blo 358757 542591 := bstep (se 1 (by rfl) ⟨406943, by rfl⟩ : syracuseStep 542591 = 813887) B813887
theorem B1362365 : Blo 358757 1362365 := bstep (se 3 (by rfl) ⟨255443, by rfl⟩ : syracuseStep 1362365 = 510887) B510887
theorem B1821851 : Blo 358757 1821851 := bstep (se 1 (by rfl) ⟨1366388, by rfl⟩ : syracuseStep 1821851 = 2732777) B2732777
theorem B3689891 : Blo 358757 3689891 := bstep (se 1 (by rfl) ⟨2767418, by rfl⟩ : syracuseStep 3689891 = 5534837) B5534837
theorem B2641855 : Blo 358757 2641855 := bstep (se 1 (by rfl) ⟨1981391, by rfl⟩ : syracuseStep 2641855 = 3962783) B3962783
theorem B611867 : Blo 358757 611867 := bstep (se 1 (by rfl) ⟨458900, by rfl⟩ : syracuseStep 611867 = 917801) B917801
theorem B3070001 : Blo 358757 3070001 := bstep (se 2 (by rfl) ⟨1151250, by rfl⟩ : syracuseStep 3070001 = 2302501) B2302501
theorem B514441 : Blo 358757 514441 := bstep (se 2 (by rfl) ⟨192915, by rfl⟩ : syracuseStep 514441 = 385831) B385831
theorem B1825901 : Blo 358757 1825901 := bstep (se 3 (by rfl) ⟨342356, by rfl⟩ : syracuseStep 1825901 = 684713) B684713
theorem B2056691 : Blo 358757 2056691 := bstep (se 1 (by rfl) ⟨1542518, by rfl⟩ : syracuseStep 2056691 = 3085037) B3085037
theorem B503407487 : Blo 358757 503407487 := bstep (se 1 (by rfl) ⟨377555615, by rfl⟩ : syracuseStep 503407487 = 755111231) B755111231
theorem B813275 : Blo 358757 813275 := bstep (se 1 (by rfl) ⟨609956, by rfl⟩ : syracuseStep 813275 = 1219913) B1219913
theorem B1371113 : Blo 358757 1371113 := bstep (se 2 (by rfl) ⟨514167, by rfl⟩ : syracuseStep 1371113 = 1028335) B1028335
theorem B3567997 : Blo 358757 3567997 := bstep (se 3 (by rfl) ⟨668999, by rfl⟩ : syracuseStep 3567997 = 1337999) B1337999
theorem B4616999 : Blo 358757 4616999 := bstep (se 1 (by rfl) ⟨3462749, by rfl⟩ : syracuseStep 4616999 = 6925499) B6925499
theorem B23754829 : Blo 358757 23754829 := bstep (se 3 (by rfl) ⟨4454030, by rfl⟩ : syracuseStep 23754829 = 8908061) B8908061
theorem B915563 : Blo 358757 915563 := bstep (se 1 (by rfl) ⟨686672, by rfl⟩ : syracuseStep 915563 = 1373345) B1373345
theorem B2390399 : Blo 358757 2390399 := bstep (se 1 (by rfl) ⟨1792799, by rfl⟩ : syracuseStep 2390399 = 3585599) B3585599
theorem B359271 : Blo 358757 359271 := bstep (se 1 (by rfl) ⟨269453, by rfl⟩ : syracuseStep 359271 = 538907) B538907
theorem B359295 : Blo 358757 359295 := bstep (se 1 (by rfl) ⟨269471, by rfl⟩ : syracuseStep 359295 = 538943) B538943
theorem B359615 : Blo 358757 359615 := bstep (se 1 (by rfl) ⟨269711, by rfl⟩ : syracuseStep 359615 = 539423) B539423
theorem B359839 : Blo 358757 359839 := bstep (se 1 (by rfl) ⟨269879, by rfl⟩ : syracuseStep 359839 = 539759) B539759
theorem B1211975 : Blo 358757 1211975 := bstep (se 1 (by rfl) ⟨908981, by rfl⟩ : syracuseStep 1211975 = 1817963) B1817963
theorem B1212191 : Blo 358757 1212191 := bstep (se 1 (by rfl) ⟨909143, by rfl⟩ : syracuseStep 1212191 = 1818287) B1818287
theorem B360559 : Blo 358757 360559 := bstep (se 1 (by rfl) ⟨270419, by rfl⟩ : syracuseStep 360559 = 540839) B540839
theorem B7012979 : Blo 358757 7012979 := bstep (se 1 (by rfl) ⟨5259734, by rfl⟩ : syracuseStep 7012979 = 10519469) B10519469
theorem B361727 : Blo 358757 361727 := bstep (se 1 (by rfl) ⟨271295, by rfl⟩ : syracuseStep 361727 = 542591) B542591
theorem B1214567 : Blo 358757 1214567 := bstep (se 1 (by rfl) ⟨910925, by rfl⟩ : syracuseStep 1214567 = 1821851) B1821851
theorem B2459927 : Blo 358757 2459927 := bstep (se 1 (by rfl) ⟨1844945, by rfl⟩ : syracuseStep 2459927 = 3689891) B3689891
theorem B1217267 : Blo 358757 1217267 := bstep (se 1 (by rfl) ⟨912950, by rfl⟩ : syracuseStep 1217267 = 1825901) B1825901
theorem B922855 : Blo 358757 922855 := bstep (se 1 (by rfl) ⟨692141, by rfl⟩ : syracuseStep 922855 = 1384283) B1384283
theorem B4757329 : Blo 358757 4757329 := bstep (se 2 (by rfl) ⟨1783998, by rfl⟩ : syracuseStep 4757329 = 3567997) B3567997
theorem B10495655 : Blo 358757 10495655 := bstep (se 1 (by rfl) ⟨7871741, by rfl⟩ : syracuseStep 10495655 = 15743483) B15743483
theorem B6956711 : Blo 358757 6956711 := bstep (se 1 (by rfl) ⟨5217533, by rfl⟩ : syracuseStep 6956711 = 10435067) B10435067
theorem B862055 : Blo 358757 862055 := bstep (se 1 (by rfl) ⟨646541, by rfl⟩ : syracuseStep 862055 = 1293083) B1293083
theorem B8792135 : Blo 358757 8792135 := bstep (se 1 (by rfl) ⟨6594101, by rfl⟩ : syracuseStep 8792135 = 13188203) B13188203
theorem B7842217 : Blo 358757 7842217 := bstep (se 2 (by rfl) ⟨2940831, by rfl⟩ : syracuseStep 7842217 = 5881663) B5881663
theorem B1224233 : Blo 358757 1224233 := bstep (se 2 (by rfl) ⟨459087, by rfl⟩ : syracuseStep 1224233 = 918175) B918175
theorem B15577865 : Blo 358757 15577865 := bstep (se 2 (by rfl) ⟨5841699, by rfl⟩ : syracuseStep 15577865 = 11683399) B11683399
theorem B407911 : Blo 358757 407911 := bstep (se 1 (by rfl) ⟨305933, by rfl⟩ : syracuseStep 407911 = 611867) B611867
theorem B2046667 : Blo 358757 2046667 := bstep (se 1 (by rfl) ⟨1535000, by rfl⟩ : syracuseStep 2046667 = 3070001) B3070001
theorem B3522473 : Blo 358757 3522473 := bstep (se 2 (by rfl) ⟨1320927, by rfl⟩ : syracuseStep 3522473 = 2641855) B2641855
theorem B3097885 : Blo 358757 3097885 := bstep (se 3 (by rfl) ⟨580853, by rfl⟩ : syracuseStep 3097885 = 1161707) B1161707
theorem B542183 : Blo 358757 542183 := bstep (se 1 (by rfl) ⟨406637, by rfl⟩ : syracuseStep 542183 = 813275) B813275
theorem B771943 : Blo 358757 771943 := bstep (se 1 (by rfl) ⟨578957, by rfl⟩ : syracuseStep 771943 = 1157915) B1157915
theorem B543113 : Blo 358757 543113 := bstep (se 2 (by rfl) ⟨203667, by rfl⟩ : syracuseStep 543113 = 407335) B407335
theorem B543209 : Blo 358757 543209 := bstep (se 2 (by rfl) ⟨203703, by rfl⟩ : syracuseStep 543209 = 407407) B407407
theorem B31673105 : Blo 358757 31673105 := bstep (se 2 (by rfl) ⟨11877414, by rfl⟩ : syracuseStep 31673105 = 23754829) B23754829
theorem B610375 : Blo 358757 610375 := bstep (se 1 (by rfl) ⟨457781, by rfl⟩ : syracuseStep 610375 = 915563) B915563
theorem B1593599 : Blo 358757 1593599 := bstep (se 1 (by rfl) ⟨1195199, by rfl⟩ : syracuseStep 1593599 = 2390399) B2390399
theorem B807983 : Blo 358757 807983 := bstep (se 1 (by rfl) ⟨605987, by rfl⟩ : syracuseStep 807983 = 1211975) B1211975
theorem B1365113 : Blo 358757 1365113 := bstep (se 2 (by rfl) ⟨511917, by rfl⟩ : syracuseStep 1365113 = 1023835) B1023835
theorem B808073 : Blo 358757 808073 := bstep (se 2 (by rfl) ⟨303027, by rfl⟩ : syracuseStep 808073 = 606055) B606055
theorem B808127 : Blo 358757 808127 := bstep (se 1 (by rfl) ⟨606095, by rfl⟩ : syracuseStep 808127 = 1212191) B1212191
theorem B13391243 : Blo 358757 13391243 := bstep (se 1 (by rfl) ⟨10043432, by rfl⟩ : syracuseStep 13391243 = 20086865) B20086865
theorem B13817465 : Blo 358757 13817465 := bstep (se 2 (by rfl) ⟨5181549, by rfl⟩ : syracuseStep 13817465 = 10363099) B10363099
theorem B9656111 : Blo 358757 9656111 := bstep (se 1 (by rfl) ⟨7242083, by rfl⟩ : syracuseStep 9656111 = 14484167) B14484167
theorem B809243 : Blo 358757 809243 := bstep (se 1 (by rfl) ⟨606932, by rfl⟩ : syracuseStep 809243 = 1213865) B1213865
theorem B809927 : Blo 358757 809927 := bstep (se 1 (by rfl) ⟨607445, by rfl⟩ : syracuseStep 809927 = 1214891) B1214891
theorem B908243 : Blo 358757 908243 := bstep (se 1 (by rfl) ⟨681182, by rfl⟩ : syracuseStep 908243 = 1362365) B1362365
theorem B2186747 : Blo 358757 2186747 := bstep (se 1 (by rfl) ⟨1640060, by rfl⟩ : syracuseStep 2186747 = 3280121) B3280121
theorem B9494441 : Blo 358757 9494441 := bstep (se 2 (by rfl) ⟨3560415, by rfl⟩ : syracuseStep 9494441 = 7120831) B7120831
theorem B2910343 : Blo 358757 2910343 := bstep (se 1 (by rfl) ⟨2182757, by rfl⟩ : syracuseStep 2910343 = 4365515) B4365515
theorem B1371127 : Blo 358757 1371127 := bstep (se 1 (by rfl) ⟨1028345, by rfl⟩ : syracuseStep 1371127 = 2056691) B2056691
theorem B335604991 : Blo 358757 335604991 := bstep (se 1 (by rfl) ⟨251703743, by rfl⟩ : syracuseStep 335604991 = 503407487) B503407487
theorem B13856831 : Blo 358757 13856831 := bstep (se 1 (by rfl) ⟨10392623, by rfl⟩ : syracuseStep 13856831 = 20785247) B20785247
theorem B5206463 : Blo 358757 5206463 := bstep (se 1 (by rfl) ⟨3904847, by rfl⟩ : syracuseStep 5206463 = 7809695) B7809695
theorem B914075 : Blo 358757 914075 := bstep (se 1 (by rfl) ⟨685556, by rfl⟩ : syracuseStep 914075 = 1371113) B1371113
theorem B685921 : Blo 358757 685921 := bstep (se 2 (by rfl) ⟨257220, by rfl⟩ : syracuseStep 685921 = 514441) B514441
theorem B3077999 : Blo 358757 3077999 := bstep (se 1 (by rfl) ⟨2308499, by rfl⟩ : syracuseStep 3077999 = 4616999) B4616999
theorem B8813063 : Blo 358757 8813063 := bstep (se 1 (by rfl) ⟨6609797, by rfl⟩ : syracuseStep 8813063 = 13219595) B13219595
theorem B360063 : Blo 358757 360063 := bstep (se 1 (by rfl) ⟨270047, by rfl⟩ : syracuseStep 360063 = 540095) B540095
theorem B360219 : Blo 358757 360219 := bstep (se 1 (by rfl) ⟨270164, by rfl⟩ : syracuseStep 360219 = 540329) B540329
theorem B361455 : Blo 358757 361455 := bstep (se 1 (by rfl) ⟨271091, by rfl⟩ : syracuseStep 361455 = 542183) B542183
theorem B362075 : Blo 358757 362075 := bstep (se 1 (by rfl) ⟨271556, by rfl⟩ : syracuseStep 362075 = 543113) B543113
theorem B362139 : Blo 358757 362139 := bstep (se 1 (by rfl) ⟨271604, by rfl⟩ : syracuseStep 362139 = 543209) B543209
theorem B4130513 : Blo 358757 4130513 := bstep (se 2 (by rfl) ⟨1548942, by rfl⟩ : syracuseStep 4130513 = 3097885) B3097885
theorem B10456289 : Blo 358757 10456289 := bstep (se 2 (by rfl) ⟨3921108, by rfl⟩ : syracuseStep 10456289 = 7842217) B7842217
theorem B9211643 : Blo 358757 9211643 := bstep (se 1 (by rfl) ⟨6908732, by rfl⟩ : syracuseStep 9211643 = 13817465) B13817465
theorem B6329627 : Blo 358757 6329627 := bstep (se 1 (by rfl) ⟨4747220, by rfl⟩ : syracuseStep 6329627 = 9494441) B9494441
theorem B6559805 : Blo 358757 6559805 := bstep (se 3 (by rfl) ⟨1229963, by rfl⟩ : syracuseStep 6559805 = 2459927) B2459927
theorem B23501501 : Blo 358757 23501501 := bstep (se 3 (by rfl) ⟨4406531, by rfl⟩ : syracuseStep 23501501 = 8813063) B8813063
theorem B2728889 : Blo 358757 2728889 := bstep (se 2 (by rfl) ⟨1023333, by rfl⟩ : syracuseStep 2728889 = 2046667) B2046667
theorem B21115403 : Blo 358757 21115403 := bstep (se 1 (by rfl) ⟨15836552, by rfl⟩ : syracuseStep 21115403 = 31673105) B31673105
theorem B1029257 : Blo 358757 1029257 := bstep (se 2 (by rfl) ⟨385971, by rfl⟩ : syracuseStep 1029257 = 771943) B771943
theorem B3880457 : Blo 358757 3880457 := bstep (se 2 (by rfl) ⟨1455171, by rfl⟩ : syracuseStep 3880457 = 2910343) B2910343
theorem B538655 : Blo 358757 538655 := bstep (se 1 (by rfl) ⟨403991, by rfl⟩ : syracuseStep 538655 = 807983) B807983
theorem B538715 : Blo 358757 538715 := bstep (se 1 (by rfl) ⟨404036, by rfl⟩ : syracuseStep 538715 = 808073) B808073
theorem B538751 : Blo 358757 538751 := bstep (se 1 (by rfl) ⟨404063, by rfl⟩ : syracuseStep 538751 = 808127) B808127
theorem B8927495 : Blo 358757 8927495 := bstep (se 1 (by rfl) ⟨6695621, by rfl⟩ : syracuseStep 8927495 = 13391243) B13391243
theorem B6437407 : Blo 358757 6437407 := bstep (se 1 (by rfl) ⟨4828055, by rfl⟩ : syracuseStep 6437407 = 9656111) B9656111
theorem B539495 : Blo 358757 539495 := bstep (se 1 (by rfl) ⟨404621, by rfl⟩ : syracuseStep 539495 = 809243) B809243
theorem B539951 : Blo 358757 539951 := bstep (se 1 (by rfl) ⟨404963, by rfl⟩ : syracuseStep 539951 = 809927) B809927
theorem B605495 : Blo 358757 605495 := bstep (se 1 (by rfl) ⟨454121, by rfl⟩ : syracuseStep 605495 = 908243) B908243
theorem B1457831 : Blo 358757 1457831 := bstep (se 1 (by rfl) ⟨1093373, by rfl⟩ : syracuseStep 1457831 = 2186747) B2186747
theorem B6997103 : Blo 358757 6997103 := bstep (se 1 (by rfl) ⟨5247827, by rfl⟩ : syracuseStep 6997103 = 10495655) B10495655
theorem B4637807 : Blo 358757 4637807 := bstep (se 1 (by rfl) ⟨3478355, by rfl⟩ : syracuseStep 4637807 = 6956711) B6956711
theorem B574703 : Blo 358757 574703 := bstep (se 1 (by rfl) ⟨431027, by rfl⟩ : syracuseStep 574703 = 862055) B862055
theorem B1230473 : Blo 358757 1230473 := bstep (se 2 (by rfl) ⟨461427, by rfl⟩ : syracuseStep 1230473 = 922855) B922855
theorem B6343105 : Blo 358757 6343105 := bstep (se 2 (by rfl) ⟨2378664, by rfl⟩ : syracuseStep 6343105 = 4757329) B4757329
theorem B609383 : Blo 358757 609383 := bstep (se 1 (by rfl) ⟨457037, by rfl⟩ : syracuseStep 609383 = 914075) B914075
theorem B543881 : Blo 358757 543881 := bstep (se 2 (by rfl) ⟨203955, by rfl⟩ : syracuseStep 543881 = 407911) B407911
theorem B2051999 : Blo 358757 2051999 := bstep (se 1 (by rfl) ⟨1538999, by rfl⟩ : syracuseStep 2051999 = 3077999) B3077999
theorem B2348315 : Blo 358757 2348315 := bstep (se 1 (by rfl) ⟨1761236, by rfl⟩ : syracuseStep 2348315 = 3522473) B3522473
theorem B4675319 : Blo 358757 4675319 := bstep (se 1 (by rfl) ⟨3506489, by rfl⟩ : syracuseStep 4675319 = 7012979) B7012979
theorem B4249597 : Blo 358757 4249597 := bstep (se 3 (by rfl) ⟨796799, by rfl⟩ : syracuseStep 4249597 = 1593599) B1593599
theorem B809711 : Blo 358757 809711 := bstep (se 1 (by rfl) ⟨607283, by rfl⟩ : syracuseStep 809711 = 1214567) B1214567
theorem B811511 : Blo 358757 811511 := bstep (se 1 (by rfl) ⟨608633, by rfl⟩ : syracuseStep 811511 = 1217267) B1217267
theorem B910075 : Blo 358757 910075 := bstep (se 1 (by rfl) ⟨682556, by rfl⟩ : syracuseStep 910075 = 1365113) B1365113
theorem B1828169 : Blo 358757 1828169 := bstep (se 2 (by rfl) ⟨685563, by rfl⟩ : syracuseStep 1828169 = 1371127) B1371127
theorem B447473321 : Blo 358757 447473321 := bstep (se 2 (by rfl) ⟨167802495, by rfl⟩ : syracuseStep 447473321 = 335604991) B335604991
theorem B813833 : Blo 358757 813833 := bstep (se 2 (by rfl) ⟨305187, by rfl⟩ : syracuseStep 813833 = 610375) B610375
theorem B5861423 : Blo 358757 5861423 := bstep (se 1 (by rfl) ⟨4396067, by rfl⟩ : syracuseStep 5861423 = 8792135) B8792135
theorem B816155 : Blo 358757 816155 := bstep (se 1 (by rfl) ⟨612116, by rfl⟩ : syracuseStep 816155 = 1224233) B1224233
theorem B914561 : Blo 358757 914561 := bstep (se 2 (by rfl) ⟨342960, by rfl⟩ : syracuseStep 914561 = 685921) B685921
theorem B9237887 : Blo 358757 9237887 := bstep (se 1 (by rfl) ⟨6928415, by rfl⟩ : syracuseStep 9237887 = 13856831) B13856831
theorem B3470975 : Blo 358757 3470975 := bstep (se 1 (by rfl) ⟨2603231, by rfl⟩ : syracuseStep 3470975 = 5206463) B5206463
theorem B10385243 : Blo 358757 10385243 := bstep (se 1 (by rfl) ⟨7788932, by rfl⟩ : syracuseStep 10385243 = 15577865) B15577865
theorem B1213433 : Blo 358757 1213433 := bstep (se 2 (by rfl) ⟨455037, by rfl⟩ : syracuseStep 1213433 = 910075) B910075
theorem B820315 : Blo 358757 820315 := bstep (se 1 (by rfl) ⟨615236, by rfl⟩ : syracuseStep 820315 = 1230473) B1230473
theorem B2753675 : Blo 358757 2753675 := bstep (se 1 (by rfl) ⟨2065256, by rfl⟩ : syracuseStep 2753675 = 4130513) B4130513
theorem B362587 : Blo 358757 362587 := bstep (se 1 (by rfl) ⟨271940, by rfl⟩ : syracuseStep 362587 = 543881) B543881
theorem B8457473 : Blo 358757 8457473 := bstep (se 2 (by rfl) ⟨3171552, by rfl⟩ : syracuseStep 8457473 = 6343105) B6343105
theorem B3116879 : Blo 358757 3116879 := bstep (se 1 (by rfl) ⟨2337659, by rfl⟩ : syracuseStep 3116879 = 4675319) B4675319
theorem B15667667 : Blo 358757 15667667 := bstep (se 1 (by rfl) ⟨11750750, by rfl⟩ : syracuseStep 15667667 = 23501501) B23501501
theorem B1218779 : Blo 358757 1218779 := bstep (se 1 (by rfl) ⟨914084, by rfl⟩ : syracuseStep 1218779 = 1828169) B1828169
theorem B3907615 : Blo 358757 3907615 := bstep (se 1 (by rfl) ⟨2930711, by rfl⟩ : syracuseStep 3907615 = 5861423) B5861423
theorem B6923495 : Blo 358757 6923495 := bstep (se 1 (by rfl) ⟨5192621, by rfl⟩ : syracuseStep 6923495 = 10385243) B10385243
theorem B403663 : Blo 358757 403663 := bstep (se 1 (by rfl) ⟨302747, by rfl⟩ : syracuseStep 403663 = 605495) B605495
theorem B4664735 : Blo 358757 4664735 := bstep (se 1 (by rfl) ⟨3498551, by rfl⟩ : syracuseStep 4664735 = 6997103) B6997103
theorem B3091871 : Blo 358757 3091871 := bstep (se 1 (by rfl) ⟨2318903, by rfl⟩ : syracuseStep 3091871 = 4637807) B4637807
theorem B406255 : Blo 358757 406255 := bstep (se 1 (by rfl) ⟨304691, by rfl⟩ : syracuseStep 406255 = 609383) B609383
theorem B6141095 : Blo 358757 6141095 := bstep (se 1 (by rfl) ⟨4605821, by rfl⟩ : syracuseStep 6141095 = 9211643) B9211643
theorem B4373203 : Blo 358757 4373203 := bstep (se 1 (by rfl) ⟨3279902, by rfl⟩ : syracuseStep 4373203 = 6559805) B6559805
theorem B539807 : Blo 358757 539807 := bstep (se 1 (by rfl) ⟨404855, by rfl⟩ : syracuseStep 539807 = 809711) B809711
theorem B541007 : Blo 358757 541007 := bstep (se 1 (by rfl) ⟨405755, by rfl⟩ : syracuseStep 541007 = 811511) B811511
theorem B1819259 : Blo 358757 1819259 := bstep (se 1 (by rfl) ⟨1364444, by rfl⟩ : syracuseStep 1819259 = 2728889) B2728889
theorem B542555 : Blo 358757 542555 := bstep (se 1 (by rfl) ⟨406916, by rfl⟩ : syracuseStep 542555 = 813833) B813833
theorem B14076935 : Blo 358757 14076935 := bstep (se 1 (by rfl) ⟨10557701, by rfl⟩ : syracuseStep 14076935 = 21115403) B21115403
theorem B544103 : Blo 358757 544103 := bstep (se 1 (by rfl) ⟨408077, by rfl⟩ : syracuseStep 544103 = 816155) B816155
theorem B609707 : Blo 358757 609707 := bstep (se 1 (by rfl) ⟨457280, by rfl⟩ : syracuseStep 609707 = 914561) B914561
theorem B2313983 : Blo 358757 2313983 := bstep (se 1 (by rfl) ⟨1735487, by rfl⟩ : syracuseStep 2313983 = 3470975) B3470975
theorem B5951663 : Blo 358757 5951663 := bstep (se 1 (by rfl) ⟨4463747, by rfl⟩ : syracuseStep 5951663 = 8927495) B8927495
theorem B971887 : Blo 358757 971887 := bstep (se 1 (by rfl) ⟨728915, by rfl⟩ : syracuseStep 971887 = 1457831) B1457831
theorem B383135 : Blo 358757 383135 := bstep (se 1 (by rfl) ⟨287351, by rfl⟩ : syracuseStep 383135 = 574703) B574703
theorem B6970859 : Blo 358757 6970859 := bstep (se 1 (by rfl) ⟨5228144, by rfl⟩ : syracuseStep 6970859 = 10456289) B10456289
theorem B1367999 : Blo 358757 1367999 := bstep (se 1 (by rfl) ⟨1025999, by rfl⟩ : syracuseStep 1367999 = 2051999) B2051999
theorem B4219751 : Blo 358757 4219751 := bstep (se 1 (by rfl) ⟨3164813, by rfl⟩ : syracuseStep 4219751 = 6329627) B6329627
theorem B1565543 : Blo 358757 1565543 := bstep (se 1 (by rfl) ⟨1174157, by rfl⟩ : syracuseStep 1565543 = 2348315) B2348315
theorem B298315547 : Blo 358757 298315547 := bstep (se 1 (by rfl) ⟨223736660, by rfl⟩ : syracuseStep 298315547 = 447473321) B447473321
theorem B5666129 : Blo 358757 5666129 := bstep (se 2 (by rfl) ⟨2124798, by rfl⟩ : syracuseStep 5666129 = 4249597) B4249597
theorem B8583209 : Blo 358757 8583209 := bstep (se 2 (by rfl) ⟨3218703, by rfl⟩ : syracuseStep 8583209 = 6437407) B6437407
theorem B686171 : Blo 358757 686171 := bstep (se 1 (by rfl) ⟨514628, by rfl⟩ : syracuseStep 686171 = 1029257) B1029257
theorem B6158591 : Blo 358757 6158591 := bstep (se 1 (by rfl) ⟨4618943, by rfl⟩ : syracuseStep 6158591 = 9237887) B9237887
theorem B2586971 : Blo 358757 2586971 := bstep (se 1 (by rfl) ⟨1940228, by rfl⟩ : syracuseStep 2586971 = 3880457) B3880457
theorem B359103 : Blo 358757 359103 := bstep (se 1 (by rfl) ⟨269327, by rfl⟩ : syracuseStep 359103 = 538655) B538655
theorem B359143 : Blo 358757 359143 := bstep (se 1 (by rfl) ⟨269357, by rfl⟩ : syracuseStep 359143 = 538715) B538715
theorem B359167 : Blo 358757 359167 := bstep (se 1 (by rfl) ⟨269375, by rfl⟩ : syracuseStep 359167 = 538751) B538751
theorem B359663 : Blo 358757 359663 := bstep (se 1 (by rfl) ⟨269747, by rfl⟩ : syracuseStep 359663 = 539495) B539495
theorem B359967 : Blo 358757 359967 := bstep (se 1 (by rfl) ⟨269975, by rfl⟩ : syracuseStep 359967 = 539951) B539951
theorem B5210153 : Blo 358757 5210153 := bstep (se 2 (by rfl) ⟨1953807, by rfl⟩ : syracuseStep 5210153 = 3907615) B3907615
theorem B360671 : Blo 358757 360671 := bstep (se 1 (by rfl) ⟨270503, by rfl⟩ : syracuseStep 360671 = 541007) B541007
theorem B1212839 : Blo 358757 1212839 := bstep (se 1 (by rfl) ⟨909629, by rfl⟩ : syracuseStep 1212839 = 1819259) B1819259
theorem B1835783 : Blo 358757 1835783 := bstep (se 1 (by rfl) ⟨1376837, by rfl⟩ : syracuseStep 1835783 = 2753675) B2753675
theorem B361703 : Blo 358757 361703 := bstep (se 1 (by rfl) ⟨271277, by rfl⟩ : syracuseStep 361703 = 542555) B542555
theorem B362735 : Blo 358757 362735 := bstep (se 1 (by rfl) ⟨272051, by rfl⟩ : syracuseStep 362735 = 544103) B544103
theorem B1542655 : Blo 358757 1542655 := bstep (se 1 (by rfl) ⟨1156991, by rfl⟩ : syracuseStep 1542655 = 2313983) B2313983
theorem B3967775 : Blo 358757 3967775 := bstep (se 1 (by rfl) ⟨2975831, by rfl⟩ : syracuseStep 3967775 = 5951663) B5951663
theorem B198877031 : Blo 358757 198877031 := bstep (se 1 (by rfl) ⟨149157773, by rfl⟩ : syracuseStep 198877031 = 298315547) B298315547
theorem B22553261 : Blo 358757 22553261 := bstep (se 3 (by rfl) ⟨4228736, by rfl⟩ : syracuseStep 22553261 = 8457473) B8457473
theorem B3777419 : Blo 358757 3777419 := bstep (se 1 (by rfl) ⟨2833064, by rfl⟩ : syracuseStep 3777419 = 5666129) B5666129
theorem B4105727 : Blo 358757 4105727 := bstep (se 1 (by rfl) ⟨3079295, by rfl⟩ : syracuseStep 4105727 = 6158591) B6158591
theorem B1093753 : Blo 358757 1093753 := bstep (se 2 (by rfl) ⟨410157, by rfl⟩ : syracuseStep 1093753 = 820315) B820315
theorem B9384623 : Blo 358757 9384623 := bstep (se 1 (by rfl) ⟨7038467, by rfl⟩ : syracuseStep 9384623 = 14076935) B14076935
theorem B406471 : Blo 358757 406471 := bstep (se 1 (by rfl) ⟨304853, by rfl⟩ : syracuseStep 406471 = 609707) B609707
theorem B2077919 : Blo 358757 2077919 := bstep (se 1 (by rfl) ⟨1558439, by rfl⟩ : syracuseStep 2077919 = 3116879) B3116879
theorem B538217 : Blo 358757 538217 := bstep (se 2 (by rfl) ⟨201831, by rfl⟩ : syracuseStep 538217 = 403663) B403663
theorem B180042709 : Blo 358757 180042709 := bstep (se 7 (by rfl) ⟨2109875, by rfl⟩ : syracuseStep 180042709 = 4219751) B4219751
theorem B541673 : Blo 358757 541673 := bstep (se 2 (by rfl) ⟨203127, by rfl⟩ : syracuseStep 541673 = 406255) B406255
theorem B1295849 : Blo 358757 1295849 := bstep (se 2 (by rfl) ⟨485943, by rfl⟩ : syracuseStep 1295849 = 971887) B971887
theorem B5722139 : Blo 358757 5722139 := bstep (se 1 (by rfl) ⟨4291604, by rfl⟩ : syracuseStep 5722139 = 8583209) B8583209
theorem B1724647 : Blo 358757 1724647 := bstep (se 1 (by rfl) ⟨1293485, by rfl⟩ : syracuseStep 1724647 = 2586971) B2586971
theorem B808955 : Blo 358757 808955 := bstep (se 1 (by rfl) ⟨606716, by rfl⟩ : syracuseStep 808955 = 1213433) B1213433
theorem B4086773 : Blo 358757 4086773 := bstep (se 5 (by rfl) ⟨191567, by rfl⟩ : syracuseStep 4086773 = 383135) B383135
theorem B10445111 : Blo 358757 10445111 := bstep (se 1 (by rfl) ⟨7833833, by rfl⟩ : syracuseStep 10445111 = 15667667) B15667667
theorem B812519 : Blo 358757 812519 := bstep (se 1 (by rfl) ⟨609389, by rfl⟩ : syracuseStep 812519 = 1218779) B1218779
theorem B4647239 : Blo 358757 4647239 := bstep (se 1 (by rfl) ⟨3485429, by rfl⟩ : syracuseStep 4647239 = 6970859) B6970859
theorem B911999 : Blo 358757 911999 := bstep (se 1 (by rfl) ⟨683999, by rfl⟩ : syracuseStep 911999 = 1367999) B1367999
theorem B1829789 : Blo 358757 1829789 := bstep (se 3 (by rfl) ⟨343085, by rfl⟩ : syracuseStep 1829789 = 686171) B686171
theorem B1043695 : Blo 358757 1043695 := bstep (se 1 (by rfl) ⟨782771, by rfl⟩ : syracuseStep 1043695 = 1565543) B1565543
theorem B4615663 : Blo 358757 4615663 := bstep (se 1 (by rfl) ⟨3461747, by rfl⟩ : syracuseStep 4615663 = 6923495) B6923495
theorem B3109823 : Blo 358757 3109823 := bstep (se 1 (by rfl) ⟨2332367, by rfl⟩ : syracuseStep 3109823 = 4664735) B4664735
theorem B2061247 : Blo 358757 2061247 := bstep (se 1 (by rfl) ⟨1545935, by rfl⟩ : syracuseStep 2061247 = 3091871) B3091871
theorem B4094063 : Blo 358757 4094063 := bstep (se 1 (by rfl) ⟨3070547, by rfl⟩ : syracuseStep 4094063 = 6141095) B6141095
theorem B5830937 : Blo 358757 5830937 := bstep (se 2 (by rfl) ⟨2186601, by rfl⟩ : syracuseStep 5830937 = 4373203) B4373203
theorem B359871 : Blo 358757 359871 := bstep (se 1 (by rfl) ⟨269903, by rfl⟩ : syracuseStep 359871 = 539807) B539807
theorem B3473435 : Blo 358757 3473435 := bstep (se 1 (by rfl) ⟨2605076, by rfl⟩ : syracuseStep 3473435 = 5210153) B5210153
theorem B361115 : Blo 358757 361115 := bstep (se 1 (by rfl) ⟨270836, by rfl⟩ : syracuseStep 361115 = 541673) B541673
theorem B2724515 : Blo 358757 2724515 := bstep (se 1 (by rfl) ⟨2043386, by rfl⟩ : syracuseStep 2724515 = 4086773) B4086773
theorem B132584687 : Blo 358757 132584687 := bstep (se 1 (by rfl) ⟨99438515, by rfl⟩ : syracuseStep 132584687 = 198877031) B198877031
theorem B2299529 : Blo 358757 2299529 := bstep (se 2 (by rfl) ⟨862323, by rfl⟩ : syracuseStep 2299529 = 1724647) B1724647
theorem B1219859 : Blo 358757 1219859 := bstep (se 1 (by rfl) ⟨914894, by rfl⟩ : syracuseStep 1219859 = 1829789) B1829789
theorem B2073215 : Blo 358757 2073215 := bstep (se 1 (by rfl) ⟨1554911, by rfl⟩ : syracuseStep 2073215 = 3109823) B3109823
theorem B1385279 : Blo 358757 1385279 := bstep (se 1 (by rfl) ⟨1038959, by rfl⟩ : syracuseStep 1385279 = 2077919) B2077919
theorem B2729375 : Blo 358757 2729375 := bstep (se 1 (by rfl) ⟨2047031, by rfl⟩ : syracuseStep 2729375 = 4094063) B4094063
theorem B1223855 : Blo 358757 1223855 := bstep (se 1 (by rfl) ⟨917891, by rfl⟩ : syracuseStep 1223855 = 1835783) B1835783
theorem B10073117 : Blo 358757 10073117 := bstep (se 3 (by rfl) ⟨1888709, by rfl⟩ : syracuseStep 10073117 = 3777419) B3777419
theorem B3814759 : Blo 358757 3814759 := bstep (se 1 (by rfl) ⟨2861069, by rfl⟩ : syracuseStep 3814759 = 5722139) B5722139
theorem B3455597 : Blo 358757 3455597 := bstep (se 3 (by rfl) ⟨647924, by rfl⟩ : syracuseStep 3455597 = 1295849) B1295849
theorem B539303 : Blo 358757 539303 := bstep (se 1 (by rfl) ⟨404477, by rfl⟩ : syracuseStep 539303 = 808955) B808955
theorem B1391593 : Blo 358757 1391593 := bstep (se 2 (by rfl) ⟨521847, by rfl⟩ : syracuseStep 1391593 = 1043695) B1043695
theorem B1458337 : Blo 358757 1458337 := bstep (se 2 (by rfl) ⟨546876, by rfl⟩ : syracuseStep 1458337 = 1093753) B1093753
theorem B6963407 : Blo 358757 6963407 := bstep (se 1 (by rfl) ⟨5222555, by rfl⟩ : syracuseStep 6963407 = 10445111) B10445111
theorem B541679 : Blo 358757 541679 := bstep (se 1 (by rfl) ⟨406259, by rfl⟩ : syracuseStep 541679 = 812519) B812519
theorem B2737151 : Blo 358757 2737151 := bstep (se 1 (by rfl) ⟨2052863, by rfl⟩ : syracuseStep 2737151 = 4105727) B4105727
theorem B541961 : Blo 358757 541961 := bstep (se 2 (by rfl) ⟨203235, by rfl⟩ : syracuseStep 541961 = 406471) B406471
theorem B3098159 : Blo 358757 3098159 := bstep (se 1 (by rfl) ⟨2323619, by rfl⟩ : syracuseStep 3098159 = 4647239) B4647239
theorem B607999 : Blo 358757 607999 := bstep (se 1 (by rfl) ⟨455999, by rfl⟩ : syracuseStep 607999 = 911999) B911999
theorem B3887291 : Blo 358757 3887291 := bstep (se 1 (by rfl) ⟨2915468, by rfl⟩ : syracuseStep 3887291 = 5830937) B5830937
theorem B808559 : Blo 358757 808559 := bstep (se 1 (by rfl) ⟨606419, by rfl⟩ : syracuseStep 808559 = 1212839) B1212839
theorem B2645183 : Blo 358757 2645183 := bstep (se 1 (by rfl) ⟨1983887, by rfl⟩ : syracuseStep 2645183 = 3967775) B3967775
theorem B2056873 : Blo 358757 2056873 := bstep (se 2 (by rfl) ⟨771327, by rfl⟩ : syracuseStep 2056873 = 1542655) B1542655
theorem B6154217 : Blo 358757 6154217 := bstep (se 2 (by rfl) ⟨2307831, by rfl⟩ : syracuseStep 6154217 = 4615663) B4615663
theorem B15035507 : Blo 358757 15035507 := bstep (se 1 (by rfl) ⟨11276630, by rfl⟩ : syracuseStep 15035507 = 22553261) B22553261
theorem B2748329 : Blo 358757 2748329 := bstep (se 2 (by rfl) ⟨1030623, by rfl⟩ : syracuseStep 2748329 = 2061247) B2061247
theorem B6256415 : Blo 358757 6256415 := bstep (se 1 (by rfl) ⟨4692311, by rfl⟩ : syracuseStep 6256415 = 9384623) B9384623
theorem B358811 : Blo 358757 358811 := bstep (se 1 (by rfl) ⟨269108, by rfl⟩ : syracuseStep 358811 = 538217) B538217
theorem B240056945 : Blo 358757 240056945 := bstep (se 2 (by rfl) ⟨90021354, by rfl⟩ : syracuseStep 240056945 = 180042709) B180042709
theorem B361119 : Blo 358757 361119 := bstep (se 1 (by rfl) ⟨270839, by rfl⟩ : syracuseStep 361119 = 541679) B541679
theorem B361307 : Blo 358757 361307 := bstep (se 1 (by rfl) ⟨270980, by rfl⟩ : syracuseStep 361307 = 541961) B541961
theorem B2065439 : Blo 358757 2065439 := bstep (se 1 (by rfl) ⟨1549079, by rfl⟩ : syracuseStep 2065439 = 3098159) B3098159
theorem B2591527 : Blo 358757 2591527 := bstep (se 1 (by rfl) ⟨1943645, by rfl⟩ : syracuseStep 2591527 = 3887291) B3887291
theorem B1382143 : Blo 358757 1382143 := bstep (se 1 (by rfl) ⟨1036607, by rfl⟩ : syracuseStep 1382143 = 2073215) B2073215
theorem B923519 : Blo 358757 923519 := bstep (se 1 (by rfl) ⟨692639, by rfl⟩ : syracuseStep 923519 = 1385279) B1385279
theorem B4102811 : Blo 358757 4102811 := bstep (se 1 (by rfl) ⟨3077108, by rfl⟩ : syracuseStep 4102811 = 6154217) B6154217
theorem B4170943 : Blo 358757 4170943 := bstep (se 1 (by rfl) ⟨3128207, by rfl⟩ : syracuseStep 4170943 = 6256415) B6256415
theorem B2303731 : Blo 358757 2303731 := bstep (se 1 (by rfl) ⟨1727798, by rfl⟩ : syracuseStep 2303731 = 3455597) B3455597
theorem B1944449 : Blo 358757 1944449 := bstep (se 2 (by rfl) ⟨729168, by rfl⟩ : syracuseStep 1944449 = 1458337) B1458337
theorem B1816343 : Blo 358757 1816343 := bstep (se 1 (by rfl) ⟨1362257, by rfl⟩ : syracuseStep 1816343 = 2724515) B2724515
theorem B88389791 : Blo 358757 88389791 := bstep (se 1 (by rfl) ⟨66292343, by rfl⟩ : syracuseStep 88389791 = 132584687) B132584687
theorem B539039 : Blo 358757 539039 := bstep (se 1 (by rfl) ⟨404279, by rfl⟩ : syracuseStep 539039 = 808559) B808559
theorem B1819583 : Blo 358757 1819583 := bstep (se 1 (by rfl) ⟨1364687, by rfl⟩ : syracuseStep 1819583 = 2729375) B2729375
theorem B1855457 : Blo 358757 1855457 := bstep (se 2 (by rfl) ⟨695796, by rfl⟩ : syracuseStep 1855457 = 1391593) B1391593
theorem B2315623 : Blo 358757 2315623 := bstep (se 1 (by rfl) ⟨1736717, by rfl⟩ : syracuseStep 2315623 = 3473435) B3473435
theorem B4642271 : Blo 358757 4642271 := bstep (se 1 (by rfl) ⟨3481703, by rfl⟩ : syracuseStep 4642271 = 6963407) B6963407
theorem B1824767 : Blo 358757 1824767 := bstep (se 1 (by rfl) ⟨1368575, by rfl⟩ : syracuseStep 1824767 = 2737151) B2737151
theorem B2742497 : Blo 358757 2742497 := bstep (se 2 (by rfl) ⟨1028436, by rfl⟩ : syracuseStep 2742497 = 2056873) B2056873
theorem B810665 : Blo 358757 810665 := bstep (se 2 (by rfl) ⟨303999, by rfl⟩ : syracuseStep 810665 = 607999) B607999
theorem B26861645 : Blo 358757 26861645 := bstep (se 3 (by rfl) ⟨5036558, by rfl⟩ : syracuseStep 26861645 = 10073117) B10073117
theorem B1533019 : Blo 358757 1533019 := bstep (se 1 (by rfl) ⟨1149764, by rfl⟩ : syracuseStep 1533019 = 2299529) B2299529
theorem B1763455 : Blo 358757 1763455 := bstep (se 1 (by rfl) ⟨1322591, by rfl⟩ : syracuseStep 1763455 = 2645183) B2645183
theorem B813239 : Blo 358757 813239 := bstep (se 1 (by rfl) ⟨609929, by rfl⟩ : syracuseStep 813239 = 1219859) B1219859
theorem B20345381 : Blo 358757 20345381 := bstep (se 4 (by rfl) ⟨1907379, by rfl⟩ : syracuseStep 20345381 = 3814759) B3814759
theorem B10023671 : Blo 358757 10023671 := bstep (se 1 (by rfl) ⟨7517753, by rfl⟩ : syracuseStep 10023671 = 15035507) B15035507
theorem B815903 : Blo 358757 815903 := bstep (se 1 (by rfl) ⟨611927, by rfl⟩ : syracuseStep 815903 = 1223855) B1223855
theorem B1832219 : Blo 358757 1832219 := bstep (se 1 (by rfl) ⟨1374164, by rfl⟩ : syracuseStep 1832219 = 2748329) B2748329
theorem B160037963 : Blo 358757 160037963 := bstep (se 1 (by rfl) ⟨120028472, by rfl⟩ : syracuseStep 160037963 = 240056945) B240056945
theorem B359535 : Blo 358757 359535 := bstep (se 1 (by rfl) ⟨269651, by rfl⟩ : syracuseStep 359535 = 539303) B539303
theorem B71631053 : Blo 358757 71631053 := bstep (se 3 (by rfl) ⟨13430822, by rfl⟩ : syracuseStep 71631053 = 26861645) B26861645
theorem B1213055 : Blo 358757 1213055 := bstep (se 1 (by rfl) ⟨909791, by rfl⟩ : syracuseStep 1213055 = 1819583) B1819583
theorem B1376959 : Blo 358757 1376959 := bstep (se 1 (by rfl) ⟨1032719, by rfl⟩ : syracuseStep 1376959 = 2065439) B2065439
theorem B1216511 : Blo 358757 1216511 := bstep (se 1 (by rfl) ⟨912383, by rfl⟩ : syracuseStep 1216511 = 1824767) B1824767
theorem B2462717 : Blo 358757 2462717 := bstep (se 3 (by rfl) ⟨461759, by rfl⟩ : syracuseStep 2462717 = 923519) B923519
theorem B3087497 : Blo 358757 3087497 := bstep (se 2 (by rfl) ⟨1157811, by rfl⟩ : syracuseStep 3087497 = 2315623) B2315623
theorem B1842857 : Blo 358757 1842857 := bstep (se 2 (by rfl) ⟨691071, by rfl⟩ : syracuseStep 1842857 = 1382143) B1382143
theorem B1221479 : Blo 358757 1221479 := bstep (se 1 (by rfl) ⟨916109, by rfl⟩ : syracuseStep 1221479 = 1832219) B1832219
theorem B58926527 : Blo 358757 58926527 := bstep (se 1 (by rfl) ⟨44194895, by rfl⟩ : syracuseStep 58926527 = 88389791) B88389791
theorem B2044025 : Blo 358757 2044025 := bstep (se 2 (by rfl) ⟨766509, by rfl⟩ : syracuseStep 2044025 = 1533019) B1533019
theorem B3094847 : Blo 358757 3094847 := bstep (se 1 (by rfl) ⟨2321135, by rfl⟩ : syracuseStep 3094847 = 4642271) B4642271
theorem B3455369 : Blo 358757 3455369 := bstep (se 2 (by rfl) ⟨1295763, by rfl⟩ : syracuseStep 3455369 = 2591527) B2591527
theorem B2735207 : Blo 358757 2735207 := bstep (se 1 (by rfl) ⟨2051405, by rfl⟩ : syracuseStep 2735207 = 4102811) B4102811
theorem B540443 : Blo 358757 540443 := bstep (se 1 (by rfl) ⟨405332, by rfl⟩ : syracuseStep 540443 = 810665) B810665
theorem B542159 : Blo 358757 542159 := bstep (se 1 (by rfl) ⟨406619, by rfl⟩ : syracuseStep 542159 = 813239) B813239
theorem B1296299 : Blo 358757 1296299 := bstep (se 1 (by rfl) ⟨972224, by rfl⟩ : syracuseStep 1296299 = 1944449) B1944449
theorem B543935 : Blo 358757 543935 := bstep (se 1 (by rfl) ⟨407951, by rfl⟩ : syracuseStep 543935 = 815903) B815903
theorem B5561257 : Blo 358757 5561257 := bstep (se 2 (by rfl) ⟨2085471, by rfl⟩ : syracuseStep 5561257 = 4170943) B4170943
theorem B3071641 : Blo 358757 3071641 := bstep (se 2 (by rfl) ⟨1151865, by rfl⟩ : syracuseStep 3071641 = 2303731) B2303731
theorem B1236971 : Blo 358757 1236971 := bstep (se 1 (by rfl) ⟨927728, by rfl⟩ : syracuseStep 1236971 = 1855457) B1855457
theorem B2351273 : Blo 358757 2351273 := bstep (se 2 (by rfl) ⟨881727, by rfl⟩ : syracuseStep 2351273 = 1763455) B1763455
theorem B1828331 : Blo 358757 1828331 := bstep (se 1 (by rfl) ⟨1371248, by rfl⟩ : syracuseStep 1828331 = 2742497) B2742497
theorem B13563587 : Blo 358757 13563587 := bstep (se 1 (by rfl) ⟨10172690, by rfl⟩ : syracuseStep 13563587 = 20345381) B20345381
theorem B6682447 : Blo 358757 6682447 := bstep (se 1 (by rfl) ⟨5011835, by rfl⟩ : syracuseStep 6682447 = 10023671) B10023671
theorem B1210895 : Blo 358757 1210895 := bstep (se 1 (by rfl) ⟨908171, by rfl⟩ : syracuseStep 1210895 = 1816343) B1816343
theorem B359359 : Blo 358757 359359 := bstep (se 1 (by rfl) ⟨269519, by rfl⟩ : syracuseStep 359359 = 539039) B539039
theorem B106691975 : Blo 358757 106691975 := bstep (se 1 (by rfl) ⟨80018981, by rfl⟩ : syracuseStep 106691975 = 160037963) B160037963
theorem B1835945 : Blo 358757 1835945 := bstep (se 2 (by rfl) ⟨688479, by rfl⟩ : syracuseStep 1835945 = 1376959) B1376959
theorem B361439 : Blo 358757 361439 := bstep (se 1 (by rfl) ⟨271079, by rfl⟩ : syracuseStep 361439 = 542159) B542159
theorem B362623 : Blo 358757 362623 := bstep (se 1 (by rfl) ⟨271967, by rfl⟩ : syracuseStep 362623 = 543935) B543935
theorem B1641811 : Blo 358757 1641811 := bstep (se 1 (by rfl) ⟨1231358, by rfl⟩ : syracuseStep 1641811 = 2462717) B2462717
theorem B1218887 : Blo 358757 1218887 := bstep (se 1 (by rfl) ⟨914165, by rfl⟩ : syracuseStep 1218887 = 1828331) B1828331
theorem B7415009 : Blo 358757 7415009 := bstep (se 2 (by rfl) ⟨2780628, by rfl⟩ : syracuseStep 7415009 = 5561257) B5561257
theorem B2303579 : Blo 358757 2303579 := bstep (se 1 (by rfl) ⟨1727684, by rfl⟩ : syracuseStep 2303579 = 3455369) B3455369
theorem B47754035 : Blo 358757 47754035 := bstep (se 1 (by rfl) ⟨35815526, by rfl⟩ : syracuseStep 47754035 = 71631053) B71631053
theorem B6270061 : Blo 358757 6270061 := bstep (se 3 (by rfl) ⟨1175636, by rfl⟩ : syracuseStep 6270061 = 2351273) B2351273
theorem B864199 : Blo 358757 864199 := bstep (se 1 (by rfl) ⟨648149, by rfl⟩ : syracuseStep 864199 = 1296299) B1296299
theorem B1228571 : Blo 358757 1228571 := bstep (se 1 (by rfl) ⟨921428, by rfl⟩ : syracuseStep 1228571 = 1842857) B1842857
theorem B1362683 : Blo 358757 1362683 := bstep (se 1 (by rfl) ⟨1022012, by rfl⟩ : syracuseStep 1362683 = 2044025) B2044025
theorem B807263 : Blo 358757 807263 := bstep (se 1 (by rfl) ⟨605447, by rfl⟩ : syracuseStep 807263 = 1210895) B1210895
theorem B1823471 : Blo 358757 1823471 := bstep (se 1 (by rfl) ⟨1367603, by rfl⟩ : syracuseStep 1823471 = 2735207) B2735207
theorem B71127983 : Blo 358757 71127983 := bstep (se 1 (by rfl) ⟨53345987, by rfl⟩ : syracuseStep 71127983 = 106691975) B106691975
theorem B3298589 : Blo 358757 3298589 := bstep (se 3 (by rfl) ⟨618485, by rfl⟩ : syracuseStep 3298589 = 1236971) B1236971
theorem B808703 : Blo 358757 808703 := bstep (se 1 (by rfl) ⟨606527, by rfl⟩ : syracuseStep 808703 = 1213055) B1213055
theorem B811007 : Blo 358757 811007 := bstep (se 1 (by rfl) ⟨608255, by rfl⟩ : syracuseStep 811007 = 1216511) B1216511
theorem B2058331 : Blo 358757 2058331 := bstep (se 1 (by rfl) ⟨1543748, by rfl⟩ : syracuseStep 2058331 = 3087497) B3087497
theorem B814319 : Blo 358757 814319 := bstep (se 1 (by rfl) ⟨610739, by rfl⟩ : syracuseStep 814319 = 1221479) B1221479
theorem B39284351 : Blo 358757 39284351 := bstep (se 1 (by rfl) ⟨29463263, by rfl⟩ : syracuseStep 39284351 = 58926527) B58926527
theorem B8909929 : Blo 358757 8909929 := bstep (se 2 (by rfl) ⟨3341223, by rfl⟩ : syracuseStep 8909929 = 6682447) B6682447
theorem B9042391 : Blo 358757 9042391 := bstep (se 1 (by rfl) ⟨6781793, by rfl⟩ : syracuseStep 9042391 = 13563587) B13563587
theorem B2063231 : Blo 358757 2063231 := bstep (se 1 (by rfl) ⟨1547423, by rfl⟩ : syracuseStep 2063231 = 3094847) B3094847
theorem B4095521 : Blo 358757 4095521 := bstep (se 2 (by rfl) ⟨1535820, by rfl⟩ : syracuseStep 4095521 = 3071641) B3071641
theorem B360295 : Blo 358757 360295 := bstep (se 1 (by rfl) ⟨270221, by rfl⟩ : syracuseStep 360295 = 540443) B540443
theorem B1215647 : Blo 358757 1215647 := bstep (se 1 (by rfl) ⟨911735, by rfl⟩ : syracuseStep 1215647 = 1823471) B1823471
theorem B47418655 : Blo 358757 47418655 := bstep (se 1 (by rfl) ⟨35563991, by rfl⟩ : syracuseStep 47418655 = 71127983) B71127983
theorem B2199059 : Blo 358757 2199059 := bstep (se 1 (by rfl) ⟨1649294, by rfl⟩ : syracuseStep 2199059 = 3298589) B3298589
theorem B8360081 : Blo 358757 8360081 := bstep (se 2 (by rfl) ⟨3135030, by rfl⟩ : syracuseStep 8360081 = 6270061) B6270061
theorem B1152265 : Blo 358757 1152265 := bstep (se 2 (by rfl) ⟨432099, by rfl⟩ : syracuseStep 1152265 = 864199) B864199
theorem B26189567 : Blo 358757 26189567 := bstep (se 1 (by rfl) ⟨19642175, by rfl⟩ : syracuseStep 26189567 = 39284351) B39284351
theorem B2730347 : Blo 358757 2730347 := bstep (se 1 (by rfl) ⟨2047760, by rfl⟩ : syracuseStep 2730347 = 4095521) B4095521
theorem B1223963 : Blo 358757 1223963 := bstep (se 1 (by rfl) ⟨917972, by rfl⟩ : syracuseStep 1223963 = 1835945) B1835945
theorem B538175 : Blo 358757 538175 := bstep (se 1 (by rfl) ⟨403631, by rfl⟩ : syracuseStep 538175 = 807263) B807263
theorem B539135 : Blo 358757 539135 := bstep (se 1 (by rfl) ⟨404351, by rfl⟩ : syracuseStep 539135 = 808703) B808703
theorem B540671 : Blo 358757 540671 := bstep (se 1 (by rfl) ⟨405503, by rfl⟩ : syracuseStep 540671 = 811007) B811007
theorem B11879905 : Blo 358757 11879905 := bstep (se 2 (by rfl) ⟨4454964, by rfl⟩ : syracuseStep 11879905 = 8909929) B8909929
theorem B31836023 : Blo 358757 31836023 := bstep (se 1 (by rfl) ⟨23877017, by rfl⟩ : syracuseStep 31836023 = 47754035) B47754035
theorem B542879 : Blo 358757 542879 := bstep (se 1 (by rfl) ⟨407159, by rfl⟩ : syracuseStep 542879 = 814319) B814319
theorem B908455 : Blo 358757 908455 := bstep (se 1 (by rfl) ⟨681341, by rfl⟩ : syracuseStep 908455 = 1362683) B1362683
theorem B2744441 : Blo 358757 2744441 := bstep (se 2 (by rfl) ⟨1029165, by rfl⟩ : syracuseStep 2744441 = 2058331) B2058331
theorem B812591 : Blo 358757 812591 := bstep (se 1 (by rfl) ⟨609443, by rfl⟩ : syracuseStep 812591 = 1218887) B1218887
theorem B2189081 : Blo 358757 2189081 := bstep (se 2 (by rfl) ⟨820905, by rfl⟩ : syracuseStep 2189081 = 1641811) B1641811
theorem B4943339 : Blo 358757 4943339 := bstep (se 1 (by rfl) ⟨3707504, by rfl⟩ : syracuseStep 4943339 = 7415009) B7415009
theorem B1535719 : Blo 358757 1535719 := bstep (se 1 (by rfl) ⟨1151789, by rfl⟩ : syracuseStep 1535719 = 2303579) B2303579
theorem B12056521 : Blo 358757 12056521 := bstep (se 2 (by rfl) ⟨4521195, by rfl⟩ : syracuseStep 12056521 = 9042391) B9042391
theorem B1375487 : Blo 358757 1375487 := bstep (se 1 (by rfl) ⟨1031615, by rfl⟩ : syracuseStep 1375487 = 2063231) B2063231
theorem B819047 : Blo 358757 819047 := bstep (se 1 (by rfl) ⟨614285, by rfl⟩ : syracuseStep 819047 = 1228571) B1228571
theorem B361919 : Blo 358757 361919 := bstep (se 1 (by rfl) ⟨271439, by rfl⟩ : syracuseStep 361919 = 542879) B542879
theorem B5573387 : Blo 358757 5573387 := bstep (se 1 (by rfl) ⟨4180040, by rfl⟩ : syracuseStep 5573387 = 8360081) B8360081
theorem B15839873 : Blo 358757 15839873 := bstep (se 2 (by rfl) ⟨5939952, by rfl⟩ : syracuseStep 15839873 = 11879905) B11879905
theorem B63224873 : Blo 358757 63224873 := bstep (se 2 (by rfl) ⟨23709327, by rfl⟩ : syracuseStep 63224873 = 47418655) B47418655
theorem B2047625 : Blo 358757 2047625 := bstep (se 2 (by rfl) ⟨767859, by rfl⟩ : syracuseStep 2047625 = 1535719) B1535719
theorem B541727 : Blo 358757 541727 := bstep (se 1 (by rfl) ⟨406295, by rfl⟩ : syracuseStep 541727 = 812591) B812591
theorem B1459387 : Blo 358757 1459387 := bstep (se 1 (by rfl) ⟨1094540, by rfl⟩ : syracuseStep 1459387 = 2189081) B2189081
theorem B1820231 : Blo 358757 1820231 := bstep (se 1 (by rfl) ⟨1365173, by rfl⟩ : syracuseStep 1820231 = 2730347) B2730347
theorem B3295559 : Blo 358757 3295559 := bstep (se 1 (by rfl) ⟨2471669, by rfl⟩ : syracuseStep 3295559 = 4943339) B4943339
theorem B16075361 : Blo 358757 16075361 := bstep (se 2 (by rfl) ⟨6028260, by rfl⟩ : syracuseStep 16075361 = 12056521) B12056521
theorem B546031 : Blo 358757 546031 := bstep (se 1 (by rfl) ⟨409523, by rfl⟩ : syracuseStep 546031 = 819047) B819047
theorem B21224015 : Blo 358757 21224015 := bstep (se 1 (by rfl) ⟨15918011, by rfl⟩ : syracuseStep 21224015 = 31836023) B31836023
theorem B810431 : Blo 358757 810431 := bstep (se 1 (by rfl) ⟨607823, by rfl⟩ : syracuseStep 810431 = 1215647) B1215647
theorem B1466039 : Blo 358757 1466039 := bstep (se 1 (by rfl) ⟨1099529, by rfl⟩ : syracuseStep 1466039 = 2199059) B2199059
theorem B17459711 : Blo 358757 17459711 := bstep (se 1 (by rfl) ⟨13094783, by rfl⟩ : syracuseStep 17459711 = 26189567) B26189567
theorem B1829627 : Blo 358757 1829627 := bstep (se 1 (by rfl) ⟨1372220, by rfl⟩ : syracuseStep 1829627 = 2744441) B2744441
theorem B1536353 : Blo 358757 1536353 := bstep (se 2 (by rfl) ⟨576132, by rfl⟩ : syracuseStep 1536353 = 1152265) B1152265
theorem B815975 : Blo 358757 815975 := bstep (se 1 (by rfl) ⟨611981, by rfl⟩ : syracuseStep 815975 = 1223963) B1223963
theorem B358783 : Blo 358757 358783 := bstep (se 1 (by rfl) ⟨269087, by rfl⟩ : syracuseStep 358783 = 538175) B538175
theorem B1211273 : Blo 358757 1211273 := bstep (se 2 (by rfl) ⟨454227, by rfl⟩ : syracuseStep 1211273 = 908455) B908455
theorem B359423 : Blo 358757 359423 := bstep (se 1 (by rfl) ⟨269567, by rfl⟩ : syracuseStep 359423 = 539135) B539135
theorem B916991 : Blo 358757 916991 := bstep (se 1 (by rfl) ⟨687743, by rfl⟩ : syracuseStep 916991 = 1375487) B1375487
theorem B360447 : Blo 358757 360447 := bstep (se 1 (by rfl) ⟨270335, by rfl⟩ : syracuseStep 360447 = 540671) B540671
theorem B361151 : Blo 358757 361151 := bstep (se 1 (by rfl) ⟨270863, by rfl⟩ : syracuseStep 361151 = 541727) B541727
theorem B1213487 : Blo 358757 1213487 := bstep (se 1 (by rfl) ⟨910115, by rfl⟩ : syracuseStep 1213487 = 1820231) B1820231
theorem B2197039 : Blo 358757 2197039 := bstep (se 1 (by rfl) ⟨1647779, by rfl⟩ : syracuseStep 2197039 = 3295559) B3295559
theorem B10716907 : Blo 358757 10716907 := bstep (se 1 (by rfl) ⟨8037680, by rfl⟩ : syracuseStep 10716907 = 16075361) B16075361
theorem B728041 : Blo 358757 728041 := bstep (se 2 (by rfl) ⟨273015, by rfl⟩ : syracuseStep 728041 = 546031) B546031
theorem B11639807 : Blo 358757 11639807 := bstep (se 1 (by rfl) ⟨8729855, by rfl⟩ : syracuseStep 11639807 = 17459711) B17459711
theorem B1219751 : Blo 358757 1219751 := bstep (se 1 (by rfl) ⟨914813, by rfl⟩ : syracuseStep 1219751 = 1829627) B1829627
theorem B1024235 : Blo 358757 1024235 := bstep (se 1 (by rfl) ⟨768176, by rfl⟩ : syracuseStep 1024235 = 1536353) B1536353
theorem B10559915 : Blo 358757 10559915 := bstep (se 1 (by rfl) ⟨7919936, by rfl⟩ : syracuseStep 10559915 = 15839873) B15839873
theorem B42149915 : Blo 358757 42149915 := bstep (se 1 (by rfl) ⟨31612436, by rfl⟩ : syracuseStep 42149915 = 63224873) B63224873
theorem B3715591 : Blo 358757 3715591 := bstep (se 1 (by rfl) ⟨2786693, by rfl⟩ : syracuseStep 3715591 = 5573387) B5573387
theorem B540287 : Blo 358757 540287 := bstep (se 1 (by rfl) ⟨405215, by rfl⟩ : syracuseStep 540287 = 810431) B810431
theorem B7783397 : Blo 358757 7783397 := bstep (se 4 (by rfl) ⟨729693, by rfl⟩ : syracuseStep 7783397 = 1459387) B1459387
theorem B543983 : Blo 358757 543983 := bstep (se 1 (by rfl) ⟨407987, by rfl⟩ : syracuseStep 543983 = 815975) B815975
theorem B807515 : Blo 358757 807515 := bstep (se 1 (by rfl) ⟨605636, by rfl⟩ : syracuseStep 807515 = 1211273) B1211273
theorem B611327 : Blo 358757 611327 := bstep (se 1 (by rfl) ⟨458495, by rfl⟩ : syracuseStep 611327 = 916991) B916991
theorem B1365083 : Blo 358757 1365083 := bstep (se 1 (by rfl) ⟨1023812, by rfl⟩ : syracuseStep 1365083 = 2047625) B2047625
theorem B14149343 : Blo 358757 14149343 := bstep (se 1 (by rfl) ⟨10612007, by rfl⟩ : syracuseStep 14149343 = 21224015) B21224015
theorem B977359 : Blo 358757 977359 := bstep (se 1 (by rfl) ⟨733019, by rfl⟩ : syracuseStep 977359 = 1466039) B1466039
theorem B362655 : Blo 358757 362655 := bstep (se 1 (by rfl) ⟨271991, by rfl⟩ : syracuseStep 362655 = 543983) B543983
theorem B14289209 : Blo 358757 14289209 := bstep (se 2 (by rfl) ⟨5358453, by rfl⟩ : syracuseStep 14289209 = 10716907) B10716907
theorem B4954121 : Blo 358757 4954121 := bstep (se 2 (by rfl) ⟨1857795, by rfl⟩ : syracuseStep 4954121 = 3715591) B3715591
theorem B5188931 : Blo 358757 5188931 := bstep (se 1 (by rfl) ⟨3891698, by rfl⟩ : syracuseStep 5188931 = 7783397) B7783397
theorem B2929385 : Blo 358757 2929385 := bstep (se 2 (by rfl) ⟨1098519, by rfl⟩ : syracuseStep 2929385 = 2197039) B2197039
theorem B538343 : Blo 358757 538343 := bstep (se 1 (by rfl) ⟨403757, by rfl⟩ : syracuseStep 538343 = 807515) B807515
theorem B407551 : Blo 358757 407551 := bstep (se 1 (by rfl) ⟨305663, by rfl⟩ : syracuseStep 407551 = 611327) B611327
theorem B28099943 : Blo 358757 28099943 := bstep (se 1 (by rfl) ⟨21074957, by rfl⟩ : syracuseStep 28099943 = 42149915) B42149915
theorem B970721 : Blo 358757 970721 := bstep (se 2 (by rfl) ⟨364020, by rfl⟩ : syracuseStep 970721 = 728041) B728041
theorem B808991 : Blo 358757 808991 := bstep (se 1 (by rfl) ⟨606743, by rfl⟩ : syracuseStep 808991 = 1213487) B1213487
theorem B1303145 : Blo 358757 1303145 := bstep (se 2 (by rfl) ⟨488679, by rfl⟩ : syracuseStep 1303145 = 977359) B977359
theorem B910055 : Blo 358757 910055 := bstep (se 1 (by rfl) ⟨682541, by rfl⟩ : syracuseStep 910055 = 1365083) B1365083
theorem B7759871 : Blo 358757 7759871 := bstep (se 1 (by rfl) ⟨5819903, by rfl⟩ : syracuseStep 7759871 = 11639807) B11639807
theorem B813167 : Blo 358757 813167 := bstep (se 1 (by rfl) ⟨609875, by rfl⟩ : syracuseStep 813167 = 1219751) B1219751
theorem B682823 : Blo 358757 682823 := bstep (se 1 (by rfl) ⟨512117, by rfl⟩ : syracuseStep 682823 = 1024235) B1024235
theorem B7039943 : Blo 358757 7039943 := bstep (se 1 (by rfl) ⟨5279957, by rfl⟩ : syracuseStep 7039943 = 10559915) B10559915
theorem B9432895 : Blo 358757 9432895 := bstep (se 1 (by rfl) ⟨7074671, by rfl⟩ : syracuseStep 9432895 = 14149343) B14149343
theorem B360191 : Blo 358757 360191 := bstep (se 1 (by rfl) ⟨270143, by rfl⟩ : syracuseStep 360191 = 540287) B540287
theorem B4693295 : Blo 358757 4693295 := bstep (se 1 (by rfl) ⟨3519971, by rfl⟩ : syracuseStep 4693295 = 7039943) B7039943
theorem B539327 : Blo 358757 539327 := bstep (se 1 (by rfl) ⟨404495, by rfl⟩ : syracuseStep 539327 = 808991) B808991
theorem B868763 : Blo 358757 868763 := bstep (se 1 (by rfl) ⟨651572, by rfl⟩ : syracuseStep 868763 = 1303145) B1303145
theorem B606703 : Blo 358757 606703 := bstep (se 1 (by rfl) ⟨455027, by rfl⟩ : syracuseStep 606703 = 910055) B910055
theorem B542111 : Blo 358757 542111 := bstep (se 1 (by rfl) ⟨406583, by rfl⟩ : syracuseStep 542111 = 813167) B813167
theorem B3459287 : Blo 358757 3459287 := bstep (se 1 (by rfl) ⟨2594465, by rfl⟩ : syracuseStep 3459287 = 5188931) B5188931
theorem B543401 : Blo 358757 543401 := bstep (se 2 (by rfl) ⟨203775, by rfl⟩ : syracuseStep 543401 = 407551) B407551
theorem B1952923 : Blo 358757 1952923 := bstep (se 1 (by rfl) ⟨1464692, by rfl⟩ : syracuseStep 1952923 = 2929385) B2929385
theorem B18733295 : Blo 358757 18733295 := bstep (se 1 (by rfl) ⟨14049971, by rfl⟩ : syracuseStep 18733295 = 28099943) B28099943
theorem B9526139 : Blo 358757 9526139 := bstep (se 1 (by rfl) ⟨7144604, by rfl⟩ : syracuseStep 9526139 = 14289209) B14289209
theorem B647147 : Blo 358757 647147 := bstep (se 1 (by rfl) ⟨485360, by rfl⟩ : syracuseStep 647147 = 970721) B970721
theorem B3302747 : Blo 358757 3302747 := bstep (se 1 (by rfl) ⟨2477060, by rfl⟩ : syracuseStep 3302747 = 4954121) B4954121
theorem B12577193 : Blo 358757 12577193 := bstep (se 2 (by rfl) ⟨4716447, by rfl⟩ : syracuseStep 12577193 = 9432895) B9432895
theorem B5173247 : Blo 358757 5173247 := bstep (se 1 (by rfl) ⟨3879935, by rfl⟩ : syracuseStep 5173247 = 7759871) B7759871
theorem B455215 : Blo 358757 455215 := bstep (se 1 (by rfl) ⟨341411, by rfl⟩ : syracuseStep 455215 = 682823) B682823
theorem B358895 : Blo 358757 358895 := bstep (se 1 (by rfl) ⟨269171, by rfl⟩ : syracuseStep 358895 = 538343) B538343
theorem B361407 : Blo 358757 361407 := bstep (se 1 (by rfl) ⟨271055, by rfl⟩ : syracuseStep 361407 = 542111) B542111
theorem B362267 : Blo 358757 362267 := bstep (se 1 (by rfl) ⟨271700, by rfl⟩ : syracuseStep 362267 = 543401) B543401
theorem B2201831 : Blo 358757 2201831 := bstep (se 1 (by rfl) ⟨1651373, by rfl⟩ : syracuseStep 2201831 = 3302747) B3302747
theorem B3448831 : Blo 358757 3448831 := bstep (se 1 (by rfl) ⟨2586623, by rfl⟩ : syracuseStep 3448831 = 5173247) B5173247
theorem B2603897 : Blo 358757 2603897 := bstep (se 2 (by rfl) ⟨976461, by rfl⟩ : syracuseStep 2603897 = 1952923) B1952923
theorem B3128863 : Blo 358757 3128863 := bstep (se 1 (by rfl) ⟨2346647, by rfl⟩ : syracuseStep 3128863 = 4693295) B4693295
theorem B9224765 : Blo 358757 9224765 := bstep (se 3 (by rfl) ⟨1729643, by rfl⟩ : syracuseStep 9224765 = 3459287) B3459287
theorem B49955453 : Blo 358757 49955453 := bstep (se 3 (by rfl) ⟨9366647, by rfl⟩ : syracuseStep 49955453 = 18733295) B18733295
theorem B606953 : Blo 358757 606953 := bstep (se 2 (by rfl) ⟨227607, by rfl⟩ : syracuseStep 606953 = 455215) B455215
theorem B1725725 : Blo 358757 1725725 := bstep (se 3 (by rfl) ⟨323573, by rfl⟩ : syracuseStep 1725725 = 647147) B647147
theorem B808937 : Blo 358757 808937 := bstep (se 2 (by rfl) ⟨303351, by rfl⟩ : syracuseStep 808937 = 606703) B606703
theorem B2316701 : Blo 358757 2316701 := bstep (se 3 (by rfl) ⟨434381, by rfl⟩ : syracuseStep 2316701 = 868763) B868763
theorem B6350759 : Blo 358757 6350759 := bstep (se 1 (by rfl) ⟨4763069, by rfl⟩ : syracuseStep 6350759 = 9526139) B9526139
theorem B8384795 : Blo 358757 8384795 := bstep (se 1 (by rfl) ⟨6288596, by rfl⟩ : syracuseStep 8384795 = 12577193) B12577193
theorem B359551 : Blo 358757 359551 := bstep (se 1 (by rfl) ⟨269663, by rfl⟩ : syracuseStep 359551 = 539327) B539327
theorem B1150483 : Blo 358757 1150483 := bstep (se 1 (by rfl) ⟨862862, by rfl⟩ : syracuseStep 1150483 = 1725725) B1725725
theorem B1544467 : Blo 358757 1544467 := bstep (se 1 (by rfl) ⟨1158350, by rfl⟩ : syracuseStep 1544467 = 2316701) B2316701
theorem B67741429 : Blo 358757 67741429 := bstep (se 5 (by rfl) ⟨3175379, by rfl⟩ : syracuseStep 67741429 = 6350759) B6350759
theorem B4171817 : Blo 358757 4171817 := bstep (se 2 (by rfl) ⟨1564431, by rfl⟩ : syracuseStep 4171817 = 3128863) B3128863
theorem B4598441 : Blo 358757 4598441 := bstep (se 2 (by rfl) ⟨1724415, by rfl⟩ : syracuseStep 4598441 = 3448831) B3448831
theorem B33303635 : Blo 358757 33303635 := bstep (se 1 (by rfl) ⟨24977726, by rfl⟩ : syracuseStep 33303635 = 49955453) B49955453
theorem B404635 : Blo 358757 404635 := bstep (se 1 (by rfl) ⟨303476, by rfl⟩ : syracuseStep 404635 = 606953) B606953
theorem B539291 : Blo 358757 539291 := bstep (se 1 (by rfl) ⟨404468, by rfl⟩ : syracuseStep 539291 = 808937) B808937
theorem B5589863 : Blo 358757 5589863 := bstep (se 1 (by rfl) ⟨4192397, by rfl⟩ : syracuseStep 5589863 = 8384795) B8384795
theorem B6149843 : Blo 358757 6149843 := bstep (se 1 (by rfl) ⟨4612382, by rfl⟩ : syracuseStep 6149843 = 9224765) B9224765
theorem B1467887 : Blo 358757 1467887 := bstep (se 1 (by rfl) ⟨1100915, by rfl⟩ : syracuseStep 1467887 = 2201831) B2201831
theorem B1735931 : Blo 358757 1735931 := bstep (se 1 (by rfl) ⟨1301948, by rfl⟩ : syracuseStep 1735931 = 2603897) B2603897
theorem B4099895 : Blo 358757 4099895 := bstep (se 1 (by rfl) ⟨3074921, by rfl⟩ : syracuseStep 4099895 = 6149843) B6149843
theorem B4629149 : Blo 358757 4629149 := bstep (se 3 (by rfl) ⟨867965, by rfl⟩ : syracuseStep 4629149 = 1735931) B1735931
theorem B90321905 : Blo 358757 90321905 := bstep (se 2 (by rfl) ⟨33870714, by rfl⟩ : syracuseStep 90321905 = 67741429) B67741429
theorem B3914365 : Blo 358757 3914365 := bstep (se 3 (by rfl) ⟨733943, by rfl⟩ : syracuseStep 3914365 = 1467887) B1467887
theorem B539513 : Blo 358757 539513 := bstep (se 2 (by rfl) ⟨202317, by rfl⟩ : syracuseStep 539513 = 404635) B404635
theorem B3065627 : Blo 358757 3065627 := bstep (se 1 (by rfl) ⟨2299220, by rfl⟩ : syracuseStep 3065627 = 4598441) B4598441
theorem B22202423 : Blo 358757 22202423 := bstep (se 1 (by rfl) ⟨16651817, by rfl⟩ : syracuseStep 22202423 = 33303635) B33303635
theorem B3726575 : Blo 358757 3726575 := bstep (se 1 (by rfl) ⟨2794931, by rfl⟩ : syracuseStep 3726575 = 5589863) B5589863
theorem B1533977 : Blo 358757 1533977 := bstep (se 2 (by rfl) ⟨575241, by rfl⟩ : syracuseStep 1533977 = 1150483) B1150483
theorem B2059289 : Blo 358757 2059289 := bstep (se 2 (by rfl) ⟨772233, by rfl⟩ : syracuseStep 2059289 = 1544467) B1544467
theorem B2781211 : Blo 358757 2781211 := bstep (se 1 (by rfl) ⟨2085908, by rfl⟩ : syracuseStep 2781211 = 4171817) B4171817
theorem B359527 : Blo 358757 359527 := bstep (se 1 (by rfl) ⟨269645, by rfl⟩ : syracuseStep 359527 = 539291) B539291
theorem B3708281 : Blo 358757 3708281 := bstep (se 2 (by rfl) ⟨1390605, by rfl⟩ : syracuseStep 3708281 = 2781211) B2781211
theorem B3086099 : Blo 358757 3086099 := bstep (se 1 (by rfl) ⟨2314574, by rfl⟩ : syracuseStep 3086099 = 4629149) B4629149
theorem B1022651 : Blo 358757 1022651 := bstep (se 1 (by rfl) ⟨766988, by rfl⟩ : syracuseStep 1022651 = 1533977) B1533977
theorem B5219153 : Blo 358757 5219153 := bstep (se 2 (by rfl) ⟨1957182, by rfl⟩ : syracuseStep 5219153 = 3914365) B3914365
theorem B2043751 : Blo 358757 2043751 := bstep (se 1 (by rfl) ⟨1532813, by rfl⟩ : syracuseStep 2043751 = 3065627) B3065627
theorem B2733263 : Blo 358757 2733263 := bstep (se 1 (by rfl) ⟨2049947, by rfl⟩ : syracuseStep 2733263 = 4099895) B4099895
theorem B60214603 : Blo 358757 60214603 := bstep (se 1 (by rfl) ⟨45160952, by rfl⟩ : syracuseStep 60214603 = 90321905) B90321905
theorem B14801615 : Blo 358757 14801615 := bstep (se 1 (by rfl) ⟨11101211, by rfl⟩ : syracuseStep 14801615 = 22202423) B22202423
theorem B2484383 : Blo 358757 2484383 := bstep (se 1 (by rfl) ⟨1863287, by rfl⟩ : syracuseStep 2484383 = 3726575) B3726575
theorem B1372859 : Blo 358757 1372859 := bstep (se 1 (by rfl) ⟨1029644, by rfl⟩ : syracuseStep 1372859 = 2059289) B2059289
theorem B359675 : Blo 358757 359675 := bstep (se 1 (by rfl) ⟨269756, by rfl⟩ : syracuseStep 359675 = 539513) B539513
theorem B80286137 : Blo 358757 80286137 := bstep (se 2 (by rfl) ⟨30107301, by rfl⟩ : syracuseStep 80286137 = 60214603) B60214603
theorem B9867743 : Blo 358757 9867743 := bstep (se 1 (by rfl) ⟨7400807, by rfl⟩ : syracuseStep 9867743 = 14801615) B14801615
theorem B2725001 : Blo 358757 2725001 := bstep (se 2 (by rfl) ⟨1021875, by rfl⟩ : syracuseStep 2725001 = 2043751) B2043751
theorem B6625021 : Blo 358757 6625021 := bstep (se 3 (by rfl) ⟨1242191, by rfl⟩ : syracuseStep 6625021 = 2484383) B2484383
theorem B3479435 : Blo 358757 3479435 := bstep (se 1 (by rfl) ⟨2609576, by rfl⟩ : syracuseStep 3479435 = 5219153) B5219153
theorem B1822175 : Blo 358757 1822175 := bstep (se 1 (by rfl) ⟨1366631, by rfl⟩ : syracuseStep 1822175 = 2733263) B2733263
theorem B9888749 : Blo 358757 9888749 := bstep (se 3 (by rfl) ⟨1854140, by rfl⟩ : syracuseStep 9888749 = 3708281) B3708281
theorem B2057399 : Blo 358757 2057399 := bstep (se 1 (by rfl) ⟨1543049, by rfl⟩ : syracuseStep 2057399 = 3086099) B3086099
theorem B681767 : Blo 358757 681767 := bstep (se 1 (by rfl) ⟨511325, by rfl⟩ : syracuseStep 681767 = 1022651) B1022651
theorem B915239 : Blo 358757 915239 := bstep (se 1 (by rfl) ⟨686429, by rfl⟩ : syracuseStep 915239 = 1372859) B1372859
theorem B1214783 : Blo 358757 1214783 := bstep (se 1 (by rfl) ⟨911087, by rfl⟩ : syracuseStep 1214783 = 1822175) B1822175
theorem B141333781 : Blo 358757 141333781 := bstep (se 6 (by rfl) ⟨3312510, by rfl⟩ : syracuseStep 141333781 = 6625021) B6625021
theorem B6592499 : Blo 358757 6592499 := bstep (se 1 (by rfl) ⟨4944374, by rfl⟩ : syracuseStep 6592499 = 9888749) B9888749
theorem B53524091 : Blo 358757 53524091 := bstep (se 1 (by rfl) ⟨40143068, by rfl⟩ : syracuseStep 53524091 = 80286137) B80286137
theorem B1816667 : Blo 358757 1816667 := bstep (se 1 (by rfl) ⟨1362500, by rfl⟩ : syracuseStep 1816667 = 2725001) B2725001
theorem B610159 : Blo 358757 610159 := bstep (se 1 (by rfl) ⟨457619, by rfl⟩ : syracuseStep 610159 = 915239) B915239
theorem B6578495 : Blo 358757 6578495 := bstep (se 1 (by rfl) ⟨4933871, by rfl⟩ : syracuseStep 6578495 = 9867743) B9867743
theorem B2319623 : Blo 358757 2319623 := bstep (se 1 (by rfl) ⟨1739717, by rfl⟩ : syracuseStep 2319623 = 3479435) B3479435
theorem B1371599 : Blo 358757 1371599 := bstep (se 1 (by rfl) ⟨1028699, by rfl⟩ : syracuseStep 1371599 = 2057399) B2057399
theorem B454511 : Blo 358757 454511 := bstep (se 1 (by rfl) ⟨340883, by rfl⟩ : syracuseStep 454511 = 681767) B681767
theorem B4394999 : Blo 358757 4394999 := bstep (se 1 (by rfl) ⟨3296249, by rfl⟩ : syracuseStep 4394999 = 6592499) B6592499
theorem B1546415 : Blo 358757 1546415 := bstep (se 1 (by rfl) ⟨1159811, by rfl⟩ : syracuseStep 1546415 = 2319623) B2319623
theorem B809855 : Blo 358757 809855 := bstep (se 1 (by rfl) ⟨607391, by rfl⟩ : syracuseStep 809855 = 1214783) B1214783
theorem B813545 : Blo 358757 813545 := bstep (se 2 (by rfl) ⟨305079, by rfl⟩ : syracuseStep 813545 = 610159) B610159
theorem B4385663 : Blo 358757 4385663 := bstep (se 1 (by rfl) ⟨3289247, by rfl⟩ : syracuseStep 4385663 = 6578495) B6578495
theorem B188445041 : Blo 358757 188445041 := bstep (se 2 (by rfl) ⟨70666890, by rfl⟩ : syracuseStep 188445041 = 141333781) B141333781
theorem B914399 : Blo 358757 914399 := bstep (se 1 (by rfl) ⟨685799, by rfl⟩ : syracuseStep 914399 = 1371599) B1371599
theorem B35682727 : Blo 358757 35682727 := bstep (se 1 (by rfl) ⟨26762045, by rfl⟩ : syracuseStep 35682727 = 53524091) B53524091
theorem B1211111 : Blo 358757 1211111 := bstep (se 1 (by rfl) ⟨908333, by rfl⟩ : syracuseStep 1211111 = 1816667) B1816667
theorem B1212029 : Blo 358757 1212029 := bstep (se 3 (by rfl) ⟨227255, by rfl⟩ : syracuseStep 1212029 = 454511) B454511
theorem B2923775 : Blo 358757 2923775 := bstep (se 1 (by rfl) ⟨2192831, by rfl⟩ : syracuseStep 2923775 = 4385663) B4385663
theorem B1030943 : Blo 358757 1030943 := bstep (se 1 (by rfl) ⟨773207, by rfl⟩ : syracuseStep 1030943 = 1546415) B1546415
theorem B539903 : Blo 358757 539903 := bstep (se 1 (by rfl) ⟨404927, by rfl⟩ : syracuseStep 539903 = 809855) B809855
theorem B542363 : Blo 358757 542363 := bstep (se 1 (by rfl) ⟨406772, by rfl⟩ : syracuseStep 542363 = 813545) B813545
theorem B609599 : Blo 358757 609599 := bstep (se 1 (by rfl) ⟨457199, by rfl⟩ : syracuseStep 609599 = 914399) B914399
theorem B807407 : Blo 358757 807407 := bstep (se 1 (by rfl) ⟨605555, by rfl⟩ : syracuseStep 807407 = 1211111) B1211111
theorem B808019 : Blo 358757 808019 := bstep (se 1 (by rfl) ⟨606014, by rfl⟩ : syracuseStep 808019 = 1212029) B1212029
theorem B11719997 : Blo 358757 11719997 := bstep (se 3 (by rfl) ⟨2197499, by rfl⟩ : syracuseStep 11719997 = 4394999) B4394999
theorem B125630027 : Blo 358757 125630027 := bstep (se 1 (by rfl) ⟨94222520, by rfl⟩ : syracuseStep 125630027 = 188445041) B188445041
theorem B47576969 : Blo 358757 47576969 := bstep (se 2 (by rfl) ⟨17841363, by rfl⟩ : syracuseStep 47576969 = 35682727) B35682727
theorem B361575 : Blo 358757 361575 := bstep (se 1 (by rfl) ⟨271181, by rfl⟩ : syracuseStep 361575 = 542363) B542363
theorem B406399 : Blo 358757 406399 := bstep (se 1 (by rfl) ⟨304799, by rfl⟩ : syracuseStep 406399 = 609599) B609599
theorem B538271 : Blo 358757 538271 := bstep (se 1 (by rfl) ⟨403703, by rfl⟩ : syracuseStep 538271 = 807407) B807407
theorem B538679 : Blo 358757 538679 := bstep (se 1 (by rfl) ⟨404009, by rfl⟩ : syracuseStep 538679 = 808019) B808019
theorem B7813331 : Blo 358757 7813331 := bstep (se 1 (by rfl) ⟨5859998, by rfl⟩ : syracuseStep 7813331 = 11719997) B11719997
theorem B1949183 : Blo 358757 1949183 := bstep (se 1 (by rfl) ⟨1461887, by rfl⟩ : syracuseStep 1949183 = 2923775) B2923775
theorem B83753351 : Blo 358757 83753351 := bstep (se 1 (by rfl) ⟨62815013, by rfl⟩ : syracuseStep 83753351 = 125630027) B125630027
theorem B31717979 : Blo 358757 31717979 := bstep (se 1 (by rfl) ⟨23788484, by rfl⟩ : syracuseStep 31717979 = 47576969) B47576969
theorem B687295 : Blo 358757 687295 := bstep (se 1 (by rfl) ⟨515471, by rfl⟩ : syracuseStep 687295 = 1030943) B1030943
theorem B359935 : Blo 358757 359935 := bstep (se 1 (by rfl) ⟨269951, by rfl⟩ : syracuseStep 359935 = 539903) B539903
theorem B21145319 : Blo 358757 21145319 := bstep (se 1 (by rfl) ⟨15858989, by rfl⟩ : syracuseStep 21145319 = 31717979) B31717979
theorem B541865 : Blo 358757 541865 := bstep (se 2 (by rfl) ⟨203199, by rfl⟩ : syracuseStep 541865 = 406399) B406399
theorem B1299455 : Blo 358757 1299455 := bstep (se 1 (by rfl) ⟨974591, by rfl⟩ : syracuseStep 1299455 = 1949183) B1949183
theorem B358847 : Blo 358757 358847 := bstep (se 1 (by rfl) ⟨269135, by rfl⟩ : syracuseStep 358847 = 538271) B538271
theorem B359119 : Blo 358757 359119 := bstep (se 1 (by rfl) ⟨269339, by rfl⟩ : syracuseStep 359119 = 538679) B538679
theorem B5208887 : Blo 358757 5208887 := bstep (se 1 (by rfl) ⟨3906665, by rfl⟩ : syracuseStep 5208887 = 7813331) B7813331
theorem B916393 : Blo 358757 916393 := bstep (se 2 (by rfl) ⟨343647, by rfl⟩ : syracuseStep 916393 = 687295) B687295
theorem B55835567 : Blo 358757 55835567 := bstep (se 1 (by rfl) ⟨41876675, by rfl⟩ : syracuseStep 55835567 = 83753351) B83753351
theorem B361243 : Blo 358757 361243 := bstep (se 1 (by rfl) ⟨270932, by rfl⟩ : syracuseStep 361243 = 541865) B541865
theorem B14096879 : Blo 358757 14096879 := bstep (se 1 (by rfl) ⟨10572659, by rfl⟩ : syracuseStep 14096879 = 21145319) B21145319
theorem B1221857 : Blo 358757 1221857 := bstep (se 2 (by rfl) ⟨458196, by rfl⟩ : syracuseStep 1221857 = 916393) B916393
theorem B866303 : Blo 358757 866303 := bstep (se 1 (by rfl) ⟨649727, by rfl⟩ : syracuseStep 866303 = 1299455) B1299455
theorem B3472591 : Blo 358757 3472591 := bstep (se 1 (by rfl) ⟨2604443, by rfl⟩ : syracuseStep 3472591 = 5208887) B5208887
theorem B37223711 : Blo 358757 37223711 := bstep (se 1 (by rfl) ⟨27917783, by rfl⟩ : syracuseStep 37223711 = 55835567) B55835567
theorem B4630121 : Blo 358757 4630121 := bstep (se 2 (by rfl) ⟨1736295, by rfl⟩ : syracuseStep 4630121 = 3472591) B3472591
theorem B24815807 : Blo 358757 24815807 := bstep (se 1 (by rfl) ⟨18611855, by rfl⟩ : syracuseStep 24815807 = 37223711) B37223711
theorem B577535 : Blo 358757 577535 := bstep (se 1 (by rfl) ⟨433151, by rfl⟩ : syracuseStep 577535 = 866303) B866303
theorem B9397919 : Blo 358757 9397919 := bstep (se 1 (by rfl) ⟨7048439, by rfl⟩ : syracuseStep 9397919 = 14096879) B14096879
theorem B814571 : Blo 358757 814571 := bstep (se 1 (by rfl) ⟨610928, by rfl⟩ : syracuseStep 814571 = 1221857) B1221857
theorem B3086747 : Blo 358757 3086747 := bstep (se 1 (by rfl) ⟨2315060, by rfl⟩ : syracuseStep 3086747 = 4630121) B4630121
theorem B6265279 : Blo 358757 6265279 := bstep (se 1 (by rfl) ⟨4698959, by rfl⟩ : syracuseStep 6265279 = 9397919) B9397919
theorem B543047 : Blo 358757 543047 := bstep (se 1 (by rfl) ⟨407285, by rfl⟩ : syracuseStep 543047 = 814571) B814571
theorem B16543871 : Blo 358757 16543871 := bstep (se 1 (by rfl) ⟨12407903, by rfl⟩ : syracuseStep 16543871 = 24815807) B24815807
theorem B1540093 : Blo 358757 1540093 := bstep (se 3 (by rfl) ⟨288767, by rfl⟩ : syracuseStep 1540093 = 577535) B577535
theorem B362031 : Blo 358757 362031 := bstep (se 1 (by rfl) ⟨271523, by rfl⟩ : syracuseStep 362031 = 543047) B543047
theorem B11029247 : Blo 358757 11029247 := bstep (se 1 (by rfl) ⟨8271935, by rfl⟩ : syracuseStep 11029247 = 16543871) B16543871
theorem B2053457 : Blo 358757 2053457 := bstep (se 2 (by rfl) ⟨770046, by rfl⟩ : syracuseStep 2053457 = 1540093) B1540093
theorem B2057831 : Blo 358757 2057831 := bstep (se 1 (by rfl) ⟨1543373, by rfl⟩ : syracuseStep 2057831 = 3086747) B3086747
theorem B8353705 : Blo 358757 8353705 := bstep (se 2 (by rfl) ⟨3132639, by rfl⟩ : syracuseStep 8353705 = 6265279) B6265279
theorem B7352831 : Blo 358757 7352831 := bstep (se 1 (by rfl) ⟨5514623, by rfl⟩ : syracuseStep 7352831 = 11029247) B11029247
theorem B1368971 : Blo 358757 1368971 := bstep (se 1 (by rfl) ⟨1026728, by rfl⟩ : syracuseStep 1368971 = 2053457) B2053457
theorem B1371887 : Blo 358757 1371887 := bstep (se 1 (by rfl) ⟨1028915, by rfl⟩ : syracuseStep 1371887 = 2057831) B2057831
theorem B11138273 : Blo 358757 11138273 := bstep (se 2 (by rfl) ⟨4176852, by rfl⟩ : syracuseStep 11138273 = 8353705) B8353705
theorem B4901887 : Blo 358757 4901887 := bstep (se 1 (by rfl) ⟨3676415, by rfl⟩ : syracuseStep 4901887 = 7352831) B7352831
theorem B7425515 : Blo 358757 7425515 := bstep (se 1 (by rfl) ⟨5569136, by rfl⟩ : syracuseStep 7425515 = 11138273) B11138273
theorem B912647 : Blo 358757 912647 := bstep (se 1 (by rfl) ⟨684485, by rfl⟩ : syracuseStep 912647 = 1368971) B1368971
theorem B914591 : Blo 358757 914591 := bstep (se 1 (by rfl) ⟨685943, by rfl⟩ : syracuseStep 914591 = 1371887) B1371887
theorem B4950343 : Blo 358757 4950343 := bstep (se 1 (by rfl) ⟨3712757, by rfl⟩ : syracuseStep 4950343 = 7425515) B7425515
theorem B6535849 : Blo 358757 6535849 := bstep (se 2 (by rfl) ⟨2450943, by rfl⟩ : syracuseStep 6535849 = 4901887) B4901887
theorem B608431 : Blo 358757 608431 := bstep (se 1 (by rfl) ⟨456323, by rfl⟩ : syracuseStep 608431 = 912647) B912647
theorem B609727 : Blo 358757 609727 := bstep (se 1 (by rfl) ⟨457295, by rfl⟩ : syracuseStep 609727 = 914591) B914591
theorem B6600457 : Blo 358757 6600457 := bstep (se 2 (by rfl) ⟨2475171, by rfl⟩ : syracuseStep 6600457 = 4950343) B4950343
theorem B811241 : Blo 358757 811241 := bstep (se 2 (by rfl) ⟨304215, by rfl⟩ : syracuseStep 811241 = 608431) B608431
theorem B812969 : Blo 358757 812969 := bstep (se 2 (by rfl) ⟨304863, by rfl⟩ : syracuseStep 812969 = 609727) B609727
theorem B8714465 : Blo 358757 8714465 := bstep (se 2 (by rfl) ⟨3267924, by rfl⟩ : syracuseStep 8714465 = 6535849) B6535849
theorem B5809643 : Blo 358757 5809643 := bstep (se 1 (by rfl) ⟨4357232, by rfl⟩ : syracuseStep 5809643 = 8714465) B8714465
theorem B540827 : Blo 358757 540827 := bstep (se 1 (by rfl) ⟨405620, by rfl⟩ : syracuseStep 540827 = 811241) B811241
theorem B541979 : Blo 358757 541979 := bstep (se 1 (by rfl) ⟨406484, by rfl⟩ : syracuseStep 541979 = 812969) B812969
theorem B8800609 : Blo 358757 8800609 := bstep (se 2 (by rfl) ⟨3300228, by rfl⟩ : syracuseStep 8800609 = 6600457) B6600457
theorem B360551 : Blo 358757 360551 := bstep (se 1 (by rfl) ⟨270413, by rfl⟩ : syracuseStep 360551 = 540827) B540827
theorem B361319 : Blo 358757 361319 := bstep (se 1 (by rfl) ⟨270989, by rfl⟩ : syracuseStep 361319 = 541979) B541979
theorem B11734145 : Blo 358757 11734145 := bstep (se 2 (by rfl) ⟨4400304, by rfl⟩ : syracuseStep 11734145 = 8800609) B8800609
theorem B3873095 : Blo 358757 3873095 := bstep (se 1 (by rfl) ⟨2904821, by rfl⟩ : syracuseStep 3873095 = 5809643) B5809643
theorem B7822763 : Blo 358757 7822763 := bstep (se 1 (by rfl) ⟨5867072, by rfl⟩ : syracuseStep 7822763 = 11734145) B11734145
theorem B2582063 : Blo 358757 2582063 := bstep (se 1 (by rfl) ⟨1936547, by rfl⟩ : syracuseStep 2582063 = 3873095) B3873095
theorem B5215175 : Blo 358757 5215175 := bstep (se 1 (by rfl) ⟨3911381, by rfl⟩ : syracuseStep 5215175 = 7822763) B7822763
theorem B1721375 : Blo 358757 1721375 := bstep (se 1 (by rfl) ⟨1291031, by rfl⟩ : syracuseStep 1721375 = 2582063) B2582063
theorem B1147583 : Blo 358757 1147583 := bstep (se 1 (by rfl) ⟨860687, by rfl⟩ : syracuseStep 1147583 = 1721375) B1721375
theorem B3476783 : Blo 358757 3476783 := bstep (se 1 (by rfl) ⟨2607587, by rfl⟩ : syracuseStep 3476783 = 5215175) B5215175
theorem B765055 : Blo 358757 765055 := bstep (se 1 (by rfl) ⟨573791, by rfl⟩ : syracuseStep 765055 = 1147583) B1147583
theorem B2317855 : Blo 358757 2317855 := bstep (se 1 (by rfl) ⟨1738391, by rfl⟩ : syracuseStep 2317855 = 3476783) B3476783
theorem B3090473 : Blo 358757 3090473 := bstep (se 2 (by rfl) ⟨1158927, by rfl⟩ : syracuseStep 3090473 = 2317855) B2317855
theorem B4080293 : Blo 358757 4080293 := bstep (se 4 (by rfl) ⟨382527, by rfl⟩ : syracuseStep 4080293 = 765055) B765055
theorem B2720195 : Blo 358757 2720195 := bstep (se 1 (by rfl) ⟨2040146, by rfl⟩ : syracuseStep 2720195 = 4080293) B4080293
theorem B2060315 : Blo 358757 2060315 := bstep (se 1 (by rfl) ⟨1545236, by rfl⟩ : syracuseStep 2060315 = 3090473) B3090473
theorem B1813463 : Blo 358757 1813463 := bstep (se 1 (by rfl) ⟨1360097, by rfl⟩ : syracuseStep 1813463 = 2720195) B2720195
theorem B1373543 : Blo 358757 1373543 := bstep (se 1 (by rfl) ⟨1030157, by rfl⟩ : syracuseStep 1373543 = 2060315) B2060315
theorem B1208975 : Blo 358757 1208975 := bstep (se 1 (by rfl) ⟨906731, by rfl⟩ : syracuseStep 1208975 = 1813463) B1813463
theorem B915695 : Blo 358757 915695 := bstep (se 1 (by rfl) ⟨686771, by rfl⟩ : syracuseStep 915695 = 1373543) B1373543
theorem B12895733 : Blo 358757 12895733 := bstep (se 5 (by rfl) ⟨604487, by rfl⟩ : syracuseStep 12895733 = 1208975) B1208975
theorem B610463 : Blo 358757 610463 := bstep (se 1 (by rfl) ⟨457847, by rfl⟩ : syracuseStep 610463 = 915695) B915695
theorem B406975 : Blo 358757 406975 := bstep (se 1 (by rfl) ⟨305231, by rfl⟩ : syracuseStep 406975 = 610463) B610463
theorem B34388621 : Blo 358757 34388621 := bstep (se 3 (by rfl) ⟨6447866, by rfl⟩ : syracuseStep 34388621 = 12895733) B12895733
theorem B542633 : Blo 358757 542633 := bstep (se 2 (by rfl) ⟨203487, by rfl⟩ : syracuseStep 542633 = 406975) B406975
theorem B22925747 : Blo 358757 22925747 := bstep (se 1 (by rfl) ⟨17194310, by rfl⟩ : syracuseStep 22925747 = 34388621) B34388621
theorem B361755 : Blo 358757 361755 := bstep (se 1 (by rfl) ⟨271316, by rfl⟩ : syracuseStep 361755 = 542633) B542633
theorem B15283831 : Blo 358757 15283831 := bstep (se 1 (by rfl) ⟨11462873, by rfl⟩ : syracuseStep 15283831 = 22925747) B22925747
theorem B20378441 : Blo 358757 20378441 := bstep (se 2 (by rfl) ⟨7641915, by rfl⟩ : syracuseStep 20378441 = 15283831) B15283831
theorem B13585627 : Blo 358757 13585627 := bstep (se 1 (by rfl) ⟨10189220, by rfl⟩ : syracuseStep 13585627 = 20378441) B20378441
theorem B72456677 : Blo 358757 72456677 := bstep (se 4 (by rfl) ⟨6792813, by rfl⟩ : syracuseStep 72456677 = 13585627) B13585627
theorem B48304451 : Blo 358757 48304451 := bstep (se 1 (by rfl) ⟨36228338, by rfl⟩ : syracuseStep 48304451 = 72456677) B72456677
theorem B32202967 : Blo 358757 32202967 := bstep (se 1 (by rfl) ⟨24152225, by rfl⟩ : syracuseStep 32202967 = 48304451) B48304451
theorem B42937289 : Blo 358757 42937289 := bstep (se 2 (by rfl) ⟨16101483, by rfl⟩ : syracuseStep 42937289 = 32202967) B32202967
theorem B28624859 : Blo 358757 28624859 := bstep (se 1 (by rfl) ⟨21468644, by rfl⟩ : syracuseStep 28624859 = 42937289) B42937289
theorem B19083239 : Blo 358757 19083239 := bstep (se 1 (by rfl) ⟨14312429, by rfl⟩ : syracuseStep 19083239 = 28624859) B28624859
theorem B12722159 : Blo 358757 12722159 := bstep (se 1 (by rfl) ⟨9541619, by rfl⟩ : syracuseStep 12722159 = 19083239) B19083239
theorem B8481439 : Blo 358757 8481439 := bstep (se 1 (by rfl) ⟨6361079, by rfl⟩ : syracuseStep 8481439 = 12722159) B12722159
theorem B11308585 : Blo 358757 11308585 := bstep (se 2 (by rfl) ⟨4240719, by rfl⟩ : syracuseStep 11308585 = 8481439) B8481439
theorem B15078113 : Blo 358757 15078113 := bstep (se 2 (by rfl) ⟨5654292, by rfl⟩ : syracuseStep 15078113 = 11308585) B11308585
theorem B10052075 : Blo 358757 10052075 := bstep (se 1 (by rfl) ⟨7539056, by rfl⟩ : syracuseStep 10052075 = 15078113) B15078113
theorem B6701383 : Blo 358757 6701383 := bstep (se 1 (by rfl) ⟨5026037, by rfl⟩ : syracuseStep 6701383 = 10052075) B10052075
theorem B8935177 : Blo 358757 8935177 := bstep (se 2 (by rfl) ⟨3350691, by rfl⟩ : syracuseStep 8935177 = 6701383) B6701383
theorem B11913569 : Blo 358757 11913569 := bstep (se 2 (by rfl) ⟨4467588, by rfl⟩ : syracuseStep 11913569 = 8935177) B8935177
theorem B7942379 : Blo 358757 7942379 := bstep (se 1 (by rfl) ⟨5956784, by rfl⟩ : syracuseStep 7942379 = 11913569) B11913569
theorem B84718709 : Blo 358757 84718709 := bstep (se 5 (by rfl) ⟨3971189, by rfl⟩ : syracuseStep 84718709 = 7942379) B7942379
theorem B56479139 : Blo 358757 56479139 := bstep (se 1 (by rfl) ⟨42359354, by rfl⟩ : syracuseStep 56479139 = 84718709) B84718709
theorem B37652759 : Blo 358757 37652759 := bstep (se 1 (by rfl) ⟨28239569, by rfl⟩ : syracuseStep 37652759 = 56479139) B56479139
theorem B25101839 : Blo 358757 25101839 := bstep (se 1 (by rfl) ⟨18826379, by rfl⟩ : syracuseStep 25101839 = 37652759) B37652759
theorem B16734559 : Blo 358757 16734559 := bstep (se 1 (by rfl) ⟨12550919, by rfl⟩ : syracuseStep 16734559 = 25101839) B25101839
theorem B22312745 : Blo 358757 22312745 := bstep (se 2 (by rfl) ⟨8367279, by rfl⟩ : syracuseStep 22312745 = 16734559) B16734559
theorem B14875163 : Blo 358757 14875163 := bstep (se 1 (by rfl) ⟨11156372, by rfl⟩ : syracuseStep 14875163 = 22312745) B22312745
theorem B9916775 : Blo 358757 9916775 := bstep (se 1 (by rfl) ⟨7437581, by rfl⟩ : syracuseStep 9916775 = 14875163) B14875163
theorem B6611183 : Blo 358757 6611183 := bstep (se 1 (by rfl) ⟨4958387, by rfl⟩ : syracuseStep 6611183 = 9916775) B9916775
theorem B4407455 : Blo 358757 4407455 := bstep (se 1 (by rfl) ⟨3305591, by rfl⟩ : syracuseStep 4407455 = 6611183) B6611183
theorem B2938303 : Blo 358757 2938303 := bstep (se 1 (by rfl) ⟨2203727, by rfl⟩ : syracuseStep 2938303 = 4407455) B4407455
theorem B3917737 : Blo 358757 3917737 := bstep (se 2 (by rfl) ⟨1469151, by rfl⟩ : syracuseStep 3917737 = 2938303) B2938303
theorem B5223649 : Blo 358757 5223649 := bstep (se 2 (by rfl) ⟨1958868, by rfl⟩ : syracuseStep 5223649 = 3917737) B3917737
theorem B6964865 : Blo 358757 6964865 := bstep (se 2 (by rfl) ⟨2611824, by rfl⟩ : syracuseStep 6964865 = 5223649) B5223649
theorem B4643243 : Blo 358757 4643243 := bstep (se 1 (by rfl) ⟨3482432, by rfl⟩ : syracuseStep 4643243 = 6964865) B6964865
theorem B3095495 : Blo 358757 3095495 := bstep (se 1 (by rfl) ⟨2321621, by rfl⟩ : syracuseStep 3095495 = 4643243) B4643243
theorem B2063663 : Blo 358757 2063663 := bstep (se 1 (by rfl) ⟨1547747, by rfl⟩ : syracuseStep 2063663 = 3095495) B3095495
theorem B1375775 : Blo 358757 1375775 := bstep (se 1 (by rfl) ⟨1031831, by rfl⟩ : syracuseStep 1375775 = 2063663) B2063663
theorem B917183 : Blo 358757 917183 := bstep (se 1 (by rfl) ⟨687887, by rfl⟩ : syracuseStep 917183 = 1375775) B1375775
theorem B611455 : Blo 358757 611455 := bstep (se 1 (by rfl) ⟨458591, by rfl⟩ : syracuseStep 611455 = 917183) B917183
theorem B815273 : Blo 358757 815273 := bstep (se 2 (by rfl) ⟨305727, by rfl⟩ : syracuseStep 815273 = 611455) B611455
theorem B543515 : Blo 358757 543515 := bstep (se 1 (by rfl) ⟨407636, by rfl⟩ : syracuseStep 543515 = 815273) B815273
theorem B362343 : Blo 358757 362343 := bstep (se 1 (by rfl) ⟨271757, by rfl⟩ : syracuseStep 362343 = 543515) B543515

theorem C0 (j : ℕ) (h1 : 89689 ≤ j) (h2 : j ≤ 90388) : Blo 358757 (4 * j + 3) := by
  interval_cases j
  · exact B358759
  · exact B358763
  · exact B358767
  · exact B358771
  · exact B358775
  · exact B358779
  · exact B358783
  · exact B358787
  · exact B358791
  · exact B358795
  · exact B358799
  · exact B358803
  · exact B358807
  · exact B358811
  · exact B358815
  · exact B358819
  · exact B358823
  · exact B358827
  · exact B358831
  · exact B358835
  · exact B358839
  · exact B358843
  · exact B358847
  · exact B358851
  · exact B358855
  · exact B358859
  · exact B358863
  · exact B358867
  · exact B358871
  · exact B358875
  · exact B358879
  · exact B358883
  · exact B358887
  · exact B358891
  · exact B358895
  · exact B358899
  · exact B358903
  · exact B358907
  · exact B358911
  · exact B358915
  · exact B358919
  · exact B358923
  · exact B358927
  · exact B358931
  · exact B358935
  · exact B358939
  · exact B358943
  · exact B358947
  · exact B358951
  · exact B358955
  · exact B358959
  · exact B358963
  · exact B358967
  · exact B358971
  · exact B358975
  · exact B358979
  · exact B358983
  · exact B358987
  · exact B358991
  · exact B358995
  · exact B358999
  · exact B359003
  · exact B359007
  · exact B359011
  · exact B359015
  · exact B359019
  · exact B359023
  · exact B359027
  · exact B359031
  · exact B359035
  · exact B359039
  · exact B359043
  · exact B359047
  · exact B359051
  · exact B359055
  · exact B359059
  · exact B359063
  · exact B359067
  · exact B359071
  · exact B359075
  · exact B359079
  · exact B359083
  · exact B359087
  · exact B359091
  · exact B359095
  · exact B359099
  · exact B359103
  · exact B359107
  · exact B359111
  · exact B359115
  · exact B359119
  · exact B359123
  · exact B359127
  · exact B359131
  · exact B359135
  · exact B359139
  · exact B359143
  · exact B359147
  · exact B359151
  · exact B359155
  · exact B359159
  · exact B359163
  · exact B359167
  · exact B359171
  · exact B359175
  · exact B359179
  · exact B359183
  · exact B359187
  · exact B359191
  · exact B359195
  · exact B359199
  · exact B359203
  · exact B359207
  · exact B359211
  · exact B359215
  · exact B359219
  · exact B359223
  · exact B359227
  · exact B359231
  · exact B359235
  · exact B359239
  · exact B359243
  · exact B359247
  · exact B359251
  · exact B359255
  · exact B359259
  · exact B359263
  · exact B359267
  · exact B359271
  · exact B359275
  · exact B359279
  · exact B359283
  · exact B359287
  · exact B359291
  · exact B359295
  · exact B359299
  · exact B359303
  · exact B359307
  · exact B359311
  · exact B359315
  · exact B359319
  · exact B359323
  · exact B359327
  · exact B359331
  · exact B359335
  · exact B359339
  · exact B359343
  · exact B359347
  · exact B359351
  · exact B359355
  · exact B359359
  · exact B359363
  · exact B359367
  · exact B359371
  · exact B359375
  · exact B359379
  · exact B359383
  · exact B359387
  · exact B359391
  · exact B359395
  · exact B359399
  · exact B359403
  · exact B359407
  · exact B359411
  · exact B359415
  · exact B359419
  · exact B359423
  · exact B359427
  · exact B359431
  · exact B359435
  · exact B359439
  · exact B359443
  · exact B359447
  · exact B359451
  · exact B359455
  · exact B359459
  · exact B359463
  · exact B359467
  · exact B359471
  · exact B359475
  · exact B359479
  · exact B359483
  · exact B359487
  · exact B359491
  · exact B359495
  · exact B359499
  · exact B359503
  · exact B359507
  · exact B359511
  · exact B359515
  · exact B359519
  · exact B359523
  · exact B359527
  · exact B359531
  · exact B359535
  · exact B359539
  · exact B359543
  · exact B359547
  · exact B359551
  · exact B359555
  · exact B359559
  · exact B359563
  · exact B359567
  · exact B359571
  · exact B359575
  · exact B359579
  · exact B359583
  · exact B359587
  · exact B359591
  · exact B359595
  · exact B359599
  · exact B359603
  · exact B359607
  · exact B359611
  · exact B359615
  · exact B359619
  · exact B359623
  · exact B359627
  · exact B359631
  · exact B359635
  · exact B359639
  · exact B359643
  · exact B359647
  · exact B359651
  · exact B359655
  · exact B359659
  · exact B359663
  · exact B359667
  · exact B359671
  · exact B359675
  · exact B359679
  · exact B359683
  · exact B359687
  · exact B359691
  · exact B359695
  · exact B359699
  · exact B359703
  · exact B359707
  · exact B359711
  · exact B359715
  · exact B359719
  · exact B359723
  · exact B359727
  · exact B359731
  · exact B359735
  · exact B359739
  · exact B359743
  · exact B359747
  · exact B359751
  · exact B359755
  · exact B359759
  · exact B359763
  · exact B359767
  · exact B359771
  · exact B359775
  · exact B359779
  · exact B359783
  · exact B359787
  · exact B359791
  · exact B359795
  · exact B359799
  · exact B359803
  · exact B359807
  · exact B359811
  · exact B359815
  · exact B359819
  · exact B359823
  · exact B359827
  · exact B359831
  · exact B359835
  · exact B359839
  · exact B359843
  · exact B359847
  · exact B359851
  · exact B359855
  · exact B359859
  · exact B359863
  · exact B359867
  · exact B359871
  · exact B359875
  · exact B359879
  · exact B359883
  · exact B359887
  · exact B359891
  · exact B359895
  · exact B359899
  · exact B359903
  · exact B359907
  · exact B359911
  · exact B359915
  · exact B359919
  · exact B359923
  · exact B359927
  · exact B359931
  · exact B359935
  · exact B359939
  · exact B359943
  · exact B359947
  · exact B359951
  · exact B359955
  · exact B359959
  · exact B359963
  · exact B359967
  · exact B359971
  · exact B359975
  · exact B359979
  · exact B359983
  · exact B359987
  · exact B359991
  · exact B359995
  · exact B359999
  · exact B360003
  · exact B360007
  · exact B360011
  · exact B360015
  · exact B360019
  · exact B360023
  · exact B360027
  · exact B360031
  · exact B360035
  · exact B360039
  · exact B360043
  · exact B360047
  · exact B360051
  · exact B360055
  · exact B360059
  · exact B360063
  · exact B360067
  · exact B360071
  · exact B360075
  · exact B360079
  · exact B360083
  · exact B360087
  · exact B360091
  · exact B360095
  · exact B360099
  · exact B360103
  · exact B360107
  · exact B360111
  · exact B360115
  · exact B360119
  · exact B360123
  · exact B360127
  · exact B360131
  · exact B360135
  · exact B360139
  · exact B360143
  · exact B360147
  · exact B360151
  · exact B360155
  · exact B360159
  · exact B360163
  · exact B360167
  · exact B360171
  · exact B360175
  · exact B360179
  · exact B360183
  · exact B360187
  · exact B360191
  · exact B360195
  · exact B360199
  · exact B360203
  · exact B360207
  · exact B360211
  · exact B360215
  · exact B360219
  · exact B360223
  · exact B360227
  · exact B360231
  · exact B360235
  · exact B360239
  · exact B360243
  · exact B360247
  · exact B360251
  · exact B360255
  · exact B360259
  · exact B360263
  · exact B360267
  · exact B360271
  · exact B360275
  · exact B360279
  · exact B360283
  · exact B360287
  · exact B360291
  · exact B360295
  · exact B360299
  · exact B360303
  · exact B360307
  · exact B360311
  · exact B360315
  · exact B360319
  · exact B360323
  · exact B360327
  · exact B360331
  · exact B360335
  · exact B360339
  · exact B360343
  · exact B360347
  · exact B360351
  · exact B360355
  · exact B360359
  · exact B360363
  · exact B360367
  · exact B360371
  · exact B360375
  · exact B360379
  · exact B360383
  · exact B360387
  · exact B360391
  · exact B360395
  · exact B360399
  · exact B360403
  · exact B360407
  · exact B360411
  · exact B360415
  · exact B360419
  · exact B360423
  · exact B360427
  · exact B360431
  · exact B360435
  · exact B360439
  · exact B360443
  · exact B360447
  · exact B360451
  · exact B360455
  · exact B360459
  · exact B360463
  · exact B360467
  · exact B360471
  · exact B360475
  · exact B360479
  · exact B360483
  · exact B360487
  · exact B360491
  · exact B360495
  · exact B360499
  · exact B360503
  · exact B360507
  · exact B360511
  · exact B360515
  · exact B360519
  · exact B360523
  · exact B360527
  · exact B360531
  · exact B360535
  · exact B360539
  · exact B360543
  · exact B360547
  · exact B360551
  · exact B360555
  · exact B360559
  · exact B360563
  · exact B360567
  · exact B360571
  · exact B360575
  · exact B360579
  · exact B360583
  · exact B360587
  · exact B360591
  · exact B360595
  · exact B360599
  · exact B360603
  · exact B360607
  · exact B360611
  · exact B360615
  · exact B360619
  · exact B360623
  · exact B360627
  · exact B360631
  · exact B360635
  · exact B360639
  · exact B360643
  · exact B360647
  · exact B360651
  · exact B360655
  · exact B360659
  · exact B360663
  · exact B360667
  · exact B360671
  · exact B360675
  · exact B360679
  · exact B360683
  · exact B360687
  · exact B360691
  · exact B360695
  · exact B360699
  · exact B360703
  · exact B360707
  · exact B360711
  · exact B360715
  · exact B360719
  · exact B360723
  · exact B360727
  · exact B360731
  · exact B360735
  · exact B360739
  · exact B360743
  · exact B360747
  · exact B360751
  · exact B360755
  · exact B360759
  · exact B360763
  · exact B360767
  · exact B360771
  · exact B360775
  · exact B360779
  · exact B360783
  · exact B360787
  · exact B360791
  · exact B360795
  · exact B360799
  · exact B360803
  · exact B360807
  · exact B360811
  · exact B360815
  · exact B360819
  · exact B360823
  · exact B360827
  · exact B360831
  · exact B360835
  · exact B360839
  · exact B360843
  · exact B360847
  · exact B360851
  · exact B360855
  · exact B360859
  · exact B360863
  · exact B360867
  · exact B360871
  · exact B360875
  · exact B360879
  · exact B360883
  · exact B360887
  · exact B360891
  · exact B360895
  · exact B360899
  · exact B360903
  · exact B360907
  · exact B360911
  · exact B360915
  · exact B360919
  · exact B360923
  · exact B360927
  · exact B360931
  · exact B360935
  · exact B360939
  · exact B360943
  · exact B360947
  · exact B360951
  · exact B360955
  · exact B360959
  · exact B360963
  · exact B360967
  · exact B360971
  · exact B360975
  · exact B360979
  · exact B360983
  · exact B360987
  · exact B360991
  · exact B360995
  · exact B360999
  · exact B361003
  · exact B361007
  · exact B361011
  · exact B361015
  · exact B361019
  · exact B361023
  · exact B361027
  · exact B361031
  · exact B361035
  · exact B361039
  · exact B361043
  · exact B361047
  · exact B361051
  · exact B361055
  · exact B361059
  · exact B361063
  · exact B361067
  · exact B361071
  · exact B361075
  · exact B361079
  · exact B361083
  · exact B361087
  · exact B361091
  · exact B361095
  · exact B361099
  · exact B361103
  · exact B361107
  · exact B361111
  · exact B361115
  · exact B361119
  · exact B361123
  · exact B361127
  · exact B361131
  · exact B361135
  · exact B361139
  · exact B361143
  · exact B361147
  · exact B361151
  · exact B361155
  · exact B361159
  · exact B361163
  · exact B361167
  · exact B361171
  · exact B361175
  · exact B361179
  · exact B361183
  · exact B361187
  · exact B361191
  · exact B361195
  · exact B361199
  · exact B361203
  · exact B361207
  · exact B361211
  · exact B361215
  · exact B361219
  · exact B361223
  · exact B361227
  · exact B361231
  · exact B361235
  · exact B361239
  · exact B361243
  · exact B361247
  · exact B361251
  · exact B361255
  · exact B361259
  · exact B361263
  · exact B361267
  · exact B361271
  · exact B361275
  · exact B361279
  · exact B361283
  · exact B361287
  · exact B361291
  · exact B361295
  · exact B361299
  · exact B361303
  · exact B361307
  · exact B361311
  · exact B361315
  · exact B361319
  · exact B361323
  · exact B361327
  · exact B361331
  · exact B361335
  · exact B361339
  · exact B361343
  · exact B361347
  · exact B361351
  · exact B361355
  · exact B361359
  · exact B361363
  · exact B361367
  · exact B361371
  · exact B361375
  · exact B361379
  · exact B361383
  · exact B361387
  · exact B361391
  · exact B361395
  · exact B361399
  · exact B361403
  · exact B361407
  · exact B361411
  · exact B361415
  · exact B361419
  · exact B361423
  · exact B361427
  · exact B361431
  · exact B361435
  · exact B361439
  · exact B361443
  · exact B361447
  · exact B361451
  · exact B361455
  · exact B361459
  · exact B361463
  · exact B361467
  · exact B361471
  · exact B361475
  · exact B361479
  · exact B361483
  · exact B361487
  · exact B361491
  · exact B361495
  · exact B361499
  · exact B361503
  · exact B361507
  · exact B361511
  · exact B361515
  · exact B361519
  · exact B361523
  · exact B361527
  · exact B361531
  · exact B361535
  · exact B361539
  · exact B361543
  · exact B361547
  · exact B361551
  · exact B361555

theorem C1 (j : ℕ) (h1 : 90389 ≤ j) (h2 : j ≤ 90688) : Blo 358757 (4 * j + 3) := by
  interval_cases j
  · exact B361559
  · exact B361563
  · exact B361567
  · exact B361571
  · exact B361575
  · exact B361579
  · exact B361583
  · exact B361587
  · exact B361591
  · exact B361595
  · exact B361599
  · exact B361603
  · exact B361607
  · exact B361611
  · exact B361615
  · exact B361619
  · exact B361623
  · exact B361627
  · exact B361631
  · exact B361635
  · exact B361639
  · exact B361643
  · exact B361647
  · exact B361651
  · exact B361655
  · exact B361659
  · exact B361663
  · exact B361667
  · exact B361671
  · exact B361675
  · exact B361679
  · exact B361683
  · exact B361687
  · exact B361691
  · exact B361695
  · exact B361699
  · exact B361703
  · exact B361707
  · exact B361711
  · exact B361715
  · exact B361719
  · exact B361723
  · exact B361727
  · exact B361731
  · exact B361735
  · exact B361739
  · exact B361743
  · exact B361747
  · exact B361751
  · exact B361755
  · exact B361759
  · exact B361763
  · exact B361767
  · exact B361771
  · exact B361775
  · exact B361779
  · exact B361783
  · exact B361787
  · exact B361791
  · exact B361795
  · exact B361799
  · exact B361803
  · exact B361807
  · exact B361811
  · exact B361815
  · exact B361819
  · exact B361823
  · exact B361827
  · exact B361831
  · exact B361835
  · exact B361839
  · exact B361843
  · exact B361847
  · exact B361851
  · exact B361855
  · exact B361859
  · exact B361863
  · exact B361867
  · exact B361871
  · exact B361875
  · exact B361879
  · exact B361883
  · exact B361887
  · exact B361891
  · exact B361895
  · exact B361899
  · exact B361903
  · exact B361907
  · exact B361911
  · exact B361915
  · exact B361919
  · exact B361923
  · exact B361927
  · exact B361931
  · exact B361935
  · exact B361939
  · exact B361943
  · exact B361947
  · exact B361951
  · exact B361955
  · exact B361959
  · exact B361963
  · exact B361967
  · exact B361971
  · exact B361975
  · exact B361979
  · exact B361983
  · exact B361987
  · exact B361991
  · exact B361995
  · exact B361999
  · exact B362003
  · exact B362007
  · exact B362011
  · exact B362015
  · exact B362019
  · exact B362023
  · exact B362027
  · exact B362031
  · exact B362035
  · exact B362039
  · exact B362043
  · exact B362047
  · exact B362051
  · exact B362055
  · exact B362059
  · exact B362063
  · exact B362067
  · exact B362071
  · exact B362075
  · exact B362079
  · exact B362083
  · exact B362087
  · exact B362091
  · exact B362095
  · exact B362099
  · exact B362103
  · exact B362107
  · exact B362111
  · exact B362115
  · exact B362119
  · exact B362123
  · exact B362127
  · exact B362131
  · exact B362135
  · exact B362139
  · exact B362143
  · exact B362147
  · exact B362151
  · exact B362155
  · exact B362159
  · exact B362163
  · exact B362167
  · exact B362171
  · exact B362175
  · exact B362179
  · exact B362183
  · exact B362187
  · exact B362191
  · exact B362195
  · exact B362199
  · exact B362203
  · exact B362207
  · exact B362211
  · exact B362215
  · exact B362219
  · exact B362223
  · exact B362227
  · exact B362231
  · exact B362235
  · exact B362239
  · exact B362243
  · exact B362247
  · exact B362251
  · exact B362255
  · exact B362259
  · exact B362263
  · exact B362267
  · exact B362271
  · exact B362275
  · exact B362279
  · exact B362283
  · exact B362287
  · exact B362291
  · exact B362295
  · exact B362299
  · exact B362303
  · exact B362307
  · exact B362311
  · exact B362315
  · exact B362319
  · exact B362323
  · exact B362327
  · exact B362331
  · exact B362335
  · exact B362339
  · exact B362343
  · exact B362347
  · exact B362351
  · exact B362355
  · exact B362359
  · exact B362363
  · exact B362367
  · exact B362371
  · exact B362375
  · exact B362379
  · exact B362383
  · exact B362387
  · exact B362391
  · exact B362395
  · exact B362399
  · exact B362403
  · exact B362407
  · exact B362411
  · exact B362415
  · exact B362419
  · exact B362423
  · exact B362427
  · exact B362431
  · exact B362435
  · exact B362439
  · exact B362443
  · exact B362447
  · exact B362451
  · exact B362455
  · exact B362459
  · exact B362463
  · exact B362467
  · exact B362471
  · exact B362475
  · exact B362479
  · exact B362483
  · exact B362487
  · exact B362491
  · exact B362495
  · exact B362499
  · exact B362503
  · exact B362507
  · exact B362511
  · exact B362515
  · exact B362519
  · exact B362523
  · exact B362527
  · exact B362531
  · exact B362535
  · exact B362539
  · exact B362543
  · exact B362547
  · exact B362551
  · exact B362555
  · exact B362559
  · exact B362563
  · exact B362567
  · exact B362571
  · exact B362575
  · exact B362579
  · exact B362583
  · exact B362587
  · exact B362591
  · exact B362595
  · exact B362599
  · exact B362603
  · exact B362607
  · exact B362611
  · exact B362615
  · exact B362619
  · exact B362623
  · exact B362627
  · exact B362631
  · exact B362635
  · exact B362639
  · exact B362643
  · exact B362647
  · exact B362651
  · exact B362655
  · exact B362659
  · exact B362663
  · exact B362667
  · exact B362671
  · exact B362675
  · exact B362679
  · exact B362683
  · exact B362687
  · exact B362691
  · exact B362695
  · exact B362699
  · exact B362703
  · exact B362707
  · exact B362711
  · exact B362715
  · exact B362719
  · exact B362723
  · exact B362727
  · exact B362731
  · exact B362735
  · exact B362739
  · exact B362743
  · exact B362747
  · exact B362751
  · exact B362755

theorem solution (m : ℕ) (hlo : 358757 ≤ m) (hhi : m ≤ 362757) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 89689 ≤ j := by omega
    have hj2 : j ≤ 90688 := by omega
    have hb : Blo 358757 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 90389 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
